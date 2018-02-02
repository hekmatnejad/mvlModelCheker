// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2014, 2015, 2016, 2017 Laboratoire
// de Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2006 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.


//#include <spot/twa/twaproduct.hh>
#include <string>
#include <cassert>
#include <spot/misc/hashfunc.hh>
#include <spot/kripke/kripke.hh>

#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/alternation.hh>
#include <spot/twa/twa.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/word.hh>
#include <valarray>
#include "mvtwaproduct.h"
//#include "mv_interval.h"
#include "KripkeModel.h"

using namespace std;

#define _MAX_COST  5555
#define _MAX_DIST  MAX_GEO_DIST
spot::twa_graph_ptr shared_formula_graph;
const spot::kripke* shared_model_kripke;
bool clear_todo_queue = false;

//namespace mv{

namespace spot
{
    using namespace spot;

  static spot::bdd_dict_ptr shared_dict;  
  static mvspot::mv_interval* shared_intervals;
  //static std::map<const spot::twa_graph_state*, std::map<int,std::list<symbol_stc>*>*>* shared_locs;
  const std::map<tuple_edge, std::map<int,std::list<symbol_stc>*>*>* shared_locs;
  //std::map<int, geo_pos> geo_locations;  
  ////////////////////////////////////////////////////////////
  // state_product

  state_product::~state_product()
  {
    left_->destroy();
    right_->destroy();
  }

  void
  state_product::destroy() const
  {
    if (--count_)
      return;
    fixed_size_pool* p = pool_;
    this->~state_product();
    p->deallocate(this);
  }

  int
  state_product::compare(const state* other) const
  {
    const state_product* o = down_cast<const state_product*>(other);
    int res = left_->compare(o->left());
    if (res != 0)
      return res;
    return right_->compare(o->right());
  }

  size_t
  state_product::hash() const
  {
    // We assume that size_t is 32-bit wide.
    return wang32_hash(left_->hash()) ^ wang32_hash(right_->hash());
  }

  state_product*
  state_product::clone() const
  {
    ++count_;
    return const_cast<state_product*>(this);
  }

  ////////////////////////////////////////////////////////////
  // twa_succ_iterator_product

  namespace
  {

    class twa_succ_iterator_product_common: public twa_succ_iterator
    {
    public:
      twa_succ_iterator_product_common(twa_succ_iterator* left,
                                        twa_succ_iterator* right,
                                        const twa_product* prod,
                                        fixed_size_pool* pool)
        : left_(left), right_(right), prod_(prod), pool_(pool)
      {
      }

      twa_succ_iterator_product_common(twa_succ_iterator* left,
                                        twa_succ_iterator* right, unsigned steps,
                                        const twa_product* prod,
                                        fixed_size_pool* pool)
        : left_(left), right_(right), steps_(steps), prod_(prod), pool_(pool)
      {
      }
        
      void recycle(const const_twa_ptr& l, twa_succ_iterator* left,
                   const_twa_ptr r, twa_succ_iterator* right, unsigned steps)
      {
        l->release_iter(left_);
        left_ = left;
        r->release_iter(right_);
        right_ = right;
        steps_ = steps;
      }

      virtual ~twa_succ_iterator_product_common()
      {
        delete left_;
        delete right_;
      }

      virtual bool next_non_false_() = 0;

      bool first() override
      {
        if (!right_)
          return false;

        // If one of the two successor sets is empty initially, we
        // reset right_, so that done() can detect this situation
        // easily.  (We choose to reset right_ because this variable
        // is already used by done().)
        if (!(left_->first() && right_->first()))
          {
            delete right_;
            right_ = nullptr;
            return false;
          }
        return next_non_false_();
      }

      bool done() const override
      {
        return !right_ || right_->done();
      }

      const state_product* dst() const override
      {
//        return new(pool_->allocate()) state_product(left_->dst(),
//                                                    right_->dst(),
//                                                    pool_);
        return new(pool_->allocate()) state_product(left_->dst(),
                                                    right_->dst(), steps_,
                                                    pool_);
      }

      unsigned steps_ = 0;

    protected:
      twa_succ_iterator* left_;
      twa_succ_iterator* right_;
      const twa_product* prod_;
      fixed_size_pool* pool_;
      friend class spot::twa_product;
    };


    /// \brief Iterate over the successors of a product computed on the fly.
    class twa_succ_iterator_product final:
      public twa_succ_iterator_product_common
    {
    public:
      twa_succ_iterator_product(twa_succ_iterator* left,
                                 twa_succ_iterator* right,
                                 const twa_product* prod,
                                 fixed_size_pool* pool)
        : twa_succ_iterator_product_common(left, right, prod, pool)
      {
      }

      virtual ~twa_succ_iterator_product()
      {
      }

      bool step_()
      {
        if (left_->next())
          return true;
        left_->first();
        return right_->next();
      }

      bool next_non_false_() override
      {
        assert(!done());
        do
          {
            bdd l = left_->cond();
            bdd r = right_->cond();
            bdd current_cond = l & r;

            cout << "--- in next_non_false " << current_cond << endl;
            if (current_cond != bddfalse)
              {
                current_cond_ = current_cond;
                return true;
              }
          }
        while (step_());
        return false;
      }

      bool next() override
      {
          cout << "next\n";
        if (step_())
          return next_non_false_();
        return false;
      }

      bdd cond() const override
      {
        return current_cond_;
      }

      acc_cond::mark_t acc() const override
      {
        return left_->acc() | (right_->acc() << prod_->left_acc().num_sets());
      }

    protected:
      bdd current_cond_;
    };

    /// Iterate over the successors of a product computed on the fly.
    /// This one assumes that LEFT is an iterator over a Kripke structure
    class twa_succ_iterator_product_kripke final:
      public twa_succ_iterator_product_common
    {
    public:
      twa_succ_iterator_product_kripke(twa_succ_iterator* left,
                                        twa_succ_iterator* right,
                                        const twa_product* prod,
                                        fixed_size_pool* pool)
        : twa_succ_iterator_product_common(left, right, prod, pool)
      {
      }

      twa_succ_iterator_product_kripke(twa_succ_iterator* left,
                                        twa_succ_iterator* right, unsigned steps,
                                        const twa_product* prod,
                                        fixed_size_pool* pool)
        : twa_succ_iterator_product_common(left, right, steps, prod, pool)
      {
      }

      virtual ~twa_succ_iterator_product_kripke()
      {
      }

float find_dist_to_locs_graph_cpy(unsigned* state_num, const tuple_edge& f_state) 
{
    bool cycle_node = false;
    if(f_state.dst_ == f_state.src_)
        cycle_node = true;
    if(cycle_node)
        return NUM_CARS;
    
    std::map<int, std::list<symbol_stc>*>* s_map = (*shared_locs).at(f_state);
    float min_dist[NUM_CARS];
    float res = 0;
    bool found = false;
    for (int i = 0; i < NUM_CARS; i++) {
        min_dist[i] = 1;
        float dist_neg = 1;
        float dist_pos = 1;
        found = false;
        std::list<symbol_stc>* s_list = (*s_map)[i + 1];
        //if(s_list->size()>1)
        //    std::cout << "\n\n**** No more than one location symbol per state must exist!\n\n";
        //if(s_list!=NULL)//not needed anymore
        //if (!s_list->empty())
            for (std::list<symbol_stc>::iterator it = s_list->begin(); it != s_list->end(); ++it) {
                //                  cout << (*it).loc << " type: ";
                //                  if((*it).type == symbol_type::NEGATIVE)
                //                      cout << "NEG\n";
                //                  else if((*it).type == symbol_type::POSITIVE)
                //                      cout << "POS\n";
                //                  else
                //                      cout << "BOT\n";

                //cout << (*geo_locations)[state_num[i]]->x_ << " , " << (*geo_locations)[state_num[i]]->y_ << endl;
                //cout << (*geo_locations)[(*it).loc]->x_ << " , " << (*geo_locations)[(*it).loc]->y_ << endl;
                //cout << "--------\n";            
/*
                //if(cycle_node)
                {
                if( (*it).type == symbol_type::NEGATIVE)
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_ , 2);  
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);  
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST; 
                    if (dist < dist_neg)
                    {
                        dist_neg = dist;
                        found = true;
                    }
                }
                    
                }
                //else
                {
                if ( (*it).type == symbol_type::POSITIVE) {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_, 2);
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST;
                    //if (dist < min_dist[i]) 
                    {
                        dist_pos = dist;
                        found = true;
                    }
                }
                    
                }
 */
                
                //this must be updated: only one location symbol per state
                if ( (*it).type == symbol_type::POSITIVE) {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_, 2);
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST;
                    //if (dist < min_dist[i]) 
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }
                /*
                else if( (*it).type == symbol_type::NEGATIVE)
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_ , 2);  
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);  
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST; 
                    //if (dist < min_dist[i])
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }
                
                else if((*it).type == symbol_type::BOTH)
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_ , 2);  
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);  
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST; 
                    dist = dist < (1-dist) ? dist : 1-dist;
                    //if(dist < min_dist[i])
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }
                */
            }
//        if(dist_pos < 1)
//            min_dist[i] = dist_pos;
//        else if(dist_neg < 1)
//            min_dist[i] = dist_neg;
        //if (found)
            res += min_dist[i];
    }

    if (!found && res == 0)
        res = NUM_CARS * 1;
    //cout << res<<endl;
    return res;
}

float find_dist_to_locs_graph(unsigned* state_num, const tuple_edge& f_state) 
{
   
    std::map<int, std::list<symbol_stc>*>* s_map = (*shared_locs).at(f_state);
    float min_dist[NUM_CARS];
    float res = 0;
    bool found = false;
    for (int i = 0; i < NUM_CARS; i++) {
        min_dist[i] = 1;
        float dist_neg = 1;
        float dist_pos = 1;
        found = false;
        std::list<symbol_stc>* s_list = (*s_map)[i + 1];
            for (std::list<symbol_stc>::iterator it = s_list->begin(); it != s_list->end(); ++it) {
                
                //this must be updated: only one location symbol per state
                if ( (*it).type == symbol_type::POSITIVE) 
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_, 2);
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST;
                    if (dist < min_dist[i]) 
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }
                /*
                else if( (*it).type == symbol_type::NEGATIVE)
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_ , 2);  
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);  
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST;
                    if (dist < min_dist[i])
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }*/
                /*
                else if((*it).type == symbol_type::BOTH)
                {
                    float dist = std::pow((*geo_locations)[state_num[i]]->x_ - (*geo_locations)[(*it).loc]->x_ , 2);  
                    dist += std::pow((*geo_locations)[state_num[i]]->y_ - (*geo_locations)[(*it).loc]->y_, 2);  
                    dist = std::sqrt(dist);
                    dist = dist / MAX_GEO_DIST; 
                    dist = dist < (1-dist) ? dist : 1-dist;
                    //if(dist < min_dist[i])
                    {
                        min_dist[i] = dist;
                        found = true;
                    }
                }
                */
            }
//        if(dist_pos < 1)
//            min_dist[i] = dist_pos;
//        else if(dist_neg < 1)
//            min_dist[i] = dist_neg;
        //if (found)
            res += min_dist[i];
    }

    if (!found && res == 0)
        res = NUM_CARS * 1;
    //cout << res<<endl;
    return res;
}
      
      bool next_non_false_() override
      {
            if(left_->cond()==bddfalse){
              current_cond_ = bddfalse;
              return false;
          }
        // All the transitions of left_ iterator have the
        // same label, because it is a Kripke structure.
        std::pair<mvspot::mv_interval*,bdd> itv_res;
        bdd l = left_->cond();
        assert(!right_->done());
        do
          {
            bdd r = right_->cond();
            bdd current_cond = l & r;
            if(current_cond != bddfalse)
            {
            itv_res = mvspot::interval_bdd::apply_and(r, l, shared_dict);   
            if(!itv_res.first->isFalse())
            {

                const marine_robot_state* mrs = 
                            static_cast<const marine_robot_state*>(left_->dst());

                tuple_edge te(shared_formula_graph->edge_storage(right_).src,
                        shared_formula_graph->edge_storage(right_).dst,
                        spot::bdd_format_formula(shared_dict,right_->cond()));
                loc_dist_ = find_dist_to_locs_graph(mrs->get_state_num(), te);
                //loc_dist_ = loc_dist_ + 1 - itv_res.first->getButtom()->getValue();

                inf_ = NUM_CARS + 1 - itv_res.first->getButtom()->getValue();
                sup_ = NUM_CARS + 1 - itv_res.first->getTop()->getValue();
                
                cost_inf_ = loc_dist_ + 1 - itv_res.first->getButtom()->getValue();
                cost_sup_ = loc_dist_ + 1 - itv_res.first->getTop()->getValue();
                
                //cout << "cost: " << cost_inf_ << " , " << cost_sup_ << endl;
//                cout << "model   cond: " << spot::bdd_format_formula(shared_dict,left_->cond()) << endl;
//                cout << "formula cond: " << spot::bdd_format_formula(shared_dict,right_->cond()) << endl;
//                std::cout << "min_dist: " << loc_dist_ << endl;                
                
                //cout << "**** " << shared_formula_graph->format_state(shared_formula_graph->state_from_number(shared_formula_graph->edge_storage(right_).src)) << endl;
                //current_cond_ = current_cond;//itv_res.second;
                
                mrs->destroy();
                current_cond_ = bddtrue;//****************test: for printout purposes
                return true;
            }
            }
          }
        while (right_->next());

        current_cond_ = bddfalse;

        return false;

      }

      bool next() override
      {
        if (left_->next())
            return true;
        left_->first();
        bool res;
        if (right_->next()){
            //cout << "\n\nnext: " << shared_formula_graph->edge_storage(right_).src << " -> "<<
            //        shared_formula_graph->edge_storage(right_).dst <<  endl;
            steps_++;
            res = next_non_false_();
        }
        if(res){
            //steps_++;
            //clear_todo_queue = true;
        }
        return res;
      }
      
      bool first() override
      {
        if (!right_)
          return false;

        //steps_=1;
        // If one of the two successor sets is empty initially, we
        // reset right_, so that done() can detect this situation
        // easily.  (We choose to reset right_ because this variable
        // is already used by done().)
        if (!(left_->first() && right_->first()))
          {
            delete right_;
            right_ = nullptr;
            return false;
          }
        bool res = next_non_false_();
        if(res){
            //cout << "\n\nfirst: " << shared_formula_graph->edge_storage(right_).src << " -> "<<
            //        shared_formula_graph->edge_storage(right_).dst <<  endl;
            //clear_todo_queue = true;
        }
        return res;
      }

      bool done() const override
      {
        return !right_|| right_->done();
      }
      
      bdd cond() const override
      {
        return current_cond_;
      }
      
      float cost_inf() 
      {
          return cost_inf_;
      }

      float cost_sup() 
      {
          return cost_sup_;
      }

      float inf() 
      {
          return inf_;
      }

      float sup() 
      {
          return sup_;
      }
      
      float loc_dist() 
      {
          return loc_dist_;
      }

      acc_cond::mark_t acc() const override
      {
        return right_->acc();
      }

    protected:
      bdd current_cond_ = bddtrue;
      float cost_inf_ = _MAX_COST;//primary cost 
      float cost_sup_ = _MAX_COST;//secondary cost
      float loc_dist_ = _MAX_DIST;//A star helper
      float inf_ = NUM_CARS;
      float sup_ = NUM_CARS;
    };

  } // anonymous

  ////////////////////////////////////////////////////////////
  // twa_product

  
    //twa_product::twa_product(const const_twa_ptr& left,
    //                         const const_twa_ptr& right, mvspot::mv_interval* intervals)
    //: twa(left->get_dict()), left_(left), right_(right),
    //  pool_(sizeof(state_product))
//    : twa_product(left, right), intervals_(interval)
    //{
    //}

  
  twa_product::twa_product(const const_twa_ptr& left,
                             const const_twa_ptr& right)
    : twa(left->get_dict()), left_(left), right_(right),
      pool_(sizeof(state_product))
  {
    if (left->get_dict() != right->get_dict())
      throw std::runtime_error("twa_product: left and right automata should "
                               "share their bdd_dict");
    assert(get_dict() == right_->get_dict());

    
    // If one of the side is a Kripke structure, it is easier to deal
    // with (we don't have to fix the acceptance conditions, and
    // computing the successors can be improved a bit).
    if (dynamic_cast<const kripke*>(left_.get()))
      {
        left_kripke_ = true;
      }
    else if (dynamic_cast<const kripke*>(right_.get()))
      {
        std::swap(left_, right_);
        left_kripke_ = true;
      }
    else
      {
        left_kripke_ = false;
      }
    
    copy_ap_of(left_);
    copy_ap_of(right_);
    
    //***************//
    shared_dict = get_dict();
    shared_model_kripke = dynamic_cast<const kripke*>(left_.get());
    //shared_locs = compute_all_locations_of_formula(right_);
    if(!shared_formula_graph)
    {
        std::cout <<" shared_formula_graph is not cloned!\n";
        exit(0);
    }
    shared_locs = compute_all_locations_of_graph_formula(shared_formula_graph);
    //tuple_edge tst(7,7,"(!C1_loc_1 & col_avo & \"q=[1,1]\") | (!C1_loc_9 & col_avo & \"q=[1,1]\")");
    //cout << (*shared_locs).at(tst)->size() << endl;
    //exit(0);
    cout << "step completed...\n";
    //TEST
    //std::list<symbol_stc>* tst_list = 
    //        (*(*shared_locs)[shared_formula_graph->get_init_state()])[1];
    //for(std::list<symbol_stc>::iterator it = tst_list->begin(); it != tst_list->end(); ++it)
    //    cout << ">>>>> " << (*it).loc << endl;
    
    
    std::cout << "*** in -> twa_product::twa_product\n";
    assert(num_sets() == 0);
    auto left_num = left->num_sets();
    auto right_acc = right->get_acceptance() << left_num;
    right_acc &= left->get_acceptance();
    set_acceptance(left_num + right->num_sets(), right_acc);
  }

  twa_product::~twa_product()
  {
    // Make sure we delete the iterator cache before erasing the two
    // automata (by reference counting).
    delete iter_cache_;
    iter_cache_ = nullptr;
  }

  const state*
  twa_product::get_init_state() const
  {
    fixed_size_pool* p = const_cast<fixed_size_pool*>(&pool_);
    return new(p->allocate()) state_product(left_->get_init_state(),
                                            right_->get_init_state(), p);
  }

  twa_succ_iterator*
  twa_product::succ_iter(const state* state) const
  {
    const state_product* s = down_cast<const state_product*>(state);
    twa_succ_iterator* li = left_->succ_iter(s->left());
    twa_succ_iterator* ri = right_->succ_iter(s->right());
    
    if (iter_cache_)
      {
        twa_succ_iterator_product_common* it =
          down_cast<twa_succ_iterator_product_common*>(iter_cache_);
        it->recycle(left_, li, right_, ri, s->steps_+1);
        iter_cache_ = nullptr;
        return it;
      }

    fixed_size_pool* p = const_cast<fixed_size_pool*>(&pool_);
    if (left_kripke_)
      return new twa_succ_iterator_product_kripke(li, ri, s->steps_+1, this, p);
    else
      return new twa_succ_iterator_product(li, ri, this, p);
  }

  const acc_cond& twa_product::left_acc() const
  {
    return left_->acc();
  }

  const acc_cond& twa_product::right_acc() const
  {
    return right_->acc();
  }

  std::string
  twa_product::format_state(const state* state) const
  {
    const state_product* s = down_cast<const state_product*>(state);
    return (left_->format_state(s->left())
            + " * "
            + right_->format_state(s->right()) 
            //+ " " + spot::bdd_format_formula(dict_, this->ap_vars()) 
            );
    //return (left_->format_state(s->left()));
  }

  state*
  twa_product::project_state(const state* s, const const_twa_ptr& t) const
  {
    const state_product* s2 = down_cast<const state_product*>(s);
    if (t.get() == this)
      return s2->clone();
    state* res = left_->project_state(s2->left(), t);
    if (res)
      return res;
    return right_->project_state(s2->right(), t);
  }

  //////////////////////////////////////////////////////////////////////
  // twa_product_init

  twa_product_init::twa_product_init(const const_twa_ptr& left,
                                       const const_twa_ptr& right,
                                       const state* left_init,
                                       const state* right_init)
    : twa_product(left, right),
      left_init_(left_init), right_init_(right_init)
  {
    if (left_ != left)
      std::swap(left_init_, right_init_);
  }

  const state*
  twa_product_init::get_init_state() const
  {
    fixed_size_pool* p = const_cast<fixed_size_pool*>(&pool_);
    return new(p->allocate()) state_product(left_init_->clone(),
                                            right_init_->clone(), p);
  }
//--------------------------

class a_star_node{
public:
    a_star_node(size_t state_hash, float primary_cost, float a_star_cost){
        state_hash_ = state_hash;
        primary_cost_ = primary_cost;
        a_star_cost_ = a_star_cost;
    }
    a_star_node(const a_star_node &node){
        state_hash_ = node.state_hash_;
        primary_cost_ = node.primary_cost_;
        a_star_cost_ = node.a_star_cost_;
    }
    
    bool operator <(const a_star_node& rhs) const
    {
        if (state_hash_ < rhs.state_hash_ || (state_hash_ == rhs.state_hash_ && 
                primary_cost_ < rhs.primary_cost_))
            return true;
        else if ((state_hash_ == rhs.state_hash_ && primary_cost_ == rhs.primary_cost_) )
            if ( a_star_cost_ < rhs.a_star_cost_)
                return true;
        return false;
    }    
    size_t state_hash_;
    float primary_cost_;
    float a_star_cost_;
};
  
class a_star_costcomparison
{
  bool reverse;
public:
  a_star_costcomparison(const bool& revparam=true)//must be true
    {reverse=revparam;}
  bool operator() (const a_star_node& lhs, const a_star_node& rhs) const
  {
      
    if (reverse) 
    {
        if(lhs.primary_cost_ > rhs.primary_cost_ ||
              (lhs.primary_cost_ == rhs.primary_cost_ && 
                lhs.a_star_cost_ > rhs.a_star_cost_)  )
            return true;
        else
            return false;
    }
    else{ 
        if(lhs.primary_cost_ < rhs.primary_cost_ ||
              (lhs.primary_cost_ == rhs.primary_cost_ && 
                lhs.a_star_cost_ < rhs.a_star_cost_)  )
            return true;
        else 
            return false;
    }
 
  }
};  

class minimal_cost {

public:
    minimal_cost(spot::twa_product_ptr twa_prd){
        twa_prd_ = twa_prd;
    }
    
    float cycle_check(size_t cc, size_t& dst) 
    {
        if(reverse_[cc].top() == cc)
            return 0;
        if(reverse_[cc].top() == dst)
            return state_cost_map_[cc];
        while(!reverse_[cc].empty()){
            return state_cost_map_[cc]+cycle_check(reverse_[cc].top(), dst);
            reverse_[cc].pop();
        }
        return 0;
    } 
    
    spot::twa_ptr find_optimal_path_A_star() {
        
        std::cout << "*** in: find_optimal_path_A_star\n";
        
        std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>*
                todo_q = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
        std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>*
                todo_q_cpy;// = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
        std::set<size_t> visited = std::set<size_t>();
        std::map<size_t,std::stack<size_t>> reverse = std::map<size_t,std::stack<size_t>>();
        state_cost_map_ = std::map<size_t,float>();
        std::map<size_t,float> total_cost_map = std::map<size_t,float>();
        std::map<size_t,const spot::state*> 
                reverse_state = std::map<size_t,const spot::state*>();
        size_t target;
        size_t start;
        std::pair<const spot::state*,float> item = 
                std::make_pair(twa_prd_->get_init_state(),0);
        std::cout << "init state: " << twa_prd_->format_state(twa_prd_->get_init_state()) << endl << endl;
        todo_q->push(a_star_node(twa_prd_->get_init_state()->hash(),0,0));
        start = item.first->hash();
        state_cost_map_[start] = 0;
        total_cost_map[start] = 0;
        visited.insert(item.first->hash());
        reverse[item.first->hash()].push(item.first->hash());
        reverse_state[item.first->hash()] = item.first;
        bool found_plan = false;
        const spot::state* cs;//current state
        float min_c = 0;
        float optimal_cost = -1;
        while(!todo_q->empty())
        {
            //auto start = chrono::steady_clock::now();

            a_star_node node(todo_q->top());
            todo_q->pop();
            visited.insert(node.state_hash_);
            cs = reverse_state[node.state_hash_];//do not need the state, hash is fine
            //min_c = node.primary_cost_;//not solid
            min_c = total_cost_map[node.state_hash_];//solid
            
            twa_succ_iterator_product_kripke* tit = 
                    down_cast<twa_succ_iterator_product_kripke*>
                    (twa_prd_->succ_iter(cs));
            //spot::twa_succ_iterator* tit = twa_prd_->succ_iter(cs);
            if(!tit->first()){
                //cout << "!tit->first()\n";
                twa_prd_->release_iter(tit);
                continue;
            }
            if(tit->cond() == bddfalse)
                cout << ".";
            while(!tit->done() && tit->cond()!=bddfalse)
            {

                const spot::state_product* tit_dst = tit->dst();
                
//                twa_succ_iterator_product_kripke* tmp = 
//                    down_cast<twa_succ_iterator_product_kripke*>
//                    (twa_prd_->succ_iter(tit_dst));
//                if(!tmp->first() || tmp->cond()==bddfalse){
//                    tit->next();
//                    twa_prd_->release_iter(tmp);
//                    tit_dst->destroy();
//                    continue;
//                }

                //cout << tit->steps_ << " " << endl;

             
//                if(twa_prd_->right_acc().accepting(tmp->acc()))
//                {
//                    cout << "cond: " << tmp->acc() << endl;
//                    target = tmp->dst()->hash();
//                    if(target != cs->hash()){
//                        reverse[target] = cs->hash();
//                        reverse_state[target] = tmp->dst();
//                    }
//                    optimal_cost = min_c;
//                    found_plan = true;
//                    break;
//                }
                if(twa_prd_->right_acc().accepting(tit->acc()) && 
                        tit->cond() != bddfalse)
                {
                    cout << "cond: " << tit->acc() << endl;
                    target = tit_dst->hash();
                    if(target != cs->hash())
                    {
                        reverse[target].push(cs->hash());
                        reverse_state[target] = tit_dst;
                    }
                    optimal_cost = min_c;
                    found_plan = true;
                    break;
                }
                if(visited.find(tit_dst->hash()) == visited.end()
//                        ||  (visited.find(tit_dst->hash()) != visited.end() 
//                            &&
//                            ////total_cost_map[tit_dst->hash()] > (min_c+(tit->cost_inf()+tit->cost_sup())/2.0)
//                            //total_cost_map[tit_dst->hash()] > (min_c+tit->cost_inf())
//                            total_cost_map[tit_dst->hash()] > (min_c+(tit->inf()+tit->sup())/2.0)
//                            )
                  )
                {
                    //cout << ".";tit->steps_
                    //cout << std::to_string(1-((tit->steps_)/25.0)) << "\n";
                    todo_q->push(a_star_node(tit_dst->hash(), 
                            //min_c+(tit->inf()+tit->sup())/2.0 , min_c+ 1-((tit->steps_)/25.0) ));
                            //min_c+(tit->inf()+tit->sup())/2.0 , min_c+tit->cost_inf() ));
                            min_c+(tit->inf()+tit->sup())/2.0 , 1 ));
                    total_cost_map[tit_dst->hash()] = min_c+(tit->inf()+tit->sup())/2.0;
                    state_cost_map_[tit_dst->hash()] = (tit->inf()+tit->sup())/2.0;
                    reverse[tit_dst->hash()].push(cs->hash());
                    if(reverse_state.find(tit_dst->hash()) == reverse_state.end())
                        reverse_state[tit_dst->hash()] = tit_dst;
                    //else
                    //    tit_dst->destroy();
                }
                else if(     visited.find(tit_dst->hash()) != visited.end() 
                        &&
                        total_cost_map[tit_dst->hash()] > (min_c+(tit->inf()+tit->sup())/2.0)
                  )
                {
                    //cout << "+";
                    total_cost_map[tit_dst->hash()] = min_c+(tit->inf()+tit->sup())/2.0;
                    state_cost_map_[tit_dst->hash()] = (tit->inf()+tit->sup())/2.0;
                    reverse[tit_dst->hash()].push(cs->hash());
                    //if(reverse_state.find(tit_dst->hash()) == reverse_state.end())
                    //    reverse_state[tit_dst->hash()] = tit_dst;
                    //else
                        tit_dst->destroy();
                }
                else
                {
                    //cout << "-";
                    //total_cost_map[tit_dst->hash()] = min_c+(tit->inf()+tit->sup())/2.0;
                    //total_cost_map[tit_dst->hash()] = min_c+(tit->inf()+tit->sup())/2.0;
                    //state_cost_map_[tit_dst->hash()] = (tit->inf()+tit->sup())/2.0;
                    //reverse[tit_dst->hash()].push(cs->hash());
                    //if(reverse_state.find(tit_dst->hash()) == reverse_state.end())
                    //    reverse_state[tit_dst->hash()] = tit_dst;
                    //else
                        tit_dst->destroy();
//                    float cpy_total_cost = total_cost_map[tit_dst->hash()];
//                    size_t cpy_dst = tit_dst->hash();
//                    if( visited.find(cpy_dst) != visited.end())
//                    {
//                        reverse_ = std::map<size_t,std::stack<size_t>>(reverse);
//                        
//                        bool loop_detected = false;;
//                        cycle_cost_ = cycle_check(cs->hash(), cpy_dst);
//                        if(cycle_cost_ !=0 )
//                            loop_detected = true;
//
//                        if(loop_detected){
//                            
//                        //cout << "^^^^" <<twa_prd_->format_state(reverse_state[tit_dst->hash()]) << endl;
//                            //cout << "update cost: " <<  total_cost_map[tit_dst->hash()] << " to " << cycle_cost_ << endl;
//                            //total_cost_map[tit_dst->hash()] = min_c+cycle_cost_;//+(tit->inf()+tit->sup())/2.0;
//                        }
//                    }
                    
//                    tit_dst->destroy();

                }
//                else if(false && (visited.find(tit_dst->hash()) != visited.end() 
//                            &&
//                            //total_cost_map[tit_dst->hash()] > (min_c+(tit->cost_inf()+tit->cost_sup())/2.0)
//                            total_cost_map[tit_dst->hash()] > (min_c+tit->cost_inf())
//                            )
//                  )
//                {
//                //cout << "^^^^" <<twa_prd_->format_state(tit_dst) << endl;//twa_prd_->format_state(st) << endl;
//                if(tit_dst->hash()==cs->hash() || tit_dst->hash()==start)
//                    break;
//                //cout << "here\n";
//                    size_t rn = cs->hash();
//                    bool loop_detected = false;
//                    while(reverse[rn].top()!=start){
//                        if(reverse[rn].top()==tit_dst->hash()){
//                            loop_detected = true;
//                            cout << ".\n";
//                            break;
//                        }
//                        rn = reverse[rn].top();
//                    }
//                    //cout << "out\n";
//
//                    if(!loop_detected){
//                    todo_q->push(a_star_node(tit_dst->hash(),
//                        min_c+tit->cost_inf(), min_c+tit->cost_sup()));
//            //total_cost_map[tit_dst->hash()] = min_c+(tit->cost_inf()+tit->cost_sup())/2.0;
//            total_cost_map[tit_dst->hash()] = min_c+tit->cost_inf();
//            reverse[tit_dst->hash()].push(cs->hash());
//                    state_cost_map[tit_dst->hash()] = (tit->inf());
//                    if(reverse_state.find(tit_dst->hash())==reverse_state.end())
//                        reverse_state[tit_dst->hash()] = tit_dst;
//                    else
//                        tit_dst->destroy();
//            
//                        
//                    }
//                }

                //twa_prd_->release_iter(tmp);

                if(!tit->next())
                    break;   
            }
            
            //cout << todo_q->size() << endl;
            
                if( false && clear_todo_queue)
                {
                    //cout << "\n^^^^" <<twa_prd_->format_state(reverse_state[tit_dst->hash()]) << endl;
                    std::cout << "\nreverse size: " << reverse.size() 
                        << " todo_q size: " << todo_q->size() 
                        << " visited size: " << visited.size() << endl <<endl;
                    cout << "cleaning priority queue... ";
                    auto start = chrono::steady_clock::now();

                    delete todo_q;
                    todo_q = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
                    auto end = chrono::steady_clock::now();
                    cout << "elapsed time in microseconds: " << chrono::duration_cast<chrono::microseconds>(end - start).count() << endl;
                    clear_todo_queue = false;
                    //if(visited.find(tit_dst->hash()) != visited.end())
                    //    visited.erase(visited.find(tit_dst->hash()));
                }               
            
            twa_prd_->release_iter(tit);
            
            if(found_plan)
                break;

           
            //auto end = chrono::steady_clock::now();
            //cout << "time ms: " << chrono::duration_cast<chrono::microseconds>(end - start).count() << endl;
            if ( todo_q->size() > MAX_Q_SIZE_)
            {
                    //const state_product* s = down_cast<const state_product*>(reverse_state[todo_q->top().state_hash_]);

                std::cout << "\nreverse size: " << reverse.size() 
                    << " todo_q size: " << todo_q->size() 
                    << " visited size: " << visited.size() << endl <<endl;
                cout << "Pruning priority queue... ";
                auto start = chrono::steady_clock::now();
                todo_q_cpy = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
                for(int i=0; i < NUM_CPY_FRM_Q_; i++)
                {
                    todo_q_cpy->push(todo_q->top());
                    todo_q->pop();
                }
                //todo: maybe visited map also must be updated!
                delete todo_q;
                todo_q = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
                swap(todo_q,todo_q_cpy);
                delete todo_q_cpy;
                auto end = chrono::steady_clock::now();
                cout << "elapsed time in microseconds: " << chrono::duration_cast<chrono::microseconds>(end - start).count() << endl;

            }
        }
        if(found_plan){
            std::cout << "\nFOUND AN OPTIMAL PLAN ****\n" << "reverse size: " << reverse.size() 
                    << " todo_q size: " << todo_q->size() 
                    << " visited size: " << visited.size() << endl;

            std::stack<const spot::state*> path = std::stack<const spot::state*> ();
            size_t st = target;
            size_t tst;

//            for(int i=0; i<50;i++){
//                path.push(reverse_state[st]);
//                tst = reverse[st].top();
//                reverse[st].pop();
//                st = tst;
//                cout << twa_prd_->format_state(path.top()) << endl;//twa_prd_->format_state(st) << endl;
//            }
//            return;
            while(st != start){
                path.push(reverse_state[st]);
                tst = reverse[st].top();
                reverse[st].pop();
                st = tst;
            }
            path.push(reverse_state[st]);
            float min_inf_cost = 0;
            //cout << twa_prd_->format_state(reverse_state[st]) << endl;//twa_prd_->format_state(st) << endl;
            while(!path.empty()){
                cout << twa_prd_->format_state(path.top()) << endl;//twa_prd_->format_state(st) << endl;
                min_inf_cost += state_cost_map_[path.top()->hash()];
                path.pop();
            }
            cout << "\noptimal path dist: " << optimal_cost << endl;
            cout << "\noptimal path cost: " << min_inf_cost << endl;
//            for(int i=0; i<100; i++){
//                cout << todo_q.top().a_star_cost_ << endl;
//                todo_q.pop();
//            }
        }else{
            std::cout << "\nNOT FOUND PLAN ****\n";
        }

        return twa_prd_;

    }

    spot::twa_ptr find_optimal_path() {
        
        std::cout << "*** in: find_optimal_path_A_star\n";
        
        std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>*
                todo_q = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
        std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>*
                todo_q_cpy;// = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
        std::set<size_t> visited = std::set<size_t>();
        std::map<size_t,size_t> reverse = std::map<size_t,size_t>();
        std::map<size_t,float> state_cost_map = std::map<size_t,float>();
        std::map<size_t,float> total_cost_map = std::map<size_t,float>();
        std::map<size_t,const spot::state*> 
                reverse_state = std::map<size_t,const spot::state*>();
        size_t target;
        size_t start;
        std::pair<const spot::state*,float> item = 
                std::make_pair(twa_prd_->get_init_state(),0);
        std::cout << "init state: " << twa_prd_->format_state(twa_prd_->get_init_state()) << endl;
        todo_q->push(a_star_node(twa_prd_->get_init_state()->hash(),0,0));
        start = item.first->hash();
        state_cost_map[start] = 0;
        total_cost_map[start] = 0;
        visited.insert(item.first->hash());
        reverse[item.first->hash()] = item.first->hash();
        reverse_state[item.first->hash()] = item.first;
        bool found_plan = false;
        const spot::state* cs;//current state
        float min_c = 0;
        float optimal_cost = -1;
        int steps = 100;
        while(!todo_q->empty())
        {
            //auto start = chrono::steady_clock::now();

            a_star_node node(todo_q->top());
            todo_q->pop();
            visited.insert(node.state_hash_);
            cs = reverse_state[node.state_hash_];//do not need the state, hash is fine
            //min_c = node.primary_cost_;//not solid
            min_c = total_cost_map[node.state_hash_];//solid
            
            twa_succ_iterator_product_kripke* tit = 
                    down_cast<twa_succ_iterator_product_kripke*>
                    (twa_prd_->succ_iter(cs));
            //spot::twa_succ_iterator* tit = twa_prd_->succ_iter(cs);
            if(!tit->first()){
                twa_prd_->release_iter(tit);
                continue;
            }
            while(!tit->done() && tit->cond()!=bddfalse)
            {

                const spot::state_product* tit_dst = tit->dst();
                twa_succ_iterator_product_kripke* tmp = 
                    down_cast<twa_succ_iterator_product_kripke*>
                    (twa_prd_->succ_iter(tit->dst()));
                if(!tmp->first()){
                    tit->next();
                    twa_prd_->release_iter(tmp);
                    continue;
                }
                else if(tmp->cond()==bddfalse){
                    tit->next();
                    twa_prd_->release_iter(tmp);
                    continue;
                }
                
//                if(twa_prd_->right_acc().accepting(tmp->acc()))
//                {
//                    cout << "cond: " << tmp->acc() << endl;
//                    target = tmp->dst()->hash();
//                    if(target != cs->hash()){
//                        reverse[target] = cs->hash();
//                        reverse_state[target] = tmp->dst();
//                    }
//                    optimal_cost = min_c;
//                    found_plan = true;
//                    break;
//                }
                if(twa_prd_->right_acc().accepting(tit->acc()) && 
                        tit->cond() != bddfalse)
                {
                    cout << "cond: " << tit->acc() << endl;
                    target = tit->dst()->hash();
                    if(target != cs->hash())
                    {
                        reverse[target] = cs->hash();
                        reverse_state[target] = tit->dst();
                    }
                    optimal_cost = min_c;
                    found_plan = true;
                    break;
                }
                if(visited.find(tit_dst->hash()) == visited.end()
                        ||  (visited.find(tit_dst->hash()) != visited.end() 
                            &&
                            total_cost_map[tit_dst->hash()] > (min_c+(tit->inf()+tit->sup())/2.0)
                            //total_cost_map[tit_dst->hash()] > (min_c+tit->cost_inf())
                            )
                  )
                {

                    //NO HURISTIC
                    todo_q->push(a_star_node(tit_dst->hash(),
                            //min_c+tit->cost_inf(), min_c+tit->cost_sup()));
                            //min_c+(tit->inf()+tit->sup())/2, (tit->cost_inf()+tit->cost_sup())/2));
                        min_c+tit->cost_inf(), min_c+tit->cost_sup()));
                            //min_c+tit->loc_dist(), tit->loc_dist()));
            total_cost_map[tit_dst->hash()] = min_c+(tit->inf()+tit->sup())/2.0;
                    //total_cost_map[tit_dst->hash()] = min_c+tit->cost_inf();
                    ////total_cost_map[tit_dst->hash()] = min_c+(tit->cost_inf()+tit->cost_sup())/2;
                    reverse[tit_dst->hash()] = cs->hash();
                    state_cost_map[tit_dst->hash()] = (tit->inf());
                    if(reverse_state.find(tit_dst->hash())==reverse_state.end())
                        reverse_state[tit_dst->hash()] = tit_dst;
                    else
                        tit_dst->destroy();
                    //state_cost_map[tit->dst()->hash()] = (tit->inf() + tit->sup())/2;

                }

                twa_prd_->release_iter(tmp);

                if(!tit->next())
                    break;   
            }
            twa_prd_->release_iter(tit);
            
            if(found_plan)
                break;
            
            //auto end = chrono::steady_clock::now();
            //cout << "time ms: " << chrono::duration_cast<chrono::microseconds>(end - start).count() << endl;
            if(todo_q->size() > MAX_Q_SIZE_)
            {
                    //const state_product* s = down_cast<const state_product*>(reverse_state[todo_q->top().state_hash_]);

                std::cout << "\nreverse size: " << reverse.size() 
                    << " todo_q size: " << todo_q->size() 
                    << " visited size: " << visited.size() << endl <<endl;
                cout << "cleaning priority queue... ";
                auto start = chrono::steady_clock::now();
                todo_q_cpy = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
                for(int i=0; i < NUM_CPY_FRM_Q_; i++)
                {
                    todo_q_cpy->push(todo_q->top());
                    todo_q->pop();
                }
                //todo: maybe visited map also must be updated!
                delete todo_q;
                todo_q = new std::priority_queue<a_star_node, std::vector<a_star_node>, a_star_costcomparison>();
                swap(todo_q,todo_q_cpy);
                delete todo_q_cpy;
                auto end = chrono::steady_clock::now();
                cout << "elapsed time in microseconds: " << chrono::duration_cast<chrono::microseconds>(end - start).count() << endl;

            }
        }
        if(found_plan){
            std::cout << "\nFOUND AN OPTIMAL PLAN ****\n" << "reverse size: " << reverse.size() 
                    << " todo_q size: " << todo_q->size() 
                    << " visited size: " << visited.size() << endl;

            std::stack<const spot::state*> path = std::stack<const spot::state*> ();
            
            size_t st = target;
            while(st != start){
                path.push(reverse_state[st]);
                st = reverse[st];
            }
            path.push(reverse_state[st]);
            float min_inf_cost = 0;
            //cout << twa_prd_->format_state(reverse_state[st]) << endl;//twa_prd_->format_state(st) << endl;
            while(!path.empty()){
                cout << twa_prd_->format_state(path.top()) << endl;//twa_prd_->format_state(st) << endl;
                min_inf_cost += state_cost_map[path.top()->hash()];
                path.pop();
            }
            cout << "\noptimal path dist: " << optimal_cost << endl;
            cout << "\noptimal path cost: " << min_inf_cost << endl;
//            for(int i=0; i<100; i++){
//                cout << todo_q.top().a_star_cost_ << endl;
//                todo_q.pop();
//            }
        }else{
            std::cout << "\nNOT FOUND PLAN ****\n";
        }
        return twa_prd_;
    }
    

        
private:
    spot::twa_product_ptr twa_prd_;
    int MAX_Q_SIZE_ = 20000;//50000;
    int NUM_CPY_FRM_Q_ = 10000;//10000;
    std::map<size_t,std::stack<size_t>> reverse_;
    float cycle_cost_;
    std::map<size_t,float> state_cost_map_;

    //auto cmp = [](std::pair<spot::state*,float> left, std::pair<spot::state*,float> right) 
    //{ return (left.second) < (right.second);};
    //prqueue todo;//(costcomparison);        
};  
  

  //twa.cc
  
    // Remove Fin-acceptance and alternation.
    const_twa_ptr remove_fin_maybe(const const_twa_ptr& a)
    {
      auto aa = std::dynamic_pointer_cast<const twa_graph>(a);
      if ((!aa || aa->is_existential()) && !a->acc().uses_fin_acceptance())
        return a;
      if (!aa)
        aa = make_twa_graph(a, twa::prop_set::all());
      return remove_fin(remove_alternation(aa));
    }
    
  twa_run_ptr
  twa::intersecting_run(const_twa_ptr other, bool from_other) const 
  {
      cout << "*** in -> intersecting_run \n";
      cout << "\n\nusing TO Lattice:\n" << *shared_intervals_->getTo_lattice_() << endl<<endl;

    auto a = shared_from_this();
    if (from_other)
      other = remove_fin_maybe(other);
    else
      a = remove_fin_maybe(a);
    //-----------------------------------
    if(true){
        auto start = chrono::steady_clock::now();
        minimal_cost minc(mv::spot::otf_product(a, other));
        //minc.find_optimal_path();
        spot::twa_ptr res = minc.find_optimal_path_A_star();
        auto end = chrono::steady_clock::now();
        cout << "\nExecution time in milliseconds: " << chrono::duration_cast<chrono::milliseconds>(end - start).count() << endl;
        exit(0);
    }
    //-----------------------------------
    auto run = mv::spot::otf_product(a, other)->accepting_run();
    //auto run = spot::otf_product(a, other)->accepting_run();
    if (!run)
      return nullptr;
    return run->project(from_other ? other : a);
  }
}//spot namespace
//}//mv namespace
