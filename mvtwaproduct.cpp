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
#include "mvtwaproduct.h"
//#include "mv_interval.h"


using namespace std;

//namespace mv{

namespace spot
{
    using namespace spot;

  static spot::bdd_dict_ptr shared_dict;  
  static mvspot::mv_interval* shared_intervals;
    
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

      void recycle(const const_twa_ptr& l, twa_succ_iterator* left,
                   const_twa_ptr r, twa_succ_iterator* right)
      {
        l->release_iter(left_);
        left_ = left;
        r->release_iter(right_);
        right_ = right;
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
        return new(pool_->allocate()) state_product(left_->dst(),
                                                    right_->dst(),
                                                    pool_);
      }

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

      virtual ~twa_succ_iterator_product_kripke()
      {
      }

      bool next_non_false_() override
      {
        // All the transitions of left_ iterator have the
        // same label, because it is a Kripke structure.
        std::pair<mvspot::mv_interval*,bdd> itv_res;
        //current_cond_ = bddfalse;
        
        bdd l = left_->cond();
        assert(!right_->done());
        //std::cout << "acc: " << this->right_->acc().has(0)<< endl;
        do
          {
            bdd r = right_->cond();
            itv_res = mvspot::interval_bdd::apply_and(r, l, shared_dict);   
            //std::cout << "****RESULT " << itv_res.first->get_as_str() << "isFalse:" << itv_res.first->isFalse()<< endl;
            bdd current_cond = l & r;
            //current_cond_ = bddfalse;
            if(!itv_res.first->isFalse() && current_cond != bddfalse)
            //if(current_cond != bddfalse)
            {
                cost_inf_ = 2 + 1 - itv_res.first->getButtom()->getValue();
                cost_sup_ = 2 + 1 - itv_res.first->getTop()->getValue();
                //cout << "cost: " << cost_inf_ << " , " << cost_sup_ << endl;
                current_cond_ = current_cond;//itv_res.second;
                current_cond_ = bddtrue;//****************test
                return true;
            }
          }
        while (right_->next());
        return false;

      }

      bool next() override
      {
        if (left_->next())
            return true;
        left_->first();
        if (right_->next())
          return next_non_false_();
        return false;
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

      acc_cond::mark_t acc() const override
      {
        return right_->acc();
      }

    protected:
      bdd current_cond_;
      float cost_inf_ = 999999999;
      float cost_sup_ = 999999999;
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

    shared_dict = get_dict();
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
    
    //mvspot::mv_kripke* mvk = dynamic_cast<mvspot::mv_kripke*>(&left);
    
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
        it->recycle(left_, li, right_, ri);
        iter_cache_ = nullptr;
        return it;
      }

    fixed_size_pool* p = const_cast<fixed_size_pool*>(&pool_);
    if (left_kripke_)
      return new twa_succ_iterator_product_kripke(li, ri, this, p);
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
            + right_->format_state(s->right()));
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

class costcomparison
{
  bool reverse;
public:
  costcomparison(const bool& revparam=true)
    {reverse=revparam;}
  bool operator() (const std::pair<const spot::state*,float>& lhs, const std::pair<const spot::state*,float>& rhs) const
  {
    if (reverse) return (lhs.second > rhs.second);
    else return (lhs.second < rhs.second);
  }
};  

template<
    class T,
    class Container = std::vector<T>,
    class Compare = costcomparison//std::less<typename Container::value_type>
> class MvQueue : public std::priority_queue<T, Container, Compare>
{
public:
    typedef typename
        std::priority_queue<
        T,
        Container,
        Compare>::container_type::const_iterator const_iterator;

    bool find_replace(const T&val) 
    {
        auto first = this->c.cbegin();
        auto last = this->c.cend();
        while (first!=last) {
            if ((*first).first->hash()==val.first->hash() && (*first).second>val.second){
                //this->c.erase(*first);
               
                //this->c.erase(std::remove(this->c.cbegin(), this->c.cend(), (*first)), this->c.cend());
                //this->c.push_back(val);
                return true;
            }
            ++first;
        }
        return false;
    }
    
    const_iterator begin() const {
        return this->c.cbegin();
    }

    const_iterator end() const {
        return this->c.cend();
    }

};

class minimal_cost {
    typedef MvQueue<std::pair<const spot::state*,float>, 
     std::vector<std::pair<const spot::state*,float>>, costcomparison> prqueue;
    using spair = std::pair<const spot::state*,float>;
    typedef std::pair<float,const spot::state*> mpair;
public:
    minimal_cost(spot::twa_product_ptr twa_prd){
        twa_prd_ = twa_prd;
    }
    
    void find_optimal_path() {
        //todo = prqueue();
        std::multimap<float,const spot::state*> explore = std::multimap<float,const spot::state*>();
        //std::priority_queue<float, std::vector<float>, std::less<float>> 
        //cost_q = std::priority_queue<float, std::vector<float>, std::less<float>>();
        std::priority_queue<float, std::vector<float>, std::greater<float>> 
                cost_q = std::priority_queue<float, std::vector<float>, std::greater<float>>();
        std::set<size_t> visited = std::set<size_t>();
        std::map<size_t,size_t> reverse = std::map<size_t,size_t>();
        std::map<size_t,const spot::state*> reverse_state = std::map<size_t,const spot::state*>();
        size_t target;
        size_t start;
        std::pair<const spot::state*,float> item = 
                std::make_pair(twa_prd_->get_init_state(),0);
        std::cout << "init: " << twa_prd_->format_state(twa_prd_->get_init_state()) << endl;
        //todo.push(item);
        explore.insert(std::make_pair<float,const spot::state*>(0,twa_prd_->get_init_state()));
        cost_q.push(0);
        start = item.first->hash();
        visited.insert(item.first->hash());
        reverse[item.first->hash()]=item.first->hash();
        reverse_state[item.first->hash()]=item.first;
        bool found_plan = false;
        const spot::state* cs;
        float min_c = 0;
        float optimal_cost = -1;
        //while(!todo.empty())
        while(!explore.empty())
        {
            min_c = cost_q.top();
            cost_q.pop();
            cs = explore.find(min_c)->second;
            //std::cout << ": " << twa_prd_->format_state(cs) << endl;
            //std::cout << "size: " << explore.size() << " min: " << min_c << endl;
            explore.erase(explore.find(min_c));
            visited.insert(cs->hash());
            twa_succ_iterator_product_kripke* tit = 
                    static_cast<twa_succ_iterator_product_kripke*>
                    (twa_prd_->succ_iter(cs));
            //spair node = todo.top();
            //todo.pop();
            //visited.insert(node.first->hash());
            //twa_succ_iterator_product_kripke* tit = 
            //        static_cast<twa_succ_iterator_product_kripke*>
            //        (twa_prd_->succ_iter(node.first));
            if(!tit->first())
                continue;
            while(!tit->done())
            {
                reverse_state[tit->dst()->hash()] = tit->dst();
                //if(tit->acc().has(0))
                if(twa_prd_->right_acc().accepting(tit->acc()))
                {
                    cout << tit->acc()<< endl;
                    target = tit->dst()->hash();
                    reverse[target] = cs->hash();
                    //reverse[target] = node.first->hash();
                    optimal_cost = min_c;
                    found_plan = true;
                    break;
                }
                if(visited.find(tit->dst()->hash())==visited.end()){
                    reverse[tit->dst()->hash()] = cs->hash();
                    cost_q.push(min_c+tit->cost_inf());
                    explore.insert(std::make_pair<float,const spot::state*>
                            (min_c+tit->cost_inf(),tit->dst()));
                    
                    //reverse[tit->dst()->hash()] = node.first->hash();
                    //todo.push(std::make_pair(tit->dst(), node.second + tit->cost_inf()));
                }else{
                }
                //while(!tit->done() && tit->cond()==bddfalse)
                    tit->next();    
                //if(!tit->next())  break;
            }
            if(found_plan)
                break;
        }
        if(found_plan){
            std::cout << "\nFOUND AN OPTIMAL PLAN ****\n" << "reverse size: " << reverse.size() 
                    << " explore size: " << explore.size() 
                    << " visited size: " << visited.size() << endl;
            //while(!todo.empty()){
            //    std::cout << "todo: " << twa_prd_->format_state(todo.top().first) << " cost: " << todo.top().second << endl;
            //    todo.pop();
            //}
//            while(!cost_q.empty()){
//                std::cout << "cost: " << cost_q.top() << endl;
//                cost_q.pop();
//            }
            std::stack<const spot::state*> path = std::stack<const spot::state*> ();
            
            size_t st = target;
            while(st != start){
                path.push(reverse_state[st]);
                //cout << twa_prd_->format_state(reverse_state[st]) << endl;//twa_prd_->format_state(st) << endl;
                st = reverse[st];
            }
            path.push(reverse_state[st]);
            //cout << twa_prd_->format_state(reverse_state[st]) << endl;//twa_prd_->format_state(st) << endl;
            while(!path.empty()){
                cout << twa_prd_->format_state(path.top()) << endl;//twa_prd_->format_state(st) << endl;
                path.pop();
            }
            cout << "\noptimal path cost: " << optimal_cost << endl;
        }else{
            std::cout << "\nNOT FOUND PLAN ****\n";
        }
    }
    
private:
    spot::twa_product_ptr twa_prd_;
    //auto cmp = [](std::pair<spot::state*,float> left, std::pair<spot::state*,float> right) 
    //{ return (left.second) < (right.second);};
    prqueue todo;//(costcomparison);        
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
    //-------
    minimal_cost minc(mv::spot::otf_product(a, other));
    minc.find_optimal_path();
    exit(0);
    //-------
    auto run = mv::spot::otf_product(a, other)->accepting_run();
    //auto run = spot::otf_product(a, other)->accepting_run();
    if (!run)
      return nullptr;
    return run->project(from_other ? other : a);
  }
}//spot namespace
//}//mv namespace
