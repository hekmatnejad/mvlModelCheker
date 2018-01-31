/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   mv_interval.cpp
 * Author: mhekmatnejad
 * 
 * Created on January 8, 2018, 2:01 AM
 */

#include "MvLtlModel.h"
#include <spot/twa/taatgba.hh>
#include <spot/twa/formula2bdd.hh>

using namespace spot;
//#include "mv_interval.h"
namespace mvspot
{
    
mv_interval::mv_interval(string name)
{
    name_ = name;
    map_intervals_ = new std::map<string,mv_interval*>();
    map_all_intervals_ = new std::map<std::pair<float,float>,mv_interval*>();

}
//this constructor is for the main interval as a TO lattice that contains other intervals
mv_interval::mv_interval(string name, lattice_node* intervals, int size) throw() :
name_(name), intervals_(intervals), int_size_(size) 
{
    is_TO_lattice_container_ = true;
    map_intervals_ = new std::map<string,mv_interval*>();
    map_all_intervals_ = new std::map<std::pair<float,float>,mv_interval*>();
    if(intervals==nullptr || size < 2)
        throw(new mv_exception("nodes and size must not be nothing!"));
    to_lattice_ = new mv_lattice(&intervals[0], &intervals[size-1]);
    lattice_node* node = to_lattice_->getTop_();
    for(int i=1; i<size-1; i++){
        if(node->compare(&intervals[i])<=0)
            throw(new mv_exception("Ascending order among interval nodes is not preserved."));
        to_lattice_->getNodes_()->insert(&intervals[i]);
        node->add_above_of(&intervals[i]);
        node = &intervals[i];
    }
    node->add_above_of(&intervals[size-1]);
    top_ = &intervals[0];
    buttom_ = &intervals[size-1];
    (*map_intervals_)[get_as_str()] = this;
}

mv_interval::mv_interval(string name, float low, float high): mv_interval(name) 
{
    //mv_interval();
    buttom_ = new lattice_node("low", low);
    top_ = new lattice_node("high", high);
    top_->add_above_of(buttom_);
    to_lattice_ = new mv_lattice(buttom_, top_);
    (*map_intervals_)[get_as_str()] = this;
}

mv_interval* mv_interval::add_interval(string symbol, float low, float high){
    if(low > high)
        throw(new mv_exception("low of interval must be less than or equals to the high."));
    //lattice_node* ln = new lattice_node("low", low);
    //lattice_node* rn = new lattice_node("high", high);
    //mv_lattice* interval;
    //ln->add_bellow_of(rn);
    //interval = new mv_lattice(ln, rn);
    mv_interval* interval = new mv_interval(get_as_str(low, high), low, high);
    (*map_intervals_)[interval->get_as_str()] = interval;
    (*map_all_intervals_)[std::make_pair(low,high)] = interval;
    //cout << ">>> " << get_as_str(low, high) << " "<< (*map_intervals_)[interval->get_as_str()]->name_<<endl;
    return interval;
}

//mv_lattice* mv_interval::get_interval(string symbol){
//    if(map_intervals_->find(symbol)==map_intervals_->end())
//        return nullptr;
//    return ((*map_intervals_)[symbol]);
//}

//void mv_interval::add_interval(float low, float high){
//    if(low > high)
//        throw(new mv_exception("low of interval must be less than or equals to the high."));
//    mv_interval* interval;
//    interval = new mv_interval(low, high);
//    (*map_intervals_)[symbol] = interval;
//    (*map_all_intervals_[std::make_pair(low,high)]) = interval;
//}

//mv_interval* mv_interval::get_interval(string symbol){
//    if(map_intervals_->find(symbol)==map_intervals_->end())
//        return nullptr;
//    return ((*map_intervals_)[symbol]);
//}

mv_interval* mv_interval::get_interval(float low, float high){
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end())
        return nullptr;
    return ((*map_all_intervals_)[std::make_pair(low,high)]);
}

mv_interval* mv_interval::parse_string_to_interval(string f){
    string l, r;
    l = f.substr(f.find_first_of("[") + 1, f.find_first_of(",") - f.find_first_of("[") - 1);
    r = f.substr(f.find_first_of(",") + 1, f.find_first_of("]") - f.find_first_of(",") - 1);
    std::string::iterator end_pos = std::remove(l.begin(), l.end(), ' ');
    l.erase(end_pos, l.end());
    end_pos = std::remove(r.begin(), r.end(), ' ');
    r.erase(end_pos, r.end());
    float low = std::stof(l);
    float high = std::stof(r);
    if((*map_intervals_)[f] == 0){
        if (get_interval(low, high) == 0){
            //return new mv_interval(f.substr(0,f.find('=')),low, high);
            return new mv_interval(f,low, high);
        }
    }

    return get_interval(low, high);
}


lattice_node* mv_interval::getTop(){
    return top_;
}

lattice_node* mv_interval::getButtom(){
    return buttom_;
}

mv_interval::mv_interval(const mv_interval& orig) {
    cout << "in mv_interval::mv_interval copy constructor\n\n";
    is_TO_lattice_container_ = orig.is_TO_lattice_container_;
    intervals_ = orig.intervals_;
    name_ = orig.name_;
    top_ = orig.top_;
    buttom_ = orig.buttom_;
    int_size_ = orig.int_size_;
    to_lattice_ = orig.to_lattice_;
    map_all_intervals_ = orig.map_all_intervals_;
    map_intervals_ = orig.map_intervals_;
}

mv_interval::~mv_interval() {
    cout << "in ~mv_interval\n";
    if(map_intervals_!=0)
        delete map_intervals_;
    if(map_all_intervals_!=0)
        delete map_all_intervals_;
    //delete intervals_;
    if(to_lattice_!=0)
        delete to_lattice_;
    if(intervals_==0){
        delete top_;
        delete buttom_;
    }
    cout << "mv_interval::~mv_interval() called successfully.\n";
}

string mv_interval::get_as_str(){
    return get_as_str(getButtom()->getValue(), getTop()->getValue());
}

string mv_interval::get_as_str(float low, float high){
    //string res = getName() + "=[";
    string res = "[";
    string num = std::to_string(low);
    while(num.size()>1 && num.at(num.size()-1)=='0')
        num = num.substr(0,num.size()-1);
    if(num.at(num.size()-1)=='.')
        num = num.substr(0,num.size()-1);
    res += num + ",";
    num = std::to_string(high);
    while(num.size()>1 && num.at(num.size()-1)=='0')
        num = num.substr(0,num.size()-1);
    if(num.at(num.size()-1)=='.')
        num = num.substr(0,num.size()-1);
    res += num + "]";
    return res;
}


std::pair<float,float> mv_interval::get_as_pair(){
    std::pair<float,float> res = std::make_pair(getButtom()->getValue(),
            getTop()->getValue());
    return res;
}


//lattice operators

float mv_interval::complement_mv(float given){
    return MAX_VAL_ - given;
}

mv_interval* mv_interval::join_mv(mv_interval* left, mv_interval* right){
    
    float low = left->getButtom()->getValue() > right->getButtom()->getValue()?
                left->getButtom()->getValue() : right->getButtom()->getValue();
    float high = left->getTop()->getValue() > right->getTop()->getValue()?
                left->getTop()->getValue() : right->getTop()->getValue();
    //cout << "pair: " << low << " , " << high << endl;
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}

mv_interval* mv_interval::meet_mv(mv_interval* left, mv_interval* right){
    float low = left->getButtom()->getValue() < right->getButtom()->getValue()?
                left->getButtom()->getValue() : right->getButtom()->getValue();
    float high = left->getTop()->getValue() < right->getTop()->getValue()?
                left->getTop()->getValue() : right->getTop()->getValue();
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}

//mv_interval* mv_interval::not_mv(mv_interval* given);

mv_interval* mv_interval::not_mv(mv_interval* given){
    
    float high = complement_mv(given->getButtom()->getValue());
    float low = complement_mv(given->getTop()->getValue());
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}


//void mv_interval::negate_mv(mv_interval* given);



mv_interval* mv_interval::psi_mv(mv_interval* base, mv_interval* given){
    
    float b_low = base->getButtom()->getValue();
    float b_high = base->getTop()->getValue();
    float low = given->getButtom()->getValue();
    float high = given->getTop()->getValue();
    float new_low = MIN_VAL_;
    float new_high = MIN_VAL_;
    //std::cout << b_low << " " << b_high << " , " << low << " " << high << endl;
    if( (b_low==MIN_VAL_ && b_high==MAX_VAL_) || (b_low<=low && b_high==MAX_VAL_)){
        new_low = low;
        new_high = high;
    }
    else if ( b_high>=high && b_low==MIN_VAL_){
        new_low = complement_mv(high);
        new_high = complement_mv(low);
    }
    if(map_all_intervals_->find(std::make_pair(new_low,new_high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(new_low,new_high), new_low, new_high);
        (*map_all_intervals_)[std::make_pair(new_low, new_high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(new_low, new_high)];
    
}

//--------------------------------------------------------//

  bdd
  replace_formula_to_bdd(formula f, formula base, formula model, bool negate, const bdd_dict_ptr& d, void* owner)
  {
    auto recurse = [base, model, negate, &d, owner](formula f)
      {
        return replace_formula_to_bdd(f, base, model, negate, d, owner);
      };
    switch (f.kind())
      {
      case op::ff:
        return bddfalse;
      case op::tt:
        return bddtrue;
      case op::eword:
      case op::Star:
      case op::FStar:
      case op::F:
      case op::G:
      case op::X:
      case op::Closure:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::U:
      case op::R:
      case op::W:
      case op::M:
      case op::UConcat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::Concat:
      case op::Fusion:
      case op::AndNLM:
      case op::OrRat:
      case op::AndRat:
        SPOT_UNIMPLEMENTED();
      case op::ap:
        if(f == model){
            if(negate)
                return !bdd_ithvar(d->register_proposition(base, owner));
            else
                return bdd_ithvar(d->register_proposition(base, owner));
        }
        else
            return bdd_ithvar(d->register_proposition(f, owner));
      case op::Not:
        return bdd_not(recurse(f[0]));
      case op::Xor:
        return bdd_apply(recurse(f[0]), recurse(f[1]), bddop_xor);
      case op::Implies:
        return bdd_apply(recurse(f[0]), recurse(f[1]), bddop_imp);
      case op::Equiv:
        return bdd_apply(recurse(f[0]), recurse(f[1]), bddop_biimp);
      case op::And:
      case op::Or:
        {
          int o = bddop_and;
          bdd res = bddtrue;
          if (f.is(op::Or))
            {
              o = bddop_or;
              res = bddfalse;
            }
          unsigned s = f.size();
          for (unsigned n = 0; n < s; ++n)
            res = bdd_apply(res, recurse(f[n]), o);
          return res;
        }
      }
    SPOT_UNREACHABLE();
    return bddfalse;
  }

    mv_interval* interval_bdd::symbol_formual_to_interval(string formula){
        return shared_intervals_->parse_string_to_interval(formula);
    }

 spot::formula
  remove_negation_from_interval_formula(formula f, const bdd_dict_ptr& d)
  {
    auto recurse = [&d](formula f)
      {
        return remove_negation_from_interval_formula(f, d);
      };
    switch (f.kind())
      {
      case op::ff:
          return formula::ff();
      case op::tt:
          return formula::tt();
      case op::eword:
      case op::Star:
      case op::FStar:
      case op::F:
      case op::G:
      case op::X:
      case op::Closure:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::U:
      case op::R:
      case op::W:
      case op::M:
      case op::UConcat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::Concat:
      case op::Fusion:
      case op::AndNLM:
      case op::OrRat:
      case op::AndRat:
      case op::Xor://added by mohammad: here we are dealing for conjunctive formulas
      case op::Implies:
      case op::Equiv:
      case op::Or:
        SPOT_UNIMPLEMENTED();
      case op::ap:
            return f;
      case op::Not:
          if(f[0].ap_name().find("=[")==std::string::npos)
            return spot::formula::Not(recurse(f[0]));
          else{
              mvspot::mv_interval* itv = interval_bdd::symbol_formual_to_interval(f[0].ap_name());
              itv = itv->not_mv(itv);
              std::string sym_name = f[0].ap_name();
              sym_name = sym_name.substr(0,sym_name.find("=")+1);//found it :)
              sym_name += itv->getName();
              //cout << ">>>> negated " << f[0].ap_name() << " to " << sym_name << endl;
              return spot::formula::ap(sym_name);
          }
      case op::And:
        {
          std::vector<formula> v;
          unsigned s = f.size();
          for (unsigned n = 0; n < s; ++n)
            v.emplace_back(recurse(f[n]));
          return spot::formula::And(v);
        }
      }
    SPOT_UNREACHABLE();
    return nullptr;
  }
    
    
    spot::formula interval_bdd::simplify_conjuctive_formula(spot::formula f, const bdd_dict_ptr& d) {
        if (f.kind() == op::ap)
            return f;
        if (f.kind() != op::And)
            return f;
        //std::cout << "******************\n" << f << endl;
        std::map<string, mvspot::mv_interval*> map_itv = std::map<string, mvspot::mv_interval*>();
        std::vector<formula> v= std::vector<formula>();
        unsigned s = f.size();
        for (unsigned n = 0; n < s; ++n) {
            if (f[n].kind() == op::ap && f[n].ap_name().find('=') != std::string::npos) {
                //std::cout << f[n] << endl;
                mvspot::mv_interval* itv = shared_intervals_->parse_string_to_interval(f[n].ap_name());
                if (map_itv.find(f[n].ap_name().substr(0, f[n].ap_name().find('='))) == map_itv.end()) {
                    //itv = shared_intervals_->parse_string_to_interval(f[n].ap_name());
                    map_itv[f[n].ap_name().substr(0, f[n].ap_name().find('='))] = itv;
                } else{
                    //itv = shared_intervals_->parse_string_to_interval(f[n].ap_name());
                    //the same interval symbols in a conjunctive format must be joint
                    itv = itv->join_mv(map_itv[f[n].ap_name().substr(0, f[n].ap_name().find('='))], itv);
                    map_itv[f[n].ap_name().substr(0, f[n].ap_name().find('='))] = itv;
                }
            }else{
                v.emplace_back(f[n]);
            }
        }
        for(std::map<string, mvspot::mv_interval*>::iterator it = map_itv.begin(); it != map_itv.end(); ++it){
            //spot::formula f_new = spot::formula::ap((*it).first);
            spot::formula f_new = spot::formula::ap((*it).first+"="+((*it).second)->get_as_str());
            d->register_proposition(f_new,nullptr);
            v.emplace_back(f_new);
        }
        spot::formula res_f = spot::formula::And(v);
        //std::cout << "------------------\n" << res_f << endl;
        return res_f;
    }


  spot::formula
  replace_model_with_base(formula f, formula base, formula model, bool negate, const bdd_dict_ptr& d, void* owner)
  {
    auto recurse = [base, model, negate, &d, owner](formula f)
      {
        return replace_model_with_base(f, base, model, negate, d, owner);
      };
    switch (f.kind())
      {
      case op::ff:
          return formula::ff();
      case op::tt:
          return formula::tt();
      case op::eword:
      case op::Star:
      case op::FStar:
      case op::F:
      case op::G:
      case op::X:
      case op::Closure:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::U:
      case op::R:
      case op::W:
      case op::M:
      case op::UConcat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::Concat:
      case op::Fusion:
      case op::AndNLM:
      case op::OrRat:
      case op::AndRat:
      case op::Xor://added by mohammad: here we are dealing for conjunctive formulas
      case op::Implies:
      case op::Equiv:
      case op::Or:
        SPOT_UNIMPLEMENTED();
      case op::ap:
        if(f == model){
            if(negate)
                return spot::formula::Not(base);
            else
                return base;
        }
        else
            return f;
      case op::Not:
        return spot::formula::Not(recurse(f[0]));
      case op::And:
        {
          std::vector<formula> v;
          unsigned s = f.size();
          for (unsigned n = 0; n < s; ++n)
            v.emplace_back(recurse(f[n]));
          return spot::formula::And(v);
        }
      }
    SPOT_UNREACHABLE();
    return nullptr;
  }
    //static definition
    std::map<std::string,mv_interval*>* mvspot::interval_bdd::map_interval_base_ = new std::map<std::string,mv_interval*>();
    std::map<std::string,mv_interval*>* mvspot::interval_bdd::map_interval_model_ = new std::map<std::string,mv_interval*>();

    std::pair<spot::formula,spot::formula> 
    mvspot::interval_bdd::prepare_apply_and(spot::formula f_base, spot::formula f_model, 
            bool negate, spot::bdd_dict_ptr dict_){

        //cout << "simplify_conjuctive_formula -> " << f_base << endl;

        //cout << "simplify_conjuctive_formula <- " << f_base << endl;
        auto aps_base = std::unique_ptr<spot::atomic_prop_set>(spot::atomic_prop_collect(f_base));
        auto aps_model = std::unique_ptr<spot::atomic_prop_set>(spot::atomic_prop_collect(f_model));

        spot::formula replaced_f_p = f_model;
        spot::formula replaced_f_n = f_model;
        for (auto b_f: *aps_base)
        {
            string str_f = b_f.ap_name();
            std::size_t found = str_f.find('=');
            string sym_name;
            if(found!=std::string::npos){//found interval in base formula
                sym_name = str_f.substr(0,str_f.find('='));
                (*map_interval_base_)[str_f] = shared_intervals_->parse_string_to_interval(str_f);
                for(spot::formula m_f : *aps_model)
                {
                    string str_f_model = m_f.ap_name();
                    found = str_f_model.find(sym_name+"=");//look for the exact interval name
                    if(found != std::string::npos){//this is an important symbol
                        (*map_interval_model_)[str_f_model] = shared_intervals_->parse_string_to_interval(str_f_model);
                        replaced_f_p = replace_model_with_base(replaced_f_p, b_f, m_f, false, dict_, nullptr);
                        replaced_f_n = replace_model_with_base(replaced_f_n, b_f, m_f, true, dict_, nullptr);
                        break;
                    }
                }
                //---------
            }
  
            //cout << ">>> old formula:" << f_model << "\n>>> new formula: " << bdd_to_formula(model_f, dict_) << endl;
        }
        return std::make_pair(replaced_f_p,replaced_f_n);
    }

    void interval_bdd::simplify_interval_formula_twa(spot::twa_graph_ptr &aut) {
        std::vector<bool> seen(aut->num_states());
        std::stack<unsigned> todo; // Now storing edges numbers
        auto& gr = aut->get_graph();
        auto push_state = [&](unsigned state) {
            todo.push(gr.state_storage(state).succ);
            seen[state] = true;
        };
        push_state(aut->get_init_state_number());
        while (!todo.empty()) {
            unsigned edge = todo.top();
            todo.pop();
            if (edge == 0U) // No more outgoing edge
                continue;
            auto& e = gr.edge_storage(edge);

            todo.push(e.next_succ); // Prepare next sibling edge.
            if (!seen[e.dst])
                push_state(e.dst);
            //std::cout << e.src << "->" << e.dst << '\n';

            //---------------------//
            spot::formula f_base = bdd_to_formula(e.cond, aut->get_dict());
            std::vector<spot::formula> vec_f = std::vector<spot::formula>();
            //loop around DNF formula base
            if(f_base.kind() == op::Or){
                for(int i=0; i<f_base.size(); i++)
                    vec_f.emplace_back(f_base[i]);
            }
            else
                vec_f.emplace_back(f_base);  
            std::vector<spot::formula> formula_conj = std::vector<spot::formula>();
            for(std::vector<spot::formula>::iterator it = vec_f.begin(); it!= vec_f.end(); ++it)
            {
                map_interval_base_->clear();
                f_base = remove_negation_from_interval_formula((*it), aut->get_dict());
                f_base = simplify_conjuctive_formula(f_base, aut->get_dict());
                formula_conj.push_back(f_base);
            }        
            spot::formula new_f = spot::formula::Or(formula_conj);


            //aut->edge_data(srcit).cond = spot::formula_to_bdd(new_f,aut->get_dict(),NULL);
            e.cond = spot::formula_to_bdd(new_f,aut->get_dict(),NULL);
            //---------------------//

        }
    }

    void interval_bdd::simplify_interval_formula_twa_graph(spot::twa_graph_ptr &aut)
    {
        
        /*
         * DFS traversing the automaton
         */
        spot::state_unicity_table seen;
        std::stack<std::pair<const spot::twa_graph_state*,
                spot::twa_succ_iterator*>> todo;

        // push receives a newly-allocated state and immediately store it in
        // seen.  Therefore any state on todo is already in seen and does
        // not need to be destroyed.
        auto push = [&](const spot::twa_graph_state * s) {
            if (seen.is_new(s)) {
                spot::twa_succ_iterator* it = aut->succ_iter(s);
                if (it->first())
                    todo.emplace(s, it);
                else // No successor for s
                    aut->release_iter(it);
            }
        };

        push(aut->get_init_state());

        while (!todo.empty()) {
            const spot::twa_graph_state* src = todo.top().first;
            spot::twa_succ_iterator* srcit = todo.top().second;
            const spot::twa_graph_state* 
                    dst = down_cast<const spot::twa_graph_state*>(srcit->dst());

            //---------------------//
        
        spot::formula f_base = bdd_to_formula(srcit->cond(), aut->get_dict());
        std::vector<spot::formula> vec_f = std::vector<spot::formula>();
        //loop around DNF formula base
        if(f_base.kind() == op::Or){
            for(int i=0; i<f_base.size(); i++)
                vec_f.emplace_back(f_base[i]);
        }
        else
            vec_f.emplace_back(f_base);  
        std::vector<spot::formula> formula_conj = std::vector<spot::formula>();
        for(std::vector<spot::formula>::iterator it = vec_f.begin(); it!= vec_f.end(); ++it)
        {
            map_interval_base_->clear();
            f_base = remove_negation_from_interval_formula((*it), aut->get_dict());
            f_base = simplify_conjuctive_formula(f_base, aut->get_dict());
            formula_conj.push_back(f_base);
        }        
        spot::formula new_f = spot::formula::Or(formula_conj);
        
        
            aut->edge_data(srcit).cond = spot::formula_to_bdd(new_f,aut->get_dict(),NULL);
            //---------------------//

            //std::cout << aut->format_state(src) << "->"
            //        << aut->format_state(dst) << '\n';
            // Advance the iterator, and maybe release it.
            if (!srcit->next()) {
                aut->release_iter(srcit);
                todo.pop();
            }
            push(dst);
        }    
    
    }
    
    std::pair<mv_interval*,bdd> interval_bdd::apply_and(bdd base, bdd model, spot::bdd_dict_ptr dict_){
        
        map_interval_base_->clear();
        map_interval_model_->clear();
        
        spot::formula f_base = bdd_to_formula(base, dict_);
        spot::formula f_model = bdd_to_formula(model, dict_);

        std::vector<spot::formula> vec_f = std::vector<spot::formula>();
        //loop around DNF formula base
        if(f_base.kind() == op::Or){
            for(int i=0; i<f_base.size(); i++)
                vec_f.emplace_back(f_base[i]);
        }
        else
            vec_f.emplace_back(f_base);
        
        bdd res_bdd_p = bddfalse;
        bdd res_bdd_n = bddfalse;
        bdd base_bdd = bddfalse;
        bdd m_bdd_p = bddfalse;
        bdd m_bdd_n = bddfalse;
        int cnt = 0;
        for(std::vector<spot::formula>::iterator it = vec_f.begin(); it!= vec_f.end(); ++it){
            f_base = (*it);
            //cout << "1>>>>> " << (*it) << endl;
            
            //note: this preprocessing is no longer needed because
            //I have simplified the formula automaton in advance
            //f_base = remove_negation_from_interval_formula((*it), dict_);
            //f_base = simplify_conjuctive_formula(f_base, dict_);
            
            //cout << "2>>>>> " << f_base << endl;
            std::pair<spot::formula,spot::formula> res_f = 
                    prepare_apply_and(f_base, f_model, true, dict_);
            //cout << "3>>>>> " << f_model << endl;
            //cout << "4>>>>> " << res_f.first << endl;
            //cout << "4>>>>> " << res_f.second << endl;
            bdd f_bdd = spot::formula_to_bdd(f_base, dict_, nullptr);
            base_bdd |= f_bdd;
            
            m_bdd_p |= spot::formula_to_bdd(res_f.first, dict_, nullptr);
            m_bdd_n |= spot::formula_to_bdd(res_f.second, dict_, nullptr);
            //cout << ++cnt << endl;
            
        }
        //cout << "@@@@ base_bdd: " << spot::bdd_to_formula(base_bdd, dict_) << endl;
        //cout << "@@@@ m_bdd_p:  " << spot::bdd_to_formula(m_bdd_p, dict_) << endl;
        //cout << "@@@@ m_bdd_n: " << spot::bdd_to_formula(m_bdd_n, dict_) << endl;
        res_bdd_p = (base_bdd & m_bdd_p);
        res_bdd_n = (base_bdd & m_bdd_n);

        if(res_bdd_p != bddfalse)    
            res_bdd_p = bddtrue;
        if(res_bdd_n != bddfalse)    
            res_bdd_n = bddtrue;
        
        
        if(res_bdd_p == bddfalse){//ok
            return std::make_pair(shared_intervals_->get_interval(0,0), bddfalse);//check for nullptr
        }
        
        if(res_bdd_n == bddtrue){
            //std::cout << "********************\n";
            return std::make_pair(shared_intervals_->get_interval(1,1), bddtrue);
        }
            
        if(res_bdd_n == bddfalse && res_bdd_p == bddtrue){
            //cout << "@@@@ base_bdd:  " << spot::bdd_to_formula(base_bdd, dict_) << endl;
            //cout << "@@@@ m_bdd_p:   " << spot::bdd_to_formula(m_bdd_p, dict_) << endl;
            //cout << "@@@@ m_bdd_n:   " << spot::bdd_to_formula(m_bdd_n, dict_) << endl;
            //cout << "@@@@ res_bdd_p: " << spot::bdd_to_formula(res_bdd_p, dict_) << endl << endl << endl;;
            string str_sym_b;
            string str_sym_m;
            mvspot::mv_interval* itv = shared_intervals_->get_interval(0,0);
            //cout << "SIZE: " << map_interval_base_->size() << " " << map_interval_model_->size()<<endl;
            for(std::map<string,mvspot::mv_interval*>::iterator it_base=map_interval_base_->begin();
                    it_base!=map_interval_base_->end(); ++it_base){
                for(std::map<string,mvspot::mv_interval*>::iterator it_model=map_interval_model_->begin();
                        it_model!=map_interval_model_->end(); ++it_model){
                    str_sym_b = (*it_base).first;
                    str_sym_m = (*it_model).first;
                    //check for same interval symbols
                    if( str_sym_b.substr(0,str_sym_b.find("=")).compare(
                            str_sym_m.substr(0,str_sym_m.find("=")))==0)
                    {
                        //std::cout << "\n*%*%* " << (*it_base).first << " " << (*it_model).first <<endl ;
                        //std::cout << "*%*%* " << (*it_base).second->get_as_str() << " " << (*it_model).second->get_as_str() <<endl <<endl;
                        itv = itv->join_mv(itv,itv->psi_mv(
                                (*it_base).second,(*it_model).second));
                    }
                }
            }
            //std::string br = itv->isFalse()? " IsFalse" : " NoFalse";
            //std::cout << "---itv: " << itv->getName() << " " << itv->get_as_str() << br << endl; 
            return std::make_pair(itv, (base & model));
            //return std::make_pair(shared_intervals_->get_interval(0.5,0.5), (base & model));
            //return shared_intervals_->get_interval(0.5,0.5);//TEST TEST TEST
        }

        //cout << "\n@@@@ res_bdd_p: " << spot::bdd_to_formula(res_bdd_p, dict_) << endl<<endl;;

        //return shared_intervals_->add_interval("WWWWWWWWWW",0.3,0.3);//TEST TEST TEST
        std::cout << "\nWRONG RESULT!!!!\n";
        return std::make_pair(nullptr,bddfalse);
        
     }


//--------------------------------------------------------//

// Convert a BDD which is known to be a conjunction into a formula. (taken form formula2bdd.cc)
static spot::formula
conj_to_formula(bdd b, const spot::bdd_dict_ptr d)
{
  if (b == bddfalse)
    return spot::formula::ff();
  std::vector<spot::formula> v;
  while (b != bddtrue)
    {
      int var = bdd_var(b);
      const spot::bdd_dict::bdd_info& i = d->bdd_map[var];
      assert(i.type == spot::bdd_dict::var);
     spot::formula res = i.f;

      bdd high = bdd_high(b);
      if (high == bddfalse)
        {
          res = spot::formula::Not(res);
          b = bdd_low(b);
        }
      else
        {
          // If bdd_low is not false, then b was not a conjunction.
          assert(bdd_low(b) == bddfalse);
          b = high;
        }
      assert(b != bddfalse);
      v.emplace_back(res);
    }
  return spot::formula::And(v);
}
    
mv_interval* create_interval_set(string name, string prefix, int num_nodes)
{
    lattice_node* nodes;
    nodes = new lattice_node[num_nodes];
    for(int i=0; i<num_nodes; i++){
        nodes[i].setName(prefix+"_"+std::to_string(i));
        nodes[i].setValue((float(num_nodes-i-1))/(num_nodes-1));
    }
    mv_interval* itv = new mv_interval(name, nodes, num_nodes);
    
    return itv;
}

void test_intervals(){

    //mv_interval itv= mv_interval();
    //itv.add_interval("q1",.5,1);    
    //itv.add_interval("q2",.5,.5);
    //cout << *itv.get_interval("q1")->getTo_lattice_() <<endl;
    //cout << *itv.get_interval("q2")->getTo_lattice_() <<endl;

//manually assign nodes or use mvspot::create_interval_set
//    mvspot::lattice_node nodes[5];
//    nodes[0].setName("a");
//    nodes[1].setName("b");
//    nodes[2].setName("c");
//    nodes[3].setName("d");
//    nodes[4].setName("e");
//    nodes[0].setValue(1);
//    nodes[1].setValue(0.75);
//    nodes[2].setValue(0.5);
//    nodes[3].setValue(0.25);
//    nodes[4].setValue(0.0);    
//    mv_interval intv(nodes, 5);
//OR    
    mv_interval intv = *mvspot::create_interval_set("my_lattice","l",5);

    cout << "size: " << intv.getTo_lattice_()->getNodes_()->size() << endl;
    cout << *intv.getTo_lattice_() << endl<<endl;   

    for(set<mvspot::lattice_node*>::iterator it 
            = intv.getTo_lattice_()->getNodes_()->begin(); 
            it != intv.getTo_lattice_()->getNodes_()->end(); it++){
        cout << *(mvspot::lattice_node*)(*it) << endl;
    }
    
    mv_interval it1= mv_interval("q",0.125,1);
    cout << "it1: " << *it1.getTo_lattice_() << endl<<endl;   
    mv_interval it2= mv_interval("q",0.625,1);
    cout << "it2: " << *it2.getTo_lattice_() << endl<<endl;   
    mv_interval* jit = intv.join_mv(&it1,&it2);
    cout << "join it1 , it2: " << *jit->getTo_lattice_() << endl<<endl;   
    mv_interval* mit = intv.meet_mv(&it1,&it2);
    cout << "meet it1 , it2: " << *mit->getTo_lattice_() << endl<<endl;   
    cout << "not it2: " << *intv.not_mv(&it2)->getTo_lattice_() << endl<<endl;
    cout << "psi it1 , it2: " << *intv.psi_mv(&it1,&it2)->getTo_lattice_() << endl<<endl;
}
}
