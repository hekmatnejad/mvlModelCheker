/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

#include "KripkeModel.h"


float* convert_formula_to_interval(const bdd &cond) {
    //cout <<"in: convert_formula_to_interval\n";
    float* res = new float[2];
    string f = bdd_format_formula(shared_dict, cond);
    if (f.substr(1, 3).compare("q=[") != 0) {
        cout << "!!!!!!!!!!!!!!!!!! wrong symbol sound: " << f << "\n\n";
        //exit(0);
        return res;
    }
    string l, r;
    l = f.substr(f.find_first_of("[") + 1, f.find_first_of(",") - f.find_first_of("[") - 1);
    r = f.substr(f.find_first_of(",") + 1, f.find_first_of("]") - f.find_first_of(",") - 1);
    std::string::iterator end_pos = std::remove(l.begin(), l.end(), ' ');
    l.erase(end_pos, l.end());
    end_pos = std::remove(r.begin(), r.end(), ' ');
    r.erase(end_pos, r.end());
    //cout << "working on: " << f << " : " << l << " " << r << endl;
    res[0] = std::stof(l);
    res[1] = std::stof(r);
    //cout <<"out: convert_formula_to_interval\n";
    return res;
}

mvspot::mv_interval* convert_formula_to_interval(const bdd &cond, 
        mvspot::mv_interval* intervals) {
    //cout<<bdd_to_formula(cond,shared_dict)<<endl;
    string f = bdd_format_formula(shared_dict, cond);
    //if(cond==bddtrue || f.compare("1")==0)
    //    return (*intervals->getMap_intervals())["[1,1]"];
    //else if (cond==bddfalse || f.compare("0")==0)
    //    return (*intervals->getMap_intervals())["[0,0]"];
    if(f.size()<7 || (f.find("=[")==std::string::npos)){
        std::cout << "*** WRONG INTERVAL: " << f << endl;
        return nullptr;
    }
    f = f.substr(f.find_first_of("[") , f.find_first_of("]") - f.find_first_of("[") + 1);
    //cout << "------ "+f+ " cnd: " << cond << "\n"; 
    if(intervals->getMap_intervals()->find(f)!=intervals->getMap_intervals()->end())
        return (*intervals->getMap_intervals())[f];
    return nullptr;
}

//initialize the shared variable for interval related functions
mvspot::mv_interval* spot::twa::shared_intervals_ = shared_intervals;//new mvspot::mv_interval("q");
mvspot::mv_interval* mvspot::interval_bdd::shared_intervals_ = spot::twa::shared_intervals_;//new mvspot::mv_interval("q");

//----------------------------------------------//
//  class marine_robot_state    
//----------------------------------------------//

    marine_robot_state::marine_robot_state(unsigned* state_num, unsigned* from_state_num, 
            spot::twa_graph_ptr org_model, mvspot::mv_interval* q_interval) 
    {
        q_interval_ = q_interval;
        org_model_ = org_model;
        state_num_ = new unsigned [NUM_CARS];
        from_state_num_ = new unsigned [NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num_[i] = state_num[i];
            from_state_num_[i] = from_state_num[i];
        }
        
        //delete[] aut_succ;
        delete[] state_num;
        delete[] from_state_num;
        //delete[] q_intervals;
    }


    unsigned* marine_robot_state::get_state_num() const {
        return state_num_;
    }

    unsigned* marine_robot_state::get_from_state_num() const {
        return from_state_num_;
    }


    mvspot::mv_interval* marine_robot_state::get_q_interval() const {
        return q_interval_;
    }

    marine_robot_state* marine_robot_state::clone() const {
        marine_robot_state* res = new marine_robot_state(state_num_, from_state_num_, 
                org_model_, q_interval_);

        return res;
    }

    size_t marine_robot_state::hash() const {
        int hash = 23;
        if (NUM_CARS > 1)
            for (int i = 0; i <= NUM_CARS - 1; i++) {
                hash = hash * 31 + state_num_[i];
            } else {
            hash = hash * 31 + state_num_[0];
        }

        return hash;
    }

    int marine_robot_state::compare(const spot::state* other) const {
        auto o = static_cast<const marine_robot_state*> (other);
        size_t oh = o->hash();
        size_t h = hash();
        if (h < oh)
            return -1;
        else
            return h > oh;
    }

//----------------------------------------------//
//  class marine_robot_succ_iterator    
//----------------------------------------------//

    marine_robot_succ_iterator::marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, 
            bdd cond, mvspot::mv_interval* intervals)
    : kripke_succ_iterator(cond), org_model_(org_model) {
        //std::cout << "in: marine_robot_succ_iterator\n";
        
        intervals_ = intervals;
        state_num_ = new unsigned[NUM_CARS];
        aut_succ_ = new spot::twa_succ_iterator*[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num_[i] = state_num[i];
            aut_succ_[i] = org_model->succ_iter(org_model->state_from_number(state_num[i]));
        }
        //delete[] state_num;
    }


    bool marine_robot_succ_iterator::first() {

        bool res = false;
        for (int i = 0; i < NUM_CARS; i++) {
            res |= aut_succ_[i]->first();
        }
        return res;
    }

    bool marine_robot_succ_iterator::next() {
        
        bool res = true;//false
        for (int i = 0; i < NUM_CARS; i++){
            if(aut_succ_[i]->next()){
                return true;
            }
            aut_succ_[i]->first();
        }
        return false;
    }

    bool marine_robot_succ_iterator::done() const {
        
        bool res = true;//true
        for (int i = 0; i < NUM_CARS; i++)
            res &= aut_succ_[i]->done();
        return res;
    }

    marine_robot_state* marine_robot_succ_iterator::dst() const {
        //std::cout << "in: marine_robot_succ_iterator::dst\n";
        unsigned* state_num;
        state_num = new unsigned[NUM_CARS];
        unsigned* from_state_num;
        from_state_num = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            state_num[i] = org_model_->state_number(aut_succ_[i]->dst());
            from_state_num[i] = state_num_[i];
            if (aut_succ_[i]->cond() != bddfalse) {
                spot::internal::twa_succ_iterable k = 
                    org_model_->succ(org_model_->state_from_number(state_num[i]));
                bdd cnd = (*k.begin())->cond();
            //cout << "\n\n\n\n\n\n\n\n------------" << spot::bdd_to_formula(cnd,shared_dict) << "\n";
                mvspot::mv_interval* tmp_itv = convert_formula_to_interval(cnd, intervals_);
                if(tmp_itv!=nullptr && itv==nullptr)
                    itv = tmp_itv;
                else if(itv!=nullptr && tmp_itv!=nullptr && i>0)
                    itv = itv->meet_mv(itv, tmp_itv);
            } 
        }
        
        //std::cout << "form: <" << state_num_[0] << " " << state_num_[1] << 
        //        "> to: <" << state_num[0] << " " << state_num[1] << ">\n";
        return new marine_robot_state(state_num, from_state_num, org_model_, itv);
    }

    void marine_robot_succ_iterator::recycle(twa_succ_iterator* aut_succ[], spot::twa_graph_ptr org_model, 
                        bdd cond, unsigned* state_num, mvspot::mv_interval* intervals) {
        org_model_ = org_model;
        intervals_ = intervals;
        aut_succ_ = new spot::twa_succ_iterator*[NUM_CARS];
        state_num_ = new unsigned[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++){
            aut_succ_[i] = aut_succ[i];
            state_num_[i] = state_num[i];
        }
        delete[] aut_succ;
        spot::kripke_succ_iterator::recycle(cond);
    }


//----------------------------------------------//
//  class marine_robot_kripke    
//----------------------------------------------//


    marine_robot_kripke::marine_robot_kripke(const spot::bdd_dict_ptr& d, const string certainty,
            const spot::twa_graph_ptr org_model, const unsigned init_state[],
            const list<string> lst_str_loc[], mvspot::mv_interval* intervals)
    : spot::kripke(d), str_certainty_(certainty), org_model_(org_model) {
        intervals_ = intervals;
        shared_intervals_ = intervals;
        mvspot::interval_bdd::shared_intervals_ = intervals;
        lst_str_loc_ = new list<string>[NUM_CARS];
        map_str_bdd_loc_ = new std::map<string, bdd>[NUM_CARS];
        init_state_ = new unsigned[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            lst_str_loc_[i] = lst_str_loc[i];
            init_state_[i] = init_state[i];
            for (std::list<string>::iterator it = lst_str_loc_[i].begin(); it != lst_str_loc_[i].end(); it++) {
                //*******************************@@@@@@@@@@@@@@@@@@@@@
                if((*it).size()>=1){
                    bdd res = bdd_ithvar(register_ap(*it));
                    map_str_bdd_loc_[i][*it] = res;
                    cout << "@@@ @@@ " << *it << "  " << res << "  bdd: " << map_str_bdd_loc_[i][*it] << endl;
                }
            }
        }
        if(COLLISION_AVOIDANCE)
            col_avo_ = bdd_ithvar(register_ap(collision_symbol));
        shared_dict = dict_;
    }

    marine_robot_state* marine_robot_kripke::get_init_state() const {

        unsigned* init_state = new unsigned[NUM_CARS];
        unsigned* from_init_state = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            init_state[i] = init_state_[i];
            from_init_state[i] = init_state_[i];
            spot::internal::twa_succ_iterable k = 
                    org_model_->succ(org_model_->state_from_number(init_state_[i]));
        cout << bdd_to_formula((*k.begin())->cond(),shared_dict) <<endl;

            if ((*k.begin())->cond() != bddfalse) {
                mvspot::mv_interval* tmp_itv = 
                        convert_formula_to_interval((*k.begin())->cond(), intervals_);
                if(tmp_itv!=nullptr && itv==nullptr)
                    itv = tmp_itv;
                else if(itv!=nullptr && tmp_itv!=nullptr && i>0)
                    itv = itv->meet_mv(itv, tmp_itv);
            }
        }
        if(itv==nullptr){
            cout << "!!!";
            exit(0);
        }
        marine_robot_state* ns = new marine_robot_state(init_state, from_init_state, org_model_, itv);
        //std::cout << "state: " << format_state(ns) << endl;
        return ns;
        //return new marine_robot_state(init_state, from_init_state, org_model_, itv);
        
    }


    marine_robot_succ_iterator* marine_robot_kripke::succ_iter(const spot::state* s) const {
        //cout << "<befor static_cast<const marine_robot_state*>(s)\n\n\n";
        auto ss = static_cast<const marine_robot_state*> (s);
        // cout << ">after static_cast<const marine_robot_state*>(s)\n\n\n";
        unsigned* state_num;
        state_num = new unsigned[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num[i] = ss->get_state_num()[i];
            //cout <<"-> " << state_num[i] << endl;
        }
        bdd cond = state_condition(ss);


//        if (iter_cache_)//******************____________-------------
//        {
//            auto it = static_cast<marine_robot_succ_iterator*>(iter_cache_);
//            iter_cache_ = nullptr;    // empty the cache
//            it->recycle(ss->get_aut_succ(), org_model_, cond);
//            return it;
//        }
        return new marine_robot_succ_iterator(state_num, org_model_, cond, intervals_);
    }

    list<string>* marine_robot_kripke::get_lst_str_loc() const {
        return lst_str_loc_;
    }

    std::map<string, bdd>* marine_robot_kripke::get_map_str_bdd_loc() const {
        return map_str_bdd_loc_;
    }

    bdd marine_robot_kripke::state_condition(const spot::state* s) const {
        //cout <<"in: state_condition\n";

        auto ss = static_cast<const marine_robot_state*> (s);
        bdd res = bddtrue;

        //check collision avoidance
        if(COLLISION_AVOIDANCE){
        for(int i=0; i<NUM_CARS; i++){
            for(int j=i+1; j<NUM_CARS; j++){
                if( (ss->get_state_num()[i] == ss->get_state_num()[j]) 
                        ||
                     ( (ss->get_from_state_num()[i] == ss->get_state_num()[j]) &&
                         (ss->get_from_state_num()[j] == ss->get_state_num()[i]) )   
                         )
                {
                    res &= !col_avo_;//return bddfalse;
                    //cout << "collision: \n" << ss->get_state_num()[0] << " " << ss->get_state_num()[1]<<endl
                    //        << ss->get_from_state_num()[0] << " " << ss->get_from_state_num()[1]<<endl;
                    break;
                }
            }
            if(res!=bddtrue)
                break;
        }
        }else{
            res &= col_avo_;
        }
        //spot::formula ff = spot::parse_formula("\"q="+ss->get_q_interval()->getName()+"\"");
        spot::formula ff = spot::formula::ap("q="+ss->get_q_interval()->getName()+"");
        //if(ss->get_q_interval()->getName().compare("[1,1]")!=0)
        //cout << "-> " <<"q="+ss->get_q_interval()->getName() << endl;
        //std::cout << "*** " << ff << " " << ss->get_state_num()[0] << " " << ss->get_state_num()[1] << " -> " << ss->get_q_interval()->getName() << "\n";
        //formula_to_bdd(ff,shared_dict)
        //spot::formula ff = org_model_->get_dict()->bdd_map[].f;
        
    //cout << "*** " << ss->get_q_interval()->getName() << " " << ff << " " << spot::formula_to_bdd(ff,shared_dict,nullptr) <<endl;
        res &= spot::formula_to_bdd(ff,shared_dict,nullptr);
        
        list<string>* tmp_symbols;
        map<string, bdd>* tmp_map;
        tmp_symbols = get_lst_str_loc();
        tmp_map = get_map_str_bdd_loc();
        for (int i = 0; i < NUM_CARS; i++) {
            string symbol = "C" + std::to_string(i + 1) + "_loc_" + std::to_string(ss->get_state_num()[i]);
            for (std::list<string>::iterator it = tmp_symbols[i].begin(); it != tmp_symbols[i].end(); it++) {
                if ((*it) == symbol) {
                    res &= tmp_map[i][*it];
                } else {
                    res &= !(tmp_map[i][*it]);
                }
            }
        }
        //cout <<"out: state_condition\n";

        //bool goal = true;
        return res;// & (goal ? goal_ : !goal_) & (ss->is_certain() ? certainty_ : !certainty_);
    }

    std::string marine_robot_kripke::format_state(const spot::state* s) const {
        auto ss = static_cast<const marine_robot_state*> (s);
        std::ostringstream out;
        string str_state = "< ";
        for (int i = 0; i < NUM_CARS; i++) {
            str_state += std::to_string(ss->get_state_num()[i]);
            if ((i + 1) < NUM_CARS)
                str_state += "  ,  ";
        }
        str_state += " >";
        out << "(state_num = " << str_state
                //<< ", is_certain = " << ss->is_certain() 
                //<< ", t = " << ss->get_time() 
                << ')' << bdd_to_formula(this->state_condition(s),dict_);
        return out.str();
    }


