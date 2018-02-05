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


void
extract_location_from_formula(formula f, std::map<int,std::list<symbol_stc>*>*& 
            list, const bdd_dict_ptr& d) 
{
    auto recurse = [&list, &d](formula f) {
        return extract_location_from_formula(f, list, d);
    };
    switch (f.kind()) {
        case op::ff:
            return ;
        case op::tt:
            return ;
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
        case op::Xor:
        case op::Implies:
        case op::Equiv:
            SPOT_UNIMPLEMENTED();
        case op::ap:
            if(f.ap_name().find("_loc_") != std::string::npos){
                int id = std::stoi(f.ap_name().substr(1,f.ap_name().find_first_of("_")-1));
                //cout << "ID: " << id << " " << f.ap_name() << endl;
                std::list<symbol_stc>* stc_list;
                //if( (*list)[id] != 0)
                if(id <= NUM_CARS)
                {
                    stc_list = (*list).at(id);//[id];
                }
                else
                {
                    return;
                //    stc_list = new std::list<symbol_stc>();
                }
                int loc = std::stoi(f.ap_name().substr(f.ap_name().find_last_of("_")+1,
                        f.ap_name().size() - f.ap_name().find_last_of("_")-1));
                symbol_stc stc;
                bool found = false;
                for(std::list<symbol_stc>::iterator it = stc_list->begin(); it != stc_list->end(); ++it)
                    if((*it).loc==loc){
                        stc = (*it);
                        found = true;
                        break;
                    }
                    //stc = symbol_stc();
                if(found && stc.type == symbol_type::NEGATIVE)
                    stc.type = symbol_type::BOTH;
                else
                    stc.type = symbol_type::POSITIVE;
                //cout << "loc: " << loc << endl;
                stc.loc = loc;
                if(!found)
                    stc_list->push_back(stc);
                //(*list).[id] = stc_list;
            }
            return;
        case op::Not:
            if(f[0].ap_name().find("_loc_") != std::string::npos){
                int id = std::stoi(f[0].ap_name().substr(1,f[0].ap_name().find_first_of("_")-1));
                //cout << "ID: " << id << " " << f[0].ap_name() << endl;
                std::list<symbol_stc>* stc_list;
                //if( (*list)[id] != 0)
                if(id <= NUM_CARS)
                {
                    stc_list = (*list).at(id);//[id];
                }
                else
                {
                    return;
                //    stc_list = new std::list<symbol_stc>();
                }
                int loc = std::stoi(f[0].ap_name().substr(f[0].ap_name().find_last_of("_")+1,
                        f[0].ap_name().size() - f[0].ap_name().find_last_of("_")-1));
                symbol_stc stc;
                bool found = false;
                for(std::list<symbol_stc>::iterator it = stc_list->begin(); it != stc_list->end(); ++it)
                    if((*it).loc==loc){
                        stc = (*it);
                        found = true;
                        break;
                    }
                if(found && stc.type == symbol_type::POSITIVE)
                    stc.type = symbol_type::BOTH;
                else
                    stc.type = symbol_type::NEGATIVE;
                //cout << "loc: " << loc << endl;
                stc.loc = loc;
                if(!found)
                    stc_list->push_back(stc);
                //(*list)[id] = stc_list;
            }
            return;
        case op::And:
        case op::Or:
        {
            unsigned s = f.size();
            for (unsigned n = 0; n < s; ++n)
                recurse(f[n]);
            return;
        }
    }
    SPOT_UNREACHABLE();
    return ;
}

//std::map<const spot::twa_graph_state*, std::map<int, std::list<symbol_stc>*>*>*
const std::map<tuple_edge, std::map<int, std::list<symbol_stc>*>*>*
compute_all_locations_of_graph_formula(const spot::const_twa_graph_ptr& aut) {
    
    std::cout << "Computing the map of locations from the formula graph automaton.\n";
    
    //std::map<const spot::twa_graph_state*, std::map<int,std::list<symbol_stc>*>*>* res;
    //res = new std::map<const spot::twa_graph_state*, std::map<int,std::list<symbol_stc>*>*>();
    std::map<tuple_edge, std::map<int,std::list<symbol_stc>*>*>* res;
    res = new std::map<tuple_edge, std::map<int,std::list<symbol_stc>*>*>();
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
        //update intervals in formula join/meet
        
        //std::cout << spot::bdd_format_formula(shared_dict, srcit->cond()) << endl;
        std::map<int,std::list<symbol_stc>*>* 
                map_loc = new std::map<int,std::list<symbol_stc>*>();
        for(int i=0; i<NUM_CARS; i++){
            (*map_loc)[i+1] = new std::list<symbol_stc>();
        }
        spot::formula f = spot::bdd_to_formula(srcit->cond(), shared_dict);
        extract_location_from_formula(f, map_loc, shared_dict);
        //cout << "--- " << (*map_loc)[1]->size() << endl;
        //(*res)[src] = map_loc;
        tuple_edge te(aut->state_number(src),aut->state_number(dst),
                spot::bdd_format_formula(shared_dict,srcit->cond()));
        (*res)[te] = map_loc;
        //if(te.src_==7 && te.dst_==7)
        //cout <<">>>>>>>>" << te.to_string() << endl;
        //cout << "from " << aut->state_number(src) << " to " << aut->state_number(dst) 
        //        << " cond " << spot::bdd_format_formula(shared_dict,srcit->cond()) << endl;
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
std::map<size_t,unsigned*> from_sate_map = std::map<size_t,unsigned*>();

//----------------------------------------------//
//  class marine_robot_state    
//----------------------------------------------//
    marine_robot_state::marine_robot_state(unsigned* state_num, //unsigned* from_state_num, 
            spot::twa_graph_ptr org_model, mvspot::mv_interval* q_interval) 
    {
        q_interval_ = q_interval;
        org_model_ = org_model;
        state_num_ = new unsigned [NUM_CARS];
        //from_state_num_ = new unsigned [NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num_[i] = state_num[i];
            //from_state_num_[i] = from_state_num[i];
        }
        
        //delete[] aut_succ;
        delete[] state_num;
        //delete[] from_state_num;
        //delete[] q_intervals;
    }


    unsigned* marine_robot_state::get_state_num() const {
        return state_num_;
    }

    unsigned* marine_robot_state::get_from_state_num() const {
        //return from_state_num_;
        return from_sate_map[this->hash()];
    }


    mvspot::mv_interval* marine_robot_state::get_q_interval() const {
        return q_interval_;
    }

    marine_robot_state* marine_robot_state::clone() const {
        marine_robot_state* res = new marine_robot_state(state_num_, //from_state_num_, 
                org_model_, q_interval_);

        return res;
    }

    size_t marine_robot_state::hash() const {
        int hash = 23;
        if (NUM_CARS > 1)
            for (int i = 0; i <= NUM_CARS - 1; i++) {
                hash = hash * 31 + state_num_[i];
                //hash = hash * 31 + from_state_num_[i];
            } else {
            hash = hash * 31 + state_num_[0];
            //hash = hash * 31 + from_state_num_[0];
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

    marine_robot_state::~marine_robot_state() {
        delete [] state_num_;
        //delete [] from_state_num_;
    }
//----------------------------------------------//
//  class marine_robot_succ_iterator    
//----------------------------------------------//

    marine_robot_succ_iterator::marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, 
            bdd cond, mvspot::mv_interval* intervals, size_t src_hash)
    : kripke_succ_iterator(cond), org_model_(org_model) {
        
        intervals_ = intervals;
        state_num_ = new unsigned[NUM_CARS];
        aut_succ_ = new spot::twa_succ_iterator*[NUM_CARS];
        src_hash_ = src_hash;
        for (int i = 0; i < NUM_CARS; i++) {
            state_num_[i] = state_num[i];
            aut_succ_[i] = org_model->succ_iter(org_model->state_from_number(state_num[i]));
        }
        delete[] state_num;
    }

    marine_robot_succ_iterator::~marine_robot_succ_iterator() {
        delete [] state_num_;
        delete [] aut_succ_;
    }

    bool marine_robot_succ_iterator::first() {

        bool res = true;//false
        for (int i = 0; i < NUM_CARS; i++) {
            res &= aut_succ_[i]->first();
        }
        //if(res)//this causes self-loop removal
        //    return next();
        return res;
    }

    bool marine_robot_succ_iterator::next() {
        
        for (int i = 0; i < NUM_CARS; i++){
            if(aut_succ_[i]->next()){
                return true;
            }
            aut_succ_[i]->first();
        }
        return false;
    }

    bool marine_robot_succ_iterator::done() const {
        
        //bool res = true;//true
        //for (int i = 0; i < NUM_CARS; i++)
        //    res &= aut_succ_[i]->done();
        //return res;
        return aut_succ_[NUM_CARS-1]->done();
    }

    marine_robot_state* marine_robot_succ_iterator::dst() const {
        //std::cout << "in: marine_robot_succ_iterator::dst\n";
        unsigned* state_num;
        state_num = new unsigned[NUM_CARS];

        //unsigned* from_state_num;
        //from_state_num = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            const spot::state* dst = aut_succ_[i]->dst();
            state_num[i] = org_model_->state_number(dst);
            dst->destroy();
            //from_state_num[i] = state_num_[i];
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
        //return new marine_robot_state(state_num, from_state_num, org_model_, itv);
        marine_robot_state* dst_state = new marine_robot_state(state_num, org_model_, itv);
        if(from_sate_map.find(dst_state->hash())==from_sate_map.end() ){
            from_sate_map[dst_state->hash()] = new unsigned[NUM_CARS];
        } 
        for (int i=0; i<NUM_CARS; i++)
            from_sate_map[dst_state->hash()][i] = state_num_[i];
            
        return dst_state;
    }

    void marine_robot_succ_iterator::recycle(twa_succ_iterator* aut_succ[], spot::twa_graph_ptr org_model, 
                        bdd cond, unsigned* state_num, mvspot::mv_interval* intervals, size_t src_hash) {
        org_model_ = org_model;
        intervals_ = intervals;
        src_hash_ = src_hash;
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
        //unsigned* from_init_state = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            init_state[i] = init_state_[i];
            //from_init_state[i] = init_state_[i];
            spot::internal::twa_succ_iterable k = 
                    org_model_->succ(org_model_->state_from_number(init_state_[i]));
        //cout << bdd_to_formula((*k.begin())->cond(),shared_dict) <<endl;

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
            cout << "!!! States must have ONE interval for now. Fix this in future. -> marine_robot_kripke::get_init_state\n";
            exit(0);
        }
        //marine_robot_state* ns = new marine_robot_state(init_state, from_init_state, org_model_, itv);
        marine_robot_state* ns = new marine_robot_state(init_state, org_model_, itv);
        //std::cout << "state: " << format_state(ns) << endl;
        from_sate_map[ns->hash()] = new unsigned[NUM_CARS];
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
        return new marine_robot_succ_iterator(state_num, org_model_, cond, intervals_, ss->hash());
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
        //if(ss->get_state_num()[0]==18 && ss->get_state_num()[1]==6)
        //    cout << "from: " << ss->get_from_state_num()[0] << 
        //            " " << ss->get_from_state_num()[1] << endl;
        //check collision avoidance
        if(COLLISION_AVOIDANCE){
        for(int i=0; i<NUM_CARS; i++){
            for(int j=i+1; j<NUM_CARS; j++){
                if( (ss->get_state_num()[i] == ss->get_state_num()[j]) 
                        ||
//                     ( (ss->get_from_state_num()[i] == ss->get_state_num()[j]) &&
//                         (ss->get_from_state_num()[j] == ss->get_state_num()[i]) )   
//                         )
                     ( (from_sate_map[ss->hash()][i] == ss->get_state_num()[j]) &&
                         (from_sate_map[ss->hash()][j] == ss->get_state_num()[i]) )   
                         )
                {
                    res &= !col_avo_;//return bddfalse;
                    //cout << "collision: \n" << ss->get_state_num()[0] << " " << ss->get_state_num()[1]<<endl
                    //        << ss->get_from_state_num()[0] << " " << ss->get_from_state_num()[1]<<endl;
                    
                    /*
                     ignore this state
                     */
                    //return bddfalse;
                    break;
                }
            }
            if(res!=bddtrue)
                break;
        }
        }
        if(COLLISION_AVOIDANCE && res == bddtrue)
            res &= col_avo_;
        //else{
        //    res &= col_avo_;
        //}
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

    bdd marine_robot_kripke::state_condition_static(const spot::state* s) const {
        //cout <<"in: state_condition\n";
        auto ss = static_cast<const marine_robot_state*> (s);
        bdd res = bddtrue;
        //if(ss->get_state_num()[0]==18 && ss->get_state_num()[1]==6)
        //    cout << "from: " << ss->get_from_state_num()[0] << 
        //            " " << ss->get_from_state_num()[1] << endl;
        //check collision avoidance
        if(COLLISION_AVOIDANCE){
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
                << ')' << bdd_to_formula(this->state_condition_static(s),dict_);
        return out.str();
    }


