/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   main.cpp
 * Author: mamad
 *
 * Created on January 17, 2017, 2:39 PM
 */

#include <cstdlib>
#include <iostream>
#include "MvLtlModel.h"
#include "Util.h"
#include "ModelGenerator.h"

#include "mvtwaproduct.h"

#include <mutex>
#include <iomanip>

//#include <spot/twa/formula2bdd.hh>
#include <spot/mv/version.hh>
#include <spot/taalgos/dot.hh>
#include <spot/tl/dot.hh>
#include <spot/twaalgos/word.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/ta/taproduct.hh>
#include <spot/twa/taatgba.hh>
//#include <spot/tl/dot.hh>
//#include <spot/taalgos/dot.hh>
//#include "secondary.h"
//#include "mv_interval.h"
using namespace std;

#define PRINT_DEBUG_DATA 1
const int NUM_CARS = 2;

void model_4(string formula);
void dfs(spot::const_twa_graph_ptr aut, bdd query);
int get_random(int low, int high);
static spot::parsed_aut_ptr read_model_aut;
static spot::kripke_graph_ptr kg_model;
static spot::twa_graph_ptr aut_model;
static spot::bdd_dict_ptr shared_dict = spot::make_bdd_dict();
float CERTAINTY_THREASHOLD = 1;
static mvspot::mv_interval* shared_intervals = new mvspot::mv_interval("q");
/*
 * 
 */
int main(int argc, char** argv) {

    std::cout << "started...\n";
    cout << mvspot::getVersion() << "\n" << mvspot::getBuild() << "\n";

    mvspot::test_intervals();
    //if(true) return 0;

std:
    ifstream inFile;
    //string model_filename = "ocean_model.dot";
    string model_filename = "sirle2018/road_network_model.dot";
    srand(time(NULL));
    read_model_aut = Util::readAutFromFile(model_filename, false, shared_dict);
    if (!read_model_aut || read_model_aut->errors.size() > 0) {
        cout << "could not read the model from file!";
        exit(0);
    } else {
        cout << "model loaded from: " << model_filename << endl;
        Util::write2File("sirle2018/road_network_graph.dot", read_model_aut->aut, "k");

    }
    kg_model = read_model_aut->ks;
    aut_model = read_model_aut->aut;


    model_4("");

    cout << "done!\n";
    return 0;
}

int get_random(int low, int high) {
    return (int) (low + (float) rand() / RAND_MAX * (high - low));
}

void dfs(spot::const_twa_graph_ptr aut, bdd query) {
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
        //bdd res = query & e.cond;
        //if(res==bddfalse){
        //gr.out_iteraser(edge).erase();

        //gr.remove_dead_edges_(); 
        // }
        //else
        {
            todo.push(e.next_succ); // Prepare next sibling edge.
            if (!seen[e.dst])
                push_state(e.dst);
            std::cout << e.src << "->" << e.dst << '\n';
        }
    }
}

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
    string f = bdd_format_formula(shared_dict, cond);
    if(f.size()<7 || (f.find("=[")==std::string::npos))
        return nullptr;
    f = f.substr(3,f.size()-4);
    //cout << "------ "+f+"\n"; 
    if(intervals->getMap_intervals()->find(f)!=intervals->getMap_intervals()->end())
        return (*intervals->getMap_intervals())[f];
    return nullptr;
}


class marine_robot_state : public spot::state {
private:
    unsigned* state_num_;
    //twa_succ_iterator** aut_succ_;
    spot::twa_graph_ptr org_model_;
    float time_ = 0;
    bool is_certain_ = false; // has a bdd equvalent for certainty
    //float** q_intervals_;
    mvspot::mv_interval* q_interval_;
public:

    marine_robot_state(unsigned* state_num = 0, float time = 0, bool is_certain = true,
            //twa_succ_iterator** aut_succ=0, 
            spot::twa_graph_ptr org_model = 0, mvspot::mv_interval* q_interval=nullptr)//float** q_intervals = 0)
    : time_(time), is_certain_(is_certain)//, org_model_(org_model)
    {
        q_interval_ = q_interval;
        //cout << "in:  marine_robot_state\n";
        org_model_ = org_model;
        //aut_succ_ = new twa_succ_iterator* [NUM_CARS];
        state_num_ = new unsigned [NUM_CARS];
        //q_intervals_ = new float*[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            //cout << "@ " << q_intervals[i][0] << " " << q_intervals[i][1] << endl;
            //q_intervals_[i] = new float[2];
            //aut_succ_[i] = aut_succ[i];
            state_num_[i] = state_num[i];
            //q_intervals_[i][0] = q_intervals[i][0];
            //q_intervals_[i][1] = q_intervals[i][1];
        }

        //if(q_interval_!=nullptr)
        //    cout << "***meet interval:\n" << *q_interval_->getTo_lattice_() << endl;


        //delete[] aut_succ;
        delete[] state_num;
        //delete[] q_intervals;
        //cout << "out:  marine_robot_state\n";
    }

    //    virtual ~marine_robot_state() override
    //    {
    //        cout << "destructor....\n";
    //        delete[] state_num_;
    //        delete[] q_intervals_;
    //        //for(int i=0; i<NUM_CARS; i++)
    //        //    aut_succ_[i]->~twa_succ_iterator();
    //        //delete[] aut_succ_;
    //    }

    unsigned* get_state_num() const {
        return state_num_;
    }

    //  twa_succ_iterator** get_aut_succ() const
    //  {
    //      return aut_succ_;
    //  }

    float get_time() const {
        return time_;
    }

    bool is_certain() const {
        return is_certain_;
    }

//    float** get_q_intervals() const {
//        return q_intervals_;
//    }

    mvspot::mv_interval* get_q_interval() const {
        return q_interval_;
    }

    marine_robot_state* clone() const override {
        //cout << "!!!!! clone: marine_robot_state\n";//the aut_succ is not cloneable. if you need to have it, bring spot::state in this class and use org_model_ to create new succ
        //exit(0);
        //twa_succ_iterator** aut_suc = new twa_succ_iterator* [NUM_CARS];
        //    marine_robot_state* res = new marine_robot_state(state_num_, time_, is_certain_, 
        //            aut_succ_, org_model_, q_intervals_);
        marine_robot_state* res = new marine_robot_state(state_num_, time_, is_certain_,
                org_model_, q_interval_);
        //for(int i=0; i<NUM_CARS; i++){
        //    res->q_intervals_[i][0] = q_intervals_[i][0];
        //    res->q_intervals_[i][1] = q_intervals_[i][1];
        //}
        return res;
    }

    size_t hash() const override {
        //assuming all variables are positive
        int hash = 23;
        if (NUM_CARS > 1)
            for (int i = 0; i <= NUM_CARS - 1; i++) {
                //hash = hash * 31 + (i + 2 + state_num_[i])*(1+state_num_[i + 1]);
                hash = hash * 31 + state_num_[i];
                //note: for q_interval and other fields for now we do not need them
                //hash = hash*31 + aut_succ_[i]->dst()->hash();
                //hash = hash*31 + q_intervals_[i][0];//not really necessary?
                //hash = hash*31 + q_intervals_[i][1];
            } else {
            hash = hash * 31 + state_num_[0];
        }
        //hash = hash*31 + aut_succ_->dst()->hash();
        //hash = hash*31 + x_;
        //hash = hash*31 + y_;
        //hash = hash*31 + time_;
        //hash = hash*31 + is_certain_;
        return hash;
        //return  (x_ + y_) * (x_ + y_ + 1) / 2 + x_;
        //return (x_ * 31) + 13*y_ + time_*7111 + (is_certain_ ? 101 : 1001);
    }

    int compare(const spot::state* other) const override {
        auto o = static_cast<const marine_robot_state*> (other);
        size_t oh = o->hash();
        size_t h = hash();
        if (h < oh)
            return -1;
        else
            return h > oh;
    }

};

class marine_robot_succ_iterator : public spot::kripke_succ_iterator {
private:
    twa_succ_iterator** aut_succ_;
    spot::twa_graph_ptr org_model_;
    mvspot::mv_interval* intervals_;
    float time_;
    unsigned* state_num_;
public:

    marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, 
            float time, bdd cond, mvspot::mv_interval* intervals)
    : kripke_succ_iterator(cond), org_model_(org_model), time_(time) {
        intervals_ = intervals;
        state_num_ = new unsigned[NUM_CARS];
        //cout << "in: marine_robot_succ_iterator\n";
        aut_succ_ = new spot::twa_succ_iterator*[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num_[i] = state_num[i];
            aut_succ_[i] = org_model->succ_iter(org_model->state_from_number(state_num[i]));
        }
        //delete[] state_num;
    }

    //virtual ~marine_robot_succ_iterator() override
    //{
    //    cout << "destructor.... marine_robot_succ_iterator\n";
    //    //for(int i=0; i<NUM_CARS; i++)
    //    //    aut_succ_[i]->~twa_succ_iterator();
    //    delete[] aut_succ_;
    //}

    bool first() override {

        bool res = false;
        for (int i = 0; i < NUM_CARS; i++) {
            res |= aut_succ_[i]->first();
        }
        return res;
    }

    bool next() override {
        
        bool res = true;//false
        for (int i = 0; i < NUM_CARS; i++){
            if(aut_succ_[i]->next()){
                return true;
            }
            aut_succ_[i]->first();
        }
        return false;
    }

    bool done() const override {
        
        bool res = true;//true
        for (int i = 0; i < NUM_CARS; i++)
            res &= aut_succ_[i]->done();
        return res;
    }

    marine_robot_state* dst() const override {

        unsigned* state_num;
        state_num = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            state_num[i] = org_model_->state_number(aut_succ_[i]->dst());

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
        return new marine_robot_state(state_num, 0, true, org_model_, itv);
    }

    void recycle(twa_succ_iterator* aut_succ[], spot::twa_graph_ptr org_model, bdd cond) {
        org_model_ = org_model;
        aut_succ_ = new spot::twa_succ_iterator*[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++)
            aut_succ_[i] = aut_succ[i];
        delete[] aut_succ;
        spot::kripke_succ_iterator::recycle(cond);
    }
};

//initialize the shared variable for interval related functions
mvspot::mv_interval* spot::twa::shared_intervals_ = shared_intervals;//new mvspot::mv_interval("q");
mvspot::mv_interval* mvspot::interval_bdd::shared_intervals_ = spot::twa::shared_intervals_;//new mvspot::mv_interval("q");

class marine_robot_kripke : public spot::kripke {
//class marine_robot_kripke : public mvspot::mv_kripke {
private:

    bdd goal_;
    bdd certainty_;
    string str_certainty_;
    spot::twa_graph_ptr org_model_;
    unsigned* init_state_;
    list<string>* lst_str_loc_;
    std::map<string, bdd>* map_str_bdd_loc_;
    marine_robot_state* cpy_init_state_;
    mvspot::mv_interval* intervals_;
public:

    marine_robot_kripke(const spot::bdd_dict_ptr& d, const string certainty,
            const spot::twa_graph_ptr org_model, const unsigned init_state[],
            const list<string> lst_str_loc[], mvspot::mv_interval* intervals)
    : spot::kripke(d), str_certainty_(certainty), org_model_(org_model) {
    //: mvspot::mv_kripke(intervals, d), str_certainty_(certainty), org_model_(org_model) {
        intervals_ = intervals;
        shared_intervals_ = intervals;
        mvspot::interval_bdd::shared_intervals_ = intervals;
        //goal_ = bdd_ithvar(register_ap("goal"));
        //certainty_ = bdd_ithvar(register_ap(certainty)); //registers the requested certainty 
        lst_str_loc_ = new list<string>[NUM_CARS];
        map_str_bdd_loc_ = new std::map<string, bdd>[NUM_CARS];
        init_state_ = new unsigned[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            lst_str_loc_[i] = lst_str_loc[i];
            init_state_[i] = init_state[i];
            for (std::list<string>::iterator it = lst_str_loc_[i].begin(); it != lst_str_loc_[i].end(); it++) {
                //*******************************@@@@@@@@@@@@@@@@@@@@@
                bdd res = bdd_ithvar(register_ap(*it));
                map_str_bdd_loc_[i][*it] = res;
                cout << "@@@ @@@ " << *it << "  " << res << "  bdd: " << map_str_bdd_loc_[i][*it] << endl;
            }
        }
        //cpy_init_state_ = create_init_state();
    }

    marine_robot_state* get_cpy_init_state() const {
        return cpy_init_state_;
    }

    
//    marine_robot_state* get_init_state() const override {
//        float** intervals;
//        intervals = new float*[NUM_CARS];
//        unsigned* init_state = new unsigned[NUM_CARS];
//        for (int i = 0; i < NUM_CARS; i++) {
//            init_state[i] = init_state_[i];
//            internal::twa_succ_iterable k = org_model_->succ(org_model_->state_from_number(init_state_[i]));
//            float* ints = convert_formula_to_interval((*k.begin())->cond());
//            intervals[i] = new float[2];
//            intervals[i][0] = ints[0];
//            intervals[i][1] = ints[1];
//        }
//        return new marine_robot_state(init_state, 0, true, org_model_, nullptr);
//    }

    marine_robot_state* get_init_state() const override {

        unsigned* init_state = new unsigned[NUM_CARS];
        mvspot::mv_interval* itv = nullptr;
        for (int i = 0; i < NUM_CARS; i++) {
            init_state[i] = init_state_[i];
            spot::internal::twa_succ_iterable k = 
                    org_model_->succ(org_model_->state_from_number(init_state_[i]));
            if ((*k.begin())->cond() != bddfalse) {
                mvspot::mv_interval* tmp_itv = 
                        convert_formula_to_interval((*k.begin())->cond(), intervals_);
                if(tmp_itv!=nullptr && itv==nullptr)
                    itv = tmp_itv;
                else if(itv!=nullptr && tmp_itv!=nullptr && i>0)
                    itv = itv->meet_mv(itv, tmp_itv);
            }
        }
        return new marine_robot_state(init_state, 0, true, org_model_, itv);
        
    }


    marine_robot_succ_iterator* succ_iter(const spot::state* s) const override {
        //cout << "<befor static_cast<const marine_robot_state*>(s)\n\n\n";
        auto ss = static_cast<const marine_robot_state*> (s);
        // cout << ">after static_cast<const marine_robot_state*>(s)\n\n\n";
        unsigned* state_num;
        state_num = new unsigned[NUM_CARS];
        for (int i = 0; i < NUM_CARS; i++) {
            state_num[i] = ss->get_state_num()[i];
            //cout <<"-> " << state_num[i] << endl;
        }
        float time = ss->get_time();
        bdd cond = state_condition(ss);


        //      if (iter_cache_)//******************____________-------------
        //        {
        //          auto it = static_cast<marine_robot_succ_iterator*>(iter_cache_);
        //          iter_cache_ = nullptr;    // empty the cache
        //          it->recycle(ss->get_aut_succ(), org_model_, cond);
        //          return it;
        //        }
        return new marine_robot_succ_iterator(state_num, org_model_, time, cond, intervals_);
    }

    list<string>* get_lst_str_loc() const {
        return lst_str_loc_;
    }

    std::map<string, bdd>* get_map_str_bdd_loc() const {
        return map_str_bdd_loc_;
    }

    bdd state_condition(const spot::state* s) const override {
        //cout <<"in: state_condition\n";

        auto ss = static_cast<const marine_robot_state*> (s);
        bdd res = bddtrue;
        
        //ss->get_q_interval()->getName()
        spot::formula ff = spot::parse_formula("\"q="+ss->get_q_interval()->getName()+"\"");
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

    std::string format_state(const spot::state* s) const override {
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
                << ')';
        return out.str();
    }

};

void model_4(string formula) {
    cout << ">>> in model_4\n";

    //****************//
    CERTAINTY_THREASHOLD = 0.99;
    unsigned* init_state;
    init_state = new unsigned[NUM_CARS];
    init_state[0] = 5;
    init_state[1] = 6;
    string** str_loc;
    str_loc = new string*[NUM_CARS];
    str_loc[0] = new string[2];
    str_loc[1] = new string[2];
    str_loc[0][0] = "C1_loc_1";
    str_loc[0][1] = "C1_loc_9";
    str_loc[1][0] = "C2_loc_4";
    str_loc[1][1] = "C2_loc_12";
    list<string>* lst_loc;
    lst_loc = new list<string>[NUM_CARS];
    lst_loc[0].push_back(str_loc[0][0]);
    lst_loc[0].push_back(str_loc[0][1]);
    lst_loc[1].push_back(str_loc[1][0]);
    lst_loc[1].push_back(str_loc[1][1]);
    //****************//
    stringstream stream;
    stream << fixed << setprecision(2) << CERTAINTY_THREASHOLD;
    string str_threshold = stream.str();
    string str_certainty_ap = "q > " + str_threshold;
    formula = "G(\"q=[0.5,1]\") & F(C1_loc_1) & F(C1_loc_9) & ((!C1_loc_1) U C1_loc_9) & "
            "G(!C1_loc_1 | !C1_loc_9) & G(C1_loc_9 -> XG(\"q=[1,1]\"))";
    formula += " & F(C2_loc_4) & F(C2_loc_12) & ((!C2_loc_12) U C2_loc_4) & "
            "G(!C2_loc_4 | !C2_loc_12)";


    formula = "G(\"q=[0.5,1]\") & F(C1_loc_1) & F(C1_loc_9) & ((!C1_loc_1) U C1_loc_9) & "
            "G(!C1_loc_1 | !C1_loc_9) & G(C1_loc_9 -> XG(\"q=[1,1]\"))";
    //formula += " & F(C2_loc_4) & F(C2_loc_12) & ((!C2_loc_12) U C2_loc_4) & "
    //        "G(!C2_loc_4 | !C2_loc_12)";


    //formula = "F(C1_loc_1) & G(!\"q=[0,0.5]\")";
    //formula += " & F(C2_loc_12)";

    cout << ">>> Formula: " << formula << endl;

    spot::parsed_formula pf = spot::parse_infix_psl(formula); //"FG(goal) & G \"c > 0.2\" "
    if (pf.format_errors(std::cerr)) {
        cout << "the formula has error!\n";
        return;
    }
    
    // Translate its negation.
    //spot::formula f = spot::formula::Not(pf.f);
    spot::formula f = pf.f;
    spot::twa_graph_ptr af = spot::translator(shared_dict).run(f);
    Util::write2File("new_formula.dot", af);
    
    //mvspot::mv_interval* intervals = mvspot::create_interval_set("certainty", "q", 5);
    mvspot::mv_interval* shared_intervals = mvspot::create_interval_set("certainty", "q", 5);
    shared_intervals->add_interval("q=[1,1]",1,1);
    shared_intervals->add_interval("q=[0.5,1]",0.5,1);
    shared_intervals->add_interval("q=[0.5,0.5]",0.5,0.5);
    shared_intervals->add_interval("q=[0,0.5]",0,0.5);
    shared_intervals->add_interval("q=[0,0]",0,0);
    shared_intervals->add_interval("q=[0,1]",0,1);

    cout << "\n\nusing TO Lattice:\n" << *shared_intervals->getTo_lattice_() << endl<<endl;
    for(std::pair<string,mvspot::mv_interval*> it : *shared_intervals->getMap_intervals()){
        
        cout << "interval: " << it.first << "\n" << *(it.second->getTo_lattice_()) << endl;
    }
    //if(true) return;
    // Find a run of or marine_robot_kripke that intersects af.
    auto k = std::make_shared<marine_robot_kripke>(shared_dict, str_certainty_ap, aut_model,
            init_state, lst_loc, shared_intervals);
    
    cout << "accepting condition <model>: " << k->acc()<< " and formulas:\n";
    for(spot::formula f:  k->ap())
        cout << f <<endl;
    cout << "accepting condition <formula>: " << af->acc()<< " and formulas:\n";
    for(spot::formula f:  af->ap())
        cout << f <<endl;
    //k->mv_intersecting_run(af);
    //if(true) return;

    if (auto run = k->intersecting_run(af))
        std::cout << "found a plan by the following run:\n" << *run;
    else
        std::cout << "no plan found.\n";

    // mvspot::mvtwaproduct mvtp;
    // mvtp.test_me_again();
}

