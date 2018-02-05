/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   KripkeModel.h
 * Author: mhekmatnejad
 *
 * Created on January 20, 2018, 1:00 PM
 */

#ifndef KRIPKEMODEL_H
#define KRIPKEMODEL_H

#include "MvLtlModel.h"
//#include "ModelGenerator.h"

using namespace spot;

const int NUM_CARS = 2;
const bool COLLISION_AVOIDANCE = true;
const std::string collision_symbol = "col_avo";
static spot::bdd_dict_ptr shared_dict = spot::make_bdd_dict();
static mvspot::mv_interval* shared_intervals = new mvspot::mv_interval("q");
extern spot::twa_graph_ptr shared_formula_graph;

class geo_pos{
public:
    geo_pos(int x, int y){
        x_ = x;
        y_ = y;
    };
    int x_;
    int y_;
};

//must be filled offline based on the road network geometric
extern std::map<int, geo_pos*>* geo_locations;  
extern int MAX_GEO_X;
extern int MAX_GEO_Y;
extern float MAX_GEO_DIST;

enum symbol_type{
    POSITIVE=2, NEGATIVE=1, BOTH=3
};

struct symbol_stc{
    int loc;
    symbol_type type;
};

class tuple_edge{
public:
    tuple_edge(int src, int dst, string cond){
        src_ = src;
        dst_ = dst;
        cond_ = cond;
    }
    
    bool operator <(const tuple_edge& rhs) const
    {
        if (src_ < rhs.src_ || (src_ == rhs.src_ && dst_ < rhs.dst_))
            return true;
        else if ((src_ == rhs.src_ && dst_ == rhs.dst_) )
            if (cond_.compare(rhs.cond_) < 0)
                return true;
        return false;
    }
    
    string to_string(){
        return std::to_string(src_) + " -> " + std::to_string(dst_) + " : " + cond_;
    }
    int src_;
    int dst_;
    string cond_;
};

float* convert_formula_to_interval(const bdd &cond);
mvspot::mv_interval* convert_formula_to_interval(const bdd &cond, 
        mvspot::mv_interval* intervals);

//std::map<const spot::twa_graph_state*, std::map<int,std::list<symbol_stc>*>*>*
const std::map<tuple_edge, std::map<int,std::list<symbol_stc>*>*>*
    compute_all_locations_of_graph_formula(const spot::const_twa_graph_ptr&  f_twa);

class marine_robot_state : public spot::state {
private:
    unsigned* state_num_;
    //unsigned* from_state_num_;
    spot::twa_graph_ptr org_model_;
    mvspot::mv_interval* q_interval_;
public:

    marine_robot_state(unsigned* state_num, //unsigned* from_state_num, 
            spot::twa_graph_ptr org_model, mvspot::mv_interval* q_interval);

    ~marine_robot_state();

    unsigned* get_state_num() const;

    unsigned* get_from_state_num() const;

    mvspot::mv_interval* get_q_interval() const;

    marine_robot_state* clone() const override;

    size_t hash() const override ;
    
    
    int compare(const spot::state* other) const override;

};

class marine_robot_succ_iterator : public spot::kripke_succ_iterator {
private:
    twa_succ_iterator** aut_succ_;
    spot::twa_graph_ptr org_model_;
    mvspot::mv_interval* intervals_;
    unsigned* state_num_;
    size_t src_hash_;
public:

    size_t src_hash() const {return src_hash_;}
    
    marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, 
            bdd cond, mvspot::mv_interval* intervals, size_t src_hash);

    ~marine_robot_succ_iterator();
    
    bool first() override;

    bool next() override;

    bool done() const override;
    
    marine_robot_state* dst() const override;

    void recycle(twa_succ_iterator* aut_succ[], spot::twa_graph_ptr org_model, bdd cond,
            unsigned* state_num, mvspot::mv_interval* intervals, size_t src_hash);
};


class marine_robot_kripke : public spot::kripke {
private:

    string str_certainty_;
    spot::twa_graph_ptr org_model_;
    unsigned* init_state_;
    list<string>* lst_str_loc_;
    std::map<string, bdd>* map_str_bdd_loc_;
    marine_robot_state* cpy_init_state_;
    mvspot::mv_interval* intervals_;
    bdd col_avo_;
public:

    marine_robot_kripke(const spot::bdd_dict_ptr& d, const string certainty,
            const spot::twa_graph_ptr org_model, const unsigned init_state[],
            const list<string> lst_str_loc[], mvspot::mv_interval* intervals);

    marine_robot_state* get_init_state() const override;


    marine_robot_succ_iterator* succ_iter(const spot::state* s) const override;

    list<string>* get_lst_str_loc() const;

    std::map<string, bdd>* get_map_str_bdd_loc() const;

    bdd state_condition(const spot::state* s) const override;

    bdd state_condition_static(const spot::state* s) const ;
    
    bdd cond(const spot::state* s) const;

    std::string format_state(const spot::state* s) const override;

};

//extern marine_robot_kripke* shared_model_kripke;

#endif /* KRIPKEMODEL_H */

