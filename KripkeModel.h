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


float* convert_formula_to_interval(const bdd &cond);
mvspot::mv_interval* convert_formula_to_interval(const bdd &cond, 
        mvspot::mv_interval* intervals);


class marine_robot_state : public spot::state {
private:
    unsigned* state_num_;
    unsigned* from_state_num_;
    spot::twa_graph_ptr org_model_;
    mvspot::mv_interval* q_interval_;
public:

    marine_robot_state(unsigned* state_num, unsigned* from_state_num, 
            spot::twa_graph_ptr org_model, mvspot::mv_interval* q_interval);


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
public:

    marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, 
            bdd cond, mvspot::mv_interval* intervals);

    bool first() override;

    bool next() override;

    bool done() const override;
    
    marine_robot_state* dst() const override;

    void recycle(twa_succ_iterator* aut_succ[], spot::twa_graph_ptr org_model, bdd cond,
            unsigned* state_num, mvspot::mv_interval* intervals);
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

    std::string format_state(const spot::state* s) const override;

};


#endif /* KRIPKEMODEL_H */

