/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   mv_interval.h
 * Author: mhekmatnejad
 *
 * Created on January 8, 2018, 2:01 AM
 */

#ifndef MV_INTERVAL_H
#define MV_INTERVAL_H

#include "MvLtlModel.h"
namespace mvspot
{
class mv_interval {
public:
    mv_interval();
    mv_interval(float low, float high);
    mv_interval(lattice_node* intervals, int size) throw();
    mv_interval(const mv_interval& orig);
    virtual ~mv_interval();
    void add_interval(string symbol, float low, float high);
    mv_interval* get_interval(string symbol);

    lattice_node* getTop();
    lattice_node* getButtom();
    //lattice operators
    float complement_mv(float given);
    mv_interval* join_mv(mv_interval* left, mv_interval* right);
    mv_interval* meet_mv(mv_interval* left, mv_interval* right);
    mv_interval* not_mv(mv_interval* given);
    void negate_mv(mv_interval* given);
    mv_interval* psi_mv(mv_interval* base, mv_interval* given);

    int getInt_size_() const {
        return int_size_;
    }

    mv_lattice* getTo_lattice_() const {
        return to_lattice_;
    }

    std::map<std::pair<float,float>,mv_interval*>* getMap_all_intervals(){
        return map_all_intervals_;
    }

    std::map<string,mv_interval*>* getMap_intervals(){
        return map_intervals_;
    }
    
private:
    lattice_node* intervals_=0;
    lattice_node* top_=0;
    lattice_node* buttom_=0;
    int int_size_=0;
    mv_lattice* to_lattice_=0;
    std::map<string,mv_interval*>* map_intervals_=0;//intervals that are added by mv_interval::add_interval
    std::map<std::pair<float,float>,mv_interval*>* map_all_intervals_=0;
};

void test_intervals();
mv_interval* create_interval_set(string prefix, int num_nodes);

class mv_exception: public exception
{
public:
    mv_exception(string msg):msg_(msg){}
    
    virtual const char* what() const throw()
    {
        return "My exception happened";
    }
private:
    string msg_;
}; 

}
#endif /* MV_INTERVAL_H */

