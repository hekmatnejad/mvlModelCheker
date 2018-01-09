/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   MvLtlModel.cpp
 * Author: mamad
 * 
 * Created on January 17, 2017, 2:48 PM
 */

#include "MvLtlModel.h"
//#include <ostream>
//#include <istream>
//#include <iostream>
//#include <fstream>

namespace mvspot {

    template< class T>
    string * set2string(set<T> s){
        int size = s.size();
        string * res = new string[size];  
        int i = 0;
        ostringstream os;
        for (typename set<T>::iterator it = s.begin() ; it != s.end(); it++ , i++){
            os << ((T)(*it));
            res[i] = os.str();
        }
        return res;      
    }
    
    mv_ltl_model::mv_ltl_model() {
    }

    mv_ltl_model::mv_ltl_model(const mv_ltl_model& orig) {
    }

    mv_ltl_model::~mv_ltl_model() {
    }

    std::ostream & operator<<(std::ostream & str, mv_ltl_model & obj) {
        // print something from v to str, e.g: Str << v.getX();
        str << obj.toString();
        return str;
    }

    std::string mv_ltl_model::toString() {
        string str = "";
        return str;
    }

    /*===============================================
     * mv_lattice:
     * Multi Valued Logic Lattice
    ===============================================*/

    mv_lattice::~mv_lattice() {
        
    }

    std::ostream& operator<<(std::ostream& str, const mv_lattice& obj) {
        str << obj.toString();
        return str;
    }

    string mv_lattice::toString() const{
        string str = "";
        if (this->nodes_->size() == 0)
            return str;
        for (set<mvspot::lattice_node*>::iterator it
                = this->nodes_->begin(); it != this->nodes_->end(); it++) {
            str += "{";
            int cnt = ((mvspot::lattice_node*)(*it))->getAbove_nodes()->size();
            if (cnt > 0){
                for (set<mvspot::lattice_node*>::iterator itt
                        = ((mvspot::lattice_node*)(*it))->getAbove_nodes()->begin();
                        itt != ((mvspot::lattice_node*)(*it))->getAbove_nodes()->end(); itt++) {
                    str += ((mvspot::lattice_node*)(*itt))->getName();
                    if ((--cnt) > 0)
                        str += ",";
                    else
                        str += "}";
                } 
            }else
                str += "}";

            str += " <--above- " + ((mvspot::lattice_node*)(*it))->getName() + "=" +
                    std::to_string(((mvspot::lattice_node*)(*it))->getValue()) + " -below--> {";

            cnt = ((mvspot::lattice_node*)(*it))->getBelow_nodes()->size();
            if ( cnt > 0){
                for (set<mvspot::lattice_node*>::iterator itt
                        = ((mvspot::lattice_node*)(*it))->getBelow_nodes()->begin();
                        itt != ((mvspot::lattice_node*)(*it))->getBelow_nodes()->end(); itt++) {
                    str += ((mvspot::lattice_node*)(*itt))->getName();
                    if ((--cnt) > 0)
                        str += ",";
                    else
                        str += "}";
                } 
            }else
                str += "}";
        str += "\n";

        }
        
        return str;
    }

/*===============================================
     * lattice_node:
     * Lattice Nodes in Multi_valued_logic
    ===============================================*/
    string lattice_node::toString() const{
        return name+"("+to_string(value)+")";
    }
    
    std::ostream & operator<<(std::ostream & str, const lattice_node & obj) {
        // print something from v to str, e.g: Str << v.getX();
        str << obj.toString();
        return str;
    }

    bool lattice_node::add_above_of(lattice_node * target) {
        
        if (this->below_nodes.count(target) > 0)//check if the target is already below the current node
            return true;
        if (this->getValue() < target->getValue())//check if the value of target is less than the current node
            return false;
        else//add the target below of the current node
        {
            pair<set<lattice_node*>::iterator,bool> res = this->below_nodes.insert(target);
            if ((bool)res.second == false)
                return false;
            res = target->above_nodes.insert(this);
            if ((bool)res.second == false)
                return false;
            
        }
        
        return true;
    }

    bool lattice_node::add_bellow_of(lattice_node * target) {
        
        if(this->above_nodes.count(target) > 0)
            return true;
        if(this->getValue() > target->getValue())
            return false;
        else
        {
            pair<set<lattice_node*>::iterator,bool> res = this->above_nodes.insert(target);
            if ((bool)res.second == false)
                return false;
            res = target->below_nodes.insert(this);
            if ((bool)res.second == false)
                return false;
        }

        return true;
    }
    
}