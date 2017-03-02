/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   MvLtlModel.h
 * Author: mamad
 *
 * Created on January 17, 2017, 2:48 PM
 */

#ifndef MVLTLMODEL_H
#define MVLTLMODEL_H

//#include <ostream>
//#include <istream>
//#include <iostream>
//#include <fstream>
#include <iosfwd>
#include <spot/kripke/kripke.hh>
//#include "mvkripke.h"
#include <spot/twaalgos/dot.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twa/twaproduct.hh>
//#include "mvtwaproduct.h"

#include <spot/twaalgos/emptiness.hh>

#include <spot/twaalgos/hoa.hh>
#include <spot/twa/twagraph.hh>
#include <stack>

#include <cmath>

#include <spot/kripke/kripkegraph.hh>
//#include "mvkripkegraph.h"


using namespace std;
using namespace spot;

namespace mvspot {
    template<class T>
    string * set2string(set<T> s);


    class mv_ltl_model {
    public:
        mv_ltl_model();
        mv_ltl_model(const mv_ltl_model& orig);
        virtual ~mv_ltl_model();
        string toString();
        friend std::ostream & operator<<(std::ostream & str, mv_ltl_model & obj);
    private:

    };
    
    //=================================================================//

    class lattice_node{
    public:

        //std::set<Node, bool (*)(const Node&, const Node&)> nodeSet(compareNode);
    
    bool operator< (const lattice_node& obj) const {
        //cout << "compare2: " << (this->compare(&obj) < 0) << endl;
        //cout << "****"<<endl;
        return (this->compare(&obj) > 0) ? true: false;
    }

        
        lattice_node() {
            above_nodes = set<lattice_node*>();
            below_nodes = set<lattice_node*>();
        }

        lattice_node(string name_, float value_) : name(name_), value(value_) {
            lattice_node();
        }
        
        string toString() const;
        
        float compare(const lattice_node *other) const
        {
            //cout << this->hash() << " >> " << other->hash() << " : " << this->getName() <<" "<<other->getName() << endl;
            //cout << *this << " , " << *other << endl;
            float res = (this->getValue() - other->getValue());
            if (res != 0)
                return res;
            else
                return (other->getName().compare(this->getName()));
        }
        
        float hash() const
        {
            return 31*(getValue()+1) * log(std::hash<std::string>{}(getName()));
        }
        
        string getName() const {
            return name;
        }

        void setName(string name) {
            this->name = name;
        }

        float getValue() const {
            return value;
        }

        void setValue(float value) {
            this->value = value;
        }

        std::set<lattice_node*> * getAbove_nodes() {
            return &above_nodes;
        }

        std::set<lattice_node*> * getBelow_nodes() {
            return &below_nodes;
        }

        
        bool add_bellow_of(lattice_node * target);
        bool add_above_of(lattice_node * target);

        friend std::ostream & operator<<(std::ostream & str, const lattice_node & obj);

        
    private:
        string name;
        float value;
        std::set<lattice_node*> above_nodes;
        std::set<lattice_node*> below_nodes;
    };
      
    struct node_compare {//: public std::binary_function<lattice_node*,lattice_node*,bool>{

        bool operator()(lattice_node* lhs, lattice_node* rhs) {
            //cout << "compare1: " << endl;
            float res = (lhs->getValue() - rhs->getValue());
            if (res != 0)
                return (res > 0);
            else
                return ((lhs->getName().compare(rhs->getName())) > 0);
            //return true;
        }
    };
#if 0
            bool compare( const lattice_node* lhs, const lattice_node* rhs) {
                cout << "compare1: "<< endl;
                return true;
                /*
                float res = (lhs->getValue() - rhs->getValue());
                if (res != 0)
                    return (res>0);
                else
                    return ((lhs->getName().compare(rhs->getName()))>0);*/
            }
#endif        
    class mv_lattice {
    public:

        mv_lattice(){
            //top_ = lattice_node("True", 1.0);
            //buttom_= lattice_node("False", 0.0);
            top_.setName("T");
            top_.setValue(1);
            buttom_.setName("F");
            buttom_.setValue(0);
            nodes_ = set<lattice_node*, node_compare>();
            nodes_.insert(&top_);
            nodes_.insert(&buttom_);
        }
        mv_lattice(const mv_lattice& orig){
            
        }
        virtual ~mv_lattice();
        string toString() const;
        friend std::ostream & operator<<(std::ostream & str, const mv_lattice & obj);

        void auto_update_values();


        lattice_node* getButtom_() {
            return &buttom_;
        }

        std::set<lattice_node*, node_compare> * getNodes_() {

            return &nodes_;
        }

        lattice_node* getTop_() {
            return &top_;
        }

    private:
      lattice_node top_;  
      lattice_node buttom_; 
      //std::set<lattice_node,lattice_node::node_compare> nodes_;
      std::set<lattice_node*, node_compare> nodes_;
     
        
    };


}



#endif /* MVLTLMODEL_H */

