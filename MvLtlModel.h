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
#include <spot/parseaut/public.hh>
#include <spot/twa/bddprint.hh>
//#include "mv_interval.h"
#include <spot/twa/bdddict.hh>
#include <spot/tl/apcollect.hh>
#include <bddx.h>
#include <queue>
#include <spot/twa/formula2bdd.hh>
#include <chrono>

using namespace std;
//using namespace spot;


namespace mvspot {
    template<class T>
    string * set2string(set<T> s);


    class mv_ltl_model : public std::enable_shared_from_this<mv_ltl_model>{
    public:
        mv_ltl_model();
        mv_ltl_model(const mv_ltl_model& orig);
        virtual ~mv_ltl_model();
        string toString();
        friend std::ostream & operator<<(std::ostream & str, mv_ltl_model & obj);
    private:

    };
    
    //=================================================================//

    class lattice_node : public std::enable_shared_from_this<lattice_node> {
    public:

        //std::set<Node, bool (*)(const Node&, const Node&)> nodeSet(compareNode);
    
        bool operator< (const lattice_node& obj) const {
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
            float res = (lhs->getValue() - rhs->getValue());
            if (res != 0)
                return (res > 0);
            else
                //return ((lhs->getName().compare(rhs->getName())) > 0);
            return true;
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
            
    class mv_lattice : public std::enable_shared_from_this<mv_lattice> {
    public:

        mv_lattice(string top_name="T", float top_val=1.0, string buttom_name="F", float buttom_val=0.0){
            top_ = new lattice_node(top_name, top_val);
            buttom_= new lattice_node(buttom_name, buttom_val);
            //top_.setName(top_name);
            //top_.setValue(top_val);
            //buttom_.setName(buttom_name);
            //buttom_.setValue(buttom_val);
            nodes_ = new set<lattice_node*, node_compare>();
            //join_irreducibles_ = new set<lattice_node*, node_compare>();
            nodes_->insert(top_);
            nodes_->insert(buttom_);
        }

        mv_lattice(lattice_node* top, lattice_node* buttom)
        {
            //cout << "<<<<\n";
            top_ = top;
            buttom_ = buttom;
            nodes_ = new set<lattice_node*, node_compare>();
            //join_irreducibles_ = new set<lattice_node*, node_compare>();
            nodes_->insert(top_);
            nodes_->insert(buttom_);
        }
        
        mv_lattice(const mv_lattice& orig){
            //std::cout << "This constructor need to be coded.\n";
            top_ = orig.getTop_();
            buttom_ = orig.getButtom_();
            nodes_ = orig.getNodes_();
            //join_irreducibles_ = orig.get_join_irreducibles();
        }
        
        virtual ~mv_lattice();
        
        string toString() const;
        friend std::ostream & operator<<(std::ostream & str, const mv_lattice & obj);
        void auto_update_values();
        
        //std::set<lattice_node*, node_compare>* get_join_irreducibles() const{
        //    //todo: first update then return
        //    return join_irreducibles_;
        //}
        
        lattice_node* getButtom_() const{
            return buttom_;
        }

        std::set<lattice_node*, node_compare> * getNodes_() const{

            return nodes_;
        }

        lattice_node* getTop_() const{
            return top_;
        }

    private:
      lattice_node* top_;  
      lattice_node* buttom_; 
      //std::set<lattice_node,lattice_node::node_compare> nodes_;
      std::set<lattice_node*, node_compare>* nodes_;
      //std::set<lattice_node*, node_compare>* join_irreducibles_;
        
    };

    
class mv_interval : public std::enable_shared_from_this<mv_interval> {
public:
    mv_interval(string name);
    mv_interval(string name, float low, float high);
    mv_interval(string name, lattice_node* intervals, int size) throw();
    mv_interval(const mv_interval& orig);
    virtual ~mv_interval();
    mv_interval* add_interval(string symbol, float low, float high);
    mv_interval* parse_string_to_interval(string symbol);
    mv_interval* get_interval(float low, float high);

    lattice_node* getTop();
    lattice_node* getButtom();
    //lattice operators
    float complement_mv(float given);
    mv_interval* join_mv(mv_interval* left, mv_interval* right);
    mv_interval* meet_mv(mv_interval* left, mv_interval* right);
    mv_interval* not_mv(mv_interval* given);
    void negate_mv(mv_interval* given);
    mv_interval* psi_mv(mv_interval* base, mv_interval* given);
    string get_as_str();
    string get_as_str(float low, float high);
    std::pair<float,float> get_as_pair();
    
    bool isFalse() {
        return (getButtom()->getValue() == MIN_VAL_ && getTop()->getValue() == MIN_VAL_);
    }

    bool isTrue() {
        return (getButtom()->getValue() == MAX_VAL_ && getTop()->getValue() == MAX_VAL_);
    }
    
    
    string getName() const {
        return name_;
    }

    void setName_(string name) {
        this->name_ = name;
    }

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
    static constexpr float MIN_VAL_ = 0;
    static constexpr float MAX_VAL_ = 1;
    bool is_TO_lattice_container_ = false;
    string name_ = "";
    lattice_node* intervals_=0;
    lattice_node* top_=0;
    lattice_node* buttom_=0;
    int int_size_=0;
    mv_lattice* to_lattice_=0;
    std::map<string,mv_interval*>* map_intervals_=0;//intervals that are added by mv_interval::add_interval
    std::map<std::pair<float,float>,mv_interval*>* map_all_intervals_=0;
};

void test_intervals();
mv_interval* create_interval_set(string name, string prefix, int num_nodes);

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

class interval_bdd : public std::enable_shared_from_this<interval_bdd> {
public:
    static std::map<std::string,mv_interval*>* map_interval_base_;
    static std::map<std::string,mv_interval*>* map_interval_model_;
    static mv_interval* shared_intervals_;
    interval_bdd(spot::bdd_dict_ptr dict){// : dict_(dict){
    }
    
    static void simplify_interval_formula_twa(spot::twa_graph_ptr& aut);
    static void simplify_interval_formula_twa_graph(spot::twa_graph_ptr& aut);
    static std::pair<mv_interval*,bdd> apply_and(bdd base, bdd model, spot::bdd_dict_ptr dict_);
    static mv_interval* symbol_formual_to_interval(string formula);
private:
    static spot::formula simplify_conjuctive_formula(spot::formula f, const spot::bdd_dict_ptr& d);
    static std::pair<spot::formula,spot::formula> prepare_apply_and(spot::formula f_base, spot::formula f_model, bool negate, spot::bdd_dict_ptr dict_);
};
    

}//mvspot namespace



#endif /* MVLTLMODEL_H */

