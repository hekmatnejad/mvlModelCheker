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


using namespace std;
//using namespace spot;


namespace spot
{
//  class mv_twa;
//  typedef std::shared_ptr<mv_twa> mv_twa_ptr;
//  typedef std::shared_ptr<const mv_twa> const_mv_twa_ptr;
//
//  class mv_twa_graph;
//  typedef std::shared_ptr<const mv_twa_graph> const_mv_twa_graph_ptr;
//  typedef std::shared_ptr<mv_twa_graph> mv_twa_graph_ptr;
//
//  class mv_twa_product;
//  typedef std::shared_ptr<const mv_twa_product> const_mv_twa_product_ptr;
//  typedef std::shared_ptr<mv_twa_product> mv_twa_product_ptr;
}



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
/*
    class mv_interval{
    public:
        mv_interval(float low, float high): low_(low), high_(high){} 
        
        float get_low(){
            return low_;
        }
        
        float get_high(){
            return high_;
        }
    private:
        float low_;
        float high_;
        mv_interval();
    };
*/
    
class mv_interval : public std::enable_shared_from_this<mv_interval> {
public:
    mv_interval(string name);
    mv_interval(string name, float low, float high);
    mv_interval(string name, lattice_node* intervals, int size) throw();
    mv_interval(const mv_interval& orig);
    virtual ~mv_interval();
    void add_interval(string symbol, float low, float high);
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
    static std::map<int,mv_interval*>* map_interval_base_;
    static std::map<int,mv_interval*>* map_interval_model_;
    static mv_interval* shared_intervals_;
    interval_bdd(spot::bdd_dict_ptr dict){// : dict_(dict){
    }
    
    static mv_interval* apply_and(bdd base, bdd model, spot::bdd_dict_ptr dict_);
    
private:
    //static bdd_dict_ptr dict_;
};
    


/*
class SPOT_API mv_twa : public spot::twa{
public:
        mv_twa(const spot::bdd_dict_ptr& d) :
        twa(d) {
        }
    
};  

class SPOT_API mv_twa_graph : public spot::twa{
public:
        mv_twa_graph(const spot::bdd_dict_ptr& dict) :
        twa(dict) {
        }
    
};  


class SPOT_API mv_twa_product final: public spot::twa_product{
public:
  mv_twa_product(const spot::const_twa_ptr& left, const spot::const_twa_ptr& right,
                    mvspot::mv_interval* intervals);
protected:
  const spot::state* left_init_;
  const spot::state* right_init_;
  mvspot::mv_interval* intervals_;
};

class SPOT_API mv_fair_kripke: public mv_twa , public spot::fair_kripke{
  public:
    mv_fair_kripke(const spot::bdd_dict_ptr& d)
      : mv_twa(d), fair_kripke(d)
      {
      }

    /// \brief The condition that label the state \a s.
    ///
    /// This should be a conjunction of atomic propositions.
    //virtual bdd state_condition(const spot::state* s) const = 0;

    /// \brief The acceptance mark that labels state \a s.
    //virtual spot::acc_cond::mark_t
    //  state_acceptance_mark(const spot::state* s) const = 0;    
};


//namespace mvspot{
class mv_kripke : public mv_fair_kripke {
public:
        mv_kripke(mv_interval* intervals, const spot::bdd_dict_ptr& d) :
        mv_fair_kripke(d){
            intervals_ = intervals;
        }

    mv_interval* getIntervals(){
        return intervals_;
    }
private:
    mv_interval* intervals_;
};
//}    
*/

}//mvspot namespace



#endif /* MVLTLMODEL_H */

