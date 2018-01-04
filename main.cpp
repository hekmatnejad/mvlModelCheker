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
//#include <spot/tl/dot.hh>
//#include <spot/taalgos/dot.hh>
#include "secondary.h"
using namespace std;

#define PRINT_DEBUG_DATA 1
#define NUM_POSITIONS 8
#define X_END 3
#define Y_END 3
#define NUM_LOCATIONS (X_END+1)*(Y_END+1)
#define X_START 0
#define Y_START 0
#define MAX_RUN_TIME 8//1580 //:RUN FINISHED; exit value 0; real time: 3s; user: 230ms; system: 700ms
#define X_TARGET 3
#define Y_TARGET 3
const int NUM_CARS = 2;

void model_1(string formula);
void model_2(string formula);
void model_3(string formula);
void model_4(string formula);
void mv_latice_test_1();
void test();
void dfs(spot::const_twa_graph_ptr aut, bdd query);
int get_random(int low, int high);
static spot::parsed_aut_ptr read_model_aut;
static spot::kripke_graph_ptr kg_model;
static spot::twa_graph_ptr aut_model;
//this is a temporarly fix instead of reading labels of graph's node
const static float X_POS[]={0,0,1,1,0,1,2,2,2,0,1,2,3,3,3,3};
const static float Y_POS[]={0,1,1,0,2,2,2,1,0,3,3,3,3,2,1,0};
void get_state_number_from_xy();
class model_node {//class for keeping the sorted nodes on a set
public:
    model_node() {
    }

    model_node(float value, float x, float y) :
    value(value), x(x), y(y) {
    }
    float GetValue() const {
        return value;
    }

    float GetX() const {
        return x;
    }

    float GetY() const {
        return y;
    }

private:    
    float value;
    float x;
    float y;
};
struct node_compare {//comparator for sorting nodes based on least distance from target

    bool operator()(model_node* lhs, model_node* rhs) {
        float res = (lhs->GetValue() - rhs->GetValue());
        if (res != 0)
            return (res <= 0);
        else
            return true;
    }
};
void create_all_model_locations();
model_node* * sorted_states_connected_to(unsigned state);
int gloabl_size_of_connected_nodes[NUM_LOCATIONS];
static int xy2number[Y_END+1][X_END+1];
static model_node* * all_model_locations[NUM_LOCATIONS];
static spot::bdd_dict_ptr shared_dict = spot::make_bdd_dict();
float CERTAINTY_THREASHOLD = 1;
/*
 * 
 */
int main(int argc, char** argv) {
    //test();
    //model_3("F !fire");
    //return 0;
    std::cout << "started...\n";
    cout << mvspot::getVersion() << "\n" <<mvspot::getBuild() <<"\n" ;
    mvspot::mv_ltl_model model = mvspot::mv_ltl_model();
    std::cout << model << std::endl;
    std:ifstream inFile;
    //string model_filename = "ocean_model.dot";
    string model_filename = "sirle2018/road_network_model.dot";
    inFile.open(model_filename);
    if(!inFile.is_open()){
        std::cout << "Generating the base model file.\n";
        //generate a mock model and write it to a file for repetitive use
        //model_generator::generate_model("ocean_model.dot",X_END,Y_END,X_TARGET,Y_TARGET,shared_dict);
    }
    else
        inFile.close();
     
    //if(true)return 0;
    srand (time(NULL));
    read_model_aut = Util::readAutFromFile(model_filename,false,shared_dict);
    if(!read_model_aut || read_model_aut->errors.size()>0)
    {
        cout << "could not read the model from file!";
        exit(0);
    }
    else{
        cout << "model loaded from: " << model_filename << endl;
        Util::write2File("sirle2018/road_network_graph.dot", read_model_aut->aut, "k");

    }
    kg_model = read_model_aut->ks;
    aut_model = read_model_aut->aut;
    
    std::cout << ">>>>>>> " << aut_model->get_init_state_number() << "\n";
    
    //for(int i=0; i<16; i++)
    //{
    //    model_node ** result = sorted_states_connected_to(i);
    //    cout<< "size: " << gloabl_size_of_connected_nodes << endl;
    //}
    
    //spot::print_dot(std::cout, aut_model,"k");
    //if(true)return 0;
    /*
    twa_succ_iterator* s1 =  aut_model->succ_iter(aut_model->get_init_state());
    twa_succ_iterator* s2 =  aut_model->succ_iter(aut_model->get_init_state());
    s1->first();
    s2->first();
    cout << "s1: " << aut_model->state_number(s1->dst()) <<  "  s2: " << aut_model->state_number(s2->dst()) << endl;
    s1->next();
    cout << "s1: " << aut_model->state_number(s1->dst()) <<  "  s2: " << aut_model->state_number(s2->dst()) << endl;
    s1->~twa_succ_iterator();
    s2->~twa_succ_iterator();
    */
    model_4("GF(odd_x) -> GF(odd_y)");
    
    cout << "done!\n";
    return 0;
}

int get_random(int low, int high)
{
    return (int)(low + (float)rand()/RAND_MAX*(high-low));
}

mutex size_mutex;
//this function sorts the visiting graph nodes based on the given map and 
//distance values toward the target
void create_all_model_locations(){
    auto& gr = aut_model->get_graph();
    unsigned edge;
    unsigned dst;    
    for(int src=0; src<NUM_LOCATIONS; src++){
        edge = gr.state_storage(src).succ;
        std::set<model_node*, node_compare> around_nodes;
        while(edge>0){
            dst = gr.edge_storage(edge).dst;
            float value = ((X_POS[dst]-X_END)*(X_POS[dst]-X_END)+(Y_POS[dst]-Y_END)*(Y_POS[dst]-Y_END));
            model_node* node = new model_node(value,X_POS[dst],Y_POS[dst]);
            around_nodes.insert(node);
            //std::cout<< "edge: " << edge << ", src: " << src << ", dst: " << dst << ", distance: " << node->GetValue() <<endl;
            edge = gr.edge_storage(edge).next_succ;
        }
        //model_node* result[around_nodes.size()];
        all_model_locations[src] = new model_node*[around_nodes.size()];
        int cnt = 0;
        for(std::set<model_node*>::iterator it = around_nodes.begin(); it!=around_nodes.end(); it++){
            all_model_locations[src][cnt++] = new model_node(((model_node*)(* it))->GetValue(),((model_node*)(* it))->GetX(),
                            ((model_node*)(* it))->GetY());
            //cout<<"value: "<<all_model_locations[src][cnt-1]->GetValue()<<endl;
        }
        gloabl_size_of_connected_nodes[src] = around_nodes.size();
    }
    /*cout<<"------TEST-------\n\n";
    for(int i=0; i<NUM_LOCATIONS; i++){
        for(int j=0; j<gloabl_size_of_connected_nodes[i]; j++){
            cout<<"("<<all_model_locations[i][j]->GetX()<<","<<all_model_locations[i][j]->GetY()<<")";
        }
        cout<<i<<endl;
    }*/
}

void get_state_number_from_xy(){
    for(int i=0; i<= X_END; i++){
        for(int j=0; j<= Y_END; j++){
            for(int m=0; m< NUM_LOCATIONS; m++){
                if((int)X_POS[m]==i && (int)Y_POS[m]==j){
                    xy2number[i][j] = m;
                    //std::cout << i <<" " << j << " state: " << m << endl;
                    break;
                }
            }
        }
    }
}
float mock_current[4][4] = {{90,90,90,90},{0,0,0,90},{0,0,0,90},{0,0,0,90}};
float calculate_certainty(float x1, float y1, float x2, float y2){
    float certainty = 1;
    //certainty = get_random(0,10)/10.0;//WRONG: nondeterminism
    float c1 = mock_current[(int)x1][(int)y1];
    float c2 = mock_current[(int)x2][(int)y2];
    certainty =  1.0 - abs(c1-c2)/360.0;
    cout << "cert: " <<certainty << endl;
    return certainty;
}

void dfs(spot::const_twa_graph_ptr aut, bdd query)
{
  std::vector<bool> seen(aut->num_states());
  std::stack<unsigned> todo;    // Now storing edges numbers
  auto& gr = aut->get_graph();
  auto push_state = [&](unsigned state)
    {
      todo.push(gr.state_storage(state).succ);
      seen[state] = true;
    };
  push_state(aut->get_init_state_number());
  while (!todo.empty())
    {
      unsigned edge = todo.top();
      todo.pop();
      if (edge == 0U)           // No more outgoing edge
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


class marine_robot_state: public spot::state
{
private:
    unsigned* state_num_ ;
    twa_succ_iterator** aut_succ_;
    spot::twa_graph_ptr org_model_;
  //float x_;
  //float y_;    
  float time_ = 0;
  bool is_certain_ = false;// has a bdd equvalent for certainty
public:
  //marine_robot_state(float x = 0, float y = 0, float time = 0, bool is_certain = true)
  //  : x_((int)x % (X_END+1)), y_((int)y % (Y_END+1)), time_(time), is_certain_(is_certain)
  //{
  //}
    
  marine_robot_state(unsigned* state_num=0, float time = 0, bool is_certain = true, twa_succ_iterator** aut_succ=0, spot::twa_graph_ptr org_model=0)
    : time_(time), is_certain_(is_certain), org_model_(org_model)
  {
        aut_succ_ = new twa_succ_iterator* [NUM_CARS];
        state_num_ = new unsigned [NUM_CARS];
      for(int i=0; i<NUM_CARS; i++)
      {
          aut_succ_[i] = aut_succ[i];
          state_num_[i] = state_num[i];
      }
  }
    /*
    marine_robot_state(const spot::state* copy_from)
    {
        auto ss = static_cast<const marine_robot_state*>(copy_from);
        std::cout << "in copy const........\n";
        state_num_ = ss->state_num_; 
        aut_succ_ = ss->aut_succ_; 
        is_certain_ = ss->is_certain_; 
        time_ = ss->time_; 
    }
  */
  unsigned* get_state_num() const
  {
      return state_num_;
  }
  
  twa_succ_iterator** get_aut_succ() const
  {
      return aut_succ_;
  }
/*  
  float get_x() const
  {
    return x_;
  }

  float get_y() const
  {
    return y_;
  }
*/  
  float get_time() const
  {
      return time_;
  }
  
  bool is_certain() const
  {
      return is_certain_;
  }
   
  marine_robot_state* clone() const override
  {
    //return new marine_robot_state(x_, y_, time_, is_certain_);
    return new marine_robot_state(state_num_, time_, is_certain_, aut_succ_);
  }

  size_t hash() const override
  {
      //assuming all variables are positive
      int hash = 23;
      for(int i=0; i<NUM_CARS; i++)
      {
        hash = hash*31 + state_num_[i];
      }
      //hash = hash*31 + aut_succ_->dst()->hash();
      //hash = hash*31 + x_;
      //hash = hash*31 + y_;
      hash = hash*31 + time_;
      hash = hash*31 + is_certain_;
      return hash;
    //return  (x_ + y_) * (x_ + y_ + 1) / 2 + x_;
    //return (x_ * 31) + 13*y_ + time_*7111 + (is_certain_ ? 101 : 1001);
  }

  int compare(const spot::state* other) const override
  {
    auto o = static_cast<const marine_robot_state*>(other);
    size_t oh = o->hash();
    size_t h = hash();
    if (h < oh)
      return -1;
    else
      return h > oh;
  }
  
};

class marine_robot_succ_iterator: public spot::kripke_succ_iterator
{
private:
    //unsigned state_num_;
    twa_succ_iterator** aut_succ_;
    spot::twa_graph_ptr org_model_;
  //float x_;
  //float y_;
  float time_;
  //unsigned char pos_;
  //int num_pos_=0;
public:
  //marine_robot_succ_iterator(float x, float y, float time, bdd cond)
  //  : kripke_succ_iterator(cond), x_(x), y_(y), time_(time)
  //{
 //   num_pos_ = gloabl_size_of_connected_nodes[xy2number[(int)x_][(int)y_]];
 //   //cout<< "size sorted_positions: <constructor>" << num_pos_ << endl;
 // }

    marine_robot_succ_iterator(unsigned* state_num, spot::twa_graph_ptr org_model, float time, bdd cond)
    : kripke_succ_iterator(cond), org_model_(org_model), time_(time)
  {
    //num_pos_ = gloabl_size_of_connected_nodes[xy2number[(int)x_][(int)y_]];
        aut_succ_ = new twa_succ_iterator*[NUM_CARS];
        for(int i=0; i<NUM_CARS; i++)
            aut_succ_[i] = org_model->succ_iter(org_model->state_from_number(state_num[i]));
  }

  bool first() override
  {
    bool res = false;
    for(int i=0; i<NUM_CARS; i++)
        res |=  aut_succ_[i]->first();
    //if(x_==X_TARGET && y_==Y_TARGET){
    //    pos_ = 0;
    //    return true;
    //}
    //if(time_==(MAX_RUN_TIME-1))
    //    return false;
    //pos_ = 0;
    return res;
  }

  bool next() override
  {
    bool res = false;
    for(int i=0; i<NUM_CARS; i++)
        res |= aut_succ_[i]->next();
    return res;
    //pos_++;
    //if(x_==X_TARGET && y_==Y_TARGET){
    //    pos_=num_pos_;
    //    return false;
   // }
    //return (pos_ < num_pos_);          // More successors?
  }

  bool done() const override
  {
      bool res = true;
    for(int i=0; i<NUM_CARS; i++)
        res &= aut_succ_[i]->done();
      return res;
      //either time-out or explored all around locations
    //return pos_ == num_pos_ || time_==(MAX_RUN_TIME-1);
  }

  marine_robot_state* dst() const override
  {
      
      unsigned state_num[NUM_CARS];
      twa_succ_iterator* tmp_succ[NUM_CARS];
    for(int i=0; i<NUM_CARS; i++){
        state_num[i] = org_model_->state_number(aut_succ_[i]->dst());
        tmp_succ[i] = org_model_->succ_iter(aut_succ_[i]->dst());
    }
      //std::cout << "~~~~~~~~~ " << org_model_->get_dict()->bdd_map[org_model_->succ_iter(aut_succ_->dst())->cond().id()].f << std::endl;
     
      //std::cout << "state_num >>>> " << state_num << "     " << org_model_->succ_iter(aut_succ_->dst())->cond() << std::endl;
      return new marine_robot_state(state_num, 0, true, tmp_succ, org_model_);
      /*
      float arrival_time = 0;
      float new_x = 0;
      float new_y = 0;
      //find a new position based on the available around locations
      new_x = all_model_locations[xy2number[(int)x_][(int)y_]][pos_]->GetX();
      new_y = all_model_locations[xy2number[(int)x_][(int)y_]][pos_]->GetY();
      //reach the target location, break and return
      if(x_==X_TARGET && y_==Y_TARGET){
        //cout <<"***" <<x_ <<',' << y_ <<",t: " << time_ << endl;
        return new marine_robot_state(x_, y_, time_, true);
      }
      else{
        //need to be updated by a forecasted/calculated elapsed time
        arrival_time = (int)(time_ + 1) % MAX_RUN_TIME;
        cout <<x_<<','<<y_<<"->"<<new_x <<',' << new_y <<",t: " << arrival_time << endl;
      }
      float certainty_value = calculate_certainty(x_,y_,new_x,new_y);
      bool is_certian = ((certainty_value>=CERTAINTY_THREASHOLD) ? true : false);
      //create new state to be explored
      return new marine_robot_state(new_x, new_y, arrival_time, is_certian);
       */
  }
/*
  void recycle(float x, float y, float time, bdd cond)
  {
    x_ = x;
    y_ = y;
    time_ = time;
    //you can also put this in the first() method
    num_pos_ = gloabl_size_of_connected_nodes[xy2number[(int)x_][(int)y_]];
    //cout<< "size sorted_positions <recycle>: " << num_pos_ << endl;
    spot::kripke_succ_iterator::recycle(cond);
  }
*/
//  void recycle(unsigned state_num, float time, twa_succ_iterator* aut_succ, bdd cond)
  void recycle(twa_succ_iterator* aut_succ[], bdd cond)
  {
      //state_num_ = state_num;
    //time_ = time;
      for(int i=0; i<NUM_CARS; i++)
        aut_succ_[i] = aut_succ[i];
    //you can also put this in the first() method
    //num_pos_ = gloabl_size_of_connected_nodes[xy2number[(int)x_][(int)y_]];
    //cout<< "size sorted_positions <recycle>: " << num_pos_ << endl;
    spot::kripke_succ_iterator::recycle(cond);
  }
};

class marine_robot_kripke: public spot::kripke
{
private:
  //bdd odd_x_;
  //bdd odd_y_;
  bdd goal_;
  bdd certainty_;
  string str_certainty_;
  spot::twa_graph_ptr org_model_;
  unsigned* init_state_;
  list<string>* lst_str_loc_;
  //list<bdd> lst_loc_bdd_;
  std::map<string,bdd>* map_str_bdd_loc_;

public:
  marine_robot_kripke(const spot::bdd_dict_ptr& d, const string certainty,const spot::twa_graph_ptr org_model, const unsigned init_state[], list<string> lst_str_loc[])
    : spot::kripke(d),str_certainty_(certainty), org_model_(org_model)
  {
    //odd_x_ = bdd_ithvar(register_ap("odd_x"));
    //odd_y_ = bdd_ithvar(register_ap("odd_y"));
    goal_ = bdd_ithvar(register_ap("goal"));
    certainty_ = bdd_ithvar(register_ap(certainty));//registers the requested certainty 
    //create_all_model_locations();//create the ordered directions to explore at each position
    //get_state_number_from_xy();//create a map table for converting (x,y) to its state number
    lst_str_loc_ = new list<string>[NUM_CARS];
    map_str_bdd_loc_ = new std::map<string,bdd>[NUM_CARS];
    init_state_ = new unsigned[NUM_CARS];
    for(int i=0; i<NUM_CARS; i++){
        lst_str_loc_[i] = lst_str_loc[i];
        init_state_[i] = init_state[i];
        for(std::list<string>::iterator it=lst_str_loc_[i].begin(); it!=lst_str_loc_[i].end(); it++ ){
            bdd res = bdd_ithvar(register_ap(*it));
            map_str_bdd_loc_[i][*it]=res;
            cout << "@@@ @@@ " << *it << "  " << res << "  bdd: " << map_str_bdd_loc_[i][*it] <<  endl;
        }
    }
  }

  marine_robot_state* get_init_state() const override
  {
    //return new marine_robot_state();
      twa_succ_iterator* aut_succ[NUM_CARS];
    for(int i=0; i<NUM_CARS; i++)
    {
        aut_succ[i] = org_model_->succ_iter(org_model_->state_from_number(init_state_[i]));
    }
    return new marine_robot_state(init_state_, 0, true, aut_succ, org_model_);
  }

    marine_robot_succ_iterator* succ_iter(const spot::state* s) const override
    {
      auto ss = static_cast<const marine_robot_state*>(s);
      unsigned state_num[NUM_CARS];
      for(int i=0; i<NUM_CARS; i++)
        state_num[i] = ss->get_state_num()[i];
      //twa_succ_iterator* aut_succ = org_model_->succ_iter(org_model_->state_from_number(state_num));//todo: change 0 to state_num
      //float x = ss->get_x();
      //float y = ss->get_y();
      float time = ss->get_time();
      bdd cond = state_condition(ss);
      std::cout << "cond -----> "<< cond << std::endl;
      if (iter_cache_)
        {
          auto it = static_cast<marine_robot_succ_iterator*>(iter_cache_);
          iter_cache_ = nullptr;    // empty the cache
          //it->recycle(x, y, time, cond);
          it->recycle(ss->get_aut_succ(), cond);
          //it->recycle(state_num, time, ss->get_aut_succ(), cond);
          return it;
        }
      //return new marine_robot_succ_iterator(x, y, time, cond);
      return new marine_robot_succ_iterator(state_num, org_model_, time, cond);
    }

    list<string>* get_lst_str_loc() const
    {
        return lst_str_loc_;
    }
    
    std::map<string,bdd>* get_map_str_bdd_loc() const
    {
        return map_str_bdd_loc_;
    }
    
  bdd state_condition(const spot::state* s) const override
  {
      cout << "@@@@@@ ---------  @@@@@@\n";
    auto ss = static_cast<const marine_robot_state*>(s);
    bdd res = bddtrue;
    list<string>* tmp_symbols;
    map<string,bdd>* tmp_map;
    tmp_symbols = get_lst_str_loc();
    tmp_map = get_map_str_bdd_loc();
    
    for(int i=0; i<NUM_CARS; i++){
        string symbol = "C"+std::to_string(i+1)+"_loc_" + std::to_string(ss->get_state_num()[i]);      
        //org_model_->get_dict()->bdd_map[org_model_->succ_iter(aut_succ_->dst())->cond().id()].f
        for(std::list<string>::iterator it = tmp_symbols[i].begin(); it != tmp_symbols[i].end(); it++ ){
                cout << "@@@@@@ @@@@@@ " << *it <<  "  bdd: " << tmp_map[i][*it] << endl;
            if((*it)==symbol){
                res &= tmp_map[i][*it];
            }
            else{
                //cout << "@@@@@@   @@@@@@ " << *it << (tmp_map[*it]) << endl;
                res &= !(tmp_map[i][*it]);
            }
        }
    }
    
    cout << "@@@@@@ @@@@@@ " << res << endl;
    //bdd res = bdd_ithvar(org_model_->register_ap(symbol));
    //lst_state_bdd.push_back(res);
    
    //bool xodd = (int)ss->get_x() & 1;
    //bool yodd = (int)ss->get_y() & 1;
    //bool goal = (int)ss->get_x()== X_TARGET && (int)ss->get_y()== Y_TARGET;
    bool goal = true;
    return res & (goal ? goal_ : !goal_) & (ss->is_certain() ? certainty_ : !certainty_);
    //return (xodd ? odd_x_ : !odd_x_) & (yodd ? odd_y_ : !odd_y_) & (goal ? goal_ : !goal_) & 
    //        (ss->is_certain() ? certainty_ : !certainty_);
  }

  std::string format_state(const spot::state* s) const override
  {
    auto ss = static_cast<const marine_robot_state*>(s);
    std::ostringstream out;
    string str_state = "<";
    for(int i=0; i<NUM_CARS; i++){
        str_state += std::to_string(ss->get_state_num()[i]);
        if((i+1)<NUM_CARS)
            str_state += ",";
    }
    str_state += ">";
    //out << "(x = " << ss->get_x() << ", y = " << ss->get_y() << ", t = " << ss->get_time() <<')';
    out << "(state_num = " << str_state << ", is_certain = " << ss->is_certain() << ", t = " << ss->get_time() <<')';
    return out.str();
  }
  
//  bdd register_new_bdd_symbol(unsigned state_num, string symbol) const 
//  {
//      symbol += "_" + std::to_string(state_num);      
//      bdd res = bdd_ithvar(register_ap(symbol));
//      //lst_state_bdd.push_back(res);
//      return res;
//  }
  
};

void model_4(string formula){
    cout<< ">>> in model_4\n";
   //just for test purposes
   //auto kk = std::make_shared<marine_robot_kripke>(spot::make_bdd_dict());
   //spot::print_dot(std::cout, kk);
   //if(true)return;
   //****************//
   CERTAINTY_THREASHOLD = 0.99;
   //float x = 0, float y = 0, float time = 0, bool is_certain = true
   unsigned init_state[NUM_CARS];
   //"q=[1,1]" "q=[0.5,1]" "q=[0,0]"
   init_state[0] = 5;
   init_state[1] = 6;
   string str_loc[NUM_CARS][2] {{"C1_loc_1","C1_loc_9"}, {"C2_loc_4","C2_loc_12"}};
   list<string> lst_loc[NUM_CARS];
   lst_loc[0].push_back(str_loc[0][0]);
   lst_loc[0].push_back(str_loc[0][1]);
   lst_loc[1].push_back(str_loc[1][0]);
   lst_loc[1].push_back(str_loc[1][1]);
   //****************//
   //string str_threshold = std::to_string(CERTAINTY_THREASHOLD);
   stringstream stream;
   stream << fixed << setprecision(2) << CERTAINTY_THREASHOLD;
   string str_threshold = stream.str();
   string str_certainty_ap = "q > " + str_threshold;
   //formula = "F(C1_loc_9) & FG(goal) & G \"" + str_certainty_ap + "\"";
   formula = "F(C1_loc_1) & F(C1_loc_9) & ((!C1_loc_1) U C1_loc_9)";
   formula += " & F(C2_loc_4) & F(C2_loc_12) & ((!C2_loc_12) U C2_loc_4)";
   //formula = "FG(goal) & G \"" + str_certainty_ap + "\"";
   cout << ">>> Formula: " << formula << endl;    
   // Convert demo_kripke into an explicit graph
   /*
    std:ifstream inFile;
    string ocean_model_filename = "marine_ocean_model.dot";
    inFile.open(ocean_model_filename);
    if(!inFile.is_open()){
        std::cout << "Generating the ocean model file.\n";
        //generate a mock model and write it to a file for repetitive use
        spot::twa_graph_ptr kg = spot::copy(std::make_shared<marine_robot_kripke>
                (shared_dict,str_certainty_ap, aut_model, init_state, lst_loc),spot::twa::prop_set::all(), true);    
        Util::write2File(ocean_model_filename, kg, "k");
    }
    else
        inFile.close();   
    */
   //if(true) return;
   //auto d = spot::make_bdd_dict();
   //formula = "FG(goal) & (!(odd_x & odd_y) U goal)";
   spot::parsed_formula pf = spot::parse_infix_psl(formula);//"FG(goal) & G \"c > 0.2\" "
   //spot::parsed_formula pf = spot::parse_infix_psl("FG(goal) & (!(odd_x & odd_y) U goal)");
   if (pf.format_errors(std::cerr)){
       cout << "the formula has error!\n";
     return ;
   }

   // Translate its negation.
   //spot::formula f = spot::formula::Not(pf.f);
   spot::formula f = pf.f;
   spot::twa_graph_ptr af = spot::translator(shared_dict).run(f);
   

      // Find a run of or marine_robot_kripke that intersects af.
   auto k = std::make_shared<marine_robot_kripke>(shared_dict, str_certainty_ap, aut_model, init_state, lst_loc);
   

   if (auto run = k->intersecting_run(af))
     std::cout << "found a plan by the following run:\n" << *run;
   else
     std::cout << "no plan found.\n";
   
   mvspot::mvtwaproduct mvtp;
   mvtp.test_me_again();
}