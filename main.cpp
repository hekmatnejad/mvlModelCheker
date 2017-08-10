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
#include <mutex>

//#include <spot/twa/formula2bdd.hh>
#include <spot/mv/version.hh>
#include <spot/taalgos/dot.hh>
#include <spot/twaalgos/word.hh>
//#include <spot/tl/dot.hh>
//#include <spot/taalgos/dot.hh>

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
model_node ** sorted_states_connected_to(unsigned state);
int gloabl_size_of_connected_nodes[NUM_LOCATIONS];

 static spot::bdd_dict_ptr shared_dict = spot::make_bdd_dict();
 void testme();
/*
 * 
 */
int main(int argc, char** argv) {
    //test();
    //return 0;
    std::cout << "started...\n";
    cout << mvspot::getVersion() << "\n" <<mvspot::getBuild() <<"\n" ;
    mvspot::mv_ltl_model model = mvspot::mv_ltl_model();
    std::cout << model << std::endl;
    //generate a mock model and write it to a file for repetitive use
    //model_generator::generate_model("ocean_model.dot",shared_dict);
    
    create_all_model_locations();
    get_state_number_from_xy();
    testme();
    if(true)return 0;
    srand (time(NULL));
    read_model_aut = Util::readAutFromFile("ocean_model.dot",false,shared_dict);
    if(!read_model_aut || read_model_aut->errors.size()>0)
    {
        cout << "could not read the model from file!";
        exit(0);
    }
    kg_model = read_model_aut->ks;
    aut_model = read_model_aut->aut;

    //for(int i=0; i<16; i++)
    //{
    //    model_node ** result = sorted_states_connected_to(i);
    //    cout<< "size: " << gloabl_size_of_connected_nodes << endl;
    //}
    
    //spot::print_dot(std::cout, aut_model,"k");
    //if(true)return 0;

    model_4("GF(odd_x) -> GF(odd_y)");
    
    cout << "done!\n";
    return 0;
}
void testme(){
    
}
mutex size_mutex;
//this function sorts the visiting graph nodes based on the given map and 
//distance values toward the target
model_node** sorted_states_connected_to(unsigned src){
    auto& gr = aut_model->get_graph();
    unsigned edge;
    unsigned dst;
    
    edge = gr.state_storage(src).succ;
    std::set<model_node*, node_compare> around_nodes;
    while(edge>0){
        dst = gr.edge_storage(edge).dst;
        float value = ((X_POS[dst]-X_END)*(X_POS[dst]-X_END)+(Y_POS[dst]-Y_END)*(Y_POS[dst]-Y_END));
        model_node* node = new model_node(value,X_POS[dst],Y_POS[dst]);
        around_nodes.insert(node);
        std::cout<< "edge: " << edge << ", src: " << src << ", dst: " << dst << ", distance: " << node->GetValue() <<endl;
        edge = gr.edge_storage(edge).next_succ;
    }
    model_node* result[around_nodes.size()];
    //result = new model_node*[around_nodes.size()]();
    int cnt = 0;
    for(std::set<model_node*>::iterator it = around_nodes.begin(); it!=around_nodes.end(); it++){
        //std:cout <<">>>"<< ((model_node*)(* it))->GetValue() << endl;
        result[cnt++] = ((model_node*)(* it));
    }
    //std::lock_guard<std::mutex> lock(size_mutex);
    //size_mutex.lock();
    gloabl_size_of_connected_nodes[src] = around_nodes.size();
    //size_mutex.unlock();
    //note: do not forget to free memory after being done using this function
    return result;
 }

static int xy2number[Y_END+1][X_END+1];

static model_node ** all_model_locations[NUM_LOCATIONS];
void create_all_model_locations(){
    for(int i=0; i<NUM_LOCATIONS; i++)
        all_model_locations[i] = sorted_states_connected_to(i);
}

void get_state_number_from_xy(){
    for(int i=0; i<= X_END; i++){
        for(int j=0; j<= Y_END; j++){
            for(int m=0; m< NUM_LOCATIONS; m++){
                if((int)X_POS[m]==i && (int)Y_POS[m]==j){
                    xy2number[i][j] = m;
                    //std::cout << i <<" " << j << " " << m << endl;
                    break;
                }
            }
        }
    }
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
  float x_;
  float y_;    
  float time_ = 0;

public:
  marine_robot_state(float x = 0, float y = 0, float time = 0)
    : x_((int)x % (X_END+1)), y_((int)y % (Y_END+1)), time_(time)
  {
  }

  float get_x() const
  {
    return x_;
  }

  float get_y() const
  {
    return y_;
  }
  
  float get_time() const
  {
      return time_;
  }
  
  marine_robot_state* clone() const override
  {
    return new marine_robot_state(x_, y_, time_);
  }

  size_t hash() const override
  {
    return (x_ * 31) + 13*y_ + time_*7111;
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

  int get_random(int low, int high)
  {
    return (int)(low + (float)rand()/RAND_MAX*(high-low));
  }
  
class marine_robot_succ_iterator: public spot::kripke_succ_iterator
{
private:
  float x_;
  float y_;
  float time_;
  unsigned char pos_;
  int num_pos=0;
public:
  marine_robot_succ_iterator(float x, float y, float time, bdd cond)
    : kripke_succ_iterator(cond), x_(x), y_(y), time_(time)
  {
    num_pos = gloabl_size_of_connected_nodes[xy2number[(int)x_][(int)y_]];
    cout<< "size sorted_positions: " << num_pos << endl;
  }

  bool first() override
  {
    if(x_==X_TARGET && y_==Y_TARGET){
        pos_=num_pos;
        return true;
    }
    if(time_==(MAX_RUN_TIME-1))
        return false;
    pos_ = 0;
    return true;
  }

  bool next() override
  {
    //if(time_==(MAX_RUN_TIME-1))
    //    return false;
    
    pos_++;
    if(x_==X_TARGET && y_==Y_TARGET){
        pos_=num_pos;
        return false;
    }
    return (pos_ < num_pos);          // More successors?
  }

  bool done() const override
  {
    return pos_ == num_pos || time_==(MAX_RUN_TIME-1);
  }

  marine_robot_state* dst() const override
  {
      float arrival_time = 0;
      float new_x = 0;
      float new_y = 0;
      new_x = all_model_locations[xy2number[(int)x_][(int)y_]][pos_]->GetX();
      new_y = all_model_locations[xy2number[(int)x_][(int)y_]][pos_]->GetY();

      if(x_==X_TARGET && y_==Y_TARGET){
        cout <<"***" <<x_ <<',' << y_ <<",t: " << time_ << endl;
        return new marine_robot_state(x_, y_, time_);
      }
      else{
        arrival_time = (int)(time_ + 1) % MAX_RUN_TIME;
        cout <<x_<<','<<y_<<"->"<<new_x <<',' << new_y <<",t: " << arrival_time << endl;
      }
      return new marine_robot_state(new_x, new_y, arrival_time);
  }

  void recycle(float x, float y, float time, bdd cond)
  {
    x_ = x;
    y_ = y;
    time_ = time;
    spot::kripke_succ_iterator::recycle(cond);
  }
};

class marine_robot_kripke: public spot::kripke
{
private:
  static const int num_time_periods = 4;
  static const int num_move_directions = 4;    
  bdd odd_x_;
  bdd odd_y_;
  bdd t_[num_time_periods];
  bdd m_[num_move_directions];
public:
  marine_robot_kripke(const spot::bdd_dict_ptr& d)
    : spot::kripke(d)
  {
    odd_x_ = bdd_ithvar(register_ap("odd_x"));
    odd_y_ = bdd_ithvar(register_ap("odd_y"));
    create_all_model_locations();
    get_state_number_from_xy();
   
    //for(int i=0; i<num_time_periods; i++)
    //    t_[i] = bdd_ithvar(register_ap("t_"+to_string(i)));
  }

  marine_robot_state* get_init_state() const override
  {
    return new marine_robot_state();
  }

  // To be defined later.
    marine_robot_succ_iterator* succ_iter(const spot::state* s) const override
    {
      auto ss = static_cast<const marine_robot_state*>(s);
      float x = ss->get_x();
      float y = ss->get_y();
      float time = ss->get_time();
      bdd cond = state_condition(ss);
      if (iter_cache_)
        {
          auto it = static_cast<marine_robot_succ_iterator*>(iter_cache_);
          iter_cache_ = nullptr;    // empty the cache
          it->recycle(x, y, time, cond);
          return it;
        }
      return new marine_robot_succ_iterator(x, y, time, cond);
    }

  bdd state_condition(const spot::state* s) const override
  {
    auto ss = static_cast<const marine_robot_state*>(s);
    bool xodd = (int)ss->get_x() & 1;
    bool yodd = (int)ss->get_y() & 1;
    return (xodd ? odd_x_ : !odd_x_) & (yodd ? odd_y_ : !odd_y_);
  }

  std::string format_state(const spot::state* s) const override
  {
    auto ss = static_cast<const marine_robot_state*>(s);
    std::ostringstream out;
    out << "(x = " << ss->get_x() << ", y = " << ss->get_y() << ", t = " << ss->get_time() <<')';
    return out.str();
  }
};

void model_4(string formula){
   //just for test purposes
   auto kk = std::make_shared<marine_robot_kripke>(spot::make_bdd_dict());
   spot::print_dot(std::cout, kk);
   if(true)return;
   // Convert demo_kripke into an explicit graph
   
   //spot::twa_graph_ptr kg = spot::copy(std::make_shared<marine_robot_kripke>(spot::make_bdd_dict()),
   //                                  spot::twa::prop_set::all(), true);    
   //Util::write2File("marine_ocean_model.dot", kg, "k");
   //if(true) return;
   auto d = spot::make_bdd_dict();
   // Parse the input formula.
   //spot::parsed_formula pf = spot::parse_infix_psl("GF(odd_x) -> GF(odd_y)");
   spot::parsed_formula pf = spot::parse_infix_psl("!FG(odd_x)");
   if (pf.format_errors(std::cerr))
     return ;

   // Translate its negation.
   spot::formula f = spot::formula::Not(pf.f);
   spot::twa_graph_ptr af = spot::translator(d).run(f);

   // Find a run of or marine_robot_kripke that intersects af.
   auto k = std::make_shared<marine_robot_kripke>(d);
   cout<<"step: 2\n";
   if (auto run = k->intersecting_run(af))
     std::cout << "formula is violated by the following run:\n" << *run;
   else
     std::cout << "formula is verified\n";
}