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

//#include <spot/twa/formula2bdd.hh>
#include <spot/mv/version.hh>
//#include <spot/tl/dot.hh>
//#include <spot/taalgos/dot.hh>

using namespace std;

#define PRINT_DEBUG_DATA 1
#define NUM_POSITIONS 8
#define X_END 3
#define Y_END 3
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
void dfs(spot::const_twa_graph_ptr aut, bdd query);
void test();
void dfs(spot::const_twa_graph_ptr aut, bdd query);
int get_random(int low, int high);
static spot::parsed_aut_ptr read_model_aut;
/**************************************************************************
 
   allsat handler for checking that all assignmenlsatBDD;
 */
 static bdd allsatSumBDD;
 static bdd allsatBDD;
 
 void allsatHandler(char* varset, int size)
 
 {
 
   bdd x = bddtrue;
 
   for (int v=0 ; v<size ; ++v)
   {
     cout << +varset[v] << " ";
 
     if (varset[v] == 0)
 
       x &= bdd_nithvar(v);
 
 else if (varset[v] == 1)
 
       x &= bdd_ithvar(v);
   }

   cout<<endl;
   // Sum up all assignments
 
   allsatSumBDD |= x;
   
   cout << "size: " << size << " allsatSumBDD: " << allsatSumBDD <<endl;
 
   // Remove assignment from initial set
 
   allsatBDD -= x;
   cout << "allsatBDD: " << allsatBDD <<endl;
 
 }
 
 void findSat(bdd eq){

    const int N = 3;
    bdd_init(N*2, N*20);
    bdd_setvarnum(N-1);
      
    bdd a = bdd_ithvar(0);// = bddtrue;
    bdd b = bdd_ithvar(1);// = bddtrue;
    bdd f = bddtrue;// = bdd_ithvar(3);// = bddtrue;

    f &= a | b;
    
    //f &= a >> !b;
    //f &= b >> a;

    
    //bdd solution = bdd_satone(f);
    //cout << bddset << solution << endl;

    bdd_allsat(f, allsatHandler);
    bdd solution = bdd_fullsatone(allsatSumBDD);

   
    cout << "There are " << bdd_satcount(allsatSumBDD) << " solutions\n";
    cout << "one is:\n";
    cout << bddset << solution << endl;
    
    bdd_done();
            
 }

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
    //model_generator::generate_model("ocean_model.dot");
    srand (time(NULL));
    read_model_aut = Util::readAutFromFile("ocean_model.dot");
    if(!read_model_aut)
    {
        cout << "could not read the model from file!";
        exit(0);
    }
    spot::kripke_graph_ptr kg = read_model_aut->ks;
    cout << (read_model_aut->errors.size());
    //auto aut = spot::copy(read_model_aut->ks->shared_from_this(), { true, false, false, false }, true);

    //dfs(aut,bddtrue);
    if(true)return 0;
    //findSat(bddtrue);

    //model_1("F(w)");
    //mv_latice_test_1();
    //model_2("G (w & z)");
    //model_3("G F(fire)");
    //model_3("F G(!fire)");
    model_4("GF(odd_x) -> GF(odd_y)");
    
    cout << "done!\n";
    return 0;
}

void model_1(string formula){

  spot::bdd_dict_ptr dict = spot::make_bdd_dict();

  // Parse the input formula.
  spot::parsed_formula pf = spot::parse_infix_psl(formula);
  if (pf.format_errors(std::cerr)){
      cout << "Input LTL formula is wrong!" << endl;
    return;
  }

  kripke_graph_ptr kg = spot::make_kripke_graph(dict);
  bdd w = bdd_ithvar(kg->register_ap("w"));
  bdd wm = bdd_ithvar(kg->register_ap("wm"));
  
  //kg->new_states(4, w|wm);
  kg->new_state(w);
  kg->new_state(w);
  kg->new_state(w);
  kg->new_state(wm);
  cout << kg->num_states() << std::endl;
  kg->new_edge(0,1);
  kg->new_edge(0,2);
  kg->new_edge(1,3);
  kg->new_edge(2,3);
  kg->new_edge(3,3);
  kg->state_from_number(0)->cond(!w);
  kg->state_from_number(1)->cond(!w);
  kg->state_from_number(2)->cond(!w);
  kg->state_from_number(3)->cond(wm);
  
  Util::write2File("model.dot", kg, "k");

  spot::print_dot(std::cout, kg, "k");

  // Translate its negation.
  //spot::formula f = spot::formula::Not(pf.f);
  spot::twa_graph_ptr af = spot::translator(dict).run(pf.f);
  spot::print_dot(std::cout, af);
  Util::write2File("formula.dot", af);

  // Construct an "on-the-fly product"
  //auto k = spot::copy(kg->shared_from_this(), spot::twa::prop_set::sta, true);
  auto k = spot::copy(kg->shared_from_this(), { true, false, false, false }, true);
  //auto p = mvspot::otf_product(k, af);
  auto p = spot::otf_product(k, af);
  //auto p = std::make_shared<twa_product>(k, af);
  
  //p->register_ap("!wm");
  //p->unregister_ap(wm.id());
  //formula fw;
  //auto fw = bdd_to_formula(!wm,p->get_dict());
  //p->get_dict()->register_proposition(fw,p);
  cout << "new product \n";
  spot::parsed_formula pfq = spot::parse_infix_psl("G(wm)");
  spot::twa_graph_ptr afq = spot::translator(dict).run(pfq.f);
  //p = mvspot::otf_product(p, afq);
  p = spot::otf_product(p, afq);
  
#if 0  
  spot::twa::prop_set ps_ = spot::twa::prop_set::all();
  spot::twa_graph_ptr aut = make_twa_graph(p, ps_);
  Util::write2File("product_graph.dot", aut, "a");
#endif  
  //dfs(aut, !wm);  

  //Util::write2File("product.dot", p, "a");
  
  return ;
  
  
  if (auto run = p->accepting_run())
    {
      run->project(k)->highlight(5); // 5 is a color number.
      spot::print_dot(std::cout, k);//, ".k");
      Util::write2File("accept.dot", k);
      cout << "hooora :) " << endl;
    }
  else{
      cout << "nooooooo :(((( " << endl;
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

void mv_latice_test_1(){

    mvspot::mv_lattice myLattice = mvspot::mv_lattice();
    mvspot::lattice_node nodes[5];
    nodes[0].setName("a");
    nodes[1].setName("b");
    nodes[2].setName("c");
    nodes[3].setName("d");
    nodes[4].setName("e");
    nodes[0].setValue(0.75);
    nodes[1].setValue(0.75);
    nodes[2].setValue(0.5);
    nodes[3].setValue(0.5);
    nodes[4].setValue(0.5);
    myLattice.getTop_()->add_above_of(&nodes[0]);
    myLattice.getTop_()->add_above_of(&nodes[1]);
    nodes[0].add_above_of(&nodes[2]);
    nodes[0].add_above_of(&nodes[3]);
    nodes[1].add_above_of(&nodes[3]);
    nodes[1].add_above_of(&nodes[4]);
    myLattice.getButtom_()->add_bellow_of(&nodes[2]);
    myLattice.getButtom_()->add_bellow_of(&nodes[3]);
    myLattice.getButtom_()->add_bellow_of(&nodes[4]);
    //cout << *myLattice.getTop_() << endl;
    //cout << *myLattice.getButtom_() << endl;


    for (int i=4; i>=0; i--){
            pair<set<mvspot::lattice_node*>::iterator,bool> res = myLattice.getNodes_()->insert(&nodes[i]);
            //pair<set<mvspot::lattice_node>::iterator,bool> res = myset.insert(nodes[i]);
            //cout << res.second <<" " << (mvspot::lattice_node)*res.first << endl;

    }

    //myLattice.getNodes_()->insert(*myLattice.getTop_());
    //myLattice.getNodes_()->insert(*myLattice.getButtom_());

    
    cout << "size: " << myLattice.getNodes_()->size() << endl;

    for(set<mvspot::lattice_node*>::iterator it 
            = myLattice.getNodes_()->begin(); it != myLattice.getNodes_()->end(); it++){
        cout << *(mvspot::lattice_node*)(*it) << endl;
    }
    
    cout << myLattice << endl;   
    return ;
    
    set<mvspot::lattice_node*> *ss = nodes[0].getBelow_nodes();
    for(set<mvspot::lattice_node*>::iterator itt 
            = ss->begin(); itt != ss->end(); itt++){
        cout << *(mvspot::lattice_node*)(*itt) << " *" << endl;
    }    
}

void model_2(string formula){

  spot::bdd_dict_ptr dict = spot::make_bdd_dict();

  // Parse the input formula.
  spot::parsed_formula pf = spot::parse_infix_psl(formula);
  if (pf.format_errors(std::cerr)){
      cout << "Input LTL formula is wrong!" << endl;
    return;
  }
  cout << "trying...\n";
  spot::twa_graph_ptr af = spot::translator(dict).run(pf.f);
    //cout << "hello\n";

  //kripke_graph_ptr kg = spot::make_kripke_graph(dict);
  mv_kripke_graph_ptr kg = spot::make_mv_kripke_graph(dict);//uses new kripke structure
  //auto kk = std::make_shared<demo_kripke>(dict);
  
   //spot::twa::prop_set ps_ = {true,false,false,false};//spot::twa::prop_set::all();
   spot::twa::prop_set ps_ = spot::twa::prop_set::all();
   //kripke_graph_ptr kg = make_kripke_graph(kk, ps_);

  bdd w = bdd_ithvar(kg->register_ap("w"));
  bdd wm = bdd_ithvar(kg->register_ap("wm"));
  bdd z = bdd_ithvar(kg->register_ap("z"));
  
  //kg->new_states(4, w|wm);
  kg->new_state(w);
  kg->new_state(w);
  kg->new_state(w);
  kg->new_state(wm);
 
  cout << kg->num_states() << std::endl;
  kg->new_edge(0,1);
  kg->new_edge(0,2);
  kg->new_edge(1,3);
  kg->new_edge(2,3);
  kg->new_edge(3,3);
  kg->state_from_number(0)->cond(!w);
  kg->state_from_number(1)->cond(w);
  kg->state_from_number(2)->cond(!w);
  kg->state_from_number(3)->cond(wm & z);

#if 0 
  stringstream os;
  spot::print_dot(os, kg, "k");
  stringstream ss = Util::readFromFile("model.dot");
  if(os.str()==ss.str())
      cout << "YYYYYYYYYYYYYYYYESSSSS\n" << os.str() << "\n" << ss.str();
  return ;
#endif  
  Util::write2File("model.dot", kg, "k");
#if PRINT_DEBUG_DATA
  cout << "========================\n";
#endif
  //spot::print_dot(std::cout, kg, "k");
  
  
  // Translate its negation.
  //spot::formula f = spot::formula::Not(pf.f);

  //spot::print_dot(std::cout, af);
  Util::write2File("formula.dot", af);

  // Construct an "on-the-fly product"
  auto k = spot::copy(kg->shared_from_this(), { true, false, false, false }, true);
  //auto p = mvspot::otf_product_at(kg, af, kg->get_init_state(),af->get_init_state());
  //auto p = mvspot::otf_product(k, af);
  auto p = spot::otf_product(k, af);
  //auto p = std::make_shared<twa_product>(k, af);
  //p->register_ap("!wm");
  //p->unregister_ap(wm.id());
  //formula fw;
  //auto fw = bdd_to_formula(!wm,p->get_dict());
  //p->get_dict()->register_proposition(fw,p);
#if 0
  cout << "new product \n";
  spot::parsed_formula pfq = spot::parse_infix_psl("G(wm)");
  spot::twa_graph_ptr afq = spot::translator(dict).run(pfq.f);
  p = mvspot::otf_product(p, afq);
#endif  
    //auto k = spot::copy(p->shared_from_this(), { true, false, false, false }, true);

  //spot::twa::prop_set ps_ = spot::twa::prop_set::all();
    //spot::twa::prop_set ps_ = { true, false, false, false };

 // spot::twa_graph_ptr aut = make_twa_graph(p, ps_);
 // Util::write2File("product_graph.dot", aut, "a");
  //dfs(aut, !wm);  

  Util::write2File("product.dot", p, "a");

//  if (auto run = p->accepting_run())
  if (auto run = k->intersecting_run(af,false))
//  if (auto run = k->intersects(af))
    {
      //run->project(k)->highlight(5); // 5 is a color number.
      ////spot::print_dot(std::cout, k);//, ".k");
      //Util::write2File("accept.dot", k);
      cout << "hooora :) " << endl;
    }
  else{
      cout << "nooooooo :(((( " << endl;
  }
  
    
}

void model_3(string formula){

  spot::bdd_dict_ptr dict = spot::make_bdd_dict();

  // Parse the input formula.
  spot::parsed_formula pf = spot::parse_infix_psl(formula);
  if (pf.format_errors(std::cerr)){
      cout << "Input LTL formula is wrong!" << endl;
    return;
  }
  cout << "trying...\n";
  spot::twa_graph_ptr af = spot::translator(dict).run(pf.f);
    //cout << "hello\n";

  //kripke_graph_ptr kg = spot::make_kripke_graph(dict);
  mv_kripke_graph_ptr kg = spot::make_mv_kripke_graph(dict);//uses new kripke structure
  //auto kk = std::make_shared<demo_kripke>(dict);
  
   //spot::twa::prop_set ps_ = {true,false,false,false};//spot::twa::prop_set::all();
   spot::twa::prop_set ps_ = spot::twa::prop_set::all();
   //kripke_graph_ptr kg = make_kripke_graph(kk, ps_);

  bdd f = bdd_ithvar(kg->register_ap("fire"));
  
  //kg->new_states(4, w|wm);
  kg->new_state(f);
  kg->new_state(f);
  kg->new_state(f);
  kg->new_state(f);
 
  cout << kg->num_states() << std::endl;
  kg->new_edge(0,1);
  kg->new_edge(1,0);
  kg->new_edge(0,2);
  kg->new_edge(2,0);
  kg->new_edge(1,3);
  kg->new_edge(3,1);
  kg->new_edge(2,3);
  kg->new_edge(3,2);
  //kg->new_edge(3,3);
  kg->state_from_number(0)->cond(!f);
  kg->state_from_number(1)->cond(f);
  kg->state_from_number(2)->cond(!f);
  kg->state_from_number(3)->cond(f);

#if 0 
  stringstream os;
  spot::print_dot(os, kg, "k");
  stringstream ss = Util::readFromFile("model.dot");
  if(os.str()==ss.str())
      cout << "YYYYYYYYYYYYYYYYESSSSS\n" << os.str() << "\n" << ss.str();
  return ;
#endif  
  Util::write2File("model.dot", kg, "k");
#if PRINT_DEBUG_DATA
  cout << "========================\n";
#endif

  Util::write2File("formula.dot", af);

  // Construct an "on-the-fly product"
  auto k = spot::copy(kg->shared_from_this(), { true, false, false, false }, true);

  auto p = spot::otf_product(k, af);

  Util::write2File("product.dot", p, "a");

//  if (auto run = p->accepting_run())
  if (auto run = k->intersecting_run(af,false))
//  if (auto run = k->intersects(af))
    {
      run->project(k)->highlight(5); // 5 is a color number.
      ////spot::print_dot(std::cout, k);//, ".k");
      Util::write2File("accept.dot", k);
      cout << "hooora :) " << endl;
    }
  else{
      cout << "nooooooo :(((( " << endl;
  }
  
    
}

void test()
{
#if 0
    spot::default_environment& env = spot::default_environment::instance();
    spot::formula f;
    auto pf = spot::parse_infix_psl("F \"a > 2\" ", env, false);
    bool exit_code = pf.format_errors(std::cerr);
    f = pf.f;
    //spot::print_dot_psl(std::cout, f);
    auto dict = spot::make_bdd_dict();
    spot::translator trans(dict);
    trans.set_pref(spot::postprocessor::Deterministic);
    spot::const_twa_ptr prop = nullptr;
    prop = trans.run(&f);
    spot::print_dot(std::cout, prop);
    
    //spot::atomic_prop_set ap;
    //atomic_prop_collect(f, &ap);
    char** argv; 
    argv = new char*[3];
    argv[0] = "-gK";
    argv[1] = "finite.dve";
    argv[2] = "F(\"P.a > 5\")";
    //model_check::checked_main(3, argv);
    delete argv;
#endif    
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

  bool is_restricted(float x, float y)
  {
      if(x < 0 || x>X_END || y<0 || y>Y_END)
          return true;
      return false;
  }
  
  int get_random(int low, int high)
  {
    return (int)(low + (float)rand()/RAND_MAX*(high-low));
  }
  
  bool check_if_valid(float x_, float y_, int pos_)
  {
      float new_x = 0;
      float new_y = 0;
      switch(pos_){
          case 4://move up
              new_x = x_;
              new_y = y_+1;
              break;
          case 3://move right
              new_x = x_+1;
              new_y = y_;
              break;
          case 2://move down
              new_x = x_;
              new_y = y_-1;
              break;
          case 1://move left
              new_x = x_-1;
              new_y = y_;
              break;
        }
      if (is_restricted(new_x, new_y))
            return false;
      return true;
      
  }
  
  static int positions[NUM_POSITIONS][2];
  //determines which move must be taken at each step based on a desired strategy
  bool next_move(float& x, float& y, int pos)
  {
      return false;
  }
  
class marine_robot_succ_iterator: public spot::kripke_succ_iterator
{
private:
  float x_;
  float y_;
  float time_;
  unsigned char pos_;
public:
  marine_robot_succ_iterator(float x, float y, float time, bdd cond)
    : kripke_succ_iterator(cond), x_(x), y_(y), time_(time)
  {
  }

  bool first() override
  {
    if(x_==X_TARGET && y_==Y_TARGET){
        pos_=0;
        return true;
    }
    if(time_==(MAX_RUN_TIME-1))
        return false;
    pos_ = 4;
    bool res = false;
    while(pos_>0){
        res = check_if_valid(x_, y_, pos_);   // There exists a successor.
        if(res)
            break;
        pos_--;
    }
    if(pos_<=0)
        return false;
    return true;
  }

  bool next() override
  {
    //if(time_==(MAX_RUN_TIME-1))
    //    return false;
    
      --pos_;
    if(x_==X_TARGET && y_==Y_TARGET){
        pos_=0;
        return false;
    }

    bool res = false;
    while(pos_>0){
        res = check_if_valid(x_, y_, pos_);   // There exists a successor.
        if(res)
            break;
        pos_--;
    }
    return (pos_ > 0);          // More successors?
  }

  bool done() const override
  {
    return pos_ == 0 || time_==(MAX_RUN_TIME-1);
  }

  marine_robot_state* dst() const override
  {
      float arrival_time = 0;
      float new_x = 0;
      float new_y = 0;
      switch(pos_){
          case 4://move up
              new_x = x_;
              new_y = y_+1;
              break;
          case 3://move right
              new_x = x_+1;
              new_y = y_;
              break;
          case 2://move down
              new_x = x_;
              new_y = y_-1;
              break;
          case 1://move left
              new_x = x_-1;
              new_y = y_;
              break;
        }

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
   //auto kk = std::make_shared<marine_robot_kripke>(spot::make_bdd_dict());
   //spot::print_dot(std::cout, kk);
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