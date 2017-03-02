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

#include <spot/twa/formula2bdd.hh>
#include <spot/mv/version.hh>
#include <spot/tl/dot.hh>
#include <spot/taalgos/dot.hh>

using namespace std;

void model_1(string formula);
void model_2(string formula);
void model_3(string formula);
void mv_latice_test_1();
void dfs(spot::const_twa_graph_ptr aut, bdd query);
void test();

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

    
    //findSat(bddtrue);

    //model_1("F(w)");
    //mv_latice_test_1();
    model_2("F(w & z)");
            
    
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


/*
 * ***********************************************************************
 */

class demo_state: public spot::kripke_graph_state
{
private:
  float x_;
  float y_;
  //bdd cond_;
public:
  demo_state(float x = 0, float y = 0)
    : x_(x), y_(y)
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
  
  bdd get_cond_() const
  {
      return cond();
  }

  demo_state* clone() const override
  {
    return new demo_state(x_, y_);
  }

  size_t hash() const override
  {
    return (x_ * 31) + 13*y_;// + z_;
  }

  int compare(const spot::state* other) const override
  {
    auto o = static_cast<const demo_state*>(other);
      if(get_x()== o->get_x() && 
              get_y()==o->get_y())// && get_z()==o->get_z())
          return 0;
      else 
          return -1;
    size_t oh = o->hash();
    size_t h = hash();
    if (h < oh)
      return -1;
    else
      return h > oh;
  }
};

class demo_succ_iterator: public spot::kripke_succ_iterator
{
private:
  float x_;
  float y_;
  int pos_;
public:
  demo_succ_iterator(float x, float y, bdd cond)
    : kripke_succ_iterator(cond), x_(x), y_(y)
  {
  }

  bool first() override 
  {
    pos_ = 0;//MOVE_NUM;
    return true;              // There exists a successor.
  }

  bool next() override
  {
    --pos_;
    return pos_ > 0;          // More successors?
  }

  bool done() const override
  {
    return pos_ == 0;
  }

  demo_state* dst() const override
  {
    float x = x_,y = y_;
    //move_robot(x, y, pos_);
    return new demo_state(x, y);

  }

  void recycle(float x, float y, bdd cond)
  {
    x_ = x;
    y_ = y;
    spot::kripke_succ_iterator::recycle(cond);
  }
  
  bdd cond() const override{
      return cond_;
  }

};


class demo_kripke: public spot::kripke
{
private:
  bdd left_, right_, up_, down_; 
public:

  demo_kripke(const spot::bdd_dict_ptr& d)
    : spot::kripke(d)
  {
    left_ = bdd_ithvar(register_ap("l"));
    right_ = bdd_ithvar(register_ap("r"));
    up_ = bdd_ithvar(register_ap("u"));
    down_ = bdd_ithvar(register_ap("d"));
  }

  demo_state* get_init_state() const override
  {
    return new demo_state();
  }

  // To be defined later.
  demo_succ_iterator* succ_iter(const spot::state* s) const override
  {
  auto ss = static_cast<const demo_state*>(s);
  float x = ss->get_x();
  float y = ss->get_y();
  bdd cond = state_condition(ss);
  
  if (iter_cache_)
    {
      auto it = static_cast<demo_succ_iterator*>(iter_cache_);
      iter_cache_ = nullptr;    // empty the cache
      it->recycle(x, y, cond);
      return it;
    }
  
  return new demo_succ_iterator(x, y, cond);
  }


  bdd state_condition(const spot::state* s) const override
  {
    auto ss = static_cast<const demo_state*>(s);
    return ss->get_cond_();
  }

  std::string format_state(const spot::state* s) const override
  {
    auto ss = static_cast<const demo_state*>(s);
    std::ostringstream out;
    out << "(x = " << ss->get_x() << ", y = " << ss->get_y() << ')';// << ", z = " << ss->get_z() << ')';
    return out.str();
  }

};

void model_2(string formula){

  spot::bdd_dict_ptr dict = spot::make_bdd_dict();

  // Parse the input formula.
  spot::parsed_formula pf = spot::parse_infix_psl(formula);
  if (pf.format_errors(std::cerr)){
      cout << "Input LTL formula is wrong!" << endl;
    return;
  }

  //kripke_graph_ptr kg = spot::make_kripke_graph(dict);
  mv_kripke_graph_ptr kg = spot::make_mv_kripke_graph(dict);
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

  
  stringstream os;
  spot::print_dot(os, kg, "k");
  stringstream ss = Util::readFromFile("model.dot");
  if(os.str()==ss.str())
      cout << "YYYYYYYYYYYYYYYY\n" << os.str() << "\n" << ss.str();
  //char * is = Util::readFromFile("model.dot");
  //delete [] is;
  return ;
  
  Util::write2File("model.dot", kg, "k");
  cout << "========================\n";
  //spot::print_dot(std::cout, kg, "k");
  
  
  // Translate its negation.
  //spot::formula f = spot::formula::Not(pf.f);
  spot::twa_graph_ptr af = spot::translator(dict).run(pf.f);
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

  if (auto run = p->accepting_run())
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


void test()
{
#if 0
    spot::default_environment& env = spot::default_environment::instance();
    spot::formula f;
    auto pf = spot::parse_infix_psl("F \"a > 2\" ", env, false);
    bool exit_code = pf.format_errors(std::cerr);
    f = pf.f;
    spot::print_dot_psl(std::cout, f);
    
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