/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   secondary.h
 * Author: mhekmatnejad
 *
 * Created on August 9, 2017, 7:07 PM
 */

#ifndef SECONDARY_H
#define SECONDARY_H

#include "MvLtlModel.h"
#include "mvtwaproduct.h"

using namespace spot;
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


#endif /* SECONDARY_H */

