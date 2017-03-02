/* 
 * File:   TestSuite
 * Author: mamad
 *
 * Created on Mar 1, 2017, 4:19:36 PM
 */

#include <CppUTest/TestHarness.h>
#include <cstdlib>
#include <iostream>
//#include "MvLtlModel.h"

//#include "Util.h"



using namespace std;
//using namespace spot;

TEST_GROUP(TestSuite) {

    void setup() {
        // Setup ...
    }

    void teardown() {
        // Teardown ...
    }

};

TEST(TestSuite, testExample) {
    FAIL("Nothing to test yet ...");
}

#if 0
TEST(TestSuite, mvKripkeGraph){

  string formula = "F(w & z)";

  spot::bdd_dict_ptr dict = spot::make_bdd_dict();

  // Parse the input formula.
  spot::parsed_formula pf = spot::parse_infix_psl(formula);
  if (pf.format_errors(std::cerr)){
      cout << "Input LTL formula is wrong!" << endl;
    return;
  }

  mv_kripke_graph_ptr kg = spot::make_mv_kripke_graph(dict);
  
   //spot::twa::prop_set ps_ = {true,false,false,false};//spot::twa::prop_set::all();
   spot::twa::prop_set ps_ = spot::twa::prop_set::all();

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
  cout << "========================\n";
#endif   
  // Translate its negation.
  spot::twa_graph_ptr af = spot::translator(dict).run(pf.f);
  //spot::print_dot(std::cout, af);
  Util::write2File("formula.dot", af);

  // Construct an "on-the-fly product"
  auto k = spot::copy(kg->shared_from_this(), { true, false, false, false }, true);
  auto p = spot::otf_product(k, af);
  Util::write2File("product.dot", p, "a");

  if (auto run = p->accepting_run())
    {
      //run->project(k)->highlight(5); // 5 is a color number.
      ////spot::print_dot(std::cout, k);//, ".k");
      //Util::write2File("accept.dot", k);
      cout << "hooora :) " << endl;
    }
  else{
      FAIL("something went wrong!");
      cout << "nooooooo :(((( " << endl;
  }
  
    


}
#endif