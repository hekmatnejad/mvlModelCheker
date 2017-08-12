/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ModelGenerator.h
 * Author: mhekmatnejad
 *
 * Created on August 7, 2017, 5:24 PM
 */

#ifndef MODELGENERATOR_H
#define MODELGENERATOR_H
namespace model_generator {
    
using namespace std;

#include <iostream>
#include <spot/kripke/kripke.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twa/twaproduct.hh>
#include <spot/twaalgos/emptiness.hh>

#include "Util.h"

#define PRINT_DEBUG_DATA 1
#define NUM_POSITIONS 8
#define X_START 0
#define Y_START 0
int X_END = 3;
int Y_END = 3;
int X_TARGET = 3;
int Y_TARGET = 3;

int get_random(int low, int high);

class model_state: public spot::state
{
private:
  float x_;
  float y_;    
  float z_ = 0;
public:
  model_state(float x = 0, float y = 0, float z = 0)
    : x_((int)x % (X_END+1)), y_((int)y % (Y_END+1)), z_(z)
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
  
  float get_z() const
  {
    return z_;
  }

  model_state* clone() const override
  {
    return new model_state(x_, y_, z_);
  }

  size_t hash() const override
  {
    return (x_ * 31) + 13*y_ + z_*7111;
  }

  int compare(const spot::state* other) const override
  {
    auto o = static_cast<const model_state*>(other);
    size_t oh = o->hash();
    size_t h = hash();
    if (h < oh)
      return -1;
    else
      return h > oh;
  }
  
  string toString(){
    std::ostringstream out;
    out << "(x = " << this->get_x() << ", y = " << this->get_y() << ", z = " << this->get_z() <<')';
    return out.str();
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
          case 8://move up
              new_x = x_;
              new_y = y_+1;
              break;
          case 7://move up,right
              new_x = x_+1;
              new_y = y_+1;
              break;
          case 6://move right
              new_x = x_+1;
              new_y = y_;
              break;
          case 5://move right,down
              new_x = x_+1;
              new_y = y_-1;
              break;
          case 4://move down
              new_x = x_;
              new_y = y_-1;
              break;
          case 3://move down,left
              new_x = x_-1;
              new_y = y_-1;
              break;
          case 2://move left
              new_x = x_-1;
              new_y = y_;
              break;
          case 1://move left,up
              new_x = x_-1;
              new_y = y_+1;
              break;
        }
      if (is_restricted(new_x, new_y))
            return false;
      return true;
      
  }
  
class model_succ_iterator: public spot::kripke_succ_iterator
{
private:
  float x_;
  float y_;
  float z_;
  unsigned char pos_;
public:
  model_succ_iterator(float x, float y, float z, bdd cond)
    : kripke_succ_iterator(cond), x_(x), y_(y), z_(z)
  {
  }

  bool first() override
  {
    if(x_==X_TARGET && y_==Y_TARGET){
        pos_=0;
        return true;
    }

    pos_ = NUM_POSITIONS;
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
    return pos_ == 0;
  }

  model_state* dst() const override
  {
      float new_x = 0;
      float new_y = 0;
      switch(pos_){
          case 8://move up
              new_x = x_;
              new_y = y_+1;
              break;
          case 7://move up,right
              new_x = x_+1;
              new_y = y_+1;
              break;
          case 6://move right
              new_x = x_+1;
              new_y = y_;
              break;
          case 5://move right,down
              new_x = x_+1;
              new_y = y_-1;
              break;
          case 4://move down
              new_x = x_;
              new_y = y_-1;
              break;
          case 3://move down,left
              new_x = x_-1;
              new_y = y_-1;
              break;
          case 2://move left
              new_x = x_-1;
              new_y = y_;
              break;
          case 1://move left,up
              new_x = x_-1;
              new_y = y_+1;
              break;
        }

      if(x_==X_TARGET && y_==Y_TARGET){
        cout <<"***" <<x_ <<',' << y_ <<"," << z_ << endl;
        return new model_state(x_, y_, z_);
      }
      else{
        cout <<x_<<','<<y_<<"->"<<new_x <<',' << new_y << endl;
      }
      return new model_state(new_x, new_y, z_);
  }

  void recycle(float x, float y, float z, bdd cond)
  {
    x_ = x;
    y_ = y;
    z_ = z;
    spot::kripke_succ_iterator::recycle(cond);
  }
};

class model_kripke: public spot::kripke
{
private:

public:
  model_kripke(const spot::bdd_dict_ptr& d)
    : spot::kripke(d)
  {
  }

  model_state* get_init_state() const override
  {
    return new model_state();
  }

  // To be defined later.
    model_succ_iterator* succ_iter(const spot::state* s) const override
    {
      auto ss = static_cast<const model_state*>(s);
      float x = ss->get_x();
      float y = ss->get_y();
      float z = ss->get_z();
      bdd cond = state_condition(ss);
      if (iter_cache_)
        {
          auto it = static_cast<model_succ_iterator*>(iter_cache_);
          iter_cache_ = nullptr;    // empty the cache
          it->recycle(x, y, z, cond);
          return it;
        }
      return new model_succ_iterator(x, y, z, cond);
    }

  bdd state_condition(const spot::state* s) const override
  {
    auto ss = static_cast<const model_state*>(s);
    return bddtrue;
  }

  std::string format_state(const spot::state* s) const override
  {
    auto ss = static_cast<const model_state*>(s);
    std::ostringstream out;
    out << "(x = " << ss->get_x() << ", y = " << ss->get_y() << ", z = " << ss->get_z() <<')';
    return out.str();
  }
};

void generate_model(string model_name, int x_end, int y_end, int x_target, int y_target, 
                        spot::bdd_dict_ptr dict=spot::make_bdd_dict()){
    X_END = x_end;
    Y_END = y_end;
    X_TARGET = x_target;
    Y_TARGET = y_target;
    srand (time(NULL));
   //just for test purposes
   //auto kk = std::make_shared<model_kripke>(spot::make_bdd_dict());
   //spot::print_dot(std::cout, kk);
   // Convert demo_kripke into an explicit graph
   spot::twa_graph_ptr kg = spot::copy(std::make_shared<model_kripke>
           (dict),spot::twa::prop_set::all(), true);    
   Util::write2FileAsHoa(model_name, kg, "k");
   cout << "model generated as: "<< model_name << endl;
}
}
#endif /* MODELGENERATOR_H */

