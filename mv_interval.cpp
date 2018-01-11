/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   mv_interval.cpp
 * Author: mhekmatnejad
 * 
 * Created on January 8, 2018, 2:01 AM
 */

#include <spot/twa/taatgba.hh>

#include "mv_interval.h"
namespace mvspot
{
    
mv_interval::mv_interval(string name)
{
    name_ = name;
    map_intervals_ = new std::map<string,mv_interval*>();
    map_all_intervals_ = new std::map<std::pair<float,float>,mv_interval*>();

}
//this constructor is for the main interval as a TO lattice that contains other intervals
mv_interval::mv_interval(string name, lattice_node* intervals, int size) throw() :
name_(name), intervals_(intervals), int_size_(size) 
{
    is_TO_lattice_container_ = true;
    map_intervals_ = new std::map<string,mv_interval*>();
    map_all_intervals_ = new std::map<std::pair<float,float>,mv_interval*>();
    if(intervals==nullptr || size < 2)
        throw(new mv_exception("nodes and size must not be nothing!"));
    to_lattice_ = new mv_lattice(&intervals[0], &intervals[size-1]);
    lattice_node* node = to_lattice_->getTop_();
    for(int i=1; i<size-1; i++){
        if(node->compare(&intervals[i])<=0)
            throw(new mv_exception("Ascending order among interval nodes is not preserved."));
        to_lattice_->getNodes_()->insert(&intervals[i]);
        node->add_above_of(&intervals[i]);
        node = &intervals[i];
    }
    node->add_above_of(&intervals[size-1]);
    top_ = &intervals[0];
    buttom_ = &intervals[size-1];
    (*map_intervals_)[get_as_str()] = this;
}

mv_interval::mv_interval(string name, float low, float high): mv_interval(name) 
{
    //mv_interval();
    buttom_ = new lattice_node("low", low);
    top_ = new lattice_node("high", high);
    top_->add_above_of(buttom_);
    to_lattice_ = new mv_lattice(buttom_, top_);
    (*map_intervals_)[get_as_str()] = this;
}

void mv_interval::add_interval(string symbol, float low, float high){
    if(low > high)
        throw(new mv_exception("low of interval must be less than or equals to the high."));
    //lattice_node* ln = new lattice_node("low", low);
    //lattice_node* rn = new lattice_node("high", high);
    //mv_lattice* interval;
    //ln->add_bellow_of(rn);
    //interval = new mv_lattice(ln, rn);
    mv_interval* interval = new mv_interval(get_as_str(low, high), low, high);
    (*map_intervals_)[interval->get_as_str()] = interval;
    //cout << ">>> " << get_as_str(low, high) << " "<< (*map_intervals_)[interval->get_as_str()]->name_<<endl;
}

//mv_lattice* mv_interval::get_interval(string symbol){
//    if(map_intervals_->find(symbol)==map_intervals_->end())
//        return nullptr;
//    return ((*map_intervals_)[symbol]);
//}

//void mv_interval::add_interval(float low, float high){
//    if(low > high)
//        throw(new mv_exception("low of interval must be less than or equals to the high."));
//    mv_interval* interval;
//    interval = new mv_interval(low, high);
//    (*map_intervals_)[symbol] = interval;
//    (*map_all_intervals_[std::make_pair(low,high)]) = interval;
//}

//mv_interval* mv_interval::get_interval(string symbol){
//    if(map_intervals_->find(symbol)==map_intervals_->end())
//        return nullptr;
//    return ((*map_intervals_)[symbol]);
//}

mv_interval* mv_interval::get_interval(float low, float high){
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end())
        return nullptr;
    return ((*map_all_intervals_)[std::make_pair(low,high)]);
}

lattice_node* mv_interval::getTop(){
    return top_;
}

lattice_node* mv_interval::getButtom(){
    return buttom_;
}

mv_interval::mv_interval(const mv_interval& orig) {
    cout << "???????????\n\n";
    is_TO_lattice_container_ = orig.is_TO_lattice_container_;
    intervals_ = orig.intervals_;
    name_ = orig.name_;
    top_ = orig.top_;
    buttom_ = orig.buttom_;
    int_size_ = orig.int_size_;
    to_lattice_ = orig.to_lattice_;
    map_all_intervals_ = orig.map_all_intervals_;
    map_intervals_ = orig.map_intervals_;
}

mv_interval::~mv_interval() {
    cout << "in ~mv_interval\n";
    if(map_intervals_!=0)
        delete map_intervals_;
    if(map_all_intervals_!=0)
        delete map_all_intervals_;
    //delete intervals_;
    if(to_lattice_!=0)
        delete to_lattice_;
    if(intervals_==0){
        delete top_;
        delete buttom_;
    }
    cout << "mv_interval::~mv_interval() called successfully.\n";
}

string mv_interval::get_as_str(){
    return get_as_str(getButtom()->getValue(), getTop()->getValue());
}

string mv_interval::get_as_str(float low, float high){
    //string res = getName() + "=[";
    string res = "[";
    string num = std::to_string(low);
    while(num.size()>1 && num.at(num.size()-1)=='0')
        num = num.substr(0,num.size()-1);
    if(num.at(num.size()-1)=='.')
        num = num.substr(0,num.size()-1);
    res += num + ",";
    num = std::to_string(high);
    while(num.size()>1 && num.at(num.size()-1)=='0')
        num = num.substr(0,num.size()-1);
    if(num.at(num.size()-1)=='.')
        num = num.substr(0,num.size()-1);
    res += num + "]";
    return res;
}


std::pair<float,float> mv_interval::get_as_pair(){
    std::pair<float,float> res = std::make_pair(getButtom()->getValue(),
            getTop()->getValue());
    return res;
}


//lattice operators

float mv_interval::complement_mv(float given){
    return getTop()->getValue() - given;
}

mv_interval* mv_interval::join_mv(mv_interval* left, mv_interval* right){
    
    float low = left->getButtom()->getValue() > right->getButtom()->getValue()?
                left->getButtom()->getValue() : right->getButtom()->getValue();
    float high = left->getTop()->getValue() > right->getTop()->getValue()?
                left->getTop()->getValue() : right->getTop()->getValue();
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}

mv_interval* mv_interval::meet_mv(mv_interval* left, mv_interval* right){
    float low = left->getButtom()->getValue() < right->getButtom()->getValue()?
                left->getButtom()->getValue() : right->getButtom()->getValue();
    float high = left->getTop()->getValue() < right->getTop()->getValue()?
                left->getTop()->getValue() : right->getTop()->getValue();
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}

//mv_interval* mv_interval::not_mv(mv_interval* given);

mv_interval* mv_interval::not_mv(mv_interval* given){
    
    float high = complement_mv(given->getButtom()->getValue());
    float low = complement_mv(given->getTop()->getValue());
    if(map_all_intervals_->find(std::make_pair(low,high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(low,high), low, high);
        (*map_all_intervals_)[std::make_pair(low,high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(low,high)];
    
}


//void mv_interval::negate_mv(mv_interval* given);



mv_interval* mv_interval::psi_mv(mv_interval* base, mv_interval* given){
    
    float b_low = base->getButtom()->getValue();
    float b_high = base->getTop()->getValue();
    float low = given->getButtom()->getValue();
    float high = given->getTop()->getValue();
    float min_val = getButtom()->getValue();
    float max_val = getTop()->getValue();
    float new_low = min_val;
    float new_high = min_val;
    if( (b_low==min_val && b_high==max_val) || (b_low<=low && b_high==max_val)){
        new_low = low;
        new_high = high;
    }
    else if ( b_high>=high && b_low==min_val){
        new_low = complement_mv(high);
        new_high = complement_mv(low);
    }
    if(map_all_intervals_->find(std::make_pair(new_low,new_high))==map_all_intervals_->end()){
        mv_interval* res = new mv_interval(get_as_str(new_low,new_high), new_low, new_high);
        (*map_all_intervals_)[std::make_pair(new_low, new_high)] = res;
        return res;
    }
    else
        return (*map_all_intervals_)[std::make_pair(new_low, new_high)];
    
}


//--------------------------------------------------------//

mv_interval* create_interval_set(string name, string prefix, int num_nodes)
{
    lattice_node* nodes;
    nodes = new lattice_node[num_nodes];
    for(int i=0; i<num_nodes; i++){
        nodes[i].setName(prefix+"_"+std::to_string(i));
        nodes[i].setValue((float(num_nodes-i-1))/(num_nodes-1));
    }
    mv_interval* itv = new mv_interval(name, nodes, num_nodes);
    
    return itv;
}

void test_intervals(){

    //mv_interval itv= mv_interval();
    //itv.add_interval("q1",.5,1);    
    //itv.add_interval("q2",.5,.5);
    //cout << *itv.get_interval("q1")->getTo_lattice_() <<endl;
    //cout << *itv.get_interval("q2")->getTo_lattice_() <<endl;

//manually assign nodes or use mvspot::create_interval_set
//    mvspot::lattice_node nodes[5];
//    nodes[0].setName("a");
//    nodes[1].setName("b");
//    nodes[2].setName("c");
//    nodes[3].setName("d");
//    nodes[4].setName("e");
//    nodes[0].setValue(1);
//    nodes[1].setValue(0.75);
//    nodes[2].setValue(0.5);
//    nodes[3].setValue(0.25);
//    nodes[4].setValue(0.0);    
//    mv_interval intv(nodes, 5);
//OR    
    mv_interval intv = *mvspot::create_interval_set("my_lattice","l",5);

    cout << "size: " << intv.getTo_lattice_()->getNodes_()->size() << endl;
    cout << *intv.getTo_lattice_() << endl<<endl;   

    for(set<mvspot::lattice_node*>::iterator it 
            = intv.getTo_lattice_()->getNodes_()->begin(); 
            it != intv.getTo_lattice_()->getNodes_()->end(); it++){
        cout << *(mvspot::lattice_node*)(*it) << endl;
    }
    
    mv_interval it1= mv_interval("q",0.125,1);
    cout << "it1: " << *it1.getTo_lattice_() << endl<<endl;   
    mv_interval it2= mv_interval("q",0.625,1);
    cout << "it2: " << *it2.getTo_lattice_() << endl<<endl;   
    mv_interval* jit = intv.join_mv(&it1,&it2);
    cout << "join it1 , it2: " << *jit->getTo_lattice_() << endl<<endl;   
    mv_interval* mit = intv.meet_mv(&it1,&it2);
    cout << "meet it1 , it2: " << *mit->getTo_lattice_() << endl<<endl;   
    cout << "not it2: " << *intv.not_mv(&it2)->getTo_lattice_() << endl<<endl;
    cout << "psi it1 , it2: " << *intv.psi_mv(&it1,&it2)->getTo_lattice_() << endl<<endl;
}
}
