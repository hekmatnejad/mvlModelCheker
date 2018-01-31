/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Util.h
 * Author: mamad
 *
 * Created on January 20, 2017, 1:07 AM
 */

#ifndef UTIL_H
#define UTIL_H

#include "MvLtlModel.h"
#include <ostream>
#include <istream>
#include <iostream>
#include <fstream>
//#include "mvtwaproduct.h"//
#include <spot/parseaut/public.hh>

class Util {
public:
    Util();
    Util(const Util& orig);
    virtual ~Util();
    
static bool write2File(string fName, const spot::const_twa_ptr& g, const char* options= nullptr){
    std:ofstream outFile;
    outFile.open(fName.c_str());
    if(!outFile.is_open())
        return false;
    spot::print_dot(outFile, g, options);
    outFile.close();
    return true;
}

static bool write2FileAsHoa(string fName, const spot::const_twa_ptr& g, const char* options= nullptr){
    std:ofstream outFile;
    outFile.open(fName.c_str());
    if(!outFile.is_open())
        return false;
    spot::print_hoa(outFile, g, options);
    outFile.close();
    return true;
}

static stringstream readFromFile(string fName){
    std:ifstream inFile;
    stringstream ss;
    inFile.open(fName.c_str());
    if(!inFile.is_open())
        return ss;
    
    inFile.seekg (0, inFile.end);
    int length = inFile.tellg();
    inFile.seekg (0, inFile.beg);

    //char * buffer = new char [length];
    ss << inFile.rdbuf();
    //inFile.read (buffer,length);
    inFile.close();
    //return buffer;
    return ss;
}
// 1 Fin(0)
//0 t
//recognized: HOA, LBTT, DSTAR, or neverclaim.
static spot::parsed_aut_ptr readAutFromFile(string fName, bool kripke_graph=true, spot::bdd_dict_ptr dict=spot::make_bdd_dict()){
    spot::automaton_parser_options opt;
    opt.want_kripke=kripke_graph;
    opt.ignore_abort=false;
    opt.debug=false;
    opt.trust_hoa=true;
    opt.raise_errors=false;
    spot::parsed_aut_ptr kg = spot::parse_aut(fName, dict,
                    spot::default_environment::instance(),opt);
    return kg;
}
private:

};

#endif /* UTIL_H */

