/*
Version information of the library
by: Mohammad Hekmatnejad
*/
#ifndef MVFF_H
#define MVFF_H

#pragma once
#include <memory>
#include <spot/twa/twa.hh>


namespace mvspot
{
    class mv_interval;
    typedef std::shared_ptr<mv_interval> mv_interval_ptr;
    class interval_bdd;
    typedef std::shared_ptr<interval_bdd> mv_interval_bdd_ptr;
}

#endif