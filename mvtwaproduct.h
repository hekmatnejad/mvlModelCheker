/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   mvtwaproduct.h
 * Author: mhekmatnejad
 *
 * Created on December 27, 2017, 5:25 PM
 */
#pragma once

#ifndef MV_TWAPRODUCT_H
#define MV_TWAPRODUCT_H

#include "MvLtlModel.h"



// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2013, 2014, 2015, 2016 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2006 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <spot/twa/twa.hh>
#include <spot/misc/fixpool.hh>
//#include "mv_interval.h"


namespace mv
{
namespace spot
{

  /// \ingroup twa_on_the_fly_algorithms
  /// \brief A state for spot::twa_product.
  ///
  /// This state is in fact a pair of state: the state from the left
  /// automaton and that of the right.
  class SPOT_API state_product final: public ::spot::state
  {
  public:
    /// \brief Constructor
    /// \param left The state from the left automaton.
    /// \param right The state from the right automaton.
    /// \param pool The pool from which the state was allocated.
    /// These states are acquired by spot::state_product, and will
    /// be destroyed on destruction.
    state_product(const state* left,
                  const state* right,
                  ::spot::fixed_size_pool* pool)
      :        left_(left), right_(right), count_(1), pool_(pool)
    {
    }

    virtual void destroy() const override;

    const state*
    left() const
    {
      return left_;
    }

    const state*
    right() const
    {
      return right_;
    }

    virtual int compare(const state* other) const override;
    virtual size_t hash() const override;
    virtual state_product* clone() const override;

  private:
    const state* left_;                ///< State from the left automaton.
    const state* right_;        ///< State from the right automaton.
    mutable unsigned count_;
    ::spot::fixed_size_pool* pool_;

    virtual ~state_product();
    state_product(const state_product& o) = delete;
  };


  /// \brief A lazy product.  (States are computed on the fly.)
  class SPOT_API twa_product: public ::spot::twa
  {
  public:
    /// \brief Constructor.
    /// \param left The left automata in the product.
    /// \param right The right automata in the product.
    /// Do not be fooled by these arguments: a product is commutative.
    twa_product(const ::spot::const_twa_ptr& left, const ::spot::const_twa_ptr& right);
    //twa_product(const ::spot::const_twa_ptr& left, const ::spot::const_twa_ptr& right, mvspot::mv_interval* intervals);
    virtual ~twa_product();

    virtual const ::spot::state* get_init_state() const override;

    virtual ::spot::twa_succ_iterator*
    succ_iter(const ::spot::state* state) const override;

    virtual std::string format_state(const ::spot::state* state) const override;

    virtual ::spot::state* project_state(const ::spot::state* s, const ::spot::const_twa_ptr& t)
      const override;

    const ::spot::acc_cond& left_acc() const;
    const ::spot::acc_cond& right_acc() const;

  protected:
    ::spot::const_twa_ptr left_;
    ::spot::const_twa_ptr right_;
    bool left_kripke_;
    ::spot::fixed_size_pool pool_;
    mvspot::mv_interval* intervals_;


  private:
    // Disallow copy.
    twa_product(const twa_product&) = delete;
    twa_product& operator=(const twa_product&) = delete;
  };

  /// \brief A lazy product with different initial states.
  class SPOT_API twa_product_init final: public ::spot::twa_product
  {
  public:
    twa_product_init(const ::spot::const_twa_ptr& left, const ::spot::const_twa_ptr& right,
                      const ::spot::state* left_init, const ::spot::state* right_init);
    virtual const ::spot::state* get_init_state() const override;
  protected:
    const ::spot::state* left_init_;
    const ::spot::state* right_init_;
  };

  /// \brief on-the-fly TGBA product
  inline ::spot::twa_product_ptr otf_product(const ::spot::const_twa_ptr& left,
                                      const ::spot::const_twa_ptr& right)
  {
      std::cout << "*** in -> otf_product\n";
    return std::make_shared<::spot::twa_product>(left, right);
    //return std::make_shared<mvspot::mv_twa_product>(left, right, nullptr);
  }

  /// \brief on-the-fly TGBA product with forced initial states
  inline ::spot::twa_product_ptr otf_product_at(const ::spot::const_twa_ptr& left,
                                        const ::spot::const_twa_ptr& right,
                                        const ::spot::state* left_init,
                                        const ::spot::state* right_init)
  {
    return std::make_shared<::spot::twa_product_init>(left, right,
                                              left_init, right_init);
  }
}//spot namespace
}//mv namespace
#endif /* MVTWAPRODUCT_HH */