/* $Id: CoinPresolveTighten.hpp 1215 2009-11-05 11:03:04Z forrest $ */
// Copyright (C) 2002, International Business Machines
// Corporation and others.  All Rights Reserved.

#ifndef CoinPresolveTighten_H
#define CoinPresolveTighten_H

#include "CoinPresolveMatrix.hpp"

// This action has no separate class;
// instead, it decides which columns can be made fixed
// and calls make_fixed_action::presolve.
const CoinPresolveAction *tighten_zero_cost(CoinPresolveMatrix *prob,
					 const CoinPresolveAction *next);

#define	DO_TIGHTEN	30

class do_tighten_action : public CoinPresolveAction {
  do_tighten_action();
  do_tighten_action(const do_tighten_action& rhs);
  do_tighten_action& operator=(const do_tighten_action& rhs);

  struct action {
    int *rows;
    double *lbound;
    double *ubound;
    int col;
    int nrows;
    int direction;	// just for assertions
  };

  const int nactions_;
  const action *const actions_;

  do_tighten_action(int nactions,
		      const action *actions,
		      const CoinPresolveAction *next) :
    CoinPresolveAction(next),
    nactions_(nactions), actions_(actions) {}

 public:
  const char *name() const;

  static const CoinPresolveAction *presolve(CoinPresolveMatrix *prob,
					 const CoinPresolveAction *next);

  void postsolve(CoinPostsolveMatrix *prob) const;

  ~do_tighten_action();

};
#endif


