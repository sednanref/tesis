/* $Id: CoinUtility.hpp 1215 2009-11-05 11:03:04Z forrest $ */
#ifndef CoinUtility_h_
#define CoinUtility_h_

#include "CoinSort.hpp"

template <typename S, typename T>
CoinPair<S,T> CoinMakePair(const S& s, const T& t)
{ return CoinPair<S,T>(s, t); }

template <typename S, typename T, typename U>
CoinTriple<S,T,U> CoinMakeTriple(const S& s, const T& t, const U& u)
{ return CoinTriple<S,T,U>(s, t, u); }

#endif
