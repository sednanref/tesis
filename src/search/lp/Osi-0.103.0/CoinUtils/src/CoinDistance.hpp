/* $Id: CoinDistance.hpp 1215 2009-11-05 11:03:04Z forrest $ */
// Copyright (C) 2000, International Business Machines
// Corporation and others.  All Rights Reserved.
#ifndef CoinDistance_H
#define CoinDistance_H

#include <iterator>

//-------------------------------------------------------------------
//
// Attempt to provide an std::distance function
// that will work on multiple platforms
//
//-------------------------------------------------------------------

/** CoinDistance

This is the Coin implementation of the std::function that is 
designed to work on multiple platforms.
*/
template <class ForwardIterator, class Distance>
void coinDistance(ForwardIterator first, ForwardIterator last,
		  Distance& n)
{
#if defined(__SUNPRO_CC)
   n = 0;
   std::distance(first,last,n);
#else
   n = std::distance(first,last);
#endif
}

template <class ForwardIterator>
size_t coinDistance(ForwardIterator first, ForwardIterator last)
{
   size_t retVal;
#if defined(__SUNPRO_CC)
   retVal = 0;
   std::distance(first,last,retVal);
#else
   retVal = std::distance(first,last);
#endif
  return retVal;
}

#endif
