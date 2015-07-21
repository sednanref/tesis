#ifndef HYPERGRAPH_H
#define HYPERGRAPH_H

#include "bitmap_set.h"
#include <iostream>
#include <set>
#include <vector>

namespace Hypergraph {

// Compute a minimum-cost cover of the hypergraph. A cover is
// a collection of edges that touch every vertex. The cost of
// a cover is the sum of the costs of the edges in the cover.

// The following methods compute covers for problems with at
// most MAX_VERTICES_CONSTRAINED. This number must be less than
// or equal to 32. An static array of 2^MAX_VERTICES_CONSTRAINED
// is allocated.

const int MAX_VERTICES_CONSTRAINED = 20;

// For these methods, each hyperedge is represented as a bitmap
// for the vertices *not in* the edge. That is, each edge is 
// represented by its complement. Since the graph contains at
// most MAX_VERTICES_CONSTRAINED, each edge can be stored in a
// 32-bit unsigned integer.
//
// Use the first method when the weight of all edges is one,
// and the second when the edges have different positive costs.

unsigned min_cover(int k,
                   const std::vector<unsigned> &compl_edges,
                   std::vector<unsigned> &cover);

unsigned min_cost_cover(int k,
                        const std::vector<unsigned> &compl_edges,
                        const std::vector<unsigned> &edge_costs,
                        std::vector<unsigned> &cover);

// The following methods work for arbitrary problems. In these
// methods, each edge is a set of vertices.

class Edge : public Utils::BitmapSet { };

unsigned min_cover_unconstrained(int k,
                                 const std::vector<Edge> &edges,
                                 std::vector<unsigned> &cover);

unsigned min_cost_cover_unconstrained(int k,
                                      const std::vector<Edge> &edges,
                                      std::vector<unsigned> &edge_costs,
                                      std::vector<unsigned> &cover);

} // end of namespace

#endif
