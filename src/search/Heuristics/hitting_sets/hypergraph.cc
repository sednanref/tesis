#include "hypergraph.h"
#include "hash_functions.h"
#include <cassert>
#include <queue>
#include <limits>
#include <set>
#include <tr1/unordered_map>

using namespace std;

//#define DEBUG

namespace Hypergraph {

// Data structures for searching for a best cover of the hypergraph.
// See the comments below.
static pair<unsigned, unsigned> generated[1<<MAX_VERTICES_CONSTRAINED];

class Node : public pair<unsigned, unsigned> {
  public:
    Node(unsigned x = 0, unsigned y = 0) : pair<unsigned, unsigned>(x, y) { }
    bool operator()(const Node &n1, const Node &n2) const {
        return (generated[n2.second].first < generated[n1.second].first) ||
               ((generated[n2.second].first == generated[n1.second].first) &&
                (n2.first > n1.first));
    }
};

unsigned min_cover(int k, const vector<unsigned> &compl_edges, vector<unsigned> &cover) {
    // Perform a breadth-first search looking for a min cover of the hypergraph.
    // Each node in the search tree correspond to the subset of remaining vertices
    // to cover. Thus, the goal node is the empty subset and the depth of the
    // goal is the size of the min cover.
    //
    // Each path in the search tree represent a subset of hypeedges. The root is
    // the empty subset, nodes at depth 1 are singletons, and so on. The search
    // tree is generated so that no two subsets are represented in the tree.
    //
    // For efficiency, each edge is represented by its complement so that its
    // application is just a bit-wise and. The set of nodes in the closed/open
    // list is represented as an array of unsigned. We allocate this array for
    // problems up to size MAX_VERTICES_CONSTRAINED implying an array of size
    // 2^MAX_VERTICES_CONSTRAINED. The value of each entry in the array is
    // initialized to -1. A value different from -1 tells the cost of the
    // min-cost cover for that subset.

    // A node structure is a pair (i,subset) where i is an index so that the
    // expansion of the node is done with only edges of index >= i (this 
    // guarantees that no duplicate edge subsets appear in the search tree),
    // and subset is the subset of vertices that still need to be covered.

    assert(k <= MAX_VERTICES_CONSTRAINED);
    deque<Node> open;

    for( int i = 0, isz = 1<<k; i < isz; ++i )
        generated[i] = make_pair(numeric_limits<unsigned>::max(), numeric_limits<unsigned>::max());

    int num_edges = compl_edges.size();
    unsigned root_subset = (1<<k) - 1;
    generated[root_subset].first = 0;
    Node start = Node(0, root_subset);
    open.push_back(start);
#ifdef DEBUG
    cout << "START" << endl;
    cout << "  push: (0, " << root_subset << ") with cost 0" << endl;
#endif

    // Breadth-first search.
    while( !open.empty() ) {
        Node node = open.front();
        open.pop_front();
        unsigned node_cost = generated[node.second].first;
#ifdef DEBUG
        cout << "  pop: (" << node.first << ", " << node.second << ") with cost " << node_cost << endl;
#endif

        // Termination.
        if( node.second == 0 ) break;

        // Expansion.
        for( int i = node.first; i < num_edges; ++i ) {
            unsigned child = node.second & compl_edges[i];
            unsigned child_cost = node_cost + 1;
            if( generated[child].first == numeric_limits<unsigned>::max() ) {
                generated[child] = make_pair(child_cost, node.second);
                open.push_back(Node(1+i, child));
#ifdef DEBUG
                cout << "  push: (" << 1+i << ", " << child << ") with cost " << child_cost << " [edge=" << ~compl_edges[i] << "]" << endl;
#endif
            }
        }
    }
    assert(generated[0].first != numeric_limits<unsigned>::max());
#ifdef DEBUG
    cout << "END" << endl;
#endif

    // Extract cover.
    cover.clear();
    unsigned subset = 0;
    unsigned parent = generated[subset].second;
    assert(parent != numeric_limits<unsigned>::max());
    while( parent != numeric_limits<unsigned>::max() ) {
        unsigned edge = numeric_limits<unsigned>::max();
        for( int i = 0; i < num_edges; ++i ) {
            if( (parent & compl_edges[i]) == subset ) {
                edge = i;
                break;
            }
        }
        assert(edge != numeric_limits<unsigned>::max());
        cover.push_back(edge);
        subset = parent;
        parent = generated[subset].second;
    }
    assert(subset == root_subset);
    assert(generated[0].first == cover.size());
    return generated[0].first;
}

unsigned min_cost_cover(int k, const vector<unsigned> &compl_edges, const vector<unsigned> &edge_costs, vector<unsigned> &cover) {
    // Perform a best-first search looking for a min-cost cover of the hypergraph.
    // Each node in the search tree correspond to the subset of remaining vertices
    // to cover. Thus, the goal node is the empty subset.
    //
    // Each path in the search tree represent a subset of hyperedges. The root is
    // the empty subset, nodes at depth 1 are singletons, and so on. The search
    // tree is generated so that no subset appears twice in the tree.
    //
    // For efficiency, each edge is represented by its complement so that its
    // application is just a bitwise and. The set of nodes in the closed/open
    // list is represented by an array of unsigned. We allocate this array for
    // problems up to size MAX_VERTICES_CONSTRAINED implying an array of size
    // 2^MAX_VERTICES_CONSTRAINED. The value of each entry in the array is
    // initialized to -1. A value different from -1 tells the cost of the
    // min-cost cover for that subset.

    // A node structure is a pair (i,subset) where i is an index so that the
    // expansion of the node is done with only edges of index >= i (this 
    // guarantees that no duplicate edge subsets appear in the search tree),
    // and subset is the subset of vertices that still need to be covered.

    assert(k <= MAX_VERTICES_CONSTRAINED);
    priority_queue<Node, vector<Node>, Node> open;

    for( int i = 0, isz = 1<<k; i < isz; ++i )
        generated[i] = make_pair(numeric_limits<unsigned>::max(), numeric_limits<unsigned>::max());

    int num_edges = compl_edges.size();
    unsigned root_subset = (1<<k) - 1;
    generated[root_subset].first = 0;
    Node start(0, root_subset);
    open.push(start);
#ifdef DEBUG
    cout << "START" << endl;
    cout << "  push: (0, " << root_subset << ") with cost 0" << endl;
#endif

    // Best-first search.
    while( !open.empty() ) {
        Node node = open.top();
        open.pop();
        unsigned node_cost = generated[node.second].first;
#ifdef DEBUG
        cout << "  pop: (" << node.first << ", " << node.second << ") with cost " << node_cost << endl;
#endif

        // Termination
        if( node.second == 0 ) break;

        // Expansion
        for( int i = node.first; i < num_edges; ++i ) {
            unsigned child = node.second & compl_edges[i];
            unsigned child_cost = node_cost + edge_costs[i];
            if( child_cost < generated[child].first ) {
                generated[child] = make_pair(child_cost, node.second);
                open.push(Node(1+i, child));
#ifdef DEBUG
                cout << "  push: (" << 1+i << ", " << child << ") with cost " << child_cost << " [edge=" << ~compl_edges[i] << "]" << endl;
#endif
            }
        }
    }
    assert(generated[0].first != numeric_limits<unsigned>::max());
#ifdef DEBUG
    cout << "END" << endl;
#endif

    // Extract cover.
    cover.clear();
    unsigned subset = 0;
    unsigned parent = generated[subset].second;
    assert(parent != numeric_limits<unsigned>::max());
    unsigned check_cost = 0;
    while( parent != numeric_limits<unsigned>::max() ) {
        unsigned edge = numeric_limits<unsigned>::max();
        for( int i = 0; i < num_edges; ++i ) {
            if( ((parent & compl_edges[i]) == subset) &&
                (generated[subset].first == generated[parent].first + edge_costs[i]) ) {
                edge = i;
                break;
            }
        }
        assert(edge != numeric_limits<unsigned>::max());
        cover.push_back(edge);
        check_cost += edge_costs[edge];
        subset = parent;
        parent = generated[subset].second;
    }
    assert(subset == root_subset);
    assert(generated[0].first == check_cost);
    return generated[0].first;
}

// Data structures for searching for a best cover of the hypergraph (unconstrained).
class Hashmap : public std::tr1::unordered_map<Utils::BitmapSet, pair<unsigned, pair<unsigned, Utils::BitmapSet> > > { };

Hashmap generated_unconstrained;

class UNode : public pair<unsigned, Utils::BitmapSet> {
  public:
    UNode(unsigned index = 0, const Utils::BitmapSet &subset = Utils::BitmapSet())
      : pair<unsigned, Utils::BitmapSet>(index, subset) { }

    bool operator()(const UNode &n1, const UNode &n2) const {
        Hashmap::const_iterator i1 = generated_unconstrained.find(n1.second);
        Hashmap::const_iterator i2 = generated_unconstrained.find(n2.second);
        assert(i1 != generated_unconstrained.end());
        assert(i2 != generated_unconstrained.end());
        return (i2->second.first < i1->second.first) ||
               ((i2->second.first == i1->second.first) && (n2.first > n1.first));
    }
};

unsigned min_cover_unconstrained(int k, const vector<Edge> &edges, vector<unsigned> &cover) {
    deque<UNode> open;

    generated_unconstrained.clear();
    int num_edges = edges.size();
    Utils::BitmapSet root_subset;
    for( int i = 0; i < k; ++i )
        root_subset.insert(i);
    generated_unconstrained[root_subset] = make_pair(0, make_pair(-1, root_subset));
    assert(generated_unconstrained.find(root_subset) != generated_unconstrained.end());
    UNode start(0, root_subset);
    open.push_back(start);
#ifdef DEBUG
    cout << "START" << endl;
    cout << "  push: (0, " << root_subset << ") with cost 0" << endl;
#endif

    // Breadth-first search.
    while( !open.empty() ) {
        UNode node = open.front();
        open.pop_front();
        Hashmap::const_iterator it = generated_unconstrained.find(node.second);
        assert(it != generated_unconstrained.end());
        unsigned node_cost = it->second.first;
#ifdef DEBUG
        cout << "  pop: (" << node.first << ", " << node.second << ") with cost " << node_cost << endl;
#endif

        // Termination.
        if( node.second.empty() ) break;

        // Expansion.
        for( int i = node.first; i < num_edges; ++i ) {
            // generate child node for ith edge.
            Utils::BitmapSet child = node.second;
            child.erase(edges[i]);
            unsigned child_cost = node_cost + 1;

            pair<Hashmap::iterator, bool> p =
                generated_unconstrained.insert(make_pair(child, make_pair(child_cost, make_pair(i, node.second))));
            assert(generated_unconstrained.find(child) != generated_unconstrained.end());
            if( p.second ) {
                open.push_back(UNode(1+i, child));
#ifdef DEBUG
                cout << "  push: (" << 1+i << ", " << child << ") with cost " << child_cost << " [edge=" << edges[i] << "]" << endl;
#endif
            }
        }
    }
    assert(generated_unconstrained.find(Utils::BitmapSet()) != generated_unconstrained.end());
#ifdef DEBUG
    cout << "END" << endl;
#endif

    // Extract cover.
    cover.clear();
    Utils::BitmapSet subset;
    Hashmap::const_iterator it = generated_unconstrained.find(subset);
    assert(it->second.second.first != -1);
    unsigned cover_cost = it->second.first;
    while( it->second.second.first != -1 ) {
        unsigned edge = it->second.second.first;
        cover.push_back(edge);
        subset = it->second.second.second;
        it = generated_unconstrained.find(subset);
        assert(it != generated_unconstrained.end());
    }
    assert(subset == root_subset);
    assert(cover_cost == cover.size());
    return cover_cost;
}

unsigned min_cost_cover_unconstrained(int k, const vector<Edge> &edges, vector<unsigned> &edge_costs, vector<unsigned> &cover) {
    priority_queue<UNode, vector<UNode>, UNode> open;

    generated_unconstrained.clear();
    int num_edges = edges.size();
    Utils::BitmapSet root_subset;
    for( int i = 0; i < k; ++i )
        root_subset.insert(i);
    generated_unconstrained[root_subset] = make_pair(0, make_pair(-1, root_subset));
    assert(generated_unconstrained.find(root_subset) != generated_unconstrained.end());
    UNode start(0, root_subset);
    open.push(start);
#ifdef DEBUG
    cout << "START" << endl;
    cout << "  push: (0, " << root_subset << ") with cost 0" << endl;
#endif

    // Breadth-first search.
    while( !open.empty() ) {
        UNode node = open.top();
        open.pop();
        Hashmap::const_iterator it = generated_unconstrained.find(node.second);
        assert(it != generated_unconstrained.end());
        unsigned node_cost = it->second.first;
#ifdef DEBUG
        cout << "  pop: (" << node.first << ", " << node.second << ") with cost " << node_cost << endl;
#endif

        // Termination.
        if( node.second.empty() ) break;

        // Expansion.
        for( int i = node.first; i < num_edges; ++i ) {
            // generate child node for ith edge.
            Utils::BitmapSet child = node.second;
            child.erase(edges[i]);
            unsigned child_cost = node_cost + edge_costs[i];

            Hashmap::const_iterator it = generated_unconstrained.find(child);
            if( (it == generated_unconstrained.end()) || (child_cost < it->second.first) ) {
                generated_unconstrained[child] = make_pair(child_cost, make_pair(i, node.second));
                assert(generated_unconstrained.find(child) != generated_unconstrained.end());
                open.push(UNode(1+i, child));
#ifdef DEBUG
                cout << "  push: (" << 1+i << ", " << child << ") with cost " << child_cost << " [edge=" << edges[i] << "]" << endl;
#endif
                // TODO: make this more efficient so to call the hash function just once.
            }
        }
    }
    assert(generated_unconstrained.find(Utils::BitmapSet()) != generated_unconstrained.end());
#ifdef DEBUG
    cout << "END" << endl;
#endif

    // Extract cover.
    cover.clear();
    Utils::BitmapSet subset;
    Hashmap::const_iterator it = generated_unconstrained.find(subset);
    assert(it->second.second.first != -1);
    unsigned cover_cost = it->second.first;
    unsigned check_cost = 0;
    while( it->second.second.first != -1 ) {
        unsigned edge = it->second.second.first;
        cover.push_back(edge);
        check_cost += edge_costs[edge];
        subset = it->second.second.second;
        it = generated_unconstrained.find(subset);
        assert(it != generated_unconstrained.end());
    }
    assert(subset == root_subset);
    assert(cover_cost == check_cost);
    return cover_cost;
}

} // end of namespace

