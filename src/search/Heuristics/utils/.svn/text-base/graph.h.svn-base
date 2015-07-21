#ifndef GRAPH_H
#define GRAPH_H

#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <cassert>
#include <strings.h>

namespace Graph {

class LabelList : public std::vector<int> { };

class Directed {
protected:
    int num_nodes_;
    int num_edges_;
    int source_, target_;
    std::map<int,LabelList> labels_;
public:
    Directed(int num_nodes, int source, int target) : num_nodes_(num_nodes), num_edges_(0), source_(source), target_(target) { }
    virtual ~Directed() { }

    int num_nodes() const { return num_nodes_; }
    int num_edges() const { return num_edges_; }
    int source() const { return source_; }
    int target() const { return target_; }
    void set_source(int source) { source_ = source; }
    void set_target(int target) { target_ = target; }

    virtual const LabelList& labels(int eindex) const {
        std::map<int,LabelList>::const_iterator li = labels_.find(eindex);
        assert( li != labels_.end() );
        return li->second;
    }
    virtual void add_label(int eindex, int label = -1) {
        std::map<int,LabelList>::iterator p = labels_.find(eindex);
        if( p == labels_.end() ) {
            labels_.insert(std::make_pair(eindex,LabelList()));
            if( label != -1 ) labels_[eindex].push_back(label);
        } else if( label != -1 ) {
            bool found = false;
            for( LabelList::const_iterator li = p->second.begin(); li != p->second.end(); ++li ) {
                if( *li == label ) {
                    found = true;
                    break;
                }
            }
            if( !found ) p->second.push_back(label);
        }
    }
    virtual void set_label(int eindex, const LabelList &label) {
        std::map<int,LabelList>::iterator p = labels_.find(eindex);
        if( p != labels_.end() ) {
            p->second = label;
        } else {
            labels_.insert(std::make_pair(eindex,label));
        }
    }

    virtual void clear_edges() = 0;
    virtual int edge_index(int u, int v) const = 0;
    virtual std::pair<int,int> edge(int index) const = 0;
    virtual bool is_edge(int u, int v) const { return edge_index(u,v) != -1; }
    virtual int add_edge(int u, int v, int label = -1) = 0;

    // Compute everything backward-reachable from node
    virtual void backward_reachability(int node, std::vector<int> &reachability) const = 0;
    // Compute everything forward-reachable from node
    virtual void forward_reachability(int node, std::vector<int> &reachability) const = 0;
    // Compute everything that is backward-reachable from target and forward-reachable 
    // from source
    virtual int reachability_analysis(std::vector<int> &reachability) const {
        reachability.clear();
        reachability.reserve(num_nodes_);
        reachability.insert(reachability.end(),num_nodes_,0);
        backward_reachability(target_,reachability);
        forward_reachability(source_,reachability);

        int num = 0;
        for( int i = 0; i < num_nodes_; ++i )
            num += reachability[i] == 3 ? 1 : 0;
        return num;
    }

    // Compute the {s,t}-reachability induced graph. The result is graph which must
    // be a graph with enough number of nodes, reachability is the vector computed
    // by reachability_analysis(), and hom and inv_hom are the resulting homomorphism
    // and inverse homomorphism between the input and output graphs.
    virtual void calculate_reduced_reachability_graph(Directed &graph, std::vector<int> &reachability, std::vector<int> &hom, std::vector<int> &inv_hom) const = 0;

    void dump(std::ostream &os) const {
        os << "p edge " << num_nodes_ << " " << num_edges_ << std::endl;
        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++ v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    const LabelList &lab = labels(eindex);
                    os << "e " << u << " " << v << " " << lab.size();
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << " " << *li;
                    os << std::endl;
                }
            }
        }
    }

    void print(std::ostream &os) const {
        os << "DirectedGraph [" << std::endl
           << "    num_nodes=" << num_nodes_ << std::endl
           << "    num_edges=" << num_edges_ << std::endl
           << "    source=" << source_ << std::endl
           << "    target=" << target_ << std::endl;

        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++ v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    os << "    edge[" << u << "," << v << "]" << std::endl;
                }
            }
        }

        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    os << "    label[" << u << "," << v << "]={";
                    const LabelList &lab = labels(eindex);
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << *li << ",";
                    os << "}" << std::endl;
                }
            }
        }

        os << "]" << std::endl;
    }

    void write(std::ostream &os) const {
        os << num_nodes_ << " " << num_edges_ << " " << source_ << " " << target_ << std::endl;
        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    const LabelList &lab = labels(eindex);
                    os << u << " " << v << " " << lab.size();
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << " " << *li;
                    os << std::endl;
                }
            }
        }
    }

};

class DirectedList : public Directed {
    std::vector<std::vector<std::pair<int,int> > > in_lists_;
    std::vector<std::vector<std::pair<int,int> > > out_lists_;
    std::vector<std::vector<int> > out_lists2_;
    std::vector<std::pair<int,int> > edges_;
public:
    DirectedList(int num_nodes, int source, int target) : Directed(num_nodes,source,target) {
        in_lists_.reserve(num_nodes_);
        out_lists_.reserve(num_nodes_);
        out_lists2_.reserve(num_nodes_);
        for( int i = 0; i < num_nodes_; ++i ) {
          in_lists_.push_back(std::vector<std::pair<int,int> >());
          out_lists_.push_back(std::vector<std::pair<int,int> >());
          out_lists2_.push_back(std::vector<int>());
        }
    }
    virtual ~DirectedList() { }

    const std::vector<std::vector<std::pair<int,int> > >& in_lists() const { return in_lists_; }
    const std::vector<std::vector<std::pair<int,int> > >& out_lists() const { return out_lists_; }
    const std::vector<std::vector<int> >& out_lists2() const { return out_lists2_; }

    virtual void clear_edges() {
        for( int i = 0; i < num_nodes_; ++i ) {
            in_lists_[i].clear();
            out_lists_[i].clear();
            out_lists2_[i].clear();
        }
        labels_.clear();
        num_edges_ = 0;
    }

    virtual int edge_index(int u, int v) const {
        for( int i = 0, isz = in_lists_[v].size(); i < isz; ++i ) {
            if( in_lists_[v][i].first == u )
                return in_lists_[v][i].second;
        }
        return -1;
    }

    virtual std::pair<int,int> edge(int index) const {
        if( (index < 0) || (index >= num_edges_) )
            return std::make_pair(-1,-1);
        else
            return edges_[index];
    }

    virtual int add_edge(int u, int v, int label = -1) {
        int eindex = edge_index(u,v);
        if( eindex == -1 ) {
            in_lists_[v].push_back(std::make_pair(u,num_edges_));
            out_lists_[u].push_back(std::make_pair(v,num_edges_));
            out_lists2_[u].push_back(v);
            eindex = num_edges_++;
            edges_.push_back(std::make_pair(u,v));
        }
        add_label(eindex,label);
        return eindex;
    }

    virtual void backward_reachability(int node, std::vector<int> &reachability) const {
        if( !(reachability[node] & 0x1) ) {
            reachability[node] += 1;
            for( int i = 0, isz = in_lists_[node].size(); i < isz; ++i ) {
                backward_reachability(in_lists_[node][i].first,reachability);
            }
        }
    }
    virtual void forward_reachability(int node, std::vector<int> &reachability) const {
        if( !(reachability[node] & 0x2) ) {
            reachability[node] += 2;
            for( int i = 0, isz = out_lists_[node].size(); i < isz; ++i ) {
                forward_reachability(out_lists_[node][i].first,reachability);
            }
        }
    }
    virtual void calculate_reduced_reachability_graph(Directed &graph, std::vector<int> &reachability, std::vector<int> &hom, std::vector<int> &inv_hom) const {

        // initialize
        graph.clear_edges();
        hom.clear();
        hom.reserve(num_nodes_);
        hom.insert(hom.end(),num_nodes_,-1);
        inv_hom.clear();
        inv_hom.reserve(graph.num_nodes());
        inv_hom.insert(inv_hom.end(),graph.num_nodes(),-1);

        // iterate over all edges
        int n = 0;
        for( int u = 0; u < num_nodes_; ++u ) {
            if( reachability[u] == 3 ) {
                if( hom[u] == -1 ) { // extend homomorphism with u
                    hom[u] = n;
                    inv_hom[n] = u;
                    ++n;
                    assert(n <= graph.num_nodes());
                }
                for( int j = 0, jsz = out_lists_[u].size(); j < jsz; ++j ) {
                    int v = out_lists_[u][j].first;
                    if( reachability[v] == 3 ) {
                        if( hom[v] == -1 ) { // extend homomorphism with v
                            hom[v] = n;
                            inv_hom[n] = v;
                            ++n;
                            assert(n <= graph.num_nodes());
                        }
                        int eindex = graph.add_edge(hom[u],hom[v]);
                        graph.set_label(eindex,labels(out_lists_[u][j].second));
                    }
                }
            }
        }

        // set source/target
        assert(hom[source_] != -1);
        assert(hom[target_] != -1);
        graph.set_source(hom[source_]);
        graph.set_target(hom[target_]);
    }

    void dump_lists(std::ostream &os) const {
        os << "{#nodes=" << num_nodes_ << ",out_list={";
        for( int i = 0; i < num_nodes_; ++i ) {
            if( !out_lists_[i].empty() ) {
                os << "[" << i << ",[";
                for( int j = 0, jsz = out_lists_[i].size(); j < jsz; ++j ) {
                    os << out_lists_[i][j].first << ",";
                }
                os << "]],";
            }
        }
        os << "}}";
    }

    static DirectedList* read(std::ifstream &is) {
        int num_nodes, num_edges, source, target;
        is >> num_nodes >> num_edges >> source >> target;
        DirectedList *graph = new DirectedList(num_nodes,source,target);
        for( int i = 0; i < num_edges; ++i ) {
            int u, v, num_labels, label;
            is >> u >> v >> num_labels;
            int eindex = graph->add_edge(u,v);
            LabelList labels;
            labels.reserve(num_labels);
            for( int j = 0; j < num_labels; ++j ) {
                is >> label;
                labels.push_back(label);
            }
            graph->set_label(eindex,labels);
        }
        return graph;
    }

};

} // end of namespace

inline std::ostream& operator<<(std::ostream &os, const Graph::Directed &digraph) {
    digraph.print(os);
    return os;
}








namespace Digraph {

class LabelList : public std::vector<int> { };

class Directed {
protected:
    const int num_nodes_;
    int num_edges_, source_, target_;
    int *matrix_;

    std::vector<std::vector<std::pair<int,int> > > in_lists_, out_lists_;
    std::vector<std::vector<int> > out_lists2_;
    std::vector<LabelList> labels_;
    std::vector<std::pair<int,int> > edges_;
    //std::map<int,LabelList> labels_;

public:
    Directed(int num_nodes, int source, int target) :
      num_nodes_(num_nodes), num_edges_(0), source_(source), target_(target),
      in_lists_(num_nodes_,std::vector<std::pair<int,int> >()),
      out_lists_(num_nodes_,std::vector<std::pair<int,int> >()),
      out_lists2_(num_nodes_,std::vector<int>()) {
        matrix_ = new int[num_nodes_*num_nodes_];
        bzero(matrix_,num_nodes_*num_nodes_*sizeof(int));
        labels_.reserve(num_nodes_);
    }
    ~Directed() { delete[] matrix_; }

    int num_nodes() const { return num_nodes_; }
    int num_edges() const { return num_edges_; }
    int source() const { return source_; }
    int target() const { return target_; }
    void set_source(int source) { source_ = source; }
    void set_target(int target) { target_ = target; }

    const std::vector<std::vector<std::pair<int,int> > >& in_lists() const { return in_lists_; }
    const std::vector<std::vector<std::pair<int,int> > >& out_lists() const { return out_lists_; }
    const std::vector<std::pair<int,int> >& out_list(int i) const { return out_lists_[i]; }
    const std::vector<std::vector<int> >& out_lists2() const { return out_lists2_; }

    void clear() {
        num_edges_ = 0;
        for( int i = 0; i < num_nodes_; ++i ) {
            in_lists_[i].clear();
            out_lists_[i].clear();
            out_lists2_[i].clear();
        }
        labels_.clear();
        edges_.clear();
        bzero(matrix_,num_nodes_*num_nodes_*sizeof(int));
    }

    const LabelList& labels(int eindex) const {
        assert(eindex < num_edges_);
        return labels_[eindex];
    }
    void add_label(int eindex, int label = -1) {
        assert(eindex < num_edges_);
        if( label == -1 ) return;
        for( LabelList::const_iterator l = labels_[eindex].begin(); l != labels_[eindex].end(); ++l ) {
            if( *l == label ) return;
        }
        labels_[eindex].push_back(label);
    }
    void set_label(int eindex, const LabelList &label) {
        assert(eindex < num_edges_);
        labels_[eindex] = label;
    }
    std::pair<int, int> get_edge(int eindex) const {
        return edges_[eindex];
    }

    //std::pair<int,int> edge(int index) const = 0;
    int edge_index(int u, int v) const { return matrix_[u*num_nodes_+v]-1; }
    bool is_edge(int u, int v) const { return edge_index(u,v) != -1; }

    int add_edge(int u, int v, int label = -1) {
        assert((u >= 0) && (u < num_nodes_));
        assert((v >= 0) && (u < num_nodes_));
        int eindex = edge_index(u,v);
        if( eindex == -1 ) {
            in_lists_[v].push_back(std::make_pair(u,num_edges_));
            out_lists_[u].push_back(std::make_pair(v,num_edges_));
            out_lists2_[u].push_back(v);
            edges_.push_back(std::make_pair(u,num_edges_));
            eindex = num_edges_++;
            matrix_[u*num_nodes_+v] = eindex+1;
            labels_.push_back(LabelList());
            //edges_.push_back(std::make_pair(u,v));
        }
        add_label(eindex,label);
        return eindex;
    }

    // Compute everything backward-reachable from node.
    void backward_reachability(int node, std::vector<int> &reachability) const {
        if( !(reachability[node] & 0x1) ) {
            reachability[node] += 1;
            for( int i = 0, isz = in_lists_[node].size(); i < isz; ++i ) {
                backward_reachability(in_lists_[node][i].first,reachability);
            }
        }
    }

    // Compute everything forward-reachable from node
    void forward_reachability(int node, std::vector<int> &reachability) const {
        if( !(reachability[node] & 0x2) ) {
            reachability[node] += 2;
            for( int i = 0, isz = out_lists_[node].size(); i < isz; ++i ) {
                forward_reachability(out_lists_[node][i].first,reachability);
            }
        }
    }

    // Compute everything that is backward-reachable from target and forward-reachable
    // from source.
    int reachability_analysis(std::vector<int> &reachability) const {
        reachability.clear();
        reachability.reserve(num_nodes_);
        reachability.insert(reachability.end(),num_nodes_,0);
        backward_reachability(target_,reachability);
        forward_reachability(source_,reachability);

        int num = 0;
        for( int i = 0; i < num_nodes_; ++i )
            num += reachability[i] == 3 ? 1 : 0;
        return num;
    }

    // Compute the {s,t}-reachability induced graph. The result is graph which must
    // be a graph with enough number of nodes, reachability is the vector computed
    // by reachability_analysis(), and hom and inv_hom are the resulting homomorphism
    // and inverse homomorphism between the input and output graphs.
    void calculate_reduced_reachability_graph(Directed &graph, std::vector<int> &reachability, std::vector<int> &hom, std::vector<int> &inv_hom) const {

        // initialize
        graph.clear();
        hom.clear();
        hom.reserve(num_nodes_);
        hom.insert(hom.end(),num_nodes_,-1);
        inv_hom.clear();
        inv_hom.reserve(num_nodes_);
        inv_hom.insert(inv_hom.end(),graph.num_nodes(),-1);

        // iterate over all edges
        int n = 0;
        for( int u = 0; u < num_nodes_; ++u ) {
            if( reachability[u] == 3 ) {
                if( hom[u] == -1 ) { // extend homomorphism with u
                    hom[u] = n;
                    inv_hom[n] = u;
                    ++n;
                    assert(n <= graph.num_nodes());
                }
                for( int j = 0, jsz = out_lists_[u].size(); j < jsz; ++j ) {
                    int v = out_lists_[u][j].first;
                    if( reachability[v] == 3 ) {
                        if( hom[v] == -1 ) { // extend homomorphism with v
                            hom[v] = n;
                            inv_hom[n] = v;
                            ++n;
                            assert(n <= graph.num_nodes());
                        }
                        int eindex = graph.add_edge(hom[u],hom[v]);
                        graph.set_label(eindex,labels(out_lists_[u][j].second));
                    }
                }
            }
        }

        // set source/target
        assert(hom[source_] != -1);
        assert(hom[target_] != -1);
        graph.set_source(hom[source_]);
        graph.set_target(hom[target_]);
    }

    // perform a complete depth-first search that detects forward and backward edges
    void dfs(std::vector<int> &parent, std::vector<int> &forward, std::vector<int> &backward) const {
        forward.clear();
        backward.clear();
        parent = std::vector<int>(num_nodes_, -1);
        std::vector<bool> visited(num_nodes_, false), done_with_node(num_nodes_, false);
        for( int root = 0; root < num_nodes_; ++root ) {
            if( !visited[root] ) {
                recursive_dfs(root, parent, visited, done_with_node, forward, backward);
            }
        }
        if( !backward.empty() ) std::cout << "Graph contains cycles!" << std::endl;
    }
    void recursive_dfs(int u, std::vector<int> &parent, std::vector<bool> &visited, std::vector<bool> &done_with_node, std::vector<int> &forward, std::vector<int> &backward) const {
        visited[u] = true;
        for( int i = 0; i < out_lists_[u].size(); ++i ) {
            std::pair<int, int> p = out_lists_[u][i];
            if( visited[p.first] && !done_with_node[p.first] ) {
                backward.push_back(p.second);
            } else if( !visited[p.first] ) {
                forward.push_back(p.second);
                parent[p.first] = u;
                recursive_dfs(p.first, parent, visited, done_with_node, forward, backward);
            }
        }
        done_with_node[u] = true;
    }

    void dump(std::ostream &os) const {
        os << "p edge " << num_nodes_ << " " << num_edges_ << std::endl;
        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++ v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    const LabelList &lab = labels(eindex);
                    os << "e " << u << " " << v << " " << lab.size();
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << " " << *li;
                    os << std::endl;
                }
            }
        }
    }

    void dump_lists(std::ostream &os) const {
        os << "{#nodes=" << num_nodes_ << ",out_list={";
        for( int i = 0; i < num_nodes_; ++i ) {
            if( !out_lists_[i].empty() ) {
                os << "[" << i << ",[";
                for( int j = 0, jsz = out_lists_[i].size(); j < jsz; ++j ) {
                    os << out_lists_[i][j].first << ",";
                }
                os << "]],";
            }
        }
        os << "}}";
    }

    void print(std::ostream &os) const {
        os << "DirectedGraph [" << std::endl
           << "    num_nodes=" << num_nodes_ << std::endl
           << "    num_edges=" << num_edges_ << std::endl
           << "    source=" << source_ << std::endl
           << "    target=" << target_ << std::endl;

        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++ v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    os << "    edge[" << u << "," << v << "]" << std::endl;
                }
            }
        }

        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    os << "    label[" << u << "," << v << "]={";
                    const LabelList &lab = labels(eindex);
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << *li << ",";
                    os << "}" << std::endl;
                }
            }
        }

        os << "]" << std::endl;
    }

    void write(std::ostream &os) const {
        os << num_nodes_ << " " << num_edges_ << " " << source_ << " " << target_ << std::endl;
        for( int u = 0; u < num_nodes_; ++u ) {
            for( int v = 0; v < num_nodes_; ++v ) {
                int eindex = edge_index(u,v);
                if( eindex != -1 ) {
                    const LabelList &lab = labels(eindex);
                    os << u << " " << v << " " << lab.size();
                    for( LabelList::const_iterator li = lab.begin(); li != lab.end(); ++li )
                        os << " " << *li;
                    os << std::endl;
                }
            }
        }
    }

    static Directed* read(std::ifstream &is) {
        int num_nodes, num_edges, source, target;
        is >> num_nodes >> num_edges >> source >> target;
        Directed *graph = new Directed(num_nodes,source,target);
        for( int i = 0; i < num_edges; ++i ) {
            int u, v, num_labels, label;
            is >> u >> v >> num_labels;
            int eindex = graph->add_edge(u,v);
            LabelList labels;
            labels.reserve(num_labels);
            for( int j = 0; j < num_labels; ++j ) {
                is >> label;
                labels.push_back(label);
            }
            graph->set_label(eindex,labels);
        }
        return graph;
    }

};

} // end of namespace

inline std::ostream& operator<<(std::ostream &os, const Digraph::Directed &digraph) {
    digraph.print(os);
    return os;
}


#endif

