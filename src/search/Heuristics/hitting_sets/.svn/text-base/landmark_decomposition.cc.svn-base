#include "landmark_decomposition.h"
#include <iomanip>

using namespace std;

//#define DEBUG
#define DBL_CHECK

namespace HittingSets {

// Solvers
int solve(const Relaxed::Problem &rproblem,
          int num_landmarks,
          const Landmark *landmarks,
          Relaxed::OperatorSet &hitting_set);

int chvatal_algorithm(const Relaxed::Problem &rproblem,
                      int num_landmarks,
                      const Landmark *landmarks,
                      Relaxed::OperatorSet &hitting_set);

LandmarkDecomposition::LandmarkDecomposition(const Relaxed::Problem &rproblem, bool optimal)
  : rproblem_(rproblem), num_operators_(0), optimal_(optimal) {
}

LandmarkDecomposition::~LandmarkDecomposition() {
    delete global_hitting_set_;
}

void LandmarkDecomposition::initialize() {
    num_operators_ = rproblem_.operators_.size();
    cout << "Initializing landmark decomposition..." << endl;

    F_ = vector<pair<int, const Landmark*> >(num_operators_, pair<int, const Landmark*>(0,0));
    hitting_sets_ = vector<Relaxed::OperatorSet>(num_operators_, Relaxed::OperatorSet());
    global_hitting_set_ = new Relaxed::OperatorSet;

    hitting_set_costs_ = vector<int>(num_operators_, 0);
    global_hitting_set_cost_ = 0;

    rank_ = vector<int>(num_operators_, 0);
    parent_ = vector<int>(num_operators_, 0);
}

void LandmarkDecomposition::clear_hitting_sets() {
    for( int i = 0; i < num_operators_; ++i ) {
        hitting_sets_[i].clear();
        hitting_set_costs_[i] = 0;
    }
    global_hitting_set_->clear();
    global_hitting_set_cost_ = 0;
}

void LandmarkDecomposition::prepare_computation() {
    for( int i = 0; i < num_operators_; ++i ) {
        rank_[i] = 0;
        parent_[i] = i;
    }
    width_ = 0;
}

void LandmarkDecomposition::remove_landmarks() {
    for( set<int>::const_iterator ri = roots_.begin(); ri != roots_.end(); ++ri ) {
        Landmark::deallocate_chain(F_[*ri].second);
        F_[*ri] = make_pair((int)0, (Landmark*)0);
    }
    roots_.clear();
}

void LandmarkDecomposition::Union(int i, int j) {
    i = Find(i);
    j = Find(j);

    int root = i, child = j;
    if( rank_[i] < rank_[j] ) {
        root = j;
        child = i;
    } else if( (i != j) && (rank_[i] == rank_[j]) ) {
        ++rank_[i];
    }

    parent_[child] = root;
    if( root != child ) {
        const Landmark *next_lm = 0;
        for( const Landmark *lm = F_[child].second; lm != 0; lm = next_lm ) {
            next_lm = lm->next_;
            lm->next_ = const_cast<Landmark*>(F_[root].second);
            F_[root].second = lm;
            ++F_[root].first;
        }
        F_[child] = std::make_pair((int)0, (Landmark*)0);
        roots_.erase(child);
        hitting_sets_[root].insert(hitting_sets_[child]);
        hitting_sets_[child].clear();
        hitting_set_costs_[root] += hitting_set_costs_[child];
        hitting_set_costs_[child] = 0;
    }
}

int LandmarkDecomposition::Find(int i) const {
    if( parent_[i] == i ) {
        return i;
    } else {
        parent_[i] = Find(parent_[i]);
        return parent_[i];
    }
}

int LandmarkDecomposition::Add(const Landmark *L) {
    // Update union/find forest.
    int first_action = *L->begin();
    for( Landmark::const_iterator l = L->begin(); l != L->end(); ++l ) {
        Union(first_action, *l);
    }
    int root = Find(first_action);
    L->next_ = const_cast<Landmark*>(F_[root].second);
    F_[root].second = L;
    ++F_[root].first;
    roots_.insert(root);
    width_ = max(F_[root].first, width_);
    global_hitting_set_->erase(hitting_sets_[root]);
    global_hitting_set_cost_ -= hitting_set_costs_[root];
    hitting_sets_[root].clear();
    hitting_set_costs_[root] = 0;
    return root;
}

int LandmarkDecomposition::Width(const Relaxed::OperatorSet &cutset) {
    set<int> cutset_roots;
    for( Relaxed::OperatorSet::const_iterator ci = cutset.begin(); ci != cutset.end(); ++ci ) {
        cutset_roots.insert(Find(*ci));
    }
    int width = 1;
    for( set<int>::const_iterator ri = cutset_roots.begin(); ri != cutset_roots.end(); ++ri )
        width += F_[*ri].first;
    return max(width, width_);
}

void LandmarkDecomposition::Repartition_bucket(int bucket, bool solve) {
    // Clear hitting set for bucket.
    global_hitting_set_->erase(hitting_sets_[bucket]);
    global_hitting_set_cost_ -= hitting_set_costs_[bucket];
    hitting_sets_[bucket].clear();
    hitting_set_costs_[bucket] = 0;

    // Remove landmarks from bucket and bucket from roots.
    const Landmark *landmarks = F_[bucket].second;
    F_[bucket] = make_pair(0, (Landmark*)0);
    roots_.erase(bucket);

    // Reset union/find forest.
    for( const Landmark *lm = landmarks; lm != 0; lm = lm->next_ ) {
        for( Landmark::const_iterator l = lm->begin(); l != lm->end(); ++l ) {
            rank_[*l] = 0;
            parent_[*l] = *l;
        }
    }

    // Recompute union/find forest.
    for( const Landmark *lm = landmarks; lm != 0; lm = lm->next_ ) {
        int first_action = Find(*lm->begin());
        for( Landmark::const_iterator l = lm->begin(); l != lm->end(); ++l )
            Union(first_action,*l);
    }

    // Distribute landmarks into new buckets.
    set<int> new_roots;
    const Landmark *next_lm = 0;
    for( const Landmark *lm = landmarks; lm != 0; lm = next_lm ) {
        next_lm = lm->next_;
        int root = Find(*lm->begin());
        lm->next_ = const_cast<Landmark*>(F_[root].second);
        F_[root].second = lm;
        ++F_[root].first;
        roots_.insert(root);
        new_roots.insert(root);
    }

    // Recompute width.
    width_ = 0;
    for( set<int>::const_iterator r = roots_.begin(); r != roots_.end(); ++r )
        width_ = max(F_[*r].first, width_);

    // Solve new buckets.
    if( solve ) {
        for( set<int>::const_iterator r = new_roots.begin(); r != new_roots.end(); ++r )
            solve_bucket(*r);
    }
}

bool LandmarkDecomposition::is_hitting_set(const Relaxed::OperatorSet &hitting_set) const {
    for( set<int>::const_iterator ri = roots_.begin(); ri != roots_.end(); ++ri ) {
        for( const Landmark *lm = F_[*ri].second; lm != 0; lm = lm->next_ ) {
            if( hitting_set.empty_intersection(*lm) ) return false;
        }
    }
    return true;
}

int LandmarkDecomposition::solve(int type) {
    global_hitting_set_->clear();
    global_hitting_set_cost_ = 0;
    for( set<int>::const_iterator ri = roots_.begin(); ri != roots_.end(); ++ri ) {
        solve_bucket(*ri, type);
    }
    return global_hitting_set_cost_;
}

void LandmarkDecomposition::solve_bucket(int bucket, int type) {
    assert(hitting_sets_[bucket].empty());
    assert(hitting_set_costs_[bucket] == 0);
    if( (type == OPTIMAL) || ((type == DEFAULT) && optimal_) ) {
        hitting_set_costs_[bucket] =
          HittingSets::solve(rproblem_, F_[bucket].first,
                             F_[bucket].second, hitting_sets_[bucket]);
    } else {
        hitting_set_costs_[bucket] =
          HittingSets::chvatal_algorithm(rproblem_, F_[bucket].first,
                                         F_[bucket].second, hitting_sets_[bucket]);
    }
    global_hitting_set_->insert(hitting_sets_[bucket]);
    global_hitting_set_cost_ += hitting_set_costs_[bucket];
}

void LandmarkDecomposition::dump_partition(ostream &os) const {
    vector<vector<int> > table = vector<vector<int> >(num_operators_, vector<int>());
    for( int i = 0; i < num_operators_; ++i ) {
        int r = Find(i);
        table[r].push_back(i);
    }
    os << "[";
    for( int i = 0; i < num_operators_; ++i ) {
        if( !table[i].empty() ) {
            os << "{";
            for( int j = 0, jsz = table[i].size(); j < jsz; ++j ) {
                os << table[i][j] << ",";
            }
            os << "},";
        }
    }
    os << "]";
}

void LandmarkDecomposition::dump_landmarks(ostream &os, int indent) const {
    os << setw(indent) << "" << "roots={";
    for( set<int>::const_iterator ri = roots_.begin(); ri != roots_.end(); ++ri )
        os << *ri << ",";
    os << "}" << endl;

    for( set<int>::const_iterator ri = roots_.begin(); ri != roots_.end(); ++ri )
        dump_landmarks_in_bucket(os, indent, *ri);

    for( int i = 0; i < num_operators_; ++i ) {
        if( (roots_.find(i) == roots_.end()) && !hitting_sets_[i].empty() ) {
            os << "Error in bucket=" << i << ": hs=" << hitting_sets_[i] << endl;
        }
        assert((roots_.find(i) != roots_.end()) || hitting_sets_[i].empty());
    }
}

void LandmarkDecomposition::dump_landmarks_in_bucket(ostream &os, int indent, int bucket) const {
    os << setw(indent) << "" << "[" << bucket << "]={";
    for( const Landmark *lm = F_[bucket].second; lm != 0; lm = lm->next_ )
        os << *lm << ",";
    os << "}, width=" << F_[bucket].first
       << ", hitting_set=" << hitting_sets_[bucket]
       << ", cost=" << hitting_set_costs_[bucket]
       << endl;
}

} // end of namespace

