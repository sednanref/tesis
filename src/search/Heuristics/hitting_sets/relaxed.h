#ifndef RELAXED_H
#define RELAXED_H

#include "bitmap_set.h"

#include <iostream>
#include <vector>
#include <limits>
#include <strings.h>

class Operator;
class State;

// This is an abstract framwork that should be specialized in order to
// implement hitting-sets based heuristics.

namespace Relaxed {

class Proposition;
class Operator;

enum PropositionStatus {
    UNREACHED = 0,
    REACHED = 1,
    GOAL_ZONE = 2,
    BEFORE_GOAL_ZONE = 3
};

const int COST_MULTIPLIER = 1;
// Choose 1 for maximum speed, larger values for possibly better
// heuristic accuracy. Heuristic computation time should increase
// roughly linearly with the multiplier.

// A relaxed operator only has positive effects, it references the real
// operator that is relaxed, and contains additional information.
struct Operator {
    const ::Operator *op_;
    std::vector<Proposition*> precondition_;
    std::vector<Proposition*> effects_;
    int base_cost_; // 0 for axioms, 1 for regular operators

    mutable int cost_; // it is base cost but gets updated by different procedures
    mutable int unsatisfied_preconditions_;
    mutable int h_max_supporter_cost_; // h_max_cost of h_max_supporter
    mutable const Proposition *h_max_supporter_;

    Operator(const std::vector<Proposition*> &pre,
             const std::vector<Proposition*> &eff,
             const ::Operator *op, int base_cost)
      : op_(op), precondition_(pre), effects_(eff), base_cost_(base_cost) {
    }

    inline void update_h_max_supporter() const;
};

// A relaxed proposition has an index and refer to an atom of the
// form Var = Val. When h_max values are computed, each relaxed 
// propositionis assigned an h_max_cost.
struct Proposition {
    int index_, var_, val_;
    std::vector<int> precondition_of_;
    std::vector<int> effect_of_;

    mutable PropositionStatus status_;
    mutable int h_max_cost_;
    mutable bool in_excluded_set_;

    Proposition(int index = -1, int var = -1, int val = -1)
      : index_(index), var_(var), val_(val) {
    }
};

// Implements a subset of relaxed operators.  Used for different
// purposes including landmarks.
struct OperatorSet : public Utils::BitmapSet {
    unsigned cost_;

    OperatorSet() : Utils::BitmapSet() {
        cost_ = std::numeric_limits<unsigned>::max();
    }
    OperatorSet(const OperatorSet &ros) : Utils::BitmapSet(ros) {
        cost_ = ros.cost_;
    }
    ~OperatorSet() { }

    void clear() {
        Utils::BitmapSet::clear();
        cost_ = std::numeric_limits<unsigned>::max();
    }
    bool empty() const { return Utils::BitmapSet::empty(); }

    void insert(int index, unsigned cost = 1) {
        Utils::BitmapSet::insert(index);
        cost_ = std::min(cost_, cost);
    }
    void insert(const OperatorSet &ros) {
        static_cast<Utils::BitmapSet*>(this)->insert(ros);
        cost_ = std::min(cost_, ros.cost_);
    }

    const OperatorSet& operator=(const OperatorSet &ros) {
        *static_cast<Utils::BitmapSet*>(this) = ros;
        cost_ = ros.cost_;
        return *this;
    }

    void print(std::ostream &os) const {
        static_cast<const Utils::BitmapSet*>(this)->print(os);
        os << ":" << cost_;
    }
};

struct Problem {
    int num_propositions_;
    std::vector<Operator> operators_;
    std::vector<std::vector<Proposition> > propositions_;
    Proposition artificial_precondition_;
    Proposition artificial_goal_;
    int index_artificial_goal_operator_;

    Problem() : num_propositions_(0), index_artificial_goal_operator_(-1) { }
    ~Problem() { }

    void initialize();
    void build_relaxed_operator(const ::Operator &op);
    void add_relaxed_operator(const std::vector<Proposition*> &precondition, const std::vector<Proposition*> &effects, const ::Operator *op, int base_cost);
};

inline void Operator::update_h_max_supporter() const {
    assert(!unsatisfied_preconditions_);
    for( int i = 0; i < precondition_.size(); ++i ) {
        if( (precondition_[i]->h_max_cost_ > h_max_supporter_->h_max_cost_) ||
            (false && (precondition_[i]->h_max_cost_ == h_max_supporter_->h_max_cost_) &&
             (precondition_[i]->effect_of_.size() < h_max_supporter_->effect_of_.size())) ) {
            h_max_supporter_ = precondition_[i];
        }
    }
    h_max_supporter_cost_ = h_max_supporter_->h_max_cost_;
}

} // end of namespace

inline std::ostream& operator<<(std::ostream &os, const Relaxed::OperatorSet::const_iterator &ci) {
    ci.print(os);
    return os;
}

inline std::ostream& operator<<(std::ostream &os, const Relaxed::OperatorSet &ros) {
    ros.print(os);
    return os;
}

#endif

