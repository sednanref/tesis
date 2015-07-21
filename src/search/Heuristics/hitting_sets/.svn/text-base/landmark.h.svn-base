#ifndef LANDMARK_H
#define LANDMARK_H

#include "relaxed.h"

#include <iostream>

namespace HittingSets {

// Landmarks are subsets of relaxed operators. For efficiency, the engine
// maintains a pool of discarded landmarks for reuse.
struct Landmark : public Relaxed::OperatorSet {
    mutable Landmark *next_; // pointer to next landmark in the pool.

    Landmark() : next_(0) { }
    Landmark(const Relaxed::OperatorSet &ros) : next_(0) { *this = ros; }
    ~Landmark() { }

    const Landmark& operator=(const Relaxed::OperatorSet &ros) {
        *static_cast<Relaxed::OperatorSet*>(this) = ros;
        return *this;
    }
    void print(std::ostream &os) const {
        os << "[ cutset=" << *static_cast<const Relaxed::OperatorSet*>(this) << " ]";
    }

    // Implements allocation and deallocation from the pool.
    static Landmark* pool_;
    static Landmark* allocate() {
        Landmark *lm = 0;
        if( pool_ != 0 ) {
            lm = pool_;
	    pool_ = pool_->next_;
	}
	else
            lm = new Landmark;
	lm->clear();
	return lm;
    }
    static void deallocate(const Landmark *lm) {
        lm->next_ = pool_;
	pool_ = const_cast<Landmark*>(lm);
    }
    static void deallocate_chain(const Landmark *lm) {
        while( lm != 0 ) {
            const Landmark *next_lm = lm->next_;
            Landmark::deallocate(lm);
            lm = next_lm;
        }
    }
};

} // end of namespace

#endif

