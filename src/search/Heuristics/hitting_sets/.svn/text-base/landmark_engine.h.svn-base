#ifndef LANDMARK_ENGINE_H
#define LANDMARK_ENGINE_H

#include "landmark.h"
#include "landmark_decomposition.h"

#include <iostream>
#include <vector>

namespace HittingSets {

class LandmarkEngine {
  protected:
    const Relaxed::Problem &rproblem_;
    int suboptimal_algorithm_;

    LandmarkDecomposition included_;   // stores included landmarks (solved optimally)
    LandmarkDecomposition excluded_;   // stores excluded landmarks (solved sub-optimally)
    int num_excluded_landmarks_;

    Relaxed::OperatorSet *zero_cost_operators_;
    Relaxed::OperatorSet *optimal_hitting_set_;
    Relaxed::OperatorSet *suboptimal_hitting_set_;

  public:
    enum { CHVATAL_ALGORITHM = 0, ONE_ACTION = 1, ALL_ACTIONS = 2 };
    enum { INC = 0, EXC = 1 };

    LandmarkEngine(const Relaxed::Problem &rproblem,
                   int subopt = CHVATAL_ALGORITHM,
                   bool included_opt = true,
                   bool excluded_opt = false)
      : rproblem_(rproblem),
        suboptimal_algorithm_(subopt),
        included_(rproblem, included_opt),
        excluded_(rproblem, excluded_opt) {
    }
    virtual ~LandmarkEngine() { }

    void initialize();
    void prepare_computation();
    void remove_landmarks();

    int solve(int fragment = 0, int type = 0) {
        if( fragment == 0 ) {
            included_.clear_hitting_sets();
            return included_.solve(type);
        } else {
            excluded_.clear_hitting_sets();
            return excluded_.solve(type);
        }
    }

    const Relaxed::OperatorSet& zero_cost_operators() const {
        return *zero_cost_operators_;
    }

    int width(int i = 0) const {
        return i == 0 ? included_.width_ : excluded_.width_;
    }
    const Relaxed::OperatorSet& hitting_set(int i = 0) const {
        return i == 0 ? *included_.global_hitting_set_ : *excluded_.global_hitting_set_;
    }
    int cost(int i = 0) const {
        return i == 0 ? included_.global_hitting_set_cost_ : excluded_.global_hitting_set_cost_;
    }

    const Relaxed::OperatorSet& optimal_hitting_set() const {
        return *optimal_hitting_set_;
    }
    int optimal_cost() const { return included_.global_hitting_set_cost_; }

    const Relaxed::OperatorSet& suboptimal_hitting_set() const {
        return *suboptimal_hitting_set_;
    }
    int suboptimal_cost() const { return excluded_.global_hitting_set_cost_; }

    Landmark* get_landmark(const State &state,
                           const Relaxed::OperatorSet &actions,
                           const std::vector<int> &h_max_cost) const;
    void add_landmark(const Landmark *lm, int width_bound, bool force, bool do_exclude);
    void exclude_landmark(const Landmark *L);

    void delete_landmarks(int bucket, const Landmark *landmarks, bool solve, bool do_exclude);
    void remove_landmarks_until_acceptable_width(int width_bound);


    void dump_landmarks(std::ostream &os, int indent) const;
};

int solve(const Relaxed::Problem &rproblem,
          int num_landmarks,
          const Landmark *landmarks,
          Relaxed::OperatorSet &hitting_set);

int chvatal_algorithm(const Relaxed::Problem &rproblem,
                      int num_landmarks,
                      const Landmark *landmarks,
                      Relaxed::OperatorSet &hitting_set);

} // end of namespace

#endif

