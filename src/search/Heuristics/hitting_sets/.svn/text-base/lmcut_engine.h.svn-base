#ifndef LMCUT_LANDMARKS_H
#define LMCUT_LANDMARKS_H

#include "relaxed.h"
#include "landmark_engine.h"
#include "../../priority_queue.h"

#include <cassert>
#include <vector>
#include <queue>
#include <set>

namespace HittingSets {

struct LMCutEngine {
    const Relaxed::Problem &rproblem_;
    int max_num_passes_;
    short unsigned *seeds_;

    std::vector<int> h_max_cost_;
    bool computed_h_max_costs_;
    int value_;
    int max_value_;
    std::vector<std::pair<int, const Landmark*> > passes_;

    bool store_landmarks_;

    LMCutEngine(const Relaxed::Problem &rproblem)
      : rproblem_(rproblem), max_num_passes_(0), seeds_(0) {
        h_max_cost_ = std::vector<int>(rproblem_.num_propositions_, 0);
    }
    virtual ~LMCutEngine() {
        delete[] seeds_;
    }

    void initialize(int num_passes, bool store_landmarks = true);
    void setup_exploration_queue(bool clear_exclude_set, int pass);
    void setup_exploration_queue_state(const State &state, int pass);
    void first_exploration(const State &state, int pass);
    void first_exploration_incremental(std::vector<int> &cut, int pass);
    int second_exploration(const State &state,
                           std::vector<const Relaxed::Proposition*> &second_exploration_queue,
                           std::vector<int> &cut,
                           int pass);
    void mark_goal_plateau(const Relaxed::Proposition *subgoal, int pass);
    std::pair<int, const Landmark*> one_pass(const State &state, int pass);
    void compute_landmarks(const State &state, int num_passes);

    // Exploration queue for LM-cut
    AdaptiveQueue<const Relaxed::Proposition*> priority_queue_;

    void enqueue_if_necessary(const Relaxed::Proposition *prop, int cost) {
        assert(cost >= 0);
        if( (prop->status_ == Relaxed::UNREACHED) || (prop->h_max_cost_ > cost) ) {
            prop->status_ = Relaxed::REACHED;
            prop->h_max_cost_ = cost;
            priority_queue_.push(cost, prop);
        }
    }
};

} // end of namespace

#endif

