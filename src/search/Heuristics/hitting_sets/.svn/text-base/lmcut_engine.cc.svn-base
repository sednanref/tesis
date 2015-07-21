#include "lmcut_engine.h"
#include "../../state.h"
#include "../../operator.h"

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <vector>
#include <limits>

using namespace std;

//#define DEBUG

namespace HittingSets {

void LMCutEngine::initialize(int max_num_passes, bool store_landmarks) {
    if( max_num_passes > max_num_passes_ ) {
        max_num_passes_ = max_num_passes;
        delete[] seeds_;
        seeds_ = new short unsigned[3*max_num_passes_];
        for( int i = 0; i < 3*max_num_passes_; ++i )
            seeds_[i] = (short unsigned)lrand48();
    }
    store_landmarks_ = store_landmarks;
}

//void LMCutEngine::setup_exploration_queue(bool clear_exclude_set, int) {
void LMCutEngine::setup_exploration_queue(bool , int) {
    priority_queue_.clear();

    for( int var = 0; var < rproblem_.propositions_.size(); ++var ) {
        for( int value = 0; value < rproblem_.propositions_[var].size(); ++value ) {
            const Relaxed::Proposition &prop = rproblem_.propositions_[var][value];
            prop.status_ = Relaxed::UNREACHED;
        }
    }

    rproblem_.artificial_goal_.status_ = Relaxed::UNREACHED;
    rproblem_.artificial_precondition_.status_ = Relaxed::UNREACHED;

    for( int i = 0; i < rproblem_.operators_.size(); ++i ) {
        const Relaxed::Operator &rop = rproblem_.operators_[i];
        rop.unsatisfied_preconditions_ = rop.precondition_.size();
        rop.h_max_supporter_ = 0;
        rop.h_max_supporter_cost_ = numeric_limits<int>::max();
    }
}

void LMCutEngine::setup_exploration_queue_state(const State &state, int) {
    for( int var = 0; var < rproblem_.propositions_.size(); ++var ) {
        const Relaxed::Proposition *init_rp = &rproblem_.propositions_[var][state[var]];
        enqueue_if_necessary(init_rp, 0);
    }
    enqueue_if_necessary(&rproblem_.artificial_precondition_, 0);
}

void LMCutEngine::first_exploration(const State &state, int pass) {
    assert(priority_queue_.empty());
    setup_exploration_queue(true, pass);
    setup_exploration_queue_state(state, pass);
    while( !priority_queue_.empty() ) {
        pair<int, const Relaxed::Proposition*> top_pair = priority_queue_.pop();
        int popped_cost = top_pair.first;
        const Relaxed::Proposition *prop = top_pair.second;
        int prop_cost = prop->h_max_cost_;
        assert(prop_cost <= popped_cost);
        if( prop_cost < popped_cost ) continue;
        const vector<int> &triggered_operators = prop->precondition_of_;
        for( int i = 0; i < triggered_operators.size(); ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[triggered_operators[i]];
            rop.unsatisfied_preconditions_--;
            assert(rop.unsatisfied_preconditions_ >= 0);
            if( rop.unsatisfied_preconditions_ == 0 ) {
                rop.h_max_supporter_ = prop;
                rop.h_max_supporter_cost_ = prop_cost;
                int target_cost = prop_cost + rop.cost_;
                for( int j = 0; j < rop.effects_.size(); ++j ) {
                    Relaxed::Proposition *effect = rop.effects_[j];
                    enqueue_if_necessary(effect, target_cost);
                }
            }
        }
    }
}

void LMCutEngine::first_exploration_incremental(vector<int> &cut, int) {
    assert(priority_queue_.empty());
    /* We pretend that this queue has had as many pushes already as we
       have propositions to avoid switching from bucket-based to
       heap-based too aggressively. This should prevent ever switching
       to heap-based in problems where action costs are at most 1.
    */
    priority_queue_.add_virtual_pushes(rproblem_.num_propositions_);
    for( size_t i = 0, isz = cut.size(); i < isz; ++i ) {
        const Relaxed::Operator &rop = rproblem_.operators_[cut[i]];
        int cost = rop.h_max_supporter_cost_ + rop.cost_;
        for( int j = 0; j < rop.effects_.size(); ++j ) {
            const Relaxed::Proposition *effect = rop.effects_[j];
            enqueue_if_necessary(effect, cost);
        }
    }

    while( !priority_queue_.empty() ) {
        pair<int, const Relaxed::Proposition*> top_pair = priority_queue_.pop();
        int popped_cost = top_pair.first;
        const Relaxed::Proposition *prop = top_pair.second;
        int prop_cost = prop->h_max_cost_;
        assert(prop_cost <= popped_cost);
        if( prop_cost < popped_cost ) continue;
        const vector<int> &triggered_operators = prop->precondition_of_;
        for( int i = 0; i < triggered_operators.size(); ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[triggered_operators[i]];
            if( rop.h_max_supporter_ == prop) {
                int old_supp_cost = rop.h_max_supporter_cost_;
                if( old_supp_cost > prop_cost ) {
                    rop.update_h_max_supporter();
                    int new_supp_cost = rop.h_max_supporter_cost_;
                    if( new_supp_cost != old_supp_cost ) {
                        // This operator has become cheaper.
                        assert(new_supp_cost < old_supp_cost);
                        int target_cost = new_supp_cost + rop.cost_;
                        for( int j = 0; j < rop.effects_.size(); ++j ) {
                            const Relaxed::Proposition *effect = rop.effects_[j];
                            enqueue_if_necessary(effect, target_cost);
                        }
                    }
                }
            }
        }
    }
}

int LMCutEngine::second_exploration(const State &state,
                                    vector<const Relaxed::Proposition*> &second_exploration_queue,
                                    vector<int> &cut,
                                    int) {
    assert(second_exploration_queue.empty());
    assert(cut.empty());

    rproblem_.artificial_precondition_.status_ = Relaxed::BEFORE_GOAL_ZONE;
    second_exploration_queue.push_back(&rproblem_.artificial_precondition_);

    for( int var = 0; var < rproblem_.propositions_.size(); ++var ) {
        const Relaxed::Proposition *init_prop = &rproblem_.propositions_[var][state[var]];
        init_prop->status_ = Relaxed::BEFORE_GOAL_ZONE;
        second_exploration_queue.push_back(init_prop);
    }

    int cut_cost = numeric_limits<int>::max();
    while( !second_exploration_queue.empty() ) {
        const Relaxed::Proposition *prop = second_exploration_queue.back();
        second_exploration_queue.pop_back();
        const vector<int> &triggered_operators = prop->precondition_of_;
        for( int i = 0; i < triggered_operators.size(); ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[triggered_operators[i]];
            if( rop.h_max_supporter_ == prop ) {
                bool reached_goal_zone = false;
                for( int j = 0; j < rop.effects_.size(); ++j ) {
                    const Relaxed::Proposition *effect = rop.effects_[j];
                    if( effect->status_ == Relaxed::GOAL_ZONE ) {
                        assert(rop.cost_ > 0);
                        reached_goal_zone = true;
                        assert(rop.cost_ > 0);
                        cut_cost = min(rop.cost_, cut_cost);
                        cut.push_back(triggered_operators[i]);
                        break;
                    }
                }
                if( !reached_goal_zone ) {
                    for( int j = 0; j < rop.effects_.size(); ++j ) {
                        const Relaxed::Proposition *effect = rop.effects_[j];
                        if( effect->status_ != Relaxed::BEFORE_GOAL_ZONE ) {
                            assert(effect->status_ == Relaxed::REACHED);
                            effect->status_ = Relaxed::BEFORE_GOAL_ZONE;
                            second_exploration_queue.push_back(effect);
                        }
                    }
                }
            }
        }
    }
    return cut_cost;
}

#if 0
void LMCutEngine::relaxed_exploration(int pass) {
    // set random seed for this pass. The important thing is that
    // the two relaxed explorations for the same cut have the same
    // seed so that the propositions extracted from the queue are 
    // the same.
    seed48(&seeds_[3*pass]);

    // do the exploration
    while( !used_buckets_.empty() ) {
        int bucket_no = -used_buckets_.top();
        used_buckets_.pop();
        for(;;) {
            Bucket &bucket = reachable_queue_[bucket_no];
            // NOTE: Cannot set "bucket" outside the loop because the
            //       reference can change if reachable_queue is
            //       resized.
            if(bucket.empty())
                break;

            // Random shuffle of the queue (bucket).
            const Relaxed::Proposition *prop = 0;
            if( pass == 0 )
                prop = bucket.back();
            else if( pass == 1 ) {
                prop = bucket[0];
                bucket[0] = bucket.back();
            } else {
                int i = lrand48() % bucket.size();
                prop = bucket[i];
                bucket[i] = bucket.back();
            }
            bucket.pop_back();

            int prop_cost = prop->h_max_cost_;
            assert(prop_cost <= bucket_no);
            if(prop_cost < bucket_no) continue;

            const vector<int> &triggered_operators = prop->precondition_of_;
            for(int i = 0, isz = triggered_operators.size(); i < isz; i++) {
                const Relaxed::Operator &rop = rproblem_.operators_[triggered_operators[i]];
                rop.unsatisfied_preconditions_--;
                assert(rop.unsatisfied_preconditions_ >= 0);

                // If all preconditions are satisfied, insert effects into queue.
                if(rop.unsatisfied_preconditions_ == 0) {
                    rop.h_max_supporter_ = prop;

                    // Compute costs for effects.
                    int target_cost = prop_cost + rop.cost_;

                    // Insert effects into queue.
                    for(int j = 0, jsz = rop.effects_.size(); j < jsz; j++) {
                        Relaxed::Proposition *effect = rop.effects_[j];
                        if( effect->in_excluded_set_ ) {
                            assert(rop.cost_ > 0);
                            cut_cost_ = min(rop.cost_, cut_cost_);
                            cut_->insert(triggered_operators[i], rproblem_.operators_[triggered_operators[i]].base_cost_);
                            break;
                        } else {
                            enqueue_if_necessary(effect, target_cost);
                        }
                    }
                }
            }
        }
    }
}
#endif

void LMCutEngine::mark_goal_plateau(const Relaxed::Proposition *subgoal, int pass) {
    // NOTE: subgoal can be null if we got here via recursion through
    // a zero-cost action that is relaxed unreachable. (This can only
    // happen in domains which have zero-cost actions to start with.)
    // For example, this happens in pegsol-strips #01.
    if( subgoal && (subgoal->status_ != Relaxed::GOAL_ZONE) ) {
#ifdef DEBUG
        cout << subgoal->index_ << ",";
#endif
        subgoal->status_ = Relaxed::GOAL_ZONE;
        const vector<int> &effect_of = subgoal->effect_of_;
        for( int i = 0; i < effect_of.size(); ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[effect_of[i]];
            if( rop.cost_ == 0 ) {
                mark_goal_plateau(rop.h_max_supporter_, pass);
            }
        }
    }
}

pair<int, const Landmark*> LMCutEngine::one_pass(const State &state, int pass) {
    assert(pass < max_num_passes_);

    // Initialize operator costs with their base costs.
    for( int i = 0, isz = rproblem_.operators_.size(); i < isz; ++i ) {
        const Relaxed::Operator &rop = rproblem_.operators_[i];
        rop.cost_ = rop.base_cost_ * Relaxed::COST_MULTIPLIER;
    }

    int lm_cut_value = 0;
    Landmark* landmarks = 0;

    vector<int> cut;
    vector<const Relaxed::Proposition*> second_exploration_queue;

    first_exploration(state, pass);
    if( rproblem_.artificial_goal_.status_ == Relaxed::UNREACHED) {
#ifdef DEBUG
        cout << "DEAD-END" << endl;
#endif
        return make_pair(numeric_limits<int>::max(), (Landmark*)0);
    }

    int num_iterations = 0;
    while( rproblem_.artificial_goal_.h_max_cost_ != 0) {
        ++num_iterations;

        // Compute V* zone (fluents from which goal can be reached thru a zero-cost path).
#ifdef DEBUG
        cout << "  V*_zone={";
#endif
        mark_goal_plateau(&rproblem_.artificial_goal_, pass);
#ifdef DEBUG
        cout << "}" << endl;
#endif

        // Perform second exploration to identify V0 and V- zones, and 
        // construct the LM-cut cut.
        int cut_cost = second_exploration(state, second_exploration_queue, cut, pass);
        assert(!cut.empty());

#ifdef DEBUG
        cout << "  cut={";
        for( size_t i = 0, isz = cut.size(); i < isz; ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[cut[i]];
            cout << cut[i];
            if( rop.op_ != 0 ) cout << ".(" << rop.op_->get_name() << ")";
            cout << ",";
        }
        cout << "}" << endl;
#endif

        // Add landmark to the list of landmarks, reduce operator costs, and update lm_cut value
        if( store_landmarks_ ) {
            Landmark *lm = Landmark::allocate();
            lm->next_ = landmarks;
            landmarks = lm;
        }

        for( size_t i = 0, isz = cut.size(); i < isz; ++i ) {
            const Relaxed::Operator &rop = rproblem_.operators_[cut[i]];
            if( store_landmarks_ ) landmarks->insert(cut[i], rop.cost_);
            rop.cost_ -= cut_cost;
            assert(rop.cost_ >= 0);
        }

        lm_cut_value += cut_cost;

#if 0
        int cut_cost = numeric_limits<int>::max();
        for( int i = 0; i < cut.size(); ++i ) {
            cut_cost = min(cut_cost, cut[i]->cost_);
            if( Relaxed::COST_MULTIPLIER > 1 ) {
                /* We're using this "if" here because COST_MULTIPLIER
                   is currently a global constant and usually 1, which
                   allows the optimizer to get rid of this additional
                   minimization (which is always correct, but not
                   necessary if COST_MULTIPLIER == 1.

                   If COST_MULTIPLIER turns into an option, this code
                   should be changed. I would assume that the savings
                   by the "if" are negligible anyway, but this should
                   be tested.

                   The whole cut cost computation could also be made
                   more efficient in the unit-cost case, where all
                   cuts have cost 1 and the cost decrement could be
                   moved directly to the place where the actions for
                   the cut are collected; indeed, we would not need to
                   collect the cut in a vector at all. But again, I
                   doubt this would have a huge impact, and it would
                   only be applicable in the unit-cost (or zero- and
                   unit-cost) case.
                */
                cut_cost = min(cut_cost, cut[i]->base_cost_);
            }
        }
#endif

        // prepare next iteration
        first_exploration_incremental(cut, pass);
        cut.clear();

        for( int var = 0; var < rproblem_.propositions_.size(); ++var ) {
            for( int value = 0; value < rproblem_.propositions_[var].size(); ++value ) {
                const Relaxed::Proposition &prop = rproblem_.propositions_[var][value];
                if( (prop.status_ == Relaxed::GOAL_ZONE) || (prop.status_ == Relaxed::BEFORE_GOAL_ZONE) )
                    prop.status_ = Relaxed::REACHED;
            }
        }
        rproblem_.artificial_goal_.status_ = Relaxed::REACHED;
        rproblem_.artificial_precondition_.status_ = Relaxed::REACHED;
    }

    return make_pair(lm_cut_value, landmarks);
}

void LMCutEngine::compute_landmarks(const State &state, int num_passes) {
    assert(num_passes <= max_num_passes_);
    h_max_cost_ = vector<int>(rproblem_.num_propositions_, 0);
    computed_h_max_costs_ = false;
    passes_.reserve(num_passes);
    passes_.clear();

    value_ = 0;
    max_value_ = 0;
    for( int pass = 0; pass < num_passes; ++pass ) {
        pair<int, const Landmark*> p = one_pass(state, pass);
        if( pass == 0 ) value_ = p.first;
        max_value_ = max(max_value_, p.first);
        passes_.push_back(p);
        if( p.first == numeric_limits<int>::max() ) break;
    }
}

} // end of namespace

