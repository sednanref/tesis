#include "landmark_engine.h"
#include "../utils/graph.h"
#include "../../globals.h"
#include "../../state.h"
#include "hypergraph.h"

#include <iomanip>
#include <queue>
#include <algorithm>

using namespace std;

//#define DEBUG
//#define DBL_CHECK

namespace HittingSets {

void LandmarkEngine::initialize() {
    cout << "Initializing landmark engine..." << endl;

    included_.initialize();
    excluded_.initialize();

    optimal_hitting_set_ = included_.global_hitting_set_;
    suboptimal_hitting_set_ = excluded_.global_hitting_set_;
    zero_cost_operators_ = new Relaxed::OperatorSet;

    num_excluded_landmarks_ = 0;

    // Fill in zero-cost operators
    for( int i = 0; i < rproblem_.operators_.size(); ++i ) {
        if( rproblem_.operators_[i].base_cost_ == 0 )
            zero_cost_operators_->insert(i);
    }
}

void LandmarkEngine::prepare_computation() {
    included_.prepare_computation();
    excluded_.prepare_computation();
    assert(num_excluded_landmarks_ == 0);
}

void LandmarkEngine::remove_landmarks() {
    included_.remove_landmarks();
    excluded_.remove_landmarks();
    num_excluded_landmarks_ = 0;
}

Landmark* LandmarkEngine::get_landmark(const State &state,
                                       const Relaxed::OperatorSet &actions,
                                       const vector<int> &h_max_cost) const {

    // Compute the set of reachable fluents from state using actions.
    vector<bool> reachable_fluents(rproblem_.num_propositions_, false);

    // Initialize queue of reached propositions.
    static deque<const Relaxed::Proposition*> q;
    for( int var = 0; var < rproblem_.propositions_.size(); ++var ) {
        const Relaxed::Proposition *rp = &rproblem_.propositions_[var][state[var]];
        reachable_fluents[rp->index_] = true;
        q.push_back(rp);
    }
    reachable_fluents[rproblem_.artificial_precondition_.index_] = true;
    q.push_back(&rproblem_.artificial_precondition_);

    for( int i = 0, isz = rproblem_.operators_.size(); i < isz; ++i ) {
        const Relaxed::Operator &rop = rproblem_.operators_[i];
        rop.unsatisfied_preconditions_ = rop.precondition_.size();
    }

#ifdef DEBUG
    cout << "    Fired actions={";
#endif

    // Iterate until queue becomes empty. At each iteration, remove reachable
    // fluent and decrement count of unsatisfied preconditions for each operator
    // that has the fluent as precondition. When the count reaches zero, add 
    // the add effects to the queue.
    while( !q.empty() ) {
        const Relaxed::Proposition *rp = q.front();
        q.pop_front();
        for( int i = 0, isz = rp->precondition_of_.size(); i < isz; ++i ) {
            int action = rp->precondition_of_[i];
            if( actions.contains(action) || zero_cost_operators_->contains(action) ) {
                const Relaxed::Operator &rop = rproblem_.operators_[action];
                assert(rop.unsatisfied_preconditions_ > 0);
                if( --rop.unsatisfied_preconditions_ == 0 ) {
#ifdef DEBUG
                    cout << action << ",";
#endif
                    for( int j = 0, jsz = rop.effects_.size(); j < jsz; ++j ) {
                        Relaxed::Proposition *eff = rop.effects_[j];
                        if( !reachable_fluents[eff->index_] ) {
                            reachable_fluents[eff->index_] = true;
                            q.push_back(eff);
                        }
                    }
                }
            }
        }
    }

#ifdef DEBUG
    cout << "}" << endl;
    cout << "    Reachable fluents={";
    for( int i = 0; i < rproblem_.num_propositions_; ++i )
        if( reachable_fluents[i] )
            cout << i << ",";
    cout << "}" << endl;
#endif

    // Check whether the reachable fluents contain goal. If so, terminate.
    if( reachable_fluents[rproblem_.artificial_goal_.index_] )
        return 0;

    // Compute the pcf D for this hitting set that will lead to a new landmark as
    // shown in the paper of ICAPS 2012. Concurrently, calculate G(D) and its reduction.
    int nodes = rproblem_.num_propositions_ + 1;
    int source = nodes - 1, target = rproblem_.artificial_goal_.index_;
    static Digraph::Directed justification_graph(nodes, source, target);
    justification_graph.clear();
    for( int i = 0, isz = rproblem_.operators_.size(); i < isz; ++i ) {
        const Relaxed::Operator &rop = rproblem_.operators_[i];
        if( rop.unsatisfied_preconditions_ == 0 ) continue;

        // Select an unreachable precondition of the operator (if any) as supporter.
        Relaxed::Proposition *sup = 0;
        static vector<Relaxed::Proposition*> supporters;
        int best_supporter_cost = 0;
        bool no_supporter = true, unreachable_precondition = false;
        supporters.clear();
        for( int j = 0, jsz = rop.precondition_.size(); j < jsz; ++j ) {
            Relaxed::Proposition *rp = rop.precondition_[j];
            if( h_max_cost[rp->index_] == -1 ) {
                unreachable_precondition = true;
                break;
            } else if( !reachable_fluents[rp->index_] ) {
                // NOTE: I'm not clear whether the best supporter should be one
                // with min or max h-max value.
                if( no_supporter || (h_max_cost[rp->index_] >= best_supporter_cost) ) {
                    if( no_supporter || (h_max_cost[rp->index_] > best_supporter_cost) ) {
                        supporters.clear();
                        best_supporter_cost = h_max_cost[rp->index_];
                        no_supporter = false;
                    }
                    supporters.push_back(rp);
                } 
                assert(!supporters.empty());
            }
        }
        if( unreachable_precondition ) continue;
        if( !supporters.empty() ) sup = supporters.front();

        // Add the edges induced by the operator. Each edge goes from the
        // supporter (chosen precondition) to an effect. If the supporter is
        // reachable from source, the edge initiates at the source. If the
        // effect is reachable from the source, the edge is discarded as it
        // wouldn't be in the cutset.
        int u = sup == 0 ? source : sup->index_;
        for( int j = 0, jsz = rop.effects_.size(); j < jsz; ++j ) {
            Relaxed::Proposition *eff = rop.effects_[j];
            if( reachable_fluents[eff->index_] ) continue;
            justification_graph.add_edge(u, eff->index_, i);
        }
    }

    // Simplify the justification graph trying to reduce the size of the cutset.
    // Compute nodes backward-reachable from target. These are the relevant nodes
    // for constructing the landmark.
    static vector<int> backward_reachable_from_target(nodes, 0);
    for( int i = 0; i < nodes; ++i ) backward_reachable_from_target[i] = 0;
    justification_graph.backward_reachability(target, backward_reachable_from_target);

    // Extract the landmark that correspond to the labels of the cutset for (R,R^c)
    // where R is the set of reachable fluents. The landmark does no need to contain
    // edges that land in nodes that cannot reach the target node.
    Landmark *new_landmark = Landmark::allocate();
    const vector<pair<int,int> > &out_list = justification_graph.out_list(source);
    for( int j = 0, jsz = out_list.size(); j < jsz; ++j ) {
        int node = out_list[j].first;
        assert(!reachable_fluents[node]);
        if(backward_reachable_from_target[node] == 1) {
            const Digraph::LabelList &labels = justification_graph.labels(out_list[j].second);
            for( Digraph::LabelList::const_iterator l = labels.begin(); l != labels.end(); ++l ) {
                new_landmark->insert(*l, rproblem_.operators_[*l].base_cost_);
            }
        }
    }

    // Return the landmark.
    return new_landmark;
}

void LandmarkEngine::add_landmark(const Landmark *L, int width_bound, bool force, bool do_exclude) {
    assert(L->cost_ > 0);

    // Add the landmark to the collection of landmarks and recompute the width.
    // First, check if this landmark is contained in another one.
    static set<int> roots;
    roots.clear();
    for( Landmark::const_iterator ai = L->begin(); ai != L->end(); ++ai ) {
        roots.insert(included_.Find(*ai));
    }

    bool some_landmark_removed = false;
    for( set<int>::const_iterator ri = roots.begin(); ri != roots.end(); ++ri ) {
        bool landmark_is_contained_in_another_landmark = false;
        int a = included_.Find(*ri), num_removed = 0;
        const Landmark *prev = 0, *lm = included_.F_[a].second, *removed = 0;
        while( lm != 0 ) {
            if( !do_exclude && L->contains(*lm) ) {
#ifdef DEBUG
                cout << " contains another landmark" << endl;
#endif
                Landmark::deallocate(L);
                return;
            } else if( lm->contains(*L) ) {
                landmark_is_contained_in_another_landmark = true;
                ++num_removed;
                if( prev == 0 ) {
                    included_.F_[a].second = lm->next_;
                    lm->next_ = const_cast<Landmark*>(removed);
                    removed = lm;
                    lm = included_.F_[a].second;
                } else {
                    prev->next_ = lm->next_;
                    lm->next_ = const_cast<Landmark*>(removed);
                    removed = lm;
                    lm = prev->next_;
                }
            } else {
                prev = lm;
                lm = lm->next_;
            }
        }

        // Update number of landmarks in bucket and re-compute width.
        if( num_removed > 0 ) {
            some_landmark_removed = true;
            included_.F_[a].first -= num_removed;
            delete_landmarks(a, removed, !force, false); // If force, don't solve buckets!
#ifdef DEBUG
            cout << "removed: " << num_removed << ", ";
#endif
        }

        // If the landmark is contained in another landmark, there is no
        // need to continue the loop because the landmark is independent 
        // of other buckets.
        if( landmark_is_contained_in_another_landmark ) break;
    }

    // Add the landmark if width is less than or equal to width-bound.
    int new_width = included_.Width(*L);
    if( force || some_landmark_removed || (new_width <= width_bound) ) {
#ifdef DEBUG
        int old_width = included_.width_;
#endif
        int bucket = included_.Add(L);
        if( !force ) included_.solve_bucket(bucket);
#ifdef DEBUG
        cout << "added: old_width=" << old_width
             << ", new_width=" << included_.width_
             << endl;
#endif
    } else {
        if( do_exclude ) {
            // Insert landmark into collection to excluded landmarks
            // and update suboptimal hitting set.
            exclude_landmark(L);
        } else {
#ifdef DEBUG
            cout << "deleting" << endl;
#endif
            Landmark::deallocate(L);
        }
    }
}

void LandmarkEngine::exclude_landmark(const Landmark *L) {
    ++num_excluded_landmarks_;
    if( suboptimal_algorithm_ == CHVATAL_ALGORITHM ) {
        int bucket = excluded_.Add(L);
        excluded_.solve_bucket(bucket);
    } else {
        if( suboptimal_algorithm_ == ONE_ACTION ) {
            suboptimal_hitting_set_->insert(*L->begin());
        } else {
            suboptimal_hitting_set_->insert(*L);
        }
        Landmark::deallocate(L);
    }
}

void LandmarkEngine::delete_landmarks(int bucket,
                                      const Landmark *landmarks,
                                      bool solve,
                                      bool do_exclude) {
    // Remove all the landmarks in landmarks which used to live in bucket.
    // Deleting landmarks from a bucket may partition the bucket into disjoints
    // subsets. Thus, we must recreate the union/find forest and repartition
    // the whole bucket.

    // Clear union/find forest for actions in deleted landmarks.
    // The forest will be reconstructed when repartitioning the bucket.
    const Landmark *next_lm = 0;
    for( const Landmark *lm = landmarks; lm != 0; lm = next_lm ) {
        next_lm = lm->next_;
        for( Landmark::const_iterator l = lm->begin(); l != lm->end(); ++l ) {
            included_.rank_[*l] = 0;
            included_.parent_[*l] = *l;
        }
        if( !do_exclude ) {
            Landmark::deallocate(lm);
        } else {
            lm->next_ = 0;
            exclude_landmark(lm);
        }
    }

    // Repartition landmarks in bucket and recompute width.
    included_.Repartition_bucket(bucket, solve);
}

typedef pair<const Landmark*, float> score_pair;
struct score_cmp {
    bool operator()(const score_pair &p1, const score_pair &p2) const {
        return (p1.second < p2.second) ||
               ((p1.second == p2.second) && (p1.first->size() < p2.first->size()));
    }
};

void LandmarkEngine::remove_landmarks_until_acceptable_width(int width_bound) {

#if 1
    while( included_.width_ > width_bound ) {
        for( set<int>::const_iterator ri = included_.roots_.begin(); ri != included_.roots_.end(); ++ri ) {
            if( included_.F_[*ri].first > width_bound ) {
                int num_landmarks = included_.F_[*ri].first;
                int num_landmarks_to_remove = num_landmarks - width_bound;

                // Compute (suboptimal) hitting set
                Relaxed::OperatorSet hitting_set;
                HittingSets::chvatal_algorithm(rproblem_, num_landmarks, included_.F_[*ri].second, hitting_set);

                // Compute landmark scores.
                vector<score_pair> scores;
                scores.reserve(included_.F_[*ri].first);
                for( const Landmark *lm = included_.F_[*ri].second; lm != 0; lm = lm->next_ ) {
                    float score = 0, num_hits = 0;
                    for( Relaxed::OperatorSet::const_iterator it = hitting_set.begin(); it != hitting_set.end(); ++it ) {
                        if( lm->contains(*it) ) {
                            ++num_hits;
                            score += rproblem_.operators_[*it].base_cost_;
                        }
                    }
                    scores.push_back(make_pair(lm, score / num_hits));
                }

                // Order scores in non-decreasing order and extract
                // landmarks to remove
                set<const Landmark*> to_remove;
                sort(scores.begin(), scores.end(), score_cmp());
#if 0
                cout << "sorted landmarks:" << endl;
                for( int i = 0; i < included_.F_[*ri].first; ++i )
                    cout << "  " << *scores[i].first << " w/ " << scores[i].second << endl;
                cout << endl;
#endif
                for( int i = 0; i < num_landmarks_to_remove; ++i )
                    to_remove.insert(scores[i].first);

                // Remove landmarks
                const Landmark *landmarks_to_remove = 0, *prev = 0;
                for( const Landmark *lm = included_.F_[*ri].second; lm != 0; ) {
                    if( to_remove.find(lm) != to_remove.end() ) {
                        --included_.F_[*ri].first;
                        const Landmark *next = lm->next_;
                        if( prev == 0 ) {
                            included_.F_[*ri].second = next;
                        } else {
                            prev->next_ = const_cast<Landmark*>(next);
                        }
                        lm->next_ = const_cast<Landmark*>(landmarks_to_remove);
                        landmarks_to_remove = lm;
                        lm = next;
                    } else {
                        prev = lm;
                        lm = lm->next_;
                    }
                }
                delete_landmarks(*ri, landmarks_to_remove, false, true);
            }
        }
    }
#endif

#if 0
    while( included_.width_ > width_bound ) {
        for( set<int>::const_iterator ri = included_.roots_.begin(); ri != included_.roots_.end(); ++ri ) {
            if( included_.F_[*ri].first > width_bound ) {
                // Search for a min-cost max-size landmark to remove.
                int min_cost = numeric_limits<unsigned>::max(), max_size = 0;
                const Landmark *prev = 0, *best = 0, *prev_best = 0;
                for( const Landmark *lm = included_.F_[*ri].second; lm != 0; lm = lm->next_ ) {
                    if( (lm->cost_ < min_cost) || ((lm->cost_ == min_cost) && (lm->size_ > max_size)) ) {
                        min_cost = lm->cost_;
                        max_size = lm->size_;
                        best = lm;
                        prev_best = prev;
                    }
                    prev = lm;
                }
                assert(best != 0);

                // Remove landmark from bucket and repartition.
                --included_.F_[*ri].first;
                if( prev_best == 0 )
                    included_.F_[*ri].second = best->next_;
                else
                    prev_best->next_ = best->next_;
                best->next_ = 0;
                delete_landmarks(*ri, best, false, true);
                break;
            }
        }
    }
#endif
}

void LandmarkEngine::dump_landmarks(ostream &os, int indent) const {
    included_.dump_landmarks(os, indent);
    os << setw(indent) << ""
       << "#excluded_landmarks=" << num_excluded_landmarks_ << endl;
    excluded_.dump_landmarks(os, indent);
}

int solve(const Relaxed::Problem &rproblem,
          int num_landmarks,
          const Landmark *landmarks,
          Relaxed::OperatorSet &hitting_set) {

    hitting_set.clear();
    if( num_landmarks == 0 ) {
        return 0;
    } else if( num_landmarks == 1 ) {
        int cost = landmarks->cost_;
        for( Landmark::const_iterator it = landmarks->begin(); it != landmarks->end(); ++it ) {
            if( rproblem.operators_[*it].base_cost_ == cost ) {
                hitting_set.insert(*it);
                break;
            }
        }
        return cost;
    } else {
        // Create hypergraph representation of for hitting-set problem.
        // A hypergraph is just a set of (hyper) edges. In this graph,
        // the vertices are the landmarks, and the edge labeled 'a' is
        // the set of all landmarks that contain a. We don't need to
        // consider multi-edges so at most one edge per each subset of
        // landmarks. Once the graph is created, a minimum hitting-set
        // is just a min cover of the hypergraph.
        //
        // An hyperedge is a subset of vertices that is represented with
        // an unsigned. Thus, the maximum number of vertices in a hypergraph
        // is 32. Additionally, each edge is represented as the complement
        // of the set for efficiency (see below).
        static set<int> actions;
        for( const Landmark *lm = landmarks; lm != 0; lm = lm->next_ ) {
            for( Landmark::const_iterator li = lm->begin(); li != lm->end(); ++li )
                actions.insert(*li);
        }

        static vector<unsigned> vec_compl_edges, vec_edge_costs, vec_actions;
        static vector<Hypergraph::Edge> vec_edges;

        bool constrained_solver = num_landmarks <= Hypergraph::MAX_VERTICES_CONSTRAINED;

        vec_compl_edges.reserve(actions.size());
        vec_edge_costs.reserve(actions.size());
        vec_actions.reserve(actions.size());
        vec_edges.reserve(actions.size());

        // Extract the hyperedges from the actions in the landmarks.
        int num_edges = 0;
        for( set<int>::const_iterator si = actions.begin(); si != actions.end(); ++si ) {
            Hypergraph::Edge edge;
            unsigned bitmap = 0, j = 0;
            for( const Landmark *lm = landmarks; lm != 0; lm = lm->next_, ++j ) {
                if( lm->contains(*si) ) {
                    if( constrained_solver ) {
                        bitmap += (1<<j);
#ifdef DBL_CHECK
                        edge.insert(j);
#endif
                    } else {
                        edge.insert(j);
                    }
                }
            }

            int cost = rproblem.operators_[*si].base_cost_;
            assert(cost > 0);

            // Look for an indentical edge in the current collection.
            int edge_index = 0;
            while( edge_index < num_edges ) {
                if( (constrained_solver && (vec_compl_edges[edge_index] == ~bitmap)) ||
                    (!constrained_solver && (vec_edges[edge_index] == edge)) )
                    break;
                ++edge_index;
            }


            // If found, update its costs. Otherwise, add the new edge.
            if( edge_index < num_edges ) {
                if( cost < vec_edge_costs[edge_index] ) {
                    vec_edge_costs[edge_index] = cost;
                    vec_actions[edge_index] = *si;
                }
            } else {
                if( constrained_solver ) {
                    vec_compl_edges.push_back(~bitmap);
#ifdef DBL_CHECK
                    vec_edges.push_back(edge);
#endif
                } else {
                    vec_edges.push_back(edge);
                }
                vec_edge_costs.push_back(cost);
                vec_actions.push_back(*si);
                ++num_edges;
            }
        }

        // Compute min-cost cover of the hypergraph.
        static vector<unsigned> cover;
        unsigned cover_cost;
        if( constrained_solver ) {
            if( g_max_action_cost > 1 ) {
                cover_cost = Hypergraph::min_cost_cover(num_landmarks,
                                                        vec_compl_edges,
                                                        vec_edge_costs,
                                                        cover);
#ifdef DBL_CHECK
                vector<unsigned> bk_cover;
                unsigned bk_cover_cost = 
                    Hypergraph::min_cost_cover_unconstrained(num_landmarks,
                                                             vec_edges,
                                                             vec_edge_costs,
                                                             bk_cover);
                assert(cover_cost == bk_cover_cost);
#endif
            } else {
                cover_cost = Hypergraph::min_cover(num_landmarks,
                                                   vec_compl_edges,
                                                   cover);
#ifdef DBL_CHECK
                vector<unsigned> bk_cover;
                unsigned bk_cover_cost = 
                    Hypergraph::min_cover_unconstrained(num_landmarks,
                                                        vec_edges,
                                                        bk_cover);
                assert(cover.size() == cover_cost);
                assert(bk_cover.size() == bk_cover_cost);
                assert(cover_cost == bk_cover_cost);
#endif
            }
        } else {
            if( g_max_action_cost > 1 ) {
                cover_cost = Hypergraph::min_cost_cover_unconstrained(num_landmarks,
                                                                      vec_edges,
                                                                      vec_edge_costs,
                                                                      cover);
            } else {
                cover_cost = Hypergraph::min_cover_unconstrained(num_landmarks,
                                                                 vec_edges,
                                                                 cover);
            }
        }

        // Extract hitting set from cover.
        for( int i = 0, isz = cover.size(); i < isz; ++i ) {
            hitting_set.insert(vec_actions[cover[i]]);
        }

        // Cleanup and return.
        actions.clear();
        vec_compl_edges.clear();
        vec_edges.clear();
        vec_edge_costs.clear();
        vec_actions.clear();

        return cover_cost;
    }
}

int chvatal_algorithm(const Relaxed::Problem &rproblem,
                       int num_landmarks,
                       const Landmark *landmarks,
                       Relaxed::OperatorSet &hitting_set) {

    int num_actions = rproblem.operators_.size();
    vector<pair<bool, const Landmark*> > vec_landmarks(num_landmarks, pair<bool, const Landmark*>());
    vector<int> num_uncovered_landmarks_hit_by(num_actions, 0);
    vector<vector<int> > landmarks_hit_by(num_actions, vector<int>());
    Relaxed::OperatorSet actions_in_landmarks;

    // Initialize
    int index = 0;
    for( const Landmark *lm = landmarks; lm != 0; lm = lm->next_, ++index ) {
        vec_landmarks[index] = make_pair(true, lm);
        for( Landmark::const_iterator it = lm->begin(); it != lm->end(); ++it ) {
            landmarks_hit_by[*it].push_back(index);
            ++num_uncovered_landmarks_hit_by[*it];
            actions_in_landmarks.insert(*it);
        }
    }

    // Greedily pick actions using pricing method for the hitting set.
    int cost = 0;
    hitting_set.clear();
    int remaining_landmarks = num_landmarks;
    while( remaining_landmarks > 0 ) {
        int best_action = -1;
        float best_score = 0;
        for( Relaxed::OperatorSet::const_iterator a = actions_in_landmarks.begin(); a != actions_in_landmarks.end(); ++a ) {
            const Relaxed::Operator &rop = rproblem.operators_[*a];
            if( (rop.base_cost_ > 0) && (num_uncovered_landmarks_hit_by[*a] > 0) ) {
                float score = (float)num_uncovered_landmarks_hit_by[*a] / (float)rop.base_cost_;
                assert(score >= 0);
                if( score > best_score ) {
                    best_score = score;
                    best_action = *a;
                }
            }
        }
        assert(best_action != -1);
        hitting_set.insert(best_action);
        cost += rproblem.operators_[best_action].base_cost_;

        // Mark subsets hit by best action as covered.
        for( int i = 0, isz = landmarks_hit_by[best_action].size(); i < isz; ++i ) {
            pair<bool, const Landmark*> &p = vec_landmarks[landmarks_hit_by[best_action][i]];
            if( p.first ) {
                p.first = false;
                --remaining_landmarks;
                const Landmark *lm = p.second;
                for( Landmark::const_iterator it = lm->begin(); it != lm->end(); ++it )
                    --num_uncovered_landmarks_hit_by[*it];
            }
        }
        assert(num_uncovered_landmarks_hit_by[best_action] == 0);
    }
    return cost;
}

} // end of namespace

