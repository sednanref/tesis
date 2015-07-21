#ifndef STATE_EQUATION_HEURISTIC_H
#define STATE_EQUATION_HEURISTIC_H

#include <map>
#include <set>

#include "../../state.h"
#include "../../heuristic.h"
#include "../../max_heuristic.h"

// For computing LM-Cut landmarks
#include "../hitting_sets/relaxed.h"
#include "../hitting_sets/lmcut_engine.h"

// For computing LA landmarks
#include "../../landmarks/landmark_graph.h"
#include "../../landmarks/landmark_status_manager.h"

#pragma GCC diagnostic ignored "-Wunused-parameter"

// Select OSI interface (API)  for lp solver
#include <CoinPackedVector.hpp>
#include <CoinPackedMatrix.hpp>
#include <OsiSolverInterface.hpp>

// encapsulate the heuristic into its own namespace
namespace StateEquation {

class Proposition;
class PCOperator;

struct SASOperator {
    const Operator *op_;
    std::vector<Prevail> prevail_;
    std::vector<PrePost> pre_post_;
    int cost_;
    SASOperator(const Operator &op)
      : op_(&op), prevail_(op.get_prevail()), pre_post_(op.get_pre_post()), cost_(op.get_cost()) {
    }
    SASOperator(const Operator *op, const std::vector<Prevail> &prevail, const std::vector<PrePost> &pre_post, int cost)
      : op_(op), prevail_(prevail), pre_post_(pre_post), cost_(cost) {
    }
};

// A PC operator has produced/consumed propositions, it references
// the real SAS operator, and contains additional information.
struct PCOperator {
    const SASOperator *op_;
    std::vector<Proposition*> produces_;
    std::vector<Proposition*> consumes_;
    std::vector<Proposition*> prevails_;
    int base_cost_;

    PCOperator(const std::vector<Proposition*> &produces,
               const std::vector<Proposition*> &consumes,
               const std::vector<Proposition*> &prevails,
               const SASOperator *op, int base_cost)
      : op_(op), produces_(produces), consumes_(consumes), prevails_(prevails), base_cost_(base_cost) {
    }

    PCOperator(const std::set<Proposition*> &produces,
               const std::set<Proposition*> &consumes,
               const std::set<Proposition*> &prevails,
               const SASOperator *op, int base_cost)
      : op_(op), base_cost_(base_cost) {
        produces_.reserve(produces.size());
        for( std::set<Proposition*>::const_iterator it = produces.begin(); it != produces.end(); ++it )
            produces_.push_back(*it);
        consumes_.reserve(consumes.size());
        for( std::set<Proposition*>::const_iterator it = consumes.begin(); it != consumes.end(); ++it )
            consumes_.push_back(*it);
        prevails_.reserve(prevails.size());
        for( std::set<Proposition*>::const_iterator it = prevails.begin(); it != prevails.end(); ++it )
            prevails_.push_back(*it);
    }
};

// A proposition has an index and refer to an atom of the form
// Var = Val. When h_max values are computed, each relaxed
// propositionis assigned an h_max_cost.
struct Proposition {
    int index_, var_, val_, row_index_;
    std::vector<int> produced_by_;
    std::vector<int> consumed_by_;
    std::vector<int> prevail_of_;

    Proposition(int index = -1, int var = -1, int val = -1)
      : index_(index), var_(var), val_(val), row_index_(-1) {
    }
};

struct Edge {
    enum { PT = 0, TP = 1 };
    int index_, type_;
    int from_, to_;
    Edge(int index, int type, int from, int to)
      : index_(index), type_(type), from_(from), to_(to) {
    }
};

// A Linear Program (LP) contains for each proposition a vector
// with indices of operators that delete it (-<index>) and 
// operators that add it (+<index>).
struct IncidenceMatrixForPN {
    int nplaces_, ntransitions_, nedges_;
    std::vector<std::vector<int> > rows_;

    IncidenceMatrixForPN(int nplaces = 0, int ntransitions = 0, int nedges = 0)
      : nplaces_(nplaces), ntransitions_(ntransitions),
        nedges_(nedges), rows_(nplaces_+ntransitions_) {
    }
};


class Heuristic : public ::Heuristic {
    int landmarks_;
    bool use_1safe_information_;
    bool use_prevails_;
    int merge_fluents_;
    int num_propositions_;

    std::vector<int> sas_variables_;
    std::vector<SASOperator*> sas_operators_;
    std::vector<std::pair<int, int> > merged_vars_;
    int num_primitive_vars_;

    std::vector<PCOperator> operators_;
    std::vector<bool> prevail_propositions_;
    std::vector<std::vector<Proposition> > propositions_;
    std::vector<Proposition> ordered_propositions_;
    std::vector<Edge> edges_;
    std::vector<bool> one_safe_;
    std::vector<state_var_t> goal_state_;

    IncidenceMatrixForPN *M_;
    int nconstraints_;
    std::vector<int> multiplicity_;

    // For constraints for prevail conditions
    std::vector<std::map<int, int> > prevail_constraints_;

    // For LM-Cut landmarks
    Relaxed::Problem rproblem_;
    HittingSets::LMCutEngine *lmcut_engine_;
    std::vector<int> lmcut_opmap_;

    // For LA landmarks
    LandmarkGraph *lm_graph_;
    LandmarkStatusManager *lm_status_manager_;
    std::vector<int> la_opmap_;
    const set<int> empty_lm_set_;
    const set<int>& get_achievers(int lmn_status, LandmarkNode &lmn);

    std::string lp_solver_;
    OsiSolverInterface *osi_solver_;

    bool safe_to_max_with_hmax_;
    HSPMaxHeuristic *hmax_heuristic_;

    virtual void initialize();

    bool is_primitive_var(int var) const { return var < num_primitive_vars_; }
    int index_merged_var(int var) const { return var - num_primitive_vars_; }
    int get_state_value(int var, const State &state) const {
        if( is_primitive_var(var) ) {
            return state[var];
        } else {
            const pair<int, int> &merge = merged_vars_[index_merged_var(var)];
            return get_state_value(merge.first, state) * sas_variables_[merge.second] + get_state_value(merge.second, state);
        }
    }
    int get_state_value(int var, const std::vector<state_var_t> &state) const {
        if( is_primitive_var(var) ) {
            return state[var];
        } else {
            const pair<int, int> &merge = merged_vars_[index_merged_var(var)];
            return get_state_value(merge.first, state) * sas_variables_[merge.second] + get_state_value(merge.second, state);
        }
    }
    bool has_value(int var, const std::vector<state_var_t> &state) const {
        if( is_primitive_var(var) ) {
            return state[var] != (state_var_t)-1;
        } else {
            const pair<int, int> &merge = merged_vars_[index_merged_var(var)];
            return has_value(merge.first, state) && has_value(merge.second, state);
        }
    }

    void compute_prevails(std::vector<int> &prevails, const std::vector<bool> &merged) const;
    std::pair<int, int> get_var_types(const SASOperator &op, int var1, int var2) const;
    size_t get_prevail_count(const pair<int, int> &type, int dom1, int dom2) const;
    size_t get_operator_count(const std::pair<int, int> &type, int dom1, int dom2) const;
    int get_var_value(const std::vector<Prevail> &prevail, int var) const;
    std::pair<int, int> get_var_value(const std::vector<PrePost> &pre_post, int var) const;
    void calculate_merge_estimation(const std::vector<int> &prevails,
                                    std::vector<int> &estimation) const;
    std::pair<int, int> choose_variables_to_merge(const std::vector<int> &prevails,
                                                  const std::vector<bool> &merged,
                                                  const std::vector<int> &estimation) const;
    size_t calculate_number_new_operators(const std::pair<int, int> &merge,
                                          std::vector<bool> &good_operators) const;
    void create_new_operators(const SASOperator &op, const std::pair<int, int> &merge, int new_var, bool swap = false);

    void build_operator(const SASOperator &op);
    void add_operator(const std::set<Proposition*> &produces,
                      const std::set<Proposition*> &consumes,
                      const std::set<Proposition*> &prevails,
                      const SASOperator *op, int base_cost);
    void add_operator(const std::vector<Edge*> &enters,
                      const std::vector<Edge*> &leaves,
                      const SASOperator *op, int base_cost);

    virtual int compute_heuristic(const State &state);
public:
    Heuristic(const Options &opts);
    virtual ~Heuristic();
    // For LA landmarks
    virtual bool reach_state(const State& parent_state, const Operator &op, const State& state);
    virtual bool dead_ends_are_reliable() const { return true; }
};

} // end of namespace

#endif

