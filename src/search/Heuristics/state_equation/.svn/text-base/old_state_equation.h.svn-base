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

// Select OSI interface (API)  for lp solver
#include <CoinPackedVector.hpp>
#include <CoinPackedMatrix.hpp>

#pragma GCC diagnostic ignored "-Wunused-parameter"

#include <OsiClpSolverInterface.hpp>
#include <OsiGrbSolverInterface.hpp>
#include <OsiCpxSolverInterface.hpp>

// encapsulate the heuristic into its own namespace
namespace StateEquation {

class Proposition;
class PCOperator;

// A PC operator has produced/consumed propositions, it references
// the real SAS operator, and contains additional information.
struct PCOperator {
    const ::Operator *op_;
    std::vector<Proposition*> produces_;
    std::vector<Proposition*> consumes_;
    std::vector<Proposition*> prevails_;
    int base_cost_;

    PCOperator(const std::vector<Proposition*> &produces,
               const std::vector<Proposition*> &consumes,
               const std::vector<Proposition*> &prevails,
               const ::Operator *op, int base_cost)
      : op_(op), produces_(produces), consumes_(consumes), prevails_(prevails), base_cost_(base_cost) {
    }

    PCOperator(const std::set<Proposition*> &produces,
               const std::set<Proposition*> &consumes,
               const std::set<Proposition*> &prevails,
               const ::Operator *op, int base_cost)
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
    int num_propositions_;

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

    void build_operator(const ::Operator &op);
    void add_operator(const std::set<Proposition*> &produces,
                      const std::set<Proposition*> &consumes,
                      const std::set<Proposition*> &prevails,
                      const ::Operator *op, int base_cost);
    void add_operator(const std::vector<Edge*> &enters,
                      const std::vector<Edge*> &leaves,
                      const ::Operator *op, int base_cost);

    virtual int compute_heuristic(const State &state);
public:
    Heuristic(const Options &opts);
    virtual ~Heuristic();
    // For LA landmarks
    virtual bool reach_state(const State& parent_state, const Operator &op, const State& state);
    virtual bool dead_ends_are_reliable() { return true; }
};

} // end of namespace

#endif

