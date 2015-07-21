#ifndef MENKES_STATE_EQUATION_HEURISTIC_H
#define MENKES_STATE_EQUATION_HEURISTIC_H

#include <map>
#include <set>
#include <vector>
#include <list>

#include "../../state.h"
#include "../../heuristic.h"
#include "../../max_heuristic.h"

// For computing LM-Cut landmarks
#include "../hitting_sets/relaxed.h"
#include "../hitting_sets/lmcut_engine.h"

// For computing LA landmarks
#include "../../landmarks/landmark_graph.h"
#include "../../landmarks/landmark_status_manager.h"

// Select OSI interface (API) for lp solver
#include <CoinPackedVector.hpp>
#include <CoinPackedMatrix.hpp>

#pragma GCC diagnostic ignored "-Wunused-parameter"

#include <OsiClpSolverInterface.hpp>
//#include <OsiGrbSolverInterface.hpp>
//#include <OsiCpxSolverInterface.hpp>

// encapsulate the heuristic into its own namespace
namespace MenkesStateEquation {

class MetaProposition;
class MetaOperator;

struct MetaProposition {
    int id_;                                    // must be unique (used as row index in osi)
    int var_;                                   // variable id
    int val_;                                   // value id
    bool is_goal_;                              // true if goal
    std::vector<MetaOperator*> produced_by_;    // list of actions that add meta proposition
    std::vector<MetaOperator*> consumed_by_;    // list of actions that delete meta proposition
    std::vector<MetaOperator*> prevail_of_;     // list of actions that prevail meta proposition
    std::vector<bool> base_vars_;               // to indicate the primitive variables (hopefully won't need this)
    std::vector<int> base_vals_;                // to indicate the primitive values (hopefully won't need this)
    MetaProposition(int id = -1, int var = -1, int val = -1)
        : id_(id), var_(var), val_(val), is_goal_(false) {
    }
    int get_id() { return id_; }
    bool is_goal() { return is_goal_; }
    void set_goal(bool goal) { is_goal_ = goal; }
    void dump(std::ostream &os = std::cout) const; // write meta proposition
};

struct MetaOperator {
    int id_;                                    // must be unique (used as column index in osi)
    const Operator& op_;                        // reference to base operator
    std::vector<MetaProposition*> produces_;    // list of propositions that meta operator adds
    std::vector<MetaProposition*> consumes_;    // list of propositions that meta operator deletes
    std::vector<MetaProposition*> prevails_;    // list of propositions that meta operator prevails
    MetaOperator(const Operator& op, int id = -1)
        : id_(id), op_(op) {
    }
    int get_id() { return id_; }
    void dump(std::ostream &os = std::cout) const; // write meta operator
};

class Heuristic : public ::Heuristic {
    int merge_fluents_;
    std::string lp_solver_;    

    std::vector<std::vector<MetaProposition*> > propositions_; // all meta propositions
    std::vector<MetaOperator*> operators_;	// all meta operators
    std::vector<bool> is_goal_var_;		// need something to check whether variable contains unique goal
    std::map<std::vector<bool>, int> merged_variables_; // need something (map?) to check whether variables have been merged
    std::map<std::vector<int>, int> merged_values_; // need something (map?) to check whether values have been merged
    std::vector<bool> checked_operators_; 	// need something (vector?) to check whether operators have been checked for merging 
    std::map<std::pair<int, int>, std::list<MetaOperator*> > operator_copies_; // need something (map?) to link operators with their copies

    int nprimitive_variables_;                  // number primitive variables
    int nprimitive_propositions_;               // number primitive propositions
    int nprimitive_operators_;                  // number primitive operators
    int nvariables_;                            // number variables
    int npropositions_;                         // number propositions
    int noperators_;                            // number operators

    OsiSolverInterface *osi_solver_;
    int nconstraints_;

    void initialize();
    int compute_heuristic(const State &state);

public:
    Heuristic(const Options &opts);
    virtual ~Heuristic();
};

} // end of namespace

#endif

