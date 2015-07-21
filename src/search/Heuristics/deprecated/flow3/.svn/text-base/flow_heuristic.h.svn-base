#ifndef FLOW3_HEURISTIC_H
#define FLOW3_HEURISTIC_H

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

// For computing lmgraph landmarks
#include "../../landmarks/landmark_graph.h"
#include "../../landmarks/landmark_status_manager.h"

#pragma GCC diagnostic ignored "-Wunused-parameter"

// Select OSI interface (API) for lp solver
#include <CoinPackedVector.hpp>
#include <CoinPackedMatrix.hpp>
#include <OsiSolverInterface.hpp>

// encapsulate the heuristic into its own namespace
namespace Flow3 {

inline bool are_mutex(int var1, int val1, int var2, int val2) {
    return ::are_mutex(std::make_pair(var1, val1), std::make_pair(var2, val2));
}

class Proposition;
class Operator;

struct Variable {
    int id_;
    bool goal_;
    bool safe_;
    Variable(int id) : id_(id), goal_(false), safe_(true) { }
    virtual void dump(std::ostream &os = std::cout) const {
        os << "v" << id_ << "[<primitive>]";
    }
};

struct MergedVariable : public Variable, std::pair<Variable*, Variable*> {
    MergedVariable(int id, Variable *first, Variable *second)
      : Variable(id), std::pair<Variable*, Variable*>(first, second) {
        goal_ = first->goal_ && second->goal_;
        safe_ = first->safe_ && second->safe_;
    }
    virtual void dump(std::ostream &os = std::cout) const {
        os << "v" << id_ << "[" << first->id_ << "," << second->id_ << "]";
    }
};

struct Proposition {
    int id_;                                    // must be unique
    int var_;                                   // variable id
    int row_index_;                             // row index of proposition's flow constraint
    bool is_mutex_with_goal_;                   // true if proposition is incompatible with goal
    std::vector<Operator*> prevail_of_;         // list of actions that prevail proposition
    std::vector<Operator*> produced_by_;        // list of actions that add proposition
    std::vector<Operator*> consumed_by_;        // list of actions that delete proposition
    std::vector<Operator*> relevant_to_;        // list of actions that are relevant to proposition

    static int nprimitive_variables_;                                   // number of primitive variables
    static const std::vector<Variable*> *variables_;                    // variables
    static const std::map<std::pair<int, int>, int> *merged_variables_; // record of merged variables

    Proposition(int id = -1, int var = -1)
      : id_(id), var_(var), row_index_(-1), is_mutex_with_goal_(true) { }
    virtual ~Proposition() { }

    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;
    virtual bool holds_at(const State &state) const = 0;
    virtual bool is_mutex_with(const Proposition *p) const = 0;
    virtual bool is_mutex_with_precondition_of(const Operator *op) const = 0;
    virtual bool is_mutex_with_postcondition_of(const Operator *op) const = 0;

    Variable* var() const { return (*variables_)[var_]; }
    bool is_primitive_proposition() const { return var_ < nprimitive_variables_; }
    bool is_goal_var() const { return (*variables_)[var_]->goal_; }
    bool is_safe() const { return (*variables_)[var_]->safe_; }

    bool is_prevail_of(const Operator *op) const {
        for( int i = 0; i < prevail_of_.size(); ++i )
            if( prevail_of_[i] == op ) return true;
        return false;
    }
    bool is_consumed_by(const Operator *op) const {
        for( int i = 0; i < consumed_by_.size(); ++i )
            if( consumed_by_[i] == op ) return true;
        return false;
    }
    bool is_produced_by(const Operator *op) const {
        for( int i = 0; i < produced_by_.size(); ++i )
            if( produced_by_[i] == op ) return true;
        return false;
    }
    bool is_relevant_to(const Operator *op) const {
        for( int i = 0; i < relevant_to_.size(); ++i )
            if( relevant_to_[i] == op ) return true;
        return false;
    }

    void remove_prevail_of(std::vector<Operator*> &ops);
};

struct PrimitiveProposition : public Proposition {
    int val_;
    PrimitiveProposition(int id, int var, int val)
      : Proposition(id, var), val_(val) { }
    virtual ~PrimitiveProposition() { }
    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;

    virtual bool holds_at(const State &state) const {
        return state[var_] == val_;
    }

    virtual bool is_mutex_with(const Proposition *p) const {
        const PrimitiveProposition *q = dynamic_cast<const PrimitiveProposition*>(p);
        if( q != 0 )
            return ((var_ == q->var_) && (val_ != q->val_)) || are_mutex(var_, val_, q->var_, q->val_);
        else
            return p->is_mutex_with(this);
    }
    virtual bool is_mutex_with_precondition_of(const Operator *op) const;
    virtual bool is_mutex_with_postcondition_of(const Operator *op) const;
};

struct MergedProposition : public Proposition, std::pair<const Proposition*, const Proposition*> {
    MergedProposition(int id, const Proposition *first, const Proposition *second)
      : Proposition(id, merged_variables_->find(std::make_pair(first->var_, second->var_))->second),
        std::pair<const Proposition*, const Proposition*>(first, second) {
        is_mutex_with_goal_ = first->is_mutex_with_goal_ || second->is_mutex_with_goal_;
    }
    virtual ~MergedProposition() { }
    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;

    virtual bool holds_at(const State &state) const {
        return first->holds_at(state) && second->holds_at(state);
    }
    virtual bool is_mutex_with(const Proposition *p) const {
        return first->is_mutex_with(p) || second->is_mutex_with(p);
    }
    virtual bool is_mutex_with_precondition_of(const Operator *op) const {
        return first->is_mutex_with_precondition_of(op) || second->is_mutex_with_precondition_of(op);
    }
    virtual bool is_mutex_with_postcondition_of(const Operator *op) const {
        return first->is_mutex_with_postcondition_of(op) || second->is_mutex_with_postcondition_of(op);
    }
};

struct Operator {
    int id_;                                    // must be unique (used as column index in osi)
    std::vector<Proposition*> prevails_;        // list of prevails
    std::vector<Proposition*> consumes_;        // list of propositions consumed
    std::vector<Proposition*> produces_;        // list of propositions produced

    static const std::vector<std::set<int> > *propositions_mutex_with_precondition_;
    static const std::vector<std::set<int> > *propositions_mutex_with_postcondition_;

    Operator(int id) : id_(id) { }
    virtual ~Operator() { }
    virtual int get_cost() const = 0;
    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;
    virtual bool proposition_is_mutex_with_precondition(const PrimitiveProposition *p, bool lookup_value = true) const = 0;
    virtual bool proposition_is_mutex_with_postcondition(const PrimitiveProposition *p, bool lookup_value = true) const = 0;

    void remove_prevail(const Proposition *p) {
        //std::cout << "removing "; p->dump(); std::cout << " as prevail of "; dump(); std::cout << prevails_.size() << std::flush;
        for( int i = 0; i < prevails_.size(); ++i ) {
            if( prevails_[i] == p ) {
                for( int j = i+1; j < prevails_.size(); ++j )
                    prevails_[j-1] = prevails_[j];
                prevails_.pop_back();
                break;
            }
        }
        //std::cout << prevails_.size() << std::endl;
    }
};

struct PrimitiveOperator : public Operator {
    const ::Operator& base_op_;                 // reference to base operator
    int cost_;
    PrimitiveOperator(int id, const ::Operator& base_op)
        : Operator(id), base_op_(base_op), cost_(base_op_.get_cost()) {
    }
    virtual ~PrimitiveOperator() { }
    virtual int get_cost() const { return cost_; }
    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;

    virtual bool proposition_is_mutex_with_precondition(const PrimitiveProposition *p, bool lookup_value = true) const {
        if( lookup_value ) {
            return (*Operator::propositions_mutex_with_precondition_)[id_].find(p->id_) != (*Operator::propositions_mutex_with_precondition_)[id_].end();
        } else {
            const std::vector<Prevail> &prevail = base_op_.get_prevail();
            for( int i = 0; i < prevail.size(); ++i ) {
                if( ((prevail[i].var == p->var_) && (prevail[i].prev != p->val_)) ||
                    are_mutex(prevail[i].var, prevail[i].prev, p->var_, p->val_) )
                    return true;
            }

            const std::vector<PrePost> &pre_post = base_op_.get_pre_post();
            for( int i = 0; i < pre_post.size(); ++i ) {
                if( ((pre_post[i].var == p->var_) && (pre_post[i].pre != -1) && (pre_post[i].pre != p->val_)) ||
                    ((pre_post[i].pre != -1) && are_mutex(pre_post[i].var, pre_post[i].pre, p->var_, p->val_)) )
                    return true;
            }
            return false;
        }
    }

    virtual bool proposition_is_mutex_with_postcondition(const PrimitiveProposition *p, bool lookup_value = true) const {
        if( lookup_value ) {
            return (*Operator::propositions_mutex_with_postcondition_)[id_].find(p->id_) != (*Operator::propositions_mutex_with_postcondition_)[id_].end();
        } else {
            const std::vector<Prevail> &prevail = base_op_.get_prevail();
            for( int i = 0; i < prevail.size(); ++i ) {
                if( ((prevail[i].var == p->var_) && (prevail[i].prev != p->val_)) ||
                    are_mutex(prevail[i].var, prevail[i].prev, p->var_, p->val_) )
                    return true;
            }

            const std::vector<PrePost> &pre_post = base_op_.get_pre_post();
            for( int i = 0; i < pre_post.size(); ++i ) {
                if( ((pre_post[i].var == p->var_) && (pre_post[i].post != p->val_)) ||
                    are_mutex(pre_post[i].var, pre_post[i].post, p->var_, p->val_) )
                    return true;
            }
            return false;
        }
    }
};

struct CopyOperator : public Operator {
    const Operator *op_;
    bool is_consumer_;
    int fluent_;
    CopyOperator(int id, const Operator *op, bool is_consumer, int fluent)
      : Operator(id), op_(op), is_consumer_(is_consumer), fluent_(fluent) {
    }
    virtual ~CopyOperator() { }
    virtual int get_cost() const { return 0; }
    virtual void dump(std::ostream &os = std::cout, bool full_info = false) const;
    virtual bool proposition_is_mutex_with_precondition(const PrimitiveProposition *p, bool lookup_value = true) const {
        return false;
    }
    virtual bool proposition_is_mutex_with_postcondition(const PrimitiveProposition *p, bool lookup_value = true) const {
        return false;
    }
};

inline void Proposition::remove_prevail_of(std::vector<Operator*> &ops) {
    //std::cout << "ops="; for( int k = 0; k < ops.size(); ++k ) std::cout << " " << ops[k]->id_; std::cout << std::endl;
    //std::cout << "pof="; for( int k = 0; k < prevail_of_.size(); ++k ) std::cout << " " << prevail_of_[k]->id_; std::cout << std::endl;
    //std::cout << "removing prevail of " << ops.size() << " " << prevail_of_.size() << " ";
    int i = 0;
    for( int j = 0; j < ops.size(); ++j ) {
        while( (i < prevail_of_.size()) && (prevail_of_[i]->id_ <= ops[j]->id_) ) {
            if( prevail_of_[i]->id_ == ops[j]->id_ ) {
                for( int k = i+1; k < prevail_of_.size(); ++k )
                    prevail_of_[k-1] = prevail_of_[k];
                prevail_of_.pop_back();
                break;
            }
            ++i;
        }
    }
    //std::cout << "pof="; for( int k = 0; k < prevail_of_.size(); ++k ) std::cout << " " << prevail_of_[k]->id_; std::cout << std::endl;
}

inline bool PrimitiveProposition::is_mutex_with_precondition_of(const Operator *op) const {
    return op->proposition_is_mutex_with_precondition(this);
}

inline bool PrimitiveProposition::is_mutex_with_postcondition_of(const Operator *op) const {
    return op->proposition_is_mutex_with_postcondition(this);
}

class Heuristic : public ::Heuristic {
    bool empty_base_lp_;
    int use_landmarks_;
    int merge_fluents_;
    bool merge_goals_;
    bool use_ubs_;
    std::string lp_solver_;    
    float epsilon_;
    bool debug_;

    bool merge_done_at_root_;
    bool safe_to_max_with_hmax_;
    HSPMaxHeuristic *hmax_heuristic_;

    int nprimitive_variables_;                  // number primitive variables
    int nprimitive_propositions_;               // number primitive propositions
    int nprimitive_operators_;                  // number primitive operators
    int nvariables_;                            // number variables
    int npropositions_;                         // number propositions
    int noperators_;                            // number operators

    std::vector<Variable*> variables_;          // all variables
    std::vector<std::vector<PrimitiveProposition*> > primitive_propositions_; // all primitive propositions indexed by (var,value)
    std::vector<Proposition*> propositions_;    // all propositions
    std::vector<Operator*> operators_;          // all operators

    std::vector<bool> checked_operators_;       // primitive operators that had been processed and can be obviated

    std::map<std::pair<int, int>, bool> merged_propositions_;
    std::map<std::pair<int, int>, int> merged_variables_; // map of merged variables
    std::map<std::pair<int, int>, std::vector<int> > operator_copies_; // map of operator copies
    std::map<std::pair<int, int>, int> row_index_for_operator_copies_; // row index of constraint for operator copies

    std::vector<std::set<int> > propositions_mutex_with_precondition_;
    std::vector<std::set<int> > propositions_mutex_with_postcondition_;

    int nconstraints_;
    int ninactive_constraints_;
    OsiSolverInterface *osi_solver_;
    std::vector<double> lp_solution_;
    float lp_value_;
    std::vector<bool> operators_active_in_solution_;

    std::vector<int> xxx_operators_;

    // to store landmarks
    HittingSets::Landmark *landmarks_;

    // For lmgraph landmarks
    LandmarkGraph *lm_graph_;
    LandmarkStatusManager *lm_status_manager_;
    std::vector<int> la_opmap_;  // TODO: REVISE IF NEEDED
    const set<int> empty_lm_set_;
    const set<int>& get_achievers(int lmn_status, LandmarkNode &lmn);

    // For LM-Cut landmarks
    int lmcut_value_;
    Relaxed::Problem rproblem_;
    HittingSets::LMCutEngine *lmcut_engine_;
    std::vector<int> lmcut_opmap_;  // TODO: REVISE IF NEEDED

    void initialize();
    void create_base_model();
    void create_primitive_operator(const ::Operator &base_op);

    void set_column_name(const Operator *op);
    void set_row_name(const Proposition *p);
    void create_base_lp();

    bool compute_landmarks(const State &state);
    void remove_landmarks() {
        HittingSets::Landmark::deallocate_chain(landmarks_);
        landmarks_ = 0;
    }
    void insert_landmark_constraints();
    void remove_landmark_constraints() { osi_solver_->restoreBaseModel(nconstraints_); }
    bool solve_lp(const State &state, bool set_active_operators);

    bool refine_lp(Operator *op, Proposition *np, bool operator_consumes_fluent);
    bool add_copy_producer(Operator *op, Proposition *np) { return refine_lp(op, np, false); }
    bool add_copy_consumer(Operator *op, Proposition *np) { return refine_lp(op, np, true); }

    bool refine_model(const State &state);
    bool merge_propositions(Proposition *first, Proposition *second);

    void set_row_bounds(const State &state);
    int compute_heuristic(const State &state);

public:
    Heuristic(const Options &opts);
    virtual ~Heuristic();
    // For lmgraph landmarks
    virtual bool reach_state(const State& parent_state, const ::Operator &op, const State& state);
    virtual bool dead_ends_are_reliable() const { return true; }
};

} // end of namespace


std::ostream& operator<<(std::ostream &os, const Flow3::Variable &var) {
    var.dump(os);
    return os;
}

std::ostream& operator<<(std::ostream &os, const Flow3::Proposition &prop) {
    prop.dump(os);
    return os;
}

std::ostream& operator<<(std::ostream &os, const Flow3::Operator &op) {
    op.dump(os);
    return os;
}

#endif

