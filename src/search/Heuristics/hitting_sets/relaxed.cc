#include "relaxed.h"
#include "../../operator.h"
#include "../../operator_cost.h"
#include <stdlib.h>

using namespace std;

//#define DEBUG

namespace Relaxed {

void Problem::initialize() {
    cout << "Building relaxed problem..." << endl;

    // framework does not support axioms or conditional effects
    ::verify_no_axioms_no_cond_effects();

    // Build propositions.
    artificial_precondition_.index_ = num_propositions_++;
    artificial_precondition_.val_ = 0;
    artificial_goal_.index_ = num_propositions_++;
    artificial_goal_.val_ = 1;
    assert(num_propositions_ == 2);
    propositions_.resize(g_variable_domain.size());
    for( int var = 0; var < g_variable_domain.size(); ++var ) {
        for( int value = 0; value < g_variable_domain[var]; ++value )
            propositions_[var].push_back(Proposition(num_propositions_++, var, value));
    }

    // Build relaxed operators for operators and axioms.
    for(int i = 0; i < g_operators.size(); i++)
        build_relaxed_operator(g_operators[i]);

    // Simplify relaxed operators.
    // simplify();
    /* TODO: Put this back in and test if it makes sense,
       but only after trying out whether and how much the change to
       unary operators hurts. */

    // Build artificial goal proposition and operator.
    vector<Proposition*> goal_op_pre, goal_op_eff;
    for( int i = 0; i < g_goal.size(); ++i ) {
        int var = g_goal[i].first, val = g_goal[i].second;
        Proposition *goal_prop = &propositions_[var][val];
        goal_op_pre.push_back(goal_prop);
    }
    goal_op_eff.push_back(&artificial_goal_);
    add_relaxed_operator(goal_op_pre, goal_op_eff, 0, 1);
    index_artificial_goal_operator_ = operators_.size() - 1;

    // Cross-reference relaxed operators.
    for( int i = 0; i < operators_.size(); ++i ) {
        Operator *rop = &operators_[i];
        for( int j = 0; j < rop->precondition_.size(); ++j )
            rop->precondition_[j]->precondition_of_.push_back(i);
        for( int j = 0; j < rop->effects_.size(); ++j )
            rop->effects_[j]->effect_of_.push_back(i);
    }

    // Initialize BitmapSet
    Utils::BitmapSet::initialize(operators_.size());
}

void Problem::build_relaxed_operator(const ::Operator &op) {
    const vector<Prevail> &prevail = op.get_prevail();
    const vector<PrePost> &pre_post = op.get_pre_post();
    vector<Proposition*> precondition;
    vector<Proposition*> effects;
    for( int i = 0; i < prevail.size(); ++i )
        precondition.push_back(&propositions_[prevail[i].var][prevail[i].prev]);
    for( int i = 0; i < pre_post.size(); ++i ) {
        if( pre_post[i].pre != -1 )
            precondition.push_back(&propositions_[pre_post[i].var][pre_post[i].pre]);
        effects.push_back(&propositions_[pre_post[i].var][pre_post[i].post]);
    }
    add_relaxed_operator(precondition, effects, &op, get_adjusted_action_cost(op, NORMAL));
}

void Problem::add_relaxed_operator(const vector<Proposition*> &precondition, const vector<Proposition*> &effects, const ::Operator *op, int base_cost) {
    Operator relaxed_op(precondition, effects, op, base_cost);
    if( relaxed_op.precondition_.empty() )
        relaxed_op.precondition_.push_back(&artificial_precondition_);
    operators_.push_back(relaxed_op);
#ifdef DEBUG
    if( op != 0 ) {
        cout << "id=" << operators_.size()-1 << flush
             << ", operator (" << op->get_name() << flush
             << ") with cost " << get_adjusted_action_cost(*op, NORMAL) << flush
             << " added" << endl;
    }
#endif
}

} // end of namespace

