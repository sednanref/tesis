#include "menkes_state_equation_heuristic.h"

#include "../../globals.h"
#include "../../operator.h"
#include "../../state.h"
#include "../../option_parser.h"
#include "../../plugin.h"

#include <cassert>
#include <queue>
#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <vector>
#include <sstream>
#include <fstream>
#include <limits>
#include <math.h>

#pragma GCC diagnostic ignored "-Wunused-variable"

#define ROW_LE      0
#define ROW_EQ      1
#define ROW_GE      2
#define ROW_DB      3
#define BIG_M       100000
#define SMALL_M     0.1

using namespace std;

//#define DEBUG

// encapsulate the heuristic into its own namespace
namespace MenkesStateEquation {

// construction and destruction
Heuristic::Heuristic(const Options &opts)
    : ::Heuristic(opts),
      merge_fluents_(opts.get<int>("merge_fluents")),
      lp_solver_(opts.get<string>("lp_solver")) {
      is_goal_var_ = vector<bool>(g_variable_domain.size(), false);
}

Heuristic::~Heuristic() {
}

// initialization
void Heuristic::initialize() {
    cout << "Initializing Order_Relaxed heuristic using:";
    cout << "merge_fluents=" << merge_fluents_;
    cout << ", LP-kit=osi:" << lp_solver_ << endl;

    // Framework does not support axioms or conditional effects
    ::verify_no_axioms_no_cond_effects();

    // Create meta-propositions (basically copy primitive propositions)
    int id = 0;
    propositions_.resize(g_variable_domain.size());
    for( int var = 0; var < g_variable_domain.size(); ++var ) {
        propositions_[var].resize(g_variable_domain[var]);
        for( int val = 0; val < g_variable_domain[var]; ++val ) {
            MetaProposition* meta_proposition = new MetaProposition(id, var, val);
            propositions_[var][val] = meta_proposition;
            id++;
        }
    }
    cout << "Initialize: meta propositions created" << endl;

    // Create meta-operators (basically copy primitive operators)
    id = 0;
    operators_.reserve(g_operators.size());
    for( int i = 0; i < g_operators.size(); ++i ) {
        Operator &op = g_operators[i];
        MetaOperator* meta_operator = new MetaOperator(op, id);
        operators_.push_back(meta_operator);
        id++;
    }
    cout << "Initialize: meta operators created" << endl;

    // Get primitive sizes // NOTE: not sure if we need this
    nprimitive_variables_ = g_variable_domain.size();
    nprimitive_propositions_ = propositions_.size();
    nprimitive_operators_ = operators_.size();

    // Define goals
    for( int i = 0; i < g_goal.size(); ++i ) {
        int var = g_goal[i].first;
        int val = g_goal[i].second;
        propositions_[var][val]->set_goal(true);
        is_goal_var_[var] = true;
        cout << "Goals: " << var << " " << val << endl;
    }
    for( int var = 0; var < propositions_.size(); ++var ) {
        if( is_goal_var_[var] == false ) {
            for( int val = 0; val < propositions_[var].size(); ++val ) {
                propositions_[var][val]->set_goal(true);
            }
        }
    }
    cout << "Initialize: goals defined" << endl;

    // Define producers, consumers, prevail conditions
    for( int i = 0; i < operators_.size(); ++i ) {
        const std::vector<Prevail> &prevail = operators_[i]->op_.get_prevail();
        for( int j = 0; j < prevail.size(); ++j ) {
            int var = prevail[j].var;
            int prev = prevail[j].prev;
            propositions_[var][prev]->prevail_of_.push_back(operators_[i]);
            operators_[i]->prevails_.push_back(propositions_[var][prev]);
        }
        cout << "hola" << endl;
        const std::vector<PrePost> &pre_post = operators_[i]->op_.get_pre_post();
        for( int j = 0; j < pre_post.size(); ++j ) {
            int var = pre_post[j].var;
            int pre = pre_post[j].pre;
            int post = pre_post[j].post;
            cout << "var=" << var << ", pre=" << pre << ", post=" << post << endl;
            propositions_[var][pre]->consumed_by_.push_back(operators_[i]);
            operators_[i]->consumes_.push_back(propositions_[var][pre]);
            propositions_[var][post]->produced_by_.push_back(operators_[i]);
            operators_[i]->produces_.push_back(propositions_[var][post]);
        }
    }
    cout << "Initialize: producers, consumers, prevails defined" << endl;

    // Construct LP.
    osi_solver_ = new OsiClpSolverInterface();
    // if( lp_solver_ == "clp" ) {
    //     osi_solver_ = new OsiClpSolverInterface();
    // } else if( lp_solver_ == "grb" ) {
    //     osi_solver_ = new OsiGrbSolverInterface();
    // } else if( lp_solver_ == "cplex" ) {
    //     osi_solver_ = new OsiCpxSolverInterface();
    // }

#if 0
    bool pvalue;
    OsiHintStrength pstrength;

    osi_solver_->getHintParam(OsiDoPresolveInInitial, pvalue, pstrength);
    cout << "OsiDoPresolveInInitial = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    //osi_solver_->setHintParam(OsiDoDualInInitial, false);
    osi_solver_->getHintParam(OsiDoDualInInitial, pvalue, pstrength);
    cout << "OsiDoDualInInitial = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    //osi_solver_->setHintParam(OsiDoPresolveInResolve, true);
    osi_solver_->getHintParam(OsiDoPresolveInResolve, pvalue, pstrength);
    cout << "OsiDoPresolveInResolve = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    //osi_solver_->setHintParam(OsiDoDualInResolve, true);
    osi_solver_->getHintParam(OsiDoDualInResolve, pvalue, pstrength);
    cout << "OsiDoDualInResolve = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    //osi_solver_->setHintParam(OsiDoScale, false);
    osi_solver_->getHintParam(OsiDoScale, pvalue, pstrength);
    cout << "OsiDoScale = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    osi_solver_->getHintParam(OsiDoCrash, pvalue, pstrength);
    cout << "OsiDoCrash = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    osi_solver_->getHintParam(OsiDoReducePrint, pvalue, pstrength);
    cout << "OsiDoReducePrint = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;

    osi_solver_->getHintParam(OsiDoInBranchAndCut, pvalue, pstrength);
    cout << "OsiDoInBranchAndCut = (" << (pvalue ? 1 : 0) << "," << pstrength << ")" << endl;
#endif

    // Variables
    vector<double> osi_col_lb(operators_.size(), 0);
    vector<double> osi_col_ub(operators_.size(), osi_solver_->getInfinity());
    cout << "Initialize: LP variables" << endl;

    // Objective function.
    vector<double> osi_obj_fn(operators_.size(), 0);
    for( int i = 0; i < operators_.size(); ++i ) {
        osi_obj_fn[i] = operators_[i]->op_.get_cost();
    }
    cout << "Initialize: LP objective function" << endl;

    // Constraints.
    double *row_val = new double[1 + operators_.size()];
    int *row_ind = new int[1 + operators_.size()];
    CoinPackedMatrix *osi_matrix = new CoinPackedMatrix(false, 0, 0);
    osi_matrix->setDimensions(0, operators_.size());
    vector<CoinPackedVector*> osi_rows;

    nconstraints_ = 0;
    for( int var = 0; var < propositions_.size(); ++var ) {
        for( int val = 0; val < propositions_[var].size(); ++val ) {
            CoinPackedVector *osi_row = new CoinPackedVector(true);
            for( int i = 0; i < propositions_[var][val]->produced_by_.size(); ++i ) {
                int op_id = propositions_[var][val]->produced_by_[i]->get_id();
                osi_row->insert(op_id, 1);
            }
            for( int i = 0; i < propositions_[var][val]->consumed_by_.size(); ++i ) {
                int op_id = propositions_[var][val]->consumed_by_[i]->get_id();
                osi_row->insert(op_id, -1);
            }
            osi_rows.push_back(osi_row);
            ++nconstraints_;
        }
    }
    cout << "Initialize: LP constraints" << endl;

    // Add rows and create lb's and ub's for rows.
    osi_matrix->appendRows(osi_rows.size(), reinterpret_cast<CoinPackedVectorBase**>(&osi_rows[0]));
    vector<double> osi_row_lb(osi_rows.size(), 0), osi_row_ub(osi_rows.size(), 0);
    for( int i = 0; i < osi_rows.size(); ++i ) {
        osi_row_lb[i] = -1.0 * osi_solver_->getInfinity();
        osi_row_ub[i] = osi_solver_->getInfinity();
    }

    // Initialize solver and clean.
    osi_solver_->loadProblem(*osi_matrix, &osi_col_lb[0], &osi_col_ub[0], &osi_obj_fn[0], &osi_row_lb[0], &osi_row_ub[0]);
    osi_solver_->setObjSense(1);
    osi_solver_->messageHandler()->setLogLevel(0);
    osi_solver_->initialSolve();
    osi_solver_->writeLp("order_relaxed");
    for( int i = 0; i < osi_rows.size(); ++i ) {
        delete osi_rows[i];
    }
    delete osi_matrix;

    cout << "Initialize: finished with initialization" << endl;
}

int Heuristic::compute_heuristic(const State &state) {
    cout << "eval nr vars " << propositions_.size() << endl;

    // Set row bounds and type
    for( int var = 0; var < propositions_.size(); ++var ) {
        for( int val = 0; val < propositions_[var].size(); ++val ) {
            int row_id = propositions_[var][val]->get_id();
            bool is_goal = propositions_[var][val]->is_goal();
            double lower_bound = 0;
            double upper_bound = 0;

            if( is_goal_var_[var] == true ) { // there is a unique goal state
                if( state[var] == val && is_goal == true ) {
                    lower_bound = 0;
                    upper_bound = 0;
                } else if( state[var] == val && is_goal == false ) {
                    lower_bound = -1;
                    upper_bound = -1;
                } else if( state[var] != val && is_goal == true ) {
                    lower_bound = 1;
                    upper_bound = 1;
                } else if( state[var] != val && is_goal == false ) {
                    lower_bound = 0;
                    upper_bound = 0;
                }
            } else { // there is *no* unique goal state
                if( state[var] == val && is_goal == true ) {
                    lower_bound = -1;
                    upper_bound = osi_solver_->getInfinity();
                } else if( state[var] == val && is_goal == false ) {
                    lower_bound = -1;
                    upper_bound = -1;
                } else if( state[var] != val && is_goal == true ) {
                    lower_bound = 0;
                    upper_bound = osi_solver_->getInfinity();
                } else if( state[var] != val && is_goal == false ) {
                    lower_bound = 0;
                    upper_bound = 0;
                }
            }

            //cout << row_id << " :: " << var << " " << val << " g gv " << is_goal << " " << is_goal_var_[var] << " lb ub " << lower_bound << " " << upper_bound << endl;
            osi_solver_->setRowLower(row_id, lower_bound);
            osi_solver_->setRowUpper(row_id, upper_bound);
        }
    }

    // Call LP solver. If unfeasible, return DEAD_END
    int rv = -1, heuristic_value = -1;
#ifdef DEBUG
    cout << "calling LP solver..." << flush;
#endif
    try {
        osi_solver_->resolve();
        osi_solver_->writeLp("state_equation_updated");
        rv = osi_solver_->isProvenPrimalInfeasible();

#if 0
        if( osi_solver_->isAbandoned() ) cout << "ABANDONED" << endl;
        if( osi_solver_->isProvenOptimal() ) cout << "OPTIMAL" << endl;
        if( osi_solver_->isProvenPrimalInfeasible() ) cout << "PRIMAL INFEASIBLE" << endl;
        if( osi_solver_->isProvenDualInfeasible() ) cout << "DUAL INFEASIBLE" << endl;
        if( osi_solver_->isPrimalObjectiveLimitReached() ) cout << "PRIMAL LIMIT" << endl;
        if( osi_solver_->isDualObjectiveLimitReached() ) cout << "DUAL LIMIT" << endl;
        if( osi_solver_->isIterationLimitReached() ) cout << "ITERATION LIMIT" << endl;

        if( osi_solver_->isProvenPrimalInfeasible() ) {
            assert(rv == 1);
        } else {
            assert(rv == 0);
        }
#endif

#if 1 // Menkes
        int ncols = osi_solver_->getNumCols();
        const double *solution = osi_solver_->getColSolution();
        cout << "Solution: value=" << (float)osi_solver_->getObjValue() << ", x*=[" << endl;
        for( int i = 0; i < ncols; ++i ) {
            if( (float)solution[i] > 0 ) {
                cout << " (" << operators_[i]->op_.get_name() << ")=" << solution[i] << ", cost=" << operators_[i]->op_.get_cost() << endl;
                //cout << solution[i] << ", ";
            }
        }
        cout << "]" << endl;
#endif
    } catch( CoinError &ex ) {
        cerr << "Exception:" << ex.message() << endl
             << " from method " << ex.methodName() << endl
             << " from class " << ex.className() << endl;
             exit(0);
    }
#ifdef DEBUG
    cout << " done (rv=" << rv << ")" << endl;
#endif

    // Compute heuristic
    if( rv == 0 ) {
        double obj_value = 0.0;
        obj_value = osi_solver_->getObjValue();
        heuristic_value = (int)ceilf((float)obj_value);
    } else {
        heuristic_value = DEAD_END;
    }

    return heuristic_value;
}

void MetaProposition::dump(ostream &os) const {
    os << id_ << " :: " << var_ << " " << val_ << endl;
}

ScalarEvaluator *_parse(OptionParser &parser) {
    parser.add_option<int>("merge_fluents", 0, "merge fluents: 0=no merge, 1=naive");
    parser.add_option<string>("lp_solver", string("clp"), string("\"clp\" (default), \"grb\", \"cplex\""));

    Heuristic::add_options_to_parser(parser);
    Options opts = parser.parse();

    string lp = opts.get<string>("lp_solver");
    if( (lp != "clp") && (lp != "grb") && (lp != "cplex") ) {
        parser.error("unknown lp-solver");
    }

    return parser.dry_run() ? 0 : new Heuristic(opts);
}

Plugin<ScalarEvaluator> _plugin("menkes_state_equation", _parse);

} // end of namespace

