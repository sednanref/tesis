#include "state_equation_heuristic.h"

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

#ifdef CLP
#include <OsiClpSolverInterface.hpp>
#endif
#ifdef CPLEX
#include <OsiCpxSolverInterface.hpp>
#endif
#ifdef GUROBI
#include <OsiGrbSolverInterface.hpp>
#endif

#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused"

#define ROW_LE      0
#define ROW_EQ      1
#define ROW_GE      2
#define ROW_DB      3
#define BIG_M       100000
#define SMALL_M     0.1

using namespace std;

//#define DEBUG

// encapsulate the heuristic into its own namespace
namespace StateEquation {

const set<int>& Heuristic::get_achievers(int lmn_status, LandmarkNode &lmn) {
    /*
     * Return the achievers of the landmark, according to its status.
     * Returns first achievers for non-reached landmarks
     * Returns all achievers for needed again landmarks
     * Return an empty set for reached landmarks (that are not accepted)
     */
    if( lmn_status == lm_not_reached ) {
        return lmn.first_achievers;
    } else if( lmn_status == lm_needed_again ) {
        return lmn.possible_achievers;
    } else {
        return empty_lm_set_;
    }
}

// construction and destruction
Heuristic::Heuristic(const Options &opts)
    : ::Heuristic(opts),
      landmarks_(opts.get<int>("landmarks")),
      use_1safe_information_(opts.get<bool>("use_1safe_information")),
      use_prevails_(opts.get<bool>("use_prevails")),
      merge_fluents_(opts.get<int>("merge_fluents")),
      lp_solver_(opts.get<string>("lp_solver")) {
    //push_histogram(new Utils::Histogram("seq2"));
    M_ = 0;
    hmax_heuristic_ = 0;
    lmcut_engine_ = 0;
    lm_graph_ = 0;
    lm_status_manager_ = 0;

    if( landmarks_ & 0x1 ) {
        lm_graph_ = new LandmarkGraph(*opts.get<LandmarkGraph *>("lm_graph"));
        lm_status_manager_ = new LandmarkStatusManager(*lm_graph_);
    }
    if( landmarks_ & 0x2 ) {
        lmcut_engine_ = new HittingSets::LMCutEngine(rproblem_);
    }
}

Heuristic::~Heuristic() {
    delete hmax_heuristic_;
    delete M_;
}

// initialization
void Heuristic::initialize() {
    cout << "Initializing State_Equation (ver 2) heuristic:"
         << " using_1-safe_information=" << (use_1safe_information_ ? 1 : 0)
         << ", use_prevails=" << (use_prevails_ ? 1 : 0)
         << ", merge_fluents=" << merge_fluents_;

    if( landmarks_ & 0x1 )
        cout << ", landmarks(LA)";
    if( landmarks_ & 0x2 )
        cout << ", landmarks(LM-CUT)";

    cout << ", LP-kit=osi:" << lp_solver_ << endl;

    // Framework does not support axioms or conditional effects
    ::verify_no_axioms_no_cond_effects();

    // Extract SAS variables and operators.
    sas_variables_.reserve(g_variable_domain.size());
    for( int var = 0; var < g_variable_domain.size(); ++var ) {
        sas_variables_.push_back(g_variable_domain[var]);
    }
    num_primitive_vars_ = sas_variables_.size();

    sas_operators_.reserve(g_operators.size());
    for( int i = 0; i < g_operators.size(); ++i) {
        Operator &op = g_operators[i];
        sas_operators_.push_back(new SASOperator(op));
    }

    // Merge fluents.
    if( merge_fluents_ > 0 ) {
        cout << "# variables before merging = " << sas_variables_.size() << endl;
        cout << "# operators before merging = " << sas_operators_.size() << endl;
        vector<int> estimation;
        vector<int> prevails(sas_variables_.size(), 0);
        vector<bool> merged(sas_variables_.size(), false);
        compute_prevails(prevails, merged);
        calculate_merge_estimation(prevails, estimation);
        pair<int, int> merge = choose_variables_to_merge(prevails, merged, estimation);
        while( merge.first != -1 ) {
            assert(merge.second != -1);
            cout << "Merging: v" << merge.first << " (sz=" << sas_variables_[merge.first]
                 << ") with v" << merge.second << " (sz=" << sas_variables_[merge.second]
                 << ")" << endl;

            // create new (merged) variable and domain
            merged_vars_.push_back(merge);
            int new_var = sas_variables_.size();
            sas_variables_.push_back(sas_variables_[merge.first] * sas_variables_[merge.second]);

            // update operators
            vector<SASOperator*> old_sas_operators = sas_operators_;
            vector<bool> good_sas_operators(sas_operators_.size(), true);
            size_t new_ops = calculate_number_new_operators(merge, good_sas_operators);
            sas_operators_.clear();
            sas_operators_.reserve(sas_operators_.size() + new_ops);
            for( int i = 0; i < old_sas_operators.size(); ++i ) {
                if( good_sas_operators[i] ) {
                    sas_operators_.push_back(old_sas_operators[i]);
                } else {
                    create_new_operators(*old_sas_operators[i], merge, new_var);
                    delete old_sas_operators[i];
                }
            }

            // pick another merge
            prevails.resize(sas_variables_.size(), 0);
            merged.resize(sas_variables_.size(), true);
            merged[merge.first] = merged[merge.second] = true;
            merge = choose_variables_to_merge(prevails, merged, estimation);
            //if( merged_vars_.size() == 1 ) merge=make_pair(sas_variables_.size() - 1, 2);
            //if( merged_vars_.size() == 2 ) break;
        }
        cout << "# operators after merging = " << sas_operators_.size() << endl;
        cout << "# variables after merging = " << sas_variables_.size() << endl;

        //prevails.resize(sas_variables_.size(), 0);
        //merged.resize(sas_variables_.size(), false);
        //compute_prevails(prevails, merged);
    }

    // Build propositions.
    num_propositions_ = 0;
    propositions_.resize(sas_variables_.size());
    ordered_propositions_.resize(2 * sas_variables_.size());
    for(int var = 0; var < sas_variables_.size(); var++) {
        propositions_[var].reserve(sas_variables_[var]);
        for(int value = 0; value < sas_variables_[var]; value++) {
            propositions_[var].push_back(Proposition(num_propositions_, var, value));
            ordered_propositions_.push_back(Proposition(num_propositions_, var, value));
            ++num_propositions_;
        }
    }

    // Build operators.
    safe_to_max_with_hmax_ = true;
    one_safe_ = vector<bool>(sas_variables_.size(), true);
    operators_.reserve(sas_operators_.size());
    for( int i = 0; i < sas_operators_.size(); ++i )
        build_operator(*sas_operators_[i]);
    cout << "safe_to_max_with_hmax=" << (safe_to_max_with_hmax_ ? 1 : 0) << endl;

    // Cross-reference strips operators.
    for( int i = 0; i < operators_.size(); ++i) {
        PCOperator *op = &operators_[i];
        for( int j = 0; j < op->produces_.size(); j++ )
            op->produces_[j]->produced_by_.push_back(i);
        for( int j = 0; j < op->consumes_.size(); j++ )
            op->consumes_[j]->consumed_by_.push_back(i);

        const vector<Prevail> &prevail = op->op_->prevail_;
        for( int j = 0; j < prevail.size(); ++j ) {
            Proposition &prop = propositions_[prevail[j].var][prevail[j].prev];
            prop.prevail_of_.push_back(i);
        }
    }

    // Initialize goal state.
    goal_state_ = vector<state_var_t>(sas_variables_.size(), (state_var_t)-1);
    for( int i = 0; i < g_goal.size(); ++i ) {
        goal_state_[g_goal[i].first] = g_goal[i].second;
    }
    for( int i = 0; i < merged_vars_.size(); ++i ) {
        if( has_value(num_primitive_vars_ + i, goal_state_) ) {
            int value = get_state_value(num_primitive_vars_ + i, goal_state_);
            goal_state_[num_primitive_vars_ + i] = value;
        }
    }

    M_ = new IncidenceMatrixForPN(num_propositions_, operators_.size(), edges_.size());

    // Calculate rows.
    for( int var = 0; var < sas_variables_.size(); var++) {
        for( int value = 0; value < sas_variables_[var]; value++ ) {
            vector<int> row;
            const Proposition &prop = propositions_[var][value];
            for( int i = 0; i < prop.produced_by_.size(); ++i ) {
                row.push_back(1 + prop.produced_by_[i]);
            }
            for( int i = 0; i < prop.consumed_by_.size(); ++i ) {
                row.push_back(-(1 + prop.consumed_by_[i]));
            }
            M_->rows_[prop.index_] = row;
        }
    }

    // Construct LP.
    osi_solver_ = 0;
    if( lp_solver_ == "clp" ) {
#ifdef CLP
        osi_solver_ = new OsiClpSolverInterface();
#endif
    } else if( lp_solver_ == "cplex" ) {
#ifdef CPLEX
        osi_solver_ = new OsiCpxSolverInterface();
#endif
    } else if( lp_solver_ == "grb" ) {
#ifdef GUROBI
        osi_solver_ = new OsiGrbSolverInterface();
#endif
    }

    if( osi_solver_ == 0 ) {
        cout << "error: lp_solver '" << lp_solver_ << "' not loaded!" << endl;
        exit(-1);
    }

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

    // Objective function.
    vector<double> osi_obj_fn((use_prevails_ ? 3 : 1) * M_->ntransitions_, 0);
    vector<double> osi_col_lb((use_prevails_ ? 3 : 1) * M_->ntransitions_, 0);
    vector<double> osi_col_ub((use_prevails_ ? 3 : 1) * M_->ntransitions_, osi_solver_->getInfinity());
    for( int t = 0; t < M_->ntransitions_; ++t ) {
        osi_obj_fn[t] = operators_[t].base_cost_;
    }

    // Constraints.
    double *row_val = new double[1 + M_->ntransitions_];
    int *row_ind = new int[1 + M_->ntransitions_];
    CoinPackedMatrix *osi_matrix = new CoinPackedMatrix(false, 0, 0);
    osi_matrix->setDimensions(0, (use_prevails_ ? 3 : 1) * M_->ntransitions_);
    vector<CoinPackedVector*> osi_rows;

    nconstraints_ = 0;
    for( int var = 0; var < propositions_.size(); ++var ) {
        for( int value = 0; value < propositions_[var].size(); ++value ) {
            Proposition &prop = propositions_[var][value];
            const vector<int> &row = M_->rows_[prop.index_];
            if( !row.empty() ) {
                int j = 0;
                vector<int> rmap(M_->ntransitions_, -1);
                for( int i = 0; i < row.size(); ++i ) {
                    bool produces = row[i] > 0;
                    int index = row[i] > 0 ? row[i] - 1: -row[i] - 1;
                    if( rmap[index] == -1 ) {
                        row_ind[1 + j] = 1 + index;
                        row_val[1 + j] = produces ? 1.0 : -1.0;
                        rmap[index] = ++j;
                    } else {
                        row_val[rmap[index]] += produces ? 1.0 : -1.0;
                    }
                }
                CoinPackedVector *osi_row = new CoinPackedVector(true);
                for( int i = 0; i < j; ++i ) {
                    osi_row->insert(row_ind[1 + i] - 1, row_val[1 + i]);
                }
                osi_rows.push_back(osi_row);
                prop.row_index_ = nconstraints_;
                ordered_propositions_[prop.index_].row_index_ = nconstraints_;
                ++nconstraints_;
            }
        }
    }

    // Add constraints for prevail conditions.
    int begin_prevail_constraints = osi_rows.size();
    int begin_prevail_constraints_type2 = osi_rows.size();

    if( use_prevails_ ) {
        int base = M_->ntransitions_;
        // Variables associated with action a:
        //     1. x(a) = a
        //     2. hat(a) = base + a
        //     3. slack(a) = 2*base + a

        // Add constraints for defined variables hat(a) and slack(a):
        //     1. hat(a) <= 1 - x(a) + slack(a)
        //     2. hat(a) >= 1 - x(a)
        //     3. hat(a) >= 0, slack(a) >= 0
        for( int t = 0; t < M_->ntransitions_; ++t ) {
            if( true || !operators_[t].op_->prevail_.empty() ) {
                CoinPackedVector *osi_row_1 = new CoinPackedVector(true);
                osi_row_1->insert(base + t, 1); // +hat(a)
                osi_row_1->insert(t, 1); // +x(a)
                osi_row_1->insert(2*base + t, -1); // -slack(a)
                osi_rows.push_back(osi_row_1);
                ++nconstraints_;

                CoinPackedVector *osi_row_2 = new CoinPackedVector(true);
                osi_row_2->insert(base + t, 1); // +hat(a)
                osi_row_2->insert(t, 1); // +x(a)
                osi_rows.push_back(osi_row_2);
                ++nconstraints_;
            }
        }
        begin_prevail_constraints_type2 = osi_rows.size();

        // Add constraints for prevail p of action a:
        //     1. \sum_{a' in O(p)} x(a') >= 1 - hat(a)
        prevail_constraints_.reserve(M_->ntransitions_);
        for( int t = 0; t < M_->ntransitions_; ++t ) {
            const PCOperator &op = operators_[t];
            const vector<Prevail> &prevail = op.op_->prevail_;
            prevail_constraints_.push_back(map<int, int>());
            for( int i = 0; i < prevail.size(); i++ ) {
                const Proposition &prop = propositions_[prevail[i].var][prevail[i].prev];
                CoinPackedVector *osi_row = new CoinPackedVector(true);
                for( int j = 0; j < prop.produced_by_.size(); ++j ) {
                    osi_row->insert(prop.produced_by_[j], 1); // +x(a')
                }
                osi_row->insert(base + t, 1); // +hat(a)
                osi_rows.push_back(osi_row);
                prevail_constraints_[t][prop.index_] = nconstraints_;
                ++nconstraints_;
            }
        }

        // Modify objective function by adding terms M * slack(a) for each action a.
        for( int t = 0; t < M_->ntransitions_; ++t ) {
            //osi_obj_fn[base + t] = 0.1;
            osi_obj_fn[2*base + t] = BIG_M;
        }
    }

    // Add rows and create lb's and ub's for rows.
    osi_matrix->appendRows(osi_rows.size(), reinterpret_cast<CoinPackedVectorBase**>(&osi_rows[0]));
    vector<double> osi_row_lb(osi_rows.size(), 0), osi_row_ub(osi_rows.size(), 0);
    for( int i = 0; i < begin_prevail_constraints; ++i ) {
        osi_row_lb[i] = -1.0 * osi_solver_->getInfinity();
        osi_row_ub[i] = osi_solver_->getInfinity();
    }
    if( use_prevails_ ) {
        for( int i = 0; i < M_->ntransitions_; ++i ) {
            if( true || !operators_[i].op_->prevail_.empty() ) {
                osi_row_lb[begin_prevail_constraints + 2*i] = -1.0 * osi_solver_->getInfinity();
                osi_row_ub[begin_prevail_constraints + 2*i] = 1.0;
                osi_row_lb[begin_prevail_constraints + 2*i + 1] = 1.0;
                osi_row_ub[begin_prevail_constraints + 2*i + 1] = osi_solver_->getInfinity();
            }
        }
        for( int i = begin_prevail_constraints_type2; i < osi_rows.size(); ++i ) {
            osi_row_lb[i] = 1.0;
            osi_row_ub[i] = osi_solver_->getInfinity();
        }
    }

    // Initialize solver and clean.
    osi_solver_->loadProblem(*osi_matrix, &osi_col_lb[0], &osi_col_ub[0], &osi_obj_fn[0], &osi_row_lb[0], &osi_row_ub[0]);
    osi_solver_->setObjSense(1);
    osi_solver_->messageHandler()->setLogLevel(0);
    osi_solver_->initialSolve();
    for( int i = 0; i < osi_rows.size(); ++i ) {
        delete osi_rows[i];
    }
    delete osi_matrix;

    // Create and initialize hmax heuristic.
    if( safe_to_max_with_hmax_ && !(landmarks_ & 0x2) ) {
        Options opts;
        opts.set<int>("cost_type", 0);
        hmax_heuristic_ = new HSPMaxHeuristic(opts);
        hmax_heuristic_->initialize();
    }

    // Initialize landmark engine (LA).
    if( landmarks_ & 0x1 ) {
        lm_status_manager_->set_landmarks_for_initial_state();
        la_opmap_ = vector<int>(g_operators.size(), -1);
        for( int i = 0; i < g_operators.size(); ++i ) {
            //const Operator& op = lgraph_->get_operator_for_lookup_index(op_id);
            for( int j = 0; j < operators_.size(); ++j ) {
                if( operators_[j].op_->op_ == &g_operators[i] ) {
                    la_opmap_[i] = j;
                    break;
                }
            }
        }
        for( int i = 0; i < g_operators.size(); ++i ) {
            if( la_opmap_[i] == -1 ) {
                cout << "Error: cross-reference between (LA) landmarks operators failed!" << endl;
                exit(-1);
            }
        }
    }

    // Initialize landmark engine (LM-Cut).
    if( landmarks_ & 0x2 ) {
        rproblem_.initialize();
        lmcut_engine_->initialize(1, true);
        lmcut_opmap_ = vector<int>(rproblem_.operators_.size(), -1);
        for( int i = 0; i < rproblem_.operators_.size(); ++i ) {
            for( int j = 0; j < operators_.size(); ++j ) {
                if( (rproblem_.operators_[i].op_ != 0) && (rproblem_.operators_[i].op_ == operators_[j].op_->op_) ) {
                    lmcut_opmap_[i] = j;
                    break;
                }
            }
        }
        for( int i = 0; i < rproblem_.operators_.size(); ++i ) {
            if( (rproblem_.operators_[i].op_ != 0) && (lmcut_opmap_[i] == -1) ) {
                cout << "Error: cross-reference between (LM-Cut) landmarks operators failed!" << endl;
                exit(-1);
            }
        }
    }
    cout << "finished with initialization" << endl;
}

void Heuristic::compute_prevails(vector<int> &prevails, const vector<bool> &merged) const {
    prevails = vector<int>(sas_variables_.size(), 0);
    for( int var = 0; var < sas_variables_.size(); ++var ) {
        if( merged[var] ) continue;
        for( int i = 0; i < sas_operators_.size(); ++i) {
            SASOperator &op = *sas_operators_[i];
            const vector<Prevail> &prevail = op.prevail_;
            for( int j = 0; j < prevail.size(); ++j ) {
                if( prevail[j].var == var ) {
                    ++prevails[var];
                    break;
                }
            }
        }
        //if( prevails[var] ) cout << "var" << var << " is prevail in " << prevails[var] << " operators!" << endl;
    }
}

pair<int, int> Heuristic::get_var_types(const SASOperator &op, int var1, int var2) const {
    const vector<Prevail> &prevail = op.prevail_;
    const vector<PrePost> &pre_post = op.pre_post_;

    // Types:  0=doesn't appear, 1=defined in prevail, 2=undefined in pre/post, 3=defined in pre/post
    int type1 = 0;
    int type2 = 0;
    for( int j = 0; j < prevail.size(); ++j ) {
        if( prevail[j].var == var1 ) type1 = 1;
        if( prevail[j].var == var2 ) type2 = 1;
    }
    for( int j = 0; j < pre_post.size(); ++j ) {
        if( (pre_post[j].var == var1) && (pre_post[j].pre == -1) ) type1 = 2;
        if( (pre_post[j].var == var1) && (pre_post[j].pre != -1) ) type1 = 3;
        if( (pre_post[j].var == var2) && (pre_post[j].pre == -1) ) type2 = 2;
        if( (pre_post[j].var == var2) && (pre_post[j].pre != -1) ) type2 = 3;
    }

    return make_pair(type1, type2);
}

size_t Heuristic::get_prevail_count(const pair<int, int> &type, int dom1, int dom2) const {
    if( (type.first == 0) & (type.second == 1) )
        return 1;//dom1 - 1;
    else if( (type.first == 1) && (type.second == 0) )
        return 1;//dom2 - 1;
    else if( (type.first == 1) && (type.second == 1) )
        return 1;
    else
        return 0;
}

size_t Heuristic::get_operator_count(const pair<int, int> &type, int dom1, int dom2) const {
    if( type.first == 0 ) {
        return type.second == 0 ? 0 : dom1 - 1;
    } else if( type.first == 1 ) {
        return type.second == 0 ? dom2 - 1 : 0;
    } else if( type.first == 2 ) {
        return type.second == 0 ? dom2 - 1 : 0;
    } else if( type.first == 3 ) {
        return type.second == 0 ? dom2 - 1 : 0;
    }
    return 0;
}

int Heuristic::get_var_value(const vector<Prevail> &prevail, int var) const {
    for( int i = 0; i < prevail.size(); ++i ) {
        if( prevail[i].var == var ) return prevail[i].prev;
    }
    cout << "ERROR" << endl; exit(0);
    return -1;
}

pair<int, int> Heuristic::get_var_value(const vector<PrePost> &pre_post, int var) const {
    for( int i = 0; i < pre_post.size(); ++i ) {
        if( pre_post[i].var == var ) return make_pair(pre_post[i].pre, pre_post[i].post);
    }
    cout << "ERROR" << endl; exit(0);
    return make_pair(-1, -1);
}

void Heuristic::calculate_merge_estimation(const vector<int> &prevails,
                                           vector<int> &estimation) const {
    estimation = vector<int>(sas_variables_.size() * sas_variables_.size(), 0);
    for( int var1 = 0; var1 < sas_variables_.size(); ++var1 ) {
        if( prevails[var1] == 0 ) continue;
        int dom1 = sas_variables_[var1];
        for(int var2 = 0; var2 < sas_variables_.size(); var2++) {
            if( var1 == var2 ) continue;
            int dom2 = sas_variables_[var2];
            int index = var1 * sas_variables_.size() + var2;
            for( int i = 0; i < sas_operators_.size(); ++i) {
                pair<int, int> type = get_var_types(*sas_operators_[i], var1, var2);
                estimation[index] += get_prevail_count(type, dom1, dom2);
            }
            //cout << "[var1=" << var1 << "(sz=" << sas_variables_[var1] << "),var2=" << var2 << "(sz=" << sas_variables_[var2] << ")] estimation = " << estimation[index] << endl;
        }
    }
}

pair<int,int> Heuristic::choose_variables_to_merge(const vector<int> &prevails,
                                                   const vector<bool> &merged,
                                                   const vector<int> &estimation) const {
    int best = -1;
    for( int var1 = 0; var1 < prevails.size(); ++var1 ) {
        if( (prevails[var1] == 0) || merged[var1] ) continue;
        for( int var2 = 0; var2 < prevails.size(); ++var2 ) {
            if( (var1 == var2) || merged[var2] ) continue;
            unsigned dom_prod = sas_variables_[var1] * sas_variables_[var2];
            if( dom_prod >= (state_var_t)-1 ) continue;
            int index = var1 * prevails.size() + var2;
            if( (best == -1) || (estimation[index] < estimation[best]) ) {
                best = index;
            }
        }
    }

    if( best != -1 ) {
        int var1 = best / prevails.size(), var2 = best % prevails.size();
        //cout << "[var1=" << var1 << ",var2=" << var2 << "] best = " << estimation[best] << endl;
        return make_pair(var1, var2);
    } else {
        return make_pair(-1, -1);
    }
}

size_t Heuristic::calculate_number_new_operators(const pair<int, int> &merge, vector<bool> &good_operators) const {
    size_t total_count = 0;
    int var1 = merge.first, var2 = merge.second;
    int dom1 = sas_variables_[var1], dom2 = sas_variables_[var2];
    for( int i = 0; i < sas_operators_.size(); ++i) {
        pair<int, int> type = get_var_types(*sas_operators_[i], var1, var2);
        size_t count = get_operator_count(type, dom1, dom2);
        good_operators[i] = (type.first == 0) && (type.second == 0);
        total_count += count;
    }
    return total_count;
}

void Heuristic::create_new_operators(const SASOperator &op, const pair<int, int> &merge, int new_var, bool swap) {
    vector<Prevail> empty_cond;
    pair<int, int> type = get_var_types(op, merge.first, merge.second);
    //cout << "create_new_operators: op=(" << op.op_->get_name() << ")" << ", types=(" << type.first << "," << type.second << ")";
    assert((type.first != 0) || (type.second != 0));

    // Types:  0=doesn't appear, 1=defined in prevail, 2=undefined in pre/post, 3=defined in pre/post
    if( type.first == 0 ) {
        if( type.second == 0 ) {
            cout << "Error: type (0,0) should not appear here" << endl;
            exit(1);
        } else if( type.second == 1 ) {
            //cout << ", n=" << sas_variables_[merge.first] << endl;
            int val2 = get_var_value(op.prevail_, merge.second);
            for( int val1 = 0; val1 < sas_variables_[merge.first]; ++val1 ) {
                int new_value = !swap ? val1 * sas_variables_[merge.second] + val2 : val2 * sas_variables_[merge.first] + val1;
                vector<Prevail> new_prevail = op.prevail_;
                Prevail prev1(merge.first, val1);
                Prevail prev2(new_var, new_value);
                new_prevail.push_back(prev1);
                new_prevail.push_back(prev2);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, op.pre_post_, op.cost_));
            }
        } else if( type.second == 2 ) {
            //cout << ", n=" << sas_variables_[merge.first] << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            for( int val1 = 0; val1 < sas_variables_[merge.first]; ++val1 ) {
                int new_value_pre = -1;
                int new_value_post = !swap ? val1 * sas_variables_[merge.second] + val2.second : val2.second * sas_variables_[merge.first] + val1;
                vector<Prevail> new_prevail = op.prevail_;
                vector<PrePost> new_pre_post = op.pre_post_;
                Prevail prev(merge.first, val1);
                PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
                new_prevail.push_back(prev);
                new_pre_post.push_back(ppost);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, new_pre_post, op.cost_));
            }
        } else if( type.second == 3 ) {
            //cout << ", n=" << sas_variables_[merge.first] << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            for( int val1 = 0; val1 < sas_variables_[merge.first]; ++val1 ) {
                int new_value_pre = !swap ? val1 * sas_variables_[merge.second] + val2.first : val2.first * sas_variables_[merge.first] + val1;
                int new_value_post = !swap ? val1 * sas_variables_[merge.second] + val2.second : val2.second * sas_variables_[merge.first] + val1;
                vector<Prevail> new_prevail = op.prevail_;
                vector<PrePost> new_pre_post = op.pre_post_;
                Prevail prev(merge.first, val1);
                PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
                new_prevail.push_back(prev);
                new_pre_post.push_back(ppost);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, new_pre_post, op.cost_));
            }
        }
    } else if( type.first == 1 ) {
        int val1 = get_var_value(op.prevail_, merge.first);
        if( type.second == 0 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=" << sas_variables_[merge.second] << endl;
            for( int val2 = 0; val2 < sas_variables_[merge.second]; ++val2 ) {
                int new_value = val1 * sas_variables_[merge.second] + val2;
                vector<Prevail> new_prevail = op.prevail_;
                Prevail prev1(merge.second, val2);
                Prevail prev2(new_var, new_value);
                new_prevail.push_back(prev1);
                new_prevail.push_back(prev2);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, op.pre_post_, op.cost_));
            }
#endif
        } else if( type.second == 1 ) {
            //cout << ", n=1" << endl;
            int val2 = get_var_value(op.prevail_, merge.second);
            int new_value = val1 * sas_variables_[merge.second] + val2;
            vector<Prevail> new_prevail = op.prevail_;
            Prevail prev(new_var, new_value);
            new_prevail.push_back(prev);
            sas_operators_.push_back(new SASOperator(op.op_, new_prevail, op.pre_post_, op.cost_));
        } else if( type.second == 2 ) {
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = -1;
            int new_value_post = !swap ? val1 * sas_variables_[merge.second] + val2.second : val2.second * sas_variables_[merge.first] + val1;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
        } else if( type.second == 3 ) {
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = !swap ? val1 * sas_variables_[merge.second] + val2.first : val2.first * sas_variables_[merge.first] + val1;
            int new_value_post = !swap ? val1 * sas_variables_[merge.second] + val2.second : val2.second * sas_variables_[merge.first] + val1;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(ppost);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
        }
    } else if( type.first == 2 ) {
        pair<int, int> val1 = get_var_value(op.pre_post_, merge.first);
        if( type.second == 0 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=" << sas_variables_[merge.second] << endl;
            for( int val2 = 0; val2 < sas_variables_[merge.second]; ++val2 ) {
                int new_value_pre = -1;
                int new_value_post = val1.second * sas_variables_[merge.second] + val2;
                vector<Prevail> new_prevail = op.prevail_;
                vector<PrePost> new_pre_post = op.pre_post_;
                Prevail prev(merge.second, val2);
                PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
                new_prevail.push_back(prev);
                new_pre_post.push_back(ppost);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, new_pre_post, op.cost_));
            }
#endif
        } else if( type.second == 1 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=1" << endl;
            int val2 = get_var_value(op.prevail_, merge.second);
            int new_value_pre = -1;
            int new_value_post = val1.second * sas_variables_[merge.second] + val2;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
#endif
        } else if( type.second == 2 ) {
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = -1;
            int new_value_post = val1.second * sas_variables_[merge.second] + val2.second;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
        } else if( type.second == 3 ) {
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = -1;
            int new_value_post = !swap ? val1.second * sas_variables_[merge.second] + val2.second : val2.second * sas_variables_[merge.first] + val1.second;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
        }
    } else if( type.first == 3 ) {
        pair<int, int> val1 = get_var_value(op.pre_post_, merge.first);
        if( type.second == 0 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=" << sas_variables_[merge.second] << endl;
            for( int val2 = 0; val2 < sas_variables_[merge.second]; ++val2 ) {
                int new_value_pre = val1.first * sas_variables_[merge.second] + val2;
                int new_value_post = val1.second * sas_variables_[merge.second] + val2;
                vector<Prevail> new_prevail = op.prevail_;
                vector<PrePost> new_pre_post = op.pre_post_;
                Prevail prev(merge.second, val2);
                PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
                new_prevail.push_back(prev);
                new_pre_post.push_back(ppost);
                sas_operators_.push_back(new SASOperator(op.op_, new_prevail, new_pre_post, op.cost_));
            }
#endif
        } else if( type.second == 1 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=1" << endl;
            int val2 = get_var_value(op.prevail_, merge.second);
            int new_value_pre = val1.first * sas_variables_[merge.second] + val2;
            int new_value_post = val1.second * sas_variables_[merge.second] + val2;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost ppost(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(ppost);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
#endif
        } else if( type.second == 2 ) {
            create_new_operators(op, make_pair(merge.second, merge.first), new_var, true);
#if 0
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = -1;
            int new_value_post = val1.second * sas_variables_[merge.second] + val2.second;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
#endif
        } else if( type.second == 3 ) {
            //cout << ", n=1" << endl;
            pair<int, int> val2 = get_var_value(op.pre_post_, merge.second);
            int new_value_pre = val1.first * sas_variables_[merge.second] + val2.first;
            int new_value_post = val1.second * sas_variables_[merge.second] + val2.second;
            vector<PrePost> new_pre_post = op.pre_post_;
            PrePost p(new_var, new_value_pre, new_value_post, empty_cond);
            new_pre_post.push_back(p);
            sas_operators_.push_back(new SASOperator(op.op_, op.prevail_, new_pre_post, op.cost_));
        }
    }
}

void Heuristic::build_operator(const SASOperator &op) {
    int base_cost = op.cost_;
    const vector<Prevail> &prevail = op.prevail_;
    const vector<PrePost> &pre_post = op.pre_post_;

    set<Proposition*> produces;
    set<Proposition*> consumes;
    set<Proposition*> prevails;

    // Index of this new operator when inserted.
    int op_index = operators_.size();
#ifdef DEBUG
    cout << "Operator id=" << op_index << " '" << op.op_->get_name() << "':" << endl;
#endif

    // Prevail conditions.
    for( int i = 0; i < prevail.size(); i++ ) {
        Proposition &prop = propositions_[prevail[i].var][prevail[i].prev];
        prevails.insert(&prop);

        //consumes.insert(&prop);
        edges_.push_back(Edge(edges_.size(), Edge::PT, prop.index_, op_index));
#ifdef DEBUG
        cout << "    consumes: v" << prevail[i].var << " = " << prevail[i].prev << endl;
#endif

        //produces.insert(&prop);
        edges_.push_back(Edge(edges_.size(), Edge::TP, op_index, prop.index_));
#ifdef DEBUG
        cout << "    produces: v" << prevail[i].var << " = " << prevail[i].prev << endl;
#endif
    }

    // Pre-post conditions.
    for( int i = 0; i < pre_post.size(); i++ ) {
        const vector<Prevail> &cond = pre_post[i].cond;
        if( !cond.empty() ) {
            // Accept conditions that are redundant, but nothing else.
            // In a better world, these would never be included in the
            // input in the first place.
            int var = pre_post[i].var;
            int post = pre_post[i].post;
            if( cond.size() != 1 || cond[0].var != var ||
                sas_variables_[var] != 2 || cond[0].prev == post ) {
                cerr << "Framework does not support conditional effects "
                     << "(operator " << op.op_->get_name() << ")"
                     << endl << "Terminating." << endl;
                exit(1);
            }
        }

        if( pre_post[i].pre != -1 ) {
            Proposition &prop_pre = propositions_[pre_post[i].var][pre_post[i].pre];
            consumes.insert(&prop_pre);
            edges_.push_back(Edge(edges_.size(), Edge::PT, prop_pre.index_, op_index));
#ifdef DEBUG
            cout << "    consumes: v" << pre_post[i].var << " = " << pre_post[i].pre << endl;
#endif
        } else {
            one_safe_[pre_post[i].var] = false;
        }
        assert(pre_post[i].post != -1 );
        Proposition &prop_post = propositions_[pre_post[i].var][pre_post[i].post];
        produces.insert(&prop_post);
        edges_.push_back(Edge(edges_.size(), Edge::TP, op_index, prop_post.index_));
#ifdef DEBUG
        cout << "    produces: v" << pre_post[i].var << " = " << pre_post[i].post << endl;
#endif
    }
    add_operator(produces, consumes, prevails, &op, base_cost);
#ifdef DEBUG
    cout << "id=" << operators_.size()-1 << ", operator (" << op.op_->get_name() << ") with cost " << base_cost << " added" << endl;
#endif
}

void Heuristic::add_operator(const set<Proposition*> &produces,
                             const set<Proposition*> &consumes,
                             const set<Proposition*> &prevails,
                             const SASOperator *op,
                             int base_cost) {
    PCOperator strips_op(produces, consumes, prevails, op, base_cost);
    operators_.push_back(strips_op);
    if( base_cost != 1 ) safe_to_max_with_hmax_ = false;
}

int Heuristic::compute_heuristic(const State &state) {
    // Compute hmax value: if dead end, return immediately.
    int hmax_value = safe_to_max_with_hmax_ && (hmax_heuristic_ != 0) ? hmax_heuristic_->compute_heuristic(state) : 0;
    if( hmax_value == DEAD_END ) {
        //histogram_push(0, numeric_limits<int>::max());
        return DEAD_END;
    }

    // Compute the bounds for the rows in the LP.
    int num_added_constraints = 0;
    for( int var = 0; var < propositions_.size(); ++var ) {
        for( int value = 0; value < propositions_[var].size(); ++value ) {
            const Proposition &prop = propositions_[var][value];
            if( prop.row_index_ >= 0 ) {
                double lower_bound = 0, upper_bound = 0;
                int type = ROW_GE;

                // Calculate row bounds and type.
                if( use_1safe_information_ ) {
                    // NOTE: SHOULD BE REVISED FOR FLUENT MERGE
                    if( (state[var] == value) && (goal_state_[var] == (state_var_t)-1) ) {
                        if( one_safe_[var] ) {
                            lower_bound = -1;
                            upper_bound = 0;
                            type = ROW_DB;
                        } else {
                            lower_bound = -1;
                        }
                    } else if( (state[var] == value) && (goal_state_[var] != value) ) {
                        if( one_safe_[var] ) {
                            lower_bound = -1;
                            upper_bound = -1;
                            type = ROW_EQ;
                        } else {
                            lower_bound = -1;
                        }
                    } else if( (state[var] != value) && (goal_state_[var] == value) ) {
                        if( one_safe_[var] ) {
                            lower_bound = 1;
                            upper_bound = 1;
                            type = ROW_EQ;
                        } else {
                            lower_bound = 1;
                        }
                    } else if( (state[var] == value) && (goal_state_[var] == value) ) {
                        if( one_safe_[var] ) {
                            lower_bound = 0;
                            upper_bound = 0;
                            type = ROW_EQ;
                        } else {
                            lower_bound = 0;
                        }
                    }

                    // Set row bounds.
                    assert((type == ROW_GE) || (type == ROW_EQ) || (type == ROW_DB));
                    if( type == ROW_GE ) {
                        osi_solver_->setRowLower(prop.row_index_, lower_bound);
                        osi_solver_->setRowUpper(prop.row_index_, osi_solver_->getInfinity());
                    } else {
                        osi_solver_->setRowLower(prop.row_index_, lower_bound);
                        osi_solver_->setRowUpper(prop.row_index_, upper_bound);
                    }
                } else {
                    int value_in_state = get_state_value(var, state);
                    if( (value_in_state == value) && (goal_state_[var] != value) ) {
                        lower_bound = -1;
                    } else if( (value_in_state != value) && (goal_state_[var] == value) ) {
                        lower_bound = 1;
                    } else if( (value_in_state == value) && (goal_state_[var] == value) ) {
                        lower_bound = 0;
                    }

                    osi_solver_->setRowLower(prop.row_index_, lower_bound);
                    osi_solver_->setRowUpper(prop.row_index_, osi_solver_->getInfinity());
                }
            }
        }
    }

    // Compute LA landmarks
    if( landmarks_ & 0x1 ) {
        // NOTE: SHOULD BE REVISED FOR FLUENT MERGE
        bool goal_reached = test_goal(state);
        if( goal_reached ) return 0;

        bool dead_end = lm_status_manager_->update_lm_status(state);
        if( dead_end ) {
            //histogram_push(0, numeric_limits<int>::max());
            return DEAD_END;
        }

        //cout << "Start-of-Landmarks" << endl;
        const set<LandmarkNode*>& nodes = lm_graph_->get_nodes();
        for( set<LandmarkNode*>::iterator node_it = nodes.begin(); node_it != nodes.end(); ++node_it ) {
            LandmarkNode& node = **node_it;
            int lmn_status = node.get_status();
            if( lmn_status != lm_reached ) {
                //cout << "    ";
                //lm_graph_->dump_node(&node);
                const set<int> &achievers = get_achievers(lmn_status, node);
                assert(!achievers.empty());

                //cout << "    LA-lm=[";
                CoinPackedVector *osi_row = new CoinPackedVector(true);
                for( set<int>::const_iterator it = achievers.begin(); it != achievers.end(); ++it ) {
                    assert(operators_[la_opmap_[*it]].op_->get_name() == g_operators[*it].get_name());
                    osi_row->insert(la_opmap_[*it], 1.0);
                    const Operator& op = lm_graph_->get_operator_for_lookup_index(*it);
                    //cout << op.get_name() << ",";
                    //set<pair<int, int> > current_lm_effects;
                    //get_landmark_effects(op, current_lm_effects);
                    //assert(current_lm_effects.size() > 0);
                    //double cost = ((double) op.get_cost()) / ((double) current_lm_effects.size());
                }
                //cout << "]" << endl;
                osi_solver_->addRow(*osi_row, 1.0, osi_solver_->getInfinity());
                delete osi_row;
            }
        }
        //cout << "End-of-Landmarks" << endl;
    }

    // Compute LM-cut landmarks.
    int lmcut_value = 0;
    if( landmarks_ & 0x2 ) {
        // NOTE: SHOULD BE REVISED FOR FLUENT MERGE
        lmcut_engine_->max_value_ = lmcut_engine_->value_ = 0;
        lmcut_engine_->compute_landmarks(state, 1);
        if( lmcut_engine_->max_value_ == numeric_limits<int>::max() ) {
            //histogram_push(0, numeric_limits<int>::max());
            return DEAD_END;
        }
        lmcut_value = lmcut_engine_->max_value_ - 1;
        //cout << "LM-cut value = " << lmcut_engine_->max_value_ - 1 <<  endl;

        //cout << "Start-of-Landmarks" << endl;
        for( const HittingSets::Landmark *lm = lmcut_engine_->passes_[0].second; lm != 0; lm = lm->next_ ) {
            //cout << "  "; lm->print(cout); cout << endl;
            bool good_landmark = rproblem_.operators_[*lm->begin()].op_ != 0;
            CoinPackedVector *osi_row = good_landmark ? new CoinPackedVector(true) : 0;
            for( Utils::BitmapSet::const_iterator it = lm->begin(); good_landmark && (it != lm->end()); ++it ) {
                good_landmark = rproblem_.operators_[*it].op_ != 0;
                if( !good_landmark ) {
                    cout << "Failure: bad landmark!" << endl;
                    exit(-1);
                }
                osi_row->insert(lmcut_opmap_[*it], 1.0);
                //cout << "  " << *it << " = " << rproblem_.operators_[*it].op_->get_name();
                ////if( lmcut_opmap_[*it] != -1 ) cout << " = " << operators_[lmcut_opmap_[*it]].op_->get_name();
                //cout << endl;
            }
            if( osi_row != 0 ) {
                osi_solver_->addRow(*osi_row, 1.0, osi_solver_->getInfinity());
                delete osi_row;
            }
        }
        HittingSets::Landmark::deallocate_chain(lmcut_engine_->passes_[0].second);
        //cout << "End-of-Landmarks" << endl;
    }

    // Lower bounds for constraints associated to prevails.
    if( use_prevails_ ) {
        for( int var = 0; var < propositions_.size(); ++var ) {
            const Proposition &prop = propositions_[var][state[var]];
            for( int i = 0; i < prop.prevail_of_.size(); ++i ) {
                int action = prop.prevail_of_[i];
                int constraint = prevail_constraints_[action][prop.index_];
                osi_solver_->setRowLower(constraint, 0);
            }
        }
    }

    // Call LP solver. If unfeasible, return DEAD_END
    int rv = -1, heuristic_value = -1;
#ifdef DEBUG
    cout << "calling LP solver..." << flush;
#endif
    try {
        osi_solver_->resolve();
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

#if 0
        int ncols = osi_solver_->getNumCols();
        const double *solution = osi_solver_->getColSolution();
        cout << "Solution: value=" << (float)osi_solver_->getObjValue() << ", x*=[" << endl;
        for( int i = 0; i < ncols; ++i ) {
            if( (float)solution[i] > 0 ) {
                cout << " (" << operators_[i].op_->op_->get_name() << ")=" << solution[i] << ", cost=" << operators_[i].base_cost_ << endl;
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
        if( !use_prevails_ ) {
            obj_value = osi_solver_->getObjValue();
            heuristic_value = (int)ceilf((float)obj_value);
        } else {
            const double *solution = osi_solver_->getColSolution();
            for( int t = 0; t < M_->ntransitions_; ++t ) {
                obj_value += solution[t] * operators_[t].base_cost_;
                //cout << "solution[" << t << "]=" << solution[t] << endl;
            }
#if 0
            for( int t = 0; t < M_->ntransitions_; ++t ) {
                int slack = 2 * M_->ntransitions_ + t;
                if( solution[slack] > 0 ) cout << "  slack(" << t << ")=" << solution[slack] << endl;
            }
#endif
        }

        heuristic_value = (int)ceilf((float)obj_value);
        if( heuristic_value < lmcut_value ) {
            cout << "Warning: value is lower than lmcut: lmcut=" << lmcut_value << ", seq=" << heuristic_value << endl;
            heuristic_value = lmcut_value;
        }
    } else {
        heuristic_value = DEAD_END;
    }

    // If constraints were added, remove them. Restore bounds for prevail constraints.
    osi_solver_->restoreBaseModel(nconstraints_);
    if( use_prevails_ ) {
        for( int var = 0; var < propositions_.size(); ++var ) {
            const Proposition &prop = propositions_[var][state[var]];
            for( int i = 0; i < prop.prevail_of_.size(); ++i ) {
                int action = prop.prevail_of_[i];
                int constraint = prevail_constraints_[action][prop.index_];
                osi_solver_->setRowLower(constraint, 1);
            }
        }
    }

    // Return value;
    if( heuristic_value == DEAD_END ) {
        //histogram_push(0, numeric_limits<int>::max());
        return DEAD_END;
    } else if( safe_to_max_with_hmax_ ) {
        int hvalue = hmax_value > heuristic_value ? hmax_value : heuristic_value;
        //histogram_push(0, hvalue);
        return hvalue;
    } else {
        //histogram_push(0, heuristic_value);
        return heuristic_value;
    }
}

bool Heuristic::reach_state(const State& parent_state, const Operator &op, const State& state) {
    if( landmarks_ & 0x1 )
        lm_status_manager_->update_reached_lms(parent_state, op, state);
    return true;
}

ScalarEvaluator *_parse(OptionParser &parser) {
    parser.add_option<int>("landmarks", 0, "landmark factory: 0=no factory (default), 1=lmgraph-factory, 2=lmcut-factory");
    parser.add_option<bool>("use_1safe_information", false, "enable use of 1-safe information");
    parser.add_option<bool>("use_prevails", false, "enable constraints for prevails");
    parser.add_option<int>("merge_fluents", 0, "merge fluents: 0=no merge, 1=naive");
    parser.add_option<LandmarkGraph *>("lm_graph", 0, "only used (and required) when landmarks=1");
    parser.add_option<string>("lp_solver", string("clp"), string("\"clp\" (default), \"grb\", \"cplex\""));
    
    Heuristic::add_options_to_parser(parser);
    Options opts = parser.parse();

    if( !parser.dry_run() && (opts.get<int>("landmarks") & 0x1) && (opts.get<LandmarkGraph*>("lm_graph") == 0) ) {
        parser.error("landmark graph could not be constructed");
    }

    string lp = opts.get<string>("lp_solver");
    if( (lp != "clp") && (lp != "grb") && (lp != "cplex") ) {
        parser.error("unknown lp-solver");
    }

    return parser.dry_run() ? 0 : new Heuristic(opts);
}

Plugin<ScalarEvaluator> _plugin("state_equation", _parse);

} // end of namespace

