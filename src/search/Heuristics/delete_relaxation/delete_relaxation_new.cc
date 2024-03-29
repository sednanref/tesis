#include "delete_relaxation.h"

#include "../../globals.h"
#include "../../operator.h"
#include "../../state.h"
#include "../../option_parser.h"
#include "../../plugin.h"

#include <cassert>
#include <algorithm>
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

//#pragma GCC diagnostic ignored "-Wunused-variable"

#define EPSILON             0.0001

using namespace std;

#define DEBUG

// encapsulate the heuristic into its own namespace
namespace Delete_rel {

int TrSystem::fetch_state(const Proposition *proposition) {
    assert(proposition != 0);
    map<const Proposition*, int>::const_iterator it = proposition_map_.find(proposition);
    if( it == proposition_map_.end() ) {
        states_.push_back(proposition);
        int id = (int)states_.size() - 1;
        proposition_map_.insert(make_pair(proposition, id));
        in_.push_back(vector<int>());
        out_.push_back(vector<int>());
        assert(states_[id] == proposition);
        return id;
    } else {
        assert(states_[it->second] == proposition);
        return it->second;
    }
}

int TrSystem::fetch_label(const Operator *op) {
    assert(op != 0);
    map<const Operator*, int>::const_iterator it = operator_map_.find(op);
    if( it == operator_map_.end() ) {
        labels_.push_back(op);
        label_set_.insert(op);
        int id = (int)labels_.size() - 1;
        operator_map_.insert(make_pair(op, id));
        return id;
    } else {
        return it->second;
    }
}

bool TrSystem::create_transition(const Proposition *pre, const Operator *op, const Proposition *post) {
    int pre_id = fetch_state(pre);
    int post_id = fetch_state(post);
    int label_id = fetch_label(op);
    pair<int, pair<int, int> > tr(label_id, make_pair(pre_id, post_id));
    if( transition_set_.find(tr) == transition_set_.end() ) {
        transition_set_.insert(tr);
        transitions_.push_back(tr);
        int tr_id = (int)transitions_.size() - 1;
        in_[post_id].push_back(tr_id);
        out_[pre_id].push_back(tr_id);
#if 0
        cout << "DTG: tr=" << tr_id << ": "
             << "pre=" << *pre << " " //"(id=" << pre_id << ") "
             << ">>>label=" << *op << ">>> " //"(id=" << label_id << ")>>> "
             << "post=" << *post //<< "(id=" << post_id << ")"
             << endl;
#endif
        return true;
    }
    return false;
}

void TrSystem::dump(ostream &os) const {
    os << "states:" << endl;
    for( int i = 0; i < states_.size(); ++i )
        os << "  " << i << ": " << *states_[i] << endl;

    os << "labels:" << endl;
    for( int i = 0; i < labels_.size(); ++i )
        os << "  " << i << ": " << *labels_[i] << endl;

    os << "transitions:" << endl;
    for( int i = 0; i < transitions_.size(); ++i ) {
        pair<int, pair<int, int> > tr = transitions_[i];
        os << "  " << i << ": pre=" << *states_[tr.second.first] << " >>> label=" << *labels_[tr.first] << " >>> post=" << *states_[tr.second.second] << endl;
    }
}

const OperatorCopy* DTG::fetch_copy(const Operator *op, const Proposition *pre, const Proposition *post) {
    map<pair<const Proposition*, const Proposition*>, const OperatorCopy*> &copy_map = operator_copies_[op];
    map<pair<const Proposition*, const Proposition*>, const OperatorCopy*>::iterator it =
      copy_map.find(make_pair(pre, post));
    if( it == copy_map.end() ) {
        OperatorCopy *copy = new OperatorCopy(-1, op, pre, post);
        //cout << "NEW COPY: cop=" << *copy << endl;
        //cout << "NEW COPY: dtg=" << this << ", pre=" << *pre << ", post=" << *post << ", cop=" << *copy << ", ptr=" << copy << endl;
        copy_map.insert(make_pair(make_pair(pre, post), copy));
        incident_operators_[pre].insert(op);
        incident_operators_[post].insert(op);
        if( link_constraints_.find(op) == link_constraints_.end() ) link_constraints_.insert(make_pair(op, -1));
        return copy;
    } else {
        return it->second;
    }
}

void DTG::invalidate_link_constraint(const Operator *op, OsiSolverInterface *osi_solver) {
    assert(link_constraints_.find(op) != link_constraints_.end());
    if( link_constraints_[op] != -1 ) {
        osi_solver->setRowUpper(link_constraints_[op], osi_solver->getInfinity());
        link_constraints_[op] = -1;
    }
}

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
      empty_base_lp_(opts.get<bool>("empty_base_lp")),
      use_landmarks_(opts.get<int>("landmarks")),
      use_ubs_(opts.get<bool>("use_ubs")),
      lp_solver_(opts.get<string>("lp_solver")),
      epsilon_(opts.get<float>("epsilon")),
      debug_(opts.get<bool>("debug")),
      //Added by del_rel \/
      use_seq_(opts.get<int>("seq")),
      use_tr_(opts.get<int>("tr")) {
    
    safe_to_max_with_hmax_ = false; // TURN OFF MAXING W/ HMAX
    hmax_heuristic_ = 0;

    landmarks_ = 0;
    if( use_landmarks_ & 0x1 ) {
        Utils::BitmapSet::initialize(g_operators.size());
        lm_graph_ = new LandmarkGraph(*opts.get<LandmarkGraph *>("lm_graph"));
        lm_status_manager_ = new LandmarkStatusManager(*lm_graph_);
    }
    if( use_landmarks_ & 0x2 ) {
        lmcut_engine_ = new HittingSets::LMCutEngine(rproblem_);
    }
}

Heuristic::~Heuristic() {
    delete hmax_heuristic_;
}

// initialization
void Heuristic::initialize() {
    cout << "Initializing delete_relaxation heuristic using:" 
         << "seq=" << use_seq_
         << "tr=" << use_tr_
         << "landmarks=" << use_landmarks_
         << ", LP-kit=osi:" << lp_solver_ << endl;

    // Framework does not support axioms or conditional effects
    ::verify_no_axioms_no_cond_effects();

    // create base model and LP
    create_primitive_variables_and_propositions();
    create_primitive_operators();
    if(use_seq_)
        preprocess();
    create_base_lp();

    // Create and initialize hmax heuristic.
    // TODO: get rid of this, use max() in arguments to FD call
    if( safe_to_max_with_hmax_ && !(use_landmarks_ & 0x2) ) {
        Options opts;
        opts.set<int>("cost_type", 0);
        hmax_heuristic_ = new HSPMaxHeuristic(opts);
        hmax_heuristic_->initialize();
        cout << "Initialize: hmax heuristic create" << endl;
    }

    // Initialize landmark engine for lmgraph
    if( use_landmarks_ & 0x1 ) {
        lm_status_manager_->set_landmarks_for_initial_state();
        la_opmap_ = vector<int>(g_operators.size(), -1);
        for( int i = 0; i < g_operators.size(); ++i ) {
            //const Operator& op = lgraph_->get_operator_for_lookup_index(op_id);
            for( int j = 0; j < operators_.size(); ++j ) {
                PrimitiveOperator *pop = static_cast<PrimitiveOperator*>(operators_[j]);
                if( &pop->base_op_ == &g_operators[i] ) {
                    la_opmap_[i] = j;
                    //cout << "la-map: " << i << " -> " << j << endl;
                    break;
                }
            }
        }
        for( int i = 0; i < g_operators.size(); ++i ) {
            if( la_opmap_[i] == -1 ) {
                cout << "Error: cross-reference between (lmgraph) landmarks operators failed!" << endl;
                exit(-1);
            }
        }
    }

    // Initialize landmark engine (LM-Cut).
    if( use_landmarks_ & 0x2 ) {
        rproblem_.initialize();
        lmcut_engine_->initialize(1, true);
        lmcut_opmap_ = vector<int>(rproblem_.operators_.size(), -1);
        for( int i = 0; i < rproblem_.operators_.size(); ++i ) {
            for( int j = 0; j < operators_.size(); ++j ) {
                PrimitiveOperator *pop = static_cast<PrimitiveOperator*>(operators_[j]);
                if( (rproblem_.operators_[i].op_ != 0) && (rproblem_.operators_[i].op_ == &pop->base_op_) ) {
                    lmcut_opmap_[i] = j;
                    //cout << "lmcut-map: " << i << " -> " << j << endl;
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
        cout << "Initialize: lmcut engine initialized" << endl;
    }

    cout << "Initialize: finished with initialization" << endl;
}

void Heuristic::create_primitive_variables_and_propositions() {
    // set static references in Proposition and Operator
    Proposition::nprimitive_variables_ = nprimitive_variables_;
    Proposition::variables_ = &variables_;
    //Proposition::merge_variables_ = &merge_variables_;
    Operator::propositions_mutex_with_precondition_ = &propositions_mutex_with_precondition_;
    Operator::propositions_mutex_with_postcondition_ = &propositions_mutex_with_postcondition_;

    // Create variables
    nprimitive_variables_ = 0;
    nvariables_ = g_variable_domain.size();
    for( int var = 0; var < nvariables_; ++var ) {
        variables_.push_back(new Variable(nprimitive_variables_++));
    }
    cout << "Base model: " << nvariables_ << " primitive variables created" << endl;

    // Create primitive propositions
    npropositions_ = 0;
    nprimitive_propositions_ = 0;
    primitive_propositions_.resize(nvariables_);

    //added by delete_rel
    indexes_begin_var_.resize(nvariables_);


    for( int var = 0; var < nvariables_; ++var ) {
        int domain_size = g_variable_domain[var];
        primitive_propositions_[var].resize(domain_size);

        if(!var){
            indexes_begin_var_[var] = 0;
        }
        else {
            indexes_begin_var_[var]=indexes_begin_var_[var-1]+g_variable_domain[var-1];
        }

        propositions_.reserve(propositions_.size() + domain_size);
        for( state_var_t val = 0; val < domain_size; ++val ) {
            PrimitiveProposition *primitive_proposition = new PrimitiveProposition(npropositions_, var, val);
            primitive_propositions_[var][val] = primitive_proposition;
            propositions_.push_back(primitive_proposition);
            ++nprimitive_propositions_;
            ++npropositions_;
        }
    }
    cout << "Base model: " << nprimitive_propositions_ << " primitive propositions created" << endl;
}
/*
void Heuristic::create_primitive_dtgs() {
    for( int i = 0; i < nvariables_; ++i )
        dtgs_.push_back(new DTG(*variables_[i]));
    cout << "Base model: " << nvariables_ << " primitive DTGs created" << endl;
}
*/  
void Heuristic::create_primitive_operators() {
    // Create primitive operators
    noperators_ = 0;
    nprimitive_operators_ = 0;
    operators_.reserve(g_operators.size());
    for( int i = 0; i < g_operators.size(); ++i ) {
        create_primitive_operator(g_operators[i]);
    }
    checked_operators_ = vector<bool>(nprimitive_operators_, false);
    cout << "Base model: " << nprimitive_operators_ << " primitive operators created" << endl;
}

void Heuristic::preprocess() {
    // pre-calculate propositions that are mutex with pre and postconditions for each primitive operator
    propositions_mutex_with_precondition_.resize(nprimitive_operators_);
    propositions_mutex_with_postcondition_.resize(nprimitive_operators_);
    for( int i = 0; i < nprimitive_operators_; ++i ) {
        const Operator *op = operators_[i];
        for( int j = 0; j < nprimitive_propositions_; ++j ) {
            const PrimitiveProposition *p = static_cast<PrimitiveProposition*>(propositions_[j]);
            if( op->proposition_is_mutex_with_precondition(p, false) ) // false == force computation rather than lookup
                propositions_mutex_with_precondition_[i].insert(j);
            if( op->proposition_is_mutex_with_postcondition(p, false) ) // false == force computation rather than lookup
                propositions_mutex_with_postcondition_[i].insert(j);
        }
    }
    cout << "Base model: propositions mutex with pre and postconditions calculated" << endl;

    // Define goal variables and fluents
    vector<state_var_t> extended_goal(nprimitive_variables_, numeric_limits<state_var_t>::max());
    for( int i = 0; i < g_goal.size(); ++i ) {
        int var = g_goal[i].first;
        state_var_t val = g_goal[i].second;
        primitive_propositions_[var][val]->is_mutex_with_goal_ = false;
        variables_[var]->goal_ = true;
        extended_goal[var] = val;
    }
    for( int var = 0; var < nvariables_; ++var ) {
        if( !variables_[var]->goal_ ) {
            for( state_var_t val = 0; val < primitive_propositions_[var].size(); ++val ) {
                primitive_propositions_[var][val]->is_mutex_with_goal_ = false;
            }
        }
    }

    // compute candidate goal values for each variable
    vector<set<state_var_t> > goal_values(nprimitive_variables_);
    for( int var = 0; var < nprimitive_variables_; ++var ) {
        if( !variables_[var]->goal_ ) {
            int domain_size = g_variable_domain[var];
            for( int val = 0; val < domain_size; ++val )
                goal_values[var].insert(val);
        } else {
            goal_values[var].insert(extended_goal[var]);
        }
    }

    // prune goal values until reaching a fix point
    bool change = true;
    while( change ) {
        change = false;
        for( int var = 0; var < nprimitive_variables_; ++var ) {
            if( !variables_[var]->goal_ ) {
                for( set<state_var_t>::iterator it = goal_values[var].begin(); it != goal_values[var].end(); ) {
                    bool valid_value = true;
                    for( int v2 = 0; valid_value && (v2 < nprimitive_variables_); ++v2 ) {
                        if( variables_[v2]->goal_ ) {
                            bool valid = false;
                            for( set<state_var_t>::iterator jt = goal_values[v2].begin(); !valid && (jt != goal_values[v2].end()); ++jt ) {
                                valid = !are_mutex(var, *it, v2, *jt);
                            }
                            valid_value = valid;
                        }
                    }
                    if( valid_value ) {
                        ++it;
                    } else {
#if 0
                        cout << "Pruning goal value " << (int)*it << " from domain of variable "
                             << *variables_[var] << ": literal='" << *primitive_propositions_[var][*it] << "'" << endl;
#endif
                        primitive_propositions_[var][*it]->is_mutex_with_goal_ = true;
                        goal_values[var].erase(it++);
                        change = true;
                        if( goal_values[var].size() == 1 ) {
                            int value = *goal_values[var].begin();
                            cout << "Variable " << *variables_[var]
                                 << " promoted to goal variable: value=" << value
                                 << ", goal literal='" << *primitive_propositions_[var][value] << "'" << endl;
                            variables_[var]->goal_ = true;
                            break;
                        }
                    }
                }
            }
        }
    }
    cout << "Base model: goals defined" << endl;
}

void Heuristic::create_primitive_operator(const ::Operator &base_op) {
    const vector<Prevail> &prevail = base_op.get_prevail();
    const vector<PrePost> &pre_post = base_op.get_pre_post();

    PrimitiveOperator *pop = new PrimitiveOperator(nprimitive_operators_++, base_op);
    ++noperators_;
    set<PrimitiveProposition*> prevails, consumes, produces;

    // Prevails
    for( int i = 0; i < prevail.size(); ++i ) {
        int var = prevail[i].var;
        int prev = prevail[i].prev;
        PrimitiveProposition *p = primitive_propositions_[var][prev];
        prevails.insert(p);
        //cout << "hola: var=" << var << ", prevail=" << p->id_ << endl;
        //dtgs_[var]->create_transition(p, pop, p);
    }

    // Pre-post conditions
    for( int i = 0; i < pre_post.size(); ++i ) {
        int var = pre_post[i].var;
        int pre = pre_post[i].pre;
        int post = pre_post[i].post;
        assert(post != -1);

        PrimitiveProposition *post_prop = primitive_propositions_[var][post];
        produces.insert(post_prop);

        Proposition *pre_prop = 0;
        if( pre == -1 ) {
            pre_prop = const_cast<UndefinedProposition*>(fetch_undefined(var).first);
        } else {
            pre_prop = primitive_propositions_[var][pre];
            consumes.insert(static_cast<PrimitiveProposition*>(pre_prop));
        }
        //cout << "hola: var=" << var << ", pre=" << pre << ", post=" << post << endl;
        //dtgs_[var]->create_transition(pre_prop, pop, post_prop);

        if( pre == -1 ) {
            //if( variables_[var]->safe_ ) cout << "Variable " << *variables_[var] << " is unsafe" << endl;
            variables_[var]->safe_ = false;
        }
    }

    // Set prevail, consumed and produced propositions in primitive operator
    for( set<PrimitiveProposition*>::iterator it = prevails.begin(); it != prevails.end(); ++it ) {
        primitive_propositions_[(*it)->var_][(*it)->val_]->prevail_of_.push_back(pop);
        pop->prevails_.push_back(*it);
    }
    for( set<PrimitiveProposition*>::iterator it = consumes.begin(); it != consumes.end(); ++it ) {
        primitive_propositions_[(*it)->var_][(*it)->val_]->consumed_by_.push_back(pop);
        pop->consumes_.push_back(*it);
    }
    for( set<PrimitiveProposition*>::iterator it = produces.begin(); it != produces.end(); ++it ) {
        primitive_propositions_[(*it)->var_][(*it)->val_]->produced_by_.push_back(pop);
        pop->produces_.push_back(*it);
    }

    // set relevant_to field in propositions
    for( int i = 0; i < pre_post.size(); ++i ) {
        int var = pre_post[i].var;
        int pre = pre_post[i].pre;
        int post = pre_post[i].post;
        if( pre == -1 ) {
            for( int j = 0; j < primitive_propositions_[var].size(); ++j ) {
                PrimitiveProposition &prop = *primitive_propositions_[var][j];
                if( (j != post) && pop->proposition_is_mutex_with_precondition(&prop, false) ) { // false == force computation rather than lookup
                    // prop isn't prevail of pop because var(prop) appears in pre_post
                    // prop isn't consumed by pop because Pre[var(prop)] = -1
                    // prop isn't produced by pop because Post[var(prop)] != j
                    prop.relevant_to_.push_back(pop);
                }
            }
        }
    }

    // insert operator
    operators_.push_back(pop);
    if( pop->get_cost() != 1 ) safe_to_max_with_hmax_ = false;
    if( false && debug_ ) pop->dump(cout, true);
}

void Heuristic::set_column_name(const Operator *op) {
#if 0
    stringstream ss;
    ss << *op;
    string name = ss.str();
    replace(name.begin(), name.end(), ' ', '_');
    replace(name.begin(), name.end(), '-', '_');
    replace(name.begin(), name.end(), '<', '_');
    replace(name.begin(), name.end(), '>', '_');
    osi_solver_->setColName(op->id_, name);
#endif
}

void Heuristic::set_row_name(const Proposition *p) {
#if 0
    if( p->row_index_ != -1 ) {
        stringstream ss;
        ss << *p;
        string name = ss.str();
        replace(name.begin(), name.end(), ' ', '_');
        replace(name.begin(), name.end(), '-', '_');
        replace(name.begin(), name.end(), '<', '_');
        replace(name.begin(), name.end(), '>', '_');
        osi_solver_->setRowName(p->row_index_, name);
    }
#endif
}

int Heuristic::get_uo(int op_id){
    return begin_uo_+op_id;
}

int Heuristic::get_to(int op_id){
    return begin_to_ + op_id;
}

int Heuristic::get_r(int var, int val){
    return begin_r_ + indexes_begin_var_[var]+val;
}

int Heuristic::get_ta(int var, int val){
    return begin_ta_ + indexes_begin_var_[var]+val;;
}

int Heuristic::get_f(int op, int var, int val){
    return index_f_[make_pair(op,make_pair(var,val))];
}

int Heuristic::get_yo(int op_id){
    return begin_yo_+op_id;
}



void Heuristic::correct_model(const State &state){

    //Correcting S(a) for second constraint
    for(int var=0;var<nvariables_;++var){
        int val = state[var];
        if(val>=0 && val<g_variable_domain[var]){
            int idx = 0;
            idx+=indexes_begin_var_[var];
            idx+=val;
            osi_solver_->setRowLower(idx,-1);
        }
    }


    //adding constraints from SEQ
    /*if(0x1 & use_seq_){
        int init = begin_const_seq_;
        for(int var=0;var<nvariables_;++var){
            for(int val=0;val<g_variable_domain[var];++val){
                int ga = tmp_goal_[var]==val;
                int sa = state[var]==val;
                osi_solver_->setRowLower(init,ga-sa);
                init++;
            }
        }
    }*/

}

void Heuristic::add_first_const(vector<double> *lb){
    for(int i=0;i<g_goal.size();++i){
        int var = g_goal[i].first;
        int val = g_goal[i].second;
        int idx = get_r(var,val);
        (*lb)[idx] = 1;
    }
}


void Heuristic::add_second_const(vector<CoinPackedVector*> *osi_rows, vector<double> &lb,vector<double> &ub){

    //These constraints depends on state for lower bounds
    for(int var=0;var<nvariables_;++var){

        for(int val=0;val<g_variable_domain[var];++val){

            vector<Operator*> &prod = primitive_propositions_[var][val]->produced_by_;
            CoinPackedVector *osi_row = new CoinPackedVector(true);
            int Ra = get_r(var,val);
            osi_row->insert(Ra,-1);

            for(int op=0;op<prod.size();++op){
                int id_op = prod[op]->id_;
                int Foa = get_f(id_op,var,val);
                osi_row->insert(Foa,1);
            }

            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }
    }
}


void Heuristic::add_third_const(vector<CoinPackedVector*> *osi_rows, vector<double> &lb,vector<double> &ub){
    for(int op = 0 ; op<operators_.size(); ++op){
        vector<Proposition*> &pr = operators_[op]->produces_;

        int id_op = operators_[op]->id_;

        for(int j =0;j<pr.size();++j){
            PrimitiveProposition *ptr = dynamic_cast<PrimitiveProposition *>(pr[j]);
            if(!ptr)
                continue;

            int var = ptr->var_;
            int val = ptr->val_;
            int id_u = get_uo(id_op);
            int id_f = get_f(id_op,var,val);

            CoinPackedVector *osi_row = new CoinPackedVector(true);
            osi_row->insert(id_u,1);
            osi_row->insert(id_f,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }

    }
}

void Heuristic::add_fourth_const(vector<CoinPackedVector*> *osi_rows, vector<double> &lb,vector<double> &ub){
    for(int op=0;op<operators_.size();++op){
        int id_op = operators_[op]->id_; 
        PrimitiveOperator *ptr = dynamic_cast<PrimitiveOperator *>(operators_[op]);
        if(!ptr) 
            continue;

        const vector<PrePost> &pre_post = ptr->base_op_.get_pre_post();
        const vector<Prevail> &prevail = ptr->base_op_.get_prevail();

        for(int j =0 ;j < prevail.size();++j){
            int var = prevail[j].var;
            int val = prevail[j].prev;
            
            if(val<0) continue;
            //cout << "/------> #############  Si hay prevails" << endl;
            int id_r = get_r(var,val);
            int id_u = get_uo(id_op);


            CoinPackedVector *osi_row = new CoinPackedVector(true);
            osi_row->insert(id_r,1);
            osi_row->insert(id_u,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }


        for(int j =0; j< pre_post.size();++j){
            int var = pre_post[j].var;
            int val = pre_post[j].pre;

            if(val<0){
                continue;
            }


            int id_u = get_uo(id_op);
            int id_r = get_r(var,val);

            CoinPackedVector *osi_row = new CoinPackedVector(true);
            osi_row->insert(id_r,1);
            osi_row->insert(id_u,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }   
    }


}

void Heuristic::add_fifth_const(vector<CoinPackedVector*> *osi_rows, vector<double> &lb,vector<double> &ub){
    for(int op=0;op<operators_.size();++op){
        int id_op = operators_[op]->id_; 
        PrimitiveOperator *ptr = dynamic_cast<PrimitiveOperator *>(operators_[op]);
        if(!ptr) 
            continue;


        const vector<PrePost> &pre_post = ptr->base_op_.get_pre_post();
        const vector<Prevail> &prevail = ptr->base_op_.get_prevail();

        for(int j =0 ;j<prevail.size();++j){
            int var = prevail[j].var;
            int val = prevail[j].prev;

            if(val<0) continue;
            //cout << "/------> #############  Si hay prevails" << endl;
            int id_to = get_to(id_op);
            int id_ta = get_ta(var,val);

            CoinPackedVector *osi_row = new CoinPackedVector(true);
            osi_row->insert(id_to,1);
            osi_row->insert(id_ta,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }


        for(int j =0; j< pre_post.size();++j){
            int var = pre_post[j].var;
            int val = pre_post[j].pre;

            if(val<0){
                continue;
            }

            int id_to = get_to(id_op);
            int id_ta = get_ta(var,val);

            CoinPackedVector *osi_row = new CoinPackedVector(true);
            osi_row->insert(id_to,1);
            osi_row->insert(id_ta,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());
        }   
    }    

}

void Heuristic::add_sixth_const(vector<CoinPackedVector*> *osi_rows, vector<double> &lb,vector<double> &ub){
    for(int op = 0 ; op<operators_.size(); ++op){
        vector<Proposition*> &pr = operators_[op]->produces_;
        for(int j =0;j<pr.size();++j){
            PrimitiveProposition *ptr = dynamic_cast<PrimitiveProposition *>(pr[j]);
            if(!ptr)
                continue;

            int id_op = operators_[op]->id_;
            int var = ptr->var_;
            int val = ptr->val_;
            int id_to = get_to(id_op);
            int id_ta = get_ta(var,val);
            int id_f = get_f(id_op,var,val);
            int m = nopr_+1;

            CoinPackedVector *osi_row = new CoinPackedVector(true);

            osi_row->insert(id_ta,1);
            osi_row->insert(id_f,-m);
            osi_row->insert(id_to,-1);
            osi_rows->push_back(osi_row);
            nconstraints_++;
            lb.push_back(1-m);
            ub.push_back(osi_solver_->getInfinity());
        }

    }

}


//from SEQ adding constraints of this kind: Yo>=Uo
void Heuristic::add_seventh_const(std::vector<CoinPackedVector*> *osi_rows,std::vector<double> &lb,std::vector<double> &ub){
    for(int op=0;op<nopr_;op++){
        int id_op = operators_[op]->id_;

        int yo = get_yo(id_op);
        int uo = get_uo(id_op);

        CoinPackedVector *osi_row = new CoinPackedVector(true);
        osi_row->insert(yo,1);
        osi_row->insert(uo,-1);
        nconstraints_++;
        osi_rows->push_back(osi_row);
        lb.push_back(0);
        ub.push_back(osi_solver_->getInfinity());
    }
}

//from SEQ adding constraints for all atoms
void Heuristic::add_eighth_const(std::vector<CoinPackedVector*> *osi_rows,std::vector<double> &lb,std::vector<double> &ub){
    begin_const_seq_=nconstraints_;

    for(int var=0;var<nvariables_;++var){
        for(int val=0;val<g_variable_domain[var];++val){
            CoinPackedVector *osi_row = new CoinPackedVector(true);

            std::vector<Operator *> &consumed = primitive_propositions_[var][val]->consumed_by_;
            std::vector<Operator *> &produced = primitive_propositions_[var][val]->produced_by_;

            for(int i=0;i<produced.size();++i){
                int id_op = produced[i]->id_;
                int yo = get_yo(id_op);
                osi_row->insert(yo,1);
            }

            for(int i=0;i<consumed.size();++i){
                int id_op = consumed[i]->id_;
                int yo = get_yo(id_op);
                osi_row->insert(yo,-1);
            }


            nconstraints_++;
            osi_rows->push_back(osi_row);
            lb.push_back(0);
            ub.push_back(osi_solver_->getInfinity());

        }        
    }

    end_const_seq_=nconstraints_;

}

void Heuristic::add_fs(){
    for(int op = 0 ; op<operators_.size(); ++op){
        vector<Proposition*> &pr = operators_[op]->produces_;

        int id_op = operators_[op]->id_;

        for(int j =0;j<pr.size();++j){
            PrimitiveProposition *ptr = dynamic_cast<PrimitiveProposition *>(pr[j]);
            if(!ptr)
                continue;

            int var = ptr->var_;
            int val = ptr->val_;

            index_f_[make_pair(id_op,make_pair(var,val))]=nvars_++;
        }
    }
}

void Heuristic::init_tmp_goal(){
    tmp_goal_.clear();
    tmp_goal_.resize(nvariables_,-1);
    for(int i=0;i<g_goal.size();++i){
        int var = g_goal[i].first;
        int val = g_goal[i].second;
        tmp_goal_[var]=val;
    }
}

void Heuristic::create_base_lp() {
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

    osi_solver_->setIntParam(OsiNameDiscipline, 2);

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

    //number
    nprop_ = npropositions_;
    nopr_  = noperators_;
    nvars_without_seq_ = 0;
    //variables in delete relaxation model
    nvars_ = nopr_;
    begin_uo_=0;
    end_uo_=nopr_;
    begin_to_=end_to_=begin_ta_=end_ta_=begin_yo_=end_yo_=-1;

    if((use_tr_&0x1)==0){
        begin_to_=nvars_;
        end_to_=nvars_+=nopr_;
    }

    begin_r_=nvars_;
    end_r_=nvars_+=nprop_;

    if((use_tr_&0x1)==0){
        begin_ta_=nvars_;
        end_ta_=nvars_+=nprop_;
    }
    begin_f_=nvars_;

    add_fs();
    end_f_=nvars_;

    nvars_without_seq_=nvars_;
    if(0x1 & use_seq_){
        begin_yo_=nvars_;
        end_yo_=nvars_+=nopr_;
    }

    // Variables
    //the first nopr variables refers to U variables in delete relaxation
    //the second nopr variables refers to To operators in delete relaxation
    //next nprop variables refers to R variables in delete relaxation
    //next nprop variables refers to Ta variables in delete relaxation
    //next nprop * nopr variables refer to Foa variables. These are ordered by operators
    //                            which means the first operator with every propositions
    //                            are before the next operator with every proposition.
    //if use_seq_ is set the next nopr_ variables refer to Yo from SEQ
    //
    vector<double> osi_col_lb(nvars_, 0);
    vector<double> osi_col_ub(nvars_, osi_solver_->getInfinity());
    for(int i=0;i<nvars_;++i){
        //upper bounds for U variables
        if(i<end_uo_){
            osi_col_ub[i]=1;
        }
        //upper bound for To variables
        else if(i<end_to_){
            osi_col_ub[i]=nopr_;
        }
        //ub for R variables
        else if(i<end_r_){
            osi_col_ub[i]=1;
        }
        //ub for Ta variables
        else if(i<end_ta_){
            osi_col_ub[i]=nopr_;
        }
        //up for F variables
        else if(i<end_f_){
            osi_col_ub[i]=1;
        }
        else if(i<end_yo_){
            //nothing to do here, already set bounds for Yo
        }
    }

    cout << "LP: base variables created" << endl;

    // Objective function.
    //setting cost only for operators. Other kind of variables haven't cost
    vector<double> osi_obj_fn(nvars_, 0);
    for( int i = 0; i < nvars_; ++i ) {
        if(i<end_uo_ && !use_seq_)
            osi_obj_fn[i] = operators_[i]->get_cost();
        else if(i<end_f_) osi_obj_fn[i] = 0;
        //Added SEQ+del
        else osi_obj_fn[i] = operators_[i-nvars_without_seq_]->get_cost();
    }


    cout << "LP: objective function created" << endl;

    // Constraints.
    CoinPackedMatrix *osi_matrix = new CoinPackedMatrix(false, 0, 0);
    osi_matrix->setDimensions(0, nvars_);
    vector<CoinPackedVector*> osi_rows;

    nconstraints_ = 0;
    ninactive_constraints_ = 0;

#if 0
    for( int i = 0; !empty_base_lp_ && (i < npropositions_); ++i ) {
        Proposition &prop = *propositions_[i];
        if( !prop.produced_by_.empty() || !prop.consumed_by_.empty() ) {
            CoinPackedVector *osi_row = new CoinPackedVector(true);
            for( int j = 0; j < prop.produced_by_.size(); ++j ) {
                int oid = prop.produced_by_[j]->id_;
                osi_row->insert(oid, 1);
            }
            for( int j = 0; j < prop.consumed_by_.size(); ++j ) {
                int oid = prop.consumed_by_[j]->id_;
                osi_row->insert(oid, -1);
            }
            osi_rows.push_back(osi_row);
            prop.row_index_ = nconstraints_;
            ++nconstraints_;
        }
    }

    for( int i = 0; !empty_base_lp_ && (i < npropositions_); ++i ) {
        Proposition &prop = *propositions_[i];
        assert((0 <= prop.var_) && (prop.var_ < dtgs_.size()));
        DTG &dtg = *dtgs_[prop.var_];
        create_flow_and_link_constraints(dtg, prop, &osi_rows);

        if( dtg.proposition_map_.find(&prop) != dtg.proposition_map_.end() ) {
            int state_id = dtg.proposition_map_.find(&prop)->second;
            assert(state_id != dtg.undef_state_);
            if( !dtg.in_[state_id].empty() || !dtg.out_[state_id].empty() ) {
                CoinPackedVector *osi_row = new CoinPackedVector(true);
                for( int j = 0; j < dtg.in_[state_id].size(); ++j ) {
                    int tr_id = dtg.in_[state_id][j];
                    if( !dtg.is_prevail_transition(tr_id) ) {
                        int oid = dtg.labels_[dtg.transitions_[tr_id].first]->id_;
                        //cout << "Prop: var=" << prop.var_ << ", id=" << prop.id_ << ", tr-id=" << tr_id << ", oid=" << oid << ", type=PROD" << endl;
                        osi_row->insert(oid, 1);
                    }
                }
                for( int j = 0; j < dtg.out_[state_id].size(); ++j ) {
                    int tr_id = dtg.out_[state_id][j];
                    if( !dtg.is_prevail_transition(tr_id) ) {
                        int oid = dtg.labels_[dtg.transitions_[tr_id].first]->id_;
                        //cout << "Prop: var=" << prop.var_ << ", id=" << prop.id_ << ", tr-id=" << tr_id << ", oid=" << oid << ", type=CONS" << endl;
                        osi_row->insert(oid, -1);
                    }
                }
                osi_rows.push_back(osi_row);
                prop.row_index_ = nconstraints_;
                ++nconstraints_;
            }
        }

    }
#else


    osi_row_lb.clear(); osi_row_ub.clear();

    add_first_const(&osi_col_lb);

    add_second_const(&osi_rows,osi_row_lb,osi_row_ub);

    add_third_const(&osi_rows,osi_row_lb,osi_row_ub);

    add_fourth_const(&osi_rows,osi_row_lb,osi_row_ub);

    if((use_tr_&0x1)==0){
        add_fifth_const(&osi_rows,osi_row_lb,osi_row_ub);

        add_sixth_const(&osi_rows,osi_row_lb,osi_row_ub);
    }

    if(0x1 & use_seq_){
        init_tmp_goal();
        //adding constraints from SEQ
        add_seventh_const(&osi_rows,osi_row_lb,osi_row_ub);
        add_eighth_const(&osi_rows,osi_row_lb,osi_row_ub);

        //tmp_goal_.clear();
    }



#endif
    cout << "LP: " << nconstraints_ << " base constraints created" << endl;

    // Add rows and create lb's and ub's for rows.
    osi_matrix->appendRows(osi_rows.size(), reinterpret_cast<CoinPackedVectorBase**>(&osi_rows[0]));

    #if 0
    for( int i = 0; i < osi_rows.size(); ++i ) {
        osi_row_lb[i] = -1e6; //-1.0 * osi_solver_->getInfinity();
        osi_row_ub[i] = osi_solver_->getInfinity();
    }
    #endif

    // Load matrix, set objective sense, and set row/col names
    osi_solver_->loadProblem(*osi_matrix, &osi_col_lb[0], &osi_col_ub[0], &osi_obj_fn[0], &osi_row_lb[0], &osi_row_ub[0]);
    osi_solver_->setObjSense(1);
    
    //set variables to being integers
  /*  for(int i=0;i<nvars_;++i){
        osi_solver_->setInteger(i);
    }*/

    // Initialize solver and clean.
    osi_solver_->messageHandler()->setLogLevel(0);
    osi_solver_->initialSolve();
    //osi_solver_->writeLp("order_relaxed");
    for( int i = 0; i < osi_rows.size(); ++i ) {
        delete osi_rows[i];
    }
    delete osi_matrix;
}

bool Heuristic::refine_model(const State &state) {
    // Solve LP for state, detect prevail for operators active in solution,
    // merge prevails with effects, and update model and LP.

    bool change = true;
    while( change ) {
        change = false;

        // solve lp for given state
        if(use_seq_)
            set_row_bounds(state);
        bool infeasible = solve_lp(state, true);
        return infeasible;


        // compute primitive operators that must be fixed
        vector<int> operators_to_fix;
        for( int i = 0; i < nprimitive_operators_; ++i ) {
            const Operator &op = *operators_[i];
            bool must_be_accounted_for = false;
            if( operators_active_in_solution_[i] ) {
                for( int j = 0; j < op.prevails_.size(); ++j ) {
                    int pid = op.prevails_[j]->id_;
                    if( pid < nprimitive_propositions_ ) {
                        //cout << "  " << *op.prevails_[j] << " is active prevail of " << op << endl;
                        must_be_accounted_for = true;
                        break;
                    }
                }
            }
            if( !checked_operators_[i] && must_be_accounted_for ) {
                if( debug_ ) cout << "Operator " << op << " scheduled for fluent merging" << endl;
                operators_to_fix.push_back(i);
            }
        }
        if( debug_ ) cout << "#operators to fix = " << operators_to_fix.size() << endl;

        // if nothing to fix, return
        if( operators_to_fix.empty() ) break;
        change = true;

        for( int i = 0; i < operators_to_fix.size(); ++i ) {
            Operator &op = *operators_[operators_to_fix[i]];
            if( checked_operators_[op.id_] ) continue;
            if( debug_ ) cout << "Fixing " << op << ": #prevails=" << op.prevails_.size() << ", #consumed=" << op.consumes_.size() << ", #produced=" << op.produces_.size() << endl;
            for( int j = 0; j < op.prevails_.size(); ++j ) {
                Proposition *first = op.prevails_[j];
                if( first->id_ >= nprimitive_propositions_ ) continue;
                if( debug_ ) cout << "Target proposition: " << *first << endl;
                for( int k = 0; k < op.consumes_.size(); ++k ) {
                    Proposition *second = op.consumes_[k];
                    if( second->id_ >= nprimitive_propositions_ ) continue;
                    //if( debug_ ) cout << "  Merge with " << *second << "..." << endl;
                    //if( !merge_propositions(first, second) ) goto fin;
                    //merge_propositions_using_dtgs(first, second);
                }
#if 0
                for( int k = 0; k < op.produces_.size(); ++k ) {
                    Proposition *second = op.produces_[k];
                    if( second->id_ >= nprimitive_propositions_ ) continue;
                    //cout << "  Merge with " << *second << "..." << endl;
                    if( !merge_propositions(first, second) ) goto fin;
                }
#endif
            }
            checked_operators_[op.id_] = true;
        }
        if( debug_ ) cout << "#operators = " << operators_.size() << endl;
    }

    return false;
}


pair<const UndefinedProposition*, bool> Heuristic::fetch_undefined(int var) {
    pair<map<int, int>::iterator, bool> p = undefined_propositions_.insert(make_pair(var, npropositions_));
    if( p.second ) { // new element was inserted into map
        UndefinedProposition *prop = new UndefinedProposition(npropositions_++, var);
        propositions_.push_back(prop);
        //cout << "New undefined prposition: " << *prop << endl;
        return make_pair(prop, true);
    } else {
        return make_pair(static_cast<UndefinedProposition*>(propositions_[p.first->second]), false);
    }
}

int Heuristic::fetch_lpvar(const Operator *op) {
    if( op->id_ == -1 ) {
        assert(dynamic_cast<const OperatorCopy*>(op) != 0);
        const_cast<Operator*>(op)->id_ = noperators_++;
        operators_.push_back(const_cast<Operator*>(op));
        CoinPackedVector osi_col(true);
        osi_solver_->addCol(osi_col, 0, osi_solver_->getInfinity(), op->get_cost());
    }
    return op->id_;
}

bool Heuristic::refine_lp(Operator *op, Proposition *np, bool operator_consumes_fluent) {
    // check if e have reached maximum number of operators
    //if( noperators_ >= 10 * nprimitive_operators_ ) return false;

    // create new operator
    CopyOperator *nop = 0;
    if( operator_consumes_fluent ) {
        nop = new CopyOperator(noperators_++, op, true, np->id_);
        np->consumed_by_.push_back(nop);
        nop->consumes_.push_back(np);
    } else {
        nop = new CopyOperator(noperators_++, op, false, np->id_);
        np->produced_by_.push_back(nop);
        nop->produces_.push_back(np);
    }
    operators_.push_back(nop);

    // create new LP variable for new operator
    CoinPackedVector *osi_row = new CoinPackedVector(true);
    osi_solver_->addCol(*osi_row, 0, osi_solver_->getInfinity(), nop->get_cost());
    set_column_name(nop);

    // create/update constraint for operator copies. Copies are indexed with
    // (sign * pid, varid) where sign is -1 or +1 if consumer or producer
    pair<int, int> index((nop->is_consumer_ ? -1 : 1) * (1 + op->id_), np->var_);
    if( operator_copies_[index].empty() ) { // create
        operator_copies_[index].push_back(nop->id_);
        row_index_for_operator_copies_[index] = nconstraints_++;
        osi_row->insert(op->id_, 1);
        osi_row->insert(nop->id_, -1);
        osi_solver_->addRow(*osi_row, 0, osi_solver_->getInfinity());
        delete osi_row;
    } else { // update
        // OSI doesn't provide a easy way to modify constraints. Since the
        // new constraint is a strengthening of the old, add a new one and
        // keep the old.
        ++ninactive_constraints_;
        operator_copies_[index].push_back(nop->id_);
        row_index_for_operator_copies_[index] = nconstraints_++;
        osi_row->insert(op->id_, 1);
        for( int i = 0; i < operator_copies_[index].size(); ++i )
            osi_row->insert(operator_copies_[index][i], -1);
        osi_solver_->addRow(*osi_row, 0, osi_solver_->getInfinity());
        delete osi_row;
#if 0
        cout << "[sz=" << operator_copies_[index].size() << "] Disjoint copies of " << *op
             << " for index=(" << index.first << "," << index.second << "):" << endl;
        for( int i = 0; i < operator_copies_[index].size(); ++i )
            cout << "    " << *operators_[operator_copies_[index][i]] << endl;
#endif
    }
    return true;
}

void Heuristic::set_row_bounds(const State &state) {
    // Set row bounds and type

    int init = begin_const_seq_;
    for(int var=0;var<nvariables_;++var){
      for(int val=0;val<g_variable_domain[var];++val){
        
        const Proposition *prop = primitive_propositions_[var][val];
            double lower_bound = 0, upper_bound = 0;

            if( prop->is_goal_var() ) { // there is a unique goal state (modulo this var)
                if( prop->holds_at(state) && !prop->is_mutex_with_goal_ ) {
                    lower_bound = 0;
                    upper_bound = prop->is_safe() ? 0 : osi_solver_->getInfinity();
                } else if( prop->holds_at(state) && prop->is_mutex_with_goal_ ) {
                    lower_bound = -1;
                    upper_bound = prop->is_safe() ? -1 : osi_solver_->getInfinity();
                } else if( !prop->holds_at(state) && !prop->is_mutex_with_goal_ ) {
                    lower_bound = 1;
                    upper_bound = prop->is_safe() ? 1 : osi_solver_->getInfinity();
                } else if( !prop->holds_at(state) && prop->is_mutex_with_goal_ ) {
                    lower_bound = 0;
                    upper_bound = prop->is_safe() ? 0 : osi_solver_->getInfinity();
                }
            } else { // there is *no* unique goal state (modulo this var)
                if( prop->holds_at(state) && !prop->is_mutex_with_goal_ ) {
                    lower_bound = -1;
                    upper_bound = osi_solver_->getInfinity();
                } else if( prop->holds_at(state) && prop->is_mutex_with_goal_ ) {
                    lower_bound = -1;
                    upper_bound = prop->is_safe() ? -1 : osi_solver_->getInfinity();
                } else if( !prop->holds_at(state) && !prop->is_mutex_with_goal_ ) {
                    lower_bound = 0;
                    upper_bound = osi_solver_->getInfinity();
                } else if( !prop->holds_at(state) && prop->is_mutex_with_goal_ ) {
                    lower_bound = 0;
                    upper_bound = prop->is_safe() ? 0 : osi_solver_->getInfinity();
                }
            }
            //cout << "bound: p=" << *prop << ", lb=" << lower_bound << ", ub=" << upper_bound << endl;
            osi_solver_->setRowLower(init, lower_bound);
            if( use_ubs_ ) 
                osi_solver_->setRowUpper(init, upper_bound);
            init++;
    }
    }
}

bool Heuristic::compute_landmarks(const State &state) {
    landmarks_ = 0;
    lmcut_value_ = 0;

    // Compute lmgraph landmarks
    if( use_landmarks_ & 0x1 ) {
        bool dead_end = lm_status_manager_->update_lm_status(state);
        if( dead_end ) return true;

        if( debug_ ) cout << "Start-of-Landmarks: lmgraph" << endl;
        const set<LandmarkNode*>& nodes = lm_graph_->get_nodes();
        for( set<LandmarkNode*>::iterator node_it = nodes.begin(); node_it != nodes.end(); ++node_it ) {
            LandmarkNode& node = **node_it;
            int lmn_status = node.get_status();
            if( lmn_status != lm_reached ) {
                //cout << "    ";
                //lm_graph_->dump_node(&node);
                const set<int> &achievers = get_achievers(lmn_status, node);
                assert(!achievers.empty());
                if( debug_ ) cout << "    lm=[";
                HittingSets::Landmark *lm = HittingSets::Landmark::allocate();
                for( set<int>::const_iterator it = achievers.begin(); it != achievers.end(); ++it ) {
                    lm->insert(*it, 1);
                    if( debug_ ) cout << *operators_[*it] << "," << flush;
                }
                if( debug_ ) cout << "]" << endl;
                lm->next_ = landmarks_;
                landmarks_ = lm;
            }
        }
        if( debug_ ) cout << "End-of-Landmarks: lmgraph" << endl;
    }

    // Compute LM-cut landmarks
    if( use_landmarks_ & 0x2 ) {
        lmcut_engine_->max_value_ = lmcut_engine_->value_ = 0;
        lmcut_engine_->compute_landmarks(state, 1);
        if( lmcut_engine_->max_value_ == numeric_limits<int>::max() ) {
            lmcut_value_ = DEAD_END;
            return true;
        }
        lmcut_value_ = lmcut_engine_->max_value_ - 1;
        if( debug_ ) cout << "LM-cut value = " << lmcut_value_ << endl;

        if( debug_ ) cout << "Start-of-Landmarks: lmcut" << endl;
        for( HittingSets::Landmark *lm = const_cast<HittingSets::Landmark*>(lmcut_engine_->passes_[0].second); lm != 0; ) {
            HittingSets::Landmark *l = lm;
            lm = lm->next_;
            if( rproblem_.operators_[*l->begin()].op_ == 0 ) {
                // skip this landmark
                HittingSets::Landmark::deallocate(l);
            } else {
                l->next_ = landmarks_;
                landmarks_ = l;
                if( debug_ ) {
                    cout << "    lm=[";
                    for( Utils::BitmapSet::const_iterator it = l->begin(); it != l->end(); ++it )
                        cout << *operators_[*it] << "," << flush;
                    cout << "]" << endl;
                }
            }
        }
        if( debug_ ) cout << "End-of-Landmarks: lmcut" << endl;
    }

    return false;
}

void Heuristic::insert_landmark_constraints() {
    CoinPackedVector *osi_row = new CoinPackedVector(true);
    for( const HittingSets::Landmark *lm = landmarks_; lm != 0; lm = lm->next_ ) {
        for( Utils::BitmapSet::const_iterator it = lm->begin(); it != lm->end(); ++it )
            osi_row->insert(*it, 1);
        osi_solver_->addRow(*osi_row, 1, osi_solver_->getInfinity());
        osi_row->clear();
    }
    delete osi_row;
}

bool Heuristic::solve_lp(const State &state, bool set_active_operators) {
    // call LP solver
    try {
        //Added for DR + LM-cut
        if(use_landmarks_ & 0x2)
            insert_landmark_constraints();
        //osi_solver_->writeLp(ss.str().c_str());
        osi_solver_->resolve();
        lp_value_ = (float)osi_solver_->getObjValue();
        lp_solution_.resize(noperators_);
        bcopy(osi_solver_->getColSolution(), &lp_solution_[0], noperators_ * sizeof(double));

        if( debug_ ) {
            cout << "Solution: status=";
            if( osi_solver_->isAbandoned() ) cout << "ABANDONED";
            if( osi_solver_->isProvenOptimal() ) cout << "OPTIMAL";
            if( osi_solver_->isProvenPrimalInfeasible() ) cout << "PRIMAL-INFEASIBLE";
            if( osi_solver_->isProvenDualInfeasible() ) cout << "DUAL-INFEASIBLE";
            if( osi_solver_->isPrimalObjectiveLimitReached() ) cout << "PRIMAL-LIMIT";
            if( osi_solver_->isDualObjectiveLimitReached() ) cout << "DUAL-LIMIT";
            if( osi_solver_->isIterationLimitReached() ) cout << "ITER-LIMIT";
            cout << ", value=" << lp_value_ << ", x*=[" << endl;
            for( int i = 0; i < noperators_; ++i ) {
                if( (float)lp_solution_[i] > epsilon_ ) {
                    cout << "  " << *operators_[i] << "=" << lp_solution_[i]
                         << ", cost=" << operators_[i]->get_cost()
                         << endl;
                }
            }
            cout << "]" << endl;
        }

        if( osi_solver_->isProvenPrimalInfeasible() ) {
            remove_landmark_constraints();
            return true;
        }

        // save solution
        if( set_active_operators ) {
            operators_active_in_solution_ = vector<bool>(noperators_, false);
            for( int i = 0; i < noperators_; ++i ) {
                operators_active_in_solution_[i] = (float)lp_solution_[i] > epsilon_;
            }
        }

        remove_landmark_constraints();
    } catch( CoinError &ex ) {
        cerr << "Exception:" << ex.message() << endl
             << " from method " << ex.methodName() << endl
             << " from class " << ex.className() << endl;
        exit(-1);
    }
    return false;
}


int Heuristic::compute_heuristic(const State &state) {
    

    //correction for S(a) values
    //and correct for integer values
    correct_model(state);

/*
    bool infeasible = solve_lp(state,true);
    int heuristic_value = -1;
    if(infeasible){
        heuristic_value = DEAD_END;
    }
    else{
        heuristic_value = (int)ceilf(lp_value_);
    }
*/
    // Compute hmax value: if dead end, return immediately.

    int hmax_value = safe_to_max_with_hmax_ && (hmax_heuristic_ != 0) ? hmax_heuristic_->compute_heuristic(state) : 0;
    if( hmax_value == DEAD_END ) {
        //histogram_push(0, numeric_limits<int>::max());
        return DEAD_END;
    }

    if( (use_landmarks_ & 0x1) && test_goal(state) ) {
        //histogram_push(0, 0);
        return 0;
    }

    bool dead_end = compute_landmarks(state);
    if( dead_end ) {
        //histogram_push(0, numeric_limits<int>::max());
        return DEAD_END;
    }

    int heuristic_value = -1;
    bool infeasible = refine_model(state);
    remove_landmarks();
    //exit(-2);

    if( infeasible ) {
        heuristic_value = DEAD_END;
    } else {
        heuristic_value = (int)ceilf(lp_value_);
        if( heuristic_value < lmcut_value_ ) {
            cout << "Warning: value is lower than lmcut: lp=" << heuristic_value << ", lmcut=" << lmcut_value_ << endl;
            heuristic_value = lmcut_value_;
        }
        if( safe_to_max_with_hmax_ ) heuristic_value = max(heuristic_value, hmax_value);
    }
    //histogram_push(0, heuristic_value);
    //cout << "lp-value " << lp_value_ << " h " << heuristic_value << endl;


    
    //cout <<"value for heuristic = " << lp_value_ << endl;
    return heuristic_value;
}

bool Heuristic::reach_state(const State& parent_state, const ::Operator &op, const State& state) {
    if( use_landmarks_ & 0x1 )
        lm_status_manager_->update_reached_lms(parent_state, op, state);
    return true;
}

void Proposition::dump(ostream &os, bool full_info) const {
    if( full_info ) {
        if( !prevail_of_.empty() ) {
            os << "Prevail of:";
            for( int i = 0; i < prevail_of_.size(); ++i ) os << " " << *prevail_of_[i];
            os << endl;
        }
        if( !consumed_by_.empty() ) {
            os << "Consumed by:";
            for( int i = 0; i < consumed_by_.size(); ++i ) os << " " << *consumed_by_[i];
            os << endl;
        }
        if( !produced_by_.empty() ) {
            os << "Produced by:";
            for( int i = 0; i < produced_by_.size(); ++i ) os << " " << *produced_by_[i];
            os << endl;
        }
    }
}

void UndefinedProposition::dump(ostream &os, bool full_info) const {
    os << "f" << id_ << ".undef(var=" << var_ << ")" << flush;
    if( full_info ) os << endl;
}

void PrimitiveProposition::dump(ostream &os, bool full_info) const {
    string name = g_fact_names[var_][val_];
    if( name.compare(0, 5, "Atom ") == 0 )
        name = name.substr(5);
    else if( name.compare(0, 12, "NegatedAtom ") == 0 )
        name = name.substr(12);
    os << "f" << id_ << "." << name << flush;
    if( full_info ) {
        os << endl;
        Proposition::dump(os, true);
    }
}


void Operator::dump(ostream &os, bool full_info) const {
    if( full_info ) {
        if( !prevails_.empty() ) {
            os << "  Prevails:";
            for( int i = 0; i < prevails_.size(); ++i ) os << " " << *prevails_[i];
            os << endl;
        }
        if( !consumes_.empty() ) {
            os << "  Consumes:";
            for( int i = 0; i < consumes_.size(); ++i ) os << " " << *consumes_[i];
            os << endl;
        }
        if( !produces_.empty() ) {
            os << "  Produces:";
            for( int i = 0; i < produces_.size(); ++i ) os << " " << *produces_[i];
            os << endl;
        }
    }
}

void PrimitiveOperator::dump(ostream &os, bool full_info) const {
    os << "x" << id_ << ".(" << base_op_.get_name() << ")" << flush;
    if( full_info ) {
        os << endl;
        Operator::dump(os, true);
    }
}

void CopyOperator::dump(ostream &os, bool full_info) const {
    os << "x" << id_ << ".copyof_" << *op_ << "."
       << (is_consumer_ ? "consumes_f" : "produces_f")
       << fluent_ << flush;
    if( full_info ) {
        os << endl;
        Operator::dump(os, true);
    }
}

void OperatorCopy::dump(ostream &os, bool full_info) const {
    os << "x" << id_ << ".copyOf_" << *op_ << flush;
}

int Proposition::nprimitive_variables_;
const vector<Variable*>* Proposition::variables_;
//const map<pair<int, int>, int>* Proposition::merge_variables_;

const vector<set<int> >* Operator::propositions_mutex_with_precondition_;
const vector<set<int> >* Operator::propositions_mutex_with_postcondition_;

ScalarEvaluator *_parse(OptionParser &parser) {
    //Added by flow
    parser.add_option<bool>("empty_base_lp", false, string("use an empty base lp"));
    parser.add_option<int>("landmarks", 0, "landmark factory: 0=no factory (default), 1=lmgraph-factory, 2=lmcut-factory");
    parser.add_option<LandmarkGraph *>("lm_graph", 0, "only used (and required) when landmarks=1");
    parser.add_option<bool>("use_ubs", true, string("use upper bounds in base LP"));
    parser.add_option<string>("lp_solver", string("clp"), string("clp (default), grb, cplex"));
    parser.add_option<float>("epsilon", EPSILON, string("epsilon for marking operator active (default=0.0001)"));
    parser.add_option<bool>("debug", false, string("print debug information (default false)"));

     //Added by del_relaxation
    parser.add_option<int>("seq", 0, string("adding SEQ to del_rel: 0=simple del_rel (default), 1=SEQ+del_rel"));
    parser.add_option<int>("tr", 0, string("adding tr to del_rel: 0=without time relaxation (default), 1=with TR"));


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

Plugin<ScalarEvaluator> _plugin("delete_rel", _parse);

} // end of namespace

