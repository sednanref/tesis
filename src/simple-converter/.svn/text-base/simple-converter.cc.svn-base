#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;


struct Literal {
    bool negated;
    string atom;
};

struct Conjunction {
    vector<Literal> literals;
};

struct Effect {
    Conjunction conditions;
    Literal effect;
};

struct Action {
    string name;
    Conjunction precondition;
    vector<Effect> effects;
};


class Matcher;


static void error(const string &msg);
static void convert(const char *domain_filename,
                    const char *problem_filename);
static void dump_sas_file(
    const set<string> &atoms,
    const set<string> &init,
    const Conjunction &goal,
    const vector<Action> &actions);
static vector<pair<int, int> > convert_conjunction(
    const Conjunction &conj, const map<string, int> &atom_to_varno);
static void tokenize(const char *filename, vector<string> &result);
static Literal parse_literal(Matcher &matcher, const set<string> &atoms);
static Conjunction parse_conjunction(Matcher &matcher,
                                     const set<string> &atoms);
static Action parse_action(Matcher &matcher, const set<string> &atoms);


class Matcher {
    vector<string> tokens;
    size_t position;
public:
    explicit Matcher(const vector<string> &tokens_)
        : tokens(tokens_), position(0) {
    }

    ~Matcher() {
    }

    string peek(size_t offset = 0) {
        if (position + offset >= tokens.size())
            fail("unexpected end of file");
        return tokens[position + offset];
    }

    string get() {
        string result = peek();
        ++position;
        return result;
    }

    void skip() {
        get();
    }

    void match(const string &token) {
        if (get() != token)
            fail(string("mismatch, expecting '") + token + "'");
    }

    void match_end() {
        if (position != tokens.size())
            fail("expected end of file");
    }

    void fail(const string &msg) const {
        error(msg);
    }
};


static void error(const string &msg) {
    cerr << "error: " << msg << endl << "aborting." << endl;
    exit(1);
}


static void convert(const char *domain_filename,
                    const char *problem_filename) {
    vector<string> domain_tokens;
    tokenize(domain_filename, domain_tokens);
    /*
    for (size_t i = 0; i < domain_tokens.size(); ++i)
        cout << "*" << domain_tokens[i] << "*" << endl;
    */

    vector<string> problem_tokens;
    tokenize(problem_filename, problem_tokens);
    /*
    for (size_t i = 0; i < problem_tokens.size(); ++i)
        cout << "*" << problem_tokens[i] << "*" << endl;
    */

    Matcher domain(domain_tokens);

    // parse "(define (domain FOO)"
    cout << "parse domain header..." << endl;
    domain.match("(");
    domain.match("define");
    domain.match("(");
    domain.match("domain");
    domain.skip();
    domain.match(")");

    // parse "(:requirements ... )"
    cout << "parse requirements..." << endl;
    domain.match("(");
    if( domain.peek() == ":requirements" ) {
        domain.match(":requirements");
        while (domain.get() != ")")
            ;
        domain.match("(");
    }

    // parse "(:predicates (FOO) (BAR) ... )"
    cout << "parse predicates..." << endl;
    set<string> atoms;
    domain.match(":predicates");
    while (domain.peek() != ")") {
        domain.match("(");
        string atom = domain.get();
        domain.match(")");
        if (atoms.count(atom)) {
            error("duplicate atom: " + atom);
        }
        atoms.insert(atom);
    }
    domain.match(")");

    cout << "parse actions..." << endl;
    vector<Action> actions;
    while (domain.peek() != ")")
        actions.push_back(parse_action(domain, atoms));

    // parse end of domain file
    cout << "parse end of domain file..." << endl;
    domain.match(")");
    domain.match_end();


    Matcher problem(problem_tokens);

    // parse "(define (problem FOO) (:domain BAR)"
    cout << "parse problem header..." << endl;
    problem.match("(");
    problem.match("define");
    problem.match("(");
    problem.match("problem");
    problem.skip();
    problem.match(")");
    problem.match("(");
    problem.match(":domain");
    problem.skip();
    problem.match(")");

    // parse "(:init (FOO) (BAR) ... )"
    cout << "parse initial state..." << endl;
    set<string> init;
    problem.match("(");
    problem.match(":init");
    while (problem.peek() != ")") {
        problem.match("(");
        string atom = problem.get();
        problem.match(")");
        if (!atoms.count(atom)) {
            error("unknown atom in init: " + atom);
        }
        init.insert(atom);
    }
    problem.match(")");

    // parse (:goal (and (FOO) (BAR) ...))
    problem.match("(");
    problem.match(":goal");
    Conjunction goal = parse_conjunction(problem, atoms);
    problem.match(")");

    // parse end of problem file
    cout << "parse end of problem file..." << endl;
    problem.match(")");
    problem.match_end();

    dump_sas_file(atoms, init, goal, actions);
}


static void dump_sas_file(
    const set<string> &atoms,
    const set<string> &init,
    const Conjunction &goal,
    const vector<Action> &actions) {
    cout << "Writing output.sas..." << endl;
    ofstream sas_file("output.sas");

    sas_file << "begin_version" << endl << 3 << endl << "end_version" << endl;
    sas_file << "begin_metric" << endl << 0 << endl << "end_metric" << endl;

    int num_vars = 0;
    map<string, int> atom_to_varno;
    vector<string> varno_to_atom;
    for (set<string>::const_iterator iter = atoms.begin();
         iter != atoms.end(); ++iter) {
        varno_to_atom.push_back(*iter);
        atom_to_varno[*iter] = num_vars++;
    }

    sas_file << num_vars << endl;
    for (int i = 0; i != num_vars; ++i) {
        const string &atom = varno_to_atom[i];
        sas_file << "begin_variable" << endl
                 << "var" << i << endl
                 << -1 << endl
                 << 2 << endl
                 << "Atom " << atom << "()" << endl
                 << "NegatedAtom " << atom << "()" << endl
                 << "end_variable" << endl;
    }

    sas_file << 0 << endl;

    sas_file << "begin_state" << endl;
    for (int i = 0; i != num_vars; ++i) {
        const string &atom = varno_to_atom[i];
        int initial_value = init.count(atom) ? 0 : 1;
        sas_file << initial_value << endl;
    }
    sas_file << "end_state" << endl;

    vector<pair<int, int> > goal_pairs = convert_conjunction(
        goal, atom_to_varno);
    sas_file << "begin_goal" << endl
             << goal_pairs.size() << endl;
    for (size_t i = 0; i < goal_pairs.size(); ++i)
        sas_file << goal_pairs[i].first << " " << goal_pairs[i].second << endl;
    sas_file << "end_goal" << endl;

    sas_file << actions.size() << endl;
    for (size_t i = 0; i < actions.size(); ++i) {
        const Action &action = actions[i];
        vector<pair<int, int> > pre_prevail = convert_conjunction(
            action.precondition, atom_to_varno);
        set<int> eff_vars;
        for (size_t j = 0; j < action.effects.size(); ++j) {
            int eff_var = atom_to_varno[action.effects[j].effect.atom];
            eff_vars.insert(eff_var);
        }

        vector<pair<int, int> > prevail;
        map<int, int> var_to_pre;
        for (size_t j = 0; j < pre_prevail.size(); ++j) {
            int varno = pre_prevail[j].first;
            int value = pre_prevail[j].second;
            if (eff_vars.count(varno)) {
                var_to_pre[varno] = value;
            } else {
                prevail.push_back(pre_prevail[j]);
            }
        }

        sas_file << "begin_operator" << endl
             << action.name << endl
             << prevail.size() << endl;
        for (size_t j = 0; j < prevail.size(); ++j)
            sas_file << prevail[j].first << " " << prevail[j].second << endl;
        sas_file << action.effects.size() << endl;
        for (size_t j = 0; j < action.effects.size(); ++j) {
            const Effect &eff = action.effects[j];
            vector<pair<int, int> > eff_cond = convert_conjunction(
                eff.conditions, atom_to_varno);
            int eff_var = atom_to_varno[eff.effect.atom];
            int post_val = eff.effect.negated ? 1 : 0;
            sas_file << eff_cond.size();
            for (size_t k = 0; k < eff_cond.size(); ++k)
                sas_file << " " << eff_cond[k].first
                         << " " << eff_cond[k].second;
            int pre_val = -1;
            if (var_to_pre.count(eff_var))
                pre_val = var_to_pre[eff_var];
            sas_file << " " << eff_var << " " << pre_val << " "
                     << post_val << endl;
        }
        sas_file << 0 << endl
                 << "end_operator" << endl;
    }

    sas_file << 0 << endl;
}


static vector<pair<int, int> > convert_conjunction(
    const Conjunction &conj, const map<string, int> &atom_to_varno) {
    set<int> included_vars;
    vector<pair<int, int> > result;
    for (size_t i = 0; i < conj.literals.size(); ++i) {
        Literal l = conj.literals[i];
        int varno = atom_to_varno.at(l.atom);
        int value = l.negated ? 1 : 0;
        if (included_vars.count(varno))
            error("conjunction with duplicate variable");
        included_vars.insert(varno);
        result.push_back(make_pair(varno, value));
    }
    sort(result.begin(), result.end());
    return result;
}


static Literal parse_literal(Matcher &matcher, const set<string> &atoms) {
    Literal result;
    matcher.match("(");
    if (matcher.peek() == "not") {
        matcher.match("not");
        result = parse_literal(matcher, atoms);
        result.negated = !result.negated;
    } else {
        string atom = matcher.get();
        if (!atoms.count(atom))
            error(string("unknown atom: ") + atom);
        result.negated = false;
        result.atom = atom;
    }
    matcher.match(")");
    return result;
}


static Conjunction parse_conjunction(Matcher &matcher,
                                     const set<string> &atoms) {
    Conjunction result;
    if (matcher.peek(1) == "and") {
        matcher.match("(");
        matcher.match("and");
        while (matcher.peek() != ")")
            result.literals.push_back(parse_literal(matcher, atoms));
        matcher.match(")");
    } else {
        result.literals.push_back(parse_literal(matcher, atoms));
    }
    return result;
}


static void parse_single_effect(Matcher &matcher, Action &action, const set<string> &atoms) {
    if (matcher.peek(1) == "when") {
        matcher.match("(");
        matcher.match("when");
        Conjunction eff_cond = parse_conjunction(matcher, atoms);
        Conjunction eff_lits = parse_conjunction(matcher, atoms);
        for (size_t i = 0; i < eff_lits.literals.size(); ++i) {
            Effect eff;
            eff.conditions = eff_cond;
            eff.effect = eff_lits.literals[i];
            action.effects.push_back(eff);
        }
        matcher.match(")");
    } else {
        Effect eff;
        eff.effect = parse_literal(matcher, atoms);
        action.effects.push_back(eff);
    }
}


static void parse_effect(Matcher &matcher, Action &action, const set<string> &atoms) {
    if( matcher.peek(1) == "and" ) {
        matcher.match("(");
        matcher.match("and");
        while (matcher.peek() != ")")
            parse_single_effect(matcher, action, atoms);
        matcher.match(")");
    } else {
        parse_single_effect(matcher, action, atoms);
    }
}


static Action parse_action(Matcher &matcher, const set<string> &atoms) {
    //parse "(:action ... )"

    //cout << "parsing action..." << endl;

    Action action;
    matcher.match("(");
    matcher.match(":action");
    action.name = matcher.get();
    //cout << action.name << endl;

    if( matcher.peek() == ":parameters" ) {
        matcher.match(":parameters");
        matcher.match("(");
        matcher.match(")");
    }

    if( matcher.peek() == ":precondition" ) {
        matcher.match(":precondition");
        action.precondition = parse_conjunction(matcher, atoms);
    }

    //if( matcher.peek() != ":effect" ) for(int i =0;i<10;++i) cout << matcher.peek(i) << endl;
    assert(matcher.peek() == ":effect");
    matcher.match(":effect");
    parse_effect(matcher, action, atoms);
    matcher.match(")");

    return action;
}


static void tokenize(const char *filename, vector<string> &result) {
    ifstream file(filename);
    while (true) {
        if (file.eof())
            return;
        if (file.fail())
            error(string("problem reading ") + filename);
        string line;
        getline(file, line);

        // Tokenize line.
        size_t pos = 0;
        while (pos < line.length()) {
            // If we're at a separator character, advance one character.
            // Otherwise, advance to the next separator character.
            size_t next_pos = line.find_first_of("() \t\n;", pos);
            if (next_pos == pos)
                next_pos += 1;
            if (next_pos == string::npos)
                next_pos = line.length();
            string token = line.substr(pos, next_pos - pos);
            if (token[0] == ';')
                next_pos = line.length();
            else if (token[0] != ';' && token[0] != ' ' && token[0] != '\t' &&
                token[0] != '\n')
                result.push_back(token);
            pos = next_pos;
        }
    }
}


int main(int argc, char **argv) {
    if (argc != 3) {
        cerr << "usage: " << argv[0] << " DOMAIN_FILE PROBLEM_FILE" << endl;
        exit(2);
    }
    try {
        convert(argv[1], argv[2]);
    } catch (const exception &e) {
        error(e.what());
    }
}
