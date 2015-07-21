#include "globals.h"
#include "operator.h"
#include "option_parser.h"
#include "ext/tree_util.hh"
#include "timer.h"
#include "utilities.h"
#include "search_engine.h"

#include <fcntl.h>
#include <unistd.h>

#include <iostream>
#include <new>

using namespace std;

int main(int argc, const char **argv) {
    register_event_handlers();

    if (argc < 2) {
        cout << OptionParser::usage(argv[0]) << endl;
        exit_with(EXIT_INPUT_ERROR);
    }

    if (string(argv[1]).compare("--help") != 0)
        read_everything(cin);

    SearchEngine *engine = 0;

    //the input will be parsed twice:
    //once in dry-run mode, to check for simple input errors,
    //then in normal mode
    try {
        OptionParser::parse_cmd_line(argc, argv, true);
        engine = OptionParser::parse_cmd_line(argc, argv, false);
    } catch (ParseError &pe) {
        cerr << pe << endl;
        exit_with(EXIT_INPUT_ERROR);
    }

    // solver initial states given in input
    assert(g_initial_state != 0);
    Timer acc_search_timer;
    do {
        Timer search_timer;
        g_initial_state->dump_pddl();
        engine->search(*g_initial_state);
        //g_timer.stop();

        if (engine->found_solution()) {
            engine->save_plan_if_necessary();
            cout << "SOLUTION" << endl;
            write(STDERR_FILENO, "S", 1);
        } else {
            cout << "FAILURE" << endl;
            write(STDERR_FILENO, "F", 1);
        }

        //engine->statistics();
        //engine->heuristic_statistics();
        //cout << "Search time: " << search_timer << endl;
        //cout << "Total time: " << g_timer << endl;

        // read next initial state
        while( isspace(cin.peek()) ) (int)cin.get();
        //cout << "peek='" << (int)cin.peek() << "=" << cin.peek() << "'" << endl;
        string line;
        getline(cin, line);
        //cout << "LINE='" << line << "'" << endl;
        if( line == "exit" ) {
            g_initial_state = 0;
        } else if( line == "state" ) {
            engine->reset();
        OptionParser::parse_cmd_line(argc, argv, true);
        engine = OptionParser::parse_cmd_line(argc, argv, false);
            read_initial_state(cin);
        } else {
            cout << "error: unrecognized command '" << line << "'" << endl;
            break;
        }
    } while( g_initial_state != 0 );

    cout << "Accumulated search time: " << acc_search_timer << endl;
    cout << "Accumulated total time: " << g_timer << endl;

    exit_with(EXIT_PLAN_FOUND);
}
