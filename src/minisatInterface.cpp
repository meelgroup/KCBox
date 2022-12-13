/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "CustomizedSolver.h"
#include "minisatInterface.h"


namespace Minisat {

using namespace std;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", solver.starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


static Solver* solver = NULL;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:


static void Solver_AddClauses(vector<vector<int>>& clauses)
{
    assert( solver != NULL );
    size_t i, j;
    int     lit, var;
    vec<Lit> lits;
    for (i = 0; i < clauses.size(); i++) {
        vector<int> & cl = clauses[i];
        for (j = 0; j < cl.size(); j++){
            lit = cl[j];
            assert(lit != 0);
            var = abs(lit)-1;
            while (var >= solver->nVars()) solver->newVar();
            lits.push( (lit > 0) ? mkLit(var) : ~mkLit(var) );
        }
        solver->addClause(lits);
        lits.clear();
    }
}

extern int8_t Ext_Solve( vector<vector<int>>& clauses, Extra_Output & output )
{
    try {
        int paramc = 1;
        char* params[1];
        params[0] = "minisat";
        setUsageHelp("USAGE: %s [options] [input-file] \n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        if (false) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);

        parseOptions(paramc, params, true);//{{{printf("here.3\n");fflush(stdin);}}}

        CustomizedSolver S;
        double initial_time = cpuTime();

        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            } }

        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n"); }

        if (paramc == 2) {
            gzFile in = gzopen(params[1], "rb");
            if (in == NULL) {
                printf("ERROR! Could not open file: %s\n", params[1]);
                exit(1);
            }
            parse_DIMACS(in, *solver);
            gzclose(in);
        }
        else if (paramc > 2) {
            printf("Use '--help' for help.\n");
        }
        S.Add_Clauses( clauses );

        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }

        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
            printf("|                                                                             |\n"); }

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        if (!solver->simplify()){
            if (solver->verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by unit propagation\n");
                printStats(*solver);
                printf("\n");
                printf("UNSATISFIABLE\n");
            }
            return 0;
        }
        vec<Lit> assumps;
        lbool ret = solver->solveLimited(assumps);
        if (solver->verbosity > 0) {
            printStats(*solver);
            printf("\n");
            printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        }
        if (ret == l_True) {
            output.Gather_Output( S );
            return 1;
        }
        else if (ret == l_False) return 0;
        else return -1;

    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}

static void Add_Model( vector<vector<int8_t>> & extmodels )
{
    assert( solver != NULL && solver->okay() );
    vector<int8_t> emodel( solver->nVars() + 1 );
    for ( size_t i = 0; i < solver->nVars(); i++ ) {
        if ( solver->model[i] == l_Undef ) {
            emodel[i+1] = -1;
        }
        else if ( solver->model[i] == l_False ) {
             emodel[i+1] = 0;
        }
        else {
            emodel[i+1] = 1;
        }
    }
    extmodels.push_back( emodel );
}

static void Add_Marked_Model( vec<bool> & model_seen, vector<vector<int8_t>> & extmodels )
{
    assert( solver != NULL && solver->okay() );
    vector<int8_t> emodel( solver->nVars() + 1 );
    for ( size_t i = 0; i < solver->nVars(); i++ ) {
        if ( solver->model[i] == l_Undef ) {
            model_seen[i + i] = true;
            model_seen[i + i + 1] = true;
            emodel[i+1] = -1;
        }
        else if ( solver->model[i] == l_False ) {
            model_seen[i + i + 1] = true;  // neg appears
            emodel[i+1] = 0;
        }
        else {
            model_seen[i + i] = true;  // pos appears
            emodel[i+1] = 1;
        }
    }
    extmodels.push_back( emodel );
}

static void Mark_Model( vec<bool> & model_seen )
{
    assert( solver != NULL && solver->okay() );
    for ( size_t i = 0; i < solver->nVars(); i++ ) {
        if ( solver->model[i] == l_Undef ) {
            model_seen[i + i] = true;
            model_seen[i + i + 1] = true;
        }
        else if ( solver->model[i] == l_False ) {
            model_seen[i + i + 1] = true;  // neg appears
        }
        else {
            model_seen[i + i] = true;  // pos appears
        }
    }
}

static void Mark_Models( vec<bool> & model_seen, vector<vector<int8_t>> & extmodels )
{
    for ( size_t m = 0; m < extmodels.size(); m++ ) {
        for ( size_t i = 0; i < solver->nVars(); i++ ) {
            if ( extmodels[m][i+1] == -1 ) {
                model_seen[i + i] = true;
                model_seen[i + i + 1] = true;
            }
            else if ( extmodels[m][i+1] == 0 ) model_seen[i + i + 1] = true;
            else model_seen[i + i] = true;
        }
    }
}

extern bool Ext_Backbone( vector<vector<int>>& clauses, Extra_Output & output )
{
    try {
        int paramc = 1;
        char* params[1];
        params[0] = "minisat";
        setUsageHelp("USAGE: %s [options] [input-file] \n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        if (false) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);

        parseOptions(paramc, params, true);//{{{printf("here.3\n");fflush(stdin);}}}

        CustomizedSolver S;
        double initial_time = cpuTime();

        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            } }

        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n"); }

        if (paramc == 2) {
            gzFile in = gzopen(params[1], "rb");
            if (in == NULL) {
                printf("ERROR! Could not open file: %s\n", params[1]);
                exit(1);
            }
            parse_DIMACS(in, *solver);
            gzclose(in);
        }
        else if (paramc > 2) {
            printf("Use '--help' for help.\n");
        }
        S.Add_Clauses( clauses );

        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }

        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
            printf("|                                                                             |\n"); }

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        if (!solver->simplify()){
            if (solver->verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by unit propagation\n");
                printStats(*solver);
                printf("\n");
                printf("UNSATISFIABLE\n");
            }
            return 0;
        }

        assert( output.return_units );
        bool ret;
        vec<bool> model_seen( 2 * S.nVars() + 2, false );
        if ( output.models.empty() ) {
            ret = S.solve();
            if ( ret ) {
                if ( output.return_model ) Add_Marked_Model( model_seen, output.models );
                else Mark_Model( model_seen );
            }
        }
        else {
            ret = true;
            Mark_Models( model_seen, output.models );
        }
        if ( ret ) {
            for ( size_t i = 0; i < S.nVars(); i++ ) {
                if ( ( S.value(i) != l_Undef ) + model_seen[i + i] + model_seen[i + i + 1] > 1 ) continue;
                Lit lit = mkLit( i, model_seen[i + i + 1] );
                if ( S.solve( ~lit ) ) {
					if ( output.return_model ) Add_Marked_Model( model_seen, output.models );
					else Mark_Model( model_seen );
                }
            }
            S.simplify();
            S.Units( output.units );
            if ( output.return_learnt_max_len >= 2 ) {
                output.short_learnts.resize( output.return_learnt_max_len - 1 );
                S.Short_Learnt_Clauses( output.short_learnts );
            }
        }
        if (solver->verbosity > 0) {
            printStats(*solver);
            printf("\n");
            printf(ret ? "SATISFIABLE\n" : "UNSATISFIABLE\n");
        }
        return ret;
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}

extern bool Ext_Block_Literals( vector<vector<int>>& focused, vector<vector<int>>& others, Extra_Output & output )
{
    try {
        int paramc = 1;
        char* params[1];
        params[0] = "minisat";
        setUsageHelp("USAGE: %s [options] [input-file] \n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        if (false) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);

        parseOptions(paramc, params, true);//{{{printf("here.3\n");fflush(stdin);}}}

        CustomizedSolver S;

        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        S.Add_Clauses( focused );
        S.Add_Clauses( others );


        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        if (!solver->simplify()){
            focused.clear();
            others.clear();
            return true;
        }
        bool found = false;
		for ( vector<int> & clause: focused ) {
			if ( clause.size() <= 2 ) continue;
			vec<Lit> lits;
			for ( int lit: clause) {
				lits.push( ~LitExt2Intern( lit ) );
			}
			for (int i = 0; i < clause.size(); i++) {
				lits[i] = ~lits[i];
				if ( !S.solve( lits ) ) {
					found = true;
					clause[i] = clause.back();
					clause.pop_back();
					lits[i] = lits.last();
					lits.pop();
					if ( clause.size() == 2 ) break;
					else i--;
				}
				else {
					if ( output.return_model ) Add_Model( output.models );
					lits[i] = ~lits[i];
				}
			}
		}
		if ( output.return_learnt_max_len >= 2 ) {
			output.short_learnts.resize( output.return_learnt_max_len - 1 );
			S.Short_Learnt_Clauses( output.short_learnts );
        }
        return found;
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}

///================================================= SimpSolver ======================================

extern int8_t Ext_SimpSolve( vector<vector<int>> & clauses, Extra_Output & output )
{
    try {
        int paramc = 1;
        char* params[1];
        params[0] = "minisat";
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
//        setX86FPUPrecision();
#if defined(__linux__) && defined(_FPU_EXTENDED) && defined(_FPU_DOUBLE) && defined(_FPU_GETCW)
    // Only correct FPU precision on Linux architectures that needs and supports it:
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    if ( false ) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        BoolOption   solve  ("MAIN", "solve",  "Completely turn on/off solving after preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);

        parseOptions(paramc, params, true);

        CustomizedSimpSolver  S;
        double      initial_time = cpuTime();

        if (!pre) S.eliminate(true);

        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        sigTerm(SIGINT_exit);

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);

        if (paramc == 0)
            printf("Reading from standard input... Use '--help' for help.\n");
        else if (paramc == 2) {
            gzFile in = (paramc == 1) ? gzdopen(0, "rb") : gzopen(params[1], "rb");
            if (in == NULL)
                printf("ERROR! Could not open file: %s\n", paramc == 1 ? "<stdin>" : params[1]), exit(1);
            parse_DIMACS(in, S, (bool)strictp);
            gzclose(in);
            FILE* res = (paramc >= 3) ? fopen(params[2], "wb") : NULL;
        }
        S.Add_Clauses( clauses );
        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n");
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses());
        }

        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        sigTerm(SIGINT_interrupt);

        S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
            printf("|                                                                             |\n"); }

        if (!S.okay()){
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by simplification\n");
                S.printStats();
                printf("\n"); }
            return 0;
        }

        lbool ret = l_Undef;

        if (solve){
            vec<Lit> assumps;
            ret = S.solveLimited( assumps );
        }else if (S.verbosity > 0)
            printf("===============================================================================\n");

        if (S.verbosity > 0){
            S.printStats();
            printf("\n");
            printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        }
        if (ret == l_True) {
            output.Gather_Output( S );
            return 1;
        }
        else if (ret == l_False) return 0;
        else return -1;

#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}

extern bool Ext_SimpBackbone( vector<vector<int>>& clauses, Extra_Output & output ) // it has some unknown bug
{
    try {
        int paramc = 1;
        char* params[1];
        params[0] = "minisat";
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
//        setX86FPUPrecision();
#if defined(__linux__) && defined(_FPU_EXTENDED) && defined(_FPU_DOUBLE) && defined(_FPU_GETCW)
    // Only correct FPU precision on Linux architectures that needs and supports it:
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    if ( false ) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        BoolOption   solve  ("MAIN", "solve",  "Completely turn on/off solving after preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);

        parseOptions(paramc, params, true);

        CustomizedSimpSolver  S;
        double      initial_time = cpuTime();

        if (!pre) S.eliminate(true);

        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        sigTerm(SIGINT_exit);

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);

        if (paramc == 0)
            printf("Reading from standard input... Use '--help' for help.\n");
        else if (paramc == 2) {
            gzFile in = (paramc == 1) ? gzdopen(0, "rb") : gzopen(params[1], "rb");
            if (in == NULL)
                printf("ERROR! Could not open file: %s\n", paramc == 1 ? "<stdin>" : params[1]), exit(1);
            parse_DIMACS(in, S, (bool)strictp);
            gzclose(in);
            FILE* res = (paramc >= 3) ? fopen(params[2], "wb") : NULL;
        }
        S.Add_Clauses( clauses );
        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n");
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses());
        }

        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        sigTerm(SIGINT_interrupt);

        S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
            printf("|                                                                             |\n"); }

        if (!S.okay()){
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by simplification\n");
                S.printStats();
                printf("\n"); }
            return 0;
        }

        assert( output.return_model && output.return_units && solve );
        bool ret;
        vec<bool> model_seen( 2 * S.nVars() + 2, false );
        if ( output.models.empty() ) {
            ret = S.solve();
            Add_Marked_Model( model_seen, output.models );
        }
        else {
            ret = true;
            Mark_Models( model_seen, output.models );
        }
        output.units.clear();
        if ( ret == true ) {
            for ( size_t i = 0; i < S.nVars(); i++ ) {
                if ( S.value(i) != l_Undef ) {
                    output.units.push_back( LitIntern2Ext( mkLit( i, S.value(i) == l_False ) ) );
                    continue;
                }
                if ( model_seen[i + i] + model_seen[i + i + 1] == 2 ) continue;
                Lit lit = mkLit( i, model_seen[i + i + 1] );
                if ( !S.solve( ~lit ) ) {
                    if ( !S.isEliminated(i) ) S.addClause( lit );
                    output.units.push_back( LitIntern2Ext( lit ) );
                }
                else Add_Marked_Model( model_seen, output.models );
            }
            if ( output.return_learnt_max_len >= 2 ) {
                output.short_learnts.resize( output.return_learnt_max_len - 1 );
                S.Short_Learnt_Clauses( output.short_learnts );
            }
        }else if (S.verbosity > 0)
            printf("===============================================================================\n");

        if (S.verbosity > 0){
            S.printStats();
            printf("\n");
            printf(ret ? "SATISFIABLE\n" : "UNSATISFIABLE\n");
        }
        return ret;
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}


}
