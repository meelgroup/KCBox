#ifndef _CustomizedSolver_h_
#define _CustomizedSolver_h_

#include <vector>
#include <iostream>
#include "minisat/simp/SimpSolver.h"

namespace Minisat {

using namespace std;

/** NOTE:
* int is the literal in DIMACS, Lit is the literal in minisat
* -1 in DIMACS corresponds to 1 in minisat, and 1 in DIMACS corresponds to 0 in minisat
* -2 in DIMACS corresponds to 3 in minisat, and 2 in DIMACS corresponds to 2 in minisat
**/

extern inline int LitIntern2Ext(Lit lit)
{
    return sign(lit) ? -var(lit) - 1 : var(lit) + 1;
}

extern inline Lit LitExt2Intern( int lit)
{
    int var = abs(lit)-1;
    return mkLit( var, lit < 0 );
}

extern inline Lit LitExt2Intern( Solver * solver, int lit)
{
    int var = abs(lit)-1;
    while ( var >= solver->nVars() ) solver->newVar();
    return mkLit( var, lit < 0 );
}

class CustomizedSolver: public Solver
{
public:
    CustomizedSolver() {}
    ~CustomizedSolver() {}
    void Add_Clauses( vector<vector<int>> & clauses );
    void Model( vector<vector<int8_t>> & extmodels );  // -1 is undef, 0 is false, 1 is true， and the variable is in DIMACS
    void Units( vector<int> & units );
    void Short_Learnt_Clauses( vector<vector<int>> & short_learnts );
    void Display_Clauses( ostream & out );
};

class CustomizedSimpSolver: public SimpSolver
{
public:
    CustomizedSimpSolver() {}
    ~CustomizedSimpSolver() {}
    void Add_Clauses( vector<vector<int>> & clauses );
    void Model( vector<vector<int8_t>> & extmodels );  // -1 is undef, 0 is false, and 1 is true
    void Units( vector<int> & units );
    void Short_Learnt_Clauses( vector<vector<int>> & short_learnts );
    void Display_Clauses( ostream & out );
};


}


#endif // _CustomizedSolver_h_

