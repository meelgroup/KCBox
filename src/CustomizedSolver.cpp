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

#include "CustomizedSolver.h"


namespace Minisat {

using std::vector;


void CustomizedSolver::Add_Clauses( vector<vector<int>>& clauses )
{
    size_t i, j;
    int lit, var;
    vec<Lit> lits;
    for (i = 0; i < clauses.size(); i++) {
        vector<int> & cl = clauses[i];
        for (j = 0; j < cl.size(); j++){
            lit = cl[j];
            assert(lit != 0);
            var = abs(lit)-1;
            while (var >= nVars()) newVar();
            lits.push( (lit > 0) ? mkLit(var) : ~mkLit(var) );
        }
        addClause_(lits);
        lits.clear();
    }
}

void CustomizedSolver::Model( vector<vector<int8_t>> & extmodels )
{
    vector<int8_t> emodel( nVars() + 1 );
    for ( size_t i = 0; i < nVars(); i++ ) {
        emodel[i+1] = -toInt( model[i] ) + 1;
        if ( model[i] == l_Undef ) assert( emodel[i+1] == -1 );
        else if ( model[i] == l_False ) assert( emodel[i+1] == 0) ;
        else assert( emodel[i+1] == 1 );
    }
    extmodels.push_back( emodel );
}

void CustomizedSolver::Units( vector<int> & units )
{
    units.clear();
    for ( int i = 0; i < nVars(); i++ ) {
        if ( value(i) != l_Undef ) {
            units.push_back( LitIntern2Ext( mkLit( i, value(i) == l_False ) ) );
        }
    }
}

void CustomizedSolver::Short_Learnt_Clauses( vector<vector<int>> & short_learnts )
{
    for ( size_t i = 0; i < short_learnts.size(); i++ ) {
        short_learnts[i].clear();
    }
    unsigned bound = short_learnts.size() + 1;
    for ( size_t i = 0; i < learnts.size(); i++ ) {
        Clause & clause = ca[learnts[i]];
        if ( clause.size() <= bound ) {
            unsigned pos = clause.size() - 2;
            for ( size_t j = 0; j < clause.size(); j++ ) {
                short_learnts[pos].push_back( LitIntern2Ext( clause[j] ) );
            }
        }
    }
}

void CustomizedSolver::Display_Clauses( ostream & out )
{
    for ( size_t i = 0; i < clauses.size(); i++ ) {
        Clause & clause = ca[clauses[i]];
        for ( size_t j = 0; j < clause.size(); j++ ) {
            out << LitIntern2Ext( clause[j] ) << " ";
        }
        out << endl;
    }
}

void CustomizedSimpSolver::Add_Clauses( vector<vector<int>> & clauses )
{
    size_t i, j;
    int lit, var;
    vec<Lit> lits;
    for (i = 0; i < clauses.size(); i++) {
        vector<int> & cl = clauses[i];
        for (j = 0; j < cl.size(); j++){
            lit = cl[j];
            assert(lit != 0);
            var = abs(lit)-1;
            while (var >= nVars()) newVar();
            lits.push( (lit > 0) ? mkLit(var) : ~mkLit(var) );
        }
        addClause_(lits);  /// NOTE: use Solver::addClause_ might return a wrong model, do not know why
        lits.clear();
    }
}

void CustomizedSimpSolver::Model( vector<vector<int8_t>> & extmodels )
{
    vector<int8_t> emodel( nVars() + 1 );
    for ( size_t i = 0; i < nVars(); i++ ) {
        emodel[i+1] = -toInt( model[i] ) + 1;
        if ( model[i] == l_Undef ) assert( emodel[i+1] == -1 );
        else if ( model[i] == l_False ) assert( emodel[i+1] == 0) ;
        else assert( emodel[i+1] == 1 );
    }
    extmodels.push_back( emodel );
}

void CustomizedSimpSolver::Units( vector<int> & units )
{
    units.clear();
    for ( int i = 0; i < nVars(); i++ ) {
        if ( value(i) != l_Undef ) {
            units.push_back( LitIntern2Ext( mkLit( i, value(i) == l_False ) ) );
        }
    }
}

void CustomizedSimpSolver::Short_Learnt_Clauses( vector<vector<int>> & short_learnts )
{
    for ( size_t i = 0; i < short_learnts.size(); i++ ) {
        short_learnts[i].clear();
    }
    unsigned bound = short_learnts.size() + 1;
    for ( size_t i = 0; i < learnts.size(); i++ ) {
        Clause & clause = ca[learnts[i]];
        if ( clause.size() <= bound ) {
            unsigned pos = clause.size() - 2;
            for ( size_t j = 0; j < clause.size(); j++ ) {
                short_learnts[pos].push_back( LitIntern2Ext( clause[j] ) );
            }
        }
    }
}

void CustomizedSimpSolver::Display_Clauses( ostream & out )
{
    for ( size_t i = 0; i < clauses.size(); i++ ) {
        Clause & clause = ca[clauses[i]];
        for ( size_t j = 0; j < clause.size(); j++ ) {
            out << LitIntern2Ext( clause[j] ) << " ";
        }
        out << endl;
    }
}


}
