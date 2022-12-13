#ifndef _minisatInterface_h_
#define _minisatInterface_h_

#include <vector>


namespace Minisat {

using namespace std;

struct Extra_Output
{
    bool return_model;
    vector<vector<int8_t>> models;
    bool return_units;
    vector<int> units;
    unsigned return_learnt_max_len;
    vector<vector<int>> short_learnts;  // binary learnts are stored at short_learnts[0], ternary learnts are stored at short_learnts[1], and quaternary learnts are stored at short_learnts[0]
    Extra_Output()
    {
        return_model = true;
        return_units = false;
        return_learnt_max_len = 0;
    }
    template<class CSolver> void Gather_Output( CSolver & solver )
    {
        assert( solver.okay() );
        if ( return_model ) {
            solver.Model( models );
        }
        if ( return_units ) {
            solver.Units( units );
        }
        if ( return_learnt_max_len >= 2 ) {
            short_learnts.resize( return_learnt_max_len - 1 );
            solver.Short_Learnt_Clauses( short_learnts );
        }
    }
};

extern int8_t Ext_Solve( vector<vector<int>>& clauses, Extra_Output & output );

extern bool Ext_Backbone( vector<vector<int>>& clauses, Extra_Output & output );

extern int8_t Ext_SimpSolve( vector<vector<int>>& clauses, Extra_Output & output );

extern bool Ext_Block_Literals( vector<vector<int>>& focused, vector<vector<int>>& others, Extra_Output & output );

}


#endif // _minisatInterface_h_

