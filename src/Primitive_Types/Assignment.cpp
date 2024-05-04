#include "Assignment.h"


namespace KCBox {


const lbool lbool::unknown;


extern void Random_Assignments( vector<vector<Literal>> & assignments, \
							Random_Generator & rand_gen, Variable max_var, unsigned min_len, unsigned max_len )
{
	assert( 0 < min_len && min_len <= max_len && max_len <= NumVars( max_var ) );
	vector<bool> lit_seen( 2 * max_var + 2, false );
	for ( vector<Literal> & assignment: assignments ) {
		unsigned len = rand_gen.Generate_Int( min_len, max_len );
		assignment.resize( len );
		for ( unsigned i = 0; i < len; ) {
			Literal lit( rand_gen.Generate_Int( Literal::start, 2 * max_var + 1 ) );
			if ( !lit_seen[lit] && !lit_seen[~lit] ) {
				lit_seen[lit] = true;
				assignment[i++] = lit;
			}
		}
		for ( unsigned i = 0; i < len; i++ ) {
			lit_seen[assignment[i]] = false;
		}
	}
}


}
