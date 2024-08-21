#ifndef _Unified_Component_h_
#define _Unified_Component_h_

#include "Component.h"


namespace KCBox {


class Unified_Component: public Component
{
protected:
	vector<unsigned> _binary_clauses;
public:
	void Add_Binary_Clause( unsigned lit0, unsigned lit1 ) { _binary_clauses.push_back( lit0 ); _binary_clauses.push_back( lit1 ); }
	unsigned Binary_Clauses_First( unsigned i ) { return _binary_clauses[i + i]; }
	unsigned Binary_Clauses_Second( unsigned i ) { return _binary_clauses[i + i + 1]; }
	unsigned Binary_ClauseIDs_Size() { return _binary_clauses.size() / 2; }
	void Clear() { _varIDs.clear(); _binary_clauses.clear(); _clauseIDs.clear(); }
	void Verify_Orderness()
	{
	    assert( Vars_Size() > 1 );
	    assert( Binary_ClauseIDs_Size() + ClauseIDs_Size() > 0 );
	    for ( unsigned i = 1; i < _varIDs.size(); i++ ) {
            assert( _varIDs[i-1] < _varIDs[i] );
	    }
	    for ( unsigned i = 2; i < _binary_clauses.size(); i += 2 ) {
	        unsigned lit0 = _binary_clauses[i - 2];
	        unsigned lit1 = _binary_clauses[i - 1];
	        unsigned lit2 = _binary_clauses[i];
	        unsigned lit3 = _binary_clauses[i + 1];
            assert( lit0 < lit2 || ( lit0 == lit2 && lit1 < lit3 ) );
	    }
	    for ( unsigned i = 1; i < _clauseIDs.size(); i++ ) {
            assert( _clauseIDs[i-1] < _clauseIDs[i] );
	    }
	}
	void Display( ostream & out )
	{
		assert( _varIDs.size() >= 1 );
		unsigned i;
		out << "vars: ";
		for ( i = 0; i < _varIDs.size(); i++ ) out << _varIDs[i] << " ";
		out << endl;
		out << "binary clauses: ";
		for ( i = 0; i < _binary_clauses.size(); i += 2 ) {
			out << "(" << ExtLit( Literal( _binary_clauses[i] ) ) << ", " << ExtLit( Literal( _binary_clauses[i+1] ) ) << ") ";
		}
		out << endl;
		out << "clauses IDs: ";
		for ( i = 0; i < _clauseIDs.size(); i++ ) out << _clauseIDs[i] << " ";
		out << endl;
	}
};


}


#endif
