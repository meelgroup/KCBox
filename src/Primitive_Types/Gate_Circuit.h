#ifndef _Gate_Circuit_h
#define _Gate_Circuit_h

#include "../Template_Library/Graph_Structures.h"
#include "CNF_Formula.h"


namespace KCBox {


class AND_Gate  /// based on union-find set
{
protected:
	vector<Literal> _inputs;
	Literal _output;
public:
	AND_Gate() { _inputs.reserve( 2 ); }
	AND_Gate( Big_Clause & inputs, Literal output )
	{
		_inputs.resize( inputs.Size() );
		for ( unsigned i = 0; i < inputs.Size(); i++ ) {
			_inputs[i] = inputs[i];
		}
		_output = output;
	}
	Literal Output() { return _output; }
	const vector<Literal> Inputs() { return _inputs; }
	Literal Inputs( unsigned i ) { return _inputs[i]; }
	unsigned Inputs_Size() { return _inputs.size(); }
	bool Is_Lit_Equivalence() { return _inputs.size() == 1; }
};

extern inline ostream & operator << ( ostream & out, AND_Gate & gate )
{
	out << "AND( " << ExtLit( gate.Inputs( 0 ) );
	for ( unsigned i = 1; i < gate.Inputs_Size(); i++ ) {
		out << ", " << ExtLit( gate.Inputs( i ) );
	}
    out << " ) <-> " << ExtLit( gate.Output() );
    return out;
}


}


#endif // _Lit_Equivalency_h
