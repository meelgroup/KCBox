#ifndef _Lit_Equivalency_h
#define _Lit_Equivalency_h

#include "../Template_Library/Graph_Structures.h"


namespace KCBox {


class Lit_Equivalency  /// based on union-find set, flat means that the height is one
{
protected:
	unsigned _max_var;
	Chain _var_order;
	Literal * _lit_equivalences;
	bool * _var_seen;
	BigVector<Variable> _substituted_vars;  // the variables in lit_equivalences with lit_equivalences[lit] != lit
	BigVector<Literal> _lit_vector;  // the literals in lit_equivalences with lit_equivalences[lit] != lit
	vector<Literal> * _equivalent_lit_sets;  // it is sorted and each cluster is also sorted, and used for optimize Replace_Equivalent_Lit()
	unsigned * _lit_appear_in_sets;  // it is sorted and each cluster is also sorted, and used for optimize Replace_Equivalent_Lit()
public:
	Lit_Equivalency();
	Lit_Equivalency( Variable max_var );
	Lit_Equivalency( Chain & var_order );
	~Lit_Equivalency();
	void Reorder( const Chain & var_order );
	void Reset();
	bool Empty() const { return _substituted_vars.Empty(); }
	void Add_Equivalence( Literal lit, Literal lit2 ) { Union( lit, lit2 ); }
	void Add_Equivalence_Flat( Literal lit, Literal lit2 );
	void Add_Equivalences( Literal * lit_equivalences );
	void Add_Equivalences( Literal * pairs, unsigned size );
	unsigned Output_Equivalences( Literal * pairs );
	void Output_Equivalences( vector<Literal> & pairs );
	Literal Rename_Lit( Literal lit ) { return Find( lit ); }
	Literal Rename_Lit_Flat( Literal lit ) { return _lit_equivalences[lit]; }
	Variable Rename_Var( Variable var ) { Literal lit = Literal( var, false ); return Find( lit ).Var(); }
	bool Lit_Renamable( Literal lit ) { return lit != _lit_equivalences[lit]; }
	bool Var_Renamable( Variable var ) { return Literal( var, false ) != _lit_equivalences[Literal( var, false )]; }
	bool Equ_Existed( Literal lit ) { return _var_seen[lit.Var()]; }
	bool Contain_Lit_Equivalence( Literal lit, Literal lit2 ) { return Find( lit ) == Find( lit2 ); }
	void Intersection( Lit_Equivalency & first, Lit_Equivalency & second );
	void Intersection_Flat( Lit_Equivalency & first, Lit_Equivalency & second );
	void Intersection_Flat( vector<Literal> & equ_class, Lit_Equivalency & equivalency );
	unsigned Cluster_Equivalent_Lits();
	void Display( ostream & out );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
	Literal Find( Literal lit );
	void Union( Literal lit, Literal lit2 );
	void Uniquify();
protected:
	bool Lit_LT( Literal lit, Literal lit2 ) { return _var_order.Less_Than( lit.Var(), lit2.Var() ); }
public:
    static void Debug()
    {
        Chain chain;
        chain.Append( 1 );
        chain.Append( 3 );
        chain.Append( 2 );
        chain.Append( 4 );
        Lit_Equivalency lit_equ( chain ), lit_equ1( chain ), lit_equ2( chain );
        lit_equ1.Add_Equivalence( Literal( 2 ), Literal( 4 ) );
        lit_equ1.Add_Equivalence( Literal( 2 ), Literal( 7 ) );
        lit_equ2.Add_Equivalence( Literal( 6 ), Literal( 4 ) );
        lit_equ.Intersection( lit_equ1, lit_equ2 );
        lit_equ.Display( cerr );
    }
};


}


#endif // _Lit_Equivalency_h
