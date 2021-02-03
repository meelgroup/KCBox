#include "Lit_Equivalency.h"


namespace KCBox {


Lit_Equivalency::Lit_Equivalency(): _max_var( Variable::undef )
{
}

Lit_Equivalency::Lit_Equivalency( Chain & var_order ): _max_var( var_order.Max() ), _var_order( var_order )
{
    if ( NumVars( Variable( var_order.Max() ) ) != var_order.Size() ) {
        cerr << "ERROR[Lit_Equivalency]: wrong variable ordering!" << endl;
        exit( 1 );
    }
    Allocate_and_Init_Auxiliary_Memory();
}

void Lit_Equivalency::Allocate_and_Init_Auxiliary_Memory()
{
    if ( _max_var == Variable::undef ) return;
	_lit_equivalences = new Literal [2 * _max_var + 2];
	_var_seen = new bool [_max_var + 1];
    _substituted_vars.Enlarge( _max_var + 1 );
    _lit_vector.Enlarge( _max_var + 1 );
    _equivalent_lit_sets = new vector<Literal> [2 * _max_var + 2];
    _lit_appear_in_sets = new unsigned [2 * _max_var + 2];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
        _lit_equivalences[i + i] = Literal( i, false );
        _lit_equivalences[i + i + 1] = Literal( i, true );
        _var_seen[i] = false;
	}
}

Lit_Equivalency::~Lit_Equivalency()
{
    Free_Auxiliary_Memory();
}

void Lit_Equivalency::Free_Auxiliary_Memory()
{
    if ( _max_var == Variable::undef ) return;
	delete [] _lit_equivalences;
	delete [] _var_seen;
	delete [] _equivalent_lit_sets;
	delete [] _lit_appear_in_sets;
}

void Lit_Equivalency::Reorder( Chain & var_order )
{
    if ( var_order.Max() != _max_var ) {
        Free_Auxiliary_Memory();
        _max_var = var_order.Max();
        _var_order = var_order;
        Allocate_and_Init_Auxiliary_Memory();
    }
    else _var_order = var_order;
}

void Lit_Equivalency::Reset()
{
	for ( unsigned i = 0; i < _substituted_vars.Size(); i++ ) {
        Variable var = _substituted_vars[i];
        Literal lit = Literal( var, false );
        _lit_equivalences[lit] = lit;
        _lit_equivalences[~lit] = ~lit;
        _var_seen[var] = false;
	}
	_substituted_vars.Clear();
}

void Lit_Equivalency::Add_Equivalences( Literal * lit_equivalences  )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
        if ( lit_equivalences[Literal( i, false )] != Literal( i, false ) ) continue;
        Union( Literal( i, false ), lit_equivalences[Literal( i, false )] );
    }
}

void Lit_Equivalency::Add_Equivalences( Literal * pairs, unsigned size )
{
    for ( unsigned i = 0; i < size; i += 2 ) {
        Union( pairs[i], pairs[i+1] );
    }
}

unsigned Lit_Equivalency::Output_Equivalences( Literal * pairs )
{
    Uniquify();
    unsigned size = 0;
	for ( unsigned i = 0; i < _substituted_vars.Size(); i++ ) {
        Literal lit = Literal( _substituted_vars[i], false );
        if ( lit == _lit_equivalences[lit] ) continue;
        Literal lit_neg = Literal( _substituted_vars[i], true );
        if ( _lit_equivalences[lit].Sign() ) {
            pairs[size + size] = _lit_equivalences[lit];
            pairs[size + size + 1] = lit;
        }
        else {
            pairs[size + size] = _lit_equivalences[lit_neg];
            pairs[size + size + 1] = lit_neg;
        }
        size++;
	}
	return size;
}

Literal Lit_Equivalency::Find( Literal lit )
{
    Literal root = _lit_equivalences[lit];
    while ( _lit_equivalences[root] != root ) {
        _lit_vector.Push_Back( root );
        root = _lit_equivalences[root];
    }
    _lit_equivalences[lit] = root;
    _lit_equivalences[~lit] = ~root;
    for ( unsigned j = 0; j < _lit_vector.Size(); j++ ) {
        _lit_equivalences[_lit_vector[j]] = root;
        _lit_equivalences[~_lit_vector[j]] = ~root;
    }
    _lit_vector.Clear();
    return root;
}

void Lit_Equivalency::Union( Literal lit, Literal lit2 )
{
	assert( lit.Var() != lit2.Var() );
    Literal tmp, root = Find( lit ), root2 = Find( lit2 );
    if ( Lit_LT( root2, root ) ) {
        tmp = lit;
        lit = lit2;
        lit2 = tmp;
        tmp = root;
        root = root2;
        root2 = tmp;
    }
    _lit_equivalences[root2] = root;
    _lit_equivalences[lit2] = root;
    _lit_equivalences[~root2] = ~root;
    _lit_equivalences[~lit2] = ~root;
    if ( !_var_seen[lit.Var()] ) {
        _substituted_vars.Push_Back( lit.Var() );
        _var_seen[lit.Var()] = true;
    }
    if ( !_var_seen[lit2.Var()] ) {
        _substituted_vars.Push_Back( lit2.Var() );
        _var_seen[lit2.Var()] = true;
    }
}

void Lit_Equivalency::Uniquify()
{
    for ( unsigned i = 0; i < _substituted_vars.Size(); i++ ) {
		Literal lit( _substituted_vars[i], false );
        Find( lit );
    }
}

void Lit_Equivalency::Intersection( Lit_Equivalency & first, Lit_Equivalency & second )
{
    if ( first._substituted_vars.Size() < second._substituted_vars.Size() ) {
        unsigned cluster_size = first.Cluster_Equivalent_Lits();
        for ( unsigned i = 0; i < cluster_size; i += 2 ) {
            vector<Literal> & cluster = first._equivalent_lit_sets[i];
            for ( unsigned j = 0; j < cluster.size(); j++ ) {
                Literal lit = cluster[j];
                for ( unsigned k = j + 1; k < cluster.size(); k++ ) {
                    Literal lit2 = cluster[k];
                    if ( second.Contain_Lit_Equivalence( lit, lit2 ) ) {
                        Add_Equivalence( lit, lit2 );
                    }
                }
            }
        }
    }
    else {
        unsigned cluster_size = second.Cluster_Equivalent_Lits();
        for ( unsigned i = 0; i < cluster_size; i += 2 ) {
            vector<Literal> & cluster = second._equivalent_lit_sets[i];
            for ( unsigned j = 0; j < cluster.size(); j++ ) {
                Literal lit = cluster[j];
                for ( unsigned k = j + 1; k < cluster.size(); k++ ) {
                    Literal lit2 = cluster[k];
                    if ( first.Contain_Lit_Equivalence( lit, lit2 ) ) {
                        Add_Equivalence( lit, lit2 );
                    }
                }
            }
        }
    }
}

unsigned Lit_Equivalency::Cluster_Equivalent_Lits()
{
	unsigned cluster_size = 0;
	vector<Literal> singleton( 1 );
	for ( unsigned i = 0; i < _substituted_vars.Size(); i++ ) {
        Variable var = _substituted_vars[i];
		if ( Find( Literal( var, false ) ) == Literal( var, false ) ) {  // Uniquify, and create new entries
			singleton[0] = Literal( var, false );
			_equivalent_lit_sets[cluster_size] = singleton;
			_lit_appear_in_sets[var + var] = cluster_size;
			cluster_size++;
			singleton[0] = Literal( var, true );
			_equivalent_lit_sets[cluster_size] = singleton;
			_lit_appear_in_sets[var + var + 1] = cluster_size;
			cluster_size++;
		}
	}
	for ( unsigned i = 0; i < _substituted_vars.Size(); i++ ) {
        Variable var = _substituted_vars[i];
		if ( _lit_equivalences[Literal( var, false )] != Literal( var, false ) ) {
            unsigned loc = _lit_appear_in_sets[_lit_equivalences[Literal( var, false )]];  // find the old entry
			_equivalent_lit_sets[loc].push_back( Literal( var, false ) );
			_equivalent_lit_sets[loc ^ 0x01].push_back( Literal( var, true ) );
		}
	}
	return cluster_size;
}

void Lit_Equivalency::Display( ostream & out )
{
	unsigned i, j;
    Uniquify();
	for ( i = 0; i < _var_order.Size(); i++ ) {
	    Literal root( Variable( _var_order[i] ), false );
        if ( _lit_equivalences[root] != root ) continue;
		for ( j = i + 1; j < _var_order.Size(); j++ ) {
		    Literal lit( Variable( _var_order[j] ), false );
			if ( _lit_equivalences[lit] == root ) out << ExtLit( lit ) << ' ';
		    lit = Literal( Variable( _var_order[j] ), true );
			if ( _lit_equivalences[lit] == root ) out << ExtLit( lit ) << ' ';
		}
		out << "|-> " << ExtLit( root );
		out << endl;
	    root = Literal( Variable( _var_order[i] ), true );
        if ( _lit_equivalences[root] != root ) continue;
		for ( j = i + 1; j < _var_order.Size(); j++ ) {
		    Literal lit( Variable( _var_order[j] ), false );
			if ( _lit_equivalences[lit] == root ) out << ExtLit( lit ) << ' ';
		    lit = Literal( Variable( _var_order[j] ), true );
			if ( _lit_equivalences[lit] == root ) out << ExtLit( lit ) << ' ';
		}
		out << "|-> " << ExtLit( root );
		out << endl;
	}
}


}

