#ifndef _Stack_Frame_h_
#define _Stack_Frame_h_

#include "Assignment.h"
#include "../Component_Types/Component.h"



namespace KCBox {


class Stack_Frame
{
protected:
	bool _existed;
	vector<Literal> _unary_clauses;
	vector<Literal> _binary_clauses;
	vector<Clause> _long_clauses;
	unsigned _old_num_long_clauses;
	vector<Literal> _binary_learnts;
	vector<Literal> _lit_equivalences;
	Component _component;
	unsigned _pre_fixed_num_vars;
	vector<Model *> _models;
	vector<Literal> _cached_binary_clauses;  // accelerate caching
public:
	Stack_Frame(): _existed( false ), _old_num_long_clauses( 0 ), _pre_fixed_num_vars( 0 ) {}
	bool Existed() { return _existed; }
	bool Solved() { return _binary_clauses.empty() && _long_clauses.empty(); }
	const vector<Literal> & Unary_Clauses() { return _unary_clauses; }
	const vector<Literal> & Binary_Clauses() { return _binary_clauses; }
	const vector<Clause> & Long_Clauses() { return _long_clauses; }
	const vector<Literal> & Binary_Learnts() { return _binary_learnts; }
	const vector<Literal> & Lit_Equivalences() { return _lit_equivalences; }
	const vector<unsigned> & Component_VarIDs() { return _component.VarIDs(); }
	void Set_Existed( bool existed ) { _existed = existed; }
	unsigned Pre_Fixed_Num_Vars() { return _pre_fixed_num_vars; }
	const vector<Model *> & Models() { return _models; }
	void Add_Unary_Clause( Literal lit ) { _unary_clauses.push_back( lit ); }
	void Add_Binary_Clause( Literal lit0, Literal lit1 ) { _binary_clauses.push_back( lit0 ); _binary_clauses.push_back( lit1 ); }
	Literal Binary_Clauses_First( unsigned i ) { return _binary_clauses[i + i]; }
	Literal Binary_Clauses_Second( unsigned i ) { return _binary_clauses[i + i + 1]; }
	unsigned Binary_Clauses_Size() { return _binary_clauses.size() / 2; }
	void Add_Binary_Learnt( Literal lit0, Literal lit1 ) { _binary_learnts.push_back( lit0 ); _binary_learnts.push_back( lit1 ); }
	Literal Binary_Learnts_First( unsigned i ) { return _binary_learnts[i + i]; }
	Literal Binary_Learnts_Second( unsigned i ) { return _binary_learnts[i + i + 1]; }
	unsigned Binary_Learnts_Size() { return _binary_learnts.size() / 2; }
	Clause Long_Clauses( unsigned i ) { return _long_clauses[i]; }
	void Add_Long_Clause( const Clause & clause ) { _long_clauses.push_back( clause ); }
	void Set_Old_Num_Long_Clauses( unsigned num ) { _old_num_long_clauses = num; }
	unsigned Old_Num_Long_Clauses() { return _old_num_long_clauses; }
	void Add_Lit_Equivalence( Literal lit0, Literal lit1 ) { _lit_equivalences.push_back( lit0 ); _lit_equivalences.push_back( lit1 ); }
	unsigned Lit_Equivalences_Size() { return _lit_equivalences.size() / 2; }
	unsigned Get_Caching_Loc() { return _component.caching_loc; }
	void Set_Caching_Loc( unsigned new_loc ) { _component.caching_loc = new_loc; }
	void Set_Pre_Fixed_Num_Vars( unsigned num_vars ) { _pre_fixed_num_vars = num_vars; }
	void Add_Cached_Binary_Clause( Literal lit0, Literal lit1 ) { _cached_binary_clauses.push_back( lit0 ); _cached_binary_clauses.push_back( lit1 ); }
	Literal Cached_Binary_Clauses_First( unsigned i ) { return _cached_binary_clauses[i + i]; }
	Literal Cached_Binary_Clauses_Second( unsigned i ) { return _cached_binary_clauses[i + i + 1]; }
	unsigned Cached_Binary_Clauses_Size() { return _cached_binary_clauses.size() / 2; }
	void Swap_Unary_Clauses( vector<Literal> & unary_clauses ) { _unary_clauses.swap( unary_clauses ); }
	void Swap_Long_Clauses( vector<Clause> & long_clauses, unsigned & old_num_long_clauses )
	{
		_long_clauses.swap( long_clauses );
		swap( _old_num_long_clauses, old_num_long_clauses );
	}
	void Swap_Lit_Equivalences( Stack_Frame & frame ) { _lit_equivalences.swap( frame._lit_equivalences ); }
	void Swap_Component( Component & comp ) { _component.Swap( comp ); }
	void Swap_Models( vector<Model *> & models ) { _models.swap( models ); }
	void Swap_Models( Stack_Frame & frame ) { _models.swap( frame._models ); }
	void Clear()
	{
		_unary_clauses.clear();
		_binary_clauses.clear();
		_long_clauses.clear();
		_binary_learnts.clear();
		_old_num_long_clauses = 0;
		_lit_equivalences.clear();
		_cached_binary_clauses.clear();
	}
	void Clear_Binary_Clauses() { _binary_clauses.clear(); }
	void Clear_Binary_Learnts() { _binary_learnts.clear(); }
	void Clear_Long_Clauses()
	{
		_long_clauses.clear();
		_old_num_long_clauses = 0;
	}
	void Clear_Lit_Equivalences() { _lit_equivalences.clear(); }
	void Clear_Cached_Binary_Clauses() { _cached_binary_clauses.clear(); }
	void Free_Long_Clauses() { for ( Clause & clause: _long_clauses ) clause.Free(); }
	size_t Memory()
	{
		return _unary_clauses.capacity() * sizeof(Literal) + \
		_binary_clauses.capacity() * sizeof(Literal) + \
        _long_clauses.capacity() * sizeof(Clause) + \
		_binary_learnts.capacity() * sizeof(Literal) + \
        _lit_equivalences.capacity() * sizeof(Literal) + \
        _component.Capacity() * sizeof(unsigned) + \
		_models.capacity() * sizeof(Model *) + \
		_cached_binary_clauses.capacity() * sizeof(Literal);
	}
	void Display( ostream & out )
	{
		unsigned i;
		out << "unary clauses: " << endl;
		for ( i = 0; i < _unary_clauses.size(); i++ ) {
			out << ExtLit( _unary_clauses[i] ) << " 0" << endl;
		}
		out << "binary clauses: " << endl;
		for ( i = 0; i < _binary_clauses.size(); i += 2 ) {
			out << ExtLit( _binary_clauses[i] ) << " " << ExtLit( _binary_clauses[i+1] ) << " 0" << endl;
		}
		out << "long clauses: " << endl;
		for ( i = 0; i < _old_num_long_clauses; i++ ) out << _long_clauses[i] << endl;
		out << "binary learnts: " << endl;
		for ( i = 0; i < _binary_learnts.size(); i += 2 ) {
			out << ExtLit( _binary_learnts[i] ) << " " << ExtLit( _binary_learnts[i+1] ) << " 0" << endl;
		}
		out << "long learnts: " << endl;
		for ( i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) out << _long_clauses[i] << endl;
		out << "literal equivalences: " << endl;
		for ( i = 0; i < _lit_equivalences.size(); i += 2 ) {
			out << ExtLit( _lit_equivalences[i] ) << " <-> " << ExtLit( _lit_equivalences[i+1] ) << endl;
		}
	}
};


}


#endif
