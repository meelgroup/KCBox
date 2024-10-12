#ifndef _Incremental_Component_Cache_h_
#define _Incremental_Component_Cache_h_

#include "Component_Cache.h"


namespace KCBox {


template <typename T> class Incremental_Component_Cache: public Component_Cache<T>
{
protected:
	Hash_Cluster<Literal> _original_binary_clauses;
	Hash_Cluster<Literal> _other_clauses;
	size_t _clause_set_memory;
public:
	Incremental_Component_Cache(): Component_Cache<T>(),
		_original_binary_clauses( Variable::start + 1 ), _other_clauses( Variable::start + 1 )
	{
		_clause_set_memory = 0;
	}
	Incremental_Component_Cache( Variable max_var, unsigned num_long_clause, T default_value ) :
		Component_Cache<T>( max_var, num_long_clause, default_value ), \
		_original_binary_clauses( max_var + 1 ), _other_clauses( max_var + 1 )
	{
		_clause_set_memory = 0;
	}
	~Incremental_Component_Cache() {}
	void Reset()
	{
		Component_Cache<T>::Reset();
		_original_binary_clauses.Clear();
		_other_clauses.Clear();
	}
	void Init( Variable max_var, unsigned num_long_clause, T default_value )
	{
		Component_Cache<T>::Init( max_var, num_long_clause, default_value );
		_original_binary_clauses.Clear();
		_original_binary_clauses.Enlarge_Fullset( max_var );
		_other_clauses.Clear();
		_other_clauses.Enlarge_Fullset( max_var );  // no tautologies
	}
	const SortedSet<Literal> Long_Clauses( SetID id ) { return _other_clauses.Elements( id ); }
	void Add_Original_Binary_Clause( Literal lit, Literal lit2 )
	{
		_original_binary_clauses.Binary_Set( lit, lit2 );
	}
	SetID Encode_Binary_Clause( Literal lit, Literal lit2 )
	{
		if ( _original_binary_clauses.Binary_Set_ID( lit, lit2 ) != SETID_UNDEF ) {
			return SETID_UNDEF;
		}
		unsigned old_size = _other_clauses.Size();
		SetID set = _other_clauses.Binary_Set( lit, lit2 );
		if ( old_size < _other_clauses.Size() ) {
//			cerr << ExtLit( lit ) << " " << ExtLit( lit2 ) << " 0" << endl;
			_clause_set_memory += sizeof(Literal) * 2;
			if ( _other_clauses.Size() - 1 > this->_hit_infor.Max_Num_Clauses() ) this->Extend_ClauseID_Encode();  // not consider the empty set
		}
		return set - 1;  // not consider the empty set
	}
	SetID Encode_Long_Clause( Literal * lits, unsigned size )
	{
		unsigned old_size = _other_clauses.Size();
		SetID set = _other_clauses.Set( lits, size );
		if ( old_size < _other_clauses.Size() ) {
			for ( unsigned i = 0; i < size; i++ ) {
//				cerr << ExtLit( lits[i] ) << " ";
			}
//			cerr << "0" << endl;
			_clause_set_memory += sizeof(Literal) * size;
			if ( _other_clauses.Size() - 1 > this->_hit_infor.Max_Num_Clauses() ) this->Extend_ClauseID_Encode();  // not consider the empty set
		}
		return set - 1;  // not consider the empty set
	}
	SetID Binary_Clause_ID( Literal lit, Literal lit2 )
	{
		cerr << ExtLit( lit ) << " " << ExtLit( lit2 ) << " 0" << endl;
		if ( _original_binary_clauses.Binary_Set_ID( lit, lit2 ) != SETID_UNDEF ) {
			return SETID_UNDEF;
		}
		else return _other_clauses.Binary_Set_ID( lit, lit2 ) - 1;  // not consider the empty set
	}
	CacheEntryID Hit_Component( Component & comp )
	{
		Cacheable_Component<T>::_infor = this->_hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		if ( comp.ClauseIDs_Size() > this->_num_long_cl ) {
			this->_num_long_cl = comp.ClauseIDs_Size();
			this->_big_cacheable_component.Update_Bits( NumVars( this->_max_var ), this->_num_long_cl );
		}
		return Component_Cache<T>::Hit_Component( comp );
	}
	const SortedSet<Literal> Read_Clause( SetID id ) { return _other_clauses.Elements( id + 1 ); }
};


}


#endif
