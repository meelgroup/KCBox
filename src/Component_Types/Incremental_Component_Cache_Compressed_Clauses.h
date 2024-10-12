#ifndef _Incremental_Component_Cache_Compressed_Clauses_h_
#define _Incremental_Component_Cache_Compressed_Clauses_h_

#include "Component_Cache.h"
#include "Cacheable_Clause.h"


namespace KCBox {


template <typename T> class Incremental_Component_Cache_Compressed_Clauses: public Component_Cache<T>
{
protected:
	Hash_Cluster<Literal> _original_binary_clauses;
	Clause_Cache _other_clauses;
	ullong _hit_count;
	ullong _hit_failed_count;
public:
	Incremental_Component_Cache_Compressed_Clauses(): Component_Cache<T>(),
		_original_binary_clauses( Variable::start + 1 )
	{
		_hit_count = _hit_failed_count = 0;
	}
	Incremental_Component_Cache_Compressed_Clauses( Variable max_var, unsigned num_long_clause, T default_value ) :
		Component_Cache<T>( max_var, num_long_clause, default_value ), \
		_original_binary_clauses( max_var + 1 ), _other_clauses( max_var )
	{
		_hit_count = _hit_failed_count = 0;
	}
	~Incremental_Component_Cache_Compressed_Clauses() {}
	void Reset()
	{
		Component_Cache<T>::Reset();
		_original_binary_clauses.Clear();
		_other_clauses.Reset();
		_hit_count = _hit_failed_count = 0;
	}
	void Init( Variable max_var, unsigned num_long_clause, T default_value )
	{
		Component_Cache<T>::Init( max_var, num_long_clause, default_value );
		_original_binary_clauses.Clear();
		_original_binary_clauses.Enlarge_Fullset( max_var );
		_other_clauses.Clear();
		_other_clauses.Init( max_var );  // no tautologies
	}
	size_t Memory_Show()
	{
		cerr << this->_hash_memory << " (" << _other_clauses.Size() << ": " << _other_clauses.Memory() << ")" << endl;  // ToRemove
		cerr << "hit ratio: " << 100 - 100.0 * _hit_failed_count / _hit_count << "%" << endl;
//		Display( cerr );  // ToRemove
		return this->_hash_memory;
	}
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
		SetID set = _other_clauses.Hit_Binary_Clause( lit, lit2 );
		if ( old_size < _other_clauses.Size() ) {
//			cerr << ExtLit( lit ) << " " << ExtLit( lit2 ) << " 0" << endl;
			if ( _other_clauses.Size() > this->_hit_infor.Max_Num_Clauses() ) this->Extend_ClauseID_Encode();
		}
		return set;
	}
	SetID Encode_Long_Clause( Literal * lits, unsigned size )
	{
		unsigned old_size = _other_clauses.Size();
		SetID set = _other_clauses.Hit_Clause( lits, size );
		if ( old_size < _other_clauses.Size() ) {
			for ( unsigned i = 0; i < size; i++ ) {
//				cerr << ExtLit( lits[i] ) << " ";
			}
//			cerr << "0" << endl;
			if ( _other_clauses.Size() > this->_hit_infor.Max_Num_Clauses() ) this->Extend_ClauseID_Encode();
		}
		return set;
	}
	SetID Binary_Clause_ID( Literal lit, Literal lit2 )
	{
		cerr << ExtLit( lit ) << " " << ExtLit( lit2 ) << " 0" << endl;
		if ( _original_binary_clauses.Binary_Set_ID( lit, lit2 ) != SETID_UNDEF ) {
			return SETID_UNDEF;
		}
		else return _other_clauses.Hit_Binary_Clause( lit, lit2 );
	}
	CacheEntryID Hit_Component( Component & comp )
	{
		Cacheable_Component<T>::_infor = this->_hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		if ( comp.ClauseIDs_Size() > this->_num_long_cl ) {
			this->_num_long_cl = comp.ClauseIDs_Size();
			this->_big_cacheable_component.Update_Bits( NumVars( this->_max_var), this->_num_long_cl );
		}
		cache_size_t pos = Component_Cache<T>::Hit_Component( comp );
		_hit_count++;
		_hit_failed_count += !this->_pool.Hit_Successful();
		return pos;
	}
};


}


#endif
