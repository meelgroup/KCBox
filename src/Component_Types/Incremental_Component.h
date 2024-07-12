#ifndef _Incremental_Component_h_
#define _Incremental_Component_h_

#include "Component.h"


namespace KCBox {


template <typename T> class Incremental_Component_Cache
{
protected:
	Variable _max_var;
	unsigned _num_long_cl;  // the total number of long clauses
	Cacheable_Component_Infor _hit_infor;
	T _default_caching_value;  // for IBCP, we could leave one component without getting result, thus use this notation
	Hash_Table<Cacheable_Component<T>> _pool;
	Cacheable_Component<T> _big_cacheable_component;
	Hash_Cluster<Literal> _original_binary_clauses;
	Hash_Cluster<Literal> _other_clauses;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
	size_t _clause_set_memory;
public:
	Incremental_Component_Cache():
		_max_var( Variable::undef ), _pool( COMPONENT_CACHE_INIT_SIZE ),
		_original_binary_clauses( Variable::start + 1 ), _other_clauses( Variable::start + 1 )
	{
		_hash_memory = _pool.Memory();
		_clause_set_memory = 0;
	}
	Incremental_Component_Cache( Variable max_var, unsigned num_long_clause, T default_value ) :
		_max_var( max_var ), _num_long_cl( num_long_clause ), _default_caching_value( default_value ), \
		_pool( COMPONENT_CACHE_INIT_SIZE ), _big_cacheable_component( NumVars( max_var ), num_long_clause ),
		_original_binary_clauses( max_var + 1 ), _other_clauses( max_var + 1 )
	{
		_hit_infor.Init( max_var, num_long_clause );
		_hash_memory = _pool.Memory();
		_clause_set_memory = 0;
	}
	~Incremental_Component_Cache()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		if ( _max_var != Variable::undef ) delete [] _big_cacheable_component._bits;
	}
	void Reset()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Reset();
		_big_cacheable_component.Reset();
		_max_var = Variable::undef;
		_hash_memory = _pool.Memory();
		_original_binary_clauses.Clear();
		_other_clauses.Clear();
	}
	void Init( unsigned max_var, unsigned num_long_clause, T default_value )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Compiler_Component_Cache]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_num_long_cl = num_long_clause;
		_hit_infor.Init( max_var, num_long_clause );
		Cacheable_Component<T>::_infor = _hit_infor;
		_default_caching_value = default_value;
		_big_cacheable_component.Init( max_var - Variable::start + 1, num_long_clause );
		_original_binary_clauses.Clear();
		_original_binary_clauses.Enlarge_Fullset( max_var );
		_other_clauses.Clear();
		_other_clauses.Enlarge_Fullset( max_var );  // no tautologies
	}
	void Clear()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Clear();
		_hash_memory = _pool.Memory();
	}
	void Clear( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) delete [] _pool[i]._bits;
		}
		_pool.Clear( kept_locs );
		_hash_memory = _pool.Memory();
	}
	unsigned Size() const { return _pool.Size(); }
	unsigned Capacity() const { return _pool.Capacity(); }
	unsigned Empty() const { return _pool.Empty(); }
	void Shrink_To_Fit()
	{
		_pool.Shrink_To_Fit();
		_hash_memory = _pool.Memory();
	}
	size_t Memory() const { return _hash_memory; }
	size_t Memory_Show()
	{
		cerr << _hash_memory << " (" << _other_clauses.Size() << ": " << _other_clauses.Memory() << ")" << endl;  // ToRemove
//		Display( cerr );  // ToRemove
		return _hash_memory;
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
			if ( _other_clauses.Size() - 1 > _hit_infor.Max_Num_Clauses() ) Extend_ClauseID_Encode();  // not consider the empty set
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
			if ( _other_clauses.Size() - 1 > _hit_infor.Max_Num_Clauses() ) Extend_ClauseID_Encode();  // not consider the empty set
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
	unsigned Hit_Component( Component & comp )
	{
		Cacheable_Component<T>::_infor = _hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		if ( comp.ClauseIDs_Size() > _num_long_cl ) {
			_num_long_cl = comp.ClauseIDs_Size();
			_big_cacheable_component.Update_Bits( NumVars( _max_var), _num_long_cl );
		}
		_big_cacheable_component.Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_component, _hash_memory );
		if ( pos == old_cache_size ) {
			unsigned size = _big_cacheable_component.Bits_Size();
			_pool[pos]._bits = new unsigned [size];
			_pool[pos]._bits[0] = _big_cacheable_component._bits[0];  // has at least one 4-bytes
			for ( i = 1; i < size; i++ ) _pool[pos]._bits[i] = _big_cacheable_component._bits[i];
			Write_Result( pos, _default_caching_value );  // the size of _big_cacheable_component._result may be different from that of _pool[pos]._result
		}
		_big_cacheable_component.Un_Assign();
		comp.caching_loc = pos;
		return pos;
	}
	bool Hit_Successful() { return _pool.Hit_Successful(); }
	void Read_Component( unsigned loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Component( comp ); }
	void Read_Component_Vars( unsigned loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Rough_Component( comp ); }
	const SortedSet<Literal> Read_Clause( SetID id ) { return _other_clauses.Elements( id + 1 ); }
	void Erase( unsigned loc )
	{
		if ( loc == _pool.Size() - 1 ) {
			_hash_memory -= _pool[loc].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += sizeof(Cacheable_Component<T>);

		}
		else {
			_hash_memory -= _pool[loc].Memory();
			_hash_memory -= _pool[_pool.Size() - 1].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += _pool[loc].Memory();
			_hash_memory += sizeof(Cacheable_Component<T>);
		}
	}
	T Read_Result( unsigned pos ) { return _pool[pos]._result; }
	void Write_Result( unsigned pos, const T result )
	{
		_hash_memory -= _pool[pos].Memory();
		_pool[pos]._result = result;
		_hash_memory += _pool[pos].Memory();  /// result's memory might not be equal to that of pool[loc]._result
	}
	double Duplicate_Rate()
	{
		vector<T> elems;
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			if ( _pool[i]._result != _default_caching_value ) {
				elems.push_back( _pool[i]._result );
			}
		}
		Quick_Sort( elems );
		unsigned real = 1;
		for ( unsigned i = 1; i < elems.size(); i++ ) {
			if ( elems[i] != elems[i-1] ) real++;
		}
		return 1.0 * elems.size() / real - 1;
	}
	double Useless_Rate()
	{
		unsigned num = 0;
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			num += ( _pool[i]._result == _default_caching_value );
		}
		return 1.0 * num / _pool.Size();
	}
	void Display( ostream & out )
	{
		Component comp;
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			Read_Component( i, comp );
			comp.Display( out );
		}
	}
protected:
	void Extend_ClauseID_Encode()
	{
		Component comp;
		Cacheable_Component_Infor old_infor = _hit_infor;
		_hit_infor.Extend_CCode( 1 );
		Cacheable_Component<T>::_infor = _hit_infor;  /// update Cacheable_Component::_infor before Update
		_big_cacheable_component.Update_Bits( NumVars( _max_var ), _num_long_cl );
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			Cacheable_Component<T>::_infor = old_infor;  /// update Cacheable_Component::_infor before Hit
			_pool[i].Read_Component( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
			delete [] _pool[i]._bits;
			unsigned new_size = Bits_Size( comp );
			_pool[i]._bits = new unsigned [new_size];
			for ( unsigned j = 1; j < new_size; j++ ) _pool[i]._bits[j] = 0;
			Cacheable_Component<T>::_infor = _hit_infor;  /// update Cacheable_Component::_infor before Hit
			_pool[i].Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		}
		_pool.Recompute_Entries();
		_hash_memory = _pool.Memory();
	}
    unsigned Bits_Size( Component & comp ) const
    {
    	unsigned num_var_bits = comp.Vars_Size() * _hit_infor._vcode_size;
    	unsigned num_cl_bits = comp.ClauseIDs_Size() * _hit_infor._ccode_size;
    	return ( num_var_bits + num_cl_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
	}
	void Verify( unsigned loc, Component & comp )
	{
		Component other;
		Read_Component( loc, other );
		assert( comp == other );
		for ( unsigned i = 0; i < loc; i++ ) {
			Read_Component( i, other );
			if ( comp == other ) {
				cerr << "ERROR[Incremental_Component_Cache]: equal entries " << i << " and " << loc << endl;
				assert( false );
			}
		}
	}
};


}


#endif
