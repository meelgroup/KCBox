#ifndef _Incremental_Component_BigInt_h_
#define _Incremental_Component_BigInt_h_

#include "Component_Cache.h"
#include "Cacheable_Clause.h"


namespace KCBox {


class Incremental_Component_Cache_BigInt
{
protected:
	Variable _max_var;
	unsigned _num_long_cl;  // the total number of long clauses
	Cacheable_Component_Infor _hit_infor;
	BigInt _default_caching_value;  // for IBCP, we could leave one component without getting result, thus use this notation
//	Hash_Table<Cacheable_Component_BigInt> _pool;
	Large_Hash_Table<Cacheable_Component<BigInt>> _pool;
	Cacheable_Component<BigInt> _big_cacheable_component;
	Hash_Cluster<Literal> _original_binary_clauses;
	Clause_Cache _other_clauses;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
	ullong _hit_count;
	ullong _hit_failed_count;
public:
	Incremental_Component_Cache_BigInt():
		_max_var( Variable::undef ), _pool( COMPONENT_CACHE_INIT_SIZE ),
		_original_binary_clauses( Variable::start + 1 )
	{
		_hash_memory = _pool.Memory();
		_hit_count = _hit_failed_count = 0;
	}
	Incremental_Component_Cache_BigInt( Variable max_var, unsigned num_long_clause, BigInt default_value ) :
		_max_var( max_var ), _num_long_cl( num_long_clause ), _default_caching_value( default_value ), \
		_pool( COMPONENT_CACHE_INIT_SIZE ), _big_cacheable_component( NumVars( max_var ), num_long_clause ),
		_original_binary_clauses( max_var + 1 ), _other_clauses( max_var )
	{
		_hit_infor.Init( max_var, num_long_clause );
		_hash_memory = _pool.Memory();
		_hit_count = _hit_failed_count = 0;
	}
	~Incremental_Component_Cache_BigInt()
	{
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		if ( _max_var != Variable::undef ) delete [] _big_cacheable_component._bits;
	}
	void Reset()
	{
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Clear();
		_big_cacheable_component.Reset();
		_max_var = Variable::undef;
		_hash_memory = _pool.Memory();
		_original_binary_clauses.Clear();
		_other_clauses.Reset();
		_hit_count = _hit_failed_count = 0;
	}
	void Init( Variable max_var, unsigned num_long_clause, BigInt default_value )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Compiler_Component_Cache]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_num_long_cl = num_long_clause;
		_hit_infor.Init( max_var, num_long_clause );
		Cacheable_Component<BigInt>::_infor = _hit_infor;
		_default_caching_value = default_value;
		_big_cacheable_component.Init( NumVars( max_var ), num_long_clause );
		_original_binary_clauses.Clear();
		_original_binary_clauses.Enlarge_Fullset( max_var );
		_other_clauses.Clear();
		_other_clauses.Init( max_var );  // no tautologies
	}
	void Clear()
	{
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Clear();
		_hash_memory = _pool.Memory();
	}
	void Clear( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( size_t i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) delete [] _pool[i]._bits;
		}
		_pool.Clear( kept_locs );
		_hash_memory = _pool.Memory();
	}
	void Clear_Shrink_Half( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( size_t i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) delete [] _pool[i]._bits;
		}
		_pool.Clear_Shrink_Half( kept_locs );
		_hash_memory = _pool.Memory();
	}
	void Clear_Half( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( size_t i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		size_t old_size = kept_locs.size();
		if ( true ) {  // ToModify
			size_t i = 0;
			for ( ; i < _pool.Size() / 2; i++ ) {
				if ( !seen[i] ) delete [] _pool[i]._bits;
			}
			for ( ; i < _pool.Size(); i++ ) {
				if ( !seen[i] ) kept_locs.push_back( i );
			}
		}
		else {
			for ( size_t i = 0; i < _pool.Size(); i++ ) {
				if ( !seen[i] ) {
					if ( i % 2 ) kept_locs.push_back( i );
					else delete [] _pool[i]._bits;
				}
			}
		}
		_pool.Clear( kept_locs );
		kept_locs.resize( old_size );
		_hash_memory = _pool.Memory();
	}
	BigInt Default_Caching_Value() const { return _default_caching_value; }
	size_t Size() const { return _pool.Size(); }
	size_t Capacity() const { return _pool.Capacity(); }
	void Reserve( size_t capacity )
	{
		_hash_memory -= _pool.Capacity() * sizeof(Cacheable_Component<BigInt>);
		_pool.Reserve( capacity );
		_hash_memory += _pool.Capacity() * sizeof(Cacheable_Component<BigInt>);
	}
	void Shrink_To_Fit()
	{
		_pool.Shrink_To_Fit();
		_hash_memory = _pool.Memory();
	}
	size_t Memory() const { return _hash_memory; }
	size_t Memory_Show()
	{
		cerr << _hash_memory << " (" << _other_clauses.Size() << ": " << _other_clauses.Memory() << ")" << endl;  // ToRemove
		cerr << "hit ratio: " << 100 - 100.0 * _hit_failed_count / _hit_count << "%" << endl;
//		Display( cerr );  // ToRemove
		return _hash_memory;
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
			if ( _other_clauses.Size() > _hit_infor.Max_Num_Clauses() ) Extend_ClauseID_Encode();
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
			if ( _other_clauses.Size() > _hit_infor.Max_Num_Clauses() ) Extend_ClauseID_Encode();
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
		Cacheable_Component<BigInt>::_infor = _hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		if ( comp.ClauseIDs_Size() > _num_long_cl ) {
			_num_long_cl = comp.ClauseIDs_Size();
			_big_cacheable_component.Update_Bits( NumVars( _max_var), _num_long_cl );
		}
		_big_cacheable_component.Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		size_t old_cache_size = _pool.Size();
		size_t pos = _pool.Hit( _big_cacheable_component, _hash_memory );
		_hit_count++;
		if ( pos == old_cache_size ) {
			_hit_failed_count++;
			unsigned size = _big_cacheable_component.Bits_Size();
			_pool[pos]._bits = new unsigned [size];
			_pool[pos]._bits[0] = _big_cacheable_component._bits[0];  // has at least one 4-bytes
			for ( unsigned i = 1; i < size; i++ ) _pool[pos]._bits[i] = _big_cacheable_component._bits[i];
			Write_Result( pos, _default_caching_value );  // the size of _big_cacheable_component._result may be different from that of _pool[pos]._result
		}
		_big_cacheable_component.Un_Assign();
		comp.caching_loc = pos;
		return pos;
	}
	bool Hit_Successful() { return _pool.Hit_Successful(); }
	void Read_Component( CacheEntryID loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Component( comp ); }
	void Read_Component_Vars( CacheEntryID loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Rough_Component( comp ); }
	void Erase( CacheEntryID loc )
	{
		if ( loc == _pool.Size() - 1 ) {
			_hash_memory -= _pool[loc].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += sizeof(Cacheable_Component<BigInt>);
		}
		else {
			_hash_memory -= _pool[loc].Memory();
			_hash_memory -= _pool[_pool.Size() - 1].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += _pool[loc].Memory();
			_hash_memory += sizeof(Cacheable_Component<BigInt>);
		}
	}
	BigInt Read_Result( CacheEntryID loc ) { return _pool[loc]._result; }
	void Write_Result( CacheEntryID loc, const BigInt result )
	{
		_hash_memory -= _pool[loc]._result.Memory();
		_pool[loc]._result = result;
		_hash_memory += _pool[loc]._result.Memory();  /// result's memory might not be equal to that of pool[loc]._result
	}
	double Duplicate_Rate()
	{
		vector<BigInt> elems;
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			if ( _pool[i]._result != _default_caching_value ) {
				elems.push_back( _pool[i]._result );
			}
		}
		Quick_Sort( elems );
		size_t real = 1;
		for ( size_t i = 1; i < elems.size(); i++ ) {
			if ( elems[i] != elems[i-1] ) real++;
		}
		return 1.0 * elems.size() / real - 1;
	}
	double Useless_Rate()
	{
		size_t num = 0;
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			num += ( _pool[i]._result == _default_caching_value );
		}
		return 1.0 * num / _pool.Size();
	}
	void Display( ostream & out )
	{
		Component comp;
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
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
		Cacheable_Component<BigInt>::_infor = _hit_infor;  /// update Cacheable_Component::_infor before Update
		_big_cacheable_component.Update_Bits( NumVars( _max_var ), _num_long_cl );
		for ( size_t i = 0; i < _pool.Size(); i++ ) {
			Cacheable_Component<BigInt>::_infor = old_infor;  /// update Cacheable_Component::_infor before Hit
			_pool[i].Read_Component( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
			delete [] _pool[i]._bits;
			unsigned new_size = Bits_Size( comp );
			_pool[i]._bits = new unsigned [new_size];
			for ( unsigned j = 1; j < new_size; j++ ) _pool[i]._bits[j] = 0;
			Cacheable_Component<BigInt>::_infor = _hit_infor;  /// update Cacheable_Component::_infor before Hit
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
public:
	bool Entry_Is_Isolated( CacheEntryID loc )
	{
		bool parent_exi = _pool[loc]._parent != CacheEntryID::undef;
		bool first_exi = _pool[loc]._first_child != CacheEntryID::undef;
		bool next_exi = _pool[loc]._next_sibling != CacheEntryID::undef;
		return !parent_exi && !first_exi && !next_exi;
	}
	bool Entry_More_Than_Two_Children( CacheEntryID loc )
	{
		CacheEntryID child = _pool[loc]._first_child;
		if ( child == CacheEntryID::undef ) return false; // 0
		child = _pool[child]._next_sibling;
		if ( child == CacheEntryID::undef ) return false; // 1
		child = _pool[child]._next_sibling;
		if ( child == CacheEntryID::undef ) return false; // 2
		return true;
	}
	bool Entry_Is_Child( CacheEntryID loc, CacheEntryID child )
	{
		assert( Entry_Valid( loc ) );
		if ( child == CacheEntryID::undef ) return false;
		assert( Entry_Valid( child ) );
		return _pool[child]._parent == loc;
	}
	void Entry_Set_Isolated( CacheEntryID loc )
	{
		_pool[loc]._parent = CacheEntryID::undef;
		_pool[loc]._first_child = CacheEntryID::undef;
		_pool[loc]._next_sibling = CacheEntryID::undef;
	}
	void Entry_Add_Child( CacheEntryID loc, CacheEntryID child )
	{
		assert( Entry_Valid( loc ) && Entry_Valid( child ) );
		_pool[child]._parent = loc;
		if ( _pool[loc]._first_child == CacheEntryID::undef ) _pool[loc]._first_child = child;
		else _pool[Entry_Last_Child( loc )]._next_sibling = child;
	}
	void Entry_Add_Sibling( CacheEntryID loc, CacheEntryID sibling )
	{
		assert( Entry_Valid( loc ) && Entry_Valid( sibling ) );
		_pool[Entry_Last_Sibling( loc )]._next_sibling = sibling;
		_pool[sibling]._parent = _pool[loc]._parent;
	}
	void Entry_Disconnect_Parent( CacheEntryID loc )
	{
		assert( Entry_Valid( loc ) && Entry_Valid( _pool[loc]._parent ) );
		CacheEntryID sibling = Entry_Previous_Sibling( loc );
		if ( sibling == CacheEntryID::undef ) _pool[_pool[loc]._parent]._first_child = _pool[loc]._next_sibling;
		else _pool[sibling]._next_sibling = _pool[loc]._next_sibling;
		_pool[loc]._parent = CacheEntryID::undef;
		_pool[loc]._next_sibling = CacheEntryID::undef;
	}
	void Entry_Swap( CacheEntryID loc, CacheEntryID new_loc )
	{
		assert( Entry_Valid( loc ) && Entry_Valid( new_loc ) && Entry_Is_Isolated( new_loc ) );
		_pool[new_loc]._parent = _pool[loc]._parent;
		_pool[new_loc]._first_child = _pool[loc]._first_child;
		_pool[new_loc]._next_sibling = _pool[loc]._next_sibling;
		CacheEntryID child = _pool[loc]._first_child;
		while ( child != CacheEntryID::undef ) {
			_pool[child]._parent = new_loc;
			child = _pool[child]._next_sibling;
		}
		CacheEntryID prev = Entry_Previous_Sibling( loc );
		if ( prev == CacheEntryID::undef ) _pool[_pool[loc]._parent]._first_child = new_loc;
		else _pool[prev]._next_sibling = new_loc;
		Entry_Set_Isolated( loc );
	}
	void Entry_Reset_Subtrees( CacheEntryID loc )
	{
		assert( Entry_Valid( loc ) );
		stack<CacheEntryID> node_stack;
		if ( _pool[loc]._first_child != CacheEntryID::undef ) {
			node_stack.push( _pool[loc]._first_child );
			_pool[loc]._first_child = CacheEntryID::undef;
		}
		while ( !node_stack.empty() ) {
			CacheEntryID top = node_stack.top();
			node_stack.pop();
			_pool[top]._parent = CacheEntryID::undef;
			_pool[top]._result = _default_caching_value;
			if ( _pool[top]._next_sibling != CacheEntryID::undef ) {
				node_stack.push( _pool[top]._next_sibling );
				_pool[top]._next_sibling = CacheEntryID::undef;
			}
			if ( _pool[top]._first_child != CacheEntryID::undef ) {
				node_stack.push( _pool[top]._first_child );
				_pool[top]._first_child = CacheEntryID::undef;
			}
		}
	}
	void Verify_Entries()
	{
		assert( _pool[0]._parent == CacheEntryID::undef );
		Entry_Verify_Children( 0 );
		vector<CacheEntryID> entries = Entry_Descendants( 0 );
		vector<bool> seen( _pool.Size(), false );
		for ( size_t i = 0; i < entries.size(); i++ ) {
			seen[entries[i]] = true;
		}
		for ( size_t i = 1; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) {
				if ( !Entry_Is_Isolated( i ) ) {
					cerr << "ERROR[Incremental_Component_Cache_BigInt]: entry " << i << " is not isolated!" << endl;
					assert( Entry_Is_Isolated( i ) );
				}
			}
			else Entry_Verify_Children( i );
		}
	}
protected:
	bool Entry_Valid( CacheEntryID loc ) { return loc < _pool.Size(); }
	CacheEntryID Entry_Previous_Sibling( CacheEntryID loc )
	{
		if ( loc == _pool[_pool[loc]._parent]._first_child ) return CacheEntryID::undef;
		CacheEntryID sibling = _pool[_pool[loc]._parent]._first_child;
		while ( _pool[sibling]._next_sibling != loc ) sibling = _pool[sibling]._next_sibling;
		return sibling;
	}
	CacheEntryID Entry_Last_Sibling( CacheEntryID loc )
	{
		CacheEntryID sibling = loc;
		while ( _pool[sibling]._next_sibling != CacheEntryID::undef ) sibling = _pool[sibling]._next_sibling;
		return sibling;

	}
	CacheEntryID Entry_Last_Child( CacheEntryID loc )
	{
		if ( _pool[loc]._first_child == CacheEntryID::undef ) return CacheEntryID::undef;
		return Entry_Last_Sibling( _pool[loc]._first_child );
	}
	void Entry_Verify_Children( CacheEntryID loc )
	{
		if ( _pool[loc]._first_child == CacheEntryID::undef ) return;
		CacheEntryID child = _pool[loc]._first_child;
		while ( child != CacheEntryID::undef ) {
			assert( _pool[child]._parent == loc );
			child = _pool[child]._next_sibling;
		}
	}
	vector<CacheEntryID> Entry_Descendants( CacheEntryID loc )
	{
		vector<CacheEntryID> nodes;
		if ( _pool[loc]._first_child != CacheEntryID::undef ) {
			nodes.push_back( _pool[loc]._first_child );
		}
		for ( size_t i = 0; i < nodes.size(); i++ ) {
			CacheEntryID top = nodes[i];
			if ( _pool[top]._first_child != CacheEntryID::undef ) {
				nodes.push_back( _pool[top]._first_child );
			}
			if ( _pool[top]._next_sibling != CacheEntryID::undef ) {
				nodes.push_back( _pool[top]._next_sibling );
			}
		}
		return nodes;
	}
};


}


#endif
