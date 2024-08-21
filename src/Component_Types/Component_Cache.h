#ifndef _Component_Cache_h_
#define _Component_Cache_h_

#include "Cacheable_Component.h"


namespace KCBox {


#ifdef DEBUG_MODE
#define COMPONENT_CACHE_INIT_SIZE 1000
#else
#define COMPONENT_CACHE_INIT_SIZE LARGE_HASH_TABLE
#endif

template <typename T> class Component_Cache
{
protected:
	Variable _max_var;
	unsigned _num_long_cl;  // the total number of long clauses
	Cacheable_Component_Infor _hit_infor;
	T _default_caching_value;  // for IBCP, we could leave one component without getting result, thus use this notation
	Large_Hash_Table<Cacheable_Component<T>> _pool;
	Cacheable_Component<T> _big_cacheable_component;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
public:
	Component_Cache(): _max_var( Variable::undef ), _pool( COMPONENT_CACHE_INIT_SIZE )
	{
		_hash_memory = _pool.Memory();
	}
	Component_Cache( Variable max_var, unsigned num_long_clause, T default_value ) :
		_max_var( max_var ), _num_long_cl( num_long_clause ), _default_caching_value( default_value ), \
		_pool( COMPONENT_CACHE_INIT_SIZE ), _big_cacheable_component( NumVars( max_var ), num_long_clause )
	{
		_hit_infor.Init( max_var, num_long_clause );
		_hash_memory = _pool.Memory();
	}
	~Component_Cache()
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
	}
	void Init( Variable max_var, unsigned num_long_clause, T default_value )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Component_Cache]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_num_long_cl = num_long_clause;
		_hit_infor.Init( max_var, num_long_clause );
		Cacheable_Component<T>::_infor = _hit_infor;
		_default_caching_value = default_value;
		_big_cacheable_component.Init( NumVars( max_var ), num_long_clause );
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
		size_t i = 0;
		for ( ; i < _pool.Size() / 2; i++ ) {
			if ( !seen[i] ) delete [] _pool[i]._bits;
		}
		for ( ; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) kept_locs.push_back( i );
		}
		_pool.Clear( kept_locs );
		kept_locs.resize( old_size );
		_hash_memory = _pool.Memory();
	}
	T Default_Caching_Value() const { return _default_caching_value; }
	size_t Size() const { return _pool.Size(); }
	size_t Capacity() const { return _pool.Capacity(); }
	bool Empty() const { return _pool.Empty(); }
	size_t Memory() const { return _hash_memory; }
	void Shrink_To_Fit()
	{
		_pool.Shrink_To_Fit();
		_hash_memory = _pool.Memory();
	}
	CacheEntryID Hit_Component( Component & comp )
	{
		Cacheable_Component<T>::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		_big_cacheable_component.Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		size_t old_cache_size = _pool.Size();
		size_t pos = _pool.Hit( _big_cacheable_component, _hash_memory );
		if ( pos == old_cache_size ) {
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
	T Read_Result( CacheEntryID pos ) { return _pool[pos]._result; }
	void Write_Result( CacheEntryID pos, const T result )
	{
		_hash_memory -= _pool[pos].Memory();
		_pool[pos]._result = result;
		_hash_memory += _pool[pos].Memory();  /// result's memory might not be equal to that of pool[loc]._result
	}
	double Duplicate_Rate()
	{
		vector<T> elems;
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
	unsigned Bits_Size( Component & comp ) const
	{
		unsigned num_var_bits = comp.Vars_Size() * _hit_infor._vcode_size;
		unsigned num_cl_bits = comp.ClauseIDs_Size() * _hit_infor._ccode_size;
		return ( num_var_bits + num_cl_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
	}
	void Verify( CacheEntryID loc, Component & comp )
	{
		Component other;
		Read_Component( loc, other );
		assert( comp == other );
		for ( size_t i = 0; i < loc; i++ ) {
			Read_Component( i, other );
			if ( comp == other ) {
				cerr << "ERROR[Incremental_Component_Cache]: equal entries " << i << " and " << loc << endl;
				assert( false );
			}
		}
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
