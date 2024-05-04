#ifndef _Component_ExtraMemo_h_
#define _Component_ExtraMemo_h_

#include "Component.h"


namespace KCBox {



class Component_Cache_BigFloat;

class Cacheable_Component_BigFloat: public Cacheable_Component<BigFloat>
{
	friend class Component_Cache_BigFloat;
protected:
public:
	Cacheable_Component_BigFloat() {}
	Cacheable_Component_BigFloat( unsigned num_var, unsigned num_cl ): Cacheable_Component<BigFloat>( num_var, num_cl ) {}
	size_t Memory() const
	{
		size_t result_extra_memo = _result.Memory() - sizeof(BigFloat);
		return sizeof(Cacheable_Component_BigFloat) + Bits_Size() * sizeof(unsigned) + result_extra_memo;
	}
protected:
};


class Component_Cache_BigFloat
{
protected:
	Variable _max_var;
	unsigned _num_long_cl;  // the total number of long clauses
	Cacheable_Component_Infor _hit_infor;
	BigFloat _default_caching_value;  // for IBCP, we could leave one component without getting result, thus use this notation
	Large_Hash_Table<Cacheable_Component_BigFloat> _pool;
	Cacheable_Component_BigFloat _big_cacheable_component;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
public:
	Component_Cache_BigFloat(): _max_var( Variable::undef ), _pool( COMPONENT_CACHE_INIT_SIZE )
	{
		_hash_memory = _pool.Memory();
	}
	Component_Cache_BigFloat( Variable max_var, unsigned num_long_clause, BigFloat default_value ) :
		_max_var( max_var ), _num_long_cl( num_long_clause ), _default_caching_value( default_value ), \
		_pool( COMPONENT_CACHE_INIT_SIZE ), _big_cacheable_component( NumVars( max_var ), num_long_clause )
	{
		_hit_infor.Init( max_var, num_long_clause );
		_hash_memory = _pool.Memory();
	}
	~Component_Cache_BigFloat()
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
		_pool.Clear();
		_big_cacheable_component.Reset();
		_max_var = Variable::undef;
		_hash_memory = _pool.Memory();
	}
	void Init( unsigned max_var, unsigned num_long_clause, BigFloat default_value )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Component_Cache_ExtraMemo]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_num_long_cl = num_long_clause;
		_hit_infor.Init( max_var, num_long_clause );
		Cacheable_Component_BigFloat::_infor = _hit_infor;
		_default_caching_value = default_value;
		_big_cacheable_component.Init( max_var - Variable::start + 1, num_long_clause );
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
	void Clear_Shrink_Half( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			if ( !seen[i] ) delete [] _pool[i]._bits;
		}
		_pool.Clear_Shrink_Half( kept_locs );
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
	unsigned Memory() const { return _hash_memory; }
	unsigned Hit_Component( Component & comp )
	{
		Cacheable_Component_BigFloat::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		_big_cacheable_component.Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_component, _hash_memory );
		if ( pos == old_cache_size ) {
			unsigned size = _big_cacheable_component.Bits_Size();
			_pool[pos]._bits = new unsigned [size];
			_pool[pos]._bits[0] = _big_cacheable_component._bits[0];  // has at least one 4-bytes
			for ( i = 1; i < size; i++ ) _pool[pos]._bits[i] = _big_cacheable_component._bits[i];
			_pool[pos]._result = _default_caching_value;
		}
		_big_cacheable_component.Un_Assign();
		comp.caching_loc = pos;
		return pos;
	}
	bool Hit_Successful() { return _pool.Hit_Successful(); }
	void Read_Component( unsigned loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Component( comp ); }
	void Read_Component_Vars( unsigned loc, Component & comp ) { comp.caching_loc = loc;  _pool[loc].Read_Rough_Component( comp ); }
	void Erase( unsigned loc )
	{
		if ( loc == _pool.Size() - 1 ) {
			_hash_memory -= _pool[loc].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += sizeof(Cacheable_Component_BigFloat);
		}
		else {
			_hash_memory -= _pool[loc].Memory();
			_hash_memory -= _pool[_pool.Size() - 1].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += _pool[loc].Memory();
			_hash_memory += sizeof(Cacheable_Component_BigFloat);
		}
	}
	BigFloat Read_Result( unsigned pos ) { return _pool[pos]._result; }
	void Write_Result( unsigned pos, const BigFloat result ) { _pool[pos]._result = result; }
	double Duplicate_Rate()
	{
		vector<BigFloat> elems;
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
};


}


#endif
