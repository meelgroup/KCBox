#ifndef _Cacheable_Component_h_
#define _Cacheable_Component_h_

#include "../Parameters.h"
#include "Component.h"
#ifdef ACTIVATE_CLHASH
#include "../clhash/clhash.h"
#endif


namespace KCBox {


struct Cacheable_Component_Infor
{
	unsigned _vcode_size;
	unsigned _ccode_size;
	unsigned _vcode_mask;  // used to recover
	unsigned _ccode_mask;  // used to recover
	Cache_Encoding_Strategy _encoding = Simple_Cache_Encoding;
	void Init( unsigned max_var, unsigned num_long_clauses )
	{
		_vcode_size = Ceil_Log2( max_var - Variable::start + 1 );
		_ccode_size = num_long_clauses <= 2 ? 1 : Ceil_Log2( num_long_clauses );  /// NOTE: a zero-bit ccode may lead to a wrong num_clause
		_vcode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _vcode_size );
		_ccode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _ccode_size );
	}
	void Set_Encoding( Cache_Encoding_Strategy encoding ) { _encoding = encoding; }
	void Extend_CCode( unsigned inc )
	{
		_ccode_size += inc;
		_ccode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _ccode_size );
	}
	unsigned Max_Num_Clauses() { return 1 << _ccode_size; }
};

template <typename T> size_t Extra_Memory( const T & data, typename T::int_type ) { return data.Memory() - sizeof(T); }
template <typename T> size_t Extra_Memory( const T & data, T ) { UNUSED(data);  return 0; }

template <typename T> class Component_Cache;
template <typename T> class Incremental_Component_Cache;
template <typename T> class Incremental_Component_Cache_Compressed_Clauses;

template <typename T> class Cacheable_Component
{
	friend class Component_Cache<T>;
	friend class Incremental_Component_Cache<T>;
	friend class Incremental_Component_Cache_Compressed_Clauses<T>;
protected:
	static Cacheable_Component_Infor _infor;   /// NOTE: for different Component_Cache, _infor is different, so please adjust it before use
#ifdef ACTIVATE_CLHASH
	static clhasher hasher;
#endif
	unsigned _num_var;  // NOTE: _num_var is always greater than 1
	unsigned _num_cl;
	unsigned * _bits;  // NOTE: when a type uses memory beyond the ones sizeof counts, please declare a sub-type int_type, and defines a function Memory
	uint64_t _key;
	T _result;
public:
	Cacheable_Component(): _num_var( 0 ) {}
	Cacheable_Component( unsigned num_var, unsigned num_cl ): _num_var( num_var ), _num_cl( num_cl )
	{
		unsigned i, size = Bits_Max_Size();
		_bits = new unsigned [size];
		for ( i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	Cacheable_Component( const Cacheable_Component & other )
	{
		_num_var = other._num_var;
		_num_cl = other._num_cl;
		_bits = other._bits;
		_key = other._key;
		_result = other._result; // node is not initialized is hash table
		_parent = other._parent;
		_first_child = other._first_child;
		_next_sibling = other._next_sibling;
	}
	void Init( unsigned num_var, unsigned num_cl )
	{
		if ( _num_var > 0 || num_var == 0 ) {
			cerr << "ERROR[Cacheable_Component]: no need to be initialized!" << endl;
			exit( 0 );
		}
		_num_var = num_var;
		_num_cl = num_cl;
		unsigned size = Bits_Max_Size();
		_bits = new unsigned [size];
		for ( unsigned i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Reset()
	{
		if ( _num_var != 0 ) {
			delete [] _bits;
			_num_var = 0;
		}
	}
	void Update_Bits( unsigned num_var, unsigned num_cl )
	{
		assert( _num_var != 0 );
		delete [] _bits;
		_num_var = num_var;
		_num_cl = num_cl;
		unsigned size = Bits_Max_Size();
		_bits = new unsigned [size];
		for ( unsigned i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Assign( Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
	{
		ASSERT( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		ASSERT( _infor._vcode_size < UNSIGNED_SIZE );
		ASSERT( _num_var > 0 );
		ASSERT( comp.Vars_Size() >= 2 );
		switch ( _infor._encoding ) {
		case Simple_Cache_Encoding:
			Assign_Simple( comp );
			break;
		case Difference_Cache_Encoding:
			Assign_Difference( comp );
			break;
		default:
			cerr << "ERROR[Cacheable_Component]: invalid encoding!" << endl;
			exit( 1 );
		}
	}
	void Assign_Simple( Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
	{
		unsigned i, begin;
		_num_var = comp.Vars_Size();
		_num_cl = comp.ClauseIDs_Size();
		_bits[0] = comp.Vars(0) - Variable::start; /// NOTE: start from 0; _infor._vcode_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
		for ( i = 1, begin = _infor._vcode_size; i < _num_var; i++, begin += _infor._vcode_size ) {  // cache.vars is nonempty
			_bits[begin / UNSIGNED_SIZE] |= ( comp.Vars(i) - Variable::start ) << ( begin % UNSIGNED_SIZE );
			if ( _infor._vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = ( comp.Vars(i) - Variable::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		for ( i = 0; i < _num_cl; i++, begin += _infor._ccode_size ) {
			_bits[begin / UNSIGNED_SIZE] |= comp.ClauseIDs(i) << ( begin % UNSIGNED_SIZE );
			if ( _infor._ccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = comp.ClauseIDs(i) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		Compute_Key();
	}
	void Assign_Difference( Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
	{
		_num_var = comp.Vars_Size();
		unsigned var_diff = comp.Vars(1) - comp.Vars(0);
		for ( unsigned i = 2; i < comp.Vars_Size(); i++ ) {
			if ( comp.Vars(i) - comp.Vars(i-1) > var_diff ) var_diff = comp.Vars(i) - comp.Vars(i-1);
		}
		unsigned var_diff_code_size = Ceil_Log2( var_diff );
		_bits[0] = var_diff; /// NOTE: start from 0; _infor._vcode_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
		unsigned begin = _infor._vcode_size;
		Write_Block( begin, comp.Vars(0) - Variable::start, _infor._vcode_size );
		begin += _infor._vcode_size;
		for ( unsigned i = 1; i < _num_var; i++, begin += var_diff_code_size ) {  // cache.vars is nonempty
			Write_Block( begin, comp.Vars(i) - comp.Vars(i-1) - 1, var_diff_code_size );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		_num_cl = comp.ClauseIDs_Size();
		if ( _num_cl > 0 ) {
			unsigned cl_diff = 0;
			for ( unsigned i = 1; i < comp.ClauseIDs_Size(); i++ ) {
				if ( comp.ClauseIDs(i) - comp.ClauseIDs(i-1) > cl_diff ) cl_diff = comp.ClauseIDs(i) - comp.ClauseIDs(i-1);
			}
			unsigned cl_diff_code_size = Ceil_Log2( cl_diff );
			Write_Block( begin, cl_diff, _infor._ccode_size );
			begin += _infor._ccode_size;
			Write_Block( begin, comp.ClauseIDs(0), _infor._ccode_size );
			begin += _infor._ccode_size;
			for ( unsigned i = 1; i < _num_cl; i++, begin += cl_diff_code_size ) {
				Write_Block( begin, comp.ClauseIDs(i) - comp.ClauseIDs(i-1) - 1, cl_diff_code_size );  // NOTE: a == ( a >> UNSIGNED_SIZE )
			}
		}
		Compute_Key();
	}
	void Un_Assign()
	{
		unsigned i, size = Bits_Size();
		for ( i = 1; i < size; i++ ) _bits[i] = 0;
	}
	void Read_Component( Component & comp )
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var >= 2 );
		switch ( _infor._encoding ) {
		case Simple_Cache_Encoding:
			Read_Component_Simple( comp );
			break;
		case Difference_Cache_Encoding:
			Read_Component_Difference( comp );
			break;
		default:
			cerr << "ERROR[Cacheable_Component]: invalid encoding!" << endl;
			exit( 1 );
		}
	}
	void Read_Component_Simple( Component & comp )
	{
		unsigned i, begin, var, cl;
		comp.Clear();
		var = _bits[0] & _infor._vcode_mask;
		comp.Add_Var( Variable( var + Variable::start ) );
		for ( i = 1, begin = _infor._vcode_size; i < _num_var; i++, begin += _infor._vcode_size ) {
			var = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & _infor._vcode_mask;
			if ( _infor._vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				var |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & _infor._vcode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			comp.Add_Var( Variable( var + Variable::start ) );
		}
		comp.Add_Var( Variable::undef );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp.Dec_Var();  /// pop Variable::undef
		for ( i = 0; i < _num_cl; i++, begin += _infor._ccode_size ) {
			cl = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & _infor._ccode_mask;
			if ( _infor._ccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				cl |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & _infor._ccode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			comp.Add_ClauseID( cl );
		}
	}
	void Read_Component_Difference( Component & comp )
	{
		comp.Clear();
		unsigned var_diff = _bits[0] & _infor._vcode_mask;
		unsigned var_diff_code_size = Ceil_Log2( var_diff );
		unsigned var_diff_code_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - var_diff_code_size );
		unsigned begin = _infor._vcode_size;
		unsigned var = Read_Block( begin, _infor._vcode_size, _infor._vcode_mask );
		comp.Add_Var( Variable( var + Variable::start ) );
		begin += _infor._vcode_size;
		for ( unsigned i = 1; i < _num_var; i++, begin += var_diff_code_size ) {
			var = Read_Block( begin, var_diff_code_size, var_diff_code_mask );
			comp.Add_Var( Variable( comp.Vars(i - 1) + var + 1 ) );
		}
		comp.Add_Var( Variable::undef );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp.Dec_Var();  /// pop Variable::undef
		if ( _num_cl == 0 ) return;
		unsigned cl_diff = Read_Block( begin, _infor._ccode_size, _infor._ccode_mask );
		begin += _infor._ccode_size;
		unsigned cl_diff_code_size = Ceil_Log2( cl_diff );  /// NOTE: a zero-bit ccode may lead to a wrong num_clause
		unsigned cl_diff_code_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - cl_diff_code_size );
		unsigned cl = Read_Block( begin, _infor._ccode_size, _infor._ccode_mask );
		begin += _infor._ccode_size;
		comp.Add_ClauseID( cl );
		for ( unsigned i = 1; i < _num_cl; i++, begin += cl_diff_code_size ) {
			cl = Read_Block( begin, cl_diff_code_size, cl_diff_code_mask );
			comp.Add_ClauseID( comp.ClauseIDs(i - 1) + cl + 1 );
		}
	}
	void Read_Rough_Component( Component & comp )  // not read _clauses
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var >= 2 );
		switch ( _infor._encoding ) {
		case Simple_Cache_Encoding:
			Read_Rough_Component_Simple( comp );
			break;
		case Difference_Cache_Encoding:
			Read_Rough_Component_Difference( comp );
			break;
		default:
			cerr << "ERROR[Cacheable_Component]: invalid encoding!" << endl;
			exit( 1 );
		}
	}
	void Read_Rough_Component_Simple( Component & comp )  // not read _clauses
	{
		unsigned i, begin, var;
		comp.Clear_Vars();
		var = _bits[0] & _infor._vcode_mask;
		comp.Add_Var( Variable( var + Variable::start ) );
		for ( i = 1, begin = _infor._vcode_size; i < _num_var; i++, begin += _infor._vcode_size ) {
			var = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & _infor._vcode_mask;
			if ( _infor._vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				var |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & _infor._vcode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			comp.Add_Var( Variable( var + Variable::start ) );
		}
		comp.Add_Var( Variable::undef );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp.Dec_Var();  /// pop Variable::undef
		comp.ClauseIDs_Resize( _num_cl );  // when we decide whether comp is trivial, we will use the size of comp.clauses
	}
	void Read_Rough_Component_Difference( Component & comp )  // not read _clauses
	{
		comp.Clear_Vars();
		unsigned var_diff = _bits[0] & _infor._vcode_mask;
		unsigned var_diff_code_size = Ceil_Log2( var_diff );
		unsigned var_diff_code_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - var_diff_code_size );
		unsigned begin = _infor._vcode_size;
		unsigned var = Read_Block( begin, _infor._vcode_size, _infor._vcode_mask );
		comp.Add_Var( Variable( var + Variable::start ) );
		begin += _infor._vcode_size;
		for ( unsigned i = 1; i < _num_var; i++, begin += var_diff_code_size ) {
			var = Read_Block( begin, var_diff_code_size, var_diff_code_mask );
			comp.Add_Var( Variable( comp.Vars(i - 1) + var + 1 ) );
		}
		comp.Add_Var( Variable::undef );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp.Dec_Var();  /// pop Variable::undef
		comp.ClauseIDs_Resize( _num_cl );  // when we decide whether comp is trivial, we will use the size of comp.clauses
	}
	Cacheable_Component & operator = ( const Cacheable_Component & other )  // NOTE: used in hash
	{
		_num_var = other._num_var;
		_num_cl = other._num_cl;
		_bits = other._bits;
		_key = other._key;
		_result = other._result; // node is not initialized is hash table
		_parent = other._parent;
		_first_child = other._first_child;
		_next_sibling = other._next_sibling;
		return *this;
	}
	bool operator == ( Cacheable_Component & other )
	{
		if ( _num_var != other._num_var || _num_cl != other._num_cl || _key != other._key ) return false;
		if ( _bits == other._bits ) return true;  /// used for deciding if the component is equal to itself
		unsigned i, tmp, size = Bits_Size();
		if ( _infor._encoding == Difference_Cache_Encoding ) {
			if ( size != other.Bits_Size_Difference() ) return false;
		}
		tmp = _bits[size - 1];
		_bits[size - 1] = other._bits[size - 1] + 1;
		for ( i = 0; _bits[i] == other._bits[i]; i++ );
		_bits[size - 1] = tmp;
		return _bits[i] == other._bits[i];
	}
	uint64_t Key() const { return _key; }
	size_t Memory() const
	{
		size_t result_extra_memo = Extra_Memory<T>( _result, 0 );
		return sizeof(Cacheable_Component) + Bits_Size() * sizeof(unsigned) + result_extra_memo;
	}
protected:
	unsigned Bits_Max_Size() const
	{
		return ( _num_var * _infor._vcode_size + _num_cl * _infor._ccode_size - 1 ) / UNSIGNED_SIZE + 1 + 1;  /* ceil + extra 1 */
	}
	unsigned Bits_Size() const
	{
		unsigned result;
		switch ( _infor._encoding ) {
		case Simple_Cache_Encoding:
			result = Bits_Size_Simply();
			break;
		case Difference_Cache_Encoding:
			result = Bits_Size_Difference();
			break;
		default:
			result = UNSIGNED_UNDEF;
			cerr << "ERROR[Cacheable_Component]: invalid encoding!" << endl;
			exit( 1 );
		}
		return result;
	}
	unsigned Bits_Size_Simply() const { return ( _num_var * _infor._vcode_size + _num_cl * _infor._ccode_size - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */ }
	unsigned Bits_Size_Difference() const
	{
		unsigned var_diff = Read_Block( 0, _infor._vcode_size, _infor._vcode_mask );
		unsigned var_diff_code_size = Ceil_Log2( var_diff );
		unsigned num_var_bits = 2 * _infor._vcode_size + ( _num_var - 1 ) * var_diff_code_size;
		if ( _num_cl == 0 ) return ( num_var_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
		unsigned cl_diff = Read_Block( num_var_bits, _infor._ccode_size, _infor._ccode_mask );
		unsigned cl_diff_code_size = Ceil_Log2( cl_diff );
		return ( num_var_bits + 2 * _infor._ccode_size + ( _num_cl - 1 ) * cl_diff_code_size - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
	}
	unsigned New_Bits_Size( Cacheable_Component_Infor & new_infor ) const
	{
		assert( _infor._vcode_size <= new_infor._vcode_size && _infor._ccode_size <= new_infor._ccode_size );
		unsigned result;
		switch ( _infor._encoding ) {
		case Simple_Cache_Encoding:
			result = New_Bits_Size_Simple( new_infor );
			break;
		case Difference_Cache_Encoding:
			result = New_Bits_Size_Difference( new_infor );
			break;
		default:
			result = UNSIGNED_UNDEF;
			cerr << "ERROR[Cacheable_Component]: invalid encoding!" << endl;
			exit( 1 );
		}
		return result;
	}
	unsigned New_Bits_Size_Simple( Cacheable_Component_Infor & new_infor ) const
	{
		assert( _infor._vcode_size <= new_infor._vcode_size && _infor._ccode_size <= new_infor._ccode_size );
		assert( _infor._encoding == new_infor._encoding );
		unsigned num_var_bits = _num_var * new_infor._vcode_size;
		unsigned num_cl_bits = _num_cl * new_infor._ccode_size;
		return ( num_var_bits + num_cl_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
	}
	unsigned New_Bits_Size_Difference( Cacheable_Component_Infor & new_infor ) const
	{
		unsigned var_diff = Read_Block( 0, _infor._vcode_size, _infor._vcode_mask );
		unsigned var_diff_code_size = Ceil_Log2( var_diff );
		unsigned num_var_bits = 2 * new_infor._vcode_size + ( _num_var - 1 ) * var_diff_code_size;
		if ( _num_cl == 0 ) return ( num_var_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
		unsigned cl_diff = Read_Block( num_var_bits, _infor._ccode_size, _infor._ccode_mask );
		unsigned cl_diff_code_size = Ceil_Log2( cl_diff );
		unsigned num_cl_bits = 2 * new_infor._ccode_size + ( _num_cl - 1 ) * cl_diff_code_size;
		return ( num_var_bits + num_cl_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
	}
	void Write_Block( unsigned begin, unsigned block, unsigned code_size )
	{
		_bits[begin / UNSIGNED_SIZE] |= block << ( begin % UNSIGNED_SIZE );
		if ( code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) {
			_bits[begin / UNSIGNED_SIZE + 1] = block >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
	}
	unsigned Read_Block( unsigned begin, unsigned code_size, unsigned code_mask ) const
	{
		unsigned block = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & code_mask;
		if ( code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) {
			block |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & code_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		return block;
	}
	void Compute_Key()
	{
#ifdef ACTIVATE_CLHASH
		_key = hasher(_bits, Bits_Size());
#else
		unsigned i, size = Bits_Size();
		_key = PAIR( PAIR( _num_var, _num_cl), _bits[0] );
		for ( i = 1; i < size; i++ ) {
			_key = PAIR( _key, _bits[i] );
		}
#endif
	}
protected:
	CacheEntryID _parent = CacheEntryID::undef;
	CacheEntryID _first_child = CacheEntryID::undef;
	CacheEntryID _next_sibling = CacheEntryID::undef;
};

#ifdef ACTIVATE_CLHASH
template <typename T> clhasher Cacheable_Component<T>::hasher(UINT64_C(0x23a23cf5033c3c81),UINT64_C(0xb3816f6a2c68e530));
#endif

template <typename T> Cacheable_Component_Infor Cacheable_Component<T>::_infor;


}


#endif
