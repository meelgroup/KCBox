#ifndef _Component_h_
#define _Component_h_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Template_Library/BigNum.h"
#include "../Primitive_Types/CNF_Formula.h"


namespace KCBox {


class Component
{
protected:
	vector<unsigned> _varIDs;
	vector<unsigned> _clauseIDs;  // denote the ID of clauses
public:
	unsigned caching_loc;
	unsigned Vars_Size() const { return _varIDs.size(); }
	unsigned ClauseIDs_Size() const { return _clauseIDs.size(); }
	void Vars_Resize( unsigned newsize ) { _varIDs.resize( newsize ); }
	void ClauseIDs_Resize( unsigned newsize ) { _clauseIDs.resize( newsize ); }
	unsigned Capacity() const { return _varIDs.capacity() + _clauseIDs.capacity(); }
	void Add_Var( Variable var ) { _varIDs.push_back( var ); }
	void Dec_Var() { _varIDs.pop_back(); }
	void Add_ClauseID( unsigned clause ) { _clauseIDs.push_back( clause ); }
	const vector<unsigned> & VarIDs() { return _varIDs; }
	Variable Vars( unsigned i ) { return Variable( _varIDs[i] ); }
	unsigned ClauseIDs( unsigned i ) { return _clauseIDs[i]; }
	vector<unsigned>::const_iterator VarIDs_Begin() { return _varIDs.cbegin(); }
	vector<unsigned>::const_iterator VarIDs_End() { return _varIDs.cend(); }
	vector<unsigned>::const_iterator ClauseIDs_Begin() { return _clauseIDs.cbegin(); }
	vector<unsigned>::const_iterator ClauseIDs_End() { return _clauseIDs.cend(); }
	void Clear() { _varIDs.clear(); _clauseIDs.clear(); }
	void Clear_Vars() { _varIDs.clear(); }
	void Clear_ClauseIDs() { _clauseIDs.clear(); }
	bool Search_Var( Variable var ) { return Search_Exi_Nonempty( _varIDs, unsigned(var) ); }
	bool Search_ClauseID( unsigned cl ) { return Search_Exi_Nonempty( _clauseIDs, cl ); }
	void Sort( QSorter & sorter ) { sorter.Sort( _varIDs ); sorter.Sort( _clauseIDs ); }
	void Sort_Vars( QSorter & sorter ) { sorter.Sort( _varIDs ); }
	void Sort_ClauseIDs( QSorter & sorter ) { sorter.Sort( _clauseIDs ); }
	bool Trivial( const unsigned bound ) { return _varIDs.size() - 1 <= bound && _clauseIDs.size() <= 2 * bound; }
	void Swap( Component & other ) { _varIDs.swap( other._varIDs ); _clauseIDs.swap( other._clauseIDs ); swap( caching_loc, other.caching_loc ); }
	void Swap_VarIDs( Component & other ) { _varIDs.swap( other._varIDs ); }
	void Swap_ClauseIDs( vector<unsigned> & clause_IDs ) { _clauseIDs.swap( clause_IDs ); }
	bool operator == ( Component & other )
	{
		if ( _varIDs.size() != other._varIDs.size() || _clauseIDs.size() != other._clauseIDs.size() ) return false;
		for ( unsigned i = 0; i < _varIDs.size(); i++ ) {
			if ( _varIDs[i] != other._varIDs[i] ) return false;
		}
		for ( unsigned i = 0; i < _clauseIDs.size(); i++ ) {
			if ( _clauseIDs[i] != other._clauseIDs[i] ) return false;
		}
		return true;
	}
	bool operator != ( Component & other )
	{
		if ( _varIDs.size() != other._varIDs.size() || _clauseIDs.size() != other._clauseIDs.size() ) return true;
		for ( unsigned i = 0; i < _varIDs.size(); i++ ) {
			if ( _varIDs[i] != other._varIDs[i] ) return true;
		}
		for ( unsigned i = 0; i < _clauseIDs.size(); i++ ) {
			if ( _clauseIDs[i] != other._clauseIDs[i] ) return true;
		}
		return false;
	}
	void Display( ostream & fout )
	{
		assert( _varIDs.size() >= 1 );
		unsigned i;
		fout << "varIDs: ";
		for ( i = 0; i < _varIDs.size(); i++ ) fout << _varIDs[i] << " ";
		fout << endl;
		fout << "clauseIDs: ";
		for ( i = 0; i < _clauseIDs.size(); i++ ) fout << _clauseIDs[i] << " ";
		fout << endl;
	}
};


struct Cacheable_Component_Infor
{
	unsigned _vcode_size;
	unsigned _ccode_size;
	unsigned _vcode_mask;  // used to recover
	unsigned _ccode_mask;  // used to recover
	void Init( unsigned max_var, unsigned num_long_clauses )
	{
        _vcode_size = Log_Ceil( max_var - Variable::start + 1 );
        _ccode_size = num_long_clauses <= 2 ? 1 : Log_Ceil( num_long_clauses );  /// NOTE: a zero-bit ccode may lead to a wrong num_clause
        _vcode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _vcode_size );
        _ccode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _ccode_size );
    }
    void Extend_CCode( unsigned inc )
    {
    	_ccode_size += inc;
    	_ccode_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _ccode_size );
    }
    unsigned Max_Num_Clauses() { return 1 << _ccode_size; }
};


template <typename T> class Component_Cache;
template <typename T> class Incremental_Component_Cache;

template <typename T> class Cacheable_Component
{
	friend class Component_Cache<T>;
	friend class Incremental_Component_Cache<T>;
	friend class Incremental_Component_Cache_BigInt;
protected:
	static Cacheable_Component_Infor _infor;   /// NOTE: for different Component_Cache, _infor is different, so please adjust it before use
	unsigned _num_var;  // NOTE: _num_var is always greater than 1
	unsigned _num_cl;
	unsigned * _bits;
	unsigned _key;
	T _result;
public:
	Cacheable_Component(): _num_var( 0 ) {}
	Cacheable_Component( unsigned num_var, unsigned num_cl ): _num_var( num_var ), _num_cl( num_cl )
	{
		unsigned i, size = Bits_Size();
		_bits = new unsigned [size];
		for ( i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Init( unsigned num_var, unsigned num_cl )
	{
		if ( _num_var > 0 || num_var == 0 ) {
			cerr << "ERROR[Cacheable_Component]: no need to be initialized!" << endl;
			exit( 0 );
		}
		_num_var = num_var;
		_num_cl = num_cl;
		unsigned size = Bits_Size();
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
		unsigned size = Bits_Size();
		_bits = new unsigned [size];
		for ( unsigned i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Assign( Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
    {
        ASSERT( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
        ASSERT( _infor._vcode_size < UNSIGNED_SIZE );
        ASSERT( _num_var > 0 );
        ASSERT( comp.Vars_Size() >= 2 );
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
	void Read_Rough_Component( Component & comp )  // not read _clauses
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var >= 2 );
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
	void operator = ( Cacheable_Component & other )  // NOTE: used in hash
	{
		_num_var = other._num_var;
		_num_cl = other._num_cl;
		_bits = other._bits;
		_key = other._key;
		_result = other._result; // node is not initialized is hash table
	}
	bool operator == ( Cacheable_Component & other )
	{
		if ( _num_var != other._num_var || _num_cl != other._num_cl || _key != other._key ) return false;
		if ( _bits == other._bits ) return true;  /// used for deciding if the component is equal to itself
		unsigned i, tmp, size = Bits_Size();
		tmp = _bits[size - 1];
		_bits[size - 1] = other._bits[size - 1] + 1;
		for ( i = 0; _bits[i] == other._bits[i]; i++ );
		_bits[size - 1] = tmp;
		return _bits[i] == other._bits[i];
	}
	unsigned Key() const { return _key; }
	size_t Memory() const { return sizeof(Cacheable_Component) + Bits_Size() * sizeof(unsigned); }
protected:
    unsigned Bits_Size() const { return ( _num_var * _infor._vcode_size + _num_cl * _infor._ccode_size - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */ }
	void Compute_Key()
	{
		unsigned i, size = Bits_Size();
		_key = PAIR( PAIR( _num_var, _num_cl), _bits[0] );
		for ( i = 1; i < size; i++ ) {
			_key = PAIR( _key, _bits[i] );
		}
	}
};


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
	Hash_Table<Cacheable_Component<T>> _pool;
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
	unsigned Memory() const { return _hash_memory; }
	unsigned Hit_Component( Component & comp )
	{
		Cacheable_Component<T>::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
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
		_hash_memory -= _pool[loc].Memory() - sizeof(Cacheable_Component<T>);
		delete [] _pool[loc]._bits;
		_pool.Erase( loc );
	}
	T Read_Result( unsigned pos ) { return _pool[pos]._result; }
	void Write_Result( unsigned pos, const T result ) { _pool[pos]._result = result; }
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
};

template <typename T> Cacheable_Component_Infor Cacheable_Component<T>::_infor;


}


#endif
