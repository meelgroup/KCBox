#ifndef _Unified_Component_h_
#define _Unified_Component_h_

#include "Component.h"


namespace KCBox {


class Unified_Component: public Component
{
protected:
	vector<unsigned> _binary_clauses;
public:
	void Add_Binary_Clause( unsigned lit0, unsigned lit1 ) { _binary_clauses.push_back( lit0 ); _binary_clauses.push_back( lit1 ); }
	unsigned Binary_Clauses_First( unsigned i ) { return _binary_clauses[i + i]; }
	unsigned Binary_Clauses_Second( unsigned i ) { return _binary_clauses[i + i + 1]; }
	unsigned Binary_ClauseIDs_Size() { return _binary_clauses.size() / 2; }
	void Clear() { _varIDs.clear(); _binary_clauses.clear(); _clauseIDs.clear(); }
	void Verify_Orderness()
	{
	    assert( Vars_Size() > 1 );
	    assert( Binary_ClauseIDs_Size() + ClauseIDs_Size() > 0 );
	    for ( unsigned i = 1; i < _varIDs.size(); i++ ) {
            assert( _varIDs[i-1] < _varIDs[i] );
	    }
	    for ( unsigned i = 2; i < _binary_clauses.size(); i += 2 ) {
	        unsigned lit0 = _binary_clauses[i - 2];
	        unsigned lit1 = _binary_clauses[i - 1];
	        unsigned lit2 = _binary_clauses[i];
	        unsigned lit3 = _binary_clauses[i + 1];
            assert( lit0 < lit2 || ( lit0 == lit2 && lit1 < lit3 ) );
	    }
	    for ( unsigned i = 1; i < _clauseIDs.size(); i++ ) {
            assert( _clauseIDs[i-1] < _clauseIDs[i] );
	    }
	}
	void Display( ostream & out )
	{
		assert( _varIDs.size() >= 1 );
		unsigned i;
		out << "vars: ";
		for ( i = 0; i < _varIDs.size(); i++ ) out << _varIDs[i] << " ";
		out << endl;
		out << "binary clauses: ";
		for ( i = 0; i < _binary_clauses.size(); i += 2 ) {
			out << "(" << ExtLit( Literal( _binary_clauses[i] ) ) << ", " << ExtLit( Literal( _binary_clauses[i+1] ) ) << ") ";
		}
		out << endl;
		out << "clauses IDs: ";
		for ( i = 0; i < _clauseIDs.size(); i++ ) out << _clauseIDs[i] << " ";
		out << endl;
	}
};


template <typename T> class Unified_Component_Cache;

template <typename T> class Cacheable_Unified_Component
{
	friend class Unified_Component_Cache<T>;
protected:
	static Cacheable_Component_Infor _infor;   /// NOTE: for different Component_Cache, _infor is different, so please adjust it before use
	unsigned _num_var;  // NOTE: num_var is always greater than 1
	unsigned _num_bin_cl;
	unsigned _num_cl;
	unsigned * _bits;
	T _result;
public:
	Cacheable_Unified_Component(): _num_var( 0 ) {}
	Cacheable_Unified_Component( unsigned num_var, unsigned num_bin_cl, unsigned num_cl ): _num_var( num_var ), _num_bin_cl( num_bin_cl ), _num_cl( num_cl )
	{
		unsigned i, size = Bits_Size();
		_bits = new unsigned [size];
		for ( i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Init( unsigned num_var, unsigned num_bin_cl, unsigned num_cl )
	{
		unsigned i;
		if ( _num_var > 0 || num_var == 0 ) {
			cerr << "ERROR[Cacheable_Unified_Component]: no need to be initialized!" << endl;
			exit( 0 );
		}
		_num_var = num_var;
		_num_bin_cl = num_bin_cl;
		_num_cl = num_cl;
		unsigned size = Bits_Size();
		_bits = new unsigned [size];
		for ( i = 1; i < size; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Reset()
	{
		if ( _num_var != 0 ) {
			delete [] _bits;
			_num_var = 0;
		}
	}
	void Assign( Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var > 0 );
		assert( comp.Vars_Size() >= 2 );
		unsigned i, begin;
		unsigned vcode_size = _infor._vcode_size;
		unsigned ccode_size = _infor._ccode_size;
		_num_var = comp.Vars_Size();
		_num_bin_cl = 0;
		_num_cl = comp.ClauseIDs_Size();
		_bits[0] = comp.Vars(0) - Variable::start; /// NOTE: start from 0; _infor._vcode_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
		for ( i = 1, begin = vcode_size; i < _num_var; i++, begin += vcode_size ) {  // cache.vars is nonempty
			_bits[begin / UNSIGNED_SIZE] |= ( comp.Vars(i) - Variable::start ) << ( begin % UNSIGNED_SIZE );
			if ( vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = ( comp.Vars(i) - Variable::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		for ( i = 0; i < _num_cl; i++, begin += ccode_size ) {
			_bits[begin / UNSIGNED_SIZE] |= comp.ClauseIDs(i) << ( begin % UNSIGNED_SIZE );
			if ( ccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = comp.ClauseIDs(i) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
/*		cerr << "Memory Status: ";  // ToRemove
		Display_Memory_Status( cerr, _bits, Bits_Size() );  // ToRemove
		cerr << endl;  // ToRemove*/
	}
	void Assign( Unified_Component & comp )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var > 0 );
		assert( comp.Vars_Size() >= 2 );
		unsigned i, begin;
		unsigned vcode_size = _infor._vcode_size;
		unsigned bccode_size = _infor._vcode_size + 1;
		unsigned ccode_size = _infor._ccode_size;
		_num_var = comp.Vars_Size();
		_num_bin_cl = comp.Binary_ClauseIDs_Size();
		_num_cl = comp.ClauseIDs_Size();
		_bits[0] = comp.Vars(0) - Variable::start; /// NOTE: start from 0; _infor._vcode_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
		for ( i = 1, begin = vcode_size; i < _num_var; i++, begin += vcode_size ) {  // cache.vars is nonempty
			_bits[begin / UNSIGNED_SIZE] |= ( comp.Vars(i) - Variable::start ) << ( begin % UNSIGNED_SIZE );
			if ( vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = ( comp.Vars(i) - Variable::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		for ( i = 0; i < _num_bin_cl; i++ ) {  // cache.vars is nonempty
			_bits[begin / UNSIGNED_SIZE] |= ( comp.Binary_Clauses_First(i) - Literal::start ) << ( begin % UNSIGNED_SIZE );
			if ( bccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = ( comp.Binary_Clauses_First(i) - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
			begin += bccode_size;
			_bits[begin / UNSIGNED_SIZE] |= ( comp.Binary_Clauses_Second(i) - Literal::start ) << ( begin % UNSIGNED_SIZE );
			if ( bccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = ( comp.Binary_Clauses_Second(i) - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
			begin += bccode_size;
		}
		for ( i = 0; i < _num_cl; i++, begin += ccode_size ) {
			_bits[begin / UNSIGNED_SIZE] |= comp.ClauseIDs(i) << ( begin % UNSIGNED_SIZE );
			if ( ccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				_bits[begin / UNSIGNED_SIZE + 1] = comp.ClauseIDs(i) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
/*		cerr << "Memory Status: ";  // ToRemove
		Display_Memory_Status( cerr, _bits, Bits_Size() );  // ToRemove
		cerr << endl;  // ToRemove*/
	}
	void Read_Component( Unified_Component & comp )
	{
		assert( _infor._vcode_size > 0 && _infor._ccode_size > 0 );
		assert( _infor._vcode_size < UNSIGNED_SIZE );
		assert( _num_var >= 2 );
		unsigned i, begin, var, lit, lit2, cl;
		unsigned vcode_size = _infor._vcode_size;
		unsigned bccode_size = _infor._vcode_size + 1;
		unsigned ccode_size = _infor._ccode_size;
		unsigned vcode_mask = _infor._vcode_mask;
		unsigned bccode_mask = ( _infor._vcode_mask << 1 ) + 1;
		unsigned ccode_mask = _infor._ccode_mask;
		comp.Clear();
		var = _bits[0] & vcode_mask;
		comp.Add_Var( Variable( var + Variable::start ) );
		for ( i = 1, begin = vcode_size; i < _num_var; i++, begin += vcode_size ) {
			var = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & vcode_mask;
			if ( vcode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				var |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & vcode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			comp.Add_Var( Variable( var + Variable::start ) );
		}
		comp.Add_Var( Variable::undef );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp.Dec_Var();  /// pop Variable::undef
		for ( i = 0; i < _num_bin_cl; i++ ) {
			lit = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & bccode_mask;
			if ( bccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				lit |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & bccode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			begin += bccode_size;
			lit2 = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & bccode_mask;
			if ( bccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				lit2 |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & bccode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			begin += bccode_size;
			comp.Add_Binary_Clause( lit + Literal::start, lit2 + Literal::start );
		}
		for ( i = 0; i < _num_cl; i++, begin += ccode_size ) {
			cl = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & ccode_mask;
			if ( ccode_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				cl |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & ccode_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			comp.Add_ClauseID( cl );
		}
	}
	void Un_Assign()
	{
		unsigned i, size = Bits_Size();
		for ( i = 1; i < size; i++ ) _bits[i] = 0;
	}
	void operator = ( Cacheable_Unified_Component & other )  // NOTE: used in hash
	{
		_num_var = other._num_var;
		_num_bin_cl = other._num_bin_cl;
		_num_cl = other._num_cl;
		_bits = other._bits;
		_result = other._result; // node is not initialized is hash table
	}
	bool operator == ( Cacheable_Unified_Component & other )
	{
		if ( _num_var != other._num_var || _num_bin_cl != other._num_bin_cl || _num_cl != other._num_cl ) return false;
		unsigned i, tmp, size = Bits_Size();
		tmp = _bits[size - 1];
		_bits[size - 1] = other._bits[size - 1] + 1;
		for ( i = 0; _bits[i] == other._bits[i]; i++ );
		_bits[size - 1] = tmp;
		return _bits[i] == other._bits[i];
	}
	unsigned Key() const
	{
		unsigned i, size = Bits_Size();
		unsigned key = PAIR( PAIR( PAIR( _num_var, _num_bin_cl ), size), _bits[0] );
		for ( i = 1; i < size; i++ ) {
			key = PAIR( key, _bits[i] );
		}
		return key;
	}
	size_t Memory() const { return sizeof(Cacheable_Unified_Component) + Bits_Size() * sizeof(unsigned); }
protected:
    unsigned Bits_Size() const
    {
        unsigned num_bits = _num_var * _infor._vcode_size + _num_bin_cl * 2 * ( _infor._vcode_size + 1 ) + _num_cl * _infor._ccode_size;
        return ( num_bits - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */
    }
};


template <typename T> class Unified_Component_Cache
{
protected:
    Variable _max_var;
    unsigned _num_long_cl;  // the total number of long clauses
    Cacheable_Component_Infor _hit_infor;
    T _default_caching_value;
	Hash_Table<Cacheable_Unified_Component<T>> _pool;
	Hash_Cluster<Literal> _clause_set;
	Cacheable_Unified_Component<T> _big_cacheable_component;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
public:
	Unified_Component_Cache():
		_max_var( Variable::undef ), _pool( COMPONENT_CACHE_INIT_SIZE ), _clause_set( Variable::start + 1 )
	{
		_hash_memory = _pool.Memory();
	}
	Unified_Component_Cache( Variable max_var, unsigned num_binary_clauses, unsigned max_num_long_clauses, unsigned total_num_long_clauses, T default_value ):
		_max_var( max_var ), _num_long_cl( max_num_long_clauses ), _default_caching_value( default_value ), \
		_pool( COMPONENT_CACHE_INIT_SIZE ), _clause_set( max_var + 1 ), \
		_big_cacheable_component( max_var - Variable::start + 1, num_binary_clauses, max_num_long_clauses )
	{
		_hit_infor.Init( max_var, total_num_long_clauses );
		_hash_memory = _pool.Memory();
	}
	~Unified_Component_Cache()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		if ( _max_var != Variable::undef ) delete [] _big_cacheable_component._bits;
	}
	void Reset()
	{
		unsigned i;
		for ( i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Clear();
		_clause_set.Clear();
		_big_cacheable_component.Reset();
		_max_var = Variable::undef;
		_hash_memory = _pool.Memory();
	}
	void Init( Variable max_var, unsigned num_binary_clauses, unsigned max_num_long_clauses, unsigned total_num_long_clauses, T default_value )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Unified_Component_Cache]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_num_long_cl = max_num_long_clauses;
		_hit_infor.Init( max_var, total_num_long_clauses );
		Cacheable_Unified_Component<T>::_infor = _hit_infor;
		_default_caching_value = default_value;
		_clause_set.Clear();
		_clause_set.Enlarge_Fullset( max_var + 1 );  // no tautologies
		_big_cacheable_component.Init( NumVars( max_var ), num_binary_clauses, max_num_long_clauses );
	}
	void Init_Max_Var( Variable max_var )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Unified_Component_Cache]: clause set already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_clause_set.Clear();
		_clause_set.Enlarge_Fullset( NumVars( max_var ) );  // no tautologies
	}
	void Init_Rest( unsigned num_binary_clauses, unsigned max_num_long_clauses, unsigned total_num_long_clauses, T default_value )
	{
		if ( _max_var == Variable::undef ) {
			cerr << "ERROR[Unified_Component_Cache]: _max_var is not initialized!" << endl;
			exit( 0 );
		}
		_num_long_cl = max_num_long_clauses;
		_hit_infor.Init( _max_var, total_num_long_clauses );
		Cacheable_Unified_Component<T>::_infor = _hit_infor;
		_default_caching_value = default_value;
		_big_cacheable_component.Init( NumVars( _max_var ), num_binary_clauses, max_num_long_clauses );
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
	unsigned Num_Long_Clauses() const { return _clause_set.Size(); }
	const SortedSet<Literal> Long_Clauses( SetID id ) { return _clause_set.Elements( id ); }
	SetID Encode_Clause( Literal * lits, unsigned size ) { return _clause_set.Set( lits, size );  }
	unsigned Hit_Component( Component & comp )
	{
		Cacheable_Unified_Component<T>::_infor = _hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
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
	unsigned Hit_Component( Unified_Component & comp )
	{
		Cacheable_Unified_Component<T>::_infor = _hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
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
	void Erase( unsigned loc )
	{
		_hash_memory -= _pool[loc].Memory() - sizeof(Cacheable_Unified_Component<T>);
		delete [] _pool[loc]._bits;
		_pool.Erase( loc );
	}
	void Recover_Component( unsigned pos, Unified_Component & comp )  // NOTE: not recover comp.clauses
	{
		_pool[pos].Read_Component( comp );
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

template <typename T> Cacheable_Component_Infor Cacheable_Unified_Component<T>::_infor;


}


#endif
