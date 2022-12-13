#ifndef _Incremental_Component_BigInt_h_
#define _Incremental_Component_BigInt_h_

#include "Component.h"


namespace KCBox {


struct Cacheable_Clause_Infor
{
	unsigned _lit_code_size;
	unsigned _lit_code_mask;  // used to recover
	void Init( unsigned max_var )
	{
        _lit_code_size = 1 + Log_Ceil( max_var - Variable::start + 1 );  // one for sign
        _lit_code_mask = UNSIGNED_UNDEF >> ( UNSIGNED_SIZE - _lit_code_size );
    }
};

class Cacheable_Clause
{
	friend class Clause_Cache;
protected:
	static Cacheable_Clause_Infor _infor;   /// NOTE: for different Component_Cache, _infor is different, so please adjust it before use
	unsigned * _bits;
public:
	Cacheable_Clause(): _bits( nullptr ) {}
	Cacheable_Clause( unsigned size )
	{
		unsigned i, num = Bits_Size( size );
		_bits = new unsigned [num];
		for ( i = 1; i < num; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Init( unsigned size )
	{
		if ( _bits != nullptr ) {
			cerr << "ERROR[Cacheable_Clause]: no need to be initialized!" << endl;
			exit( 0 );
		}
		unsigned num = Bits_Size( size );
		_bits = new unsigned [num];
		for ( unsigned i = 1; i < num; i++ ) _bits[i] = 0;  // the first bit is not needed to be initialized
	}
	void Reset()
	{
		if ( _bits != nullptr ) {
			delete [] _bits;
			_bits = nullptr;
		}
	}
	unsigned Size() const { return _bits[0] & _infor._lit_code_mask; }
	Literal operator [] ( unsigned i )
	{
		unsigned begin = ( i + 1 ) * _infor._lit_code_size;  // the first slot is for size
		unsigned loc = begin / UNSIGNED_SIZE;
		unsigned shift = begin % UNSIGNED_SIZE;
		unsigned lit = ( _bits[loc] >> shift ) & _infor._lit_code_mask;
		if ( shift + _infor._lit_code_size > UNSIGNED_SIZE ) {
			lit |= ( _bits[loc + 1] << ( UNSIGNED_SIZE - shift ) ) & _infor._lit_code_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
		}
		return Literal( lit + Literal::start );
	}
	void Assign( Clause & clause )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
    {
        ASSERT( 0 < _infor._lit_code_size && _infor._lit_code_size < UNSIGNED_SIZE );
        ASSERT( _bits != nullptr );
        ASSERT( clause.Size() >= 2 );
        unsigned i, begin;
        _bits[0] = clause.Size(); /// NOTE: start from 0; _infor._lit_code_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
        for ( i = 0, begin = _infor._lit_code_size; i < clause.Size(); i++, begin += _infor._lit_code_size ) {  // cache.vars is nonempty
            _bits[begin / UNSIGNED_SIZE] |= ( clause[i] - Literal::start ) << ( begin % UNSIGNED_SIZE );
            if ( _infor._lit_code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
                _bits[begin / UNSIGNED_SIZE + 1] = ( clause[i] - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
        }
    }
	void Assign( Literal lit, Literal lit2 )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
    {
        ASSERT( 0 < _infor._lit_code_size && _infor._lit_code_size < UNSIGNED_SIZE );
        ASSERT( _bits != nullptr );
        _bits[0] = 2; /// NOTE: start from 0; _infor._lit_code_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
        unsigned begin = _infor._lit_code_size;
		_bits[begin / UNSIGNED_SIZE] |= ( lit - Literal::start ) << ( begin % UNSIGNED_SIZE );
		if ( _infor._lit_code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
			_bits[begin / UNSIGNED_SIZE + 1] = ( lit - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
		begin += _infor._lit_code_size;
		_bits[begin / UNSIGNED_SIZE] |= ( lit2 - Literal::start ) << ( begin % UNSIGNED_SIZE );
		if ( _infor._lit_code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
			_bits[begin / UNSIGNED_SIZE + 1] = ( lit2 - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
    }
	void Assign( Literal * lits, unsigned size )  // NOTE: #*this# was Un_Assign; #comp# has at least two variables
    {
        ASSERT( 0 < _infor._lit_code_size && _infor._lit_code_size < UNSIGNED_SIZE );
        ASSERT( _bits != nullptr );
        ASSERT( size >= 2 );
        unsigned i, begin;
        _bits[0] = size; /// NOTE: start from 0; _infor._lit_code_size may be greater than UNSIGNED_SIZE / 2, so cannot start from 1
        for ( i = 0, begin = _infor._lit_code_size; i < size; i++, begin += _infor._lit_code_size ) {  // cache.vars is nonempty
            _bits[begin / UNSIGNED_SIZE] |= ( lits[i] - Literal::start ) << ( begin % UNSIGNED_SIZE );
            if ( _infor._lit_code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
                _bits[begin / UNSIGNED_SIZE + 1] = ( lits[i] - Literal::start ) >> ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE );  // NOTE: a == ( a >> UNSIGNED_SIZE )
        }
    }
	void Un_Assign()
	{
		unsigned size = Size();
		unsigned num = Bits_Size( size );
		for ( unsigned i = 1; i < num; i++ ) _bits[i] = 0;
	}
	void Read_Clause( Big_Clause & clause )
	{
        ASSERT( 0 < _infor._lit_code_size && _infor._lit_code_size < UNSIGNED_SIZE );
        ASSERT( _bits != nullptr );
		unsigned i, begin;
		unsigned size = Size();
		ASSERT( size >= 2 );
		clause.Resize( size );
		for ( i = 0, begin = _infor._lit_code_size; i < size; i++, begin += _infor._lit_code_mask ) {
			unsigned lit = ( _bits[begin / UNSIGNED_SIZE] >> ( begin % UNSIGNED_SIZE ) ) & _infor._lit_code_mask;
			if ( _infor._lit_code_size > UNSIGNED_SIZE - begin % UNSIGNED_SIZE )
				lit |= ( _bits[begin / UNSIGNED_SIZE + 1] << ( UNSIGNED_SIZE - begin % UNSIGNED_SIZE ) ) & _infor._lit_code_mask; // NOTE: a == ( a >> UNSIGNED_SIZE )
			clause[i] = Literal( lit + Literal::start );
		}
	}
	void operator = ( Cacheable_Clause & other )  // NOTE: used in hash
	{
		_bits = other._bits;
	}
	bool operator == ( Cacheable_Clause & other )
	{
		unsigned size = Size();
		unsigned size2 = other.Size();
		if ( size != size2 ) return false;
		unsigned num = Bits_Size( size );
		unsigned i, tmp;
		tmp = _bits[num - 1];
		_bits[num - 1] = other._bits[num - 1] + 1;
		for ( i = 0; _bits[i] == other._bits[i]; i++ );
		_bits[num - 1] = tmp;
		return _bits[i] == other._bits[i];
	}
	unsigned Key() const
	{
		unsigned num = Bits_Size( Size() );
		unsigned key = _bits[0];
		for ( unsigned i = 1; i < num; i++ ) {
			key = PAIR( key, _bits[i] );
		}
		return key;
	}
	size_t Memory() const
	{
		unsigned num = Bits_Size( Size() );
		return sizeof(Cacheable_Clause) + num * sizeof(unsigned);
	}
protected:
    unsigned Bits_Size( unsigned size ) const { return ( ( size + 1 ) * _infor._lit_code_size - 1 ) / UNSIGNED_SIZE + 1;  /* ceil */ }
};


#ifndef DEBUG_MODE
#define CLAUSE_CACHE_INIT_SIZE 256
#else
#define CLAUSE_CACHE_INIT_SIZE LARGE_HASH_TABLE
#endif

class Clause_Cache
{
protected:
	Variable _max_var;
	Cacheable_Clause_Infor _hit_infor;
	Hash_Table<Cacheable_Clause> _pool;
	Cacheable_Clause _big_cacheable_clause;
	size_t _hash_memory;  // used to record the number of used bytes for storing components
public:
	Clause_Cache(): _max_var( Variable::undef ), _pool( CLAUSE_CACHE_INIT_SIZE )
	{
		_hash_memory = _pool.Memory();
	}
	Clause_Cache( Variable max_var ) :
		_max_var( max_var ), _pool( CLAUSE_CACHE_INIT_SIZE ), _big_cacheable_clause( NumVars( max_var ) )
	{
		_hit_infor.Init( max_var );
		_hash_memory = _pool.Memory();
	}
	~Clause_Cache()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		if ( _max_var != Variable::undef ) delete [] _big_cacheable_clause._bits;
	}
	void Reset()
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			delete [] _pool[i]._bits;
		}
		_pool.Clear();
		_big_cacheable_clause.Reset();
		_max_var = Variable::undef;
		_hash_memory = _pool.Memory();
	}
	void Init( unsigned max_var )
	{
		if ( _max_var != Variable::undef ) {
			cerr << "ERROR[Clause_Cache]: already initialized!" << endl;
			exit( 0 );
		}
		_max_var = max_var;
		_hit_infor.Init( max_var );
		Cacheable_Clause::_infor = _hit_infor;
		_big_cacheable_clause.Init( NumVars( _max_var ) );
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
	unsigned Hit_Binary_Clause( Literal lit, Literal lit2 )
	{
		Cacheable_Clause::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		_big_cacheable_clause.Assign( lit, lit2 );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_clause, _hash_memory );
		if ( pos == old_cache_size ) {
			unsigned num = _big_cacheable_clause.Bits_Size( 2 );
			_pool[pos]._bits = new unsigned [num];
			_pool[pos]._bits[0] = _big_cacheable_clause._bits[0];  // has at least one 4-bytes
			for ( i = 1; i < num; i++ ) _pool[pos]._bits[i] = _big_cacheable_clause._bits[i];
		}
		_big_cacheable_clause.Un_Assign();
		return pos;
	}
	unsigned Hit_Clause( Clause & clause )
	{
		Cacheable_Clause::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		_big_cacheable_clause.Assign( clause );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_clause, _hash_memory );
		if ( pos == old_cache_size ) {
			unsigned num = _big_cacheable_clause.Bits_Size( clause.Size() );
			_pool[pos]._bits = new unsigned [num];
			_pool[pos]._bits[0] = _big_cacheable_clause._bits[0];  // has at least one 4-bytes
			for ( i = 1; i < num; i++ ) _pool[pos]._bits[i] = _big_cacheable_clause._bits[i];
		}
		_big_cacheable_clause.Un_Assign();
		return pos;
	}
	unsigned Hit_Clause( Literal * lits, unsigned size )
	{
		Cacheable_Clause::_infor = _hit_infor;  /// NOTE: for different Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		_big_cacheable_clause.Assign( lits, size );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_clause, _hash_memory );
		if ( pos == old_cache_size ) {
			unsigned num = _big_cacheable_clause.Bits_Size( size );
			_pool[pos]._bits = new unsigned [num];
			_pool[pos]._bits[0] = _big_cacheable_clause._bits[0];  // has at least one 4-bytes
			for ( i = 1; i < num; i++ ) _pool[pos]._bits[i] = _big_cacheable_clause._bits[i];
		}
		_big_cacheable_clause.Un_Assign();
		return pos;
	}
	bool Hit_Successful() { return _pool.Hit_Successful(); }
	void Read_Clause( unsigned loc, Big_Clause & clause ) { _pool[loc].Read_Clause( clause ); }
	void Erase( unsigned loc )
	{
		_hash_memory -= _pool[loc].Memory() - sizeof(Cacheable_Clause);
		delete [] _pool[loc]._bits;
		_pool.Erase( loc );
	}
	void Display( ostream & out )
	{
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
			out << i << ": ";
			Cacheable_Clause & cclause = _pool[i];
			out << cclause[0] << " " << cclause[1] << " ";
			for ( unsigned j = 2; j < cclause.Size(); j++ ) {
				out << cclause[j] << " ";
			}
			out << "0" << endl;
		}
	}
};


class Cacheable_Component_BigInt: public Cacheable_Component<BigInt>
{
	friend class Incremental_Component_Cache_BigInt;
protected:
public:
	Cacheable_Component_BigInt() {}
	Cacheable_Component_BigInt( unsigned num_var, unsigned num_cl ): Cacheable_Component<BigInt>( num_var, num_cl ) {}
	size_t Memory() const
	{
		size_t result_extra_memo = _result.Memory() - sizeof(BigInt);
		return sizeof(Cacheable_Component_BigInt) + Bits_Size() * sizeof(unsigned) + result_extra_memo;
	}
protected:
};

class Incremental_Component_Cache_BigInt
{
protected:
	Variable _max_var;
	unsigned _num_long_cl;  // the total number of long clauses
	Cacheable_Component_Infor _hit_infor;
	BigInt _default_caching_value;  // for IBCP, we could leave one component without getting result, thus use this notation
//	Hash_Table<Cacheable_Component_BigInt> _pool;
	Large_Hash_Table<Cacheable_Component_BigInt> _pool;
	Cacheable_Component_BigInt _big_cacheable_component;
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
		_original_binary_clauses.Clear();
		_other_clauses.Reset();
		_hit_count = _hit_failed_count = 0;
	}
	void Init( unsigned max_var, unsigned num_long_clause, BigInt default_value )
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
		_big_cacheable_component.Init( max_var - Variable::start + 1, num_long_clause );
		_original_binary_clauses.Clear();
		_original_binary_clauses.Enlarge_Fullset( max_var );
		_other_clauses.Clear();
		_other_clauses.Init( max_var );  // no tautologies
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
	void Clear_Half( vector<size_t> & kept_locs )
	{
		vector<bool> seen( _pool.Size(), false );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			seen[kept_locs[i]] = true;
		}
		unsigned old_size = kept_locs.size();
		if ( true ) {  // ToModify
			unsigned i = 0;
			for ( ; i < _pool.Size() / 2; i++ ) {
				if ( !seen[i] ) delete [] _pool[i]._bits;
			}
			for ( ; i < _pool.Size(); i++ ) {
				if ( !seen[i] ) kept_locs.push_back( i );
			}
		}
		else {
			for ( unsigned i = 0; i < _pool.Size(); i++ ) {
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
	unsigned Size() const { return _pool.Size(); }
	unsigned Capacity() const { return _pool.Capacity(); }
	void Reserve( size_t capacity )
	{
		_hash_memory -= _pool.Capacity() * sizeof(Cacheable_Component_BigInt);
		_pool.Reserve( capacity );
		_hash_memory += _pool.Capacity() * sizeof(Cacheable_Component_BigInt);
	}
	void Shrink_To_Fit()
	{
		_pool.Shrink_To_Fit();
		_hash_memory = _pool.Memory();
	}
	unsigned Memory() const { return _hash_memory; }
	unsigned Memory_Show()
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
	unsigned Hit_Component( Component & comp )
	{
		Cacheable_Component<BigInt>::_infor = _hit_infor;  /// NOTE: for different Unified_Component_Cache, Cacheable_Component::_infor is different, so update Cacheable_Component::_infor before Hit
		if ( comp.ClauseIDs_Size() > _num_long_cl ) {
			_num_long_cl = comp.ClauseIDs_Size();
			_big_cacheable_component.Update_Bits( NumVars( _max_var), _num_long_cl );
		}
		_big_cacheable_component.Assign( comp );  /// this calling needs to use the right _infor.vcode_size and _infor.ccode_size
		unsigned i, old_cache_size = _pool.Size();
		unsigned pos = _pool.Hit( _big_cacheable_component, _hash_memory );
		_hit_count++;
		if ( pos == old_cache_size ) {
			_hit_failed_count++;
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
	void Erase( unsigned loc )
	{
		if ( loc == _pool.Size() - 1 ) {
			_hash_memory -= _pool[loc].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += sizeof(Cacheable_Component_BigInt);
		}
		else {
			_hash_memory -= _pool[loc].Memory();
			_hash_memory -= _pool[_pool.Size() - 1].Memory();
			delete [] _pool[loc]._bits;
			_pool.Erase( loc );
			_hash_memory += _pool[loc].Memory();
			_hash_memory += sizeof(Cacheable_Component_BigInt);
		}
	}
	BigInt Read_Result( unsigned loc ) { return _pool[loc]._result; }
	void Write_Result( unsigned loc, const BigInt result )
	{
		_hash_memory -= _pool[loc]._result.Memory();
		_pool[loc]._result = result;
		_hash_memory += _pool[loc]._result.Memory();  /// result's memory might not be equal to that of pool[loc]._result
	}
	double Duplicate_Rate()
	{
		vector<BigInt> elems;
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
		Cacheable_Component<BigInt>::_infor = _hit_infor;  /// update Cacheable_Component::_infor before Update
		_big_cacheable_component.Update_Bits( NumVars( _max_var ), _num_long_cl );
		for ( unsigned i = 0; i < _pool.Size(); i++ ) {
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
};


}


#endif
