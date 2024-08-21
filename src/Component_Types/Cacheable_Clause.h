#ifndef _Cacheable_Clause_h_
#define _Cacheable_Clause_h_

#include "Component_Cache.h"


namespace KCBox {


struct Cacheable_Clause_Infor
{
	unsigned _lit_code_size;
	unsigned _lit_code_mask;  // used to recover
	void Init( Variable max_var )
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
	void Init( Variable max_var )
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


}


#endif
