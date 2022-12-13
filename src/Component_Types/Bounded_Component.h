#ifndef _Bounded_Component_h_
#define _Bounded_Component_h_

#include "Component.h"


namespace KCBox {


#define BOUNDED_COMPONENT_CODE_BITS  10
#define BOUNDED_COMPONENT_VAR_BOUND  ( BOUNDED_COMPONENT_CODE_BITS * ULLONG_SIZE )
#define BOUNDED_COMPONENT_LONG_CLAUSE_BOUND  ( 2 * BOUNDED_COMPONENT_CODE_BITS * ULLONG_SIZE )
#define BOUNDED_TREEWIDTH  32


template <typename T> class Bounded_Component_Cache;

template <typename T> class Cacheable_Bounded_Component
{
	friend class Bounded_Component_Cache<T>;
protected:
	ullong _vars_bits[BOUNDED_COMPONENT_CODE_BITS];  // NOTE: BOUNDED_COMPONENT_CODE_BITS * ULLONG_SIZE must be not greater than 1024, and otherwise double will overflow
	ullong _cls_bits[2 * BOUNDED_COMPONENT_CODE_BITS];
	T _result;
public:
	Cacheable_Bounded_Component() {}
	void Init()
	{
		unsigned i;
		_vars_bits[0] = _cls_bits[0] = _cls_bits[1] = ullong(0);
		for ( i = 1; i < BOUNDED_COMPONENT_CODE_BITS; i++ ) {
        		_vars_bits[i] = _cls_bits[i + i] = _cls_bits[i + i + 1] = ullong(0);
		}
		_result = -1;
	}
	void Assign( Component & comp )
	{
		assert( 1 < comp.Vars_Size() && comp.Vars_Size() <= BOUNDED_COMPONENT_VAR_BOUND );
		assert( comp.ClauseIDs_Size() <= BOUNDED_COMPONENT_LONG_CLAUSE_BOUND );
		unsigned i;
		unsigned num_var = comp.Vars_Size();
		unsigned num_cl = comp.ClauseIDs_Size();
		Init();
		assert( comp.Vars(0) < BOUNDED_COMPONENT_VAR_BOUND );
		assert( comp.Vars(1) < BOUNDED_COMPONENT_VAR_BOUND );
		_vars_bits[comp.Vars(0) / ULLONG_SIZE] |= ullong(1) << ( comp.Vars(0) % ULLONG_SIZE ); // start from 0
		_vars_bits[comp.Vars(1) / ULLONG_SIZE] |= ullong(1) << ( comp.Vars(1) % ULLONG_SIZE );
		for ( i = 2; i < num_var; i++ ) { // cache.vars is nonempty, and discard the last element max_var + 1
			assert( comp.Vars( i ) < BOUNDED_COMPONENT_VAR_BOUND );
			_vars_bits[comp.Vars(i) / ULLONG_SIZE] |= ullong(1) << ( comp.Vars(i) % ULLONG_SIZE );
		}
		for ( i = 0; i < num_cl; i++ ) {
			assert( comp.ClauseIDs(i) < BOUNDED_COMPONENT_LONG_CLAUSE_BOUND );
			_cls_bits[comp.ClauseIDs(i) / ULLONG_SIZE] |= ullong(1) << ( comp.ClauseIDs(i) % ULLONG_SIZE );
		}
	}
	bool operator == ( Cacheable_Bounded_Component & other )
	{
	    unsigned i;
	    bool tmp = ( _cls_bits[0] == other._cls_bits[0] ) && ( _cls_bits[1] == other._cls_bits[1] );
	    bool same = ( _vars_bits[0] == other._vars_bits[0] ) && tmp;
	    for ( i = 1; i < BOUNDED_COMPONENT_CODE_BITS; i++ ) {
            tmp = ( _cls_bits[i + i] == other._cls_bits[i + i] ) && ( _cls_bits[i + i + 1] == other._cls_bits[i + i + 1] );
            same = same && ( _vars_bits[i] == other._vars_bits[i] ) && tmp;
	    }
		return same;
	}
	unsigned Key() const
	{
	    unsigned i, key = PAIR( _vars_bits[0], PAIR( _cls_bits[0], _cls_bits[1] ) );
	    for ( i = 1; i < BOUNDED_COMPONENT_CODE_BITS; i++ ) {
            key = PAIR( key, PAIR( _vars_bits[i], PAIR( _cls_bits[i + i], _cls_bits[i + i + 1] ) ) );
	    }
	    return key;
	}
	void Display( ostream & fout )
	{
	    unsigned i;
	    fout << "<" << _vars_bits[0];
	    for ( i = 1; i < BOUNDED_COMPONENT_CODE_BITS; i++ ) {
            fout << ", " << _vars_bits[i];
	    }
	    fout << "; " << _cls_bits[0] << ", " << _cls_bits[1];
	    for ( i = 1; i < BOUNDED_COMPONENT_CODE_BITS; i++ ) {
            fout << ", " << _cls_bits[i + i] << ", " << _cls_bits[i + i + 1];
	    }
	    fout << ">" << endl;
	}
};

template <typename T> class Bounded_Component_Cache
{
protected:
	Hash_Table<Cacheable_Bounded_Component<T>> pool;
	Cacheable_Bounded_Component<T> comp_code;
public:
	Bounded_Component_Cache(): pool( 40000 ) {}
	void Clear() { pool.Clear(); }
	unsigned Size() const { return pool.Size(); }
	unsigned Memory() const { return pool.Capacity() * ( BOUNDED_COMPONENT_VAR_BOUND + BOUNDED_COMPONENT_LONG_CLAUSE_BOUND ) / 8; }
	unsigned Hit_Component( Component & comp )
	{
		comp_code.Assign( comp );
		comp.caching_loc = pool.Hit( comp_code );
		return comp.caching_loc;
	}
	bool Result_Exists( unsigned pos ) { return pool[pos]._result >= 0; }
	T Read_Result( unsigned pos ) { return pool[pos]._result; }
	void Write_Result( unsigned pos, const T result ) { pool[pos]._result = result; }
};


}


#endif
