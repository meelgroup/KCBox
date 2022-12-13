#ifndef _Assignment_
#define _Assignment_

#include "CNF_Formula.h"


namespace KCBox {


class lbool
{
protected:
	int8_t _val;
public:
    lbool(): _val( -1 ) { }
    explicit lbool( bool v ) : _val( v ) {}
    lbool( const lbool &b ) : _val( b._val ) {}
	lbool & operator = ( lbool b ) { _val = b._val; return *this; }
	lbool & operator = ( bool v ) { _val = v; return *this; }
	bool operator == (const lbool &other) const { return _val == other._val; }
	bool operator != (const lbool &other) const { return _val != other._val; }
	bool operator == (const bool v) const { return _val == v; }
	bool operator != (const bool v) const { return _val != v; }
	operator int8_t () const { return _val; }
	const static lbool unknown;
};

class Assignment
{
protected:
	Variable _max_var; // max_var == UNSIGNED_UNDEF means Preprocessor is reset
	lbool * _assignment; // The last bit is used to mark the variable not assigned
	lbool _value_backup;
public:
	Variable Max_Var() { return _max_var; }
protected:
	Assignment(): _max_var( Variable::undef ) {}
	~Assignment() { if ( _max_var != Variable::undef ) Free_Auxiliary_Memory(); }
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var )
	{
		if ( _max_var == max_var ) return;
		if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
		_max_var = max_var;
		_assignment = new lbool [_max_var + 2];  // The last bit is used to mark the variable not assigned
	}
	void Free_Auxiliary_Memory() { delete [] _assignment; }
	void Label_Value( Variable var, bool val ) { _value_backup = _assignment[var];  _assignment[var] = val; }
	void Label_Value( Literal lit ) { _value_backup = _assignment[lit.Var()];  _assignment[lit.Var()] = lit.Sign(); }
	void Un_Label_Value( Variable var ) { _assignment[var] = _value_backup; }
	void Un_Label_Value( Literal lit ) { _assignment[lit.Var()] = _value_backup; }
	bool Var_Decided( Variable var ) { return _assignment[var] != lbool::unknown; }
	bool Var_Undecided( Variable var ) { return _assignment[var] == lbool::unknown; }
	bool Lit_Decided( Literal lit ) { return _assignment[lit.Var()] != lbool::unknown; }
	bool Lit_Undecided( Literal lit ) { return _assignment[lit.Var()] == lbool::unknown; }
	bool Lit_SAT( Literal lit ) { return _assignment[lit.Var()] == lit.Sign(); }
	bool Lit_UNSAT( Literal lit ) { return _assignment[lit.Var()] == !lit.Sign(); }
	bool Clause_SAT( Clause & clause )
	{
		unsigned i;
		Label_Value( clause.Last_Lit().Var(), clause.Last_Lit().Sign() );  // label last literal as SAT
		for ( i = 0; !Lit_SAT( clause[i] ); i++ ) {}
		Un_Label_Value( clause.Last_Lit().Var() );
		return Lit_SAT( clause[i] );
	}
	bool Clause_3_SAT( Clause & clause ) { return Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) || Lit_SAT( clause[2] ); }
	bool Clause_4_SAT( Clause & clause ) { return Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) || Lit_SAT( clause[2] ) || Lit_SAT( clause[3] ); }
	bool Clause_GE_3_SAT( Clause & clause )
	{
		if ( Lit_SAT( clause[0] ) ) return true;
		unsigned i;
		Label_Value( clause.Last_Lit().Var(), clause.Last_Lit().Sign() );  // label last literal as SAT
		for ( i = 1; !Lit_SAT( clause[i] ); i++ ) {}
		Un_Label_Value( clause.Last_Lit().Var() );
		return Lit_SAT( clause[i] );
	}
	bool Clause_GE_4_SAT( Clause & clause )
	{
		if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) return true;
		unsigned i;
		Label_Value( clause.Last_Lit().Var(), clause.Last_Lit().Sign() );  // label last literal as SAT
		for ( i = 2; !Lit_SAT( clause[i] ); i++ ) {}
		Un_Label_Value( clause.Last_Lit().Var() );
		return Lit_SAT( clause[i] );
	}
	bool Clause_GE_5_SAT( Clause & clause )
	{
		if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) || Lit_SAT( clause[2] ) ) return true;
		unsigned i;
		Label_Value( clause.Last_Lit().Var(), clause.Last_Lit().Sign() );  // label last literal as SAT
		for ( i = 3; !Lit_SAT( clause[i] ); i++ ) {}
		Un_Label_Value( clause.Last_Lit().Var() );
		return Lit_SAT( clause[i] );
	}
	bool Clause_GE_3_SAT( Big_Clause & clause )
	{
		if ( Lit_SAT( clause[0] ) ) return true;
		unsigned i;
		Label_Value( clause.Last_Lit().Var(), clause.Last_Lit().Sign() );  // label last literal as SAT
		for ( i = 1; !Lit_SAT( clause[i] ); i++ ) {}
		Un_Label_Value( clause.Last_Lit().Var() );
		return Lit_SAT( clause[i] );
	}
};

class Decision_Stack: public Assignment
{
protected:
	Literal * _dec_stack;
	unsigned _num_dec_stack;
	unsigned * _dec_offsets;
	unsigned _num_levels;  // each level includes decision literals (in _dec_stack) and components (in comp_stack)
public:
	Decision_Stack() {}
	~Decision_Stack() { if ( _max_var != Variable::undef ) Free_Auxiliary_Memory(); }
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when mv < max_var
	{
		if ( _max_var == max_var ) return;
		if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
		Assignment::Allocate_and_Init_Auxiliary_Memory( max_var );
		_dec_stack = new Literal [NumVars( max_var )];
		_dec_offsets = new unsigned [NumVars( max_var ) + 2];  // for counter, the first level storing implied literals could be empty, and the last level is preserved for _num_dec_stack
		/// init
		_num_dec_stack = 0;
		_num_levels = 0;
	}
	void Free_Auxiliary_Memory()
	{
		delete [] _dec_stack;
		delete [] _dec_offsets;
	}
	void Reset()
	{
		for ( unsigned  i = 0; i < _num_dec_stack; i++ ) {
			Un_Assign( _dec_stack[i].Var() );
		}
		_num_levels = _num_dec_stack = 0;
	}
	void Assign( Variable var, bool val )
	{
		assert( !Var_Decided( var ) );
		_dec_stack[_num_dec_stack++] = Literal( var, val );
		_assignment[var] = val;
	}
	void Assign( const Literal lit )
	{
		ASSERT( !Var_Decided( lit.Var() ) );
		_dec_stack[_num_dec_stack++] = lit;
		_assignment[lit.Var()] = lit.Sign();
	}
	void Un_Assign( Variable var ) { _assignment[var] = lbool::unknown; }
	void Extend_New_Level() { _dec_offsets[_num_levels++] = _num_dec_stack; }
	void Backtrack()
	{
		_num_levels--;
		while ( _num_dec_stack > _dec_offsets[_num_levels] ) {
			Un_Assign( _dec_stack[--_num_dec_stack].Var() );
		}
	}
	void Backjump( unsigned num_kept_levels )
	{
		_num_levels = num_kept_levels;
		while ( _num_dec_stack > _dec_offsets[_num_levels] ) {
			Un_Assign( _dec_stack[--_num_dec_stack].Var() );
		}
	}
	Literal Current_Decision() const { return _dec_stack[_dec_offsets[_num_levels - 1]]; }
	unsigned Num_Current_Imps() const { return _num_dec_stack - _dec_offsets[_num_levels - 1] - 1; }
	unsigned Num_Imps_On_Level( unsigned level ) const
	{
		_dec_offsets[_num_levels] = _num_dec_stack;
		return _dec_offsets[level + 1] - _dec_offsets[level] - 1;
	}
};

class Model
{
	friend class Model_Pool;
protected:
	unsigned * bits;
	Model * pre;
	Model * next;
	unsigned num_copy;  // NOTE: not consider itself, and 0 is initialized
public:
	Model( const Variable max_var )
	{
		unsigned size = Size( max_var );
		bits = new unsigned [size];
		num_copy = 0;
	}
	~Model() { delete [] bits; }
	void Copy( unsigned num = 1 ) { num_copy += num; }
	Model * Clone( const Variable max_var )
	{
		unsigned i, size = Size( max_var );
		Model * other = new Model( max_var );
		for ( i = 0; i < size; i++ ) {
			other->bits[i] = bits[i];
		}
		return other;
	}
	void Assign( bool * assignment, Variable max_var )
	{
		unsigned i, q, r, mask, size = Size( max_var );  // quotient remainder
		for ( i = 0; i < size; i++ ) {
			bits[i] = 0;
		}
		for ( i = Variable::start; i <= max_var; i++ ) {
			q = ( i - Variable::start ) / UNSIGNED_SIZE;
			r = ( i - Variable::start ) % UNSIGNED_SIZE;
			mask = assignment[i] << r;
			bits[q] |= mask;
		}
	}
	void Assign( Variable var, bool value )
	{
		unsigned q = ( var - Variable::start ) / UNSIGNED_SIZE, r = ( var - Variable::start ) % UNSIGNED_SIZE;  // quotient remainder
		unsigned mask = 1 << r;
		mask = ~mask;
		bits[q] &= mask;
		mask = value << r;
		bits[q] |= mask;
	}
	void Assign( Literal lit )
	{
		unsigned var = lit.Var(), q = ( var - Variable::start ) / UNSIGNED_SIZE, r = ( var - Variable::start ) % UNSIGNED_SIZE;
		unsigned mask = 1 << r;
		mask = ~mask;
		bits[q] &= mask;
		mask = lit.Sign() << r;
		bits[q] |= mask;
	}
	void Assign( Model * other, Variable max_var )
	{
	    unsigned i, size = Size( max_var );
		for ( i = 0; i < size; i++ ) {
            bits[i] = other->bits[i];
		}
	}
	bool operator [] ( const unsigned i )
	{
		unsigned q = ( i - Variable::start ) / UNSIGNED_SIZE, r = ( i - Variable::start ) % UNSIGNED_SIZE;
		unsigned mask = 1 << r;
		return bits[q] & mask;
	}
	bool Satisfy( Literal lit )
	{
		unsigned q = ( lit.Var() - Variable::start ) / UNSIGNED_SIZE, r = ( lit.Var() - Variable::start ) % UNSIGNED_SIZE;
		unsigned mask = 1 << r;
		bool bit = bits[q] & mask;
		return bit == lit.Sign();
	}
	bool Falsify( Literal lit )
	{
		unsigned q = ( lit.Var() - Variable::start ) / UNSIGNED_SIZE, r = ( lit.Var() - Variable::start ) % UNSIGNED_SIZE;
		unsigned mask = 1 << r;
		bool bit = bits[q] & mask;
		return bit != lit.Sign();
	}
	void Read( Variable max_var, char line[] )
	{
		unsigned i, q, r, mask, size = Size( max_var );  // quotient remainder
		for ( i = 0; i < size; i++ ) {
			bits[i] = 0;
		}
		char * p = line;
		while ( BLANK_CHAR( *p ) ) p++;
		for ( i = Variable::start; i <= max_var; i++ ) {
			int tmp;
			sscanf( p, "%d", &tmp);
			assert( -tmp == int(i) || tmp == int(i) );
			q = (i-Variable::start) / UNSIGNED_SIZE;
			r = (i-Variable::start) % UNSIGNED_SIZE;
			mask = (tmp > 0) << r;
			bits[q] |= mask;
			if( *p == '-' ) p++;
			while ( '0' <= *p && *p <= '9' ) p++;
			while ( BLANK_CHAR( *p ) ) p++;
		}
 	}
	void Display( unsigned max_var, ostream & fout )
	{
		fout << "[" << num_copy << "]: ";
		for ( unsigned i = Variable::start; i <= max_var; i++ ) {
			if ( (*this)[i] ) fout << i << " ";
			else fout << "-" << i << " ";
		}
		fout << endl;
	}
	void Display_Simple( unsigned max_var, ostream & fout )
	{
		for ( unsigned i = Variable::start; i <= max_var; i++ ) {
			if ( (*this)[i] ) fout << i << " ";
			else fout << "-" << i << " ";
		}
		fout << endl;
	}
protected:
	unsigned Size( Variable max_var )
	{
		return ( max_var - Variable::start + 1 + UNSIGNED_SIZE - 1 ) / UNSIGNED_SIZE;
	}
};

class Model_Pool
{
protected:
	Variable _max_var;
	Model * _allocated;  // Doubly linked list with a sentinel node
	Model * _unallocated;  // Singly linked list
	unsigned _alloc_size;  // the size of doubly linked list
public:
	Model_Pool( Variable max_var, unsigned capacity = 0 ) : _max_var( max_var ), _alloc_size( 0 )
	{
		_allocated = new Model( max_var );
		_allocated->pre = _allocated;
		_allocated->next = _allocated;
		_unallocated = NULL;
		for ( ; capacity > 0; capacity-- ) {
			Model * model = new Model( max_var );
			model->next = _unallocated;
			_unallocated = model;
		}
	}
	~Model_Pool()
	{
		Model * itr;
		for ( itr = _allocated->next; itr != _allocated;  ) {
			Model * tmp = itr;
			itr = itr->next;
			delete tmp;
		}
		delete _allocated;
		while ( _unallocated != NULL ) {
			itr = _unallocated;
			_unallocated = _unallocated->next;
			delete itr;
		}
	}
	void operator = ( Model_Pool & another )
	{
		Reset_Max_Var( another._max_var );
		for ( Model * itr = _allocated->pre; itr != _allocated; itr = itr->pre ) {
			Model * model = Allocate();
			for ( unsigned i = 0; i < model->Size( _max_var ); i++ ) {
				model->bits[i] = itr->bits[i];
			}
		}
	}
	void Free_Unallocated_Models()
	{
		while ( _unallocated != NULL ) {  // delete the list _unallocated
			Model * tmp = _unallocated;
			_unallocated = _unallocated->next;
			delete tmp;
		}
	}
	void Reset_Max_Var( Variable new_max_var )
	{
		if ( _max_var == new_max_var ) return;
		Model * itr;
		for ( itr = _allocated->next; itr != _allocated;  ) {  // delete the list _allocated
			Model * tmp = itr;
			itr = itr->next;
			delete tmp;
		}
		delete _allocated;
		while ( _unallocated != NULL ) {  // delete the list _unallocated
			itr = _unallocated;
			_unallocated = _unallocated->next;
			delete itr;
		}
		_max_var = new_max_var;
		_allocated = new Model( _max_var );  // realloc the list _allocated
		_allocated->pre = _allocated;
		_allocated->next = _allocated;
		_unallocated = NULL;
	}
	void Shrink_Max_Var( Variable new_max_var, Variable var_map[] )
	{
		assert( new_max_var < _max_var );
		for ( Model * itr = _allocated->next; itr != _allocated; itr = itr->next ) {  // delete the list _allocated
			unsigned size = itr->Size( new_max_var );
			unsigned * new_bits = new unsigned [size];
			unsigned * old_bits = itr->bits;
			itr->bits = new_bits;
			for ( Variable x = Variable::start; x <= _max_var; x++ ) {
				Variable x_map = var_map[x];
				if ( x_map <= new_max_var ) {
					itr->bits = old_bits;
					bool val = (*itr)[x];
					itr->bits = new_bits;
					itr->Assign( x_map, val );
				}
			}
			delete [] old_bits;
		}
		while ( _unallocated != nullptr ) {  // delete the list _unallocated
			Model * itr = _unallocated;
			_unallocated = _unallocated->next;
			delete itr;
		}
		_max_var = new_max_var;
		_unallocated = nullptr;
	}
	Model * Allocate()
	{
		unsigned i;
		Model * model;
		if ( _unallocated == NULL ) {
			for ( i = 0; i < 512; i++ ) {  // NOTE: reduce memory fragments
				model = new Model( _max_var );
				model->next = _unallocated;
				_unallocated = model;
			}
 		}
		model = _unallocated;
		_unallocated = _unallocated->next;
		model->next = _allocated->next;
		model->pre = _allocated;
		_allocated->next->pre = model;
		_allocated->next = model;
		_alloc_size++;
		return model;
	}
	void Free( Model * model )
	{
		if ( model->num_copy == 0 ) {
			model->pre->next = model->next;
			model->next->pre = model->pre;
			model->next = _unallocated;
			_unallocated = model;
			_alloc_size--;
		}
		else model->num_copy--;
	}
	void Clear()
	{
		Model * itr;
		for ( itr = _allocated->next; itr != _allocated;  ) {
			Model * tmp = itr;
			itr = itr->next;
			tmp->next = _unallocated;
			_unallocated = tmp;
		}
		_allocated->pre = _allocated;
		_allocated->next = _allocated;
		_alloc_size = 0;
	}
	vector<Model *> Models() const
	{
		vector<Model *> models;
		models.reserve( 512 );
		for ( Model * itr = _allocated->next; itr != _allocated; itr = itr->next ) {
			models.push_back( itr );
		}
		return models;
	}
	unsigned Size() const
	{
		return _alloc_size;
	}
	unsigned Capacity() const
	{
		unsigned capa = 0;
		for ( Model * itr = _unallocated; itr != NULL; itr = itr->next ) {
			capa++;
		}
		return capa + _alloc_size;
	}
	size_t Memory() const { return Capacity() * ( sizeof(Model) + ( _max_var - Variable::start + 1 ) / 8 ); }
	bool Empty() const { return _allocated->next == _allocated; }
	void Display( ostream & fout )
	{
		Model * itr;
		for ( itr = _allocated->next; itr != _allocated; itr = itr->next ) {
			itr->Display( _max_var, fout );
		}
	}
};


}


#endif
