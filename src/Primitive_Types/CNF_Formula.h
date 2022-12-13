#ifndef _CNF_Formula_
#define _CNF_Formula_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Template_Library/BigNum.h"
#include "../Template_Library/Graph_Structures.h"


namespace KCBox {


/** NOTE:
** sign = true: this is a positive literal
** otherwise it is a negative literal
** external variables and literals are in the format of DIMACS
** internal variable must begin with 0 or 1
**/


class Literal;

class Variable
{
protected:
	unsigned _val;
public:
	Variable() {}
	explicit Variable( unsigned var ): _val(var) {}
	Variable( const Variable &other ): _val(other._val) {}
	Variable Next() const { return Variable( _val + 1 ); }
	Variable & operator ++(int) { _val++; return *this; }
	Variable & operator --(int) { _val--; return *this; }
	Variable & operator = ( unsigned var ) { _val = var; return *this; }
	Variable & operator = ( const Variable other ) { _val = other._val; return *this; }
	bool operator == (const Variable &other) const { return _val == other._val; }
	bool operator != (const Variable &other) const { return _val != other._val; }
	bool operator == (const unsigned other) const { return _val == other; }
	bool operator != (const unsigned other) const { return _val != other; }
//	const Literal operator ~() const { return Literal( *this, false ); }
	operator unsigned () const { return _val; }
	const static Variable start;
	const static Variable undef;
};

class Literal
{
protected:
	unsigned _val;
public:
	Literal() {}
	explicit Literal( unsigned val ) { _val = val; }
	Literal( Variable var, bool sign) { _val = ( unsigned(var) << 1 ) + (unsigned) sign; }
	Variable Var() const { return Variable( _val >> 1 ); }
	Literal & operator ++(int) { _val++; return *this; }
	Literal & Inc_Var() { _val += 2; return *this; }
	bool Sign() const { return _val & 0x01; }
	bool NSign() const { return !(_val & 0x01); }
	bool operator == (const Literal &other) const { return _val == other._val; }
	bool operator != (const Literal &other) const { return _val != other._val; }
	bool operator == (const unsigned other) const { return _val == other; }
	bool operator != (const unsigned other) const { return _val != other; }
	const Literal operator ~() const { return Literal( _val ^ 0x01 ); }
	operator unsigned () const { return _val; }
	const static Literal start;
	const static Literal start_neg;
	const static Literal undef;
protected:
};

typedef unsigned VarID;
typedef unsigned LitID;

extern inline ostream & operator << ( ostream & out, Literal & lit )
{
	out << unsigned(lit);
	return out;
}

extern inline Variable InternVar( int evar )
{
	return Variable( evar - 1 + Variable::start );
}

extern inline Literal InternLit( int elit )
{
	Variable var = elit > 0 ? InternVar(elit) : InternVar(-elit);
	return Literal( var, elit > 0 );
}

extern inline int ExtVar( Variable var )  // external variable
{
	return var - Variable::start + 1;
}

extern inline int ExtLit( Literal lit )  // external literal
{
	int evar = ExtVar( lit.Var() );
	return lit.Sign() ? evar : -evar;
}

extern inline int ExtLit( Variable var, bool sign )
{
	int evar = ExtVar( var );
	return sign ? evar : -evar;
}

extern inline unsigned NumVars( Variable max_var )
{
	return max_var - Variable::start + 1;
}

extern void Read_Ext_Clauses( istream & fin, vector<vector<int>> & clauses );

/* NOTE:
* Filter <lits> by <vars>, and the resulting literals are left in <left_lits>, where <lits> and <vars> are sorted
*/
extern inline unsigned Filter_Lits( Literal * lits, unsigned len, Variable * vars, unsigned size, Literal * left_lits )
{
	unsigned i = 0, j = 0, num = 0;
	while ( i < len && j < size ) {
		if ( lits[i].Var() < vars[j] ) i++;
		else if ( lits[i].Var() > vars[j] ) j++;
		else {
			left_lits[num++] = lits[i];
			i++, j++;
		}
	}
	return num;
}

class Big_Clause
{
protected:
	Literal * _lits;
	unsigned _size;
	unsigned _capacity;
public:
	Big_Clause( unsigned max_var ): _size( 0 ), _capacity( max_var ) { Allocate_Memory(); }
	~Big_Clause() { delete [] _lits; }
	unsigned Size() const { return _size; }
	void Resize( unsigned size ) { _size = size; }
	void Reserve( unsigned max_var )
	{
		delete [] _lits;
		_capacity = max_var + 1;
		Allocate_Memory();
	}
	Literal & operator [] ( unsigned i ) { return _lits[i]; }
	Literal & Last_Lit() { return _lits[_size - 1]; }  /// NOTE: this clause cannot be empty
	void Add_Lit( Literal lit ) { _lits[_size++] = lit; }
	void Erase_Lit( unsigned i ) { assert( i < _size ); _lits[i] = _lits[--_size]; }
	void Swap_Lits( unsigned i, unsigned j ) { Literal tmp = _lits[i]; _lits[i] = _lits[j]; _lits[j] = tmp; }
	void Clear() { _size = 0; }
protected:
	void Allocate_Memory()
	{
		_lits = new Literal [_capacity];
		if ( _lits == nullptr ) {
			cerr << "ERROR[Big_Clause]: fail for allocating space for Big_Clause!" << endl;
			exit( 1 );
		}
	}
};

class Clause
{
protected:
	Literal * _lits;  /// NOTE: need to call Free() to free the memory outside
	unsigned _size;
public:
	Clause(): _lits( nullptr ), _size( 0 ) {}
	Clause( Literal lit ): _size( 1 )
	{
		Allocate_Memory();
		_lits[0] = lit;
	}
	Clause( Literal lit0, Literal lit1 ): _size( 2 )
	{
		Allocate_Memory();
		_lits[0] = lit0;
		_lits[1] = lit1;
	}
	Clause( const Literal * lits, unsigned size ): _size( size )
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < size; i++ ) {
			_lits[i] = lits[i];
		}
	}
	Clause( const vector<Literal> & lits ): _size( lits.size() )
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < _size; i++ ) {
			_lits[i] = lits[i];
		}
	}
	Clause( Big_Clause & clause ): _size ( clause.Size() )
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < _size; i++ ) {
			_lits[i] = clause[i];
		}
	}
	Clause Copy() const { return Clause( _lits, _size ); }  /// NOTE: the object created by copy constructor will share the same memory
	void Free() { delete [] _lits; }
	unsigned Size() const { return _size; }
	void Shrink( unsigned size ) { assert( size <= _size ); _size = size; }
	Literal & operator [] ( unsigned i ) { return _lits[i]; }
	Literal & Last_Lit() { return _lits[_size - 1]; }  /// NOTE: this clause cannot be empty
	void Erase_Lit( unsigned i ) { assert( i < _size ); _lits[i] = _lits[--_size]; }
	void Swap_Lits( unsigned i, unsigned j ) { Literal tmp = _lits[i]; _lits[i] = _lits[j]; _lits[j] = tmp; }
	void Swap( Clause & clause )
	{
		unsigned tmp_size = _size;
		_size = clause._size;
		clause._size = tmp_size;
		Literal * tmp_lits = _lits;
		_lits = clause._lits;
		clause._lits = tmp_lits;
	}
	void Sort( QSorter & sorter ) { sorter.Sort( _lits, _size ); }
	void Sort( const unsigned * var_rank );
	void Display( ostream & out)
	{
		for ( unsigned i = 0; i < _size; i++ ) {
			out << ExtLit( _lits[i] ) << ' ';
		}
		out << '0' << endl;
	}
protected:
	void Allocate_Memory()
	{
		_lits = new Literal [_size];
		if ( _size > 0 && _lits == NULL ) {
			cerr << "ERROR[Clause]: fail for allocating space for clause!" << endl;
			exit( 1 );
		}
	}
};


extern vector<int> ExtLits( Literal lit );

extern vector<int> ExtLits( Literal lit1, Literal lit2 );

extern vector<int> ExtLits( Big_Clause & clause );

extern vector<int> ExtLits( Clause & clause );

extern Clause Clause_Random( Variable max_var, unsigned max_len, unsigned min_len );

extern ostream & operator << ( ostream & out, Clause & clause );

extern void Display_Clauses( ostream & out, unsigned num_vars, vector<Clause> & clauses );

extern void Display_Ext_Clause( ostream & out, vector<int> & eclause  );

extern void Display_Ext_Clauses( ostream & out, vector<vector<int>> & eclauses );

extern void Display_Ext_Clauses( ostream & out, unsigned num_vars, vector<vector<int>> & eclauses );

class Greedy_Graph;
struct Chain;

class CNF_Formula
{
	friend ostream & operator << ( ostream & out, CNF_Formula & cnf );
protected:
	Variable _max_var;
	vector<Clause> _clauses;
protected: // auxuliary memory
	vector<unsigned> _independent_support;
	BigInt _known_count;
public:
	CNF_Formula( unsigned max_var ): _max_var( max_var ) {}
	CNF_Formula( istream & fin );
	CNF_Formula( Random_Generator & rand_gen, unsigned num_var, unsigned num_cl, unsigned min_len, unsigned max_len );  /// generate a random formula
	CNF_Formula( CNF_Formula & other );
	CNF_Formula( unsigned max_var, vector<Clause> & clauses );
	CNF_Formula( vector<vector<int>> & extclauses );
	~CNF_Formula();
	void Rename( Variable map[] );  // i -> map[i]
	void Divide_Into_Two_Halves( CNF_Formula * & first, CNF_Formula * & second );  /// first and second are created in the function
	void Add_Unary_Clause( Literal lit ) { _clauses.push_back( Clause( &lit, 1 ) ); }
	void Add_Binary_Clause( Literal lit0, Literal lit1 ) { Literal lits[2] = {lit0, lit1}; _clauses.push_back( Clause( lits, 2 ) ); }
	void Add_Ternary_Clause( Literal lit0, Literal lit1, Literal lit2 ) { Literal lits[3] = {lit0, lit1, lit2}; _clauses.push_back( Clause( lits, 3 ) ); }
	void Add_Clause( Clause & cl ) { _clauses.push_back( cl.Copy() ); }  /// allocate space
	void Add_Clause( Big_Clause & cl ) { _clauses.push_back( cl ); }  /// allocate space
	void Input_Clause( Clause & cl ) { _clauses.push_back( cl ); }  /// not allocate space
	unsigned Num_Vars() const { return _max_var - Variable::start + 1; }
	Variable Max_Var() const { return _max_var; }
	BigInt Known_Count() const { return _known_count; }
	vector<unsigned> & Independent_Support() { return _independent_support; }
	unsigned Num_Clauses() const { return _clauses.size(); }
	Clause & Last_Clause() { return _clauses.back(); }
	vector<Clause>::iterator Clause_Begin() { return _clauses.begin(); }
	vector<Clause>::iterator Clause_End() { return _clauses.end(); }
	Clause & operator [] ( unsigned i ) { return _clauses[i]; }
	void Sort_Clauses();
	void ExtClauses( vector<vector<int>> & extclauses );
protected:
	CNF_Formula(): _max_var( Variable::undef ) {}
    bool Get_Line( istream & fin, char line[] );
    bool Read_Known_Result( char line[] );
    unsigned Read_Clause( char line[], Literal lits[] );
    Literal Read_Lit( char * & p );
	void Read_Independent_Support( char line[] );
	void Generate_Lit_Membership_Lists( vector<vector<unsigned>> & membership_lists );
	void Generate_Var_Membership_Lists( vector<vector<unsigned>> & membership_lists );
	void Compute_Heur_Var_Values();
public:
	Greedy_Graph * Create_Primal_Graph_Opt();  // use membership_list
public:
	static void Debug()
	{
	    ifstream fin( "debug.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
	    cout << cnf;
	}
};

class EPCCL_Theory: public CNF_Formula
{
protected:
	bool Check();
	bool Check_New_Clauses( Clause cl );
public:
	EPCCL_Theory( unsigned mv ): CNF_Formula( mv ) {}
	BigInt Count_Models();
};

class WCNF_Formula: public CNF_Formula
{
	friend ostream & operator << ( ostream & out, WCNF_Formula & cnf );
protected:
	vector<float> _weights;  // _weights[lit] is the weight of lit
public:
	WCNF_Formula( unsigned max_var ): CNF_Formula( max_var ), _weights( 2 * max_var + 2, 1 ) {}
	WCNF_Formula( istream & fin, unsigned format = 0 );
	WCNF_Formula( Random_Generator & rand_gen, unsigned num_var, unsigned num_cl, unsigned min_len, unsigned max_len );  /// generate a random formula
	const vector<float> & Weights() { return _weights; }
	float Weights( Literal lit ) const { return _weights[lit]; }
	void Display( ostream & out, unsigned format = 0 );
protected:
	void Read_MC_Competition_Format( istream & fin );
    bool Get_Line_MC_Competition( istream & fin, char line[] );
	void Read_Literal_Weight( char * p );
	void Read_MiniC2D_Format( istream & fin );
    bool Get_Line_MiniC2D( istream & fin, char line[] );
	void Remove_Zero();
};

extern BigFloat Count_Models_ADDMC( WCNF_Formula & wcnf );


}



#endif
