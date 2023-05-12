#include "CNF_Formula.h"


namespace KCBox {


const Variable Variable::start( 1 );
const Variable Variable::undef( UNSIGNED_UNDEF );
const Literal Literal::start( Variable::start, false );
const Literal Literal::start_neg( Variable::start, true );
const Literal Literal::undef( UNSIGNED_UNDEF );


extern void Read_Ext_Clauses( istream & fin, vector<vector<int>> & clauses )
{
	if ( fin.fail() ) {
		cerr << "ERROR[CNF_Formula]: the input file cannot be opened!" << endl;
		exit( 0 );
	}
	char line[MAX_LINE];
	fin.getline( line, MAX_LINE );
	unsigned max_var, num_cl;
	if ( sscanf( line, "p cnf %u %u", &max_var, &num_cl ) != 2 ) {
		cerr << "ERROR[CNF_Formula]: wrong cnf-file format!" << endl;
	}
	vector<int> lits;
	for( unsigned int i = 0; i < num_cl; i++ ) {
		fin.getline( line, MAX_LINE );
		char * p = line;
		while ( *p == ' ' || *p == '\t' ) p++;
		while ( 1 ) {
			int tmp;
			sscanf( p, "%d", &tmp);
			if ( tmp == 0 ) break;
			lits.push_back( tmp );
			if( *p == '-' ) p++;
			while ( *p >= '0' && *p <= '9' ) p++;
			while ( *p == ' ' || *p == '\t' ) p++;
		}
		clauses.push_back( lits );
		lits.clear();
	}
}

void Clause::Sort( const unsigned * var_rank )
{
	unsigned i, j, begin;
	for ( i = begin = _size - 1; i > 0; i-- ) { // validate the following insertion_sort
		if ( var_rank[_lits[i].Var()] < var_rank[_lits[i-1].Var()] ) {
			begin = i;
			Literal tmp = _lits[i-1];
			_lits[i-1] = _lits[i];
			_lits[i] = tmp;
		}
	}
	for ( i = begin + 1; i < _size; i++ ) {
		Literal tmp = _lits[i];
		for ( j = i - 1; var_rank[_lits[j].Var()] > var_rank[tmp.Var()]; j-- ) {
			_lits[j+1] = _lits[j];
		}
		_lits[j+1] = tmp;
	}
}

extern vector<int> ExtLits( Literal lit )
{
	vector<int> eclause( 1 );
	eclause[0] = ExtLit( lit );
	return eclause;
}

extern vector<int> ExtLits( Literal lit1, Literal lit2 )
{
	vector<int> eclause( 2 );
	eclause[0] = ExtLit( lit1 );
	eclause[1] = ExtLit( lit2 );
	return eclause;
}

extern vector<int> ExtLits( Big_Clause & bclause )
{
	size_t i;
	vector<int> eclause( bclause.Size() );
	for ( i = 0; i < bclause.Size(); i++ ) { // validate the following insertion_sort
		eclause[i] = ExtLit( bclause[i] );
	}
	return eclause;
}

extern vector<int> ExtLits( Clause & clause )
{
	size_t i;
	vector<int> eclause( clause.Size() );
	for ( i = 0; i < clause.Size(); i++ ) { // validate the following insertion_sort
		eclause[i] = ExtLit( clause[i] );
	}
	return eclause;
}

extern Clause Clause_Random( Variable max_var, unsigned max_len, unsigned min_len )
{
	assert( 0 < min_len && min_len <= max_len && max_len <= NumVars( max_var ) );
	unsigned i;
	Random_Generator rand_gen;
	unsigned len = rand_gen.Generate_Int( min_len, max_len );
	vector<Literal> lits( len );
	vector<bool> var_seen( max_var + 1, false );
	for ( i = 0; i < len; ) {
		lits[i] = Literal( rand_gen.Generate_Int( Literal::start, 2 * max_var + 1 ) );
		i += !var_seen[lits[i].Var()];
		var_seen[lits[i].Var()] = true;
	}
	return Clause( lits );
}

extern ostream & operator << ( ostream & out, Clause & clause )
{
	for ( unsigned i = 0; i < clause.Size(); i++ ) {
		out << ExtLit( clause[i] ) << ' ';
	}
	out << '0';
	return out;
}

extern void Display_Clauses( ostream & out, unsigned num_vars, vector<Clause> & clauses )
{
	out << "p cnf " << num_vars << ' ' << clauses.size() << endl;
	for ( unsigned i = 0; i < clauses.size(); i++ ) {
		out << clauses[i] << endl;
	}
}

extern void Display_Ext_Clause( ostream & out, vector<int> & eclause  )
{
	unsigned i;
	for ( i = 0; i < eclause.size(); i++ ) {
		out << eclause[i] << ' ';
	}
	out << '0' << endl;
}

extern void Display_Ext_Clauses( ostream & out, vector<vector<int>> & eclauses )
{
	for ( unsigned i = 0; i < eclauses.size(); i++ ) {
		for ( unsigned j = 0; j < eclauses[i].size(); j++ ) {
			out << eclauses[i][j] << ' ';
		}
		out << '0' << endl;
	}
}

extern void Display_Ext_Clauses( ostream & out, unsigned num_vars, vector<vector<int>> & eclauses )
{
	out << "p cnf " << num_vars << ' ' << eclauses.size() << endl;
	Display_Ext_Clauses( out, eclauses );
}

CNF_Formula::CNF_Formula( istream & fin )
{
	if ( fin.fail() ) {
		cerr << "ERROR[CNF_Formula]: the input file cannot be opened!" << endl;
		exit( 1 );
	}
	unsigned i, num_cl;
	bool extra_header = false, extra_clause = false;
	char line[MAX_LINE];
	if ( !Get_Line( fin, line ) ) {
		cerr << "Warning[CNF_Formula]: no header!" << endl;
		_max_var = Variable::undef;
		_known_count = 0;
		return;
	}
	if ( Read_Known_Result( line ) ) {
		Get_Line( fin, line );
		if ( !fin.eof() ) {
			cerr << "ERROR[CNF_Formula]: wrong cnf-file format!" << endl;
			exit( 1 );
		}
		_max_var = Variable::undef;
		return;
	}
	unsigned num_vars;
	if ( sscanf( line, "p cnf %u %u", &num_vars, &num_cl ) != 2 ) {
		cerr << "ERROR[CNF_Formula]: wrong cnf-file format!" << endl;
		exit( 1 );
	}
	_max_var = Variable::start + num_vars - 1;
	Literal * lits = new Literal [_max_var + 1];
	for( i = 0; i < num_cl; i++ ) {
		if ( !Get_Line( fin, line ) ) {
			cerr << "Warning[CNF_Formula]: not enough clauses!" << endl;
			break;
		}
		if ( line[0] == 'p' ) {
			if ( !extra_header ) {
				cerr << "Warning[CNF_Formula]: extra header!" << endl;
				extra_header = true;
			}
			i--;
			continue;
		}
		char * p = line;
		unsigned len = Read_Clause( p, lits );
		_clauses.push_back( Clause( lits, len ) );
	}
	while ( Get_Line( fin, line ) ) {
		char * p = line;
		while ( BLANK_CHAR_GENERAL( *p ) ) p++;
		if ( DIGIT_CHAR( *p ) || *p == '-' ) {
			if ( !extra_clause ) {
				cerr << "Warning[CNF_Formula]: extra clauses beyond stated!" << endl;
				extra_clause = true;
			}
			unsigned len = Read_Clause( p, lits );
			_clauses.push_back( Clause( lits, len ) );
		}
		else {
			cerr << "ERROR[CNF_Formula]: invalid information!" << endl;
			exit( 1 );
		}
	}
	delete [] lits;
}

bool CNF_Formula::Get_Line( istream & fin, char line[] )
{
	while ( !fin.eof() ) {
		fin.getline( line, MAX_LINE );
		if ( line[0] == 'c' ) {
			Read_Independent_Support( line );
			continue;
		}
		char * p = line;
		while ( BLANK_CHAR_GENERAL( *p ) ) p++;
		if ( *p == '\0' ) continue;
		return true;
	}
	return false;
}

bool CNF_Formula::Read_Known_Result( char line[] )
{
	char * p = line;
	while ( BLANK_CHAR( *p ) ) p++;
	if ( p[0] == 's' ) {
		p++;
		sscanf( p, _known_count );
		return true;
	}
	else return false;
}

unsigned CNF_Formula::Read_Clause( char line[], Literal lits[] )
{
	unsigned len = 0;
	char * p = line;
	while ( BLANK_CHAR_GENERAL( *p ) ) p++;
	while ( *p != '\0' ) {
		Literal lit = Read_Lit( p );
		if ( lit == Literal::undef ) break;
		lits[len++] = lit;
		while ( BLANK_CHAR( *p ) ) p++;
	}
	if ( *p == '\0' ) {
		cerr << "ERROR[CNF_Formula]: invalid clause without a zero end!" << endl;
		exit( 1 );
	}
	else if ( len == 0 ) {
		cerr << "ERROR[CNF_Formula]: empty clause!" << endl;
		exit( 1 );
	}
	return len;
}

Literal CNF_Formula::Read_Lit( char * & p )
{
	int elit;
	if ( sscanf( p, "%d", &elit) != 1 ) {
		cerr << "ERROR[CNF_Formula]: invalid literal!" << endl;
		exit( 1 );
	}
	if ( elit == 0 ) return Literal::undef;
	if( *p == '-' ) p++;
	while ( DIGIT_CHAR( *p ) ) p++;
	return InternLit( elit );
}

void CNF_Formula::Read_Independent_Support( char line[] )
{
	assert( line[0] == 'c' );
	char * p = line + 1;
	if ( !Read_String_Change( p, "ind" ) ) return;
	while ( *p == ' ' || *p == '\t' ) p++;
	unsigned old_size = _independent_support.size();
	int tmp = _max_var + 1;
	while ( 1 ) {
		if ( sscanf( p, "%d", &tmp) != 1 ) {
			cerr << "ERROR[CNF_Formula]: invalid independent support!" << endl;
			exit( 0 );
		}
		if ( tmp == 0 ) break;
		_independent_support.push_back( tmp );
		while ( '0' <= *p && *p <= '9' ) p++;
		while ( *p == ' ' || *p == '\t' ) p++;
	}
	if ( tmp != 0 ) _independent_support.resize( old_size );
}

CNF_Formula::CNF_Formula( Random_Generator & rand_gen, unsigned num_var, unsigned num_cl, unsigned min_len, unsigned max_len ) :
_max_var( Variable::start + num_var - 1 )
{
	assert( 0 < min_len && min_len <= max_len && max_len <= num_var );
	unsigned i, j, len;
	vector<bool> lit_seen( 2 * _max_var + 2, false );
	Big_Clause lits( _max_var );
	for ( i = 0; i < num_cl; i++ ) {
		len = rand_gen.Generate_Int( min_len, max_len );
		lits.Resize( len );
		while ( true ) {
			for ( j = 0; j < len; ) {
				Literal lit( rand_gen.Generate_Int( Literal::start, 2 * _max_var + 1 ) );
				if ( !lit_seen[lit] && !lit_seen[~lit] ) {
					lit_seen[lit] = true;
					lits[j++] = lit;
				}
			}
			vector<Clause>::iterator itr = _clauses.begin();
			vector<Clause>::iterator end = _clauses.end();
			for ( ; itr < end; itr++ ) {
				if ( itr->Size() > len ) continue;
				for ( j = 0; j < itr->Size(); j++ ) {
					if ( !lit_seen[(*itr)[j]] ) break;
				}
				if ( j == itr->Size() ) break;
			}
			for ( j = 0; j < len; j++ ) {
				lit_seen[lits[j]] = false;
			}
			if ( itr == end ) break;
		}
		_clauses.push_back( lits );
	}
}

CNF_Formula::CNF_Formula( CNF_Formula & other ) :
_max_var( other._max_var )
{
	vector<Clause>::iterator itr =  other._clauses.begin(), end = other._clauses.end();
	for ( ; itr < end; itr++ ) {
		Add_Clause( *itr );
	}
}

CNF_Formula::CNF_Formula( unsigned max_var, vector<Clause> & clauses ) :
_max_var( max_var ),
_clauses( clauses )
{
	clauses.clear();
}

CNF_Formula::CNF_Formula( vector<vector<int>> & extclauses ) :
_max_var( Variable::start )
{
	unsigned i;
	vector<vector<int>>::iterator itr =  extclauses.begin(), end = extclauses.end();
	vector<Literal> lits;
	for ( ; itr < end; itr++ ) {
		lits.resize( itr->size() );
		for ( i = 0; i < itr->size(); i++ ) {
			lits[i] = InternLit( (*itr)[i] );
			if ( _max_var < lits[i].Var() ) _max_var = lits[i].Var();
		}
		_clauses.push_back( Clause( lits ) );
	}
}

CNF_Formula::~CNF_Formula()
{
	vector<Clause>::iterator itr = _clauses.begin(), end = _clauses.end();
	for ( ; itr < end; itr++ ) {
		itr->Free();
	}
}

void CNF_Formula::Rename( Variable map[] )
{
	vector<Clause>::iterator itr = _clauses.begin(), end = _clauses.end();
	for ( ; itr < end; itr++ ) {
		for ( unsigned i = 0; i < itr->Size(); i++ ) {
			(*itr)[i] = Literal( map[(*itr)[i].Var()], (*itr)[i].Sign() );
		}
	}
}

void CNF_Formula::Divide_Into_Two_Halves( CNF_Formula * & first, CNF_Formula * & second )
{
	unsigned i;
	unsigned half = ( _clauses.size() + 1 ) / 2;
	first = new CNF_Formula( _max_var );
	for( i = 0; i < half; i++ ) {
		first->Add_Clause( _clauses[i] );
	}
	second = new CNF_Formula( _max_var );
	for( ; i < _clauses.size(); i++ ) {
		second->Add_Clause( _clauses[i] );
	}
}

void CNF_Formula::Sort_Clauses()
{
	QSorter sorter;
	vector<Clause>::iterator itr = _clauses.begin(), end = _clauses.end();
	for ( ; itr < end; itr++ ) {
		itr->Sort( sorter );
	}
}

void CNF_Formula::ExtClauses( vector<vector<int>> & extclauses )
{
	vector<Clause>::iterator itr = _clauses.begin(), end = _clauses.end();
	for ( ; itr < end; itr++ ) {
		extclauses.push_back( ExtLits( *itr ) );
	}
}

void CNF_Formula::Generate_Lit_Membership_Lists( vector<vector<unsigned>> & membership_lists )
{
	vector<Clause>::iterator begin = _clauses.begin();
	vector<Clause>::iterator end = _clauses.end();
	for ( vector<Clause>::iterator itr = begin; itr < end; itr++ ) {
		for ( unsigned i = 0; i < itr->Size(); i++ ) {
			membership_lists[(*itr)[i]].push_back( itr - begin );
		}
	}
}

void CNF_Formula::Generate_Var_Membership_Lists( vector<vector<unsigned>> & membership_lists )
{
	vector<Clause>::iterator begin = _clauses.begin();
	vector<Clause>::iterator end = _clauses.end();
	for ( vector<Clause>::iterator itr = begin; itr < end; itr++ ) {
		for ( unsigned i = 0; i < itr->Size(); i++ ) {
			membership_lists[(*itr)[i].Var()].push_back( itr - begin );
		}
	}
}

Greedy_Graph * CNF_Formula::Create_Primal_Graph_Opt()
{
	unsigned i, j;
	vector<vector<unsigned>> membership_lists( _max_var + 1 );
	Generate_Var_Membership_Lists( membership_lists );
	unsigned * vertices = new unsigned [_max_var];
	unsigned size;
	vector<vector<unsigned>> edges( _max_var + 1 );
	vector<bool> var_seen( _max_var + 1, false );
	for ( i = Variable::start; i <= _max_var; i++ ) {
		size = 0;
		vector<unsigned>::iterator itr = membership_lists[i].begin();
		vector<unsigned>::iterator end = membership_lists[i].end();
		for ( ; itr < end; itr++ ) {
			Clause & clause = _clauses[*itr];
			for ( j = 0; clause[j].Var() != i; j++ ) {
				vertices[size] = clause[j].Var();
				size += !var_seen[clause[j].Var()];
				var_seen[clause[j].Var()] = true;
			}
			for ( j++; j < clause.Size(); j++ ) {
				vertices[size] = clause[j].Var();
				size += !var_seen[clause[j].Var()];
				var_seen[clause[j].Var()] = true;
			}
		}
		for ( j = 0; j < size; j++ ) {
			edges[i].push_back( vertices[j] );
			var_seen[vertices[j]] = false;
		}
	}
	delete [] vertices;
	Greedy_Graph * gp = new Greedy_Graph( _max_var, edges );
	return gp;
}

void CNF_Formula::Condition( const vector<Literal> & term )
{
	vector<bool> lit_seen( _max_var * 2 + 2, false );
	for ( Literal lit: term ) {
		if ( lit_seen[~lit] ) {
			cerr << "ERROR[CNF_Formula]: an inconsistent term with conditioning!" << endl;
			exit(0);
		}
		lit_seen[lit] = true;
	}
	unsigned i = 0, j;
	while ( i < _clauses.size() ) {
		for ( j = 0; j < _clauses[i].Size(); ) {
			Literal lit = _clauses[i][j];
			if ( lit_seen[lit] ) break;
			else if ( lit_seen[~lit] ) _clauses[i].Erase_Lit( j );
			else j++;
		}
		if ( j < _clauses[i].Size() ) {
			_clauses[i].Free();
			_clauses.erase( _clauses.begin() + i );
		}
		else if ( _clauses[i].Size() == 0 ) break;
		else i++;
	}
	if ( i < _clauses.size() ) {
		_max_var = Variable::undef;
		_known_count = 0;
	}
}

ostream & operator << ( ostream & out, CNF_Formula & cnf )
{
	if ( cnf._max_var < Variable::start ) {
		cerr << "ERROR[CNF_Formula]: Invalid formula!"<< endl;
		return out;
	}
	out << "p cnf " << cnf.Num_Vars() << ' ' << cnf._clauses.size() << endl;
	for ( unsigned i = 0; i < cnf._clauses.size(); i++ ) {
		out << cnf[i] << endl;
	}
	return out;
}

BigInt EPCCL_Theory::Count_Models()
{
	BigInt result = 1, tmp;
	result.Mul_2exp( _max_var );
	vector<Clause>::iterator itr = _clauses.begin(), end = _clauses.end();
	for ( ; itr < end; itr++ ) {
		tmp.Assign_2exp( _max_var - itr->Size() );
		result -= tmp;
	}
	return result;
}

WCNF_Formula::WCNF_Formula( istream & fin, unsigned format )
{
	if ( fin.fail() ) {
		cerr << "ERROR[WCNF_Formula]: the input file cannot be opened!" << endl;
		exit( 1 );
	}
	switch ( format ) {
	case 0:
		Read_MC_Competition_Format( fin );
		break;
	case 1:
		Read_MiniC2D_Format( fin );
		break;
	default:
		cerr << "ERROR[WCNF_Formula]: format not supported!" << endl;
		exit( 1 );
	}
}

void WCNF_Formula::Read_MC_Competition_Format( istream & fin )
{
	unsigned num_cl;
	bool extra_header = false, extra_clause = false;
	char line[MAX_LINE];
	if ( !Get_Line_MC_Competition( fin, line ) ) {
		cerr << "ERROR[WCNF_Formula]: no header!" << endl;
		exit( 1 );
	}
	unsigned num;
	if ( sscanf( line, "p cnf %d %u", &num, &num_cl ) != 2 ) {
		cerr << "ERROR[WCNF_Formula]: wrong cnf-file format!" << endl;
		exit( 1 );
	}
	_max_var = Variable::start + num - 1;
	num = _weights.size() / 2;
	_weights.resize( 2 * _max_var + 2 );  //
	for ( unsigned i = num; i <= _max_var;i++ ) {
		_weights[i + i] = 1;
		_weights[i + i + 1] = 1;
	}
	Literal * lits = new Literal [_max_var + 1];
	for( unsigned i = 0; i < num_cl; i++ ) {
		if ( !Get_Line_MC_Competition( fin, line ) ) {
			cerr << "Warning[WCNF_Formula]: not enough clauses!" << endl;
			break;
		}
		if ( line[0] == 'p' ) {
			if ( !extra_header ) {
				cerr << "Warning[WCNF_Formula]: extra header!" << endl;
				extra_header = true;
			}
			i--;
			continue;
		}
		char * p = line;
		unsigned len = Read_Clause( p, lits );
		_clauses.push_back( Clause( lits, len ) );
	}
	while ( Get_Line_MC_Competition( fin, line ) ) {
		char * p = line;
		while ( BLANK_CHAR_GENERAL( *p ) ) p++;
		if ( DIGIT_CHAR( *p ) || *p == '-' ) {
			if ( !extra_clause ) {
				cerr << "Warning[WCNF_Formula]: extra clauses beyond stated!" << endl;
				extra_clause = true;
			}
			unsigned len = Read_Clause( p, lits );
			_clauses.push_back( Clause( lits, len ) );
		}
		else {
			cerr << "ERROR[WCNF_Formula]: invalid information!" << endl;
			exit( 1 );
		}
	}
	delete [] lits;
	Remove_Zero();
}

bool WCNF_Formula::Get_Line_MC_Competition( istream & fin, char line[] )
{
	while ( !fin.eof() ) {
		fin.getline( line, MAX_LINE );
		if ( line[0] != 'c' ) {
			char * p = line;
			while ( BLANK_CHAR_GENERAL( *p ) ) p++;
			if ( *p == '\0' ) continue;
			else return true;
		}
		char * p = line + 1;
		while ( BLANK_CHAR( *p ) ) p++;
		if ( Read_String_Change( p, "t" ) ) {
			if ( !Read_String_Change( p, "wmc" ) ) {
				cerr << "ERROR[WCNF_Formula]: invalid type!" << endl;
				exit( 1 );
			}
		}
		else if ( Read_String_Change( p, "p" ) ) {
			if ( !Read_String_Change( p, "weight" ) ) {
				cerr << "ERROR[WCNF_Formula]: invalid weight!" << endl;
				exit( 1 );
			}
			Read_Literal_Weight( p );
		}
	}
	return false;
}

void WCNF_Formula::Read_Literal_Weight( char * p )
{
	while ( BLANK_CHAR( *p ) ) p++;
	Literal lit = Read_Lit( p );
	if ( lit == Literal::undef ) {
		cerr << "ERROR[WCNF_Formula]: wrong literal!" << endl;
		exit( 1 );
	}
	while ( BLANK_CHAR( *p ) ) p++;
	double w;
	if ( sscanf( p, "%lf", &w ) != 1 ) {
		cerr << "ERROR[WCNF_Formula]: wrong weight!" << endl;
		exit( 1 );
	}
	if ( w < 0 || w > 1 ) {
		cerr << "ERROR[WCNF_Formula]: wrong weight!" << endl;
		exit( 1 );
	}
	while ( DIGIT_CHAR( *p ) || *p == '.' || *p == '-' || *p == '+' ) p++;
	if ( *p == 'e' || *p == 'E' ) {
		p++;
		if ( *p == '-' || *p == '+' ) p++;
		while ( DIGIT_CHAR( *p ) ) p++;
	}
	while ( BLANK_CHAR( *p ) ) p++;
	if ( *p != '0' ) {
		cerr << "ERROR[WCNF_Formula]: invalid weight-end!" << endl;
		exit( 1 );
	}
	p++;
	while ( BLANK_CHAR( *p ) ) p++;
	if ( *p != '\0' ) {
		cerr << "ERROR[WCNF_Formula]: invalid weight-end!" << endl;
		exit( 1 );
	}
	for ( unsigned i = _weights.size() / 2; i <= lit.Var(); i++ ) {
		_weights.push_back( 1 );
		_weights.push_back( 1 );
	}
	_weights[lit] = w;
}

void WCNF_Formula::Read_MiniC2D_Format( istream & fin )
{
	unsigned num_cl;
	bool extra_header = false, extra_clause = false;
	char line[MAX_LINE];
	if ( !CNF_Formula::Get_Line( fin, line ) ) {
		cerr << "ERROR[WCNF_Formula]: no header!" << endl;
		exit( 1 );
	}
	unsigned num_vars;
	if ( sscanf( line, "p cnf %d %u", &num_vars, &num_cl ) != 2 ) {
		cerr << "ERROR[WCNF_Formula]: wrong cnf-file format!" << endl;
	}
	_max_var = Variable::start + num_vars - 1;
	Literal * lits = new Literal [_max_var + 1];
	for( unsigned i = 0; i < num_cl; i++ ) {
		if ( !Get_Line_MiniC2D( fin, line ) ) {
			cerr << "Warning[WCNF_Formula]: not enough clauses!" << endl;
			break;
		}
		if ( line[0] == 'p' ) {
			if ( !extra_header ) {
				cerr << "Warning[WCNF_Formula]: extra header!" << endl;
				extra_header = true;
			}
			i--;
			continue;
		}
		char * p = line;
		unsigned len = Read_Clause( p, lits );
		_clauses.push_back( Clause( lits, len ) );
	}
	while ( Get_Line_MiniC2D( fin, line ) ) {
		char * p = line;
		while ( BLANK_CHAR_GENERAL( *p ) ) p++;
		if ( DIGIT_CHAR( *p ) || *p == '-' ) {
			if ( !extra_clause ) {
				cerr << "Warning[WCNF_Formula]: extra clauses beyond stated!" << endl;
				extra_clause = true;
			}
			unsigned len = Read_Clause( p, lits );
			_clauses.push_back( Clause( lits, len ) );
		}
		else {
			cerr << "ERROR[WCNF_Formula]: invalid information!" << endl;
			exit( 1 );
		}
	}
	delete [] lits;
	Remove_Zero();
}

bool WCNF_Formula::Get_Line_MiniC2D( istream & fin, char line[] )
{
	while ( !fin.eof() ) {
		fin.getline( line, MAX_LINE );
		if ( line[0] == 'c' ) {
			char * p = line + 1;
			if ( !Read_String_Change( p, "weights") ) continue;
			if ( !_weights.empty() ) {
				cerr << "ERROR[WCNF_Formula]: weights appeared!" << endl;
				exit( 0 );
			}
			_weights.resize( 2 * _max_var + 2 );  //
			for ( unsigned i = 0; i < 2 * Num_Vars(); i++ ) {
				_weights[i + Literal::start] = Read_Float_Change( p );
			}
			continue;
		}
		char * p = line;
		while ( BLANK_CHAR_GENERAL( *p ) ) p++;
		if ( *p == '\0' ) continue;
		return true;
	}
	return false;
}

void WCNF_Formula::Remove_Zero()
{
	if ( _weights.empty() ) {
		_weights.resize( 2 * _max_var + 2 );  //
		for ( unsigned i = 0; i <= _max_var;i++ ) {
			_weights[i + i] = 1;
			_weights[i + i + 1] = 1;
		}
	}
	else {
		for ( Variable i = Variable::start; i <= _max_var;i++ ) {
			if ( _weights[i + i] == 0 ) {
				if ( _weights[i + i + 1] == 0 ) {
					cerr << "ERROR[WCNF_Formula]: zero weight!" << endl;
					exit( 1 );
				}
				Add_Unary_Clause( Literal( i, true ) );
			}
			else if ( _weights[i + i + 1] == 0 ) {
				Add_Unary_Clause( Literal( i, false ) );
			}
		}
	}
}

WCNF_Formula::WCNF_Formula( Random_Generator & rand_gen, unsigned num_var, unsigned num_cl, unsigned min_len, unsigned max_len ) :
CNF_Formula( rand_gen, num_var, num_cl, min_len, max_len )
{
	_weights.resize( 2 * _max_var + 2 );
	for ( Variable i = Variable::start; i <= _max_var;i++ ) {
		_weights[Literal( i, false )] = rand_gen.Generate_Double() * 2;
		_weights[Literal( i, true )] = 2 - _weights[Literal( i, false )];
	}
}

void WCNF_Formula::Display( ostream & out, unsigned format )
{
	if ( _max_var < Variable::start ) {
		cerr << "ERROR[CNF_Formula]: Invalid formula!"<< endl;
		return;
	}
	out << "p wcnf " << Num_Vars() << ' ' << _clauses.size() << endl;
	if ( format == 0 ) {
		for ( Literal l = Literal::start; l <= 2 * Max_Var() + 1; l++ ) {
			if ( _weights[l] != 1 ) {
				out << "w " << ExtLit( l ) << ' ' << _weights[l] << " 0" << endl;
			}
		}
	}
	if ( format == 1 ) {
		out << "c weights";
		for ( Literal i = Literal::start; i <= 2 * Max_Var() + 1; i++ ) {
			out << ' ' << _weights[i];
		}
		out << endl;
	}
	for ( unsigned i = 0; i < _clauses.size(); i++ ) {
		out << _clauses[i] << endl;
	}
	return;
}

ostream & operator << ( ostream & out, WCNF_Formula & cnf )
{
	if ( cnf._max_var < Variable::start ) {
		cerr << "ERROR[CNF_Formula]: Invalid formula!"<< endl;
		return out;
	}
	out << "c t wmc" << endl;
	out << "p cnf " << cnf.Num_Vars() << ' ' << cnf._clauses.size() << endl;
	for ( Literal l = Literal::start; l <= 2 * cnf.Max_Var() + 1; l++ ) {
		if ( cnf._weights[l] != 1 ) {
			out << "c p weight " << ExtLit( l ) << ' ' << cnf._weights[l] << " 0" << endl;
		}
	}
	for ( unsigned i = 0; i < cnf._clauses.size(); i++ ) {
		out << cnf[i] << endl;
	}
	return out;
}

BigFloat Count_Models_ADDMC( WCNF_Formula & wcnf )
{
	ofstream fout( "solvers/addmc-input.txt" );
	fout << wcnf;
	fout.close();
	system( "solvers/addmc --cf solvers/addmc-input.txt > solvers/addmc-output.txt" );
	BigFloat result;
	ifstream fin( "solvers/addmc-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		if ( line[0] != 's' ) continue;
		char *p = line + 1;
		if ( Read_String_Change( p, "wmc" ) ) {
			sscanf( p, result );
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR: addmc did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}


}
