#include "Solver.h"
#include <sys/sysinfo.h>


namespace KCBox {


const Reason Reason::mismatched( UNSIGNED_UNDEF - 1, 1 );  // UNSIGNED_UNDEF - 2
const Reason Reason::unknown( UNSIGNED_UNDEF, 0 );  // UNSIGNED_UNDEF - 1
const Reason Reason::undef( UNSIGNED_UNDEF, 1 );  // UNSIGNED_UNDEF

Solver::Solver():
_old_num_long_clauses( 0 ),
_heur_lits_heap( Literal::start, _heur_decaying_sum ),
_big_clause( 0 ),
_big_learnt( 0 )
{
}

Solver::~Solver()
{
	if ( _max_var != Variable::undef || Is_Oracle_Mode() ) Free_Auxiliary_Memory();
	if ( _max_var == Variable::undef && Is_Oracle_Mode() ) {
//		Decision_Manager::Free_Auxiliary_Memory();
	}
}

void Solver::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when mv < max_var
{
	if ( Is_Oracle_Mode() ) {
		assert( max_var <= running_options.variable_bound );
		_max_var = max_var;
		return;
	}
	if ( running_options.profile_solving != Profiling_Close ) statistics.Init_Solver();
	if ( _max_var == max_var ) return;  /// to make the recursive calls from inherited classes correct
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	Decision_Manager::Allocate_and_Init_Auxiliary_Memory( max_var );
	_binary_clauses = new vector<Literal> [2 * _max_var + 2];
	_old_num_binary_clauses = new unsigned [2 * _max_var + 2];
	_long_watched_lists = new vector<unsigned> [2 * _max_var + 2];
	_var_seen = new bool [_max_var + 2];  // The last bit is used to mark max_var + 1 not assigned
	_lit_seen = new bool [2 * _max_var + 4];  // The last two bits are used to mark 2*max_var + 2 and 2*max_var + 3 not assigned
	_heur_decaying_sum = new double [2 * _max_var + 4];  // heur_value[0] and heur_value[1] is sometimes used to reduce the number of iteration	}
	_heur_sorted_lits = new Literal [2 * _max_var + 4];  // "heur_lits[2 * max_var + 2]" and "heur_lits[2 * max_var + 3]" is sometimes used to reduce the number of iteration
	_heur_lits_heap.Enlarge_Index( 2 * _max_var + 1, _heur_decaying_sum );
	_var_rank = new unsigned [2 * _max_var + 2];
	_big_clause.Reserve( 2 * NumVars( _max_var ) );  /// NOTE: avoid overflow with tautology
	_big_learnt.Reserve( _max_var );  // used in learning conflict
	if ( Hyperscale_Problem() ) _model_pool = new Model_Pool( _max_var, 1 );
	else if ( Large_Scale_Problem() ) _model_pool = new Model_Pool( _max_var, _max_var );
	else _model_pool = new Model_Pool( _max_var, 10 * _max_var );
	/// Init
	_no_instance = true;
	for ( unsigned i = 0; i < Variable::start; i++ ) {
		_var_seen[i] = false;  // _var_seen is sometimes used for indices
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = 0;
		_old_num_binary_clauses[i + i + 1] = 0;
		_var_seen[i] = false;
		_lit_seen[i + i] = false;
		_lit_seen[i + i + 1] = false;
	}
	_var_seen[max_var + 1] = false;
	_lit_seen[2 * max_var + 2] = false;
	_lit_seen[2 * max_var + 3] = false;
}

void Solver::Free_Auxiliary_Memory()  // NOTE: only called in Allocate_and_Init_Auxiliary_Memory
{
	delete [] _binary_clauses;
	delete [] _old_num_binary_clauses;
	delete [] _long_watched_lists;
	delete [] _var_seen;  // The last bit is used to mark max_var + 1 not assigned
	delete [] _lit_seen;  // The last two bits are used to mark 2*max_var + 2 and 2*max_var + 3 not assigned
	delete [] _heur_decaying_sum;  // heur_value[0] and heur_value[1] is sometimes used to reduce the number of iteration	}
	delete [] _heur_sorted_lits;  // "heur_lits[2 * max_var + 2]" and "heur_lits[2 * max_var + 3]" is sometimes used to reduce the number of iteration
	delete [] _var_rank;
	delete _model_pool;
}

void Solver::Reset()
{
	Decision_Manager::Reset();  /// if we detect some implied literals, we need to initialize them for other callings
	_no_instance = true;
	_unary_clauses.clear();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
 		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
		lit = Literal( i, true );
 		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
	}
	_old_num_long_clauses = 0;
	vector<Clause>::iterator itr = _long_clauses.begin();
	vector<Clause>::iterator end = _long_clauses.end();
	for ( ; itr < end; itr++ ) itr->Free();
	_long_clauses.clear();
}

void Solver::operator = ( Solver & another )
{
	Allocate_and_Init_Auxiliary_Memory( another._max_var );
	Decision_Manager::operator=( another);
	_no_instance = another._no_instance;
	_unary_clauses = another._unary_clauses;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		_binary_clauses[lit] = another._binary_clauses[lit];
		_old_num_binary_clauses[lit] = another._old_num_binary_clauses[lit];
		_long_watched_lists[lit] = another._long_watched_lists[lit];
		lit = Literal( i, true );
		_binary_clauses[lit] = another._binary_clauses[lit];
		_old_num_binary_clauses[lit] = another._old_num_binary_clauses[lit];
		_long_watched_lists[lit] = another._long_watched_lists[lit];
	}
	_old_num_long_clauses = another._old_num_long_clauses;
	for ( Clause & clause: another._long_clauses ) {
		_long_clauses.push_back( clause.Copy() );
	}
	_clause_status = another._clause_status;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_sorted_lits[i + i - Literal::start] = another._heur_sorted_lits[i + i - Literal::start];
		_heur_sorted_lits[i + i + 1 - Literal::start] = another._heur_sorted_lits[i + i + 1 - Literal::start];
		_heur_decaying_sum[i + i] = another._heur_decaying_sum[i + i];
		_heur_decaying_sum[i + i + 1] = another._heur_decaying_sum[i + i + 1];
	}
	_heur_lit_sentinel = Literal( _max_var.Next(), false );
	_heur_sorted_lits[2 * _max_var + 2 - Literal::start] = _heur_lit_sentinel;  // NOTE: this line guarantee the correctness of "Branch"
	_heur_sorted_lits[2 * _max_var + 3 - Literal::start] = ~_heur_lit_sentinel;
	_heur_decaying_sum[_heur_lit_sentinel] = -1;  /// NOTE: to speed up Branch and Branch_Component by using only one comparison in for-loop
	_heur_decaying_sum[~_heur_lit_sentinel] = -2;  /// NOTE: return 2 * _max_var + 2 exactly when all variables are assigned
	if ( running_options.sat_heur_lits == Heuristic_Literal_Heap ) {
		_heur_lits_heap.Build( _heur_sorted_lits, 2 * NumVars( _max_var ) );
	}
	*_model_pool = *another._model_pool;
	running_options = another.running_options;
	debug_options = another.debug_options;
}

void Solver::Open_Oracle_Mode( Variable var_bound )
{
	Allocate_and_Init_Auxiliary_Memory( var_bound );
	running_options.variable_bound = var_bound;  /// Allocate_and_Init_Auxiliary_Memory will use running_options.bounded_problem_mode, so please don't change the calling order
	running_options.display_solving_process = false;
}

void Solver::Close_Oracle_Mode()
{
	running_options.variable_bound = Variable::undef;
}

bool Solver::Solve( CNF_Formula & cnf, vector<Model *> & models )
{
	if ( running_options.display_solving_process ) {
		cout << running_options.display_prefix << "Number of original variables: " << cnf.Num_Vars() << endl;
		cout << running_options.display_prefix << "Number of original clauses: " << cnf.Num_Clauses() << endl;
	}
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( !Load_Instance( cnf ) ) {
		Un_BCP( 0 );
		return false;
	}
	Gather_Infor_For_SAT();
	Extend_New_Level();  // to store initialized implied literals
	bool sat = Solve( models );
	Backtrack();
	Reset();
	if ( debug_options.verify_satisfiability ) Verify_Satisfiability( cnf, sat );
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_solving_process ) {
		Display_Statistics( cout );
	}
	if ( running_options.display_solving_process ) {
		if ( sat ) cout << "s SATISFIABLE" << endl;
		else cout << "s UNSATISFIABLE" << endl;
	}
	return sat;
}

bool Solver::Load_Instance( CNF_Formula & cnf )
{
	unsigned i, j;
	_clause_status.assign( cnf.Num_Clauses(), false );  // Annotate: the bit true means that the corresponding clause is blocked
	for ( i = 0; i < cnf.Num_Clauses(); i++ ) {
		Clause & clause = cnf[i];
		_big_clause.Clear();
		for ( j = 0; j < clause.Size(); j++ ) {
			if ( _lit_seen[clause[j]] ) continue;
			else if ( _lit_seen[~clause[j]] ) break;
			else {
				_big_clause.Add_Lit( clause[j] );
				_lit_seen[clause[j]] = true;
			}
		}
		if ( j < clause.Size() ) { // Annotate: tautology
			_lit_seen[_big_clause[0]] = false;
			for ( j = 1; j < _big_clause.Size(); j++ ) _lit_seen[_big_clause[j]] = false;
			_clause_status[i] = true;
			continue;
		}
		if ( _big_clause.Size() == 1 ) {
			_lit_seen[_big_clause[0]] = false;
			if ( Lit_Undecided( _big_clause[0] ) ) {
				_unary_clauses.push_back( _big_clause[0] );
				Assign( _big_clause[0] );
				clause[0] = _big_clause[0];
				clause.Shrink( 1 );
			}
			else if ( Lit_UNSAT( _big_clause[0] ) ) return false;
			_clause_status[i] = true;  // Annotate: appeared previously
		}
		else {
			_lit_seen[_big_clause[0]] = false;
			clause[0] = _big_clause[0];
			_lit_seen[_big_clause[1]] = false;
			clause[1] = _big_clause[1];
			for ( j = 2; j < _big_clause.Size(); j++ ) {
				_lit_seen[_big_clause[j]] = false;
				clause[j] = _big_clause[j];
			}
			clause.Shrink( _big_clause.Size() );
		}
	}
	if ( !_unary_clauses.empty() && !Simplify_Original_Clauses_By_Unary( cnf ) ) return false;
	for ( i = 0; i < cnf.Num_Clauses(); i++ ) {  /// NOTE: load non-unary clauses here
		Clause & clause = cnf[i];
		if ( _clause_status[i] ) _clause_status[i] = false;
		else if ( clause.Size() == 2 ) Add_Binary_Clause_Naive( clause[0], clause[1] );
		else _long_clauses.push_back( clause.Copy() );  /// cannot use clause._lits because it will be free in ~CNF_Formula
	}
	_old_num_long_clauses = _long_clauses.size();
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = _binary_clauses[i + i].size();
		_old_num_binary_clauses[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
	return true;
}

bool Solver::Simplify_Original_Clauses_By_Unary( CNF_Formula & cnf )
{
	unsigned i, j;
	for ( i = 0; i < cnf.Num_Clauses(); i++ ) {
		if ( _clause_status[i] ) continue;
		Clause & clause = cnf[i];
		_long_watched_lists[clause[0]].push_back( i );
		_long_watched_lists[clause[1]].push_back( i );
		for ( j = 2; j < clause.Size(); j++ ) {
			_long_watched_lists[clause[j]].push_back( i );
		}
	}
	for ( i = 0; i < _unary_clauses.size(); i++ ) {
		Literal lit = _unary_clauses[i];
		vector<unsigned>::iterator it = _long_watched_lists[lit].begin();
		vector<unsigned>::iterator en = _long_watched_lists[lit].end();
		for ( ; it < en; it++ ) {
			_clause_status[*it] = true;
		}
		Literal lit_neg = ~lit;
		it = _long_watched_lists[lit_neg].begin();
		en = _long_watched_lists[lit_neg].end();
		for ( ; it < en; it++ ) {
			Clause & clause = cnf[*it];
			for ( j = 0; clause[j] != lit_neg; j++ ) {}
			clause.Erase_Lit( j );
			if ( clause.Size() == 1 ) {
				if ( Lit_Undecided( clause[0] ) ) {
					_unary_clauses.push_back( clause[0] );
					Assign( clause[0] );
				}
				else if ( Lit_UNSAT( clause[0] ) ) return false;  /// no need to clear _long_watched_lists
				_clause_status[*it] = true;
			}
		}
	}
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
	}
	return true;
}

void Solver::Add_Binary_Clause_Naive( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr;
	for ( itr = _binary_clauses[lit1].begin(); *itr != lit2; itr++ ) {}
	if ( itr != _binary_clauses[lit1].end() - 1 ) _binary_clauses[lit1].pop_back();
	else _binary_clauses[lit2].push_back( lit1 );
}

void Solver::Gather_Infor_For_SAT()
{
	_no_instance = false;
	Generate_Long_Watched_Lists();
	Init_Heur_Decaying_Sum();
}

void Solver::Generate_Long_Watched_Lists()
{
	unsigned i;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
	}
	vector<Clause>::iterator begin = _long_clauses.begin(), itr = begin, end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		_long_watched_lists[(*itr)[0]].push_back( itr - begin );
		_long_watched_lists[(*itr)[1]].push_back( itr - begin );
	}
}

void Solver::Generate_Long_Watched_Lists_No_Clear()
{
	vector<Clause>::iterator begin = _long_clauses.begin(), itr = begin, end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		_long_watched_lists[(*itr)[0]].push_back( itr - begin );
		_long_watched_lists[(*itr)[1]].push_back( itr - begin );
	}
}

void Solver::Init_Heur_Decaying_Sum()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_sorted_lits[i + i - Literal::start] = Literal( i, false );
		_heur_sorted_lits[i + i + 1 - Literal::start] = Literal( i, true );
		_heur_decaying_sum[i + i] = _binary_clauses[i + i].size();
		_heur_decaying_sum[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
	_heur_lit_sentinel = Literal( _max_var.Next(), false );
	_heur_sorted_lits[2 * _max_var + 2 - Literal::start] = _heur_lit_sentinel;  // NOTE: this line guarantee the correctness of "Branch"
	_heur_sorted_lits[2 * _max_var + 3 - Literal::start] = ~_heur_lit_sentinel;
	_heur_decaying_sum[_heur_lit_sentinel] = -1;  /// NOTE: to speed up Branch and Branch_Component by using only one comparison in for-loop
	_heur_decaying_sum[~_heur_lit_sentinel] = -2;  /// NOTE: return 2 * _max_var + 2 exactly when all variables are assigned
	vector<Clause>::iterator begin = _long_clauses.begin(), itr = begin, end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		_heur_decaying_sum[(*itr)[0]] += 1;
		_heur_decaying_sum[(*itr)[1]] += 1;
		_heur_decaying_sum[(*itr)[2]] += 1;
		for ( unsigned i = 3; i < itr->Size(); i++ ) _heur_decaying_sum[(*itr)[i]] += 1;
	}
	switch( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Quick_Sort_Weight_Reverse( _heur_sorted_lits, 2 * NumVars( _max_var ), _heur_decaying_sum );
		break;
	case Heuristic_Literal_Heap:
		running_options.sat_heur_cumulative_inc = 1;
		_heur_lits_heap.Build( _heur_sorted_lits, 2 * NumVars( _max_var ) );
		break;
	}
}

bool Solver::Solve( vector<Model *> & models )
{
	assert( _num_levels == 1 );
	StopWatch begin_watch;
	if ( running_options.profile_solving >= Profiling_Abstract ) begin_watch.Start();
	if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_solve++;
	unsigned lifted_sat;
	unsigned num_restart = 0;
	double restart_bound = Restart_Bound();
	while ( ( lifted_sat = Search_Solution( restart_bound ) ) == 2 ) {
		restart_bound *= running_options.sat_restart_trigger_inc;
		num_restart++;
		if ( running_options.sat_employ_external_solver && num_restart > running_options.sat_restart_max ) {
			return Solve_External( models );
		}
	}
	assert( lifted_sat <= 1 );
	if ( lifted_sat == 1 ) {
		Add_Model( models );  // Un_BCP will change _assignment
		if ( debug_options.verify_model ) Verify_Model( models.back() );
		if ( _num_levels > 1 ) Backjump( 1 );
	}
	else if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_solving >= Profiling_Abstract ) statistics.time_solve += begin_watch.Get_Elapsed_Seconds();
	return lifted_sat == 1;
}

unsigned Solver::Search_Solution( unsigned conf_limit )
{
	unsigned old_num_levels = _num_levels;
	unsigned old_size = _long_clauses.size();
	Literal branch;
	while ( ( branch = Branch() ) != _heur_lit_sentinel ) {
		Extend_New_Level();
		Assign( branch );
		Reason conf = BCP( _num_dec_stack - 1 );
		while ( conf != Reason::undef ) {
			assert( _num_levels >= old_num_levels );
			if ( _num_levels == old_num_levels ) {
				return 0;  // UNSAT
			}
			unsigned back_level = Analyze_Conflict( conf );
			if ( back_level < old_num_levels - 1 ) {
				Backjump( old_num_levels );
				return 3;  // implied literal by some previous level before \old_num_levels
			}
			Backjump( back_level + 1 );
			Assign( _big_learnt[0], Add_Learnt_Sort() );
			if ( _long_clauses.size() - old_size > conf_limit ) {
				Backjump( old_num_levels );
				return 2;  // restart
			}
			conf = BCP( _num_dec_stack - 1 );
		}
	}
	return 1;  // SAT
}

unsigned Solver::Restart_Bound()
{
	if ( !running_options.sat_restart_activate ) return UNSIGNED_UNDEF;
	else {
		switch( 2 ) {
		case 1:
			return _max_var + _old_num_long_clauses;
			break;
		case 2:
			return running_options.sat_restart_trigger_init;
			break;
		}
	}
}

Literal Solver::Branch() // TODO: we can optimize this function in a bin-search-like fashion
{
	if ( running_options.sat_heur_lits == Heuristic_Literal_Sorted_List ) {
		unsigned i;
		for ( i = 0; Lit_Decided( _heur_sorted_lits[i] ); i++ );
		return _heur_sorted_lits[i];
	}
	else {
		while ( !_heur_lits_heap.Empty() ) {
			Literal lit = _heur_lits_heap.Extract_Max();
			if ( Lit_Undecided( lit ) ) return lit;
		}
		return _heur_lit_sentinel;
	}
}

Reason Solver::BCP( unsigned start )
{
	unsigned i, j, size;
	for ( ; start < _num_dec_stack; start++ ) {
		Literal lit = ~_dec_stack[start];
		for ( i = 0, size = _binary_clauses[lit].size(); i < size; i++ ) {
			if ( Lit_UNSAT( _binary_clauses[lit][i] ) ) {
				_big_learnt[1] = _binary_clauses[lit][i];
				return Reason( lit );
			}
			else if ( Lit_Undecided( _binary_clauses[lit][i] ) ) {
				Assign( _binary_clauses[lit][i], Reason( lit ) );
			}
		}
		vector<unsigned> & watched = _long_watched_lists[lit];
		for ( i = 0, size = watched.size(); i < size; ) {
			Clause & clause = _long_clauses[watched[i]];
			if ( clause.Size() < 3 ) {
				cerr << "ERROR[Solver::BCP]: _long_clauses[" << watched[i] << "] = " << _long_clauses[watched[i]] << endl;
			}
			assert( clause.Size() >= 3 );
			if ( clause[0] == lit ) {  // let watched[i]->lits[1] be lit, *itr can only propagate watched[i]->lits[0]
				clause[0] = clause[1];
				clause[1] = lit;
			}
			if ( Lit_SAT( clause[0] ) ) {
				i++;
				continue;
			}
			bool unit;  // itr is changed in the following loop, we cannot replace unit by j == watched[i]->len
			Literal li = clause[2];
			if ( !Lit_UNSAT( li ) ) {  // l is not falsified
				unit = false;
				clause[2] = clause[1];
				clause[1] = li;
				_long_watched_lists[li].push_back( watched[i] );
				Simply_Erase_Vector_Element( watched, i, size );
			}
			else {
				unit = true;
				for ( j = 3; j < clause.Size(); j++ ) {
					li = clause[j];
					if ( !Lit_UNSAT( li ) ) {  // l is not falsified
						unit = false;
						clause[j] = clause[1];
						clause[1] = li;
						_long_watched_lists[li].push_back( watched[i] );
						Simply_Erase_Vector_Element( watched, i, size );
						break;
					}
				}
			}
			if ( unit ) {
				if ( Lit_Decided( clause[0] ) ) {
					_big_learnt[1] = clause[0];
					return Reason( watched[i], SAT_REASON_CLAUSE );  // (*itr)->lits[0] is falsified
				}
				else {
					Assign( clause[0], Reason( watched[i], SAT_REASON_CLAUSE ) );
					i++;
				}
			}
		}
	}
	return Reason::undef;
}

void Solver::Un_BCP( unsigned start )
{
	while ( _num_dec_stack > start ) {
		_assignment[_dec_stack[--_num_dec_stack].Var()] = lbool::unknown;
	}
}

void Solver::Backjump( unsigned num_kept_levels )
{
	assert( num_kept_levels <= _num_levels );
	_num_levels = num_kept_levels;
	for ( ; _num_dec_stack > _dec_offsets[_num_levels]; _num_dec_stack-- ) {
		Literal lit = _dec_stack[_num_dec_stack - 1];
		Un_Assign( lit.Var() );
		if ( running_options.sat_heur_lits == Heuristic_Literal_Heap ) _heur_lits_heap.Insert( lit );
	}
}

unsigned Solver::Analyze_Conflict( Reason confl )
{
//	if ( _assignment[1] == 0 && _assignment[2] == 0 && _assignment[3] == 0 && _assignment[4] == 1 && _assignment[5] == 1 && _assignment[6] == 0 ) {
//		Compile_Top_Down_Display_Clauses( cout, true );
//		Compile_Top_Down_Display_Watched_List( cout );
//	}
	unsigned i, j, k, num_ip = 0;
	Variable var = _big_learnt[1].Var();
	_var_seen[var] = true;
	if ( _var_stamps[var] + 1 == _num_levels ) {
		_big_learnt.Resize( 1 );
		num_ip++;
	}
	else _big_learnt.Resize( 2 );  /// _big_learnt[1] is reserved
	assert( confl != Reason::undef );  // ToRemove
	if ( confl.Is_Clause_Reason() ) {  /// SAT_IS_REASON_LONG( Reason::undef ) is true but this situation will not appear
		Clause & clause = _long_clauses[confl.Clause_Value()];
		assert( _big_learnt[1] == clause[0] );
		var = clause[1].Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
		else _big_learnt.Add_Lit( clause[1] );
		var = clause[2].Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
		else _big_learnt.Add_Lit( clause[2] );
		for ( i = 3; i < clause.Size(); i++ ) {
			var = clause[i].Var();
			_var_seen[var] = true;
			if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
			else _big_learnt.Add_Lit( clause[i] );
		}
	}
	else {
		var = confl.Lit_Value().Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
		else _big_learnt.Add_Lit( confl.Lit_Value() );
	}
	unsigned index = _num_dec_stack - 1;
	while ( !_var_seen[_dec_stack[index].Var()] ) index--;
	Literal uip = _dec_stack[index--];
	confl = _reasons[uip.Var()];
	_var_seen[uip.Var()] = false;
	num_ip--;
	while ( num_ip > 0 ) {
		assert( confl != Reason::undef );  // ToRemove
		if ( confl.Is_Clause_Reason() ) {
			Clause & clause = _long_clauses[confl.Clause_Value()];
			assert( uip == clause[0] );
			var = clause[1].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
				else _big_learnt.Add_Lit( clause[1] );
			}
			var = clause[2].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
				else _big_learnt.Add_Lit( clause[2] );
			}
			for ( i = 3; i < clause.Size(); i++ ) {
				var = clause[i].Var();
				if ( !_var_seen[var] ) {
					_var_seen[var] = true;
					if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
					else _big_learnt.Add_Lit( clause[i] );
				}
			}
		}
		else {
			var = confl.Lit_Value().Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 == _num_levels ) num_ip++;
				else _big_learnt.Add_Lit( confl.Lit_Value() );
			}
		}
		while ( !_var_seen[_dec_stack[index].Var()] ) index--;
		uip = _dec_stack[index--];
		confl = _reasons[uip.Var()];
		_var_seen[uip.Var()] = false;
		num_ip--;
	}
	_big_learnt[0] = ~uip;
	_big_clause.Clear();
	for ( j = i = 1; i < _big_learnt.Size(); i++ ) {  /// simplify _big_learnt
		var = _big_learnt[i].Var();
		if ( _reasons[var] == Reason::undef ) _big_learnt[j++] = _big_learnt[i];
		else {
			if ( _reasons[var].Is_Clause_Reason() ) {
				Clause & clause = _long_clauses[_reasons[var].Clause_Value()];
				if ( !_var_seen[clause[1].Var()] ) _big_learnt[j++] = _big_learnt[i];
				else {
					bool tmp_seen = _var_seen[clause.Last_Lit().Var()];
					_var_seen[clause.Last_Lit().Var()] = false;
					for ( k = 2; _var_seen[clause[k].Var()]; k++ );
					_var_seen[clause.Last_Lit().Var()] = tmp_seen;
					if ( _var_seen[clause[k].Var()] ) _big_clause.Add_Lit( _big_learnt[i] );
					else _big_learnt[j++] = _big_learnt[i];
				}
			}
			else {
				if ( _var_seen[_reasons[var].Lit_Value().Var()] ) _big_clause.Add_Lit( _big_learnt[i] );
				else _big_learnt[j++] = _big_learnt[i];
			}
		}
	}
	assert( ( j + _big_clause.Size() ) == _big_learnt.Size() );
	_big_learnt.Resize( j );
	for ( i = 0; i < _big_clause.Size(); i++ ) _var_seen[_big_clause[i].Var()] = false;
	_var_seen[_big_learnt[0].Var()] = false;
 	assert( Lit_Decided( _big_learnt[0] ) );
	if ( _big_learnt.Size() == 1 ) return 0;
	_var_seen[_big_learnt[1].Var()] = false;
	assert( Lit_Decided( _big_learnt[1] ) );
	unsigned max = 1;
	for ( i = 2; i < _big_learnt.Size(); i++ ) {
		_var_seen[_big_learnt[i].Var()] = false;
		assert( Lit_Decided( _big_learnt[i] ) );
		if ( _var_stamps[_big_learnt[i].Var()] > _var_stamps[_big_learnt[max].Var()] )
			max = i;
	}
	Literal lit = _big_learnt[max];
	_big_learnt[max] = _big_learnt[1];
	_big_learnt[1] = lit;
	return _var_stamps[lit.Var()]; // I should check this line!
}

inline Reason Solver::Add_Learnt_Sort()
{
	Reason reason;
	if ( _big_learnt.Size() == 1 ) return Reason::undef;
	else if ( _big_learnt.Size() == 2 ) {
		_binary_clauses[_big_learnt[0]].push_back( _big_learnt[1] );
		_binary_clauses[_big_learnt[1]].push_back( _big_learnt[0] );
		reason = Reason( _big_learnt[1] );
	}
	else {
		_long_watched_lists[_big_learnt[0]].push_back( _long_clauses.size() );
		_long_watched_lists[_big_learnt[1]].push_back( _long_clauses.size() );
		reason = Reason( _long_clauses.size(), SAT_REASON_CLAUSE );
		_long_clauses.push_back( Clause( _big_learnt ) );  // allocate memory
	}
	Update_Heur_Decaying_Sum();
	return reason;
}

void Solver::Update_Heur_Decaying_Sum()
{
    switch ( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Update_Heur_Decaying_Sum_Sorted_List();
		break;
	case Heuristic_Literal_Heap:
		Update_Heur_Decaying_Sum_Heap();
		break;
    }
}

void Solver::Update_Heur_Decaying_Sum_Sorted_List()  // input information is store in _big_learnt
{
	unsigned i, j, k, l;
	for ( i = 0; i < _big_learnt.Size(); i++ ) {
		assert( _big_learnt[i] <= 2 * _max_var + 1 );
		assert( !_lit_seen[_big_learnt[i]] );
		_lit_seen[_big_learnt[i]] = true;
	}
	const double sentinel_weight = _heur_decaying_sum[_heur_lit_sentinel];
	_heur_decaying_sum[_heur_lit_sentinel] = _heur_decaying_sum[_heur_sorted_lits[0]] + 2;  /// for the next loop termination
	_big_clause.Resize( _big_learnt.Size() + 1 );
	_big_clause.Last_Lit() = _heur_lit_sentinel;
	j = k = _big_learnt.Size();
	l = 2 * ( _max_var - Variable::start + 1 ) - 1;  /// last position of heur_lits
	for ( i = l; i != UNSIGNED_UNDEF; i-- ) {
		_heur_decaying_sum[_heur_sorted_lits[i]] *= running_options.sat_heur_decay_factor;
		if ( _lit_seen[_heur_sorted_lits[i]] ) {
			_heur_decaying_sum[_heur_sorted_lits[i]] += 1;
			_big_clause[j--] = _heur_sorted_lits[i];
			_big_clause[j] = _heur_lit_sentinel;
			assert( j <= _max_var );//////////
		}
		else {
			while ( _heur_decaying_sum[_big_clause[k]] <= _heur_decaying_sum[_heur_sorted_lits[i]] ) {
				_heur_sorted_lits[l--] = _big_clause[k--];
			}
			_heur_sorted_lits[l--] = _heur_sorted_lits[i];
		}
		//		Compile_Top_Down_Display_SAT_Heuristic_Value( cout );
	}
	while ( k > 0 ) {
		assert( l <= _max_var + 1 );  /// cannot put it outside the loop because l might be equal to UNSIGNED_UNDEF
		_heur_sorted_lits[l--] = _big_clause[k--];
	}
	_heur_decaying_sum[_heur_lit_sentinel] = sentinel_weight;
	for ( i = 0; i < _big_learnt.Size(); i++ ) {
		_lit_seen[_big_learnt[i]] = false;
	}
}

void Solver::Update_Heur_Decaying_Sum_Heap()  // input information is store in _big_learnt
{
/*	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_decaying_sum[Literal( i, false )] *= running_options.sat_heur_decay_factor;
		_heur_decaying_sum[Literal( i, true )] *= running_options.sat_heur_decay_factor;
	}
	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		_heur_decaying_sum[_big_learnt[i]] += 1;
		_heur_lits_heap.Prioritize( _big_learnt[i] );
	}*/
	running_options.sat_heur_cumulative_inc *= ( 1 / running_options.sat_heur_decay_factor );
	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		Bump_Heur_Lit( _big_learnt[i] );
	}
}

void Solver::Bump_Heur_Lit( Literal lit )
{
	_heur_decaying_sum[lit] += running_options.sat_heur_cumulative_inc;
	if ( _heur_decaying_sum[lit] > running_options.sat_heur_bound ) {
		Rescale_Heur_Decaying_Sum();
	}
    _heur_lits_heap.Prioritize( lit );
}

void Solver::Rescale_Heur_Decaying_Sum()
{
	ASSERT( running_options.sat_heur_lits == Heuristic_Literal_Heap );
	if ( running_options.display_solving_process && running_options.profile_solving != Profiling_Close ) {
		cout << running_options.display_prefix << "rescale" << endl;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_decaying_sum[Literal( i, false )] /= running_options.sat_heur_bound;
		_heur_decaying_sum[Literal( i, true )] /= running_options.sat_heur_bound;
	}
	running_options.sat_heur_cumulative_inc /= running_options.sat_heur_bound;
}

bool Solver::Solve_External( vector<Model *> & models )
{
	StopWatch watch;
	size_t i;
	if ( running_options.profile_solving >= Profiling_Detail ) watch.Start();
	if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_external_solve++;
	vector<vector<int>> clauses;
	Prepare_Ext_Clauses( clauses );
	_minisat_extra_output.return_model = true;
	_minisat_extra_output.return_units = true;
	_minisat_extra_output.return_learnt_max_len = 2;
	int8_t result = Minisat::Ext_Solve( clauses, _minisat_extra_output );
	if ( result == 1 ) {
		for ( i = 0; i < _minisat_extra_output.units.size(); i++ ) {
			Literal lit = InternLit( _minisat_extra_output.units[i] );
			if ( Lit_Undecided( lit ) ) {
				Assign( lit );
				BCP( _num_dec_stack - 1 );
			}
		}
		for ( i = 0; i < _minisat_extra_output.short_learnts[0].size(); i += 2 ) {
			Add_Binary_Clause_Naive( InternLit( _minisat_extra_output.short_learnts[0][i] ), InternLit( _minisat_extra_output.short_learnts[0][i+1] ) );
		}
		assert( _minisat_extra_output.models.size() == 1 );
		Add_Model( _minisat_extra_output.models.front(), models );
		_minisat_extra_output.models.clear();
	}
	else if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_solving >= Profiling_Detail ) statistics.time_external_solve += watch.Get_Elapsed_Seconds();
	return result == 1;
}

void Solver::Prepare_Ext_Clauses( vector<vector<int>> & clauses )
{
	vector<int> ext_clause(1);
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		ext_clause[0] = ExtLit( _dec_stack[i] );
		clauses.push_back( ext_clause );
	}
	ext_clause.resize(2);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) continue;
		Literal lit = Literal( i, false );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			ext_clause[1] = ExtLit( lit2 );
			clauses.push_back( ext_clause );
		}
		lit = Literal( i, true );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			ext_clause[1] = ExtLit( lit2 );
			clauses.push_back( ext_clause );
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		ext_clause.clear();
		unsigned j;
		for ( j = 0; j < _long_clauses[i].Size(); j++ ) {
			Literal lit = _long_clauses[i][j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) continue;
			ext_clause.push_back( ExtLit( lit ) );
		}
		if ( j == _long_clauses[i].Size() ) clauses.push_back( ext_clause );
	}
	if ( DEBUG_OFF ) {
		for ( unsigned i = 0; i < clauses.size(); i++ ) {  // ToRemove
			for ( unsigned j = 0; j < clauses[i].size(); j++ ) {  // ToRemove
				if ( InternLit( clauses[i][j] ) > _max_var ) {  // ToRemove
					cerr << "clauses[" << i << "][" << j << "] = " << clauses[i][j] << endl;
					assert( InternLit( clauses[i][j] ) <= _max_var );
				}
			}  // ToRemove
		}  // ToRemove
	}
}

void Solver::Add_Model( vector<int8_t> & minisat_model, vector<Model *> & models )
{
	Model * model = _model_pool->Allocate();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		model->Assign( i, minisat_model[ExtVar( i )] == 1 );
	}
	if ( DEBUG_OFF ) Verify_Model( model );  // ToModify
	models.push_back( model );
}

void Solver::Add_Model( vector<Model *> & models )
{
	Model * model = _model_pool->Allocate();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		model->Assign( i, _assignment[i] == true );
	}
	models.push_back( model );
}

Reason Solver::Search_Solution_Component( Component & comp, unsigned conf_limit )
{
	unsigned old_num_levels = _num_levels;
	assert( old_num_levels >= 3 );  /// required all initialized implied literals are pulled out
	unsigned old_size = _long_clauses.size();
	unsigned max_learnts = 4 * ( comp.Vars_Size() + 1 + old_size );
	Literal branch;
	while ( ( branch = Branch_Component( comp ) ) != _heur_lit_sentinel ) {
		Extend_New_Level();
		Assign( branch );
		Reason conf = BCP( _num_dec_stack - 1 );
		while ( conf != Reason::undef ) {
			assert( _num_levels >= old_num_levels );
			if ( _num_levels == old_num_levels ) {
				return conf;  // UNSAT
			}
			unsigned back_level = Analyze_Conflict( conf );
			assert( _big_learnt.Size() > 1 && back_level >= old_num_levels - 2 );  /// required all initialized implied literals are pulled out
			if ( back_level < old_num_levels - 1 ) {
				Backjump( old_num_levels );
				return Reason::mismatched;  // implied literal by some previous level before \old_num_levels
			}
			Backjump( back_level + 1 );
			Assign( _big_learnt[0], Add_Learnt_Sort_Component( comp ) );
			if ( _long_clauses.size() - old_size > conf_limit ) {
				Backjump( old_num_levels );
				return Reason::unknown;  // restart
			}
			conf = BCP( _num_dec_stack - 1 );
		}
		if ( _long_clauses.size() - old_size - _num_dec_stack >= max_learnts && max_learnts < UNSIGNED_UNDEF / 2 ) {
			Filter_Long_Learnts_During_Solving( old_num_levels - 1, old_size );
			max_learnts *= 2;
		}
	}
	return Reason::undef;  // SAT
}

unsigned Solver::Restart_Bound_Component( Component & comp )
{
//	return UNSIGNED_UNDEF;
	switch( 2 ) {
	case 1:
		return comp.Vars_Size() - 2 + comp.ClauseIDs_Size();
		break;
	case 2:
		return running_options.sat_restart_trigger_init;
		break;
	}
}

Reason Solver::Add_Learnt_Sort_Component( Component & comp )
{
	if ( debug_options.verify_learnts ) Verify_Learnt( _big_learnt );
	Reason reason;
	if ( _big_learnt.Size() == 2 ) {
		_binary_clauses[_big_learnt[0]].push_back( _big_learnt[1] );
		_binary_clauses[_big_learnt[1]].push_back( _big_learnt[0] );
		reason = Reason( _big_learnt[1] );
	}
	else {
		assert( _big_learnt.Size() >= 3 );  // all initialized implied were pulled out
		_long_watched_lists[_big_learnt[0]].push_back( _long_clauses.size() );
		_long_watched_lists[_big_learnt[1]].push_back( _long_clauses.size() );
		reason = Reason( _long_clauses.size(), SAT_REASON_CLAUSE );
		_long_clauses.push_back( Clause( _big_learnt ) );
	}
/*	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		assert( Literal::start <= _big_learnt[i] && _big_learnt[i] <= 2 * _max_var + 1 );
		assert( !_lit_seen[_big_learnt[i]] );
		_heur_decaying_sum[_big_learnt[i]] += 1 / running_options.sat_heur_decay_factor;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_decaying_sum[i + i] *= running_options.sat_heur_decay_factor;
		_heur_decaying_sum[i + i + 1] *= running_options.sat_heur_decay_factor;
	}*/
	Update_Heur_Decaying_Sum_Component( comp );
	return reason;
}

void Solver::Update_Heur_Decaying_Sum_Component( Component & comp )  // input information is store in _big_learnt
{
    switch ( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Update_Heur_Decaying_Sum_Sorted_List_Component( comp );
		break;
	case Heuristic_Literal_Heap:
		Update_Heur_Decaying_Sum_Heap();
//		Update_Heur_Decaying_Sum_Heap_Component( comp );
		break;
    }
}

void Solver::Update_Heur_Decaying_Sum_Sorted_List_Component( Component & comp )  // input information is store in _big_learnt
{
	unsigned i, j, k, l, num_effective_lits = 0;
	for ( i = 0; i < _big_learnt.Size(); i++ ) {
		assert( _big_learnt[i] <= 2 * _max_var + 1 );
		assert( !_lit_seen[_big_learnt[i]] );
		if ( comp.Search_Var( _big_learnt[i].Var() ) ) {
			_lit_seen[_big_learnt[i]] = true;
			num_effective_lits++;
		}
	}
	const double sentinel_weight = _heur_decaying_sum[_heur_lit_sentinel];
	_heur_decaying_sum[_heur_lit_sentinel] = _heur_decaying_sum[_heur_sorted_lits[0]] + 2;  /// for the next loop termination
	_big_clause.Resize( num_effective_lits + 1 );
	_big_clause.Last_Lit() = _heur_lit_sentinel;
	j = k = num_effective_lits;
	l = 2 * comp.Vars_Size() - 1;  /// last position of heur_lits
	for ( i = l; i != UNSIGNED_UNDEF; i-- ) {
		_heur_decaying_sum[_heur_sorted_lits[i]] *= running_options.sat_heur_decay_factor;
		if ( _lit_seen[_heur_sorted_lits[i]] ) {
			_heur_decaying_sum[_heur_sorted_lits[i]] += 1;
			_big_clause[j--] = _heur_sorted_lits[i];
			_big_clause[j] = _heur_lit_sentinel;
			assert( j <= comp.Vars_Size() );//////////
		}
		else {
			while ( _heur_decaying_sum[_big_clause[k]] <= _heur_decaying_sum[_heur_sorted_lits[i]] ) {
				_heur_sorted_lits[l--] = _big_clause[k--];
			}
			_heur_sorted_lits[l--] = _heur_sorted_lits[i];
		}
		//		Compile_Top_Down_Display_SAT_Heuristic_Value( cout );
	}
	while ( k > 0 ) {
		assert( l <= comp.Vars_Size() + 1 );  /// cannot put it outside the loop because l might be equal to UNSIGNED_UNDEF
		_heur_sorted_lits[l--] = _big_clause[k--];
	}
	_heur_decaying_sum[_heur_lit_sentinel] = sentinel_weight;
	for ( i = 0; i < _big_learnt.Size(); i++ ) {
		_lit_seen[_big_learnt[i]] = false;
	}
}

void Solver::Update_Heur_Decaying_Sum_Heap_Component( Component & comp )  // input information is store in _big_learnt
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_heur_decaying_sum[Literal( var, false )] *= running_options.sat_heur_decay_factor;
		_heur_decaying_sum[Literal( var, true )] *= running_options.sat_heur_decay_factor;
	}
	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		_heur_decaying_sum[_big_learnt[i]] += 1;
		_heur_lits_heap.Prioritize( _big_learnt[i] );
	}
}

Literal Solver::Branch_Component( Component & comp )
{
	if ( running_options.sat_heur_lits == Heuristic_Literal_Unsorted_List ) {
		comp.Add_Var( _max_var.Next() );  /// NOTE: to terminate the following for-loop without comparing
		vector<unsigned>::const_iterator itr = comp.VarIDs_Begin();
		vector<unsigned>::const_iterator end = comp.VarIDs_End();
		Literal lit;
	//	Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
		for ( ; Var_Decided( Variable( *itr ) ); itr++ );
		if ( _heur_decaying_sum[*itr + *itr] > _heur_decaying_sum[*itr + *itr + 1] ) lit = Literal( Variable( *itr ), false );
		else lit = Literal( Variable( *itr ), true );
		for ( itr++, end--; itr < end; itr++ ) {
			if ( Var_Undecided( Variable( *itr ) ) ) {
				if ( _heur_decaying_sum[*itr + *itr] > _heur_decaying_sum[*itr + *itr + 1] ) {
					if ( _heur_decaying_sum[*itr + *itr] > _heur_decaying_sum[lit] ) lit = Literal( Variable( *itr ), false );
				}
				else {
					if ( _heur_decaying_sum[*itr + *itr + 1] > _heur_decaying_sum[lit] ) lit = Literal( Variable( *itr ), true );
				}
			}
		}
		comp.Dec_Var();  /// pop _max_var.Next()
		return lit;
	}
	else if ( running_options.sat_heur_lits == Heuristic_Literal_Sorted_List ) {
		unsigned i;
		for ( i = 0; Lit_Decided( _heur_sorted_lits[i] ); i++ );
		return _heur_sorted_lits[i];
	}
	else {
		while ( !_heur_lits_heap.Empty() ) {
			Literal lit = _heur_lits_heap.Extract_Max();
			if ( Lit_Undecided( lit ) ) return lit;
		}
		return _heur_lit_sentinel;
	}
}

void Solver::Filter_Long_Learnts_During_Solving( unsigned old_num_levels, unsigned old_size )
{
	if ( !running_options.sat_filter_long_learnts ) return;
	while ( _clause_status.size() < _long_clauses.size() ) {
		_clause_status.push_back( false );
	}
	_clause_stack.resize( _long_clauses.size() );
	for ( unsigned i = _dec_offsets[old_num_levels]; i < _num_dec_stack; i++ ) {
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef || r.Is_Lit_Reason() ) continue;  /// NOTE: SAT_IS_REASON_LONG( Reason::undef ) is true
		unsigned cl = r.Clause_Value();
		if ( cl >= old_size ) {
			_clause_status[cl] = true;
		}
	}
	unsigned new_size = old_size;
	const unsigned fixed_len = 3;
	vector<Clause>::iterator begin = _long_clauses.begin(), end = _long_clauses.end();
	for ( vector<Clause>::iterator itr = begin + old_size; itr < end; itr++ ) {
		if ( _clause_status[itr - begin] ) {
			_clause_stack[itr - begin] = new_size;
			_long_clauses[new_size++] = *itr;
		}
		else if ( itr->Size() <= fixed_len ) _long_clauses[new_size++] = *itr;
		else if ( Two_Unassigned_Literals( *itr ) ) _long_clauses[new_size++] = *itr;
		else if ( ( itr - begin ) % 2 == 0 ) _long_clauses[new_size++] = *itr;
		else itr->Free();
	}
	_long_clauses.resize( new_size ), end = _long_clauses.end();
	for ( unsigned i = _dec_offsets[old_num_levels]; i < _num_dec_stack; i++ ) {
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef || r.Is_Lit_Reason() ) continue;
		unsigned cl = r.Clause_Value();
		if ( _clause_status[cl] ) {
			_clause_status[cl] = false;
			_reasons[_dec_stack[i].Var()] = Reason( _clause_stack[cl], SAT_REASON_CLAUSE );  // update reason by new position
			assert( _long_clauses[_clause_stack[cl]][0] == _dec_stack[i] );  // ToRemove
		}
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		_long_watched_lists[x + x].clear();
		_long_watched_lists[x + x + 1].clear();
	}
	for ( vector<Clause>::iterator itr = begin; itr < end; itr++ ) {
		Clause & clause = *itr;
		_long_watched_lists[clause[0]].push_back( itr - begin );
		_long_watched_lists[clause[1]].push_back( itr - begin );
	}
}

bool Solver::Two_Unassigned_Literals( Clause & clause )
{
	assert( clause.Size() > 2 );
	if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) return false;
	Label_Value( clause.Last_Lit() );  // label last literal as SAT
	unsigned i;
	for ( i = 2; Lit_UNSAT( clause[i] ); i++ ) {}
	Un_Label_Value( clause.Last_Lit() );
	return Lit_UNSAT( clause[i] );
}

unsigned Solver::Num_Unassigned_Literals( Clause & clause )
{
	assert( clause.Size() > 2 );
	if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) return 0;
	unsigned num = 2;
	Label_Value( clause.Last_Lit() );  // label last literal as SAT
	unsigned i;
	for ( i = 2; !Lit_SAT( clause[i] ); i++ ) {
		num += Lit_Undecided( clause[i] );
	}
	Un_Label_Value( clause.Last_Lit() );
	if ( Lit_SAT( clause[i] ) ) return 0;
	else return num + Lit_Undecided( clause[i] );
}

Reason Solver::Assign_Late( unsigned level, Literal lit, Reason reason )
{
	ASSERT( !Var_Decided( lit.Var() ) && level < _num_levels && reason != Reason::undef );
	stack<Literal> old_decisions;
	while ( _num_levels > level + 1 ) {
		Backtrack();
		assert( _reasons[_dec_stack[_num_dec_stack].Var()] == Reason::undef );
		old_decisions.push( _dec_stack[_num_dec_stack] );
	}
	Assign( lit, reason );
	Reason conf = BCP( _num_dec_stack - 1);
	if ( conf != Reason::undef ) return conf;
	while ( old_decisions.size() > 1 ) {
		Extend_New_Level();
		Literal decision = old_decisions.top();
		old_decisions.pop();
		Assign( decision );
		conf = BCP( _num_dec_stack - 1);
		if ( conf != Reason::undef ) return conf;
	}
	Extend_New_Level();
	Assign( old_decisions.top() );
	return BCP( _num_dec_stack - 1);
}

unsigned Solver::Num_Clauses()
{
	unsigned i, num = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _binary_clauses[i + i].size();
		num += _binary_clauses[i + i + 1].size();
	}
	num = num / 2 + _unary_clauses.size() + _long_clauses.size();
	return num;
}

unsigned Solver::Old_Num_Clauses()
{
	unsigned i, num = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _old_num_binary_clauses[i + i];
		num += _old_num_binary_clauses[i + i + 1];
	}
	num = num / 2 + _unary_clauses.size() + _old_num_long_clauses;
	return num;
}

unsigned Solver::Old_Num_Binary_Clauses()
{
	unsigned i, num = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _old_num_binary_clauses[i + i];
		num += _old_num_binary_clauses[i + i + 1];
	}
	return num / 2;
}

unsigned Solver::Num_Learnts()
{
	unsigned i, num = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _binary_clauses[i + i].size() - _old_num_binary_clauses[i + i];
		num += _binary_clauses[i + i + 1].size() - _old_num_binary_clauses[i + i + 1];
	}
	num = num / 2 + _long_clauses.size() - _old_num_long_clauses;
	return num;
}

unsigned Solver::Num_Binary_Learnts()
{
	unsigned i, num = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _binary_clauses[i + i].size() - _old_num_binary_clauses[i + i];
		num += _binary_clauses[i + i + 1].size() - _old_num_binary_clauses[i + i + 1];
	}
	return num / 2;
}

void Solver::Verify_Satisfiability( CNF_Formula & cnf, bool result )
{
	vector<vector<int>> original_eclauses;
	cnf.ExtClauses( original_eclauses );
	int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
	assert( result == sat );
}

void Solver::Verify_Long_Learnt( unsigned pos )
{
	assert( _old_num_long_clauses <= pos && pos <= _long_clauses.size() );
	vector<vector<int>> clauses;
	vector<int> ext_clause(1);
	for ( unsigned i = 0; i < _long_clauses[pos].Size(); i++ ) {
		ext_clause[0] = -ExtLit( _long_clauses[pos][i] );
		clauses.push_back( ext_clause );
	}
	ext_clause.resize(2);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			ext_clause[1] = ExtLit( _binary_clauses[lit][j] );
			clauses.push_back( ext_clause );
		}
		lit = Literal( i, true );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			ext_clause[1] = ExtLit( _binary_clauses[lit][j] );
			clauses.push_back( ext_clause );
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		clauses.push_back( ExtLits( _long_clauses[i] ) );
	}
	assert( Minisat::Ext_Solve( clauses, _minisat_extra_output ) == 0 );
}

void Solver::Verify_Learnt( Big_Clause & learnt )
{
	vector<vector<int>> original_eclauses;
	vector<int> unary_eclause(1);
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		unary_eclause[0] = ExtLit( _unary_clauses[i] );
		original_eclauses.push_back( unary_eclause );
	}
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			original_eclauses.push_back( ExtLits( lit, _binary_clauses[lit][i] ) );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			original_eclauses.push_back( ExtLits( lit, _binary_clauses[lit][i] ) );
		}
		lit++;
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		original_eclauses.push_back( ExtLits( _long_clauses[i] ) );
	}
	for ( unsigned i = 0; i < learnt.Size(); i++ ) {
		unary_eclause[0] = -ExtLit( learnt[i] );
		original_eclauses.push_back( unary_eclause );
	}
	int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
	if ( sat != 0 ) {
		Display_Decision_Stack( cerr, _num_levels );
		cerr << "invalid learnt clause: ";
		for ( unsigned j = 0; j < learnt.Size(); j++ ) {
			cerr << ExtLit( learnt[j] ) << ' ';
		}
		cerr << "0" << endl;
		assert( sat == 0 );
	}
}

void Solver::Verify_Learnts( CNF_Formula & cnf )
{
	unsigned learnt_index = Old_Num_Clauses();
	Literal * lits = new Literal [2];
	vector<Clause> learnts;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		lits[0] = Literal( i, false );
		for ( unsigned j = _old_num_binary_clauses[i + i]; j < _binary_clauses[i + i].size(); j++ ) {
			if ( i + i > _binary_clauses[i + i][j] ) continue;
			lits[1] = _binary_clauses[i + i][j];
			learnts.push_back( Clause( lits, 2 ) );
			learnt_index++;
		}
		lits[0] = Literal( i, true );
		for ( unsigned j = _old_num_binary_clauses[i + i + 1]; j < _binary_clauses[i + i + 1].size(); j++ ) {
			if ( i + i + 1 > _binary_clauses[i + i + 1][j] ) continue;
			lits[1] = _binary_clauses[i + i + 1][j];
			learnts.push_back( Clause( lits, 2 ) );
			learnt_index++;
		}
	}
	delete [] lits;
	vector<Clause>::iterator itr = _long_clauses.begin() + _old_num_long_clauses, end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		learnts.push_back( itr->Copy() );
	}
	assert( learnts.size() == Num_Learnts() );
	for ( itr = learnts.begin(), end = learnts.end(); itr < end; itr++ ) {
		if ( !Imply_Clause_CNF_No_Learnt( cnf, *itr ) ) {
			cerr << "The following learnt clause is not implied by cnf:" << endl;
			cerr << learnt_index << ":\t";
			itr->Display( cerr );
			assert( false );
		}
		itr->Free();
		learnt_index++;
	}
}

bool Solver::Imply_Clause_CNF_No_Learnt( CNF_Formula & cnf, Clause & clause )
{
	vector<Clause>::iterator itr = _long_clauses.begin();
	vector<Clause>::iterator end = _long_clauses.end();
	for ( ; itr < end; itr++ ) itr->Free();
	_long_clauses.clear();
	_old_num_long_clauses = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_binary_clauses[i + i].clear();
		_old_num_binary_clauses[i + i] = 0;
		_long_watched_lists[i + i].clear();
		_binary_clauses[i + i + 1].clear();
		_old_num_binary_clauses[i + i + 1] = 0;
		_long_watched_lists[i + i + 1].clear();
	}
	_unary_clauses.clear();
	Load_Instance( cnf );
	for ( itr = _long_clauses.begin(), end = _long_clauses.end(); itr < end; itr++ ) {
		_long_watched_lists[(*itr)[0]].push_back( itr - _long_clauses.begin() );
		_long_watched_lists[(*itr)[1]].push_back( itr - _long_clauses.begin() );
	}
	assert( _num_dec_stack == 0 );
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		if ( Lit_Undecided( _unary_clauses[i] ) ) Assign( _unary_clauses[i] );
		else if ( _assignment[_unary_clauses[i].Var()] != _unary_clauses[i].Sign() ) {
			Un_BCP( 0 );
			return true;
		}
	}
	for ( unsigned i = 0; i < clause.Size(); i++ ) {
		if ( !Var_Decided( clause[i].Var() ) ) Assign( ~clause[i] );
		else if ( Lit_SAT( clause[i] ) ) {
			Un_BCP( 0 );
			return true;
		}
	}
	if ( BCP( 0 ) != Reason::undef ) {
		Un_BCP( 0 );
		return true;
	}
	assert( _num_levels == 0 );
	_dec_offsets[_num_levels++] = _num_dec_stack;
	while ( true ) {
		Variable i;
		for ( i = Variable::start; Var_Decided( i ); i++ );
		if ( i > _max_var ) {
			Verify_Model( cnf );
			Un_BCP( 0 );
			_num_levels = 0;
			return false;
		}
		else {
			_dec_offsets[_num_levels++] = _num_dec_stack;
			Assign( i, false, Reason::undef );
		}
		while ( BCP( _num_dec_stack - 1 ) != Reason::undef ) {
			Un_BCP( _dec_offsets[--_num_levels] );
			if ( _num_levels == 0 ) {
				Un_BCP( 0 );
				return true;
			}
			Assign( ~_dec_stack[_dec_offsets[_num_levels]] );
		}
	}
	assert( false );
	return true;
}

void Solver::Verify_Current_Imps()
{
	vector<vector<int>> clauses;
	vector<int> ext_clause(1);
	for ( unsigned i = 0; i <= _dec_offsets[_num_levels - 1]; i++ ) {
		ext_clause[0] = ExtLit( _dec_stack[i] );
		clauses.push_back( ext_clause );
	}
	ext_clause.resize(2);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit = Literal( i, false );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			ext_clause[1] = ExtLit( _binary_clauses[lit][j] );
			clauses.push_back( ext_clause );
		}
		lit = Literal( i, true );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			ext_clause[1] = ExtLit( _binary_clauses[lit][j] );
			clauses.push_back( ext_clause );
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		clauses.push_back( ExtLits( _long_clauses[i] ) );
	}
	ext_clause.resize(1);
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		ext_clause[0] = -ExtLit( _dec_stack[i] );
		clauses.push_back( ext_clause );
		if ( Minisat::Ext_Solve( clauses, _minisat_extra_output ) != 0 ) {
			Display_Decision_Stack( cerr, _num_levels - 1 );
			cerr << "ERROR[Compiler]: _dec_stack[" << i << "] = " << _dec_stack[i] << " is an invalid implied literal!" << endl;
			assert( false );
		}
		clauses.back()[0] = ExtLit( _dec_stack[i] );
	}
}

void Solver::Verify_Model( Model * model )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, !(*model)[i] );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal li = _binary_clauses[lit][j];
			if ( (*model)[li.Var()] != li.Sign() ) {
				cerr << "ERROR[Solver]: not satisfy ";
				cerr << ExtLit( lit );
				cerr << " ";
				cerr << ExtLit( li );
				cerr << endl;
			}
			assert( (*model)[li.Var()] == li.Sign() );
		}
	}
	vector<Clause>::iterator itr = _long_clauses.begin();
	vector<Clause>::iterator end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		Clause & clause = *itr;
		unsigned i;
		for ( i = 0; i < clause.Size(); i++ ) {
			if ( (*model)[clause[i].Var()] == clause[i].Sign() ) break;
		}
		if ( i == clause.Size() ) {
			cerr << "ERROR[Solver]: model is invalid!" << endl;
			for ( Variable j = Variable::start; j <= _max_var; j++ ) {
				if ( (*model)[j] == 0 ) cerr << "-";
				cerr << ExtVar( j ) << " ";
			}
			cerr << endl;
			cerr << "ERROR[Solver]: not satisfy the " << itr - _long_clauses.begin() << "th clause ";
			itr->Display( cerr );
			assert( false );
		}
	}
}

void Solver::Verify_Model( CNF_Formula & cnf )
{
	vector<Clause>::iterator itr = cnf.Clause_Begin();
	vector<Clause>::iterator end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		Clause & clause = *itr;
		unsigned i;
		for ( i = 0; i < clause.Size(); i++ ) {
			if ( Lit_SAT( clause[i] ) ) break;
		}
		if ( i == clause.Size() ) {
			cerr << "ERROR[Solver]: The following _assignment is not a model of cnf!" << endl;
			for ( Variable j = Variable::start; j <= _max_var; j++ ) {
				assert( Var_Decided( j ) );
				if ( _assignment[j] == false ) cerr << "-";
				cerr << ExtVar( j ) << " ";
			}
			cerr << endl;
			assert( false );
		}
	}
}

void Solver::Verify_Model( Model * model, CNF_Formula & cnf )
{
	unsigned num = 0;
	vector<Clause>::iterator itr = cnf.Clause_Begin();
	vector<Clause>::iterator end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		Clause & clause = *itr;
		unsigned i;
		for ( i = 0; i < clause.Size(); i++ ) {
			if ( (*model)[clause[i].Var()] == clause[i].Sign() ) break;
		}
		if ( i == clause.Size() ) {
			cerr << "ERROR[Solver]: The " << itr - cnf.Clause_Begin() << "th clause is not satisfied!" << endl;
			num++;
		}
	}
	if ( num > 0 ) {
		for ( Variable i = Variable::start; i <= _max_var; i++ ) {
			if ( !(*model)[i] ) cerr << "-";
			cerr << ExtVar( i ) << " ";
		}
		cerr << endl;
		assert( num == 0 );
	}
}

void Solver::Verify_Binary_Clauses()
{
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
		assert( _binary_clauses[lit].size() <= _max_var + 1 );
		for ( unsigned i = 0; i < _binary_clauses[lit].size(); i++ ) {
			Literal lit2 = _binary_clauses[lit][i];
			assert( lit2 <= 2 * _max_var + 1 );
			assert( lit2 != lit );
			unsigned j;
			for ( j = 0; j < _binary_clauses[lit2].size(); j++ ) {
				if ( _binary_clauses[lit2][j] == lit ) break;
			}
			if ( j == _binary_clauses[lit2].size() ) {
				cerr << "ERROR[Solver]: " << lit << " does not appear in _binary_clauses[" << lit2 << "]" << endl;
				assert( j < _binary_clauses[lit2].size() );
			}
			unsigned loc = j;
			for ( j++; j < _binary_clauses[lit2].size(); j++ ) {
				if ( _binary_clauses[lit2][j] == lit ) break;
			}
			if ( j < _binary_clauses[lit2].size() ) {
				cerr << "ERROR[Solver]: " << lit << " does not appear in _binary_clauses[" << lit2 << "] more than once!" << endl;
				assert( j == _binary_clauses[lit2].size() );
			}
			if ( i < _old_num_binary_clauses[lit] ) {
				if ( loc >= _old_num_binary_clauses[lit2] ) {
					cerr << "ERROR[Solver]: literal" << ExtLit( lit2 ) << " should be in an original binary clause with " << ExtLit( lit ) << "!" << endl;
					assert( loc < _old_num_binary_clauses[lit2] );
				}
			}
			else if ( loc < _old_num_binary_clauses[lit2] ) {
				cerr << "ERROR[Solver]: literal" << ExtLit( lit2 ) << " should be in a binary learnt clause with " << ExtLit( lit ) << "!" << endl;
				assert( loc >= _old_num_binary_clauses[lit2] );
			}
		}
	}
}

void Solver::Verify_Reasons()
{
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef || r.Is_Lit_Reason() ) continue;
		unsigned cl = r.Clause_Value();
		assert( _long_clauses[cl][0] == _dec_stack[i] );
	}
}

void Solver::Display_Statistics( ostream & out )
{
}

void Solver::Display_Clauses( ostream & out, bool all )
{
	unsigned index = 0;
	if ( !all ) out << "p cnf " << _max_var - Variable::start + 1 << ' ' << Old_Num_Clauses() << endl;
	else out << "p cnf " << _max_var - Variable::start + 1 << ' ' << Num_Clauses() << endl;
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		if ( all ) out << index++ << ":\t";
		out << ExtLit( _unary_clauses[i] ) << ' ' << '0' << endl;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		for ( unsigned j = 0; j < _old_num_binary_clauses[i + i]; j++ ) {
			if ( i + i > _binary_clauses[i + i][j] ) continue;
			if ( all ) out << index++ << ":\t";
			out << '-' << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i][j] ) << " 0" << endl;
		}
		for ( unsigned j = 0; j < _old_num_binary_clauses[i + i + 1]; j++ ) {
			if ( i + i + 1 > _binary_clauses[i + i + 1][j] ) continue;
			if ( all ) out << index++ << ":\t";
			out << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i + 1][j] ) << " 0" << endl;
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		if ( all ) out << index++ << ":\t";
		out << _long_clauses[i] << endl;
	}
	if ( !all ) return;
	out << "--------" << endl;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		for ( unsigned j = _old_num_binary_clauses[i + i]; j < _binary_clauses[i + i].size(); j++ ) {
			if ( i + i > _binary_clauses[i + i][j] ) continue;
			out << index++ << ":\t";
			out << '-' << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i][j] ) << " 0" << endl;
		}
		for ( unsigned j = _old_num_binary_clauses[i + i + 1]; j < _binary_clauses[i + i + 1].size(); j++ ) {
			if ( i + i + 1 > _binary_clauses[i + i + 1][j] ) continue;
			out << index++ << ":\t";
			out << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i + 1][j] ) << " 0" << endl;
		}
	}
	for ( unsigned i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) {
		out << index++ << ":\t";
		out << _long_clauses[i] << endl;
	}
}

void Solver::Display_Clauses_No_Learnt( ostream & out )
{
	if ( _max_var == Variable::undef ) {
		out << "No data."<< endl;
		return;
	}
	unsigned index = 0;
	out << "p cnf " << _max_var - Variable::start + 1 << ' ' << Num_Clauses() << endl;
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		out << index++ << ":\t";
		out << ExtLit( _unary_clauses[i] ) << ' ' << '0' << endl;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		for ( unsigned j = 0; j < _binary_clauses[i + i].size(); j++ ) {
			if ( i + i > _binary_clauses[i + i][j] ) continue;
			out << index++ << ":\t";
			out << '-' << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i][j] ) << " 0" << endl;
		}
		for ( unsigned j = 0; j < _binary_clauses[i + i + 1].size(); j++ ) {
			if ( i + i + 1 > _binary_clauses[i + i + 1][j] ) continue;
			out << index++ << ":\t";
			out << ExtVar( i ) << " ";
			out << ExtLit( _binary_clauses[i + i + 1][j] ) << " 0" << endl;
		}
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		out << index++ << ":\t";
		Clause & clause = _long_clauses[i];
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			out << ExtLit( clause[j] ) << ' ';
		}
		out << '0' << endl;
	}
}

void Solver::Display_Long_Clauses( ostream & out, bool all )
{
	unsigned i, j, index = 0;
	if ( !all ) out << "p cnf " << _max_var - Variable::start + 1 << ' ' << _old_num_long_clauses << endl;
	else out << "p cnf " << _max_var - Variable::start + 1 << ' ' << _long_clauses.size() << endl;
	for ( i = 0; i < _old_num_long_clauses; i++ ) {
		if ( all ) out << index++ << ":\t";
		Clause & clause = _long_clauses[i];
		for ( j = 0; j < clause.Size(); j++ ) {
			out << ExtLit( clause[j] ) << ' ';
		}
		out << '0' << endl;
	}
	if ( !all ) return;
	out << "--------" << endl;
	for ( i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) {
		out << index++ << ":\t";
		Clause & clause = _long_clauses[i];
		for ( j = 0; j < clause.Size(); j++ ) {
			out << ExtLit( clause[j] ) << ' ';
		}
		out << '0' << endl;
	}
}

void Solver::Display_Long_Clauses_No_Learnt( ostream & out )
{
	unsigned i, j, index = 0;
	out << "p cnf " << _max_var - Variable::start + 1 << ' ' << _long_clauses.size() << endl;
	for ( i = 0; i < _long_clauses.size(); i++ ) {
		out << index++ << ":\t";
		Clause & clause = _long_clauses[i];
		for ( j = 0; j < clause.Size(); j++ ) {
			out << ExtLit( clause[j] ) << ' ';
		}
		out << '0' << endl;
	}
}

void Solver::Display_Binary_Learnts( ostream & out )
{
	for ( Literal i = Literal::start; i <= 2 * _max_var + 1; i++ ) {
		out << ExtLit(i) << ":";
		for ( unsigned j = _old_num_binary_clauses[i]; j < _binary_clauses[i].size(); j++ ) {
			out << ' ' << ExtLit( _binary_clauses[i][j] );
		}
		out << endl;
	}
}

void Solver::Display_Watched_List_Naive( ostream & out )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << "-" << ExtVar( i ) << ": ";
		vector<unsigned>::iterator itr = _long_watched_lists[i + i].begin();
		vector<unsigned>::iterator end = _long_watched_lists[i + i].end();
		for ( ; itr < end; itr++ ) {
			if ( *itr < _old_num_long_clauses ) out << *itr << ' ';
			else out << *itr << ' ';
		}
		out << endl;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << ExtVar( i ) << ": ";
		vector<unsigned>::iterator itr = _long_watched_lists[i + i + 1].begin();
		vector<unsigned>::iterator end = _long_watched_lists[i + i + 1].end();
		for ( ; itr < end; itr++ ) {
			if ( *itr < _old_num_long_clauses ) out << *itr << ' ';
			else out << *itr << ' ';
		}
		out << endl;
	}
}

void Solver::Display_Watched_List( ostream & out )
{
	unsigned num_old_short = Old_Num_Clauses() - _old_num_long_clauses;  // NOTE: the number of old short clauses (unary or binary)
	unsigned num_short = Num_Clauses() - _long_clauses.size();  // NOTE: the number of short clauses (unary or binary)
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << "-" << ExtVar( i ) << ": ";
		vector<unsigned>::iterator itr = _long_watched_lists[2 * i].begin();
		vector<unsigned>::iterator end = _long_watched_lists[2 * i].end();
		for ( ; itr < end; itr++ ) {
			if ( *itr < _old_num_long_clauses ) out << *itr + num_old_short << ' ';
			else out << *itr + num_short << ' ';
		}
		out << endl;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << ExtVar( i ) << ": ";
		vector<unsigned>::iterator itr = _long_watched_lists[2 * i].begin();
		vector<unsigned>::iterator end = _long_watched_lists[2 * i].end();
		for ( ; itr < end; itr++ ) {
			if ( *itr < _old_num_long_clauses ) out << *itr + num_old_short << ' ';
			else out << *itr + num_short << ' ';
		}
		out << endl;
	}
}

void Solver::Display_SAT_Heuristic_Value( ostream & out )
{
	if ( running_options.sat_heur_lits == Heuristic_Literal_Sorted_List ) {
		for ( unsigned i = 0; i < 2 * NumVars( _max_var ); i++ ) {
			out << ExtLit( _heur_sorted_lits[i] ) << ": ";
			out << _heur_decaying_sum[_heur_sorted_lits[i]] << endl;
		}
	}
	else if ( running_options.sat_heur_lits == Heuristic_Literal_Heap ) {
		for ( unsigned i = 0; i < _heur_lits_heap.Size(); i++ ) {
			out << ExtLit( _heur_lits_heap[i] ) << ": ";
			out << _heur_decaying_sum[_heur_lits_heap[i]] << endl;
		}
	}
}

void Solver::Display_Decision_Stack( ostream & out, unsigned base_dec_level )
{
	unsigned i = 0, j = _dec_offsets[0];
	if ( 0 < base_dec_level && base_dec_level < _num_levels ) {
		for ( ; i < base_dec_level; i++ ) {
			out << "(" << i << ") ";
			for ( ; j < _dec_offsets[i + 1]; j++ ) {
				out << ExtLit( _dec_stack[j] ) << " ";
			}
		}
		out << endl;
	}
	for ( ; i < _num_levels - 1; i++ ) {
		out << "(" << i << ") ";
		for ( ; j < _dec_offsets[i + 1]; j++ ) {
			out << ExtLit( _dec_stack[j] ) << " ";
		}
	}
	out << "(" << i << ") ";
	for ( ; j < _num_dec_stack; j++ ) {
		out << ExtLit( _dec_stack[j] ) << " ";
	}
	out << endl;
}

void Solver::Display_Decision_Path( ostream & out )
{
	unsigned i = 0;
	for ( ; i < _num_levels - 1; i++ ) {
		if ( _dec_offsets[i+1] > _dec_offsets[i] ) break;
	}
	if ( i < _num_levels - 1 ) {
		Literal decision = _dec_stack[_dec_offsets[i]];
		out << "_assignment[" << decision.Var() << "] == ";
		if ( decision.Sign() ) cerr << "true";
		else cerr << "false";
		for ( i++; i < _num_levels - 1; i++ ) {
			if ( _dec_offsets[i+1] == _dec_offsets[i] ) continue;
			decision = _dec_stack[_dec_offsets[i]];
			cerr << " && ";
			out << "_assignment[" << decision.Var() << "] == ";
			if ( decision.Sign() ) cerr << "true";
			else cerr << "false";
		}
		if ( _num_dec_stack > _dec_offsets[i] ) {
			decision = _dec_stack[_dec_offsets[_num_levels - 1]];
			cerr << " && ";
			out << "_assignment[" << decision.Var() << "] = ";
			if ( decision.Sign() ) cerr << "true";
			else cerr << "false";
		}
		out << endl;
	}
	else if ( _num_dec_stack > _dec_offsets[i] ) {
		Literal decision = _dec_stack[_dec_offsets[_num_levels - 1]];
		out << "_assignment[" << decision.Var() << "] = ";
		if ( decision.Sign() ) cerr << "true";
		else cerr << "false";
		out << endl;
	}
}

void Solver::Display_Conflict( Reason confl, ostream & out )
{
	unsigned i;
	if ( confl == Reason::undef ) {
		out << "confl = \tReason::undefined" << endl;
	}
	else if ( confl.Is_Clause_Reason() ) {
		Clause &clause = _long_clauses[confl.Clause_Value()];
		out << "confl = " << confl.Clause_Value() << ":";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t";
			out << ExtLit( clause[i] );
		}
		out << endl;
		out << "_var_stamps = ";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t" << _var_stamps[clause[i].Var()];
		}
		out << endl;
		out << "_var_seen = ";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t" << _var_seen[clause[i].Var()];
		}
		out << endl;
	}
	else {
		out << "confl = \t";
		out << ExtLit( confl.Lit_Value() );
		out << endl;
		out << "_var_stamps = \t" << _var_stamps[confl.Lit_Value().Var()] << endl;
		out << "_var_seen = \t" << _var_seen[confl.Lit_Value().Var()] << endl;
	}
}

bool Solver::Load_Instance( vector<Clause> & clauses )
{
	unsigned i, j;
	_clause_status.assign( clauses.size(), false );  // Annotate: the bit true means that the corresponding clause is blocked
	for ( i = 0; i < clauses.size(); i++ ) {
		Clause & clause = clauses[i];
		_big_clause.Clear();
		for ( j = 0; j < clause.Size(); j++ ) {
			if ( _lit_seen[clause[j]] ) continue;
			else if ( _lit_seen[~clause[j]] ) break;
			else {
				_big_clause.Add_Lit( clause[j] );
				_lit_seen[clause[j]] = true;
			}
		}
		if ( j < clause.Size() ) { // Annotate: tautology
			_lit_seen[_big_clause[0]] = false;
			for ( j = 1; j < _big_clause.Size(); j++ ) _lit_seen[_big_clause[j]] = false;
			_clause_status[i] = true;
			continue;
		}
		if ( _big_clause.Size() == 1 ) {
			_lit_seen[_big_clause[0]] = false;
			if ( Lit_Undecided( _big_clause[0] ) ) {
				_unary_clauses.push_back( _big_clause[0] );
				Assign( _big_clause[0] );
				clause[0] = _big_clause[0];
				clause.Shrink( 1 );
			}
			else if ( Lit_UNSAT( _big_clause[0] ) ) return false;
			_clause_status[i] = true;  // Annotate: appeared previously
		}
		else {
			_lit_seen[_big_clause[0]] = false;
			clause[0] = _big_clause[0];
			_lit_seen[_big_clause[1]] = false;
			clause[1] = _big_clause[1];
			for ( j = 2; j < _big_clause.Size(); j++ ) {
				_lit_seen[_big_clause[j]] = false;
				clause[j] = _big_clause[j];
			}
			clause.Shrink( _big_clause.Size() );
		}
	}
	if ( !_unary_clauses.empty() && !Simplify_Original_Clauses_By_Unary( clauses ) ) return false;
	for ( i = 0; i < clauses.size(); i++ ) {  /// NOTE: load non-unary clauses here
		Clause & clause = clauses[i];
		if ( _clause_status[i] ) {
			_clause_status[i] = false;
			clause.Free();
		}
		else if ( clause.Size() == 2 ) {
			Add_Binary_Clause_Naive( clause[0], clause[1] );
			clause.Free();
		}
		else _long_clauses.push_back( clause );  /// cannot use clause._lits because it will be free in ~CNF_Formula
	}
	clauses.clear();
	_old_num_long_clauses = _long_clauses.size();
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = _binary_clauses[i + i].size();
		_old_num_binary_clauses[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
	return true;
}

bool Solver::Simplify_Original_Clauses_By_Unary( vector<Clause> & clauses )
{
	for ( unsigned i = 0; i < clauses.size(); i++ ) {  // _long_watched_lists is used as lit_membership_list
		if ( _clause_status[i] ) continue;
		Clause & clause = clauses[i];
		_long_watched_lists[clause[0]].push_back( i );
		_long_watched_lists[clause[1]].push_back( i );
		for ( unsigned j = 2; j < clause.Size(); j++ ) {
			_long_watched_lists[clause[j]].push_back( i );
		}
	}
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		Literal lit = _unary_clauses[i];
		vector<unsigned>::iterator it = _long_watched_lists[lit].begin();
		vector<unsigned>::iterator en = _long_watched_lists[lit].end();
		for ( ; it < en; it++ ) {
			_clause_status[*it] = true;
		}
		it = _long_watched_lists[~lit].begin();
		en = _long_watched_lists[~lit].end();
		for ( ; it < en; it++ ) {
			Clause & clause = clauses[*it];
			unsigned j;
			for ( j = 0; clause[j] != ~lit; j++ ) {}
			clause.Erase_Lit( j );
			if ( clause.Size() == 1 ) {
				if ( Lit_Undecided( clause[0] ) ) {
					_unary_clauses.push_back( clause[0] );
					Assign( clause[0] );
				}
				else if ( Lit_UNSAT( clause[0] ) ) return false;  /// no need to clear _long_watched_lists
				_clause_status[*it] = true;
			}
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
	}
	return true;
}

size_t Solver::Memory()
{
	size_t mem = _model_pool->Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _binary_clauses[i + i].capacity() * sizeof(unsigned);
		mem += _binary_clauses[i + i + 1].capacity() * sizeof(unsigned);
		mem += _long_watched_lists[i + i].capacity() * sizeof(unsigned);
		mem += _long_watched_lists[i + i + 1].capacity() * sizeof(unsigned);
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		mem += _long_clauses[i].Size() * sizeof(unsigned) + sizeof(unsigned *) + sizeof(unsigned);
	}
	return mem;
}

void Solver::Free_Models( vector<Model *> & models )
{
	vector<Model *>::iterator end = models.end();
	for ( vector<Model *>::iterator itr = models.begin(); itr < end; itr++ ) {
		_model_pool->Free( *itr );
	}
	models.clear();
}


}
