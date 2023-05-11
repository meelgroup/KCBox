#include "Preprocessor.h"
#include <sys/sysinfo.h>


namespace KCBox {


Preprocessor::Preprocessor() {}

Preprocessor::~Preprocessor()
{
	if ( _max_var != Variable::undef || Is_Oracle_Mode() ) Free_Auxiliary_Memory();
}

void Preprocessor::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when mv < _max_var
{
	if ( Is_Oracle_Mode() ) {
		assert( max_var <= running_options.variable_bound );
		_max_var = max_var;
		return;
	}
	if ( _max_var == max_var ) {  /// to make the recursive calls from inherited classes correct
		if ( running_options.profile_preprocessing != Profiling_Close ) statistics.Init_Preprocessor();
		return;
	}
	if ( running_options.profile_preprocessing != Profiling_Close ) statistics.Init_Preprocessor_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	Solver::Allocate_and_Init_Auxiliary_Memory( max_var );
	_binary_learnts = new vector<Literal> [2 * _max_var + 2];
	_lit_equivalences = new Literal [2 * _max_var + 2];
	_lit_appeared = new bool [2 * _max_var + 4];  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	_model_seen = new bool [2 * _max_var + 4];  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	_lit_stack = new Literal [2 * _max_var + 2];
	_lit_search_state = new unsigned [2 * _max_var + 4];  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	_lit_index = new unsigned [2 * _max_var + 2];
	_lit_lowlink = new unsigned [2 * _max_var + 2];
	_active_lits = new Literal [2 * _max_var + 2];
	_var_map = new Variable [_max_var + 1];
	_lit_map = new Literal [2 * _max_var + 2];
	_equivalent_lit_sets = new vector<Literal> [2 * _max_var + 2];
	_long_lit_membership_lists = new vector<unsigned> [2 * max_var + 2];  /// literal membership
	_solver_krom = new Solver_Krom( _max_var, _model_seen, _model_pool );  // _model_seen will be written in Backbone_Recognizer, and thus can be use when computing implied literals
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_lit_equivalences[i + i] = Literal( i, false );
		_lit_equivalences[i + i + 1] = Literal( i, true );
		_lit_appeared[i + i] = false;
		_lit_appeared[i + i + 1] = false;
		_model_seen[i + i] = false;
		_model_seen[i + i + 1] = false;
		_lit_search_state[i + i] = UNSIGNED_UNDEF;
		_lit_search_state[i + i + 1] = UNSIGNED_UNDEF;
	}
	_lit_appeared[2 * _max_var + 2] = false;
	_lit_appeared[2 * _max_var + 3] = false;
	_model_seen[2 * _max_var + 2] = false;
	_model_seen[2 * _max_var + 3] = false;
	_lit_search_state[2 * _max_var + 2] = UNSIGNED_UNDEF;
	_lit_search_state[2 * _max_var + 3] = UNSIGNED_UNDEF;
}

void Preprocessor::Free_Auxiliary_Memory()  // NOTE: only called in Allocate_and_Init_Auxiliary_Memory
{
	delete [] _binary_learnts;
	delete [] _lit_equivalences;
	delete [] _lit_appeared;  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	delete [] _model_seen;  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	delete [] _lit_stack;
	delete [] _lit_search_state;  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	delete [] _lit_index;  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	delete [] _lit_lowlink;  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	delete [] _active_lits;
	delete [] _var_map;
	delete [] _lit_map;
	delete [] _equivalent_lit_sets;
	delete [] _long_lit_membership_lists;  /// literal membership
	delete _solver_krom;  // _model_seen will be written in Backbone_Recognizer, and thus can be use when computing implied literals
}

void Preprocessor::Reset()
{
	Solver::Reset();
	_and_gates.clear();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		_lit_equivalences[lit] = lit;
		_long_lit_membership_lists[lit].clear();
		lit = Literal( i, true );
		_lit_equivalences[lit] = lit;
		_long_lit_membership_lists[lit].clear();
	}
}

void Preprocessor::operator = ( Preprocessor & another )
{
	Allocate_and_Init_Auxiliary_Memory( another._max_var );
	Solver::operator=( another );
	_and_gates = another._and_gates;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		_lit_equivalences[lit] = another._lit_equivalences[lit];
		_long_lit_membership_lists[lit] = another._long_lit_membership_lists[lit];
		lit = Literal( i, true );
		_lit_equivalences[lit] = another._lit_equivalences[lit];
		_long_lit_membership_lists[lit] = another._long_lit_membership_lists[lit];
	}
	_fixed_num_vars = another._fixed_num_vars;
}

void Preprocessor::Open_Oracle_Mode( Variable var_bound )
{
	Allocate_and_Init_Auxiliary_Memory( var_bound );
	running_options.variable_bound = var_bound;
	running_options.display_preprocessing_process = false;
}

void Preprocessor::Close_Oracle_Mode()
{
	running_options.variable_bound = Variable::undef;
}

bool Preprocessor::Preprocess( CNF_Formula & cnf, vector<Model *> & models )
{
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_preprocessing_process ) {
		cout << running_options.display_prefix << "Number of original variables: " << cnf.Num_Vars() << endl;
		cout << running_options.display_prefix << "Number of original clauses: " << cnf.Num_Clauses() << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( !Load_Instance( cnf ) ) {
		Un_BCP( 0 );
		return false;
	}
	bool sat = Preprocess( models );
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) statistics.time_preprocess += begin_watch.Get_Elapsed_Seconds();
	if ( !sat ) {
		if ( running_options.display_preprocessing_process ) {
			cout << "s UNSATISFIABLE" << endl;
		}
		if ( debug_options.verify_processed_clauses ) {
			Verify_Satisfiability( cnf, false );
		}
	}
	else {
		if ( running_options.display_preprocessing_process ) {
			cout << "s SATISFIABLE" << endl;
			Display_Statistics( cout );
		}
		if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
		if ( debug_options.verify_processed_clauses ) Verify_Processed_Clauses( cnf );
	}
	return sat;
}

bool Preprocessor::Preprocess( vector<Model *> & models )
{
	StopWatch tmp_watch;
	assert( _num_levels == 0 );
	Extend_New_Level();  // NOTE: Without this line, the _var_stamps of init implied literals will be UNSIGNED_UNDEF
	Gather_Infor_For_SAT();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
	if ( _max_var > 5000 ) running_options.sat_employ_external_solver_always = true;
	if ( running_options.sat_employ_external_solver_always ) {
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			if ( !models.empty() ) return true;
			else return Solve_External( models );
		}
		if ( !Get_All_Imp_Init_External( models ) ) {
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
	}
	else {
		if ( models.empty() && !Solve( models ) ) {
			Un_BCP( 0 );
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
		_fixed_num_vars = _unary_clauses.size();
		Replace_Equivalent_Lit_First();
		if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			return true;
		}
		Get_All_Imp_Init( models );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
	if ( _unary_clauses.size() < _num_dec_stack ) {
		unsigned i = _unary_clauses.size();
		_unary_clauses.push_back( _dec_stack[i] );  // one new unit is already known
		_reasons[_dec_stack[i].Var()] = Reason::undef;
		for ( i++; i < _num_dec_stack; i++ ) {
			_unary_clauses.push_back( _dec_stack[i] );
			_reasons[_dec_stack[i].Var()] = Reason::undef;
		}
		Simplify_Binary_Clauses_By_Unary();
		Simplify_Long_Clauses_By_Unary();
		Simplify_Lit_Equivalences_By_Unary();
	}
	_fixed_num_vars = _unary_clauses.size();
	do {
		Eliminate_Redundancy();
	} while ( Replace_Equivalent_Lit() );
	if ( running_options.block_lits_external && !Large_Scale_Problem() ) Block_Lits_External( models );
	Block_Binary_Clauses();
	if ( running_options.recover_exterior ) Transform_Exterior_Into_Clauses();
	return true;
}

bool Preprocessor::Get_All_Imp_Init_External( vector<Model *> & models )
{
	StopWatch watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_external_solve++;
	bool * var_filled = new bool [_max_var + 1];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		var_filled[i] = true;
	}
	vector<vector<int>> clauses;
	Prepare_Ext_Clauses_Without_Omitted_Vars( clauses, var_filled );  // var_filled is assigned in this function
	_minisat_extra_output.return_model = !Hyperscale_Problem();
	_minisat_extra_output.return_units = true;
	_minisat_extra_output.return_learnt_max_len = 8;
	vector<int8_t> emodel( _max_var + 1 );
	for ( unsigned i = 0; i < models.size(); i++ ) {
		for ( Variable j = Variable::start; j <= _max_var; j++ ) {
			emodel[ExtVar( j )] = (*models[i])[j];
		}
		_minisat_extra_output.models.push_back( emodel );
	}
	unsigned minisat_extra_output_old_num_models = _minisat_extra_output.models.size();
	bool sat = Minisat::Ext_Backbone( clauses, _minisat_extra_output );
	if ( sat ) {
		for ( unsigned i = 0; i < _minisat_extra_output.units.size(); i++ ) {
			Literal lit = InternLit( _minisat_extra_output.units[i] );
			if ( !var_filled[lit.Var()] && Lit_Undecided( lit ) ) {
				Assign( lit );
				BCP( _num_dec_stack - 1 );
			}
		}
		for ( unsigned i = 0; i < _minisat_extra_output.short_learnts[0].size(); i += 2 ) {
			Add_Binary_Clause_Naive( InternLit( _minisat_extra_output.short_learnts[0][i] ), InternLit( _minisat_extra_output.short_learnts[0][i+1] ) );
		}
		for ( unsigned i = 3; i <= _minisat_extra_output.return_learnt_max_len; i++ ) {
			vector<int> & elits = _minisat_extra_output.short_learnts[i-2];
			for ( vector<int>::const_iterator begin = elits.cbegin(); begin < elits.cend(); begin += i ) {
				vector<Literal> lits( i );
				for ( unsigned j = 0; j < i; j++ ) {
					lits[j] = InternLit( *(begin + j) );
				}
				_long_clauses.push_back( lits );
			}
		}
		for ( unsigned i = minisat_extra_output_old_num_models; i < _minisat_extra_output.models.size(); i++ ) {
			Add_Model( _minisat_extra_output.models[i], models );
		}
		_minisat_extra_output.models.clear();
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_external_solve += watch.Get_Elapsed_Seconds();
	delete [] var_filled;
	return sat;
}

void Preprocessor::Prepare_Ext_Clauses_Without_Omitted_Vars( vector<vector<int>> & clauses, bool * var_filled )
{
	vector<int> ext_clause(1);
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		ext_clause[0] = ExtLit( _dec_stack[i] );
		clauses.push_back( ext_clause );
		var_filled[_dec_stack[i].Var()] = false;
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
			var_filled[lit.Var()] = false;
			var_filled[lit2.Var()] = false;
		}
		lit = Literal( i, true );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			ext_clause[1] = ExtLit( lit2 );
			clauses.push_back( ext_clause );
			var_filled[lit.Var()] = false;
			var_filled[lit2.Var()] = false;
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
		if ( j == _long_clauses[i].Size() ) {
			clauses.push_back( ext_clause );
			for ( unsigned k = 0; k < ext_clause.size(); k++ ) {
				int evar = abs( ext_clause[k] );
				var_filled[InternVar( evar )] = false;
			}
		}
	}
	ext_clause.resize(1);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( var_filled[i] ) {
			ext_clause[0] = ExtVar( i );
			clauses.push_back( ext_clause );
		}
	}
	if ( DEBUG_OFF ) {
		for ( unsigned i = 0; i < clauses.size(); i++ ) {  // ToRemove
			for ( unsigned j = 0; j < clauses[i].size(); j++ ) {  // ToRemove
				if ( InternVar( clauses[i][j] ) > _max_var ) {  // ToRemove
					cerr << "clauses[" << i << "][" << j << "] = " << clauses[i][j] << endl;
					assert( InternVar( clauses[i][j] ) <= _max_var );
				}
			}  // ToRemove
		}  // ToRemove
	}
}

bool Preprocessor::Replace_Equivalent_Lit_First()
{
	StopWatch begin_watch;
	if ( !running_options.detect_lit_equivalence_first ) return false;
	assert( !running_options.detect_lit_equivalence_first );  /// NOTE: there is a bug for s13207, and it leads to longer time in preprocessing this instance
	begin_watch.Start();
	if ( !Detect_Lit_Equivalence_Tarjan() ) {  // ToModify
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_lit_equivalences += begin_watch.Get_Elapsed_Seconds();
		return false;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
		Store_Binary_Learnts( i + i );
		Store_Binary_Learnts( i + i + 1 );
	}
	unsigned old_num_d_stack = _num_dec_stack;
	Replace_Equivalent_Lit_Binary_Clauses_First();
	Store_Long_Learnts();
	Replace_Equivalent_Lit_Long_Clauses_First();
	_old_num_long_clauses = _long_clauses.size();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = _binary_clauses[i + i].size();
		_old_num_binary_clauses[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
	Replace_Equivalent_Lit_Binary_Learnts_First();
	Replace_Equivalent_Lit_Long_Learnts_First();
	BCP( old_num_d_stack );
	Init_Heur_Decaying_Sum();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_lit_equivalences += begin_watch.Get_Elapsed_Seconds();
	return true;
}

void Preprocessor::Replace_Equivalent_Lit_Binary_Clauses_First()
{
	unsigned i, j, k;
	for ( i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		Literal root = _equivalent_lit_sets[i][0];
		for ( k = 0; k < _binary_clauses[root].size(); k++ ) {
			Literal equ_lit = _lit_equivalences[_binary_clauses[root][k]];
			if ( equ_lit.Var() == root.Var() || _lit_seen[equ_lit] ) {
				if ( equ_lit == root && Lit_Undecided( root ) ) Assign( root );
				Simply_Erase_Vector_Element( _binary_clauses[root], k );
				k--;
			}
			else {
				_binary_clauses[root][k] = equ_lit;
				_lit_seen[equ_lit] = true;
			}
		}
		for ( j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			assert( root == _lit_equivalences[lit] );
			for ( k = 0; k < _binary_clauses[lit].size(); k++ ) {
				Literal equ_lit = _lit_equivalences[_binary_clauses[lit][k]];
				if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
					if ( equ_lit == root && Lit_Undecided( root ) ) Assign( root );
					_binary_clauses[root].push_back( equ_lit );
					_lit_seen[equ_lit] = true;
				}
			}
			_binary_clauses[lit].clear();
		}
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = false;
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Long_Clauses_First()
{
	unsigned i;
	vector<Clause>::iterator begin = _long_clauses.begin(), itr;
	for ( itr = begin; itr < _long_clauses.end(); itr++ ) {
		_big_clause.Clear();
		for ( i = 0; i < itr->Size(); i++ ) {
			Literal equ_lit = _lit_equivalences[(*itr)[i]];
			if ( _lit_seen[equ_lit] ) continue;
			else if ( _lit_seen[~equ_lit] ) break;
			else {
				_big_clause.Add_Lit( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		if ( i < itr->Size() ) {  // Annotate: tautology
			_long_clauses[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_clauses, itr - begin );
			itr--;
			_lit_seen[_big_clause[0]] = false;
			for ( i = 1; i < _big_clause.Size(); i++ ) _lit_seen[_big_clause[i]] = false;
			continue;
		}
		if ( _big_clause.Size() == 1 ) {
			_lit_seen[_big_clause[0]] = false;
			if ( Lit_Undecided( _big_clause[0] ) ) Assign( _big_clause[0] );
			_long_clauses[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_clauses, itr - begin );
			itr--;
		}
		else {
			_lit_seen[_big_clause[0]] = false;
			_lit_seen[_big_clause[1]] = false;
			if ( _big_clause.Size() == 2 ) {
				Add_Binary_Clause_Naive( _big_clause[0], _big_clause[1] );
				_long_clauses[itr - begin].Free();
				Simply_Erase_Vector_Element( _long_clauses, itr - begin );
				itr--;
			}
			else {
				(*itr)[0] = _big_clause[0];
				(*itr)[1] = _big_clause[1];
				for ( i = 2; i < _big_clause.Size(); i++ ) {
					_lit_seen[_big_clause[i]] = false;
					(*itr)[i] = _big_clause[i];
				}
				itr->Shrink( _big_clause.Size() );
				_long_watched_lists[(*itr)[0]].push_back( itr - begin );
				_long_watched_lists[(*itr)[1]].push_back( itr - begin );
			}
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Binary_Learnts_First()
{
	unsigned i, j, k;
	for ( i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		Literal root = _equivalent_lit_sets[i][0];
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = true;
		}
		for ( k = 0; k < _binary_learnts[root].size(); k++ ) {
			Literal equ_lit = _lit_equivalences[_binary_learnts[root][k]];
			if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
				if ( equ_lit == root && Lit_Undecided( root ) ) Assign( root );
				_binary_clauses[root].push_back( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		_binary_learnts[root].clear();
		for ( j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			assert( root == _lit_equivalences[lit] );
			for ( k = 0; k < _binary_learnts[lit].size(); k++ ) {
				Literal equ_lit = _lit_equivalences[_binary_learnts[lit][k]];
				if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
					if ( equ_lit == root && Lit_Undecided( root ) ) Assign( root );
					_binary_clauses[root].push_back( equ_lit );
					_lit_seen[equ_lit] = true;
				}
			}
			_binary_learnts[lit].clear();
		}
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = false;
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Long_Learnts_First()
{
	vector<Clause>::iterator begin, itr;
	for ( itr = begin = _long_learnts.begin(); itr < _long_learnts.end(); itr++ ) {
		_big_clause.Clear();
		unsigned i;
		for ( i = 0; i < itr->Size(); i++ ) {
			Literal equ_lit = _lit_equivalences[(*itr)[i]];
			if ( _lit_seen[equ_lit] ) continue;
			else if ( _lit_seen[~equ_lit] ) break;
			else {
				_big_clause.Add_Lit( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		if ( i < itr->Size() ) {  // Annotate: tautology
			_long_learnts[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_learnts, itr - begin );
			itr--;
			_lit_seen[_big_clause[0]] = false;
			for ( i = 1; i < _big_clause.Size(); i++ ) _lit_seen[_big_clause[i]] = false;
			continue;
		}
		if ( _big_clause.Size() == 1 ) {
			_lit_seen[_big_clause[0]] = false;
			if ( Lit_Undecided( _big_clause[0] ) ) Assign( _big_clause[0] );
			_long_learnts[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_learnts, itr - begin );
			itr--;
		}
		else {
			_lit_seen[_big_clause[0]] = false;
			_lit_seen[_big_clause[1]] = false;
			if ( _big_clause.Size() == 2 ) {
				Add_Binary_Clause_Naive( _big_clause[0], _big_clause[1] );
				_long_learnts[itr - begin].Free();
				Simply_Erase_Vector_Element( _long_learnts, itr - begin );
				itr--;
			}
			else {
				(*itr)[0] = _big_clause[0];
				(*itr)[1] = _big_clause[1];
				for ( i = 2; i < _big_clause.Size(); i++ ) {
					_lit_seen[_big_clause[i]] = false;
					(*itr)[i] = _big_clause[i];
				}
				itr->Shrink( _big_clause.Size() );
				_long_clauses.push_back( *itr );
				_long_watched_lists[(*itr)[0]].push_back( _long_clauses.size() - 1 );
				_long_watched_lists[(*itr)[1]].push_back( _long_clauses.size() - 1 );
			}
		}
	}
}

void Preprocessor::Get_All_Imp_Init( vector<Model *> & models )
{
	Variable old_start = Variable::start, start = Variable::start, old_num_d_stack;
	_fixed_num_long_clauses = _old_num_long_clauses;  // used in Filter_Long_Learnts
	Mark_Models( models );
	if ( running_options.recognize_backbone_external ) {
		if ( Is_Oracle_Mode() ) _solver_krom->_max_var = _max_var;
		Prepare_Originial_Binary_Clauses_For_BBR();
		for ( unsigned i = 0; i < models.size(); i++ ) {
			Recognize_Non_Implied_Literals( models[i], models );
		}
	}
	Literal lit;
	while ( ( lit = Pick_Imp_Init_Heuristic( start ) ) != _heur_lit_sentinel ) {
//		Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
//		cerr << _long_clauses.size() << endl;  // ToRemove
//		cerr << _long_clauses[1039] << endl;  // ToRemove
		old_num_d_stack = _num_dec_stack;
		if ( Imply_Lit( models, lit ) ) {
			if ( Lit_Undecided( lit ) ) {  /// it is possible that \lit was assigned in \Imply_lit
				Assign( lit );
				BCP( _num_dec_stack - 1 );
			}
			if ( running_options.recognize_backbone_external ) {
				_solver_krom->Assign_Original_Binary_Clauses( _dec_stack[old_num_d_stack] );  // it is possible that \_dec_stack[old_num_d_stack] != \lit
				for ( old_num_d_stack++; old_num_d_stack < _num_dec_stack; old_num_d_stack++ ) {
					_solver_krom->Assign_Original_Binary_Clauses( _dec_stack[old_num_d_stack] );
				}
			}
		}
		else {
			if ( running_options.recognize_backbone_external ) {
				Recognize_Non_Implied_Literals( models.back(), models );
			}
		}
		if ( Learnts_Exploded() ) {
			Filter_Long_Learnts();
			if ( running_options.sat_heur_lits == Heuristic_Literal_Sorted_List ) {
				Quick_Sort_Weight_Reverse( _heur_sorted_lits, 2 * NumVars( _max_var ), _heur_decaying_sum );
			}
			else if ( running_options.sat_heur_lits ==  Heuristic_Literal_Heap ) {
				running_options.sat_heur_cumulative_inc = 1;
				_heur_lits_heap.Build( _heur_sorted_lits, 2 * NumVars( _max_var ) );
			}
		}
	}
	assert( start > _max_var );
	if ( running_options.recognize_backbone_external ) {
		_solver_krom->Reset();
	}
	for ( ; old_start <= _max_var; old_start++ ) {
		_model_seen[old_start + old_start] = false;
		_model_seen[old_start + old_start + 1] = false;
	}
}

void Preprocessor::Mark_Models( vector<Model *> & models )
{
	vector<Model *>::iterator begin = models.begin(), end = models.end() - 1;
	if ( begin == end ) {
		for ( Variable i = Variable::start; i <= _max_var; i++ ) {
			_model_seen[i + i + (**begin)[i]] = true;
		}
	}
	else {
		for ( Variable i = Variable::start; i <= _max_var; i++ ) {
			bool tmp_bit = (**end)[i];
			(*end)->Assign( i, !(**begin)[i] );
			vector<Model *>::iterator itr = begin + 1;
			for ( ; (**itr)[i] == (**begin)[i]; itr++ );
			(*end)->Assign( i, tmp_bit );
			if ( (**itr)[i] != (**begin)[i] ) {
				_model_seen[i + i] = true;
				_model_seen[i + i + 1] = true;
			}
			else _model_seen[i + i + (**begin)[i]] = true;
		}
	}
}

void Preprocessor::Prepare_Originial_Binary_Clauses_For_BBR()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) {
			_solver_krom->Assign( Literal( i, _assignment[i] ) );
			_solver_krom->_original_num_binary_clauses[Literal( i, false )] = 0;
			_solver_krom->_original_num_binary_clauses[Literal( i, true )] = 0;
			continue;
		}
		for ( unsigned j = 0; j < _old_num_binary_clauses[i + i]; j++ ) {
			Literal lit = _binary_clauses[i + i][j];
			if ( Lit_Decided( lit ) ) continue;
			_solver_krom->_binary_clauses[i + i].push_back( lit );
		}
		for ( unsigned j = 0; j < _old_num_binary_clauses[i + i + 1]; j++ ) {
			Literal lit = _binary_clauses[i + i + 1][j];
			if ( Lit_Decided( lit ) ) continue;
			_solver_krom->_binary_clauses[i + i + 1].push_back( lit );
		}
		_solver_krom->_original_num_binary_clauses[i + i] = _solver_krom->_binary_clauses[i + i].size();
		_solver_krom->_original_num_binary_clauses[i + i + 1] = _solver_krom->_binary_clauses[i + i + 1].size();
	}
}

void Preprocessor::Recognize_Non_Implied_Literals( Model * seed_model, vector<Model *> & models )
{
	unsigned i, j, bbr_num_d_stack = _solver_krom->_num_dec_stack;
	for ( i = 0; i < _old_num_long_clauses; i++ ) {
		_big_clause.Clear();
		for ( j = 0; j < _long_clauses[i].Size(); j++ ) {
			Literal lit = _long_clauses[i][j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) continue;
			_big_clause.Add_Lit( lit );
		}
		if ( j == _long_clauses[i].Size() ) {
			assert( _big_clause.Size() >= 2 );
			if ( _big_clause.Size() >= 3 ) _solver_krom->Add_Binary_Clause_From_Long( _big_clause, *seed_model );
			else _solver_krom->Add_Binary_Clause_Naive( _big_clause[0], _big_clause[1] );
		}
	}
	_solver_krom->Mark_Non_Imp_Krom( *seed_model, models );
	_solver_krom->Un_BCP( bbr_num_d_stack );  /// NOTE: cannot Un_BCP in Mark_Non_Imp_Krom because Add_Binary_Clause_From_Long may assign variable
	for ( i = Variable::start; i <= _max_var; i++ ) {  // reset the binary clauses in _solver_krom
		_solver_krom->_binary_clauses[i + i].resize( _solver_krom->_original_num_binary_clauses[i + i] );
		_solver_krom->_binary_clauses[i + i + 1].resize( _solver_krom->_original_num_binary_clauses[i + i + 1] );
	}
}

Literal Preprocessor::Pick_Imp_Init_Heuristic( Variable & start )
{
	for ( ; Var_Decided( start ) + _model_seen[start + start] + _model_seen[start + start + 1] > 1; start++ );
	Literal lit( start, _model_seen[start + start + 1] );
	for ( Variable i = start.Next(); i <= _max_var; i++ ) {
		if ( Var_Decided( i ) + _model_seen[i + i] + _model_seen[i + i + 1] > 1 ) continue;
		Literal tmp( i, _model_seen[i + i + 1] );
		if ( _heur_decaying_sum[tmp] > _heur_decaying_sum[lit] ) lit = tmp;
	}
	return lit;
}

bool Preprocessor::Imply_Lit( vector<Model *> & models, Literal lit )
{
	assert( Lit_Undecided( lit ) );
	unsigned old_num_levels = _num_levels;
	unsigned lifted_sat;
	while ( true ) {
		Extend_New_Level();
		Assign( ~lit );
		if ( BCP( _num_dec_stack - 1 ) != Reason::undef ) {
			Backjump( old_num_levels );  /// NOTE: need to put back to heap
			return true;
		}
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_solve++;
		unsigned num_restart = 0;
		double restart_bound = Restart_Bound();
		while ( ( lifted_sat = Search_Solution( restart_bound ) ) == 2 ) {
			restart_bound *= running_options.sat_restart_trigger_inc;
			num_restart++;
			if ( running_options.sat_employ_external_solver && num_restart > running_options.sat_restart_max ) {
				bool sat = Imply_Lit_External( models, lit );
				Backjump( old_num_levels );
				return sat;
			}
		}
		if ( lifted_sat <= 1 ) break;  // Otherwise, we detected another implied literal not \lit
		Backjump( old_num_levels );
		Assign( _big_learnt[0] );
		BCP( _num_dec_stack - 1 );
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
		if ( Lit_SAT( lit ) ) return true;  // already Backtracked
	}
	if ( lifted_sat ) {
		Add_Marked_Model( models );  // Un_BCP will change _assignment
		if ( debug_options.verify_model ) Verify_Model( models.back() );
	}
	else if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
	Backjump( old_num_levels );
	return lifted_sat == 0;
}

bool Preprocessor::Imply_Lit_External( vector<Model *> & models, Literal lit )
{
	StopWatch watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_external_solve++;
	vector<vector<int>> clauses;
	Prepare_Ext_Clauses( clauses );
	_minisat_extra_output.return_model = true;
	_minisat_extra_output.return_units = true;
	_minisat_extra_output.return_learnt_max_len = 0;
	int8_t result = Minisat::Ext_Solve( clauses, _minisat_extra_output );
	if ( result == 1 ) {
		for ( unsigned i = 0; i < _minisat_extra_output.units.size(); i++ ) {
			Literal lit2 = InternLit( _minisat_extra_output.units[i] );
			if ( Lit_Undecided( lit2 ) ) {
				Add_Binary_Clause_Naive( lit, lit2 );  /// Can be improved
			}
		}
		assert( _minisat_extra_output.models.size() == 1 );
		Add_Marked_Model( _minisat_extra_output.models.front(), models );
		_minisat_extra_output.models.clear();
	}
	else if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_external_solve += watch.Get_Elapsed_Seconds();
	return result == 0;
}

void Preprocessor::Add_Marked_Model( vector<int8_t> & minisat_model, vector<Model *> & models )
{
	Model * model = _model_pool->Allocate();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		model->Assign( i, minisat_model[ExtVar( i )] == 1 );
		_model_seen[i + i + (*model)[i]] = true;
	}
	if ( DEBUG_OFF ) Verify_Model( model );  // ToModify
	models.push_back( model );
}

void Preprocessor::Add_Marked_Model( vector<Model *> & models )
{
	Model * model = _model_pool->Allocate();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		ASSERT( _assignment[i] != lbool::unknown );
		model->Assign( i, _assignment[i] == true );
		_model_seen[i + i + (*model)[i]] = true;
	}
	models.push_back( model );
}

inline bool Preprocessor::Learnts_Exploded()
{
	return _long_clauses.size() - _fixed_num_long_clauses > 2 * ( _max_var + _old_num_long_clauses );
}

void Preprocessor::Filter_Long_Learnts()
{
	unsigned i;
	for ( i = _clause_status.size(); i < _long_clauses.size(); i++ ) {
		_clause_status.push_back( false );
	}
	_clause_stack.resize( _long_clauses.size() );
	for ( i = 0; i < _num_dec_stack; i++ ) {  // labeling the learnts being used
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef || r.Is_Lit_Reason() ) continue;  /// NOTE: SAT_IS_REASON_LONG( Reason::undef ) is true
		unsigned cl = r.Clause_Value();
		if ( cl >= _fixed_num_long_clauses ) {
			_clause_status[cl] = true;
		}
	}
	const unsigned fixed_len = 3;
	vector<Clause>::iterator itr, begin = _long_clauses.begin(), end = _long_clauses.end();
	for ( i = _fixed_num_long_clauses, itr = begin + i; itr < end; itr++ ) {
		if ( _clause_status[itr - begin] ) {
			_clause_stack[itr - begin] = i;
			_long_clauses[i++] = *itr;
		}
		else if ( itr->Size() <= fixed_len ) _long_clauses[i++] = *itr;
		else itr->Free();
	}
	_long_clauses.resize( i );
	begin = _long_clauses.begin(), end = _long_clauses.end();
	for ( i = 0; i < _num_dec_stack; i++ ) {
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef || r.Is_Lit_Reason() ) continue;
		unsigned cl = r.Clause_Value();
		if ( _clause_status[cl] ) {
			_clause_status[cl] = false;
			_reasons[_dec_stack[i].Var()] = Reason( _clause_stack[cl], SAT_REASON_CLAUSE );  // update reason by new position
			assert( _long_clauses[_clause_stack[cl]][0] == _dec_stack[i] );  // ToRemove
		}
	}
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_heur_decaying_sum[i + i] = _binary_clauses[i + i].size();
		_heur_decaying_sum[i + i + 1] = _binary_clauses[i + i + 1].size();
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
	}
	for ( itr = begin; itr < begin + _old_num_long_clauses; itr++ ) {
		Clause & clause = *itr;
		_long_watched_lists[clause[0]].push_back( itr - begin );
		_long_watched_lists[clause[1]].push_back( itr - begin );
		_heur_decaying_sum[clause[0]] += 1;
		_heur_decaying_sum[clause[1]] += 1;
		_heur_decaying_sum[clause[2]] += 1;
		for ( i = 3; i < clause.Size(); i++ ) {
			_heur_decaying_sum[clause[i]] += 1;
		}
	}
	for ( ; itr < begin + _fixed_num_long_clauses; itr++ ) {
		Clause & clause = *itr;
		_long_watched_lists[clause[0]].push_back( itr - begin );
		_long_watched_lists[clause[1]].push_back( itr - begin );
		_heur_decaying_sum[clause[0]] += 1;
		_heur_decaying_sum[clause[1]] += 1;
		_heur_decaying_sum[clause[2]] += 1;
		assert( clause.Size() == 3 );
	}
	for ( end = _long_clauses.end(); itr < end && itr->Size() <= fixed_len; itr++ ) {
		_fixed_num_long_clauses++;
		Clause & clause = *itr;
		_long_watched_lists[clause[0]].push_back( itr - begin );
		_long_watched_lists[clause[1]].push_back( itr - begin );
		_heur_decaying_sum[clause[0]] += 1;
		_heur_decaying_sum[clause[1]] += 1;
		_heur_decaying_sum[clause[2]] += 1;
		assert( clause.Size() == 3 );
	}
	for ( ; itr < end; itr++ ) {
		Clause & clause = *itr;
		_long_watched_lists[clause[0]].push_back( itr - begin );
		_long_watched_lists[clause[1]].push_back( itr - begin );
		_heur_decaying_sum[clause[0]] += 1;
		_heur_decaying_sum[clause[1]] += 1;
		_heur_decaying_sum[clause[2]] += 1;
		for ( i = 3; i < clause.Size(); i++ ) {
			_heur_decaying_sum[clause[i]] += 1;
		}
	}
}

void Preprocessor::Simplify_Binary_Clauses_By_Unary()  // NOTE: all implied literals have been extracted
{
	unsigned i;
	for ( i = 0; i < _unary_clauses.size(); i++ ) {
		vector<Literal>::iterator itr = _binary_clauses[_unary_clauses[i]].begin();  // Annote: we know [a] or b, and then we remove [b] or a
		vector<Literal>::iterator end = _binary_clauses[_unary_clauses[i]].end();
		for ( ; itr < end; itr++ ) {
			vector<Literal>::iterator be = _binary_clauses[*itr].begin(), it = be;
			for ( ; *it != _unary_clauses[i]; it++ );
			if ( unsigned( it - be ) < _old_num_binary_clauses[*itr] )  {
				Remove_Old_Binary_Clause_Half( *itr, it - be );
			}
			else Simply_Erase_Vector_Element( _binary_clauses[*itr], it - be );
		}
		_binary_clauses[_unary_clauses[i]].clear();
		_old_num_binary_clauses[_unary_clauses[i]] = 0;
	}
}

void Preprocessor::Remove_Old_Binary_Clause_Half( unsigned lit, unsigned pos )
{
	_old_num_binary_clauses[lit]--;
	Swap_Two_Elements_Vector( _binary_clauses[lit], pos, _old_num_binary_clauses[lit] );  // Annote: let pos be learnts
	Simply_Erase_Vector_Element( _binary_clauses[lit], _old_num_binary_clauses[lit] );  // Annote: remove pos
}

void Preprocessor::Simplify_Long_Clauses_By_Unary()  // NOTE: all unary clauses has been computed
{
	unsigned i, j;
	for ( i = 0; i < _old_num_long_clauses; ) {
		for ( j = 0; j < _long_clauses[i].Size(); ) {
			Literal lit = _long_clauses[i][j];
			if ( Lit_Undecided( lit ) ) j++;
			else if ( Lit_SAT( lit ) ) break;
			else _long_clauses[i].Erase_Lit( j );
		}
		if ( j < _long_clauses[i].Size() ) 	Remove_Old_Long_Clause_No_Watch( i );
		else {
			if ( _long_clauses[i].Size() == 2 ) {
				Add_Old_Binary_Clause( _long_clauses[i][0], _long_clauses[i][1] );
				Remove_Old_Long_Clause_No_Watch( i );
			}
			else i++;
		}
	}
	for ( ; i < _long_clauses.size(); ) {  // NOTE: _long_clauses would changes
		for ( j = 0; j < _long_clauses[i].Size(); ) {
			Literal lit = _long_clauses[i][j];
			if ( Lit_Undecided( lit ) ) j++;
			else if ( Lit_SAT( lit ) ) break;
			else _long_clauses[i].Erase_Lit( j );
		}
		if ( j < _long_clauses[i].Size() ) Remove_Long_Learnt_No_Watch( i );
		else {
			if ( _long_clauses[i].Size() == 2 ) {
				Add_Binary_Clause_Naive( _long_clauses[i][0], _long_clauses[i][1] );
				Remove_Long_Learnt_No_Watch( i );
			}
			else i++;
		}
	}
	Generate_Long_Watched_Lists();  /// watched lists must be generated again after some long clauses are removed
}

void Preprocessor::Remove_Old_Long_Clause_No_Watch( unsigned pos )
{
	assert( pos < _old_num_long_clauses );
	_old_num_long_clauses--;
	Swap_Two_Elements_Vector( _long_clauses, pos, _old_num_long_clauses );
	_long_clauses[_old_num_long_clauses].Free();
	Simply_Erase_Vector_Element( _long_clauses, _old_num_long_clauses );  // Annote: remove the long clause pos
}

void Preprocessor::Add_Old_Binary_Clause( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr, begin = _binary_clauses[lit1].begin();
	for ( itr = begin; *itr != lit2; itr++ ) {}
	if ( itr != _binary_clauses[lit1].end() - 1 ) {
		_binary_clauses[lit1].pop_back();
		if ( itr - begin >= _old_num_binary_clauses[lit1] ) {  // learnt to original
			Swap_Two_Elements_Vector( _binary_clauses[lit1], _old_num_binary_clauses[lit1], itr - begin );
			_old_num_binary_clauses[lit1]++;
			begin = _binary_clauses[lit2].begin();
			for ( itr = begin; *itr != lit1; itr++ ) {}
			Swap_Two_Elements_Vector( _binary_clauses[lit2], _old_num_binary_clauses[lit2], itr - begin );
			_old_num_binary_clauses[lit2]++;
		}
	}
	else {
		_binary_clauses[lit1].back() = _binary_clauses[lit1][_old_num_binary_clauses[lit1]];
		_binary_clauses[lit1][_old_num_binary_clauses[lit1]] = lit2;
		_old_num_binary_clauses[lit1]++;
		Simply_Insert_Vector_Element( _binary_clauses[lit2], _old_num_binary_clauses[lit2], lit1 );
		_old_num_binary_clauses[lit2]++;
	}
}

void Preprocessor::Remove_Long_Learnt_No_Watch( unsigned pos )
{
	assert( _old_num_long_clauses <= pos && pos < _long_clauses.size() );
	_long_clauses[pos].Free();
	Simply_Erase_Vector_Element( _long_clauses, pos );  // Annote: remove the long clause pos
}

void Preprocessor::Simplify_Lit_Equivalences_By_Unary()
{
	if ( !running_options.detect_lit_equivalence_first ) return;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		if ( Var_Decided( i ) ) {
			_lit_equivalences[lit] = lit;
			_lit_equivalences[~lit] = ~lit;
			continue;
		}
		Literal lit_equ = _lit_equivalences[lit];
		if ( lit == lit_equ ) continue;
		if ( Lit_Undecided( lit_equ ) ) continue;
		if ( Lit_SAT( lit_equ ) ) _unary_clauses.push_back( lit );  // can be optimized
		else _unary_clauses.push_back( ~lit );
		_lit_equivalences[lit] = lit;
		_lit_equivalences[~lit] = ~lit;
	}
}

void Preprocessor::Eliminate_Redundancy()
{
	if ( !running_options.block_clauses && !running_options.block_lits ) return;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Store_Binary_Learnts( i + i );
		Store_Binary_Learnts( i + i + 1);
	}
	Store_Long_Learnts();  // NOTE: not consider learnts, otherwise impacts the equivalence
	Generate_Long_Watched_Lists();
	Block_Lits();
	Vivification();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Recover_Binary_Learnts( i + i );
		Recover_Binary_Learnts( i + i + 1 );
	}
	_old_num_long_clauses = _long_clauses.size();
	for ( unsigned i = 0; i < _long_learnts.size(); i++ ) {  // only need to recover _long_watched_lists for _long_learnts
		Block_Lits_In_Extra_Clause( _long_learnts[i] );
		if ( _long_learnts[i].Size() == 2 ) {  // become binary learnt clause
			Add_Binary_Clause_Naive( _long_learnts[i][0], _long_learnts[i][1] );
			_long_learnts[i].Free();
			Simply_Erase_Vector_Element( _long_learnts, i );
			i--;
		}
		else {
			_long_clauses.push_back( _long_learnts[i] );
			_long_watched_lists[_long_learnts[i][0]].push_back( i + _old_num_long_clauses );
			_long_watched_lists[_long_learnts[i][1]].push_back( i + _old_num_long_clauses );
		}
	}
}

void Preprocessor::Store_Long_Learnts()
{
	_long_learnts.assign( _long_clauses.begin() + _old_num_long_clauses, _long_clauses.end() );
	_long_clauses.resize( _old_num_long_clauses );
}

void Preprocessor::Store_Binary_Learnts( unsigned lit )
{
	_binary_learnts[lit].assign( _binary_clauses[lit].begin() + _old_num_binary_clauses[lit], _binary_clauses[lit].end() );
	_binary_clauses[lit].resize( _old_num_binary_clauses[lit] );
}

void Preprocessor::Recover_Binary_Learnts( unsigned lit )
{
	_old_num_binary_clauses[lit] = _binary_clauses[lit].size();
	for ( unsigned i = 0; i < _binary_clauses[lit].size(); i++ ) {
		Literal lit2 = _binary_clauses[lit][i];
		_lit_seen[lit2] = true;
	}
	for ( unsigned i = 0; i < _binary_learnts[lit].size(); i++ ) {
		Literal lit2 = _binary_learnts[lit][i];
		if ( !_lit_seen[lit2] ) {  /// NOTE: new binary clauses may be generated when block literals in long clauses, so we cannot use _binary_clauses[lit].insert instead
			_binary_clauses[lit].push_back( lit2 );
			_lit_seen[lit2] = true;
		}
	}
	_binary_learnts[lit].clear();
	for ( unsigned i = 0; i < _binary_clauses[lit].size(); i++ ) {
		unsigned lit2 = _binary_clauses[lit][i];
		_lit_seen[lit2] = false;
	}
}

void Preprocessor::Vivification()  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_clauses ) return;
	StopWatch begin_watch;
	unsigned i, j, old_num_dec_stack = _num_dec_stack;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( i = 0; i < _long_clauses.size(); ) {  // NOTE: _long_clauses would change
		Clause clause = Pull_Old_Long_Clause_No_Learnt( i );
		for ( j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) {
				clause.Erase_Lit( j );
				j--;
				continue;
			}
			Assign( ~lit );
			if ( BCP( _num_dec_stack - 1 ) != Reason::undef ) break;
		}
		Un_BCP( old_num_dec_stack );
		if ( j < clause.Size() ) clause.Free();
		else if ( clause.Size() == 2 ) {
			Add_Binary_Clause_Naive( clause[0], clause[1] );
			clause.Free();
		}
		else Add_Old_Long_Clause_Fixed_No_Learnt( clause, i++ );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_clauses += begin_watch.Get_Elapsed_Seconds();
}

void Preprocessor::Remove_Old_Binary_Clause_No_Learnt( Literal lit, unsigned pos )  // NOTE: no learnt
{
	Literal lit2 = _binary_clauses[lit][pos];
	vector<Literal>::iterator begin = _binary_clauses[lit2].begin(), itr;
	for ( itr = begin; *itr != lit; itr++ ) {}
	Simply_Erase_Vector_Element( _binary_clauses[lit2], itr - begin );  // Annote: remove lit from pos
	Simply_Erase_Vector_Element( _binary_clauses[lit], pos );  // Annote: remove pos from _binary_clauses[lit]
}

bool Preprocessor::Imply_Binary_Clause_BCP( Literal lit1, Literal lit2 )
{
	_dec_offsets[_num_levels++] = _num_dec_stack;
	assert( Lit_Undecided( lit1 ) );
	Assign( ~lit1 );
	assert( Lit_Undecided( lit2 ) );
	Assign( ~lit2 );
	Reason conf = BCP( _dec_offsets[_num_levels - 1] );
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	return conf != Reason::undef;
}

bool Preprocessor::Imply_Long_Clause_BCP( Clause & clause )
{
	assert( clause.Size() >= 3 );
	unsigned i;
	_dec_offsets[_num_levels++] = _num_dec_stack;
	assert( Lit_Undecided( clause[0] ) );
	Assign( ~clause[0] );
	assert( Lit_Undecided( clause[1] ) );
	Assign( ~clause[1] );
	assert( Lit_Undecided( clause[2] ) );
	Assign( ~clause[2] );
	for ( i = 3; i < clause.Size(); i++ ) {
		assert( Lit_Undecided( clause[i] ) );
		Assign( ~clause[i] );
	}
	Reason conf = BCP( _dec_offsets[_num_levels - 1] );
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	return conf != Reason::undef;
}

void Preprocessor::Add_Old_Binary_Clause_Fixed_No_Learnt( Literal lit1, Literal lit2, unsigned pos )  // NOTE: no learnt
{
	assert( lit1 < lit2 && pos <= _binary_clauses[lit1].size() );
	Simply_Insert_Vector_Element( _binary_clauses[lit1], pos, lit2 );
	_binary_clauses[lit2].push_back( lit1 );
}

Clause Preprocessor::Pull_Old_Long_Clause_No_Learnt( unsigned pos )  // NOTE: no learnt
{
	assert( pos < _long_clauses.size() );
	vector<unsigned>::iterator itr, begin;
	Clause cl = _long_clauses[pos];
	unsigned lit = cl[0];
	for (  itr = begin = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
	Simply_Erase_Vector_Element( _long_watched_lists[lit], itr - begin );  // Annote: remove clause pos from watched_list
	lit = cl[1];
	for ( itr = begin = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
	Simply_Erase_Vector_Element( _long_watched_lists[lit], itr - begin );  // Annote: remove clause pos from watched_list
	if ( pos < _long_clauses.size() - 1 ) {  // Annote: not back
		unsigned back = _long_clauses.size() - 1;
		lit = _long_clauses[back][0];
		for ( itr = _long_watched_lists[lit].begin(); *itr != back; itr++ ) {}
		*itr = pos;  // Annote: update the last long clause in watched_list
		lit = _long_clauses[back][1];
		for ( itr = _long_watched_lists[lit].begin(); *itr != back; itr++ ) {}
		*itr = pos;  // Annote: update the last long clause in watched_list
		_long_clauses[pos] = _long_clauses[back];
	}
	_long_clauses.pop_back();
	return cl;
}

void Preprocessor::Add_Old_Long_Clause_Fixed_No_Learnt( Clause & clause, unsigned pos )
{
	unsigned lit;
	_long_watched_lists[clause[0]].push_back( pos );
	_long_watched_lists[clause[1]].push_back( pos );
	_long_clauses.push_back( clause );
	if ( pos < _long_clauses.size() - 1 ) {
		unsigned last = _long_clauses.size() - 1;
		vector<unsigned>::iterator itr;
		lit = _long_clauses[pos][0];
		for ( itr = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
		*itr = last;  // Annote: update the first learnt in watched_list
		lit = _long_clauses[pos][1];
		for ( itr = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
		*itr = last;  // Annote: update the first learnt in watched_list
		Swap_Two_Elements_Vector( _long_clauses, pos, last );
	}
}


void Preprocessor::Block_Lits()  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_lits ) return;
	StopWatch begin_watch;
	unsigned i, j;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( i = 0; i < _long_clauses.size(); ) {
		_big_clause.Resize( _long_clauses[i].Size() );
		_big_clause[0] = _long_clauses[i][0];
		_big_clause[1] = _long_clauses[i][1];
		_big_clause[2] = _long_clauses[i][2];
		for ( j = 3; j < _long_clauses[i].Size(); j++ ) {
			_big_clause[j] = _long_clauses[i][j];
		}
		for ( j = 0; j < _long_clauses[i].Size(); ) {
			Literal lit = _big_clause[j];
			_big_clause[j] = ~lit;
			if ( Imply_Long_Clause_BCP( _big_clause ) ) {
				_big_clause.Erase_Lit( j );
				Erase_Fixed_Lit_From_Long_Clause( i, lit );
				if ( _big_clause.Size() == 2 ) break;
			}
			else _big_clause[j++] = lit;
		}
		if ( _long_clauses[i].Size() == 2 ) {  // NOTE: add new binary and j != 2 when break
			Add_Binary_Clause_Naive( _long_clauses[i][0], _long_clauses[i][1] );
			Remove_Old_Long_Clause_No_Learnt( i );
		}
		else i++;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_lits += begin_watch.Get_Elapsed_Seconds();
}

bool Preprocessor::Imply_Long_Clause_BCP( Big_Clause & clause )
{
	assert( clause.Size() >= 3 );
	unsigned i;
	_dec_offsets[_num_levels++] = _num_dec_stack;
	assert( Lit_Undecided( clause[0] ) );
	Assign( ~clause[0] );
	assert( Lit_Undecided( clause[1] ) );
	Assign( ~clause[1] );
	assert( Lit_Undecided( clause[2] ) );
	Assign( ~clause[2] );
	for ( i = 3; i < clause.Size(); i++ ) {
		assert( Lit_Undecided( clause[i] ) );
		Assign( ~clause[i] );
	}
	Reason conf = BCP( _dec_offsets[_num_levels - 1] );
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	return conf != Reason::undef;
}

void Preprocessor::Block_Lits_Improved()  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_lits ) return;
	StopWatch begin_watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( unsigned i = 0; i < _long_clauses.size(); ) {
		_big_clause.Resize( _long_clauses[i].Size() );
		_big_clause[0] = _long_clauses[i][0];
		_big_clause[1] = _long_clauses[i][1];
		_big_clause[2] = _long_clauses[i][2];
		for ( unsigned j = 3; j < _long_clauses[i].Size(); j++ ) {
			_big_clause[j] = _long_clauses[i][j];
		}
		Block_Lits_In_Clause( i );
		if ( _long_clauses[i].Size() == 2 ) {  // NOTE: add new binary and j != 2 when break
			Add_Binary_Clause_Naive( _long_clauses[i][0], _long_clauses[i][1] );
			Remove_Old_Long_Clause_No_Learnt( i );
		}
		else i++;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_lits += begin_watch.Get_Elapsed_Seconds();
}

void Preprocessor::Block_Lits_In_Clause( unsigned i )
{
	unsigned j, k;
	Literal lit;
	unsigned old_num_levels = _num_levels;
	lit = _big_clause[0];
	_dec_offsets[_num_levels++] = _num_dec_stack;
	Assign( ~lit );
	BCP( _num_dec_stack - 1 );
	for ( j = 1; !Lit_SAT( _big_clause[j] ); j++ ) {  // when j is _big_clause.size() - 2, _big_clause.Last_Lit() must be satisfied by BCP
		lit = _big_clause[j];
		if ( Lit_UNSAT( lit ) ) {
			_big_clause.Erase_Lit( j );
			Erase_Fixed_Lit_From_Long_Clause( i, lit );  /// _long_clauses[i] may change after BCP
			j--;
			continue;
		}
		_dec_offsets[_num_levels++] = _num_dec_stack;
		Assign( ~lit );
		if ( BCP( _num_dec_stack - 1 ) != Reason::undef ) {
			Un_BCP( _dec_offsets[_num_levels - 1] );
			Assign( lit );
			while ( BCP( _num_dec_stack - 1 ) != Reason::undef ) {  // _big_clause[j] can be removed
				j--;
				lit = _big_clause[j];
				_num_levels--;
				assert( _dec_stack[_dec_offsets[_num_levels - 1]] == ~lit );
				Un_BCP( _dec_offsets[_num_levels - 1] );
				Assign( lit );
			}
			assert( _dec_stack[_dec_offsets[_num_levels - 1]] == lit );
			Un_BCP( _dec_offsets[_num_levels - 1] );
			_num_levels--;
			break;
		}
	}
	assert( j == _num_levels - old_num_levels );
	_big_clause.Resize( j + 1 );  // remove the literals after _big_clause[j], and _big_clause[j] has been checked
	for ( k = j + 1; k < _big_clause.Size(); k++ ) {
		Erase_Fixed_Lit_From_Long_Clause( i, _big_clause[k] );
	}
	assert( _big_clause.Size() >= 2 );
	for ( j--; j != UNSIGNED_UNDEF && _big_clause.Size() > 2; j--, _num_levels-- ) {
		Un_BCP( _dec_offsets[_num_levels - 1] );
		lit = _big_clause[j];
		assert( _dec_stack[_dec_offsets[_num_levels - 1]] == ~lit );
		Assign( lit );
		for ( k = j + 1; k < _big_clause.Size(); k++ ) {
			if ( Lit_SAT( _big_clause[k] ) ) break;
			if ( Lit_UNSAT( _big_clause[k] ) ) continue;
			Assign( ~_big_clause[k] );
		}
		if ( k < _big_clause.Size() || BCP( _num_dec_stack - 1 ) != Reason::undef ) {
			_big_clause.Erase_Lit( j );
			Erase_Fixed_Lit_From_Long_Clause( i, lit );
		}
	}
	assert( _num_levels >= old_num_levels );
	Un_BCP( _dec_offsets[old_num_levels] );
	_num_levels = old_num_levels;
}

void Preprocessor::Erase_Fixed_Lit_From_Long_Clause( unsigned cl_pos, Literal lit )
{
	unsigned i;
	for ( i = 0; _long_clauses[cl_pos][i] != lit; i++ );
	if ( i < 2 ) {
		vector<unsigned>::iterator itr, begin;
		for ( itr = begin = _long_watched_lists[lit].begin(); *itr != cl_pos; itr++ ) {}
		Simply_Erase_Vector_Element( _long_watched_lists[lit], itr - begin );  // NOTE: remove the clause from watched_list
		_long_clauses[cl_pos].Erase_Lit( i );
		lit = _long_clauses[cl_pos][i];
		_long_watched_lists[lit].push_back( cl_pos );
	}
	else _long_clauses[cl_pos].Erase_Lit( i );
}

void Preprocessor::Remove_Old_Long_Clause_No_Learnt( unsigned pos )
{
	assert( pos < _long_clauses.size() );
	vector<unsigned>::iterator itr, begin;
	unsigned lit = _long_clauses[pos][0];
	for ( itr = begin = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
	Simply_Erase_Vector_Element( _long_watched_lists[lit], itr - begin );  // Annote: remove clause pos from watched_list
	lit = _long_clauses[pos][1];
	for ( itr = begin = _long_watched_lists[lit].begin(); *itr != pos; itr++ ) {}
	Simply_Erase_Vector_Element( _long_watched_lists[lit], itr - begin );  // Annote: remove clause pos from watched_list
	if ( pos == _long_clauses.size() - 1 ) {  // change previously
		_long_clauses[pos].Free();
		_long_clauses.pop_back();  // Annote: remove the long clause pos
	}
	else {
		unsigned last = _long_clauses.size() - 1;
		lit = _long_clauses[last][0];
		for ( itr = _long_watched_lists[lit].begin(); *itr != last; itr++ ) {}
		*itr = pos;  // Annote: update the last learnt in watched_list
		lit = _long_clauses[last][1];
		for ( itr = _long_watched_lists[lit].begin(); *itr != last; itr++ ) {}
		*itr = pos;  // Annote: update the last learnt in watched_list
		_long_clauses[pos].Free();
		Simply_Erase_Vector_Element( _long_clauses, pos );  // Annote: remove the long clause pos
	}
}

void Preprocessor::Block_Lits_In_Extra_Clause( Clause & clause )  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_lits ) return;
	StopWatch begin_watch;
	unsigned i;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( i = 0; i < clause.Size(); ) {
		Literal lit = clause[i];
		clause[i] = ~lit;
		if ( Imply_Long_Clause_BCP( clause ) ) {
			clause.Erase_Lit( i );
			if ( clause.Size() == 2 ) break;
		}
		else clause[i++] = lit;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_lits += begin_watch.Get_Elapsed_Seconds();
}

void Preprocessor::Block_Lits_In_Extra_Clause( Big_Clause & clause )  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_lits ) return;
	StopWatch begin_watch;
	unsigned i;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( i = 0; i < clause.Size(); ) {
		Literal lit = clause[i];
		clause[i] = ~lit;
		if ( Imply_Long_Clause_BCP( clause ) ) {
			clause.Erase_Lit( i );
			if ( clause.Size() == 2 ) break;
		}
		else clause[i++] = lit;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_lits += begin_watch.Get_Elapsed_Seconds();
}

bool Preprocessor::Replace_Equivalent_Lit()
{
	StopWatch begin_watch;
	if ( !running_options.detect_lit_equivalence ) return false;
	begin_watch.Start();
	if ( !Detect_Lit_Equivalence() ) {
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_lit_equivalences += begin_watch.Get_Elapsed_Seconds();
		return false;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_long_watched_lists[i + i].clear();
		_long_watched_lists[i + i + 1].clear();
		Store_Binary_Learnts( i + i );
		Store_Binary_Learnts( i + i + 1 );
	}
	Replace_Equivalent_Lit_Binary_Clauses();
	Store_Long_Learnts();
	Replace_Equivalent_Lit_Long_Clauses();
	_old_num_long_clauses = _long_clauses.size();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = _binary_clauses[i + i].size();
		_old_num_binary_clauses[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
	Replace_Equivalent_Lit_Binary_Learnts();
	Replace_Equivalent_Lit_Long_Learnts();
	for ( Literal i = Literal::start; DEBUG_OFF && i <= 2 * _max_var + 1; i++ ) {  // ToModify
		for ( unsigned j = 0; j < _binary_clauses[i].size(); j++ ) {
			Literal lit = _binary_clauses[i][j];
			unsigned k;
			for ( k = j + 1; k < _binary_clauses[i].size(); k++ ) {
				if ( _binary_clauses[i][k] == lit ) break;
			}
			assert( k == _binary_clauses[i].size() );
			if ( lit == i || _lit_equivalences[lit] != lit ) {
				cerr << "lit = " << lit << endl;
				cerr << "i = " << i << endl;
				cerr << "_lit_equivalences[lit] = " << _lit_equivalences[lit] << endl;
				assert( lit != i && _lit_equivalences[lit] == lit );
			}
			for ( k = 0; k < _binary_clauses[lit].size(); k++ ) {
				if ( _binary_clauses[lit][k] == i ) break;
			}
			assert( !_binary_clauses[lit].empty() && k < _binary_clauses[lit].size() );
			if ( j < _old_num_binary_clauses[i] ) assert( k < _old_num_binary_clauses[lit] );
			else assert( k >= _old_num_binary_clauses[lit] );
		}
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_lit_equivalences += begin_watch.Get_Elapsed_Seconds();
	return true;
}

bool Preprocessor::Detect_Lit_Equivalence()
{
	switch ( running_options.lit_equivalence_detecting_strategy ) {  // ToModify
	case Literal_Equivalence_Detection_Naive:
		return Detect_Lit_Equivalence_Naive();
		break;
	case Literal_Equivalence_Detection_Tarjan:
		return Detect_Lit_Equivalence_Tarjan();
	case Literal_Equivalence_Detection_BCP:
		return Detect_Lit_Equivalence_BCP();
		break;
	case Literal_Equivalence_Detection_IBCP:
		return Detect_Lit_Equivalence_IBCP();
		break;
	}
	return false;
}

bool Preprocessor::Detect_Lit_Equivalence_Naive()
{
	Detect_Binary_Learnts();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( _binary_clauses[i + i].empty() || _binary_clauses[i + i + 1].empty() ) continue;
		_lit_seen[_binary_clauses[i + i][0]] = true;
		for ( unsigned j = 1; j < _binary_clauses[i + i].size(); j++ ) {
			_lit_seen[_binary_clauses[i + i][j]] = true;
		}
		for ( unsigned j = 0; j < _binary_clauses[i + i + 1].size(); j++ ) {
			Literal lit = ~_binary_clauses[i + i + 1][j];
			if ( !_lit_seen[lit] ) continue;
			if ( _lit_equivalences[i + i + 1] < _lit_equivalences[lit] ) {  /// NOTE: merge two trees based on union-find sets
				_lit_equivalences[_lit_equivalences[lit]] = _lit_equivalences[i + i + 1];
				_lit_equivalences[~_lit_equivalences[lit]] = ~_lit_equivalences[i + i + 1];
				_lit_equivalences[lit] = _lit_equivalences[i + i + 1];
				_lit_equivalences[~lit] = ~_lit_equivalences[i + i + 1];
			}
			else {
				_lit_equivalences[_lit_equivalences[i + i + 1]] = _lit_equivalences[lit];
				_lit_equivalences[~_lit_equivalences[i + i + 1]] = ~_lit_equivalences[lit];
				_lit_equivalences[i + i + 1] = _lit_equivalences[lit];
				_lit_equivalences[i + i] = ~_lit_equivalences[lit];
			}
		}
		_lit_seen[_binary_clauses[i + i][0]] = false;
		for ( unsigned j = 1; j < _binary_clauses[i + i].size(); j++ ) {
			_lit_seen[_binary_clauses[i + i][j]] = false;
		}
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits();  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

void Preprocessor::Detect_Binary_Learnts()
{
	if ( running_options.detect_binary_learnts_resolution ) Detect_Binary_Learnts_Resolution();
	else if ( running_options.detect_binary_learnts_bcp ) Detect_Binary_Learnts_BCP();
}

void Preprocessor::Detect_Binary_Learnts_Resolution()
{
	vector<unsigned> propogation_positions( 2 * _max_var + 2, 0 );
	vector<Literal> propogation_lits;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		if ( !_binary_clauses[lit].empty() ) propogation_lits.push_back( lit );
		lit = Literal( i, true );
		if ( !_binary_clauses[lit].empty() ) propogation_lits.push_back( lit );
	}
	for ( unsigned i = 0; i < propogation_lits.size(); i++ ) {
		Literal lit = propogation_lits[i];
		for ( ; propogation_positions[lit] < _binary_clauses[lit].size(); propogation_positions[lit]++ ) {
			Literal lit1 = _binary_clauses[lit][propogation_positions[lit]];
			for ( unsigned j = 0; j < _binary_clauses[~lit].size(); j++ ) {
				Literal lit2 = _binary_clauses[~lit][j];
				unsigned old_size = _binary_clauses[lit1].size();
				Add_Binary_Clause_Naive( lit1, lit2 );  /// resolution: ( lit or lit1 ) + ( ~lit or lit2 ) => lit1 or lit2
				if ( old_size < _binary_clauses[lit1].size() ) { // added successfully
					propogation_lits.push_back( lit1 );
					propogation_lits.push_back( lit2 );
				}
			}
		}
	}
}

void Preprocessor::Detect_Binary_Learnts_BCP()
{
	cerr << "ERROR[Preprocessor]: Detect_Binary_Learnts_BCP is not implemented yet!" << endl;
	exit( 1 );
}

void Preprocessor::Cluster_Equivalent_Lits()
{
	_fixed_num_vars = _unary_clauses.size() + _and_gates.size();
	_equivalent_lit_cluster_size = 0;
	vector<Literal> singleton( 1 );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {  /// after the first calling of Detect_Lit_Equivalence, the first if-statement in this loop needs ti be used
		Literal lit = _lit_equivalences[i + i];
		if ( _lit_equivalences[lit] != lit ) {  /// handle the case where the path to the root is greater than one
			Literal root = _lit_equivalences[lit];
			assert( _lit_equivalences[root] == root );  /// handled from one to _max_var, so the length of sub-path is not greater than one
			_lit_equivalences[i + i] = root;
			_lit_equivalences[i + i + 1] = ~root;
		}
		if ( _lit_equivalences[i + i] != i + i ) {  // NOTE: lit may be changed, so we need to use _lit_equivalences[i + i]
			unsigned j;
			for ( j = 0; _lit_equivalences[i + i] != _equivalent_lit_sets[j][0]; j++ ) {}  // find the old entry
			_equivalent_lit_sets[j].push_back( Literal( i, false ) );
			_equivalent_lit_sets[j ^ 0x01].push_back( Literal( i, true ) );
			_fixed_num_vars++;
		}
		else {  // create new entries
			singleton[0] = Literal( i, false );
			_equivalent_lit_sets[_equivalent_lit_cluster_size++] = singleton;
			singleton[0] = Literal( i, true );
			_equivalent_lit_sets[_equivalent_lit_cluster_size++] = singleton;
		}
	}
}

bool Preprocessor::Detect_Lit_Equivalence_Tarjan()
{
	vector<Literal> lit_equivalence_old;
	if ( DEBUG_OFF ) {  // ToModify
		lit_equivalence_old.resize( 2 * _max_var + 2 );
		for ( Literal i = Literal::start; i <= 2 * _max_var + 1; i++ ) {
			lit_equivalence_old[i] = _lit_equivalences[i];
		}
		Display_Clauses( cerr, true );  // ToRemove
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( _lit_search_state[i + i] != UNSIGNED_UNDEF || _lit_search_state[i + i + 1] != UNSIGNED_UNDEF ) continue;
		if ( _lit_equivalences[i + i] != i + i ) continue;
		Strongly_Connected_Component( Literal( i, false ) );
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_lit_search_state[i + i] = UNSIGNED_UNDEF;
		_lit_search_state[i + i + 1] = UNSIGNED_UNDEF;
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits();  // _fixed_num_vars will change in the function
	if ( DEBUG_OFF ) {  // ToModify
		cerr << "====" << endl;
		Display_Equivalent_Lit_Clusters( cerr );
		vector<Literal> lit_equivalence_copy( 2 * _max_var + 2 );
		unsigned fixed_num_vars_copy = _fixed_num_vars;
		vector<unsigned> num_binary_clauses_copy( 2 * _max_var + 2 );
		for ( Literal i = Literal::start; i <= 2 * _max_var + 1; i++ ) {
			lit_equivalence_copy[i] = _lit_equivalences[i];
			num_binary_clauses_copy[i] = _binary_clauses[i].size();
			_lit_equivalences[i] = lit_equivalence_old[i];
		}
		vector<vector<Literal>> equivalent_lit_sets_copy;
		for ( unsigned i = 0; i < _equivalent_lit_cluster_size; i++ ) {
			equivalent_lit_sets_copy.push_back( _equivalent_lit_sets[i] );
		}
		Detect_Lit_Equivalence_Naive();
		cerr << "====" << endl;
		Display_Equivalent_Lit_Clusters( cerr );
		for ( Literal i = Literal::start; i <= 2 * _max_var + 1; i++ ) {
			assert( _lit_equivalences[i] == lit_equivalence_copy[i] );
//			_binary_clauses[i].resize( num_binary_clauses_copy[i] );
		}
		cerr << _equivalent_lit_cluster_size << " vs " << equivalent_lit_sets_copy.size() << endl;
		assert( _equivalent_lit_cluster_size == equivalent_lit_sets_copy.size() );
		assert( _fixed_num_vars == fixed_num_vars_copy );
		for ( unsigned i = 0; i < _equivalent_lit_cluster_size; i++ ) {
			assert( _equivalent_lit_sets[i].size() == equivalent_lit_sets_copy[i].size() );
			for ( unsigned j = 0; j < _equivalent_lit_sets[i].size(); j++ ) {
				/** NOTE: after Replace_Equivalent_Lit, new implied literals may be generated.
				** Therefore, both a <-> b and a <-> not b will be right.
				**/
				assert( _equivalent_lit_sets[i][j] == equivalent_lit_sets_copy[i][j] );
			}
		}

	}
	return old_fixed_num_vars < _fixed_num_vars;
}

void Preprocessor::Strongly_Connected_Component( Literal source )
{
	Literal top, lit;
	unsigned size = 0, capacity = 0;  // size is used for _lit_stack, and capacity is used for reachable_lits
	unsigned index = 0;  // label the visiting number
	_lit_stack[size++] = source;  // push to _lit_stack
	_active_lits[capacity++] = source;  // push to _active_lits
	_lit_seen[source] = true;  // mark active literals
	_lit_search_state[source] = 0;
	_lit_index[source] = index++;
	_lit_lowlink[source] = _lit_index[source];
	while ( size > 0 ) {
		top = _lit_stack[size - 1];
		if ( _lit_search_state[top] < _binary_clauses[~top].size() ) {  /// a or b means that (not a) -> b is an edge
			lit = _binary_clauses[~top][_lit_search_state[top]];
			if ( _lit_search_state[lit] == UNSIGNED_UNDEF ) {
				_lit_stack[size++] = lit;  // push to _lit_stack
				_active_lits[capacity++] = lit;  // push to _active_lits
				_lit_seen[lit] = true;
				_lit_search_state[lit] = 0;
				_lit_index[lit] = index++;
				_lit_lowlink[lit] = _lit_index[lit];
			}
			_lit_search_state[top]++;
		}
		else {
			for ( unsigned i = 0; i < _binary_clauses[~top].size(); i++ ) {
				lit = _binary_clauses[~top][i];
				/** NOTE:
				** only consider the active literals (excluding the literals searched by different callings or from different branches without loop)
				**/
				if ( _lit_seen[lit] && _lit_lowlink[lit] < _lit_lowlink[top] ) _lit_lowlink[top] = _lit_lowlink[lit];
			}
			if ( _lit_lowlink[top] == _lit_index[top] ) {
				Literal min = top;
				for ( unsigned i = capacity - 1; _active_lits[i] != top; i-- ) {  // NOTE: _lit_equivalences[lit] is not greater than lit
					if ( _active_lits[i] < min ) min = _active_lits[i];
				}
				while ( _active_lits[capacity - 1] != top ) {
					lit = _active_lits[capacity - 1];
					_lit_equivalences[lit] = min;
					_lit_equivalences[~lit] = ~min;
					_lit_seen[lit] = false;
					capacity--;
				}
				_lit_equivalences[top] = min;  // NOTE: top may not be min
				_lit_equivalences[~top] = ~min;
				_lit_seen[top] = false;
				capacity--;  // pop top in _active_lits
			}
			size--;  // pop top in _lit_stack
		}
	}
	assert( size == 0 && capacity == 0 );
}

void Preprocessor::Replace_Equivalent_Lit_Binary_Clauses()
{
	unsigned i, j, k;
	for ( i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		Literal root = _equivalent_lit_sets[i][0];
		for ( k = 0; k < _binary_clauses[root].size(); k++ ) {
			Literal equ_lit = _lit_equivalences[_binary_clauses[root][k]];
			if ( equ_lit.Var() == root.Var() || _lit_seen[equ_lit] ) {
				Simply_Erase_Vector_Element( _binary_clauses[root], k );
				k--;
			}
			else {
				_binary_clauses[root][k] = equ_lit;
				_lit_seen[equ_lit] = true;
			}
		}
		for ( j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			assert( root == _lit_equivalences[lit] );
			for ( k = 0; k < _binary_clauses[lit].size(); k++ ) {
				Literal equ_lit = _lit_equivalences[_binary_clauses[lit][k]];
				if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
					_binary_clauses[root].push_back( equ_lit );
					_lit_seen[equ_lit] = true;
				}
			}
			_binary_clauses[lit].clear();
		}
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = false;
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Long_Clauses()
{
	unsigned i;
	vector<Clause>::iterator begin = _long_clauses.begin(), itr;
	for ( itr = begin; itr < _long_clauses.end(); itr++ ) {
		_big_clause.Clear();
		for ( i = 0; i < itr->Size(); i++ ) {
			Literal equ_lit = _lit_equivalences[(*itr)[i]];
			if ( _lit_seen[equ_lit] ) continue;
			else if ( _lit_seen[~equ_lit] ) break;
			else {
				_big_clause.Add_Lit( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		if ( i < itr->Size() ) {  // Annotate: tautology
			_long_clauses[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_clauses, itr - begin );
			itr--;
			_lit_seen[_big_clause[0]] = false;
			for ( i = 1; i < _big_clause.Size(); i++ ) _lit_seen[_big_clause[i]] = false;
			continue;
		}
		assert( _big_clause.Size() > 1 );
		_lit_seen[_big_clause[0]] = false;
		_lit_seen[_big_clause[1]] = false;
		if ( _big_clause.Size() == 2 ) {
			Add_Binary_Clause_Naive( _big_clause[0], _big_clause[1] );
			_long_clauses[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_clauses, itr - begin );
			itr--;
		}
		else {
			(*itr)[0] = _big_clause[0];
			(*itr)[1] = _big_clause[1];
			for ( i = 2; i < _big_clause.Size(); i++ ) {
				_lit_seen[_big_clause[i]] = false;
				(*itr)[i] = _big_clause[i];
			}
			itr->Shrink( _big_clause.Size() );
			_long_watched_lists[(*itr)[0]].push_back( itr - begin );
			_long_watched_lists[(*itr)[1]].push_back( itr - begin );
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Binary_Learnts()
{
	unsigned i, j, k;
	for ( i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		Literal root = _equivalent_lit_sets[i][0];
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = true;
		}
		for ( k = 0; k < _binary_learnts[root].size(); k++ ) {
			Literal equ_lit = _lit_equivalences[_binary_learnts[root][k]];
			if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
				_binary_clauses[root].push_back( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		_binary_learnts[root].clear();
		for ( j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			assert( root == _lit_equivalences[lit] );
			for ( k = 0; k < _binary_learnts[lit].size(); k++ ) {
				Literal equ_lit = _lit_equivalences[_binary_learnts[lit][k]];
				if ( equ_lit.Var() != root.Var() && !_lit_seen[equ_lit] ) {
					_binary_clauses[root].push_back( equ_lit );
					_lit_seen[equ_lit] = true;
				}
			}
			_binary_learnts[lit].clear();
		}
		for ( j = 0; j < _binary_clauses[root].size(); j++ ) {
			_lit_seen[_binary_clauses[root][j]] = false;
		}
	}
}

void Preprocessor::Replace_Equivalent_Lit_Long_Learnts()
{
	vector<Clause>::iterator begin, itr;
	for ( itr = begin = _long_learnts.begin(); itr < _long_learnts.end(); itr++ ) {
		_big_clause.Clear();
		unsigned i;
		for ( i = 0; i < itr->Size(); i++ ) {
			Literal equ_lit = _lit_equivalences[(*itr)[i]];
			if ( _lit_seen[equ_lit] ) continue;
			else if ( _lit_seen[~equ_lit] ) break;
			else {
				_big_clause.Add_Lit( equ_lit );
				_lit_seen[equ_lit] = true;
			}
		}
		if ( i < itr->Size() ) {  // Annotate: tautology
			_long_learnts[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_learnts, itr - begin );
			itr--;
			_lit_seen[_big_clause[0]] = false;
			for ( i = 1; i < _big_clause.Size(); i++ ) _lit_seen[_big_clause[i]] = false;
			continue;
		}
		assert( _big_clause.Size() > 1 );
		_lit_seen[_big_clause[0]] = false;
		_lit_seen[_big_clause[1]] = false;
		if ( _big_clause.Size() == 2 ) {
			Add_Binary_Clause_Naive( _big_clause[0], _big_clause[1] );
			_long_learnts[itr - begin].Free();
			Simply_Erase_Vector_Element( _long_learnts, itr - begin );
			itr--;
		}
		else {
			(*itr)[0] = _big_clause[0];
			(*itr)[1] = _big_clause[1];
			for ( i = 2; i < _big_clause.Size(); i++ ) {
				_lit_seen[_big_clause[i]] = false;
				(*itr)[i] = _big_clause[i];
			}
			itr->Shrink( _big_clause.Size() );
			_long_clauses.push_back( *itr );
			_long_watched_lists[(*itr)[0]].push_back( _long_clauses.size() - 1 );
			_long_watched_lists[(*itr)[1]].push_back( _long_clauses.size() - 1 );
		}
	}
}

void Preprocessor::Add_Binary_Clause_Naive_Half( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr;
	for ( itr = _binary_clauses[lit1].begin(); *itr != lit2; itr++ ) {}
	if ( itr != _binary_clauses[lit1].end() - 1 ) _binary_clauses[lit1].pop_back();
}

bool Preprocessor::Detect_Lit_Equivalence_BCP()
{
	unsigned old_num_d_stack = _num_dec_stack;
	vector<Literal> neg_implied_literals, pos_implied_literals;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) continue;
		Assign( Literal( i, false ) );
		BCP( old_num_d_stack );
		neg_implied_literals.resize( _num_dec_stack - old_num_d_stack - 1 );
		for ( unsigned j = old_num_d_stack + 1; j < _num_dec_stack; j++ ) {
			neg_implied_literals[j - old_num_d_stack - 1] = _dec_stack[j];
		}
		Un_BCP( old_num_d_stack );
		Assign( Literal( i, true ) );
		BCP( old_num_d_stack );
		pos_implied_literals.resize( _num_dec_stack - old_num_d_stack - 1 );
		for ( unsigned j = old_num_d_stack + 1; j < _num_dec_stack; j++ ) {
			pos_implied_literals[j - old_num_d_stack - 1] = _dec_stack[j];
		}
		Un_BCP( old_num_d_stack );
		if ( neg_implied_literals.empty() || pos_implied_literals.empty() ) continue;
		_lit_seen[neg_implied_literals[0]] = true;
		for ( unsigned j = 1; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = true;
		}
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			Literal lit = pos_implied_literals[j];
			if ( !_lit_seen[~lit] ) continue;
			Record_Equivalent_Lit_Pair( Literal( i, true ), lit );
		}
		_lit_seen[neg_implied_literals[0]] = false;
		for ( unsigned j = 1; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = false;
		}
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits();  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

bool Preprocessor::Detect_Lit_Equivalence_IBCP()
{
	unsigned old_num_d_stack = _num_dec_stack, tmp_num_d_stack;
	vector<Literal> neg_implied_literals, pos_implied_literals;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) continue;
		Implied_Literals_Approx( Literal( i, false ), neg_implied_literals );
		Implied_Literals_Approx( Literal( i, true ), pos_implied_literals );
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = true;
		}
		Assign( i, false, Reason::undef );
		BCP( old_num_d_stack );
		tmp_num_d_stack = _num_dec_stack;
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			Literal lit = pos_implied_literals[j];  // phi and (i+i+1) |= lit
			bool imp = false;
			if ( _lit_seen[~lit] ) imp = true;  // phi and (i+i) |= not lit
			else {
				Assign( lit );
				if ( BCP( tmp_num_d_stack ) != Reason::undef ) imp = true;  // phi and (i+i) |= not lit, if phi and (i+i) and lit is unsatisfiable
				Un_BCP( tmp_num_d_stack );
			}
			if ( imp ) Record_Equivalent_Lit_Pair( Literal( i, true ), lit );
		}
		Un_BCP( old_num_d_stack );
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = false;
		}
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			_lit_seen[pos_implied_literals[j]] = true;
		}
		Assign( i, true, Reason::undef );
		BCP( old_num_d_stack );
		tmp_num_d_stack = _num_dec_stack;
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			Literal lit = neg_implied_literals[j];  // phi and (i+i) |= lit
			if ( !_lit_seen[~lit] ) {  // the case of _lit_seen[~lit] is already detected
				Assign( lit );
				if ( BCP( tmp_num_d_stack ) != Reason::undef ) Record_Equivalent_Lit_Pair( Literal( i, false ), lit );  // phi and (i+i+1) |= not lit, if phi and (i+i+1) and lit is unsatisfiable
				Un_BCP( tmp_num_d_stack );
			}
		}
		Un_BCP( old_num_d_stack );
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			_lit_seen[pos_implied_literals[j]] = false;
		}
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits();  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

void Preprocessor::Implied_Literals_Approx( Literal lit, vector<Literal> & imp_lits )
{
	unsigned i, old_num_d_stack = _num_dec_stack;
	Assign( lit );
	BCP( old_num_d_stack );
	imp_lits.resize( _num_dec_stack - old_num_d_stack - 1 );
	for ( i = old_num_d_stack + 1; i < _num_dec_stack; i++ ) {
		imp_lits[i - old_num_d_stack - 1] = _dec_stack[i];
	}
	Un_BCP( old_num_d_stack );
}

void Preprocessor::Record_Equivalent_Lit_Pair( Literal lit, Literal lit2 )
{
	if ( _lit_equivalences[lit] < _lit_equivalences[lit2] ) {  /// NOTE: merge two trees based on union-find sets
		Literal equ = _lit_equivalences[lit2];
		_lit_equivalences[equ] = _lit_equivalences[lit];  /// NOTE: _lit_equivalences[lit2] might change after this line, and thus cannot use _lit_equivalences[_lit_equivalences[lit2]]
		_lit_equivalences[~equ] = ~_lit_equivalences[lit];
		_lit_equivalences[lit2] = _lit_equivalences[lit];
		_lit_equivalences[~lit2] = ~_lit_equivalences[lit];
	}
	else {
		Literal equ = _lit_equivalences[lit];
		_lit_equivalences[equ] = _lit_equivalences[lit2];
		_lit_equivalences[~equ] = ~_lit_equivalences[lit2];
		_lit_equivalences[lit] = _lit_equivalences[lit2];
		_lit_equivalences[~lit] = ~_lit_equivalences[lit2];
	}
}

void Preprocessor::Block_Binary_Clauses()  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_clauses || running_options.keep_binary_learnts ) return;
	StopWatch begin_watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Store_Binary_Learnts( i + i );
		Store_Binary_Learnts( i + i + 1);
	}
	Store_Long_Learnts();  // NOTE: not consider learnts, otherwise impacts the equivalence
	Generate_Long_Watched_Lists();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); ) {  // NOTE: _binary_clauses[lit] would change
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) {
				j++;
				continue;
			}
			Remove_Old_Binary_Clause_No_Learnt( lit, j );
			if ( !Imply_Binary_Clause_BCP( lit, lit2 ) ) Add_Old_Binary_Clause_Fixed_No_Learnt( lit, lit2, j++ );
		}
		lit = Literal( i, true );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); ) {  // NOTE: _binary_clauses[lit] would change
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) {
				j++;
				continue;
			}
			Remove_Old_Binary_Clause_No_Learnt( lit, j );
			if ( !Imply_Binary_Clause_BCP( lit, lit2 ) ) Add_Old_Binary_Clause_Fixed_No_Learnt( lit, lit2, j++ );
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Recover_Binary_Learnts( i + i );
		Recover_Binary_Learnts( i + i + 1 );
	}
	for ( unsigned i = 0; i < _long_learnts.size(); i++ ) {
		_long_clauses.push_back( _long_learnts[i] );
		_long_watched_lists[_long_learnts[i][0]].push_back( i + _old_num_long_clauses );
		_long_watched_lists[_long_learnts[i][1]].push_back( i + _old_num_long_clauses );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_block_clauses += begin_watch.Get_Elapsed_Seconds();
}

bool Preprocessor::Block_Lits_External( vector<Model *> & models )
{
	StopWatch watch;
	if ( _old_num_long_clauses == 0 ) return false;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_external_solve++;
	bool * var_filled = new bool [_max_var + 1];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		var_filled[i] = true;
	}
	vector<vector<int>> simplified;
	vector<vector<int>> others;
	Prepare_Ext_Clauses_Without_Omitted_Vars( simplified, others, var_filled );  // var_filled is assigned in this function
	_minisat_extra_output.return_model = !Hyperscale_Problem();
	_minisat_extra_output.return_units = false;
	_minisat_extra_output.return_learnt_max_len = 8;
	bool found = Minisat::Ext_Block_Literals( simplified, others, _minisat_extra_output );
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		_long_clauses[i].Free();
	}
	unsigned num_long = 0;
	for ( vector<int> & clause: simplified ) {
		if ( clause.size() == 2 ) {
			Add_Old_Binary_Clause( InternLit( clause[0] ), InternLit( clause[1] ) );
			continue;
		}
		vector<Literal> lits( clause.size() );
		for ( unsigned i = 0; i < clause.size(); i++ ) {
			lits[i] = InternLit( clause[i] );
		}
		_long_clauses[num_long++] = Clause( lits );
	}
	_long_clauses.erase( _long_clauses.begin() + num_long, _long_clauses.begin() + _old_num_long_clauses );
	_fixed_num_long_clauses = _old_num_long_clauses = num_long;
	Generate_Long_Watched_Lists();
	for ( unsigned i = 0; i < _minisat_extra_output.short_learnts[0].size(); i += 2 ) {
		Literal lit0 = InternLit( _minisat_extra_output.short_learnts[0][i] );
		Literal lit1 = InternLit( _minisat_extra_output.short_learnts[0][i+1] );
		Add_Binary_Clause_Naive( lit0, lit1 );
	}
	Big_Clause learnt( _max_var );
	for ( unsigned i = 3; i <= _minisat_extra_output.return_learnt_max_len; i++ ) {
		vector<int> & elits = _minisat_extra_output.short_learnts[i-2];
		for ( vector<int>::const_iterator begin = elits.cbegin(); begin < elits.cend(); begin += i ) {
			learnt.Resize( i );
			for ( unsigned j = 0; j < i; j++ ) {
				learnt[j] = InternLit( *(begin + j) );
			}
			Block_Lits_In_Extra_Clause( learnt );
			if ( learnt.Size() == 2 ) Add_Binary_Clause_Naive( learnt[0], learnt[1] );
			else {
				_long_clauses.push_back( learnt );
				_long_watched_lists[learnt[0]].push_back( _long_clauses.size() - 1 );
				_long_watched_lists[learnt[1]].push_back( _long_clauses.size() - 1 );
			}
		}
	}
	for ( unsigned i = 0; i < _minisat_extra_output.models.size(); i++ ) {
		Add_Model( _minisat_extra_output.models[i], models );
	}
	_minisat_extra_output.models.clear();
	Init_Heur_Decaying_Sum();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_external_solve += watch.Get_Elapsed_Seconds();
	delete [] var_filled;
	return found;
}

void Preprocessor::Prepare_Ext_Clauses_Without_Omitted_Vars( vector<vector<int>> & simplified, vector<vector<int>> & others, bool * var_filled )  // mark the omitted variable in var_omitted
{
	vector<int> ext_clause(1);
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		ext_clause[0] = ExtLit( _dec_stack[i] );
		others.push_back( ext_clause );
		var_filled[_dec_stack[i].Var()] = false;
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
			others.push_back( ext_clause );
			var_filled[lit.Var()] = false;
			var_filled[lit2.Var()] = false;
		}
		lit = Literal( i, true );
		ext_clause[0] = ExtLit( lit );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			ext_clause[1] = ExtLit( lit2 );
			others.push_back( ext_clause );
			var_filled[lit.Var()] = false;
			var_filled[lit2.Var()] = false;
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
		if ( j == _long_clauses[i].Size() ) {
			simplified.push_back( ext_clause );
			for ( unsigned k = 0; k < ext_clause.size(); k++ ) {
				int evar = abs( ext_clause[k] );
				var_filled[InternVar( evar )] = false;
			}
		}
	}
	ext_clause.resize(1);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( var_filled[i] ) {
			ext_clause[0] = ExtVar( i );
			others.push_back( ext_clause );
		}
	}
}

bool Preprocessor::Non_Unary_Clauses_Empty()
{
	if ( !_long_clauses.empty() ) return false;
	unsigned i;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		if ( !_binary_clauses[i + i].empty() || !_binary_clauses[i + i + 1].empty() ) return false;
	}
	return true;
}

void Preprocessor::Verify_Backbone( CNF_Formula & cnf )
{
	vector<vector<int>> original_eclauses;
	cnf.ExtClauses( original_eclauses );
	vector<int> unary_eclause(1);
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) {
			unary_eclause[0] = -ExtLit( Literal( i, _assignment[i] ) );
			original_eclauses.push_back( unary_eclause );
			int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
			if ( sat == 1 ) {
				cerr << "ERROR[Preprocessor]: " << -unary_eclause[0] << " is not any implied literal!" << endl;
				assert( sat == 1 );
			}
			continue;
		}
		unary_eclause[0] = ExtLit( Literal( i, false ) );
		original_eclauses.push_back( unary_eclause );
		int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
		if ( sat == 0 ) {
			cerr << "ERROR[Preprocessor]: Implied literal " << -unary_eclause[0] << " has not been detected yet!" << endl;
			assert( sat == 1 );
		}
		original_eclauses.pop_back();
		unary_eclause[0] = ExtLit( Literal( i, true ) );
		original_eclauses.push_back( unary_eclause );
		sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
		if ( sat == 0 ) {
			cerr << "ERROR[Preprocessor]: Implied literal " << -unary_eclause[0] << " has not been detected yet!" << endl;
			assert( sat == 1 );
		}
		original_eclauses.pop_back();
	}
}

void Preprocessor::Verify_Processed_Clauses( CNF_Formula & cnf )
{
	vector<vector<int>> processed_eclauses;
	Output_Processed_Ext_Clauses( processed_eclauses );
	vector<vector<int>> original_eclauses;
	cnf.ExtClauses( original_eclauses );
	vector<vector<int>> eclauses;
	vector<int> unary_eclause(1);
	eclauses = processed_eclauses;
	unsigned old_size = eclauses.size();
	for ( unsigned i = 0; i < original_eclauses.size(); i++ ) {
		vector<int> & eclause = original_eclauses[i];
		for ( unsigned j = 0; j < eclause.size(); j++ ) {
			unary_eclause[0] = -eclause[j];
			eclauses.push_back( unary_eclause );
		}
		int sat = Minisat::Ext_Solve( eclauses, _minisat_extra_output );
		if ( sat != 0 ) {
			cerr << "processed cnf formula:" << endl;
			Display_Ext_Clauses( cerr, processed_eclauses );
			cerr << "the current original clause:" << endl;
			for ( unsigned j = 0; j < eclause.size(); j++ ) {
				cerr << eclause[j] << ' ';
			}
			cerr << "0" << endl;
			assert( sat == 0 );
		}
		eclauses.resize( old_size );
	}
	eclauses = original_eclauses;
	old_size = eclauses.size();
	for ( unsigned i = 0; i < processed_eclauses.size(); i++ ) {
		vector<int> & eclause = processed_eclauses[i];
		for ( unsigned j = 0; j < eclause.size(); j++ ) {
			unary_eclause[0] = -eclause[j];
			eclauses.push_back( unary_eclause );
		}
		int sat = Minisat::Ext_Solve( eclauses, _minisat_extra_output );
		if ( sat != 0 ) {
			cerr << "original cnf formula:" << endl;
			Display_Ext_Clauses( cerr, original_eclauses );
			cerr << "the current processed clause:" << endl;
			for ( unsigned j = 0; j < eclause.size(); j++ ) {
				cerr << eclause[j] << ' ';
			}
			cerr << "0" << endl;
			assert( sat == 0 );
		}
		eclauses.resize( old_size );
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) continue;
		unary_eclause[0] = ExtLit( Literal( i, false ) );
		eclauses.push_back( unary_eclause );
		int sat = Minisat::Ext_Solve( eclauses, _minisat_extra_output );
		if ( sat == 0 ) {
			cerr << "ERROR[Preprocessor]: Implied literal " << -unary_eclause[0] << " has not been detected yet!" << endl;
			assert( sat == 1 );
		}
		eclauses.pop_back();
		unary_eclause[0] = ExtLit( Literal( i, true ) );
		eclauses.push_back( unary_eclause );
		sat = Minisat::Ext_Solve( eclauses, _minisat_extra_output );
		if ( sat == 0 ) {
			cerr << "ERROR[Preprocessor]: Implied literal " << -unary_eclause[0] << " has not been detected yet!" << endl;
			assert( sat == 1 );
		}
		eclauses.pop_back();
	}
}

void Preprocessor::Verify_Learnts( CNF_Formula & cnf )
{
	vector<vector<int>> original_eclauses;
	cnf.ExtClauses( original_eclauses );
	unsigned old_size = original_eclauses.size();
	vector<int> unary_eclause(1);
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
		for ( unsigned i = _old_num_binary_clauses[lit]; i < _binary_clauses[lit].size(); i++ ) {
			unary_eclause[0] = ExtLit( ~lit );
			original_eclauses.push_back( unary_eclause );
			unary_eclause[0] = ExtLit( ~_binary_clauses[lit][i] );
			original_eclauses.push_back( unary_eclause );
			int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
			if ( sat != 0 ) {
				cerr << "invalid learnt clause: " << ExtLit( lit ) << " " << -unary_eclause[0] << endl;
				assert( sat == 0 );
			}
			original_eclauses.resize( old_size );
		}
	}
	for ( unsigned i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) {
		Clause & clause = _long_clauses[i];
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			unary_eclause[0] = -ExtLit( clause[j] );
			original_eclauses.push_back( unary_eclause );
		}
		int sat = Minisat::Ext_Solve( original_eclauses, _minisat_extra_output );
		if ( sat != 0 ) {
			cerr << "invalid learnt clause: ";
			for ( unsigned j = 0; j < clause.Size(); j++ ) {
				cerr << ExtLit( clause[j] ) << ' ';
			}
			cerr << "0" << endl;
			assert( sat == 0 );
		}
		original_eclauses.resize( old_size );
	}
}

void Preprocessor::Verify_Imply_Clause( Clause & clause )
{
	unsigned i;
	CNF_Formula * cnf = Output_Processed_Clauses();
	for ( i = 0; i < clause.Size(); i++ ) {
		cnf->Add_Unary_Clause( ~clause[i] );
	}
	vector<vector<int>> eclauses;
	cnf->ExtClauses( eclauses );
	delete cnf;
	assert( Minisat::Ext_Solve( eclauses, _minisat_extra_output ) == 0 );
}

void Preprocessor::Load_Original_Instance( CNF_Formula & cnf ) // cnf must be simplify
{
	unsigned i;
	_max_var = cnf.Max_Var();
	vector<Clause>::iterator itr = cnf.Clause_Begin();
	vector<Clause>::iterator end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		Clause & clause = *itr;
		if ( clause.Size() <= 2 ) {
			if ( clause.Size() == 1 ) _unary_clauses.push_back( clause[0] );
			else {
				_binary_clauses[clause[0]].push_back( clause[1] );
				_binary_clauses[clause[1]].push_back( clause[0] );
			}
		}
		else _long_clauses.push_back( clause.Copy() );  // cannot use clause._lits because it will be free in ~CNF_Formula
	}
	_old_num_long_clauses = _long_clauses.size();
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_old_num_binary_clauses[i + i] = _binary_clauses[i + i].size();
		_old_num_binary_clauses[i + i + 1] = _binary_clauses[i + i + 1].size();
	}
}

void Preprocessor::Verify_Equivalent_Lit_Clusters()
{
	unsigned sum = 0;
	for ( unsigned i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		assert( !_equivalent_lit_sets[i].empty() );
		sum += _equivalent_lit_sets[i].size();
		Literal root = _equivalent_lit_sets[i][0];
		assert( _lit_equivalences[root] == root );
		for ( unsigned j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			assert( _lit_equivalences[lit] != lit && _lit_equivalences[lit] == root );
			assert( Imply_Binary_Clause_BCP( root, ~lit ) );
			assert( Imply_Binary_Clause_BCP( ~root, lit ) );
		}
	}
	assert( sum == 2 * _max_var + 2 );
}

void Preprocessor::Display_Statistics( ostream & out )
{
	unsigned num_omitted_vars = Num_Omitted_Vars();
	out << running_options.display_prefix << "Number of unsimplifiable variables: " << NumVars( _max_var ) - _unary_clauses.size() - Lit_Equivalency_Size() - num_omitted_vars
		<< " (" << _unary_clauses.size() << " unit, " << Lit_Equivalency_Size() << " equ, " << num_omitted_vars << " omit)" << endl;
	out << running_options.display_prefix << "Number of unsimplifiable non-unary clauses: " << Old_Num_Clauses() - _unary_clauses.size() << endl;
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) {
		out << running_options.display_prefix << "Preprocessing Time: " << statistics.time_preprocess << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) {
		out << running_options.display_prefix << "    Time of SAT: " << statistics.time_solve << endl;
		if ( running_options.block_clauses ) out << running_options.display_prefix << "    Time of blocking clauses: " << statistics.time_block_clauses << endl;
		if ( running_options.block_lits ) out << running_options.display_prefix << "    Time of blocking literals: " << statistics.time_block_lits << endl;
		if ( running_options.detect_lit_equivalence ) out << running_options.display_prefix << "    Time of replacing literal equivalency: " << statistics.time_replace_lit_equivalences << endl;
	}
}

void Preprocessor::Display_Temp_Binary_Learnts( ostream & out )
{
	for ( Literal i = Literal::start; i <= 2 * _max_var + 1; i++ ) {
		out << ExtLit(i) << ":";
		for ( unsigned j = 0; j < _binary_learnts[i].size(); j++ ) {
			out << ' ' << ExtLit( _binary_learnts[i][j] );
		}
		out << endl;
	}
}

inline void Preprocessor::Display_Models( vector<Model *> & source, ostream & fout )
{
	unsigned i, size;
	for ( i = 0, size = source.size(); i < size; i++ ) {
		source[i]->Display_Simple( _max_var, fout );
	}
}

void Preprocessor::Display_Clauses_For_Verifying_Imp( ostream & out, unsigned old_num_d_stack, unsigned new_num_d_stack )
{
	unsigned i;
	CNF_Formula cnf( _max_var );
	for ( i = 0; i < old_num_d_stack; i++ ) {
		cnf.Add_Unary_Clause( _dec_stack[i] );
	}
	_big_clause.Resize( new_num_d_stack - old_num_d_stack );
	for ( ; i < new_num_d_stack; i++ ) {
		_big_clause[i - old_num_d_stack] = ~_dec_stack[i];
	}
	cnf.Add_Clause( _big_clause );
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		lit++;
		for ( i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		lit++;
	}
	for ( i = 0; i < _old_num_long_clauses; i++ ) {
		cnf.Add_Clause( _long_clauses[i] );
	}
	out << cnf;
}

void Preprocessor::Display_Lit_Equivalence( ostream & out )
{
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
		if ( _lit_equivalences[lit] != lit ) {
			out << ExtLit( lit ) << " <-> " << ExtLit( _lit_equivalences[lit] ) << endl;
		}
	}
}

void Preprocessor::Display_Equivalent_Lit_Clusters( ostream & out )
{
	for ( unsigned i = 0; i < _equivalent_lit_cluster_size; i++ ) {
		if ( _equivalent_lit_sets[i].size() == 1 ) continue;
		out << i << ": ";
		Literal root = _equivalent_lit_sets[i][0];
		out << ExtLit( root );
		for ( unsigned j = 1; j < _equivalent_lit_sets[i].size(); j++ ) {
			Literal lit = _equivalent_lit_sets[i][j];
			out << ' ' << ExtLit( lit );
		}
		out << endl;
	}
}

bool Preprocessor::Preprocess( unsigned num_vars, vector<Clause> & clauses )
{
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_preprocessing_process ) {
		cout << running_options.display_prefix << "Number of original variables: " << num_vars << endl;
		cout << running_options.display_prefix << "Number of original clauses: " << clauses.size() << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( Variable( Variable::start + num_vars - 1 ) );
	if ( !Load_Instance( clauses ) ) {
		Un_BCP( 0 );
		return false;
	}
	vector<Model *> models;
	bool sat = Preprocess( models );
	Free_Models( models );
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) statistics.time_preprocess += begin_watch.Get_Elapsed_Seconds();
	if ( !sat ) {
		if ( running_options.display_preprocessing_process ) {
			cout << "s UNSATISFIABLE" << endl;
		}
	}
	else {
		if ( running_options.display_preprocessing_process ) {
			cout << "s SATISFIABLE" << endl;
			Display_Statistics( cout );
		}
	}
	return sat;
}

bool Preprocessor::Preprocess( vector<vector<int>> & eclauses )
{
	CNF_Formula cnf( eclauses );
	vector<Model *> models;
	bool sat = Preprocess( cnf, models );
	Free_Models( models );
	return sat;
}

bool Preprocessor::Preprocess_Sharp( CNF_Formula & cnf, vector<Model *> & models )
{
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_preprocessing_process ) {
		cout << running_options.display_prefix << "Number of original variables: " << cnf.Num_Vars() << endl;
		cout << running_options.display_prefix << "Number of original clauses: " << cnf.Num_Clauses() << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( !Load_Instance( cnf ) ) {
		Un_BCP( 0 );
		return false;
	}
	bool sat = Preprocess_Sharp( models );
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) statistics.time_preprocess += begin_watch.Get_Elapsed_Seconds();
	if ( !sat ) {
		if ( running_options.display_preprocessing_process ) {
			cout << "s UNSATISFIABLE" << endl;
		}
		if ( debug_options.verify_processed_clauses ) {
			Verify_Satisfiability( cnf, false );
		}
	}
	else {
		if ( running_options.display_preprocessing_process ) {
			cout << "s SATISFIABLE" << endl;
			Display_Statistics_Sharp( cout );
		}
		if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
		if ( debug_options.verify_processed_clauses ) Verify_Processed_Clauses( cnf );
		if ( _fixed_num_vars >= 32 && !Hyperscale_Problem() ) Shrink_Max_Var();
	}
	return sat;
}

bool Preprocessor::Preprocess_Sharp( vector<Model *> & models )
{
	StopWatch tmp_watch;
	assert( _num_levels == 0 );
	Extend_New_Level();  // NOTE: Without this line, the _var_stamps of init implied literals will be UNSIGNED_UNDEF
	Gather_Infor_For_SAT();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
	if ( _max_var > 5000 ) running_options.sat_employ_external_solver_always = true;
	if ( running_options.sat_employ_external_solver_always ) {
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			if ( !models.empty() ) return true;
			else return Solve_External( models );
		}
		if ( !Get_All_Imp_Init_External( models ) ) {
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
	}
	else {
		if ( models.empty() && !Solve( models ) ) {
			Un_BCP( 0 );
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
		_fixed_num_vars = _unary_clauses.size();
		Replace_Equivalent_Lit_First();
		if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			return true;
		}
		Get_All_Imp_Init( models );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
	if ( _unary_clauses.size() < _num_dec_stack ) {
		unsigned i = _unary_clauses.size();
		_unary_clauses.push_back( _dec_stack[i] );  // one new unit is already known
		_reasons[_dec_stack[i].Var()] = Reason::undef;
		for ( i++; i < _num_dec_stack; i++ ) {
			_unary_clauses.push_back( _dec_stack[i] );
			_reasons[_dec_stack[i].Var()] = Reason::undef;
		}
		Simplify_Binary_Clauses_By_Unary();
		Simplify_Long_Clauses_By_Unary();
		Simplify_Lit_Equivalences_By_Unary();
	}
	_fixed_num_vars = _unary_clauses.size();
	bool flag;
	for ( unsigned i = 0; i < 2; i++ ) {
		Eliminate_Redundancy();
		flag = Replace_Equivalent_Lit();
		if ( !flag ) break;
	}
	if ( !flag ) flag = Replace_AND_Gates();
	while ( flag ) {
		Eliminate_Redundancy();
		flag = Replace_Equivalent_Lit();
		flag = flag || Replace_AND_Gates();
	}
	Block_Binary_Clauses();
	if ( running_options.recover_exterior ) Transform_Exterior_Into_Clauses();
	return true;
}

bool Preprocessor::Replace_AND_Gates()
{
	if ( !running_options.detect_AND_gates ) return false;
	StopWatch watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	assert( running_options.detect_lit_equivalence );
	for ( unsigned i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) {
		_long_clauses[i].Free();
	}
	_long_clauses.resize( _old_num_long_clauses );
	Generate_Long_Watched_Lists();
	Generate_Lit_Membership_Lists();
	bool happened = false;
	CNF_Formula * cnf = nullptr;
	if ( DEBUG_OFF ) cnf = Output_Processed_Clauses();
	for ( Variable i = _max_var; i > Variable::start; i-- ) {
		if ( Var_Decided( i ) || _lit_equivalences[i + i] != i + i ) continue;
		bool found = false;
		if ( Detect_Gate( Literal( i, false ) ) ) found = true;
		else if ( Detect_Gate( Literal( i, true ) ) ) found = true;
		if ( !found ) continue;
		Literal output = _and_gates.back().Output();
		if ( _and_gates.back().Is_Lit_Equivalence() ) {
			if ( DEBUG_OFF ) cout << "replace " << _and_gates.back() << endl;
			Replace_Single_Lit_Equivalence( _and_gates.back().Inputs( 0 ), output );
			happened = true;
			_and_gates.pop_back();
			_fixed_num_vars++;
			if ( DEBUG_OFF ) {
				Verify_Binary_Clauses();
				Verify_Watched_Lists();
				Verify_Long_Lit_Membership_Lists();
			}
		}
		else if ( Gain_Of_Gate_Substitution( _and_gates.back() ) >= -1 ) {
			if ( DEBUG_OFF ) cout << "replace " << _and_gates.back() << endl;
			Gate_Substitution_Binary_Clause( _and_gates.back() );
			Gate_Substitution_Long_Clause( _and_gates.back() );
			Gate_Substitution_Binary_Learnt( _and_gates.back() );
			happened = true;
			_fixed_num_vars++;
			if ( DEBUG_OFF ) {
				Verify_Binary_Clauses();
				Verify_Watched_Lists();
				Verify_Long_Lit_Membership_Lists();
			}
		}
		else _and_gates.pop_back();
		_old_num_long_clauses = _long_clauses.size();
		if ( DEBUG_OFF ) Verify_Processed_Clauses( *cnf );
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		_long_lit_membership_lists[lit].clear();
		lit = Literal( i, true );
		_long_lit_membership_lists[lit].clear();
	}
	delete cnf;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_gates += watch.Get_Elapsed_Seconds();
	return happened;
}

void Preprocessor::Generate_Lit_Membership_Lists()
{
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		_long_lit_membership_lists[clause[0]].push_back( i );
		_long_lit_membership_lists[clause[1]].push_back( i );
		_long_lit_membership_lists[clause[2]].push_back( i );
		for ( unsigned j = 3; j < clause.Size(); j++ ) {
			_long_lit_membership_lists[clause[j]].push_back( i );
		}
	}
}

bool Preprocessor::Detect_Gate( Literal output )
{
	vector<Literal> imps;
	Implied_Literals_Approx( output, imps );
	unsigned old_num_dec_stack = _num_dec_stack;
	Assign( ~output );
	BCP( _num_dec_stack - 1 );
	Reason conf;
	unsigned i;
	for ( i = 0; i < imps.size(); i++ ) {
		if ( Lit_UNSAT( imps[i] ) ) {
			conf = _reasons[imps[i].Var()];
			for ( ; _dec_stack[_num_dec_stack - 1].Var() != imps[i].Var(); _num_dec_stack-- ) {
				Un_Assign( _dec_stack[_num_dec_stack - 1].Var() );
			}
			_big_learnt[0] = imps[i];
			_big_learnt.Resize( 1 );
			break;
		}
		else if ( Lit_Undecided( imps[i] ) ) {
			Assign( imps[i] );
			conf = BCP( _num_dec_stack - 1 );
			if ( conf != Reason::undef ) {
				_big_learnt[0] = _big_learnt[1];
				_big_learnt.Resize( 0 );
				break;
			}
		}
	}
	if ( i < imps.size() ) {
		_var_seen[output.Var()] = true;
//		cerr << "output = " << ExtLit( output ) << endl;  // ToRemove
//		cerr << "<-> " << ExtLit( _big_learnt[0] ) << endl;  // ToRemove
		Ascertain_Gate( output, conf );
		_var_seen[output.Var()] = false;
		Un_BCP( old_num_dec_stack );
		if ( debug_options.verify_AND_gates ) Verify_AND_Gate( _and_gates.back() );
		return true;
	}
	else {
		Un_BCP( old_num_dec_stack );
		return false;
	}
}

void Preprocessor::Ascertain_Gate( Literal output, Reason confl )
{
//	if ( _assignment[1] == 0 && _assignment[2] == 0 && _assignment[3] == 0 && _assignment[4] == 1 && _assignment[5] == 1 && _assignment[6] == 0 ) {
//		Compile_Top_Down_Display_Clauses( cout, true );
//		Compile_Top_Down_Display_Watched_List( cout );
//	}
	unsigned num_ip = 0;
	Variable current;
	if ( _big_learnt.Size() == 0 ) {
		current = _big_learnt[0].Var();
		if ( _reasons[current] != Reason::undef ) {
			_var_seen[current] = true;
			num_ip++;
		}
		else {
			_big_learnt[0] = Literal( current, _assignment[current] );
			_big_learnt.Resize( 1 );  /// _big_learnt[1] is reserved
		}
	}
	unsigned index = _num_dec_stack;
	while ( true ) {
		if ( confl == Reason::undef ) {}  // confl.Is_Clause_Reason( Reason::undef ) is true
		else if ( confl.Is_Clause_Reason() ) {
			Clause & clause = _long_clauses[confl.Clause_Value()];
			Variable var = clause[1].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				num_ip++;
				if ( _reasons[var] == Reason::undef ) _big_learnt.Add_Lit( ~clause[1] );
			}
			var = clause[2].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				num_ip++;
				if ( _reasons[var] == Reason::undef ) _big_learnt.Add_Lit( ~clause[2] );
			}
			for ( unsigned i = 3; i < clause.Size(); i++ ) {
				var = clause[i].Var();
				if ( !_var_seen[var] ) {
					_var_seen[var] = true;
					num_ip++;
					if ( _reasons[var] == Reason::undef ) _big_learnt.Add_Lit( ~clause[i] );
				}
			}
		}
		else {
			Variable var = confl.Lit_Value().Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				num_ip++;
				if ( _reasons[var] == Reason::undef ) _big_learnt.Add_Lit( ~confl.Lit_Value() );
			}
		}
		if ( num_ip == 0 ) break;
		for ( current = _dec_stack[--index].Var(); !_var_seen[current]; current = _dec_stack[--index].Var() ) {}
		confl = _reasons[current];
		_var_seen[current] = false;
		num_ip--;
	}
	_var_seen[_big_learnt[0].Var()] = false;
	for ( unsigned i = 1; i < _big_learnt.Size(); i++ ) {
		_var_seen[_big_learnt[i].Var()] = false;
	}
	_and_gates.push_back( AND_Gate( _big_learnt, output ) );
}

void Preprocessor::Replace_Single_Lit_Equivalence( Literal lit1, Literal lit2 )
{
	if ( lit1 > lit2 ) {
		Literal tmp = lit2;
		lit2 = lit1;
		lit1 = tmp;
	}
	assert( _lit_equivalences[lit1] == lit1 && lit1 < lit2 );
	_lit_equivalences[lit2] = lit1;
	_lit_equivalences[~lit2] = ~lit1;
	for ( Variable i = lit2.Var().Next(); i <= _max_var; i++ ) {
		Literal lit = _lit_equivalences[i + i];
		if ( lit.Var() == lit2.Var() ) {
			_lit_equivalences[i + i] = _lit_equivalences[lit];
			_lit_equivalences[i + i + 1] = ~_lit_equivalences[lit];
		}
	}
	Replace_Single_Lit_Equivalence_Binary_Clauses( lit1, lit2 );
	Replace_Single_Lit_Equivalence_Binary_Clauses( ~lit1, ~lit2 );
	Replace_Single_Lit_Equivalence_Binary_Learnts( lit1, lit2 );
	Replace_Single_Lit_Equivalence_Binary_Learnts( ~lit1, ~lit2 );
	Replace_Single_Lit_Equivalence_Long_Clauses( lit1, lit2 );
	Replace_Single_Lit_Equivalence_Long_Clauses( ~lit1, ~lit2 );
}

void Preprocessor::Replace_Single_Lit_Equivalence_Binary_Clauses( Literal lit1, Literal lit2 )
{
	assert( lit1 == _lit_equivalences[lit1] );
	while ( _old_num_binary_clauses[lit2] > 0 ) {
		Literal lit = _binary_clauses[lit2][0];
		Remove_Old_Binary_Clause( lit2, 0 );
		if ( lit1.Var() != lit.Var() ) Add_Old_Binary_Clause( lit1, lit );
	}
}

void Preprocessor::Remove_Old_Binary_Clause( Literal lit, unsigned loc )
{
	Literal lit2 = _binary_clauses[lit][loc];
	vector<Literal>::iterator begin = _binary_clauses[lit2].begin(), itr;
	for ( itr = begin; *itr != lit; itr++ ) {}
	if ( _old_num_binary_clauses[lit2] == _binary_clauses[lit2].size() ) {
		Simply_Erase_Vector_Element( _binary_clauses[lit2], itr - begin );  // remove last old literal
	}
	else {
		*itr = _binary_clauses[lit2][_old_num_binary_clauses[lit2]-1];  // rewrite \lit
		Simply_Erase_Vector_Element( _binary_clauses[lit2], _old_num_binary_clauses[lit2]-1 );  // remove last old literal

	}
	_old_num_binary_clauses[lit2]--;
	if ( _old_num_binary_clauses[lit] == _binary_clauses[lit].size() ) {
		Simply_Erase_Vector_Element( _binary_clauses[lit], loc );  // remove loc from _binary_clauses[lit]
	}
	else {
		 _binary_clauses[lit][loc] = _binary_clauses[lit][_old_num_binary_clauses[lit]-1];  // rewrite \lit2
		Simply_Erase_Vector_Element( _binary_clauses[lit], _old_num_binary_clauses[lit]-1 );  // remove last old literal
	}
	_old_num_binary_clauses[lit]--;
}

void Preprocessor::Replace_Single_Lit_Equivalence_Binary_Learnts( Literal lit1, Literal lit2 )
{
	assert( lit1 == _lit_equivalences[lit1] );
	while ( _old_num_binary_clauses[lit2] < _binary_clauses[lit2].size() ) {
		Literal lit = _binary_clauses[lit2][_old_num_binary_clauses[lit2]];
		Simply_Erase_Vector_Element( _binary_clauses[lit2], _old_num_binary_clauses[lit2] );
		unsigned i;
		for ( i = 0; _binary_clauses[lit][i] != lit2; i++ ) {}
		Simply_Erase_Vector_Element( _binary_clauses[lit], i );
		if ( lit1.Var() != lit.Var() ) Add_Binary_Clause_Naive( lit1, lit );
	}
}

void Preprocessor::Replace_Single_Lit_Equivalence_Long_Clauses( Literal lit1, Literal lit2 )
{
	while ( !_long_lit_membership_lists[lit2].empty() ) {
		unsigned cid = _long_lit_membership_lists[lit2][0];
		Clause & clause = _long_clauses[cid];
		unsigned i;
		for ( i = 0; clause[i] != lit2; i++ ) {
			_big_clause[i] = clause[i];
		}
		_big_clause[i] = lit1;
		for ( i++; i < clause.Size(); i++ ) {
			_big_clause[i] = clause[i];
		}
		_big_clause.Resize( clause.Size() );
		unsigned size = Add_Old_Clause_Binary_Learnt( _big_clause );
		if ( size >= 3 ) {
			Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
		}
		Remove_From_Lit_Membership_Lists( cid );
		Remove_Old_Long_Clause_No_Learnt( cid );
	}
}

void Preprocessor::Add_To_Lit_Membership_Lists( unsigned clauseID )
{
	Clause & clause = _long_clauses[clauseID];
	_long_lit_membership_lists[clause[0]].push_back( clauseID );
	_long_lit_membership_lists[clause[1]].push_back( clauseID );
	_long_lit_membership_lists[clause[2]].push_back( clauseID );
	for ( unsigned i = 3; i < clause.Size(); i++ ) {
		_long_lit_membership_lists[clause[i]].push_back( clauseID );
	}
}

void Preprocessor::Remove_From_Lit_Membership_Lists( unsigned clauseID )
{
	Clause & clause = _long_clauses[clauseID];
	Literal lit = clause[0];
	unsigned j;
	for ( j = 0; clauseID != _long_lit_membership_lists[lit][j]; j++ ) {}
	Simply_Erase_Vector_Element( _long_lit_membership_lists[lit], j );
	lit = clause[1];
	for ( j = 0; clauseID != _long_lit_membership_lists[lit][j]; j++ ) {}
	Simply_Erase_Vector_Element( _long_lit_membership_lists[lit], j );
	lit = clause[2];
	for ( j = 0; clauseID != _long_lit_membership_lists[lit][j]; j++ ) {}
	Simply_Erase_Vector_Element( _long_lit_membership_lists[lit], j );
	for ( unsigned i = 3; i < clause.Size(); i++ ) {
		lit = clause[i];
		for ( j = 0; clauseID != _long_lit_membership_lists[lit][j]; j++ ) {}
		Simply_Erase_Vector_Element( _long_lit_membership_lists[lit], j );
	}
	unsigned replacedID = _long_clauses.size() - 1;
	if ( clauseID == replacedID ) return;
	Clause & replaced = _long_clauses[replacedID];
	lit = replaced[0];
	for ( j = 0; replacedID != _long_lit_membership_lists[lit][j]; j++ ) {}
	_long_lit_membership_lists[lit][j] = clauseID;
	lit = replaced[1];
	for ( j = 0; replacedID != _long_lit_membership_lists[lit][j]; j++ ) {}
	_long_lit_membership_lists[lit][j] = clauseID;
	lit = replaced[2];
	for ( j = 0; replacedID != _long_lit_membership_lists[lit][j]; j++ ) {}
	_long_lit_membership_lists[lit][j] = clauseID;
	for ( unsigned i = 3; i < replaced.Size(); i++ ) {
		lit = replaced[i];
		for ( j = 0; replacedID != _long_lit_membership_lists[lit][j]; j++ ) {}
		_long_lit_membership_lists[lit][j] = clauseID;
	}

}

int Preprocessor::Gain_Of_Gate_Substitution( AND_Gate & gate )
{
	Literal output = gate.Output();
	int gain = _long_lit_membership_lists[output].size() + _long_lit_membership_lists[~output].size();
	_big_clause[0] = ~gate.Inputs(0);
	_big_clause[1] = ~gate.Inputs(1);
	for ( unsigned i = 2; i < gate.Inputs_Size(); i++ ) {
		_big_clause[i] = ~gate.Inputs(i);
	}
	for ( unsigned i = 0; i < _old_num_binary_clauses[~output]; i++ ) {
		_big_clause.Resize( 1 + gate.Inputs_Size() );
		_big_clause.Last_Lit() = _binary_clauses[~output][i];
		Simplify_Clause( _big_clause );
		gain -= ( _big_clause.Size() >= 3 );
	}
	for ( unsigned k = 0; k < _long_lit_membership_lists[output].size(); k++ ) {
		Clause & clause = _long_clauses[_long_lit_membership_lists[output][k]];
		unsigned i;
		for ( i = 0; clause[i] != output; i++ ) {
			_big_clause[i] = clause[i];
		}
		for ( i++; i < clause.Size(); i++ ) {
			_big_clause[i-1] = clause[i];
		}
		_big_clause.Resize( clause.Size() );
		_big_clause.Last_Lit() = gate.Inputs( 0 );
		Simplify_Clause( _big_clause );
		gain -= ( _big_clause.Size() >= 3 );
		_big_clause.Resize( clause.Size() );
		_big_clause.Last_Lit() = gate.Inputs( 1 );
		Simplify_Clause( _big_clause );
		gain -= ( _big_clause.Size() >= 3 );
		for ( i = 2; i < gate.Inputs_Size(); i++ ) {
			_big_clause.Resize( clause.Size() );
			_big_clause.Last_Lit() = gate.Inputs( i );
			Simplify_Clause( _big_clause );
			gain -= ( _big_clause.Size() >= 3 );
		}
	}
	for ( unsigned k = 0; k < _long_lit_membership_lists[~output].size(); k++ ) {
		Clause & clause = _long_clauses[_long_lit_membership_lists[~output][k]];
		_big_clause.Resize( clause.Size() - 1 + gate.Inputs_Size() );
		unsigned i;
		for ( i = 0; clause[i] != ~output; i++ ) {
			_big_clause[i] = clause[i];
		}
		for ( i++; i < clause.Size(); i++ ) {
			_big_clause[i-1] = clause[i];
		}
		_big_clause[i-1] = ~gate.Inputs( 0 );
		_big_clause[i] = ~gate.Inputs( 1 );
		for ( unsigned j = 2; j < gate.Inputs_Size(); j++ ) {
			_big_clause[i-1+j] = ~gate.Inputs( j );
		}
		Simplify_Clause( _big_clause );
		gain -= ( _big_clause.Size() >= 3 );
	}
	return gain;
}

void Preprocessor::Simplify_Clause( Big_Clause & clause )
{
	_lit_seen[clause[0]] = true;
	unsigned i, new_size = 1;
	for ( i = 1; i < clause.Size(); i++ ) {
		Literal lit = clause[i];
		if ( _lit_seen[lit] ) continue;
		else if ( _lit_seen[~lit] ) break;
		else {
			clause[new_size++] = lit;
			_lit_seen[lit] = true;
		}
	}
	_lit_seen[clause[0]] = false;
	for ( unsigned j = 1; j < new_size; j++ ) _lit_seen[clause[j]] = false;
	if ( i < clause.Size() ) clause.Clear();
	else clause.Resize( new_size );
}

void Preprocessor::Gate_Substitution_Binary_Clause( AND_Gate & gate )
{
	Literal output = gate.Output();
	while ( _old_num_binary_clauses[output] > 0 ) {
		Literal lit = _binary_clauses[output][0];
		Remove_Old_Binary_Clause( output, 0 );
		if ( gate.Inputs(0).Var() != lit.Var() ) Add_Old_Binary_Clause( gate.Inputs(0), lit );
		if ( gate.Inputs(1).Var() != lit.Var() ) Add_Old_Binary_Clause( gate.Inputs(1), lit );
		for ( unsigned j = 2; j < gate.Inputs_Size(); j++ ) {
			if ( gate.Inputs(j).Var() != lit.Var() ) Add_Old_Binary_Clause( gate.Inputs(j), lit );
		}
	}
	while ( _old_num_binary_clauses[~output] > 0 ) {
		Literal lit = _binary_clauses[~output][0];
		Remove_Old_Binary_Clause( ~output, 0 );
		_big_clause.Resize( 1 + gate.Inputs_Size() );
		_big_clause[0] = lit;
		_big_clause[1] = ~gate.Inputs(0);
		_big_clause[2] = ~gate.Inputs(1);
		for ( unsigned j = 2; j < gate.Inputs_Size(); j++ ) {
			_big_clause[j+1] = ~gate.Inputs(j);
		}
		unsigned size = Add_Old_Clause_Binary_Learnt( _big_clause );
		if ( size >= 3 ) Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
	}
}

void Preprocessor::Gate_Substitution_Long_Clause( AND_Gate & gate )  // ToDo: improve
{
	Literal output = gate.Output();
	while ( !_long_lit_membership_lists[output].empty() ) {
		unsigned cid = _long_lit_membership_lists[output][0];
		Clause & clause = _long_clauses[cid];
//		cerr << clause << endl;  // ToRemove
		unsigned csize = clause.Size();  // realloc might change \clause
		unsigned i;
		for ( i = 0; clause[i] != output; i++ ) {
			_big_clause[i] = clause[i];
		}
		for ( i++; i < clause.Size(); i++ ) {
			_big_clause[i-1] = clause[i];
		}
		_big_clause.Resize( csize );
		_big_clause.Last_Lit() = gate.Inputs( 0 );
		unsigned size = Add_Old_Clause_Binary_Learnt( _big_clause );
		if ( size >= 3 ) Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
		_big_clause.Resize( csize );
		_big_clause.Last_Lit() = gate.Inputs( 1 );
		size = Add_Old_Clause_Binary_Learnt( _big_clause );
		if ( size >= 3 ) Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
		for ( i = 2; i < gate.Inputs_Size(); i++ ) {
			_big_clause.Resize( csize );
			_big_clause.Last_Lit() = gate.Inputs( i );
			size = Add_Old_Clause_Binary_Learnt( _big_clause );
			if ( size >= 3 ) Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
		}
		Remove_From_Lit_Membership_Lists( cid );
		Remove_Old_Long_Clause_No_Learnt( cid );
	}
	_long_lit_membership_lists[output].clear();
	while ( !_long_lit_membership_lists[~output].empty() ) {
		unsigned cid = _long_lit_membership_lists[~output][0];
		Clause & clause = _long_clauses[cid];
		_big_clause.Resize( clause.Size() - 1 + gate.Inputs_Size() );
		unsigned i;
		for ( i = 0; clause[i] != ~output; i++ ) {
			_big_clause[i] = clause[i];
		}
		for ( i++; i < clause.Size(); i++ ) {
			_big_clause[i-1] = clause[i];
		}
		_big_clause[i-1] = ~gate.Inputs( 0 );
		_big_clause[i] = ~gate.Inputs( 1 );
		for ( unsigned j = 2; j < gate.Inputs_Size(); j++ ) {
			_big_clause[i-1+j] = ~gate.Inputs( j );
		}
		unsigned size = Add_Old_Clause_Binary_Learnt( _big_clause );
		if ( size >= 3 ) Add_To_Lit_Membership_Lists( _long_clauses.size() - 1 );
		Remove_From_Lit_Membership_Lists( cid );
		Remove_Old_Long_Clause_No_Learnt( cid );
	}
	_long_lit_membership_lists[~output].clear();
}

unsigned Preprocessor::Add_Old_Clause_Binary_Learnt( Big_Clause & clause )
{
	_lit_seen[clause[0]] = true;
	unsigned i, new_size = 1;
	for ( i = 1; i < clause.Size(); i++ ) {
		Literal lit = clause[i];
		if ( _lit_seen[lit] ) continue;
		else if ( _lit_seen[~lit] ) break;
		else {
			clause[new_size++] = lit;
			_lit_seen[lit] = true;
		}
	}
	_lit_seen[clause[0]] = false;
	for ( unsigned j = 1; j < new_size; j++ ) _lit_seen[clause[j]] = false;
	if ( i < clause.Size() ) return 0;
	else if ( new_size == 2 ) {
		Add_Old_Binary_Clause( clause[0], clause[1] );
		return 2;
	}
	else {
		clause.Resize( new_size );
		_long_clauses.push_back( clause );
		_long_watched_lists[clause[0]].push_back( _long_clauses.size() - 1 );
		_long_watched_lists[clause[1]].push_back( _long_clauses.size() - 1 );
		return new_size;
	}
}

void Preprocessor::Gate_Substitution_Binary_Learnt( AND_Gate & gate )
{
	Literal output = gate.Output();
	while ( _old_num_binary_clauses[output] < _binary_clauses[output].size() ) {
		Literal lit = _binary_clauses[output][_old_num_binary_clauses[output]];
		Simply_Erase_Vector_Element( _binary_clauses[output], _old_num_binary_clauses[output] );
		unsigned i;
		for ( i = 0; _binary_clauses[lit][i] != output; i++ ) {}
		Simply_Erase_Vector_Element( _binary_clauses[lit], i );
		if ( gate.Inputs( 0 ).Var() != lit.Var() ) Add_Binary_Clause_Naive( gate.Inputs( 0 ), lit );
		if ( gate.Inputs( 1 ).Var() != lit.Var() ) Add_Binary_Clause_Naive( gate.Inputs( 0 ), lit );
		for ( i = 2; i < gate.Inputs_Size(); i++ ) {
			if ( gate.Inputs( i ).Var() != lit.Var() ) Add_Binary_Clause_Naive( gate.Inputs( i ), lit );
		}
	}
	while ( _old_num_binary_clauses[~output] < _binary_clauses[~output].size() ) {
		Literal lit = _binary_clauses[~output][_old_num_binary_clauses[~output]];
		Simply_Erase_Vector_Element( _binary_clauses[~output], _old_num_binary_clauses[~output] );
		unsigned i;
		for ( i = 0; _binary_clauses[lit][i] != ~output; i++ ) {}
		Simply_Erase_Vector_Element( _binary_clauses[lit], i );
		_big_clause.Resize( 1 + gate.Inputs_Size() );
		_big_clause[0] = lit;
		_big_clause[1] = ~gate.Inputs( 0 );
		_big_clause[2] = ~gate.Inputs( 1 );
		for ( i = 2; i < gate.Inputs_Size(); i++ ) {
			_big_clause[i+1] = ~gate.Inputs( i );
		}
		Add_Only_Old_Binary_Clause( _big_clause );
	}
}

void Preprocessor::Add_Only_Old_Binary_Clause( Big_Clause & clause )
{
	_lit_seen[clause[0]] = true;
	unsigned i, new_size = 1;
	for ( i = 1; i < clause.Size(); i++ ) {
		Literal lit = clause[i];
		if ( _lit_seen[lit] ) continue;
		else if ( _lit_seen[~lit] ) break;
		else {
			clause[new_size++] = lit;
			_lit_seen[lit] = true;
		}
	}
	_lit_seen[clause[0]] = false;
	for ( unsigned j = 1; j < new_size; j++ ) _lit_seen[clause[j]] = false;
	if ( i == clause.Size() && new_size == 2 ) {
		Add_Old_Binary_Clause( clause[0], clause[1] );
	}
}

void Preprocessor::Shrink_Max_Var()
{
	Check_Var_Appearances();
	unsigned num_removed = 0, num_omitted = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_seen[i] ) {
			num_omitted += ( Var_Undecided( i ) && _lit_equivalences[i + i] == i + i );
			num_removed++;
			_lit_equivalences[i + i] = Literal( i, false );
			_lit_equivalences[i + i + 1] = Literal( i, true );
			_var_map[i] = Variable::undef;
		}
		else {
			_var_seen[i] = false;  // was assigned in Check_Omitted_Vars
			_var_map[i] = i - num_removed;
		}
	}
	num_omitted -= _and_gates.size();
	_and_gates.clear();
	Un_BCP( 0 );
	_unary_clauses.clear();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( _var_map[i] == Variable::undef ) continue;
		Literal lit = Literal( i, false );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			_binary_clauses[lit][j] = Literal( _var_map[lit2.Var()], lit2.Sign() );
		}
		Literal lit_map = Literal( _var_map[i], false );
		_binary_clauses[lit_map] = _binary_clauses[lit];
		_old_num_binary_clauses[lit_map] = _old_num_binary_clauses[lit];
		_long_watched_lists[lit_map] = _long_watched_lists[lit];
		_heur_decaying_sum[lit_map] = _heur_decaying_sum[lit];
		lit = Literal( i, true );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			_binary_clauses[lit][j] = Literal( _var_map[lit2.Var()], lit2.Sign() );
		}
		lit_map = Literal( _var_map[i], true );
		_binary_clauses[lit_map] = _binary_clauses[lit];
		_old_num_binary_clauses[lit_map] = _old_num_binary_clauses[lit];
		_long_watched_lists[lit_map] = _long_watched_lists[lit];
		_heur_decaying_sum[lit_map] = _heur_decaying_sum[lit];
	}
	for ( Variable i = Variable( _max_var - num_removed + 1 ); i <= _max_var; i++ ) {
		Literal lit = Literal( i, false );
		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
		lit = Literal( i, true );
		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		Literal lit = _long_clauses[i][0];
		_long_clauses[i][0] = Literal( _var_map[lit.Var()], lit.Sign() );
		lit = _long_clauses[i][1];
		_long_clauses[i][1] = Literal( _var_map[lit.Var()], lit.Sign() );
		lit = _long_clauses[i][2];
		_long_clauses[i][2] = Literal( _var_map[lit.Var()], lit.Sign() );
		for ( unsigned j = 3; j < _long_clauses[i].Size(); j++ ) {
			lit = _long_clauses[i][j];
			_long_clauses[i][j] = Literal( _var_map[lit.Var()], lit.Sign() );
		}
	}
	_max_var = Variable( _max_var - num_removed + num_omitted );
	_fixed_num_vars = 0;
	_model_pool->Shrink_Max_Var( _max_var, _var_map );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_sorted_lits[i + i - Literal::start] = Literal( i, false );
		_heur_sorted_lits[i + i + 1 - Literal::start] = Literal( i, true );
	}
	_heur_lit_sentinel = Literal( _max_var.Next(), false );
	_heur_sorted_lits[2 * _max_var + 2 - Literal::start] = _heur_lit_sentinel;  // NOTE: this line guarantee the correctness of "Branch"
	_heur_sorted_lits[2 * _max_var + 3 - Literal::start] = ~_heur_lit_sentinel;
	_heur_decaying_sum[_heur_lit_sentinel] = -1;  /// NOTE: to speed up Branch and Branch_Component by using only one comparison in for-loop
	_heur_decaying_sum[~_heur_lit_sentinel] = -2;  /// NOTE: return 2 * _max_var + 2 exactly when all variables are assigned
	switch( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Quick_Sort_Weight_Reverse( _heur_sorted_lits, 2 * NumVars( _max_var ), _heur_decaying_sum );
		break;
	case Heuristic_Literal_Heap:
		_heur_lits_heap.Build( _heur_sorted_lits, 2 * NumVars( _max_var ) );
		break;
	}
}

void Preprocessor::Check_Var_Appearances()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_var_seen[i] = ( _old_num_binary_clauses[i + i] + _old_num_binary_clauses[i + i + 1] > 0 );
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		_var_seen[clause[0].Var()] = true;
		_var_seen[clause[1].Var()] = true;
		_var_seen[clause[2].Var()] = true;
		for ( unsigned j = 3; j < clause.Size(); j++ ) {
			_var_seen[clause[j].Var()] = true;
		}
	}
}

bool Preprocessor::Generate_Models_External( vector<Model *> & models )
{
	StopWatch watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_external_solve++;
	bool * var_filled = new bool [_max_var + 1];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		var_filled[i] = true;
	}
	vector<vector<int>> clauses;
	Prepare_Ext_Clauses_Without_Omitted_Vars( clauses, var_filled );  // var_filled is assigned in this function
	_minisat_extra_output.return_model = true;
	_minisat_extra_output.return_units = true;
	_minisat_extra_output.return_learnt_max_len = 8;
	vector<int8_t> emodel( _max_var + 1 );
	for ( unsigned i = 0; i < models.size(); i++ ) {
		for ( Variable j = Variable::start; j <= _max_var; j++ ) {
			emodel[ExtVar( j )] = (*models[i])[j];
		}
		_minisat_extra_output.models.push_back( emodel );
	}
	unsigned minisat_extra_output_old_num_models = _minisat_extra_output.models.size();
	bool sat = Minisat::Ext_Backbone( clauses, _minisat_extra_output );
	if ( sat ) {
		for ( unsigned i = 0; i < _minisat_extra_output.units.size(); i++ ) {
			Literal lit = InternLit( _minisat_extra_output.units[i] );
			if ( !var_filled[lit.Var()] && Lit_Undecided( lit ) ) {
				Assign( lit );
				BCP( _num_dec_stack - 1 );
			}
		}
		for ( unsigned i = 0; i < _minisat_extra_output.short_learnts[0].size(); i += 2 ) {
			Add_Binary_Clause_Naive( InternLit( _minisat_extra_output.short_learnts[0][i] ), InternLit( _minisat_extra_output.short_learnts[0][i+1] ) );
		}
		for ( unsigned i = 3; i <= _minisat_extra_output.return_learnt_max_len; i++ ) {
			vector<int> & elits = _minisat_extra_output.short_learnts[i-2];
			for ( vector<int>::const_iterator begin = elits.cbegin(); begin < elits.cend(); begin += i ) {
				vector<Literal> lits( i );
				for ( unsigned j = 0; j < i; j++ ) {
					lits[j] = InternLit( *(begin + j) );
				}
				_long_clauses.push_back( lits );
			}
		}
		for ( unsigned i = minisat_extra_output_old_num_models; i < _minisat_extra_output.models.size(); i++ ) {
			Add_Model( _minisat_extra_output.models[i], models );
		}
		_minisat_extra_output.models.clear();
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.num_unsat_solve++;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_external_solve += watch.Get_Elapsed_Seconds();
	delete [] var_filled;
	return sat;
}

void Preprocessor::Display_Statistics_Sharp( ostream & out )
{
	unsigned omitted = Num_Omitted_Vars();
	unsigned unsimplifiable = NumVars( _max_var ) - _unary_clauses.size() - Lit_Equivalency_Size() - _and_gates.size() - omitted;
	out << running_options.display_prefix << "Number of unsimplifiable variables: " << unsimplifiable
		<< " (" << _unary_clauses.size() << " unit, " << Lit_Equivalency_Size() << " equ, ";
	if ( running_options.detect_AND_gates ) out << _and_gates.size() << " AND, ";
	out << omitted << " omit)" << endl;
	out << running_options.display_prefix << "Number of unsimplifiable non-unary clauses: " << Old_Num_Clauses() - _unary_clauses.size() << endl;
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) {
		out << running_options.display_prefix << "Preprocessing Time: " << statistics.time_preprocess << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) {
		out << running_options.display_prefix << "    Time of SAT: " << statistics.time_solve << endl;
		if ( running_options.block_clauses ) out << running_options.display_prefix << "    Time of blocking clauses: " << statistics.time_block_clauses << endl;
		if ( running_options.block_lits ) out << running_options.display_prefix << "    Time of blocking literals: " << statistics.time_block_lits << endl;
		if ( running_options.detect_lit_equivalence ) out << running_options.display_prefix << "    Time of replacing literal equivalency: " << statistics.time_replace_lit_equivalences << endl;
		if ( running_options.detect_AND_gates ) out << running_options.display_prefix << "    Time of replacing gates: " << statistics.time_replace_gates << endl;
	}
}

void Preprocessor::Verify_AND_Gate( AND_Gate & gate )
{
	assert( gate.Inputs_Size() > 0 );
	Literal output = gate.Output();
	if ( gate.Is_Lit_Equivalence() ) {
		assert( Imply_Binary_Clause_BCP( ~output, gate.Inputs( 0 ) ) );
		assert( Imply_Binary_Clause_BCP( output, ~gate.Inputs( 0 ) ) );
		return;
	}
	Big_Clause clause( _max_var );
	clause.Resize( gate.Inputs_Size() );
	for ( unsigned i = 0; i < gate.Inputs_Size(); i++ ) {
		if ( !Imply_Binary_Clause_BCP( ~output, gate.Inputs( i ) ) ) {
			cerr << gate << endl;
			cerr << "The following clause is not implied: " << ExtLit( ~output ) << " " << ExtLit( gate.Inputs( i ) ) << " 0" << endl;
			assert( false );
		}
		clause[i] = ~gate.Inputs( i );
	}
	clause.Add_Lit( output );
	assert( Imply_Long_Clause_BCP( clause ) );
}

void Preprocessor::Verify_Watched_Lists()
{
	for ( Literal l = Literal::start; l <= _max_var + _max_var + 1; l++ ) {
		for ( unsigned j = 0; j < _long_watched_lists[l].size(); j++ ) {
			assert( _long_watched_lists[l][j] < _long_clauses.size() );
		}
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		for ( Literal l = Literal::start; l <= _max_var + _max_var + 1; l++ ) {
			unsigned num = 0;
			for ( unsigned j = 0; j < _long_watched_lists[l].size(); j++ ) {
				num += ( _long_watched_lists[l][j] == i );
			}
			bool check = ( l == _long_clauses[i][0] || l == _long_clauses[i][1] );
			if ( num != check ) {
				cerr << "ERROR[Preprocessor]: Clause " << i << " = " << _long_clauses[i] << " appears " << num << " times" << endl;
				assert( num == check );
			}
		}
	}
}

void Preprocessor::Verify_Long_Lit_Membership_Lists()
{
	for ( Literal l = Literal::start; l <= _max_var + _max_var + 1; l++ ) {
		for ( unsigned j = 0; j < _long_lit_membership_lists[l].size(); j++ ) {
			if ( _long_lit_membership_lists[l][j] >= _long_clauses.size() ) {
				cerr << "_long_lit_membership_lists[" << l << "][" << j << "] = " << _long_lit_membership_lists[l][j] << endl;
				assert( _long_lit_membership_lists[l][j] < _long_clauses.size() );
			}
		}
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		for ( Literal l = Literal::start; l <= _max_var + _max_var + 1; l++ ) {
			unsigned num = 0;
			for ( unsigned j = 0; j < _long_lit_membership_lists[l].size(); j++ ) {
				num += ( _long_lit_membership_lists[l][j] == i );
			}
			Clause & clause = _long_clauses[i];
			bool exi = false;
			for ( unsigned j = 0; j < clause.Size(); j++ ) {
				exi = exi || ( l == clause[j] );
			}
			if ( num != exi ) {
				cerr << "_long_clauses[" << i << "] = " << _long_clauses[i] << endl;
				cerr << "_long_lit_membership_lists[" << l << "] has " << num << " No. " << i << endl;
				assert( num == exi );
			}
		}
	}
}

bool Preprocessor::Preprocess_Sharp( WCNF_Formula & cnf, vector<Model *> & models )
{
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_preprocessing_process ) {
		cout << running_options.display_prefix << "Number of original variables: " << cnf.Num_Vars() << endl;
		cout << running_options.display_prefix << "Number of original clauses: " << cnf.Num_Clauses() << endl;
	}
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( !Load_Instance( cnf ) ) {
		Un_BCP( 0 );
		return false;
	}
	bool sat = Preprocess_Sharp( cnf.Weights(), models );
	if ( running_options.profile_preprocessing >= Profiling_Abstract ) statistics.time_preprocess += begin_watch.Get_Elapsed_Seconds();
	if ( !sat ) {
		if ( running_options.display_preprocessing_process ) {
			cout << "s UNSATISFIABLE" << endl;
		}
		if ( debug_options.verify_processed_clauses ) {
			Verify_Satisfiability( cnf, false );
		}
	}
	else {
		if ( running_options.display_preprocessing_process ) {
			cout << "s SATISFIABLE" << endl;
			Display_Statistics_Sharp( cout );
		}
		if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
		if ( debug_options.verify_processed_clauses ) Verify_Processed_Clauses( cnf );
	}
	return sat;
}

bool Preprocessor::Preprocess_Sharp( const vector<double> & weights, vector<Model *> & models )
{
	StopWatch tmp_watch;
	assert( _num_levels == 0 );
	Extend_New_Level();  // NOTE: Without this line, the _var_stamps of init implied literals will be UNSIGNED_UNDEF
	Gather_Infor_For_SAT();
	if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
	if ( _max_var > 5000 ) running_options.sat_employ_external_solver_always = true;
	if ( running_options.sat_employ_external_solver_always ) {
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			if ( !models.empty() ) return true;
			else return Solve_External( models );
		}
		if ( !Get_All_Imp_Init_External( models ) ) {
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
	}
	else {
		if ( models.empty() && !Solve( models ) ) {
			Un_BCP( 0 );
			if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
			return false;
		}
		if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
		_fixed_num_vars = _unary_clauses.size();
		Replace_Equivalent_Lit_First();
		if ( running_options.profile_preprocessing >= Profiling_Detail ) tmp_watch.Start();
		if ( !running_options.recognize_backbone ) {
			cerr << "Warning[Preprocessor]: other technologies depend on recognizing backbone!" << endl;
			return true;
		}
		Get_All_Imp_Init( models );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_solve += tmp_watch.Get_Elapsed_Seconds();
	if ( _unary_clauses.size() < _num_dec_stack ) {
		unsigned i = _unary_clauses.size();
		_unary_clauses.push_back( _dec_stack[i] );  // one new unit is already known
		_reasons[_dec_stack[i].Var()] = Reason::undef;
		for ( i++; i < _num_dec_stack; i++ ) {
			_unary_clauses.push_back( _dec_stack[i] );
			_reasons[_dec_stack[i].Var()] = Reason::undef;
		}
		Simplify_Binary_Clauses_By_Unary();
		Simplify_Long_Clauses_By_Unary();
		Simplify_Lit_Equivalences_By_Unary();
	}
	_fixed_num_vars = _unary_clauses.size();
	bool flag;
	for ( unsigned i = 0; i < 2; i++ ) {
		Eliminate_Redundancy();
		flag = Replace_Equivalent_Lit();
		if ( !flag ) break;
	}
	if ( !flag ) flag = Replace_AND_Gates( weights );
	while ( flag ) {
		Eliminate_Redundancy();
		flag = Replace_Equivalent_Lit();
		flag = flag || Replace_AND_Gates( weights );
	}
	Block_Binary_Clauses();
	if ( running_options.recover_exterior ) Transform_Exterior_Into_Clauses();
	return true;
}

bool Preprocessor::Replace_AND_Gates( const vector<double> & weights )
{
	if ( !running_options.detect_AND_gates ) return false;
	StopWatch watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) watch.Start();
	assert( running_options.detect_lit_equivalence );
	for ( unsigned i = _old_num_long_clauses; i < _long_clauses.size(); i++ ) {
		_long_clauses[i].Free();
	}
	_long_clauses.resize( _old_num_long_clauses );
	Generate_Long_Watched_Lists();
	Generate_Lit_Membership_Lists();
	bool happened = false;
//	CNF_Formula * cnf = Output_Processed_Clauses();  // ToRemove
//	cerr << *cnf << endl;  // ToRemove
	for ( Variable i = _max_var; i > Variable::start; i-- ) {
		if ( Var_Decided( i ) || _lit_equivalences[i + i] != i + i ) continue;
		if ( weights[i+i] != weights[i+i+1] ) continue;
		bool found = false;
		if ( Detect_Gate( Literal( i, false ) ) ) found = true;
		else if ( Detect_Gate( Literal( i, true ) ) ) found = true;
		if ( !found ) continue;
		Literal output = _and_gates.back().Output();
		if ( _and_gates.back().Is_Lit_Equivalence() ) {
//			cerr << "replace " << _and_gates.back() << endl;
//			system( "./pause" );
			Replace_Single_Lit_Equivalence( _and_gates.back().Inputs( 0 ), output );
			happened = true;
			_and_gates.pop_back();
			_fixed_num_vars++;
			if ( DEBUG_OFF ) {
				Verify_Binary_Clauses();  // ToRemove
				Verify_Watched_Lists();  // ToRemove
				Verify_Long_Lit_Membership_Lists();  // ToRemove
			}
		}
		else if ( Gain_Of_Gate_Substitution( _and_gates.back() ) >= -1 ) {
//			cerr << "replace " << _and_gates.back() << endl;
//			system( "./pause" );
			Gate_Substitution_Binary_Clause( _and_gates.back() );
			Gate_Substitution_Long_Clause( _and_gates.back() );
			Gate_Substitution_Binary_Learnt( _and_gates.back() );
			happened = true;
			_fixed_num_vars++;
			if ( DEBUG_OFF ) {
				Verify_Binary_Clauses();  // ToRemove
				Verify_Watched_Lists();  // ToRemove
				Verify_Long_Lit_Membership_Lists();  // ToRemove
			}
		}
		else _and_gates.pop_back();
		_old_num_long_clauses = _long_clauses.size();
//		Verify_Processed_Clauses( *cnf );  // ToRemove
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		_long_lit_membership_lists[lit].clear();
		lit = Literal( i, true );
		_long_lit_membership_lists[lit].clear();
	}
//	delete cnf;  // ToRemove
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_replace_gates += watch.Get_Elapsed_Seconds();
	return happened;
}

void Preprocessor::Transform_Exterior_Into_Clauses()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Store_Binary_Learnts( i + i );
		Store_Binary_Learnts( i + i + 1);
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			_binary_clauses[~lit].push_back( _lit_equivalences[lit] );
			_binary_clauses[_lit_equivalences[lit]].push_back( ~lit );
			_binary_clauses[lit].push_back( ~_lit_equivalences[lit] );
			_binary_clauses[~_lit_equivalences[lit]].push_back( lit );
			_lit_equivalences[lit] = lit;
			_lit_equivalences[~lit] = ~lit;
			_fixed_num_vars--;
		}
	}
	for ( unsigned i = 0; i < _and_gates.size(); i++ ) {
		AND_Gate & gate = _and_gates[i];
		Literal output = gate.Output();
		_big_clause.Resize( gate.Inputs_Size() + 1 );
		for ( unsigned j = 0; j < gate.Inputs_Size(); j++ ) {
			Literal lit = gate.Inputs( j );
			_binary_clauses[~output].push_back( lit );
			_binary_clauses[lit].push_back( ~output );
			_big_clause[j] = ~lit;
		}
		_big_clause[gate.Inputs_Size()] = output;
		_long_clauses.push_back( _big_clause );
		_fixed_num_vars--;
	}
	_and_gates.clear();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Recover_Binary_Learnts( i + i );
		Recover_Binary_Learnts( i + i + 1 );
	}
}

CNF_Formula * Preprocessor::Output_Processed_Clauses()
{
	CNF_Formula * cnf = new CNF_Formula( _max_var );
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		cnf->Add_Unary_Clause( _unary_clauses[i] );
	}
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf->Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			cnf->Add_Binary_Clause( ~lit, _lit_equivalences[lit] );
			cnf->Add_Binary_Clause( lit, ~_lit_equivalences[lit] );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf->Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		lit++;
	}
	for ( unsigned i = 0; i < _and_gates.size(); i++ ) {
		AND_Gate & gate = _and_gates[i];
		Literal output = gate.Output();
		_big_clause.Resize( gate.Inputs_Size() + 1 );
		for ( unsigned j = 0; j < gate.Inputs_Size(); j++ ) {
			cnf->Add_Binary_Clause( ~output, gate.Inputs( j ) );
			_big_clause[j] = ~gate.Inputs( j );
		}
		_big_clause[gate.Inputs_Size()] = output;
		cnf->Add_Clause( _big_clause );
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		cnf->Add_Clause( _long_clauses[i] );
	}
	return cnf;
}

void Preprocessor::Output_Processed_Ext_Clauses( vector<vector<int>> & eclauses )
{
	_big_clause.Resize( 1 );
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		_big_clause[0] = _unary_clauses[i];
		eclauses.push_back( ExtLits( _big_clause ) );
	}
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			eclauses.push_back( ExtLits( lit, _binary_clauses[lit][i] ) );
		}
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			eclauses.push_back( ExtLits( ~lit, _lit_equivalences[lit] ) );
			eclauses.push_back( ExtLits( lit, ~_lit_equivalences[lit] ) );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			eclauses.push_back( ExtLits( lit, _binary_clauses[lit][i] ) );
		}
		lit++;
	}
	for ( unsigned i = 0; i < _and_gates.size(); i++ ) {
		AND_Gate & gate = _and_gates[i];
		Literal output = gate.Output();
		_big_clause.Resize( gate.Inputs_Size() + 1 );
		for ( unsigned j = 0; j < gate.Inputs_Size(); j++ ) {
			eclauses.push_back( ExtLits( ~output, gate.Inputs( j ) ) );
			_big_clause[j] = ~gate.Inputs( j );
		}
		_big_clause[gate.Inputs_Size()] = output;
		eclauses.push_back( ExtLits( _big_clause ) );
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		eclauses.push_back( ExtLits( _long_clauses[i] ) );
	}
}

void Preprocessor::Output_Same_Count_Ext_Clauses( int & num_vars, vector<vector<int>> & eclauses, int & num_omitted_vars )
{
	Check_Var_Appearances();
	num_vars = num_omitted_vars = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_seen[i] ) {
			num_omitted_vars += ( Var_Undecided( i ) && _lit_equivalences[i + i] == i + i );
			continue;
		}
		_var_seen[i] = false;  // was assigned in Check_Omitted_Vars
		_lit_map[i + i] = Literal( Variable( num_vars ), false );
		_lit_map[i + i + 1] = Literal( Variable( num_vars ), true );
		num_vars++;
	}
	num_omitted_vars -= _and_gates.size();
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			eclauses.push_back( ExtLits( _lit_map[lit], _lit_map[_binary_clauses[lit][i]] ) );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			eclauses.push_back( ExtLits( _lit_map[lit], _lit_map[_binary_clauses[lit][i]] ) );
		}
		lit++;
	}
	vector<int> elits;
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		for ( unsigned j = 0; j < _long_clauses[i].Size(); j++ ) {
			elits.push_back( ExtLit( _lit_map[_long_clauses[i][j]] ) );
		}
		eclauses.push_back( elits );
		elits.clear();
	}
}

void Preprocessor::Output_Equivalent_Literal_Pairs( vector<int> & elits )
{
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit.Inc_Var() ) {
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			elits.push_back( ExtLit( _lit_equivalences[lit] ) );
			elits.push_back( ExtLit( lit ) );
		}
	}
}

void Preprocessor::Output_Unary_Clauses( vector<Literal> & units )
{
	units.resize( _unary_clauses.size() );
	for ( unsigned i = 0; i < _unary_clauses.size(); i++ ) {
		units[i] = _unary_clauses[i];
	}
}

void Preprocessor::Output_Binary_Clauses( vector<Literal> & binary_clauses, vector<Literal> & binary_learnts )
{
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
		unsigned i = 0;
		for ( ; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			binary_clauses.push_back( lit );
			binary_clauses.push_back( _binary_clauses[lit][i] );
		}
		for ( ; i < _binary_clauses[lit].size(); i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			binary_learnts.push_back( lit );
			binary_learnts.push_back( _binary_clauses[lit][i] );
		}
	}
}

void Preprocessor::Output_Long_clauses( vector<Clause> & clauses )
{
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause clause = _long_clauses[i].Copy();
		clauses.push_back( clause );
	}
}

void Preprocessor::Display_Processed_Clauses( ostream & out, bool eq )
{
	vector<vector<int>> eclauses;
	if ( eq ) {
		Output_Processed_Ext_Clauses( eclauses );
		Display_Ext_Clauses( out, NumVars( _max_var ), eclauses );
	}
	else {
		int num_vars, num_omitted_vars;
		Output_Same_Count_Ext_Clauses( num_vars, eclauses, num_omitted_vars );
		Display_Ext_Clauses( out, num_vars, eclauses );
	}
}


size_t Preprocessor::Memory()
{
	size_t mem = Solver::Memory() + _solver_krom->Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _long_lit_membership_lists[i + i].capacity() * sizeof(unsigned);
		mem += _long_lit_membership_lists[i + i + 1].capacity() * sizeof(unsigned);
	}
	return mem;
}

unsigned Preprocessor::Num_Omitted_Vars()
{
	Check_Var_Appearances();
	unsigned num_omitted_vars = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_seen[i] ) {
			num_omitted_vars += ( Var_Undecided( i ) && _lit_equivalences[i + i] == i + i );
			continue;
		}
		_var_seen[i] = false;  // was assigned in Check_Omitted_Vars
	}
	return num_omitted_vars - _and_gates.size();
}

void Preprocessor::Draw_Lit_Equivalency( vector<Literal> & equ_pairs )
{
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit.Inc_Var() ) {
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			equ_pairs.push_back( _lit_equivalences[lit] );
			equ_pairs.push_back( lit );
			_lit_equivalences[lit] = lit;
			_lit_equivalences[~lit] = ~lit;
			_fixed_num_vars--;
		}
	}
}

BigFloat Preprocessor::Normalize_Weights( const vector<double> & original_weights, BigFloat * normalized_weights )
{
	for ( Variable i = Variable::start; i <= _max_var;i++ ) {  // eliminate literal equivalences
		Literal lit( i, false );
		Literal lit_equ = _lit_equivalences[lit];
		normalized_weights[lit] = original_weights[lit];
		normalized_weights[~lit] = original_weights[~lit];
		if ( lit == lit_equ ) continue;
		normalized_weights[lit_equ] *= normalized_weights[lit];
		normalized_weights[~lit_equ] *= normalized_weights[~lit];
		normalized_weights[lit] = 0.5;
		normalized_weights[~lit] = 0.5;
		_lit_equivalences[lit] = lit;
		_lit_equivalences[~lit] = lit;
	}
	BigFloat normalized_factor = 1;
	for ( unsigned i = 0; i < _and_gates.size(); i++ ) {  // eliminate AND gates
		AND_Gate & gate = _and_gates[i];
		Literal output = gate.Output();
		assert( normalized_weights[output] == normalized_weights[~output] );
		normalized_factor *= normalized_weights[output];
		normalized_weights[output] = 0.5;
		normalized_weights[~output] = 0.5;
	}
	_and_gates.clear();
	for ( Variable i = Variable::start; i <= _max_var;i++ ) {
		if ( Var_Decided( i ) ) {  // eliminate implied literals
			Literal lit( i, _assignment[i] );
			normalized_factor *= normalized_weights[lit];
			normalized_weights[lit] = 1;
			normalized_weights[~lit] = 0;
			continue;
		}
		BigFloat sum = normalized_weights[i + i] + normalized_weights[i + i + 1];
		normalized_factor *= sum;
		normalized_weights[i + i] /= sum;
		normalized_weights[i + i + 1] = 1 - normalized_weights[i + i];
	}
	if ( running_options.display_preprocessing_process ) {
		cout << running_options.display_prefix << "norm: " << normalized_factor << endl;
	}
	Shrink_Max_Var( normalized_weights );
	return normalized_factor;
}

void Preprocessor::Shrink_Max_Var( BigFloat * normalized_weights )
{
	Check_Var_Appearances();
	unsigned num_removed = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_seen[i] ) {
			assert( _lit_equivalences[i + i] = Literal( i, false ) );
			assert( _lit_equivalences[i + i + 1] = Literal( i, true ) );
			num_removed++;
			_var_map[i] = Variable::undef;
		}
		else {
			_var_seen[i] = false;  // was assigned in Check_Omitted_Vars
			_var_map[i] = i - num_removed;
		}
	}
	if ( num_removed < 32 ) return;
	assert( _and_gates.empty() );
	Un_BCP( 0 );
	_unary_clauses.clear();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( _var_map[i] == Variable::undef ) continue;
		Literal lit = Literal( i, false );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			_binary_clauses[lit][j] = Literal( _var_map[lit2.Var()], lit2.Sign() );
		}
		Literal lit_map = Literal( _var_map[i], false );
		_binary_clauses[lit_map] = _binary_clauses[lit];
		_old_num_binary_clauses[lit_map] = _old_num_binary_clauses[lit];
		_long_watched_lists[lit_map] = _long_watched_lists[lit];
		_heur_decaying_sum[lit_map] = _heur_decaying_sum[lit];
		normalized_weights[lit_map] = normalized_weights[lit];
		lit = Literal( i, true );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			_binary_clauses[lit][j] = Literal( _var_map[lit2.Var()], lit2.Sign() );
		}
		lit_map = Literal( _var_map[i], true );
		_binary_clauses[lit_map] = _binary_clauses[lit];
		_old_num_binary_clauses[lit_map] = _old_num_binary_clauses[lit];
		_long_watched_lists[lit_map] = _long_watched_lists[lit];
		_heur_decaying_sum[lit_map] = _heur_decaying_sum[lit];
		normalized_weights[lit_map] = normalized_weights[lit];
	}
	for ( Variable i = Variable( _max_var - num_removed + 1 ); i <= _max_var; i++ ) {
		Literal lit = Literal( i, false );
		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
		lit = Literal( i, true );
		_binary_clauses[lit].clear();
		_old_num_binary_clauses[lit] = 0;
		_long_watched_lists[lit].clear();
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		Literal lit = _long_clauses[i][0];
		_long_clauses[i][0] = Literal( _var_map[lit.Var()], lit.Sign() );
		lit = _long_clauses[i][1];
		_long_clauses[i][1] = Literal( _var_map[lit.Var()], lit.Sign() );
		lit = _long_clauses[i][2];
		_long_clauses[i][2] = Literal( _var_map[lit.Var()], lit.Sign() );
		for ( unsigned j = 3; j < _long_clauses[i].Size(); j++ ) {
			lit = _long_clauses[i][j];
			_long_clauses[i][j] = Literal( _var_map[lit.Var()], lit.Sign() );
		}
	}
	_max_var = Variable( _max_var - num_removed );
	_fixed_num_vars = 0;
	_model_pool->Shrink_Max_Var( _max_var, _var_map );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_heur_sorted_lits[i + i - Literal::start] = Literal( i, false );
		_heur_sorted_lits[i + i + 1 - Literal::start] = Literal( i, true );
	}
	_heur_lit_sentinel = Literal( _max_var.Next(), false );
	_heur_sorted_lits[2 * _max_var + 2 - Literal::start] = _heur_lit_sentinel;  // NOTE: this line guarantee the correctness of "Branch"
	_heur_sorted_lits[2 * _max_var + 3 - Literal::start] = ~_heur_lit_sentinel;
	_heur_decaying_sum[_heur_lit_sentinel] = -1;  /// NOTE: to speed up Branch and Branch_Component by using only one comparison in for-loop
	_heur_decaying_sum[~_heur_lit_sentinel] = -2;  /// NOTE: return 2 * _max_var + 2 exactly when all variables are assigned
	switch( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Quick_Sort_Weight_Reverse( _heur_sorted_lits, 2 * NumVars( _max_var ), _heur_decaying_sum );
		break;
	case Heuristic_Literal_Heap:
		_heur_lits_heap.Build( _heur_sorted_lits, 2 * NumVars( _max_var ) );
		break;
	}
}


}
