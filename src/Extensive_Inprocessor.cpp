#include "Extensive_Inprocessor.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


Extensive_Inprocessor::Extensive_Inprocessor():
_current_kdepth( 0 ),
_current_non_trivial_kdepth( 0 )
{
}

void Extensive_Inprocessor::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( Is_Oracle_Mode() ) {
		assert( max_var <= running_options.variable_bound );
		_max_var = max_var;
		return;
	}
	if ( _max_var == max_var ) {  /// to make the recursive calls from inherited classes correct
		if ( running_options.profiling_inprocessing != Profiling_Close ) statistics.Init_Extensive_Inprocessor();
		return;
	}
	if ( running_options.profiling_inprocessing != Profiling_Close ) statistics.Init_Extensive_Inprocessor_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_call_stack = new Stack_Frame [max_var + 1];
	_many_lits = new Literal [2 * max_var + 2];
	_cached_binary_clauses = new vector<Literal> [2 * _max_var + 2];
}

Extensive_Inprocessor::~Extensive_Inprocessor()
{
	if ( _max_var != Variable::undef || Is_Oracle_Mode() ) Free_Auxiliary_Memory();
}

void Extensive_Inprocessor::Free_Auxiliary_Memory()
{
	delete [] _call_stack;
	delete [] _many_lits;
	delete [] _cached_binary_clauses;
}

void Extensive_Inprocessor::Reset()
{
	Inprocessor::Reset();
}

void Extensive_Inprocessor::Open_Oracle_Mode( Variable var_bound )
{
	Allocate_and_Init_Auxiliary_Memory( var_bound );
	running_options.variable_bound = var_bound;
	running_options.display_preprocessing_process = false;
}

void Extensive_Inprocessor::Close_Oracle_Mode()
{
	running_options.variable_bound = Variable::undef;
}

size_t Extensive_Inprocessor::Memory()
{
	size_t mem = Inprocessor::Memory() + _swap_frame.Memory();
	for ( unsigned i = 0; i < _input_frames.size(); i++ ) {
		mem += _input_frames[i].Memory();
	}
	for ( unsigned i = 0; i <= _max_var; i++ ) {
		mem += _call_stack[i].Memory();
		mem += _cached_binary_clauses[i + i].capacity() * sizeof(Literal);
		mem += _cached_binary_clauses[i + i + 1].capacity() * sizeof(Literal);
	}
	return mem;
}

void Extensive_Inprocessor::Get_All_Imp_Component( Component & comp, vector<Model *> & models )
{
	StopWatch begin_watch;
	Literal lit;
	assert( !models.empty() );
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	if ( Learnts_Exploded() ) Filter_Long_Learnts();
	BCP( _num_dec_stack - 1 );
	Mark_Models_Component( comp, models );
	Init_Heur_Decaying_Sum_Component( comp );  // ToDo: rename
	vector<unsigned>::const_iterator old_start = comp.VarIDs_Begin(), start, stop = comp.VarIDs_End();
//	Debug_Print_Visit_Number( cerr, __LINE__, 10000 );  // ToRemove
	if ( DEBUG_OFF ) cerr << "#levels = " << _num_levels << ", #vars = " << comp.Vars_Size();  // ToModify
	for ( start = old_start; ( lit = Pick_Imp_Component_Heuristic( comp, start ) ) <= 2 * _max_var + 1; ) {
		Reason reason = Imply_Lit_Out_Reason_Component( comp, lit, models );
		if ( reason != Reason::undef ) {
			if ( Lit_Undecided( lit ) ) {  /// it is possible that \lit was assigned in \Imply_Lit_Out_Reason_Component
				Assign( lit, reason );
				BCP( _num_dec_stack - 1 );
			}
		}
	}
	if ( DEBUG_OFF ) {  // ToModify
		cerr << ", time = " << begin_watch.Get_Elapsed_Seconds() << endl;  // ToRemove
	}
	if ( DEBUG_OFF ) Verify_Current_Imps();  // ToModify
	for ( start = old_start; start < stop; start++ ) {
		_model_seen[*start + *start] = false;
		_model_seen[*start + *start + 1] = false;
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_solve += begin_watch.Get_Elapsed_Seconds();
}

void Extensive_Inprocessor::Filter_Long_Learnts()
{
	unsigned i, j;
	for ( i = _clause_status.size(); i < _long_clauses.size(); i++ ) {
		_clause_status.push_back( false );
	}
	_clause_stack.resize( _long_clauses.size() );
	unsigned last_level = Search_Last_Kernelizition_Level();
	for ( i = _dec_offsets[last_level + 1]; i < _num_dec_stack; i++ ) {
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
		else {
			if ( !SHIELD_OPTIMIZATION ) itr->Free();  // ToModify
			else {
				if ( Lit_SAT( (*itr)[0] ) || Lit_SAT( (*itr)[1] ) ) itr->Free();
				else {
					for ( j = 2; j < itr->Size() && Lit_UNSAT( (*itr)[j] ); j++ ) {}
					if ( j < itr->Size() ) itr->Free();
					else _long_clauses[i++] = *itr;
				}
			}
		}
	}
	_long_clauses.resize( i );
	begin = _long_clauses.begin(), end = _long_clauses.end();
	for ( i = _dec_offsets[last_level + 1]; i < _num_dec_stack; i++ ) {
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
	if ( running_options.sat_heur_lits == Heuristic_Literal_Heap ) running_options.sat_heur_cumulative_inc = 1;
}

void Extensive_Inprocessor::Get_All_Projected_Imp_Component( Component & comp, vector<Model *> & models )
{
	StopWatch begin_watch;
	Literal lit;
	assert( !models.empty() );
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	if ( Learnts_Exploded() ) Filter_Long_Learnts();
	Get_Approx_Imp_Component_Partial_IBCP( comp );
	Mark_Models_Component( comp, models );
	Init_Heur_Decaying_Sum_Component( comp );  // ToDo: rename
	vector<unsigned>::const_iterator old_start = comp.VarIDs_Begin(), start, stop = comp.VarIDs_End();
//	Debug_Print_Visit_Number( cerr, __LINE__, 10000 );  // ToRemove
	if ( DEBUG_OFF ) cerr << "#levels = " << _num_levels << ", #vars = " << comp.Vars_Size();  // ToModify
	for ( start = old_start; ( lit = Pick_Projected_Imp_Component_Heuristic( comp, start ) ) <= 2 * _max_var + 1; ) {
		Reason reason = Imply_Projected_Lit_Out_Reason_Component( comp, lit, models );
		if ( reason != Reason::undef ) {
			if ( Lit_Undecided( lit ) ) {  /// it is possible that \lit was assigned in \Imply_Lit_Out_Reason_Component
				Assign( lit, reason );
				BCP( _num_dec_stack - 1 );
			}
		}
	}
	if ( DEBUG_OFF ) {  // ToModify
		cerr << ", time = " << begin_watch.Get_Elapsed_Seconds() << endl;  // ToRemove
	}
	if ( DEBUG_OFF ) Verify_Current_Imps();  // ToModify
	for ( start = old_start; start < stop; start++ ) {
		_model_seen[*start + *start] = false;
		_model_seen[*start + *start + 1] = false;
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_solve += begin_watch.Get_Elapsed_Seconds();
}

bool Extensive_Inprocessor::Estimate_Kernelization_Effect_Enough_Decisions( unsigned step, unsigned ratio )
{
	unsigned last_level = Search_Last_Kernelizition_Level();
	unsigned num_decisions = _num_dec_stack - _dec_offsets[last_level + 1];
	unsigned num_levels = _num_levels - last_level - 1;
	if ( running_options.display_kernelizing_process && running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
		cout << running_options.display_prefix << "level " << last_level + 1 << " -> " << _num_levels - 1 << " (#decisions: " << num_decisions << ")" << endl;
	}
	return num_decisions > step && num_levels < num_decisions / ratio;
}

void Extensive_Inprocessor::Kernelize_Without_Imp()
{
	if ( DEBUG_OFF ) {
		static unsigned num_visited = 0;  // ToRemove
		if ( ++num_visited == 13 ) {
			CNF_Formula * cnf = Output_Original_Clauses_In_Component( Current_Component() );
			cnf->Sort_Clauses();
			ofstream ferr( "debug/debug3.cnf" );
			ferr << *cnf;
			ferr.close();
		}
	}
/*	static unsigned num_visited = 0;  // ToRemove
	if ( ++num_visited == 1 ) {
		Display_Clauses( cerr, true );
	}*/
//	Display_Decision_Stack( cerr, 1 );
//	Debug_Print_Visit_Number( cerr, __FUNCTION__, __LINE__ );  // ToRemove
	if ( running_options.display_kernelizing_process && running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
		cout << running_options.display_prefix << "kernelizing: " << Current_Component().Vars_Size() << " vars, " << Current_Component().ClauseIDs_Size() << " long clauses" << endl;
	}
	StopWatch begin_watch, tmp_watch;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) begin_watch.Start();
	unsigned last_level = Search_Last_Kernelizition_Level(), level = _num_levels - 1;
	Component & last_comp = _comp_stack[_active_comps[last_level]];
	Component & comp = _comp_stack[_active_comps[level]];
//	Display_Component( comp, cerr );  // ToRemove
	// first: compute the sub-formula under the current assignment
	Store_Active_Clauses_Component( _swap_frame, comp );
//	_swap_frame.Display( cerr );  // ToRemove
	// second: store the current clauses
	Store_Binary_Clauses_Component( _call_stack[level], comp );
	_call_stack[level].Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	Clear_Auxiliary_Lists_Subdivision_Long_Component( last_comp );  // need to clear some lists, and _binary_var_membership_lists will be handle separately for efficiency
//	if ( _num_levels == 3 ) _call_stack[level].Display( cerr );  // ToRemove
	// third: shift to the sub-formula
	Load_Binary_Clauses( _swap_frame );
	_swap_frame.Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	// fourth: kernelize
	Generate_Long_Watched_Lists_No_Clear();
	_fixed_num_vars = _unary_clauses.size();
	do {
		Eliminate_Redundancy_Component( comp );
	} while ( Replace_Equivalent_Lit_Component( comp ) );
	Block_Binary_Clauses_Component( comp );
	if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) Rename_Clauses_Linear_Ordering_Component( comp );
	if ( debug_options.verify_kernelization ) Verify_Kernelization();
	// fifth: store literal equivalences
	Store_Lit_Equivalences_Component( _call_stack[level], comp );
	// sixth: update component
	_call_stack[level].Swap_Component( comp );
	Update_Kernelized_Component( comp, _call_stack[level].Component_VarIDs() );
	_fixed_num_long_clauses = _old_num_long_clauses;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) statistics.time_kernelize += begin_watch.Get_Elapsed_Seconds();
	if ( running_options.display_kernelizing_process && running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
		cout << running_options.display_prefix << "kernelization effect: " << Current_Component().Vars_Size() << " vars, " << Current_Component().ClauseIDs_Size() << " long clauses" << endl;
	}
//	Display_Component( comp, cerr );  // ToRemove
}

void Extensive_Inprocessor::Store_Active_Clauses_Component( Stack_Frame & frame, Component & comp )
{
	unsigned i, j, k;
	Literal lit, lit2;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		lit = Literal( comp.Vars( i ), false );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			frame.Add_Binary_Clause( lit, lit2 );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			frame.Add_Binary_Learnt( lit, lit2 );
		}
		for ( j = 0; j < _long_watched_lists[lit].size(); j++ ) {
			unsigned watched_id = _long_watched_lists[lit][j];
			if ( watched_id < _old_num_long_clauses ) continue;
			Clause & clause = _long_clauses[watched_id];
			assert( clause.Size() >= 3 );
			if ( clause[1] == lit ) continue;  // stop being repeatedly used
			if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) continue;
			for ( k = 2; k < clause.Size() && Lit_UNSAT( clause[k] ); k++ ) {}
			if ( k == clause.Size() ) {
				frame.Add_Binary_Learnt( clause[0], clause[1] );
				frame.Add_Binary_Learnt( clause[1], clause[0] );
			}
		}
		lit = Literal( comp.Vars( i ), true );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			frame.Add_Binary_Clause( lit, lit2 );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			frame.Add_Binary_Learnt( lit, lit2 );
		}
		for ( j = 0; j < _long_watched_lists[lit].size(); j++ ) {
			unsigned watched_id = _long_watched_lists[lit][j];
			if ( watched_id < _old_num_long_clauses ) continue;
			Clause & clause = _long_clauses[watched_id];
			assert( clause.Size() >= 3 );
			if ( clause[1] == lit ) continue;  // stop being repeatedly used
			if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) continue;
			for ( k = 2; k < clause.Size() && Lit_UNSAT( clause[k] ); k++ ) {}
			if ( k == clause.Size() ) {
				frame.Add_Binary_Learnt( clause[0], clause[1] );
				frame.Add_Binary_Learnt( clause[1], clause[0] );
			}
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( j = 0; j < clause.Size(); j++ ) {
			lit = clause[j];
			if ( Lit_Decided( lit ) ) continue;
			_big_clause.Add_Lit( lit );
		}
		assert( _big_clause.Size() >= 2 );
		if ( _big_clause.Size() == 2 ) {
			frame.Add_Binary_Clause( _big_clause[0], _big_clause[1] );
			frame.Add_Binary_Clause( _big_clause[1], _big_clause[0] );
		}
		else frame.Add_Long_Clause( _big_clause );
	}
	frame.Set_Old_Num_Long_Clauses( frame.Long_Clauses().size() );
}

void Extensive_Inprocessor::Store_Binary_Clauses_Component( Stack_Frame & frame, Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		unsigned j;
		Literal lit( var, false );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			frame.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			frame.Add_Binary_Learnt( lit, _binary_clauses[lit][j] );
		}
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
		lit = Literal( var, true );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			frame.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			frame.Add_Binary_Learnt( lit, _binary_clauses[lit][j] );
		}
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
	}
}

void Extensive_Inprocessor::Load_Binary_Clauses( Stack_Frame & frame )
{
	for ( unsigned i = 0; i < frame.Binary_Clauses_Size(); i++ ) {
		const Literal & lit = frame.Binary_Clauses_First( i );
		const Literal & lit2 = frame.Binary_Clauses_Second( i );
		_binary_clauses[lit].push_back( lit2 );
		_old_num_binary_clauses[lit]++;
	}
	frame.Clear_Binary_Clauses();
	for ( unsigned i = 0; i < frame.Binary_Learnts_Size(); i++ ) {
		const Literal & lit = frame.Binary_Learnts_First( i );
		const Literal & lit2 = frame.Binary_Learnts_Second( i );
		_binary_clauses[lit].push_back( lit2 );
	}
	frame.Clear_Binary_Learnts();
}

void Extensive_Inprocessor::Load_Lit_Equivalences( Stack_Frame & frame )
{
	for ( unsigned i = 0; i < frame.Lit_Equivalences().size(); i += 2 ) {
		const Literal & lit = frame.Lit_Equivalences()[i];
		const Literal & lit2 = frame.Lit_Equivalences()[i+1];
		_lit_equivalences[lit2] = lit;
		_lit_equivalences[~lit2] = ~lit;
	}
	_fixed_num_vars += frame.Lit_Equivalences_Size();
}

void Extensive_Inprocessor::Eliminate_Redundancy_Component( Component & comp )
{
	if ( !running_options.block_clauses && !running_options.block_lits ) return;
	StopWatch tmp_watch;
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Store_Binary_Learnts( var + var );
		Store_Binary_Learnts( var + var + 1);
	}
	Store_Long_Learnts();  // NOTE: not consider learnts, otherwise impacts the equivalence
	Generate_Long_Watched_Lists_Component( comp );
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) tmp_watch.Start();
	Block_Lits_Improved();
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) statistics.time_kernelize_block_lits += tmp_watch.Get_Elapsed_Seconds();
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) tmp_watch.Start();
	Vivification();
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) statistics.time_kernelize_vivification += tmp_watch.Get_Elapsed_Seconds();
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Recover_Binary_Learnts( var + var );
		Recover_Binary_Learnts( var + var + 1 );
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

void Extensive_Inprocessor::Generate_Long_Watched_Lists_Component( Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_long_watched_lists[var + var].clear();
		_long_watched_lists[var + var + 1].clear();
	}
	vector<Clause>::iterator begin = _long_clauses.begin(), itr = begin, end = _long_clauses.end();
	for ( ; itr < end; itr++ ) {
		_long_watched_lists[(*itr)[0]].push_back( itr - begin );
		_long_watched_lists[(*itr)[1]].push_back( itr - begin );
	}
}

bool Extensive_Inprocessor::Replace_Equivalent_Lit_Component( Component & comp )
{
	StopWatch begin_watch;
	if ( !running_options.detect_lit_equivalence ) return false;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) begin_watch.Start();
	if ( !Detect_Lit_Equivalence_Component( comp ) ) {
		if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) statistics.time_kernelize_lit_equ += begin_watch.Get_Elapsed_Seconds();
		return false;
	}
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_long_watched_lists[var + var].clear();
		_long_watched_lists[var + var + 1].clear();
		Store_Binary_Learnts( var + var );
		Store_Binary_Learnts( var + var + 1 );
	}
	Replace_Equivalent_Lit_Binary_Clauses();
	Store_Long_Learnts();
	Replace_Equivalent_Lit_Long_Clauses();
	_old_num_long_clauses = _long_clauses.size();
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_old_num_binary_clauses[var + var] = _binary_clauses[var + var].size();
		_old_num_binary_clauses[var + var + 1] = _binary_clauses[var + var + 1].size();
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
	if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) statistics.time_kernelize_lit_equ += begin_watch.Get_Elapsed_Seconds();
	return true;
}

bool Extensive_Inprocessor::Detect_Lit_Equivalence_Component( Component & comp )
{
	switch ( running_options.lit_equivalence_detecting_strategy ) {  // ToModify
	case Literal_Equivalence_Detection_Tarjan:
		return Detect_Lit_Equivalence_Tarjan_Component( comp );
	case Literal_Equivalence_Detection_BCP:
		return Detect_Lit_Equivalence_BCP_Component( comp );
		break;
	case Literal_Equivalence_Detection_IBCP:
		return Detect_Lit_Equivalence_IBCP_Component( comp );
		break;
	default:
		return false;
	}
}

bool Extensive_Inprocessor::Detect_Lit_Equivalence_Tarjan_Component( Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		if ( _lit_search_state[var + var] != UNSIGNED_UNDEF || _lit_search_state[var + var + 1] != UNSIGNED_UNDEF ) continue;
		if ( _lit_equivalences[var + var] != var + var ) continue;
		Strongly_Connected_Component( Literal( var, false ) );
	}
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_lit_search_state[var + var] = UNSIGNED_UNDEF;
		_lit_search_state[var + var + 1] = UNSIGNED_UNDEF;
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits_Component( comp );  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

void Extensive_Inprocessor::Cluster_Equivalent_Lits_Component( Component & comp )
{
	_fixed_num_vars = _unary_clauses.size();
	_equivalent_lit_cluster_size = 0;
	vector<Literal> singleton( 1 );
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {  /// after the first calling of Detect_Lit_Equivalence, the first if-statement in this loop needs ti be used
		Variable var = comp.Vars( i );
		Literal lit = _lit_equivalences[var + var];
		if ( _lit_equivalences[lit] != lit ) {  /// handle the case where the path to the root is greater than one
			Literal root = _lit_equivalences[lit];
			assert( _lit_equivalences[root] == root );  /// handled from one to _max_var, so the length of sub-path is not greater than one
			_lit_equivalences[var + var] = root;
			_lit_equivalences[var + var + 1] = ~root;
		}
		if ( _lit_equivalences[var + var] != var + var ) {  // NOTE: lit may be changed, so we need to use _lit_equivalences[i + i]
			unsigned j;
			for ( j = 0; _lit_equivalences[var + var] != _equivalent_lit_sets[j][0]; j++ ) {}  // find the old entry
			_equivalent_lit_sets[j].push_back( Literal( var, false ) );
			_equivalent_lit_sets[j ^ 0x01].push_back( Literal( var, true ) );
			_fixed_num_vars++;
		}
		else {  // create new entries
			singleton[0] = Literal( var, false );
			_equivalent_lit_sets[_equivalent_lit_cluster_size++] = singleton;
			singleton[0] = Literal( var, true );
			_equivalent_lit_sets[_equivalent_lit_cluster_size++] = singleton;
		}
	}
}

bool Extensive_Inprocessor::Detect_Lit_Equivalence_BCP_Component( Component & comp )
{
	unsigned old_num_d_stack = _num_dec_stack;
	vector<Literal> neg_implied_literals, pos_implied_literals;
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		if ( Var_Decided( var ) ) continue;
		Assign( Literal( var, false ) );
		BCP( old_num_d_stack );
		neg_implied_literals.resize( _num_dec_stack - old_num_d_stack - 1 );
		for ( unsigned j = old_num_d_stack + 1; j < _num_dec_stack; j++ ) {
			neg_implied_literals[j - old_num_d_stack - 1] = _dec_stack[j];
		}
		Un_BCP( old_num_d_stack );
		Assign( Literal( var, true ) );
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
			Record_Equivalent_Lit_Pair( Literal( var, true ), lit );
		}
		_lit_seen[neg_implied_literals[0]] = false;
		for ( unsigned j = 1; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = false;
		}
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits_Component( comp );  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

bool Extensive_Inprocessor::Detect_Lit_Equivalence_IBCP_Component( Component & comp )
{
	unsigned old_num_d_stack = _num_dec_stack, tmp_num_d_stack;
	vector<Literal> neg_implied_literals, pos_implied_literals;
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		if ( Var_Decided( var ) ) continue;
		Implied_Literals_Approx( Literal( var, false ), neg_implied_literals );
		Implied_Literals_Approx( Literal( var, true ), pos_implied_literals );
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = true;
		}
		Assign( var, false, Reason::undef );
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
			if ( imp ) Record_Equivalent_Lit_Pair( Literal( var, true ), lit );
		}
		Un_BCP( old_num_d_stack );
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			_lit_seen[neg_implied_literals[j]] = false;
		}
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			_lit_seen[pos_implied_literals[j]] = true;
		}
		Assign( var, true, Reason::undef );
		BCP( old_num_d_stack );
		tmp_num_d_stack = _num_dec_stack;
		for ( unsigned j = 0; j < neg_implied_literals.size(); j++ ) {
			Literal lit = neg_implied_literals[j];  // phi and (i+i) |= lit
			if ( !_lit_seen[~lit] ) {  // the case of _lit_seen[~lit] is already detected
				Assign( lit );
				if ( BCP( tmp_num_d_stack ) != Reason::undef ) Record_Equivalent_Lit_Pair( Literal( var, false ), lit );  // phi and (i+i+1) |= not lit, if phi and (i+i+1) and lit is unsatisfiable
				Un_BCP( tmp_num_d_stack );
			}
		}
		Un_BCP( old_num_d_stack );
		for ( unsigned j = 0; j < pos_implied_literals.size(); j++ ) {
			_lit_seen[pos_implied_literals[j]] = false;
		}
	}
	unsigned old_fixed_num_vars = _fixed_num_vars;
	Cluster_Equivalent_Lits_Component( comp );  // _fixed_num_vars will change in the function
	return old_fixed_num_vars < _fixed_num_vars;
}

void Extensive_Inprocessor::Block_Binary_Clauses_Component( Component & comp )  // NOTE: all unary clauses has been computed
{
	if ( !running_options.block_clauses || running_options.keep_binary_learnts ) return;
	StopWatch begin_watch;
	if ( running_options.profile_preprocessing >= Profiling_Detail ) begin_watch.Start();
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		Store_Binary_Learnts( var + var );
		Store_Binary_Learnts( var + var + 1);
	}
	Store_Long_Learnts();  // NOTE: not consider learnts, otherwise impacts the equivalence
	Generate_Long_Watched_Lists_Component( comp );
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		Literal lit( var, false );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); ) {  // NOTE: _binary_clauses[lit] would change
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) {
				j++;
				continue;
			}
			Remove_Old_Binary_Clause_No_Learnt( lit, j );
			if ( !Imply_Binary_Clause_BCP( lit, lit2 ) ) Add_Old_Binary_Clause_Fixed_No_Learnt( lit, lit2, j++ );
		}
		lit = Literal( var, true );
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
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Recover_Binary_Learnts( var + var );
		Recover_Binary_Learnts( var + var + 1 );
	}
	for ( unsigned i = 0; i < _long_learnts.size(); i++ ) {
		_long_clauses.push_back( _long_learnts[i] );
		_long_watched_lists[_long_learnts[i][0]].push_back( i + _old_num_long_clauses );
		_long_watched_lists[_long_learnts[i][1]].push_back( i + _old_num_long_clauses );
	}
	if ( running_options.profile_preprocessing >= Profiling_Detail ) statistics.time_kernelize_vivification += begin_watch.Get_Elapsed_Seconds();
}

void Extensive_Inprocessor::Rename_Clauses_Linear_Ordering_Component( Component & comp )
{
	Record_Lit_Equivalency_Component( comp );
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		Literal lit( var, false );
		if ( !_binary_clauses[lit].empty() ) {
			Literal ren_lit = _lit_equivalency.Rename_Lit( lit );
			if ( ren_lit != lit ) {
				assert( _binary_clauses[ren_lit].empty() );
				_binary_clauses[ren_lit] = _binary_clauses[lit];
				_old_num_binary_clauses[ren_lit] = _old_num_binary_clauses[lit];
				_binary_clauses[lit].clear();
				_old_num_binary_clauses[lit] = 0;
			}
			for ( unsigned j = 0; j <  _binary_clauses[ren_lit].size(); j++ ) {
				_binary_clauses[ren_lit][j] = _lit_equivalency.Rename_Lit( _binary_clauses[ren_lit][j] );
			}
		}
		_lit_equivalences[lit] = _lit_equivalency.Rename_Lit( lit );
		lit = Literal( var, true );
		if ( !_binary_clauses[lit].empty() ) {
			Literal ren_lit = _lit_equivalency.Rename_Lit( lit );
			if ( ren_lit != lit ) {
				assert( _binary_clauses[ren_lit].empty() );
				_binary_clauses[ren_lit] = _binary_clauses[lit];
				_old_num_binary_clauses[ren_lit] = _old_num_binary_clauses[lit];
				_binary_clauses[lit].clear();
				_old_num_binary_clauses[lit] = 0;
			}
			for ( unsigned j = 0; j <  _binary_clauses[ren_lit].size(); j++ ) {
				_binary_clauses[ren_lit][j] = _lit_equivalency.Rename_Lit( _binary_clauses[ren_lit][j] );
			}
		}
		_lit_equivalences[lit] = _lit_equivalency.Rename_Lit( lit );
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		Clause & clause = _long_clauses[i];
		clause[0] = _lit_equivalency.Rename_Lit( clause[0] );
		clause[1] = _lit_equivalency.Rename_Lit( clause[1] );
		_long_watched_lists[clause[0]].push_back( i );
		_long_watched_lists[clause[1]].push_back( i );
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			clause[j] = _lit_equivalency.Rename_Lit( clause[j] );
		}
	}
//	Display_Clauses( cerr, true );  // ToRemove
	_lit_equivalency.Reset();
}

void Extensive_Inprocessor::Record_Lit_Equivalency_Component( Component & comp )
{
	if ( _unary_clauses.size() == _fixed_num_vars ) return;
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Literal lit( var, false );
		if ( lit != _lit_equivalences[lit] ) _lit_equivalency.Add_Equivalence( lit, _lit_equivalences[lit] );
		lit = ~lit;
		if ( lit != _lit_equivalences[lit] ) _lit_equivalency.Add_Equivalence( lit, _lit_equivalences[lit] );
	}
}

void Extensive_Inprocessor::Update_Kernelized_Component( Component & comp, const vector<unsigned> & vars )
{
	/** NOTE:
	** We cannot change the variables in comp because we need use them to recover the previous comp when leave kernelization
	**/
	for ( vector<unsigned>::const_iterator itr = vars.cbegin(); itr < vars.cend(); itr++ ) {
		Variable var( *itr );
		_binary_var_membership_lists[var].clear();
		_ternary_var_membership_lists[var].clear();
		_quaternary_var_membership_lists[var].clear();
		_long_var_membership_lists[var].clear();
		Literal lit( var, false );
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
		lit = Literal( var, true );
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
		_var_seen[var] = ( _old_num_binary_clauses[var + var] + _old_num_binary_clauses[var + var + 1] > 0 );
	}
	comp.Clear_ClauseIDs();
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		comp.Add_ClauseID( i );
		Clause & clause = _long_clauses[i];
		_var_seen[clause[0].Var()] = true;
		_var_seen[clause[1].Var()] = true;
		_var_seen[clause[2].Var()] = true;
		for ( unsigned j = 3; j < clause.Size(); j++ ) {
			_var_seen[clause[j].Var()] = true;
		}
	}
	for ( vector<unsigned>::const_iterator itr = vars.cbegin(); itr < vars.cend(); itr++ ) {
		Variable var( *itr );
		if ( _var_seen[var] ) {
			comp.Add_Var( var );
			_var_seen[var] = false;
		}
	}
	comp.Add_Var( _max_var.Next() );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
	comp.Dec_Var();  /// pop _max_var.Next()
}

void Extensive_Inprocessor::Store_Lit_Equivalences_Component( Stack_Frame & frame, Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Literal lit( var, false );
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			frame.Add_Lit_Equivalence( _lit_equivalences[lit], lit );
			_lit_equivalences[lit] = lit;
			_lit_equivalences[~lit] = ~lit;
			_fixed_num_vars--;
		}
	}
}

void Extensive_Inprocessor::Gather_Kernelization_Infor( unsigned level )
{
	if ( statistics.max_kdepth < _current_kdepth ) statistics.max_kdepth = _current_kdepth;
	bool non_trivial = ( _call_stack[level].Lit_Equivalences_Size() > 0 );
	_current_non_trivial_kdepth += non_trivial;
	assert( _current_non_trivial_kdepth <= _current_kdepth );
	if ( statistics.max_non_trivial_kdepth < _current_non_trivial_kdepth ) statistics.max_non_trivial_kdepth = _current_non_trivial_kdepth;
	statistics.num_kernelizations++;
	statistics.num_non_trivial_kernelizations += non_trivial;
}

void Extensive_Inprocessor::Generate_Auxiliary_Lists_Subdivision_Component( Component & comp )
{
	Generate_Long_Watched_Lists_No_Clear();
	Generate_Membership_Lists_Subdivision_Binary_Component( comp );
	Generate_Membership_Lists_Subdivision_Long();
}

void Extensive_Inprocessor::Generate_Membership_Lists_Subdivision_Binary_Component( Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		unsigned lit = var + var;
		vector<Literal>::iterator it = _binary_clauses[lit].begin();
		vector<Literal>::iterator en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			_binary_var_membership_lists[var].push_back( it->Var() );
		}
		lit = var + var + 1;
		it = _binary_clauses[lit].begin();
		en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			_binary_var_membership_lists[var].push_back( it->Var() );
			unsigned j;
			for ( j = 0; _binary_var_membership_lists[var][j] != it->Var(); j++ );
			if ( j < _binary_var_membership_lists[var].size() - 1 ) _binary_var_membership_lists[var].pop_back();  // appeared
		}
	}
}

void Extensive_Inprocessor::Clear_Auxiliary_Lists_Subdivision_Long_Component( Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_ternary_var_membership_lists[var].clear();
		_quaternary_var_membership_lists[var].clear();
		_long_var_membership_lists[var].clear();
		Literal lit( var, false );
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
		lit = Literal( var, true );
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
	}
}

void Extensive_Inprocessor::Clear_Membership_Lists_Subdivision_Long()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_ternary_var_membership_lists[i].clear();
		_quaternary_var_membership_lists[i].clear();
		_long_var_membership_lists[i].clear();
		Literal lit( i, false );
		_long_lit_membership_lists[lit].clear();
		lit = Literal( i, true );
		_long_lit_membership_lists[lit].clear();
	}
}

void Extensive_Inprocessor::Clear_Membership_Lists_Subdivision_Component( Component & comp )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_binary_var_membership_lists[var].clear();
		_ternary_var_membership_lists[var].clear();
		_quaternary_var_membership_lists[var].clear();
		_long_var_membership_lists[var].clear();
		Literal lit( var, false );
		_long_lit_membership_lists[lit].clear();
		lit = Literal( var, true );
		_long_lit_membership_lists[lit].clear();
	}
}

void Extensive_Inprocessor::Clear_Membership_Lists_Subdivision_Binary_Component( Component & comp )
{
	for ( unsigned ii = 0; ii < comp.Vars_Size(); ii++ ) {
		Variable var = comp.Vars( ii );
		_binary_var_membership_lists[var].clear();
	}
}

void Extensive_Inprocessor::Cancel_Kernelization_Without_Imp()
{
	StopWatch begin_watch;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) begin_watch.Start();
	_call_stack[_num_levels - 1].Clear_Lit_Equivalences();
	for ( unsigned i = 0; i < Current_Component().Vars_Size(); i++ ) {
		Variable var = Current_Component().Vars( i );
		_binary_var_membership_lists[var].clear();
		Literal lit( var, false );
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
		lit = Literal( var, true );
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
	}
	Clear_Auxiliary_Lists_Subdivision_Long_Component( Current_Component() );
//	if ( _num_levels == 3 ) _call_stack[_num_levels - 1].Display( cerr );  // ToRemove
//	cerr << "Load from: " << endl;  // ToRemove
//	_call_stack[_num_levels - 1].Display( cerr );  // ToRemove
	Load_Binary_Clauses( _call_stack[_num_levels - 1] );
	_old_num_long_clauses = 0;
	vector<Clause>::iterator itr = _long_clauses.begin();
	vector<Clause>::iterator end = _long_clauses.end();
	for ( ; itr < end; itr++ ) itr->Free();
	_long_clauses.clear();
	_call_stack[_num_levels - 1].Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	_fixed_num_long_clauses = _old_num_long_clauses;
	Current_Component().Clear();
	_call_stack[_num_levels - 1].Swap_Component( Current_Component() );
	Generate_Auxiliary_Lists_Subdivision_Component( Current_Component() );
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) statistics.time_kernelize += begin_watch.Get_Elapsed_Seconds();
}

void Extensive_Inprocessor::Set_Current_Level_Kernelized( bool flag )
{
	_call_stack[_num_levels - 1].Set_Existed( flag );
	if ( flag ) {
		_current_kdepth++;
		if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
			Gather_Kernelization_Infor( _num_levels - 1 );
		}
	}
	else {
		_current_kdepth--;
		if ( running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
			bool non_trivial = ( _call_stack[_num_levels - 1].Lit_Equivalences_Size() > 0 );
			_current_non_trivial_kdepth -= non_trivial;
			assert( _current_non_trivial_kdepth <= _current_kdepth );
		}
	}
	if ( false ) cerr << "current kdepth: " << _current_kdepth << endl;  // ToRemove
}

unsigned Extensive_Inprocessor::Search_Last_Decomposition_Level()
{
	if ( _num_comp_stack > _comp_offsets[_num_levels - 1] + 1 ) return _num_levels - 1;
	unsigned i = _num_levels - 2;
	for ( ; i > 0 && _comp_offsets[i+1] - _comp_offsets[i] <= 1; i-- ) {}
	return i;
}

unsigned Extensive_Inprocessor::Search_Last_Kernelizition_Level()
{
	assert( _call_stack[0].Existed() );
	unsigned i = _num_levels - 1;
	for ( ; !_call_stack[i].Existed(); i-- ) {}
	return i;
}

void Extensive_Inprocessor::Store_Cached_Binary_Clauses()
{
	unsigned last_level = Search_Last_Kernelizition_Level();
	Component & last_comp = _comp_stack[_active_comps[last_level]];
	Stack_Frame & last_frame = _call_stack[last_level];
	assert( last_frame.Cached_Binary_Clauses_Size() == 0 );
	for ( unsigned i = 0; i < last_comp.Vars_Size(); i++ ) {
		Variable var = last_comp.Vars( i );
		Literal lit( var, false );
		for ( unsigned j = 0; j < _cached_binary_clauses[lit].size(); j++ ) {
			last_frame.Add_Cached_Binary_Clause( lit, _cached_binary_clauses[lit][j] );
		}
		_cached_binary_clauses[lit].clear();
		lit = Literal( var, true );
		for ( unsigned j = 0; j < _cached_binary_clauses[lit].size(); j++ ) {
			last_frame.Add_Cached_Binary_Clause( lit, _cached_binary_clauses[lit][j] );
		}
		_cached_binary_clauses[lit].clear();
	}
}

void Extensive_Inprocessor::Clear_Cached_Binary_Clauses()
{
	for ( unsigned i = 0; i < Current_Component().Vars_Size(); i++ ) {
		Variable var = Current_Component().Vars( i );
		Literal lit( var, false );
		_cached_binary_clauses[lit].clear();
		lit = Literal( var, true );
		_cached_binary_clauses[lit].clear();
	}
}

void Extensive_Inprocessor::Recover_Cached_Binary_Clauses()
{
	unsigned last_level = Search_Last_Kernelizition_Level();
	Stack_Frame & last_frame = _call_stack[last_level];
	for ( unsigned i = 0; i < last_frame.Cached_Binary_Clauses_Size(); i++ ) {
		const Literal & lit = last_frame.Cached_Binary_Clauses_First( i );
		const Literal & lit2 = last_frame.Cached_Binary_Clauses_Second( i );
		_cached_binary_clauses[lit].push_back( lit2 );
	}
	last_frame.Clear_Cached_Binary_Clauses();
}

void Extensive_Inprocessor::Verify_Kernelization()
{
	vector<vector<int>> processed_eclauses;
	vector<vector<int>> original_eclauses;
	unsigned level = Search_Last_Kernelizition_Level();
	for ( unsigned i = _dec_offsets[level]; i < _num_dec_stack; i++ ) {
		processed_eclauses.push_back( ExtLits( _dec_stack[i] ) );
		original_eclauses.push_back( ExtLits( _dec_stack[i] ) );
	}
	Component & comp = Current_Component();
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		Literal lit( var, false );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			processed_eclauses.push_back( ExtLits( lit, lit2 ) );
		}
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			processed_eclauses.push_back( ExtLits( ~lit, _lit_equivalences[lit] ) );
			processed_eclauses.push_back( ExtLits( lit, ~_lit_equivalences[lit] ) );
		}
		lit = Literal( var, true );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			processed_eclauses.push_back( ExtLits( lit, lit2 ) );
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		processed_eclauses.push_back( ExtLits( _long_clauses[i] ) );
	}
	Stack_Frame & frame = _call_stack[_num_levels - 1];
	for ( unsigned i = 0; i < frame.Binary_Clauses_Size(); i++ ) {
		Literal lit = frame.Binary_Clauses_First( i );
		Literal lit2 = frame.Binary_Clauses_Second( i );
        if ( comp.Search_Var( lit.Var() ) && comp.Search_Var( lit2.Var() ) ) {
			original_eclauses.push_back( ExtLits( lit, lit2 ) );
        }
	}
	for ( unsigned i = 0; i < frame.Long_Clauses().size(); i++ ) {
		Clause clause = frame.Long_Clauses( i );
		bool appeared = false;
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			if ( comp.Search_Var( clause[j].Var() ) ) appeared = true;
		}
		if ( appeared ) original_eclauses.push_back( ExtLits( clause ) );
	}
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

void Extensive_Inprocessor::Add_Formula( CNF_Formula & cnf, Component & comp, vector<Model *> & models, unsigned pre_fixed_num_vars )
{
	assert( cnf.Max_Var() <= _max_var );
	Input_Models_Component( comp, models );
	Add_Input_Frame( cnf, _models_stack[0], pre_fixed_num_vars );
}

void Extensive_Inprocessor::Add_Input_Frame( CNF_Formula & cnf, vector<Model *> & models, unsigned pre_fixed_num_vars )
{
	_input_frames.push_back( Stack_Frame() );
	Stack_Frame & frame = _input_frames.back();
	for ( unsigned i = 0; i < cnf.Num_Clauses(); i++ ) {
		Clause & clause = cnf[i];
		if ( clause.Size() == 1 ) {
			frame.Add_Unary_Clause( clause[0] );
		}
		else if ( clause.Size() == 2 ) {
			frame.Add_Binary_Clause( clause[0], clause[1] );
			frame.Add_Binary_Clause( clause[1], clause[0] );
		}
		else {
			Clause clause_copy = clause.Copy();
			frame.Add_Long_Clause( clause_copy );
		}
	}
	frame.Swap_Models( models );
	frame.Set_Pre_Fixed_Num_Vars( pre_fixed_num_vars );
}

void Extensive_Inprocessor::Batch_Preprocess()
{
	assert( !_input_frames.empty() && _no_instance && _current_kdepth == 1 );
	StopWatch begin_watch;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) begin_watch.Start();
	for ( unsigned i = 0; i < _input_frames.size(); i++ ) {
		assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
		if ( running_options.display_kernelizing_process ) cout << running_options.display_prefix << "Begin kernelization..." << endl;
		assert( _input_frames[i].Lit_Equivalences().empty() );
		Load_Frame( _input_frames[i] );
		bool cnf_sat = Preprocess( _models_stack[0] );
		_input_frames[i].Set_Existed( cnf_sat );
		if ( _input_frames[i].Existed() ) Store_Frame( _input_frames[i] );
		Preprocessor::Reset();
		if ( running_options.display_kernelizing_process ) cout << running_options.display_prefix << "Kernelization done." << endl;
	}
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) statistics.time_kernelize += begin_watch.Get_Elapsed_Seconds();
}

void Extensive_Inprocessor::Load_Frame( Stack_Frame & frame )
{
	frame.Swap_Unary_Clauses( _unary_clauses );
	Load_Binary_Clauses( frame );
	frame.Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	frame.Swap_Lit_Equivalences( _call_stack[0] );
	frame.Swap_Models( _models_stack[0] );
}

void Extensive_Inprocessor::Store_Frame( Stack_Frame & frame )
{
	frame.Swap_Unary_Clauses( _unary_clauses );
	Store_Binary_Clauses( frame );
	frame.Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	Store_Lit_Equivalences( frame );
	frame.Swap_Models( _models_stack[0] );
}

void Extensive_Inprocessor::Store_Binary_Clauses( Stack_Frame & frame )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned j;
		Literal lit( i, false );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			frame.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			frame.Add_Binary_Learnt( lit, _binary_clauses[lit][j] );
		}
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
		lit = Literal( i, true );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			frame.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			frame.Add_Binary_Learnt( lit, _binary_clauses[lit][j] );
		}
		_old_num_binary_clauses[lit] = 0;
		_binary_clauses[lit].clear();
	}
}

void Extensive_Inprocessor::Store_Lit_Equivalences( Stack_Frame & frame )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		if ( _lit_equivalences[lit] != lit ) {  /// NOTE: no need to compare lit + 1
			frame.Add_Lit_Equivalence( _lit_equivalences[lit], lit );
			_lit_equivalences[lit] = lit;
			_lit_equivalences[~lit] = ~lit;
			_fixed_num_vars--;
		}
	}
}

void Extensive_Inprocessor::Generate_Unified_Component( Component & comp )
{
	unsigned i, j, num;
	_unified_comp.Clear();
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars(i);
		_unified_comp.Add_Var( var );
		Literal lit( var, false );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			_unified_comp.Add_Binary_Clause( lit, _many_lits[j] );
		}
		lit = Literal( var, true );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			_unified_comp.Add_Binary_Clause( lit, _many_lits[j] );
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_unified_comp.Add_ClauseID( _long_clause_ids[comp.ClauseIDs(i)] );
	}
	if ( DEBUG_OFF ) _unified_comp.Verify_Orderness();  // ToRemove
}

void Extensive_Inprocessor::Verify_Reasons_With_Kernelization()
{
	unsigned last_level = Search_Last_Kernelizition_Level();
	Component init_comp = _comp_stack[_active_comps[last_level]];
	for ( unsigned i = _dec_offsets[last_level + 1]; i < _num_dec_stack; i++ ) {
		assert( init_comp.Search_Var( _dec_stack[i].Var() ) );
		Reason r = _reasons[_dec_stack[i].Var()];
		if ( r == Reason::undef ) continue;
		if ( r.Is_Lit_Reason() ) {
			Literal lit = r.Lit_Value();
			assert( init_comp.Search_Var( lit.Var() ) );
		}
		else {
			unsigned cl = r.Clause_Value();
			assert( cl < _long_clauses.size() );
			Clause & clause = _long_clauses[cl];
			assert( clause[0] == _dec_stack[i] );
			for ( unsigned j = 1; j < clause.Size(); j++ ) {
				Literal lit = clause[j];
				assert( init_comp.Search_Var( lit.Var() ) );
			}
		}
	}
}




}
