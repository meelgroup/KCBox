#include "KCounter.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


KCounter::KCounter():
_num_rsl_stack( 0 )
{
}

KCounter::~KCounter()
{
	Free_Auxiliary_Memory();
}

void KCounter::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_counting != Profiling_Close ) statistics.Init_Counter();
		return;
	}
	if ( running_options.profile_counting != Profiling_Close ) statistics.Init_Counter_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Extensive_Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_rsl_stack = new BigInt [2 * _max_var + 2];
	_aux_rsl_stack = new unsigned [2 * _max_var + 2];
}

void KCounter::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
	delete [] _rsl_stack;
	delete [] _aux_rsl_stack;
}

void KCounter::Reset()
{
	Extensive_Inprocessor::Reset();
	_component_cache.Reset();
}

size_t KCounter::Memory()
{
	if ( _max_var == Variable::undef ) return 0;
	size_t mem = Extensive_Inprocessor::Memory() + _component_cache.Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _models_stack[i].capacity() * sizeof(unsigned);
		mem += _comp_stack[i].Capacity() * sizeof(unsigned);
	}
	return mem;
}

BigInt KCounter::Count_Models( CNF_Formula & cnf, Heuristic heur )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	running_options.detect_lit_equivalence = ( running_options.max_kdepth > 0 );
	bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigInt count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		return count;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	_fixed_num_vars -= _and_gates.size();
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( heur );
	else Choose_Running_Options_Static( heur );
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) running_options.Display( cout );  // ToRemove
	Set_Current_Level_Kernelized( true );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {  // ToModify
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Count_With_Implicite_BCP();
	}
	else {
		if ( running_options.max_kdepth > 1 ) {
			if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) _lit_equivalency.Reorder( _var_order );
			Encode_Long_Clauses();
		}
		Count_With_SAT_Imp_Computing();
	}
	Set_Current_Level_Kernelized( false );
	_fixed_num_vars += _and_gates.size();
	Load_Lit_Equivalences( _call_stack[0] );
	_call_stack[0].Clear_Lit_Equivalences();
	BigInt count = Backtrack_Init();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_counting_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_counting >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Memory_Status( cout );
		}
	}
	Reset();
	if ( debug_options.verify_count ) {
		BigInt verified_count = Count_Verified_Models_d4( cnf );
		cerr << count << " vs " << verified_count << endl;
		assert( count == verified_count );
	}
	return count;
}

BigInt KCounter::Backtrack_Init()
{
	if ( _num_rsl_stack == 0 ) {
		_rsl_stack[0] = 1;
		_rsl_stack[0].Mul_2exp( NumVars( _max_var ) - _fixed_num_vars );  /// _unsimplifiable_num_vars is 0
		Un_BCP( _dec_offsets[--_num_levels] );
	}
	else {
		_num_rsl_stack--;
		_rsl_stack[0].Mul_2exp( Num_Omitted_Vars() );
		Backtrack();
	}
	return _rsl_stack[0];
}

void KCounter::Choose_Running_Options( Heuristic heur )
{
	running_options.var_ordering_heur = heur;
	switch ( running_options.var_ordering_heur ) {
	case AutomaticalHeur:
		Compute_Var_Order_Automatical();
		break;
	case minfill:
		Compute_Var_Order_Min_Fill_Heuristic_Opt();
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
		break;
	case FlowCutter:
		Compute_Var_Order_Flow_Cutter();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The flow cutter treewidth: " << running_options.treewidth << endl;
	case LinearLRW:
		Compute_Var_Order_Single_Cluster();
		break;
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	case VSADS:
		break;
	case DLCS:
		break;
	case DLCP:
		break;
	case dynamic_minfill:
		Compute_Dynamic_Min_Fill_Bound( _max_var );
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
		break;
	default:
		cerr << "ERROR[KCounter]: this heuristic strategy is not supported yet!" << endl;
		exit( 1 );
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
	if ( running_options.trivial_variable_bound > _unsimplifiable_num_vars / 2 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars / 2;
	}
	if ( running_options.var_ordering_heur == minfill ) {
		if ( running_options.max_kdepth > 1 ) running_options.max_kdepth = 1;
//		running_options.trivial_variable_bound = 192;
		running_options.mixed_var_ordering = false;
	}
	else {
		if ( _unsimplifiable_num_vars < 320 ) running_options.kernelizing_step = 32;
		else running_options.kernelizing_step = 48;
	}
	if ( running_options.var_ordering_heur == DLCP ) {
//		running_options.lit_equivalence_detecting_strategy = Literal_Equivalence_Detection_IBCP;
	}
}

void KCounter::Compute_Var_Order_Automatical()
{
	const unsigned upper_bound = 128;
	unsigned treewidth_bound;
	if ( _unsimplifiable_num_vars <= 32 ) treewidth_bound = _unsimplifiable_num_vars / 4;
	else {
		treewidth_bound = 32 / 4;
		if ( _unsimplifiable_num_vars <= 64 ) treewidth_bound += ( _unsimplifiable_num_vars - 32 ) / 5;
		else {
			treewidth_bound += ( 64 - 32 ) / 5;
			if ( _unsimplifiable_num_vars <= 128 ) treewidth_bound += ( _unsimplifiable_num_vars - 64 ) / 6;
			else {
				treewidth_bound += ( 128 - 64 ) / 6;
				treewidth_bound += ( _unsimplifiable_num_vars - 128 ) / 7;
			}
		}
	}
	if ( treewidth_bound > upper_bound ) treewidth_bound = upper_bound;
	Compute_Var_Order_Min_Fill_Heuristic_Bound( treewidth_bound );
	if ( running_options.treewidth <= treewidth_bound ) {
		running_options.var_ordering_heur = minfill;
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
	}
	else {
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: > " << treewidth_bound << endl;
		running_options.var_ordering_heur = DLCP;  // ToModify
		if ( running_options.var_ordering_heur == LinearLRW ) Compute_Var_Order_Single_Cluster();
	}
}

void KCounter::Choose_Running_Options_Static( Heuristic heur )
{
	running_options.var_ordering_heur = heur;
	switch ( running_options.var_ordering_heur ) {
	case AutomaticalHeur:
		Compute_Var_Order_Automatical_Static();
		break;
	case minfill:
		Compute_Var_Order_Min_Fill_Heuristic_Opt();
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
		break;
	case FlowCutter:
		Compute_Var_Order_Flow_Cutter();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The flow cutter treewidth: " << running_options.treewidth << endl;
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	default:
		cerr << "ERROR[KCounter]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		if ( !running_options.static_heur ) Choose_Implicate_Computing_Strategy();
		else Choose_Implicate_Computing_Strategy_Static();
	}
}

void KCounter::Compute_Var_Order_Automatical_Static()
{
	const unsigned treewidth_bound = _unsimplifiable_num_vars / 4;
	Compute_Var_Order_Min_Fill_Heuristic_Bound( treewidth_bound );
	if ( running_options.treewidth <= treewidth_bound ) {
		running_options.var_ordering_heur = minfill;
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
	}
	else {
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: > " << treewidth_bound << endl;
		running_options.var_ordering_heur = LinearLRW;
		Compute_Var_Order_Single_Cluster();
	}
}

void KCounter::Choose_Implicate_Computing_Strategy()
{
	assert( running_options.imp_strategy == Automatical_Imp_Computing );
	if ( Is_TreeD_Based_Ordering( running_options.var_ordering_heur ) ) {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else if ( running_options.treewidth <= 48 ) running_options.imp_strategy = No_Implicit_BCP;
		else if ( running_options.treewidth <= 72 ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else if ( running_options.treewidth <= _unsimplifiable_num_vars / 128 ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	else {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	running_options.sat_employ_external_solver_always = false;
}

void KCounter::Choose_Implicate_Computing_Strategy_Static()
{
	assert( running_options.imp_strategy == Automatical_Imp_Computing );
	if ( running_options.var_ordering_heur == minfill ) {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else if ( running_options.treewidth <= 48 ) running_options.imp_strategy = No_Implicit_BCP;
		else if ( running_options.treewidth <= 72 ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else if ( running_options.treewidth <= _unsimplifiable_num_vars / 128 ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	else {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	running_options.sat_employ_external_solver_always = false;
}

void KCounter::Create_Init_Level()
{
	StopWatch tmp_watch;
	_dec_offsets[0] = 0;  // NOTE: the first bit facilitates loop break
	_comp_offsets[0] = 0;
	_active_comps[0] = 0;
	_num_rsl_stack = 0;
	assert( _num_levels == 1 );  // NOTE: level 0 is used to unary clauses
	Generate_Init_Component( *_comp_stack );  // NOTE: we will not decompose the initialized formula
	_dec_offsets[1] = _num_dec_stack;
	_state_stack[1] = 1;
	_num_comp_stack = 1;
	_comp_offsets[1] = 0;
	_active_comps[1] = 0;
	_num_levels = 2;
	assert( _component_cache.Size() == 0 );
	if ( running_options.profile_counting >= Profiling_Abstract ) tmp_watch.Start();
	_component_cache.Init( _max_var, _old_num_long_clauses, -1 );
	Component_Cache_Add_Original_Clauses();
	_component_cache.Hit_Component( _comp_stack[0] );
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
}

void KCounter::Component_Cache_Add_Original_Clauses()
{
	unsigned j, num;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			assert( Lit_Undecided( lit ) && Lit_Undecided( _many_lits[j] ) );
			_component_cache.Add_Original_Binary_Clause( lit, _many_lits[j] );
		}
		lit = Literal( i, true );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			assert( Lit_Undecided( lit ) && Lit_Undecided( _many_lits[j] ) );
			_component_cache.Add_Original_Binary_Clause( lit, _many_lits[j] );
		}
	}
	if ( DEBUG_OFF ) _unified_comp.Verify_Orderness();  // ToRemove
}

void KCounter::Count_With_Implicite_BCP()
{
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigInt cached_result;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					Backjump_Decision( backjump_level );
					break;
				}
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Backtrack_True();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						Backtrack_Known( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				var = Pick_Good_Var_Component( Current_Component() );
				Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				if ( _rsl_stack[_num_rsl_stack - 1] != 0 ) {
					_state_stack[_num_levels - 1]++;
					Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
				}
				else {
					_num_rsl_stack--;  // pop 0
					_num_comp_stack = _comp_offsets[_num_levels - 1];  // re-decompose
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );  // reason is assigned in the last iteration
				}
				break;
			case 3:
				Backtrack_Decision();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there are unknown cacheable component
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Pick_Good_Var_Component( Current_Component() );
						Extend_New_Level();
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					if ( _rsl_stack[_num_rsl_stack - 1] != 0 ) {
						Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_rsl_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
						backjump_reason = Get_Approx_Imp_Component( Current_Component(), backjump_level );  /// current component rather than parent component
						if ( backjump_reason != Reason::undef ) {
							Backjump_Decomposition( backjump_level );
							break;
						}
						unsigned num_comp = Dynamic_Decompose_Component( Current_Component(), _comp_stack + _num_comp_stack );
						_num_comp_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Component() = _comp_stack[_num_comp_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							Backtrack_Decomposition2Decision();  // overwrite the result of the only one component
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_comps[_num_levels - 1] == _num_comp_stack - 1 );
							cached_result = Component_Cache_Map_Current_Component();  /// NOTE: the current component was after the collapsed one
							if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there are unknown cacheable component
								Backtrack_Known( cached_result );
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					Iterate_Decision();
					break;
				}
			}
			else {  // all components are already processed
				Backtrack_Decomposition();
			}
		}
	}
	assert( _num_levels == old_num_levels - 1 && _num_rsl_stack == old_num_rsl_stack + 1 );
}

void KCounter::Backjump_Decision( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
	_component_cache.Entry_Reset_Subtrees( Current_Component().caching_loc );
	if ( !Finished_Decision_Of_Current_Component() ) _component_cache.Entry_Disconnect_Parent( Current_Component().caching_loc );
	_rsl_stack[_num_rsl_stack++] = 0;  /// NOTE: cannot omit when in the second decision, and need to be AFTER backjump
}

void KCounter::Backtrack_True()
{
	_rsl_stack[_num_rsl_stack] = 1;
	_aux_rsl_stack[_num_rsl_stack++] = Num_Current_Imps();
	Backtrack();
}

void KCounter::Backtrack_Known( BigInt cached_result )
{
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), cached_result );
	}
	_rsl_stack[_num_rsl_stack] = cached_result;
	_aux_rsl_stack[_num_rsl_stack++] = Current_Component().Vars_Size() + Num_Current_Imps();
	Backtrack();
}

BigInt KCounter::Component_Cache_Map_Current_Component()
{
	StopWatch begin_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	Component & comp = Current_Component();
	if ( _current_kdepth <= 1 ) comp.caching_loc = _component_cache.Hit_Component( comp );
	else {
		Generate_Incremental_Component( comp );
		comp.caching_loc = _component_cache.Hit_Component( _incremental_comp );
	}
	if ( DEBUG_OFF && comp.caching_loc == 9 ) {  // ToRemove
		comp.Display( cerr );
		if ( _current_kdepth > 1 ) _incremental_comp.Display( cerr );
		Display_Component( comp, cerr );
	}
	if ( _component_cache.Entry_Is_Isolated( comp.caching_loc ) ) {
		Component_Cache_Connect_Current_Component();
	}
	if ( Cache_Clear_Applicable() ) Component_Cache_Clear();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += begin_watch.Get_Elapsed_Seconds();
	return _component_cache.Read_Result( comp.caching_loc );
}

void KCounter::Generate_Incremental_Component( Component & comp )
{
	_incremental_comp.Clear();
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars(i);
		_incremental_comp.Add_Var( var );
		Literal lit( var, false );
		for ( unsigned j = 0; j < _cached_binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _cached_binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned id = _component_cache.Encode_Binary_Clause( lit, lit2 );
			ASSERT( lit < lit2 && id != UNSIGNED_UNDEF );
			_incremental_comp.Add_ClauseID( id );
		}
		lit = Literal( var, true );
		for ( unsigned j = 0; j < _cached_binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _cached_binary_clauses[lit][j];
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned id = _component_cache.Encode_Binary_Clause( lit, lit2 );
			ASSERT( lit < lit2 && id != UNSIGNED_UNDEF );
			_incremental_comp.Add_ClauseID( id );
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_incremental_comp.Add_ClauseID( _long_clause_ids[comp.ClauseIDs(i)] );
	}
}

void KCounter::Generate_Incremental_Component_Old( Component & comp )
{
	unsigned i, j, num;
	_incremental_comp.Clear();
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars(i);
		_incremental_comp.Add_Var( var );
		Literal lit( var, false );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			unsigned id = _component_cache.Encode_Binary_Clause( lit, _many_lits[j] );
			if ( id != UNSIGNED_UNDEF ) _incremental_comp.Add_ClauseID( id );
		}
		lit = Literal( var, true );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 || Lit_Decided( lit2 ) ) continue;
			_many_lits[num++] = lit2;
		}
		_qsorter.Sort( _many_lits, num );
		for ( j = 0; j < num; j++ ) {
			unsigned id = _component_cache.Encode_Binary_Clause( lit, _many_lits[j] );
			if ( id != UNSIGNED_UNDEF ) _incremental_comp.Add_ClauseID( id );
		}
	}
//	_incremental_comp.Sort_ClauseIDs( _qsorter );
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_incremental_comp.Add_ClauseID( _long_clause_ids[comp.ClauseIDs(i)] );
	}
}

void KCounter::Component_Cache_Connect_Current_Component()
{
	if ( Is_Current_Level_Decision() || Active_Position_On_Level( _num_levels - 1 ) == 0 ) {
		_component_cache.Entry_Add_Child( Parent_of_Current_Component().caching_loc, Current_Component().caching_loc );
	}
	else _component_cache.Entry_Add_Sibling( Previous_Component().caching_loc, Current_Component().caching_loc );
}

bool KCounter::Cache_Clear_Applicable()
{
	const size_t GB = 1024 * 1024 * 1024;
	double max_mem = running_options.max_memory * GB;
	if ( false ) {
		return _component_cache.Memory() > max_mem * 0.5;
/*		if ( _component_cache.Memory() > max_mem * 0.5 ) return true;
		double upper_bound = max_mem * 0.8;
		if ( mem >= upper_bound ) return true;
		unsigned size = _component_cache.Size();
		unsigned capacity = size + size * ( upper_bound / mem - 1 ) / 2;
		_component_cache.Reserve( capacity );  // in case of overflow
		return false;*/
	}
	if ( _component_cache.Memory() <= max_mem * 0.3 ) return false;
	if ( _component_cache.Memory() > max_mem * 0.7 ) return true;
	if ( _component_cache.Size() < _component_cache.Capacity() || _component_cache.Hit_Successful() ) return false;
	size_t mem = Total_Used_Memory();
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) {
		cout << running_options.display_prefix << (float) _component_cache.Memory() / GB << " (cache) / ";
		cout << (float) mem / GB << " (total) in GB" << endl;
	}
	if ( mem < max_mem * 0.8 ) return false;
	else return true;
}

void KCounter::Component_Cache_Clear()
{
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "clear cache" << endl;
	vector<size_t> kept_locs;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( _comp_stack[_comp_offsets[i]].caching_loc );
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			kept_locs.push_back( _comp_stack[j].caching_loc );
		}
	}
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		if ( _call_stack[i].Existed() ) kept_locs.push_back( _call_stack[i].Get_Caching_Loc() );
	}
	if ( !running_options.clear_half_of_cache ) _component_cache.Clear_Shrink_Half( kept_locs );
	else _component_cache.Clear_Half( kept_locs );
	unsigned index = 0;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		_comp_stack[_comp_offsets[i]].caching_loc = kept_locs[index++];
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			_comp_stack[j].caching_loc = kept_locs[index++];
		}
	}
	Component_Cache_Reconnect_Components();
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		if ( _call_stack[i].Existed() ) _call_stack[i].Set_Caching_Loc( kept_locs[index++] );
	}
}

void KCounter::Component_Cache_Reconnect_Components()
{
	_component_cache.Entry_Set_Isolated( Active_Component( 1 ).caching_loc );
	for ( unsigned i = 2; i < _num_levels; i++ ) {
		Component & parent = Active_Component( i - 1 );
		_component_cache.Entry_Set_Isolated( _comp_stack[_comp_offsets[i]].caching_loc );
		_component_cache.Entry_Add_Child( parent.caching_loc, _comp_stack[_comp_offsets[i]].caching_loc );
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			_component_cache.Entry_Set_Isolated( _comp_stack[j].caching_loc );
			_component_cache.Entry_Add_Sibling( _comp_stack[j - 1].caching_loc, _comp_stack[j].caching_loc );
		}
	}
}

void KCounter::Backtrack()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void KCounter::Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	_comp_offsets[_num_levels] = _num_comp_stack;
	_active_comps[_num_levels] = _comp_offsets[_num_levels];
	_state_stack[_num_levels++] = 0;
}

void KCounter::Backtrack_Decision()
{
	assert( _num_rsl_stack > 1 );
	assert( _rsl_stack[_num_rsl_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( _rsl_stack[_num_rsl_stack - 1] == 0 );  /// NOTE: conflict can come from the upper levels
//	cerr << _rsl_stack[_num_rsl_stack - 2] << " vs " << _rsl_stack[_num_rsl_stack - 1] << endl;  // ToRemove
	_num_rsl_stack--;
	unsigned omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack - 1] - 1;
	_rsl_stack[_num_rsl_stack - 1].Mul_2exp( omit );
	omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack] - 1;
	_rsl_stack[_num_rsl_stack].Mul_2exp( omit );
	_rsl_stack[_num_rsl_stack - 1] += _rsl_stack[_num_rsl_stack];
	if ( _num_levels != 2 ) _aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size() + Num_Current_Imps();
	else _aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();// NOTE: _dec_offsets[1] is equal to the number of initial implied literals
	if ( !incomplete && debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	if ( !incomplete ) _component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	Backtrack();
}

void KCounter::Backjump_Decomposition( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	_num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
	_component_cache.Entry_Reset_Subtrees( Current_Component().caching_loc );
	if ( !Finished_Decision_Of_Current_Component() ) _component_cache.Entry_Disconnect_Parent( Current_Component().caching_loc );
	_rsl_stack[_num_rsl_stack++] = 0;  /// NOTE: cannot omit when in the second decision, and need to be AFTER backjump
}

void KCounter::Iterate_Known( BigInt cached_result )
{
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), cached_result );
	}
	_rsl_stack[_num_rsl_stack] = cached_result;
	_aux_rsl_stack[_num_rsl_stack++] = Current_Component().Vars_Size();
	_active_comps[_num_levels - 1]++;
}

void KCounter::Backtrack_Decomposition2Decision()
{
	_aux_rsl_stack[_num_rsl_stack - 1] += Num_Current_Imps();  // overwrite the result of the only one component
	Backtrack();
}

void KCounter::Iterate_Decision()
{
	assert( _num_rsl_stack > 1 );
	assert( _rsl_stack[_num_rsl_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( _rsl_stack[_num_rsl_stack - 1] == 0 );  /// NOTE: conflict can come from the upper levels
	_num_rsl_stack--;
	unsigned omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack - 1] - 1;
	_rsl_stack[_num_rsl_stack - 1].Mul_2exp( omit );
	omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack] - 1;
	_rsl_stack[_num_rsl_stack].Mul_2exp( omit );
	_rsl_stack[_num_rsl_stack - 1] += _rsl_stack[_num_rsl_stack];
	_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();
	if ( !incomplete && debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	if ( !incomplete ) _component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	_active_comps[_num_levels - 1]++;
}

void KCounter::Backtrack_Decomposition()
{
	_num_rsl_stack -= Num_Components_On_Current_Level();
	assert( _num_levels > 2 );  // not decompose the initial formula
	_rsl_stack[_num_rsl_stack] *= _rsl_stack[_num_rsl_stack + 1];
	_aux_rsl_stack[_num_rsl_stack] += _aux_rsl_stack[_num_rsl_stack + 1];
	for ( unsigned i = 2; i < Num_Components_On_Current_Level(); i++ ) {
		_rsl_stack[_num_rsl_stack] *= _rsl_stack[_num_rsl_stack + i];
		_aux_rsl_stack[_num_rsl_stack] += _aux_rsl_stack[_num_rsl_stack + i];
	}
	_aux_rsl_stack[_num_rsl_stack] += Num_Current_Imps();
	_num_rsl_stack++;
	Backtrack();
}

void KCounter::Count_With_SAT_Imp_Computing()
{
	StopWatch tmp_watch;
	Variable var;
	BigInt cached_result;
	Move_Models( _models_stack[0], _models_stack[1] );
	while ( _num_levels > 1 ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				Get_All_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack_True();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Recycle_Models( _models_stack[_num_levels - 1] );
						Backtrack_Known( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				if ( Try_Shift_To_Implicite_BCP() ) break;
				_state_stack[_num_levels - 1]++;
				if ( Try_Kernelization() == lbool::unknown ) break;
				var = Pick_Good_Var_Component( Current_Component() );
				Extend_New_Level();
				Pick_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
				Assign( Literal( var, false ) );
				break;
			case 2:
				assert( _rsl_stack[_num_rsl_stack - 1] != 0 );
				_state_stack[_num_levels - 1]++;
				Extend_New_Level();
				Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
				Assign( ~_dec_stack[_num_dec_stack] );
				break;
			case 3:
				assert( _models_stack[_num_levels - 1].empty() );
				Calculate_Decision();
				Leave_Kernelization();
				Backtrack_Decision_Imp();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						if ( Try_Kernelization() == lbool::unknown ) break;
						var = Pick_Good_Var_Component( Current_Component() );
						Extend_New_Level();
						Inherit_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					assert( _rsl_stack[_num_rsl_stack - 1] != 0 );
					Extend_New_Level();
					Inherit_Models( _models_stack[_num_levels - 2], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels - 1] );
					Assign( ~_dec_stack[_num_dec_stack] );
					break;
				case 2:
					Calculate_Decision();
					Leave_Kernelization();
					Iterate_Decision_Next();
					break;
				}
			}
			else {  // all components are already processed
				Recycle_Models( _models_stack[_num_levels - 1] );
				Backtrack_Decomposition();
			}
		}
	}
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

bool KCounter::Try_Shift_To_Implicite_BCP()
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
	if ( Try_Final_Kernelization() == lbool::unknown ) return true;
	running_options.imp_strategy = Partial_Implicit_BCP_Neg;
	if ( !running_options.static_heur && running_options.mixed_var_ordering ) {
		Heuristic old_heur = running_options.var_ordering_heur;
		Chain old_order;
		_var_order.Swap( old_order );
		Compute_Second_Var_Order_Automatical( comp );
		Recycle_Models( _models_stack[_num_levels - 1] );
		Count_With_Implicite_BCP();
		_var_order.Swap( old_order );
		running_options.var_ordering_heur = old_heur;
	}
	else {
		Recycle_Models( _models_stack[_num_levels - 1] );
		Count_With_Implicite_BCP();
	}
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) system( "./pause" );  // ToRemove
	running_options.imp_strategy = SAT_Imp_Computing;
	Leave_Final_Kernelization();
	return true;
}

bool KCounter::Estimate_Hardness( Component & comp )
{
	unsigned density = 0;
	if ( false ) {
		for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
			Variable var = comp.Vars( i );
			for ( unsigned j = 0; j < _binary_var_membership_lists[var].size(); j++ ) {
				density += Var_Undecided( _binary_var_membership_lists[var][j] );
			}
		}
		density /= 2;
		cerr << comp.Vars_Size() << ": " << density;
		for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
			Clause & clause = _long_clauses[comp.ClauseIDs( i )];
			unsigned true_size = 0;
			true_size += Lit_Undecided( clause[0] );
			true_size += Lit_Undecided( clause[1] );
			true_size += Lit_Undecided( clause[2] );
			for ( unsigned j = 3; j < clause.Size(); j++ ) {
				true_size += Lit_Undecided( clause[j] );
			}
			density += true_size * ( true_size - 1 ) / 2;
	//		cerr << "(" << clause.Size() << " vs " << true_size << ")";
		}
		cerr << " -> " << density << endl;
		return density / comp.Vars_Size() >= 16;
	}
	else if ( true ) {
		unsigned density = 0;
		unsigned sum = 0;
		for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
			Clause & clause = _long_clauses[comp.ClauseIDs( i )];
			unsigned true_size = 0;
			true_size += Lit_Undecided( clause[0] );
			true_size += Lit_Undecided( clause[1] );
			true_size += Lit_Undecided( clause[2] );
			for ( unsigned j = 3; j < clause.Size(); j++ ) {
				true_size += Lit_Undecided( clause[j] );
			}
			if ( true_size > 2 ) {
				density += true_size * ( true_size - 1 ) / 2;
				sum += true_size;
			}
			if ( false ) cerr << "(" << clause.Size() << " vs " << true_size << ")";
		}
		if ( false ) cerr << comp.Vars_Size() << ": " << density << " and " << sum << endl;  // ToRemove
		return density / comp.Vars_Size() >= 3 && sum > comp.Vars_Size() / 2;
	}
	else {
		unsigned density = 0;
		for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
			Clause & clause = _long_clauses[comp.ClauseIDs( i )];
			density += clause.Size() * Ceil_Log2( clause.Size() );
		}
		cerr << comp.Vars_Size() << ": " << density << endl;  // ToRemove
		return density / comp.Vars_Size() >= 8;
	}
}

lbool KCounter::Try_Final_Kernelization()
{
	if ( _current_kdepth >= running_options.max_kdepth || Estimate_Final_Kernelization_Effect() == false ) return lbool(false);
	_component_cache.Entry_Disconnect_Parent( Current_Component().caching_loc );
	Store_Cached_Binary_Clauses();
	Kernelize_Without_Imp();
	Set_Current_Level_Kernelized( true );
	Sort_Clauses_For_Caching();
	BigInt cached_result;
	if ( Current_Component().Vars_Size() == 0 ) {
		Current_Component().caching_loc == CacheEntryID::undef;
		cached_result = 1;
	}
	else cached_result = Component_Cache_Map_Current_Component();
	if ( cached_result != _component_cache.Default_Caching_Value() ) {
		if ( debug_options.verify_component_count ) {
			Verify_Result_Component( Current_Component(), cached_result );
		}
		_rsl_stack[_num_rsl_stack] = cached_result;
		_aux_rsl_stack[_num_rsl_stack++] = Current_Component().Vars_Size();
		Leave_Kernelization();
		ASSERT( Is_Current_Level_Decision() );
		_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size() + Num_Current_Imps();
		Recycle_Models( _models_stack[_num_levels - 1] );
		Backtrack();
		return lbool::unknown;
	}
	assert( running_options.decompose_strategy == Decompose_Without_Sorting );
	Generate_Long_Watched_Lists_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Binary_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Long();  // ToModify
	return lbool(true);
}

bool KCounter::Estimate_Final_Kernelization_Effect()
{
	const double ratio = 0.5;
	if ( Current_Component().Vars_Size() <= running_options.trivial_variable_bound * ratio ) return false;
	unsigned step = running_options.kernelizing_step / 2;
	if ( step > running_options.trivial_variable_bound / 8 ) step = running_options.trivial_variable_bound / 8;
	if ( false ) {
		if ( _num_levels > 2 ) return true;  // ToModify
		else return false;
	}
	else if ( true ) {
		return Estimate_Kernelization_Effect_Enough_Decisions( step, 3 );
	}
	else if ( true ) {
		if ( Current_Component().Vars_Size() > running_options.trivial_variable_bound * 2 ) return false;
		return Estimate_Kernelization_Effect_Enough_Decisions( step, 3 );
	}
	else {
		return Current_Component().Vars_Size() <= running_options.trivial_variable_bound / ratio;
	}
}

void KCounter::Leave_Final_Kernelization()
{
	if ( !_call_stack[_num_levels].Existed() ) return;  // _num_levels-- is done in IBCP
	Extend_New_Level();
	_num_comp_stack += 1;
	unsigned old_size = Current_Component().Vars_Size();
	unsigned lit_equ_size = _call_stack[_num_levels - 1].Lit_Equivalences_Size();
	CacheEntryID kernelized_loc = Current_Component().caching_loc;
	Clear_Cached_Binary_Clauses();
	Set_Current_Level_Kernelized( false );
	Cancel_Kernelization_Without_Imp();
	if ( _component_cache.Entry_Is_Child( Parent_of_Current_Component().caching_loc, kernelized_loc ) ) {
		if ( kernelized_loc != Current_Component().caching_loc ) {
			_component_cache.Entry_Swap( kernelized_loc, Current_Component().caching_loc );
		}
	} else {
		_component_cache.Entry_Add_Child( Parent_of_Current_Component().caching_loc, Current_Component().caching_loc );
	}
	Recover_Cached_Binary_Clauses();
	Encode_Long_Clauses();
//	Display_Component( Current_Component(), cerr );  // ToRemove
	unsigned exp = Current_Component().Vars_Size() - old_size - lit_equ_size;
	_rsl_stack[_num_rsl_stack - 1].Mul_2exp( exp );
	if ( false && debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	unsigned num_decisions = _aux_rsl_stack[_num_rsl_stack - 1] - old_size;
	_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size() + num_decisions;
	Backtrack();
}

void KCounter::Compute_Second_Var_Order_Automatical( Component & comp )
{
	if ( comp.Vars_Size() <= 32 ) {
//		cerr << "unknown width" << endl;  // ToRemove
		running_options.var_ordering_heur = DLCP;
		return;
	}
	const unsigned bound = comp.Vars_Size() / 6;
	unsigned width = Compute_Var_Order_Min_Fill_Bound_Component( comp, bound );
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) {
		cerr << comp.Vars_Size() << ", ";
		if ( width > bound ) cerr << "width > " << bound << endl;  // ToRemove
		else cerr << "width = " << width << endl;  // ToRemove
		_var_order.Display_Top( cerr, comp.Vars_Size() );  // ToRemove
	}
	if ( width <= bound ) {
		running_options.var_ordering_heur = minfill;
	}
	else running_options.var_ordering_heur = DLCP;
}

lbool KCounter::Try_Kernelization()
{
	if ( _current_kdepth >= running_options.max_kdepth || Estimate_Kernelization_Effect() == false ) return lbool(false);
	_component_cache.Entry_Disconnect_Parent( Current_Component().caching_loc );
	Store_Cached_Binary_Clauses();
	Kernelize_Without_Imp();
	Set_Current_Level_Kernelized( true );
	Sort_Clauses_For_Caching();
	BigInt cached_result;
	if ( Current_Component().Vars_Size() == 0 ) {
		Current_Component().caching_loc == CacheEntryID::undef;
		cached_result = 1;
	}
	else cached_result = Component_Cache_Map_Current_Component();
	if ( cached_result != _component_cache.Default_Caching_Value() ) {
		if ( debug_options.verify_component_count ) {
			Verify_Result_Component( Current_Component(), cached_result );
		}
		_rsl_stack[_num_rsl_stack] = cached_result;
		_aux_rsl_stack[_num_rsl_stack++] = Current_Component().Vars_Size();
		Leave_Kernelization();
		if ( Is_Current_Level_Decision() ) {
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size() + Num_Current_Imps();
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			Recycle_Models( _models_stack[_num_levels - 1] );
			Backtrack();
		}
		else {
			_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();
			_active_comps[_num_levels - 1]++;
			_state_stack[_num_levels - 1] += 2;
		}
		return lbool::unknown;
	}
	assert( running_options.decompose_strategy == Decompose_Without_Sorting );
	Generate_Long_Watched_Lists_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Binary_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Long();  // ToModify
	return lbool(true);
}

bool KCounter::Estimate_Kernelization_Effect()
{
	const double ratio = 0.75;
	if ( Current_Component().Vars_Size() <= running_options.trivial_variable_bound * ratio ) return false;
	if ( false ) {
		if ( _num_levels > 2 ) return true;  // ToModify
		else return false;
	}
	else if ( running_options.var_ordering_heur == DLCP ) {
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step, 3 );
	}
	else if ( Is_TreeD_Based_Ordering( running_options.var_ordering_heur ) ) {
		if ( Current_Component().Vars_Size() > running_options.trivial_variable_bound * 2 ) return false;
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step, 3 );
	}
	else {
		return Current_Component().Vars_Size() <= running_options.trivial_variable_bound / ratio;
	}
}

void KCounter::Sort_Clauses_For_Caching()
{
	StopWatch begin_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	for ( unsigned i = 0; i < Current_Component().Vars_Size(); i++ ) {
		Variable var = Current_Component().Vars(i);
		unsigned j, num;
		Literal lit( var, false );
		_cached_binary_clauses[lit].resize( _old_num_binary_clauses[lit] );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			ASSERT( Lit_Undecided( lit2 ) );
			if ( lit > lit2 ) continue;
			_cached_binary_clauses[lit][num] = lit2;
			unsigned id = _component_cache.Encode_Binary_Clause( lit, lit2 );
			num += ( id != UNSIGNED_UNDEF );
		}
		_cached_binary_clauses[lit].resize( num );
		_qsorter.Sort( _cached_binary_clauses[lit] );
		lit = Literal( var, true );
		_cached_binary_clauses[lit].resize( _old_num_binary_clauses[lit] );
		for ( j = num = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			ASSERT( Lit_Undecided( lit2 ) );
			if ( lit > lit2 ) continue;
			_cached_binary_clauses[lit][num] = lit2;
			unsigned id = _component_cache.Encode_Binary_Clause( lit, lit2 );
			num += ( id != UNSIGNED_UNDEF );
		}
		_cached_binary_clauses[lit].resize( num );
		_qsorter.Sort( _cached_binary_clauses[lit] );
	}
	Sort_Long_Clauses_By_IDs();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += begin_watch.Get_Elapsed_Seconds();
}

void KCounter::Sort_Long_Clauses_By_IDs()
{
	Encode_Long_Clauses();
	_long_clause_ranks.resize( _old_num_long_clauses );
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		_long_clause_ranks[i] = i;
	}
	_qsorter.Sort( _long_clause_ranks, _long_clause_ids );
	_swap_frame.Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	_long_clauses.resize( _long_clause_ranks.size() );
	_old_num_long_clauses = _long_clauses.size();
	_clause_stack = _long_clause_ids;
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		_long_clauses[i] = _swap_frame.Long_Clauses()[_long_clause_ranks[i]];
		_long_clause_ids[i] = _clause_stack[_long_clause_ranks[i]];
	}
	_swap_frame.Clear_Long_Clauses();
	_clause_stack.clear();
}

void KCounter::Encode_Long_Clauses()
{
	_long_clause_ids.resize( _old_num_long_clauses );
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			_many_lits[j] = clause[j];
		}
		_qsorter.Sort( _many_lits, clause.Size() );
		_long_clause_ids[i] = _component_cache.Encode_Long_Clause( _many_lits, clause.Size() );
	}
}

void KCounter::Leave_Kernelization()
{
	if ( !_call_stack[_num_levels - 1].Existed() ) return;
	unsigned lit_equ_size = _call_stack[_num_levels - 1].Lit_Equivalences_Size();
	CacheEntryID kernelized_loc = Current_Component().caching_loc;
	Clear_Cached_Binary_Clauses();
	Set_Current_Level_Kernelized( false );
	Cancel_Kernelization_Without_Imp();
	if ( _component_cache.Entry_Is_Child( Parent_of_Current_Component().caching_loc, kernelized_loc ) ) {
		if ( kernelized_loc != Current_Component().caching_loc ) {
			_component_cache.Entry_Swap( kernelized_loc, Current_Component().caching_loc );
		}
	} else {
		_component_cache.Entry_Add_Child( Parent_of_Current_Component().caching_loc, Current_Component().caching_loc );
	}
	Recover_Cached_Binary_Clauses();
	Encode_Long_Clauses();
	unsigned exp = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack - 1] - lit_equ_size;
	_rsl_stack[_num_rsl_stack - 1].Mul_2exp( exp );
	_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
}

void KCounter::Calculate_Decision()
{
	assert( _num_rsl_stack > 1 );
	assert( _rsl_stack[_num_rsl_stack - 2] != 0 );  // backjump guarantees this
//	cerr << _rsl_stack[_num_rsl_stack - 2] << " vs " << _rsl_stack[_num_rsl_stack - 1] << endl;  // ToRemove
	_num_rsl_stack--;
	unsigned omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack - 1] - 1;
	_rsl_stack[_num_rsl_stack - 1].Mul_2exp( omit );
	omit = Current_Component().Vars_Size() - _aux_rsl_stack[_num_rsl_stack] - 1;
	_rsl_stack[_num_rsl_stack].Mul_2exp( omit );
	_rsl_stack[_num_rsl_stack - 1] += _rsl_stack[_num_rsl_stack];
	_aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
}

void KCounter::Backtrack_Decision_Imp()
{
	assert( Is_Current_Level_Decision() );
	if ( _num_levels != 2 ) _aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size() + Num_Current_Imps();
	else _aux_rsl_stack[_num_rsl_stack - 1] = Current_Component().Vars_Size();// NOTE: _dec_offsets[1] is equal to the number of initial implied literals
	Backtrack();
}

void KCounter::Iterate_Decision_Next()
{
	_active_comps[_num_levels - 1]++;
}

BigInt KCounter::Count_Models( CNF_Formula & cnf, vector<Model *> & models )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	running_options.detect_lit_equivalence = ( running_options.max_kdepth > 0 );
	_models_stack[0] = models;
	models.clear();
	bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigInt count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		return count;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	_fixed_num_vars -= _and_gates.size();
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( AutomaticalHeur );
	else Choose_Running_Options_Static( AutomaticalHeur );
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) running_options.Display( cout );  // ToRemove
	Set_Current_Level_Kernelized( true );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {  // ToModify
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Count_With_Implicite_BCP();
	}
	else {
		if ( running_options.max_kdepth > 1 ) {
			if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) _lit_equivalency.Reorder( _var_order );
			Encode_Long_Clauses();
			assert( _long_clause_ids.back() == _old_num_long_clauses - 1 );
		}
		Count_With_SAT_Imp_Computing();
	}
	Set_Current_Level_Kernelized( false );
	_fixed_num_vars += _and_gates.size();
	Load_Lit_Equivalences( _call_stack[0] );
	_call_stack[0].Clear_Lit_Equivalences();
	BigInt count = Backtrack_Init();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_counting_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_counting >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Memory_Status( cout );
		}
	}
	Reset();
	if ( debug_options.verify_count ) {
		BigInt verified_count = Count_Verified_Models_d4( cnf );
		cerr << count << " vs " << verified_count << endl;
		assert( count == verified_count );
	}
	return count;
}

BigInt KCounter::Count_Models( CNF_Formula & cnf, vector<Model *> & models, double timeout )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	running_options.detect_lit_equivalence = ( running_options.max_kdepth > 0 );
	_models_stack[0] = models;
	models.clear();
	bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigInt count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		return count;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	_fixed_num_vars -= _and_gates.size();
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( AutomaticalHeur );
	else Choose_Running_Options_Static( AutomaticalHeur );
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) running_options.Display( cout );  // ToRemove
	Set_Current_Level_Kernelized( true );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {  // ToModify
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Count_With_Implicite_BCP( timeout );
	}
	else {
		if ( running_options.max_kdepth > 1 ) {
			if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) _lit_equivalency.Reorder( _var_order );
			Encode_Long_Clauses();
			assert( _long_clause_ids.back() == _old_num_long_clauses - 1 );
		}
		Count_With_SAT_Imp_Computing( timeout );
	}
	Set_Current_Level_Kernelized( false );
	_fixed_num_vars += _and_gates.size();
	Load_Lit_Equivalences( _call_stack[0] );
	_call_stack[0].Clear_Lit_Equivalences();
	BigInt count;
	if ( _num_rsl_stack == 1 ) count = Backtrack_Init();
	else count = Backtrack_Failure();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_counting_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_counting >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Memory_Status( cout );
		}
	}
	Reset();
	if ( debug_options.verify_count ) {
		BigInt verified_count = Count_Verified_Models_d4( cnf );
		cerr << count << " vs " << verified_count << endl;
		assert( count == verified_count );
	}
	return count;
}

void KCounter::Count_With_Implicite_BCP( double timeout )
{
	StopWatch stop_watch;
	stop_watch.Start();
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigInt cached_result;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		if ( stop_watch.Get_Elapsed_Seconds() >= timeout ) break;
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					Backjump_Decision( backjump_level );
					break;
				}
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Backtrack_True();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						Backtrack_Known( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				var = Pick_Good_Var_Component( Current_Component() );
				Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				if ( _rsl_stack[_num_rsl_stack - 1] != 0 ) {
					_state_stack[_num_levels - 1]++;
					Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
				}
				else {
					_num_rsl_stack--;  // pop 0
					_num_comp_stack = _comp_offsets[_num_levels - 1];  // re-decompose
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );  // reason is assigned in the last iteration
				}
				break;
			case 3:
				Backtrack_Decision();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there are unknown cacheable component
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Pick_Good_Var_Component( Current_Component() );
						Extend_New_Level();
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					if ( _rsl_stack[_num_rsl_stack - 1] != 0 ) {
						Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_rsl_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
						backjump_reason = Get_Approx_Imp_Component( Current_Component(), backjump_level );  /// current component rather than parent component
						if ( backjump_reason != Reason::undef ) {
							Backjump_Decomposition( backjump_level );
							break;
						}
						unsigned num_comp = Dynamic_Decompose_Component( Current_Component(), _comp_stack + _num_comp_stack );
						_num_comp_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Component() = _comp_stack[_num_comp_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							Backtrack_Decomposition2Decision();  // overwrite the result of the only one component
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_comps[_num_levels - 1] == _num_comp_stack - 1 );
							cached_result = Component_Cache_Map_Current_Component();  /// NOTE: the current component was after the collapsed one
							if ( cached_result != _component_cache.Default_Caching_Value() ) {  /// NOTE: backjump makes that there are unknown cacheable component
								Backtrack_Known( cached_result );
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					Iterate_Decision();
					break;
				}
			}
			else {  // all components are already processed
				Backtrack_Decomposition();
			}
		}
	}
	if ( _num_levels == old_num_levels - 1 ) assert( _num_rsl_stack == old_num_rsl_stack + 1 );
	else Terminate_Counting();
}

void KCounter::Terminate_Counting()
{
	_num_rsl_stack = 0;
	_swap_frame.Clear();
	while ( _num_levels > 1 ) {
		_call_stack[_num_levels - 1].Free_Long_Clauses();
		_call_stack[_num_levels - 1].Clear();
		Recycle_Models( _models_stack[_num_levels - 1] );
		Backtrack();
	}
}

void KCounter::Count_With_SAT_Imp_Computing( double timeout )
{
	StopWatch stop_watch, tmp_watch;
	stop_watch.Start();
	Variable var;
	BigInt cached_result;
	Move_Models( _models_stack[0], _models_stack[1] );
	while ( _num_levels > 1 ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		if ( stop_watch.Get_Elapsed_Seconds() >= timeout ) break;
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				Get_All_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack_True();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Recycle_Models( _models_stack[_num_levels - 1] );
						Backtrack_Known( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				if ( Try_Shift_To_Implicite_BCP( timeout - stop_watch.Get_Elapsed_Seconds() ) ) break;
				_state_stack[_num_levels - 1]++;
				if ( Try_Kernelization() == lbool::unknown ) break;
				var = Pick_Good_Var_Component( Current_Component() );
				Extend_New_Level();
				Pick_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
				Assign( Literal( var, false ) );
				break;
			case 2:
				assert( _rsl_stack[_num_rsl_stack - 1] != 0 );
				_state_stack[_num_levels - 1]++;
				Extend_New_Level();
				Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
				Assign( ~_dec_stack[_num_dec_stack] );
				break;
			case 3:
				assert( _models_stack[_num_levels - 1].empty() );
				Calculate_Decision();
				Leave_Kernelization();
				Backtrack_Decision_Imp();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_Current_Component();
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						if ( Try_Kernelization() == lbool::unknown ) break;
						var = Pick_Good_Var_Component( Current_Component() );
						Extend_New_Level();
						Inherit_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					assert( _rsl_stack[_num_rsl_stack - 1] != 0 );
					Extend_New_Level();
					Inherit_Models( _models_stack[_num_levels - 2], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels - 1] );
					Assign( ~_dec_stack[_num_dec_stack] );
					break;
				case 2:
					Calculate_Decision();
					Leave_Kernelization();
					Iterate_Decision_Next();
					break;
				}
			}
			else {  // all components are already processed
				Recycle_Models( _models_stack[_num_levels - 1] );
				Backtrack_Decomposition();
			}
		}
	}
	if ( _num_levels != 1 ) Terminate_Counting();
}

bool KCounter::Try_Shift_To_Implicite_BCP( double timeout )
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
	if ( Try_Final_Kernelization() == lbool::unknown ) return true;
	running_options.imp_strategy = Partial_Implicit_BCP_Neg;
	if ( !running_options.static_heur && running_options.mixed_var_ordering ) {
		Heuristic old_heur = running_options.var_ordering_heur;
		Chain old_order;
		_var_order.Swap( old_order );
		Compute_Second_Var_Order_Automatical( comp );
		Recycle_Models( _models_stack[_num_levels - 1] );
		Count_With_Implicite_BCP( timeout );
		_var_order.Swap( old_order );
		running_options.var_ordering_heur = old_heur;
	}
	else {
		Recycle_Models( _models_stack[_num_levels - 1] );
		Count_With_Implicite_BCP( timeout );
	}
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) system( "./pause" );  // ToRemove
	running_options.imp_strategy = SAT_Imp_Computing;
	if ( _num_rsl_stack > 0 ) Leave_Final_Kernelization();
	return true;
}

BigInt KCounter::Backtrack_Failure()
{
	assert( _num_rsl_stack == 0 );
	Backtrack();
	return _component_cache.Default_Caching_Value();
}

void KCounter::Verify_Result_Component( Component & comp, BigInt count )
{
	if ( !Verified_Path() && !Verified_Components( comp ) ) return;
	CNF_Formula * cnf = Output_Renamed_Clauses_In_Component( comp );
	BigInt verified_count = Count_Verified_Models_d4( *cnf );
	if ( verified_count != count ) {
		comp.Display( cerr );
		cerr << "caching location: " << comp.caching_loc << endl;
		Display_Decision_Stack( cerr, _num_levels - 1 );
		cerr << *cnf;
		cerr << "Count: " << count << endl;
		cerr << "Verified count: " << verified_count << endl;
		assert( verified_count == count );
	}
	delete cnf;
}

bool KCounter::Verified_Path()
{
	if ( true ) return true;  // all paths
	return _assignment[254] == false && _assignment[246] == false && _assignment[262] == false && _assignment[263] == false \
	&& _assignment[264] == false && _assignment[252] == false && _assignment[253] == true;
}

bool KCounter::Verified_Components( Component & comp )
{
	if ( true ) return true;  // all components
	return comp.caching_loc == 95855 || comp.caching_loc == 95856 || comp.caching_loc == 95857;
}

void KCounter::Display_Result_Stack( ostream & out )
{
	unsigned num = 0;
	for ( unsigned i = 2; i < _num_levels; i++ ) {
		if ( Num_Components_On_Level( i ) <= 1 ) {
			if ( _state_stack[i] == 2 ) {
				out << "[?, ?]" << endl;
			}
			else {
				assert( _state_stack[i] == 3 );
				out << "[" << _rsl_stack[num++] << ", ?]" << endl;
			}
		}
		else {
			if ( _active_comps[i] == _comp_offsets[i] ) {
				out << "[?";
				for ( unsigned j = 1; j < Num_Components_On_Level( i ); j++ ) {
					out << ", ?";
				}
				out << "]" << endl;
			}
			else {
				unsigned j;
				out << "[" << _rsl_stack[num++];
				for ( j = 1; j < _active_comps[i] - _comp_offsets[i]; j++ ) {
					out << ", " << _rsl_stack[num++];
				}
				for ( ; j < Num_Components_On_Level( i ); j++ ) {
					out << ", ?";
				}
				out << "]" << endl;
			}
		}
	}
}

void KCounter::Display_Statistics( unsigned option )
{
	switch ( option ) {
		case 0:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_count << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 1:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time compute tree decomposition: " << statistics.time_tree_decomposition << endl;
			if ( running_options.imp_strategy == SAT_Imp_Computing ) cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			cout << running_options.display_prefix << "time IBCP: " << statistics.time_ibcp << endl;
			cout << running_options.display_prefix << "time dynamic decomposition: " << statistics.time_dynamic_decompose << " (" << statistics.time_dynamic_decompose_sort << " sorting)" << endl;
			cout << running_options.display_prefix << "time cnf cache: " << statistics.time_gen_cnf_cache << endl;
			cout << running_options.display_prefix << "time kernelize: " << statistics.time_kernelize
				<< " (block lits: " << statistics.time_kernelize_block_lits
				<< "; vivi: " << statistics.time_kernelize_vivification
				<< "; equ: " << statistics.time_kernelize_lit_equ << ")";
			cout << " (max kdepth: " << statistics.max_non_trivial_kdepth << "/" << statistics.max_kdepth
				<< "; #kernelizations: " << statistics.num_non_trivial_kernelizations << "/" << statistics.num_kernelizations << ")" << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_count << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 10:  // sharpSAT
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_count << endl;
			break;
		default:
			cerr << "ERROR[KCounter]: this display mode is not existing!" << endl;
			assert( false );
			exit( 0 );
	}
}

void KCounter::Display_Memory_Status( ostream & out )
{
	size_t i, mem = 0;
	for ( i = 0; i < _long_clauses.size(); i++ ) {
		mem += _long_clauses[i].Size() * sizeof(unsigned) + sizeof(unsigned *) + sizeof(unsigned);
	}
	out << running_options.display_prefix << "#clauses: " << Num_Clauses() << " (" << mem / (1.0 * 1024 * 1024) << " M)" << endl;
	out << running_options.display_prefix << "#components: " << _component_cache.Size() << " (" << _component_cache.Memory() / (1.0 * 1024 * 1024) << " M)" << endl;
	if ( DEBUG_OFF ) out << running_options.display_prefix << "    Where the duplicate rate is " << _component_cache.Duplicate_Rate() << " and the useless ratio is " << _component_cache.Useless_Rate() << endl;
	out << running_options.display_prefix << "#models: " << _model_pool->Size() << "/" << _model_pool->Capacity() << " (" << _model_pool->Memory() / (1.0 * 1024 * 1024) << " M)" << endl;
	out << running_options.display_prefix << "Total memory: " << Memory() / (1.0 * 1024 * 1024) << "M" << endl;
}

bool KCounter::Is_Memory_Exhausted()
{
	size_t counterram = Memory();  // int overflows
	struct sysinfo info;
	sysinfo(&info);
	double free_ratio = 1.0 * info.freeram / info.totalram;
	static unsigned exhausted = 0.4;
	if ( counterram > exhausted * info.freeram && free_ratio <= 0.1 ) {
		return true;
	}
	else return false;
}


}
