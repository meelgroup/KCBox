#include "WCounter.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


WCounter::WCounter():
_num_rsl_stack( 0 )
{
}

WCounter::~WCounter()
{
	Free_Auxiliary_Memory();
}

void WCounter::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_counting != Profiling_Close ) statistics.Init_Compiler();
		return;
	}
	if ( running_options.profile_counting != Profiling_Close ) statistics.Init_Compiler_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_weights = new BigFloat [2 * _max_var + 2];
	_rsl_stack = new BigFloat [2 * _max_var + 2];
}

void WCounter::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
	delete [] _weights;
	delete [] _rsl_stack;
}

void WCounter::Reset()
{
	Inprocessor::Reset();
	_component_cache.Reset();
}

size_t WCounter::Memory()
{
	if ( _max_var == Variable::undef ) return 0;
	size_t mem = Preprocessor::Memory() + Inprocessor::Memory() + _component_cache.Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _models_stack[i].capacity() * sizeof(unsigned);
		mem += _comp_stack[i].Capacity() * sizeof(unsigned);
	}
	return mem;
}

BigFloat WCounter::Count_Models( WCNF_Formula & cnf, Heuristic heur )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
	}
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	bool cnf_sat;
	if ( !running_options.detect_AND_gates ) cnf_sat = Preprocess( cnf, _models_stack[0] );
	else cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	_normalized_factor = Normalize_Weights( cnf.Weights(), _weights );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigFloat count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		return count;
	}
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( heur );
	else Choose_Running_Options_Static( heur );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Count_With_Implicite_BCP();  // ToModify
	}
	else Count_With_SAT_Imp_Computing();
	BigFloat count = Backtrack_Init();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
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
		BigFloat verified_count = Count_Verified_Models_c2d( cnf );
		cout << verified_count << endl;
		cerr << count << " vs " << verified_count << endl;
		BigFloat ub = verified_count;
		ub *= 1.0001;
		BigFloat lb = verified_count;
		lb /= 1.0001;
		assert ( lb < count && count < ub );
	}
	return count;
}

BigFloat WCounter::Backtrack_Init()
{
	if ( _num_rsl_stack == 0 ) {
		_rsl_stack[0] = 1;
		Un_BCP( _dec_offsets[--_num_levels] );
	}
	else {
		_num_rsl_stack--;
		Backtrack();
	}
	_rsl_stack[0] *= _normalized_factor;
	return _rsl_stack[0];
}

void WCounter::Choose_Running_Options( Heuristic heur )
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
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	case VSADS:
		break;
	case DLCS:
		break;
	default:
		cerr << "ERROR[WCounter]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
}

void WCounter::Compute_Var_Order_Automatical()
{
	const unsigned bound = 64;  // 72;  // ToModify
	unsigned treewidth_bound = _unsimplifiable_num_vars / 128;
	if ( treewidth_bound < bound ) treewidth_bound = bound;
	Compute_Var_Order_Min_Fill_Heuristic_Bound( treewidth_bound );
	if ( running_options.treewidth <= treewidth_bound ) {
		running_options.var_ordering_heur = minfill;
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
	}
	else {
		if ( running_options.display_counting_process ) cout << running_options.display_prefix << "The minfill treewidth: > " << treewidth_bound << endl;
		running_options.var_ordering_heur = VSADS;
	}
}

void WCounter::Choose_Running_Options_Static( Heuristic heur )
{
	running_options.var_ordering_heur = heur;
	switch ( running_options.var_ordering_heur ) {
	case AutomaticalHeur:
		Compute_Var_Order_Automatical_Static();
		break;
	case minfill:
		Compute_Var_Order_Min_Fill_Heuristic_Opt();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
		break;
	case FlowCutter:
		Compute_Var_Order_Flow_Cutter();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The flow cutter treewidth: " << running_options.treewidth << endl;
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	default:
		cerr << "ERROR[WCounter]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
}

void WCounter::Compute_Var_Order_Automatical_Static()
{
	const unsigned treewidth_bound = _unsimplifiable_num_vars / 2;
	Compute_Var_Order_Min_Fill_Heuristic_Bound( treewidth_bound );
	if ( running_options.treewidth <= treewidth_bound ) {
		running_options.var_ordering_heur = minfill;
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
	}
	else {
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The minfill treewidth: > " << treewidth_bound << endl;
		running_options.var_ordering_heur = LinearLRW;
		Compute_Var_Order_Single_Cluster();
	}
}

void WCounter::Choose_Implicate_Computing_Strategy()
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

void WCounter::Create_Init_Level()
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
	_component_cache.Hit_Component( _comp_stack[0] );
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
}

void WCounter::Count_With_Implicite_BCP()
{
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigFloat cached_result;
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

void WCounter::Backjump_Decision( unsigned num_kept_levels )
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

void WCounter::Backtrack_True()
{
	_rsl_stack[_num_rsl_stack] = 1;
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_rsl_stack[_num_rsl_stack] *= _weights[_dec_stack[i]];
	}
	_num_rsl_stack++;
	Backtrack();
}

void WCounter::Backtrack_Known( BigFloat cached_result )
{
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), cached_result );
	}
	_rsl_stack[_num_rsl_stack] = cached_result;
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_rsl_stack[_num_rsl_stack] *= _weights[_dec_stack[i]];
	}
	_num_rsl_stack++;
	Backtrack();
}

BigFloat WCounter::Component_Cache_Map_Current_Component()
{
	StopWatch tmp_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) tmp_watch.Start();
	Component & comp = Current_Component();
	comp.caching_loc = _component_cache.Hit_Component( comp );
	if ( _component_cache.Entry_Is_Isolated( comp.caching_loc ) ) {
		Component_Cache_Connect_Current_Component();
	}
	if ( Cache_Clear_Applicable() ) Component_Cache_Clear();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
	return _component_cache.Read_Result( comp.caching_loc );
}

void WCounter::Component_Cache_Connect_Current_Component()
{
	if ( Is_Current_Level_Decision() || Active_Position_On_Level( _num_levels - 1 ) == 0 ) {
		_component_cache.Entry_Add_Child( Parent_of_Current_Component().caching_loc, Current_Component().caching_loc );
	}
	else _component_cache.Entry_Add_Sibling( Previous_Component().caching_loc, Current_Component().caching_loc );
}

bool WCounter::Cache_Clear_Applicable()
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

void WCounter::Component_Cache_Clear()
{
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "clear cache" << endl;
	vector<size_t> kept_locs;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( _comp_stack[_comp_offsets[i]].caching_loc );
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			kept_locs.push_back( _comp_stack[j].caching_loc );
		}
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
}

void WCounter::Component_Cache_Reconnect_Components()
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

void WCounter::Backtrack()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void WCounter::Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	_comp_offsets[_num_levels] = _num_comp_stack;
	_active_comps[_num_levels] = _comp_offsets[_num_levels];
	_state_stack[_num_levels++] = 0;
}

void WCounter::Backtrack_Decision()
{
	assert( _num_rsl_stack > 1 );
	assert( _rsl_stack[_num_rsl_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( _rsl_stack[_num_rsl_stack - 1] == 0 );  /// NOTE: conflict can come from the upper levels
	Literal decision = _dec_stack[_num_dec_stack];
//	cerr << _rsl_stack[_num_rsl_stack - 2] << " vs " << _rsl_stack[_num_rsl_stack - 1] << endl;  // ToRemove
	_num_rsl_stack--;
	_rsl_stack[_num_rsl_stack] *= _weights[decision];
	_rsl_stack[_num_rsl_stack - 1] *= _weights[~decision];
	_rsl_stack[_num_rsl_stack - 1] += _rsl_stack[_num_rsl_stack];
	if ( !incomplete && debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	if ( !incomplete ) _component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_rsl_stack[_num_rsl_stack - 1] *= _weights[_dec_stack[i]];
	}
	Backtrack();
}

void WCounter::Backjump_Decomposition( unsigned num_kept_levels )
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

void WCounter::Iterate_Known( BigFloat cached_result )
{
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), cached_result );
	}
	_rsl_stack[_num_rsl_stack++] = cached_result;
	_active_comps[_num_levels - 1]++;
}

void WCounter::Backtrack_Decomposition2Decision()
{
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_rsl_stack[_num_rsl_stack - 1] *= _weights[_dec_stack[i]];
	}
	Backtrack();
}

void WCounter::Iterate_Decision()
{
	assert( _num_rsl_stack > 1 );
	assert( _rsl_stack[_num_rsl_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( _rsl_stack[_num_rsl_stack - 1] == 0 );  /// NOTE: conflict can come from the upper levels
	Literal decision = _dec_stack[_num_dec_stack];
//	cerr << _rsl_stack[_num_rsl_stack - 2] << " vs " << _rsl_stack[_num_rsl_stack - 1] << endl;  // ToRemove
	_num_rsl_stack--;
	_rsl_stack[_num_rsl_stack] *= _weights[decision];
	_rsl_stack[_num_rsl_stack - 1] *= _weights[~decision];
	_rsl_stack[_num_rsl_stack - 1] += _rsl_stack[_num_rsl_stack];
	if ( !incomplete && debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Component(), _rsl_stack[_num_rsl_stack - 1] );
	}
	if ( !incomplete ) _component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	_active_comps[_num_levels - 1]++;
}

void WCounter::Backtrack_Decomposition()
{
	_num_rsl_stack -= Num_Components_On_Current_Level();
	assert( _num_levels > 2 );  // not decompose the initial formula
	_rsl_stack[_num_rsl_stack] *= _rsl_stack[_num_rsl_stack + 1];
	for ( unsigned i = 2; i < Num_Components_On_Current_Level(); i++ ) {
		_rsl_stack[_num_rsl_stack] *= _rsl_stack[_num_rsl_stack + i];
	}
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_rsl_stack[_num_rsl_stack] *= _weights[_dec_stack[i]];
	}
	_num_rsl_stack++;
	Backtrack();
}

void WCounter::Count_With_SAT_Imp_Computing()
{
	StopWatch tmp_watch;
	Variable var;
    BigFloat cached_result;
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
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
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
					Iterate_Decision();
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

bool WCounter::Try_Shift_To_Implicite_BCP()
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
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
	return true;
}

bool WCounter::Estimate_Hardness( Component & comp )
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

void WCounter::Compute_Second_Var_Order_Automatical( Component & comp )
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

BigFloat WCounter::Count_Models( WCNF_Formula & cnf, vector<Model *> & models, double timeout )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
	}
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	_models_stack[0] = models;
	models.clear();
	bool cnf_sat;
	if ( !running_options.detect_AND_gates ) cnf_sat = Preprocess( cnf, _models_stack[0] );
	else cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	_normalized_factor = Normalize_Weights( cnf.Weights(), _weights );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigFloat count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		return count;
	}
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( AutomaticalHeur );
	else Choose_Running_Options_Static( AutomaticalHeur );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Count_With_Implicite_BCP();  // ToModify
	}
	else Count_With_SAT_Imp_Computing( timeout );
	BigFloat count;
	if ( _num_rsl_stack == 1 ) count = Backtrack_Init();
	else count = Backtrack_Failure();
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
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
		BigFloat verified_count = Count_Verified_Models_c2d( cnf );
		cout << verified_count << endl;
		cerr << count << " vs " << verified_count << endl;
		BigFloat ub = verified_count;
		ub *= 1.0001;
		BigFloat lb = verified_count;
		lb /= 1.0001;
		assert ( lb < count && count < ub );
	}
	return count;
}

void WCounter::Count_With_Implicite_BCP( double timeout )
{
	StopWatch stop_watch;
	stop_watch.Start();
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigFloat cached_result;
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

void WCounter::Terminate_Counting()
{
	_num_rsl_stack = 0;
	while ( _num_levels > 1 ) {
		Recycle_Models( _models_stack[_num_levels - 1] );
		Backtrack();
	}
}

void WCounter::Count_With_SAT_Imp_Computing( double timeout )
{
	StopWatch stop_watch, tmp_watch;
	stop_watch.Start();
	Variable var;
    BigFloat cached_result;
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
					if ( cached_result != _component_cache.Default_Caching_Value() ) {  // no backjump
						Iterate_Known( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
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
					Iterate_Decision();
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

bool WCounter::Try_Shift_To_Implicite_BCP( double timeout )
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
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
	return true;
}

BigFloat WCounter::Backtrack_Failure()
{
	assert( _num_rsl_stack == 0 );
	Backtrack();
	return _component_cache.Default_Caching_Value();
}

void WCounter::Verify_Result_Component( Component & comp, BigFloat count )
{
	WCNF_Formula * cnf = Output_Renamed_Clauses_In_Component( comp, _weights );
	BigFloat verified_count = Count_Verified_Models_c2d( *cnf );
	BigFloat ub = verified_count;
	ub *= 1.0001;
	BigFloat lb = verified_count;
	lb /= 1.0001;
	if ( count < lb || count > ub ) {
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

void WCounter::Display_Result_Stack( ostream & out )
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

void WCounter::Display_Statistics( unsigned option )
{
	switch ( option ) {
		case 0:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 1:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time compute tree decomposition: " << statistics.time_tree_decomposition << endl;
			if ( running_options.imp_strategy == SAT_Imp_Computing ) cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			else cout << running_options.display_prefix << "time IBCP: " << statistics.time_ibcp << endl;
			cout << running_options.display_prefix << "time dynamic decomposition: " << statistics.time_dynamic_decompose << " (" << statistics.time_dynamic_decompose_sort << " sorting)" << endl;
			cout << running_options.display_prefix << "time cnf cache: " << statistics.time_gen_cnf_cache << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 10:  // sharpSAT
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			break;
		default:
			cerr << "ERROR[WCounter]: this display mode is not existing!" << endl;
			assert( false );
			exit( 0 );
	}
	statistics.Init_Compiler();
}

void WCounter::Display_Memory_Status( ostream & out )
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

bool WCounter::Is_Memory_Exhausted()
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
