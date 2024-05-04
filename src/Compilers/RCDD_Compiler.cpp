#include "RCDD_Compiler.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


RCDD_Compiler::RCDD_Compiler()
{
}

RCDD_Compiler::~RCDD_Compiler()
{
	Free_Auxiliary_Memory();
}

void RCDD_Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler();
		return;
	}
	if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	CDD_Compiler::Allocate_and_Init_Auxiliary_Memory( max_var );
}

void RCDD_Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
}

void RCDD_Compiler::Reset()
{
	CDD_Compiler::Reset();
}

CDDiagram RCDD_Compiler::Compile( RCDD_Manager & manager, CNF_Formula & cnf, Heuristic heur, Chain & vorder )
{
	assert( Is_Linear_Ordering( heur ) );
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Compiling..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	bool cnf_sat = Preprocess( cnf, _models_stack[0] );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
				cout << running_options.display_prefix << "Number of edges: " << 0 << endl;
				cout << running_options.display_prefix << "Number of models: " << 0 << endl;
			}
		}
		Reset();
		return manager.Generate_CCDD( NodeID::bot );
	}
	Store_Lit_Equivalences( _call_stack[0] );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		NodeID result = Make_Root_Node( manager, NodeID::top );
		Un_BCP( _dec_offsets[--_num_levels] );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
				Display_Result_Statistics( cout, manager, result );
			}
		}
		Reset();
		return manager.Generate_CCDD( result );
	}
	Gather_Infor_For_Counting();
	Choose_Running_Options( heur, vorder );
	if ( heur != FixedLinearOrder ) Reorder_Manager( manager );
	Set_Current_Level_Kernelized( true );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Compile_With_Implicite_BCP( manager );
	}
	else {
		_lit_equivalency.Reorder( _var_order );
		Encode_Long_Clauses();
		if ( true ) Compile_With_SAT_Imp_Computing( manager );
		else Compile_Layered_Kernelization( manager );
	}
	_num_rsl_stack--;
//	ofstream fout( "debug.cdd" );  // ToRemove
//	manager.Display_Stat( fout );  // ToRemove
//	fout.close();
	NodeID result = Make_Root_Node( manager, _rsl_stack[0] );
	Set_Current_Level_Kernelized( false );
	Backtrack();
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_compiling >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Memory_Status( cout );
			Display_Result_Statistics( cout, manager, result );
		}
	}
	Reset();
	if ( debug_options.verify_compilation ) {
//		manager.Display_Stat( cout );  // ToRemove
		manager.Verify_RCDD( result );
		manager.Verify_Entail_CNF( result, cnf );
		BigInt count = manager.Count_Models( result );
		BigInt verified_count = Count_Verified_Models_sharpSAT( cnf );
		assert( count == verified_count );
	}
	return manager.Generate_CCDD( result );
}

NodeID RCDD_Compiler::Make_Root_Node( RCDD_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	node = Make_Kernelized_Conjunction_Node( manager, node );
	_cdd_rnode.sym = CDD_SYMBOL_DECOMPOSE;
	_cdd_rnode.ch[0] = node;
	_cdd_rnode.ch_size = ( node != NodeID::top );
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		_cdd_rnode.ch[_cdd_rnode.ch_size++] = NodeID::literal( _dec_stack[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _cdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

NodeID RCDD_Compiler::Make_Kernelized_Conjunction_Node( RCDD_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_cdd_rnode.sym = CDD_SYMBOL_KERNELIZE;
	_cdd_rnode.ch[0] = node;
	_cdd_rnode.ch_size = manager.Add_Equivalence_Nodes( _call_stack[_num_levels - 1].Lit_Equivalences(), _cdd_rnode.ch + 1 );
	_cdd_rnode.ch_size++;
	if ( _cdd_rnode.ch_size > 1 ) node = manager.Add_Kernelization_Node( _cdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return node;
}

void RCDD_Compiler::Choose_Running_Options( Heuristic heur, Chain & vorder )
{
	running_options.var_ordering_heur = heur;
	switch ( running_options.var_ordering_heur ) {
	case AutomaticalHeur:
		Compute_Var_Order_Automatical();
		break;
	case minfill:
		Compute_Var_Order_Min_Fill_Heuristic_Opt();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The minfill treewidth: " << running_options.treewidth << endl;
		break;
	case FixedLinearOrder:
		_var_order = vorder;
		Rename_Clauses_Fixed_Ordering();
		break;
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	default:
		cerr << "ERROR[RCDD_Compiler]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
}

void RCDD_Compiler::Compute_Var_Order_Automatical()
{
	const unsigned treewidth_bound = _unsimplifiable_num_vars / 4;
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

void RCDD_Compiler::Choose_Implicate_Computing_Strategy()
{
	assert( running_options.imp_strategy == Automatical_Imp_Computing );
	if ( running_options.var_ordering_heur == minfill ) {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP;
		else if ( running_options.treewidth <= 72 ) running_options.imp_strategy = Partial_Implicit_BCP;
		else if ( running_options.treewidth <= _unsimplifiable_num_vars / 128 ) running_options.imp_strategy = Partial_Implicit_BCP;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	else {
		if ( Hyperscale_Problem() ) running_options.imp_strategy = Partial_Implicit_BCP;
		else running_options.imp_strategy = SAT_Imp_Computing;
	}
	running_options.sat_employ_external_solver_always = false;
}

void RCDD_Compiler::Reorder_Manager( RCDD_Manager & manager )
{
	Chain new_order;
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		if ( Variable::start <= _var_order[i] && _var_order[i] <= _max_var ) {
			new_order.Append( _var_order[i] );
		}
	}
	manager.Reorder( new_order );
}

void RCDD_Compiler::Compile_With_Implicite_BCP( RCDD_Manager & manager )
{
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	NodeID cached_result;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	while ( _num_levels >= old_num_levels ) {
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
				backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					Backjump_Decision( backjump_level );
					_rsl_stack[_num_rsl_stack++] = NodeID::bot;  /// NOTE: cannot omit when in high decision, and need to be AFTER backjump
					break;
				}
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, NodeID::top );
					Backtrack();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						if ( debug_options.verify_component_compilation ) {
							Verify_Result_Component( Current_Component(), manager, cached_result );
						}
						_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, cached_result );
						Backtrack();
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				var = Pick_Good_Var_Linearly_Component( Current_Component() );
				Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				if ( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot ) {
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
				assert( _num_rsl_stack > 1 );
//				manager.Display( cerr );  // ToRemove
				_num_rsl_stack--;
				_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );
				if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );  // NOTE: _dec_offsets[_num_levels - 1] is equal to the number of initial implied literals
				Backtrack();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  /// NOTE: backjump makes that there are unknown cacheable component
						if ( debug_options.verify_component_compilation ) {
							Verify_Result_Component( Current_Component(), manager, cached_result );
						}
						_rsl_stack[_num_rsl_stack++] = cached_result;
						_active_comps[_num_levels - 1]++;
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Pick_Good_Var_Linearly_Component( Current_Component() );
						Extend_New_Level();
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					if ( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot ) {
						Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_rsl_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
						backjump_reason = Get_Approx_Imp_Component( Current_Component(), backjump_level );  /// current component rather than parent component
						if ( backjump_reason != Reason::undef ) {
							Backjump_Decomposition( backjump_level );
							_rsl_stack[_num_rsl_stack++] = NodeID::bot;  /// NOTE: cannot omit when in high decision, and need to be AFTER backjump
							break;
						}
						unsigned num_comp = Dynamic_Decompose_Component( Current_Component(), _comp_stack + _num_comp_stack );
						_num_comp_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Component() = _comp_stack[_num_comp_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							_rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );  // overwrite the result of the only one component
							Backtrack();
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_comps[_num_levels - 1] == _num_comp_stack - 1 );
							cached_result = Component_Cache_Map( Current_Component() );  /// NOTE: the current component was after the collapsed one
							if ( cached_result != NodeID::undef ) {  /// NOTE: backjump makes that there are unknown cacheable component
								if ( debug_options.verify_component_compilation ) {
									Verify_Result_Component( Current_Component(), manager, cached_result );
								}
								_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, cached_result );
								Backtrack();
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					assert( _num_rsl_stack > 1 );
					_num_rsl_stack--;
					_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );  // NOTE: there exists no implied literal
					_active_comps[_num_levels - 1]++;
					break;
				}
			}
			else {  // all components are already processed
				_num_rsl_stack -= Num_Components_On_Current_Level();
				assert( _num_levels > 2 );  // not decompose the initial formula
//				manager.Display( cerr );  // ToRemove
				_rsl_stack[_num_rsl_stack] = Make_Node_With_Imp( manager, _rsl_stack + _num_rsl_stack, Num_Components_On_Current_Level() );
				_num_rsl_stack++;
				Backtrack();
			}
		}
	}
	assert( _num_levels == old_num_levels - 1 && _num_rsl_stack == old_num_rsl_stack + 1 );
}

NodeID RCDD_Compiler::Make_Node_With_Imp( RCDD_Manager & manager, NodeID node  )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_cdd_rnode.sym = CDD_SYMBOL_DECOMPOSE;
	_cdd_rnode.ch[0] = node;
	_cdd_rnode.ch_size = ( node != NodeID::top );
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_cdd_rnode.ch[_cdd_rnode.ch_size++] = NodeID::literal( _dec_stack[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _cdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

NodeID RCDD_Compiler::Make_Decision_Node( RCDD_Manager & manager, NodeID low, NodeID high )
{
//	Debug_Print_Visit_Number( cerr, __FUNCTION__, __LINE__ );  // ToRemove
	StopWatch begin_watch;
	assert( low != NodeID::bot );  // backjump guarantees this
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Decision_Node bnode( _dec_stack[_num_dec_stack].Var(), low, high );
	NodeID result = manager.Add_Decision_Node( bnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	if ( high != NodeID::bot && debug_options.verify_component_compilation ) {
		Verify_Result_Component( Current_Component(), manager, result );
	}
	if ( high != NodeID::bot ) _component_cache.Write_Result( Current_Component().caching_loc, result );
	const size_t GB = 1024 * 1024 * 1024;
	if ( _component_cache.Memory() > running_options.max_memory / 4 * GB ) {
		Component_Cache_Clear();
	}
	if ( manager.Num_Nodes() >= running_options.removing_redundant_nodes_trigger ) {
		if ( high == NodeID::bot ) _rsl_stack[_num_rsl_stack++] = result;
		Remove_Redundant_Nodes( manager );
		if ( high == NodeID::bot ) result = _rsl_stack[--_num_rsl_stack];
		else result = _component_cache.Read_Result( Current_Component().caching_loc );
	}
	return result;
}

NodeID RCDD_Compiler::Make_Node_With_Imp( RCDD_Manager & manager, NodeID * nodes, unsigned num )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	unsigned i;
	_cdd_rnode.sym = CDD_SYMBOL_DECOMPOSE;
	_cdd_rnode.ch_size = 0;
	for ( i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_cdd_rnode.Add_Child( NodeID::literal( _dec_stack[i] ) );
	}
	for ( i = 0; i < num; i++ ) {
		_cdd_rnode.Add_Child( nodes[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _cdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void RCDD_Compiler::Compile_With_SAT_Imp_Computing( RCDD_Manager & manager )
{
	StopWatch tmp_watch;
	Variable var;
	NodeID cached_result;
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
					_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, NodeID::top );
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack();
				}
				else if ( Is_Current_Level_Decision() ) {
					if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  // no backjump
						if ( debug_options.verify_component_compilation ) {
							Verify_Result_Component( Current_Component(), manager, cached_result );
						}
//						Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
						_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, cached_result );
//						Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
						Recycle_Models( _models_stack[_num_levels - 1] );
						Backtrack();
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				if ( Try_Shift_To_Implicite_BCP( manager ) ) break;
				_state_stack[_num_levels - 1]++;
				if ( Try_Kernelization( manager ) == lbool::unknown ) break;
				var = Pick_Good_Var_Linearly_Component( Current_Component() );
				Extend_New_Level();
				Pick_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
				Assign( Literal( var, false ) );
				break;
			case 2:
				assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
				_state_stack[_num_levels - 1]++;
				Extend_New_Level();
				Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
				Assign( ~_dec_stack[_num_dec_stack] );
				break;
			case 3:
				assert( _models_stack[_num_levels - 1].empty() );
				assert( _num_rsl_stack > 1 );
				_num_rsl_stack--;
				_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				Leave_Kernelization( manager );
				if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );  // NOTE: _dec_offsets[_num_levels - 1] is equal to the number of initial implied literals
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				Backtrack();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  // no backjump
						if ( debug_options.verify_component_compilation ) {
							Verify_Result_Component( Current_Component(), manager, cached_result );
						}
						_rsl_stack[_num_rsl_stack++] = cached_result;
						_active_comps[_num_levels - 1]++;
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						if ( Try_Kernelization( manager ) == lbool::unknown ) break;
						var = Pick_Good_Var_Linearly_Component( Current_Component() );
						Extend_New_Level();
						Inherit_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
					Extend_New_Level();
					Inherit_Models( _models_stack[_num_levels - 2], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels - 1] );
					Assign( ~_dec_stack[_num_dec_stack] );
					break;
				case 2:
					assert( _num_rsl_stack > 1 );
					_num_rsl_stack--;
					_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );  // NOTE: there exist no implied literals
					assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
					Leave_Kernelization( manager );
					_active_comps[_num_levels - 1]++;
					break;
				}
			}
			else {  // all components are already processed
				_num_rsl_stack -= Num_Components_On_Current_Level();
				assert( _num_levels > 2 );  // not decompose the initial formula
//				manager.Display_Stat( cerr );  // ToRemove
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				_rsl_stack[_num_rsl_stack] = Make_Node_With_Imp( manager, _rsl_stack + _num_rsl_stack, Num_Components_On_Current_Level() );
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				_num_rsl_stack++;
				Recycle_Models( _models_stack[_num_levels - 1] );
				Backtrack();
			}
		}
	}
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

bool RCDD_Compiler::Try_Shift_To_Implicite_BCP( RCDD_Manager & manager )
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
	running_options.imp_strategy = Partial_Implicit_BCP;
	Recycle_Models( _models_stack[_num_levels - 1] );
	Compile_With_Implicite_BCP( manager );
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) system( "./pause" );  // ToRemove
	running_options.imp_strategy = SAT_Imp_Computing;
	return true;
}

bool RCDD_Compiler::Estimate_Hardness( Component & comp )
{
	if ( false ) {
		unsigned density = 0;
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
			density += clause.Size() * Log_Ceil( clause.Size() );
		}
		cerr << comp.Vars_Size() << ": " << density << endl;  // ToRemove
		return density / comp.Vars_Size() >= 8;
	}
}

lbool RCDD_Compiler::Try_Kernelization( RCDD_Manager & manager )
{
	if ( _current_kdepth >= running_options.max_kdepth || Estimate_Kernelization_Effect() == false ) return lbool(false);
	Store_Cached_Binary_Clauses();
	Kernelize_Without_Imp();
	Set_Current_Level_Kernelized( true );
	Sort_Clauses_For_Caching();
	NodeID cached_result;
	if ( Current_Component().Vars_Size() == 0 ) cached_result = NodeID::top;
	else cached_result = Component_Cache_Map( Current_Component() );
	if ( cached_result != NodeID::undef ) {
		if ( debug_options.verify_component_compilation ) {
			Verify_Result_Component( Current_Component(), manager, cached_result );
		}
		if ( Is_Current_Level_Decision() ) {
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			_rsl_stack[_num_rsl_stack++] = cached_result;
			Leave_Kernelization( manager );
			_rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			Recycle_Models( _models_stack[_num_levels - 1] );
			Backtrack();
		}
		else {
			_rsl_stack[_num_rsl_stack++] = cached_result;
			Leave_Kernelization( manager );
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

bool RCDD_Compiler::Estimate_Kernelization_Effect()
{
	if ( false ) {
		if ( _num_levels > 2 ) return true;  // ToModify
		else return false;
	}
	else if ( _current_kdepth + 1 < running_options.max_kdepth ) {
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step );
	}
	else  {
		if ( Current_Component().Vars_Size() > running_options.trivial_variable_bound * 2 ) return false;
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step );
	}
}

bool RCDD_Compiler::Estimate_Kernelization_Effect_Enough_Decisions( unsigned step )
{
	unsigned last_level = Search_Last_Kernelizition_Level();
	unsigned num_decisions = _num_dec_stack - _dec_offsets[last_level + 1];
	unsigned num_levels = _num_levels - last_level - 1;
	if ( running_options.display_kernelizing_process ) {
		cout << running_options.display_prefix << "" << last_level + 1 << " -> " << _num_levels - 1 << " (" << num_decisions << ")" << endl;
	}
	return num_decisions > step && num_levels < num_decisions / 3;
}

void RCDD_Compiler::Leave_Kernelization( RCDD_Manager & manager )
{
	if ( !_call_stack[_num_levels - 1].Existed() ) return;
	_rsl_stack[_num_rsl_stack - 1] = Make_Kernelized_Conjunction_Node( manager, _rsl_stack[_num_rsl_stack - 1] );
	Clear_Cached_Binary_Clauses();
	Set_Current_Level_Kernelized( false );
	Cancel_Kernelization_Without_Imp();
	Recover_Cached_Binary_Clauses();
	Encode_Long_Clauses();
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
}

void RCDD_Compiler::Compile_Layered_Kernelization( RCDD_Manager & manager )
{
	assert( _input_frames.empty() );
	Search_Graph<NodeID> graph( _max_var, _component_cache );
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Layered Kernelization......" << endl;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	const unsigned loc = 2;
	Construct_Search_Graph( graph, Variable( _var_order[loc] ) );  // _current_kdepth == 0 after employment
//	graph.Display( cerr );  // ToRemove
	vector<NodeID> roots( _input_frames.size(), NodeID::undef );
	if ( _input_frames.empty() ) {
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Done." << endl;
		Make_Nodes_With_Search_Graph( manager, graph, roots );
		return;
	}
	Batch_Preprocess();
	if ( true ) {
		_var_order.Shrink( loc + 1 );
		Update_Var_Order_Automatical();
		manager.Reorder( _var_order );
	}
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Done." << endl;
	for ( unsigned i = 0; i < _input_frames.size(); i++ ) {
		if ( !_input_frames[i].Existed() ) {
			roots[i] = NodeID::bot;
			continue;
		}
		Load_Frame( _input_frames[i] );
		Extend_New_Level();  // NOTE: Without this line, the _var_stamps of init implied literals will be UNSIGNED_UNDEF
		if ( Non_Unary_Clauses_Empty() ) {
			Recycle_Models( _models_stack[0] );
			roots[i] = Make_Root_Node( manager, NodeID::top );
			Un_BCP( _dec_offsets[--_num_levels] );
			Preprocessor::Reset();
			continue;
		}
		Sort_Long_Clauses_By_IDs();
		Gather_Infor_For_SAT();
		_fixed_num_vars = _unary_clauses.size() + _call_stack[0].Lit_Equivalences().size() / 2;
//		Display_Clauses( cerr, true );  // ToRemove
//		Display_Watched_List( cerr );  // ToRemove
//		cerr << "cache size: " << _component_cache.Size() << endl;  // ToRemove
		Gather_Infor_For_Counting();
		Set_Current_Level_Kernelized( true );
		if ( Create_Init_Level() ) {
			Compile_With_SAT_Imp_Computing( manager );
		}
		_num_rsl_stack--;
		roots[i] = Make_Root_Node( manager, _rsl_stack[0] );
		Set_Current_Level_Kernelized( false );
		Backtrack();
		if ( debug_options.verify_compilation ) {
//			if ( i == 4 ) Display_Processed_Clauses( cerr, true );  // ToRemove
//			if ( i == 4 ) manager.Display_CDD( cerr, roots[i] );  // ToRemove
			manager.Verify_RCDD( roots[i] );
			CNF_Formula * cnf = Output_Processed_Clauses();
			NodeID node = roots[i];
			if ( manager.Node( node ).sym == CDD_SYMBOL_KERNELIZE ) {
				node = manager.Node( node ).ch[0];
			}
			manager.Verify_Entail_CNF( node, *cnf );
			BigInt count = manager.Count_Models( node );
			BigInt verified_count = Count_Verified_Models_sharpSAT( *cnf );
			if ( count != verified_count ) {
				cerr << count << " vs " << verified_count << " (verified)" << endl;
				assert( count == verified_count );
			}
			delete cnf;
		}
		Clear_Membership_Lists_Subdivision_Component( _comp_stack[0] );
		Preprocessor::Reset();
	}
	_input_frames.clear();
	Make_Nodes_With_Search_Graph( manager, graph, roots );
}

void RCDD_Compiler::Construct_Search_Graph( Search_Graph<NodeID> & graph, Variable upper_bound )
{
	Variable var;
	NodeID cached_result;
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
					_rsl_stack[_num_rsl_stack++] = Search_Node_With_Imp( graph, NodeID::top );
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  // no backjump
//						Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
						_rsl_stack[_num_rsl_stack++] = Search_Node_With_Imp( graph, cached_result );
//						Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
						Recycle_Models( _models_stack[_num_levels - 1] );
						Backtrack();
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				var = Try_Demarcation( graph, upper_bound );
				if ( var == Variable::undef ) break;
				Extend_New_Level();
				Pick_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
				Assign( Literal( var, false ) );
				break;
			case 2:
				assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
				_state_stack[_num_levels - 1]++;
				Extend_New_Level();
				Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
				Assign( ~_dec_stack[_num_dec_stack] );
				break;
			case 3:
				assert( _models_stack[_num_levels - 1].empty() );
				assert( _num_rsl_stack > 1 );
				_num_rsl_stack--;
				_rsl_stack[_num_rsl_stack - 1] = Search_Decision_Node( graph, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack - 1] = Search_Node_With_Imp( graph, _rsl_stack[_num_rsl_stack - 1] );  // NOTE: _dec_offsets[_num_levels - 1] is equal to the number of initial implied literals
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				Backtrack();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  // no backjump
						_rsl_stack[_num_rsl_stack++] = cached_result;
						_active_comps[_num_levels - 1]++;
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Try_Demarcation( graph, upper_bound );
						if ( var == Variable::undef ) break;
						Extend_New_Level();
						Inherit_Models( _models_stack[_num_levels - 2], Literal( var, false ), _models_stack[_num_levels - 1] );
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
					Extend_New_Level();
					Inherit_Models( _models_stack[_num_levels - 2], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels - 1] );
					Assign( ~_dec_stack[_num_dec_stack] );
					break;
				case 2:
					assert( _num_rsl_stack > 1 );
					_num_rsl_stack--;
					_rsl_stack[_num_rsl_stack - 1] = Search_Decision_Node( graph, _rsl_stack[_num_rsl_stack - 1], _rsl_stack[_num_rsl_stack] );  // NOTE: there exist no implied literals
					assert( _rsl_stack[_num_rsl_stack - 1] != NodeID::bot );
					_active_comps[_num_levels - 1]++;
					break;
				}
			}
			else {  // all components are already processed
				_num_rsl_stack -= Num_Components_On_Current_Level();
				assert( _num_levels > 2 );  // not decompose the initial formula
//				manager.Display_Stat( cerr );  // ToRemove
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				_rsl_stack[_num_rsl_stack] = Search_Node_With_Imp( graph, _rsl_stack + _num_rsl_stack, Num_Components_On_Current_Level() );
//				Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
				_num_rsl_stack++;
				Recycle_Models( _models_stack[_num_levels - 1] );
				Backtrack();
			}
		}
	}
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
	_num_rsl_stack--;
	Search_Root_Node( graph, _rsl_stack[0] );
	Set_Current_Level_Kernelized( false );
	_current_kdepth++;  // recover for parent-call
	Backtrack();
	Clear_Membership_Lists_Subdivision_Component( _comp_stack[0] );
	Preprocessor::Reset();
}

Variable RCDD_Compiler::Try_Demarcation( Search_Graph<NodeID> & graph, Variable upper_bound )
{
	Variable var = Pick_Good_Var_Linearly_Component( Current_Component() );
	if ( _var_order.Less_Than( upper_bound, var ) ) {
		_input_frames.push_back( Stack_Frame() );
		_input_frames.back();
		Store_Active_Clauses_Component( _input_frames.back(), Current_Component() );
		_rsl_stack[_num_rsl_stack++] = graph.Push_Unknown_Node();
		if ( Is_Current_Level_Decision() ) {
			_rsl_stack[_num_rsl_stack - 1] = Search_Node_With_Imp( graph, _rsl_stack[_num_rsl_stack - 1] );
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			_input_frames.back().Swap_Models( _models_stack[_num_levels - 1] );
			Backtrack();
		}
		else {
			Copy_Models( _models_stack[_num_levels - 1], _models_stack[_num_levels] );
			_input_frames.back().Swap_Models( _models_stack[_num_levels] );
			_active_comps[_num_levels - 1]++;
			_state_stack[_num_levels - 1] += 2;
		}
		return Variable::undef;
	}
	return var;
}

void RCDD_Compiler::Update_Var_Order_Automatical()
{
	const unsigned treewidth_bound = _unsimplifiable_num_vars / 4;
	Compute_Var_Order_Min_Fill_Heuristic_Bound( treewidth_bound );
	if ( running_options.var_ordering_heur == minfill ) {
		Update_Var_Order_Min_Fill_Heuristic();
	}
	else {
		assert( running_options.var_ordering_heur == LinearLRW );
		Update_Var_Order_Single_Cluster();
	}
}

void RCDD_Compiler::Update_Var_Order_Min_Fill_Heuristic()
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	double * var_weight = new double [_max_var + 1];
	Greedy_Graph * pg = Create_Weighted_Primal_Graph_Frames( var_weight );
	Simple_TreeD treed( *pg, NumVars( _max_var ), true );  /// optimized for large-scale problems
	running_options.treewidth = treed.Width();
	Generate_Var_Order_From_TreeD( treed, var_weight );
	delete pg;
	delete [] var_weight;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition = begin_watch.Get_Elapsed_Seconds();
}

Greedy_Graph * RCDD_Compiler::Create_Weighted_Primal_Graph_Frames( double * var_weight )
{
	vector<vector<unsigned>> edges( _max_var + 1 );
	vector<double> scores( 2 * _max_var + 2, 0 );
	for ( unsigned ii = 0; ii < _input_frames.size(); ii++ ) {
		Stack_Frame & frame = _input_frames[ii];
		for ( unsigned j = 0; j < frame.Binary_Clauses_Size(); j++ ) {
			Literal lit = frame.Binary_Clauses_First( j );
			Literal lit2 = frame.Binary_Clauses_Second( j );
            edges[lit.Var()].push_back( lit2.Var() );
            edges[lit2.Var()].push_back( lit.Var() );
            scores[lit] += 2;
            scores[lit2] += 2;
		}
		for ( unsigned j = 0; j < frame.Binary_Learnts_Size(); j++ ) {
			Literal lit = frame.Binary_Learnts_First( j );
			Literal lit2 = frame.Binary_Learnts_Second( j );
            scores[lit] += 1;
            scores[lit2] += 1;
		}
		for ( unsigned j = 0; j < frame.Old_Num_Long_Clauses(); j++ ) {
			Clause clause = frame.Long_Clauses( j );
			for ( unsigned k = 0; k < clause.Size(); k++ ) {
				Literal lit = clause[k];
				unsigned kk;
				for ( kk = 0; kk < k; kk++ ) {
					edges[lit.Var()].push_back( clause[kk].Var() );
				}
				for ( kk++; kk < clause.Size(); kk++ ) {
					edges[lit.Var()].push_back( clause[kk].Var() );
				}
				scores[lit] += 1.0 / clause.Size();
			}
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned size = 0;
		for ( unsigned j = 0; j < edges[i].size(); j++ ) {
			edges[i][size] = edges[i][j];
			size += !_var_seen[edges[i][j]];
			_var_seen[edges[i][j]] = true;
		}
		edges[i].resize( size );
		for ( unsigned j = 0; j < size; j++ ) {
			_var_seen[edges[i][j]] = false;
		}
		var_weight[i] = scores[Literal( i, false )] * scores[Literal( i, true )];
	}
	return new Greedy_Graph( _max_var, edges );
}

void RCDD_Compiler::Update_Var_Order_Single_Cluster()
{
	double * var_weight = new double [_max_var + 1];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		var_weight[i] = 0;
	}
	Var_Weight_For_Tree_Decomposition_Frames( var_weight );
	SList<Variable> left_vertices;
	SList_Node<Variable> * pre = left_vertices.Head();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !Var_Appeared( i ) ) continue;
		left_vertices.Insert_After( pre, i );
		pre = pre->next;
	}
	while ( !left_vertices.Empty() ) {
		SList_Node<Variable> * chosen_pre = left_vertices.Head();
		Variable chosen_var = chosen_pre->next->data;
		for ( pre = chosen_pre->next; pre->next != nullptr; pre = pre->next ) {
			Variable var = pre->next->data;
			if ( var_weight[var] > var_weight[chosen_var] ) {
				chosen_pre = pre;
				chosen_var = var;
			}
		}
		_var_order.Append( chosen_var );
		left_vertices.Delete_After( chosen_pre );
	}
	delete [] var_weight;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_order.Contain( i ) ) {
			_var_order.Append( i );
		}
	}
	_var_order.Append( _max_var.Next() );  /// Note: I cannot remember why this line is needed, maybe in order to terminate some loop
}

void RCDD_Compiler::Var_Weight_For_Tree_Decomposition_Frames( double * var_weight )
{
	vector<double> scores( 2 * _max_var + 2, 0 );
	for ( unsigned i = 0; i < _input_frames.size(); i++ ) {
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			scores[Literal( x, false )] = 0;
			scores[Literal( x, true )] = 0;
		}
		Stack_Frame & frame = _input_frames[i];
		for ( unsigned j = 0; j < frame.Binary_Clauses_Size(); j++ ) {
			Literal lit = frame.Binary_Clauses_First( j );
			Literal lit2 = frame.Binary_Clauses_Second( j );
            scores[lit] += 2;
            scores[lit2] += 2;
		}
		for ( unsigned j = 0; j < frame.Binary_Learnts_Size(); j++ ) {
			Literal lit = frame.Binary_Learnts_First( j );
			Literal lit2 = frame.Binary_Learnts_Second( j );
            scores[lit] += 1;
            scores[lit2] += 1;
		}
		for ( unsigned j = 0; j < frame.Old_Num_Long_Clauses(); j++ ) {
			Clause clause = frame.Long_Clauses( j );
			for ( unsigned k = 0; k < clause.Size(); k++ ) {
				scores[clause[k]] += 1.0 / clause.Size();
			}
		}
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			var_weight[x] += scores[Literal( x, false )] * scores[Literal( x, true )];  // prefer old ordering
		}
	}
}

void RCDD_Compiler::Make_Nodes_With_Search_Graph( RCDD_Manager & manager, Search_Graph<NodeID> & graph, vector<NodeID> & known_nodes )
{
	assert( _num_levels == 0 && _num_rsl_stack == 0 );
	Decision_Manager::Extend_New_Level();
	NodeID root = graph._nodes.size() - 1;
	Search_Node & rootn = graph._nodes[root];
	assert( rootn.ch_size == 1 );
	for ( unsigned i = 0; i < rootn.imp_size; i++ ) {
		Assign( rootn.imp[i] );
	}
	unsigned index = 0;
	graph._path[0] = rootn.ch[0];
	graph._path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = graph._path[path_len - 1];
		Search_Node & topn = graph._nodes[top];
		unsigned ch_size;
		if ( topn.sym <= _max_var ) ch_size = 2;
		else if ( topn.sym == SEARCH_KNOWN ) ch_size = 0;
		else ch_size = topn.ch_size;
		if ( graph._path_mark[path_len - 1] < ch_size ) {
			NodeID child = topn.ch[graph._path_mark[path_len - 1]];
			Search_Node & childn = graph._nodes[child];
			graph._path_mark[path_len - 1]++;  // path_len will change in the following statement
			if ( childn.infor.mark == UNSIGNED_UNDEF ) {
				graph._path[path_len] = child;
				graph._path_mark[path_len++] = 0;
			}
		}
		else {
			if ( topn.sym == SEARCH_KNOWN ) topn.infor.mark = topn.ch[0];
			else if ( topn.sym == SEARCH_UNKNOWN ) topn.infor.mark = known_nodes[index++];
			else Make_Node_With_Search_Graph( manager, graph, topn );
			path_len--;
		}
	}
	assert( index == known_nodes.size() );
	_rsl_stack[_num_rsl_stack++] = graph._nodes[rootn.ch[0]].infor.mark;
}

void RCDD_Compiler::Make_Node_With_Search_Graph( RCDD_Manager & manager, Search_Graph<NodeID> & graph, Search_Node & snode )
{
//	Debug_Print_Visit_Number( cerr, __FUNCTION__, __LINE__ );  // ToRemove
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	switch ( snode.sym ) {
	case SEARCH_CONFLICTED:
		snode.infor.mark = NodeID::bot;
		break;
	case SEARCH_EMPTY:
		snode.infor.mark = NodeID::top;
		break;
	case SEARCH_DECOMPOSED:
		_cdd_rnode.sym = CDD_SYMBOL_DECOMPOSE;
		_cdd_rnode.ch_size = 0;
		for ( unsigned i = 0; i < snode.imp_size; i++ ) {
			_cdd_rnode.Add_Child( NodeID::literal( snode.imp[i] ) );
		}
		for ( unsigned i = 0; i < snode.ch_size; i++ ) {
			_cdd_rnode.Add_Child( graph._nodes[snode.ch[i]].infor.mark );
		}
		snode.infor.mark = manager.Add_Decomposition_Node( _cdd_rnode );
		break;
	case SEARCH_KERNELIZED:
		_cdd_rnode.sym = CDD_SYMBOL_KERNELIZE;
		_cdd_rnode.ch[0] = graph._nodes[snode.ch[0]].infor.mark;
		_cdd_rnode.ch_size = manager.Add_Equivalence_Nodes( snode.imp, snode.imp_size / 2, _cdd_rnode.ch + 1 );
		_cdd_rnode.ch_size++;
		snode.infor.mark = manager.Add_Kernelization_Node( _cdd_rnode );
		break;
	default:
		NodeID low = graph._nodes[snode.ch[0]].infor.mark, high = graph._nodes[snode.ch[1]].infor.mark;
		Decision_Node bnode( snode.sym, low, high );
		snode.infor.mark = manager.Add_Decision_Node( bnode );
		assert( snode.caching_loc < _component_cache.Size() );
		_component_cache.Write_Result( snode.caching_loc, snode.infor.mark );
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
}

void RCDD_Compiler::Verify_Result_Component( Component & comp, RCDD_Manager & manager, NodeID result )
{
	CNF_Formula * cnf = Output_Original_Clauses_In_Component( comp );
	manager.Verify_RCDD( result );
	BigInt count = manager.Count_Models( result );
	BigInt verified_count = Count_Verified_Models_sharpSAT( *cnf );
	BigInt tmp_count = count;  // ToRemove
	tmp_count.Div_2exp( _num_dec_stack );
	if ( verified_count != count ) {
		manager.Display_CDD( cerr, manager.Generate_CCDD( result ) );  // ToRemove
		cerr << "NodeID: " << result << endl;
		comp.Display( cerr );
		Display_Decision_Stack( cerr, _num_levels - 1 );
		cerr << *cnf;
		cerr << "Count: " << count << endl;
		cerr << "Verified count: " << verified_count << endl;
		assert( verified_count == count );
	}
	delete cnf;
}


}
