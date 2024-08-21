#include "R2D2_Compiler.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


R2D2_Compiler::R2D2_Compiler()
{
}

R2D2_Compiler::~R2D2_Compiler()
{
	Free_Auxiliary_Memory();
}

void R2D2_Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
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

void R2D2_Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
}

void R2D2_Compiler::Reset()
{
	CDD_Compiler::Reset();
}

size_t R2D2_Compiler::Memory()
{
	return CDD_Compiler::Memory();
}

CDDiagram R2D2_Compiler::Compile( R2D2_Manager & manager, CNF_Formula & cnf, Heuristic heur, Chain & vorder )
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
		_call_stack[0].Clear_Lit_Equivalences();
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
		Compile_With_SAT_Imp_Computing( manager );
	}
	_num_rsl_stack--;
//	ofstream fout( "debug.cdd" );  // ToRemove
//	manager.Display_Stat( fout );  // ToRemove
//	fout.close();
	NodeID result = Make_Root_Node( manager, _rsl_stack[0] );
	Set_Current_Level_Kernelized( false );
	_call_stack[0].Clear_Lit_Equivalences();
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
		manager.Verify_R2D2( result );
		manager.Verify_Entail_CNF( result, cnf );
		BigInt count = manager.Count_Models( result );
		BigInt verified_count = Count_Verified_Models_sharpSAT( cnf );
		assert( count == verified_count );
	}
	return manager.Generate_CCDD( result );
}

NodeID R2D2_Compiler::Make_Root_Node( R2D2_Manager & manager, NodeID node )
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

NodeID R2D2_Compiler::Make_Kernelized_Conjunction_Node( R2D2_Manager & manager, NodeID node )
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

void R2D2_Compiler::Choose_Running_Options( Heuristic heur, Chain & vorder )
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
	case FlowCutter:
		Compute_Var_Order_Flow_Cutter();
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "The flow cutter treewidth: " << running_options.treewidth << endl;
		break;
	case FixedLinearOrder:
		_var_order = vorder;
		running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		Rename_Clauses_Fixed_Ordering();
		break;
	case LexicographicOrder:
		Compute_Var_Order_Lexicographic();
		break;
	default:
		cerr << "ERROR[R2D2_Compiler]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
}

void R2D2_Compiler::Compute_Var_Order_Automatical()
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

void R2D2_Compiler::Choose_Implicate_Computing_Strategy()
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

void R2D2_Compiler::Reorder_Manager( R2D2_Manager & manager )
{
	Chain new_order;
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		if ( Variable::start <= _var_order[i] && _var_order[i] <= _max_var ) {
			new_order.Append( _var_order[i] );
		}
	}
	manager.Reorder( new_order );
}

void R2D2_Compiler::Compile_With_Implicite_BCP( R2D2_Manager & manager )
{
	Variable var;
	NodeID cached_result;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	while ( _num_levels > 1 ) {
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
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

NodeID R2D2_Compiler::Make_Node_With_Imp( R2D2_Manager & manager, NodeID node  )
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

NodeID R2D2_Compiler::Make_Decision_Node( R2D2_Manager & manager, NodeID low, NodeID high )
{
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
	if ( Cache_Clear_Applicable( manager ) ) Component_Cache_Clear();
	if ( manager.Num_Nodes() >= _node_redundancy_factor * running_options.removing_redundant_nodes_trigger ) {
		if ( high == NodeID::bot ) _rsl_stack[_num_rsl_stack++] = result;
		unsigned old_size = manager.Num_Nodes();
		Remove_Redundant_Nodes( manager );
		unsigned new_size = manager.Num_Nodes();
		if ( high == NodeID::bot ) result = _rsl_stack[--_num_rsl_stack];
		else result = _component_cache.Read_Result( Current_Component().caching_loc );
		if ( old_size - new_size < running_options.removing_redundant_nodes_trigger / 2000 ) _node_redundancy_factor *= 3;
		else if ( old_size - new_size < running_options.removing_redundant_nodes_trigger / 200 ) _node_redundancy_factor *= 2;
		else if ( old_size - new_size < running_options.removing_redundant_nodes_trigger / 10 ) _node_redundancy_factor *= 1.5;
		else _node_redundancy_factor += 0.05 + new_size / running_options.removing_redundant_nodes_trigger;
	}
	return result;
}

NodeID R2D2_Compiler::Make_Node_With_Imp( R2D2_Manager & manager, NodeID * nodes, unsigned num  )
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

void R2D2_Compiler::Compile_With_SAT_Imp_Computing( R2D2_Manager & manager )
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

bool R2D2_Compiler::Try_Shift_To_Implicite_BCP( R2D2_Manager & manager )
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
	running_options.imp_strategy = Partial_Implicit_BCP_Neg;
	Recycle_Models( _models_stack[_num_levels - 1] );
	Compile_With_Implicite_BCP( manager );
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) system( "./pause" );  // ToRemove
	running_options.imp_strategy = SAT_Imp_Computing;
	return true;
}

bool R2D2_Compiler::Estimate_Hardness( Component & comp )
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

CDDiagram R2D2_Compiler::Compile_FixedLinearOrder( R2D2_Manager & manager, Preprocessor & preprocessor, Chain & vorder )
{
	StopWatch begin_watch, tmp_watch;
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Compiling..." << endl;
	Allocate_and_Init_Auxiliary_Memory( preprocessor.Max_Var() );
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	Preprocessor::operator=( preprocessor );
	_models_stack[0] = _model_pool->Models();
	Store_Lit_Equivalences( _call_stack[0] );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		NodeID result = Make_Root_Node( manager, NodeID::top );
		_call_stack[0].Clear_Lit_Equivalences();
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
	Choose_Running_Options( FixedLinearOrder, vorder );
	Set_Current_Level_Kernelized( true );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {
		Recycle_Models( _models_stack[0] );
		if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
		Compile_With_Implicite_BCP( manager );
	}
	else {
		Compile_With_SAT_Imp_Computing( manager );
	}
	_num_rsl_stack--;
	NodeID result = Make_Root_Node( manager, _rsl_stack[0] );
	Set_Current_Level_Kernelized( false );
	_call_stack[0].Clear_Lit_Equivalences();
	Backtrack();
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_compiling >= Profiling_Abstract ) {
			Display_Statistics( 2 );
			Display_Memory_Status( cout );
			Display_Result_Statistics( cout, manager, result );
		}
	}
	Reset();
	return manager.Generate_CCDD( result );
}

void R2D2_Compiler::Verify_Result_Component( Component & comp, R2D2_Manager & manager, NodeID result )
{
//	Display_Component( comp, cout );
	CNF_Formula cnf( _max_var );
	_big_clause.Resize( 2 );
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Literal lit( comp.Vars(i), false );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		lit = Literal( comp.Vars(i), true );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		unsigned len = 0;
		_big_clause[len] = clause[0];
		len += Lit_Undecided( clause[0] );
		_big_clause[len] = clause[1];
		len += Lit_Undecided( clause[1] );
		_big_clause[len] = clause[2];
		len += Lit_Undecided( clause[2] );
		for ( unsigned j = 3; j < clause.Size(); j++ ) {
			_big_clause[len] = clause[j];
			len += Lit_Undecided( clause[j] );
		}
		assert( len >= 2 );  // there exist at least two unassigned variables in each clause
		_big_clause.Resize( len );
		cnf.Add_Clause( _big_clause );
	}
	manager.Verify_R2D2( result );
	BigInt count = manager.Count_Models( result );
	BigInt verified_count = Count_Verified_Models_sharpSAT( cnf );
	if ( verified_count != count ) {
		Display_Decision_Stack( cerr, _num_levels - 1 );
		cerr << cnf;
		assert( verified_count == count );
	}
	assert( verified_count == count );
}

void R2D2_Compiler::Display_Statistics( unsigned option )
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
			cout << running_options.display_prefix << "time generate DAG: " << statistics.time_gen_dag << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 2:
			if ( running_options.imp_strategy == SAT_Imp_Computing ) cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			else cout << running_options.display_prefix << "time IBCP: " << statistics.time_ibcp << endl;
			cout << running_options.display_prefix << "time dynamic decomposition: " << statistics.time_dynamic_decompose << " (" << statistics.time_dynamic_decompose_sort << " sorting)" << endl;
			cout << running_options.display_prefix << "time cnf cache: " << statistics.time_gen_cnf_cache << endl;
			cout << running_options.display_prefix << "time generate DAG: " << statistics.time_gen_dag << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << statistics.num_solve << endl;
			break;
		case 10:  // sharpSAT
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			break;
		default:
			cerr << "ERROR[Compiler]: this display mode is not existing!" << endl;
			assert( false );
			exit( 0 );
	}
	statistics.Init_Compiler();
}

void R2D2_Compiler::Display_Result_Statistics( ostream & out, R2D2_Manager & manager, NodeID root )
{
	out << running_options.display_prefix << "Number of nodes: " << manager.Num_Nodes( root ) << endl;
	out << running_options.display_prefix << "Number of edges: " << manager.Num_Edges( root ) << endl;
//	out << "Number of models: " << manager.Count_Models( cdd ) << endl;
//	OBDDC_Manager bddc_manager( _var_order, _max_var );
//	manager.Convert_Down( cdd, bddc_manager );
//	out << "Number of edges of the equivalent BDDC: " << manager.Num_Edges( cdd ) << endl;
}


}
