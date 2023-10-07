#include "CCDD_Compiler.h"
#include "R2D2_Compiler.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


CCDD_Compiler::CCDD_Compiler()
{
}

CCDD_Compiler::~CCDD_Compiler()
{
	Free_Auxiliary_Memory();
}

void CCDD_Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
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

void CCDD_Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
}

void CCDD_Compiler::Reset()
{
	CDD_Compiler::Reset();
}

CDD CCDD_Compiler::Compile( CCDD_Manager & manager, CNF_Formula & cnf, Heuristic heur, Chain & vorder )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_compiling_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
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
		return NodeID::bot;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		CDD result = Make_Root_Node( manager, NodeID::top );
		Un_BCP( _dec_offsets[--_num_levels] );
		_call_stack[0].Clear_Lit_Equivalences();
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
				Display_Result_Statistics( cout, manager, result );
			}
		}
		Reset();
		return result;
	}
	Gather_Infor_For_Counting();
	Choose_Running_Options( heur, vorder );
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close ) running_options.Display( cout );  // ToRemove
	if ( Is_Linear_Ordering( running_options.var_ordering_heur ) == lbool(true) ) Reorder_Manager( manager );
	CDD result;
	if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) {
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "==== Shift to R2-D2 compilation ====" << endl;
		manager.Shrink_Nodes();
		_component_cache.Shrink_To_Fit();
		for ( Variable x = _max_var.Next(); x <= Variable( _var_order.Max() ); x++ ) {
			_var_order.Erase( x );
		}
		Load_Lit_Equivalences( _call_stack[0] );
		R2D2_Manager manager2( _var_order );
		R2D2_Compiler compiler;
		result = compiler.Compile_FixedLinearOrder( manager2, *this, _var_order );
		if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "==== Finish R2-D2 compilation ====" << endl;
		manager.Load_Nodes( manager2 );
	}
	else {
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
			Compile_With_SAT_Imp_Computing( manager );
		}
		_num_rsl_stack--;
		result = Make_Root_Node( manager, _rsl_stack[0] );
		Set_Current_Level_Kernelized( false );
		Backtrack();
		_call_stack[0].Clear_Lit_Equivalences();
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_compiling >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Memory_Status( cout );
			manager.Statistics( result );
		}
	}
	Reset();
	if ( debug_options.verify_compilation ) {
//		manager.Display_Stat( cout );  // ToRemove
//		manager.Verify_CCDD( result );
		manager.Verify_Entail_CNF( result, cnf );
		BigInt count = manager.Count_Models( result );
		BigInt verified_count = Count_Verified_Models_sharpSAT( cnf );
		assert( count == verified_count );
	}
	return result;
}

NodeID CCDD_Compiler::Make_Root_Node( CCDD_Manager & manager, NodeID node )
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

NodeID CCDD_Compiler::Make_Kernelized_Conjunction_Node( CCDD_Manager & manager, NodeID node )
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

void CCDD_Compiler::Choose_Running_Options( Heuristic heur, Chain & vorder )
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
	case LinearLRW:
		Compute_Var_Order_Single_Cluster();
		break;
	case FixedLinearOrder:
		_var_order = vorder;
		Rename_Clauses_Fixed_Ordering();
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
		cerr << "ERROR[CCDD_Compiler]: this heuristic strategy is not supported yet!" << endl;
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
		if ( _call_stack[0].Lit_Equivalences_Size() == 0 ) running_options.max_kdepth = 2;
	}
	if ( running_options.var_ordering_heur == DLCP ) {
//		running_options.lit_equivalence_detecting_strategy = Literal_Equivalence_Detection_IBCP;
	}
}

void CCDD_Compiler::Compute_Var_Order_Automatical()
{
	const unsigned upper_bound = 128;
	unsigned treewidth_bound = _unsimplifiable_num_vars / 5;
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

void CCDD_Compiler::Choose_Implicate_Computing_Strategy()
{
	assert( running_options.imp_strategy == Automatical_Imp_Computing );
	if ( Is_TreeD_Based_Ordering( running_options.var_ordering_heur ) ) {
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

void CCDD_Compiler::Reorder_Manager( CCDD_Manager & manager )
{
	Chain new_order;
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		if ( Variable::start <= _var_order[i] && _var_order[i] <= _max_var ) {
			new_order.Append( _var_order[i] );
		}
	}
	manager.Reorder( new_order );
}

void CCDD_Compiler::Compile_With_Implicite_BCP( CCDD_Manager & manager )
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
				var = Pick_Good_Var_Component( Current_Component() );
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
						var = Pick_Good_Var_Component( Current_Component() );
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

NodeID CCDD_Compiler::Make_Node_With_Imp( CCDD_Manager & manager, NodeID node  )
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

NodeID CCDD_Compiler::Make_Decision_Node( CCDD_Manager & manager, NodeID low, NodeID high )
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
		else _node_redundancy_factor *= 1.5;
	}
	return result;
}

NodeID CCDD_Compiler::Make_Node_With_Imp( CCDD_Manager & manager, NodeID * nodes, unsigned num )
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

void CCDD_Compiler::Compile_With_SAT_Imp_Computing( CCDD_Manager & manager )
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
				var = Pick_Good_Var_Component( Current_Component() );
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
						var = Pick_Good_Var_Component( Current_Component() );
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

bool CCDD_Compiler::Try_Shift_To_Implicite_BCP( CCDD_Manager & manager )
{
	if ( !running_options.mixed_imp_computing ) return false;
	Component & comp = Current_Component();
	if ( comp.Vars_Size() > running_options.trivial_variable_bound && Estimate_Hardness( comp ) ) return false;
	assert( running_options.imp_strategy == SAT_Imp_Computing );
	if ( Try_Final_Kernelization( manager ) == lbool::unknown ) return true;
	running_options.imp_strategy = Partial_Implicit_BCP;
	if ( !running_options.static_heur && running_options.mixed_var_ordering ) {
		Heuristic old_heur = running_options.var_ordering_heur;
		Chain old_order;
		_var_order.Swap( old_order );
		Compute_Second_Var_Order_Automatical( comp );
		Recycle_Models( _models_stack[_num_levels - 1] );
		Compile_With_Implicite_BCP( manager );
		_var_order.Swap( old_order );
		running_options.var_ordering_heur = old_heur;
	}
	else {
		Recycle_Models( _models_stack[_num_levels - 1] );
		Compile_With_Implicite_BCP( manager );
	}
	if ( false && comp.Vars_Size() > running_options.trivial_variable_bound / 1 ) system( "./pause" );  // ToRemove
	running_options.imp_strategy = SAT_Imp_Computing;
	Leave_Final_Kernelization( manager );
	return true;
}

bool CCDD_Compiler::Estimate_Hardness( Component & comp )
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

lbool CCDD_Compiler::Try_Final_Kernelization( CCDD_Manager & manager )
{
	if ( _current_kdepth >= running_options.max_kdepth || Estimate_Final_Kernelization_Effect() == false ) return lbool(false);
	Store_Cached_Binary_Clauses();
	Kernelize_Without_Imp();
	Set_Current_Level_Kernelized( true );
	Sort_Clauses_For_Caching();
	NodeID cached_result;
	if ( Current_Component().Vars_Size() == 0 ) cached_result = NodeID::top;
	else cached_result = Component_Cache_Map( Current_Component() );
	if ( cached_result != NodeID::undef ) {
		if ( debug_options.verify_component_count ) {
			Verify_Result_Component( Current_Component(), manager, cached_result );
		}
		_rsl_stack[_num_rsl_stack++] = cached_result;
		Leave_Kernelization( manager );
		ASSERT( Is_Current_Level_Decision() );
		Recycle_Models( _models_stack[_num_levels - 1] );
		_rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );
		Backtrack();
		return lbool::unknown;
	}
	assert( running_options.decompose_strategy == Decompose_Without_Sorting );
	Generate_Long_Watched_Lists_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Binary_Component( Current_Component() );
	Generate_Membership_Lists_Subdivision_Long();  // ToModify
	return lbool(true);
}

bool CCDD_Compiler::Estimate_Final_Kernelization_Effect()
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

void CCDD_Compiler::Leave_Final_Kernelization( CCDD_Manager & manager )
{
	if ( !_call_stack[_num_levels].Existed() ) return;  // _num_levels-- is done in IBCP
	Extend_New_Level();
	_num_comp_stack += 1;
	const CDD_Node & sub_root = manager.Node( _rsl_stack[_num_rsl_stack - 1] );
	NodeID core;
	if ( sub_root.sym == CDD_SYMBOL_DECOMPOSE ) core = sub_root.ch[sub_root.ch_size - 1];  /// NOTE: first imp, and then kernelization; need to recover
	else core = _rsl_stack[_num_rsl_stack - 1];
	_rsl_stack[_num_rsl_stack - 1] = Make_Kernelized_Conjunction_Node( manager, core );
	Clear_Cached_Binary_Clauses();
	Set_Current_Level_Kernelized( false );
	Cancel_Kernelization_Without_Imp();
	Recover_Cached_Binary_Clauses();
	Encode_Long_Clauses();
	if ( false && debug_options.verify_component_compilation ) {
		Verify_Result_Component( Current_Component(), manager, _rsl_stack[_num_rsl_stack - 1] );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	if ( sub_root.sym == CDD_SYMBOL_DECOMPOSE ) {
		_cdd_rnode.sym = CDD_SYMBOL_DECOMPOSE;
		_cdd_rnode.ch_size = sub_root.ch_size;
		for ( unsigned i = 0; i < sub_root.ch_size - 1; i++ ) {
			_cdd_rnode.ch[i] = sub_root.ch[i];
		}
		_cdd_rnode.ch[_cdd_rnode.ch_size - 1] = _rsl_stack[_num_rsl_stack - 1];
		_rsl_stack[_num_rsl_stack - 1] = manager.Add_Decomposition_Node( _cdd_rnode );
	}
	Backtrack();
}

void CCDD_Compiler::Compute_Second_Var_Order_Automatical( Component & comp )
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

lbool CCDD_Compiler::Try_Kernelization( CCDD_Manager & manager )
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

bool CCDD_Compiler::Estimate_Kernelization_Effect()
{
	if ( false ) {
		if ( _num_levels > 2 ) return true;  // ToModify
		else return false;
	}
	else if ( _current_kdepth + 1 < running_options.max_kdepth ) {
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step, 3 );
	}
	else  {
//		if ( running_options.max_kdepth == 2 ) return false;
		if ( Current_Component().Vars_Size() > running_options.trivial_variable_bound * 2 ) return false;
		return Estimate_Kernelization_Effect_Enough_Decisions( running_options.kernelizing_step, 3 );
	}
}

void CCDD_Compiler::Leave_Kernelization( CCDD_Manager & manager )
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

void CCDD_Compiler::Verify_Result_Component( Component & comp, CCDD_Manager & manager, NodeID result )
{
	CNF_Formula * cnf = Output_Original_Clauses_In_Component( comp );
	manager.Verify_CCDD( result );
	BigInt count = manager.Count_Models( result );
	BigInt verified_count = Count_Verified_Models_sharpSAT( *cnf );
	BigInt tmp_count = count;  // ToRemove
	tmp_count.Div_2exp( _num_dec_stack );
	if ( verified_count != count ) {
		manager.Display_CDD( cerr, result );  // ToRemove
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
