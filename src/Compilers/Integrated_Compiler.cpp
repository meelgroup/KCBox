#include "Integrated_Compiler.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


Compiler::Compiler():
_num_rsl_stack( 0 ),
_remove_redundancy_trigger( running_options.removing_redundant_nodes_trigger )
{
}

Compiler::~Compiler()
{
	Free_Auxiliary_Memory();
}

void Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler();
		return;
	}
	if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_rsl_stack = new NodeID [2 * max_var + 2];
	_bddc_rnode.Reset_Max_Var( max_var );
}

void Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
	delete [] _rsl_stack;
}

void Compiler::Reset()
{
	Inprocessor::Reset();
	_component_cache.Reset();
}

size_t Compiler::Memory()
{
	if ( _max_var == Variable::undef ) return 0;
	size_t mem = Preprocessor::Memory() + Inprocessor::Memory() + _component_cache.Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _models_stack[i].capacity() * sizeof(unsigned);
		mem += _comp_stack[i].Capacity() * sizeof(unsigned);
	}
	return mem;
}

BDDC Compiler::Compile( OBDDC_Manager & manager, CNF_Formula & cnf, Heuristic heur, Chain & vorder )
{
	assert( Is_Linear_Ordering( heur ) );
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_compiling_process ) running_options.display_preprocessing_process = false;
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Compiling..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	running_options.activate_easy_compiler = false;
	running_options.recover_exterior = true;
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
	if ( Non_Unary_Clauses_Empty() ) {
		BDDC result = Make_Node_With_Init_Imp( manager, NodeID::top );
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
		return result;
	}
	Gather_Infor_For_Counting();
	Choose_Running_Options( heur, vorder );
	if ( heur != FixedLinearOrder ) Reorder_BDDC_Manager( manager );
	Create_Init_Level();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) Compile_With_Implicite_BCP( manager );
	else Compile_With_SAT_Imp_Computing( manager );
	_num_rsl_stack--;
	BDDC result = Make_Node_With_Init_Imp( manager, _rsl_stack[0] );
	Backtrack();
	if ( running_options.display_compiling_process && running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
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
		manager.Verify_OBDDC( result );
		manager.Verify_ROBDDC_Finest( result );
		manager.Verify_Entail_CNF( result, cnf );
		BigInt count = manager.Count_Models( result );
		BigInt verified_count = Count_Verified_Models_sharpSAT( cnf );
		assert( count == verified_count );
	}
	return result;
}

NodeID Compiler::Make_Node_With_Init_Imp( OBDDC_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
//	assert( _unary_clauses.size() == _fixed_num_vars );
	_bddc_rnode.sym = BDDC_SYMBOL_CONJOIN;
	_bddc_rnode.ch[0] = node;
	_bddc_rnode.ch_size = ( node != NodeID::top );
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		_bddc_rnode.ch[_bddc_rnode.ch_size++] = NodeID::literal( _dec_stack[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _bddc_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void Compiler::Reorder_BDDC_Manager( OBDDC_Manager & manager )
{
	Chain new_order;
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		if ( Variable::start <= _var_order[i] && _var_order[i] <= _max_var ) {
			new_order.Append( _var_order[i] );
		}
	}
	manager.Reorder( new_order );
}

void Compiler::Create_Init_Level()
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
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	_component_cache.Init( _max_var, _old_num_long_clauses, NodeID::undef );
	_component_cache.Hit_Component( _comp_stack[0] );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
}


void Compiler::Compile_With_Implicite_BCP( OBDDC_Manager & manager )
{
	Variable var;
	NodeID cached_result;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	Recycle_Models( _models_stack[0] );
	if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
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
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

void Compiler::Backjump_Decision( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
		if ( running_options.erase_useless_cacheable_component ) Component_Cache_Erase( Current_Component() );
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void Compiler::Component_Cache_Erase( Component & comp )
{
	unsigned back_loc = _component_cache.Size() - 1;
	_component_cache.Erase( comp.caching_loc );
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		if ( _comp_stack[_comp_offsets[i]].caching_loc == back_loc ) {
			_comp_stack[_comp_offsets[i]].caching_loc = comp.caching_loc;
		}
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			if ( _comp_stack[j].caching_loc == back_loc ) {
				_comp_stack[j].caching_loc = comp.caching_loc;
			}
		}
	}
}

NodeID Compiler::Make_Node_With_Imp( OBDDC_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_bddc_rnode.sym = BDDC_SYMBOL_CONJOIN;
	_bddc_rnode.ch[0] = node;
	_bddc_rnode.ch_size = ( node != NodeID::top );
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_bddc_rnode.ch[_bddc_rnode.ch_size++] = NodeID::literal( _dec_stack[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _bddc_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

NodeID Compiler::Component_Cache_Map( Component & comp )
{
	StopWatch tmp_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	unsigned loc = _component_cache.Hit_Component( comp );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
	return _component_cache.Read_Result( loc );
}

void Compiler::Backtrack()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void Compiler::Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	_comp_offsets[_num_levels] = _num_comp_stack;
	_active_comps[_num_levels] = _comp_offsets[_num_levels];
	_state_stack[_num_levels++] = 0;
}

NodeID Compiler::Make_Decision_Node( OBDDC_Manager & manager, NodeID low, NodeID high )
{
	StopWatch begin_watch;
	assert( low != NodeID::bot );  // backjump guarantees this
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Decision_Node bnode( _dec_stack[_num_dec_stack].Var(), low, high );
	NodeID result = manager.Add_Decision_Node( bnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_component_compilation ) {
		Verify_Result_Component( Current_Component(), manager, result );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, result );
	const size_t GB = 1024 * 1024 * 1024;
	if ( _component_cache.Memory() > running_options.max_memory / 4 * GB ) {
		Component_Cache_Clear();
	}
	if ( manager.Num_Nodes() >= _remove_redundancy_trigger ) {
		unsigned old_size = manager.Num_Nodes();
		Remove_Redundant_Nodes( manager );
		unsigned new_size = manager.Num_Nodes();
		result = _component_cache.Read_Result( Current_Component().caching_loc );
		if ( old_size - new_size < 1000 ) _remove_redundancy_trigger += 2 * _remove_redundancy_trigger;
		else if ( old_size - new_size < 10000 ) _remove_redundancy_trigger += _remove_redundancy_trigger;
		else _remove_redundancy_trigger += _remove_redundancy_trigger / 2;
	}
	return result;
}

void Compiler::Component_Cache_Clear()
{
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "clear cache" << endl;
	StopWatch watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) watch.Start();
	vector<size_t> kept_locs;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( _comp_stack[_comp_offsets[i]].caching_loc );
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			kept_locs.push_back( _comp_stack[j].caching_loc );
		}
	}
	_component_cache.Clear( kept_locs );
	for ( unsigned i = 1, k = 0; i < _num_levels; i++ ) {
		_comp_stack[_comp_offsets[i]].caching_loc = kept_locs[k++];
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			_comp_stack[j].caching_loc = kept_locs[k++];
		}
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += watch.Get_Elapsed_Seconds();
}

void Compiler::Remove_Redundant_Nodes( OBDDC_Manager & manager )
{
	StopWatch watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) watch.Start();
	vector<NodeID> kept_nodes;
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "remove DAG redundancy: " << manager.Num_Nodes();
	for ( unsigned i = 0; i < _num_rsl_stack; i++ ) {
		kept_nodes.push_back( _rsl_stack[i] );
	}
	for ( unsigned i = 0; i < _component_cache.Size(); i++ ) {
		NodeID n = _component_cache.Read_Result( i );
		if ( n != NodeID::undef ) {
			kept_nodes.push_back( n );
		}
	}
	manager.Remove_Redundant_Nodes( kept_nodes );
	if ( running_options.display_compiling_process ) cout << " -> " << manager.Num_Nodes() << endl;
	for ( unsigned i = 0; i < _num_rsl_stack; i++ ) {
		_rsl_stack[i] = kept_nodes[i];
	}
	for ( unsigned i = 0, j = _num_rsl_stack; i < _component_cache.Size(); i++ ) {
		NodeID n = _component_cache.Read_Result( i );
		if ( n != NodeID::undef ) {
			_component_cache.Write_Result( i, kept_nodes[j++] );
		}
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += watch.Get_Elapsed_Seconds();
}

void Compiler::Backjump_Decomposition( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	_num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	if ( running_options.erase_useless_cacheable_component ) Component_Cache_Erase( Current_Component() );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
		if ( running_options.erase_useless_cacheable_component ) Component_Cache_Erase( Current_Component() );
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void Compiler::Backtrack_Halfway()
{
	_num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	_rsl_stack[_num_rsl_stack - 1] = NodeID::bot;
	Backtrack();
}

NodeID Compiler::Make_Node_With_Imp( OBDDC_Manager & manager, NodeID * nodes, unsigned num )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	unsigned i;
	_bddc_rnode.sym = BDDC_SYMBOL_CONJOIN;
	_bddc_rnode.ch_size = 0;
	for ( i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_bddc_rnode.Add_Child( NodeID::literal( _dec_stack[i] ) );
	}
	for ( i = 0; i < num; i++ ) {
		_bddc_rnode.Add_Child( nodes[i] );
	}
	NodeID result = manager.Add_Decomposition_Node( _bddc_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void Compiler::Compile_With_SAT_Imp_Computing( OBDDC_Manager & manager )
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
					cached_result = Component_Cache_Map( Current_Component() );
					if ( cached_result != NodeID::undef ) {  // no backjump
						if ( debug_options.verify_component_compilation ) {
							Verify_Result_Component( Current_Component(), manager, cached_result );
						}
						_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, cached_result );
						Recycle_Models( _models_stack[_num_levels - 1] );
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

void Compiler::Verify_Result_Component( Component & comp, OBDDC_Manager & manager, NodeID result )
{
	CNF_Formula * cnf = Output_Original_Clauses_In_Component( comp );
	manager.Verify_ROBDDC_Finest( result );
	BigInt count = manager.Count_Models( result );
	BigInt verified_count = Count_Verified_Models_sharpSAT( *cnf );
	if ( verified_count != count ) {
		manager.Display( cerr );  // ToRemove
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

void Compiler::Display_Statistics( unsigned option )
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

void Compiler::Display_Memory_Status( ostream & out )
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

void Compiler::Display_Result_Stack( ostream & out )
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

void Compiler::Display_Result_Statistics( ostream & out, OBDDC_Manager & manager, BDDC bddc )
{
	out << running_options.display_prefix << "Number of nodes: " << manager.Num_Nodes( bddc ) << endl;
	out << running_options.display_prefix << "Number of edges: " << manager.Num_Edges( bddc ) << endl;
	out << running_options.display_prefix << "Number of models: " << manager.Count_Models_Opt( bddc ) << endl;
}

void Compiler::Choose_Running_Options( Heuristic heur, Chain & vorder )
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
		cerr << "ERROR[Compiler]: this heuristic strategy is not supported yet!" << endl;
	}
	if ( running_options.imp_strategy == Automatical_Imp_Computing ) {
		Choose_Implicate_Computing_Strategy();
	}
}

void Compiler::Compute_Var_Order_Automatical()
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

void Compiler::Choose_Implicate_Computing_Strategy()
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

bool Compiler::Is_Memory_Exhausted()
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
