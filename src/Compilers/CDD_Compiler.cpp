#include "CDD_Compiler.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


CDD_Compiler::CDD_Compiler():
_num_rsl_stack( 0 ),
_node_redundancy_factor( 1 )
{
}

CDD_Compiler::~CDD_Compiler()
{
	Free_Auxiliary_Memory();
}

void CDD_Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler();
		return;
	}
	if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Compiler_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Extensive_Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_rsl_stack = new NodeID [2 * max_var + 2];
	_cdd_rnode.Reset_Max_Var( max_var );
	/// initialization
}

void CDD_Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
	delete [] _rsl_stack;
}

void CDD_Compiler::Reset()
{
	Extensive_Inprocessor::Reset();
	_component_cache.Reset();
	_node_redundancy_factor = 1;
}

size_t CDD_Compiler::Memory()
{
	if ( _max_var == Variable::undef ) return 0;
	size_t mem = Extensive_Inprocessor::Memory() + _component_cache.Memory();
	mem += (2 * _max_var + 2) * sizeof(NodeID);
	mem += _equivalent_lit_pairs.capacity() * sizeof(Literal);
	mem += _incremental_comp.Capacity() * sizeof(unsigned);
	return mem;
}

bool CDD_Compiler::Create_Init_Level()
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
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	if ( _current_kdepth == 1 ) {
		assert( _component_cache.Size() == 0 );
		_component_cache.Init( _max_var, _old_num_long_clauses, NodeID::undef );
		Component_Cache_Add_Original_Clauses();
		_component_cache.Hit_Component( _comp_stack[0] );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
		return true;
	}
	else {
		NodeID cached_result = Component_Cache_Map( _comp_stack[0] );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
		if ( cached_result != NodeID::undef ) {  /// NOTE: backjump makes that there are unknown cacheable component
			_rsl_stack[_num_rsl_stack++] = cached_result;
			Recycle_Models( _models_stack[0] );
			Backtrack();
			return false;
		}
		return true;
	}
}

void CDD_Compiler::Component_Cache_Add_Original_Clauses()
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

void CDD_Compiler::Backjump_Decision( unsigned num_kept_levels )
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

void CDD_Compiler::Component_Cache_Erase( Component & comp )
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
		if ( _call_stack[i].Existed() ) {
			if ( _call_stack[i].Get_Caching_Loc() == back_loc ) {
				_call_stack[i].Set_Caching_Loc( comp.caching_loc );
			}
		}
	}
}

NodeID CDD_Compiler::Component_Cache_Map( Component & comp )
{
	StopWatch tmp_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	if ( _current_kdepth <= 1 ) comp.caching_loc = _component_cache.Hit_Component( comp );
	else {
		Generate_Incremental_Component( comp );
		comp.caching_loc = _component_cache.Hit_Component( _incremental_comp );
	}
	if ( DEBUG_OFF && comp.caching_loc == 9 ) {  // ToRemove
		comp.Display( cerr );
		_incremental_comp.Display( cerr );
		Display_Component( comp, cerr );
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
	return _component_cache.Read_Result( comp.caching_loc );
}

void CDD_Compiler::Generate_Incremental_Component( Component & comp )
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

void CDD_Compiler::Backtrack()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void CDD_Compiler::Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	_comp_offsets[_num_levels] = _num_comp_stack;
	_active_comps[_num_levels] = _comp_offsets[_num_levels];
	_state_stack[_num_levels++] = 0;
}

bool CDD_Compiler::Cache_Clear_Applicable( CDD_Manager & manager )
{
	const size_t GB = 1024 * 1024 * 1024;
	double max_mem = running_options.max_memory * GB;
	if ( _component_cache.Memory() < max_mem * 0.005 ) return false;
	if ( _component_cache.Memory() > max_mem * 0.25 ) return true;
	size_t evaluated_mem = _component_cache.Memory() + manager.Hash_Memory();
	if ( evaluated_mem <= max_mem * 0.3 ) return false;
	if ( evaluated_mem > max_mem * 0.7 && _component_cache.Memory() > max_mem * 0.1 ) return true;
	if ( _component_cache.Size() < _component_cache.Capacity() || _component_cache.Hit_Successful() ) return false;
	size_t mem = Total_Used_Memory();
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close ) {
		cout << running_options.display_prefix << (float) _component_cache.Memory() / GB << " (cache) /";
		cout << (float) mem / GB << " (total) in GB" << endl;
	}
	if ( mem < max_mem * 0.8 ) return false;
	else return true;
}

void CDD_Compiler::Component_Cache_Clear()
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
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		if ( _call_stack[i].Existed() ) kept_locs.push_back( _call_stack[i].Get_Caching_Loc() );
	}
	_component_cache.Clear( kept_locs );
	unsigned index = 0;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		_comp_stack[_comp_offsets[i]].caching_loc = kept_locs[index++];
		for ( unsigned j = _comp_offsets[i] + 1; j <= _active_comps[i]; j++ ) {
			_comp_stack[j].caching_loc = kept_locs[index++];
		}
	}
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		if ( _call_stack[i].Existed() ) _call_stack[i].Set_Caching_Loc( kept_locs[index++] );
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += watch.Get_Elapsed_Seconds();
}

void CDD_Compiler::Remove_Redundant_Nodes( CDD_Manager & manager )
{
	unsigned old_size = manager.Num_Nodes();
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
	unsigned new_size = manager.Num_Nodes();
	if ( old_size - new_size < 1000 ) running_options.removing_redundant_nodes_trigger += 2 * running_options.removing_redundant_nodes_trigger;
	else if ( old_size - new_size < 10000 ) running_options.removing_redundant_nodes_trigger += running_options.removing_redundant_nodes_trigger;
	else running_options.removing_redundant_nodes_trigger += running_options.removing_redundant_nodes_trigger / 2;
}

void CDD_Compiler::Backjump_Decomposition( unsigned num_kept_levels )
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

void CDD_Compiler::Backtrack_Halfway()
{
	_num_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	_rsl_stack[_num_rsl_stack - 1] = NodeID::bot;
	Backtrack();
}

void CDD_Compiler::Sort_Clauses_For_Caching()
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

void CDD_Compiler::Sort_Long_Clauses_By_IDs()
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

void CDD_Compiler::Encode_Long_Clauses()
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

NodeID CDD_Compiler::Search_Root_Node( Search_Graph<NodeID> & graph, NodeID child )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	child = Search_Kernelized_Conjunction_Node( graph, child );
	Search_Node node( _dec_stack, _num_dec_stack, &child, 1 );
	child = graph.Push_Node( node );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return child;
}

NodeID CDD_Compiler::Search_Kernelized_Conjunction_Node( Search_Graph<NodeID> & graph, NodeID child )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	if ( !_call_stack[_num_levels - 1].Lit_Equivalences().empty() ) {
		Search_Node node( child, _call_stack[_num_levels - 1].Lit_Equivalences(), Current_Component().caching_loc );
		child = graph.Push_Node( node );
		_call_stack[_num_levels - 1].Clear_Lit_Equivalences();
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return child;
}

NodeID CDD_Compiler::Search_Node_With_Imp( Search_Graph<NodeID> & graph, NodeID child )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Literal * lits = _dec_stack + _dec_offsets[_num_levels - 1] + 1;
	unsigned num_lits = _num_dec_stack - _dec_offsets[_num_levels - 1] - 1;
	Search_Node node( lits, num_lits, &child, 1 );
	child = graph.Push_Node( node );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return child;
}

NodeID CDD_Compiler::Search_Decision_Node( Search_Graph<NodeID> & graph, NodeID low, NodeID high )
{
//	Debug_Print_Visit_Number( cerr, __FUNCTION__, __LINE__ );  // ToRemove
	StopWatch begin_watch;
	assert( low != NodeID::bot );  // backjump guarantees this
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Decision_Node bnode( _dec_stack[_num_dec_stack].Var(), low, high );
	NodeID result = graph.Push_Decision_Node( bnode, Current_Component().caching_loc );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	_component_cache.Write_Result( Current_Component().caching_loc, result );
	return result;
}

NodeID CDD_Compiler::Search_Node_With_Imp( Search_Graph<NodeID> & graph, NodeID * nodes, unsigned num )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Literal * lits = _dec_stack + _dec_offsets[_num_levels - 1] + 1;
	unsigned num_lits = _num_dec_stack - _dec_offsets[_num_levels - 1] - 1;
	Search_Node node( lits, num_lits, nodes, num );
	NodeID result = graph.Push_Node( node );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void CDD_Compiler::Display_Statistics( unsigned option )
{
	switch ( option ) {
		case 0:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << Inprocessor::statistics.num_solve << endl;
			break;
		case 1:
			cout << running_options.display_prefix << "time preprocess: " << Preprocessor::statistics.time_preprocess << endl;
			cout << running_options.display_prefix << "time compute tree decomposition: " << Inprocessor::statistics.time_tree_decomposition << endl;
			if ( running_options.imp_strategy == SAT_Imp_Computing ) cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			else cout << running_options.display_prefix << "time IBCP: " << statistics.time_ibcp << endl;
			cout << running_options.display_prefix << "time dynamic decomposition: " << statistics.time_dynamic_decompose << " (" << statistics.time_dynamic_decompose_sort << " sorting)" << endl;
			cout << running_options.display_prefix << "time cnf cache: " << statistics.time_gen_cnf_cache << endl;
			if ( running_options.max_kdepth > 1 ) cout << running_options.display_prefix << "time kernelize: " << statistics.time_kernelize << endl;
			cout << running_options.display_prefix << "time generate DAG: " << statistics.time_gen_dag << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << Inprocessor::statistics.num_solve << endl;
			break;
		case 10:  // sharpSAT
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			break;
		default:
			cerr << "ERROR[CDD_Compiler]: this display mode is not existing!" << endl;
			assert( false );
			exit( 0 );
	}
	statistics.Init_Compiler();
}

void CDD_Compiler::Display_Memory_Status( ostream & out )
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

void CDD_Compiler::Display_Result_Stack( ostream & out )
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

void CDD_Compiler::Display_Result_Statistics( ostream & out, CDD_Manager & manager, CDD cdd )
{
	out << running_options.display_prefix << "Number of nodes: " << manager.Num_Nodes( cdd ) << endl;
	out << running_options.display_prefix << "Number of edges: " << manager.Num_Edges( cdd ) << endl;
}

bool CDD_Compiler::Is_Memory_Exhausted()
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
