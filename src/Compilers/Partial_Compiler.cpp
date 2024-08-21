#include "Partial_Compiler.h"


namespace KCBox {


Partial_CCDD_Compiler::Partial_CCDD_Compiler():
_num_rsl_stack( 0 ),
_num_pmc_rsl_stack( 0 ),
_node_redundancy_factor( 1 ),
_store_one_model( false )
{
}

Partial_CCDD_Compiler::~Partial_CCDD_Compiler()
{
	Free_Auxiliary_Memory();
}

void Partial_CCDD_Compiler::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( _max_var == max_var ) {
		if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Partial_KC();
		return;
	}
	if ( running_options.profile_compiling != Profiling_Close ) statistics.Init_Partial_KC_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use max_var because it is not assigned yet (it will be assigned in Preprocessor::Allocate_and_Init_Auxiliary_Memory)
	Extensive_Inprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_var_distribution = new double [max_var + 1];
	_rsl_stack = new NodeID [2 * max_var + 2];
	_pmc_rsl_stack = new double [2 * max_var + 2];
	_level_ExactMC_failed = new bool [max_var + 1];
	/// initialization
	_exact_counter.running_options.display_counting_process = false;
	for ( unsigned i = 0; i < max_var + 1; i++ ) {
		_level_ExactMC_failed[i] = false;
	}
}

void Partial_CCDD_Compiler::Free_Auxiliary_Memory()
{
	if ( _max_var == Variable::undef ) return;
	delete [] _var_distribution;
	delete [] _rsl_stack;
	delete [] _pmc_rsl_stack;
	delete [] _level_ExactMC_failed;
}

void Partial_CCDD_Compiler::Reset()
{
	Extensive_Inprocessor::Reset();
	_component_cache.Reset();
	_node_redundancy_factor = 1;
	_store_one_model = false;
}

size_t Partial_CCDD_Compiler::Memory()
{
	if ( _max_var == Variable::undef ) return 0;
	size_t mem = Extensive_Inprocessor::Memory() + _component_cache.Memory();
	mem += (_max_var + 1) * sizeof(double);
	mem += 2 * (2 * _max_var + 2) * sizeof(NodeID);
	mem += _pcdd_rnode.Memory();
	mem += _incremental_comp.Capacity() * sizeof(unsigned);
	return mem;
}

NodeID Partial_CCDD_Compiler::Partially_Compile( Partial_CCDD_Manager & manager, CNF_Formula & cnf, Heuristic heur )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_compiling_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Compiling..." << endl;
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	assert( running_options.sampling_count > 0 );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	bool cnf_sat = Preprocess( cnf, _models_stack[0] );
	if ( _models_stack[0].empty() ) Generate_Models_External( _models_stack[0] );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
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
		NodeID result = Make_Root_Node( manager, NodeID::top );
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
	Choose_Compiling_Options( heur );
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close ) running_options.Display( cout );  // ToRemove
	_exact_counter.running_options.max_memory = running_options.max_memory / 2;
	BigInt exact_count;
	if ( debug_options.verify_compilation ) exact_count = _exact_counter.Count_Models( cnf );
	Set_Current_Level_Kernelized( true );
	for ( unsigned current_sample = 1; current_sample <= running_options.sampling_count; current_sample++ ) {
//		Display_Clauses( cout, true );  // ToRemove
//		Display_Models( models_stack[1], cout );  // ToRemove
//		cout << "====" << endl;
		Create_Init_Level( current_sample == 1 );
		Microcompile( manager );
//		nr_stack[0]->Display_Weight( cout, max_var );
//		cout << "====" << endl;
//		Display_Memory_Status( cout );  // ToRemove
//	  ofstream fout( "debug2.txt" );
//		nnf->root = nr_stack[0];  // ToRemove
//		nnf->Display_Weight( fout );  // ToRemove
//		fout.close();
//		cout << "====" << endl;
//		nnf->root = NULL;  // ToRemove
		_num_rsl_stack--;
		if ( running_options.display_compiling_process && current_sample % running_options.sampling_display_interval == 0 ) {
			BigFloat weight = manager.Node( _rsl_stack[0] ).weight;  // ToCheck: without this line, it will output an error result
			weight.Div_2exp( _fixed_num_vars + _call_stack[0].Lit_Equivalences_Size() );
			cout << running_options.display_prefix << current_sample << "(" << begin_watch.Get_Elapsed_Seconds() << "s): " << weight << endl;
			if ( debug_options.verify_compilation ) {
				cout << running_options.display_prefix << "Exact count: " << exact_count << endl;
			}
		}
	}
	NodeID result = Make_Root_Node( manager, _rsl_stack[0] );
	Set_Current_Level_Kernelized( false );
	Backtrack();
	_call_stack[0].Clear_Lit_Equivalences();
	if ( running_options.display_compiling_process ) Display_Memory_Status( cout ); // ToRemove
	manager.Realloc_Model_Space( _model_pool );
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	assert( _model_pool->Empty() );
	Reset();
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_partial_kc >= Profiling_Abstract ) {
			Display_Statistics( 1 );
			Display_Result_Statistics( cout, manager, result );
//			ofstream fout( "result.txt" );  // ToRemove
//			nnf->Display_Weight( fout, true );  // ToRemove
//		  fout.close();  // ToRemove
//			system( "sleep 20h" );  // ToRemove
		}
	}
	if ( debug_options.verify_compilation ) {
//		nnf->Display_Weight( cout );
//		nnf->Init_Reserved_Infor();
		manager.Verify_Decomposability( result );
//		Verify_Bound( cnf, *nnf );
	}
	return result;
}

NodeID Partial_CCDD_Compiler::Make_Root_Node( Partial_CCDD_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	node = Make_Kernelized_Conjunction_Node( manager, node );
	_pcdd_rnode.sym = SEARCH_DECOMPOSED;
	_pcdd_rnode.imp.resize( _num_dec_stack );
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		_pcdd_rnode.imp[i] = _dec_stack[i];
	}
	_pcdd_rnode.ch.resize( node != NodeID::top );
	if ( node != NodeID::top ) _pcdd_rnode.ch[0] = node;
	NodeID result = manager.Add_Decomposition_Node( _pcdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

NodeID Partial_CCDD_Compiler::Make_Kernelized_Conjunction_Node( Partial_CCDD_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_pcdd_rnode.sym = SEARCH_KERNELIZED;
	_pcdd_rnode.Update( node );
	_pcdd_rnode.imp = _call_stack[_num_levels - 1].Lit_Equivalences();
	node = manager.Add_Kernelization_Node( _pcdd_rnode, Current_Component().caching_loc );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return node;
}

void Partial_CCDD_Compiler::Choose_Compiling_Options( Heuristic heur )
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
		cerr << "ERROR[Partial_Compiler]: this heuristic strategy is not supported yet!" << endl;
		exit( 1 );
	}
	if ( running_options.treewidth <= 32 && running_options.trivial_variable_bound > _unsimplifiable_num_vars * 3 / 4 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars * 3 / 4;
	}
	else if ( running_options.treewidth <= 64 && running_options.trivial_variable_bound > _unsimplifiable_num_vars * 2 / 3 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars * 2 / 3;
	}
	else if ( running_options.trivial_variable_bound > _unsimplifiable_num_vars / 2 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars / 2;
	}
	running_options.trivial_clause_bound = running_options.trivial_variable_bound;
	running_options.trivial_density_bound = 3;
	running_options.trivial_length_bound = 0.5;
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
	if ( running_options.estimate_marginal_probability && !Is_Linear_Ordering( running_options.var_ordering_heur ) ) {
		Compute_Var_Order_Single_Cluster();
	}
	running_options.mem_load_factor = 0.5;
}

void Partial_CCDD_Compiler::Compute_Var_Order_Automatical()
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

void Partial_CCDD_Compiler::Create_Init_Level( bool initial )
{
	assert( _current_kdepth == 1 );
	if ( initial ) {
		assert( _component_cache.Size() == 0 );
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
		_component_cache.Init( _max_var, _old_num_long_clauses, NodeID::undef );
		Component_Cache_Add_Original_Clauses();
		_component_cache.Hit_Component( _comp_stack[0] );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
	}
	else {
		assert( _models_stack[0].empty() && _models_stack[1].empty() );
		assert( _num_levels == 1 );  // NOTE: level 0 is used to unary clauses
		assert( _component_cache.Read_Result( _comp_stack[0].caching_loc ) != NodeID::undef );
		_dec_offsets[1] = _num_dec_stack;
		_state_stack[1] = 1;
		_num_comp_stack = 1;
		_comp_offsets[1] = 0;
		_active_comps[1] = 0;
		_num_levels = 2;
	}
}

void Partial_CCDD_Compiler::Component_Cache_Add_Original_Clauses()
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

void Partial_CCDD_Compiler::Microcompile( Partial_CCDD_Manager & manager )
{
	Variable var;
	NodeID parent, old_result;
	Move_Models( _models_stack[0], _models_stack[1] );
	while ( _num_levels > 1 ) {
//		Display_Clauses( cout, false );
//		Display_Watched_List( cout );
//		model_pool->Display( cout );
//		cout << "----" << endl;
//		Display_Models( models_stack[_num_levels - 1], cout );
//		cout << "====" << endl;
//		Display_Decision_Stack( cout );
//		system( "pause" );
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				parent = _component_cache.Read_Result( Parent_of_Current_Component().caching_loc );
				if ( parent == NodeID::undef ) old_result = NodeID::undef;
				else old_result = manager.Node(parent).ch[ _dec_stack[_num_dec_stack - 1].Sign()];
				if ( old_result == NodeID::undef || manager.Node(old_result).sym == SEARCH_UNKNOWN ) {
					Get_All_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );  // NOTE: comp_stack[num_level - 1] is not generated yet
					_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
					Handle_Components( manager, _num_comp_stack - _comp_offsets[_num_levels - 1] );
				}
				else {
					Recover_All_Imp( manager, old_result );
					Recover_and_Handle_Components( manager, old_result );
				}
				break;
			case 1:
				if ( Is_Component_Trivial( Current_Component() ) ) {
					Backtrack_Trivial( manager );
					break;
				}
				if ( Try_Kernelization( manager ) == lbool::unknown ) break;
				Extend_New_Level( manager );
				break;
			case 2:
				assert( _num_rsl_stack >= 1 );
				Backtrack_Decision( manager );
				break;
			}
		}
		else {
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 2 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1] % 2 ) {
				case 0:
					Component_Cache_Map( Current_Component() );
					if ( Is_Component_Trivial( Current_Component() ) ) {
						Iterate_Trivial( manager );
					}
					else Extend_New_Level( manager );
					break;
				case 1:
					assert( _num_rsl_stack >= 1 );
					Iterate_Decision( manager );
					break;
				}
			}
			else {
				assert( _num_rsl_stack >= _state_stack[_num_levels - 1] / 2 && _num_rsl_stack >= 2 );
				Backtrack_Decomposition( manager );
			}
		}
	}
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

void Partial_CCDD_Compiler::Handle_Components( Partial_CCDD_Manager & manager, unsigned num_comp )
{
	if ( num_comp == 0 ) Backtrack_True( manager );
	else if ( num_comp == 1 ) {
		Component_Cache_Map( Current_Component() );
		_state_stack[_num_levels - 1]++;
	}
	else _state_stack[_num_levels - 1] = 0;
}

void Partial_CCDD_Compiler::Backtrack_True( Partial_CCDD_Manager & manager )
{
	_rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, NodeID::top );
	Recycle_Models( _models_stack[_num_levels - 1] );
	Backtrack();
}

NodeID Partial_CCDD_Compiler::Make_Node_With_Imp( Partial_CCDD_Manager & manager, NodeID node )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_pcdd_rnode.sym = SEARCH_DECOMPOSED;
	_pcdd_rnode.ch.resize( node != NodeID::top );
	if ( node != NodeID::top ) _pcdd_rnode.ch[0] = node;
	_pcdd_rnode.imp.resize( Num_Current_Imps() );
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		_pcdd_rnode.imp[i - _dec_offsets[_num_levels - 1] - 1] = _dec_stack[i];
	}
	NodeID result = manager.Add_Decomposition_Node( _pcdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

NodeID Partial_CCDD_Compiler::Component_Cache_Map( Component & comp )
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

void Partial_CCDD_Compiler::Generate_Incremental_Component( Component & comp )
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

void Partial_CCDD_Compiler::Recover_All_Imp( Partial_CCDD_Manager & manager, NodeID root )
{
	assert( root != NodeID::undef );
	assert( manager.Node( root ).sym != SEARCH_UNKNOWN );
	StopWatch watch;
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) watch.Start();
	const Partial_CDD_Node & old_node = manager.Node( root );
	if ( old_node.sym == SEARCH_DECOMPOSED ) {
		for ( unsigned i = 0; i < old_node.imp_size; i++ ) {
			assert( Lit_Undecided( old_node.imp[i] ) );
			Assign( old_node.imp[i] );
		}
	}
	unsigned old_num_dec_stack = _num_dec_stack;
	BCP( _dec_offsets[_num_levels - 1] );
	if ( old_num_dec_stack != _num_dec_stack ) {  // NOTE: this statement can report many bugs
		Display_Decision_Stack( cerr, _num_levels - 1 );
		for ( unsigned i = old_num_dec_stack; i < _num_dec_stack; i++ ) {
			Display_Conflict( _reasons[_dec_stack[i].Var()], cerr );
		}
		assert( old_num_dec_stack == _num_dec_stack );
	}
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_solve += watch.Get_Elapsed_Seconds();
}

void Partial_CCDD_Compiler::Recover_and_Handle_Components( Partial_CCDD_Manager & manager, NodeID root )
{
	assert( root != NodeID::undef );
	assert( manager.Node( root ).sym != SEARCH_UNKNOWN );
	assert( _models_stack[_num_levels - 1].empty() );
	StopWatch tmp_watch;
	const Partial_CDD_Node & old_node = manager.Node( root );
	if ( old_node.ch_size == 0 ) Backtrack_True( manager );
	else if ( old_node.sym == SEARCH_DECOMPOSED ) {
		_num_comp_stack += old_node.ch_size;
		_state_stack[_num_levels - 1] = (old_node.ch_size == 1);
		for ( unsigned i = 0; i < old_node.ch_size; i++ ) {
			const Partial_CDD_Node & old_child = manager.Node( old_node.ch[i] );
			assert( old_child.sym <= _max_var || old_child.sym == SEARCH_KERNELIZED || old_child.sym == SEARCH_KNOWN );
			assert( old_child.caching_loc < _component_cache.Size() );
			unsigned offset = _comp_offsets[_num_levels - 1] + i;
			Component_Cache_Recover( old_child.caching_loc, _comp_stack[offset] );
		}
	}
	else {
		_num_comp_stack++;
		_state_stack[_num_levels - 1] = 1;
		assert( old_node.sym <= _max_var || old_node.sym == SEARCH_KERNELIZED || old_node.sym == SEARCH_KNOWN );
		assert( old_node.caching_loc < _component_cache.Size() );
		unsigned offset = _comp_offsets[_num_levels - 1];
		Component_Cache_Recover( old_node.caching_loc, _comp_stack[offset] );
	}
}

void Partial_CCDD_Compiler::Component_Cache_Recover( unsigned loc, Component & comp )
{
	StopWatch tmp_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	if ( _current_kdepth <= 1 ) _component_cache.Read_Component( loc, comp );
	else {
		_component_cache.Read_Component( loc, _incremental_comp );
		Recover_From_Incremental_Component( comp );
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
}

void Partial_CCDD_Compiler::Recover_From_Incremental_Component( Component & comp )
{
	comp.Clear();
	comp.Swap_VarIDs( _incremental_comp );
	comp.caching_loc = _incremental_comp.caching_loc;
	if ( _incremental_comp.ClauseIDs_Size() == 0 ) return;
	SetID id = *(_incremental_comp.ClauseIDs_End() - 1);
	if ( _component_cache.Read_Clause( id ).size == 2 ) return;
	unsigned i = 0;
	for ( ; _component_cache.Read_Clause( _incremental_comp.ClauseIDs( i ) ).size == 2; i++ ) {}
	for ( ; i < _incremental_comp.ClauseIDs_Size(); i++ ) {
		id = _incremental_comp.ClauseIDs( i );
		unsigned pos = Search_Pos_Nonempty( _long_clause_ids.data(), _long_clause_ids.size(), id );
		comp.Add_ClauseID( pos );
	}
	comp.Sort_ClauseIDs( _qsorter );
}

bool Partial_CCDD_Compiler::Is_Component_Trivial( Component & comp )
{
	if ( comp.Vars_Size() > 128 ) {
		unsigned num_failed = 0, last_level = _max_var;
		unsigned stop_level = _num_levels > 16 ? _num_levels - 16 : 1;
		for ( unsigned i = _num_levels - 1; i >= stop_level; i-- ) {
			if ( !_level_ExactMC_failed[i] ) continue;
			num_failed++;
			if ( last_level == _max_var ) last_level = i;
		}
		if ( last_level != _max_var ) {
			Component & last_comp = _comp_stack[_active_comps[last_level]];
			if ( last_comp.Vars_Size() - comp.Vars_Size() < 8 * num_failed ) return false;
		}
	}
	unsigned trivial_lower_bound = running_options.trivial_variable_bound;
	unsigned trivial_upper_bound = running_options.trivial_variable_bound * 2;
	if ( NumVars( _max_var ) - 16 <= trivial_upper_bound ) trivial_upper_bound = NumVars( _max_var ) - 16;
	unsigned trivial_clause_bound = running_options.trivial_clause_bound;
	if ( _old_num_long_clauses - 32 < trivial_clause_bound ) trivial_clause_bound = _old_num_long_clauses - 32;
	if ( comp.Vars_Size() <= trivial_lower_bound || comp.ClauseIDs_Size() <= trivial_clause_bound ) return true;
	if ( comp.Vars_Size() > trivial_upper_bound ) return false;
	float density, length;
	Hardness_Features_of_Clauses( comp, density, length );
	if ( density < running_options.trivial_density_bound || length < running_options.trivial_length_bound ) return true;
	else return false;
}

void Partial_CCDD_Compiler::Hardness_Features_of_Clauses( Component & comp, float & density, float & length )
{
	unsigned den = 0;
	unsigned len = 0;
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
			den += true_size * ( true_size - 1 ) / 2;
			len += true_size;
		}
		if ( false ) cerr << "(" << clause.Size() << " vs " << true_size << ")";
	}
	density = 1.0 * den / comp.Vars_Size();
	length = 1.0 * len / comp.Vars_Size();
	if ( false ) cerr << density << " and " << length << endl;  // ToRemove
}

void Partial_CCDD_Compiler::Backtrack_Trivial( Partial_CCDD_Manager & manager )
{
	StopWatch tmp_watch;
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.sym != SEARCH_UNKNOWN ) {
			assert( old_node.sym == SEARCH_KNOWN );
			if ( _num_levels == 2 ) _rsl_stack[_num_rsl_stack++] = old_id;
			else _rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, old_id );
			Recycle_Models( _models_stack[_num_levels - 1] );
			Backtrack();
			return;
		}
	}
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) tmp_watch.Start();
	if ( DEBUG_OFF ) cout << "#vars: " << Current_Component().Vars_Size() << endl;  // ToModify
	BigInt exact = Count_Models_Simple_Component( Current_Component(), _models_stack[_num_levels - 1] );
	assert( exact.LE_2exp( Current_Component().Vars_Size() ) );  // ToModify
	BigFloat exact_num( exact );
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_simply_counting += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) cout << "time simply: " << statistics.time_simply_counting << endl;  // ToRemove
	exact_num.Mul_2exp( NumVars(_max_var) - Current_Component().Vars_Size() );
	_rsl_stack[_num_rsl_stack] = manager.Add_Known_Node( exact_num, Current_Component().caching_loc );
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack] );
	if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack] );
	_num_rsl_stack++;
	Recycle_Models( _models_stack[_num_levels - 1] );
	Backtrack();
}

void Partial_CCDD_Compiler::Backtrack()
{
	_num_levels--;
	_level_ExactMC_failed[_num_levels] = false;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

BigInt Partial_CCDD_Compiler::Count_Models_Simple_Component( Component & comp, vector<Model *> & models, double timeout )
{
	assert( !models.empty() );
	CNF_Formula * cnf = Output_Renamed_Clauses_In_Component( comp );
	vector<Model *> borrowed_models;
	_exact_counter.Set_Max_Var( cnf->Max_Var() );
	_exact_counter.Lend_Models( borrowed_models, models.size() );  // transforming models
	for ( unsigned i = 0; i < models.size(); i++ ) {
		for ( unsigned j = 0; j < comp.Vars_Size(); j++ ) {
			borrowed_models[i]->Assign( Variable(j+1), (*models[i])[comp.Vars(j)] );
		}
	}
	BigInt result = _exact_counter.Count_Models( *cnf, borrowed_models, timeout );
	delete cnf;
	return result;
}

lbool Partial_CCDD_Compiler::Try_Kernelization( Partial_CCDD_Manager & manager )
{
	if ( _current_kdepth >= running_options.max_kdepth ) return lbool(false);
	if ( Estimate_Kernelization_Effect( manager ) == false ) return lbool(false);
	Store_Cached_Binary_Clauses();
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	NodeID old_core;
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.ch[0] == NodeID::top ) {
			_rsl_stack[_num_rsl_stack - 1] = old_id;
			Clear_Cached_Binary_Clauses();
			return lbool::unknown;
		}
		assert( old_node.sym == SEARCH_KERNELIZED );
		Kernelize_Without_Imp( manager );
		Set_Current_Level_Kernelized( true );
		old_core = _component_cache.Read_Result( Current_Component().caching_loc );  /// NOTE: old_node.ch[0] might be out of date, because two distinct nodes may point to the same cache
	}
	else {
		Extensive_Inprocessor::Kernelize_Without_Imp();
		Set_Current_Level_Kernelized( true );
		Sort_Clauses_For_Caching();
		if ( _call_stack[_num_levels - 1].Lit_Equivalences_Size() == 0 ) {  // NOTE: avoid that two components point to the same node
			Clear_Cached_Binary_Clauses();
			Set_Current_Level_Kernelized( false );
			Cancel_Kernelization_Without_Imp();
			Recover_Cached_Binary_Clauses();
			Encode_Long_Clauses();
			return lbool(false);
		}
		if ( Current_Component().Vars_Size() == 0 ) old_core = NodeID::top;
		else {
			old_core = Component_Cache_Map( Current_Component() );
			if ( old_core != NodeID::undef && manager.Node( old_core ).sym == SEARCH_KERNELIZED ) {
				_rsl_stack[_num_rsl_stack++] = old_core;
				Leave_Kernelization( manager );
				_num_rsl_stack--;  /// pop the extra node
				Kernelize_Without_Imp( manager );
				Set_Current_Level_Kernelized( true );
				old_core = manager.Node( old_core ).ch[0];
			}
		}
	}
	bool core_known = false;
	if ( old_core == NodeID::top ) core_known = true;
	else if ( old_core != NodeID::undef && manager.Node( old_core ).sym == SEARCH_KNOWN ) core_known = true;
	if ( core_known ) {
		_rsl_stack[_num_rsl_stack++] = old_core;
		Leave_Kernelization( manager );
		if ( Is_Current_Level_Decision() ) {
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			_rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );
//			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
			Recycle_Models( _models_stack[_num_levels - 1] );
			Backtrack();
		}
		else {
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

bool Partial_CCDD_Compiler::Estimate_Kernelization_Effect( Partial_CCDD_Manager & manager )
{
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		return old_node.sym == SEARCH_KERNELIZED;
	}
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

void Partial_CCDD_Compiler::Kernelize_Without_Imp( Partial_CCDD_Manager & manager )
{
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
	NodeID old_id = _component_cache.Read_Result( comp.caching_loc );
	// first: store the current clauses
	Store_Binary_Clauses_Component( _call_stack[level], comp );
	_call_stack[level].Swap_Long_Clauses( _long_clauses, _old_num_long_clauses );
	_call_stack[level].Swap_Component( comp );
	Clear_Auxiliary_Lists_Subdivision_Long_Component( last_comp );  // need to clear some lists, and _binary_var_membership_lists will be handle separately for efficiency
	// second: load sub-formula
	const Partial_CDD_Node & old_node = manager.Node( old_id );
	const Partial_CDD_Node & old_child = manager.Node( old_node.ch[0] );
	Component_Cache_Load_With_Kernelization( old_child.caching_loc );
	Pick_Original_Binary_Clauses( _call_stack[level], comp );
	Clear_Membership_Lists_Subdivision_Binary_Component( comp );
	if ( DEBUG_OFF ) Verify_Kernelization();  // ToModify
	// third: store literal equivalences
	Recover_Lit_Equivalences( _call_stack[level], old_node );
	// forth: modify auxiliary information
	_fixed_num_vars = _unary_clauses.size();
	_fixed_num_long_clauses = _old_num_long_clauses;
	if ( running_options.profiling_ext_inprocessing >= Profiling_Abstract ) statistics.time_kernelize += begin_watch.Get_Elapsed_Seconds();
	if ( running_options.display_kernelizing_process && running_options.profiling_ext_inprocessing >= Profiling_Detail ) {
		cout << running_options.display_prefix << "kernelization effect: " << Current_Component().Vars_Size() << " vars, " << Current_Component().ClauseIDs_Size() << " long clauses" << endl;
	}
//	Display_Component( comp, cerr );  // ToRemove
}

void Partial_CCDD_Compiler::Component_Cache_Load_With_Kernelization( unsigned loc )
{
	StopWatch tmp_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	_component_cache.Read_Component( loc, _incremental_comp );
	Current_Component().Clear();
	Current_Component().Swap_VarIDs( _incremental_comp );
	unsigned i = 0;
	for ( ; i < _incremental_comp.ClauseIDs_Size(); i++ ) {
		const SortedSet<Literal> & lits = _component_cache.Read_Clause( _incremental_comp.ClauseIDs( i ) );
		if ( lits.size > 2 ) break;
		Add_Binary_Clause_Naive( lits.elems[0], lits.elems[1] );
		if ( lits.elems[0] < lits.elems[1] ) _cached_binary_clauses[lits.elems[0]].push_back( lits.elems[1] );
		else _cached_binary_clauses[lits.elems[1]].push_back( lits.elems[0] );
	}
	assert( _long_clauses.empty() );
	_long_clause_ids.resize( _incremental_comp.ClauseIDs_Size() - i );
	for ( ; i < _incremental_comp.ClauseIDs_Size(); i++ ) {
		unsigned pos = _long_clauses.size();
		SetID id = _incremental_comp.ClauseIDs( i );
		const SortedSet<Literal> & lits = _component_cache.Read_Clause( id );
		assert( lits.size >= 3 );
		_long_clauses.push_back( Clause( lits.elems, lits.size ) );
		_long_clause_ids[pos] = id;
		Current_Component().Add_ClauseID( pos );
	}
	Current_Component().caching_loc = _incremental_comp.caching_loc;
	for ( i = 0; i < Current_Component().Vars_Size(); i++ ) {
		Variable var = Current_Component().Vars( i );
		_old_num_binary_clauses[Literal( var, false )] = _binary_clauses[Literal( var, false )].size();
		_old_num_binary_clauses[Literal( var, true )] = _binary_clauses[Literal( var, true )].size();
	}
	Current_Component().Add_Var( _max_var.Next() );  /// NOTE: prevent Vars() from reallocating memory when push_back mar_var + 1 later
	Current_Component().Dec_Var();  /// pop _max_var.Next()
	_old_num_long_clauses = _long_clauses.size();
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
}

void Partial_CCDD_Compiler::Pick_Original_Binary_Clauses( Stack_Frame & frame, Component & comp )
{
	for ( unsigned i = 0; i < frame.Binary_Clauses_Size(); i++ ) {
		Literal lit = frame.Binary_Clauses_First( i );
		Literal lit2 = frame.Binary_Clauses_Second( i );
		if ( !comp.Search_Var( lit.Var() ) || !comp.Search_Var( lit2.Var() ) ) continue;
		_binary_clauses[lit].push_back( lit2 );
		_binary_clauses[lit2].push_back( lit );
		_old_num_binary_clauses[lit]++;
		_old_num_binary_clauses[lit2]++;
	}
	for ( unsigned i = 0; i < frame.Binary_Learnts_Size(); i++ ) {
		Literal lit = frame.Binary_Learnts_First( i );
		Literal lit2 = frame.Binary_Learnts_Second( i );
		if ( !comp.Search_Var( lit.Var() ) || !comp.Search_Var( lit2.Var() ) ) continue;
		_binary_clauses[lit].push_back( lit2 );
		_binary_clauses[lit2].push_back( lit );
	}
}

void Partial_CCDD_Compiler::Recover_Lit_Equivalences( Stack_Frame & frame, const Partial_CDD_Node & node )
{
	assert( node.sym == SEARCH_KERNELIZED );
	for ( unsigned i = 0; i < node.imp_size; i += 2 ) {
		frame.Add_Lit_Equivalence( node.imp[i], node.imp[i + 1] );
	}
}

void Partial_CCDD_Compiler::Sort_Clauses_For_Caching()
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

void Partial_CCDD_Compiler::Sort_Long_Clauses_By_IDs()
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

void Partial_CCDD_Compiler::Encode_Long_Clauses()
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

void Partial_CCDD_Compiler::Leave_Kernelization( Partial_CCDD_Manager & manager )
{
	if ( !_call_stack[_num_levels - 1].Existed() ) return;
	_rsl_stack[_num_rsl_stack - 1] = Make_Kernelized_Conjunction_Node( manager, _rsl_stack[_num_rsl_stack - 1] );  // NOTE: caching_loc is wrong
	Clear_Cached_Binary_Clauses();
	Set_Current_Level_Kernelized( false );
	Cancel_Kernelization_Without_Imp();
	Recover_Cached_Binary_Clauses();
	Encode_Long_Clauses();
	assert( manager.Node( _rsl_stack[_num_rsl_stack - 1] ).sym == SEARCH_KERNELIZED );
	manager.Cache_Location( _rsl_stack[_num_rsl_stack - 1] ) = Current_Component().caching_loc;
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
}

void Partial_CCDD_Compiler::Extend_New_Level( Partial_CCDD_Manager & manager )
{
	Variable var;
	bool sign;
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		var = Variable( old_node.sym );
		assert( Variable::start <= var && var <= _max_var );
		assert( Var_Undecided( var ) );
		if ( Is_Level_Decision( _num_levels - 1 ) ) Recycle_Models( _models_stack[_num_levels - 1] );
		sign = Dice_Var_Adaptive( manager, old_id );
		_state_stack[_num_levels - 1]++;
		Extend_New_Level();
		assert( _models_stack[_num_levels - 1].empty() );
		const Partial_CDD_Node & old_child = manager.Node( old_node.ch[sign] );
		if ( old_child.sym == SEARCH_UNKNOWN ) {
			manager.Swap_Unknown_Models( old_node.ch[sign], _models_stack[_num_levels - 1] );
			for ( Model * model: _models_stack[_num_levels - 1] ) {
				assert( (*model)[var] == sign );
			}
		}
	}
	else {
		var = Pick_Good_Var_Component( Current_Component() );
		sign = Dice_Var( var, _var_distribution[var], Current_Component() );
		_state_stack[_num_levels - 1]++;
		Extend_New_Level();
		if ( Is_Level_Decision( _num_levels - 2 ) ) {
			Pick_Models( _models_stack[_num_levels - 2], Literal(var, sign), _models_stack[_num_levels - 1] );
		}
		else Inherit_Models( _models_stack[_num_levels - 2], Literal(var, sign), _models_stack[_num_levels - 1] );
	}
	Assign( Literal(var, sign) );
}

void Partial_CCDD_Compiler::Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	_comp_offsets[_num_levels] = _num_comp_stack;
	_active_comps[_num_levels] = _comp_offsets[_num_levels];
	_state_stack[_num_levels++] = 0;
}

bool Partial_CCDD_Compiler::Dice_Var_Adaptive( Partial_CCDD_Manager & manager, NodeID n )
{
	const Partial_CDD_Node & node = manager.Node(n);
	const unsigned sparse_threshold = 1;  // whether child has enough frequency
	if ( !running_options.adaptive_sampling || node.freq[0] <= sparse_threshold || node.freq[1] <= sparse_threshold ) {
		return manager.Sample( _rand_gen, n );  // probability of true
	}
	const unsigned adaptive_threshold = 200;  // NOTE: adaptive_threshold / 2 must be greater than rebanlance_threshold
	const unsigned rebanlance_threshold = 40;  // NOTE: rebanlance_threshold / 2 must be not less than sparse_threshold
	unsigned total_freq = node.freq[0] + node.freq[1];
	if ( total_freq < rebanlance_threshold ) {
		return manager.Sample( _rand_gen, n );  // probability of true
	}
	if ( total_freq < adaptive_threshold ) {
		bool ws = manager.Node(node.ch[0]).weight >= manager.Node(node.ch[1]).weight;  // ws --> weight sign
		bool es = node.estimate < 0.5;  // es --> estimate sign
		if ( ( ws && !es ) || ( !ws && es ) ) {
			return manager.Sample_Adaptive( _rand_gen, n, 0.5 );
		}
		else return manager.Sample( _rand_gen, n );  // probability of true
	}
	else {
		BigFloat ratio = manager.Node(node.ch[0]).weight;
		ratio /= manager.Node(node.ch[1]).weight;
		double prob = ratio.TransformDouble();
		prob = 1 / (1 + prob);  // NOTE: x / (x + y) = 1 / (1 + y / x)
		prob = ( prob + node.estimate ) / 2;  // median value
		if ( prob > 0.9 ) prob = 0.9;
		else if ( prob < 0.1 ) prob = 0.1;
		return manager.Sample_Adaptive( _rand_gen, n, prob ); // probability of true
	}
}

bool Partial_CCDD_Compiler::Dice_Var( Variable var, double & prob, Component & comp )
{
	if ( !running_options.estimate_marginal_probability ) {
		prob = 0.5;
		return _rand_gen.Generate_Bool( prob );
	}
	else {
		prob = Estimate_Posterior_Probability( var, comp );
		return _rand_gen.Generate_Bool( prob );  // probability of true
	}
}

double Partial_CCDD_Compiler::Estimate_Posterior_Probability( Variable var, Component & comp )
{
	assert( comp.Search_Var( var ) );
	StopWatch begin_watch, tmp_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	const unsigned projected_size = Projected_Size_For_Estimation( comp );
	vector<unsigned> weights( comp.Vars_Size() - 1 );
	unsigned i;
	for ( i = 0; comp.Vars(i) != var; i++ ) {
		weights[i] = _var_order.Rank(comp.Vars(i));
	}
	for ( i++; i < comp.Vars_Size(); i++ ) {
		weights[i-1] = _var_order.Rank(comp.Vars(i));
	}
	First_k_Elements( weights, projected_size - 1 );
	_projected_vars.resize( projected_size );
	_projected_vars[0] = var;
	_var_projected[var] = true;
	unsigned min_weight = _var_order.Rank(var);
	for ( i = 0; i < projected_size - 1; i++ ) {
		if ( min_weight > weights[i] ) min_weight = weights[i];
		_projected_vars[i + 1] = Variable(_var_order[weights[i]]);
		_var_projected[_var_order[weights[i]]] = true;
	}
	Variable first_var( _var_order[min_weight] );
	_var_order.Swap( var, first_var );
	assert( _pmc_component_cache.Size() == 0 );
	Extend_New_Level();
	_state_stack[_num_levels - 1] = 1;
	_comp_stack[_num_comp_stack++] = comp;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	_pmc_component_cache.Init( _max_var, _old_num_long_clauses, -1 );
	_pmc_component_cache.Hit_Component( _comp_stack[_num_comp_stack - 1] );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_cnf_cache += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) debug_options.verify_component_count = comp.Vars_Size() <= _projected_vars.size();
	Implicate_Computing_Strategy old_strategy = running_options.imp_strategy;
	if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) {
		running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		Estimate_Posterior_Probability_With_Implicite_BCP();
	}
	else if ( true ) {
		running_options.imp_strategy = Partial_Implicit_BCP_Neg;
		if ( Is_Level_Decision( _num_levels - 2 ) ) {
			Estimate_Posterior_Probability_With_Implicite_BCP_Opt();
		}
		else Estimate_Posterior_Probability_With_Implicite_BCP();  /// NOTE: cannot reuse the generated models for decomposition level
	}
	else {
		running_options.imp_strategy = SAT_Imp_Computing;
		Estimate_Posterior_Probability_With_SAT_Imp_Computing();
	}
	_pmc_component_cache.Reset();
	running_options.imp_strategy = old_strategy;
	_var_order.Swap( var, first_var );
	_var_projected[var] = false;
	for ( i = 0; i < projected_size - 1; i++ ) {
		_var_projected[_var_order[weights[i]]] = false;
	}
	double prob = _pmc_rsl_stack[1] / _pmc_rsl_stack[0];
	_num_pmc_rsl_stack--;
	if ( prob > 0.9 ) prob = 0.9;
	else if ( prob < 0.1 ) prob = 0.1;
//	cerr << "probability[" << var << "] = " << prob << endl;  // ToRemove
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_estimate_marginal_probability += tmp_watch.Get_Elapsed_Seconds();
	return prob;
}

unsigned Partial_CCDD_Compiler::Projected_Size_For_Estimation( Component & comp )
{
	if ( comp.Vars_Size() <= 20 ) return comp.Vars_Size();
	unsigned hard_factor = 0;
	if ( running_options.treewidth > 128 ) {
		if ( _unsimplifiable_num_vars > 1024 * 8 ) hard_factor = 4;
		else if ( _unsimplifiable_num_vars > 1024 * 4 ) hard_factor = 3;
		else if ( _unsimplifiable_num_vars > 1024 * 2 ) hard_factor = 2;
		else if ( _unsimplifiable_num_vars > 1024 ) hard_factor = 1;
	}
	if ( comp.Vars_Size() >= 8192 || comp.ClauseIDs_Size() >= 16384 ) return 14 - hard_factor;
	else if ( comp.Vars_Size() >= 4096 || comp.ClauseIDs_Size() >= 8192 ) return 15 - hard_factor;
	else if ( comp.Vars_Size() >= 2048 || comp.ClauseIDs_Size() >= 4096 ) return 16 - hard_factor;
	else if ( comp.Vars_Size() >= 1024 || comp.ClauseIDs_Size() >= 2048 ) return 17 - hard_factor;
	else if ( comp.Vars_Size() >= 512 || comp.ClauseIDs_Size() >= 1024 ) return 18 - hard_factor;
	else if ( comp.Vars_Size() >= 256 || comp.ClauseIDs_Size() >= 512 ) return 19 - hard_factor;
	else return 20 - hard_factor;  // NOTE: 20 is a bit expensive for many instances
}

void Partial_CCDD_Compiler::Estimate_Posterior_Probability_With_Implicite_BCP()
{
	unsigned old_num_levels = _num_levels;
	unsigned old_num_pmc_rsl_stack = _num_pmc_rsl_stack;
	Variable picked_var;
	double cached_result;
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
				if ( Learnts_Exploded() ) Filter_Long_Learnts();
				backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					Backjump_Decision_PMC( backjump_level );
					break;
				}
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Backtrack_True_PMC();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_PMC( Current_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						Backtrack_Known_PMC( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				picked_var = Pick_Good_Projected_Var_Linearly_Component( Current_Component() );
				if ( picked_var == Variable::undef ) {
					Backtrack_True_PMC();
				}
				else {
					Extend_New_Level();
					Assign( Literal( picked_var, false ) );
				}
				break;
			case 2:
				if ( _pmc_rsl_stack[_num_pmc_rsl_stack - 1] != 0 ) {
					_state_stack[_num_levels - 1]++;
					Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
				}
				else {
					_num_pmc_rsl_stack--;  // pop 0
					_num_comp_stack = _comp_offsets[_num_levels - 1];  // re-decompose
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );  // reason is assigned in the last iteration
				}
				break;
			case 3:
				Backtrack_Decision_PMC();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_PMC( Current_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
						Iterate_Known_PMC( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						picked_var = Pick_Good_Projected_Var_Linearly_Component( Current_Component() );
						if ( picked_var == Variable::undef ) {
							Iterate_True_PMC();
							_state_stack[_num_levels - 1] += 2;
						}
						else {
							Extend_New_Level();
							Assign( Literal( picked_var, false ) );
						}
					}
					break;
				case 1:
					if ( _pmc_rsl_stack[_num_pmc_rsl_stack - 1] != 0 ) {
						Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_pmc_rsl_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
						backjump_reason = Get_Approx_Imp_Component( Current_Component(), backjump_level );  /// current component rather than parent component
						if ( backjump_reason != Reason::undef ) {
							Backjump_Decomposition_PMC( backjump_level );
							break;
						}
						unsigned num_comp = Dynamic_Decompose_Component( Current_Component(), _comp_stack + _num_comp_stack );
						_num_comp_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Component() = _comp_stack[_num_comp_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							Backtrack_PMC();  // overwrite the result of the only one component
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_comps[_num_levels - 1] == _num_comp_stack - 1 );
							cached_result = Component_Cache_Map_PMC( Current_Component() );  /// NOTE: the current component was after the collapsed one
							if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
								Backtrack_Known_PMC( cached_result );
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					Iterate_Decision_PMC();
					break;
				}
			}
			else {  // all components are already processed
				Backtrack_Decomposition_PMC();
			}
		}
	}
	assert( _num_pmc_rsl_stack == old_num_pmc_rsl_stack + 1 );
}

void Partial_CCDD_Compiler::Backjump_Decision_PMC( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_pmc_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else {
			_num_pmc_rsl_stack -= _state_stack[_num_levels - 1] % 3 - 1;  // ToCheck in other files
			_num_pmc_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
		}
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
	_pmc_rsl_stack[_num_pmc_rsl_stack++] = 0;  /// NOTE: cannot omit when in the second decision, and need to be AFTER backjump
}

void Partial_CCDD_Compiler::Backtrack_True_PMC()
{
	_pmc_rsl_stack[_num_pmc_rsl_stack] = 1;
	unsigned num_assigned = Num_Projected_Vars_Assigned( _dec_offsets[_num_levels - 1] + 1 );
	Shift_Left_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], _projected_vars.size() - num_assigned );
	_num_pmc_rsl_stack++;
	Backtrack_PMC();
}

double Partial_CCDD_Compiler::Component_Cache_Map_PMC( Component & comp )
{
	StopWatch begin_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	comp.caching_loc = _pmc_component_cache.Hit_Component( comp );
	if ( DEBUG_OFF && comp.caching_loc == 9 ) {  // ToRemove
		comp.Display( cerr );
		Display_Component( comp, cerr );
	}
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += begin_watch.Get_Elapsed_Seconds();
	return _pmc_component_cache.Read_Result( comp.caching_loc );
}

void Partial_CCDD_Compiler::Backtrack_Known_PMC( double known_result )
{
	if ( debug_options.verify_component_count ) {
		double tmp_result = known_result;
		Shift_Left_Unsafe( tmp_result, NumVars(_max_var) - _projected_vars.size() );
		Verify_Result_Component( Current_Component(), tmp_result );
	}
	_pmc_rsl_stack[_num_pmc_rsl_stack] = known_result;
	unsigned num_assigned = Num_Projected_Vars_Assigned( _dec_offsets[_num_levels - 1] + 1 );
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], num_assigned );
	_num_pmc_rsl_stack++;
	Backtrack_PMC();
}

void Partial_CCDD_Compiler::Backtrack_PMC()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
}

void Partial_CCDD_Compiler::Backtrack_Decision_PMC()
{
	assert( _num_pmc_rsl_stack > 1 );
	assert( _pmc_rsl_stack[_num_pmc_rsl_stack - 2] != 0 );  // backjump guarantees this
//	cerr << _pmc_rsl_stack[_num_pmc_rsl_stack - 2] << " vs " << _pmc_rsl_stack[_num_pmc_rsl_stack - 1] << endl;  // ToRemove
	_num_pmc_rsl_stack--;
	_pmc_rsl_stack[_num_pmc_rsl_stack - 1] += _pmc_rsl_stack[_num_pmc_rsl_stack];
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack - 1], 1 );
	if ( debug_options.verify_component_count ) {
		double tmp_result = _pmc_rsl_stack[_num_pmc_rsl_stack - 1];
		Shift_Left_Unsafe( tmp_result, NumVars(_max_var) - _projected_vars.size() );
		Verify_Result_Component( Current_Component(), tmp_result );
	}
	_pmc_component_cache.Write_Result( Current_Component().caching_loc, _pmc_rsl_stack[_num_pmc_rsl_stack - 1] );
	unsigned num_assigned = Num_Projected_Vars_Assigned( _dec_offsets[_num_levels - 1] + 1 );
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack - 1], num_assigned );
	Backtrack_PMC();
}

void Partial_CCDD_Compiler::Iterate_Known_PMC( double known_result )
{
	if ( debug_options.verify_component_count ) {
		double tmp_result = known_result;
		Shift_Left_Unsafe( tmp_result, NumVars(_max_var) - _projected_vars.size() );
		Verify_Result_Component( Current_Component(), tmp_result );
	}
	_pmc_rsl_stack[_num_pmc_rsl_stack++] = known_result;
	_active_comps[_num_levels - 1]++;
}

void Partial_CCDD_Compiler::Iterate_True_PMC()
{
	_pmc_rsl_stack[_num_pmc_rsl_stack] = 1;
	Shift_Left_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], _projected_vars.size() );
	_num_pmc_rsl_stack++;
	_active_comps[_num_levels - 1]++;
}

void Partial_CCDD_Compiler::Backjump_Decomposition_PMC( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	_num_pmc_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( _comp_offsets[_num_levels] - _comp_offsets[_num_levels - 1] <= 1 ) _num_pmc_rsl_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else {
			_num_pmc_rsl_stack -= _state_stack[_num_levels - 1] % 3 - 1;  // ToCheck in other files
			_num_pmc_rsl_stack -= _active_comps[_num_levels - 1] - _comp_offsets[_num_levels - 1];
		}
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_comp_stack = _comp_offsets[_num_levels];
	_pmc_rsl_stack[_num_pmc_rsl_stack++] = 0;  /// NOTE: cannot omit when in the second decision, and need to be AFTER backjump
}

void Partial_CCDD_Compiler::Iterate_Decision_PMC()
{
	assert( _num_pmc_rsl_stack > 1 );
	assert( _pmc_rsl_stack[_num_pmc_rsl_stack - 2] != 0 );  // backjump guarantees this
	_num_pmc_rsl_stack--;
	_pmc_rsl_stack[_num_pmc_rsl_stack - 1] += _pmc_rsl_stack[_num_pmc_rsl_stack];
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack - 1], 1 );
	if ( debug_options.verify_component_count ) {
		double tmp_result = _pmc_rsl_stack[_num_pmc_rsl_stack - 1];
		Shift_Left_Unsafe( tmp_result, NumVars(_max_var) - _projected_vars.size() );
		Verify_Result_Component( Current_Component(), tmp_result );
	}
	_pmc_component_cache.Write_Result( Current_Component().caching_loc, _pmc_rsl_stack[_num_pmc_rsl_stack - 1] );
	_active_comps[_num_levels - 1]++;
}

void Partial_CCDD_Compiler::Backtrack_Decomposition_PMC()
{
	_num_pmc_rsl_stack -= Num_Components_On_Current_Level();
	assert( _num_levels > 2 );  // not decompose the initial formula
	_pmc_rsl_stack[_num_pmc_rsl_stack] *= _pmc_rsl_stack[_num_pmc_rsl_stack + 1];
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], _projected_vars.size() );
	for ( unsigned i = 2; i < Num_Components_On_Current_Level(); i++ ) {
		_pmc_rsl_stack[_num_pmc_rsl_stack] *= _pmc_rsl_stack[_num_pmc_rsl_stack + i];
		Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], _projected_vars.size() );
	}
	unsigned num_assigned = Num_Projected_Vars_Assigned( _dec_offsets[_num_levels - 1] + 1 );
	Shift_Right_Unsafe( _pmc_rsl_stack[_num_pmc_rsl_stack], num_assigned );
	_num_pmc_rsl_stack++;
	Backtrack_PMC();
}

void Partial_CCDD_Compiler::Estimate_Posterior_Probability_With_Implicite_BCP_Opt()
{
	assert( Is_Level_Decision( _num_levels - 2 ) );
	unsigned old_num_levels = _num_levels;
	unsigned old_num_dec_stack = _num_dec_stack;
	unsigned old_num_comp_stack = _num_comp_stack;
	Variable picked_var;
	Current_Component().Add_Var( _max_var.Next() );
	Current_Component().Dec_Var();
	Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		switch ( _state_stack[_num_levels - 1] ) {
		case 0:
			Get_All_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );
			_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
			if ( Is_Current_Level_Empty() ) {
				Backtrack_True_PMC();
				break;
			}
			else if ( Is_Current_Level_Decision() ) _state_stack[_num_levels - 1]++;
			else _state_stack[_num_levels - 1] = 0;
			Estimate_Posterior_Probability_With_Implicite_BCP();
			break;
		case 1:
			_state_stack[_num_levels - 1]++;
			picked_var = Pick_Good_Projected_Var_Linearly_Component( Current_Component() );
			Extend_New_Level();
			Pick_Models( _models_stack[_num_levels - 2], Literal( picked_var, false ), _models_stack[_num_levels - 1] );
			Assign( Literal( picked_var, false ) );
			break;
		case 2:
			assert( _pmc_rsl_stack[_num_pmc_rsl_stack - 1] != 0 );
			_state_stack[_num_levels - 1]++;
			Extend_New_Level();
			Swap_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
			Assign( ~_dec_stack[_num_dec_stack] );
			break;
		case 3:
			Move_Models( _models_stack[_num_levels], _models_stack[_num_levels - 1] );
			Backtrack_Decision_PMC();
			break;
		}
	}
	assert( _num_dec_stack == old_num_dec_stack && _num_comp_stack == old_num_comp_stack - 1 );
	assert( _num_pmc_rsl_stack == 1 );
	Move_Models( _models_stack[_num_levels], _models_stack[_num_levels - 1] );
}

void Partial_CCDD_Compiler::Estimate_Posterior_Probability_With_SAT_Imp_Computing()
{
	assert( Is_Level_Decision( _num_levels - 2 ) );
	unsigned old_num_levels = _num_levels;
	unsigned old_num_dec_stack = _num_dec_stack;
	unsigned old_num_comp_stack = _num_comp_stack;
	Variable picked_var;
	double cached_result;
	Current_Component().Add_Var( _max_var.Next() );
	Current_Component().Dec_Var();
	Copy_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Component(), cerr );  // ToRemove
			else Display_Component( Current_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
//		Debug_Print_Visit_Number( cerr, __LINE__ );
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation
			switch ( _state_stack[_num_levels - 1] ) {
			case 0:
				Get_All_Projected_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );
				_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack_True_PMC();
				}
				else if ( Is_Current_Level_Decision() ) {
					cached_result = Component_Cache_Map_PMC( Current_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						Recycle_Models( _models_stack[_num_levels - 1] );
						Backtrack_Known_PMC( cached_result );
					}
					else _state_stack[_num_levels - 1]++;
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++;
				picked_var = Pick_Good_Projected_Var_Linearly_Component( Current_Component() );
				if ( picked_var == Variable::undef ) {
					Recycle_Models( _models_stack[_num_levels - 1] );
					Backtrack_True_PMC();
				}
				else {
					Extend_New_Level();
					Pick_Models( _models_stack[_num_levels - 2], Literal( picked_var, false ), _models_stack[_num_levels - 1] );
					Assign( Literal( picked_var, false ) );
				}
				break;
			case 2:
				assert( _pmc_rsl_stack[_num_pmc_rsl_stack - 1] != 0 );
				_state_stack[_num_levels - 1]++;
				Extend_New_Level();
				Move_Models( _models_stack[_num_levels - 2], _models_stack[_num_levels - 1] );
				Assign( ~_dec_stack[_num_dec_stack] );
				break;
			case 3:
				assert( _models_stack[_num_levels - 1].empty() );
				Backtrack_Decision_PMC();
				break;
			}
		}
		else { // decomposition
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					cached_result = Component_Cache_Map_PMC( Current_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
						Iterate_Known_PMC( cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						picked_var = Pick_Good_Projected_Var_Linearly_Component( Current_Component() );
						if ( picked_var == Variable::undef ) {
							Iterate_True_PMC();
							_state_stack[_num_levels - 1] += 2;
						}
						else {
							Extend_New_Level();
							Inherit_Models( _models_stack[_num_levels - 2], Literal( picked_var, false ), _models_stack[_num_levels - 1] );
							Assign( Literal( picked_var, false ) );
						}
					}
					break;
				case 1:
					assert( _pmc_rsl_stack[_num_pmc_rsl_stack - 1] != 0 );
					Extend_New_Level();
					Inherit_Models( _models_stack[_num_levels - 2], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels - 1] );
					Assign( ~_dec_stack[_num_dec_stack] );
					break;
				case 2:
					Iterate_Decision_PMC();
					break;
				}
			}
			else {  // all components are already processed
				Recycle_Models( _models_stack[_num_levels - 1] );
				Backtrack_Decomposition_PMC();
			}
		}
	}
	assert( _num_dec_stack == old_num_dec_stack && _num_comp_stack == old_num_comp_stack - 1 );
	assert( _num_pmc_rsl_stack == 1 );
}

void Partial_CCDD_Compiler::Restart_Decision_PMC( Reason reason, unsigned level )
{
	assert( level < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( unsigned i = _num_levels - 1; i > level; i-- ) {
		if ( _comp_offsets[i] - _comp_offsets[i - 1] <= 1 ) _num_pmc_rsl_stack -= _state_stack[i - 1] - 2;  // ToCheck
		else {
			_num_pmc_rsl_stack -= _state_stack[i - 1] % 3 - 1;  // ToCheck in other files
			_num_pmc_rsl_stack -= _active_comps[i - 1] - _comp_offsets[i - 1];
		}
		Un_BCP( _dec_offsets[i] );
		Raise_Models( _models_stack[i], level );
	}
	_num_comp_stack = _comp_offsets[level];
	_active_comps[level] = _comp_offsets[level];
	_state_stack[level] = 0;
	_num_levels = level + 1;
	Assign( _big_learnt[0], reason );
}

void Partial_CCDD_Compiler::Backtrack_Decision( Partial_CCDD_Manager & manager )
{
	bool sign = _dec_stack[_num_dec_stack].Sign();
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef && manager.Node( old_id ).sym != SEARCH_UNKNOWN ) {
		assert( _models_stack[_num_levels - 1].empty() );
		_rsl_stack[_num_rsl_stack - 1] = manager.Update_Decision_Child( old_id, sign, _rsl_stack[_num_rsl_stack - 1] );
	}
	else {
		assert( !_models_stack[_num_levels - 1].empty() );
		NodeID ch[2];
		ch[sign] = _rsl_stack[_num_rsl_stack - 1];
		ch[!sign] = Make_Unknown_Node( manager,  _models_stack[_num_levels - 1] );
		_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, ch[0], ch[1] );
	}
	if ( debug_options.verify_component_compilation ) {
		Verify_Result_Bound( Current_Component(), manager.Node(_rsl_stack[_num_rsl_stack - 1]).weight );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	Leave_Kernelization( manager );
	if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack - 1] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack - 1] );
	Backtrack();
}

NodeID Partial_CCDD_Compiler::Make_Unknown_Node( Partial_CCDD_Manager & manager, vector<Model *> & models )
{
	if ( _store_one_model ) {
		vector<Model *>::iterator end = models.end();
		for ( vector<Model *>::iterator itr = models.begin() + 1; itr < end; itr++ ) {
			_model_pool->Free( *itr );
		}
		models.resize( 1 );
		models.shrink_to_fit();  // save memory for the latter swapping
	}
	return manager.Add_Unknown_Node( models );
}

NodeID Partial_CCDD_Compiler::Make_Decision_Node( Partial_CCDD_Manager & manager, NodeID low, NodeID high )
{
//	Debug_Print_Visit_Number( cerr, __FUNCTION__, __LINE__ );  // ToRemove
	StopWatch begin_watch;
	assert( low != NodeID::bot );  // backjump guarantees this
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	Variable var = _dec_stack[_num_dec_stack].Var();
	Partial_Decision_Node bnode( var, low, high, _var_distribution[var] );
	NodeID result = manager.Add_Decision_Node( bnode, Current_Component().caching_loc );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_component_compilation ) {
//		Verify_Result_Component( Current_Component(), manager, result );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, result );
	if ( manager.Num_Nodes() >= _node_redundancy_factor * running_options.removing_redundant_nodes_trigger ) {
		unsigned old_size = manager.Num_Nodes();
		Remove_Redundant_Nodes( manager );
		unsigned new_size = manager.Num_Nodes();
		result = _component_cache.Read_Result( Current_Component().caching_loc );
		if ( old_size - new_size < running_options.removing_redundant_nodes_trigger / 2000 ) _node_redundancy_factor *= 3;
		else if ( old_size - new_size < running_options.removing_redundant_nodes_trigger / 200 ) _node_redundancy_factor *= 2;
		else _node_redundancy_factor *= 1.5;
	}
	return result;
}

void Partial_CCDD_Compiler::Remove_Redundant_Nodes( Partial_CCDD_Manager & manager )
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

void Partial_CCDD_Compiler::Iterate_Trivial( Partial_CCDD_Manager & manager )
{
	StopWatch tmp_watch;
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.sym != SEARCH_UNKNOWN ) {
			assert( old_node.sym == SEARCH_KNOWN );
			_rsl_stack[_num_rsl_stack++] = old_id;
			_active_comps[_num_levels - 1]++;
			_state_stack[_num_levels - 1] += 2;
			return;
		}
	}
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) tmp_watch.Start();
	if ( DEBUG_OFF ) cout << "#vars: " << Current_Component().Vars_Size() << endl;  // ToModify
	BigInt exact = Count_Models_Simple_Component( Current_Component(), _models_stack[_num_levels - 1] );
	BigFloat exact_num( exact );
	assert( exact_num.LE_2exp( Current_Component().Vars_Size() ) );  // ToModify
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_simply_counting += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) cout << "time simply: " << statistics.time_simply_counting << endl;  // ToRemove
	exact_num.Mul_2exp( NumVars(_max_var) - Current_Component().Vars_Size() );
	_rsl_stack[_num_rsl_stack] = manager.Add_Known_Node( exact_num, Current_Component().caching_loc );
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack] );
	_num_rsl_stack++;
	_active_comps[_num_levels - 1]++;
	_state_stack[_num_levels - 1] += 2;
}

void Partial_CCDD_Compiler::Iterate_Decision( Partial_CCDD_Manager & manager )
{
	bool sign = _dec_stack[_num_dec_stack].Sign();
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef && manager.Node( old_id ).sym != SEARCH_UNKNOWN ) {
		_rsl_stack[_num_rsl_stack - 1] = manager.Update_Decision_Child( old_id, sign, _rsl_stack[_num_rsl_stack - 1] );
	}
	else {
		assert( !_models_stack[_num_levels - 1].empty() );
		NodeID ch[2];
		Inherit_Models( _models_stack[_num_levels - 1], ~_dec_stack[_num_dec_stack], _models_stack[_num_levels] );
		ch[sign] = _rsl_stack[_num_rsl_stack - 1];
		ch[!sign] = Make_Unknown_Node( manager, _models_stack[_num_levels] );
		_rsl_stack[_num_rsl_stack - 1] = Make_Decision_Node( manager, ch[0], ch[1] );
	}
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack - 1] );
	if ( debug_options.verify_component_compilation ) {
		Verify_Result_Bound( Current_Component(), manager.Node(_rsl_stack[_num_rsl_stack - 1]).weight );
	}
	Leave_Kernelization( manager );
	_active_comps[_num_levels - 1]++;
	_state_stack[_num_levels - 1]++;
}

void Partial_CCDD_Compiler::Backtrack_Decomposition( Partial_CCDD_Manager & manager )
{
	_num_rsl_stack -= Num_Components_On_Current_Level();
	assert( _num_levels > 2 );  // not decompose the initial formula
//	manager.Display_Stat( cerr );  // ToRemove
//	Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	_rsl_stack[_num_rsl_stack] = Make_Node_With_Imp( manager, _rsl_stack + _num_rsl_stack, Num_Components_On_Current_Level() );
//	Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	_num_rsl_stack++;
	Recycle_Models( _models_stack[_num_levels - 1] );
	Backtrack();
}

NodeID Partial_CCDD_Compiler::Make_Node_With_Imp( Partial_CCDD_Manager & manager, NodeID * nodes, unsigned num )
{
	StopWatch begin_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) begin_watch.Start();
	_pcdd_rnode.sym = SEARCH_DECOMPOSED;
	_pcdd_rnode.Update( _dec_stack + _dec_offsets[_num_levels - 1] + 1, Num_Current_Imps() );
	_pcdd_rnode.Update( nodes, num );
	NodeID result = manager.Add_Decomposition_Node( _pcdd_rnode );
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void Partial_CCDD_Compiler::Verify_Result_Bound( Component & comp, BigFloat result )
{
	CNF_Formula * cnf = Output_Renamed_Clauses_In_Component( comp );
	BigInt num = _exact_counter.Count_Models( *cnf );
	delete cnf;
	BigFloat exact( num );
	result.Div_2exp( NumVars(_max_var) - comp.Vars_Size() );
	if ( result > exact * 1000 ) {
		cerr << result << " vs " << exact << endl;
		cerr << "Warning[Partial_CCDD_Compiler]: this assert holds with probability 0.1% according to Markov\'s inequality" << endl;
		assert( false );
	}
	if ( result < exact / 1000 ) {
		cerr << result << " vs " << exact << endl;
		cerr << "Warning[Partial_CCDD_Compiler]: this assert holds with probability 0.1% according to Markov\'s inequality" << endl;
		assert( false );
	}
}

void Partial_CCDD_Compiler::Verify_Result_Component( Component & comp, double count )
{
	CNF_Formula * cnf = Output_Original_Clauses_In_Component( comp );
	BigInt verified_count = Count_Verified_Models_d4( *cnf );
	if ( verified_count > 1.001 * count || verified_count < count / 1.001 ) {
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

void Partial_CCDD_Compiler::Display_Statistics( unsigned option )
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
			cout << running_options.display_prefix << "time compute tree decomposition: " << statistics.time_tree_decomposition << endl;
			cout << running_options.display_prefix << "time SAT: " << statistics.time_solve << endl;
			cout << running_options.display_prefix << "time dynamic decomposition: " << statistics.time_dynamic_decompose << " (" << statistics.time_dynamic_decompose_sort << " sorting)" << endl;
			cout << running_options.display_prefix << "time cnf cache: " << statistics.time_gen_cnf_cache << endl;
			cout << running_options.display_prefix << "time kernelize: " << statistics.time_kernelize
				<< " (block lits: " << statistics.time_kernelize_block_lits
				<< "; vivi: " << statistics.time_kernelize_vivification
				<< "; equ: " << statistics.time_kernelize_lit_equ << ")";
			cout << " (max kdepth: " << statistics.max_non_trivial_kdepth << "/" << statistics.max_kdepth
				<< "; #kernelizations: " << statistics.num_non_trivial_kernelizations << "/" << statistics.num_kernelizations << ")" << endl;
			cout << running_options.display_prefix << "time generate estimate marginal: " << statistics.time_estimate_marginal_probability << endl;
			cout << running_options.display_prefix << "time IBCP: " << statistics.time_ibcp << endl;
			cout << running_options.display_prefix << "time simply counting: " << statistics.time_simply_counting << endl;
			cout << running_options.display_prefix << "time generate DAG: " << statistics.time_gen_dag << endl;
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			cout << running_options.display_prefix << "number of (binary) learnt clauses: " << statistics.num_binary_learnt << "/" << statistics.num_learnt << endl;
			cout << running_options.display_prefix << "number of (useful) sat calls: " << statistics.num_unsat_solve << "/" << Inprocessor::statistics.num_solve << endl;
			break;
		case 10:  // sharpSAT
			cout << running_options.display_prefix << "Total time cost: " << statistics.time_compile << endl;
			break;
		default:
			cerr << "ERROR[Partial_CCDD_Compiler]: this display mode is not existing!" << endl;
			assert( false );
			exit( 0 );
	}
	statistics.Init_Compiler();
}

void Partial_CCDD_Compiler::Display_Memory_Status( ostream & out )
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

void Partial_CCDD_Compiler::Display_Result_Stack( ostream & out )
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

void Partial_CCDD_Compiler::Display_Result_Statistics( ostream & out, Partial_CCDD_Manager & manager, NodeID cdd )
{
	out << running_options.display_prefix << "Number of nodes: " << manager.Num_Nodes( cdd ) << endl;
	out << running_options.display_prefix << "Number of edges: " << manager.Num_Edges( cdd ) << endl;
}

BigFloat Partial_CCDD_Compiler::Count_Models_Approximately( CNF_Formula & cnf, Heuristic heur )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_compiling_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	assert( running_options.sampling_count > 0 );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( _fixed_num_vars >= 32 ) Shrink_Max_Var();
	if ( _models_stack[0].empty() ) Generate_Models_External( _models_stack[0] );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
			cout << running_options.display_prefix << "The final model count: " << 0 << endl;
		}
		Reset();
		return 0;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		Un_BCP( _dec_offsets[--_num_levels] );
		_call_stack[0].Clear_Lit_Equivalences();
		BigFloat result;
		result.Assign_2exp( NumVars( _max_var ) - _fixed_num_vars );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
			cout << running_options.display_prefix << "The final model count: " << result << endl;
		}
		Reset();
		return result;
	}
	Gather_Infor_For_Counting();
	Choose_Counting_Options( heur );
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close ) running_options.Display( cout );  // ToRemove
	Set_Current_Level_Kernelized( true );
	running_options.sampling_time -= begin_watch.Get_Elapsed_Seconds();
	tmp_watch.Start();
	Partial_CCDD_Manager manager( _max_var );
	manager.Open_Counting_Mode();
	BigFloat final_result = Count_With_One_Round( manager, tmp_watch );
	Set_Current_Level_Kernelized( false );
	Backtrack();
	_call_stack[0].Clear_Lit_Equivalences();
	if ( running_options.display_compiling_process ) Display_Memory_Status( cout ); // ToRemove
	manager.Clear( _model_pool );
	Recycle_Models( _models_stack[0] );
	Recycle_Models( _stored_models );
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	assert( _model_pool->Empty() );
	Reset();
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_partial_kc >= Profiling_Abstract ) {
			Display_Statistics( 1 );
		}
		cout << running_options.display_prefix << "The final model count: " << final_result << endl;
	}
	return final_result;
}

void Partial_CCDD_Compiler::Choose_Counting_Options( Heuristic heur )
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
		cerr << "ERROR[Partial_Compiler]: this heuristic strategy is not supported yet!" << endl;
		exit( 1 );
	}
	if ( running_options.treewidth <= 32 && running_options.trivial_variable_bound > _unsimplifiable_num_vars * 3 / 4 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars * 3 / 4;
	}
	else if ( running_options.treewidth <= 64 && running_options.trivial_variable_bound > _unsimplifiable_num_vars * 2 / 3 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars * 2 / 3;
	}
	else if ( running_options.trivial_variable_bound > _unsimplifiable_num_vars / 2 ) {
		running_options.trivial_variable_bound = _unsimplifiable_num_vars / 2;
	}
	running_options.trivial_clause_bound = running_options.trivial_variable_bound;
	running_options.trivial_density_bound = 3;
	running_options.trivial_length_bound = 0.5;
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
	if ( running_options.estimate_marginal_probability && !Is_Linear_Ordering( running_options.var_ordering_heur ) ) {
		Compute_Var_Order_Single_Cluster();
	}
	running_options.mem_load_factor = 0.5;
	if ( running_options.max_memory > 2 ) {
		_exact_counter.running_options.max_memory = 1.5 + (running_options.max_memory - 2) / 2;
	}
	else _exact_counter.running_options.max_memory = running_options.max_memory * 0.75;
}

BigFloat Partial_CCDD_Compiler::Count_With_One_Round( Partial_CCDD_Manager & manager, StopWatch & begin_watch )
{
	if ( _component_cache.Empty() ) Copy_Models( _models_stack[0], _stored_models );
	BigFloat pre_result = 0, current_result, final_result;
	unsigned previous_sample, current_sample;
	unsigned interval = running_options.sampling_display_interval;
	for ( previous_sample = 0, current_sample = 1; current_sample <= running_options.sampling_count; current_sample++ ) {
		unsigned old_cache_size = _component_cache.Size();
		Create_Init_Level( _component_cache.Empty() );
		Microcompile_Opt( manager );
		_num_rsl_stack--;
//		manager.Display_Partial_CCDD_With_Weights( cout, _rsl_stack[0] );  // ToRemove
		if ( !_store_one_model && Is_Memory_Tight( manager, old_cache_size ) ) {
			Remove_Redundant_Nodes( manager, _rsl_stack[0] );
			manager.Thin_Model_Space( _model_pool );
			_store_one_model = true;
		}
		current_result = manager.Node( _rsl_stack[0] ).weight;
		current_result.Div_2exp( _fixed_num_vars + _call_stack[0].Lit_Equivalences_Size() );
		if ( _store_one_model && Is_Memory_Tight( manager, old_cache_size ) ) {
			if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Out of memory and restart" << endl;
//			cout << previous_sample << " * " << pre_result << " vs " << current_sample - previous_sample << " * " << nr_stack[0]->weight;  // ToRemove
			pre_result.Mean( pre_result, current_result, 1.0 * previous_sample / current_sample );
//			cout << " = " << pre_result << endl;  // ToRemove
			previous_sample = current_sample;
			current_result = 0;
			manager.Clear( _model_pool );
			_component_cache.Reset();
			assert( _model_pool->Size() == _stored_models.size() );
			Copy_Models( _stored_models, _models_stack[0] );
			_store_one_model = false;
		}
		if ( running_options.display_compiling_process && current_sample % interval == 0 ) {
			final_result.Mean( pre_result, current_result, 1.0 * previous_sample / current_sample );
			cout << running_options.display_prefix << current_sample << "(" << begin_watch.Get_Elapsed_Seconds() << "s): " << final_result << endl;
			if ( current_sample >= interval * 1000 ) interval *= 10;
		}
		if ( _rsl_stack[0] < manager.Num_Nodes() && manager.Node( _rsl_stack[0] ).sym == SEARCH_KNOWN ) {
			if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Converged" << endl;
			break;
		}
		if ( Timeout_Possibly( current_sample, begin_watch.Get_Elapsed_Seconds() ) ) break;
	}
	if ( _rsl_stack[0] < manager.Num_Nodes() && manager.Node( _rsl_stack[0] ).sym == SEARCH_KNOWN ) {
		final_result = manager.Node( _rsl_stack[0] ).weight;
		final_result.Div_2exp( _fixed_num_vars + _call_stack[0].Lit_Equivalences_Size() );
	}
	else final_result.Mean( pre_result, current_result, 1.0 * previous_sample / current_sample );
	if ( _component_cache.Empty() ) Recycle_Models( _stored_models );
	return final_result;
}

void Partial_CCDD_Compiler::Microcompile_Opt( Partial_CCDD_Manager & manager )
{
	Variable var;
	NodeID parent, old_result;
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
				parent = _component_cache.Read_Result( Parent_of_Current_Component().caching_loc );
				if ( parent == NodeID::undef ) old_result = NodeID::undef;
				else old_result = manager.Node(parent).ch[ _dec_stack[_num_dec_stack - 1].Sign()];
				if ( old_result == NodeID::undef || manager.Node(old_result).sym == SEARCH_UNKNOWN ) {
					Get_All_Imp_Component( Parent_of_Current_Component(), _models_stack[_num_levels - 1] );  // NOTE: comp_stack[num_level - 1] is not generated yet
					_num_comp_stack += Dynamic_Decompose_Component( Parent_of_Current_Component(), _comp_stack + _comp_offsets[_num_levels - 1] );
					Handle_Components( manager, _num_comp_stack - _comp_offsets[_num_levels - 1] );
				}
				else {
					Recover_All_Imp( manager, old_result );
					Recover_and_Handle_Components( manager, old_result );
				}
				break;
			case 1:
				if ( Is_Component_Trivial( manager ) ) {
					if ( Backtrack_Trivial_Possibly( manager ) ) break;
				}
				if ( Try_Kernelization( manager ) == lbool::unknown ) break;
				Extend_New_Level( manager );
				break;
			case 2:
				assert( _num_rsl_stack >= 1 );
				Backtrack_Decision( manager );
				break;
			}
		}
		else {
			assert( _active_comps[_num_levels - 1] == _comp_offsets[_num_levels - 1] + _state_stack[_num_levels - 1] / 2 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1] % 2 ) {
				case 0:
					Component_Cache_Map( Current_Component() );
					if ( Is_Component_Trivial( manager ) ) {
						if ( Iterate_Trivial_Possibly( manager ) ) break;
					}
					if ( Try_Kernelization( manager ) == lbool::unknown ) break;
					Extend_New_Level( manager );
					break;
				case 1:
					assert( _num_rsl_stack >= 1 );
					Iterate_Decision( manager );
					break;
				}
			}
			else {
				assert( _num_rsl_stack >= _state_stack[_num_levels - 1] / 2 && _num_rsl_stack >= 2 );
				Backtrack_Decomposition( manager );
			}
		}
	}
	assert( _num_levels == 1 && _num_rsl_stack == 1 );
}

bool Partial_CCDD_Compiler::Is_Component_Trivial( Partial_CCDD_Manager & manager )
{
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.sym != SEARCH_UNKNOWN ) return old_node.sym == SEARCH_KNOWN;
	}
	return Is_Component_Trivial( Current_Component() );
}

bool Partial_CCDD_Compiler::Backtrack_Trivial_Possibly( Partial_CCDD_Manager & manager )
{
	StopWatch tmp_watch;
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.sym != SEARCH_UNKNOWN ) {
			assert( old_node.sym == SEARCH_KNOWN );
			if ( _num_levels == 2 ) _rsl_stack[_num_rsl_stack++] = old_id;
			else _rsl_stack[_num_rsl_stack++] = Make_Node_With_Imp( manager, old_id );
			Recycle_Models( _models_stack[_num_levels - 1] );
			Backtrack();
			return true;
		}
	}
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) tmp_watch.Start();
	if ( DEBUG_OFF ) cout << "#vars: " << Current_Component().Vars_Size() << ", #clauses: " << Current_Component().ClauseIDs_Size() << endl;  // ToModify
	double timeout = running_options.simply_counting_time;
	BigInt exact = Count_Models_Simple_Component( Current_Component(), _models_stack[_num_levels - 1], timeout );
	assert( exact.LE_2exp( Current_Component().Vars_Size() ) );  // ToModify
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_simply_counting += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) cout << "time simply: " << statistics.time_simply_counting << endl;  // ToRemove
	if ( exact < 0 ) {
		_level_ExactMC_failed[_num_levels - 1] = true;
		if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close  ) {
			cout << running_options.display_prefix << "ExactMC failed on level " << _num_levels - 1 << "!" << endl;
		}
		Adjust_Trivial_Bound( Current_Component() );
		return false;
	}
	BigFloat exact_num( exact );
	exact_num.Mul_2exp( NumVars(_max_var) - Current_Component().Vars_Size() );
	_rsl_stack[_num_rsl_stack] = manager.Add_Known_Node( exact_num, Current_Component().caching_loc );
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack] );
	if ( _num_levels != 2 ) _rsl_stack[_num_rsl_stack] = Make_Node_With_Imp( manager, _rsl_stack[_num_rsl_stack] );
	_num_rsl_stack++;
	Recycle_Models( _models_stack[_num_levels - 1] );
	Backtrack();
	return true;
}

void Partial_CCDD_Compiler::Adjust_Trivial_Bound( Component & comp )
{
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close  ) {
		cout << running_options.display_prefix << "old "
		<< "trivial_variable_bound = " << running_options.trivial_variable_bound
		<< ", trivial_clause_bound = " << running_options.trivial_clause_bound
		<< ", trivial_density_bound = " << running_options.trivial_density_bound
		<< ", trivial_length_bound = " << running_options.trivial_length_bound << endl;
	}
	if ( comp.ClauseIDs_Size() <= running_options.trivial_clause_bound ) {
		running_options.trivial_clause_bound = comp.ClauseIDs_Size() * 9 / 10;
	}
	else if ( comp.Vars_Size() > running_options.trivial_variable_bound ) {
		float density, length;
		Hardness_Features_of_Clauses( comp, density, length );
		if ( density < running_options.trivial_density_bound ) running_options.trivial_density_bound = density * 7 / 8;
		else if ( length < running_options.trivial_length_bound ) running_options.trivial_length_bound = length * 15 / 16;
	}
	else {
		if ( running_options.trivial_variable_bound > 256 && comp.Vars_Size() > 128 ) {
			running_options.trivial_variable_bound = running_options.trivial_variable_bound - 32;
			Variable new_bound( comp.Vars_Size() - 32 );
			if ( new_bound < running_options.trivial_variable_bound ) running_options.trivial_variable_bound = new_bound;
		}
		else if ( running_options.trivial_variable_bound > 32 && comp.Vars_Size() > 16 ) {
			running_options.trivial_variable_bound = running_options.trivial_variable_bound - 16;
			Variable new_bound( comp.Vars_Size() - 16 );
			if ( new_bound < running_options.trivial_variable_bound ) running_options.trivial_variable_bound = new_bound;
		}
		if ( running_options.trivial_clause_bound > running_options.trivial_variable_bound ) {
			running_options.trivial_clause_bound = running_options.trivial_variable_bound;
		}
	}
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close  ) {
		cout << running_options.display_prefix << "new "
		<< "trivial_variable_bound = " << running_options.trivial_variable_bound
		<< ", trivial_clause_bound = " << running_options.trivial_clause_bound
		<< ", trivial_density_bound = " << running_options.trivial_density_bound
		<< ", trivial_length_bound = " << running_options.trivial_length_bound << endl;
	}
}

bool Partial_CCDD_Compiler::Iterate_Trivial_Possibly( Partial_CCDD_Manager & manager )
{
	StopWatch tmp_watch;
	NodeID old_id = _component_cache.Read_Result( Current_Component().caching_loc );
	if ( old_id != NodeID::undef ) {
		const Partial_CDD_Node & old_node = manager.Node( old_id );
		if ( old_node.sym != SEARCH_UNKNOWN ) {
			assert( old_node.sym == SEARCH_KNOWN );
			_rsl_stack[_num_rsl_stack++] = old_id;
			_active_comps[_num_levels - 1]++;
			_state_stack[_num_levels - 1] += 2;
			return true;
		}
	}
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) tmp_watch.Start();
	if ( DEBUG_OFF ) cout << "#vars: " << Current_Component().Vars_Size() << ", #clauses: " << Current_Component().ClauseIDs_Size() << endl;  // ToModify
	double timeout = running_options.simply_counting_time;
	BigInt exact = Count_Models_Simple_Component( Current_Component(), _models_stack[_num_levels - 1], timeout );
	assert( exact.LE_2exp( Current_Component().Vars_Size() ) );  // ToModify
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_simply_counting += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) cout << "time simply: " << statistics.time_simply_counting << endl;  // ToRemove
	if ( exact < 0 ) {
		_level_ExactMC_failed[_num_levels - 1] = true;
		if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close  ) {
			cout << running_options.display_prefix << "ExactMC failed on level " << _num_levels - 1 << "!" << endl;
		}
		Adjust_Trivial_Bound( Current_Component() );
		return false;
	}
	BigFloat exact_num( exact );
	exact_num.Mul_2exp( NumVars(_max_var) - Current_Component().Vars_Size() );
	_rsl_stack[_num_rsl_stack] = manager.Add_Known_Node( exact_num, Current_Component().caching_loc );
	_component_cache.Write_Result( Current_Component().caching_loc, _rsl_stack[_num_rsl_stack] );
	_num_rsl_stack++;
	_active_comps[_num_levels - 1]++;
	_state_stack[_num_levels - 1] += 2;
	return true;
}

bool Partial_CCDD_Compiler::Is_Memory_Tight( Partial_CCDD_Manager & manager, unsigned old_cache_size )
{
	if ( _component_cache.Size() <= old_cache_size ) return false;
	const float delta = 0.15;
	const size_t GB = 1024 * 1024 * 1024;
	double max_mem = running_options.max_memory * GB;
	size_t evaluated_mem = _component_cache.Memory() + _model_pool->Memory() + manager.Memory() + _exact_counter.Memory();
	if ( evaluated_mem < max_mem * (running_options.mem_load_factor - delta) ) return false;
	if ( evaluated_mem > max_mem * (running_options.mem_load_factor + delta) ) return true;
	size_t true_mem = Total_Used_Memory();
	running_options.mem_load_factor = evaluated_mem / true_mem;
	if ( running_options.mem_load_factor - delta < 0 ) running_options.mem_load_factor = delta;
	else if ( running_options.mem_load_factor + delta > 1 ) running_options.mem_load_factor = 1 - delta;
	if ( running_options.profile_compiling != Profiling_Close ) {
		cout << running_options.display_prefix << (float) _component_cache.Memory() / GB << " (cache) + " \
			<< (float) _model_pool->Memory() / GB << " (model) + " \
			<<  (float) manager.Memory() / GB << " (DAG) / ";
		cout << (float) true_mem / GB << " (total) in GB" << endl;
	}
	if ( true_mem < max_mem * 0.9 ) return false;
	else return true;
}

void Partial_CCDD_Compiler::Remove_Redundant_Nodes( Partial_CCDD_Manager & manager, NodeID & root )
{
	assert( _num_rsl_stack == 0 );
	StopWatch watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) watch.Start();
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "remove DAG redundancy: " << manager.Num_Nodes();
	vector<NodeID> kept_nodes( 1 );
	kept_nodes[0] = root;
	for ( unsigned i = 0; i < _component_cache.Size(); i++ ) {
		NodeID n = _component_cache.Read_Result( i );
		if ( n != NodeID::undef ) {
			kept_nodes.push_back( n );
		}
	}
	manager.Remove_Redundant_Nodes( kept_nodes );
	if ( running_options.display_compiling_process ) cout << " -> " << manager.Num_Nodes() << endl;
	root = kept_nodes[0];
	for ( unsigned i = 0, j = 1; i < _component_cache.Size(); i++ ) {
		NodeID n = _component_cache.Read_Result( i );
		if ( n != NodeID::undef ) {
			_component_cache.Write_Result( i, kept_nodes[j++] );
		}
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_gen_dag += watch.Get_Elapsed_Seconds();
}

bool Partial_CCDD_Compiler::Timeout_Possibly( unsigned samples, double elapsed )
{
    return elapsed + elapsed / samples > 0.999 * running_options.sampling_time;
}

BigFloat Partial_CCDD_Compiler::Count_Models_Lower_Bound( CNF_Formula & cnf, Heuristic heur, float confidence )
{
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_compiling_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Counting models..." << endl;
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) begin_watch.Start();
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	assert( _num_levels == 0 && _num_dec_stack == 0 && _num_comp_stack == 0 );
	assert( running_options.sampling_count > 0 );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	if ( _fixed_num_vars >= 32 ) Shrink_Max_Var();
	if ( _models_stack[0].empty() ) Generate_Models_External( _models_stack[0] );
	if ( running_options.display_compiling_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		_num_levels--;
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
			cout << running_options.display_prefix << "The exact model count: " << 0 << endl;
		}
		Reset();
		return 0;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		Un_BCP( _dec_offsets[--_num_levels] );
		_call_stack[0].Clear_Lit_Equivalences();
		BigFloat result;
		result.Assign_2exp( NumVars( _max_var ) - _fixed_num_vars );
		if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_compiling >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
			cout << running_options.display_prefix << "The exact model count: " << result << endl;
		}
		Reset();
		return result;
	}
	Gather_Infor_For_Counting();
	Choose_Counting_Options( heur );
	if ( running_options.display_compiling_process && running_options.profile_compiling != Profiling_Close ) running_options.Display( cout );  // ToRemove
	Set_Current_Level_Kernelized( true );
	Partial_CCDD_Manager manager( _max_var );
	manager.Open_Counting_Mode();
	double sampling_time = running_options.sampling_time;
	BigFloat counts[32], lower_approximation = _models_stack[0].size();
	unsigned round, num_rounds = ceil( log2( 1 / (1 - confidence) ) );
	assert( num_rounds <= 32 );
	for ( round = 1; round <= num_rounds; round++ ) {
		double elapsed_time = begin_watch.Get_Elapsed_Seconds();
		if ( sampling_time < elapsed_time ) break;
		running_options.sampling_time = ( sampling_time - elapsed_time ) / (num_rounds - round + 1.05);
		tmp_watch.Start();
		counts[round - 1] = Count_With_One_Round( manager, tmp_watch );
		if ( _rsl_stack[0] < manager.Num_Nodes() && manager.Node( _rsl_stack[0] ).sym == SEARCH_KNOWN ) {
			lower_approximation = counts[round - 1];
			break;
		}
		lower_approximation = Compute_Lower_Approximation( counts, confidence, round );
		if ( running_options.display_compiling_process ) {
			cout << running_options.display_prefix << "A lower bound of count (" << confidence * 100 << "\% confidence): " << lower_approximation << endl;
		}
		Remove_Redundant_Nodes( manager, _rsl_stack[0] );
		manager.Reset_Frequencies();
//		manager.Display_Partial_CCDD_With_Weights( cout, _rsl_stack[0] );  // ToRemove
	}
	Set_Current_Level_Kernelized( false );
	Backtrack();
	_call_stack[0].Clear_Lit_Equivalences();
	if ( running_options.display_compiling_process ) Display_Memory_Status( cout ); // ToRemove
	manager.Clear( _model_pool );
	Recycle_Models( _models_stack[0] );
	Recycle_Models( _stored_models );
	if ( running_options.profile_partial_kc >= Profiling_Abstract ) statistics.time_compile = begin_watch.Get_Elapsed_Seconds();
	if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	assert( _model_pool->Empty() );
	Reset();
	if ( running_options.display_compiling_process ) {
		cout << running_options.display_prefix << "Done." << endl;
		if ( running_options.profile_partial_kc >= Profiling_Abstract ) {
			Display_Statistics( 1 );
		}
		cout << running_options.display_prefix;
		if ( round <= num_rounds ) cout << "The exact model count: ";
		else cout << "The final lower bound of model count (" << confidence * 100 << "%% confidence): ";
		cout << lower_approximation << endl;
	}
	return lower_approximation;
}

BigFloat Partial_CCDD_Compiler::Compute_Lower_Approximation( BigFloat counts[], float confidence, unsigned num_rounds )
{
	assert( num_rounds >= 1 );
	BigFloat min_count = counts[0];
	for ( unsigned i = 1; i < num_rounds; i++ ) {
		if ( counts[i] < min_count ) min_count = counts[i];
	}
	float tmp = 1 / (1 - confidence);
	float relaxed_factor = pow( tmp, 1.0 / num_rounds );
	min_count /= relaxed_factor;
	return min_count;
}


}
