#include "Inprocessor.h"
#include <sstream>
#include <sys/sysinfo.h>


namespace KCBox {


using namespace std;


Inprocessor::Inprocessor() :
_num_comp_stack( 0 )
{
}

Inprocessor::~Inprocessor()
{
	if ( _max_var != Variable::undef || Is_Oracle_Mode() ) Free_Auxiliary_Memory();
}

void Inprocessor::Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	if ( Is_Oracle_Mode() ) {
		assert( max_var <= running_options.variable_bound );
		_max_var = max_var;
		return;
	}
	if ( _max_var == max_var ) {  /// to make the recursive calls from inherited classes correct
		if ( running_options.profiling_inprocessing != Profiling_Close ) statistics.Init_Inprocessor();
		return;
	}
	if ( running_options.profiling_inprocessing != Profiling_Close ) statistics.Init_Inprocessor_Single();
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
	/// NOTE: on the following lines, we cannot use _max_var because it is not assigned yet (it will be assigned in Solver::Allocate_and_Init_Auxiliary_Memory)
	Preprocessor::Allocate_and_Init_Auxiliary_Memory( max_var );
	_extra_binary_clauses = new vector<Literal> [2 * max_var + 2];  // used for minisat
	_var_scores = new double [max_var + 2];  // extra bit for _max_var.Next()
	_lit_scores = new double [2 * max_var + 2];
	_models_stack = new vector<Model *> [2 * max_var + 2];
	_binary_var_membership_lists = new vector<Variable> [max_var + 1];  /// variable membership
	_ternary_var_membership_lists = new vector<unsigned> [max_var + 1];  /// <clauseID, first var, second var, third var>
	_quaternary_var_membership_lists = new vector<unsigned> [max_var + 1];  /// <clauseID, first var, second var, third var, fourth var>
	_long_var_membership_lists = new vector<unsigned> [max_var + 1];  /// variable membership
	_comp_stack = new Component [2 * max_var + 2];
	_comp_offsets = new unsigned [2 * max_var + 2];
	_active_comps = new unsigned [2 * max_var + 2];  // recording the current component which is being compiled
	_state_stack = new unsigned [2 * max_var + 2];
	_var_projected.assign( max_var + 2, false );
}

void Inprocessor::Free_Auxiliary_Memory()
{
	delete [] _extra_binary_clauses;  // used for minisat
	delete [] _var_scores;
	delete [] _lit_scores;
	delete [] _models_stack;
	delete [] _binary_var_membership_lists;  /// variable membership
	delete [] _ternary_var_membership_lists;  /// <clauseID, first var, second var, third var>
	delete [] _quaternary_var_membership_lists;  /// <clauseID, first var, second var, third var, fourth var>
	delete [] _long_var_membership_lists;  /// variable membership
	delete [] _comp_stack;
	delete [] _comp_offsets;
	delete [] _active_comps;
	delete [] _state_stack;
}

void Inprocessor::Reset()
{
	Preprocessor::Reset();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_binary_var_membership_lists[i].clear();
		_ternary_var_membership_lists[i].clear();
		_quaternary_var_membership_lists[i].clear();
		_long_var_membership_lists[i].clear();
		Literal lit( i, false );
		_extra_binary_clauses[lit].clear();
		_long_lit_membership_lists[lit].clear();
		lit = Literal( i, true );
		_extra_binary_clauses[lit].clear();
		_long_lit_membership_lists[lit].clear();
	}
	_var_order.Clear();
}

void Inprocessor::Open_Oracle_Mode( Variable var_bound )
{
	Allocate_and_Init_Auxiliary_Memory( var_bound );
	running_options.variable_bound = var_bound;
	running_options.display_preprocessing_process = false;
}

void Inprocessor::Close_Oracle_Mode()
{
	running_options.variable_bound = Variable::undef;
}

bool Inprocessor::Var_Appeared( Variable var ) const
{
	if ( running_options.decompose_strategy == Decompose_With_Sorting ) {
		return _binary_var_membership_lists[var].size() + _long_var_membership_lists[var].size();
	}
	else {
		return _binary_var_membership_lists[var].size() + \
			_ternary_var_membership_lists[var].size() + \
			_quaternary_var_membership_lists[var].size() + \
			_long_var_membership_lists[var].size();
	}
}

unsigned Inprocessor::Num_Var_Appearances( Variable var ) const
{
	if ( running_options.decompose_strategy == Decompose_With_Sorting ) {
		return _binary_var_membership_lists[var].size() + _long_var_membership_lists[var].size();
	}
	else {
		return _binary_var_membership_lists[var].size() + \
			_ternary_var_membership_lists[var].size() / 3 + \
			_quaternary_var_membership_lists[var].size() / 4 + \
			_long_var_membership_lists[var].size();
	}
}

size_t Inprocessor::Memory()
{
	size_t mem = Preprocessor::Memory();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		mem += _models_stack[i].capacity() * sizeof(unsigned);
		mem += _comp_stack[i].Capacity() * sizeof(unsigned);
		mem += _binary_var_membership_lists[i].capacity() * sizeof(unsigned);
		mem += _ternary_var_membership_lists[i].capacity() * sizeof(unsigned);
		mem += _quaternary_var_membership_lists[i].capacity() * sizeof(unsigned);
		mem += _long_var_membership_lists[i].capacity() * sizeof(unsigned);
		mem += _long_lit_membership_lists[i+i].capacity() * sizeof(unsigned);
		mem += _long_lit_membership_lists[i+i+1].capacity() * sizeof(unsigned);
	}
	return mem;
}

void Inprocessor::Compute_Var_Order_Min_Fill_Heuristic_Bound( unsigned bound )
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	Greedy_Graph * pg = Create_Primal_Graph();
	if ( _unsimplifiable_num_vars == _max_var ) {
		Simple_TreeD treed( *pg, bound );
		running_options.treewidth = treed.Width();
		if ( running_options.treewidth <= bound ) {
			Generate_Var_Order_From_TreeD( treed );
		}
	}
	else {
		Simple_TreeD treed( *pg, bound, true );  /// optimized for large-scale problems
		running_options.treewidth = treed.Width();
		if ( running_options.treewidth <= bound ) {
			Generate_Var_Order_From_TreeD( treed );
		}
	}
	delete pg;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition = begin_watch.Get_Elapsed_Seconds();
}

void Inprocessor::Compute_Var_Order_Min_Fill_Heuristic_Opt()
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	Greedy_Graph * pg = Create_Primal_Graph();
	Simple_TreeD treed( *pg );
	running_options.treewidth = treed.Width();
	Generate_Var_Order_From_TreeD( treed );
	delete pg;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition = begin_watch.Get_Elapsed_Seconds();
}

Greedy_Graph * Inprocessor::Create_Primal_Graph()
{
	if ( running_options.decompose_strategy == Decompose_With_Sorting ) {
		return Create_Primal_Graph_With_Sorting();
	}
	else {
		return Create_Primal_Graph_Without_Sorting();
	}
}

Greedy_Graph * Inprocessor::Create_Primal_Graph_With_Sorting()
{
	unsigned i, j, size;
	unsigned * vertices = new unsigned [_max_var - Variable::start + 1];
	vector<vector<unsigned>> edges( _max_var + 1 );
	for ( i = Variable::start; i <= _max_var; i++ ) {
		size = 0;
		vector<Literal>::iterator itr = _binary_clauses[i + i].begin();
		vector<Literal>::iterator end = _binary_clauses[i + i].begin() + _old_num_binary_clauses[i + i];
		for ( ; itr < end; itr++ ) {
			vertices[size] = itr->Var();
			size += !_var_seen[itr->Var()];
			_var_seen[itr->Var()] = true;
		}
		itr = _binary_clauses[i + i + 1].begin();
		end = _binary_clauses[i + i + 1].begin() + _old_num_binary_clauses[i + i + 1];
		for ( ; itr < end; itr++ ) {
			vertices[size] = itr->Var();
			size += !_var_seen[itr->Var()];
			_var_seen[itr->Var()] = true;
		}
		vector<unsigned>::iterator it = _long_var_membership_lists[i].begin();
		vector<unsigned>::iterator en = _long_var_membership_lists[i].end();
		for ( ; it < en; it++ ) {
			Clause & clause = _long_clauses[*it];
			for ( j = 0; clause[j].Var() != i; j++ ) {
				vertices[size] = clause[j].Var();
				size += !_var_seen[clause[j].Var()];
				_var_seen[clause[j].Var()] = true;
			}
			for ( j++; j < clause.Size(); j++ ) {
				vertices[size] = clause[j].Var();
				size += !_var_seen[clause[j].Var()];
				_var_seen[clause[j].Var()] = true;
			}
		}
		for ( j = 0; j < size; j++ ) {
			edges[i].push_back( vertices[j] );
			_var_seen[vertices[j]] = false;
		}
	}
	delete [] vertices;
	return new Greedy_Graph( _max_var, edges );
}

Greedy_Graph * Inprocessor::Create_Primal_Graph_Without_Sorting()
{
	unsigned * vertices = new unsigned [_max_var - Variable::start + 1];
	vector<vector<unsigned>> edges( _max_var + 1 );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned size = 0;
		vector<Variable>::iterator itr = _binary_var_membership_lists[i].begin();
		vector<Variable>::iterator end = _binary_var_membership_lists[i].end();
		for ( ; itr < end; itr++ ) {
			vertices[size] = *itr;
			size += !_var_seen[*itr];
			_var_seen[*itr] = true;
		}
		vector<unsigned>::iterator it = _ternary_var_membership_lists[i].begin();
		vector<unsigned>::iterator en = _ternary_var_membership_lists[i].end();
		for ( ; it < en; it += 3 ) {
			unsigned var = *(it+1);
			vertices[size] = var;
			size += !_var_seen[var];
			_var_seen[var] = true;
			var = *(it+2);
			vertices[size] = var;
			size += !_var_seen[var];
			_var_seen[var] = true;
		}
		it = _quaternary_var_membership_lists[i].begin();
		en = _quaternary_var_membership_lists[i].end();
		for ( ; it < en; it += 4 ) {
			unsigned var = *(it+1);
			vertices[size] = var;
			size += !_var_seen[var];
			_var_seen[var] = true;
			var = *(it+2);
			vertices[size] = var;
			size += !_var_seen[var];
			_var_seen[var] = true;
			var = *(it+3);
			vertices[size] = var;
			size += !_var_seen[var];
			_var_seen[var] = true;
		}
		it = _long_var_membership_lists[i].begin();
		en = _long_var_membership_lists[i].end();
		for ( ; it < en; it++ ) {
			Clause & clause = _long_clauses[*it];
			unsigned j;
			for ( j = 0; clause[j].Var() != i; j++ ) {
				vertices[size] = clause[j].Var();
				size += !_var_seen[clause[j].Var()];
				_var_seen[clause[j].Var()] = true;
			}
			for ( j++; j < clause.Size(); j++ ) {
				vertices[size] = clause[j].Var();
				size += !_var_seen[clause[j].Var()];
				_var_seen[clause[j].Var()] = true;
			}
		}
		for ( unsigned j = 0; j < size; j++ ) {
			edges[i].push_back( vertices[j] );
			_var_seen[vertices[j]] = false;
		}
	}
	delete [] vertices;
	return new Greedy_Graph( _max_var, edges );
}

void Inprocessor::Var_Weight_For_Tree_Decomposition( double * var_weight )
{
	if ( running_options.decompose_strategy == Decompose_With_Sorting ) {
		Var_Weight_For_Tree_Decomposition_With_Sorting( var_weight );
	}
	else {
		Var_Weight_For_Tree_Decomposition_Without_Sorting( var_weight );
	}
}

void Inprocessor::Var_Weight_For_Tree_Decomposition_With_Sorting( double * var_weight )
{
	unsigned i, j;
	double scores[2];
	vector<unsigned>::iterator itr, end;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		switch( 2 ) {  // ToModify
		case 1:
			var_weight[i] = 2 * ( _old_num_binary_clauses[i + i] + _old_num_binary_clauses[i + i + 1] );
			itr = _long_var_membership_lists[i].begin(), end = _long_var_membership_lists[i].end();
			for ( ; itr < end; itr++ ) {
				var_weight[i] += 1.0 / _long_clauses[*itr].Size();
			}
			break;
		case 2:
			scores[0] = _old_num_binary_clauses[i + i] + _binary_clauses[i + i].size();
			scores[1] = _old_num_binary_clauses[i + i + 1] + _binary_clauses[i + i + 1].size();
			itr = _long_var_membership_lists[i].begin(), end = _long_var_membership_lists[i].end();
			for ( ; itr < end; itr++ ) {
				Clause & clause = _long_clauses[*itr];
				for ( j = 0; clause[j].Var() != i; j++ ) {}
				scores[clause[j].Sign()] += 1.0 / clause.Size();
			}
			var_weight[i] = scores[0] * scores[1];
			break;
		case 3:
			var_weight[i] = _max_var - i;
			break;
		 }
	}
}

void Inprocessor::Var_Weight_For_Tree_Decomposition_Without_Sorting( double * var_weight )
{
	unsigned i, j;
	double scores[2];
	vector<unsigned>::iterator itr, end;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		switch( 2 ) {  // ToModify
		case 1:
			var_weight[i] = 2 * ( _old_num_binary_clauses[i + i] + _old_num_binary_clauses[i + i + 1] );
			var_weight[i] += 1.0 * _ternary_var_membership_lists[i].size() / 3 / 3;
			var_weight[i] += 1.0 * _quaternary_var_membership_lists[i].size() / 4 / 4;
			itr = _long_var_membership_lists[i].begin(), end = _long_var_membership_lists[i].end();
			for ( ; itr < end; itr++ ) {
				var_weight[i] += 1.0 / _long_clauses[*itr].Size();
			}
			break;
		case 2:
			scores[0] = _old_num_binary_clauses[i + i] + _binary_clauses[i + i].size();
			scores[1] = _old_num_binary_clauses[i + i + 1] + _binary_clauses[i + i + 1].size();
			itr = _ternary_var_membership_lists[i].begin(), end = _ternary_var_membership_lists[i].end();
			for ( ; itr < end; itr += 3 ) {
				Clause & clause = _long_clauses[*itr];
				for ( j = 0; clause[j].Var() != i; j++ ) {}
				scores[clause[j].Sign()] += 1.0 / 3;
			}
			itr = _quaternary_var_membership_lists[i].begin(), end = _quaternary_var_membership_lists[i].end();
			for ( ; itr < end; itr += 4 ) {
				Clause & clause = _long_clauses[*itr];
				for ( j = 0; clause[j].Var() != i; j++ ) {}
				scores[clause[j].Sign()] += 1.0 / 4;
			}
			itr = _long_var_membership_lists[i].begin(), end = _long_var_membership_lists[i].end();
			for ( ; itr < end; itr++ ) {
				Clause & clause = _long_clauses[*itr];
				for ( j = 0; clause[j].Var() != i; j++ ) {}
				scores[clause[j].Sign()] += 1.0 / clause.Size();
			}
			var_weight[i] = scores[0] * scores[1];
			break;
		default:
			var_weight[i] = _max_var - i;
			break;
		 }
	}
}

void Inprocessor::Generate_Var_Order_From_TreeD( Simple_TreeD & treed )
{
	double * var_weight = new double [_max_var + 1];
	Var_Weight_For_Tree_Decomposition( var_weight );
	Chain init_order = treed.Transform_Chain( var_weight );
	for ( unsigned i = 0; i < init_order.Size(); i++ ) {
		Variable var( init_order[i] );
		if ( Var_Appeared( var ) ) {
			_var_order.Append( var );
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_order.Contain( i ) ) {
			_var_order.Append( i );
		}
	}
	_var_order.Append( _max_var.Next() );  /// Note: I cannot remember why this line is needed, maybe in order to terminate some loop
	delete [] var_weight;
}

void Inprocessor::Generate_Var_Order_From_TreeD( Simple_TreeD & treed, double * var_weight )
{
	Chain init_order = treed.Transform_Chain( var_weight );
	for ( unsigned i = 0; i < init_order.Size(); i++ ) {
		Variable var( init_order[i] );
		if ( Var_Appeared( var ) ) {
			_var_order.Append( var );
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_order.Contain( i ) ) {
			_var_order.Append( i );
		}
	}
	_var_order.Append( _max_var.Next() );  /// Note: I cannot remember why this line is needed, maybe in order to terminate some loop
}

void Inprocessor::Compute_Var_Order_Flow_Cutter()
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	const char * graph_file = "solvers/flow_cutter_pace17-input.txt";
	const char * solver_file = "solvers/flow_cutter_pace17";
	const char * treed_file = "solvers/flow_cutter_pace17-output.txt";
	Greedy_Graph * pg = Create_Primal_Graph();
	ofstream fout( graph_file );
	pg->Display_PACE( fout );
	fout.close();
	string cmd = string("timeout ") + "120s " + solver_file + " " + graph_file + " > " + treed_file + " 2>/dev/null";
	int status = system(cmd.c_str());
	assert(status >= 0);
	ifstream fin( treed_file );
	Simple_TreeD treed( fin );
	treed.Verify( *pg );
	running_options.treewidth = treed.Width();
	Generate_Var_Order_From_TreeD( treed );
	delete pg;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition = begin_watch.Get_Elapsed_Seconds();
}

void Inprocessor::Compute_Var_Order_Lexicographic()
{
	unsigned i;
	_var_order.Clear();
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_var_order.Append( i );
	}
	_var_order.Append( _max_var.Next() );  /// Note: I cannot remember why this line is needed, maybe in order to terminate some loop
}

void Inprocessor::Compute_Var_Order_Single_Cluster()
{
	double * var_weight = new double [_max_var + 1];
	Var_Weight_For_Tree_Decomposition( var_weight );
	SList<Variable> left_vertices;
	SList_Node<Variable> * pre = left_vertices.Head();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !Var_Appeared( i ) ) continue;
		left_vertices.Insert_After( pre, i );
		pre = pre->next;
	}
	_var_order.Clear();
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
		Propagate_Var_Order_Weight( chosen_var, var_weight );
	}
	delete [] var_weight;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( !_var_order.Contain( i ) ) {
			_var_order.Append( i );
		}
	}
	_var_order.Append( _max_var.Next() );  /// Note: I cannot remember why this line is needed, maybe in order to terminate some loop
}

void Inprocessor::Propagate_Var_Order_Weight( Variable var, double * var_weight )
{
	const double factor = 0.01;
	for ( unsigned i = 0; i < _binary_var_membership_lists[var].size(); i++ ) {
		var_weight[_binary_var_membership_lists[var][i]] += factor / 2;
	}
	vector<unsigned>::iterator itr;
	if ( running_options.decompose_strategy == Decompose_With_Sorting ) {
		for ( itr = _long_var_membership_lists[var].begin(); itr < _long_var_membership_lists[var].end(); itr++ ) {
			Clause & clause = _long_clauses[*itr];
			var_weight[clause[0].Var()] += factor / clause.Size();
			var_weight[clause[1].Var()] += factor / clause.Size();
			for ( unsigned i = 2; i < clause.Size(); i++ ) {
				var_weight[clause[i].Var()] += factor / clause.Size();
			}
		}
	}
	else {
		for ( itr = _ternary_var_membership_lists[var].begin(); itr < _ternary_var_membership_lists[var].end(); itr += 3 ) {
			Clause & clause = _long_clauses[*itr];
//			cerr << clause << endl;  // ToRemove
			var_weight[clause[0].Var()] += factor / clause.Size();
			var_weight[clause[1].Var()] += factor / clause.Size();
			var_weight[clause[2].Var()] += factor / clause.Size();
		}
		for ( itr = _quaternary_var_membership_lists[var].begin(); itr < _quaternary_var_membership_lists[var].end(); itr += 4 ) {
			Clause & clause = _long_clauses[*itr];
			var_weight[clause[0].Var()] += factor / clause.Size();
			var_weight[clause[1].Var()] += factor / clause.Size();
			var_weight[clause[2].Var()] += factor / clause.Size();
			var_weight[clause[3].Var()] += factor / clause.Size();
		}
		for ( itr = _long_var_membership_lists[var].begin(); itr < _long_var_membership_lists[var].end(); itr++ ) {
			Clause & clause = _long_clauses[*itr];
			var_weight[clause[0].Var()] += factor / clause.Size();
			var_weight[clause[1].Var()] += factor / clause.Size();
			var_weight[clause[2].Var()] += factor / clause.Size();
			var_weight[clause[3].Var()] += factor / clause.Size();
			var_weight[clause[4].Var()] += factor / clause.Size();
			for ( unsigned i = 5; i < clause.Size(); i++ ) {
				var_weight[clause[i].Var()] += factor / clause.Size();
			}
		}
	}
}

void Inprocessor::Compute_Dynamic_Min_Fill_Bound( unsigned bound )
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	Greedy_Graph * pg = Create_Primal_Graph();
	if ( _unsimplifiable_num_vars == _max_var ) {
		Simple_TreeD treed( *pg, bound );
		running_options.treewidth = treed.Width();
		if ( running_options.treewidth <= bound ) {
			Var_Weight_For_Tree_Decomposition( _var_scores );
			treed.Compute_DTree_Scores( _var_scores );
		}
	}
	else {
		Simple_TreeD treed( *pg, bound, true );  /// optimized for large-scale problems
		running_options.treewidth = treed.Width();
		if ( running_options.treewidth <= bound ) {
			Var_Weight_For_Tree_Decomposition( _var_scores );
			treed.Compute_DTree_Scores( _var_scores );
		}
	}
	delete pg;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition = begin_watch.Get_Elapsed_Seconds();
}

unsigned Inprocessor::Compute_Var_Order_Min_Fill_Bound_Component( Component & comp, unsigned bound )
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	double * var_weight = new double [_max_var + 1];
	Greedy_Graph * pg = Create_Weighted_Primal_Graph_Component( comp, var_weight );
	Simple_TreeD treed( *pg, bound, true );  /// optimized for large-scale problems
	unsigned treewidth = treed.Width();
	if ( treewidth <= bound ) {
		assert( _var_order.Empty() );
		Generate_Var_Order_Min_Fill_Component( comp, treed, var_weight );
	}
	delete pg;
	delete [] var_weight;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_tree_decomposition += begin_watch.Get_Elapsed_Seconds();
	return treewidth;
}

Greedy_Graph * Inprocessor::Create_Weighted_Primal_Graph_Component( Component & comp, double * var_weight )
{
	vector<vector<unsigned>> edges( comp.Vars_Size() );
	vector<double> scores( 2 * comp.Vars_Size(), 0 );
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		_var_map[comp.Vars( i )] = i;
	}
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		unsigned j;
		Literal lit( comp.Vars( i ), false );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned x = _var_map[lit2.Var()];
			edges[i].push_back( x );
			edges[x].push_back( i );
			scores[i + i + lit.Sign()] += 2;
			scores[x + x + lit2.Sign()] += 2;
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned x = _var_map[lit2.Var()];
			scores[i + i + lit.Sign()] += 1;
			scores[x + x + lit2.Sign()] += 1;
		}
		lit = Literal( comp.Vars( i ), true );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned x = _var_map[lit2.Var()];
			edges[i].push_back( x );
			edges[x].push_back( i );
			scores[i + i + lit.Sign()] += 2;
			scores[x + x + lit2.Sign()] += 2;
		}
		for ( ; j < _binary_clauses[lit].size(); j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			unsigned x = _var_map[lit2.Var()];
			scores[i + i + lit.Sign()] += 1;
			scores[x + x + lit2.Sign()] += 1;
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_Decided( lit ) ) continue;
			_big_clause.Add_Lit( lit );
		}
		assert( _big_clause.Size() >= 2 );
		for ( unsigned k = 0; k < _big_clause.Size(); k++ ) {
			Literal lit = _big_clause[k];
			unsigned x = _var_map[lit.Var()];
			unsigned kk;
			for ( kk = 0; kk < k; kk++ ) {
				unsigned y = _var_map[_big_clause[kk].Var()];
				edges[x].push_back( y );
			}
			for ( kk++; kk < _big_clause.Size(); kk++ ) {
				unsigned y = _var_map[_big_clause[kk].Var()];
				edges[x].push_back( y );
			}
			scores[x + x + lit.Sign()] += 1.0 / _big_clause.Size();
		}
	}
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
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
		var_weight[i] = scores[i + i] * scores[i + i + 1];
	}
	return new Greedy_Graph( comp.Vars_Size() - 1, edges );
}

void Inprocessor::Generate_Var_Order_Min_Fill_Component( Component & comp, Simple_TreeD & treed, double * var_weight )
{
	Chain init_order = treed.Transform_Chain( var_weight );
	assert( init_order.Size() == comp.Vars_Size() );
	for ( unsigned i = 0; i < init_order.Size(); i++ ) {
		unsigned index = init_order[i];
		Variable var( comp.Vars( index ) );
		ASSERT( !_var_order.Contain( var ) );
		_var_order.Append( var );
	}
}

Literal Inprocessor::Pick_Good_Lit_Component( Component & comp )  // using clause_seen
{
	if ( !running_options.phase_selecting  ) {
		Variable var = Pick_Good_Var_Component( Current_Component() );
		return Literal( var, false );
	}
	switch ( running_options.var_ordering_heur ) {
	case minfill:
		return Pick_Good_Lit_Linearly_Component( comp );
		break;
	case DLCP:
		return Pick_Good_Lit_DLCP_Component( comp );
		break;
	default:
		cerr << "ERROR[Inprocessor]: This heuristic strategy is undefined!" << endl;
		return Literal::undef;
	}
}

Literal Inprocessor::Pick_Good_Lit_Linearly_Component( Component & comp )
{
	Variable var = Pick_Good_Var_Linearly_Component( comp );
	assert( running_options.decompose_strategy == Decompose_Without_Sorting );
	Literal lit0( var, false ), lit1( var, true );
	unsigned scores[2];
	if ( false ) {  // for BCP
		scores[0] = _binary_clauses[lit1].size() + _heur_decaying_sum[lit1];
		scores[1] = _binary_clauses[lit0].size() + _heur_decaying_sum[lit0];
	}
	else {
		Lit_Appearances_Component( comp, var, scores );
	}
	if ( scores[0] + scores[1] <= 5 ) {
//		Display_Component( comp, cerr );
//		cerr << var << ": " << scores[0] << " " << scores[1] << endl;  // ToRemove
	}
	return scores[0] > scores[1] ? lit0 : lit1;
}

void Inprocessor::Lit_Appearances_Component( Component & comp, Variable var, unsigned appearances[] )
{
	Literal lit0( var, false ), lit1( var, true );
	appearances[0] = appearances[1] = 0;
	for ( unsigned i = 0; i < _old_num_binary_clauses[lit0]; i++ ) {
		appearances[0] += Lit_Undecided( _binary_clauses[lit0][i] );
	}
	for ( unsigned i = 0; i < _old_num_binary_clauses[lit1]; i++ ) {
		appearances[1] += Lit_Undecided( _binary_clauses[lit1][i] );
	}
	for ( unsigned i = 0; i < _ternary_var_membership_lists[var].size(); i += 3 ) {
		Clause & clause = _long_clauses[_ternary_var_membership_lists[var][i]];
		if ( Clause_3_SAT( clause ) ) continue;
		unsigned j;
		for ( j = 0; clause[j].Var() != var; j++ ) {}
		appearances[clause[j].Sign()]++;
	}
	for ( unsigned i = 0; i < _quaternary_var_membership_lists[var].size(); i += 4 ) {
		Clause & clause = _long_clauses[_quaternary_var_membership_lists[var][i]];
		if ( Clause_4_SAT( clause ) ) continue;
		unsigned j;
		for ( j = 0; clause[j].Var() != var; j++ ) {}
		appearances[clause[j].Sign()]++;
	}
	for ( unsigned i = 0; i < _long_var_membership_lists[var].size(); i++ ) {
		Clause & clause = _long_clauses[_long_var_membership_lists[var][i]];
		if ( Clause_GE_5_SAT( clause ) ) continue;
		unsigned j;
		for ( j = 0; clause[j].Var() != var; j++ ) {}
		appearances[clause[j].Sign()]++;
	}
}

Literal Inprocessor::Pick_Good_Lit_DLCP_Component( Component & comp )  // using clause_seen
{
	Variable var = Pick_Good_Var_DLCP_Component( comp );
	if ( false ) {  // for BCP
		Literal lit0( var, false ), lit1( var, true );
		return _lit_scores[lit0] < _lit_scores[lit1] ? lit0 : lit1;
	}
	else {
		unsigned scores[2];
		Lit_Appearances_Component( comp, var, scores );
		return scores[0] > scores[1] ? Literal( var, false ) : Literal( var, true );
	}
}

void Inprocessor::Gather_Infor_For_Counting()
{
	Init_Heur_Decaying_Sum();
	switch ( running_options.decompose_strategy ) {  /// ToModify
	case Decompose_With_Sorting:
		Generate_Membership_Lists();
		break;
	case Decompose_Without_Sorting:
		Generate_Membership_Lists_Subdivision();
		break;
	}
	_unsimplifiable_num_vars = 0;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_unsimplifiable_num_vars += Var_Appeared( i );
	}
	_fixed_num_long_clauses = _old_num_long_clauses;  // used in Filter_Long_Learnts
	while ( _fixed_num_long_clauses < _long_clauses.size() && _long_clauses[_fixed_num_long_clauses].Size() <= 3 ) {
		_fixed_num_long_clauses++;
	}
}

void Inprocessor::Generate_Membership_Lists()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned lit = i + i;
		vector<Literal>::iterator it = _binary_clauses[lit].begin();
		vector<Literal>::iterator en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			_binary_var_membership_lists[i].push_back( it->Var() );
		}
		lit = i + i + 1;
		it = _binary_clauses[lit].begin();
		en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			Variable var = it->Var();
			_binary_var_membership_lists[i].push_back( var );
			unsigned j;
			for ( j = 0; _binary_var_membership_lists[i][j] != it->Var(); j++ );
			if ( j < _binary_var_membership_lists[i].size() - 1 ) _binary_var_membership_lists[i].pop_back();
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		_long_var_membership_lists[clause[0].Var()].push_back( i );
		_long_var_membership_lists[clause[1].Var()].push_back( i );
		_long_var_membership_lists[clause[2].Var()].push_back( i );
		_long_lit_membership_lists[clause[0]].push_back( i );
		_long_lit_membership_lists[clause[1]].push_back( i );
		_long_lit_membership_lists[clause[2]].push_back( i );
		for ( unsigned j = 3; j < clause.Size(); j++ ) {
			_long_var_membership_lists[clause[j].Var()].push_back( i );
			_long_lit_membership_lists[clause[j]].push_back( i );
		}
	}
}

void Inprocessor::Generate_Membership_Lists_Subdivision()
{
	Generate_Membership_Lists_Subdivision_Binary();
	Generate_Membership_Lists_Subdivision_Long();
}

void Inprocessor::Generate_Membership_Lists_Subdivision_Binary()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned lit = i + i;
		vector<Literal>::iterator it = _binary_clauses[lit].begin();
		vector<Literal>::iterator en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			_binary_var_membership_lists[i].push_back( it->Var() );
		}
		lit = i + i + 1;
		it = _binary_clauses[lit].begin();
		en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			Variable var = it->Var();
			_binary_var_membership_lists[i].push_back( var );
			unsigned j;
			for ( j = 0; _binary_var_membership_lists[i][j] != var; j++ );
			if ( j < _binary_var_membership_lists[i].size() - 1 ) _binary_var_membership_lists[i].pop_back();  // appeared
		}
	}
}

void Inprocessor::Generate_Membership_Lists_Subdivision_Long()
{
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		switch ( clause.Size() ) {
		case 3:
			_ternary_var_membership_lists[clause[0].Var()].push_back( i );
			_ternary_var_membership_lists[clause[0].Var()].push_back( clause[1].Var() );
			_ternary_var_membership_lists[clause[0].Var()].push_back( clause[2].Var() );
			_ternary_var_membership_lists[clause[1].Var()].push_back( i );
			_ternary_var_membership_lists[clause[1].Var()].push_back( clause[0].Var() );
			_ternary_var_membership_lists[clause[1].Var()].push_back( clause[2].Var() );
			_ternary_var_membership_lists[clause[2].Var()].push_back( i );
			_ternary_var_membership_lists[clause[2].Var()].push_back( clause[0].Var() );
			_ternary_var_membership_lists[clause[2].Var()].push_back( clause[1].Var() );
			_long_lit_membership_lists[clause[0]].push_back( i );
			_long_lit_membership_lists[clause[1]].push_back( i );
			_long_lit_membership_lists[clause[2]].push_back( i );
			break;
		case 4:
			_quaternary_var_membership_lists[clause[0].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[2].Var() );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[2].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[2].Var() );
			_long_lit_membership_lists[clause[0]].push_back( i );
			_long_lit_membership_lists[clause[1]].push_back( i );
			_long_lit_membership_lists[clause[2]].push_back( i );
			_long_lit_membership_lists[clause[3]].push_back( i );
			break;
		default:
			_long_var_membership_lists[clause[0].Var()].push_back( i );
			_long_var_membership_lists[clause[1].Var()].push_back( i );
			_long_var_membership_lists[clause[2].Var()].push_back( i );
			_long_var_membership_lists[clause[3].Var()].push_back( i );
			_long_var_membership_lists[clause[4].Var()].push_back( i );
			_long_lit_membership_lists[clause[0]].push_back( i );
			_long_lit_membership_lists[clause[1]].push_back( i );
			_long_lit_membership_lists[clause[2]].push_back( i );
			_long_lit_membership_lists[clause[3]].push_back( i );
			_long_lit_membership_lists[clause[4]].push_back( i );
			for ( unsigned j = 5; j < clause.Size(); j++ ) {
				_long_var_membership_lists[clause[j].Var()].push_back( i );
				_long_lit_membership_lists[clause[j]].push_back( i );
			}
			break;
		}
	}
}

void Inprocessor::Generate_Var_Membership_Lists()
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		unsigned lit = i + i;
		vector<Literal>::iterator it = _binary_clauses[lit].begin();
		vector<Literal>::iterator en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			_binary_var_membership_lists[i].push_back( it->Var() );
		}
		lit = i + i + 1;
		it = _binary_clauses[lit].begin();
		en = _binary_clauses[lit].begin() + _old_num_binary_clauses[lit];
		for ( ; it < en; it++ ) {
			Variable var = it->Var();
			_binary_var_membership_lists[i].push_back( var );
			unsigned j;
			for ( j = 0; _binary_var_membership_lists[i][j] != it->Var(); j++ );
			if ( j < _binary_var_membership_lists[i].size() - 1 ) _binary_var_membership_lists[i].pop_back();
		}
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		Clause & clause = _long_clauses[i];
		switch ( clause.Size() ) {
		case 3:
			_ternary_var_membership_lists[clause[0].Var()].push_back( i );
			_ternary_var_membership_lists[clause[0].Var()].push_back( clause[1].Var() );
			_ternary_var_membership_lists[clause[0].Var()].push_back( clause[2].Var() );
			_ternary_var_membership_lists[clause[1].Var()].push_back( i );
			_ternary_var_membership_lists[clause[1].Var()].push_back( clause[0].Var() );
			_ternary_var_membership_lists[clause[1].Var()].push_back( clause[2].Var() );
			_ternary_var_membership_lists[clause[2].Var()].push_back( i );
			_ternary_var_membership_lists[clause[2].Var()].push_back( clause[0].Var() );
			_ternary_var_membership_lists[clause[2].Var()].push_back( clause[1].Var() );
			break;
		case 4:
			_quaternary_var_membership_lists[clause[0].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[2].Var() );
			_quaternary_var_membership_lists[clause[0].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[2].Var() );
			_quaternary_var_membership_lists[clause[1].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[2].Var()].push_back( clause[3].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( i );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[0].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[1].Var() );
			_quaternary_var_membership_lists[clause[3].Var()].push_back( clause[2].Var() );
			break;
		default:
			_long_var_membership_lists[clause[0].Var()].push_back( i );
			_long_var_membership_lists[clause[1].Var()].push_back( i );
			_long_var_membership_lists[clause[2].Var()].push_back( i );
			_long_var_membership_lists[clause[3].Var()].push_back( i );
			_long_var_membership_lists[clause[4].Var()].push_back( i );
			for ( unsigned j = 5; j < clause.Size(); j++ ) {
				_long_var_membership_lists[clause[j].Var()].push_back( i );
			}
			break;
		}
	}
}

void Inprocessor::Generate_Init_Component( Component & comp )
{
	StopWatch tmp_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) tmp_watch.Start();
	comp.Clear();  // NOTE: comp is initialized here
	Variable i;
	for ( i = Variable::start; Var_Decided( i ); i++ ) {}
	if ( Var_Appeared( i ) ) comp.Add_Var( i );
	for ( i++; i <= _max_var; i++ ) {  /// NOTE: must be sorted with respect to the lexicographic order for binary search
		if ( Var_Undecided( i ) && ( Var_Appeared( i ) ) ) comp.Add_Var( i );
	}
	comp.Add_Var( _max_var.Next() );
	comp.Dec_Var();  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
	for ( i = 0; i < _old_num_long_clauses; i++ ) {
		comp.Add_ClauseID( i );
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_dynamic_decompose += tmp_watch.Get_Elapsed_Seconds();
}

void Inprocessor::Recycle_Models( vector<Model *> & models )
{
	vector<Model *>::iterator end = models.end();
	for ( vector<Model *>::iterator itr = models.begin(); itr < end; itr++ ) {
		_model_pool->Free( *itr );
	}
	models.clear();
}

Reason Inprocessor::BCP_Component( Component & comp, unsigned start )
{
	unsigned i, j, size;
	for ( ; start < _num_dec_stack; start++ ) {
		Literal lit = ~_dec_stack[start];
		for ( i = 0, size = _binary_clauses[lit].size(); i < size; i++ ) {
			if ( Lit_UNSAT( _binary_clauses[lit][i] ) && comp.Search_Var( _binary_clauses[lit][i].Var() ) ) {
				_big_learnt[1] = _binary_clauses[lit][i];
				return Reason( lit );
			}
			else if ( Lit_Undecided( _binary_clauses[lit][i] ) && comp.Search_Var( _binary_clauses[lit][i].Var() ) ) {
				Assign( _binary_clauses[lit][i], Reason( lit ) );
			}
		}
		vector<unsigned> & watched = _long_watched_lists[lit];
		for ( i = 0, size = watched.size(); i < size; ) {
			Clause & clause = _long_clauses[watched[i]];
			assert( clause.Size() >= 3 );
			if ( clause[0] == lit ) {  // let watched[i]->lits[1] be lit, *itr can only propagate watched[i]->lits[0]
				clause[0] = clause[1];
				clause[1] = lit;
			}
			if ( Lit_SAT( clause[0] ) ) {
				i++;
				continue;
			}
			bool unit;  // itr is changed in the following loop, we cannot replace unit by j == watched[i]->len
			Literal li = clause[2];
			if ( !Lit_UNSAT( li ) ) {  // l is not falsified
				unit = false;
				clause[2] = clause[1];
				clause[1] = li;
				_long_watched_lists[li].push_back( watched[i] );
				Simply_Erase_Vector_Element( watched, i, size );
			}
			else {
				unit = true;
				for ( j = 3; j < clause.Size(); j++ ) {
					li = clause[j];
					if ( !Lit_UNSAT( li ) ) {  // l is not falsified
						unit = false;
						clause[j] = clause[1];
						clause[1] = li;
						_long_watched_lists[li].push_back( watched[i] );
						Simply_Erase_Vector_Element( watched, i, size );
						break;
					}
				}
			}
			if ( unit ) {
				if ( comp.Search_Var( clause[0].Var() ) ) {
					if ( Lit_Decided( clause[0] ) ) {
						_big_learnt[1] = clause[0];
						return Reason( watched[i], SAT_REASON_CLAUSE );  // (*itr)->lits[0] is falsified
					}
					else  {
						Assign( clause[0], Reason( watched[i], SAT_REASON_CLAUSE ) );
						i++;
					}
				}
				else i++;
			}
		}
	}
	return Reason::undef;
}

unsigned Inprocessor::Analyze_Conflict_Decision( Reason confl )  // NOTE: return the deciding level
{
	unsigned i, j, k;
	Variable var = _big_learnt[1].Var();
	_var_seen[var] = true;
	_big_learnt[0] = _big_learnt[1];
	_var_rank[var] = 0;  // NOTE: in the first stage, _big_clause records the position of each lit in _big_learnt; in the second stage, records the rest literals
	if ( confl.Is_Clause_Reason() ) {
		Clause & clause = _long_clauses[confl.Clause_Value()];
		assert( _big_learnt[0] == clause[0] );
		var = clause[1].Var();
		_var_seen[var] = true;
		_big_learnt[1] = clause[1];
		_var_rank[var] = 1;
		var = clause[2].Var();
		_var_seen[var] = true;
		_big_learnt[2] = clause[2];
		_var_rank[var] = 2;
		for ( i = 3; i < clause.Size(); i++ ) {
			var = clause[i].Var();
			_var_seen[var] = true;
			_big_learnt[i] = clause[i];
			_var_rank[var] = i;
		}
		_big_learnt.Resize( clause.Size() );
	}
	else {
		var = confl.Lit_Value().Var();
		_var_seen[var] = true;
		_big_learnt[1] = confl.Lit_Value();
		_var_rank[var] = 1;
		_big_learnt.Resize( 2 );
	}
	unsigned index = _num_dec_stack - 1;
	while ( !_var_seen[_dec_stack[index].Var()] ) index--;
	Literal uip = _dec_stack[index--];
	confl = _reasons[uip.Var()];
	_var_seen[uip.Var()] = false;
	while ( _reasons[uip.Var()] != Reason::undef ) {
		if ( confl.Is_Clause_Reason() ) {
			Clause & clause = _long_clauses[confl.Clause_Value()];
			assert( uip == clause[0] );
			var = clause[1].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				_big_learnt.Add_Lit( clause[1] );
				_var_rank[var] = _big_learnt.Size() - 1;
			}
			var = clause[2].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				_big_learnt.Add_Lit( clause[2] );
				_var_rank[var] = _big_learnt.Size() - 1;
			}
			for ( i = 3; i < clause.Size(); i++ ) {
				var = clause[i].Var();
				if ( !_var_seen[var] ) {
					_var_seen[var] = true;
					_big_learnt.Add_Lit( clause[i] );
					_var_rank[var] = _big_learnt.Size() - 1;
				}
			}
			_var_rank[_big_learnt.Last_Lit().Var()] = _var_rank[uip.Var()];
			_big_learnt.Erase_Lit( _var_rank[uip.Var()] );
		}
		else {
			var = confl.Lit_Value().Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				_big_learnt[_var_rank[uip.Var()]] = confl.Lit_Value();
				_var_rank[var] = _var_rank[uip.Var()];
			}
			else {
				_var_rank[_big_learnt.Last_Lit().Var()] = _var_rank[uip.Var()];
				_big_learnt.Erase_Lit( _var_rank[uip.Var()] );
			}
		}
		while ( !_var_seen[_dec_stack[index].Var()] ) index--;
		uip = _dec_stack[index--];
		confl = _reasons[uip.Var()];
		_var_seen[uip.Var()] = false;
	}
	_big_learnt[_var_rank[uip.Var()]] = _big_learnt[0];
	_big_learnt[0] = ~uip;
	_big_clause.Clear();
	for ( j = i = 1; i < _big_learnt.Size(); i++ ) {  // Annotate: simplify learnt
		var = _big_learnt[i].Var();
		if ( _reasons[var] == Reason::undef ) _big_learnt[j++] = _big_learnt[i];
		else {
			if ( _reasons[var].Is_Clause_Reason() ) {
				Clause & clause = _long_clauses[_reasons[var].Clause_Value()];
				if ( !_var_seen[clause[1].Var()] ) _big_learnt[j++] = _big_learnt[i];
				else {
					bool tmp_seen = _var_seen[clause.Last_Lit().Var()];
					_var_seen[clause.Last_Lit().Var()] = false;
					for ( k = 2; _var_seen[clause[k].Var()]; k++ );
					_var_seen[clause.Last_Lit().Var()] = tmp_seen;
					if ( _var_seen[clause[k].Var()] ) _big_clause.Add_Lit( _big_learnt[i] );
					else _big_learnt[j++] = _big_learnt[i];
				}
			}
			else {
				if ( !_var_seen[_reasons[var].Lit_Value().Var()] ) _big_learnt[j++] = _big_learnt[i];
				else _big_clause.Add_Lit( _big_learnt[i] );
			}
		}
	}
	assert( j + _big_clause.Size() == _big_learnt.Size() );
	_big_learnt.Resize( j );
	for ( i = 0; i < _big_clause.Size(); i++ ) _var_seen[_big_clause[i].Var()] = false;
	_var_seen[_big_learnt[0].Var()] = false;
	if ( _big_learnt.Size() == 1 ) return _base_dec_level;
	_var_seen[_big_learnt[1].Var()] = false;
	assert( Lit_Decided( _big_learnt[1] ) );
	unsigned max = 1;
	for ( i = 2; i < _big_learnt.Size(); i++ ) {
		_var_seen[_big_learnt[i].Var()] = false;
		assert( Lit_Decided( _big_learnt[i] ) );
		if ( _var_stamps[_big_learnt[i].Var()] > _var_stamps[_big_learnt[max].Var()] )
			max = i;
	}
	Literal lit = _big_learnt[max];
	_big_learnt[max] = _big_learnt[1];
	_big_learnt[1] = lit;
	unsigned level = _var_stamps[_big_learnt[0].Var()];
	return _base_dec_level > level ? _base_dec_level : level;
}

Reason Inprocessor::Add_Learnt()
{
	Reason reason;
	assert( _big_learnt.Size() > 1 );
	if ( _big_learnt.Size() == 2 ) {
		_binary_clauses[_big_learnt[0]].push_back( _big_learnt[1] );
		_binary_clauses[_big_learnt[1]].push_back( _big_learnt[0] );
		reason = Reason( _big_learnt[1] );
	}
	else {
		_long_watched_lists[_big_learnt[0]].push_back( _long_clauses.size() );
		_long_watched_lists[_big_learnt[1]].push_back( _long_clauses.size() );
		reason = Reason( _long_clauses.size(), SAT_REASON_CLAUSE );
		_long_clauses.push_back( Clause( _big_learnt ) );  // allocate memory
	}
/*	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		assert( _big_learnt[i] <= 2 * _max_var + 1 );
		assert( !_lit_seen[_big_learnt[i]] );
		_heur_decaying_sum[_big_learnt[i]] += 1 / running_options.sat_heur_decay_factor;  // Get_Approx_Imp_Component uses _heur_decaying_sum
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {  // ToModify
		_heur_decaying_sum[i+i] *= running_options.sat_heur_decay_factor;
		_heur_decaying_sum[i+i+1] *= running_options.sat_heur_decay_factor;
	}*/
	running_options.sat_heur_cumulative_inc *= ( 1 / running_options.sat_heur_decay_factor );  // ToModify
	for ( unsigned i = 0; i < _big_learnt.Size(); i++ ) {
		Bump_Heur_Lit( _big_learnt[i] );
	}
	return reason;
}

Reason Inprocessor::Get_Approx_Imp_Component( Component & comp, unsigned & backjump_level )
{
	StopWatch tmp_watch;
	if ( running_options.profile_compiling >= Profiling_Abstract ) tmp_watch.Start();
	Reason confl;
	switch( running_options.imp_strategy ) {
	case No_Implicit_BCP:
		confl = BCP_Component( comp, _num_dec_stack - 1 );
		break;
	case Full_Implicit_BCP:
		confl = Get_Approx_Imp_Component_Full_IBCP( comp );
		break;
	case Partial_Implicit_BCP:
		confl = Get_Approx_Imp_Component_Partial_IBCP( comp );
		break;
	case Partial_Implicit_BCP_Neg:
		confl = Get_Approx_Imp_Component_Partial_IBCP_Neg( comp );
		break;
	default:
		cerr << "ERROR[Inprocessor]: invalid computing strategy about implied literals!" << endl;
		exit( 1 );
	}
	if ( confl != Reason::undef ) {
		_base_dec_level = 0;
		backjump_level = Analyze_Conflict_Decision( confl );
		assert( backjump_level == _var_stamps[_big_learnt[0].Var()] );
		confl = Add_Learnt();
	}
	if ( running_options.profile_compiling >= Profiling_Abstract ) statistics.time_ibcp += tmp_watch.Get_Elapsed_Seconds();
	if ( DEBUG_OFF ) Verify_Current_Imps();  // ToModify
	return confl;
}

Reason Inprocessor::Get_Approx_Imp_Component_Full_IBCP( Component & comp )
{
	Reason confl = BCP_Component( comp, _num_dec_stack - 1 );  // NOTE: cannot replace with _dec_offsets[_num_levels - 1] because of backjump
	if ( confl != Reason::undef ) return confl;
	unsigned i, num_var = comp.Vars_Size();
	_base_dec_level = _num_levels;
	_dec_offsets[_num_levels++] = _num_dec_stack;
	unsigned up = 0, down;
	do {
		down = (unsigned) -1;
		for ( i = up; true; i++ ) {
			comp.Add_Var( _max_var.Next() );  /// NOTE: to terminate the following for-loop
			for ( ; Var_Decided( comp.Vars(i) ); i++ );
			comp.Dec_Var();  /// pop _max_var.Next()
			if ( i >= num_var ) break;
			Assign( comp.Vars(i), false, Reason::undef );
			confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
			if ( confl != Reason::undef ) {
				Analyze_Conflict_Fixed_UIP( confl, Literal( comp.Vars(i), false ) );
				Un_BCP( _dec_offsets[_num_levels - 1] );
				_num_levels--;
				Assign( comp.Vars(i), true, Add_Learnt() );
				confl = BCP_Component( comp, _num_dec_stack - 1 );
				if ( confl != Reason::undef ) return confl;
				else {
					_dec_offsets[_num_levels++] = _num_dec_stack;
					down = i - 1;
				}
			}
			else {
				Un_BCP( _dec_offsets[_num_levels - 1] );
				Assign( comp.Vars(i), true, Reason::undef );
				confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
				if ( confl != Reason::undef ) {
					Analyze_Conflict_Fixed_UIP( confl, Literal( comp.Vars(i), true ) );
					Un_BCP( _dec_offsets[_num_levels - 1] );
					_num_levels--;
					Assign( comp.Vars(i), false, Add_Learnt() );
					BCP_Component( comp, _num_dec_stack - 1 );
					_dec_offsets[_num_levels++] = _num_dec_stack;
					down = i - 1;
				}
				else Un_BCP( _dec_offsets[_num_levels - 1] );
			}
		}
		if ( down == (unsigned) -1 ) break;
		up = num_var;
		for ( i = down; true; i-- ) {
			//	Compile_Top_Down_Display_Clauses( cout, true );
			//	Compile_Top_Down_Display_Watched_List( cout );
			for ( ; i != UNSIGNED_UNDEF && Var_Decided( comp.Vars(i) ); i-- );
			if ( i == UNSIGNED_UNDEF ) break;
			Assign( comp.Vars(i), false, Reason::undef );
			confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
			if ( confl != Reason::undef ) {
				Analyze_Conflict_Fixed_UIP( confl, Literal( comp.Vars(i), false ) );
				Un_BCP( _dec_offsets[_num_levels - 1] );
				_num_levels--;
				Assign( comp.Vars(i), true, Add_Learnt() );
				confl = BCP_Component( comp, _num_dec_stack - 1 );
				if ( confl != Reason::undef ) return confl;
				else {
					_dec_offsets[_num_levels++] = _num_dec_stack;
					up = i + 1;
				}
			}
			else {
				Un_BCP( _dec_offsets[_num_levels - 1] );
				Assign( comp.Vars(i), true, Reason::undef );
				confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
				if ( confl != Reason::undef ) {
					Analyze_Conflict_Fixed_UIP( confl, Literal( comp.Vars(i), true ) );
					Un_BCP( _dec_offsets[_num_levels - 1] );
					_num_levels--;
					Assign( comp.Vars(i), false, Add_Learnt() );
					BCP_Component( comp, _num_dec_stack - 1 );
					_dec_offsets[_num_levels++] = _num_dec_stack;
					up = i + 1;
				}
				else Un_BCP( _dec_offsets[_num_levels - 1] );
			}
		}
	} while ( up < num_var );
	_num_levels--;
	return Reason::undef;
}

unsigned Inprocessor::Analyze_Conflict_Fixed_UIP( Reason confl, Literal fixed )  // NOTE: _var_stamps[LIT_VAR( fixed )] == _num_levels - 1
{
	unsigned i, j, k;
	_big_learnt.Resize( 1 );
	unsigned var = _big_learnt[1].Var();
	_var_seen[var] = true;
	if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Resize( 2 );
	if ( confl.Is_Clause_Reason() ) {
		Clause & clause = _long_clauses[confl.Clause_Value()];
		assert( _big_learnt[1] == clause[0] );
		var = clause[1].Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[1] );
		var = clause[2].Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[2] );
		for ( i = 3; i < clause.Size(); i++ ) {
			var = clause[i].Var();
			_var_seen[var] = true;
			if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[i] );
		}
	}
	else {
		var = confl.Lit_Value().Var();
		_var_seen[var] = true;
		if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( confl.Lit_Value() );
	}
	unsigned index = _num_dec_stack - 1;
	while ( !_var_seen[_dec_stack[index].Var()] ) index--;
	Literal uip = _dec_stack[index--];
	confl = _reasons[uip.Var()];
	_var_seen[uip.Var()] = false;
	while ( uip != fixed ) {
		if ( confl.Is_Clause_Reason() ) {
			Clause & clause = _long_clauses[confl.Clause_Value()];
			assert( uip == clause[0] );
			var = clause[1].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[1] );
			}
			var = clause[2].Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[2] );
			}
			for ( i = 3; i < clause.Size(); i++ ) {
				var = clause[i].Var();
				if ( !_var_seen[var] ) {
					_var_seen[var] = true;
					if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( clause[i] );
				}
			}
		}
		else {
			var = confl.Lit_Value().Var();
			if ( !_var_seen[var] ) {
				_var_seen[var] = true;
				if ( _var_stamps[var] + 1 != _num_levels ) _big_learnt.Add_Lit( confl.Lit_Value() );
			}
		}
		while ( !_var_seen[_dec_stack[index].Var()] ) index--;
		uip = _dec_stack[index--];
		confl = _reasons[uip.Var()];
		_var_seen[uip.Var()] = false;
	}
	_big_learnt[0] = ~uip;
	_big_clause.Clear();
	for ( j = i = 1; i < _big_learnt.Size(); i++ ) {
		unsigned x = _big_learnt[i].Var();
		if ( _reasons[x] == Reason::undef ) _big_learnt[j++] = _big_learnt[i];
		else{
			if ( _reasons[x].Is_Clause_Reason() ) {
				Clause & clause = _long_clauses[_reasons[x].Clause_Value()];
				if ( !_var_seen[clause[1].Var()] ) _big_learnt[j++] = _big_learnt[i];
				else {
					bool tmp_seen = _var_seen[clause.Last_Lit().Var()];
					_var_seen[clause.Last_Lit().Var()] = false;
					for ( k = 2; _var_seen[clause[k].Var()]; k++ );
					_var_seen[clause.Last_Lit().Var()] = tmp_seen;
					if ( !_var_seen[clause[k].Var()] ) _big_learnt[j++] = _big_learnt[i];
					else _big_clause.Add_Lit( _big_learnt[i] );
				}
			}
			else {
				if ( !_var_seen[_reasons[x].Lit_Value().Var()] ) _big_learnt[j++] = _big_learnt[i];
				else _big_clause.Add_Lit( _big_learnt[i] );
			}
		}
	}
	assert( j + _big_clause.Size() == _big_learnt.Size() );
	_big_learnt.Resize( j );
	for ( i = 0; i < _big_clause.Size(); i++ ) _var_seen[_big_clause[i].Var()] = false;
	_var_seen[_big_learnt[0].Var()] = false;
	if ( _big_learnt.Size() == 1 ) return _base_dec_level;
	_var_seen[_big_learnt[1].Var()] = false;
	assert( Lit_Decided( _big_learnt[1] ) );
	unsigned max = 1;
	for ( i = 2; i < _big_learnt.Size(); i++ ) {
		_var_seen[_big_learnt[i].Var()] = false;
		assert( Lit_Decided( _big_learnt[i] ) );
		if ( _var_stamps[_big_learnt[i].Var()] > _var_stamps[_big_learnt[max].Var()] )
			max = i;
	}
	Literal lit = _big_learnt[max];
	_big_learnt[max] = _big_learnt[1];
	_big_learnt[1] = lit;
	return _base_dec_level > _var_stamps[lit.Var()] ? _base_dec_level : _var_stamps[lit.Var()];  // ToCheck: I should check this line!
}

Reason Inprocessor::Get_Approx_Imp_Component_Partial_IBCP( Component & comp )
{
	unsigned i, j, k;
	Reason confl = BCP_Component( comp, _num_dec_stack - 1 );  // NOTE: cannot replace with _dec_offsets[_num_levels - 1] because of backjump
	if ( confl != Reason::undef ) return confl;
	_base_dec_level = _num_levels;
	_dec_offsets[_num_levels++] = _num_dec_stack;
	unsigned old_num_d_stack = _num_dec_stack - 1;
	while ( old_num_d_stack < _num_dec_stack ) {
		unsigned num_active_lits = 0;
		for ( i = old_num_d_stack; i < _num_dec_stack; i++) {
			unsigned lit_neg = ~_dec_stack[i];
			for ( j = 0; j < _long_lit_membership_lists[lit_neg].size(); j++ ) {
				unsigned tmp_num = num_active_lits;
				unsigned loc = _long_lit_membership_lists[lit_neg][j];
				Clause & clause = _long_clauses[loc];
				for ( k = 0; k < clause.Size(); k++ ) {
					Literal lit = clause[k];
					if ( Lit_SAT( lit ) ) break;
					if ( Lit_UNSAT( lit ) ) continue;
					_active_lits[tmp_num] = lit;  // lit is a possible implied literal, and assign ~lit to check
					tmp_num += !_lit_seen[lit];
					_lit_seen[lit] = true;
				}
				if ( k < clause.Size() ) {
					for ( k = num_active_lits; k < tmp_num; k++ ) {
						Literal lit = _active_lits[k];
						_lit_seen[lit] = false;
					}
				}
				else num_active_lits = tmp_num;
			}
		}
		vector<float> scores;
		scores.resize( num_active_lits );
		for ( i = 0; i < num_active_lits; i++ ) {
			Literal lit = _active_lits[i];
			_lit_seen[lit] = false;
			scores[i] = _heur_decaying_sum[lit];
		}
		unsigned num_curr_decisions = _num_dec_stack - old_num_d_stack;
		old_num_d_stack = _num_dec_stack;
		unsigned num_test_lits = 10 + num_curr_decisions / 20;
		float threshold = 0.0;
		if ( scores.size() > num_test_lits ) {
			threshold = kth_Element( scores, scores.size() - num_test_lits );
		}
		for ( i = 0; i < num_active_lits; i++ ) {
			Literal lit = ~_active_lits[i];
			if ( Lit_Decided( lit ) || _heur_decaying_sum[lit] < threshold ) continue;
			Assign( lit );
			confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
			if ( confl != Reason::undef ) {
				Analyze_Conflict_Fixed_UIP( confl, lit );
				Un_BCP( _dec_offsets[_num_levels - 1] );
				_num_levels--;
				Assign( ~lit, Add_Learnt() );
				confl = BCP_Component( comp, _num_dec_stack - 1 );  // NOTE: cannot use _dec_offsets[_num_levels - 1]
				if ( confl != Reason::undef ) return confl;
				else _dec_offsets[_num_levels++] = _num_dec_stack;
			}
			else Un_BCP( _dec_offsets[_num_levels - 1] );
		}
	}
	_num_levels--;
	return Reason::undef;
}

Reason Inprocessor::Get_Approx_Imp_Component_Partial_IBCP_Neg( Component & comp )
{
	unsigned i, j, k;
	Reason confl = BCP_Component( comp, _num_dec_stack - 1 );  // NOTE: cannot replace with _dec_offsets[_num_levels - 1] because of backjump
	if ( confl != Reason::undef ) return confl;
	_base_dec_level = _num_levels;
	_dec_offsets[_num_levels++] = _num_dec_stack;
	unsigned old_num_d_stack = _num_dec_stack - 1;
	while ( old_num_d_stack < _num_dec_stack ) {
		unsigned num_active_lits = 0;
		for ( i = old_num_d_stack; i < _num_dec_stack; i++) {
			unsigned lit_neg = ~_dec_stack[i];
			for ( j = 0; j < _long_lit_membership_lists[lit_neg].size(); j++ ) {
				unsigned tmp_num = num_active_lits;
				unsigned loc = _long_lit_membership_lists[lit_neg][j];
				Clause & clause = _long_clauses[loc];
				for ( k = 0; k < clause.Size(); k++ ) {
					Literal lit = clause[k];
					if ( Lit_SAT( lit ) ) break;
					if ( Lit_UNSAT( lit ) ) continue;
					_active_lits[tmp_num] = lit;  // lit is a possible implied literal, and assign ~lit to check
					tmp_num += !_lit_seen[lit];
					_lit_seen[lit] = true;
				}
				if ( k < clause.Size() ) {
					for ( k = num_active_lits; k < tmp_num; k++ ) {
						Literal lit = _active_lits[k];
						_lit_seen[lit] = false;
					}
				}
				else num_active_lits = tmp_num;
			}
		}
		vector<float> scores;
		scores.resize( num_active_lits );
		for ( i = 0; i < num_active_lits; i++ ) {
			Literal lit = _active_lits[i];
			_lit_seen[lit] = false;
			scores[i] = _heur_decaying_sum[lit];
		}
		unsigned num_curr_decisions = _num_dec_stack - old_num_d_stack;
		old_num_d_stack = _num_dec_stack;
		unsigned num_test_lits = 10 + num_curr_decisions / 20;
		float threshold = 0.0;
		if ( scores.size() > num_test_lits ) {
			threshold = kth_Element( scores, scores.size() - num_test_lits );
		}
		for ( i = 0; i < num_active_lits; i++ ) {
			Literal lit = _active_lits[i];
			if ( Lit_Decided( lit ) || _heur_decaying_sum[lit] < threshold ) continue;
			Assign( lit );
			confl = BCP_Component( comp, _dec_offsets[_num_levels - 1] );
			if ( confl != Reason::undef ) {
				Analyze_Conflict_Fixed_UIP( confl, lit );
				Un_BCP( _dec_offsets[_num_levels - 1] );
				_num_levels--;
				Assign( ~lit, Add_Learnt() );
				confl = BCP_Component( comp, _num_dec_stack - 1 );  // NOTE: cannot use _dec_offsets[_num_levels - 1]
				if ( confl != Reason::undef ) return confl;
				else _dec_offsets[_num_levels++] = _num_dec_stack;
			}
			else Un_BCP( _dec_offsets[_num_levels - 1] );
		}
	}
	_num_levels--;
	return Reason::undef;
}

unsigned Inprocessor::Dynamic_Decompose_Component( Component & source, Component smaller_comps[] )
{
	switch ( running_options.decompose_strategy ) {
	case Decompose_With_Sorting:
		return Dynamic_Decompose_Component_With_Sorting( source, smaller_comps );
		break;
	case Decompose_Without_Sorting:
		return Dynamic_Decompose_Component_Without_Sorting( source, smaller_comps );
		break;
	}
	return UNSIGNED_UNDEF;
}

unsigned Inprocessor::Dynamic_Decompose_Component_With_Sorting( Component & source, Component smaller_comps[] )
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	source.Add_Var( _max_var.Next() );  /// NOTE: to terminate the for-loop "for ( ; _assignment[source.Vars(i)] != lbool::undef || _var_seen[source.Vars(i)]; i++ );"
	Component * comp = smaller_comps;
	for ( unsigned i = 0; true; i++ ) {
		comp->Clear();  // NOTE: comp is initialized here
		for ( ; Var_Decided( source.Vars(i) ) || _var_seen[source.Vars(i)]; i++ );
		if ( i >= source.Vars_Size() - 1 ) break;
		comp->Add_Var( source.Vars(i) );
		_var_seen[source.Vars(i)] = true;
		for ( unsigned j = 0; j < comp->Vars_Size(); j++ ) {
			Variable var = comp->Vars(j);
			Add_Var_Neighbors_In_Binary_Clauses( var, *comp );
			Add_Var_Neighbors_In_Beyond_2_Clauses( var, *comp );
		}
		if ( comp->Vars_Size() == 1 ) _var_seen[source.Vars(i)] = false;
		else comp++;
	}
	source.Dec_Var();  /// pop _max_var.Next()
	unsigned result = comp - smaller_comps;
	vector<unsigned>::const_iterator it = _clause_stack.begin(), en = _clause_stack.end();
	for ( ; it < en; it++ ) _clause_status[*it] = false;  // reset satisfied clauses
	_clause_stack.clear();
	for ( comp--; comp >= smaller_comps; comp-- ) {
		StopWatch tmp_watch;  // ToRemove
		if ( running_options.profiling_inprocessing >= Profiling_Detail ) tmp_watch.Start();  // ToRemove
		comp->Sort( _qsorter ); // sorted vars and clauses are required when calling BCP_Component and Cacheable_Component::Assign
		if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_dynamic_decompose_sort += tmp_watch.Get_Elapsed_Seconds();
		for ( it = comp->VarIDs_Begin(), en = comp->VarIDs_End(); it < en; it++ ) _var_seen[*it] = false;
		for ( it = comp->ClauseIDs_Begin(), en = comp->ClauseIDs_End(); it < en; it++ ) _clause_status[*it] = false;
		comp->Add_Var( _max_var.Next() );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp->Dec_Var();  /// pop _max_var.Next()
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_dynamic_decompose += begin_watch.Get_Elapsed_Seconds();
	return result;
}

void Inprocessor::Add_Var_Neighbors_In_Binary_Clauses( Variable var, Component & target )
{
	vector<Variable>::iterator it = _binary_var_membership_lists[var].begin();
	vector<Variable>::iterator en = _binary_var_membership_lists[var].end();
	for ( ; it < en; it++ ) {
		if ( !Var_Decided( *it ) && !_var_seen[*it] ) {
			target.Add_Var( *it );
			_var_seen[*it] = true;
		}
	}
}

void Inprocessor::Add_Var_Neighbors_In_Beyond_2_Clauses( Variable var, Component & target )
{
	vector<unsigned>::iterator itr = _long_var_membership_lists[var].begin();
	vector<unsigned>::iterator end = _long_var_membership_lists[var].end();
	for ( ; itr < end; itr++ ) {
		if ( _clause_status[*itr] ) continue;
		_clause_status[*itr] = true;  // mark it as selected
		Clause & clause = _long_clauses[*itr];
		if ( Clause_GE_3_SAT( clause ) ) {
			_clause_stack.push_back( *itr );
			continue;
		}
		target.Add_ClauseID( *itr );
		unsigned k;
		for ( k = 0; clause[k].Var() != var; k++ ) {
			if ( Lit_Undecided( clause[k] ) && !_var_seen[clause[k].Var()] ) {
				target.Add_Var( clause[k].Var() );
				_var_seen[clause[k].Var()] = true;
			}
		}
		for ( k++; k < clause.Size(); k++ ) {
			if ( Lit_Undecided( clause[k] ) && !_var_seen[clause[k].Var()] ) {
				target.Add_Var( clause[k].Var() );
				_var_seen[clause[k].Var()] = true;
			}
		}
	}
}

unsigned Inprocessor::Dynamic_Decompose_Component_Without_Sorting( Component & source, Component smaller_comps[] )
{
	StopWatch begin_watch;
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	unsigned num_vars, num_cls;
	Filter_Vars_Clauses_In_Component( source, num_vars, num_cls );
	unsigned * vars = _var_rank;  // _var_rank record the undecided variables and _clause_stack record the active clauses
	Component * comp = smaller_comps;
	while ( num_vars > 0 ) {
		comp->Clear();  // NOTE: comp is initialized here
		comp->Add_Var( Variable( vars[0] ) );
		_var_seen[vars[0]] = true;
		unsigned i = 0;
		do {
			Variable var = comp->Vars(i);
			Add_Var_Neighbors_In_Binary_Clauses( var, *comp );
			Add_Var_Neighbors_In_Ternary_Clauses( var, *comp );
			Add_Var_Neighbors_In_Quaternary_Clauses( var, *comp );
			Add_Var_Neighbors_In_Beyond_4_Clauses( var, *comp );
		} while ( ++i < comp->Vars_Size() );
		_var_seen[vars[0]] = false;
		vars++, num_vars--;
		if ( comp->Vars_Size() == 1 ) continue;
		comp->Vars_Resize( 1 );
		unsigned num_rest;
		for ( i = num_rest = 0; i < num_vars; i++ ) {
			unsigned var = vars[i];
			if ( _var_seen[var] ) {
				comp->Add_Var( Variable( var ) );
				_var_seen[var] = false;
			}
			else vars[num_rest++] = vars[i];
		}
		num_vars = num_rest;
		for ( i = num_rest = 0; i < num_cls; i++ ) {
			unsigned cl = _clause_stack[i];
			if ( _clause_status[cl] == 2 ) {  // was selected
				comp->Add_ClauseID( cl );
				_clause_status[cl] = 0;  // reset
			}
			else _clause_stack[num_rest++] = _clause_stack[i];
		}
		num_cls = num_rest;
		comp->Add_Var( _max_var.Next() );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
		comp->Dec_Var();  /// pop _max_var.Next()
		ASSERT( comp->Vars_Size() >= 2 );
		comp++;
	}
	for ( unsigned i = 0; DEBUG_OFF && i < _old_num_long_clauses; i++ ) ASSERT( _clause_status[i] == 0 );  // ToRemove
	for ( Variable i = Variable::start; DEBUG_OFF && i <= _max_var; i++ ) ASSERT( !_var_seen[i] );  // ToRemove
	_clause_stack.clear();
	if ( running_options.imp_strategy != SAT_Imp_Computing ) {
		for ( Component * comp_i = smaller_comps; comp_i < comp - 1; comp_i++ ) {  // when backjump happens, reduce compilation
			if ( comp_i->Vars_Size() <= 8 ) continue;
			Component * min = comp_i;
			for ( Component * comp_j = comp_i + 1; comp_j < comp; comp_j++ ) {
				if ( comp_j->Vars_Size() < min->Vars_Size() ) min = comp_j;
			}
			if ( comp_i != min ) {
				comp_i->Swap( *min );
			}
		}
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_dynamic_decompose += begin_watch.Get_Elapsed_Seconds();
	return comp - smaller_comps;
}

void Inprocessor::Filter_Vars_Clauses_In_Component( Component & source, unsigned & num_vars, unsigned & num_cls )
{
	vector<unsigned>::const_iterator itr, end;
	num_vars = 0;
	for ( itr = source.VarIDs_Begin(), end = source.VarIDs_End(); itr < end; itr++ ) {
		_var_rank[num_vars] = *itr;
		num_vars += Var_Undecided( Variable( *itr ) );
		ASSERT( !_var_seen[*itr] );  // ToRemove
	}
	_clause_stack.resize( source.ClauseIDs_Size() );  // record clause ids
	num_cls = 0;
	for ( itr = source.ClauseIDs_Begin(), end = source.ClauseIDs_End(); itr < end; itr++ ) {
		bool sat = Clause_GE_3_SAT( _long_clauses[*itr] );
		_clause_stack[num_cls] = *itr;
		num_cls += !sat;
		_clause_status[*itr] = !sat;
	}
}

void Inprocessor::Add_Var_Neighbors_In_Ternary_Clauses( Variable var, Component & target )
{
	vector<unsigned>::iterator itr = _ternary_var_membership_lists[var].begin();
	vector<unsigned>::iterator end = _ternary_var_membership_lists[var].end();
	for ( ; itr < end; itr += 3 ) {
		if ( _clause_status[*itr] != 1 ) continue;  // satisfied or selected
		_clause_status[*itr] = 2;  // mark it as selected
		unsigned var = *(itr + 1);
		if ( Var_Undecided( Variable( var ) ) && !_var_seen[var] ) {  /// NOTE: prevent the edges from var to outside of the current component
			target.Add_Var( Variable( var ) );
			_var_seen[var] = true;
		}
		var = *(itr + 2);
		if ( Var_Undecided( Variable( var ) ) && !_var_seen[var] ) {
			target.Add_Var( Variable( var ) );
			_var_seen[var] = true;
		}
	}
}

void Inprocessor::Add_Var_Neighbors_In_Quaternary_Clauses( Variable var, Component & target )
{
	vector<unsigned>::iterator itr = _quaternary_var_membership_lists[var].begin();
	vector<unsigned>::iterator end = _quaternary_var_membership_lists[var].end();
	for ( ; itr < end; itr += 4 ) {
		if ( _clause_status[*itr] != 1 ) continue;  /// NOTE: prevent the edges from var to outside of the current component
		_clause_status[*itr] = 2;  // mark it as selected
		unsigned var = *(itr + 1);
		if ( Var_Undecided( Variable( var ) ) && !_var_seen[var] ) {
			target.Add_Var( Variable( var ) );
			_var_seen[var] = true;
		}
		var = *(itr + 2);
		if ( Var_Undecided( Variable( var ) ) && !_var_seen[var] ) {
			target.Add_Var( Variable( var ) );
			_var_seen[var] = true;
		}
		var = *(itr + 3);
		if ( Var_Undecided( Variable( var ) ) && !_var_seen[var] ) {
			target.Add_Var( Variable( var ) );
			_var_seen[var] = true;
		}
	}
}

void Inprocessor::Add_Var_Neighbors_In_Beyond_4_Clauses( Variable var, Component & target )
{
	vector<unsigned>::iterator itr = _long_var_membership_lists[var].begin();
	vector<unsigned>::iterator end = _long_var_membership_lists[var].end();
	for ( ; itr < end; itr++ ) {
		if ( _clause_status[*itr] != 1 ) continue;  // satisfied or selected
		_clause_status[*itr] = 2;  // mark it as selected
		Clause & clause = _long_clauses[*itr];
		unsigned k;
		for ( k = 0; clause[k].Var() != var; k++ ) {
			if ( Lit_Undecided( clause[k] ) && !_var_seen[clause[k].Var()] ) {
				target.Add_Var( clause[k].Var() );
				_var_seen[clause[k].Var()] = true;
			}
		}
		for ( k++; k < clause.Size(); k++ ) {
			if ( Lit_Undecided( clause[k] ) && !_var_seen[clause[k].Var()] ) {
				target.Add_Var( clause[k].Var() );
				_var_seen[clause[k].Var()] = true;
			}
		}
	}
}

bool Inprocessor::Generate_Current_Component( Component & parent, Component & current )
{
	current.Clear();
	vector<unsigned>::const_iterator itr, end;
	for ( itr = parent.VarIDs_Begin(), end = parent.VarIDs_End(); itr < end; itr++ ) {
		if ( Var_Undecided( Variable( *itr ) ) ) current.Add_Var( Variable( *itr ) );
	}
	for ( itr = parent.ClauseIDs_Begin(), end = parent.ClauseIDs_End(); itr < end; itr++ ) {
		if ( !Clause_GE_3_SAT( _long_clauses[*itr] ) ) current.Add_ClauseID( *itr );
	}
	current.Add_Var( _max_var.Next() );  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
	current.Dec_Var();  /// pop _max_var.Next()
	return current.Vars_Size();
}

Variable Inprocessor::Pick_Good_Var_Component( Component & comp )  // using clause_seen
{
	switch ( running_options.var_ordering_heur ) {
	case minfill:
		return Pick_Good_Var_Linearly_Component( comp );
		break;
	case FlowCutter:
		return Pick_Good_Var_Linearly_Component( comp );
		break;
	case LinearLRW:
		return Pick_Good_Var_Linearly_Component( comp );
		break;
	case LexicographicOrder:
		return Pick_Good_Var_Linearly_Component( comp );
		break;
	case VSADS:
		if ( !SHIELD_OPTIMIZATION ) return Pick_Good_Var_VSADS_Component( comp );
		else return Pick_Good_Var_VSADS_Improved_Component( comp );
		break;
	case DLCS:
		return Pick_Good_Var_DLCS_Component( comp );
		break;
	case DLCP:
		return Pick_Good_Var_DLCP_Component( comp );
		break;
	case dynamic_minfill:
		return Pick_Good_Var_Dminfill_Component( comp );
		break;
	default:
		cerr << "ERROR[Inprocessor]: This heuristic strategy is undefined!" << endl;
		return Variable::undef;
	}
}

Variable Inprocessor::Pick_Good_Var_Linearly_Component( Component & comp )
{
	vector<unsigned>::const_iterator itr, begin, end, best;
	itr = comp.VarIDs_Begin();
	best = itr;
	for ( itr++, end = comp.VarIDs_End(); itr < end; itr++ ) {
		assert( !Var_Decided( Variable( *itr ) ) );
		if ( _var_order.Less_Than( *itr, *best ) ) {
			best = itr;
		}
	}
	return Variable( *best );
}

Variable Inprocessor::Pick_Good_Var_Dminfill_Component( Component & comp )
{
	Lit_Scores_DLCP( comp );
	vector<unsigned>::const_iterator itr, end, best = comp.VarIDs_Begin();
	double best_score = _lit_scores[*best + *best] * _lit_scores[*best + *best + 1];
	for ( itr = comp.VarIDs_Begin() + 1, end = comp.VarIDs_End(); itr < end; itr++ ) {
		if ( _var_scores[*itr] < _var_scores[*best] ) {
			best = itr;
			best_score = _lit_scores[*best + *best] * _lit_scores[*best + *best + 1];
		}
		else if ( _var_scores[*itr] == _var_scores[*best] ) {
			double itr_score = _lit_scores[*itr + *itr] * _lit_scores[*itr + *itr + 1];
			if ( itr_score > best_score ) {
				best = itr;
				best_score = _lit_scores[*best + *best] * _lit_scores[*best + *best + 1];
			}
		}
	}
//	cerr << "_var_scores[" << *best << "] = " << _var_scores[*best] << "; best_score = " << best_score << endl;  // ToRemove
//	system( "./pause" );  // ToRemove
	return Variable( *best );
}

void Inprocessor::Lit_Scores_DLCP( Component & comp )
{
	vector<unsigned>::const_iterator itr, end;
	for ( itr = comp.VarIDs_Begin(), end = comp.VarIDs_End(); itr < end; itr++ ) {
		Variable var( *itr );
		ASSERT( !Var_Decided( var ) );
		unsigned i;
		Literal lit( var, false );
		_lit_scores[lit] = 0;
		for ( i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			Literal lit2 = _binary_clauses[lit][i];
			_lit_scores[lit] += 2 * Lit_Undecided( lit2 );
		}
		for ( ; i < _binary_clauses[lit].size(); i++ ) {
			Literal lit2 = _binary_clauses[lit][i];
			_lit_scores[lit] += Lit_Undecided( lit2 );
		}
		lit = Literal( var, true );
		_lit_scores[lit] = 0;
		for ( i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			Literal lit2 = _binary_clauses[lit][i];
			_lit_scores[lit] += 2 * Lit_Undecided( lit2 );
		}
		for ( ; i < _binary_clauses[lit].size(); i++ ) {
			Literal lit2 = _binary_clauses[lit][i];
			_lit_scores[lit] += Lit_Undecided( lit2 );
		}
	}
	for ( itr = comp.ClauseIDs_Begin(), end = comp.ClauseIDs_End(); itr < end; itr++ ) {
		Clause & clause = _long_clauses[*itr];  // undecided variable will not be considered
		if ( true ) {  // ToModify
			_big_clause.Clear();
			if ( Lit_Undecided( clause[0] ) ) _big_clause.Add_Lit( clause[0] );
			if ( Lit_Undecided( clause[1] ) ) _big_clause.Add_Lit( clause[1] );
			if ( Lit_Undecided( clause[2] ) ) _big_clause.Add_Lit( clause[2] );
			for ( unsigned i = 3; i < clause.Size(); i++ ) {
				if ( Lit_Undecided( clause[i] ) ) _big_clause.Add_Lit( clause[i] );
			}
			if ( _big_clause.Size() == 2 ) {
				_lit_scores[_big_clause[0]] += 2;
				_lit_scores[_big_clause[1]] += 2;
	//			cerr << "new binary: " << ExtLit( _big_clause[0] ) << " " << ExtLit( _big_clause[1] ) << endl;
			}
			else {
				_lit_scores[_big_clause[0]] += 1.0 / _big_clause.Size();
				_lit_scores[_big_clause[1]] += 1.0 / _big_clause.Size();
				_lit_scores[_big_clause[2]] += 1.0 / _big_clause.Size();
				for ( unsigned i = 3; i < _big_clause.Size(); i++ ) {
					_lit_scores[_big_clause[i]] += 1.0 / _big_clause.Size();
				}
			}
		}
		else if ( false ) {
			_big_clause.Clear();
			if ( Lit_Undecided( clause[0] ) ) _big_clause.Add_Lit( clause[0] );
			if ( Lit_Undecided( clause[1] ) ) _big_clause.Add_Lit( clause[1] );
			if ( Lit_Undecided( clause[2] ) ) _big_clause.Add_Lit( clause[2] );
			for ( unsigned i = 3; i < clause.Size(); i++ ) {
				if ( Lit_Undecided( clause[i] ) ) _big_clause.Add_Lit( clause[i] );
			}
			_lit_scores[_big_clause[0]] += 1.0 / _big_clause.Size();
			_lit_scores[_big_clause[1]] += 1.0 / _big_clause.Size();
			for ( unsigned i = 2; i < _big_clause.Size(); i++ ) {
				_lit_scores[_big_clause[i]] += 1.0 / _big_clause.Size();
			}
		}
		else {
			_lit_scores[clause[0]] += 1.0 / clause.Size();
			_lit_scores[clause[1]] += 1.0 / clause.Size();
			_lit_scores[clause[2]] += 1.0 / clause.Size();
			for ( unsigned i = 3; i < clause.Size(); i++ ) {
				_lit_scores[clause[i]] += 1.0 / clause.Size();
			}
		}
	}
}

Variable Inprocessor::Pick_Good_Var_VSADS_Component( Component & comp )  // using clause_seen
{
	vector<unsigned>::const_iterator itr, end, best;
	double best_score;
	for ( itr = comp.ClauseIDs_Begin(), end = comp.ClauseIDs_End(); itr < end; itr++ ) {
		_clause_status[*itr] = true;
	}
	itr = comp.VarIDs_Begin();
	best_score = Var_Score_VSADS( *itr );
	best = itr;
	for ( itr++, end = comp.VarIDs_End(); itr < end; itr++ ) {
		assert( Var_Undecided( Variable( *itr ) ) );
		double score = Var_Score_VSADS( *itr );
		if ( score > best_score ) {
			best_score = score;
			best = itr;
		}
	}
	for ( itr = comp.ClauseIDs_Begin(), end = comp.ClauseIDs_End(); itr < end; itr++ ) {
		_clause_status[*itr] = false;
	}
	return Variable( *best );
}

double Inprocessor::Var_Score_VSADS( unsigned var )
{
	if ( running_options.decompose_strategy == Decompose_With_Sorting )
		return Var_Score_VSADS_With_Sorting( var );
	else return Var_Score_VSADS_Without_Sorting( var );
}

double Inprocessor::Var_Score_VSADS_With_Sorting( unsigned var )  // using _clause_status
{
	unsigned i, num = 0;
	for ( i = 0; i < _old_num_binary_clauses[var + var]; i++ ) {
		num += Lit_Undecided( _binary_clauses[var + var][i] );
	}
	for ( i = 0; i < _old_num_binary_clauses[var + var + 1]; i++ ) {
		num +=  Lit_Undecided( _binary_clauses[var + var + 1][i] );
	}
	for ( i = 0; i < _long_var_membership_lists[var].size(); i++ ) {
		num += _clause_status[_long_var_membership_lists[var][i]];
	}
	return _heur_decaying_sum[var + var] + _heur_decaying_sum[var + var + 1] + 0.5 * num;  // this ratio is used in the software sharpSAT
}

double Inprocessor::Var_Score_VSADS_Without_Sorting( unsigned var )  // using _clause_status
{
	const double factor = 10 / running_options.sat_heur_cumulative_inc;
	unsigned num = 0;
	for ( unsigned i = 0; i < _binary_var_membership_lists[var].size(); i++ ) {
		num += Var_Undecided( _binary_var_membership_lists[var][i] );
	}
	for ( unsigned i = 0; i < _ternary_var_membership_lists[var].size(); i += 3 ) {
		num += _clause_status[_ternary_var_membership_lists[var][i]];
	}
	for ( unsigned i = 0; i < _quaternary_var_membership_lists[var].size(); i += 4 ) {
		num += _clause_status[_quaternary_var_membership_lists[var][i]];
	}
	for ( unsigned i = 0; i < _long_var_membership_lists[var].size(); i++ ) {
		num += _clause_status[_long_var_membership_lists[var][i]];
	}
	return factor * ( _heur_decaying_sum[var + var] + _heur_decaying_sum[var + var + 1] ) + num;  // this ratio is used in the software sharpSAT
}

Variable Inprocessor::Pick_Good_Var_VSADS_Improved_Component( Component & comp )  // using clause_seen
{
	const double factor = 10 / running_options.sat_heur_cumulative_inc;
	vector<unsigned>::const_iterator itr, end;
	for ( itr = comp.VarIDs_Begin(), end = comp.VarIDs_End(); itr < end; itr++ ) {
		unsigned var = *itr;
		ASSERT( !Var_Decided( Variable( var ) ) );
		double sum = _heur_decaying_sum[var + var] + _heur_decaying_sum[var + var + 1];
		_var_scores[var] = sum * factor;
		for ( unsigned i = 0; i < _binary_var_membership_lists[var].size(); i++ ) {
			_var_scores[var] += Var_Undecided( _binary_var_membership_lists[var][i] );
		}
	}
	for ( itr = comp.ClauseIDs_Begin(), end = comp.ClauseIDs_End(); itr < end; itr++ ) {
		Clause & clause = _long_clauses[*itr];  // undecided variable will not be considered
		_var_scores[clause[0].Var()] += 1;
		_var_scores[clause[1].Var()] += 1;
		_var_scores[clause[2].Var()] += 1;
		for ( unsigned i = 3; i < clause.Size(); i++ ) {
			_var_scores[clause[i].Var()] += 1;
		}
	}
	itr = comp.VarIDs_Begin();
	vector<unsigned>::const_iterator best = itr;
	for ( itr++, end = comp.VarIDs_End(); itr < end; itr++ ) {
		if ( _var_scores[*itr] > _var_scores[*best] ) {
			best = itr;
		}
	}
	if ( DEBUG_OFF && *best != Pick_Good_Var_VSADS_Component( comp ) ) {  // ToRemove
		Variable another = Pick_Good_Var_VSADS_Component( comp );
		cerr << "_var_scores[" << *best << "] = " << _var_scores[*best] << " vs _var_scores[" << another << "] = " << _var_scores[another] << endl;
		assert( *best == another );
	}
	return Variable( *best );
}

Variable Inprocessor::Pick_Good_Var_DLCS_Component( Component & comp )  // using clause_seen
{
	vector<unsigned>::const_iterator itr, end;
	for ( itr = comp.VarIDs_Begin(), end = comp.VarIDs_End(); itr < end; itr++ ) {
		unsigned var = *itr;
		ASSERT( !Var_Decided( Variable( var ) ) );
		_var_scores[var] = 0;
		for ( unsigned i = 0; i < _binary_var_membership_lists[var].size(); i++ ) {
			_var_scores[var] += Var_Undecided( _binary_var_membership_lists[var][i] );
		}
	}
	for ( itr = comp.ClauseIDs_Begin(), end = comp.ClauseIDs_End(); itr < end; itr++ ) {
		Clause & clause = _long_clauses[*itr];  // undecided variable will not be considered
		_var_scores[clause[0].Var()] += 1;
		_var_scores[clause[1].Var()] += 1;
		_var_scores[clause[2].Var()] += 1;
		for ( unsigned i = 3; i < clause.Size(); i++ ) {
			_var_scores[clause[i].Var()] += 1;
		}
	}
	itr = comp.VarIDs_Begin();
	vector<unsigned>::const_iterator best = itr;
	for ( itr++, end = comp.VarIDs_End(); itr < end; itr++ ) {
		if ( _var_scores[*itr] > _var_scores[*best] ) {
			best = itr;
		}
	}
	return Variable( *best );
}

Variable Inprocessor::Pick_Good_Var_DLCP_Component( Component & comp )  // using clause_seen
{
	Lit_Scores_DLCP( comp );
	vector<unsigned>::const_iterator itr, end, best = comp.VarIDs_Begin();
	double best_score = _lit_scores[*best + *best] * _lit_scores[*best + *best + 1];
	for ( itr = comp.VarIDs_Begin() + 1, end = comp.VarIDs_End(); itr < end; itr++ ) {
		double itr_score = _lit_scores[*itr + *itr] * _lit_scores[*itr + *itr + 1];
		if ( itr_score > best_score ) {
			best = itr;
			best_score = _lit_scores[*best + *best] * _lit_scores[*best + *best + 1];
		}
	}
	return Variable( *best );
}

Variable Inprocessor::Pick_Good_Projected_Var_Linearly_Component( Component & comp )
{
	vector<unsigned>::const_iterator itr = comp.VarIDs_Begin(), end = comp.VarIDs_End();
	bool projected = _var_projected[*(end - 1)];
	_var_projected[*(end - 1)] = true;
	for ( ; !_var_projected[*itr]; itr++ ) {}
	_var_projected[*(end - 1)] = projected;
	if ( !_var_projected[*itr] ) return Variable::undef;
	unsigned best = *itr;
	for ( itr++; itr < end; itr++ ) {
		assert( !Var_Decided( Variable( *itr ) ) );
		if ( _var_projected[*itr] && _var_order.Less_Than( *itr, best ) ) {
			best = *itr;
		}
	}
	return Variable( best );
}

void Inprocessor::Rename_Clauses_Fixed_Ordering()
{
	if ( _unary_clauses.size() == _fixed_num_vars ) return;
	_lit_equivalency.Reorder( _var_order );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
		if ( lit != _lit_equivalences[lit] ) _lit_equivalency.Add_Equivalence( lit, _lit_equivalences[lit] );
		lit = ~lit;
		if ( lit != _lit_equivalences[lit] ) _lit_equivalency.Add_Equivalence( lit, _lit_equivalences[lit] );
	}
	if ( _lit_equivalency.Empty() ) return;
//	_lit_equivalency.Display( cerr );  // ToRemove
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, false );
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
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
		_lit_equivalences[lit] = _lit_equivalency.Rename_Lit( lit );
		lit = Literal( i, true );
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
		_long_watched_lists[lit].clear();
		_long_lit_membership_lists[lit].clear();
		_lit_equivalences[lit] = _lit_equivalency.Rename_Lit( lit );
		_binary_var_membership_lists[i].clear();
		_ternary_var_membership_lists[i].clear();
		_quaternary_var_membership_lists[i].clear();
		_long_var_membership_lists[i].clear();
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
	Init_Heur_Decaying_Sum();
	Generate_Membership_Lists();
}

void Inprocessor::Gather_Learnts_Infor()
{
	unsigned i;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		statistics.num_binary_learnt += _binary_clauses[i + i].size() - _old_num_binary_clauses[i + i];
		statistics.num_binary_learnt += _binary_clauses[i + i + 1].size() - _old_num_binary_clauses[i + i + 1];
	}
	statistics.num_learnt = statistics.num_binary_learnt + _long_clauses.size() - _old_num_long_clauses;
}

BigInt Inprocessor::Count_Verified_Models_sharpSAT( CNF_Formula & cnf )
{
	StopWatch begin_watch, tmp_watch;
	ofstream fout( "solvers/sharpSAT-input.txt" );
	fout << cnf;
	fout.close();
	system( "solvers/sharpSAT solvers/sharpSAT-input.txt > solvers/sharpSAT-output.txt" );
	BigInt result;
	ifstream fin( "solvers/sharpSAT-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		if ( String_Fuzzy_Match( line, "# solutions" ) ) {
			fin >> result;
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR[Inprocessor]: sharpSAT did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}

BigInt Inprocessor::Count_Verified_Models_d4( CNF_Formula & cnf )
{
	StopWatch begin_watch, tmp_watch;
	ofstream fout( "solvers/d4-input.txt" );
	fout << cnf;
	fout.close();
	system( "solvers/d4 solvers/d4-input.txt > solvers/d4-output.txt" );
	BigInt result;
	ifstream fin( "solvers/d4-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		if ( line[0] == 's' && line[1] == ' ' ) {
			char * p = line + 2;
			sscanf( p, result );
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR[Inprocessor]: d4 did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}

BigFloat Inprocessor::Count_Verified_Models_ganak( CNF_Formula & cnf, double weights[] )
{
	StopWatch begin_watch, tmp_watch;
	ofstream fout( "solvers/ganak_wmc-input.txt" );
	for ( unsigned i = Literal::start_neg; i <= 2 * cnf.Max_Var() + 1; i += 2 ) {
		fout << "w " << ExtLit( Literal( i ) ) << ' ' << weights[i] << endl;
	}
	fout << cnf;
	fout.close();
	system( "solvers/ganak_wmc -cs 2000 solvers/ganak_wmc-input.txt > solvers/ganak_wmc-output.txt" );
	BigFloat result;
	ifstream fin( "solvers/ganak_wmc-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		if ( String_Fuzzy_Match( line, "# solutions" ) ) {
			fin.getline( line, MAX_LINE );
			sscanf( line, result );
			char *p = line;
			while ( *p != 'x' && *p != '\0' ) p++;
			if ( *p != 'x' ) break;
			p += 4;  // x10^
			float base = 10;
			int exp;
			sscanf( p, "%d", &exp );
			if ( exp < 0 ) {
				base = 0.1;
				exp = -exp;
			}
			for ( int i = 0; i < exp; i++ ) {
				result *= base;
			}
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR[Inprocessor]: ganak_wmc did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}

BigFloat Inprocessor::Count_Verified_Models_ADDMC( CNF_Formula & cnf, double weights[] )
{
	StopWatch begin_watch, tmp_watch;
	ofstream fout( "solvers/addmc-input.txt" );
	fout << "p cnf " << cnf.Num_Vars() << ' ' << cnf.Num_Clauses() << endl;
	fout << "c weights";
	for ( Literal i = Literal::start; i <= 2 * cnf.Max_Var() + 1; i++ ) {
		fout << ' ' << weights[i];
	}
	fout << endl;
	for ( unsigned i = 0; i < cnf.Num_Clauses(); i++ ) {
		fout << cnf[i] << endl;
	}
	fout.close();
	system( "solvers/addmc --cf solvers/addmc-input.txt > solvers/addmc-output.txt" );
	BigFloat result;
	ifstream fin( "solvers/addmc-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		if ( line[0] != '*' ) continue;
		char *p = line + 1;
		if ( Read_String_Change( p, "modelCount" ) ) {
			sscanf( p, result );
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR[Inprocessor]: addmc did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}

BigFloat Inprocessor::Count_Verified_Models_c2d( WCNF_Formula & cnf )
{
	StopWatch begin_watch, tmp_watch;
	ofstream fout( "solvers/c2d-input.txt" );
	fout << cnf;
	fout.close();
	system( "solvers/c2d -in solvers/c2d-input.txt > solvers/c2d-output.txt" );
	BigFloat result;
	ifstream fin( "solvers/c2d-output.txt" );
	while ( !fin.eof() ) {
		char line[MAX_LINE];
		fin.getline( line, MAX_LINE );
		char * str = line;
		if ( String_Fuzzy_Match_Prefix_Change( str, "c s exact double prec-sci" ) ) {
			sscanf( str, result );
			break;
		}
	}
	if ( fin.eof() ) {
		cerr << "ERROR[Inprocessor]: c2d did not solve this instance!" << endl;
		exit( 0 );
	}
	fin.close();
	return result;
}

void Inprocessor::Display_Heuristic_Values( ostream & out )
{
	unsigned i;
	switch ( running_options.var_ordering_heur ) {
	case VSADS:
		out << "VSADS decaying sum:" << endl;
		for ( i = Variable::start; i <= _max_var; i++ ) {
			out << i + i << ": ";
			out << _heur_decaying_sum[i + i] << endl;
			out << i + i + 1 << ": ";
			out << _heur_decaying_sum[i + i + 1] << endl;
		}
		break;
	default:
		cerr << "ERROR[Inprocessor]: This heuristic strategy is undefined!" << endl;
	}
}

void Inprocessor::Display_Conflict( Reason confl, ostream & out )
{
	unsigned i;
	if ( confl == Reason::undef ) {
		out << "confl = \tSAT_REASON_UNDEF" << endl;
	}
	else if ( confl.Is_Clause_Reason() ) {
		Clause & clause = _long_clauses[confl.Clause_Value()];
		out << "confl = " << confl.Clause_Value() << ":";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t";
			out << ExtLit( clause[i] );
		}
		out << endl;
		out << "_var_stamps = ";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t" << _var_stamps[clause[i].Var()];
		}
		out << endl;
		out << "_var_seen = ";
		for ( i = 0; i < clause.Size(); i++ ) {
			out << "\t" << _var_seen[clause[i].Var()];
		}
		out << endl;
	}
	else {
		out << "confl = \t";
		out << ExtLit( confl.Lit_Value() );
		out << endl;
		out << "_var_stamps = \t" << _var_stamps[confl.Lit_Value().Var()] << endl;
		out << "_var_seen = \t" << _var_seen[confl.Lit_Value().Var()] << endl;
	}
}

CNF_Formula * Inprocessor::Output_Old_Clauses()
{
	CNF_Formula * cnf = new CNF_Formula( _max_var );
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf->Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			cnf->Add_Binary_Clause( lit, _binary_clauses[lit][i] );
		}
		lit++;
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		cnf->Add_Clause( _long_clauses[i] );
	}
	return cnf;
}

void Inprocessor::Display_Comp_Stack( ostream & out )
{
	for ( unsigned i = 0; i < _num_levels - 1; i++ ) {
		out << "==== Level " << i << " ====" << endl;
		for ( unsigned j = _comp_offsets[i]; j < _comp_offsets[i + 1]; j++ ) {
			if ( j == _active_comps[i] ) out << "[active] ";
			_comp_stack[j].Display( out );
		}
	}
	out << "==== Level " << _num_levels - 1 << " ====" << endl;
	for ( unsigned j = _comp_offsets[_num_levels - 1]; j < _num_comp_stack; j++ ) {
		if ( j == _active_comps[_num_levels - 1] ) out << "[active] ";
		_comp_stack[j].Display( out );
	}
}

void Inprocessor::Display_Comp_And_Decision_Stacks( ostream & out )
{
	for ( unsigned i = 0; i < _num_levels - 1; i++ ) {
		out << "==== Level " << i << " ====" << endl;
		out << "Decisions:";
		for ( unsigned j = _dec_offsets[i]; j < _dec_offsets[i + 1]; j++ ) {
			out << " " << ExtLit( _dec_stack[j] );
		}
		out << endl;
		out << "Components: " << endl;
		for ( unsigned j = _comp_offsets[i]; j < _comp_offsets[i + 1]; j++ ) {
			if ( j == _active_comps[i] ) out << "[active] ";
			_comp_stack[j].Display( out );
		}
	}
	out << "==== Level " << _num_levels - 1 << " ====" << endl;
	out << "Decisions:";
	for ( unsigned j = _dec_offsets[_num_levels - 1]; j < _num_dec_stack; j++ ) {
		out << " " << ExtLit( _dec_stack[j] );
	}
	out << endl;
	for ( unsigned j = _comp_offsets[_num_levels - 1]; j < _num_comp_stack; j++ ) {
		if ( j == _active_comps[_num_levels - 1] ) out << "[active] ";
		_comp_stack[j].Display( out );
	}
}

void Inprocessor::Display_Component( Component & comp, ostream & out )
{
	unsigned i, j, lit, num = 0;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		lit = comp.Vars(i) + comp.Vars(i);
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			num++;
		}
		lit = comp.Vars(i) + comp.Vars(i) + 1;
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			num++;
		}
	}
	out << "p cnf " << _max_var - Variable::start + 1 << ' ' << num + comp.ClauseIDs_Size() << endl;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		lit = comp.Vars(i) + comp.Vars(i);
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			out << '-' << comp.Vars(i) << " ";
			out << ExtLit( _binary_clauses[lit][j] );
			out << " 0" << endl;
		}
		lit = comp.Vars(i) + comp.Vars(i) + 1;
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
			out << comp.Vars(i) << " ";
			out << ExtLit( _binary_clauses[lit][j] );
			out << " 0" << endl;
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( j = 0; j < clause.Size(); j++ ) {
			if ( Lit_Undecided( clause[j] ) ) {
				out << ExtLit( clause[j] );
				out << " ";
			}
		}
		out << "0" << endl;
	}
}

void Inprocessor::Display_Component_Fixed_Len( Component & comp, ostream & out, unsigned len )
{
	if ( len == 2 ) {
		for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
			unsigned lit = comp.Vars(i) + comp.Vars(i);
			for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
				if ( lit > _binary_clauses[lit][j] ) continue;
				if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
				out << '-' << comp.Vars(i) << " ";
				out << ExtLit( _binary_clauses[lit][j] );
				out << " 0" << endl;
			}
			lit = comp.Vars(i) + comp.Vars(i) + 1;
			for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
				if ( lit > _binary_clauses[lit][j] ) continue;
				if ( Lit_Decided( _binary_clauses[lit][j] ) ) continue;
				out << comp.Vars(i) << " ";
				out << ExtLit( _binary_clauses[lit][j] );
				out << " 0" << endl;
			}
		}
	}
	else {
		for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
			Clause & clause = _long_clauses[comp.ClauseIDs(i)];
			if ( clause.Size() != len ) continue;
			for ( unsigned j = 0; j < clause.Size(); j++ ) {
				if ( Lit_Undecided( clause[j] ) ) {
					out << ExtLit( clause[j] );
					out << " ";
				}
			}
			out << "0" << endl;
		}
	}
}

void Inprocessor::Display_Clauses_For_Counting_Component( ostream & out, Component & comp )
{
	CNF_Formula cnf( _max_var );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) {
			cnf.Add_Unary_Clause( Literal( i, _assignment[i] ) );
		}
		else if ( !comp.Search_Var( i ) ) {
			cnf.Add_Unary_Clause( Literal( i, false ) );
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) || !comp.Search_Var( i ) ) {
			continue;
		}
		Literal lit( i, false );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		lit = Literal( i, true );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		cnf.Add_Clause( _long_clauses[comp.ClauseIDs(i)] );
	}
	out << cnf;
}

void Inprocessor::Display_Clauses_For_Counting_Component( ostream & out, Component comps[], unsigned num_comp )
{
	CNF_Formula cnf( _max_var );
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) {
			cnf.Add_Unary_Clause( Literal( i, _assignment[i] ) );
		}
		else {
			unsigned j;
			for ( j = 0; j < num_comp; j++ ) {
				if ( comps[j].Search_Var( i ) ) break;
			}
			if ( j == num_comp ) {
				cnf.Add_Unary_Clause( Literal( i, false ) );
			}
		}
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) )  continue;
		unsigned j;
		for ( j = 0; j < num_comp; j++ ) {
			if ( comps[j].Search_Var( i ) ) break;
		}
		if ( j == num_comp ) continue;
		Literal lit( i, false );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
		lit = Literal( i, true );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			if ( lit > _binary_clauses[lit][j] ) continue;
			cnf.Add_Binary_Clause( lit, _binary_clauses[lit][j] );
		}
	}
	for ( unsigned i = 0; i < num_comp; i++ ) {
		for ( unsigned j = 0; j < comps[i].ClauseIDs_Size(); j++ ) {
			cnf.Add_Clause( _long_clauses[comps[i].ClauseIDs(j)] );
		}
	}
	out << cnf;
}

void Inprocessor::Display_Clauses_For_Verifying_Imp( ostream & out, Clause & clause )
{
	unsigned i;
	CNF_Formula cnf( _max_var );
	for ( i = 0; i < clause.Size(); i++ ) {
		cnf.Add_Unary_Clause( ~clause[i] );
	}
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

void Inprocessor::Get_All_Imp_Component_SAT( Component & comp, vector<Model *> & models )
{
	if ( !running_options.sat_employ_external_solver_always ) Get_All_Imp_Component( comp, models );
	else Get_All_Imp_Component_External( comp, models );
}

void Inprocessor::Get_All_Imp_Component( Component & comp, vector<Model *> & models )
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

void Inprocessor::Mark_Models_Component( Component & comp, vector<Model *> & models )
{
	if ( debug_options.verify_model ) Verify_Models_Component( models, comp );
	vector<unsigned>::const_iterator old_start = comp.VarIDs_Begin(), start, stop = comp.VarIDs_End();
	vector<Model *>::iterator begin = models.begin(), end = models.end() - 1;
	if ( begin == end ) {
		for ( start = old_start; start < stop; start++ ) {
			_model_seen[*start + *start + (**begin)[*start]] = true;
		}
	}
	else {
		for ( start = old_start; start < stop; start++ ) {
			bool tmp_bit = (**end)[*start];
			(*end)->Assign( Variable( *start ), !(**begin)[*start] );
			vector<Model *>::iterator itr = begin + 1;
			for ( ; (**itr)[*start] == (**begin)[*start]; itr++ );
			(*end)->Assign( Variable( *start ), tmp_bit );
			if ( (**itr)[*start] != (**begin)[*start] ) {
				_model_seen[*start + *start] = true;
				_model_seen[*start + *start + 1] = true;
			}
			else _model_seen[*start + *start + (**begin)[*start]] = true;
		}
	}
}

void Inprocessor::Init_Heur_Decaying_Sum_Component( Component & comp )
{
	switch ( running_options.sat_heur_lits ) {
	case Heuristic_Literal_Unsorted_List:
		break;
	case Heuristic_Literal_Sorted_List:
		Init_Heur_Decaying_Sum_Sorted_Lists_Component( comp );
		break;
	case Heuristic_Literal_Heap:
		Init_Heur_Decaying_Sum_Heap_Component( comp );
		break;
	}
}

void Inprocessor::Init_Heur_Decaying_Sum_Sorted_Lists_Component( Component & comp )
{
	unsigned i;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		_heur_sorted_lits[i + i] = Literal( var, false );
		_heur_sorted_lits[i + i + 1] = Literal( var, true );
	}
	_heur_sorted_lits[i + i] = _heur_lit_sentinel;  // NOTE: this line guarantee the correctness of "Branch"
	_heur_sorted_lits[i + i + 1] = ~_heur_lit_sentinel;
	Quick_Sort_Weight_Reverse( _heur_sorted_lits, 2 * comp.Vars_Size(), _heur_decaying_sum );
}

void Inprocessor::Init_Heur_Decaying_Sum_Heap_Component( Component & comp )
{
	unsigned heur_num_lits = 0;
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		if ( Var_Decided( var ) ) continue;
		_heur_sorted_lits[heur_num_lits++] = Literal( var, false );
		_heur_sorted_lits[heur_num_lits++] = Literal( var, true );
	}
	_heur_lits_heap.Build( _heur_sorted_lits, heur_num_lits );
}

bool Inprocessor::Learnts_Exploded()
{
//	return _long_clauses.size() > _max_var / 2 + _old_num_long_clauses; // ToRemove
	return _long_clauses.size() - _fixed_num_long_clauses > 2 * ( _max_var + 1 + _old_num_long_clauses );
}

void Inprocessor::Filter_Long_Learnts()
{
	unsigned i;
	for ( i = _clause_status.size(); i < _long_clauses.size(); i++ ) {
		_clause_status.push_back( false );
	}
	_clause_stack.resize( _long_clauses.size() );
	for ( i = 0; i < _num_dec_stack; i++ ) {
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
				if ( !Two_Unassigned_Literals( *itr ) ) itr->Free();
				else _long_clauses[i++] = *itr;
			}
		}
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
	if ( running_options.sat_heur_lits == Heuristic_Literal_Heap ) running_options.sat_heur_cumulative_inc = 1;
}

Literal Inprocessor::Pick_Imp_Component_Heuristic( Component & comp, vector<unsigned>::const_iterator & start )
{
	comp.Add_Var( _max_var.Next() );  /// NOTE: to terminate the following for-loop
 	for ( ; Var_Decided( Variable( *start ) ) + _model_seen[*start + *start] + _model_seen[*start + *start + 1] > 1; start++ );
	Literal lit( Variable( *start ), _model_seen[*start + *start + 1] );
	vector<unsigned>::const_iterator itr = start + 1;
	vector<unsigned>::const_iterator end = comp.VarIDs_End();
	for ( ; itr < end; itr++ ) {
		if ( Var_Decided( Variable( *itr ) ) + _model_seen[*itr + *itr] + _model_seen[*itr + *itr + 1] > 1 ) continue;
		Literal tmp( Variable( *itr ), _model_seen[*itr + *itr + 1] );
		if ( _heur_decaying_sum[tmp] > _heur_decaying_sum[lit] ) lit = tmp;
	}
	comp.Dec_Var();  /// pop _max_var.Next()
	return lit;
}

Reason Inprocessor::Imply_Lit_Out_Reason_Component( Component & comp, Literal lit, vector<Model *> & models )
{
	assert( Lit_Undecided( lit ) );
	unsigned old_num_levels = _num_levels;
	Reason sat_reason;
	while ( true ) {
		Extend_New_Level();
		Assign( ~lit );
		Reason conf = BCP( _num_dec_stack - 1 );
		if ( conf != Reason::undef ) {
			Analyze_Conflict_Fixed_UIP( conf, ~lit );
			Backjump( old_num_levels );  /// NOTE: need to put back to heap
			return Add_Learnt_Sort_Component( comp );
		}
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_solve++;
		unsigned num_restart = 0;
		double restart_bound = Restart_Bound_Component( comp );
		while ( ( sat_reason = Search_Solution_Component( comp, restart_bound ) ) == Reason::unknown ) {
			restart_bound *= running_options.sat_restart_trigger_inc;
			num_restart++;
		}
		if ( sat_reason != Reason::mismatched ) break;  // Otherwise, we detected another implied literal not \lit
		Backjump( old_num_levels );
		Assign( _big_learnt[0], Add_Learnt_Sort_Component( comp ) );  // Analyzing Conflict was done in Search_Solution_Component
		BCP( _num_dec_stack - 1 );
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
		if ( Lit_SAT( lit ) ) return _reasons[lit.Var()];  // already Backtracked
	}
	if ( sat_reason == Reason::undef ) {
		Add_Marked_Model_Component( comp, models );  // Un_BCP will change _assignment
		Backjump( old_num_levels );
		if ( debug_options.verify_model ) Verify_Model_Component( models.back(), comp );
		return Reason::undef;
	}
	else {
		Analyze_Conflict_Fixed_UIP( sat_reason, ~lit );
		Backjump( old_num_levels );
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
		return Add_Learnt_Sort_Component( comp );
	}
}

unsigned Inprocessor::Restart_Bound_Component( Component & comp )
{
//	return UNSIGNED_UNDEF;
	switch( 2 ) {
	case 1:
		return comp.Vars_Size() - 2 + comp.ClauseIDs_Size();
		break;
	case 2:
		return running_options.sat_restart_trigger_init;
		break;
	}
}

void Inprocessor::Add_Marked_Model_Component( Component & comp, vector<Model *> & models )
{
	Model * model = _model_pool->Allocate();
	vector<unsigned>::const_iterator itr = comp.VarIDs_Begin(), end = comp.VarIDs_End();
	for ( ; itr < end; itr++ ) {
		ASSERT( _assignment[*itr] != lbool::unknown );
		model->Assign( Variable( *itr ), _assignment[*itr] == true );
		_model_seen[*itr + *itr + _assignment[*itr]] = true;
	}
	models.push_back( model );
}

void Inprocessor::Get_All_Imp_Component_External( Component & comp, vector<Model *> & models )
{
	StopWatch begin_watch;
	assert( !models.empty() );
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) begin_watch.Start();
	if ( Learnts_Exploded() ) Filter_Long_Learnts();
	BCP( _num_dec_stack - 1 );
	if ( running_options.sat_solver == solver_MiniSat ) Get_All_Imp_Component_MiniSat( comp, models );
	else if ( running_options.sat_solver == solver_CaDiCaL ) Get_All_Imp_Component_CaDiCaL( comp, models );
	else {
		cerr << "ERROR[Inprocessor]: invalid external solver!" << endl;
		exit( 1 );
	}
	if ( running_options.profiling_inprocessing >= Profiling_Detail ) statistics.time_solve += begin_watch.Get_Elapsed_Seconds();
}

void Inprocessor::Get_All_Imp_Component_MiniSat( Component & comp, vector<Model *> & models )
{
	unsigned pos;
	vector<vector<int>> eclauses;
	Prepare_Renamed_Ext_Clauses_Component( comp, eclauses );  // NOTE: _var_map is assigned in this function
	_minisat_extra_output.return_model = !Hyperscale_Problem();
	_minisat_extra_output.return_units = true;
	_minisat_extra_output.return_learnt_max_len = 2;
	vector<int8_t> emodel( comp.Vars_Size() + 1 );
	for ( unsigned i = 0; i < models.size(); i++ ) {
		for ( unsigned j = 0; j < comp.Vars_Size(); j++ ) {
			Variable var = comp.Vars( j );
			emodel[ExtVar( _var_map[var] )] = (*models[i])[var];
		}
		_minisat_extra_output.models.push_back( emodel );
	}
	unsigned minisat_extra_output_old_num_models = _minisat_extra_output.models.size();
	bool sat = Minisat::Ext_Backbone( eclauses, _minisat_extra_output );
	assert( sat );
	for ( unsigned i = 0; i < _minisat_extra_output.units.size(); i++ ) {
		Literal renamed_lit = InternLit( _minisat_extra_output.units[i] );
		pos = renamed_lit.Var() - Variable::start;
		Literal lit( comp.Vars( pos ), renamed_lit.Sign() );
		if ( Lit_Undecided( lit ) ) {
			Analyze_Conflict_Naive( ~lit );
			Assign( lit, Add_Learnt() );
			BCP( _num_dec_stack - 1 );
		}
	}
	for ( unsigned i = 0; i < _minisat_extra_output.short_learnts[0].size(); i += 2 ) {
		Literal renamed_lit = InternLit( _minisat_extra_output.short_learnts[0][i] );
		pos = renamed_lit.Var() - Variable::start;
		Literal lit = Literal( comp.Vars( pos ), renamed_lit.Sign() );
		renamed_lit = InternLit( _minisat_extra_output.short_learnts[0][i+1] );
		pos = renamed_lit.Var() - Variable::start;
		Literal lit2 = Literal( comp.Vars( pos ), renamed_lit.Sign() );
		Add_Extra_Binary_Clause_Naive( lit, lit2 );
	}
	for ( unsigned i = minisat_extra_output_old_num_models; i < _minisat_extra_output.models.size(); i++ ) {
		Add_Model_Component( _minisat_extra_output.models[i], comp, models );
	}
	_minisat_extra_output.models.clear();
}

void Inprocessor::Prepare_Renamed_Ext_Clauses_Component( Component & comp, vector<vector<int>> & eclauses )
{
	vector<int> unary_ext_clause( 1 );
	vector<int> ext_clause( 2 );
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		_var_map[comp.Vars( i )] = i + Variable::start;
	}
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		if ( Var_Decided( var ) ) {
			unary_ext_clause[0] = ExtLit( Literal( _var_map[var], _assignment[var] ) );
			eclauses.push_back( unary_ext_clause );
			_var_seen[_var_map[var]] = true;
			continue;
		}
		ext_clause[0] = -1 * (int)(_var_map[var]);  // unsigned to signed
		for ( unsigned j = 0; j < _binary_clauses[var + var].size(); j++ ) {
			Literal lit = _binary_clauses[var + var][j];
			if ( var + var > lit ) continue;
			if ( Lit_Decided( lit ) ) continue;
			Literal renamed_lit = Literal( _var_map[lit.Var()], lit.Sign() );
			ext_clause[1] = ExtLit( renamed_lit );
			eclauses.push_back( ext_clause );
			_var_seen[_var_map[var]] = true;
			_var_seen[_var_map[lit.Var()]] = true;
		}
		for ( unsigned j = 0; j < _extra_binary_clauses[var + var].size(); j++ ) {
			Literal lit = _extra_binary_clauses[var + var][j];
			if ( var + var > lit ) continue;
			if ( Lit_Decided( lit ) ) {
				if ( _var_stamps[lit.Var()] < _base_dec_level ) {  // remove decided variable
					Simply_Erase_Vector_Element( _extra_binary_clauses[var + var], j );
					j--;
				}
				continue;
			}
			Literal renamed_lit = Literal( _var_map[lit.Var()], lit.Sign() );
			ext_clause[1] = ExtLit( renamed_lit );
			eclauses.push_back( ext_clause );
			_var_seen[_var_map[var]] = true;
			_var_seen[_var_map[lit.Var()]] = true;
		}
		ext_clause[0] = _var_map[var];
		for ( unsigned j = 0; j < _binary_clauses[var + var + 1].size(); j++ ) {
			Literal lit = _binary_clauses[var + var + 1][j];
			if ( var + var + 1 > lit ) continue;
			if ( Lit_Decided( lit ) ) continue;
			Literal renamed_lit = Literal( _var_map[lit.Var()], lit.Sign() );
			ext_clause[1] = ExtLit( renamed_lit );
			eclauses.push_back( ext_clause );
			_var_seen[_var_map[var]] = true;
			_var_seen[_var_map[lit.Var()]] = true;
		}
		for ( unsigned j = 0; j < _extra_binary_clauses[var + var + 1].size(); j++ ) {
			Literal lit = _extra_binary_clauses[var + var + 1][j];
			if ( var + var + 1 > lit ) continue;
			if ( Lit_Decided( lit ) ) {
				if ( _var_stamps[lit.Var()] < _base_dec_level ) {  // remove decided variable
					Simply_Erase_Vector_Element( _extra_binary_clauses[var + var + 1], j );
					j--;
				}
				continue;
			}
			Literal renamed_lit = Literal( _var_map[lit.Var()], lit.Sign() );
			ext_clause[1] = ExtLit( renamed_lit );
			eclauses.push_back( ext_clause );
			_var_seen[_var_map[var]] = true;
			_var_seen[_var_map[lit.Var()]] = true;
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		Clause & clause = _long_clauses[comp.ClauseIDs( i )];
		ext_clause.clear();
		unsigned j;
		for ( j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) continue;
			ext_clause.push_back( ExtLit( _var_map[lit.Var()], lit.Sign() ) );
		}
		if ( j == clause.Size() ) {  // not sat yet
			assert( ext_clause.size() >= 2 );
			eclauses.push_back( ext_clause );
			for ( j = 0; j < ext_clause.size(); j++ ) {
				_var_seen[InternLit( ext_clause[j] )] = true;
			}
		}
	}
	ext_clause.resize(2);
	for ( Variable i = Variable::start; i <= Variable::start + comp.Vars_Size() - 1; i++ ) {
		if ( !_var_seen[i] ) {
			ext_clause[0] = ExtLit( i, false );
			ext_clause[1] = ExtLit( i, true );
			eclauses.push_back( ext_clause );
		}
		else _var_seen[i] = false;
	}
	if ( DEBUG_OFF ) {
		for ( unsigned i = 0; i < eclauses.size(); i++ ) {  // ToRemove
			for ( unsigned j = 0; j < eclauses[i].size(); j++ ) {  // ToRemove
				if ( InternVar( eclauses[i][j] ) > Variable::start + comp.Vars_Size() - 1 ) {  // ToRemove
					cerr << "comp.vars.size() = " << comp.Vars_Size() << endl;
					cerr << "eclauses[" << i << "][" << j << "] = " << eclauses[i][j] << endl;
					assert( InternVar( eclauses[i][j] ) <= Variable::start + comp.Vars_Size() - 1 );
				}
			}  // ToRemove
		}  // ToRemove
	}
}

unsigned Inprocessor::Analyze_Conflict_Naive( Literal uip )
{
	unsigned i;
	_big_learnt[0] = ~uip;
	_big_learnt.Resize( 1 );
	for ( i = 1; i < _num_levels - 1; i++ ) {
		if ( _dec_offsets[i + 1] > _dec_offsets[i] ) {
			_big_learnt.Add_Lit( ~_dec_stack[_dec_offsets[i]] );
		}
	}
	if ( _num_dec_stack > _dec_offsets[i] ) {
		_big_learnt.Add_Lit( ~_dec_stack[_dec_offsets[i]] );
	}
	Literal lit = _big_learnt.Last_Lit();
	_big_learnt.Last_Lit() = _big_learnt[1];
	_big_learnt[1] = lit;
	return _base_dec_level > _var_stamps[lit.Var()] ? _base_dec_level : _var_stamps[lit.Var()]; // I should check this line!
}

void Inprocessor::Add_Extra_Binary_Clause_Naive( Literal lit1, Literal lit2 )
{
	assert( 2 <= lit1 && lit1 <= _max_var + _max_var + 1 );
	assert( 2 <= lit2 && lit2 <= _max_var + _max_var + 1 );
	_extra_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr;
	for ( itr = _extra_binary_clauses[lit1].begin(); *itr != lit2; itr++ ) {}
	if ( itr != _extra_binary_clauses[lit1].end() - 1 ) _extra_binary_clauses[lit1].pop_back();
	else _extra_binary_clauses[lit2].push_back( lit1 );
}

void Inprocessor::Add_Model_Component( vector<int8_t> & minisat_model, Component & comp, vector<Model *> & models )
{
	assert( minisat_model.size() - 1 == comp.Vars_Size() );
	Model * model = _model_pool->Allocate();
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars( i );
		model->Assign( var, minisat_model[ExtVar( Variable( i+Variable::start ) )] > 0 );
	}
	if ( DEBUG_OFF ) Verify_Model_Component( model, comp );  // ToModify
	models.push_back( model );
}

void Inprocessor::Get_All_Imp_Component_CaDiCaL( Component & comp, vector<Model *> & models )
{
	if ( _cadiback == nullptr ) Prepare_CadiBack();
	unsigned old_size = _num_dec_stack;
	_cadiback->calculate( comp, *this, models, _model_pool );
	for ( unsigned i = old_size; i < _num_dec_stack; i++ ) {
		Literal lit = _dec_stack[i];
		Analyze_Conflict_CaDiCaL( ~lit );
		_reasons[lit.Var()] = Add_Learnt();
	}
	BCP( old_size );
	if ( DEBUG_OFF ) Verify_All_Imp_Component( comp );
}

unsigned Inprocessor::Analyze_Conflict_CaDiCaL( Literal uip )
{
	if ( _cadiback == nullptr ) Prepare_CadiBack();
	_big_learnt[0] = ~uip;
	_big_learnt.Resize( 1 );
	for ( unsigned i = 1; i < _num_levels - 1; i++ ) {
		if ( _dec_offsets[i + 1] > _dec_offsets[i] ) {
			_big_learnt.Add_Lit( ~_dec_stack[_dec_offsets[i]] );
		}
	}
	if ( _num_dec_stack > _dec_offsets[_num_levels - 1] ) {
		_big_learnt.Add_Lit( ~_dec_stack[_dec_offsets[_num_levels - 1]] );
	}
	for ( unsigned i = 1; i < _big_learnt.Size(); ) {
		Literal lit = _big_learnt[i];
		_big_learnt[i] = ~lit;
		if ( _cadiback->imply( _big_learnt ) ) _big_learnt.Erase_Lit( i );
		else _big_learnt[i++] = lit;
	}
	assert( _big_learnt.Size() > 1 );
	unsigned max = 1;
	for ( unsigned i = 2; i < _big_learnt.Size(); i++ ) {
		if ( _var_stamps[_big_learnt[i].Var()] > _var_stamps[_big_learnt[max].Var()] ) max = i;
	}
	Literal lit = _big_learnt[max];
	_big_learnt[max] = _big_learnt[1];
	_big_learnt[1] = lit;
	return _base_dec_level > _var_stamps[lit.Var()] ? _base_dec_level : _var_stamps[lit.Var()]; // I should check this line!
}

void Inprocessor::Verify_All_Imp_Component( Component & comp )
{
	CaDiCaL::Solver solver;
	for ( unsigned i = 0; i < _dec_offsets[_num_levels - 1] + 1; i++ ) {
		solver.clause( ExtLit( _dec_stack[i] ) );
	}
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1;  ) {
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			solver.clause( ExtLit( lit ), ExtLit( _binary_clauses[lit][i] ) );
		}
		lit++;
		for ( unsigned i = 0; i < _old_num_binary_clauses[lit]; i++ ) {
			if ( lit > _binary_clauses[lit][i] ) continue;
			solver.clause( ExtLit( lit ), ExtLit( _binary_clauses[lit][i] ) );
		}
		lit++;
	}
	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
		solver.clause( ExtLits( _long_clauses[i] ) );
	}
	assert( solver.solve() == 10 );
	for ( unsigned i = _dec_offsets[_num_levels - 1] + 1; i < _num_dec_stack; i++ ) {
		assert( comp.Search_Var( _dec_stack[i].Var() ) );
		solver.assume( -ExtLit( _dec_stack[i] ) );
		if ( solver.solve() != 20 ) {
			Display_Comp_And_Decision_Stacks( cerr );
			cerr << "ERROR[Inprocessor]: wrong implied literal " << ExtLit( _dec_stack[i] ) << "!" << endl;
			exit( 0 );
		}
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		if ( Var_Decided( x ) ) continue;
		solver.assume( -x );
		assert( solver.solve() == 10 );
		solver.assume( x );
		assert( solver.solve() == 10 );
	}
}

unsigned Inprocessor::Num_Projected_Vars_Assigned( unsigned start )  // vars[num] == max_var
{
    unsigned num = 0;
    for ( ; start < _num_dec_stack; start++ ) {
        bool projected = _var_projected[_dec_stack[start].Var()];  // selected only if the position is not greater than max_var;
        num += projected;
    }
	return num;
}

void Inprocessor::Reset_Extra_Binary_Clauses()
{
	for ( unsigned i = Variable::start; i <= _max_var; i++ ) {
		_extra_binary_clauses[i + i].clear();
		_extra_binary_clauses[i + i + 1].clear();
	}
}

void Inprocessor::Get_All_Projected_Imp_Component( Component & comp, vector<Model *> & models )
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

Literal Inprocessor::Pick_Projected_Imp_Component_Heuristic( Component & comp, vector<unsigned>::const_iterator & start )
{
	_var_projected[_max_var + 1] = true;
	comp.Add_Var( _max_var.Next() );  /// NOTE: to terminate the following for-loops
	for ( ; ; start++ ) {
		if ( !_var_projected[*start] || Var_Decided( Variable( *start ) ) ) continue;
		if ( !_model_seen[*start + *start] || !_model_seen[*start + *start + 1] ) break;
	}
	Literal lit( Variable( *start ), _model_seen[*start + *start + 1] );
	vector<unsigned>::const_iterator itr = start + 1;
	vector<unsigned>::const_iterator end = comp.VarIDs_End();
	for ( ; itr < end; itr++ ) {
		if ( !_var_projected[*itr] || Var_Decided( Variable( *itr ) ) ) continue;
		if ( _model_seen[*itr + *itr] && _model_seen[*itr + *itr + 1] ) continue;
		Literal tmp( Variable( *itr ), _model_seen[*itr + *itr + 1] );
		if ( _heur_decaying_sum[tmp] > _heur_decaying_sum[lit] ) lit = tmp;
	}
	comp.Dec_Var();  /// pop _max_var.Next()
	_var_projected[_max_var + 1] = false;
	return lit;
}

Reason Inprocessor::Imply_Projected_Lit_Out_Reason_Component( Component & comp, Literal lit, vector<Model *> & models )
{
	assert( Lit_Undecided( lit ) && _var_projected[lit.Var()] );
	unsigned old_num_levels = _num_levels;
	Reason sat_reason;
	while ( true ) {
		Extend_New_Level();
		Assign( ~lit );
		Reason conf = BCP( _num_dec_stack - 1 );
		if ( conf != Reason::undef ) {
			Analyze_Conflict_Fixed_UIP( conf, ~lit );
			Backjump( old_num_levels );  /// NOTE: need to put back to heap
			return Add_Learnt_Sort_Component( comp );
		}
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_solve++;
		unsigned num_restart = 0;
		double restart_bound = Restart_Bound_Component( comp );
		while ( ( sat_reason = Search_Solution_Projected_Component( comp, restart_bound ) ) == Reason::unknown ) {
			restart_bound *= running_options.sat_restart_trigger_inc;
			num_restart++;
		}
		if ( sat_reason != Reason::mismatched ) break;  // Otherwise, we detected another implied literal not \lit
		Backjump( old_num_levels );
		Assign( _big_learnt[0], Add_Learnt_Sort_Component( comp ) );  // Analyzing Conflict was done in Search_Solution_Component
		BCP( _num_dec_stack - 1 );
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
		if ( Lit_SAT( lit ) ) return _reasons[lit.Var()];  // already Backtracked
	}
	if ( sat_reason == Reason::undef ) {
		Add_Marked_Model_Component( comp, models );  // Un_BCP will change _assignment
		Backjump( old_num_levels );
		if ( debug_options.verify_model ) Verify_Model_Component( models.back(), comp );
		return Reason::undef;
	}
	else {
		Analyze_Conflict_Fixed_UIP( sat_reason, ~lit );
		Backjump( old_num_levels );
		if ( running_options.profile_solving >= Profiling_Detail ) statistics.num_unsat_solve++;
		return Add_Learnt_Sort_Component( comp );
	}
}

Reason Inprocessor::Search_Solution_Projected_Component( Component & comp, unsigned conf_limit )
{
	unsigned old_num_levels = _num_levels;
	assert( old_num_levels >= 3 );  /// required all initialized implied literals are pulled out
	unsigned old_size = _long_clauses.size();
	Literal branch;
	while ( ( branch = Branch_Component( comp ) ) != _heur_lit_sentinel ) {
		Extend_New_Level();
		Assign( branch );
		Reason conf = BCP( _num_dec_stack - 1 );
		while ( conf != Reason::undef ) {
			assert( _num_levels >= old_num_levels );
			if ( _num_levels == old_num_levels ) {
				return conf;  // UNSAT
			}
			unsigned back_level = Analyze_Conflict( conf );
			assert( _big_learnt.Size() > 1 && back_level >= 2 );  /// not required all initialized implied literals are pulled out
			if ( back_level < old_num_levels - 1 ) {
				Backjump( old_num_levels );
				return Reason::mismatched;  // implied literal by some previous level before \old_num_levels
			}
			Backjump( back_level + 1 );
			Assign( _big_learnt[0], Add_Learnt_Sort_Component( comp ) );
			if ( _long_clauses.size() - old_size > conf_limit ) {
				Backjump( old_num_levels );
				return Reason::unknown;  // restart
			}
			conf = BCP( _num_dec_stack - 1 );
		}
	}
	return Reason::undef;  // SAT
}

void Inprocessor::Verify_Model_Component( Model * model, Component & comp )
{
	unsigned i, j;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Literal lit( comp.Vars(i), !(*model)[comp.Vars(i)] );
		for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal li = _binary_clauses[lit][j];
			if ( lit > li ) continue;
			if ( Lit_SAT( li ) ) continue;
			if ( model->Falsify( li ) ) {
				cerr << "ERROR[Inprocessor]: not satisfy ";
				cerr << ExtLit( lit ) << " " << ExtLit( li ) << endl;
				ofstream fout( "debug.txt" );
				comp.Display( fout );
				fout.close();
				assert( false );
			}
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		Clause & clause = _long_clauses[comp.ClauseIDs( i )];
		for ( j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) continue;
			if ( (*model)[lit.Var()] == lit.Sign() ) break;
		}
		if ( j == clause.Size() ) {
			cerr << "ERROR[Inprocessor]: not satisfy ";
			clause.Display( cerr );
			assert( false );
		}
	}
}

void Inprocessor::Verify_Models_Component( vector<Model *> models, Component & comp )
{
	for ( vector<Model *>::iterator itr = models.begin(); itr < models.end(); itr++ ) {
		unsigned i, j;
		for ( i = 0; i < comp.Vars_Size(); i++ ) {
			Literal lit( comp.Vars(i), !(**itr)[comp.Vars(i)] );
			for ( j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
				Literal li = _binary_clauses[lit][j];
				if ( lit > li ) continue;
				if ( Lit_SAT( li ) ) continue;
				if ( (*itr)->Falsify( li ) ) {
					cerr << "ERROR[Inprocessor]: Model " << itr - models.begin() << " does not satisfy ";
					cerr << ExtLit( lit ) << " " << ExtLit( li ) << endl;
					assert( false );
				}
			}
		}
		for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
			Clause & clause = _long_clauses[comp.ClauseIDs( i )];
			for ( j = 0; j < clause.Size(); j++ ) {
				Literal lit = clause[j];
				if ( Lit_SAT( lit ) ) break;
				if ( Lit_UNSAT( lit ) ) continue;
				if ( (**itr)[lit.Var()] == lit.Sign() ) break;
			}
			if ( j == clause.Size() ) {
				cerr << "ERROR[Inprocessor]: Model " << itr - models.begin() << " does not satisfy ";
				clause.Display( cerr );
				assert( false );
			}
		}
	}
}

void Inprocessor::Verify_Membership_Lists()
{
	Verify_Long_Lit_Membership_Lists();
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		for ( unsigned j = 0; j < _binary_var_membership_lists[i].size(); j++ ) {
			unsigned neighbor = _binary_var_membership_lists[i][j];
			assert( neighbor <= _max_var );
			bool exi = false;
			for ( unsigned k = 0; k < _old_num_binary_clauses[i + i]; k++ ) {
				exi = exi || ( neighbor == _binary_clauses[i + i][k].Var() );
			}
			for ( unsigned k = 0; k < _old_num_binary_clauses[i + i + 1]; k++ ) {
				exi = exi || ( neighbor == _binary_clauses[i + i + 1][k].Var() );
			}
			assert( exi );
		}
		for ( unsigned j = 0; j < _ternary_var_membership_lists[i].size(); j += 3 ) {
			assert( _ternary_var_membership_lists[i][j] < _long_clauses.size() );
			for ( unsigned k = 0; k < j; k += 3 ) {
				assert( _ternary_var_membership_lists[i][k] != _ternary_var_membership_lists[i][j] );
			}
			Clause & clause = _long_clauses[_ternary_var_membership_lists[i][j]];
			assert( clause.Size() == 3 );
			assert( clause[0].Var() == i || clause[1].Var() == i || clause[2].Var() == i );
			unsigned x = _ternary_var_membership_lists[i][j+1];
			assert( clause[0].Var() == x || clause[1].Var() == x || clause[2].Var() == x );
			x = _ternary_var_membership_lists[i][j+2];
			assert( clause[0].Var() == x || clause[1].Var() == x || clause[2].Var() == x );
		}
		for ( unsigned j = 0; j < _quaternary_var_membership_lists[i].size(); j += 4 ) {
			assert( _quaternary_var_membership_lists[i][j] < _long_clauses.size() );
			for ( unsigned k = 0; k < j; k += 4 ) {
				assert( _quaternary_var_membership_lists[i][k] != _quaternary_var_membership_lists[i][j] );
			}
			Clause & clause = _long_clauses[_quaternary_var_membership_lists[i][j]];
			assert( clause.Size() == 4 );
			assert( clause[0].Var() == i || clause[1].Var() == i || clause[2].Var() == i || clause[3].Var() == i );
			unsigned x = _quaternary_var_membership_lists[i][j+1];
			assert( clause[0].Var() == x || clause[1].Var() == x || clause[2].Var() == x || clause[3].Var() == x );
			x = _quaternary_var_membership_lists[i][j+2];
			assert( clause[0].Var() == x || clause[1].Var() == x || clause[2].Var() == x || clause[3].Var() == x );
			x = _quaternary_var_membership_lists[i][j+3];
			assert( clause[0].Var() == x || clause[1].Var() == x || clause[2].Var() == x || clause[3].Var() == x );
		}
		for ( unsigned j = 0; j < _long_var_membership_lists[i].size(); j++ ) {
			Clause & clause = _long_clauses[_long_var_membership_lists[i][j]];
			assert( clause.Size() >= 5 );
			assert( _long_var_membership_lists[i][j] < _long_clauses.size() );
		}
	}
	for ( unsigned i = 0; i < _long_clauses.size(); i++ ) {
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			unsigned num = 0;
			for ( unsigned j = 0; j < _long_var_membership_lists[x].size(); j++ ) {
				num += ( _long_var_membership_lists[x][j] == i );
			}
			Clause & clause = _long_clauses[i];
			bool exi = false;
			for ( unsigned j = 0; j < clause.Size(); j++ ) {
				exi = exi || ( x == clause[j] );
			}
			if ( num != exi ) {
				cerr << "_long_clauses[" << i << "] = " << _long_clauses[i] << endl;
				cerr << "_long_var_membership_lists[" << x << "] has " << num << " No. " << i << endl;
				assert( num == exi );
			}
		}
	}
}

CNF_Formula * Inprocessor::Output_Original_Clauses_In_Component( Component & comp )
{
	CNF_Formula * cnf = new CNF_Formula( _max_var );
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Literal lit( comp.Vars( i ), false );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			cnf->Add_Binary_Clause( lit, lit2 );
		}
		lit = Literal( comp.Vars( i ), true );
		for ( unsigned j = 0; j < _old_num_binary_clauses[lit]; j++ ) {
			Literal lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			cnf->Add_Binary_Clause( lit, lit2 );
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( unsigned j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_Decided( lit ) ) continue;
			_big_clause.Add_Lit( lit );
		}
		assert( _big_clause.Size() >= 2 );
		cnf->Add_Clause( _big_clause );
	}
	return cnf;
}

CNF_Formula * Inprocessor::Output_Original_And_Learnt_Clauses_In_Component( Component & comp )
{
	unsigned i, j, k;
	Literal lit, lit2;
	CNF_Formula * cnf = new CNF_Formula( _max_var );
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		lit = Literal( comp.Vars( i ), false );
		for ( j = 0; j < _binary_clauses[lit].size(); j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			cnf->Add_Binary_Clause( lit, lit2 );
		}
		for ( j = 0; j < _long_watched_lists[lit].size(); j++ ) {
			unsigned watched_id = _long_watched_lists[lit][j];
			if ( watched_id < _old_num_long_clauses ) continue;
			Clause & clause = _long_clauses[watched_id];
			assert( clause.Size() >= 3 );
			if ( clause[1] == lit ) continue;  // stop being repeatedly used
			if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) continue;
			for ( k = 2; k < clause.Size() && Lit_UNSAT( clause[k] ); k++ ) {}
			if ( k == clause.Size() ) cnf->Add_Binary_Clause( clause[0], clause[1] );
		}
		lit = Literal( comp.Vars( i ), true );
		for ( j = 0; j < _binary_clauses[lit].size(); j++ ) {
			lit2 = _binary_clauses[lit][j];
			if ( lit > lit2 ) continue;
			if ( Lit_Decided( lit2 ) ) continue;
			cnf->Add_Binary_Clause( lit, lit2 );
		}
		for ( j = 0; j < _long_watched_lists[lit].size(); j++ ) {
			unsigned watched_id = _long_watched_lists[lit][j];
			if ( watched_id < _old_num_long_clauses ) continue;
			Clause & clause = _long_clauses[watched_id];
			assert( clause.Size() >= 3 );
			if ( clause[1] == lit ) continue;  // stop being repeatedly used
			if ( Lit_SAT( clause[0] ) || Lit_SAT( clause[1] ) ) continue;
			for ( k = 2; k < clause.Size() && Lit_UNSAT( clause[k] ); k++ ) {}
			if ( k == clause.Size() ) cnf->Add_Binary_Clause( clause[0], clause[1] );
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
		cnf->Add_Clause( _big_clause );
	}
	return cnf;
}

CNF_Formula * Inprocessor::Output_Renamed_Clauses_In_Component( Component & comp )
{
	unsigned i, j;
	Literal lit, lit2, old_lit;
	CNF_Formula * cnf = new CNF_Formula( Variable::start + comp.Vars_Size() - 1 );
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		_var_map[comp.Vars(i)] = i + Variable::start;
	}
	for ( i = 0; i < comp.Vars_Size() ; i++ ) {
		Variable var = comp.Vars(i);
		if ( Var_Decided( var ) ) {
			cnf->Add_Unary_Clause( Literal( _var_map[var], _assignment[var] ) );
			continue;
		}
		lit = Literal( _var_map[var], false );
		for ( j = 0; j < _old_num_binary_clauses[var + var]; j++ ) {
			old_lit = _binary_clauses[var + var][j];
			if ( var + var > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			cnf->Add_Binary_Clause( lit, lit2 );
		}
		lit = Literal( _var_map[var], true );
		for ( j = 0; j < _old_num_binary_clauses[var + var + 1]; j++ ) {
			old_lit = _binary_clauses[var + var + 1][j];
			if ( var + var + 1 > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			cnf->Add_Binary_Clause( lit, lit2 );
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( j = 0; j < clause.Size(); j++ ) {
			old_lit = clause[j];
			if ( Lit_SAT( old_lit ) ) break;
			if ( Lit_UNSAT( old_lit ) ) continue;
			lit = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			_big_clause.Add_Lit( lit );
		}
		if ( j == clause.Size() ) {
			assert( _big_clause.Size() >= 2 );
			cnf->Add_Clause( _big_clause );
		}
	}
	return cnf;
}

WCNF_Formula * Inprocessor::Output_Renamed_Clauses_In_Component( Component & comp, BigFloat * weights )
{
	unsigned i, j;
	Literal lit, lit2, old_lit;
	WCNF_Formula * cnf = new WCNF_Formula( Variable::start + comp.Vars_Size() - 1 );
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var = comp.Vars(i);
		_var_map[var] = i + Variable::start;
		lit = Literal( _var_map[var], false );
		cnf->Set_Weight( lit, weights[Literal(var, false)].TransformDouble() );
		lit = Literal( _var_map[var], true );
		cnf->Set_Weight( lit, weights[Literal(var, true)].TransformDouble() );
	}
	for ( i = 0; i < comp.Vars_Size() ; i++ ) {
		Variable var = comp.Vars(i);
		if ( Var_Decided( var ) ) {
			cnf->Add_Unary_Clause( Literal( _var_map[var], _assignment[var] ) );
			continue;
		}
		lit = Literal( _var_map[var], false );
		for ( j = 0; j < _old_num_binary_clauses[var + var]; j++ ) {
			old_lit = _binary_clauses[var + var][j];
			if ( var + var > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			cnf->Add_Binary_Clause( lit, lit2 );
		}
		lit = Literal( _var_map[var], true );
		for ( j = 0; j < _old_num_binary_clauses[var + var + 1]; j++ ) {
			old_lit = _binary_clauses[var + var + 1][j];
			if ( var + var + 1 > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			cnf->Add_Binary_Clause( lit, lit2 );
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		for ( j = 0; j < clause.Size(); j++ ) {
			old_lit = clause[j];
			if ( Lit_SAT( old_lit ) ) break;
			if ( Lit_UNSAT( old_lit ) ) continue;
			lit = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			_big_clause.Add_Lit( lit );
		}
		if ( j == clause.Size() ) {
			assert( _big_clause.Size() >= 2 );
			cnf->Add_Clause( _big_clause );
		}
	}
	return cnf;
}

void Inprocessor::Output_Renamed_Clauses_In_Component( Component & comp, vector<Clause> & clauses )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		_var_map[comp.Vars(i)] = i + Variable::start;
	}
	for ( unsigned i = 0; i < comp.Vars_Size() ; i++ ) {
		Variable var = comp.Vars(i);
		if ( Var_Decided( var ) ) {
			clauses.push_back( Literal( _var_map[var], _assignment[var] ) );
			continue;
		}
		Literal lit = Literal( _var_map[var], false );
		for ( unsigned j = 0; j < _old_num_binary_clauses[var + var]; j++ ) {
			Literal old_lit = _binary_clauses[var + var][j];
			if ( var + var > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			Literal lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			clauses.push_back( Clause( lit, lit2 ) );
		}
		lit = Literal( _var_map[var], true );
		for ( unsigned j = 0; j < _old_num_binary_clauses[var + var + 1]; j++ ) {
			Literal old_lit = _binary_clauses[var + var + 1][j];
			if ( var + var + 1 > old_lit ) continue;
			if ( Lit_Decided( old_lit ) ) continue;
			Literal lit2 = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			clauses.push_back( Clause( lit, lit2 ) );
		}
	}
	for ( unsigned i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		_big_clause.Clear();
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		unsigned j;
		for ( j = 0; j < clause.Size(); j++ ) {
			Literal old_lit = clause[j];
			if ( Lit_SAT( old_lit ) ) break;
			if ( Lit_UNSAT( old_lit ) ) continue;
			Literal lit = Literal( _var_map[old_lit.Var()], old_lit.Sign() );
			_big_clause.Add_Lit( lit );
		}
		if ( j == clause.Size() ) {
			assert( _big_clause.Size() >= 2 );
			clauses.push_back( Clause( _big_clause ) );
		}
	}
}

void Inprocessor::Output_Renamed_Clauses_In_Component( Component & comp, vector<vector<int>> & eclauses )
{
	unsigned i, j;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		_var_map[comp.Vars(i)] = i + Variable::start;
	}
	vector<int> elits;
	for ( i = 0; i < comp.Vars_Size(); i++ ) {
		Variable var( comp.Vars(i) );
		if ( Var_Decided( var ) ) {
			elits.resize( 1 );
			elits[0] = ExtLit( Literal( _var_map[var], _assignment[var] ) );
			eclauses.push_back( elits );
			continue;
		}
		elits.resize( 2 );
		elits[0] = ExtLit( Literal( _var_map[var], false ) );
		for ( j = 0; j < _old_num_binary_clauses[var + var]; j++ ) {
			Literal lit = _binary_clauses[var + var][j];
			if ( var + var > lit ) continue;
			if ( Lit_Decided( lit ) ) continue;
			elits[1] = ExtLit( Literal( _var_map[lit.Var()], lit.Sign() ) );
			eclauses.push_back( elits );
		}
		elits[0] = ExtLit( Literal( _var_map[var], true ) );
		for ( j = 0; j < _old_num_binary_clauses[var + var + 1]; j++ ) {
			Literal lit = _binary_clauses[var + var + 1][j];
			if ( var + var + 1 > lit ) continue;
			if ( Lit_Decided( lit ) ) continue;
			elits[1] = ExtLit( Literal( _var_map[lit.Var()], lit.Sign() ) );
			eclauses.push_back( elits );
		}
	}
	for ( i = 0; i < comp.ClauseIDs_Size(); i++ ) {
		Clause & clause = _long_clauses[comp.ClauseIDs(i)];
		elits.clear();
		for ( j = 0; j < clause.Size(); j++ ) {
			Literal lit = clause[j];
			if ( Lit_SAT( lit ) ) break;
			if ( Lit_UNSAT( lit ) ) continue;
			elits.push_back( ExtLit( Literal( _var_map[lit.Var()], lit.Sign() ) ) );
		}
		if ( j == clause.Size() ) {
			assert( elits.size() >= 2 );
			eclauses.push_back( elits );
		}
	}
}

void Inprocessor::Pick_Models( vector<Model *> & source, Literal lit, vector<Model *> & target )
{
	assert( target.empty() );
	unsigned i, size;
	for ( i = 0, size = source.size(); i < size; ) {
		if ( (*source[i])[lit.Var()] == lit.Sign() ) {
			target.push_back( source[i] );
			Simply_Erase_Vector_Element( source, i, size );
		}
		else i++;
	}
	assert( !source.empty() && !target.empty() );
}

void Inprocessor::Move_Models( vector<Model *> & source, vector<Model *> & target )
{
	target.insert( target.end(), source.begin(), source.end() );
	source.clear();
}

void Inprocessor::Inherit_Models( vector<Model *> & source, Literal lit, vector<Model *> & target )
{
	assert( !source.empty() && target.empty() );
	unsigned i, size = source.size();
	for ( i = 0; i < size; i++ ) {
		if ( (*source[i])[lit.Var()] == lit.Sign() ) {
			source[i]->Copy();
			target.push_back( source[i] );
		}
	}
	assert( !source.empty() && !target.empty() );
}

void Inprocessor::Copy_Models( vector<Model *> & source, vector<Model *> & target )
{
	assert( !source.empty() && target.empty() );
	unsigned i, size = source.size();
	target.resize( size );
	for ( i = 0; i < size; i++ ) {
		source[i]->Copy();
		target[i] = source[i];
	}
	assert( !source.empty() && !target.empty() );
}

void Inprocessor::Raise_Models( vector<Model *> & source, unsigned target_level )
{
	for ( Model * model: source ) {
		for ( unsigned i = _dec_offsets[target_level]; i < _num_dec_stack; i++ ) {
			model->Assign( _dec_stack[i] );
		}
	}
	vector<Model *> & target = _models_stack[target_level];
	target.insert( target.end(), source.begin(), source.end() );
	source.clear();
}

void Inprocessor::Input_Models( vector<Model *> & source )
{
	assert( !source.empty() && _models_stack[0].empty() );
	unsigned i, size = source.size();
	for ( i = 0; i < size; i++ ) {
		Model * model = _model_pool->Allocate();
		model->Assign( source[i], Variable( running_options.variable_bound ) );
		_models_stack[0].push_back( model );
	}
}

void Inprocessor::Input_Models_Component( Component & comp, vector<Model *> & source )
{
	assert( _models_stack[0].empty() );
	Variable maxv;
	if ( Is_Oracle_Mode() ) maxv = running_options.variable_bound;
	else maxv = _max_var;
	if ( source.empty() ) return;
	Model & orig_model = *source[0];
	Model * model = _model_pool->Allocate();
	_models_stack[0].push_back( model );
	if ( source.size() == 1 ) {
		if ( maxv == Variable::start + comp.Vars_Size() - 1 ) {
			model->Assign( source[0], maxv );
		}
		else {
			Model * model2 = _model_pool->Allocate();
			_models_stack[0].push_back( model2 );
			for ( Variable j = Variable::start; j <= maxv; j++ ) {
				model->Assign( j, false );
				model2->Assign( j, true );
			}
			for ( unsigned j = 0; j < comp.Vars_Size(); j++ ) {
				Variable var = comp.Vars(j);
				model->Assign( var, orig_model[var] );
				model2->Assign( var, orig_model[var] );
			}
		}
	}
	else {
		for ( Variable j = Variable::start; j <= maxv; j++ ) {
			model->Assign( j, false );
		}
		for ( unsigned j = 0; j < comp.Vars_Size(); j++ ) {
			Variable var = comp.Vars(j);
			model->Assign( var, orig_model[var] );
		}
		for ( unsigned i = 1; i < source.size(); i++ ) {
			Model & orig_model2 = *source[i];
			Model * model2 = _model_pool->Allocate();
			_models_stack[0].push_back( model2 );
			for ( Variable j = Variable::start; j <= maxv; j++ ) {
				model2->Assign( j, true );
			}
			for ( unsigned j = 0; j < comp.Vars_Size(); j++ ) {
				Variable var = comp.Vars(j);
				model2->Assign( var, orig_model2[var] );
			}
		}
	}
}

void Inprocessor::Lend_Models( vector<Model *> & models, unsigned size )
{
	assert( _max_var != Variable::undef );
	for ( unsigned i = 0; i < size; i++ ) {
		models.push_back( _model_pool->Allocate() );
	}
}

void Inprocessor::Display_Var_Membership_Lists_With_Sorting( ostream & out )
{
	out << "binary variable membership list [variables]: " << endl;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << ExtVar( i ) << ": ";
		vector<Variable>::iterator itr = _binary_var_membership_lists[i].begin();
		vector<Variable>::iterator end = _binary_var_membership_lists[i].end();
		for ( ; itr < end; itr++ ) out << *itr << ' ';
		out << endl;
	}
	out << "long variable membership list [" << _old_num_long_clauses << " long clauses]: " << endl;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		out << ExtVar( i ) << ": ";
		vector<unsigned>::iterator itr = _long_var_membership_lists[i].begin();
		vector<unsigned>::iterator end = _long_var_membership_lists[i].end();
		for ( ; itr < end; itr++ ) {
			out << *itr << ' ';
		}
		out << endl;
	}
}

void Inprocessor::Display_Models( vector<Model *> & source, ostream & fout )
{
	unsigned i, size;
	for ( i = 0, size = source.size(); i < size; i++ ) {
		source[i]->Display_Simple( _max_var, fout );
	}
}


}
