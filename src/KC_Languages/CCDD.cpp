#include "CCDD.h"


namespace KCBox {


CCDD_Manager::CCDD_Manager( Variable max_var, unsigned estimated_node_num ):
CDD_Manager( max_var, estimated_node_num ),
_lit_sets( _max_var + 1 )
{
	Generate_Lexicographic_Var_Order( _max_var );
	Allocate_and_Init_Auxiliary_Memory();
}

void CCDD_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_lit_equivalency.Reorder( _var_order );
	_lit_equivalency_low.Reorder( _var_order );
	_lit_equivalency_high.Reorder( _var_order );
	_many_vars = new Variable [_max_var + 1];
	_many_lits = new Literal [2 * _max_var + 4];
	_many_nodes = new NodeID [_max_var + 2];
	_many_lit_nodes = new NodeID [_max_var + 2];
	_many_equ_nodes = new NodeID [_max_var + 2];
	_equ_node_seen = new bool [_max_var + 2];
	_node_sets = new NodeID * [_max_var + 2];
	_node_set_sizes = new unsigned [_max_var + 2];
	_many_sets = new SetID [_max_var + 1];
	_aux_rnode.Reset_Max_Var( _max_var );
	_aux_decom_rnode.Reset_Max_Var( _max_var );
	_aux_kerne_rnode.Reset_Max_Var( _max_var );
	_condition_rnode.Reset_Max_Var( _max_var );
	_lit_sets.Enlarge_Fullset( _max_var + 1 );  // no tautologies
	_decision_stack = new Literal [_max_var + 1];
	_decision_levels = new unsigned [_max_var + 2];
	_cache_stack = new unsigned [_max_var + 2];
	for ( unsigned i = 0; i <= _max_var; i++ ) {
		_equ_node_seen[i] = false;
	}
	_aux_decom_rnode.sym = CDD_SYMBOL_DECOMPOSE;
	_aux_kerne_rnode.sym = CDD_SYMBOL_KERNELIZE;
}

CCDD_Manager::CCDD_Manager( Chain & vorder, unsigned estimated_node_num ):
CDD_Manager( Variable( vorder.Max() ), estimated_node_num ),
Linear_Order( vorder ),
_lit_sets( _max_var + 1 )
{
	Allocate_and_Init_Auxiliary_Memory();
}

CCDD_Manager::CCDD_Manager( istream & fin ):
CDD_Manager( Variable::start, LARGE_HASH_TABLE ),
_lit_sets( 2 )
{
	if ( fin.fail() ) {
		cerr << "ERROR[CDD]: the CDD file cannot be opened!" << endl;
		exit( 0 );
	}
	vector<unsigned> arr;
	char line[MAX_LINE];
	fin.getline( line, MAX_LINE );
	char * p = line;
	unsigned max_var;
	if ( sscanf( line, "Maximum variable: %u", &max_var ) != 1 ) {
		cerr << "ERROR[CDD]: the CDD-file does not state the maximum variable!" << endl;
		exit( 1 );
	}
	_max_var = InternVar( max_var );
	Diagram_Manager::Allocate_and_Init_Auxiliary_Memory( _max_var );
	CDD_Manager::Enlarge_Max_Var( _max_var );
	Allocate_and_Init_Auxiliary_Memory();
	fin.getline( line, MAX_LINE );
	unsigned num_node;
	if ( sscanf( line, "Number of nodes: %u", &num_node ) != 1 ) {
		cerr << "ERROR[CDD]: wrong CDD-file format, no num_node!" << endl;
	}
	fin.getline( line, MAX_LINE );
	p = line;
	if ( Read_Unsigned_Change( p ) != 0 ) cerr << "ERROR[CDD]: the false-node has a wrong ID!" << endl;
	if ( *p == ':' ) p++;
	else cerr << "ERROR[CDD]: the false-node has a wrong separation character!" << endl;
	if ( !String_Fuzzy_Match( p, "F 0" ) ) cerr << "ERROR[CDD]: wrong CDD-file format, wrong false-node!" << endl;
	fin.getline( line, MAX_LINE );
	p = line;
	if ( Read_Unsigned_Change( p ) != 1 ) cerr << "ERROR[CDD]: the true-node has a wrong ID!" << endl;
	if ( *p == ':' ) p++;
	else cerr << "ERROR[CDD]: the true-node has a wrong separation character!" << endl;
	if ( !String_Fuzzy_Match( p, "T 0" ) ) cerr << "ERROR[CDD]: wrong CDD-file format, wrong true-node!" << endl;
	for ( unsigned u = 2; u < _num_fixed_nodes; u++ ) {
		Literal lit = Node2Literal( u );
		fin.getline( line, MAX_LINE );
		p = line;
		if ( Read_Unsigned_Change( p ) != u ) cerr << "ERROR[CDD]: the " << u << "-node has a wrong ID!" << endl;
		if ( *p == ':' ) p++;
		else cerr << "ERROR[CDD]: the " << u << "-node has a wrong separation character!" << endl;
		arr.clear();
		Exactly_Read_Unsigneds( p, arr );
		if ( arr.size() != 4 || arr[0] !=  lit.Var() || arr[1] != lit.NSign() || arr[2] != lit.Sign() || arr[3] != 0 )
			cerr << "ERROR[CDD]: wrong CDD-file format, wrong " << u << "-node!" << endl;
	}
	for ( unsigned u = _num_fixed_nodes; u < num_node; u++ ) {
		arr.clear();
		CDD_Node node;
		fin.getline( line, MAX_LINE );
		p = line;
		if ( Read_Unsigned_Change( p ) != u ) cerr << "ERROR[CDD]: wrong CDD-file format, the " << u << "th node is invalid!" << endl;
		if ( *p == ':' ) p++;
		else cerr << "ERROR[CDD]: wrong CDD-file format, the " << u << "th node is invalid!" << endl;
		while ( BLANK_CHAR( *p ) ) p++;
		if ( *p == 'D' || *p == 'S' ) {
			node.sym = ( *p == 'D' ) ? CDD_SYMBOL_DECOMPOSE : CDD_SYMBOL_KERNELIZE;
			p++;
			Exactly_Read_Unsigneds( p, arr );
			node.ch_size = arr.size() - 1;
			if ( node.ch_size < 2 || arr[node.ch_size] != 0 )
				cerr << "ERROR[CDD]: wrong CDD-file format, the " << u << "th node is invalid!" << endl;
			node.ch = new NodeID [node.ch_size];
			for ( unsigned i = 0; i < node.ch_size; i++ ) node.ch[i] = arr[i];
		}
		else if ( *p == 'E' ) {
			node.sym = CDD_SYMBOL_EQU;
			p++;
			Exactly_Read_Unsigneds( p, arr );
			node.ch_size = arr.size() - 1;
			if ( node.ch_size < 2 || arr[node.ch_size] != 0 )
				cerr << "ERROR[CDD]: wrong CDD-file format, the " << u << "th node is invalid!" << endl;
			node.ch = new NodeID [node.ch_size];
			for ( unsigned i = 0; i < node.ch_size; i++ ) node.ch[i] = arr[i];
		}
		else {
			Exactly_Read_Unsigneds( p, arr );
			node.ch_size = arr.size() - 2;
			if ( node.ch_size != 2 || arr[3] != 0 )
				cerr << "ERROR[CDD]: wrong CDD-file format, the " << u << "th node is invalid!" << endl;
			node.sym = arr[0];
			node.ch = new NodeID [2];
			node.ch[0] = arr[1];
			node.ch[1] = arr[2];
		}
		Push_New_Node( node );
	}
}

CCDD_Manager::CCDD_Manager( CCDD_Manager & other ):
CDD_Manager( other._max_var, other._nodes.Size() * 2 ),
_lit_sets( 2 * _max_var + 2 )
{
	Allocate_and_Init_Auxiliary_Memory();
	for ( unsigned u = _num_fixed_nodes; u < other._nodes.Size(); u++ ) {
		Push_New_Node( other._nodes[u] );
	}
}

CCDD_Manager::~CCDD_Manager()
{
	Free_Auxiliary_Memory();
}

void CCDD_Manager::Free_Auxiliary_Memory()
{
	delete [] _many_vars;
	delete [] _many_lits;
	delete [] _many_nodes;
	delete [] _many_lit_nodes;
	delete [] _many_equ_nodes;
	delete [] _equ_node_seen;
	delete [] _node_sets;
	delete [] _node_set_sizes;
	delete [] _many_sets;
	delete [] _decision_stack;
	delete [] _decision_levels;
	delete [] _cache_stack;
}

void CCDD_Manager::Reorder( const Chain & new_order )
{
	if ( _nodes.Size() > _num_fixed_nodes ) {
		cerr << "ERROR[CCDD]: cannot be reordered with non-fixed nodes yet!" << endl;
	}
	_var_order = new_order;
	_lit_equivalency.Reorder( new_order );
	_lit_equivalency_low.Reorder( new_order );
	_lit_equivalency_high.Reorder( new_order );
}

void CCDD_Manager::Enlarge_Max_Var( Chain & new_order )
{
	assert( _var_order.Subchain( new_order ) );
	if ( new_order.Max() - Variable::start + 1 != new_order.Size() ) {
		cerr << "ERROR[CCDD]: wrong variable ordering!" << endl;
		exit( 1 );
	}
	_var_order = new_order;
	CDD_Manager::Enlarge_Max_Var( Variable( _var_order.Max() ) );
	Free_Auxiliary_Memory();
	Allocate_and_Init_Auxiliary_Memory();
}

void CCDD_Manager::Load_Nodes( RCDD_Manager & other )
{
	assert( _max_var == other.Max_Var() );
	assert( _nodes.Size() == _num_fixed_nodes );
	Reorder( other.Var_Order() );
	Swap_Nodes( other );
}

BigInt CCDD_Manager::Count_Models( CDD root )
{
	unsigned num_vars = NumVars( _max_var );
	BigInt result;
	if ( Is_Fixed( root ) ) {
	    if ( root == NodeID::bot ) return 0;
        result.Assign_2exp( num_vars - ( root != NodeID::top ) );
		return result;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigInt * results = new BigInt [root + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.mark = _max_var;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.mark = _max_var;
	while ( num_node_stack ) {
	    CDD top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
//	    cerr << top << ": ";
//	    topn.Display( cerr );
		assert( topn.ch_size >= 0 );
		if ( topn.infor.mark != UNSIGNED_UNDEF ) {
			num_node_stack--;
		}
		else if ( topn.sym <= _max_var ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.ch[1];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				CDD_Node & low = _nodes[topn.ch[0]];
				CDD_Node & high = _nodes[topn.ch[1]];
				if ( low.infor.mark < high.infor.mark ) {
					results[top] = results[topn.ch[1]];
					results[top].Mul_2exp( high.infor.mark - low.infor.mark );
					results[top] += results[topn.ch[0]];
					topn.infor.mark = low.infor.mark - 1;
				}
				else {
					results[top] = results[topn.ch[0]];
					results[top].Mul_2exp( low.infor.mark - high.infor.mark );
					results[top] += results[topn.ch[1]];
					topn.infor.mark = high.infor.mark - 1;
				}
				if ( DEBUG_OFF ) {
					cerr << "results[" << topn.ch[0] << "] = " << results[topn.ch[0]] << " * 2 ^ " << _nodes[topn.ch[0]].infor.mark << endl;
					cerr << "results[" << topn.ch[1] << "] = " << results[topn.ch[1]] << " * 2 ^ " << _nodes[topn.ch[1]].infor.mark << endl;
					cerr << "results[" << top << "] = " << results[top] << " * 2 ^ " << topn.infor.mark << endl;
				}
				_visited_nodes.push_back( top );
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( loc == topn.ch_size ) {
				num_node_stack--;
				results[top] = 1;
				topn.infor.mark = num_vars - topn.ch_size;
				_visited_nodes.push_back( top );
			}
			else if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[loc];
				_node_mark_stack[num_node_stack++] = true;
				for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				num_node_stack--;
				results[top] = results[topn.ch[loc]];
				topn.infor.mark = _nodes[topn.ch[loc]].infor.mark;
                for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
                    results[top] *= results[topn.ch[i]];
                    topn.infor.mark += _nodes[topn.ch[i]].infor.mark;
                }
                topn.infor.mark -= ( topn.ch_size - loc - 1 ) * num_vars + loc;
				_visited_nodes.push_back( top );
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				results[top] = results[topn.ch[0]];
				topn.infor.mark = _nodes[topn.ch[0]].infor.mark - ( topn.ch_size - 1 );
				_visited_nodes.push_back( top );
			}
		}
	}
	result = results[root];
	result.Mul_2exp( _nodes[root].infor.mark );
    _nodes[NodeID::bot].infor.mark = UNSIGNED_UNDEF;
    _nodes[NodeID::top].infor.mark = UNSIGNED_UNDEF;
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.mark = UNSIGNED_UNDEF;
	}
	delete [] results;
	return result;
}

void CCDD_Manager::Mark_Models( CDD root, vector<BigFloat> & results )
{
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	unsigned num_vars = NumVars( _max_var );
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top].Assign_2exp( num_vars );
	_nodes[NodeID::top].infor.visited = true;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		results[i].Assign_2exp( num_vars - 1 );
		_nodes[i].infor.visited = true;
	}
	while ( num_node_stack ) {
	    CDD top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( topn.sym <= _max_var ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.ch[1];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				results[top] = results[topn.ch[0]];
				results[top] += results[topn.ch[1]];
				results[top].Div_2exp( 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( loc == topn.ch_size ) {
				results[top].Assign_2exp( num_vars - topn.ch_size );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
			else if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[loc];
				_node_mark_stack[num_node_stack++] = true;
				for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				results[top] = results[topn.ch[loc]];
				for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
					results[top].Div_2exp( num_vars );
				}
				results[top].Div_2exp( loc );
                topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				for ( unsigned i = 1; i < topn.ch_size; i++ ) {
					results[topn.ch[i]].Assign_2exp( num_vars - 1 );
				}
				results[top] = results[topn.ch[0]];
				results[top].Div_2exp( topn.ch_size - 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = false;
	}
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
}

void CCDD_Manager::Probabilistic_Model( CDD root, vector<float> & prob_values )
{
	if ( root == NodeID::bot ) {
		cerr << "ERROR[CCDD_Manager]: invalid probabilistic model!" << endl;
		assert( root != NodeID::bot );
	}
	else if ( root == NodeID::top ) return;
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	unsigned num_vars = NumVars( _max_var );
	BigFloat * results = new BigFloat [root + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top].Assign_2exp( num_vars );
	_nodes[NodeID::top].infor.visited = true;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		results[i].Assign_2exp( num_vars - 1 );
		prob_values[i] = Node2Literal( i ).Sign();
		_nodes[i].infor.visited = true;
	}
	while ( num_node_stack ) {
	    CDD top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( topn.sym <= _max_var ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.ch[1];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				results[top] = results[topn.ch[0]];
				results[top] += results[topn.ch[1]];
				results[top].Div_2exp( 1 );
				prob_values[top] = Normalize( results[topn.ch[0]], results[topn.ch[1]] );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( loc == topn.ch_size ) {
				results[top].Assign_2exp( num_vars - topn.ch_size );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
			else if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[loc];
				_node_mark_stack[num_node_stack++] = true;
				for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				results[top] = results[topn.ch[loc]];
				for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
					results[top].Div_2exp( num_vars );
				}
				results[top].Div_2exp( loc );
                topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
               for ( unsigned i = 1; i < topn.ch_size; i++ ) {
                    results[topn.ch[i]].Assign_2exp( num_vars - 1 );
                    prob_values[topn.ch[i]] = 0.5;
                 }
				results[top] = results[topn.ch[0]];
				results[top].Div_2exp( topn.ch_size - 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = false;
	}
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	delete [] results;
}

void CCDD_Manager::Uniformly_Sample( Random_Generator & rand_gen, CDD root, vector<vector<bool>> & samples )
{
	vector<BigFloat> model_values( root + 1 );
	Mark_Models( root, model_values );
	for ( vector<bool> & current_sample: samples ) {
		current_sample.resize( _max_var + 1 );
		_path[0] = root;
		_path_mark[0] = true;
		unsigned path_len = 1;
		while ( path_len > 0 ) {
			NodeID top = _path[path_len - 1];
			CDD_Node & topn = _nodes[top];
			if ( topn.sym <= _max_var ) {
				if ( top < _num_fixed_nodes ) {
					Literal lit = Node2Literal( top );
					current_sample[lit.Var()] = lit.Sign();
					_var_seen[lit.Var()] = true;
					path_len--;
				}
				else if ( _path_mark[path_len - 1] ) {
					double prob = Normalize( model_values[topn.ch[0]], model_values[topn.ch[1]] );
					bool b = rand_gen.Generate_Bool( prob );
					current_sample[topn.sym] = b;
					_var_seen[topn.sym] = true;
					_path_mark[path_len - 1] = false;
					_path[path_len] = topn.ch[b];
					_path_mark[path_len++] = true;
				}
				else path_len--;
			}
			else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
				unsigned loc = Search_First_Non_Literal_Position( top );
				if ( _path_mark[path_len - 1] ) {
					_path_mark[path_len - 1] = false;
					for ( unsigned i = loc; i < topn.ch_size; i++ ) {
						_path[path_len] = topn.ch[i];
						_path_mark[path_len++] = true;
					}
				}
				else {
					for ( unsigned i = 0; i < loc; i++ ) {
						Literal imp = Node2Literal( topn.ch[i] );
						current_sample[imp.Var()] = imp.Sign();
						_var_seen[imp.Var()] = true;
					}
					path_len--;
				}
			}
			else if ( topn.sym == CDD_SYMBOL_KERNELIZE) {
				if ( _path_mark[path_len - 1] ) {
					_path_mark[path_len - 1] = false;
					_path[path_len] = topn.ch[0];
					_path_mark[path_len++] = true;
				}
				else {
				   for ( unsigned i = 1; i < topn.ch_size; i++ ) {
						CDD_Node & equ = _nodes[topn.ch[i]];
						if ( !_var_seen[equ.sym] ) {
							bool b = rand_gen.Generate_Bool( 0.5 );
							current_sample[equ.sym] = b;
							_var_seen[equ.sym] = true;
						}
						bool b = current_sample[equ.sym];
						Literal equ_lit = Node2Literal( equ.ch[b] );
						current_sample[equ_lit.Var()] = equ_lit.Sign();
						_var_seen[equ_lit.Var()] = true;
					 }
					path_len--;
				}
			}
			else path_len--;
		}
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			if ( !_var_seen[x] ) {
				current_sample[x] = rand_gen.Generate_Bool( 0.5 );
			}
			else _var_seen[x] = false;
		}
	}
}

void CCDD_Manager::Statistics( CDD root )
{
	if ( Is_Const( root ) ) {
		cout << "Number of nodes: " << 1 << endl;
		cout << "Number of edges: " << 0 << endl;
		cout << "Number of kernelized nodes: " << 0 << endl;
		cout << "Kernelization depth: " << 0 << endl;
		return;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	_nodes[NodeID::bot].infor.mark = 0;
	_nodes[NodeID::top].infor.mark = 0;
	unsigned num_nodes = 2;
	unsigned num_edges = 0;
	unsigned num_kernelized_nodes = 0;
	while ( num_node_stack ) {
	    CDD top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.infor.mark != UNSIGNED_UNDEF ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.ch[0];
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.ch[1];
			_node_mark_stack[num_node_stack++] = true;
			for ( unsigned i = 2; i < topn.ch_size; i++ ) {
				_node_stack[num_node_stack] = topn.ch[i];
				_node_mark_stack[num_node_stack++] = true;
			}
		}
		else {
			num_nodes++;
			num_kernelized_nodes += ( topn.sym == CDD_SYMBOL_KERNELIZE );
			num_edges += topn.ch_size;
			if ( topn.sym == CDD_SYMBOL_KERNELIZE ) {
				topn.infor.mark = _nodes[topn.ch[0]].infor.mark + 1;
			}
			else {
				if ( _nodes[topn.ch[0]].infor.mark > _nodes[topn.ch[1]].infor.mark )
					topn.infor.mark = _nodes[topn.ch[0]].infor.mark;
				else topn.infor.mark = _nodes[topn.ch[1]].infor.mark;
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
					if ( topn.infor.mark < _nodes[topn.ch[i]].infor.mark ) {
						topn.infor.mark = _nodes[topn.ch[i]].infor.mark;
					}
				}
			}
			_visited_nodes.push_back( top );
			num_node_stack--;
		}
	}
	cout << "Number of nodes: " << num_nodes << endl;
	cout << "Number of edges: " << num_edges << endl;
	cout << "Number of kernelized nodes: " << num_kernelized_nodes << endl;
	cout << "Kernelization depth: " << _nodes[root].infor.mark << endl;
	_nodes[NodeID::bot].infor.mark = UNSIGNED_UNDEF;
	_nodes[NodeID::top].infor.mark = UNSIGNED_UNDEF;
	for ( NodeID id: _visited_nodes ) {
		_nodes[id].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
}

CDD CCDD_Manager::Add_Node( Rough_CDD_Node & rnode )
{
	if ( rnode.sym == CDD_SYMBOL_FALSE ) return NodeID::bot;
	else if ( rnode.sym == CDD_SYMBOL_TRUE ) return NodeID::top;
	else if ( rnode.sym <= _max_var ) {
		Decision_Node bnode( rnode.sym, rnode.ch[0], rnode.ch[1] );
		return Add_Decision_Node( bnode );
	}
	else if ( rnode.sym == CDD_SYMBOL_DECOMPOSE ) return Add_Decomposition_Node( rnode );
	else if ( rnode.sym == CDD_SYMBOL_KERNELIZE ) return Add_Kernelization_Node( rnode );
	else return NodeID::undef;
}

CDD CCDD_Manager::Add_Decision_Node( Decision_Node & bnode )
{
	assert( Variable::start <= bnode.var && bnode.var <= _max_var );
	assert( bnode.low < _nodes.Size() && bnode.high < _nodes.Size() );
	NodeID tmp_link, low = bnode.low, high = bnode.high;
	if ( low == high ) tmp_link = low;
    else if ( Is_Const( bnode.low ) && Is_Const( bnode.high ) ) tmp_link = NodeID::literal( bnode.var, bnode.high == NodeID::top );
	else if ( low == NodeID::bot ) tmp_link = Extract_Leaf_Left_No_Check( bnode );
	else if ( high == NodeID::bot ) tmp_link = Extract_Leaf_Right_No_Check( bnode );
	else if ( BOTH_X( _nodes[low].sym, _nodes[high].sym, CDD_SYMBOL_DECOMPOSE ) && \
			 !Intersection_Empty( _nodes[low].ch, _nodes[low].ch_size, _nodes[high].ch, _nodes[high].ch_size ) ) {
		tmp_link = Extract_Share_No_Check( bnode );
	}
	else if ( _nodes[high].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[high].ch, _nodes[high].ch_size, low ) ) {
		tmp_link = Extract_Part_Left_No_Check( bnode );
	}
	else if ( _nodes[low].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[low].ch, _nodes[low].ch_size, high ) ) {
		tmp_link = Extract_Part_Right_No_Check( bnode );
	}
	else tmp_link = Extract_Lit_Equivalences( bnode );
	return tmp_link;
}

NodeID CCDD_Manager::Extract_Leaf_Left_No_Check( Decision_Node & bnode )
{
	assert( Variable::start <= bnode.var && bnode.var <= _max_var );
	assert( bnode.low == NodeID::bot && Is_Internal( bnode.high ) );
	CDD_Node node;
	NodeID lit = NodeID::literal( bnode.var, true );
	node.sym = CDD_SYMBOL_DECOMPOSE;
	if ( _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE ) {
		node.ch_size = _nodes[bnode.high].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, lit, node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < bnode.high ) {
			node.ch[0] = lit;
			node.ch[1] = bnode.high;
		}
		else {
			node.ch[0] = bnode.high;
			node.ch[1] = lit;
		}
	}
	return Push_Node( node );
}

NodeID CCDD_Manager::Extract_Leaf_Right_No_Check( Decision_Node & bnode )
{
	assert( Variable::start <= bnode.var && bnode.var <= _max_var );
	assert( Is_Internal( bnode.low ) && bnode.high == NodeID::bot );
	CDD_Node node;
	NodeID lit = NodeID::literal( bnode.var, false );
	node.sym = CDD_SYMBOL_DECOMPOSE;
	if ( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE ) {
		node.ch_size = _nodes[bnode.low].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, lit, node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < bnode.low ) {
			node.ch[0] = lit;
			node.ch[1] = bnode.low;
		}
		else {
			node.ch[0] = bnode.low;
			node.ch[1] = lit;
		}
	}
	return Push_Node( node );
}

NodeID CCDD_Manager::Extract_Share_No_Check( Decision_Node & bnode )  // use _lit_seen, _many_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
//	unsigned old_size = _nodes.Size();  // ToRemove
	assert( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE && _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE );
	unsigned num_shared = Intersection( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, \
		_nodes[bnode.high].ch, _nodes[bnode.high].ch_size, _many_nodes );
	assert( num_shared != 0 );
	unsigned i, n;
	if ( num_shared == _nodes[bnode.low].ch_size ) {
		bnode.low = NodeID::top;
		bnode.high = Remove_Children( bnode.high, _many_nodes, num_shared );
		n = Push_Node( bnode );
	}
	else if ( num_shared == _nodes[bnode.high].ch_size ) {
		bnode.low = Remove_Children( bnode.low, _many_nodes, num_shared );
		bnode.high = NodeID::top;
		n = Push_Node( bnode );
	}
	else {
		bnode.low = Remove_Children( bnode.low, _many_nodes, num_shared );
		bnode.high = Remove_Children( bnode.high, _many_nodes, num_shared );
		n = Extract_Lit_Equivalences( bnode );
	}
	if ( n < _many_nodes[0] ) {
		for ( i = num_shared - 1; i != UNSIGNED_UNDEF; i-- ) _many_nodes[i+1] = _many_nodes[i];
		_many_nodes[0] = n;
	}
	else {
		for ( i = num_shared - 1; _many_nodes[i] > n; i-- ) _many_nodes[i+1] = _many_nodes[i];
		_many_nodes[i+1] = n;
	}
	return Push_Decomposition_Node( _many_nodes, num_shared + 1 );
}

NodeID CCDD_Manager::Remove_Children( NodeID parent, NodeID * children, unsigned num_ch )
{
	assert( _nodes[parent].sym == CDD_SYMBOL_DECOMPOSE );
	if ( _nodes[parent].ch_size == num_ch ) return NodeID::top;
	else if ( _nodes[parent].ch_size == num_ch + 1 ) {
		unsigned i;
		if ( _nodes[parent].ch[_nodes[parent].ch_size - 1] != children[num_ch - 1] ) return _nodes[parent].ch[_nodes[parent].ch_size - 1];
		for ( i = 0; _nodes[parent].ch[i] == children[i]; i++ );
		return _nodes[parent].ch[i];
	}
	else {
		CDD_Node node;
		node.sym = _nodes[parent].sym;
		node.ch_size = _nodes[parent].ch_size - num_ch;
		node.ch = new NodeID [node.ch_size];
		Difference_Subset( _nodes[parent].ch, _nodes[parent].ch_size, children, num_ch, node.ch );
		return Push_Node( node );
	}
}

NodeID CCDD_Manager::Extract_Part_Left_No_Check( Decision_Node & bnode )
{
	assert( Is_Internal( bnode.low ) && _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE );
	CDD_Node node;
	node.sym = bnode.var;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	node.ch[0] = NodeID::top;
	if ( _nodes[bnode.high].ch_size == 2 ) node.ch[1] = _nodes[bnode.high].ch[0] + _nodes[bnode.high].ch[1] - bnode.low;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[1] = Remove_Child_No_Check_GE_3( bnode.high, bnode.low );
	NodeID n = Push_Node( node );
	node.sym = CDD_SYMBOL_DECOMPOSE;
	node.ch = new NodeID [2];
	if ( n < bnode.low ) {
		node.ch[0] = n;
		node.ch[1] = bnode.low;
	}
	else {
		node.ch[0] = bnode.low;
		node.ch[1] = n;
	}
	return Push_Node( node );
}

NodeID CCDD_Manager::Remove_Child_No_Check_GE_3( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == CDD_SYMBOL_DECOMPOSE );
	assert( _nodes[parent].ch_size >= 3 );
	CDD_Node node;
	node.sym = _nodes[parent].sym;
	node.ch_size = _nodes[parent].ch_size - 1;
	node.ch = new NodeID [node.ch_size];
	Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
	return Push_Node( node );
}

NodeID CCDD_Manager::Extract_Part_Right_No_Check( Decision_Node & bnode )
{
	assert( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE && Is_Internal( bnode.high ) );
	CDD_Node node;
	node.sym = bnode.var;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	if ( _nodes[bnode.low].ch_size == 2 ) node.ch[0] = _nodes[bnode.low].ch[0] + _nodes[bnode.low].ch[1] - bnode.high;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[0] = Remove_Child_No_Check_GE_3( bnode.low, bnode.high );
	node.ch[1] = NodeID::top;
	NodeID n = Push_Node( node );
	node.sym = CDD_SYMBOL_DECOMPOSE;
	node.ch = new NodeID [2];
	if ( n < bnode.high ) {
		node.ch[0] = n;
		node.ch[1] = bnode.high;
	}
	else {
		node.ch[0] = bnode.high;
		node.ch[1] = n;
	}
	return Push_Node( node );
}

NodeID CCDD_Manager::Extract_Lit_Equivalences( Decision_Node & bnode )  // use _lit_seen, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode, _aux_rnode
{
	if ( true ) return Push_Node( bnode );
	NodeID result;
	if ( Is_Literal( bnode.low ) ) {
		if ( _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.low );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			if ( Search_Exi_Nonempty( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, lit_neg_node ) ) {
				return Extract_Lit_Equivalence_Left_Lit( bnode );
			}
		}
		return Push_Decision_Node( bnode.var, bnode.low, bnode.high );
	}
	if ( Is_Literal( bnode.high ) ) {
		if ( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.high );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			if ( Search_Exi_Nonempty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, lit_neg_node ) ) {
				return Extract_Lit_Equivalence_Right_Lit( bnode );
			}
		}
		return Push_Decision_Node( bnode.var, bnode.low, bnode.high );
	}
	Shared_Lit_Equivalency( bnode );
	unsigned num_equ = Transform_Lit_Equivalences( _lit_equivalency, _many_equ_nodes );
	if ( num_equ > 0 ) {
		bnode.low = Remove_Lit_Equivalences( bnode.low, _lit_equivalency );
		bnode.high = Remove_Lit_Equivalences( bnode.high, _lit_equivalency );
		_aux_kerne_rnode.ch_size = 0;  // _aux_kerne_rnode is also used in Remove_Lit_Equivalences
		NodeID core = Push_Core_After_Extracting( bnode );  // check the case where both children are true
		_aux_kerne_rnode.Add_Child( core );  // check the case where both children are true
		for ( unsigned i = 0; i < num_equ; i++ ) {
			_aux_kerne_rnode.Add_Child( _many_equ_nodes[i] );
		}
		result = Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
	}
	else result = Push_Node( bnode );
	_lit_equivalency.Reset();
	return result;
}

NodeID CCDD_Manager::Extract_Lit_Equivalence_Left_Lit( Decision_Node & bnode )  // use _lit_seen, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
	Literal lit = Node2Literal( bnode.low );
	NodeID lit_neg_node = NodeID::literal( ~lit );
	NodeID high = Remove_Child_No_Check( bnode.high, lit_neg_node );
	if ( Var_LT( bnode.var, lit.Var() ) ) {
		_aux_kerne_rnode.ch[0] = Push_Decision_Node( bnode.var, NodeID::top, high );  // check the case where both children are true
		_aux_kerne_rnode.ch[1] = Push_Decision_Node( bnode.var, bnode.low, lit_neg_node );
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
	}
	else {
		if ( lit.Sign() ) _aux_kerne_rnode.ch[0] = Push_Decision_Node( lit.Var(), high, NodeID::top );  // check the case where both children are true
		else _aux_kerne_rnode.ch[0] = Push_Decision_Node( lit.Var(), NodeID::top, high );  // check the case where both children are true
		NodeID equ_low = NodeID::literal( bnode.var, lit.Sign() );
		NodeID equ_high = NodeID::literal( bnode.var, lit.NSign() );  // bnode.var <-> ~lit
		_aux_kerne_rnode.ch[1] = Push_Decision_Node( lit.Var(), equ_low, equ_high );
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
	}
}

NodeID CCDD_Manager::Extract_Lit_Equivalence_Right_Lit( Decision_Node & bnode )  // use _lit_seen, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
	Literal lit = Node2Literal( bnode.high );
	NodeID lit_neg_node = NodeID::literal( ~lit );
	NodeID low = Remove_Child_No_Check( bnode.low, lit_neg_node );
	if ( Var_LT( bnode.var, lit.Var() ) ) {
		_aux_kerne_rnode.ch[0] = Push_Decision_Node( bnode.var, low, NodeID::top );  // check the case where both children are true
		_aux_kerne_rnode.ch[1] = Push_Decision_Node( bnode.var, lit_neg_node, bnode.high );
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
	}
	else {
		if ( lit.Sign() ) _aux_kerne_rnode.ch[0] = Push_Decision_Node( lit.Var(), low, NodeID::top );  // check the case where both children are true
		else _aux_kerne_rnode.ch[0] = Push_Decision_Node( lit.Var(), NodeID::top, low );  // check the case where both children are true
		NodeID equ_low = NodeID::literal( bnode.var, lit.NSign() );
		NodeID equ_high = NodeID::literal( bnode.var, lit.Sign() );  // bnode.var <-> lit
		_aux_kerne_rnode.ch[1] = Push_Decision_Node( lit.Var(), equ_low, equ_high );
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
	}
}

NodeID CCDD_Manager::Remove_Child_No_Check( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == CDD_SYMBOL_DECOMPOSE );
	if ( _nodes[parent].ch_size == 2 ) return _nodes[parent].ch[0] + _nodes[parent].ch[1] - child;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else {
		CDD_Node node;
		node.sym = _nodes[parent].sym;
		node.ch_size = _nodes[parent].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
		return Push_Node( node );
	}
}

unsigned CCDD_Manager::Lit_Equivalences( NodeID n, NodeID * equ_nodes )
{
	unsigned i, j, num = 0;
	CDD_Node & node = _nodes[n];
	if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
		for ( i = Search_First_Non_Literal_Position( node ); i < node.ch_size; i++ ) {
			CDD_Node & child = _nodes[node.ch[i]];
			if ( child.sym == CDD_SYMBOL_KERNELIZE ) {
				for ( j = 1; j < child.ch_size; j++ ) {
					equ_nodes[num++] = child.ch[j];
				}
			}
			else if ( Is_Equivalence_Node( child ) ) equ_nodes[num++] = node.ch[i];
		}
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		for ( j = 1; j < node.ch_size; j++ ) {
			equ_nodes[num++] = node.ch[j];
		}
	}
	else if ( Is_Equivalence_Node( node ) ) equ_nodes[num++] = n;
	return num;
}

void CCDD_Manager::Record_Lit_Equivalency( unsigned n, Lit_Equivalency & lit_equivalency )
{
	unsigned i, j;
	CDD_Node & node = _nodes[n];
	if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
		for ( i = Search_First_Non_Literal_Position( node ); i < node.ch_size; i++ ) {
			CDD_Node & child = _nodes[node.ch[i]];
			if ( child.sym == CDD_SYMBOL_KERNELIZE ) {
				for ( j = 1; j < child.ch_size; j++ ) {
					CDD_Node & grandch = _nodes[child.ch[j]];
					Literal lit( grandch.Var(), true );
					Literal lit2 = Node2Literal( grandch.ch[1] );
					lit_equivalency.Add_Equivalence( lit, lit2 );
				}
			}
			else if ( Is_Equivalence_Node( child ) ) {
				Literal lit = Literal( child.Var(), true );
				Literal lit2 = Node2Literal( child.ch[1] );
				lit_equivalency.Add_Equivalence( lit, lit2 );
			}
		}
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		for ( i = 1; i < node.ch_size; i++ ) {
			CDD_Node & child = _nodes[node.ch[i]];
			Literal lit( child.Var(), true );
			Literal lit2 = Node2Literal( child.ch[1] );
			lit_equivalency.Add_Equivalence( lit, lit2 );
		}
	}
	else if ( Is_Equivalence_Node( node ) ) {
		Literal lit( node.Var(), true );
		Literal lit2 = Node2Literal( node.ch[1] );
		lit_equivalency.Add_Equivalence( lit, lit2 );
	}
}

void CCDD_Manager::Shared_Lit_Equivalency( Decision_Node & bnode )  // use _var_seen, _lit_seen
{
	Simple_CDD_Node low( _nodes[bnode.low] );  // NOTE: _nodes might be reallocated
	Simple_CDD_Node high( _nodes[bnode.high] );
	unsigned num_lits0 = 0, num_lits1 = 0;
	if ( low.sym == CDD_SYMBOL_DECOMPOSE ) num_lits0 = Search_First_Non_Literal_Position( bnode.low );
	if ( high.sym == CDD_SYMBOL_DECOMPOSE ) num_lits1 = Search_First_Non_Literal_Position( bnode.high );
	Record_Lit_Equivalency( bnode.low, _lit_equivalency_low );
	Record_Lit_Equivalency( bnode.high, _lit_equivalency_high );
	for ( unsigned i = 0; i < num_lits0; i++ ) {
		Literal lit = Node2Literal( low.ch[i] );
		if ( !_lit_equivalency_high.Lit_Renamable( lit ) ) continue;
		Literal lit_equ = _lit_equivalency_high.Rename_Lit( lit );
		for ( unsigned j = 0; j < i; j++ ) {
			Literal lit2 = Node2Literal( low.ch[j] );
			if ( lit_equ == _lit_equivalency_high.Rename_Lit( lit2 ) ) {  // Reduce the callings of Lit_Equivalency::Find()
				_lit_equivalency_low.Add_Equivalence( lit, lit2 );
			}
		}
		for ( unsigned j = i + 1; j < num_lits0; j++ ) {
			Literal lit2 = Node2Literal( low.ch[j] );
			if ( lit_equ == _lit_equivalency_high.Rename_Lit( lit2 ) ) {
				_lit_equivalency_low.Add_Equivalence( lit, lit2 );
			}
		}
	}
	for ( unsigned i = 0; i < num_lits1; i++ ) {
		Literal lit = Node2Literal( high.ch[i] );
		if ( !_lit_equivalency_low.Lit_Renamable( lit ) ) continue;
		Literal lit_equ = _lit_equivalency_low.Rename_Lit( lit );
		for ( unsigned j = 0; j < i; j++ ) {
			Literal lit2 = Node2Literal( high.ch[j] );
			if ( lit_equ == _lit_equivalency_low.Rename_Lit( lit2 ) ) {
				_lit_equivalency_high.Add_Equivalence( lit, lit2 );
			}
		}
		for ( unsigned j = i + 1; j < num_lits1; j++ ) {
			Literal lit2 = Node2Literal( high.ch[j] );
			if ( lit_equ == _lit_equivalency_low.Rename_Lit( lit2 ) ) {
				_lit_equivalency_high.Add_Equivalence( lit, lit2 );
			}
		}
	}
	_lit_equivalency.Intersection( _lit_equivalency_low, _lit_equivalency_high );
	_lit_equivalency_low.Reset();
	_lit_equivalency_high.Reset();
	for ( unsigned i = 0; i < num_lits1; i++ ) {
		Literal lit = Node2Literal( high.ch[i] );
		_var_seen[lit.Var()] = true;  // NOTE: lit does not appear in low, otherwise low and high share child
	}
	Literal dec_lit = Literal( bnode.var, false ), min_lit = dec_lit;
	for ( unsigned i = 0; i < num_lits0; i++ ) {
		Literal lit = Node2Literal( low.ch[i] );
		if ( _var_seen[lit.Var()] && Lit_LT( lit, min_lit ) ) {
			min_lit = lit;
		}
	}
	bool exchange = false;
	for ( unsigned i = 0; i < num_lits0; i++ ) {
		Literal lit = Node2Literal( low.ch[i] );
		if ( _var_seen[lit.Var()] ) {
			_lit_equivalency.Add_Equivalence( dec_lit, lit );
			if ( lit == min_lit ) {
				unsigned pos = high.Search_Child( NodeID(~lit) );
				assert( pos != UNSIGNED_UNDEF );
				if ( lit.Sign() ) exchange = true;
				bnode.low = Update_Child( bnode.low, i, NodeID(dec_lit) );
				bnode.high = Update_Child( bnode.high, pos, NodeID(~dec_lit) );
				low.ch = _nodes[bnode.low].ch;  // NOTE: _nodes might be reallocated
				high.ch = _nodes[bnode.high].ch;  // NOTE: _nodes might be reallocated
				bnode.var = lit.Var();
				_var_seen[lit.Var()] = false;  // shift lit.Var() to sym
			}
		}
	}
	for ( unsigned i = 0; i < num_lits1; i++ ) {
		Literal lit = Node2Literal( high.ch[i] );
		_var_seen[lit.Var()] = false;
	}
	if ( exchange ) {
		NodeID tmp = bnode.low;
		bnode.low = bnode.high;
		bnode.high = tmp;
	}
}

unsigned CCDD_Manager::Intersection_Equ_Nodes( unsigned * equ_nodes0, unsigned size0, unsigned * equ_nodes1, unsigned size1 )
{
	unsigned i, ii, j, jj;
	for ( i = ii = 0; i < size0; i++ ) {
		equ_nodes1[size1] = equ_nodes0[i];
		for ( j = 0; equ_nodes1[j] != equ_nodes0[i]; j++ ) {}
		equ_nodes0[ii] = equ_nodes0[i];  // keep the shared nodes in equ_nodes0 under the original order
		ii += ( j < size1 );
		_equ_node_seen[j] = ( j < size1 );
	}
	for ( j = jj = 0; j < size1; j++ ) {
		equ_nodes1[jj] = equ_nodes1[j];  // keep the shared nodes in equ_nodes1 under the original order
		jj += _equ_node_seen[j];
		_equ_node_seen[j] = false;
	}
	assert( ii == jj );
	return ii;
}

NodeID CCDD_Manager::Remove_Lit_Equivalences( NodeID n, Lit_Equivalency & lit_equivalency )  // uses _aux_rnode, _aux_kerne_rnode
{
	Simple_CDD_Node node( _nodes[n] );
	if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
		unsigned i, num_lits = Search_First_Non_Literal_Position( n );
		_aux_rnode.sym = CDD_SYMBOL_DECOMPOSE;
		_aux_rnode.ch_size = 0;
		for ( i = 0; i < num_lits; i++ ) {
			Literal lit = Node2Literal( node.ch[i] );
			if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_rnode.Add_Child( node.ch[i] );
		}
		unsigned num_left_lits = _aux_rnode.ch_size;
		for ( ; i < node.ch_size; i++ ) {
			Simple_CDD_Node child( _nodes[node.ch[i]] );
			if ( child.sym == CDD_SYMBOL_KERNELIZE ) {
				_aux_kerne_rnode.ch_size = 0;
				_aux_kerne_rnode.Add_Child( child.ch[0] );
				for ( unsigned j = 1; j < child.ch_size; j++ ) {
					Simple_CDD_Node grandch = _nodes[child.ch[j]];
					Literal lit = Node2Literal( grandch.ch[1] );
					if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_kerne_rnode.Add_Child( child.ch[j] );
				}
				unsigned c = Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
				if ( c != NodeID::top ) _aux_rnode.Add_Child( c );
			}
			else if ( Is_Equivalence_Node( _nodes[node.ch[i]] ) ) {
                Literal lit0 = Literal(child.Var(), true);
				Literal lit = Node2Literal( child.ch[1] );
				if ( !lit_equivalency.Contain_Lit_Equivalence( lit0, lit ) ) _aux_rnode.Add_Child( node.ch[i] );
			}
			else _aux_rnode.Add_Child( node.ch[i] );
		}
		return Push_Decomposition_Node_After_Extracting( _aux_rnode );  // will use _node_sets, _node_set_sizes
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		_aux_kerne_rnode.ch_size = 0;
		_aux_kerne_rnode.Add_Child( node.ch[0] );
		for ( unsigned i = 1; i < node.ch_size; i++ ) {
			Simple_CDD_Node child( _nodes[node.ch[i]] );
			Literal lit = Node2Literal( child.ch[1] );
			if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_kerne_rnode.Add_Child( node.ch[i] );
		}
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
	}
	else if ( Is_Equivalence_Node( _nodes[n] ) ) {
        Literal lit0 = Literal(node.Var(), true);
		Literal lit = Node2Literal( node.ch[1] );
		if ( !lit_equivalency.Contain_Lit_Equivalence( lit0, lit ) ) return n;
		else return NodeID::top;
	}
	else return n;
}

CDD CCDD_Manager::Push_Decomposition_Node_After_Extracting( Rough_CDD_Node & rnode )  // use node_sets, node_set_sizes
{
	assert( rnode.sym == CDD_SYMBOL_DECOMPOSE );
	unsigned i, tmp_size = 0;
	for ( i = 0; i < rnode.ch_size; i++ ) {
		if ( _nodes[rnode.ch[i]].sym != CDD_SYMBOL_TRUE ) {
			assert( rnode.ch[i] < _nodes.Size() );
			rnode.ch[tmp_size++] = rnode.ch[i];
		}
	}
	rnode.ch_size = tmp_size;
	if ( rnode.ch_size == 0 ) return NodeID::top;
	else if ( rnode.ch_size == 1 ) return rnode.ch[0];
	_qsorter.Sort( rnode.ch, rnode.ch_size );  // ToCheck
	unsigned tmp = _nodes[rnode.Last_Child()].sym;
	_nodes[rnode.Last_Child()].sym = CDD_SYMBOL_DECOMPOSE;
	for ( i = 0; _nodes[rnode.ch[i]].sym != CDD_SYMBOL_DECOMPOSE; i++ ) {}
	_nodes[rnode.Last_Child()].sym = tmp;
	if ( _nodes[rnode.ch[i]].sym != CDD_SYMBOL_DECOMPOSE ) return Push_Node( rnode );
	CDD_Node node;
	node.sym = CDD_SYMBOL_DECOMPOSE;
	_node_sets[0] = new NodeID [rnode.ch_size - 1];
	_node_set_sizes[0] = i;
	for ( unsigned j = 0; j < i; j++ ) _node_sets[0][j] = rnode.ch[j];
	node.ch_size = _nodes[rnode.ch[i]].ch_size;
	_node_sets[1] = _nodes[rnode.ch[i]].ch;
	_node_set_sizes[1] = _nodes[rnode.ch[i]].ch_size;
	unsigned cluster_size = 2;
	for ( i++; i < rnode.ch_size; i++ ) {
		if ( _nodes[rnode.ch[i]].sym == CDD_SYMBOL_DECOMPOSE ) {
			node.ch_size += _nodes[rnode.ch[i]].ch_size;
			_node_sets[cluster_size] = _nodes[rnode.ch[i]].ch;
			_node_set_sizes[cluster_size++] = _nodes[rnode.ch[i]].ch_size;
		}
		else _node_sets[0][_node_set_sizes[0]++] = rnode.ch[i];
	}
	node.ch_size += _node_set_sizes[0];
	node.ch = new NodeID [node.ch_size];
	if ( _node_set_sizes[0] == 0 ) Merge_Many_Arrays( _node_sets + 1, _node_set_sizes + 1, cluster_size - 1, node.ch );
	else Merge_Many_Arrays( _node_sets, _node_set_sizes, cluster_size, node.ch );
	delete [] _node_sets[0];
	return Push_Node( node );
}

NodeID CCDD_Manager::Push_Core_After_Extracting( Decision_Node & bnode )  // uses _aux_rnode
{
	NodeID low = bnode.low, high = bnode.high;
	if ( low == high ) return low;
	else if ( BOTH_X( _nodes[low].sym, _nodes[high].sym, CDD_SYMBOL_DECOMPOSE ) && \
			 !Intersection_Empty( _nodes[low].ch, _nodes[low].ch_size, _nodes[high].ch, _nodes[high].ch_size ) ) {
		_aux_rnode.ch_size  = Intersection( _nodes[low].ch, _nodes[low].ch_size, \
			_nodes[high].ch, _nodes[high].ch_size, _aux_rnode.ch );
		assert( _aux_rnode.ch_size != 0 );  // NOTE: cannot use _many_nodes due to possible conflict
		if ( _aux_rnode.ch_size == _nodes[low].ch_size ) {
			bnode.low = NodeID::top;
			bnode.high = Remove_Children( high, _aux_rnode.ch, _aux_rnode.ch_size );
		}
		else if ( _aux_rnode.ch_size == _nodes[high].ch_size ) {
			bnode.low = Remove_Children( low, _aux_rnode.ch, _aux_rnode.ch_size );
			bnode.high = NodeID::top;
		}
		else {
			bnode.low = Remove_Children( low, _aux_rnode.ch, _aux_rnode.ch_size );
			bnode.high = Remove_Children( high, _aux_rnode.ch, _aux_rnode.ch_size );
		}
		_aux_rnode.Add_Child( Push_Node( bnode ) );
		Insert_Sort_Last( _aux_rnode.ch, _aux_rnode.ch_size );
		return Push_Decomposition_Node( _aux_rnode.ch, _aux_rnode.ch_size );
	}
	else if ( _nodes[high].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[high].ch, _nodes[high].ch_size, low ) ) {
		return Extract_Part_Left_No_Check( bnode );
	}
	else if ( _nodes[low].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[low].ch, _nodes[low].ch_size, high ) ) {
		return Extract_Part_Right_No_Check( bnode );
	}
	else return Push_Node( bnode );
}

CDD CCDD_Manager::Add_Decomposition_Node( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, node_set_sizes
{
	assert( rnode.sym == CDD_SYMBOL_DECOMPOSE );
	if ( rnode.ch_size == 0 ) return NodeID::top;
	if ( rnode.ch_size == 1 ) return rnode.ch[0];
	unsigned i, tmp_link;
	unsigned tmp = _nodes[rnode.Last_Child()].sym;  // NOTE: Search NodeID::bot
	_nodes[rnode.Last_Child()].sym = CDD_SYMBOL_FALSE;
	for ( i = 0; _nodes[rnode.ch[i]].sym != CDD_SYMBOL_FALSE; i++ );
	_nodes[rnode.Last_Child()].sym = tmp;
	if ( _nodes[rnode.ch[i]].sym == CDD_SYMBOL_FALSE )
		tmp_link = CDD_SYMBOL_FALSE;
	else {
		unsigned tmp_size = 0;
		for ( i = 0; i < rnode.ch_size; i++ ) {
			if ( _nodes[rnode.ch[i]].sym != CDD_SYMBOL_TRUE ) {
				assert( rnode.ch[i] < _nodes.Size() );
				rnode.ch[tmp_size++] = rnode.ch[i];
			}
		}
		rnode.ch_size = tmp_size;
		if ( rnode.ch_size == 0 ) tmp_link = CDD_SYMBOL_TRUE;
		else if ( rnode.ch_size == 1 ) tmp_link = rnode.ch[0];
		else {
			_qsorter.Sort( rnode.ch, rnode.ch_size );  // ToCheck
			tmp_link = Finest( rnode );
		}
	}
	return tmp_link;
}

unsigned CCDD_Manager::Finest( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, _node_set_sizes
{
	assert( rnode.sym == CDD_SYMBOL_DECOMPOSE );
	unsigned i, j;
	unsigned tmp = _nodes[rnode.Last_Child()].sym;
	_nodes[rnode.Last_Child()].sym = CDD_SYMBOL_DECOMPOSE;
	for ( i = 0; _nodes[rnode.ch[i]].sym != CDD_SYMBOL_DECOMPOSE; i++ );
	_nodes[rnode.Last_Child()].sym = tmp;
	if ( _nodes[rnode.ch[i]].sym != CDD_SYMBOL_DECOMPOSE ) return Push_Node( rnode );
	else {
		_node_sets[0] = _many_nodes;
		_node_set_sizes[0] = i;
		for ( j = 0; j < i; j++ ) _many_nodes[j] = rnode.ch[j];
		_node_sets[1] = _nodes[rnode.ch[i]].ch;
		_node_set_sizes[1] = _nodes[rnode.ch[i]].ch_size;
		unsigned cluster_size = 2;
		CDD_Node node;
		node.sym = CDD_SYMBOL_DECOMPOSE;
		node.ch_size = _nodes[rnode.ch[i]].ch_size;
		for ( i++; i < rnode.ch_size; i++ ) {
			if ( _nodes[rnode.ch[i]].sym == CDD_SYMBOL_DECOMPOSE ) {
				node.ch_size += _nodes[rnode.ch[i]].ch_size;
				_node_sets[cluster_size] = _nodes[rnode.ch[i]].ch;
				_node_set_sizes[cluster_size++] = _nodes[rnode.ch[i]].ch_size;
			}
			else _many_nodes[_node_set_sizes[0]++] = rnode.ch[i];
		}
		node.ch_size += _node_set_sizes[0];
		node.ch = new NodeID [node.ch_size];
		if ( _node_set_sizes[0] == 0 ) Merge_Many_Arrays( _node_sets + 1, _node_set_sizes + 1, cluster_size - 1, node.ch );
		else Merge_Many_Arrays( _node_sets, _node_set_sizes, cluster_size, node.ch );
		return Push_Node( node );
	}
}

CDD CCDD_Manager::Add_Kernelization_Node( Rough_CDD_Node & rnode )  // use _many_nodes, _many_equ_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
	assert( rnode.sym == CDD_SYMBOL_KERNELIZE );
	if ( rnode.ch_size == 0 ) return NodeID::top;
	if ( rnode.ch_size == 1 ) return rnode.ch[0];
	CDD cdd;
	unsigned main_ch_sym = _nodes[rnode.ch[0]].sym;
	if ( main_ch_sym == CDD_SYMBOL_FALSE ) return NodeID::bot;
	if ( main_ch_sym == CDD_SYMBOL_KERNELIZE ) {
		CDD_Node & node = _nodes[rnode.ch[0]];
		for ( unsigned i = 1; i < node.ch_size; i++ ) {
			NodeID * grandch = _nodes[node.ch[i]].ch;
			Literal lit0( _nodes[node.ch[i]].Var(), true );
			Literal lit1 = Node2Literal( grandch[1] );
			_lit_equivalency.Add_Equivalence_Flat( lit0, lit1 );
		}
		rnode.ch[0] = node.ch[0];
	}
	for ( unsigned i = 1; i < rnode.ch_size; i++ ) {
		assert( _nodes[rnode.ch[i]].ch_size == 2 );
		Verify_Equivalence_Node( _nodes[rnode.ch[i]] );
		NodeID * grandch = _nodes[rnode.ch[i]].ch;
		Literal lit0( _nodes[rnode.ch[i]].Var(), true );
		Literal lit1 = Node2Literal( grandch[1] );
		_lit_equivalency.Add_Equivalence( lit0, lit1 );
	}
	rnode.ch_size = Transform_Lit_Equivalences( _lit_equivalency, rnode.ch + 1 );
	rnode.ch_size++;
	_lit_equivalency.Reset();
	return Push_Kernelization_Node( rnode.ch, rnode.ch_size );
}

unsigned CCDD_Manager::Transform_Lit_Equivalences( Lit_Equivalency & lit_equivalency, NodeID * equ_nodes )
{
	unsigned num_equ = lit_equivalency.Output_Equivalences( _many_lits );
	for ( unsigned i = 0; i < num_equ; i++ ) {
		Literal lit = _many_lits[i + i], lit2 = _many_lits[i + i + 1];
		equ_nodes[i] = Push_Equivalence_Node( lit, lit2 );
	}
	_qsorter.Sort( equ_nodes, num_equ );
	return num_equ;
}

CDD CCDD_Manager::Add_Equivalence_Node( int elit, int elit2 )
{
	Literal lit = InternLit( elit ), lit2 = InternLit( elit2 );
	assert( lit.Var() != lit2.Var() && lit.Var() <= _max_var && lit2.Var() <= _max_var );
	Literal tmp;
	if ( Lit_LT( lit2, lit ) ) {
		tmp = lit;
		lit = lit2;
		lit2 = tmp;
	}
	if ( !lit.Sign() ) {
		lit = ~lit;
		lit2 = ~lit2;
	}
	return Push_Equivalence_Node( lit, lit2 );
}

unsigned CCDD_Manager::Add_Equivalence_Nodes( const vector<Literal> & lit_equivalences, NodeID * nodes )
{
	for ( unsigned i = 0; i < lit_equivalences.size(); i += 2 ) {
		Literal lit0 = lit_equivalences[i];
		Literal lit1 = lit_equivalences[i + 1];
		_lit_equivalency.Add_Equivalence( lit0, lit1 );
	}
	unsigned num = Transform_Lit_Equivalences( _lit_equivalency, nodes );
	_lit_equivalency.Reset();
	return num;
}

unsigned CCDD_Manager::Add_Equivalence_Nodes( Literal * lit_pairs, unsigned num_pairs, NodeID * nodes )
{
	for ( unsigned i = 0; i < num_pairs; i++ ) {
		Literal lit0 = lit_pairs[i + i];
		Literal lit1 = lit_pairs[i + i + 1];
		_lit_equivalency.Add_Equivalence( lit0, lit1 );
	}
	NodeID n = Transform_Lit_Equivalences( _lit_equivalency, nodes );
	_lit_equivalency.Reset();
	return n;
}

unsigned CCDD_Manager::Finest_Last( Rough_CDD_Node & rnode )
{
	assert( rnode.sym == CDD_SYMBOL_DECOMPOSE );
	if ( _nodes[rnode.Last_Child()].sym != CDD_SYMBOL_DECOMPOSE ) {
		Insert_Sort_Last( rnode.ch, rnode.ch_size );
		return Push_Node( rnode );
	}
	else {
		CDD_Node & last = _nodes[rnode.Last_Child()];
		rnode.ch_size--;
		for ( unsigned i = 0; i < last.ch_size; i++ ) {
			rnode.Add_Child( last.ch[i] );
			Insert_Sort_Last( rnode.ch, rnode.ch_size );
		}
		return Push_Node( rnode );
	}
}

void CCDD_Manager::Verify_CCDD( CDD root )
{
	if ( Is_Fixed( root ) ) return;
	Hash_Cluster<Variable> var_cluster( NumVars( _max_var ) );
	vector<SetID> sets( root + 1 );
	Compute_Var_Sets( root, var_cluster, sets );
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		unsigned top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
//		cerr << "top = " << top << ": ";  // ToRemove
//		topn.Display( cerr );  // ToRemove
		Verify_Node( top, var_cluster, sets );
		num_node_stack--;
		if ( topn.sym <= _max_var ) {
			if ( !_nodes[topn.ch[1]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[1];
				_nodes[topn.ch[1]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[1] );
			}
			if ( !_nodes[topn.ch[0]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[0];
				_nodes[topn.ch[0]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[0] );
			}
		}
		else {
			for ( unsigned i = topn.ch_size - 1; i != UNSIGNED_UNDEF; i-- ) {
				if ( !_nodes[topn.ch[i]].infor.visited ) {
					_node_stack[num_node_stack++] = topn.ch[i];
					_nodes[topn.ch[i]].infor.visited = true;
					_visited_nodes.push_back( topn.ch[i] );
				}
			}
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
}

void CCDD_Manager::Compute_Var_Sets( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	sets[NodeID::bot] = SETID_EMPTY;
	_nodes[NodeID::bot].infor.visited = true;
	sets[NodeID::top] = SETID_EMPTY;
	_nodes[NodeID::top].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		NodeID n = NodeID::literal( i, false );
		sets[n] = var_cluster.Singleton( i );
		_nodes[n].infor.visited = true;
		n = NodeID::literal( i, true );
		sets[n] = var_cluster.Singleton( i );
		_nodes[n].infor.visited = true;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
//		cerr << top << endl;  // ToRemove
		if ( top == NodeID(59) ) {
//			Display_Var_Sets( cerr, var_cluster, sets );
		}
		if ( topn.infor.visited ) {
			num_node_stack--;
		}
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.ch[0];
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.ch[1];
			_node_mark_stack[num_node_stack++] = true;
			for ( unsigned i = 2; i < topn.ch_size; i++ ) {
				_node_stack[num_node_stack] = topn.ch[i];
				_node_mark_stack[num_node_stack++] = true;
			}
		}
		else {
			num_node_stack--;
			Compute_Vars( top, var_cluster, sets );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		NodeID n = NodeID::literal( i, false );
		_nodes[n].infor.visited = false;
		n = NodeID::literal( i, true );
		_nodes[n].infor.visited = false;
	}
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
}

void CCDD_Manager::Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	unsigned i;
	if ( _nodes[n].sym <= _max_var ) {
		sets[n] = var_cluster.Union( sets[_nodes[n].ch[0]], sets[_nodes[n].ch[1]], _nodes[n].Var() );
	}
	else if ( _nodes[n].sym == CDD_SYMBOL_DECOMPOSE ) {
		unsigned num_lits = Search_First_Non_Literal_Position( n );
		if ( num_lits < 2 ) {
			_many_sets[0] = sets[_nodes[n].ch[0]];
			_many_sets[1] = sets[_nodes[n].ch[1]];
			for ( i = 2; i < _nodes[n].ch_size; i++ ) {
				_many_sets[i] = sets[_nodes[n].ch[i]];
			}
			sets[n] = var_cluster.Union_Disjoint( _many_sets, _nodes[n].ch_size );
		}
		else {
			_many_vars[0] = _nodes[_nodes[n].ch[0]].sym;
			_many_vars[1] = _nodes[_nodes[n].ch[1]].sym;
			for ( i = 2; i < num_lits; i++ ) {
				_many_vars[i] = _nodes[_nodes[n].ch[i]].sym;
			}
			if ( i == _nodes[n].ch_size ) sets[n] = var_cluster.Set( _many_vars, num_lits );
			else {
				SetID sub_vars;
				if ( i + 1 == _nodes[n].ch_size ) sub_vars = sets[_nodes[n].ch[i]];
				else {
					_many_sets[0] = sets[_nodes[n].ch[i]];
					_many_sets[1] = sets[_nodes[n].ch[i + 1]];
					for ( i += 2; i < _nodes[n].ch_size; i++ ) {
						_many_sets[i - num_lits] = sets[_nodes[n].ch[i]];
					}
					sub_vars = var_cluster.Union_Disjoint( _many_sets, _nodes[n].ch_size - num_lits );
				}
				sets[n] = var_cluster.Union_Disjoint( sub_vars, _many_vars, num_lits );
			}
		}
	}
	else {
		SetID vars = sets[_nodes[n].ch[0]];
		unsigned ch = _nodes[n].ch[1];
		vars = var_cluster.Union( vars, _nodes[ch].sym );
		unsigned lit = _nodes[ch].ch[1];
		_many_vars[0] = _nodes[lit].sym;
		for ( i = 2; i < _nodes[n].ch_size; i++ ) {
			ch = _nodes[n].ch[i];
			vars = var_cluster.Union( vars, _nodes[ch].sym );
			lit = _nodes[ch].ch[1];
			_many_vars[i - 1] = _nodes[lit].sym;
		}
		_qsorter.Sort( _many_vars, _nodes[n].ch_size - 1 );
		sets[n] = var_cluster.Union_Disjoint( vars, _many_vars, _nodes[n].ch_size - 1 );
	}
}

void CCDD_Manager::Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	CDD_Node & node = _nodes[n];
	assert( node.ch_size >= 2 );
	if ( node.sym == CDD_SYMBOL_FALSE ) { assert( node.ch[0] == NodeID::bot && node.ch[1] == NodeID::bot ); }
	else if ( node.sym == CDD_SYMBOL_TRUE ) { assert( node.ch[0] == NodeID::top && node.ch[1] == NodeID::top ); }
	else if ( n <= NodeID::literal( _max_var, true ) ) { assert( Is_Const( node.ch[0] ) && Is_Const( node.ch[1] ) ); }
	else if ( node.sym <= _max_var ) Verify_Decision_Node( node, var_cluster, sets );
	else if ( node.sym == CDD_SYMBOL_DECOMPOSE ) Verify_Decomposition_Node( node, var_cluster, sets );
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) Verify_Kernelization_Node( node, var_cluster, sets );
	else {
		cerr << "ERROR[CDD]: Node " << n << " has a wrong symbol!" << endl;
		assert( node.sym == false );
	}
}

void CCDD_Manager::Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	assert( node.ch_size == 2 );
	if ( Is_Const( node.ch[0] ) && Is_Const( node.ch[1] ) ) {
		cerr << "ERROR[CDD]: Node " << _nodes.Location( node ) << " has two constant children!" << endl;
		assert( !Is_Const( node.ch[0] ) || !Is_Const( node.ch[1] ) );
	}
	assert( node.ch[0] != CDD_SYMBOL_FALSE && node.ch[0] != CDD_SYMBOL_FALSE );
	assert( node.ch[0] != node.ch[1] );
	VarSet vars = var_cluster.Elements( sets[node.ch[0]] );
	for ( unsigned i = 0; i < vars.size; i++ ) {
		assert( node.Var() != vars[i] );
	}
	vars = var_cluster.Elements( sets[node.ch[1]] );
	for ( unsigned i = 0; i < vars.size; i++ ) {
		assert( node.Var() != vars[i] );
	}
	Decision_Node bnode( node.sym, node.ch[0], node.ch[1] );
	if ( BOTH_X( _nodes[bnode.low].sym, _nodes[bnode.high].sym, CDD_SYMBOL_DECOMPOSE ) ) {
		if ( !Intersection_Empty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, _nodes[bnode.high].ch, _nodes[bnode.high].ch_size ) ) {
			cerr << "ERROR[CDD]: Node " << bnode.low << " and Node " << bnode.high << " share children!" << endl;
			assert( Intersection_Empty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, _nodes[bnode.high].ch, _nodes[bnode.high].ch_size ) );
		}
	}
	if ( _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE ) assert( !Search_Exi_Nonempty( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, bnode.low ) );
	if ( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE ) assert( !Search_Exi_Nonempty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, bnode.high ) );
}

void CCDD_Manager::Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	assert( node.ch_size >= 2 );
	for ( unsigned i = 0; i < node.ch_size; i++ ) {
		assert( !Is_Const( node.ch[i] ) );
		if ( _nodes[node.ch[i]].sym == CDD_SYMBOL_DECOMPOSE ) {
			CDD_Node copied( node );
			NodeID id = Push_Node( copied );
			cerr << "Node " << id << " has a decomposed child " << node.ch[i] << endl;
			assert( _nodes[node.ch[i]].sym != CDD_SYMBOL_DECOMPOSE );
		}
		for ( unsigned j = i + 1; j < node.ch_size; j++ ) {
			assert( node.ch[i] < node.ch[j] );
			VarSet vars = var_cluster.Elements( sets[node.ch[j]] );
			for ( unsigned k = 0; k < vars.size; k++ ) {
				assert( !var_cluster.In( sets[node.ch[i]], vars[k] ) );
			}
		}
	}
}

void CCDD_Manager::Verify_Kernelization_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	if ( node.ch[0] == NodeID::top ) assert( node.ch_size >= 3 );
	else assert( node.ch_size >= 2 );
	if ( _nodes[node.ch[0]].sym == CDD_SYMBOL_KERNELIZE || _nodes[node.ch[0]].sym == CDD_SYMBOL_FALSE ) {
		cerr << "Node has a invalid main child " << node.ch[0] << endl;
		assert( _nodes[node.ch[0]].sym != CDD_SYMBOL_KERNELIZE && _nodes[node.ch[0]].sym != CDD_SYMBOL_FALSE );
	}
	assert( _nodes[node.ch[0]].sym != CDD_SYMBOL_KERNELIZE && _nodes[node.ch[0]].sym != CDD_SYMBOL_FALSE );
	SetID main_vars = sets[node.ch[0]];
	if ( main_vars == SETID_EMPTY ) assert( node.ch[0] == NodeID::top );
	vector<Literal> lit_pairs;
	for ( unsigned i = 1; i < node.ch_size; i++ ) {
		assert( _nodes[node.ch[i]].ch_size == 2 );
		Verify_Equivalence_Node( _nodes[node.ch[i]] );
		NodeID * grandch = _nodes[node.ch[i]].ch;
		Literal lit0 = Literal( _nodes[node.ch[i]].Var(), true );
		Literal lit1 = Node2Literal( grandch[1] );
		lit_pairs.push_back( lit0 );
		lit_pairs.push_back( lit1 );
		if ( i > 1 ) assert( node.ch[i-1] < node.ch[i] );
	}
	vector<unsigned> lit_equivalency( 2 * _max_var + 2 );
	for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
		lit_equivalency[lit] = lit;
	}
	lit_equivalency[lit_pairs[1]] = lit_pairs[0];
	for ( unsigned i = 2; i < lit_pairs.size(); i += 2 ) {
		Literal lit0 = lit_pairs[i];
		Literal lit1 = lit_pairs[i + 1];
		assert( lit0.Sign() );
		assert( lit_equivalency[lit0] == lit0 && lit_equivalency[lit1] == lit1 );  // lit1 appears exactly once
		lit_equivalency[~lit1] = ~lit0;
		lit_equivalency[~lit1] = ~lit0;
	}
}

void CCDD_Manager::Verify_Equivalence_Node( CDD_Node & node )
{
	assert( node.ch_size == 2 );
	assert( node.sym <= _max_var );
	assert( node.ch[0] <= NodeID::literal( _max_var, true ) && node.ch[1] <= NodeID::literal( _max_var, true ) );
	assert( node.ch[0] == ( node.ch[1] ^ 0x01 ) );
	CDD_Node & child = _nodes[node.ch[0]];
	assert( Var_LT( node.Var(), child.Var() ) );
}

void CCDD_Manager::Verify_Entail_CNF( CDD root, CNF_Formula & cnf )
{
	Hash_Cluster<Variable> var_cluster( NumVars( _max_var ) );
	vector<SetID> sets( root + 1 );
	Compute_Var_Sets( root, var_cluster, sets );
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		unsigned i;
		for ( i = 0; i < itr->Size(); i++ ) {
			if ( Lit_SAT( (*itr)[i] ) ) break;
			_assignment[(*itr)[i].Var()] = (*itr)[i].NSign();
		}
		if ( i == itr->Size() ) Verify_UNSAT_Under_Assignment( root, var_cluster, sets );
		for ( i--; i != UNSIGNED_UNDEF; i-- ) {
			_assignment[(*itr)[i].Var()] = lbool::unknown;
		}
	}
}

void CCDD_Manager::Verify_UNSAT_Under_Assignment( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	if ( Is_Const( n ) ) {
		assert( n == NodeID::bot );
	}
//	Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	unsigned i, old_size;
	Binary_Map<NodeID, NodeID, NodeID> op_table;
	Binary_Map_Node<NodeID, NodeID, NodeID> op_node;
	_path[0] = n;
	_path_mark[0] = unsigned (-1);
	_decision_levels[0] = 0;
	_num_levels = 1;
	_num_result_stack = 0;
	_num_decisions = 0;
	while ( _num_levels > 0 ) {
		unsigned top = _path[_num_levels - 1];
		if ( Is_Const( top ) ) {
			_result_stack[_num_result_stack++] = ( top == NodeID::top );
			_num_levels--;
			continue;
		}
		CDD_Node & topn = _nodes[_path[_num_levels - 1]];
		if ( _path_mark[_num_levels - 1] == unsigned (-1) ) {
			SetID pre_lits = _num_levels == 1 ? SETID_EMPTY : unsigned(op_table[_cache_stack[_num_levels - 2]].right);
			SetID lits = Pick_Effective_Equ_Decisions( top, pre_lits, var_cluster, sets );
			old_size = op_table.Size();
			op_node.left = top;
			op_node.right = lits;
			_cache_stack[_num_levels - 1] = op_table.Hit( op_node );
			if ( old_size == op_table.Size() ) {
				_result_stack[_num_result_stack++] = op_table[_cache_stack[_num_levels - 1]].result;
				_num_levels--;
				continue;
			}
			_path_mark[_num_levels - 1]++;
		}
		else if ( topn.sym <= _max_var ) {
			if ( _path_mark[_num_levels - 1] == 0 ) {
				if ( _assignment[topn.sym] >= 0 ) {
					_path_mark[_num_levels - 1] = 2;
					_path[_num_levels] = topn.ch[_assignment[topn.sym]];
				}
				else {
					_path_mark[_num_levels - 1]++;
					_path[_num_levels] = topn.ch[0];
				}
				_path_mark[_num_levels] = unsigned (-1);
				_decision_levels[_num_levels] = _num_decisions;
				_num_levels++;
			}
			else if ( _path_mark[_num_levels - 1] == 1 ) {
				if ( _result_stack[_num_result_stack - 1] ) {
					op_table[_cache_stack[_num_levels - 1]].result = true;
					_num_levels--;
					continue;
				}
				_num_result_stack--;
				_path_mark[_num_levels - 1]++;
				_path[_num_levels] = topn.ch[1];
				_path_mark[_num_levels] = unsigned (-1);
				_decision_levels[_num_levels] = _num_decisions;
				_num_levels++;
			}
			else {
				op_table[_cache_stack[_num_levels - 1]].result = _result_stack[_num_result_stack - 1];
				_num_levels--;
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned pos = _path_mark[_num_levels - 1];
			if ( pos < topn.ch_size ) {
				if ( pos > 0 ) {
					if ( !_result_stack[_num_result_stack - 1] ) {
						op_table[_cache_stack[_num_levels - 1]].result = false;
						_num_levels--;
						continue;
					}
					_num_result_stack--;
				}
				_path_mark[_num_levels - 1]++;
				_path[_num_levels] = topn.ch[pos];
				_path_mark[_num_levels] = unsigned (-1);
				_decision_levels[_num_levels] = _num_decisions;
				_num_levels++;
			}
			else {
				op_table[_cache_stack[_num_levels - 1]].result = _result_stack[_num_result_stack - 1];
				_num_levels--;
 			}
		}
		else {
			if ( _path_mark[_num_levels - 1] == 0 ) {
				assert( _decision_levels[_num_levels - 1] == _num_decisions );  // a substituted node does not has a substituted child
				if ( !Propagate_New_Equ_Decisions( top ) ) {
					_result_stack[_num_result_stack++] = false;
					op_table[_cache_stack[_num_levels - 1]].result = false;
					Cancel_Current_Equ_Decisions();
					_num_levels--;
					continue;
				}
				_path_mark[_num_levels - 1]++;
				_path[_num_levels] = topn.ch[0];
				_path_mark[_num_levels] = unsigned (-1);
				_decision_levels[_num_levels] = _decision_levels[_num_levels - 1];
				_num_levels++;
			}
			else {
				Cancel_Current_Equ_Decisions();
				op_table[_cache_stack[_num_levels - 1]].result = _result_stack[_num_result_stack - 1];
				_num_levels--;
			}
		}
	}
	assert( _num_decisions == 0 && _num_levels == 0 && _num_result_stack == 1 );
	if ( (unsigned) _result_stack[0] == 1 ) {
		cerr << "The current assignment:";
		for ( Variable i = Variable::start; i <= _max_var; i++ ) {
			if ( _assignment[i] >= 0 ) cerr << " " << ExtLit( Literal( i, _assignment[i] ) );
		}
		cerr << endl;
		vector<Literal> lit_vec;
		lit_vec.reserve( 64 );
		_path[0] = n;
		_path_mark[0] = 0;
		_num_levels = 1;
		while ( _num_levels ) {
			unsigned top = _path[_num_levels - 1];
			CDD_Node & topn = _nodes[_path[_num_levels - 1]];
			if ( top == NodeID::top ) {
				_num_levels--;
				continue;
			}
			SetID pre_lits = _num_levels == 1 ? SETID_EMPTY : unsigned(op_table[_cache_stack[_num_levels - 2]].right);
			SetID lits = Pick_Effective_Equ_Decisions( top, pre_lits, var_cluster, sets );
			if ( topn.sym <= _max_var ) {
				if ( _assignment[topn.sym] >= 0 ) {
					if ( _path_mark[_num_levels - 1] == 0 ) {
						lit_vec.push_back( Literal( topn.Var(), _assignment[topn.sym] ) );
						_path_mark[_num_levels - 1]++;
						_path[_num_levels] = topn.ch[_assignment[topn.sym]];
						_path_mark[_num_levels++] = 0;
					}
					else _num_levels--;
				}
				else {
					if ( _path_mark[_num_levels - 1] == 0 ) {
						if ( topn.ch[0] == NodeID::bot ) {
							lit_vec.push_back( Literal( topn.Var(), true ) );
							_path_mark[_num_levels - 1]++;
							_path[_num_levels] = topn.ch[1];
							_path_mark[_num_levels++] = 0;
						}
						else if ( topn.ch[0] == NodeID::top ) {
							lit_vec.push_back( Literal( topn.Var(), false ) );
							_path_mark[_num_levels - 1]++;
							_path[_num_levels] = topn.ch[0];
							_path_mark[_num_levels++] = 0;
						}
						else {
							op_node.left = topn.ch[0];
							op_node.right = lits;
							op_node.result = false;
							unsigned cache_pos = op_table.Hit( op_node );
							if ( op_table[cache_pos].result ) {
								lit_vec.push_back( Literal( topn.Var(), false ) );
								_path_mark[_num_levels - 1]++;
								_path[_num_levels] = topn.ch[0];
								_path_mark[_num_levels++] = 0;
							}
							else {
								lit_vec.push_back( Literal( topn.Var(), true ) );
								_path_mark[_num_levels - 1]++;
								_path[_num_levels] = topn.ch[1];
								_path_mark[_num_levels++] = 0;
							}
						}
					}
					else _num_levels--;
				}
			}
			else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
				unsigned pos = _path_mark[_num_levels - 1];
				if ( pos < topn.ch_size ) {
					_path_mark[_num_levels - 1]++;
					_path[_num_levels] = topn.ch[pos];
					_path_mark[_num_levels++] = 0;
				}
				else _num_levels--;
			}
			else {
				Propagate_New_Equ_Decisions( top );
				if ( _path_mark[_num_levels - 1] == 0 ) {
					_path_mark[_num_levels - 1]++;
					_path[_num_levels] = topn.ch[0];
					_path_mark[_num_levels++] = 0;
				}
				else {
					for ( i = 1; i < topn.ch_size; i++ ) {
						CDD_Node & ch = _nodes[topn.ch[i]];
						Variable var = ch.Var();
						if ( _assignment[var] >= 0 ) {
							lit_vec.push_back( Literal( var, _assignment[var] ) );
							assert( !Is_Const( ch.ch[_assignment[var]] ) );
							lit_vec.push_back( Node2Literal( ch.ch[_assignment[var]] ) );
						}
					}
					_num_levels--;
				}
			}
		}
		cerr << "ERROR[CDD]: The following assignment is a model of cdd!" << endl;
		Quick_Sort( lit_vec );
		cerr << ExtLit( lit_vec[0] ) << " ";
		for ( i = 1; i < lit_vec.size(); i++ ) {
			if ( lit_vec[i] != lit_vec[i-1] ) cerr << ExtLit( lit_vec[i] ) << " ";
		}
		cerr << endl;
		exit( 0 );
	}
	_lit_sets.Clear();
	_visited_nodes.clear();
}

void CCDD_Manager::Display_Var_Sets( ostream & out, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	out << "Maximum variable: " << ExtVar( _max_var ) << endl;
	out << "Number of nodes: " << _nodes.Size() << endl;
	out << "0:\t" << "F 0" << endl;
	out << "1:\t" << "T 0" << endl;
	for ( unsigned u = 2; u < _nodes.Size(); u++ ) {
		out << u << ":\t";
		if ( _nodes[u].sym == CDD_SYMBOL_DECOMPOSE ) out << "D";
		else if ( _nodes[u].sym == CDD_SYMBOL_KERNELIZE ) out << "K";
		else out << _nodes[u].sym;
		for ( unsigned i = 0; i < _nodes[u].ch_size; i++ ) {
			out << ' ' << _nodes[u].ch[i];
		}
		out << " 0 ";
		var_cluster.Elements( sets[u] ).Display( out );
		out << endl;
	}
}

SetID CCDD_Manager::Pick_Effective_Equ_Decisions( unsigned n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	unsigned i, num = 0;
	Literal * new_lits = _decision_stack + _decision_levels[_num_levels - 1];
	unsigned num_new = _num_decisions - _decision_levels[_num_levels - 1];
	const LitSet & plits = _lit_sets.Elements( pre_lits );
	SetID vars = sets[n];
	for ( i = 0; i < plits.size; i++ ) {
		Literal lit = plits.elems[i];
		if ( var_cluster.In( vars, lit.Var() ) ) _many_lits[num++] = lit;
	}
	for ( i = 0; i < num_new; i++ ) {
		if ( var_cluster.In( vars, new_lits[i].Var() ) ) _many_lits[num++] = new_lits[i];
	}
	_qsorter.Sort( _many_lits, num );
/*	for ( unsigned i = 0; i < num; i++ ) {  // ToRemove
		cerr << _many_lits[i] << " ";
	}
	cerr << endl;  // ToRemove*/
	return _lit_sets.Set( _many_lits, num );
}

bool CCDD_Manager::Propagate_New_Equ_Decisions( unsigned n )
{
	unsigned i;
	CDD_Node & node = _nodes[n];
	for ( i = 1; i < node.ch_size; i++ ) {
		Literal lit0( _nodes[node.ch[i]].Var(), true );
		Literal lit1 = Node2Literal( _nodes[node.ch[i]].ch[1] );
		if ( Lit_Decided( lit0 ) && Lit_Decided( lit1 ) ) {
			if ( ( Lit_SAT( lit0 ) && Lit_UNSAT( lit1 ) ) || ( Lit_UNSAT( lit0 ) && Lit_SAT( lit1 ) ) ) return false;
		}
		else if ( Lit_Decided( lit1 ) ) {
			if ( Lit_SAT( lit1 ) ) Assign( lit0 );
			else Assign( ~lit0 );
		}
	}
	return true;
}

void CCDD_Manager::Cancel_Current_Equ_Decisions()
{
	while ( _num_decisions > _decision_levels[_num_levels - 1] ) {
		Literal lit = _decision_stack[--_num_decisions];
		_assignment[lit.Var()] = lbool::unknown;
	}
}

void CCDD_Manager::Verify_Model( CDD root, const vector<bool> & sample )
{
	_path[0] = root;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.sym <= _max_var ) {
			if ( top < _num_fixed_nodes ) {
				Literal lit = Node2Literal( top );
				assert( sample[lit.Var()] == lit.Sign() );
				path_len--;
			}
			else _path[path_len - 1] = topn.ch[sample[topn.sym]];
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned loc = Search_First_Non_Literal_Position( top );
			for ( unsigned i = 0; i < loc; i++ ) {
				Literal imp = Node2Literal( topn.ch[i] );
				assert( sample[imp.Var()] == imp.Sign() );
			}
			path_len--;
			for ( unsigned i = loc; i < topn.ch_size; i++ ) {
				_path[path_len++] = topn.ch[i];
			}
		}
		else if ( topn.sym == CDD_SYMBOL_KERNELIZE) {
			for ( unsigned i = 1; i < topn.ch_size; i++ ) {
				CDD_Node & equ = _nodes[topn.ch[i]];
				bool b = sample[equ.sym];
				Literal equ_lit = Node2Literal( equ.ch[b] );
				assert( sample[equ_lit.Var()] == equ_lit.Sign() );
			}
			_path[path_len - 1] = topn.ch[0];
		}
		else {
			assert( top != NodeID::bot );
			path_len--;
		}
	}
}

void CCDD_Manager::Display( ostream & out )
{
	out << "Variable order: ";
	_var_order.Display( out, ' ' );
	Display_Nodes( out );
}

void CCDD_Manager::Display_Stat( ostream & out )
{
	out << "Variable order: ";
	_var_order.Display( out, ' ' );
	Display_Nodes_Stat( out );
}

}

