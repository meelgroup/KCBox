#include "RCDD.h"


namespace KCBox {


RCDD_Manager::RCDD_Manager( Variable max_var, unsigned estimated_node_num ):
CDD_Manager( max_var, estimated_node_num ),
_lit_sets( _max_var + 1 )
{
	Generate_Lexicographic_Var_Order( _max_var );
	Allocate_and_Init_Auxiliary_Memory();
}

void RCDD_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_lit_equivalency.Reorder( _var_order );
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
	_aux_rnode2.Reset_Max_Var( _max_var );
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

RCDD_Manager::RCDD_Manager( Chain & vorder, unsigned estimated_node_num ):
CDD_Manager( Variable( vorder.Max() ), estimated_node_num ),
Linear_Order( vorder ),
_lit_sets( _max_var + 1 )
{
	Allocate_and_Init_Auxiliary_Memory();
}

RCDD_Manager::RCDD_Manager( istream & fin ):
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
	if ( !Read_String_Change( p, "Variable order:" ) ) {
		cerr << "ERROR[CDD]: the CDD-file does not state the variable order!" << endl;
		exit( 1 );
	}
	Exactly_Read_Unsigneds( p, arr );
	_var_order.Append( arr.begin(), arr.end() );
	Diagram_Manager::Allocate_and_Init_Auxiliary_Memory( Variable( _var_order.Max() ) );
	CDD_Manager::Enlarge_Max_Var( Variable( _var_order.Max() ) );
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
		if ( *p == 'D' || *p == 'K' ) {
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

RCDD_Manager::RCDD_Manager( RCDD_Manager & other ):
CDD_Manager( other._max_var, other._nodes.Size() * 2 ),
Linear_Order( other._var_order ),
_lit_sets( 2 * _max_var + 2 )
{
	Allocate_and_Init_Auxiliary_Memory();
	for ( unsigned u = _num_fixed_nodes; u < other._nodes.Size(); u++ ) {
		Push_New_Node( other._nodes[u] );
	}
}

RCDD_Manager::~RCDD_Manager()
{
	Free_Auxiliary_Memory();
}

void RCDD_Manager::Free_Auxiliary_Memory()
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

void RCDD_Manager::Reorder( Chain & new_order )
{
	if ( _nodes.Size() > _num_fixed_nodes ) {
		cerr << "ERROR[CDD]: cannot be Reorder with non-fixed nodes yet!" << endl;
	}
	_var_order = new_order;
	_lit_equivalency.Reorder( new_order );
}

void RCDD_Manager::Enlarge_Max_Var( Chain & new_order )
{
	assert( _var_order.Subchain( new_order ) );
	if ( new_order.Max() - Variable::start + 1 != new_order.Size() ) {
		cerr << "ERROR[CDD]: wrong variable ordering!" << endl;
		exit( 1 );
	}
	_var_order = new_order;
	CDD_Manager::Enlarge_Max_Var( Variable( _var_order.Max() ) );
	Free_Auxiliary_Memory();
	Allocate_and_Init_Auxiliary_Memory();
}

BigInt RCDD_Manager::Count_Models( CDD root )
{
	if ( Is_Fixed( root ) ) {
		if ( root == NodeID::bot ) return 0;
		BigInt result = 1;
		result.Mul_2exp( _max_var );
		result.Div_2exp( root != NodeID::top );
		return result;
	}
	BigInt * results = new BigInt [root + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = 1;
	results[NodeID::top].Mul_2exp( _max_var );
	_nodes[NodeID::top].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		NodeID n = NodeID::literal( i, false );
		results[n] = 1;
		results[n].Mul_2exp( _max_var - 1 );
		_nodes[n].infor.visited = true;
		n = NodeID::literal( i, true );
		results[n] = 1;
		results[n].Mul_2exp( _max_var - 1 );
		_nodes[n].infor.visited = true;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		CDD top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
//		cerr << top << endl;  // ToRemove
		if ( topn.infor.visited ) {
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
				results[top] = results[topn.ch[0]];
				results[top] += results[topn.ch[1]];
				results[top].Div_2exp( 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
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
				results[top] = results[topn.ch[0]];
				results[top] *= results[topn.ch[1]];
				results[top].Div_2exp( _max_var );
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
					results[top].Div_2exp( _max_var );
				}
				if ( top == root && DEBUG_OFF ) {
					cerr << "results[" << topn.ch[0] << "] = " << results[topn.ch[0]] << endl;
					cerr << "results[" << topn.ch[1] << "] = " << results[topn.ch[1]] << endl;
					for ( unsigned i = 2; i < topn.ch_size; i++ ) {
						cerr << "results[" << topn.ch[i] << "] = " << results[topn.ch[i]] << endl;;
					}
					cerr << "results[" << top << "] = " << results[top] << endl;
				}
				topn.infor.visited = true;
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
				results[top] = results[topn.ch[0]];
				results[top].Div_2exp( topn.ch_size - 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
			}
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
	BigInt result = results[root];
	delete [] results;
	return result;
}

BigInt RCDD_Manager::Count_Models_Opt( BDDC root )
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
	_visited_nodes.clear();
	delete [] results;
	return result;
}

CDD RCDD_Manager::Add_Node( Rough_CDD_Node & rnode )
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

CDD RCDD_Manager::Add_Decision_Node( Decision_Node & bnode )
{
	assert( Variable::start <= bnode.var && bnode.var <= _max_var );
	assert( bnode.low < _nodes.Size() && bnode.high < _nodes.Size() );
	NodeID tmp_link, low = bnode.low, high = bnode.high;
	if ( low == high ) tmp_link = low;
    else if ( Is_Const( bnode.low ) && Is_Const( bnode.high ) ) tmp_link = NodeID::literal( bnode.var, bnode.high == NodeID::top );
	else if ( low == NodeID::bot ) tmp_link = Extract_Leaf_Left_No_Check( bnode );
	else if ( high == NodeID::bot ) tmp_link = Extract_Leaf_Right_No_Check( bnode );
	else if ( BOTH_X( _nodes[low].sym, _nodes[high].sym, CDD_SYMBOL_DECOMPOSE ) ) {
		tmp_link = Extract_Share_Semi_Check( bnode );
	}
	else if ( _nodes[high].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[high].ch, _nodes[high].ch_size, low ) ) {
		tmp_link = Extract_Part_Left_No_Check( bnode );
	}
	else if ( _nodes[low].sym == CDD_SYMBOL_DECOMPOSE && \
		Search_Exi_Nonempty( _nodes[low].ch, _nodes[low].ch_size, high ) ) {
		tmp_link = Extract_Part_Right_No_Check( bnode );
	}
    else tmp_link = Push_Node( bnode );
	return tmp_link;
}

NodeID RCDD_Manager::Extract_Leaf_Left_No_Check( Decision_Node & bnode )
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

NodeID RCDD_Manager::Extract_Leaf_Right_No_Check( Decision_Node & bnode )
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

NodeID RCDD_Manager::Extract_Share_Semi_Check( Decision_Node & bnode )  // use _lit_seen, _many_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
//	unsigned old_size = _nodes.Size();  // ToRemove
	assert( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE && _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE );
	unsigned num_shared = Intersection( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, \
		_nodes[bnode.high].ch, _nodes[bnode.high].ch_size, _many_nodes );
	if ( num_shared == 0 ) return Push_Node( bnode );
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
		n = Push_Node( bnode );
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

NodeID RCDD_Manager::Remove_Children( NodeID parent, NodeID * children, unsigned num_ch )
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

NodeID RCDD_Manager::Extract_Part_Left_No_Check( Decision_Node & bnode )
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

NodeID RCDD_Manager::Remove_Child_No_Check_GE_3( NodeID parent, NodeID child )
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

NodeID RCDD_Manager::Extract_Part_Right_No_Check( Decision_Node & bnode )
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

NodeID RCDD_Manager::Remove_Child_No_Check( NodeID parent, NodeID child )
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

CDD RCDD_Manager::Add_Decomposition_Node( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, node_set_sizes, _aux_decom_rnode
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
		_aux_decom_rnode.ch_size = 0;
		for ( i = 0; i < rnode.ch_size; i++ ) {
			if ( _nodes[rnode.ch[i]].sym != CDD_SYMBOL_TRUE ) {
				assert( rnode.ch[i] < _nodes.Size() );
				_aux_decom_rnode.Add_Child( rnode.ch[i] );
			}
		}
		if ( _aux_decom_rnode.ch_size == 0 ) tmp_link = CDD_SYMBOL_TRUE;
		else if ( _aux_decom_rnode.ch_size == 1 ) tmp_link = rnode.ch[0];
		else {
			_qsorter.Sort( _aux_decom_rnode.ch, _aux_decom_rnode.ch_size );  // ToCheck
			tmp_link = Finest( _aux_decom_rnode );
		}
	}
	return tmp_link;
}

unsigned RCDD_Manager::Finest( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, _node_set_sizes
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

CDD RCDD_Manager::Add_Kernelization_Node( Rough_CDD_Node & rnode )  // use _many_nodes, _many_equ_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
	assert( rnode.sym == CDD_SYMBOL_KERNELIZE );
	if ( rnode.ch_size == 1 ) return rnode.ch[0];
	CDD cdd;
	unsigned main_ch_sym = _nodes[rnode.ch[0]].sym;
	if ( main_ch_sym == CDD_SYMBOL_KERNELIZE ) {
		CDD_Node & node = _nodes[rnode.ch[0]];
		for ( unsigned i = 1; i < node.ch_size; i++ ) {
			NodeID * grandch = _nodes[node.ch[i]].ch;
			Literal lit0( _nodes[node.ch[i]].Var(), true );
			Literal lit1 = Node2Literal( grandch[1] );
			_lit_equivalency.Add_Equivalence( lit0, lit1 );
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

unsigned RCDD_Manager::Transform_Lit_Equivalences( Lit_Equivalency & lit_equivalency, NodeID * equ_nodes )
{
	unsigned num_equ = lit_equivalency.Output_Equivalences( _many_lits );
	for ( unsigned i = 0; i < num_equ; i++ ) {
		Literal lit = _many_lits[i + i], lit2 = _many_lits[i + i + 1];
		equ_nodes[i] = Push_Equivalence_Node( lit, lit2 );
	}
	_qsorter.Sort( equ_nodes, num_equ );
	return num_equ;
}

CDD RCDD_Manager::Add_Equivalence_Node( int elit, int elit2 )
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

unsigned RCDD_Manager::Add_Equivalence_Nodes( const vector<Literal> & lit_equivalences, NodeID * nodes )
{
	for ( unsigned i = 0; i < lit_equivalences.size(); i += 2 ) {
		Literal lit0 = lit_equivalences[i];
		Literal lit1 = lit_equivalences[i + 1];
		_lit_equivalency.Add_Equivalence( lit0, lit1 );
	}
	NodeID n = Transform_Lit_Equivalences( _lit_equivalency, nodes );
	_lit_equivalency.Reset();
	return n;
}

unsigned RCDD_Manager::Add_Equivalence_Nodes( Literal * lit_pairs, unsigned num_pairs, NodeID * nodes )
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

unsigned RCDD_Manager::Finest_Last( Rough_CDD_Node & rnode )
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

void RCDD_Manager::Verify_RCDD( CDD root )
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

void RCDD_Manager::Compute_Var_Sets( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void RCDD_Manager::Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void RCDD_Manager::Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	CDD_Node & node = _nodes[n];
	assert( node.ch_size >= 2 );
	if ( node.sym == CDD_SYMBOL_FALSE ) { assert( node.ch[0] == NodeID::bot && node.ch[1] == NodeID::bot ); }
	else if ( node.sym == CDD_SYMBOL_TRUE ) { assert( node.ch[0] == NodeID::top && node.ch[1] == NodeID::top ); }
	else if ( n <= NodeID::literal( _max_var, true ) ) { assert( Is_Const( node.ch[0] ) && Is_Const( node.ch[1] ) ); }
	else if ( node.sym <= _max_var ) Verify_Decision_Node( node, var_cluster, sets );
	else if ( node.sym == CDD_SYMBOL_DECOMPOSE ) Verify_Decomposition_Node( node, var_cluster, sets );
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) Verify_Substitution_Node( node, var_cluster, sets );
	else {
		cerr << "ERROR[CDD]: Node " << n << " has a wrong symbol!" << endl;
		assert( node.sym == false );
	}
}

void RCDD_Manager::Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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
		assert( Var_LT( node.Var(), vars[i] ) );
	}
	vars = var_cluster.Elements( sets[node.ch[1]] );
	for ( unsigned i = 0; i < vars.size; i++ ) {
		assert( Var_LT( node.Var(), vars[i] ) );
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

void RCDD_Manager::Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	assert( node.ch_size >= 2 );
	for ( unsigned i = 0; i < node.ch_size; i++ ) {
		assert( !Is_Const( node.ch[i] ) );
		assert( _nodes[node.ch[i]].sym != CDD_SYMBOL_DECOMPOSE );
		for ( unsigned j = i + 1; j < node.ch_size; j++ ) {
			assert( node.ch[i] < node.ch[j] );
			VarSet vars = var_cluster.Elements( sets[node.ch[j]] );
			for ( unsigned k = 0; k < vars.size; k++ ) {
				assert( !var_cluster.In( sets[node.ch[i]], vars[k] ) );
			}
		}
	}
}

void RCDD_Manager::Verify_Substitution_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	if ( node.ch[0] == NodeID::top ) assert( node.ch_size >= 3 );
	else assert( node.ch_size >= 2 );
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

void RCDD_Manager::Verify_Equivalence_Node( CDD_Node & node )
{
	assert( node.ch_size == 2 );
	assert( node.sym <= _max_var );
	assert( node.ch[0] <= NodeID::literal( _max_var, true ) && node.ch[1] <= NodeID::literal( _max_var, true ) );
	assert( node.ch[0] == ( node.ch[1] ^ 0x01 ) );
	CDD_Node & child = _nodes[node.ch[0]];
	assert( Var_LT( node.Var(), child.Var() ) );
}

void RCDD_Manager::Verify_Entail_CNF( CDD root, CNF_Formula & cnf )
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

void RCDD_Manager::Verify_UNSAT_Under_Assignment( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

SetID RCDD_Manager::Pick_Effective_Equ_Decisions( unsigned n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

bool RCDD_Manager::Propagate_New_Equ_Decisions( unsigned n )
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

void RCDD_Manager::Cancel_Current_Equ_Decisions()
{
	while ( _num_decisions > _decision_levels[_num_levels - 1] ) {
		Literal lit = _decision_stack[--_num_decisions];
		_assignment[lit.Var()] = lbool::unknown;
	}
}

void RCDD_Manager::Display( ostream & out )
{
	out << "Variable order:";
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		out << ' ' << _var_order[i];
	}
	out << endl;
	out << "Number of nodes: " << _nodes.Size() << endl;
	out << "0:\t" << "F 0" << endl;
	out << "1:\t" << "T 0" << endl;
	for ( unsigned u = 2; u < _nodes.Size(); u++ ) {
		out << u << ":\t";
		_nodes[u].Display( out, false );
	}
}

void RCDD_Manager::Display_Stat( ostream & out )
{
	out << "Variable order:";
	for ( unsigned i = 0; i < _var_order.Size(); i++ ) {
		out << ' ' << _var_order[i];
	}
	out << endl;
	out << "Number of nodes: " << _nodes.Size() << endl;
	for ( unsigned u = 0; u < _nodes.Size(); u++ ) {
		out << u << ":\t";
		_nodes[u].Display( out, true );
	}
}


}

