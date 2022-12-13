#include "OBDD.h"


namespace KCBox {


OBDD_Manager::OBDD_Manager( const Chain & var_order ) :
Diagram_Manager( Variable( var_order.Max() ) ),
Linear_Order( var_order ),
_nodes( LARGE_HASH_TABLE ),
_op_table( LARGE_HASH_TABLE * 10 )
{
    assert( var_order.Max() - Variable::start + 1 == var_order.Size() );
    Allocate_and_Init_Auxiliary_Memory();
	Add_Fixed_Nodes();
}

void OBDD_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_result_stack = new NodeID [_max_var + 2];
}

void OBDD_Manager::Add_Fixed_Nodes()
{
	/* NOTE:
	* Previously, _nodes must be empty
	*/
	BDD_Node node;
	node.var = BDD_SYMBOL_FALSE;
	node.low = NodeID::top;
	node.high = NodeID::top;
	_nodes.Hit( node );
	node.var = BDD_SYMBOL_TRUE;
	node.low = NodeID::top;
	node.high = NodeID::top;
	_nodes.Hit( node );
	/* NOTE:
	* We add <x, 1, 0> and <x, 0, 1> here
	*/
	for ( node.var = Variable::start; node.var <= _max_var; node.var++ ) {
		node.low = NodeID::top;
		node.high = NodeID::bot;
		_nodes.Hit( node );
		assert( _nodes.Size() - 1 == NodeID::literal( node.var, false ) );
		node.low = NodeID::bot;
		node.high = NodeID::top;
		_nodes.Hit( node );
		assert( _nodes.Size() - 1 == NodeID::literal( node.var, true ) );
	}
	_num_fixed_nodes = _nodes.Size();
}

OBDD_Manager::~OBDD_Manager()
{
    Free_Auxiliary_Memory();
}

void OBDD_Manager::Free_Auxiliary_Memory()
{
	delete [] _result_stack;
}

void OBDD_Manager::Reorder( const Chain & new_order )
{
    if ( _nodes.Size() > _num_fixed_nodes ) {
        cerr << "ERROR[OBDD]: cannot be Reorder with non-fixed _nodes!" << endl;
    }
	_var_order = new_order;
}

void OBDD_Manager::Verify_ROBDD( BDD bdd )
{
    Verify_Ordered( bdd );
    Verify_Reduced( bdd );
}

void OBDD_Manager::Verify_Ordered( BDD bdd )
{
	if ( Is_Fixed( bdd ) ) return;
	_nodes[0].infor.visited = true;
	_nodes[1].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_nodes[NodeID::literal( i, false )].infor.visited = true;
		_nodes[NodeID::literal( i, true )].infor.visited = true;
	}
	_node_stack[0] = bdd;
	_nodes[_node_stack[0]].infor.visited = true;
	unsigned num_n_stack = 1;
	_visited_nodes.push_back( _node_stack[0] );
	while ( num_n_stack > 0 ) {
		BDD_Node * node = &(_nodes[_node_stack[num_n_stack - 1]]);
		BDD_Node * low = &(_nodes[node->low]);
		BDD_Node * high = &(_nodes[node->high]);
		if ( !Is_Const( node->low ) && Var_LE( low->var, node->var ) ) {
            cerr << "ERROR[OBDD_Manager]: node " << _node_stack[num_n_stack - 1] << " is not ordered!" << endl;
            assert( Var_LT( node->var, low->var ) );
		}
		if ( !Is_Const( node->high ) && Var_LE( high->var, node->var ) ) {
            cerr << "ERROR[OBDD_Manager]: node " << _node_stack[num_n_stack - 1] << " is not ordered!" << endl;
            assert( Var_LT( node->var, high->var ) );
		}
		num_n_stack--;
		if ( !high->infor.visited ) {
			_node_stack[num_n_stack++] = node->high;
			high->infor.visited = true;
			_visited_nodes.push_back( node->high );
		}
		if ( !low->infor.visited ) {
			_node_stack[num_n_stack++] = node->low;
			low->infor.visited = true;
			_visited_nodes.push_back( node->low );
		}
	}
	_nodes[0].infor.visited = false;
	_nodes[1].infor.visited = false;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_nodes[NodeID::literal( i, false )].infor.visited = false;
		_nodes[NodeID::literal( i, true )].infor.visited = false;
	}
	vector<NodeID>::iterator itr, end = _visited_nodes.end();
	for ( itr = _visited_nodes.begin(); itr < end; itr++ ) _nodes[*itr].infor.visited = false;
	_visited_nodes.clear();
}

void OBDD_Manager::Verify_Reduced( BDD bdd )
{
	if ( Is_Fixed( bdd ) ) return;
	_nodes[0].infor.visited = true;
	_nodes[1].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_nodes[NodeID::literal( i, false )].infor.visited = true;
		_nodes[NodeID::literal( i, true )].infor.visited = true;
	}
	_node_stack[0] = bdd;
	_nodes[_node_stack[0]].infor.visited = true;
	unsigned num_n_stack = 1;
	_visited_nodes.push_back( _node_stack[0] );
	while ( num_n_stack > 0 ) {
		BDD_Node * node = &(_nodes[_node_stack[num_n_stack - 1]]);
		BDD_Node * low = &(_nodes[node->low]);
		BDD_Node * high = &(_nodes[node->high]);
		if ( node->low == node->high ) {
            cerr << "ERROR[OBDD_Manager]: node " << _node_stack[num_n_stack - 1] << " is not reduced!" << endl;
            assert( node->low != node->high );
		}
		num_n_stack--;
		if ( !high->infor.visited ) {
			_node_stack[num_n_stack++] = node->high;
			high->infor.visited = true;
			_visited_nodes.push_back( node->high );
		}
		if ( !low->infor.visited ) {
			_node_stack[num_n_stack++] = node->low;
			low->infor.visited = true;
			_visited_nodes.push_back( node->low );
		}
	}
	_nodes[0].infor.visited = false;
	_nodes[1].infor.visited = false;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_nodes[NodeID::literal( i, false )].infor.visited = false;
		_nodes[NodeID::literal( i, true )].infor.visited = false;
	}
	vector<NodeID>::iterator itr, end = _visited_nodes.end();
	for ( itr = _visited_nodes.begin(); itr < end; itr++ ) _nodes[*itr].infor.visited = false;
	_visited_nodes.clear();
}

BigInt OBDD_Manager::Count_Models( BDD bdd )
{
	if ( bdd == NodeID::bot ) return 0;
	if ( bdd == NodeID::top ) {
		BigInt result = 1;
		result.Mul_2exp( _max_var - Variable::start + 1 );
		return result;
	}
	if ( Is_Fixed( bdd ) ) {
		BigInt result = 1;
		result.Mul_2exp( _max_var - Variable::start );
		return result;
	}
	BigInt * results = new BigInt [bdd + 1];
	BigInt result = 1;
	result.Mul_2exp( _max_var - Variable::start );  // the number of models of a literal
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = result;
	results[NodeID::top].Mul_2exp( 1 );
	_nodes[NodeID::top].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		NodeID pos = NodeID::literal( i, false );
		results[pos] = result;
        _nodes[pos].infor.visited = true;
		pos = NodeID::literal( i, true );
		results[pos] = result;
        _nodes[pos].infor.visited = true;
	}
	_path[0] = bdd;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
        NodeID top = _path[path_len - 1];
		BDD_Node & topn = _nodes[top];
		BDD_Node & low = _nodes[topn.low];
		BDD_Node & high = _nodes[topn.high];
		switch ( _path_mark[path_len - 1]++ ) {
		case 0:
			if ( !low.infor.visited ) {
				_path[path_len] = topn.low;
				_path_mark[path_len++] = 0;
				low.infor.visited = true;
				_visited_nodes.push_back( topn.low );
			}
			break;
		case 1:
			if ( !high.infor.visited ) {
				_path[path_len] = topn.high;
				_path_mark[path_len++] = 0;
				high.infor.visited = true;
				_visited_nodes.push_back( topn.high );
			}
			break;
		case 2:
			results[top] = results[topn.low];
			results[top] += results[topn.high];
			results[top].Div_2exp( 1 );
			path_len--;
			break;
		}
	}
	result = results[bdd];
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		NodeID pos = NodeID::literal( i, false );
        _nodes[pos].infor.visited = false;
		pos = NodeID::literal( i, true );
        _nodes[pos].infor.visited = false;
	}
	vector<NodeID>::iterator itr, end = _visited_nodes.end();
	for ( itr = _visited_nodes.begin(); itr < end; itr++ ) {
        _nodes[*itr].infor.visited = false;
	}
	delete [] results;
	return result;
}

bool OBDD_Manager::Entail_Clause( BDD root, Clause & clause )
{
	unsigned i;
	for ( i = 0; i < clause.Size(); i++ ) {
		if ( Lit_SAT( clause[i] ) ) {
			break;
		}
		_assignment[clause[i].Var()] = clause[i].NSign();
	}
	bool result;
	if ( i < clause.Size() ) result = true;
	else result = !Decide_SAT_Under_Assignment( root );
	for ( i--; i != (unsigned) -1; i-- ) {
		_assignment[clause[i].Var()] = lbool::unknown;
	}
	return result;
}

bool OBDD_Manager::Decide_SAT_Under_Assignment( BDD root )
{
	if ( Is_Const( root ) ) return root == NodeID::top;
	_nodes[0].infor.mark = 0;
	_nodes[1].infor.mark = 1;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( Var_Decided( i ) ) {
			_nodes[i + i].infor.mark = ( _assignment[i] == false );
			_nodes[i + i + 1].infor.mark = ( _assignment[i] == true );
		}
		else {
			_nodes[i + i].infor.mark = 1;
			_nodes[i + i + 1].infor.mark = 1;
		}
	}
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len ) {
		BDD_Node & topn = _nodes[_path[path_len - 1]];
		if ( Var_Decided( topn.var ) ) {
			NodeID ch = ( _assignment[topn.var] == false ) ? topn.low : topn.high;
			if ( _nodes[ch].infor.mark == UNSIGNED_UNDEF ) {
				_path[path_len] = ch;
				_path_mark[path_len++] = 0;
			}
			else {
				topn.infor.mark = _nodes[ch].infor.mark;
				_visited_nodes.push_back( _path[--path_len] );
			}
		}
		else {
			switch ( _path_mark[path_len - 1] ) {
				case 0:
					if ( EITHOR_X( _nodes[topn.low].infor.mark, _nodes[topn.high].infor.mark, 1 ) ) {
						topn.infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( BOTH_ZERO( _nodes[topn.low].infor.mark, _nodes[topn.high].infor.mark ) ) {
						topn.infor.mark = 0;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( _nodes[topn.low].infor.mark == 0 ) {
						_path[path_len] = topn.high;
						_path_mark[path_len - 1] += 2;
						_path_mark[path_len++] = 0;
					}
					else {
						_path[path_len] = topn.low;
						_path_mark[path_len - 1]++;
						_path_mark[path_len++] = 0;
					}
					break;
				case 1:
					if ( _nodes[topn.low].infor.mark == 1 ) {
						topn.infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( _nodes[topn.high].infor.mark != UNSIGNED_UNDEF ) { // ch[1] may be a descendant of ch[0]
						topn.infor.mark = _nodes[topn.high].infor.mark;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = topn.high;
						_path_mark[path_len - 1]++;
						_path_mark[path_len++] = 0;
					}
					break;
				case 2:
					topn.infor.mark = _nodes[topn.high].infor.mark;
					_visited_nodes.push_back( _path[--path_len] );
					break;
			}
		}
	}
	bool result = _nodes[root].infor.mark == 1;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_nodes[i + i].infor.mark = UNSIGNED_UNDEF;
		_nodes[i + i + 1].infor.mark = UNSIGNED_UNDEF;
	}
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
	return result;
}

bool OBDD_Manager::Entail_CNF( BDD root, CNF_Formula & cnf )
{
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		cerr << itr - cnf.Clause_Begin() << endl;
		if ( !Entail_Clause( root, *itr ) ) return false;
	}
	return true;
}

BDD OBDD_Manager::Convert( Clause & clause )
{
    if ( clause.Size() == 0 ) return NodeID::bot;
    assert( clause[0] <= 2 * _max_var + 1 );
    if ( clause.Size() == 1 ) return NodeID::literal( clause[0] );
    unsigned i, len;
    for ( i = len = 1; i < clause.Size(); i++ ) {
    	assert( Lit_LT( clause[len-1], clause[i] ) && clause[len-1].Var() == clause[i].Var() );
    	if ( clause[len-1] == clause[i] ) continue;
    	if ( clause[len-1] == ~clause[i] ) break;
    	clause[len++] = clause[i];
    }
    if ( i < clause.Size() ) return NodeID::top;
    clause.Shrink( len );
    Decision_Node bnode;
	NodeID root = NodeID::literal( clause[len - 1] );
	for ( i = 1; i < len; i++ ) {
		Literal lit = clause[len - i - 1];
		bnode.var = lit.Var();
		if ( lit.Sign() ) {
            bnode.low = root;
            bnode.high = NodeID::top;
		}
		else {
            bnode.low = NodeID::top;
            bnode.high = root;
		}
        root = Push_Node( bnode );
	}
	return root;
}

BDD OBDD_Manager::Convert( CNF_Formula & cnf )
{
	if ( cnf.Num_Clauses() == 0 ) return NodeID::top;
	unsigned * var_rank = new unsigned [_max_var + 1];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		var_rank[i] = _var_order.Rank( i );
	}
	cnf[0].Sort( var_rank );
	BDD root = Convert( cnf[0] );
	for ( unsigned i = 1; i < cnf.Num_Clauses(); i++ ) {
		cnf[i].Sort( var_rank );
		BDD inc = Convert( cnf[i] );
		root = Conjoin( root, inc );
	}
	delete [] var_rank;
	return root;
}

BDD OBDD_Manager::Conjoin( BDD left, BDD right )
{
	Binary_Map_Node<NodeID, NodeID, NodeID> op_table_node;
	_node_stack[0] = left;
	_path[0] = right;
	_node_mark_stack[0] = 1;
	unsigned num_n_stack = 1;
	_num_result_stack = 0;
	unsigned * c_stack = new unsigned [2 * _max_var + 2];  // c denotes cache
	unsigned * v_stack = new unsigned [2 * _max_var + 2];  // v denotes var
	while ( num_n_stack ) {
		op_table_node.left = _node_stack[num_n_stack - 1];
		op_table_node.right  = _path[num_n_stack - 1];
		if ( EITHOR_X( op_table_node.left, op_table_node.right, NodeID::bot ) ) {
			_result_stack[_num_result_stack++] = NodeID::bot;
			num_n_stack--;
		}
		else if ( EITHOR_X( op_table_node.left, op_table_node.right, NodeID::top ) ) {
			_result_stack[_num_result_stack++] = op_table_node.left + op_table_node.right - NodeID::top;
			num_n_stack--;
		}
		else if ( _node_mark_stack[num_n_stack - 1] ) {
			_node_mark_stack[num_n_stack - 1] = false;  // NOTE: indicate that this case is computed
			unsigned old_size = _op_table.Size();
			c_stack[num_n_stack - 1] = _op_table.Hit( op_table_node );
			if ( c_stack[num_n_stack - 1] < old_size ) {
				_result_stack[_num_result_stack++] = _op_table[c_stack[num_n_stack - 1]].result;
				num_n_stack--;
			}
			else if ( Var_LT( _nodes[op_table_node.left].var, _nodes[op_table_node.right].var ) ) {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.left].var;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].high;
				_path[num_n_stack] = op_table_node.right;
				_node_mark_stack[num_n_stack++] = true;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].low;
				_path[num_n_stack] = op_table_node.right;
				_node_mark_stack[num_n_stack++] = true;
			}
			else if ( Var_LT( _nodes[op_table_node.right].var, _nodes[op_table_node.left].var ) ) {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.right].var;
				_node_stack[num_n_stack] = op_table_node.left;
				_path[num_n_stack] = _nodes[op_table_node.right].high;
				_node_mark_stack[num_n_stack++] = true;
				_node_stack[num_n_stack] = op_table_node.left;
				_path[num_n_stack] = _nodes[op_table_node.right].low;
				_node_mark_stack[num_n_stack++] = true;
			}
			else {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.left].var;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].high;
				_path[num_n_stack] = _nodes[op_table_node.right].high;
				_node_mark_stack[num_n_stack++] = true;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].low;
				_path[num_n_stack] = _nodes[op_table_node.right].low;
				_node_mark_stack[num_n_stack++] = true;
			}
		}
		else {
			_num_result_stack--, num_n_stack--;
			if ( _result_stack[_num_result_stack - 1] != _result_stack[_num_result_stack] ) {
				BDD_Node node;
				node.var = v_stack[num_n_stack];
				node.low = _result_stack[_num_result_stack - 1];
				node.high = _result_stack[_num_result_stack];
				_result_stack[_num_result_stack - 1] = Push_Node( node );
			}
			_op_table[c_stack[num_n_stack]].result = _result_stack[_num_result_stack - 1];
		}
	}
	_op_table.Clear();
	delete [] v_stack;
	delete [] c_stack;
	return _result_stack[0];
}

BDD OBDD_Manager::Disjoin( BDD left, BDD right )
{
	Binary_Map_Node<NodeID, NodeID, NodeID> op_table_node;
	_node_stack[0] = left;
	_path[0] = right;
	_node_mark_stack[0] = 1;
	unsigned num_n_stack = 1;
	_num_result_stack = 0;
	unsigned * c_stack = new unsigned [2 * _max_var + 2];  // c denotes cache
	unsigned * v_stack = new unsigned [2 * _max_var + 2];  // v denotes var
	while ( num_n_stack ) {
		op_table_node.left = _node_stack[num_n_stack - 1];
		op_table_node.right  = _path[num_n_stack - 1];
		if ( EITHOR_X( op_table_node.left, op_table_node.right, NodeID::top ) ) {
			_result_stack[_num_result_stack++] = NodeID::top;
			num_n_stack--;
		}
		else if ( EITHOR_X( op_table_node.left, op_table_node.right, NodeID::bot ) ) {
			_result_stack[_num_result_stack++] = op_table_node.left + op_table_node.right - NodeID::bot;
			num_n_stack--;
		}
		else if ( _node_mark_stack[num_n_stack - 1] ) {
			_node_mark_stack[num_n_stack - 1]--;  // NOTE: indicate that this case is computed
			unsigned old_size = _op_table.Size();
			c_stack[num_n_stack - 1] = _op_table.Hit( op_table_node );
			if ( c_stack[num_n_stack - 1] < old_size ) {
				_result_stack[_num_result_stack++] = _op_table[c_stack[num_n_stack - 1]].result;
				num_n_stack--;
			}
			else if ( Var_LT( _nodes[op_table_node.left].var, _nodes[op_table_node.right].var ) ) {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.left].var;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].high;
				_path[num_n_stack] = op_table_node.right;
				_node_mark_stack[num_n_stack++] = 1;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].low;
				_path[num_n_stack] = op_table_node.right;
				_node_mark_stack[num_n_stack++] = 1;
			}
			else if ( Var_LT( _nodes[op_table_node.right].var, _nodes[op_table_node.left].var ) ) {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.right].var;
				_node_stack[num_n_stack] = op_table_node.left;
				_path[num_n_stack] = _nodes[op_table_node.right].high;
				_node_mark_stack[num_n_stack++] = 1;
				_node_stack[num_n_stack] = op_table_node.left;
				_path[num_n_stack] = _nodes[op_table_node.right].low;
				_node_mark_stack[num_n_stack++] = 1;
			}
			else {
				v_stack[num_n_stack - 1] = _nodes[op_table_node.left].var;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].high;
				_path[num_n_stack] = _nodes[op_table_node.right].high;
				_node_mark_stack[num_n_stack++] = 1;
				_node_stack[num_n_stack] = _nodes[op_table_node.left].low;
				_path[num_n_stack] = _nodes[op_table_node.right].low;
				_node_mark_stack[num_n_stack++] = 1;
			}
		}
		else {
			_num_result_stack--, num_n_stack--;
			if ( _result_stack[_num_result_stack - 1] != _result_stack[_num_result_stack] ) {
				BDD_Node node;
				node.var = v_stack[num_n_stack];
				node.low = _result_stack[_num_result_stack - 1];
				node.high = _result_stack[_num_result_stack];
				_result_stack[_num_result_stack - 1] = Push_Node( node );
			}
			_op_table[c_stack[num_n_stack]].result = _result_stack[_num_result_stack - 1];
		}
	}
	_op_table.Clear();
	delete [] v_stack;
	delete [] c_stack;
	return _result_stack[0];
}

EPCCL_Theory * OBDD_Manager::Convert_EPCCL( BDD root )
{
	EPCCL_Theory * cnf = new EPCCL_Theory( _max_var );
	Big_Clause clause( _max_var );
	if ( root == NodeID::bot ) {
	    clause.Resize( 1 );
		clause[0] = Literal::start;
		cnf->Add_Clause( clause );
		clause[1] = Literal::start_neg;
		cnf->Add_Clause( clause );
		return cnf;
	}
	if ( root == NodeID::top ) {
		return cnf;
	}
	unsigned i;
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len ) {
		if ( _path[path_len - 1] == NodeID::bot ) {
			for ( i = 0; i < path_len - 1; i++ ) {
				if ( _path[i + 1] == _nodes[_path[i]].low ) clause.Add_Lit( Literal(_nodes[_path[i]].var, true ) );
				else clause.Add_Lit( Literal( _nodes[_path[i]].var, false ) );
			}
			cnf->Add_Clause( clause );
			clause.Clear();
			path_len--;
			continue;
		}
		if ( _path[path_len - 1] == NodeID::top ) {
			path_len--;
			continue;
		}
		BDD_Node & topn = _nodes[_path[path_len - 1]];
		switch ( _path_mark[path_len - 1]++ ) {
			case 0:
				_path[path_len] = topn.low;
				_path_mark[path_len++] = 0;
				break;
			case 1:
				_path[path_len] = topn.high;
				_path_mark[path_len++] = 0;
				break;
			case 2:
				path_len--;
		}
	}
	return cnf;
}

void OBDD_Manager::Display( ostream & out )
{
	unsigned i;
	out << "Variable order: ";
	_var_order.Display( out );
	out << "Number of nodes: " << _nodes.Size() << endl;
	out << "0:\t F - -" << endl;
	out << "1:\t T - -" << endl;
	for ( i = 2; i < _nodes.Size(); i++ ) {
		out << i << ":\t " << _nodes[i].var << ' ' << _nodes[i].low << ' ' << _nodes[i].high << endl;
	}
}


}
