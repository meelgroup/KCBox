#include "OBDD.h"


namespace KCBox {


OBDD_Manager::OBDD_Manager( Variable max_var ): // _var_order is not assigned
Diagram_Manager( max_var ),
_nodes( LARGE_HASH_TABLE ),
_op_table( LARGE_HASH_TABLE * 10 )
{
	Generate_Lexicographic_Var_Order( _max_var );
	Add_Fixed_Nodes();
	Allocate_and_Init_Auxiliary_Memory();
}

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
	_hash_memory = _nodes.Memory();
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

void OBDD_Manager::Verify_ROBDD( Diagram & bdd )
{
	assert( Contain( bdd ) );
	Verify_Ordered( bdd.Root() );
	Verify_Reduced( bdd.Root() );
}

void OBDD_Manager::Verify_Ordered( NodeID bdd )
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

void OBDD_Manager::Verify_Reduced( NodeID bdd )
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

void OBDD_Manager::Remove_Redundant_Nodes()
{
	DLList_Node<NodeID> * itr;
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		_nodes[itr->data].infor.visited = true;
	}
	for ( dag_size_t i = _nodes.Size() - 1; i >= _num_fixed_nodes; i-- ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[_nodes[i].low].infor.visited = true;
			_nodes[_nodes[i].high].infor.visited = true;
		}
	}
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
	dag_size_t num_remove = 0;
	for ( dag_size_t i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[i].infor.mark = i - num_remove;
			_nodes[i - num_remove].var = _nodes[i].var;
			_nodes[i - num_remove].low = _nodes[_nodes[i].low].infor.mark;
			_nodes[i - num_remove].high = _nodes[_nodes[i].high].infor.mark;
		}
		else num_remove++;
	}
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		itr->data = _nodes[itr->data].infor.mark;
	}
	dag_size_t new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	for ( dag_size_t i = 0; i < _nodes.Size(); i++ ) {
		_nodes[i].infor.Init();
	}
	Shrink_Nodes();
}

void OBDD_Manager::Remove_Redundant_Nodes( vector<NodeID> & kept_nodes )
{
	DLList_Node<NodeID> * itr;
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		_nodes[itr->data].infor.visited = true;
	}
	for ( dag_size_t i = 0; i < kept_nodes.size(); i++ ) {
		_nodes[kept_nodes[i]].infor.visited = true;
	}
	for ( dag_size_t i = _nodes.Size() - 1; i >= _num_fixed_nodes; i-- ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[_nodes[i].low].infor.visited = true;
			_nodes[_nodes[i].high].infor.visited = true;
		}
	}
	dag_size_t num_remove = 0;
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
//	unsigned debug_no = 30715; // 25861;  // 30711;  // ToRemove
	for ( dag_size_t i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
/*		if ( i == debug_no ) {
			cerr << debug_no << ": ";
			_nodes[debug_no].Display( cerr );
		}*/
		if ( _nodes[i].infor.visited ) {
			_nodes[i].infor.mark = i - num_remove;
			_nodes[i - num_remove].var = _nodes[i].var;
			_nodes[i - num_remove].low = _nodes[_nodes[i].low].infor.mark;
			_nodes[i - num_remove].high = _nodes[_nodes[i].high].infor.mark;
		}
		else num_remove++;
	}
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		itr->data = _nodes[itr->data].infor.mark;
	}
	for ( dag_size_t i = 0; i < kept_nodes.size(); i++ ) {
		assert( _nodes[kept_nodes[i]].infor.Marked() );
		kept_nodes[i] = _nodes[kept_nodes[i]].infor.mark;
	}
	dag_size_t new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	for ( dag_size_t i = 0; i < _nodes.Size(); i++ ) _nodes[i].infor.Init();
	_hash_memory = _nodes.Memory();
}

dag_size_t OBDD_Manager::Num_Nodes( const Diagram & bdd )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() < 2 ) return 1;
	else if ( bdd.Root() < _num_fixed_nodes ) return 3;
	_node_stack[0] = bdd.Root();
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		BDD_Node & topn = _nodes[top];
		if ( Is_Const( top ) ) continue;
		if ( !_nodes[topn.low].infor.visited ) {
			_node_stack[num_node_stack++] = topn.low;
			_nodes[topn.low].infor.visited = true;
			_visited_nodes.push_back( topn.low );
		}
		if ( !_nodes[topn.high].infor.visited ) {
			_node_stack[num_node_stack++] = topn.high;
			_nodes[topn.high].infor.visited = true;
			_visited_nodes.push_back( topn.high );
		}
	}
	dag_size_t node_size = _visited_nodes.size() + 1;  // 1 denotes the root
	for ( const NodeID & n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	_visited_nodes.clear();
	return node_size;
}

dag_size_t OBDD_Manager::Num_Edges( const Diagram & bdd )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() < 2 ) return 0;
	else if ( bdd.Root() < _num_fixed_nodes ) return 2;
	_node_stack[0] = bdd.Root();
	unsigned num_node_stack = 1;
	dag_size_t result = 0;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		BDD_Node & topn = _nodes[top];
		if ( Is_Const( top ) ) continue;
		result += 2;
		if ( !_nodes[topn.low].infor.visited ) {
			_node_stack[num_node_stack++] = topn.low;
			_nodes[topn.low].infor.visited = true;
			_visited_nodes.push_back( topn.low );
		}
		if ( !_nodes[topn.high].infor.visited ) {
			_node_stack[num_node_stack++] = topn.high;
			_nodes[topn.high].infor.visited = true;
			_visited_nodes.push_back( topn.high );
		}
	}
	for ( const NodeID & n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	_visited_nodes.clear();
	return result;
}

bool OBDD_Manager::Entail_Clause( const Diagram & bdd, Clause & clause )
{
	assert( Contain( bdd ) );
	unsigned i;
	for ( i = 0; i < clause.Size(); i++ ) {
		if ( Lit_SAT( clause[i] ) ) {
			break;
		}
		_assignment[clause[i].Var()] = clause[i].NSign();
	}
	bool result;
	if ( i < clause.Size() ) result = true;
	else result = !Decide_SAT_Under_Assignment( bdd.Root() );
	for ( i--; i != (unsigned) -1; i-- ) {
		_assignment[clause[i].Var()] = lbool::unknown;
	}
	return result;
}

bool OBDD_Manager::Decide_SAT_Under_Assignment( NodeID root )
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
			NodeID ch = topn.Ch( _assignment[topn.var] );
			if ( !_nodes[ch].infor.Marked() ) {
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
					else if ( _nodes[topn.high].infor.Marked() ) { // ch[1] may be a descendant of ch[0]
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
		_nodes[i + i].infor.Unmark();
		_nodes[i + i + 1].infor.Unmark();
	}
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.Unmark();
	}
	_visited_nodes.clear();
	return result;
}

bool OBDD_Manager::Entail_CNF( const Diagram & bdd, CNF_Formula & cnf )
{
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		if ( !Entail_Clause( bdd, *itr ) ) return false;
	}
	return true;
}

bool OBDD_Manager::Decide_SAT( const Diagram & bdd, const vector<Literal> & assignment )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) return false;
	unsigned i;
	Label_Value( ~assignment.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( assignment[i] ); i++ ) {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
	}
	Un_Label_Value( assignment.back() );
	bool result;
	if ( Lit_UNSAT( assignment[i] ) ) result = 0;
	else {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
		result = Decide_SAT_Under_Assignment( bdd.Root() );
	}
	return result;
}

bool OBDD_Manager::Decide_Valid_With_Condition( const Diagram & bdd, const vector<Literal> & term )
{
	assert( Contain( bdd ) );
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	bool result;
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[OBDD_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	else {
		_assignment[term[i].Var()] = term[i].Sign();
		result = Decide_Valid_Under_Assignment( bdd.Root() );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return result;
}

bool OBDD_Manager::Decide_Valid_Under_Assignment( NodeID root )
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
			_nodes[i + i].infor.mark = 0;
			_nodes[i + i + 1].infor.mark = 0;
		}
	}
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len ) {
		BDD_Node & topn = _nodes[_path[path_len - 1]];
		if ( Var_Decided( topn.var ) ) {
			if ( !_nodes[topn.Ch(_assignment[topn.var])].infor.Marked() ) {
				_path[path_len] = topn.Ch(_assignment[topn.var]);
				_path_mark[path_len++] = 0;
			}
			else {
				topn.infor.mark = _nodes[topn.Ch(_assignment[topn.var])].infor.mark;
				_visited_nodes.push_back( _path[--path_len] );
			}
		}
		else {
			switch ( _path_mark[path_len - 1] ) {
				case 0:
					if ( EITHOR_ZERO( _nodes[topn.low].infor.mark, _nodes[topn.high].infor.mark ) ) {
						topn.infor.mark = 0;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( BOTH_X( _nodes[topn.low].infor.mark, _nodes[topn.high].infor.mark, 1 ) ) {
						topn.infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( _nodes[topn.low].infor.mark == 1 ) {
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
					if ( _nodes[topn.low].infor.mark == 0 ) {
						topn.infor.mark = 0;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else if ( _nodes[topn.high].infor.Marked() ) { // ch[1] may be a descendant of ch[0]
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
		_nodes[i + i].infor.Unmark();
		_nodes[i + i + 1].infor.Unmark();
	}
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.Unmark();
	}
	_visited_nodes.clear();
	return result;
}

BigInt OBDD_Manager::Count_Models( const Diagram & bdd )
{
	assert( Contain( bdd ) );
	unsigned num_vars = NumVars( _max_var );
	BigInt result;
	if ( Is_Fixed( bdd.Root() ) ) {
		if ( bdd.Root() == NodeID::bot ) return 0;
		result.Assign_2exp( num_vars - ( bdd.Root() != NodeID::top ) );
		return result;
	}
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigInt * results = new BigInt [bdd.Root() + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.mark = num_vars;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.mark = num_vars;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
//		cerr << top << ": ";
//		topn.Display( cerr );
		if ( topn.infor.Marked() ) {
			num_node_stack--;
		}
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			num_node_stack--;
			BDD_Node & low = _nodes[topn.low];
			BDD_Node & high = _nodes[topn.high];
			if ( low.infor.mark < high.infor.mark ) {
				results[top] = results[topn.high];
				results[top].Mul_2exp( high.infor.mark - low.infor.mark );
				results[top] += results[topn.low];
				topn.infor.mark = low.infor.mark - 1;
			}
			else {
				results[top] = results[topn.low];
				results[top].Mul_2exp( low.infor.mark - high.infor.mark );
				results[top] += results[topn.high];
				topn.infor.mark = high.infor.mark - 1;
			}
			if ( DEBUG_OFF ) {
				cerr << "results[" << topn.low << "] = " << results[topn.low] << " * 2 ^ " << _nodes[topn.low].infor.mark << endl;
				cerr << "results[" << topn.high << "] = " << results[topn.high] << " * 2 ^ " << _nodes[topn.high].infor.mark << endl;
				cerr << "results[" << top << "] = " << results[top] << " * 2 ^ " << topn.infor.mark << endl;
			}
			_visited_nodes.push_back( top );
		}
	}
	result = results[bdd.Root()];
	result.Mul_2exp( _nodes[bdd.Root()].infor.mark );
	_nodes[NodeID::bot].infor.Unmark();
	_nodes[NodeID::top].infor.Unmark();
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.Unmark();
	}
	_visited_nodes.clear();
	delete [] results;
	return result;
}

BigFloat OBDD_Manager::Count_Models( const Diagram & bdd, const vector<double> & weights )
{
	assert( Contain( bdd ) );
	unsigned num_vars = NumVars( _max_var );
	BigFloat result;
	if ( Is_Fixed( bdd.Root() ) ) {
		if ( bdd.Root() == NodeID::bot ) return 0;
		result.Assign_2exp( num_vars - ( bdd.Root() != NodeID::top ) );
		return result;
	}
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigFloat * results = new BigFloat [bdd.Root() + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.visited = true;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		results[i] = weights[Node2Literal( i )];
		_nodes[i].infor.visited = true;
	}
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			Literal lo( topn.var, false ), hi( topn.var, true );
			results[top].Weighted_Sum( weights[lo], results[topn.low], weights[hi], results[topn.high] );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
		}
	}
	result = results[bdd.Root()];
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	delete [] results;
	return result;
}

BigInt OBDD_Manager::Count_Models( const Diagram & bdd, const vector<Literal> & assignment )
{
	assert( Contain( bdd ) );
	unsigned i, size = 0;
	Label_Value( ~assignment.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( assignment[i] ); i++ ) {
		size += !Lit_SAT( assignment[i] );
		_assignment[assignment[i].Var()] = assignment[i].Sign();
	}
	Un_Label_Value( assignment.back() );
	BigInt result;
	if ( Lit_UNSAT( assignment[i] ) ) result = 0;
	else {
		size += !Lit_SAT( assignment[i] );
		_assignment[assignment[i].Var()] = assignment[i].Sign();
		result = Count_Models_Under_Assignment( bdd.Root(), size );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[assignment[i].Var()] = lbool::unknown;
	}
	return result;
}

BigInt OBDD_Manager::Count_Models_Under_Assignment( NodeID root, unsigned assignment_size )
{
	unsigned num_vars = NumVars( _max_var ) - assignment_size;
	BigInt result;
	if ( Is_Const( root ) ) {
		if ( root == NodeID::bot ) result = 0;
		else result.Assign_2exp( num_vars );
		return result;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigInt * results = new BigInt [root + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.mark = num_vars;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.mark = num_vars;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
//		cerr << top << ": ";
//		topn.Display( cerr );
		if ( topn.infor.Marked() ) {
			num_node_stack--;
		}
		else if ( Var_Decided( Variable(topn.var) ) ) {
			NodeID child = _assignment[topn.var] == false ? topn.low : topn.high;
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = child;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				results[top] = results[child];
				topn.infor.mark = _nodes[child].infor.mark;
				_visited_nodes.push_back( top );
				if ( DEBUG_OFF ) {
					cerr << "results[" << child << "] = " << results[child] << " * 2 ^ " << _nodes[child].infor.mark << endl;
					cerr << "results[" << top << "] = " << results[top] << " * 2 ^ " << topn.infor.mark << endl;
				}
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.low;
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.high;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				BDD_Node & low = _nodes[topn.low];
				BDD_Node & high = _nodes[topn.high];
				if ( low.infor.mark < high.infor.mark ) {
					results[top] = results[topn.high];
					results[top].Mul_2exp( high.infor.mark - low.infor.mark );
					results[top] += results[topn.low];
					topn.infor.mark = low.infor.mark - 1;
				}
				else {
					results[top] = results[topn.low];
					results[top].Mul_2exp( low.infor.mark - high.infor.mark );
					results[top] += results[topn.high];
					topn.infor.mark = high.infor.mark - 1;
				}
				if ( DEBUG_OFF ) {
					cerr << "results[" << topn.low << "] = " << results[topn.low] << " * 2 ^ " << _nodes[topn.low].infor.mark << endl;
					cerr << "results[" << topn.high << "] = " << results[topn.high] << " * 2 ^ " << _nodes[topn.high].infor.mark << endl;
					cerr << "results[" << top << "] = " << results[top] << " * 2 ^ " << topn.infor.mark << endl;
				}
				_visited_nodes.push_back( top );
			}
		}
	}
	result = results[root];
	result.Mul_2exp( _nodes[root].infor.mark );
	_nodes[NodeID::bot].infor.Unmark();
	_nodes[NodeID::top].infor.Unmark();
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.Unmark();
	}
	_visited_nodes.clear();
	delete [] results;
	return result;
}

BigInt OBDD_Manager::Count_Models_With_Condition( const Diagram & bdd, const vector<Literal> & term )
{
	assert( Contain( bdd ) );
	unsigned i, size = 0;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		size += !Lit_SAT( term[i] );
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	BigInt result;
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[OBDDC_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	else {
		size += !Lit_SAT( term[i] );
		_assignment[term[i].Var()] = term[i].Sign();
		result = Count_Models_Under_Assignment( bdd.Root(), size );
		result.Mul_2exp( size );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return result;
}

BigFloat OBDD_Manager::Count_Models_With_Condition( const Diagram & bdd, const vector<double> & weights, const vector<Literal> & term )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) return 0;
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[OBDDC_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	_assignment[term[i].Var()] = term[i].Sign();
	vector<BigFloat> results( bdd.Root() + 1 );
	Mark_Models_Under_Assignment( bdd.Root(), weights, results );
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return results[bdd.Root()];
}

void OBDD_Manager::Mark_Models_Under_Assignment( NodeID root, const vector<double> & weights, vector<BigFloat> & results )
{
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.visited = true;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
//		cerr << top << ": ";
//		topn.Display( cerr );
		if ( topn.infor.visited ) num_node_stack--;
		else if ( Var_Decided( topn.var ) ) {
			NodeID child = topn.Ch(_assignment[topn.var]);
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = child;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				results[top] = results[child];
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.low;
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.high;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				Literal lo( topn.var, false ), hi( topn.var, true );
				results[top].Weighted_Sum( weights[lo], results[topn.low], weights[hi], results[topn.high] );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
			}
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
}

void OBDD_Manager::Mark_Models( const Diagram & bdd, vector<BigFloat> & results )
{
	assert( Contain( bdd ) );
	_node_stack[0] = bdd.Root();
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
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			results[top] = results[topn.low];
			results[top] += results[topn.high];
			results[top].Div_2exp( 1 );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
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

void OBDD_Manager::Probabilistic_Model( const Diagram & bdd, vector<float> & prob_values )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) {
		cerr << "ERROR[OBDD_Manager]: invalid probabilistic model!" << endl;
		assert( bdd.Root() != NodeID::bot );
	}
	else if ( bdd.Root() == NodeID::top ) return;
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	unsigned num_vars = NumVars( _max_var );
	BigFloat * results = new BigFloat [bdd.Root() + 1];
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
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			results[top] = results[topn.low];
			results[top] += results[topn.high];
			results[top].Div_2exp( 1 );
			prob_values[top] = Normalize( results[topn.low], results[topn.high] );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
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

void OBDD_Manager::Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	vector<BigFloat> model_values( bdd.Root() + 1 );
	Mark_Models( bdd, model_values );
	for ( vector<bool> & current_sample: samples ) {
		Uniformly_Sample( rand_gen, bdd.Root(), current_sample, model_values );
	}
}

void OBDD_Manager::Uniformly_Sample( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & counts )
{
	sample.resize( _max_var + 1 );
	while ( root != NodeID::top ) {
		BDD_Node & topn = _nodes[root];
		double prob = Normalize( counts[topn.low], counts[topn.high] );
		bool b = rand_gen.Generate_Bool( prob );
		sample[topn.var] = b;
		_var_seen[topn.var] = true;
		root = topn.Ch(b);
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		if ( !_var_seen[x] ) {
			sample[x] = rand_gen.Generate_Bool( 0.5 );
		}
		else _var_seen[x] = false;
	}
}

void OBDD_Manager::Mark_Models( Diagram & bdd, const vector<double> & weights, vector<BigFloat> & results )
{
	assert( Contain( bdd ) );
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.visited = true;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		results[i] = weights[Node2Literal( i )];
		_nodes[i].infor.visited = true;
	}
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			Literal lo( topn.var, false ), hi( topn.var, true );
			results[top].Weighted_Sum( weights[lo], results[topn.low], weights[hi], results[topn.high] );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
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

void OBDD_Manager::Probabilistic_Model( Diagram & bdd, const vector<double> & weights, vector<double> & prob_values )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) {
		cerr << "ERROR[OBDDC_Manager]: invalid probabilistic model!" << endl;
		assert( bdd.Root() != NodeID::bot );
	}
	else if ( bdd.Root() == NodeID::top ) return;
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigFloat * results = new BigFloat [bdd.Root() + 1];
	results[NodeID::bot] = 0;
	_nodes[NodeID::bot].infor.visited = true;
	results[NodeID::top] = 1;
	_nodes[NodeID::top].infor.visited = true;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		results[i] = weights[Node2Literal( i )];
		_nodes[i].infor.visited = true;
	}
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			_node_stack[num_node_stack] = topn.low;
			_node_mark_stack[num_node_stack++] = true;
			_node_stack[num_node_stack] = topn.high;
			_node_mark_stack[num_node_stack++] = true;
		}
		else {
			Literal lo( topn.var, false ), hi( topn.var, true );
			results[top].Weighted_Sum( weights[lo], results[topn.low], weights[hi], results[topn.high] );
			BigFloat right_result = results[topn.high];
			right_result *= weights[hi];
			prob_values[top] = Ratio( right_result, results[top] );
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
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

void OBDD_Manager::Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, const vector<double> & weights, vector<vector<bool>> & samples )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	vector<BigFloat> model_values( bdd.Root() + 1 );
	Mark_Models( bdd, weights, model_values );
	for ( vector<bool> & current_sample: samples ) {
		Uniformly_Sample( rand_gen, bdd.Root(), current_sample, model_values );
	}
}

void OBDD_Manager::Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples, const vector<Literal> & assignment )
{
	assert( Contain( bdd ) );
	unsigned i;
	Label_Value( ~assignment.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( assignment[i] ); i++ ) {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
	}
	Un_Label_Value( assignment.back() );
	BigInt result;
	if ( !Lit_UNSAT( assignment[i] ) ) {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
		vector<BigFloat> model_values( bdd.Root() + 1 );
		Mark_Models_Under_Assignment( bdd.Root(), model_values );
		if ( model_values[bdd.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, bdd.Root(), current_sample, model_values );
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[assignment[i].Var()] = lbool::unknown;
	}
}

void OBDD_Manager::Mark_Models_Under_Assignment( NodeID root, vector<BigFloat> & results )
{
	unsigned num_vars = NumVars( _max_var );
	results[NodeID::bot] = 0;
	results[NodeID::top].Assign_2exp( num_vars );
	if ( Is_Const( root ) ) return;
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
//		cerr << top << ": ";
//		topn.Display( cerr );
		if ( topn.infor.visited ) num_node_stack--;
		else if ( Var_Decided( topn.var ) ) {
			NodeID child = topn.Ch( _assignment[topn.var] );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = child;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				results[top] = results[child];
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				if ( DEBUG_OFF ) {
					cerr << "results[" << child << "] = " << results[child] << endl;
					cerr << "results[" << top << "] = " << results[top] << endl;
				}
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.low;
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.high;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				results[top] = results[topn.low];
				results[top] += results[topn.high];
				results[top].Div_2exp( 1 );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				if ( DEBUG_OFF ) {
					cerr << "results[" << topn.low << "] = " << results[topn.low] << endl;
					cerr << "results[" << topn.high << "] = " << results[topn.high] << endl;
					cerr << "results[" << top << "] = " << results[top] << endl;
				}
			}
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
}

void OBDD_Manager::Uniformly_Sample_Under_Assignment( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & counts )
{
	sample.resize( _max_var + 1 );
	while ( root != NodeID::top ) {
		BDD_Node & topn = _nodes[root];
		bool b;
		if ( Var_Decided( topn.var ) ) b = ( _assignment[topn.var] == true );
		else {
			double prob = Normalize( counts[topn.low], counts[topn.high] );
			b = rand_gen.Generate_Bool( prob );
		}
		sample[topn.var] = b;
		_var_seen[topn.var] = true;
		root = topn.Ch(b);
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		if ( !_var_seen[x] ) {
			if ( Var_Decided( x ) ) sample[x] = ( _assignment[x] == true );
			else sample[x] = rand_gen.Generate_Bool( 0.5 );
		}
		else _var_seen[x] = false;
	}
}

void OBDD_Manager::Uniformly_Sample_With_Condition( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples, const vector<Literal> & term )
{
	if ( bdd.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	BigInt result;
	if ( !Lit_UNSAT( term[i] ) ) {
		_assignment[term[i].Var()] = term[i].Sign();
		vector<BigFloat> model_values( bdd.Root() + 1 );
		Mark_Models_Under_Assignment( bdd.Root(), model_values );
		if ( model_values[bdd.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, bdd.Root(), current_sample, model_values );
			for ( unsigned j = 0; j <= i; j++ ) {
				current_sample[term[j].Var()] = rand_gen.Generate_Bool( 0.5 );
			}
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
}

void OBDD_Manager::Uniformly_Sample_With_Condition( Random_Generator & rand_gen, Diagram & bdd, const vector<double> & weights, vector<vector<bool>> & samples, const vector<Literal> & term )
{
	assert( Contain( bdd ) );
	if ( bdd.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	BigInt result;
	if ( !Lit_UNSAT( term[i] ) ) {
		_assignment[term[i].Var()] = term[i].Sign();
		vector<BigFloat> model_values( bdd.Root() + 1 );
		Mark_Models_Under_Assignment( bdd.Root(), weights, model_values );
		if ( model_values[bdd.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, bdd.Root(), current_sample, model_values );
			for ( unsigned j = 0; j <= i; j++ ) {
				current_sample[term[j].Var()] = rand_gen.Generate_Bool( 0.5 );
			}
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
}

bool OBDD_Manager::Entail( const Diagram & left, const Diagram & right )
{
	assert( Contain( left ) && Contain( right ) );
	Binary_Map<NodeID, NodeID, bool> op_table;
	Binary_Map_Node<NodeID, NodeID, bool> op_table_node;
	_path[0] = left.Root();
	_node_stack[0] = right.Root();
	_path_mark[0] = 0;
	dag_size_t * c_stack = new dag_size_t [2 * _max_var + 2];  // c denotes cache
	unsigned path_len = 1;
	bool * r_stack = new bool [2 * _max_var + 2];  // r denotes result
	unsigned num_r_stack = 0;
	while ( path_len > 0 ) {
		op_table_node.left = _path[path_len - 1];
		op_table_node.right  = _node_stack[path_len - 1];
		if ( op_table_node.left == NodeID::bot || op_table_node.right == NodeID::top ) {
			r_stack[num_r_stack++] = true;
			path_len--;
		}
		else if ( op_table_node.left == NodeID::top || op_table_node.right == NodeID::bot ) {
			r_stack[num_r_stack++] = false;
			path_len--;
		}
		else if ( _path_mark[path_len - 1] == 0 ) {
			c_stack[path_len - 1] = op_table.Hit( op_table_node );
			if ( op_table.Hit_Successful() ) {
				r_stack[num_r_stack++] = op_table[c_stack[path_len - 1]].result;
				path_len--;
				continue;
			}
			_path_mark[path_len - 1]++;  // NOTE: indicate that this case is computed
			if ( Var_LT( _nodes[op_table_node.left].var, _nodes[op_table_node.right].var ) ) {
				_path[path_len] = _nodes[op_table_node.left].low;
				_node_stack[path_len] = op_table_node.right;
				_path_mark[path_len++] = 0;
			}
			else if ( Var_LT( _nodes[op_table_node.right].var, _nodes[op_table_node.left].var ) ) {
				_path[path_len] = op_table_node.left;
				_node_stack[path_len] = _nodes[op_table_node.right].low;
				_path_mark[path_len++] = 0;
			}
			else {
				_path[path_len] = _nodes[op_table_node.left].low;
				_node_stack[path_len] = _nodes[op_table_node.right].low;
				_path_mark[path_len++] = 0;
			}
		}
		else if ( _path_mark[path_len - 1] == 1 ) {
			if ( r_stack[num_r_stack - 1] == false ) {
				op_table[c_stack[path_len - 1]].result = false;
				path_len--;
				continue;
			}
			_path_mark[path_len - 1]++;  // NOTE: indicate that this case is computed
			if ( Var_LT( _nodes[op_table_node.left].var, _nodes[op_table_node.right].var ) ) {
				_path[path_len] = _nodes[op_table_node.left].high;
				_node_stack[path_len] = op_table_node.right;
				_path_mark[path_len++] = 0;
			}
			else if ( Var_LT( _nodes[op_table_node.right].var, _nodes[op_table_node.left].var ) ) {
				_path[path_len] = op_table_node.left;
				_node_stack[path_len] = _nodes[op_table_node.right].high;
				_path_mark[path_len++] = 0;
			}
			else {
				_path[path_len] = _nodes[op_table_node.left].high;
				_node_stack[path_len] = _nodes[op_table_node.right].high;
				_path_mark[path_len++] = 0;
			}
		}
		else {
			num_r_stack--, path_len--;
			assert( r_stack[num_r_stack - 1] );
			r_stack[num_r_stack - 1] = r_stack[num_r_stack];
			op_table[c_stack[path_len]].result = r_stack[num_r_stack - 1];
		}
	}
	bool result = r_stack[0];
	delete [] c_stack;
	delete [] r_stack;
	return result;
}

Diagram OBDD_Manager::Convert( Clause & clause )
{
	if ( clause.Size() == 0 ) return Generate_Diagram( NodeID::bot );
	assert( clause[0] <= 2 * _max_var + 1 );
	if ( clause.Size() == 1 ) return Generate_Diagram( NodeID::literal( clause[0] ) );
	clause.Sort( _var_order.Rank() );
	unsigned i, len;
	for ( i = len = 1; i < clause.Size(); i++ ) {
		assert( Lit_LT( clause[len-1], clause[i] ) || clause[len-1].Var() == clause[i].Var() );
		if ( clause[len-1] == clause[i] ) continue;
		if ( clause[len-1] == ~clause[i] ) break;
		clause[len++] = clause[i];
	}
	if ( i < clause.Size() ) return Generate_Diagram( NodeID::top );
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
	return Generate_Diagram( root );
}

Diagram OBDD_Manager::Convert( CNF_Formula & cnf )
{
	if ( cnf.Num_Clauses() == 0 ) return Generate_Diagram( NodeID::top );
	Diagram root = Convert( cnf[0] );
	for ( unsigned i = 1; i < cnf.Num_Clauses(); i++ ) {
		Diagram inc = Convert( cnf[i] );
		root = Conjoin( root, inc );
	}
	return root;
}

Diagram OBDD_Manager::Conjoin( const Diagram & left, const Diagram & right )
{
	assert( Contain( left ) && Contain( right ) );
	Binary_Map_Node<NodeID, NodeID, NodeID> op_table_node;
	_node_stack[0] = left.Root();
	_path[0] = right.Root();
	_node_mark_stack[0] = 1;
	unsigned num_n_stack = 1;
	_num_result_stack = 0;
	dag_size_t * c_stack = new dag_size_t [2 * _max_var + 2];  // c denotes cache
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
			dag_size_t old_size = _op_table.Size();
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
	return Generate_Diagram( _result_stack[0] );
}

Diagram OBDD_Manager::Disjoin( const Diagram & left, const Diagram & right )
{
	assert( Contain( left ) && Contain( right ) );
	Binary_Map_Node<NodeID, NodeID, NodeID> op_table_node;
	_node_stack[0] = left.Root();
	_path[0] = right.Root();
	_node_mark_stack[0] = 1;
	unsigned num_n_stack = 1;
	_num_result_stack = 0;
	dag_size_t * c_stack = new dag_size_t [2 * _max_var + 2];  // c denotes cache
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
			dag_size_t old_size = _op_table.Size();
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
	return Generate_Diagram( _result_stack[0] );
}

Diagram OBDD_Manager::Negate( const Diagram & bdd )
{
	assert( Contain( bdd ) );
	if ( Is_Fixed( bdd.Root() ) ) {
		dag_size_t neg = bdd.Root();
		neg = neg ^ 0x01;
		return Generate_Diagram( NodeID( neg ) );
	}
	_nodes[NodeID::bot].infor.mark = NodeID::top;
	_nodes[NodeID::top].infor.mark = NodeID::bot;
	_node_stack[0] = bdd.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDD_Node & topn = _nodes[top];
//		cerr << top << ": ";
//		topn.Display( cerr );
		if ( topn.infor.Marked() ) num_node_stack--;
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.low;
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.high;
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				num_node_stack--;
				dag_size_t low = _nodes[topn.low].infor.mark;
				dag_size_t high = _nodes[topn.high].infor.mark;
				Decision_Node dnode( topn.var, low, high );
				topn.infor.mark = Push_Node( dnode );
				_visited_nodes.push_back( top );
			}
		}
	}
	Diagram result = Generate_Diagram( _nodes[bdd.Root()].infor.mark );
	_nodes[NodeID::bot].infor.Unmark();
	_nodes[NodeID::top].infor.Unmark();
	for ( dag_size_t i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.Unmark();
	}
	_visited_nodes.clear();
	return result;
}

EPCCL_Theory * OBDD_Manager::Convert_EPCCL( const Diagram & bdd )
{
	assert( Contain( bdd ) );
	EPCCL_Theory * cnf = new EPCCL_Theory( _max_var );
	Big_Clause clause( _max_var );
	if ( bdd.Root() == NodeID::bot ) {
		clause.Resize( 1 );
		clause[0] = Literal::start;
		cnf->Add_Clause( clause );
		clause[1] = Literal::start_neg;
		cnf->Add_Clause( clause );
		return cnf;
	}
	if ( bdd.Root() == NodeID::top ) {
		return cnf;
	}
	unsigned i;
	_path[0] = bdd.Root();
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
	out << "Variable order: ";
	_var_order.Display( out );
	out << "Number of nodes: " << _nodes.Size() << endl;
	out << "0:\t F - -" << endl;
	out << "1:\t T - -" << endl;
	for ( dag_size_t i = 2; i < _nodes.Size(); i++ ) {
		out << i << ":\t " << _nodes[i].var << ' ' << _nodes[i].low << ' ' << _nodes[i].high << endl;
	}
}

void OBDD_Manager::Display_dot( ostream & out )
{
	out << "digraph DD {" << endl;
	out << "size = \"7.5,10\"" << endl
		<< "center = true" << endl;
	out << "  node_0 [label=F,shape=square]" << endl;  //⊥
	out << "  node_1 [label=T,shape=square]" << endl;
	for ( dag_size_t i = 2; i < _nodes.Size(); i++ ) {
		out << "  node_" << i << "[label=" << _nodes[i].var << ",shape=circle] " << endl;
		out << "  node_" << i << " -> " << "node_" << _nodes[i].low << " [style = dotted]" << endl;
		out << "  node_" << i << " -> " << "node_" << _nodes[i].high << " [style = solid]" << endl;
	}
	out << "}" << endl;
}

void OBDD_Manager::Display_OBDD_dot( ostream & out, Diagram & bdd )
{
	assert( Contain( bdd ) );
	out << "digraph DD {" << endl;
	out << "size = \"7.5,10\"" << endl
		<< "center = true" << endl;
	if ( Is_Fixed( bdd.Root() ) ) {
		if ( bdd.Root() == NodeID::bot ) out << "  node_0 [label=F,shape=square]" << endl;  //⊥
		else out << "  node_1 [label=T,shape=square]" << endl;
		out << "}" << endl;
		return;
	}
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_node_stack[0] = bdd.Root();
	_nodes[bdd.Root()].infor.visited = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		BDD_Node & topn = _nodes[top];
		if ( !_nodes[topn.high].infor.visited ) {
			_node_stack[num_node_stack++] = topn.high;
			_nodes[topn.high].infor.visited = true;
		}
		if ( !_nodes[topn.low].infor.visited ) {
			_node_stack[num_node_stack++] = topn.low;
			_nodes[topn.low].infor.visited = true;
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	out << "  node_0 [label=F,shape=square]" << endl;  //⊥
	_nodes[NodeID::top].infor.visited = false;
	out << "  node_1 [label=T,shape=square]" << endl;
	for ( dag_size_t i = 2; i <= bdd.Root(); i++ ) {
		if ( !_nodes[i].infor.visited ) continue;
		_nodes[i].infor.visited = false;
		out << "  node_" << i << "[label=" << _nodes[i].var << ",shape=circle] " << endl;
		out << "  node_" << i << " -> " << "node_" << _nodes[i].low << " [style = dotted]" << endl;
		out << "  node_" << i << " -> " << "node_" << _nodes[i].high << " [style = solid]" << endl;
	}
	out << "}" << endl;
}


}
