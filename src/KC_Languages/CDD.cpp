#include "CDD.h"


namespace KCBox {


CDD_Manager::CDD_Manager( Variable max_var, unsigned estimated_node_num ):
Diagram_Manager( max_var ),
_nodes( 2 * estimated_node_num )
{
	Allocate_and_Init_Auxiliary_Memory();
	Add_Fixed_Nodes();
}

void CDD_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_result_stack = new NodeID [_max_var + 2];
	_hash_memory = _nodes.Memory();
}

void CDD_Manager::Add_Fixed_Nodes()
{
	/* NOTE:
	* Previously, _nodes must be empty
	*/
	CDD_Node node;
	node.ch_size = 2;
	node.sym = CDD_SYMBOL_FALSE;
	node.ch = new NodeID [2];
	node.ch[0] = node.ch[1] = NodeID::bot;
	_nodes.Hit( node );
	node.sym = CDD_SYMBOL_TRUE;
	node.ch = new NodeID [2];
	node.ch[0] = node.ch[1] = NodeID::top;
	_nodes.Hit( node );
	/* NOTE:
	* We add <x, 1, 0> and <x, 0, 1> here
	*/
	for ( node.sym = Variable::start; node.sym <= _max_var; node.sym++ ) {
		node.ch = new NodeID [2];
		node.ch[0] = NodeID::top;
		node.ch[1] = NodeID::bot;
		_nodes.Hit( node );
		node.ch = new NodeID [2];
		node.ch[0] = NodeID::bot;
		node.ch[1] = NodeID::top;
		_nodes.Hit( node );
	}
	_num_fixed_nodes = _nodes.Size();
}

CDD_Manager::~CDD_Manager()
{
	for ( unsigned u = 0; u < _nodes.Size(); u++ ) {
		delete [] _nodes[u].ch;
	}
	Free_Auxiliary_Memory();
}

void CDD_Manager::Free_Auxiliary_Memory()
{
	delete [] _result_stack;
}

void CDD_Manager::Rename( unsigned map[] )
{
	unsigned i, j;
	for ( i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].sym == CDD_SYMBOL_DECOMPOSE ) {
			unsigned tmp = _nodes[i].ch[_nodes[i].ch_size - 1];
			_nodes[i].ch[_nodes[i].ch_size - 1] = NodeID::undef;
			for ( j = 0; _nodes[i].ch[j] < _num_fixed_nodes; j++ ) {
				_nodes[i].ch[j] = ( map[_nodes[i].ch[j] >> 1] << 1 ) + ( _nodes[i].ch[j] & 1 );
			}
			_nodes[i].ch[_nodes[i].ch_size - 1] = tmp;
			if ( _nodes[i].ch[j] < _num_fixed_nodes ) {
				_nodes[i].ch[j] = ( map[_nodes[i].ch[j] >> 1] << 1 ) + ( _nodes[i].ch[j] & 1 );
				_qsorter.Sort( _nodes[i].ch, j + 1 );
			}
			else _qsorter.Sort( _nodes[i].ch, j );
		}
		else {
			_nodes[i].sym = map[_nodes[i].sym];
		}
	}
	_nodes.Recompute_Entries();
}

void CDD_Manager::Abandon_Rename( unsigned map[] )
{
	unsigned i;
	unsigned * new_map = new unsigned [_max_var + 1];
	for ( i = Variable::start; i <= _max_var; i++ ) {
		new_map[map[i]] = i;
	}
	Rename( new_map );
	delete [] new_map;
}

void CDD_Manager::Enlarge_Max_Var( Variable max_var )
{
	unsigned i, j, old_num_fixed_nodes = _num_fixed_nodes;
	vector<CDD_Node> old_nodes;
	for ( i = 0; i < _nodes.Size(); i++ ) {
		old_nodes.push_back( _nodes[i] );
	}
	_nodes.Clear();
	for ( i = 0; i < old_num_fixed_nodes; i++ ) {
		_nodes.Hit( old_nodes[i] );
	}
	CDD_Node node;
	node.ch_size = 2;
	for ( node.sym = _max_var + 1; node.sym <= max_var; node.sym++ ) {
		node.ch = new NodeID [2];
		node.ch[0] = NodeID::top;
		node.ch[1] = NodeID::bot;
		_nodes.Hit( node );
		node.ch = new NodeID [2];
		node.ch[0] = NodeID::bot;
		node.ch[1] = NodeID::top;
		_nodes.Hit( node );
	}
	_num_fixed_nodes = _nodes.Size();
	for ( i = old_num_fixed_nodes; i < old_nodes.size(); i++ ) {
		if ( old_nodes[i].ch[0] >= old_num_fixed_nodes ) {
			old_nodes[i].ch[0] = old_nodes[i].ch[0] + _num_fixed_nodes - old_num_fixed_nodes;
		}
		if ( old_nodes[i].ch[1] >= old_num_fixed_nodes ) {
			old_nodes[i].ch[1] = old_nodes[i].ch[1] + _num_fixed_nodes - old_num_fixed_nodes;
		}
		for ( j = 2; j < old_nodes[i].ch_size; j++ ) {
			if ( old_nodes[i].ch[j] >= old_num_fixed_nodes ) {
				old_nodes[i].ch[j] = old_nodes[i].ch[j] + _num_fixed_nodes - old_num_fixed_nodes;
			}
		}
		_nodes.Hit( old_nodes[i] );
	}
	_max_var = max_var;
	Free_Auxiliary_Memory();
	Allocate_and_Init_Auxiliary_Memory();
}

unsigned CDD_Manager::Num_Nodes( NodeID root )
{
	if ( Is_Const( root ) ) return 1;
	unsigned i;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		CDD_Node & topn = _nodes[top];
		if ( Is_Const( top ) ) continue;
		if ( !_nodes[topn.ch[0]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[0];
			_nodes[topn.ch[0]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[0] );
		}
		if ( !_nodes[topn.ch[1]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[1];
			_nodes[topn.ch[1]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[1] );
		}
		for ( i = 2; i < topn.ch_size; i++ ) {
			if ( !_nodes[topn.ch[i]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[i];
				_nodes[topn.ch[i]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[i] );
			}
		}
	}
	unsigned node_size = _visited_nodes.size() + 1;  // 1 denotes the root
	for ( i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
	return node_size;
}

unsigned CDD_Manager::Num_Edges( NodeID root )
{
	if ( root < 2 ) return 0;
	else if ( root < _num_fixed_nodes ) return 2;
	unsigned i;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	unsigned result = 0;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		CDD_Node & topn = _nodes[top];
		if ( Is_Const( top ) ) continue;
		result += topn.ch_size;
		if ( !_nodes[topn.ch[0]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[0];
			_nodes[topn.ch[0]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[0] );
		}
		if ( !_nodes[topn.ch[1]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[1];
			_nodes[topn.ch[1]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[1] );
		}
		for ( i = 2; i < topn.ch_size; i++ ) {
			if ( !_nodes[topn.ch[i]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[i];
				_nodes[topn.ch[i]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[i] );
			}
		}
	}
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
	return result;
}

bool CDD_Manager::Decide_Valid_With_Condition( const CDDiagram & cdd, const vector<Literal> & term )
{
	assert( Contain( cdd ) );
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	bool result;
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[CDD_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	else {
		_assignment[term[i].Var()] = term[i].Sign();
		result = Decide_Valid_Under_Assignment( cdd.Root() );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return result;
}

bool CDD_Manager::Decide_Valid_Under_Assignment( NodeID root )
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
		CDD_Node & topn = _nodes[_path[path_len - 1]];
		if ( topn.sym <= _max_var ) {
			if ( Var_Decided( topn.Var() ) ) {
				if ( _nodes[topn.ch[_assignment[topn.sym]]].infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = topn.ch[_assignment[topn.sym]];
					_path_mark[path_len++] = 0;
				}
				else {
					topn.infor.mark = _nodes[topn.ch[_assignment[topn.sym]]].infor.mark;
					_visited_nodes.push_back( _path[--path_len] );
				}
			}
			else {
				switch ( _path_mark[path_len - 1] ) {
					case 0:
						if ( EITHOR_ZERO( _nodes[topn.ch[0]].infor.mark, _nodes[topn.ch[1]].infor.mark ) ) {
							topn.infor.mark = 0;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( BOTH_X( _nodes[topn.ch[0]].infor.mark, _nodes[topn.ch[1]].infor.mark, 1 ) ) {
							topn.infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[topn.ch[0]].infor.mark == 1 ) {
							_path[path_len] = topn.ch[1];
							_path_mark[path_len - 1] += 2;
							_path_mark[path_len++] = 0;
						}
						else {
							_path[path_len] = topn.ch[0];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 1:
						if ( _nodes[topn.ch[0]].infor.mark == 0 ) {
							topn.infor.mark = 0;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[topn.ch[1]].infor.mark != UNSIGNED_UNDEF ) { // ch[1] may be a descendant of ch[0]
							topn.infor.mark = _nodes[topn.ch[1]].infor.mark;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else {
							_path[path_len] = topn.ch[1];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 2:
						topn.infor.mark = _nodes[topn.ch[1]].infor.mark;
						_visited_nodes.push_back( _path[--path_len] );
						break;
				}
			}
		}
		else {
			if ( _path_mark[path_len - 1] == 0 ) {
				unsigned i, tmp = _nodes[topn.ch[topn.ch_size - 1]].infor.mark;
				_nodes[topn.ch[topn.ch_size - 1]].infor.mark = 0;
				for ( i = 0; _nodes[topn.ch[i]].infor.mark != 0; i++ );
				_nodes[topn.ch[topn.ch_size - 1]].infor.mark = tmp;
				if ( _nodes[topn.ch[i]].infor.mark == 0 ) {
					topn.infor.mark = 0;
					_visited_nodes.push_back( _path[path_len - 1] );
					path_len--;
				}
				else {
					_nodes[topn.ch[topn.ch_size - 1]].infor.mark = 0;
					for ( i = 0; _nodes[topn.ch[i]].infor.mark == 1; i++ );
					_nodes[topn.ch[topn.ch_size - 1]].infor.mark = tmp;
					if ( _nodes[topn.ch[i]].infor.mark == 1 ) {
						topn.infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = topn.ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else if ( _path_mark[path_len - 1] < topn.ch_size ) {
				if ( _nodes[topn.ch[_path_mark[path_len - 1] - 1]].infor.mark == 0 ) {
					topn.infor.mark = 0;
					_visited_nodes.push_back( _path[--path_len] );
				}
				else {
					unsigned i, tmp = _nodes[topn.ch[topn.ch_size - 1]].infor.mark;
					_nodes[topn.ch[topn.ch_size - 1]].infor.mark = 0;
					for ( i = _path_mark[path_len - 1]; _nodes[topn.ch[i]].infor.mark == 1; i++ );
					_nodes[topn.ch[topn.ch_size - 1]].infor.mark = tmp;
					if ( _nodes[topn.ch[i]].infor.mark == 1 ) {
						topn.infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = topn.ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else {
				topn.infor.mark = _nodes[topn.ch[topn.ch_size - 1]].infor.mark;
				_visited_nodes.push_back( _path[--path_len ] );
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

void CDD_Manager::Clear_Nodes()
{
	for ( unsigned u = _num_fixed_nodes; u < _nodes.Size(); u++ ) {
		delete [] _nodes[u].ch;
	}
	_nodes.Resize( _num_fixed_nodes );
}

void CDD_Manager::Remove_Redundant_Nodes()
{
	DLList_Node<NodeID> * itr;
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		_nodes[itr->data].infor.visited = true;
	}
	for ( unsigned i = _nodes.Size() - 1; i >= _num_fixed_nodes; i-- ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[_nodes[i].ch[0]].infor.visited = true;
			_nodes[_nodes[i].ch[1]].infor.visited = true;
			for ( unsigned j = 2; j < _nodes[i].ch_size; j++ ) {
				_nodes[_nodes[i].ch[j]].infor.visited = true;
			}
		}
	}
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
	unsigned num_remove = 0;
	for ( unsigned i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[i].infor.mark = i - num_remove;
			_nodes[i - num_remove].sym = _nodes[i].sym;
			_nodes[i - num_remove].ch = _nodes[i].ch;
			_nodes[i - num_remove].ch_size = _nodes[i].ch_size;
			_nodes[i - num_remove].ch[0] = _nodes[_nodes[i].ch[0]].infor.mark;
			_nodes[i - num_remove].ch[1] = _nodes[_nodes[i].ch[1]].infor.mark;
			for ( unsigned j = 2; j < _nodes[i].ch_size; j++ ) {
				_nodes[i - num_remove].ch[j] = _nodes[_nodes[i].ch[j]].infor.mark;
			}
		}
		else {
			num_remove++;
			delete [] _nodes[i].ch;
		}
	}
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		itr->data = _nodes[itr->data].infor.mark;
	}
	unsigned new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	for ( unsigned i = 0; i < _nodes.Size(); i++ ) {
		_nodes[i].infor.Init();
	}
	Shrink_Nodes();
}

void CDD_Manager::Remove_Redundant_Nodes( vector<NodeID> & kept_nodes )
{
//	Display( cout );
	DLList_Node<NodeID> * itr;
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		_nodes[itr->data].infor.visited = true;
	}
	for ( unsigned i = 0; i < kept_nodes.size(); i++ ) {
		_nodes[kept_nodes[i]].infor.visited = true;
	}
	for ( unsigned i = _nodes.Size() - 1; i >= _num_fixed_nodes; i-- ) {
		if ( _nodes[i].infor.visited ) {
			_nodes[_nodes[i].ch[0]].infor.visited = true;
			_nodes[_nodes[i].ch[1]].infor.visited = true;
			for ( unsigned j = 2; j < _nodes[i].ch_size; j++ ) {
				_nodes[_nodes[i].ch[j]].infor.visited = true;
			}
		}
	}
	unsigned i, num_remove = 0;
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
//	unsigned debug_no = 30715; // 25861;  // 30711;  // ToRemove
	for ( ; i < _nodes.Size(); i++ ) {
/*		if ( i == debug_no ) {
			cerr << debug_no << ": ";
			_nodes[debug_no].Display( cerr );
		}*/
		if ( _nodes[i].infor.visited ) {
			_nodes[i].infor.mark = i - num_remove;
			_nodes[i - num_remove].sym = _nodes[i].sym;
			_nodes[i - num_remove].ch = _nodes[i].ch;
			_nodes[i - num_remove].ch_size = _nodes[i].ch_size;
			_nodes[i - num_remove].ch[0] = _nodes[_nodes[i].ch[0]].infor.mark;
			_nodes[i - num_remove].ch[1] = _nodes[_nodes[i].ch[1]].infor.mark;
			for ( unsigned j = 2; j < _nodes[i].ch_size; j++ ) {
				_nodes[i - num_remove].ch[j] = _nodes[_nodes[i].ch[j]].infor.mark;
			}
		}
		else {
			num_remove++;
			delete [] _nodes[i].ch;
		}
	}
	for ( itr = _allocated_nodes.Front(); itr != _allocated_nodes.Head(); itr = _allocated_nodes.Next( itr ) ) {
		itr->data = _nodes[itr->data].infor.mark;
	}
	for ( unsigned i = 0; i < kept_nodes.size(); i++ ) {
		assert( _nodes[kept_nodes[i]].infor.mark != UNSIGNED_UNDEF );
		kept_nodes[i] = _nodes[kept_nodes[i]].infor.mark;
	}
	unsigned new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	for ( i = 0; i < _nodes.Size(); i++ ) _nodes[i].infor.Init();
	_hash_memory = _nodes.Memory();
}

void CDD_Manager::Display( ostream & out )
{
	out << "Maximum variable: " << ExtVar( _max_var ) << endl;
	Display_Nodes( out );
}

void CDD_Manager::Display_dot( ostream & out )
{
	out << "digraph DD {" << endl;
	out << "size = \"7.5,10\"" << endl
		<< "center = true" << endl;
	out << "  node_0 [label=F,shape=square]" << endl;  //⊥
	out << "  node_1 [label=T,shape=square]" << endl;
	for ( unsigned i = 2; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].sym == CDD_SYMBOL_CONJOIN ) {
			out << "  node_" << i << "[label=∧,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else if ( _nodes[i].sym == CDD_SYMBOL_DECOMPOSE ) {
			out << "  node_" << i << "[label=<∧<SUB>d</SUB>>,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else if ( _nodes[i].sym == CDD_SYMBOL_KERNELIZE ) {
			out << "  node_" << i << "[label=<∧<SUB>k</SUB>>,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else {
			out << "  node_" << i << "[label=" << _nodes[i].sym << ",shape=circle] " << endl;
			out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[0] << " [style = dotted]" << endl;
			out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[1] << " [style = solid]" << endl;
		}
	}
	out << "}" << endl;
}

void CDD_Manager::Display_Nodes( ostream & out )
{
	out << "Number of nodes: " << _nodes.Size() << endl;
	out << "0:\t" << "F 0" << endl;
	out << "1:\t" << "T 0" << endl;
	for ( unsigned i = 2; i < _nodes.Size(); i++ ) {
		out << i << ":\t";
		_nodes[i].Display( out, false );
	}
}

void CDD_Manager::Display_Stat( ostream & out )
{
	out << "Maximum variable: " << ExtVar( _max_var ) << endl;
	Display_Nodes_Stat( out );
}

void CDD_Manager::Display_Nodes_Stat( ostream & out )
{
	out << "Number of nodes: " << _nodes.Size() << endl;
	for ( unsigned i = 0; i < _nodes.Size(); i++ ) {
		out << i << ":\t";
		_nodes[i].Display( out, true );
	}
}

void CDD_Manager::Display_New_Nodes( ostream & out, unsigned & old_size )
{
	for ( ; old_size < _nodes.Size(); old_size++ ) {
		out << old_size << ":\t";
		_nodes[old_size].Display( out );
	}
}

void CDD_Manager::Display_Nodes( ostream & out, NodeID * nodes, unsigned size )
{
	for ( unsigned i = 0; i < size; i++ ) {
		out << nodes[i] << ":\t";
		_nodes[nodes[i]].Display( out );
	}
}

void CDD_Manager::Display_CDD( ostream & out, const CDDiagram & cdd )
{
	if ( Is_Fixed( cdd.Root() ) ) {
		out << cdd.Root() << ":\t";
		_nodes[cdd.Root()].Display( out );
		return;
	}
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_path[0] = cdd.Root();
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		CDD_Node & topn = _nodes[top];
		if ( _path_mark[path_len - 1] == topn.ch_size ) {
			path_len--;
			continue;
		}
		NodeID child = topn.ch[_path_mark[path_len - 1]];
		CDD_Node & childn = _nodes[child];
		_path_mark[path_len - 1]++;  // path_len will change in the following statement
		if ( !childn.infor.visited ) {
			_path[path_len] = child;
			_path_mark[path_len++] = 0;
			childn.infor.visited = true;
		}
	}
	for ( unsigned i = 0; i < cdd.Root(); i++ ) {
		if ( _nodes[i].infor.visited ) {
			out << i << ":\t";
			_nodes[i].Display( out );
			_nodes[i].infor.visited = false;
		}
	}
	out << cdd.Root() << ":\t";
	_nodes[cdd.Root()].Display( out );
	_nodes[cdd.Root()].infor.visited = false;
}

void CDD_Manager::Display_CDD_dot( ostream & out, const CDDiagram & cdd )
{
	out << "digraph DD {" << endl;
	out << "size = \"7.5,10\"" << endl
		<< "center = true" << endl;
	if ( Is_Fixed( cdd.Root() ) ) {
		if ( cdd.Root() == NodeID::bot ) out << "  node_0 [label=F,shape=square]" << endl;  //⊥
		else out << "  node_1 [label=T,shape=square]" << endl;
		out << "}" << endl;
		return;
	}
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_path[0] = cdd.Root();
	_path_mark[0] = 0;
	_nodes[cdd.Root()].infor.visited = true;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		CDD_Node & topn = _nodes[top];
		if ( _path_mark[path_len - 1] == topn.ch_size ) {
			path_len--;
			continue;
		}
		NodeID child = topn.ch[_path_mark[path_len - 1]];
		CDD_Node & childn = _nodes[child];
		_path_mark[path_len - 1]++;  // path_len will change in the following statement
		if ( !childn.infor.visited ) {
			_path[path_len] = child;
			_path_mark[path_len++] = 0;
			childn.infor.visited = true;
		}
	}
	_nodes[NodeID::bot].infor.visited = false;
	out << "  node_0 [label=F,shape=square]" << endl;  //⊥
	_nodes[NodeID::top].infor.visited = false;
	out << "  node_1 [label=T,shape=square]" << endl;
	for ( unsigned i = 2; i <= cdd.Root(); i++ ) {
		if ( !_nodes[i].infor.visited ) continue;
		_nodes[i].infor.visited = false;
		if ( _nodes[i].sym == CDD_SYMBOL_CONJOIN ) {
			out << "  node_" << i << "[label=∧,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else if ( _nodes[i].sym == CDD_SYMBOL_DECOMPOSE ) {
			out << "  node_" << i << "[label=<∧<SUB>d</SUB>>,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else if ( _nodes[i].sym == CDD_SYMBOL_KERNELIZE ) {
			out << "  node_" << i << "[label=<∧<SUB>k</SUB>>,shape=circle] " << endl;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[j] << " [style = solid]" << endl;
			}
		}
		else {
			out << "  node_" << i << "[label=" << _nodes[i].sym << ",shape=circle] " << endl;
			out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[0] << " [style = dotted]" << endl;
			out << "  node_" << i << " -> " << "node_" << _nodes[i].ch[1] << " [style = solid]" << endl;
		}
	}
	out << "}" << endl;
}


}

