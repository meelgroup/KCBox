#include "OBDD[AND].h"


namespace KCBox {


BDDC_Debug_Options OBDDC_Manager::debug_options;


OBDDC_Manager::OBDDC_Manager( istream & fin, int mode ):
_nodes( LARGE_HASH_TABLE )
{
	if ( fin.fail() ) {
		cerr << "ERROR[BDDC]: the BDDC file cannot be opened!" << endl;
		exit( 0 );
	}
	vector<unsigned> arr;
	char line[MAX_LINE];
	fin.getline( line, MAX_LINE );
	char * p = line;
	if ( !Read_String_Change( p, "Variable order:" ) ) {
		cerr << "ERROR[BDDC]: the BDDC-file does not state the variable order!" << endl;
		exit( 1 );
	}
	else {
		Exactly_Read_Unsigneds( p, arr );
		_var_order.Append( arr.begin(), arr.end() );
        fin.getline( line, MAX_LINE );
	}
	Diagram_Manager::Allocate_and_Init_Auxiliary_Memory( Variable( _var_order.Max() ) );
    Add_Fixed_Nodes();
    unsigned num_node;
	if ( sscanf( line, "Number of nodes: %u", &num_node ) != 2 ) {
		cerr << "ERROR[BDDC]: wrong BDDC-file format, no num_node!" << endl;
	}
	fin.getline( line, MAX_LINE );
	p = line;
	if ( Read_Unsigned_Change( p ) != 0 ) cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong false-node!" << endl;
	if ( *p == ':' ) p++;
	else cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong false-node!" << endl;
	if ( !String_Fuzzy_Match( p, "F 0" ) ) cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong false-node!" << endl;
	fin.getline( line, MAX_LINE );
	p = line;
	if ( Read_Unsigned_Change( p ) != 1 ) cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong true-node!" << endl;
	if ( *p == ':' ) p++;
	else cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong false-node!" << endl;
	if ( !String_Fuzzy_Match( p, "T 0" ) ) cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong true-node!" << endl;
	for ( unsigned u = 2; u < _num_fixed_nodes; u++ ) {
		Literal lit = Node2Literal( u );
		fin.getline( line, MAX_LINE );
		p = line;
		if ( Read_Unsigned_Change( p ) != u ) cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong " << u << "-node!" << endl;
		if ( *p == ':' ) p++;
		else cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong " << u << "-node!" << endl;
		arr.clear();
		Exactly_Read_Unsigneds( p, arr );
		if ( arr.size() != 4 || arr[0] != lit.Var() || arr[1] != 1 || arr[2] != 0 || arr[3] != 0 )
			cerr << "ERROR[BDDC]: wrong BDDC-file format, wrong " << u << "-node!" << endl;
	}
	for ( unsigned u = _num_fixed_nodes; u < num_node; u++ ) {
        arr.clear();
		BDDC_Node node;
		fin.getline( line, MAX_LINE );
		p = line;
		if ( Read_Unsigned_Change( p ) != u ) cerr << "ERROR[BDDC]: wrong BDDC-file format, the " << u << "th node is invalid!" << endl;
		if ( *p == ':' ) p++;
		else cerr << "ERROR[BDDC]: wrong BDDC-file format, the " << u << "th node is invalid!" << endl;
		while ( BLANK_CHAR( *p ) ) p++;
		if ( *p == 'C' ) {
			node.sym = BDDC_SYMBOL_CONJOIN;
			p++;
			Exactly_Read_Unsigneds( p, arr );
			node.ch_size = arr.size() - 1;
			if ( node.ch_size < 2 || arr[node.ch_size] != 0 )
				cerr << "ERROR[BDDC]: wrong BDDC-file format, the " << u << "th node is invalid!" << endl;
			node.ch = new NodeID [node.ch_size];
			for ( unsigned i = 0; i < node.ch_size; i++ ) node.ch[i] = arr[i];
		}
		else {
		    Exactly_Read_Unsigneds( p, arr );
			node.ch_size = arr.size() - 2;
			if ( node.ch_size != 2 || arr[3] != 0 )
				cerr << "ERROR[BDDC]: wrong BDDC-file format, the " << u << "th node is invalid!" << endl;
			node.sym = arr[0];
			node.ch = new NodeID [2];
			node.ch[0] = arr[1];
			node.ch[1] = arr[2];
		}
		_nodes.Hit( node );
	}
	Allocate_and_Init_Auxiliary_Memory();
}

OBDDC_Manager::OBDDC_Manager( OBDDC_Manager & other ):
Diagram_Manager( other._max_var ),
_nodes( other._nodes.Size() * 2 )
{
	Add_Fixed_Nodes();
	for ( unsigned u = _num_fixed_nodes; u < other._nodes.Size(); u++ ) {
		Push_New_Node( other._nodes[u] );
	}
	Allocate_and_Init_Auxiliary_Memory();
}

OBDDC_Manager::OBDDC_Manager( Variable max_var, unsigned estimated_node_num ): // _var_order is not assigned
Diagram_Manager( max_var ),
_nodes( 2 * estimated_node_num ),
_aux_rnode( Variable::start )
{
	Generate_Lexicographic_Var_Order( _max_var );
	Add_Fixed_Nodes();
	Allocate_and_Init_Auxiliary_Memory();
}

OBDDC_Manager::OBDDC_Manager( const Chain & vorder, unsigned estimated_node_num ):
Diagram_Manager( Variable( vorder.Max() ) ),
_nodes( 2 * estimated_node_num )
{
	Add_Fixed_Nodes();
	Allocate_and_Init_Auxiliary_Memory();
    _var_order = vorder;
}

OBDDC_Manager::~OBDDC_Manager()
{
	for ( unsigned u = 0; u < _nodes.Size(); u++ ) {
		delete [] _nodes[u].ch;
	}
	Free_Auxiliary_Memory();
}

void OBDDC_Manager::Reorder( const Chain & new_order )
{
    if ( _nodes.Size() > _num_fixed_nodes ) {
        cerr << "ERROR[BDDC]: cannot be Reorder with non-fixed _nodes!" << endl;
    }
	_var_order = new_order;
}

void OBDDC_Manager::Rename( unsigned map[] )
{
	unsigned i, j;
	_var_order.Rename( map );
	for ( i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].sym == BDDC_SYMBOL_CONJOIN ) {
			unsigned tmp = _nodes[i].ch[_nodes[i].ch_size - 1];
			_nodes[i].ch[_nodes[i].ch_size - 1] = UNSIGNED_UNDEF;
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

void OBDDC_Manager::Abandon_Rename( unsigned map[] )
{
	unsigned i;
	unsigned * new_map = new unsigned [_max_var + 1];
	for ( i = Variable::start; i <= _max_var; i++ ) {
		new_map[map[i]] = i;
	}
	Rename( new_map );
	delete [] new_map;
}

OBDDC_Manager * OBDDC_Manager::Copy_BDDC_Standard_Order( unsigned root )
{
	OBDDC_Manager * other = new OBDDC_Manager( _var_order, 2 * _nodes.Size() );
	if ( root < _num_fixed_nodes ) {
		return other;
	}
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
		BDDC_Node & top = _nodes[_node_stack[num_node_stack - 1]];
		if ( top.infor.mark != UNSIGNED_UNDEF ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
			if ( top.sym <= _max_var ) {
				_node_stack[num_node_stack] = top.ch[1];
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = top.ch[0];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				Sort_Children_Over_GLB_Reverse( _node_stack[num_node_stack - 1], _node_stack + num_node_stack );
				for ( unsigned i = 0; i < top.ch_size; i++ ) _node_mark_stack[num_node_stack++] = true;
			}
		}
		else {
			BDDC_Node node;
			node.sym = top.sym;
			if ( top.sym == BDDC_SYMBOL_CONJOIN ) {
				node.ch = new NodeID [top.ch_size];
				node.ch_size = top.ch_size;
				for ( unsigned i = 0; i < top.ch_size; i++ ) {
					node.ch[i] = _nodes[top.ch[i]].infor.mark;
				}
				_qsorter.Sort( node.ch, node.ch_size );
			}
			else {
				node.ch = new NodeID [2];
				node.ch_size = 2;
				node.ch[0] = _nodes[top.ch[0]].infor.mark;
				node.ch[1] = _nodes[top.ch[1]].infor.mark;
			}
			top.infor.mark = other->Push_New_Node( node );
			num_node_stack--;
		}
	}
	for ( unsigned u = 0; u <= root; u++ ) {
		_nodes[u].infor.mark = UNSIGNED_UNDEF;
	}
	return other;
}

void OBDDC_Manager::Verify_OBDDC( unsigned root )
{
	if ( root < _num_fixed_nodes ) return;
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = true;
	}
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
	    unsigned topn = _node_stack[num_node_stack - 1];
		BDDC_Node & top = _nodes[topn];
		num_node_stack--;
		if ( top.sym <= _max_var ) {
			Verify_Ordered_Decision( topn );
			BDDC_Node & ch1 = _nodes[top.ch[1]];
			BDDC_Node & ch0 = _nodes[top.ch[0]];
			if ( !ch1.infor.visited ) {
				_node_stack[num_node_stack++] = top.ch[1];
				ch1.infor.visited = true;
			}
			if ( !ch0.infor.visited ) {
				_node_stack[num_node_stack++] = top.ch[0];
				ch0.infor.visited = true;
			}
		}
		else {
			unsigned i = top.ch_size - 1;
			for ( ; i != (unsigned) -1; i-- ) {
				if ( Is_Const( top.ch[i] ) ) {
					cerr << "ERROR[BDDC]: The " << topn << "th node has a constant child!" << endl;
					assert( Is_Internal( top.ch[i] ) );
				}
				BDDC_Node & ch = _nodes[top.ch[i]];
				if ( !ch.infor.visited ) {
					_node_stack[num_node_stack++] = top.ch[i];
					ch.infor.visited = true;
				}
			}
		}
	}
	for ( unsigned i = 0; i <= root; i++ ) {
		_nodes[i].infor.visited = false;
	}
}

void OBDDC_Manager::Verify_Ordered_Decision( unsigned root )
{
	assert( _nodes[root].sym <= _max_var );
	unsigned i;
	unsigned num_node_stack = 0;
	if ( Is_Internal( _nodes[root].ch[0] ) ) _node_stack[num_node_stack++] = _nodes[root].ch[0];
	if ( Is_Internal( _nodes[root].ch[1] ) ) _node_stack[num_node_stack++] = _nodes[root].ch[1];
	while ( num_node_stack > 0 ) {
		unsigned top = _node_stack[--num_node_stack];
		if ( _nodes[top].sym <= _max_var ) {
			if ( !Var_LT( _nodes[root].sym, _nodes[top].sym ) ) {
				cerr << "ERROR[BDDC]: The variable of" << top << "th node is not less than that of the " << root << "th!" << endl;
				cerr << top << ": ";
				_nodes[top].Display( cerr );
				cerr << root << ": ";
				_nodes[root].Display( cerr );
				assert( _nodes[top].sym > _max_var || Var_LT( _nodes[root].sym, _nodes[top].sym ) );
			}
		}
		else {
			for ( i = 0; i < _nodes[top].ch_size; i++ ) {
				if ( Is_Const( _nodes[top].ch[i] ) ) {
					cerr << "ERROR[BDDC]: The " << top << "th node has a constant child!" << endl;
					assert( Is_Internal( _nodes[top].ch[i] ) );
				}
				_node_stack[num_node_stack++] = _nodes[top].ch[i];
			}
		}
	}
}

void OBDDC_Manager::Verify_ROBDDC_Finest( unsigned root )
{
	if ( root < _num_fixed_nodes ) return;
	unsigned i;
	Verify_OBDDC( root );
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = true;
	}
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
	    unsigned topn = _node_stack[--num_node_stack];
		BDDC_Node * top = &(_nodes[topn]);
		if ( top->sym <= _max_var ) {
			BDDC_Node * ch1 = &(_nodes[top->ch[1]]);
			BDDC_Node * ch0 = &(_nodes[top->ch[0]]);
			if ( top->ch[0] == top->ch[1] ) {
				cerr << "ERROR[BDDC]: The " << topn << "th node has two identical children!" << endl;
				assert( top->ch[0] != top->ch[1] );
			}
			if ( top->ch[0] == NodeID::bot || top->ch[1] == NodeID::bot ) {
                cerr << "ERROR[BDDC]: The " << topn << "th node is conjunctively decomposable, because it has a false child!" << endl;
                assert( top->ch[0] != top->ch[1] );
			}
			else if ( _nodes[top->ch[0]].sym == BDDC_SYMBOL_CONJOIN && _nodes[top->ch[1]].sym == BDDC_SYMBOL_CONJOIN ) {
				unsigned num_shared = Intersection( _nodes[top->ch[0]].ch, _nodes[top->ch[0]].ch_size, \
					_nodes[top->ch[1]].ch, _nodes[top->ch[1]].ch_size, _many_nodes );
				if ( num_shared > 0 ) {
                    cerr << "ERROR[BDDC]: The " << topn << "th node is conjunctively decomposable, because left and right share children!" << endl;
                    assert( num_shared == 0 );
				}
			}
			else if ( _nodes[top->ch[1]].sym == BDDC_SYMBOL_CONJOIN && \
				Search_Exi_Nonempty( _nodes[top->ch[1]].ch, _nodes[top->ch[1]].ch_size, top->ch[0] ) ) {
                cerr << "ERROR[BDDC]: The " << topn << "th node is decomposable, because left is a part of right!" << endl;
                assert( false );
			}
			else if ( _nodes[top->ch[0]].sym == BDDC_SYMBOL_CONJOIN && \
				Search_Exi_Nonempty( _nodes[top->ch[0]].ch, _nodes[top->ch[0]].ch_size, top->ch[1] ) ) {
                cerr << "ERROR[BDDC]: The " << topn << "th node is decomposable, because right is a part of left!" << endl;
                assert( false );
			}
			if ( !ch1->infor.visited ) {
				_node_stack[num_node_stack++] = top->ch[1];
				ch1->infor.visited = true;
			}
			if ( !ch0->infor.visited ) {
				_node_stack[num_node_stack++] = top->ch[0];
				ch0->infor.visited = true;
			}
		}
		else {
			unsigned i;
			unsigned tmp = _nodes[top->ch[top->ch_size - 1]].sym;
			_nodes[top->ch[top->ch_size - 1]].sym = BDDC_SYMBOL_CONJOIN;
			for ( i = 0; _nodes[top->ch[i]].sym != BDDC_SYMBOL_CONJOIN; i++ );
			_nodes[top->ch[top->ch_size - 1]].sym = tmp;
			if ( _nodes[top->ch[i]].sym == BDDC_SYMBOL_CONJOIN ) {
				cerr << "ERROR[BDDC]: The " << topn << "th node is not finest!" << endl;
				cerr << topn << ": ";
				top->Display( cerr );
				cerr << endl;
				cerr << top->ch[i] << ": ";
				_nodes[top->ch[i]].Display( cerr );
				cerr << endl;
				assert( top->sym != _nodes[top->ch[i]].sym );
			}
			if ( !_nodes[top->ch[0]].infor.visited ) {
				_node_stack[num_node_stack++] = top->ch[0];
				_nodes[top->ch[0]].infor.visited = true;
			}
			for ( i = 1; i < top->ch_size; i++ ) {
				if ( top->ch[i-1] >= top->ch[i] ) {
					cerr << "ERROR[BDDC]: The children of the " << topn << "th node are not sorted!" << endl;
					assert( top->ch[i-1] < top->ch[i] );
				}
				if ( !_nodes[top->ch[i]].infor.visited ) {
					_node_stack[num_node_stack++] = top->ch[i];
					_nodes[top->ch[i]].infor.visited = true;
				}
			}
		}
	}
	for ( unsigned i = 0; i <= root; i++ ) {
		_nodes[i].infor.visited = false;
	}
}

void OBDDC_Manager::Add_Fixed_Nodes()
{
	/* NOTE:
	* Previously, _nodes must be empty
	*/
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_FALSE;
	node.ch = NULL;
	node.ch_size = 0;
	_nodes.Hit( node );
	node.sym = BDDC_SYMBOL_TRUE;
	_nodes.Hit( node );
	/* NOTE:
	* We add <x, 1, 0> and <x, 0, 1> here
	*/
	node.ch_size = 2;
	for ( node.sym = Variable::start; node.sym <= _max_var; node.sym++ ) {
		node.ch = new NodeID [2];
		node.ch[0] = 1;
		node.ch[1] = 0;
		_nodes.Hit( node );
		node.ch = new NodeID [2];
		node.ch[0] = 0;
		node.ch[1] = 1;
		_nodes.Hit( node );
	}
	_num_fixed_nodes = _nodes.Size();
}

void OBDDC_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_many_nodes = new NodeID [_max_var + 1];
	_node_sets = new NodeID * [_max_var + 1];
	_node_set_sizes = new unsigned [_max_var + 1];
	_aux_rnode.Reset_Max_Var( _max_var );
	if ( debug_options.activate_running_time ) {
		running_time.Init();
	}
}

void OBDDC_Manager::Free_Auxiliary_Memory()
{
	delete [] _many_nodes;
	delete [] _node_sets;
	delete [] _node_set_sizes;
}

unsigned OBDDC_Manager::Add_Node( Rough_BDDC_Node & rnode )
{
	unsigned tmp_link;
	unsigned old_size = _nodes.Size();
    if ( debug_options.display_Decompose_Infty ) {
        cout << "rnode => ";
        if ( rnode.sym == BDDC_SYMBOL_CONJOIN ) cout << "C";
        else cout << rnode.sym;
        for ( unsigned i = 0; i < rnode.ch_size; i++ ) {
            cout << ' ' << rnode.ch[i];
        }
        cout << " 0" << endl;
    }
    if ( rnode.sym <= _max_var ) {
        Decision_Node bnode;
        bnode.var = rnode.sym;
        bnode.low = rnode.ch[0];
        bnode.high = rnode.ch[1];
        tmp_link = Decompose_Decision( bnode );
    }
    else tmp_link = Decompose_Conjunction( rnode );
    if ( debug_options.display_Decompose_Infty ) {
        cout << "result => " << tmp_link << endl;
        cout << "New _nodes:" << endl;
        for ( ; old_size < _nodes.Size(); old_size++ ) {
            cout << old_size << ": ";
            _nodes[old_size].Display( cout );
        }
    }
//	Display( cout );
    return tmp_link; // _nodes.data may be re_assigned, so "_nodes[u]" cannot be replaced by "itr"
}

NodeID OBDDC_Manager::Decompose_Decision( Decision_Node & bnode )
{
    unsigned tmp_link;
    if ( bnode.low == bnode.high ) tmp_link = bnode.low;
    else if ( Is_Const( bnode.low ) && Is_Const( bnode.high ) ) tmp_link = NodeID::literal( bnode.var, bnode.high == NodeID::top );
    else if ( bnode.low == NodeID::bot ) tmp_link = Extract_Leaf_Left_No_Check( &bnode );
    else if ( bnode.high == NodeID::bot ) tmp_link = Extract_Leaf_Right_No_Check( &bnode );
    else if ( BOTH_X( _nodes[bnode.low].sym, _nodes[bnode.high].sym, BDDC_SYMBOL_CONJOIN ) ) {
        tmp_link = Extract_Share_Semi_Check( &bnode );
    }
    else if ( _nodes[bnode.high].sym == BDDC_SYMBOL_CONJOIN && \
        Search_Exi_Nonempty( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, bnode.low ) ) {
        tmp_link = Extract_Part_Left_No_Check( &bnode );
    }
    else if ( _nodes[bnode.low].sym == BDDC_SYMBOL_CONJOIN && \
        Search_Exi_Nonempty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, bnode.high ) ) {
        tmp_link = Extract_Part_Right_No_Check( &bnode );
    }
    else tmp_link = Push_Node( bnode );
    return tmp_link;
}

unsigned OBDDC_Manager::Add_Decomposition_Node( Rough_BDDC_Node & rnode )
{
	assert( rnode.sym == BDDC_SYMBOL_CONJOIN );
	if ( rnode.ch_size == 0 ) return NodeID::top;
	else if ( rnode.ch_size == 1 ) return rnode.ch[0];
    else return Decompose_Conjunction( rnode );
}

BDDC OBDDC_Manager::Decompose_Infty( OBDD_Manager & bdd_manager, unsigned root )
{
	assert( _max_var == bdd_manager.Max_Var() );
	if ( root < _num_fixed_nodes ) return root;
	/* NOTE:
	* Under the release mode, the procedure sometimes has a bug when using the statement such as '_nodes[u].infor.mark = f();',
	* where f will update _nodes.data. We will use tmp_link to rewrite 'tmp_link = f(); _nodes[u].infor.mark = tmp_link;'
	*/
	unsigned i, tmp_link, old_size = _nodes.Size();
	Rough_BDDC_Node rnode( _max_var );
	vector<unsigned> node_links( root + 1, UNSIGNED_UNDEF );
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		node_links[ i ] = i;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
        unsigned top = _node_stack[num_node_stack - 1];
		const BDD_Node & topn = bdd_manager.Node( top );
		if ( node_links[top] != UNSIGNED_UNDEF ) num_node_stack--;
		else if ( _node_mark_stack[num_node_stack - 1] ) {
			_node_mark_stack[num_node_stack - 1] = false;
            _node_stack[num_node_stack] = topn.high;
            _node_mark_stack[num_node_stack++] = true;
            _node_stack[num_node_stack] = topn.low;
            _node_mark_stack[num_node_stack++] = true;
		}
		else {
            if ( debug_options.display_Decompose_Infty ) {
                cout << "top => ";
                cout << _node_stack[num_node_stack - 1] << ": ";
                cout << topn.var << ' ' << node_links[topn.low] << ' ' << node_links[topn.high] << endl;
            }
            Decision_Node bnode;
            bnode.var = topn.var;
            bnode.low = node_links[topn.low];
            bnode.high = node_links[topn.high];
            tmp_link = Decompose_Decision( bnode );
            node_links[top] = tmp_link; // _nodes.data may be re_assigned, so "_nodes[u]" cannot be replaced by "itr"
            if ( debug_options.display_Decompose_Infty ) {
                cout << top  << " => " << node_links[top] << endl;
                cout << "New _nodes:" << endl;
                for ( ; old_size < _nodes.Size(); old_size++ ) {
                    cout << old_size << ": ";
                    _nodes[old_size].Display( cout );
                }
            }
			num_node_stack--;
		}
	}
//	Display( cout );
	BDDC new_root = node_links[root];
	if ( debug_options.verify_Decompose_Infty ) {
		Verify_ROBDDC_Finest( new_root );
		BigInt model_num1 = bdd_manager.Count_Models( root );
		BigInt model_num2 = Count_Models( new_root );
//		model_num3.Display_DEC( cout );
		EPCCL_Theory * cnf = bdd_manager.Convert_EPCCL( root );
//		cnf->Display( cout );
		assert( model_num1 == model_num2 );
		assert( Entail_CNF( new_root, cnf ) );
		delete cnf;
	}
	return new_root;
}

NodeID OBDDC_Manager::Decompose_Conjunction( Rough_BDDC_Node & rnode )
{
    unsigned i, tmp_link;
    unsigned tmp = _nodes[rnode.ch[rnode.ch_size - 1]].sym;  // NOTE: Search NodeID::bot
    _nodes[rnode.ch[rnode.ch_size - 1]].sym = BDDC_SYMBOL_FALSE;
    for ( i = 0; _nodes[rnode.ch[i]].sym != BDDC_SYMBOL_FALSE; i++ );
    _nodes[rnode.ch[rnode.ch_size - 1]].sym = tmp;
    if ( _nodes[rnode.ch[i]].sym == BDDC_SYMBOL_FALSE )
        tmp_link = NodeID::bot;
    else {
        _aux_rnode.sym = rnode.sym;
        _aux_rnode.ch_size = 0;
        for ( i = 0; i < rnode.ch_size; i++ ) {
            if ( _nodes[rnode.ch[i]].sym != BDDC_SYMBOL_TRUE ) {
                _aux_rnode.ch[_aux_rnode.ch_size++] = rnode.ch[i];
            }
        }
        if ( _aux_rnode.ch_size == 0 ) tmp_link = NodeID::top;
        else if ( _aux_rnode.ch_size == 1 ) tmp_link = rnode.ch[0];
        else {
            _qsorter.Sort( _aux_rnode.ch, _aux_rnode.ch_size );  // ToCheck
            tmp_link = Finest( &_aux_rnode );
        }
    }
    return tmp_link;
}

NodeID OBDDC_Manager::Decompose_Conjunction( BDDC_Node * itr )
{
    unsigned i, tmp_link;
    unsigned tmp = _nodes[_nodes[itr->ch[itr->ch_size - 1]].infor.mark].sym;  // NOTE: Search NodeID::bot
    _nodes[_nodes[itr->ch[itr->ch_size - 1]].infor.mark].sym = BDDC_SYMBOL_FALSE;
    for ( i = 0; _nodes[_nodes[itr->ch[i]].infor.mark].sym != BDDC_SYMBOL_FALSE; i++ );
    _nodes[_nodes[itr->ch[itr->ch_size - 1]].infor.mark].sym = tmp;
    if ( _nodes[_nodes[itr->ch[i]].infor.mark].sym == BDDC_SYMBOL_FALSE )
        tmp_link = NodeID::bot;
    else {
        _aux_rnode.sym = itr->sym;
        _aux_rnode.ch_size = 0;
        for ( i = 0; i < itr->ch_size; i++ ) {
            if ( _nodes[_nodes[itr->ch[i]].infor.mark].sym != BDDC_SYMBOL_TRUE ) {
                _aux_rnode.ch[_aux_rnode.ch_size++] = _nodes[itr->ch[i]].infor.mark;
            }
        }
        if ( _aux_rnode.ch_size == 0 ) tmp_link = NodeID::top;
        else if ( _aux_rnode.ch_size == 1 ) tmp_link = _aux_rnode.ch[0];
        else {
            _qsorter.Sort( _aux_rnode.ch, _aux_rnode.ch_size );  // ToCheck
            tmp_link = Finest( &_aux_rnode );
        }
    }
    return tmp_link;
}

NodeID OBDDC_Manager::Finest( Rough_BDDC_Node * p )
{
	assert( p->sym == BDDC_SYMBOL_CONJOIN );
	unsigned i, j;
	unsigned tmp = _nodes[p->ch[p->ch_size - 1]].sym;
	_nodes[p->ch[p->ch_size - 1]].sym = BDDC_SYMBOL_CONJOIN;
	for ( i = 0; _nodes[p->ch[i]].sym != BDDC_SYMBOL_CONJOIN; i++ );
	_nodes[p->ch[p->ch_size - 1]].sym = tmp;
	if ( _nodes[p->ch[i]].sym != BDDC_SYMBOL_CONJOIN ) return Push_Node( *p );
	else {
		_node_sets[0] = _many_nodes;
		_node_set_sizes[0] = i;
		for ( j = 0; j < i; j++ ) _many_nodes[j] = p->ch[j];
		_node_sets[1] = _nodes[p->ch[i]].ch;
		_node_set_sizes[1] = _nodes[p->ch[i]].ch_size;
		unsigned cluster_size = 2;
		BDDC_Node node;
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = _nodes[p->ch[i]].ch_size;
		for ( i++; i < p->ch_size; i++ ) {
			if ( _nodes[p->ch[i]].sym == BDDC_SYMBOL_CONJOIN ) {
				node.ch_size += _nodes[p->ch[i]].ch_size;
				_node_sets[cluster_size] = _nodes[p->ch[i]].ch;
				_node_set_sizes[cluster_size++] = _nodes[p->ch[i]].ch_size;
			}
			else _many_nodes[_node_set_sizes[0]++] = p->ch[i];
		}
		node.ch_size += _node_set_sizes[0];
		node.ch = new NodeID [node.ch_size];
		if ( _node_set_sizes[0] == 0 ) Merge_Many_Arrays( _node_sets + 1, _node_set_sizes + 1, cluster_size - 1, node.ch );
		else Merge_Many_Arrays( _node_sets, _node_set_sizes, cluster_size, node.ch );
		return Push_Node( node );
	}
}

NodeID OBDDC_Manager::Finest_Exi( Rough_BDDC_Node * p )
{
	assert( p->sym == BDDC_SYMBOL_CONJOIN );
	unsigned i;
	for ( i = 0; _nodes[p->ch[i]].sym != BDDC_SYMBOL_CONJOIN; i++ ) {
		_many_nodes[i] = p->ch[i];
	}
    _node_sets[0] = _many_nodes;
    _node_set_sizes[0] = i;
    _node_sets[1] = _nodes[p->ch[i]].ch;
    _node_set_sizes[1] = _nodes[p->ch[i]].ch_size;
    unsigned cluster_size = 2;
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch_size = _nodes[p->ch[i]].ch_size;
    for ( i++; i < p->ch_size; i++ ) {
        if ( _nodes[p->ch[i]].sym == BDDC_SYMBOL_CONJOIN ) {
            node.ch_size += _nodes[p->ch[i]].ch_size;
            _node_sets[cluster_size] = _nodes[p->ch[i]].ch;
            _node_set_sizes[cluster_size++] = _nodes[p->ch[i]].ch_size;
        }
        else _many_nodes[_node_set_sizes[0]++] = p->ch[i];
    }
    node.ch_size += _node_set_sizes[0];
    node.ch = new NodeID [node.ch_size];
    if ( _node_set_sizes[0] == 0 ) Merge_Many_Arrays( _node_sets + 1, _node_set_sizes + 1, cluster_size - 1, node.ch );
    else Merge_Many_Arrays( _node_sets, _node_set_sizes, cluster_size, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Leaf_Left_No_Check( Decision_Node * p )
{
	assert( 0 < p->var && p->var <= _max_var );
	assert( p->low == NodeID::bot && Is_Internal( p->high ) );
	BDDC_Node node;
	Literal lit( p->var, true );
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[p->high].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[p->high].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[p->high].ch, _nodes[p->high].ch_size, NodeID::literal( lit ), node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < p->high ) {
			node.ch[0] = NodeID::literal( lit );
			node.ch[1] = p->high;
		}
		else {
			node.ch[0] = p->high;
			node.ch[1] = NodeID::literal( lit );
		}
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Leaf_Right_No_Check( Decision_Node * p )
{
	assert( 0 < p->var && p->var <= _max_var );
	assert( Is_Internal( p->low ) && p->high == NodeID::bot );
	BDDC_Node node;
	Literal lit( p->var, false );
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[p->low].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[p->low].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[p->low].ch, _nodes[p->low].ch_size, NodeID::literal( lit ), node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < p->low ) {
			node.ch[0] = NodeID::literal( lit );
			node.ch[1] = p->low;
		}
		else {
			node.ch[0] = p->low;
			node.ch[1] = NodeID::literal( lit );
		}
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Share_Semi_Check( Decision_Node * p )
{
	assert( _nodes[p->low].sym == BDDC_SYMBOL_CONJOIN && _nodes[p->high].sym == BDDC_SYMBOL_CONJOIN );
	unsigned num_shared = Intersection( _nodes[p->low].ch, _nodes[p->low].ch_size, \
		_nodes[p->high].ch, _nodes[p->high].ch_size, _many_nodes );
	if ( num_shared == 0 ) return Push_Node( *p );
	BDDC_Node node;
	node.sym = p->var;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	if ( num_shared == _nodes[p->low].ch_size ) {
		node.ch[0] = NodeID::top;
		node.ch[1] = Remove_Children( p->high, _many_nodes, num_shared );
	}
	else if ( num_shared == _nodes[p->high].ch_size ) {
		node.ch[0] = Remove_Children( p->low, _many_nodes, num_shared );
		node.ch[1] = NodeID::top;
	}
	else {
		node.ch[0] = Remove_Children( p->low, _many_nodes, num_shared );
		node.ch[1] = Remove_Children( p->high, _many_nodes, num_shared );
	}
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [num_shared + 1];
	node.ch_size = num_shared + 1;
	Insert( _many_nodes, num_shared, n, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Part_Left_No_Check( Decision_Node * p )
{
	assert( Is_Internal( p->low ) && _nodes[p->high].sym == BDDC_SYMBOL_CONJOIN );
	BDDC_Node node;
	node.sym = p->var;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	node.ch[0] = NodeID::top;
	if ( _nodes[p->high].ch_size == 2 ) node.ch[1] = _nodes[p->high].ch[0] + _nodes[p->high].ch[1] - p->low;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[1] = Remove_Child_No_Check_GE_3( p->high, p->low );
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [2];
	if ( n < p->low ) {
		node.ch[0] = n;
		node.ch[1] = p->low;
	}
	else {
		node.ch[0] = p->low;
		node.ch[1] = n;
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Part_Right_No_Check( Decision_Node * p )
{
	assert( _nodes[p->low].sym == BDDC_SYMBOL_CONJOIN && Is_Internal( p->high ) );
	BDDC_Node node;
	node.sym = p->var;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	if ( _nodes[p->low].ch_size == 2 ) node.ch[0] = _nodes[p->low].ch[0] + _nodes[p->low].ch[1] - p->high;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[0] = Remove_Child_No_Check_GE_3( p->low, p->high );
	node.ch[1] = NodeID::top;
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [2];
	if ( n < p->high ) {
		node.ch[0] = n;
		node.ch[1] = p->high;
	}
	else {
		node.ch[0] = p->high;
		node.ch[1] = n;
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Leaf_Left_No_Check( BDDC_Node * p )
{
	assert( 0 < p->sym && p->sym <= _max_var );
	assert( p->ch[0] == NodeID::bot && Is_Internal( p->ch[1] ) );
	BDDC_Node node;
	Literal lit( p->Var(), true );
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[p->ch[1]].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[p->ch[1]].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[p->ch[1]].ch, _nodes[p->ch[1]].ch_size, NodeID::literal( lit ), node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < p->ch[1] ) {
			node.ch[0] = NodeID::literal( lit );
			node.ch[1] = p->ch[1];
		}
		else {
			node.ch[0] = p->ch[1];
			node.ch[1] = NodeID::literal( lit );
		}
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Leaf_Right_No_Check( BDDC_Node * p )
{
	assert( 0 < p->sym && p->sym <= _max_var );
	assert( Is_Internal( p->ch[0] ) && p->ch[1] == NodeID::bot );
	BDDC_Node node;
	Literal lit( p->Var(), false );
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[p->ch[0]].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[p->ch[0]].ch_size + 1;
		node.ch = new NodeID [node.ch_size];
		Insert( _nodes[p->ch[0]].ch, _nodes[p->ch[0]].ch_size, NodeID::literal( lit ), node.ch );
	}
	else {
		node.ch_size = 2;
		node.ch = new NodeID [2];
		if ( lit < p->ch[0] ) {
			node.ch[0] = NodeID::literal( lit );
			node.ch[1] = p->ch[0];
		}
		else {
			node.ch[0] = p->ch[0];
			node.ch[1] = NodeID::literal( lit );
		}
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Share_Semi_Check( BDDC_Node * p )
{
	assert( _nodes[p->ch[0]].sym == BDDC_SYMBOL_CONJOIN && _nodes[p->ch[1]].sym == BDDC_SYMBOL_CONJOIN );
	unsigned num_shared = Intersection( _nodes[p->ch[0]].ch, _nodes[p->ch[0]].ch_size, \
		_nodes[p->ch[1]].ch, _nodes[p->ch[1]].ch_size, _many_nodes );
	if ( num_shared == 0 ) return Push_Node( *p );
	BDDC_Node node;
	node.sym = p->sym;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	if ( num_shared == _nodes[p->ch[0]].ch_size ) {
		node.ch[0] = NodeID::top;
		node.ch[1] = Remove_Children( p->ch[1], _many_nodes, num_shared );
	}
	else if ( num_shared == _nodes[p->ch[1]].ch_size ) {
		node.ch[0] = Remove_Children( p->ch[0], _many_nodes, num_shared );
		node.ch[1] = NodeID::top;
	}
	else {
		node.ch[0] = Remove_Children( p->ch[0], _many_nodes, num_shared );
		node.ch[1] = Remove_Children( p->ch[1], _many_nodes, num_shared );
	}
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [num_shared + 1];
	node.ch_size = num_shared + 1;
	Insert( _many_nodes, num_shared, n, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Part_Left_No_Check( BDDC_Node * p )
{
	assert( Is_Internal( p->ch[0] ) && _nodes[p->ch[1]].sym == BDDC_SYMBOL_CONJOIN );
	BDDC_Node node;
	node.sym = p->sym;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	node.ch[0] = NodeID::top;
	if ( _nodes[p->ch[1]].ch_size == 2 ) node.ch[1] = _nodes[p->ch[1]].ch[0] + _nodes[p->ch[1]].ch[1] - p->ch[0];  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[1] = Remove_Child_No_Check_GE_3( p->ch[1], p->ch[0] );
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [2];
	if ( n < p->ch[0] ) {
		node.ch[0] = n;
		node.ch[1] = p->ch[0];
	}
	else {
		node.ch[0] = p->ch[0];
		node.ch[1] = n;
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Extract_Part_Right_No_Check( BDDC_Node * p )
{
	assert( _nodes[p->ch[0]].sym == BDDC_SYMBOL_CONJOIN && Is_Internal( p->ch[1] ) );
	BDDC_Node node;
	node.sym = p->sym;
	node.ch = new NodeID [2];
	node.ch_size = 2;
	if ( _nodes[p->ch[0]].ch_size == 2 ) node.ch[0] = _nodes[p->ch[0]].ch[0] + _nodes[p->ch[0]].ch[1] - p->ch[1];  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else node.ch[0] = Remove_Child_No_Check_GE_3( p->ch[0], p->ch[1] );
	node.ch[1] = NodeID::top;
	NodeID n = Push_Node( node );
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch = new NodeID [2];
	if ( n < p->ch[1] ) {
		node.ch[0] = n;
		node.ch[1] = p->ch[1];
	}
	else {
		node.ch[0] = p->ch[1];
		node.ch[1] = n;
	}
	return Push_Node( node );
}

BDD OBDDC_Manager::Convert_Down_ROBDD( BDDC root, OBDD_Manager & bdd_manager )
{
	unsigned i;
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	Decision_Node * b_stack = new Decision_Node [2 * _max_var + 4];  // recording the results of Condition_Min_Change
	unsigned num_node_stack = 1;
	/* IMPORTANT:
	* Under the release mode, the procedure sometimes has a bug when using the statement such as '_nodes[n_stack[num_n_stack - 1]].infor.mark = f();',
	* where f will update _nodes.data. We will use tmp_link to rewrite 'tmp_link = f(); _nodes[n_stack[num_n_stack - 1]].infor.mark = tmp_link;'
	*/
	unsigned tmp_link;
	while ( num_node_stack ) {
		BDDC_Node & topn = _nodes[_node_stack[num_node_stack - 1]];
		if ( debug_options.display_Convert_Down ) {
			cout << "TOP: " << _node_stack[num_node_stack - 1] << endl;
			topn.Display( cout, false );
		}
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
				b_stack[num_node_stack].var = topn.sym;
				b_stack[num_node_stack].low = _nodes[topn.ch[0]].infor.mark;
				b_stack[num_node_stack].high = _nodes[topn.ch[1]].infor.mark;
				tmp_link = bdd_manager.Add_Node( b_stack[num_node_stack] );
				_nodes[_node_stack[num_node_stack]].infor.mark = tmp_link;  /// NOTE: _nodes.data may be re_assigned, so "_nodes[u]" cannot be replaced by "topn"
			}
		}
		else {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				unsigned min_var;
				unsigned min_var_ch;
				if ( Var_LT( _nodes[topn.ch[0]].sym, _nodes[topn.ch[1]].sym ) ) {
					min_var = _nodes[topn.ch[0]].sym;
					min_var_ch = topn.ch[0];
				}
				else {
					min_var = _nodes[topn.ch[1]].sym;
					min_var_ch = topn.ch[1];
				}
				for ( i = 2; i < topn.ch_size; i++ ) {
					if ( Var_LT( _nodes[topn.ch[i]].sym, min_var ) ) {
						min_var = _nodes[topn.ch[i]].sym;
						min_var_ch = topn.ch[i];
					}
				}
				b_stack[num_node_stack - 1].var = min_var;
				unsigned low = _nodes[min_var_ch].ch[0], high = _nodes[min_var_ch].ch[1];
				b_stack[num_node_stack - 1].low = Replace_Child( _node_stack[num_node_stack - 1], min_var_ch, low );
				b_stack[num_node_stack - 1].high = Replace_Child( _node_stack[num_node_stack - 1], min_var_ch, high );
				if ( debug_options.display_Convert_Down ) {
//					Display( cout );
					_nodes[b_stack[num_node_stack - 1].low].Display( cout, true );
					_nodes[b_stack[num_node_stack - 1].high].Display( cout, true );
				}
				_node_stack[num_node_stack] = b_stack[num_node_stack - 1].low;
				_node_mark_stack[num_node_stack] = true;
				_node_stack[num_node_stack + 1] = b_stack[num_node_stack - 1].high;
				_node_mark_stack[num_node_stack + 1] = true;
				num_node_stack += 2;
			}
			else {
				num_node_stack--;
				b_stack[num_node_stack].low = _nodes[b_stack[num_node_stack].low].infor.mark;
				b_stack[num_node_stack].high = _nodes[b_stack[num_node_stack].high].infor.mark;
				tmp_link = bdd_manager.Add_Node( b_stack[num_node_stack] );
				_nodes[_node_stack[num_node_stack]].infor.mark = tmp_link; /// NOTE: _nodes.data may be re_assigned, so "_nodes[u]" cannot be replaced by "topn"
				if ( debug_options.display_Convert_Down ) {
					cout << "new nodes in OBDD_Manager: " << _node_stack[num_node_stack] << " => " << _nodes[_node_stack[num_node_stack]].infor.mark << endl;
					_nodes[_nodes[_node_stack[num_node_stack]].infor.mark].Display( cout, true );
				}
			}
		}
	}
	BDD new_root = _nodes[root].infor.mark;
	delete [] b_stack;
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = UNSIGNED_UNDEF;
	}
	for ( ; i <=  root; i++ ) {
		_nodes[i].infor.mark = UNSIGNED_UNDEF;
	}
	if ( debug_options.verify_Convert_Down ) {
		bdd_manager.Verify_ROBDD( new_root );
		BigInt model_num1 = Count_Models( root );
//		model_num1.Display_DEC( cout );
		BigInt model_num2 = bdd_manager.Count_Models( new_root );
//		model_num2.Display_DEC( cout );
		assert( model_num1 == model_num2 );
//		this->Copy_Standard_Order()->Display( cout );
		EPCCL_Theory * cnf = bdd_manager.Convert_EPCCL( new_root );
//		cnf->Display( cout );
		assert( Entail_CNF( root, cnf ) );
		delete cnf;
	}
	return new_root;
}

NodeID OBDDC_Manager::Add_Child( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN  );
	assert( child > 1 );
	BDDC_Node node;
	node.sym = _nodes[parent].sym;
	node.ch_size = _nodes[parent].ch_size + 1;
	node.ch = new NodeID [node.ch_size];
	Insert( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Add_Children( NodeID parent, NodeID * children, unsigned num_ch )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	BDDC_Node node;
	node.sym = _nodes[parent].sym;
	node.ch_size = _nodes[parent].ch_size + num_ch;
	node.ch = new NodeID [node.ch_size];
	Merge_Two_Arrays( _nodes[parent].ch, _nodes[parent].ch_size, children, num_ch, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Remove_Child( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN || _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	if ( _nodes[parent].ch_size == 2 ) {
		if ( EITHOR_X( _nodes[parent].ch[0], _nodes[parent].ch[1], child ) )
			return _nodes[parent].ch[0] + _nodes[parent].ch[1] - child;  // NOTE: For integers, {x, y} \ {x} = x + y - x
		else return parent;
	}
	else {
		unsigned pos = Search_Pos_Nonempty( _nodes[parent].ch, _nodes[parent].ch_size, child );
		if ( pos < _nodes[parent].ch_size ) {
			BDDC_Node node;
			node.sym = _nodes[parent].sym;
			node.ch_size = _nodes[parent].ch_size - 1;
			node.ch = new NodeID [node.ch_size];
			Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
			return Push_Node( node );
		}
		else return parent;
	}
}

NodeID OBDDC_Manager::Remove_Child_No_Check( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	if ( _nodes[parent].ch_size == 2 ) return _nodes[parent].ch[0] + _nodes[parent].ch[1] - child;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else {
		BDDC_Node node;
		node.sym = _nodes[parent].sym;
		node.ch_size = _nodes[parent].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
		return Push_Node( node );
	}
}

NodeID OBDDC_Manager::Remove_Child_No_Check_GE_3( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( _nodes[parent].ch_size >= 3 );
	BDDC_Node node;
	node.sym = _nodes[parent].sym;
	node.ch_size = _nodes[parent].ch_size - 1;
	node.ch = new NodeID [node.ch_size];
	Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Remove_Child_No_Check_Change( NodeID parent, NodeID child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	if ( _nodes[parent].ch_size == 2 ) return _nodes[parent].ch[0] + _nodes[parent].ch[1] - child;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else {
		BDDC_Node node;
		node.sym = _nodes[parent].sym;
		node.ch_size = _nodes[parent].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Delete( _nodes[parent].ch, _nodes[parent].ch_size, child, node.ch );
		NodeID new_parent = Push_Node( node );
		return new_parent;
	}
}

NodeID OBDDC_Manager::Remove_Child_No_Check_Rough( Rough_BDDC_Node & parent, NodeID child )
{
	assert( parent.sym == BDDC_SYMBOL_CONJOIN );
	if ( parent.ch_size == 2 ) return parent.ch[0] + parent.ch[1] - child;  // NOTE: For integers, {x, y} \ {x} = x + y - x
	else {
		BDDC_Node node;
		node.sym = parent.sym;
		node.ch_size = parent.ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Delete( parent.ch, parent.ch_size, child, node.ch );
		return Push_Node( node );
	}
}

NodeID OBDDC_Manager::Remove_Children( NodeID parent, NodeID * children, unsigned num_ch )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	if ( _nodes[parent].ch_size == num_ch ) return NodeID::top;
	else if ( _nodes[parent].ch_size == num_ch + 1 ) {
		unsigned i;
		if ( _nodes[parent].ch[_nodes[parent].ch_size - 1] != children[num_ch - 1] ) return _nodes[parent].ch[_nodes[parent].ch_size - 1];
		for ( i = 0; _nodes[parent].ch[i] == children[i]; i++ );
		return _nodes[parent].ch[i];
	}
	else {
		BDDC_Node node;
		node.sym = _nodes[parent].sym;
		node.ch_size = _nodes[parent].ch_size - num_ch;
		node.ch = new NodeID [node.ch_size];
		Difference_Subset( _nodes[parent].ch, _nodes[parent].ch_size, children, num_ch, node.ch );
		return Push_Node( node );
	}
}

NodeID OBDDC_Manager::Replace_Child( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	if ( Is_Const( new_child ) ) {
		if ( new_child == NodeID::bot ) return NodeID::bot;
		else return Remove_Child_No_Check( parent, child );
	}
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
	}
	else {
		node.ch_size = _nodes[parent].ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Replace_Child_Nonconstant( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( new_child != NodeID::bot );
	if ( Is_Const( new_child ) ) return Remove_Child_No_Check( parent, child );
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
	}
	else {
		node.ch_size = _nodes[parent].ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Replace_Child_Internal( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( Is_Internal( new_child ) );
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	if ( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN ) {
		node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
	}
	else {
		node.ch_size = _nodes[parent].ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
	}
	return Push_Node( node );
}

NodeID OBDDC_Manager::Replace_Child_Internal_Same( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN );
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
	node.ch = new NodeID [node.ch_size];
	Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Replace_Child_Internal_Different( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( _nodes[new_child].sym <= _max_var );
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch_size = _nodes[parent].ch_size;
	node.ch = new NodeID [node.ch_size];
	Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
	return Push_Node( node );
}

NodeID OBDDC_Manager::Replace_Child_Nonconstant_Change( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( new_child != NodeID::bot );
	BDDC_Node node;
	NodeID new_parent;
	if ( new_child < 2 ) {
		new_parent = Remove_Child_No_Check_Change( parent, child );
	}
	else if ( _nodes[parent].sym == _nodes[new_child].sym ) {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
		new_parent = Push_Node( node );
	}
	else {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = _nodes[parent].ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
		new_parent = Push_Node( node );
	}
	return new_parent;
}

NodeID OBDDC_Manager::Replace_Child_Internal_Change( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( Is_Internal( new_child ) );
	BDDC_Node node;
	NodeID new_parent;
	if ( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN ) {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = _nodes[parent].ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( _nodes[parent].ch, _nodes[parent].ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
		new_parent = Push_Node( node );
	}
	else {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = _nodes[parent].ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
		new_parent = Push_Node( node );
	}
	return new_parent;
}

NodeID OBDDC_Manager::Replace_Child_Internal_Different_Change( NodeID parent, NodeID child, NodeID new_child )
{
	assert( _nodes[parent].sym == BDDC_SYMBOL_CONJOIN );
	assert( _nodes[new_child].sym <= _max_var );
	BDDC_Node node;
	node.sym = BDDC_SYMBOL_CONJOIN;
	node.ch_size = _nodes[parent].ch_size;
	node.ch = new NodeID [node.ch_size];
	Replace_One_By_One( _nodes[parent].ch, _nodes[parent].ch_size, child, new_child, node.ch );
	NodeID new_parent = Push_Node( node );
	return new_parent;
}

NodeID OBDDC_Manager::Replace_Child_Rough( Rough_BDDC_Node & parent, NodeID child, NodeID new_child )
{
	assert( parent.sym == BDDC_SYMBOL_CONJOIN );
	BDDC_Node node;
	if ( Is_Const( new_child ) ) {
		if ( new_child == NodeID::bot ) return NodeID::bot;
		else return Remove_Child_No_Check_Rough( parent, child );
	}
	else if ( _nodes[new_child].sym == BDDC_SYMBOL_CONJOIN ) {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = parent.ch_size + _nodes[new_child].ch_size - 1;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_Many( parent.ch, parent.ch_size, child, _nodes[new_child].ch, _nodes[new_child].ch_size, node.ch );
		return Push_Node( node );
	}
	else {
		node.sym = BDDC_SYMBOL_CONJOIN;
		node.ch_size = parent.ch_size;
		node.ch = new NodeID [node.ch_size];
		Replace_One_By_One( parent.ch, parent.ch_size, child, new_child, node.ch );
		return Push_Node( node );
	}
}

unsigned OBDDC_Manager::Num_Nodes( BDDC root )
{
	if ( root < 2 ) return 1;
	else if ( root < _num_fixed_nodes ) return 3;
	unsigned i;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
	    BDDC top = _node_stack[--num_node_stack];
	    BDDC_Node & topn = _nodes[top];
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

unsigned OBDDC_Manager::Num_Edges( BDDC root )
{
	if ( root < 2 ) return 0;
	else if ( root < _num_fixed_nodes ) return 2;
	unsigned i;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	unsigned result = 0;
	while ( num_node_stack > 0 ) {
	    BDDC top = _node_stack[--num_node_stack];
	    BDDC_Node & topn = _nodes[top];
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

size_t OBDDC_Manager::Memory()
{
	return Diagram_Manager::Memory() + 3 * _max_var * sizeof(unsigned) + _nodes.Memory();
}

unsigned OBDDC_Manager::Min_Decomposition_Depth( BDDC root )  // NOTE: the minimum depth of all decomposition _nodes.
{
	if ( root < _num_fixed_nodes ) return _max_var;
	unsigned i;
	_nodes[0].infor.mark = _max_var;
	_nodes[1].infor.mark = _max_var;
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len ) {
		BDDC_Node * top = &(_nodes[_path[path_len - 1]]);
		if ( top->sym <= _max_var ) {
			if ( _path_mark[path_len - 1] < 2 ) {
				if ( _nodes[top->ch[_path_mark[path_len - 1]]].infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = top->ch[_path_mark[path_len - 1]];
					_path_mark[path_len - 1]++;
					_path_mark[path_len++] = 0;
				}
				else _path_mark[path_len - 1]++;
			}
			else {
				if ( _nodes[top->ch[0]].infor.mark < _nodes[top->ch[1]].infor.mark ) top->infor.mark = _nodes[top->ch[0]].infor.mark;
				else top->infor.mark = _nodes[top->ch[1]].infor.mark;
				if ( top->infor.mark != _max_var ) top->infor.mark++;
				_visited_nodes.push_back( _path[--path_len] );
			}
		}
		else {
			top->infor.mark = 0;
			_visited_nodes.push_back( _path[--path_len] );
		}
	}
	unsigned result = _nodes[root].infor.mark;
	_nodes[0].infor.mark = UNSIGNED_UNDEF;
	_nodes[1].infor.mark = UNSIGNED_UNDEF;
	for ( i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
	return result;
}

void OBDDC_Manager::Remove_Redundant_Nodes( vector<BDDC> & kept_nodes )
{
//	Display( cout );
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
	for ( unsigned i = 0; i < kept_nodes.size(); i++ ) {
		assert( _nodes[kept_nodes[i]].infor.mark != UNSIGNED_UNDEF );
		kept_nodes[i] = _nodes[kept_nodes[i]].infor.mark;
	}
	unsigned new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	for ( i = 0; i < _nodes.Size(); i++ ) _nodes[i].infor.Init();
}

bool Is_Equivalent( OBDDC_Manager & manager1, BDDC root1, OBDDC_Manager & manager2, BDDC root2 )
{
	if ( root1 < manager1._num_fixed_nodes && root1 == root2 ) return true;
	else if ( root1 < manager1._num_fixed_nodes || root2 < manager2._num_fixed_nodes ) return false;
	unsigned i;
	for ( i = 0; i < manager1._num_fixed_nodes; i++ ) {
		manager1._nodes[i].infor.mark = i;
		manager2._nodes[i].infor.visited = true;
	}
	for ( i = 0; i < manager1._num_fixed_nodes; i++ ) {
		manager2._nodes[i].infor.visited = true;
	}
	manager1._node_stack[0] = root1;
	manager2._node_stack[0] = root2;
	unsigned num_n_stack = 1;
	bool result;
	for ( result = true; num_n_stack > 0; result = true ) { // it may break when num_n_stack == 0
		result = false;
		NodeID n_top1 = manager1._node_stack[--num_n_stack];  /// cannot delete result and use num_n_stack > 0, because of this statement
		NodeID n_top2 = manager2._node_stack[num_n_stack];
		BDDC_Node * node1 = &(manager1._nodes[n_top1]);
		BDDC_Node * node2 = &(manager2._nodes[n_top2]);
		if ( node1->sym != node2->sym || node1->ch_size != node2->ch_size ) break;
		if ( node1->sym <= manager1._max_var ) {
			BDDC_Node * ch1 = &(manager1._nodes[node1->ch[1]]);
			BDDC_Node * ch2 = &(manager2._nodes[node2->ch[1]]);
			if ( ( ch1->infor.mark != UNSIGNED_UNDEF ) != ch2->infor.visited ) break;
			if ( ch1->infor.mark == UNSIGNED_UNDEF ) {
				manager1._node_stack[num_n_stack] = node1->ch[1];
				ch1->infor.mark = node2->ch[1];
				manager1._visited_nodes.push_back( node1->ch[1] );
				manager2._node_stack[num_n_stack++] = node2->ch[1];
				ch2->infor.visited = true;
				manager2._visited_nodes.push_back( node2->ch[1] );
			}
			else if ( ch1->infor.mark != node2->ch[1] ) break;
			ch1 = &(manager1._nodes[node1->ch[0]]);
			ch2 = &(manager2._nodes[node2->ch[0]]);
			if ( ( ch1->infor.mark != UNSIGNED_UNDEF ) != ch2->infor.visited ) break;
			if ( ch1->infor.mark == UNSIGNED_UNDEF ) {
				manager1._node_stack[num_n_stack] = node1->ch[0];
				ch1->infor.mark = node2->ch[0];
				manager1._visited_nodes.push_back( node1->ch[0] );
				manager2._node_stack[num_n_stack++] = node2->ch[0];
				ch2->infor.visited = true;
				manager2._visited_nodes.push_back( node2->ch[0] );
			}
			else if ( ch1->infor.mark != node2->ch[0] ) break;
		}
		else {
			manager1.Sort_Children_Over_GLB( n_top1, manager1._many_nodes );
			manager2.Sort_Children_Over_GLB( n_top2, manager2._many_nodes );
			unsigned i = node1->ch_size - 1;
			for ( ; i != (unsigned) -1; i-- ) {
				BDDC_Node * ch1 = &(manager1._nodes[manager1._many_nodes[i]]);
				BDDC_Node * ch2 = &(manager2._nodes[manager2._many_nodes[i]]);
				if ( ( ch1->infor.mark != UNSIGNED_UNDEF ) != ch2->infor.visited || ch1->sym != ch2->sym )
					break;
				if ( ch1->infor.mark == UNSIGNED_UNDEF ) {
					manager1._node_stack[num_n_stack] = manager1._many_nodes[i];
					ch1->infor.mark = manager2._many_nodes[i];
                    manager1._visited_nodes.push_back( manager1._many_nodes[i] );
					manager2._node_stack[num_n_stack++] = manager2._many_nodes[i];
					ch2->infor.visited = true;
                    manager2._visited_nodes.push_back( manager2._many_nodes[i] );
				}
				else if ( ch1->infor.mark != manager2._many_nodes[i] ) break;
			}
			if ( i != (unsigned) -1 ) break;
		}
	}
	for ( i = 0; i < manager1._visited_nodes.size(); i++ ) {
        manager1._nodes[manager1._visited_nodes[i]].infor.mark = UNSIGNED_UNDEF;
        manager2._nodes[manager2._visited_nodes[i]].infor.visited = false;
	}
	manager1._visited_nodes.clear();
	manager2._visited_nodes.clear();
	return result;
}

bool OBDDC_Manager::Verify_Equ( BDDC root, OBDDC_Manager & other, BDDC other_root )
{
	if ( _max_var != other._max_var ) return false;
	unsigned i;
	if ( root < _num_fixed_nodes && root == other_root ) return true;
	else if ( root < _num_fixed_nodes || other_root < other._num_fixed_nodes ) return false;
	for ( i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
		other._nodes[i].infor.visited = true;
	}
	_path[0] = root;
	other._path[0] = other_root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		unsigned n_top1 = _path[path_len - 1];
		unsigned n_top2 = other._path[path_len - 1];
		BDDC_Node * node1 = &(_nodes[n_top1]);
		BDDC_Node * node2 = &(other._nodes[n_top2]);
		if ( node1->sym != node2->sym || node1->ch_size != node2->ch_size ) break;
		if ( node1->sym <= _max_var ) {
			if ( _path_mark[path_len - 1] < 2 ) {
				BDDC_Node * ch1 = &(_nodes[node1->ch[_path_mark[path_len - 1]]]);
				BDDC_Node * ch2 = &(other._nodes[node2->ch[_path_mark[path_len - 1]]]);
				if ( ( ch1->infor.mark != UNSIGNED_UNDEF ) != ch2->infor.visited ) break;
				if ( ch1->infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = node1->ch[_path_mark[path_len - 1]];
					ch1->infor.mark = node2->ch[_path_mark[path_len - 1]];
					other._path[path_len] = node2->ch[_path_mark[path_len - 1]];
					ch2->infor.visited = true;
					_path_mark[path_len - 1]++;
					_path_mark[path_len++] = 0;
				}
				else if ( ch1->infor.mark != node2->ch[_path_mark[path_len - 1]] ) break;
				else _path_mark[path_len - 1]++;
			}
			else path_len--;
		}
		else {
			Sort_Children_Over_GLB( n_top1, _many_nodes );
			other.Sort_Children_Over_GLB( n_top2, other._many_nodes );
			if ( _path_mark[path_len - 1] < node1->ch_size ) {
				BDDC_Node * ch1 = &(_nodes[_many_nodes[_path_mark[path_len - 1]]]);
				BDDC_Node * ch2 = &(other._nodes[other._many_nodes[_path_mark[path_len - 1]]]);
				if ( ( ch1->infor.mark != UNSIGNED_UNDEF ) != ch2->infor.visited || ch1->sym != ch2->sym ) break;
				else if ( ch1->infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = _many_nodes[_path_mark[path_len - 1]];
					ch1->infor.mark = other._many_nodes[_path_mark[path_len - 1]];
					other._path[path_len] = other._many_nodes[_path_mark[path_len - 1]];
					ch2->infor.visited = true;
					_path_mark[path_len - 1]++;
					_path_mark[path_len++] = 0;
				}
				else if ( ch1->infor.mark != other._many_nodes[_path_mark[path_len - 1]] ) break;
				else _path_mark[path_len - 1]++;
			}
			else path_len--;
		}
	}
	if ( path_len > 0 ) {
		Display( cerr );
		other.Display( cerr );
		cerr << "Error _path: " << endl;
		for ( i = 0; i < path_len - 1; i++ ) {
			cerr << _path[i] << " -> ";
		}
		cerr << _path[path_len - 1] << endl;
		for ( i = 0; i < path_len - 1; i++ ) {
			cerr << other._path[i] << " -> ";
		}
		cerr << other._path[path_len - 1] << endl;
	}
	for ( i = 0; i <= root; i++ ) {
		if ( _nodes[i].infor.mark != UNSIGNED_UNDEF ) {
			other._nodes[_nodes[i].infor.mark].infor.visited = false;
			_nodes[i].infor.mark = UNSIGNED_UNDEF;
		}
	}
	return path_len == 0;
}

BigInt OBDDC_Manager::Count_Models( BDDC root )
{
	unsigned num_vars = NumVars( _max_var );
	if ( Is_Fixed( root ) ) {
	    if ( root == NodeID::bot ) return 0;
		BigInt result = 1;
        result.Mul_2exp( num_vars );
        result.Div_2exp( root != NodeID::top );
		return result;
	}
    NodeID n;
	BigInt * results = new BigInt [root + 1];
	results[0] = 0;
    _nodes[NodeID::bot].infor.visited = true;
	results[1] = 1;
	results[1].Mul_2exp( num_vars );
    _nodes[NodeID::top].infor.visited = true;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
        n = NodeID::literal( i, false );
		results[n] = 1;
        results[n].Mul_2exp( num_vars - 1 );
        _nodes[n].infor.visited = true;
        n = NodeID::literal( i, true );
		results[n] = 1;
        results[n].Mul_2exp( num_vars - 1 );
        _nodes[n].infor.visited = true;
	}
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	while ( num_node_stack ) {
	    BDDC top = _node_stack[num_node_stack - 1];
		BDDC_Node & topn = _nodes[top];
		assert( topn.ch_size >= 0 );
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
				if ( DEBUG_OFF ) {
					cerr << "results[" << topn.ch[0] << "] = " << results[topn.ch[0]] << endl;
					cerr << "results[" << topn.ch[1] << "] = " << results[topn.ch[1]] << endl;
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
				_node_stack[num_node_stack] = topn.ch[1];
				_node_mark_stack[num_node_stack++] = true;
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
                    _node_stack[num_node_stack] = topn.ch[i];
                    _node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				num_node_stack--;
                results[top] = results[topn.ch[0]];
                results[top] *= results[topn.ch[1]];
                results[top].Div_2exp( num_vars );
                for ( unsigned i = 2; i < topn.ch_size; i++ ) {
                    results[top] *= results[topn.ch[i]];
                    results[top].Div_2exp( num_vars );
                }
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
			}
		}
	}
    _nodes[NodeID::bot].infor.visited = false;
    _nodes[NodeID::top].infor.visited = false;
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
        n = NodeID::literal( i, false );
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

BigInt OBDDC_Manager::Count_Models_Opt( BDDC root )
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
	    BDDC top = _node_stack[num_node_stack - 1];
		BDDC_Node & topn = _nodes[top];
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
				BDDC_Node & low = _nodes[topn.ch[0]];
				BDDC_Node & high = _nodes[topn.ch[1]];
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
		else {
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

bool OBDDC_Manager::Entail_Clause( BDDC root, Clause &cl )
{
	unsigned i;
	Label_Value( cl.Last_Lit() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_SAT( cl[i] ); i++ ) {
		_assignment[cl[i].Var()] = cl[i].NSign();
	}
	Un_Label_Value( cl.Last_Lit() );
	bool result;
	if ( Lit_SAT( cl[i] ) ) result = true;
	else {
		_assignment[cl[i].Var()] = cl[i].NSign();
		result = !Decide_Node_SAT_Under_Assignment( root );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[cl[i].Var()] = lbool::unknown;
	}
	return result;
}

bool OBDDC_Manager::Entail_CNF( BDDC root, CNF_Formula * cnf )
{
	vector<Clause>::iterator itr = cnf->Clause_Begin(), end = cnf->Clause_End();
	for ( ; itr < end; itr++ ) {
		if ( !Entail_Clause( root, *itr ) ) return false;
	}
	return true;
}

void OBDDC_Manager::Verify_Entail_CNF( BDDC root, CNF_Formula & cnf )
{
	unsigned i;
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		for ( i = 0; i < itr->Size(); i++ ) {
			if ( Lit_SAT( (*itr)[i] ) ) break;
			else _assignment[(*itr)[i].Var()] = (*itr)[i].NSign();
		}
		if ( i == itr->Size() ) Verify_Node_UNSAT_Under_Assignment( root );
		for ( i--; i != (unsigned) -1; i-- ) {
			_assignment[(*itr)[i].Var()] = lbool::unknown;
		}
	}
}

bool OBDDC_Manager::Decide_Node_SAT_Under_Assignment( BDDC root )
{
	if ( Is_Const( root ) ) return root == NodeID::top;
	if ( debug_options.display_Decide_Node_SAT_Under_Assignment ) {
		for ( Variable i = Variable::start; i <= _max_var; i++ ) {
			if ( _assignment[i] == true ) cout << i << " ";
			else if ( _assignment[i] == false ) cout << "-" << i << " ";
		}
		cout << endl;
	}
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
		BDDC_Node * top = &(_nodes[_path[path_len - 1]]);
		if ( top->sym <= _max_var ) {
			if ( Var_Decided( top->Var() ) ) {
				if ( _nodes[top->ch[_assignment[top->sym]]].infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = top->ch[_assignment[top->sym]];
					_path_mark[path_len++] = 0;
				}
				else {
					top->infor.mark = _nodes[top->ch[_assignment[top->sym]]].infor.mark;
					_visited_nodes.push_back( _path[--path_len] );
				}
			}
			else {
				switch ( _path_mark[path_len - 1] ) {
					case 0:
						if ( EITHOR_X( _nodes[top->ch[0]].infor.mark, _nodes[top->ch[1]].infor.mark, 1 ) ) {
							top->infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( BOTH_ZERO( _nodes[top->ch[0]].infor.mark, _nodes[top->ch[1]].infor.mark ) ) {
							top->infor.mark = 0;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[top->ch[0]].infor.mark == 0 ) {
							_path[path_len] = top->ch[1];
							_path_mark[path_len - 1] += 2;
							_path_mark[path_len++] = 0;
						}
						else {
							_path[path_len] = top->ch[0];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 1:
						if ( _nodes[top->ch[0]].infor.mark == 1 ) {
							top->infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[top->ch[1]].infor.mark != UNSIGNED_UNDEF ) { // ch[1] may be a descendant of ch[0]
							top->infor.mark = _nodes[top->ch[1]].infor.mark;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else {
							_path[path_len] = top->ch[1];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 2:
						top->infor.mark = _nodes[top->ch[1]].infor.mark;
						_visited_nodes.push_back( _path[--path_len] );
						break;
				}
			}
		}
		else {
			if ( _path_mark[path_len - 1] == 0 ) {
				unsigned i, tmp = _nodes[top->ch[top->ch_size - 1]].infor.mark;
				_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
				for ( i = 0; _nodes[top->ch[i]].infor.mark != 0; i++ );
				_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
				if ( _nodes[top->ch[i]].infor.mark == 0 ) {
					top->infor.mark = 0;
					_visited_nodes.push_back( _path[path_len - 1] );
					path_len--;
				}
				else {
					_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
					for ( i = 0; _nodes[top->ch[i]].infor.mark == 1; i++ );
					_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
					if ( _nodes[top->ch[i]].infor.mark == 1 ) {
						top->infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = top->ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else if ( _path_mark[path_len - 1] < top->ch_size ) {
				if ( _nodes[top->ch[_path_mark[path_len - 1] - 1]].infor.mark == 0 ) {
					top->infor.mark = 0;
					_visited_nodes.push_back( _path[--path_len] );
				}
				else {
					unsigned i, tmp = _nodes[top->ch[top->ch_size - 1]].infor.mark;
					_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
					for ( i = _path_mark[path_len - 1]; _nodes[top->ch[i]].infor.mark == 1; i++ );
					_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
					if ( _nodes[top->ch[i]].infor.mark == 1 ) {
						top->infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = top->ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else {
				top->infor.mark = _nodes[top->ch[top->ch_size - 1]].infor.mark;
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

void OBDDC_Manager::Verify_Node_UNSAT_Under_Assignment( BDDC n )
{
	if ( Is_Const( n ) ) {
		assert( n == NodeID::bot );
	}
	unsigned i;
	_nodes[0].infor.mark = 0;
	_nodes[1].infor.mark = 1;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		if ( _assignment[i] >= 0 ) {
			_nodes[i + i].infor.mark = !_assignment[i];
			_nodes[i + i + 1].infor.mark = _assignment[i];
		}
		else {
			_nodes[i + i].infor.mark = 1;
			_nodes[i + i + 1].infor.mark = 1;
		}
	}
	_path[0] = n;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len ) {
		BDDC_Node * top = &(_nodes[_path[path_len - 1]]);
		if ( top->sym <= _max_var ) {
			if ( _assignment[top->sym] >= 0 ) {
				if ( _nodes[top->ch[_assignment[top->sym]]].infor.mark == UNSIGNED_UNDEF ) {
					_path[path_len] = top->ch[_assignment[top->sym]];
					_path_mark[path_len++] = 0;
				}
				else {
					top->infor.mark = _nodes[top->ch[_assignment[top->sym]]].infor.mark;
					_visited_nodes.push_back( _path[--path_len] );
				}
			}
			else {
				switch ( _path_mark[path_len - 1] ) {
					case 0:
						if ( EITHOR_X( _nodes[top->ch[0]].infor.mark, _nodes[top->ch[1]].infor.mark, 1 ) ) {
							top->infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( BOTH_ZERO( _nodes[top->ch[0]].infor.mark, _nodes[top->ch[1]].infor.mark ) ) {
							top->infor.mark = 0;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[top->ch[0]].infor.mark == 0 ) {
							_path[path_len] = top->ch[1];
							_path_mark[path_len - 1] += 2;
							_path_mark[path_len++] = 0;
						}
						else {
							_path[path_len] = top->ch[0];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 1:
						if ( _nodes[top->ch[0]].infor.mark == 1 ) {
							top->infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[top->ch[1]].infor.mark != UNSIGNED_UNDEF ) { // ch[1] may be a descendant of ch[0]
							top->infor.mark = _nodes[top->ch[1]].infor.mark;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else {
							_path[path_len] = top->ch[1];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						break;
					case 2:
						top->infor.mark = _nodes[top->ch[1]].infor.mark;
						_visited_nodes.push_back( _path[--path_len] );
						break;
				}
			}
		}
		else {
			if ( _path_mark[path_len - 1] == 0 ) {
				unsigned tmp = _nodes[top->ch[top->ch_size - 1]].infor.mark;
				_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
				for ( i = 0; _nodes[top->ch[i]].infor.mark != 0; i++ );
				_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
				if ( _nodes[top->ch[i]].infor.mark == 0 ) {
					top->infor.mark = 0;
					_visited_nodes.push_back( _path[--path_len] );
				}
				else {
					_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
					for ( i = 0; _nodes[top->ch[i]].infor.mark == 1; i++ );
					_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
					if ( _nodes[top->ch[i]].infor.mark == 1 ) {
						top->infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = top->ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else if ( _path_mark[path_len - 1] < top->ch_size ) {
				if ( _nodes[top->ch[_path_mark[path_len - 1] - 1]].infor.mark == 0 ) {
					top->infor.mark = 0;
					_visited_nodes.push_back( _path[--path_len] );
				}
				else {
					unsigned tmp = _nodes[top->ch[top->ch_size - 1]].infor.mark;
					_nodes[top->ch[top->ch_size - 1]].infor.mark = 0;
					for ( i = _path_mark[path_len - 1]; _nodes[top->ch[i]].infor.mark == 1; i++ );
					_nodes[top->ch[top->ch_size - 1]].infor.mark = tmp;
					if ( _nodes[top->ch[i]].infor.mark == 1 ) {
						top->infor.mark = 1;
						_visited_nodes.push_back( _path[--path_len] );
					}
					else {
						_path[path_len] = top->ch[i];
						_path_mark[path_len - 1] = i + 1;
						_path_mark[path_len++] = 0;
					}
				}
			}
			else {
				top->infor.mark = _nodes[top->ch[top->ch_size - 1]].infor.mark;
				_visited_nodes.push_back( _path[--path_len] );
			}
		}
	}
	if ( _nodes[n].infor.mark == 1 ) {
		vector<Literal> lit_vec;
		lit_vec.reserve( 64 );
		_path[0] = n;
		_path_mark[0] = 0;
		path_len = 1;
		while ( path_len ) {
			BDDC_Node * top = &(_nodes[_path[path_len - 1]]);
			if ( Is_Const( _path[path_len - 1] ) ) path_len--;
			else if ( top->sym <= _max_var ) {
				if ( _assignment[top->sym] >= 0 ) {
					if ( _path_mark[path_len - 1] == 0 ) {
						lit_vec.push_back( Literal( Variable( top->sym ), _assignment[top->sym] ) );
						_path[path_len] = top->ch[_assignment[top->sym]];
						_path_mark[path_len - 1]++;
						_path_mark[path_len++] = 0;
					}
					else path_len--;
				}
				else {
					if ( _path_mark[path_len - 1] == 0 ) {
						if ( _nodes[top->ch[0]].infor.mark == 1 ) {
							lit_vec.push_back( Literal( Variable( top->sym ), false ) );
							_path[path_len] = top->ch[0];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						else {
							lit_vec.push_back( Literal( Variable( top->sym ), true ) );
							_path[path_len] = top->ch[1];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
					}
					else path_len--;
				}
			}
			else {
				if ( _path_mark[path_len - 1] < top->ch_size ) {
					_path[path_len] = top->ch[_path_mark[path_len - 1]];
					_path_mark[path_len - 1]++;
					_path_mark[path_len++] = 0;
				}
				else path_len--;
			}
		}
		cerr << "ERROR[BDDC]: The following _assignment is a model of cddd!" << endl;
		Quick_Sort( lit_vec );
		for ( i = 0; i < lit_vec.size(); i++ ) {
			cerr << ExtLit( lit_vec[i] ) << " ";
		}
		cerr << endl;
		assert( _nodes[n].infor.mark == 0 );
	}
	for ( i = Variable::start; i <= _max_var; i++ ) {
		_nodes[i + i].infor.mark = UNSIGNED_UNDEF;
		_nodes[i + i + 1].infor.mark = UNSIGNED_UNDEF;
	}
	for ( i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
}

void OBDDC_Manager::Display( ostream & out )
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
		if ( _nodes[u].sym == BDDC_SYMBOL_CONJOIN ) out << "C";
		else out << _nodes[u].sym;
		for ( unsigned i = 0; i < _nodes[u].ch_size; i++ ) {
			out << ' ' << _nodes[u].ch[i];
		}
		out << " 0" << endl;
	}
}

void OBDDC_Manager::Display_Stat( ostream & out )
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

void OBDDC_Manager::Display_New_Nodes( ostream & out, unsigned & old_size )
{
	for ( ; old_size < _nodes.Size(); old_size++ ) {
		out << old_size << ":\t";
		_nodes[old_size].Display( out );
	}
}


}

