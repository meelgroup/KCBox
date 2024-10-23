#include "smooth-OBDD[AND].h"


namespace KCBox {


void Smooth_OBDDC_Manager::Verify_Smoothness( NodeID root )
{
	if ( root < _num_fixed_nodes ) return;
	Hash_Cluster<Variable> var_cluster( NumVars( _max_var ) );
	vector<SetID> sets( root + 1 );
	Compute_Var_Sets( root, var_cluster, sets );
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = true;
	}
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[num_node_stack - 1];
		BDDC_Node & topn = _nodes[top];
		num_node_stack--;
		if ( topn.sym <= _max_var ) {
			if ( sets[topn.ch[0]] != sets[topn.ch[1]] ) {
				cerr << "ERROR[BDDC]: The " << top << "th node is not smooth!" << endl;
				assert( sets[topn.ch[0]] == sets[topn.ch[1]] );
			}
			BDDC_Node & ch1 = _nodes[topn.ch[1]];
			BDDC_Node & ch0 = _nodes[topn.ch[0]];
			if ( !ch1.infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[1];
				ch1.infor.visited = true;
			}
			if ( !ch0.infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[0];
				ch0.infor.visited = true;
			}
		}
		else {
			unsigned i = topn.ch_size - 1;
			for ( ; i != (unsigned) -1; i-- ) {
				BDDC_Node & ch = _nodes[topn.ch[i]];
				if ( !ch.infor.visited ) {
					_node_stack[num_node_stack++] = topn.ch[i];
					ch.infor.visited = true;
				}
			}
		}
	}
	for ( dag_size_t i = 0; i <= root; i++ ) {
		_nodes[i].infor.visited = false;
	}
}

void Smooth_OBDDC_Manager::Compute_Var_Sets( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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
		BDDC_Node & topn = _nodes[top];
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
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	_visited_nodes.clear();
}

void Smooth_OBDDC_Manager::Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	unsigned i;
	if ( _nodes[n].sym <= _max_var ) {
		sets[n] = var_cluster.Union( sets[_nodes[n].ch[0]], sets[_nodes[n].ch[1]], _nodes[n].Var() );
	}
	else {
		assert( _nodes[n].sym == DECOMP_SYMBOL_CONJOIN );
		SetID * copied_sets = new SetID [_nodes[n].ch_size];
		copied_sets[0] = sets[_nodes[n].ch[0]];
		copied_sets[1] = sets[_nodes[n].ch[1]];
		for ( i = 2; i < _nodes[n].ch_size; i++ ) {
			copied_sets[i] = sets[_nodes[n].ch[i]];
		}
		sets[n] = var_cluster.Union_Disjoint( copied_sets, _nodes[n].ch_size );
		delete [] copied_sets;
	}
}

void Smooth_OBDDC_Manager::Verify_Smooth_ROBDDC_Finest( NodeID root )
{
	if ( root < _num_fixed_nodes ) return;
	Verify_OBDDC( root );
	Verify_Smoothness( root );
	for ( unsigned i = 0; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.visited = true;
	}
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID topn = _node_stack[--num_node_stack];
		BDDC_Node * top = &(_nodes[topn]);
		if ( top->sym <= _max_var ) {
			BDDC_Node * ch1 = &(_nodes[top->ch[1]]);
			BDDC_Node * ch0 = &(_nodes[top->ch[0]]);
			if ( top->ch[0] == top->ch[1] && top->ch[1] != NodeID::top ) {
				cerr << "ERROR[BDDC]: The " << topn << "th node has two identical non-true children!" << endl;
				assert( top->ch[0] != top->ch[1] || top->ch[1] == NodeID::top );
			}
			if ( top->ch[0] == NodeID::bot || top->ch[1] == NodeID::bot ) {
				cerr << "ERROR[BDDC]: The " << topn << "th node is conjunctively decomposable, because it has a false child!" << endl;
				assert( top->ch[0] != top->ch[1] );
			}
			else if ( _nodes[top->ch[0]].sym == DECOMP_SYMBOL_CONJOIN && _nodes[top->ch[1]].sym == DECOMP_SYMBOL_CONJOIN ) {
				unsigned num_shared = Intersection( _nodes[top->ch[0]].ch, _nodes[top->ch[0]].ch_size, \
					_nodes[top->ch[1]].ch, _nodes[top->ch[1]].ch_size, _many_nodes );
				if ( num_shared > 0 ) {
					cerr << "ERROR[BDDC]: The " << topn << "th node is conjunctively decomposable, because left and right share children!" << endl;
					assert( num_shared == 0 );
				}
			}
			else if ( _nodes[top->ch[1]].sym == DECOMP_SYMBOL_CONJOIN && \
				Search_Exi_Nonempty( _nodes[top->ch[1]].ch, _nodes[top->ch[1]].ch_size, top->ch[0] ) ) {
				cerr << "ERROR[BDDC]: The " << topn << "th node is decomposable, because left is a part of right!" << endl;
				assert( false );
			}
			else if ( _nodes[top->ch[0]].sym == DECOMP_SYMBOL_CONJOIN && \
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
			_nodes[top->ch[top->ch_size - 1]].sym = DECOMP_SYMBOL_CONJOIN;
			for ( i = 0; _nodes[top->ch[i]].sym != DECOMP_SYMBOL_CONJOIN; i++ );
			_nodes[top->ch[top->ch_size - 1]].sym = tmp;
			if ( _nodes[top->ch[i]].sym == DECOMP_SYMBOL_CONJOIN ) {
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
	for ( dag_size_t i = 0; i <= root; i++ ) {
		_nodes[i].infor.visited = false;
	}
}

NodeID Smooth_OBDDC_Manager::Supplement_Auxiliary_Nodes( NodeID root, const vector<unsigned> & super_vars, const vector<unsigned> & vars )
{
	if ( root == NodeID::bot ) return NodeID::bot;
	_aux_rnode.sym = DECOMP_SYMBOL_CONJOIN;
	_aux_rnode.ch_size = 0;
	_aux_rnode.ch[0] = root;
	unsigned i = 0, j = 0;
	while ( i < super_vars.size() && j < vars.size() ) {
		if ( super_vars[i] < vars[j] ) {
			_aux_rnode.Add_Child( Push_Auxiliary_Node( Variable( super_vars[i] ) ) );
			i++;
		}
		else {
			assert( super_vars[i] == vars[j] );
			i++, j++;
		}
	}
	for ( ; i < super_vars.size(); i++ ) {
		_aux_rnode.Add_Child( Push_Auxiliary_Node( Variable( super_vars[i] ) ) );
	}
	if ( _nodes[root].sym == DECOMP_SYMBOL_CONJOIN ) {
		_aux_rnode.Add_Children( _nodes[root].ch, _nodes[root].ch_size );
	} else if ( root != NodeID::top ) _aux_rnode.Add_Child( root );
	if ( _aux_rnode.ch_size == 0 ) return NodeID::top;
	if ( _aux_rnode.ch_size == 1 ) return _aux_rnode.ch[0];
	_qsorter.Sort( _aux_rnode.ch, _aux_rnode.ch_size );
	return Push_Node( _aux_rnode );
}

NodeID Smooth_OBDDC_Manager::Add_Decision_Node( Decision_Node & dnode, const vector<unsigned> ** var_sets )
{
	if ( dnode.low == dnode.high ) {
		return Supplement_Auxiliary_Nodes( dnode.low, *(var_sets[0]), *(var_sets[1]) );
	}
	else if ( Is_Const( dnode.low ) && Is_Const( dnode.high ) ) {
		vector<unsigned> vars = {dnode.var};
		NodeID lit = NodeID::literal( dnode.var, dnode.high == NodeID::top );
		return Supplement_Auxiliary_Nodes( lit, *(var_sets[0]), vars );
	}
	else if ( dnode.low == NodeID::bot ) {
		NodeID root = Extract_Leaf_Left_No_Check( &dnode );
		Delete( *(var_sets[0]), unsigned(dnode.var), _aux_varIDs );
		return Supplement_Auxiliary_Nodes( root, _aux_varIDs, *(var_sets[2]) );
	}
	else if ( dnode.high == NodeID::bot ) {
		NodeID root = Extract_Leaf_Right_No_Check( &dnode );
		Delete( *(var_sets[0]), unsigned(dnode.var), _aux_varIDs );
		return Supplement_Auxiliary_Nodes( root, _aux_varIDs, *(var_sets[1]) );
	}
	else if ( BOTH_X( _nodes[dnode.low].sym, _nodes[dnode.high].sym, DECOMP_SYMBOL_CONJOIN ) ) {
		Smooth_Decision_Node( dnode, *(var_sets[1]), *(var_sets[2]) );
		NodeID root = Extract_Share_Semi_Check( &dnode );
		return Supplement_Auxiliary_Nodes( root, *(var_sets[0]), _aux_varIDs );
	}
	else if ( _nodes[dnode.high].sym == DECOMP_SYMBOL_CONJOIN && \
		Search_Exi_Nonempty( _nodes[dnode.high].ch, _nodes[dnode.high].ch_size, dnode.low ) ) {
		NodeID root = Extract_Part_Left_No_Check( &dnode );
		Delete( *(var_sets[0]), unsigned(dnode.var), _aux_varIDs );
		return Supplement_Auxiliary_Nodes( root, _aux_varIDs, *(var_sets[2]) );
	}
	else if ( _nodes[dnode.low].sym == DECOMP_SYMBOL_CONJOIN && \
		Search_Exi_Nonempty( _nodes[dnode.low].ch, _nodes[dnode.low].ch_size, dnode.high ) ) {
		NodeID root = Extract_Part_Right_No_Check( &dnode );
		Delete( *(var_sets[0]), unsigned(dnode.var), _aux_varIDs );
		return Supplement_Auxiliary_Nodes( root, _aux_varIDs, *(var_sets[1]) );
	} else {
		Smooth_Decision_Node( dnode, *(var_sets[1]), *(var_sets[2]) );
		NodeID root = Push_Node( dnode );
		return Supplement_Auxiliary_Nodes( root, *(var_sets[0]), _aux_varIDs );
	}
}

void Smooth_OBDDC_Manager::Smooth_Decision_Node( Decision_Node & dnode, const vector<unsigned> & lvars, const vector<unsigned> & hvars )
{
	_aux_varIDs.resize( 1 );
	_aux_varIDs[0] = dnode.var;
	_aux_rnode.sym = DECOMP_SYMBOL_CONJOIN;
	_aux_rnode.ch_size = 0;
	unsigned i = 0, j = 0;
	while ( i < lvars.size() && j < hvars.size() ) {
		if ( lvars[i] < hvars[j] ) _aux_varIDs.push_back( lvars[i++] );
		else {
			if ( lvars[i] == hvars[j] ) i++;
			else _aux_rnode.Add_Child( Push_Auxiliary_Node( hvars[j] ) );
			_aux_varIDs.push_back( hvars[j++] );
		}
	}
	while ( i < lvars.size() ) {
		_aux_varIDs.push_back( lvars[i++] );
	}
	while ( j < hvars.size() ) {
		_aux_rnode.Add_Child( Push_Auxiliary_Node( hvars[j] ) );
		_aux_varIDs.push_back( hvars[j++] );
	}
	if ( _nodes[dnode.low].sym == DECOMP_SYMBOL_CONJOIN ) {
		_aux_rnode.Add_Children( _nodes[dnode.low].ch, _nodes[dnode.low].ch_size );
	} else _aux_rnode.Add_Child( dnode.low );
	_qsorter.Sort( _aux_rnode.ch, _aux_rnode.ch_size );
	dnode.low = Push_Node( _aux_rnode );
	_aux_rnode.ch_size = i = j = 0;
	while ( i < lvars.size() && j < hvars.size() ) {
		if ( lvars[i] < hvars[j] ) {
			_aux_rnode.Add_Child( Push_Auxiliary_Node( lvars[i] ) );
			i++;
		}
		else if ( lvars[i] == hvars[j] ) i++, j++;
		else  j++;
	}
	for ( ; i < lvars.size(); i++ ) {
		_aux_rnode.Add_Child( Push_Auxiliary_Node( lvars[i] ) );
	}
	if ( _nodes[dnode.high].sym == DECOMP_SYMBOL_CONJOIN ) {
		_aux_rnode.Add_Children( _nodes[dnode.high].ch, _nodes[dnode.high].ch_size );
	} else _aux_rnode.Add_Child( dnode.high );
	_qsorter.Sort( _aux_rnode.ch, _aux_rnode.ch_size );
	dnode.high = Push_Node( _aux_rnode );
}

NodeID Smooth_OBDDC_Manager::Add_Decomposition_Node( Rough_BDDC_Node & rnode, const vector<unsigned> ** var_sets )
{
	const vector<unsigned> & allvars = *(var_sets[0]);
	_aux_varIDs.clear();
	const vector<unsigned> ** new_var_sets = new const vector<unsigned> * [rnode.ch_size];
	unsigned num_new_sets = 0;
	for ( unsigned i = 0; i < rnode.ch_size; i++ ) {
		if ( rnode.ch[i] == NodeID::bot ) {
			delete [] new_var_sets;
			return NodeID::bot;
		}
		else if ( Is_Literal( rnode.ch[i] ) ) _aux_varIDs.push_back( _nodes[rnode.ch[i]].sym );
		else if ( rnode.ch[i] != NodeID::top ) new_var_sets[num_new_sets++] = var_sets[i+1];
	}
	if ( !_aux_varIDs.empty() ) {
		_qsorter.Sort( _aux_varIDs );
		new_var_sets[num_new_sets++] = &_aux_varIDs;
	}
	if ( num_new_sets == 0 ) {
		for ( unsigned x: allvars ) {
			rnode.Add_Child( Push_Auxiliary_Node( x ) );
		}
	}
	else if ( num_new_sets == 1 ) {
		const vector<unsigned> & vars = *(new_var_sets[0]);
		unsigned i = 0, j = 0;
		while ( i < allvars.size() && j < vars.size() ) {
			if ( allvars[i] < vars[j] ) rnode.Add_Child( Push_Auxiliary_Node( allvars[i++] ) );
			else {
				assert( allvars[i] == vars[j] );
				i++, j++;
			}
		}
		while ( i < allvars.size() ) {
			rnode.Add_Child( Push_Auxiliary_Node( allvars[i++] ) );
		}
	}
	else if ( num_new_sets == 2 ) {
		unsigned j = 0, k = 0;
		const vector<unsigned> & vars0 = *(new_var_sets[0]);
		const vector<unsigned> & vars1 = *(new_var_sets[1]);
		for ( unsigned i = 0; i < allvars.size(); i++ ) {
			if ( j < vars0.size() && vars0[j] == allvars[i] ) j++;
			else if ( k < vars1.size() && vars1[k] == allvars[i] ) k++;
			else rnode.Add_Child( Push_Auxiliary_Node( allvars[i] ) );
		}
	}
	else {
		unsigned * iterator = new unsigned [num_new_sets];
		iterator[0] = 0;
		for ( unsigned j = 1; j < num_new_sets; j++ ) {
			iterator[j] = 0;
		}
		for ( unsigned i = 0; i < allvars.size(); i++ ) {
			unsigned j = 0;
			while ( j < num_new_sets ) {
				if ( iterator[j] == new_var_sets[j]->size() ) {
					iterator[j] = iterator[num_new_sets - 1];
					new_var_sets[j] = new_var_sets[num_new_sets - 1];
					num_new_sets--;
					continue;
				}
				if ( (*(new_var_sets[j]))[iterator[j]] == allvars[i] ) {
					iterator[j]++;
					break;
				}
				j++;
			}
			if ( j == num_new_sets ) rnode.Add_Child( Push_Auxiliary_Node( allvars[i] ) );
		}
		delete [] iterator;
	}
	delete [] new_var_sets;
	return OBDDC_Manager::Add_Decomposition_Node( rnode );
}

bool Is_Equivalent( Smooth_OBDDC_Manager & manager1, Diagram bddc1, Smooth_OBDDC_Manager & manager2, Diagram bddc2 )
{
	assert( manager1.Contain( bddc1 ) && manager2.Contain( bddc2 ) );
	if ( bddc1.Root() < manager1._num_fixed_nodes && bddc1.Root() == bddc2.Root() ) return true;
	else if ( bddc1.Root() < manager1._num_fixed_nodes || bddc2.Root() < manager2._num_fixed_nodes ) return false;
	unsigned i;
	for ( i = 0; i < manager1._num_fixed_nodes; i++ ) {
		manager1._nodes[i].infor.mark = i;
		manager2._nodes[i].infor.visited = true;
	}
	for ( i = 0; i < manager1._num_fixed_nodes; i++ ) {
		manager2._nodes[i].infor.visited = true;
	}
	manager1._node_stack[0] = bddc1.Root();
	manager2._node_stack[0] = bddc2.Root();
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
			if ( ch1->infor.Marked() != ch2->infor.visited ) break;
			if ( !ch1->infor.Marked() ) {
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
			if ( ch1->infor.Marked() != ch2->infor.visited ) break;
			if ( !ch1->infor.Marked() ) {
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
				if ( ch1->infor.Marked() != ch2->infor.visited || ch1->sym != ch2->sym )
					break;
				if ( !ch1->infor.Marked() ) {
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
		manager1._nodes[manager1._visited_nodes[i]].infor.Unmark();
		manager2._nodes[manager2._visited_nodes[i]].infor.visited = false;
	}
	manager1._visited_nodes.clear();
	manager2._visited_nodes.clear();
	return result;
}


}

