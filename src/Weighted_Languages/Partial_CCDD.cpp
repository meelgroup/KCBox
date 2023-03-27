#include "Partial_CCDD.h"


namespace KCBox {


Partial_CCDD_Manager::Partial_CCDD_Manager( Variable max_var, unsigned estimated_num_node ):
Diagram_Manager( max_var ),
_nodes( 2 * estimated_num_node ),
_lit_equivalency( max_var )
{
	Allocate_and_Init_Auxiliary_Memory();
	Add_Fixed_Nodes();
}

void Partial_CCDD_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_main_memory = 0;
	_counting_mode = false;
}

void Partial_CCDD_Manager::Add_Fixed_Nodes()
{
	Push_Node( false );
	Push_Node( true );
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		Push_Node( Literal( x, false ) );
		Push_Node( Literal( x, true ) );
	}
	_num_fixed_nodes = _nodes.Size();
}

Partial_CCDD_Manager::~Partial_CCDD_Manager()
{
	for ( unsigned u = 0; u < _nodes.Size(); u++ ) {
		_nodes[u].Free();
	}
	Free_Auxiliary_Memory();
}

void Partial_CCDD_Manager::Free_Auxiliary_Memory()
{
}

void Partial_CCDD_Manager::Clear( Model_Pool * pool )
{
	for ( unsigned u = _num_fixed_nodes; u < _nodes.Size(); u++ ) {
		_nodes[u].Free();
		if ( _nodes[u].sym == SEARCH_UNKNOWN ) {
			for ( Model * model: _nodes[u].models ) {
				pool->Free( model );
			}
		}
	}
	_nodes.Resize( _num_fixed_nodes );
	_main_memory = 0;
	for ( unsigned u = 0; u < _nodes.Size(); u++ ) {
		_main_memory += _nodes[u].Memory();
	}
}

size_t Partial_CCDD_Manager::Memory()
{
	size_t mem = Diagram_Manager::Memory() + _main_memory;
	mem += ( _nodes.Capacity() - _nodes.Size() ) * sizeof(Partial_CDD_Node);
	return mem;
}

void Partial_CCDD_Manager::Verify_Decomposability( CDD root )
{
	if ( root < _num_fixed_nodes ) return;
	vector<DynamicSet<Variable>> var_sets( _nodes.Size() );
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		DynamicSet<Variable> & var_set = var_sets[i];
		var_set.Add_Element( Variable(_nodes[i].sym) );
	}
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		Partial_CDD_Node & topn = _nodes[top];
		DynamicSet<Variable> & var_set = var_sets[top];
		if ( topn.ch_size == 0 ) {
			for ( unsigned i = 0; i < topn.imp_size; i++ ) {
				var_set.Add_Element( topn.imp[i].Var() );
			}
			path_len--;
		}
		else if ( _path_mark[path_len - 1] < topn.ch_size ) {
			NodeID ch = topn.ch[_path_mark[path_len - 1]];
			Partial_CDD_Node & child = _nodes[ch];
			_path_mark[path_len - 1]++;
			if ( !child.infor.visited ) {
				_path[path_len] = ch;
				_path_mark[path_len++] = 0;
				child.infor.visited = true;
				_visited_nodes.push_back( ch );
			}
		}
		else {
			if ( topn.sym <= _max_var ) {
				DynamicSet<Variable> & set0 = var_sets[topn.ch[0]];
				DynamicSet<Variable> & set1 = var_sets[topn.ch[1]];
				var_set.Union( set0 , set1 );
				if ( var_set.In( Variable(topn.sym) ) ) {
					cerr << "ERROR[Partial_CCDD]: The symbol of the " << top << "th node appears in its descendant!" << endl;
					topn.Display( cerr, top );
					assert( false );
				}
				var_set.Add_Element( Variable(topn.sym) );
			}
			else {
				for ( unsigned i = 0; i < topn.ch_size; i++ ) {
					DynamicSet<Variable> & set1 = var_sets[topn.ch[i]];
					for ( unsigned j = i + 1; j < topn.ch_size; j++ ) {
						DynamicSet<Variable> & set2 = var_sets[topn.ch[j]];
						if ( !set1.Is_Disjoint( set2 ) ) {
							cerr << "ERROR[Partial_CCDD]: The " << i << "th and " << j << "th children of " << top << "th node is not decomposable!" << endl;
							topn.Display( cerr, top );
							assert( false );
						}
					}
					var_set.Union( set1 );
				}
				if ( topn.sym == SEARCH_DECOMPOSED ) {
					for ( unsigned i = 0; i < topn.imp_size; i++ ) {
						if ( var_set.In( topn.imp[i].Var() ) ) {
							cerr << "ERROR[Partial_CCDD]: The " << i << "th implied literal of " << top << "th node is not decomposable!" << endl;
							topn.Display( cerr, top );
							assert( false );
						}
						var_set.Add_Element( topn.imp[i].Var() );
					}
				}
				else {
					for ( unsigned i = 0; i < topn.imp_size; i += 2 ) {
						if ( var_set.In( topn.imp[i+1].Var() ) ) {
							cerr << "ERROR[Partial_CCDD]: The " << i/2 << "th pair of " << top << "th node is not kernelized!" << endl;
							topn.Display( cerr, top );
							assert( false );
						}
						var_set.Add_Element( topn.imp[i].Var() );
						var_set.Add_Element( topn.imp[i+1].Var() );
					}
				}
			}
			path_len--;
		}
	}
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
}

void Partial_CCDD_Manager::Realloc_Model_Space( Model_Pool * pool )
{
	for ( unsigned i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].sym == SEARCH_UNKNOWN ) {
			for ( Model * & model: _nodes[i].models ) {
				Model * other = model->Clone( _max_var );
				pool->Free( model );
				model = other;
			}
		}
	}
}

void Partial_CCDD_Manager::Thin_Model_Space( Model_Pool * pool)
{
	if ( _nodes.Size() == _num_fixed_nodes ) return;
	_node_stack[0] = _nodes.Size() - 1;;
	unsigned num_stack = 1;
	while ( num_stack > 0 ) {
		NodeID top = _node_stack[--num_stack];
		Partial_CDD_Node & topn = _nodes[top];
		if ( Is_Leaf( top ) ) {
			if ( topn.sym == SEARCH_UNKNOWN ) {
                assert( !topn.models.empty() );
				vector<Model *>::iterator itr = topn.models.end() - 1, begin = topn.models.begin();
				for ( ; itr > begin; itr-- ) {
					pool->Free( *itr );
				}
				topn.models.resize( 1 );
				_main_memory -= ( topn.models.capacity() - 1 ) * sizeof(Model *);
				topn.models.shrink_to_fit();
			}
			continue;
		}
		if ( topn.sym <= _max_var ) {
			Partial_CDD_Node & ch1 = _nodes[topn.ch[1]];
			if ( !ch1.infor.visited ) {
				_node_stack[num_stack++] = topn.ch[1];
				ch1.infor.visited = true;
				_visited_nodes.push_back( topn.ch[1] );
			}
			Partial_CDD_Node & ch0 = _nodes[topn.ch[0]];
			if ( !ch0.infor.visited ) {
				_node_stack[num_stack++] = topn.ch[0];
				ch0.infor.visited = true;
				_visited_nodes.push_back( topn.ch[0] );
			}
		}
		else {
			for ( unsigned i = 0; i < topn.ch_size; i++ ) {
				Partial_CDD_Node & ch = _nodes[topn.ch[i]];
				if ( !ch.infor.visited ) {
					_node_stack[num_stack++] = topn.ch[i];
					ch.infor.visited = true;
					_visited_nodes.push_back( topn.ch[i] );
				}
			}
		}
	}
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
}

void Partial_CCDD_Manager::Verify_Node( NodeID n )
{
	Partial_CDD_Node & node = _nodes[n];
	if ( Is_False( n ) ) assert( n == NodeID::bot );
	else if ( Is_True( n ) ) assert( n == NodeID::top );
	else if ( Literal( node ) != Literal::undef ) assert( n == Literal( node ) );
	if ( node.sym == SEARCH_CONFLICTED || node.sym == SEARCH_EMPTY || node.sym == SEARCH_KNOWN || node.sym == SEARCH_UNKNOWN ) {
		assert(  node.ch_size == 0 &&  node.imp_size == 0 );
		assert(  node.weight >= 0 );
		if ( node.sym == SEARCH_CONFLICTED ) {
			assert( node.weight == 0 );
			assert( node.models.empty() );
		}
		else if ( node.sym == SEARCH_KNOWN ) {
			assert( node.models.empty() );
		}
		else if ( node.sym == SEARCH_UNKNOWN ) {
			assert( !node.models.empty() );
		}
	}
	else if ( node.sym == SEARCH_DECOMPOSED ) {
		assert( node.models.empty() && node.imp_size + node.ch_size >= 2 );
		for ( unsigned i = 0; i < node.ch_size; i++ ) {  // no leaf node
			if ( Is_Leaf( node.ch[i] ) ) {
				assert( node.sym == SEARCH_KNOWN );
			}
		}
		for ( unsigned i = 1; i < node.imp_size; i++ ) {  // no identical imp
			assert( 2 <= node.imp[i] && node.imp[i] <= 2 * _max_var + 1 );
			for ( unsigned j = 0; j < i; j++ ) {
				assert( node.imp[j] != node.imp[i] );
			}
		}
		if ( node.ch_size == 0 ) {
			BigFloat w = 1;
			w.Mul_2exp( NumVars(_max_var) - node.imp_size );
			assert( node.weight == w );
		}
	}
	else if ( node.sym == SEARCH_KERNELIZED ) {
		assert( node.models.empty() && node.ch_size == 1 && node.imp_size >= 2 );
		if ( Is_Leaf( node.ch[0] ) ) {
			assert( node.sym != SEARCH_UNKNOWN && node.ch_size == 0 );
		}
		for ( unsigned i = 3; i < node.imp_size; i += 2 ) {  // no identical imp
			for ( unsigned j = 1; j < i; j += 2 ) {
				assert( node.imp[j] != node.imp[i] );
			}
		}
		BigFloat w = _nodes[node.ch[0]].weight;
		w.Div_2exp( node.imp_size / 2 );
		assert( node.weight == w );
	}
	else {
		assert( node.ch_size == 3 );
		assert( node.imp_size == 0 );
		assert( _nodes[node.ch[0]].sym != SEARCH_CONFLICTED || _nodes[node.ch[0]].sym != SEARCH_CONFLICTED );
		assert( 0 < node.estimate && node.estimate < 1 );
		assert( node.models.empty() );
	}
}

CDD Partial_CCDD_Manager::Complete_Lower_Bound( CDD root, CCDD_Manager & manager )
{
	assert( _max_var == manager.Max_Var() );
	if ( root < _num_fixed_nodes ) return root;
	_node_stack[0] = root;
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	_nodes[NodeID::bot].infor.mark = NodeID::bot;
	_nodes[NodeID::top].infor.mark = NodeID::top;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = i;
	}
	Rough_CDD_Node rnode( _max_var );
	while ( num_node_stack ) {
	    NodeID top = _node_stack[num_node_stack - 1];
		Partial_CDD_Node & topn = _nodes[top];
		if ( topn.infor.mark == UNSIGNED_UNDEF ) num_node_stack--;
		else if ( topn.sym == SEARCH_UNKNOWN ) {
			topn.infor.mark = NodeID::bot;
			_visited_nodes.push_back( top );
			num_node_stack--;
		}
		else if ( topn.sym <= _max_var ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				_node_stack[num_node_stack] = topn.ch[1];
				_node_mark_stack[num_node_stack++] = true;
				_node_stack[num_node_stack] = topn.ch[0];
				_node_mark_stack[num_node_stack++] = true;
			}
			else {
				Decision_Node bnode( topn.sym, _nodes[topn.ch[0]].infor.mark, _nodes[topn.ch[1]].infor.mark );
				topn.infor.mark = manager.Add_Decision_Node( bnode );
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else if ( topn.sym == CDD_SYMBOL_DECOMPOSE ) {
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				for ( unsigned i = topn.ch_size - 1; i != UNSIGNED_UNDEF; i-- ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				rnode.sym = CDD_SYMBOL_DECOMPOSE;
				rnode.ch_size = topn.imp_size + topn.ch_size;
				for ( unsigned i = 0; i < topn.ch_size; i++ ) {
					rnode.ch[i] = NodeID::literal( topn.imp[i] );
				}
				for ( unsigned i = 0; i < topn.ch_size; i++ ) {
					rnode.ch[topn.imp_size + i] = _nodes[topn.ch[i]].infor.mark;
				}
                topn.infor.mark = manager.Add_Decomposition_Node( rnode );
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
				rnode.sym = CDD_SYMBOL_KERNELIZE;
				rnode.ch_size = manager.Add_Equivalence_Nodes( topn.imp, topn.imp_size, rnode.ch );
				topn.infor.mark = manager.Add_Kernelization_Node( rnode );
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
	}
	NodeID result = _nodes[root].infor.mark;
	_nodes[NodeID::bot].infor.mark = UNSIGNED_UNDEF;
	_nodes[NodeID::top].infor.mark = UNSIGNED_UNDEF;
	for ( unsigned i = 2; i < _num_fixed_nodes; i++ ) {
		_nodes[i].infor.mark = UNSIGNED_UNDEF;
	}
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
	return result;
}

unsigned Partial_CCDD_Manager::Num_Nodes( CDD root )
{
	if ( root < _num_fixed_nodes ) return 1;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		Partial_CDD_Node & topn = _nodes[top];
		if ( Is_Leaf( top ) ) continue;
		if ( !_nodes[topn.ch[0]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[0];
			_nodes[topn.ch[0]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[0] );
		}
		for ( unsigned i = 1; i < topn.ch_size; i++ ) {
			if ( !_nodes[topn.ch[i]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[i];
				_nodes[topn.ch[i]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[i] );
			}
		}
	}
	unsigned node_size = _visited_nodes.size() + 1;  // 1 denotes the root
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
	return node_size;
}

unsigned Partial_CCDD_Manager::Num_Edges( CDD root )
{
	if ( root < _num_fixed_nodes ) return 0;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	unsigned result = 0;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		Partial_CDD_Node & topn = _nodes[top];
		if ( Is_Leaf( top ) ) continue;
		result += topn.ch_size;
		if ( !_nodes[topn.ch[0]].infor.visited ) {
			_node_stack[num_node_stack++] = topn.ch[0];
			_nodes[topn.ch[0]].infor.visited = true;
			_visited_nodes.push_back( topn.ch[0] );
		}
		for ( unsigned i = 1; i < topn.ch_size; i++ ) {
			if ( !_nodes[topn.ch[i]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[i];
				_nodes[topn.ch[i]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[i] );
			}
		}
	}
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
	return result;
}

unsigned Partial_CCDD_Manager::Num_Nodes( unsigned type, CDD root )
{
	if ( root < _num_fixed_nodes ) return 1;
	_node_stack[0] = root;
	unsigned num_node_stack = 1;
	unsigned result = 0;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		Partial_CDD_Node & topn = _nodes[top];
		if ( topn.sym == type ) result++;
		if ( Is_Leaf( top ) ) continue;
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
		for ( unsigned i = 2; i < topn.ch_size; i++ ) {
			if ( !_nodes[topn.ch[i]].infor.visited ) {
				_node_stack[num_node_stack++] = topn.ch[i];
				_nodes[topn.ch[i]].infor.visited = true;
				_visited_nodes.push_back( topn.ch[i] );
			}
		}
	}
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
	return result;
}

unsigned Partial_CCDD_Manager::Decision_Depth( CDD root )
{
	if ( root < _num_fixed_nodes ) return 0;
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		Partial_CDD_Node & topn = _nodes[top];
		if ( Is_Leaf( top ) ) {
			path_len--;
			topn.infor.mark = 0;
		}
		else if ( _path_mark[path_len - 1] < topn.ch_size ) {
			NodeID child = topn.ch[_path_mark[path_len - 1]++];
			if ( _nodes[child].infor.mark == UNSIGNED_UNDEF ) {
				_path[path_len] = child;
				_path_mark[path_len++] = 0;
				_visited_nodes.push_back( child );
			}
		}
		else {
			path_len--;
			if ( topn.sym <= _max_var ) {
				Partial_CDD_Node & low = _nodes[topn.ch[0]];
				Partial_CDD_Node & high = _nodes[topn.ch[1]];
			    if ( low.infor.mark > high.infor.mark ) topn.infor.mark = low.infor.mark + 1;
			    else topn.infor.mark = high.infor.mark + 1;
			}
			else if ( topn.sym == SEARCH_DECOMPOSED ) {
				topn.infor.mark = _nodes[topn.ch[0]].infor.mark;
				for ( unsigned i = 1; i < topn.ch_size; i++ ) {
				    if ( topn.infor.mark < _nodes[topn.ch[i]].infor.mark ) topn.infor.mark = _nodes[topn.ch[i]].infor.mark;
				}
			}
		}
	}
	unsigned result = _nodes[root].infor.mark;
	_nodes[root].infor.mark = UNSIGNED_UNDEF;
	for ( unsigned id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
	return result;
}

CDD Partial_CCDD_Manager::Add_Decision_Node( Partial_Decision_Node & bnode, unsigned cloc )
{
	if ( !_counting_mode ) return Push_Node( bnode, cloc );
	if ( Is_Node_Known( bnode.Low() ) && Is_Node_Known( bnode.High() ) ) {
		BigFloat count = _nodes[bnode.Low()].weight;
		count += _nodes[bnode.High()].weight;
		count.Div_2exp( 1 );
		return Add_Known_Node( count, cloc );
	}
	else return Push_Node( bnode, cloc );
}

bool Partial_CCDD_Manager::Is_Node_Known( NodeID n )
{
	assert( _counting_mode );
	_path[0] = n;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		Partial_CDD_Node & topn = _nodes[top];
		if ( Is_Leaf( top ) ) {
			if ( topn.sym == SEARCH_UNKNOWN ) break;
			path_len--;
		}
		else if ( topn.sym <= _max_var ) break;
		else if ( _path_mark[path_len - 1] < topn.ch_size ) {
			NodeID child = topn.ch[_path_mark[path_len - 1]++];
			_path[path_len] = child;
			_path_mark[path_len++] = 0;
		}
		else path_len--;
	}
	return path_len == 0;
}

NodeID Partial_CCDD_Manager::Add_Decision_Node( Rough_Partial_CDD_Node & rnode, unsigned cloc )
{
	assert( rnode.sym <= _max_var && rnode.ch.size() == 2 && rnode.imp.empty() > 0 );
	assert( rnode.ch[0] != NodeID::bot && rnode.ch[1] != NodeID::bot );
	Partial_Decision_Node bnode( Variable(rnode.sym), rnode.ch[0], rnode.ch[1], rnode.estimate );
	return Add_Decision_Node( bnode, cloc );
}

NodeID Partial_CCDD_Manager::Add_Decomposition_Node( Rough_Partial_CDD_Node & rnode )
{
	assert( rnode.sym == SEARCH_DECOMPOSED );
	if ( rnode.ch.size() == 1 && rnode.ch[0] == NodeID::top ) rnode.ch.clear();
	if ( rnode.imp.empty() && rnode.ch.empty() ) return NodeID::top;
	if ( rnode.imp.size() == 1 && rnode.ch.empty() ) return NodeID::literal( rnode.imp[0] );
	if ( rnode.imp.size() == 0 && rnode.ch.size() == 1 ) return rnode.ch[0];
	return Push_Node( rnode.imp.data(), rnode.imp.size(), rnode.ch.data(), rnode.ch.size() );
}

NodeID Partial_CCDD_Manager::Add_Kernelization_Node( Rough_Partial_CDD_Node & rnode, unsigned cloc )
{
	assert( rnode.sym == SEARCH_KERNELIZED );
	assert( rnode.ch.size() == 1 && rnode.imp.size() % 2 == 0 );
	if ( rnode.imp.empty() ) return rnode.ch[0];
	if ( _nodes[rnode.ch[0]].sym == SEARCH_KERNELIZED ) {
		_lit_equivalency.Add_Equivalences( rnode.imp.data(), rnode.imp.size() );
		rnode.imp.clear();
		Partial_CDD_Node & child = _nodes[rnode.ch[0]];
		_lit_equivalency.Add_Equivalences( child.imp, child.imp_size );
		_lit_equivalency.Output_Equivalences( rnode.imp );
		_lit_equivalency.Reset();
		rnode.ch[0] = child.ch[0];
	}
	return Push_Node( rnode.ch[0], rnode.imp, cloc );
}

CDD Partial_CCDD_Manager::Update_Decision_Child( NodeID parent, bool sign, NodeID new_child )
{
	assert( _nodes[parent].sym <= _max_var && _nodes[parent].ch_size == 2 && _nodes[parent].imp_size == 0 );
	assert( 0 < _nodes[parent].estimate && _nodes[parent].estimate < 1 );
	assert( _nodes[new_child].sym != SEARCH_CONFLICTED && _nodes[new_child].sym != SEARCH_UNKNOWN );
	Partial_CDD_Node & old_node = _nodes[parent];
	if ( _counting_mode && Is_Node_Known( old_node.ch[!sign] ) && Is_Node_Known( new_child ) ) {
		BigFloat count = _nodes[old_node.ch[!sign]].weight;
		count += _nodes[new_child].weight;
		count.Div_2exp( 1 );
		return Add_Known_Node( count, old_node.caching_loc );
	}
	Partial_Decision_Node dnode( Variable(old_node.sym), old_node.ch[0], old_node.ch[1], old_node.estimate );
	Partial_CDD_Node new_node( dnode, old_node.caching_loc );
	new_node.ch[sign] = new_child;
	new_node.freq[sign] = old_node.freq[sign] + 1;
	new_node.freq[!sign] = old_node.freq[!sign];
	Decision_Compute_Weight( new_node );
	return Push_Node( new_node );
}

CDD Partial_CCDD_Manager::Update_Kernelization_Child( NodeID parent, NodeID new_child )
{
	assert( _nodes[parent].sym == SEARCH_KERNELIZED && _nodes[parent].ch_size == 1 && _nodes[parent].imp_size % 2 == 0 );
	assert( _nodes[new_child].sym != SEARCH_CONFLICTED && _nodes[new_child].sym != SEARCH_UNKNOWN );
	Partial_CDD_Node & old_node = _nodes[parent];
	Partial_CDD_Node new_node( new_child, old_node.imp, old_node.imp_size / 2, old_node.caching_loc );
	return Push_Node( new_node );
}

bool Partial_CCDD_Manager::Sample( Random_Generator & rand_gen, NodeID n )
{
	assert( _nodes[n].sym <= _max_var && _nodes[n].ch_size == 2 && _nodes[n].imp_size == 0 );
	Partial_CDD_Node & node = _nodes[n];
	if ( _counting_mode ) {
		if ( Is_Node_Known( node.ch[0] ) ) return true;
		else if ( Is_Node_Known( node.ch[1] ) ) return false;
	}
	return rand_gen.Generate_Bool( node.estimate );
}

bool Partial_CCDD_Manager::Sample_Adaptive( Random_Generator & rand_gen, NodeID n, double prob )
{
	assert( _nodes[n].sym <= _max_var && _nodes[n].ch_size == 2 && _nodes[n].imp_size == 0 );
	assert( 0 < prob && prob < 1 );
	Partial_CDD_Node & node = _nodes[n];
    unsigned total_freq = node.freq[0] + node.freq[1];
	double pre = total_freq * node.estimate;  // expectation of true sampling
	node.estimate = ( pre + prob ) / ( total_freq + 1 );
	return rand_gen.Generate_Bool( node.estimate );
}

void Partial_CCDD_Manager::Remove_Redundant_Nodes( vector<CDD> & kept_nodes )
{
//	Display( cout );
	for ( unsigned i = 0; i < kept_nodes.size(); i++ ) {
		_nodes[kept_nodes[i]].infor.visited = true;
	}
	for ( unsigned i = _nodes.Size() - 1; i >= _num_fixed_nodes; i-- ) {
		if ( _nodes[i].infor.visited ) {
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
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
			_nodes[i - num_remove].imp = _nodes[i].imp;
			_nodes[i - num_remove].imp_size = _nodes[i].imp_size;
			_nodes[i - num_remove].ch = _nodes[i].ch;
			_nodes[i - num_remove].ch_size = _nodes[i].ch_size;
			_nodes[i - num_remove].caching_loc = _nodes[i].caching_loc;
			_nodes[i - num_remove].freq[0] = _nodes[i].freq[0];
			_nodes[i - num_remove].freq[1] = _nodes[i].freq[1];
			_nodes[i - num_remove].estimate = _nodes[i].estimate;
			_nodes[i - num_remove].weight = _nodes[i].weight;
			_nodes[i - num_remove].models = _nodes[i].models;
			for ( unsigned j = 0; j < _nodes[i].ch_size; j++ ) {
				_nodes[i - num_remove].ch[j] = _nodes[_nodes[i].ch[j]].infor.mark;
			}
		}
		else {
			num_remove++;
			delete [] _nodes[i].ch;
		}
	}
	for ( i = 0; i < kept_nodes.size(); i++ ) {
		assert( _nodes[kept_nodes[i]].infor.mark != UNSIGNED_UNDEF );
		kept_nodes[i] = _nodes[kept_nodes[i]].infor.mark;
	}
	unsigned new_size = _nodes.Size() - num_remove;
	_nodes.Resize( new_size );
	_main_memory = 0;
	for ( i = 0; i < _nodes.Size(); i++ ) {
		_nodes[i].infor.Init();
		_main_memory += _nodes[i].Memory();
	}
}

void Partial_CCDD_Manager::Reset_Frequencies()
{
	for ( unsigned i = _num_fixed_nodes; i < _nodes.Size(); i++ ) {
		if ( _nodes[i].sym <= _max_var ) {
			_nodes[i].freq[0] = 0;
			_nodes[i].freq[1] = 0;
		}
	}
}

void Partial_CCDD_Manager::Display( ostream & out )
{
	out << "Maximum variable: " << ExtVar( _max_var ) << endl;
	Display_Nodes( out );
}

void Partial_CCDD_Manager::Display_Nodes( ostream & out )
{
	out << "Number of nodes: " << _nodes.Size() << endl;
	for ( unsigned i = 0; i < _nodes.Size(); i++ ) {
		_nodes[i].Display( out, i );
	}
}

void Partial_CCDD_Manager::Display_Stat( ostream & out )
{
	out << "Maximum variable: " << ExtVar( _max_var ) << endl;
	out << "Number of nodes: " << _nodes.Size() << endl;
	for ( unsigned i = 0; i < _nodes.Size(); i++ ) {
		out << i << ":\t";
		_nodes[i].Display( out, true );
	}
}

void Partial_CCDD_Manager::Display_New_Nodes( ostream & out, unsigned & old_size )
{
	for ( ; old_size < _nodes.Size(); old_size++ ) {
		_nodes[old_size].Display( out, old_size );
	}
}

void Partial_CCDD_Manager::Display_Partial_CCDD( ostream & out, CDD root )
{
	if ( Is_Fixed( root ) ) {
		_nodes[root].Display( out, root );
		return;
	}
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		Partial_CDD_Node & topn = _nodes[top];
		if ( _path_mark[path_len - 1] == topn.ch_size ) {
			path_len--;
			continue;
		}
		NodeID child = topn.ch[_path_mark[path_len - 1]];
		Partial_CDD_Node & childn = _nodes[child];
		_path_mark[path_len - 1]++;  // path_len will change in the following statement
		if ( !childn.infor.visited ) {
			_path[path_len] = child;
			_path_mark[path_len++] = 0;
			childn.infor.visited = true;
		}
	}
	for ( unsigned i = 0; i < root; i++ ) {
		if ( _nodes[i].infor.visited ) {
			out << i << ":\t";
			_nodes[i].Display( out, i );
			_nodes[i].infor.visited = false;
		}
	}
	out << root << ":\t";
	_nodes[root].Display( out, root );
	_nodes[root].infor.visited = false;
}

void Partial_CCDD_Manager::Display_Partial_CCDD_With_Weights( ostream & out, CDD root )
{
	if ( Is_Fixed( root ) ) {
		_nodes[root].Display_Weight( out, root );
		return;
	}
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	_path[0] = root;
	_path_mark[0] = 0;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		Partial_CDD_Node & topn = _nodes[top];
		if ( _path_mark[path_len - 1] == topn.ch_size ) {
			path_len--;
			continue;
		}
		NodeID child = topn.ch[_path_mark[path_len - 1]];
		Partial_CDD_Node & childn = _nodes[child];
		_path_mark[path_len - 1]++;  // path_len will change in the following statement
		if ( !childn.infor.visited ) {
			_path[path_len] = child;
			_path_mark[path_len++] = 0;
			childn.infor.visited = true;
		}
	}
	for ( unsigned i = 0; i < root; i++ ) {
		if ( _nodes[i].infor.visited ) {
			out << i << ":\t";
			_nodes[i].Display_Weight( out );
			_nodes[i].infor.visited = false;
		}
	}
	out << root << ":\t";
	_nodes[root].Display_Weight( out, root );
	_nodes[root].infor.visited = false;
}

}
