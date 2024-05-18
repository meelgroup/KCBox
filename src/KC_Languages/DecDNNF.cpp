#include "DecDNNF.h"


namespace KCBox {


DecDNNF_Manager::DecDNNF_Manager( Variable max_var, unsigned estimated_node_num ):
CDD_Manager( max_var, estimated_node_num )
{
	Allocate_and_Init_Auxiliary_Memory();
}

void DecDNNF_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_many_vars = new Variable [_max_var + 1];
	_many_lits = new Literal [2 * _max_var + 4];
	_many_nodes = new NodeID [_max_var + 2];
	_node_sets = new NodeID * [_max_var + 2];
	_node_set_sizes = new unsigned [_max_var + 2];
	_many_sets = new SetID [_max_var + 1];
	_aux_rnode.Reset_Max_Var( _max_var );
}

DecDNNF_Manager::DecDNNF_Manager( istream & fin ):
CDD_Manager( Variable::start, LARGE_HASH_TABLE )
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
		if ( *p == 'D' ) {
			node.sym = CDD_SYMBOL_DECOMPOSE;
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

DecDNNF_Manager::DecDNNF_Manager( DecDNNF_Manager & other ):
CDD_Manager( other._max_var, other._nodes.Size() * 2 )
{
	Allocate_and_Init_Auxiliary_Memory();
	for ( unsigned u = _num_fixed_nodes; u < other._nodes.Size(); u++ ) {
		Push_New_Node( other._nodes[u] );
	}
}

DecDNNF_Manager::~DecDNNF_Manager()
{
	Free_Auxiliary_Memory();
}

void DecDNNF_Manager::Free_Auxiliary_Memory()
{
	delete [] _many_vars;
	delete [] _many_lits;
	delete [] _many_nodes;
	delete [] _node_sets;
	delete [] _node_set_sizes;
	delete [] _many_sets;
}

void DecDNNF_Manager::Enlarge_Max_Var( Variable & max_var )
{
	CDD_Manager::Enlarge_Max_Var( max_var );
	Free_Auxiliary_Memory();
	Allocate_and_Init_Auxiliary_Memory();
}

BigInt DecDNNF_Manager::Count_Models( NodeID root )
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
	    NodeID top = _node_stack[num_node_stack - 1];
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
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
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

BigFloat DecDNNF_Manager::Count_Models( const CDDiagram & dnnf, const vector<double> & weights )
{
	assert( Contain( dnnf ) );
	unsigned num_vars = NumVars( _max_var );
	BigFloat result;
	if ( Is_Fixed( dnnf.Root() ) ) {
	    if ( dnnf.Root() == NodeID::bot ) return 0;
        result.Assign_2exp( num_vars - ( dnnf.Root() != NodeID::top ) );
		return result;
	}
	_node_stack[0] = dnnf.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigFloat * results = new BigFloat [dnnf.Root() + 1];
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
				Literal lo( topn.Var(), false ), hi( topn.Var(), true );
				results[top].Weighted_Sum( weights[lo], results[topn.ch[0]], weights[hi], results[topn.ch[1]] );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				for ( unsigned i = Search_First_Non_Literal_Position( top ); i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				results[top] = results[topn.ch[0]];
				results[top] *= results[topn.ch[1]];
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
				}
                topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
	}
	result = results[dnnf.Root()];
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.visited = false;
	}
	delete [] results;
	return result;
}

BigInt DecDNNF_Manager::Count_Models( const CDDiagram & dnnf, const vector<Literal> & assignment )
{
	assert( Contain( dnnf ) );
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
		result = Count_Models_Under_Assignment( dnnf.Root(), size );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[assignment[i].Var()] = lbool::unknown;
	}
	return result;
}

BigInt DecDNNF_Manager::Count_Models_Under_Assignment( NodeID root, unsigned assignment_size )
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
		CDD_Node & topn = _nodes[top];
//	    cerr << top << ": ";
//	    topn.Display( cerr );
		assert( topn.ch_size >= 0 );
		if ( topn.infor.mark != UNSIGNED_UNDEF ) {
			num_node_stack--;
		}
		else if ( topn.sym <= _max_var ) {
			if ( Var_Decided( topn.Var() ) ) {
				NodeID child = topn.ch[_assignment[topn.sym]];
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
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				unsigned i;
				for ( i = 0; i < loc; i++ ) {
					if ( Lit_UNSAT( Node2Literal( topn.ch[i] ) ) ) break;
				}
				if ( i < loc ) {
					num_node_stack--;
					results[top] = 0;
					topn.infor.mark = num_vars;
					_visited_nodes.push_back( top );
				}
				else {
					_node_mark_stack[num_node_stack - 1] = false;
					for ( ; i < topn.ch_size; i++ ) {
						_node_stack[num_node_stack] = topn.ch[i];
						_node_mark_stack[num_node_stack++] = true;
					}
				}
			}
			else {
				num_node_stack--;
				unsigned num_sat = 0;
				for ( unsigned i = 0; i < loc; i++ ) {
					num_sat += Lit_SAT( Node2Literal( topn.ch[i] ) );
				}
				if ( loc == topn.ch_size ) {
					results[top] = 1;
					topn.infor.mark = num_vars - ( loc - num_sat );
				}
				else {
					results[top] = results[topn.ch[loc]];
					topn.infor.mark = _nodes[topn.ch[loc]].infor.mark;
					for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
						results[top] *= results[topn.ch[i]];
						topn.infor.mark += _nodes[topn.ch[i]].infor.mark;
					}
					topn.infor.mark -= ( topn.ch_size - loc - 1 ) * num_vars;
					topn.infor.mark -= loc - num_sat;
				}
				if ( DEBUG_OFF ) {
					for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
						cerr << "results[" << topn.ch[i] << "] = " << results[topn.ch[i]] << " * 2 ^ " << _nodes[topn.ch[i]].infor.mark << endl;
					}
					cerr << "results[" << top << "] = " << results[top] << " * 2 ^ " << topn.infor.mark << endl;
				}
				assert( topn.infor.mark <= num_vars );
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

BigInt DecDNNF_Manager::Count_Models_With_Condition( const CDDiagram & dnnf, const vector<Literal> & term )
{
	assert( Contain( dnnf ) );
	unsigned i, size = 0;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		size += !Lit_SAT( term[i] );
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	BigInt result;
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[DecDNNF_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	else {
		size += !Lit_SAT( term[i] );
		_assignment[term[i].Var()] = term[i].Sign();
		result = Count_Models_Under_Assignment( dnnf.Root(), size );
		result.Mul_2exp( size );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return result;
}

BigFloat DecDNNF_Manager::Count_Models_With_Condition( const CDDiagram & dnnf, const vector<double> & weights, const vector<Literal> & term )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) return 0;
	unsigned i;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( term[i] ); i++ ) {
		_assignment[term[i].Var()] = term[i].Sign();
	}
	Un_Label_Value( term.back() );
	if ( Lit_UNSAT( term[i] ) ) {
		cerr << "ERROR[DecDNNF_Manager]: an inconsistent term with conditioning!" << endl;
		exit(0);
	}
	_assignment[term[i].Var()] = term[i].Sign();
	vector<BigFloat> results( dnnf.Root() + 1 );
	Mark_Models_Under_Assignment( dnnf.Root(), weights, results );
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
	return results[dnnf.Root()];
}

void DecDNNF_Manager::Mark_Models_Under_Assignment( NodeID root, const vector<double> & weights, vector<BigFloat> & results )
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
		CDD_Node & topn = _nodes[top];
//	    cerr << top << ": ";
//	    topn.Display( cerr );
		assert( topn.ch_size >= 0 );
		if ( topn.infor.visited ) num_node_stack--;
		else if ( topn.sym <= _max_var ) {
			if ( Var_Decided( topn.Var() ) ) {
				NodeID child = topn.ch[_assignment[topn.sym]];
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
					_node_stack[num_node_stack] = topn.ch[0];
					_node_mark_stack[num_node_stack++] = true;
					_node_stack[num_node_stack] = topn.ch[1];
					_node_mark_stack[num_node_stack++] = true;
				}
				else {
					num_node_stack--;
					Literal lo( topn.Var(), false ), hi( topn.Var(), true );
					results[top].Weighted_Sum( weights[lo], results[topn.ch[0]], weights[hi], results[topn.ch[1]] );
					topn.infor.visited = true;
					_visited_nodes.push_back( top );
				}
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				unsigned i;
				for ( i = 0; i < loc; i++ ) {
					if ( Lit_UNSAT( Node2Literal( topn.ch[i] ) ) ) break;
				}
				if ( i < loc ) {
					num_node_stack--;
					results[top] = 0;
					topn.infor.visited = true;
					_visited_nodes.push_back( top );
				}
				else {
					_node_mark_stack[num_node_stack - 1] = false;
					for ( ; i < topn.ch_size; i++ ) {
						_node_stack[num_node_stack] = topn.ch[i];
						_node_mark_stack[num_node_stack++] = true;
					}
				}
			}
			else {
				num_node_stack--;
				results[top] = 1;
				for ( unsigned i = 0; i < loc; i++ ) {
					Literal lit = Node2Literal( topn.ch[i] );
					if ( !Lit_SAT( lit ) ) results[top] *= weights[lit];
				}
				for ( unsigned i = loc; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
				}
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
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

void DecDNNF_Manager::Mark_Models( const CDDiagram & dnnf, vector<BigFloat> & results )
{
	assert( Contain( dnnf ) );
	_node_stack[0] = dnnf.Root();
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
		else {
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

void DecDNNF_Manager::Probabilistic_Model( const CDDiagram & dnnf, vector<float> & prob_values )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
		cerr << "ERROR[DecDNNF_Manager]: invalid probabilistic model!" << endl;
		assert( dnnf.Root() != NodeID::bot );
	}
	else if ( dnnf.Root() == NodeID::top ) return;
	_node_stack[0] = dnnf.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	unsigned num_vars = NumVars( _max_var );
	BigFloat * results = new BigFloat [dnnf.Root() + 1];
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
		else {
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

void DecDNNF_Manager::Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	vector<BigFloat> model_values( dnnf.Root() + 1 );
	Mark_Models( dnnf, model_values );
	for ( vector<bool> & current_sample: samples ) {
		Uniformly_Sample( rand_gen, dnnf.Root(), current_sample, model_values );
	}
}

void DecDNNF_Manager::Uniformly_Sample( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & counts )
{
	sample.resize( _max_var + 1 );
	_path[0] = root;
	_path_mark[0] = true;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.sym <= _max_var ) {
			if ( top < _num_fixed_nodes ) {
				Literal lit = Node2Literal( top );
				sample[lit.Var()] = lit.Sign();
				_var_seen[lit.Var()] = true;
				path_len--;
			}
			else if ( _path_mark[path_len - 1] ) {
				double prob = Normalize( counts[topn.ch[0]], counts[topn.ch[1]] );
				bool b = rand_gen.Generate_Bool( prob );
				sample[topn.sym] = b;
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
					sample[imp.Var()] = imp.Sign();
					_var_seen[imp.Var()] = true;
				}
				path_len--;
			}
		}
		else path_len--;
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		if ( !_var_seen[x] ) {
			sample[x] = rand_gen.Generate_Bool( 0.5 );
		}
		else _var_seen[x] = false;
	}
}

void DecDNNF_Manager::Mark_Models( const CDDiagram & dnnf, const vector<double> & weights, vector<BigFloat> & results )
{
	assert( Contain( dnnf ) );
	_node_stack[0] = dnnf.Root();
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
				Literal lo( topn.Var(), false ), hi( topn.Var(), true );
				results[top].Weighted_Sum( weights[lo], results[topn.ch[0]], weights[hi], results[topn.ch[1]] );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				for ( unsigned i = Search_First_Non_Literal_Position( top ); i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				results[top] = results[topn.ch[0]];
				results[top] *= results[topn.ch[1]];
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
				}
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

void DecDNNF_Manager::Probabilistic_Model( const CDDiagram & dnnf, const vector<double> & weights, vector<double> & prob_values )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
		cerr << "ERROR[DecDNNF_Manager]: invalid probabilistic model!" << endl;
		assert( dnnf.Root() != NodeID::bot );
	}
	else if ( dnnf.Root() == NodeID::top ) return;
	_node_stack[0] = dnnf.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	BigFloat * results = new BigFloat [dnnf.Root() + 1];
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
				Literal lo( topn.Var(), false ), hi( topn.Var(), true );
				results[top].Weighted_Sum( weights[lo], results[topn.ch[0]], weights[hi], results[topn.ch[1]] );
				BigFloat right_result = results[topn.ch[1]];
				right_result *= weights[hi];
				prob_values[top] = Ratio( right_result, results[top] );
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
				num_node_stack--;
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				_node_mark_stack[num_node_stack - 1] = false;
				for ( unsigned i = Search_First_Non_Literal_Position( top ); i < topn.ch_size; i++ ) {
					_node_stack[num_node_stack] = topn.ch[i];
					_node_mark_stack[num_node_stack++] = true;
				}
			}
			else {
				results[top] = results[topn.ch[0]];
				results[top] *= results[topn.ch[1]];
				for ( unsigned i = 2; i < topn.ch_size; i++ ) {
					results[top] *= results[topn.ch[i]];
				}
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

void DecDNNF_Manager::Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, const vector<double> & weights, vector<vector<bool>> & samples )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
		samples.clear();
		return;
	}
	vector<BigFloat> model_values( dnnf.Root() + 1 );
	Mark_Models( dnnf, weights, model_values );
	for ( vector<bool> & current_sample: samples ) {
		Uniformly_Sample( rand_gen, dnnf.Root(), current_sample, model_values );
	}
}

void DecDNNF_Manager::Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples, const vector<Literal> & assignment )
{
	assert( Contain( dnnf ) );
	unsigned i;
	Label_Value( ~assignment.back() );  // ToDo: Check this line! It seems problematic
	for ( i = 0; !Lit_UNSAT( assignment[i] ); i++ ) {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
	}
	Un_Label_Value( assignment.back() );
	BigInt result;
	if ( !Lit_UNSAT( assignment[i] ) ) {
		_assignment[assignment[i].Var()] = assignment[i].Sign();
		vector<BigFloat> model_values( dnnf.Root() + 1 );
		Mark_Models_Under_Assignment( dnnf.Root(), model_values );
		if ( model_values[dnnf.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, dnnf.Root(), current_sample, model_values );
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[assignment[i].Var()] = lbool::unknown;
	}
}

void DecDNNF_Manager::Mark_Models_Under_Assignment( NodeID root, vector<BigFloat> & results )
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
		CDD_Node & topn = _nodes[top];
//	    cerr << top << ": ";
//	    topn.Display( cerr );
		assert( topn.ch_size >= 0 );
		if ( topn.infor.visited ) num_node_stack--;
		else if ( topn.sym <= _max_var ) {
			if ( Var_Decided( topn.Var() ) ) {
				NodeID child = topn.ch[_assignment[topn.sym]];
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
					if ( DEBUG_OFF ) {
						cerr << "results[" << child << "] = " << results[child] << endl;
						cerr << "results[" << top << "] = " << results[top] << endl;
					}
				}
			}
			else {
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
					if ( DEBUG_OFF ) {
						cerr << "results[" << topn.ch[0] << "] = " << results[topn.ch[0]] << endl;
						cerr << "results[" << topn.ch[1] << "] = " << results[topn.ch[1]] << endl;
						cerr << "results[" << top << "] = " << results[top] << endl;
					}
				}
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				unsigned i;
				for ( i = 0; i < loc; i++ ) {
					if ( Lit_UNSAT( Node2Literal( topn.ch[i] ) ) ) break;
				}
				if ( i < loc ) {
					num_node_stack--;
					results[top] = 0;
					topn.infor.visited = true;
					_visited_nodes.push_back( top );
				}
				else {
					_node_mark_stack[num_node_stack - 1] = false;
					for ( ; i < topn.ch_size; i++ ) {
						_node_stack[num_node_stack] = topn.ch[i];
						_node_mark_stack[num_node_stack++] = true;
					}
				}
			}
			else {
				num_node_stack--;
				unsigned num_sat = 0;
				for ( unsigned i = 0; i < loc; i++ ) {
					num_sat += Lit_SAT( Node2Literal( topn.ch[i] ) );
				}
				if ( loc == topn.ch_size ) {
					results[top].Assign_2exp( num_vars - ( loc - num_sat ) );
				}
				else {
					results[top] = results[topn.ch[loc]];
					for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
						results[top] *= results[topn.ch[i]];
						results[top].Div_2exp( num_vars );
					}
					results[top].Div_2exp( loc - num_sat );
				}
				if ( DEBUG_OFF ) {
					for ( unsigned i = loc + 1; i < topn.ch_size; i++ ) {
						cerr << "results[" << topn.ch[i] << "] = " << results[topn.ch[i]] << endl;
					}
					cerr << "results[" << top << "] = " << results[top] << endl;
				}
				topn.infor.visited = true;
				_visited_nodes.push_back( top );
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

void DecDNNF_Manager::Uniformly_Sample_Under_Assignment( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & counts )
{
	sample.resize( _max_var + 1 );
	_path[0] = root;
	_path_mark[0] = true;
	unsigned path_len = 1;
	while ( path_len > 0 ) {
		NodeID top = _path[path_len - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.sym <= _max_var ) {
			if ( top < _num_fixed_nodes ) {
				Literal lit = Node2Literal( top );
				assert( !Lit_UNSAT( lit ) );
				sample[lit.Var()] = lit.Sign();
				_var_seen[lit.Var()] = true;
				path_len--;
			}
			else if ( _path_mark[path_len - 1] ) {
				bool b;
				if ( Var_Decided( topn.Var() ) ) b = ( _assignment[topn.Var()] == true );
				else {
					double prob = Normalize( counts[topn.ch[0]], counts[topn.ch[1]] );
					b = rand_gen.Generate_Bool( prob );
				}
				sample[topn.sym] = b;
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
					sample[imp.Var()] = imp.Sign();
					_var_seen[imp.Var()] = true;
				}
				path_len--;
			}
		}
		else path_len--;
	}
	for ( Variable x = Variable::start; x <= _max_var; x++ ) {
		if ( !_var_seen[x] ) {
			if ( Var_Decided( x ) ) sample[x] = ( _assignment[x] == true );
			else sample[x] = rand_gen.Generate_Bool( 0.5 );
		}
		else _var_seen[x] = false;
	}
}

void DecDNNF_Manager::Uniformly_Sample_With_Condition( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples, const vector<Literal> & term )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
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
		vector<BigFloat> model_values( dnnf.Root() + 1 );
		Mark_Models_Under_Assignment( dnnf.Root(), model_values );
		if ( model_values[dnnf.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, dnnf.Root(), current_sample, model_values );
			for ( unsigned j = 0; j <= i; j++ ) {
				current_sample[term[j].Var()] = rand_gen.Generate_Bool( 0.5 );
			}
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
}

void DecDNNF_Manager::Uniformly_Sample_With_Condition( Random_Generator & rand_gen, const CDDiagram & dnnf, const vector<double> & weights, vector<vector<bool>> & samples, const vector<Literal> & term )
{
	assert( Contain( dnnf ) );
	if ( dnnf.Root() == NodeID::bot ) {
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
		vector<BigFloat> model_values( dnnf.Root() + 1 );
		Mark_Models_Under_Assignment( dnnf.Root(), weights, model_values );
		if ( model_values[dnnf.Root()] == 0 ) samples.clear();
		for ( vector<bool> & current_sample: samples ) {
			Uniformly_Sample( rand_gen, dnnf.Root(), current_sample, model_values );
			for ( unsigned j = 0; j <= i; j++ ) {
				current_sample[term[j].Var()] = rand_gen.Generate_Bool( 0.5 );
			}
		}
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[term[i].Var()] = lbool::unknown;
	}
}

void DecDNNF_Manager::Statistics( const CDDiagram & dnnf )
{
	assert( Contain( dnnf ) );
	if ( Is_Const( dnnf.Root() ) ) {
		cout << "Number of nodes: " << 1 << endl;
		cout << "Number of edges: " << 0 << endl;
		return;
	}
	_node_stack[0] = dnnf.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	_nodes[NodeID::bot].infor.visited = true;
	_nodes[NodeID::top].infor.visited = true;
	unsigned num_nodes = 2;
	unsigned num_edges = 0;
	while ( num_node_stack ) {
	    NodeID top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
		if ( topn.infor.visited ) num_node_stack--;
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
			num_edges += topn.ch_size;
			topn.infor.visited = true;
			_visited_nodes.push_back( top );
			num_node_stack--;
		}
	}
	cout << "Number of nodes: " << num_nodes << endl;
	cout << "Number of edges: " << num_edges << endl;
	_nodes[NodeID::bot].infor.visited = false;
	_nodes[NodeID::top].infor.visited = false;
	for ( NodeID id: _visited_nodes ) {
		_nodes[id].infor.visited = false;
	}
	_visited_nodes.clear();
}

NodeID DecDNNF_Manager::Add_Node( Rough_CDD_Node & rnode )
{
	if ( rnode.sym == CDD_SYMBOL_FALSE ) return NodeID::bot;
	else if ( rnode.sym == CDD_SYMBOL_TRUE ) return NodeID::top;
	else if ( rnode.sym <= _max_var ) {
		Decision_Node bnode( rnode.sym, rnode.ch[0], rnode.ch[1] );
		return Add_Decision_Node( bnode );
	}
	else if ( rnode.sym == CDD_SYMBOL_DECOMPOSE ) return Add_Decomposition_Node( rnode );
	else return NodeID::undef;
}

NodeID DecDNNF_Manager::Add_Decision_Node( Decision_Node & bnode )
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
	else tmp_link = Push_Node( bnode );
	return tmp_link;
}

NodeID DecDNNF_Manager::Extract_Leaf_Left_No_Check( Decision_Node & bnode )
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

NodeID DecDNNF_Manager::Extract_Leaf_Right_No_Check( Decision_Node & bnode )
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

NodeID DecDNNF_Manager::Extract_Share_No_Check( Decision_Node & bnode )  // use _lit_seen, _many_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
//	unsigned old_size = _nodes.Size();  // ToRemove
	assert( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE && _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE );
	unsigned num_shared = Intersection( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, \
		_nodes[bnode.high].ch, _nodes[bnode.high].ch_size, _many_nodes );
	assert( num_shared != 0 );
	if ( num_shared == _nodes[bnode.low].ch_size ) {
		bnode.low = NodeID::top;
		bnode.high = Remove_Children( bnode.high, _many_nodes, num_shared );
	}
	else if ( num_shared == _nodes[bnode.high].ch_size ) {
		bnode.low = Remove_Children( bnode.low, _many_nodes, num_shared );
		bnode.high = NodeID::top;
	}
	else {
		bnode.low = Remove_Children( bnode.low, _many_nodes, num_shared );
		bnode.high = Remove_Children( bnode.high, _many_nodes, num_shared );
	}
	NodeID n = Push_Node( bnode );
	Insert( _many_nodes, num_shared, n );
	return Push_Decomposition_Node( _many_nodes, num_shared + 1 );
}

NodeID DecDNNF_Manager::Remove_Children( NodeID parent, NodeID * children, unsigned num_ch )
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

NodeID DecDNNF_Manager::Extract_Part_Left_No_Check( Decision_Node & bnode )
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

NodeID DecDNNF_Manager::Remove_Child_No_Check_GE_3( NodeID parent, NodeID child )
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

NodeID DecDNNF_Manager::Extract_Part_Right_No_Check( Decision_Node & bnode )
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

NodeID DecDNNF_Manager::Remove_Child_No_Check( NodeID parent, NodeID child )
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

NodeID DecDNNF_Manager::Add_Decomposition_Node( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, node_set_sizes
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

unsigned DecDNNF_Manager::Finest( Rough_CDD_Node & rnode )  // use _many_nodes, node_sets, _node_set_sizes
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

unsigned DecDNNF_Manager::Finest_Last( Rough_CDD_Node & rnode )
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

CDDiagram DecDNNF_Manager::Condition( const CDDiagram & dnnf, const vector<Literal> & term )
{
	assert( Contain( dnnf ) );
	unsigned ii, size = 0;
	Label_Value( ~term.back() );  // ToDo: Check this line! It seems problematic
	for ( ii = 0; !Lit_UNSAT( term[ii] ); ii++ ) {
		size += !Lit_SAT( term[ii] );
		_assignment[term[ii].Var()] = term[ii].Sign();
	}
	Un_Label_Value( term.back() );
	if ( Lit_UNSAT( term[ii] ) ) {
		for ( ii--; ii != (unsigned) -1; ii-- ) {
			_assignment[term[ii].Var()] = lbool::unknown;
		}
		return Generate_DNNF( NodeID::bot );
	}
	if ( Is_Const( dnnf.Root() ) ) {
		for ( ii--; ii != (unsigned) -1; ii-- ) {
			_assignment[term[ii].Var()] = lbool::unknown;
		}
		return dnnf;
	}
	_assignment[term[ii].Var()] = term[ii].Sign();
	_node_stack[0] = dnnf.Root();
	_node_mark_stack[0] = true;
	unsigned num_node_stack = 1;
	_nodes[NodeID::bot].infor.mark = NodeID::bot;
	_nodes[NodeID::top].infor.mark = NodeID::top;
	while ( num_node_stack ) {
	    NodeID top = _node_stack[num_node_stack - 1];
		CDD_Node & topn = _nodes[top];
//	    cerr << top << ": ";
//	    topn.Display( cerr );
		assert( topn.ch_size >= 0 );
		if ( topn.infor.mark != UNSIGNED_UNDEF ) {
			num_node_stack--;
		}
		else if ( topn.sym <= _max_var ) {
			if ( Var_Decided( topn.Var() ) ) {
				NodeID child = topn.ch[_assignment[topn.sym]];
				if ( _node_mark_stack[num_node_stack - 1] ) {
					_node_mark_stack[num_node_stack - 1] = false;
					_node_stack[num_node_stack] = child;
					_node_mark_stack[num_node_stack++] = true;
				}
				else {
					topn.infor.mark = _nodes[child].infor.mark;
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
				}
				else {
					num_node_stack--;
					CDD_Node & low = _nodes[topn.ch[0]];
					CDD_Node & high = _nodes[topn.ch[1]];
					Decision_Node bnode( topn.sym, low.infor.mark, high.infor.mark );
					topn.infor.mark = Add_Decision_Node( bnode );
					_visited_nodes.push_back( top );
				}
			}
		}
		else {
			assert( topn.sym == CDD_SYMBOL_DECOMPOSE );
			unsigned loc = Search_First_Non_Literal_Position( top );
			if ( _node_mark_stack[num_node_stack - 1] ) {
				unsigned i;
				for ( i = 0; i < loc; i++ ) {
					if ( Lit_UNSAT( Node2Literal( topn.ch[i] ) ) ) break;
				}
				if ( i < loc ) {
					num_node_stack--;
					topn.infor.mark = NodeID::bot;
					_visited_nodes.push_back( top );
				}
				else {
					_node_mark_stack[num_node_stack - 1] = false;
					for ( ; i < topn.ch_size; i++ ) {
						_node_stack[num_node_stack] = topn.ch[i];
						_node_mark_stack[num_node_stack++] = true;
					}
				}
			}
			else {
				num_node_stack--;
				_aux_rnode.sym = CDD_SYMBOL_DECOMPOSE;
				_aux_rnode.ch_size = 0;
				unsigned i;
				for ( i = 0; i < loc; i++ ) {
					_aux_rnode.ch[_aux_rnode.ch_size] = topn.ch[i];
					_aux_rnode.ch_size += Lit_Undecided( Node2Literal( topn.ch[i] ) );
				}
				for ( ; i < topn.ch_size; i++ ) {
					CDD_Node & child = _nodes[topn.ch[i]];
					if ( child.infor.mark == NodeID::bot ) break;
					_aux_rnode.ch[_aux_rnode.ch_size] = child.infor.mark;
					_aux_rnode.ch_size += child.infor.mark != NodeID::top;
				}
				if ( i < topn.ch_size ) topn.infor.mark = NodeID::bot;
				else topn.infor.mark = Add_Decomposition_Node( _aux_rnode );
				_visited_nodes.push_back( top );
			}
		}
	}
	NodeID result = _nodes[dnnf.Root()].infor.mark;
	_nodes[NodeID::bot].infor.mark = UNSIGNED_UNDEF;
	_nodes[NodeID::top].infor.mark = UNSIGNED_UNDEF;
	for ( NodeID n: _visited_nodes ) {
		_nodes[n].infor.mark = UNSIGNED_UNDEF;
	}
	_visited_nodes.clear();
	for ( ; ii != (unsigned) -1; ii-- ) {
		_assignment[term[ii].Var()] = lbool::unknown;
	}
	return Generate_DNNF( result );
}

void DecDNNF_Manager::Verify_DecDNNF( NodeID root )
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

void DecDNNF_Manager::Compute_Var_Sets( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void DecDNNF_Manager::Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void DecDNNF_Manager::Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	CDD_Node & node = _nodes[n];
	assert( node.ch_size >= 2 );
	if ( node.sym == CDD_SYMBOL_FALSE ) { assert( node.ch[0] == NodeID::bot && node.ch[1] == NodeID::bot ); }
	else if ( node.sym == CDD_SYMBOL_TRUE ) { assert( node.ch[0] == NodeID::top && node.ch[1] == NodeID::top ); }
	else if ( n <= NodeID::literal( _max_var, true ) ) { assert( Is_Const( node.ch[0] ) && Is_Const( node.ch[1] ) ); }
	else if ( node.sym <= _max_var ) Verify_Decision_Node( node, var_cluster, sets );
	else if ( node.sym == CDD_SYMBOL_DECOMPOSE ) Verify_Decomposition_Node( node, var_cluster, sets );
	else {
		cerr << "ERROR[CDD]: Node " << n << " has a wrong symbol!" << endl;
		assert( node.sym == false );
	}
}

void DecDNNF_Manager::Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void DecDNNF_Manager::Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

bool DecDNNF_Manager::Entail_Clause( const CDDiagram & dnnf, Clause &cl )
{
	assert( Contain( dnnf ) );
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
		result = !Decide_SAT_Under_Assignment( dnnf.Root() );
	}
	for ( ; i != (unsigned) -1; i-- ) {
		_assignment[cl[i].Var()] = lbool::unknown;
	}
	return result;
}

bool DecDNNF_Manager::Decide_SAT_Under_Assignment( NodeID root )
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
						if ( EITHOR_X( _nodes[topn.ch[0]].infor.mark, _nodes[topn.ch[1]].infor.mark, 1 ) ) {
							topn.infor.mark = 1;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( BOTH_ZERO( _nodes[topn.ch[0]].infor.mark, _nodes[topn.ch[1]].infor.mark ) ) {
							topn.infor.mark = 0;
							_visited_nodes.push_back( _path[--path_len] );
						}
						else if ( _nodes[topn.ch[0]].infor.mark == 0 ) {
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
						if ( _nodes[topn.ch[0]].infor.mark == 1 ) {
							topn.infor.mark = 1;
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

bool DecDNNF_Manager::Entail_CNF( const CDDiagram & dnnf, CNF_Formula & cnf )
{
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		if ( !Entail_Clause( dnnf, *itr ) ) return false;
	}
	return true;
}

bool DecDNNF_Manager::Decide_SAT( const CDDiagram & dnnf, const vector<Literal> & assignment )
{
	if ( dnnf.Root() == NodeID::bot ) return false;
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
		result = Decide_SAT_Under_Assignment( dnnf.Root() );
	}
	return result;
}

void DecDNNF_Manager::Verify_Entail_CNF( NodeID root, CNF_Formula & cnf )
{
	unsigned i;
	vector<Clause>::iterator itr = cnf.Clause_Begin(), end = cnf.Clause_End();
	for ( ; itr < end; itr++ ) {
		for ( i = 0; i < itr->Size(); i++ ) {
			if ( Lit_SAT( (*itr)[i] ) ) break;
			else _assignment[(*itr)[i].Var()] = (*itr)[i].NSign();
		}
		if ( i == itr->Size() ) Verify_UNSAT_Under_Assignment( root );
		for ( i--; i != (unsigned) -1; i-- ) {
			_assignment[(*itr)[i].Var()] = lbool::unknown;
		}
	}
}

void DecDNNF_Manager::Verify_UNSAT_Under_Assignment( NodeID n )
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
		CDD_Node * top = &(_nodes[_path[path_len - 1]]);
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
			CDD_Node * top = &(_nodes[_path[path_len - 1]]);
			if ( Is_Const( _path[path_len - 1] ) ) path_len--;
			else if ( top->sym <= _max_var ) {
				if ( _assignment[top->sym] >= 0 ) {
					if ( _path_mark[path_len - 1] == 0 ) {
						lit_vec.push_back( Literal( top->Var(), _assignment[top->sym] ) );
						_path[path_len] = top->ch[_assignment[top->sym]];
						_path_mark[path_len - 1]++;
						_path_mark[path_len++] = 0;
					}
					else path_len--;
				}
				else {
					if ( _path_mark[path_len - 1] == 0 ) {
						if ( _nodes[top->ch[0]].infor.mark == 1 ) {
							lit_vec.push_back( Literal( top->Var(), false ) );
							_path[path_len] = top->ch[0];
							_path_mark[path_len - 1]++;
							_path_mark[path_len++] = 0;
						}
						else {
							lit_vec.push_back( Literal( top->Var(), true ) );
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
		cerr << "ERROR[DecDNNF]: The following _assignment is a model of Decision-DNNF!" << endl;
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

void DecDNNF_Manager::Display_Var_Sets( ostream & out, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void DecDNNF_Manager::Verify_Model( NodeID root, const vector<bool> & sample )
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

void DecDNNF_Manager::Display( ostream & out )
{
	Display_Nodes( out );
}

void DecDNNF_Manager::Display_Stat( ostream & out )
{
	Display_Nodes_Stat( out );
}


}


