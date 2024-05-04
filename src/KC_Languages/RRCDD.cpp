#include "RRCDD.h"


namespace KCBox {


R2D2_Manager::R2D2_Manager( Variable max_var, unsigned estimated_node_num ):
RCDD_Manager( max_var, estimated_node_num )
{
	Allocate_and_Init_Auxiliary_Memory();
}

void R2D2_Manager::Allocate_and_Init_Auxiliary_Memory()
{
	_lit_vector.reserve( NumVars( _max_var ) );
}

R2D2_Manager::R2D2_Manager( Chain & vorder, unsigned estimated_node_num ):
RCDD_Manager( vorder, estimated_node_num )
{
	Allocate_and_Init_Auxiliary_Memory();
}

R2D2_Manager::R2D2_Manager( istream & fin ):
RCDD_Manager( fin )
{
	Allocate_and_Init_Auxiliary_Memory();
}

R2D2_Manager::R2D2_Manager( R2D2_Manager & other ):
RCDD_Manager( other )
{
	Allocate_and_Init_Auxiliary_Memory();
}

R2D2_Manager::~R2D2_Manager()
{
	Free_Auxiliary_Memory();
}

void R2D2_Manager::Free_Auxiliary_Memory()
{
}

NodeID R2D2_Manager::Add_Node( Rough_CDD_Node & rnode )
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

NodeID R2D2_Manager::Add_Decision_Node( Decision_Node & bnode )
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

NodeID R2D2_Manager::Extract_Share_No_Check( Decision_Node & bnode )  // use _lit_seen, _many_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
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

NodeID R2D2_Manager::Extract_Lit_Equivalences( Decision_Node & bnode )  // use _lit_seen, _many_equ_nodes, _aux_decom_rnode, _aux_kerne_rnode
{
	NodeID result;
//	Display( cerr );  // ToRemove
//	Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
//	cerr << bnode.low << " vs " << bnode.high << endl;
	if ( Is_Literal( bnode.low ) ) {
		if ( _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.low );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			if ( Search_Exi_Nonempty( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, lit_neg_node ) ) {
				unsigned high = Remove_Child_No_Check( bnode.high, lit_neg_node );
				_aux_kerne_rnode.ch[0] = Push_Decision_Node( bnode.var, NodeID::top, high );  // check the case where both children are true
				_aux_kerne_rnode.ch[1] = Push_Decision_Node( bnode.var, bnode.low, lit_neg_node );
				return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
			}
		}
		return Push_Decision_Node( bnode.var, bnode.low, bnode.high );
	}
	if ( Is_Literal( bnode.high ) ) {
		if ( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.high );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			if ( Search_Exi_Nonempty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, lit_neg_node ) ) {
				unsigned low = Remove_Child_No_Check( bnode.low, lit_neg_node );
				_aux_kerne_rnode.ch[0] = Push_Decision_Node( bnode.var, low, NodeID::top );  // check the case where both children are true
				_aux_kerne_rnode.ch[1] = Push_Decision_Node( bnode.var, lit_neg_node, bnode.high );
				return Push_Kernelization_Node( _aux_kerne_rnode.ch, 2 );
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
		_aux_kerne_rnode.Add_Child( Push_Decision_Node( bnode.var, bnode.low, bnode.high ) );  // check the case where both children are true
		for ( unsigned i = 0; i < num_equ; i++ ) {
			_aux_kerne_rnode.Add_Child( _many_equ_nodes[i] );
		}
		result = Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
	}
	else result = Push_Node( bnode );
	_lit_equivalency.Reset();
	return result;
}

unsigned R2D2_Manager::Lit_Equivalences( NodeID n, NodeID * equ_nodes )
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

void R2D2_Manager::Record_Lit_Equivalency( NodeID n, Lit_Equivalency & lit_equivalency )
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
					lit_equivalency.Add_Equivalence_Flat( lit, lit2 );
				}
			}
			else if ( Is_Equivalence_Node( child ) ) {
				Literal lit = Literal( child.Var(), true );
				Literal lit2 = Node2Literal( child.ch[1] );
				lit_equivalency.Add_Equivalence_Flat( lit, lit2 );
			}
		}
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		for ( i = 1; i < node.ch_size; i++ ) {
			CDD_Node & child = _nodes[node.ch[i]];
			Literal lit( child.Var(), true );
			Literal lit2 = Node2Literal( child.ch[1] );
			lit_equivalency.Add_Equivalence_Flat( lit, lit2 );
		}
	}
	else if ( Is_Equivalence_Node( node ) ) {
		Literal lit( node.Var(), true );
		Literal lit2 = Node2Literal( node.ch[1] );
		lit_equivalency.Add_Equivalence_Flat( lit, lit2 );
	}
}

void R2D2_Manager::Shared_Lit_Equivalency( Decision_Node & bnode )  // use _var_seen, _lit_seen
{
	Simple_CDD_Node low( _nodes[bnode.low] );  // NOTE: _nodes might be reallocated
	Simple_CDD_Node high( _nodes[bnode.high] );
	unsigned num_lits0 = 0, num_lits1 = 0;
	if ( low.sym == CDD_SYMBOL_DECOMPOSE ) num_lits0 = Search_First_Non_Literal_Position( bnode.low );
	if ( high.sym == CDD_SYMBOL_DECOMPOSE ) num_lits1 = Search_First_Non_Literal_Position( bnode.high );
	Record_Lit_Equivalency( bnode.low, _lit_equivalency_low );
	Record_Lit_Equivalency( bnode.high, _lit_equivalency_high );
	Shared_Lit_Equivalency_Imp( low.ch, num_lits0, _lit_equivalency_high, _lit_equivalency_low );
	Shared_Lit_Equivalency_Imp( high.ch, num_lits1, _lit_equivalency_low, _lit_equivalency_high );
	_lit_equivalency.Intersection_Flat( _lit_equivalency_low, _lit_equivalency_high );
	_lit_equivalency_low.Reset();
	_lit_equivalency_high.Reset();
	for ( unsigned i = 0; i < num_lits1; i++ ) {
		Literal lit = Node2Literal( high.ch[i] );
		_var_seen[lit.Var()] = true;  // NOTE: lit does not appear in low, otherwise low and high share child
	}
	for ( unsigned i = 0; i < num_lits0; i++ ) {
		Literal lit = Node2Literal( low.ch[i] );
		if ( _var_seen[lit.Var()] ) {
			_lit_equivalency.Add_Equivalence_Flat( Literal( bnode.var, false ), lit );
		}
	}
	for ( unsigned i = 0; i < num_lits1; i++ ) {
		Literal lit = Node2Literal( high.ch[i] );
		_var_seen[lit.Var()] = false;
	}
}

void R2D2_Manager::Shared_Lit_Equivalency_Imp( NodeID * imps, unsigned num_imps, Lit_Equivalency & equivalency, Lit_Equivalency & result_equivalency )  // use _var_seen, _lit_seen
{
	for ( unsigned i = 0; i < num_imps; i++ ) {
		Literal lit = Node2Literal( imps[i] );
		if ( !equivalency.Lit_Renamable( lit ) ) continue;
		if ( result_equivalency.Lit_Renamable( lit ) ) continue;
		Literal lit_equ = equivalency.Rename_Lit_Flat( lit );
		Literal min_lit = lit;
		for ( unsigned j = 0; j < i; j++ ) {
			Literal lit2 = Node2Literal( imps[j] );
			if ( lit_equ == equivalency.Rename_Lit_Flat( lit2 ) ) {  // Reduce the callings of Lit_Equivalency::Find()
				if ( Lit_LT( lit2, min_lit ) ) {
					_lit_vector.push_back( min_lit );
					min_lit = lit2;
				}
				else _lit_vector.push_back( lit2 );
			}
		}
		for ( unsigned j = i + 1; j < num_imps; j++ ) {
			Literal lit2 = Node2Literal( imps[j] );
			if ( lit_equ == equivalency.Rename_Lit_Flat( lit2 ) ) {
				if ( Lit_LT( lit2, min_lit ) ) {
					_lit_vector.push_back( min_lit );
					min_lit = lit2;
				}
				else _lit_vector.push_back( lit2 );
			}
		}
		for ( Literal lit: _lit_vector ) {
			if ( !result_equivalency.Lit_Renamable( lit ) ) {
				result_equivalency.Add_Equivalence_Flat( min_lit, lit );
			}
		}
		_lit_vector.clear();
	}
}

NodeID R2D2_Manager::Remove_Lit_Equivalences( NodeID n, Lit_Equivalency & lit_equivalency )
{
	unsigned i, j, num_lits;
	Simple_CDD_Node node( _nodes[n] );
	if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
		num_lits = Search_First_Non_Literal_Position( n );
		_aux_decom_rnode.ch_size = 0;
		for ( i = 0; i < num_lits; i++ ) {
			Literal lit = Node2Literal( node.ch[i] );
			if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_decom_rnode.Add_Child( node.ch[i] );
		}
		unsigned num_left_lits = _aux_decom_rnode.ch_size;
		for ( ; i < node.ch_size; i++ ) {
			Simple_CDD_Node child( _nodes[node.ch[i]] );
			if ( child.sym == CDD_SYMBOL_KERNELIZE ) {
				_aux_kerne_rnode.ch_size = 0;
				_aux_kerne_rnode.Add_Child( child.ch[0] );
				for ( j = 1; j < child.ch_size; j++ ) {
					Simple_CDD_Node grandch = _nodes[child.ch[j]];
					Literal lit = Node2Literal( grandch.ch[1] );
					if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_kerne_rnode.Add_Child( child.ch[j] );
				}
				unsigned c = Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
				if ( c != NodeID::top ) _aux_decom_rnode.Add_Child( c );
			}
			else if ( Is_Equivalence_Node( _nodes[node.ch[i]] ) ) {
				Literal lit = Node2Literal( child.ch[1] );
				if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_decom_rnode.Add_Child( node.ch[i] );
			}
			else _aux_decom_rnode.Add_Child( node.ch[i] );
		}
		_qsorter.Sort( _aux_decom_rnode.ch + num_left_lits, _aux_decom_rnode.ch_size - num_left_lits );
		return Push_Decomposition_Node( _aux_decom_rnode.ch, _aux_decom_rnode.ch_size );
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		_aux_kerne_rnode.ch_size = 0;
		_aux_kerne_rnode.Add_Child( node.ch[0] );
		for ( i = 1; i < node.ch_size; i++ ) {
			Simple_CDD_Node child( _nodes[node.ch[i]] );
			Literal lit = Node2Literal( child.ch[1] );
			if ( !lit_equivalency.Lit_Renamable( lit ) ) _aux_kerne_rnode.Add_Child( node.ch[i] );
		}
		return Push_Kernelization_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
	}
	else if ( Is_Equivalence_Node( _nodes[n] ) ) {
		Literal lit = Node2Literal( node.ch[1] );
		if ( !lit_equivalency.Lit_Renamable( lit ) ) return n;
		else return NodeID::top;
	}
	else return n;
}

NodeID R2D2_Manager::Add_Kernelization_Node( Rough_CDD_Node & rnode )  // use _many_nodes, _many_equ_nodes, _many_equ_nodes, _aux_decom_rnode, _aux_subst_rnode
{
	assert( rnode.sym == CDD_SYMBOL_KERNELIZE );
	if ( rnode.ch_size == 0 ) return NodeID::top;
	if ( rnode.ch_size == 1 ) return rnode.ch[0];
	NodeID cdd;
	unsigned main_ch_sym = _nodes[rnode.ch[0]].sym;
	if ( main_ch_sym == CDD_SYMBOL_FALSE ) return CDD_SYMBOL_FALSE;
	for ( unsigned i = 1; i < rnode.ch_size; i++ ) {
		assert( _nodes[rnode.ch[i]].ch_size == 2 );
		Verify_Equivalence_Node( _nodes[rnode.ch[i]] );
		NodeID * grandch = _nodes[rnode.ch[i]].ch;
		Literal lit0( _nodes[rnode.ch[i]].Var(), true );
		Literal lit1 = Node2Literal( grandch[1] );
		_lit_equivalency.Add_Equivalence_Flat( lit0, lit1 );
	}
	rnode.ch_size = Transform_Lit_Equivalences( _lit_equivalency, rnode.ch + 1 );
	rnode.ch_size++;
	if ( main_ch_sym == CDD_SYMBOL_TRUE ) cdd = Decompose( rnode.ch, 0, rnode.ch + 1, rnode.ch_size - 1 );
	else if ( main_ch_sym <= _max_var ) cdd = Decompose( rnode.ch, 1, rnode.ch + 1, rnode.ch_size - 1 );
	else {
		unsigned num_ch, num_equ_ch;
		Remove_All_Lit_Equivalences( rnode.ch[0], _many_nodes, num_ch, _many_equ_nodes, num_equ_ch );
		for ( unsigned i = 0; i < num_equ_ch; i++ ) {
			Simple_CDD_Node equ_ch( _nodes[_many_equ_nodes[i]] );
			Literal lit0( equ_ch.Var(), true );
			Literal lit1 = Node2Literal( equ_ch.ch[1] );
			_lit_equivalency.Add_Equivalence( lit0, lit1 );
//			_lit_equivalency.Display( cerr );  // ToRemove
		}
		num_equ_ch = Transform_Lit_Equivalences( _lit_equivalency, _many_equ_nodes );
		cdd = Decompose( _many_nodes, num_ch, _many_equ_nodes, num_equ_ch );
	}
	_lit_equivalency.Reset();
	return cdd;
}

void R2D2_Manager::Remove_All_Lit_Equivalences( NodeID parent, NodeID * rest_nodes, unsigned & num_rest, NodeID * rm_nodes, unsigned & num_rm )
{
	unsigned i, j;
	Simple_CDD_Node node( _nodes[parent] );
	num_rest = num_rm = 0;
	if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
		for ( i = 0; i < node.ch_size; i++ ) {
			CDD_Node & ch = _nodes[node.ch[i]];
			if ( ch.sym == CDD_SYMBOL_KERNELIZE ) {
				rest_nodes[num_rest] = ch.ch[0];
				num_rest += ( ch.ch[0] != NodeID::top );
				for ( j = 1; j < ch.ch_size; j++ ) {
					rm_nodes[num_rm++] = ch.ch[j];
				}
			}
			else if ( Is_Equivalence_Node( ch ) ) rm_nodes[num_rm++] = node.ch[i];
			else rest_nodes[num_rest++] = node.ch[i];
		}
	}
	else if ( node.sym == CDD_SYMBOL_KERNELIZE ) {
		rest_nodes[num_rest] = node.ch[0];
		num_rest += ( node.ch[0] != NodeID::top );
		for ( j = 1; j < node.ch_size; j++ ) {
			rm_nodes[num_rm++] = node.ch[j];
		}
	}
	else if ( Is_Equivalence_Node( _nodes[parent] ) ) rm_nodes[num_rm++] = parent;
}

NodeID R2D2_Manager::Decompose( NodeID * dnodes, unsigned num, NodeID * equ_nodes, unsigned num_equ )  // use _aux_decom_rnode, _aux_kerne_rnode, _equ_node_seen
{
	unsigned i, j;
	_aux_decom_rnode.ch_size = 0;
	for ( i = 0; i < num; i++ ) {
		_aux_kerne_rnode.ch[0] = dnodes[i];
		_aux_kerne_rnode.ch_size = 1;
		for ( unsigned j = 0; j < num_equ; j++ ) {
			if ( _equ_node_seen[j] ) continue;
			Variable var = _nodes[equ_nodes[j]].Var();
			if ( Var_Apppeared( dnodes[i], var ) ) {
				_aux_kerne_rnode.Add_Child( equ_nodes[j] );
				_equ_node_seen[j] = true;
			}
		}
		if ( _aux_kerne_rnode.ch_size == 1 ) _aux_decom_rnode.Add_Child( dnodes[i] );
		else if ( Is_Fixed( dnodes[i] ) ) {
			Simple_CDD_Node main_ch( _nodes[_aux_kerne_rnode.ch[0]] );
			bool sign = ( main_ch.ch[1] == NodeID::top );
			for ( j = 1; j < _aux_kerne_rnode.ch_size; j++ ) {
				_aux_kerne_rnode.ch[j] = _nodes[_aux_kerne_rnode.ch[j]].ch[sign];
			}
			_qsorter.Sort( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size );
			_aux_decom_rnode.Add_Child( Push_Decomposition_Node( _aux_kerne_rnode.ch, _aux_kerne_rnode.ch_size ) );
		}
		else _aux_decom_rnode.Add_Child( Push_Node( _aux_kerne_rnode ) );
	}
	for ( i = 0; i < num_equ; i++ ) {
		bool tmp = _equ_node_seen[num_equ - 1];
		_equ_node_seen[num_equ - 1] = false;
		for ( ; _equ_node_seen[i]; i++ ) {}
		_equ_node_seen[num_equ - 1] = tmp;
		if ( _equ_node_seen[i] ) break;
		unsigned equ_node_sym = _nodes[equ_nodes[i]].sym;
		_aux_kerne_rnode.ch[0] = NodeID::top;
		_aux_kerne_rnode.ch[1] = equ_nodes[i];
		_aux_kerne_rnode.ch_size = 2;
		for ( j = i + 1; j < num_equ; j++ ) {
			if ( _equ_node_seen[j] ) continue;
			CDD_Node & equ_node2 = _nodes[equ_nodes[j]];
			if ( equ_node2.sym == equ_node_sym ) {
				_aux_kerne_rnode.Add_Child( equ_nodes[j] );
				_equ_node_seen[j] = true;
			}
		}
		if ( _aux_kerne_rnode.ch_size == 2 ) _aux_decom_rnode.Add_Child( equ_nodes[i] );
		else _aux_decom_rnode.Add_Child( Push_Node( _aux_kerne_rnode ) );
	}
	NodeID n;
	if ( _aux_decom_rnode.ch_size == 1 ) n = _aux_decom_rnode.ch[0];
	else {
		_qsorter.Sort( _aux_decom_rnode.ch, _aux_decom_rnode.ch_size );
		n = Push_Node( _aux_decom_rnode );
	}
	for ( j = 0; j < num_equ; j++ ) {
		_equ_node_seen[j] = false;
	}
	return n;
}

bool R2D2_Manager::Var_Apppeared( NodeID n, Variable var )
{
	bool appeared = false;
	_node_stack[0] = n;
	unsigned num_node_stack = 1;
	while ( num_node_stack > 0 ) {
		NodeID top = _node_stack[--num_node_stack];
		CDD_Node & topn = _nodes[top];
		if ( Is_Const( top ) ) continue;
		if ( topn.sym <= _max_var ) {
			if ( topn.sym == var ) {
				appeared = true;
				break;
			}
			else if ( Var_LT( var, Variable( topn.sym ) ) ) continue;
		}
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
	for ( unsigned i = 0; i < _visited_nodes.size(); i++ ) {
		_nodes[_visited_nodes[i]].infor.visited = false;
	}
	_visited_nodes.clear();
	return appeared;
}

void R2D2_Manager::Verify_R2D2( NodeID root )
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

void R2D2_Manager::Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void R2D2_Manager::Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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
	if ( Is_Literal( bnode.low ) ) {
		if ( _nodes[bnode.high].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.low );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			assert( !Search_Exi_Nonempty( _nodes[bnode.high].ch, _nodes[bnode.high].ch_size, lit_neg_node ) );
		}
	}
	if ( Is_Literal( bnode.high ) ) {
		if ( _nodes[bnode.low].sym == CDD_SYMBOL_DECOMPOSE ) {
			Literal lit = Node2Literal( bnode.high );
			NodeID lit_neg_node = NodeID::literal( ~lit );
			assert( !Search_Exi_Nonempty( _nodes[bnode.low].ch, _nodes[bnode.low].ch_size, lit_neg_node ) );
		}
	}
	Shared_Lit_Equivalency( bnode );
	unsigned num_equ = Transform_Lit_Equivalences( _lit_equivalency, _many_equ_nodes );
	if ( num_equ > 0 ) {
		Display( cerr );
		cerr << "ERROR[RRCDD]: Some equivalence can construct from Node " << bnode.low << " and Node " << bnode.high << "!" << endl;
		assert( num_equ == 0 );
	}
	_lit_equivalency.Reset();
	assert( _lit_equivalency.Output_Equivalences( _many_lits ) == 0 );
}

void R2D2_Manager::Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
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

void R2D2_Manager::Verify_Kernelization_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets )
{
	if ( node.ch[0] == NodeID::top ) assert( node.ch_size >= 3 );
	else assert( node.ch_size >= 2 );
	assert( _nodes[node.ch[0]].sym <= _max_var || _nodes[node.ch[0]].sym == CDD_SYMBOL_TRUE );
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

void R2D2_Manager::Verify_Equivalence_Node( CDD_Node & node )
{
	assert( node.ch_size == 2 );
	assert( node.sym <= _max_var );
	assert( node.ch[0] <= NodeID::literal( _max_var, true ) && node.ch[1] <= NodeID::literal( _max_var, true ) );
	assert( node.ch[0] == ( node.ch[1] ^ 0x01 ) );
	CDD_Node & child = _nodes[node.ch[0]];
	assert( Var_LT( node.Var(), child.Var() ) );
}


}

