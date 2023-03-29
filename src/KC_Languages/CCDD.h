#ifndef _CCDD_h_
#define _CCDD_h_
/// NOTE: unfinished

#include "CDD.h"
#include "RRCDD.h"
#include "../Primitive_Types/Lit_Equivalency.h"


namespace KCBox {


class CCDD_Manager: public CDD_Manager, public Linear_Order
{
    friend class CCDD_Compiler;
protected:  // auxiliary memory
	Lit_Equivalency _lit_equivalency;
	Lit_Equivalency _lit_equivalency_low;  // used for compute shared literal equivalences
	Lit_Equivalency _lit_equivalency_high;  // used for compute shared literal equivalences
	Variable * _many_vars;
	Literal * _many_lits;
	NodeID * _many_nodes;  // stored temporary children
	NodeID * _many_lit_nodes;  // stored temporary children
	NodeID * _many_equ_nodes;  // stored temporary equ children
	bool * _equ_node_seen;  // whether a equ node in an array appears
	NodeID ** _node_sets;
	unsigned * _node_set_sizes;
	SetID * _many_sets;
	Rough_CDD_Node _aux_rnode;
	Rough_CDD_Node _aux_decom_rnode;
	Rough_CDD_Node _aux_kerne_rnode;
	Rough_CDD_Node _condition_rnode;
protected:  // used for condition
	Hash_Cluster<Literal> _lit_sets;
	Literal * _decision_stack;
	unsigned _num_decisions;
	unsigned * _decision_levels;
	unsigned _num_levels;
	unsigned * _cache_stack;
public:
	CCDD_Manager( Variable max_var, unsigned estimated_node_num = LARGE_HASH_TABLE );
	CCDD_Manager( Chain & order, unsigned estimated_node_num = LARGE_HASH_TABLE );
	CCDD_Manager( istream & fin );
	CCDD_Manager( CCDD_Manager & other );
	~CCDD_Manager();
	void Reorder( const Chain & new_order );
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	void Enlarge_Max_Var( Chain & new_order );
	void Load_Nodes( RCDD_Manager & other );
	void Display( ostream & out );
	void Display_Stat( ostream & out );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
public: // querying
	bool Entail_Clause( CDD root, Clause & cl );
	bool Entail_CNF( CDD root, CNF_Formula & cnf );
	BigInt Count_Models( CDD root );
	void Mark_Models( CDD root, vector<BigFloat> & results );
	void Probabilistic_Model( CDD root, vector<float> & prob_values );
	void Uniformly_Sample( Random_Generator & rand_gen, CDD root, vector<vector<bool>> & samples );
	void Statistics( CDD root );
protected:
	void Assign( Literal lit ) { if ( Lit_Undecided( lit ) ) { _assignment[lit.Var()] = lit.Sign(); _decision_stack[_num_decisions++] = lit; } }
	SetID Pick_Less_Equ_Decisions( unsigned n, SetID pre_lits );  // select decisions whose variables less than the current decision node
	bool Propagate_New_Equ_Decisions( unsigned n );
	void Cancel_Current_Equ_Decisions();
public: // transformation
	CDD Add_Node( Rough_CDD_Node & rnode );
	CDD Add_Decision_Node( Decision_Node & bnode );
	CDD Add_Decomposition_Node( Rough_CDD_Node & rnode );
	CDD Add_Kernelization_Node( Rough_CDD_Node & rnode );
	CDD Add_Equivalence_Node( int elit, int elit2 );  // literal in DAMICS
	unsigned Add_Equivalence_Nodes( const vector<Literal> & lit_equivalences, NodeID * nodes );
	unsigned Add_Equivalence_Nodes( Literal * lit_pairs, unsigned num_pairs, NodeID * nodes );
protected:
	NodeID Extract_Leaf_Left_No_Check( Decision_Node & bnode );
	NodeID Extract_Leaf_Right_No_Check( Decision_Node & bnode );
	NodeID Extract_Share_No_Check( Decision_Node & bnode );
	NodeID Extract_Part_Left_No_Check( Decision_Node & bnode );
	NodeID Remove_Child_No_Check_GE_3( NodeID parent, NodeID child );
	NodeID Extract_Part_Right_No_Check( Decision_Node & bnode );
	NodeID Extract_Lit_Equivalences( Decision_Node & bnode );
	NodeID Extract_Lit_Equivalence_Left_Lit( Decision_Node & bnode );
	NodeID Extract_Lit_Equivalence_Right_Lit( Decision_Node & bnode );
	NodeID Transform_Lit_Equivalence( Literal lit, Literal lit2 );
	unsigned Lit_Equivalences( NodeID n, NodeID * equ_nodes );
	void Record_Lit_Equivalency( unsigned n, Lit_Equivalency & lit_equivalency );
	void Shared_Lit_Equivalency( Decision_Node & bnode );
	unsigned Intersection_Equ_Nodes( unsigned * equ_nodes1, unsigned size1, unsigned * equ_nodes2, unsigned size2 );  // NOTE: equ_nodes1 must have an extra bit
	unsigned Finest( Rough_CDD_Node & rnode );
	unsigned Finest_Exi( Rough_CDD_Node & rnode );
	NodeID Add_Child( NodeID parent, NodeID child );
	NodeID Add_Children( NodeID parent, NodeID * children, unsigned num_ch );
	NodeID Remove_Child( NodeID parent, NodeID child );
	NodeID Remove_Child_No_Check( NodeID parent, NodeID child ); // "child" is really a child of "parent"
	NodeID Remove_Child_No_Check_Change( unsigned parent, unsigned child ); // called by "Condition_Min_Change"
	NodeID Remove_Child_No_Check_Rough( Rough_BDDC_Node & parent, unsigned child );
	NodeID Remove_Child_No_Check_Rough_Change( Rough_BDDC_Node & parent, unsigned child );
	NodeID Remove_Children( NodeID parent, NodeID * children, unsigned num_ch );
	NodeID Remove_Lit_Equivalences( NodeID n, Lit_Equivalency & lit_equivalency );
	NodeID Push_Decomposition_Node_After_Extracting( Rough_CDD_Node & rnode );
	NodeID Push_Core_After_Extracting( Decision_Node & bnode );
	unsigned Transform_Lit_Equivalences( Lit_Equivalency & lit_equivalency, NodeID * equ_nodes );
	NodeID Replace_Child( unsigned parent, unsigned child, unsigned new_child );
	NodeID Replace_Child_Nonconstant( unsigned parent, unsigned child, unsigned new_child ); // result is not constant
	NodeID Replace_Child_Internal( unsigned parent, unsigned child, unsigned new_child ); // new_child is internal
	NodeID Replace_Child_Internal_Same( unsigned parent, unsigned child, unsigned new_child ); // the symbols of "child" and "new_child" are same
	NodeID Replace_Child_Internal_Different( unsigned parent, unsigned child, unsigned new_child ); // the symbols of "child" and "new_child" are different
	NodeID Replace_Child_Nonconstant_Change( unsigned parent, unsigned child, unsigned new_child ); // called by "Condition_Min_Change"
	NodeID Replace_Child_Internal_Change( unsigned parent, unsigned child, unsigned new_child );
	NodeID Replace_Child_Internal_Different_Change( unsigned parent, unsigned child, unsigned new_child ); // change infor.min_var and infor.num_var
	NodeID Replace_Child_Rough( Rough_BDDC_Node & parent, unsigned child, unsigned new_child );
protected: // called by Compiler
//	CDD Add_Decision_Node_Nocheck( Decision_Node & bnode );
//	CDD Add_Decomposition_Node_Nocheck( Rough_CDD_Node & rnode );
//	CDD Add_Kernelization_Node_Nocheck( Rough_CDD_Node & rnode );
protected:
    void Condition_Min_Substitution( NodeID root, Decision_Node & bnode );
    unsigned Finest_Last( Rough_CDD_Node & rnode );
public: // transforming
	CDD Condition( CDD root, vector<int> elits );
protected:
	void Verify_CCDD( CDD root );
	void Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Kernelization_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Equivalence_Node( CDD_Node & node );
	void Verify_Entail_CNF( CDD root, CNF_Formula & cnf );
	void Verify_UNSAT_Under_Assignment( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Model( CDD root, const vector<bool> & sample );
	void Display_Var_Sets( ostream & out, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:
	void Compute_Var_Sets( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	SetID Pick_Effective_Equ_Decisions( unsigned n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:  // basic functions
	NodeID Push_Decomposition_Node( NodeID * ch, unsigned size )
	{
		return Push_Conjunction_Node( CDD_SYMBOL_DECOMPOSE, ch, size );
	}
	NodeID Push_Kernelization_Node( NodeID * ch, unsigned size )
	{
		if ( ch[0] == NodeID::top && size == 2 ) return ch[1];
		else return Push_Conjunction_Node( CDD_SYMBOL_KERNELIZE, ch, size );
	}
	NodeID Push_Equivalence_Node( Literal lit, Literal lit2 )
	{
		assert( Lit_LT( lit, lit2 ) );
		NodeID ch[2];
		ch[lit.NSign()] = NodeID::literal( ~lit2 );
		ch[lit.Sign()] = NodeID::literal( lit2 );
		Decision_Node bnode( lit.Var(), ch[0], ch[1] );
		return Push_Node( bnode );  // Not check low == high
	}
	NodeID Update_Child( NodeID n, unsigned pos, NodeID child )
	{
	    assert( _nodes[n].sym == CDD_SYMBOL_DECOMPOSE && _nodes[n].ch[pos] != child );
	    NodeID * ch = new NodeID [_nodes[n].ch_size];
        ch[0] = _nodes[n].ch[0];
        ch[1] = _nodes[n].ch[1];
        for ( unsigned i = 2; i < _nodes[n].ch_size; i++ ) ch[i] = _nodes[n].ch[i];
        ch[pos] = child;
        Insert_Sort_Position( ch, _nodes[n].ch_size, pos );
		CDD_Node node( _nodes[n].sym, ch, _nodes[n].ch_size );
		return Push_Node( node );
	}
	unsigned Search_First_Non_Literal_Position( unsigned n )
	{
		assert( _nodes[n].sym == CDD_SYMBOL_DECOMPOSE );
		if ( Is_Fixed( _nodes[n].ch[_nodes[n].ch_size - 1] ) ) return _nodes[n].ch_size;
		if ( !Is_Fixed( _nodes[n].ch[0] ) ) return 0;
		unsigned i;
		for ( i = _nodes[n].ch_size - 2; !Is_Fixed( _nodes[n].ch[i] ); i-- );
		return i + 1;
	}
	unsigned Search_First_Non_Literal_Position( CDD_Node & node )
	{
		assert( node.sym == CDD_SYMBOL_DECOMPOSE );
		if ( Is_Fixed( node.ch[node.ch_size - 1] ) ) return node.ch_size;
		if ( !Is_Fixed( node.ch[0] ) ) return 0;
		unsigned i;
		for ( i = node.ch_size - 2; !Is_Fixed( node.ch[i] ); i-- );
		return i + 1;
	}
	bool Is_Equivalence_Node( CDD_Node & node )
	{
		if ( node.sym <= _max_var && Is_Literal( node.ch[0] ) && Is_Literal( node.ch[1] ) ) {
			return node.ch[0] == ( node.ch[1] ^ 0x01 );
		}
		else return false;
	}
public:
	static void Debug()
	{
		ifstream fin( "result.cdd" );
		CCDD_Manager cdd_manager( fin );
		fin.close();
//		cdd_manager.Display_Stat( cout );
		Rough_CDD_Node rnode( cdd_manager.Max_Var() );
		Decision_Node bnode;
		bnode.var = 1;
		bnode.low = 7999997;
		bnode.high = 8000011;
		cdd_manager.Add_Decision_Node( bnode );
//		CNF_Formula cnf( cdd_manager.Max_Var() );
//		cnf.Add_Ternary_Clause( 20, 6, 10 );
//		cnf.Add_Ternary_Clause( 13, 16, 19 );
//		cdd_manager.Verify_Entail_CNF( cdd, cnf );
//		Debug_Print_Visit_Number( cerr, __LINE__ );
	}
};


}


#endif  // _CDD_h_
