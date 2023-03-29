#ifndef _RCDD_h_
#define _RCDD_h_

#include "CDD.h"
#include "../Primitive_Types/Lit_Equivalency.h"


namespace KCBox {


class RCDD_Manager: public CDD_Manager, public Linear_Order
{
    friend class RCDD_Compiler;
protected:  // auxiliary memory
	Lit_Equivalency _lit_equivalency;
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
	Rough_CDD_Node _aux_rnode2;
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
	RCDD_Manager( Variable max_var, unsigned estimated_node_num = LARGE_HASH_TABLE );
	RCDD_Manager( Chain & order, unsigned estimated_node_num = LARGE_HASH_TABLE );
	RCDD_Manager( istream & fin );
	RCDD_Manager( RCDD_Manager & other );
	~RCDD_Manager();
	void Reorder( Chain & new_order );
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	void Enlarge_Max_Var( Chain & new_chain );
	void Display( ostream & out );
	void Display_Stat( ostream & out );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
public: // querying
	bool Entail_Clause( CDD root, Clause & cl );
	bool Entail_CNF( CDD root, CNF_Formula & cnf );
	BigInt Count_Models( CDD root );
	BigInt Count_Models_Opt( CDD root );
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
	NodeID Extract_Share_Semi_Check( Decision_Node & bnode );
	NodeID Extract_Part_Left_No_Check( Decision_Node & bnode );
	NodeID Remove_Child_No_Check_GE_3( NodeID parent, NodeID child );
	NodeID Extract_Part_Right_No_Check( Decision_Node & bnode );
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
public: // transformation
	CDD Convert_Up( OBDD_Manager & bdd_manager, BDD bdd );
	CDD Convert_Up( OBDDC_Manager & bddc_manager, BDDC bddc );
	BDD Convert_Down( CDD cdd, OBDD_Manager & bdd_manager );
	BDDC Convert_Down( CDD cdd, OBDDC_Manager & bddc_manager );
protected:
    void Condition_Min_Substitution( NodeID root, Decision_Node & bnode );
    unsigned Finest_Last( Rough_CDD_Node & rnode );
public: // transforming
	CDD Condition( CDD root, vector<int> elits );
protected:
	void Verify_RCDD( CDD root );
	void Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Substitution_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Equivalence_Node( CDD_Node & node );
	void Verify_Entail_CNF( CDD root, CNF_Formula & cnf );
	void Verify_UNSAT_Under_Assignment( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:
	void Compute_Var_Sets( CDD root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	SetID Pick_Effective_Equ_Decisions( unsigned n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:  // basic functions
	Variable Node_GLB( unsigned n )
	{
		CDD_Node & node = _nodes[n];
		if ( node.sym <= _max_var ) return node.Var();
		else if ( node.sym == CDD_SYMBOL_DECOMPOSE ) {
			bool comp = Var_LT( _nodes[node.ch[0]].Var(), _nodes[node.ch[1]].Var() );
			Variable min = comp ? _nodes[node.ch[0]].Var() : _nodes[node.ch[1]].Var();
			for ( unsigned i = 2; i < node.ch_size; i++ ) {
				if ( Var_LT( _nodes[node.ch[i]].Var(), min ) ) min = _nodes[node.ch[i]].Var();
			}
			return min;
		}
		else return node.ch[0] != NodeID::top ? _nodes[node.ch[0]].Var() : _nodes[node.ch[1]].Var();
	}
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
		RCDD_Manager cdd_manager( fin );
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
