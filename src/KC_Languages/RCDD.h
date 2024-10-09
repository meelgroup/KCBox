#ifndef _RCDD_h_
#define _RCDD_h_

#include "CCDD.h"
#include "../Primitive_Types/Lit_Equivalency.h"


namespace KCBox {


class RCDD_Manager: public CCDD_Manager
{
    friend class RCDD_Compiler;
public:
	RCDD_Manager( Variable max_var, dag_size_t estimated_node_num = LARGE_HASH_TABLE );
	RCDD_Manager( Chain & order, dag_size_t estimated_node_num = LARGE_HASH_TABLE );
	RCDD_Manager( istream & fin );
	RCDD_Manager( RCDD_Manager & other );
	~RCDD_Manager();
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	void Display( ostream & out );
	void Display_Stat( ostream & out );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
public: // querying
	bool Entail_Clause( const CDDiagram & rcdd, Clause & cl );
	bool Entail_CNF( const CDDiagram & rcdd, CNF_Formula & cnf );
	BigInt Count_Models( const CDDiagram & rcdd );
protected:
	void Assign( Literal lit ) { if ( Lit_Undecided( lit ) ) { _assignment[lit.Var()] = lit.Sign(); _decision_stack[_num_decisions++] = lit; } }
	SetID Pick_Less_Equ_Decisions( NodeID n, SetID pre_lits );  // select decisions whose variables less than the current decision node
	bool Propagate_New_Equ_Decisions( NodeID n );
	void Cancel_Current_Equ_Decisions();
	BigInt Count_Models( NodeID root ) { return CCDD_Manager::Count_Models( root ); }
public: // transformation
	NodeID Add_Node( Rough_CDD_Node & rnode );
	NodeID Add_Decision_Node( Decision_Node & bnode );
	NodeID Add_Decomposition_Node( Rough_CDD_Node & rnode );
	NodeID Add_Kernelization_Node( Rough_CDD_Node & rnode );
	NodeID Add_Equivalence_Node( int elit, int elit2 );  // literal in DAMICS
	unsigned Add_Equivalence_Nodes( const vector<Literal> & lit_equivalences, NodeID * nodes );
	unsigned Add_Equivalence_Nodes( Literal * lit_pairs, unsigned num_pairs, NodeID * nodes );
protected:
	NodeID Extract_Leaf_Left_No_Check( Decision_Node & bnode );
	NodeID Extract_Leaf_Right_No_Check( Decision_Node & bnode );
	NodeID Extract_Share_Semi_Check( Decision_Node & bnode );
	NodeID Extract_Part_Left_No_Check( Decision_Node & bnode );
	NodeID Remove_Child_No_Check_GE_3( NodeID parent, NodeID child );
	NodeID Extract_Part_Right_No_Check( Decision_Node & bnode );
	NodeID Finest( Rough_CDD_Node & rnode );
	NodeID Finest_Exi( Rough_CDD_Node & rnode );
	NodeID Add_Child( NodeID parent, NodeID child );
	NodeID Add_Children( NodeID parent, NodeID * children, unsigned num_ch );
	NodeID Remove_Child( NodeID parent, NodeID child );
	NodeID Remove_Child_No_Check( NodeID parent, NodeID child ); // "child" is really a child of "parent"
	NodeID Remove_Children( NodeID parent, NodeID * children, unsigned num_ch );
	unsigned Transform_Lit_Equivalences( Lit_Equivalency & lit_equivalency, NodeID * equ_nodes );
public: // transformation
	CDDiagram Convert_Up( OBDD_Manager & bdd_manager, const Diagram & bdd );
	CDDiagram Convert_Up( OBDDC_Manager & bddc_manager, const Diagram & bddc );
	Diagram Convert_Down( const CDDiagram & rcdd, OBDD_Manager & bdd_manager );
	Diagram Convert_Down( const CDDiagram & rcdd, OBDDC_Manager & bddc_manager );
protected:
	NodeID Finest_Last( Rough_CDD_Node & rnode );
public: // transforming
	CDDiagram Condition( const CDDiagram & rcdd, vector<int> elits );
protected:
	void Verify_RCDD( NodeID root );
	void Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Kernelization_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Equivalence_Node( CDD_Node & node );
	void Verify_Entail_CNF( NodeID root, CNF_Formula & cnf );
	void Verify_UNSAT_Under_Assignment( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:
	void Compute_Var_Sets( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	SetID Pick_Effective_Equ_Decisions( NodeID n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:  // basic functions
	Variable Node_GLB( NodeID n )
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
	unsigned Search_First_Non_Literal_Position( NodeID n )
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
