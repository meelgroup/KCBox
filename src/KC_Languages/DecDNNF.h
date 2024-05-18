#ifndef _DecDNNF_h_
#define _DecDNNF_h_

#include "CDD.h"


namespace KCBox {


class DecDNNF_Manager: public CDD_Manager
{
    friend class DNNF_Compiler;
protected:  // auxiliary memory
	Variable * _many_vars;
	Literal * _many_lits;
	NodeID * _many_nodes;  // stored temporary children
	NodeID ** _node_sets;
	unsigned * _node_set_sizes;
	SetID * _many_sets;
	Rough_CDD_Node _aux_rnode;
public:
	DecDNNF_Manager( Variable max_var, unsigned estimated_node_num = LARGE_HASH_TABLE );
	DecDNNF_Manager( istream & fin );
	DecDNNF_Manager( DecDNNF_Manager & other );
	~DecDNNF_Manager();
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	void Enlarge_Max_Var( Variable & max_var );
	CDDiagram Generate_DNNF( NodeID root ) { assert( root < _nodes.Size() );  return Generate_CDD( root ); }
	void Display( ostream & out );
	void Display_Stat( ostream & out );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
public: // querying
	bool Entail_Clause( const CDDiagram & dnnf, Clause & cl );
	bool Entail_CNF( const CDDiagram & dnnf, CNF_Formula & cnf );
	bool Decide_SAT( const CDDiagram & dnnf, const vector<Literal> & assignment );
	BigInt Count_Models( const CDDiagram & dnnf ) { assert( Contain( dnnf ) );  return Count_Models( dnnf.Root() ); }
	BigFloat Count_Models( const CDDiagram & dnnf, const vector<double> & weights );  // NOTE: weights[lit] + weights[~lit] == 1
	BigInt Count_Models( const CDDiagram & dnnf, const vector<Literal> & assignment );
	BigInt Count_Models_With_Condition( const CDDiagram & dnnf, const vector<Literal> & term );
	BigFloat Count_Models_With_Condition( const CDDiagram & dnnf, const vector<double> & weights, const vector<Literal> & term );
	void Mark_Models( const CDDiagram & dnnf, vector<BigFloat> & results );
	void Probabilistic_Model( const CDDiagram & dnnf, vector<float> & prob_values );
	void Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples );
	void Mark_Models( const CDDiagram & dnnf, const vector<double> & weights, vector<BigFloat> & results );
	void Probabilistic_Model( const CDDiagram & dnnf, const vector<double> & weights, vector<double> & prob_values );
	void Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, const vector<double> & weights, vector<vector<bool>> & samples );
	void Uniformly_Sample( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples, const vector<Literal> & assignment );
	void Uniformly_Sample_With_Condition( Random_Generator & rand_gen, const CDDiagram & dnnf, vector<vector<bool>> & samples, const vector<Literal> & term );
	void Uniformly_Sample_With_Condition( Random_Generator & rand_gen, const CDDiagram & dnnf, const vector<double> & weights, vector<vector<bool>> & samples, const vector<Literal> & term );
	void Statistics( const CDDiagram & dnnf );
protected:
	bool Decide_SAT_Under_Assignment( NodeID root );
	BigInt Count_Models( NodeID root );
	BigInt Count_Models_Under_Assignment( NodeID root, unsigned assignment_size );
	void Mark_Models_Under_Assignment( NodeID root, const vector<double> & weights, vector<BigFloat> & results );
	void Uniformly_Sample( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & counts );
	void Mark_Models_Under_Assignment( NodeID root, vector<BigFloat> & results );
	void Uniformly_Sample_Under_Assignment( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & prob_values );
public: // transformation
	NodeID Add_Node( Rough_CDD_Node & rnode );
	NodeID Add_Decision_Node( Decision_Node & bnode );
	NodeID Add_Decomposition_Node( Rough_CDD_Node & rnode );
protected:
	NodeID Extract_Leaf_Left_No_Check( Decision_Node & bnode );
	NodeID Extract_Leaf_Right_No_Check( Decision_Node & bnode );
	NodeID Extract_Share_No_Check( Decision_Node & bnode );
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
protected:
	unsigned Finest_Last( Rough_CDD_Node & rnode );
public: // transforming
	CDDiagram Condition( const CDDiagram & dnnf, const vector<Literal> & term );
protected:
	void Verify_DecDNNF( NodeID root );
	void Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Entail_CNF( NodeID root, CNF_Formula & cnf );
	void Verify_UNSAT_Under_Assignment( NodeID root );
	void Verify_Model( NodeID root, const vector<bool> & sample );
	void Display_Var_Sets( ostream & out, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:
	void Compute_Var_Sets( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	SetID Pick_Effective_Equ_Decisions( unsigned n, SetID pre_lits, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:  // basic functions
	NodeID Push_Decomposition_Node( NodeID * ch, unsigned size )
	{
		return Push_Conjunction_Node( CDD_SYMBOL_DECOMPOSE, ch, size );
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
		DecDNNF_Manager cdd_manager( fin );
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


#endif  // _DNNF_h_
