#ifndef _RRCDD_h_
#define _RRCDD_h_

#include "RCDD.h"


namespace KCBox {


class R2D2_Manager: public RCDD_Manager
{
    friend class R2D2_Compiler;
protected:  // auxiliary memory
	Lit_Equivalency _lit_equivalency_low;  // used for compute shared literal equivalences
	Lit_Equivalency _lit_equivalency_high;  // used for compute shared literal equivalences
	vector<Literal> _lit_vector;
public:
	R2D2_Manager( Variable max_var, unsigned estimated_node_num = LARGE_HASH_TABLE );
	R2D2_Manager( Chain & order, unsigned estimated_node_num = LARGE_HASH_TABLE );
	R2D2_Manager( istream & fin );
	R2D2_Manager( R2D2_Manager & other );
	~R2D2_Manager();
	void Reorder( Chain & new_order );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
public: // querying
protected:
public: // transformation
	CDD Add_Node( Rough_CDD_Node & rnode );
	CDD Add_Decision_Node( Decision_Node & bnode );
	CDD Add_Kernelization_Node( Rough_CDD_Node & rnode );
protected:
	NodeID Extract_Share_No_Check( Decision_Node & bnode );
	NodeID Extract_Lit_Equivalences( Decision_Node & bnode );
	unsigned Lit_Equivalences( NodeID n, NodeID * equ_nodes );
	void Record_Lit_Equivalency( NodeID n, Lit_Equivalency & lit_equivalency );
	void Shared_Lit_Equivalency( Decision_Node & bnode );
	void Shared_Lit_Equivalency_Imp( NodeID * imps, unsigned num_imps, Lit_Equivalency & equivalency, Lit_Equivalency & result_equivalency );
	NodeID Remove_Lit_Equivalences( NodeID n, Lit_Equivalency & lit_equivalency );
	void Remove_All_Lit_Equivalences( NodeID parent, NodeID * rest_nodes, unsigned & num_rest, NodeID * rm_nodes, unsigned & num_rm );
	NodeID Decompose( NodeID * dnodes, unsigned num, NodeID * equ_nodes, unsigned num_equ );
	bool Var_Apppeared( NodeID n, Variable var );  // var appears in Vars(n)
public: // transformation
	CDD Convert_Up( OBDD_Manager & bdd_manager, BDD bdd );
	CDD Convert_Up( OBDDC_Manager & bddc_manager, BDDC bddc );
	BDD Convert_Down( CDD cdd, OBDD_Manager & bdd_manager );
	BDDC Convert_Down( CDD cdd, OBDDC_Manager & bddc_manager );
protected:
    void Condition_Min_Substitution( NodeID root, Decision_Node & bnode );
public: // transforming
	CDD Condition( CDD root, vector<int> elits );
protected:
	void Verify_R2D2( CDD root );
	void Verify_Node( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decision_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Decomposition_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Kernelization_Node( CDD_Node & node, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Verify_Equivalence_Node( CDD_Node & node );
protected:  // basic functions
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
