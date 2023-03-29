#ifndef _RCDD_Compiler_h_
#define _RCDD_Compiler_h_

#include "../KC_Languages/OBDD[AND].h"
#include "../KC_Languages/RCDD.h"
#include "../KC_Languages/RRCDD.h"
#include "CDD_Compiler.h"


namespace KCBox {


class RCDD_Compiler: public CDD_Compiler
{
protected:
public:
	RCDD_Compiler();
	~RCDD_Compiler();
	void Reset();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	CDD Compile( RCDD_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );  // Reset outside
protected:
	NodeID Make_Root_Node( RCDD_Manager & manager, NodeID node );
	NodeID Make_Kernelized_Conjunction_Node( RCDD_Manager & manager, NodeID node );
	void Choose_Running_Options( Heuristic heur, Chain & vorder );
	void Compute_Var_Order_Automatical();
	void Choose_Implicate_Computing_Strategy();
	void Reorder_Manager( RCDD_Manager & manager );
protected:
	void Compile_With_Implicite_BCP( RCDD_Manager & manager );
	NodeID Make_Node_With_Imp( RCDD_Manager & manager, NodeID node );
	NodeID Make_Decision_Node( RCDD_Manager & manager, NodeID low, NodeID high );
	NodeID Make_Node_With_Imp( RCDD_Manager & manager, NodeID * nodes, unsigned num );
protected:
	void Verify_Result_Component( Component & comp, RCDD_Manager & manager, NodeID result );
protected:
	void Compile_With_SAT_Imp_Computing( RCDD_Manager & manager );  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP( RCDD_Manager & manager );
	bool Estimate_Hardness( Component & comp );
	lbool Try_Kernelization( RCDD_Manager & manager );  // return whether solved by this function
	bool Estimate_Kernelization_Effect();
	bool Estimate_Kernelization_Effect_Enough_Decisions( unsigned step );
	void Leave_Kernelization( RCDD_Manager & manager );
protected:
	void Compile_Layered_Kernelization( RCDD_Manager & manager );  // employ SAT engine to compute implied literals
	void Construct_Search_Graph( Search_Graph<NodeID> & graph, Variable upper_bound );  // employ SAT engine to compute implied literals
	Variable Try_Demarcation( Search_Graph<NodeID> & graph, Variable upper_bound );
	void Update_Var_Order_Automatical();
	void Update_Var_Order_Min_Fill_Heuristic();
	Greedy_Graph * Create_Weighted_Primal_Graph_Frames( double * var_weight );
	void Update_Var_Order_Single_Cluster();
	void Var_Weight_For_Tree_Decomposition_Frames( double * var_weight );
	void Make_Nodes_With_Search_Graph( RCDD_Manager & manager, Search_Graph<NodeID> & graph, vector<NodeID> & known_nodes );
	void Make_Node_With_Search_Graph( RCDD_Manager & manager, Search_Graph<NodeID> & graph, Search_Node & snode );
public:
	static void Debug() { Debug_File_RCDD(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		RCDD_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = false;
		for ( unsigned i = 50; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			RCDD_Manager manager( Variable( Variable::start + nv - 1 ) );
			CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
			cnf.Sort_Clauses();
			cout << cnf;
			compiler.Compile( manager, cnf, AutomaticalHeur );
//			ofstream fout( "result.cdd" );
			manager.Display( cout );
//			fout.close();
//			system( "./pause" );
		}
	}
	static void Debug_File_RCDD()
	{
		RCDD_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = false;
//		ifstream fin( "instances/logistics.c.cnf" );
		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Planning_prob005.pddl.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/misc_prod-20.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/Benchmarks-Shubham-BE/Verification_blasted_case103.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		RCDD_Manager manager( cnf.Max_Var() );
		compiler.Compile( manager, cnf, AutomaticalHeur );
		ofstream fout( "result.cdd" );
		manager.Display( fout );
		fout.close();
	}
	static void Test_RCDD_Compiler( const char * infile, Compiler_Parameters & parameters )
	{
		RCDD_Compiler compiler;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler.running_options.max_kdepth = parameters.kdepth;
		compiler.running_options.mixed_imp_computing = true;
		compiler.running_options.trivial_variable_bound = 128;
		compiler.running_options.display_kernelizing_process = false;
		compiler.running_options.max_memory = parameters.memo;
		compiler.running_options.removing_redundant_nodes_trigger *= parameters.memo / 4;
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
			if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
			return;
		}
		RCDD_Manager manager( cnf.Max_Var() );
		CDD root = compiler.Compile( manager, cnf, AutomaticalHeur );
		if ( parameters.CT ) {
			BigInt count = manager.Count_Models_Opt( root );
			cout << compiler.running_options.display_prefix << "Number of models: " << count << endl;
		}
		if ( parameters.out_file != nullptr ) {
            ofstream fout( parameters.out_file );
            manager.Display( fout );
            fout.close();
		}
	}
};


}


#endif  // _Compiler_h_
