#ifndef _Partial_Compiler_h_
#define _Partial_Compiler_h_

#include "../Counters/KCounter.h"
#include "../Weighted_Languages/Partial_CCDD.h"


namespace KCBox {


class Partial_CCDD_Compiler: public Extensive_Inprocessor
{
protected:
	double * _var_distribution;
	NodeID * _rsl_stack; // rsl denotes result
	unsigned _num_rsl_stack;  // recording the number of temporary results
	double * _pmc_rsl_stack;  // for projected mc
	unsigned _num_pmc_rsl_stack;
	Incremental_Component_Cache<NodeID> _component_cache;
	Component_Cache<double> _pmc_component_cache;
	Rough_Partial_CDD_Node _pcdd_rnode;
	Component _incremental_comp;
	double _node_redundancy_factor;
	vector<Model *> _stored_models;
	bool _store_one_model;
	Random_Generator _rand_gen;
	KCounter _exact_counter;
	bool * _level_ExactMC_failed;
public:
	Partial_CCDD_Compiler();
	~Partial_CCDD_Compiler();
	void Reset();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	CDD Partially_Compile( Partial_CCDD_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur );  // Reset outside
protected:
	NodeID Make_Root_Node( Partial_CCDD_Manager & manager, NodeID node );
	NodeID Make_Kernelized_Conjunction_Node( Partial_CCDD_Manager & manager, NodeID node );
	void Choose_Compiling_Options( Heuristic heur );
	void Compute_Var_Order_Automatical();
	void Create_Init_Level( bool initial );
	void Component_Cache_Add_Original_Clauses();
protected:
	void Microcompile( Partial_CCDD_Manager & manager );
	void Handle_Components(  Partial_CCDD_Manager & manager, unsigned num_comp );
	void Backtrack_True( Partial_CCDD_Manager & manager );
	NodeID Make_Node_With_Imp( Partial_CCDD_Manager & manager, NodeID node );
	NodeID Component_Cache_Map( Component & comp );
	void Generate_Incremental_Component( Component & comp );
	void Recover_All_Imp( Partial_CCDD_Manager & manager, NodeID root );
	void Recover_and_Handle_Components( Partial_CCDD_Manager & manager, NodeID root );
	void Component_Cache_Recover( unsigned loc, Component & comp );
	void Recover_From_Incremental_Component( Component & comp );
	bool Is_Component_Trivial( Component & comp );
	void Hardness_Features_of_Clauses( Component & comp, float & density, float & length );
	void Backtrack_Trivial( Partial_CCDD_Manager & manager );
	void Backtrack();  // backtrack one level without discarding results
	BigInt Count_Models_Simple_Component( Component & comp, vector<Model *> & models, double timeout = 365 * 24 * 3600 );
	lbool Try_Kernelization( Partial_CCDD_Manager & manager );  // return whether solved by this function
	bool Estimate_Kernelization_Effect( Partial_CCDD_Manager & manager );
	void Kernelize_Without_Imp( Partial_CCDD_Manager & manager );
	void Component_Cache_Load_With_Kernelization( unsigned loc );
	void Pick_Original_Binary_Clauses( Stack_Frame & frame, Component & comp );
	void Recover_Lit_Equivalences( Stack_Frame & frame, const Partial_CDD_Node & node );
	void Sort_Clauses_For_Caching();
	void Sort_Long_Clauses_By_IDs();
	void Encode_Long_Clauses();
	void Leave_Kernelization( Partial_CCDD_Manager & manager );
	void Extend_New_Level( Partial_CCDD_Manager & manager );
	void Extend_New_Level();
	bool Dice_Var_Adaptive( Partial_CCDD_Manager & manager, NodeID n );
	bool Dice_Var( Variable var, double & prob, Component & comp );
	double Estimate_Posterior_Probability( Variable var, Component & comp );
	unsigned Projected_Size_For_Estimation( Component & comp );
	void Estimate_Posterior_Probability_With_Implicite_BCP();
	void Backjump_Decision_PMC( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	void Backtrack_True_PMC();
	void Backtrack_PMC();  // backtrack one level without discarding results
	double Component_Cache_Map_PMC( Component & comp );
	void Backtrack_Known_PMC( double known_result );
	void Backtrack_Decision_PMC();
	void Iterate_Known_PMC( double known_result );
	void Iterate_True_PMC();
	void Backjump_Decomposition_PMC( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	void Iterate_Decision_PMC();
	void Backtrack_Decomposition_PMC();
	void Estimate_Posterior_Probability_With_Implicite_BCP_Opt();
	void Estimate_Posterior_Probability_With_SAT_Imp_Computing();
	void Restart_Decision_PMC( Reason reason, unsigned level );
	void Backtrack_Decision( Partial_CCDD_Manager & manager );
	NodeID Make_Unknown_Node( Partial_CCDD_Manager & manager, vector<Model *> & models );
	NodeID Make_Decision_Node( Partial_CCDD_Manager & manager, NodeID low, NodeID high );
	void Remove_Redundant_Nodes( Partial_CCDD_Manager & manager );
	void Iterate_Trivial( Partial_CCDD_Manager & manager );
	void Iterate_Decision( Partial_CCDD_Manager & manager );
	void Backtrack_Decomposition( Partial_CCDD_Manager & manager );
	NodeID Make_Node_With_Imp( Partial_CCDD_Manager & manager, NodeID * nodes, unsigned num );
protected:
	void Verify_Result_Bound( Component & comp, BigFloat result );
	void Verify_Result_Component( Component & comp, double count );
	void Display_Statistics( unsigned option );
	void Display_Result_Statistics( ostream & out, Partial_CCDD_Manager & manager, CDD cdd );
	void Display_Memory_Status( ostream & out );
	void Display_Result_Stack( ostream & out );
public:
	BigFloat Count_Models_Approximately( CNF_Formula & cnf, Heuristic heur );
protected:
	void Choose_Counting_Options( Heuristic heur );
	BigFloat Count_With_One_Round( Partial_CCDD_Manager & manager, StopWatch & begin_watch );
	void Microcompile_Opt( Partial_CCDD_Manager & manager );
	bool Is_Component_Trivial( Partial_CCDD_Manager & manager );
	bool Backtrack_Trivial_Possibly( Partial_CCDD_Manager & manager );
	void Adjust_Trivial_Bound( Component & comp );
	bool Iterate_Trivial_Possibly( Partial_CCDD_Manager & manager );
	bool Is_Memory_Tight( Partial_CCDD_Manager & manager, unsigned old_cache_size );
	void Remove_Redundant_Nodes( Partial_CCDD_Manager & manager, NodeID & root );
	bool Timeout_Possibly( unsigned samples, double elapsed );
public:
	BigFloat Count_Models_Lower_Bound( CNF_Formula & cnf, Heuristic heur, float confidence );
protected:
	BigFloat Compute_Lower_Approximation( BigFloat counts[], float confidence, unsigned num_rounds );
public:
	static void Debug() { Debug_File_Counting(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		Partial_CCDD_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.running_options.sampling_count = 20;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = true;
		compiler._rand_gen.Reset(0);
		for ( unsigned i = 2; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			Partial_CCDD_Manager manager( Variable( Variable::start + nv - 1 ) );
			CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
			cnf.Sort_Clauses();
			cout << cnf;
			compiler.Partially_Compile( manager, cnf, AutomaticalHeur );
//			ofstream fout( "result.cdd" );
			manager.Display( cout );
//			fout.close();
//			system( "./pause" );
		}
	}
	static void Debug_File()
	{
		Partial_CCDD_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.running_options.sampling_count = 20;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = false;
		compiler._rand_gen.Reset(0);
//		ifstream fin( "instances/2bitcomp_5.cnf" );
//		ifstream fin( "instances/ii8a1.cnf" );
		ifstream fin( "instances/s5378.cnf");
//		ifstream fin( "instances/binsearch.16.cnf");
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/circuit_s13207.txt.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/ModelChecking_bmc-ibm-2.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/QIF_min-2s.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/BlastedSMT_blasted_squaring1.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Planning_logistics.a.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		Partial_CCDD_Manager manager( cnf.Max_Var() );
		compiler.Partially_Compile( manager, cnf, AutomaticalHeur );
		ofstream fout( "result.cdd" );
		manager.Display( fout );
		fout.close();
	}
	static void Debug_File_Counting()
	{
		Partial_CCDD_Compiler compiler;
		compiler.running_options.detect_AND_gates = true;
		compiler.running_options.trivial_variable_bound = 512;
		compiler.running_options.max_memory = 8;
		compiler.running_options.max_kdepth = 128;
		compiler.running_options.sampling_count = 20;
		compiler.running_options.sampling_time = 1800;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler._rand_gen.Reset(0);
//		ifstream fin( "instances/2bitcomp_5.cnf" );
//		ifstream fin( "instances/ii8a1.cnf" );
//		ifstream fin( "instances/s5378.cnf");
//		ifstream fin( "instances/binsearch.16.cnf");
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/ModelChecking_bmc-ibm-5.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/BayesianNetwork_fs-19.net.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/BlastedSMT_blasted_case142.cnf" );
		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/circuit_alu2_gr_rcs_w8.shuffled.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/Configuration_C638_FKB.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/inductive-inference_ii8a2.txt.cnf");
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/Planning_uts_k10_p_t10.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/ProgramSynthesis_sygus_17A-1.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/QIF_min-32.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/circuit_s13207.txt.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Planning_logistics.d.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		Partial_CCDD_Manager manager( cnf.Max_Var() );
		compiler.Count_Models_Approximately( cnf, AutomaticalHeur );
	}
	static void Test_Approximate_Counter( const char * infile, Approx_Counter_Parameters & parameters, bool quiet )
	{
		Partial_CCDD_Compiler compiler;
		compiler.debug_options.verify_model = false;
		compiler.debug_options.verify_processed_clauses = false;
		compiler.debug_options.verify_kernelization = false;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler.running_options.max_kdepth = parameters.kdepth;
		compiler.running_options.trivial_variable_bound = 512;
		compiler.running_options.display_kernelizing_process = false;
		compiler.running_options.max_memory = parameters.memo;
		compiler.running_options.removing_redundant_nodes_trigger *= parameters.memo / 16;
		compiler.running_options.sampling_time = parameters.time;
		compiler.running_options.sampling_count = parameters.micro;
		compiler._rand_gen.Reset( parameters.seed );
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( heur != AutomaticalHeur && heur != minfill && heur != LinearLRW && heur != DLCP && heur != dynamic_minfill ) {
			cerr << "ERROR: the heuristic is not supported yet!" << endl;
			exit( 0 );
		}
		if ( quiet ) {
			compiler.running_options.profile_solving = Profiling_Close;
			compiler.running_options.profile_preprocessing = Profiling_Close;
			compiler.running_options.profile_compiling = Profiling_Close;
		}
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
			return;
		}
		if ( !parameters.lower ) compiler.Count_Models_Approximately( cnf, heur );
		else compiler.Count_Models_Lower_Bound( cnf, heur, parameters.confidence );
	}
};


}


#endif
