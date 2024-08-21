#ifndef _KCounter_h_
#define _KCounter_h_

#include "../Component_Types/Incremental_Component.h"
#include "../Component_Types/Incremental_Component_BigInt.h"
#include "../Extensive_Inprocessor.h"


namespace KCBox {


class KCounter: public Extensive_Inprocessor
{
protected:
	BigInt * _rsl_stack;  // rsl denotes result
	unsigned * _aux_rsl_stack;  // record the auxiliary information for results
	unsigned _num_rsl_stack;  // recording the number of temporary results
	Incremental_Component_Cache_BigInt _component_cache;
	Component _incremental_comp;
	vector<Literal> _equivalent_lit_pairs;
public:
	KCounter();
	~KCounter();
	void Reset();
	size_t Memory();
	void Set_Max_Var( Variable max_var ) { Allocate_and_Init_Auxiliary_Memory( max_var ); }
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	BigInt Count_Models( CNF_Formula & cnf, Heuristic heur = AutomaticalHeur );
protected:
	BigInt Backtrack_Init();
	void Choose_Running_Options( Heuristic heur );
	void Compute_Var_Order_Automatical();
	void Choose_Running_Options_Static( Heuristic heur );
	void Compute_Var_Order_Automatical_Static();
	void Choose_Implicate_Computing_Strategy();
	void Choose_Implicate_Computing_Strategy_Static();
	void Create_Init_Level();
	void Component_Cache_Add_Original_Clauses();
protected:
	void Count_With_Implicite_BCP();
	void Backjump_Decision( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	void Backtrack_True();
	void Backtrack_Known( BigInt cached_result );
	BigInt Component_Cache_Map_Current_Component();
	void Generate_Incremental_Component( Component & comp );
	void Generate_Incremental_Component_Old( Component & comp );
	void Component_Cache_Connect_Current_Component();
	bool Cache_Clear_Applicable();
	void Component_Cache_Clear();
	void Component_Cache_Reconnect_Components();
	void Backtrack();  // backtrack one level without discarding results
	void Extend_New_Level();
	void Backtrack_Decision();
	void Backjump_Decomposition( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	void Iterate_Known( BigInt cached_result );
	void Backtrack_Decomposition2Decision();
	void Iterate_Decision();
	void Backtrack_Decomposition();
protected:
	void Verify_Result_Component( Component & comp, BigInt count );
	bool Verified_Path();
	bool Verified_Components( Component & comp );
	void Display_Statistics( unsigned option );
	void Display_Result_Stack( ostream & out );
	void Display_Memory_Status( ostream & out );
protected:
	void Count_With_SAT_Imp_Computing();  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP();
	bool Estimate_Hardness( Component & comp );
	lbool Try_Final_Kernelization();  // return whether solved by this function
	bool Estimate_Final_Kernelization_Effect();
	void Leave_Final_Kernelization();
	void Compute_Second_Var_Order_Automatical( Component & comp );
	lbool Try_Kernelization();  // return whether solved by this function
	bool Estimate_Kernelization_Effect();
	void Sort_Clauses_For_Caching();
	void Sort_Long_Clauses_By_IDs();
	void Encode_Long_Clauses();
	void Leave_Kernelization();
	void Calculate_Decision();
	void Backtrack_Decision_Imp();
	void Iterate_Decision_Next();
public:
	BigInt Count_Models( CNF_Formula & cnf, vector<Model *> & models );
	BigInt Count_Models( CNF_Formula & cnf, vector<Model *> & models, double timeout );
protected:
	void Count_With_Implicite_BCP( double timeout );
	void Terminate_Counting();
	void Count_With_SAT_Imp_Computing( double timeout );  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP( double timeout );
	BigInt Backtrack_Failure();
	bool Is_Memory_Exhausted();
public:
	static void Debug() { Debug_File(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		KCounter counter;
		counter.debug_options.verify_count = true;
		counter.debug_options.verify_component_count = false;
		for ( unsigned i = 0; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
			cnf.Sort_Clauses();
			cout << cnf;
			counter.Count_Models( cnf, AutomaticalHeur );
//			ofstream fout( "result.cdd" );
//			manager.Display( fout );
//			fout.close();
//			system( "./pause" );
		}
	}
	static void Debug_File()
	{
		KCounter counter;
		counter.debug_options.verify_count = true;
		counter.running_options.max_kdepth = 2;
		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/misc_07A-3.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/Benchmarks-Shubham-BE/log2.sk_72_391.cnf.gz.no_w.cnf.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		counter.Count_Models( cnf, AutomaticalHeur );
	}
	static void Test( const char * infile, Counter_Parameters parameters, bool quiet )
	{
		KCounter counter;
		counter.debug_options.verify_learnts = false;
		counter.debug_options.verify_count = false;
		counter.debug_options.verify_component_count = false;
		counter.debug_options.verify_kernelization = false;
		counter.running_options.phase_selecting = false;
		counter.running_options.sat_filter_long_learnts = false;
		counter.running_options.detect_AND_gates = false;
		counter.running_options.block_lits_external = true;
		counter.running_options.static_heur = parameters.static_heur;
		counter.running_options.max_kdepth = parameters.kdepth;
		counter.running_options.mixed_imp_computing = true;
		counter.running_options.trivial_variable_bound = 128;
		counter.running_options.display_kernelizing_process = false;
		counter.running_options.max_memory = parameters.memo;
		counter.running_options.clear_half_of_cache = parameters.clear_half;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( quiet ) {
			counter.running_options.profile_solving = Profiling_Close;
			counter.running_options.profile_preprocessing = Profiling_Close;
			counter.running_options.profile_counting = Profiling_Close;
		}
		if ( parameters.competition ) counter.running_options.display_prefix = "c o ";
		if ( !parameters.condition.Exists() ) {
			ifstream fin( infile );
			CNF_Formula cnf( fin );
			fin.close();
			BigInt count;
			if ( cnf.Max_Var() == Variable::undef ) {
				count = cnf.Known_Count();
				if ( count != 0 ) cout << "s SATISFIABLE" << endl;
				else cout << "s UNSATISFIABLE" << endl;
			}
			else count = counter.Count_Models( cnf, heur );
			cout << counter.running_options.display_prefix << "Number of models: " << count << endl;
			if ( parameters.competition ) {  // for model counting competition
				cout << "c s type mc" << endl;
				cout << "c o The solver log10-estimates a solution of " << count << endl;
				long exp;
				double num = count.TransformDouble_2exp( exp );
				cout << "c s log10-estimate " << log10( num ) + exp * log10(2) << endl;
				cout << "c o Arbitrary precision result is " << count << endl;
				cout << "c s exact arb int " << count << endl;
			}
		}
		else {
			ifstream fin_cond( parameters.condition );
			vector<vector<Literal>> terms;
			Read_Assignments( fin_cond, terms );
			fin_cond.close();
			vector<BigInt> counts( terms.size() );
			if ( access("B+E_linux", X_OK ) == 0 || access("solvers/B+E_linux", X_OK ) == 0 ) {
				for ( unsigned i = 0; i < terms.size(); i++ ) {
					ifstream fin( infile );
					CNF_Formula cnf( fin );
					fin.close();
					cnf.Condition( terms[i] );
					char BE_input[2048];
					strcpy( BE_input, infile );
					strcat( BE_input, ".condition.cnf" );
					ofstream fout( BE_input );
					fout << cnf;
					fout.close();
					char BE_output[2048];
					strcpy( BE_output, BE_input );
					strcat( BE_output, ".BE.cnf" );
					char command[4096];
					if ( access("B+E_linux", X_OK ) == 0 ) strcpy( command, "./B+E_linux " );
					else strcpy( command, "solvers/B+E_linux " );
					strcat( command, BE_input );
					strcat( command, " > ");
					strcat( command, BE_output );
					system( command );
					ifstream fin2( BE_output );
					CNF_Formula cnf2( fin2 );
					fin2.close();
					if ( cnf2.Max_Var() == Variable::undef ) counts[i] = cnf2.Known_Count();
					else counts[i] = counter.Count_Models( cnf2, heur );
				}
			}
			else {
				cerr << "Warning: it would be better to use B+E with the path solvers/B+E_linux!" << endl;
				for ( unsigned i = 0; i < terms.size(); i++ ) {
					ifstream fin( infile );
					CNF_Formula cnf( fin );
					fin.close();
					cnf.Condition( terms[i] );
					if ( cnf.Max_Var() == Variable::undef ) counts[i] = cnf.Known_Count();
					else counts[i] = counter.Count_Models( cnf, heur );
				}
			}
			for ( unsigned i = 0; i < counts.size(); i++ ) {
				cout << counter.running_options.display_prefix << "Number of models: " << counts[i] << endl;
			}
		}
	}
};


}


#endif  // _Compiler_h_
