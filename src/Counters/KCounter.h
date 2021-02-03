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
	void Component_Cache_Erase( Component & comp );
	void Backtrack_True();
	void Backtrack_Known( BigInt cached_result );
	BigInt Component_Cache_Map( Component & comp );
	void Generate_Incremental_Component( Component & comp );
	void Generate_Incremental_Component_Old( Component & comp );
	bool Cache_Clear_Applicable();
	void Component_Cache_Clear();
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
	void Display_Statistics( unsigned option );
	void Display_Result_Stack( ostream & out );
	void Display_Memory_Status( ostream & out );
protected:
	void Count_With_SAT_Imp_Computing();  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP();
	bool Estimate_Hardness( Component & comp );
	lbool Try_Final_Kernelization();  // return whether solved by this function
	bool Estimate_Final_Kernelization_Effect();
	bool Estimate_Kernelization_Effect_Enough_Decisions( unsigned step );
	void Leave_Tmp_Kernelization();
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
protected:
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
		counter.debug_options.verify_count = false;
		counter.debug_options.verify_component_count = false;
		counter.running_options.static_heur = parameters.static_heur;
		counter.running_options.phase_selecting = false;
		counter.running_options.max_kdepth = parameters.kdepth;
		counter.running_options.mixed_imp_computing = true;
		counter.running_options.trivial_variable_bound = 128;
		counter.running_options.display_kernelizing_process = false;
		counter.running_options.max_memory = parameters.memo;
		Heuristic heur;
		if ( parameters.heur == 1 ) heur = minfill;
		else if ( parameters.heur == 2 ) heur = LinearLRW;
		else if ( parameters.heur == 3 ) heur = Dminfill;
		else if ( parameters.heur == 4 ) heur = VSADS;
		else if ( parameters.heur == 5 ) heur = DLCS;
		else if ( parameters.heur == 6 ) heur = DLCP;
		else heur = AutomaticalHeur;
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			cout << "Number of models: " << cnf.Known_Count() << endl;
			return;
		}
		BigInt count = counter.Count_Models( cnf, heur );
		cout << "Number of models: " << count << endl;
	}
};


}


#endif  // _Compiler_h_
