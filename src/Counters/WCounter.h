#ifndef _WCounter_h_
#define _WCounter_h_

#include "../Inprocessor.h"
#include "../Component_Types/Component_BigFloat.h"


namespace KCBox {


class WCounter: public Inprocessor
{
protected:
	BigFloat _normalized_factor;
	BigFloat * _weights;  // double might overflow
	BigFloat * _rsl_stack;  // rsl denotes result
	unsigned _num_rsl_stack;  // recording the number of temporary results
	Component_Cache_BigFloat _component_cache;
	vector<Literal> _equivalent_lit_pairs;
public:
	WCounter();
	~WCounter();
	void Reset();
	size_t Memory();
	void Set_Max_Var( Variable max_var ) { Allocate_and_Init_Auxiliary_Memory( max_var ); }
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	BigFloat Count_Models( WCNF_Formula & cnf, Heuristic heur = AutomaticalHeur );
protected:
	BigFloat Backtrack_Init();
	void Choose_Running_Options( Heuristic heur );
	void Compute_Var_Order_Automatical();
	void Choose_Running_Options_Static( Heuristic heur );
	void Compute_Var_Order_Automatical_Static();
	void Choose_Implicate_Computing_Strategy();
	void Create_Init_Level();
protected:
	void Count_With_Implicite_BCP();
	void Backjump_Decision( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	void Component_Cache_Erase( Component & comp );
	void Backtrack_True();
	void Backtrack_Known( BigFloat cached_result );
	BigFloat Component_Cache_Map( Component & comp );
	void Backtrack();  // backtrack one level without discarding results
	void Extend_New_Level();
	void Backtrack_Decision();
	void Backjump_Decomposition( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	void Iterate_Known( BigFloat cached_result );
	void Backtrack_Decomposition2Decision();
	void Iterate_Decision();
	void Backtrack_Decomposition();
protected:
	void Verify_Result_Component( Component & comp, BigFloat count );
	void Display_Statistics( unsigned option );
	void Display_Result_Stack( ostream & out );
	void Display_Memory_Status( ostream & out );
protected:
	void Count_With_SAT_Imp_Computing();  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP();
	bool Estimate_Hardness( Component & comp );
	void Compute_Second_Var_Order_Automatical( Component & comp );
public:
	BigFloat Count_Models( WCNF_Formula & cnf, vector<Model *> & models, double timeout );
protected:
	void Count_With_Implicite_BCP( double timeout );
	void Terminate_Counting();
	void Count_With_SAT_Imp_Computing( double timeout );  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP( double timeout );
	BigFloat Backtrack_Failure();
	bool Is_Memory_Exhausted();
public:
	static void Debug() { Debug_File(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		WCounter counter;
		counter.debug_options.verify_count = true;
		for ( unsigned i = 12; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			WCNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
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
		WCounter counter;
		counter.debug_options.verify_count = true;
		counter.running_options.detect_AND_gates = true;
		unsigned format;
		ifstream fin;
		if ( false ) {
			fin.open( "instances-weighted/2bitcomp_5.wcnf" );
			format = 0;
		}
		else {
			fin.open( "instances-weighted/log-3.cnf" );
			format = 1;
		}
		WCNF_Formula cnf( fin, format );
		fin.close();
		BigFloat count = counter.Count_Models( cnf, AutomaticalHeur );
		cout << "Number of models: " << count << endl;
	}
	static void Test( const char * infile, Counter_Parameters parameters, bool quiet )
	{
		WCounter counter;
		counter.debug_options.verify_processed_clauses = false;
		counter.debug_options.verify_count = false;
		counter.debug_options.verify_component_count = false;
		counter.running_options.detect_AND_gates = false;
		counter.running_options.static_heur = parameters.static_heur;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( quiet ) {
			counter.running_options.profile_solving = Profiling_Close;
			counter.running_options.profile_preprocessing = Profiling_Close;
			counter.running_options.profile_counting = Profiling_Close;
		}
		if ( parameters.competition ) counter.running_options.display_prefix = "c o ";
		ifstream fin( infile );
		WCNF_Formula cnf( fin, parameters.format );
		fin.close();
		BigFloat count;
		if ( cnf.Max_Var() == Variable::undef ) {
			if ( count != 0 ) cout << "s SATISFIABLE" << endl;
			else cout << "s UNSATISFIABLE" << endl;
			count = cnf.Known_Count();
		}
		else count = counter.Count_Models( cnf, heur );
		cout << counter.running_options.display_prefix << "Weighted model count: " << count << endl;
		if ( parameters.competition ) {  // for model counting competition
			cout << "c s type wmc" << endl;
			cout << "c o This file describes that the weighted model count is" << endl;
			cout << "c o " << count << endl;
			cout << "c s type wmc" << endl;
//			long exp;
//			double num = count.TransformDouble_2exp( exp );
//			cout << "c s log10-estimate " << log10( num ) + exp * log10(2) << endl;
//			cout << "c s exact arb int " << count << endl;
		}
	}
};


}


#endif  // _Compiler_h_
