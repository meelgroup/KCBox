#ifndef _Compiler_h_
#define _Compiler_h_

#include "../Inprocessor.h"
#include "../KC_Languages/OBDD[AND].h"


namespace KCBox {


class Compiler: public Inprocessor
{
protected:
	NodeID * _rsl_stack; // rsl denotes result
	unsigned _num_rsl_stack;  // recording the number of temporary results
	Component_Cache<NodeID> _component_cache;
	vector<Literal> _equivalent_lit_pairs;
	Rough_BDDC_Node _bddc_rnode;
	unsigned _remove_redundancy_trigger;
public:
	Compiler();
	~Compiler();
	void Reset();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	BDDC Compile( OBDDC_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );
protected:
	NodeID Make_Node_With_Init_Imp( OBDDC_Manager & manager, NodeID node );
	void Reorder_BDDC_Manager( OBDDC_Manager & manager );
	void Create_Init_Level();
protected:
	void Compile_With_Implicite_BCP( OBDDC_Manager & manager );
	void Backjump_Decision( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	void Component_Cache_Erase( Component & comp );
	NodeID Make_Node_With_Imp( OBDDC_Manager & manager, NodeID node );
	NodeID Component_Cache_Map( Component & comp );
	void Backtrack();  // backtrack one level without discarding results
	void Extend_New_Level();
	void Refactor_Current_Level();
	NodeID Make_Decision_Node( OBDDC_Manager & manager, NodeID low, NodeID high );
	void Remove_Redundant_Nodes( OBDDC_Manager & manager );
	void Component_Cache_Clear();
	void Backjump_Decomposition( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	void Backtrack_Halfway();  // backtrack one decomposition level when getting a UNSAT
	NodeID Make_Node_With_Imp( OBDDC_Manager & manager, NodeID * nodes, unsigned num );
protected:
	void Verify_Result_Component( Component & comp, OBDDC_Manager & manager, NodeID result );
	void Display_Statistics( unsigned option );
	void Display_Result_Statistics( ostream & out, OBDDC_Manager & manager, BDDC bddc );
	void Display_Memory_Status( ostream & out );
	void Display_Result_Stack( ostream & out );
protected:
	void Compile_With_SAT_Imp_Computing( OBDDC_Manager & manager );  // employ SAT engine to compute implied literals
protected:
	void Choose_Running_Options( Heuristic heur, Chain & vorder );
	void Compute_Var_Order_Automatical();
	void Choose_Implicate_Computing_Strategy();
protected:
	bool Is_Memory_Exhausted();
public:
	static void Debug() { Debug_File_BDDC(); }
	static void Debug_File_BDDC()
	{
		Compiler compiler;
		ifstream fin( "../kc-domain-benchmarks/BayesianNetwork_fs-01.net.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		OBDDC_Manager manager( cnf.Max_Var() );
		compiler.Compile( manager, cnf, AutomaticalHeur );
		ofstream fout( "result.cdd" );
		manager.Display( fout );
		fout.close();
	}
	static void Test_OBDD_Compiler( const char * infile, Compiler_Parameters & parameters, bool quiet )
	{
		Compiler compiler;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( heur != AutomaticalHeur && heur != minfill && heur != LexicographicOrder ) {
			cerr << "ERROR: the heuristic is not supported yet!" << endl;
			exit( 0 );
		}
		if ( quiet ) {
			compiler.running_options.profile_solving = Profiling_Close;
			compiler.running_options.profile_preprocessing = Profiling_Close;
			compiler.running_options.profile_compiling = Profiling_Close;
		}
		if ( parameters.CT.Exists() || parameters.US.Exists() ) {
			cerr << "ERROR: the query is not supported yet!" << endl;
			exit( 0 );
		}
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			if ( compiler.running_options.display_compiling_process ) cout << "c o Number of edges: 0" << endl;
			return;
		}
		OBDDC_Manager manager( cnf.Max_Var() );
		BDDC root = compiler.Compile( manager, cnf, heur );
		OBDD_Manager bdd_manager( manager.Var_Order() );
		manager.Convert_Down_ROBDD( root, bdd_manager );
		if ( parameters.out_file != nullptr ) {
			ofstream fout( parameters.out_file );
			bdd_manager.Display( fout );
			fout.close();
		}
	}
	static void Test_OBDDC_Compiler( const char * infile, Compiler_Parameters & parameters, bool quiet )
	{
		Compiler compiler;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( heur != AutomaticalHeur && heur != minfill && heur != LexicographicOrder ) {
			cerr << "ERROR: the heuristic is not supported yet!" << endl;
			exit( 0 );
		}
		if ( quiet ) {
			compiler.running_options.profile_solving = Profiling_Close;
			compiler.running_options.profile_preprocessing = Profiling_Close;
			compiler.running_options.profile_compiling = Profiling_Close;
		}
		if ( parameters.US.Exists() ) {
			cerr << "ERROR: the query is not supported yet!" << endl;
			exit( 0 );
		}
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			if ( compiler.running_options.display_compiling_process ) cout << "c o Number of edges: 0" << endl;
			if ( parameters.CT ) cout << "c o Number of models: " << cnf.Known_Count() << endl;
			return;
		}
		OBDDC_Manager manager( cnf.Max_Var() );
		BDDC root = compiler.Compile( manager, cnf, heur );
		if ( parameters.CT ) cout << "c o Number of models: " << manager.Count_Models_Opt( root ) << endl;
		if ( parameters.out_file != nullptr ) {
			ofstream fout( parameters.out_file );
            manager.Display( fout );
            fout.close();
		}
	}
};


}


#endif  // _Compiler_h_
