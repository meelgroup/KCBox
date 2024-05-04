#ifndef _R2D2_Compiler_h_
#define _R2D2_Compiler_h_

#include "../KC_Languages/RRCDD.h"
#include "CDD_Compiler.h"


namespace KCBox {


class R2D2_Compiler: public CDD_Compiler
{
protected:
public:
	R2D2_Compiler();
	~R2D2_Compiler();
	void Reset();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	CDDiagram Compile( R2D2_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );
protected:
	NodeID Make_Root_Node( R2D2_Manager & manager, NodeID node );
	NodeID Make_Kernelized_Conjunction_Node( R2D2_Manager & manager, NodeID node );
	void Choose_Running_Options( Heuristic heur, Chain & vorder );
	void Compute_Var_Order_Automatical();
	void Choose_Implicate_Computing_Strategy();
	void Reorder_Manager( R2D2_Manager & manager );
protected:
	void Compile_With_Implicite_BCP( R2D2_Manager & manager );
	bool Try_Shift_To_Implicite_BCP( R2D2_Manager & manager );
	bool Estimate_Hardness( Component & comp );
	NodeID Make_Node_With_Imp( R2D2_Manager & manager, NodeID node );
	NodeID Make_Decision_Node( R2D2_Manager & manager, NodeID low, NodeID high );
	NodeID Make_Node_With_Imp( R2D2_Manager & manager, NodeID * nodes, unsigned num );
protected:
	void Verify_Result_Component( Component & comp, R2D2_Manager & manager, NodeID result );
	void Display_Statistics( unsigned option );
	void Display_Result_Statistics( ostream & out, R2D2_Manager & manager, NodeID root );
protected:
	void Compile_With_SAT_Imp_Computing( R2D2_Manager & manager );  // employ SAT engine to compute implied literals
public:
	CDDiagram Compile_FixedLinearOrder( R2D2_Manager & manager, Preprocessor & preprocessor, Chain & vorder = Chain::default_empty_chain );
protected:
	bool Is_Memory_Exhausted();
public:
	static void Debug() { Debug_File_RRCDD(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		R2D2_Compiler compiler;
		for ( unsigned i = 0; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			R2D2_Manager manager( Variable( Variable::start + nv - 1 ) );
			CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
			cnf.Sort_Clauses();
			cout << cnf;
			compiler.Compile( manager, cnf, AutomaticalHeur );
//			ofstream fout( "result.cdd" );
//			manager.Display( fout );
//			fout.close();
//			system( "./pause" );
		}
	}
	static void Debug_File_RRCDD()
	{
		R2D2_Compiler compiler;
		compiler.debug_options.verify_compilation = true;
		compiler.running_options.var_ordering_heur = FlowCutter;
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/circuit_s13207.txt.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Configuration_C170_FR.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/ModelChecking_bmc-ibm-12.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Verification_blasted_case11.cnf" );
		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Verification_blasted_case_1_b11_1.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Planning_ring2_r6_p_t10.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		R2D2_Manager manager( cnf.Max_Var() );
		compiler.Compile( manager, cnf, compiler.running_options.var_ordering_heur );
		ofstream fout( "result.cdd" );
		manager.Display( fout );
		fout.close();
	}
	static void Test_R2D2_Compiler( const char * infile, Compiler_Parameters & parameters )
	{
		R2D2_Compiler compiler;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler.running_options.max_kdepth = parameters.kdepth;
		compiler.running_options.mixed_imp_computing = true;
		compiler.running_options.trivial_variable_bound = 128;
		compiler.running_options.display_kernelizing_process = false;
		compiler.running_options.max_memory = parameters.memo;
		compiler.running_options.removing_redundant_nodes_trigger *= parameters.memo / 4;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( Is_Linear_Ordering( heur ) == lbool(false) ) {
			cerr << "ERROR: the heuristic is not linear!" << endl;
			exit( 0 );
		}
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
			if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
			return;
		}
		R2D2_Manager manager( cnf.Max_Var() );
		CDDiagram r2d2 = compiler.Compile( manager, cnf, heur );
		if ( parameters.CT || parameters.US.Exists() ) {
			compiler._component_cache.Shrink_To_Fit();
			manager.Remove_Redundant_Nodes();
		}
		if ( parameters.CO ) {
			if ( !parameters.condition.Exists() ) {
				cout << compiler.running_options.display_prefix << "Consistency: " << (r2d2.Root() != NodeID::bot) << endl;
			}
			else {
				ifstream fin2( parameters.condition );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					bool sat = manager.Decide_SAT( r2d2, term );
					cout << compiler.running_options.display_prefix << "Consistency: " << sat << endl;
				}
			}
		}
		if ( parameters.VA ) {
			if ( !parameters.condition.Exists() ) {
				cout << compiler.running_options.display_prefix << "Validity: " << (r2d2.Root() != NodeID::top) << endl;
			}
			else {
				ifstream fin2( parameters.condition );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					bool valid = manager.Decide_Valid_With_Condition( r2d2, term );
					cout << compiler.running_options.display_prefix << "Validity: " << valid << endl;
				}
			}
		}
		if ( parameters.CE ) {
			ifstream fin2( parameters.CE );
			vector<vector<Literal>> terms;
			Read_Assignments( fin2, terms );
			fin2.close();
			for ( vector<Literal> & term: terms ) {
				for ( Literal & lit: term ) {
					lit = ~lit;
				}
				bool sat = manager.Decide_SAT( r2d2, term );
				cout << compiler.running_options.display_prefix << "Entailment: " << !sat << endl;
			}
		}
		if ( parameters.IM ) {
			ifstream fin2( parameters.IM );
			vector<vector<Literal>> terms;
			Read_Assignments( fin2, terms );
			fin2.close();
			for ( vector<Literal> & term: terms ) {
				bool valid = manager.Decide_Valid_With_Condition( r2d2, term );
				cout << compiler.running_options.display_prefix << "Implicant: " << valid << endl;
			}
		}
		if ( parameters.CT ) {
			if ( !parameters.condition.Exists() ) {
				BigInt count = manager.Count_Models( r2d2 );
				cout << compiler.running_options.display_prefix << compiler.running_options.display_prefix << "Number of models: " << count << endl;
			}
			else {
				ifstream fin2( parameters.condition );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					BigInt count = manager.Count_Models_With_Condition( r2d2, term );
					cout << compiler.running_options.display_prefix << "Number of models: " << count << endl;
				}
			}
		}
		if ( parameters.US.Exists() ) {
			Random_Generator rand_gen;
			vector<vector<bool>> samples( parameters.US );
			const char * sample_file = "samples.txt";
			ofstream fout( sample_file );
			if ( !parameters.condition.Exists() ) {
				manager.Uniformly_Sample( rand_gen, r2d2, samples );
				Write_Assignments( fout, samples, manager.Max_Var() );
			}
			else {
				ifstream fin2( parameters.condition );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					manager.Uniformly_Sample_With_Condition( rand_gen, r2d2, samples, term );
					fout << "c assignment: ";
					Write_Assignment( fout, term );
					fout << endl;
					Write_Assignments( fout, samples, manager.Max_Var() );
					samples.resize( parameters.US );
				}
			}
			fout.close();
			cout << compiler.running_options.display_prefix << "Samples saved to " << sample_file << endl;
		}
		if ( parameters.out_file != nullptr ) {
            ofstream fout( parameters.out_file );
            manager.Display( fout );
            fout.close();
		}
		if ( parameters.out_file_dot != nullptr ) {
			ofstream fout( parameters.out_file_dot );
			manager.Display_CDD_dot( fout, r2d2 );
			fout.close();
		}
	}
};


}


#endif  // _Compiler_h_
