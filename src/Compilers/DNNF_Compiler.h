#ifndef _DNNF_Compiler_h_
#define _DNNF_Compiler_h_

#include "../KC_Languages/DecDNNF.h"
#include "CDD_Compiler.h"


namespace KCBox {


class DNNF_Compiler: public CDD_Compiler
{
protected:
public:
	DNNF_Compiler();
	~DNNF_Compiler();
	void Reset();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	CDDiagram Compile( DecDNNF_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );  // Reset outside
protected:
	NodeID Make_Root_Node( DecDNNF_Manager & manager, NodeID node );
	void Choose_Running_Options( Heuristic heur, Chain & vorder );
	void Compute_Var_Order_Automatical();
	void Choose_Implicate_Computing_Strategy();
protected:
	void Compile_With_Implicite_BCP( DecDNNF_Manager & manager );
	NodeID Make_Node_With_Imp( DecDNNF_Manager & manager, NodeID node );
	NodeID Make_Decision_Node( DecDNNF_Manager & manager, NodeID low, NodeID high );
	NodeID Make_Node_With_Imp( DecDNNF_Manager & manager, NodeID * nodes, unsigned num );
protected:
	void Verify_Result_Component( Component & comp, DecDNNF_Manager & manager, NodeID result );
protected:
	void Compile_With_SAT_Imp_Computing( DecDNNF_Manager & manager );  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP( DecDNNF_Manager & manager );
	bool Estimate_Hardness( Component & comp );
	void Compute_Second_Var_Order_Automatical( Component & comp );
public:
	static void Debug() { Debug_File(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		DNNF_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = false;
		for ( unsigned i = 0; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			DecDNNF_Manager manager( Variable( Variable::start + nv - 1 ) );
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
	static void Debug_File()
	{
		DNNF_Compiler compiler;
		compiler.running_options.max_kdepth = 2;
		compiler.debug_options.verify_compilation = true;
		compiler.debug_options.verify_component_compilation = false;
		ifstream fin( "instances/s27.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/circuit_s13207.txt.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/ModelChecking_bmc-ibm-10.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/QIF_min-2s.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks/BlastedSMT_blasted_squaring1.cnf" );
//		ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/Planning_logistics.a.cnf" );
		WCNF_Formula cnf( fin );
		fin.close();
		DecDNNF_Manager manager( cnf.Max_Var() );
		CDDiagram dnnf = compiler.Compile( manager, cnf, AutomaticalHeur );
		ofstream fout( "result.cdd" );
		manager.Display( fout );
		fout.close();
		Random_Generator rand_gen( 0 );
		vector<vector<bool>> samples( 10 );
		manager.Uniformly_Sample( rand_gen, dnnf, cnf.Weights(), samples );
		for ( vector<bool> & sample: samples ) {
			for ( Variable i = Variable::start; i <= manager.Max_Var(); i++ ) {
				if ( sample[i] ) cout << i << " ";
				else cout << '-' << i << " ";
			}
			cout << endl;
		}
	}
	static void Test_DecDNNF_Compiler( const char * infile, Compiler_Parameters & parameters, bool quiet )
	{
		DNNF_Compiler compiler;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler.running_options.mixed_imp_computing = true;
		compiler.running_options.trivial_variable_bound = 128;
		compiler.running_options.display_kernelizing_process = false;
		compiler.running_options.cache_encoding = Parse_Cache_Encoding_Strategy( parameters.cache_enc );
		compiler.running_options.max_memory = parameters.memo;
		compiler.running_options.removing_redundant_nodes_trigger *= parameters.memo / 4;
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
		if ( parameters.Weighted_Query() ) {
			WCNF_Formula cnf( fin );
			fin.close();
			if ( cnf.Max_Var() == Variable::undef ) {
				if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
				if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
				return;
			}
			DecDNNF_Manager manager( cnf.Max_Var() );
			CDDiagram dnnf = compiler.Compile( manager, cnf, heur );
			compiler._component_cache.Shrink_To_Fit();
			manager.Remove_Redundant_Nodes();
			vector<double> weights( 2 * cnf.Max_Var() + 2 );
			BigFloat normalized_factor = compiler.Normalize_Weights( cnf.Weights(), weights );
			if ( parameters.wCT ) {
				if ( !parameters.condition.Exists() ) {
					BigFloat count = manager.Count_Models( dnnf, weights );
					count *= normalized_factor;
					cout << compiler.running_options.display_prefix << compiler.running_options.display_prefix << "Weighted model count: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigFloat count = manager.Count_Models_With_Condition( dnnf, weights, term );
						count *= normalized_factor;
						cout << compiler.running_options.display_prefix << "Weighted model count: " << count << endl;
					}
				}
			}
			if ( parameters.wUS.Exists() ) {
				Random_Generator rand_gen;
				vector<vector<bool>> samples( parameters.wUS );
				const char * sample_file = "samples.txt";
				ofstream fout( sample_file );
				if ( !parameters.condition.Exists() ) {
					manager.Uniformly_Sample( rand_gen, dnnf, weights, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, dnnf, weights, samples, term );
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
				manager.Display_dot( fout );
				fout.close();
			}
		}
		else {
			CNF_Formula cnf( fin );
			fin.close();
			if ( cnf.Max_Var() == Variable::undef ) {
				if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
				if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
				return;
			}
			DecDNNF_Manager manager( cnf.Max_Var() );
			CDDiagram dnnf = compiler.Compile( manager, cnf, heur );
			if ( parameters.CT || parameters.US.Exists() ) {
				compiler._component_cache.Shrink_To_Fit();
				manager.Remove_Redundant_Nodes();
			}
			if ( parameters.CO ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Consistency: " << (dnnf.Root() != NodeID::bot) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool sat = manager.Decide_SAT( dnnf, term );
						cout << compiler.running_options.display_prefix << "Consistency: " << sat << endl;
					}
				}
			}
			if ( parameters.VA ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Validity: " << (dnnf.Root() != NodeID::top) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool valid = manager.Decide_Valid_With_Condition( dnnf, term );
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
					bool sat = manager.Decide_SAT( dnnf, term );
					cout << compiler.running_options.display_prefix << "Entailment: " << !sat << endl;
				}
			}
			if ( parameters.IM ) {
				ifstream fin2( parameters.IM );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					bool valid = manager.Decide_Valid_With_Condition( dnnf, term );
					cout << compiler.running_options.display_prefix << "Implicant: " << valid << endl;
				}
			}
			if ( parameters.CT ) {
				if ( !parameters.condition.Exists() ) {
					BigInt count = manager.Count_Models( dnnf );
					cout << compiler.running_options.display_prefix << "Number of models: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigInt count = manager.Count_Models_With_Condition( dnnf, term );
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
					manager.Uniformly_Sample( rand_gen, dnnf, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, dnnf, samples, term );
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
				manager.Display_dot( fout );
				fout.close();
			}
		}
	}
	static void Test_Sampler( const char * infile, Sampler_Parameters & parameters, bool quiet )
	{
		DNNF_Compiler compiler;
		compiler.debug_options.verify_compilation = false;
		compiler.debug_options.verify_component_compilation = false;
		compiler.running_options.mixed_imp_computing = true;
		compiler.running_options.trivial_variable_bound = 128;
		compiler.running_options.display_kernelizing_process = false;
		compiler.running_options.max_memory = parameters.memo;
		compiler.running_options.removing_redundant_nodes_trigger *= parameters.memo / 4;
		if ( quiet ) {
			compiler.running_options.profile_solving = Profiling_Close;
			compiler.running_options.profile_preprocessing = Profiling_Close;
			compiler.running_options.profile_compiling = Profiling_Close;
		}
		ifstream fin( infile );
		WCNF_Formula cnf( fin, parameters.format );
		fin.close();
		if ( cnf.Max_Var() == Variable::undef ) {
			cerr << "ERROR: empty instance!" << endl;
			return;
		}
		DecDNNF_Manager manager( cnf.Max_Var() );
		CDDiagram dnnf = compiler.Compile( manager, cnf, AutomaticalHeur );
		compiler._component_cache.Shrink_To_Fit();
		Random_Generator rand_gen;
		vector<vector<bool>> samples( parameters.nsamples );
		manager.Uniformly_Sample( rand_gen, dnnf, cnf.Weights(), samples );
		ofstream fout( parameters.out_file );
		Write_Assignments( fout, samples, manager.Max_Var() );
		fout.close();
		cout << compiler.running_options.display_prefix << "Samples saved to " << parameters.out_file << endl;
	}
};


}


#endif  // _DNNF_Compiler_h_
