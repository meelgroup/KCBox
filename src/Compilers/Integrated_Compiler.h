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
	Diagram Compile( OBDDC_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );
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
	void Display_Result_Statistics( ostream & out, OBDDC_Manager & manager, NodeID root );
	void Display_Memory_Status( ostream & out );
	void Display_Result_Stack( ostream & out );
protected:
	void Compile_With_SAT_Imp_Computing( OBDDC_Manager & manager );  // employ SAT engine to compute implied literals
protected:
	void Choose_Running_Options( Heuristic heur, Chain & vorder );
	void Compute_Var_Order_Automatical();
	void Choose_Implicate_Computing_Strategy();
public:
	Diagram Compile( OBDD_Manager & manager, CNF_Formula & cnf, Heuristic heur = AutomaticalHeur, Chain & vorder = Chain::default_empty_chain );
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
		compiler.debug_options.verify_compilation = false;
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
		ifstream fin( infile );
		if ( parameters.Weighted_Query() ) {
			WCNF_Formula cnf( fin );
			fin.close();
			if ( cnf.Max_Var() == Variable::undef ) {
				if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
				if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
				return;
			}
			OBDD_Manager manager( cnf.Max_Var() );
			Diagram bdd = compiler.Compile( manager, cnf, heur );
			vector<double> weights( 2 * cnf.Max_Var() + 2 );
			BigFloat normalized_factor = compiler.Normalize_Weights( cnf.Weights(), weights );
			if ( parameters.wCT ) {
				if ( !parameters.condition.Exists() ) {
					BigFloat count = manager.Count_Models( bdd, weights );
					count *= normalized_factor;
					cout << compiler.running_options.display_prefix << "Weighted model count: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigFloat count = manager.Count_Models_With_Condition( bdd, weights, term );
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
					manager.Uniformly_Sample( rand_gen, bdd, weights, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, bdd, weights, samples, term );
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
				manager.Display_OBDD_dot( fout, bdd );
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
			OBDD_Manager manager( cnf.Max_Var() );
			Diagram bdd = compiler.Compile( manager, cnf, heur );
			if ( parameters.CO ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Consistency: " << (bdd.Root() != NodeID::bot) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool sat = manager.Decide_SAT( bdd, term );
						cout << compiler.running_options.display_prefix << "Consistency: " << sat << endl;
					}
				}
			}
			if ( parameters.VA ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Validity: " << (bdd.Root() != NodeID::top) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool valid = manager.Decide_Valid_With_Condition( bdd, term );
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
					bool sat = manager.Decide_SAT( bdd, term );
					cout << compiler.running_options.display_prefix << "Entailment: " << !sat << endl;
				}
			}
			if ( parameters.IM ) {
				ifstream fin2( parameters.IM );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					bool valid = manager.Decide_Valid_With_Condition( bdd, term );
					cout << compiler.running_options.display_prefix << "Implicant: " << valid << endl;
				}
			}
			if ( parameters.CT ) {
				if ( !parameters.condition.Exists() ) {
					BigInt count = manager.Count_Models( bdd );
					cout << compiler.running_options.display_prefix << "Number of models: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigInt count = manager.Count_Models_With_Condition( bdd, term );
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
					manager.Uniformly_Sample( rand_gen, bdd, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, bdd, samples, term );
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
				manager.Display_OBDD_dot( fout, bdd );
				fout.close();
			}
		}
	}
	static void Test_OBDDC_Compiler( const char * infile, Compiler_Parameters & parameters, bool quiet )
	{
		Compiler compiler;
		compiler.debug_options.verify_compilation = false;
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
		ifstream fin( infile );
		if ( parameters.Weighted_Query() ) {
			WCNF_Formula cnf( fin );
			fin.close();
			if ( cnf.Max_Var() == Variable::undef ) {
				if ( compiler.running_options.display_compiling_process ) cout << compiler.running_options.display_prefix << "Number of edges: 0" << endl;
				if ( parameters.CT ) cout << compiler.running_options.display_prefix << "Number of models: " << cnf.Known_Count() << endl;
				return;
			}
			OBDDC_Manager manager( cnf.Max_Var() );
			Diagram bddc = compiler.Compile( manager, cnf, heur );
			compiler._component_cache.Shrink_To_Fit();
			manager.Remove_Redundant_Nodes();
			vector<double> weights( 2 * cnf.Max_Var() + 2 );
			BigFloat normalized_factor = compiler.Normalize_Weights( cnf.Weights(), weights );
			if ( parameters.wCT ) {
				if ( !parameters.condition.Exists() ) {
					BigFloat count = manager.Count_Models( bddc, weights );
					count *= normalized_factor;
					cout << compiler.running_options.display_prefix << "Weighted model count: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigFloat count = manager.Count_Models_With_Condition( bddc, weights, term );
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
					manager.Uniformly_Sample( rand_gen, bddc, weights, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, bddc, weights, samples, term );
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
				manager.Display_OBDDC_dot( fout, bddc );
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
			OBDDC_Manager manager( cnf.Max_Var() );
			Diagram bddc = compiler.Compile( manager, cnf, heur );
			if ( parameters.CT || parameters.US.Exists() ) {
				compiler._component_cache.Shrink_To_Fit();
				manager.Remove_Redundant_Nodes();
			}
			if ( parameters.CO ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Consistency: " << (bddc.Root() != NodeID::bot) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool sat = manager.Decide_SAT( bddc, term );
						cout << compiler.running_options.display_prefix << "Consistency: " << sat << endl;
					}
				}
			}
			if ( parameters.VA ) {
				if ( !parameters.condition.Exists() ) {
					cout << compiler.running_options.display_prefix << "Validity: " << (bddc.Root() != NodeID::top) << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						bool valid = manager.Decide_Valid_With_Condition( bddc, term );
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
					bool sat = manager.Decide_SAT( bddc, term );
					cout << compiler.running_options.display_prefix << "Entailment: " << !sat << endl;
				}
			}
			if ( parameters.IM ) {
				ifstream fin2( parameters.IM );
				vector<vector<Literal>> terms;
				Read_Assignments( fin2, terms );
				fin2.close();
				for ( vector<Literal> & term: terms ) {
					bool valid = manager.Decide_Valid_With_Condition( bddc, term );
					cout << compiler.running_options.display_prefix << "Implicant: " << valid << endl;
				}
			}
			if ( parameters.CT ) {
				if ( !parameters.condition.Exists() ) {
					BigInt count = manager.Count_Models( bddc );
					cout << compiler.running_options.display_prefix << "Number of models: " << count << endl;
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						BigInt count = manager.Count_Models_With_Condition( bddc, term );
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
					manager.Uniformly_Sample( rand_gen, bddc, samples );
					Write_Assignments( fout, samples, manager.Max_Var() );
				}
				else {
					ifstream fin2( parameters.condition );
					vector<vector<Literal>> terms;
					Read_Assignments( fin2, terms );
					fin2.close();
					for ( vector<Literal> & term: terms ) {
						manager.Uniformly_Sample_With_Condition( rand_gen, bddc, samples, term );
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
				manager.Display_OBDDC_dot( fout, bddc );
				fout.close();
			}
		}
	}
};


}


#endif  // _Compiler_h_
