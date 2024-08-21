#ifndef _Preprocessor_h_
#define _Preprocessor_h_

#include "Solver.h"
#include "Solver_Krom.h"
#include "Primitive_Types/Gate_Circuit.h"
#include "minisatInterface.h"
#include "CadiBack.h"


namespace KCBox {


class Preprocessor: public Solver
{
protected:
	unsigned _fixed_num_long_clauses;  // old + 3-learnts
	vector<Clause> _long_learnts;  // record long learnts temporarily
	vector<Literal> * _binary_learnts;  // record binary learnts temporarily
	Literal * _lit_equivalences;  /// NOTE: position lit records the equivalent literal of lit
	unsigned _fixed_num_vars;  /// unary_clauses.size() + the number of equivalent literals
	vector<AND_Gate> _and_gates;
protected:
	bool * _lit_appeared;  // use it in a higher level if lit_seen will be occupied in a low level
	bool * _model_seen;  // model_seen[lit] is true means that some model satisfies lit
	Literal * _lit_stack;  // used in recursive algorithm
	unsigned * _lit_search_state;  // used in Strongly_Connected_Component
	unsigned * _lit_index;  // used in Strongly_Connected_Component
	unsigned * _lit_lowlink;  // used in Strongly_Connected_Component
	Literal * _active_lits;  // used in Strongly_Connected_Component, IBCP
	Variable * _var_map;  // used for renaming formulas
	Literal * _lit_map;  // used for renaming formulas
	vector<Literal> * _equivalent_lit_sets;  // it is sorted and each cluster is also sorted, and used for optimize Replace_Equivalent_Lit()
	unsigned _equivalent_lit_cluster_size;
	vector<unsigned> * _long_lit_membership_lists;  /// literal membership
	Solver_Krom * _solver_krom;  // max_var is assigned when compiled
	CadiBack * _cadiback;
public:
	Preprocessor();
	~Preprocessor();
	void Reset();   /// this function should be called after calling Preprocess()
	void operator = ( Preprocessor & another );
	void Open_Oracle_Mode( Variable var_bound );
	void Close_Oracle_Mode();
	void Switch_Recognizing_Backbone( bool is_on ) { running_options.recognize_backbone = is_on; }
	void Switch_Blocking_Clauses( bool is_on ) { running_options.block_clauses = is_on; }
	void Switch_Blocking_Lits( bool is_on ) { running_options.block_lits = is_on; }
	void Switch_Detecting_lit_equivalence( bool is_on ) { running_options.detect_lit_equivalence = is_on; }
	void Switch_Detecting_Binary_Learnts_Resolution( bool is_on ) { running_options.detect_binary_learnts_resolution = is_on; }
	void Switch_Detecting_Binary_Learnts_BCP( bool is_on ) { running_options.detect_binary_learnts_bcp = is_on; }
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	bool Preprocess( CNF_Formula & cnf, vector<Model *> & models );  /// NOTE: <models> is used to gather the models generated in the process, and the initial elements MUST be models of cnf and be allocated by model_pool
protected:
	bool Preprocess( vector<Model *> & models );
	bool Get_All_Imp_Init_External( vector<Model *> & models );
	bool Get_All_Imp_Init_MiniSat( vector<Model *> & models );
	void Prepare_Ext_Clauses_Without_Omitted_Vars( vector<vector<int>> & clauses, bool * var_filled );  // mark the omitted variable in var_omitted
	bool Get_All_Imp_Init_CaDiCaL( vector<Model *> & models );
	void Prepare_CadiBack();
	bool Replace_Equivalent_Lit_First();  // called before computing all implied literals
	void Replace_Equivalent_Lit_Binary_Clauses_First();  // no learnt clauses, might generate unit clauses
	void Replace_Equivalent_Lit_Long_Clauses_First();  // no learnt clauses, might generate unit clauses
	void Replace_Equivalent_Lit_Binary_Learnts_First();
	void Replace_Equivalent_Lit_Long_Learnts_First();
	void Get_All_Imp_Init( vector<Model *> & models );
	void Mark_Models( vector<Model *> & models );
	void Prepare_Originial_Binary_Clauses_For_BBR();
	void Recognize_Non_Implied_Literals( Model * seed_model, vector<Model *> & models );
	Literal Pick_Imp_Init_Heuristic( Variable & start );
	bool Imply_Lit( vector<Model *> & models, Literal lit );
	bool Imply_Lit_External( vector<Model *> & models, Literal lit );  // there exists an external level that assigned lit
	void Add_Marked_Model( vector<int8_t> & minisat_model, vector<Model *> & models );
	void Add_Marked_Model( vector<Model *> & models );
	inline bool Learnts_Exploded();
	void Filter_Long_Learnts();  // first delete the learnt clauses with more than 3 literals, and if still exploded, delete all long learnt clauses
	void Simplify_Binary_Clauses_By_Unary();
	inline void Remove_Old_Binary_Clause_Half( unsigned lit, unsigned pos );
	void Simplify_Long_Clauses_By_Unary();
	inline void Remove_Old_Long_Clause_No_Watch( unsigned pos );  // not considering watched list
	void Add_Old_Binary_Clause( Literal lit1, Literal lit2 );
	inline void Remove_Long_Learnt_No_Watch( unsigned pos );  // not considering watched list
	void Simplify_Lit_Equivalences_By_Unary();
	void Eliminate_Redundancy();  // block literals and remove clauses
	void Store_Long_Learnts();
	void Store_Binary_Learnts( unsigned lit );
	void Vivification();
	void Remove_Old_Binary_Clause_No_Learnt( Literal lit, unsigned pos );
	bool Imply_Binary_Clause_BCP( Literal lit1, Literal lit2 );  // use BCP to approximately determine whether implies binary clause
	bool Imply_Long_Clause_BCP( Clause & clause );  // use BCP to approximately determine whether implies clause
	void Add_Old_Binary_Clause_Fixed_No_Learnt( Literal lit1, Literal lit2, unsigned pos );  // fix the position of lit2 in binary_clauses[lit1]
	Clause Pull_Old_Long_Clause_No_Learnt( unsigned pos );
	void Add_Old_Long_Clause_Fixed_No_Learnt( Clause & clause, unsigned pos );  // not update heur
	void Block_Lits();
	bool Imply_Long_Clause_BCP( Big_Clause & clause );  // use BCP to approximately determine whether implies clause
	void Block_Lits_Improved();
	void Block_Lits_In_Clause( unsigned i );  // long_clauses[i] are copied to big_clause because it will change when BCP
	inline void Erase_Fixed_Lit_From_Long_Clause( unsigned cl_pos, Literal lit );
	inline void Remove_Old_Long_Clause_No_Learnt( unsigned pos );
	void Recover_Binary_Learnts( unsigned lit );
	void Block_Lits_In_Extra_Clause( Clause & clause );
	void Block_Lits_In_Extra_Clause( Big_Clause & clause );
	bool Replace_Equivalent_Lit();
	bool Detect_Lit_Equivalence();
	bool Detect_Lit_Equivalence_Naive();
	void Detect_Binary_Learnts();
	void Detect_Binary_Learnts_Resolution();
	void Detect_Binary_Learnts_BCP();
	bool Detect_Lit_Equivalence_Tarjan();  // using Tarjan's strongly connected components algorithm
	void Strongly_Connected_Component( Literal source );  /// Tarjan's strongly connected components algorithm, the source is stored as component[0]
	bool Detect_Lit_Equivalence_Transitive();  // transitive closure
	void Cluster_Equivalent_Lits();
	void Replace_Equivalent_Lit_Binary_Clauses();  // no consider learnt clauses
	void Replace_Equivalent_Lit_Long_Clauses();  // no consider learnt clauses
	void Replace_Equivalent_Lit_Binary_Learnts();
	void Replace_Equivalent_Lit_Long_Learnts();
	void Add_Binary_Clause_Naive_Half( Literal lit1, Literal lit2 );  // only push into _binary_clauses[lit1]
	void Clear_Equivalent_lit_Sets();
	bool Detect_Lit_Equivalence_BCP();
	bool Detect_Lit_Equivalence_IBCP();
	void Implied_Literals_Approx( Literal lit, vector<Literal> & imp_lits );
	void Record_Equivalent_Lit_Pair( Literal lit, Literal lit2 );
	void Block_Binary_Clauses();
	bool Non_Unary_Clauses_Empty();
	void Reset_Extra_Binary_Clauses();
	unsigned Analyze_Conflict_Fixed_UIP( Reason confl, unsigned fixed );
	inline void Add_Extra_Binary_Clause_Naive( Literal lit1, Literal lit2 );
	unsigned Analyze_Conflict_Naive( unsigned uip );
	bool Block_Lits_External( vector<Model *> & models );  // block literals and remove clauses
	bool Block_Lits_External_Appliable();
	void Prepare_Ext_Clauses_Without_Omitted_Vars( vector<vector<int>> & simplified, vector<vector<int>> & others, bool * var_filled );  // mark the omitted variable in var_omitted
protected:
	void Verify_Backbone( CNF_Formula & cnf );
	void Verify_Processed_Clauses( CNF_Formula & cnf );
	void Verify_Learnts( CNF_Formula & cnf );
	void Verify_Imply_Clause( Clause & clause );
	void Load_Original_Instance( CNF_Formula & cnf );
	void Verify_Equivalent_Lit_Clusters();
	void Display_Statistics( ostream & out );
	void Display_Temp_Binary_Learnts( ostream & out );
	void Display_Models( vector<Model *> & source, ostream & out );
	void Display_Var_Membership_List( ostream & out );
	void Display_Clauses_For_Verifying_Imp( ostream & out, unsigned old_num_d_stack, unsigned new_num_d_stack );
	void Display_Lit_Equivalence( ostream & out );
	void Display_Equivalent_Lit_Clusters( ostream & out );
public:
	bool Preprocess( unsigned num_vars, vector<Clause> & clauses );  /// clauses will be clear
public:
	bool Preprocess( vector<vector<int>> & eclauses );
public:
	bool Preprocess_Sharp( CNF_Formula & cnf, vector<Model *> & models );  /// NOTE: <models> is used to gather the models generated in the process, and the initial elements MUST be models of cnf and be allocated by model_pool
protected:
	bool Preprocess_Sharp( vector<Model *> & models );
	bool Replace_AND_Gates();
	void Generate_Lit_Membership_Lists();
	bool Detect_Gate( Literal output );  // use _active_lits and _big_learnt
	void Ascertain_Gate( Literal output, Reason confl );  // use _active_lits and _big_learnt
	void Replace_Single_Lit_Equivalence( Literal lit1, Literal lit2 );
	void Replace_Single_Lit_Equivalence_Binary_Clauses( Literal lit1, Literal lit2 );
	void Remove_Old_Binary_Clause( Literal lit, unsigned loc );
	void Replace_Single_Lit_Equivalence_Binary_Learnts( Literal lit1, Literal lit2 );
	void Replace_Single_Lit_Equivalence_Long_Clauses( Literal lit1, Literal lit2 );
	void Add_To_Lit_Membership_Lists( unsigned clauseID );
	void Remove_From_Lit_Membership_Lists( unsigned clauseID );
	int Gain_Of_Gate_Substitution( AND_Gate & gate );
	void Simplify_Clause( Big_Clause & clause );
	void Gate_Substitution_Binary_Clause( AND_Gate & gate );  // gate[0] <-> gate[1] and gate[2] and ...
	unsigned Add_Old_Clause_Binary_Learnt( Big_Clause & clause );  // return the true length
	void Gate_Substitution_Long_Clause( AND_Gate & gate );  // gate[0] <-> gate[1] and gate[2] and ...
	void Gate_Substitution_Binary_Learnt( AND_Gate & gate );  // gate[0] <-> gate[1] and gate[2] and ...
	void Add_Only_Old_Binary_Clause( Big_Clause & clause );  // return the true length
protected:
	void Shrink_Max_Var();
	void Check_Var_Appearances();
	void Remove_Unseen_Lits_In_Learnts();
	void Erase_Fixed_Lit_From_Long_Clause( unsigned cl_pos, unsigned lit_pos );
	bool Generate_Models_External( vector<Model *> & models );
protected:
	void Display_Statistics_Sharp( ostream & out );
	void Verify_AND_Gate( AND_Gate & gate );
	void Verify_Watched_Lists();
	void Verify_Long_Lit_Membership_Lists();
public:
	bool Preprocess_Sharp( WCNF_Formula & cnf, vector<Model *> & models );  /// NOTE: <models> is used to gather the models generated in the process, and the initial elements MUST be models of cnf and be allocated by model_pool
protected:
	bool Preprocess_Sharp( const vector<double> & weights, vector<Model *> & models );
	bool Replace_AND_Gates( const vector<bool> & weight_equ );
public:
	void Transform_Exterior_Into_Clauses();  // transform literal equivalences and AND-gates into clauses
	unsigned Lit_Equivalency_Size() const { return _fixed_num_vars - _unary_clauses.size() - _and_gates.size(); }
	CNF_Formula * Output_Processed_Clauses();  /// the output result includes the clauses represented by lit_equivalence
	void Output_Processed_Ext_Clauses( vector<vector<int>> & clauses );  /// the output result includes the clauses represented by lit_equivalence
	void Output_Same_Count_Ext_Clauses( int & num_vars, vector<vector<int>> & clauses, int & num_omitted_vars );  /// the output formula has the same number of models as the input formula
	void Output_Equivalent_Literal_Pairs( vector<int> & elits );  /// the output result is lit_equivalence
	void Output_Unary_Clauses( vector<Literal> & units );
	void Output_Binary_Clauses( vector<Literal> & binary_clauses, vector<Literal> & binary_learnts );
	void Output_Long_clauses( vector<Clause> & clauses );
	void Display_Processed_Clauses( ostream & out, bool eq = true );  /// the output result includes the clauses represented by lit_equivalence
	size_t Memory();  /// not the exact memory (omit some auxiliary memory)
	unsigned Num_Omitted_Vars();
protected:
    void Draw_Lit_Equivalency( vector<Literal> & equ_pairs );
protected:
	BigFloat Normalize_Weights( const vector<double> & original_weights, vector<double> & normalized_weights );
	BigFloat Normalize_Weights( const vector<double> & original_weights, BigFloat * normalized_weights );
	void Shrink_Max_Var( BigFloat * normalized_weights );

//-------------------------------------------------------------
public:
	static void Debug()
	{
		Preprocessor preprocessor;
		preprocessor.debug_options.verify_processed_clauses = true;
		preprocessor.debug_options.verify_learnts = false;
		vector<Model *> models;
		bool weighted = true;
		bool sharp = true;
		if ( true ) {
			if ( !weighted ) {
				ifstream fin( "../benchmarks/kc-domain-benchmarks-pmc/BayesianNetwork_or-50-10-3-UC-10.cnf" );
				CNF_Formula cnf( fin );
				if ( !sharp ) preprocessor.Preprocess( cnf, models );
				else preprocessor.Preprocess_Sharp( cnf, models );
			}
			else {
				ifstream fin( "instances-weighted/prob.cnf" );
				WCNF_Formula cnf( fin, 1 );
				preprocessor.Preprocess_Sharp( cnf, models );
			}
			preprocessor.Free_Models( models );
//			preprocessor.Display_Processed_Clauses( cout );
			system( "./pause" );
			ofstream fout( "results.cnf" );
			preprocessor.Display_Processed_Clauses( fout );
			fout.close();
			preprocessor.Reset();
		}
		else {
			Random_Generator rand_gen;
			for ( unsigned i = 0; i < 10000; i++ ) {
				rand_gen.Reset( i );
				cout << "========== " << i << " ==========" << endl;
				unsigned nv = 60, nc = 120;
				CNF_Formula cnf( rand_gen, nv, nc, 2, 4 );
				cnf.Sort_Clauses();
				cout << cnf;
//				ofstream fout( "debug.cnf" );
//				fout << cnf;
//				fout.close();
				if ( !sharp ) preprocessor.Preprocess( cnf, models );
				else preprocessor.Preprocess_Sharp( cnf, models );
				preprocessor.Free_Models( models );
//				preprocessor.Display_Processed_Clauses( cout );
				preprocessor.Reset();
//				system( "./pause" );
			}
		}
	}
	static void Test( const char * infile, Preprocessor_Parameters & parameters, bool quiet )
	{
		ifstream cnf_fin;
		cnf_fin.open( infile );
		CNF_Formula cnf( cnf_fin );
		cnf_fin.close();
		Preprocessor preprocessor;
		preprocessor.running_options.sat_solver = Parse_Solver( parameters.solver );
		preprocessor.running_options.block_clauses = !parameters.no_rm_clauses;
		preprocessor.running_options.detect_lit_equivalence = !parameters.no_lit_equ;
		preprocessor.running_options.display_preprocessing_process = !quiet;
		if ( quiet ) {
			preprocessor.running_options.profile_solving = Profiling_Close;
			preprocessor.running_options.profile_preprocessing = Profiling_Close;
		}
		if ( parameters.competition ) preprocessor.running_options.display_prefix = "c o ";
		vector<Model *> models;
		bool sat = preprocessor.Preprocess( cnf, models );
		if ( !sat ) {
			if ( parameters.out_file == nullptr ) {
				cout << "p cnf 1 2" << endl;
				cout << "1 0" << endl;
				cout << "-1 0" << endl;
			}
			else {
				ofstream fout( parameters.out_file );
				fout << "p cnf 1 2" << endl;
				fout << "1 0" << endl;
				fout << "-1 0" << endl;
				fout.close();
			}
		}
		else if ( parameters.out_file == nullptr ) {
			preprocessor.Display_Processed_Clauses( cout );
		}
		else {
			ofstream fout( parameters.out_file );
			preprocessor.Display_Processed_Clauses( fout );
			fout.close();
		}
		preprocessor.Reset();
	}
};


}


#endif
