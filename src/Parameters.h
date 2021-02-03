#ifndef _Parameters_h_
#define _Parameters_h_

#include "Template_Library/Basic_Functions.h"
#include "Template_Library/Basic_Structures.h"
#include "Template_Library/Options.h"
#include "Primitive_Types/Assignment.h"
#include "Component_Types/Bounded_Component.h"


namespace KCBox {


#define SAT_REASON_LITERAL false
#define SAT_REASON_CLAUSE true


struct Preprocessor_Parameters: public Tool_Parameters
{
	StringOption out_file;
	Preprocessor_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		out_file( "--out", "the output file with the processed instance", nullptr )
	{
		Add_Option( &out_file );
	}
};

struct Counter_Parameters: public Tool_Parameters
{
	BoolOption weighted;
	BoolOption exact;
	BoolOption static_heur;
	IntOption heur;
	FloatOption memo;
	IntOption kdepth;
	IntOption format;
	Counter_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		weighted( "--weighted", "weighted model counting", false ),
		exact( "--exact", "exact or probabilistic exact", true ),
		static_heur( "--static", "focusing on static heuristic", false ),
		heur( "--heur", "heuristic strategy (0: auto, 1: minfill, 2: LinearLRW, 3: Dminfill, 4: VSADS, 5: DLCS, 6: DLCP)", 0, 0, 6 ),
		memo( "--memo", "the available memory in GB", 4 ),
		kdepth( "--kdepth", "maximum kernelization depth", 128 ),
		format( "--format", "MC Competition format (0), miniC2D format (1)", 0, 0, 1 )
	{
//		Add_Option( &weighted );
//		Add_Option( &exact );
//		Add_Option( &static_heur );
		Add_Option( &heur );
		Add_Option( &memo );
		Add_Option( &kdepth );
//		Add_Option( &format );
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( static_heur ) {
			if ( heur > 1 ) return false;
		}
		if ( !weighted ) {
			if ( format.Exists() ) return false;
		}
		return true;
	}
};

struct Compiler_Parameters: public Tool_Parameters
{
	IntOption lang;
	StringOption out_file;
	FloatOption memo;
	BoolOption CT;
	IntOption kdepth;
	Compiler_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		lang( "--lang", "KC languages ROBDD (0), OBDD[AND] (1), R2-D2 (2), and CCDD (3)", 1 ),
		out_file( "--out", "the output file with compilation", nullptr ),
		memo( "--memo", "the available memory in GB", 4 ),
		CT( "--CT", "performing model counting query", false ),
		kdepth( "--kdepth", "maximum kernelization depth (not applicable for BDD and OBDD[AND])", 2 )
	{
//		Add_Option( &lang );
		Add_Option( &out_file );
		Add_Option( &memo );
		Add_Option( &CT );
//		Add_Option( &kdepth );
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( lang == 0 || lang == 1 ) {
			if ( kdepth.Exists() ) return false;
		}
		return true;
	}
};

enum Heuristic
{
	AutomaticalHeur = 0,
	minfill,
	LinearLRW,  // Linear Largest Related Weight
	FixedLinearOrder,
	LexicographicOrder,
	Dminfill,  // Dynamic minfill
	VSIDS,  // Variable State Independent Decaying Sum
	VSADS,  // Variable State Aware Decaying Sum
	DLCS,  // Dynamic Largest Combined Sum
	DLCP,  // Dynamic Largest Combined Production
	MostBalanced,
	IndependentSupport
};

extern inline bool Is_Linear_Ordering( Heuristic heur )
{
	if ( heur == AutomaticalHeur || \
		heur == LexicographicOrder || heur == minfill || heur == LinearLRW || \
		heur == FixedLinearOrder ) return true;
	else return false;
}

extern inline lbool Is_Ordering_minfill( Heuristic heur )
{
	if ( heur == AutomaticalHeur ) return lbool::unknown;
	else if ( heur == minfill || heur == Dminfill ) return lbool(true);
	else return lbool(false);
}

enum Heuristic_Literal_Structure
{
	Heuristic_Literal_Unsorted_List = 0,
	Heuristic_Literal_Sorted_List,
	Heuristic_Literal_Heap
};

enum Implicate_Computing_Strategy
{
	Automatical_Imp_Computing = 0,
	Partial_Implicit_BCP,  /// used in sharpSAT
	Full_Implicit_BCP,  /// used in ydotlai's compilers and counters
	SAT_Imp_Computing  /// employ SAT solver to computing exact implied literals
};

enum Literal_Equivalence_Detecting_Strategy
{
	Literal_Equivalence_Detection_Naive = 0,
	Literal_Equivalence_Detection_Tarjan,
	Literal_Equivalence_Detection_BCP,
	Literal_Equivalence_Detection_IBCP
};

enum Dynamic_Decomposition_Strategy
{
	Decompose_With_Sorting = 0,  /// used in ydotlai's compilers and counters
	Decompose_Without_Sorting  /// improved version of the one used in sharpSAT
};

enum Profiling_Level
{
	Profiling_Close = 0,
	Profiling_Abstract,
	Profiling_Detail
};

struct Running_Options
{
/// parameters of solver
	Variable variable_bound;  // used for oracle mode
	double sat_heur_decay_factor;
	double sat_heur_cumulative_inc;
	double sat_heur_bound;
	bool sat_restart_activate;
	unsigned sat_restart_trigger_init;  // the initialized number of new learnt clauses trigger restarting
	double sat_restart_trigger_inc;
	unsigned sat_restart_max;  // the maximum times of restart, and after that, external solver will be called
	bool sat_employ_external_solver;
	bool sat_employ_external_solver_always;
	Heuristic_Literal_Structure sat_heur_lits;
	bool display_solving_process;
	Profiling_Level profile_solving;
/// parameters of preprocessor
	bool recognize_backbone;
	bool recognize_backbone_external;
	bool block_clauses;
	bool block_lits;
	bool detect_lit_equivalence_first;
	bool detect_lit_equivalence;
	Literal_Equivalence_Detecting_Strategy lit_equivalence_detecting_strategy;
	bool detect_binary_learnts_resolution;
	bool detect_binary_learnts_bcp;
	bool detect_AND_gates;
	bool keep_binary_learnts;
	bool recover_exterior;  // represented into clauses
	bool display_preprocessing_process;
	Profiling_Level profile_preprocessing;
/// parameters of inprocessor
	unsigned treewidth;  /// the minfill treewidth of the current problem
	Heuristic var_ordering_heur;  /// the current heuristic strategy
	bool mixed_var_ordering;
	bool phase_selecting;
	Implicate_Computing_Strategy imp_strategy;
	bool mixed_imp_computing;  /// first SAT and then Partial_Implicit_BCP
	Dynamic_Decomposition_Strategy decompose_strategy;
	bool display_inprocessing_process;
	Profiling_Level profiling_inprocessing;
/// parameters of extensive inprocessor
	unsigned max_kdepth;
	unsigned kernelizing_step;
	bool display_kernelizing_process;
	Profiling_Level profiling_ext_inprocessing;
/// parameters of compiler
	float max_memory;  /// in G bytes
	unsigned trivial_variable_bound;  /// NOTE: it is trivial for the problems whose maximum variable exceeds variable_bound or whose long clauses are more than 2 * variable_bound
	unsigned treewidth_bound;  /// NOTE: when the minfill treewidth is greater than treewidth_bound, we will terminate the construction of Simple_TreeD
	bool activate_easy_compiler;
	bool compute_duplicate_rate;
	bool erase_useless_cacheable_component;
	unsigned removing_redundant_nodes_trigger;
	bool display_compiling_process;
	bool display_memory_status;
	Profiling_Level profile_compiling;
/// parameters of counter
	bool static_heur;
	bool display_counting_process;
	Profiling_Level profile_counting;
/// parameters of oracle
	Profiling_Level profile_oracle;
	size_t oracle_memory_limit;
	Running_Options()
	{
		variable_bound = Variable::undef;  /// NOTE: only Preprocessor and its inherited class can open this mode
		/// solver
		sat_heur_decay_factor = 0.99;
		sat_heur_cumulative_inc = 1;
		sat_heur_bound = 1e100;
		sat_restart_activate = true;
		sat_restart_trigger_init = 100;
		sat_restart_trigger_inc = 1.5;
		sat_restart_max = 2;
		sat_employ_external_solver = true;
		sat_employ_external_solver_always = false;
		sat_heur_lits = Heuristic_Literal_Heap;
		display_solving_process = false;
		profile_solving = Profiling_Abstract;
		/// preprocessor
		recognize_backbone = true;
		recognize_backbone_external = false;  /// whether using Backbone_Recognizer or not
		block_clauses = true;
		block_lits = true;
		detect_lit_equivalence_first = false;
		lit_equivalence_detecting_strategy = Literal_Equivalence_Detection_BCP;
		detect_lit_equivalence = true;
		detect_binary_learnts_resolution = true;
		detect_binary_learnts_bcp = false;
		detect_AND_gates = true;
		keep_binary_learnts = false;
		recover_exterior = false;
		display_preprocessing_process = true;
		profile_preprocessing = Profiling_Detail;
		/// inprocessor
		var_ordering_heur = AutomaticalHeur;
		mixed_var_ordering = true;
		phase_selecting = true;
		imp_strategy = Automatical_Imp_Computing;  // Automatical_Imp_Computing, Partial_Implicit_BCP, Full_Implicit_BCP, SAT_Imp_Computing
		mixed_imp_computing = true;
		decompose_strategy = Decompose_Without_Sorting;
		display_inprocessing_process = true;
		profiling_inprocessing = Profiling_Detail;
		/// extensive inprocessor
		max_kdepth = 2;
		kernelizing_step = 64;
		display_kernelizing_process = true;
		profiling_ext_inprocessing = Profiling_Detail;
		/// compiler
		max_memory = 4;  // 4 GB
		trivial_variable_bound = 1024;
		treewidth_bound = BOUNDED_TREEWIDTH;
		activate_easy_compiler = true;
		erase_useless_cacheable_component = true;
		removing_redundant_nodes_trigger = 2000000;
		display_compiling_process = true;
		profile_compiling = Profiling_Abstract;
		/// counter
		static_heur = false;
		display_counting_process = true;
		profile_counting = Profiling_Abstract;
		/// oracle
		profile_oracle = Profiling_Abstract;
		oracle_memory_limit = 100 * 1024 * 1024;  // 100M
	}
	void Display( ostream & out )
	{
		out << "variable_bound = " << variable_bound << endl;  /// NOTE: only Preprocessor and its inherited class can open this mode
		/// solver
		out << "sat_heur_decay_factor = " << sat_heur_decay_factor << endl;
		out << "sat_heur_cumulative_inc = " << sat_heur_cumulative_inc << endl;
		out << "sat_heur_bound = " << sat_heur_bound << endl;
		out << "sat_restart_activate = " << sat_restart_activate << endl;
		out << "sat_restart_trigger_init = " << sat_restart_trigger_init << endl;
		out << "sat_restart_trigger_inc = " << sat_restart_trigger_inc << endl;
		out << "sat_restart_max = " << sat_restart_max << endl;
		out << "sat_employ_external_solver = " << sat_employ_external_solver << endl;
		out << "sat_employ_external_solver_always = " << sat_employ_external_solver_always << endl;
		out << "sat_heur_lits = " << sat_heur_lits << endl;
		out << "display_solving_process = " << display_solving_process << endl;
		out << "profile_solving = " << profile_solving << endl;
		/// preprocessor
		out << "recognize_backbone = " << recognize_backbone << endl;
		out << "recognize_backbone_external = " << recognize_backbone_external << endl;  /// whether using Backbone_Recognizer or not
		out << "block_clauses = " << block_clauses << endl;
		out << "block_lits = " << block_lits << endl;
		out << "detect_lit_equivalence_first = " << detect_lit_equivalence_first << endl;
		out << "lit_equivalence_detecting_strategy = " << lit_equivalence_detecting_strategy << endl;
		out << "detect_lit_equivalence = " << detect_lit_equivalence << endl;
		out << "detect_binary_learnts_resolution = " << detect_binary_learnts_resolution << endl;
		out << "detect_binary_learnts_bcp = " << detect_binary_learnts_bcp << endl;
		out << "detect_AND_gates = " << detect_AND_gates << endl;
		out << "keep_binary_learnts = " << keep_binary_learnts << endl;
		out << "recover_exterior = " << recover_exterior << endl;
		out << "display_preprocessing_process = " << display_preprocessing_process << endl;
		out << "profile_preprocessing = " << profile_preprocessing << endl;
		/// inprocessor
		out << "var_ordering_heur = " << var_ordering_heur << endl;
		out << "mixed_var_ordering = " << mixed_var_ordering << endl;
		out.setf(std::ios_base::boolalpha);
		out << "phase_selecting = " << phase_selecting << endl;
		out.unsetf(std::ios_base::boolalpha);
		out << "imp_strategy = " << imp_strategy << endl;  // Automatical_Imp_Computing, Partial_Implicit_BCP, Full_Implicit_BCP, SAT_Imp_Computing
		out << "mixed_imp_computing = " << mixed_imp_computing << endl;
		out << "decompose_strategy = " << decompose_strategy << endl;
		out << "display_inprocessing_process = " << display_inprocessing_process << endl;
		out << "profiling_inprocessing = " << profiling_inprocessing << endl;
		/// extensive inprocessor
		out << "max_kdepth = " << max_kdepth << endl;
		out << "kernelizing_step = " << kernelizing_step << endl;
		out << "display_kernelizing_process = " << display_kernelizing_process << endl;
		out << "profiling_ext_inprocessing = " << profiling_ext_inprocessing << endl;
		/// compiler
		out << "max_memory = " << max_memory << endl;  // 4 GB
		out << "trivial_variable_bound = " << trivial_variable_bound << endl;
		out << "treewidth_bound = " << treewidth_bound << endl;
		out << "activate_easy_compiler = " << activate_easy_compiler << endl;
		out << "erase_useless_cacheable_component = " << erase_useless_cacheable_component << endl;
		out << "removing_redundant_nodes_trigger = " << removing_redundant_nodes_trigger << endl;
		out << "display_compiling_process = " << display_compiling_process << endl;
		out << "profile_compiling = " << profile_compiling << endl;
		/// counter
		out << "static_heur = " << static_heur << endl;
		out << "display_counting_process = " << display_counting_process << endl;
		out << "profile_counting = " << profile_counting << endl;
		/// oracle
		out << "profile_oracle = " << profile_oracle << endl;
		out << "oracle_memory_limit = " << oracle_memory_limit << endl;  // 100M
	}
};

struct Debug_Options
{
	/// solver
	bool verify_satisfiability;
	bool verify_model;
	bool verify_learnts;
	/// preprocessor
	bool verify_AND_gates;
	bool verify_processed_clauses;
	/// compiler
	bool verify_compilation;
	bool verify_component_compilation;
	/// counter
	bool verify_count;
	bool verify_component_count;
	Debug_Options()
	{
		/// solver
		verify_satisfiability = false;
		verify_model = false;
		verify_learnts = false;
		/// preprocessor
		verify_AND_gates = false;
		verify_processed_clauses = false;
		/// compiler
		verify_compilation = false;
		verify_component_compilation = false;
		/// counter
		verify_count = false;
		verify_component_count = false;
	}
};

struct Statistics
{
	/// solver
	double time_solve;
	double time_external_solve;
	unsigned num_solve;
	unsigned num_unsat_solve;
	unsigned num_external_solve;
	unsigned num_binary_learnt;
	unsigned num_learnt;
	void Init_Solver()
	{
		time_solve = 0;
		time_external_solve = 0;
		num_solve = 0;
		num_unsat_solve = 0;
		num_external_solve = 0;
		num_binary_learnt = 0;
		num_learnt = 0;
	}
	/// preprocess
	double time_preprocess;
	double time_block_clauses;
	double time_block_lits;
	double time_replace_lit_equivalences;
	double time_replace_gates;
	void Init_Preprocessor_Single()
	{
		time_preprocess = 0;
		time_block_clauses = 0;
		time_block_lits = 0;
		time_replace_lit_equivalences = 0;
		time_replace_gates = 0;
	}
	void Init_Preprocessor()
	{
		Init_Solver();
		Init_Preprocessor_Single();
	}
	/// inprocess
	double time_minfill;
	double time_ibcp;
	double time_dynamic_decompose;
	double time_dynamic_decompose_sort;
	void Init_Inprocessor_Single()
	{
		time_minfill = 0;
		time_ibcp = 0;
		time_dynamic_decompose = 0;
		time_dynamic_decompose_sort = 0;
	}
	void Init_Inprocessor()
	{
		Init_Preprocessor();
		Init_Inprocessor_Single();
	}
	/// extensive compiler
	double time_kernelize;
	double time_kernelize_block_lits;
	double time_kernelize_vivification;
	double time_kernelize_lit_equ;
	unsigned max_kdepth;
	unsigned max_non_trivial_kdepth;
	unsigned num_kernelizations;
	unsigned num_non_trivial_kernelizations;
	void Init_Extensive_Inprocessor_Single()
	{
		time_kernelize = 0;
		time_kernelize_block_lits = 0;
		time_kernelize_vivification = 0;
		time_kernelize_lit_equ = 0;
		max_kdepth = 0;
		max_non_trivial_kdepth = 0;
		num_kernelizations = 0;
		num_non_trivial_kernelizations = 0;
	}
	void Init_Extensive_Inprocessor()
	{
		Init_Extensive_Inprocessor_Single();
		Init_Inprocessor();
	}
	/// count or compile
	double time_compile;
	double time_gen_cnf_cache;
	double time_gen_dag;
	void Init_Compiler_Single()
	{
		time_compile = 0;
		time_gen_cnf_cache = 0;
		time_gen_dag = 0;
	}
	void Init_Compiler()
	{
		Init_Inprocessor();
		Init_Compiler_Single();
	}
	double time_count;
	void Init_Counter_Single()
	{
		time_count = 0;
		time_gen_cnf_cache = 0;
	}
	void Init_Counter()
	{
		Init_Inprocessor();
		Init_Counter_Single();
	}
	/// oracle
};






}


#endif
