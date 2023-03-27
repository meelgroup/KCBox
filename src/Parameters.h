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
	BoolOption competition;
	FloatOption diffversion;
	BoolOption weighted;
	BoolOption exact;
	BoolOption static_heur;
	StringOption heur;
	FloatOption memo;
	IntOption kdepth;
	IntOption format;
	Counter_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		competition( "--competition", "working for mc competition", false ),
		diffversion( "--diffversion", "running with a given version", 1 ),
		weighted( "--weighted", "weighted model counting", false ),
		exact( "--exact", "exact or probabilistic exact", true ),
		static_heur( "--static", "focusing on static heuristic", false ),
		heur( "--heur", "heuristic strategy (auto, minfill, LinearLRW, VSADS, DLCS, DLCP, dynamic_minfill)", "auto" ),
		memo( "--memo", "the available memory in GB", 4 ),
		kdepth( "--kdepth", "maximum kernelization depth", 128 ),
		format( "--format", "MC Competition format (0), miniC2D format (1)", 0, 0, 1 )
	{
		Add_Option( &competition );
		Add_Option( &diffversion );
		Add_Option( &weighted );
		Add_Option( &exact );
		Add_Option( &static_heur );
		Add_Option( &heur );
		Add_Option( &memo );
		Add_Option( &kdepth );
		Add_Option( &format );
		Add_Version( 1 );
		if ( diffversion != _versions.back() ) {
			cerr << "Warning: the default version of " << tool_name << " is " << diffversion << " rather than the latest version " << _versions.back() << endl;
		}
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( diffversion.Exists() && !Search_Exi_Nonempty( _versions, float(diffversion) ) ) {
			cerr << "Current versions:";
			for ( float ver: _versions ) {
				cerr << " " << ver;
			}
			cerr << endl;
			return false;
		}
		if ( strcmp( heur, "auto") != 0 && strcmp( heur, "minfill") != 0 && \
			strcmp( heur, "LinearLRW") != 0 && strcmp( heur, "VSADS") != 0 && strcmp( heur, "DLCS") != 0 && \
			strcmp( heur, "DLCP") != 0 && strcmp( heur, "dynamic_minfill") != 0 ) {
			return false;
		}
		if ( static_heur && strcmp( heur, "auto") != 0 && strcmp( heur, "minfill") != 0 && \
			strcmp( heur, "LinearLRW") != 0 ) {
			return false;
		}
		if ( !weighted ) {
			if ( format.Exists() ) return false;
		}
		return true;
	}
};

struct Compiler_Parameters: public Tool_Parameters
{
	StringOption lang;
	StringOption out_file;
	StringOption heur;
	FloatOption memo;
	BoolOption CT;
	IntOption US;
	IntOption kdepth;
	Compiler_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		lang( "--lang", "KC language ROBDD, OBDD[AND], R2-D2, or CCDD", "OBDD[AND]" ),
		out_file( "--out", "the output file with compilation", nullptr ),
		heur( "--heur", "heuristic strategy (auto, minfill, FlowCutter, LinearLRW, VSADS, DLCP, or dynamic_minfill)", "auto" ),
		memo( "--memo", "the available memory in GB", 4 ),
		CT( "--CT", "performing model counting", false ),
		US( "--US", "performing uniform sampling", 1 ),
		kdepth( "--kdepth", "maximum kernelization depth (not applicable for BDD and OBDD[AND])", 128 )
	{
		Add_Option( &lang );
		Add_Option( &out_file );
		Add_Option( &heur );
		Add_Option( &memo );
		Add_Option( &CT );
		Add_Option( &US );
		Add_Option( &kdepth );
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( strcmp( lang, "ROBDD") == 0 || strcmp( lang, "OBDD[AND]") == 0 ) {
			if ( kdepth.Exists() ) return false;
		}
		if ( strcmp( lang, "CCDD") != 0 ) {
			if ( US.Exists() ) return false;
		}
		if ( strcmp( lang, "ROBDD") != 0 && strcmp( lang, "OBDD[AND]") != 0 && \
			strcmp( lang, "R2-D2") != 0 && strcmp( lang, "CCDD") != 0 ) {
			return false;
		}
		if ( strcmp( heur, "auto") != 0 && strcmp( heur, "minfill") != 0 && \
			strcmp( heur, "FlowCutter") != 0 && strcmp( heur, "LinearLRW") != 0 && \
			strcmp( heur, "VSADS") != 0 && strcmp( heur, "DLCP") != 0 && strcmp( heur, "dynamic_minfill") != 0 ) {
			return false;
		}
		return true;
	}
};

struct Sampler_Parameters: public Tool_Parameters
{
	BoolOption weighted;
	BoolOption exact;
	IntOption nsamples;
	FloatOption memo;
	IntOption format;
	StringOption out_file;
	Sampler_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		weighted( "--weighted", "weighted sampling", false ),
		exact( "--exact", "exactly uniform", true ),
		nsamples( "--nsamples", "number of samples", 1 ),
		memo( "--memo", "the available memory in GB", 4 ),
		format( "--format", "MC Competition format (0), miniC2D format (1)", 0, 0, 1 ),
		out_file( "--out", "the output file for samples", "samples.txt" )
	{
		Add_Option( &weighted );
		Add_Option( &exact );
		Add_Option( &nsamples );
		Add_Option( &memo );
		Add_Option( &format );
		Add_Option( &out_file );
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( !weighted ) {
			if ( format.Exists() ) return false;
		}
		return true;
	}
};

struct Approx_Counter_Parameters: public Tool_Parameters
{
	BoolOption weighted;
	StringOption heur;
	FloatOption time;
	FloatOption memo;
	IntOption kdepth;
	IntOption micro;
	IntOption seed;
	IntOption format;
	BoolOption lower;
	FloatOption confidence;
	Approx_Counter_Parameters( const char * tool_name ): Tool_Parameters( tool_name ),
		weighted( "--weighted", "weighted model counting", false ),
		heur( "--heur", "heuristic strategy (auto, minfill, LinearLRW, VSADS, DLCS, DLCP, dynamic_minfill)", "auto" ),
		time( "--time", "timeout in seconds", 3600 ),
		memo( "--memo", "the available memory in GB", 4 ),
		kdepth( "--kdepth", "maximum kernelization depth", 128 ),
		micro( "--micro", "number of microcompilations", 1024 * 1024 * 1024 ),
		seed( "--seed", "random seed", 0 ),
		format( "--format", "MC Competition format (0), miniC2D format (1)", 0, 0, 1 ),
		lower( "--lower", "computing lower bound", false ),
		confidence( "--confidence", "the confidence of lower bound", 0.99 )
	{
		Add_Option( &weighted );
		Add_Option( &heur );
		Add_Option( &time );
		Add_Option( &memo );
		Add_Option( &kdepth );
		Add_Option( &micro );
		Add_Option( &seed );
		Add_Option( &format );
		Add_Option( &lower );
		Add_Option( &confidence );
	}
	bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		if ( !Tool_Parameters::Parse_Parameters( i, argc, argv ) ) return false;
		if ( strcmp( heur, "auto") != 0 && strcmp( heur, "minfill") != 0 && \
			strcmp( heur, "LinearLRW") != 0 && strcmp( heur, "VSADS") != 0 && strcmp( heur, "DLCS") != 0 && \
			strcmp( heur, "DLCP") != 0 && strcmp( heur, "dynamic_minfill") != 0 ) {
			return false;
		}
		if ( !weighted ) {
			if ( format.Exists() ) return false;
		}
		else {
			if ( kdepth.Exists() ) return false;
		}
		if ( confidence.Exists() ) {
			if ( !lower ) return false;
			if ( confidence <= 0 || confidence >= 1 ) return false;
		}
		return true;
	}
};

enum Heuristic
{
	AutomaticalHeur = 0,
	minfill,
	FlowCutter,
	LinearLRW,  // Linear Largest Related Weight
	FixedLinearOrder,
	LexicographicOrder,
	VSIDS,  // Variable State Independent Decaying Sum
	VSADS,  // Variable State Aware Decaying Sum
	DLCS,  // Dynamic Largest Combined Sum
	DLCP,  // Dynamic Largest Combined Production
	dynamic_minfill,  // dynamic minfill: minfill + DLCP
	MostBalanced,
	IndependentSupport
};

extern inline Heuristic Parse_Heuristic( const char * heur )
{
	if ( strcmp( heur, "auto" ) == 0 ) return AutomaticalHeur;
	else if ( strcmp( heur, "minfill" ) == 0 ) return minfill;
	else if ( strcmp( heur, "FlowCutter" ) == 0 ) return FlowCutter;
	else if ( strcmp( heur, "LinearLRW" ) == 0 ) return LinearLRW;
	else if ( strcmp( heur, "VSADS" ) == 0 ) return VSADS;
	else if ( strcmp( heur, "DLCS" ) == 0 ) return DLCS;
	else if ( strcmp( heur, "DLCP" ) == 0 ) return DLCP;
	else if ( strcmp( heur, "dynamic_minfill" ) == 0 ) return dynamic_minfill;
	else {
		cerr << "ERROR: wrong heuristic!" << endl;
		exit( 0 );
	}
}

extern inline lbool Is_Linear_Ordering( Heuristic heur )
{
	if ( heur == AutomaticalHeur ) return lbool::unknown;
	else if ( heur == LexicographicOrder || heur == minfill || heur == FlowCutter || \
		heur == LinearLRW || heur == FixedLinearOrder ) return lbool(true);
	else return lbool(false);
}

extern inline lbool Is_TreeD_Based_Ordering( Heuristic heur )
{
	if ( heur == AutomaticalHeur ) return lbool::unknown;
	else if ( heur == minfill || heur == dynamic_minfill || heur == FlowCutter ) return lbool(true);
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
	const char * display_prefix;
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
	bool block_lits_external;
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
	float mem_load_factor;
	unsigned trivial_variable_bound;  /// NOTE: it might be trivial for the problems whose maximum variable exceeds variable_bound or whose long clauses are more than 2 * variable_bound
	unsigned trivial_clause_bound;
	float trivial_density_bound;
	float trivial_length_bound;
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
	/// parameters of partial kc
	bool estimate_marginal_probability;
	bool adaptive_sampling;
	float simply_counting_time;
	float sampling_time;
	unsigned sampling_count;
	unsigned sampling_display_interval;
	Profiling_Level profile_partial_kc;
/// parameters of oracle
	Profiling_Level profile_oracle;
	size_t oracle_memory_limit;
	Running_Options()
	{
		display_prefix = "";
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
		block_lits_external = true;
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
		mem_load_factor = 0.5;
		trivial_variable_bound = 1024;
		trivial_clause_bound = trivial_variable_bound * 2;
		trivial_density_bound = 3;
		trivial_length_bound = 0.5;
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
		/// partial kc
		estimate_marginal_probability = true;
		adaptive_sampling = false;
		simply_counting_time = 240;
		sampling_time = 3600;
		sampling_count = UNSIGNED_UNDEF;
		sampling_display_interval = 1;
		profile_partial_kc = Profiling_Abstract;
		/// oracle
		profile_oracle = Profiling_Abstract;
		oracle_memory_limit = 100 * 1024 * 1024;  // 100M
	}
	void Display( ostream & out )
	{
		out << display_prefix << "variable_bound = " << variable_bound << endl;  /// NOTE: only Preprocessor and its inherited class can open this mode
		/// solver
		out << display_prefix << "sat_heur_decay_factor = " << sat_heur_decay_factor << endl;
		out << display_prefix << "sat_heur_cumulative_inc = " << sat_heur_cumulative_inc << endl;
		out << display_prefix << "sat_heur_bound = " << sat_heur_bound << endl;
		out << display_prefix << "sat_restart_activate = " << sat_restart_activate << endl;
		out << display_prefix << "sat_restart_trigger_init = " << sat_restart_trigger_init << endl;
		out << display_prefix << "sat_restart_trigger_inc = " << sat_restart_trigger_inc << endl;
		out << display_prefix << "sat_restart_max = " << sat_restart_max << endl;
		out << display_prefix << "sat_employ_external_solver = " << sat_employ_external_solver << endl;
		out << display_prefix << "sat_employ_external_solver_always = " << sat_employ_external_solver_always << endl;
		out << display_prefix << "sat_heur_lits = " << sat_heur_lits << endl;
		out << display_prefix << "display_solving_process = " << display_solving_process << endl;
		out << display_prefix << "profile_solving = " << profile_solving << endl;
		/// preprocessor
		out << display_prefix << "recognize_backbone = " << recognize_backbone << endl;
		out << display_prefix << "recognize_backbone_external = " << recognize_backbone_external << endl;  /// whether using Backbone_Recognizer or not
		out << display_prefix << "block_clauses = " << block_clauses << endl;
		out << display_prefix << "block_lits = " << block_lits << endl;
		out << display_prefix << "block_lits_external = " << block_lits_external << endl;
		out << display_prefix << "detect_lit_equivalence_first = " << detect_lit_equivalence_first << endl;
		out << display_prefix << "lit_equivalence_detecting_strategy = " << lit_equivalence_detecting_strategy << endl;
		out << display_prefix << "detect_lit_equivalence = " << detect_lit_equivalence << endl;
		out << display_prefix << "detect_binary_learnts_resolution = " << detect_binary_learnts_resolution << endl;
		out << display_prefix << "detect_binary_learnts_bcp = " << detect_binary_learnts_bcp << endl;
		out << display_prefix << "detect_AND_gates = " << detect_AND_gates << endl;
		out << display_prefix << "keep_binary_learnts = " << keep_binary_learnts << endl;
		out << display_prefix << "recover_exterior = " << recover_exterior << endl;
		out << display_prefix << "display_preprocessing_process = " << display_preprocessing_process << endl;
		out << display_prefix << "profile_preprocessing = " << profile_preprocessing << endl;
		/// inprocessor
		out << display_prefix << "var_ordering_heur = " << var_ordering_heur << endl;
		out << display_prefix << "mixed_var_ordering = " << mixed_var_ordering << endl;
		out.setf(std::ios_base::boolalpha);
		out << display_prefix << "phase_selecting = " << phase_selecting << endl;
		out.unsetf(std::ios_base::boolalpha);
		out << display_prefix << "imp_strategy = " << imp_strategy << endl;  // Automatical_Imp_Computing, Partial_Implicit_BCP, Full_Implicit_BCP, SAT_Imp_Computing
		out << display_prefix << "mixed_imp_computing = " << mixed_imp_computing << endl;
		out << display_prefix << "decompose_strategy = " << decompose_strategy << endl;
		out << display_prefix << "display_inprocessing_process = " << display_inprocessing_process << endl;
		out << display_prefix << "profiling_inprocessing = " << profiling_inprocessing << endl;
		/// extensive inprocessor
		out << display_prefix << "max_kdepth = " << max_kdepth << endl;
		out << display_prefix << "kernelizing_step = " << kernelizing_step << endl;
		out << display_prefix << "display_kernelizing_process = " << display_kernelizing_process << endl;
		out << display_prefix << "profiling_ext_inprocessing = " << profiling_ext_inprocessing << endl;
		/// compiler
		out << display_prefix << "max_memory = " << max_memory << " GB" << endl;  // 4 GB
		out << display_prefix << "mem_load_factor = " << mem_load_factor << endl;
		out << display_prefix << "trivial_variable_bound = " << trivial_variable_bound << endl;
		out << display_prefix << "trivial_clause_bound = " << trivial_clause_bound << endl;
		out << display_prefix << "trivial_density_bound = " << trivial_density_bound << endl;
		out << display_prefix << "trivial_length_bound = " << trivial_length_bound << endl;
		out << display_prefix << "treewidth_bound = " << treewidth_bound << endl;
		out << display_prefix << "activate_easy_compiler = " << activate_easy_compiler << endl;
		out << display_prefix << "erase_useless_cacheable_component = " << erase_useless_cacheable_component << endl;
		out << display_prefix << "removing_redundant_nodes_trigger = " << removing_redundant_nodes_trigger << endl;
		out << display_prefix << "display_compiling_process = " << display_compiling_process << endl;
		out << display_prefix << "profile_compiling = " << profile_compiling << endl;
		/// counter
		out << display_prefix << "static_heur = " << static_heur << endl;
		out << display_prefix << "display_counting_process = " << display_counting_process << endl;
		out << display_prefix << "profile_counting = " << profile_counting << endl;
		/// partial kc
		out << display_prefix << "estimate_marginal_probability = " << estimate_marginal_probability << endl;
		out << display_prefix << "adaptive_sampling = " << adaptive_sampling << endl;
		out << display_prefix << "simply_counting_time = " << simply_counting_time << endl;
		out << display_prefix << "sampling_time = " << sampling_time << endl;
		out << display_prefix << "sampling_count = " << sampling_count << endl;
		out << display_prefix << "sample_display_interval = " << sampling_display_interval << endl;
		out << display_prefix << "profile_partial_kc = " << profile_partial_kc << endl;
		/// oracle
		out << display_prefix << "profile_oracle = " << profile_oracle << endl;
		out << display_prefix << "oracle_memory_limit = " << oracle_memory_limit << endl;  // 100M
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
	/// extensive inprocessor
	bool verify_kernelization;
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
		/// extensive inprocessor
		verify_kernelization = false;
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
	double time_tree_decomposition;
	double time_ibcp;
	double time_dynamic_decompose;
	double time_dynamic_decompose_sort;
	void Init_Inprocessor_Single()
	{
		time_tree_decomposition = 0;
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
		Init_Extensive_Inprocessor();
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
		Init_Extensive_Inprocessor();
		Init_Counter_Single();
	}
	/// partial kc
	double time_simply_counting;
	double time_estimate_marginal_probability;
	void Init_Partial_KC_Single()
	{
		Init_Compiler_Single();
		time_simply_counting = 0;
		time_estimate_marginal_probability = 0;
	}
	void Init_Partial_KC()
	{
		Init_Extensive_Inprocessor();
		Init_Partial_KC_Single();
	}
};






}


#endif
