#ifndef _Solver_h_
#define _Solver_h_

#include "Template_Library/Basic_Functions.h"
#include "Template_Library/Basic_Structures.h"
#include "Template_Library/Time_Memory.h"
#include "Parameters.h"
#include "Primitive_Types/CNF_Formula.h"
#include "Primitive_Types/Assignment.h"
#include "minisatInterface.h"
#include "Component_Types/Component.h"


namespace KCBox {


class Reason
{
protected:
	unsigned _val;
public:
	Reason() {}
	Reason( Literal lit )  { _val = unsigned(lit) << 1; }
	Reason( unsigned val, bool type )  { _val = ( val << 1 ) + type; }
	Literal Lit_Value() const { return Literal( _val >> 1 ); }
	unsigned Clause_Value() const { return _val >> 1; }
	bool Is_Lit_Reason() const { return !(_val & 0x01); }
	bool Is_Clause_Reason() const { return _val & 0x01; }
	bool operator == (const Reason &other) const { return _val == other._val; }
	bool operator != (const Reason &other) const { return _val != other._val; }
public:
	const static Reason mismatched;
	const static Reason unknown;
	const static Reason undef;
};

class Decision_Manager: public Assignment
{
	friend class CadiBack;
protected:
	unsigned * _var_stamps;  // decision level of variable
	Reason * _reasons;  // decision reason of variable
	Literal * _dec_stack;
	unsigned _num_dec_stack;
	unsigned * _dec_offsets;
	unsigned _num_levels;  // each level includes decision literals (in _dec_stack) and components (in comp_stack)
	unsigned _base_dec_level;
protected:
	Decision_Manager() {}
	~Decision_Manager() { if ( _max_var != Variable::undef ) Free_Auxiliary_Memory(); }
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when mv < max_var
	{
		if ( _max_var == max_var ) return;
		if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
		Assignment::Allocate_and_Init_Auxiliary_Memory( max_var );
		_var_stamps = new unsigned [max_var + 1];
		_reasons = new Reason [max_var + 1];
		_dec_stack = new Literal [NumVars( max_var )];
		_dec_offsets = new unsigned [NumVars( max_var ) + 2];  // for counter, the first level storing implied literals could be empty, and the last level is preserved for _num_dec_stack
		/// init
		_num_dec_stack = 0;
		_num_levels = 0;
	}
	void Free_Auxiliary_Memory()
	{
		delete [] _dec_stack;
		delete [] _var_stamps;
		delete [] _dec_offsets;
		delete [] _reasons;
	}
	void Reset()
	{
		for ( unsigned  i = 0; i < _num_dec_stack; i++ ) {
			Un_Assign( _dec_stack[i].Var() );
		}
		_num_levels = _num_dec_stack = 0;
	}
	void operator = ( Decision_Manager & another )
	{
		Allocate_and_Init_Auxiliary_Memory( another._max_var );
		while ( _num_dec_stack < another._num_dec_stack ) {
			Literal lit = another._dec_stack[_num_dec_stack];
			Assign( lit, _reasons[lit.Var()] );
		}
		for ( ; _num_levels < another._num_levels; _num_levels++ ) {
			_dec_offsets[_num_levels] = another._dec_offsets[_num_levels];
		}
		_base_dec_level = another._base_dec_level;
	}
	void Assign( Variable var, bool val, Reason reason )
	{
		assert( !Var_Decided( var ) );
		_dec_stack[_num_dec_stack++] = Literal( var, val );
		_assignment[var] = val;
		_var_stamps[var] = _num_levels - 1;
		_reasons[var] = reason;
	}
	void Assign( Literal lit, Reason reason = Reason::undef )
	{
		ASSERT( !Var_Decided( lit.Var() ) );
		_dec_stack[_num_dec_stack++] = lit;
		_assignment[lit.Var()] = lit.Sign();
		_var_stamps[lit.Var()] = _num_levels - 1;
		_reasons[lit.Var()] = reason;
	}
	void Un_Assign( Variable var ) { _assignment[var] = lbool::unknown; }
	void Extend_New_Level() { _dec_offsets[_num_levels++] = _num_dec_stack; }
	void Backtrack()
	{
		_num_levels--;
		while ( _num_dec_stack > _dec_offsets[_num_levels] ) {
			Un_Assign( _dec_stack[--_num_dec_stack].Var() );
		}
	}
	void Backjump( unsigned num_kept_levels )
	{
		_num_levels = num_kept_levels;
		while ( _num_dec_stack > _dec_offsets[_num_levels] ) {
			Un_Assign( _dec_stack[--_num_dec_stack].Var() );
		}
	}
	Literal Current_Decision() const { return _dec_stack[_dec_offsets[_num_levels - 1]]; }
	unsigned Num_Current_Imps() const { return _num_dec_stack - _dec_offsets[_num_levels - 1] - 1; }
	unsigned Num_Imps_On_Level( unsigned level ) const
	{
		_dec_offsets[_num_levels] = _num_dec_stack;
		return _dec_offsets[level + 1] - _dec_offsets[level] - 1;
	}
};

class Solver: public Decision_Manager
{
protected:
	bool _no_instance;
	vector<Literal> _unary_clauses;
	vector<Literal> * _binary_clauses;   /// NOTE: lit1 \or lit2 will be push into binary_clauses[lit1] and binary_clauses[lit2]
	unsigned * _old_num_binary_clauses;
	vector<Clause> _long_clauses;
	unsigned _old_num_long_clauses;  // original long clauses
	vector<unsigned> * _long_watched_lists;
	vector<unsigned> _independent_support;
protected:
	bool * _var_seen;  // var_seen[var] is true means that variable var appears
	bool * _lit_seen;  // lit_seen[lit] is true means that literal lit appears
	vector<uint8_t> _clause_status;  // 0: nothing happens
	vector<unsigned> _clause_stack;  // used to store the IDs of the seen clauses
	double * _heur_decaying_sum;  // used for VSIDS and VSADS
	Literal * _heur_sorted_lits;  // the lits in the array are sorted by heur_decaying_sum
	Literal _heur_lit_sentinel;  // the sentinel in heur_sorted_lits
	Heap<Literal, double> _heur_lits_heap;
	unsigned * _var_rank;  // used for conflict learning, and dynamic decomposition
	Big_Clause _big_clause;  // only used in a single function, cannot used for transmitting parameters
	Big_Clause _big_learnt;  // only used in learning conflict
	Model_Pool * _model_pool;  // each model pool should be recreate for each instance
	Minisat::Extra_Output _minisat_extra_output;
	QSorter _qsorter;
public:
	Solver();
	~Solver();
	void Open_Oracle_Mode( Variable var_bound );
	void Close_Oracle_Mode();
	bool Is_Oracle_Mode() const { return running_options.variable_bound != Variable::undef; }
	void Reset();   /// this function should be called after calling Preprocess()
	void operator = ( Solver & another );
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
public:
	bool Solve( CNF_Formula & cnf, vector<Model *> & models );  /// NOTE: <models> is used to gather the models generated in the process, and the initial elements MUST be models of cnf and be allocated by model_pool
protected:
	bool Load_Instance( CNF_Formula & cnf );  // cnf will be changed
	bool Simplify_Original_Clauses_By_Unary( CNF_Formula & cnf );  // simplify clauses in cnf
	void Add_Binary_Clause_Naive( Literal lit1, Literal lit2 );
	bool Large_Scale_Problem() { return _max_var >= 10000; }
	bool Hyperscale_Problem() { return _max_var >= 120000; }  // NOTE: cannot record models
	void Gather_Infor_For_SAT();
	void Generate_Long_Watched_Lists();
	void Generate_Long_Watched_Lists_No_Clear();
	void Init_Heur_Decaying_Sum();
	bool Solve( vector<Model *> & models );
	bool Solve_External( vector<Model *> & models );
	void Prepare_Ext_Clauses( vector<vector<int>> & clauses );
protected:
	unsigned Search_Solution( unsigned conf_limit );  /// 0: UNSAT; 1: SAT; 2: unknown; 3: new implied literal
	unsigned Restart_Bound();
	Literal Branch();
	Reason BCP( unsigned start );
	void Backjump( unsigned num_kept_levels );
	void Un_BCP( unsigned start );
	unsigned Analyze_Conflict( Reason confl );
	Reason Add_Learnt_Sort();  // return reason, sort heur_lits according to heur_decaying_sum
	void Update_Heur_Decaying_Sum();
	void Update_Heur_Decaying_Sum_Sorted_List();
	void Update_Heur_Decaying_Sum_Heap();
	void Bump_Heur_Lit( Literal lit );
	void Rescale_Heur_Decaying_Sum();
	void Add_Model( vector<int8_t> & minisat_model, vector<Model *> & models );
	void Add_Model( vector<Model *> & models );
protected:
	Reason Search_Solution_Component( Component & comp, unsigned conf_limit );
	unsigned Restart_Bound_Component( Component & comp );
	Reason Add_Learnt_Sort_Component( Component & comp );
	void Update_Heur_Decaying_Sum_Component( Component & comp );
	void Update_Heur_Decaying_Sum_Sorted_List_Component( Component & comp );
	void Update_Heur_Decaying_Sum_Heap_Component( Component & comp );
	Literal Branch_Component( Component & comp );
	void Filter_Long_Learnts_During_Solving( unsigned old_num_levels, unsigned old_size );
	bool Two_Unassigned_Literals( Clause & clause );
	unsigned Num_Unassigned_Literals( Clause & clause );
protected:
	Reason Assign_Late( unsigned level, Literal lit, Reason reason );
protected:
	unsigned Num_Clauses();
	unsigned Old_Num_Clauses();
	unsigned Old_Num_Binary_Clauses();
	unsigned Num_Learnts();
	unsigned Num_Binary_Learnts();
	void Verify_Satisfiability( CNF_Formula & cnf, bool result );
	void Verify_Long_Learnt( unsigned pos );
	void Verify_Learnt( Big_Clause & learnt );
	void Verify_Learnts( CNF_Formula & cnf );
	bool Imply_Clause_CNF_No_Learnt( CNF_Formula & cnf, Clause & clause );
	void Verify_Imply_Clause( Clause & clause );
	void Load_Original_Instance( CNF_Formula & cnf );
	void Verify_Model( Model * model );
	void Verify_Model( CNF_Formula & cnf );
	void Verify_Model( Model * model, CNF_Formula & cnf );
	void Verify_Binary_Clauses();
	void Verify_Current_Imps();
	void Verify_Reasons();
	void Display_Statistics( ostream & out );
	void Display_Clauses( ostream & out, bool all = false );
	void Display_Clauses_No_Learnt( ostream & fout );  // when all == true, learnts are all displayed
	void Display_Long_Clauses( ostream & fout, bool all = false );  // when all == true, learnts are all displayed
	void Display_Long_Clauses_No_Learnt( ostream & fout );  // when all == true, learnts are all displayed
	void Display_Binary_Learnts( ostream & out );
	void Display_Watched_List_Naive( ostream & out );  // without adjustment
	void Display_Watched_List( ostream & out );
	void Display_SAT_Heuristic_Value( ostream & out );
	void Display_Decision_Stack( ostream & out, unsigned base_dec_level );
	void Display_Decision_Path( ostream & out );
	void Display_Conflict( Reason confl, ostream & out );
	void Display_Models( vector<Model *> & source, ostream & out );
	void Display_Clauses_For_Verifying_Imp( ostream & out, unsigned old_num_d_stack, unsigned new_num_d_stack );
public:
	bool Solve( unsigned num_vars, vector<Clause> & clauses );  /// clauses will be clear
protected:
	bool Load_Instance( vector<Clause> & clauses );  // cnf will be changed
	bool Simplify_Original_Clauses_By_Unary( vector<Clause> & clauses );
public:
	bool Solve( vector<vector<int>> & eclauses );
public:
	size_t Memory();  /// not the exact memory (omit some auxiliary memory)
	void Free_Models( vector<Model *> & models );  /// NOTE: free the models EXACTLY output by calling Solve() or Preprocess()
//-------------------------------------------------------------
public:
	Statistics statistics;
	Running_Options running_options;
	Debug_Options debug_options;
public:
	static void Debug()
	{
		Solver solver;
		solver.debug_options.verify_learnts = true;
		vector<Model *> models;
		if ( false ) {
			ifstream fin( "instances/C202_FS.cnf" );
			CNF_Formula cnf( fin );
			solver.Solve( cnf, models );
			solver.Free_Models( models );
			solver.Reset();
		}
		else {
			Random_Generator rand_gen;
			for ( unsigned i = 6; i < 10000; i++ ) {
				rand_gen.Reset( i );
				cout << "========== " << i << " ==========" << endl;
				unsigned nv = 30, nc = 100;
				CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
				cnf.Sort_Clauses();
//  			cout << cnf;
//				ofstream fout( "debug.cnf" );
//				fout << cnf;
//				fout.close();
				solver.Solve( cnf, models );
				solver.Free_Models( models );
//				solver.Display_Processed_Clauses( cout );
				solver.Reset();
//				system( "./pause" );
			}
		}
	}
	static void Test( char infile[], bool quiet )
	{
		ifstream cnf_fin;
		cnf_fin.open( infile );
		CNF_Formula cnf( cnf_fin );
		cnf_fin.close();
		Solver solver;
		solver.running_options.display_solving_process = !quiet;
		vector<Model *> models;
		solver.Solve( cnf, models );
		solver.Reset();
	}
};


}


#endif
