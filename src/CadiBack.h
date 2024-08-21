#ifndef _cadiback_h_
#define _cadiback_h_

#include <vector>
#include "../cadical/src/cadical.hpp"
#include "Solver.h"


namespace KCBox {


class CadiBack: public CaDiCaL::Solver
{
public:
	struct
	{
		bool no_fixed = false;
		bool no_flip = true;
		bool really_flip = false;
		bool no_inprocessing = false;
		bool one_by_one = true;
		bool chunking = false;
		bool models = true;
	} options;
	struct
	{
		size_t backbones = 0;     // Number of backbones found.
		size_t dropped = 0;       // Number of non-backbones found.
		size_t filtered = 0;      // Number of candidates with two models.
		size_t fixed = 0;         // Number of fixed variables.
		struct {
			size_t sat = 0;     // Calls with result SAT to SAT solver.
			size_t unsat = 0;   // Calls with result UNSAT to SAT solver.
			size_t unknown = 0; // Interrupted solver calls.
			size_t total = 0;   // Calls to SAT solver.
		} calls;
		size_t flipped = 0;   // How often 'solver->flip (lit)' succeeded.
		size_t flippable = 0; // How often 'solver->flip (lit)' succeeded.
	} statistics;
protected:
	Variable _max_var;        // The number of variables in the CNF.
	Literal * _backbones;      // The resulting fixed backbone literals.
	bool * _assumed;
	std::vector<Literal> _candidates; // The backbone candidates (if non-zero).
	unsigned _constraint_size; // Literals to constrain.
public:
	CadiBack(): Solver() {}
	int solve();
public:
	void set_options( bool no_fixed, bool no_flip, bool really_flip, bool no_inprocessing, bool one_by_one, bool chunking, bool models );
	void reset_options();
	bool calculate( Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool );  // backbone will be stored in assumptions, and the obtained models will be stored in models
protected:
	void calculate_pre( Decision_Manager & manager );
	int solve( Decision_Manager & manager );
	void add_model( vector<Model *> & models, Model_Pool * model_pool );
	void init_candidates( Decision_Manager & manager, vector<Model *> & models );
	void try_to_flip_remaining( vector<Model *> & models, Model_Pool * model_pool );
	void drop_candidate( unsigned pos );
	bool fix_candidate( unsigned pos );
	void backbone_variable( unsigned pos );
	void filter_candidates();
	bool filter_candidate( unsigned pos );
	void backbone_variables();
	int calculate_one_by_one( Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool );
	void calculate_post( Decision_Manager & manager );
public:
	void calculate( Component & comp, Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool );  // backbone will be stored in assumptions, and the obtained models will be stored in models
protected:
	void calculate_pre( Component & comp, Decision_Manager & manager );
	void add_model( Component & comp, vector<Model *> & models, Model_Pool * model_pool );
	void init_candidates( Component & comp, Decision_Manager & manager, vector<Model *> & models );
	void try_to_flip_remaining( Component & comp, vector<Model *> & models, Model_Pool * model_pool );
	int calculate_one_by_one( Component & comp, Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool );
	void calculate_post( Component & comp, Decision_Manager & manager );
public:
	bool imply( Big_Clause & clause );
};


};


#endif

