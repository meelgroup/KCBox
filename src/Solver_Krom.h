/*
* This header file are used to recognize some literals that are not implied by a cnf formula
*/
#ifndef _Solver_Krom_h_
#define _Solver_Krom_h_

#include "Template_Library/Basic_Functions.h"
#include "Primitive_Types/Assignment.h"
#include "Component_Types/Component.h"


namespace KCBox {


class Solver_Krom: public Assignment
{
    friend class Preprocessor;
	friend class Inprocessor;
protected:
	vector<Literal> * _binary_clauses;   // NOTE: used in Krom, and lit1 \or lit2 will be pushed into binary_clauses[lit1] and binary_clauses[lit2]
	unsigned * _original_num_binary_clauses;  // NOTE: the binary clauses exceeding to old_num_binary_clauses are from long_clauses
	bool * _model_seen;  // model_seen[lit] is true means that some model satisfies lit
	Literal * _dec_stack;
	unsigned _num_dec_stack;
	bool * ext_model_seen;  // external, true mean existing model
	Model_Pool * ext_model_pool;  // external
protected:
    Solver_Krom( Variable max_var, bool * seen, Model_Pool * pool );
    ~Solver_Krom();
	void Recognize_Non_Implied_Literals( unsigned mv );
	void Recognize_Non_Implied_Literals( Component & comp, Model & seed_model, vector<Model *> & new_models );
	void Reset();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
	size_t Memory();
	void Assign_Original_Binary_Clauses( Literal lit );
    void Add_Binary_Clause_Naive( Literal lit1, Literal lit2 );
	void Add_Binary_Clause_From_Long( Big_Clause & cl, Model & seed_model );  // 2CNF
	void Add_Binary_Clause( Literal lit1, Literal lit2 );
	void Mark_Non_Imp_Krom( Model & seed_model, vector<Model *> & new_models );
	Literal Pick_Imp( Variable & i );
	void Assign( Literal lit );
	bool BCP_Krom( unsigned start );
	void Un_BCP( unsigned start );
	void Add_Binary_Clause_After_Blocking( Literal lit1, Literal lit2 );  /// NOTE: after Block_Clauses, the binary clauses from long clauses are not same as the original binary clauses
	void Mark_Non_Imp_Krom_Without_Reset( Component & comp, Model & seed_model, vector<Model *> & new_models );  // not reset assignment and binary_clauses
	Literal Pick_Imp( vector<unsigned>::const_iterator & itr );
protected:
	void Verify_Model_Krom( Model & model );
	void Display_Non_Implied_Literals( ostream & fout );
	void Display_Binary_Clauses( ostream & fout );
    void Display_Decision_Stack( ostream & fout );
};


}


#endif
