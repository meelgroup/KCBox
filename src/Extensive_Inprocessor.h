#ifndef _Extensive_Inprocessor_h_
#define _Extensive_Inprocessor_h_

#include "Template_Library/Basic_Functions.h"
#include "Primitive_Types/Stack_Frame.h"
#include "Component_Types/Unified_Component.h"
#include "Inprocessor.h"


namespace KCBox {


class Extensive_Inprocessor: public Inprocessor
{
protected:
	vector<Stack_Frame> _input_frames;
	Stack_Frame * _call_stack;
	Stack_Frame _swap_frame;
	vector<SetID> _long_clause_ids;
	vector<unsigned> _long_clause_ranks;
	Literal * _many_lits;
	Unified_Component _unified_comp;
	unsigned _current_kdepth;
	unsigned _current_non_trivial_kdepth;
	vector<Literal> * _cached_binary_clauses;  // used for accelerating caching
public:
	Extensive_Inprocessor();
	~Extensive_Inprocessor();
	void Reset();
	void Open_Oracle_Mode( Variable var_bound );
	void Close_Oracle_Mode();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
protected:
	void Get_All_Imp_Component( Component & comp, vector<Model *> & models );
	void Filter_Long_Learnts();
protected:
	void Kernelize_Without_Imp();
	void Store_Active_Clauses_Component( Stack_Frame & frame, Component & comp );
	void Store_Binary_Clauses_Component( Stack_Frame & frame, Component & comp );
	void Load_Binary_Clauses( Stack_Frame & frame );
	void Eliminate_Redundancy_Component( Component & comp );
	void Generate_Long_Watched_Lists_Component( Component & comp );
	bool Replace_Equivalent_Lit_Component( Component & comp );
	bool Detect_Lit_Equivalence_Component( Component & comp );
	bool Detect_Lit_Equivalence_Tarjan_Component( Component & comp );
	void Cluster_Equivalent_Lits_Component( Component & comp );
	bool Detect_Lit_Equivalence_BCP_Component( Component & comp );
	bool Detect_Lit_Equivalence_IBCP_Component( Component & comp );
	void Block_Binary_Clauses_Component( Component & comp );
	void Rename_Clauses_Linear_Ordering_Component( Component & comp );
	void Record_Lit_Equivalency_Component( Component & comp );
	void Update_Kernelized_Component( Component & comp, const vector<unsigned> & vars );
	void Store_Lit_Equivalences_Component( Stack_Frame & frame, Component & comp );
	void Gather_Kernelization_Infor( unsigned level );
protected:
	void Generate_Auxiliary_Lists_Subdivision_Component( Component & comp );
	void Generate_Auxiliary_Lists_Subdivision_Long_Component( Component & comp );
	void Generate_Membership_Lists_Subdivision_Binary_Component( Component & comp );
	void Clear_Auxiliary_Lists_Subdivision_Long_Component( Component & comp );
	void Clear_Membership_Lists_Subdivision();
	void Clear_Membership_Lists_Subdivision_Long();
	void Clear_Membership_Lists_Subdivision_Component( Component & comp );
	void Clear_Membership_Lists_Subdivision_Binary_Component( Component & comp );
protected:
	void Cancel_Kernelization_Without_Imp();
protected:
	void Set_Current_Level_Kernelized( bool flag );
	unsigned Search_Last_Decomposition_Level();
	unsigned Search_Last_Kernelizition_Level();
	bool Is_Level_Kernelization( unsigned level ) { return _call_stack[level].Existed(); }
protected:
	void Store_Cached_Binary_Clauses();
	void Clear_Cached_Binary_Clauses();
	void Recover_Cached_Binary_Clauses();
protected:
	void Verify_Kernelization();
public:
	void Add_Formula( CNF_Formula & cnf, Component & comp, vector<Model *> & models, unsigned pre_fixed_num_vars );  //
protected:
	void Add_Input_Frame( CNF_Formula & cnf, vector<Model *> & models, unsigned pre_fixed_num_vars );
public:
	void Batch_Preprocess();
protected:
	void Load_Frame( Stack_Frame & frame );
	void Load_Lit_Equivalences( Stack_Frame & frame );
	void Store_Frame( Stack_Frame & frame );
	void Store_Binary_Clauses( Stack_Frame & frame );
	void Store_Lit_Equivalences( Stack_Frame & frame );
protected:
	void Generate_Unified_Component( Component & comp );  // complete the information in unified_comp
protected:
	void Verify_Reasons_With_Kernelization();
};


}


#endif  // _Easy_Compiler_h_
