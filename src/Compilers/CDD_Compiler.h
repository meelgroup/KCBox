#ifndef _CDD_Compiler_h_
#define _CDD_Compiler_h_

#include "../Extensive_Inprocessor.h"
#include "../KC_Languages/OBDD[AND].h"
#include "../KC_Languages/RCDD.h"
#include "../KC_Languages/RRCDD.h"
#include "../Component_Types/Incremental_Component.h"
#include "../Search_Graph.h"


namespace KCBox {


class CDD_Compiler: public Extensive_Inprocessor
{
protected:
	NodeID * _rsl_stack; // rsl denotes result
	unsigned _num_rsl_stack;  // recording the number of temporary results
	Incremental_Component_Cache<NodeID> _component_cache;
	vector<Literal> _equivalent_lit_pairs;
	Rough_CDD_Node _cdd_rnode;
	Component _incremental_comp;
	double _node_redundancy_factor;
public:
	CDD_Compiler();
	~CDD_Compiler();
	void Reset();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory();
protected:
	bool Create_Init_Level();
	void Component_Cache_Add_Original_Clauses();
protected:
	void Backjump_Decision( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	NodeID Component_Cache_Map( Component & comp );
	void Generate_Incremental_Component( Component & comp );
	void Component_Cache_Connect( Component & comp );
	void Backtrack();  // backtrack one level without discarding results
	void Extend_New_Level();
	void Refactor_Current_Level();
	void Remove_Redundant_Nodes( CDD_Manager & manager );
	bool Cache_Clear_Applicable( CDD_Manager & manager );
	void Component_Cache_Clear();
	void Component_Cache_Reconnect_Components();
	void Backjump_Decomposition( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	void Backtrack_Halfway();  // backtrack one decomposition level when getting a UNSAT
protected:
	void Sort_Clauses_For_Caching();
	void Sort_Long_Clauses_By_IDs();
	void Encode_Long_Clauses();
protected:
	NodeID Search_Root_Node( Search_Graph<NodeID> & graph, NodeID child );
	NodeID Search_Kernelized_Conjunction_Node( Search_Graph<NodeID> & graph, NodeID child );
	NodeID Search_Node_With_Imp( Search_Graph<NodeID> & graph, NodeID child );
	NodeID Search_Decision_Node( Search_Graph<NodeID> & graph, NodeID low, NodeID high );
	NodeID Search_Node_With_Imp( Search_Graph<NodeID> & graph, NodeID * children, unsigned num );
protected:
	void Display_Statistics( unsigned option );
	void Display_Result_Statistics( ostream & out, CDD_Manager & manager, NodeID root );
	void Display_Memory_Status( ostream & out );
	void Display_Result_Stack( ostream & out );
protected:
	bool Is_Memory_Exhausted();
};


}


#endif  // _Compiler_h_
