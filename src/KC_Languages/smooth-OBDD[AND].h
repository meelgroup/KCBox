#ifndef _smooth_OBDDC_h_
#define _smooth_OBDDC_h_

#include "OBDD[AND].h"


namespace KCBox {


class Smooth_OBDDC_Manager: public OBDDC_Manager
{
	friend bool Is_Equivalent( Smooth_OBDDC_Manager & manager1, Diagram bddc1, Smooth_OBDDC_Manager & manager2, Diagram bddc2 );
	friend class BDDC_Compiler;
protected:
	vector<unsigned> _aux_varIDs;
public:
	Smooth_OBDDC_Manager( Variable max_var,  dag_size_t node_num = LARGE_HASH_TABLE ): OBDDC_Manager( max_var, node_num ) {}
	Smooth_OBDDC_Manager( const Chain & order, dag_size_t node_num = 100 ): OBDDC_Manager( order, node_num ) {}
	Smooth_OBDDC_Manager( istream & fin ): OBDDC_Manager( fin ) {}
	Smooth_OBDDC_Manager( Smooth_OBDDC_Manager & other ): OBDDC_Manager( other ) {}
protected:
	void Verify_Smoothness( NodeID root );
	void Verify_Smooth_ROBDDC_Finest( NodeID root );
protected:
	void Compute_Var_Sets( NodeID root, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
	void Compute_Vars( NodeID n, Hash_Cluster<Variable> & var_cluster, vector<SetID> & sets );
protected:
	NodeID Add_Node( Rough_BDDC_Node & rnode );
	NodeID Add_Decision_Node( Decision_Node & bnode ) { return OBDDC_Manager::Add_Decision_Node( bnode ); }
	NodeID Add_Decomposition_Node( Rough_BDDC_Node & rnode );
	Diagram Decompose_Infty( OBDD_Manager & bdd_manager, Diagram & bdd );
	Diagram Convert_Down_ROBDD( const Diagram & bddc, OBDD_Manager & bdd_manager );
public:
	NodeID Supplement_Auxiliary_Nodes( NodeID root, const vector<unsigned> & super_vars, const vector<unsigned> & vars );
	NodeID Add_Decision_Node( Decision_Node & dnode, const vector<unsigned> ** var_sets );
	NodeID Add_Decomposition_Node( Rough_BDDC_Node & rnode, const vector<unsigned> ** var_sets );
protected:
	void Smooth_Decision_Node( Decision_Node & dnode, const vector<unsigned> & lvars, const vector<unsigned> & hvars );  // vars of result are stored in _aux_varIDs
protected:
	dag_size_t Push_Auxiliary_Node( unsigned var )
	{
		dag_size_t old_size = _nodes.Size();
		NodeID ch[2] = { NodeID::top, NodeID::top };
		BDDC_Node node( var, ch, 2 );
		dag_size_t pos = Hash_Hit_Node( _nodes, node );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [2];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = _nodes[pos].ch[1] = NodeID::top;
		}
		return pos;
	}
public:
	static void Debug();
};


}


#endif
