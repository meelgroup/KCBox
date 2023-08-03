#ifndef _BDD_h_
#define _BDD_h_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Template_Library/BigNum.h"
#include "DAG.h"


namespace KCBox {


#define BDD_SYMBOL_TRUE	( unsigned(-1) )
#define BDD_SYMBOL_FALSE	( unsigned(-2) )


struct BDD_Node_Infor
{
	bool visited;
	unsigned link;
	unsigned reserved;
	void * ext; // the memory of ext must be free once after it has been used.
	BDD_Node_Infor(): visited( false ), link( NodeID::undef ), reserved( UNSIGNED_UNDEF ), ext( nullptr ) {}
	void Init()
	{
		visited = false;
		link = NodeID::undef;
		reserved = UNSIGNED_UNDEF;
		ext = nullptr;
	}
	void operator = ( BDD_Node_Infor & other )
	{
		visited = other.visited;
		link = other.link;
		reserved = other.reserved;
		ext = other.ext;
	}
};

struct BDD_Node
{
	Variable var;
	NodeID low;
	NodeID high;
	Node_Infor infor;
	BDD_Node() {}
	BDD_Node( Decision_Node & bnode ): var( bnode.var ), low( bnode.low ), high( bnode.high ) {}
	bool operator == ( BDD_Node & other )
	{
		return ( var == other.var ) + ( low == other.low ) + ( high == other.high ) == 3;
	}
	unsigned Key() const
	{
		return PAIR( PAIR( var, low ), high );
	}
};

typedef NodeID BDD;
//typedef unsigned NodeID;

class OBDD_Manager: public Diagram_Manager, public Linear_Order
{
protected:
	Hash_Table<BDD_Node> _nodes;
protected:
	NodeID * _result_stack;
	unsigned _num_result_stack;
	Binary_Map<NodeID, NodeID, NodeID> _op_table;
public:
	OBDD_Manager( Variable max_var );
	OBDD_Manager( const Chain & var_order );
	OBDD_Manager( istream & fin );
	~OBDD_Manager();
	void Reorder( const Chain & new_order );
	void Display( ostream & out );
	unsigned Add_Node( Decision_Node & bnode ) { assert( bnode.var <= _max_var && bnode.low < _nodes.Size() && bnode.high < _nodes.Size() ); return Push_Node( bnode ); }
	void Verify_ROBDD( BDD bdd );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Add_Fixed_Nodes();
	void Free_Auxiliary_Memory();
	void Clear_Nodes();
	void Verify_Ordered( BDD bdd );
	void Verify_Reduced( BDD bdd );
public: // querying
	unsigned Num_Nodes() const { return _nodes.Size(); }
	const BDD_Node & Node( unsigned i ) { return _nodes[i]; }
	bool Entail_Clause( BDD root, Clause & clause );
	bool Entail_CNF( BDD root, CNF_Formula & cnf );
	BigInt Count_Models( BDD bdd );
	bool Equivalent( BDD left, BDD right );
	EPCCL_Theory * Convert_EPCCL( BDD root );
protected:
    bool Decide_SAT_Under_Assignment( BDD root );
public: // transformation
    BDD Convert( Clause & clause );
    BDD Convert( CNF_Formula & cnf );
	BDD Conjoin( BDD left, BDD right );
	BDD Disjoin( BDD left, BDD right );
	BDD Negate( BDD bdd );

protected:
	bool Decide_Node( unsigned n );
protected: // simple inline functions
	NodeID Push_Node( BDD_Node & node )
	{
		if ( node.low == node.high ) return node.low;
		else return NodeID( _nodes.Hit( node ) );
	}
	NodeID Push_Node( Decision_Node & bnode )
	{
		if ( bnode.low == bnode.high ) return bnode.low;
		BDD_Node node( bnode );
		return NodeID( _nodes.Hit( node ) );
	}
};


}


#endif
