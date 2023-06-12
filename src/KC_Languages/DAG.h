#ifndef _DAG_h_
#define _DAG_h_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Template_Library/BigNum.h"
#include "../Primitive_Types/CNF_Formula.h"
#include "../Primitive_Types/Assignment.h"


namespace KCBox {


struct Node_Infor
{
	bool visited;
	unsigned mark;
	Node_Infor(): visited( false ), mark( UNSIGNED_UNDEF ) {}
	void Init()
	{
		visited = false;
		mark = UNSIGNED_UNDEF;
	}
	void operator = ( Node_Infor & other )
	{
		visited = other.visited;
		mark = other.mark;
	}
	void Display( ostream & out ) const
	{
		out << "[";
		if ( visited ) out << "Visited";
		out << ", ";
		if ( mark != UNSIGNED_UNDEF ) out << "mark = " << mark;
		out << "]";
	}
};

class NodeID: public Identity
{
public:
	NodeID() {}
	NodeID( unsigned id ): Identity( id ) {}
	NodeID( const NodeID &n ): Identity( n._id ) {}
	NodeID & operator = ( NodeID node ) { _id = node._id; return *this; }
	const static NodeID bot;
	const static NodeID top;
	const static NodeID literal( Variable var, bool sign ) { return NodeID( 2 + 2 * var + sign - Literal::start ); }
	const static NodeID literal( Literal lit ) { return NodeID( 2 + lit - Literal::start ); }
	const static NodeID undef;
};

struct Decision_Node
{
	Variable var;
	NodeID low;
	NodeID high;
	Decision_Node() {}
	Decision_Node( unsigned variable, NodeID low_ch, NodeID high_ch ): var( variable ), low( low_ch ), high( high_ch ) {}
};

class Linear_Order
{
protected:
	Chain _var_order; // extra two bits for num_var + 1 and num_var + 2
public:
	Linear_Order() {}
	Linear_Order( const Chain & vorder ): _var_order( vorder ) {}
	bool Var_LT( Variable x, Variable y ) { return _var_order.Less_Than( x, y ); }
	bool Var_LE( Variable x, Variable y ) { return _var_order.Less_Eq( x, y ); }
	bool Lit_LT( Literal lit, Literal lit2 ) { return _var_order.Less_Than( lit.Var(), lit2.Var() ); }
	bool Lit_LE( Literal lit, Literal lit2 ) { return _var_order.Less_Eq( lit.Var(), lit2.Var() ); }
	const Chain & Var_Order() const { return _var_order; }
	void Generate_Lexicographic_Var_Order( Variable max_var )
	{
		for ( unsigned i = Variable::start; i <= max_var; i++ ) {
			_var_order.Append( i );
		}
	}
	void Generate_Var_Order( Chain & vorder ) { _var_order = vorder; }
};

typedef SortedSet<Variable> VarSet;
typedef SortedSet<Literal> LitSet;

class Diagram_Manager: public Assignment
{
protected:
	unsigned _num_fixed_nodes;  // FALSE, TRUE, and literals
protected:
	NodeID * _path;
	unsigned * _path_mark;
	NodeID * _node_stack;
	unsigned * _node_mark_stack;
	vector<NodeID> _visited_nodes;
	bool * _var_seen;
	bool * _lit_seen;
public:
	Diagram_Manager( Variable max_var = Variable::undef );
	virtual ~Diagram_Manager();
	size_t Memory();
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	virtual void Add_Fixed_Nodes() {}
	void Free_Auxiliary_Memory();
public: // querying
    bool Is_Const( NodeID root ) { return root <= 1; }
    bool Is_Internal( NodeID root ) { return root > 1; }
    bool Is_Literal( NodeID root ) { return 2 <= root && root <= 2 * _max_var + 1 + 2 - Literal::start; }
    bool Is_Fixed( NodeID root ) { return root <= 2 * _max_var + 1 + 2 - Literal::start; }
protected:
	Literal Node2Literal( NodeID n )	{ return Literal( n - 2 + Literal::start ); }
};


}


#endif
