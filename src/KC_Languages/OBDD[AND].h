#ifndef _BDDC_h_
#define _BDDC_h_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Primitive_Types/CNF_Formula.h"
#include "OBDD.h"


namespace KCBox {


#define BDDC_CHILD_POS_UNDEF (unsigned(-1))
#define BDDC_SYMBOL_TRUE	( unsigned(-1) )
#define BDDC_SYMBOL_FALSE	( unsigned(-2) )
#define BDDC_SYMBOL_CONJOIN	(unsigned(-3))


struct Rough_BDDC_Node
{
	unsigned sym;
	NodeID * ch;
	unsigned ch_size;
	Rough_BDDC_Node( Variable max_var = Variable::start ) { ch = new NodeID [max_var + 1]; }
	~Rough_BDDC_Node() { delete [] ch; }
	void Reset_Max_Var( Variable max_var ) { delete [] ch; ch = new NodeID [max_var + 1]; }
	void Add_Child( NodeID child ) { ch[ch_size++] = child; }
	void Display( ostream & out )
	{
		if ( sym == BDDC_SYMBOL_FALSE ) out << "F 0";
		else if ( sym == BDDC_SYMBOL_TRUE ) out << "T 0";
		else {
			if ( sym == BDDC_SYMBOL_CONJOIN ) out << "C";
			else out << sym;
			for ( unsigned i = 0; i < ch_size; i++ ) {
				out << ' ' << ch[i];
			}
			out << " 0";
		}
	}
};

struct BDDC_Node
{
	unsigned sym;
	NodeID * ch;  /// NOTE: need to call Free() to free the memory outside
	unsigned ch_size;
	Node_Infor infor;
	BDDC_Node() {}
	BDDC_Node( unsigned symbol, NodeID * children, unsigned size ) : sym( symbol ), ch( children ), ch_size( size ) {}
	BDDC_Node( Rough_BDDC_Node & rnode ) : sym( rnode.sym ), ch_size( rnode.ch_size )
	{
		ch = new NodeID [ch_size];
		for ( unsigned i = 0; i < ch_size; i++ ) ch[i] = rnode.ch[i];
	}
	BDDC_Node( Decision_Node & bnode ) : sym( bnode.var ), ch_size( 2 )
	{
		ch = new NodeID [2];
		ch[0] = bnode.low;
		ch[1] = bnode.high;
	}
	void Free() { delete [] ch; }
	bool operator == ( BDDC_Node & other ) // Constant node is applicable
	{
		if ( ( sym != other.sym ) || ( ch_size != other.ch_size ) ) return false;
		unsigned tmp = ch[ch_size - 1];
		ch[ch_size - 1] = NodeID::undef;
		unsigned i = 0;
		while ( ch[i] == other.ch[i] ) i++;
		ch[ch_size - 1] = tmp;
		return ch[i] == other.ch[i];
	}
	Variable Var() { return Variable( sym ); }
	NodeID & Ch( unsigned i ) { return ch[i]; }
	unsigned Ch_Size() { return ch_size; }
	Node_Infor & Infor() { return infor; }
	unsigned Key() const
	{
		unsigned k = PAIR( sym, ch_size );
		for ( unsigned i = 0; i < ch_size; i++ ) k = PAIR( k, ch[i] );
		return k;
	}
	size_t Memory() const { return sizeof(BDDC_Node) + ch_size * sizeof(NodeID); }
	void Sort_Children( QSorter & sorter ) { sorter.Sort( ch, ch_size ); }
	void Sort_Children_Two_Halves( QSorter & sorter, unsigned mid )
	{
		assert( mid <= ch_size );
		sorter.Sort( ch, mid );
		sorter.Sort( ch + mid, ch_size - mid );
	}
	void Display( ostream & out, bool stat = false ) const
	{
		if ( sym == BDDC_SYMBOL_FALSE ) out << "F 0";
		else if ( sym == BDDC_SYMBOL_TRUE ) out << "T 0";
		else {
			if ( sym == BDDC_SYMBOL_CONJOIN ) out << "C";
			else out << sym;
			for ( unsigned i = 0; i < ch_size; i++ ) {
				out << ' ' << ch[i];
			}
			out << " 0";
		}
		if ( stat ) {
			out << " ";
			infor.Display( out );
		}
		out << endl;
	}
};

struct BDDC_Debug_Options
{
	bool verify_Decompose_Infty;
	bool verify_Convert_Down;
	bool verify_Conjoin_One_Zero;
	bool verify_Conjoin_One_Zero_Simple;
	bool verify_Conjoin_One_Zero_Simple_No_Preprocess;
	bool display_Decompose_Infty;
	bool display_Convert_Down;
	bool display_Convert_Down_time;
	bool display_Decide_Node_SAT_Under_Assignment;
	bool display_Condition;
	bool display_Conjoin_One_Zero_Simple;
	bool display_Conjoin_One_Zero;
	bool display_Condition_One_Zero_Under_Assignment;
	bool display_Conjoin_One_Zero_time;
	bool display_Conjoin_One_Zero_Simple_No_Preprocess;
	bool display_Conjoin_One_Zero_Simple_No_Preprocess_time;
	bool display_Conjoin_Zero_Zero_time;
	bool activate_running_time;
	BDDC_Debug_Options()
	{
        verify_Decompose_Infty = true;
        verify_Convert_Down = true;
        verify_Conjoin_One_Zero_Simple = false;
        verify_Conjoin_One_Zero = false;
        verify_Conjoin_One_Zero_Simple_No_Preprocess = false;
        display_Decompose_Infty = false;
        display_Convert_Down = false;
        display_Convert_Down_time = false;
        display_Decide_Node_SAT_Under_Assignment = false;
        display_Condition = false;
        display_Conjoin_One_Zero_Simple = false;
        display_Conjoin_One_Zero = false;
        display_Conjoin_One_Zero_time = false;
        display_Conjoin_One_Zero_Simple_No_Preprocess = false;
        display_Conjoin_One_Zero_Simple_No_Preprocess_time = false;
        display_Condition_One_Zero_Under_Assignment = false;
        display_Conjoin_Zero_Zero_time = false;
        activate_running_time = true;
    }
};

struct BDDC_Running_Time
{
	double Decompose_Infty;
	double Convert_Down;
	double Conjoin_One_Zero_Simple;
	double Conjoin_One_Zero_Simple_Compute_Var;
	double Conjoin_One_Zero_Simple_Assign_Memory;
	double Conjoin_One_Zero_Simple_No_Preprocess;
	double Conjoin_One_Zero;
	double Conjoin_One_Zero_Assign_Memory;
	double Conjoin_One_Zero_Condition;
	double Conjoin_One_Zero_Decompose;
	double Conjoin_One_Zero_Hash_Hit;
	double Conjoin_Zero_Zero;
	double Conjoin_Zero_Zero_No_Preprocess;
	void Init()
	{
		Decompose_Infty = 0;
		Convert_Down = 0;
		Conjoin_One_Zero_Simple_No_Preprocess = 0;
		Conjoin_One_Zero_Simple = 0;
		Conjoin_One_Zero = 0;
		Conjoin_One_Zero_Condition = 0;
		Conjoin_One_Zero_Decompose = 0;
		Conjoin_One_Zero_Hash_Hit = 0;
		Conjoin_Zero_Zero = 0;
		Conjoin_Zero_Zero_No_Preprocess = 0;
	}
};

struct BDDC_Op_Node
{
	unsigned left;
	unsigned right;
	unsigned result;
	bool operator == ( BDDC_Op_Node & other )
	{
		return left == other.left && right == other.right;
	}
	unsigned Key() const
	{
		return PAIR( left, right );
	}
};

struct BDDC_Ternary_Op_Node
{
	unsigned left;
	unsigned right;
	unsigned imp;
	unsigned result;
	bool operator == ( BDDC_Ternary_Op_Node & other )
	{
		return ( left == other.left ) + ( right == other.right ) + ( imp == other.imp ) == 3;
	}
	unsigned Key() const
	{
		return PAIR( PAIR( left, right ), imp );
	}
};

typedef NodeID BDDC;

class OBDDC_Manager: public Diagram_Manager, public Linear_Order
{
	friend bool Is_Equivalent( OBDDC_Manager & manager1, BDDC root1, OBDDC_Manager & manager2, BDDC root2 );
	friend class Compiler;
protected:
	Hash_Table<BDDC_Node> _nodes;
	unsigned _num_fixed_nodes;  // FALSE, TRUE, and literals
protected: //auxiliary memory
	NodeID * _many_nodes;  // stored temporary children
	NodeID ** _node_sets;
	unsigned * _node_set_sizes;
	Rough_BDDC_Node _aux_rnode;
	QSorter _qsorter;
public:
	/* NOTE:
	* mode = 1: it is a BDDC file
	* mode = 3: it is a OBDD file
	* mode = 4: it is a OBDD-L file
	*/
	OBDDC_Manager( Variable max_var,  unsigned node_num = LARGE_HASH_TABLE );
	OBDDC_Manager( const Chain & order, unsigned node_num = 100 ); // Only called by the static generating functions
	OBDDC_Manager( istream & fin, int mode = 1 );
	OBDDC_Manager( OBDDC_Manager & other );
	~OBDDC_Manager();
	void Reorder( const Chain & new_order );
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	OBDDC_Manager * Copy_BDDC_Standard_Order( unsigned root ); /// For each decision node u, the position of the low children of u is less than that of the high children of of u. Furthermore, for any two children v and w of decomposition node u, the position of v is less than that of u if the min_var of v is less than that of u
	const BDDC_Node & Node( unsigned i ) { return _nodes[i]; }
	unsigned Add_Node( Rough_BDDC_Node & rnode );
	unsigned Add_Decision_Node( Decision_Node & bnode ) { return Decompose_Decision( bnode ); }
	unsigned Add_Decomposition_Node( Rough_BDDC_Node & rnode );
	BDDC Decompose_Infty( OBDD_Manager & bdd_manager, unsigned root );
	void Decompose_Infty();
	BDD Convert_Down_ROBDD( BDDC root, OBDD_Manager & bdd_manager );
	void Display( ostream & out );
	void Display_Stat( ostream & out );
	void Display_New_Nodes( ostream & out, unsigned & old_size );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
	void Add_Fixed_Nodes();
	void Verify_OBDDC( unsigned root );
	void Verify_Ordered_Decision( unsigned root );
	void Verify_ROBDDC_Finest( unsigned root );
	void Remove_Redundant_Nodes( vector<BDDC> & kept_nodes );

protected:
	NodeID Finest( Rough_BDDC_Node * p );
	NodeID Finest_Exi( Rough_BDDC_Node * p );
	NodeID Decompose_Decision( Decision_Node & root );
	NodeID Decompose_Decision( BDDC_Node * itr );
	NodeID Extract_Leaf_Left_No_Check( Decision_Node * p );
	NodeID Extract_Leaf_Right_No_Check( Decision_Node * p );
	NodeID Extract_Share_Semi_Check( Decision_Node * p );
	NodeID Extract_Share_Semi_Check_Debug( Decision_Node * p );
	NodeID Extract_Part_Left_No_Check( Decision_Node * p );
	NodeID Extract_Part_Right_No_Check( Decision_Node * p );
	NodeID Decompose_Conjunction( Rough_BDDC_Node & rnode );
	NodeID Decompose_Conjunction( BDDC_Node * itr );
	NodeID Extract_Leaf_Left_No_Check( BDDC_Node * p );
	NodeID Extract_Leaf_Right_No_Check( BDDC_Node * p );
	NodeID Extract_Share_Semi_Check( BDDC_Node * p );
	NodeID Extract_Part_Left_No_Check( BDDC_Node * p );
	NodeID Extract_Part_Right_No_Check( BDDC_Node * p );
	NodeID Add_Child( NodeID parent, NodeID child );
	NodeID Add_Children( NodeID parent, NodeID * children, unsigned num_ch );
	NodeID Remove_Child( NodeID parent, NodeID child );
	NodeID Remove_Child_No_Check( NodeID parent, NodeID child ); // "child" is really a child of "parent"
	NodeID Remove_Child_No_Check_GE_3( NodeID parent, NodeID child ); // "parent" has more than two children
	NodeID Remove_Child_No_Check_Change( NodeID parent, NodeID child ); // called by "Condition_Min_Change"
	NodeID Remove_Child_No_Check_Rough( Rough_BDDC_Node & parent, NodeID child );
	NodeID Remove_Child_No_Check_Rough_Change( Rough_BDDC_Node & parent, NodeID child );
	NodeID Remove_Children( NodeID parent, NodeID * children, unsigned num_ch );
	NodeID Replace_Child( NodeID parent, NodeID child, NodeID new_child );
	NodeID Replace_Child_Nonconstant( NodeID parent, NodeID child, NodeID new_child ); // result is not constant
	NodeID Replace_Child_Internal( NodeID parent, NodeID child, NodeID new_child ); // new_child is internal
	NodeID Replace_Child_Internal_Same( NodeID parent, NodeID child, NodeID new_child ); // the symbols of "child" and "new_child" are same
	NodeID Replace_Child_Internal_Different( NodeID parent, NodeID child, NodeID new_child ); // the symbols of "child" and "new_child" are different
	NodeID Replace_Child_Nonconstant_Change( NodeID parent, NodeID child, NodeID new_child ); // called by "Condition_Min_Change"
	NodeID Replace_Child_Internal_Change( NodeID parent, NodeID child, NodeID new_child );
	NodeID Replace_Child_Internal_Different_Change( NodeID parent, NodeID child, NodeID new_child ); // change infor.min_var and infor.num_var
	NodeID Replace_Child_Rough( Rough_BDDC_Node & parent, NodeID child, NodeID new_child );
	void Compute_Var_Num();
	void Condition_Min_Change( NodeID n, NodeID & low, NodeID & high );
public: // querying
	unsigned Num_Nodes() const { return _nodes.Size(); }
	unsigned Num_Nodes( BDDC root );
	unsigned Num_Edges( BDDC root );
	unsigned Min_Decomposition_Depth( BDDC root );
	size_t Memory();
	bool Entail_Clause( BDDC root, Clause & cl );
	bool Entail_CNF( BDDC root, CNF_Formula * cnf );
	BigInt Count_Models( BDDC root );
protected:
	bool Decide_Node_SAT_Under_Assignment( BDDC root );
	bool Decide_Node_UNSAT_Under_Assignment( BDDC root );
	void Verify_Node_UNSAT_Under_Assignment( BDDC root );
	BigInt Count_Models_Opt( BDDC root );  // #Vars(root) <= num_vars
public: // transforming
	unsigned Condition_Min( BDDC root, bool sign );
protected:
	bool Verify_Equ( BDDC root, OBDDC_Manager & other, BDDC other_root );
	void Verify_Entail_CNF( BDDC root, CNF_Formula & cnf );

protected:
	void Real_Var_Num( unsigned n );

protected:
	bool Var_LT( unsigned u, unsigned v ) { return _var_order.Less_Than( u, v ); }
	bool Var_LE( unsigned u, unsigned v ) { return _var_order.Less_Eq( u, v ); }
	unsigned Push_Node( BDDC_Node node )  // node.ch will be push into _nodes
	{
		unsigned old_size = _nodes.Size();
		unsigned pos = _nodes.Hit( node );
		if ( pos < old_size ) node.Free();
		return pos;
	}
	unsigned Push_New_Node( BDDC_Node node )  /// node does not appear in manager
	{
		unsigned old_size = _nodes.Size();
		unsigned pos = _nodes.Hit( node );
		assert( pos == old_size );  // ToRemove
		return pos;
	}
	unsigned Push_Node( Rough_BDDC_Node & rnode )
	{
		unsigned i, old_size = _nodes.Size();
		BDDC_Node node( rnode.sym, rnode.ch, rnode.ch_size );
		unsigned pos = _nodes.Hit( node );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [rnode.ch_size];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = rnode.ch[0];
			_nodes[pos].ch[1] = rnode.ch[1];
			for ( i = 2; i < rnode.ch_size; i++ ) _nodes[pos].ch[i] = rnode.ch[i];
		}
		return pos;
	}
	unsigned Push_Node( Decision_Node & bnode )
	{
		unsigned old_size = _nodes.Size();
		NodeID ch[2] = { bnode.low, bnode.high };
		BDDC_Node node( bnode.var, ch, 2 );
		unsigned pos = _nodes.Hit( node );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [2];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = bnode.low;
			_nodes[pos].ch[1] = bnode.high;
		}
		return pos;
	}
	void Sort_Children_Over_GLB( NodeID n, NodeID * target )  /// sort by comparing glb of subgraph
	{
		assert( _nodes[n].sym == BDDC_SYMBOL_CONJOIN );
		unsigned i, j;
		for ( i = 0; i < _nodes[n].ch_size; i++ ) {
			target[i] = _nodes[n].ch[i];
		}
		for ( i = 0; i < _nodes[n].ch_size; i++ ) {
			unsigned min = i;
			for ( j = i + 1; j < _nodes[n].ch_size; j++ ) {
				if ( Var_LT( _nodes[target[j]].sym, _nodes[target[min]].sym ) ) min = j;
			}
			unsigned tmp = target[min];
			target[min] = target[i];
			target[i] = tmp;
		}
	}
	void Sort_Children_Over_GLB_Reverse( unsigned n, NodeID * target )  /// sort by comparing glb of subgraph
	{
		assert( _nodes[n].sym == BDDC_SYMBOL_CONJOIN );
		for ( unsigned i = 0; i < _nodes[n].ch_size; i++ ) {
			target[i] = _nodes[n].ch[i];
		}
		for ( unsigned i = 0; i < _nodes[n].ch_size; i++ ) {
			unsigned max = i;
			for ( unsigned j = i + 1; j < _nodes[n].ch_size; j++ ) {
				if ( Var_LT( _nodes[target[max]].sym, _nodes[target[j]].sym ) ) max = j;
			}
			unsigned tmp = target[max];
			target[max] = target[i];
			target[i] = tmp;
		}
	}
	unsigned Search_First_Non_Literal_Position( unsigned n )
	{
		assert( _nodes[n].sym == BDDC_SYMBOL_CONJOIN );
		if ( Is_Fixed( _nodes[n].ch[_nodes[n].ch_size - 1] ) ) return _nodes[n].ch_size;
		if ( !Is_Fixed( _nodes[n].ch[0] ) ) return 0;
		unsigned i;
		for ( i = _nodes[n].ch_size - 2; !Is_Fixed( _nodes[n].ch[i] ); i-- );
		return i + 1;
	}
	unsigned Search_First_Non_Literal_Position( BDDC_Node * node )
	{
		assert( node->sym == BDDC_SYMBOL_CONJOIN );
		if ( Is_Fixed( node->ch[node->ch_size - 1] ) ) return node->ch_size;
		if ( !Is_Fixed( node->ch[0] ) ) return 0;
		unsigned i;
		for ( i = node->ch_size - 2; !Is_Fixed( node->ch[i] ); i-- );
		return i + 1;
	}

protected:
	BDDC_Running_Time running_time;
	Hash_Table<BDDC_Op_Node> op_table;
	static Hash_Table<BDDC_Ternary_Op_Node> ternary_op_table;
	static BDDC_Debug_Options debug_options;
public:
	static void Debug();
	static void Test_Size( CNF_Formula * cnf );
	static void Test_Size_BDDjLu( CNF_Formula * cnf );
	static void Test_Gradual_Sizes( CNF_Formula * cnf );
	static void Test_Gradual_Sizes_Quiet( CNF_Formula * cnf );
	static void Test_Gradual_Sizes_Conjoin( char infile[] );
	static void Test_Conjoin_Time_Total( CNF_Formula * cnf );
	static void Test_Conjoin_Time_Once( CNF_Formula * cnf );
	static void Test_Conjoin_Time_Once_Random( unsigned nv, unsigned nc, unsigned len );
};


}


#endif
