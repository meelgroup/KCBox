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
	dag_size_t link;
	void * ext; // the memory of ext must be free once after it has been used.
	BDD_Node_Infor(): visited( false ), link( NodeID::undef ), ext( nullptr ) {}
	void Init()
	{
		visited = false;
		link = NodeID::undef;
		ext = nullptr;
	}
	BDD_Node_Infor & operator = ( const BDD_Node_Infor & other )
	{
		visited = other.visited;
		link = other.link;
		ext = other.ext;
		return *this;
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
	uint64_t Key() const
	{
		return PAIR( PAIR( var, low ), high );
	}
	size_t Memory() const { return sizeof(BDD_Node); }
	NodeID Ch( bool b ) { return b == false ? low : high; }
	void Display( ostream & out, bool stat = false ) const
	{
		if ( var == BDD_SYMBOL_FALSE ) out << "F";
		else if ( var == BDD_SYMBOL_TRUE ) out << "T";
		else out << var << ' ' << low << ' ' << high;
		if ( stat ) {
			out << " ";
			infor.Display( out );
		}
		out << endl;
	}
};


class OBDD_Manager: public Diagram_Manager, public Linear_Order
{
protected:
	Large_Hash_Table<BDD_Node> _nodes;
protected:
	NodeID * _result_stack;
	unsigned _num_result_stack;
	size_t _hash_memory;
	Binary_Map<NodeID, NodeID, NodeID> _op_table;
public:
	OBDD_Manager( Variable max_var );
	OBDD_Manager( const Chain & var_order );
	OBDD_Manager( istream & fin );
	~OBDD_Manager();
	void Reorder( const Chain & new_order );
	void Display( ostream & out );
	void Display_dot( ostream & out );
	void Display_OBDD_dot( ostream & out, Diagram & bdd );
	NodeID Add_Node( Decision_Node & bnode ) { assert( bnode.var <= _max_var && bnode.low < _nodes.Size() && bnode.high < _nodes.Size() ); return Push_Node( bnode ); }
	NodeID Add_Node( Variable x, NodeID l, NodeID h ) { Decision_Node dnode( x, l, h );  return Add_Node( dnode ); }
	Diagram Generate_OBDD( NodeID root ) { assert( root < _nodes.Size() );  return Generate_Diagram( root ); }
	void Verify_ROBDD( Diagram & bdd );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Add_Fixed_Nodes();
	void Free_Auxiliary_Memory();
	void Verify_Ordered( NodeID root );
	void Verify_Reduced( NodeID root );
public: // transformation
	void Clear_Nodes() { _nodes.Resize( _num_fixed_nodes ); }
	void Shrink_Nodes() { _nodes.Shrink_To_Fit(); _hash_memory = _nodes.Memory(); }
	void Swap_Nodes( OBDD_Manager & other ) { _nodes.Swap( other._nodes); }
	void Remove_Redundant_Nodes();
	void Remove_Redundant_Nodes( vector<NodeID> & kept_nodes );
public: // querying
	dag_size_t Num_Nodes() const { return _nodes.Size(); }
	dag_size_t Num_Nodes( const Diagram & bdd );
	dag_size_t Num_Edges( const Diagram & bdd );
	const BDD_Node & Node( NodeID i ) { return _nodes[i]; }
	bool Entail_Clause( const Diagram & bdd, Clause & clause );
	bool Entail_CNF( const Diagram & bdd, CNF_Formula & cnf );
	bool Decide_SAT( const Diagram & bdd, const vector<Literal> & assignment );
	bool Decide_Valid_With_Condition( const Diagram & bdd, const vector<Literal> & assignment );
	BigInt Count_Models( const Diagram & bdd );
	BigFloat Count_Models( const Diagram & bdd, const vector<double> & weights );  // NOTE: weights[lit] + weights[~lit] == 1
	BigInt Count_Models( const Diagram & bdd, const vector<Literal> & assignment );
	BigInt Count_Models_With_Condition( const Diagram & bdd, const vector<Literal> & term );
	BigFloat Count_Models_With_Condition( const Diagram & bdd, const vector<double> & weights, const vector<Literal> & term );
	void Mark_Models( const Diagram & bdd, vector<BigFloat> & results );
	void Probabilistic_Model( const Diagram & bdd, vector<float> & prob_values );
	void Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples );
	void Mark_Models( Diagram & bdd, const vector<double> & weights, vector<BigFloat> & results );
	void Probabilistic_Model( Diagram & bdd, const vector<double> & weights, vector<double> & prob_values );
	void Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, const vector<double> & weights, vector<vector<bool>> & samples );
	void Uniformly_Sample( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples, const vector<Literal> & assignment );
	void Uniformly_Sample_With_Condition( Random_Generator & rand_gen, Diagram & bdd, vector<vector<bool>> & samples, const vector<Literal> & term );
	void Uniformly_Sample_With_Condition( Random_Generator & rand_gen, Diagram & bdd, const vector<double> & weights, vector<vector<bool>> & samples, const vector<Literal> & term );
	EPCCL_Theory * Convert_EPCCL( const Diagram & bdd );
protected:
	bool Decide_SAT_Under_Assignment( NodeID root );
	bool Decide_Valid_Under_Assignment( NodeID root );
	BigInt Count_Models_Under_Assignment( NodeID root, unsigned assignment_size );
	void Mark_Models_Under_Assignment( NodeID root, const vector<double> & weights, vector<BigFloat> & results );
	void Uniformly_Sample( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & prob_values );
	void Mark_Models_Under_Assignment( NodeID root, vector<BigFloat> & results );
	void Uniformly_Sample_Under_Assignment( Random_Generator & rand_gen, NodeID root, vector<bool> & sample, vector<BigFloat> & prob_values );
public: // binary queries
	bool Entail( const Diagram & left, const Diagram & right );
public: // transformation
	Diagram Convert( Clause & clause );
	Diagram Convert( CNF_Formula & cnf );
	Diagram Conjoin( const Diagram & left, const Diagram & right );
	Diagram Disjoin( const Diagram & left, const Diagram & right );
	Diagram Negate( const Diagram & bdd );

protected:
	bool Decide_Node( NodeID n );
protected: // simple inline functions
	bool Contain( const Diagram & bdd ) { return bdd.Root() < _nodes.Size() && Diagram_Manager::Contain( bdd ); }
	NodeID Push_Node( BDD_Node & node )
	{
		if ( node.low == node.high ) return node.low;
		else return Hash_Hit_Node( _nodes, node );
	}
	NodeID Push_Node( Decision_Node & bnode )
	{
		if ( bnode.low == bnode.high ) return bnode.low;
		BDD_Node node( bnode );
		return Hash_Hit_Node( _nodes, node );
	}
public:
	static void Debug()
	{
		Random_Generator rand_gen;
		rand_gen.Reset( 20 );
		unsigned nv = 20;
		CNF_Formula cnf( rand_gen, nv, 50, 3, 3 );
		cout << cnf;
//		system( "./pause" );
		Chain chain;
		for ( unsigned i = nv; i > Variable::start; i-- ) {
			chain.Append( i );
		}
		chain.Append( Variable::start );
		OBDD_Manager bdd_manager( chain );
		Diagram bdd = bdd_manager.Convert( cnf[0] );
		bdd_manager.Display( cout );
		Diagram part;
		for ( unsigned i = 1; i < cnf.Num_Clauses() - 1; i++ ) {
			part = bdd_manager.Convert( cnf[i] );
			bdd = bdd_manager.Conjoin( bdd, part );
		}
		bdd_manager.Display( cout );
		cout << "== 1 ==" << endl;
		Diagram last = bdd_manager.Convert( cnf.Last_Clause() );
		bdd_manager.Display( cout );
		cout << "== 2 ==" << endl;
		cerr << bdd.Root() << " and " << last.Root() << endl;
		Diagram bdd2 = bdd_manager.Conjoin( bdd, last );
		bdd_manager.Display( cout );
		assert( bdd_manager.Entail( bdd2, bdd ) );
	}
};


}


#endif
