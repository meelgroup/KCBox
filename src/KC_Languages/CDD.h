#ifndef _CDD_h_
#define _CDD_h_

#include "OBDD[AND].h"
#include "../Primitive_Types/Lit_Equivalency.h"


namespace KCBox {


#define CDD_SYMBOL_TRUE	            (unsigned(-1))
#define CDD_SYMBOL_FALSE	        (unsigned(-2))
#define CDD_SYMBOL_CONJOIN          (unsigned(-3))
#define CDD_SYMBOL_DECOMPOSE    	(unsigned(-4))
#define CDD_SYMBOL_KERNELIZE		(unsigned(-5))
#define CDD_SYMBOL_EQU              (unsigned(-6))


struct Rough_CDD_Node
{
	unsigned sym;
	NodeID * ch;
	unsigned ch_size;
	Rough_CDD_Node( Variable max_var = Variable::undef ) { ch = new NodeID [max_var + 1]; }
	~Rough_CDD_Node() { delete [] ch; }
	Variable Var() const { return Variable( sym ); }
	void Reset_Max_Var( Variable max_var ) { delete [] ch; ch = new NodeID [max_var + 1]; }
	void Add_Child( NodeID child ) { ch[ch_size++] = child; }
	void Add_Children( NodeID * children, unsigned size ){ for ( unsigned i = 0; i < size; i++ ) ch[ch_size++] = children[i]; }
	NodeID & Last_Child() { return ch[ch_size - 1]; }
	void Display( ostream & out )
	{
		if ( sym == CDD_SYMBOL_FALSE ) out << "F 0";
		else if ( sym == BDDC_SYMBOL_TRUE ) out << "T 0";
		else {
			if ( sym == CDD_SYMBOL_DECOMPOSE ) out << "D";
			else if ( sym == CDD_SYMBOL_KERNELIZE ) out << "K";
			else out << sym;
			for ( unsigned i = 0; i < ch_size; i++ ) {
				out << ' ' << ch[i];
			}
			out << " 0";
		}
	}
};

struct CDD_Node
{
	unsigned sym;
	NodeID * ch;  /// NOTE: need to call Free() to free the memory outside
	unsigned ch_size;
	Node_Infor infor;
	CDD_Node() {}
	CDD_Node( unsigned symbol, NodeID * children, unsigned size ) : sym( symbol ), ch( children ), ch_size( size ) {}
	CDD_Node( Rough_CDD_Node & rnode ) : sym( rnode.sym ), ch_size( rnode.ch_size )
	{
		ch = new NodeID [ch_size];
		for ( unsigned i = 0; i < ch_size; i++ ) ch[i] = rnode.ch[i];
	}
	CDD_Node( Decision_Node & bnode ) : sym( bnode.var ), ch_size( 2 )
	{
		ch = new NodeID [2];
		ch[0] = bnode.low;
		ch[1] = bnode.high;
	}
	CDD_Node Copy() const  /// NOTE: cannot use copying construct function because the default one is used in hash table
	{
		NodeID * children = new NodeID [ch_size];
		for ( unsigned i = 0; i < ch_size; i++ ) children[i] = ch[i];
		return CDD_Node( sym, children, ch_size );
	}
	void Free() { delete [] ch; }
	Variable Var() const { return Variable( sym ); }
	bool operator == ( CDD_Node & other ) // Constant node is applicable
	{
		if ( ( sym != other.sym ) || ( ch_size != other.ch_size ) ) return false;
		unsigned tmp = ch[ch_size - 1];
		ch[ch_size - 1] = NodeID::undef;
		unsigned i = 0;
		while ( ch[i] == other.ch[i] ) i++;
		ch[ch_size - 1] = tmp;
		return ch[i] == other.ch[i];
	}
	unsigned & Sym() { return sym; }
	NodeID & Ch( unsigned i ) { return ch[i]; }
	unsigned Ch_Size() { return ch_size; }
	Node_Infor & Infor() { return infor; }
	unsigned Key() const
	{
		unsigned k = PAIR( sym, ch_size );
		k = PAIR( PAIR( k, ch[0] ), ch[1] );
		for ( unsigned i = 2; i < ch_size; i++ ) k = PAIR( k, ch[i] );
		return k;
	}
	size_t Memory() const { return sizeof(CDD_Node) + ch_size * sizeof(NodeID); }
	unsigned Search_Child( NodeID child )
	{
		unsigned pos = Binary_Search( ch, 0, ch_size, child );
		if ( ch[pos] == child ) return pos;
		else return UNSIGNED_UNDEF;
	}
	void Sort_Children( QSorter & sorter ) { sorter.Sort( ch, ch_size ); }
	void Sort_Children_Two_Halves( QSorter & sorter, unsigned mid )
	{
		assert( mid <= ch_size );
		sorter.Sort( ch, mid );
		sorter.Sort( ch + mid, ch_size - mid );
	}
	void Display( ostream & out, bool stat = false ) const
	{
		if ( sym == CDD_SYMBOL_FALSE ) out << "F 0";
		else if ( sym == CDD_SYMBOL_TRUE ) out << "T 0";
		else {
			if ( sym == CDD_SYMBOL_DECOMPOSE ) out << "D";
			else if ( sym == CDD_SYMBOL_KERNELIZE ) out << "K";
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

struct Simple_CDD_Node  // used to copy key infor in CDD_Node when cannot use CDD_Node & because of _nodes reallocation
{
	unsigned sym;
	NodeID * ch;  /// NOTE: need to call Free() to free the memory outside
	unsigned ch_size;
	Simple_CDD_Node( CDD_Node & node ) : sym( node.sym ), ch( node.ch ), ch_size( node.ch_size ) {}
	Simple_CDD_Node( unsigned symbol, NodeID * children, unsigned size ) : sym( symbol ), ch( children ), ch_size( size ) {}
	Variable Var() const { return Variable( sym ); }
	unsigned Search_Child( NodeID child )
	{
		unsigned pos = Binary_Search( ch, 0, ch_size, child );
		if ( ch[pos] == child ) return pos;
		else return UNSIGNED_UNDEF;
	}
};

typedef NodeID CDD;
typedef SortedSet<Variable> VarSet;
typedef SortedSet<Literal> LitSet;

class CDD_Manager: public Diagram_Manager
{
protected:
	Large_Hash_Table<CDD_Node> _nodes;
protected:  // auxiliary memory
	NodeID * _result_stack;
	unsigned _num_result_stack;
	QSorter _qsorter;
	size_t _hash_memory;
public:
	CDD_Manager( Variable max_var, unsigned estimated_node_num = LARGE_HASH_TABLE );
	~CDD_Manager();
	void Rename( unsigned map[] );
	void Abandon_Rename( unsigned map[] );
	void Enlarge_Max_Var( Variable max_var );
	size_t Hash_Memory() const { return _hash_memory; }
	void Display( ostream & out );
	void Display_Nodes( ostream & out );
	void Display_Stat( ostream & out );
	void Display_Nodes_Stat( ostream & out );
	void Display_New_Nodes( ostream & out, unsigned & old_size );
	void Display_Nodes( ostream & out, NodeID * nodes, unsigned size );
	void Display_CDD( ostream & out, CDD root );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Add_Fixed_Nodes();
	void Compute_Vars( NodeID n );
	void Free_Auxiliary_Memory();
public: // querying
	unsigned Num_Nodes() const { return _nodes.Size(); }
	unsigned Min_Decomposition_Depth( CDD root );
public: // querying
	const CDD_Node & Node( NodeID n ) { return _nodes[n]; }
	unsigned Num_Nodes( CDD root );
	unsigned Num_Edges( CDD root );
public: // transformation
	void Shrink_Nodes() { _nodes.Shrink_To_Fit(); _hash_memory = _nodes.Memory(); }
	void Swap_Nodes( CDD_Manager & other ) { _nodes.Swap( other._nodes); }
	void Remove_Redundant_Nodes( CDD & kept_root );
	void Remove_Redundant_Nodes( vector<CDD> & kept_nodes );
protected:  // basic functions
	unsigned & Node_Mark( NodeID n ) { return _nodes[n].infor.mark; }
	NodeID Push_Node( CDD_Node & node )  // node.ch will be push into _nodes
	{
		unsigned old_size = _nodes.Size();
		unsigned pos = _nodes.Hit( node, _hash_memory );
		if ( pos < old_size ) node.Free();
		return pos;
	}
	NodeID Push_New_Node( CDD_Node & node )  /// node does not appear in _nodes
	{
		unsigned old_size = _nodes.Size();
		unsigned pos = _nodes.Hit( node, _hash_memory );
		ASSERT( pos == old_size );  // ToRemove
		return pos;
	}
	NodeID Push_Node( Rough_CDD_Node & rnode )
	{
		unsigned i, old_size = _nodes.Size();
		CDD_Node node( rnode.sym, rnode.ch, rnode.ch_size );
		unsigned pos = _nodes.Hit( node, _hash_memory );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [rnode.ch_size];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = rnode.ch[0];
			_nodes[pos].ch[1] = rnode.ch[1];
			for ( i = 2; i < rnode.ch_size; i++ ) _nodes[pos].ch[i] = rnode.ch[i];
		}
		return pos;
	}
	NodeID Push_Node( Decision_Node & bnode )
	{
		unsigned old_size = _nodes.Size();
		NodeID ch[2] = { bnode.low, bnode.high };
		CDD_Node node( bnode.var, ch, 2 );
		unsigned pos = _nodes.Hit( node, _hash_memory );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [2];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = bnode.low;
			_nodes[pos].ch[1] = bnode.high;
		}
		return pos;
	}
	NodeID Push_Decision_Node( Variable var, unsigned low, unsigned high )
	{
		if ( low == high ) return low;
		unsigned old_size = _nodes.Size();
		NodeID ch[2] = { low, high };
		CDD_Node node( var, ch, 2 );
		unsigned pos = _nodes.Hit( node, _hash_memory );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [2];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = low;
			_nodes[pos].ch[1] = high;
		}
		return pos;
	}
	NodeID Push_Conjunction_Node( unsigned type, NodeID * ch, unsigned size )
	{
		if ( size == 0 ) return NodeID::top;
		if ( size == 1 ) return ch[0];
		unsigned old_size = _nodes.Size();
		CDD_Node node( type, ch, size );
		unsigned pos = _nodes.Hit( node, _hash_memory );
		if ( pos == old_size ) {
			_nodes[pos].ch = new NodeID [size];  // NOTE: replace _nodes[pos].ch by a dynamic array
			_nodes[pos].ch[0] = ch[0];
			_nodes[pos].ch[1] = ch[1];
			for ( unsigned i = 2; i < size; i++ ) _nodes[pos].ch[i] = ch[i];
		}
		return pos;
	}
	unsigned Search_First_Non_Literal_Position( unsigned n )
	{
		assert( _nodes[n].sym == CDD_SYMBOL_DECOMPOSE );
		if ( Is_Fixed( _nodes[n].ch[_nodes[n].ch_size - 1] ) ) return _nodes[n].ch_size;
		if ( !Is_Fixed( _nodes[n].ch[0] ) ) return 0;
		unsigned i;
		for ( i = _nodes[n].ch_size - 2; !Is_Fixed( _nodes[n].ch[i] ); i-- );
		return i + 1;
	}
	unsigned Search_First_Non_Literal_Position( CDD_Node & node )
	{
		assert( node.sym == CDD_SYMBOL_DECOMPOSE );
		if ( Is_Fixed( node.ch[node.ch_size - 1] ) ) return node.ch_size;
		if ( !Is_Fixed( node.ch[0] ) ) return 0;
		unsigned i;
		for ( i = node.ch_size - 2; !Is_Fixed( node.ch[i] ); i-- );
		return i + 1;
	}
	bool Is_Equivalence_Node( CDD_Node & node )
	{
		if ( node.sym <= _max_var && Is_Literal( node.ch[0] ) && Is_Literal( node.ch[1] ) ) {
			return node.ch[0] == ( node.ch[1] ^ 0x01 );
		}
		else return false;
	}
};


}


#endif  // _CDD_h_
