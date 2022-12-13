#ifndef _Partial_CCDD_h_
#define _Partial_CCDD_h_

#include "../Search_Graph.h"
#include "../KC_Languages/CDD.h"

namespace KCBox {


struct Partial_Decision_Node
{
	Variable var;
	NodeID ch[2];
	double estimate;
	NodeID & Low() { return ch[0]; }
	NodeID & High() { return ch[1]; }
	Partial_Decision_Node() {}
	Partial_Decision_Node( Variable v, NodeID l, NodeID h, double w ): var(v), estimate(w) { ch[0] = l, ch[1] = h; }
	operator Decision_Node () const { return Decision_Node( var, ch[0], ch[1] ); }
	unsigned Lit( const unsigned max_var ) const;
};

struct Rough_Partial_CDD_Node
{
public:
	unsigned sym;
	vector<NodeID> ch;
	vector<Literal> imp;
	unsigned freq[2];  // record the number of visiting children when it is a decision node
	double estimate;  // the estimate of the marginal distribution of sym for a decision node
	vector<Model *> models;  // record some models of unknown node
protected:
public:
	Rough_Partial_CDD_Node() {}
	void Update( Literal * lits, unsigned lit_size ) // decomposition node
	{
		imp.resize( lit_size );
		for ( unsigned i = 0; i < lit_size; i++ ) {  // no leaf node
			imp[i] = lits[i];
		}
	}
	void Update( NodeID child ) // decomposition node
	{
		ch.resize( 1 );
		ch[0] = child;
	}
	void Update( NodeID * children, unsigned ch_size ) // decomposition node
	{
		ch.resize( ch_size );
		for ( unsigned i = 0; i < ch_size; i++ ) {  // no leaf node
			ch[i] = children[i];
		}
	}
	size_t Memory()
	{
		return sizeof(Rough_Partial_CDD_Node) \
		 + ch.capacity() * sizeof(NodeID) \
		 + imp.capacity() * sizeof(Literal) \
		 + models.capacity() * sizeof(Model *);
	}
	void Display( ostream & out )
	{
		if ( sym == SEARCH_CONFLICTED ) out << "Conflicted";
		else if ( sym == SEARCH_EMPTY ) out << "Empty";
		else if ( sym == SEARCH_KNOWN ) {
			out << "Known: " << ch[0];
		}
		else if ( sym == SEARCH_UNKNOWN ) {
			out << "Unknown";
		}
		else if ( sym == SEARCH_DECOMPOSED ) {
			out << "Decomposed: literals";
			for ( Literal lit: imp ) {
				out << ' ' << ExtLit( lit );
			}
			out << ", components";
			for ( unsigned i = 0; i < ch.size(); i++ ) {
				out << ' ' << ch[i];
			}
		}
		else if ( sym == SEARCH_KERNELIZED ) {
			out << "Kernelized: component " << ch[0];
			out << ", literal equivalences";
			for ( unsigned i = 0; i < imp.size(); i += 2 ) {
				out << ' ' << ExtLit( imp[i] ) << " <-> " << ExtLit( imp[i + 1] );
			}
		}
		else out << "Decision on " << sym << ": low " << ch[0] << ", high " << ch[1] << ", cache " << ch[2];
	}
};

struct Partial_CDD_Node: public Search_Node
{
public:
	unsigned freq[2];  // record the number of visiting children when it is a decision node
	double estimate;  // the estimate of the marginal distribution of sym for a decision node
	BigFloat weight;
	vector<Model *> models;  // record some models of unknown node
public:
	Partial_CDD_Node() {}
	Partial_CDD_Node( unsigned num_imp, unsigned num_ch ): Search_Node( num_imp, num_ch ) {} // allocate memory
	Partial_CDD_Node( bool val ) : Search_Node( val ) {} // constant node
	Partial_CDD_Node( Literal lit ) : Search_Node( lit ) {} // constant node
	Partial_CDD_Node( Partial_Decision_Node & dnode, unsigned cloc ): Search_Node( dnode.var, dnode.ch[0], dnode.ch[1], cloc ), estimate( dnode.estimate ) {} // decision node
	Partial_CDD_Node( Literal * lits, unsigned num_lit, NodeID * children, unsigned num_ch ): Search_Node( lits, num_lit, children, num_ch ) {} // decomposition node
	Partial_CDD_Node( NodeID core, Literal * lit_pairs, unsigned num_pairs, unsigned cloc ) : Search_Node( core, lit_pairs, num_pairs, cloc ) {} // kernelized node
	Partial_CDD_Node( NodeID core, const vector<Literal> & lit_pairs, unsigned cloc ) : Search_Node( core, lit_pairs, cloc ) {} // kernelized node
	Partial_CDD_Node( BigFloat w, unsigned cloc ) : Search_Node( NodeID::top, cloc ), weight( w ) {}  // known node
	Partial_CDD_Node( vector<Model *> & mods ) : Search_Node( NodeID::undef ) { models.swap( mods ); }  // unknown node
	operator Literal () const
	{
		if ( sym == SEARCH_DECOMPOSED && imp_size == 1 && ch_size == 0 ) return imp[0];
		else return Literal::undef;
	}
	unsigned Memory() const
	{
		return Search_Node::Memory()  // sym
		 + 2 * sizeof(unsigned)  // freq
		 + sizeof(double)  // estimate
		 + sizeof(BigFloat)  // weight
		 + models.capacity() * sizeof(Model *);
	}
	void Display( ostream & out, NodeID id ) const
	{
		out << id << ": ";
		Search_Node::Display( out );
		out << endl;
	}
	void Display_Weight( ostream & out, bool sorted = false )
	{
		if ( sym == SEARCH_CONFLICTED ) out << "Conflicted";
		else if ( sym == SEARCH_EMPTY ) out << "Empty";
		else if ( sym == SEARCH_KNOWN ) {
			out << "Known: " << ch[0] << ", cache " << caching_loc;
		}
		else if ( sym == SEARCH_UNKNOWN ) {
			out << "Unknown";
		}
		else if ( sym == SEARCH_DECOMPOSED ) {
			if ( sorted ) {
				vector<Literal> sorted_imps;
				for ( unsigned i = 0; i < imp_size; i++ ) {
					sorted_imps.push_back( imp[i] );
				}
				Quick_Sort( sorted_imps );
				for ( unsigned i = 0; i < imp_size; i++ ) {
					imp[i] = sorted_imps[i];
				}
			}
			out << "Decomposed: literals";
			for ( unsigned i = 0; i < imp_size; i++ ) {
				out << ' ' << ExtLit( imp[i] );
			}
			out << ", components";
			for ( unsigned i = 0; i < ch_size; i++ ) {
				out << ' ' << ch[i];
			}
		}
		else if ( sym == SEARCH_KERNELIZED ) {
			out << "Kernelized: component " << ch[0];
			out << ", literal equivalences";
			for ( unsigned i = 0; i < imp_size; i += 2 ) {
				out << ' ' << ExtLit( imp[i] ) << ' ' << ExtLit( imp[i + 1] );
			}
			out << ", cache " << caching_loc;
		}
		else {
			out << "Decision on " << sym << ": low " << ch[0] << ", high " << ch[1] << ", cache " << caching_loc;
			out << ", estimate " << estimate * 100 << "%";
			out << " #" << freq[0] << " #" << freq[1];
		}
		if ( sym == SEARCH_UNKNOWN ) out << " <?>" << endl;
		else out << " <" << weight << ">" << endl;
	}
};


class Partial_CCDD_Manager: public Diagram_Manager
{
	friend class Partial_CCDD_Compiler;
protected:
	BlockVector<Partial_CDD_Node> _nodes;
protected: //auxiliary memory
	Lit_Equivalency _lit_equivalency;
	size_t _main_memory;
	bool _counting_mode;
public:
	Partial_CCDD_Manager( Variable max_var, unsigned estimated_num_node = LARGE_HASH_TABLE );
	Partial_CCDD_Manager( const Partial_CCDD_Manager & other );
	~Partial_CCDD_Manager();
	void Clear( Model_Pool * pool );
	BigFloat Weight( CDD root );
	size_t Memory();
	void Open_Counting_Mode() { assert( _nodes.Size() == _num_fixed_nodes );  _counting_mode = true; }
	void Remove_Redundant_Nodes( vector<CDD> & kept_nodes );
	void Reset_Frequencies();
	void Display( ostream & out );
	void Display_Nodes( ostream & out );
	void Display_Stat( ostream & out );
	void Display_New_Nodes( ostream & out, unsigned & old_size );
	void Display_Weight( ostream & out, bool sorted = false );
	void Display_Imbalance_Nodes( ostream & out );
	void Display_Partial_CCDD( ostream & out, CDD root );
	void Display_Partial_CCDD_With_Weights( ostream & out, CDD root );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Add_Fixed_Nodes();
	void Free_Auxiliary_Memory();
	void Verify_Decomposability( CDD root );
	void Verify_Parents();
	void Realloc_Model_Space( Model_Pool * pool);
	void Thin_Model_Space( Model_Pool * pool);  // each unknown node reserve one model
	void Init_Reserved_Infor();
	void Replace_Node( unsigned old_node, unsigned new_node );  // replace old_node by new_node, where old_node appears in a DAG
	void Verify_Node( NodeID n );
public: // querying
	unsigned Num_Nodes() { return _nodes.Size(); }
	unsigned Num_Nodes( CDD root );
	unsigned Num_Edges( CDD root );
	unsigned Num_Nodes( unsigned type, CDD root );
	unsigned Decision_Depth( CDD root );  // the max number of decision vertices in all paths from root to leaves
	const Partial_CDD_Node & Node( NodeID n ) { return _nodes[n]; }
	unsigned & Cache_Location( NodeID n ) { return _nodes[n].caching_loc; }
	double Count_Models();
	void Count_Models_Ternary( double & lower, double & inter, double & upper );  // return a lower bound, an upper bound, an intermediate estimation
public: // transformation
	CDD Add_Known_Node( BigFloat count, unsigned cloc ) { return Push_Node( count, cloc ); }
	CDD Add_Unknown_Node( vector<Model *> & mods ) { return Push_Node( mods ); }
	CDD Add_Decision_Node( Partial_Decision_Node & bnode, unsigned cloc );
	CDD Add_Decision_Node( Rough_Partial_CDD_Node & rnode, unsigned cloc );
	CDD Add_Decomposition_Node( Rough_Partial_CDD_Node & rnode );
	CDD Add_Kernelization_Node( Rough_Partial_CDD_Node & rnode, unsigned cloc );
	CDD Update_Decision_Child( NodeID parent, bool sign, NodeID new_child );  // false: low; true: high
	CDD Update_Kernelization_Child( NodeID parent, NodeID new_child );
	void Swap_Unknown_Models( NodeID n, vector<Model *> & models ) { _nodes[n].models.swap( models ); }
	bool Sample( Random_Generator & rand_gen, NodeID n );
	bool Sample_Adaptive( Random_Generator & rand_gen, NodeID n, double prob );
protected:
	bool Is_Node_Known( NodeID n );
protected: // simple inline functions
	bool Is_False( NodeID n ) const { return n == NodeID::bot; }
	bool Is_True( NodeID n ) const { return n == NodeID::top; }
	bool Is_Const( NodeID n ) const { return n <= 2; }
	bool Is_Leaf( NodeID n ) { return _nodes[n].ch_size == 0; }
	bool Is_Fixed( NodeID n ) const { return n < _num_fixed_nodes; }
	NodeID Push_Node( const Partial_CDD_Node & node )
	{
		_main_memory += node.Memory();
		_nodes.Push_Back( node );
		return _nodes.Size() - 1;
	}
	NodeID Push_Node( bool val )  // constant node
	{
		assert( _nodes.Size() == val );
		Partial_CDD_Node node( val );
		if ( val == false ) node.weight = 0;
		else node.weight.Assign_2exp( NumVars( _max_var ) );
		return Push_Node( node );
	}
	NodeID Push_Node( Literal lit )  // constant node
	{
		assert( _nodes.Size() == NumVars( lit.Var() ) * 2 + lit.Sign() );
		Partial_CDD_Node node( lit );
		node.weight.Assign_2exp( NumVars( _max_var ) - 1 );
		return Push_Node( node );
	}
	NodeID Push_Node( Partial_Decision_Node & dnode, unsigned cloc )  // decision node
	{
		assert( 0 < dnode.estimate && dnode.estimate < 1 );
		Partial_CDD_Node node( dnode, cloc );
		node.freq[0] = _nodes[node.ch[0]].sym != SEARCH_UNKNOWN;  // unknown child's frequency is 0
		node.freq[1] = _nodes[node.ch[1]].sym != SEARCH_UNKNOWN;  // unknown child's frequency is 0;
		Decision_Compute_Weight( node );
		return Push_Node( node );
	}
	NodeID Push_Node( Literal * lits, unsigned lit_size, NodeID * children, unsigned ch_size ) // decomposition node
	{
		assert( lit_size + ch_size >= 2 );
		Partial_CDD_Node node( lits, lit_size, children, ch_size );
		node.weight.Assign_2exp( NumVars( _max_var ) - lit_size );
		for ( unsigned i = 0; i < ch_size; i++ ) {  // no leaf node
			if( Is_Leaf( children[i] ) ) assert( _nodes[children[i]].sym == SEARCH_KNOWN );
			node.ch[i] = children[i];
			node.weight *= _nodes[children[i]].weight;
			node.weight.Div_2exp( NumVars( _max_var ) );
		}
		return Push_Node( node );
	}
	NodeID Push_Node( NodeID core, Literal * lit_pairs, unsigned num_pairs, unsigned cloc ) // kernelized node
	{
		Partial_CDD_Node node( core, lit_pairs, num_pairs, cloc );
		node.weight = _nodes[core].weight;
		node.weight.Div_2exp( num_pairs );
		return Push_Node( node );
	}
	NodeID Push_Node( NodeID core, const vector<Literal> & lit_pairs, unsigned cloc ) // kernelized node
	{
		Partial_CDD_Node node( core, lit_pairs, cloc );
		node.weight = _nodes[core].weight;
		node.weight.Div_2exp( lit_pairs.size() / 2 );
		return Push_Node( node );
	}
	NodeID Push_Node( BigFloat w, unsigned cloc )  // known node
	{
		Partial_CDD_Node node( w, cloc );
		return Push_Node( node );
	}
	NodeID Push_Node( vector<Model *> & mods )  // unknown node
	{
		Partial_CDD_Node node( mods );
		return Push_Node( node );
	}
	void Decision_Compute_Weight( Partial_CDD_Node & node )
	{
		assert( node.sym <= _max_var && node.freq[0] + node.freq[1] > 0 );
		Partial_CDD_Node & low = _nodes[node.ch[0]];
		Partial_CDD_Node & high = _nodes[node.ch[1]];
		if ( _counting_mode ) {
			if ( Is_Node_Known( node.ch[0] ) || Is_Node_Known( node.ch[1] )  ) {
				node.weight = low.weight;
				node.weight += high.weight;
				node.weight.Div_2exp( 1 );
				return;
			}
		}
		double ratio0 = 1.0 * node.freq[0] / ( node.freq[0] + node.freq[1] );
		double ratio1 = 1.0 - ratio0;
		double marginal0 = 1 - node.estimate;
		double marginal1 = node.estimate;
		switch (1) {
		case 1:
			node.weight.Weighted_Sum( 0.5 * ratio0 / marginal0, low.weight, 0.5 * ratio1 / marginal1, high.weight );
			break;
		case 2:
			node.weight.Mean( low.weight, high.weight, (ratio0 / marginal0) / (ratio0 / marginal0 + ratio1 / marginal1) );
			break;
		case 3:
			node.weight.Mean( low.weight, high.weight, ratio0 );
			break;
		}
//		cout << "ratio = " << ratio0 << endl;  // ToRemove
//		cout << "marginal = " << marginal0 << endl;  // ToRemove
//		cout << "ch[0]->weight = " << ch[0]->weight << endl;  // ToRemove
//		cout << "ch[1]->weight = " << ch[1]->weight << endl;  // ToRemove
//		cout << weight << endl;  // ToRemove
//		cout.flush();  // ToRemove
	}
	void Decomposition_Update_Weight( Partial_CDD_Node & node )  // update weight
	{
		node.weight.Assign_2exp( NumVars(_max_var) - node.imp_size );
//		cout << "weight = " << weight << endl;  // ToRemove
		for ( unsigned i = 0; i < node.ch_size; i++ ) {  // no leaf node except known
			if( Is_Leaf(node.ch[i]) ) assert( _nodes[node.ch[i]].sym == SEARCH_KNOWN );
			node.weight *= _nodes[node.ch[i]].weight;
			node.weight.Div_2exp( NumVars(_max_var) );
 //		   cout << "ch[" << i << "]->weight = " << ch[i]->weight << endl;  // ToRemove
 //		   cout << "weight = " << weight << endl;  // ToRemove
		}
	}
	void Kernelization_Update_Weight( NodeID n )  // update weight
	{
		Partial_CDD_Node & node = _nodes[n];
		node.weight = _nodes[node.ch[0]].weight;
		node.weight.Div_2exp( node.imp_size / 2 );
	}
	NodeID Map_Link( NodeID n )
	{
		Partial_CDD_Node & node = _nodes[n];
		Partial_CDD_Node new_node( node.ch_size, node.imp_size );
		new_node.sym = node.sym;
		for ( unsigned i = 0; i < node.imp_size; i++ ) {
			new_node.imp[i] = node.imp[i];
		}
		for ( unsigned i = 0; i < node.ch_size; i++ ) {
			new_node.ch[i] = _nodes[node.ch[i]].infor.mark;
		}
		new_node.estimate = node.estimate;
		new_node.weight = node.weight;
		new_node.models = node.models;
		_nodes.Push_Back( new_node );
		return _nodes.Size() - 1;
	}
public:
	static void Config();
	static void Debug();
};


}

#endif
