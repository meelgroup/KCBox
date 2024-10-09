#ifndef _Search_Space_h_
#define _Search_Space_h_

#include "KC_Languages/DAG.h"
#include "Component_Types/Incremental_Component_Cache_Compressed_Clauses.h"


namespace KCBox {


#define SEARCH_CONFLICTED	        (unsigned(-1))
#define SEARCH_EMPTY				(unsigned(-2))
#define SEARCH_KNOWN				(unsigned(-3))
#define SEARCH_UNKNOWN				(unsigned(-4))
#define SEARCH_DECOMPOSED	    	(unsigned(-5))
#define SEARCH_KERNELIZED			(unsigned(-6))


struct Search_Node
{
	unsigned sym;
	Literal * imp;  // implied literals for decomposed conjunction
	unsigned imp_size;
	NodeID * ch;
	unsigned ch_size;
	unsigned caching_loc;
	Node_Infor infor;
	Search_Node(): caching_loc( UNSIGNED_UNDEF ) {}
	Search_Node( unsigned num_imp, unsigned num_ch ): imp_size( num_imp ), ch_size( num_ch ), caching_loc( UNSIGNED_UNDEF )
	{
		Allocate_Memory();
	}
	Search_Node( bool val ): imp_size( 0 ), ch_size( 0 ), caching_loc( UNSIGNED_UNDEF )  // constant node
	{
		Allocate_Memory();
		if ( !val ) sym = SEARCH_CONFLICTED;
		else sym = SEARCH_EMPTY;
	}
	Search_Node( Literal lit ): sym( SEARCH_DECOMPOSED ), imp_size( 1 ), ch_size( 0 ), caching_loc( UNSIGNED_UNDEF )  // literal node
	{
		Allocate_Memory();
		imp[0] = lit;
	}
	Search_Node( Variable var, NodeID low, NodeID high, unsigned cloc ): sym( var ), imp_size( 0 ), ch_size( 2 ), caching_loc( cloc )
	{
		Allocate_Memory();
		ch[0] = low;
		ch[1] = high;
	}
	Search_Node( Decision_Node & dnode, unsigned cloc ): sym( dnode.var ), imp_size( 0 ), ch_size( 2 ), caching_loc( cloc )
	{
		Allocate_Memory();
		ch[0] = dnode.low;
		ch[1] = dnode.high;
	}
	Search_Node( const Literal * lits, unsigned num_lits, const NodeID * comps, unsigned num_comps ):
		sym( SEARCH_DECOMPOSED ), imp_size( num_lits ), ch_size( num_comps ), caching_loc( UNSIGNED_UNDEF )  // decomposition node
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < num_lits; i++ ) {  // no leaf node
			imp[i] = lits[i];
		}
		for ( unsigned i = 0; i < num_comps; i++ ) {  // no leaf node
			ch[i] = comps[i];
		}
	}
	Search_Node( NodeID comp, const Literal * lit_pairs, unsigned num_pairs, unsigned cloc ):
		sym( SEARCH_KERNELIZED ), imp_size( num_pairs * 2 ), ch_size( 1 ), caching_loc( cloc )
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < num_pairs; i++ ) {  // no leaf node
			imp[i + i] = lit_pairs[i + i];
			imp[i + i + 1] = lit_pairs[i + i + 1];
		}
		ch[0] = comp;
	}
	Search_Node( NodeID comp, const vector<Literal> & lit_pairs, unsigned cloc ):
		sym( SEARCH_KERNELIZED ), imp_size( lit_pairs.size() ), ch_size( 1 ), caching_loc( cloc )
	{
		Allocate_Memory();
		for ( unsigned i = 0; i < imp_size; i += 2 ) {  // no leaf node
			imp[i] = lit_pairs[i];
			imp[i + 1] = lit_pairs[i + 1];
		}
		ch[0] = comp;
	}
	Search_Node( NodeID node, unsigned cloc = UNSIGNED_UNDEF ): imp_size( 0 ), caching_loc( cloc )  // non-constant leaf node
	{
		if ( node != NodeID::undef ) {
			assert( cloc != UNSIGNED_UNDEF );
			ch_size = 1;
			Allocate_Memory();
			sym = SEARCH_KNOWN;
			ch[0] = node;
		}
		else {
			ch_size = 0;
			Allocate_Memory();
			sym = SEARCH_UNKNOWN;
		}
	}
	void Free()
	{
        delete [] imp;
        delete [] ch;
	}
	void Realloc_Memory()
	{
		Free();
		imp = new Literal [imp_size];
		if ( imp_size > 0 && imp == NULL ) {
			cerr << "ERROR[Search_Node]: fail for allocating space!" << endl;
			exit( 1 );
		}
		ch = new NodeID [ch_size];
		if ( ch_size > 0 && ch == NULL ) {
			cerr << "ERROR[Search_Node]: fail for allocating space!" << endl;
			exit( 1 );
		}
	}
	size_t Memory() const { return sizeof( Search_Node ) + sizeof( Literal ) * imp_size + sizeof( NodeID ) * ch_size; }
	void Display( ostream & out ) const
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
		}
		else out << "Decision on " << sym << ": low " << ch[0] << ", high " << ch[1];
		if ( caching_loc != UNSIGNED_UNDEF ) out << ", cache " << caching_loc;
	}
	void Display_Stat( ostream & out )
	{
		Display( out );
		infor.Display( out );
	}
protected:
	void Allocate_Memory()
	{
		imp = new Literal [imp_size];
		if ( imp_size > 0 && imp == NULL ) {
			cerr << "ERROR[Search_Node]: fail for allocating space!" << endl;
			exit( 1 );
		}
		ch = new NodeID [ch_size];
		if ( ch_size > 0 && ch == NULL ) {
			cerr << "ERROR[Search_Node]: fail for allocating space!" << endl;
			exit( 1 );
		}
	}
};


template <typename T> class Search_Graph
{
	friend class RCDD_Compiler;
protected:
	Variable _max_var;
	vector<Search_Node> _nodes;
	Incremental_Component_Cache_Compressed_Clauses<T> & _component_cache;
protected:
	NodeID * _path;
	unsigned * _path_mark;
	vector<NodeID> _visited_nodes;
public:
	Search_Graph( Variable max_var, Incremental_Component_Cache_Compressed_Clauses<T> & component_cache ):
		_max_var( max_var ), _component_cache( component_cache )
	{
		_nodes.push_back( Search_Node( false ) );
		_nodes.push_back( Search_Node( true ) );
		_path = new NodeID [2 * _max_var + 1];
		_path_mark = new unsigned [2 * _max_var + 1];
	}
	~Search_Graph()
	{
		for ( unsigned i = 0; i < _nodes.size(); i++ ) {
			_nodes[i].Free();
		}
		delete [] _path;
		delete [] _path_mark;
	}
	void Clear() { _nodes.clear(); }
	size_t Memory()
	{
		size_t memo = 0;
		for ( unsigned i = 0; i < _nodes.size(); i++ ) memo += _nodes[i].Memory();
		return memo;
	}
	unsigned Push_Node( Search_Node & node )  // node.ch will be push into _nodes
	{
		_nodes.push_back( node );
		return _nodes.size() - 1;
	}
	unsigned Push_Decision_Node( Decision_Node & dnode, unsigned cache_loc )
	{
		_nodes.push_back( Search_Node( dnode, cache_loc ) );
		return _nodes.size() - 1;
	}
	unsigned Push_Unknown_Node()
	{
		_nodes.push_back( Search_Node( NodeID::undef ) );
		return _nodes.size() - 1;
	}
	Search_Node & Nodes( unsigned i ) { return _nodes[i]; }
	void Display( ostream & out )
	{
		out << "Number of nodes: " << _nodes.size() << endl;
		for ( unsigned i = 0; i < _nodes.size(); i++ ) {
			out << i << ":\t";
			_nodes[i].Display( out );
			out << endl;
		}
	}
	void Display_Stat( ostream & fout );
protected:
	void Verify()
	{
		NodeID root = _nodes.size() - 1;
		_path[0] = root;
		_path_mark[0] = 0;
		unsigned path_len = 1;
		while ( path_len > 0 ) {
			NodeID top = _path[path_len - 1];
			Search_Node & node = _nodes[top];
			if ( node.ch_size == 0 ) {
				Verify_Leaf( top );
				path_len--;
			}
			else if ( _path_mark[path_len - 1] < node.ch_size ) {
				NodeID child = node.ch[_path_mark[path_len - 1]++];
				if ( !_nodes[child].infor.visited ) {
					_path[path_len] = child;
					_path_mark[path_len++] = 0;
					_nodes[child].infor.visited = true;
					_visited_nodes.push_back( child );
				}
			}
			else if ( node.sym == SEARCH_DECOMPOSED ) {
				Verify_Decomposed_Conjunction( top );
				path_len--;
			}
			else if ( node.sym == SEARCH_KERNELIZED ) {
				Verify_Kernelized_Conjunction( top );
				path_len--;
			}
			else {
                Verify_Decision( top );
				path_len--;
			}
		}
		for ( vector<NodeID>::const_iterator itr = _visited_nodes.begin(), end = _visited_nodes.end(); itr < end; itr++ ) {
			_nodes[*itr].infor.visited = false;
		}
		_visited_nodes.clear();
	}
	void Verify_Decision( NodeID n ) const
	{
		Search_Node & node = _nodes[n];
		assert( node.sym <= _max_var && node.ch_size == 3 );
		Component comp;
		_component_cache.Read_Component_Vars( node.ch[2], comp );
		for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
			assert( node.sym <= comp.Vars( i ) );
		}
	}
	void Verify_Decomposed_Conjunction( NodeID n ) const
	{
		Search_Node & node = _nodes[n];
		assert( node.sym == SEARCH_DECOMPOSED );
		for ( unsigned i = 0; i < node.imp_size; i++ ) {  // no identical imp
			assert( Literal::start <= node.imp[i] && node.imp[i] <= 2 * _max_var + 1 );
			for ( unsigned j = i + 1; j < node.imp_size; j++ ) {
				assert( node.imp[i].Var() != node.imp[j].Var() );
			}
		}
		for ( unsigned i = 0; i < node.imp_size; i++ ) {  // no identical imp
			for ( unsigned j = 0; j < node.ch_size; j++ ) {
				Search_Node & child = _nodes[node.ch[j]];
				assert( child.sym <= _max_var && child.ch_size == 3 );
				Component comp;
				_component_cache.Read_Component_Vars( child.ch[2], comp );
				assert( !comp.Search_Var( node.imp[i].Var() ) );
			}
		}
		for ( unsigned i = 0; i < node.ch_size; i++ ) {  // no identical imp
			Search_Node & child_i = _nodes[node.ch[i]];
			Component comp_i;
			_component_cache.Read_Component_Vars( child_i.ch[2], comp_i );
			for ( unsigned j = i + 1; j < node.ch_size; j++ ) {
				Search_Node & child = _nodes[node.ch[j]];
				Component comp;
				_component_cache.Read_Component_Vars( child.ch[2], comp );
				for ( unsigned k = 0; k < comp.Vars_Size(); k++ ) {
					assert( !comp_i.Search_Var( comp.Vars( k ) ) );
				}
			}
		}
	}
	void Verify_Kernelized_Conjunction( NodeID n ) const
	{
		Search_Node & node = _nodes[n];
		assert( node.sym == SEARCH_KERNELIZED && node.ch_size == 1 );
		Search_Node & child = _nodes[node.ch[0]];
		assert( child.sym <= _max_var && child.ch_size == 3 );
		Component comp;
		_component_cache.Read_Component_Vars( child.ch[2], comp );
		vector<unsigned> lit_equivalency( 2 * _max_var + 2 );
		for ( Literal lit = Literal::start; lit <= 2 * _max_var + 1; lit++ ) {
			lit_equivalency[lit] = lit;
		}
		for ( unsigned i = 0; i < node.imp_size; i += 2 ) {  // no identical imp
			assert( !comp.Search_Var( node.imp[i].Var() ) );
			Literal lit0 = node.imp[i];
			Literal lit1 = node.imp[i + 1];
			assert( lit0.Sign() );
			assert( lit_equivalency[lit0] == lit0 && lit_equivalency[lit1] == lit1 );  // lit1 appears exactly once
			lit_equivalency[~lit1] = ~lit0;
			lit_equivalency[~lit1] = ~lit0;
		}
	}
	void Verify_Leaf( NodeID n ) const
	{
		Search_Node & node = _nodes[n];
		assert( node.ch_size == 0 );
		if ( node.sym == SEARCH_KNOWN ) {
			assert( node.imp_size == 0 && node.ch_size == 1 );
		}
		else {
			assert( node.imp_size == 0 && node.ch_size == 0 );
		}
	}
};


}


#endif
