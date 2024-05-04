#ifndef _Graph_Structures_h_
#define _Graph_Structures_h_

#include "Basic_Functions.h"
#include "../Primitive_Types/CNF_Formula.h"


namespace KCBox {


class Chain
{
protected:
    vector<unsigned> _elems;
	vector<unsigned> _rank;
public:
    Chain() {}  /// empty chain
    Chain( unsigned size ) { _elems.reserve( size ); _rank.reserve( size + 1 ); }
    Chain( vector<unsigned> & elems );
    Chain( istream & fin );
    void Assign( vector<unsigned>::iterator begin, vector<unsigned>::iterator end );
    void Reserve( unsigned capa ) { _elems.reserve( capa ); }
    void Append( unsigned elem );  /// Add a element
    void Append( unsigned * elems, unsigned size );  /// Add some elements
    void Append( vector<unsigned>::iterator begin, vector<unsigned>::iterator end );  /// Add some elements
	unsigned operator [] ( const unsigned pos ) const { return _elems[pos]; }
	void Clear() { _elems.clear(); _rank.clear(); }
	void Erase( unsigned elem )
	{
	    if ( _rank[elem] == UNSIGNED_UNDEF ) return;
	    for ( unsigned i = _rank[elem] + 1; i < _elems.size(); i++ ) {
            _elems[i-1] = _elems[i];
            _rank[_elems[i-1]] = i - 1;
	    }
	    _elems.pop_back();
	    _rank[elem] = UNSIGNED_UNDEF;
	}
	void Swap( unsigned elem1, unsigned elem2 );
	void Swap_Position( unsigned pos1, unsigned pos2 );
	template<typename R> void Sort_Reverse( unsigned bpos, unsigned epos, R * rank )
	{
	    Insert_Sort_Reverse_Rank( _elems.begin() + bpos, _elems.begin() + epos, rank );
        for ( unsigned i = bpos; i < epos; i++ ) {
            _rank[_elems[i]] = i;
        }
	}
	void Rename( unsigned * elem_map )
	{
        for ( unsigned i = 0; i < _elems.size(); i++ ) {
            _elems[i] = elem_map[_elems[i]];
            _rank[_elems[i]] = i;
        }
	}
	bool Empty() const { return _elems.empty(); }
	unsigned Size() const { return _elems.size(); }
	void Shrink( unsigned size )
	{
		ASSERT( size <= _elems.size() );
	    for ( unsigned i = size; i < _elems.size(); i++ ) {
            _rank[_elems[i]] = UNSIGNED_UNDEF;
	    }
	    _elems.resize( size );
	}
	bool Contain( unsigned elem ) const { return elem < _rank.size() && _rank[elem] != UNSIGNED_UNDEF; }
	unsigned Rank( unsigned elem ) const { return _rank[elem]; }
	const unsigned * Rank() { return _rank.data(); }
	unsigned Max() const
	{
		if ( _elems.empty() ) return UNSIGNED_UNDEF;
		unsigned i;
		for ( i = _rank.size() - 1; _rank[i] == UNSIGNED_UNDEF; i-- ) {}
		return i;
	}
	bool Less_Than( unsigned elem1, unsigned elem2 ) const
	{
	    assert( _rank[elem1] != UNSIGNED_UNDEF && _rank[elem2] != UNSIGNED_UNDEF );
	    return _rank[elem1] < _rank[elem2];
	}
	bool Less_Eq( unsigned elem1, unsigned elem2 ) const
	{
	    assert( _rank[elem1] != UNSIGNED_UNDEF && _rank[elem2] != UNSIGNED_UNDEF );
	    return _rank[elem1] <= _rank[elem2];
	}
	bool operator == ( const Chain & other );
	bool Subchain( Chain & other ) const;  /// *this is a subchain of other
	void Swap( Chain & other ) { _elems.swap( other._elems );  _rank.swap( other._rank ); }
	void Display( ostream & out, const char separator = ',' ) const
	{
		if ( _elems.empty() ) {
			out << "empty chain" << endl;
			return;
		}
		out << _elems[0];
		if ( BLANK_CHAR_GENERAL( separator ) ) {
			for ( unsigned i = 1; i < _elems.size(); i++ ) {
				out << separator << _elems[i];
			}
		}
		else {
			for ( unsigned i = 1; i < _elems.size(); i++ ) {
				out << separator << ' ' << _elems[i];
			}
		}
		out << endl;
	}
	void Display_Top( ostream & out, unsigned top ) const
	{
		if ( _elems.size() < top ) {
			out << "no enough elements" << endl;
			return;
		}
		out << _elems[0];
		for ( unsigned i = 1; i < top; i++ ) out << ", " << _elems[i];
		out << endl;
	}
public:
    static Chain default_empty_chain;
};


//====================================================================================================


struct Neighbour
{
	unsigned vertex;
	Neighbour * next;
	unsigned infor;
	Neighbour( unsigned v, Neighbour * n ): vertex(v), next(n), infor( UNSIGNED_UNDEF ) {}
	Neighbour() : infor( UNSIGNED_UNDEF ) {}
};

struct Vertex
{
	unsigned degree;
	unsigned infor;
	Neighbour * adjacency;  /// a sentinel head neighbour and a common tail neighbour
	Vertex() {}
	Vertex( Neighbour * list ): degree( 0 ), infor( UNSIGNED_UNDEF ) {
		adjacency = new Neighbour( 0, list );  /// NOTE: must maintain the memory by the users
	}
};

class Greedy_Graph
{
	friend class Simple_TreeD;
protected:
	/*NOTE:
	The actual number of vertices may be less than max_vertex due to the removal of vertices
	*/
	unsigned max_vertex;
	/*NOTE:
	The vertex of adj_lists[i].vertex denote the existence the corresponding vertex:
	adj_lists[i].vertex == 0: not existent
	adj_lists[i].vertex == -1: existent
	*/
	vector<Vertex> vertices;
	Neighbour * free_neighbours;
	Neighbour * common_tail_neighbour;
protected:
    bool * vertex_appeared;
    bool * vertex_seen;
public:
	Greedy_Graph( unsigned max );
	Greedy_Graph( unsigned max, vector<vector<unsigned>> & edges ); // all neighbours of i are stored in edges[i]
	~Greedy_Graph();
	unsigned Max_Vertex() const { return max_vertex; }
	inline bool Is_Vertex_Isolated( unsigned v ) { return vertices[v].adjacency->next->vertex > max_vertex; }
	inline Vertex & Vertices( unsigned i ) { return vertices[i]; }
	inline vector<Neighbour *> Neighbours( unsigned v );
	inline void Add_Vertex();
	inline void Add_Edge_Naive( unsigned u, unsigned v );
	inline void Add_Edge_Naive_No_Check( unsigned u, unsigned v );
	inline void Add_Edge_Naive_No_Check_Semi( unsigned u, unsigned v );
	inline void Add_Edge_Naive_No_Check_Semi_No_Change( Neighbour * & npre, unsigned v );
	inline void Remove_Vertex( unsigned v );
	inline void Remove_Vertex_Naive( unsigned v );
	inline void Remove_Vertex_Front( unsigned v );
	inline void Remove_Vertex_Back( unsigned v );
	inline void Remove_Edge_No_Check_Semi( unsigned u, unsigned v );
	/* NOTE:
	* Eliminate vertex in induced order
	*/
	void Eliminate_Vertex( unsigned v );
	void Eliminate_Vertex_Opt( unsigned v );  // use g_element_appear, this function is optimized from Eliminate_Vertex
	void Eliminate_Vertex_No_Infor( unsigned v );
	void Eliminate_Vertex_Naive( unsigned v );
	bool Is_Adjecent_Naive( unsigned u, unsigned v );
	void Fill_Size( unsigned v );
	void Fill_Size_Opt( unsigned v );
	unsigned Fill_Size_Naive( unsigned v );
	void Verify_Fill_Size();
	void Induced_Order_Min_Fill_Opt( unsigned * chain );
	unsigned Induced_Width_Min_Fill_Opt();
	unsigned Induced_Width_Min_Fill_Bound( unsigned bound );  // if output <= bound, then it is the true width, else it is not
	void Strongly_Connected_Components( vector<vector<unsigned>> & components );  /// Tarjan's strongly connected components algorithm
	void Strongly_Connected_Component( unsigned v, vector<unsigned> & component );  /// Tarjan's strongly connected components algorithm
	void Display( ostream & fout );
	void Display_PACE( ostream & fout );
	void Display_Degree( ostream & fout );
	void Display_Fill_Size( ostream & fout );
protected:
	inline Neighbour * Allocate_Neighbour();
	inline Neighbour * Allocate_Neighbour( unsigned v, Neighbour * n );
	inline void Free_Neighbour( Neighbour * n );
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
};

inline vector<Neighbour *> Greedy_Graph::Neighbours( unsigned v )
{
	assert( v <= max_vertex );
	assert( vertices[v].degree != UNSIGNED_UNDEF );
	vector<Neighbour *> neighbours;
	Neighbour * p = vertices[v].adjacency->next;
	while ( p->vertex <= max_vertex ) {
		neighbours.push_back( p );
		p = p->next;
	}
	return neighbours;
}

inline void Greedy_Graph::Add_Vertex()
{
	max_vertex++;
	common_tail_neighbour->vertex++;
	Vertex vertex( common_tail_neighbour );
	vertices.push_back( vertex );
	Free_Auxiliary_Memory();
	Allocate_and_Init_Auxiliary_Memory();
}

inline void Greedy_Graph::Add_Edge_Naive( unsigned u, unsigned v )
{
	assert( 0 < u && u <= max_vertex && u != v && 0 < v && v <= max_vertex );
	assert( vertices[u].degree != UNSIGNED_UNDEF && vertices[v].degree != UNSIGNED_UNDEF );
	/* NOTE:
	* Insert (u, v)
	*/
	Neighbour * pre = vertices[u].adjacency;
	Neighbour * p = pre->next;
	while ( p->vertex < v ) {
		pre = p;
		p = p->next;
	}
	if ( p->vertex == v ) return;
	pre->next = Allocate_Neighbour( v, p );
	vertices[u].degree++;
	/* NOTE:
	* Insert (v, u)
	*/
	pre = vertices[v].adjacency;
	p = pre->next;
	while ( p->vertex < u ) {
		pre = p;
		p = p->next;
	}
	pre->next = Allocate_Neighbour( u, p );
	vertices[v].degree++;
}

inline void Greedy_Graph::Add_Edge_Naive_No_Check( unsigned u, unsigned v )
{
	assert( u <= max_vertex && u != v && v <= max_vertex );
	assert( vertices[u].degree != UNSIGNED_UNDEF && vertices[v].degree != UNSIGNED_UNDEF );
	/* NOTE:
	Insert (u, v)
	*/
	Neighbour * pre = vertices[u].adjacency;
	Neighbour * p = pre->next;
	while ( p->vertex < v ) {
		pre = p;
		p = p->next;
	}
	pre->next = Allocate_Neighbour( v, p );
	vertices[u].degree++;
	/* NOTE:
	Insert (v, u)
	*/
	pre = vertices[v].adjacency;
	p = pre->next;
	while ( p->vertex < u ) {
		pre = p;
		p = p->next;
	}
	pre->next = Allocate_Neighbour( u, p );
	vertices[v].degree++;
}

inline void Greedy_Graph::Add_Edge_Naive_No_Check_Semi( unsigned u, unsigned v )
{
	assert( 0 < u && u <= max_vertex && u != v && 0 < v && v <= max_vertex );
	assert( vertices[u].degree != UNSIGNED_UNDEF && vertices[v].degree != UNSIGNED_UNDEF );
	/* NOTE:
	* Insert (u, v)
	*/
	Neighbour * pre = vertices[u].adjacency;
	Neighbour * p = pre->next;
	while ( p->vertex < v ) {
		pre = p;
		p = p->next;
	}
	pre->next = Allocate_Neighbour( v, p );
	vertices[u].degree++;
}

inline void Greedy_Graph::Add_Edge_Naive_No_Check_Semi_No_Change( Neighbour * & npre, unsigned v ) // degree no change
{
	while ( npre->next->vertex < v ) {
		npre = npre->next;
	}
	npre->next = Allocate_Neighbour( v, npre->next );
	npre = npre->next;
}

inline void Greedy_Graph::Remove_Vertex_Naive( unsigned v )
{
	assert( v <= max_vertex );
	Neighbour * n = vertices[v].adjacency->next;
	vertices[v].adjacency->next = common_tail_neighbour;
	vertices[v].degree = UNSIGNED_UNDEF;
	while ( n->vertex <= max_vertex ) {
		Neighbour * nnpre = vertices[n->vertex].adjacency;
		while ( nnpre->next->vertex != v ) nnpre = nnpre->next;
		Neighbour * tmp = nnpre->next;
		nnpre->next = tmp->next;
		Free_Neighbour( tmp ); // Remove v from the adjecency list of its neighbour
		vertices[n->vertex].degree--;
		tmp = n;
		n = n->next;
		Free_Neighbour( tmp ); // Remove the neighbour of v
	}
	assert( n == common_tail_neighbour );
}

inline void Greedy_Graph::Remove_Vertex( unsigned v )  // NOTE: remove the neighbours of v from its adjacency, and remove v from the adjacency of the neighbours of v
{
	assert( v <= max_vertex );
	Neighbour *n, *nn, *nn_pre;
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		vertex_appeared[n->vertex] = true;
	}
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		nn_pre = vertices[n->vertex].adjacency;
		nn = nn_pre->next;
		while ( nn->vertex < v ) {
			vertices[n->vertex].infor -= !vertex_appeared[nn->vertex];  // Preiously, v and nn->vertex are two neighbours of n->vertex which are not connected
			nn_pre = nn;
			nn = nn->next;
		}
		nn_pre->next = nn->next;
		Free_Neighbour( nn );
		nn = nn_pre->next;
		while ( nn->vertex <= max_vertex ) {
			vertices[n->vertex].infor -= !vertex_appeared[nn->vertex];
			nn = nn->next;
		}
		vertices[n->vertex].degree--;
	}
	n = vertices[v].adjacency->next;
	vertices[v].adjacency->next = common_tail_neighbour;
	vertices[v].degree = UNSIGNED_UNDEF;  /// the label of being removed
	while ( n->vertex <= max_vertex ) {
		vertex_appeared[n->vertex] = false;
		Neighbour * tmp = n;
		n = n->next;
		Free_Neighbour( tmp ); // Remove the neighbour of v
	}
	assert( n == common_tail_neighbour );
}

inline void Greedy_Graph::Remove_Vertex_Front( unsigned v )  // NOTE: remove the neighbours of v from its adjacency
{
	assert( v <= max_vertex );
	Neighbour * n = vertices[v].adjacency->next;
	vertices[v].adjacency->next = common_tail_neighbour;
	vertices[v].degree = UNSIGNED_UNDEF;
	while ( n->vertex <= max_vertex ) {
		Neighbour * tmp = n;
		n = n->next;
		Free_Neighbour( tmp ); // Remove the neighbour of v
	}
	assert( n == common_tail_neighbour );
}

inline void Greedy_Graph::Remove_Vertex_Back( unsigned v )  // NOTE: remove v from the adjacency of the neighbours of v
{
	Neighbour *n, *nn, *nn_pre;
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		vertex_appeared[n->vertex] = true;
	}
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		nn_pre = vertices[n->vertex].adjacency;
		nn = nn_pre->next;
		while ( nn->vertex < v ) {
			if ( !vertex_appeared[nn->vertex] ) vertices[n->vertex].infor--;  // Preiously, v and nn->vertex are two neighbours of n->vertex which are not connected
			nn_pre = nn;
			nn = nn->next;
		}
		nn_pre->next = nn->next;
		Free_Neighbour( nn );
		nn = nn_pre->next;
		while ( nn->vertex <= max_vertex ) {
			if ( !vertex_appeared[nn->vertex] ) vertices[n->vertex].infor--;
			nn = nn->next;
		}
		vertices[n->vertex].degree--;
	}
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		vertex_appeared[n->vertex] = false;
	}
}

inline bool Greedy_Graph::Is_Adjecent_Naive( unsigned u, unsigned v )
{
	assert( u <= max_vertex && u != v && 0 < v && v <= max_vertex );
	assert( vertices[u].degree != UNSIGNED_UNDEF && vertices[v].degree != UNSIGNED_UNDEF );
	Neighbour * p = vertices[u].adjacency->next;
	while ( p->vertex < v ) p = p->next;
	return p->vertex == v;
}

inline void Greedy_Graph::Fill_Size( unsigned v )
{
	vertices[v].infor = 0;
	Neighbour * n = vertices[v].adjacency->next;
	while ( n->vertex <= max_vertex ) {
		Neighbour * m = n->next;
		Neighbour * nn = vertices[n->vertex].adjacency->next;
		while ( m->vertex <= max_vertex ) {
			if ( m->vertex < nn->vertex ) {
				vertices[v].infor++;
				m = m->next;
			}
			else if ( m->vertex == nn->vertex ) {
				m = m->next;
				nn = nn->next;
			}
			else nn = nn->next;
		}
		n = n->next;
	}
}

inline void Greedy_Graph::Fill_Size_Opt( unsigned v )
{
	if ( vertices[v].adjacency->next->vertex > max_vertex ) {
		vertices[v].infor = 0;
		return;
	}
	vertices[v].infor = 0;
	Neighbour * n = vertices[v].adjacency->next->next;
	while ( n->vertex <= max_vertex ) {
		vertex_appeared[n->vertex] = true;
		n = n->next;
	}
	n = vertices[v].adjacency->next;
	for ( unsigned num = vertices[v].degree - 1; num > 0; num-- ) {
		vertices[v].infor += num;
		for ( Neighbour * nn = vertices[n->vertex].adjacency->next; nn->vertex <= max_vertex; nn = nn->next ) {
			vertices[v].infor -= vertex_appeared[nn->vertex];  // reduce the number of shared neighbour
		}
		n = n->next;
		vertex_appeared[n->vertex] = false;
	}
}

inline unsigned Greedy_Graph::Fill_Size_Naive( unsigned v )
{
	unsigned size = 0;
	Neighbour * p = vertices[v].adjacency->next;
	while ( p->vertex <= max_vertex ) {
		Neighbour * q = p->next;
		while ( q->vertex <= max_vertex ) {
			size += !Is_Adjecent_Naive( p->vertex, q->vertex );
			q = q->next;
		}
		p = p->next;
	}
	return size;
}

inline void Greedy_Graph::Verify_Fill_Size()
{
	for ( unsigned i = 0; i <= max_vertex; i++ ) {
		if ( vertices[i].degree == UNSIGNED_UNDEF ) continue;
		assert( vertices[i].infor != UNSIGNED_UNDEF );
		unsigned nf = Fill_Size_Naive( i );
		assert( vertices[i].infor == nf );
	}
}

inline Neighbour * Greedy_Graph::Allocate_Neighbour()
{
	Neighbour * neigh;
	if ( free_neighbours != NULL ) {
		neigh = free_neighbours;
		free_neighbours = free_neighbours->next;
	}
	else neigh = new Neighbour;
	return neigh;
}

inline Neighbour * Greedy_Graph::Allocate_Neighbour( unsigned v, Neighbour * n )
{
	Neighbour * neigh;
	if ( free_neighbours != NULL ) {
		neigh = free_neighbours;
		free_neighbours = free_neighbours->next;
		neigh->vertex = v;
		neigh->next = n;
	}
	else neigh = new Neighbour( v, n );
	return neigh;
}

inline void Greedy_Graph::Free_Neighbour( Neighbour * n )
{
	n->next = free_neighbours;
	free_neighbours = n;
}


//====================================================================================================


struct TreeD_Cluster_Adjacency
{
	unsigned ordinal;  // point the adjacent cluster
	TreeD_Cluster_Adjacency * next;
	unsigned * sep;  // the variables shared with ordinal-cluster
	unsigned sep_size;
	unsigned infor;
	double weight;  // used in message passing algorithm
	TreeD_Cluster_Adjacency( unsigned c, TreeD_Cluster_Adjacency * a ): ordinal( c ), next( a ), sep( NULL ), \
		sep_size( 0 ), infor( UNSIGNED_UNDEF )	{}
//	TreeD_Cluster_Adjacency() {}
	unsigned Separation_Mask_Move( bool * seen, unsigned * target )
	{
		unsigned i, num;
		for ( i = num = 0; i < sep_size; i++ ) {
			if ( seen[sep[i]] ) {
				target[num++] = sep[i];
				seen[sep[i]] = false;
			}
		}
		return num;
	}
};

struct Simple_TreeD_Cluster
{
	unsigned * vars;
	unsigned num_vars;
	unsigned degree;
	unsigned infor;
	TreeD_Cluster_Adjacency * adj;
	Simple_TreeD_Cluster(): vars( NULL ), num_vars( 0 ), adj( NULL ) {}
	Simple_TreeD_Cluster( TreeD_Cluster_Adjacency * n ): vars( NULL ), num_vars( 0 ), degree( 0 ), infor( UNSIGNED_UNDEF )
	{
		adj = new TreeD_Cluster_Adjacency( 0, n );
	}
	bool Subset_Except_One_Var( unsigned pos, Simple_TreeD_Cluster & other )
	{
		return Subset_Except_One( vars, num_vars, pos, other.vars, other.num_vars );
	}
	unsigned Separation( Simple_TreeD_Cluster & other, unsigned * sep )
	{
		return Intersection( vars, num_vars, other.vars, other.num_vars, sep );
	}
	unsigned Separation_Mask( Simple_TreeD_Cluster & other, bool * seen, unsigned * sep )
	{
		unsigned i = 0, j = 0, num = 0;
		while ( i < num_vars && j < other.num_vars ) {
			if ( vars[i] < other.vars[j] ) i++;
			else if ( vars[i] > other.vars[j] ) j++;
			else {
				if ( seen[vars[i]] ) {
					sep[num++] = vars[i];
					seen[vars[i]] = false;
				}
				i++, j++;
			}
		}
		return num;
	}
};

class Simple_TreeD  /// without the information about factors (e.g., clauses in cnf and factors in pgm)
{
public:
	Simple_TreeD( Greedy_Graph & graph );  // using min-fill to generate tree decomposition from graph
	Simple_TreeD( Greedy_Graph & graph, unsigned bound );  /// using min-fill to generate tree decomposition from graph, and if the treewidth exceeds bound, then terminate
	Simple_TreeD( Greedy_Graph & graph, unsigned bound, bool opt );  /// using min-fill to generate tree decomposition from graph, and if the treewidth exceeds bound, then terminate
	Simple_TreeD( istream & in );
	~Simple_TreeD();
	Chain Transform_Chain( double * weight );
	void Compute_DTree_Scores( double * scores );
	unsigned Width();
	void Display( ostream & out );
	void Verify();
	void Verify( Greedy_Graph & graph );
protected:
	unsigned _max_vertex;
	vector<Simple_TreeD_Cluster> _clusters;
protected:  // auxiliary memory
	double * _vertex_weight;
protected:
	void Allocate_and_Init_Auxiliary_Memory();
	void Free_Auxiliary_Memory();
    void Generate_Clusters( Greedy_Graph & graph );
    void Generate_Singleton_Cluster();
	void Add_First_Cluster( Simple_TreeD_Cluster & cluster );
	void Add_Cluster( Simple_TreeD_Cluster & cluster, unsigned neighbour );
	/* NOTE:
	* The variables of the last cluster subsumes the ones of itr
	*/
	void Minimize( vector<Simple_TreeD_Cluster>::iterator itr, Simple_TreeD_Cluster & cluster );
	void Add_Cluster_Neighbour( unsigned cluster, unsigned neighbour );
	void Minimize();
	void Merge_Cluster_Neighbour( unsigned cluster, unsigned neighbour );
	void Add_Cluster_Neighbours( unsigned cluster, TreeD_Cluster_Adjacency * adj );
	void Remove_Leaf( unsigned leaf );
protected:
//	bool Lit_LT( unsigned l1, unsigned l2, unsigned * var_rank ) { return var_rank[LIT_VAR(l1)] < var_rank[LIT_VAR(l2)]; }
	void Compute_All_Separators();
	unsigned Compute_Root_Lowest_Weighted_Depth_Reserved(); //reserve infor of clusters
	void Compute_Fixed_Root_Weight_Reserved( unsigned root ); //reserve infor of clusters
	TreeD_Cluster_Adjacency * Search_First_Seen_Neighbour( TreeD_Cluster_Adjacency * head );
	TreeD_Cluster_Adjacency * Pick_Preferred_Neighbour( TreeD_Cluster_Adjacency * head, Chain & chain );
	void DFS_With_Vertex_Appearance( Simple_TreeD_Cluster & source, unsigned vertex );
public:
	static void Debug()
	{
	    Random_Generator rand_gen;
	    rand_gen.Reset( 0 );
	    Debug_Print_Visit_Number( cerr, __LINE__ );
//	    CNF_Formula cnf( rand_gen, 8, 15, 3, 3 );
//	    cout << cnf;
//	    Simple_TreeD treed( cnf );
	}
};



}


#endif  // _Graph_Structures_h_
