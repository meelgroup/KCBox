#include "Graph_Structures.h"


namespace KCBox {

//====================================================================================================

Chain Chain::default_empty_chain;

Chain::Chain( vector<unsigned> & elems )
{
	_elems.reserve( elems.size() );
	_rank.reserve( elems.size() + 1 );
	for ( unsigned i = 0; i < elems.size(); i++ ) {
		unsigned elem = elems[i];
		while ( _rank.size() <= elem ) {
			_rank.push_back( UNSIGNED_UNDEF );
		}
		if ( _rank[elem] == UNSIGNED_UNDEF ) {
			_rank[elem] = _elems.size();
			_elems.push_back( elem );
		}
	 }
}

void Chain::Assign( vector<unsigned>::iterator begin, vector<unsigned>::iterator end )
{
	_elems.clear();
	_rank.clear();
	_elems.assign( begin, end );
	for ( ; begin < end; begin++ ) {
		unsigned elem = *begin;
		while ( _rank.size() <= elem ) {
			_rank.push_back( UNSIGNED_UNDEF );
		}
		assert( _rank[elem] == UNSIGNED_UNDEF );
		_rank[elem] = _elems.size();
		_elems.push_back( elem );
	}
}

void Chain::Append( unsigned elem )
{
	while ( _rank.size() <= elem ) {
		_rank.push_back( UNSIGNED_UNDEF );
	}
	if ( _rank[elem] == UNSIGNED_UNDEF ) {
		_rank[elem] = _elems.size();
		_elems.push_back( elem );
	}
}

void Chain::Append( unsigned * elems, unsigned size )
{
	for ( unsigned i = 0; i < size; i++ ) {
		unsigned elem = elems[i];
		while ( _rank.size() <= elem ) {
			_rank.push_back( UNSIGNED_UNDEF );
		}
		if ( _rank[elem] == UNSIGNED_UNDEF ) {
			_rank[elem] = _elems.size();
			_elems.push_back( elem );
		}
	}
}

void Chain::Append( vector<unsigned>::iterator begin, vector<unsigned>::iterator end )
{
	for ( ; begin < end; begin++ ) {
		unsigned elem = *begin;
		while ( _rank.size() <= elem ) {
			_rank.push_back( UNSIGNED_UNDEF );
		}
		if ( _rank[elem] == UNSIGNED_UNDEF ) {
			_rank[elem] = _elems.size();
			_elems.push_back( elem );
		}
	}
}

void Chain::Swap( unsigned elem1, unsigned elem2 )
{
	assert( Contain( elem1 ) && Contain( elem2 ) );
	unsigned pos1 = _rank[elem1], pos2 = _rank[elem2];
	_elems[pos2] = elem1;
	_elems[pos1] = elem2;
	_rank[elem1] = pos2;
	_rank[elem2] = pos1;
}

void Chain::Swap_Position( unsigned pos1, unsigned pos2 )
{
	assert( pos1 < _elems.size() && pos2 < _elems.size() );
	unsigned elem1 = _elems[pos1], elem2 = _elems[pos2];
	_elems[pos2] = elem1;
	_elems[pos1] = elem2;
	_rank[elem1] = pos2;
	_rank[elem2] = pos1;
}

bool Chain::operator == ( const Chain & other )
{
	if ( _elems.size() != other._elems.size() ) return false;
	if ( _elems.empty() ) return true;
	size_t i;
	unsigned tmp = _elems.back();
	_elems.back() = UNSIGNED_UNDEF;
	for ( i = 0; _elems[i] == other._elems[i]; i++ ) {}
	_elems.back() = tmp;
	return _elems[i] == other._elems[i];
}

bool Chain::Subchain( Chain & other ) const
{
	if ( _elems.empty() ) return true;
	if ( !other.Contain( _elems[0] ) ) return false;
	for ( unsigned i = 1; i < _elems.size(); i++ ) {
		if ( !other.Contain( _elems[i] ) ) return false;
		if ( !other.Less_Than( _elems[i-1], _elems[i] ) ) return false;
	}
	return true;
}

//====================================================================================================


Greedy_Graph::Greedy_Graph( unsigned max ): max_vertex( max ), free_neighbours( nullptr )
{
	Allocate_and_Init_Auxiliary_Memory();
	common_tail_neighbour = new Neighbour( max + 1, nullptr );  // exact one dummy node whose vertex is more than max_vertex
	Vertex vertex( new Neighbour( 0, common_tail_neighbour ) );
	vertices.push_back( vertex );   /// for zero
	for ( unsigned i = 1; i <= max_vertex; i++ ) {
		vertex.adjacency = new Neighbour( 0, common_tail_neighbour );  //new vertex
		vertices.push_back( vertex );
	}
	vertex.adjacency = new Neighbour( 0, common_tail_neighbour );
	vertices.push_back( vertex );  /// for max + 1, which will be used for minfill
}

void Greedy_Graph::Allocate_and_Init_Auxiliary_Memory()
{
	vertex_appeared = new bool [max_vertex + 1];
	vertex_seen = new bool [max_vertex + 1];
	for ( unsigned i = 0; i <= max_vertex; i++ ) {
		vertex_appeared[i] = false;
		vertex_seen[i] = false;
	}
}

Greedy_Graph::Greedy_Graph( unsigned max, vector<vector<unsigned>> & edges ): max_vertex( max ), free_neighbours( nullptr )
{
	assert( max + 1 == edges.size() );
	unsigned i, j;
	Allocate_and_Init_Auxiliary_Memory();
	QSorter sorter;
	common_tail_neighbour = new Neighbour( max + 1, nullptr ); // exact one dummy node whose vertex is more than max_vertex
	Vertex vertex;
	for ( i = 0; i <= max_vertex; i++ ) {
		vertex.adjacency = new Neighbour; //new vertex
		vertices.push_back( vertex );
		sorter.Sort( edges[i] );
		vertices[i].degree = edges[i].size();
		Neighbour * pre = vertices[i].adjacency;
		for ( j = 0; j < edges[i].size(); j++ ) {
			pre->next = new Neighbour;
			pre = pre->next;
			pre->vertex = edges[i][j];
		}
		pre->next = common_tail_neighbour;
	}
	vertex.adjacency = new Neighbour( 0, common_tail_neighbour );
	vertices.push_back( vertex );  /// for max + 1, which will be used for minfill
}

Greedy_Graph::~Greedy_Graph()
{
	for ( unsigned v = 0; v <= max_vertex; v++ ) {
		Neighbour * p = vertices[v].adjacency->next;
		delete vertices[v].adjacency;
		while ( p != common_tail_neighbour ) {
			Neighbour * tmp = p;
			p = p->next;
			delete tmp;
		}
	}
	delete vertices[max_vertex + 1].adjacency;
	delete common_tail_neighbour;
	while ( free_neighbours != nullptr ) {
		Neighbour * tmp = free_neighbours;
		free_neighbours = free_neighbours->next;
		delete tmp;
	}
	Free_Auxiliary_Memory();
}

void Greedy_Graph::Free_Auxiliary_Memory()
{
	delete [] vertex_appeared;
	delete [] vertex_seen;
}

void Greedy_Graph::Eliminate_Vertex( unsigned v )
{
	assert( 0 < v && v <= max_vertex );
//	vertices[v].degree = UNSIGNED_UNDEF;
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
	Remove_Vertex_Back( v );
	if ( vertices[v].infor == 0 ) {  // .infor = fill_size
		Remove_Vertex_Front( v );
		return;
	}
	for ( Neighbour * n = vertices[v].adjacency->next->next; vertices[v].infor > 0; n = n->next ) {
//		Display( cout );
//		Display_Degree( cout );
//		Display_Fill_Size( cout );
		Neighbour * m = vertices[v].adjacency->next;
		Neighbour * nn = vertices[n->vertex].adjacency->next;
		while ( m != n ) { // look for the first fill edge
			if ( m->vertex < nn->vertex ) break;
			else if ( m->vertex == nn->vertex ) {
				m = m->next;
				nn = nn->next;
			}
			else nn = nn->next;
		}
		if ( m != n ) {
			vertices[v].infor--;
			Neighbour * nn = vertices[n->vertex].adjacency->next;
			while ( nn->vertex <= max_vertex ) {
				vertex_appeared[nn->vertex] = true;
				nn = nn->next;
			}
			Neighbour * new_nn_head = Allocate_Neighbour( m->vertex, common_tail_neighbour );
			Neighbour * new_nn = new_nn_head;
			vertex_appeared[new_nn->vertex] = true;
			Neighbour * nm, * nm_pre = vertices[m->vertex].adjacency;
			unsigned num_shared = 0;
			while ( nm_pre->next->vertex < n->vertex) {
				nm_pre = nm_pre->next;
				if ( vertex_appeared[nm_pre->vertex] ) {
					vertices[nm_pre->vertex].infor--;
					num_shared++;
				}
			}
			nm = nm_pre->next;
			nm_pre->next = Allocate_Neighbour( n->vertex, nm );
			for ( ; nm->vertex <= max_vertex; nm = nm->next) {
				if ( vertex_appeared[nm->vertex] ) {
					vertices[nm->vertex].infor--;
					num_shared++;
				}
			}
			vertices[n->vertex].infor += vertices[n->vertex].degree - num_shared;
			vertices[n->vertex].degree++;
			vertices[m->vertex].infor += vertices[m->vertex].degree - num_shared;
			vertices[m->vertex].degree++;
//			Display_Fill_Size( cout );
			for ( m = m->next; vertices[v].infor > 0 && m != n; m = m->next ) {
				if ( !vertex_appeared[m->vertex] ) {
					vertices[v].infor--;
					new_nn->next = Allocate_Neighbour( m->vertex, new_nn->next );
					new_nn = new_nn->next;
					vertex_appeared[new_nn->vertex] = true;
					nm_pre = vertices[m->vertex].adjacency;
					num_shared = 0;
					while ( nm_pre->next->vertex < n->vertex) {
						nm_pre = nm_pre->next;
						if ( vertex_appeared[nm_pre->vertex] ) {
							vertices[nm_pre->vertex].infor--;
							num_shared++;
						}
					}
					nm = nm_pre->next;
					nm_pre->next = Allocate_Neighbour( n->vertex, nm );
					for ( ; nm->vertex <= max_vertex; nm = nm->next) {
						if ( vertex_appeared[nm->vertex] ) {
							vertices[nm->vertex].infor--;
							num_shared++;
						}
					}
					vertices[n->vertex].infor += vertices[n->vertex].degree - num_shared;
					vertices[n->vertex].degree++;
					vertices[m->vertex].infor += vertices[m->vertex].degree - num_shared;
					vertices[m->vertex].degree++;
//					Display_Fill_Size( cout );
				}
			}
			Neighbour * nn_pre = vertices[n->vertex].adjacency;
			do {
				while ( nn_pre->next->vertex < new_nn_head->vertex ) {
					nn_pre = nn_pre->next;
					vertex_appeared[nn_pre->vertex] = false;
				}
				nn = nn_pre->next;
				Neighbour * new_nn_pre = new_nn_head;
				vertex_appeared[new_nn_pre->vertex] = false;
				while ( new_nn_pre->next->vertex < nn->vertex ) {
					new_nn_pre = new_nn_pre->next;
					vertex_appeared[new_nn_pre->vertex] = false;
				}
				nn_pre->next = new_nn_head;
				new_nn_head = new_nn_pre->next;
				new_nn_pre->next = nn;
				nn_pre = new_nn_pre;
			} while ( new_nn_head->vertex <= max_vertex );
			for ( ; nn->vertex <= max_vertex; nn = nn->next) {
				vertex_appeared[nn->vertex] = false;
			}
		}
	}
	Remove_Vertex_Front( v );
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
}

void Greedy_Graph::Eliminate_Vertex_Opt( unsigned v )
{
	assert( v <= max_vertex );
//	vertices[v].degree = UNSIGNED_UNDEF;
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
	if ( vertices[v].infor == 0 ) {  // .infor = fill_size
		Remove_Vertex( v );
		return;
	}
	Neighbour *m, *n, *nn, *nn_pre;
	for ( n = vertices[v].adjacency->next; n->vertex <= max_vertex; n = n->next ) {
		vertex_seen[n->vertex] = true;
	}
	n = vertices[v].adjacency->next;
	nn_pre = vertices[n->vertex].adjacency;
	nn = nn_pre->next;
	while ( nn->vertex < v ) {
		vertices[n->vertex].infor -= !vertex_seen[nn->vertex];  // Preiously, v and nn->vertex are two neighbours of n->vertex which are not connected
		nn_pre = nn;
		nn = nn->next;
	}
	nn_pre->next = nn->next;
	Free_Neighbour( nn );
	nn = nn_pre->next;
	while ( nn->vertex <= max_vertex ) {
		vertices[n->vertex].infor -= !vertex_seen[nn->vertex];
		nn = nn->next;
	}
	vertices[n->vertex].degree--;
	for ( n = n->next; vertices[v].infor > 0; n = n->next ) {
		nn_pre = vertices[n->vertex].adjacency;
		nn = nn_pre->next;
		while ( nn->vertex < v ) {
			vertices[n->vertex].infor -= !vertex_seen[nn->vertex];  // Preiously, v and nn->vertex are two neighbours of n->vertex which are not connected
			vertex_appeared[nn->vertex] = true;
			nn_pre = nn;
			nn = nn->next;
		}
		nn_pre->next = nn->next;
		Free_Neighbour( nn );
		nn = nn_pre->next;
		while ( nn->vertex <= max_vertex ) {
			vertices[n->vertex].infor -= !vertex_seen[nn->vertex];
			vertex_appeared[nn->vertex] = true;
			nn = nn->next;
		}
		vertices[n->vertex].degree--;
//		Display( cout );
//		Display_Degree( cout );
//		Display_Fill_Size( cout );
		for ( m = vertices[v].adjacency->next; vertex_appeared[m->vertex]; m = m->next ); // look for the first fill edge, and vertex_appeared[n->vertex] == false
		if ( m != n ) {
			vertices[v].infor--;
			vertex_appeared[m->vertex] = true;
			Neighbour * new_nn_head = Allocate_Neighbour( m->vertex, common_tail_neighbour );
			Neighbour * new_nn = new_nn_head;
			Neighbour * nm, * nm_pre = vertices[m->vertex].adjacency;
			unsigned num_shared = 0;
			while ( nm_pre->next->vertex < n->vertex) {
				nm_pre = nm_pre->next;
				vertices[nm_pre->vertex].infor -= vertex_appeared[nm_pre->vertex];  // nm_pre->vertex is shared between the neighours of m and n
				num_shared += vertex_appeared[nm_pre->vertex];
			}
			nm = nm_pre->next;
			nm_pre->next = Allocate_Neighbour( n->vertex, nm );  // insert n into adjacency of m
			for ( ; nm->vertex <= max_vertex; nm = nm->next) {
				vertices[nm->vertex].infor -= vertex_appeared[nm->vertex];
				num_shared += vertex_appeared[nm->vertex];
			}
			vertices[n->vertex].infor += vertices[n->vertex].degree - num_shared;
			vertices[n->vertex].degree++;
			vertices[m->vertex].infor += vertices[m->vertex].degree - num_shared;
			vertices[m->vertex].degree++;
//			Display_Fill_Size( cout );
			for ( m = m->next; vertices[v].infor > 0 && m != n; m = m->next ) {
				if ( !vertex_appeared[m->vertex] ) {
					vertices[v].infor--;
					new_nn->next = Allocate_Neighbour( m->vertex, new_nn->next );
					new_nn = new_nn->next;
					vertex_appeared[new_nn->vertex] = true;
					nm_pre = vertices[m->vertex].adjacency;
					unsigned num_shared = 0;
					while ( nm_pre->next->vertex < n->vertex) {
						nm_pre = nm_pre->next;
						vertices[nm_pre->vertex].infor -= vertex_appeared[nm_pre->vertex];
						num_shared += vertex_appeared[nm_pre->vertex];
					}
					nm = nm_pre->next;
					nm_pre->next = Allocate_Neighbour( n->vertex, nm );
					for ( ; nm->vertex <= max_vertex; nm = nm->next) {
						vertices[nm->vertex].infor -= vertex_appeared[nm->vertex];
						num_shared += vertex_appeared[nm->vertex];
					}
					vertices[n->vertex].infor += vertices[n->vertex].degree - num_shared;
					vertices[n->vertex].degree++;
					vertices[m->vertex].infor += vertices[m->vertex].degree - num_shared;
					vertices[m->vertex].degree++;
//					Display_Fill_Size( cout );
				}
			}
			nn_pre = vertices[n->vertex].adjacency;
			do {  // insert new_nn into nn
				while ( nn_pre->next->vertex < new_nn_head->vertex ) {
					nn_pre = nn_pre->next;
					vertex_appeared[nn_pre->vertex] = false;
				}
				nn = nn_pre->next;
				Neighbour * new_nn_pre = new_nn_head;
				vertex_appeared[new_nn_pre->vertex] = false;
				while ( new_nn_pre->next->vertex < nn->vertex ) {
					new_nn_pre = new_nn_pre->next;
					vertex_appeared[new_nn_pre->vertex] = false;
				}
				nn_pre->next = new_nn_head;
				new_nn_head = new_nn_pre->next;
				new_nn_pre->next = nn;
				nn_pre = new_nn_pre;
			} while ( new_nn_head->vertex <= max_vertex );
		}
		else nn = vertices[n->vertex].adjacency->next;
		for ( ; nn->vertex <= max_vertex; nn = nn->next) {
			vertex_appeared[nn->vertex] = false;
		}
	}
	for ( ; n->vertex <= max_vertex; n = n->next ) {
		nn_pre = vertices[n->vertex].adjacency;
		nn = nn_pre->next;
		while ( nn->vertex < v ) {
			vertices[n->vertex].infor -= !vertex_seen[nn->vertex];  // Preiously, v and nn->vertex are two neighbours of n->vertex which are not connected
			nn_pre = nn;
			nn = nn->next;
		}
		nn_pre->next = nn->next;
		Free_Neighbour( nn );
		nn = nn_pre->next;
		while ( nn->vertex <= max_vertex ) {
			vertices[n->vertex].infor -= !vertex_seen[nn->vertex];
			nn = nn->next;
		}
		vertices[n->vertex].degree--;
	}
	n = vertices[v].adjacency->next;
	vertices[v].adjacency->next = common_tail_neighbour;
	vertices[v].degree = UNSIGNED_UNDEF;
	while ( n->vertex <= max_vertex ) {
		vertex_seen[n->vertex] = false;
		Neighbour * tmp = n;
		n = n->next;
		Free_Neighbour( tmp ); // Remove the neighbour of v
	}
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
}

void Greedy_Graph::Eliminate_Vertex_No_Infor( unsigned v )
{
	assert( 0 < v && v <= max_vertex );
//	vertices[v].degree = UNSIGNED_UNDEF;
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
	Remove_Vertex_Back( v );
	if ( vertices[v].degree < 2 ) {
		Remove_Vertex_Front( v );
		return;
	}
	for ( Neighbour * n = vertices[v].adjacency->next->next; n->vertex <= max_vertex; n = n->next ) {
//		Display( cout );
//		Display_Degree( cout );
		Neighbour * m = vertices[v].adjacency->next;
		Neighbour * nn = vertices[n->vertex].adjacency->next;
		while ( m != n ) { // look for the first fill edge
			if ( m->vertex < nn->vertex ) break;
			else if ( m->vertex == nn->vertex ) {
				m = m->next;
				nn = nn->next;
			}
			else nn = nn->next;
		}
		if ( m != n ) {
			Neighbour * nn = vertices[n->vertex].adjacency->next;
			while ( nn->vertex <= max_vertex ) {
				vertex_appeared[nn->vertex] = true;
				nn = nn->next;
			}
			Neighbour * new_nn_head = Allocate_Neighbour( m->vertex, common_tail_neighbour );
			Neighbour * new_nn = new_nn_head;
			vertex_appeared[new_nn->vertex] = true;
			Neighbour * nm, * nm_pre = vertices[m->vertex].adjacency;
			for ( nm_pre = vertices[m->vertex].adjacency; nm_pre->next->vertex < n->vertex; nm_pre = nm_pre->next );
			nm = nm_pre->next;
			nm_pre->next = Allocate_Neighbour( n->vertex, nm );
			vertices[n->vertex].degree++;
			vertices[m->vertex].degree++;
			for ( m = m->next; m != n; m = m->next ) {
				if ( !vertex_appeared[m->vertex] ) {
					new_nn->next = Allocate_Neighbour( m->vertex, new_nn->next );
					new_nn = new_nn->next;
					vertex_appeared[new_nn->vertex] = true;
					nm_pre = vertices[m->vertex].adjacency;
					for ( ; nm_pre->next->vertex < n->vertex; nm_pre = nm_pre->next );
					nm = nm_pre->next;
					nm_pre->next = Allocate_Neighbour( n->vertex, nm );
					vertices[n->vertex].degree++;
					vertices[m->vertex].degree++;
				}
			}
			Neighbour * nn_pre = vertices[n->vertex].adjacency;
			do {
				while ( nn_pre->next->vertex < new_nn_head->vertex ) {
					nn_pre = nn_pre->next;
					vertex_appeared[nn_pre->vertex] = false;
				}
				nn = nn_pre->next;
				Neighbour * new_nn_pre = new_nn_head;
				vertex_appeared[new_nn_pre->vertex] = false;
				while ( new_nn_pre->next->vertex < nn->vertex ) {
					new_nn_pre = new_nn_pre->next;
					vertex_appeared[new_nn_pre->vertex] = false;
				}
				nn_pre->next = new_nn_head;
				new_nn_head = new_nn_pre->next;
				new_nn_pre->next = nn;
				nn_pre = new_nn_pre;
			} while ( new_nn_head->vertex <= max_vertex );
			for ( ; nn->vertex <= max_vertex; nn = nn->next) {
				vertex_appeared[nn->vertex] = false;
			}
		}
	}
	Remove_Vertex_Front( v );
//	Display( cout );
//	Display_Degree( cout );
//	Display_Fill_Size( cout );
}

void Greedy_Graph::Eliminate_Vertex_Naive( unsigned v )
{
	assert( 0 < v && v <= max_vertex );
	for ( Neighbour * p = vertices[v].adjacency->next; p->vertex <= max_vertex; p = p->next ) {
		for ( Neighbour * q = p->next; q->vertex <= max_vertex; q = q->next ) {
			Add_Edge_Naive( p->vertex, q->vertex );
		}
	}
	Remove_Vertex_Naive( v );
}

void Greedy_Graph::Induced_Order_Min_Fill_Opt( unsigned * chain )
{
//	Display( cout );
	for ( unsigned i = 0; i <= max_vertex; i++ ) {
		Fill_Size_Opt( i );
	}
	for ( unsigned i = 0; i < max_vertex; i++ ) {
		Verify_Fill_Size();  // ToRemove
		vector<Vertex>::iterator begin = vertices.begin();
		vector<Vertex>::iterator itr = begin;
		while ( itr->degree == UNSIGNED_UNDEF ) itr++;
		unsigned min_fill_var = itr - begin;
		vector<Vertex>::iterator end = vertices.end() - 1;  // the last node is invalid
		for ( itr++; itr < end; itr++ ) {
			if ( itr->degree == UNSIGNED_UNDEF ) continue;
			if ( vertices[itr - begin].infor < vertices[min_fill_var].infor ) {
				min_fill_var = itr - begin;
			}
		}
//		cout << min_fill_var << ": " << gp->vertices[min_fill_var].degree << " vs "<< gp->vertices[min_fill_var].infor << endl;
		chain[i] = min_fill_var;
		Eliminate_Vertex_Opt( min_fill_var );
//		gp->Display( cout );
	}
}

unsigned Greedy_Graph::Induced_Width_Min_Fill_Opt()
{
	unsigned i;
	for ( i = 0; i <= max_vertex; i++ ) {
		Fill_Size_Opt( i );
	}
	unsigned width, inducedwidth = 0;
	vector<Vertex>::iterator begin = vertices.begin();
	vector<Vertex>::iterator end = vertices.end() - 1;  // the last node is invalid
	for ( i = 0; true; i++ ) {
		Verify_Fill_Size();  // ToRemove
		while ( begin->degree == UNSIGNED_UNDEF ) begin++;
		vector<Vertex>::iterator itr = begin;
		unsigned min_fill_vertex = itr - vertices.begin();
		for ( itr++; itr < end; itr++ ) {
			if ( itr->degree == UNSIGNED_UNDEF ) continue;
			if ( vertices[itr - vertices.begin()].infor < vertices[min_fill_vertex].infor ) {
				min_fill_vertex = itr - vertices.begin();
			}
		}
		width = vertices[min_fill_vertex].degree + 1;
		if ( width > inducedwidth ) inducedwidth = width;
		if ( width >= max_vertex - i ) break;
		Eliminate_Vertex_Opt( min_fill_vertex );
		cerr << min_fill_vertex << " ";  // ToRemove
	}
	cerr << endl;  // ToRemove
	return inducedwidth;
}

unsigned Greedy_Graph::Induced_Width_Min_Fill_Bound( unsigned bound )
{
	unsigned i, width, inducedwidth = max_vertex;
	for ( i = 0; i <= max_vertex; i++ ) {
		width = vertices[i].degree;
		if ( width < inducedwidth ) inducedwidth = width;
	}
	if ( inducedwidth > bound ) return inducedwidth;  // inducedwidth is not less than the minimum degree + 1
	for ( i = 0; i <= max_vertex; i++ ) {
		Fill_Size_Opt( i );
	}
	vector<Vertex>::iterator begin = vertices.begin();
	vector<Vertex>::iterator end = vertices.end() - 1;  // the last node is invalid
	for ( i = 0; true; i++ ) {
		while ( begin->degree == UNSIGNED_UNDEF ) begin++;
		vector<Vertex>::iterator itr = begin;
		unsigned min_fill_vertex = itr - vertices.begin();
		for ( itr++; itr < end; itr++ ) {
			if ( itr->degree == UNSIGNED_UNDEF ) continue;
			if ( vertices[itr - vertices.begin()].infor < vertices[min_fill_vertex].infor ) {
				min_fill_vertex = itr - vertices.begin();
			}
		}
		width = vertices[min_fill_vertex].degree;
		if ( width > inducedwidth ) inducedwidth = width;
		if ( inducedwidth > bound || inducedwidth >= max_vertex - i ) break;  /// inducedwidth + 1 >= ( max_vertex + 1 ) - i
		Eliminate_Vertex_Opt( min_fill_vertex );
	}
	return inducedwidth;
}

void Greedy_Graph::Display( ostream & out)
{
	out << "Vertices:";
	unsigned last = UNSIGNED_UNDEF;
	for ( unsigned v = 0; v <= max_vertex; v++ ) {
		if ( vertices[v].degree != UNSIGNED_UNDEF ) last = v;
	}
	if ( last != UNSIGNED_UNDEF ) {
		for ( unsigned v = 0; v < last; v++ ) {
			if ( vertices[v].degree != UNSIGNED_UNDEF ) out << " " << v << ',';
		}
		out << " " << last;
	}
	out << endl
		<< "Edges:" << endl;
	for ( unsigned v = 0; v <= max_vertex; v++ ) {
		if ( vertices[v].degree == UNSIGNED_UNDEF ) continue;
		out << v << ":";
		Neighbour * p = vertices[v].adjacency->next;
		while ( p->vertex <= max_vertex ) {
			out << ' ' << p->vertex;
			out << ',';
			p = p->next;
		}
		if ( vertices[v].adjacency->next != common_tail_neighbour ) out << char( 8 ) << ';';
		out << endl;
	}
	out << "End." << endl;
}

void Greedy_Graph::Display_Degree( ostream & fout)
{
	fout << "Degree:" << endl;
	for ( unsigned v = 0; v <= max_vertex; v++ ) {
		if ( vertices[v].degree == UNSIGNED_UNDEF ) continue;
		fout << v << ": " << vertices[v].degree << endl;
	}
}

void Greedy_Graph::Display_Fill_Size( ostream & fout)
{
	fout << "Fill size:" << endl;
	for ( unsigned v = 0; v <= max_vertex; v++ ) {
		if ( vertices[v].degree == UNSIGNED_UNDEF ) continue;
		fout << v << ": " << vertices[v].infor << endl;
	}
}

//====================================================================================================

Simple_TreeD::Simple_TreeD( Greedy_Graph & graph ): _max_vertex( graph.Max_Vertex() ), _clusters( 2 )
{
	Allocate_and_Init_Auxiliary_Memory();
	Generate_Clusters( graph );
}

void Simple_TreeD::Allocate_and_Init_Auxiliary_Memory()
{
	_vertex_weight = new double [_max_vertex + 1];
}

void Simple_TreeD::Free_Auxiliary_Memory()
{
	delete [] _vertex_weight;
}

void Simple_TreeD::Generate_Clusters( Greedy_Graph & graph )
{
	unsigned min_fill_var;
	for ( unsigned i = 0; i <= _max_vertex; i++ ) {
		graph.Fill_Size_Opt( i );
	}
//	graph.Display( cout );
	vector<Simple_TreeD_Cluster> tmp_clusters;
	SList<unsigned> left_vertices;
	unsigned num_left_vertices = 0;
	SList_Node<unsigned> * pre = left_vertices.Head();
	vector<Vertex>::iterator vbegin = graph.vertices.begin();
	vector<Vertex>::iterator vend = graph.vertices.end() - 1;  // the last node is invalid
	for ( vector<Vertex>::iterator itr = vbegin; itr < vend; itr++ ) {
		unsigned var = itr - vbegin;
		if ( itr->degree == UNSIGNED_UNDEF ) continue;
		if ( graph.vertices[var].degree == 0 ) {  // old version: if ( graph.vertices[var].infor == 0 ) {  // ToModify: bug for 0-fill but not simplified
			graph.Remove_Vertex( var );
			continue;
		}
		left_vertices.Insert_After( pre, var );
		pre = pre->next;
		num_left_vertices++;
	}
	if ( num_left_vertices == 0 ) {
        Simple_TreeD_Cluster first_cluster;
        first_cluster.vars = new unsigned [1];
        first_cluster.num_vars = 1;
        first_cluster.vars[0] = 1;
        Add_First_Cluster( first_cluster );
        return;
	}
	for ( unsigned i = 0; true; i++ ) {
//		graph.Validate_Fill_Size();
		SList_Node<unsigned> * min_fill_pre = left_vertices.Head();
		min_fill_var = min_fill_pre->next->data;
		for ( pre = min_fill_pre->next; pre->next != nullptr; pre = pre->next ) {
			unsigned var = pre->next->data;
			if ( graph.vertices[var].infor < graph.vertices[min_fill_var].infor ) {
				min_fill_pre = pre;
				min_fill_var = var;
			}
		}
		left_vertices.Delete_After( min_fill_pre );
//		cout << min_fill_var << ": " << graph.vertices[min_fill_var].degree << " vs "<< graph.vertices[min_fill_var].infor << endl;
		if ( graph.vertices[min_fill_var].degree + 1 >= num_left_vertices - i ) break;  /// rest of the vertices _max_vertex + 1 - i is not greater than the current cluster degree + 1
		Simple_TreeD_Cluster cluster;
		cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
		cluster.num_vars = 0;
		Neighbour * p;
		for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		cluster.infor = cluster.num_vars;  /// record the position of min_fill_var
		cluster.vars[cluster.num_vars++] = min_fill_var;
		for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		tmp_clusters.push_back( cluster );
		graph.Eliminate_Vertex_Opt( min_fill_var );
//		graph.Display( cout );
	}
	Simple_TreeD_Cluster first_cluster;
	first_cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
	first_cluster.num_vars = 0;
	Neighbour * p;
	for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
		first_cluster.vars[first_cluster.num_vars++] = p->vertex;
	}
	first_cluster.vars[first_cluster.num_vars++] = min_fill_var;
	for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
		first_cluster.vars[first_cluster.num_vars++] = p->vertex;
	}
	Add_First_Cluster( first_cluster );
	for ( unsigned i = tmp_clusters.size() - 1; i != UNSIGNED_UNDEF; i-- ) {
//		Display( cout, cnf );
		vector<Simple_TreeD_Cluster>::iterator begin = _clusters.begin(), itr = begin;
		for ( ; !tmp_clusters[i].Subset_Except_One_Var( tmp_clusters[i].infor, *itr ); itr++ );
		if ( itr->num_vars == tmp_clusters[i].num_vars - 1 ) {
			delete [] itr->vars;
			itr->num_vars = tmp_clusters[i].num_vars;
			itr->vars = tmp_clusters[i].vars;
		}
		else Add_Cluster( tmp_clusters[i], itr - begin );
	}
}

Simple_TreeD::Simple_TreeD( Greedy_Graph & graph, unsigned bound ): _max_vertex( graph.Max_Vertex() ), _clusters( 2 )
{
	Allocate_and_Init_Auxiliary_Memory();
	unsigned min_fill_var;
//	graph.Display( cout );
	for ( unsigned i = 0; i <= _max_vertex; i++ ) {
		graph.Fill_Size_Opt( i );
	}
//	graph.Display( cout );
	vector<Simple_TreeD_Cluster> tmp_clusters;
	for ( unsigned i = 0; true; i++ ) {
//		graph.Validate_Fill_Size();
		vector<Vertex>::iterator begin = graph.vertices.begin();
		vector<Vertex>::iterator itr = begin;
		while ( itr->degree == UNSIGNED_UNDEF ) itr++;
		min_fill_var = itr - begin;
		vector<Vertex>::iterator end = graph.vertices.end() - 1;  // the last node is invalid
		for ( itr++; itr < end; itr++ ) {
			if ( itr->degree == UNSIGNED_UNDEF ) continue;
			if ( graph.vertices[itr - begin].infor < graph.vertices[min_fill_var].infor ) {
				min_fill_var = itr - begin;
			}
		}
//		cout << min_fill_var << ": " << graph.vertices[min_fill_var].degree << " vs "<< graph.vertices[min_fill_var].infor << endl;
		if ( graph.vertices[min_fill_var].degree > bound ) {  /// exceed bound
			Generate_Singleton_Cluster();
			for ( i = tmp_clusters.size() - 1; i != UNSIGNED_UNDEF; i-- ) {
				delete [] tmp_clusters[i].vars;
			}
			return;
		}
		if ( graph.vertices[min_fill_var].degree >= _max_vertex - i ) break;  /// rest of the vertices _max_vertex + 1 - i is not greater than the current cluster degree + 1
		Simple_TreeD_Cluster cluster;
		cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
		cluster.num_vars = 0;
		Neighbour * p;
		for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		cluster.infor = cluster.num_vars;  /// record the position of min_fill_var
		cluster.vars[cluster.num_vars++] = min_fill_var;
		for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		tmp_clusters.push_back( cluster );
		graph.Eliminate_Vertex_Opt( min_fill_var );
//		graph.Display( cout );
	}
	Simple_TreeD_Cluster cluster;
	cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
	cluster.num_vars = 0;
	Neighbour * p;
	for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
		cluster.vars[cluster.num_vars++] = p->vertex;
	}
	cluster.vars[cluster.num_vars++] = min_fill_var;
	for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
		cluster.vars[cluster.num_vars++] = p->vertex;
	}
	Add_First_Cluster( cluster );
	for ( unsigned i = tmp_clusters.size() - 1; i != UNSIGNED_UNDEF; i-- ) {
//		Display( cout, cnf );
		vector<Simple_TreeD_Cluster>::iterator begin = _clusters.begin(), itr = begin;
		for ( ; !tmp_clusters[i].Subset_Except_One_Var( tmp_clusters[i].infor, *itr ); itr++ );
		if ( itr->num_vars == tmp_clusters[i].num_vars - 1 ) {
			delete [] itr->vars;
			itr->num_vars = tmp_clusters[i].num_vars;
			itr->vars = tmp_clusters[i].vars;
		}
		else Add_Cluster( tmp_clusters[i], itr - begin );
	}
}

void Simple_TreeD::Generate_Singleton_Cluster()
{
	Simple_TreeD_Cluster cluster;
	cluster.vars = new unsigned [_max_vertex + 1];
	for ( cluster.num_vars = 0; cluster.num_vars <= _max_vertex; cluster.num_vars++ ) {
		cluster.vars[cluster.num_vars] = cluster.num_vars;
	}
	Add_First_Cluster( cluster );
}

Simple_TreeD::Simple_TreeD( Greedy_Graph & graph, unsigned bound, bool opt ): _max_vertex( graph.Max_Vertex() ), _clusters( 2 )  /// use SList optimize it
{
	assert( opt == true );  /// use SList optimize it
	Allocate_and_Init_Auxiliary_Memory();
	unsigned min_fill_var;
	for ( unsigned i = 0; i <= _max_vertex; i++ ) {
		graph.Fill_Size_Opt( i );
	}
//	graph.Display( cout );
	vector<Simple_TreeD_Cluster> tmp_clusters;
	SList<unsigned> left_vertices;
	unsigned num_left_vertices = 0;
	SList_Node<unsigned> * pre = left_vertices.Head();
	vector<Vertex>::iterator vbegin = graph.vertices.begin();
	vector<Vertex>::iterator vend = graph.vertices.end() - 1;  // the last node is invalid
	for ( vector<Vertex>::iterator itr = vbegin; itr < vend; itr++ ) {
		unsigned var = itr - vbegin;
		if ( itr->degree == UNSIGNED_UNDEF ) continue;
		if ( graph.vertices[var].degree == 0 ) {  // old version: if ( graph.vertices[var].infor == 0 ) {  // ToModify: bug for 0-fill but not simplified
			graph.Remove_Vertex( var );
			continue;
		}
		left_vertices.Insert_After( pre, var );
		pre = pre->next;
		num_left_vertices++;
	}
	if ( num_left_vertices == 0 ) {
        Simple_TreeD_Cluster first_cluster;
        first_cluster.vars = new unsigned [1];
        first_cluster.num_vars = 1;
        first_cluster.vars[0] = 1;
        Add_First_Cluster( first_cluster );
        return;
	}
	for ( unsigned i = 0; true; i++ ) {
//		graph.Validate_Fill_Size();
		SList_Node<unsigned> * min_fill_pre = left_vertices.Head();
		min_fill_var = min_fill_pre->next->data;
		for ( pre = min_fill_pre->next; pre->next != nullptr; pre = pre->next ) {
			unsigned var = pre->next->data;
			if ( graph.vertices[var].infor < graph.vertices[min_fill_var].infor ) {
				min_fill_pre = pre;
				min_fill_var = var;
			}
		}
		left_vertices.Delete_After( min_fill_pre );
//		cout << min_fill_var << ": " << graph.vertices[min_fill_var].degree << " vs "<< graph.vertices[min_fill_var].infor << endl;
		if ( graph.vertices[min_fill_var].degree > bound ) {  /// exceed bound
			Generate_Singleton_Cluster();
			for ( i = tmp_clusters.size() - 1; i != UNSIGNED_UNDEF; i-- ) {
				delete [] tmp_clusters[i].vars;
			}
			return;
		}
		if ( graph.vertices[min_fill_var].degree + 1 >= num_left_vertices - i ) break;  /// rest of the vertices _max_vertex + 1 - i is not greater than the current cluster degree + 1
		Simple_TreeD_Cluster cluster;
		cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
		cluster.num_vars = 0;
		Neighbour * p;
		for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		cluster.infor = cluster.num_vars;  /// record the position of min_fill_var
		cluster.vars[cluster.num_vars++] = min_fill_var;
		for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
			cluster.vars[cluster.num_vars++] = p->vertex;
		}
		tmp_clusters.push_back( cluster );
		graph.Eliminate_Vertex_Opt( min_fill_var );
//		graph.Display( cout );
	}
	Simple_TreeD_Cluster first_cluster;
	first_cluster.vars = new unsigned [graph.vertices[min_fill_var].degree + 1];
	first_cluster.num_vars = 0;
	Neighbour * p;
	for ( p = graph.vertices[min_fill_var].adjacency->next; p->vertex < min_fill_var; p = p->next ) {
		first_cluster.vars[first_cluster.num_vars++] = p->vertex;
	}
	first_cluster.vars[first_cluster.num_vars++] = min_fill_var;
	for ( ; p->vertex <= graph.max_vertex; p = p->next ) {
		first_cluster.vars[first_cluster.num_vars++] = p->vertex;
	}
	Add_First_Cluster( first_cluster );
	for ( unsigned i = tmp_clusters.size() - 1; i != UNSIGNED_UNDEF; i-- ) {
//		Display( cout, cnf );
		vector<Simple_TreeD_Cluster>::iterator begin = _clusters.begin(), itr = begin;
		for ( ; !tmp_clusters[i].Subset_Except_One_Var( tmp_clusters[i].infor, *itr ); itr++ );
		if ( itr->num_vars == tmp_clusters[i].num_vars - 1 ) {
			delete [] itr->vars;
			itr->num_vars = tmp_clusters[i].num_vars;
			itr->vars = tmp_clusters[i].vars;
		}
		else Add_Cluster( tmp_clusters[i], itr - begin );
	}
}

Simple_TreeD::~Simple_TreeD()
{
	unsigned cluster_size = _clusters.size() - 1;
	TreeD_Cluster_Adjacency * tail = _clusters[cluster_size].adj->next;
	vector<Simple_TreeD_Cluster>::iterator itr = _clusters.begin();
	vector<Simple_TreeD_Cluster>::iterator end = _clusters.end() - 1;
	for ( ; itr < end; itr++ ) {
		delete [] itr->vars;
		TreeD_Cluster_Adjacency * p = itr->adj;
		while ( p != tail ) {
			TreeD_Cluster_Adjacency * tmp = p;
			if ( p->sep != nullptr ) delete [] p->sep;
			p = p->next;
			delete tmp;
		}
	}
	delete end->adj;
	delete tail;
	Free_Auxiliary_Memory();
}

void Simple_TreeD::Add_First_Cluster( Simple_TreeD_Cluster & cluster )
{
	assert( cluster.adj == nullptr );
	TreeD_Cluster_Adjacency * tail = new TreeD_Cluster_Adjacency( 2, nullptr ); // exact one dummy node shared by all clusters
	_clusters[0].vars = cluster.vars;
	_clusters[0].num_vars = cluster.num_vars;
	_clusters[0].adj = new TreeD_Cluster_Adjacency( 0, tail );
	_clusters[0].degree = 0;
	_clusters[0].infor = UNSIGNED_UNDEF;
	_clusters[1].adj = new TreeD_Cluster_Adjacency( 0, tail );
	_clusters[1].degree = 0;
	_clusters[1].infor = UNSIGNED_UNDEF;
}

void Simple_TreeD::Add_Cluster( Simple_TreeD_Cluster & cluster, unsigned neighbour )
{
	unsigned old_size = _clusters.size() - 1;
	TreeD_Cluster_Adjacency * tail =  _clusters[old_size].adj->next;
	tail->ordinal++;
	_clusters[old_size].vars = cluster.vars;
	_clusters[old_size].num_vars = cluster.num_vars;
	_clusters[old_size].adj->next = new TreeD_Cluster_Adjacency( neighbour, tail );
	_clusters[old_size].degree = 1;
	Simple_TreeD_Cluster tmp_cluster( tail );
	_clusters.push_back( tmp_cluster );
	TreeD_Cluster_Adjacency * pre = _clusters[neighbour].adj;
	TreeD_Cluster_Adjacency * p = pre->next;
	while ( p->ordinal < old_size ) {
		pre = p;
		p = p->next;
	}
	pre->next = new TreeD_Cluster_Adjacency( old_size, p );
	_clusters[neighbour].degree++;
}

void Simple_TreeD::Compute_All_Separators()
{
	unsigned i, j;
	vector<unsigned> many_variables( _max_vertex + 1 );
	vector<bool> var_seen( _max_vertex + 1, false );
	vector<Simple_TreeD_Cluster>::iterator itr = _clusters.begin(), end = _clusters.end() - 1;
	unsigned cluster_size = end - itr;
	for ( ; itr < end; itr++ ) {
		for ( i = 0; i < itr->num_vars; i++ ) var_seen[itr->vars[i]] = true;
		TreeD_Cluster_Adjacency * adj = itr->adj->next;
		for ( ; adj->ordinal < cluster_size; adj = adj->next ) {
			for ( j = 0; j < _clusters[adj->ordinal].num_vars; j++ ) {
				if ( var_seen[_clusters[adj->ordinal].vars[j]] ) {
					many_variables[adj->sep_size++] = _clusters[adj->ordinal].vars[j];
				}
			}
			adj->sep = new unsigned [adj->sep_size];
			for ( j = 0; j < adj->sep_size; j++ ) {
				adj->sep[j] = many_variables[j];
			}
		}
		for ( i = 0; i < itr->num_vars; i++ ) var_seen[itr->vars[i]] = false;
	}
}

Chain Simple_TreeD::Transform_Chain( double * weight )
{
	unsigned i;
	unsigned cluster_size = _clusters.size() - 1;
	for ( i = 0; i <= _max_vertex; i++ ) {
		_vertex_weight[i] = weight[i];
	}
	Chain chain( _max_vertex );
	if ( cluster_size == 1 ) {
		chain.Append( _clusters[0].vars, _clusters[0].num_vars );
		chain.Sort_Reverse( 0, chain.Size(), _vertex_weight );
	}
	Compute_All_Separators();
	unsigned root;
	if ( Width() < 200 ) root = Compute_Root_Lowest_Weighted_Depth_Reserved();  // ToModify
	else {
		root = cluster_size - 1;  // the first minfill cluster with minimum width
		Compute_Fixed_Root_Weight_Reserved( root );  /// Compute_Root_Lowest_Weighted_Depth_Reserved trends to reduce the height of tree decomposition, but often begins with a big cluster
	}
	TreeD_Cluster_Adjacency * adj;
	unsigned old_chain_size;
	unsigned * c_stack = new unsigned [cluster_size];
	unsigned num_c_stack = 0;
	adj = Search_First_Seen_Neighbour( _clusters[root].adj->next );
	for ( ; adj->ordinal < cluster_size; adj = Search_First_Seen_Neighbour( adj ) ) {
		TreeD_Cluster_Adjacency * max_adj = Pick_Preferred_Neighbour( adj, chain );
		max_adj->infor = 0;  // this neighbour is picked
		c_stack[num_c_stack++] = max_adj->ordinal;
		old_chain_size = chain.Size();
		chain.Append( max_adj->sep, max_adj->sep_size );
		chain.Sort_Reverse( old_chain_size, chain.Size(), _vertex_weight );
//		for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//		cout << endl;
	}
	old_chain_size = chain.Size();
	chain.Append( _clusters[root].vars, _clusters[root].num_vars );
	chain.Sort_Reverse( old_chain_size, chain.Size(), _vertex_weight );
	_clusters[root].infor = 0;
//	for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//	cout << endl;
	while ( num_c_stack-- ) {
		unsigned top = c_stack[num_c_stack];
		adj = Search_First_Seen_Neighbour( _clusters[top].adj->next );
		for ( ; adj->ordinal < cluster_size; adj = Search_First_Seen_Neighbour( adj ) ) {
			TreeD_Cluster_Adjacency * max_adj = Pick_Preferred_Neighbour( adj, chain );
			max_adj->infor = 0;
			c_stack[num_c_stack++] = max_adj->ordinal;
			old_chain_size = chain.Size();
			chain.Append( max_adj->sep, max_adj->sep_size );
			chain.Sort_Reverse( old_chain_size, chain.Size(), _vertex_weight );
//			for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//			cout << endl;
		}
		old_chain_size = chain.Size();
		chain.Append( _clusters[top].vars, _clusters[top].num_vars );
		chain.Sort_Reverse( old_chain_size, chain.Size(), _vertex_weight );
		_clusters[top].infor = 0;
//		for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//		cout << endl;
	}
	for ( i = 0; i <= _max_vertex; i++ ) {
		chain.Append( i );
	}
	for ( i = 0; i < cluster_size; i++ ) {
		_clusters[i].infor = UNSIGNED_UNDEF;
		for ( adj = _clusters[i].adj->next; adj->ordinal < cluster_size; adj = adj->next ) adj->infor = UNSIGNED_UNDEF;
	}
	delete [] c_stack;
	return chain;
}

unsigned Simple_TreeD::Compute_Root_Lowest_Weighted_Depth_Reserved()  // NOTE: _clusters[i].infor is reserved when return
{
	unsigned cluster_size = _clusters.size() - 1;
	_clusters[0].infor = 0;
	if ( cluster_size == 1 ) return 0;
	TreeD_Cluster_Adjacency * adj = _clusters[0].adj->next;
	unsigned * c_stack = new unsigned [cluster_size]; // c denotes cluster
	c_stack[0] = adj->ordinal;
	unsigned num_c_stack = 1;
	for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
		c_stack[num_c_stack++] = adj->ordinal;
	}
	while ( num_c_stack ) {
		unsigned top = c_stack[num_c_stack - 1];
		if ( _clusters[top].infor == UNSIGNED_UNDEF ) { // "UNSIGNED_UNDEF - 1" denotes "visited" but its children is unvisited yet
			if ( _clusters[top].degree == 1 ) {
				_clusters[top].infor = _clusters[top].num_vars - _clusters[top].adj->next->sep_size;
				num_c_stack--;
			}
			else {
				adj = _clusters[top].adj->next;
				for ( ; _clusters[adj->ordinal].infor == UNSIGNED_UNDEF; adj = adj->next ) {
					c_stack[num_c_stack++] = adj->ordinal;
				}
				for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
					c_stack[num_c_stack++] = adj->ordinal;
				}
				_clusters[top].infor = 0;
			}
		}
		else {
			/* NOTE:
			* _clusters[top].infor is already equal to 0;
			* we suppose that the treed is minimal, and thus there is exactly one neighbour satisfies _clusters[adj->ordinal].infor == 0
			*/
			for ( adj = _clusters[top].adj->next; _clusters[adj->ordinal].infor != 0; adj = adj->next ) {
				_clusters[top].infor += _clusters[adj->ordinal].infor;
			}
			_clusters[top].infor += _clusters[top].num_vars - adj->sep_size;
			for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
				_clusters[top].infor += _clusters[adj->ordinal].infor;
			}
//			cout << top << ": " << _clusters[top].infor << endl;
			num_c_stack--;
		}
	}
	unsigned root = 0;
	while ( true ) {
		adj = _clusters[root].adj->next;
		unsigned sum = _clusters[adj->ordinal].infor;
		unsigned max = _clusters[adj->ordinal].infor;
		TreeD_Cluster_Adjacency * pos = adj;
		for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
			sum += _clusters[adj->ordinal].infor;
			if ( max < _clusters[adj->ordinal].infor ) {
				max = _clusters[adj->ordinal].infor;
				pos = adj;
			}
		}
		sum += _clusters[root].num_vars - pos->sep_size - max;
		if ( sum < max ) {
			_clusters[root].infor = sum;
			root = pos->ordinal;
		}
		else break;
	}
	delete [] c_stack;
	return root;
}

void Simple_TreeD::Compute_Fixed_Root_Weight_Reserved( unsigned root )  // NOTE: _clusters[i].infor is reserved when return
{
	unsigned cluster_size = _clusters.size() - 1;
	assert( root < cluster_size );
	_clusters[root].infor = 0;
	if ( cluster_size == 1 ) return;
	TreeD_Cluster_Adjacency * adj = _clusters[root].adj->next;
	unsigned * c_stack = new unsigned [cluster_size]; // c denotes cluster
	c_stack[0] = adj->ordinal;
	unsigned num_c_stack = 1;
	for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
		c_stack[num_c_stack++] = adj->ordinal;
	}
	while ( num_c_stack ) {
		unsigned top = c_stack[num_c_stack - 1];
		if ( _clusters[top].infor == UNSIGNED_UNDEF ) { // "UNSIGNED_UNDEF - 1" denotes "visited" but its children is unvisited yet
			if ( _clusters[top].degree == 1 ) {
				_clusters[top].infor = _clusters[top].num_vars - _clusters[top].adj->next->sep_size;
				num_c_stack--;
			}
			else {
				adj = _clusters[top].adj->next;
				for ( ; _clusters[adj->ordinal].infor == UNSIGNED_UNDEF; adj = adj->next ) {
					c_stack[num_c_stack++] = adj->ordinal;
				}
				for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
					c_stack[num_c_stack++] = adj->ordinal;
				}
				_clusters[top].infor = 0;
			}
		}
		else {
			/* NOTE:
			* _clusters[top].infor is already equal to 0;
			* we suppose that the treed is minimal, and thus there is exactly one neighbour satisfies _clusters[adj->ordinal].infor == 0
			*/
			for ( adj = _clusters[top].adj->next; _clusters[adj->ordinal].infor != 0; adj = adj->next ) {
				_clusters[top].infor += _clusters[adj->ordinal].infor;
			}
			_clusters[top].infor += _clusters[top].num_vars - adj->sep_size;
			for ( adj = adj->next; adj->ordinal < cluster_size; adj = adj->next ) {
				_clusters[top].infor += _clusters[adj->ordinal].infor;
			}
//			cout << top << ": " << _clusters[top].infor << endl;
			num_c_stack--;
		}
	}
	delete [] c_stack;
}

TreeD_Cluster_Adjacency * Simple_TreeD::Search_First_Seen_Neighbour( TreeD_Cluster_Adjacency * head )
{
	unsigned cluster_size = _clusters.size() - 1;
	for ( ; head->ordinal < cluster_size; head = head->next ) {
		if ( _clusters[head->ordinal].infor == 0 ) continue;
		if ( head->infor ) break;
	}
	return head;
}

TreeD_Cluster_Adjacency * Simple_TreeD::Pick_Preferred_Neighbour( TreeD_Cluster_Adjacency * head, Chain & chain )
{
	unsigned i, num;
	unsigned cluster_size = _clusters.size() - 1;
	TreeD_Cluster_Adjacency * adj;
	double max_weight = 0;
	TreeD_Cluster_Adjacency * max_adj = head;
	for ( i = num = 0; i < head->sep_size; i++ ) {
		if ( !chain.Contain( head->sep[i] ) ) {
			max_weight += _vertex_weight[head->sep[i]];
			num++;
		}
	}
	if ( num == 0 ) return head;
	max_weight = max_weight / num + 1.0 * ( _clusters[head->ordinal].infor - num ) / _max_vertex;  // Currently, _clusters[head->ordinal].infor is the number of variables in sub-tree rooted at head->ordinal
	for ( adj = head->next; adj->ordinal < cluster_size; adj = adj->next ) {
		if ( _clusters[adj->ordinal].infor == 0 || adj->infor == 0 ) continue;
		double weight = 0;
		for ( i = num = 0; i < adj->sep_size; i++ ) {
			if ( !chain.Contain( adj->sep[i] ) ) {
				weight += _vertex_weight[adj->sep[i]];
				num++;
			}
		}
		if ( num > 0 ) {
			weight = weight / num + 1.0 * ( _clusters[adj->ordinal].infor - num ) / _max_vertex;
			if ( weight > max_weight ) {
				max_weight = weight;
				max_adj = adj;
			}
		}
		else return adj;
	}
	return max_adj;
}

void Simple_TreeD::Compute_DTree_Scores( double * scores )
{
	unsigned i;
	unsigned cluster_size = _clusters.size() - 1;
	for ( i = 0; i <= _max_vertex; i++ ) {
		_vertex_weight[i] = scores[i];
		scores[i] = 0;
	}
	Chain chain( _max_vertex );
	if ( cluster_size == 1 ) {
		for ( unsigned i = 0; i < _clusters[0].num_vars; i++ ) {
			unsigned var = _clusters[0].vars[i];
			scores[var] = 1;
		}
		return;
	}
	unsigned index = 1;
	Compute_All_Separators();
	unsigned root;
	if ( Width() < 200 ) root = Compute_Root_Lowest_Weighted_Depth_Reserved();  // ToModify
	else {
		root = cluster_size - 1;  // the first minfill cluster with minimum width
		Compute_Fixed_Root_Weight_Reserved( root );  /// Compute_Root_Lowest_Weighted_Depth_Reserved trends to reduce the height of tree decomposition, but often begins with a big cluster
	}
	TreeD_Cluster_Adjacency * adj;
	unsigned * c_stack = new unsigned [cluster_size];
	unsigned num_c_stack = 0;
	adj = Search_First_Seen_Neighbour( _clusters[root].adj->next );
	for ( ; adj->ordinal < cluster_size; adj = Search_First_Seen_Neighbour( adj ) ) {
		TreeD_Cluster_Adjacency * max_adj = Pick_Preferred_Neighbour( adj, chain );
		max_adj->infor = 0;  // this neighbour is picked
		c_stack[num_c_stack++] = max_adj->ordinal;
		for ( unsigned i = 0; i < max_adj->sep_size; i++ ) {
			unsigned var = max_adj->sep[i];
			if ( scores[var] == 0 ) scores[var] = index;
		}
		index++;
	}
	for ( unsigned i = 0; i < _clusters[root].num_vars; i++ ) {
		unsigned var = _clusters[root].vars[i];
		if ( scores[var] == 0 ) scores[var] = index;
	}
	index++;
	_clusters[root].infor = 0;
//	for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//	cout << endl;
	while ( num_c_stack-- ) {
		unsigned top = c_stack[num_c_stack];
		adj = Search_First_Seen_Neighbour( _clusters[top].adj->next );
		for ( ; adj->ordinal < cluster_size; adj = Search_First_Seen_Neighbour( adj ) ) {
			TreeD_Cluster_Adjacency * max_adj = Pick_Preferred_Neighbour( adj, chain );
			max_adj->infor = 0;
			c_stack[num_c_stack++] = max_adj->ordinal;
			for ( unsigned i = 0; i < max_adj->sep_size; i++ ) {
				unsigned var = max_adj->sep[i];
				if ( scores[var] == 0 ) scores[var] = index;
			}
			index++;
		}
		for ( unsigned i = 0; i < _clusters[top].num_vars; i++ ) {
			unsigned var = _clusters[top].vars[i];
			if ( scores[var] == 0 ) scores[var] = index;
		}
		index++;
		_clusters[top].infor = 0;
//		for ( i = 0; i < chain_size; i++ ) cout << (*chain)[i] << ", ";
//		cout << endl;
	}
	for ( i = 0; i < cluster_size; i++ ) {
		_clusters[i].infor = UNSIGNED_UNDEF;
		for ( adj = _clusters[i].adj->next; adj->ordinal < cluster_size; adj = adj->next ) adj->infor = UNSIGNED_UNDEF;
	}
	delete [] c_stack;
}

unsigned Simple_TreeD::Width()
{
	vector<Simple_TreeD_Cluster>::iterator itr = _clusters.begin(), end = _clusters.end() - 1;
	unsigned max = itr->num_vars;
	for ( itr++; itr < end; itr++ ) {
		if ( max < itr->num_vars ) max = itr->num_vars;
	}
	return max - 1;
}

void Simple_TreeD::Display( ostream & fout )
{
	unsigned i, j;
	unsigned cluster_size = _clusters.size() - 1;
	fout << "Tree decomposition: " << endl;
	for ( i = 0; i < cluster_size; i++ ) {
		fout << i << ": ";
		TreeD_Cluster_Adjacency * p = _clusters[i].adj->next;
		if ( p->ordinal < cluster_size ) {
			fout << p->ordinal;
			p = p->next;
			while ( p->ordinal < cluster_size ) {
				fout << ", " << p->ordinal;
				p = p->next;
			}
			fout << " ";
		}
		fout << "[";
		if ( _clusters[i].num_vars ) fout << _clusters[i].vars[0];
		for ( j = 1; j < _clusters[i].num_vars; j++ ) {
			fout << ", " << _clusters[i].vars[j];
		}
		fout << "];" << endl;
	}
	fout << "End." << endl;
}


}
