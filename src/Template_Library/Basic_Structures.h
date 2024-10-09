#ifndef _Basic_Structures_h_
#define _Basic_Structures_h_

#include "randomc.h"
#include "Basic_Functions.h"


namespace KCBox {


/****************************************************************************************************
*                                                                                                   *
*                                    small auxiliary classes                                        *
*                                                                                                   *
****************************************************************************************************/

template<typename T_UINT> class Identity
{
protected:
	T_UINT _id;
public:
	Identity() {}
	Identity( T_UINT id ): _id( id ) {}
	Identity( const Identity &n ): _id( n._id ) {}
	Identity & operator ++(int) { _id++; return *this; }
	Identity & operator = ( Identity node ) { _id = node._id; return *this; }
	bool operator == (const Identity &other) const { return _id == other._id; }
	bool operator != (const Identity &other) const { return _id != other._id; }
	bool operator == (const T_UINT other) const { return _id == other; }
	bool operator != (const T_UINT other) const { return _id != other; }
	operator T_UINT () const { return _id; }
};


/****************************************************************************************************
*                                                                                                   *
*                                         List                                                      *
*                                                                                                   *
****************************************************************************************************/

#define _LIST_SAFE_MODE_

/**************************************************/

template<typename T> class Array
{
protected:
	T * data;
	unsigned size;
public:
	Array(): data( NULL ), size( 0 ) {}
	Array( unsigned num ): size( num )
	{
		data = new T [size];
#ifndef _LIST_SAFE_MODE_
		if ( data == NULL ) {
			cerr << "ERROR[Array]: Memory allocation failed!" << endl;
			exit( 0 );
		}
#endif
	}
	~Array()
	{
		delete [] data;
	}
	void Assign_External( T * elems, unsigned num )
	{
		data = elems;
		size = num;
	}
	void Free_External()
	{
		data = NULL;
		size = 0;
	}
	inline T & operator [] ( unsigned i )
	{
#ifndef _LIST_SAFE_MODE_
		if ( i >= size ) {
			cerr << "ERROR[Array]: Out of range!" << endl;
		}
#endif
		return data[i];
	}
	inline unsigned Size() const
	{
		return size;
	}
};

template<typename T> extern void Merge_Many_Sorted_Arrays( Array<T> arrays[], unsigned num, T * target )
{
	unsigned i, j;
	unsigned * iterator = new unsigned [num];
	iterator[0] = 0;
	T max_element = arrays[0][arrays[0].Size() - 1];
	unsigned max_array = 0;
	for ( j = 1; j < num; j++ ) {
		iterator[j] = 0;
		if ( max_element < arrays[j][arrays[j].Size() - 1] ) {
			max_element = arrays[j][arrays[j].Size() - 1];
			max_array = j;
		}
	}
	for ( i = 0; true; i++ ) {
		T current_element = max_element;
		unsigned current_array = max_array;
		for ( j = 0; j < num; j++ ) {
			if ( iterator[j] < arrays[j].Size() && arrays[j][iterator[j]] < current_element ) {
				current_element = arrays[j][iterator[j]];
				current_array = j;
			}
		}
		target[i] = current_element;
		iterator[current_array]++;
		if ( current_element == max_element ) break;
	}
	delete [] iterator;
}

/**************************************************/

template<typename T> struct SList_Node
{
	T data;
	SList_Node<T> * next;
	unsigned infor;
	SList_Node(): infor( UNSIGNED_UNDEF ) {}
	SList_Node( T value, SList_Node<T> * p ): data( value ), next( p ), infor( UNSIGNED_UNDEF ) {}
};

template<typename T> class SList
{
protected:
	SList_Node<T> * head;
public:
	SList()
	{
		head = new SList_Node<T>;
		head->next = NULL;
	}
	~SList()
	{
		do {
			SList_Node<T> * tmp = head;
			head = head->next;
			delete tmp;
		} while ( head != NULL );
	}
	unsigned Size() const
	{
		SList_Node<T> * tmp = head;
		unsigned size = 0;
		for ( ; tmp->next != NULL; tmp = tmp->next ) size++;
		return size;
	}
	SList_Node<T> * Head() { return head; }
	SList_Node<T> * Front() { return head->next; }
	SList_Node<T> * Next( SList_Node<T> * itr ) { return itr->next; }
	bool Empty() { return head->next == NULL; }
	void Push_Front( T value )
	{
		SList_Node<T> * tmp = new SList_Node<T>( value, head->next );
		head->next = tmp;
	}
	void Delete_Front()
	{
#ifndef _LIST_SAFE_MODE_
		if ( head->next == NULL ) {
			cerr << "ERROR[SList]: Empty list!" << endl;
		}
#endif
		SList_Node<T> * tmp = head->next;
		head->next = tmp->next;
		delete tmp;
	}
	void Insert_After( SList_Node<T> * itr, T value )
	{
#ifndef _LIST_SAFE_MODE_
		if ( itr == NULL ) {
			cerr << "ERROR[SList]: Invalid current node!" << endl;
		}
#endif
		SList_Node<T> * tmp = new SList_Node<T>( value, itr->next );
		itr->next = tmp;
	}
	void Delete_After( SList_Node<T> * itr )
	{
#ifndef _LIST_SAFE_MODE_
		if ( itr->next == NULL ) {
			cerr << "ERROR[SList]: Invalid current node!" << endl;
		}
#endif
		SList_Node<T> * tmp = itr->next;
		itr->next = tmp->next;
		delete tmp;
	}
};

template<typename T> class Greedy_SList
{
protected:
	SList_Node<T> * head;
	SList_Node<T> * backup;
public:
	Greedy_SList()
	{
		head = new SList_Node<T>;
		head->next = NULL;
		backup = NULL;
	}
	~Greedy_SList()
	{
		do {
			SList_Node<T> * tmp = head;
			delete tmp;
			head = head->next;
		} while ( head != NULL );
		while ( backup != NULL ) {
			SList_Node<T> * tmp = backup;
			delete tmp;
			backup = backup->next;
		}
	}
	unsigned Size() const
	{
		SList_Node<T> * tmp = head;
		unsigned size = 0;
		for ( ; tmp->next != NULL; tmp = tmp->next ) size++;
		return size;
	}
	SList_Node<T> * Head()
	{
		return head;
	}
	SList_Node<T> * First()
	{
		return head->next;
	}
	SList_Node<T> * Next( SList_Node<T> * itr )
	{
		return itr->next;
	}
	bool IsEmpty()
	{
		return head->next == NULL;
	}
	void Push_Front( T value )
	{
		SList_Node<T> * tmp;
		if ( backup != NULL ) {
			tmp = backup;
			tmp->data = value;
			tmp->next = head->next;
			backup = backup->next;
		}
		else tmp = new SList_Node<T>( value, head->next );
		head->next = tmp;
	}
	void Delete_Front()
	{
#ifndef _LIST_SAFE_MODE_
		if ( head->next == NULL ) {
			cerr << "ERROR[SList]: Empty list!" << endl;
			exit( 1 );
		}
#endif
		SList_Node<T> * tmp = head->next;
		head->next = tmp->next;
		tmp->infor = unsigned (-1);
		tmp->next = backup;
		backup = tmp;
	}
	void Insert_After( SList_Node<T> * itr, T value )
	{
#ifndef _LIST_SAFE_MODE_
		if ( itr == NULL ) {
			cerr << "ERROR[SList]: Invalid current node!" << endl;
			exit( 1 );
		}
#endif
		SList_Node<T> * tmp;
		if ( backup != NULL ) {
			tmp = backup;
			tmp->data = value;
			tmp->next = itr->next;
			backup = backup->next;
		}
		else tmp = new SList_Node<T>( value, itr->next );
		itr->next = tmp;
	}
	void Delete_After( SList_Node<T> * itr )
	{
#ifndef _LIST_SAFE_MODE_
		if ( itr->next == NULL ) {
			cerr << "ERROR[SList]: Invalid current node!" << endl;
			exit( 1 );
		}
#endif
		SList_Node<T> * tmp = itr->next;
		itr->next = tmp->next;
		tmp->infor = unsigned (-1);
		tmp->next = backup;
		backup = tmp;
	}
};

template<typename T> class Greedy_Stack
{
protected:
	SList_Node<T> * head;
	SList_Node<T> * backup;
public:
	Greedy_Stack()
	{
		head = nullptr;
		backup = nullptr;
	}
	~Greedy_Stack()
	{
		while ( head != nullptr ) {
			SList_Node<T> * tmp = head;
			head = head->next;
			delete tmp;
		}
		while ( backup != nullptr ) {
			SList_Node<T> * tmp = backup;
			delete tmp;
			backup = backup->next;
		}
	}
	bool Empty()
	{
		return head == nullptr;
	}
	void Push( T value )
	{
		if ( backup != nullptr ) {
			SList_Node<T> * tmp = backup;
			backup = backup->next;
			tmp->data = value;
			tmp->next = head;
			head = tmp;
		}
		else head = new SList_Node<T>( value, head );
	}
	void Pop()
	{
		if ( head == nullptr ) return;
		SList_Node<T> * tmp = head;
		head = head->next;
		tmp->infor = UNSIGNED_UNDEF;
		tmp->next = backup;
		backup = tmp;
	}
};

template<typename T> class Greedy_Queue
{
protected:
	SList_Node<T> * _head;
	SList_Node<T> * _tail;
public:
	Greedy_Queue()
	{
		_head = new SList_Node<T>;
		_head->next = _head;
		_tail = _head;
	}
	~Greedy_Queue()
	{
		_tail = _head;
		while ( _head != _tail ) {
			SList_Node<T> * tmp = _head;
			_head = _head->next;
			delete tmp;
		}
	}
	bool Empty() { return _head == _tail; }
	void Push( T value )
	{
		if ( _tail->next != _head ) {
			_tail = _tail->next;
			_tail->data = value;
		}
		else {
			_tail->next = new SList_Node<T>( value, _head );
			_tail = _tail->next;
		}
	}
	void Pop()
	{
		if ( _head == _tail ) return;
		_head = _head->next;
	}
};

template<typename T> struct DLList_Node
{
	T data;
	DLList_Node<T> * prev;
	DLList_Node<T> * next;
	unsigned infor;
	DLList_Node(): infor( UNSIGNED_UNDEF ) {}
	DLList_Node( T value, DLList_Node<T> * p, DLList_Node<T> * n ): data( value ), prev( p ), next( n ), infor( UNSIGNED_UNDEF ) {}
};

template<typename T> class CDLList
{
protected:
	DLList_Node<T> * head;
public:
	CDLList()
	{
		head = new DLList_Node<T>;
		head->next = head->prev = head;
	}
	~CDLList()
	{
		for ( DLList_Node<T> * itr = head->next; itr != head;  ) {
			DLList_Node<T> * tmp = itr;
			itr = itr->next;
			delete tmp;
		}
		delete head;
	}
	unsigned Size() const
	{
		DLList_Node<T> * tmp = head;
		unsigned size = 0;
		for ( ; tmp->next != head; tmp = tmp->next ) size++;
		return size;
	}
	DLList_Node<T> * Head() { return head; }
	DLList_Node<T> * Front() { return head->next; }
	DLList_Node<T> * Back() { return head->prev; }
	DLList_Node<T> * Prev( DLList_Node<T> * itr ) { return itr->prev; }
	DLList_Node<T> * Next( DLList_Node<T> * itr ) { return itr->next; }
	bool Empty() { return head->next == head; }
	DLList_Node<T> * Insert_Front( T value )
	{
		DLList_Node<T> * tmp = new DLList_Node<T>( value, head, head->next );
		head->next->prev = tmp;
		head->next = tmp;
		return tmp;
	}
	DLList_Node<T> * Insert_Back( T value )
	{
		DLList_Node<T> * tmp = new DLList_Node<T>( value, head->prev, head );
		head->prev->next = tmp;
		head->prev = tmp;
		return tmp;
	}
	void Delete_Front()
	{
		if ( head->next == head ) {
			cerr << "ERROR[CDLList]: Empty list!" << endl;
			exit( 1 );
		}
		DLList_Node<T> * tmp = head->next;
		head->next = tmp->next;
		head->next->prev = head;
		delete tmp;
	}
	DLList_Node<T> * Insert_After( DLList_Node<T> * itr, T value )
	{
		if ( itr == nullptr ) {
			cerr << "ERROR[CDLList]: Invalid current node!" << endl;
			exit( 1 );
		}
		DLList_Node<T> * tmp = new DLList_Node<T>( value, itr, itr->next );
		itr->next->prev = tmp;
		itr->next = tmp;
		return tmp;
	}
	void Delete( DLList_Node<T> * itr )
	{
		if ( itr == nullptr ) {
			cerr << "ERROR[CDLList]: Invalid node!" << endl;
			exit( 1 );
		}
		itr->next->prev = itr->prev;
		itr->prev->next = itr->next;
		delete itr;
	}
};

/**************************************************/

template<typename T> class BigVector
{
protected:
	T * _elems;
	size_t _size;
	size_t _capacity;
public:
	BigVector( size_t max_size = 0 ): _size( 0 ), _capacity( max_size ) { Allocate(); }
	BigVector( size_t max_size, const T elem ): _size( max_size ), _capacity( max_size )
	{
		Allocate();
		for ( size_t i = 0; i < _size; i++ ) _elems[i] = elem;
	}
	~BigVector() { delete [] _elems; }
	bool Empty() const { return _size == 0; }
	T * Elements() { return _elems; }
	size_t Size() const { return _size; }
	void Resize( size_t size ) { _size = size; }
	void Enlarge( size_t max_size )
	{
		if ( _capacity > max_size ) return;
		T * elems = _elems;
		_capacity = max_size;
		Allocate();
		for ( size_t i = 0; i < _size; i++ ) _elems[i] = elems[i];
		delete [] elems;
	}
	void Enlarge( size_t max_size, const T elem )
	{
		if ( _capacity > max_size ) return;
		T * elems = _elems;
		_capacity = max_size;
		Allocate();
		for ( size_t i = 0; i < _size; i++ ) _elems[i] = elems[i];
		for ( ; _size < max_size; _size++ ) _elems[_size] = elem;
		delete [] elems;
	}
	T & operator [] ( size_t i ) { return _elems[i]; }
	T & operator [] ( unsigned i ) { return _elems[i]; }
	T & Back() { return _elems[_size - 1]; }
	void Push_Back( T elem ) { _elems[_size++] = elem; }  /// guarantee externally that _size is less than _capacity
	void Push_Back( T elem, bool flag ) { _elems[_size] = elem; _size += flag; }  /// guarantee externally that _size is less than _capacity
	void Erase( size_t i ) { assert( i < _size ); _elems[i] = _elems[--_size]; }
	T Pop_Back() { return _elems[--_size]; }
	void Clear() { _size = 0; }
protected:
	void Allocate()
	{
		_elems = new T [_capacity];
		if ( _capacity > 0 && _elems == nullptr ) {
			cerr << "ERROR[BigVector]: fail in allocating space for BigClause!" << endl;
			exit( 1 );
		}
	}
};

/**************************************************/

template<typename T> class BlockVector  // used for huge array
{
protected:
	unsigned _size_per_block;
	unsigned _bits_of_size_per_block;
	unsigned _block_mask;
	vector<vector<T>> _blocks;
	size_t _size;
public:
	BlockVector( unsigned size_per_block, size_t block_count = 0 ): _size( 0 )
	{
		assert( size_per_block > 0 );
		_bits_of_size_per_block = Ceil_Log2( size_per_block );
		_size_per_block = 1 << _bits_of_size_per_block;
		_block_mask = _size_per_block - 1;
		_blocks.reserve( 8 );  // exclude 0
		_blocks.resize( block_count );
		for ( size_t i = 0; i < block_count; i++ ) {
			_blocks[i] = vector<T>( _size_per_block );
		}
	}
	bool Empty() const { return _size == 0; }
	size_t Size() const { return _size; }
	void Resize( size_t size )
	{
		if ( size > Capacity() ) Reserve( size );
		_size = size;
	}
	size_t Capacity() const { return _blocks.size() * _size_per_block; }
	void Reserve( size_t capacity )
	{
		size_t old_count = _blocks.size();
		size_t new_count = Block_Count( capacity );
		if ( new_count < old_count ) {
			_blocks.resize( new_count );
			if ( _size > new_count * _size_per_block ) _size = new_count * _size_per_block;
		}
		else if ( new_count > old_count ) {
			while ( new_count > _blocks.capacity() ) Realloc_Blocks();
			_blocks.resize( new_count );
			_blocks[old_count] = vector<T>( _size_per_block );
			for ( ; old_count < new_count; old_count++ ) {
				_blocks[old_count] = vector<T>( _size_per_block );
			}
		}
	}
	void Double_Block_Size()
	{
		_bits_of_size_per_block++;
		assert( _bits_of_size_per_block <= UNSIGNED_SIZE - 1 );
		_size_per_block = 1 << _bits_of_size_per_block;
		_block_mask = _size_per_block - 1;
		size_t i;
		for ( i = 0; i + i + 1 < _blocks.size(); i++ ) {
			_blocks[i] = _blocks[i + i];
			_blocks[i].insert( _blocks[i].end(), _blocks[i + i + 1].begin(), _blocks[i + i + 1].end() );
		}
		if ( _blocks.size() % 2 ) {
			_blocks[i] = _blocks.back();
			_blocks[i].resize( _size_per_block );
			i++;
		}
		_blocks.resize( i );
	}
	void Shrink_To_Fit()
	{
		size_t new_count = Block_Count( _size );
		_blocks.resize( new_count );
		_blocks.shrink_to_fit();
	}
	T & operator [] ( size_t i )
	{
		if ( i >= _size ) {
			cerr << "ERROR[BlockVector]: " << i << " exceeds " << _size << endl;
			assert( i < _size );
		}
		return _blocks[Upper_Loc(i)][Lower_Loc(i)];
	}
	T & Back() { return (*this)[_size - 1]; }
	void Push_Back( T elem )
	{
		if ( _size == Capacity() ) {
			if ( _blocks.size() == _blocks.capacity() ) Realloc_Blocks();
			_blocks.push_back( vector<T>( _size_per_block ) );
		}
		(*this)[_size++] = elem;
	}
	void Erase_Simply( size_t i ) { (*this)[i] = (*this)[_size - 1]; _size--; }
	void Erase( size_t i )
	{
		for ( size_t j = i + 1; j < _size; j++ ) {
			(*this)[j-1] = (*this)[j];
		}
		_size--;
	}
	void Erase( size_t begin, size_t end ) // remove [begin, end)
	{
		assert( begin < end && end <= _size );
		size_t diff = end - begin;
		for ( size_t j = end; j < _size; j++ ) {
			(*this)[j - diff] = (*this)[j];
		}
		_size -= diff;
	}
	T Pop_Back() { return (*this)[--_size]; }
	void Clear() { _size = 0; }
	void Swap( BlockVector<T> & other )
	{
		swap( _size_per_block, other._size_per_block );
		swap( _bits_of_size_per_block, other._bits_of_size_per_block );
		swap( _block_mask, other._block_mask );
		_blocks.swap( other._blocks );
		swap( _size, other._size );
	}
protected:
	size_t Upper_Loc( size_t i ) { return i >> _bits_of_size_per_block; }
	unsigned Lower_Loc( size_t i ) { return i & _block_mask; }
	size_t Block_Count( size_t capacity ) { return ( capacity + _size_per_block - 1 ) >> _bits_of_size_per_block; }
	void Realloc_Blocks()
	{
		vector<vector<T>> new_blocks( _blocks.capacity() * 2 );
		new_blocks.resize( _blocks.size() );
		for ( size_t i = 0; i < _blocks.size(); i++ ) {
			new_blocks[i].swap( _blocks[i] );
		}
		_blocks.swap( new_blocks );
	}
};


/****************************************************************************************************
*                                                                                                   *
*                                            Hash table                                             *
*                                                                                                   *
****************************************************************************************************/

#define LITTLE_HASH_TABLE       100
#define SMALL_HASH_TABLE		1000
#define MEDIAN_HASH_TABLE	    10000
#define BIG_HASH_TABLE  	    100000
#define LARGE_HASH_TABLE		1000000
#define HUGE_HASH_TABLE    		10000000

template <typename T> class Hash_Table
{
protected:
	vector<vector<size_t>> _entries;
	vector<T> _data;
	bool _hit_success;  // record the status of the latest hit
public:
	Hash_Table( size_t num_entries = MEDIAN_HASH_TABLE )
	{
		_entries.resize( Prime_Close( num_entries ) );
		size_t data_capacity = _entries.size() * 2;
		size_t entry_capacity = 4;  /// entry_capacity = 2 * data_capacity / _entries.size()
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].reserve( entry_capacity );
		}
		_data.reserve( data_capacity );
		_hit_success = false;
	}
	size_t Hit( T & element )
	{
		if ( _data.size() > _entries.size() * 4 ) Resize_Entries( _entries.size() * 2 );
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) {
				_hit_success = true;
				return _entries[key][i];
			}
		}
		_entries[key].push_back( _data.size() );
		_data.push_back( element );
		_hit_success = false;
		return _data.size() - 1;
	}
	size_t Hit( T & element, size_t & memory )
	{
		if ( _data.size() > _entries.size() * 4 ) {
			ASSERT( memory == Memory() );
			Resize_Entries( _entries.size() * 2 );
			memory = Memory();
		}
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) {
				_hit_success = true;
				return _entries[key][i];
			}
		}
		memory -= _entries[key].capacity() * sizeof(size_t);
		_entries[key].push_back( _data.size() );
		memory += _entries[key].capacity() * sizeof(size_t);
		memory -= ( _data.capacity() - _data.size() ) * sizeof(T);
		_data.push_back( element );
		memory += ( _data.capacity() - _data.size() ) * sizeof(T);
		_hit_success = false;
		memory += _data.back().Memory();  /// _data[_data.Size() - 1] might have different memory from element
		return _data.size() - 1;
	}
	bool Hit_Successful() const { return _hit_success; }
	void Erase( size_t loc )
	{
		ASSERT( loc < _data.size() );
		size_t i, key = _data[loc].Key() % _entries.size();
		for ( i = 0; loc != _entries[key][i]; i++ ) {}
		Simply_Erase_Vector_Element( _entries[key], i );
		size_t fill_loc = _data.size() - 1;
		key = _data.back().Key() % _entries.size();
		for ( i = 0; fill_loc != _entries[key][i]; i++ ) {}
		_entries[key][i] = loc;
		Simply_Erase_Vector_Element( _data, loc );
	}
	size_t Location( T & element )
	{
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) return _entries[key][i];
		}
		return SIZET_UNDEF;
	}
	const vector<T> & Data() const { return _data; }
	T & operator [] ( size_t i ) { return _data[i];	}
	bool Empty() const { return _data.empty(); }
	size_t Size() const { return _data.size(); }
	size_t Capacity() const { return _data.capacity(); }
	void Reserve( size_t capacity )
	{
		assert( capacity >= _data.size() );
		_data.reserve( capacity );
	}
	void Shrink_To_Fit()
	{
		_data.shrink_to_fit();
		_entries.clear();
		_entries.shrink_to_fit();
		_entries.resize( Prime_Close( _data.size() / 2 ) );
		for ( size_t i = 0; i < _data.size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	size_t Memory() const
	{
		size_t mem = 0;
		for ( size_t i = 0; i < _data.size(); i++ ) {
			mem += _data[i].Memory();
		}
		mem += ( _data.capacity() - _data.size() ) * sizeof(T);
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			mem += _entries[i].capacity() * sizeof(size_t);
		}
		mem += _entries.capacity() * sizeof(vector<size_t>);
		return mem;
	}
	void Recompute_Entries()
	{
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_entries.resize( Prime_Close( _data.size() / 2 ) );
		for ( size_t i = 0; i < _data.size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Resize( size_t new_size )
	{
		if ( new_size > _data.size() ) {
			cerr << "Warning[Hash_Table]: new size is greater than old size" << endl;
			return;
		}
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_data.resize( new_size );
		for ( size_t i = 0; i < _data.size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Resize_Entries( size_t new_size )
	{
		if ( new_size <= _entries.size() ) {
			cerr << "Warning[Hash_Table]: new size of _entries is not greater than old size" << endl;
			return;
		}
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_entries.resize( Prime_Close( new_size ) );
		for ( size_t i = 0; i < _data.size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Clear()
	{
		size_t entry_size = _entries.size();
		_entries.clear();
		_entries.resize( entry_size );
		_data.clear();
	}
	void Clear( vector<size_t> & kept_locs )
	{
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		Clear();
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Clear_Shrink_Half( vector<size_t> & kept_locs )
	{
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		Clear();
		_data.reserve( _data.capacity() / 2 );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Clear_Old_Data( vector<size_t> & kept_locs, size_t cleared_size )
	{
		assert( 0 < cleared_size && cleared_size <= _data.size() );
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		_data.erase( _data.begin(), _data.begin() + cleared_size );
		Recompute_Entries();
		_data.reserve( _data.size() + ( _data.capacity() - _data.size() ) / 2 );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Swap( Hash_Table<T> & other )
	{
		_entries.swap( other._entries );
		_data.swap( other._data );
	}
	void Reset()
	{
		vector<vector<size_t>> tmp_entries;
		vector<T> tmp_data;
		_entries.swap(  tmp_entries);
		_data.swap( tmp_data );
		_entries.resize( Prime_Close( MEDIAN_HASH_TABLE ) );
		size_t data_capacity = _entries.size() * 2;
		size_t entry_capacity = 4;  /// entry_capacity = 2 * data_capacity / _entries.size()
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].reserve( entry_capacity );
		}
		_data.reserve( data_capacity );
		_hit_success = false;
	}
};

template <typename T> class Large_Hash_Table  // designed for memory exhausted
{
protected:
	vector<vector<size_t>> _entries;
	BlockVector<T> _data;
	bool _hit_success;  // record the status of the latest hit
public:
	Large_Hash_Table( size_t num_entries = LARGE_HASH_TABLE ): _data( 64 * 1024, 16 )
	{
		_entries.resize( Prime_Close( num_entries ) );
		size_t data_capacity = _entries.size() * 2;
		size_t entry_capacity = 4;  /// entry_capacity = 2 * data_capacity / _entries.size()
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].reserve( entry_capacity );
		}
		_data.Reserve( data_capacity );
		_hit_success = false;
	}
	size_t Hit( T & element )
	{
		if ( _data.Size() > _entries.size() * 4 ) Resize_Entries( _entries.size() * 2 );
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) {
				_hit_success = true;
				return _entries[key][i];
			}
		}
		_entries[key].push_back( _data.Size() );
		_data.Push_Back( element );
		_hit_success = false;
		return _data.Size() - 1;
	}
	size_t Hit( T & element, size_t & memory )
	{
		if ( _data.Size() > _entries.size() * 4 ) {
			ASSERT( memory == Memory() );
			Resize_Entries( _entries.size() * 2 );
			memory = Memory();
		}
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) {
				_hit_success = true;
				return _entries[key][i];
			}
		}
		memory -= _entries[key].capacity() * sizeof(size_t);
		_entries[key].push_back( _data.Size() );
		memory += _entries[key].capacity() * sizeof(size_t);
		memory -= ( _data.Capacity() - _data.Size() ) * sizeof(T);
		_data.Push_Back( element );
		memory += ( _data.Capacity() - _data.Size() ) * sizeof(T);
		_hit_success = false;
		memory += _data.Back().Memory();  // _data[_data.Size() - 1] might have different memory from element
		return _data.Size() - 1;
	}
	bool Hit_Successful() const { return _hit_success; }
	void Erase( size_t loc )
	{
		ASSERT( loc < _data.Size() );
		size_t i, key = _data[loc].Key() % _entries.size();
		for ( i = 0; loc != _entries[key][i]; i++ ) {}
		Simply_Erase_Vector_Element( _entries[key], i );
		size_t fill_loc = _data.Size() - 1;
		key = _data.Back().Key() % _entries.size();
		for ( i = 0; fill_loc != _entries[key][i]; i++ ) {}
		_entries[key][i] = loc;
		_data.Simply_Erase( loc );
	}
	size_t Location( T & element )
	{
		size_t key = element.Key();
		key %= _entries.size();
		for ( size_t i = 0; i < _entries[key].size(); i++ ) {
			if ( element == _data[_entries[key][i]] ) return _entries[key][i];
		}
		return SIZET_UNDEF;
	}
	const vector<T> & Data() const { return _data; }
	T & operator [] ( size_t i ) { return _data[i];	}
	bool Empty() const { return _data.Empty(); }
	size_t Size() const { return _data.Size(); }
	size_t Capacity() const { return _data.Capacity(); }
	void Reserve( size_t capacity )
	{
		assert( capacity >= _data.Size() );
		_data.Reserve( capacity );
	}
	void Shrink_To_Fit()
	{
		_data.Shrink_To_Fit();
		_entries.clear();
		_entries.shrink_to_fit();
		_entries.resize( Prime_Close( _data.Size() / 2 ) );
		for ( size_t i = 0; i < _data.Size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	size_t Memory()
	{
		size_t mem = 0;
		for ( size_t i = 0; i < _data.Size(); i++ ) {
			mem += _data[i].Memory();
		}
		mem += ( _data.Capacity() - _data.Size() ) * sizeof(T);
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			mem += _entries[i].capacity() * sizeof(size_t);
		}
		mem += _entries.capacity() * sizeof(vector<size_t>);
		return mem;
	}
	void Recompute_Entries()
	{
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_entries.resize( Prime_Close( _data.Size() / 2 ) );
		for ( size_t i = 0; i < _data.Size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Resize( size_t new_size )
	{
		if ( new_size > _data.Size() ) {
			cerr << "Warning[Large_Hash_Table]: new size is greater than old size" << endl;
			return;
		}
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_data.Resize( new_size );
		for ( size_t i = 0; i < _data.Size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Resize_Entries( size_t new_size )
	{
		if ( new_size <= _entries.size() ) {
			cerr << "Warning[Large_Hash_Table]: new size of _entries is not greater than old size" << endl;
			return;
		}
		for ( size_t i = 0; i < _entries.size(); i++ ) {
			_entries[i].clear();
		}
		_entries.resize( Prime_Close( new_size ) );
		for ( size_t i = 0; i < _data.Size(); i++ ) {
			size_t key = _data[i].Key();
			key %= _entries.size();
			_entries[key].push_back( i );
		}
	}
	void Clear()
	{
		size_t entry_size = _entries.size();
		_entries.clear();
		_entries.resize( entry_size );
		_data.Clear();
	}
	void Clear( vector<size_t> & kept_locs )
	{
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		Clear();
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Clear_Shrink_Half( vector<size_t> & kept_locs )
	{
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		Clear();
		_data.Reserve( _data.Capacity() / 2 );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Clear_Old_Data( vector<size_t> & kept_locs, size_t cleared_size )
	{
		assert( 0 < cleared_size && cleared_size <= _data.Size() );
		vector<T> kept_elems( kept_locs.size() );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_elems[i] = _data[kept_locs[i]];
		}
		_data.Erase( 0, cleared_size );
		Recompute_Entries();
		_data.Reserve( _data.Size() + ( _data.Capacity() - _data.Size() ) / 2 );
		for ( unsigned i = 0; i < kept_locs.size(); i++ ) {
			kept_locs[i] = Hit( kept_elems[i] );
		}
	}
	void Swap( Large_Hash_Table<T> & other )
	{
		_entries.swap( other._entries );
		_data.Swap( other._data );
	}
};


/****************************************************************************************************
*                                                                                                   *
*                                            Pair                                                   *
*                                                                                                   *
****************************************************************************************************/

template<typename T1, typename T2> struct Pair
{
	T1 left;
	T2 right;
	Pair() {}
	Pair( T1 first, T2 second ) : left( first ), right( second ) {}
	bool operator == ( Pair & other ) const
	{
		return left == other.left + right == other.right;
	}
};

/****************************************************************************************************
*                                                                                                   *
*                                            Map                                                    *
*                                                                                                   *
****************************************************************************************************/

struct Unary_Map_Node
{
	unsigned key;
	unsigned result;
	bool operator == ( Unary_Map_Node & other ) const
	{
		return key == other.key;
	}
	unsigned Key() const
	{
		return key;
	}
};

class Unary_Map: public Hash_Table<Unary_Map_Node>
{
public:
	Unary_Map(): Hash_Table() {}
	Unary_Map( unsigned num_entries ): Hash_Table( num_entries ) {}
	unsigned Map( unsigned key ) { Unary_Map_Node node; node.key = key; node.result = UNSIGNED_UNDEF; return (*this)[Hit( node )].result; }
};

template<class T1, class T2, class TR>
struct Binary_Map_Node
{
	T1 left;
	T2 right;
	TR result;
	Binary_Map_Node() {}
	Binary_Map_Node( T1 l, T2 r ): left( l ), right( r ) {}
	Binary_Map_Node( T1 l, T2 r, TR rsl ): left( l ), right( r ), result( rsl ) {}
	bool operator == ( Binary_Map_Node<T1, T2, TR> & other ) const
	{
		return ( left == other.left ) + ( right == other.right ) == 2;
	}
	unsigned Key() const
	{
		return PAIR( left, right );
	}
};

template<class T1, class T2, class TR>
class Binary_Map: public Hash_Table<Binary_Map_Node<T1, T2, TR>>
{
public:
	Binary_Map(): Hash_Table<Binary_Map_Node<T1, T2, TR>>() {}
	Binary_Map( unsigned num_entries ): Hash_Table<Binary_Map_Node<T1, T2, TR>>( num_entries ) {}
	TR Map( T1 left, T2 right )
	{
		Binary_Map_Node<T1, T2, TR> node( left, right );
		size_t loc = this->Location( node );  /// without "this->": no declarations were found by argument-dependent lookup at the point of instantiation
		assert( loc != SIZET_UNDEF );
		return (*this)[loc].result;
	}
};

template<class T1, class T2, class TR>
class Large_Binary_Map: public Large_Hash_Table<Binary_Map_Node<T1, T2, TR>>
{
public:
	Large_Binary_Map(): Large_Hash_Table<Binary_Map_Node<T1, T2, TR>>() {}
	Large_Binary_Map( unsigned num_entries ): Large_Hash_Table<Binary_Map_Node<T1, T2, TR>>( num_entries ) {}
	TR Map( T1 left, T2 right )
	{
		Binary_Map_Node<T1, T2, TR> node( left, right );
		size_t loc = this->Location( node );  /// without "this->": no declarations were found by argument-dependent lookup at the point of instantiation
		assert( loc != SIZET_UNDEF );
		return (*this)[loc].result;
	}
};

template<class T1, class T2, class T3, class TR>
struct Ternary_Map_Node
{
	T1 left;
	T2 mid;
	T3 right;
	TR result;
	bool operator == ( Ternary_Map_Node<T1, T2, T3, TR> & other ) const
	{
		return ( left == other.left ) + ( mid == other.mid ) + ( right == other.right ) == 3;
	}
	unsigned Key() const
	{
		return PAIR( PAIR( left, mid ), right );
	}
};

template<class T1, class T2, class T3, class TR>
class Ternary_Map: public Hash_Table<Ternary_Map_Node<T1, T2, T3, TR>>
{
public:
	Ternary_Map(): Hash_Table<Ternary_Map_Node<T1, T2, T3, TR>>() {}
	Ternary_Map( unsigned num_entries ): Hash_Table<Ternary_Map_Node<T1, T2, T3, TR>>( num_entries ) {}
};

template<class T1, class T2, class T3, class T4, class TR>
struct Quaternary_Map_Node
{
	T1 first;
	T2 second;
	T3 third;
	T4 fourth;
	TR result;
	bool operator == ( Quaternary_Map_Node<T1, T2, T3, T4, TR> & other ) const
	{
		return ( first == other.first ) + ( second == other.second ) + \
		( third == other.third ) + ( fourth == other.fourth ) == 4;
	}
	unsigned Key() const
	{
		return PAIR( PAIR( PAIR( first, second ), third ), fourth );
	}
};

template<class T1, class T2, class T3, class T4, class TR>
class Quaternary_Map: public Hash_Table<Quaternary_Map_Node<T1, T2, T3, T4, TR>>
{
public:
	Quaternary_Map(): Hash_Table<Quaternary_Map_Node<T1, T2, T3, T4, TR>>() {}
	Quaternary_Map( unsigned num_entries ): Hash_Table<Quaternary_Map_Node<T1, T2, T3, T4, TR>>( num_entries ) {}
};


/****************************************************************************************************
*                                                                                                   *
*                                         Set                                                       *
*                                                                                                   *
****************************************************************************************************/

template<class T>
struct SortedSet
{
	T * elems;  // elems is sorted
	unsigned size;
	SortedSet() : elems( nullptr ), size( 0 ) {}
	SortedSet( T * elements, unsigned num ) : elems( elements ), size( num ) {}
	void Realloc() { elems = new T [size]; }
	T & operator [] ( unsigned i ) { return elems[i]; }
	T Element( unsigned i ) const { return elems[i]; }
	bool Contain( T & elem ) const
	{
		if ( size == 0 ) return false;
		unsigned pos = Binary_Search( elems, 0, size, elem );
		return elems[pos] == elem;
	}
	T & Back() { return elems[size - 1]; }
	bool operator == ( SortedSet & other ) // Constant node is applicable
	{
		if ( size != other.size ) return false;
		unsigned i;
		for ( i = 0; i < size && elems[i] == other.elems[i]; i++ ) {}
		return i == size;
	}
	unsigned Key() const
	{
		unsigned k = size;
		for ( unsigned i = 0; i < size; i++ ) k = PAIR( k, elems[i] );  // T is transformable to a number
		return k;
	}
	size_t Memory() const { return sizeof(SortedSet) + sizeof(T) * size; }
	void Display( ostream & out ) const
	{
		unsigned i;
		if ( size == 0 ) out << "{}";
		else {
			out << "{";
			out << elems[0];
			for ( i = 1; i < size; i++ ) {
				out << ", " << elems[i];
			}
			out << "}";
		}
	}
};

template<class T>
class DynamicSet: protected vector<T>
{
public:
	DynamicSet() {}
	DynamicSet( unsigned num ): vector<T>( num ) {}
	DynamicSet( T * elements, unsigned num ): vector<T>( num )
	{
		unsigned i;
		if ( num > 0 ) {
			(*this)[0] = elements[0];
		}
		for ( i = 1; i < num; i++ ) {
			assert( elements[i-1] < elements[i] );
			(*this)[i] = elements[i];
		}
	}
	DynamicSet( vector<T> elements ): vector<T>( elements.size() ) {}
	unsigned Size() const { return this->size(); }
	bool In( const T & elem )
	{
		if ( this->empty() ) return false;
		unsigned low = 0, high = this->size(); // data[high - 1] is the last element
		while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
			unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
			if ( elem < (*this)[mid] ) high = mid;
			else low = mid;
		}
		T tmp = (*this)[high - 1];
		(*this)[high - 1] = elem;
		for ( ; (*this)[low] < elem; low++ );
		(*this)[high - 1] = tmp;
		return (*this)[low] == elem;
	}
	bool Is_Disjoint( const DynamicSet & other )
	{
		unsigned i = 0, j = 0;
		while ( i < this->size() && j < other.size() ) {
			if ( (*this)[i] < other[j] ) i++;
			else if ( other[j] < (*this)[i] ) j++;
			else return false;
		}
		return true;
	}
	void Singleton( const T & elem )
	{
		this->resize( 1 );
		(*this)[0] = elem;
	}
	void Add_Element( const T & elem )
	{
		unsigned i, s = this->size();
		if ( s == 0 ) {
			this->push_back( elem );
			return;
		}
		if ( this->front() > elem ) {
			this->resize( s + 1 );
			for ( i = s; i > 0; i-- ) {
				(*this)[i] = (*this)[i-1];
			}
			(*this)[0] = elem;
		}
		unsigned low = 0, high = s;
		while ( low + 1 < high ) { // low < high may not quit from loop, the old version "low < high - 1" may be overflow
			unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
			if ( elem < (*this)[mid] ) high = mid;
			else low = mid;
		}
		if ( (*this)[low] != elem ) {
			this->resize( s + 1 );
			for ( i = s - 1; i > low; i-- ) {
				(*this)[i+1] = (*this)[i];
			}
			(*this)[i+1] = elem;
		}
	}
	void Intersection( const DynamicSet & a, const DynamicSet & b )
	{
		unsigned i = 0, j = 0;
		this->clear();
		while ( ( i < a.size() ) && ( j < b.size() ) ) {
			if ( a[i] < b[j] ) i++;
			else if ( b[j] < a[i] ) j++;
			else {
				push_back( a[i] );
				i++, j++;
			}
		}
	}
	void Union( const DynamicSet & a, const DynamicSet & b )
	{
		assert( this != &a && this != &b );
		unsigned i = 0, j = 0;
		this->clear();
		while ( i < a.size() && j < b.size() ) {
			if ( a[i] < b[j] ) this->push_back( a[i++] );
			else {
				if ( a[i] == b[j] ) i++;
				this->push_back( b[j++] );
			}
		}
		while ( i < a.size() ) this->push_back( a[i++] );
		while ( j < b.size() ) this->push_back( b[j++] );
	}
	void Union( const DynamicSet & other )
	{
		unsigned i = 0, j = 0;
		vector<T> a( this->begin(), this->end() );
		this->clear();
		while ( i < a.size() && j < other.size() ) {
			if ( a[i] < other[j] ) this->push_back( a[i++] );
			else {
				if ( a[i] == other[j] ) i++;
				this->push_back( other[j++] );
			}
		}
		while ( i < a.size() ) this->push_back( a[i++] );
		while ( j < other.size() ) this->push_back( other[j++] );
	}
	void Difference( const DynamicSet & a, const DynamicSet & b )
	{
		unsigned i = 0, j = 0;
		this->clear();
		while ( i < a.size() && j < b.size() ) {
			if ( a[i] < b[j] ) this->push_back( a[i++] );
			else if ( a[i] > b[j] ) j++;
			else i++, j++;
		}
		while ( i < a.size() ) this->push_back( a[i++] );
	}
	void Display( ostream & fout )
	{
		unsigned i;
		if ( this->empty() ) fout << "{}";
		else {
			fout << "{" << (*this)[0];
			for ( i = 1; i < this->size(); i++ ) fout << ", " << (*this)[i];
			fout << "}";
		}
	}
protected:
	void Add_Element_No_Check( T element )
	{
		unsigned i, s = this->size();
		this->resize( s + 1 );
		if ( s == 0 ) (*this)[0] = element;
		else if ( element < (*this)[0] ) {
			for ( i = s; i > 0; i-- ) {
				(*this)[i] = (*this)[i-1];
			}
			(*this)[0] = element;
		}
		else {
			for ( i = s - 1; (*this)[i] > element; i-- ) {
				(*this)[i+1] = (*this)[i];
			}
			(*this)[i+1] = element;
		}
	}
	void Union_Disjoint( const DynamicSet & other )
	{
		unsigned i = this->size() - 1, j = other.size() - 1, k = this->size() + other.size() - 1;
		this->resize( k + 1 );
		while ( i != unsigned (-1) && j != unsigned (-1) ) {
			if ( (*this)[i] > other[j] ) (*this)[k--] = (*this)[i--];
			else (*this)[k--] = other[j--];
		}
		while ( j != unsigned (-1) ) (*this)[k--] = other[j--];
	}
	void Union_Disjoint( const DynamicSet & a, const DynamicSet & b )
	{
		unsigned i = 0, j = 0;
		while ( i < a.size() && j < b.size() ) {
			if ( a[i] < b[j] ) push_back( a[i++] );
			else push_back( b[j++] );
		}
		while ( i < a.size() ) push_back( a[i++] );
		while ( j < b.size() ) push_back( b[j++] );
	}
	void Difference_Subset( const DynamicSet & a, const DynamicSet & b )
	{
		unsigned i = 0, j = 0;
		while ( i < a.size() && j < b.size() ) {
			if ( a[i] < b[j] ) push_back( a[i++] );
			else {
				assert( a[i] == b[j] );
				i++, j++;
			}
		}
		while ( i < a.size() ) push_back( a[i++] );
	}
};

class BoundedSet
{
protected:
	static unsigned _max_elem;
	static unsigned _num_sets;
	static unsigned _num_bits;
	ullong * _bits;
public:
	static void Set_Max_Element( unsigned max_elem )
	{
		if ( _num_sets > 0 && _max_elem != max_elem ) {
			cerr << "ERROR in BoundedSet::Set_Max_Element: there exist bounded sets with a different _max_elem!" << endl;
			exit( 1 );
		}
		_max_elem = max_elem;
		_num_bits = _max_elem / ULLONG_SIZE + 1;
	}
	BoundedSet()
	{
		_bits = new ullong [_num_bits];
		_bits[0] = 0;
		for ( unsigned i = 1; i < _num_bits; i++ ) {
			_bits[i] = 0;
		}
		_num_sets++;
	}
	BoundedSet( const BoundedSet & other )
	{
		_bits = new ullong [_num_bits];
		_bits[0] = other._bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) {
			_bits[i] = other._bits[i];
		}
		_num_sets++;
	}
	~BoundedSet() { delete [] _bits; _num_sets--; }
	bool Empty()
	{
		unsigned i;
		ullong tmp = _bits[_num_bits - 1];
		_bits[_num_bits - 1] = ullong( 1 );
		for ( i = 0; _bits[i] == ullong( 0 ); i++ ) {}
		_bits[_num_bits - 1] = tmp;
		return _bits[i] == ullong( 0 );
	}
	unsigned Size() const
	{
		unsigned size = Binary_Bit_One_Num( _bits[0] );
		for ( unsigned i = 1; i < _num_bits; i++ ) size += Binary_Bit_One_Num( _bits[i] );
		return size;
	}
	bool In( const unsigned elem )
	{
		if ( elem > _max_elem ) {
			cerr << "ERROR[BoundedSet::In]: invalid element!" << endl;
			exit( 1 );
		}
		unsigned q = elem / ULLONG_SIZE, r = elem % ULLONG_SIZE;
		ullong mask = ullong( 1 ) << r;
		return ( _bits[q] & mask ) != ullong( 0 );
	}
	unsigned operator [] ( unsigned i )  // the i-th element
	{
		unsigned q = 0, num_ones;
		for ( q = 0; q < _num_bits; q++ ) {
			num_ones =  Binary_Bit_One_Num( _bits[q] );
			if ( i < num_ones ) break;
			i -= num_ones;
		}
		if ( q == _num_bits ) {
			cerr << "ERROR[BoundedSet::[]]: invalid element!" << endl;
			exit( 1 );
		}
		unsigned elem = q * ULLONG_SIZE;
		ullong mask = 1;
		i -= ( ( _bits[q] & mask ) != ullong( 0 ) );
		while ( i != UNSIGNED_UNDEF ) {
			elem++;
			mask <<= 1;
			i -= ( ( _bits[q] & mask ) != ullong( 0 ) );
		}
		return elem;
	}
	bool operator == ( const BoundedSet & other )
	{
		bool same = ( _bits[0] == other._bits[0] );
		for ( unsigned i = 1; i < _num_bits; i++ ) same = same && ( _bits[i] == other._bits[i] );
		return same;
	}
	BoundedSet & operator = ( const BoundedSet & other )
	{
		_bits[0] = other._bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) _bits[i] = other._bits[i];
		return *this;
	}
	void Add_Element( const unsigned elem )
	{
		if ( elem > _max_elem ) {
			cerr << "ERROR[BoundedSet::Add_Element]: invalid element!" << endl;
			exit( 1 );
		}
		unsigned q = elem / ULLONG_SIZE, r = elem % ULLONG_SIZE;
		ullong mask = 1 << r;
		_bits[q] = _bits[q] | mask;
	}
	BoundedSet operator ~ () const  // complement
	{
		BoundedSet set;
		set._bits[0] = ~_bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) set._bits[i] = ~_bits[i];
		return set;
	}
	void operator &= ( const BoundedSet & other )  // intersection
	{
		_bits[0] &= other._bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) _bits[i] &= other._bits[i];
	}
	void operator |= ( const BoundedSet & other )  // union
	{
		_bits[0] |= other._bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) _bits[i] |= other._bits[i];
	}
	unsigned Key()
	{
		ullong key = _bits[0];
		for ( unsigned i = 1; i < _num_bits; i++ ) {
			key = PAIR( key, _bits[i] );
		}
		unsigned low = key & ullong( UNSIGNED_UNDEF ), high = key >> UNSIGNED_SIZE;
		return PAIR( low, high );
	}
	void Display( ostream & out )
	{
		unsigned i;
		if ( Empty() ) out << "{}";
		else {
			out << "{";
			if ( In( 0 ) ) out << 0;
			for ( i = 1; i < _max_elem; i++ ) {
				if ( In( i ) ) out << ", " << i;
			}
			out << "}";
		}
	}
};

class BitSet_Reference
{
protected:
	unsigned & _bits;
	unsigned _pos;
public:
	BitSet_Reference( unsigned & bits, unsigned pos ): _bits( bits ), _pos( pos ) {}
	BitSet_Reference & operator = ( const bool value )
	{
		unsigned mask = 1 << _pos;
		mask = ~mask;
		_bits &= mask;
		mask = value << _pos;
		_bits |= mask;
		return *this;
	}
	operator bool ()
	{
		unsigned mask = 1 << _pos;
		return _bits & mask;
	}
};

class BitSet
{
protected:
	unsigned * _bits;
	unsigned _size;
public:
	BitSet( const unsigned size )
	{
		unsigned num = Num_Bits( size );
		_bits = new unsigned [num];
	}
	BitSet( const unsigned size, bool value )
	{
		unsigned num = Num_Bits( size );
		_bits = new unsigned [num];
		unsigned integrated_value = value ? UNSIGNED_UNDEF : 0;
		for ( unsigned i = 0; i < num; i++ ) {
			_bits[i] = integrated_value;
		}
	}
	~BitSet() { delete [] _bits; }
	BitSet_Reference operator [] ( const unsigned pos )
	{
		unsigned q = pos / UNSIGNED_SIZE, r = pos % UNSIGNED_SIZE;
		return BitSet_Reference( _bits[q], r );
	}
	void Display( ostream & out )
	{
		if ( _size == 0 ) return;
		for ( unsigned i = 0; i < _size; i++ ) {
			out << (*this)[i];
		}
	}
protected:
	unsigned Num_Bits( unsigned size )
	{
		return ( size + UNSIGNED_SIZE - 1 ) / UNSIGNED_SIZE;
	}
};


typedef unsigned SetID;
#define SETID_UNDEF (unsigned (-1))
#define SETID_EMPTY 0

template<class T>
class Hash_Cluster
{
protected:
	unsigned _fullset_size;
	Hash_Table<SortedSet<T>> _sets;
	T * _many_elems;
	unsigned * _records;
public:
	Hash_Cluster( unsigned fullset_size, unsigned num_entries = MEDIAN_HASH_TABLE ): _fullset_size( fullset_size ), _sets( num_entries )
	{
		_many_elems = new T [_fullset_size];
		_records = new unsigned [_fullset_size];
		SortedSet<T> set( nullptr, 0 );
		_sets.Hit( set );
	}
	~Hash_Cluster()
	{
		for ( unsigned i = 1; i < _sets.Size(); i++ ) {  // the first set is the empty set
			delete [] _sets[i].elems;
		}
		delete [] _many_elems;
		delete [] _records;
	}
	void Clear()
	{
		for ( unsigned i = 1; i < _sets.Size(); i++ ) {  // the first set is the empty set
			delete [] _sets[i].elems;
		}
		_sets.Resize( 1 );
	}
	void Enlarge_Fullset( unsigned new_size )
	{
		if ( new_size <= _fullset_size ) return;
		_fullset_size = new_size;
		delete [] _many_elems;
		delete [] _records;
		_many_elems = new T [_fullset_size];
		_records = new unsigned [_fullset_size];
	}
	unsigned Size() const { return _sets.Size(); }
	size_t Memory() const { return _sets.Memory() + sizeof(T) * _fullset_size + sizeof(unsigned) * _fullset_size; }
	const SortedSet<T> Elements( SetID s ) { return _sets[s]; }
	const SortedSet<T> operator [] ( SetID s ) { return _sets[s]; }
	SetID EmptySet() { return 0; }
	bool Existed( const SortedSet<T> & set ) { return _sets.Location( set ) != SIZET_UNDEF; }
	SetID Singleton( T elem )
	{
		SortedSet<T> set( &elem, 1 );
		unsigned old_size = _sets.Size(), pos = _sets.Hit( set );
		if ( pos == old_size ) {
			_sets[pos].Realloc();
			_sets[pos][0] = elem;
		}
		return pos;
	}
	SetID Binary_Set( T elem, T elem2 )
	{
	    assert( elem != elem2 );
	    T elems[2];
		if ( elem < elem2 ) { elems[0] = elem; elems[1] = elem2; }
		else { elems[0] = elem2; elems[1] = elem; }
		SortedSet<T> set( elems, 2 );
		unsigned old_size = _sets.Size(), pos = _sets.Hit( set );
		if ( pos == old_size ) {
			_sets[pos].Realloc();
			_sets[pos][0] = elems[0];
			_sets[pos][1] = elems[1];
		}
		return pos;
	}
	SetID Binary_Set_ID( T elem, T elem2 )
	{
	    assert( elem != elem2 );
	    T elems[2];
		if ( elem < elem2 ) { elems[0] = elem; elems[1] = elem2; }
		else { elems[0] = elem2; elems[1] = elem; }
		SortedSet<T> set( elems, 2 );
		return _sets.Location( set );
	}
	SetID Set( T * elems, unsigned size )  // NOTE: elems needs to be sorted
	{
		if ( size > _fullset_size ) {  // ToRemove
			cerr << "{" << elems[0];
			for ( unsigned i = 1; i < size; i++ ) cerr << ", " << elems[i];
			cerr << "}";
			assert( size <= _fullset_size );
		}
		if ( DEBUG_OFF && size > 1 ) {
			for ( unsigned i = 0; i < size - 1; i++ ) {
				if ( elems[i] >= elems[i+1] ) {  // ToRemove
					cerr << "{" << elems[0];
					for ( unsigned i = 1; i < size; i++ ) cerr << ", " << elems[i];
					cerr << "}";
					assert( elems[i] < elems[i+1] );
				}
			}
		}
		SortedSet<T> set( elems, size );
		unsigned old_size = _sets.Size(), pos = _sets.Hit( set );
		if ( pos == old_size ) {
			_sets[pos].Realloc();  // NOTE: replace nodes[pos].ch by a dynamic array
			for ( unsigned i = 0; i < size; i++ ) _sets[pos][i] = elems[i];
		}
		return pos;
	}
	bool In( SetID s, T elem )
	{
		if ( _sets[s].size == 0 ) return false;
		return Search_Exi_Nonempty( _sets[s].elems, _sets[s].size, elem );
	}
	SetID Remove( SetID s, T elem )
	{
		if ( !In( s, elem ) ) return s;
		SortedSet<T> & set = _sets[s];
		Set_Dec_Element( set.elems, set.size, elem, _many_elems );
		return Set( _many_elems, set.size - 1 );
	}
	SetID Intersection( SetID s1, SetID s2 )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		unsigned size = KCBox::Intersection( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		return Set( _many_elems, size );
	}
	SetID Union( SetID s1, SetID s2 )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		unsigned size = KCBox::Union( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		return Set( _many_elems, size );
	}
	SetID Union( SetID s, const T & elem )
	{
		SortedSet<T> & set = _sets[s];
		unsigned i, pos = Search_First_GE_Pos( set.elems, set.size, elem );
		if ( _many_elems[pos] == elem ) return s;
		for ( i = 0; i < pos; i++ ) {
			_many_elems[i] = set.elems[i];
		}
		_many_elems[i] = elem;
		for ( ; i < set.size; i++ ) {
			_many_elems[i+1] = set.elems[i];
		}
		return Set( _many_elems, set.size + 1 );
	}
	SetID Union( SetID s1, SetID s2, const T & elem )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		unsigned i, size = KCBox::Union( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		unsigned pos = Search_First_GE_Pos( _many_elems, size, elem );
		ASSERT( pos == size || _many_elems[pos] != elem );
		if ( pos == size ) _many_elems[size++] = elem;
		else if ( _many_elems[pos] != elem ) {
			for ( i = size-1; i > pos; i-- ) {
				_many_elems[i+1] = _many_elems[i];
			}
			_many_elems[pos+1] = _many_elems[pos];
			_many_elems[pos] = elem;
			size++;
		}
		return Set( _many_elems, size );
	}
	SetID Union_Disjoint( SetID s1, SetID s2 )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		unsigned i = 0, j = 0, k = 0;
		while ( i < set1.size && j < set2.size ) {
			if ( set1[i] < set2[j] ) _many_elems[k++] = set1[i++];
			else _many_elems[k++] = set2[j++];
		}
		while ( i < set1.size ) _many_elems[k++] = set1[i++];
		while ( j < set2.size ) _many_elems[k++] = set2[j++];
		return Set( _many_elems, k );
	}
	SetID Union_Disjoint( SetID s1, SetID s2, const T & elem )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		unsigned i, size = KCBox::Union_Disjoint( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		unsigned pos = Search_First_GE_Pos( _many_elems, size, elem );
		ASSERT( pos == size || _many_elems[pos] != elem );
		if ( pos == size ) _many_elems[size++] = elem;
		else if ( _many_elems[pos] != elem ) {
			for ( i = size-1; i > pos; i-- ) {
				_many_elems[i+1] = _many_elems[i];
			}
			_many_elems[pos+1] = _many_elems[pos];
			_many_elems[pos] = elem;
			size++;
		}
		return Set( _many_elems, size );
	}
	SetID Union_Disjoint( SetID s, const T * elems, unsigned size )  // NOTE: elems needs to be sorted
	{
		SortedSet<T> & set = _sets[s];
		unsigned i = 0, j = 0, k = 0;
		while ( i < set.size && j < size ) {
			if ( set[i] < elems[j] ) _many_elems[k++] = set[i++];
			else _many_elems[k++] = elems[j++];
		}
		while ( i < set.size ) _many_elems[k++] = set[i++];
		while ( j < size ) _many_elems[k++] = elems[j++];
		return Set( _many_elems, k );
	}
	SetID Union_Disjoint( SetID s, const T * elems, unsigned size, const T & elem )
	{
		SortedSet<T> & set = _sets[s];
		unsigned i, new_size = KCBox::Union_Disjoint( set.elems, set.size, elems, size, _many_elems );
		unsigned pos = Search_First_GE_Pos( _many_elems, new_size, elem );
		ASSERT( pos == new_size || _many_elems[pos] != elem );
		if ( pos == new_size ) _many_elems[new_size++] = elem;
		else if ( _many_elems[pos] != elem ) {
			for ( i = new_size-1; i > pos; i-- ) {
				_many_elems[i+1] = _many_elems[i];
			}
			_many_elems[pos+1] = _many_elems[pos];
			_many_elems[pos] = elem;
			new_size++;
		}
		return Set( _many_elems, new_size );
	}
	SetID Union_Disjoint( SetID * sets, unsigned num )  // NOTE: sets will be changed
	{
		unsigned i, size = 0;
		for ( i = 0; i < num; i++ ) {
			_records[i] = 0;
		}
		while ( true ) {
			while ( _records[0] == _sets[sets[0]].size && num > 0 ) {  // remove the sets whose elements are pushed into _many_elems
				sets[0] = sets[num - 1];
				_records[0] = _records[num - 1];
				num--;
			}
			if ( num == 0 ) break;
			T min_element = _sets[sets[0]][_records[0]];
			size_t min_array = 0;
			for ( i = 1; i < num; i++ ) {
				SortedSet<T> & set = _sets[sets[i]];
				if ( _records[i] == set.size ) {
					sets[i] = sets[num - 1];
					_records[i] = _records[num - 1];
					num--;
					i--;
					continue;
				}
				if ( set[_records[i]] < min_element ) {
					min_element = set[_records[i]];
					min_array = i;
				}
			}
			_many_elems[size++] = min_element;
			_records[min_array]++;
		}
		return Set( _many_elems, size );
	}
	SetID Difference( SetID s1, SetID s2 )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		size_t size = KCBox::Difference( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		return Set( _many_elems, size );
	}
	SetID Differece_Subset( SetID s1, SetID s2 )
	{
		SortedSet<T> & set1 = _sets[s1];
		SortedSet<T> & set2 = _sets[s2];
		KCBox::Difference_Subset( set1.elems, set1.size, set2.elems, set2.size, _many_elems );
		return Set( _many_elems, set1.size - set2.size );
	}
	SetID Differece_Subset( SetID s, const T * elems, unsigned size )
	{
		SortedSet<T> & set = _sets[s];
		KCBox::Difference_Subset( set.elems, set.size, elems, size, _many_elems );
		return Set( _many_elems, set.size - size );
	}
	void Display( ostream & out )
	{
		for ( unsigned i = 0; i < _sets.Size(); i++ ) {
			out << i << ": ";
			SortedSet<T> & set = _sets[i];
			set.Display( out );
			out << endl;
		}
	}
};


/****************************************************************************************************
*                                                                                                   *
*                                            Sorter                                                 *
*                                                                                                   *
****************************************************************************************************/

class QSorter
{
protected:
	const unsigned threshold;  // when the number of elements is less than threshold, we will employ the insertion sort
	BigVector<pair<unsigned, unsigned>> call_stack;  // record the beginnings and ends in the calling stack
public:
	QSorter(): threshold( 16 ), call_stack( 1023 ) {}
	~QSorter() {}
	template<typename T> void Sort( T * data, unsigned size )
	{
		if ( size <= 1 ) return;
		unsigned i, j;
		call_stack.Enlarge( size );
		T tmp;
		for ( i = j = size - 1; i > 0; i-- ) { // validate the following insertion_sort
			if ( data[i] < data[i-1] ) {
				j = i;
				tmp = data[i-1];
				data[i-1] = data[i];
				data[i] = tmp;
			}
		}
		pair<size_t, size_t> record( j, size - 1 );  // elements in the interval [j, size - 1];
		call_stack.Push_Back( record );
		while ( !call_stack.Empty() ) {
			record = call_stack.Back();
			if ( record.first + threshold > record.second ) {  /// second might be less than first
				for ( i = record.first + 1; i <= record.second; i++ ) {
					tmp = data[i];
					for ( j = i - 1; data[j] > tmp; j-- ) {
						data[j+1] = data[j];
					}
					data[j+1] = tmp;
				}
				call_stack.Pop_Back();
			}
			else {
				unsigned pos = ( record.first + record.second ) / 2;
				if ( ( data[record.first] < data[pos] ) + ( data[pos] < data[record.second] ) == 1 ) {
					if ( ( data[record.first] < data[pos] ) + ( data[record.first] < data[record.second] ) == 1 )
						pos = record.first;
					else pos = record.second;
				}
				T pivot = data[pos];
				data[pos] = data[record.second];
				for ( i = record.first; data[i] < pivot; i++ );
				for ( j = record.second - 1; data[j] > pivot; j-- );
				while ( i < j ) {
					tmp = data[i];
					data[i++] = data[j];
					data[j--] = tmp;
					for ( ; data[i] < pivot; i++ );
					for ( ; data[j] > pivot; j-- );
				}
				data[record.second] = data[i];
				data[i] = pivot;
				call_stack.Back().second = i - 1;  // .second = j is less efficient when i = j
				call_stack.Push_Back( pair<size_t, size_t>( i + 1, record.second ) );
			}
		}
	}
	template<typename T> void Sort( vector<T> & data )
	{
		if ( data.size() <= 1 ) return;
		unsigned i, j;
		call_stack.Enlarge( data.size() );
		T tmp;
		for ( i = j = data.size() - 1; i > 0; i-- ) { // validate the following insertion_sort
			if ( data[i] < data[i-1] ) {
				j = i;
				tmp = data[i-1];
				data[i-1] = data[i];
				data[i] = tmp;
			}
		}
		pair<size_t, size_t> record( j, data.size() - 1 );  // elements in the interval [j, size - 1];
		call_stack.Push_Back( record );
		while ( !call_stack.Empty() ) {
			record = call_stack.Back();
			if ( record.first + threshold > record.second ) {  /// second might be less than first
				for ( i = record.first + 1; i <= record.second; i++ ) {
					tmp = data[i];
					for ( j = i - 1; data[j] > tmp; j-- ) {
						data[j+1] = data[j];
					}
					data[j+1] = tmp;
				}
				call_stack.Pop_Back();
			}
			else {
				unsigned pos = ( record.first + record.second ) / 2;
				if ( ( data[record.first] < data[pos] ) + ( data[pos] < data[record.second] ) == 1 ) {
					if ( ( data[record.first] < data[pos] ) + ( data[record.first] < data[record.second] ) == 1 )
						pos = record.first;
					else pos = record.second;
				}
				T pivot = data[pos];
				data[pos] = data[record.second];
				for ( i = record.first; data[i] < pivot; i++ );
				for ( j = record.second - 1; data[j] > pivot; j-- );
				while ( i < j ) {
					tmp = data[i];
					data[i++] = data[j];
					data[j--] = tmp;
					for ( ; data[i] < pivot; i++ );
					for ( ; data[j] > pivot; j-- );
				}
				data[record.second] = data[i];
				data[i] = pivot;
				call_stack.Back().second = i - 1;  // .second = j is less efficient when i = j
				call_stack.Push_Back( pair<size_t, size_t>( i + 1, record.second ) );
			}
		}
	}
	template<typename W> void Sort( vector<unsigned> & data, const W & rank )
	{
		if ( data.size() <= 1 ) return;
		unsigned i, j, tmp;
		call_stack.Enlarge( data.size() );
		for ( i = j = data.size() - 1; i > 0; i-- ) {  // validate the following insertion_sort
			if ( rank[data[i]] < rank[data[i-1]] ) {
				j = i;
				tmp = data[i-1];
				data[i-1] = data[i];
				data[i] = tmp;
			}
		}
		pair<size_t, size_t> record( j, data.size() - 1 );  // elements in the interval [j, data.size() - 1];
		call_stack.Push_Back( record );
		while ( !call_stack.Empty() ) {
			record = call_stack.Back();
			if ( record.first + threshold > record.second ) {  /// second might be less than first
				for ( i = record.first + 1; i <= record.second; i++ ) {
					tmp = data[i];
					for ( j = i - 1; rank[data[j]] > rank[tmp]; j-- ) {
						data[j+1] = data[j];
					}
					data[j+1] = tmp;
				}
				call_stack.Pop_Back();
			}
			else {
				unsigned pos = ( record.first + record.second ) / 2;
				if ( ( rank[data[record.first]] < rank[data[pos]] ) + ( rank[data[pos]] < rank[data[record.second]] ) == 1 ) {
					if ( ( rank[data[record.first]] < rank[data[pos]] ) + ( rank[data[record.first]] < rank[data[record.second]] ) == 1 )
						pos = record.first;
					else pos = record.second;
				}
				unsigned pivot = data[pos];
				data[pos] = data[record.second];
				for ( i = record.first; rank[data[i]] < rank[pivot]; i++ );
				for ( j = record.second - 1; rank[data[j]] > rank[pivot]; j-- );
				while ( i < j ) {
					tmp = data[i];
					data[i++] = data[j];
					data[j--] = tmp;
					for ( ; rank[data[i]] < rank[pivot]; i++ );
					for ( ; rank[data[j]] > rank[pivot]; j-- );
				}
				data[record.second] = data[i];
				data[i] = pivot;
				call_stack.Back().second = i - 1;  // .second = j is less efficient when i = j
				call_stack.Push_Back( pair<size_t, size_t>( i + 1, record.second ) );
			}
		}
	}
	template<typename W> void Sort_Reverse( vector<unsigned> & data, W & rank )
	{
		if ( data.size() <= 1 ) return;
		unsigned i, j, tmp;
		call_stack.Enlarge( data.size() );
		for ( i = j = data.size() - 1; i > 0; i-- ) {  // validate the following insertion_sort
			if ( rank[data[i]] > rank[data[i-1]] ) {
				j = i;
				tmp = data[i-1];
				data[i-1] = data[i];
				data[i] = tmp;
			}
		}
		pair<size_t, size_t> record( j, data.size() - 1 );  // elements in the interval [j, data.size() - 1];
		call_stack.Push_Back( record );
		while ( !call_stack.Empty() ) {
			record = call_stack.Back();
			if ( record.first + threshold > record.second ) {  /// second might be less than first
				for ( i = record.first + 1; i <= record.second; i++ ) {
					tmp = data[i];
					for ( j = i - 1; rank[data[j]] < rank[tmp]; j-- ) {
						data[j+1] = data[j];
					}
					data[j+1] = tmp;
				}
				call_stack.Pop_Back();
			}
			else {
				unsigned pos = ( record.first + record.second ) / 2;
				if ( ( rank[data[record.first]] > rank[data[pos]] ) + ( rank[data[pos]] > rank[data[record.second]] ) == 1 ) {
					if ( ( rank[data[record.first]] > rank[data[pos]] ) + ( rank[data[record.first]] > rank[data[record.second]] ) == 1 )
						pos = record.first;
					else pos = record.second;
				}
				unsigned pivot = data[pos];
				data[pos] = data[record.second];
				for ( i = record.first; rank[data[i]] > rank[pivot]; i++ );
				for ( j = record.second - 1; rank[data[j]] < rank[pivot]; j-- );
				while ( i < j ) {
					tmp = data[i];
					data[i++] = data[j];
					data[j--] = tmp;
					for ( ; rank[data[i]] > rank[pivot]; i++ );
					for ( ; rank[data[j]] < rank[pivot]; j-- );
				}
				data[record.second] = data[i];
				data[i] = pivot;
				call_stack.Back().second = i - 1;  // .second = j is less efficient when i = j
				call_stack.Push_Back( pair<size_t, size_t>( i + 1, record.second ) );
			}
		}
	}
};


/****************************************************************************************************
*                                                                                                   *
*                                         Heap                                                      *
*                                                                                                   *
****************************************************************************************************/

template<class T, class W>
class Heap
{
protected:
    vector<T> _elems;  // Heap of elements
    vector<int> _indices;  // Each element's position (index) in the Heap, an unsigned 0 minus 1 is invalid
    W * _weights;  // The heap is a maximum-heap with respect to the weight of each element
protected:
    int Num_Elems() { return (int) _elems.size(); }
    static inline int Left( int i ) { return i*2+1; }
    static inline int Right( int i ) { return (i+1)*2; }
    static inline int Parent( int i ) { return (i-1) >> 1; } // 0's parent is -1
    static inline bool Is_Root( int i ) { return i == 0; }
    bool Is_Leaf( int i ) { return Left( i ) >= Num_Elems(); }
    int Last_Internal() { return Parent( Num_Elems() - 1 ); }
    void Sift_Up( int i )
    {
        T elem = _elems[i];
        int p = Parent(i);
        while ( !Is_Root( i ) && _weights[elem] > _weights[_elems[p]] ){
            _elems[i] = _elems[p];
            _indices[_elems[i]] = i;
            i = p;
            p = Parent(p);
        }
        _elems[i] = elem;
        _indices[elem] = i;
        if ( DEBUG_OFF ) Verify();
    }
    void Sift_Down( int i )
    {
    	if ( Is_Leaf( i ) ) return;
        T elem = _elems[i];
    	int last = Parent( Num_Elems() - 2 );  // the last node with two children
        while ( i <= last ) {
            int child = _weights[_elems[Left(i)]] > _weights[_elems[Right(i)]] ? Left(i) : Right(i);
            if ( _weights[_elems[child]] <= _weights[elem] ) break;
            _elems[i] = _elems[child];
            _indices[_elems[i]] = i;
            i = child;
        }
        if ( !Is_Leaf( i ) && Right( i ) >= Num_Elems() ) {  // with only the left child
            int child = Left(i);
            if ( _weights[_elems[child]] > _weights[elem] ) {
				_elems[i] = _elems[child];
				_indices[_elems[i]] = i;
				i = child;
            }
        }
        _elems[i] = elem;
        _indices[elem] = i;
    }
    void Verify()
    {
    	if ( Empty() ) return;
		assert( _indices[_elems[0]] == 0 );
    	assert( Parent( 0 ) == -1 );
		for ( int i = 1; i < Num_Elems(); i++ ) {
            assert( _indices[_elems[i]] == i );
            if ( _weights[_elems[i]] > _weights[_elems[Parent( i )]] ) {
				cerr << "ERROR[Heap]: _elems[" << i << "] = " << (unsigned)_elems[i]
					<< " is greater than _elems[" << Parent( i ) << "] = " << (unsigned)_elems[Parent( i )] << endl;
				assert( _weights[_elems[i]] <= _weights[_elems[Parent( i )]] );
            }
		}
		unsigned num = 0;
		for ( unsigned i = 0; i < _indices.size(); i++ ) {
            num += ( _indices[i] != -1 );
 		}
 		assert( num == _elems.size() );
	}
public:
    Heap( unsigned max_index, W * weights ): _indices( max_index + 1, -1 ), _weights( weights ) {}
    void operator = ( Heap<T, W> & another )
    {
		_elems = another._elems;
		_indices = another._indices;
		for ( T & elem: _elems ) {
			assert( _weights[elem] == another._weights[elem] );
		}
    }
    void Enlarge_Index( unsigned max_index, W * weights )
    {
    	_weights = weights;
    	if ( max_index < _indices.size() ) return;
    	unsigned old_size = _indices.size();
    	_indices.resize( max_index + 1 );
    	for ( unsigned i = old_size; i <= max_index; i++ ) {
			_indices[i] = -1;
    	}
	}
    unsigned Size() const { return _elems.size(); }
    bool Empty () const { return _elems.empty(); }
    bool Contain( T elem ) const { return _indices[elem] != -1; }
    T operator[] ( unsigned i ) const { ASSERT( i < _elems.size() );  return _elems[i]; }
    void Insert( T elem )
    {
        if( Contain( elem ) ) return;
        _indices[elem] = _elems.size();
        _elems.push_back( elem );
		Sift_Up( _indices[elem] );
    }
	void Update( T elem )
	{
		ASSERT( Contain( elem ) );
		int i = _indices[elem], p = Parent( i );
		if ( _weights[elem] >= _weights[_elems[p]] ) Sift_Up( i );
		else Sift_Down( i );
	}
	void Prioritize( T elem ) { if ( Contain( elem ) ) Sift_Up( _indices[elem] ); }
	void Erase( T elem )
    {
        ASSERT( Contain( elem ) );
        int i  = _indices[elem];
        _indices[elem] = -1;
        if ( i < _elems.size()-1 ){
            _elems[i] = _elems.back();
            _indices[_elems[i]] = i;
            _elems.pop_back();
            int p = Parent( i );
            if ( !Is_Root( i ) && _weights[_elems[p]] < _indices[_elems[i]] ) Sift_Up( i );
            else Sift_Down( i );
        }
        else _elems.pop_back();
    }
    T Extract_Max()
    {
        T elem = _elems[0];
        _indices[elem] = -1;
        if ( _elems.size() == 1 ) {
			_elems.clear();
			return elem;
        }
        _elems[0] = _elems.back();
        _indices[_elems[0]] = 0;
        _elems.pop_back();
        Sift_Down( 0 );  // for empty heap, this statement is valid
		if ( DEBUG_OFF ) Verify();
        return elem;
    }
    void Build( const T elems[], const unsigned size )
    {
    	Clear();
    	_elems.resize( size );
        for ( unsigned i = 0; i < size; i++ ) {
            ASSERT( !Contain( elems[i] ) );
			_elems[i] = elems[i];
            _indices[elems[i]] = i;
		}
        for ( int i = Last_Internal(); i >= 0; i--) {
            Sift_Down( i );
        }
		if ( DEBUG_OFF ) Verify();
	}
    void Clear()
    {
        for ( unsigned i = 0; i < _elems.size(); i++ ) {
            _indices[_elems[i]] = -1;
        }
        _elems.clear();
    }
};



/****************************************************************************************************
*                                                                                                   *
*                                            Random Generator                                       *
*                                                                                                   *
****************************************************************************************************/

class Random_Generator
{
protected:
	int _seed;
	CRandomMersenne _rand_gen;  // choose one of the random number generators
public:
	Random_Generator() : _seed( (int) time(NULL) ), _rand_gen( _seed ) {}
	Random_Generator( int seed ) : _seed( seed ), _rand_gen( seed ) {}
	void Reset( int seed ) { _seed = seed; _rand_gen.RandomInit( seed ); }
	double Generate_Double() { return _rand_gen.Random(); }
	int Generate_Int() { return _rand_gen.BRandom(); }
	int Generate_Int( int min, int max ) { return _rand_gen.IRandomX( min, max ); }
	bool Generate_Bool( double p )
	{
		assert( 0 <= p && p <= 1 );
		double result = _rand_gen.Random();
		return result < p;  // This will happen with probability p
	}
public:
	static void Debug()
	{
		Random_Generator gen;
		for ( unsigned i = 0; i < 10; i++ ) {
			if ( gen.Generate_Bool( 0.4 ) ) cout << "TRUE" << endl;
			else cout << "FALSE" << endl;
		}

	}
};


}


#endif
