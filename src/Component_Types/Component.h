#ifndef _Component_h_
#define _Component_h_

#include "../Template_Library/Basic_Functions.h"
#include "../Template_Library/Basic_Structures.h"
#include "../Template_Library/BigNum.h"
#include "../Primitive_Types/CNF_Formula.h"


namespace KCBox {


#ifndef CACHEENTRYID_64BITS
typedef unsigned cache_size_t;
#else
typedef size_t cache_size_t;
#endif // CACHEENTRYID_64BITS

class CacheEntryID: public Identity<cache_size_t>
{
public:
	CacheEntryID() {}
	CacheEntryID( cache_size_t id ): Identity<cache_size_t>( id ) {}
	CacheEntryID( const CacheEntryID &cid ): Identity<cache_size_t>( cid._id ) {}
	CacheEntryID & operator = ( CacheEntryID cid ) { _id = cid._id; return *this; }
	bool operator == (const CacheEntryID &other) const { return _id == other._id; }
	bool operator == (const cache_size_t other) const { return _id == other; }
	bool operator == (const int other) const { return _id == cache_size_t(other); }
	const static CacheEntryID undef;
};


class Component
{
protected:
	vector<unsigned> _varIDs;
	vector<unsigned> _clauseIDs;  // denote the ID of clauses
public:
	CacheEntryID caching_loc;
	unsigned Vars_Size() const { return _varIDs.size(); }
	unsigned ClauseIDs_Size() const { return _clauseIDs.size(); }
	void Vars_Resize( unsigned newsize ) { _varIDs.resize( newsize ); }
	void ClauseIDs_Resize( unsigned newsize ) { _clauseIDs.resize( newsize ); }
	unsigned Capacity() const { return _varIDs.capacity() + _clauseIDs.capacity(); }
	void Add_Var( Variable var ) { _varIDs.push_back( var ); }
	void Dec_Var() { _varIDs.pop_back(); }
	void Add_ClauseID( unsigned clause ) { _clauseIDs.push_back( clause ); }
	const vector<unsigned> & VarIDs() { return _varIDs; }
	Variable Vars( unsigned i ) { return Variable( _varIDs[i] ); }
	unsigned ClauseIDs( unsigned i ) { return _clauseIDs[i]; }
	vector<unsigned>::const_iterator VarIDs_Begin() { return _varIDs.cbegin(); }
	vector<unsigned>::const_iterator VarIDs_End() { return _varIDs.cend(); }
	vector<unsigned>::const_iterator ClauseIDs_Begin() { return _clauseIDs.cbegin(); }
	vector<unsigned>::const_iterator ClauseIDs_End() { return _clauseIDs.cend(); }
	void Clear() { _varIDs.clear(); _clauseIDs.clear(); }
	void Clear_Vars() { _varIDs.clear(); }
	void Clear_ClauseIDs() { _clauseIDs.clear(); }
	bool Search_Var( Variable var ) { return Search_Exi_Nonempty( _varIDs, unsigned(var) ); }
	bool Search_ClauseID( unsigned cl ) { return Search_Exi_Nonempty( _clauseIDs, cl ); }
	void Sort( QSorter & sorter ) { sorter.Sort( _varIDs ); sorter.Sort( _clauseIDs ); }
	void Sort_Vars( QSorter & sorter ) { sorter.Sort( _varIDs ); }
	void Sort_ClauseIDs( QSorter & sorter ) { sorter.Sort( _clauseIDs ); }
	bool Trivial( const unsigned bound ) { return _varIDs.size() - 1 <= bound && _clauseIDs.size() <= 2 * bound; }
	void Swap( Component & other ) { _varIDs.swap( other._varIDs ); _clauseIDs.swap( other._clauseIDs ); swap( caching_loc, other.caching_loc ); }
	void Swap_VarIDs( Component & other ) { _varIDs.swap( other._varIDs ); }
	void Swap_ClauseIDs( vector<unsigned> & clause_IDs ) { _clauseIDs.swap( clause_IDs ); }
	bool operator == ( Component & other )
	{
		if ( _varIDs.size() != other._varIDs.size() || _clauseIDs.size() != other._clauseIDs.size() ) return false;
		for ( unsigned i = 0; i < _varIDs.size(); i++ ) {
			if ( _varIDs[i] != other._varIDs[i] ) return false;
		}
		for ( unsigned i = 0; i < _clauseIDs.size(); i++ ) {
			if ( _clauseIDs[i] != other._clauseIDs[i] ) return false;
		}
		return true;
	}
	bool operator != ( Component & other )
	{
		if ( _varIDs.size() != other._varIDs.size() || _clauseIDs.size() != other._clauseIDs.size() ) return true;
		for ( unsigned i = 0; i < _varIDs.size(); i++ ) {
			if ( _varIDs[i] != other._varIDs[i] ) return true;
		}
		for ( unsigned i = 0; i < _clauseIDs.size(); i++ ) {
			if ( _clauseIDs[i] != other._clauseIDs[i] ) return true;
		}
		return false;
	}
	void Display( ostream & fout )
	{
		assert( _varIDs.size() >= 1 );
		unsigned i;
		fout << "varIDs: ";
		for ( i = 0; i < _varIDs.size(); i++ ) fout << _varIDs[i] << " ";
		fout << endl;
		fout << "clauseIDs: ";
		for ( i = 0; i < _clauseIDs.size(); i++ ) fout << _clauseIDs[i] << " ";
		fout << endl;
	}
};


}


#endif
