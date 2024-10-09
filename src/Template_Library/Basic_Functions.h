#ifndef _Basic_Functions_h_
#define _Basic_Functions_h_

#include <cassert>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <sys/time.h>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <stack>
#include <queue>
#include <map>
#include <bitset>
#include <algorithm>
#include <limits>
#include "../Debug_Library/Debug_Functions.h"
using namespace std;


namespace KCBox {


#define MAX_ELEMENT  (128 * 1024)
#define MAX_LINE	(65536 * 8)
typedef long double ldouble;
typedef unsigned long long ullong;

//#define ACTIVATE_CLHASH
#define PAIR( a, b )	( ( a + b ) * ( a + b + 1 ) / 2 + a )
#define EITHOR_ZERO( a, b ) ( !a + !b > 0 )
#define BOTH_ZERO( a, b ) ( !a + !b == 2 )
#define NEITHOR_X( a, b, x ) ( ( a == x ) + ( b == x ) == 0 )
#define EITHOR_X( a, b, x ) ( ( a == x ) + ( b == x ) > 0 )
#define BOTH_X( a, b, x ) ( ( a == x ) + ( b == x ) == 2 )
#define UNSIGNED_SIZE ( sizeof(unsigned) * 8 )
#define UNSIGNED_UNDEF	(unsigned (-1))
#define SIZET_UNDEF	(size_t (-1))
#define ULONG_SIZE ( sizeof( unsigned long ) * 8 )
#define ULONG_UNDEF	(unsigned long (-1))
#define ULLONG_SIZE ( sizeof( unsigned long long ) * 8 )
#define ULLONG_UNDEF	((unsigned long long) (-1))
#define RAND_SEED	((unsigned)time( NULL ))
#define BLANK_CHAR( ch )  ( ch == ' ' || ch == '\t' )
#define BLANK_CHAR_GENERAL( ch )  ( ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n' )
#define DIGIT_CHAR( ch )  ( '0' <= ch && ch <= '9' )

#define UNUSED(x) (void)(x)


/**************************************** number ****************************************/

extern inline unsigned Binary_Bit_Num( unsigned num )
{
	unsigned i;
	for ( i = 0; num > 0; i++ ) num >>= 1;
	return i;
}

extern inline unsigned Binary_Bit_Num_2step( unsigned num )
{
	unsigned i;
	for ( i = 0; num > 1; i++ ) num >>= 2;  // ToDo: right shift 2 bits
	return i + i + ( num > 0 );
}

extern inline int Log2( unsigned v )
{
	#define SIXTEEN(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n
	static const int8_t log_table256[256] = { -1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
		SIXTEEN(4), SIXTEEN(5), SIXTEEN(5), SIXTEEN(6), SIXTEEN(6), SIXTEEN(6), SIXTEEN(6),
		SIXTEEN(7), SIXTEEN(7), SIXTEEN(7), SIXTEEN(7), SIXTEEN(7), SIXTEEN(7), SIXTEEN(7), SIXTEEN(7)
	};
	unsigned int t, tt; // temporaries
	if ((tt = v >> 16) != 0) return ((t = tt >> 8) != 0) ? 24 + log_table256[t] : 16 + log_table256[tt];
	else return ((t = v >> 8) != 0) ? 8 + log_table256[t] : log_table256[v];
}

extern inline unsigned Ceil_Log2( unsigned num ) // num > 0, otherwise it gives 64
{
	return Log2( num - 1 ) + 1;
}

template<typename T>
extern inline unsigned Binary_Bit_One_Num( T number )
{
    static uint8_t count_table[] = {0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, \
                                    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, \
                                    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, \
                                    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, \
                                    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, \
                                    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, \
                                    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, \
                                    4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8};
	unsigned count = 0;
	for ( ; number > 255; number >>= 8 ) {
        count += count_table[number & 255];
	}
    return count + count_table[number];
}

extern inline vector<bool> Bool_Vector( unsigned num ) // 0 => (); 6 => (0, 1, 1)
{
	vector<bool> result;
	for ( ; num > 0; num >>= 1 ) {
        result.push_back( num & 1 );
	}
	return result;
}

extern inline void Bool_Vector( unsigned num, vector<bool>::iterator begin, vector<bool>::iterator end ) // 0 => (); 6 => (0, 1, 1)
{
	for ( ; begin < end; begin++ ) {
        *begin = num & 1;
        num >>= 1;
	}
}

extern inline void Shift_Left_Unsafe( double & d, unsigned step )
{
	const int DOUBLE_EXP_SHIFT = 52;
	const ullong DOUBLE_MANT_MASK = (1ull << DOUBLE_EXP_SHIFT) - 1ull;
	const ullong DOUBLE_EXP_MASK = ((1ull << 63) - 1) & ~DOUBLE_MANT_MASK;
	ullong * i = (ullong *)(&d);
	if ((*i & DOUBLE_EXP_MASK) && ((*i & DOUBLE_EXP_MASK) != DOUBLE_EXP_MASK)) {
		*i += (ullong) step << DOUBLE_EXP_SHIFT;
	} else if (*i) {
		d *= (1 << step);
    }
}

extern inline void Shift_Right_Unsafe( double & d, unsigned step)
{
	const int DOUBLE_EXP_SHIFT = 52;
	const ullong DOUBLE_MANT_MASK = (1ull << DOUBLE_EXP_SHIFT) - 1ull;
	const ullong DOUBLE_EXP_MASK = ((1ull << 63) - 1) & ~DOUBLE_MANT_MASK;
	ullong * i = (ullong *)(&d);
	if ((*i & DOUBLE_EXP_MASK) && ((*i & DOUBLE_EXP_MASK) != DOUBLE_EXP_MASK)) {
		*i -= (ullong) step << DOUBLE_EXP_SHIFT;
	} else if (*i) {
		d /= (1 << step);
	}
}


/**************************************** search ****************************************/

template<typename T>
extern inline unsigned Binary_Search( const T * data, unsigned low, unsigned high, T element ) // data[high - 1] is the last element
{
	while ( low + 1 < high ) { // low < high may not quit from loop, the old version "low < high - 1" may be overflow
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;  /// mid - 1 may overflow
		else low = mid;
	}
	return low; // It is needed to be checked again outside the function
}

template<typename T>
extern inline unsigned Search_Pos_Nonempty( T * data, unsigned len, T element )
{
	assert( len > 0 );
	unsigned low = 0, high = len; // data[high - 1] is the last element
	while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;
		else low = mid;
	}
	T tmp = data[high - 1];
	data[high - 1] = element;
	for ( ; data[low] < element; low++ );
	data[high - 1] = tmp;
	if ( data[low] == element ) return low;
	else return len;
}

template<typename T>
extern inline unsigned Search_First_GE_Pos( T * data, unsigned len, T element )
{
	if ( len == 0 || data[len - 1] < element ) return len;
	unsigned low = 0, high = len; // data[high - 1] is the last element
	while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;
		else low = mid;
	}
	for ( ; data[low] < element; low++ );
	return low;
}

template<typename T>
extern inline bool Search_Exi_Nonempty( T * data, unsigned len, T element )
{
	unsigned low = 0, high = len; // data[high - 1] is the last element
	while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;
		else low = mid;
	}
	T tmp = data[high - 1];
	data[high - 1] = element;
	for ( ; data[low] < element; low++ );
	data[high - 1] = tmp;
	return data[low] == element;
}

template<typename T>
extern inline bool Search_Exi( T * data, unsigned len, T element )
{
	if ( len == 0 ) return false;
	else return Search_Exi_Nonempty( data, len, element );
}

template<typename T>
extern inline bool Search_Exi_Nonempty( vector<T> & data, T element )
{
	unsigned low = 0, high = data.size(); // data[high - 1] is the last element
	while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;
		else low = mid;
	}
	T tmp = data[high - 1];
	data[high - 1] = element;
	for ( ; data[low] < element; low++ );
	data[high - 1] = tmp;
	return data[low] == element;
}

template<typename T>
extern inline bool Search_Unsorted_Exi_Nonempty( vector<T> & data, T element )
{
	unsigned i, e = data.size() - 1;
	T tmp = data[e];
	data[e] = element;
	for ( i = 0; data[i] != element; i++ );
	data[e] = tmp;
	return data[i] == element;
}

template<typename T>
extern inline unsigned Search_First_GE_Pos( vector<T> & data, T element )
{
	if ( data.size() == 0 || data.back() < element ) return data.size();
	unsigned low = 0, high = data.size(); // data[high - 1] is the last element
	while ( low + 8 < high ) { // 2 + ceil{n/2} + 1 >= n/2 + 1, the least n is 9
		unsigned mid = ( low + high ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
		if ( element < data[mid] ) high = mid;
		else low = mid;
	}
	for ( ; data[low] < element; low++ );
	return low;
}


/**************************************** set ****************************************/

template<typename T>
extern inline void Set_Copy( T * set, unsigned size, T * target )
{
	for ( unsigned i = 0; i < size; i++ ) {
		target[i] = set[i];
	}
}

template<typename T>
extern inline void Set_Add_Element( T * set, unsigned size, T element, T * target )
{
	unsigned i;
	if ( set[size - 1] < element ) {
		for ( i = 0; i < size; i++ ) {
			target[i] = set[i];
		}
		target[size] = element;
	}
	else {
		for ( i = 0; set[i] < element; i++ ) {
			target[i] = set[i];
		}
		target[i] = element;
		for ( ; i < size; i++ ) {
			target[i+1] = set[i];
		}
	}
}

template<typename T>
extern inline void Set_Dec_Element( T * set, unsigned size, T element, T * target )
{
	unsigned i;
	for ( i = 0; set[i] < element; i++ ) {
		target[i] = set[i];
	}
	for ( i++; i < size; i++ ) {
		target[i-1] = set[i];
	}
}

template<typename T>
extern inline bool Subset( T * set1, unsigned size1, T * set2, unsigned size2 )
{
	if ( size1 > size2 ) return false;
	unsigned i = 0, j = 0;
	while ( i < size1 ) {
		if ( set1[i] < set2[j] ) return false;
		else {
			if ( set1[i] == set2[j] ) i++, j++;
			else {
				j++;
				if ( size1 - i > size2 -j ) return false;
			}
		}
	}
	return true;
}

template<typename T>
extern inline bool Subset_Except_One( T * set1, unsigned size1, unsigned exp, T * set2, unsigned size2 )
{
	if ( size1 - 1 > size2 ) return false;
	unsigned i = 0, j = 0;
	while ( i < exp ) {
		if ( set1[i] < set2[j] ) return false;
		else {
			if ( set1[i] == set2[j] ) i++, j++;
			else {
				j++;
				if ( size1 - i - 1 > size2 - j ) return false;
			}
		}
	}
	i++;
	while ( i < size1 ) {
		if ( set1[i] < set2[j] ) return false;
		else {
			if ( set1[i] == set2[j] ) i++, j++;
			else {
				j++;
				if ( size1 - i > size2 - j ) return false;
			}
		}
	}
	return true;
}

template<typename T>
extern inline bool Subset_Except_One( vector<T> & set1, unsigned exp, vector<T> & set2 )
{
	if ( set1.size() > set2.size() + 1 ) return false;
	unsigned i = 0, j = 0;
	while ( i < exp ) {
		if ( set1[i] < set2[j] ) return false;
		else {
			if ( set1[i] == set2[j] ) i++, j++;
			else {
				j++;
				if ( set1.size() - i > set2.size() - j + 1 ) return false;
			}
		}
	}
	i++;
	while ( i < set1.size() ) {
		if ( set1[i] < set2[j] ) return false;
		else {
			if ( set1[i] == set2[j] ) i++, j++;
			else {
				j++;
				if ( set1.size() - i > set2.size() - j ) return false;
			}
		}
	}
	return true;
}

template<typename T>
extern inline bool Intersection_Empty( const T * data1, unsigned len1, const T * data2, unsigned len2 )
{
	unsigned i = 0, j = 0;
	while ( i < len1 && j < len2 ) {
		if ( data1[i] < data2[j] ) i++;
		else if ( data1[i] > data2[j] ) j++;
		else return false;
	}
	return true;
}

template<typename T>
extern inline unsigned Union( const T * set1, unsigned size1, const T * set2, unsigned size2, T * target )
{
	unsigned i = 0, j = 0, k = 0;
	while ( ( i < size1 ) && ( j < size2 ) ) {
		if ( set1[i] < set2[j] ) target[k++] = set1[i++];
		else {
			if ( set1[i] == set2[j] ) i++;
			target[k++] = set2[j++];
		}
	}
	while ( i < size1 ) target[k++] = set1[i++];
	while ( j < size2 ) target[k++] = set2[j++];
	return k;
}

template<typename T>
extern inline unsigned Union_Disjoint( const T * set1, unsigned size1, const T * set2, unsigned size2, T * target )
{
	unsigned i = 0, j = 0, k = 0;
	while ( ( i < size1 ) && ( j < size2 ) ) {
		if ( set1[i] < set2[j] ) target[k++] = set1[i++];
		else target[k++] = set2[j++];
	}
	while ( i < size1 ) target[k++] = set1[i++];
	while ( j < size2 ) target[k++] = set2[j++];
	return k;
}

template<typename T>
extern inline unsigned Intersection( const T * set1, unsigned size1, const T * set2, unsigned size2, T * shared )
{
	unsigned i = 0, j = 0, num = 0;
	while ( i < size1 && j < size2 ) {
		if ( set1[i] < set2[j] ) i++;
		else if ( set1[i] > set2[j] ) j++;
		else {
			shared[num++] = set1[i];
			i++, j++;
		}
	}
	return num;
}

template<typename T>
extern inline void Intersection( vector<T> & set1, vector<T> & set2, vector<T> & shared )
{
	unsigned i = 0, j = 0;
	while ( i < set1.size() && j < set2.size() ) {
		if ( set1[i] < set2[j] ) i++;
		else if ( set1[i] > set2[j] ) j++;
		else {
			shared.push_back( set1[i] );
			i++, j++;
		}
	}
}

template<typename T>
extern inline unsigned Difference( const T * set1, unsigned size1, const T * set2, unsigned size2, T * dif )
{
	unsigned i = 0, j = 0, num = 0;
	while ( i < size1 && j < size2 ) {
		if ( set1[i] < set2[j] ) dif[num++] = set1[i++];
		else if ( set1[i] > set2[j] ) j++;
		else i++, j++;
	}
	while ( i < size1 ) dif[num++] = set1[i++];
	return num;
}

template<typename T>
extern inline void Difference_Subset( const T * set1, unsigned size1, const T * set2, unsigned size2, T * dif )
{
	unsigned i = 0, j = 0;
	while ( j < size2 ) {
		if ( set1[i] == set2[j] ) i++, j++;
		else { dif[i-j] = set1[i]; i++; }
	}
	while ( i < size1 ) { dif[i-j] = set1[i]; i++; }  /// NOTE: it is very surprised that we can use "dif[i-j] = set1[i++]" instead (it is right when compiled under virtual studio)
}

extern inline unsigned Mask_Unsigned( unsigned * set, unsigned size, bool * seen )
{
	unsigned i;
	unsigned new_size = 0;
	for ( i = 0; i < size; i++ ) {
		if ( seen[set[i]] ) {
			set[new_size++] = set[i];
			seen[set[i]] = false;
		}
	}
	return new_size;
}

extern inline unsigned Mask_Unsigned_Move( unsigned * set, unsigned size, bool * seen, unsigned * target )
{
	unsigned i;
	unsigned new_size = 0;
	for ( i = 0; i < size; i++ ) {
		if ( seen[set[i]] ) {
			target[new_size++] = set[i];
			seen[set[i]] = false;
		}
	}
	return new_size;
}

template<typename T>
extern inline void Replace_One_By_Many( T * set1, unsigned size1, unsigned pos, T * set2, unsigned size2 )
{
	assert( pos < size1 && size2 > 0 );
	unsigned i;
	set1[pos] = set2[0];
	for ( i = 1; i < size2; i++ ) {
		set1[size1++] = set2[i];
	}
}


/**************************************** sort ****************************************/

template<typename T>
extern T kth_Element( vector<T> & data, size_t k )
{
    if ( k >= data.size() ) {
        cerr << "ERROR: invalid location when looking for the k-th element!" << endl;
        exit( 1 );
    }
    if ( data.size() == 1 ) return data[0];
    unsigned i, j;
    T tmp, pivot;
    for ( i = j = data.size() - 1; i > 0; i-- ) { // validate the following for-loop
        if ( data[i] < data[i-1] ) {
            j = i;
            tmp = data[i-1];
            data[i-1] = data[i];
            data[i] = tmp;
        }
    }
    if ( k < j ) return data[k];
    unsigned first = j, second = data.size() - 1;  // the kth element in the interval [j, size - 1];
    while ( first < second ) {
        pivot = data[second];
        for ( i = first; data[i] < pivot; i++ );
        for ( j = second - 1; data[j] > pivot; j-- );
        while ( i < j ) {
            tmp = data[i];
            data[i++] = data[j];
            data[j--] = tmp;
            for ( ; data[i] < pivot; i++ );
            for ( ; data[j] > pivot; j-- );
        }
        data[second] = data[i];
        data[i] = pivot;
        if ( i == k ) first = second = k;
        else if ( i < k ) first = i + 1;
        else second = i - 1;
    }
    return data[first];
}

template<typename T, typename W>
extern T kth_Element( vector<T> & data, const W & rank, size_t k )
{
    if ( k >= data.size() ) {
        cerr << "ERROR: invalid location when looking for the k-th element!" << endl;
        exit( 1 );
    }
    if ( data.size() == 1 ) return data[0];
    unsigned i, j;
    T tmp, pivot;
    for ( i = j = data.size() - 1; i > 0; i-- ) { // validate the following for-loop
        if ( rank[data[i]] < rank[data[i-1]] ) {
            j = i;
            tmp = data[i-1];
            data[i-1] = data[i];
            data[i] = tmp;
        }
    }
    if ( k < j ) return data[k];
    unsigned first = j, second = data.size() - 1;  // the kth element in the interval [j, size - 1];
    while ( first < second ) {
        pivot = data[second];
        for ( i = first; rank[data[i]] < rank[pivot]; i++ );
        for ( j = second - 1; rank[data[j]] > rank[pivot]; j-- );
        while ( i < j ) {
            tmp = data[i];
            data[i++] = data[j];
            data[j--] = tmp;
            for ( ; rank[data[i]] < rank[pivot]; i++ );
            for ( ; rank[data[j]] > rank[pivot]; j-- );
        }
        data[second] = data[i];
        data[i] = pivot;
        if ( i == k ) first = second = k;
        else if ( i < k ) first = i + 1;
        else second = i - 1;
    }
    return data[first];
}

template<typename T>
extern void First_k_Elements( vector<T> & data, size_t k )
{
    if ( k > data.size() ) {
        cerr << "ERROR: less than << " << k << " elements!" << endl;
        exit( 1 );
    }
    if ( k == 0 || k == data.size() ) return;
    unsigned i, j;
    T tmp, pivot;
    for ( i = j = data.size() - 1; i > 0; i-- ) { // validate the following for-loop
        if ( data[i] < data[i-1] ) {
            j = i;
            tmp = data[i-1];
            data[i-1] = data[i];
            data[i] = tmp;
        }
    }
    if ( k <= j ) return;
    unsigned first = j, second = data.size() - 1;  // the kth element in the interval [j, size - 1];
    while ( first < second ) {
        pivot = data[second];
        for ( i = first; data[i] < pivot; i++ );
        for ( j = second - 1; data[j] > pivot; j-- );
        while ( i < j ) {
            tmp = data[i];
            data[i++] = data[j];
            data[j--] = tmp;
            for ( ; data[i] < pivot; i++ );
            for ( ; data[j] > pivot; j-- );
        }
        data[second] = data[i];
        data[i] = pivot;
        if ( i == k - 1 ) first = second = k - 1;
        else if ( i < k - 1 ) first = i + 1;
        else second = i - 1;
    }
}

template<typename T>
extern void Insert_Sort_Last( T * data, unsigned size )
{
	if ( size <= 1 ) return;
	unsigned i;
	T last = data[size - 1];
	if ( last < data[0] ) {
		for ( i = size - 1; i > 0; i-- ) {
			data[i] = data[i-1];
		}
		data[0] = last;
	}
	else {
		for ( i = size - 2; data[i] > last; i-- ) {
			data[i+1] = data[i];
		}
		data[i+1] = last;
	}
}

template<typename T>
extern void Insert_Sort_Position( T * data, unsigned size, unsigned pos )
{
	if ( size <= 1 || pos >= size ) return;
	unsigned i;
	T elem = data[pos];
	if ( elem <= data[0] ) {
		for ( i = pos; i > 0; i-- ) {
			data[i] = data[i-1];
		}
		data[0] = elem;
	}
	else if ( elem < data[pos - 1] ) {
		for ( i = pos - 1; data[i] > elem; i-- ) {
			data[i+1] = data[i];
		}
		data[i+1] = elem;
	}
	else if ( elem >= data[size - 1] ) {
		for ( i = pos + 1; i < size; i++ ) {
			data[i-1] = data[i];
		}
		data[size - 1] = elem;
	}
	else {
		for ( i = pos + 1; data[i] < elem; i++ ) {
			data[i-1] = data[i];
		}
		data[i-1] = elem;
	}
}
extern void Insert_Sort_Weight( unsigned * data, unsigned size, unsigned * weight );

extern void Insert_Sort_Weight_Part( unsigned * data, unsigned mid, unsigned size, unsigned * weight );

template<typename R>
extern void Insert_Sort_Rank( vector<unsigned> data, R * rank )
{
	if ( data.size() <= 1 ) return;
	unsigned i, j, tmp;
	for ( i = j = data.size() - 1; i > 0; i-- ) {
		if ( rank[data[i]] < rank[data[i-1]] ) {
			j = i;  // mark the bound of change
			tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	for ( i = j + 1; i < data.size(); i++ ) {
		tmp = data[i];
		for ( j = i - 1; rank[tmp] < rank[data[j]]; j-- ) {
			data[j+1] = data[j];
		}
		data[j+1] = tmp;
	}
}

template<typename R>
extern void Insert_Sort_Reverse_Rank( vector<unsigned>::iterator begin, vector<unsigned>::iterator end, R * rank )
{
	if ( end - begin <= 1 ) return;
	vector<unsigned>::iterator itr, it;
	unsigned tmp;
	for ( itr = it = end - 1; itr > begin; itr-- ) {
		if ( rank[*itr] > rank[*(itr - 1)] ) {
			it = itr;  // mark the bound of change
			tmp = *(itr - 1);
			*(itr - 1) = *itr;
			*itr = tmp;
		}
	}
	for ( itr = it + 1; itr < end; itr++ ) {
		tmp = *itr;
		for ( it = itr - 1; rank[tmp] > rank[*it]; it-- ) {
			*(it + 1) = *it;
		}
		*(it + 1) = tmp;
	}
}

extern void Sort( unsigned * data, unsigned size );

extern void Sort_Reverse( unsigned * data, unsigned size );

extern void Quick_Sort( unsigned * data, unsigned size );

extern void Quick_Sort_Weight( unsigned * data, unsigned size, double * weight );

template<typename T, typename W>
extern void Quick_Sort_Weight( vector<T> & data, W & weight )
{
	if ( data.size() > UNSIGNED_UNDEF - 16 ) {
		cerr << "ERROR: the size of elements is more than UNSINGED_UNDEF - 16!" << endl;
		exit( 0 );
	}
	unsigned i, j;
	for ( i = j = data.size() - 1; i > 0; i-- ) { // Here we use Bubble once
		if ( weight[data[i]] < weight[data[i-1]] ) {
			j = i;
			T tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	unsigned * b_stack = new unsigned [data.size() - j];
	unsigned * e_stack = new unsigned [data.size() - j];
	b_stack[0] = j;
	e_stack[0] = data.size() - 1;
	unsigned num_stack = 1;
	while ( num_stack-- ) {
		if ( e_stack[num_stack] < 16 + b_stack[num_stack] ) { // NOTE: b_stack[num_stack] may be more than e_stack[num_stack] by one.
			for ( i = b_stack[num_stack] + 1; i <= e_stack[num_stack]; i++ ) {
				T tmp = data[i];
				for ( j = i - 1; weight[tmp] < weight[data[j]]; j-- ) {
					data[j+1] = data[j];
				}
				data[j+1] = tmp;
			}
		}
		else {
			unsigned pos = (b_stack[num_stack] + e_stack[num_stack] ) / 2;
			if ( ( weight[data[b_stack[num_stack]]] < weight[data[pos]] ) + \
				( weight[data[pos]] < weight[data[e_stack[num_stack]]] ) == 1 ) {
				if ( ( weight[data[b_stack[num_stack]]] < weight[data[pos]] ) +
					( weight[data[b_stack[num_stack]]] < weight[data[e_stack[num_stack]]] ) == 1 )
					pos = b_stack[num_stack];
				else pos = e_stack[num_stack];
			}
			T pivot = data[pos];
			data[pos] = data[e_stack[num_stack]];
//			clauses[e_stack[num_stack]] = pivot;
			for ( i = b_stack[num_stack]; weight[data[i]] < weight[pivot]; i++ );
			for ( j = e_stack[num_stack] - 1; weight[pivot] < weight[data[j]]; j-- );
			while ( i < j ) {
				T tmp = data[i];
				data[i++] = data[j];
				data[j--] = tmp;
				for ( ; weight[data[i]] < weight[pivot]; i++ );
				for ( ; weight[pivot] < weight[data[j]]; j-- );
			}
			data[e_stack[num_stack]] = data[i];
			data[i] = pivot;
			b_stack[num_stack + 1] = i + 1;
			e_stack[num_stack + 1] = e_stack[num_stack];
			e_stack[num_stack] = i - 1;
			num_stack += 2;
		}
	}
	delete [] b_stack;
	delete [] e_stack;
}

template<typename T, typename W>
extern void Quick_Sort_Weight_Reverse( T * data, unsigned size, W & weight )
{
	if ( size > UNSIGNED_UNDEF - 16 ) {
		cerr << "ERROR[TreeD]: the size of clauses in Sort_Clauses is more than UNSINGED_UNDEF - 16!" << endl;
		exit( 0 );
	}
	unsigned i, j;
	for ( i = j = size - 1; i > 0; i-- ) { // Here we use Bubble once
		if ( weight[data[i]] > weight[data[i-1]] ) {
			j = i;
			T tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	unsigned * b_stack = new unsigned [size - j];
	unsigned * e_stack = new unsigned [size - j];
	b_stack[0] = j;
	e_stack[0] = size - 1;
	unsigned num_stack = 1;
	while ( num_stack-- ) {
		if ( e_stack[num_stack] < 16 + b_stack[num_stack] ) { // NOTE: b_stack[num_stack] may be more than e_stack[num_stack] by one.
			for ( i = b_stack[num_stack] + 1; i <= e_stack[num_stack]; i++ ) {
				T tmp = data[i];
				for ( j = i - 1; weight[tmp] > weight[data[j]]; j-- ) {
					data[j+1] = data[j];
				}
				data[j+1] = tmp;
			}
		}
		else {
			unsigned pos = (b_stack[num_stack] + e_stack[num_stack] ) / 2;
			if ( ( weight[data[b_stack[num_stack]]] > weight[data[pos]] ) + \
				( weight[data[pos]] > weight[data[e_stack[num_stack]]] ) == 1 ) {
				if ( ( weight[data[b_stack[num_stack]]] > weight[data[pos]] ) +
					( weight[data[b_stack[num_stack]]] > weight[data[e_stack[num_stack]]] ) == 1 )
					pos = b_stack[num_stack];
				else pos = e_stack[num_stack];
			}
			T pivot = data[pos];
			data[pos] = data[e_stack[num_stack]];
//			clauses[e_stack[num_stack]] = pivot;
			for ( i = b_stack[num_stack]; weight[data[i]] > weight[pivot]; i++ );
			for ( j = e_stack[num_stack] - 1; weight[pivot] > weight[data[j]]; j-- );
			while ( i < j ) {
				T tmp = data[i];
				data[i++] = data[j];
				data[j--] = tmp;
				for ( ; weight[data[i]] > weight[pivot]; i++ );
				for ( ; weight[pivot] > weight[data[j]]; j-- );
			}
			data[e_stack[num_stack]] = data[i];
			data[i] = pivot;
			b_stack[num_stack + 1] = i + 1;
			e_stack[num_stack + 1] = e_stack[num_stack];
			e_stack[num_stack] = i - 1;
			num_stack += 2;
		}
	}
	delete [] b_stack;
	delete [] e_stack;
}

extern void Sort_Weight_Reverse( unsigned * data, unsigned size, double * weight );

extern void Sort_Weight_Reverse_Max( unsigned * data, unsigned size, double * weight ); //if size > 1, data[0] = max or data[-1] = max

template<typename T>
extern void Quick_Sort( vector<T> & vec )
{
	if ( vec.size() <= 1 ) return;
	unsigned i, j;
	T tmp;
	for ( i = j = vec.size() - 1; i > 0; i-- ) { // validate the following insertion_sort
		if ( vec[i] < vec[i-1] ) {
			j = i;
			tmp = vec[i-1];
			vec[i-1] = vec[i];
			vec[i] = tmp;
		}
	}
	unsigned * b_stack = new unsigned [vec.size() - j];
	unsigned * e_stack = new unsigned [vec.size() - j];
	b_stack[0] = j;
	e_stack[0] = vec.size() - 1;
	unsigned num_stack = 1;
	while ( num_stack-- ) {
		if ( e_stack[num_stack] < 16 + b_stack[num_stack] ) { // NOTE: b_stack[num_stack] may be more than e_stack[num_stack] by one.
			for ( i = b_stack[num_stack] + 1; i <= e_stack[num_stack]; i++ ) {
				tmp = vec[i];
				for ( j = i - 1; vec[j] > tmp; j-- ) {
					vec[j+1] = vec[j];
				}
				vec[j+1] = tmp;
			}
		}
		else {
			unsigned pos = (b_stack[num_stack] + e_stack[num_stack] ) / 2;
			if ( ( vec[b_stack[num_stack]] < vec[pos] ) + ( vec[pos] < vec[e_stack[num_stack]] ) == 1 ) {
				if ( ( vec[b_stack[num_stack]] < vec[pos] ) + ( vec[b_stack[num_stack]] < vec[e_stack[num_stack]] ) == 1 )
					pos = b_stack[num_stack];
				else pos = e_stack[num_stack];
			}
			T pivot = vec[pos];
			vec[pos] = vec[e_stack[num_stack]];
			for ( i = b_stack[num_stack]; vec[i] < pivot; i++ );
			for ( j = e_stack[num_stack] - 1; vec[j] > pivot; j-- );
			while ( i < j ) {
				tmp = vec[i];
				vec[i++] = vec[j];
				vec[j--] = tmp;
				for ( ; vec[i] < pivot; i++ );
				for ( ; vec[j] > pivot; j-- );
			}
			vec[e_stack[num_stack]] = vec[i];
			vec[i] = pivot;
			b_stack[num_stack + 1] = i + 1;
			e_stack[num_stack + 1] = e_stack[num_stack];
			e_stack[num_stack] = i - 1; // e_stack[num_stack] = j is less efficient when i = j
			num_stack += 2;
		}
	}
	delete [] b_stack;
	delete [] e_stack;
}


/**************************************** array/vector ****************************************/

template<typename T>
extern inline void Erase_Vector_Element( vector<T> & vec, unsigned pos )
{
	assert( pos < vec.size() );
	for ( ; pos + 1 < vec.size(); pos++ ) vec[pos] = vec[pos + 1];
	vec.pop_back();
}

template<typename T>
extern inline void Erase_Vector_Element( vector<T> & vec, unsigned pos, unsigned & size )
{
	assert( pos < size && size == vec.size() );
	for ( ; pos + 1 < size; pos++ ) vec[pos] = vec[pos + 1];
	vec.pop_back();
	size--;
}

template<typename T>
extern inline void Erase_Vector_Elements( vector<T> & vec, unsigned begin, unsigned end, unsigned & size )
{
	assert( begin < end && end <= size  && size == vec.size() );
	unsigned num = end - begin;
	for ( ; begin + num < size; begin++ ) vec[begin] = vec[begin + num];
	vec.pop_back();
	size -= num;
}

template<typename T>
extern inline void Simply_Erase_Vector_Element( vector<T> & vec, unsigned pos )
{
	ASSERT( pos < vec.size() );
	vec[pos] = vec.back();
	vec.pop_back();
}

template<typename T>
extern inline void Simply_Erase_Vector_Element( vector<T> & vec, unsigned pos, unsigned & size )
{
	ASSERT( pos < size && size == vec.size() );
	vec[pos] = vec.back();
	vec.pop_back();
	size--;
}

template<typename T>
extern inline void Simply_Insert_Vector_Element( vector<T> & vec, unsigned pos, T & elem )
{
	assert( pos <= vec.size() );
	if ( pos < vec.size() ) {
		vec.push_back( vec[pos] );
		vec[pos] = elem;
	}
	else vec.push_back( elem );
}

template<typename T>
extern inline void Swap_Two_Elements_Vector( vector<T> & vec, unsigned first, unsigned second )
{
	T tmp = vec[first];
	vec[first] = vec[second];
	vec[second] = tmp;
}

template<typename T>
extern inline void Insert( T * source, unsigned len, T element )
{
	if ( len == 0 ) source[0] = element;
	else if ( element < source[0] ) {
		for ( unsigned i = len - 1; i != UNSIGNED_UNDEF; i-- ) source[i+1] = source[i];
		source[0] = element;
	}
	else {
		unsigned i;
		for ( i = len - 1; source[i] > element; i-- ) source[i+1] = source[i];
		source[i+1] = element;
	}
}

template<typename T>
extern inline void Insert( T * source, unsigned len, T element, T * target )
{
	if ( len == 0 ) source[0] = element;
	else if ( source[len - 1] < element ) {
		for ( unsigned i = 0; i < len; i++ ) target[i] = source[i];
		target[len] = element;
	}
	else {
		unsigned i;
		for ( i = 0; source[i] < element; i++ ) target[i] = source[i];
		target[i] = element;
		for ( ; i < len; i++ ) target[i+1] = source[i];
	}
}

template<typename T>
extern inline void Delete( const T * source, unsigned len, T element, T * target )
{
	unsigned i;
	for ( i = 0; source[i] != element; i++ ) target[i] = source[i];
	for ( i++; i < len; i++ ) target[i - 1] = source[i];
}

template<typename T>
extern inline void Delete( const vector<T> & source, T element, vector<T> & target )
{
	target.resize( source.size() - 1 );
	unsigned i;
	for ( i = 0; source[i] != element; i++ ) target[i] = source[i];
	for ( i++; i < source.size(); i++ ) target[i - 1] = source[i];
}

template<typename T>
extern inline void Replace_One_By_One( T * source, unsigned len, T old_element, T new_element, T * target )
{
	unsigned i;
	if ( source[len - 1] < new_element ) {
		for ( i = 0; source[i] < old_element; i++ ) target[i] = source[i];
		for ( i++; i < len; i++ ) target[i-1] = source[i];
		target[len-1] = new_element;
	}
	else {
		if ( old_element < new_element ) {
			for ( i = 0; source[i] < old_element; i++ ) target[i] = source[i];
			for ( i++; source[i] < new_element; i++ ) target[i-1] = source[i];
			target[i-1] = new_element;
			for ( ; i < len; i++ ) target[i] = source[i];
		}
		else {
			for ( i = 0; source[i] < new_element; i++ ) target[i] = source[i];
			target[i] = new_element;
			for ( ; source[i] < old_element; i++ ) target[i+1] = source[i];
			for ( i++; i < len; i++ ) target[i] = source[i];
		}
	}
}

template<typename T>
extern inline void Replace_One_By_Many( T * source, unsigned len, T old_element, T * new_element, unsigned num_new, T * target )
{
	unsigned i = 0, j = 0, k = 0;
	while ( ( source[i] < old_element ) && ( j < num_new ) ) {
		if ( source[i] < new_element[j] ) target[k++] = source[i++];
		else target[k++] = new_element[j++];
	}
	if ( j == num_new ) {
		for ( ; source[i] < old_element; ) target[k++] = source[i++];
		for ( i++; i < len; ) target[k++] = source[i++];
	}
	else {
		i++;
		while ( i < len && j < num_new ) {
			if ( source[i] < new_element[j] ) target[k++] = source[i++];
			else target[k++] = new_element[j++];
		}
		while ( i < len ) target[k++] = source[i++];
		while ( j < num_new ) target[k++] = new_element[j++];
	}
}

template<typename T>
extern inline void Merge_Two_Arrays( T * array1, unsigned len1, T * array2, unsigned len2, T * target )
{
	unsigned i = 0, j = 0, k = 0;
	while ( ( i < len1 ) && ( j < len2 ) ) {
		if ( array1[i] < array2[j] ) target[k++] = array1[i++];
		else target[k++] = array2[j++];
	}
	while ( i < len1 ) target[k++] = array1[i++];
	while ( j < len2 ) target[k++] = array2[j++];
}

extern void Merge_Two_Arrays( unsigned * a, int len1, unsigned * b, int len2, unsigned c, unsigned * d );  // sorted arrays

/* NOTE:
* Each element appears exactly once.
* Each array is nonempty.
*/
template<typename T>
extern void Merge_Many_Arrays( T ** arrays, unsigned * array_lens, unsigned array_num, T * target )
{
	unsigned * iterator = new unsigned [array_num];
	unsigned i;
	iterator[0] = 0;
	T max_element = arrays[0][array_lens[0] - 1];
	unsigned max_array = 0;
	for ( i = 1; i < array_num; i++ ) {
		iterator[i] = 0;
		if ( max_element < arrays[i][array_lens[i] - 1] ) {
			max_element = arrays[i][array_lens[i] - 1];
			max_array = i;
		}
	}
	for ( unsigned num = 0; true; num++ ) {
		unsigned current_element = max_element;
		unsigned current_array = max_array;
		for ( i = 0; i < array_num; i++ ) {
			if ( iterator[i] < array_lens[i] && arrays[i][iterator[i]] < current_element ) {
				current_element = arrays[i][iterator[i]];
				current_array = i;
			}
		}
		target[num] = current_element;
		iterator[current_array]++;
		if ( current_element == max_element ) break;
	}
	delete [] iterator;
}


/**************************************** input/output ****************************************/

extern int Exactly_Read_Integers( char * source, int target[] );

extern int Exactly_Read_Unsigneds( char * source, unsigned target[] );

extern void Exactly_Read_Unsigneds( char * source, vector<unsigned> & target );

extern bool Read_String_Change( char * & source, const char * target );

extern int Read_Integer_Change( char * & source );

extern unsigned Read_Unsigned_Change( char * & source );

extern float Read_Float_Change( char * & source );

extern double Read_Double_Change( char * & source );

extern bool String_Fuzzy_Match( const char * str1, const char * str2 );

extern bool String_Fuzzy_Match_Prefix_Change( char * & str, const char * prefix );

extern inline bool Separate_Suffix( char file_name[], char file_suffix[] )
{
	unsigned len = strlen( file_name );
	if ( len == 0 ) return false;
	unsigned i, j;
	char first = file_name[0];
	file_name[0] = '.';
	for ( i = len; file_name[i] != '.'; i-- );
	file_name[0] = first;
	if ( file_name[i] != '.' ) return false;
	for ( j = i; j < len; j++ ) file_suffix[j - i] = file_name[j];
	file_suffix[j - i] = '\0';
	file_name[i] = '\0';
	return true;
}

extern inline void Basename( const char * filename, char * newname )
{
	int i, j, len = strlen( filename );
	for ( i = len - 1; i >= 0; i-- ) {
		if ( filename[i] == '\\' || filename[i] == '/' ) break;
	}
	j = i + 1;
	for ( i = 0; i < len - j; i++ ) newname[i] = filename[j+i];
	newname[i] = '\0';
}

extern inline void Display_Memory_Status( ostream & fout, void * p, unsigned size )
{
	assert( sizeof(unsigned) == 4 );
	unsigned i, j, u;
	unsigned mask = 2147483648;  // 2^31
	char str[33];
	str[32] = '\0';
	u = *( (unsigned *)p );
	for ( j = 0; j < 32; j++ ) {
		str[j] = '0' + ( ( u & mask ) > 0 );
		u = u << 1;
	}
	fout << str;
	for ( i = 1; i < size; i++ ) {
		u = *( (unsigned *)p + i );
		for ( j = 0; j < 32; j++ ) {
			str[j] = '0' + ( ( u & mask ) > 0 );
			u = u << 1;
		}
		fout << ',' << str;
	}
}


/**************************************** prime number ****************************************/

extern unsigned Prime_ith( const unsigned i );

extern unsigned Prime_Close( const unsigned a );


}


#endif
