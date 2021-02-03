#include "Basic_Functions.h"


namespace KCBox {


/**************************************** sort ****************************************/

extern void Sort( unsigned * data, unsigned size )
{
	for ( unsigned i = 0; i < size; i++ ) {
		unsigned min = i;
		for ( unsigned j = i + 1; j < size; j++ ) {
			if ( data[j] < data[min] ) min = j;
		}
		unsigned tmp = data[min];
		data[min] = data[i];
		data[i] = tmp;
	}
}

extern void Bubble_Sort( unsigned * data, unsigned size )
{
	if ( size <= 1 ) return;
	unsigned upper = size - 1;
	while ( 0 < upper ) {
		unsigned old_upper = upper;
		upper = 0;
		for ( unsigned i = 0; i < old_upper; i++ ) {
			if ( data[i] > data[i+1] ) {
				upper = i;
				unsigned tmp = data[i+1];
				data[i+1] = data[i];
				data[i] = tmp;
			}
		}
	}
}

extern void Double_Bubble_Sort( unsigned * data, unsigned size )
{
	if ( size <= 1 ) return;
	unsigned lower = 0, upper = size - 1;
	while ( lower < upper ) {
		unsigned old = upper;
		upper = lower;
		for ( unsigned i = lower; i < old; i++ ) {
			if ( data[i] > data[i+1] ) {
				upper = i;
				unsigned tmp = data[i+1];
				data[i+1] = data[i];
				data[i] = tmp;
			}
		}
		old = lower;
		lower = upper;
		for ( unsigned i = upper; i > lower; i-- ) {
			if ( data[i] < data[i-1] ) {
				lower = i;
				unsigned tmp = data[i-1];
				data[i-1] = data[i];
				data[i] = tmp;
			}
		}
	}
}

extern void Sort_Reverse( unsigned * data, unsigned size )
{
	for ( unsigned i = 0; i < size; i++ ) {
		unsigned max = i;
		for ( unsigned j = i + 1; j < size; j++ ) {
			if ( data[j] > data[max] ) max = j;
		}
		unsigned tmp = data[max];
		data[max] = data[i];
		data[i] = tmp;
	}
}

/* NOTE:
* It is required that there does not exist duplicate elements
*/
extern void Quick_Sort( unsigned * data, unsigned size )
{
	if ( size <= 1 ) return;
	unsigned i, j, tmp;
	for ( i = j = size - 1; i > 0; i-- ) { // validate the following insertion_sort
		if ( data[i] < data[i-1] ) {
			j = i;
			tmp = data[i-1];
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
		if ( e_stack[num_stack] - b_stack[num_stack] < 16 ) {
			for ( i = b_stack[num_stack] + 1; i <= e_stack[num_stack]; i++ ) {
				tmp = data[i];
				for ( j = i - 1; data[j] > tmp; j-- ) {
					data[j+1] = data[j];
				}
				data[j+1] = tmp;
			}
		}
		else {
			unsigned pos = (b_stack[num_stack] + e_stack[num_stack] ) / 2;
			if ( ( data[b_stack[num_stack]] < data[pos] ) + ( data[pos] < data[e_stack[num_stack]] ) == 1 ) {
				if ( ( data[b_stack[num_stack]] < data[pos] ) + ( data[b_stack[num_stack]] < data[e_stack[num_stack]] ) == 1 )
					pos = b_stack[num_stack];
				else pos = e_stack[num_stack];
			}
			unsigned pivot = data[pos];
			data[pos] = data[e_stack[num_stack]];
			for ( i = b_stack[num_stack]; data[i] < pivot; i++ );
			for ( j = e_stack[num_stack] - 1; data[j] > pivot; j-- );
			while ( i < j ) {
				tmp = data[i];
				data[i++] = data[j];
				data[j--] = tmp;
				for ( ; data[i] < pivot; i++ );
				for ( ; data[j] > pivot; j-- );
			}
			data[e_stack[num_stack]] = data[i];
			data[i] = pivot;
			b_stack[num_stack + 1] = i + 1;
			e_stack[num_stack + 1] = e_stack[num_stack];
			e_stack[num_stack] = i - 1; // e_stack[num_stack] = j is less efficient when i = j
			num_stack += 2;
		}
	}
	delete [] b_stack;
	delete [] e_stack;
}

void Quick_Sort_Weight( unsigned * data, unsigned size, double * weight )
{
	if ( size > UNSIGNED_UNDEF - 16 ) {
		cerr << "ERROR[TreeD]: the size of clauses in Sort_Clauses is more than UNSINGED_UNDEF - 16!" << endl;
		exit( 0 );
	}
	unsigned i, j, tmp;
	for ( i = j = size - 1; i > 0; i-- ) { // Here we use Bubble once
		if ( weight[data[i]] < weight[data[i-1]] ) {
			j = i;
			tmp = data[i-1];
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
				tmp = data[i];
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
			unsigned pivot = data[pos];
			data[pos] = data[e_stack[num_stack]];
//			clauses[e_stack[num_stack]] = pivot;
			for ( i = b_stack[num_stack]; weight[data[i]] < weight[pivot]; i++ );
			for ( j = e_stack[num_stack] - 1; weight[pivot] < weight[data[j]]; j-- );
			while ( i < j ) {
				tmp = data[i];
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

void Quick_Sort_Weight( vector<unsigned> & data, unsigned * weight )
{
	if ( data.size() > UNSIGNED_UNDEF - 16 ) {
		cerr << "ERROR[TreeD]: the size of clauses in Sort_Clauses is more than UNSINGED_UNDEF - 16!" << endl;
		exit( 0 );
	}
	unsigned i, j, tmp;
	for ( i = j = data.size() - 1; i > 0; i-- ) { // Here we use Bubble once
		if ( weight[data[i]] < weight[data[i-1]] ) {
			j = i;
			tmp = data[i-1];
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
			for ( unsigned i = b_stack[num_stack] + 1; i <= e_stack[num_stack]; i++ ) {
				tmp = data[i];
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
			unsigned pivot = data[pos];
			data[pos] = data[e_stack[num_stack]];
//			clauses[e_stack[num_stack]] = pivot;
			for ( i = b_stack[num_stack]; weight[data[i]] < weight[pivot]; i++ );
			for ( j = e_stack[num_stack] - 1; weight[pivot] < weight[data[j]]; j-- );
			while ( i < j ) {
				tmp = data[i];
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

void Insert_Sort_Weight( unsigned * data, unsigned size, unsigned * weight )
{
	if ( size <= 1 ) return;
	unsigned i, j, tmp;
	for ( i = j = size - 1; i > 0; i-- ) {
		if ( weight[data[i]] < weight[data[i-1]] ) {
			j = i;
			tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	for ( i = j + 1; i < size; i++ ) {
		tmp = data[i];
		for ( j = i - 1; weight[tmp] < weight[data[j]]; j-- ) {
			data[j+1] = data[j];
		}
		data[j+1] = tmp;
	}
}

void Insert_Sort_Weight_Part( unsigned * data, unsigned mid, unsigned size, unsigned * weight ) // datat[0..mid - 1] is sort
{
	if ( size <= 1 ) return;
	unsigned i, j, tmp;
	for ( i = j = size - 1; i > mid; i-- ) {
		if ( weight[data[i]] < weight[data[i-1]] ) {
			j = i;
			tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	for ( i = j + 1; i < size; i++ ) {
		tmp = data[i];
		for ( j = i - 1; weight[tmp] < weight[data[j]]; j-- ) {
			data[j+1] = data[j];
		}
		data[j+1] = tmp;
	}
}

void Sort_Weight_Reverse( unsigned * data, unsigned size, double * weight )
{
	if ( size <= 1 ) return;
	unsigned i, j, tmp;
	for ( i = j = size - 1; i > 0; i-- ) {
		if ( weight[data[i]] > weight[data[i-1]] ) {
			j = i;
			tmp = data[i-1];
			data[i-1] = data[i];
			data[i] = tmp;
		}
	}
	for ( i = j + 1; i < size; i++ ) {
		tmp = data[i];
		for ( j = i - 1; weight[data[j]] < weight[tmp]; j-- ) {
			data[j+1] = data[j];
		}
		data[j+1] = tmp;
	}
}

void Sort_Weight_Reverse_Max( unsigned * data, unsigned size, double * weight ) // data[0] is the maximum element
{
	unsigned i, j, tmp;
	for ( i = 2; i < size; i++ ) {
		tmp = data[i];
		for ( j = i - 1; weight[data[j]] < weight[tmp]; j-- ) {
			data[j+1] = data[j];
		}
		data[j+1] = tmp;
	}
}

extern bool Intersection_Empty_Unsigned_Bin( unsigned * data1, unsigned len1, unsigned * data2, unsigned len2 )
{
	unsigned low1 = 0, low2 = 0;
	while ( low1 == len1 || low2 == len2 ) {
		unsigned high1 = len1, high2 = len2;
		while ( low2 != high2 - 1 ) {
			unsigned mid = ( low2 + high2 ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
			if ( data1[low1] < data2[mid] ) high2 = mid;
			else low2 = mid;
		}
		if ( data1[low1] == data2[low2] ) return true;
		else low1++;
		while ( low1 != high1 - 1 ) {
			unsigned mid = ( low1 + high1 ) / 2; // wiki: Do not use (low+high)/2 which might encounter overflow issue
			if ( data2[low1] < data1[mid] ) high1 = mid;
			else low1 = mid;
		}
		if ( data1[low1] == data2[low2] ) return true;
		else low2++;
	}
	return false;
}


/**************************************** array/vector ****************************************/

extern void Merge( unsigned * a, int len1, unsigned * b, int len2, unsigned c, unsigned * d )
{
	int i = 0, j = 0, k = 0;
	bool inserted = false;
	while ( ( i < len1 ) && ( j < len2 ) ) {
		if ( c < a[i] ) {
			if ( c < b[j] ) {
				 d[k++] = c;
				 inserted = true;
				 break;
			}
			else d[k++] = b[j++];
		}
		else if ( a[i] < b[j] ) d[k++] = a[i++];
		else d[k++] = b[j++];
	}
	if ( inserted ) {
		while ( ( i < len1 ) && ( j < len2 ) ) {
			if ( a[i] < b[j] ) d[k] = a[i++];
			else d[k] = b[j++];
			k++;
		}
		while ( i < len1 ) d[k++] = a[i++];
		while ( j < len2 ) d[k++] = b[j++];
	}
	else if ( i == len1 ) {
		while ( j < len2 ) {
			if ( c < b[j] ) break;
			d[k++] = b[j++];
		}
		d[k++] = c;
		while ( j < len2 ) d[k++] = b[j++];
	}
	else {
		while ( i < len1 ) {
			if ( c < a[i] ) break;
			d[k++] = a[i++];
		}
		d[k++] = c;
		while ( i < len1 ) d[k++] = a[i++];
	}
	while ( i < len1 ) d[k++] = a[i++];
	while ( j < len2 ) d[k++] = b[j++];
}


/**************************************** input/output ****************************************/

extern int Exactly_Read_Integers( char * source, int target[] )
{
	int i = 0;
	while ( *source == ' ' || *source == '\t' ) source++;
	while ( *source != '\0' ) {
		if ( sscanf( source, "%d", &target[i++]) != 1 ) {
			cerr << "ERROR: Invalid input!" << endl;
		}
		if( *source == '-' ) source++;
		while ( *source >= '0' && *source <= '9' ) source++;
		while ( *source == ' ' || *source == '\t' ) source++;
	}
	return i;
}

extern int Exactly_Read_Unsigneds( char * source, unsigned target[] )
{
	int i = 0;
	while ( *source == ' ' || *source == '\t' ) source++;
	while ( '0' <= *source && *source <= '9' ) {
		if ( sscanf( source, "%u", &target[i++]) != 1 ) {
			cerr << "ERROR: Invalid input!" << endl;
		}
		while ( '0' <= *source && *source <= '9' ) source++;
		while ( *source == ' ' || *source == '\t' ) source++;
	}
	return i;
}

extern void Exactly_Read_Unsigneds( char * source, vector<unsigned> & target )
{
	unsigned u;
	while ( *source == ' ' || *source == '\t' ) source++;
	while ( '0' <= *source && *source <= '9' ) {
		if ( sscanf( source, "%u", &u ) != 1 ) {
			cerr << "ERROR: Invalid input!" << endl;
		}
		target.push_back( u );
		while ( '0' <= *source && *source <= '9' ) source++;
		while ( *source == ' ' || *source == '\t' ) source++;
	}
}

extern int Exactly_Read_Unsigneds_Change( char * & source, unsigned target[] )
{
	int i = 0;
	while ( *source == ' ' || *source == '\t' ) source++;
	while ( '0' <= *source && *source <= '9' ) {
		if ( sscanf( source, "%u", &target[i++]) != 1 ) {
			cerr << "ERROR: Invalid input!" << endl;
		}
		while ( '0' <= *source && *source <= '9' ) source++;
		while ( *source == ' ' || *source == '\t' ) source++;
	}
	return i;
}

extern int Read_Integer_Change( char * & source )
{
	while ( *source == ' ' || *source == '\t' ) source++;
	int a;
	if ( sscanf( source, "%d", &a) != 1 ) {
		cerr << "ERROR: Invalid input!" << endl;
	}
	if( *source == '-' ) source++;
	while ( *source >= '0' && *source <= '9' ) source++;
	while ( *source == ' ' || *source == '\t' ) source++;
	return a;
}

extern unsigned Read_Unsigned_Change( char * & source )
{
	while ( *source == ' ' || *source == '\t' ) source++;
	unsigned a;
	if ( sscanf( source, "%u", &a) != 1 ) {
		cerr << "ERROR: Invalid input!" << endl;
	}
	while ( *source >= '0' && *source <= '9' ) source++;
	while ( *source == ' ' || *source == '\t' ) source++;
	return a;
}

extern double Read_Float_Change( char * & source )
{
	while ( *source == ' ' || *source == '\t' ) source++;
	float f;
	if ( sscanf( source, "%f", &f) != 1 ) {
		cerr << "ERROR: Invalid input!" << endl;
	}
	if( *source == '-' ) source++;
	while ( *source >= '0' && *source <= '9' ) source++;
	if( *source == '.' ) source++;
	while ( *source >= '0' && *source <= '9' ) source++;
	while ( *source == ' ' || *source == '\t' ) source++;
	return f;
}

extern double Read_Double_Change( char * & source )
{
	while ( *source == ' ' || *source == '\t' ) source++;
	double a;
	if ( sscanf( source, "%lf", &a) != 1 ) {
		cerr << "ERROR: Invalid input!" << endl;
	}
	if( *source == '-' ) source++;
	while ( *source >= '0' && *source <= '9' ) source++;
	if( *source == '.' ) source++;
	while ( *source >= '0' && *source <= '9' ) source++;
	while ( *source == ' ' || *source == '\t' ) source++;
	return a;
}

extern bool Read_String_Change( char * & source, char * target )
{
    char * source_copy = source;
	while ( *source == ' ' || *source == '\t' ) source++;
	while ( *source != '\0' && *source == *target ) source++, target++;
	bool matched = *target == '\0';
	if ( !matched ) source = source_copy;
	return matched;
}

extern bool String_Fuzzy_Match( char * str1, char * str2 )
{
	while ( true ) {
		while ( BLANK_CHAR(*str1) ) str1++;
		while ( BLANK_CHAR(*str2) ) str2++;
 		while ( *str1 != '\0' && *str2 != '\0' && !BLANK_CHAR(*str1) && !BLANK_CHAR(*str2) && *str1 == *str2 ) {
			str1++, str2++;
		}
		if ( *str1 == '\0' ) {
            while ( BLANK_CHAR(*str2) ) str2++;
            return *str2 == '\0';
		}
		if ( *str2 == '\0' ) {
            while ( BLANK_CHAR(*str1) ) str1++;
            return *str1 == '\0';
		}
		if ( !BLANK_CHAR(*str1) || !BLANK_CHAR(*str2) ) return false;
	}
}


/**************************************** prime number ****************************************/

static unsigned prime_possible_remainders[8] = {1, 7, 11, 13, 17, 19, 23, 29};  // NOTE: N is prime only if N % 30 is an element in prime_steps
static unsigned prime_possible_positions[30] = {8, 0, 8, 8, 8, 8, 8, 1, 8, 8, \
												8, 2, 8, 3, 8, 8, 8, 4, 8, 5, \
												8, 8, 8, 6, 8, 8, 8, 8, 8, 7};  // NOTE: the possible positions with prime numbers, 8 means impossible
static unsigned prime_possible_steps[8] = {6, 4, 2, 4, 2, 4, 6, 2};  // NOTE: the step to the next possible prime number
static vector<unsigned> primes_reservoir;

static void Prime_Init()
{
	for ( unsigned i = 0; DEBUG_OFF && i < 7; i++ ) {
		assert( prime_possible_steps[i] == prime_possible_remainders[i+1] - prime_possible_remainders[i] );
	}  /// NOTE: do NOTE remove these comments
	assert( !DEBUG_OFF || prime_possible_steps[7] == 30 + prime_possible_remainders[0] - prime_possible_remainders[7] );
	primes_reservoir.reserve( 79 * 1024 );  // NOTE: there are 78498 prime numbers between [1, 10 ^ 6]
	primes_reservoir.push_back( 2 );
	primes_reservoir.push_back( 3 );
	primes_reservoir.push_back( 5 );
	primes_reservoir.push_back( 7 );
	primes_reservoir.push_back( 11 );
	primes_reservoir.push_back( 13 );
	primes_reservoir.push_back( 17 );
	primes_reservoir.push_back( 19 );
	primes_reservoir.push_back( 23 );
	primes_reservoir.push_back( 29 );
	///
	primes_reservoir.push_back( 31 );
	primes_reservoir.push_back( 37 );
	primes_reservoir.push_back( 41 );
	primes_reservoir.push_back( 43 );
	primes_reservoir.push_back( 47 );
	primes_reservoir.push_back( 53 );
	primes_reservoir.push_back( 59 );
	primes_reservoir.push_back( 61 );
	primes_reservoir.push_back( 67 );
	primes_reservoir.push_back( 71 );
	primes_reservoir.push_back( 73 );
	primes_reservoir.push_back( 79 );
	primes_reservoir.push_back( 83 );
	primes_reservoir.push_back( 89 );
	primes_reservoir.push_back( 97 );
	/// 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97
}

static void Prime_Next()
{
	unsigned i, val = primes_reservoir.back();
	vector<unsigned>::iterator itr, begin = primes_reservoir.begin() + 3;
	for ( i = prime_possible_positions[val % 30]; true; i++ ) {
		val += prime_possible_steps[i % 8];
		for ( itr = begin; (*itr) * (*itr) <= val && val % (*itr); itr++ );
		if (  (*itr) * (*itr) > val ) break;
	}
	primes_reservoir.push_back( val );
}

extern unsigned Prime_ith( const unsigned i )
{
	unsigned size = primes_reservoir.size();
	if ( i < size ) return primes_reservoir[i];
	if ( primes_reservoir.empty() ) Prime_Init();
	for ( ; size <= i; size++ ) {
		Prime_Next();
	}
	return primes_reservoir[i];
}

extern unsigned Prime_Close( const unsigned a )
{
	if ( primes_reservoir.empty() ) Prime_Init();
	if ( primes_reservoir.back() >= a ) {
		unsigned i = Search_First_GE_Pos( primes_reservoir, a );
		return primes_reservoir[i];
	}
	else {
		while ( primes_reservoir.back() < a ) {
			Prime_Next();
		}
		return primes_reservoir.back();
	}
}


}
