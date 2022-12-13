#include "BigNum.h"
#include <fstream>
using namespace std;


namespace KCBox {


extern int sscanf( char str[], BigInt & i )
{
	return gmp_sscanf( str, "%Zd", i._xCount );
}

extern void printf( BigInt & i )
{
	gmp_printf( "%Zd", i._xCount );
}

istream & operator >> ( istream & in, BigInt & i )
{
	if ( false ) {  // gmpxx
		in >> i._xCount;
		return in;
	}
	string str;
	in >> str;
	gmp_sscanf( str.c_str(), "%Zd", i._xCount );
	return in;
}

ostream & operator << ( ostream & out, const BigInt & i )
{
    if ( false ) {  // gmpxx
		out << i._xCount;
		return out;
    }
    BigInt copy = i;
    unsigned num_dec_bits = 1 + 10 + 1;  // 1 sign, 2 ^ 33 = 858,993,4592 < 10 ^ 10, 1 '\0'
    copy.Div_2exp( 33 );
	while ( copy != 0 ) {
		num_dec_bits += 10;
		copy.Div_2exp( 33 );
    }
	char * str = new char [num_dec_bits];
	gmp_sprintf( str, "%Zd", i._xCount );
	out << str;
	delete [] str;
    return out;
}

double DoubleQuotient( const BigInt & n, const BigInt & d ) // return n / d
{
    return mpz_get_d( n._xCount ) / mpz_get_d( d._xCount );
}

extern int sscanf( char str[], BigFloat & f )
{
	return gmp_sscanf( str, "%FE", f._xCount );
}

extern void printf( BigFloat & f )
{
	gmp_printf( "%FE", f._xCount );
}

extern double Normalize( const BigFloat & left, const BigFloat & right )
{
	mpf_t tmp;
	mpf_init( tmp );
	mpf_add( tmp, left._xCount, right._xCount );
	mpf_div( tmp, right._xCount, tmp );
	double result = mpf_get_d( tmp );
	mpf_clear( tmp );
	return result;
}

extern double Normalize( const BigFloat & left, const BigFloat & right, BigFloat & sum )
{
	mpf_t tmp;
	mpf_init( tmp );
	mpf_add( sum._xCount, left._xCount, right._xCount );
	mpf_div( tmp, right._xCount, sum._xCount );
	double result = mpf_get_d( tmp );
	mpf_clear( tmp );
	return result;
}

ostream & operator << ( ostream & out, const BigFloat & f )
{
	unsigned num_bits = mpf_get_prec( f._xCount );  // mp_bitcnt_t
	num_bits += 1 + 1 + sizeof( unsigned long long );  // first 1 is sign, second 1 is 'E' and ULLONG_SIZE is exponent
	char * str = new char [num_bits];
	gmp_sprintf( str, "%FE", f._xCount );
	out << str;
	delete [] str;
	return out;
}


}
