#ifndef _Debug_Functions_h_
#define _Debug_Functions_h_

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <queue>
#include <map>
#include <bitset>
#include <algorithm>
using namespace std;


namespace KCBox {


//#define DEBUG_MODE
#define DEBUG_ON    true
#define DEBUG_OFF   false
#define DEBUG_UNCOMPLETE    false
#define SHIELD_OPTIMIZATION	true
#define APPLY_OPTIMIZATION	true
#define ASSERT( statement ) if ( DEBUG_ON ) assert( statement )


extern inline void Debug_Print_Visit_Number( ostream & out, unsigned lineno, unsigned print_bound = 1 )
{
    static map<unsigned, unsigned> visit_infor;
    map<unsigned, unsigned>::iterator itr = visit_infor.find( lineno );
    if( itr == visit_infor.end() ) {
        visit_infor.insert( map<unsigned, unsigned>::value_type( lineno, 1 ) );
        if ( print_bound == 1 ) out << "#visit of Line " << lineno << ": " << 1 << endl;
    } else {
        itr->second++;
        if ( itr->second >= print_bound )  out << "#visit of Line " << lineno << ": " << itr->second << endl;
    }
    out.flush();
}

template<typename T>
extern inline void Debug_Pause( ostream & out, unsigned lineno, const T & var, const T stop )
{
    static map<unsigned, unsigned> visit_infor;
    map<unsigned, unsigned>::iterator itr = visit_infor.find( lineno );
    if( itr == visit_infor.end() ) {
        visit_infor.insert( map<unsigned, unsigned>::value_type( lineno, 1 ) );
    }
    else itr->second++;
	if ( var == stop ) {
		out << "pause in line " << lineno << " at #visits: " << itr->second << endl;
		system( "Debug_Library/pause" );
	}
}

template<typename T>
extern inline void Debug_Print_Infor( ostream & out, T & infor, unsigned lineno, unsigned print_bound = 1 )
{
    static map<unsigned, unsigned> visit_infor;
    map<unsigned, unsigned>::iterator itr = visit_infor.find( lineno );
    if( itr == visit_infor.end() ) {
        visit_infor.insert( map<unsigned, unsigned>::value_type( lineno, 1 ) );
        if ( print_bound == 1 ) out << infor << endl;
    } else {
        itr->second++;
        if ( itr->second >= print_bound )  out << infor << endl;
    }
    out.flush();
}

void Basename( const char * filename, char * newname );

extern inline void Debug_Print_Visit_Number( ostream & out, const char * filename, unsigned lineno, unsigned print_bound = 1 )
{
    // __LINE__, __FILE__, __FUNCTION__
    char newname[64];
    Basename( filename, newname );
    out << newname << " ";
    Debug_Print_Visit_Number( out, lineno, print_bound );
}


}


#endif
