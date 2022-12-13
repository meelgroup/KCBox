#ifndef _Time_Memory_h_
#define _Time_Memory_h_

#include "Basic_Functions.h"
#include <unistd.h>
#include <asm/param.h>


namespace KCBox {


/****************************************************************************************************
*                                                                                                   *
*                                         Time                                                      *
*                                                                                                   *
****************************************************************************************************/

class StopWatch
{
public:
	StopWatch() {}
	bool Timeout( double time_bound )
	{
		timeval tmp_time;
		gettimeofday( &tmp_time, NULL );
		return difftime( tmp_time, start_time ) > time_bound;
	}
	bool Start()
	{
		bool ret = gettimeofday(&start_time, NULL);
		stop_time = start_time;
		return !ret;
	}
	bool Stop() { return gettimeofday( &stop_time, NULL ) == 0; }
	double Get_Elapsed_Seconds()
	{
		timeval tmp_time = stop_time;
		if ( stop_time.tv_sec == start_time.tv_sec && stop_time.tv_usec == start_time.tv_usec )
			gettimeofday( &tmp_time, NULL );
		double result = difftime( tmp_time, start_time );
		return result;
	}
private:
	timeval start_time;
	timeval stop_time;
	double difftime( timeval e, timeval b ) { return ( e.tv_sec - b.tv_sec ) + ( e.tv_usec - b.tv_usec ) / 1000000.0; }
};


/****************************************************************************************************
*                                                                                                   *
*                                         Memory                                                    *
*                                                                                                   *
****************************************************************************************************/

inline size_t Total_Used_Memory()  // idea from Mate Soos
{
	using std::ios_base;
	using std::ifstream;
	using std::string;

	// 'file' stat seems to give the most reliable results
	ifstream stat_stream("/proc/self/stat", ios_base::in);

	// dummy vars for leading entries in stat that we don't care about
	string pid, comm, state, ppid, pgrp, session, tty_nr;
	string tpgid, flags, minflt, cminflt, majflt, cmajflt;
	string utime, stime, cutime, cstime, priority, nice;
	string O, itrealvalue, starttime, vsize;
	// the field we want
	size_t rss;

	stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
			   >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
			   >> utime >> stime >> cutime >> cstime >> priority >> nice
			   >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

	stat_stream.close();

	size_t page_size_kb = sysconf(_SC_PAGE_SIZE); // in case x86-64 is configured to use 2MB pages
	size_t resident_set = rss * page_size_kb;
	return resident_set;
}

inline float Total_Elapsed_Seconds()
{
	using std::ios_base;
	using std::ifstream;
	using std::string;

	// 'file' stat seems to give the most reliable results
	ifstream stat_stream("/proc/self/stat", ios_base::in);

	// dummy vars for leading entries in stat that we don't care about
	string pid, comm, state, ppid, pgrp, session, tty_nr;
	string tpgid, flags, minflt, cminflt, majflt, cmajflt;
	long utime, stime;  // the field we want
	string cutime, cstime, priority, nice;
	string O, itrealvalue, starttime, vsize, rss;

	stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
			   >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
			   >> utime >> stime >> cutime >> cstime >> priority >> nice
			   >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

	stat_stream.close();

	return (float)(utime + stime) / HZ;
}


}


#endif
