#include "Template_Library/Basic_Functions.h"
#include "Template_Library/Basic_Structures.h"
#include "Template_Library/Graph_Structures.h"
#include "Primitive_Types/CNF_Formula.h"
#include "Compilers/Integrated_Compiler.h"
#include "Compilers/R2D2_Compiler.h"
#include "Compilers/CCDD_Compiler.h"
#include "Compilers/Partial_Compiler.h"
#include "Counters/KCounter.h"
#include "Counters/WCounter.h"

using namespace KCBox;

#ifndef DEBUG_MODE


Preprocessor_Parameters preprocessor_parameters( "PreLite" );

Counter_Parameters counter_parameters( "ExactMC" );

Compiler_Parameters compiler_parameters( "Panini" );

Sampler_Parameters sampler_parameters( "ExactUS" );

Approx_Counter_Parameters approx_counter_parameters( "PartialKC" );

Tool_Parameters * tools[] = {&preprocessor_parameters, \
	&counter_parameters, \
	&compiler_parameters, \
	&sampler_parameters, \
	&approx_counter_parameters};
const int num_tools = sizeof(tools) / sizeof(Tool_Parameters *);


struct Parameters
{
	char current_path[128];
    char procedure_name[64];
	const char * cnf_file;
	const char * tool;
	BoolOption quiet;
	Parameters(): quiet( "--quiet", "no display of running information", false )
	{
        cnf_file = nullptr;
        tool = nullptr;
	}
} parameters;

void Parse_Basename( const char *argv[] )
{
	int i, j, len = strlen( argv[0] );
	for ( i = len - 1; i >= 0; i-- ) {
		if ( argv[0][i] == '\\' ) break;
		else if ( argv[0][i] == '/' ) break;
	}
	j = i + 1;
	for ( i = 0; i < j; i++ ) parameters.current_path[i] = argv[0][i];
	parameters.current_path[i] = '\0';
	for ( i = 0; i < len - j; i++ ) parameters.procedure_name[i] = argv[0][j+i];
	parameters.procedure_name[i] = '\0';
}

void Print_Usage()
{
	cout << "The usage of " << parameters.procedure_name << " tool [parameters] [--quiet] infile:" << endl;
	cout << "    " << "infile: the cnf file in DIMACS." << endl;
	cout << "    " << "tool: ";
	for ( unsigned i = 0; i < num_tools - 1; i++ ) {
		cout << tools[i]->Tool_Name() << ", ";
	}
	cout << "or " << tools[num_tools - 1]->Tool_Name() << "." << endl;
	cout << "    " << "--quiet: not display running information." << endl;
	cout << "    " << "--help: display options." << endl;
}

void Print_Tool_Additional_Usage()
{
	cout << "Additional option (must be placed after the previous options): " << endl;
	cout << "    " << "--quiet: not display running information." << endl;
	cout << "The last option: MUST be a cnf file in DIMACS." << endl;
}

void Parse_Parameters( int argc, const char *argv[] )
{
	if ( argc == 1 ) {
		cerr << "ERROR: please state a tool!" << endl;
		Print_Usage();
		exit( 1 );
	}
	if ( strcmp( argv[1], "--help" ) == 0 ) {
		Print_Usage();
		exit( 1 );
	}
	int i = 2, t = 0;
	for ( ; t < num_tools; t++ ) {
		if ( strcmp( argv[1], tools[t]->Tool_Name() ) == 0 ) {
			parameters.tool = argv[1];
			if ( !tools[t]->Parse_Parameters( i, argc, argv ) ) {
				tools[t]->Helper( cout );
				exit( 1 );
			}
			break;
		}
	}
	if ( t == num_tools ) {
		cerr << "ERROR: invalid tool!" << endl;
		Print_Usage();
		exit( 1 );
	}
	while ( i < argc ) {
		if ( parameters.quiet.Match( i, argc, argv ) ) continue;
		break;
	}
	if ( parameters.cnf_file == nullptr && i == argc ) {
		cerr << "ERROR: no cnf_file!" << endl;
		Print_Usage();
		exit( 1 );
	}
	if ( parameters.cnf_file == nullptr ) parameters.cnf_file = argv[i++];
	if ( i < argc ) {
		cerr << "ERROR: extra information after the cnf_file \"" << parameters.cnf_file << "\"!" << endl;
		Print_Usage();
		exit( 1 );
	}
}

void Parse_Tool_Parameters( Tool_Parameters & tool_parameter, int argc, const char *argv[] )
{
	if ( argc == 1 || strcmp( argv[1], "--help" ) == 0 ) {
		tool_parameter.Helper( cout );
		Print_Tool_Additional_Usage();
		exit( 1 );
	}
	int i = 1;
	parameters.tool = tool_parameter.Tool_Name();
	if ( !tool_parameter.Parse_Parameters( i, argc, argv ) ) {
		tool_parameter.Helper( cout );
		Print_Tool_Additional_Usage();
		exit( 1 );
	}
	while ( i < argc ) {
		if ( parameters.quiet.Match( i, argc, argv ) ) continue;
		break;
	}
	if ( parameters.cnf_file == nullptr && i == argc ) {
		cerr << "ERROR: no cnf_file!" << endl;
		tool_parameter.Helper( cout );
		Print_Tool_Additional_Usage();
		exit( 1 );
	}
	if ( parameters.cnf_file == nullptr ) parameters.cnf_file = argv[i++];
	if ( i < argc ) {
		cerr << "ERROR: extra information after the cnf_file \"" << parameters.cnf_file << "\"!" << endl;
		tool_parameter.Helper( cout );
		Print_Tool_Additional_Usage();
		exit( 1 );
	}
}

void Test_Preprocessor()
{
	Preprocessor::Test( parameters.cnf_file, preprocessor_parameters.out_file, parameters.quiet );
}

void Test_Counter()
{
	if ( !counter_parameters.weighted ) {
		KCounter::Test( parameters.cnf_file, counter_parameters, parameters.quiet );
	}
	else {
		WCounter::Test( parameters.cnf_file, counter_parameters, parameters.quiet );
	}
}

void Test_Compiler()
{
	if ( strcmp( compiler_parameters.lang, "ROBDD" ) == 0 ) {
        Compiler::Test_OBDD_Compiler( parameters.cnf_file, compiler_parameters, parameters.quiet );
	}
    else if ( strcmp( compiler_parameters.lang, "OBDD[AND]" ) == 0 ) {
        Compiler::Test_OBDDC_Compiler( parameters.cnf_file, compiler_parameters, parameters.quiet );
    }
    else if ( strcmp( compiler_parameters.lang, "R2-D2" ) == 0 ) {
        R2D2_Compiler::Test_R2D2_Compiler( parameters.cnf_file, compiler_parameters );
    }
    else if ( strcmp( compiler_parameters.lang, "CCDD" ) == 0 ) {
		CCDD_Compiler::Test_CCDD_Compiler( parameters.cnf_file, compiler_parameters, parameters.quiet );
    }
    else {
        cerr << "ERROR: invalid language!" << endl;
        Print_Usage();
        exit( 1 );
 	}
}

void Test_Sampler()
{
	if ( !sampler_parameters.weighted ) {
		if ( !sampler_parameters.approx ) {
			CCDD_Compiler::Test_Sampler( parameters.cnf_file, sampler_parameters, parameters.quiet );
		}
		else {
			cerr << "ERROR: Approximately uniform not supported yet!" << endl;
			Print_Usage();
			exit( 1 );
		}
	}
	else {
		if ( !sampler_parameters.approx ) {
			cerr << "ERROR: Weighted uniform not supported yet!" << endl;
			Print_Usage();
			exit( 1 );
		}
		else {
			cerr << "ERROR: Approximately uniform not supported yet!" << endl;
			Print_Usage();
			exit( 1 );
		}
	}
}

void Test_PartialKC()
{
	if ( !approx_counter_parameters.weighted ) {
		Partial_CCDD_Compiler::Test_Approximate_Counter( parameters.cnf_file, approx_counter_parameters, parameters.quiet );
	}
	else {
		cerr << "ERROR: weighted anytime counting not supported yet!" << endl;
	}
}

void Test()
{
    if ( !parameters.quiet ) {
		if ( counter_parameters.competition ) {
			cout << "c o Instance name: " << parameters.cnf_file << endl;
			system( "printf 'c o '" );
			system( "date" );
		}
		else {
			cout << "Instance name: " << parameters.cnf_file << endl;
			system( "date" );
		}
    }
	if ( strcmp( parameters.tool, preprocessor_parameters.Tool_Name() ) == 0 ) {
		Test_Preprocessor();
	}
	else if ( strcmp( parameters.tool, compiler_parameters.Tool_Name() ) == 0 ) {
		Test_Compiler();
	}
	else if ( strcmp( parameters.tool, counter_parameters.Tool_Name() ) == 0 ) {
		if ( counter_parameters.diffversion == 1 ) Test_Counter();
	}
	else if ( strcmp( parameters.tool, sampler_parameters.Tool_Name() ) == 0 ) {
		Test_Sampler();
	}
	else if ( strcmp( parameters.tool, approx_counter_parameters.Tool_Name() ) == 0 ) {
		Test_PartialKC();
	}
}

int main( int argc, const char *argv[] )
{
/*	argc = 12;
	argv[0] = "PartialKC.exe";
	argv[1] = "--seed";
	argv[2] = "123456789";
	argv[3] = "--sample";
	argv[4] = "1000";
	argv[5] = "--interval";
	argv[6] = "1";
	argv[7] = "--time";
	argv[8] = "300s";
	argv[9] = "--mode";
	argv[10] = "2";
	argv[11] = "cnf.txt";
//	argv[11] = "/home/leven/Projects/model-counters/benchmarks/SampleCount-benchmarks/langford/lang16.txt";
	for ( unsigned i = 0; i < argc; i++ ) cout << argv[i] << endl;*/
	Parse_Basename( argv );
	int t = 0;
	for ( ; t < num_tools; t++ ) {
		if ( strcmp( parameters.procedure_name, tools[t]->Tool_Name() ) == 0 ) {
			Parse_Tool_Parameters( *tools[t], argc, argv );
			break;
		}
	}
	if ( t == num_tools ) Parse_Parameters( argc, argv );
	Test();
	return 0;
}

#else

void Debug()
{
	cout << "Begin Debugging..." << endl;
//	CNF_Formula::Debug();
//	Lit_Equivalency::Debug();
//	Solver::Debug();
//	Preprocessor::Debug();
//	Compiler::Debug();
//	RCDD_Compiler::Debug();
//	CCDD_Compiler::Debug();
//	R2D2_Compiler::Debug();
//	Counter::Debug();
//	KCounter::Debug();
//	WCounter::Debug();
	Partial_CCDD_Compiler::Debug();
//	CDD_Manager::Debug_Uniqueness();
//	CDD_Manager::Debug_Convert();
//	CDD_Manager::Debug_Convert_Down();
//	DNNF_Manager::Debug();
//	Prob_BDDL_Manager::Debug_Conjoin();
	cout << "Debugging done." << endl;
	system( "./pause" );
	exit( 0 );
}

int main( int argc, char *argv[] )
{
    Debug();
	return 0;
}

#endif
