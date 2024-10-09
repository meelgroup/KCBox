#ifndef _Options_h_
#define _Options_h_

#include <limits.h>
#include "Basic_Functions.h"


namespace KCBox {


class Option
{
protected:
	const char * _name;
	const char * _description;
	bool _exi;
public:
	Option( const char * name, const char * description ): _name( name ), _description( description ), _exi( false ) {}
	bool Matched( const char * argv ) { return strcmp( argv, _name ) == 0; }
	virtual int Match( int & i, int argc, const char * argv[] ) = 0;
	void Register()
	{
		if ( _exi ) {
			cerr << "ERROR: extra " << _name << "!" << endl;
			exit( 1 );
		}
		_exi = true;
	}
	bool Exists() const { return _exi; }
	const char * Name() { return _name; }
	virtual void Display( ostream & out ) = 0;
};

class BoolOption: public Option
{
protected:
	bool _val;
	bool _default;
public:
	BoolOption( const char * name, const char * description, bool value = false ):
		Option( name, description ),
		_val( value ), _default( value ) {}
	operator bool () { return _val; }
	int Match( int & i, int argc, const char * argv[] )
	{
		assert( i < argc );
		if ( Matched( argv[i] ) ) {
			i++;
			Register();
			_val = !_val;
			return true;
		}
		else return false;
	}
	void Display( ostream & out )
	{
		out << '\t' << _name << ": " << _description << " (default: ";
		if ( _default ) out << "true";
		else out << "false";
		out << ")" << endl;
	}
};

class IntOption: public Option
{
protected:
	int _val;
	int _default;
	int _lb;
	int _ub;
public:
	IntOption( const char * name, const char * description, const int value ):
		Option( name, description ),
		_val( value ), _default( value ), _lb( INT_MIN ), _ub( INT_MAX ) {}
	IntOption( const char * name, const char * description, const int value, int lb, int ub ):
		Option( name, description ),
		_val( value ), _default( value ), _lb( lb ), _ub( ub ) {}
	operator int () { return _val; }
	int Match( int & i, int argc, const char * argv[] )
	{
		if ( Matched( argv[i] ) ) {
			i++;
			if ( i >= argc )  return -1;  // error
			if ( sscanf( argv[i++], "%d", &_val ) != 1 ) return -1;  // error
			Register();
			if ( _val < _lb || _val > _ub  ) {
				return -1;
			}
			else return 1;  // match
		}
		else return 0;  // no match
	}
	void Display( ostream & out )
	{
		out << '\t' << _name << ": " << _description << " (";
		if ( _lb != INT_MIN || _ub != INT_MAX ) {
			out << "[";
			if ( _lb != INT_MIN ) out << _lb;
			out << ", ";
			if ( _ub != INT_MAX ) out << _ub;
			out << "], ";
		}
		out << "default: " << _default << ")" << endl;
	}
};

class FloatOption: public Option
{
protected:
	float _val;
	float _default;
public:
	FloatOption( const char * name, const char * description, const float value ):
		Option( name, description ), _val( value ), _default( value ) {}
	operator float () { return _val; }
	int Match( int & i, int argc, const char * argv[] )
	{
		if ( Matched( argv[i] ) ) {
			i++;
			if ( i >= argc )  return -1;  // error
			if ( sscanf( argv[i++], "%f", &_val ) != 1 ) return -1;  // error
			Register();
			return 1;  // match
		}
		else return 0;  // no match
	}
	void Display( ostream & out )
	{
		out << '\t' << _name << ": " << _description << " (default: " << _default << ")" << endl;
	}
};

class StringOption: public Option
{
protected:
	const char * _val;
	const char * _default;
public:
	StringOption( const char * name, const char * description, const char * value = nullptr ):
		Option( name, description ), _val( value ), _default( value ) {}
	operator const char * () { return _val; }
	int Match( int & i, int argc, const char * argv[] )
	{
		if ( Matched( argv[i] ) ) {
			i++;
			if ( i >= argc )  return -1;  // error
			Register();
			_val = argv[i++];
			return 1;
		}
		else return 0;
	}
	void Display( ostream & out )
	{
		if ( _default == nullptr ) out << '\t' << _name << ": " << _description << " (default: )" << endl;
		else out << '\t' << _name << ": " << _description << " (default: " << _default << ")" << endl;
	}
};

class Tool_Parameters
{
protected:
	const char * _tool_name;
	vector<Option *> _options;
	const char * _version;
public:
	Tool_Parameters( const char * tool ): _tool_name( tool ), _version( nullptr ) {}
	const char * Tool_Name() { return _tool_name; }
	void Add_Option( Option * option )
	{
		_options.push_back( option );
	}
	Option * operator [] ( const char * option_name )
	{
		for ( unsigned i = 0; i < _options.size(); i++ ) {
			if ( strcmp( _options[i]->Name(), option_name ) == 0 ) return _options[i];
		}
		return nullptr;
	}
	void Set_Version( const char * version )
	{
		if ( _version != nullptr ) {
			cerr << "ERROR: the version was set!" << endl;
			exit( 1 );
		}
		_version = version;
	}
	virtual bool Parse_Parameters( int & i, int argc, const char *argv[] )
	{
		int stat;
		while ( i < argc ) {
			if ( strcmp( argv[i], "--help" ) == 0 ) {
				Helper( cerr );
				exit( 1 );
			}
			if ( strcmp( argv[i], "--version" ) == 0 ) {
				if ( _version == nullptr ) {
					cout << "ERROR: no version!" << endl;
					return false;
				}
				else {
					cout << "version " << _version << endl;
					exit( 0 );
				}
			}
			unsigned j = 0;
			for ( ; j < _options.size(); j++ ) {
				if ( ( stat = _options[j]->Match( i, argc, argv ) ) != 0 ) {
					if ( stat == -1 ) {
						cerr << "ERROR: wrong usage for " << _options[j]->Name() << endl;
						return false;
					}
					break;
				}
			}
			if ( j == _options.size() ) break;
		}
		return true;
	}
	virtual void Helper( ostream & out )
	{
		out << "The usage of " << _tool_name << ": " << endl;
		for ( unsigned i = 0; i < _options.size(); i++ ) {
			_options[i]->Display( out );
		}
		out << endl;
	}
};


}


#endif
