#include "DAG.h"


namespace KCBox {


const NodeID NodeID::bot( 0 );
const NodeID NodeID::top( 1 );
const NodeID NodeID::undef( UNSIGNED_UNDEF );

Diagram_Manager::Diagram_Manager( Variable max_var )
{
    if ( max_var != Variable::undef ) Allocate_and_Init_Auxiliary_Memory( max_var );
}

void Diagram_Manager::Allocate_and_Init_Auxiliary_Memory( Variable max_var )
{
    Assignment::Allocate_and_Init_Auxiliary_Memory( max_var );
	_path = new NodeID [2 * _max_var + 2];
	_path_mark = new unsigned [2 * _max_var + 2];
	_node_stack = new NodeID [2 * _max_var + 4];
	_node_mark_stack = new unsigned [2 * _max_var + 4];
	_var_seen = new bool [_max_var + 1];
	_lit_seen = new bool [2 * _max_var + 2];
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_var_seen[i] = false;
		_lit_seen[i + i] = false;
		_lit_seen[i + i + 1] = false;
	}
}

Diagram_Manager::~Diagram_Manager()
{
    if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
    if ( !_allocated_nodes.Empty() ) {
		cerr << "ERROR[Diagram_Manager]: please free allocated nodes first!" << endl;
		exit( 1 );
    }
}

void Diagram_Manager::Free_Auxiliary_Memory()
{
	delete [] _path;
	delete [] _path_mark;
	delete [] _node_stack;
	delete [] _node_mark_stack;
	delete [] _var_seen;
	delete [] _lit_seen;
}

size_t Diagram_Manager::Memory()
{
	return 9 * _max_var * sizeof(unsigned) + 3 * _max_var * sizeof( bool );
}


}
