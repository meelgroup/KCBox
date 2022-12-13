#include "Solver_Krom.h"


namespace KCBox {


Solver_Krom::Solver_Krom( Variable max_var, bool * seen, Model_Pool * pool ) :
_num_dec_stack( 0 ),
ext_model_seen( seen ),
ext_model_pool( pool )
{
	Allocate_and_Init_Auxiliary_Memory( max_var );
}

Solver_Krom::~Solver_Krom()
{
	if ( _max_var != Variable::undef ) Free_Auxiliary_Memory();
}

void Solver_Krom::Allocate_and_Init_Auxiliary_Memory( Variable  max_var )  // ToDo: whether can we optimize when mv < max_var
{
	Assignment::Allocate_and_Init_Auxiliary_Memory( max_var );
	_model_seen = new bool [2 * _max_var + 4];  // The last two bits are used to mark 2*_max_var + 2 and 2*_max_var + 3 not assigned
	_binary_clauses = new vector<Literal> [2 * max_var + 2];
	_original_num_binary_clauses = new unsigned [2 * max_var + 2];
	_dec_stack = new Literal [max_var + 1];
}

void Solver_Krom::Free_Auxiliary_Memory()
{
	delete [] _model_seen;
	delete [] _binary_clauses;
	delete [] _original_num_binary_clauses;
	delete [] _dec_stack;
}

size_t Solver_Krom::Memory()
{
    size_t mem = 0;
    for ( Variable i = Variable::start; i <= _max_var; i++ ) {
        mem += _binary_clauses[i + i].capacity() * sizeof(unsigned);
        mem += _binary_clauses[i + i + 1].capacity() * sizeof(unsigned);
    }
	return mem;
}

void Solver_Krom::Add_Binary_Clause_Naive( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
    _binary_clauses[lit2].push_back( lit1 );
}

void Solver_Krom::Add_Binary_Clause_From_Long( Big_Clause & cl, Model & seed_model )
{
    assert( cl.Size() >= 3 );
	if ( Clause_GE_3_SAT( cl ) ) return;
	unsigned i, j;
	Literal lit = Literal::undef;
	for ( i = 0; seed_model[cl[i].Var()] != cl[i].Sign(); i++ ) {}
	for ( j = i + 1; j < cl.Size(); j++ ) {
		if ( Lit_UNSAT( cl[j] ) ) continue;
		if ( seed_model.Satisfy( cl[j] ) ) break;
		lit = cl[j];
	}
	if ( j < cl.Size() ) Add_Binary_Clause( cl[i], cl[j] );
	else if ( lit != Literal::undef ) Add_Binary_Clause( cl[i], lit );
	else {
        for ( j = 0; j < i && Lit_UNSAT( cl[j] ); j++ ) {}
        if ( j < i ) Add_Binary_Clause( cl[i], cl[j] );  /// NOTE: there are new binary clauses generated from long clauses
        else {
            Assign( cl[i] );  /// all literals are falsified by seed_model except cl[i]
            assert( seed_model.Satisfy( cl[i] ) );
            BCP_Krom( _num_dec_stack - 1 );  /// NOTE: new binary clauses generated from long clauses are BCPed in Add_Binary_Clause_From_Long
        }
	}
}

void Solver_Krom::Add_Binary_Clause( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr;
	for ( itr = _binary_clauses[lit1].begin(); itr->Var() != lit2.Var(); itr++ ) {}  /// NOTE: because Block_Clauses and Block_Lits are employed
	if ( itr != _binary_clauses[lit1].end() - 1 ) {
		if ( *itr != lit2 ) {  // neg appears
			Assign( lit1 );
			BCP_Krom( _num_dec_stack - 1 );  // need employ BCP_Krom for new clauses
		}
		_binary_clauses[lit1].pop_back();
	}
	else _binary_clauses[lit2].push_back( lit1 );
}

void Solver_Krom::Mark_Non_Imp_Krom( Model & seed_model, vector<Model *> & new_models )
{
//    Display_Non_Implied_Literals( cout );
//    Display_Binary_Clauses( cout );
	Literal lit;
	for ( Variable i = Variable::start; ( lit = Pick_Imp( i ) ) <= 2 * _max_var + 1; i++ ) {
		unsigned old_num_d_stack = _num_dec_stack;
		Assign( ~lit );
		if ( !BCP_Krom( old_num_d_stack ) ) {  // Annote: implies lit
			for ( _num_dec_stack--; _num_dec_stack > old_num_d_stack; _num_dec_stack-- ) {
				_assignment[_dec_stack[_num_dec_stack].Var()] = lbool::unknown;
			}
			Assign( lit );
			assert( seed_model.Satisfy( lit ) );
			BCP_Krom( old_num_d_stack );
		}
		else {
            Model * model = ext_model_pool->Allocate();
            for ( Variable j = Variable::start; j <= _max_var; j++ ) {
                model->Assign( j, seed_model[j] );
            }
			for ( _num_dec_stack--; _num_dec_stack > old_num_d_stack; _num_dec_stack-- ) {
				model->Assign( _dec_stack[_num_dec_stack] );
				_assignment[_dec_stack[_num_dec_stack].Var()] = lbool::unknown;
				ext_model_seen[_dec_stack[_num_dec_stack]] = true;
			}
            model->Assign( ~lit );
			_assignment[lit.Var()] = lbool::unknown;
			ext_model_seen[~lit] = true;
//			model->Display( _max_var, cout );
			new_models.push_back( model );
		}
	}
}

Literal Solver_Krom::Pick_Imp( Variable & i )
{
	// the number of the elements of ext_model_seen is not more than 2 * _max_var + 4
	for ( ; Var_Decided( i ) + ext_model_seen[i + i] + ext_model_seen[i + i + 1] > 1; i++ ) {}
	return Literal( i, ext_model_seen[i + i + 1] );
}

void Solver_Krom::Assign( Literal lit )
{
	_dec_stack[_num_dec_stack++] = lit;
	_assignment[lit.Var()] = lit.Sign();
}

bool Solver_Krom::BCP_Krom( unsigned start )
{
	unsigned i, size;
	for ( ; start < _num_dec_stack; start++ ) {
		unsigned lit = ~_dec_stack[start];
		for ( i = 0, size = _binary_clauses[lit].size(); i < size; i++ ) {
			if ( Lit_UNSAT( _binary_clauses[lit][i] ) ) return false;
			else if ( Lit_Undecided( _binary_clauses[lit][i] ) ) {
				Assign( _binary_clauses[lit][i] );
			}
		}
	}
	return true;
}

void Solver_Krom::Un_BCP( unsigned start )
{
    while ( _num_dec_stack > start ) {
        Literal lit = _dec_stack[--_num_dec_stack];
        _assignment[lit.Var()] = lbool::unknown;
    }
}

void Solver_Krom::Assign_Original_Binary_Clauses( Literal lit )
{
    unsigned i;
    Assign( lit );
    for ( i = 0; i < _original_num_binary_clauses[lit]; i++ ) {  // NOTE: removing the original binary clauses is different from the binary clauses from long
        Literal lit2 = _binary_clauses[lit][i];
        vector<Literal>::iterator begin = _binary_clauses[lit2].begin(), itr;
        for ( itr = begin; *itr != lit; itr++ ) {}
        _original_num_binary_clauses[lit2]--;
        Swap_Two_Elements_Vector( _binary_clauses[lit2], itr - begin, _original_num_binary_clauses[lit2] );
        Simply_Erase_Vector_Element( _binary_clauses[lit2], _original_num_binary_clauses[lit2] );  // Annote: remove lit from pos
    }
    for ( ; i < _binary_clauses[lit].size(); i++ ) {
        Literal lit2 = _binary_clauses[lit][i];
        vector<Literal>::iterator begin = _binary_clauses[lit2].begin(), itr;
        for ( itr = begin; *itr != lit; itr++ ) {}
        Simply_Erase_Vector_Element( _binary_clauses[lit2], itr - begin );  // Annote: remove lit from pos
        _original_num_binary_clauses[lit2]--;
    }
    _binary_clauses[lit].clear();  // Annote: remove pos from _binary_clauses[lit]
    _original_num_binary_clauses[lit] = 0;
}

void Solver_Krom::Reset()
{
	while ( _num_dec_stack > 0 ) {
	    Literal lit = _dec_stack[--_num_dec_stack];
		_assignment[lit.Var()] = lbool::unknown;
	}
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		_binary_clauses[i + i].clear();
		_binary_clauses[i + i + 1].clear();
	    _original_num_binary_clauses[i + i] = 0;
	    _original_num_binary_clauses[i + i + 1] = 0;
	}
}

void Solver_Krom::Add_Binary_Clause_After_Blocking( Literal lit1, Literal lit2 )
{
	_binary_clauses[lit1].push_back( lit2 );
	vector<Literal>::iterator itr;
	for ( itr = _binary_clauses[lit1].begin() + _original_num_binary_clauses[lit1]; itr->Var() != lit2.Var(); itr++ ) {}  /// NOTE: because Block_Clauses and Block_Lits are employed
	if ( itr != _binary_clauses[lit1].end() - 1 ) {
		if ( *itr != lit2 ) {  // neg appears
			Assign( lit1 );
			BCP_Krom( _num_dec_stack - 1 );  // need employ BCP_Krom for new clauses
		}
		_binary_clauses[lit1].pop_back();
	}
	else _binary_clauses[lit2].push_back( lit1 );
}

void Solver_Krom::Mark_Non_Imp_Krom_Without_Reset( Component & comp, Model & seed_model, vector<Model *> & new_models )
{
	Literal lit;
	vector<unsigned>::const_iterator itr, begin = comp.VarIDs_Begin(), end = comp.VarIDs_End();
	for ( itr = begin; ( lit = Pick_Imp( itr ) ) <= 2 * _max_var + 1; itr++ ) {
		unsigned old_num_d_stack = _num_dec_stack;
		Assign( ~lit );
		if ( !BCP_Krom( old_num_d_stack ) ) {  // Annote: implies lit
			for ( _num_dec_stack--; _num_dec_stack > old_num_d_stack; _num_dec_stack-- ) {
				_assignment[_dec_stack[_num_dec_stack].Var()] = lbool::unknown;
			}
			Assign( lit );
			assert( seed_model.Satisfy( lit ) );
			BCP_Krom( old_num_d_stack );
		}
		else {
            Model * model = ext_model_pool->Allocate();
            for ( vector<unsigned>::const_iterator it = begin; it < end; it++ ) {
                model->Assign( Variable( *it ), seed_model[*it] );
            }
			for ( _num_dec_stack--; _num_dec_stack > old_num_d_stack; _num_dec_stack-- ) {
				model->Assign( _dec_stack[_num_dec_stack] );
				_assignment[_dec_stack[_num_dec_stack].Var()] = lbool::unknown;
				ext_model_seen[_dec_stack[_num_dec_stack]] = true;
			}
            model->Assign( ~lit );
			_assignment[lit.Var()] = lbool::unknown;
			ext_model_seen[~lit] = true;
			new_models.push_back( model );
		}
	}
}

Literal Solver_Krom::Pick_Imp( vector<unsigned>::const_iterator & itr )
{
	// the number of the elements of ext_model_seen is not more than 2 * _max_var + 4
	for ( ; Var_Decided( Variable( *itr ) ) + ext_model_seen[*itr + *itr] + ext_model_seen[*itr + *itr + 1] > 1; itr++ ) {}
	return Literal( Variable( *itr ), ext_model_seen[*itr + *itr + 1] );
}

void Solver_Krom::Verify_Model_Krom( Model & model )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		Literal lit( i, !model[i] );
		for ( unsigned j = 0; j < _binary_clauses[lit].size(); j++ ) {
			Literal li = _binary_clauses[lit][j];
			assert( model.Satisfy( li ) );
		}
	}
}

void Solver_Krom::Display_Non_Implied_Literals( ostream & fout )
{
	for ( Variable i = Variable::start; i <= _max_var; i++ ) {
		if ( ext_model_seen[i + i] ) fout << "-" << ExtVar( i ) << " ";
		if ( ext_model_seen[i + i + 1] ) fout << ExtVar( i ) << " ";
	}
	fout << endl;
}

void Solver_Krom::Display_Binary_Clauses( ostream & fout )
{
	if ( _max_var == Variable::undef ) {
		fout << "No data."<< endl;
		return;
	}
	unsigned i, j, num = 0, index = 0;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		num += _binary_clauses[i + i].size() + _binary_clauses[i + i + 1].size();
	}
	fout << "p cnf " << _max_var - Variable::start + 1 << ' ' << num << endl;
	for ( i = Variable::start; i <= _max_var; i++ ) {
		for ( j = 0; j < _binary_clauses[i + i].size(); j++ ) {
			if ( i + i > _binary_clauses[i + i][j] ) continue;
			fout << index++ << ":\t";
			fout << '-' << i << " ";
			fout << ExtLit( _binary_clauses[i + i][j] );
			fout << " 0" << endl;
		}
		for ( j = 0; j < _binary_clauses[i + i + 1].size(); j++ ) {
			if ( i + i + 1 > _binary_clauses[i + i + 1][j] ) continue;
			fout << index++ << ":\t";
			fout << i << " ";
			fout << ExtLit( _binary_clauses[i + i + 1][j] );
			fout << " 0" << endl;
		}
	}
}

void Solver_Krom::Display_Decision_Stack( ostream & fout )
{
	for ( unsigned i = 0; i < _num_dec_stack; i++ ) {
		fout << ExtLit( _dec_stack[i] ) << " ";
	}
	fout << endl;
}


}
