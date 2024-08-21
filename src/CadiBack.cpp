#include <cassert>
#include <climits>
#include "CadiBack.h"


namespace KCBox {


int CadiBack::solve()
{
	statistics.calls.total++;
	int res = CaDiCaL::Solver::solve();
	if (res == 10) {
		statistics.calls.sat++;
	}
	else {
		assert (res == 20);
		statistics.calls.unsat++;
	}
	return res;
}

void CadiBack::set_options( bool no_fixed, bool no_flip, bool really_flip, bool no_inprocessing, bool one_by_one, bool chunking, bool models )
{
	options.no_fixed = no_fixed;
	options.no_flip = no_flip;
	options.really_flip = really_flip;
	options.no_inprocessing = no_inprocessing;
	options.one_by_one = one_by_one;
	options.chunking = chunking;
	options.models = models;
}

void CadiBack::reset_options()
{
	options.no_fixed = false;
	options.no_flip = true;
	options.really_flip = false;
	options.no_inprocessing = false;
	options.one_by_one = true;
	options.chunking = false;
	options.models = true;
}

bool CadiBack::calculate( Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool )
{
	assert( !options.one_by_one || !options.chunking );
	assert( options.models || models.empty() );
	calculate_pre( manager );
	if ( models.empty() ) {
		int res = solve( manager );
		if ( res == 20 ) {
			calculate_post( manager );
			return false;
		}
		add_model( models, model_pool );
		init_candidates( manager, models );
		try_to_flip_remaining( models, model_pool );
	} else init_candidates( manager, models );
	unsigned constraint_limit = UINT_MAX; // Adapted dynamically using 'last'.
	int last_rsl = 10;                  // Last solver result.
	while ( !_candidates.empty() ) {
		if ( !options.no_fixed && fix_candidate( 0 ) ) continue;
		if ( !options.one_by_one && options.chunking ) {
			if ( last_rsl == 20 )
				constraint_limit = (constraint_limit < UINT_MAX / 8) ? 8 * constraint_limit : UINT_MAX;
			else constraint_limit = 1;
		}
		if ( !options.one_by_one && constraint_limit > 1 ) {
			assert (constraint_limit > 1);
			for ( _constraint_size = 1; _constraint_size < _candidates.size(); ) {
				if ( !options.no_fixed && fix_candidate( _constraint_size ) ) continue;
				_constraint_size++;
				if ( _constraint_size == constraint_limit ) break;
			}
			if ( _constraint_size == 1 ) {
				last_rsl = calculate_one_by_one( manager, models, model_pool );
				if ( last_rsl == 10 ) add_model( models, model_pool );
				continue;
			}
			for ( unsigned i = 0; i < _constraint_size; i++ ) {
				constrain( -ExtLit( _candidates[i] ) );
			}
			constrain(0);
			last_rsl = solve( manager );
			if ( last_rsl == 10 ) {
				add_model( models, model_pool );
				filter_candidates();
				try_to_flip_remaining( models, model_pool );
			} else {
				assert (last_rsl == 20);
				backbone_variables(); // Plural!  So all assumed.
			}
		} else {
			last_rsl = calculate_one_by_one( manager, models, model_pool );
			if ( last_rsl == 10 ) add_model( models, model_pool );
		}
	}
	calculate_post( manager );
	return true;
}

void CadiBack::calculate_pre( Decision_Manager & manager )
{
	assert( (unsigned)(vars()) <= NumVars( manager.Max_Var() ) );  /// some variables might not really appear
	_max_var = (unsigned)(vars());
	_backbones = new Literal [_max_var + 1];
	_assumed = new bool [_max_var + 1];
	for ( Variable x = Variable::start; x <= _max_var; x++) {
		_backbones[x] = Literal::undef;
		_assumed[x] = false;
	}
	for ( unsigned i = 0; i < manager._num_dec_stack; i++ ) {
		_assumed[manager._dec_stack[i].Var()] = true;
	}
}

int CadiBack::solve( Decision_Manager & manager )
{
	for ( unsigned i = 0; i < manager._num_dec_stack; i++ ) {
		int lit = ExtLit( manager._dec_stack[i] );
		assume( lit );
	}
	return solve();
}

void CadiBack::add_model( vector<Model *> & models, Model_Pool * model_pool )
{
	if ( !options.models ) return;
	Model * model = model_pool->Allocate();
	for ( Variable x = Variable::start; x <= _max_var; x++) {
		model->Assign( x, val(x) > 0 );
	}
	for ( Variable x = _max_var.Next(); x <= model_pool->Max_Var(); x++) {
		model->Assign( x, false );
	}
    models.push_back( model );
}

void CadiBack::init_candidates( Decision_Manager & manager, vector<Model *> & models )
{
	for ( unsigned i = 0; i < manager._num_dec_stack; i++ ) {
		Variable var = manager._dec_stack[i].Var();
		_backbones[var] = manager._dec_stack[i];
	}
	if ( models.empty() ) {
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			if ( _backbones[x] != Literal::undef ) continue;
			_candidates.push_back( Literal( x, val(x) > 0 ) );
		}
		return;
	}
	Model & first_model = *(models[0]);
	if ( models.size() == 1 ) {
		for ( Variable x = Variable::start; x <= _max_var; x++ ) {
			if ( _backbones[x] != Literal::undef ) continue;
			_candidates.push_back( Literal( x, first_model[x] ) );
		}
	} else {
		for ( Variable x = Variable::start; x <= _max_var; x++) {
			if ( _backbones[x] != Literal::undef ) continue;
			unsigned m = 1;
			for ( ; m < models.size(); m++ ) {
				if ( (*models[m])[x] != first_model[x] ) break;
			}
			if ( m == models.size() ) {
				_candidates.push_back( Literal( x, first_model[x] ) );
			}
		}
	}
}

void CadiBack::try_to_flip_remaining( vector<Model *> & models, Model_Pool * model_pool )
{
	if (options.no_flip) return;
	for ( unsigned i = 0; i < _candidates.size(); ) {
		Literal lit = _candidates[i];
		int elit = ExtLit( lit );
		if (options.really_flip) {
			if ( !flip( elit ) ) {
				i++;
				continue;
			}
			statistics.flipped++;
		} else {
			if ( !flippable( elit ) ) {
				i++;
				continue;
			}
			statistics.flippable++;
		}
		drop_candidate( i );
		add_model( models, model_pool );
		if ( options.models ) models.back()->Assign( ~lit );
	}
}

void CadiBack::drop_candidate( unsigned pos )
{
	Variable var = _candidates[pos].Var();
	assert( _backbones[var] == Literal::undef );
	_candidates[pos] = _candidates.back();
	_candidates.pop_back();
	statistics.dropped++;
}

bool CadiBack::fix_candidate( unsigned pos )
{
	assert (!options.no_fixed);
	int tmp = fixed( ExtLit( _candidates[pos] ) );
	if ( !tmp ) return false;
	if (tmp > 0) backbone_variable( pos );
	if (tmp < 0) drop_candidate( pos );
	statistics.fixed++;
	return true;
}

void CadiBack::backbone_variable( unsigned pos )
{
	Variable var = _candidates[pos].Var();
	_backbones[var] = _candidates[pos];
	_candidates[pos] = _candidates.back();
	_candidates.pop_back();
	statistics.backbones++;
}

void CadiBack::filter_candidates()
{
	for ( unsigned i = 0; i < _candidates.size(); ) {
		if ( !filter_candidate( i ) ) i++;
	}
}

bool CadiBack::filter_candidate ( unsigned pos )
{
	Variable var = _candidates[pos].Var();
	Literal assignment( var, val(var) > 0 ); // Legacy support.
	if ( _candidates[pos] == assignment ) return false;
	statistics.filtered++;
	drop_candidate( pos );
	return true;
}

void CadiBack::backbone_variables()
{
	if ( _constraint_size == 1 ) {
		backbone_variable( 0 );
		return;
	}
	Variable var = _candidates[0].Var();
	_backbones[var] = _candidates[0];
	var = _candidates[1].Var();
	_backbones[var] = _candidates[1];
	for ( unsigned i = 2; i < _constraint_size; i++ ) {
		var = _candidates[i].Var();
		_backbones[var] = _candidates[i];
	}
	_candidates.erase( _candidates.begin(), _candidates.begin() + _constraint_size );
	statistics.backbones += _constraint_size;
}

int CadiBack::calculate_one_by_one( Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool )
{
	assume( -ExtLit( _candidates[0] ) );
	int rsl = solve( manager );
	if ( rsl == 10 ) {
		drop_candidate( 0 );
		filter_candidates();
		try_to_flip_remaining( models, model_pool );
	} else {
		assert (rsl == 20);
		backbone_variable( 0 ); // Singular! So only this one.
	}
	return rsl;
}

void CadiBack::calculate_post( Decision_Manager & manager )
{
    for ( Variable x = Variable::start; x <= _max_var; x++) {
    	if ( _backbones[x] != Literal::undef && !_assumed[x] ) manager.Assign( _backbones[x] );
    }
	delete [] _backbones;
	delete [] _assumed;
}

void CadiBack::calculate( Component & comp, Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool )
{
	assert( !options.one_by_one || !options.chunking );
	assert( options.models );
	calculate_pre( comp, manager );
	if ( models.empty() ) {
		int res = solve( manager );
		assert( res == 10 );
		add_model( comp, models, model_pool );
		init_candidates( comp, manager, models );
		try_to_flip_remaining( comp, models, model_pool );
	} else init_candidates( comp, manager, models );
	unsigned constraint_limit = UINT_MAX; // Adapted dynamically using 'last'.
	int last_rsl = 10;                  // Last solver result.
	while ( !_candidates.empty() ) {
		if ( !options.no_fixed && fix_candidate( 0 ) ) continue;
		if ( !options.one_by_one && options.chunking ) {
			if ( last_rsl == 20 )
				constraint_limit = (constraint_limit < UINT_MAX / 8) ? 8 * constraint_limit : UINT_MAX;
			else constraint_limit = 1;
		}
		if ( !options.one_by_one && constraint_limit > 1 ) {
			assert (constraint_limit > 1);
			for ( _constraint_size = 1; _constraint_size < _candidates.size(); ) {
				if ( !options.no_fixed && fix_candidate( _constraint_size ) ) continue;
				_constraint_size++;
				if ( _constraint_size == constraint_limit ) break;
			}
			if ( _constraint_size == 1 ) {
				last_rsl = calculate_one_by_one( comp, manager, models, model_pool );
				if ( last_rsl == 10 ) add_model( comp, models, model_pool );
				continue;
			}
			for ( unsigned i = 0; i < _constraint_size; i++ ) {
				constrain( -ExtLit( _candidates[i] ) );
			}
			constrain(0);
			last_rsl = solve( manager );
			if ( last_rsl == 10 ) {
				add_model( comp, models, model_pool );
				filter_candidates();
				try_to_flip_remaining( comp, models, model_pool );
			} else {
				assert (last_rsl == 20);
				backbone_variables(); // Plural!  So all assumed.
			}
		} else {
			last_rsl = calculate_one_by_one( comp, manager, models, model_pool );
			if ( last_rsl == 10 ) add_model( comp, models, model_pool );
		}
	}
	calculate_post( comp, manager );
}

void CadiBack::calculate_pre( Component & comp, Decision_Manager & manager )
{
	assert( (unsigned)(vars()) <= NumVars( manager.Max_Var() ) );  /// some variables might not really appear
	_max_var = (unsigned)(vars());
	_backbones = new Literal [_max_var + 1];
	_assumed = new bool [_max_var + 1];
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable x = comp.Vars( i );
		_backbones[x] = Literal::undef;
		_assumed[x] = false;
	}
	for ( unsigned i = 0; i < manager._num_dec_stack; i++ ) {
		_assumed[manager._dec_stack[i].Var()] = true;
	}
}

void CadiBack::add_model( Component & comp, vector<Model *> & models, Model_Pool * model_pool )
{
	Model * model = model_pool->Allocate();
	vector<unsigned>::const_iterator itr = comp.VarIDs_Begin(), end = comp.VarIDs_End();
	for ( ; itr < end; itr++ ) {
		model->Assign( Variable( *itr ), val(*itr) > 0 );
	}
    models.push_back( model );
}

void CadiBack::init_candidates( Component & comp, Decision_Manager & manager, vector<Model *> & models )
{
	assert( !models.empty() );
	for ( unsigned i = 0; i < manager._num_dec_stack; i++ ) {
		Variable var = manager._dec_stack[i].Var();
		_backbones[var] = manager._dec_stack[i];
	}
	Model & first_model = *(models[0]);
	if ( models.size() == 1 ) {
		for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
			Variable x = comp.Vars( i );
			if ( _backbones[x] != Literal::undef ) continue;
			_candidates.push_back( Literal( x, first_model[x] ) );
		}
	} else {
		for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
			Variable x = comp.Vars( i );
			if ( _backbones[x] != Literal::undef ) continue;
			unsigned m = 1;
			for ( ; m < models.size(); m++ ) {
				if ( (*models[m])[x] != first_model[x] ) break;
			}
			if ( m == models.size() ) {
				_candidates.push_back( Literal( x, first_model[x] ) );
			}
		}
	}
}

void CadiBack::try_to_flip_remaining( Component & comp, vector<Model *> & models, Model_Pool * model_pool )
{
	if (options.no_flip) return;
	for ( unsigned i = 0; i < _candidates.size(); ) {
		Literal lit = _candidates[i];
		int elit = ExtLit( lit );
		if (options.really_flip) {
			if ( !flip( elit ) ) {
				i++;
				continue;
			}
			statistics.flipped++;
		} else {
			if ( !flippable( elit ) ) {
				i++;
				continue;
			}
			statistics.flippable++;
		}
		drop_candidate( i );
		add_model( comp, models, model_pool );
		models.back()->Assign( ~lit );
	}
}

int CadiBack::calculate_one_by_one( Component & comp, Decision_Manager & manager, vector<Model *> & models, Model_Pool * model_pool )
{
	assume( -ExtLit( _candidates[0] ) );
	int rsl = solve( manager );
	if ( rsl == 10 ) {
		drop_candidate( 0 );
		filter_candidates();
		try_to_flip_remaining( models, model_pool );
	} else {
		assert (rsl == 20);
		backbone_variable( 0 ); // Singular! So only this one.
	}
	return rsl;
}

void CadiBack::calculate_post( Component & comp, Decision_Manager & manager )
{
	for ( unsigned i = 0; i < comp.Vars_Size(); i++ ) {
		Variable x = comp.Vars( i );
    	if ( _backbones[x] != Literal::undef && !_assumed[x] ) manager.Assign( _backbones[x] );
    }
	delete [] _backbones;
	delete [] _assumed;
}

bool CadiBack::imply( Big_Clause & clause )
{
	for ( unsigned i = 0; i < clause.Size(); i++ ) {
		int lit = ExtLit( clause[i] );
		assume( -lit );
	}
	return solve() == 20;
}


};
