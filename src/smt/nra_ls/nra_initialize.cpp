#include "nra_ls.h"
namespace nra {

//initialize
ls_solver::ls_solver()
    : _swt_p(0.3),
      _swt_threshold(50),
      smooth_probability(3),
      _cutoff(1200),
      _additional_len(10),
      _max_step(UINT64_MAX),
      random_walk_clauses(1),
      random_walk_idx(5),
      min_ration(1,128),
      BMS_cnt(45) {
    mt.seed(1);
}

ls_solver::ls_solver(int random_seed)
    : _swt_p(0.3),
      _swt_threshold(50),
      smooth_probability(3),
      _cutoff(1200),
      _additional_len(10),
      _max_step(UINT64_MAX),
      random_walk_clauses(1),
      random_walk_idx(5),
      min_ration(1, 128),
      BMS_cnt(45) {
    mt.seed(random_seed);
}

void ls_solver::initialize() {
    clear_prev_data();
    construct_slution_score();
    initialize_term_datas();
    initialize_lit_datas();
    initialize_clause_datas();
    initialize_variable_datas();
    best_found_this_restart = unsat_clauses->size();
    update_best_solution();
}

void ls_solver::clear_prev_data(){
    for (int v : bool_var_vec) {
        _vars[v].score = 0;
    }
    _best_found_hard_cost_this_bool = INT32_MAX;
    _best_found_hard_cost_this_nra = INT32_MAX;
    no_improve_cnt_bool = 0;
    no_improve_cnt_nra = 0;
}

// construction
void ls_solver::construct_slution_score() {
    // TODO: this is a temp function, setting all vars 0
    for (int i = 0; i < _num_vars; i++) {
        if (!_vars[i].is_nra) {
            _solution[i] = -1;
            continue;
        }
        if (_pre_value_1[i] != INT32_MAX) {
            _solution[i] = _pre_value_1[i];
        } // if the pre value is set, then set it
        else if (_vars[i].low_bound <= 0 && _vars[i].upper_bound >= 0) {
            _solution[i] = 0;
        } // if 0 is within the bound, then set it to 0
        else if (_vars[i].low_bound != -max_int && _vars[i].upper_bound != max_int) {
            _solution[i] = mid_ration(_vars[i].low_bound, _vars[i].upper_bound);
        } // no bound is extended to max_int
        else if (_vars[i].low_bound == -max_int) {
            _solution[i] = _vars[i].upper_bound;
        } // (-inf , up_bound] : choose up_bound
        else {
            _solution[i] = _vars[i].low_bound;
        } // [low_bound, inf) : choose low_bound
    }
//    read_model();
}

void ls_solver::read_model(){
    int size;
    std::cin >> size;
    std::string in_string, in_string_2;
    for (int i = 0; i < size; i++) {
        std::cin >> in_string;
        std::cin >> in_string_2;
        if (name2var.find(in_string) != name2var.end()) {
            if (in_string_2 == "false") {
                _solution[name2var[in_string]] = -1;
            }
            else if (in_string_2 == "true") {
                _solution[name2var[in_string]] = 1;
            }
            else {
                _solution[name2var[in_string]] = atoi(in_string_2.c_str());
            }
        }
    }
}

void ls_solver::initialize_variable_datas(){
    
}

// initialize the value of each term
void ls_solver::initialize_term_datas() {
    for (int term_idx = 0; term_idx < _terms.size(); term_idx++) {
        if (!term_appear[term_idx]) {
            continue;
        }
        term *t = &(_terms[term_idx]);
        t->value = 1;
        for (var_exp & ve : t->var_epxs) {
            if (ve.exponent == 1) {
                t->value *= _solution[ve.var_index];
            }
            else {
                t->value *= power(_solution[ve.var_index], ve.exponent);
            }
            if (t->value == 0) {
                break;
            }
        }
    }
}

// initialize the delta of each literal by delta_lit operation
void ls_solver::initialize_lit_datas(){
    for (lit & l : _lits) {
        if (l.lits_index != 0) {
            if (l.is_nra_lit) {
                l.delta = delta_lit(l);
                if (l.is_equal) {
                    l.is_true = (l.delta == 0) ? 1 : -1;
                }
                else {
                    l.is_true = (l.delta <= 0) ? 1 : -1;
                }
            } // nra lit
            else {
                l.is_true = (_solution[l.delta.get_int32()] > 0) ? 1 : -1;
            } // boolean lit
        }
    }
}

// set the sat num of each clause, and sat/unsat a clause
void ls_solver::initialize_clause_datas() {
    _lit_in_unsat_clause_num = 0;
    _bool_lit_in_unsat_clause_num = 0;
    for (uint64_t c = 0; c < _num_clauses; c++) {
        clause *cl = &(_clauses[c]);
        cl->sat_count = 0;
        cl->weight = 1;
        for (int l_idx : cl->literals) {
            if (l_idx * _lits[std::abs(l_idx)].is_true > 0) {
                cl->sat_count++;
                cl->watch_lit_idx = l_idx;
            } // determine the sat count and watch lit
        }
        if (cl->sat_count == 0) {
            unsat_a_clause(c);
            _lit_in_unsat_clause_num += _clauses[c].literals.size();
            _bool_lit_in_unsat_clause_num += _clauses[c].bool_literals.size();
            for (int l_sign_idx : cl->bool_literals) {
                _vars[_lits[std::abs(l_sign_idx)].delta.get_int32()].score++;
            }
        }
        else {
            sat_a_clause(c);
        }
        if (cl->sat_count > 0 && cl->sat_count < cl->literals.size()) {
            sat_clause_with_false_literal->insert_element((int) c);
        }
        // TODO: else{sat_clause_with_false_literal->delete_element((int)c);}
        if (cl->sat_count == 1) {
            lit *l = &(_lits[std::abs(cl->watch_lit_idx)]);
            if (!l->is_nra_lit) {
                _vars[l->delta.get_int32()].score--;
            }
        }
    }
    total_clause_weight = _num_clauses;
}
}
