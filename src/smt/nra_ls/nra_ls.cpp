#include "nra_ls.h"
#include <sstream>
#define NLS_DEBUG
#define NUSE_TWO_LEVEL
#define USE_BOUND
namespace nra {

// random walk
void ls_solver::update_clause_weight() {
    for (int i = 0; i < unsat_clauses->size(); i++) {
        clause *unsat_cl = &(_clauses[unsat_clauses->element_at(i)]);
        unsat_cl->weight++;
        for (int l_sign_idx : unsat_cl->bool_literals) {
            _vars[_lits[std::abs(l_sign_idx)].delta.get_int32()].score++;
        }
    }
    total_clause_weight += unsat_clauses->size();
}

void ls_solver::smooth_clause_weight(){
    for (int i = 0; i < _num_clauses; i++) {
        if (_clauses[i].weight > 1 && !unsat_clauses->is_in_array(i)) {
            _clauses[i].weight--;
            total_clause_weight--;
            if (_clauses[i].sat_count == 1 && !_lits[std::abs(_clauses[i].watch_lit_idx)].is_nra_lit) {
                __int128_t watch_lit_idx = _lits[std::abs(_clauses[i].watch_lit_idx)].delta.get_int32();
                _vars[watch_lit_idx].score++;
            }
        }
    }
}

// when there is no operation, simply find a lit in a random false clause,
// pick a random var with coff != 0, set it to 0
void ls_solver::no_operation_random_walk() {
#ifdef LS_DEBUG
    std::cout << "begin no operation random walk\n";
    std::cout.flush();
#endif
    clause *cp = &(_clauses[unsat_clauses->element_at(mt()%unsat_clauses->size())]); //choose a random unsat clause
    int lit_idx = cp->literals[mt()%cp->literals.size()];
    lit *l = &(_lits[std::abs(lit_idx)]);
    if (!l->is_nra_lit) {
        critical_move(l->delta.get_int32(), rational(0));
        return;
    } //boolean lit
    var_lit_term *vlt; //nra lit
    rational coffs[2] = {rational(0),rational(0)}; //the coff = sum(term_coff*vlt_coff) ( 1 * x1*x2 ) + ( -1 * x1 ) + ( -1 * x3 ) for x1 the coff=(1*x2)+(-1)
    uint64_t var_idx_curr = l->var_lit_terms[0].var_idx;//the current var idx of var_lit_term
    int l_var_lit_term_num = (int) l->var_lit_terms.size();
    std::vector<uint64_t> var_idx_none_zero;//the vars with coff != 0
    // go through the var_lit_term and insert critical move for each var
    for (int vlt_idx = 0; vlt_idx < l_var_lit_term_num; vlt_idx++) {
        vlt = &(l->var_lit_terms[vlt_idx]);
        if (vlt->var_idx != var_idx_curr) {
            coffs[0] = coffs[1] = 0;
            var_idx_curr = vlt->var_idx;
        } //enter a new var
        if (vlt->exponent < 3) {
            coffs[vlt->exponent-1] += vlt->coff * coff_in_term(var_idx_curr, vlt->term_idx, vlt->exponent);
        } // determine the coff, for vars with only coff > 2, the var will not be considered
        if ((vlt_idx == l_var_lit_term_num - 1) || (var_idx_curr != l->var_lit_terms[vlt_idx+1].var_idx)) {
            if (coffs[0] != 0 || coffs[1] != 0) {
                var_idx_none_zero.push_back(var_idx_curr);
            } // if coff == 0, changing the var cannot make any progress
        } // the last vlt of the var or the last vlt of the lit
    }
    if (var_idx_none_zero.size() == 0) {
        var_idx_curr = l->var_lit_terms[mt()%l_var_lit_term_num].var_idx;
    }
    else {
        var_idx_curr = var_idx_none_zero[mt()%var_idx_none_zero.size()];
    }
    rational future_solution(0);
    variable *var = &(_vars[var_idx_curr]);
    if (future_solution == _solution[var_idx_curr]) {
        if (!l->is_equal) {
            if ((coffs[0] > 0 && lit_idx > 0) || (coffs[0] < 0 && lit_idx < 0)) {
                future_solution = diff_floor(future_solution);
            }
            else {
                future_solution = diff_ceil(future_solution);
            }
        }
        else {
            if ((coffs[0] > 0 && l->delta > 0) || (coffs[0] < 0 && l->delta < 0)) {
                future_solution = diff_floor(future_solution);
            }
            else {
                future_solution = diff_ceil(future_solution);
            }
        }
    }
    if (var->low_bound > future_solution) {
        future_solution = var->low_bound;
    }
    else if (var->upper_bound < future_solution) {
        future_solution = var->upper_bound;
    }
    critical_move(var_idx_curr, future_solution-_solution[var_idx_curr]); // move a random var with coff != 0 to 0
}

void ls_solver::random_walk() {
#ifdef LS_DEBUG
    std::cout << "begin random walk\n";
    std::cout.flush();
#endif
    int operation_idx(0), operation_idx_bool(0), clause_idx;
    clause *cp;
    // determine the operations
    for (int i = 0; i < random_walk_clauses && operation_idx + operation_idx_bool < random_walk_idx; i++) {
        clause_idx = unsat_clauses->element_at(mt()%unsat_clauses->size());
        cp = &(_clauses[clause_idx]);
        for (int l_idx : cp->nra_literals) {
            add_operation_from_false_lit(false, l_idx, operation_idx);
        }
        for (int l_idx : cp->bool_literals) {
            add_bool_operation(false, l_idx, operation_idx_bool);
        }
    }
    // recover bool vec
    for (int i = 0; i < operation_idx_bool; i++) {
        is_chosen_bool_var[operation_var_idx_bool_vec[i]] = false;
    }
    // recover the false_lit
    false_lit_occur->clear();
    // if no operation, return
    if (operation_idx + operation_idx_bool == 0) {
        last_op_var = UINT64_MAX; // in case the random walk make no move, it will not ban the only operation
        no_operation_random_walk();
        return;
    }
    // nra mode make move
    if (operation_idx_bool == 0 || (operation_idx > 0 && operation_idx_bool > 0 && !is_in_bool_search)) {
        rational best_value_nra;
        int best_var_idx_nra, best_score_nra(INT32_MIN);
        select_best_operation_from_vec(operation_idx, best_score_nra, best_var_idx_nra, best_value_nra); //choose best nra operation
        critical_move(best_var_idx_nra, best_value_nra);
    }
    // bool mode make move
    else {
        // choose best bool operation
        int best_var_idx_bool(0), best_score_bool(INT32_MIN);
        select_best_operation_from_bool_vec(operation_idx_bool, best_score_bool, best_var_idx_bool);
        critical_move(best_var_idx_bool, rational(0));
    }
}

// basic operations
bool ls_solver::update_best_solution() {
    bool improve = false;
    if (unsat_clauses->size() < best_found_this_restart) {
        improve = true;
        best_found_this_restart = unsat_clauses->size();
    }
    if (unsat_clauses->size() < best_found_cost) {
        improve = true;
        best_found_cost = unsat_clauses->size();
        best_cost_time = TimeElapsed();
    }
    return improve;
}

int ls_solver::pick_critical_move_bool() {
    int best_var_idx(-1), best_score(1);
    int operation_idx = 0;
    for (int i = 0; i < contain_bool_unsat_clauses->size(); i++) {
        int clause_idx = contain_bool_unsat_clauses->element_at(i);
        clause *cl = &(_clauses[clause_idx]);
        for (int l_sign_idx : cl->bool_literals) {
            add_bool_operation(true, l_sign_idx, operation_idx);
        }
    }
    for (int i = 0; i < operation_idx; i++) {
        is_chosen_bool_var[operation_var_idx_bool_vec[i]] = false;
    } // recover chosen_bool_var
    select_best_operation_from_bool_vec(operation_idx, best_score, best_var_idx);
    // if there is untabu decreasing move
    if (best_var_idx != -1) {
        return best_var_idx;
    }
    // update weight
    if (mt() % 10000 > smooth_probability) {
        update_clause_weight();
    }
    else {
        smooth_clause_weight();
    }
    random_walk();
    return -1;
}

void ls_solver::add_bool_operation(bool use_tabu, int lit_idx, int & operation_idx_bool) {
    __int128_t bool_var_idx = _lits[std::abs(lit_idx)].delta.get_int32();
    if (is_chosen_bool_var[bool_var_idx]) {
        return; // operations will not be inserted repeatedly
    }
    if (!use_tabu || (use_tabu && _outer_layer_step > tabulist[2*bool_var_idx])) { // tabu mechanism
        operation_var_idx_bool_vec[operation_idx_bool++] = (int) bool_var_idx;
        is_chosen_bool_var[bool_var_idx] = true;
    }
}

void ls_solver::set_bounds(uint64_t var_idx_curr, bool use_tabu, int lit_idx, int & operation_idx,
                           const rational & coff_1){
    lit *l = &(_lits[std::abs(lit_idx)]);
    rational lit_delta = l->delta;
    if (l->is_equal) {
        if (lit_idx > 0) {
            insert_operation(var_idx_curr, (-lit_delta/coff_1), operation_idx, use_tabu);
        } // the delta should be 0, while it is now != 0, so the change value should be -delta/coff
        else {
            insert_operation(var_idx_curr, min_ration, operation_idx, use_tabu);
            insert_operation(var_idx_curr, -min_ration, operation_idx, use_tabu);
        } //the delta should be != 0, while it is now 0, so the change value should be +/- ration_min
    }
    else {
        rational change_value = (-lit_delta / coff_1);
        if (lit_idx < 0) {
            change_value += (coff_1 > 0) ? min_ration : (-min_ration);
        }
        rational future_value = _solution[var_idx_curr] + change_value;
        if (use_tabu) {
            vars_with_tight_bound->insert_element((int) var_idx_curr);
            if ((lit_idx > 0 && coff_1 < 0) || (lit_idx < 0 && coff_1 > 0)) {
                if (future_value > low_bound_tight[var_idx_curr]) {
                    low_bound_tight[var_idx_curr] = future_value;
                }
            }
            else if (future_value < up_bound_tight[var_idx_curr]) {
                up_bound_tight[var_idx_curr] = future_value;
            }
        } // eager mode->tight
        else {
            vars_with_slack_bound->insert_element((int) var_idx_curr);
            if ((lit_idx > 0 && coff_1 < 0) || (lit_idx < 0 && coff_1 > 0)) {
                if (future_value < low_bound_slack[var_idx_curr]) {
                    low_bound_slack[var_idx_curr] = future_value;
                }
            }
            else if (future_value > up_bound_slack[var_idx_curr]) {
                up_bound_slack[var_idx_curr] = future_value;
            }
        } // random mode->slack
    }
}

void ls_solver::insert_from_bounds(bool use_tabu, int &operation_idx) {
    rational future_value, change_value;
    for(int i = 0; i < vars_with_tight_bound->size(); i++) {
        uint64_t v_idx = vars_with_tight_bound->element_at(i);
        bool has_up_bound = (up_bound_tight[v_idx] != INT32_MAX);
        bool has_low_bound = (low_bound_tight[v_idx] != INT32_MIN);
        if (has_up_bound) {
            future_value = up_bound_tight[v_idx];
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_floor(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
        if (has_low_bound) {
            future_value = low_bound_tight[v_idx];
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_ceil(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
        if (has_up_bound && has_low_bound && low_bound_tight[v_idx] < up_bound_tight[v_idx]) {
            future_value = (low_bound_tight[v_idx]+up_bound_tight[v_idx]) / 2;
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_ceil(future_value)-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_floor(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
    }
    for (int i = 0; i < vars_with_slack_bound->size(); i++) {
        uint64_t v_idx = vars_with_slack_bound->element_at(i);
        bool has_up_bound = (up_bound_slack[v_idx] != INT32_MIN);
        bool has_low_bound = (low_bound_slack[v_idx] != INT32_MAX);
        if (has_up_bound) {
            future_value = up_bound_slack[v_idx];
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_floor(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
        if (has_low_bound) {
            future_value = low_bound_slack[v_idx];
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_ceil(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
        if (has_up_bound && has_low_bound && low_bound_slack[v_idx] < up_bound_slack[v_idx]) {
            future_value = (low_bound_slack[v_idx]+up_bound_slack[v_idx]) / 2;
            insert_operation(v_idx, future_value-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_ceil(future_value)-_solution[v_idx], operation_idx, use_tabu);
            insert_operation(v_idx, diff_floor(future_value)-_solution[v_idx], operation_idx, use_tabu);
        }
    }
    reset_bounds(); //after insertion, reset the bounds
}

void ls_solver::reset_bounds() {
    for (int i = 0; i < vars_with_tight_bound->size(); i++) {
        uint64_t v_idx = vars_with_tight_bound->element_at(i);
        up_bound_tight[v_idx] = rational(INT32_MAX);
        low_bound_tight[v_idx] = rational(INT32_MIN);
    }
    vars_with_tight_bound->clear();
    for(int i = 0; i < vars_with_slack_bound->size(); i++) {
        uint64_t v_idx = vars_with_slack_bound->element_at(i);
        up_bound_slack[v_idx] = rational(INT32_MIN);
        low_bound_slack[v_idx] = rational(INT32_MAX);
    }
    vars_with_slack_bound->clear();
}

// calculate the operation to be added for exp == 1
void ls_solver::add_coff(uint64_t var_idx_curr, bool use_tabu, int lit_idx, int &operation_idx,const rational &  coff_1){
    lit *l = &(_lits[std::abs(lit_idx)]);
    rational lit_delta = l->delta;
    if (l->is_equal) {
        if (lit_idx > 0) {
            insert_operation(var_idx_curr, (-lit_delta/coff_1), operation_idx,use_tabu);
        } // the delta should be 0, while it is now != 0, so the change value should be -delta/coff
        else {
            insert_operation(var_idx_curr, min_ration, operation_idx, use_tabu);
            insert_operation(var_idx_curr, -min_ration, operation_idx, use_tabu);
            // insert_operation(var_idx_curr,diff_ceil(_solution[var_idx_curr])-_solution[var_idx_curr],operation_idx,use_tabu);
            // insert_operation(var_idx_curr,diff_floor(_solution[var_idx_curr])-_solution[var_idx_curr],operation_idx,use_tabu);
        } //the delta should be !=0, while it is now 0, so the change value should be +/- ration_min
    }
    else {
        rational change_value = (-lit_delta / coff_1);
        if (lit_idx < 0) {
            change_value += (coff_1 > 0) ? min_ration : (-min_ration);
        }
        insert_operation(var_idx_curr, change_value, operation_idx, use_tabu);
        rational futre_value = _solution[var_idx_curr] + change_value;
        if ((lit_idx > 0 && coff_1 < 0) || (lit_idx < 0 && coff_1 > 0)) {
            futre_value = diff_ceil(futre_value);
        }
        else {
            futre_value = diff_floor(futre_value);
        }
        change_value = futre_value - _solution[var_idx_curr];
        insert_operation(var_idx_curr, change_value, operation_idx, use_tabu); // modify the var to closest integer satisfying the literal
    }
}

// calculate the operation to be added for exp==2: a*x^2+b*x+c
void ls_solver::add_coff(uint64_t var_idx_curr, bool use_tabu, int lit_idx, int & operation_idx,
                         const rational & a, const rational & b, const rational & c) {
    lit *l = &(_lits[std::abs(lit_idx)]);
    if (l->is_equal) {
        if (lit_idx > 0) {} // the delta should be 0, while it is now != 0
        else {}             // the delta should be != 0, while it is now 0
    }
    else{
        if (lit_idx > 0) {}
        else {}
    }
} // a*x^2+b*x+c

//for a falsified nra lit, choose critical move from it
void ls_solver::add_operation_from_false_lit(bool use_tabu, int lit_idx, int & operation_idx){
    if (false_lit_occur->is_in_array(std::abs(lit_idx))) {
        return;
    } // if the false lit has been considered, then the lit will not be considered repeatedly
    false_lit_occur->insert_element(std::abs(lit_idx));
    rational total_term_value(0); // the value of terms containing the var
    lit *l = &(_lits[std::abs(lit_idx)]);
    if (l->var_lit_terms.size() == 0) {
        return;
    }
    uint64_t var_idx_curr = l->var_lit_terms[0].var_idx; // the current var idx of var_lit_term
    var_lit_term *vlt;
    int l_var_lit_term_num = (int) l->var_lit_terms.size();
    bool too_high_exp = false; // if the exponent of var is larger than 2, then the var should not be modified
    rational coffs[2] = {rational(0), rational(0)}; // the coff = sum(term_coff*vlt_coff) ( 1 * x1*x2 ) + ( -1 * x1 ) + ( -1 * x3 ) for x1 the coff=(1*x2)+(-1)
    // go through the var_lit_term and insert critical move for each var
    for (int vlt_idx = 0; vlt_idx < l_var_lit_term_num; vlt_idx++) {
        vlt = &(l->var_lit_terms[vlt_idx]);
        if (vlt->var_idx != var_idx_curr) {
            total_term_value = 0;
            coffs[0] = coffs[1] = 0;//reset coffs
            var_idx_curr = vlt->var_idx;
            too_high_exp = false;
        } // enter a new var
        if (vlt->exponent > 2) {
            too_high_exp = true;
        }
        if (too_high_exp) {
            continue;
        } // if too high exponent, the operations will not be inserted
        coffs[vlt->exponent-1] += (vlt->coff * coff_in_term(var_idx_curr, vlt->term_idx, vlt->exponent)); //determine the coff
        total_term_value += vlt->coff * _terms[vlt->term_idx].value;
        if ((vlt_idx == l_var_lit_term_num - 1) || (var_idx_curr != l->var_lit_terms[vlt_idx+1].var_idx)) {
            if (coffs[0] == 0 && coffs[1] == 0) {
                insert_operation(var_idx_curr, diff_ceil(_solution[var_idx_curr])-_solution[var_idx_curr], operation_idx, use_tabu);
                insert_operation(var_idx_curr, diff_floor(_solution[var_idx_curr])-_solution[var_idx_curr], operation_idx, use_tabu);
                continue;
            } // if coff == 0, change the var to the closest integer
#ifdef USE_BOUND
            set_bounds(var_idx_curr, use_tabu, lit_idx, operation_idx, coffs[0]);
#else   
            else if (coffs[1] == 0) {
                add_coff(var_idx_curr, use_tabu, lit_idx, operation_idx, coffs[0]);
            } // high coff is 1
            else {
                add_coff(var_idx_curr, use_tabu, lit_idx, operation_idx, coffs[1], coffs[0], l->delta-total_term_value);
            } // high coff is 2
#endif
        } // the last vlt of the var or the last vlt of the lit
    }
#ifdef USE_BOUND
    insert_from_bounds(use_tabu,operation_idx);
#endif
}

// select best bool operation from
void ls_solver::select_best_operation_from_bool_vec(int operation_idx_bool, int & best_score_bool, int & best_var_idx_bool) {
    int cnt, score, var_idx;
    uint64_t best_last_move(UINT64_MAX);
    bool BMS;
    if (operation_idx_bool > BMS_cnt) {
        BMS = true;
        cnt = BMS_cnt;
    }
    else {
        BMS = false;
        cnt = operation_idx_bool;
    }
    for (int i = 0; i < cnt; i++) {
        if (BMS){
            int idx = mt() % (operation_idx_bool - i);
            int tmp = operation_var_idx_bool_vec[operation_idx_bool-i-1];
            var_idx = operation_var_idx_bool_vec[idx];
            operation_var_idx_bool_vec[idx] = tmp;
        }
        else {
            var_idx = operation_var_idx_bool_vec[i];
        }
        score = _vars[var_idx].score;
        uint64_t last_move_step = last_move[2*var_idx];
        if (score > best_score_bool || (score == best_score_bool && last_move_step < best_last_move)) {
            best_score_bool = score;
            best_var_idx_bool = var_idx;
            best_last_move = last_move_step;
        }
    }
}

// select the best nra operation from operation_vec depending on score
void ls_solver::select_best_operation_from_vec(int operation_idx, int & best_score, int & best_var_idx, rational & best_value) {
    bool BMS;
    int cnt, score;
    uint64_t operation_var_idx, best_last_move(UINT64_MAX);
    rational operation_change_value, best_future_abs_value(INT32_MAX), future_abs_value;
    if (operation_idx > BMS_cnt) {
        BMS = true;
        cnt = BMS_cnt;
    }
    else {
        BMS = false;
        cnt = operation_idx;
    }
    for (int i = 0; i < cnt; i++) {
        if (BMS) {
            int idx = mt() % (operation_idx - i);
            operation_change_value = operation_change_value_vec[idx];
            operation_var_idx = operation_var_idx_vec[idx];
            operation_change_value_vec[idx] = operation_change_value_vec[operation_idx-i-1];
            operation_var_idx_vec[idx] = operation_var_idx_vec[operation_idx-i-1];
        }
        else {
            operation_change_value = operation_change_value_vec[i];
            operation_var_idx = operation_var_idx_vec[i];
        }
        future_abs_value = abs(_solution[operation_var_idx] + operation_change_value);
        score = critical_score(operation_var_idx, operation_change_value);
        // if the change value is > 0, then means it is moving forward, the opposite direction is 1 (backward)
        int opposite_direction = (operation_change_value > 0) ? 1 : 0;
        uint64_t last_move_step = last_move[2*operation_var_idx+opposite_direction];
        if ((score > best_score) ||
            (score == best_score && denominator(future_abs_value) < denominator(best_future_abs_value)) ||
            (score == best_score && denominator(future_abs_value) == denominator(best_future_abs_value) && future_abs_value < best_future_abs_value) ||
            (score == best_score && denominator(future_abs_value) == denominator(best_future_abs_value) && future_abs_value == best_future_abs_value && last_move_step < best_last_move)) {
            best_score = score;
            best_var_idx = (int) operation_var_idx;
            best_value = operation_change_value;
            best_last_move = last_move_step;
            best_future_abs_value = future_abs_value;
        } // priority: score > rational.m > future_num > last_move
    }
}

//pick a nra critical move
int ls_solver::pick_critical_move(rational &best_value){
#ifdef LS_DEBUG
    std::cout << "begin pick critical move\n";
    std::cout.flush();
#endif
    int best_score(1), best_var_idx(-1), operation_idx(0);
    // determine the critical value from unsat sat, using tabu
    for (int i = 0; i < unsat_clauses->size(); i++) {
        clause *cl = &(_clauses[unsat_clauses->element_at(i)]);
        for (int l_idx : cl->nra_literals) {
            add_operation_from_false_lit(true, l_idx, operation_idx);
        }
    }
    // recover the false_lit
    false_lit_occur->clear();
    // go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    select_best_operation_from_vec(operation_idx, best_score, best_var_idx, best_value);
    // if there is untabu decreasing move
#ifdef LS_DEBUG
    std::cout << "best var idx: " << best_var_idx << "\n";
    std::cout.flush();
#endif
    if (best_var_idx != -1) {
        return best_var_idx;
    }
    // choose from swap operations if there is no decreasing unsat critical
#ifdef USE_TWO_LEVEL
    if (!sat_clause_with_false_literal->empty()) {
        operation_idx = 0;
        add_swap_operation(operation_idx);
        // recover the false_lit
        false_lit_occur->clear();
        select_best_operation_from_vec(operation_idx, best_score, best_var_idx, best_value);
#ifdef LS_DEBUG
    std::cout << "best swap move varidx: " << best_var_idx << "\n";
    std::cout.flush();
#endif
        if (best_var_idx != -1) {
            return best_var_idx;
        }
    }
#endif
    // update weight and random walk
    if (mt() % 10000 > smooth_probability) {
        update_clause_weight();
    }
    else {
        smooth_clause_weight();
    }
    random_walk();
    return -1;
}

// make move
void ls_solver::critical_move(uint64_t var_idx, const rational & change_value) {
#ifdef LS_DEBUG
    std::cout << "critical move: " << var_idx << " value: " << change_value << "\n";
#endif
    int direction = (change_value > 0) ? 0 : 1;
    if (_vars[var_idx].is_nra) {
        last_op_value = change_value;
        last_op_var = var_idx;
        move_update(var_idx, change_value);
        _solution[var_idx] += change_value;
    }
    else {
        last_op_var = UINT64_MAX;  // if last operation is boolean operation, the var should no longer be banned
        int origin_score = _vars[var_idx].score;
        move_update(var_idx);
        _solution[var_idx] *= -1;
        _vars[var_idx].score = -origin_score;
    }
    // step
    if (_vars[var_idx].is_nra) {
        last_move[2*var_idx+direction] = _step;
        tabulist[var_idx*2+(direction+1)%2] = _step + 3 + mt() % 10;
    }
    else{
        last_move[2*var_idx] = _outer_layer_step;
        tabulist[2*var_idx] = _outer_layer_step + 1 + mt() % 3;
        _outer_layer_step++;
    }
}

//all coffs are positive, go through all terms of the literal
rational ls_solver::delta_lit(lit &l) {
    rational delta = l.key;
    for (int i = 0; i < l.coff_terms.size(); i++) {
        delta += (l.coff_terms[i].coff * _terms[l.coff_terms[i].term_idx].value);
    }
    return delta;
}

rational ls_solver::coff_in_term(uint64_t var_idx, uint64_t term_idx, int exponent) {
    if (_terms[term_idx].var_epxs.size() == 1) {
        return rational(1);
    } // the term only contains the var
    if (_solution[var_idx] != 0) {
        if (exponent == 1) {
            return _terms[term_idx].value / _solution[var_idx];
        }
        else {
            return _terms[term_idx].value / power(_solution[var_idx], exponent);
        }
    } // if the var != 0, the coff is value/var_solution
    else {
        rational coff(1);
        for (var_exp & ve : _terms[term_idx].var_epxs) {
            if (ve.var_index == var_idx) {
                continue;
            } // the var itself will not be counted
            if (ve.exponent == 1) {
                coff *= _solution[ve.var_index];
            }
            else {
                coff *= power(_solution[ve.var_index], ve.exponent);
            }
            if (coff == 0) {
                break;
            }
        }
        return coff;
    } // the var_solution == 0, then the coff should be calculated by going through the ve of the term
}

double ls_solver::TimeElapsed(){
    std::chrono::steady_clock::time_point finish = std::chrono::steady_clock::now();
    std::chrono::duration<double> duration = finish - start;
    return duration.count();
}

// return the upper round of (a/b): (-3.5)->-4; (3.5)->4
__int128_t ls_solver::devide(__int128_t a, __int128_t b){
    __int128_t abs_a = abs_128(a);
    __int128_t abs_b = abs_128(b);
    __int128_t up_round = abs_a / abs_b;
    if (abs_a % abs_b > 0) {
        up_round++;
    }
    return (a ^ b) >= 0 ? up_round : -up_round;
}

void ls_solver::insert_operation(uint64_t var_idx,const rational &  change_value,int &operation_idx,bool use_tabu){
    if (var_in_long_term->is_in_array((int) var_idx)) {
        for (term_exp & te : _vars[var_idx].term_exps) {
            term & t = _terms[te.term_idx];
            if (t.var_epxs.size() > 2 || t.var_epxs[0].exponent > 1) {
                rational future_term_value;
                if (te.exponent == 1) {
                    future_term_value = t.value + coff_in_term(var_idx, te.term_idx, te.exponent) * change_value;
                }
                else {
                    future_term_value = coff_in_term(var_idx, te.term_idx, te.exponent) * power((_solution[var_idx] + change_value), te.exponent);
                }
                if (future_term_value > max_int || future_term_value < -max_int) {
                    return;
                }
            }
        }
    }
    if (has_only_pre_value[var_idx]) {
        return;
    } // if the var is fixed, then it should not be modified
    if (var_idx == last_op_var && change_value == -last_op_value) {
        return;
    } // if op returns to previous assignment, it is banned
    uint64_t direction = (change_value > 0) ? 0 : 1;
    if (use_tabu && _step < tabulist[2*var_idx+direction]) {
        return;
    } // the operation is now tabued
    rational future_solution = _solution[var_idx] + change_value;
    if (denominator(future_solution) > max_int || future_solution > max_int || future_solution < -max_int) {
        return;
    }
    bool no_pre_value = (
        _pre_value_1[var_idx] == INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
        future_solution >= _vars[var_idx].low_bound && future_solution <= _vars[var_idx].upper_bound);
    bool has_pre_value_1 = (
        _pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
        future_solution == _pre_value_1[var_idx]);
    bool has_pre_value_2 = (
        _pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] != INT32_MAX &&
        (future_solution == _pre_value_1[var_idx] || future_solution == _pre_value_2[var_idx]));
    if (no_pre_value || has_pre_value_1 || has_pre_value_2) {
//    if(future_solution>=_vars[var_idx].low_bound&&future_solution<=_vars[var_idx].upper_bound){
        operation_var_idx_vec[operation_idx] = var_idx;
        operation_change_value_vec[operation_idx++] = change_value;
    }
}

void ls_solver::add_swap_operation(int &operation_idx){
#ifdef USE_TWO_LEVEL
    int clause_idx;
    clause *cl;
    if (sat_clause_with_false_literal->size() < 20) {
        for (int i = 0; i < sat_clause_with_false_literal->size(); i++) {
            clause_idx = sat_clause_with_false_literal->element_at(i);
            cl = &(_clauses[clause_idx]);
            for (int l_idx : cl->nra_literals) {
                if ((_lits[std::abs(l_idx)].is_true ^ l_idx) < 0) {
                    add_operation_from_false_lit(true, l_idx, operation_idx);
                } // determine a false lit, and add operation from it
            }
        }
    }
    else {
        for (int i = 0; operation_idx < 20 && i < 50; i++) {
            clause_idx = sat_clause_with_false_literal->element_at(mt()%sat_clause_with_false_literal->size());
            cl = &(_clauses[clause_idx]);
            for (int l_idx : cl->nra_literals) {
                if ((_lits[std::abs(l_idx)].is_true ^ l_idx) < 0) {
                    add_operation_from_false_lit(true, l_idx, operation_idx);
                } // determine a false lit, and add operation from it
            }
        }
    }
#endif
}

// choose a clause with small weight, then choose a random lit, select the operation
// with greatest score in the lit
void ls_solver::swap_from_small_weight_clause(){}


// calculate score for nra vars
int ls_solver::critical_score(uint64_t var_idx, const rational & change_value){
    int critical_score = 0;
    rational future_value = _solution[var_idx] + change_value;
    variable * var = &(_vars[var_idx]);
    var_lit_term *vlt;
    uint64_t curr_lit_idx = var->var_lit_terms[0].lit_idx;
    rational curr_lit_delta_new = _lits[curr_lit_idx].delta;
    rational coff; // (coff of original term) * (term_value / _solution[var]) ( 2 * x1*x2 ) x1=3, x2=4  -> coff[x2]=2*3
    for (term_exp & te : var->term_exps) {
        term_coffs[te.term_idx] = coff_in_term(var_idx, te.term_idx, te.exponent);
    } // determine the term coff
    // determine the lit_make_break by going through the vlt of var
    for (int vlt_idx = 0; vlt_idx < var->var_lit_terms.size(); vlt_idx++) {
        vlt = &(var->var_lit_terms[vlt_idx]);
        if (curr_lit_idx != vlt->lit_idx) {
            curr_lit_idx = vlt->lit_idx;
            curr_lit_delta_new = _lits[curr_lit_idx].delta;
        } //enter a new lit
        coff = vlt->coff * term_coffs[vlt->term_idx];
        if (vlt->exponent == 1) {
            curr_lit_delta_new += coff * change_value;
        }
        else {
            curr_lit_delta_new += coff * (power(future_value, vlt->exponent) - power(_solution[var_idx], vlt->exponent));
        }
        if ((vlt_idx == var->var_lit_terms.size() - 1) || (curr_lit_idx != var->var_lit_terms[vlt_idx+1].lit_idx)) {
            if (_lits[curr_lit_idx].is_equal) {
                if (_lits[curr_lit_idx].delta == 0 && curr_lit_delta_new != 0) {
                    _lit_make_break[curr_lit_idx] = -1;
                }
                else if (_lits[curr_lit_idx].delta != 0 && curr_lit_delta_new == 0) {
                    _lit_make_break[curr_lit_idx] = 1;
                }
            } // equal lit
            else {
                if (_lits[curr_lit_idx].delta <= 0 && curr_lit_delta_new > 0) {
                    _lit_make_break[curr_lit_idx] = -1;
                }
                else if (_lits[curr_lit_idx].delta > 0 && curr_lit_delta_new <= 0) {
                    _lit_make_break[curr_lit_idx] = 1;
                }
            } // nra <= lit
        } // the last vlt of the var or the last vlt of current lit
    }
    // determine the score by going through the clauses of var
    clause *c;
    for (int cls_idx : var->clause_idxs) {
        c = &(_clauses[cls_idx]);
        int clause_sat_count_new = c->sat_count;
        for (int v_lit : c->literals) {
            clause_sat_count_new += (v_lit > 0) ? _lit_make_break[v_lit] : (-_lit_make_break[-v_lit]);
        }
        if (c->sat_count > 0 && clause_sat_count_new == 0) {
            critical_score -= c->weight;
        }
        else if (c->sat_count == 0 && clause_sat_count_new > 0) {
            critical_score += c->weight;
        }
    }
    // recover the lit_make_break
    for (uint64_t l_idx : var->literal_idxs) {
        _lit_make_break[l_idx] = 0;
    }
    return critical_score;
}

// sat or unsat a clause, update the delta, dedicated for nra var
void ls_solver::move_update(uint64_t var_idx, const rational & change_value){
    variable *var = &(_vars[var_idx]);
    var_lit_term *vlt;
    uint64_t curr_lit_idx = var->var_lit_terms[0].lit_idx;
    rational curr_lit_delta_new = _lits[curr_lit_idx].delta;
    rational term_coff, lit_coff;
    rational future_value = _solution[var_idx]+change_value;
    // update term value
    for (term_exp & te : var->term_exps){
        term_coff = coff_in_term(var_idx, te.term_idx, te.exponent);
        term_coffs[te.term_idx] = term_coff;
        if (te.exponent == 1) {
            _terms[te.term_idx].value += term_coff * change_value;
        }
        else {
            _terms[te.term_idx].value = term_coff * power(future_value, te.exponent);
        }
    }
    // determine the lit_is_true by going through the vlt of var, and update the delta of lits
    for (int vlt_idx = 0; vlt_idx < var->var_lit_terms.size(); vlt_idx++) {
        vlt = &(var->var_lit_terms[vlt_idx]);
        if (curr_lit_idx != vlt->lit_idx) {
            curr_lit_idx = vlt->lit_idx;
            curr_lit_delta_new = _lits[curr_lit_idx].delta;
        } // enter a new lit
        lit_coff = term_coffs[vlt->term_idx] * vlt->coff;
        if (vlt->exponent == 1) {
            curr_lit_delta_new += lit_coff * change_value;
        }
        else {
            curr_lit_delta_new += lit_coff * (power(future_value, vlt->exponent) - power(_solution[var_idx], vlt->exponent));
        }
        if ((vlt_idx == var->var_lit_terms.size() - 1) || (curr_lit_idx != var->var_lit_terms[vlt_idx+1].lit_idx)) {
            if (_lits[curr_lit_idx].is_equal) {
                if (_lits[curr_lit_idx].delta == 0 && curr_lit_delta_new != 0) {
                    _lits[curr_lit_idx].is_true = -1;
                }
                else if (_lits[curr_lit_idx].delta != 0 && curr_lit_delta_new == 0) {
                    _lits[curr_lit_idx].is_true = 1;
                }
            } // equal lit
            else {
                if (_lits[curr_lit_idx].delta <= 0 && curr_lit_delta_new > 0) {
                    _lits[curr_lit_idx].is_true = -1;
                }
                else if (_lits[curr_lit_idx].delta > 0 && curr_lit_delta_new <= 0) {
                    _lits[curr_lit_idx].is_true = 1;
                }
            } // nra <= lit
            _lits[curr_lit_idx].delta = curr_lit_delta_new; //update lit delta
        } // the last vlt of the var or the last vlt of current lit
    }
    // unsat/sat a clause by going through the lits in it
    clause *c;
    lit *l;
    for (int cls_idx : var->clause_idxs) {
        c = &(_clauses[cls_idx]);
        int clause_sat_count_old = c->sat_count;
        int watch_lit_idx_old = c->watch_lit_idx;
        c->sat_count = 0; //reset the sat count
        for(int l_idx : c->literals) {
            if ((l_idx ^ _lits[std::abs(l_idx)].is_true) >= 0) {
                c->sat_count++;
                c->watch_lit_idx = l_idx;
            }
        }
        // sat or unsat a clause, update the lit_in_unsat_clause
        if (c->sat_count > 0 && clause_sat_count_old == 0) {
            sat_a_clause(cls_idx);
            _lit_in_unsat_clause_num -= c->literals.size();
            _bool_lit_in_unsat_clause_num -= c->bool_literals.size();
        }
        else if (c->sat_count == 0 && clause_sat_count_old > 0) {
            unsat_a_clause(cls_idx);
            _lit_in_unsat_clause_num += c->literals.size();
            _bool_lit_in_unsat_clause_num += c->bool_literals.size();
        }
#ifdef USE_TWO_LEVEL
        //update the sat_clause_with_false_lit
        if (c->sat_count > 0 && c->sat_count < c->literals.size()) {
            sat_clause_with_false_literal->insert_element((int)cls_idx);
        }
        else {
            sat_clause_with_false_literal->delete_element((int)cls_idx);
        }
#endif
        // update the score of boolean vars
        if (clause_sat_count_old == 0 && c->sat_count > 0) {
            for (int l_sign_idx : c->bool_literals) {
                l = &(_lits[std::abs(l_sign_idx)]);
                _vars[l->delta.get_int32()].score -= c->weight;
            }
        }
        else if (clause_sat_count_old == 1 && c->sat_count > 1) {
            l = &(_lits[std::abs(watch_lit_idx_old)]);
            if (!l->is_nra_lit) {
                _vars[l->delta.get_int32()].score += c->weight;
            }
        }
        else if (clause_sat_count_old > 0 && c->sat_count == 0) {
            for (int l_sign_idx : c->bool_literals) {
                l = &(_lits[std::abs(l_sign_idx)]);
                _vars[l->delta.get_int32()].score += c->weight;
            }
        }
        else if (clause_sat_count_old > 1 && c->sat_count == 1) {
            l = &(_lits[std::abs(c->watch_lit_idx)]);
            if (!l->is_nra_lit) {
                _vars[l->delta.get_int32()].score -= c->weight;
            }
        }
    }
}

// dedicated for boolean var
void ls_solver::move_update(uint64_t var_idx) {
    variable *var = &(_vars[var_idx]);
    int v_lit_idx = (int) var->literal_idxs[0]; // the lit_idx containing the var
    _lits[v_lit_idx].is_true *= -1;
    int make_break_in_clause = 0;
    int cl_sign_idx;
    for (int i = 0; i < var->clause_idxs.size(); i++) {
        cl_sign_idx = var->clause_idxs[i];
        if ((_solution[var_idx] > 0 && var->bool_var_in_pos_clause[i]) ||
            (_solution[var_idx] < 0 && !var->bool_var_in_pos_clause[i])) {
            make_break_in_clause = -1;
        }   //true to false
        else {
            make_break_in_clause = 1;
        }   //false to true
        int clause_idx = std::abs(cl_sign_idx);
        clause *cp = &(_clauses[clause_idx]);
        // sat or unsat a clause
        if (cp->sat_count > 0 && cp->sat_count + make_break_in_clause == 0) {
            unsat_a_clause(clause_idx);
            _lit_in_unsat_clause_num += cp->literals.size();
            _bool_lit_in_unsat_clause_num += cp->bool_literals.size();
        }
        else if (cp->sat_count == 0 && cp->sat_count + make_break_in_clause > 0) {
            sat_a_clause(clause_idx);
            _lit_in_unsat_clause_num -= cp->literals.size();
            _bool_lit_in_unsat_clause_num -= cp->bool_literals.size();
        }
        int origin_watch_lit = cp->watch_lit_idx;
        int origin_sat_count = cp->sat_count;
        cp->sat_count += make_break_in_clause;
#ifdef USE_TWO_LEVEL
        // update sat_clause_with_false_lit
        if (cp->sat_count > 0 && cp->sat_count < cp->literals.size()) {
            sat_clause_with_false_literal->insert_element(clause_idx);
        }
        else {
            sat_clause_with_false_literal->delete_element(clause_idx);
        }
#endif
        // update the watch lit
        if (std::abs(origin_watch_lit) == v_lit_idx && cp->sat_count > 0){
            // if the original watch lit exactly contains the var and the sat_count > 0, set the new watch lit
            for (int l_idx : cp->literals) {
                if ((l_idx ^ _lits[std::abs(l_idx)].is_true) >= 0) {
                    cp->watch_lit_idx = l_idx;
                    break;
                }
            }
        }
        else if (origin_sat_count == 0) {
            cp->watch_lit_idx = (cl_sign_idx > 0) ? (v_lit_idx) : (-v_lit_idx);
        } //if origin sat count==0, then set new watch lit
        // update the score of boolean vars
        if (make_break_in_clause > 0) {
            if (origin_sat_count == 0) {
                for (int bl : cp->bool_literals) {
                    lit *l = &(_lits[std::abs(bl)]);
                    _vars[l->delta.get_int32()].score -= cp->weight;
                }
            }
            else if (origin_sat_count == 1) {
                lit *l = &(_lits[std::abs(origin_watch_lit)]);
                if (!l->is_nra_lit) {
                    _vars[l->delta.get_int32()].score += cp->weight;
                }
            }
        }
        else if (make_break_in_clause < 0) {
            if (cp->sat_count == 0) {
                for (int bl : cp->bool_literals) {
                    lit *l = &(_lits[std::abs(bl)]);
                    _vars[l->delta.get_int32()].score += cp->weight;
                }
            }
            else if (cp->sat_count == 1) {
                lit *l = &(_lits[std::abs(cp->watch_lit_idx)]);
                if (!l->is_nra_lit) {
                    _vars[l->delta.get_int32()].score -= cp->weight;
                }
            }
        }
    }
}

// check
bool ls_solver::check_after_init(){
    lit *l;
    for(clause & cl:_clauses){
        int false_lit_num=0;
        for(int l_idx:cl.literals){
            l=&(_lits[std::abs(l_idx)]);
            if(l->is_nra_lit&&l->coff_terms.size()==0&&(l->is_true^l_idx)<0){ false_lit_num++; }//the lit is a nra lit AND it has no var in it AND it is false
            else{ break; }
        }
        if(false_lit_num==cl.literals.size()){return false;}//all lits in the clause is nra and false: then the clause cannot be satisfied
    }
    return true;
}//dedicate for lits with no vars: true -> no clause with all false lits


bool ls_solver::check_solution(){
    clause *cp;
    int unsat_num = 0;

    // Check the value of each term agrees with the saved value.
    for (int term_idx = 0; term_idx < _terms.size(); term_idx++) {
        if (!term_appear[term_idx]) {
            continue;
        }
        term *t = &(_terms[term_idx]);
        rational new_term_value(1);
        for (var_exp & ve : t->var_epxs) {
            if (ve.exponent == 1) {
                new_term_value *= _solution[ve.var_index];
            }
            else {
                new_term_value *= power(_solution[ve.var_index], ve.exponent);
            }
            if (new_term_value == 0) {
                break;
            }
        }
        if (new_term_value != _terms[term_idx].value) {
            std::cout << "term value wrong: " << term_idx << "\n";
        }
    }

    // Check the value of polynomial in each literal agrees with the saved value.
    for (int lit_idx = 0; lit_idx < _lits.size(); lit_idx++) {
        if (_lits[lit_idx].lits_index == 0 || !_lits[lit_idx].is_nra_lit) {
            continue;
        }
        rational delta = delta_lit(_lits[lit_idx]);
        if (delta != _lits[lit_idx].delta) {
            std::cout << "delta: " << delta << " lit_delta: " << _lits[lit_idx].delta << "\n";
            std::cout << "lit delta wrong: " << lit_idx << "\n";
        }
    }

    // Check the number of satisfied literals in each clause agrees with the saved value.
    for (uint64_t i = 0; i < _num_clauses; i++) {
        int sat_count = 0;
        cp = &(_clauses[i]);
        for (int lit_idx : cp->literals) {
            rational delta = _lits[std::abs(lit_idx)].delta;
            bool is_equal = _lits[std::abs(lit_idx)].is_equal;
            if (!_lits[std::abs(lit_idx)].is_nra_lit) {
                __int128_t var_idx = _lits[std::abs(lit_idx)].delta.get_int32();
                if ((_solution[var_idx] > 0 && lit_idx > 0) || (_solution[var_idx] < 0 && lit_idx < 0)){
                    sat_count++;
                }
            }
            else if ((!is_equal && ((delta <= 0 && lit_idx > 0) || (delta > 0 && lit_idx < 0))) ||
                     (is_equal && ((delta == 0 && lit_idx > 0) || (delta != 0 && lit_idx < 0)))) {
                sat_count++;
            }
        }
        if (sat_count != cp->sat_count) {
            std::cout << "sat count wrong at clause " << i << "\n";
        }
        if (sat_count == 0) {
            unsat_num++;
        }
    }

    // Check the assignment of each variable is within range.
    for (int var_idx = 0; var_idx < _vars.size(); var_idx++) {
        if (!has_only_pre_value[var_idx] && (_solution[var_idx] > _vars[var_idx].upper_bound ||
                _solution[var_idx] < _vars[var_idx].low_bound)) {
            std::cout << "var " << var_idx << " out of range\n";
        }
    }

    // Finally, check the number of unsatisfied clauses agrees.
    if (unsat_num == unsat_clauses->size()) {
        std::cout << "right solution\n";
    } else {
        std::cout << "wrong solution\n";
    }
    return unsat_num == unsat_clauses->size();
}

bool ls_solver::update_inner_best_solution() {
    if (unsat_clauses->size() < _best_found_hard_cost_this_nra) {
        _best_found_hard_cost_this_nra = unsat_clauses->size();
        return true;
    }
    return false;
}

bool ls_solver::update_outer_best_solution() {
    if (unsat_clauses->size() < _best_found_hard_cost_this_bool) {
        _best_found_hard_cost_this_bool = unsat_clauses->size();
        return true;
    }
    return false;
}

void ls_solver::enter_nra_mode() {
    _best_found_hard_cost_this_nra = unsat_clauses->size();
    if (is_in_bool_search) {
        no_improve_cnt_nra = 0;
    }   // only when it is now in boolean mode, the no_improve_cnt_nra will be 0
    is_in_bool_search = false;
}

void ls_solver::enter_bool_mode() {
    _best_found_hard_cost_this_bool = unsat_clauses->size();
    if (!is_in_bool_search) {
        no_improve_cnt_bool = 0;
    }   // only when it is now in integer mode, the no_improve_cnt_bool will be 0
    is_in_bool_search = true;
}

// The main local search algorithm
bool ls_solver::local_search() {
    if(build_unsat){return false;}
    int no_improve_cnt = 0;
    int flipv;
    rational change_value(0);
    start = std::chrono::steady_clock::now();
    initialize();
    if(!check_after_init()){return false;}
    _outer_layer_step = 1;
    for (_step = 1; _step < _max_step; _step++) {
#ifdef LS_DEBUG
        std::cout << "step: " << _step << "\n";
        std::cout.flush();
#endif
        if (unsat_clauses->size() == 0) {
#ifdef LS_DEBUG
            check_solution();
            // up_bool_vars();
            print_mv();
#endif
            up_bool_vars();
            return true;
        }
        // if (_step % 1000 == 0 && TimeElapsed() > _cutoff) {
        //     break;
        // }
        if (no_improve_cnt > 200000) {
            initialize();
            no_improve_cnt = 0;
        }   //restart
        bool time_up_bool = (no_improve_cnt_bool * _lit_in_unsat_clause_num > 5 * _bool_lit_in_unsat_clause_num);
        bool time_up_nra = (no_improve_cnt_nra * _lit_in_unsat_clause_num > 20 * (_lit_in_unsat_clause_num - _bool_lit_in_unsat_clause_num));
        if ((is_in_bool_search && _bool_lit_in_unsat_clause_num < _lit_in_unsat_clause_num && time_up_bool) ||
                _bool_lit_in_unsat_clause_num == 0) {
            enter_nra_mode();
        }
        else if ((!is_in_bool_search && _bool_lit_in_unsat_clause_num > 0 && time_up_nra) ||
                (_lit_in_unsat_clause_num == _bool_lit_in_unsat_clause_num)) {
            enter_bool_mode();
        }
        if (is_in_bool_search) {
            flipv = pick_critical_move_bool();
            if (flipv != -1) {
                critical_move(flipv, change_value);
            }
            if (update_outer_best_solution()) {
                no_improve_cnt_bool = 0;
            } else {
                no_improve_cnt_bool++;
            }
        }
        else {
            flipv = pick_critical_move(change_value);
            if (flipv != -1) {
                critical_move(flipv, change_value);
            }
            if (update_inner_best_solution()) {
                no_improve_cnt_nra=0;
            } else {
                no_improve_cnt_nra++;
            }
        }
        no_improve_cnt = (update_best_solution()) ? 0 : (no_improve_cnt + 1);
    }
    return false;
}
}
