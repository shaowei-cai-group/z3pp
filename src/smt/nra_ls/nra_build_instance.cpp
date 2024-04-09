#include "nra_ls.h"

namespace nra {

// input transformation
void ls_solver::split_string(std::string &in_string, std::vector<std::string> &str_vec,
                             std::string pattern=" ") {
    std::string::size_type pos;
    in_string += pattern;
    size_t size = in_string.size();
    for (size_t i = 0; i < size; i++) {
        pos = in_string.find(pattern, i);
        if (pos < size) {
            std::string s = in_string.substr(i, pos-i);
            str_vec.push_back(s);
            i = pos + pattern.size() - 1;
        }
    }
}

bool cmp_ve(var_exp ve1, var_exp ve2) {
    return (ve1.var_index < ve2.var_index) ||
        (ve1.var_index == ve2.var_index && ve1.exponent < ve2.exponent);
}

void ls_solver::modify_term_exp(term &t) {
    std::sort(t.var_epxs.begin(), t.var_epxs.end(), cmp_ve);
    int ve_size = 0;
    for (int curr_ve_idx = 1; curr_ve_idx < t.var_epxs.size(); curr_ve_idx++) {
        if (t.var_epxs[curr_ve_idx].var_index != t.var_epxs[ve_size].var_index) {
            t.var_epxs[++ve_size].var_index = t.var_epxs[curr_ve_idx].var_index;
            t.var_epxs[ve_size].exponent = 1;
        } // enter the next var
        else {
            t.var_epxs[ve_size].exponent++;
        } // the same var
    }
    if (++ve_size < t.var_epxs.size()) {
        t.var_epxs.resize(ve_size);
    }
} // (* x x y) --> (* x^2 y)

// transfer the ">=" to "<="
void ls_solver::invert_lit(lit &l) {
    l.key = -l.key;
    for (int i = 0; i < l.coff_terms.size(); i++) {
        l.coff_terms[i].coff *= -1;
    }
}

void ls_solver::build_lits(std::string &in_string) {
    std::vector<std::string> vec;
    split_string(in_string, vec);
    if (vec[0] == "0") {
        _lits[0].lits_index = 0;
        return;
    } // true literal
    int lit_index = std::atoi(vec[0].c_str());
    lit *l = &(_lits[lit_index]);
    if (vec[1] == "or" || vec[1] == "if") {
        l->delta = (int) transfer_name_to_resolution_var(vec[2], false);
        l->key = 1;
        l->is_nra_lit = false;
        l->lits_index = lit_index;
        return;
    } // or term in the form: 1 or newvar_2
    if (vec.size() > 2) {
        l->is_nra_lit = true;
        if (vec.size() > 6) {
            l->lits_index = std::atoi(vec[0].c_str());
            int idx = 5;
            if (vec[2] == "=" && vec[3] != "(") {
                idx++;
                l->key = -rational(vec[3].c_str());
            }
            l->is_equal = (vec[2] == "=");
            bool single_mul = false;
            if (vec[idx-1] == "*") {
                idx -= 2;
                single_mul = true;
            } // 849 ( = ( * lam6n64 rfc9 ) 0 ) now the idx at second '('
            for (; idx < vec.size(); idx++) {
                if (vec[idx] == ")") {
                    break;
                }
                if (vec[idx] == "(") {
                    idx += 2;
                    term new_t;
                    if ((vec[idx][0] < '0' || vec[idx][0] > '9') && (vec[idx][0] != '-')) {
                        // ( * global_invc1_0 lam1n4 )
                        while (vec[idx] != ")") {
                            var_exp ve((int) transfer_name_to_tmp_var(vec[idx++]));
                            new_t.var_epxs.push_back(ve);
                        }
                        modify_term_exp(new_t); // modify term: (* x x y) --> (* x^2 y)
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), rational(1)));
                        if (single_mul) {
                            break;
                        } // now the idx at ')'
                    }
                    else {
                        rational coff(vec[idx].c_str());
                        while (denominator(coff) > denominator(min_ration)) {
                            min_ration /= rational(2);
                        }
                        if (vec[++idx] == "(") { // ( * -1 ( * x y ) )idx at '('
                            idx += 2;
                            while (vec[idx] != ")") {
                                var_exp ve((int) transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                        }
                        else { // ( * 115 x ) idx at x
                            var_exp ve((int)transfer_name_to_tmp_var(vec[idx]));
                            new_t.var_epxs.push_back(ve);
                        }
                        modify_term_exp(new_t);
                        l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t), coff));
                        idx++;
                        if (single_mul) {
                            break;
                        } // now the idx at ')'
                    }
                }
                else {
                    term new_t;
                    new_t.var_epxs.push_back(var_exp((int) transfer_name_to_tmp_var(vec[idx])));
                    l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t), rational(1)));
                }
                _num_opt += l->coff_terms.size();
            }
            if (vec[2] != "=" || vec[3] == "(") {
                l->key = -rational(vec[++idx].c_str());
            }
            if (vec[2] == ">=") {
                invert_lit(*l);
            }
        } // ( <= ( + x1 ( * -1 x2 ) x7 ( * -1 x8 ) ) 0 )
        else {
            l->lits_index = std::atoi(vec[0].c_str());
            if (vec[2] == "=" && vec.size() == 6 && (vec[3][0] < '0' || vec[3][0] > '9') &&
                    (vec[4][0] < '0' || vec[4][0] > '9') && (vec[3][0] != '-') && (vec[4][0] != '-')) {
                l->is_equal = true;
                l->key = 0;
                term new_t_1, new_t_2;
                var_exp ve_1((int) transfer_name_to_tmp_var(vec[3])), ve_2((int) transfer_name_to_tmp_var(vec[4]));
                new_t_1.var_epxs.push_back(ve_1);
                new_t_2.var_epxs.push_back(ve_2);
                l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t_1), rational(1)));
                l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t_2), rational(-1)));
            } // ( = x1 x2 )
            else {
                rational bound;
                uint64_t var_idx;
                if ((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3][0] != '-')) {
                    bound = rational(vec[4].c_str());
                    var_idx = transfer_name_to_tmp_var(vec[3]);
                } // ( >= x 0 )
                else {
                    bound = rational(vec[3].c_str());
                    var_idx = transfer_name_to_tmp_var(vec[4]);
                } // ( = 0 x )
                term new_t;
                new_t.var_epxs.push_back(var_exp((int)var_idx));
                if (vec[2] == ">=") {
                    l->key = bound;
                    l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t), rational(-1)));
                }
                else {
                    l->key = -bound;
                    l->coff_terms.push_back(coff_term((int) transfer_term_to_idx(new_t), rational(1)));
                }
                l->is_equal = (vec[2] == "=");
            } // ( >= x 0 )
        }
    } // nra lit
    else {
        l->delta = (int) transfer_name_to_resolution_var(vec[1], false);
        l->key = 1;
        l->is_nra_lit = false;
        l->lits_index = lit_index;
    } // boolean lit
}

int ls_solver::find(int var_idx) {
    if (var_idx == fa[var_idx]) {
        fa_coff[var_idx] = 1;
        return var_idx;
    }
    else {
        int old_fa = fa[var_idx];
        int new_fa = find(fa[var_idx]);
        fa_coff[var_idx] *= fa_coff[old_fa];
        return fa[var_idx] = new_fa;
    }
}

// Merge with condition coff_1 * var_1 == coff_2 * var_2
void ls_solver::merge(int var_idx_1, int var_idx_2, const rational & coff_1, const rational & coff_2) {
    int fa_1 = find(var_idx_1), fa_2 = find(var_idx_2);
    if (fa_1 == fa_2) {
        return;
    }
    // fa_coff_1 * fa_1 = fa_coff_2 * fa_2
    rational fa_coff_1 = fa_coff[var_idx_1] * coff_1, fa_coff_2 = fa_coff[var_idx_2] * coff_2;
    if (abs(fa_coff_1) > abs(fa_coff_2)) {
        fa[fa_2] = fa_1;
        fa_coff[fa_2] = fa_coff_1 / fa_coff_2;
    } // fa_2 = (fa_coff_1 / fa_coff_2) * fa_1
    else {
        fa[fa_1] = fa_2;
        fa_coff[fa_1] = fa_coff_2 / fa_coff_1;
    } // fa_1 = (fa_coff_2 / fa_coff_1) * fa_2
}

bool cmp_coff_term(coff_term cf1, coff_term cf2) {
    return cf1.term_idx < cf2.term_idx;
}

void ls_solver::equal_vars(std::vector<std::vector<int> >& clause_vec) {
    fa.resize(_tmp_vars.size());
    for (int var_idx = 0; var_idx < _tmp_vars.size(); var_idx++) {
        fa[var_idx] = var_idx;
    } // initialize the fa vec
    fa_coff.resize(_tmp_vars.size(), rational(1));
    std::vector<int> unit_equal_lits;
    // find out all unit equal lits
    for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++) {
        if (clause_vec[clause_idx].size() == 1 && clause_vec[clause_idx][0] > 0) {
            int lit_idx = clause_vec[clause_idx][0];
            lit *l = &(_lits[lit_idx]);
            if (l->key == 0 && l->is_equal) { // t1 + t2 + ... + tn = 0
                bool flag_all_single = true;
                for (coff_term & cf : l->coff_terms) {
                    if (!is_single_var_term(_terms[cf.term_idx])) {
                        flag_all_single = false;
                        break;
                    }
                }
                if (flag_all_single) {
                    unit_equal_lits.push_back(lit_idx);
                }
            }
        }
    }
    bool find_new_merge = true;
    while (find_new_merge) {
        find_new_merge = false;
        // merge the equalities
        for (int i = 0; i < unit_equal_lits.size(); i++) {
            lit *l = &(_lits[unit_equal_lits[i]]);
            if (l->lits_index == 0) {
                continue;
            }
            if (l->coff_terms.size() == 2) {
                find_new_merge = true;
                int var_1 = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                int var_2 = _terms[l->coff_terms[1].term_idx].var_epxs[0].var_index;
                merge(var_1, var_2, l->coff_terms[0].coff, -l->coff_terms[1].coff);
                l->lits_index = 0;
            }
        }
        // modify the lit by new equality
        for (int i = 0; i < unit_equal_lits.size(); i++) {
            update_lit_equal(unit_equal_lits[i]);
        }
    }
//    std::cout<<"eq map\n";
//    for(int v_idx=0;v_idx<_tmp_vars.size();v_idx++){
//        int new_v_idx=find(v_idx);
//        if(new_v_idx!=v_idx){
//            std::cout<<_tmp_vars[v_idx].var_name<<" = "<<fa_coff[v_idx]<<" * "<<_tmp_vars[new_v_idx].var_name<<"\n";
//        }
//    }
    // update all lits
    for (int lit_idx = 0; lit_idx < _lits.size(); lit_idx++) {
        update_lit_equal(lit_idx);
    }
}

void ls_solver::update_lit_equal(int lit_idx) {
    lit *l = &(_lits[lit_idx]);
    if (l->lits_index == 0 || !l->is_nra_lit) {
        return;
    }
    bool lit_modified = false;
    for (coff_term & cf : l->coff_terms) {
        term new_t = _terms[cf.term_idx];
        bool term_modified = false;
        rational new_coff = cf.coff;
        for (var_exp & ve : new_t.var_epxs) {
            int var_idx = ve.var_index;
            int new_var_idx = find(var_idx);
            if (new_var_idx != var_idx) { // modify the var
                lit_modified = true;
                term_modified = true;
                ve.var_index = new_var_idx;
                new_coff *= fa_coff[var_idx];
            }
        }
        if (term_modified) {
            cf = coff_term((int) transfer_term_to_idx(new_t), new_coff);
        }
    }
    if (lit_modified) {
        std::sort(l->coff_terms.begin(), l->coff_terms.end(), cmp_coff_term);
        int curr_term_idx = l->coff_terms[0].term_idx;
        rational curr_coff(0);
        int lit_coff_term_idx = 0;
        for (int cf_idx = 0; cf_idx < l->coff_terms.size(); cf_idx++) {
            if (l->coff_terms[cf_idx].term_idx != curr_term_idx) {
                curr_term_idx = l->coff_terms[cf_idx].term_idx;
                curr_coff = rational(0);
            } // enter a new term
            curr_coff += l->coff_terms[cf_idx].coff; // the same term
            if (curr_coff != 0 && cf_idx == l->coff_terms.size() - 1 ||
                    l->coff_terms[cf_idx+1].term_idx != curr_term_idx) {
                l->coff_terms[lit_coff_term_idx].term_idx = curr_term_idx;
                l->coff_terms[lit_coff_term_idx++].coff = curr_coff;
            } // the last coff_term of the current term
        }
        l->coff_terms.resize(lit_coff_term_idx);
        int ct_size = 0;
        for (int ct_idx = 0; ct_idx < lit_coff_term_idx; ct_idx++) {
            if (l->coff_terms[ct_idx].coff != 0) {
                l->coff_terms[ct_size++] = l->coff_terms[ct_idx];
            }
        } // delete those lits with coff == 0
        l->coff_terms.resize(ct_size);
        if (ct_size == 0) {
            l->lits_index = 0;
        }
    }
}

void ls_solver::build_instance(std::vector<std::vector<int> > & clause_vec) {
    equal_vars(clause_vec);
    for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++) {
        if (clause_vec[clause_idx].size() == 1) {
            lit *l = &(_lits[std::abs(clause_vec[clause_idx][0])]);
            if (l->is_equal || !l->is_nra_lit) {
                continue;
            } // equal lit is not bound lit
            if (l->coff_terms.size() == 1 && is_single_var_term(_terms[l->coff_terms[0].term_idx])) {
                rational new_low_bound(-max_int);
                rational new_upper_bound(max_int);
                int var_idx = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                if (clause_vec[clause_idx][0] > 0) {
                    if (l->coff_terms[0].coff > 0) {
                        new_upper_bound = (-l->key) / (l->coff_terms[0].coff);
                    } // ax+k<=0   x<=(-k/a)
                    else {
                        new_low_bound = (-l->key) / (l->coff_terms[0].coff);
                    } // ax+k<=0  x>=(-k/a)
                }
                else {
                    if (l->coff_terms[0].coff > 0) {
                        new_low_bound = ((-l->key) / (l->coff_terms[0].coff)) + min_ration;
                    } // ax+k>0  x>(-k)/a
                    else {
                        new_upper_bound = ((-l->key) / (l->coff_terms[0].coff)) - min_ration;
                    } // ax+k>1 x<(-k)/a
                }
                if (new_low_bound > _tmp_vars[var_idx].low_bound) {
                    _tmp_vars[var_idx].low_bound = new_low_bound;
                }
                else if (new_upper_bound < _tmp_vars[var_idx].upper_bound) {
                    _tmp_vars[var_idx].upper_bound = new_upper_bound;
                }
                if (l->lits_index != 0) {
                    _bound_lits.push_back(l->lits_index);
                }
                l->lits_index = 0;
                if (clause_vec[clause_idx][0] < 0) {
                    clause_vec[clause_idx][0] = -clause_vec[clause_idx][0];
                }
            }
        }
    }
    for (variable & v_tmp : _tmp_vars) {
        if (v_tmp.low_bound > v_tmp.upper_bound) {
            build_unsat = true;
            break;
        }
    }
    // if the clause contains more than 2 lits, and one of them is nra_lit and true,
    // then the clause is tautology
    std::vector<bool> tautology_clauses_with_lits2(clause_vec.size(), false);
    for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++) {
        if (clause_vec[clause_idx].size() < 2) {
            continue;
        }
        for (auto l_idx : clause_vec[clause_idx]) {
            lit *l = &(_lits[std::abs(l_idx)]);
            if (l->lits_index == 0 && l->is_nra_lit) {
                tautology_clauses_with_lits2[clause_idx] = true;
                break;
            }
        }
    }
    reduce_vars();
    _clauses.resize(clause_vec.size());
    _num_clauses = 0;
    for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++) {
        bool is_tautology = false;
        for (auto l_idx : clause_vec[clause_idx]) {
            if (_lits[std::abs(l_idx)].lits_index == 0) {
                is_tautology = true;
                break;
            }
        }
        if (is_tautology || tautology_clauses_with_lits2[clause_idx]) {
            continue;
        }
        for (auto l_idx : clause_vec[clause_idx]) {
            _clauses[_num_clauses].literals.push_back(l_idx);
            lit *l = &(_lits[std::abs(l_idx)]);
            if (l->lits_index == 0) {
                continue;
            }
            if (!l->is_nra_lit) {
                _resolution_vars[l->delta.get_int32()].clause_idxs.push_back((int) _num_clauses);
            }
        }
        _num_clauses++;
    }
    _clauses.resize(_num_clauses);
    // now the vars are all in the resolution vars
    unit_prop();
    resolution();
    unit_prop();
    reduce_clause();
//    print_formula();
    best_found_cost = (int) _num_clauses;
    make_space();
    set_pre_value();
}

// return the index of a term if it exists, otherwise create a new one
uint64_t ls_solver::transfer_term_to_idx(term t) {
    std::string term_str;
    transfer_term_to_str(t, term_str);
    if (str2termidx.find(term_str) == str2termidx.end()) {
        str2termidx[term_str] = _terms.size();
        _terms.push_back(t);
        return _terms.size() - 1;
    }
    else {
        return str2termidx[term_str];
    }
}

// sort the term var_index and the exponent
void ls_solver::transfer_term_to_str(term &t, std::string &str) {
    std::sort(t.var_epxs.begin(), t.var_epxs.end(), cmp_ve);
    str.clear();
    for (int i = 0; i < t.var_epxs.size(); i++) {
        str += "_" + std::to_string(t.var_epxs[i].var_index) + "^" + std::to_string(t.var_epxs[i].exponent);
    }
}

uint64_t ls_solver::transfer_name_to_reduced_var(std::string &name, bool is_nra) {
    if (name2var.find(name) == name2var.end()) {
        name2var[name] = _vars.size();
        variable var;
        var.var_name = name;
        var.is_nra = is_nra;
        _vars.push_back(var);
        if (is_nra) {
            nra_var_vec.push_back((int)_vars.size()-1);
        }
        else {
            bool_var_vec.push_back((int)_vars.size()-1);
        }
        return _vars.size()-1;
    }
    else {
        return name2var[name];
    }
}

uint64_t ls_solver::transfer_name_to_resolution_var(std::string & name,bool is_nra) {
    if (name2resolution_var.find(name) == name2resolution_var.end()) {
        name2resolution_var[name] = _resolution_vars.size();
        variable var;
        var.clause_idxs.reserve(64);
        var.literal_idxs.reserve(64);
        var.term_exps.reserve(64);
        var.var_lit_terms.reserve(64);
        var.var_name = name;
        var.is_nra = is_nra;
        _resolution_vars.push_back(var);
        if (is_nra) {
            nra_var_vec.push_back((int)_resolution_vars.size()-1);
        }
        else {
            bool_var_vec.push_back((int)_resolution_vars.size()-1);
        }
        return _resolution_vars.size()-1;
    }
    else {
        return name2resolution_var[name];
    }
}

uint64_t ls_solver::transfer_name_to_tmp_var(std::string & name) {
    if (name2tmp_var.find(name) == name2tmp_var.end()) {
        name2tmp_var[name] = _tmp_vars.size();
        variable var;
        var.is_nra = true;
        var.var_name = name;
        _tmp_vars.push_back(var);
        return _tmp_vars.size()-1;
    }
    else {
        return name2tmp_var[name];
    }
}

// transfer the nra var into _resolution_vars, turn (x-y) to z
void ls_solver::reduce_vars() {
    const uint64_t tmp_vars_size = _tmp_vars.size();
    // hash_map[A*(size)+b]=n means A-B has occurred n times
    std::vector<int> hash_map(tmp_vars_size * tmp_vars_size, 0);
    // occur_time[a]=n means that a has occured in lits for n times
    std::vector<int> occur_time(tmp_vars_size, 0);
    term *t;
    variable * original_var;
    variable * new_var;
    std::string var_name;
    int original_var_idx;
    use_pbs = !(_resolution_vars.size() == 0);
    for (int var_idx = 0; var_idx < tmp_vars_size; var_idx++) {
        if (_tmp_vars[var_idx].upper_bound > 1 || _tmp_vars[var_idx].low_bound < 0) {
            use_pbs = false;
            break;
        }
    }
    if (use_pbs) {
        _resolution_vars = _tmp_vars;
    } // if there is no boolean vars and all nra vars are in [0,1], then use pbs, and no need to reduce the vars
    else {
        name2var.clear();
        str2termidx.clear();
        // rewrite terms, and put all integer vars into resolution_vars, map the term to number again
        for (int term_idx = 0; term_idx < _terms.size(); term_idx++) {
            t = &(_terms[term_idx]);
            for (int ve_idx = 0; ve_idx < t->var_epxs.size(); ve_idx++) {
                original_var_idx = t->var_epxs[ve_idx].var_index;
                t->var_epxs[ve_idx].var_index = (int) transfer_name_to_resolution_var(_tmp_vars[original_var_idx].var_name, true);
            }
            std::string term_s;
            transfer_term_to_str(*t, term_s);
            str2termidx[term_s] = term_idx;
        }
        std::string term_s;
        for (int term_idx = 0; term_idx < _terms.size(); term_idx++) {
            transfer_term_to_str(_terms[term_idx], term_s);
            str2termidx[term_s] = term_idx;
        }
        // set lower and upper bound
        for (original_var_idx = 0; original_var_idx<_tmp_vars.size(); original_var_idx++) {
            original_var = &(_tmp_vars[original_var_idx]);
            // original var
            new_var = &(_resolution_vars[transfer_name_to_resolution_var(original_var->var_name,true)]);
            new_var->low_bound = original_var->low_bound;
            new_var->upper_bound = original_var->upper_bound;
        }
    }
    int num_var_with_bound = 0;
    for (int var_idx = 0; var_idx < _resolution_vars.size(); var_idx++) {
        new_var = &(_resolution_vars[var_idx]);
        if (!new_var->is_nra) {
            continue;
        }
        if (new_var->upper_bound != max_int && new_var->low_bound != -max_int) {
            continue;
        } // if a var has both upper bound and lower bound, no bound lits is added.
        if (new_var->low_bound != -max_int) {
            int lit_idx = _bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_nra_lit = true;
            bound_lit.lits_index = lit_idx;
            term new_t;
            new_t.var_epxs.push_back(var_idx);
            bound_lit.coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -denominator(new_var->low_bound)));
            bound_lit.key = numerator(new_var->low_bound);
            _lits[lit_idx] = bound_lit;
            new_var->low_bound = -max_int;
        }
        if (new_var->upper_bound != max_int) {
            int lit_idx = _bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_nra_lit = true;
            bound_lit.lits_index = lit_idx;
            term new_t;
            new_t.var_epxs.push_back(var_idx);
            bound_lit.coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), denominator(new_var->upper_bound)));
            bound_lit.key = -numerator(new_var->upper_bound);
            _lits[lit_idx] = bound_lit;
            new_var->upper_bound = max_int;
        }
    }
}

void ls_solver::unit_prop() {
    std::stack<uint64_t> unit_clause; // the var_idx in the unit clause
    for (uint64_t clause_idx = 0; clause_idx < _num_clauses; clause_idx++) {
        // the unit clause is the undeleted clause containing only one bool var
        if (!_clauses[clause_idx].is_delete && _clauses[clause_idx].literals.size() == 1 &&
                !_lits[std::abs(_clauses[clause_idx].literals[0])].is_nra_lit) {
            unit_clause.push(clause_idx);
        }
    }
    while (!unit_clause.empty()) {
        uint64_t unit_clause_idx = unit_clause.top();
        unit_clause.pop();
        if (_clauses[unit_clause_idx].is_delete) {
            continue;
        }
        int is_pos_lit = (_clauses[unit_clause_idx].literals[0] > 0) ? 1 : -1; // determine the sign of the var in unit clause
        int unit_var = (int) _lits[std::abs(_clauses[unit_clause_idx].literals[0])].delta.get_int32(); // determing the var in unit clause
        _resolution_vars[unit_var].is_delete = true; // delete the unit var
        _resolution_vars[unit_var].up_bool = is_pos_lit; // set the solution of a boolean var as its unit propogation value
        for (uint64_t cl_idx : _resolution_vars[unit_var].clause_idxs) {
            clause *cl = &(_clauses[cl_idx]);
            if (cl->is_delete) {
                continue;
            }
            for (uint64_t lit_idx = 0; lit_idx < cl->literals.size(); lit_idx++) {
                int l_id_in_lits = cl->literals[lit_idx];
                lit *l = &(_lits[std::abs(l_id_in_lits)]);
                // go through the clauses of the unit var, find the var in corresponding clause
                if (!l->is_nra_lit && l->delta == unit_var) {
                    if ((is_pos_lit > 0 && l_id_in_lits > 0) || (is_pos_lit < 0 && l_id_in_lits < 0)) {
                        cl->is_delete = true;
                        // delete the clause from corresponding bool var
                        for (int l_idx_inner : cl->literals) {
                            lit *l_inner = &(_lits[std::abs(l_idx_inner)]);
                            if (!l_inner->is_nra_lit && l_inner->delta != unit_var) {
                                variable *var_inner = &(_resolution_vars[l_inner->delta.get_int32()]);
                                for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++) {
                                    if (var_inner->clause_idxs[delete_idx] == cl_idx) {
                                        var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();
                                        var_inner->clause_idxs.pop_back();
                                        break;
                                    }
                                }
                            }
                        }
                    } // if there exist same lit, the clause is already set true, then delete the clause
                    else { // else delete the lit
                        cl->literals[lit_idx] = cl->literals.back();
                        cl->literals.pop_back();
                        if (cl->literals.size() == 1 && !_lits[std::abs(cl->literals[0])].is_nra_lit) {
                            unit_clause.push(cl_idx);
                        } // if after deleting, it becomes unit clause
                    }
                    break;
                }
            }
        }
    }
}

__int128_t ls_solver::hash_lits_to_num(std::vector<int> &lits){
    std::sort(lits.begin(), lits.end());
    __int128_t hash_num = 0;
    for (int lit_idx : lits) {
        hash_num = (__int128_t) hash_num * (__int128_t)(_num_lits) + (__int128_t)lit_idx + (__int128_t)_num_lits;
    }
    return hash_num;
}

bool ls_solver::is_same_lits(std::vector<int> &lits_1, std::vector<int> &lits_2) {
    if (lits_1.size() != lits_2.size()) {
        return false;
    }
    std::sort(lits_1.begin(), lits_1.end());
    std::sort(lits_2.begin(), lits_2.end());
    for (int l_idx = 0; l_idx < lits_1.size(); l_idx++) {
        if (lits_1[l_idx] != lits_2[l_idx]) {
            return false;
        }
    }
    return true;
}

void ls_solver::resolution(){
    std::vector<uint64_t> pos_clauses(10 * _num_clauses);
    std::vector<uint64_t> neg_clauses(10 * _num_clauses);
    // for the clause with literal {a,b,c}, sort the lit by its order,
    // and hash the literals to a number, then map it to the clause_idx,
    // if deleted, set it to -1
    std::map<__int128_t,int>  clauselit_map;
    std::vector<__int128_t>   clauselit(_clauses.size()); // hash the lits of clause to a number
    for (int cls_idx = 0; cls_idx < _clauses.size(); cls_idx++) {
        clauselit[cls_idx] = hash_lits_to_num(_clauses[cls_idx].literals);
        clauselit_map[clauselit[cls_idx]] = cls_idx;
    }
    int pos_clause_size, neg_clause_size;
    bool is_improve = true;
    while (is_improve) {
        is_improve = false;
    for (uint64_t bool_var_idx : bool_var_vec) {
        if (_resolution_vars[bool_var_idx].is_delete) {
            continue;
        }
        pos_clause_size = 0;
        neg_clause_size = 0;
        for (int i = 0; i < _resolution_vars[bool_var_idx].clause_idxs.size(); i++) {
            uint64_t clause_idx = _resolution_vars[bool_var_idx].clause_idxs[i];
            if (_clauses[clause_idx].is_delete) {
                continue;
            }
            for (int l_var_sign : _clauses[clause_idx].literals) {
                // make sure that it is a boolean literal and is exactly the one containing the var
                if (!_lits[std::abs(l_var_sign)].is_nra_lit &&
                        _lits[std::abs(l_var_sign)].delta == (int) bool_var_idx) {
                    if (l_var_sign > 0) {
                        pos_clauses[pos_clause_size++] = clause_idx;
                    }
                    else {
                        neg_clauses[neg_clause_size++] = clause_idx;
                    }
                    break;
                }
            }
        } // determine the pos_clause and neg_clause
        int tautology_num = 0;
        for (int i = 0; i < pos_clause_size; i++) { //pos clause X neg clause
            uint64_t pos_clause_idx = pos_clauses[i];
            for (int j = 0; j < neg_clause_size; j++) {
                uint64_t neg_clause_idx = neg_clauses[j];
                bool is_tautology_flag=false;
                for (int k = 0; k < _clauses[neg_clause_idx].literals.size(); k++) {
                    int l_neg_lit = _clauses[neg_clause_idx].literals[k];
                    // the bool_var for resolution is not considered
                    // (that is \neg (the lit is bool lit and it contains the var))
                    if (_lits[std::abs(l_neg_lit)].delta != (int) bool_var_idx ||
                            _lits[std::abs(l_neg_lit)].is_nra_lit) {
                        for (int l_pos_lit : _clauses[pos_clause_idx].literals) {
                            if (-l_neg_lit == (l_pos_lit)) {
                                tautology_num++;
                                break;
                            } //if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                    }
                    if(is_tautology_flag){break;}
                }
                if(is_tautology_flag){tautology_num++;}
            }
        }
        if ((pos_clause_size * neg_clause_size - tautology_num) > (pos_clause_size + neg_clause_size)) {
            continue;
        } // if deleting the var can cause 2 times clauses, then skip it
        for (uint64_t clause_idx : _resolution_vars[bool_var_idx].clause_idxs) {
            // delete the clauses of bool_var
            _clauses[clause_idx].is_delete = true;
            for (int l_idx_sign : _clauses[clause_idx].literals) {
                // delete the clause from corresponding bool var
                lit *l = &(_lits[std::abs(l_idx_sign)]);
                if (!l->is_nra_lit && l->delta != (int) bool_var_idx) {
                    variable *var_inner = &(_resolution_vars[l->delta.get_int32()]);
                    for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++) {
                        if (var_inner->clause_idxs[delete_idx] == clause_idx) {
                            var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();
                            var_inner->clause_idxs.pop_back();
                            break;
                        }
                    }
                }
            }
        }
        is_improve = true;
        _resolution_vars[bool_var_idx].is_delete = true;
        if (pos_clause_size == 0) {
            _resolution_vars[bool_var_idx].up_bool = -1;
        } // if it is a false pure lit, the var is set to false
        if (neg_clause_size == 0) {
            _resolution_vars[bool_var_idx].up_bool = 1;
        } // if it is a true pure lit, the var is set to true
        if (pos_clause_size == 0 || neg_clause_size == 0) {
            continue;
        } // pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause
        for (int i = 0; i < pos_clause_size; i++) { // pos clause X neg clause
            uint64_t pos_clause_idx = pos_clauses[i];
            for (int j = 0; j < neg_clause_size; j++) {
                uint64_t neg_clause_idx = neg_clauses[j];
                clause new_clause;
                uint64_t pos_lit_size = _clauses[pos_clause_idx].literals.size();
                uint64_t neg_lit_size = _clauses[neg_clause_idx].literals.size();
                new_clause.literals.reserve(pos_lit_size + neg_lit_size);
                bool is_tautology = false;
                for (int k = 0; k < pos_lit_size; k++) {
                    int l_sign_idx = _clauses[pos_clause_idx].literals[k];
                    if (_lits[std::abs(l_sign_idx)].is_nra_lit ||
                            _lits[std::abs(l_sign_idx)].delta != (int) bool_var_idx) {
                        new_clause.literals.push_back(l_sign_idx);
                    }
                } // add the lits in pos clause to new clause
                for (int k = 0; k < neg_lit_size; k++) {
                    int l_sign_idx = _clauses[neg_clause_idx].literals[k];
                    if (_lits[std::abs(l_sign_idx)].is_nra_lit ||
                            _lits[std::abs(l_sign_idx)].delta != (int) bool_var_idx) {
                        bool is_existed_lit = false;
                        for (uint64_t i = 0; i < pos_lit_size - 1; i++) {
                            if (l_sign_idx == (new_clause.literals[i])) {
                                is_existed_lit = true;
                                break;
                            } // if the lit has existed, then it will not be added
                            if (l_sign_idx == (-new_clause.literals[i])) {
                                is_tautology = true;
                                break;
                            } // if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                        if (is_tautology) {
                            break;
                        }
                        if (!is_existed_lit) {
                            new_clause.literals.push_back(l_sign_idx);
                        }
                    }
                }
                if (!is_tautology) {
                    __int128_t clause_lit_hash = hash_lits_to_num(new_clause.literals);
                    bool should_add = false;
                    if (clauselit_map.find(clause_lit_hash) == clauselit_map.end()) {
                        should_add = true;
                    } // the clause never appears
                    else {
                        int origin_clause_idx = clauselit_map[clause_lit_hash];
                        clause *cl_origin = &(_clauses[origin_clause_idx]);
                        if (cl_origin->is_delete) {
                            should_add = true;
                        } // the clause has been deleted
                        else if (!is_same_lits(cl_origin->literals, new_clause.literals)) {
                            should_add = true;
                        } // not the same one
                    }
                    if (should_add) {
                        // add new clause, if it never appers then add it
                        for (int l_sign_idx : new_clause.literals) {
                            lit *l_inner = &(_lits[std::abs(l_sign_idx)]);
                            if (!l_inner->is_nra_lit) {
                                _resolution_vars[l_inner->delta.get_int32()].clause_idxs.push_back((int) _num_clauses);
                            }
                        }
                        _clauses.push_back(new_clause);
                        clauselit.push_back(clause_lit_hash);
                        clauselit_map[clause_lit_hash] = (int) _num_clauses;
                        _num_clauses++;
                    }
                }
            }
        }
        for (int i = 0; i < pos_clause_size; i++) {
            clause pos_cl = _clauses[pos_clauses[i]];
            for (int j = 0; j < pos_cl.literals.size(); j++) {
                int l_idx = pos_cl.literals[j];
                lit *l = &(_lits[std::abs(l_idx)]);
                if (!l->is_nra_lit && l->delta == bool_var_idx) {
                    pos_cl.literals[j] = pos_cl.literals[0];
                    pos_cl.literals[0] = l_idx;
                    break;
                }
            }
            _reconstruct_stack.push(pos_cl);
        }
        for (int i = 0; i < neg_clause_size; i++) {
            clause neg_cl = _clauses[neg_clauses[i]];
            for(int j = 0; j < neg_cl.literals.size(); j++) {
                int l_idx = neg_cl.literals[j];
                lit *l = &(_lits[std::abs(l_idx)]);
                if (!l->is_nra_lit && l->delta == bool_var_idx) {
                    neg_cl.literals[j] = neg_cl.literals[0];
                    neg_cl.literals[0] = l_idx;
                    break;
                }
            }
            _reconstruct_stack.push(neg_cl);
        }
    }
    }
}

bool cmp_vlt_by_var(var_lit_term vlt1, var_lit_term vlt2) {
    return vlt1.var_idx < vlt2.var_idx ||
        (vlt1.var_idx == vlt2.var_idx && vlt1.exponent < vlt2.exponent) ||
        (vlt1.var_idx == vlt2.var_idx && vlt1.exponent == vlt2.exponent && vlt1.term_idx < vlt2.term_idx);
}

bool cmp_vlt_by_lit(var_lit_term vlt1, var_lit_term vlt2) {
    return vlt1.lit_idx < vlt2.lit_idx || (vlt1.lit_idx == vlt2.lit_idx && vlt1.term_idx < vlt2.term_idx);
}

void ls_solver::reduce_clause() {
    bool_var_vec.clear();
    nra_var_vec.clear();
    _vars.reserve(_resolution_vars.size());
    int i, reduced_clause_num;
    i = 0;
    reduced_clause_num = 0;
    for (; i < _num_clauses; i++) {
        if (!_clauses[i].is_delete) {
            _clauses[reduced_clause_num++] = _clauses[i];
        }
    }
    _clauses.resize(reduced_clause_num);
    
    _num_nra_lits = 0;
    _num_bool_lits = 0;
    for (int l_idx = 0; l_idx < _lits.size(); l_idx++) {
        _lits[l_idx].lits_index = 0;
    } // reset the lit_index
    // transfer the resolution vars to vars
    _num_clauses = reduced_clause_num;
    lit_appear.resize(_num_lits + _additional_len, false);
    term_appear.resize(_terms.size() + _additional_len, false);
    for (variable & v : _resolution_vars) {
        if (v.is_nra && v.upper_bound != max_int && v.low_bound != -max_int) {
            transfer_name_to_reduced_var(v.var_name, true);
        }
    } // if the var has both upper and lower bound, then it may not exist in any clause, but it should be considered as a var
    for (int clause_idx = 0; clause_idx < reduced_clause_num; clause_idx++) {
        _clauses[clause_idx].weight = 1;
        for (int k = 0; k < _clauses[clause_idx].literals.size(); k++) {
            int l_sign_idx = _clauses[clause_idx].literals[k];
            lit *l = &(_lits[std::abs(l_sign_idx)]);
            if (l->is_nra_lit) {
                variable *v;
                for (int j = 0; j < l->coff_terms.size(); j++) {
                    term *t = &(_terms[l->coff_terms[j].term_idx]);
                    if (!term_appear[l->coff_terms[j].term_idx]) {
                        for (var_exp & ve : t->var_epxs) {
                            ve.var_index = (int) transfer_name_to_reduced_var(_resolution_vars[ve.var_index].var_name, true);
                        }
                        term_appear[l->coff_terms[j].term_idx] = true;
                    }
                    for (var_exp & ve : t->var_epxs) {
                        v = &(_vars[ve.var_index]);
                        v->clause_idxs.push_back(clause_idx);
                    }
                }
                _clauses[clause_idx].nra_literals.push_back(l_sign_idx);
            }
            else {
                if (!lit_appear[std::abs(l_sign_idx)]) {
                    l->delta = (int)transfer_name_to_reduced_var(_resolution_vars[l->delta.get_int32()].var_name, false);
                    // for a boolean var, its first lit_idx is the lit containing the var
                    _vars[l->delta.get_int32()].literal_idxs.push_back(std::abs(l_sign_idx));
                }
                _vars[l->delta.get_int32()].clause_idxs.push_back(clause_idx);
                // for a boolean var, if it is neg in a clause, it is false
                _vars[l->delta.get_int32()].bool_var_in_pos_clause.push_back(l_sign_idx > 0);
                _clauses[clause_idx].bool_literals.push_back(l_sign_idx);
            }
            if (!lit_appear[std::abs(l_sign_idx)]) {
                lit_appear[std::abs(l_sign_idx)] = true;
                _lits[std::abs(l_sign_idx)].lits_index = std::abs(l_sign_idx);
            }
        }
    }
    _vars.resize(_vars.size());
    _num_vars = _vars.size();
    _num_nra_vars = 0;
    for(variable & v : _vars) {
        uint64_t pre_clause_idx = INT64_MAX;
        int var_clause_num = 0;
        for (int i = 0; i < v.clause_idxs.size(); i++) {
            uint64_t tmp_clause_idx = v.clause_idxs[i];
            if (pre_clause_idx != tmp_clause_idx) {
                pre_clause_idx = tmp_clause_idx;
                v.clause_idxs[var_clause_num++] = (int) pre_clause_idx;
            }
        }
        v.clause_idxs.resize(var_clause_num);
        if (v.is_nra) {
            v.upper_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true)].upper_bound;
            v.low_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true)].low_bound;
            _num_nra_vars++;
        }
    } // determine the clause_idxs of var
    lit *l;
    term *t;
    for (int l_idx = 0; l_idx < _lits.size(); l_idx++) {
        l = &(_lits[l_idx]);
        if (l->lits_index == 0) {
            continue;
        }
        for (int pos_term_idx = 0; pos_term_idx < l->coff_terms.size(); pos_term_idx++) {
            uint64_t term_idx = l->coff_terms[pos_term_idx].term_idx;
            rational coff = l->coff_terms[pos_term_idx].coff;
            t = &(_terms[term_idx]);
            for (int ve_idx = 0; ve_idx < t->var_epxs.size(); ve_idx++) {
                uint64_t var_idx = t->var_epxs[ve_idx].var_index;
                var_lit_term vlt(t->var_epxs[ve_idx], term_idx, l_idx, coff);
                _vars[var_idx].var_lit_terms.push_back(vlt);
                l->var_lit_terms.push_back(vlt);
            }
        }
    } // determine the var_lit_term of var and lit, the vlt has been sorted by the lit_idx in vars
    for (lit & l : _lits) {
        if (l.lits_index != 0) {
            std::sort(l.var_lit_terms.begin(), l.var_lit_terms.end(), cmp_vlt_by_var);
        }
    } // sort the vlt in lit by its var_idx
    for (variable & v : _vars) {
        uint64_t pre_lit_idx = INT64_MAX;
        int var_lit_num = 0;
        for(int i = 0; i < v.var_lit_terms.size(); i++) {
            uint64_t tmp_lit_idx = v.var_lit_terms[i].lit_idx;
            if (pre_lit_idx != tmp_lit_idx) {
                var_lit_num++;
                pre_lit_idx = tmp_lit_idx;
                v.literal_idxs.push_back(pre_lit_idx);
            }
        }
        v.literal_idxs.resize(var_lit_num);
    } // determine the lit_idxs of var
    var_in_long_term = new Array((int)_num_vars + (int)_additional_len);
    for (uint64_t term_idx = 0; term_idx < _terms.size(); term_idx++) {
        if (!term_appear[term_idx]) {
            continue;
        }
        t = &(_terms[term_idx]);
        std::sort(t->var_epxs.begin(), t->var_epxs.end(), cmp_ve);
        for (var_exp & ve : t->var_epxs) {
            _vars[ve.var_index].term_exps.push_back(term_exp(term_idx,ve.exponent));
            if (ve.exponent == 2) {
                // std::cout<<_vars[ve.var_index].var_name<<"\n";
                var_in_long_term->insert_element(ve.var_index);
            }
            if (ve.exponent >= 2) {
                has_high_coff = true;
            }
//            else if(ve.exponent>2){has_high_coff=true;}//no longer regard high coff as unsolvable
        }
        if (t->var_epxs.size() > 2) {
            for (var_exp & ve : t->var_epxs) {
                var_in_long_term->insert_element(ve.var_index);
            }
        }
    } // determine the term_idxs of vars
}

void ls_solver::make_space() {
    _num_opt *= 3;
    _solution.resize(5 * _num_vars + _additional_len);
    _best_solutin.resize(_num_vars + _additional_len);
    tabulist.resize(2 * _num_vars + _additional_len, 0);
    operation_var_idx_vec.resize(_num_opt + _additional_len);
    operation_var_idx_bool_vec.resize(_num_opt + _additional_len);
    operation_change_value_vec.resize(_num_opt + _additional_len);
    last_move.resize(2 * _num_vars + _additional_len, 0);
    unsat_clauses = new Array((int)_num_clauses + (int)_additional_len);
    sat_clause_with_false_literal = new Array((int)_num_clauses + (int)_additional_len);
    false_lit_occur = new Array((int)_num_lits + (int)_additional_len);
    contain_bool_unsat_clauses = new Array((int)_num_clauses);
    is_chosen_bool_var.resize(_num_vars + _additional_len, false);
    _lit_make_break.resize(_num_lits + _additional_len, 0);
    term_coffs.resize(_terms.size() + _additional_len, rational(0));
    low_bound_tight.resize(_num_vars + _additional_len, rational(INT32_MIN));
    up_bound_tight.resize(_num_vars + _additional_len, rational(INT32_MAX));
    low_bound_slack.resize(_num_vars + _additional_len, rational(INT32_MAX));
    up_bound_slack.resize(_num_vars + _additional_len, rational(INT32_MIN));
    vars_with_tight_bound = new Array((int)_num_vars + _additional_len);
    vars_with_slack_bound = new Array((int)_num_vars + _additional_len);
}

void ls_solver::set_pre_value() {
    _pre_value_1.resize(_num_vars + _additional_len, rational(INT32_MAX));
    _pre_value_2.resize(_num_vars + _additional_len, rational(INT32_MAX));
    has_only_pre_value.resize(_num_vars + _additional_len, false);
    for (clause & cl : _clauses) {
        if (cl.literals.size() == 1 && cl.literals[0] > 0 && _lits[cl.literals[0]].is_equal) {
            lit *l = &(_lits[cl.literals[0]]);
            if (l->coff_terms.size() == 1 && _terms[l->coff_terms[0].term_idx].var_epxs.size() == 1) {
                int var_idx = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                _pre_value_1[var_idx] = (-l->key/l->coff_terms[0].coff);
                has_only_pre_value[var_idx] = true;
            }
        } // (a==0)
        else if (cl.literals.size() == 2 && cl.literals[0] > 0 &&
                 _lits[cl.literals[0]].is_equal && cl.literals[1] > 0 && _lits[cl.literals[1]].is_equal) {
            lit *l1 = &(_lits[cl.literals[0]]);
            lit *l2 = &(_lits[cl.literals[1]]);
            if ((l1->coff_terms.size() == 1) && (l2->coff_terms.size() == 1)) {
                term *t_1 = &(_terms[l1->coff_terms[0].term_idx]);
                term *t_2 = &(_terms[l2->coff_terms[0].term_idx]);
                if (t_1->var_epxs.size() == 1 && t_2->var_epxs.size() == 1 &&
                    t_1->var_epxs[0].var_index == t_2->var_epxs[0].var_index) {
                    int var_idx = t_1->var_epxs[0].var_index;
                    _pre_value_1[var_idx] = (-l1->key / l1->coff_terms[0].coff);
                    _pre_value_2[var_idx] = (-l2->key / l2->coff_terms[0].coff);
                }
            }
        } // (a==0 OR a==1)
    }
    // if the gap between upper_bound and low_bound is limited, then the var is pre set
    for (int var_idx = 0; var_idx < _vars.size(); var_idx++) {
        variable *v = &(_vars[var_idx]);
        if (v->low_bound != -max_int && v->upper_bound != max_int && (v->upper_bound - v->low_bound) < min_ration) {
            _pre_value_1[var_idx] = mid_ration(v->upper_bound, v->low_bound);
            has_only_pre_value[var_idx] = true;
        }
    }
}
}
