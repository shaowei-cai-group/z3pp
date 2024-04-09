#include "nlsat/nlsat_local_search.h"
#include "util/heap.h"

/**
 * * local search for nlsat on nonlinear real arithmetic
*/

namespace nlsat {
    struct ls_helper::imp {
        /**
         * * Basic Manager
        */
        anum_manager                       &                 m_am;
        pmanager                           &                 m_pm;
        interval_set_manager               &                 m_ism;
        evaluator                          &                 m_evaluator;
        polynomial::cache                  &                 m_cache;
        solver                             &                 m_solver;

        /**
         * * Assignment
        */
        assignment                         &                 m_assignment;
        svector<lbool>                     &                 m_bvalues;

        /**
         * ^ Const Anum
         * ^ Zero: 0
         * ^ One: 1
         * ^ Delta: 1/max
         * ^ Max: INT_MAX
         */
        unsigned                                             m_threshold;
        unsigned                                             m_slack_threshold;
        anum                                                 m_zero, 
                                                             m_one, 
                                                             m_two, 
                                                             m_min,
                                                             m_slack_min,
                                                             m_slack_min2;

        /**
         * * Arith Var
         */
        nra_arith_var_vector                                 m_arith_vars;
        // ^ arith vars that are visited
        var_table                                            m_vars_visited;
        var_table                                            m_vars_visited2;
        
        /**
         * * Bool Var
         */
        nra_bool_var_vector                                  m_bool_vars;
        // ^ pure bool index --> atom index
        const bool_var_vector        &                       m_pure_bool_vars;
        // ^ atom index --> pure bool index
        const bool_var_vector        &                       m_pure_bool_convert;
        bool_var                                             m_max_bool_var;

        /**
         * * Literal
         */
        nra_literal_vector                                   m_nra_literals;
        var                                                  m_num_bool_literals;
        var                                                  m_num_arith_literals;
        
        literal_vector                                       m_literal_visited;
        // ^ used for set literal anum
        var_vector                                           m_literal_index_visited;
        // ^ store before sat information
        bool_vector                                          m_literal_before_sat;

        /**
         * Clause
         */
        const clause_vector                 &                m_clauses;
        nra_clause_vector                                    m_nra_clauses;

        /** 
         * * Used for init arith var's infeasible set
        */
        // only contain just one arith variable
        var_table                                            m_unit_var_clauses;
        // only contain one literal
        var_table                                            m_unit_clauses;

        // unsat clauses (index)
        var_vector                                           m_unsat_clauses;

        /**
         * * Weight
        */
        const unsigned                                       smooth_probability = 3;

        /**
         * Atoms
         */
        const atom_vector                &                   m_atoms;

        /**
         * Information
         */
        var                                                  m_num_vars;
        var                                                  m_num_bool_vars;
        var                                                  m_num_literals;
        var                                                  m_num_clauses;

        /**
         * Random
         */
        unsigned                                             m_rand_seed;
        random_gen                                           m_rand;


        /**
         * * improvement and restart
         */
        unsigned                                             m_best_found_restart;
        unsigned                                             no_improve_cnt;
        unsigned                                             m_restart_count;

        /**
         * * local search control
         */
        unsigned                                             m_step;
        const unsigned                                       max_step        =       UINT_MAX;
        bool                                                 use_infeasible_st;

        /**
         * * Time
        */
        std::chrono::steady_clock::time_point                m_start_time;
        int                                                  m_time_label;
        double                                               m_best_cost_time;
        double                                               m_cutoff;

        /**
         * * Operation
         */
        
        /**
         * * Statistics
        */
        const substitute_value_vector        &               m_sub_value;

        // Equations
        bool                                                 use_equal_slack;

        svector<svector<clause_index>>                       m_equal_clause_lsts;
        // Placeholder for empty clause vector
        svector<clause_index>                                m_empty_clause_lst;

        imp(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, svector<lbool> & bvalues, clause_vector const & cls, atom_vector const & ats, bool_var_vector const & pure_bool_vars, 
                         bool_var_vector const & pure_bool_convert, unsigned seed, 
                         substitute_value_vector const & vec)
        : m_am(am), m_pm(pm), m_ism(ism), m_evaluator(ev), m_assignment(ass), m_threshold(10), m_slack_threshold(10000),
        m_clauses(cls), m_atoms(ats), m_rand_seed(seed), m_solver(s), m_cutoff(1200),
        use_infeasible_st(true), m_restart_count(0),
        m_cache(cache), m_sub_value(vec), m_step(0),
        m_time_label(1), m_pure_bool_vars(pure_bool_vars), m_pure_bool_convert(pure_bool_convert), m_bvalues(bvalues),
        use_equal_slack(true)
        {
            set_const_anum();
        }

        ~imp() {
        }

        /**
         * * Initialize
         */
        void set_var_num(unsigned x){
            LSTRACE(tout << "set arith variable number: " << x << std::endl;
                std::cout << "start of set arith variable number\n";
            );
            m_num_vars = x;
            LSTRACE(display_vars(tout); display_clauses(tout););
            init_bool_vars();
            init_arith_vars();
            init_clauses();
            LSTRACE(tout << "end of set arith variable numbers" << std::endl;
                std::cout << "end of set arith variable number\n";
            );
        }

        /**
         * * fill in with pure bool vars
        */
        void init_bool_vars(){
            m_bool_vars.reset();
            m_num_bool_vars = m_pure_bool_vars.size();
            m_max_bool_var = m_pure_bool_vars.empty() ? null_var : m_pure_bool_vars.back();
            for(unsigned i = 0; i < m_num_bool_vars; i++) {
                // pure bool index, atom index
                m_bool_vars.push_back(new nra_bool_var(i, m_pure_bool_vars[i]));
            }
            LSTRACE(tout << "number of pure bool variables: " << m_num_bool_vars << std::endl;);
        }

        /**
         * * fill in with arith vars
        */
        void init_arith_vars(){
            m_arith_vars.reset();
            for(var v = 0; v < m_num_vars; v++){
                interval_set * curr_full = m_ism.mk_full();
                m_ism.inc_ref(curr_full);
                // m_ism.inc_ref(curr_empty);
                nra_arith_var * temp = new nra_arith_var(v, curr_full, nullptr);
                m_arith_vars.push_back(temp);
            }
        }

        void init_clauses(){
            LSTRACE(tout << "begin init clauses\n";);
            m_num_clauses = m_clauses.size();
            m_num_literals = 0;
            m_num_arith_literals = 0;
            m_num_bool_literals = 0;
            m_literal_visited.reset();
            m_nra_clauses.reset();
            m_nra_literals.reset();
            m_unit_var_clauses.reset();
            m_unit_clauses.reset();
            for(clause_index idx = 0; idx < m_clauses.size(); idx++){
                const clause & cls = *(m_clauses[idx]);
                LSTRACE(tout << "init clause "; m_solver.display(tout, cls); tout << std::endl;);
                nra_literal_vector curr_literals;
                var_table m_clause_vars;
                var_table m_clause_bool_vars;
                for(literal l: cls){
                    LSTRACE(tout << "pre-init literal "; m_solver.display(tout, l); tout << std::endl;);
                    literal_index lit_index = find_literal_vector(m_literal_visited, l);
                    nra_literal * m_literal;
                    if(lit_index == UINT_MAX){
                        // not register literal yet
                        init_literal(l);
                        m_literal = m_nra_literals.back();
                        lit_index = m_nra_literals.size() - 1;
                    }
                    else {
                        // registered literal
                        LSTRACE(tout << "already registered\n";);
                        SASSERT(m_nra_literals.size() > lit_index);
                        SASSERT(m_nra_literals[lit_index]->get_literal() == m_literal_visited[lit_index]);
                        m_literal = m_nra_literals[lit_index];
                    }
                    curr_literals.push_back(m_literal);
                    // bool literal
                    if(m_literal->is_bool()){
                        LSTRACE(tout << "bool literal, collect info for bool variables\n";);
                        SASSERT(m_literal->m_vars.empty());
                        bool_var b = m_literal->get_bool_index();
                        SASSERT(b != null_var);
                        nra_bool_var * b_var = m_bool_vars[b];
                        if(!m_clause_bool_vars.contains(b)){
                            m_clause_bool_vars.insert(b);
                            b_var->add_clause(idx);
                        }
                        b_var->add_literal_clause(lit_index, idx);
                        LSTRACE(tout << "bool var: " << b << std::endl;
                            tout << "bool literals: "; display_literal_set(tout, b_var->m_literals);
                            tout << std::endl;
                            tout << "bool lit_cls: \n"; display_clause_set(tout, b_var->m_lit_cls);
                            tout << std::endl;
                        );
                    }
                    else {
                        // loop arith var
                        LSTRACE(tout << "arith literal, collect info for arith variables\n";);
                        for(var v: m_literal->m_vars){
                            // LSTRACE(tout << "show size: " << m_arith_vars.size() << std::endl;);
                            if(!m_clause_vars.contains(v)){
                                m_clause_vars.insert(v);
                                m_arith_vars[v]->add_clause(idx);
                            }
                            m_arith_vars[v]->add_literal_clause(lit_index, idx);
                            LSTRACE(tout << "collect arith var " << v << " succeed\n";);
                        }
                    }
                }
                nra_clause * temp_clause = new nra_clause(idx, m_clauses[idx], curr_literals, m_clause_vars, m_clause_bool_vars);
                m_nra_clauses.push_back(temp_clause);
                // only one arith var and no bool literal
                if(m_clause_vars.size() == 1 && temp_clause->bool_size() == 0){
                    m_unit_var_clauses.insert(idx);
                    // var cls_var = *m_clause_vars.begin();
                    var cls_var = null_var;
                    for(var v: m_clause_vars){
                        cls_var = v;
                    }
                    SASSERT(cls_var != null_var);
                    nra_arith_var * curr_var = m_arith_vars[cls_var];
                    // curr_st = /\. st, stands for infeasible set of a variable
                    interval_set_ref curr_st(m_ism);
                    curr_st = m_ism.mk_full();
                    for(literal_index l_idx: temp_clause->m_literals){
                        nra_literal const * loop_literal = m_nra_literals[l_idx];
                        SASSERT(loop_literal->is_arith());
                        SASSERT(loop_literal->m_vars.size() == 1 && loop_literal->m_vars[0] == cls_var);
                        // we get infeasible set
                        interval_set_ref loop_st(m_ism);
                        loop_st = m_evaluator.infeasible_intervals(loop_literal->get_atom(), loop_literal->sign(), temp_clause->get_clause(), cls_var);
                        curr_st = m_ism.mk_intersection(curr_st, loop_st);
                    }
                    // infeasible set --> feasible set
                    curr_st = m_ism.mk_complement(curr_st);
                    // intersect feasible set
                    curr_var->m_feasible_st = m_ism.mk_intersection(curr_var->m_feasible_st, curr_st);
                }
                // only one literal
                if(temp_clause->size() == 1){
                    m_unit_clauses.insert(idx);
                }
                LSTRACE(tout << "end of this clause\n";);
            }
            LSTRACE(tout << "end of init clauses\n";);
            init_arith_infeasible_set();
            LSTRACE(tout << "show arith var's feasible set:\n";
                display_arith_intervals(tout);
            );
        }

        void init_arith_infeasible_set(){
            for (var v = 0; v < m_arith_vars.size(); v++) {
                nra_arith_var * curr = m_arith_vars[v];
                curr->m_infeasible_st = m_ism.mk_complement(curr->m_feasible_st);
                if (curr->m_infeasible_st != nullptr) {
                    m_ism.inc_ref(curr->m_infeasible_st);
                }
            }
        }

        void init_literal(literal l){
            LSTRACE(tout << "init literal "; m_solver.display(tout, l); tout << std::endl;);
            bool is_bool = is_bool_literal(l);
            // bool literal: pure bool index
            // arith literal: null_var
            bool_var b_idx = is_bool ? m_pure_bool_convert[l.var()] : null_var;
            literal_index m_index = m_nra_literals.size();
            var_table m_vars;
            get_literal_vars(l, m_vars);
            LSTRACE(tout << "show literal vars: "; display_var_table(tout, m_vars); tout << std::endl;);
            nra_literal * temp = new nra_literal(m_index, b_idx, l, is_bool, m_vars, m_atoms[l.var()]);
            // LSCTRACE(m_atoms[l.var()] != nullptr,
            //     tout << "show literal atom:\n";
            //     m_solver.display(tout, *(temp->get_atom()));
            // );
            m_nra_literals.push_back(temp);
            m_literal_visited.push_back(l);
            m_num_literals++;
            if(is_bool){
                m_num_bool_literals++;
            }
            else {
                m_num_arith_literals++;
            }
            SASSERT(m_nra_literals.size() == m_literal_visited.size());
            LSTRACE(tout << "end of init literal\n";);
        }

        void init_arith_var_info() {
            // For each arith variable, compute the current infeasible set
            // for each clause and literal it appears in
            for (var v = 0; v < m_arith_vars.size(); v++){
                compute_arith_var_info(v);
                compute_boundary(v);
            }
        }

        void compute_arith_var_info(var v) {
            // Compute infeasible set information for variable
            interval_set_ref result_st(m_ism);
            interval_set_ref curr_st(m_ism);

            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                clause_index c_idx = m_arith_var->m_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                result_st = m_ism.mk_full();
                for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                    literal_index l_idx = curr_clause->m_arith_literals[j];
                    nra_literal * curr_literal = m_nra_literals[l_idx];
                    if (!curr_literal->m_vars.contains(v)) {
                        continue;
                    }
                    // std::cout << "clause " << c_idx << " literal " << l_idx << std::endl;
                    if (curr_literal->is_slacked()) {
                        const ineq_atom * left_atom = curr_literal->get_left_atom();
                        const ineq_atom * right_atom = curr_literal->get_right_atom();
                        if (left_atom != nullptr && right_atom != nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(left_atom, !curr_literal->sign(), nullptr, v);
                            curr_st = m_ism.mk_union(curr_st, m_evaluator.infeasible_intervals(right_atom, !curr_literal->sign(), nullptr, v));
                        } else if (left_atom == nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(right_atom, curr_literal->sign(), nullptr, v);
                        } else if (right_atom == nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(left_atom, curr_literal->sign(), nullptr, v);
                        } else {
                            UNREACHABLE();
                        }
                    } else {
                        curr_st = m_evaluator.infeasible_intervals(curr_literal->get_atom(), curr_literal->sign(), nullptr, v);
                    }
                    result_st = m_ism.mk_intersection(result_st, curr_st);
                }
                if (m_arith_var->m_clause_intervals[i] != nullptr) {
                    m_ism.dec_ref(m_arith_var->m_clause_intervals[i]);
                }
                m_arith_var->m_clause_intervals[i] = result_st;
                if (result_st != nullptr) {
                    m_ism.inc_ref(result_st);
                }
            }
        }

        void compute_arith_var_clause_info(var v, clause_index c_idx, bool set_flag) {
            // Compute infeasible set information for variable
            interval_set_ref result_st(m_ism);
            interval_set_ref curr_st(m_ism);

            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                if (c_idx != m_arith_var->m_clauses[i]) {
                    continue;
                }
                if (set_flag) {
                    m_arith_var->m_clause_intervals_flag[i] = true;
                    continue;
                }
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                result_st = m_ism.mk_full();
                for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                    literal_index l_idx = curr_clause->m_arith_literals[j];
                    nra_literal * curr_literal = m_nra_literals[l_idx];
                    if (!curr_literal->m_vars.contains(v)) {
                        continue;
                    }
                    // std::cout << "clause " << c_idx << " literal " << l_idx << std::endl;
                    if (curr_literal->is_slacked()) {
                        const ineq_atom * left_atom = curr_literal->get_left_atom();
                        const ineq_atom * right_atom = curr_literal->get_right_atom();
                        if (left_atom != nullptr && right_atom != nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(left_atom, !curr_literal->sign(), nullptr, v);
                            curr_st = m_ism.mk_union(curr_st, m_evaluator.infeasible_intervals(right_atom, !curr_literal->sign(), nullptr, v));
                        } else if (left_atom == nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(right_atom, curr_literal->sign(), nullptr, v);
                        } else if (right_atom == nullptr) {
                            curr_st = m_evaluator.infeasible_intervals(left_atom, curr_literal->sign(), nullptr, v);
                        } else {
                            UNREACHABLE();
                        }
                    } else {
                        curr_st = m_evaluator.infeasible_intervals(curr_literal->get_atom(), curr_literal->sign(), nullptr, v);
                    }
                    result_st = m_ism.mk_intersection(result_st, curr_st);
                }
                if (m_arith_var->m_clause_intervals[i] != nullptr) {
                    m_ism.dec_ref(m_arith_var->m_clause_intervals[i]);
                }
                m_arith_var->m_clause_intervals[i] = result_st;
                if (result_st != nullptr) {
                    m_ism.inc_ref(result_st);
                }
            }
        }

        void compute_boundary(var v) {
            // Compute boundary information for variable
            // std::cout << "compute boundary for " << v << std::endl;
            nra_arith_var * m_arith_var = m_arith_vars[v];
            m_arith_var->m_start_score = 0;
            m_arith_var->m_boundaries.reset();

            // If variable has infeasible set, add it with large weight
            if (use_infeasible_st) {
                if (m_arith_var->m_infeasible_st != nullptr) {
                    m_ism.add_boundaries(m_arith_var->m_infeasible_st, m_arith_var->m_boundaries,
                                         m_arith_var->m_start_score, INT_MAX / 2, UINT_MAX);
                }
            }

            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                clause_index c_idx = m_arith_var->m_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];

                // std::cout << "clause " << c_idx << " weight " << curr_clause->get_weight() << std::endl;
                unsigned before_sat_count = curr_clause->get_sat_count();

                interval_set const * s = m_arith_var->m_clause_intervals[i];
                if (s == nullptr) {
                    continue;
                }
                if (before_sat_count > 0) {
                    // Potential break case, test whether some other literals are true
                    bool always_sat = false;
                    for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                        literal_index l_idx = curr_clause->m_arith_literals[j];
                        nra_literal * curr_literal = m_nra_literals[l_idx];
                        if (curr_literal->get_sat_status() && !curr_literal->m_vars.contains(v)) {
                            always_sat = true;
                        }
                    }
                    for (unsigned j = 0; j < curr_clause->m_bool_literals.size(); j++) {
                        literal_index l_idx = curr_clause->m_bool_literals[j];
                        nra_literal * curr_literal = m_nra_literals[l_idx];
                        if (curr_literal->get_sat_status()) {
                            always_sat = true;
                        }
                    }
                    if (always_sat) {
                        continue;
                    }
                    // break case: infeasible intervals decrease score by 1
                    // std::cout << "break" << std::endl;
                    // m_ism.display(std::cout, s);
                    // std::cout << std::endl;
                    m_ism.add_boundaries(s, m_arith_var->m_boundaries, m_arith_var->m_start_score, curr_clause->get_weight(), c_idx);
                }

                if (before_sat_count == 0) {
                    // make case: feasible intervals increase score by 1
                    // std::cout << "make" << std::endl;
                    // m_ism.display(std::cout, s);
                    // std::cout << std::endl;
                    m_arith_var->m_start_score += curr_clause->get_weight();
                    m_ism.add_boundaries(s, m_arith_var->m_boundaries, m_arith_var->m_start_score, curr_clause->get_weight(), c_idx);
                }
            }
            std::sort(m_arith_var->m_boundaries.begin(), m_arith_var->m_boundaries.end(), lt_anum_boundary(m_am));
            // int score = m_arith_var->m_start_score;
            // std::cout << "start " << score << std::endl;
            // for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
            //     score += m_arith_var->m_boundaries[j].score;
            //     m_am.display(std::cout, m_arith_var->m_boundaries[j].value);
            //     std::cout << " " << m_arith_var->m_boundaries[j].is_open << " " << score << std::endl;
            // }
        }

        int get_best_arith_score(var v) {
            // Obtain the best score for variable v. Scores less than INT_MIN / 4
            // must be due to infeasible set of a variable, and hence discarded.
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            if (m_arith_var->m_boundaries.size() == 0) {
                return INT_MIN;
            }
            int best_score = score;
            for (unsigned i = 0; i < m_arith_var->m_boundaries.size(); i++) {
                score += m_arith_var->m_boundaries[i].score;
                if (score > best_score) {
                    best_score = score;
                }
            }
            if (best_score < INT_MIN / 4) {
                return INT_MIN;
            }
            return best_score;
        }

        bool contains_value(interval_set const * s, anum const & val) {
            // Whether interval set s contains val.
            interval_set_ref pt_val(m_ism);
            pt_val = m_ism.mk_point_interval(val);
            return m_ism.subset(pt_val, s);
        }

        void get_denominator(anum const & val, mpq & den) {
            scoped_mpq rat(m_am.qm());
            m_am.to_rational(val, rat);
            m_am.qm().get_denominator(rat, den);
        }

        bool lt_denominator(anum const & val1, anum const & val2) {
            scoped_mpq den1(m_am.qm());
            scoped_mpq den2(m_am.qm());
            get_denominator(val1, den1);
            get_denominator(val2, den2);
            return m_am.qm().lt(den1, den2);
        }

        bool is_rational(anum const & val) {
            return m_am.degree(val) <= 1;
        }

        bool is_int(anum const & val) {
            return is_rational(val) && m_am.is_int(val);
        }

        bool is_simpler(anum const & val1, anum const & val2) {
            // Return whether val2 is simpler than val1
            if (is_rational(val1) && !is_rational(val2)) {
                return false;
            } else if (!is_rational(val1) && is_rational(val2)) {
                return true;
            } else if (!is_rational(val1) && !is_rational(val2)) {
                return false;  // cannot compare
            } else if (lt_denominator(val1, m_slack_min2) && lt_denominator(val2, m_slack_min2)) {
                return false;  // does not compare denominator when less than 10
            } else {
                return lt_denominator(val2, val1);
            }
        }

        unsigned get_simplest_index(anum_vector & vs) {
            // Return the index in vs with "simplest" number. Ties are
            // broken by chance.
            vector<int> best_indices = vector<int>();
            best_indices.push_back(0);
            for (int i = 1; i < vs.size(); i++) {
                if (is_simpler(vs[best_indices[0]], vs[i])) {
                    best_indices.reset();
                    best_indices.push_back(i);
                } else if (!is_simpler(vs[i], vs[best_indices[0]])) {
                    best_indices.push_back(i);
                }
            }
            return best_indices[rand_int() % best_indices.size()];
        }

        void int_lt(anum const & a, anum & b) {
            m_am.int_lt(a, b);
            scoped_anum diff(m_am);
            m_am.sub(a, b, diff);
            if (m_am.lt(m_one, diff)) {
                m_am.add(b, m_one, b);
            }
        }

        void int_gt(anum const & a, anum & b) {
            m_am.int_gt(a, b);
            scoped_anum diff(m_am);
            m_am.sub(b, a, diff);
            if (m_am.lt(m_one, diff)) {
                m_am.sub(b, m_one, b);
            }
        }

        void get_best_arith_value(var v, int best_score, anum & best_value, svector<clause_index> & equation_idx) {
            // Obtain the best value for variable v (where the best score is known)
            SASSERT(best_score != INT_MIN);
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            int len = m_arith_var->m_boundaries.size();
            scoped_anum_vector vec(m_am);
            m_equal_clause_lsts.reset();
            if (score == best_score) {
                // Return value before left boundary
                if (m_arith_var->m_boundaries[0].is_open) {
                    // x] case, can include x
                    scoped_anum w(m_am);
                    if (is_int(m_arith_var->m_boundaries[0].value)) {
                        m_am.set(w, m_arith_var->m_boundaries[0].value);
                    } else {
                        int_lt(m_arith_var->m_boundaries[0].value, w);
                    }
                    vec.push_back(w);
                    m_equal_clause_lsts.push_back(m_empty_clause_lst);
                }
                else {
                    // x) case, cannot include x
                    scoped_anum w(m_am);
                    int_lt(m_arith_var->m_boundaries[0].value, w);
                    vec.push_back(w);
                    m_equal_clause_lsts.push_back(m_empty_clause_lst);
                }
            }
            for (unsigned i = 0; i < len; i++) {
                score += m_arith_var->m_boundaries[i].score;
                if (score == best_score) {
                    // Return value after right boundary
                    if (i == len - 1) {
                        if (m_arith_var->m_boundaries[len-1].is_open) {
                            // x] case, cannot include x
                            scoped_anum w(m_am);
                            int_gt(m_arith_var->m_boundaries[len-1].value, w);
                            vec.push_back(w);
                            m_equal_clause_lsts.push_back(m_empty_clause_lst);
                        }
                        else {
                            // x) case, can include x
                            scoped_anum w(m_am);
                            if (is_int(m_arith_var->m_boundaries[len-1].value)) {
                                m_am.set(w, m_arith_var->m_boundaries[len-1].value);
                            } else {
                                int_gt(m_arith_var->m_boundaries[len-1].value, w);
                            }
                            vec.push_back(w);
                            m_equal_clause_lsts.push_back(m_empty_clause_lst);
                        }
                    }
                    // Return value in the middle
                    else {
                        if (m_am.eq(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value)) {
                            SASSERT(!m_arith_var->m_boundaries[i].is_open && m_arith_var->m_boundaries[i+1].is_open);
                            scoped_anum w(m_am);
                            m_am.set(w, m_arith_var->m_boundaries[i].value);
                            vec.push_back(w);
                            svector<clause_index> cur_clauses;
                            for (unsigned cls_idx : m_arith_var->m_boundaries[i].m_clauses) {
                                if (!cur_clauses.contains(cls_idx)) {
                                    cur_clauses.push_back(cls_idx);
                                }
                            }
                            for (unsigned cls_idx : m_arith_var->m_boundaries[i+1].m_clauses) {
                                if (!cur_clauses.contains(cls_idx)) {
                                    cur_clauses.push_back(cls_idx);
                                }
                            }
                            m_equal_clause_lsts.push_back(cur_clauses);
                        }
                        else {
                            scoped_anum w(m_am);
                            m_am.select(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value, w);
                            vec.push_back(w);
                            m_equal_clause_lsts.push_back(m_empty_clause_lst);
                        }
                    }
                }
            }
            SASSERT(vec.size() > 0);
            unsigned id = get_simplest_index(vec);
            SASSERT(id >= 0 && id < vec.size());
            m_am.set(best_value, vec[id]);
            equation_idx.reset();
            for (unsigned cls_idx : m_equal_clause_lsts[id]) {
                equation_idx.push_back(cls_idx);
            }
            return;
        }

        bool get_best_arith_value_clause(var v, anum & best_value, clause_index c_idx, int & best_score) {
            // Obtain the best value for variable v, subject to the condition that
            // it is outside the infeasible interval of clause c_idx.
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            int len = m_arith_var->m_boundaries.size();
            scoped_anum_vector vec(m_am);
            vector<int> scores = vector<int>();

            interval_set * s = nullptr;
            for (int i = 0; i < m_arith_var->m_clauses.size(); i++) {
                if (c_idx == m_arith_var->m_clauses[i]) {
                    s = m_arith_var->m_clause_intervals[i];
                }
            }
            if (m_ism.is_full(s)) {
                return false;
            }

            // Return value before left boundary
            if (m_arith_var->m_boundaries[0].is_open) {
                // x] case, can include x
                scoped_anum w(m_am);
                if (is_int(m_arith_var->m_boundaries[0].value)) {
                    m_am.set(w, m_arith_var->m_boundaries[0].value);
                } else {
                    int_lt(m_arith_var->m_boundaries[0].value, w);
                }
                if (!contains_value(s, w) && score >= INT_MIN / 4) {
                    if (score > best_score) {
                        best_score = score;
                        scores.reset();
                        vec.reset();
                    }
                    scores.push_back(score);
                    vec.push_back(w);
                }
            }
            else {
                // x) case, cannot include x
                scoped_anum w(m_am);
                int_lt(m_arith_var->m_boundaries[0].value, w);
                if (!contains_value(s, w) && score >= INT_MIN / 4) {
                    if (score > best_score) {
                        best_score = score;
                        scores.reset();
                        vec.reset();
                    }
                    scores.push_back(score);
                    vec.push_back(w);
                }
            }

            for (unsigned i = 0; i < len; i++) {
                score += m_arith_var->m_boundaries[i].score;
                // Return value after right boundary
                if (i == len - 1) {
                    if (m_arith_var->m_boundaries[len-1].is_open) {
                        // x] case, cannot include x
                        scoped_anum w(m_am);
                        int_gt(m_arith_var->m_boundaries[len-1].value, w);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                        }
                    }
                    else {
                        // x) case, can include x
                        scoped_anum w(m_am);
                        if (is_int(m_arith_var->m_boundaries[len-1].value)) {
                            m_am.set(w, m_arith_var->m_boundaries[len-1].value);
                        } else {
                            int_gt(m_arith_var->m_boundaries[len-1].value, w);
                        }
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                        }
                    }
                }
                // Return value in the middle
                else {
                    if (m_am.eq(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value)) {
                        SASSERT(!m_arith_var->m_boundaries[i].is_open && m_arith_var->m_boundaries[i+1].is_open);
                        scoped_anum w(m_am);
                        m_am.set(w, m_arith_var->m_boundaries[i].value);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                        }
                    }
                    else {
                        scoped_anum w(m_am);
                        m_am.select(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value, w);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                        }
                    }
                }
            }
            if (vec.size() == 0) {
                return false;
            }
            unsigned id = get_simplest_index(vec);
            SASSERT(id >= 0 && id < vec.size());
            m_am.set(best_value, vec[id]);
            best_score = scores[id];
            // int r = rand_int() % vec.size();
            // best_value = vec[r];
            // best_score = scores[r];
            SASSERT(best_score >= INT_MIN / 4);
            return true;
        }

        int get_arith_score(var v, anum const & new_value) {
            // Obtain score from the index for updating variable v to new value
            nra_arith_var * m_arith_var = m_arith_vars[v];
            // std::cout << "query var " << v << " at value ";
            // m_am.display(std::cout, new_value);
            // std::cout << std::endl;
            int score;
            // score = m_arith_var->m_start_score;
            // std::cout << "start " << score << std::endl;
            // for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
            //     score += m_arith_var->m_boundaries[j].score;
            //     m_am.display(std::cout, m_arith_var->m_boundaries[j].value);
            //     std::cout << " " << m_arith_var->m_boundaries[j].is_open << " " << score << std::endl;
            // }
            score = m_arith_var->m_start_score;
            for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
                if (m_am.lt(new_value, m_arith_var->m_boundaries[j].value)) {
                    return score;
                }
                if (m_am.eq(new_value, m_arith_var->m_boundaries[j].value) && m_arith_var->m_boundaries[j].is_open) {
                    return score;
                }
                score += m_arith_var->m_boundaries[j].score;
            }
            return score;
        }

        bool is_var_all_sat(var v) {
            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (clause_index c_idx : m_arith_var->m_clauses) {
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                if (!curr_clause->get_sat_status()) {
                    return false;
                }
            }
            return true;
        }

        void update_arith_score(var v, anum const & new_value) {
            // Update score in response to updating variable v to new value
            // We assume that satisfiability of clauses (and literals in it) has already
            // been updated. Loop over variables that share a clause with v.
            m_vars_visited.reset();
            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (clause_index c_idx : m_arith_var->m_clauses) {
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                // Update for each variable in that clause
                for (auto it = curr_clause->m_vars.begin(); it != curr_clause->m_vars.end(); it++) {
                    var v2 = *it;
                    bool is_all_sat = is_var_all_sat(v2);
                    compute_arith_var_clause_info(v2, c_idx, is_all_sat);
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                var v2 = *it;
                if (!is_var_all_sat(v2)) {
                    nra_arith_var * m_arith_var2 = m_arith_vars[v2];
                    for (unsigned j = 0; j < m_arith_var2->m_clauses.size(); j++) {
                        if (m_arith_var2->m_clause_intervals_flag[j]) {
                            compute_arith_var_clause_info(v2, m_arith_var2->m_clauses[j], false);
                            m_arith_var2->m_clause_intervals_flag[j] = false;
                        }
                    }
                }
                compute_boundary(*it);
            }
        }

        void update_bool_score(bool_var b) {
            // Update score in response to flipping boolean variable
            m_vars_visited.reset();
            nra_bool_var * m_bool_var = m_bool_vars[b];
            for (clause_index c_idx : m_bool_var->m_clauses) {
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                // Update for each variable in that clause
                for (auto it = curr_clause->m_vars.begin(); it != curr_clause->m_vars.end(); it++) {
                    var v2 = *it;
                    bool is_all_sat = is_var_all_sat(v2);
                    compute_arith_var_clause_info(v2, c_idx, is_all_sat);
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                var v2 = *it;
                if (!is_var_all_sat(v2)) {
                    nra_arith_var * m_arith_var2 = m_arith_vars[v2];
                    for (unsigned j = 0; j < m_arith_var2->m_clauses.size(); j++) {
                        if (m_arith_var2->m_clause_intervals_flag[j]) {
                            compute_arith_var_clause_info(v2, m_arith_var2->m_clauses[j], false);
                            m_arith_var2->m_clause_intervals_flag[j] = false;
                        }
                    }
                }
                compute_boundary(*it);
            }
        }

        /**
         * Init Solution
         */
        // false means ICP returns unsat
        // only ICP for the first initialize
        bool init_solution(bool first_init){
            LSTRACE(tout << "start of init solution\n";);
            if(!construct_assignment(first_init)){
                return false;
            }
            init_literals_delta();
            init_clauses_delta();
            m_best_found_restart = m_num_clauses;
            update_solution_info();
            init_arith_var_info();
            LSTRACE(tout << "end of init solution\n";
                display_unsat_clauses(tout);
            );
            return true;
        }

        // first init: ICP
        bool construct_assignment(bool first_init){
            return first_init ? init_assignment() : restart_assignment();
        }

        // ^ construct assignment for the first time
        bool init_assignment() {
            LSTRACE(tout << "start of init assignment\n";);
            m_assignment.reset();
            // bool vars set all true
            for(bool_var b = 0; b < m_num_bool_vars; b++){
                m_bool_vars[b]->set_value(true);
            }
            // arith vars set zero or other
            for(var v = 0; v < m_num_vars; v++){
                nra_arith_var const * curr_arith = m_arith_vars[v];
                // infeasible set full, ICP returns false
                if(m_ism.is_full(curr_arith->m_infeasible_st)){
                    return false;
                }
                LSTRACE(tout << "var " << v << ", "; m_ism.display(tout, curr_arith->m_feasible_st); tout << std::endl;);

                if (contains_value(curr_arith->m_feasible_st, m_zero)){
                    LSTRACE(tout << "set zero\n";);
                    m_assignment.set(v, m_zero);
                }
                else {
                    LSTRACE(tout << "not zero\n";);
                    scoped_anum w(m_am);
                    m_ism.peek_in_complement(curr_arith->m_infeasible_st, false, w, true);
                    m_assignment.set(v, w);
                }
            }
            LSTRACE(tout << "end of init assignment\n";
                show_ls_assignment(tout);
            );
            return true;
        }

        // ^ construct assignment when restarting
        bool restart_assignment() {
            if(m_unsat_clauses.empty()){
                return true;
            }
            clause_index curr_index = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * curr_clause = m_nra_clauses[curr_index];
            SASSERT(curr_clause->size() > 0);
            literal_index l_idx = curr_clause->m_literals[rand_int() % curr_clause->size()];
            nra_literal const * curr_l = m_nra_literals[l_idx];
            if(curr_l->is_bool()){
                return true;
            }
            SASSERT(!curr_l->m_vars.empty());
            for(var v: curr_l->m_vars){
                nra_arith_var const * curr_arith = m_arith_vars[v];
                scoped_anum w(m_am), old_value(m_am);
                m_am.set(old_value, m_assignment.value(v));
                interval_set_ref old_value_interval(m_ism);
                // [old_value, old_value]
                old_value_interval = m_ism.mk_point_interval(old_value);
                interval_set_ref curr_st(m_ism);
                curr_st = m_ism.mk_union(old_value_interval, curr_arith->m_infeasible_st);
                // happens for ==
                if(!m_ism.is_full(curr_st)){
                    m_ism.peek_in_complement(curr_st, false, w, true);
                    critical_nra_move(v, w);
                    return true;
                }
            }
            return true;
        }

        void init_literals_delta(){
            LSTRACE(tout << "start of init literals delta\n";);
            for(literal_index i = 0; i < m_num_literals; i++){
                set_literal_anum(m_nra_literals[i]);
            }
            LSTRACE(tout << "end of init literals delta\n";);
        }

        void init_clauses_delta(){
            LSTRACE(tout << "start of init clauses delta\n";);

            m_unsat_clauses.reset();
            for(clause_index i = 0; i < m_num_clauses; i++){
                update_clause_delta(m_nra_clauses[i]);
            }
            LSTRACE(tout << "end of init clauses delta\n";
                display_unsat_clauses(tout);
            );
        }

        bool update_solution_info(){
            bool improved = false;
            if(m_unsat_clauses.size() < m_best_found_restart){
                improved = true;
                m_best_found_restart = m_unsat_clauses.size();
                m_best_cost_time = TimeElapsed();
            }
            return improved;
        }

        /**
         * Get Variables
         */
        void get_literal_vars(literal l, var_table & vars){
            vars.reset();
            if(is_bool_literal(l)){
                return;
            }
            ineq_atom * aa = to_ineq_atom(m_atoms[l.var()]);
            for(unsigned i = 0; i < aa->size(); i++){
                var_vector curr;
                poly * p = aa->p(i);
                m_pm.vars(p, curr);
                for(var v: curr){
                    if(!vars.contains(v)){
                        vars.insert(v);
                    }
                }
            }
        }

        /**
         * Set delta anum for literal
         */
        void set_literal_anum(nra_literal * l){
            // LSTRACE(tout << "start of set literal anum for "; m_solver.display(tout, l->m_literal); tout << std::endl;
            //     show_ls_assignment(tout);
            // );
            // std::cout << "start of set literal anum for "; m_solver.display(std::cout, l->m_literal); std::cout << std::endl;
            // std::cout << "start set_literal_anum" << std::endl;
            if(l->is_bool()){
                bool sat_status = is_bool_sat(l);
                l->set_sat_status(sat_status);
            }
            else {
                // we use evaluator's eval to check satisfiability of arith literals
                // checking sign of multi-poly is faster then getting accurate value
                if (l->is_slacked()) {
                    // std::cout << "eval is slacked" << std::endl;
                    ineq_atom * left_atom = (ineq_atom *) (l->get_left_atom());
                    ineq_atom * right_atom = (ineq_atom *) (l->get_right_atom());
                    // m_solver.display(std::cout, *left_atom); std::cout << std::endl;
                    // m_solver.display(std::cout, *right_atom); std::cout << std::endl;
                    if (left_atom != nullptr && right_atom != nullptr) {
                        if (l->sign()) {
                            UNREACHABLE();
                        } 
                        l->set_sat_status(m_evaluator.eval(left_atom, !l->sign()) &&
                                          m_evaluator.eval(right_atom, !l->sign()));
                    } else if (left_atom == nullptr) {
                        if (!l->sign()) {
                            UNREACHABLE();
                        }
                        l->set_sat_status(m_evaluator.eval(right_atom, l->sign()));
                    } else if (right_atom == nullptr) {
                        if (!l->sign()) {
                            UNREACHABLE();
                        }
                        l->set_sat_status(m_evaluator.eval(left_atom, l->sign()));
                    } else {
                        UNREACHABLE();
                    }
                    // bool left_sat = (left_atom == nullptr || m_evaluator.eval(left_atom, !l->sign()));
                    // bool right_sat = (right_atom == nullptr || m_evaluator.eval(right_atom, !l->sign()));
                    // l->set_sat_status(left_sat && right_sat);
                } else {
                    l->set_sat_status(m_evaluator.eval((atom *) (l->get_atom()), l->sign()));
                }
            }
            // std::cout << "end set_literal_anum" << std::endl;
            // LSTRACE(tout << "end of set literal anum\n";);
        }


        void update_clause_delta(nra_clause * cls){
            LSTRACE(tout << "start of update clause delta for: "; m_solver.display(tout, *cls->get_clause()); tout << std::endl;);
            unsigned sat_count = 0;

            for(literal_index lit_index: cls->m_literals){
                nra_literal * curr_literal = m_nra_literals[lit_index];
                LSTRACE(tout << "loop literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;);
                if(curr_literal->get_sat_status()){
                    LSTRACE(tout << "sat literal\n";);
                    sat_count++;
                }
            }
            cls->set_sat_count(sat_count);
            LSTRACE(tout << "sat count: " << sat_count << std::endl;);
            if(sat_count > 0){
                sat_clause(cls);
                LSTRACE(tout << "satisfy\n";);
            }
            else {
                unsat_clause(cls);
                LSTRACE(tout << "unsatisfy\n";);
            }
            LSTRACE(display_clause_info(tout, cls););
            LSTRACE(tout << "end of update clause delta\n";);
        }

        /**
         * Sat
         */
        bool is_bool_sat(nra_literal const * l) const {
            SASSERT(l->is_bool());
            SASSERT(l->get_bool_index() != null_var);
            nra_bool_var * b = m_bool_vars[l->get_bool_index()];
            return l->sign() != b->get_value();
        }

        void set_const_anum(){
            m_am.set(m_zero, 0);
            m_am.set(m_one, 1);
            m_am.set(m_two, 2);
            // We primarily use m_min as a threshold for comparing denominators.
            // If two numbers have denominators smaller than that of m_min, they
            // are not distinguished in the comparison.
            scoped_anum threshold(m_am);
            m_am.set(threshold, m_threshold);
            m_am.div(m_one, threshold, m_min);
            scoped_anum slack_threshold(m_am);
            m_am.set(slack_threshold, m_slack_threshold);
            m_am.div(m_one, slack_threshold, m_slack_min);
            m_am.set(m_slack_min2, m_slack_min);
        }

        /**
         * Util
         */
        double TimeElapsed() {
            auto finish = std::chrono::steady_clock::now();
            std::chrono::duration<double> dura = finish - m_start_time;
            double res = dura.count();
            LSTRACE(tout << "Time Elapsed: " << res << std::endl;
                tout << "m_time_label: " << m_time_label << std::endl;
                std::cout << "elapsed: " << res << " s" << std::endl;
            );
            int curr_floor = floor(res);
            if(curr_floor >= m_time_label){
                // LSTRACE(std::cout << "Flow: " << curr_floor << " s" << std::endl;);
                m_time_label = curr_floor + 1;
            }
            return res;
        }

        var random_table(var_table const & vars) {
            if(vars.empty()){
                return null_var;
            }
            var res = null_var;
            unsigned count = 1;
            for(auto it = vars.begin(); it != vars.end(); it++){
                // 1/count to replace
                if(rand_int() % count == 0){
                    res = *it;
                }
                count++;
            }
            return res;
        }

        unsigned find_index_vector(var_vector const & vars, var v) const {
            for(unsigned i = 0; i < vars.size(); i++){
                if(vars[i] == v){
                    return i;
                }
            }
            return null_var;
        }

        unsigned rand_int(){
            return m_rand();
        }

        void sat_clause(nra_clause * cls){
            cls->set_sat_status(true);
            clause_index m_index = cls->get_index();
            m_unsat_clauses.erase(m_index);
        }

        void unsat_clause(nra_clause * cls){
            cls->set_sat_status(false);
            clause_index m_index = cls->get_index();
            m_unsat_clauses.insert(m_index);
        }

        bool is_bool_literal(literal l) const {
            return m_atoms[l.var()] == nullptr;
        }

        bool is_arith_literal(literal l) const {
            return !is_bool_literal(l);
        }

        unsigned find_literal_vector(literal_vector const & vec, literal l) const {
            for(unsigned i = 0; i < vec.size(); i++){
                if(vec[i] == l){
                    return i;
                }
            }
            return UINT_MAX;
        }

        void collect_bool_values(){
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                m_bvalues[m_bool_vars[b]->get_origin_index()] = b2lb(m_bool_vars[b]->get_value());
            }
        }

        static lbool b2lb(bool b) {
            return b ? l_true : l_false;
        }

        /**
         * * Critical Move
         */
        int pick_critical_move_random(bool_var & bvar, var & avar, anum & best_value, int & best_score) {
            // Random walk case
            clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * curr_clause = m_nra_clauses[c_idx];

            m_vars_visited.reset();

            vector<var> best_arith_index = vector<var>();
            scoped_anum_vector arith_vals(m_am);
            vector<int> best_scores = vector<int>();
            for (literal_index l_idx : curr_clause->m_arith_literals) {
                nra_literal const * curr_literal = m_nra_literals[l_idx];
                for (var v : curr_literal->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                        scoped_anum best_value(m_am);
                        int best_score = INT_MIN;
                        if (get_best_arith_value_clause(v, best_value, c_idx, best_score)) {
                            best_arith_index.push_back(v);
                            arith_vals.push_back(best_value);
                            best_scores.push_back(best_score);
                        }
                    }
                }
            }

            vector<bool_var> best_bool_index = vector<bool_var>();
            for (literal_index l_idx : curr_clause->m_bool_literals) {
                nra_literal const * curr_literal = m_nra_literals[l_idx];
                SASSERT(curr_literal->is_bool());
                bool_var b = curr_literal->get_bool_index();
                best_bool_index.push_back(b);
            }

            int total_size = best_bool_index.size() + best_arith_index.size();
            if (total_size > 0) {
                int r = rand_int() % total_size;
                if (r < best_bool_index.size()) {
                    bvar = best_bool_index[r];
                    best_score = get_bool_critical_score(bvar);
                    return 0;  // bool operation
                } else {
                    SASSERT(arith_vals.size() > 0);
                    unsigned id = get_simplest_index(arith_vals);
                    avar = best_arith_index[id];
                    m_am.set(best_value, arith_vals[id]);
                    best_score = best_scores[id];
                    if (!is_simpler(best_value, m_slack_min2)) {
                        return 1;  // arith operation
                    }
                }
            }
            return -1;  // no operation found
        }

        int pick_critical_move(bool_var & bvar, var & avar, anum & best_value, int & best_score,
                               svector<clause_index> & equation_index) {
            int curr_score;
            int best_arith_score = INT_MIN;
            vector<var> best_arith_index = vector<var>();
            scoped_anum_vector best_values(m_am);

            int best_bool_score = INT_MIN;
            vector<bool_var> best_bool_index = vector<bool_var>();

            svector<svector<clause_index>> equation_clause_indices;

            m_vars_visited.reset();

            for (int i = 0; i < m_unsat_clauses.size(); i++) {
                clause_index c_idx = m_unsat_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                for (var v : curr_clause->m_vars) {
                    curr_score = get_best_arith_score(v);
                    if (curr_score > best_arith_score) {
                        best_arith_score = curr_score;
                    }
                }
            }

            for (int i = 0; i < m_unsat_clauses.size(); i++) {
                clause_index c_idx = m_unsat_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];

                if (best_arith_score != INT_MIN) {
                    for (var v : curr_clause->m_vars) {
                        if (!m_vars_visited.contains(v)) {
                            m_vars_visited.insert(v);
                            curr_score = get_best_arith_score(v);
                            if (curr_score == best_arith_score) {
                                best_arith_index.push_back(v);
                                scoped_anum w(m_am);
                                svector<clause_index> eq_idx;
                                get_best_arith_value(v, curr_score, w, eq_idx);
                                best_values.push_back(w);
                                equation_clause_indices.push_back(eq_idx);
                            }
                        }
                    }
                }

                for (literal_index l_idx : curr_clause->m_bool_literals) {
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    SASSERT(curr_literal->is_bool());
                    bool_var b = curr_literal->get_bool_index();
                    curr_score = get_bool_critical_score(b);
                    if (curr_score > best_bool_score) {
                        best_bool_score = curr_score;
                        best_bool_index.reset();
                        best_bool_index.push_back(b);
                    } else if (curr_score == best_bool_score) {
                        best_bool_index.push_back(b);
                    }
                }
            }

            if (best_bool_score > 0 || best_arith_score > 0) {
                // Has decreasing move
                if (best_bool_score > best_arith_score) {
                    bvar = best_bool_index[rand_int() % best_bool_index.size()];
                    best_score = best_bool_score;
                    return 0;  // bool operation
                }
                else if (best_bool_score < best_arith_score) {
                    SASSERT(best_values.size() > 0);
                    SASSERT(best_values.size() == equation_clause_indices.size());
                    unsigned id = get_simplest_index(best_values);
                    SASSERT(id >= 0 && id < best_values.size());
                    avar = best_arith_index[id];
                    best_score = best_arith_score;
                    m_am.set(best_value, best_values[id]);
                    for (clause_index cls_idx : equation_clause_indices[id]) {
                        equation_index.push_back(cls_idx);
                    }
                    return 1;  // arith operation
                } else {
                    int total_size = best_bool_index.size() + best_arith_index.size();
                    int r = rand_int() % total_size;
                    if (r < best_bool_index.size()) {
                        bvar = best_bool_index[r];
                        best_score = best_bool_score;
                        return 0;  // bool operation
                    } else {
                        SASSERT(best_values.size() > 0);
                        SASSERT(best_values.size() == equation_clause_indices.size());
                        unsigned id = get_simplest_index(best_values);
                        SASSERT(id >= 0 && id < best_values.size());
                        avar = best_arith_index[id];
                        best_score = best_arith_score;
                        m_am.set(best_value, best_values[id]);
                        for (clause_index cls_idx : equation_clause_indices[id]) {
                            equation_index.push_back(cls_idx);
                        }
                        return 1;  // arith operation
                    }
                }
            }

            // update clause weight
            if(rand_int() % 500 > smooth_probability){
                update_clause_weight();
            }
            else {
                smooth_clause_weight();
            }

            for (int i = 0; i < 3; i++) {
                int res = pick_critical_move_random(bvar, avar, best_value, best_score);
                if (res != -1) {
                    return res;
                }
            }
            no_operation_random_walk();
            return -1;
        }

        // pick var with coeff !=0, move to zero
        poly * get_atom_polys(ineq_atom const * a) const {
            LSTRACE(tout << "size: " << a->size() << std::endl;);
            SASSERT(a->size() > 0);
            poly * p = a->p(0);
            for(unsigned i = 1; i < a->size(); i++){
                poly * curr = a->p(i);
                p = m_pm.mul(p, curr);
            }
            return p;
        }

        /**
         * Score
         */
        int get_bool_critical_score(var b){
            int res_score = 0;
            nra_bool_var * m_bool_var = m_bool_vars[b];

            // loop all literal-clause pairs in this arith variable
            // literal 0 1 3 4 1 ...
            // clause  0 0 1 1 1 ...
            SASSERT(m_bool_var->m_literals.size() == m_bool_var->m_lit_cls.size());
            int make_break = 0; 

            for(unsigned i = 0; i < m_bool_var->m_literals.size(); i++){
                literal_index l_idx = m_bool_var->m_literals[i];
                clause_index c_idx = m_bool_var->m_lit_cls[i];
                nra_literal * curr_literal = m_nra_literals[l_idx];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(
                    tout << "consider literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;
                    tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;
                );
                SASSERT(curr_literal->is_bool());
                bool before_sat, after_sat;
                before_sat = is_literal_sat(curr_literal);
                after_sat = !before_sat;
                make_break += (after_sat - before_sat);
                LSTRACE(
                    tout << "bool value: "; tout << (before_sat ? "true" : "false"); tout << "->"; tout << (after_sat ? "true" : "false"); tout << std::endl;
                );

                // the end of a clause block (claus block means an area of the same clause index)
                // time to count clause count
                if(i == m_bool_var->m_literals.size() - 1 || (c_idx != m_bool_var->m_lit_cls[i + 1])){
                    LSTRACE(tout << "end for clause "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                    unsigned before_sat_count = curr_clause->get_sat_count();
                    LSTRACE(tout << "show make break: " << make_break << std::endl;);
                    unsigned after_sat_count = before_sat_count + make_break;
                    LSTRACE(tout << "sat count in get score: " << before_sat_count << "->" << after_sat_count << std::endl;);
                    SASSERT(after_sat_count >= 0);
                    // unsat --> sat
                    if(before_sat_count == 0 && after_sat_count > 0){
                        res_score += curr_clause->get_weight();
                    }
                    // sat --> unsat
                    else if(before_sat_count > 0 && after_sat_count == 0){
                        res_score -= curr_clause->get_weight();
                    }
                    make_break = 0;
                }
            }
            return res_score;
        }
        
        /**
         * Critical Move
         */
        void critical_bool_move(bool_var b){
            LSTRACE(tout << "start of critical bool move\n";);
            LSTRACE(tout << "show time entering critical bool move\n";
                TimeElapsed();
            );
            nra_bool_var * b_var = m_bool_vars[b];
            critical_subscore_bool(b);
            // flip the bool variable
            b_var->set_value(!b_var->get_value());
            // update bool score
            update_bool_score(b);
            LSTRACE(tout << "end of critical bool move\n";);
            LSTRACE(tout << "show time exiting critical bool move\n";
                TimeElapsed();
            );
        }

        // has not been flipped yet
        void critical_subscore_bool(bool_var b){
            // has not been assigned
            nra_bool_var * b_var = m_bool_vars[b];
            LSTRACE(tout << "start of critical subscore bool for bool var: " << b << std::endl;);
            int make_break = 0;
            m_literal_index_visited.reset();
            // same literal may appear, because same literals can be found in different clauses
            // in this case, we update literal's sat status at last
            
            for(unsigned i = 0; i < b_var->m_literals.size(); i++){
                literal_index l_idx = b_var->m_literals[i];
                if(!m_literal_index_visited.contains(l_idx)){
                    m_literal_index_visited.push_back(l_idx);
                }
                nra_literal * curr_literal = m_nra_literals[l_idx];
                bool before_sat = curr_literal->get_sat_status();
                LSTRACE(tout << "consider literal "; 
                    m_solver.display(tout, curr_literal->m_literal); tout << std::endl;
                );
                // true --> false
                if(before_sat){
                    LSTRACE(tout << "true --> false\n";);
                    make_break = -1;
                }
                // false --> true
                else {
                    LSTRACE(tout << "false --> true\n";);
                    make_break = 1;
                }
                // we assume that for a bool variable, 
                // it won't appear in the same clause twice or more
                clause_index c_idx = b_var->m_lit_cls[i];
                nra_clause * curr_clause = m_nra_clauses[c_idx];
                unsigned before_sat_count = curr_clause->get_sat_count();
                unsigned after_sat_count = before_sat_count + make_break;
                curr_clause->set_sat_count(after_sat_count);
                LSTRACE(tout << "show clause:\n";
                    m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;
                    tout << "before sat count: " << before_sat_count << std::endl;
                    show_ls_assignment(tout);
                );

                // sat --> unsat
                if(before_sat > 0 && after_sat_count == 0){
                    unsat_clause(curr_clause);
                }
                // unsat --> sat
                else if(before_sat == 0 && after_sat_count > 0){
                    sat_clause(curr_clause);
                }
            }
            for(literal_index l_idx: m_literal_index_visited){
                nra_literal * curr_l = m_nra_literals[l_idx];
                curr_l->flip_sat_status();
            }
            LSTRACE(tout << "end of critical subscore bool\n";);
        }

        void critical_nra_move(var v, anum const & value){
            scoped_anum old_value(m_am);
            m_am.set(old_value, m_assignment.value(v));
            LSTRACE(tout << "start of critical nra move\n";
                tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, old_value);
                tout << "->";
                m_am.display(tout, value); tout << std::endl;
                display_unsat_clauses(tout);
            );
            LSTRACE(show_ls_assignment(tout););
            m_assignment.set(v, value);

            // std::cout << "var: " << v << " "; m_solver.display_var(std::cout, v); std::cout << std::endl;
            // std::cout << "value: "; m_am.display(std::cout, old_value);
            // std::cout << "->";
            // m_am.display_root(std::cout, value); std::cout << " "; m_am.display(std::cout, value); std::cout << std::endl;

            critical_subscore_nra(v, value);
            // update arith score, except when the problem is already solved
            if (m_unsat_clauses.size() > 0 || use_equal_slack) {
                update_arith_score(v, value);
            }
            LSTRACE(tout << "end of critical nra move\n";
                display_unsat_clauses(tout);
            );
        }

        void critical_subscore_nra(var v, anum const & value){
            LSTRACE(tout << "start of nra subscore\n";
                tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, value); tout << std::endl;
                show_ls_assignment(tout);
            );
            LSTRACE(tout << "show time entering critical nra move\n";
                TimeElapsed();
            );
            // has been assigned
            nra_arith_var * v_var = m_arith_vars[v];
            int make_break = 0;
            // check whether has been changed anum and sat_status
            m_literal_index_visited.reset();
            m_literal_before_sat.reset();
            // if a literal has been reset literal, its before anum and before sat has also been changed

            for(unsigned i = 0; i < v_var->m_literals.size(); i++){
                literal_index l_idx = v_var->m_literals[i];
                nra_literal * curr_literal = m_nra_literals[l_idx];
                clause_index c_idx = v_var->m_lit_cls[i];
                nra_clause * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(tout << "consider literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;);
                bool before_sat, after_sat;
                // not found
                unsigned find_result = find_index_vector(m_literal_index_visited, l_idx);
                if(find_result == null_var){
                    before_sat = curr_literal->get_sat_status();
                    LSTRACE(tout << "not cached literal\n";);
                    set_literal_anum(curr_literal);
                    after_sat = curr_literal->get_sat_status();
                    // insert literal
                    m_literal_index_visited.push_back(l_idx);
                    m_literal_before_sat.push_back(before_sat);
                    SASSERT(m_literal_index_visited.size() == m_literal_before_sat.size());
                }
                // found cached
                else {
                    LSTRACE(tout << "cached literal\n";
                        display_literal_vector(tout, m_literal_index_visited);
                        display_bool_vector(tout, m_literal_before_sat);
                        tout << "find result: " << find_result << std::endl;
                    );
                    before_sat = m_literal_before_sat[find_result];
                    after_sat = curr_literal->get_sat_status();
                }
                make_break += (after_sat - before_sat);
                LSTRACE(
                    tout << "critical move bool value: "; tout << (before_sat ? "true" : "false"); tout << "->"; tout << (after_sat ? "true" : "false"); tout << std::endl;
                );
                // update delta informatiom
                // the end of a clause block (claus block means an area of the same clause index)
                // time to count clause count
                if(i == v_var->m_literals.size() - 1 || c_idx != v_var->m_lit_cls[i + 1]){
                    LSTRACE(tout << "enter new clause in critical nra move\n";);
                    unsigned before_sat_count = curr_clause->get_sat_count();
                    unsigned after_sat_count = before_sat_count + make_break;
                    curr_clause->set_sat_count(after_sat_count);
                    LSTRACE(tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                    LSTRACE(
                        tout << "make break: " << make_break << std::endl;
                        tout << "critical sat count: " << before_sat_count << "->" << after_sat_count << std::endl;);
                    // sat --> unsat
                    if(before_sat_count > 0 && after_sat_count == 0){
                        unsat_clause(curr_clause);
                    }
                    // unsat --> sat
                    else if(before_sat_count == 0 && after_sat_count > 0){
                        sat_clause(curr_clause);
                    }

                    // restore make break
                    make_break = 0;
                }
            }
            LSTRACE(tout << "end of nra subscore\n";);
            LSTRACE(tout << "show time exiting nra subscore\n";
                TimeElapsed();
            );
        }

        /**
         * Weight
         */
        void update_clause_weight(){
            // update unsat clauses weight
            m_vars_visited.reset();
            for(clause_index idx: m_unsat_clauses){
                nra_clause * cls = m_nra_clauses[idx];
                cls->inc_weight();
                for(var v : cls->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
            LSTRACE(display_clause_weight(tout););
        }

        void smooth_clause_weight(){
            m_vars_visited.reset();
            for(clause_index i = 0; i < m_num_clauses; i++){
                nra_clause * curr_clause = m_nra_clauses[i];
                // smooth weight for sat clause with weight > 1
                if(!m_unsat_clauses.contains(i) && curr_clause->get_weight() > 1){
                    curr_clause->dec_weight();
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
        }

        void reset_clause_weight(){
            m_vars_visited.reset();
            for (clause_index i = 0; i < m_num_clauses; i++){
                nra_clause * curr_clause = m_nra_clauses[i];
                curr_clause->set_weight(1);
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
        }

        void no_operation_random_walk(){
            SASSERT(!m_unsat_clauses.empty());
            // ^ random select a clause
            clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * cls = m_nra_clauses[c_idx];
            SASSERT(cls->size() != 0);
            // ^ random select a literal
            literal_index l_idx = cls->m_literals[rand_int() % cls->size()];
            nra_literal const * lit = m_nra_literals[l_idx];
            // ^ bool critical move
            if(lit->is_bool()){
                critical_bool_move(lit->get_bool_index());
            }
            else {
                SASSERT(!lit->m_vars.empty());
                var_vector non_zero_coeff_vars;
                polynomial_ref lc(m_pm);
                polynomial_ref curr_p(m_pm);
                for(var v: lit->m_vars){
                    curr_p = get_atom_polys(lit->get_atom());
                    unsigned k = degree(curr_p, v);
                    lc = m_pm.coeff(curr_p, v, k);
                    if(m_am.eval_sign_at(lc, m_assignment) != 0){
                        non_zero_coeff_vars.push_back(v);
                    }
                }
                var picked_v = null_var;
                // random choose one var
                if(non_zero_coeff_vars.empty()){
                    picked_v = random_table(lit->m_vars);
                    SASSERT(picked_v != null_var);
                }
                else {
                    picked_v = non_zero_coeff_vars[rand_int() % non_zero_coeff_vars.size()];
                }

                // choose value for picked arith var
                scoped_anum w(m_am);
                nra_arith_var const * curr_arith = m_arith_vars[picked_v];
                scoped_anum old_value(m_am);
                m_am.set(old_value, m_assignment.value(picked_v));

                scoped_anum_vector sample_values(m_am);
                m_ism.peek_in_complement_heuristic(curr_arith->m_infeasible_st, sample_values);
                scoped_anum w1(m_am);
                scoped_anum w2(m_am);
                int_gt(old_value, w1);
                if (!contains_value(curr_arith->m_infeasible_st, w1) && !contains_value(sample_values, w1)) {
                    sample_values.push_back(w1);
                }
                int_lt(old_value, w2);
                if (!contains_value(curr_arith->m_infeasible_st, w2) && !contains_value(sample_values, w2)) {
                    sample_values.push_back(w2);
                }
                m_am.set(w, sample_values[rand_int() % sample_values.size()]);
                critical_nra_move(picked_v, w);
                return;
            }
        }

        bool contains_value(anum_vector const & vec, anum const & w){
            for(auto ele: vec){
                if(m_am.eq(ele, w)){
                    return true;
                }
            }
            return false;
        }

        void propagate_sub_values(){
            for(auto ele: m_sub_value){
                var v = ele.m_var;
                poly const * p = ele.p, * q = ele.q;
                // v = q / p
                scoped_anum p_val(m_am), q_val(m_am), val(m_am);
                m_pm.eval(p, m_assignment, p_val);
                m_pm.eval(q, m_assignment, q_val);
                m_am.div(q_val, p_val, val);
                m_assignment.set(v, val);
            }
        }

        int get_total_weight() {
            // std::cout << "compute total weight" << std::endl;
            int result = 0;
            for (int i = 0; i < m_unsat_clauses.size(); i++) {
                clause_index curr_index = m_unsat_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[curr_index];
                result += curr_clause->get_weight();
                // std::cout << "unsat clause " << curr_index << " with weight " << curr_clause->get_weight() << std::endl;
            }
            return result;
        }

        /**
        * @brief Given a polynomial p
        * @return ineq_atom with left: !(p + slack < 0), right: !(p - slack > 0)
        */
        bool_var make_slack_atom_left(poly const * p) {
            poly * pp = m_pm.mul(rational(m_slack_threshold), p);
            poly * slack_poly = m_pm.mk_const(rational(1));
            poly * atom_poly = m_pm.add(pp, slack_poly);
            m_pm.inc_ref(atom_poly);
            bool is_even = false;
            return m_solver.mk_ineq_atom(atom::kind::LT, 1, &atom_poly, &is_even);
        }

        bool_var make_slack_atom_right(poly const * p) {
            poly * pp = m_pm.mul(rational(m_slack_threshold), p);
            poly * slack_poly = m_pm.mk_const(rational(1));
            poly * atom_poly = m_pm.sub(pp, slack_poly);
            m_pm.inc_ref(atom_poly);
            bool is_even = false;
            return m_solver.mk_ineq_atom(atom::kind::GT, 1, &atom_poly, &is_even);
        }

        /**
        * @brief Given a clause and picked arith var, select value according to different slack method
        * 1. var slack: pick value in [value - slack_min, value + slack_min]
        * 2. poly slack: rewrite == into [-slack_min, slack_min]
        */
        void slack_equational_clause_using_poly(svector<clause_index> c_idxs, var picked_v, anum & value) {
            // std::cout << "Variable " << picked_v << " value "; m_am.display(std::cout, value); std::cout << std::endl;
            // std::cout << "Number of clauses: " << c_idxs.size() << std::endl;
            for (unsigned i = 0; i < c_idxs.size(); i++) {
                clause_index c_idx = c_idxs[i];
                if (c_idx == UINT_MAX) {
                    continue;
                }
                nra_clause * cls = m_nra_clauses[c_idx];
                // std::cout << "Clause " << c_idx << ", number of literals: " << cls->m_literals.size() << std::endl;
                bool relaxed = false;
                for (unsigned j = 0; j < cls->m_literals.size(); j++) {
                    literal_index lit_index = cls->m_literals[j];
                    nra_literal * curr_literal = m_nra_literals[lit_index];
                    // m_solver.display(std::cout, curr_literal->m_literal); std::cout << std::endl;

                    if (curr_literal->is_arith()) {
                        if (curr_literal->is_slacked()) {
                            // already has slack
                            // std::cout << "already slack" << std::endl;
                            relaxed = true;
                        } else {
                            ineq_atom const * curr_atom = curr_literal->get_atom();
                            interval_set_ref curr_st(m_ism);
                            curr_st = m_evaluator.infeasible_intervals(curr_literal->get_atom(), curr_literal->sign(), nullptr, picked_v);
                            // m_ism.display(std::cout, curr_st); std::cout << std::endl;
                            if (!m_ism.has_infeasible_boundary(curr_st, value)) {
                                // std::cout << "Does not have infeasible boundary" << std::endl;
                                continue;
                            }
                            relaxed = true;
                            polynomial_ref p(m_pm);
                            p = get_atom_polys(curr_atom);
                            if (curr_atom->get_kind() == atom::EQ && !curr_literal->sign()) {
                                // p = 0, relax into !(p + slack < 0) and !(p - slack > 0)
                                bool_var left_atom_idx = make_slack_atom_left(p);
                                bool_var right_atom_idx = make_slack_atom_right(p);
                                m_solver.inc_ref(left_atom_idx);
                                m_solver.inc_ref(right_atom_idx);
                                ineq_atom * left_atom = (ineq_atom *) m_atoms[left_atom_idx];
                                ineq_atom * right_atom = (ineq_atom *) m_atoms[right_atom_idx];
                                curr_literal->set_slack_atoms(picked_v, left_atom, right_atom);
                            } else if (curr_atom->get_kind() == atom::LT && curr_literal->sign()) {
                                // !(p < 0), relax into !(p + slack < 0)
                                // std::cout << "case !(p < 0)" << std::endl;
                                bool_var left_atom_idx = make_slack_atom_left(p);
                                m_solver.inc_ref(left_atom_idx);
                                ineq_atom * left_atom = (ineq_atom *) m_atoms[left_atom_idx];
                                curr_literal->set_slack_atoms(picked_v, left_atom, nullptr);
                            } else if (curr_atom->get_kind() == atom::GT && curr_literal->sign()) {
                                // !(p > 0), relax into !(p - slack > 0)
                                // std::cout << "case !(p > 0)" << std::endl;
                                bool_var right_atom_idx = make_slack_atom_right(p);
                                m_solver.inc_ref(right_atom_idx);
                                ineq_atom * right_atom = (ineq_atom *) m_atoms[right_atom_idx];
                                curr_literal->set_slack_atoms(picked_v, nullptr, right_atom);
                            } else {
                                UNREACHABLE();
                            }
                        }
                    }
                }
            }
        }

        void restore_slacked_clauses() {
            // std::cout << "restore slacked clauses" << std::endl;
            // for (int i = 0; i < m_arith_vars.size(); i++) {
            //     std::cout << "var " << i << " "; m_solver.display(std::cout, i); std::cout << " ";
            //     m_am.display(std::cout, m_assignment.value(i)); std::cout << " = ";
            //     m_am.display_root(std::cout, m_assignment.value(i)); std::cout << std::endl;
            // }
            m_vars_visited2.reset();

            for (int i = 0; i < m_nra_literals.size(); i++) {
                nra_literal * curr_literal = m_nra_literals[i];
                if (curr_literal->is_slacked()) {
                    for (var v : curr_literal->m_vars) {
                        if (!m_vars_visited2.contains(v)) {
                            m_vars_visited2.insert(v);
                        }
                    }
                    // std::cout << "unslack literal "; m_solver.display(std::cout, curr_literal->m_literal); std::cout << std::endl;
                    curr_literal->unset_slack_atoms();

                    scoped_anum old_value(m_am);
                    m_am.set(old_value, m_assignment.value(curr_literal->get_slacked_var()));
                    critical_nra_move(curr_literal->get_slacked_var(), old_value);
                }
            }
            // std::cout << "Recompute for all variables" << std::endl;
            for (auto it = m_vars_visited2.begin(); it != m_vars_visited2.end(); it++) {
                compute_arith_var_info(*it);
                compute_boundary(*it);
            }
            // std::cout << "after restore slacked clauses" << std::endl;
            // std::cout << "Number of unsat clauses: " << m_unsat_clauses.size() << std::endl;
        }

        /**
         * Local Search
         */
        lbool local_search(){
            SPLIT_LINE(tout);
            LSTRACE(tout << "local search begin\n";
                std::cout << "local search begin\n";
            );
            SPLIT_LINE(tout);
            no_improve_cnt = 0;
            m_start_time = std::chrono::steady_clock::now();
            m_step = 0;
            // ICP returns false
            if(!init_solution(true)){
                LSTRACE(std::cout << "ICP returns false\n";);
                LSTRACE(tout << "ICP returns false\n";);
                return l_false;
            }
            for(m_step = 1; m_step < max_step; m_step++){
                // if (m_step % 100 == 0) {
                //     std::cout << "step: " << m_step << " #unsat clauses: " << m_unsat_clauses.size() << std::endl;
                // }

                LSTRACE(tout << "step: " << m_step << std::endl;
                    tout << "no improve cnt: " << no_improve_cnt << std::endl;
                );

                // Finished stage with slack
                if (m_unsat_clauses.empty() && use_equal_slack){
                    SPLIT_LINE(std::cout);
                    LSTRACE(
                        std::cout << "local search succeed\n";
                        tout << "local search succeed\n";
                    );
                    SPLIT_LINE(std::cout);
                    use_equal_slack = false;
                    restore_slacked_clauses();
                    reset_clause_weight();
                    m_best_found_restart = m_unsat_clauses.size();
                    no_improve_cnt = 0;
                    m_am.set(m_slack_min2, m_slack_min);
                }

                // Succeed
                if (m_unsat_clauses.empty() && !use_equal_slack) {
                    collect_bool_values();
                    check_solution_sat();
                    propagate_sub_values();
                    return l_true;
                }

                // // Fail
                // if(TimeElapsed() > m_cutoff && m_step % 100 == 0){
                //     SPLIT_LINE(std::cout);
                //     LSTRACE(std::cout << "local search failed\n";);
                //     SPLIT_LINE(std::cout);
                //     return l_undef;
                // }
                
                // Main
                LSTRACE(tout << "enter main procedure\n";);

                // Search

                // pick bool variable
                bool_var picked_b;
                var picked_v;
                scoped_anum next_value(m_am);
                int best_score;
                svector<clause_index> equation_index;
                int mode = pick_critical_move(picked_b, picked_v, next_value, best_score, equation_index);

                // int before_weight = get_total_weight();
                if (mode == 0) {  // bool operation
                    SASSERT(equation_index.size() == 0);
                    critical_bool_move(picked_b);
                    // int after_weight = get_total_weight();
                    // if (before_weight - after_weight != best_score) {
                    //     std::cout << before_weight << std::endl;
                    //     std::cout << after_weight << std::endl;
                    //     std::cout << best_score << std::endl;
                    //     UNREACHABLE();
                    // }
                    // SASSERT(before_weight - get_total_weight() == best_score);
                } else if (mode == 1) {  // arith operation
                    // slack equational clauses
                    if (use_equal_slack && equation_index.size() > 0 && is_simpler(next_value, m_slack_min2)) {
                        // only slack when next_value is more complex than m_min
                        slack_equational_clause_using_poly(equation_index, picked_v, next_value);
                        scoped_anum old_value(m_am);
                        m_am.set(old_value, m_assignment.value(picked_v));
                        critical_nra_move(picked_v, old_value);
                    } else {
                        critical_nra_move(picked_v, next_value);
                        if (use_equal_slack && is_simpler(next_value, m_slack_min2)) {
                            m_am.set(m_slack_min2, next_value);
                        }
                        // int after_weight = get_total_weight();
                        // if (before_weight - after_weight != best_score) {
                        //     std::cout << "before weight: " << before_weight << std::endl;
                        //     std::cout << "after weight: " << after_weight << std::endl;
                        //     std::cout << "best score: " << best_score << std::endl;
                        //     UNREACHABLE();
                        // }
                        // SASSERT(before_weight - get_total_weight() == best_score);
                    }
                } else {
                    // No operation
                }

                // update improvement
                if(update_solution_info()){
                    no_improve_cnt = 0;
                }
                else {
                    no_improve_cnt++;
                }

                // Restart for recover stage
                // if (!use_equal_slack && no_improve_cnt > 10) {
                //     init_solution(true);
                //     no_improve_cnt = 0;
                //     use_equal_slack = true;
                // }

                // Small restart
                if (no_improve_cnt > 100){
                    LSTRACE(tout << "no improve count: " << no_improve_cnt << std::endl;
                        tout << "restart\n";
                        SPLIT_LINE(std::cout);
                        SPLIT_LINE(tout);
                        std::cout << "no improve, restart\n";
                        SPLIT_LINE(std::cout);
                        SPLIT_LINE(tout);
                    );
                    init_solution(false);
                    use_equal_slack = true;
                    no_improve_cnt = 0;
                    use_infeasible_st = !use_infeasible_st;
                    m_restart_count += 1;

                    // Big restart
                    if (m_restart_count % 100 == 0) {
                        init_solution(true);
                        m_restart_count = 0;
                    }
                }
            }
            SPLIT_LINE(std::cout);
            LSTRACE(std::cout << "local search failed\n";);
            SPLIT_LINE(std::cout);
            return l_undef;
        }

        void check_solution_sat() const {
            for(unsigned i = 0; i < m_nra_clauses.size(); i++){
                if(!is_clause_sat(m_nra_clauses[i])){
                    UNREACHABLE();
                }
            }
        }

        bool is_clause_sat(nra_clause const * cls) const {
            for(literal_index l_idx: cls->m_literals){
                nra_literal const * l = m_nra_literals[l_idx];
                if(is_literal_sat(l)){
                    return true;
                }
            }
            return false;
        }

        bool is_literal_sat(nra_literal const * l) const {
            if(l->is_bool()){
                nra_bool_var const * b = m_bool_vars[l->get_bool_index()];
                return l->sign() != b->get_value();
            }
            else {
                return m_evaluator.eval((atom * ) l->get_atom(), l->sign());
            }
        }

        /**
         * Display
         */
        std::ostream & show_ls_assignment(std::ostream & out) const {
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                nra_bool_var const * b_var = m_bool_vars[b];
                out << "b" << b << ": " << (b_var->get_value() ? "true" : "false") << std::endl;
            }
            m_assignment.display(out);
            return out;
        }

        std::ostream & display_var_vector(std::ostream & out, var_vector const & vec) const {
            for(var v = 0; v < vec.size(); v++){
                out << v << " -> " << vec[v] << std::endl;
            }
            return out;
        }

        std::ostream & display_var_set(std::ostream & out, var_vector const & vec) const {
            for(var v: vec){
                out << v << " ";
            }
            return out;
        }

        std::ostream & display_var_table(std::ostream & out, var_table const & vec) const {
            for(var v: vec){
                out << v << " ";
            }
            return out;
        }

        std::ostream & display_literal_set(std::ostream & out, var_vector const & vec) const {
            for(literal_index v: vec){
                literal l = m_nra_literals[v]->m_literal;
                m_solver.display(out, l);
                out << " ";
            }
            return out;
        }

        std::ostream & display_clause_set(std::ostream & out, var_vector const & vec) const {
            for(clause_index v: vec){
                clause const & cls = *m_clauses[v];
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_bool(std::ostream & out, bool b) const {
            out << (b ? "true" : "false");
            return out;
        }

        std::ostream & display_arith_intervals(std::ostream & out) const {
            for(var v = 0; v < m_arith_vars.size(); v++){
                nra_arith_var const * curr = m_arith_vars[v];
                out << v << ": " << "feasible: ";
                m_ism.display(out, curr->m_feasible_st);
                out << "  " << "infeasible: ";
                m_ism.display(out, curr->m_infeasible_st);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clause_info(std::ostream & out, nra_clause const * c) const {
            out << "show clause info:\n";
            out << "clause: "; m_solver.display(out, *c->get_clause()); out << std::endl;
            out << "sat count: " << c->get_sat_count() << std::endl;
            out << "sat status: " << (c->get_sat_status() ? "true" : "false") << std::endl;
            return out;
        }

        std::ostream & display_vars(std::ostream & out) const {
            out << "display arith vars\n";
            for(var v = 0; v < m_num_vars; v++){
                out << v << "  ";
                m_solver.display_var(out, v);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clauses(std::ostream & out) const {
            out << "display clauses\n";
            for(clause_index c = 0; c < m_clauses.size(); c++){
                out << "clause " << c << ": ";
                const clause & cls = *(m_clauses[c]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_unit_clauses(std::ostream & out) const {
            out << "display unit clauses\n";
            for(clause_index cls_idx: m_unit_clauses){
                const clause & cls = *(m_clauses[cls_idx]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_unsat_clauses(std::ostream & out) const {
            out << "display unsat clauses\n";
            if(m_unsat_clauses.empty()){
                out << "no unsat clauses\n";
            }
            for(clause_index cls_idx: m_unsat_clauses){
                const clause & cls = *(m_clauses[cls_idx]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_literal_vector(std::ostream & out, var_vector const & vec) const {
            out << "show literal index vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << i << " ";
                m_solver.display(out, m_nra_literals[vec[i]]->m_literal);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_bool_vector(std::ostream & out, bool_vector const & vec) const {
            out << "show bool vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << i << " ";
                out << (vec[i] ? "true" : "false");
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_anum_vector(std::ostream & out, anum_vector const & vec) const {
            out << "show anum vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << "[" << i << "] ";
                m_am.display(out, vec[i]);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clause_weight(std::ostream & out) const {
            out << "display clause weights\n";
            for(clause_index i = 0; i < m_nra_clauses.size(); i++){
                const clause & cls = *(m_nra_clauses[i]->get_clause());
                m_solver.display(out, cls);
                out << std::endl;
                out << "weight: " << m_nra_clauses[i]->get_weight() << std::endl;
            }
            return out;
        }

        std::ostream & display_poly_vector(std::ostream & out, polynomial_ref_vector const & vec) const {
            for(unsigned i = 0; i < vec.size(); i++){
                polynomial_ref ele(m_pm);
                ele = vec.get(i);
                m_pm.display(out, ele);
                out << std::endl;
            }
            return out;
        }
    };

    ls_helper::ls_helper(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, svector<lbool> & bvalues, clause_vector const & cls, atom_vector const & ats, bool_var_vector const & pure_bool_vars, 
                         bool_var_vector const & pure_bool_convert, 
                        unsigned seed, substitute_value_vector const & vec
                         ){
        m_imp = alloc(imp, s, am, pm, cache, ism, ev, ass, bvalues, cls, ats, pure_bool_vars, pure_bool_convert, seed, vec);
    }

    ls_helper::~ls_helper(){
        dealloc(m_imp);
    }

    void ls_helper::set_var_num(unsigned x){
        m_imp->set_var_num(x);
    }

    lbool ls_helper::local_search(){
        return m_imp->local_search();
    }
};