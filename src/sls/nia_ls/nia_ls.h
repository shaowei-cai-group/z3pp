#pragma once
#include <cstdio>
#include <chrono>
#include <string.h>
#include<stack>
#include<random>
#include<map>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdlib>
#include<exception>
#include<time.h>
#include<signal.h>
#include<unistd.h>
#include<sys/types.h>
#include<string>
#include "nia_Array.h"
#include <algorithm>

namespace nia {
const __int128_t max_int=__int128_t(INT64_MAX);
//the var_index=1(_vars[1]=x), exponent=2: x^2
struct var_exp{
    int var_index;
    int exponent=1;
    var_exp(int index){var_index=index;}
};

//the term are in the form of x^3*y^2*z, stored in var_exps, and var_exps are sorted according to its exponents
struct term{
    std::vector<var_exp>        var_epxs;
    __int128_t                   value;
};

//term_in_lit means the term containing the var in the corresponding lit, with the coff coffient
struct var_lit_term{
    uint64_t var_idx;
    uint64_t term_idx;
    uint64_t lit_idx;
    __int128_t coff;
    var_lit_term(uint64_t _var_idx,uint64_t _term_idx,int _lit_idx,int _coff):var_idx(_var_idx),term_idx(_term_idx),lit_idx(_lit_idx),coff(_coff){};
};

struct coff_term{
    int term_idx;
    __int128_t coff;
    coff_term(){};
    coff_term(int _term_idx,__int128_t _coff):term_idx(_term_idx),coff(_coff){};
};
//one arith lit is in the form of a_1*term_1+...+a_n*term_n+k<=0, the cofficient are divided into positive ones and negative ones, the coff are positive.
//if coff =1 , -1 term=xy, ab means xy-ab
//if is_nia_lit: \sum coff*term<=key
//else:_vars[delta] 
struct lit{
    std::vector<coff_term>          coff_terms;//sort by term
    std::vector<var_lit_term>      var_lit_terms;//sort by var
    __int128_t                     key;
    int                         lits_index;
    __int128_t                     delta;//the current value of left side
    bool                        is_equal=false;//true means a-b-k==0, else a-b-k<=0
    bool                        is_nia_lit=false;
    int                         is_true;//1 means the lit is true, -1 otherwise
};

struct variable{
    std::vector<int>            clause_idxs;
    std::vector<bool>            bool_var_in_pos_clause;//true means the boolean var is the pos form in corresponding clause
    std::vector<var_lit_term>   var_lit_terms;//sort by lit
    std::vector<uint64_t>         literal_idxs;
    std::vector<uint64_t>       term_idxs;//term idx(no repeating)
    std::string                 var_name;
    __int128_t                         low_bound=-max_int;
    __int128_t                         upper_bound=max_int;
    bool                        is_nia;
    bool                        is_delete=false;
    int                         score;//if it is a bool var, then the score is calculated beforehand
    int                         up_bool=0;//the bool value of variables deleted(1 true -1 false)
};

struct clause{
    std::vector<int>            literals;//literals[i]=l means the ith literal of the clause if the pos(neg) of the _lits, it can be negative
    std::vector<int>            nia_literals;
    std::vector<int>             bool_literals;
    int                          weight=1;
    int                          sat_count;
    int                          watch_lit_idx;//the lit_idx of sat literal in the clause
    bool                         is_delete=false;
};

class ls_solver{
public:
    
    //basic information
    uint64_t                    _num_vars;
    uint64_t                    _num_nia_vars;
    uint64_t                    _num_lits;
    int                         _num_nia_lits;
    int                         _num_bool_lits;
    uint64_t                    _num_clauses;
    uint64_t                    _num_opt=0;//the number of vars in all literals, which is the max number of operations
    std::vector<variable>       _vars;
    std::vector<variable>       _tmp_vars;
    std::vector<variable>        _resolution_vars;
    std::vector<int>            nia_var_vec;
    std::vector<int>            bool_var_vec;
    std::vector<__int128_t>     term_coffs;//given a current var, the term_coff[t] means the term_coff of var in term t
    std::vector<term>           _terms;
    std::vector<lit>            _lits;
    std::vector<int>            _lit_make_break;//making a move will make or break the lit itself (1:make, -1:break, 0:no change)
    std::vector<int>            _bound_lits;//record the index of bounded lits
    std::vector<clause>         _clauses;
    std::stack<clause>          _reconstruct_stack;
    Array                       *unsat_clauses;
    Array                       *sat_clause_with_false_literal;//clauses with 0<sat_num<literal_num, from which swap operation are choosen
    Array                       *contain_bool_unsat_clauses;//unsat clause with at least one boolean var
    Array                       *false_lit_occur;//the false lits for choosing critical move
    Array                       *var_in_long_term;//the var in terms with length>2
    int                         nia_var_idx_with_most_lits;
    bool                        use_pbs=false;
    bool                        is_idl=true;//if it is the IDL mode
    uint64_t                    last_op_var;
    __int128_t                  last_op_value;//the last value and last var, x +1, at least at next step, x -1 is forbidden
    bool                        has_high_coff=false;//if there exists x*x
    //solution
    std::vector<__int128_t>       _solution;
    std::vector<__int128_t>       _best_solutin;
    int                         best_found_cost;
    int                         best_found_this_restart;
    int                         no_improve_cnt_bool=0;
    int                         no_improve_cnt_nia=0;
    bool                        is_in_bool_search=false;
    int                         _best_found_hard_cost_this_bool;
    int                         _best_found_hard_cost_this_nia;
    //control
    uint64_t                    _step;
    uint64_t                    _outer_layer_step;
    const uint64_t              _max_step;
    std::vector<uint64_t>       tabulist;//tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then
    std::vector<bool>           is_chosen_bool_var;
    std::vector<uint64_t>       last_move;
    std::vector<uint64_t>            operation_var_idx_vec;
    std::vector<__int128_t>        operation_change_value_vec;
    std::vector<int>             operation_var_idx_bool_vec;
    std::chrono::steady_clock::time_point start;
    double                      best_cost_time;
    double                      _cutoff;
    std::mt19937                mt;
    const uint64_t              _additional_len;
    std::map<std::string,uint64_t> name2var;//map the name of a variable to its index
    std::map<std::string,uint64_t> name2tmp_var;
    std::map<std::string,uint64_t> name2resolution_var;
    std::map<std::string,uint64_t>  str2termidx;//map the term string to its index, how to hash the term? etc: x^3*y^2 the idx of x and y is 1 and 2 then sort x,y first to get "_1^3_2^2"
    std::vector<int>            _pre_value_1;//the 1st pre-set value of a var, if the var is in the form of (a==0 OR a==1)
    std::vector<int>            _pre_value_2;
    bool                         use_swap_from_from_small_weight;
    std::vector<bool>           term_appear;//true means the term exists
    std::vector<bool>           lit_appear;//true means the lit exists in the formula
    // data structure for clause weighting
    const uint64_t              smooth_probability;
    uint64_t                    _swt_threshold;
    float                       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t                    total_clause_weight;
    int                         _lit_in_unsat_clause_num;
    int                         _bool_lit_in_unsat_clause_num;
    //data structure for equality
    std::vector<int>            fa;//fa[x]=f means x=coff*f
    std::vector<int>            fa_coff;//fa_coff[x]=c means x==c*fa[x]
    
    //input transformation
    void                        split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern);
    void                        build_lits(std::string &in_string);
    void                        build_instance(std::vector<std::vector<int> >& clause_vec);
    void                        equal_vars(std::vector<std::vector<int> >& clause_vec);//find out the equalilty among vars, and reset the terms and lits
    int                        find(int var_idx);//return the fa of var_idx
    void                        merge(int var_idx_1,int var_idx_2,int coff_1,int coff_2);//var_1*coff_1=var_2*coff_2
    void                        update_lit_equal(int lit_idx);
    uint64_t                    transfer_name_to_reduced_var(std::string & name,bool is_nia);//after the resolution vars are inserted into _vars
    uint64_t                    transfer_name_to_resolution_var(std::string &name,bool is_nia);//bool var is inserted into _resolution_var when build lit
    uint64_t                    transfer_name_to_tmp_var(std::string &name);//nia var is first inserted into _tmp_var when build lit, then inserted into _resolution_var when reduce var(x-y->z)
    uint64_t                    transfer_term_to_idx(term t);
    void                        transfer_term_to_str(term &t,std::string &str);
    void                        reduce_vars();//reduce the x-y in all lits to new var z
    
    
    //initialize
    ls_solver();
    ls_solver(int random_seed);
    void                        make_space();
    void                        make_lits_space(uint64_t num_lits){_num_lits=num_lits;_lits.resize(num_lits+_additional_len);};
    void                        initialize();
    void                        initialize_variable_datas();
    void                        initialize_term_datas();
    void                        initialize_lit_datas();
    void                        initialize_clause_datas();
    void                        unit_prop();
    void                        resolution();
    __int128_t                  hash_lits_to_num(std::vector<int> &lits);
    void                        reduce_clause();
    void                        set_pre_value();
    void                        read_model();
    bool                        is_same_lits(std::vector<int> &lits_1,std::vector<int> &lits_2);
    
    //random walk
    void                        update_clause_weight();
    void                        smooth_clause_weight();
    void                        random_walk();
    void                        no_operation_random_walk();//when there is no operation, simply find a lit in a random false clause, pick a random var with coff!=0, set it to 0
    
    //construction
    void                        construct_slution_score();//construct the solution based on score
    
    //basic operations
    inline void                 sat_a_clause(uint64_t clause_idx){unsat_clauses->delete_element((int)clause_idx);contain_bool_unsat_clauses->delete_element((int)clause_idx);};
    inline void                 unsat_a_clause(uint64_t clause_idx){unsat_clauses->insert_element((int)clause_idx);
                                 if(_clauses[clause_idx].bool_literals.size()>0)contain_bool_unsat_clauses->insert_element((int)clause_idx);};
    bool                        update_best_solution();
    int                         pick_critical_move(__int128_t &best_value);
    int                         pick_critical_move_bool();
    void                        critical_move(uint64_t var_idx,__int128_t change_value);
    void                        move_update(uint64_t var_idx,__int128_t change_value);
    void                        move_update(uint64_t var_idx);//dedicated for boolean var
    void                        invert_lit(lit &l);
    __int128_t                     delta_lit(lit &l);
    __int128_t                  coff_in_term(uint64_t var_idx,uint64_t term_idx);
    double                      TimeElapsed();
    void                        clear_prev_data();
    __int128_t                     devide(__int128_t a, __int128_t b);
    void                        insert_operation(uint64_t var_idx,__int128_t change_value,int &operation_idx,bool use_tabu);
    void                        add_bool_operation(bool use_tabu,int lit_idx,int &operation_idx_bool);//given a false lit, add the corresponding var to the operation_vec_bool
    void                        add_operation_from_false_lit(bool use_tabu,int lit_idx,int &operation_idx);//given a false lit(lit_idx<0 means it is the neg form)
    void                        select_best_operation_from_vec(int operation_idx,int &best_score,int &best_var_idx,__int128_t &best_value);
    void                        select_best_operation_from_bool_vec(int operation_idx_bool,int &best_score_bool,int &best_var_idx_bool);
    void                        add_swap_operation(int &operation_idx);
    void                        swap_from_small_weight_clause();
    void                        enter_nia_mode();
    void                        enter_bool_mode();
    bool                        update_inner_best_solution();
    bool                        update_outer_best_solution();
    //print
    void                        print_formula();
    void                        print_literal(lit &l);
    void                        print_formula_pbs();
    void                        print_lit_pbs(lit &l);
    void                        print_formula_smt();
    void                        print_lit_smt(int lit_idx);
    void                        print_mv();
    void                        print_mv_vars(uint64_t var_idx);
    void                        print_var_solution(std::string &var_name,std::string &var_value);
    void                        print_term(term &t);
    void                        up_bool_vars();
    //calculate score
    int                         critical_score(uint64_t var_idx,__int128_t change_value);
    __int128_t                     critical_subscore(uint64_t var_idx,__int128_t change_value);
    //check
    bool                        check_solution();
    inline bool                 is_single_var_term(term &t){return t.var_epxs.size()==1&&t.var_epxs[0].exponent==1;}//if the term is in the form of X (single var)
    //handle 128
    inline __int128_t           abs_128(__int128_t n){return n>=0?n:-n;}
    std::string                 print_128(__int128 n);
    //local search
    bool                        local_search();
};
}
