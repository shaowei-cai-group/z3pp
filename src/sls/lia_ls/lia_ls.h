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
#include "sls/lia_ls/lia_Array.h"

namespace lia {
const __int128_t max_int=__int128_t(INT64_MAX)*__int128_t(INT64_MAX);
//one arith lit is in the form of a_1*x_1+...+a_n*x_n+k<=0, the cofficient are divided into positive ones and negative ones, the coff are positive.
//if neg_coff =1 neg_coff_var=x pos_coff=1 pos_coff_var=y means y-x
//if is_lia_lit: \sum coff*var_idx<=key
//else:_vars[delta]
struct lit{
    std::vector<int>            pos_coff_var_idx;
    std::vector<__int128_t>        pos_coff;
    std::vector<int>            neg_coff_var_idx;
    std::vector<__int128_t>        neg_coff;
    __int128_t                     key;
    int                         lits_index;
    __int128_t                     delta;//the current value of left side
    bool                        is_equal=false;//true means a-b-k==0, else a-b-k<=0
    bool                        is_lia_lit=false;
};

struct variable{
    std::vector<int>            literals;//literals[i]=l means the ith literal of the var is the pos(neg) of lth of _lits, it can be negative
    std::vector<int>            literal_clause;//literal_clause[i]=c means the ith literal containing the var is in cth clause
    std::vector<__int128_t>            literal_coff;//literal_coff[i] denotes the coff of the var in corresponding literal, it can be negative
    std::vector<uint64_t>       clause_idxs;
    std::string                 var_name;
    __int128_t                         low_bound=-max_int;
    __int128_t                         upper_bound=max_int;
    bool                        is_lia;
    bool                        is_delete=false;
    int                         score;//if it is a bool var, then the score is calculated beforehand
    int                         up_bool=0;//the bool value of variables deleted(1 true -1 false)
};

struct clause{
    std::vector<int>            literals;//literals[i]=l means the ith literal of the clause if the pos(neg) of the _lits, it can be negative
    std::vector<int>            lia_literals;
    std::vector<int>             bool_literals;
    int                          weight=1;
    int                          sat_count;
    __int128_t                      min_delta;//a positive value, the distance from sat, delta for pos lit, 1-delta for neg lit
    int                          min_delta_lit_index;//the lit index with the min_delta
    bool                         is_delete=false;
};

class ls_solver{
public:
    
    //basic information
    uint64_t                    _num_vars;
    uint64_t                    _num_lia_vars;
    uint64_t                    _num_lits;
    int                         _num_lia_lits;
    int                         _num_bool_lits;
    uint64_t                    _num_clauses;
    uint64_t                    _num_opt=0;//the number of vars in all literals, which is the max number of operations
    std::vector<variable>       _vars;
    std::vector<variable>       _tmp_vars;
    std::vector<variable>        _resolution_vars;
    std::vector<int>            lia_var_vec;
    std::vector<int>            bool_var_vec;
    std::vector<lit>            _lits;
    std::vector<int>            _bound_lits;//record the index of bounded lits
    std::vector<clause>         _clauses;
    std::vector<bool>           lit_appear;
    Array                       *unsat_clauses;
    Array                       *sat_clause_with_false_literal;//clauses with 0<sat_num<literal_num, from which swap operation are choosen
    Array                       *contain_bool_unsat_clauses;//unsat clause with at least one boolean var
    Array                       *lit_occur;//the lit containing the lia var in one single clause
    Array                       *pair_x;//x-y-->z
    Array                       *pair_y;
    std::vector<__int128_t>    pair_x_value;
    std::vector<__int128_t>     pair_y_value;
    int                         lia_var_idx_with_most_lits;
    bool                        use_pbs=false;
    bool                        is_idl=true;//if it is the IDL mode
    //solution
    std::vector<__int128_t>       _solution;
    std::vector<__int128_t>       _best_solutin;
    int                         best_found_cost;
    int                         best_found_this_restart;
    int                         no_improve_cnt_bool=0;
    int                         no_improve_cnt_lia=0;
    bool                        is_in_bool_search=false;
    int                         _best_found_hard_cost_this_bool;
    int                         _best_found_hard_cost_this_lia;
    std::stack<clause>          _reconstruct_stack;
    //control
    uint64_t                    _step;
    uint64_t                    _outer_layer_step;
    const uint64_t              _max_step;
    std::vector<uint64_t>       tabulist;//tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then
    std::vector<int>            CClist;//CClist[2*var]==1 and [2*var+1]==1 means that var is allowed to move forward or backward
    std::vector<bool>           is_chosen_bool_var;
    int                          CC_mode;
    std::vector<uint64_t>       last_move;
    std::vector<int>            operation_var_idx_vec;
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
    std::vector<int>            _pre_value_1;//the 1st pre-set value of a var, if the var is in the form of (a==0 OR a==1)
    std::vector<int>            _pre_value_2;
    bool                         use_swap_from_from_small_weight;
    // data structure for clause weighting
    const uint64_t              smooth_probability;
    uint64_t                    _swt_threshold;
    float                       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t                    total_clause_weight;
    int                         _lit_in_unsat_clause_num;
    int                         _bool_lit_in_unsat_clause_num;
    
    //input transformation
    void                        split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern);
    void                        build_lits(std::string &in_string);
    void                        build_instance(std::vector<std::vector<int> >& clause_vec);
    uint64_t                    transfer_name_to_reduced_var(std::string & name,bool is_lia);//after the resolution vars are inserted into _vars
    uint64_t                    transfer_name_to_resolution_var(std::string &name,bool is_lia);//bool var is inserted into _resolution_var when build lit
    uint64_t                    transfer_name_to_tmp_var(std::string &name);//lia var is first inserted into _tmp_var when build lit, then inserted into _resolution_var when reduce var(x-y->z)
    void                        reduce_vars();//reduce the x-y in all lits to new var z
    
    
    //initialize
    ls_solver();
    ls_solver(int random_seed);
    ls_solver(int random_seed,unsigned cutoff);
    void                        make_space();
    void                        make_lits_space(uint64_t num_lits){_num_lits=num_lits;_lits.resize(num_lits+_additional_len);};
    void                        initialize();
    void                        initialize_variable_datas();
    void                        initialize_lit_datas();
    void                        initialize_clause_datas();
    void                        build_neighbor();
    void                        unit_prop();
    void                        resolution();
    void                        reduce_clause();
    void                        set_pre_value();
    
    //random walk
    void                        update_clause_weight();
    void                        smooth_clause_weight();
    void                        random_walk();
    
    //construction
    void                        construct_slution_score();//construct the solution based on score
    uint64_t                    pick_construct_idx(__int128_t &best_value);
    void                        construct_move(uint64_t var_idx,__int128_t change_value);
    int                         construct_score(uint64_t var_idx,__int128_t change_value);
    
    //basic operations
    inline void                 sat_a_clause(uint64_t clause_idx){unsat_clauses->delete_element((int)clause_idx);contain_bool_unsat_clauses->delete_element((int)clause_idx);};
    inline void                 unsat_a_clause(uint64_t clause_idx){unsat_clauses->insert_element((int)clause_idx);
                                 if(_clauses[clause_idx].bool_literals.size()>0)contain_bool_unsat_clauses->insert_element((int)clause_idx);};
    void                        convert_to_pos_delta(__int128_t &delta,int l_idx);
    bool                        update_best_solution();
    void                        modify_CC(uint64_t var_idx,int direction);
    int                         pick_critical_move(__int128_t &best_value);
    int                         pick_critical_move_bool();
    void                        critical_move(uint64_t var_idx,__int128_t change_value);
    void                        invert_lit(lit &l);
    __int128_t                     delta_lit(lit &l);
    double                      TimeElapsed();
    void                        clear_prev_data();
    __int128_t                     devide(__int128_t a, __int128_t b);
    void                        insert_operation(int var_idx,__int128_t change_value,int &operation_idx);
    void                        add_swap_operation(int &operation_idx);
    void                        swap_from_small_weight_clause();
    void                        enter_lia_mode();
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
    void                        choose_value_for_pair();//dedicated for x-y=z, choose a value for x
    void                        up_bool_vars();
    //calculate score
    int                         critical_score(uint64_t var_idx,__int128_t change_value);
    __int128_t                     critical_subscore(uint64_t var_idx,__int128_t change_value);
    void                        critical_score_subscore(uint64_t var_idx,__int128_t change_value);
    void                        critical_score_subscore(uint64_t var_idx);//dedicated for boolean var
    //check
    bool                        check_solution();
    //handle 128
    inline __int128_t           abs_128(__int128_t n){return n>=0?n:-n;}
    std::string                 print_128(__int128 n);
    //local search
    bool                        local_search();
};
}