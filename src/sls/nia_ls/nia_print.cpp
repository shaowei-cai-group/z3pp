#include"nia_ls.h"
#include <sstream>
namespace nia{
//print
void ls_solver::print_formula(){
    for(int i=0;i<_num_clauses;i++){
        clause *cl=&(_clauses[i]);
        std::cout<<i<<"\n";
        for(int l_idx: cl->literals){
            std::cout<<l_idx<<": ";
            if(l_idx<0){std::cout<<"neg: ";}
            print_literal(_lits[std::abs(l_idx)]);}
        std::cout<<"\n";
    }
}

void ls_solver::print_formula_pbs(){
    std::cout<<"p wcnf "<<_num_vars<<" "<<(_num_lits-_num_vars*2)<<" "<<_num_vars+1<<"\n";
    for(int lit_idx=1;lit_idx<_num_lits;lit_idx++){
        lit *l=&(_lits[lit_idx]);
        if(l->lits_index==0){continue;}
        print_lit_pbs(_lits[lit_idx]);
    }
    std::cout<<"2 0 1 1 0\n";
}

void ls_solver::print_formula_smt(){
    std::cout<<"(set-info :smt-lib-version 2.6)\n(set-logic QF_IDL)\n";
    for(variable &v:_vars){std::cout<<"(declare-fun "<<v.var_name<<" () "<<(v.is_nia?"Int":"Bool")<<")\n";}
    std::cout<<"(assert\n(and\n";
    for(clause &cl:_clauses){
        std::cout<<"(or ";
        for(int lit_idx:cl.literals){print_lit_smt(lit_idx);}
        std::cout<<")\n";
    }
    std::cout<<"))\n(check-sat)\n(exit)\n";
}


void ls_solver::print_term(term &t){
    for(int i=0;i<t.var_epxs.size();i++){
        var_exp * ve=&(t.var_epxs[i]);
        if(i!=0){std::cout<<"*";}
        std::cout<<_vars[ve->var_index].var_name;
        if(ve->exponent>1){std::cout<<"^"<<ve->exponent;}
    }
}
void ls_solver::print_literal(lit &l){
    if(!l.is_nia_lit){std::cout<<_vars[l.delta].var_name<<"\n";}
    else{
    for(int i=0;i<l.coff_terms.size();i++){
        std::cout<<"( "<<print_128(l.coff_terms[i].coff)<<" * ";
        print_term(_terms[l.coff_terms[i].term_idx]);
        std::cout<<" ) + ";
    }
    std::cout<<"( "<<print_128(l.key)<<" ) "<<(l.is_equal?"==":"<=")<<" 0\n";
    }
}

void ls_solver::print_lit_pbs(lit &l){
    __int128_t degree=l.key;
    for(int i=0;i<l.coff_terms.size();i++){degree+=l.coff_terms[i].coff;}
    std::cout<<_num_vars+1<<" "<<print_128(degree)<<" ";
    for(int i=0;i<l.coff_terms.size();i++){std::cout<<print_128(l.coff_terms[i].coff)<<" "<<-(l.coff_terms[i].term_idx+1)<<" ";}
    std::cout<<"0\n";
}

void ls_solver::print_lit_smt(int lit_idx){
    lit *l=&(_lits[std::abs(lit_idx)]);
    if(l->is_nia_lit){
        //TODO:
    }
    else{
        if(lit_idx>0){std::cout<<_vars[l->delta].var_name<<" ";}
        else{std::cout<<"("<<" not "<<_vars[l->delta].var_name<<" ) ";}
    }
}

void ls_solver::print_mv(){
    std::cout<<"(model\n";
    for(uint64_t var_idx=0;var_idx<_num_vars;var_idx++){
        print_mv_vars(var_idx);
    }
    std::cout<<")\n";
}

void ls_solver::print_mv_vars(uint64_t var_idx){
    variable *v=&(_vars[var_idx]);
    __int128_t var_solution=_solution[var_idx];
    std::cout<<"  (define-fun "<<v->var_name<<" () ";
    if(v->is_nia){
        std::cout<<"Int ";
        if(var_solution>=0){std::cout<<print_128(var_solution)<<")\n";}
        else{std::cout<<"(- "<<print_128(-var_solution)<<"))\n";}
    }
    else{
        std::cout<<"Bool ";
        if(var_solution>0){std::cout<<"true )\n";}
        else{std::cout<<"false )\n";}
    }
}

void ls_solver::print_var_solution(std::string &var_name,std::string & var_value){
    uint64_t var_idx=0;
    if(name2var.find(var_name)!=name2var.end()){
        var_idx=name2var[var_name];
        var_value=print_128(_solution[var_idx]);
        return;
    }//the var exists in _vars
    else{
        if(name2tmp_var.find(var_name)!=name2tmp_var.end()){
            int v_idx=(int)name2tmp_var[var_name];
            int new_v_tmp_idx=find(v_idx);
            int new_v_idx=(int)name2var[_tmp_vars[new_v_tmp_idx].var_name];
            var_value=print_128(_solution[new_v_idx]*fa_coff[v_idx]);
        }//a nia var
        else{
            var_value=_resolution_vars[name2resolution_var[var_name]].up_bool>0?"1":"-1";
        }//a boolean var
        return;
    }//the var does not exist in reduced formula
}

std::string ls_solver::print_128(__int128_t n){
    std::stringstream ss;
    if (n==0) return "0";
        if (n<0) {
            ss<<"-";
            n=-n;
        }
        int a[50],ai=0;
        memset(a,0,sizeof a);
        while (n!=0){
            a[ai++]=n%10;
            n/=10;
        }
        for (int i=1;i<=ai;i++) ss<<abs(a[ai-i]);
        return ss.str();
}
void ls_solver::up_bool_vars(){//reconstruct the solution by pop the stack
    for(variable &var:_tmp_vars){
        if(var.is_nia&&name2var.find(var.var_name)==name2var.end()){//if it is an nia var and it is not in the formula
            int var_idx=(int)transfer_name_to_reduced_var(var.var_name, true);//insert it into the vars
            int tmp_var_idx=(int)name2tmp_var[var.var_name];//the idx in tmp_vars
            int new_v_tmp_idx=find(tmp_var_idx);// the root of the var
            if(new_v_tmp_idx!=tmp_var_idx){//it has the root
                int new_v_idx=(int)name2var[_tmp_vars[new_v_tmp_idx].var_name];//the idx of root var in _vars
                _solution[var_idx]=_solution[new_v_idx]*fa_coff[tmp_var_idx];
            }
            else{_solution[var_idx]=0;}
        }
    }//set the var solution
    for(int term_idx=0;term_idx<_terms.size();term_idx++){
        if(!term_appear[term_idx]){
            term *t=&(_terms[term_idx]);
            t->value=1;
            for(var_exp &ve:t->var_epxs){
                ve.var_index=(int)transfer_name_to_reduced_var(_resolution_vars[ve.var_index].var_name, true);
                t->value*=_solution[ve.var_index];
            }
            term_appear[term_idx]=true;
        }//now the var_idx of term is that in the _vars, while the value has updated
    }
    for(int lit_idx=0;lit_idx<_lits.size();lit_idx++){
        if(!lit_appear[lit_idx]&&_lits[lit_idx].is_nia_lit){
            lit_appear[lit_idx]=true;
            delta_lit(_lits[lit_idx]);
        }
    }//now all nia lit has delta
    for(int i=0;i<_resolution_vars.size();i++){if(!_resolution_vars[i].is_nia&&_resolution_vars[i].up_bool==0){_resolution_vars[i].up_bool=-1;}}//set all origin bool var as false
    while(!_reconstruct_stack.empty()){
        clause cl=_reconstruct_stack.top();
        _reconstruct_stack.pop();
        bool sat_flag=false;
        for(int l_idx:cl.literals){
            lit *l=&(_lits[std::abs(l_idx)]);
            if(l->is_nia_lit){
                if(!lit_appear[std::abs(l_idx)]){
                    __int128_t delta=l->delta;
                    for(coff_term& cf:l->coff_terms){
                        if(!term_appear[cf.term_idx]){sat_flag=true;break;}//if the term does not exist, the nia lit can be true
                        else{delta+=(cf.coff*_terms[cf.term_idx].value);}
                    }
                    if(!l->is_equal){if((delta<=0&&l_idx>0)||(delta>0&&l_idx<0)){sat_flag=true;}}
                    else{if((delta==0&&l_idx>0)||(delta!=0&&l_idx<0)){sat_flag=true;}}
                    if(sat_flag==true){break;}
                }//if the nia lit does not exist
                else{
                    if(!l->is_equal){if((l->delta<=0&&l_idx>0)||(l->delta>0&&l_idx<0)){sat_flag=true;break;}}
                    else{if((l->delta==0&&l_idx>0)||(l->delta!=0&&l_idx<0)){sat_flag=true;break;}}
                    //if the nia lit exists
                }
            }
            else{
                if(!lit_appear[std::abs(l_idx)]){
                    if((l_idx>0&&_resolution_vars[l->delta].up_bool>0)||(l_idx<0&&_resolution_vars[l->delta].up_bool<0)){sat_flag=true;break;}}//if the boolean lit does not exist
                else if((_solution[l->delta]>0&&l_idx>0)||(_solution[l->delta]<0&&l_idx<0)){sat_flag=true;break;}
            }
        }
        if(sat_flag==false){
            lit *l=&(_lits[std::abs(cl.literals[0])]);
            _resolution_vars[l->delta].up_bool=1;
        }//if the clause is false, flip the var
    }
}
}
