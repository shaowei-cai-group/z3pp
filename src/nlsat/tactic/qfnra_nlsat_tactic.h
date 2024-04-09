/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_nlsat_tactic.h

Abstract:

    Tactic based on nlsat for solving QF_NRA problems

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

// //#linxi begin preprocess tactic
// tactic * linxi_mk_qfnra_preprocess_tactic(ast_manager & m, params_ref const& p);
// //#linxi end preprocess tactic


tactic * mk_qfnra_nlsat_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_qfnra_local_search_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("qfnra-nlsat", "builtin strategy for solving QF_NRA problems using only nlsat.", "mk_qfnra_nlsat_tactic(m, p)")
*/

