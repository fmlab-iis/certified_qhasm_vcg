
(*i camlp4deps: "parsing/grammar.cma" i*)

open Qf_bv

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "qf_bv_plugin"

let solve_simp_tac csolver csplit cjobs cid cimp =
    try
        let osolver = convert_coq_solver csolver in
        let _ = split_conj := obool_of_cbool csplit in
        let _ = jobs := Num.int_of_num (onum_of_cpos cjobs) in
        let _ = trace ("Solver: " ^ string_of_solver osolver) in
        let _ = trace ("isafety: " ^ string_of_bool !split_conj) in
        let _ = trace ("jobs: " ^ string_of_int !jobs) in
        let oimp = oimp_of_cimp cimp in
        let res = cbool_of_obool (solve_simp ~solver:osolver oimp) in
        Tactics.letin_tac None (Names.Name cid) (EConstr.of_constr res) None Locusops.nowhere
    with _ ->
         Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str "Failed"))

TACTIC EXTEND qfbv
| ["solve_simp_ml" reference(solver) constr(split) constr(jobs) ident(id) constr(imp)] ->
    [solve_simp_tac solver (EConstr.Unsafe.to_constr split) (EConstr.Unsafe.to_constr jobs) id (EConstr.Unsafe.to_constr imp)]
END
