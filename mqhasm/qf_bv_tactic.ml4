
(*i camlp4deps: "parsing/grammar.cma" i*)

open Qf_bv

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "qf_bv_plugin"

let solve_simp_tac s id f =
    try
        let s = convert_coq_solver s in
        let res = solve_simp ~solver:s f in
        Tactics.letin_tac None (Names.Name id) (EConstr.of_constr res) None Locusops.nowhere
    with _ ->
         Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str "Failed"))

TACTIC EXTEND qfbv
| ["solve_simp_ml" reference(s) ident(id) constr(f)] -> [solve_simp_tac s id (EConstr.Unsafe.to_constr f)]
END
