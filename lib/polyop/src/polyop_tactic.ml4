
(*i camlp4deps: "parsing/grammar.cma" i*)

open Polyop

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "polyop_plugin"

let pdiv_tac eng id p c =
  Proofview.Goal.enter (fun gl ->
    try
      let op = oterm_of_cterm p in
      let oeng = convert_coq_engine eng in
      let oc = oterm_of_cterm c in
      let owit = pdiv ~engine:oeng op oc in
      let wit = cterm_of_oterm owit in
      Tactics.letin_tac None (Names.Name id) (EConstr.of_constr wit) None Locusops.nowhere
    with _ ->
      Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str ("Failed")))
  )
TACTIC EXTEND modp
| ["pdiv_ml" reference(eng) ident(id) constr(p) constr(c)] -> [pdiv_tac eng id (EConstr.Unsafe.to_constr p) (EConstr.Unsafe.to_constr c)]
END
