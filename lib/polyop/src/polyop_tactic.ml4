
(*i camlp4deps: "parsing/grammar.cma" i*)

open Polyop

open Num

open Globnames
open Glob_term
open Proofview.Notations
open Tacexpr
open Tacinterp

DECLARE PLUGIN "polyop_plugin"

let pdiv_tac id p c =
  Proofview.Goal.enter (fun gl ->
    try
      let op = oterm_of_cterm p in
      let oc = oterm_of_cterm c in
      let owit = pdiv op oc in
      let wit = cterm_of_oterm owit in
      Tactics.letin_tac None (Names.Name id) wit None Locusops.nowhere
    with _ ->
      Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str ("Failed")))
  )
TACTIC EXTEND modp
| ["pdiv_ml" ident(id) constr(p) constr(c)] -> [pdiv_tac id p c]
END
