
val qfbv : unit -> string

type solver = Z3 | Boolector

val default_solver : solver
val trace : string -> unit
val solve_simp : ?solver:solver -> Constr.t -> Constr.t
(*
type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of (term * term)
  | Sub of (term * term)
  | Mul of (term * term)
  | Pow of (term * int)

val default_engine : engine

val convert_coq_engine : Globnames.global_reference -> engine

val cterm_of_oterm : term -> Constr.t

val oterm_of_cterm : Constr.t -> term

val pdiv : ?engine:engine -> term -> term -> term
*)
