
val qfbv : unit -> string

type solver = Z3 | Boolector

val default_solver : solver

val trace : string -> unit

val convert_coq_solver : Globnames.global_reference -> solver

val solve_simp : ?solver:solver -> Constr.t -> Constr.t
