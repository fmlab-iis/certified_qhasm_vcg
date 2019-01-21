
open Num

val qfbv : unit -> string

type solver = Z3 | Boolector

val default_solver : solver
val string_of_solver : solver -> string

val split_conj : bool ref

val jobs : int ref

val trace : string -> unit

type var = (num * num)

type exp =
  | Var of (int * var)
  | Const of (int * num)
  | Not of (int * exp)
  | And of (int * exp * exp)
  | Or of (int * exp * exp)
  | Xor of (int * exp * exp)
  | Neg of (int * exp)
  | Add of (int * exp * exp)
  | Sub of (int * exp * exp)
  | Mul of (int * exp * exp)
  | Mod of (int * exp * exp)
  | Shl of (int * exp * exp)
  | Shr of (int * exp * exp)
  | Concat of (int * int * exp * exp)
  | Extract of (int * int * int * exp)
  | Slice of (int * int * int * exp)
  | High of (int * int * exp)
  | Low of (int * int * exp)
  | ZeroExtend of (int * int * exp)
  | SignExtend of (int * int * exp)

type bexp =
  | False
  | True
  | Ult of (int * exp * exp)
  | Ule of (int * exp * exp)
  | Ugt of (int * exp * exp)
  | Uge of (int * exp * exp)
  | Eq of (int * exp * exp)
  | Addo of (int * exp * exp)
  | Subo of (int * exp * exp)
  | Mulo of (int * exp * exp)
  | Lneg of bexp
  | Conj of (bexp * bexp)
  | Disj of (bexp * bexp)

val cbool_of_obool : bool -> Constr.t
val obool_of_cbool : Constr.t -> bool
val cnat_of_oint : int -> Constr.t
val oint_of_cnat : Constr.t -> int
val cpos_of_onum : num -> Constr.t
val onum_of_cpos : Constr.t -> num
val cn_of_onum : num -> Constr.t
val onum_of_cn : Constr.t -> num
val cz_of_onum : num -> Constr.t
val onum_of_cz : Constr.t -> num
val cpos_of_ostring : string -> Constr.t
val ostring_of_cpos : Constr.t -> string
val ovar_of_cvar : Constr.t -> var
val oexp_of_cexp : Constr.t -> exp
val obexp_of_cbexp : Constr.t -> bexp
val oimp_of_cimp : Constr.t -> bexp list

val string_of_var : var -> string
val string_of_exp : exp -> string
val string_of_bexp : bexp -> string
val string_of_imp : bexp list -> string

val convert_coq_solver : Globnames.global_reference -> solver
val osolver_of_csolver : Constr.t -> solver

val solve_simp : ?solver:solver -> bexp list -> bool
