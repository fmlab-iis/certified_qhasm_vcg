
type vname = string

type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of (term * term)
  | Sub of (term * term)
  | Mul of (term * term)
  | Pow of (term * int)

val cterm_of_oterm : term -> Constr.t

val oterm_of_cterm : Constr.t -> term

val pdiv : term -> term -> term
