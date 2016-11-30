
From Coq Require Import ZArith.

Inductive term : Set :=
| Zero : term
| Const : Z -> positive -> term
| Var : positive -> term
| Opp : term -> term
| Add : term -> term -> term
| Sub : term -> term -> term
| Mul : term -> term -> term
| Pow : term -> positive -> term.

Declare ML Module "polyop_plugin".

Ltac pdiv p c k :=
  let id := fresh in
  pdiv_ml id p c;
  let res := eval compute in id in
  k res.
