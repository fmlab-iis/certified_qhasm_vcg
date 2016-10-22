
(** * Sequential integer programs *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From Common Require Import ZAriths Types Var Env Store.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Syntax *)

Inductive exp : Set :=
| SVar : var -> exp
| SConst : Z -> exp
| SAdd : exp -> exp -> exp
| SSub : exp -> exp -> exp
| SMul : exp -> exp -> exp
| SDiv : exp -> exp -> exp
| SMod : exp -> exp -> exp.

Inductive instr : Set :=
| SAssign : var -> exp -> instr.

Definition program : Set := seq instr.



(** Semantics *)

Module State := TStoreAdapter NOrder ZType.

Fixpoint eval_exp (e : exp) (s : State.t) : Z :=
  match e with
  | SVar v => State.acc v s
  | SConst n => 0 (* tbd *)
  | SAdd e1 e2 => 0 (* tbd *)
  | SSub e1 e2 => 0 (* tbd *)
  | SMul e1 e2 => 0 (* tbd *)
  | SDiv e1 e2 => 0 (* tbd *)
  | SMod e1 e2 => 0 (* tbd *)
  end.

Definition eval_instr (i : instr) (s : State.t) : State.t :=
  match i with
  | SAssign v e => State.upd v (eval_exp e s) s
  end.

Fixpoint eval_program (p : program) (s : State.t) : State.t :=
  match p with
  | nil => s
  | hd::tl => eval_program tl (eval_instr hd s)
  end.

Lemma eval_program_concat :
  forall (p1 p2 : program) (s : State.t),
    eval_program (p1 ++ p2) s = eval_program p2 (eval_program p1 s).
Proof.
  induction p1.
  - reflexivity.
  - move=> p2 s.
    exact: IHp1.
Qed.
