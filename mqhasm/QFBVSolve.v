
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Common Require Import Arch Var Bits Nats SsrOrdered FSets Store.
From mQhasm Require Import bvDSL bvSSA bvSSA2zSSA QFBV bvSSA2QFBV.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Declare ML Module "qf_bv_plugin".

Import QFBV64.

Inductive solver : Set :=
| Z3
| Boolector.

Inductive sexp : Type :=
| sbvVar : nat -> bv64SSA.var -> sexp
| sbvConst : nat -> Z -> sexp
| sbvNot : nat -> sexp -> sexp
| sbvAnd : nat -> sexp -> sexp -> sexp
| sbvOr : nat -> sexp -> sexp -> sexp
| sbvXor : nat -> sexp -> sexp -> sexp
| sbvNeg : nat -> sexp -> sexp
| sbvAdd : nat -> sexp -> sexp -> sexp
| sbvSub : nat -> sexp -> sexp -> sexp
| sbvMul : nat -> sexp -> sexp -> sexp
| sbvMod : nat -> sexp -> sexp -> sexp
| sbvShl : nat -> sexp -> sexp -> sexp
| sbvShr : nat -> sexp -> sexp -> sexp
| sbvConcat : nat -> nat -> sexp -> sexp -> sexp
| sbvExtract : nat -> nat -> nat -> sexp -> sexp
| sbvSlice : nat -> nat -> nat -> sexp -> sexp
| sbvHigh : nat -> nat -> sexp -> sexp
| sbvLow : nat -> nat -> sexp -> sexp
| sbvZeroExtend : nat -> nat -> sexp -> sexp
| sbvSignExtend : nat -> nat -> sexp -> sexp.

Inductive sbexp : Type :=
| sbvFalse : sbexp
| sbvTrue : sbexp
| sbvUlt : nat -> sexp -> sexp -> sbexp
| sbvUle : nat -> sexp -> sexp -> sbexp
| sbvUgt : nat -> sexp -> sexp -> sbexp
| sbvUge : nat -> sexp -> sexp -> sbexp
| sbvEq : nat -> sexp -> sexp -> sbexp
| sbvAddo : nat -> sexp -> sexp -> sbexp
| sbvSubo : nat -> sexp -> sexp -> sbexp
| sbvMulo : nat -> sexp -> sexp -> sbexp
| sbvLneg : sbexp -> sbexp
| sbvConj : sbexp -> sbexp -> sbexp
| sbvDisj : sbexp -> sbexp -> sbexp.

Inductive simp : Type :=
| sbvNil : simp
| sbvCons : sbexp -> simp -> simp.

Ltac abs_exp e :=
  lazymatch e with
  | @bvVar ?v =>
    let w := constr:(AMD64.wordsize) in
    let w := eval compute in w in
    constr:(sbvVar w v)
  | @bvConst ?w ?n =>
    let w := eval compute in w in
    let m := constr:(toPosZ n) in
    let m := eval compute in m in
    constr:(sbvConst w m)
  | @bvNot ?w ?e =>
    let w := eval compute in w in
    let e := abs_exp e in
    constr:(sbvNot w e)
  | @bvAnd ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvAnd w e1 e2)
  | @bvOr ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvOr w e1 e2)
  | @bvXor ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvXor w e1 e2)
  | @bvNeg ?w ?e =>
    let w := eval compute in w in
    let e := abs_exp e in
    constr:(sbvNeg w e)
  | @bvAdd ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvAdd w e1 e2)
  | @bvSub ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvSub w e1 e2)
  | @bvMul ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvMul w e1 e2)
  | @bvMod ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvMod w e1 e2)
  | @bvShl ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvShl w e1 e2)
  | @bvShr ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvShr w e1 e2)
  | @bvConcat ?w1 ?w2 ?e1 ?e2 =>
    let w1 := eval compute in w1 in
    let w2 := eval compute in w2 in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvConcat w1 w2 e1 e2)
  | @bvExtract ?w ?i ?j ?e =>
    let w := eval compute in w in
    let i := eval compute in i in
    let j := eval compute in j in
    let e := abs_exp e in
    constr:(sbvExtract w i j e)
  | @bvSlice ?w1 ?w2 ?w3 ?e =>
    let w1 := eval compute in w1 in
    let w2 := eval compute in w2 in
    let w3 := eval compute in w3 in
    let e := abs_exp e in
    constr:(sbvSlice w1 w2 w3 e)
  | @bvHigh ?w1 ?w2 ?e =>
    let w1 := eval compute in w1 in
    let w2 := eval compute in w2 in
    let e := abs_exp e in
    constr:(sbvHigh w1 w2 e)
  | @bvLow ?w1 ?w2 ?e =>
    let w1 := eval compute in w1 in
    let w2 := eval compute in w2 in
    let e := abs_exp e in
    constr:(sbvLow w1 w2 e)
  | @bvZeroExtend ?w ?i ?e =>
    let w := eval compute in w in
    let i := eval compute in i in
    let e := abs_exp e in
    constr:(sbvZeroExtend w i e)
  | @bvSignExtend ?w ?i ?e =>
    let w := eval compute in w in
    let i := eval compute in i in
    let e := abs_exp e in
    constr:(sbvSignExtend w i e)
  | _ => fail 100
              "Failed to convert the QFBV.exp '" e
              "' to QFBVSolver.sexp: not matched."
  end.

Ltac abs_bexp e :=
  lazymatch e with
  | bvFalse => constr:(sbvFalse)
  | bvTrue => constr:(sbvTrue)
  | @bvUlt ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvUlt w e1 e2)
  | @bvUle ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvUle w e1 e2)
  | @bvUgt ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvUgt w e1 e2)
  | @bvUge ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvUge w e1 e2)
  | @bvEq ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvEq w e1 e2)
  | @bvAddo ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvAddo w e1 e2)
  | @bvSubo ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvSubo w e1 e2)
  | @bvMulo ?w ?e1 ?e2 =>
    let w := eval compute in w in
    let e1 := abs_exp e1 in
    let e2 := abs_exp e2 in
    constr:(sbvMulo w e1 e2)
  | @bvLneg ?e =>
    let e := abs_bexp e in
    constr:(sbvLneg e)
  | @bvConj ?e1 ?e2 =>
    let e1 := abs_bexp e1 in
    let e2 := abs_bexp e2 in
    match e1 with
    | sbvTrue => e2
    | _ => match e2 with
           | sbvTrue => e1
           | _ => constr:(sbvConj e1 e2)
           end
    end
  | @bvDisj ?e1 ?e2 =>
    let e1 := abs_bexp e1 in
    let e2 := abs_bexp e2 in
    match e1 with
    | sbvFalse => e2
    | _ => match e2 with
           | sbvFalse => e1
           | _ => constr:(sbvDisj e1 e2)
           end
    end
  | _ => fail 100
              "Failed to convert the QFBV.bexp '" e
              "' to QFBVSolver.sbexp: not matched."
  end.

Ltac simp_concat es1 es2 :=
  match es1 with
  | sbvNil => es2
  | sbvCons ?e ?es1 =>
    let es2 := simp_concat es1 es2 in
    constr:(sbvCons e es2)
  end.

Ltac abs_conjs es :=
  lazymatch es with
  | ?a /\ ?b =>
    let a := abs_conjs a in
    let b := abs_conjs b in
    match a with
    | sbvTrue => b
    | _ => match b with
           | sbvTrue => a
           | _ => constr:(sbvConj a b)
           end
    end
  | QFBV64.eval_bexp ?a ?s =>
    abs_bexp a
  | True => constr:(sbvTrue)
  end.

Ltac abs_imp g :=
  lazymatch g with
  | ?a -> ?b =>
    let a := abs_conjs a in
    let b := abs_imp b in
    match a with
    | sbvTrue => b
    | _ => constr:(sbvCons a b)
    end
  | ?a =>
    let a := abs_conjs a in
    constr:(sbvCons a sbvNil)
  end.

Ltac bvsimpl :=
  cbv beta iota zeta delta -[
    QFBV64.eval_bexp QFBV64.eval_exp
    fromNat fromPosZ fromZ
  ].

Ltac split_hyps :=
  match goal with
  | H : _ /\ _ |- _ =>
    let H1 := fresh in let H2 := fresh in
    move: H => [H1 H2]; split_hyps
  | |- _ => idtac
  end.

Ltac split_goals := repeat split.

Ltac clear_trivials :=
  match goal with
  | H : True |- _ => clear H; clear_trivials
  | |- _ => idtac
  end.

Ltac gen_bexps :=
  match goal with
  | H : QFBV64.eval_bexp _ _ |- _ => move: H; gen_bexps
  | |- _ => idtac
  end.

Ltac abs :=
  match goal with
  | |- ?g => abs_imp g
  end.

Ltac solve_simp_with s f k :=
  let id := fresh in
  ((solve_simp_ml s id f || fail 100 "Failed to solve on the OCaml side: " f);
  let res := eval compute in id in
  k res).

Ltac solve_simp f k :=
  solve_simp_with Z3 f k || solve_simp_with Boolector f k.

Axiom valid_simp : forall P : Prop, P.

Ltac solve_qfbv_with s :=
  bvsimpl; intro;
  let f := abs in
  solve_simp_with s f ltac:(fun res =>
    match res with
    | true => exact: valid_simp
    | false => fail "Invalid QF_BV formula"
    end
  ).

Ltac solve_qfbv :=
  solve_qfbv_with Z3 || solve_qfbv_with Boolector.