Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From mQhasm Require Import mQhasm SSA PolyGen.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope mqhasm_scope.

Definition ispec : Type := (VS.t * Qhasm.spec).

Definition valid_ispec (s : ispec) : Prop :=
  well_formed_spec (fst s) (snd s) /\ valid_spec (snd s).

From GBArith Require Import GBZ GBZArith.

Ltac split_conjs :=
  match goal with
  | H: _ /\ _ |- _ =>
    let H1 := fresh in
    let H2 := fresh in
    move: H => [H1 H2]; split_conjs
  | |- _ => idtac
  end.

Ltac clear_true :=
  match goal with
  | H: True |- _ => clear H; clear_true
  | _ => idtac
  end.

Ltac rename_variables :=
  match goal with
  | |- context f [ ?s (?v, ?i) ] =>
    let x := fresh "x" in
    set x := s (v, i); rename_variables
  | |- _ => idtac
  end.

Ltac unfold_ispec :=
  match goal with
  | |- valid_ispec ?ispec =>
    split; [
      by done || fail "The specification is not well formed" |
      apply: ssa_spec_sound;
      apply: (bexp_spec_sound (vs:=ssa_vars empty_vmap (fst ispec))); [
        by done |
        rewrite /valid_bexp_spec /=
                /ssa_var /get_index /initial_index /first_assigned_index;
          simplZ; intros; split_conjs; clear_true
      ]
    ]
  end.

Definition opaque_eq (S : Type) (x y : S) := x = y.

Lemma lock_eq : forall (S : Type) (x y : S), x = y -> opaque_eq x y.
Proof.
  done.
Qed.

Lemma unlock_eq : forall (S : Type) (x y : S), opaque_eq x y -> x = y.
Proof.
  done.
Qed.

Ltac lock_hyp H :=
  move: (lock_eq H); clear H; move=> H.

Ltac unlock_hyp H :=
  move: (unlock_eq H); clear H; move=> H.

Ltac unlock_hyps :=
  match goal with
  | H: opaque_eq _ _ |- _ => unlock_hyp H; unlock_hyps
  | |- _ => idtac
  end.

Ltac gen_eqs :=
  match goal with
  | H: _ = _ |- _ => move: H; gen_eqs
  | |- _ => idtac
  end.

Ltac rewrite_assign :=
  match goal with
  | st: N * N -> value |- _ =>
    match goal with
    | H: st _ = _ |- _ =>
      lock_hyp H; gen_eqs; unlock_hyp H; (try rewrite H);
      clear H; intros; rewrite_assign
    | |- _ => idtac
    end
  end.

From Coq Require Import Nsatz.

Ltac solve_ispec :=
  match goal with
  | |- _ = _ => nsatz
  | |- exists _, _ = _ => gbarith
  end.

Ltac verify_ispec := unfold_ispec; rewrite_assign; solve_ispec.
