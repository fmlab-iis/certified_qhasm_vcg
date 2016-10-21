Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
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

Ltac unfold_ispec :=
  match goal with
  | |- valid_ispec ?ispec =>
    let H := fresh in
    have: (well_formed_spec (fst ispec) (snd ispec)); [
        by done || fail "The specification is not well formed" |
        move=> H;
          split; [
            by exact: H |
            apply: ssa_spec_sound; apply: bexp_spec_sound; [
              exact: (ssa_spec_well_formed H) |
              clear H;
              progress repeat rewrite /valid_bexp_spec /=
                       /ssa_var /get_index /initial_index /first_assigned_index;
              simplZ; intros; split_conjs; clear_true
            ]
          ]
      ]
  end.

Ltac solve_ispec :=
  match goal with
  | |- _ = _ => gbZ
  | |- exists _, _ = _ => gbarith
  end.

Ltac verify_ispec := unfold_ispec; solve_ispec.
