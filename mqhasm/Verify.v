Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From mQhasm Require Import mQhasm SSA PolyGen.
From GBArith Require Import GBCompute.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope mqhasm_scope.

(** Options *)

Record verify_options : Set :=
  mkOptions { opt_split : bool;
              opt_slicing : bool;
              opt_gb : gb_algorithm }.

Definition default_options : verify_options :=
  {| opt_split := true;
     opt_slicing := false;
     opt_gb := SingularZ |}.

Definition options_none : verify_options :=
  {| opt_split := false;
     opt_slicing := false;
     opt_gb := SingularZ |}.

Definition options_all : verify_options :=
  {| opt_split := true;
     opt_slicing := true;
     opt_gb := SingularZ |}.

Inductive bool_flag : Set :=
| Split
| Slicing.

Inductive vflag : Set :=
| With : bool_flag -> vflag
| Without : bool_flag -> vflag
| GB : gb_algorithm -> vflag.

Definition set_bool_flag f b o : verify_options :=
  match f with
  | Split => {| opt_split := b;
                opt_slicing := opt_slicing o;
                opt_gb := opt_gb o |}
  | Slicing => {| opt_split := opt_split o;
                  opt_slicing := b;
                  opt_gb := opt_gb o |}
  end.

Definition set_vflag f o : verify_options :=
  match f with
  | With g => set_bool_flag g true o
  | Without g => set_bool_flag g false o
  | GB alg => {| opt_split := opt_split o;
                 opt_slicing := opt_slicing o;
                 opt_gb := alg |}
  end.

Definition vconfig_with flags o : verify_options :=
  foldr set_vflag o flags.

Definition vconfig flags : verify_options :=
  vconfig_with flags default_options.



(** ispec *)

Definition ispec : Type := (VS.t * Qhasm.spec).

Definition valid_ispec (s : ispec) : Prop :=
  well_formed_spec (fst s) (snd s) /\ valid_spec (snd s).



(** Tactics *)

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

Ltac apply_spec_split_post o :=
  let b := constr:(opt_split o) in
  let b := eval compute in b in
  match b with
  | true => repeat apply: spec_split_post
  | false => idtac
  end.

Ltac apply_qslice_sound o :=
  let b := constr:(opt_slicing o) in
  let b := eval compute in b in
  match b with
  | true => apply: qslice_sound; rewrite /qslice /slice_pre /=
  | false => idtac
  end.

Ltac unfold_ispec_with o :=
  match goal with
  | |- valid_ispec ?ispec =>
    split; [
      by done || fail "The specification is not well formed" |
      apply_spec_split_post o;
      (apply_qslice_sound o;
      apply: ssa_spec_sound;
      apply: (bexp_spec_sound (vs:=ssa_vars empty_vmap (fst ispec))); [
        by done |
        simplZ; intros; split_conjs; clear_true
      ])
    ]
  end.

Tactic Notation "unfold_ispec" := unfold_ispec_with default_options.

Definition opaque_eq (S : Type) (x y : S) := x = y.

Ltac lock_hyp H :=
  match type of H with
  | ?x = ?y => fold (opaque_eq x y) in H
  end.

Ltac unlock_hyp H :=
  unfold opaque_eq in H.

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
  | st: _ -> value |- _ =>
    match goal with
    | H: st _ = _ |- _ =>
      ( try rewrite -> H in * ); clear H; rewrite_assign
    | |- _ => idtac
    end
  end.

Ltac rewrite_equality :=
  match goal with
  | H: _ = _ |- _ =>
    ( try rewrite -> H in * ); move: H; rewrite_equality
  | |- _ => intros
  end.

From Coq Require Import Nsatz.

Ltac gbarith_with o :=
  let a := constr:(opt_gb o) in
  let a := eval compute in a in
  gbarith_choice a.

Ltac solve_ispec_with o :=
  match goal with
  | |- _ /\ _ => split; solve_ispec_with o
  | |- exists _, _ = _ => gbarith_with o
  | |- modulo _ _ _ => gbarith_with o
  | |- _ = _ => nsatz
  end.

Tactic Notation "solve_ispec" := solve_ispec_with default_options.

Ltac verify_bexp_with o :=
  match goal with
  | |- valid (QEq _ _) => move=> s; simplZ; nsatz
  | |- _ = _ => nsatz
  | |- valid (QCong _ _ _) => move=> s; simplZ; gbarith_with o
  | |- modulo _ _ _ => gbarith_with o
  | |- exists k : Z, (_ - _)%Z = (k * _)%Z => gbarith_with o
  | |- valid (QAnd _ _) => split; verify_bexp_with o
  | |- _ /\ _ => split; verify_bexp_with o
  end.

Tactic Notation "verify_bexp" := verify_bexp_with default_options.

Ltac verify_entail_with o :=
  match goal with
  | |- ?f ===> ?g =>
    let H := fresh in
    simplZ; move=> s H; split_conjs; clear_true;
    rewrite_assign; rewrite_equality; verify_bexp_with o
  end.

Tactic Notation "verify_entail" := verify_entail_with default_options.

Ltac verify_ispec_with o :=
  unfold_ispec_with o; rewrite_assign; rewrite_equality; solve_ispec_with o.

Tactic Notation "verify_ispec" := verify_ispec_with default_options.

Ltac verify_spec_with o vs :=
  match goal with
  | |- valid_spec ?spec =>
    have: valid_ispec (vs, spec);
      [ verify_ispec_with o |
        let H := fresh in
        move=> [_ H]; exact: H
      ]
  end.

Tactic Notation "verify_spec" constr(vs) := verify_spec_with default_options vs.
