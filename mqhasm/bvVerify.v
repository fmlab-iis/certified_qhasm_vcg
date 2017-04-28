
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Common Require Import Arch Var Bits Nats SsrOrdered FSets Store.
From mQhasm Require Import zDSL zSSA zPoly bvDSL bvSSA bvSSA2zSSA QFBV bvSSA2QFBV QFBVSolve zVerify Options.
From GBArith Require Import GBZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** bvspec - specification with specified input variables *)

Definition bvspec : Type := (bv64DSL.VS.t * bv64DSL.spec).

Definition valid_bvspec (s : bvspec) : Prop :=
  bv64DSL.well_formed_spec (fst s) (snd s) /\ bv64DSL.valid_spec (snd s).



(* We need to convert bv64DSL.VS.t to zDSL.VS.t. *)
Module M2 := Map2 bv64DSL.VS zDSL.VS.
Definition bvdsl2zdsl_vars (vs : bv64DSL.VS.t) : zDSL.VS.t :=
  M2.map2 id vs.

Ltac get_smt_solver o :=
  let a := constr:((opt_z3 o, opt_boolector o)) in
  let a := eval compute in a in
  let a :=
      match a with
      | (true, _) => QFBVSolve.Z3
      | (_, true) => QFBVSolve.Boolector
      | _ => fail 100 "No SMT solver is selected."
      end in
  a.

Ltac verify_qfbv_with o :=
  let a := get_smt_solver o in
  bvsimpl; solve_qfbv_with a.

(* Prove bv2z_bexp_safe_at with SMT solvers. *)
Ltac verify_bexp_safe_with o :=
  let a := get_smt_solver o in
  lazymatch goal with
  | |- forall s, is_true (bv2z_bexp_safe_at ?e s) =>
    intro s; verify_bexp_safe_with o
  | |- is_true (bv2z_bexp_safe_at ?e ?s) =>
    apply: eval_bexp_bexp_safe1; bvsimpl; solve_qfbv_with a
  | |- _ => fail 100 "Failed to prove bv2z_bexp_safe_at: goal does not match"
  end.

(* Prove that program is safe. *)
Ltac verify_program_safe_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      lazymatch goal with
      | |- forall s, bv64SSA.eval_bexp ?pre s ->
                     is_true (bv2z_program_safe_at ?prog s) =>
        apply: (@eval_bexp_program_safe1 (ssa_vars empty_vmap vs));
        [
          (* ssa_vars_unchanged_program *)
          done
        |
          (* well_formed_ssa_program *)
          done
        |
          (* implication of QFBV64.eval_bexp *)
          verify_qfbv_with o || fail 100 "Failed to prove bv2z_program_safe_at"
        ]
      | |- _ => fail 100 "Failed to prove bv2z_program_safe_at: goal does not match"
      end in
  match b with
  | true => time "verify_program_safe" (tac unit)
  | false => tac unit
  end.

(* Prove specifications regarding ranges. *)
Ltac verify_spec_rng_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      match goal with
      | |- bv64SSA.valid_spec ?s =>
        apply: (@bexp_spec_sound_imp (bvSSA.ssa_vars bvSSA.empty_vmap vs));
        [
          (* well_formed_ssa_spec *)
          done
        |
          (*  valid_bexp_spec_imp *)
          verify_qfbv_with o || fail 100 "Failed to prove bv2z_spec_rng"
        ]
      | |- _ => fail 100 "Failed to verify bv2z_spec_rng: goal does not match"
      end in
  match b with
  | true => time "verify_spec_rng" (tac unit)
  | false => tac unit
  end.

(* We need to fold (toPosZ (fromPosZ _)) to do rewriting.
   Otherwise, Coq freezes. *)
Definition toPosZfromPosZ w n := toPosZ (@fromPosZ w n).

Ltac fold_toPosZfromPosZ :=
  match goal with
  | |- context f [toPosZ (@fromPosZ ?n ?c)] =>
    fold (toPosZfromPosZ n c)
  end.

Ltac rewrite_toPosZfromPosZ :=
  match goal with
  | |- context f [toPosZfromPosZ ?n ?c] =>
    let m := constr:(toPosZfromPosZ n c) in
    let m := eval compute in m in
    have: toPosZfromPosZ n c = m;
    [done | move=> ->]
  end.

Ltac rewrite_toNatfromNat :=
  rewrite toNat_fromNatBounded; last by done.

Ltac rewrite_bv2z_consts :=
  repeat fold_toPosZfromPosZ; repeat rewrite_toPosZfromPosZ;
  repeat rewrite_toNatfromNat.

(* Convert bv2z_spec_poly to polynomials. *)
Ltac bv2zspec_to_poly_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      lazymatch goal with
      | |- zSSA.valid_spec (bv2z_spec_poly (bvSSA.ssa_spec ?spec)) =>
        apply: (zPoly.bexp_spec_sound
                  (vs:=zSSA.ssa_vars zSSA.empty_vmap (bvdsl2zdsl_vars vs)));
        [ (* well_formed_ssa_spec *)
          done
        | bvzsimpl; rewrite_bv2z_consts; intros;
          repeat (remove_exists_hyp || split_conj); clear_true
        ]
      | |- _ => fail 100 "Tactic bv2z_spec_to_poly fails: goal does not match"
      end in
  match b with
  | true => time "bv2zspec_to_poly" (tac unit)
  | false => tac unit
  end.

Tactic Notation "bv2zspec_to_poly" constr(vs) :=
  bv2zspec_to_poly_with default_options vs.

Ltac verify_bv2zssa_with o vs :=
  bv2zspec_to_poly_with o vs; to_assign_with o;
  rewrite_assign_with o; rewrite_equality_with o; solve_zspec_with o.

Tactic Notation "verify_bv2zssa" constr(vs) :=
  verify_bv2zssa_with default_options vs.

Ltac verify_bvdsl_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  lazymatch goal with
  | |- bv64DSL.valid_spec ?sp =>
    apply: ssa_spec_sound; apply: bv2z_spec_sound;
    [
      (* bv2z_spec_safe *)
      apply: (bv2z_spec_safe_qfbv1 (vs := (bvSSA.ssa_vars bvSSA.empty_vmap vs)));
      [
        (* well_formed_ssa_spec *)
        done
      |
        (* bv2z_spec_safe_qfbv *)
        split; last split;
        [
          (* bv2z_spre_safe_qfbv *)
          (match b with
           | true => time "bv2z_spre_safe_qfbv" (verify_qfbv_with o)
           | false => (verify_qfbv_with o)
           end)
        |
          (* bv2z_sprog_safe_qfbv *)
          (match b with
           | true => time "bv2z_sprog_safe_qfbv" (verify_qfbv_with o)
           | false => (verify_qfbv_with o)
           end)
        |
          (* bv2z_spost_safe_qfbv *)
          (match b with
           | true => time "bv2z_spost_safe_qfbv" (verify_qfbv_with o)
           | false => (verify_qfbv_with o)
           end)
        ]
      ]
    |
      (* valid bv2z_spec_rng *)
      verify_spec_rng_with o vs
    |
      (* valid_spec on the zSSA side *)
      verify_bv2zssa_with o vs
    ]
  | |- _ => fail 100 "Tactic verify_bvdsl_with fails: goal does not match"
  end.

Tactic Notation "verify_bvdsl" constr(vs) := verify_bvdsl_with default_options vs.
Tactic Notation "verify_bvdsl" constr(vs) "with" constr(opts) := verify_bvdsl_with (oconf opts) vs.

Ltac verify_bvspec_with o :=
  lazymatch goal with
  | |- valid_bvspec (?vs, ?sp) =>
    split; [
      (* well_formed_spec *)
      done || fail 100 "The specification is not well-formed."
    |
      (* valid_spec *)
      verify_bvdsl_with o vs
    ]
  | |- _ => fail 100 "Tactic verify_bvspec_with fails: goal does not match"
  end.

Tactic Notation "verify_bvspec" := verify_bvspec_with default_options.
Tactic Notation "verify_bvspec" "with" constr(opts) := verify_bvspec_with (oconf opts).
