
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Common Require Import Arch Var Bits Nats SsrOrdered FSets Store.
From mQhasm Require Import zDSL zSSA zPoly bvDSL bvSSA bvSSA2zSSA QFBV bvSSA2QFBV QFBVSolve zVerify Options.
From GBArith Require Import GBZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** bvspec - specification with specified input variables *)

Definition bvspec : Type := (VS.t * bv64DSL.spec).

Definition valid_bvspec (s : bvspec) : Prop :=
  bv64DSL.well_formed_spec (fst s) (snd s) /\ bv64DSL.valid_spec (snd s).

Ltac verify_qfbv_with o :=
  bvsimpl; solve_qfbv_with o.

(* Prove that program is safe. *)
Ltac verify_program_safe_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      lazymatch goal with
      | |- forall s, bv64SSA.eval_bexp ?pre s ->
                     is_true (bv2z_program_safe_at ?prog s) =>
        time "bvVerify: verify_program_safe_with: apply theorem" (apply: (@eval_bexp_program_safe1 (ssa_vars empty_vmap vs)));
        [
          (* ssa_vars_unchanged_program *)
          time "bvVerify: verify_program_safe_with: ssa_vars_unchanged_program" done
        |
          (* well_formed_ssa_program *)
          time "bvVerify: verify_program_safe_with: well_formed_ssa_program" done
        |
          (* implication of QFBV64.eval_bexp *)
          time "bvVerify: verify_program_safe_with: verify_qfbv_with" verify_qfbv_with o || fail 100 "bvVerify: failed to prove bv2z_program_safe_at"
        ]
      | |- _ => fail 100 "bvVerify: verify_program_safe_with: goal does not match"
      end in
  match b with
  | true => time "bvVerify: verify_program_safe_with" (tac unit)
  | false => tac unit
  end.

Ltac verify_spec_safe_with o ssa_vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      (* bv2z_spec_safe *)
      time "bvVerify: verify_spec_safe_with: apply theorem" (apply: (@bv2z_spec_safe_qfbv1 ssa_vs));
      [
        (* well_formed_ssa_spec *)
        time "bvVerify: verify_spec_safe_with: well_formed_ssa_spec" done
      |
        (* bv2z_spec_safe_qfbv *)
        (match b with
         | true => time "bvVerify: verify_spec_safe_with: verify_qfbv_with" (verify_qfbv_with o)
         | false => (verify_qfbv_with o)
         end) || fail 100 "bvVerify: verify_spec_safe_with: verify_qfbv_with fails"
      ] in
  match b with
  | true => time "bvVerify: verify_spec_safe_with" (tac unit)
  | false => tac unit
  end.

(* Prove specifications regarding ranges. *)
Ltac verify_spec_rng_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      match goal with
      | |- bv64SSA.valid_rspec ?s =>
        time "bvVerify: verify_spec_rng_with: apply theorem" (apply: (@bexp_spec_sound_imp (bvSSA.ssa_vars bvSSA.empty_vmap vs)));
        [
          (* well_formed_ssa_spec *)
          time "bvVerify: verify_spec_rng_with: well_formed_ssa_spec" done
        |
          (*  valid_bexp_spec_imp *)
          time "bvVerify: verify_spec_rng_with: verify_qfbv_with" verify_qfbv_with o || fail 100 "Failed to prove bv2z_spec_rng"
        ]
      | |- _ => fail 100 "bvVerify: verify_spec_rng_with: goal does not match"
      end in
  match b with
  | true => time "bvVerify: verify_spec_rng_with" (tac unit)
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
Ltac bv2zspec_to_poly_with o :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let tac _ :=
      lazymatch goal with
      | |- zSSA.valid_spec (bv2z_spec_eqn ?ssa_vs (bvSSA.ssa_spec ?spec)) =>
        time "bvVerify: bv2zspec_to_poly_with: apply theorem" (apply: (@zPoly.bexp_spec_sound ssa_vs));
        [ (* well_formed_ssa_spec *)
          time "bvVerify: bv2zspec_to_poly_with: well_formed_ssa_spec" done
        | time "bvVerify: bv2zspec_to_poly_with: simplify goal"
               (bvzsimpl; rewrite_bv2z_consts; intros;
                repeat (remove_exists_hyp || split_conj); clear_true)
        ]
      | |- _ => fail 100 "bvVerify: bv2zspec_to_poly_with: goal does not match"
      end in
  match b with
  | true => time "bvVerify: bv2zspec_to_poly_with" (tac unit)
  | false => tac unit
  end.

Tactic Notation "bv2zspec_to_poly" :=
  bv2zspec_to_poly_with default_options.

(* zVerify does not accept Zpower_nat. *)
Ltac rewrite_zpower_nat :=
  gen_eqs; (rewrite !Zpower_nat_Z || idtac); simplZ; intros .

Ltac verify_bv2zssa_with o :=
  bv2zspec_to_poly_with o; to_assign_with o;
  rewrite_assign_with o; rewrite_equality_with o;
  rewrite_zpower_nat; solve_zspec_with o.

Tactic Notation "verify_bv2zssa" :=
  verify_bv2zssa_with default_options.

Ltac verify_bvdsl_with o vs :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let ssa_vs := constr:(bvSSA.ssa_vars bvSSA.empty_vmap vs) in
  lazymatch goal with
  | |- bv64DSL.valid_spec ?sp =>
    apply: ssa_spec_sound; apply: (@bv2z_spec_sound ssa_vs);
    [
      (* spec safe *)
      verify_spec_safe_with o ssa_vs
    |
      (* valid bv2z_spec_rng *)
      verify_spec_rng_with o vs
    |
      (* valid_spec on the zSSA side *)
      verify_bv2zssa_with o
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
