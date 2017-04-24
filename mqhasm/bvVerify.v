
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Common Require Import Arch Var Bits Nats SsrOrdered FSets Store.
From mQhasm Require Import bvDSL bvSSA bvSSA2zSSA QFBV bvSSA2QFBV QFBVSolve.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Ltac verify_bexp_safe :=
  lazymatch goal with
  | |- forall s, is_true (bv2z_bexp_safe_at ?e s) =>
    intro s; verify_bexp_safe
  | |- is_true (bv2z_bexp_safe_at ?e ?s) =>
    apply: eval_bexp_bexp_safe1; bvsimpl; verify_qfbv
  | |- _ => fail 100 "Failed to prove bv2z_bexp_safe_at: goal does not match"
  end.

Ltac verify_program_safe inputs :=
  lazymatch goal with
  | |- forall s, bv64SSA.eval_bexp ?pre s ->
                 is_true (bv2z_program_safe_at ?prog s) =>
    apply: (@eval_bexp_program_safe1 (ssa_vars empty_vmap inputs));
    [
      (* ssa_vars_unchanged_program *)
      done
    |
      (* well_formed_ssa_program *)
      done
    |
      (* implication of QFBV64.eval_bexp *)
      verify_qfbv || fail 100 "Failed to prove bv2z_program_safe_at"
    ]
  | |- _ => fail 100 "Failed to prove bv2z_program_safe_at: goal does not match"
  end.

Ltac verify_spec_rng inputs :=
  match goal with
  | |- bv64SSA.valid_spec ?s =>
    apply: (@bexp_spec_sound_imp (ssa_vars empty_vmap inputs));
    [
      (* well_formed_ssa_spec *)
      done
    |
      (*  valid_bexp_spec_imp *)
      verify_qfbv || fail 100 "Failed to prove bv2z_spec_rng"
    ]
  | |- _ => fail 100 "Failed to verify bv2z_spec_rng: goal does not match"
  end.

Ltac verify_bvdsl inputs :=
  match goal with
  | |- bv64DSL.valid_spec ?sp =>
    apply: ssa_spec_sound; apply: bv2z_spec_sound;
    [
      (* spec_safe *)
      split; last split;
      [
        (* program_safe *)
        verify_program_safe inputs
      |
        (* bexp_safe precondition *)
        verify_bexp_safe || fail 100 "Failed to prove bexp_safe for precondition"
      |
        (* bexp_safe postcondition *)
        verify_bexp_safe || fail 100 "Failed to prove bexp_safe for postcondition"
      ]
    |
      (* rng_safe *)
      verify_spec_rng inputs
    |
      (* valid_spec on the zDSL side *)
      idtac
    ]
  end.
