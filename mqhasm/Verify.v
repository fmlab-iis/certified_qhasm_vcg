
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From mQhasm Require Import mQhasm SSA PolyGen.
From GBArith Require Import GBCompute.
From PolyOp Require Import Modp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope mqhasm_scope.

(** Options *)

(*
  - opt_split: split postcondition at specification level,
               good for slicing, bad for rewriting a lot of assignments
  - opt_slicing: apply slicing before converting to SSA
  - opt_to_assign: rewrite equations (e1 = e2) to assignment form (x = e)
  - opt_lazy: use Lazy to do simplification
  - opt_native: use native_compute to do simplification
  - opt_singular: use Singular to do polynomial operations
  - opt_magma: use Magma to do polynomial operations
  - opt_profiling: print some timing information
*)
Record verify_options : Set :=
  mkOptions { opt_split : bool;
              opt_slicing : bool;
              opt_to_assign : bool;
              opt_lazy : bool;
              opt_native : bool;
              opt_singular : bool;
              opt_magma : bool;
              opt_profiling : bool }.

Definition default_options : verify_options :=
  {| opt_split := true;
     opt_slicing := false;
     opt_to_assign := true;
     opt_lazy := false;
     opt_native := true;
     opt_singular := true;
     opt_magma := false;
     opt_profiling := true |}.

Inductive bool_flag : Set :=
| Split
| Slicing
| ToAssign
| Lazy
| Native
| Singular
| Magma
| Profiling.

Inductive vflag : Set :=
| With : bool_flag -> vflag
| Without : bool_flag -> vflag.

Definition set_bool_flag f b o : verify_options :=
  match f with
  | Split => {| opt_split := b;
                opt_slicing := opt_slicing o;
                opt_to_assign := opt_to_assign o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := opt_singular o;
                opt_magma := opt_magma o;
                opt_profiling := opt_profiling o |}
  | Slicing => {| opt_split := opt_split o;
                  opt_slicing := b;
                  opt_to_assign := opt_to_assign o;
                  opt_lazy := opt_lazy o;
                  opt_native := opt_native o;
                  opt_singular := opt_singular o;
                  opt_magma := opt_magma o;
                  opt_profiling := opt_profiling o |}
  | ToAssign => {| opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := b;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := opt_singular o;
                   opt_magma := opt_magma o;
                   opt_profiling := opt_profiling o |}
  | Lazy => {| opt_split := opt_split o;
               opt_slicing := opt_slicing o;
               opt_to_assign := opt_to_assign o;
               opt_lazy := b;
               opt_native := opt_native o;
               opt_singular := opt_singular o;
               opt_magma := opt_magma o;
               opt_profiling := opt_profiling o |}
  | Native => {| opt_split := opt_split o;
                 opt_slicing := opt_slicing o;
                 opt_to_assign := opt_to_assign o;
                 opt_lazy := opt_lazy o;
                 opt_native := b;
                 opt_singular := opt_singular o;
                 opt_magma := opt_magma o;
                 opt_profiling := opt_profiling o |}
  | Singular => {| opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := opt_to_assign o;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := b;
                   opt_magma := opt_magma o;
                   opt_profiling := opt_profiling o |}
  | Magma => {| opt_split := opt_split o;
                opt_slicing := opt_slicing o;
                opt_to_assign := opt_to_assign o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := opt_singular o;
                opt_magma := b;
                opt_profiling := opt_profiling o |}
  | Profiling => {| opt_split := opt_split o;
                    opt_slicing := opt_slicing o;
                    opt_to_assign := opt_to_assign o;
                    opt_lazy := opt_lazy o;
                    opt_native := opt_native o;
                    opt_singular := opt_singular o;
                    opt_magma := opt_magma o;
                    opt_profiling := b |}
  end.

Definition set_vflag f o : verify_options :=
  match f with
  | With g => set_bool_flag g true o
  | Without g => set_bool_flag g false o
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

Ltac split_conj :=
  match goal with
  | H: _ /\ _ |- _ =>
    let H1 := fresh in
    let H2 := fresh in
    move: H => [H1 H2]
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

Ltac lsimplZ :=
  lazy beta iota zeta delta
  -[Zmult Zplus Zpower Z.pow_pos Zminus Zopp Zdiv Zmod].

Ltac simplZ_with o :=
  let c := constr:((opt_lazy o, opt_native o)) in
  let c := eval compute in c in
  match c with
  | (false, false) => simplZ
  | _ => lsimplZ
  end.

Ltac simpl_with o :=
  let c := constr:((opt_lazy o, opt_native o)) in
  let c := eval compute in c in
  match c with
  | (true, _) => lazy
  | (false, true) => native_compute
  | _ => cbv
  end.

Ltac ispec_to_poly_with o :=
  match goal with
  | |- valid_ispec ?ispec =>
    split; [
      by (simpl_with o; reflexivity)
         || fail "The specification is not well formed" |
      apply_spec_split_post o;
      (apply_qslice_sound o;
      apply: ssa_spec_sound;
      apply: (bexp_spec_sound (vs:=ssa_vars empty_vmap (fst ispec))); [
        by (simpl_with o; reflexivity) |
        simplZ_with o; intros;
        repeat (remove_exists_hyp || split_conj); clear_true
      ])
    ]
  end.

Tactic Notation "ispec_to_poly" := ispec_to_poly_with default_options.

Ltac gen_eqs :=
  match goal with
  | H: _ = _ |- _ => move: H; gen_eqs
  | |- _ => idtac
  end.

Lemma add_move_r1 n m p :
  n + m = p -> n = p - m.
Proof.
  move: (Z.add_move_r n m p) => [H _].
  exact: H.
Qed.

Lemma add_move_l1 n m p :
  n + m = p -> m = p - n.
Proof.
  move: (Z.add_move_l n m p) => [H _].
  exact: H.
Qed.

(* The patterns here should include the pattern in PolyGen.bexp_instr. *)
Ltac to_assign :=
  match goal with
  | st : _ -> Z |- _ =>
    match goal with
    | H : st _ + _ = _ |- _ => move: (add_move_r1 H) => {H} H
    | H : _ + st _ = _ |- _ => move: (add_move_l1 H) => {H} H
    | H : (st _ +  _) + _ = _ |- _ =>
      rewrite -Z.add_assoc in H;
      move: (add_move_r1 H) => {H} H
    | H : (?z + st _) + _ = _ |- _ =>
      rewrite (Z.add_comm z (st _)) -Z.add_assoc in H;
      move: (add_move_r1 H) => {H} H
    | H : _ + (st _ + ?z) = _ |- _ =>
      rewrite (Z.add_comm (st _) z) Z.add_assoc in H;
      move: (add_move_l1 H) => {H} H
    | H : _ + (_ + st _) = _ |- _ =>
      rewrite Z.add_assoc in H;
      move: (add_move_l1 H) => {H} H
    end
  | x : Z |- _ =>
    match goal with
    | H : x + _ = _ |- _ => move: (add_move_r1 H) => {H} H
    | H : _ + x = _ |- _ => move: (add_move_l1 H) => {H} H
    | H : (x +  _) + _ = _ |- _ =>
      rewrite -Z.add_assoc in H;
      move: (add_move_r1 H) => {H} H
    | H : (?z + x) + _ = _ |- _ =>
      rewrite (Z.add_comm z x) -Z.add_assoc in H;
      move: (add_move_r1 H) => {H} H
    | H : _ + (x + ?z) = _ |- _ =>
      rewrite (Z.add_comm x z) Z.add_assoc in H;
      move: (add_move_l1 H) => {H} H
    | H : _ + (_ + x) = _ |- _ =>
      rewrite Z.add_assoc in H;
      move: (add_move_l1 H) => {H} H
    end
  end.

Ltac to_assign_with o :=
  let b := constr:(opt_to_assign o) in
  let b := eval compute in b in
  match b with
  | true => repeat to_assign
  | false => idtac
  end.

Ltac rewrite_assign1 :=
  match goal with
  | st : _ -> Z |- _ =>
    match goal with
    | H : st _ = _ |- _ =>
      ( try rewrite -> H in * ); clear H
    end
  end.

Ltac rewrite_assign2 :=
  match goal with
  | x : Z |- _ =>
    match goal with
    | H : x = _ |- _ =>
      ( try rewrite -> H in * ); clear H; try clear x
    end
  end.

Ltac rewrite_assign := rewrite_assign1 || rewrite_assign2.

Ltac rewrite_equality :=
  match goal with
  | H: _ = _ |- _ =>
    ( try rewrite -> H in * ); move: H; rewrite_equality
  | |- _ => intros
  end.

From Coq Require Import Nsatz.

Ltac gbarith_with o :=
  let a := constr:((opt_singular o, opt_magma o)) in
  let a := eval compute in a in
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  match goal with
  | H : _ = _ |- _ =>
    let a :=
        match a with
        | (true, _) => SingularZ
        | (_, true) => MagmaZ
        | _ => fail 100 "No Groebner basis engine is selected."
        end in
    match b with
    | true => time "gbarith" (gbarith_choice a)
    | false => gbarith_choice a
    end
  | |- _ =>
    match b with
    | true => time "modp_find_witness" modp_find_witness
    | false => modp_find_witness
    end
  end.

Ltac nsatz_with o :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  match goal with
  | H : _ = _ |- _ =>
    match b with
    | true => time "nsatz" nsatz
    | false => nsatz
    end
  | |- _ =>
    match b with
    | true => time "ring" ring
    | false => ring
    end
  end.

Ltac solve_ispec_with o :=
  match goal with
  | |- _ /\ _ => split; solve_ispec_with o
  | |- exists _, _ = _ => gbarith_with o
  | |- modulo _ _ _ => gbarith_with o
  | |- _ = _ => nsatz_with o
  end.

Tactic Notation "solve_ispec" := solve_ispec_with default_options.

Ltac verify_bexp_with o :=
  match goal with
  | |- valid (QEq _ _) => move=> s; simplZ; nsatz_with o
  | |- _ = _ => nsatz_with o
  | |- valid (QEqMod _ _ _) => move=> s; simplZ; gbarith_with o
  | |- modulo _ _ _ => gbarith_with o
  | |- exists k : Z, (_ - _)%Z = (k * _)%Z => gbarith_with o
  | |- valid (QAnd _ _) => split; verify_bexp_with o
  | |- _ /\ _ => split; verify_bexp_with o
  end.

Tactic Notation "verify_bexp" := verify_bexp_with default_options.
Tactic Notation "verify_bexp" "with" constr(opts) := verify_bexp_with (vconfig opts).

Ltac verify_entail_with o :=
  match goal with
  | |- ?f ===> ?g =>
    let H := fresh in
    simplZ; move=> s H; repeat (remove_exists_hyp || split_conj);
    clear_true; to_assign_with o;
    repeat rewrite_assign; rewrite_equality; verify_bexp_with o
  end.

Tactic Notation "verify_entail" := verify_entail_with default_options.
Tactic Notation "verify_entail" "with" constr(opts) := verify_entail_with (vconfig opts).

Ltac verify_ispec_with o :=
  ispec_to_poly_with o; to_assign_with o;
  repeat rewrite_assign; rewrite_equality; solve_ispec_with o.

Tactic Notation "verify_ispec" := verify_ispec_with default_options.
Tactic Notation "verify_ispec" "with" constr(opts) := verify_ispec_with (vconfig opts).

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
Tactic Notation "verify_spec" constr(vs) "with" constr(opts) := verify_spec_with (vconfig opts) vs.
