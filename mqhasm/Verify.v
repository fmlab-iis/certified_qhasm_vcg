
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From mQhasm Require Import zDSL zSSA zPoly.
From GBArith Require Import GBCompute.
From PolyOp Require Import Modp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope zdsl_scope.

(** Options *)

(*
  - opt_split: split postcondition at specification level,
               good for slicing, bad for rewriting a lot of assignments
  - opt_slicing: apply slicing before converting to SSA
  - opt_to_assign: convert equations (e1 = e2) to assignment form (x = e)
  - opt_keep_unused: do not convert (hi*2^w + lo = e) to (lo = e - hi*2^w)
                     if lo is not used but hi is used
  - opt_rewrite_assign: rewrite x = e and clear it
  - opt_rewrite_equality: rewrite e1 = e2
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
              opt_keep_unused : bool;
              opt_rewrite_assign : bool;
              opt_rewrite_equality : bool;
              opt_lazy : bool;
              opt_native : bool;
              opt_singular : bool;
              opt_magma : bool;
              opt_profiling : bool }.

Definition default_options : verify_options :=
  {| opt_split := true;
     opt_slicing := false;
     opt_to_assign := true;
     opt_keep_unused := false;
     opt_rewrite_assign := true;
     opt_rewrite_equality := true;
     opt_lazy := false;
     opt_native := true;
     opt_singular := true;
     opt_magma := false;
     opt_profiling := true |}.

Inductive bool_flag : Set :=
| Split
| Slicing
| ToAssign
| KeepUnused
| RewriteAssign
| RewriteEquality
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
                opt_keep_unused := opt_keep_unused o;
                opt_rewrite_assign := opt_rewrite_assign o;
                opt_rewrite_equality := opt_rewrite_equality o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := opt_singular o;
                opt_magma := opt_magma o;
                opt_profiling := opt_profiling o |}
  | Slicing => {| opt_split := opt_split o;
                  opt_slicing := b;
                  opt_to_assign := opt_to_assign o;
                  opt_keep_unused := opt_keep_unused o;
                  opt_rewrite_assign := opt_rewrite_assign o;
                  opt_rewrite_equality := opt_rewrite_equality o;
                  opt_lazy := opt_lazy o;
                  opt_native := opt_native o;
                  opt_singular := opt_singular o;
                  opt_magma := opt_magma o;
                  opt_profiling := opt_profiling o |}
  | ToAssign => {| opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := b;
                   opt_keep_unused := opt_keep_unused o;
                   opt_rewrite_assign := opt_rewrite_assign o;
                   opt_rewrite_equality := opt_rewrite_equality o;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := opt_singular o;
                   opt_magma := opt_magma o;
                   opt_profiling := opt_profiling o |}
  | KeepUnused => {| opt_split := opt_split o;
                     opt_slicing := opt_slicing o;
                     opt_to_assign := opt_to_assign o;
                     opt_keep_unused := b;
                     opt_rewrite_assign := opt_rewrite_assign o;
                     opt_rewrite_equality := opt_rewrite_equality o;
                     opt_lazy := opt_lazy o;
                     opt_native := opt_native o;
                     opt_singular := opt_singular o;
                     opt_magma := opt_magma o;
                     opt_profiling := opt_profiling o |}
  | RewriteAssign => {| opt_split := opt_split o;
                        opt_slicing := opt_slicing o;
                        opt_to_assign := opt_to_assign o;
                        opt_keep_unused := opt_keep_unused o;
                        opt_rewrite_assign := b;
                        opt_rewrite_equality := opt_rewrite_equality o;
                        opt_lazy := opt_lazy o;
                        opt_native := opt_native o;
                        opt_singular := opt_singular o;
                        opt_magma := opt_magma o;
                        opt_profiling := opt_profiling o |}
  | RewriteEquality => {| opt_split := opt_split o;
                          opt_slicing := opt_slicing o;
                          opt_to_assign := opt_to_assign o;
                          opt_keep_unused := opt_keep_unused o;
                          opt_rewrite_assign := opt_rewrite_assign o;
                          opt_rewrite_equality := b;
                          opt_lazy := opt_lazy o;
                          opt_native := opt_native o;
                          opt_singular := opt_singular o;
                          opt_magma := opt_magma o;
                          opt_profiling := opt_profiling o |}
  | Lazy => {| opt_split := opt_split o;
               opt_slicing := opt_slicing o;
               opt_to_assign := opt_to_assign o;
               opt_keep_unused := opt_keep_unused o;
               opt_rewrite_assign := opt_rewrite_assign o;
               opt_rewrite_equality := opt_rewrite_equality o;
               opt_lazy := b;
               opt_native := ~~b;
               opt_singular := opt_singular o;
               opt_magma := opt_magma o;
               opt_profiling := opt_profiling o |}
  | Native => {| opt_split := opt_split o;
                 opt_slicing := opt_slicing o;
                 opt_to_assign := opt_to_assign o;
                 opt_keep_unused := opt_keep_unused o;
                 opt_rewrite_assign := opt_rewrite_assign o;
                 opt_rewrite_equality := opt_rewrite_equality o;
                 opt_lazy := ~~b;
                 opt_native := b;
                 opt_singular := opt_singular o;
                 opt_magma := opt_magma o;
                 opt_profiling := opt_profiling o |}
  | Singular => {| opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := opt_to_assign o;
                   opt_keep_unused := opt_keep_unused o;
                   opt_rewrite_assign := opt_rewrite_assign o;
                   opt_rewrite_equality := opt_rewrite_equality o;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := b;
                   opt_magma := ~~b;
                   opt_profiling := opt_profiling o |}
  | Magma => {| opt_split := opt_split o;
                opt_slicing := opt_slicing o;
                opt_to_assign := opt_to_assign o;
                opt_keep_unused := opt_keep_unused o;
                opt_rewrite_assign := opt_rewrite_assign o;
                opt_rewrite_equality := opt_rewrite_equality o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := ~~b;
                opt_magma := b;
                opt_profiling := opt_profiling o |}
  | Profiling => {| opt_split := opt_split o;
                    opt_slicing := opt_slicing o;
                    opt_to_assign := opt_to_assign o;
                    opt_keep_unused := opt_keep_unused o;
                    opt_rewrite_assign := opt_rewrite_assign o;
                    opt_rewrite_equality := opt_rewrite_equality o;
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



(** ispec - specification with specified input variables *)

Definition ispec : Type := (VS.t * zDSL.spec).

Definition valid_ispec (s : ispec) : Prop :=
  well_formed_spec (fst s) (snd s) /\ valid_spec (snd s).



(** Tactics *)

From GBArith Require Import GBZArith.

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

Ltac apply_zslice_sound o :=
  let b := constr:(opt_slicing o) in
  let b := eval compute in b in
  match b with
  | true => apply: zslice_sound; rewrite /zslice /slice_pre /=
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
  let tac _ := (
    match goal with
    | |- valid_ispec ?ispec =>
      split; [
        by (simpl_with o; reflexivity)
           || fail 100 "The specification is not well formed" |
        apply_spec_split_post o;
        (apply_zslice_sound o;
        apply: ssa_spec_sound;
        apply: (bexp_spec_sound (vs:=ssa_vars empty_vmap (fst ispec))); [
          by (simpl_with o; reflexivity) |
          simplZ_with o; intros;
          repeat (remove_exists_hyp || split_conj); clear_true
        ])
      ]
    end) in
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  match b with
  | true => time "ispec_to_poly" (tac unit)
  | false => tac unit
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

(* Get the variables at the right-hand side of equations. *)
Ltac right_variables t :=
  let rec aux t fv :=
  match t with
  | 0 => fv
  | 1 => fv
  | Zpos _ => fv
  | Zneg _ => fv
  | False  => fv
  | ?t1 -> ?g1 =>
    let fv1  := aux t1 fv in
    let fv2  := aux g1 fv1 in fv2
  | (_ <= ?t1) => aux t1 fv
  | (_ < ?t1) => aux t1 fv
  | (_ = ?t1) => aux t1 fv
  | (?t1 + ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (?t1 * ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (?t1 - ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (-?t1) =>
    let fv1  := aux t1 fv in fv1
  | (?t1 ^ ?t2) =>
    let fv1  := aux t1 fv in
    match NCst t2 with
    | false => let fv1 := rAddFv t fv in fv1
    | _ => fv1
    end
  | _ => let fv1 := rAddFv t fv in fv1
  end in
  aux t (@nil Z).

Ltac union_variables vs1 vs2 :=
  match vs1 with
  | (cons ?x ?vs) => let vs2 := rAddFv x vs2 in union_variables vs vs2
  | _ => vs2
  end.

Ltac goal_variables :=
  match goal with
  | |- exists k, ?a = k * ?b =>
    let vs1 := variables a in
    let vs2 := variables b in
    union_variables vs1 vs2
  | |- modulo ?a ?b ?c =>
    let vs1 := variables a in
    let vs2 := variables b in
    let vs3 := variables c in
    let vs23 := union_variables vs2 vs3 in
    union_variables vs1 vs23
  | |- ?a = ?b =>
    let vs1 := variables a in
    let vs2 := variables b in
    union_variables vs1 vs2
  end.

Ltac variables_disjoint vs1 vs2 :=
  match vs1 with
  | cons ?a ?vs =>
    match rIN a vs2 with
    | true => constr:false
    | false => variables_disjoint vs vs2
    end
  | _ => constr:true
  end.

Ltac keep_unused1 x e vars :=
  let evs := variables e in
  match rIN x vars with
  | true => constr:false
  | false =>
    match variables_disjoint evs vars with
    | true => constr:false
    | false => constr:true
    end
  end.

Ltac keep_unused2 x e1 e2 vars :=
  let evs1 := variables e1 in
  let evs2 := variables e2 in
  match rIN x vars with
  | true => constr:false
  | false =>
    match variables_disjoint evs1 vars with
    | true =>
      match variables_disjoint evs2 vars with
      | true => constr:false
      | false => constr:true
      end
    | false => constr:true
    end
  end.

(* Convert (x + y = z) to (x = z - y) where x is a variable.
   The equation (hi*2^p + lo = e) is not converted if lo is not used
   by hi is used.
   The patterns here should include the pattern in PolyGen.bexp_instr. *)
Ltac to_assign_keep vars :=
  match goal with
  | st : _ -> Z |- _ =>
    match goal with
    | H : st ?x + ?y = _ |- _ =>
      match (keep_unused1 (st x) y vars) with
      | true => idtac "found unused:" x; move: H
      | false => move: (add_move_r1 H) => {H} H
      end
    | H : ?y + st ?x = _ |- _ =>
      match (keep_unused1 (st x) y vars) with
      | true => idtac "found unused:" x; move: H
      | false => move: (add_move_l1 H) => {H} H
      end
    | H : (st ?x + ?y) + ?z = _ |- _ =>
      match (keep_unused2 (st x) y z vars) with
      | true => move: H
      | false =>
        rewrite -Z.add_assoc in H;
        move: (add_move_r1 H) => {H} H
      end
    | H : (?z + st ?x) + ?y = _ |- _ =>
      match (keep_unused2 (st x) y z vars) with
      | true => move: H
      | false =>
        rewrite (Z.add_comm z (st _)) -Z.add_assoc in H;
        move: (add_move_r1 H) => {H} H
      end
    | H : ?y + (st ?x + ?z) = _ |- _ =>
      match (keep_unused2 (st x) y z vars) with
      | true => move: H
      | false =>
        rewrite (Z.add_comm (st _) z) Z.add_assoc in H;
        move: (add_move_l1 H) => {H} H
      end
    | H : ?z + (?y + st ?x) = _ |- _ =>
      match (keep_unused2 (st x) y z vars) with
      | true => move: H
      | false =>
        rewrite Z.add_assoc in H;
        move: (add_move_l1 H) => {H} H
      end
    end
  | x : Z |- _ =>
    match goal with
    | H : x + ?y = _ |- _ =>
      match (keep_unused1 x y vars) with
      | true => move: H
      | false => move: (add_move_r1 H) => {H} H
      end
    | H : ?y + x = _ |- _ =>
      match (keep_unused1 x y vars) with
      | true => move: H
      | false => move: (add_move_l1 H) => {H} H
      end
    | H : (x +  ?y) + ?z = _ |- _ =>
      match (keep_unused2 x y z vars) with
      | true => move: H
      | false =>
        rewrite -Z.add_assoc in H;
        move: (add_move_r1 H) => {H} H
      end
    | H : (?z + x) + ?y = _ |- _ =>
      match (keep_unused2 x y z vars) with
      | true => move: H
      | false =>
        rewrite (Z.add_comm z x) -Z.add_assoc in H;
        move: (add_move_r1 H) => {H} H
      end
    | H : ?y + (x + ?z) = _ |- _ =>
      match (keep_unused2 x y z vars) with
      | true => move: H
      | false =>
        rewrite (Z.add_comm x z) Z.add_assoc in H;
        move: (add_move_l1 H) => {H} H
      end
    | H : ?z + (?y + x) = _ |- _ =>
      match (keep_unused2 x y z vars) with
      | true => move: H
      | false =>
        rewrite Z.add_assoc in H;
        move: (add_move_l1 H) => {H} H
      end
    end
  end.

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
  let k := constr:(opt_keep_unused o) in
  let k := eval compute in k in
  match k with
  | true =>
    let gvars := goal_variables in
    gen_eqs;
    match goal with
    | |- ?g =>
      let hyplist := lhyps g in
      let dummy := constr:(0 = 0) in
      let hyps := ajoute_hyps hyplist dummy in
      let rvars := right_variables hyps in
      let vars := union_variables gvars rvars in
      intros;
      match b with
      | true => repeat (to_assign_keep vars)
      | false => idtac
      end
    end
  | false =>
    match b with
    | true => repeat to_assign
    | false => idtac
    end
  end.

Ltac rewrite_assign1_with o :=
  match goal with
  | st : _ -> Z |- _ =>
    match goal with
    | H : st ?x = _ |- _ => ( try rewrite -> H in * ); clear H
    end
  end.

Ltac rewrite_assign2_with o :=
  match goal with
  | x : Z |- _ =>
    match goal with
    | H : ?x = _ |- _ => ( try rewrite -> H in * ); clear H; try clear x
    end
  end.

Ltac rewrite_assign3_with o :=
  rewrite_assign1_with o || rewrite_assign2_with o.

Ltac rewrite_assign_with o :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let r := constr:(opt_rewrite_assign o) in
  let r := eval compute in r in
  match r with
  | true =>
    match b with
    | true => time "rewrite_assign" (repeat rewrite_assign3_with o)
    | false => repeat rewrite_assign3_with o
    end
  | false => idtac
  end; intros.

Tactic Notation "rewrite_assign" := rewrite_assign_with default_options.

Ltac rewrite_equality_rec :=
  match goal with
  | H: _ = _ |- _ =>
    ( try rewrite -> H in * ); move: H; rewrite_equality_rec
  | |- _ => intros
  end.

Ltac rewrite_equality_with o :=
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  let r := constr:(opt_rewrite_equality o) in
  let r := eval compute in r in
  match r with
  | true =>
    match b with
    | true => time "rewrite_equality" rewrite_equality_rec
    | false => rewrite_equality_rec
    end
  | false => idtac
  end.

Tactic Notation "rewrite_equality" := rewrite_equality_with default_options.

From Coq Require Import Nsatz.

Ltac gbarith_with o :=
  let a := constr:((opt_singular o, opt_magma o)) in
  let a := eval compute in a in
  let b := constr:(opt_profiling o) in
  let b := eval compute in b in
  lazymatch goal with
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
    let a :=
        match a with
        | (true, _) => PolyOp.Singular
        | (_, true) => PolyOp.Magma
        | _ => fail 100 "No polynomial engine is selected."
        end in
    match b with
    | true => time "modp_find_witness" (modp_find_witness_with a)
    | false => modp_find_witness_with a
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
Tactic Notation "solve_ispec" "with" constr(opts) := solve_ispec_with (vconfig opts).

Ltac verify_bexp_with o :=
  match goal with
  | |- valid (zEq _ _) => move=> s; simplZ; nsatz_with o
  | |- _ = _ => nsatz_with o
  | |- valid (zEqMod _ _ _) => move=> s; simplZ; gbarith_with o
  | |- modulo _ _ _ => gbarith_with o
  | |- exists k : Z, (_ - _)%Z = (k * _)%Z => gbarith_with o
  | |- valid (zAnd _ _) => split; verify_bexp_with o
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
    rewrite_assign_with o; rewrite_equality_with o; verify_bexp_with o
  end.

Tactic Notation "verify_entail" := verify_entail_with default_options.
Tactic Notation "verify_entail" "with" constr(opts) := verify_entail_with (vconfig opts).

Ltac verify_ispec_with o :=
  ispec_to_poly_with o; to_assign_with o;
  rewrite_assign_with o; rewrite_equality_with o; solve_ispec_with o.

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
