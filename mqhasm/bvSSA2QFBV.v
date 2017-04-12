
From Coq Require Import Program ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From Common Require Import Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
From mQhasm Require Import bvSSA QF_BV.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import bv64SSA.

Module QFBV64 := MakeQFBV AMD64 bv64SSA.V.

Notation wordsize := AMD64.wordsize.



(* Conversion from bv64SSA to QFBV64. *)

Definition exp_atomic (a : atomic) : QFBV64.exp wordsize :=
  match a with
  | bvVar v => QFBV64.bvVar v
  | bvConst c => QFBV64.bvConst c
  end.

Definition extAdd n a1 a2 :=
  QFBV64.bvAdd (QFBV64.bvZeroExtend n (exp_atomic a1))
               (QFBV64.bvZeroExtend n (exp_atomic a2)).

Definition extMul n a1 a2 :=
  QFBV64.bvMul (QFBV64.bvZeroExtend n (exp_atomic a1))
               (QFBV64.bvZeroExtend n (exp_atomic a2)).

Definition concatShl n a1 a2 :=
  QFBV64.bvShl
    (QFBV64.bvConcat (exp_atomic a1) (exp_atomic a2))
    (QFBV64.bvConst (fromNat n)).

Definition bexp_instr (i : instr) : QFBV64.bexp :=
  match i with
  | bvAssign v a => QFBV64.bvEq (QFBV64.bvVar v)
                                (exp_atomic a)
  | bvAdd v a1 a2 => QFBV64.bvEq (QFBV64.bvVar v)
                                 (QFBV64.bvAdd (exp_atomic a1)
                                               (exp_atomic a2))
  | bvAddC c v a1 a2 =>
    QFBV64.bvConj
      (QFBV64.bvEq (QFBV64.bvVar c)
                   (QFBV64.bvZeroExtend
                      (wordsize - 1)
                      (@QFBV64.bvHigh _ 1 (extAdd 1 a1 a2))))
      (QFBV64.bvEq (QFBV64.bvVar v)
                   (@QFBV64.bvLow wordsize _ (extAdd 1 a1 a2)))
  | bvSub v a1 a2 => QFBV64.bvEq (QFBV64.bvVar v)
                                 (QFBV64.bvSub (exp_atomic a1)
                                               (exp_atomic a2))
  | bvMul v a1 a2 => QFBV64.bvEq (QFBV64.bvVar v)
                                 (QFBV64.bvMul (exp_atomic a1)
                                               (exp_atomic a2))
  | bvMulf vh vl a1 a2 =>
    QFBV64.bvConj
      (QFBV64.bvEq
         (QFBV64.bvVar vh)
         (@QFBV64.bvHigh _ wordsize (extMul wordsize a1 a2)))
      (QFBV64.bvEq
         (QFBV64.bvVar vl)
         (@QFBV64.bvLow wordsize _ (extMul wordsize a1 a2)))
  | bvShl v a p => QFBV64.bvEq (QFBV64.bvVar v)
                               (QFBV64.bvShl (exp_atomic a)
                                             (QFBV64.bvConst p))
  | bvSplit vh vl a p =>
    QFBV64.bvConj
      (QFBV64.bvEq (QFBV64.bvVar vh)
                   (QFBV64.bvShr
                      (exp_atomic a)
                      (QFBV64.bvConst p)))
      (QFBV64.bvEq (QFBV64.bvVar vl)
                   (QFBV64.bvShr
                      (QFBV64.bvShl (exp_atomic a)
                                    (QFBV64.bvConst
                                       (fromNat (wordsize - toNat p))))
                      (QFBV64.bvConst
                         (fromNat (wordsize - toNat p)))))
  | bvConcatShl vh vl a1 a2 p =>
    QFBV64.bvConj
      (QFBV64.bvEq (QFBV64.bvVar vh)
                   (@QFBV64.bvHigh _ wordsize (concatShl (toNat p) a1 a2)))
      (QFBV64.bvEq (QFBV64.bvVar vl)
                   (QFBV64.bvShr
                      (@QFBV64.bvLow wordsize _ (concatShl (toNat p) a1 a2))
                      (QFBV64.bvConst p)))
  end.

Definition bexp_program (p : program) : seq QFBV64.bexp :=
  map bexp_instr p.

Fixpoint exp_exp w (e : exp w) : QFBV64.exp w :=
  match e with
  | bvAtomic a => exp_atomic a
  | bvBinop _ op e1 e2 =>
    match op with
    | bvAddOp => QFBV64.bvAdd (exp_exp e1) (exp_exp e2)
    | bvSubOp => QFBV64.bvSub (exp_exp e1) (exp_exp e2)
    | bvMulOp => QFBV64.bvMul (exp_exp e1) (exp_exp e2)
    end
  | bvExt _ e i => QFBV64.bvZeroExtend i (exp_exp e)
  end.

Fixpoint bexp_bexp (e : bexp) : QFBV64.bexp :=
  match e with
  | bvTrue => QFBV64.bvTrue
  | bvEq _ e1 e2 => QFBV64.bvEq (exp_exp e1) (exp_exp e2)
  | bvEqMod _ e1 e2 p => QFBV64.bvEqMod (exp_exp e1)
                                        (exp_exp e2)
                                        (QFBV64.bvConst p)
  | bvCmp _ op e1 e2 =>
    match op with
    | bvUltOp => QFBV64.bvUlt (exp_exp e1) (exp_exp e2)
    | bvUleOp => QFBV64.bvUle (exp_exp e1) (exp_exp e2)
    | bvUgtOp => QFBV64.bvUgt (exp_exp e1) (exp_exp e2)
    | bvUgeOp => QFBV64.bvUge (exp_exp e1) (exp_exp e2)
    end
  | bvAnd e1 e2 => QFBV64.bvConj (bexp_bexp e1) (bexp_bexp e2)
  end.

Record bexp_spec : Type :=
  mkQFBVSpec { bpre : QFBV64.bexp;
               bprog : seq QFBV64.bexp;
               bpost : QFBV64.bexp }.

Definition bexp_of_spec (s : spec) : bexp_spec :=
  {| bpre := bexp_bexp (spre s);
     bprog := bexp_program (sprog s);
     bpost := bexp_bexp (spost s) |}.



(* Properties of the conversion. *)

Lemma fullmulB_zeroExtend w (bv1 bv2 : BITS w) :
  (fullmulB bv1 bv2) = mulB (zeroExtend w bv1) (zeroExtend w bv2).
Proof.
Admitted.

Lemma bv_mod_modulo w (bv1 bv2 n : BITS w) :
  @fromPosZ w (toPosZ bv1 mod toPosZ n) =
  @fromPosZ w (toPosZ bv2 mod toPosZ n) ->
  modulo (toPosZ bv1) (toPosZ bv2) (toPosZ n).
Proof.
Admitted.

Lemma modulo_bv_mod w (bv1 bv2 n : BITS w) :
  modulo (toPosZ bv1) (toPosZ bv2) (toPosZ n) ->
  @fromPosZ w (toPosZ bv1 mod toPosZ n) =
  @fromPosZ w (toPosZ bv2 mod toPosZ n).
Proof.
Admitted.

Lemma bv_width_sub_bounded w (bv : BITS w) :
  w - toNat bv < 2 ^ w.
Proof.
  apply: (@ltn_leq_trans (2^w - toNat bv)).
  - apply: ltn_sub2r.
    + exact: toNatBounded.
    + by apply: ltn_expl.
  - exact: leq_subr.
Qed.

Lemma leq_exp_plus n a b :
  n > 0 ->
  n^a <= n^(a + b).
Proof.
  move=> H.
  rewrite expnD.
  apply: leq_pmulr.
  rewrite expn_gt0 H.
  done.
Qed.

Lemma store_state_acc v s :
  QFBV64.Store.acc v s = State.acc v s.
Proof.
  reflexivity.
Qed.

Lemma eval_exp_atomic a s :
  QFBV64.eval_exp (exp_atomic a) s = eval_atomic a s.
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma eval_exp_exp w (e : exp w) s:
  QFBV64.eval_exp (exp_exp e) s = eval_exp e s.
Proof.
  elim: e => {w} /=.
  - move=> a. exact: eval_exp_atomic.
  - move=> w op e1 IH1 e2 IH2.
    case: op; rewrite /= IH1 IH2; reflexivity.
  - move=> w e IH m.
    rewrite IH; reflexivity.
Qed.

Lemma eval_exp_bexp e s:
  QFBV64.eval_bexp (bexp_bexp e) s <-> eval_bexp e s.
Proof.
  split; elim: e => /=.
  - done.
  - move=> w e1 e2; by repeat rewrite eval_exp_exp.
  - move=> w e1 e2 n; repeat rewrite eval_exp_exp; exact: bv_mod_modulo.
  - move=> w op e1 e2. case: op; rewrite /= 2!eval_exp_exp.
    + done.
    + done.
    + by rewrite ltBNle.
    + by rewrite leBNlt.
  - move=> e1 IH1 e2 IH2 [H1 H2]; exact: (conj (IH1 H1) (IH2 H2)).
  - done.
  - move=> w e1 e2; by repeat rewrite eval_exp_exp.
  - move=> w e1 e2 n; repeat rewrite eval_exp_exp; exact: modulo_bv_mod.
  - move=> w op e1 e2; case: op; rewrite /= 2!eval_exp_exp.
    + done.
    + done.
    + by rewrite ltBNle.
    + by rewrite leBNlt.
  - move=> e1 IH1 e2 IH2 [H1 H2]; exact: (conj (IH1 H1) (IH2 H2)).
Qed.

Lemma eval_exp_bexp1 e s:
  QFBV64.eval_bexp (bexp_bexp e) s -> eval_bexp e s.
Proof.
  move: (eval_exp_bexp e s) => [H1 H2].
  exact: H1.
Qed.

Lemma eval_exp_bexp2 e s:
  eval_bexp e s -> QFBV64.eval_bexp (bexp_bexp e) s.
Proof.
  move: (eval_exp_bexp e s) => [H1 H2].
  exact: H2.
Qed.

Lemma eval_bexp_instr i p s1 s2 :
  ssa_vars_unchanged_program (vars_instr i) p ->
  eval_program s1 p = s2 ->
  QFBV64.eval_bexp (bexp_instr i) s1 ->
  QFBV64.eval_bexp (bexp_instr i) s2.
Proof.
  case: i => /=; intros;
    (let rec tac :=
         match goal with
         | H : context f [QFBV64.eval_exp (exp_atomic ?a) ?s] |- _ =>
           (* convert (QFBV64.eval_exp (exp_atomic a) s) to (eval_atomic a s) *)
           rewrite eval_exp_atomic in H; tac
         | |- context f [QFBV64.eval_exp (exp_atomic ?a) ?s] =>
           rewrite eval_exp_atomic; tac
         | H : context f [QFBV64.Store.acc ?v ?s] |- _ =>
           (* convert (QFBV64.Store.acc v s) to (State.acc v s) *)
           rewrite store_state_acc in H; tac
         | |- context f [QFBV64.Store.acc ?v ?s] =>
           rewrite store_state_acc; tac
         | H : is_true (ssa_vars_unchanged_program (VS.add _ _) ?p) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]; tac
         | H : is_true (ssa_vars_unchanged_program (VS.union _ _) ?p) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           move: (ssa_unchanged_program_union1 H) => {H} [H1 H2]; tac
         | H1 : eval_program ?s1 ?p = ?s2,
           H2 : is_true (ssa_var_unchanged_program ?v ?p) |-
           context f [State.acc ?v ?s2] =>
           (* convert (State.acc v s2) to (State.acc v s1) *)
           rewrite -(acc_unchanged_program H2 H1); tac
         | H1 : eval_program ?s1 ?p = ?s2,
           H2 : is_true (ssa_vars_unchanged_program (vars_atomic ?a) ?p) |-
           context f [eval_atomic ?a ?s2] =>
           (* convert (eval_atomic a s2) to (eval_atomic a s1) *)
           rewrite -(ssa_unchanged_program_eval_atomic H2 H1); tac
         | |- _ => try assumption
         end in
    tac).
Qed.

Ltac eval_exp_exp_atomic_to_pred_state :=
  match goal with
  | Hsub : is_true (VS.subset (vars_atomic ?a) ?vs),
    Hun : is_true (ssa_vars_unchanged_instr ?vs _),
    Hupd : State.upd _ _ ?s1 = ?s2 |-
    context f [QFBV64.eval_exp (exp_atomic ?a) ?s2] =>
    rewrite (eval_exp_atomic a s2);
    rewrite -(ssa_unchanged_instr_eval_atomic
                (ssa_unchanged_instr_subset Hun Hsub)
                Hupd)
  | Hsub : is_true (VS.subset (vars_atomic ?a) ?vs),
    Hun : is_true (ssa_vars_unchanged_instr ?vs _),
    Hupd : State.upd2 _ _ _ _ ?s1 = ?s2 |-
    context f [QFBV64.eval_exp (exp_atomic ?a) ?s2] =>
    rewrite (eval_exp_atomic a s2);
    rewrite -(ssa_unchanged_instr_eval_atomic
                (ssa_unchanged_instr_subset Hun Hsub)
                Hupd)
  end.

Ltac qfbv64_store_acc :=
  match goal with
  | Hupd : State.upd _ _ _ = ?s2 |- context f [QFBV64.Store.acc _ ?s2] =>
    rewrite -Hupd; qfbv64_store_acc
  | Hupd : State.upd2 _ _ _ _ _ = ?s2 |- context f [QFBV64.Store.acc _ ?s2] =>
    rewrite -Hupd; qfbv64_store_acc
  | |- context f [QFBV64.Store.acc ?v (State.upd ?v _ ?s1)] =>
    rewrite (QFBV64.Store.acc_upd_eq _ _ (eqxx v))
  | Hne : is_true (?vh != ?vl) |-
    context f [QFBV64.Store.acc ?vh (State.upd2 ?vh _ ?vl _ ?s1)] =>
    rewrite (QFBV64.Store.acc_upd_neq _ _ Hne)
            (QFBV64.Store.acc_upd_eq _ _ (eqxx vh))
  | Hne : is_true (?vh != ?vl) |-
    context f [QFBV64.Store.acc ?vl (State.upd2 ?vh _ ?vl _ ?s1)] =>
    rewrite (QFBV64.Store.acc_upd_eq _ _ (eqxx vl))
  end.

Lemma bexp_instr_eval vs i s1 s2 :
  well_formed_instr vs i ->
  ssa_vars_unchanged_instr vs i ->
  eval_instr s1 i = s2 ->
  QFBV64.eval_bexp (bexp_instr i) s2.
Proof.
  case: i => /=.
  - move=> v a Hsub Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - move=> vh vl a1 a2 /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    split.
    + exact: (addB_zeroExtend1_high_ext (eval_atomic a1 s1)
                                        (eval_atomic a2 s1)).
    + exact: (ssrfun.esym (addB_zeroExtend1_low (eval_atomic a1 s1)
                                                (eval_atomic a2 s1))).
  - move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - move=> vh vl a1 a2 /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    by rewrite -fullmulB_zeroExtend.
  - move=> v a n Hsub Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - move=> vh vl a n /andP [Hne Hsub] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    split; first by reflexivity.
    rewrite fromNatK; first by reflexivity.
    exact: bv_width_sub_bounded.
  - move=> vh vl a1 a2 n /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    rewrite fromNatK; first by done.
    apply: (ltn_leq_trans (toNatBounded n)).
    apply: leq_exp_plus.
    done.
Qed.



(* Connect premises by conjunction. *)

Fixpoint eval_bexps_conj (es : seq QFBV64.bexp) (s : State.t) : Prop :=
  match es with
  | [::] => True
  | hd::tl => QFBV64.eval_bexp hd s /\ eval_bexps_conj tl s
  end.

Lemma bexp_program_eval vs p s1 s2 :
  well_formed_ssa_program vs p ->
  eval_program s1 p = s2 ->
  eval_bexps_conj (bexp_program p) s2.
Proof.
  elim: p vs s1 s2 => /=.
  - done.
  - move=> hd tl IH vs s1 s2 Hwfssa Hep.
    move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    split.
    + apply: (eval_bexp_instr _ Hep).
      * exact: (well_formed_ssa_vars_unchanged_hd Hwfssa).
      * apply: (bexp_instr_eval
                  (well_formed_program_cons1 Hwf)
                  (ssa_unchanged_program_hd Huc)).
        reflexivity.
    + exact: (IH _ _ _ (well_formed_ssa_tl Hwfssa) Hep).
Qed.

Definition valid_bexp_spec_conj (s : bexp_spec) : Prop :=
  forall st : State.t,
    QFBV64.eval_bexp (bpre s) st ->
    eval_bexps_conj (bprog s) st ->
    QFBV64.eval_bexp (bpost s) st.

Lemma bexp_spec_sound_conj (vs : VS.t) (s : spec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec_conj (bexp_of_spec s) -> valid_spec s.
Proof.
  destruct s as [f p g].
  rewrite /bexp_of_spec /valid_bexp_spec_conj /=.
  move=> Hwfssa Hvalid s1 s2 /= Hf Hp.
  apply: eval_exp_bexp1.
  apply: Hvalid.
  - move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa].
    apply: eval_exp_bexp2.
    apply: (ssa_unchanged_program_eval_bexp1 _ Hp Hf).
    apply: (ssa_unchanged_program_subset Huc).
    move/andP: Hwf => /= [/andP [H _] _].
    exact: H.
  - exact: (bexp_program_eval (well_formed_ssa_spec_program Hwfssa) Hp).
Qed.



(* Connect premises by implication. *)

Fixpoint eval_bexps_imp (es : seq QFBV64.bexp) (s : State.t) (p : Prop) : Prop :=
  match es with
  | [::] => p
  | hd::tl => QFBV64.eval_bexp hd s -> eval_bexps_imp tl s p
  end.

Definition valid_bexp_spec_imp (s : bexp_spec) : Prop :=
  forall st : State.t,
    QFBV64.eval_bexp (bpre s) st ->
    eval_bexps_imp (bprog s) st (QFBV64.eval_bexp (bpost s) st).

Lemma valid_bexp_spec_conj_imp (s : bexp_spec) :
  valid_bexp_spec_conj s -> valid_bexp_spec_imp s.
Proof.
  destruct s as [f p g].
  move => Hc s /= Hf.
  move: (Hc s Hf) => /= {Hc Hf f} Hc.
  elim: p Hc => /=.
  - by apply.
  - move=> hd tl IH Hc Hhd.
    apply: IH => Htl.
    apply: Hc; split; assumption.
Qed.

Lemma valid_bexp_spec_imp_conj (s : bexp_spec) :
  valid_bexp_spec_imp s -> valid_bexp_spec_conj s.
Proof.
  destruct s as [f p g].
  move => Hi s /= Hf.
  move: (Hi s Hf) => /= {Hi Hf f} Hi.
  elim: p Hi => /=.
  - done.
  - move=> hd tl IH Hi [Hhd Htl].
    exact: (IH (Hi Hhd) Htl).
Qed.

Lemma bexp_spec_sound_imp (vs : VS.t) (s : spec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec_imp (bexp_of_spec s) -> valid_spec s.
Proof.
  move=> Hw Hv.
  apply: (bexp_spec_sound_conj Hw).
  exact: valid_bexp_spec_imp_conj.
Qed.



(* Soundness *)

Definition valid_bexp_spec := valid_bexp_spec_imp.

Theorem bexp_spec_sound (vs : VS.t) (s : spec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec (bexp_of_spec s) -> valid_spec s.
Proof.
  exact: bexp_spec_sound_imp.
Qed.
