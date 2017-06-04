
From Coq Require Import Program ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Common Require Import Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
From mQhasm Require Import bvSSA bvSSA2zSSA QFBV.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import bv64SSA.

Notation wordsize := AMD64.wordsize.



Lemma nneq_is_eqn (A : eqType) (x y : A) :
  ~ x <> y -> x == y.
Proof.
  move=> H. case Hxy: (x == y); first by done.
 apply: False_ind; apply: H. apply/eqP/negPf. assumption.
Qed.

Lemma subn_modn_expn2 (n m : nat) :
  (n - m) %% 2 ^ n = n - m.
Proof.
  rewrite modn_small; first reflexivity.
  apply: (@leq_ltn_trans n).
  - exact: leq_subr.
  - by apply: ltn_expl.
Qed.



(* Conversion from bv64SSA to QFBV64. *)

Definition exp_var v : QFBV64.exp wordsize := QFBV64.bvVar v.

Definition exp_const c : QFBV64.exp wordsize := QFBV64.bvConst c.

Definition exp_atomic (a : atomic) : QFBV64.exp wordsize :=
  match a with
  | bvVar v => exp_var v
  | bvConst c => exp_const c
  end.

Definition extAdd n a1 a2 :=
  QFBV64.bvAdd (QFBV64.bvZeroExtend n (exp_atomic a1))
               (QFBV64.bvZeroExtend n (exp_atomic a2)).

Definition extAdc n a1 a2 v :=
  QFBV64.bvAdd
    (QFBV64.bvAdd (QFBV64.bvZeroExtend n (exp_atomic a1))
                  (QFBV64.bvZeroExtend n (exp_atomic a2)))
    (QFBV64.bvZeroExtend n (QFBV64.bvVar v)).

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
                   (@QFBV64.bvHigh _ wordsize (extAdd wordsize a1 a2)))
      (QFBV64.bvEq (QFBV64.bvVar v)
                   (@QFBV64.bvLow wordsize _ (extAdd wordsize a1 a2)))
  | bvAdc v a1 a2 c =>
    QFBV64.bvEq (QFBV64.bvVar v)
                (@QFBV64.bvLow wordsize _ (extAdc wordsize a1 a2 c))
  | bvAdcC c v a1 a2 a =>
    QFBV64.bvConj
      (QFBV64.bvEq (QFBV64.bvVar c)
                   (@QFBV64.bvHigh _ wordsize (extAdc wordsize a1 a2 a)))
      (QFBV64.bvEq (QFBV64.bvVar v)
                   (@QFBV64.bvLow wordsize _ (extAdc wordsize a1 a2 a)))
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

Fixpoint exp_rexp w (e : rexp w) : QFBV64.exp w :=
  match e with
  | bvrVar v => QFBV64.bvVar v
  | bvrConst _ c => QFBV64.bvConst c
  | bvrBinop _ op e1 e2 =>
    match op with
    | bvAddOp => QFBV64.bvAdd (exp_rexp e1) (exp_rexp e2)
    | bvSubOp => QFBV64.bvSub (exp_rexp e1) (exp_rexp e2)
    | bvMulOp => QFBV64.bvMul (exp_rexp e1) (exp_rexp e2)
    end
  | bvrExt _ e i => QFBV64.bvZeroExtend i (exp_rexp e)
  end.

Fixpoint bexp_rbexp (e : rbexp) : QFBV64.bexp :=
  match e with
  | bvrTrue => QFBV64.bvTrue
  | bvrCmp _ op e1 e2 =>
    match op with
    | bvUltOp => QFBV64.bvUlt (exp_rexp e1) (exp_rexp e2)
    | bvUleOp => QFBV64.bvUle (exp_rexp e1) (exp_rexp e2)
    | bvUgtOp => QFBV64.bvUgt (exp_rexp e1) (exp_rexp e2)
    | bvUgeOp => QFBV64.bvUge (exp_rexp e1) (exp_rexp e2)
    end
  | bvrAnd e1 e2 => QFBV64.bvConj (bexp_rbexp e1) (bexp_rbexp e2)
  end.

Record bexp_spec : Type :=
  mkQFBVSpec { bpre : QFBV64.bexp;
               bprog : seq QFBV64.bexp;
               bpost : QFBV64.bexp }.

Definition bexp_of_rspec (s : rspec) : bexp_spec :=
  {| bpre := bexp_rbexp (rspre s);
     bprog := bexp_program (rsprog s);
     bpost := bexp_rbexp (rspost s) |}.



(* Properties of the conversion. *)

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

Lemma eval_exp_var v s :
  QFBV64.eval_exp (exp_var v) s = State.acc v s.
Proof.
  reflexivity.
Qed.

Lemma eval_exp_atomic a s :
  QFBV64.eval_exp (exp_atomic a) s = eval_atomic a s.
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma eval_exp_rexp w (e : rexp w) s:
  QFBV64.eval_exp (exp_rexp e) s = eval_rexp e s.
Proof.
  elim: e => {w} /=.
  - reflexivity.
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2. case: op; rewrite /= IH1 IH2; reflexivity.
  - move=> w e IH m. rewrite IH; reflexivity.
Qed.

Lemma eval_bexp_rbexp e s:
  QFBV64.eval_bexp (bexp_rbexp e) s <-> eval_rbexp e s.
Proof.
  split; elim: e => /=.
  - done.
  - move=> w op e1 e2. case: op; rewrite /= 2!eval_exp_rexp.
    + done.
    + done.
    + by rewrite ltBNle.
    + by rewrite leBNlt.
  - move=> e1 IH1 e2 IH2 [H1 H2]; exact: (conj (IH1 H1) (IH2 H2)).
  - done.
  - move=> w op e1 e2; case: op; rewrite /= 2!eval_exp_rexp.
    + done.
    + done.
    + by rewrite ltBNle.
    + by rewrite leBNlt.
  - move=> e1 IH1 e2 IH2 [H1 H2]; exact: (conj (IH1 H1) (IH2 H2)).
Qed.

Lemma eval_bexp_rbexp1 e s:
  QFBV64.eval_bexp (bexp_rbexp e) s -> eval_rbexp e s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H1.
Qed.

Lemma eval_bexp_rbexp2 e s:
  eval_rbexp e s -> QFBV64.eval_bexp (bexp_rbexp e) s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H2.
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
  - (* bvAssign *)
    move=> v a Hsub Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    reflexivity.
  - (* bvAdd *)
    move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    reflexivity.
  - (* bvAddC *)
    move=> vh vl a1 a2 /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    split; reflexivity.
  - (* bvAdc *)
    move=> v a1 a2 c /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    have Hcv: (c != v).
    { move: (ssa_unchanged_instr_mem Hun Hne). rewrite /ssa_var_unchanged_instr /=.
      move/negP => Hmem. apply/negP=> Heq. apply: Hmem.
      exact: (VSLemmas.mem_singleton2 Heq). }
    rewrite (QFBV64.Store.acc_upd_neq _ _ Hcv). reflexivity.
  - (* bvAdcC *)
    move=> c v a1 a2 a /andP [/andP [/andP [Hne Hmem] Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state. repeat qfbv64_store_acc.
    have Havc: (a != v) && (a != c).
    { move: (ssa_unchanged_instr_mem Hun Hmem). rewrite /ssa_var_unchanged_instr /=.
      move=> H. move: (VSLemmas.not_mem_add1 H) => [/idP H1 H2].
      move: (VSLemmas.not_mem_singleton1 H2) => {H2} /idP H2.
      by rewrite H1 H2. }
    move/andP: Havc => [Hav Hac].
    rewrite (QFBV64.Store.acc_upd_neq _ _ Hav) (QFBV64.Store.acc_upd_neq _ _ Hac).
    split; reflexivity.
  - (* bvSub *)
    move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - (* bvMul *)
    move=> v a1 a2 /andP [Hsub1 Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - (* bvMulf *)
    move=> vh vl a1 a2 /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    by rewrite mulB_zeroExtend_fullmulB.
  - (* bvShl *)
    move=> v a n Hsub Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    reflexivity.
  - (* bvSplit *)
    move=> vh vl a n /andP [Hne Hsub] Hun Hupd.
    repeat eval_exp_exp_atomic_to_pred_state.
    repeat qfbv64_store_acc.
    split; first by reflexivity.
    rewrite fromNatK; first by reflexivity.
    exact: bv_width_sub_bounded.
  - (* bvConcatShl *)
    move=> vh vl a1 a2 n /andP [/andP [Hne Hsub1] Hsub2] Hun Hupd.
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

Lemma bexp_spec_sound_conj (vs : VS.t) (s : rspec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec_conj (bexp_of_rspec s) -> valid_rspec (bv2z_spec_rng s).
Proof.
  destruct s as [f p g].
  rewrite /bexp_of_rspec /valid_bexp_spec_conj /bv2z_spec_rng /=.
  move=> Hwfssa Hvalid s1 s2 /= Hf Hp. apply: eval_bexp_rbexp1.
  apply: Hvalid.
  - move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa]. apply: eval_bexp_rbexp2.
    apply: (proj1 (ssa_unchanged_program_eval_rbexp _ Hp) Hf).
    apply: (ssa_unchanged_program_subset Huc).
    move/andP: Hwf => /= [/andP [H _] _]. exact: (VSLemmas.subset_union5 H).
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

Lemma bexp_spec_sound_imp (vs : VS.t) (s : rspec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec_imp (bexp_of_rspec s) -> valid_rspec (bv2z_spec_rng s).
Proof.
  move=> Hw Hv.
  apply: (bexp_spec_sound_conj Hw).
  exact: valid_bexp_spec_imp_conj.
Qed.



(* Soundness *)

Definition valid_bexp_spec := valid_bexp_spec_imp.

Theorem bexp_spec_sound (vs : VS.t) (s : rspec) :
  well_formed_ssa_spec vs s ->
  valid_bexp_spec (bexp_of_rspec s) -> valid_rspec (bv2z_spec_rng s).
Proof.
  exact: bexp_spec_sound_imp.
Qed.



(* Convert conditions needed for the conversion from bvSSA to zSSA. *)

Definition bexp_atomic_addB_safe (a1 a2 : atomic) : QFBV64.bexp :=
  QFBV64.bvLneg (QFBV64.bvAddo (exp_atomic a1) (exp_atomic a2)).

Definition bexp_atomic_adcB_safe (a1 a2 : atomic) (c : var) : QFBV64.bexp :=
  QFBV64.bvConj
    (QFBV64.bvLneg (QFBV64.bvAddo (exp_atomic a1) (exp_atomic a2)))
    (QFBV64.bvLneg (QFBV64.bvAddo
                      (QFBV64.bvAdd (exp_atomic a1) (exp_atomic a2))
                      (exp_var c))).

Definition bexp_atomic_subB_safe (a1 a2 : atomic) : QFBV64.bexp :=
  QFBV64.bvLneg (QFBV64.bvSubo (exp_atomic a1) (exp_atomic a2)).

Definition bexp_atomic_mulB_safe (a1 a2 : atomic) : QFBV64.bexp :=
  QFBV64.bvLneg (QFBV64.bvMulo (exp_atomic a1) (exp_atomic a2)).

Definition bexp_atomic_shlBn_safe (a : atomic) (n : bv64SSA.value) : QFBV64.bexp :=
  QFBV64.bvUlt (exp_atomic a)
               (QFBV64.bvShl (QFBV64.bvConst (@fromNat wordsize 1))
                             (QFBV64.bvConst (fromNat (wordsize - toNat n)))).

Definition bexp_atomic_concatshl_safe (a1 a2 : atomic) (n : bv64SSA.value) : QFBV64.bexp :=
  QFBV64.bvConj
    (QFBV64.bvUle (QFBV64.bvConst n) (QFBV64.bvConst (fromNat wordsize)))
    (bexp_atomic_shlBn_safe a1 n).

Definition bexp_instr_safe (i : instr) : QFBV64.bexp :=
  match i with
  | bvAssign _ _ => QFBV64.bvTrue
  | bvAdd _ a1 a2 => bexp_atomic_addB_safe a1 a2
  | bvAddC _ _ _ _ => QFBV64.bvTrue
  | bvAdc _ a1 a2 c => bexp_atomic_adcB_safe a1 a2 c
  | bvAdcC _ _ _ _ _ => QFBV64.bvTrue
  | bvSub _ a1 a2 => bexp_atomic_subB_safe a1 a2
  | bvMul _ a1 a2 => bexp_atomic_mulB_safe a1 a2
  | bvMulf _ _ _ _ => QFBV64.bvTrue
  | bvShl _ a n => bexp_atomic_shlBn_safe a n
  | bvSplit _ _ _ _ => QFBV64.bvTrue
  | bvConcatShl _ _ a1 a2 n => bexp_atomic_concatshl_safe a1 a2 n
  end.

Fixpoint bexp_program_safe (p : program) : QFBV64.bexp :=
  match p with
  | [::] => QFBV64.bvTrue
  | hd::tl => QFBV64.bvConj (bexp_instr_safe hd) (bexp_program_safe tl)
  end.

Definition bexp_program_safe_at (p : program) s : Prop :=
  eval_bexps_imp (bexp_program p) s
                 (QFBV64.eval_bexp (bexp_program_safe p) s).



Lemma eval_bexp_atomic_addB_safe1 a1 a2 s :
  QFBV64.eval_bexp (bexp_atomic_addB_safe a1 a2) s ->
  addB_safe (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /addB_safe /= !eval_exp_atomic. move/negP=> H. exact: H.
Qed.

Lemma eval_bexp_atomic_addB_safe2 a1 a2 s :
  addB_safe (eval_atomic a1 s) (eval_atomic a2 s) ->
  QFBV64.eval_bexp (bexp_atomic_addB_safe a1 a2) s.
Proof.
  rewrite /addB_safe /= !eval_exp_atomic. move/negP=> H. exact: H.
Qed.

Lemma eval_bexp_atomic_adcB_safe1 a1 a2 c s :
  QFBV64.eval_bexp (bexp_atomic_adcB_safe a1 a2 c) s ->
  adcB_safe (eval_atomic a1 s) (eval_atomic a2 s) (State.acc c s).
Proof.
  rewrite /adcB_safe /= !eval_exp_atomic store_state_acc.
  move=> [/negP H1 /negP H2]. rewrite H1 H2. done.
Qed.

Lemma eval_bexp_atomic_adcB_safe2 a1 a2 c s :
  adcB_safe (eval_atomic a1 s) (eval_atomic a2 s) (State.acc c s) ->
  QFBV64.eval_bexp (bexp_atomic_adcB_safe a1 a2 c) s.
Proof.
  rewrite /adcB_safe /= !eval_exp_atomic store_state_acc.
  move=> /andP [H1 H2]. split; apply/negP; assumption.
Qed.

Lemma eval_bexp_atomic_subB_safe1 a1 a2 s :
  QFBV64.eval_bexp (bexp_atomic_subB_safe a1 a2) s ->
  subB_safe (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /subB_safe /= !eval_exp_atomic. move/negP=> H. exact: H.
Qed.

Lemma eval_bexp_atomic_subB_safe2 a1 a2 s :
  subB_safe (eval_atomic a1 s) (eval_atomic a2 s) ->
  QFBV64.eval_bexp (bexp_atomic_subB_safe a1 a2) s.
Proof.
  rewrite /subB_safe /= !eval_exp_atomic. move/negP=> H. exact: H.
Qed.

Lemma eval_bexp_atomic_mulB_safe1 a1 a2 s :
  QFBV64.eval_bexp (bexp_atomic_mulB_safe a1 a2) s ->
  mulB_safe (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /mulB_safe /= !eval_exp_atomic => H.
  rewrite (eqP (nneq_is_eqn H)). exact: eqxx.
Qed.

Lemma eval_bexp_atomic_mulB_safe2 a1 a2 s :
  mulB_safe (eval_atomic a1 s) (eval_atomic a2 s) ->
  QFBV64.eval_bexp (bexp_atomic_mulB_safe a1 a2) s.
Proof.
  rewrite /mulB_safe /= !eval_exp_atomic => H1 H2; apply: H2.
  rewrite (eqP H1). apply/eqP. exact: eqxx.
Qed.

Lemma eval_bexp_atomic_shlBn_safe1 a n s :
  QFBV64.eval_bexp (bexp_atomic_shlBn_safe a n) s ->
  shlBn_safe (eval_atomic a s) (toNat n).
Proof.
  rewrite /shlBn_safe /= !eval_exp_atomic => H.
  rewrite toNat_fromNat subn_modn_expn2 in H. exact: H.
Qed.

Lemma eval_bexp_atomic_shlBn_safe2 a n s :
  shlBn_safe (eval_atomic a s) (toNat n) ->
  QFBV64.eval_bexp (bexp_atomic_shlBn_safe a n) s.
Proof.
  rewrite /shlBn_safe /= !eval_exp_atomic => H.
  rewrite toNat_fromNat subn_modn_expn2. exact: H.
Qed.

Lemma eval_bexp_atomic_concatshl_safe1 a1 a2 n s :
  QFBV64.eval_bexp (bexp_atomic_concatshl_safe a1 a2 n) s ->
  concatshl_safe (eval_atomic a1 s) (eval_atomic a2 s) (toNat n).
Proof.
  rewrite /concatshl_safe /= !eval_exp_atomic => H.
  rewrite toNat_fromNat subn_modn_expn2 in H. apply/andP.
  move: H => [H1 H2]. split; last exact: H2.
  rewrite leB_nat fromNatK in H1; first exact: H1.
  by apply: ltn_expl.
Qed.

Lemma eval_bexp_atomic_concatshl_safe2 a1 a2 n s :
  concatshl_safe (eval_atomic a1 s) (eval_atomic a2 s) (toNat n) ->
  QFBV64.eval_bexp (bexp_atomic_concatshl_safe a1 a2 n) s.
Proof.
  rewrite /concatshl_safe /= !eval_exp_atomic => H.
  rewrite toNat_fromNat subn_modn_expn2. move/andP: H => [H1 H2].
  split; last exact: H2. rewrite leB_nat fromNatK; first exact: H1.
  by apply: ltn_expl.
Qed.

Lemma eval_bexp_instr_safe1 i s :
  QFBV64.eval_bexp (bexp_instr_safe i) s ->
  bv2z_instr_safe_at i s.
Proof.
  (* "elim: i => //=; intros" makes Coq freeze *)
  elim: i; intros.
  - done.
  - exact: eval_bexp_atomic_addB_safe1.
  - done.
  - exact: eval_bexp_atomic_adcB_safe1.
  - done.
  - exact: eval_bexp_atomic_subB_safe1.
  - exact: eval_bexp_atomic_mulB_safe1.
  - done.
  - exact: eval_bexp_atomic_shlBn_safe1.
  - done.
  - exact: eval_bexp_atomic_concatshl_safe1.
Qed.

Lemma eval_bexp_instr_safe2 i s :
  bv2z_instr_safe_at i s ->
  QFBV64.eval_bexp (bexp_instr_safe i) s.
Proof.
  (* "elim: i => //=; intros" makes Coq freeze *)
  case: i; intros.
  - done.
  - exact: (eval_bexp_atomic_addB_safe2 H).
  - done.
  - (* without rewriting, the exact tactic fails *)
    rewrite /bv2z_instr_safe_at in H.
    exact: (eval_bexp_atomic_adcB_safe2 H).
  - done.
  - exact: (eval_bexp_atomic_subB_safe2 H).
    (* exact: (eval_bexp_subB_safe2) is much slower. *)
  - exact: (eval_bexp_atomic_mulB_safe2 H).
  - done.
  - exact: (eval_bexp_atomic_shlBn_safe2 H).
  - done.
  - exact: (eval_bexp_atomic_concatshl_safe2 H).
Qed.

Lemma eval_exp_var_succ v i s :
  ssa_var_unchanged_instr v i ->
  QFBV64.eval_exp (exp_var v) s =
  QFBV64.eval_exp (exp_var v) (eval_instr s i).
Proof.
  move=> Hun. rewrite !(eval_exp_var v _).
  rewrite -(ssa_unchanged_instr_eval_singleton
              (ssa_unchanged_instr_singleton2 Hun) Logic.eq_refl).
  reflexivity.
Qed.

Lemma eval_exp_atomic_succ a i s :
  ssa_vars_unchanged_instr (vars_atomic a) i ->
  QFBV64.eval_exp (exp_atomic a) s =
  QFBV64.eval_exp (exp_atomic a) (eval_instr s i).
Proof.
  move=> Hun. rewrite !(eval_exp_atomic a _).
  rewrite -(ssa_unchanged_instr_eval_atomic Hun Logic.eq_refl).
  reflexivity.
Qed.

Lemma eval_exp_var_succs v p s :
  ssa_var_unchanged_program v p ->
  QFBV64.eval_exp (exp_var v) s =
  QFBV64.eval_exp (exp_var v) (eval_program s p).
Proof.
  move=> Hun. rewrite !(eval_exp_var v _).
  rewrite -(ssa_unchanged_program_eval_singleton
              (ssa_unchanged_program_singleton2 Hun) Logic.eq_refl).
  reflexivity.
Qed.

Lemma eval_exp_atomic_succs a p s :
  ssa_vars_unchanged_program (vars_atomic a) p ->
  QFBV64.eval_exp (exp_atomic a) s =
  QFBV64.eval_exp (exp_atomic a) (eval_program s p).
Proof.
  move=> Hun. rewrite !(eval_exp_atomic a _).
  rewrite -(ssa_unchanged_program_eval_atomic Hun Logic.eq_refl).
  reflexivity.
Qed.

Lemma eval_bexp_instr_safe_succ i s :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  QFBV64.eval_bexp (bexp_instr_safe i) s ->
  QFBV64.eval_bexp (bexp_instr_safe i) (eval_instr s i).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- True => by trivial
       | H : is_true (ssa_vars_unchanged_instr (VS.union _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_instr_union1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_instr (VS.add _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_instr_add1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_instr (vars_atomic ?a) _) |-
         context f [QFBV64.eval_exp (exp_atomic ?a) (State.upd _ _ ?s)] =>
         rewrite -(eval_exp_atomic_succ s H); tac
       | H : is_true (ssa_vars_unchanged_instr (vars_atomic ?a) _) |-
         context f [QFBV64.eval_exp (exp_atomic ?a) (State.upd2 _ _ _ _ ?s)] =>
         rewrite -(eval_exp_atomic_succ s H); tac
       | H : is_true (ssa_var_unchanged_instr ?v _) |-
         context f [QFBV64.Store.acc ?v (State.upd _ _ ?s)] =>
         move: (eval_exp_var_succ s H) =>
         /= <-; tac
       | H : ?p |- ?p => exact: H
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma eval_bexp_instr_safe_succs i p s :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  QFBV64.eval_bexp (bexp_instr_safe i) s ->
  QFBV64.eval_bexp (bexp_instr_safe i) (eval_program s p).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- True => by trivial
       | H : is_true (ssa_vars_unchanged_program (VS.union _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_program_union1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_program (VS.add _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_program (vars_atomic ?a) ?p) |-
         context f [QFBV64.eval_exp (exp_atomic ?a) (eval_program ?s ?p)] =>
         rewrite -(eval_exp_atomic_succs s H); tac
       | H : is_true (ssa_var_unchanged_program ?v _) |-
         context f [QFBV64.Store.acc ?v (eval_program ?s ?p)] =>
         move: (eval_exp_var_succs s H) =>
         /= <-; tac
       | H : ?p |- ?p => exact: H
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma eval_bexp_instr_safe_pred i s :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  QFBV64.eval_bexp (bexp_instr_safe i) (eval_instr s i) ->
  QFBV64.eval_bexp (bexp_instr_safe i) s.
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- True => by trivial
       | H : is_true (ssa_vars_unchanged_instr (VS.union _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_instr_union1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_instr (VS.add _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_instr_add1 H) => {H} [H1 H2]; tac
       | H1 : is_true (ssa_vars_unchanged_instr (vars_atomic ?a) _),
         H2 : context f [QFBV64.eval_exp (exp_atomic ?a) (State.upd _ _ ?s)]
         |- _ =>
         rewrite -(eval_exp_atomic_succ s H1) in H2; tac
       | H1 : is_true (ssa_vars_unchanged_instr (vars_atomic ?a) _),
         H2 : context f [QFBV64.eval_exp (exp_atomic ?a) (State.upd2 _ _ _ _ ?s)]
         |- _ =>
         rewrite -(eval_exp_atomic_succ s H1) in H2; tac
       | H1 : is_true (ssa_var_unchanged_instr ?v _),
         H2 : context f [QFBV64.Store.acc ?v (State.upd _ _ ?s)]
         |- _ =>
         move: (eval_exp_var_succ s H1) => /= <- in H2; tac
         idtac
       | H : ?p |- ?p => exact: H
       | |- _ => idtac
       end in
      tac).
Qed.

Lemma eval_bexp_instr_safe_preds i p s :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  QFBV64.eval_bexp (bexp_instr_safe i) (eval_program s p) ->
  QFBV64.eval_bexp (bexp_instr_safe i) s.
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- True => by trivial
       | H : is_true (ssa_vars_unchanged_program (VS.union _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_program_union1 H) => {H} [H1 H2]; tac
       | H : is_true (ssa_vars_unchanged_program (VS.add _ _) _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]; tac
       | H1 : is_true (ssa_vars_unchanged_program (vars_atomic ?a) _),
         H2 : context f [QFBV64.eval_exp (exp_atomic ?a) (eval_program ?s ?p)]
         |- _ =>
         rewrite -(eval_exp_atomic_succs s H1) in H2; tac
       | H1 : is_true (ssa_var_unchanged_program ?v _),
         H2 : context f [QFBV64.Store.acc ?v (eval_program ?s ?p)]
         |- _ =>
         move: (eval_exp_var_succs s H1) => /= <- in H2; tac
         idtac
       | H : ?p |- ?p => exact: H
       | |- _ => idtac
       end in
      tac).
Qed.

Lemma eval_bexp_program_safe1 vs pre p :
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program vs p ->
  (forall s, QFBV64.eval_bexp (bexp_rbexp pre) s ->
             eval_bexps_conj (bexp_program p) s ->
             QFBV64.eval_bexp (bexp_program_safe p) s) ->
  (forall s, eval_rbexp pre s ->
             bv2z_program_safe_at p s).
Proof.
  move=> Hun Hwell H s Hpre.
  set s' := eval_program s p.
  move: (eval_bexp_rbexp2 (ssa_unchanged_program_eval_rbexp1
                             Hun (Logic.eq_refl s') Hpre)) => Hpre'.
  move: (bexp_program_eval Hwell (Logic.eq_refl s')) => Hp'.
  move: (H (eval_program s p) Hpre' Hp') => {Hun H Hpre Hpre' Hp' s' pre}.
  elim: p vs s Hwell => /=.
  - done.
  - move=> i p IH vs s Hssa [Hi Hp]. move: (well_formed_ssa_tl Hssa) => Hssap.
    move: Hssa => /andP [/andP [Hwell Hun] Hssa].
    move: (well_formed_program_cons1 Hwell) (well_formed_program_cons2 Hwell)
    => {Hwell} Hwelli Hwellp.
    move: (ssa_unchanged_program_cons1 Hun) => {Hun} [Huni Hunp].
    apply/andP; split.
    + apply: eval_bexp_instr_safe1.
      apply: (eval_bexp_instr_safe_pred
                (well_formed_instr_rvs_unchanged_instr Hwelli Huni)).
      apply: (eval_bexp_instr_safe_preds _ Hi).
      exact: (well_formed_instr_rvs_unchanged_program Hwelli Hunp).
    + exact: (IH _ _ Hssap Hp).
Qed.

Lemma eval_bexp_program_safe2 vs pre p :
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program vs p ->
  (forall s, eval_rbexp pre s -> bv2z_program_safe_at p s) ->
  (forall s, QFBV64.eval_bexp (bexp_rbexp pre) s ->
             eval_bexps_conj (bexp_program p) s ->
             QFBV64.eval_bexp (bexp_program_safe p) s).
Proof.
  (* We may need to construct an initial state given a final state. *)
Abort.



Definition bv2z_spec_safe_qfbv sp : Prop :=
  forall s,
    QFBV64.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
    eval_bexps_conj (bexp_program (sprog sp)) s ->
    QFBV64.eval_bexp (bexp_program_safe (sprog sp)) s.

Lemma bv2z_spec_safe_qfbv1 vs sp :
  well_formed_ssa_spec vs sp ->
  bv2z_spec_safe_qfbv sp ->
  bv2z_spec_safe sp.
Proof.
  destruct sp as [f p g]. move => Hwell Hsafe.
  apply: (@eval_bexp_program_safe1 vs).
  - apply: (ssa_unchanged_program_subset
              (well_formed_ssa_spec_pre_unchanged Hwell)) => /=.
    exact: vars_rbexp_subset.
  - exact: (well_formed_ssa_spec_program Hwell).
  - move=> /= s Hf Hp. exact: (Hsafe _ Hf Hp).
Qed.
