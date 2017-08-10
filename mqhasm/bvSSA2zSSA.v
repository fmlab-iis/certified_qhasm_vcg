
From Coq Require Import Arith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Common Require Import Tactics Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
From mQhasm Require Import QFBV zSSA bvSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation wordsize := AMD64.wordsize.

Opaque wordsize.

Import zSSA.
Import bv64SSA.



Definition svar_notin v vs : Prop := forall i, ~~ SSAVS.mem (v, i) vs.

Lemma svar_notin_singleton1 v x :
  svar_notin v (SSAVS.singleton x) -> v != svar x.
Proof.
  destruct x as [x i]. move=> /= H; move: (VSLemmas.not_mem_singleton1 (H i)).
  move=> Hne; apply/negP => Heq; apply: Hne. rewrite (eqP Heq).
  exact: SSAVS.E.eq_refl.
Qed.

Lemma svar_notin_singleton2 v x :
  v != svar x -> svar_notin v (SSAVS.singleton x).
Proof.
  move/negP=> Hne i. apply/negP => Heq; apply: Hne.
  move: (VSLemmas.mem_singleton1 Heq) => {Heq}. destruct x as [x j] => /=.
  move/eqP => [Hv Hi]. by rewrite Hv.
Qed.

Lemma svar_notin_union1 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs1.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj1 (VSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union2 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs2.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj2 (VSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union3 v vs1 vs2 :
  svar_notin v vs1 -> svar_notin v vs2 ->
  svar_notin v (SSAVS.union vs1 vs2).
Proof.
  move=> H1 H2 i. move: (H1 i) (H2 i) => {H1 H2} H1 H2.
  exact: (VSLemmas.not_mem_union2 H1 H2).
Qed.

Lemma svar_notin_add1 v x vs :
  svar_notin v (SSAVS.add x vs) -> v != svar x.
Proof.
  destruct x as [x i] => /= H. move: (H i) => {H} H.
  move: (VSLemmas.not_mem_add1 H) => {H}. move=> [H _]; apply/negP => Heq.
  apply: H. rewrite (eqP Heq); exact: eqxx.
Qed.

Lemma svar_notin_add2 v x vs :
  svar_notin v (SSAVS.add x vs) -> svar_notin v vs.
Proof.
  move=> H i. move: (H i) => {H} H. move: (VSLemmas.not_mem_add1 H) => {H}.
  move=> [_ H]; exact: H.
Qed.

Lemma svar_notin_replace v vs1 vs2 :
  SSAVS.Equal vs1 vs2 -> svar_notin v vs1 -> svar_notin v vs2.
Proof.
  move=> H H1 x. rewrite -H. exact: H1.
Qed.

Lemma svar_notin_subset v vs1 vs2 :
  SSAVS.subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
Proof.
  move=> H H2 x. apply/negP => H1. move: (VSLemmas.mem_subset H1 H) => Hmem.
  move/negP: (H2 x). apply. exact: Hmem.
Qed.



(** Generate new SSA variables *)

Definition max_svar (vs : SSAVS.t) : VarOrder.t :=
  match SSAVS.max_elt vs with
  | Some v => svar v
  | None => 0%num
  end.

Definition new_svar (vs : SSAVS.t) : VarOrder.t :=
  N.succ (max_svar vs).

Definition new_svar_program (p : program) : VarOrder.t :=
  N.succ (max_svar (vars_program p)).

Lemma N_ltb_succ v : (v <? N.succ v)%num.
Proof.
  apply: (proj2 (N.ltb_lt v (N.succ v))). exact: N.lt_succ_diag_r.
Qed.

Lemma V_ltb_succ v i j : SSAVarOrder.ltb (v, j) ((N.succ v), i).
Proof.
  rewrite /SSAVarOrder.ltb /SSAVarOrder.M.lt /VarOrder.ltb /NOrderMinimal.lt /=.
  rewrite N_ltb_succ. exact: is_true_true.
Qed.

Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
Proof.
  rewrite /new_svar /max_svar. set x := SSAVS.max_elt vs.
  have: SSAVS.max_elt vs = x by reflexivity. case x.
  - move=> v Hmax i. apply/negP => Hmem. apply: (VSLemmas.max_elt2 Hmax Hmem).
    exact: V_ltb_succ.
  - move=> Hnone i. apply: VSLemmas.is_empty_mem.
    exact: (VSLemmas.max_elt3 Hnone).
Qed.

Lemma new_svar_notin_program p :
  svar_notin (new_svar_program p) (vars_program p).
Proof.
  exact: new_svar_notin.
Qed.



(** Convert instructions and programs. *)

Definition bv2z_atomic (a : atomic) : zSSA.exp :=
  match a with
  | bvVar v => zVar v
  | bvConst c => zConst (toPosZ c)
  end.

Definition bv2z_instr (tmp : N) (idx : N) (i : instr) : (N * seq zSSA.instr) :=
  match i with
  | bvAssign v a => (idx, [:: zAssign v (bv2z_atomic a)])
(*  | bvNeg v a => [:: zAssign v (zUnop zNeg (bv2z_atomic a))] *)
  | bvAdd v a1 a2 => (idx,
                      [:: zAssign v (zadd (bv2z_atomic a1) (bv2z_atomic a2))])
  | bvAddC c v a1 a2 =>
    (idx,
     [:: zSplit c v (zadd (bv2z_atomic a1) (bv2z_atomic a2)) wordsize])
  | bvAdc v a1 a2 y =>
    (idx,
     [:: zAssign v (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y))])
  | bvAdcC c v a1 a2 y =>
    (idx,
     [:: zSplit c v
         (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y)) wordsize])
  | bvSub v a1 a2 => (idx,
                      [:: zAssign v (zsub (bv2z_atomic a1) (bv2z_atomic a2))])
  | bvSubC c v a1 a2 =>
    (N.succ idx,
     [:: zSplit (tmp, idx) v
         (zsub (bv2z_atomic a1) (bv2z_atomic a2)) wordsize;
        zAssign c (zneg (zVar (tmp, idx)))])
  | bvSbb v a1 a2 y =>
    (idx,
     [:: zAssign v (zsub (zsub (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y))])
  | bvSbbC c v a1 a2 y =>
    (N.succ idx,
     [:: zSplit (tmp, idx) v
         (zsub (zsub (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y)) wordsize;
        zAssign c (zneg (zVar (tmp, idx)))])
  | bvMul v a1 a2 => (idx,
                      [:: zAssign v (zmul (bv2z_atomic a1) (bv2z_atomic a2))])
  | bvMulf vh vl a1 a2 =>
    (idx,
     [:: zSplit vh vl (zmul (bv2z_atomic a1) (bv2z_atomic a2)) wordsize])
  | bvShl v a n => (idx,
                    [:: zAssign v (zmul2p (bv2z_atomic a) (toNat n))])
  | bvSplit vh vl a n => (idx, [:: zSplit vh vl (bv2z_atomic a) (toNat n)])
  | bvConcatShl vh vl a1 a2 n =>
    (idx,
     [:: zSplit vh vl
         (zadd (zmul2p (bv2z_atomic a1) wordsize) (bv2z_atomic a2))
         (wordsize - (toNat n))])
  end.

Fixpoint bv2z_program (tmp : N) (idx : N) (p : program) : (N * zSSA.program) :=
  match p with
  | [::] => (idx, [::])
  | hd::tl =>
    let (idx, hd) := (bv2z_instr tmp idx hd) in
    let (idx, tl) := (bv2z_program tmp idx tl) in
    (idx, hd ++ tl)
  end.

Definition addB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_addB bv1 bv2.

Definition adcB_safe w (bv1 bv2 c : BITS w) : bool :=
  ~~ carry_addB bv1 bv2 && ~~ carry_addB (addB bv1 bv2) c.

Definition subB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_subB bv1 bv2.

Definition sbbB_safe w (bv1 bv2 c : BITS w) : bool :=
  ~~ carry_subB bv1 bv2 && ~~ carry_subB (subB bv1 bv2) c.

Definition mulB_safe w (bv1 bv2 : BITS w) : bool :=
  high w (fullmulB bv1 bv2) == fromNat 0.

Definition shlBn_safe w (bv : BITS w) n : bool :=
  ltB bv (shlBn (@fromNat w 1) (w - n)).

Definition concatshl_safe w (bv1 bv2 : BITS w) n : bool :=
  (n <= w) && shlBn_safe bv1 n.

Definition bv2z_instr_safe_at (i : instr) (s : bv64SSA.State.t) : bool :=
  match i with
  | bvAssign _ _ => true
(*  | bvNeg _ _ => true *)
  | bvAdd _ a1 a2 => addB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvAddC _ _ _ _ => true
  | bvAdc _ a1 a2 y => adcB_safe (eval_atomic a1 s) (eval_atomic a2 s)
                                 (bv64SSA.State.acc y s)
  | bvAdcC _ _ _ _ _ => true
  | bvSub _ a1 a2 => subB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvSubC _ _ _ _ => true
  | bvSbb _ a1 a2 y => sbbB_safe (eval_atomic a1 s) (eval_atomic a2 s)
                                 (bv64SSA.State.acc y s)
  | bvSbbC _ _ _ _ _ => true
  | bvMul _ a1 a2 => mulB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvMulf _ _ _ _ => true
  | bvShl _ a n => shlBn_safe (eval_atomic a s) (toNat n)
  | bvSplit _ _ _ _ => true
  | bvConcatShl _ _ a1 a2 n =>
    concatshl_safe (eval_atomic a1 s) (eval_atomic a2 s) (toNat n)
  end.

Fixpoint bv2z_program_safe_at p s : bool :=
  match p with
  | [::] => true
  | hd::tl => bv2z_instr_safe_at hd s && bv2z_program_safe_at tl (eval_instr s hd)
  end.

Definition bv2z_program_safe p : Prop :=
  forall s, bv2z_program_safe_at p s.

Lemma bv2z_program_cons tmp idx1 idx2 i p zip :
  (idx2, zip) = bv2z_program tmp idx1 (i::p) ->
  exists idx3, exists zi, exists zp,
        (idx3, zi) = bv2z_instr tmp idx1 i /\
        (idx2, zp) = bv2z_program tmp idx3 p /\
        zip = zi ++ zp.
Proof.
  rewrite /=. sethave temp (bv2z_instr tmp idx1 i). destruct temp as [idx3 zi].
  sethave temp (bv2z_program tmp idx3 p). destruct temp as [idx zp].
  move=> Hp Hi [] -> ->. exists idx3; exists zi; exists zp. done.
Qed.

Lemma bv2z_instr_idx_inc tmp idx1 idx2 i zi :
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  (idx1 <= idx2)%num.
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => -> _; tac
       | |- (?x <= ?x)%num => exact: N.le_refl
       | |- (?x <= N.succ ?x)%num => exact: N.le_succ_diag_r
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_idx_inc tmp idx1 idx2 p zp :
  (idx2, zp) = bv2z_program tmp idx1 p ->
  (idx1 <= idx2)%num.
Proof.
  elim: p idx1 idx2 zp.
  - move=> idx1 idx2 zp [] -> _. exact: N.le_refl.
  - move=> i p IH idx1 idx2 zip H. move: (bv2z_program_cons H) => {H}.
    move=> [idx3 [zi [zp [Hzi [Hzp Hzip]]]]].
    move: (bv2z_instr_idx_inc Hzi) (IH _ _ _ Hzp) => Hle1 Hle2.
    exact: (N.le_trans _ _ _ Hle1 Hle2).
Qed.

Lemma bv2z_instr_lvs_case tmp idx1 idx2 i zi v :
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  SSAVS.mem v (zSSA.lvs_program zi) ->
  SSAVS.mem v (lvs_instr i) \/
  tmp = svar v /\ (idx1 <= sidx v)%num /\ (sidx v < idx2)%num.
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H1 : (_, ?zi) = (_, _),
         H2 : is_true (SSAVS.mem _ (zSSA.lvs_program ?zi)) |- _ =>
         let H := fresh in case: H1 => -> H; rewrite H /= in H2 => {H}; tac
       | H : is_true (SSAVS.mem _ (SSAVS.singleton _)) |- _ =>
         move: (zSSA.VSLemmas.mem_singleton1 H) => {H} H; tac
       | H : is_true (SSAVS.mem _ (SSAVS.add _ _)) |- _ =>
         case: (zSSA.VSLemmas.mem_add1 H) => {H} H; tac
       | H : is_true (SSAVS.mem _ (SSAVS.union _ _)) |- _ =>
         case: (zSSA.VSLemmas.mem_union1 H) => {H} H; tac
       | H : SSAVS.E.eq ?v ?t |-
         is_true (SSAVS.mem ?v (SSAVS.singleton ?t)) \/ _ =>
         left; apply: VSLemmas.mem_singleton2; exact: H
       | H : SSAVS.E.eq ?v ?t |-
         is_true (SSAVS.mem ?v (SSAVS.add ?t _)) \/ _ =>
         left; apply: VSLemmas.mem_add2; exact: H
       | H : SSAVS.E.eq ?v ?t |-
         is_true (SSAVS.mem ?v (SSAVS.add _ (SSAVS.singleton ?t))) \/ _ =>
         left; apply: VSLemmas.mem_add3; apply: VSLemmas.mem_singleton2; exact: H
       | H : is_true (SSAVS.mem _ SSAVS.empty) |- _ =>
         apply: False_ind; rewrite zSSA.VSLemmas.mem_empty in H;
         exact: (not_false_is_true H)
       | H : SSAVS.E.eq ?v (?tmp, _) |- _ \/ (?tmp = svar ?v /\ _ /\ _) =>
         right; repeat split; [by rewrite (eqP H) | tac | tac]
       | H : SSAVS.E.eq ?v (_, ?i) |- (?i <= sidx ?v)%num =>
         rewrite (eqP H) /=; exact: N.le_refl
       | H : SSAVS.E.eq ?v (_, ?i) |- (sidx ?v < N.succ ?i)%num =>
         rewrite (eqP H0) /=; exact: N.lt_succ_diag_r
       | |- _ => idtac
       end in
      tac).
Qed.

Lemma bv2z_program_lvs_case tmp idx1 idx2 p zp v :
  (idx2, zp) = bv2z_program tmp idx1 p ->
  SSAVS.mem v (zSSA.lvs_program zp) ->
  SSAVS.mem v (lvs_program p) \/
  tmp = svar v /\ (idx1 <= sidx v)%num /\ (sidx v < idx2)%num.
Proof.
  elim: p tmp idx1 idx2 zp v => /=.
  - move=> tmp idx1 idx2 zp v [] -> -> H. apply: False_ind.
    apply: not_false_is_true. rewrite zSSA.VSLemmas.mem_empty in H.
    exact: H.
  - move=> i p IH tmp idx1 idx2 zip v Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.lvs_program_concat => Hmem.
    case: (zSSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + case: (bv2z_instr_lvs_case Hzi Hmem).
      * move=> {Hmem} Hmem; left; apply: VSLemmas.mem_union2; exact: Hmem.
      * move=> [H1 [H2 H3]]. right; repeat split; [exact: H1 | exact: H2 | idtac].
        exact: (N.lt_le_trans _ _ _ H3 (bv2z_program_idx_inc Hzp)).
    + case: (IH _ _ _ _ _ Hzp Hmem).
      * move=> {Hmem} Hmem; left; apply: VSLemmas.mem_union3; exact: Hmem.
      * move=> [H1 [H2 H3]]. right; repeat split; [exact: H1 | idtac | exact: H3].
        exact: (N.le_trans _ _ _ (bv2z_instr_idx_inc Hzi) H2).
Qed.



(** State equivalence. *)

Definition bvz_eq (sb : State.t) (sz : zSSA.State.t) : Prop :=
  forall x, toPosZ (State.acc x sb) = zSSA.State.acc x sz.

Lemma bvz_eq_upd v bv zv sb sz :
  bvz_eq sb sz ->
  toPosZ bv = zv ->
  bvz_eq (State.upd v bv sb) (zSSA.State.upd v zv sz).
Proof.
  move=> Heq Hbv x. case Hxv: (x == v).
  - rewrite (State.acc_upd_eq _ _ Hxv) (zSSA.State.acc_upd_eq _ _ Hxv).
    exact: Hbv.
  - move/idP/negP: Hxv => Hxv.
    rewrite (State.acc_upd_neq _ _ Hxv) (zSSA.State.acc_upd_neq _ _ Hxv).
    exact: Heq.
Qed.

Lemma bvz_eq_upd2 vh vl bvh bvl zvh zvl sb sz :
  bvz_eq sb sz ->
  toPosZ bvh = zvh ->
  toPosZ bvl = zvl ->
  bvz_eq (State.upd2 vh bvh vl bvl sb) (zSSA.State.upd2 vh zvh vl zvl sz).
Proof.
  move=> Heq Hbvh Hbvl x. case Hxvl: (x == vl).
  - rewrite (State.acc_upd_eq _ _ Hxvl) (zSSA.State.acc_upd_eq _ _ Hxvl).
    exact: Hbvl.
  - move/idP/negP: Hxvl => Hxvl.
    rewrite (State.acc_upd_neq _ _ Hxvl) (zSSA.State.acc_upd_neq _ _ Hxvl).
    case Hxvh: (x == vh).
    + rewrite (State.acc_upd_eq _ _ Hxvh) (zSSA.State.acc_upd_eq _ _ Hxvh).
      exact: Hbvh.
    + move/idP/negP: Hxvh => Hxvh.
      rewrite (State.acc_upd_neq _ _ Hxvh) (zSSA.State.acc_upd_neq _ _ Hxvh).
      exact: Heq.
Qed.



(** State equivalence except a set of variables. *)

Definition bvz_eqm (tmp : VarOrder.t) (sb : State.t) (sz : zSSA.State.t) : Prop :=
  forall x, tmp != svar x ->
            (toPosZ (State.acc x sb) = zSSA.State.acc x sz).

Lemma bvz_eq_eqm tmp sb sz : bvz_eq sb sz -> bvz_eqm tmp sb sz.
Proof.
  move=> H x _. exact: H.
Qed.

Lemma bvz_eqm_upd v bv zv tmp sb sz :
  bvz_eqm tmp sb sz ->
  toPosZ bv = zv ->
  bvz_eqm tmp (State.upd v bv sb) (zSSA.State.upd v zv sz).
Proof.
  move=> Heq Hbv x Hne. case Hxv: (x == v).
  - rewrite (State.acc_upd_eq _ _ Hxv) (zSSA.State.acc_upd_eq _ _ Hxv).
    exact: Hbv.
  - move/idP/negP: Hxv => Hxv.
    rewrite (State.acc_upd_neq _ _ Hxv) (zSSA.State.acc_upd_neq _ _ Hxv).
    exact: (Heq _ Hne).
Qed.

Lemma bvz_eqm_upd2 vh vl bvh bvl zvh zvl tmp sb sz :
  bvz_eqm tmp sb sz ->
  toPosZ bvh = zvh ->
  toPosZ bvl = zvl ->
  bvz_eqm tmp (State.upd2 vh bvh vl bvl sb) (zSSA.State.upd2 vh zvh vl zvl sz).
Proof.
  move=> Heq Hbvh Hbvl x Hne. case Hxvl: (x == vl).
  - rewrite (State.acc_upd_eq _ _ Hxvl) (zSSA.State.acc_upd_eq _ _ Hxvl).
    exact: Hbvl.
  - move/idP/negP: Hxvl => Hxvl.
    rewrite (State.acc_upd_neq _ _ Hxvl) (zSSA.State.acc_upd_neq _ _ Hxvl).
    case Hxvh: (x == vh).
    + rewrite (State.acc_upd_eq _ _ Hxvh) (zSSA.State.acc_upd_eq _ _ Hxvh).
      exact: Hbvh.
    + move/idP/negP: Hxvh => Hxvh.
      rewrite (State.acc_upd_neq _ _ Hxvh) (zSSA.State.acc_upd_neq _ _ Hxvh).
      exact: (Heq _ Hne).
Qed.

Lemma bvz_eqm_upd2_aux c v bvc bvv zvc zvv zvt tmp idx sb sz :
  bvz_eqm tmp sb sz ->
  toPosZ bvc = zvc ->
  toPosZ bvv = zvv ->
  tmp != svar c ->
  tmp != svar v ->
  bvz_eqm tmp
          (State.upd2 v bvv c bvc sb)
          (zSSA.State.upd c
                          zvc
                          (zSSA.State.upd2 v zvv (tmp, idx) zvt sz)).
Proof.
  move=> Heqm Hc Hv Hnec Hnev x Hnex.
  case Hxc: (x == c).
  - rewrite (zSSA.State.acc_upd_eq _ _ Hxc) (State.acc_upd2_eq2 _ _ _ _ Hxc).
    exact: Hc.
  - move/idP/negP: Hxc => Hxc. rewrite (zSSA.State.acc_upd_neq _ _ Hxc).
    have Hxtmp: x != (tmp, idx).
    { apply/negP => Heq. move/negP: Hnex; apply. by rewrite (eqP Heq). }
    case Hxv: (x == v).
    + rewrite (State.acc_upd2_eq1 _ _ _ Hxv Hxc).
      rewrite (zSSA.State.acc_upd2_eq1 _ _ _ Hxv Hxtmp). exact: Hv.
    + move/idP/negP: Hxv => Hxv.
      rewrite (State.acc_upd2_neq _ _ _ Hxv Hxc).
      rewrite (zSSA.State.acc_upd2_neq _ _ _ Hxv Hxtmp).
      exact: (Heqm _ Hnex).
Qed.



(** Properties of program conversion. *)

Lemma bvz_eqm_eval_atomic tmp a sb sz :
  bvz_eqm tmp sb sz ->
  svar_notin tmp (vars_atomic a) ->
  toPosZ (eval_atomic a sb) = (zSSA.eval_exp (bv2z_atomic a) sz).
Proof.
  move=> Heqm; case: a => /=.
  - move=> x Hnotin. exact: (Heqm _ (svar_notin_singleton1 Hnotin)).
  - reflexivity.
Qed.

Lemma bvz_eqm_eval_instr tmp idx1 idx2 i zi sb sz :
  bvz_eqm tmp sb sz ->
  svar_notin tmp (vars_instr i) ->
  bv2z_instr_safe_at i sb ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  bvz_eqm tmp (eval_instr sb i) (zSSA.eval_program sz zi).
Proof.
  move=> Heqm; case: i.
  - (* bvAssign *)
    move=> v a Hnotin _ [] _ -> /=. apply: (bvz_eqm_upd _ Heqm).
    exact: (bvz_eqm_eval_atomic Heqm (svar_notin_add2 Hnotin)).
  - (* bvAdd *)
    move=> v a1 a2 Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add2 Hnotin) => {Hnotin} Hnotin.
    apply: (bvz_eqm_upd _ Heqm).
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    exact: toPosZ_addB_bounded.
  - (* bvAddC *)
    move=> c v a1 a2 Hnotin _ [] _ -> /=.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    sethave temp
            (Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                        (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr. apply: (bvz_eqm_upd2 _ _ Heqm).
    + exact: (toPosZ_addB_zeroExtend_low Hqr).
    + exact: (toPosZ_addB_zeroExtend_high Hqr).
  - (* bvAdc *)
    move=> v a1 a2 y Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add1 Hnotin) => Hne.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    apply: (bvz_eqm_upd _ Heqm).
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin))
            -(Heqm _ Hne).
    move: Hsafe => /andP [Hsafe1 Hsafe2].
    exact: toPosZ_addB3_bounded.
  - (* bvAdcC *)
    move=> c v a1 a2 y Hnotin _ [] _ -> /=.
    move: (svar_notin_add1 Hnotin) => Hne.
    move: (svar_notin_add2 (svar_notin_add2 (svar_notin_add2 Hnotin)))
          => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin))
            -(Heqm _ Hne).
    sethave temp
            (Z.div_eucl
               (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb) +
                toPosZ (State.acc y sb)) (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr.
    apply: (bvz_eqm_upd2 _ _ Heqm).
    + exact: (toPosZ_addB3_zeroExtend_low Hqr).
    + exact: (toPosZ_addB3_zeroExtend_high Hqr).
  - (* bvSub *)
    move=> v a1 a2 Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add2 Hnotin) => {Hnotin} Hnotin.
    apply: (bvz_eqm_upd _ Heqm).
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    exact: toPosZ_subB_bounded.
  - (* bvSubC *)
    move=> c v a1 a2 Hnotin _ [] _ -> /=.
    move: (svar_notin_add1 Hnotin) => Hnec.
    move: (svar_notin_add1 (svar_notin_add2 Hnotin)) => Hnev.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    sethave temp (Z.div_eucl
                    (toPosZ (eval_atomic a1 sb) - toPosZ (eval_atomic a2 sb))
                    (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr.
    apply: (bvz_eqm_upd2_aux _ _ Heqm _ _ Hnec Hnev).
    + rewrite (zSSA.State.acc_upd2_eq2 _ _ _ _ (eqxx (tmp, idx1))).
      exact: (toPosZ_subB_zeroExtend_high Hqr).
    + exact: (toPosZ_subB_zeroExtend_low Hqr).
  - (* bvSbb *)
    move=> v a1 a2 y Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add1 Hnotin) => Hne.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    apply: (bvz_eqm_upd _ Heqm).
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin))
            -(Heqm _ Hne).
    move: Hsafe => /andP [Hsafe1 Hsafe2].
    exact: toPosZ_subB3_bounded.
  - (* bvSbbC *)
    move=> c v a1 a2 y Hnotin _ [] _ -> /=.
    move: (svar_notin_add1 Hnotin) => Hney.
    move: (svar_notin_add1 (svar_notin_add2 Hnotin)) => Hnec.
    move: (svar_notin_add1 (svar_notin_add2 ((svar_notin_add2 Hnotin)))) => Hnev.
    move: (svar_notin_add2 (svar_notin_add2 ((svar_notin_add2 Hnotin))))
    => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin))
            -(Heqm _ Hney).
    sethave temp (Z.div_eucl
                    (toPosZ (eval_atomic a1 sb) - toPosZ (eval_atomic a2 sb) -
                     toPosZ (State.acc y sb)) (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr.
    apply: (bvz_eqm_upd2_aux _ _ Heqm _ _ Hnec Hnev).
    + rewrite (zSSA.State.acc_upd2_eq2 _ _ _ _ (eqxx (tmp, idx1))).
      exact: (toPosZ_subB3_zeroExtend_high Hqr).
    + exact: (toPosZ_subB3_zeroExtend_low Hqr).
  - (* bvMul *)
    move=> v a1 a2 Hnotin Hsafe [] _ -> /=. apply: (bvz_eqm_upd _ Heqm).
    move: (svar_notin_add2 Hnotin) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    apply: toPosZ_mulB_bounded. rewrite -fromNat0. apply/eqP.
    exact: Hsafe.
  - (* bvMulf *)
    move=> vh vl a1 a2 Hnotin _ [] _ -> /=.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    sethave temp
            (Z.div_eucl (toPosZ (eval_atomic a1 sb) * toPosZ (eval_atomic a2 sb))
                        (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr. apply: (bvz_eqm_upd2 _ _ Heqm).
    + exact: (toPosZ_fullmulB_low Hqr).
    + exact: (toPosZ_fullmulB_high Hqr).
  - (* bvShl *)
    move=> v a n Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add2 Hnotin) => {Hnotin} Hnotin.
    apply: (bvz_eqm_upd _ Heqm). rewrite -(bvz_eqm_eval_atomic Heqm Hnotin).
    exact: toPosZ_shlBn_bounded.
  - (* bvSplit *)
    move=> vh vl a n Hnotin _ [] _ -> /=.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm Hnotin).
    set temp := Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n)).
    have: temp = Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n))
      by reflexivity.
    destruct temp as [q r] => Hqr.
    apply: (bvz_eqm_upd2 _ _ Heqm).
    + exact: (toPosZ_shrBn_low Hqr).
    + exact: (toPosZ_shrBn_high Hqr).
  - (* bvConcatShl *)
    move=> vh vl a1 a2 n Hnotin Hsafe [] _ -> /=.
    move: (svar_notin_add2 (svar_notin_add2 Hnotin)) => {Hnotin} Hnotin.
    rewrite -(bvz_eqm_eval_atomic Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_atomic Heqm (svar_notin_union2 Hnotin)).
    sethave temp
            (Z.div_eucl
               (toPosZ (eval_atomic a1 sb) *
                2 ^ Z.of_nat wordsize +
                    toPosZ (eval_atomic a2 sb))
               (2 ^ Z.of_nat (wordsize - (toNat n)))).
    destruct temp as [q r] => Hqr. move/andP: Hsafe => [Hle Hsafe].
    apply: (bvz_eqm_upd2 _ _ Heqm).
    + exact: (toPosZ_catB_shlBn_low_shrBn Hle Hsafe Hqr).
    + exact: (toPosZ_catB_shlBn_high Hle Hsafe Hqr).
Qed.

Lemma bvz_eqm_eval_program tmp idx1 idx2 p zp sb sz :
  bvz_eqm tmp sb sz ->
  svar_notin tmp (vars_program p) ->
  bv2z_program_safe_at p sb ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  bvz_eqm tmp (eval_program sb p) (zSSA.eval_program sz zp).
Proof.
  elim: p tmp idx1 idx2 zp sb sz.
  - move=> tmp idx1 idx2 zp sb sz Heqm Hnotin _ /= [] _ ->. exact: Heqm.
  - move=> hd tl IH tmp idx1 idx2 zip sb sz Heqm Hnotin /andP [Hhd Htl] Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.eval_program_concat_step.
    move: (svar_notin_union1 Hnotin) (svar_notin_union2 Hnotin) =>
    {Hnotin} Hnotinhd Hnotintl. apply: (IH _ _ _ _ _ _ _ _ _ Hzp).
    + apply: (bvz_eqm_eval_instr Heqm Hnotinhd Hhd Hzi).
    + exact: Hnotintl.
    + exact: Htl.
Qed.



(** Convert specifications. *)

Definition bv2z_unop (op : unop) : zSSA.unop :=
  match op with
  | bvNegOp => zSSA.zNeg
  end.

Definition bv2z_binop (op : binop) : zSSA.binop :=
  match op with
  | bvAddOp => zSSA.zAdd
  | bvSubOp => zSSA.zSub
  | bvMulOp => zSSA.zMul
  end.

Fixpoint bv2z_eexp (e : eexp) : zSSA.exp :=
  match e with
  | bveVar v => zVar v
  | bveConst c => zConst c
  | bveUnop op e => zUnop (bv2z_unop op) (bv2z_eexp e)
  | bveBinop op e1 e2 => zBinop (bv2z_binop op) (bv2z_eexp e1) (bv2z_eexp e2)
  end.

Fixpoint bv2z_ebexp e : zSSA.bexp :=
  match e with
  | bveTrue => zSSA.zTrue
  | bveEq e1 e2 => zSSA.zEq (bv2z_eexp e1) (bv2z_eexp e2)
  | bveEqMod e1 e2 p => zSSA.zEqMod (bv2z_eexp e1) (bv2z_eexp e2) (bv2z_eexp p)
  | bveAnd e1 e2 => zSSA.zAnd (bv2z_ebexp e1) (bv2z_ebexp e2)
  end.

Definition bv2z_spec_rng s : rspec :=
  {| rspre := rng_bexp (spre s);
     rsprog := sprog s;
     rspost := rng_bexp (spost s) |}.

Definition initial_tmp_sidx : N := 1.

Definition new_svar_spec_eqn vs s : VarOrder.t :=
  new_svar (SSAVS.union vs
                     (SSAVS.union
                        (vars_bexp (spre s))
                        (SSAVS.union (vars_program (sprog s))
                                  (vars_bexp (spost s))))).

(* vs: input variables
   s: specification *)
Definition bv2z_spec_eqn vs s : zSSA.spec :=
  let (idx, zp) := bv2z_program (new_svar_spec_eqn vs s)
                                initial_tmp_sidx (sprog s) in
  {| zSSA.spre := bv2z_ebexp (eqn_bexp (spre s));
     zSSA.sprog := zp;
     zSSA.spost := bv2z_ebexp (eqn_bexp (spost s)) |}.

Definition bv2z_spec_safe sp :=
  forall s, eval_rbexp (rng_bexp (spre sp)) s ->
            bv2z_program_safe_at (sprog sp) s.

Lemma svar_notin_inputs vs s :
  svar_notin (new_svar_spec_eqn vs s) vs.
Proof.
  rewrite /new_svar_spec_eqn.
  set ss := (SSAVS.union vs
                     (SSAVS.union (vars_bexp (spre s))
                               (SSAVS.union (vars_program (sprog s))
                                         (vars_bexp (spost s))))).
  move: (new_svar_notin ss) => H. exact: (svar_notin_union1 H).
Qed.

Lemma svar_notin_spre vs s :
  svar_notin (new_svar_spec_eqn vs s) (vars_bexp (spre s)).
Proof.
  rewrite /new_svar_spec_eqn.
  set ss := (SSAVS.union vs
                     (SSAVS.union (vars_bexp (spre s))
                               (SSAVS.union (vars_program (sprog s))
                                         (vars_bexp (spost s))))).
  move: (new_svar_notin ss) => H.
  exact: (svar_notin_union1 (svar_notin_union2 H)).
Qed.

Lemma svar_notin_sprog vs s :
  svar_notin (new_svar_spec_eqn vs s) (vars_program (sprog s)).
Proof.
  rewrite /new_svar_spec_eqn.
  set ss := (SSAVS.union vs
                     (SSAVS.union (vars_bexp (spre s))
                               (SSAVS.union (vars_program (sprog s))
                                         (vars_bexp (spost s))))).
  move: (new_svar_notin ss) => H.
  exact: (svar_notin_union1 (svar_notin_union2 (svar_notin_union2 H))).
Qed.

Lemma svar_notin_spost vs s :
  svar_notin (new_svar_spec_eqn vs s) (vars_bexp (spost s)).
Proof.
  rewrite /new_svar_spec_eqn.
  set ss := (SSAVS.union vs
                     (SSAVS.union (vars_bexp (spre s))
                               (SSAVS.union (vars_program (sprog s))
                                         (vars_bexp (spost s))))).
  move: (new_svar_notin ss) => H.
  exact: (svar_notin_union2 (svar_notin_union2 (svar_notin_union2 H))).
Qed.



(** Properties of specification conversion. *)

Lemma bvz_eq_eval_eunop op (v : Z) :
  eval_eunop op v =
  zSSA.eval_unop (bv2z_unop op) v.
Proof.
  case: op; reflexivity.
Qed.

Lemma bvz_eq_eval_ebinop op (v1 v2 : Z) :
  eval_ebinop op v1 v2 =
  zSSA.eval_binop (bv2z_binop op) v1 v2.
Proof.
  case: op; reflexivity.
Qed.

Lemma bvz_eq_eval_eexp (e : eexp) bs zs :
  bvz_eq bs zs ->
  eval_eexp e bs = zSSA.eval_exp (bv2z_eexp e) zs.
Proof.
  elim: e => /=.
  - move=> a Heq. exact: Heq.
  - reflexivity.
  - move=> op e IH Heq. rewrite -(IH Heq). exact: bvz_eq_eval_eunop.
  - move=> op e1 IH1 e2 IH2 Heq. rewrite -(IH1 Heq) -(IH2 Heq).
    exact: bvz_eq_eval_ebinop.
Qed.

Lemma bvz_eq_eval_ebexp1 e bs zs :
  bvz_eq bs zs ->
  eval_ebexp e bs ->
  zSSA.eval_bexp (bv2z_ebexp e) zs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heq Heval.
    rewrite -(bvz_eq_eval_eexp e1 Heq) -(bvz_eq_eval_eexp e2 Heq). exact: Heval.
  - move=> e1 e2 p Heq Heval.
    rewrite -(bvz_eq_eval_eexp e1 Heq) -(bvz_eq_eval_eexp e2 Heq)
            -(bvz_eq_eval_eexp p Heq). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heq [Heval1 Heval2].
    split; [exact: (IH1 Heq Heval1) | exact: (IH2 Heq Heval2)].
Qed.

Lemma bvz_eq_eval_ebexp2 e bs zs :
  bvz_eq bs zs ->
  zSSA.eval_bexp (bv2z_ebexp e) zs ->
  eval_ebexp e bs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heq Heval.
    rewrite (bvz_eq_eval_eexp e1 Heq) (bvz_eq_eval_eexp e2 Heq). exact: Heval.
  - move=> e1 e2 p Heq Heval.
    rewrite (bvz_eq_eval_eexp e1 Heq) (bvz_eq_eval_eexp e2 Heq)
            (bvz_eq_eval_eexp p Heq). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heq [Heval1 Heval2].
    split; [exact: (IH1 Heq Heval1) | exact: (IH2 Heq Heval2)].
Qed.

Lemma eval_bexp_combine e bs zs :
  bvz_eq bs zs ->
  eval_rbexp (rng_bexp e) bs ->
  zSSA.eval_bexp (bv2z_ebexp (eqn_bexp e)) zs ->
  eval_bexp e bs.
Proof.
  move=> Heq Her Hee. split.
  - exact: (bvz_eq_eval_ebexp2 Heq Hee).
  - exact: Her.
Qed.

Lemma bvz_eqm_eval_eexp tmp (e : eexp) bs zs :
  bvz_eqm tmp bs zs ->
  svar_notin tmp (vars_eexp e) ->
  eval_eexp e bs = zSSA.eval_exp (bv2z_eexp e) zs.
Proof.
  elim: e => /=.
  - move=> a Heqm Hnotin. exact: (Heqm _ (svar_notin_singleton1 Hnotin)).
  - reflexivity.
  - move=> op e IH Heqm Hnotin. rewrite -(IH Heqm Hnotin).
    exact: bvz_eq_eval_eunop.
  - move=> op e1 IH1 e2 IH2 Heqm Hnotin.
    rewrite -(IH1 Heqm (svar_notin_union1 Hnotin))
            -(IH2 Heqm (svar_notin_union2 Hnotin)).
    exact: bvz_eq_eval_ebinop.
Qed.

Lemma bvz_eqm_eval_ebexp1 tmp e bs zs :
  bvz_eqm tmp bs zs ->
  svar_notin tmp (vars_ebexp e) ->
  eval_ebexp e bs ->
  zSSA.eval_bexp (bv2z_ebexp e) zs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heqm Hnotin Heval.
    rewrite -(bvz_eqm_eval_eexp Heqm (svar_notin_union1 Hnotin))
            -(bvz_eqm_eval_eexp Heqm (svar_notin_union2 Hnotin)). exact: Heval.
  - move=> e1 e2 p Heqm Hnotin Heval.
    move: (svar_notin_union1 Hnotin)
          (svar_notin_union1 (svar_notin_union2 Hnotin))
          (svar_notin_union2 (svar_notin_union2 Hnotin)) =>
    {Hnotin} He1 He2 Hp.
    rewrite -(bvz_eqm_eval_eexp Heqm He1) -(bvz_eqm_eval_eexp Heqm He2)
            -(bvz_eqm_eval_eexp Heqm Hp). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heqm Hnotin [Heval1 Heval2].
    split; [exact: (IH1 Heqm (svar_notin_union1 Hnotin) Heval1) |
            exact: (IH2 Heqm (svar_notin_union2 Hnotin) Heval2)].
Qed.

Lemma bvz_eqm_eval_ebexp2 tmp e bs zs :
  bvz_eqm tmp bs zs ->
  svar_notin tmp (vars_ebexp e) ->
  zSSA.eval_bexp (bv2z_ebexp e) zs ->
  eval_ebexp e bs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heqm Hnotin Heval.
    rewrite (bvz_eqm_eval_eexp Heqm (svar_notin_union1 Hnotin))
            (bvz_eqm_eval_eexp Heqm (svar_notin_union2 Hnotin)). exact: Heval.
  - move=> e1 e2 p Heqm Hnotin Heval.
    move: (svar_notin_union1 Hnotin)
          (svar_notin_union1 (svar_notin_union2 Hnotin))
          (svar_notin_union2 (svar_notin_union2 Hnotin)) =>
    {Hnotin} He1 He2 Hp.
    rewrite (bvz_eqm_eval_eexp Heqm He1) (bvz_eqm_eval_eexp Heqm He2)
            (bvz_eqm_eval_eexp Heqm Hp). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heqm Hnotin [Heval1 Heval2].
    split; [exact: (IH1 Heqm (svar_notin_union1 Hnotin) Heval1) |
            exact: (IH2 Heqm (svar_notin_union2 Hnotin) Heval2)].
Qed.

Lemma eval_bexp_combine_eqm tmp e bs zs :
  bvz_eqm tmp bs zs ->
  svar_notin tmp (vars_bexp e) ->
  eval_rbexp (rng_bexp e) bs ->
  zSSA.eval_bexp (bv2z_ebexp (eqn_bexp e)) zs ->
  eval_bexp e bs.
Proof.
  move=> Heqm Hnotin Her Hee. split.
  - exact: (bvz_eqm_eval_ebexp2 Heqm (svar_notin_union1 Hnotin) Hee).
  - exact: Her.
Qed.



(** Convert bvState to zState. *)

Definition bv2z_state bs : zSSA.State.t :=
  fun v => toPosZ (State.acc v bs).

Lemma bv2z_state_eq bs :
  bvz_eq bs (bv2z_state bs).
Proof.
  move=> x; reflexivity.
Qed.


(** Well-formedness *)

Lemma bv2z_atomic_vars a :
  SSAVS.Equal (zSSA.vars_exp (bv2z_atomic a)) (bv64SSA.vars_atomic a).
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma bv2z_eexp_vars (e : eexp) :
  SSAVS.Equal (zSSA.vars_exp (bv2z_eexp e)) (vars_eexp e).
Proof.
  elim: e => /=.
  - reflexivity.
  - reflexivity.
  - move=> _ e IH. exact: IH.
  - move=> _ e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
Qed.

(* Convert (vars_* (bv2z_* _)) to (vars_* _). *)
Ltac vars_to_bvssa :=
  match goal with
  | |- context f [SSAVS.union _ SSAVS.empty] =>
    rewrite zSSA.VSLemmas.union_emptyr; vars_to_bvssa
  | |- context f [vars_exp (bv2z_atomic _)] =>
    rewrite !bv2z_atomic_vars; vars_to_bvssa
  | |- context f [vars_exp (bv2z_eexp _)] =>
    rewrite !bv2z_eexp_vars; vars_to_bvssa
  | |- _ => idtac
  end.

Lemma bv2z_instr_lvs_subset tmp idx1 idx2 i zi :
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  SSAVS.subset (lvs_instr i) (zSSA.lvs_program zi).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- _ => zSSA.VSLemmas.dp_subset
       end in
   tac).
Qed.

Lemma bv2z_program_lvs_subset tmp idx1 idx2 p zp :
  (idx2, zp) = bv2z_program tmp idx1 p ->
  SSAVS.subset (lvs_program p) (zSSA.lvs_program zp).
Proof.
  elim: p tmp idx1 idx2 zp => /=.
  - move=> _ idx1 idx2 zp [] _ ->. done.
  - move=> i p IH tmp idx1 idx2 zip Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.lvs_program_concat. apply: zSSA.VSLemmas.union_subsets.
    + exact: (bv2z_instr_lvs_subset Hzi).
    + exact: (IH _ _ _ _ Hzp).
Qed.

Lemma bv2z_instr_vars_subset tmp idx1 idx2 i zi :
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  SSAVS.subset (vars_instr i) (zSSA.vars_program zi).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- is_true (SSAVS.mem _ _) => zSSA.VSLemmas.dp_mem
       | |- is_true (SSAVS.subset _ _) => vars_to_bvssa; zSSA.VSLemmas.dp_subset
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_vars_subset tmp idx1 idx2 p zp :
  (idx2, zp) = bv2z_program tmp idx1 p ->
  SSAVS.subset (vars_program p) (zSSA.vars_program zp).
Proof.
  elim: p tmp idx1 idx2 zp => /=.
  - move=> _ idx1 idx2 zp [] _ ->. done.
  - move=> i p IH tmp idx1 idx2 zip Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.vars_program_concat. apply: zSSA.VSLemmas.union_subsets.
    + exact: (bv2z_instr_vars_subset Hzi).
    + exact: (IH _ _ _ _ Hzp).
Qed.

Lemma bv2z_ebexp_vars_subset f :
  SSAVS.subset (zSSA.vars_bexp (bv2z_ebexp (eqn_bexp f))) (vars_bexp f).
Proof.
  case: f => e r /=. apply: zSSA.VSLemmas.subset_union1 => /= {r}.
  elim: e => /=; intros; vars_to_bvssa; zSSA.VSLemmas.dp_subset.
Qed.

Ltac split_svar_notin_hyp :=
  match goal with
  | H : svar_notin _ (SSAVS.add _ _) |- _ =>
    let H1 := fresh in let H2 := fresh in
    move: (svar_notin_add1 H) (svar_notin_add2 H) => {H} H1 H2;
    split_svar_notin_hyp
  | H : svar_notin _ (SSAVS.union _ _) |- _ =>
    let H1 := fresh in let H2 := fresh in
    move: (svar_notin_union1 H) (svar_notin_union2 H) => {H} H1 H2;
    split_svar_notin_hyp
  | |- _ => idtac
  end.

Lemma bv2z_instr_well_formed tmp idx1 idx2 vs i zi :
  svar_notin tmp (vars_instr i) ->
  well_formed_instr vs i ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  zSSA.well_formed_program vs zi.
Proof.
  case: i => /=; intros; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | |- is_true true => done
       | H : ?p |- ?p => exact: H
       | H : is_true (?x != svar ?y) |- is_true ((?x, _) != ?y) =>
         apply: svar_ne; exact: H
       (* *)
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | H : is_true (_ && _) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move/andP: H => [H1 H2]; tac
       (* *)
       | |- is_true (SSAVS.subset _ _) => vars_to_bvssa; VSLemmas.dp_subset
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_well_formed tmp idx1 idx2 vs p zp :
  svar_notin tmp (vars_program p) ->
  well_formed_program vs p ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  zSSA.well_formed_program vs zp.
Proof.
  elim: p tmp idx1 idx2 vs zp => /=.
  - move=> tmp idx1 idx2 vs zp _ _ [] _ ->; done.
  - move=> hd tl IH tmp idx1 idx2 vs zip Hnotin /andP [Hwellhd Hwelltl] Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.well_formed_program_concat.
    rewrite (bv2z_instr_well_formed (svar_notin_union1 Hnotin) Hwellhd Hzi) /=.
    apply: (@zSSA.well_formed_program_subset (SSAVS.union vs (lvs_instr hd))).
    + exact: (IH _ _ _ _ _ (svar_notin_union2 Hnotin) Hwelltl Hzp).
    + move: (bv2z_instr_lvs_subset Hzi) => Hsubset. zSSA.VSLemmas.dp_subset.
Qed.

Lemma bv2z_var_unchanged_instr tmp idx1 idx2 vs v i zi :
  svar_notin tmp vs ->
  ssa_vars_unchanged_instr vs i ->
  SSAVS.mem v vs ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  zSSA.ssa_var_unchanged_program v zi.
Proof.
  case: i => /=; intros; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | |- is_true (zSSA.ssa_var_unchanged_instr _ _) =>
         rewrite /zSSA.ssa_var_unchanged_instr /=; tac
       | H1 : is_true (ssa_vars_unchanged_instr ?vs _),
         H2 : is_true (SSAVS.mem ?v ?vs) |- _ =>
         move: (ssa_unchanged_instr_mem H1 H2);
         rewrite /ssa_var_unchanged_instr /= => {H1} H1; tac
       | H : is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) |- _ =>
         move: (VSLemmas.not_mem_singleton1 H) => {H} H; tac
       | H : is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (VSLemmas.not_mem_add1 H) => {H} [H1 H2]; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) =>
         apply: zSSA.VSLemmas.not_mem_singleton2; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) =>
         apply: zSSA.VSLemmas.not_mem_add2; split; tac
       | |- is_true true => done
       | H : ?p |- ?p => exact: H
       | H1 : svar_notin ?tmp ?vs, H2 : is_true (SSAVS.mem ?v ?vs) |-
         ~ (SSAVS.E.eq v (?tmp, ?i)) =>
         let H := fresh in
         move=> H; rewrite (eqP H) in H2; move: (H1 i); rewrite H2; done
       | |- _ => idtac
       end in
      tac).
Qed.

Lemma bv2z_var_unchanged_program tmp idx1 idx2 vs v p zp :
  svar_notin tmp vs ->
  ssa_vars_unchanged_program vs p ->
  SSAVS.mem v vs ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  zSSA.ssa_var_unchanged_program v zp.
Proof.
  elim: p idx1 idx2 vs v zp => /=.
  - move=> idx1 idx2 vs v zp _ _ _ [] _ ->.
    exact: zSSA.ssa_var_unchanged_program_empty.
  - move=> i p IH idx1 idx2 vs v zip Hnotin Hunch Hmem Hzip.
    move: (ssa_unchanged_program_cons1 Hunch) => {Hunch} [Hi Hp].
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    rewrite zSSA.ssa_var_unchanged_program_concat2.
    + done.
    + exact: (bv2z_var_unchanged_instr Hnotin Hi Hmem Hzi).
    + apply: (IH _ _ _ _ _ Hnotin Hp Hmem Hzp).
Qed.

Lemma bv2z_vars_unchanged_instr tmp idx1 idx2 vs i zi :
  svar_notin tmp vs ->
  ssa_vars_unchanged_instr vs i ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  zSSA.ssa_vars_unchanged_program vs zi.
Proof.
  case: i => /=; intros; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- is_true (zSSA.ssa_vars_unchanged_program _ _) =>
         let x := fresh in let Hx := fresh in
         apply: zSSA.ssa_unchanged_program_global => x Hx /=; tac
       | H1 : is_true (ssa_vars_unchanged_instr ?vs _),
         H2 : is_true (SSAVS.mem ?x ?vs) |- _ =>
         let H := fresh in
         move: (ssa_unchanged_instr_local H1 H2) => {H1} H; tac
       | H : is_true (ssa_var_unchanged_instr _ _) |- _ =>
         rewrite /ssa_var_unchanged_instr /= in H; tac
       | |- context f [zSSA.ssa_var_unchanged_instr _ _] =>
         rewrite /zSSA.ssa_var_unchanged_instr /=; tac
       | H : is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) |- _ =>
         move: (VSLemmas.not_mem_singleton1 H) => {H} H; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) =>
         apply: zSSA.VSLemmas.not_mem_singleton2; tac
       | H : is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) |- _ =>
         let H1 := fresh in let H2 := fresh in
         move: (VSLemmas.not_mem_add1 H) => {H} [H1 H2]; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) =>
         apply: zSSA.VSLemmas.not_mem_add2; split; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | |- is_true true => done
       | H : ?p |- ?p => exact: H
       | H1 : svar_notin ?tmp ?vs,
         H2 : is_true (SSAVS.mem ?v ?vs) |-
         ~ (SSAVS.E.eq ?v (?tmp, ?idx)) =>
         let H := fresh in
         move=> H; move/negP: (H1 idx); apply;
         rewrite -(eqP H); exact: H2
       | |- _ => idtac
       end in
      tac).
Qed.

Lemma bv2z_vars_unchanged_program tmp idx1 idx2 vs p zp :
  svar_notin tmp vs ->
  ssa_vars_unchanged_program vs p ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  zSSA.ssa_vars_unchanged_program vs zp.
Proof.
  elim: p tmp idx1 idx2 vs zp => /=.
  - move=> tmp idx1 idx2 vs zp _ _ [] _ ->.
    exact: zSSA.ssa_unchanged_program_empty.
  - move=> i p IH tmp idx1 idx2 vs zip Hnotin Hun Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    move: (ssa_unchanged_program_cons1 Hun) => {Hun} [Hi Hp].
    apply: zSSA.ssa_unchanged_program_concat2.
    + exact: (bv2z_vars_unchanged_instr Hnotin Hi Hzi).
    + exact: (IH _ _ _ _ _ Hnotin Hp Hzp).
Qed.

Lemma bv2z_instr_idx_lt_unchanged tmp idx1 idx2 idx3 i zi :
  svar_notin tmp (vars_instr i) ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  (idx3 < idx1)%num ->
  zSSA.ssa_var_unchanged_program (tmp, idx3) zi.
Proof.
  case: i => /=; intros; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ =>
         let Hidx := fresh H in case: H => Hidx -> /=; tac
       | |- context f [zSSA.ssa_var_unchanged_instr _ _] =>
         rewrite /zSSA.ssa_var_unchanged_instr /=; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) =>
         apply: zSSA.VSLemmas.not_mem_singleton2; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) =>
         apply: zSSA.VSLemmas.not_mem_add2; split; tac
       | |- ~ (SSAVS.E.eq _ _) => apply/negP; tac
       | |- is_true true => done
       | H : is_true (?tmp != svar ?v) |- is_true ((?tmp, _) != ?v) =>
         apply: svar_ne; exact: H
       | H : (?i1 < ?i2)%num |- is_true ((?tmp, ?i1) != (?tmp, ?i2)) =>
         let Heq := fresh in
         apply: sidx_ne => /=; apply/negP => Heq; rewrite (eqP Heq) in H;
         exact: (N.lt_irrefl _ H)
       | |- _ => idtac
       end in
    tac).
Qed.

Lemma bv2z_instr_idx_ge_unchanged tmp idx1 idx2 idx3 i zi :
  svar_notin tmp (vars_instr i) ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  (idx2 <= idx3)%num ->
  zSSA.ssa_var_unchanged_program (tmp, idx3) zi.
Proof.
  case: i => /=; intros; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ =>
         let Hidx := fresh H in case: H => Hidx -> /=; tac
       | |- context f [zSSA.ssa_var_unchanged_instr _ _] =>
         rewrite /zSSA.ssa_var_unchanged_instr /=; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) =>
         apply: zSSA.VSLemmas.not_mem_singleton2; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.add _ _)) =>
         apply: zSSA.VSLemmas.not_mem_add2; split; tac
       | |- ~ (SSAVS.E.eq _ _) => apply/negP; tac
       | |- is_true true => done
       | H : is_true (?tmp != svar ?v) |- is_true ((?tmp, _) != ?v) =>
         apply: svar_ne; exact: H
       | H1 : (?i3 <= ?i1)%num, H2 : ?i3 = N.succ ?i2
         |- is_true ((?tmp, ?i1) != (?tmp, ?i2)) =>
         let Heq := fresh in let H := fresh in
         apply: sidx_ne => /=; apply/negP => Heq; rewrite (eqP Heq) in H1;
         rewrite H2 in H1;
         move: (N.le_lt_trans _ _ _ H1 (N.lt_succ_diag_r i2)) => H;
         exact: (N.lt_irrefl _ H)
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_idx_lt_unchanged tmp idx1 idx2 idx3 p zp :
  svar_notin tmp (vars_program p) ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  (idx3 < idx1)%num ->
  zSSA.ssa_var_unchanged_program (tmp, idx3) zp.
Proof.
  elim: p tmp idx1 idx2 idx3 zp => /=.
  - move=> tmp idx1 idx2 idx3 zp _ [] _ -> _ /=. done.
  - move=> i p IH tmp idx1 idx2 idx3 zip Hnotin Hzip Hidx31.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx4 [zi [zp [Hzi [Hzp ->]]]]].
    apply: zSSA.ssa_var_unchanged_program_concat2.
    + exact: (bv2z_instr_idx_lt_unchanged (svar_notin_union1 Hnotin) Hzi Hidx31).
    + apply: (IH _ _ _ _ _ (svar_notin_union2 Hnotin) Hzp).
      exact: (N.lt_le_trans _ _ _ Hidx31 (bv2z_instr_idx_inc Hzi)).
Qed.

Lemma bv2z_program_idx_ge_unchanged tmp idx1 idx2 idx3 p zp :
  svar_notin tmp (vars_program p) ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  (idx2 <= idx3)%num ->
  zSSA.ssa_var_unchanged_program (tmp, idx3) zp.
Proof.
  elim: p tmp idx1 idx2 idx3 zp => /=.
  - move=> tmp idx1 idx2 idx3 zp _ [] _ -> _ /=. done.
  - move=> i p IH tmp idx1 idx2 idx3 zip Hnotin Hzip Hidx23.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx4 [zi [zp [Hzi [Hzp ->]]]]].
    apply: zSSA.ssa_var_unchanged_program_concat2.
    + apply: (bv2z_instr_idx_ge_unchanged (svar_notin_union1 Hnotin) Hzi).
      exact: (N.le_trans _ _ _ (bv2z_program_idx_inc Hzp) Hidx23).
    + exact: (IH _ _ _ _ _ (svar_notin_union2 Hnotin) Hzp Hidx23).
Qed.

Lemma bv2z_succ_lvs_unchanged tmp idx1 idx2 idx3 i p zi zp :
  svar_notin tmp (vars_instr i) ->
  svar_notin tmp (vars_program p) ->
  ssa_vars_unchanged_program (lvs_instr i) p ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  (idx3, zp) = bv2z_program tmp idx2 p ->
  zSSA.ssa_vars_unchanged_program (zSSA.lvs_program zi) zp.
Proof.
  move=> Hni Hnp Hun Hzi Hzp. apply: zSSA.ssa_unchanged_program_global => x Hmem.
  case: (bv2z_instr_lvs_case Hzi Hmem) => {Hmem}.
  - move=> Hmem. move: (svar_notin_subset (lvs_instr_subset i) Hni).
    move=> {Hni} Hni. exact: (bv2z_var_unchanged_program Hni Hun Hmem Hzp).
  - destruct x as [x idx] => /=. move=> [<- [Hle Hlt]].
    exact: (bv2z_program_idx_lt_unchanged Hnp Hzp Hlt).
Qed.

Lemma bv2z_instr_single_assignment tmp idx1 idx2 vs i zi :
  svar_notin tmp (vars_instr i) ->
  well_formed_instr vs i ->
  (idx2, zi) = bv2z_instr tmp idx1 i ->
  zSSA.ssa_single_assignment zi.
Proof.
  case: i => /=; intros; hyps_splitb; split_svar_notin_hyp;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ -> /=; tac
       | |- is_true (_ && _) => splitb; tac
       | |- is_true (zSSA.ssa_vars_unchanged_program (SSAVS.add _ _) _) =>
         apply: zSSA.ssa_unchanged_program_add2; rewrite /=; split; tac
       | |- is_true (zSSA.ssa_vars_unchanged_program (SSAVS.singleton _) _) =>
         apply: zSSA.ssa_unchanged_program_singleton2; rewrite /=; tac
       | |- context f [zSSA.ssa_var_unchanged_instr _ _] =>
         rewrite /zSSA.ssa_var_unchanged_instr /=; tac
       | |- is_true (~~ SSAVS.mem _ (SSAVS.singleton _)) =>
         apply: zSSA.VSLemmas.not_mem_singleton2; apply/negP; tac
       | |- is_true true => done
       | |- is_true (zSSA.ssa_vars_unchanged_program _ [::]) =>
         exact: zSSA.ssa_unchanged_program_empty
       | H : is_true (?x != ?y) |- is_true (?y != ?x) =>
         rewrite eq_sym; exact: H
       | H : is_true (?tmp != svar ?v) |- is_true((?tmp, _) != ?v) =>
         apply: svar_ne; exact: H
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_single_assignment tmp idx1 idx2 vs p zp :
  svar_notin tmp (vars_program p) ->
  well_formed_program vs p ->
  ssa_single_assignment p ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  zSSA.ssa_single_assignment zp.
Proof.
  elim: p tmp idx1 idx2 vs zp => /=.
  - move=> tmp idx1 idx2 _ zp _ _ _ [] _ ->; done.
  - move=> i p IH tmp idx1 idx2 vs zip Hnotin /andP [Hwelli Hwellp]
             /andP [Hi Hp] Hzip.
    move: (bv2z_program_cons Hzip) => {Hzip} [idx3 [zi [zp [Hzi [Hzp ->]]]]].
    apply: zSSA.ssa_single_assignment_concat2.
    + exact: (bv2z_instr_single_assignment (svar_notin_union1 Hnotin) Hwelli Hzi).
    + exact: (IH _ _ _ _ _ (svar_notin_union2 Hnotin) Hwellp Hp Hzp).
    + exact: (bv2z_succ_lvs_unchanged (svar_notin_union1 Hnotin)
                                      (svar_notin_union2 Hnotin)
                                      Hi Hzi Hzp).
Qed.

Lemma bv2z_program_well_formed_ssa tmp idx1 idx2 vs p zp :
  svar_notin tmp vs ->
  svar_notin tmp (vars_program p) ->
  well_formed_ssa_program vs p ->
  (idx2, zp) = bv2z_program tmp idx1 p ->
  zSSA.well_formed_ssa_program vs zp.
Proof.
  move=> Hnvs Hnp /andP [/andP [Hwf Hun] Hssa] Hzp.
  apply/andP; split; first (apply/andP; split).
  - exact: (bv2z_program_well_formed Hnp Hwf Hzp).
  - exact: (bv2z_vars_unchanged_program Hnvs Hun Hzp).
  - exact: (bv2z_program_single_assignment Hnp Hwf Hssa Hzp).
Qed.

Lemma bv2z_spec_rng_well_formed vs sp :
  well_formed_spec vs sp ->
  well_formed_spec vs (bv2z_spec_rng sp).
Proof.
  destruct sp as [f p g]. move=> /andP /= [/andP [Hf Hp] Hg].
  rewrite /well_formed_spec /=. rewrite /vars_bexp /=.
  rewrite 2!VSLemmas.union_emptyl Hp.
  rewrite (VSLemmas.subset_trans (vars_rbexp_subset f) Hf).
  rewrite (VSLemmas.subset_trans (vars_rbexp_subset g) Hg).
  done.
Qed.

Lemma bv2z_spec_eqn_well_formed vs sp :
  well_formed_spec vs sp ->
  zSSA.well_formed_spec vs (bv2z_spec_eqn vs sp).
Proof.
  destruct sp as [f p g]. move=> /andP /= [/andP [Hf Hp] Hg].
  rewrite /bv2z_spec_eqn. set tmp := new_svar_spec_eqn vs ({{f}} p {{g}})%bvssa.
  set idx1 := initial_tmp_sidx.
  sethave temp (bv2z_program tmp idx1 (sprog ({{f}} p {{g}})%bvssa)).
  destruct temp as [idx2 zp]. move=> Hzp /=.
  apply/andP => /=; split; first (apply/andP; split).
  - apply: (@zSSA.VSLemmas.subset_trans _ (vars_bexp f)).
    + apply: bv2z_ebexp_vars_subset.
    + assumption.
  - exact: (bv2z_program_well_formed (svar_notin_sprog vs ({{f}} p {{g}})%bvssa)
                                     Hp Hzp).
  - apply: (zSSA.VSLemmas.subset_trans (bv2z_ebexp_vars_subset g)).
    apply: (@zSSA.VSLemmas.subset_trans _ (SSAVS.union vs (vars_program p))).
    + exact: Hg.
    + move: (bv2z_program_vars_subset Hzp) => /= Hsubset.
      zSSA.VSLemmas.dp_subset.
Qed.

Theorem bv2z_spec_eqn_well_formed_ssa vs sp :
  well_formed_ssa_spec vs sp ->
  zSSA.well_formed_ssa_spec vs (bv2z_spec_eqn vs sp).
Proof.
  destruct sp as [f p g]. move=> /andP /= [/andP [Hwf Hun] Hssa].
  move: (bv2z_spec_eqn_well_formed Hwf).
  rewrite /bv2z_spec_eqn. set tmp := new_svar_spec_eqn vs ({{f}} p {{g}})%bvssa.
  set idx1 := initial_tmp_sidx.
  sethave temp (bv2z_program tmp idx1 (sprog ({{f}} p {{g}})%bvssa)).
  destruct temp as [idx2 zp]. move=> Hzp /= Hzwf.
  apply/andP => /=; split; first (apply/andP; split).
  - exact: Hzwf.
  - apply: (bv2z_vars_unchanged_program _ Hun Hzp).
    exact: (svar_notin_inputs vs).
  - move: Hwf => /andP [/andP [_ Hwfp] _].
    apply: (bv2z_program_single_assignment _ Hwfp Hssa Hzp).
    exact: (svar_notin_sprog vs).
Qed.



(** Soundness *)

(* vs: inputs *)
Theorem bv2z_spec_sound vs sp :
  bv2z_spec_safe sp ->
  valid_rspec (bv2z_spec_rng sp) ->
  zSSA.valid_spec (bv2z_spec_eqn vs sp) ->
  valid_spec sp.
Proof.
  destruct sp as [f p g] => /=. rewrite /bv2z_spec_eqn /=.
  sethave tmp (new_svar_spec_eqn vs ({{f}} p {{g}})%bvssa).
  set idx1 := initial_tmp_sidx.
  sethave temp (bv2z_program tmp idx1 (sprog ({{f}} p {{g}})%bvssa)).
  destruct temp as [idx2 zp]. move=> Hzp Htmp Hsafe Hrng Heqn bs1 bs2 /= Hbf Hbp.
  move: (Hrng bs1 bs2 (eval_bexp_rng Hbf) Hbp) => {Hrng} /= Hrng.
  set zs1 := bv2z_state bs1. set zs2 := zSSA.eval_program zs1 zp.
  move: (@bvz_eq_eqm tmp _ _ (bv2z_state_eq bs1)) => Heqm.
  move: (svar_notin_spre vs ({{f}}p{{g}})%bvssa); rewrite -Htmp => Hnf.
  move: (svar_notin_sprog vs ({{f}}p{{g}})%bvssa); rewrite -Htmp => Hnp.
  move: (svar_notin_spost vs ({{f}}p{{g}})%bvssa); rewrite -Htmp => Hng.
  move: (bvz_eqm_eval_ebexp1 Heqm (svar_notin_union1 Hnf)
                             (eval_bexp_eqn Hbf)) => Heqnf.
  move: (Heqn zs1 zs2 Heqnf (Logic.eq_refl zs2)) => {Heqn} /= Heqn.
  apply: (eval_bexp_combine_eqm _ Hng Hrng Heqn). rewrite -Hbp.
  exact: (bvz_eqm_eval_program Heqm Hnp (Hsafe _ (eval_bexp_rng Hbf)) Hzp).
Qed.
