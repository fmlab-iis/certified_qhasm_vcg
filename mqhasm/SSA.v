
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From Common Require Import Types Nats ZAriths Var Store.
From mQhasm Require Import mQhasm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Delimit Scope ssa_scope with ssa.

Local Open Scope ssa_scope.

Module MakeSSA (VO : SsrOrderedType) (IO : SsrOrderedType).
  Module V := MakeSsrPairOrderedType VO IO.
  Module Q := MakeQhasm V.
  Include Q.
End MakeSSA.

Module SSA := MakeSSA VarOrder NatOrder.

Notation "s |= f" := (SSA.eval_bexp f true s) (at level 74, no associativity) : ssa_scope.
Notation "f ===> g" := (SSA.entails f g) (at level 82, no associativity) : ssa_scope.
Notation "{{ f }} p {{ g }}" := (SSA.valid_spec (f, p, g)) (at level 82) : ssa_scope.



(** Conversion to SSA *)

Definition index : Type := nat.

(* A map from a Qhasm variable to its current index. *)
Definition vmap : Type := VM.t index.

Definition empty_vmap : vmap := VM.empty index.

Definition initial_index : index := 0.

Definition first_assigned_index : index := 1.

(* Find the current index of a Qhasm variable. *)
Definition get_index (m : vmap) (v : var) : index :=
  match VM.find v m with
  | None => initial_index
  | Some i => i
  end.

(* Increment the current index of a Qhasm variable. *)
Definition upd_index (m : vmap) (v : var) : vmap * index :=
  match VM.find v m with
  | None => (VM.add v first_assigned_index m, first_assigned_index)
  | Some i => (VM.add v (i + 1) m, i + 1)
  end.

Definition ssa_unop (op : unop) : SSA.unop :=
  match op with
  | QNeg => SSA.QNeg
  end.

Definition ssa_binop (op : binop) : SSA.binop :=
  match op with
  | QAdd => SSA.QAdd
  | QSub => SSA.QSub
  | QMul => SSA.QMul
  end.

Fixpoint ssa_exp (m : vmap) (e : exp) : SSA.exp :=
  match e with
  | QVar v => SSA.QVar (v, get_index m v)
  | QConst c => SSA.QConst c
  | QUnop op e => SSA.QUnop (ssa_unop op) (ssa_exp m e)
  | QBinop op e1 e2 => SSA.QBinop (ssa_binop op) (ssa_exp m e1) (ssa_exp m e2)
  end.

Definition ssa_instr (m : vmap) (i : instr) : vmap * SSA.instr :=
  match i with
  | QAssign v e =>
    let e := ssa_exp m e in
    let (m, i) := upd_index m v in
    (m, SSA.QAssign (v, i) e)
  | QSplit vh vl e p =>
    let e := ssa_exp m e in
    let (m, i) := upd_index m vh in
    let (m, j) := upd_index m vl in
    (m, SSA.QSplit (vh, i) (vl, j) e p)
  end.

Fixpoint ssa_program (m : vmap) (p : program) : (vmap * SSA.program) :=
  match p with
  | [::] => (m, [::])
  | hd::tl =>
    let (m, hd) := ssa_instr m hd in
    let (m, tl) := ssa_program m tl in
    (m, hd::tl)
  end.

Fixpoint ssa_bexp (m : vmap) (e : bexp) : SSA.bexp :=
  match e with
  | QTrue => SSA.QTrue
  | QEq e1 e2 => SSA.QEq (ssa_exp m e1) (ssa_exp m e2)
  | QCong e1 e2 p => SSA.QCong (ssa_exp m e1) (ssa_exp m e2) p
  | QAnd e1 e2 => SSA.QAnd (ssa_bexp m e1) (ssa_bexp m e2)
  end.

Definition ssa_spec (s : spec) : SSA.spec :=
  let m := empty_vmap in
  let f := ssa_bexp m (spre s) in
  let (m, p) := ssa_program m (sprog s) in
  let g := ssa_bexp m (spost s) in
  (f, p, g).

Lemma upd_index_gt0 :
  forall (m : vmap) (v : var),
    snd (upd_index m v) > 0.
Proof.
  move=> m v; rewrite /upd_index.
  case: (VM.find v m) => /=.
  - move=> a.
    rewrite addn1.
    exact: ltn0Sn.
  - done.
Qed.

Lemma get_upd_index_eq :
  forall (m1 m2 : vmap) (v : var) (i : index),
    (m2, i) = upd_index m1 v ->
    get_index m2 v = i.
Proof.
  move=> m1 m2 v i.
  rewrite /upd_index /get_index.
  set b := (VM.find v m1).
  case: b.
  - move=> a [] Hm Hi.
    rewrite Hm.
    rewrite VM.Lemmas.find_add_eq.
    + by rewrite Hi.
    + exact: eqxx.
  - move=> [] Hm Hi.
    rewrite Hm.
    rewrite VM.Lemmas.find_add_eq.
    + by rewrite Hi.
    + exact: eqxx.
Qed.

Lemma get_upd_index_neq :
  forall (m1 m2 : vmap) (v : var) (i : index) (x : var),
    x != v ->
    (m2, i) = upd_index m1 v ->
    get_index m2 x = get_index m1 x.
Proof.
  move=> m1 m2 v i x.
  rewrite /upd_index /get_index.
  set b := (VM.find v m1).
  case: b.
  - move=> a Hxv [] Hm Hi.
    rewrite Hm.
    rewrite (VM.Lemmas.find_add_neq _ _ (negP Hxv)).
    reflexivity.
  - move=> Hxv [] Hm Hi.
    rewrite Hm.
    rewrite (VM.Lemmas.find_add_neq _ _ (negP Hxv)).
    reflexivity.
Qed.

Lemma ssa_program_empty : forall m, ssa_program m [::] = (m, [::]).
Proof.
  reflexivity.
Qed.

Lemma ssa_program_cons :
  forall m1 m2 hd tl p,
    ssa_program m1 (hd::tl) = (m2, p) ->
    exists m3 h t,
      ssa_instr m1 hd = (m3, h) /\ ssa_program m3 tl = (m2, t) /\ p = h::t.
Proof.
  move=> m1 m2 hd tl p /=.
  set tmp := ssa_instr m1 hd.
  have: (tmp = ssa_instr m1 hd) by reflexivity.
  destruct tmp as [m3 h].
  set tmp := ssa_program m3 tl.
  have: (tmp = ssa_program m3 tl) by reflexivity.
  destruct tmp as [m4 t].
  move=> Htl Hhd [] Hm Hp.
  exists m3; exists h; exists t; split; [idtac | split].
  - reflexivity.
  - rewrite -Htl Hm.
    reflexivity.
  - symmetry; exact: Hp.
Qed.

Lemma ssa_eval_unop :
  forall (op : unop) (v : value),
    SSA.eval_unop (ssa_unop op) v = eval_unop op v.
Proof.
  by case.
Qed.

Lemma ssa_eval_binop :
  forall (op : binop) (v1 v2 : value),
    SSA.eval_binop (ssa_binop op) v1 v2 = eval_binop op v1 v2.
Proof.
  by case.
Qed.



(** State equivalence *)

Definition state_equiv (m : vmap) (s : State.t) (ss : SSA.State.t) : Prop :=
  forall x, State.acc x s = SSA.State.acc (x, get_index m x) ss.

Lemma pair_neq1 :
  forall (T : eqType) (a b c d : T),
    a != c -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hac; exact: eqxx.
Qed.

Lemma pair_neq2 :
  forall (T : eqType) (a b c d : T),
    b != d -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hbd; exact: eqxx.
Qed.

Lemma ssa_eval_exp m s ss e n :
  state_equiv m s ss ->
  eval_exp e n s ->
  SSA.eval_exp (ssa_exp m e) n ss.
Proof.
  move=> Heq; elim: e n => /=.
  - move=> v n He.
    inversion_clear He.
    apply: SSA.EQVar.
    rewrite -Heq.
    exact: H.
  - move=> c n He.
    inversion_clear He.
    exact: SSA.EQConst.
  - move=> op e IH n He.
    inversion_clear He.
    apply: SSA.EQUnop.
    + exact: (IH _ H).
    + rewrite ssa_eval_unop.
      exact: H0.
  - move=> op e1 IH1 e2 IH2 n He.
    inversion_clear He.
    apply: SSA.EQBinop.
    + exact: (IH1 _ H).
    + exact: (IH2 _ H0).
    + rewrite ssa_eval_binop.
      exact: H1.
Qed.

Lemma ssa_eval_exp_eq m s ss e n sn :
  state_equiv m s ss ->
  eval_exp e n s ->
  SSA.eval_exp (ssa_exp m e) sn ss ->
  n = sn.
Proof.
  move=> Heq He Hes.
  move: (ssa_eval_exp Heq He) => Hes'.
  move: (SSA.eval_exp_unique Hes Hes') => H.
  symmetry; exact: (eqP H).
Qed.

Lemma ssa_eval_bexp m s ss e b :
  state_equiv m s ss ->
  eval_bexp e b s ->
  SSA.eval_bexp (ssa_bexp m e) b ss.
Proof.
  move=> Heq; elim: e b => /=.
  - move=> b He.
    inversion_clear He.
    exact: SSA.EQTrue.
  - move=> e1 e2 b He.
    inversion_clear He.
    exact: (SSA.EQEq (ssa_eval_exp Heq H) (ssa_eval_exp Heq H0)).
  - move=> e1 e2 p b He.
    inversion_clear He.
    exact: (SSA.EQCong _ (ssa_eval_exp Heq H) (ssa_eval_exp Heq H0)).
  - move=> e1 IH1 e2 IH2 b He.
    inversion_clear He.
    exact: (SSA.EQAnd (IH1 _ H) (IH2 _ H0)).
Qed.

Lemma ssa_eval_bexp_eq m s ss e b sb :
  state_equiv m s ss ->
  eval_bexp e b s ->
  SSA.eval_bexp (ssa_bexp m e) sb ss ->
  b = sb.
Proof.
  move=> Heq He Hes.
  move: (ssa_eval_bexp Heq He) => Hes'.
  move: (SSA.eval_bexp_unique Hes Hes') => H.
  symmetry; exact: (eqP H).
Qed.

Lemma ssa_eval_instr :
  forall m1 m2 s1 s2 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i s2 ->
    SSA.eval_instr ss1 si ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 i.
  elim: i => /=.
  - move=> v e si.
    set tmp := upd_index m1 v.
    have: (tmp = upd_index m1 v) by done.
    destruct tmp as [m' idx].
    move=> Hupd [] Hm Hsi Heq1 Hei Hesi x.
    rewrite Hm in Hupd => {m' Hm}.
    rewrite -Hsi in Hesi.
    inversion_clear Hei.
    inversion_clear Hesi.
    case Hxv: (x == v).
    + rewrite (State.acc_Upd_eq Hxv H0).
      rewrite (SSA.State.acc_Upd_eq _ H2).
      * move: (ssa_eval_exp Heq1 H) => H3.
        move: (SSA.eval_exp_unique H1 H3).
        by move/eqP=> Hn; rewrite Hn.
      * rewrite (eqP Hxv) (get_upd_index_eq Hupd).
        exact: eqxx.
    + move/idP/negP: Hxv => Hxv.
      rewrite (get_upd_index_neq Hxv Hupd).
      rewrite (State.acc_Upd_neq Hxv H0).
      rewrite (SSA.State.acc_Upd_neq _ H2).
      * exact: (Heq1 x).
      * exact: (pair_neq1 _ _ Hxv).
  - move=> vh vl e p si.
    set tmp := upd_index m1 vh.
    have: (tmp = upd_index m1 vh) by done.
    destruct tmp as [mh idh].
    set tmp := upd_index mh vl.
    have: (tmp = upd_index mh vl) by done.
    destruct tmp as [ml idl].
    move=> Hupdl Hupdh [] Hml Hsi Heq Hei Hesi.
    rewrite Hml in Hupdl => {ml Hml}.
    inversion_clear Hei.
    rewrite -Hsi in Hesi; inversion_clear Hesi => {Hsi}.
    move: (ssa_eval_exp_eq Heq H H3) => {H H3} Hnn4. (* n = n4 *)
    rewrite Hnn4 in H1 H2.
    rewrite -H1 in H5; rewrite -H2 in H6 => {H1 H2}. (* n0 = n1, n3 = n2 *)
    move=> x.
    rewrite H0 H4.
    case Hxl: (x == vl); [idtac | case Hxh: (x == vh)].
    + rewrite (State.acc_upd_eq _ _ Hxl).
      rewrite (eqP Hxl) (get_upd_index_eq Hupdl).
      rewrite (SSA.State.acc_upd_eq _ _ (eqxx (vl, idl))).
      by rewrite H6.
    + move/idP/negP: Hxl => Hxl.
      rewrite (State.acc_upd_neq _ _ Hxl).
      rewrite (State.acc_upd_eq _ _ Hxh).
      rewrite (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl)).
      move: (get_upd_index_eq Hupdh) => Hidx.
      move: (get_upd_index_neq Hxl Hupdl) => Hidx'.
      rewrite -Hidx Hidx' (eqP Hxh).
      rewrite (SSA.State.acc_upd_eq _ _ (eqxx (vh, get_index mh vh))).
      by rewrite H5.
    + move/idP/negP: Hxl => Hxl.
      move/idP/negP: Hxh => Hxh.
      rewrite (State.acc_upd_neq _ _ Hxl) (State.acc_upd_neq _ _ Hxh).
      rewrite (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl))
              (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxh)).
      move: (get_upd_index_neq Hxh Hupdh) => Hidx.
      move: (get_upd_index_neq Hxl Hupdl) => Hidx'.
      rewrite Hidx' Hidx.
      exact: Heq.
Qed.

Lemma ssa_eval_instr_succ :
  forall m1 m2 s1 s2 ss1 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i s2 ->
    exists ss2,
      SSA.eval_instr ss1 si ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 i si Hi Heq Hei.
  have: (exists ss2, SSA.eval_instr ss1 si ss2).
  - elim: i si Hi Heq Hei => /=.
    + move=> v e si.
      set tmp := upd_index m1 v.
      have: (tmp = upd_index m1 v) by done.
      destruct tmp as [m' idx].
      move=> Hupd [] Hm Hsi Heq Hei.
      inversion_clear Hei.
      pose ss2 := SSA.State.upd (v, idx) n ss1.
      exists ss2.
      * rewrite -Hsi; apply: (SSA.EQAssign (n:=n)).
        -- exact: (ssa_eval_exp Heq H).
        -- exact: SSA.State.Upd_upd.
    + move=> vh vl e p si.
      set tmp := upd_index m1 vh.
      have: (tmp = upd_index m1 vh) by done.
      destruct tmp as [mh idh].
      set tmp := upd_index mh vl.
      have: (tmp = upd_index mh vl) by done.
      destruct tmp as [ml idl].
      move=> Hupdl Hupdh [] Hml Hsi Heq Hei.
      inversion_clear Hei.
      pose ss2 := SSA.State.upd (vl, idl) n2 (SSA.State.upd (vh, idh) n1 ss1).
      exists ss2.
      * rewrite -Hsi; apply: (SSA.EQSplit (n1:=n1) (n2:=n2)).
        -- exact: (ssa_eval_exp Heq H).
        -- move=> x.
           reflexivity.
        -- assumption.
        -- assumption.
  - move=> [ss2 Hesi].
    exists ss2; split; [exact: Hesi | idtac].
    exact: (ssa_eval_instr Hi Heq Hei Hesi).
Qed.

Lemma ssa_eval_program :
  forall m1 m2 s1 s2 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p s2 ->
    SSA.eval_program ss1 sp ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 p.
  elim: p m1 m2 s1 s2 ss1 ss2.
  - move=> m1 m2 s1 s2 ss1 ss2 p Hsp Heq Hep Hesp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm Hp.
    rewrite -Hp in Hesp.
    move: (eval_program_empty Hep) => Hs.
    move: (SSA.eval_program_empty Hesp) => Hss.
    rewrite -Hs -Hss -Hm; exact: Heq.
  - move=> hd tl IH m1 m2 s1 s2 ss1 ss2 sp Hsp Heq Hep Hesp.
    inversion_clear Hep.
    move: (ssa_program_cons Hsp) => [m3 [h [t [Hh [Ht Hht]]]]].
    rewrite Hht in Hesp.
    inversion_clear Hesp.
    move: (ssa_eval_instr Hh Heq H H1) => Heq'.
    exact: (IH _ _ _ _ _ _ _ Ht Heq' H0 H2).
Qed.

Lemma ssa_eval_program_succ :
  forall m1 m2 s1 s2 ss1 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p s2 ->
    exists ss2,
      SSA.eval_program ss1 sp ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 p sp Hp Heq Hep.
  have: (exists ss2, SSA.eval_program ss1 sp ss2).
  - elim: p m1 m2 s1 s2 ss1 sp Hp Heq Hep.
    + move=> m1 m2 s1 s2 ss1 sp Hsp Heq Hep.
      rewrite ssa_program_empty in Hsp.
      case: Hsp => Hm Hsp.
      exists ss1.
      rewrite -Hsp; exact: SSA.EQEmpty.
    + move=> hd tl IH m1 m2 s1 s2 ss1 sp Hsp Heq Hep.
      inversion_clear Hep.
      move: (ssa_program_cons Hsp) => [m3 [h [t [Hh [Ht Hht]]]]].
      move: (ssa_eval_instr_succ Hh Heq H) => [ss3 [Heh Heqh]].
      move: (IH m3 m2 _ _ _ t Ht Heqh H0) => [ss2 Het].
      exists ss2.
      rewrite Hht; exact: (SSA.EQCons Heh Het).
  - move=> [ss2 Hesp].
    exists ss2; split; [exact: Hesp | idtac].
    exact: (ssa_eval_program Hp Heq Hep Hesp).
Qed.

Lemma dessa_eval_exp m s ss e n :
  state_equiv m s ss ->
  SSA.eval_exp (ssa_exp m e) n ss ->
  eval_exp e n s.
Proof.
  move=> Heq; elim: e n => /=.
  - move=> v n He.
    inversion_clear He.
    apply: EQVar.
    rewrite Heq.
    exact: H.
  - move=> c n He.
    inversion_clear He.
    exact: EQConst.
  - move=> op e IH n He.
    inversion_clear He.
    apply: EQUnop.
    + exact: (IH _ H).
    + rewrite -ssa_eval_unop.
      exact: H0.
  - move=> op e1 IH1 e2 IH2 n He.
    inversion_clear He.
    apply: EQBinop.
    + exact: (IH1 _ H).
    + exact: (IH2 _ H0).
    + rewrite -ssa_eval_binop.
      exact: H1.
Qed.

Lemma dessa_eval_bexp m s ss e b :
  state_equiv m s ss ->
  SSA.eval_bexp (ssa_bexp m e) b ss ->
  eval_bexp e b s.
Proof.
  move=> Heq; elim: e b => /=.
  - move=> b He.
    inversion_clear He.
    exact: EQTrue.
  - move=> e1 e2 b He.
    inversion_clear He.
    exact: (EQEq (dessa_eval_exp Heq H) (dessa_eval_exp Heq H0)).
  - move=> e1 e2 p b He.
    inversion_clear He.
    exact: (EQCong _ (dessa_eval_exp Heq H) (dessa_eval_exp Heq H0)).
  - move=> e1 IH1 e2 IH2 b He.
    inversion_clear He.
    exact: (EQAnd (IH1 _ H) (IH2 _ H0)).
Qed.

Lemma dessa_eval_instr_succ :
  forall m1 m2 s1 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    SSA.eval_instr ss1 si ss2 ->
    exists s2,
      eval_instr s1 i s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 i si Hi Heq Hesi.
  have: (exists s2, eval_instr s1 i s2).
  - elim: i si Hi Heq Hesi => /=.
    + move=> v e si.
      set tmp := upd_index m1 v.
      have: (tmp = upd_index m1 v) by done.
      destruct tmp as [m' idx].
      move=> Hupd [] Hm Hsi Heq Hesi.
      rewrite -Hsi in Hesi.
      inversion_clear Hesi.
      pose s2 := State.upd v n s1.
      exists s2.
      * apply: (EQAssign (n:=n)).
        -- exact: (dessa_eval_exp Heq H).
        -- exact: State.Upd_upd.
    + move=> vh vl e p si.
      set tmp := upd_index m1 vh.
      have: (tmp = upd_index m1 vh) by done.
      destruct tmp as [mh idh].
      set tmp := upd_index mh vl.
      have: (tmp = upd_index mh vl) by done.
      destruct tmp as [ml idl].
      move=> Hupdl Hupdh [] Hml Hsi Heq Hesi.
      rewrite -Hsi in Hesi.
      inversion_clear Hesi.
      pose s2 := State.upd vl n2 (State.upd vh n1 s1).
      exists s2.
      * apply: (EQSplit (n1:=n1) (n2:=n2)).
        -- exact: (dessa_eval_exp Heq H).
        -- move=> x.
           reflexivity.
        -- assumption.
        -- assumption.
  - move=> [s2 Hei].
    exists s2; split; [exact: Hei | idtac].
    exact: (ssa_eval_instr Hi Heq Hei Hesi).
Qed.

Lemma dessa_eval_program_succ :
  forall m1 m2 s1 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    SSA.eval_program ss1 sp ss2 ->
    exists s2,
      eval_program s1 p s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 p sp Hp Heq Hesp.
  have: (exists s2, eval_program s1 p s2).
  - elim: p m1 m2 s1 ss1 ss2 sp Hp Heq Hesp.
    + move=> m1 m2 s1 ss1 ss2 sp Hsp Heq Hep.
      rewrite ssa_program_empty in Hsp.
      case: Hsp => Hm Hsp.
      exists s1.
      exact: EQEmpty.
    + move=> hd tl IH m1 m2 s1 ss1 ss2 sp Hsp Heq Hesp.
      move: (ssa_program_cons Hsp) => [m3 [h [t [Hh [Ht Hht]]]]].
      rewrite Hht in Hesp.
      inversion_clear Hesp.
      move: (dessa_eval_instr_succ Hh Heq H) => [s3 [Heh Heqh]].
      move: (IH m3 m2 _ _ _ t Ht Heqh H0) => [s4 Het].
      exists s4.
      exact: (EQCons Heh Het).
  - move=> [s2 Hep].
    exists s2; split; [exact: Hep | idtac].
    exact: (ssa_eval_program Hp Heq Hep Hesp).
Qed.



(** Convert a Qhasm state to an SSA state. *)

Definition ssa_state (m : vmap) (s : State.t) : SSA.State.t :=
  Store.M.fold (fun x v t => SSA.State.upd (x, get_index m x) v t)
               s
               SSA.State.empty.

Lemma ssa_state_empty :
  forall m, ssa_state m State.empty = SSA.State.empty.
Proof.
  reflexivity.
Qed.

Lemma ssa_state_Empty :
  forall m s, State.Empty s -> SSA.State.Empty (ssa_state m s).
Proof.
  move=> m s Hemp.
  rewrite /ssa_state.
  rewrite (Store.L.P.fold_Empty RelationClasses.eq_equivalence _ _ Hemp).
  exact: SSA.Store.M.empty_1.
Qed.

Lemma acc_ssa_state_eq :
  forall (m : vmap) (s : State.t) (v : var) (i : index),
    i == get_index m v ->
    SSA.State.acc (v, i) (ssa_state m s) = State.acc v s.
Proof.
  move=> m s v i Heq.
  rewrite /ssa_state.
  eapply Store.L.P.fold_rec.
  - move=> {s} s Hemp.
    rewrite (State.Empty_acc _ Hemp).
    exact: SSA.State.acc_empty.
  - move=> x vx ss s1 s2 Hmapsto Hin Hadd Hacc => {Hmapsto s}.
    case Hvx: (v == x).
    + move/eqP: Hvx => Hvx.
      rewrite (SSA.State.acc_upd_eq); rewrite Hvx;
      [idtac | by rewrite (eqP Heq) Hvx].
      rewrite /State.acc /Store.acc (Hadd x).
      rewrite Store.L.find_add_eq; [reflexivity | exact: eqxx].
    + move/eqP/eqP: Hvx => Hvx.
      rewrite (SSA.State.acc_upd_neq).
      * rewrite Hacc.
        rewrite /State.acc /Store.acc (Hadd v).
        rewrite Store.L.find_add_neq; first by reflexivity.
        apply/negP.
        exact: Hvx.
      * apply/negP => H.
        move/eqP: H => [] => H _.
        rewrite H in Hvx.
        apply: (negP Hvx).
        exact: eqxx.
Qed.

Lemma acc_ssa_state_neq :
  forall (m : vmap) (s : State.t) (v : var) (i : index),
    i != get_index m v ->
    SSA.State.acc (v, i) (ssa_state m s) = None.
Proof.
  move=> m s v i Hne.
  rewrite /ssa_state.
  eapply Store.L.P.fold_rec.
  - move=> {s} s Hemp.
    exact: SSA.State.acc_empty.
  - move=> x vx ss s1 s2 Hmapsto Hin Hadd Hacc.
    case H: ((v, i) == (x, get_index m x)).
    + move/eqP: H; case => Heq1 Heq2.
      rewrite Heq1 Heq2 in Hne.
      apply: False_ind; apply: (negP Hne).
      exact: eqxx.
    + move/idP/negP: H => H.
      rewrite (SSA.State.acc_upd_neq _ _ H).
      exact: Hacc.
Qed.

Lemma ssa_state_equiv :
  forall m s, state_equiv m s (ssa_state m s).
Proof.
  move=> m s x.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index m x))).
  reflexivity.
Qed.



(** Convert an SSA state to a Qhasm state. *)

Definition dessa_state (m : vmap) (s : SSA.State.t) : State.t :=
  SSA.Store.M.fold (fun x v t =>
                      if snd x == get_index m (fst x) then State.upd (fst x) v t
                      else t)
                   s
                   State.empty.

Lemma acc_dessa_empty :
  forall (m : vmap),
    dessa_state m SSA.State.empty = State.empty.
Proof.
  reflexivity.
Qed.

Lemma dessa_state_Empty :
  forall (m : vmap) (s : SSA.State.t),
    SSA.State.Empty s -> State.Empty (dessa_state m s).
Proof.
  move=> m s Hemp.
  rewrite /dessa_state.
  rewrite (SSA.Store.L.P.fold_Empty RelationClasses.eq_equivalence _ _ Hemp).
  exact: Store.M.empty_1.
Qed.

Lemma acc_dessa_state :
  forall (m : vmap) (s : SSA.State.t) (v : var),
    State.acc v (dessa_state m s) = SSA.State.acc (v, get_index m v) s.
Proof.
  move=> m s v.
  rewrite /dessa_state.
  eapply SSA.Store.L.P.fold_rec.
  - move=> {s} s Hemp.
    rewrite (SSA.State.Empty_acc _ Hemp).
    exact: State.acc_empty.
  - move=> x vx ss s1 s2 Hmapsto Hin Hadd Hacc => {Hmapsto s}.
    destruct x as [x ix] => /=.
    case Hix: (ix == get_index m x).
    + case Hvx: (v == x).
      * rewrite (eqP Hvx) (State.acc_upd_eq _ _ (eqxx x)).
        rewrite -(eqP Hix).
        rewrite /SSA.State.acc /SSA.Store.acc (Hadd (x, ix)).
        rewrite (SSA.Store.L.find_add_eq _ _ (eqxx (x, ix))).
        reflexivity.
      * move/negP/idP: Hvx => Hvx.
        rewrite (State.acc_upd_neq _ _ Hvx).
        rewrite /SSA.State.acc /SSA.Store.acc (Hadd (v, get_index m v)).
        rewrite SSA.Store.L.find_add_neq.
        -- exact: Hacc.
        -- move/eqP=> [] H _.
           apply/idP/eqP: Hvx.
           exact: H.
    + case Hvx: (v == x).
      * rewrite Hacc (eqP Hvx).
        rewrite /SSA.State.acc /SSA.Store.acc (Hadd (x, get_index m x)).
        rewrite SSA.Store.L.find_add_neq.
        -- reflexivity.
        -- move/eqP=> [] H.
           move/eqP: Hix.
           apply; by rewrite H.
      * rewrite Hacc /SSA.State.acc /SSA.Store.acc (Hadd (v, get_index m v)).
        rewrite SSA.Store.L.find_add_neq.
        -- reflexivity.
        -- move/eqP=> [] H _.
           apply/negPf: Hvx.
           rewrite H; exact: eqxx.
Qed.

Lemma ssa_dessaK :
  forall (m : vmap) (s : State.t) (x : var),
    State.acc x (dessa_state m (ssa_state m s)) = State.acc x s.
Proof.
  move=> m s x.
  rewrite acc_dessa_state.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index m x))).
  reflexivity.
Qed.

Lemma dessa_state_equiv :
  forall m s, state_equiv m (dessa_state m s) s.
Proof.
  move=> m s x.
  exact: acc_dessa_state.
Qed.



(** Soundness and completeness *)

Lemma ssa_spec_sound (s : spec) :
  SSA.valid_spec (ssa_spec s) -> valid_spec s.
Proof.
  destruct s as ((f, p), g).
  rewrite /ssa_spec /spre /spost /sprog /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec s1 s2.
  rewrite /spre /sprog /spost /= => Hf Hep.
  pose ss1 := ssa_state empty_vmap s1.
  pose Heq1 := (ssa_state_equiv empty_vmap s1).
  move: (ssa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hep) => [ss2 [Hesp Heq2]].
  move: (ssa_eval_bexp Heq1 Hf) => Hsf.
  move: (Hspec ss1 ss2 Hsf Hesp) => /= Hsg.
  exact: (dessa_eval_bexp Heq2 Hsg).
Qed.

Lemma ssa_spec_complete (s : spec) :
  valid_spec s -> SSA.valid_spec (ssa_spec s).
Proof.
  destruct s as ((f, p), g).
  rewrite /ssa_spec /spre /spost /sprog /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec ss1 ss2.
  rewrite /SSA.spre /SSA.sprog /SSA.spost /= => Hsf Hesp.
  pose s1 := dessa_state empty_vmap ss1.
  pose Heq1 := (dessa_state_equiv empty_vmap ss1).
  move: (dessa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hesp) => [s2 [Hep Heq2]].
  move: (dessa_eval_bexp Heq1 Hsf) => Hf.
  move: (Hspec s1 s2 Hf Hep) => /= Hg.
  exact: (ssa_eval_bexp Heq2 Hg).
Qed.
