
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
  | QPow e n => SSA.QPow (ssa_exp m e) n
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

Lemma ssa_qassign :
  forall m1 m2 v e si,
    ssa_instr m1 (QAssign v e) = (m2, si) ->
    exists i,
      (m2, i) = upd_index m1 v /\ si = SSA.QAssign (v, i) (ssa_exp m1 e).
Proof.
  move=> m1 m2 v e si /=.
  set tmp := upd_index m1 v.
  have: (tmp = upd_index m1 v) by reflexivity.
  destruct tmp as [m2' iv].
  move=> Hupd [Hm2' Hsi].
  exists iv; split.
  - rewrite Hm2'; reflexivity.
  - symmetry; assumption.
Qed.

Lemma ssa_qsplit :
  forall m1 m2 vh vl e p si,
    ssa_instr m1 (QSplit vh vl e p) = (m2, si) ->
    exists ih il m3,
      (m3, ih) = upd_index m1 vh /\
      (m2, il) = upd_index m3 vl /\
      si = SSA.QSplit (vh, ih) (vl, il) (ssa_exp m1 e) p.
Proof.
  move=> m1 m2 vh vl e p si /=.
  set tmp := upd_index m1 vh.
  have: (tmp = upd_index m1 vh) by reflexivity.
  destruct tmp as [m3 ih].
  set tmp := upd_index m3 vl.
  have: (tmp = upd_index m3 vl) by reflexivity.
  destruct tmp as [m2' il].
  move=> Hupdl Hupdh [Hm2' Hsi].
  exists ih; exists il; exists m3; split; [idtac | split].
  - reflexivity.
  - rewrite -Hm2'; assumption.
  - symmetry; assumption.
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

Lemma ssa_spec_unfold s :
  exists m, SSA.spre (ssa_spec s) = ssa_bexp empty_vmap (spre s) /\
            (m, SSA.sprog (ssa_spec s)) = ssa_program empty_vmap (sprog s) /\
            SSA.spost (ssa_spec s) = ssa_bexp m (spost s).
Proof.
  destruct s as [[f p] g].
  rewrite /ssa_spec /spre /sprog /spost /=.
  set tmp := ssa_program empty_vmap p.
  destruct tmp as [m sp].
  rewrite /SSA.spre /SSA.sprog /SSA.spost /=.
  exists m; split; [idtac | split]; reflexivity.
Qed.

Lemma upd_index_gt0 :
  forall (m1 m2 : vmap) (v : var) (i : index),
    (m2, i) = upd_index m1 v -> i > 0.
Proof.
  move=> m1 m2 v i; rewrite /upd_index.
  case: (VM.find v m1) => /=.
  - move=> a [] _ H.
    rewrite addn1 in H.
    rewrite H.
    exact: ltn0Sn.
  - move=> [] _ H.
    rewrite H.
    done.
Qed.

Lemma upd_index_lt :
  forall (m1 m2 : vmap) (v : var) (i : index),
    (m2, i) = upd_index m1 v -> get_index m1 v < i.
Proof.
  move=> m1 m2 v i; rewrite /upd_index /get_index.
  case: (VM.find v m1) => /=.
  - move=> a [] _ H.
    rewrite addn1 in H.
    rewrite H.
    exact: ltnSn.
  - move=> [] _ H.
    rewrite H.
    done.
Qed.

Lemma upd_index_leF :
  forall (m1 m2 : vmap) (v : var) (i : index),
    (m2, i) = upd_index m1 v -> i <= get_index m1 v -> False.
Proof.
  move=> m1 m2 v i Heq Hle.
  move: (upd_index_lt Heq) => Hlt.
  move: (leq_ltn_trans Hle Hlt).
  rewrite ltnn.
  done.
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

Lemma get_upd_index_le :
  forall (m1 m2 : vmap) (v : var) (i : index) (x : var),
    (m2, i) = upd_index m1 v ->
    get_index m1 x <= get_index m2 x.
Proof.
  move=> m1 m2 v i x Hupd.
  case Hxv: (x == v).
  - rewrite (eqP Hxv).
    rewrite (get_upd_index_eq Hupd).
    move: (upd_index_lt Hupd) => Hlt.
    exact: (ltnW Hlt).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq Hxv Hupd).
    exact: leqnn.
Qed.

Lemma ssa_instr_index_le :
  forall m1 m2 v i si,
    ssa_instr m1 i = (m2, si) ->
    get_index m1 v <= get_index m2 v.
Proof.
  move=> m1 m2 v i si.
  elim: i m1 m2 v si.
  - move=> v e m1 m2 x si Hsi.
    move: (ssa_qassign Hsi) => {Hsi} [i [Hupd Hsi]].
    exact: (get_upd_index_le _ Hupd).
  - move=> vh vl e p m1 m2 x si Hsi.
    move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
    move: (get_upd_index_le x Hupdh) => Hle1.
    move: (get_upd_index_le x Hupdl) => Hle2.
    exact: (leq_trans Hle1 Hle2).
Qed.

Lemma ssa_program_index_le :
  forall m1 m2 v p sp,
    ssa_program m1 p = (m2, sp) ->
    get_index m1 v <= get_index m2 v.
Proof.
  move=> m1 m2 v p sp.
  elim: p m1 m2 v sp.
  - move=> m1 m2 v sp Hsp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm1 Hsp.
    rewrite Hm1; exact: leqnn.
  - move=> hd tl IH m1 m2 v sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    move: (ssa_instr_index_le v Hshd) => Hle1.
    move: (IH _ _ v _ Hstl) => Hle2.
    exact: (leq_trans Hle1 Hle2).
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
  - move=> e IH p n Hn.
    inversion_clear Hn.
    apply: SSA.EQPow.
    exact: (IH _ H).
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
  elim: i.
  - move=> v e si Hsi Heq /= Hei Hesi.
    move: (ssa_qassign Hsi) => {Hsi} [idx [Hupd Hsi]].
    move=> x.
    rewrite Hsi in Hesi.
    inversion_clear Hei.
    inversion_clear Hesi.
    case Hxv: (x == v).
    + rewrite (State.acc_Upd_eq Hxv H0).
      rewrite (SSA.State.acc_Upd_eq _ H2).
      * move: (ssa_eval_exp Heq H) => H3.
        move: (SSA.eval_exp_unique H1 H3).
        by move/eqP=> Hn; rewrite Hn.
      * rewrite (eqP Hxv) (get_upd_index_eq Hupd).
        exact: eqxx.
    + move/idP/negP: Hxv => Hxv.
      rewrite (get_upd_index_neq Hxv Hupd).
      rewrite (State.acc_Upd_neq Hxv H0).
      rewrite (SSA.State.acc_Upd_neq _ H2).
      * exact: (Heq x).
      * exact: (pair_neq1 _ _ Hxv).
  - move=> vh vl e p si Hsi Heq Hei Hesi.
    move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
    inversion_clear Hei.
    rewrite Hsi in Hesi; inversion_clear Hesi => {Hsi}.
    move: (ssa_eval_exp_eq Heq H H3) => {H H3} Hnn4. (* n = n4 *)
    rewrite Hnn4 in H1 H2.
    rewrite -H1 in H5; rewrite -H2 in H6 => {H1 H2}. (* n0 = n1, n3 = n2 *)
    move=> x.
    rewrite H0 H4.
    case Hxl: (x == vl); [idtac | case Hxh: (x == vh)].
    + rewrite (State.acc_upd_eq _ _ Hxl).
      rewrite (eqP Hxl) (get_upd_index_eq Hupdl).
      rewrite (SSA.State.acc_upd_eq _ _ (eqxx (vl, il))).
      by rewrite H6.
    + move/idP/negP: Hxl => Hxl.
      rewrite (State.acc_upd_neq _ _ Hxl).
      rewrite (State.acc_upd_eq _ _ Hxh).
      rewrite (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl)).
      move: (get_upd_index_eq Hupdh) => Hidx.
      move: (get_upd_index_neq Hxl Hupdl) => Hidx'.
      rewrite -Hidx Hidx' (eqP Hxh).
      rewrite (SSA.State.acc_upd_eq _ _ (eqxx (vh, get_index m3 vh))).
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
  - elim: i si Hi Heq Hei.
    + move=> v e si Hsi Heq Hei.
      move: (ssa_qassign Hsi) => {Hsi} [idx [Hupd Hsi]].
      inversion_clear Hei.
      pose ss2 := SSA.State.upd (v, idx) n ss1.
      exists ss2.
      * rewrite Hsi; apply: (SSA.EQAssign (n:=n)).
        -- exact: (ssa_eval_exp Heq H).
        -- exact: SSA.State.Upd_upd.
    + move=> vh vl e p si Hsi Heq Hei.
      move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
      inversion_clear Hei.
      pose ss2 := SSA.State.upd (vl, il) n2 (SSA.State.upd (vh, ih) n1 ss1).
      exists ss2.
      * rewrite Hsi; apply: (SSA.EQSplit (n1:=n1) (n2:=n2)).
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
    move: (eval_program_cons Hep) => [s3 [Hehd Hetl]].
    move: (ssa_program_cons Hsp) => [m3 [h [t [Hh [Ht Hht]]]]].
    rewrite Hht in Hesp.
    move: (SSA.eval_program_cons Hesp) => [ss3 [Heshd Hestl]].
    move: (ssa_eval_instr Hh Heq Hehd Heshd) => Heq'.
    exact: (IH _ _ _ _ _ _ _ Ht Heq' Hetl Hestl).
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
      move: (eval_program_cons Hep) => [s3 [Hehd Hetl]].
      move: (ssa_program_cons Hsp) => [m3 [h [t [Hh [Ht Hht]]]]].
      move: (ssa_eval_instr_succ Hh Heq Hehd) => [ss3 [Heh Heqh]].
      move: (IH m3 m2 _ _ _ t Ht Heqh Hetl) => [ss2 Het].
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
  - move=> e IH p n He.
    inversion_clear He.
    apply: EQPow.
    exact: (IH _ H).
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
  - elim: i si Hi Heq Hesi.
    + move=> v e si Hsi Heq Hesi.
      move: (ssa_qassign Hsi) => {Hsi} [idx [Hupd Hsi]].
      rewrite Hsi in Hesi.
      inversion_clear Hesi.
      pose s2 := State.upd v n s1.
      exists s2.
      * apply: (EQAssign (n:=n)).
        -- exact: (dessa_eval_exp Heq H).
        -- exact: State.Upd_upd.
    + move=> vh vl e p si Hsi Heq Hesi.
      move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
      rewrite Hsi in Hesi.
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
      move: (SSA.eval_program_cons Hesp) => [ss3 [Heshd Hestl]].
      move: (dessa_eval_instr_succ Hh Heq Heshd) => [s3 [Heh Heqh]].
      move: (IH m3 m2 _ _ _ t Ht Heqh Hestl) => [s4 Het].
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

Corollary dessa_state_equiv :
  forall m s, state_equiv m (dessa_state m s) s.
Proof.
  move=> m s x.
  exact: acc_dessa_state.
Qed.



(** Soundness and completeness *)

Theorem ssa_spec_sound (s : spec) :
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

Theorem ssa_spec_complete (s : spec) :
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



(** Well-formed SSA *)

Definition ssa_var_unchanged_instr (v : SSA.var) (i : SSA.instr) : bool :=
  match i with
  | SSA.QAssign v' _ => v != v'
  | SSA.QSplit vh vl _ _ => (v != vh) && (v != vl)
  end.

Fixpoint ssa_var_unchanged_program (v : SSA.var) (p : SSA.program) : bool :=
  match p with
  | [::] => true
  | hd::tl => (ssa_var_unchanged_instr v hd) && (ssa_var_unchanged_program v tl)
  end.

Fixpoint ssa_vars_unchanged_program (vs : seq SSA.var) (p : SSA.program) : bool :=
  match vs with
  | [::] => true
  | hd::tl => ssa_var_unchanged_program hd p && ssa_vars_unchanged_program tl p
  end.

Fixpoint ssa_well_formed_program (p : SSA.program) : bool :=
  match p with
  | [::] => true
  | hd::tl =>
    match hd with
    | SSA.QAssign v _ => (ssa_var_unchanged_program v tl)
                           && (ssa_well_formed_program tl)
    | SSA.QSplit vh vl _ _ => (ssa_var_unchanged_program vh tl)
                                && (ssa_var_unchanged_program vl tl)
                                && (ssa_well_formed_program tl)
    end
  end.

Definition ssa_well_formed_spec (sp : SSA.spec) : bool :=
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp (SSA.spre sp)))
                             (SSA.sprog sp)
                             && ssa_well_formed_program (SSA.sprog sp).

Lemma acc_unchanged_instr v i s1 s2 :
  ssa_var_unchanged_instr v i ->
  SSA.eval_instr s1 i s2 ->
  SSA.State.acc v s2 = SSA.State.acc v s1.
Proof.
  elim: i.
  - move=> v' e /= Hne Hei.
    inversion_clear Hei.
    rewrite (H0 v) (SSA.State.acc_upd_neq _ _ Hne).
    reflexivity.
  - move=> vh vl e p /= /andP [Hneh Hnel] Hei.
    inversion_clear Hei.
    rewrite (H0 v) (SSA.State.acc_upd_neq _ _ Hnel)
            (SSA.State.acc_upd_neq _ _ Hneh).
    reflexivity.
Qed.

Lemma acc_unchanged_program v p s1 s2 :
  ssa_var_unchanged_program v p ->
  SSA.eval_program s1 p s2 ->
  SSA.State.acc v s2 = SSA.State.acc v s1.
Proof.
  elim: p s1 s2.
  - move=> s1 s2 _ Hep.
    rewrite (SSA.eval_program_empty Hep).
    reflexivity.
  - move=> hd tl IH s1 s2 /andP [Huchd Huctl] Hep.
    move: (SSA.eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    rewrite -(acc_unchanged_instr Huchd Hehd).
    exact: (IH _ _ Huctl Hetl).
Qed.

Lemma ssa_var_unchanged_program_cons v hd tl :
  ssa_var_unchanged_program v (hd::tl) ->
  ssa_var_unchanged_instr v hd /\ ssa_var_unchanged_program v tl.
Proof.
  move => /andP H.
  exact: H.
Qed.

Lemma ssa_var_unchanged_program_concat v p1 p2 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  ssa_var_unchanged_program v p1 /\ ssa_var_unchanged_program v p2.
Proof.
  elim: p1 p2.
  - move=> /= p2 H.
    by rewrite H.
  - move=> hd tl IH p2 /andP [Hhd Htlp2].
    move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2].
    by rewrite /= Hhd Htl Hp2.
Qed.

Lemma acc_unchanged_program_cons v hd tl s1 s2 s3 :
  ssa_var_unchanged_program v (hd::tl) ->
  SSA.eval_instr s1 hd s2 ->
  SSA.eval_program s2 tl s3 ->
  SSA.State.acc v s2 = SSA.State.acc v s1 /\
  SSA.State.acc v s3 = SSA.State.acc v s1.
Proof.
  move=> /andP [Hunhd Huntl] Hehd Hetl.
  move: (acc_unchanged_instr Hunhd Hehd) (acc_unchanged_program Huntl Hetl) =>
    H21 H32.
  rewrite H32 H21.
  split; reflexivity.
Qed.

Lemma acc_unchanged_program_concat v p1 p2 s1 s2 s3 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  SSA.eval_program s1 p1 s2 ->
  SSA.eval_program s2 p2 s3 ->
  SSA.State.acc v s2 = SSA.State.acc v s1 /\
  SSA.State.acc v s3 = SSA.State.acc v s1.
Proof.
  move=> Hun12 Hep1 Hep2.
  move: (ssa_var_unchanged_program_concat Hun12) => {Hun12} [Hun1 Hun2].
  rewrite (acc_unchanged_program Hun2 Hep2) (acc_unchanged_program Hun1 Hep1).
  split; reflexivity.
Qed.

Lemma ssa_instr_le_unchanged m1 m2 i si :
  forall v iv,
    iv <= get_index m1 v ->
    ssa_instr m1 i = (m2, si) ->
    ssa_var_unchanged_instr (v, iv) si.
Proof.
  elim: i m1 m2 si.
  - move=> x e m1 m2 si v iv Hiv Hsi.
    move: (ssa_qassign Hsi) => {Hsi} [ix [Hupd Hsi]].
    rewrite Hsi => {Hsi} /=.
    apply/eqP => Heq; case: Heq => Hv Hi.
    rewrite Hv Hi in Hiv => {Hv Hi}.
    exact: (upd_index_leF Hupd Hiv).
  - move=> vh vl e p m1 m2 si v iv Hiv Hsi.
    move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
   rewrite Hsi => {Hsi} /=.
    apply/andP; split; apply/eqP => Heq; case: Heq => Hv Hi.
    + rewrite Hv Hi in Hiv => {Hv Hi v iv}.
      exact: (upd_index_leF Hupdh Hiv).
    + rewrite Hv Hi in Hiv => {Hv Hi v iv}.
      move: (get_upd_index_le vl Hupdh) => Hle.
      move: (upd_index_lt Hupdl) => Hlt.
      move: (leq_ltn_trans Hle Hlt) => {Hle Hlt} Hlt.
      move: (leq_ltn_trans Hiv Hlt) => {Hiv Hlt} Hlt.
      rewrite ltnn in Hlt.
      done.
Qed.

Lemma ssa_program_le_unchanged m1 m2 p sp :
  forall v i,
    i <= get_index m1 v ->
    ssa_program m1 p = (m2, sp) ->
    ssa_var_unchanged_program (v, i) sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp v i Hi /= [Hm Hp].
    by rewrite -Hp.
  - move=> hd tl IH m1 m2 sp v i Hle Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp => {Hsp sp} /=.
    apply/andP; split.
    + exact: (ssa_instr_le_unchanged Hle Hshd).
    + move: (ssa_instr_index_le v Hshd) => Hle2.
      move: (leq_trans Hle Hle2) => {Hle Hle2} Hle.
      exact: (IH _ _ _ _ _ Hle Hstl).
Qed.

Theorem ssa_program_well_formed m1 m2 p sp :
  ssa_program m1 p = (m2, sp) ->
  ssa_well_formed_program sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp Hsp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm Hsp.
    rewrite -Hsp; done.
  - move=> hd tl IH m1 m2 sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp => {Hsp sp}.
    case: hd Hshd.
    + move=> v e Hshd.
      move: (ssa_qassign Hshd) => {Hshd} [iv [Hupd Hshd]].
      rewrite Hshd /= => {Hshd shd}.
      apply/andP; split.
      * apply: (ssa_program_le_unchanged _ Hstl).
        rewrite (get_upd_index_eq Hupd).
        exact: leqnn.
      * exact: (IH _ _ _ Hstl).
    + move=> vh vl e p Hshd.
      move: (ssa_qsplit Hshd) => {Hshd} [ih [il [m4 [Hupdh [Hupdl Hshd]]]]].
      rewrite Hshd /= => {Hshd shd}.
      apply/andP; split; [apply/andP; split | idtac].
      * apply: (ssa_program_le_unchanged _ Hstl).
        rewrite -(get_upd_index_eq Hupdh).
        exact: (get_upd_index_le vh Hupdl).
      * apply: (ssa_program_le_unchanged _ Hstl).
        rewrite (get_upd_index_eq Hupdl).
        exact: leqnn.
      * exact: (IH _ _ _ Hstl).
Qed.

Lemma ssa_exp_var_index m e v i :
  SSA.VS.mem (v, i) (SSA.vars_exp (ssa_exp m e)) ->
  get_index m v = i.
Proof.
  elim: e m v i.
  - move=> v m x i Hmem.
    move/SSA.VSLemmas.memP: Hmem => Hin.
    move: (SSA.VS.singleton_1 Hin) => /eqP [] Hv Hi.
    rewrite -Hv; exact: Hi.
  - move=> c m x i Hmem.
    discriminate.
  - move=> op e IH m x i Hmem.
    exact: (IH _ _ _ Hmem).
  - move=> op e1 IH1 e2 IH2 m x i Hmem.
    move/SSA.VSLemmas.memP: Hmem => Hin.
    move: {Hin} (SSA.VS.union_1 Hin); case => /SSA.VSLemmas.memP Hmem.
    + apply: (IH1 _ _ _ Hmem); reflexivity.
    + apply: (IH2 _ _ _ Hmem); reflexivity.
  - move=> e IH p n v i /= Hmem.
    exact: (IH _ _ _ Hmem).
Qed.

Lemma ssa_bexp_var_index m e v i :
  SSA.VS.mem (v, i) (SSA.vars_bexp (ssa_bexp m e)) ->
  get_index m v = i.
Proof.
  elim: e m v i => /=.
  - move=> m v i Hmem.
    discriminate.
  - move=> e1 e2 m v i Hmem.
    rewrite SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_exp_var_index Hmem); reflexivity.
  - move=> e1 e2 p m v i Hmem.
    rewrite SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_exp_var_index Hmem); reflexivity.
  - move=> e1 IH1 e2 IH2 m v i Hmem.
    rewrite SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem.
    + apply: (IH1 _ _ _ Hmem); reflexivity.
    + apply: (IH2 _ _ _ Hmem); reflexivity.
Qed.

Lemma ssa_spec_in_pre_unchanged s v :
  SSA.VS.mem v (SSA.vars_bexp (SSA.spre (ssa_spec s))) ->
  ssa_var_unchanged_program v (SSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  move=> Hmem.
  rewrite Hpre in Hmem.
  destruct v as [v i].
  move: (ssa_bexp_var_index Hmem) => Hidx.
  apply: (ssa_program_le_unchanged (m1:=empty_vmap)).
  - by rewrite Hidx.
  - symmetry; exact: Hprog.
Qed.

Lemma ssa_spec_unchanged_pre s :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp (SSA.spre (ssa_spec s)))) (SSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  set vs := SSA.vars_bexp (SSA.spre (ssa_spec s)).
  have: forall v : SSA.var,
      SetoidList.InA SSA.V.eq v (SSA.VS.elements vs) -> SSA.VS.mem v vs.
  - move=> v Hvl.
    move: (SSA.VS.elements_2 Hvl) => Hvs.
    apply/SSA.VSLemmas.memP.
    assumption.
  - set vl := SSA.VS.elements vs.
    elim: vl.
    + done.
    + move=> hd tl IH H.
      apply/andP; split.
      * move: (H hd (SetoidList.InA_cons_hd _ (eqxx hd))) => Hmem.
        exact: (ssa_spec_in_pre_unchanged Hmem).
      * apply: IH => v Hin.
        apply: H.
        apply: SetoidList.InA_cons_tl.
        assumption.
Qed.

Lemma ssa_spec_well_formed_program s :
  ssa_well_formed_program (SSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  exact: (ssa_program_well_formed (Logic.eq_sym Hprog)).
Qed.

Theorem ssa_spec_well_formed s :
  ssa_well_formed_spec (ssa_spec s).
Proof.
  apply/andP; split.
  - exact: ssa_spec_unchanged_pre.
  - exact: ssa_spec_well_formed_program.
Qed.