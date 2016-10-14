
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

Notation "@- x" := (SSA.QNeg x) (at level 35, right associativity) : ssa_scope.
Notation "x @+ y" := (SSA.QBinop SSA.QAdd x y) (at level 50, left associativity) : ssa_scope.
Notation "x @- y" := (SSA.QBinop SSA.QSub x y)  (at level 50, left associativity) : ssa_scope.
Notation "x @* y" := (SSA.QBinop SSA.QMul x y)  (at level 40, left associativity) : ssa_scope.
Notation "x @^ y" := (SSA.QPow x y)  (at level 30, right associativity) : ssa_scope.
Notation "x @:= y" := (SSA.QAssign x y) (at level 70, no associativity) : ssa_scope.
Notation "x ++ y @:= z # p" := (SSA.QSplit x y z p) (at level 70, no associativity) : ssa_scope.
Notation "x @= y" := (SSA.QEq x y) (at level 70, no associativity) : ssa_scope.
Notation "x @= y 'mod' z" := (SSA.QCong x y z) (at level 70, y at next level, no associativity) : ssa_scope.
Notation "x @&& y" := (SSA.QAnd x y) (at level 70, no associativity) : mqhasm_scope.
Notation "s |= f" := (SSA.eval_bexp f true s) (at level 74, no associativity) : ssa_scope.
Notation "f ===> g" := (SSA.entails f g) (at level 82, no associativity) : ssa_scope.
Notation "{{ f }} p {{ g }}" := ({| SSA.spre := f; SSA.sprog := p; SSA.spost := g |}) (at level 82, no associativity) : ssa_scope.
Notation "|= s" := (valid_spec s) (at level 83, no associativity).

Definition svar (x : SSA.V.t) := fst x.
Definition sidx (x : SSA.V.t) := snd x.
Hint Unfold svar sidx.



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
  {| SSA.spre := f; SSA.sprog := p; SSA.spost := g |}.

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
  destruct s as [f p g] => /=.
  rewrite /ssa_spec /=.
  set tmp := ssa_program empty_vmap p.
  destruct tmp as [m sp] => /=.
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

Lemma ssa_eval_exp m s ss e :
  state_equiv m s ss ->
  SSA.eval_exp (ssa_exp m e) ss = eval_exp e s.
Proof.
  move=> Heq; elim: e => /=.
  - move=> v.
    rewrite (Heq v).
    reflexivity.
  - move=> c.
    reflexivity.
  - move=> op e IH.
    rewrite ssa_eval_unop IH.
    reflexivity.
  - move=> op e1 IH1 e2 IH2.
    rewrite ssa_eval_binop IH1 IH2.
    reflexivity.
  - move=> e IH p.
    rewrite IH.
    reflexivity.
Qed.

Lemma ssa_eval_bexp m s ss e :
  state_equiv m s ss ->
  SSA.eval_bexp (ssa_bexp m e) ss <-> eval_bexp e s.
Proof.
  move=> Heq; elim: e => /=.
  - done.
  - move=> e1 e2.
    rewrite 2!(ssa_eval_exp _ Heq).
    done.
  - move=> e1 e2 p.
    rewrite 2!(ssa_eval_exp _ Heq).
    done.
  - move=> e1 [IH11 IH12] e2 [IH21 IH22].
    tauto.
Qed.

Lemma ssa_eval_bexp1 m s ss e :
  state_equiv m s ss ->
  SSA.eval_bexp (ssa_bexp m e) ss -> eval_bexp e s.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_eval_bexp2 m s ss e :
  state_equiv m s ss ->
  eval_bexp e s -> SSA.eval_bexp (ssa_bexp m e) ss.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma ssa_eval_instr :
  forall m1 m2 s1 s2 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i = s2 ->
    SSA.eval_instr ss1 si = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 i.
  elim: i.
  - move=> v e si Hsi Heq /= Hei Hesi.
    move: (ssa_qassign Hsi) => {Hsi} [idx [Hupd Hsi]].
    move=> x.
    rewrite Hsi /= in Hesi => {Hsi}.
    move: (get_upd_index_eq Hupd) => Hidx.
    rewrite -Hei -Hesi => {Hei Hesi}.
    case Hxv: (x == v) => /=.
    + rewrite (State.acc_upd_eq _ _ Hxv).
      rewrite (eqP Hxv) Hidx (SSA.State.acc_upd_eq _ _ (eqxx (v, idx))).
      rewrite (ssa_eval_exp _ Heq).
      reflexivity.
    + move/idP/negP: Hxv => Hxv.
      rewrite (State.acc_upd_neq _ _ Hxv).
      rewrite (get_upd_index_neq Hxv Hupd).
      rewrite (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxv)).
      exact: Heq.
  - move=> vh vl e p si Hsi Heq /= Hei Hesi.
    move: (ssa_qsplit Hsi) => {Hsi} [ih [il [m3 [Hupdh [Hupdl Hsi]]]]].
    rewrite Hsi /= in Hesi => {Hsi}.
    rewrite (ssa_eval_exp _ Heq) in Hesi.
    move: Hei Hesi; set tmp := Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p);
        destruct tmp as [q r] => Hei Hesi.
    move=> x.
    rewrite -Hei -Hesi => {Hei Hesi}.
    case Hxl: (x == vl); [idtac | case Hxh: (x == vh)].
    + rewrite (State.acc_upd_eq _ _ Hxl).
      rewrite (eqP Hxl) (get_upd_index_eq Hupdl)
              (SSA.State.acc_upd_eq _ _ (eqxx (vl, il))).
      reflexivity.
    + move/idP/negP: Hxl => Hxl.
      rewrite (State.acc_upd_neq _ _ Hxl) (State.acc_upd_eq _ _ Hxh).
      rewrite (SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl)).
      move: (get_upd_index_eq Hupdh) => Hidx.
      move: (get_upd_index_neq Hxl Hupdl) => Hidx'.
      rewrite -Hidx Hidx' (eqP Hxh).
      rewrite (SSA.State.acc_upd_eq _ _ (eqxx (vh, get_index m3 vh))).
      reflexivity.
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
    eval_instr s1 i = s2 ->
    exists ss2,
      SSA.eval_instr ss1 si = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 i si Hi Heq Hei.
  exists (SSA.eval_instr ss1 si); split.
  - reflexivity.
  - exact: (ssa_eval_instr Hi Heq Hei).
Qed.

Lemma ssa_eval_program :
  forall m1 m2 s1 s2 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    SSA.eval_program ss1 sp = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 p.
  elim: p m1 m2 s1 s2 ss1 ss2 => /=.
  - move=> m1 m2 s1 s2 ss1 ss2 p [Hm Hp] Heq Hep Hesp.
    rewrite -Hp in Hesp.
    rewrite -Hep -Hesp -Hm.
    exact: Heq.
  - move=> hd tl IH m1 m2 s1 s2 ss1 ss2 sp Hsp Heq Hep Hesp.
    move: (eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [h [t [Hh [Ht Hht]]]]].
    rewrite Hht in Hesp.
    move: (SSA.eval_program_cons Hesp) => [ss3 [Heshd Hestl]].
    move: (ssa_eval_instr Hh Heq Hehd Heshd) => Heq'.
    exact: (IH _ _ _ _ _ _ _ Ht Heq' Hetl Hestl).
Qed.

Lemma ssa_eval_program_succ :
  forall m1 m2 s1 s2 ss1 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    exists ss2,
      SSA.eval_program ss1 sp = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 p sp Hp Heq Hep.
  exists (SSA.eval_program ss1 sp); split.
  - reflexivity.
  - exact: (ssa_eval_program Hp Heq Hep).
Qed.

Lemma dessa_eval_instr_succ :
  forall m1 m2 s1 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    SSA.eval_instr ss1 si = ss2 ->
    exists s2,
      eval_instr s1 i = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 i si Hi Heq Hesi.
  exists (eval_instr s1 i); split.
  - reflexivity.
  - apply: (ssa_eval_instr Hi Heq _ Hesi).
    reflexivity.
Qed.

Lemma dessa_eval_program_succ :
  forall m1 m2 s1 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    SSA.eval_program ss1 sp = ss2 ->
    exists s2,
      eval_program s1 p = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 p sp Hp Heq Hesp.
  exists (eval_program s1 p); split.
  - reflexivity.
  - apply: (ssa_eval_program Hp Heq _ Hesp).
    reflexivity.
Qed.



(** Convert a Qhasm state to an SSA state. *)

Definition ssa_state (m : vmap) (s : State.t) : SSA.State.t :=
  fun v =>
    if (sidx v) == get_index m (svar v)
    then State.acc (svar v) s
    else State.acc (svar v) State.empty.

Lemma acc_ssa_state_eq :
  forall (m : vmap) (s : State.t) (v : var) (i : index),
    i == get_index m v ->
    SSA.State.acc (v, i) (ssa_state m s) = State.acc v s.
Proof.
  move=> m s v i Heq.
  rewrite /ssa_state /SSA.State.acc /SSA.Store.acc /=.
  rewrite Heq.
  reflexivity.
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
  fun v => SSA.State.acc (v, get_index m v) s.

Lemma acc_dessa_state :
  forall (m : vmap) (s : SSA.State.t) (v : var),
    State.acc v (dessa_state m s) = SSA.State.acc (v, get_index m v) s.
Proof.
  reflexivity.
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
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec s1 s2 /= Hf Hep.
  pose ss1 := ssa_state empty_vmap s1.
  pose Heq1 := (ssa_state_equiv empty_vmap s1).
  move: (ssa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hep) => [ss2 [Hesp Heq2]].
  move: (ssa_eval_bexp2 Heq1 Hf) => Hsf.
  move: (Hspec ss1 ss2 Hsf Hesp) => /= Hsg.
  exact: (ssa_eval_bexp1 Heq2 Hsg).
Qed.

Theorem ssa_spec_complete (s : spec) :
  valid_spec s -> SSA.valid_spec (ssa_spec s).
Proof.
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec ss1 ss2 /= Hsf Hesp.
  pose s1 := dessa_state empty_vmap ss1.
  pose Heq1 := (dessa_state_equiv empty_vmap ss1).
  move: (dessa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hesp) => [s2 [Hep Heq2]].
  move: (ssa_eval_bexp1 Heq1 Hsf) => Hf.
  move: (Hspec s1 s2 Hf Hep) => /= Hg.
  exact: (ssa_eval_bexp2 Heq2 Hg).
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
    (ssa_well_formed_program tl) &&
    match hd with
    | SSA.QAssign v _ => (ssa_var_unchanged_program v tl)
    | SSA.QSplit vh vl _ _ => (ssa_var_unchanged_program vh tl)
                                && (ssa_var_unchanged_program vl tl)
    end
  end.

Definition ssa_well_formed_spec (sp : SSA.spec) : bool :=
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp (SSA.spre sp)))
                             (SSA.sprog sp)
                             && ssa_well_formed_program (SSA.sprog sp).

Lemma acc_unchanged_instr v i s1 s2 :
  ssa_var_unchanged_instr v i ->
  SSA.eval_instr s1 i = s2 ->
  SSA.State.acc v s2 = SSA.State.acc v s1.
Proof.
  elim: i.
  - move=> v' e /= Hne Hei.
    rewrite -Hei (SSA.State.acc_upd_neq _ _ Hne).
    reflexivity.
  - move=> vh vl e p /= /andP [Hneh Hnel] Hei.
    rewrite -Hei => {Hei}.
    set tmp := Z.div_eucl (SSA.eval_exp e s1) (Z.pow_pos 2 p);
        destruct tmp as [q r].
    rewrite (SSA.State.acc_upd_neq _ _ Hnel)
            (SSA.State.acc_upd_neq _ _ Hneh).
    reflexivity.
Qed.

Lemma acc_unchanged_program v p s1 s2 :
  ssa_var_unchanged_program v p ->
  SSA.eval_program s1 p = s2 ->
  SSA.State.acc v s1 = SSA.State.acc v s2.
Proof.
  elim: p s1 s2.
  - move=> s1 s2 _ Hep.
    rewrite -Hep.
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
  SSA.eval_instr s1 hd = s2 ->
  SSA.eval_program s2 tl = s3 ->
  SSA.State.acc v s2 = SSA.State.acc v s1 /\
  SSA.State.acc v s3 = SSA.State.acc v s1.
Proof.
  move=> /andP [Hunhd Huntl] Hehd Hetl.
  move: (acc_unchanged_instr Hunhd Hehd) (acc_unchanged_program Huntl Hetl) =>
    H21 H32.
  rewrite -H32 -H21.
  split; reflexivity.
Qed.

Lemma acc_unchanged_program_concat v p1 p2 s1 s2 s3 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  SSA.eval_program s1 p1 = s2 ->
  SSA.eval_program s2 p2 = s3 ->
  SSA.State.acc v s2 = SSA.State.acc v s1 /\
  SSA.State.acc v s3 = SSA.State.acc v s1.
Proof.
  move=> Hun12 Hep1 Hep2.
  move: (ssa_var_unchanged_program_concat Hun12) => {Hun12} [Hun1 Hun2].
  rewrite -(acc_unchanged_program Hun2 Hep2) -(acc_unchanged_program Hun1 Hep1).
  split; reflexivity.
Qed.

Lemma ssa_unchanged_program_mem v vs p :
  ssa_vars_unchanged_program (SSA.VS.elements vs) p ->
  SSA.VS.mem v vs ->
  ssa_var_unchanged_program v p.
Proof.
  move=> Hunch Hmem.
  move: (SSA.VSLemmas.mem_in_elements Hmem) Hunch => {Hmem}.
  set vl := SSA.VS.elements vs.
  elim: vl v p.
  - move=> v p Hin Hunch.
    by inversion_clear Hin.
  - move=> hd tl IH v p Hin /andP [Hhd Htl].
    inversion_clear Hin.
    + by rewrite (eqP H).
    + exact: (IH _ _ H Htl).
Qed.

Lemma ssa_unchanged_program_local s p :
  (forall v, SSA.VS.mem v s -> ssa_var_unchanged_program v p) ->
  ssa_vars_unchanged_program (SSA.VS.elements s) p.
Proof.
  move=> H.
  have: forall v, SetoidList.InA SSA.VS.E.eq v (SSA.VS.elements s) ->
                  ssa_var_unchanged_program v p by
        move=> v Hin; apply: H; exact: (SSA.VSLemmas.in_elements_mem Hin).
  move=> {H}.
  set vl := SSA.VS.elements s.
  elim: vl p.
  - done.
  - move=> hd tl IH p H.
    apply/andP; split.
    + apply: H.
      exact: SetoidList.InA_cons_hd.
    + apply: IH.
      move=> v Hin.
      apply: H.
      exact: (SetoidList.InA_cons_tl _ Hin).
Qed.

Lemma ssa_unchanged_program_global s p :
  ssa_vars_unchanged_program (SSA.VS.elements s) p ->
  (forall v, SSA.VS.mem v s -> ssa_var_unchanged_program v p).
Proof.
  move=> H v Hmem.
  exact: (ssa_unchanged_program_mem H Hmem).
Qed.

Lemma ssa_unchanged_program_union s1 s2 p :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.VS.union s1 s2)) p ->
  ssa_vars_unchanged_program (SSA.VS.elements s1) p /\
  ssa_vars_unchanged_program (SSA.VS.elements s2) p.
Proof.
  move=> Hun.
  move: (ssa_unchanged_program_global Hun) => {Hun} Hun.
  split; apply: ssa_unchanged_program_local => v Hmem.
  - apply: Hun.
    rewrite SSA.VSLemmas.union_b.
    by rewrite Hmem.
  - apply: Hun.
    rewrite SSA.VSLemmas.union_b.
    rewrite Hmem.
    by case: (SSA.VS.mem v s1).
Qed.

Lemma ssa_unchanged_program_eval_exp e s1 s2 p :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_exp e)) p ->
  SSA.eval_program s1 p = s2 ->
  SSA.eval_exp e s1 = SSA.eval_exp e s2.
Proof.
  elim: e => /=.
  - move=> v /andP [Hunch _] Hp.
    exact: (acc_unchanged_program Hunch Hp).
  - move=> c _ Hp.
    reflexivity.
  - move=> op e IH Hunch Hp.
    rewrite (IH Hunch Hp).
    reflexivity.
  - move=> op e1 IH1 e2 IH2 Hunch Hp.
    move: (ssa_unchanged_program_union Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp).
    reflexivity.
  - move=> e IH i Hunch Hp.
    rewrite (IH Hunch Hp).
    reflexivity.
Qed.

Lemma ssa_unchanged_program_eval_bexp e s1 s2 p :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp e)) p ->
  SSA.eval_program s1 p = s2 ->
  SSA.eval_bexp e s1 <-> SSA.eval_bexp e s2.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Hunch Hp.
    move: (ssa_unchanged_program_union Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (ssa_unchanged_program_eval_exp Hunch1 Hp)
            (ssa_unchanged_program_eval_exp Hunch2 Hp).
    done.
  - move=> e1 e2 i Hunch Hp.
    move: (ssa_unchanged_program_union Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (ssa_unchanged_program_eval_exp Hunch1 Hp)
            (ssa_unchanged_program_eval_exp Hunch2 Hp).
    done.
  - move=> e1 IH1 e2 IH2 Hunch Hp.
    move: (ssa_unchanged_program_union Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp).
    done.
Qed.

Lemma ssa_unchanged_program_eval_bexp1 e s1 s2 p :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp e)) p ->
  SSA.eval_program s1 p = s2 ->
  SSA.eval_bexp e s1 -> SSA.eval_bexp e s2.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_unchanged_program_eval_bexp2 e s1 s2 p :
  ssa_vars_unchanged_program (SSA.VS.elements (SSA.vars_bexp e)) p ->
  SSA.eval_program s1 p = s2 ->
  SSA.eval_bexp e s2 -> SSA.eval_bexp e s1.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma well_formed_program_tl hd tl :
  ssa_well_formed_program (hd::tl) ->
  ssa_well_formed_program tl.
Proof.
  move=> /andP [H _].
  assumption.
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
    apply/andP; split.
    + exact: (IH _ _ _ Hstl).
    + case: hd Hshd.
      * move=> v e Hshd.
        move: (ssa_qassign Hshd) => {Hshd} [iv [Hupd Hshd]].
        rewrite Hshd /= => {Hshd shd}.
        apply: (ssa_program_le_unchanged _ Hstl).
        rewrite (get_upd_index_eq Hupd).
        exact: leqnn.
      * move=> vh vl e p Hshd.
        move: (ssa_qsplit Hshd) => {Hshd} [ih [il [m4 [Hupdh [Hupdl Hshd]]]]].
        rewrite Hshd /= => {Hshd shd}.
        apply/andP; split.
        -- apply: (ssa_program_le_unchanged _ Hstl).
           rewrite -(get_upd_index_eq Hupdh).
           exact: (get_upd_index_le vh Hupdl).
        -- apply: (ssa_program_le_unchanged _ Hstl).
           rewrite (get_upd_index_eq Hupdl).
           exact: leqnn.
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
