
(** * Integer programs as mini Qhasm+ *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From Common Require Import Types Nats ZAriths FSets Var Store.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope mqhasm_scope with mqhasm.

Local Open Scope mqhasm_scope.


Reserved Notation "@- x" (at level 35, right associativity).
Reserved Notation "x @+ y" (at level 50, left associativity).
Reserved Notation "x @- y" (at level 50, left associativity).
Reserved Notation "x @* y" (at level 40, left associativity).
Reserved Notation "x @^ y" (at level 30, right associativity).
Reserved Notation "x @:= y" (at level 70, no associativity).
Reserved Notation "x ++ y @:= z # p" (at level 70, no associativity).
Reserved Notation "x @= y" (at level 70, no associativity).
Reserved Notation "x @= y 'mod' z" (at level 70, y at next level, no associativity).
Reserved Notation "x @&& y" (at level 70, no associativity).
Reserved Notation "s |= f" (at level 74, no associativity).
Reserved Notation "f ===> g" (at level 82, no associativity).
Reserved Notation "{{ f }} p {{ g }}" (at level 82, no associativity).
Reserved Notation "|= s" (at level 83, no associativity).

Module MakeQhasm (V : SsrOrderedType).

  Module VS := FSetList.Make V.
  Module VSLemmas := FSetLemmas VS.



  (** Syntax *)

  Definition var : Type := V.t.

  Inductive unop : Set :=
  | QNeg.

  Inductive binop : Set :=
  | QAdd
  | QSub
  | QMul.

  Inductive exp : Type :=
  | QVar : var -> exp
  | QConst : Z -> exp
  | QUnop : unop -> exp -> exp
  | QBinop : binop -> exp -> exp -> exp
  | QPow : exp -> positive -> exp.

  Inductive instr : Type :=
  | QAssign : var -> exp -> instr
  | QSplit : var -> var -> exp -> positive -> instr.

  Global Arguments QConst n%Z.

  Definition program : Type := seq instr.

  Fixpoint vars_exp (e : exp) : VS.t :=
    match e with
    | QVar v => VS.singleton v
    | QConst _ => VS.empty
    | QUnop _ e => vars_exp e
    | QBinop _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | QPow e _ => vars_exp e
    end.

  Fixpoint vars_instr (i : instr) : VS.t :=
    match i with
    | QAssign v e => VS.add v (vars_exp e)
    | QSplit vh vl e _ => VS.add vh (VS.add vl (vars_exp e))
    end.

  Fixpoint vars_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (vars_instr hd) (vars_program tl)
    end.



  (** State *)

  Notation value := Z.

  Module Store := MakeTStore V.

  Module State.

    Definition t : Type := Store.t value.

    Definition empty : t := Store.empty value.

    Definition acc (x : var) (s : t) : value :=
      Store.acc x s.

    Definition upd (x : var) (v : value) (s : t) : t :=
      Store.upd x v s.

    Definition upd2 x1 v1 x2 v2 (s : t) : t :=
      Store.upd x2 v2 (Store.upd x1 v1 s).

    Lemma acc_upd_eq :
      forall x y v (s : t),
        x == y ->
        acc x (upd y v s) = v.
    Proof.
      exact: Store.acc_upd_eq.
    Qed.

    Lemma acc_upd_neq :
      forall x y v (s : t),
        x != y ->
        acc x (upd y v s) = acc x s.
    Proof.
      exact: Store.acc_upd_neq.
    Qed.

    Lemma acc_upd2_eq1 :
      forall x y1 v1 y2 v2 (s : t),
        x == y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof.
      move=> x y1 v1 y2 v2 s Hx1 Hx2.
      rewrite /upd2 (acc_upd_neq _ _ Hx2) (acc_upd_eq _ _ Hx1).
      reflexivity.
    Qed.

    Lemma acc_upd2_eq2 :
      forall x y1 v1 y2 v2 (s : t),
        x == y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof.
      move=> x y1 v1 y2 v2 s Hx2.
      rewrite /upd2 (acc_upd_eq _ _ Hx2).
      reflexivity.
    Qed.

    Lemma acc_upd2_neq :
      forall x y1 v1 y2 v2 s,
        x != y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof.
      move=> x y1 v1 y2 v2 s Hx1 Hx2.
      rewrite /upd2 (acc_upd_neq _ _ Hx2) (acc_upd_neq _ _ Hx1).
      reflexivity.
    Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Lemma Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).
    Proof.
      exact: Store.Upd_upd.
    Qed.

    Lemma Upd2_upd :
      forall x1 v1 x2 v2 s,
        Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof.
      move=> x1 v1 x2 v2 s y.
      reflexivity.
    Qed.

    Lemma acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.
    Proof.
      exact: Store.acc_Upd_eq.
    Qed.

    Lemma acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      exact: Store.acc_Upd_neq.
    Qed.

    Lemma acc_Upd2_eq1 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v1.
    Proof.
      move=> x y1 v1 y2 v2 s1 s2 Heq Hne Hupd.
      rewrite (Hupd x).
      exact: acc_upd2_eq1.
    Qed.

    Lemma acc_Upd2_eq2 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v2.
    Proof.
      move=> x y1 v1 y2 v2 s1 s2 Heq Hupd.
      rewrite (Hupd x).
      exact: acc_upd2_eq2.
    Qed.

    Lemma acc_Upd2_neq :
      forall x y1 v1 y2 v2 s1 s2,
        x != y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      move=> x y1 v1 y2 v2 s1 s2 Hne1 Hne2 Hupd.
      rewrite (Hupd x).
      exact: acc_upd2_neq.
    Qed.

  End State.



  (** Semantics *)

  Definition eval_unop (op : unop) (v : value) : value :=
    match op with
    | QNeg => (-v)%Z
    end.

  Definition eval_binop (op : binop) (v1 v2 : value) : value :=
    match op with
    | QAdd => (v1 + v2)%Z
    | QSub => (v1 - v2)%Z
    | QMul => (v1 * v2)%Z
    end.

  Fixpoint eval_exp (e : exp) (s : State.t) : value :=
    match e with
    | QVar v => State.acc v s
    | QConst n => n
    | QUnop op e => eval_unop op (eval_exp e s)
    | QBinop op e1 e2 => eval_binop op (eval_exp e1 s) (eval_exp e2 s)
    | QPow e p => (eval_exp e s) ^ (Zpos p)
    end.

  Definition eval_instr (s : State.t) (i : instr) : State.t :=
    match i with
    | QAssign v e => State.upd v (eval_exp e s) s
    | QSplit vh vl e i =>
      let (q, r) := Z.div_eucl (eval_exp e s) (2^(Zpos i)) in
      State.upd2 vh q vl r s
    end.

  Fixpoint eval_program (s : State.t) (p : program) : State.t :=
    match p with
    | [::] => s
    | hd::tl => eval_program (eval_instr s hd) tl
    end.

  Lemma eval_program_singleton :
    forall (i : instr) (s1 s2 : State.t),
      eval_program s1 ([:: i]) = s2 ->
      eval_instr s1 i = s2.
  Proof.
    move=> i s1 s2 H; assumption.
  Qed.

  Lemma eval_program_cons :
    forall (hd : instr) (tl : program) (s1 s2 : State.t),
      eval_program s1 (hd::tl) = s2 ->
      exists s3 : State.t,
        eval_instr s1 hd = s3 /\ eval_program s3 tl = s2.
  Proof.
    move=> hd tl s1 s2 H.
    exists (eval_instr s1 hd); split.
    - reflexivity.
    - assumption.
  Qed.

  Lemma eval_program_concat :
    forall (p1 p2 : program) (s1 s2 s3 : State.t),
      eval_program s1 p1 = s2 ->
      eval_program s2 p2 = s3 ->
      eval_program s1 (p1 ++ p2) = s3.
  Proof.
    move=> p1; elim: p1 => /=.
    - move=> p2 s1 s2 s3 He1 He2.
      by rewrite He1.
    - move=> hd tl H p2 s1 s2 s3 He1 He2.
      move: (eval_program_cons He1) => {He1} [s4 [He1 He4]].
      move: (H _ _ _ _ He4 He2) => Htlp2.
      rewrite He1; assumption.
  Qed.

  Lemma eval_program_split :
    forall (p1 p2 : program) (s1 s2 : State.t),
      eval_program s1 (p1 ++ p2) = s2 ->
      exists s3 : State.t,
        eval_program s1 p1 = s3 /\ eval_program s3 p2 = s2.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 s1 s2 H1.
      exists s1; split.
      + reflexivity.
      + exact: H1.
    - move=> hd tl H p2 s1 s2 He1.
      move: (eval_program_cons He1) => {He1} [s3 [He13 He32]].
      move: (H _ _ _ He32) => {H} [s4 [He34 He42]].
      exists s4; split.
      + rewrite /= He13.
        assumption.
      + exact: He42.
  Qed.

  (** Specification *)

  Inductive bexp : Type :=
  | QTrue : bexp
  | QEq : exp -> exp -> bexp
  | QCong : exp -> exp -> positive -> bexp
  | QAnd : bexp -> bexp -> bexp.

  Fixpoint vars_bexp (e : bexp) : VS.t :=
    match e with
    | QTrue => VS.empty
    | QEq e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | QCong e1 e2 _ => VS.union (vars_exp e1) (vars_exp e2)
    | QAnd e1 e2 => VS.union (vars_bexp e1) (vars_bexp e2)
    end.

  Fixpoint eval_bexp (e : bexp) (s : State.t) : Prop :=
    match e with
    | QTrue => True
    | QEq e1 e2 => eval_exp e1 s = eval_exp e2 s
    | QCong e1 e2 p => modulo (eval_exp e1 s) (eval_exp e2 s) (Zpos p)
    | QAnd e1 e2 => eval_bexp e1 s /\ eval_bexp e2 s
    end.

  Definition valid (f : bexp) : Prop :=
    forall s : State.t, eval_bexp f s.

  Definition entails (f g : bexp) : Prop :=
    forall s : State.t,
      eval_bexp f s -> eval_bexp g s.

  Record spec : Type :=
    mkSpec { spre : bexp;
             sprog : program;
             spost : bexp }.

  Definition valid_spec (s : spec) : Prop :=
    forall s1 s2,
      eval_bexp (spre s) s1 ->
      eval_program s1 (sprog s) = s2 ->
      eval_bexp (spost s) s2.

  Local Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity).
  Local Notation "f ===> g" := (entails f g) (at level 82, no associativity).
  Local Notation "{{ f }} p {{ g }}" :=
    ({| spre := f; sprog := p; spost := g |}) (at level 82).
  Local Notation "|= s" := (valid_spec s) (at level 83).

  Definition counterexample (sp : spec) (s : State.t) : Prop :=
    eval_bexp (spre sp) s /\
    exists s' : State.t,
      eval_program s (sprog sp) = s' /\ (~ eval_bexp (spost sp) s').

  Lemma spec_empty :
    forall f g,
      |= {{ f }} [::] {{ g }} -> f ===> g.
  Proof.
    move=> f g He s Hf.
    apply: (He s _ Hf).
    reflexivity.
  Qed.

  Lemma spec_strengthing :
    forall f g h p,
      entails f g -> |= {{ g }} p {{ h }} -> |= {{ f }} p {{ h }}.
  Proof.
    move=> f g h p Hfg Hgh s1 s2 Hf Hp.
    apply: (Hgh _ _ _ Hp).
    exact: (Hfg _ Hf).
  Qed.

  Lemma spec_weakening :
    forall f g h p,
      |= {{ f }} p {{ g }} -> g ===> h -> |= {{ f }} p {{ h }}.
  Proof.
    move=> f g h p Hfg Hgh s1 s2 Hf Hp.
    apply: Hgh.
    exact: (Hfg _ _ Hf Hp).
  Qed.

  Lemma spec_cons :
    forall f g h hd tl,
      |= {{ f }} [::hd] {{ g }} -> |= {{ g }} tl {{ h }} ->
      |= {{ f }} (hd::tl) {{ h }}.
  Proof.
    move=> f g h hd tl Hshd Hstl s1 s2 /= Hf Hp.
    move: (eval_program_cons Hp) => {Hp} [s3 [Hhd Htl]].
    apply: (Hstl _ _ _ Htl) => /=.
    apply: (Hshd _ _ _ Hhd) => /=.
    assumption.
  Qed.

  Lemma spec_split_post :
    forall f g1 g2 p,
      |= {{ f }} p {{ g1 }} ->
      |= {{ f }} p {{ g2 }} ->
      |= {{ f }} p {{ QAnd g1 g2 }}.
  Proof.
    move=> f g1 g2 p Hg1 Hg2 s1 s2 /= Hf Hp.
    move: (Hg1 s1 s2 Hf Hp) => /= {Hg1} Hg1.
    move: (Hg2 s1 s2 Hf Hp) => /= {Hg2} Hg2.
    exact: (conj Hg1 Hg2).
  Qed.



  (** Well-formed programs *)

  Definition lvals_instr (i : instr) : VS.t :=
    match i with
    | QAssign v _ => VS.singleton v
    | QSplit vh vl _ _ => VS.add vh (VS.singleton vl)
    end.

  Definition well_formed_instr (vs : VS.t) (i : instr) : bool :=
    match i with
    | QAssign v e => VS.subset (vars_exp e) vs
    | QSplit vh vl e p => VS.subset (vars_exp e) vs
    end.

  Fixpoint well_formed_program (vs : VS.t) (p : program) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      well_formed_instr vs hd &&
                        well_formed_program (VS.union (lvals_instr hd) vs) tl
    end.

End MakeQhasm.

Module Qhasm := MakeQhasm VarOrder.
Export Qhasm.

Notation "@- x" := (QNeg x) (at level 35, right associativity) : mqhasm_scope.
Notation "x @+ y" := (QBinop QAdd x y) (at level 50, left associativity) : mqhasm_scope.
Notation "x @- y" := (QBinop QSub x y)  (at level 50, left associativity) : mqhasm_scope.
Notation "x @* y" := (QBinop QMul x y)  (at level 40, left associativity) : mqhasm_scope.
Notation "x @^ y" := (QPow x y)  (at level 30, right associativity) : mqhasm_scope.
Notation "x @:= y" := (QAssign x y) (at level 70, no associativity) : mqhasm_scope.
Notation "x ++ y @:= z # p" := (QSplit x y z p) (at level 70, no associativity) : mqhasm_scope.
Notation "x @= y" := (QEq x y) (at level 70, no associativity) : mqhasm_scope.
Notation "x @= y 'mod' z" := (QCong x y z) (at level 70, y at next level, no associativity) : mqhasm_scope.
Notation "x @&& y" := (QAnd x y) (at level 70, no associativity) : mqhasm_scope.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : mqhasm_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : mqhasm_scope.
Notation "{{ f }} p {{ g }}" := ({| spre := f; sprog := p; spost := g |}) (at level 82, no associativity) : mqhasm_scope.
Notation "|= s" := (valid_spec s) (at level 83, no associativity) : mqhasm_scope.
