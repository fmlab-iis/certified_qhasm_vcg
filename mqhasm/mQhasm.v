
(** * Integer programs as mini Qhasm+ *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From Common Require Import ZAriths Var Store.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope mqhasm_scope with mqhasm.

Local Open Scope mqhasm_scope.



(** Syntax *)

Section Syntax.

  Inductive unop : Set :=
  | QNeg.

  Inductive binop : Set :=
  | QAdd
  | QSub
  | QMul.

  Inductive exp : Set :=
  | QVar : var -> exp
  | QConst : Z -> exp
  | QUnop : unop -> exp -> exp
  | QBinop : binop -> exp -> exp -> exp.

  Inductive instr : Set :=
  | QAssign : var -> exp -> instr
  | QSplit : var -> var -> exp -> positive -> instr.

  Definition program : Set := seq instr.

End Syntax.



(** Semantics *)

Notation value := Z.

Module State.

  Definition t : Type := VStore.t value.

  Definition empty : t := VStore.empty value.

  Definition acc (x : var) (s : t) : option value :=
    VStore.acc x s.

  Definition upd (x : var) (v : value) (s : t) : t :=
    VStore.upd x v s.

  Definition unset (x : var) (s : t) : t :=
    VStore.unset x s.

  Lemma acc_upd_eq :
    forall x y v (s : t),
      x == y ->
      acc x (upd y v s) = Some v.
  Proof.
    exact: VStore.acc_upd_eq.
  Qed.

  Lemma acc_upd_neq :
    forall x y v (s : t),
      x != y ->
      acc x (upd y v s) = acc x s.
  Proof.
    exact: VStore.acc_upd_neq.
  Qed.

  Lemma acc_empty :
    forall x, acc x empty = None.
  Proof.
    exact: VStore.acc_empty.
  Qed.

  Lemma acc_unset_eq :
    forall x y s,
      x == y ->
      acc x (unset y s) = None.
  Proof.
    exact: VStore.acc_unset_eq.
  Qed.

  Lemma acc_unset_neq :
    forall x y s,
      x != y ->
      acc x (unset y s) = acc x s.
  Proof.
    exact: VStore.acc_unset_neq.
  Qed.

  Definition Upd x v (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (upd x v s1).

  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (upd x1 v1 (upd x2 v2 s1)).

  Definition Unset x (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (unset x s1).

  Lemma Upd_upd :
    forall x v s,
      Upd x v s (upd x v s).
  Proof.
    exact: VStore.Upd_upd.
  Qed.

  Lemma Upd2_upd :
    forall x1 v1 x2 v2 s,
      Upd2 x1 v1 x2 v2 s (upd x1 v1 (upd x2 v2 s)).
  Proof.
    move=> x1 v1 x2 v2 s y.
    reflexivity.
  Qed.

  Lemma Unset_unset :
    forall x s,
      Unset x s (unset x s).
  Proof.
    exact: VStore.Unset_unset.
  Qed.

  Lemma acc_Upd_eq :
    forall x y v s1 s2,
      x == y ->
      Upd y v s1 s2 ->
      acc x s2 = Some v.
  Proof.
    exact: VStore.acc_Upd_eq.
  Qed.

  Lemma acc_Upd_neq :
    forall x y v s1 s2,
      x != y ->
      Upd y v s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    exact: VStore.acc_Upd_neq.
  Qed.

  Lemma acc_Upd2_eq1 :
    forall x y1 v1 y2 v2 s1 s2,
      x == y1 ->
      Upd2 y1 v1 y2 v2 s1 s2 ->
      acc x s2 = Some v1.
  Proof.
    move=> x y1 v1 y2 v2 s1 s2 Heq Hupd.
    exact: (acc_Upd_eq Heq Hupd).
  Qed.

  Lemma acc_Upd2_eq2 :
    forall x y1 v1 y2 v2 s1 s2,
      x != y1 ->
      x == y2 ->
      Upd2 y1 v1 y2 v2 s1 s2 ->
      acc x s2 = Some v2.
  Proof.
    move=> x y1 v1 y2 v2 s1 s2 Hne Heq Hupd.
    rewrite (Hupd x).
    rewrite (acc_upd_neq _ _ Hne).
    rewrite (acc_upd_eq _ _ Heq).
    reflexivity.
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
    rewrite (acc_upd_neq _ _ Hne1).
    rewrite (acc_upd_neq _ _ Hne2).
    reflexivity.
  Qed.

  Lemma acc_Unset_eq :
    forall x y s1 s2,
      x == y ->
      Unset y s1 s2 ->
      acc x s2 = None.
  Proof.
    exact: VStore.acc_Unset_eq.
  Qed.

  Lemma acc_Unset_neq :
    forall x y s1 s2,
      x != y ->
      Unset y s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    exact: VStore.acc_Unset_neq.
  Qed.

End State.

Section Semantics.

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

  Inductive eval_exp : exp -> value -> State.t -> Prop :=
  | EQVar :
      forall v n s,
        State.acc v s = Some n ->
        eval_exp (QVar v) n s
  | EQConst : forall n s, eval_exp (QConst n) n s
  | EQUnop :
      forall op e n m s,
        eval_exp e n s ->
        eval_unop op n = m ->
        eval_exp (QUnop op e) m s
  | EQBinop :
      forall op e1 e2 v1 v2 n s,
        eval_exp e1 v1 s ->
        eval_exp e2 v2 s ->
        eval_binop op v1 v2 = n ->
        eval_exp (QBinop op e1 e2) n s.

  Inductive eval_instr : State.t -> instr -> State.t -> Prop :=
  | EQAssign :
      forall v e n s1 s2,
        eval_exp e n s1 ->
        State.Upd v n s1 s2 ->
        eval_instr s1 (QAssign v e) s2
  | EQSplit :
      forall v1 v2 e i n1 n2 n s1 s2,
        eval_exp e n s1 ->
        State.Upd2 v1 n1 v2 n2 s1 s2 ->
        (n1 * 2^(Zpos i) + n2 = n)%Z ->
        eval_instr s1 (QSplit v1 v2 e i) s2.

  Inductive eval_program : State.t -> program -> State.t -> Prop :=
  | EQEmpty : forall s, eval_program s nil s
  | EQCons :
      forall hd tl s1 s2 s3,
        eval_instr s1 hd s2 ->
        eval_program s2 tl s3 ->
        eval_program s1 (hd::tl) s3.

  Lemma eval_qvar_unique v n m s :
    let e := QVar v in
    eval_exp e n s -> eval_exp e m s -> n == m.
  Proof.
    move=> e Hn Hm.
    inversion_clear Hn.
    inversion_clear Hm.
    move: H H0; case: (State.acc v s).
    + move=> u [] Hun [] Hum.
      rewrite -Hun -Hum; exact: eqxx.
    + discriminate.
  Qed.

  Lemma eval_qconst_unique v n m s :
    let e := QConst v in
    eval_exp e n s -> eval_exp e m s -> n == m.
  Proof.
    move=> e Hn Hm.
    have: (v = n /\ v = m).
    - split.
      + inversion_clear Hn.
        reflexivity.
      + inversion_clear Hm.
        reflexivity.
    - move=> [] Hvn Hvm; rewrite -Hvn -Hvm; exact: eqxx.
  Qed.

  Lemma eval_qunop_unique :
    forall (op : unop) (e : exp),
      (forall (n m : value) (s : State.t),
          eval_exp e n s -> eval_exp e m s -> n == m) ->
      forall (n m : value) (s : State.t),
        eval_exp (QUnop op e) n s ->
        eval_exp (QUnop op e) m s ->
        n == m.
  Proof.
    move=> op e Hind n m s Hn Hm.
    inversion_clear Hn.
    inversion_clear Hm.
    move: (Hind _ _ _ H H1) => {H H1} H01.
    rewrite -H0 -H2 (eqP H01).
    exact: eqxx.
  Qed.

  Lemma eval_qbinop_unique :
    forall (op : binop) (e1 : exp),
      (forall (n m : value) (s : State.t),
          eval_exp e1 n s -> eval_exp e1 m s -> n == m) ->
      forall e2 : exp,
        (forall (n m : value) (s : State.t),
            eval_exp e2 n s -> eval_exp e2 m s -> n == m) ->
        forall (n m : value) (s : State.t),
          eval_exp (QBinop op e1 e2) n s ->
          eval_exp (QBinop op e1 e2) m s ->
          n == m.
  Proof.
    move=> op e1 Hind1 e2 Hind2 n m s Hn Hm.
    inversion_clear Hn.
    inversion_clear Hm.
    move: (Hind1 _ _ _ H H2) => {H H2} => H10.
    move: (Hind2 _ _ _ H0 H3) => {H0 H3} => H23.
    rewrite -H1 -H4 (eqP H10) (eqP H23).
    exact: eqxx.
  Qed.

  Lemma eval_exp_unique :
    forall e n m s, eval_exp e n s -> eval_exp e m s -> n == m.
  Proof.
    move=> e; elim: e.
    - exact: eval_qvar_unique.
    - exact: eval_qconst_unique.
    - exact: eval_qunop_unique.
    - exact: eval_qbinop_unique.
  Qed.

  Lemma eval_program_empty :
    forall (s1 s2 : State.t),
      eval_program s1 [::] s2 -> s1 = s2.
  Proof.
    move=> s1 s2 H; by inversion_clear H.
  Qed.

  Lemma eval_program_singleton :
    forall (i : instr) (s1 s2 : State.t),
      eval_program s1 ([:: i]) s2 ->
      eval_instr s1 i s2.
  Proof.
    move=> i s1 s2 H; inversion_clear H.
    move: (eval_program_empty H1) => {H1} H1.
    rewrite -H1.
    exact: H0.
  Qed.

  Lemma eval_program_cons :
    forall (hd : instr) (tl : program) (s1 s2 : State.t),
      eval_program s1 (hd::tl) s2 ->
      exists s3 : State.t,
        eval_instr s1 hd s3 /\ eval_program s3 tl s2.
  Proof.
    move=> hd tl s1 s2 H.
    inversion_clear H.
    exists s3; split; assumption.
  Qed.

  Lemma eval_program_concat :
    forall (p1 p2 : program) (s1 s2 s3 : State.t),
      eval_program s1 p1 s2 ->
      eval_program s2 p2 s3 ->
      eval_program s1 (p1 ++ p2) s3.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 s1 s2 s3 He1 He2.
      move: (eval_program_empty He1) => {He1} He1.
      rewrite He1.
      exact: He2.
    - move=> hd tl H p2 s1 s2 s3 He1 He2.
      move: (eval_program_cons He1) => {He1} [s4 [He1 He4]].
      apply: (EQCons He1).
      apply: (H _ _ _ _ He4).
      exact: He2.
  Qed.

  Lemma eval_program_split :
    forall (p1 p2 : program) (s1 s2 : State.t),
      eval_program s1 (p1 ++ p2) s2 ->
      exists s3 : State.t,
        eval_program s1 p1 s3 /\ eval_program s3 p2 s2.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 s1 s2 H1.
      exists s1; split.
      + exact: EQEmpty.
      + exact: H1.
    - move=> hd tl H p2 s1 s2 He1.
      move: (eval_program_cons He1) => {He1} [s3 [He13 He32]].
      move: (H _ _ _ He32) => {H} [s4 [He34 He42]].
      exists s4; split.
      + exact: (EQCons He13 He34).
      + exact: He42.
  Qed.

End Semantics.



(** Specification *)

Section Specification.

  Inductive bexp : Set :=
  | QEq : exp -> exp -> bexp
  | QCong : exp -> exp -> positive -> bexp
  | QAnd : bexp -> bexp -> bexp.

  Inductive eval_bexp : bexp -> bool -> State.t -> Prop :=
  | EQEq :
      forall e1 e2 n1 n2 s,
        eval_exp e1 n1 s ->
        eval_exp e2 n2 s ->
        eval_bexp (QEq e1 e2) (n1 == n2) s
  | EQCong :
      forall e1 e2 n1 n2 p s,
        eval_exp e1 n1 s ->
        eval_exp e2 n2 s ->
        eval_bexp (QCong e1 e2 p) (n1 === n2 # (Zpos p)) s
  | EQAnd :
      forall e1 e2 b1 b2 s,
        eval_bexp e1 b1 s ->
        eval_bexp e2 b2 s ->
        eval_bexp (QAnd e1 e2) (b1 && b2) s.

  Definition valid (f : bexp) : Prop :=
    forall s : State.t, eval_bexp f true s.

  Definition entails (f g : bexp) : Prop :=
    forall s : State.t,
      eval_bexp f true s -> eval_bexp g true s.

  Definition spec (f : bexp) (p : program) (g : bexp) : Prop :=
    forall s1 s2,
      eval_bexp f true s1 ->
      eval_program s1 p s2 ->
      eval_bexp g true s2.

  Definition counterexample (f : bexp) (p : program) (g : bexp) (s : State.t) : Prop :=
    eval_bexp f true s /\
    exists s' : State.t, eval_program s p s' /\ eval_bexp g false s'.

  Lemma spec_empty :
    forall f g,
      spec f [::] g -> entails f g.
  Proof.
    move=> f g He s Hf.
    apply: (He s _ Hf).
    apply: EQEmpty.
  Qed.

  Lemma spec_strengthing :
    forall f g h p,
      entails f g -> spec g p h -> spec f p h.
  Proof.
    move=> f g h p Hfg Hgh s1 s2 Hf Hp.
    apply: (Hgh _ _ _ Hp).
    exact: (Hfg _ Hf).
  Qed.

  Lemma spec_weakening :
    forall f g h p,
      spec f p g -> entails g h -> spec f p h.
  Proof.
    move=> f g h p Hfg Hgh s1 s2 Hf Hp.
    apply: Hgh.
    exact: (Hfg _ _ Hf Hp).
  Qed.

  Lemma spec_cons :
    forall f g h hd tl,
      spec f [::hd] g -> spec g tl h ->
      spec f (hd::tl) h.
  Proof.
    move=> f g h hd tl Hhd Htl s1 s2 Hf Hp.
    inversion_clear Hp.
    apply: (Htl s3 _ _ H0).
    apply: (Hhd s1 _ Hf).
    apply: (EQCons H).
    exact: EQEmpty.
  Qed.

  Lemma spec_split_post :
    forall f g1 g2 p,
      spec f p g1 ->
      spec f p g2 ->
      spec f p (QAnd g1 g2).
  Proof.
    move=> f g1 g2 p Hg1 Hg2 s1 s2 Hf Hp.
    move: (Hg1 s1 s2 Hf Hp) => {Hg1} Hg1.
    move: (Hg2 s1 s2 Hf Hp) => {Hg2} Hg2.
    exact: (EQAnd Hg1 Hg2).
  Qed.

End Specification.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : iprog_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : iprog_scope.
Notation "{{ f }} p {{ g }}" := (spec f p g) (at level 82, no associativity) : iprog_scope.
