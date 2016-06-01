
(** * Sequential integer programs *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From Common Require Import ZRing Env Var Store.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope iprog_scope with iprog.

Local Open Scope iprog_scope.



(** Syntax *)

Section Syntax.

  Variable E : SEnv.t.
  Notation pvar := (SEnv.pvar E).

  Inductive unop : Set :=
  | INeg.

  Inductive binop : Set :=
  | IAdd
  | ISub
  | IMul
  | IDiv
  | IMod.

  Inductive exp : Set :=
  | IVar : pvar -> exp
  | IConst : Z -> exp
  | IUnop : unop -> exp -> exp
  | IBinop : binop -> exp -> exp -> exp.

  Inductive instr : Set :=
  | IAssign : pvar -> exp -> instr.

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

  Definition Unset x (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (unset x s1).

  Lemma Upd_upd :
    forall x v s,
      Upd x v s (upd x v s).
  Proof.
    exact: VStore.Upd_upd.
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

  Variable E : SEnv.t.
  Notation pvar_var := (SEnv.pvar_var).

  Definition eval_unop (op : unop) (v : value) : value :=
    match op with
    | INeg => (-v)%Z
    end.

  Definition eval_binop (op : binop) (v1 v2 : value) : value :=
    match op with
    | IAdd => (v1 + v2)%Z
    | ISub => (v1 - v2)%Z
    | IMul => (v1 * v2)%Z
    | IDiv => (v1 / v2)%Z
    | IMod => (v1 mod v2)%Z
    end.

  Inductive eval_exp : exp E -> value -> State.t -> Prop :=
  | EIVar :
      forall v n s,
        State.acc (pvar_var v) s = Some n ->
        eval_exp (IVar v) n s
  | EIConst : forall n s, eval_exp (IConst E n) n s
  | EIUnop :
      forall op e n m s,
        eval_exp e n s ->
        eval_unop op n = m ->
        eval_exp (IUnop op e) m s
  | EIBinop :
      forall op e1 e2 v1 v2 n s,
        eval_exp e1 v1 s ->
        eval_exp e2 v2 s ->
        eval_binop op v1 v2 = n ->
        eval_exp (IBinop op e1 e2) n s.

  Inductive eval_instr : State.t -> instr E -> State.t -> Prop :=
  | EIAssign :
      forall v e n s1 s2,
        eval_exp e n s1 ->
        State.Upd (pvar_var v) n s1 s2 ->
        eval_instr s1 (IAssign v e) s2.

  Inductive eval_program : State.t -> program E -> State.t -> Prop :=
  | EIEmpty : forall s, eval_program s nil s
  | EICons :
      forall hd tl s1 s2 s3,
        eval_instr s1 hd s2 ->
        eval_program s2 tl s3 ->
        eval_program s1 (hd::tl) s3.

  Lemma eval_ivar_unique v n m s :
    let e := IVar v in
    eval_exp e n s -> eval_exp e m s -> n == m.
  Proof.
    move=> e Hn Hm.
    inversion_clear Hn.
    inversion_clear Hm.
    move: H H0; case: (State.acc (pvar_var v) s).
    + move=> u [] Hun [] Hum.
      rewrite -Hun -Hum; exact: eqxx.
    + discriminate.
  Qed.

  Lemma eval_iconst_unique v n m s :
    let e := IConst E v in
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

  Lemma eval_iunop_unique :
    forall (op : unop) (e : exp E),
      (forall (n m : value) (s : State.t),
          eval_exp e n s -> eval_exp e m s -> n == m) ->
      forall (n m : value) (s : State.t),
        eval_exp (IUnop op e) n s ->
        eval_exp (IUnop op e) m s ->
        n == m.
  Proof.
    move=> op e Hind n m s Hn Hm.
    inversion_clear Hn.
    inversion_clear Hm.
    move: (Hind _ _ _ H H1) => {H H1} H01.
    rewrite -H0 -H2 (eqP H01).
    exact: eqxx.
  Qed.

  Lemma eval_ibinop_unique :
    forall (op : binop) (e1 : exp E),
      (forall (n m : value) (s : State.t),
          eval_exp e1 n s -> eval_exp e1 m s -> n == m) ->
      forall e2 : exp E,
        (forall (n m : value) (s : State.t),
            eval_exp e2 n s -> eval_exp e2 m s -> n == m) ->
        forall (n m : value) (s : State.t),
          eval_exp (IBinop op e1 e2) n s ->
          eval_exp (IBinop op e1 e2) m s ->
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
    - exact: eval_ivar_unique.
    - exact: eval_iconst_unique.
    - exact: eval_iunop_unique.
    - exact: eval_ibinop_unique.
  Qed.

  Lemma eval_program_empty :
    forall (s1 s2 : State.t),
      eval_program s1 [::] s2 -> s1 = s2.
  Proof.
    move=> s1 s2 H; by inversion_clear H.
  Qed.

  Lemma eval_program_singleton :
    forall (i : instr E) (s1 s2 : State.t),
      eval_program s1 ([:: i]) s2 ->
      eval_instr s1 i s2.
  Proof.
    move=> i s1 s2 H; inversion_clear H.
    move: (eval_program_empty H1) => {H1} H1.
    rewrite -H1.
    exact: H0.
  Qed.

  Lemma eval_program_cons :
    forall (hd : instr E) (tl : program E) (s1 s2 : State.t),
      eval_program s1 (hd::tl) s2 ->
      exists s3 : State.t,
        eval_instr s1 hd s3 /\ eval_program s3 tl s2.
  Proof.
    move=> hd tl s1 s2 H.
    inversion_clear H.
    exists s3; split; assumption.
  Qed.

  Lemma eval_program_concat :
    forall (p1 p2 : program E) (s1 s2 s3 : State.t),
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
      apply: (EICons He1).
      apply: (H _ _ _ _ He4).
      exact: He2.
  Qed.

  Lemma eval_program_split :
    forall (p1 p2 : program E) (s1 s2 : State.t),
      eval_program s1 (p1 ++ p2) s2 ->
      exists s3 : State.t,
        eval_program s1 p1 s3 /\ eval_program s3 p2 s2.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 s1 s2 H1.
      exists s1; split.
      + exact: EIEmpty.
      + exact: H1.
    - move=> hd tl H p2 s1 s2 He1.
      move: (eval_program_cons He1) => {He1} [s3 [He13 He32]].
      move: (H _ _ _ He32) => {H} [s4 [He34 He42]].
      exists s4; split.
      + exact: (EICons He13 He34).
      + exact: He42.
  Qed.

End Semantics.



(** Specification *)

Section Specification.

  Variable E : SEnv.t.

  Inductive cop : Set :=
  | IEq
  | ILt
  | ILe
  | IGt
  | IGe.

  Inductive bexp : Set :=
  | IComp : cop -> exp E -> exp E -> bexp
  | INot : bexp -> bexp
  | IAnd : bexp -> bexp -> bexp
  | IOr : bexp -> bexp -> bexp.

  Definition eval_cop op (v1 v2 : value) : bool :=
    match op with
    | IEq => v1 == v2
    | ILt => (v1 <? v2)%Z
    | ILe => (v1 <=? v2)%Z
    | IGt => (v1 >? v2)%Z
    | IGe => (v1 >=? v2)%Z
    end.

  Inductive eval_bexp : bexp -> bool -> State.t -> Prop :=
  | EIComp :
      forall op e1 e2 n1 n2 s,
        eval_exp e1 n1 s ->
        eval_exp e2 n2 s ->
        eval_bexp (IComp op e1 e2) (eval_cop op n1 n2) s
  | EINot :
      forall e b s,
        eval_bexp e b s ->
        eval_bexp (INot e) (~~b) s
  | EIAnd :
      forall e1 e2 b1 b2 s,
        eval_bexp e1 b1 s ->
        eval_bexp e2 b2 s ->
        eval_bexp (IAnd e1 e2) (b1 && b2) s
  | EIOr :
      forall e1 e2 b1 b2 s,
        eval_bexp e1 b1 s ->
        eval_bexp e2 b2 s ->
        eval_bexp (IOr e1 e2) (b1 || b2) s.

  Definition valid (f : bexp) : Prop :=
    forall s : State.t, eval_bexp f true s.

  Definition entails (f g : bexp) : Prop :=
    forall s : State.t,
      eval_bexp f true s -> eval_bexp g true s.

  Definition spec (f : bexp) (p : program E) (g : bexp) : Prop :=
    forall s1 s2,
      eval_bexp f true s1 ->
      eval_program s1 p s2 ->
      eval_bexp g true s2.

  Definition counterexample (f : bexp) (p : program E) (g : bexp) (s : State.t) : Prop :=
    eval_bexp f true s /\
    exists s' : State.t, eval_program s p s' /\ eval_bexp g false s'.

  Lemma spec_empty :
    forall f g,
      spec f [::] g -> entails f g.
  Proof.
    move=> f g He s Hf.
    apply: (He s _ Hf).
    apply: EIEmpty.
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
    apply: (EICons H).
    exact: EIEmpty.
  Qed.

End Specification.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : iprog_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : iprog_scope.
Notation "{{ f }} p {{ g }}" := (spec f p g) (at level 82, no associativity) : iprog_scope.



(*
Fixpoint eval_exp E (e : exp E) (s : State.t) : value :=
  match e with
  | SVar v => State.acc (pvar_var v) s
  | SConst n => Some n
  | SUnop op e' => eval_unop op (eval_exp e' s)
  | SBinop op e1 e2 => eval_binop op (eval_exp e1 s) (eval_exp e2 s)
  end.

Definition eval_instr (i : instr) (s : State.t) : State.t :=
  match i with
  | SAssign v e => State.upd v (eval_exp e s) s
  end.

Fixpoint eval_program (p : program) (s : State.t) : State.t :=
  match p with
  | nil => s
  | hd::tl => eval_program tl (eval_instr hd s)
  end.
*)