
(** * MiniQhasm+ for AMD64 *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From CompCert Require Import Integers.
From Common Require Import ZAriths Env Var Store Integers.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope qhasm_scope with qhasm.



(** Syntax *)

Section Syntax.

  Variable E : SEnv.t.
  Notation pvar := (SEnv.pvar E).

  (* Constants *)
  Definition const : Set := int64.

  (* Atomics can be variables or constants. *)
  Inductive atomic : Set :=
  | QVar : pvar -> atomic
  | QConst : const -> atomic.

  (* Instructions.
   Below is the list of instructions:
   - QAssign r s: r = s
   - QAdd r s t: r = s + t
   - QAddC r s t: r = s + t + carry
   - QAdc r s t: carry? r = s + t
   - QAdcC r s t: carry? r = s + t + carry
   - QSub r s t: r = s - t
   - QSubC r s t: r = s - t - carry
   - QSbb r s t: carry? r = s - t
   - QSbbC r s t: carry? r = s - t - carry
   - QMul r s t: r = s * t
   - QMulf r s t u: r s = t * u
   - QShl r s n: r = s $<<$#&lt;&lt;# n
   - QShr r s n: r = s $>>$#&gt;&gt;# n
   - QMod2n r s n: r = s $\%$#%# 2%\textasciicircum%#^#n
   *)
  Inductive instr : Set :=
  | QAssign : pvar -> atomic -> instr
  | QAdd : pvar -> atomic -> atomic -> instr
  | QAddC : pvar -> atomic -> atomic -> instr
  | QAdc : pvar -> atomic -> atomic -> instr
  | QAdcC : pvar -> atomic -> atomic -> instr
  | QSub : pvar -> atomic -> atomic -> instr
  | QSubC : pvar -> atomic -> atomic -> instr
  | QSbb : pvar -> atomic -> atomic -> instr
  | QSbbC : pvar -> atomic -> atomic -> instr
  | QMul : pvar -> atomic -> atomic -> instr
  | QMulf : pvar -> pvar -> atomic -> atomic -> instr
  | QShl : pvar -> atomic -> nat -> instr
  | QShr : pvar -> atomic -> nat -> instr
  | QMod2n : pvar -> atomic -> nat -> instr.

  Definition program : Set := seq instr.

End Syntax.



(** Values *)

Definition value : Set := int64.

Definition ctoZ c := if c then 1%Z else 0%Z.

Definition add_carry n m := Int64.add_carry n m Int64.zero == Int64.one.



(** States *)

Module State.

  Record t : Type :=
    mkState { store: VStore.t value;
              carry: option bool }.

  Definition empty : t :=
    {| store := VStore.empty value;
       carry := None |}.

  Definition acc (x : var) (s : t) : option value :=
    VStore.acc x (store s).

  Definition upd (x : var) (v : value) (s : t) : t :=
    {| store := VStore.upd x v (store s);
       carry := carry s |}.

  Definition set_carry c (s : t) : t :=
    {| store := store s;
       carry := Some c |}.

  Definition reset_carry (s : t) : t :=
    {| store := store s;
       carry := None |}.

  Lemma acc_upd_eq :
    forall x y v s,
      x == y ->
      acc x (upd y v s) = Some v.
  Proof.
    rewrite /acc /upd => x y v s Hxy.
    exact: VStore.acc_upd_eq.
  Qed.

  Lemma acc_upd_neq :
    forall x y v s,
      x != y ->
      acc x (upd y v s) = acc x s.
  Proof.
    rewrite /acc /upd => x y v s Hxy.
    exact: VStore.acc_upd_neq.
  Qed.

  Lemma acc_empty :
    forall x,
      acc x empty = None.
  Proof.
    rewrite /acc => x.
    exact: VStore.acc_empty.
  Qed.

  Definition Upd x v s1 s2 : Prop :=
    (forall y, acc y s2 = acc y (upd x v s1)) /\
    carry s1 = carry s2.

  Definition Carry c s1 s2 : Prop :=
    (forall x, acc x s2 = acc x s1) /\
    carry s2 = c.

  Lemma Upd_upd :
    forall x v s,
      Upd x v s (upd x v s).
  Proof.
    move=> x v s.
    split.
    - exact: VStore.Upd_upd.
    - reflexivity.
  Qed.

  Lemma acc_Upd_eq :
    forall x y v s1 s2,
      x == y ->
      Upd y v s1 s2 ->
      acc x s2 = Some v.
  Proof.
    move=> x y v s1 s2 Hxy [Hupd _].
    exact: (VStore.acc_Upd_eq Hxy Hupd).
  Qed.

  Lemma acc_Upd_neq :
    forall x y v s1 s2,
      x != y ->
      Upd y v s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    move=> x y v s1 s2 Hxy [Hupd _].
    exact: (VStore.acc_Upd_neq Hxy Hupd).
  Qed.

  Lemma acc_Carry :
    forall c x s1 s2,
      Carry c s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    move=> c x s1 s2 [Hv Hc].
    exact: Hv.
  Qed.

  Lemma Carry_carry :
    forall c s1 s2,
      Carry c s1 s2 ->
      carry s2 = c.
  Proof.
    move=> c s1 s2 [_ Hc].
    exact: Hc.
  Qed.

End State.



(** Semantics *)

Section Semantics.

  Variable E : SEnv.t.
  Notation pvar_var := SEnv.pvar_var.

  Inductive eval_atomic : atomic E -> value -> State.t -> Prop :=
  | EQVar :
      forall v n st,
        State.acc (pvar_var v) st = Some n ->
        eval_atomic (QVar v) n st
  | EQConst :
      forall n st,
        eval_atomic (QConst E n) n st.

  Inductive eval_instr : State.t -> instr E -> State.t -> Prop :=
  | EQAssign :
      forall r s vs s1 s2,
        eval_atomic s vs s1 ->
        State.Upd (pvar_var r) vs s1 s2 ->
        eval_instr s1 (QAssign r s) s2
  | EQAdd : (* tbd *)
      forall r s t st,
        eval_instr st (QAdd r s t) st
  | EQAddC : (* tbd *)
      forall r s t st,
        eval_instr st (QAddC r s t) st
  | EQAdc :
      forall r s t vs vt s1 s2 s3,
        let v := Int64.add vs vt in
        let c := add_carry vs vt in
        eval_atomic s vs s1 ->
        eval_atomic t vt s1 ->
        State.Upd (pvar_var r) v s1 s2 ->
        State.Carry (Some c) s2 s3 ->
        eval_instr s1 (QAdc r s t) s3
  | EQAdcC : (* tbd *)
      forall r s t st,
        eval_instr st (QAdcC r s t) st
  | EQSub : (* tbd *)
      forall r s t st,
        eval_instr st (QSub r s t) st
  | EQSubC : (* tbd *)
      forall r s t st,
        eval_instr st (QSubC r s t) st
  | EQSbb : (* tbd *)
      forall r s t st,
        eval_instr st (QSbb r s t) st
  | EQSbbC : (* tbd *)
      forall r s t st,
        eval_instr st (QSbbC r s t) st
  | EQMul : (* tbd *)
      forall r s t st,
        eval_instr st (QMul r s t) st
  | EQMulf : (* tbd *)
      forall r s t u st,
        eval_instr st (QMulf r s t u) st
  | EQShl : (* tbd *)
      forall r s n st,
        eval_instr st (QShl r s n) st
  | EQShr : (* tbd *)
      forall r s n st,
        eval_instr st (QShr r s n) st
  | EQMod2n : (* tbd *)
      forall r s n st,
        eval_instr st (QMod2n r s n) st.

  Inductive eval_program : State.t -> program E -> State.t -> Prop :=
  | EQEmpty : forall st, eval_program st nil st
  | EQCons :
      forall hd tl st1 st2 st3,
        eval_instr st1 hd st2 ->
        eval_program st2 tl st3 ->
        eval_program st1 (hd::tl) st3.

  Lemma eval_program_empty :
    forall (st1 st2 : State.t),
      eval_program st1 [::] st2 -> st1 = st2.
  Proof.
    move=> st1 st2 H; by inversion_clear H.
  Qed.

  Lemma eval_program_singleton :
    forall (i : instr E) (st1 st2 : State.t),
      eval_program st1 ([:: i]) st2 ->
      eval_instr st1 i st2.
  Proof.
    move=> i st1 st2 H; inversion_clear H.
    move: (eval_program_empty H1) => {H1} H1.
    rewrite -H1.
    exact: H0.
  Qed.

  Lemma eval_program_cons :
    forall (hd : instr E) (tl : program E) (st1 st2 : State.t),
      eval_program st1 (hd::tl) st2 ->
      exists st3 : State.t,
        eval_instr st1 hd st3 /\ eval_program st3 tl st2.
  Proof.
    move=> hd tl st1 st2 H.
    inversion_clear H.
    exists st3; split; assumption.
  Qed.

  Lemma eval_program_concat :
    forall (p1 p2 : program E) (st1 st2 st3 : State.t),
      eval_program st1 p1 st2 ->
      eval_program st2 p2 st3 ->
      eval_program st1 (p1 ++ p2) st3.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 st1 st2 st3 H1 H2.
      move: (eval_program_empty H1) => {H1} H1.
      rewrite H1.
      exact: H2.
    - move=> hd tl H p2 st1 st2 st3 H1 H2.
      move: (eval_program_cons H1) => {H1} [st4 [H1 H4]].
      apply: (EQCons H1).
      apply: (H _ _ _ _ H4).
      exact: H2.
  Qed.

  Lemma eval_program_split :
    forall (p1 p2 : program E) (st1 st2 : State.t),
      eval_program st1 (p1 ++ p2) st2 ->
      exists st3 : State.t,
        eval_program st1 p1 st3 /\ eval_program st3 p2 st2.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 st1 st2 H1.
      exists st1; split.
      + exact: EQEmpty.
      + exact: H1.
    - move=> hd tl H p2 st1 st2 H1.
      move: (eval_program_cons H1) => {H1} [st3 [H13 H32]].
      move: (H _ _ _ H32) => {H} [st4 [H34 H42]].
      exists st4; split.
      + exact: (EQCons H13 H34).
      + exact: H42.
  Qed.

End Semantics.



(** Uncaught carry *)

Section Safety.

  Variable E : SEnv.t.

  (* Detect if an instruction will cause uncaught carry. *)
  Inductive instr_safe : instr E -> State.t -> Prop :=
  | SQAssign : forall r s st, instr_safe (QAssign r s) st
  | SQAdd :
      forall r s t vs vt st,
        eval_atomic s vs st ->
        eval_atomic t vt st ->
        ~~ add_carry vs vt ->
        instr_safe (QAdd r s t) st.

  Inductive program_safe : program E -> State.t -> Prop :=
  | SQEmpty : forall st : State.t, program_safe [::] st
  | SQCons :
      forall hd tl st,
        instr_safe hd st ->
        (forall st' : State.t, eval_instr st hd st' -> program_safe tl st') ->
        program_safe (hd::tl) st.

  Lemma program_safe_hd :
    forall (hd : instr E) (tl : program E) (s : State.t),
      program_safe (hd::tl) s ->
      instr_safe hd s.
  Proof.
    move=> hd tl s H.
    inversion_clear H.
    exact: H0.
  Qed.

  Lemma program_safe_tl :
    forall (hd : instr E) (tl : program E) (st1 st2 : State.t),
      program_safe (hd::tl) st1 ->
      eval_instr st1 hd st2 ->
      program_safe tl st2.
  Proof.
    move=> hd tl st1 st2 H Hi.
    inversion_clear H.
    exact: (H1 _ Hi).
  Qed.

  Lemma program_safe_split :
    forall (p1 p2 : program E) (st1 : State.t),
      program_safe p1 st1 ->
      (forall st2 : State.t,
          eval_program st1 p1 st2 -> program_safe p2 st2) ->
      program_safe (p1 ++ p2) st1.
  Proof.
    move=> p1; elim: p1.
    - move=> p2 st1 Hs1 Hs2.
      apply: Hs2.
      exact: EQEmpty.
    - move=> hd tl H p2 st1 Hs1 Hs2.
      apply: SQCons.
      + exact: (program_safe_hd Hs1).
      + move=> st3 He1.
        move: (program_safe_tl Hs1 He1) => Hs3.
        apply: (H _ _ Hs3).
        move=> st4 He3.
        apply: Hs2.
        exact: (EQCons He1 He3).
  Qed.

End Safety.



(** Specification *)

Section Specification.

  Variable E : SEnv.t.
  Notation pvar := (SEnv.pvar E).
  Notation pvar_var := SEnv.pvar_var.
  Notation value := Z.

  Inductive unop : Set :=
  | ONeg.

  Inductive binop : Set :=
  | OAdd
  | OSub
  | OMul
  | ODiv
  | OMod.

  Inductive exp : Set :=
  | EVar : pvar -> exp
  | EConst : Z -> exp
  | ECarry : exp
  | EUnop : unop -> exp -> exp
  | EBinop : binop -> exp -> exp -> exp.

  Inductive cop : Set :=
  | CEq
  | CLt
  | CLe
  | CGt
  | CGe.

  Inductive bexp : Set :=
  | BComp : cop -> exp -> exp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp.

  Definition eval_unop (op : unop) (v : value) : value :=
    match op with
    | ENeg => (-v)%Z
    end.

  Definition eval_binop (op : binop) (v1 v2 : value) : value :=
    match op with
    | OAdd => (v1 + v2)%Z
    | OSub => 0 (* tbd *)
    | OMul => 0 (* tbd *)
    | ODiv => 0 (* tbd *)
    | OMod => 0 (* tbd *)
    end.

  Inductive eval_exp : exp -> value -> State.t -> Prop :=
  | EEVar :
      forall v n s,
        State.acc (pvar_var v) s = Some n ->
        eval_exp (EVar v) (Int64.unsigned n) s
  | EEConst : forall n s, eval_exp (EConst n) n s
  | EECarry :
      forall s c,
        State.carry s = Some c ->
        eval_exp ECarry (ctoZ c) s
  | EEUnop :
      forall op e n m s,
        eval_exp e n s ->
        eval_unop op n = m ->
        eval_exp (EUnop op e) m s
  | EEBinop :
      forall op e1 e2 v1 v2 n s,
        eval_exp e1 v1 s ->
        eval_exp e2 v2 s ->
        eval_binop op v1 v2 = n ->
        eval_exp (EBinop op e1 e2) n s.

  Definition eval_cop op (v1 v2 : value) : bool :=
    match op with
    | CEq => v1 == v2
    | CLt => Z.ltb v1 v2
    | CLe => Z.leb v1 v2
    | CGt => Z.gtb v1 v2
    | CGe => Z.geb v1 v2
    end.

  Inductive eval_bexp : bexp -> bool -> State.t -> Prop :=
  | EBComp :
      forall op e1 e2 n1 n2 s,
        eval_exp e1 n1 s ->
        eval_exp e2 n2 s ->
        eval_bexp (BComp op e1 e2) (eval_cop op n1 n2) s
  | EBNot :
      forall e b s,
        eval_bexp e b s ->
        eval_bexp (BNot e) (~~b) s
  | EBAnd :
      forall e1 e2 b1 b2 s,
        eval_bexp e1 b1 s ->
        eval_bexp e2 b2 s ->
        eval_bexp (BAnd e1 e2) (b1 && b2) s
  | EBOr :
      forall e1 e2 b1 b2 s,
        eval_bexp e1 b1 s ->
        eval_bexp e2 b2 s ->
        eval_bexp (BOr e1 e2) (b1 || b2) s.

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

  Lemma spec_empty_entails :
    forall f g,
      spec f [::] g -> entails f g.
  Proof.
    move=> f g He s Hf.
    apply: (He s _ Hf).
    apply: EQEmpty.
  Qed.

  Lemma spec_empty :
    forall f g,
      entails f g -> spec f [::] g.
  Proof.
    move=> f g Hfg s1 s2 Hf Hp.
    move: Hf.
    inversion_clear Hp => {s1} Hf.
    exact: (Hfg _ Hf).
  Qed.

  Lemma spec_cons :
    forall f g h hd tl,
      spec f [::hd] g -> spec g tl h ->
      spec f (hd::tl) h.
  Proof.
    move=> f g h hd tl Hhd Htl s1 s2 Hf Hp.
    inversion_clear Hp.
    apply: (Htl st2 _ _ H0).
    apply: (Hhd s1 _ Hf).
    apply: (EQCons H).
    exact: EQEmpty.
  Qed.

End Specification.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : qhasm_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : qhasm_scope.
Notation "{{ f }} p {{ g }}" := (spec f p g) (at level 82, no associativity) : qhasm_scope.



(* A program is safe under a precondition. *)
Definition program_safe_under E (p : program E) (e : bexp E) : Prop :=
  forall s : State.t,
    eval_bexp e true s ->
    program_safe p s.
