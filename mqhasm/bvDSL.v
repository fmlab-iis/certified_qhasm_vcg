
(** * A domain specific language over bit-vectors *)

From Coq Require Import Program ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.
From Common Require Import Arch Types SsrOrdered Env Nats ZAriths Bits FSets Var Store Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope bvdsl_scope with bvdsl.

Local Open Scope bvdsl_scope.



Reserved Notation "@- x" (at level 35, right associativity).
Reserved Notation "x @+ y" (at level 50, left associativity).
Reserved Notation "x @- y" (at level 50, left associativity).
Reserved Notation "x @* y" (at level 40, left associativity).
Reserved Notation "x @^ y" (at level 30, right associativity).
Reserved Notation "x @:= y" (at level 70, no associativity).
Reserved Notation "[ x , y ] @:= z # p" (at level 0, format "[ x , y ] @:= z # p", only parsing).
Reserved Notation "x @= y" (at level 70, no associativity).
Reserved Notation "x @= y 'mod' z" (at level 70, y at next level, no associativity).
Reserved Notation "x @&& y" (at level 70, no associativity).
Reserved Notation "s |= f" (at level 74, no associativity).
Reserved Notation "f ===> g" (at level 82, no associativity).
Reserved Notation "{{ f }} p {{ g }}" (at level 82, no associativity).
Reserved Notation "|= s" (at level 83, no associativity).

Module MakeBVDSL (A : ARCH) (V : SsrOrderedType).

  Module VS := FSetList.Make V.
  Module VSLemmas := FSetLemmas VS.



  (** Syntax *)

  Notation var := V.t.

  Local Notation int := (BITS A.wordsize).

  Inductive atomic : Type :=
  | bvVar : var -> atomic
  | bvConst : int -> atomic.

  (*
    bvAddC carry v e1 e2: carry? v = e1 + e2
    bvAdc v e1 e2 c: v = e1 + e2 + c
    bvAdcC carry v e1 e2 c: carry? v = e1 + e2 + c
    bvSubC carry v e1 e2: carry? v = e1 - e2
    bvMulf vh vl e1 e2: split (e1 * e2) at A.wordsize
    bvShl v e p: v = e * 2^p
    bvSplit vh vl e p: split e at p
    bvConcatShl: vh vl e1 e2 p: split (e1 * 2^A.wordsize + e2) at (A.wordsize - p)
   *)
  Inductive instr : Type :=
  | bvAssign : var -> atomic -> instr
(*  | bvNeg : var -> atomic -> instr *)
  | bvAdd : var -> atomic -> atomic -> instr
  | bvAddC : var -> var -> atomic -> atomic -> instr
  | bvAdc : var -> atomic -> atomic -> var -> instr
  | bvAdcC : var -> var -> atomic -> atomic -> var -> instr
  | bvSub : var -> atomic -> atomic -> instr
(*  | bvSubC : var -> var -> atomic -> atomic -> instr *)
  | bvMul : var -> atomic -> atomic -> instr
  | bvMulf : var -> var -> atomic -> atomic -> instr
  | bvShl : var -> atomic -> int -> instr
  | bvSplit : var -> var -> atomic -> int -> instr
  | bvConcatShl : var -> var -> atomic -> atomic -> int -> instr.

  Global Arguments bvConst n%bits.

  Definition program : Type := seq instr.

  Definition vars_atomic (a : atomic) : VS.t :=
    match a with
    | bvVar v => VS.singleton v
    | bvConst _ => VS.empty
    end.

  Definition vars_instr (i : instr) : VS.t :=
    match i with
    | bvAssign v e
(*    | bvNeg v e *)
    | bvShl v e _ => VS.add v (vars_atomic e)
    | bvAdd v e1 e2
    | bvSub v e1 e2
    | bvMul v e1 e2 => VS.add v (VS.union (vars_atomic e1) (vars_atomic e2))
    | bvAddC c v e1 e2
    | bvAdc v e1 e2 c
    (*| bvSubC c v e1 e2*) => VS.add c (VS.add v (VS.union (vars_atomic e1) (vars_atomic e2)))
    | bvAdcC c v e1 e2 a => VS.add a (VS.add c (VS.add v (VS.union (vars_atomic e1) (vars_atomic e2))))
    | bvSplit vh vl e _ => VS.add vh (VS.add vl (vars_atomic e))
    | bvMulf vh vl e1 e2
    | bvConcatShl vh vl e1 e2 _ =>
      VS.add vh (VS.add vl (VS.union (vars_atomic e1) (vars_atomic e2)))
    end.

  Definition lvs_instr (i : instr) : VS.t :=
    match i with
    | bvAssign v _
(*    | bvNeg v _ *)
    | bvAdd v _ _
    | bvAdc v _ _ _
    | bvSub v _ _
    | bvMul v _ _
    | bvShl v _ _ => VS.singleton v
    | bvAddC c v _ _
    | bvAdcC c v _ _ _
    (*| bvSubC c v _ _*) => VS.add c (VS.singleton v)
    | bvMulf vh vl _ _
    | bvSplit vh vl _ _
    | bvConcatShl vh vl _ _ _ => VS.add vh (VS.singleton vl)
    end.

  Definition rvs_instr (i : instr) : VS.t :=
    match i with
    | bvAssign _ e
(*    | bvNeg _ e *)
    | bvShl _ e _
    | bvSplit _ _ e _ => vars_atomic e
    | bvAdc _ e1 e2 c
    | bvAdcC _ _ e1 e2 c => VS.add c (VS.union (vars_atomic e1) (vars_atomic e2))
    | bvAdd _ e1 e2
    | bvAddC _ _ e1 e2
    | bvSub _ e1 e2
(*    | bvSubC _ _ e1 e2 *)
    | bvMul _ e1 e2
    | bvMulf _ _ e1 e2
    | bvConcatShl _ _ e1 e2 _ => VS.union (vars_atomic e1) (vars_atomic e2)
    end.

  Fixpoint vars_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (vars_instr hd) (vars_program tl)
    end.

  Fixpoint lvs_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (lvs_instr hd) (lvs_program tl)
    end.

  Fixpoint rvs_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (rvs_instr hd) (rvs_program tl)
    end.

  Definition bvzero : int := fromNat 0.
  Definition bvone : int := fromNat 1.
  Definition bvtwo : int := fromNat 2.

  Lemma vars_instr_split i :
    VS.Equal (vars_instr i) (VS.union (lvs_instr i) (rvs_instr i)).
  Proof.
    elim : i => /=; move=> *;
    match goal with
    | |- VS.Equal (VS.add ?v (vars_atomic ?e)) (VS.union (VS.singleton ?v) (vars_atomic ?e)) =>
      rewrite -VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- VS.Equal (VS.add ?v (VS.union (vars_atomic ?e1) (vars_atomic ?e2)))
                  (VS.union (VS.singleton ?v)
                            (VS.union (vars_atomic ?e1) (vars_atomic ?e2))) =>
      rewrite -VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- VS.Equal (VS.add ?vh (VS.add ?vl (vars_atomic ?e)))
                  (VS.union (VS.add ?vh (VS.singleton ?vl)) (vars_atomic ?e)) =>
      rewrite VSLemmas.OP.P.union_add;
      rewrite -VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- VS.Equal
           (VS.add ?vh (VS.add ?vl (VS.union (vars_atomic ?e1) (vars_atomic ?e2))))
           (VS.union (VS.add ?vh (VS.singleton ?vl))
                     (VS.union (vars_atomic ?e1) (vars_atomic ?e2))) =>
      rewrite VSLemmas.OP.P.union_add;
      rewrite -VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- VS.Equal
           (VS.add ?c (VS.add ?v (VS.union (vars_atomic ?e1) (vars_atomic ?e2))))
           (VS.union (VS.singleton ?v)
                     (VS.add ?c (VS.union (vars_atomic ?e1) (vars_atomic ?e2)))) =>
      rewrite VSLemmas.OP.P.add_add;
      rewrite VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- VS.Equal
           (VS.add ?a
                   (VS.add ?c (VS.add ?v (VS.union (vars_atomic ?e1) (vars_atomic ?e2)))))
           (VS.union (VS.add ?c (VS.singleton ?v))
                     (VS.add ?a (VS.union (vars_atomic ?e1) (vars_atomic ?e2)))) =>
      rewrite (VSLemmas.OP.P.union_sym (VS.add _ _) (VS.add _ _))
              VSLemmas.OP.P.union_add
              (VSLemmas.OP.P.union_sym (VS.union _ _) (VS.add _ _))
              VSLemmas.OP.P.union_add
              -VSLemmas.OP.P.add_union_singleton;
      reflexivity
    | |- _ => idtac "not matched"
    end.
  Qed.

  Lemma mem_vars_instr1 v i :
    VS.mem v (vars_instr i) ->
    VS.mem v (lvs_instr i) \/ VS.mem v (rvs_instr i).
  Proof.
    rewrite vars_instr_split => H.
    case: (VSLemmas.mem_union1 H) => {H} H.
    - by left.
    - by right.
  Qed.

  Lemma mem_vars_instr2 v i :
    VS.mem v (lvs_instr i) ->
    VS.mem v (vars_instr i).
  Proof.
    rewrite vars_instr_split => H.
    by apply: VSLemmas.mem_union2.
  Qed.

  Lemma mem_vars_instr3 v i :
    VS.mem v (rvs_instr i) ->
    VS.mem v (vars_instr i).
  Proof.
    rewrite vars_instr_split => H.
    by apply: VSLemmas.mem_union3.
  Qed.

  Lemma lvs_instr_subset i :
    VS.subset (lvs_instr i) (vars_instr i).
  Proof.
    rewrite vars_instr_split.
    exact: VSLemmas.union_subset_1.
  Qed.

  Lemma rvs_instr_subset i :
    VS.subset (rvs_instr i) (vars_instr i).
  Proof.
    rewrite vars_instr_split.
    exact: VSLemmas.union_subset_2.
  Qed.

  Lemma vars_program_split p :
    VS.Equal (vars_program p) (VS.union (lvs_program p) (rvs_program p)).
  Proof.
    elim: p => /=.
    - rewrite VSLemmas.union_emptyl.
      reflexivity.
    - move=> hd tl IH.
      rewrite VSLemmas.OP.P.union_assoc.
      rewrite (VSLemmas.OP.P.union_sym (rvs_instr hd) (rvs_program tl)).
      rewrite -(VSLemmas.OP.P.union_assoc (lvs_program tl)).
      rewrite (VSLemmas.OP.P.union_sym _ (rvs_instr hd)).
      rewrite -VSLemmas.OP.P.union_assoc.
      rewrite -IH.
      rewrite -vars_instr_split.
      reflexivity.
  Qed.

  Lemma mem_vars_program1 v p :
    VS.mem v (vars_program p) ->
    VS.mem v (lvs_program p) \/ VS.mem v (rvs_program p).
  Proof.
    rewrite vars_program_split => H.
    case: (VSLemmas.mem_union1 H) => {H} H.
    - by left.
    - by right.
  Qed.

  Lemma mem_vars_program2 v p :
    VS.mem v (lvs_program p) ->
    VS.mem v (vars_program p).
  Proof.
    rewrite vars_program_split => H.
    by apply: VSLemmas.mem_union2.
  Qed.

  Lemma mem_vars_program3 v p :
    VS.mem v (rvs_program p) ->
    VS.mem v (vars_program p).
  Proof.
    rewrite vars_program_split => H.
    by apply: VSLemmas.mem_union3.
  Qed.

  Lemma lvs_program_subset p :
    VS.subset (lvs_program p) (vars_program p).
  Proof.
    rewrite vars_program_split.
    exact: VSLemmas.union_subset_1.
  Qed.

  Lemma rvs_program_subset p :
    VS.subset (rvs_program p) (vars_program p).
  Proof.
    rewrite vars_program_split.
    exact: VSLemmas.union_subset_2.
  Qed.

  Lemma vars_program_concat p1 p2 :
    VS.Equal (vars_program (p1 ++ p2)) (VS.union (vars_program p1) (vars_program p2)).
  Proof.
    elim: p1 p2 => /=.
    - move=> p2.
      rewrite VSLemmas.union_emptyl.
      reflexivity.
    - move=> hd tl IH p2.
      rewrite IH.
      rewrite VSLemmas.OP.P.union_assoc.
      reflexivity.
  Qed.

  Lemma lvs_program_concat p1 p2 :
    VS.Equal (lvs_program (p1 ++ p2)) (VS.union (lvs_program p1) (lvs_program p2)).
  Proof.
    elim: p1 p2 => /=.
    - move=> p2.
      rewrite VSLemmas.union_emptyl.
      reflexivity.
    - move=> hd tl IH p2.
      rewrite IH.
      rewrite VSLemmas.OP.P.union_assoc.
      reflexivity.
  Qed.

  Lemma vars_program_rcons p i :
    VS.Equal (vars_program (rcons p i)) (VS.union (vars_program p) (vars_instr i)).
  Proof.
    rewrite -cats1.
    rewrite vars_program_concat /=.
    rewrite VSLemmas.union_emptyr.
    reflexivity.
  Qed.

  Lemma lvs_program_rcons p i :
    VS.Equal (lvs_program (rcons p i)) (VS.union (lvs_program p) (lvs_instr i)).
  Proof.
    rewrite -cats1.
    rewrite lvs_program_concat /=.
    rewrite VSLemmas.union_emptyr.
    reflexivity.
  Qed.



  (** State *)

  Notation value := int.

  Module Store := MakeTStore V.

  Module State.

    Definition t : Type := Store.t value.

    Definition empty : t := Store.empty value.

    Definition acc (x : var) (s : t) : value :=
      Store.acc x s.

    Definition upd (x : var) (v : value) (s : t) : t :=
      Store.upd x v s.

    Definition upd2 (x1 : var) v1 (x2 : var) v2 (s : t) : t :=
      upd x2 v2 (upd x1 v1 s).

    Lemma acc_upd_eq :
      forall (x y : var) v (s : t),
        x == y ->
        acc x (upd y v s) = v.
    Proof.
      exact: Store.acc_upd_eq.
    Qed.

    Lemma acc_upd_neq :
      forall (x y : var) v (s : t),
        x != y ->
        acc x (upd y v s) = acc x s.
    Proof.
      exact: Store.acc_upd_neq.
    Qed.

    Lemma acc_upd2_eq1 :
      forall (x : var) (y1 : var) v1 (y2 : var) v2 (s : t),
        x == y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof.
      move=> x y1 v1 y2 v2 s Hx1 Hx2.
      rewrite (acc_upd_neq _ _ Hx2) (acc_upd_eq _ _ Hx1).
      reflexivity.
    Qed.

    Lemma acc_upd2_eq2 :
      forall (x : var) (y1 : var) v1 (y2 : var) v2 (s : t),
        x == y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof.
      move=> x y1 v1 y2 v2 s Hx2.
      rewrite (acc_upd_eq _ _ Hx2).
      reflexivity.
    Qed.

    Lemma acc_upd2_neq :
      forall (x : var) (y1 : var) v1 (y2 : var) v2 s,
        x != y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof.
      move=> x y1 v1 y2 v2 s Hx1 Hx2.
      rewrite (acc_upd_neq _ _ Hx2) (acc_upd_neq _ _ Hx1).
      reflexivity.
    Qed.

    Definition Upd (x : var) v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 (x1 : var) v1 (x2 : var) v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Lemma Upd_upd :
      forall (x : var) v s,
        Upd x v s (upd x v s).
    Proof.
      exact: Store.Upd_upd.
    Qed.

    Lemma Upd2_upd :
      forall (x1 : var) v1 (x2 : var) v2 s,
        Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof.
      move=> x1 v1 x2 v2 s y.
      reflexivity.
    Qed.

    Lemma acc_Upd_eq :
      forall (x y : var) v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      rewrite (Hupd x).
      exact: acc_upd_eq.
    Qed.

    Lemma acc_Upd_neq :
      forall (x y : var) v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      rewrite (Hupd x).
      exact: acc_upd_neq.
    Qed.

    Lemma acc_Upd2_eq1 :
      forall (x : var) (y1 : var) v1 (y2 : var) v2 s1 s2,
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
      forall (x : var) (y1 : var) v1 (y2 : var) v2 s1 s2,
        x == y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v2.
    Proof.
      move=> x y1 v1 y2 v2 s1 s2 Heq Hupd.
      rewrite (Hupd x).
      exact: acc_upd2_eq2.
    Qed.

    Lemma acc_Upd2_neq :
      forall (x : var) (y1 : var) v1 (y2 : var) v2 s1 s2,
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

  Definition eval_atomic (a : atomic) (s : State.t) : value :=
    match a with
    | bvVar v => State.acc v s
    | bvConst n => n
    end.

  Program Definition high_ext (n : nat) (x : BITS n) (p : nat) : BITS n :=
    (if Program.Utils.dec (p < n)
     then zeroExtend (n - p) (@high p (n - p) x)
     else zero n)%GEN_IF.
  Next Obligation.
    apply: Logic.eq_sym.
    apply: subnK.
    exact: ltnW.
  Qed.
  Next Obligation.
    apply: subnKC.
    exact: ltnW.
  Qed.

  Program Definition low_ext (n : nat) (x : BITS n) (p : nat) : BITS n :=
    (if Program.Utils.dec (p < n)
     then zeroExtend (n - p) (@low (n - p) p x)
     else x)%GEN_IF.
  Next Obligation.
    apply: Logic.eq_sym.
    apply: subnKC.
    exact: ltnW.
  Qed.
  Next Obligation.
    apply: subnKC.
    exact: ltnW.
  Qed.

  (*
  Definition split_ext (n : nat) (x : BITS n) (p : nat) :=
    (high_ext x (n - p), low_ext x p).
   *)

  Definition split_ext (n : nat) (x : BITS n) (p : nat) :=
    (shrBn x p,
     shrBn (shlBn x (n - p)) (n - p)).

  Definition concat_shl (n : nat) (x y : BITS n) (p : nat) :=
    (high n (shlBn (x ## y) p),
     shrBn (low n (shlBn (x ## y) p)) p).

  Definition eval_instr (s : State.t) (i : instr) : State.t :=
    match i with
    | bvAssign v e => State.upd v (eval_atomic e s) s
(*    | bvNeg v e => State.upd v (negB (eval_atomic e s)) s *)
    | bvAdd v e1 e2 => State.upd v (addB (eval_atomic e1 s) (eval_atomic e2 s)) s
    | bvAddC c v e1 e2 =>
      State.upd2 c
                 (high A.wordsize
                       (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                             (zeroExtend A.wordsize (eval_atomic e2 s))))
                 v
                 (low A.wordsize
                      (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                            (zeroExtend A.wordsize (eval_atomic e2 s))))
                 s
    | bvAdc v e1 e2 c =>
      State.upd v
                (low A.wordsize
                     (addB
                        (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                              (zeroExtend A.wordsize (eval_atomic e2 s)))
                        (zeroExtend A.wordsize (State.acc c s))))
                s
    | bvAdcC c v e1 e2 a =>
      State.upd2 c
                 (high A.wordsize
                       (addB
                          (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                                (zeroExtend A.wordsize (eval_atomic e2 s)))
                          (zeroExtend A.wordsize (State.acc a s))))
                 v
                 (low A.wordsize
                      (addB
                         (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                               (zeroExtend A.wordsize (eval_atomic e2 s)))
                         (zeroExtend A.wordsize (State.acc a s))))
                 s
    | bvSub v e1 e2 => State.upd v (subB (eval_atomic e1 s) (eval_atomic e2 s)) s
(*    | bvSubC c v e1 e2 =>
      State.upd2 c
                 (if carry_subB (eval_atomic e1 s) (eval_atomic e2 s) then bvone else bvzero)
                 v (subB (eval_atomic e1 s) (eval_atomic e2 s))
                 s *)
    | bvMul v e1 e2 => State.upd v (mulB (eval_atomic e1 s) (eval_atomic e2 s)) s
    | bvMulf vh vl e1 e2 =>
      State.upd2 vh (high A.wordsize (fullmulB (eval_atomic e1 s) (eval_atomic e2 s)))
                 vl (low A.wordsize (fullmulB (eval_atomic e1 s) (eval_atomic e2 s)))
                 s
    | bvShl v e p => State.upd v (shlBn (eval_atomic e s) (toNat p)) s
    | bvSplit vh vl e p =>
      State.upd2 vh (fst (split_ext (eval_atomic e s) (toNat p)))
                 vl (snd (split_ext (eval_atomic e s) (toNat p)))
                 s
    | bvConcatShl vh vl e1 e2 p =>
      State.upd2 vh (fst (concat_shl (eval_atomic e1 s)
                                     (eval_atomic e2 s) (toNat p)))
                 vl (snd (concat_shl (eval_atomic e1 s)
                                     (eval_atomic e2 s) (toNat p)))
                 s
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

  Lemma eval_program_concat_step :
    forall (p1 p2 : program) (s : State.t),
      eval_program s (p1 ++ p2) =
      eval_program (eval_program s p1) p2.
  Proof.
    elim => /=.
    - reflexivity.
    - move=> hd tl IH p2 s.
      rewrite IH.
      reflexivity.
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

  Inductive unop : Set :=
  | bvNegOp.

  Inductive binop : Set :=
  | bvAddOp
  | bvSubOp
  | bvMulOp.

  Inductive cmpop : Set :=
  | bvUltOp
  | bvUleOp
  | bvUgtOp
  | bvUgeOp.

  Inductive exp : nat -> Type :=
  | bvVarE : var -> exp A.wordsize
  | bvConstE : forall n : nat, BITS n -> exp n
(*  | bvUnop : forall n : nat, unop -> exp n -> exp n *)
  | bvBinop : forall n : nat, binop -> exp n -> exp n -> exp n
  | bvExt : forall n : nat, exp n -> forall m : nat, exp (n + m).

  Definition bvvar v := bvVarE v.
  Definition bvposz {w} n := bvConstE (@fromPosZ w n).
  Definition bvadd w (e1 e2 : exp w) := bvBinop bvAddOp e1 e2.
  Definition bvsub w (e1 e2 : exp w) := bvBinop bvSubOp e1 e2.
  Definition bvmul w (e1 e2 : exp w) := bvBinop bvMulOp e1 e2.

  Inductive bexp : Type :=
  | bvTrue : bexp
  | bvEq : forall n : nat, exp n -> exp n -> bexp
  | bvEqMod : forall n : nat, exp n -> exp n -> exp n -> bexp
  | bvCmp : forall n : nat, cmpop -> exp n -> exp n -> bexp
  | bvAnd : bexp -> bexp -> bexp.

  Definition bvult w (e1 e2 : exp w) := bvCmp bvUltOp e1 e2.
  Definition bvule w (e1 e2 : exp w) := bvCmp bvUleOp e1 e2.
  Definition bvugt w (e1 e2 : exp w) := bvCmp bvUgtOp e1 e2.
  Definition bvuge w (e1 e2 : exp w) := bvCmp bvUgeOp e1 e2.

  Fixpoint bvands es : bexp :=
    match es with
    | [::] => bvTrue
    | hd::[::] => hd
    | hd::tl => bvAnd hd (bvands tl)
    end.

  Fixpoint vars_exp (n : nat) (e : exp n) : VS.t :=
    match e with
    | bvVarE x => VS.singleton x
    | bvConstE _ _ => VS.empty
(*    | bvUnop _ _ e => vars_exp e *)
    | bvBinop _ _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvExt _ e _ => vars_exp e
    end.

  Fixpoint vars_bexp (e : bexp) : VS.t :=
    match e with
    | bvTrue => VS.empty
    | bvEq _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvEqMod _ e1 e2 p => VS.union (vars_exp e1)
                                    (VS.union (vars_exp e2) (vars_exp p))
    | bvCmp _ _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvAnd e1 e2 => VS.union (vars_bexp e1) (vars_bexp e2)
    end.

  Definition eval_unop (n : nat) (op : unop) (v : BITS n) : BITS n :=
    match op with
    | bvNegOp => negB v
    end.

  Definition eval_binop (n : nat) (op : binop) (v1 v2 : BITS n) : BITS n :=
    match op with
    | bvAddOp => addB v1 v2
    | bvSubOp => subB v1 v2
    | bvMulOp => mulB v1 v2
    end.

  Definition eval_cmpop (n : nat) (op : cmpop) (v1 v2 : BITS n) : bool :=
    match op with
    | bvUltOp => ltB v1 v2
    | bvUleOp => leB v1 v2
    | bvUgtOp => ~~ (leB v1 v2)
    | bvUgeOp => ~~ (ltB v1 v2)
    end.

  Fixpoint eval_exp (n : nat) (e : exp n) (s : State.t) : BITS n :=
    match e with
    | bvVarE x => State.acc x s
    | bvConstE _ n => n
(*    | bvUnop _ op e => eval_unop op (eval_exp e s) *)
    | bvBinop _ op e1 e2 => eval_binop op (eval_exp e1 s) (eval_exp e2 s)
    | bvExt _ e m => zeroExtend m (eval_exp e s)
    end.

  Fixpoint eval_bexp (e : bexp) (s : State.t) : Prop :=
    match e with
    | bvTrue => True
    | bvEq _ e1 e2 => eval_exp e1 s = eval_exp e2 s
    | bvEqMod _ e1 e2 p => modulo (toPosZ (eval_exp e1 s)) (toPosZ (eval_exp e2 s)) (toPosZ (eval_exp p s))
    | bvCmp _ op e1 e2 => eval_cmpop op (eval_exp e1 s) (eval_exp e2 s)
    | bvAnd e1 e2 => eval_bexp e1 s /\ eval_bexp e2 s
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

  Lemma spec_concat :
    forall f g h p1 p2,
      |= {{ f }} p1 {{ g }} -> |= {{ g }} p2 {{ h }} ->
      |= {{ f }} (p1 ++ p2) {{ h }}.
  Proof.
    move=> f g h p1 p2 Hp1 Hp2 s1 s2 /= Hf Hp.
    move: (eval_program_split Hp) => [s3 [Hep1 Hep2]].
    apply: (Hp2 _ _ _ Hep2) => /=.
    apply: (Hp1 _ _ _ Hep1) => /=.
    assumption.
  Qed.

  Lemma spec_split_post :
    forall f g1 g2 p,
      |= {{ f }} p {{ g1 }} ->
      |= {{ f }} p {{ g2 }} ->
      |= {{ f }} p {{ bvAnd g1 g2 }}.
  Proof.
    move=> f g1 g2 p Hg1 Hg2 s1 s2 /= Hf Hp.
    move: (Hg1 s1 s2 Hf Hp) => /= {Hg1} Hg1.
    move: (Hg2 s1 s2 Hf Hp) => /= {Hg2} Hg2.
    exact: (conj Hg1 Hg2).
  Qed.



  (** Well-formed programs *)

  Definition well_formed_instr (vs : VS.t) (i : instr) : bool :=
    match i with
    | bvAssign v e
    (*| bvNeg v e*) => VS.subset (vars_atomic e) vs
    | bvAdd v e1 e2
    | bvSub v e1 e2
    | bvMul v e1 e2 => VS.subset (vars_atomic e1) vs
                                 && VS.subset (vars_atomic e2) vs
    | bvAddC c v e1 e2
    (*| bvSubC c v e1 e2*) => (c != v)
                            && VS.subset (vars_atomic e1) vs
                            && VS.subset (vars_atomic e2) vs
    | bvAdc v e1 e2 c => VS.mem c vs
                                && VS.subset (vars_atomic e1) vs
                                && VS.subset (vars_atomic e2) vs
    | bvAdcC c v e1 e2 a => (c != v)
                              && VS.mem a vs
                              && VS.subset (vars_atomic e1) vs
                              && VS.subset (vars_atomic e2) vs
    | bvShl v e p => VS.subset (vars_atomic e) vs
    | bvSplit vh vl e _ => (vh != vl) && (VS.subset (vars_atomic e) vs)
    | bvMulf vh vl e1 e2
    | bvConcatShl vh vl e1 e2 _ => (vh != vl)
                                     && VS.subset (vars_atomic e1) vs
                                     && VS.subset (vars_atomic e2) vs
    end.

  Fixpoint well_formed_program (vs : VS.t) (p : program) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      well_formed_instr vs hd &&
      well_formed_program (VS.union vs (lvs_instr hd)) tl
    end.

  Fixpoint find_non_well_formed_instr (vs : VS.t) (p : program) : option instr :=
    match p with
    | [::] => None
    | hd::tl =>
      if well_formed_instr vs hd
      then find_non_well_formed_instr (VS.union vs (lvs_instr hd)) tl
      else Some hd
    end.

  Ltac check_well_formedness vs p :=
    let res := constr:(find_non_well_formed_instr vs p) in
    let res := eval compute in res in
        match res with
        | None => idtac "The program is well-formed."
        | Some ?i => idtac "The program is not well-formed,"
                           "caused by the following instruction."; idtac i
        end.

  Definition well_formed_spec (vs : VS.t) (s : spec) : bool :=
    VS.subset (vars_bexp (spre s)) vs &&
    well_formed_program vs (sprog s) &&
    VS.subset (vars_bexp (spost s)) (VS.union vs (vars_program (sprog s))).

  Lemma well_formed_instr_subset_rvs vs i :
    well_formed_instr vs i ->
    VS.subset (rvs_instr i) vs.
  Proof.
    elim: i => /=; intros;
    (let rec tac :=
         match goal with
         | H : ?a |- ?a => assumption
         | H : is_true (_ && _) |- _ =>
           let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
         | |- is_true (VS.subset (VS.add _ _) _) =>
           apply: VSLemmas.subset_add3; tac
         | |- is_true (VS.subset (VS.union _ _) _) =>
           apply: VSLemmas.subset_union3; tac
         | |- _ => idtac
         end in
     tac).
  Qed.

  Lemma well_formed_instr_subset vs1 vs2 i :
    well_formed_instr vs1 i ->
    VS.subset vs1 vs2 ->
    well_formed_instr vs2 i.
  Proof.
    elim: i vs1 vs2 => /=; move=> *;
    hyps_splitb; repeat splitb;
    (match goal with
     | H: ?a |- ?a => assumption
     | H1: is_true (VS.subset ?s ?vs1),
       H2 : is_true (VS.subset ?vs1 ?vs2)
       |- is_true (VS.subset ?s ?vs2) =>
         by rewrite (VSLemmas.subset_trans H1 H2)
     | H1 : is_true (VS.mem ?v ?vs1),
       H2 : is_true (VS.subset ?vs1 ?vs2)
       |- is_true (VS.mem ?v ?vs3) =>
       exact: (VSLemmas.mem_subset H1 H2)
     | |- _ => idtac
     end).
  Qed.

  Lemma well_formed_instr_replace vs1 vs2 i :
    well_formed_instr vs1 i ->
    VS.Equal vs1 vs2 ->
    well_formed_instr vs2 i.
  Proof.
    move=> Hwell Heq.
    apply: (well_formed_instr_subset Hwell).
    rewrite Heq.
    exact: VSLemmas.subset_refl.
  Qed.

  Lemma well_formed_program_subset vs1 vs2 p :
    well_formed_program vs1 p ->
    VS.subset vs1 vs2 ->
    well_formed_program vs2 p.
  Proof.
    elim: p vs1 vs2 => //=.
    move=> hd tl IH vs1 vs2 /andP [Hhd Htl] Hsub.
    apply/andP; split.
    - exact: (well_formed_instr_subset Hhd Hsub).
    - apply: (IH _ _ Htl).
      apply: (VSLemmas.union_subsets Hsub).
      exact: VSLemmas.subset_refl.
  Qed.

  Lemma well_formed_program_replace vs1 vs2 p :
    well_formed_program vs1 p ->
    VS.Equal vs1 vs2 ->
    well_formed_program vs2 p.
  Proof.
    move=> Hwell Heq.
    apply: (well_formed_program_subset Hwell).
    rewrite Heq.
    exact: VSLemmas.subset_refl.
  Qed.

  Lemma well_formed_instr_vars vs i :
    well_formed_instr vs i ->
    VS.Equal (VS.union vs (vars_instr i)) (VS.union vs (lvs_instr i)).
  Proof.
    case: i => /=; intros; hyps_splitb;
    (match goal with
     | H: is_true (VS.subset ?s ?vs) |-
       VS.Equal (VS.union ?vs (VS.add ?t ?s)) (VS.union ?vs (VS.singleton ?t)) =>
      rewrite (VSLemmas.OP.P.union_sym vs (VS.add t s))
              VSLemmas.OP.P.union_add
              (VSLemmas.union_subset_equal H)
              (VSLemmas.OP.P.union_sym vs (VS.singleton t))
              -VSLemmas.OP.P.add_union_singleton;
      reflexivity
     | H1: is_true (VS.subset ?s1 ?vs),
       H2: is_true (VS.subset ?s2 ?vs) |-
       VS.Equal (VS.union ?vs (VS.add ?t (VS.union ?s1 ?s2)))
                (VS.union ?vs (VS.singleton ?t)) =>
       rewrite (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_assoc
               (VSLemmas.union_subset_equal H2)
               (VSLemmas.union_subset_equal H1)
               (VSLemmas.OP.P.union_sym vs (VS.singleton _))
               -VSLemmas.OP.P.add_union_singleton;
       reflexivity
     | H1: is_true (VS.subset ?s1 ?vs),
       H2: is_true (VS.subset ?s2 ?vs) |-
       VS.Equal
         (VS.union ?vs
                   (VS.add ?t1 (VS.add ?t2 (VS.union ?s1 ?s2))))
         (VS.union ?vs (VS.add ?t1 (VS.singleton ?t2))) =>
       rewrite (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_assoc
               (VSLemmas.union_subset_equal H2)
               (VSLemmas.union_subset_equal H1)
               (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               -VSLemmas.OP.P.add_union_singleton;
       reflexivity
     | H: is_true (VS.subset ?s ?vs) |-
       VS.Equal (VS.union ?vs (VS.add ?t1 (VS.add ?t2 ?s)))
                (VS.union ?vs (VS.add ?t1 (VS.singleton ?t2))) =>
       rewrite (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_add
               (VSLemmas.union_subset_equal H)
               (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               -VSLemmas.OP.P.add_union_singleton;
       reflexivity
     | H0 : is_true (VS.subset (vars_atomic ?e2) ?vs),
       H1 : is_true (VS.mem ?c ?vs),
       H2 : is_true (VS.subset (vars_atomic ?e1) ?vs) |-
       VS.Equal
         (VS.union ?vs
                   (VS.add ?c
                           (VS.add ?v
                                   (VS.union
                                      (vars_atomic ?e1) (vars_atomic ?e2)))))
         (VS.union ?vs (VS.singleton ?v)) =>
       rewrite (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_assoc
               (VSLemmas.union_subset_equal H0)
               (VSLemmas.union_subset_equal H2)
               VSLemmas.OP.P.add_add
               (VSLemmas.add_equal H1)
               VSLemmas.OP.P.union_sym
               -VSLemmas.OP.P.add_union_singleton;
       reflexivity
     | H1 : is_true (VS.subset (vars_atomic ?e2) ?vs),
       H2 : is_true (VS.subset (vars_atomic ?e1) ?vs),
       H0 : is_true (?c != ?v),
       H3 : is_true (VS.mem ?a vs) |-
       VS.Equal
         (VS.union ?vs
                   (VS.add ?a (VS.add ?c (VS.add ?v (VS.union (vars_atomic ?e1) (vars_atomic ?e2))))))
         (VS.union ?vs (VS.add ?c (VS.singleton ?v))) =>
       rewrite (VSLemmas.OP.P.union_sym vs (VS.add _ _))
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_add
               VSLemmas.OP.P.union_assoc
               (VSLemmas.union_subset_equal H1)
               (VSLemmas.union_subset_equal H2)
               (VSLemmas.OP.P.add_add)
               (VSLemmas.OP.P.add_add vs)
               (VSLemmas.add_equal H3)
               VSLemmas.OP.P.union_sym
               VSLemmas.OP.P.union_add
               -VSLemmas.OP.P.add_union_singleton;
       reflexivity
     | |- _ => idtac
     end).
  Qed.

  Lemma well_formed_program_concat vs p1 p2 :
    well_formed_program vs (p1 ++ p2) =
    well_formed_program vs p1 &&
                        well_formed_program (VS.union vs (lvs_program p1)) p2.
  Proof.
    case H: (well_formed_program vs p1 &&
                        well_formed_program (VS.union vs (lvs_program p1)) p2).
    - move/andP: H => [Hp1 Hp2].
      elim: p1 vs p2 Hp1 Hp2 => /=.
      + move=> vs p2 _ Hp2.
        apply: (well_formed_program_replace Hp2).
        exact: VSLemmas.union_emptyr.
      + move=> hd tl IH vs p2 /andP [Hhd Htl] Hp2.
        rewrite Hhd /=.
        apply: (IH _ _ Htl).
        apply: (well_formed_program_replace Hp2).
        rewrite VSLemmas.OP.P.union_assoc.
        reflexivity.
    - move/negP: H => Hneg.
      apply/negP => H; apply: Hneg; apply/andP.
      elim: p1 vs p2 H => /=.
      + move=> vs p2 Hp2; split; first by trivial.
        apply: (well_formed_program_replace Hp2).
        rewrite VSLemmas.union_emptyr.
        reflexivity.
      + move=> hd tl IH vs p2 /andP [Hhd Htlp2].
        move: (IH _ _ Htlp2) => {IH Htlp2} [Htl Hp2].
        split.
        * by rewrite Hhd Htl.
        * apply: (well_formed_program_replace Hp2).
          rewrite VSLemmas.OP.P.union_assoc.
          reflexivity.
  Qed.

  Lemma well_formed_program_concat1 vs p1 p2 :
    well_formed_program vs (p1 ++ p2) ->
    well_formed_program vs p1.
  Proof.
    rewrite well_formed_program_concat.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_concat2 vs p1 p2 :
    well_formed_program vs (p1 ++ p2) ->
    well_formed_program (VS.union vs (lvs_program p1)) p2.
  Proof.
    rewrite well_formed_program_concat.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_concat3 vs p1 p2 :
    well_formed_program vs p1 ->
    well_formed_program (VS.union vs (lvs_program p1)) p2 ->
    well_formed_program vs (p1 ++ p2).
  Proof.
    rewrite well_formed_program_concat.
    by move=> H1 H2; rewrite H1 H2.
  Qed.

  Lemma well_formed_program_cons1 vs p i :
    well_formed_program vs (i::p) ->
    well_formed_instr vs i.
  Proof.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_cons2 vs p i :
    well_formed_program vs (i::p) ->
    well_formed_program (VS.union vs (lvs_instr i)) p.
  Proof.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_cons3 vs p i :
    well_formed_instr vs i ->
    well_formed_program (VS.union vs (lvs_instr i)) p ->
    well_formed_program vs (i::p).
  Proof.
    move=> H1 H2.
    by rewrite /= H1 H2.
  Qed.

  Lemma well_formed_program_rcons vs p i :
    well_formed_program vs (rcons p i) =
    well_formed_program vs p &&
                        well_formed_instr (VS.union vs (lvs_program p)) i.
  Proof.
    rewrite -cats1.
    rewrite well_formed_program_concat.
    case: (well_formed_program vs p) => //=.
    by case: (well_formed_instr (VS.union vs (lvs_program p)) i).
  Qed.

  Lemma well_formed_program_rcons1 vs p i :
    well_formed_program vs (rcons p i) ->
    well_formed_program vs p.
  Proof.
    rewrite well_formed_program_rcons.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_rcons2 vs p i :
    well_formed_program vs (rcons p i) ->
    well_formed_instr (VS.union vs (lvs_program p)) i.
  Proof.
    rewrite well_formed_program_rcons.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_rcons3 vs p i :
    well_formed_program vs p ->
    well_formed_instr (VS.union vs (lvs_program p)) i ->
    well_formed_program vs (rcons p i).
  Proof.
    rewrite well_formed_program_rcons.
    by move=> H1 H2; rewrite H1 H2.
  Qed.

  Lemma well_formed_program_vars vs p :
    well_formed_program vs p ->
    VS.Equal (VS.union vs (vars_program p)) (VS.union vs (lvs_program p)).
  Proof.
    elim: p vs => /=.
    - move=> vs _.
      reflexivity.
    - move=> hd tl IH vs /andP [Hhd Htl].
      move: (IH _ Htl) => {IH Htl} => Heq.
      rewrite -(@VSLemmas.OP.P.union_assoc _ (lvs_instr hd)).
      rewrite -{}Heq.
      rewrite -(well_formed_instr_vars Hhd).
      rewrite VSLemmas.OP.P.union_assoc.
      reflexivity.
  Qed.



  (** L-vars are different. Used as an assumption weaker
      than well-formedness for the proof of slicing. *)

  Definition instr_lvne i : bool :=
    match i with
    | bvAssign _ _
(*    | bvNeg _ _ *)
    | bvAdd _ _ _
    | bvAdc _ _ _ _
    | bvSub _ _ _
    | bvMul _ _ _
    | bvShl _ _ _ => true
    | bvAddC c v _ _
    | bvAdcC c v _ _ _
    (*| bvSubC c v _ _*) => c != v
    | bvMulf vh vl _ _
    | bvSplit vh vl _ _
    | bvConcatShl vh vl _ _ _ => vh != vl
    end.

  Fixpoint program_lvne p : bool :=
    match p with
    | [::] => true
    | hd::tl => instr_lvne hd && program_lvne tl
    end.

  Lemma program_lvne_rcons p i :
    program_lvne (rcons p i) = program_lvne p && instr_lvne i.
  Proof.
    elim: p i => /=.
    - move=> i.
      by case: (instr_lvne i).
    - move=> hd tl IH i.
      case: (instr_lvne hd) => /=; last by reflexivity.
      rewrite -IH.
      reflexivity.
  Qed.

  Lemma program_lvne_concat p1 p2 :
    program_lvne (p1 ++ p2) = program_lvne p1 && program_lvne p2.
  Proof.
    elim: p1 p2 => /=.
    - reflexivity.
    - move=> hd tl IH p2.
      case: (instr_lvne hd) => /=; last by reflexivity.
      rewrite -IH.
      reflexivity.
  Qed.

  Lemma program_lvne_rev p :
    program_lvne p = program_lvne (rev p).
  Proof.
    elim: p => //=.
    move=> hd tl IH.
    rewrite IH rev_cons andbC -program_lvne_rcons.
    reflexivity.
  Qed.

  Lemma well_formed_instr_lvne vs i :
    well_formed_instr vs i -> instr_lvne i.
  Proof.
    case: i => //=; move=> *; hyps_splitb; assumption.
  Qed.

  Lemma well_formed_program_lvne vs p :
    well_formed_program vs p -> program_lvne p.
  Proof.
    elim: p vs => //=.
    move=> hd tl IH vs /andP [Hhd Htl]; apply/andP; split.
    - exact: (well_formed_instr_lvne Hhd).
    - exact: (IH _ Htl).
  Qed.

  Lemma instr_lvne_well_formed vs i :
    instr_lvne i ->
    VS.subset (rvs_instr i) vs ->
    well_formed_instr vs i.
  Proof.
    case: i => /=; intros; repeat splitb;
    (let rec tac :=
         match goal with
         | H: ?a |- ?a => assumption
         | H : is_true (VS.subset (VS.union _ _) _) |- _ =>
           let H1 := fresh in let H2 := fresh in
           rewrite VSLemmas.subset_union6 in H;
           move/andP: H => [H1 H2]; tac
         | H : is_true (VS.subset (VS.add _ _) _) |- _ =>
           let H1 := fresh in let H2 := fresh in
           rewrite VSLemmas.subset_add6 in H;
           move/andP: H => [H1 H2]; tac
         | |- _ => idtac
         end in
     tac).
  Qed.



  (** Big integers *)

  Section BigIntegers.

    From Common Require Import Nats.
    From mathcomp Require Import ssrnat.

    Variable w : nat.

    Fixpoint limbs_rec i ew (vs : seq (exp ew)) (n : nat) : exp (ew + (i - ew)) :=
      match vs with
      | [::] => bvConstE (@fromNat (ew + (i - ew)) 0)
      | hd::[::] => if n == 0 then bvExt hd (i - ew)
                    else bvBinop bvMulOp
                                 (bvExt hd (i - ew))
                                 (bvConstE (fromPosZ (Zpower_nat 2 n)))
      | hd::tl =>
        let m := (n + w) in
        if n == 0 then bvBinop bvAddOp (bvExt hd (i - ew)) (limbs_rec i tl m)
        else bvBinop bvAddOp
                     (bvBinop bvMulOp (bvExt hd (i - ew))
                              (bvConstE (fromPosZ (Zpower_nat 2 n))))
                     (limbs_rec i tl m)
      end.

    Definition limbs i ew (vs : seq (exp ew)) : exp (ew + (i - ew)) :=
      limbs_rec i vs 0.

  End BigIntegers.



  (** State equality modulo values of a set of variables *)
(*
  Section StateEqmod.

    Variable vs : VS.t.

    Definition state_eqmod s1 s2 : Prop :=
      forall v, VS.mem v vs -> State.acc v s1 = State.acc v s2.

    Lemma state_eqmod_refl s :
      state_eqmod s s.
    Proof.
      move=> v Hmem; reflexivity.
    Qed.

    Lemma state_eqmod_sym s1 s2 :
      state_eqmod s1 s2 -> state_eqmod s2 s1.
    Proof.
      move=> Heqm v Hmem.
      rewrite (Heqm v Hmem).
      reflexivity.
    Qed.

    Lemma state_eqmod_trans s1 s2 s3 :
      state_eqmod s1 s2 -> state_eqmod s2 s3 -> state_eqmod s1 s3.
    Proof.
      move=> Heqm12 Heqm23 v Hmem.
      rewrite (Heqm12 v Hmem) (Heqm23 v Hmem).
      reflexivity.
    Qed.

    Global Instance state_eqmod_equiv : RelationClasses.Equivalence state_eqmod.
    Proof.
      split.
      - exact: state_eqmod_refl.
      - exact: state_eqmod_sym.
      - exact: state_eqmod_trans.
    Defined.

  End StateEqmod.

  Lemma state_eqmod_subset vs1 vs2 s1 s2 :
    state_eqmod vs1 s1 s2 ->
    VS.subset vs2 vs1 ->
    state_eqmod vs2 s1 s2.
  Proof.
    move=> Heqm Hsub v Hmem.
    exact: (Heqm v (VSLemmas.mem_subset Hmem Hsub)).
  Qed.

  Lemma state_eqmod_add1 v vs s1 s2 :
    state_eqmod (VS.add v vs) s1 s2 ->
    State.acc v s1 = State.acc v s2 /\ state_eqmod vs s1 s2.
  Proof.
    move=> Heqm; split.
    - apply: Heqm.
      exact: VSLemmas.mem_add2.
    - move=> x Hmem; apply: Heqm.
      apply: VSLemmas.mem_add3.
      assumption.
  Qed.

  Lemma state_eqmod_add2 v vs s1 s2 :
    state_eqmod vs s1 s2 ->
    State.acc v s1 = State.acc v s2 ->
    state_eqmod (VS.add v vs) s1 s2.
  Proof.
    move=> Heqm Hv x Hmem.
    case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
    - by rewrite (eqP Hmem).
    - exact: (Heqm x Hmem).
  Qed.

  Lemma state_eqmod_union1 vs1 vs2 s1 s2 :
    state_eqmod (VS.union vs1 vs2) s1 s2 ->
    state_eqmod vs1 s1 s2 /\ state_eqmod vs2 s1 s2.
  Proof.
    move=> Heqm; split; move=> v Hmem; apply: Heqm.
    - apply: VSLemmas.mem_union2.
      assumption.
    - apply: VSLemmas.mem_union3.
      assumption.
  Qed.

  Lemma state_eqmod_union2 vs1 vs2 s1 s2 :
    state_eqmod vs1 s1 s2 ->
    state_eqmod vs2 s1 s2 ->
    state_eqmod (VS.union vs1 vs2) s1 s2.
  Proof.
    move=> Heqm1 Heqm2 v Hmem.
    case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    - exact: (Heqm1 v Hmem).
    - exact: (Heqm2 v Hmem).
  Qed.

  Lemma state_eqmod_exp s1 s2 e :
    state_eqmod (vars_exp e) s1 s2 ->
    eval_exp e s1 = eval_exp e s2.
  Proof.
    elim: e => /=.
    - move=> v Heqm.
      apply: Heqm.
      exact: VSLemmas.mem_singleton2.
    - reflexivity.
    - move=> op e IH Heqm.
      rewrite (IH Heqm).
      reflexivity.
    - move=> op e1 IH1 e2 IH2 Heqm.
      move: (state_eqmod_union1 Heqm) => {Heqm} [Heqm1 Heqm2].
      rewrite (IH1 Heqm1) (IH2 Heqm2); reflexivity.
    - move=> e IH p Heqm.
      rewrite (IH Heqm).
      reflexivity.
  Qed.

  Lemma state_eqmod_bexp s1 s2 e :
    state_eqmod (vars_bexp e) s1 s2 ->
    eval_bexp e s1 = eval_bexp e s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 Heqm.
      move: (state_eqmod_union1 Heqm) => {Heqm} [Heqm1 Heqm2].
      rewrite (state_eqmod_exp Heqm1) (state_eqmod_exp Heqm2).
      reflexivity.
    - move=> e1 e2 p Heqm.
      move: (state_eqmod_union1 Heqm) => {Heqm} [Heqm1 Heqm2].
      rewrite (state_eqmod_exp Heqm1) (state_eqmod_exp Heqm2).
      reflexivity.
    - move=> e1 IH1 e2 IH2 Heqm.
      move: (state_eqmod_union1 Heqm) => {Heqm} [Heqm1 Heqm2].
      rewrite (IH1 Heqm1) (IH2 Heqm2).
      reflexivity.
  Qed.

  Lemma state_eqmod_instr vs i s1 s2 :
    state_eqmod vs s1 s2 ->
    VS.subset (rvs_instr i) vs ->
    state_eqmod (VS.union vs (lvs_instr i)) (eval_instr s1 i) (eval_instr s2 i).
  Proof.
    elim: i => /=.
    - move=> v e Heqm Hsub x Hmem.
      case Hxv: (x == v).
      + rewrite 2!(State.acc_upd_eq _ _ Hxv).
        apply: state_eqmod_exp.
        exact: (state_eqmod_subset Heqm Hsub).
      + move/idP/negP: Hxv => Hxv.
        rewrite 2!(State.acc_upd_neq _ _ Hxv).
        apply: Heqm.
        case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
        * assumption.
        * move: (VSLemmas.mem_singleton1 Hmem) => Heq.
          apply: False_ind; apply: (negP Hxv).
          assumption.
    - move=> vh vl e p Heqm Hsub.
      set tmp := Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p).
      have: tmp = Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p) by reflexivity.
      destruct tmp as [q1 r1] => Hqr1.
      set tmp := Z.div_eucl (eval_exp e s2) (Z.pow_pos 2 p).
      have: tmp = Z.div_eucl (eval_exp e s2) (Z.pow_pos 2 p) by reflexivity.
      destruct tmp as [q2 r2] => Hqr2.
      rewrite (state_eqmod_exp (state_eqmod_subset Heqm Hsub)) in Hqr1.
      rewrite -Hqr2 in Hqr1.
      move: Hqr1 => {Hqr2} [] Hq Hr.
      rewrite {}Hq {}Hr => {q1 r1}.
      move=> v Hmem.
      case Hvvl: (v == vl).
      + rewrite 2!(State.acc_upd2_eq2 _ _ _ _ Hvvl).
        reflexivity.
      + move/idP/negP: Hvvl => Hvvl.
        case Hvvh: (v == vh).
        * rewrite 2!(State.acc_upd2_eq1 _ _ _ Hvvh Hvvl).
          reflexivity.
        * move/idP/negP: Hvvh => Hvvh.
          case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
          -- rewrite 2!(State.acc_upd2_neq _ _ _ Hvvh Hvvl).
             exact: (Heqm v Hmem).
          -- apply: False_ind.
             case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
             ++ apply: (negP Hvvh); assumption.
             ++ move: (VSLemmas.mem_singleton1 Hmem) => {Hmem} Hmem.
                apply: (negP Hvvl); assumption.
  Qed.

  Lemma state_eqmod_program vs p s1 s2 :
    well_formed_program vs p ->
    state_eqmod vs s1 s2 ->
    state_eqmod (VS.union vs (vars_program p))
                (eval_program s1 p) (eval_program s2 p).
  Proof.
    elim: p vs s1 s2 => /=.
    - move=> vs s1 s2 _ Heqm x Hmem.
      case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
      + exact: (Heqm _ Hmem).
      + rewrite VSLemmas.mem_empty in Hmem; discriminate.
    - move=> hd tl IH vs s1 s2 /andP [Hhd Htl] Heqm x Hmem.
      move: (well_formed_instr_subset_rvs Hhd) => Hsub.
      move: (state_eqmod_instr Heqm Hsub) => {Hhd Heqm} Heqm.
      move: (IH _ _ _ Htl Heqm) => {IH Heqm Htl} Heqm.
      apply: Heqm.
      case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
      [idtac | case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem].
    - apply: VSLemmas.mem_union2.
      apply: VSLemmas.mem_union2.
      assumption.
    - case: (mem_vars_instr1 Hmem) => {Hmem} Hmem.
      + apply: VSLemmas.mem_union2.
        apply: VSLemmas.mem_union3.
        assumption.
      + apply: VSLemmas.mem_union2.
        apply: VSLemmas.mem_union2.
        exact: (VSLemmas.mem_subset Hmem Hsub).
    - apply: VSLemmas.mem_union3.
      assumption.
  Qed.
*)


  (** Program slicing *)
(*
  Definition slice_instr vs i :=
    match i with
    | zAssign v e => if VS.mem v vs
                     then (VS.union (vars_exp e) (VS.remove v vs), Some i)
                     else (vs, None)
    | zSplit vh vl e p => if VS.mem vh vs || VS.mem vl vs
                          then (VS.union (vars_exp e)
                                         (VS.remove vh (VS.remove vl vs)), Some i)
                          else (vs, None)
    end.

  Fixpoint slice_program_rec vs sliced rinstrs :=
    match rinstrs with
    | [::] => (vs, sliced)
    | i::instrs =>
      match slice_instr vs i with
      | (vs', None) => slice_program_rec vs' sliced instrs
      | (vs', Some i') => slice_program_rec vs' (i'::sliced) instrs
      end
    end.

  Definition slice_program vs p :=
    slice_program_rec vs [::] (rev p).

  Definition slice_spec' s :=
    let (vs, sp) := slice_program (vars_bexp (spost s)) (sprog s) in
    (vs, {| spre := spre s;
            sprog := sp;
            spost := spost s |}).

  Definition slice_spec s := snd (slice_spec' s).

  Lemma slice_instr_some_replace vs1 vs2 vs3 i1 i2 :
    VS.Equal vs1 vs3 ->
    slice_instr vs1 i1 = (vs2, Some i2) ->
    exists vs4, slice_instr vs3 i1 = (vs4, Some i2) /\ VS.Equal vs2 vs4.
  Proof.
    case: i1 => /=.
    - move=> v e H13.
      case H1: (VS.mem v vs1).
      + move=> [Hvs Hi].
        exists (VS.union (vars_exp e) (VS.remove v vs3)); split.
        * rewrite -{1}H13 H1 Hi; reflexivity.
        * rewrite -H13 Hvs; reflexivity.
      + discriminate.
    - move=> vh vl e p H13.
      case H1: (VS.mem vh vs1 || VS.mem vl vs1).
      + move=> [Hvs Hi].
        exists (VS.union (vars_exp e) (VS.remove vh (VS.remove vl vs3))); split.
        * rewrite -{1 2}H13 H1 Hi; reflexivity.
        * rewrite -H13 Hvs; reflexivity.
      + discriminate.
  Qed.

  Lemma slice_instr_none_replace vs1 vs2 vs3 i :
    VS.Equal vs1 vs3 ->
    slice_instr vs1 i = (vs2, None) ->
    exists vs4, slice_instr vs3 i = (vs4, None) /\ VS.Equal vs2 vs4.
  Proof.
    case: i => /=.
    - move=> v e H13.
      case H1: (VS.mem v vs1).
      + discriminate.
      + move=> [Hvs].
        exists vs3; split.
        * rewrite -{1}H13 H1; reflexivity.
        * rewrite -Hvs; assumption.
    - move=> vh vl e p H13.
      case H1: (VS.mem vh vs1 || VS.mem vl vs1).
      + discriminate.
      + move=> [Hvs].
        exists vs3; split.
        * rewrite -{1 2}H13 H1; reflexivity.
        * rewrite -Hvs; assumption.
  Qed.

  Lemma slice_program_rec_replace vs1 vs2 vs3 sliced p1 p2 :
    VS.Equal vs1 vs3 ->
    slice_program_rec vs1 sliced p1 = (vs2, p2) ->
    exists vs4, slice_program_rec vs3 sliced p1 = (vs4, p2) /\ VS.Equal vs2 vs4.
  Proof.
    elim: p1 vs1 vs2 vs3 sliced p2 => /=.
    - move=> vs1 vs2 vs3 sliced p2 H13 [Hvs Hp].
      exists vs3; split.
      + rewrite Hp; reflexivity.
      + rewrite -Hvs; assumption.
    - move=> hd tl IH vs1 vs2 vs3 sliced p2 H13.
      set tmp := slice_instr vs1 hd.
      have: tmp = slice_instr vs1 hd by reflexivity.
      destruct tmp as (vs1', shd).
      case: shd.
      + move=> shd Hshd Hstl.
        move: (Logic.eq_sym Hshd) => {Hshd} Hshd.
        move: (slice_instr_some_replace H13 Hshd) => [vs4 [Hshd4 H14]].
        rewrite Hshd4.
        exact: (IH _ _ _ _ _ H14 Hstl).
      + move=> Hshd Hstl.
        move: (Logic.eq_sym Hshd) => {Hshd} Hshd.
        move: (slice_instr_none_replace H13 Hshd) => [vs4 [Hshd4 H14]].
        rewrite Hshd4.
        exact: (IH _ _ _ _ _ H14 Hstl).
  Qed.

  Lemma slice_program_replace vs1 vs2 vs3 p1 p2 :
    VS.Equal vs1 vs3 ->
    slice_program vs1 p1 = (vs2, p2) ->
    exists vs4, slice_program vs3 p1 = (vs4, p2) /\ VS.Equal vs2 vs4.
  Proof.
    exact: slice_program_rec_replace.
  Qed.

  Lemma slice_instr_some_instr vs1 vs2 i1 i2 :
    slice_instr vs1 i1 = (vs2, Some i2) ->
    i1 = i2.
  Proof.
    case: i1 => /=.
    - move=> v e; case: (VS.mem v vs1).
      + move=> [_ Hi].
        assumption.
      + discriminate.
    - move=> vh vl e p; case: (VS.mem vh vs1 || VS.mem vl vs1).
      + move=> [_ Hi].
        assumption.
      + discriminate.
  Qed.

  Lemma slice_instr_some_vars vs1 vs2 i1 i2 :
    slice_instr vs1 i1 = (vs2, Some i2) ->
    VS.Equal (VS.union (rvs_instr i1) (VS.diff vs1 (lvs_instr i1))) vs2.
  Proof.
    case: i1 => /=.
    - move=> v e; case: (VS.mem v vs1).
      + move=> [Hvs _].
        rewrite -VSLemmas.OP.P.remove_diff_singleton.
        rewrite Hvs.
        reflexivity.
      + discriminate.
    - move=> vh vl e p; case: (VS.mem vh vs1 || VS.mem vl vs1).
      + move=> [Hvs _].
        rewrite VSLemmas.diff_add.
        rewrite -VSLemmas.OP.P.remove_diff_singleton.
        rewrite Hvs.
        reflexivity.
      + discriminate.
  Qed.

  Lemma slice_instr_none vs1 vs2 i :
    slice_instr vs1 i = (vs2, None) ->
    VS.Equal vs1 vs2.
  Proof.
    case: i => /=.
    - move=> v e; case: (VS.mem v vs1).
      + discriminate.
      + move=> [Hvs]; rewrite Hvs; reflexivity.
    - move=> vh vl e p; case: (VS.mem vh vs1 || VS.mem vl vs1).
      + discriminate.
      + move=> [Hvs]; rewrite Hvs; reflexivity.
  Qed.

  Lemma slice_instr_none_lvs_disjoint vs1 vs2 i :
    slice_instr vs1 i = (vs2, None) ->
    VSLemmas.disjoint vs1 (lvs_instr i).
  Proof.
    elim: i => /=.
    - move=> v e.
      case H: (VS.mem v vs1); first by discriminate.
      move=> _.
      by rewrite VSLemmas.disjoint_singleton H.
    - move=> vh vl e p.
      case H: (VS.mem vh vs1 || VS.mem vl vs1); first by discriminate.
      move=> _.
      rewrite VSLemmas.disjoint_add.
      move/idP/negP: H.
      rewrite negb_or.
      move=> /andP [H1 H2].
      rewrite H1 /=.
      by rewrite VSLemmas.disjoint_singleton H2.
  Qed.

  Lemma slice_instr_some_subset_lvs vs vs1 vs1' p lst lst' :
    well_formed_program vs (rcons p lst) ->
    VS.subset vs1 (VS.union vs (lvs_program (rcons p lst))) ->
    slice_instr vs1 lst = (vs1', Some lst') ->
    VS.subset vs1' (VS.union vs (lvs_program p)).
  Proof.
    rewrite well_formed_program_rcons.
    move => /andP [Hp1 Hlst] Hsub Hslst.
    rewrite -(slice_instr_some_vars Hslst).
    apply: VSLemmas.subset_union3.
    -- move=> {Hsub Hslst}.
       move: (well_formed_instr_subset_rvs Hlst) => Hsub.
       apply: (VSLemmas.subset_trans Hsub).
       exact: VSLemmas.subset_refl.
    -- apply: VSLemmas.subset_union_diff1.
       apply: (VSLemmas.subset_trans Hsub).
       rewrite lvs_program_rcons.
       rewrite -VSLemmas.OP.P.union_assoc.
       rewrite (VSLemmas.OP.P.union_sym (lvs_instr lst)).
       exact: VSLemmas.subset_refl.
  Qed.

  Lemma slice_instr_some_subset_vars vs vs1 vs1' p lst lst' :
    well_formed_program vs (rcons p lst) ->
    VS.subset vs1 (VS.union vs (vars_program (rcons p lst))) ->
    slice_instr vs1 lst = (vs1', Some lst') ->
    VS.subset vs1' (VS.union vs (vars_program p)).
  Proof.
    move=> Hwell.
    rewrite (well_formed_program_vars Hwell) => Hsub Hslst.
    have: well_formed_program vs (rcons p lst) by assumption.
    rewrite well_formed_program_rcons.
    move => /andP [H _].
    rewrite (well_formed_program_vars H) => {H}.
    exact: (slice_instr_some_subset_lvs Hwell Hsub Hslst).
  Qed.

  Lemma slice_instr_none_subset_lvs vs vs1 vs1' p lst :
    VS.subset vs1 (VS.union vs (lvs_program (rcons p lst))) ->
    slice_instr vs1 lst = (vs1', None) ->
    VS.subset vs1' (VS.union vs (lvs_program p)).
  Proof.
    rewrite lvs_program_rcons.
    rewrite -VSLemmas.OP.P.union_assoc.
    move=> Hsub Hslst.
    rewrite -(slice_instr_none Hslst).
    apply: (VSLemmas.subset_union_disjoint1 Hsub).
    exact: (slice_instr_none_lvs_disjoint Hslst).
  Qed.

  Lemma slice_instr_none_subset_vars vs vs1 vs1' p lst :
    well_formed_program vs (rcons p lst) ->
    VS.subset vs1 (VS.union vs (vars_program (rcons p lst))) ->
    slice_instr vs1 lst = (vs1', None) ->
    VS.subset vs1' (VS.union vs (vars_program p)).
  Proof.
    move=> Hwell.
    rewrite (well_formed_program_vars Hwell) => Hsub Hslst.
    have: well_formed_program vs (rcons p lst) by assumption.
    rewrite well_formed_program_rcons.
    move => /andP [H _].
    rewrite (well_formed_program_vars H) => {H}.
    exact: (slice_instr_none_subset_lvs Hsub Hslst).
  Qed.

  Lemma slice_program_empty vs :
    slice_program vs [::] = (vs, [::]).
  Proof.
    reflexivity.
  Qed.

  Lemma slice_program_rec_concat vs1 vs2 vs3 p1 p2 sliced1 sliced2 sliced3 :
    slice_program_rec vs1 sliced1 p1 = (vs2, sliced2) ->
    slice_program_rec vs2 sliced2 p2 = (vs3, sliced3) ->
    slice_program_rec vs1 sliced1 (p1 ++ p2) = (vs3, sliced3).
  Proof.
    elim: p1 vs1 vs2 vs3 p2 sliced1 sliced2 sliced3 => /=.
    - move=> vs1 vs2 vs3 p2 sliced1 sliced2 sliced3 [Hvs1 Hsliced1] Hs2.
      rewrite {}Hvs1 {}Hsliced1.
      assumption.
    - move=> hd tl IH vs1 vs2 vs3 p2 sliced1 sliced2 sliced3.
      set tmp := slice_instr vs1 hd.
      have: tmp = slice_instr vs1 hd by reflexivity.
      destruct tmp as (vs1', shd).
      case: shd.
      + move=> shd Hshd Hp1 Hp2.
        exact: (IH _ _ _ _ _ _ _ Hp1 Hp2).
      + move=> Hshd Hp1 Hp2.
        exact: (IH _ _ _ _ _ _ _ Hp1 Hp2).
  Qed.

  Lemma slice_program_rec_rcons_some vs1 vs2 vs3 p sliced1 sliced2 lst slst :
    slice_program_rec vs1 sliced1 p = (vs2, sliced2) ->
    slice_instr vs2 lst = (vs3, Some slst) ->
    slice_program_rec vs1 sliced1 (rcons p lst) = (vs3, slst :: sliced2).
  Proof.
    move=> Hp Hlst.
    rewrite -cats1.
    apply: (slice_program_rec_concat Hp) => /=.
    rewrite Hlst.
    reflexivity.
  Qed.

  Lemma slice_program_rec_rcons_none vs1 vs2 vs3 p sliced1 sliced2 lst :
    slice_program_rec vs1 sliced1 p = (vs2, sliced2) ->
    slice_instr vs2 lst = (vs3, None) ->
    slice_program_rec vs1 sliced1 (rcons p lst) = (vs3, sliced2).
  Proof.
    move=> Hp Hlst.
    rewrite -cats1.
    apply: (slice_program_rec_concat Hp) => /=.
    rewrite Hlst.
    reflexivity.
  Qed.

  Lemma slice_program_rec_sliced_concat vs1 vs2 p1 p2 sliced :
    slice_program_rec vs1 sliced p1 = (vs2, p2) ->
    exists p3, p2 = p3 ++ sliced.
  Proof.
    elim: p1 vs1 vs2 p2 sliced => /=.
    - move=> vs1 vs2 p2 sliced [Hvs1 Hsliced].
      exists [::].
      rewrite Hsliced /=.
      reflexivity.
    - move=> hd tl IH vs1 vs2 p2 sliced.
      set tmp := slice_instr vs1 hd.
      have: tmp = slice_instr vs1 hd by reflexivity.
      destruct tmp as (svs1, shd).
      case: shd.
      + move=> shd Hshd Hstl.
        move: (IH _ _ _ _ Hstl) => [p3 Hp3].
        exists (rcons p3 shd).
        rewrite cat_rcons.
        exact: Hp3.
      + move=> Hshd Hstl.
        exact: (IH _ _ _ _ Hstl).
  Qed.

  Lemma slice_program_rec_sliced_vars vs1 vs2 p1 p2 sliced :
    slice_program_rec vs1 sliced p1 = (vs2, p2) ->
    VS.subset (vars_program sliced) (vars_program p2).
  Proof.
    move=> H.
    move: (slice_program_rec_sliced_concat H) => [p3 Hp3].
    rewrite Hp3 vars_program_concat.
    apply: VSLemmas.subset_union2.
    exact: VSLemmas.subset_refl.
  Qed.

  Lemma slice_program_rec_sliced_lvs vs1 vs2 p1 p2 sliced :
    slice_program_rec vs1 sliced p1 = (vs2, p2) ->
    VS.subset (lvs_program sliced) (lvs_program p2).
  Proof.
    move=> H.
    move: (slice_program_rec_sliced_concat H) => [p3 Hp3].
    rewrite Hp3 lvs_program_concat.
    apply: VSLemmas.subset_union2.
    exact: VSLemmas.subset_refl.
  Qed.

  Lemma slice_instr_some_eqmod vs1 vs2 i1 i2 s1 s2 :
    slice_instr vs1 i1 = (vs2, Some i2) ->
    state_eqmod vs2 s1 s2 ->
    state_eqmod vs1 (eval_instr s1 i1) (eval_instr s2 i2).
  Proof.
    elim: i1 vs1 vs2 i2 s1 s2 => /=.
    - move=> v e vs1 vs2 i2 s1 s2.
      case Hmemv: (VS.mem v vs1).
      + move => [Hvs Hi2] Heqm.
        rewrite -{}Hi2 /= => x Hmemx.
        case Hxv: (x == v).
        * rewrite 2!(State.acc_upd_eq _ _ Hxv).
          apply: state_eqmod_exp.
          apply: (state_eqmod_subset Heqm).
          rewrite -Hvs.
          exact: VSLemmas.union_subset_1.
        * move/idP/negP: Hxv => Hxv.
          rewrite 2!(State.acc_upd_neq _ _ Hxv).
          apply: Heqm.
          rewrite -Hvs; apply: VSLemmas.mem_union3.
          apply: (VSLemmas.mem_remove3 _ Hmemx).
          move=> Heq; apply: (negP Hxv).
          assumption.
      + discriminate.
    - move=> vh vl e p vs1 vs2 i2 s1 s2.
      set tmp := Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p).
      have: tmp = Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p) by reflexivity.
      destruct tmp as (q1, r1) => Hqr1.
      case Hmemhl: (VS.mem vh vs1 || VS.mem vl vs1).
      + move=> [Hvs Hi2] Heqm.
        rewrite -{}Hi2 /= => x Hmemx.
        have: (eval_exp e s1) = (eval_exp e s2) by
          apply: state_eqmod_exp;
          apply: (state_eqmod_subset Heqm);
          rewrite -Hvs;
          exact: VSLemmas.union_subset_1.
        move=> He; rewrite -{}He -{}Hqr1.
        case Hxvl: (x == vl).
        * rewrite 2!(State.acc_upd2_eq2 _ _ _ _ Hxvl).
          reflexivity.
        * move/idP/negP: Hxvl => Hxvl.
          case Hxvh: (x == vh).
          -- rewrite 2!(State.acc_upd2_eq1 _ _ _ Hxvh Hxvl).
             reflexivity.
          -- move/idP/negP: Hxvh => Hxvh.
             rewrite 2!(State.acc_upd2_neq _ _ _ Hxvh Hxvl).
             apply: Heqm.
             rewrite -Hvs.
             apply: VSLemmas.mem_union3.
             apply: (VSLemmas.mem_remove3 (negP Hxvh)).
             apply: (VSLemmas.mem_remove3 (negP Hxvl)).
             assumption.
      + discriminate.
  Qed.

  Lemma slice_instr_none_eqmod vs1 vs2 i s1 s2 :
    slice_instr vs1 i = (vs2, None) ->
    state_eqmod vs2 s1 s2 ->
    state_eqmod vs1 (eval_instr s1 i) s2.
  Proof.
    elim: i vs1 vs2 s1 s2 => /=.
    - move=> v e vs1 vs2 s1 s2.
      case Hmemv: (VS.mem v vs1).
      + discriminate.
      + move => [Hvs] Heqm.
        rewrite -Hvs in Heqm => {Hvs vs2}.
        move => x Hmemx.
        case Hxv: (x == v).
        * rewrite (eqP Hxv) Hmemv in Hmemx.
          discriminate.
        * move/idP/negP: Hxv => Hxv.
          rewrite (State.acc_upd_neq _ _ Hxv).
          apply: Heqm.
          assumption.
    - move=> vh vl e p vs1 vs2 s1 s2.
      set tmp := Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p).
      have: tmp = Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p) by reflexivity.
      destruct tmp as (q1, r1) => Hqr1.
      case Hmemhl: (VS.mem vh vs1 || VS.mem vl vs1).
      + discriminate.
      + move=> [Hvs] Heqm.
        rewrite -Hvs in Heqm => {Hvs vs2}.
        move => x Hmemx.
        case Hxvl: (x == vl).
        * rewrite -(eqP Hxvl) Hmemx orbT in Hmemhl.
          discriminate.
        * move/idP/negP: Hxvl => Hxvl.
          case Hxvh: (x == vh).
          -- rewrite -(eqP Hxvh) Hmemx in Hmemhl.
             discriminate.
          -- move/idP/negP: Hxvh => Hxvh.
             rewrite (State.acc_upd2_neq _ _ _ Hxvh Hxvl).
             apply: Heqm.
             assumption.
  Qed.

  Lemma slice_instr_some_cons_eqmod vs1 vs2 vs3 lst slst p sliced s1 s2 :
    slice_program_rec vs1 [::] (rev p) = (vs2, sliced) ->
    (forall t1 t2,
      state_eqmod vs2 t1 t2 ->
      state_eqmod vs1 (eval_program t1 p) (eval_program t2 sliced)
    ) ->
    slice_instr vs2 lst = (vs3, Some slst) ->
    state_eqmod vs3 s1 s2 ->
    state_eqmod vs1 (eval_program s1 (lst :: p)) (eval_program s2 (slst :: sliced)).
  Proof.
    move=> Hp IH Hlst Heqm.
    apply: IH.
    exact: (slice_instr_some_eqmod Hlst Heqm).
  Qed.

  Lemma slice_instr_none_cons_eqmod vs1 vs2 vs3 lst p sliced s1 s2 :
    slice_program_rec vs1 [::] (rev p) = (vs2, sliced) ->
    (forall t1 t2,
      state_eqmod vs2 t1 t2 ->
      state_eqmod vs1 (eval_program t1 p) (eval_program t2 sliced)
    ) ->
    slice_instr vs2 lst = (vs3, None) ->
    state_eqmod vs3 s1 s2 ->
    state_eqmod vs1 (eval_program s1 (lst :: p)) (eval_program s2 sliced).
  Proof.
    move=> Hp IH Hlst Heqm.
    apply: IH.
    exact: (slice_instr_none_eqmod Hlst Heqm).
  Qed.

  Lemma slice_program_rec_eqmod vs_beg vs_mid vs_fin sliced p11 p12 p2 s1 s2 :
    slice_program_rec vs_fin [::] (rev p12) = (vs_mid, sliced) ->
    slice_program_rec vs_mid sliced (rev p11) = (vs_beg, p2) ->
    (forall t1 t2, state_eqmod vs_mid t1 t2 ->
                   state_eqmod vs_fin (eval_program t1 p12)
                               (eval_program t2 sliced)) ->
    state_eqmod vs_beg s1 s2 ->
    state_eqmod vs_fin (eval_program s1 (p11 ++ p12)) (eval_program s2 p2).
  Proof.
    move: p11 vs_beg vs_mid vs_fin sliced p12 p2 s1 s2.
    apply: last_ind => /=.
    - move=> vs_beg vs_mid vs_fin sliced p12 p2 s1 s2 Hsp12 [Hvs_mid Hsliced]
                    Hasum Heqm.
      rewrite {}Hvs_mid {}Hsliced in Hsp12 Hasum.
      exact: (Hasum _ _ Heqm).
    - move=> p11 lst IH vs_beg vs_mid vs_fin sliced p12 p2 s1 s2
                 Hsp12 Hsp11 Hasum Heqm.
      rewrite cat_rcons.
      rewrite rev_rcons in Hsp11.
      have: slice_program_rec vs_mid sliced (lst :: rev p11) = (vs_beg, p2)
        by assumption.
      rewrite /=.
      set tmp := slice_instr vs_mid lst.
      have: tmp = slice_instr vs_mid lst by reflexivity.
      destruct tmp as (vs_mid', lst').
      case: lst'.
      + move=> lst' Hlst Hsp11'.
        apply: (IH _ _ _ _ _ _ _ _ _ Hsp11' _ Heqm).
        * rewrite rev_cons.
          exact: (slice_program_rec_rcons_some Hsp12 (Logic.eq_sym Hlst)).
        * move=> t1 t2 Heqm_mid'.
          exact: (slice_instr_some_cons_eqmod Hsp12 Hasum
                                              (Logic.eq_sym Hlst) Heqm_mid').
      + move=> Hlst Hsp11'.
        apply: (IH _ _ _ _ _ _ _ _ _ Hsp11' _ Heqm).
        * rewrite rev_cons.
          exact: (slice_program_rec_rcons_none Hsp12 (Logic.eq_sym Hlst)).
        * move=> t1 t2 Heqm_mid'.
          exact: (slice_instr_none_cons_eqmod Hsp12 Hasum
                                              (Logic.eq_sym Hlst) Heqm_mid').
  Qed.

  Lemma slice_program_eqmod vs1 vs2 p1 p2 s1 s2 :
    slice_program vs1 p1 = (vs2, p2) ->
    state_eqmod vs2 s1 s2 ->
    state_eqmod vs1 (eval_program s1 p1) (eval_program s2 p2).
  Proof.
    rewrite /slice_program.
    rewrite -{2}(cats0 p1).
    move=> Hp1 Heqm.
    apply: (slice_program_rec_eqmod _ Hp1 _ Heqm).
    - reflexivity.
    - move=> t1 t2 Heqmt.
      assumption.
  Qed.

  Lemma slice_instr_some_well_formed vs1 vs2 i1 i2 :
    instr_lvne i1 ->
    slice_instr vs1 i1 = (vs2, Some i2) ->
    well_formed_instr vs2 i2.
  Proof.
    move=> Hok Hs.
    rewrite -(slice_instr_some_instr Hs).
    apply: (instr_lvne_well_formed Hok).
    rewrite -(slice_instr_some_vars Hs).
    exact: VSLemmas.union_subset_1.
  Qed.

  Lemma slice_instr_some_cons_well_formed vs vs' i i' p :
    instr_lvne i ->
    well_formed_program vs p ->
    slice_instr vs i = (vs', Some i') ->
    well_formed_program vs' (i' :: p).
  Proof.
    move=> Hi Hp Hsi.
    apply/andP; split.
    * exact: (slice_instr_some_well_formed Hi Hsi).
    * apply: (well_formed_program_subset Hp).
      rewrite -(slice_instr_some_instr Hsi) -(slice_instr_some_vars Hsi).
      rewrite VSLemmas.OP.P.union_assoc.
      apply: VSLemmas.subset_union2.
      exact: VSLemmas.subset_union_diff3.
  Qed.

  Lemma slice_instr_none_rcons_concat_well_formed vs vs1 vs2 p lst sliced :
    well_formed_program vs (rcons p lst ++ sliced) ->
    well_formed_program vs1 sliced ->
    VS.subset vs1 (VS.union vs (vars_program (rcons p lst))) ->
    slice_instr vs1 lst = (vs2, None) ->
    well_formed_program vs (p ++ sliced).
  Proof.
    move=> Hwell1 Hwell2 Hsub Hslst.
    rewrite well_formed_program_concat.
    apply/andP; split; first by
        exact: (well_formed_program_rcons1 (well_formed_program_concat1 Hwell1)).
    apply: (well_formed_program_subset Hwell2).
    move: Hsub.
    rewrite (well_formed_program_vars (well_formed_program_concat1 Hwell1)) =>
    Hsub.
    rewrite (slice_instr_none Hslst).
    exact: (slice_instr_none_subset_lvs Hsub Hslst).
  Qed.

  Lemma slice_program_rec_well_formed vs1 vs2 p sliced1 sliced2 :
    program_lvne p ->
    well_formed_program vs1 sliced1 ->
    slice_program_rec vs1 sliced1 p = (vs2, sliced2) ->
    well_formed_program vs2 sliced2.
  Proof.
    elim: p vs1 vs2 sliced1 sliced2 => /=.
    - move=> vs1 vs2 sliced1 sliced2 _ Hwell1 [Hvs1 Hsliced1].
      rewrite -Hvs1 -Hsliced1; exact: Hwell1.
    - move=> hd tl IH vs1 vs2 sliced1 sliced2 /andP [Hokhd Hoktl] Hwell1.
      set tmp := slice_instr vs1 hd.
      have: tmp = slice_instr vs1 hd by reflexivity.
      destruct tmp as (svs1, shd).
      case: shd.
      + move=> shd Hshd Hstl.
        move: (Logic.eq_sym Hshd) => {Hshd} Hshd.
        apply: (IH _ _ _ _ Hoktl _ Hstl).
        exact: (slice_instr_some_cons_well_formed Hokhd Hwell1 Hshd).
      + move=> Hshd Hstl.
        apply: (IH _ _ _ _ Hoktl _ Hstl).
        move: (Logic.eq_sym Hshd) => {Hshd} Hshd.
        apply: (well_formed_program_replace Hwell1).
        rewrite -(slice_instr_none Hshd).
        reflexivity.
  Qed.

  Lemma slice_program_well_formed vs1 vs2 p sliced :
    program_lvne p ->
    slice_program vs1 p = (vs2, sliced) ->
    well_formed_program vs2 sliced.
  Proof.
    move=> Hokp Hsp.
    rewrite /slice_program in Hsp.
    apply: (slice_program_rec_well_formed _ _ Hsp).
    - rewrite -program_lvne_rev.
      assumption.
    - done.
  Qed.

  Lemma slice_program_rec_subset vs vs1 vs2 sliced p1 p2 :
    well_formed_program vs (p1 ++ sliced) ->
    well_formed_program vs1 sliced ->
    VS.subset vs1 (VS.union vs (vars_program p1)) ->
    slice_program_rec vs1 sliced (rev p1) = (vs2, p2) ->
    VS.subset vs2 vs.
  Proof.
    move: p1 vs vs1 vs2 sliced p2.
    apply: last_ind => /=.
    - move=> vs vs1 vs2 sliced p2 Hwell1 Hwell2 Hsub [Hvs1 Hsliced].
      rewrite -{}Hvs1.
      apply: (VSLemmas.subset_trans Hsub).
      rewrite VSLemmas.union_emptyr.
      exact: VSLemmas.subset_refl.
    - move=> p1 lst IH vs vs1 vs2 sliced p2 Hwell1 Hwell2 Hsub.
      have: well_formed_program vs (rcons p1 lst ++ sliced) by exact: Hwell1.
      move=> Htmp.
      rewrite cat_rcons well_formed_program_concat in Htmp.
      move/andP: Htmp => [Hp1 /andP [Hlst Hsliced]].
      rewrite rev_rcons /=.
      set tmp := slice_instr vs1 lst.
      have: tmp = slice_instr vs1 lst by reflexivity.
      destruct tmp as (vs1', lst').
      case: lst'.
      + move=> lst' Hlst' Hsp1.
        move: (Logic.eq_sym Hlst') => {Hlst'} Hlst'.
        apply: (IH _ _ _ _ _ _ _ _ Hsp1).
        * rewrite -cat_rcons -(slice_instr_some_instr Hlst').
          exact: Hwell1.
        * exact: (slice_instr_some_cons_well_formed
                    (well_formed_instr_lvne Hlst) Hwell2 Hlst').
        * exact: (slice_instr_some_subset_vars
                    (well_formed_program_concat1 Hwell1) Hsub Hlst').
      + move=> Hslst Hsp1.
        move: (Logic.eq_sym Hslst) => {Hslst} Hslst.
        (* start have *)
        have: VS.subset vs1 (VS.union vs (lvs_program p1)).
        move: Hsub.
        rewrite (well_formed_program_vars (well_formed_program_concat1 Hwell1)) =>
        Hsub.
        rewrite (slice_instr_none Hslst).
        exact: (slice_instr_none_subset_lvs Hsub Hslst).
        (* end have *)
        move=> Hsub1.
        apply: (IH _ _ _ _ _ _ _ _ Hsp1).
        * exact: (slice_instr_none_rcons_concat_well_formed Hwell1 Hwell2 Hsub Hslst).
        * apply: (well_formed_program_replace Hwell2).
          rewrite (slice_instr_none Hslst).
          reflexivity.
        * exact: (slice_instr_none_subset_vars (well_formed_program_concat1 Hwell1) Hsub Hslst).
  Qed.

  Lemma slice_program_subset vs vs1 vs2 p1 p2 :
    well_formed_program vs p1 ->
    VS.subset vs1 (VS.union vs (vars_program p1)) ->
    slice_program vs1 p1 = (vs2, p2) ->
    VS.subset vs2 vs.
  Proof.
    rewrite /slice_program.
    move=> Hwell Hsub Hsp1.
    rewrite -(cats0 p1) in Hwell.
    by apply: (slice_program_rec_subset Hwell _ Hsub Hsp1).
  Qed.

  Lemma slice_program_rec_lvs_sliced vs vs1 vs2 p1 p2 sliced :
    well_formed_program vs (p1 ++ sliced) ->
    well_formed_program vs1 sliced ->
    VS.subset vs1 (VS.union vs (lvs_program p1)) ->
    slice_program_rec vs1 sliced (rev p1) = (vs2, p2) ->
    VS.subset vs1 (VS.union vs (lvs_program p2)).
  Proof.
    move: p1 vs vs1 vs2 p2 sliced.
    apply: last_ind => /=.
    - move=> vs vs1 vs2 p2 sliced.
      rewrite VSLemmas.union_emptyr.
      move=> _ _ Hsub _.
      apply: VSLemmas.subset_union1.
      assumption.
    - move=> p1 lst IH vs vs1 vs2 p2 sliced Hwell1 Hwell2 Hsub.
      rewrite rev_rcons /=.
      set tmp := slice_instr vs1 lst.
      have: tmp = slice_instr vs1 lst by reflexivity.
      destruct tmp as (vs1', lst').
      case: lst'.
      + move=> lst' Hslst Hsp1.
        move: (Logic.eq_sym Hslst) => {Hslst} Hslst.
        move: (slice_instr_some_subset_lvs
                 (well_formed_program_concat1 Hwell1) Hsub Hslst) => Hsub'.
        rewrite cat_rcons in Hwell1.
        (* start have *)
        have: well_formed_program vs1' (lst' :: sliced).
        apply: (slice_instr_some_cons_well_formed _ Hwell2 Hslst).
        exact: (well_formed_instr_lvne
                  (well_formed_program_cons1 (well_formed_program_concat2 Hwell1))).
        (* end have *)
        move=> Hwell'.
        rewrite -(slice_instr_some_instr Hslst) in Hwell' Hsp1.
        move: (IH vs vs1' vs2 p2 (lst::sliced) Hwell1 Hwell' Hsub' Hsp1).
        rewrite -(slice_instr_some_vars Hslst).
        move=> H.
        move: (VSLemmas.subset_union_diff4 (VSLemmas.subset_union5 H)) => {H} H.
        (* start have *)
        have: VS.subset (lvs_instr lst) (VS.union vs (lvs_program p2)).
        apply: VSLemmas.subset_union2.
        exact: (VSLemmas.subset_union4 (slice_program_rec_sliced_lvs Hsp1)).
        (* end have *)
        move=> H1.
        move: H; rewrite (VSLemmas.union_subset_equal H1).
        by apply.
      + move=> Hslst Hsp1.
        move: (Logic.eq_sym Hslst) => {Hslst} Hslst.
        move: (VSLemmas.OP.P.equal_sym (slice_instr_none Hslst)) => Heq1.
        move: (slice_program_rec_replace Heq1 Hsp1) => [vs2' [Hsp1' Heq2]].
        apply: (IH _ _ vs2' _ _ _ Hwell2 _ Hsp1').
        * move: Hsub;
          rewrite -(well_formed_program_vars (well_formed_program_concat1 Hwell1)) =>
          Hsub.
          exact: (slice_instr_none_rcons_concat_well_formed Hwell1 Hwell2 Hsub Hslst).
        * rewrite (slice_instr_none Hslst).
          exact: (slice_instr_none_subset_lvs Hsub Hslst).
  Qed.

  Lemma slice_program_rec_vars_sliced vs vs1 vs2 p1 p2 sliced :
    well_formed_program vs (p1 ++ sliced) ->
    well_formed_program vs1 sliced ->
    VS.subset vs1 (VS.union vs (vars_program p1)) ->
    slice_program_rec vs1 sliced (rev p1) = (vs2, p2) ->
    VS.subset vs1 (VS.union vs (vars_program p2)).
  Proof.
    move=> Hwell1 Hwell2 Hsub Hsp1.
    move: Hsub;
      rewrite (well_formed_program_vars (well_formed_program_concat1 Hwell1)) => H.
    move: (slice_program_rec_lvs_sliced Hwell1 Hwell2 H Hsp1) => {H} H.
    rewrite vars_program_split.
    rewrite -VSLemmas.OP.P.union_assoc.
    apply: VSLemmas.subset_union1.
    assumption.
  Qed.

  Lemma slice_program_lvs_sliced vs vs1 vs2 p1 p2 :
    well_formed_program vs p1 ->
    VS.subset vs1 (VS.union vs (lvs_program p1)) ->
    slice_program vs1 p1 = (vs2, p2) ->
    VS.subset vs1 (VS.union vs (lvs_program p2)).
  Proof.
    rewrite /slice_program.
    rewrite -{1}(cats0 p1).
    move=> Hwell Hsub Hslice.
    exact: (slice_program_rec_lvs_sliced Hwell _ Hsub Hslice).
  Qed.

  Lemma slice_program_vars_sliced vs vs1 vs2 p1 p2 :
    well_formed_program vs p1 ->
    VS.subset vs1 (VS.union vs (vars_program p1)) ->
    slice_program vs1 p1 = (vs2, p2) ->
    VS.subset vs1 (VS.union vs (vars_program p2)).
  Proof.
    rewrite /slice_program.
    rewrite -{1}(cats0 p1).
    move=> Hwell Hsub Hslice.
    exact: (slice_program_rec_vars_sliced Hwell _ Hsub Hslice).
  Qed.
*)


  (** Well-formedness and soundness of program slicing *)
(*
  Theorem slice_spec_well_formed vs s :
    well_formed_spec vs s ->
    well_formed_spec vs (slice_spec s).
  Proof.
    destruct s as [f p g].
    rewrite /slice_spec /slice_spec' /well_formed_spec /=.
    set tmp := slice_program (vars_bexp g) p.
    have: tmp = slice_program (vars_bexp g) p by reflexivity.
    destruct tmp as (svs, sp).
    move=> /= Hs /andP [/andP [Hf Hp] Hg].
    move: (Logic.eq_sym Hs) => {Hs} Hs.
    apply/andP; split; first (apply/andP; split).
    - assumption.
    - apply: (well_formed_program_subset
                (slice_program_well_formed (well_formed_program_lvne Hp) Hs)).
      exact: (slice_program_subset Hp Hg Hs).
    - exact: (slice_program_vars_sliced Hp Hg Hs).
  Qed.

  Theorem slice_spec_sound s :
    valid_spec (slice_spec s) -> valid_spec s.
  Proof.
    destruct s as [f p g].
    rewrite /slice_spec /slice_spec' /=.
    set tmp := slice_program (vars_bexp g) p.
    have: tmp = slice_program (vars_bexp g) p by reflexivity.
    destruct tmp as (vs', p') => /=.
    move=> Hsp Hs s1 s2 /= Hf Hp.
    rewrite -{}Hp.
    move: (Logic.eq_sym Hsp) => {Hsp} Hsp.
    move: (slice_program_eqmod Hsp (state_eqmod_refl s1)) => Heqm.
    move: (Hs s1 (eval_program s1 p') Hf
              (Logic.eq_refl (eval_program s1 p'))) => /= Hg.
    rewrite (state_eqmod_bexp Heqm).
    assumption.
  Qed.

  Theorem slice_spec_complete s :
    valid_spec s -> valid_spec (slice_spec s).
  Proof.
    destruct s as [f p g].
    rewrite /slice_spec /slice_spec' /=.
    set tmp := slice_program (vars_bexp g) p.
    have: tmp = slice_program (vars_bexp g) p by reflexivity.
    destruct tmp as (vs', p') => /=.
    move=> Hsp Hs s1 s2 /= Hf Hp.
    rewrite -{}Hp.
    move: (Logic.eq_sym Hsp) => {Hsp} Hsp.
    move: (slice_program_eqmod Hsp (state_eqmod_refl s1)) => Heqm.
    move: (Hs s1 (eval_program s1 p) Hf
              (Logic.eq_refl (eval_program s1 p))) => /= Hg.
    rewrite -(state_eqmod_bexp Heqm).
    assumption.
  Qed.
*)


  (** Precondition slicing *)
(*
  Fixpoint slice_bexp vs e : bexp :=
    match e with
    | zTrue => e
    | zEq e1 e2 =>
      if VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2))
      then zTrue
      else e
    | zEqMod e1 e2 p =>
      if VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2))
      then zTrue
      else e
    | zAnd e1 e2 => zAnd (slice_bexp vs e1) (slice_bexp vs e2)
    end.

  Fixpoint split_qands e : seq bexp :=
    match e with
    | zTrue => [::]
    | zEq _ _ => [:: e]
    | zEqMod _ _ _ => [:: e]
    | zAnd e1 e2 => (split_qands e1) ++ (split_qands e2)
    end.

  Fixpoint related_vars_bexp_once vs es :=
    match es with
    | [::] => vs
    | hd::tl => if VSLemmas.disjoint vs (vars_bexp hd)
                then related_vars_bexp_once vs tl
                else related_vars_bexp_once (VS.union vs (vars_bexp hd)) tl
    end.

  Fixpoint related_vars_bexp_rec n vs es :=
    match n with
    | 0%nat => vs
    | S m =>
      let vs' := related_vars_bexp_once vs es in
      if Nat.eqb (VS.cardinal vs) (VS.cardinal vs')
      then vs'
      else related_vars_bexp_rec m vs' es
    end.

  Lemma eval_slice_bexp vs e s :
    eval_bexp e s ->
    eval_bexp (slice_bexp vs e) s.
  Proof.
    elim: e vs s => /=.
    - done.
    - move=> e1 e2 vs s He.
      case: (VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2)));
        first by done.
      exact: He.
    - move=> e1 e2 p vs s Hm.
      case: (VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2)));
        first by done.
      exact: Hm.
    - move=> e1 IH1 e2 IH2 vs s [H1 H2].
      split; [exact: (IH1 _ _ H1) | exact: (IH2 _ _ H2)].
  Qed.

  Lemma slice_bexp_vars vs e :
    VS.subset (vars_bexp (slice_bexp vs e)) (vars_bexp e).
  Proof.
    elim: e => /=.
    - exact: VSLemmas.subset_refl.
    - move=> e1 e2.
      case: (VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2))) => /=.
      + exact: VSLemmas.subset_empty.
      + exact: VSLemmas.subset_refl.
    - move=> e1 e2 p.
      case: (VSLemmas.disjoint vs (VS.union (vars_exp e1) (vars_exp e2))) => /=.
      + exact: VSLemmas.subset_empty.
      + exact: VSLemmas.subset_refl.
    - move=> e1 IH1 e2 IH2.
      by apply: VSLemmas.union_subsets.
  Qed.

  Definition slice_pre vs s : spec :=
    {| spre := slice_bexp vs (spre s);
       sprog := sprog s;
       spost := spost s |}.

  Lemma slice_pre_well_formed vs1 vs2 s :
    well_formed_spec vs1 s ->
    well_formed_spec vs1 (slice_pre vs2 s).
  Proof.
    destruct s as (f, p, g).
    rewrite /well_formed_spec /=.
    move=> /andP [/andP [Hf Hp] Hg].
    apply/andP; split; first (apply/andP; split).
    - apply: (VSLemmas.subset_trans _ Hf).
      exact: slice_bexp_vars.
    - assumption.
    - assumption.
  Qed.

  Lemma slice_pre_sound vs s :
    valid_spec (slice_pre vs s) -> valid_spec s.
  Proof.
    destruct s as (f, p, g).
    rewrite /valid_spec /slice_pre /=.
    move=> H s1 s2 Hf Hp.
    apply: (H _ _ _ Hp).
    exact: (eval_slice_bexp _ Hf).
  Qed.

  (* Slice program and then precondition. *)
  Definition zslice s : spec :=
    let (vs, ss) := slice_spec' s in
    let vs' := related_vars_bexp_rec (VS.cardinal (vars_bexp (spre ss)))
                                     vs (split_qands (spre ss)) in
    slice_pre vs' ss.

  Lemma zslice_well_formed vs s :
    well_formed_spec vs s ->
    well_formed_spec vs (zslice s).
  Proof.
    destruct s as (f, p, g).
    rewrite /zslice.
    set tmp := slice_spec' ({{f}} p {{g}}).
    have: tmp = slice_spec' ({{f}} p {{g}}) by reflexivity.
    destruct tmp as (xs, ss).
    move=> Hss Hwell.
    apply: slice_pre_well_formed.
    move: (slice_spec_well_formed Hwell).
    rewrite /slice_spec -Hss /=.
    by apply.
  Qed.

  Lemma zslice_sound s :
    valid_spec (zslice s) -> valid_spec s.
  Proof.
    destruct s as (f, p, g).
    rewrite /zslice.
    set tmp := slice_spec' ({{f}} p {{g}}).
    have: tmp = slice_spec' ({{f}} p {{g}}) by reflexivity.
    destruct tmp as (xs, ss).
    move=> Hss Hsp.
    apply: slice_spec_sound.
    rewrite /slice_spec -Hss /=.
    exact: (slice_pre_sound Hsp).
  Qed.
*)
End MakeBVDSL.

Module bv64DSL := MakeBVDSL AMD64 VarOrder.
Export bv64DSL.
Arguments bv64DSL.bvVar v%N.

(*Notation "@- x" := (bvNeg x) (at level 35, right associativity) : bvdsl_scope.*)
Notation "x @+ y" := (bvBinop bvAddOp x y) (at level 50, left associativity) : bvdsl_scope.
Notation "x @- y" := (bvBinop bvSubOp x y)  (at level 50, left associativity) : bvdsl_scope.
Notation "x @* y" := (bvBinop bvMulOp x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x @:= y" := (bvAssign x%N y) (at level 70, no associativity) : bvdsl_scope.
Notation "x @= y" := (bvEq x y) (at level 70, no associativity) : bvdsl_scope.
Notation "x @= y 'mod' z" := (bvEqMod x y z) (at level 70, y at next level, no associativity) : bvdsl_scope.
Notation "x @&& y" := (bvAnd x y) (at level 70, no associativity) : bvdsl_scope.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : bvdsl_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : bvdsl_scope.
Notation "{{ f }} p {{ g }}" := ({| spre := f; sprog := p; spost := g |}) (at level 82, no associativity) : bvdsl_scope.
Notation "|= s" := (valid_spec s) (at level 83, no associativity) : bvdsl_scope.
