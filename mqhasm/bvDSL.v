
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

Module MakeBVDSL (A : ARCH) (V : SsrOrderedType) (VS : SsrFSet with Module E := V).

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
  | bvSubC : var -> var -> atomic -> atomic -> instr
  | bvSbb : var -> atomic -> atomic -> var -> instr
  | bvSbbC : var -> var -> atomic -> atomic -> var -> instr
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
    | bvSubC c v e1 e2
    | bvSbb v e1 e2 c =>
      VS.add c (VS.add v (VS.union (vars_atomic e1) (vars_atomic e2)))
    | bvAdcC c v e1 e2 y
    | bvSbbC c v e1 e2 y =>
      VS.add y (VS.add c (VS.add v (VS.union (vars_atomic e1) (vars_atomic e2))))
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
    | bvSbb v _ _ _
    | bvMul v _ _
    | bvShl v _ _ => VS.singleton v
    | bvAddC c v _ _
    | bvAdcC c v _ _ _
    | bvSubC c v _ _
    | bvSbbC c v _ _ _ => VS.add c (VS.singleton v)
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
    | bvAdcC _ _ e1 e2 c
    | bvSbb _ e1 e2 c
    | bvSbbC _ _ e1 e2 c => VS.add c (VS.union (vars_atomic e1) (vars_atomic e2))
    | bvAdd _ e1 e2
    | bvAddC _ _ e1 e2
    | bvSub _ e1 e2
    | bvSubC _ _ e1 e2
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
    elim : i => /=; move=> *; by VSLemmas.dp_Equal.
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
      have: VS.Equal (VS.union (VS.union (lvs_instr hd) (lvs_program tl))
                               (VS.union (rvs_instr hd) (rvs_program tl)))
                     (VS.union (VS.union (lvs_instr hd) (rvs_instr hd))
                               (VS.union (lvs_program tl) (rvs_program tl))) by
          VSLemmas.dp_Equal.
      move=> ->. rewrite -IH. rewrite -vars_instr_split. reflexivity.
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

  Module IntType <: Equalities.Typ.
    Definition t : Set := int.
  End IntType.

  Module State := TStoreAdapter V IntType.



  (** Semantics *)

  Definition eval_atomic (a : atomic) (s : State.t) : value :=
    match a with
    | bvVar v => State.acc v s
    | bvConst n => n
    end.

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
      State.upd2 v
                 (low A.wordsize
                      (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                            (zeroExtend A.wordsize (eval_atomic e2 s))))
                 c
                 (high A.wordsize
                       (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                             (zeroExtend A.wordsize (eval_atomic e2 s))))
                 s
    | bvAdc v e1 e2 y =>
      State.upd v
                (addB (addB (eval_atomic e1 s) (eval_atomic e2 s))
                      (State.acc y s))
                s
    | bvAdcC c v e1 e2 y =>
      State.upd2 v
                 (low A.wordsize
                      (addB
                         (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                               (zeroExtend A.wordsize (eval_atomic e2 s)))
                         (zeroExtend A.wordsize (State.acc y s))))
                 c
                 (high A.wordsize
                       (addB
                          (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                                (zeroExtend A.wordsize (eval_atomic e2 s)))
                          (zeroExtend A.wordsize (State.acc y s))))
                 s
    | bvSub v e1 e2 => State.upd v (subB (eval_atomic e1 s) (eval_atomic e2 s)) s
    | bvSubC c v e1 e2 =>
      State.upd2 v
                 (low A.wordsize
                      (subB (zeroExtend A.wordsize (eval_atomic e1 s))
                            (zeroExtend A.wordsize (eval_atomic e2 s))))
                 c
                 (negB
                    (high A.wordsize
                          (subB (zeroExtend A.wordsize (eval_atomic e1 s))
                                (zeroExtend A.wordsize (eval_atomic e2 s)))))
                 s
    | bvSbb v e1 e2 y =>
      State.upd v
                (subB (subB (eval_atomic e1 s) (eval_atomic e2 s))
                      (State.acc y s))
                s
    | bvSbbC c v e1 e2 y =>
      State.upd2 v
                 (low A.wordsize
                       (subB
                          (subB (zeroExtend A.wordsize (eval_atomic e1 s))
                                (zeroExtend A.wordsize (eval_atomic e2 s)))
                          (zeroExtend A.wordsize (State.acc y s))))
                 c
                 (negB
                    (high A.wordsize
                          (subB
                             (subB (zeroExtend A.wordsize (eval_atomic e1 s))
                                   (zeroExtend A.wordsize (eval_atomic e2 s)))
                             (zeroExtend A.wordsize (State.acc y s)))))
                 s
    | bvMul v e1 e2 => State.upd v (mulB (eval_atomic e1 s) (eval_atomic e2 s)) s
    | bvMulf vh vl e1 e2 =>
      State.upd2 vl
                 (low A.wordsize
                      (fullmulB (eval_atomic e1 s) (eval_atomic e2 s)))
                 vh
                 (high A.wordsize
                       (fullmulB (eval_atomic e1 s) (eval_atomic e2 s)))
                 s
    | bvShl v e p => State.upd v (shlBn (eval_atomic e s) (toNat p)) s
    | bvSplit vh vl e p =>
      State.upd2 vl (snd (split_ext (eval_atomic e s) (toNat p)))
                 vh (fst (split_ext (eval_atomic e s) (toNat p)))
                 s
    | bvConcatShl vh vl e1 e2 p =>
      State.upd2 vl (snd (concat_shl (eval_atomic e1 s)
                                     (eval_atomic e2 s) (toNat p)))
                 vh (fst (concat_shl (eval_atomic e1 s)
                                     (eval_atomic e2 s) (toNat p)))
                 s
    end.

  Inductive succ_instr (s : State.t) : instr -> State.t -> Prop :=
  | succAssign v e :
      succ_instr s (bvAssign v e)
           (State.upd v (eval_atomic e s) s)
  | succAdd v e1 e2 :
      succ_instr s (bvAdd v e1 e2)
           (State.upd v (addB (eval_atomic e1 s) (eval_atomic e2 s)) s)
  | succAddC c v e1 e2 :
      succ_instr s (bvAddC c v e1 e2)
           (State.upd2
              c (high A.wordsize
                      (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                            (zeroExtend A.wordsize (eval_atomic e2 s))))
              v (low A.wordsize
                     (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                           (zeroExtend A.wordsize (eval_atomic e2 s))))
              s)
  | succAdc v e1 e2 c :
      succ_instr s (bvAdc v e1 e2 c)
           (State.upd
              v (low A.wordsize
                     (addB
                        (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                              (zeroExtend A.wordsize (eval_atomic e2 s)))
                        (zeroExtend A.wordsize (State.acc c s))))
              s)
  | succAdcC c v e1 e2 a :
      succ_instr s (bvAdcC c v e1 e2 a)
           (State.upd2
              c (high A.wordsize
                      (addB
                         (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                               (zeroExtend A.wordsize (eval_atomic e2 s)))
                         (zeroExtend A.wordsize (State.acc a s))))
              v (low A.wordsize
                     (addB
                        (addB (zeroExtend A.wordsize (eval_atomic e1 s))
                              (zeroExtend A.wordsize (eval_atomic e2 s)))
                        (zeroExtend A.wordsize (State.acc a s))))
              s)
  | succSub v e1 e2 :
      succ_instr s (bvSub v e1 e2)
           (State.upd v (subB (eval_atomic e1 s) (eval_atomic e2 s)) s)
(*
  | succSubC c v e1 e2 : 
      succ_instr s (bvSubC c v e1 e2)
           (State.upd2 
              c (if carry_subB (eval_atomic e1 s) (eval_atomic e2 s) then bvone else bvzero)
              v (subB (eval_atomic e1 s) (eval_atomic e2 s))
              s)
*)
  | succMul v e1 e2 :
      succ_instr s (bvMul v e1 e2)
           (State.upd v (mulB (eval_atomic e1 s) (eval_atomic e2 s)) s)
  | succMulf vh vl e1 e2 :
      succ_instr s (bvMulf vh vl e1 e2)
           (State.upd2
              vh (high A.wordsize (fullmulB (eval_atomic e1 s)
                                            (eval_atomic e2 s)))
              vl (low A.wordsize (fullmulB (eval_atomic e1 s)
                                           (eval_atomic e2 s)))
              s)
  | succShl v e p :
      succ_instr s (bvShl v e p)
           (State.upd v (shlBn (eval_atomic e s) (toNat p)) s)
  | succSplit vh vl e p :
      succ_instr s (bvSplit vh vl e p)
           (State.upd2
              vh (fst (split_ext (eval_atomic e s) (toNat p)))
              vl (snd (split_ext (eval_atomic e s) (toNat p)))
              s)
  | succConcatShl vh vl e1 e2 p :
      succ_instr s (bvConcatShl vh vl e1 e2 p)
           (State.upd2
              vh (fst (concat_shl (eval_atomic e1 s)
                                  (eval_atomic e2 s) (toNat p)))
              vl (snd (concat_shl (eval_atomic e1 s)
                                  (eval_atomic e2 s) (toNat p)))
              s) .

  Fixpoint succ_program (s : State.t) (p: program) (t : State.t) : Prop :=
    match p with
      | [::] => s = t
      | hd::tl => exists r, succ_instr s hd r /\ succ_program r tl t
    end .
  
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

  Lemma succ_program_singleton :
    forall (i : instr) (s1 s2 : State.t),
      succ_program s1 [:: i] s2 -> succ_instr s1 i s2 .
  Proof .
    move=> i s1 s2 H .
    case: H .
    simpl .
    move=> x [] => H0 H1 .
    by rewrite H1 in H0 .
  Qed .

  Lemma succ_singleton_program :
    forall (i : instr) (s1 s2 : State.t),
      succ_instr s1 i s2 -> succ_program s1 [:: i] s2 .
  Proof .
    move=> i s1 s2 H => /= .
    by exists s2 .
  Qed .

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

  Lemma succ_program_cons :
    forall (hd : instr) (tl : program) (s1 s2 : State.t),
      succ_program s1 (hd::tl) s2 ->
      exists s3 : State.t,
        succ_instr s1 hd s3 /\ succ_program s3 tl s2 .
  Proof .
    by [] .
  Qed .
    
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

  Lemma succ_program_concat :
    forall (p1 p2 : program) (s1 s2 s3 : State.t),
      succ_program s1 p1 s2 ->
      succ_program s2 p2 s3 ->
      succ_program s1 (p1 ++ p2) s3 .
  Proof .
    move => p1; elim p1 => /= .
    - move => p2 s1 s2 s3 Heq Hsucc .
      rewrite Heq //= .
    - move => hd tl Hind p2 s1 s2 s3 [] => x [] => Hsucchd Hsucctl Hsuccp2 .
      exists x; split => //= .
      by apply: (Hind p2 x s2 s3) .
  Qed .
      
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

  Lemma succ_program_split :
    forall (p1 p2 : program) (s1 s2 : State.t),
      succ_program s1 (p1 ++ p2) s2 ->
      exists s3, succ_program s1 p1 s3 /\ succ_program s3 p2 s2 .
  Proof .
    move => p1; elim: p1 .
    - move => p2 s1 s2 Hsucc .
      exists s1; split => // .
    - move => hd tl Hind p2 s1 s2 Hsucc .
      move: (succ_program_cons Hsucc) => {Hsucc} [s3 [Hsucchd Hsucctl]] .
      move: (Hind _ _ _ Hsucctl) => {Hsucctl} [s4 [Hsucctl Hsuccp2]] .
      exists s4; split => // .
      simpl .
      by exists s3 .
  Qed .
  
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

  Inductive eexp : Type :=
  | bveVar : var -> eexp
  | bveConst : Z -> eexp
  | bveUnop : unop -> eexp -> eexp
  | bveBinop : binop -> eexp -> eexp -> eexp.

  Definition bvevar v := bveVar v.
  Definition bveconst n := bveConst n.
  Definition bvconst n := bveconst n.
  Definition bveneg (e : eexp) := bveUnop bvNegOp e.
  Definition bveadd (e1 e2 : eexp) := bveBinop bvAddOp e1 e2.
  Definition bvesub (e1 e2 : eexp) := bveBinop bvSubOp e1 e2.
  Definition bvemul (e1 e2 : eexp) := bveBinop bvMulOp e1 e2.
  Definition bvesq (e : eexp) := bveBinop bvMulOp e e.
  Fixpoint bveadds (es : seq eexp) : eexp :=
    match es with
    | [::] => bveconst 0
    | e::[::] => e
    | hd::tl => bveadd hd (bveadds tl)
    end.
  Fixpoint bvemuls (es : seq eexp) : eexp :=
    match es with
    | [::] => bveconst 0
    | e::[::] => e
    | hd::tl => bvemul hd (bvemuls tl)
    end.
  Definition bve2pow n := Zpower_nat 2 n.

  Inductive rexp : nat -> Type :=
  | bvrVar : var -> rexp A.wordsize
  | bvrConst : forall n : nat, BITS n -> rexp n
  | bvrBinop : forall n : nat, binop -> rexp n -> rexp n -> rexp n
  | bvrExt : forall n : nat, rexp n -> forall m : nat, rexp (n + m).

  Definition bvrvar v := bvrVar v.
  Definition bvrposz {w} n := bvrConst (@fromPosZ w n).
  Definition bvposz {w} n := @bvrposz w n.
  Definition bvradd w (e1 e2 : rexp w) := bvrBinop bvAddOp e1 e2.
  Definition bvrsub w (e1 e2 : rexp w) := bvrBinop bvSubOp e1 e2.
  Definition bvrmul w (e1 e2 : rexp w) := bvrBinop bvMulOp e1 e2.
  Definition bvrsq w (e : rexp w) := bvrBinop bvMulOp e e.
  Fixpoint bvradds w (es : seq (rexp w)) : rexp w :=
    match es with
    | [::] => bvrposz 0
    | e::[::] => e
    | hd::tl => bvradd hd (bvradds tl)
    end.
  Fixpoint bvrmuls w (es : seq (rexp w)) : rexp w :=
    match es with
    | [::] => bvrposz 0
    | e::[::] => e
    | hd::tl => bvrmul hd (bvrmuls tl)
    end.

  Inductive ebexp :=
  | bveTrue : ebexp
  | bveEq : eexp -> eexp -> ebexp
  | bveEqMod : eexp -> eexp -> eexp -> ebexp
  | bveAnd : ebexp -> ebexp -> ebexp.

  Definition bveand e1 e2 : ebexp :=
    match e1, e2 with
    | bveTrue, _ => e2
    | _, bveTrue => e1
    | _, _ => bveAnd e1 e2
    end.

  Fixpoint bveands es : ebexp :=
    match es with
    | [::] => bveTrue
    | hd::[::] => hd
    | hd::tl => bveand hd (bveands tl)
    end.

  Inductive rbexp :=
  | bvrTrue : rbexp
  | bvrCmp : forall n : nat, cmpop -> rexp n -> rexp n -> rbexp
  | bvrAnd : rbexp -> rbexp -> rbexp.

  Definition bvult w (e1 e2 : rexp w) := bvrCmp bvUltOp e1 e2.
  Definition bvule w (e1 e2 : rexp w) := bvrCmp bvUleOp e1 e2.
  Definition bvugt w (e1 e2 : rexp w) := bvrCmp bvUgtOp e1 e2.
  Definition bvuge w (e1 e2 : rexp w) := bvrCmp bvUgeOp e1 e2.

  Definition bvrand e1 e2 : rbexp :=
    match e1, e2 with
    | bvrTrue, _ => e2
    | _, bvrTrue => e1
    | _, _ => bvrAnd e1 e2
    end.

  Fixpoint bvrands es : rbexp :=
    match es with
    | [::] => bvrTrue
    | hd::[::] => hd
    | hd::tl => bvrand hd (bvrands tl)
    end.

  Definition bexp : Type := (ebexp * rbexp).

  Definition bvTrue : bexp := (bveTrue, bvrTrue).

  Definition eqn_bexp (e : bexp) : ebexp := fst e.
  Definition rng_bexp (e : bexp) : rbexp := snd e.

  Coercion singleton_ebexp e : bexp := (e, bvrTrue).
  Coercion singleton_rbexp e : bexp := (bveTrue, e).

  Fixpoint bvand e1 e2 : bexp :=
    match e1, e2 with
    | (ee1, re1), (ee2, re2) => (bveand ee1 ee2, bvrand re1 re2)
    end.

  Fixpoint bvands es : bexp :=
    match es with
    | [::] => (bveTrue, bvrTrue)
    | hd::[::] => hd
    | hd::tl => bvand hd (bvands tl)
    end.

  Definition bvands2 es rs : bexp := (bveands es, bvrands rs).

  Fixpoint vars_eexp (e : eexp) : VS.t :=
    match e with
    | bveVar x => VS.singleton x
    | bveConst _ => VS.empty
    | bveUnop _ e => vars_eexp e
    | bveBinop _ e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    end.

  Fixpoint vars_rexp (n : nat) (e : rexp n) : VS.t :=
    match e with
    | bvrVar x => VS.singleton x
    | bvrConst _ _ => VS.empty
    | bvrBinop _ _ e1 e2 => VS.union (vars_rexp e1) (vars_rexp e2)
    | bvrExt _ e _ => vars_rexp e
    end.

  Fixpoint vars_ebexp (e : ebexp) : VS.t :=
    match e with
    | bveTrue => VS.empty
    | bveEq e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    | bveEqMod e1 e2 p => VS.union (vars_eexp e1)
                                  (VS.union (vars_eexp e2) (vars_eexp p))
    | bveAnd e1 e2 => VS.union (vars_ebexp e1) (vars_ebexp e2)
    end.

  Fixpoint vars_rbexp (e : rbexp) : VS.t :=
    match e with
    | bvrTrue => VS.empty
    | bvrCmp _ _ e1 e2 => VS.union (vars_rexp e1) (vars_rexp e2)
    | bvrAnd e1 e2 => VS.union (vars_rbexp e1) (vars_rbexp e2)
    end.

  Definition vars_bexp (e : bexp) : VS.t :=
    VS.union (vars_ebexp (eqn_bexp e)) (vars_rbexp (rng_bexp e)).

  Definition eval_eunop (op : unop) (v : Z) : Z :=
    match op with
    | bvNegOp => - v
    end.

  Definition eval_ebinop (op : binop) (v1 v2 : Z) : Z :=
    match op with
    | bvAddOp => v1 + v2
    | bvSubOp => v1 - v2
    | bvMulOp => v1 * v2
    end.

  Definition eval_runop (n : nat) (op : unop) (v : BITS n) : BITS n :=
    match op with
    | bvNegOp => negB v
    end.

  Definition eval_rbinop (n : nat) (op : binop) (v1 v2 : BITS n) : BITS n :=
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

  Fixpoint eval_eexp (e : eexp) (s : State.t) : Z :=
    match e with
    | bveVar x => toPosZ (State.acc x s)
    | bveConst n => n
    | bveUnop op e => eval_eunop op (eval_eexp e s)
    | bveBinop op e1 e2 => eval_ebinop op (eval_eexp e1 s) (eval_eexp e2 s)
    end.

  Fixpoint eval_rexp (n : nat) (e : rexp n) (s : State.t) : BITS n :=
    match e with
    | bvrVar x => State.acc x s
    | bvrConst _ n => n
    | bvrBinop _ op e1 e2 => eval_rbinop op (eval_rexp e1 s) (eval_rexp e2 s)
    | bvrExt _ e m => zeroExtend m (eval_rexp e s)
    end.

  Fixpoint eval_ebexp (e : ebexp) (s : State.t) : Prop :=
    match e with
    | bveTrue => True
    | bveEq e1 e2 => eval_eexp e1 s = eval_eexp e2 s
    | bveEqMod e1 e2 p => modulo (eval_eexp e1 s) (eval_eexp e2 s) (eval_eexp p s)
    | bveAnd e1 e2 => eval_ebexp e1 s /\ eval_ebexp e2 s
    end.

  Fixpoint eval_rbexp (e : rbexp) (s : State.t) : Prop :=
    match e with
    | bvrTrue => True
    | bvrCmp _ op e1 e2 => eval_cmpop op (eval_rexp e1 s) (eval_rexp e2 s)
    | bvrAnd e1 e2 => eval_rbexp e1 s /\ eval_rbexp e2 s
    end.

  Definition eval_bexp (e : bexp) (s : State.t) : Prop :=
    eval_ebexp (eqn_bexp e) s /\ eval_rbexp (rng_bexp e) s.

  Definition valid (f : bexp) : Prop :=
    forall s : State.t, eval_bexp f s.

  Definition entails (f g : bexp) : Prop :=
    forall s : State.t,
      eval_bexp f s -> eval_bexp g s.

  Record spec : Type := mkSpec { spre : bexp; sprog : program; spost : bexp }.

  Record espec : Type := mkeSpec { espre : ebexp;
                                   esprog : program;
                                   espost : ebexp }.

  Record rspec : Type := mkrSpec { rspre : rbexp;
                                   rsprog : program;
                                   rspost : rbexp }.

  Coercion spec_of_espec rs :=
    {| spre := (espre rs, bvrTrue);
       sprog := esprog rs;
       spost := (espost rs, bvrTrue) |}.

  Coercion spec_of_rspec rs :=
    {| spre := (bveTrue, rspre rs);
       sprog := rsprog rs;
       spost := (bveTrue, rspost rs) |}.

  Definition valid_spec (s : spec) : Prop :=
    forall s1 s2,
      eval_bexp (spre s) s1 ->
      eval_program s1 (sprog s) = s2 ->
      eval_bexp (spost s) s2.

  Definition succ_valid_spec (s: spec) : Prop :=
    forall s1 s2,
      eval_bexp (spre s) s1 ->
      succ_program s1 (sprog s) s2 ->
      eval_bexp (spost s) s2 .

  Definition valid_espec (s : espec) : Prop :=
    forall s1 s2,
      eval_ebexp (espre s) s1 ->
      eval_program s1 (esprog s) = s2 ->
      eval_ebexp (espost s) s2.

  Definition succ_valid_espec (s : espec) : Prop :=
    forall s1 s2,
      eval_ebexp (espre s) s1 ->
      succ_program s1 (esprog s) s2 ->
      eval_ebexp (espost s) s2 .

  Definition valid_rspec (s : rspec) : Prop :=
    forall s1 s2,
      eval_rbexp (rspre s) s1 ->
      eval_program s1 (rsprog s) = s2 ->
      eval_rbexp (rspost s) s2.

  Definition succ_valid_rspec (s : rspec) : Prop :=
    forall s1 s2,
      eval_rbexp (rspre s) s1 ->
      succ_program s1 (rsprog s) s2 ->
      eval_rbexp (rspost s) s2 .

  Local Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity).
  Local Notation "f ===> g" := (entails f g) (at level 82, no associativity).
  Local Notation "{{ f }} p {{ g }}" :=
    ({| spre := f; sprog := p; spost := g |}) (at level 82).
  Local Notation "|= s" := (valid_spec s) (at level 83).
  Local Notation "||= s" := (succ_valid_spec s) (at level 83) .
  
  Definition counterexample (sp : spec) (s : State.t) : Prop :=
    eval_bexp (spre sp) s /\
    exists s' : State.t,
      eval_program s (sprog sp) = s' /\ (~ eval_bexp (spost sp) s').

  Definition succ_counterexample (sp : spec) (s : State.t) : Prop :=
    eval_bexp (spre sp) s /\
    exists s' : State.t,
      succ_program s (sprog sp) s' /\ (~ eval_bexp (spost sp) s').

  Lemma vars_ebexp_subset e :
    VS.subset (vars_ebexp (eqn_bexp e)) (vars_bexp e).
  Proof.
    apply: VSLemmas.subset_union1. exact: VSLemmas.subset_refl.
  Qed.

  Lemma vars_rbexp_subset e :
    VS.subset (vars_rbexp (rng_bexp e)) (vars_bexp e).
  Proof.
    apply: VSLemmas.subset_union2. exact: VSLemmas.subset_refl.
  Qed.

  Lemma eval_bexp_eqn e s :
    eval_bexp e s -> eval_ebexp (eqn_bexp e) s.
  Proof.
    move=> H; exact: (proj1 H).
  Qed.

  Lemma eval_bexp_rng e s :
    eval_bexp e s -> eval_rbexp (rng_bexp e) s.
  Proof.
    move=> H; exact: (proj2 H).
  Qed.

  Lemma eval_bveand e1 e2 s :
    (eval_ebexp e1 s /\ eval_ebexp e2 s) <-> (eval_ebexp (bveand e1 e2) s).
  Proof.
    case: e1; case: e2 => /=; tauto.
  Qed.

  Lemma eval_bveand1 e1 e2 s :
    eval_ebexp e1 s -> eval_ebexp e2 s -> eval_ebexp (bveand e1 e2) s.
  Proof.
    move=> H1 H2; exact: ((proj1 (eval_bveand e1 e2 s)) (conj H1 H2)).
  Qed.

  Lemma eval_bveand2 e1 e2 s :
    eval_ebexp (bveand e1 e2) s ->
    eval_ebexp e1 s /\ eval_ebexp e2 s.
  Proof.
    move=> H; exact: ((proj2 (eval_bveand e1 e2 s)) H).
  Qed.

  Lemma eval_bvrand e1 e2 s :
    (eval_rbexp e1 s /\ eval_rbexp e2 s) <-> (eval_rbexp (bvrand e1 e2) s).
  Proof.
    case: e1; case: e2 => /=; tauto.
  Qed.

  Lemma eval_bvrand1 e1 e2 s :
    eval_rbexp e1 s -> eval_rbexp e2 s -> eval_rbexp (bvrand e1 e2) s.
  Proof.
    move=> H1 H2; exact: ((proj1 (eval_bvrand e1 e2 s)) (conj H1 H2)).
  Qed.

  Lemma eval_bvrand2 e1 e2 s :
    eval_rbexp (bvrand e1 e2) s ->
    eval_rbexp e1 s /\ eval_rbexp e2 s.
  Proof.
    move=> H; exact: ((proj2 (eval_bvrand e1 e2 s)) H).
  Qed.

  Lemma eval_bvand_eqn_distr e1 e2 s :
    (eval_ebexp (eqn_bexp e1) s /\ eval_ebexp (eqn_bexp e2) s) <->
    eval_ebexp (eqn_bexp (bvand e1 e2)) s.
  Proof.
    destruct e1 as [ee1 er1]; destruct e2 as [ee2 er2] => /=.
    exact: eval_bveand.
  Qed.

  Lemma eval_bvand_eqn_distr1 e1 e2 s :
    eval_ebexp (eqn_bexp e1) s -> eval_ebexp (eqn_bexp e2) s ->
    eval_ebexp (eqn_bexp (bvand e1 e2)) s.
  Proof.
    move=> H1 H2; exact: ((proj1 (eval_bvand_eqn_distr e1 e2 s)) (conj H1 H2)).
  Qed.

  Lemma eval_bvand_eqn_distr2 e1 e2 s :
    eval_ebexp (eqn_bexp (bvand e1 e2)) s ->
    eval_ebexp (eqn_bexp e1) s /\ eval_ebexp (eqn_bexp e2) s.
  Proof.
    move=> H; exact: ((proj2 (eval_bvand_eqn_distr e1 e2 s)) H).
  Qed.

  Lemma eval_bvand_rng_distr e1 e2 s :
    (eval_rbexp (rng_bexp e1) s /\ eval_rbexp (rng_bexp e2) s) <->
    eval_rbexp (rng_bexp (bvand e1 e2)) s.
  Proof.
    destruct e1 as [ee1 er1]; destruct e2 as [ee2 er2] => /=.
    exact: eval_bvrand.
  Qed.

  Lemma eval_bvand_rng_distr1 e1 e2 s :
    eval_rbexp (rng_bexp e1) s -> eval_rbexp (rng_bexp e2) s ->
    eval_rbexp (rng_bexp (bvand e1 e2)) s.
  Proof.
    move=> H1 H2; exact: ((proj1 (eval_bvand_rng_distr e1 e2 s)) (conj H1 H2)).
  Qed.

  Lemma eval_bvand_rng_distr2 e1 e2 s :
    eval_rbexp (rng_bexp (bvand e1 e2)) s ->
    eval_rbexp (rng_bexp e1) s /\ eval_rbexp (rng_bexp e2) s.
  Proof.
    move=> H; exact: ((proj2 (eval_bvand_rng_distr e1 e2 s)) H).
  Qed.

  Lemma spec_empty :
    forall f g,
      |= {{ f }} [::] {{ g }} -> f ===> g.
  Proof.
    move=> f g He s Hf.
    apply: (He s _ Hf).
    reflexivity.
  Qed.

  Lemma succ_spec_empty :
    forall f g,
      ||= {{ f }} [::] {{ g }} -> f ===> g .
  Proof .
    move => f g He s Hf .
    by apply: (He s _ Hf) .
  Qed .
    
  Lemma spec_strengthing :
    forall f g h p,
      entails f g -> |= {{ g }} p {{ h }} -> |= {{ f }} p {{ h }}.
  Proof.
    move=> f g h p Hfg Hgh s1 s2 Hf Hp.
    apply: (Hgh _ _ _ Hp).
    exact: (Hfg _ Hf).
  Qed.

  Lemma succ_spec_strengthing :
    forall f g h p,
      entails f g -> ||= {{ g }} p {{ h }} -> ||= {{ f }} p {{ h }}.
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

  Lemma succ_spec_weakening :
    forall f g h p,
      ||= {{ f }} p {{ g }} -> g ===> h -> ||= {{ f }} p {{ h }}.
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

  Lemma succ_spec_cons :
    forall f g h hd tl,
      ||= {{ f }} [::hd] {{ g }} -> ||= {{ g }} tl {{ h }} ->
      ||= {{ f }} (hd::tl) {{ h }}.
  Proof.
    move=> f g h hd tl Hshd Hstl s1 s2 /= Hf Hp.
    move: (succ_program_cons Hp) => {Hp} [s3 [Hhd Htl]].
    apply: (Hstl _ _ _ Htl) => /=.
    by apply: (Hshd _ _ _ (succ_singleton_program Hhd)) => /=.
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

  Lemma succ_spec_concat :
    forall f g h p1 p2,
      ||= {{ f }} p1 {{ g }} -> ||= {{ g }} p2 {{ h }} ->
      ||= {{ f }} (p1 ++ p2) {{ h }}.
  Proof.
    move=> f g h p1 p2 Hp1 Hp2 s1 s2 /= Hf Hp.
    move: (succ_program_split Hp) => [s3 [Hep1 Hep2]].
    apply: (Hp2 _ _ _ Hep2) => /=.
    apply: (Hp1 _ _ _ Hep1) => /=.
    assumption.
  Qed.

  Lemma spec_split_post :
    forall f g1 g2 p,
      |= {{ f }} p {{ g1 }} ->
      |= {{ f }} p {{ g2 }} ->
      |= {{ f }} p {{ bvand g1 g2 }}.
  Proof.
    move=> f g1 g2 p Hg1 Hg2 s1 s2 /= Hf Hp.
    move: (Hg1 s1 s2 Hf Hp) => /= {Hg1} [Hge1 Hgr1].
    move: (Hg2 s1 s2 Hf Hp) => /= {Hg2} [Hge2 Hgr2].
    split.
    - exact: (eval_bvand_eqn_distr1 Hge1 Hge2).
    - exact: (eval_bvand_rng_distr1 Hgr1 Hgr2).
  Qed.

  Lemma succ_spec_split_post :
    forall f g1 g2 p,
      ||= {{ f }} p {{ g1 }} ->
      ||= {{ f }} p {{ g2 }} ->
      ||= {{ f }} p {{ bvand g1 g2 }}.
  Proof.
    move=> f g1 g2 p Hg1 Hg2 s1 s2 /= Hf Hp.
    move: (Hg1 s1 s2 Hf Hp) => /= {Hg1} [Hge1 Hgr1].
    move: (Hg2 s1 s2 Hf Hp) => /= {Hg2} [Hge2 Hgr2].
    split.
    - exact: (eval_bvand_eqn_distr1 Hge1 Hge2).
    - exact: (eval_bvand_rng_distr1 Hgr1 Hgr2).
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
    | bvSubC c v e1 e2 => (c != v)
                            && VS.subset (vars_atomic e1) vs
                            && VS.subset (vars_atomic e2) vs
    | bvAdc v e1 e2 c
    | bvSbb v e1 e2 c => VS.mem c vs
                                && VS.subset (vars_atomic e1) vs
                                && VS.subset (vars_atomic e2) vs
    | bvAdcC c v e1 e2 y
    | bvSbbC c v e1 e2 y => (c != v)
                              && VS.mem y vs
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
    elim: i vs1 vs2 => /=; move=> *; hyps_splitb; repeat splitb;
    (match goal with
     | H: ?a |- ?a => assumption
     | |- is_true (VS.subset _ _) => by VSLemmas.dp_subset
     | |- is_true (VS.mem _ _) => by VSLemmas.dp_mem
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
    case: i => /=; intros; hyps_splitb; by VSLemmas.dp_Equal.
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
    | bvSbb _ _ _ _
    | bvMul _ _ _
    | bvShl _ _ _ => true
    | bvAddC c v _ _
    | bvAdcC c v _ _ _
    | bvSubC c v _ _
    | bvSbbC c v _ _ _ => c != v
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
         | |- is_true (VS.subset _ _) => by VSLemmas.dp_subset
         | |- is_true (VS.mem _ _) => by VSLemmas.dp_mem
         | |- _ => idtac
         end in
    tac).
  Qed.



  (** Big integers *)

  Section BigIntegers.

    From Common Require Import Nats.
    From mathcomp Require Import ssrnat.

    Variable w : nat.

    Fixpoint limbs_rec vs (n : nat) : eexp :=
      match vs with
      | [::] => bveConst 0
      | hd::[::] => if n == 0 then hd
                    else bvemul hd (bveConst (bve2pow n))
      | hd::tl =>
        let m := (n + w) in
        if n == 0 then bveadd hd (limbs_rec tl m)
        else bveadd (bvemul hd (bveConst (bve2pow n))) (limbs_rec tl m)
      end.

    Definition limbs (vs : seq eexp) : eexp :=
      limbs_rec vs 0.

  End BigIntegers.

End MakeBVDSL.

Module bv64DSL := MakeBVDSL AMD64 VarOrder VS.
Export bv64DSL.
Arguments bv64DSL.bvVar v%N.

Notation "'-e' x" := (bveneg x) (at level 35, right associativity) : bvdsl_scope.
Notation "x '+e' y" := (bveadd x y) (at level 50, left associativity) : bvdsl_scope.
Notation "x '-e' y" := (bvesub x y)  (at level 50, left associativity) : bvdsl_scope.
Notation "x '*e' y" := (bvemul x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x @:= y" := (bvAssign x%N y) (at level 70, no associativity) : bvdsl_scope.
Notation "x '=e' y" := (bveEq x y) (at level 70, no associativity) : bvdsl_scope.
Notation "x '=e' y 'mod' z" := (bveEqMod x y z) (at level 70, y at next level, no associativity) : bvdsl_scope.
Notation "x '&&e' y" := (bveand x y) (at level 70, no associativity) : bvdsl_scope.

Notation "x '+r' y" := (bvradd x y) (at level 50, left associativity) : bvdsl_scope.
Notation "x '-r' y" := (bvrsub x y)  (at level 50, left associativity) : bvdsl_scope.
Notation "x '*r' y" := (bvrmul x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x '&&r' y" := (bvrand x y) (at level 70, no associativity) : bvdsl_scope.
Notation "x '<r' y" := (bvult x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x '<=r' y" := (bvule x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x '>r' y" := (bvugt x y)  (at level 40, left associativity) : bvdsl_scope.
Notation "x '>=r' y" := (bvuge x y)  (at level 40, left associativity) : bvdsl_scope.

Notation "s |= f" := (eval_bexp f true s) (at level 74, no associativity) : bvdsl_scope.
Notation "s '|=e' f" := (eval_ebexp f true s) (at level 74, no associativity) : bvdsl_scope.
Notation "s '|=r' f" := (eval_rbexp f true s) (at level 74, no associativity) : bvdsl_scope.
Notation "f ===> g" := (entails f g) (at level 82, no associativity) : bvdsl_scope.
Notation "{{ f }} p {{ g }}" := ({| spre := f; sprog := p; spost := g |}) (at level 82, no associativity) : bvdsl_scope.
Notation "|= s" := (valid_spec s) (at level 83, no associativity) : bvdsl_scope.
Notation "'|=e' s" := (valid_espec s) (at level 83, no associativity) : bvdsl_scope.
Notation "'|=r' s" := (valid_rspec s) (at level 83, no associativity) : bvdsl_scope.
