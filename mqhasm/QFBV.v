
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Common Require Import Arch Var Bits Nats SsrOrdered FSets Store.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module MakeQFBV (A : ARCH) (V : SsrOrderedType).

  Module VS := FSetList.Make V.
  Module VSLemmas := FSetLemmas VS.

  (*
    bvSlice w1 w2 w3 e is equivalent to (_ extract (w1 + w2 - 1) w1) e
    in SMTLIB.
   *)
  Inductive exp : nat -> Type :=
  | bvVar : V.t -> exp A.wordsize
  | bvConst : forall w, BITS w -> exp w
  | bvNot : forall w, exp w -> exp w
  | bvAnd : forall w, exp w -> exp w -> exp w
  | bvOr : forall w, exp w -> exp w -> exp w
  | bvXor : forall w, exp w -> exp w -> exp w
  | bvNeg : forall w, exp w -> exp w
  | bvAdd : forall w, exp w -> exp w -> exp w
  | bvSub : forall w, exp w -> exp w -> exp w
  | bvMul : forall w, exp w -> exp w -> exp w
  | bvMod : forall w, exp w -> exp w -> exp w
  | bvShl : forall w, exp w -> exp w -> exp w
  | bvShr : forall w, exp w -> exp w -> exp w
  | bvConcat : forall w1 w2, exp w1 -> exp w2 -> exp (w2 + w1)
  | bvExtract : forall w i j, exp (j + (i - j + 1) + (w - i - 1)) ->
                              exp (i - j + 1)
  | bvSlice : forall w1 w2 w3, exp (w1 + w2 + w3) -> exp w2
  | bvHigh : forall w1 w2, exp (w1 + w2) -> exp w2
  | bvLow : forall w1 w2, exp (w1 + w2) -> exp w1
  | bvZeroExtend : forall w i, exp w -> exp (w + i)
  | bvSignExtend : forall w i, exp (w.+1) -> exp (w.+1 + i).

  Inductive bexp : Type :=
  | bvTrue : bexp
  | bvUlt : forall w, exp w -> exp w -> bexp
  | bvUle : forall w, exp w -> exp w -> bexp
  | bvUgt : forall w, exp w -> exp w -> bexp
  | bvUge : forall w, exp w -> exp w -> bexp
  | bvEq : forall w, exp w -> exp w -> bexp
  | bvAddo : forall w, exp w -> exp w -> bexp
  | bvSubo : forall w, exp w -> exp w -> bexp
  | bvMulo : forall w, exp w -> exp w -> bexp
  | bvLneg : bexp -> bexp
  | bvConj : bexp -> bexp -> bexp.

  Definition bvEqMod w (e1 e2 p : exp w) : bexp :=
    bvEq (bvMod e1 p) (bvMod e2 p).

  Fixpoint vars_exp w (e : exp w) : VS.t :=
    match e with
    | bvVar v => VS.singleton v
    | bvConst _ _ => VS.empty
    | bvNot _ e => vars_exp e
    | bvAnd _ e1 e2
    | bvOr _ e1 e2
    | bvXor _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvNeg _ e => vars_exp e
    | bvAdd _ e1 e2
    | bvSub _ e1 e2
    | bvMul _ e1 e2
    | bvMod _ e1 e2
    | bvShl _ e1 e2
    | bvShr _ e1 e2
    | bvConcat _ _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvExtract _ _ _ e
    | bvSlice _ _ _ e
    | bvHigh _ _ e
    | bvLow _ _ e
    | bvZeroExtend _ _ e
    | bvSignExtend _ _ e => vars_exp e
    end.

  Fixpoint vars_bexp e : VS.t :=
    match e with
    | bvTrue => VS.empty
    | bvUlt _ e1 e2
    | bvUle _ e1 e2
    | bvUgt _ e1 e2
    | bvUge _ e1 e2
    | bvEq _ e1 e2
    | bvAddo _ e1 e2
    | bvSubo _ e1 e2
    | bvMulo _ e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | bvLneg e => vars_bexp e
    | bvConj e1 e2 => VS.union (vars_bexp e1) (vars_bexp e2)
    end.



  Notation value := (BITS A.wordsize).

  Module Store := MakeTStore V.

  Definition state := Store.t value.

  Fixpoint eval_exp w (e : exp w) (s : state) : BITS w :=
    match e with
    | bvVar v => Store.acc v s
    | bvConst _ n => n
    | bvNot _ e => invB (eval_exp e s)
    | bvAnd _ e1 e2 => andB (eval_exp e1 s) (eval_exp e2 s)
    | bvOr _ e1 e2 => orB (eval_exp e1 s) (eval_exp e2 s)
    | bvXor _ e1 e2 => xorB (eval_exp e1 s) (eval_exp e2 s)
    | bvNeg _ e => negB (eval_exp e s)
    | bvAdd _ e1 e2 => addB (eval_exp e1 s) (eval_exp e2 s)
    | bvSub _ e1 e2 => subB (eval_exp e1 s) (eval_exp e2 s)
    | bvMul _ e1 e2 => mulB (eval_exp e1 s) (eval_exp e2 s)
    | bvMod _ e p => fromPosZ (Z.modulo (toPosZ (eval_exp e s))
                                        (toPosZ (eval_exp p s)))
    | bvShl _ e1 e2 => shlBn (eval_exp e1 s) (toNat (eval_exp e2 s))
    | bvShr _ e1 e2 => shrBn (eval_exp e1 s) (toNat (eval_exp e2 s))
    | bvConcat _ _ e1 e2 => catB (eval_exp e1 s) (eval_exp e2 s)
    | bvExtract w i j e => slice j (i - j + 1) (w - i - 1) (eval_exp e s)
    | bvSlice w1 w2 w3 e => slice w1 w2 w3 (eval_exp e s)
    | bvHigh w1 w2 e => high w2 (eval_exp e s)
    | bvLow w1 w2 e => low w1 (eval_exp e s)
    | bvZeroExtend _ i e => zeroExtend i (eval_exp e s)
    | bvSignExtend _ i e => signExtend i (eval_exp e s)
    end.

  Fixpoint eval_bexp (e : bexp) (s : state) : Prop :=
    match e with
    | bvTrue => True
    | bvUlt _ e1 e2 => ltB (eval_exp e1 s) (eval_exp e2 s)
    | bvUle _ e1 e2 => leB (eval_exp e1 s) (eval_exp e2 s)
    | bvUgt _ e1 e2 => ltB (eval_exp e2 s) (eval_exp e1 s)
    | bvUge _ e1 e2 => leB (eval_exp e2 s) (eval_exp e1 s)
    | bvEq _ e1 e2 => eval_exp e1 s = eval_exp e2 s
    | bvAddo _ e1 e2 => carry_addB (eval_exp e1 s) (eval_exp e2 s) = true
    | bvSubo _ e1 e2 => carry_subB (eval_exp e1 s) (eval_exp e2 s) = true
    | bvMulo w e1 e2 =>
      high w (fullmulB (eval_exp e1 s) (eval_exp e2 s)) <> #0
    | bvLneg e => ~ eval_bexp e s
    | bvConj e1 e2 => eval_bexp e1 s /\ eval_bexp e2 s
    end.

  Definition valid (e : bexp) : Prop :=
    forall s, eval_bexp e s.

  Lemma low_slice w1 w2 (e : exp (w1 + w2)) s :
    eval_exp (bvLow e) s = eval_exp (@bvSlice 0 w1 w2 e) s.
  Proof.
    reflexivity.
  Qed.

  Definition exp_assoc w1 w2 w3 (e : exp (w1 + w2 + w3))
             (pf : w1 + w2 + w3 = w1 + (w2 + w3)) : exp (w1 + (w2 + w3)) :=
    match pf in (_ = w) return exp w with
    | eq_refl => e
    end.

  Definition exp_addn0 w (e : exp (w + 0))
             (pf : w + 0 = w) : exp w :=
    match pf in (_ = w) return exp w with
    | eq_refl => e
    end.

  Definition exp_add0 w (e : exp w)
             (pf : w = w + 0) : exp (w + 0) :=
    match pf in (_ = w) return exp w with
    | eq_refl => e
    end.

  Lemma high_slice1 w1 w2 (e : exp (w1 + w2)) s
        (pf : w1 + w2 = w1 + w2 + 0) :
    eval_exp (bvHigh e) s =
    eval_exp (@bvSlice w1 w2 0 (exp_add0 e pf)) s.
  Proof.
    From Coq Require Import Program.
    rewrite /exp_add0 /=.
    rewrite /slice /=.
    have: eval_exp e s =
          (low (w1 + w2)
               (eval_exp match pf in (_ = w) return (exp w) with
                         | eq_refl => e
                         end s)).
    - move: pf e.
    -
  Abort.

  Lemma high_slice2 w1 w2 (e : exp (w1 + w2 + 0)) s
        (pf1 : w1 + w2 + 0 = w1 + (w2 + 0))
        (pf2 : w2 + 0 = w2) :
    eval_exp (exp_addn0 (bvHigh (exp_assoc e pf1)) pf2) s =
    eval_exp (@bvSlice w1 w2 0 e) s.
  Proof.
    From Coq Require Import Program.
    rewrite /exp_addn0 /exp_assoc /=.
    move: pf1 pf2 e.
    rewrite (addn0 w2).
    move=> pf1 pf2 e.
    rewrite (UIP_refl _ _ pf2) => {pf2}.
    rewrite /slice /=.
    have: (eval_exp match pf1 in (_ = w) return (exp w) with
              | eq_refl => e
              end s) = (low (w1 + w2) (eval_exp e s)).
    - move: pf1 e.
      generalize (w1 + w2).
    -
  Abort.

  Fixpoint well_formed_exp w (e : exp w) : bool :=
    match e with
    | bvExtract w i j e => ((0 <= j) && (j <= i) && (i < w))
                             && (well_formed_exp e)
    | bvHigh w1 w2 e => (w2 > 0) && (well_formed_exp e)
    | bvLow w1 w2 e => (w1 > 0) && (well_formed_exp e)
    | _ => true
    end.

  Fixpoint well_formed_bexp (e : bexp) : bool :=
    match e with
    | bvTrue => true
    | bvUlt _ e1 e2
    | bvUle _ e1 e2
    | bvUgt _ e1 e2
    | bvUge _ e1 e2
    | bvEq _ e1 e2
    | bvAddo _ e1 e2
    | bvSubo _ e1 e2
    | bvMulo _ e1 e2 => (well_formed_exp e1) && (well_formed_exp e1)
    | bvLneg e => well_formed_bexp e
    | bvConj e1 e2 => (well_formed_bexp e1) && (well_formed_bexp e1)
    end.

End MakeQFBV.



From mQhasm Require Import bvSSA.

Module QFBV64 := MakeQFBV AMD64 bv64SSA.V.
