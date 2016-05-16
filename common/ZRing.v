
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun choice eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*
(** Z is an eqType. *)

Definition zeq (n m : Z) : bool :=
  match Z.eq_dec n m with
  | left _ => true
  | right _ => false
  end.

Lemma z_eqP : Equality.axiom zeq.
Proof.
  move=> n m.
  rewrite /zeq; case: (Z.eq_dec n m) => Hnm.
  - apply: ReflectT; exact: Hnm.
  - apply: ReflectF; exact: Hnm.
Qed.

Canonical Z_eqMixin := EqMixin z_eqP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.
*)

(** Z is an eqType, a choiceType, and a countType. *)

Definition natsum_of_Z (n : Z) : nat + nat :=
  match n with
  | Z0 => inl 0
  | Zpos m => inl (Pos.to_nat m)
  | Zneg m => inr (Pos.to_nat m)
  end.

Definition Z_of_natsum (n : nat + nat) : Z :=
  match n with
  | inl O => Z0
  | inl (S _ as m) => Zpos (Pos.of_nat m)
  | inr m => Zneg (Pos.of_nat m)
  end.

Lemma natsum_of_ZK : cancel natsum_of_Z Z_of_natsum.
Proof.
  move=> n.
  elim: n => /=.
  - reflexivity.
  - move=> p.
    rewrite Pos2Nat.id.
    case H: (Pos.to_nat p).
    + move: (Pos2Nat.is_pos p) => Hp.
      rewrite H in Hp.
      by inversion Hp.
    + reflexivity.
  - move=> p.
    rewrite Pos2Nat.id.
    reflexivity.
Qed.

Definition Z_eqMixin := CanEqMixin natsum_of_ZK.
Definition Z_countMixin := CanCountMixin natsum_of_ZK.
Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.
Canonical Z_countType := Eval hnf in CountType Z Z_countMixin.



(** Z is a ZmodType *)

Module ZZmod.

  Definition zopp (n : Z) : Z := -n.

  Definition zaddA : associative Z.add := Z.add_assoc.
  Definition zaddC : commutative Z.add := Z.add_comm.
  Definition zadd0 : left_id 0%Z Z.add := Z.add_0_l.
  Lemma zaddN : left_inverse 0%Z zopp Z.add.
  Proof.
    move=> n.
    rewrite /zopp.
    rewrite zaddC.
    exact: Z.add_opp_diag_r.
  Qed.

  Definition Mixin := ZmodMixin zaddA zaddC zadd0 zaddN.

End ZZmod.

Canonical Z_ZmodType := ZmodType Z ZZmod.Mixin.



(** Z is a ring. *)

Module ZRing.

  Definition zmulA : associative Z.mul := Z.mul_assoc.
  Definition zmulC : commutative Z.mul := Z.mul_comm.
  Definition zmul1 : left_id 1%Z Z.mul := Z.mul_1_l.
  Definition zmul_addl : left_distributive Z.mul Z.add := Z.mul_add_distr_r.
  Definition znonzero1 : (1 != 0)%Z := is_true_true.

  Definition comMixin := ComRingMixin zmulA zmulC zmul1 zmul_addl znonzero1.

End ZRing.

Canonical Z_Ring := Eval hnf in RingType Z ZRing.comMixin.
Canonical Z_comRing := Eval hnf in ComRingType Z ZRing.zmulC.
