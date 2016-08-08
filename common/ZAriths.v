
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun choice eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Additional Lemmas *)

Section ZLemmas.

  Local Open Scope Z_scope.

  Lemma Zdouble_positive (n : Z) :
    0 <= n -> n <= Z.double n.
  Proof.
    rewrite Z.double_spec -Z.add_diag => H.
    exact: (Z.add_le_mono _ _ _ _ H (Z.le_refl n)).
  Qed.

  Lemma Zdouble_negative (n : Z) :
    n <= 0 -> Z.double n <= n.
  Proof.
    rewrite Z.double_spec -Z.add_diag => H.
    move: (Z.add_le_mono _ _ _ _ (Z.le_refl n) H) => {H} H.
    rewrite Z.add_0_r in H.
    exact: H.
  Qed.

  Lemma Zle_plus_r n m p :
    n <= m -> 0 <= p -> n <= m + p.
  Proof.
    move=> Hnm H0p.
    apply: (Z.le_trans _ _ _ Hnm).
    rewrite -{1}(Z.add_0_r m).
    exact: (Zplus_le_compat_l _ _ _ H0p).
  Qed.

  Lemma Zle_plus_l n m p :
    n <= m -> p <= 0 -> n + p <= m.
  Proof.
    move=> Hnm H0p.
    apply: (Z.le_trans _ _ _ _ Hnm).
    rewrite -{2}(Z.add_0_r n).
    exact: (Zplus_le_compat_l _ _ _ H0p).
  Qed.

  Lemma Zle_succ n : n <= Z.succ n.
  Proof.
    apply: (Zle_plus_r (Z.le_refl n)).
    done.
  Qed.

  Lemma two_power_nat_gt_zero n : two_power_nat n > 0.
  Proof.
    rewrite two_power_nat_equiv.
    move: (two_p_gt_ZERO (Z.of_nat n)).
    rewrite two_p_correct.
    apply.
      by induction n.
  Qed.

  Lemma zero_lt_two_power_nat n : 0 < two_power_nat n.
  Proof.
    apply: Z.gt_lt.
    exact: two_power_nat_gt_zero.
  Qed.

  Lemma ltn_Sdouble n m : n < m -> 2 * n + 1 < 2 * m.
  Proof.
    move=> Hnm.
    rewrite -2!Z.add_diag.
    rewrite -Z.add_assoc.
    apply: Z.add_lt_le_mono.
    - exact: Hnm.
    - apply: Zlt_le_succ.
      exact: Hnm.
  Qed.

  Lemma Sdouble_ltn n m : 2 * n + 1 < 2 * m -> n < m.
  Proof.
    move=> H.
    apply: (Zmult_lt_reg_r _ _ 2).
    - done.
    - rewrite (Z.mul_comm n 2) (Z.mul_comm m 2).
      move: (Zle_succ_l (2 * n)%Z (2 * m)%Z) => [] H1 _; apply: H1.
      exact: (Z.lt_le_incl _ _ H).
  Qed.

  Lemma Zminus_plus : forall n m : Z, n - m + m = n.
  Proof.
    move=> n m.
    rewrite -Z.add_assoc (Z.add_comm (-m) m) Z.add_opp_diag_r Z.add_0_r.
    reflexivity.
  Qed.

End ZLemmas.



(** Z is an eqType, a choiceType, and a countType. *)

Section ZEqType.

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

End ZEqType.



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



(** Equality Modulo *)

Section EqualityModulo.

  Local Open Scope Z_scope.

  Definition eqmb (x y p : Z) : bool :=
    x mod p == y mod p.

  Lemma eqmP : forall x y p, reflect (eqm p x y) (eqmb x y p).
  Proof.
    rewrite /eqm /eqmb => x y p.
    case Hxy: (x mod p == y mod p)%Z.
    - apply: ReflectT.
      apply/eqP.
      assumption.
    - apply: ReflectF.
      apply/eqP/negP.
      by rewrite Hxy.
  Qed.

  Definition modulo (x y p : Z) := exists k : Z, x - y = k * p.

  Lemma Zminus_mod_mod :
    forall x p : Z,
      p <> 0 ->
      (x - (x mod p)) mod p = 0.
  Proof.
    move=> x p Hp.
    rewrite Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    exact: Zmod_0_l.
  Qed.

  Lemma Zminus_mod_div_mul :
    forall x p : Z,
      p <> 0 ->
      (x - (x mod p)) / p * p = x - (x mod p).
  Proof.
    move=> x p Hp.
    rewrite (Z_div_exact_full_2 _ _ Hp (Zminus_mod_mod _ Hp)).
    move: (Zdiv_mult_cancel_l ((x - x mod p) / p) 1 p Hp) => Heq.
    rewrite Z.mul_1_r Z.div_1_r in Heq.
    rewrite Heq.
    rewrite Z.mul_comm.
    reflexivity.
  Qed.

  Lemma eqm_modulo :
    forall x y p : Z,
      p <> 0 -> eqm p x y -> modulo x y p.
  Proof.
    move=> x y p Hp Hm.
    exists ((x - (x mod p)) / p - (y - (y mod p)) / p).
    rewrite Z.mul_sub_distr_r 2!(Zminus_mod_div_mul _ Hp) Hm Zminus_plus_simpl_r.
    reflexivity.
  Qed.

  Lemma modulo_eqm :
    forall x y p : Z,
      p <> 0 -> modulo x y p -> eqm p x y.
  Proof.
    move=> x y p Hp [k Heq].
    move: (Zplus_eq_compat _ _ _ _ Heq (Logic.eq_refl y)) => {Heq}.
    rewrite (Z.add_comm (k * p) y) Zminus_plus => Heq.
    rewrite Heq /eqm Z_mod_plus_full.
    reflexivity.
  Qed.

  Lemma eqmb_modulo :
    forall x y p : Z,
      p <> 0 -> eqmb x y p -> modulo x y p.
  Proof.
    move=> x y p Hp Hm.
    move/eqmP: Hm.
    exact: eqm_modulo.
  Qed.

  Lemma modulo_eqmb :
    forall x y p : Z,
      p <> 0 -> modulo x y p -> eqmb x y p.
  Proof.
    move=> x y p Hp Hm.
    apply/eqmP.
    exact: modulo_eqm.
  Qed.

  Lemma modulo_inj : forall x y p z,
      (z <> 0)%Z ->
      modulo (z * x) (z * y) (z * p) ->
      modulo x y p.
  Proof.
    move=> x y p z Hz [k H].
    exists k.
    rewrite -Z.mul_sub_distr_l Z.mul_assoc (Z.mul_comm k z) -Z.mul_assoc in H.
    exact (Z.mul_reg_l _ _ z Hz H).
  Qed.

End EqualityModulo.

Notation "x === y # p" := (eqmb x y p) (at level 70, no associativity).

(**
 * Prove
 *   forall x1 ... xn : Z,
 *     P1 -> ... -> Pn -> modulo f g p
 * with modulo_inj and another proved lemma H
 *   forall x1 ... xn y z : Z,
 *     P1 -> ... -> Pn -> y = z^2 + 1 -> modulo (y * f) (y * g) (y * p).
 *)
Ltac modulo_inj_pow2add1 H :=
  intros;
  apply (modulo_inj (z:=2%Z)); [
    discriminate |
    apply H with 1%Z; first [assumption | reflexivity]
  ].
