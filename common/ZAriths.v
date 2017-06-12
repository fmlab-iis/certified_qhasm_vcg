
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssralg ssrfun choice eqtype.
From mathcomp Require ssrnat.
From Common Require Import Types SsrOrdered Nats.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Positive is an eqType, a choiceType, and a countType. *)

Section PositiveEqType.

  Local Open Scope positive_scope.

  Lemma pos_eqP : forall (n m : positive), reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (Pos.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition pos_pickle (n : positive) : nat :=
    ssrnat.subn (Pos.to_nat n) 1.

  Definition pos_unpickle (n : nat) : option positive :=
    Some (Pos.of_nat (ssrnat.addn n 1)).

  Lemma pos_count : pcancel pos_pickle pos_unpickle.
  Proof.
    move=> n.
    rewrite /pos_unpickle /pos_pickle.
    move: (Pos2Nat.is_succ n) => [m Hm].
    rewrite Hm -ssrnat.addn1 (ssrnat.addnK 1%nat m).
    rewrite (ssrnat.addnC m 1%nat) ssrnat.add1n -Hm.
    rewrite Pos2Nat.id.
    reflexivity.
  Qed.

  Definition pos_eqMixin := EqMixin pos_eqP.
  Definition pos_countMixin := CountMixin pos_count.
  Definition pos_choiceMixin := CountChoiceMixin pos_countMixin.
  Canonical pos_eqType := Eval hnf in EqType positive pos_eqMixin.
  Canonical pos_choiceType := Eval hnf in ChoiceType positive pos_choiceMixin.
  Canonical pos_countType := Eval hnf in CountType positive pos_countMixin.

End PositiveEqType.

Section PositiveLemmas.

  Local Open Scope positive_scope.

  Lemma pos_ltP : forall x y : positive, reflect (x < y) (x <? y).
  Proof.
    move=> x y.
    move: (Pos.ltb_lt x y) => [H1 H2].
    case H: (x <? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma pos_leP : forall x y : positive, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y.
    move: (Pos.leb_le x y) => [H1 H2].
    case H: (x <=? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

End PositiveLemmas.



(** N is an eqType, a choiceType, and a countType. *)

Section NEqType.

  Local Open Scope N_scope.

  Lemma N_eqP : forall n m, reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (N.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition N_pickle (n : N) : nat := N.to_nat n.

  Definition N_unpickle (n : nat) : option N := Some (N.of_nat n).

  Lemma N_count : pcancel N_pickle N_unpickle.
  Proof.
    move=> n.
    rewrite /N_unpickle /N_pickle.
    rewrite Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Definition N_eqMixin := EqMixin N_eqP.
  Definition N_countMixin := CountMixin N_count.
  Definition N_choiceMixin := CountChoiceMixin N_countMixin.
  Canonical N_eqType := Eval hnf in EqType N N_eqMixin.
  Canonical N_choiceType := Eval hnf in ChoiceType N N_choiceMixin.
  Canonical N_countType := Eval hnf in CountType N N_countMixin.

End NEqType.

Reserved Notation "m <=? n <=? p" (at level 70, n at next level).
Reserved Notation "m <? n <=? p" (at level 70, n at next level).
Reserved Notation "m <=? n <? p" (at level 70, n at next level).
Reserved Notation "m <? n <? p" (at level 70, n at next level).

Section NLemmas.

  Notation "m <=? n <=? p" := ((m <=? n) && (n <=? p)) (at level 70, n at next level) : N_scope.
  Notation "m <? n <=? p" := ((m <? n) && (n <=? p)) (at level 70, n at next level) : N_scope.
  Notation "m <=? n <? p" := ((m <=? n) && (n <? p)) (at level 70, n at next level) : N_scope.
  Notation "m <? n <? p" := ((m <? n) && (n <? p)) (at level 70, n at next level) : N_scope.

  Local Open Scope N_scope.

  Lemma N_ltP : forall x y : N, reflect (x < y) (x <? y).
  Proof.
    move=> x y.
    move: (N.ltb_lt x y) => [H1 H2].
    case H: (x <? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
        by rewrite H.
  Qed.

  Lemma N_leP : forall x y : N, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y.
    move: (N.leb_le x y) => [H1 H2].
    case H: (x <=? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma NltSn n : n < n + 1.
  Proof.
    rewrite N.add_1_r.
    exact: N.lt_succ_diag_r.
  Qed.

  Lemma NltnSn n : n <? n + 1.
  Proof.
    apply/N_ltP.
    exact: NltSn.
  Qed.

  Lemma Nltnn n : (n <? n) = false.
  Proof.
    exact: N.ltb_irrefl.
  Qed.

  Lemma Nltn_trans n m p : (m <? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_ltP Hnp.
    apply/N_ltP.
    exact: (N.lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_trans n m p : (m <=? n) -> (n <=? p) -> (m <=? p).
  Proof.
    move=> /N_leP Hmn /N_leP Hnp.
    apply/N_leP.
    exact: (N.le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_ltn_trans n m p : (m <=? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_leP Hmn /N_ltP Hnp.
    apply/N_ltP.
    exact: (N.le_lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nltn_leq_trans n m p : (m <? n) -> (n <=? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_leP Hnp.
    apply/N_ltP.
    exact: (N.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nltn0Sn n : 0 <? n + 1.
  Proof.
    apply/N_ltP.
    apply: N.add_pos_r.
    done.
  Qed.

  Lemma NltnW m n : (m <? n) -> (m <=? n).
  Proof.
    move=> /N_ltP H.
    apply/N_leP.
    exact: (N.lt_le_incl _ _ H).
  Qed.

  Lemma Nleqnn n : n <=? n.
  Proof.
    exact: N.leb_refl.
  Qed.

  Lemma Nleqn0 n : (n <=? 0) = (n == 0).
  Proof.
    move: (N.le_0_r n) => [H1 H2].
    case H: (n == 0); apply/N_leP.
    - exact: (H2 (eqP H)).
    - move=> Hle.
      move: (H1 Hle) => /eqP Heq.
      by rewrite H in Heq.
  Qed.

  Lemma Nsubn0 n : n - 0 = n.
  Proof.
    exact: (N.sub_0_r n).
  Qed.

  Lemma Nleq_eqVlt m n : (m <=? n) = (m == n) || (m <? n).
  Proof.
    move: (N.lt_eq_cases m n) => [H1 H2].
    symmetry.
    case H: (m <=? n).
    - apply/orP.
      move/N_leP: H => H.
      case: (H1 H) => {H} H.
      + right; apply/N_ltP; assumption.
      + left; apply/eqP; assumption.
    - apply/negP => /orP Hor.
      move/negP: H; apply; apply/N_leP; apply: H2.
      case: Hor => H.
      + right; apply/eqP; assumption.
      + left; apply/N_ltP; assumption.
  Qed.

  Lemma NltnS n m : (n <? m + 1) = (n <=? m).
  Proof.
    rewrite N.add_1_r.
    move: (N.lt_succ_r n m) => [H1 H2].
    case Hle: (n <=? m).
    - move/N_leP: Hle => Hle.
      apply/N_ltP.
      exact: (H2 Hle).
    - apply/N_ltP => Hlt.
      move/negP: Hle; apply.
      apply/N_leP.
      exact: (H1 Hlt).
  Qed.

  Lemma Nltn_add2r p m n : ((m + p) <? (n + p)) = (m <? n).
  Proof.
    move: (N.add_lt_mono_r m n p) => [H1 H2].
    case Hlt: (m <? n).
    - move/N_ltP: Hlt => Hlt.
      apply/N_ltP.
      exact: (H1 Hlt).
    - apply/negP => /N_ltP H.
      move/negP: Hlt; apply; apply/N_ltP.
      exact: (H2 H).
  Qed.

End NLemmas.

Notation "m <=? n <=? p" := ((m <=? n) && (n <=? p))%N (at level 70, n at next level) : N_scope.
Notation "m <? n <=? p" := ((m <? n) && (n <=? p))%N (at level 70, n at next level) : N_scope.
Notation "m <=? n <? p" := ((m <=? n) && (n <? p))%N (at level 70, n at next level) : N_scope.
Notation "m <? n <? p" := ((m <? n) && (n <? p))%N (at level 70, n at next level) : N_scope.



(** Z is an eqType, a choiceType, and a countType. *)

Section ZEqType.

  Local Open Scope Z_scope.

  Lemma Z_eqP : forall n m, reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (Z.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition natsum_of_Z (n : Z) : nat + nat :=
    match n with
    | Z0 => inl 0%nat
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

  Definition Z_eqMixin := EqMixin Z_eqP.
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



(** EQTYPE modules. *)

Module PositiveEqtype <: EQTYPE.
  Definition t := pos_eqType.
End PositiveEqtype.

Module NEqtype <: EQTYPE.
  Definition t := N_eqType.
End NEqtype.

Module ZEqtype <: EQTYPE.
  Definition t := Z_eqType.
End ZEqtype.



(** Additional Lemmas *)

Section ZLemmas.

  Local Open Scope Z_scope.

  Lemma Z_ltP : forall x y : Z, reflect (x < y) (x <? y).
  Proof.
    move=> x y.
    move: (Z.ltb_lt x y) => [H1 H2].
    case H: (x <? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma Z_leP : forall x y : Z, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y.
    move: (Z.leb_le x y) => [H1 H2].
    case H: (x <=? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

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

  Lemma two_power_of_nat_gt0 n : 2 ^ Z.of_nat n > 0.
  Proof.
    rewrite -two_p_equiv. apply: two_p_gt_ZERO. exact: Nat2Z.is_nonneg.
  Qed.

  Lemma zero_lt_two_power_of_nat n : 0 < 2 ^ Z.of_nat n.
  Proof.
    apply: Z.gt_lt. exact: two_power_of_nat_gt0.
  Qed.

  Lemma two_power_of_nat_ne0 n : 2 ^ Z.of_nat n <> 0.
  Proof.
    move=> H. apply: (Z.lt_neq _ _ (zero_lt_two_power_of_nat n)).
    symmetry. exact: H.
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

  Lemma Zsplit_l :
    forall h l n p,
      0 <= l < 2^p ->
      h * 2^p + l = n ->
      l = n mod (2^p).
  Proof.
    move=> h l n p Hl Heq.
    apply: (Zmod_unique_full _ _ h).
    - by left.
    - by rewrite Z.mul_comm Heq.
  Qed.

  Lemma Zsplit_h :
    forall h l n p,
      0 <= l < 2^p ->
      h * 2^p + l = n ->
      h = n / (2^p).
  Proof.
    move=> h l n p Hl Heq.
    apply: (Zdiv_unique _ _ _ l).
    - exact: Hl.
    - by rewrite Z.mul_comm Heq.
  Qed.

  Lemma Zpower_nat_gt0 n p :
    n > 0 ->
    Zpower_nat n p > 0.
  Proof.
    elim: p n => /=.
    - done.
    - move=> p IH n Hn.
      exact: (Zmult_gt_0_compat _ _ Hn (IH _ Hn)).
  Qed.

  Lemma Zpow_pos_gt0 n p :
    n > 0 ->
    Z.pow_pos n p > 0.
  Proof.
    rewrite Zpower_pos_nat.
    exact: Zpower_nat_gt0.
  Qed.

  Lemma Zdiv_mul_lt_l x y p :
    0 <= x < p -> 0 <= y < p -> (x * y) / p < p.
  Proof.
    move=> [Hx1 Hx2] [Hy1 Hy2].
    have: 0 < p by omega.
    move=> Hp.
    exact: (Zdiv_lt_upper_bound (x * y) p p Hp (Z.mul_lt_mono_nonneg _ _ _ _ Hx1 Hx2 Hy1 Hy2)) => H.
  Qed.

  Lemma Zhalf_bit_double (n : Z) (b : bool) :
    Z.div2 (Z.b2z b + n * 2) = n.
  Proof.
    rewrite Zdiv2_div Z_div_plus.
    - by case: b.
    - done.
  Qed.

  Lemma Zmul2l_add (n : Z) : 2 * n = n + n.
  Proof.
    replace 2 with (Z.succ 1) by reflexivity.
    rewrite Z.mul_succ_l Z.mul_1_l. reflexivity.
  Qed.

  Lemma Zmul2r_add (n : Z) : n * 2 = n + n.
  Proof.
    rewrite Z.mul_comm. exact: Zmul2l_add.
  Qed.

  Lemma Zmod_mul2_sub1 n : 0 < n -> (n * 2 - 1) mod n = n - 1.
  Proof.
    move=> Hn. rewrite Zmul2r_add -Z.add_sub_assoc Z.add_comm.
    rewrite -{2}(Z.mul_1_l n) Z_mod_plus_full Zmod_small; first by reflexivity.
    split.
    - exact: (proj1 (Z.lt_le_pred _ _) Hn).
    - exact: (Z.lt_pred_l).
  Qed.

  Lemma divn_muln2_subn1 n : 0 < n -> (n * 2 - 1) / n = 1.
  Proof.
    move=> Hn1.
    move: (not_eq_sym (Z.lt_neq _ _ Hn1)) => Hn2.
    move: (Z_div_mod_eq (n * 2 - 1) n (Z.lt_gt _ _ Hn1)).
    rewrite (Zmod_mul2_sub1 Hn1).
    replace (n * 2 - 1) with (n + (n - 1)) by ring.
    move=> H. move: (proj1 (Z.add_cancel_r _ _ _) H) => {H} H.
    exact: (proj1 (Z.mul_id_r _ _ Hn2) (Logic.eq_sym H)).
  Qed.

  Lemma ltn_ltn_addn_divn x y n :
    0 <= x < n -> 0 <= y < n -> Zdiv (x + y) n = 0 \/ Zdiv (x + y) n = 1.
  Proof.
    move=> [Hx1 Hx2] [Hy1 Hy2].
    move: (Z.le_lt_trans _ _ _ Hx1 Hx2) => Hn1.
    move: (Z.lt_gt _ _ Hn1) => Hn2.
    move: (not_eq_sym (Z.lt_neq _ _ Hn1)) => Hn3.
    move: (Z.add_le_mono _ _ _ _ Hx1 Hy1) => /= Hxy1.
    move: (Z.add_lt_mono _ _ _ _ Hx2 Hy2) => Hxy2.
    move: (proj1 (Z.lt_le_pred (x + y) (n + n)) Hxy2) => {Hxy2} Hxy2.
    move: (Z.lt_ge_cases (x + y) n); case => Hxy3.
    - rewrite (Z.div_small _ _ (conj Hxy1 Hxy3)). left; reflexivity.
    - move: (Z_div_le _ _ _ Hn2 Hxy3).
      rewrite (Z_div_same_full _ Hn3) => Hdiv1.
      move: (Z_div_le _ _ _ Hn2 Hxy2).
      rewrite -Zmul2r_add (divn_muln2_subn1 Hn1) => Hdiv2.
      right. exact: (Z.le_antisymm _ _ Hdiv2 Hdiv1).
  Qed.

  Lemma Zdiv_eucl_q (n d q r : Z) :
    (q, r) = Z.div_eucl n d ->
    q = n / d.
  Proof.
    move=> Hqr. rewrite /Z.div -Hqr. reflexivity.
  Qed.

  Lemma Zdiv_eucl_r (n d q r : Z) :
    (q, r) = Z.div_eucl n d ->
    r = n mod d.
  Proof.
    move=> Hqr. rewrite /Z.modulo -Hqr. reflexivity.
  Qed.

  Lemma Zdiv_eucl_q_ge0 (a b : Z) :
    let (q, r) := Z.div_eucl a b in
    0 <= a -> 0 <= b -> 0 <= q.
  Proof.
    set tmp := Z.div_eucl a b.
    have: tmp = Z.div_eucl a b by reflexivity.
    destruct tmp as [q r]. move=> Heucl Ha Hb.
    rewrite (Zdiv_eucl_q Heucl).
    case: (proj1 (Z.lt_eq_cases 0 b) Hb) => {Hb} Hb.
    - exact: (Z.ge_le _ _ (Z_div_ge0 _ _ (Z.lt_gt _ _ Hb) (Z.le_ge _ _ Ha))).
    - by rewrite -Hb Zdiv_0_r.
  Qed.

  Lemma Zmod_sub (n m : Z) :
    m <= n -> n mod m = (n - m) mod m.
  Proof.
    move=> Hmn. rewrite -(Z_mod_plus_full (n - m) 1).
    rewrite Z.mul_1_l. rewrite -Z.sub_sub_distr Z.sub_diag Z.sub_0_r.
    reflexivity.
  Qed.

  Lemma Nat2Z_inj_odd (n : nat) :
    Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    elim: n.
    - reflexivity.
    - move=> n IH. rewrite -Nat.add_1_r Nat2Z.inj_add Z.odd_add Nat.odd_add /=.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma Nat2Z_inj_pow (n m : nat) :
    Z.of_nat (Nat.pow n m) = Z.pow (Z.of_nat n) (Z.of_nat m).
  Proof.
    elim: m n.
    - reflexivity.
    - move=> n IH m.
      rewrite Nat2Z.inj_mul IH -!Zpower_nat_Z -Zpower_nat_succ_r.
      reflexivity.
  Qed.

  Import ssrnat div.

  Lemma Nat2Z_inj_modn (n m : nat) :
    (m != 0)%N ->
    Z.of_nat (div.modn n m) = (Z.of_nat n) mod (Z.of_nat m).
  Proof.
    move=> Hm0. case H: (n < m)%N.
    - rewrite (modn_small H) Zmod_small; first reflexivity.
      split; first exact: Nat2Z.is_nonneg. apply: (proj1 (Nat2Z.inj_lt _ _)).
      apply: ltn_lt. exact: H.
    - move/negP/idP: H; rewrite -leqNgt => H.
      move: m H Hm0. induction n using nat_strong_ind.
      move=> m Hmn Hm0. have HmnZ: Z.of_nat m <= Z.of_nat n.
      { apply: (proj1 (Nat2Z.inj_le _ _)). apply: leq_le. exact: Hmn. }
      rewrite (modn_subn Hmn) (Zmod_sub HmnZ).
      case Hsub: ((n - m) < m)%N.
      + have HsubZ: Z.of_nat n - Z.of_nat m < Z.of_nat m.
        { rewrite -(Nat2Z.inj_sub _ _ (leq_le Hmn)).
          apply: (proj1 (Nat2Z.inj_lt _ _)). apply: ltn_lt. exact: Hsub. }
        have Hge0: 0 <= Z.of_nat n - Z.of_nat m.
        { apply: (proj2 (Z.le_0_sub _ _)). apply: (proj1 (Nat2Z.inj_le _ _)).
          apply: leq_le. exact: Hmn. }
        rewrite (modn_small Hsub) (Zmod_small _ _ (conj Hge0 HsubZ)).
        rewrite subn_sub (Nat2Z.inj_sub _ _ (leq_le Hmn)). reflexivity.
      + move/negP/idP: Hsub; rewrite -leqNgt => Hsub.
        rewrite -(Nat2Z.inj_sub _ _ (leq_le Hmn)). apply: H.
        * rewrite -lt0n in Hm0. rewrite -{2}(subn0 n). apply: ltn_sub2l.
          -- exact: (ltn_leq_trans Hm0 Hmn).
          -- exact: Hm0.
        * exact: Hsub.
        * exact: Hm0.
  Qed.

  Lemma Nat2Z_inj_divn (n m : nat) :
    Z.of_nat (div.divn n m) = (Z.of_nat n) / (Z.of_nat m).
  Proof.
    case Hm0: (m == 0)%N.
    - rewrite (eqP Hm0) divn0 Zdiv_0_r. reflexivity.
    - move/negP/idP: Hm0=> Hm0. have Hne: (m <> 0)%N by move/eqP: Hm0; apply.
      case Hnm: (n < m)%N.
      + rewrite (divn_small Hnm) Zdiv_small; first reflexivity.
        split; first exact: Nat2Z.is_nonneg. apply: (proj1 (Nat2Z.inj_lt _ _)).
        apply: ltn_lt. exact: Hnm.
      + move/negP/idP: Hnm; rewrite -leqNgt => Hnm. move: (eq_refl n).
        rewrite {1}(divn_eq n m). have Hmod: (n %% m <= n)%N.
        { apply: ltnW. apply: (ltn_leq_trans _ Hnm). rewrite ltn_mod.
          rewrite lt0n. exact: Hm0. }
        rewrite (addn_subn _ Hmod). move=> H. have HneZ: Z.of_nat m <> 0.
        { move=> Heq; apply: Hne. apply: Nat2Z.inj. exact: Heq. }
        apply: (proj1 (Z.mul_cancel_r (Z.of_nat (n %/ m))
                                      (Z.of_nat n / Z.of_nat m)
                                      (Z.of_nat m) HneZ)).
        rewrite -Nat2Z.inj_mul -muln_mul. rewrite (eqP H).
        rewrite (Nat2Z.inj_sub _ _ (leq_le Hmod)) (Nat2Z_inj_modn _ Hm0).
        symmetry.
        apply: (proj1 (Z.add_move_l (Z.of_nat n mod Z.of_nat m)
                                    (Z.of_nat n / Z.of_nat m * Z.of_nat m)
                                    (Z.of_nat n))).
        rewrite Z.add_comm Z.mul_comm -Z_div_mod_eq; first reflexivity.
        change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_gt _ _)).
        apply: gtn_gt. rewrite lt0n. exact: Hm0.
  Qed.

  Local Close Scope Z_scope.

End ZLemmas.



(** An ordered type for positive with a Boolean equality in mathcomp. *)

Module PositiveOrderMinimal <: SsrOrderedTypeMinimal.

  Local Open Scope positive_scope.

  Definition t : eqType := pos_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := fun x y => Pos.ltb x y.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z Hxy Hyz.
    move/pos_ltP: Hxy; move/pos_ltP: Hyz => Hyz Hxy.
    apply/pos_ltP.
    exact: (Pos.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y Hlt.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (Pos.lt_irrefl y).
    apply/pos_ltP.
    assumption.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case H: (Pos.compare x y).
    - apply: EQ.
      move: (Pos.compare_eq_iff x y) => [Hc _].
      apply/eqP.
      exact: (Hc H).
    - apply: LT.
      move: (Pos.compare_lt_iff x y) => [Hc _].
      apply/pos_ltP.
      exact: (Hc H).
    - apply: GT.
      move: (Pos.compare_gt_iff x y) => [Hc _].
      apply/pos_ltP.
      exact: (Hc H).
  Defined.

  Local Close Scope positive_scope.

End PositiveOrderMinimal.

Module PositiveOrder <: SsrOrderedType := MakeSsrOrderedType PositiveOrderMinimal.



(** An ordered type for N with a Boolean equality in mathcomp. *)

Module NOrderMinimal <: SsrOrderedTypeMinimal.

  Local Open Scope N_scope.

  Definition t : eqType := N_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := fun x y => N.ltb x y.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z Hxy Hyz.
    move/N_ltP: Hxy; move/N_ltP: Hyz => Hyz Hxy.
    apply/N_ltP.
    exact: (N.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y Hlt.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (N.lt_irrefl y).
    apply/N_ltP.
    assumption.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case H: (N.compare x y).
    - apply: EQ.
      move: (N.compare_eq_iff x y) => [Hc _].
      apply/eqP.
      exact: (Hc H).
    - apply: LT.
      move: (N.compare_lt_iff x y) => [Hc _].
      apply/N_ltP.
      exact: (Hc H).
    - apply: GT.
      move: (N.compare_gt_iff x y) => [Hc _].
      apply/N_ltP.
      exact: (Hc H).
  Defined.

  Local Close Scope N_scope.

End NOrderMinimal.

Module NOrder <: SsrOrderedType := MakeSsrOrderedType NOrderMinimal.



(** An ordered type for Z with a Boolean equality in mathcomp. *)

Module ZOrderMinimal <: SsrOrderedTypeMinimal.

  Local Open Scope Z_scope.

  Definition t : eqType := Z_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := fun x y => Z.ltb x y.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z Hxy Hyz.
    move/Z_ltP: Hxy; move/Z_ltP: Hyz => Hyz Hxy.
    apply/Z_ltP.
    exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y Hlt.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (Z.lt_irrefl y).
    apply/Z_ltP.
    assumption.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case H: (Z.compare x y).
    - apply: EQ.
      move: (Z.compare_eq_iff x y) => [Hc _].
      apply/eqP.
      exact: (Hc H).
    - apply: LT.
      move: (Z.compare_lt_iff x y) => [Hc _].
      apply/Z_ltP.
      exact: (Hc H).
    - apply: GT.
      move: (Z.compare_gt_iff x y) => [Hc _].
      apply/Z_ltP.
      exact: (Hc H).
  Defined.

  Local Close Scope Z_scope.

End ZOrderMinimal.

Module ZOrder <: SsrOrderedType := MakeSsrOrderedType ZOrderMinimal.



(** Equality Modulo *)

From GBArith Require GBZArith.

Notation modulo := GBZArith.modulo.

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

  Require Import Nsatz.

  Lemma modulo_plus x y a b p :
    modulo x a p -> modulo y b p ->
    modulo (x + y) (a + b) p.
  Proof.
    move=> [k1 H1] [k2 H2].
    exists (k1 + k2).
    nsatz.
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
