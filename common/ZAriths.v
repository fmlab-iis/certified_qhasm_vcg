
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssralg ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
