
From Coq Require Import Arith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat div eqtype.
From Common Require Import Types SsrOrdered.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section NatLemmas.

  Lemma addn_add n m :
    n + m = (n + m)%coq_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma muln_mul n m :
    n * m = (n * m)%coq_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma leq_le_iff n m : n <= m <-> (n <= m)%coq_nat.
  Proof.
    elim: m n => /=.
    - move=> n; split => H.
      + rewrite /leq subn0 in H. rewrite (eqP H). done.
      + inversion_clear H. done.
    - move=> m IH n; split => H.
      + apply: (proj1 (Nat.le_pred_le_succ n m)). apply: (proj1 (IH (n.-1))).
        rewrite -subn1 leq_subLR addnC addn1. exact: H.
      + rewrite -addn1 addnC -leq_subLR subn1. apply: (proj2 (IH (n.-1))).
        apply: (proj2 (Nat.le_pred_le_succ n m)). exact: H.
  Qed.

  Lemma leq_le n m : n <= m -> (n <= m)%coq_nat.
  Proof.
    exact: (proj1 (leq_le_iff n m)).
  Qed.

  Lemma le_leq n m : (n <= m)%coq_nat -> n <= m.
  Proof.
    exact: (proj2 (leq_le_iff n m)).
  Qed.

  Lemma ltn_lt_iff n m : n < m <-> (n < m)%coq_nat.
  Proof.
    split => H.
    - apply: (proj1 (Nat.le_succ_l n m)). apply: leq_le. exact: H.
    - apply: le_leq. apply: (proj2 (Nat.le_succ_l n m)). exact: H.
  Qed.

  Lemma ltn_lt n m : n < m -> (n < m)%coq_nat.
  Proof.
    exact: (proj1 (ltn_lt_iff n m)).
  Qed.

  Lemma lt_ltn n m : (n < m)%coq_nat -> n < m.
  Proof.
    exact: (proj2 (ltn_lt_iff n m)).
  Qed.

  Lemma subn_gtn : forall n m r, n < m - r -> r < m.
  Proof.
    move=> n m r H.
    have: r < m.
    - rewrite -(subn_gt0 r m).
      induction n.
      + assumption.
      + by auto.
    - exact.
  Qed.

  Lemma lt_subr_addl : forall n m r : nat, (n < m - r) == (n + r < m).
  Proof.
    move=> n m r.
    case Hrm: (r < m).
    - rewrite -(ltn_add2r r n (m - r)).
      rewrite (subnK (ltnW Hrm)).
      exact: eqxx.
    - (* left is false *)
      move/negP/negP: (Hrm) => Hle.
      rewrite -leqNgt in Hle.
      move: (subn_eq0 m r) => Hsub.
      rewrite Hle in Hsub.
      move/idP/eqP: Hsub => Hsub.
      rewrite Hsub => {Hsub}.
      rewrite ltn0.
      (* right is false *)
      rewrite -(leq_add2l n m r) in Hle.
      move: (leq_trans (leq_addl n m) Hle) => {Hle} Hle.
      rewrite (leqNgt m (n + r)) in Hle.
      move/negPf: Hle => Hle.
      rewrite Hle.
      exact: eqxx.
  Qed.

  Lemma lt_sub1r_add1l : forall n m : nat, (n < m.-1) == (n.+1 < m).
  Proof.
    move=> n m.
    rewrite -{2}addn1 -subn1.
    exact: (lt_subr_addl n m 1).
  Qed.

  Lemma addr_subK : forall n m : nat, n + m - m = n.
  Proof.
    move=> n; elim: n.
    - move=> m.
      rewrite add0n subnn.
      reflexivity.
    - move=> n IH m.
      rewrite -(addnA 1 n m) -addnBA.
      + rewrite IH.
        reflexivity.
      + exact: leq_addl.
  Qed.

  Lemma addl_subK : forall n m : nat, m + n - m = n.
  Proof.
    move=> n m.
    rewrite addnC.
    exact: addr_subK.
  Qed.

  Lemma gt0_sub1F :
    forall n : nat, n > 0 -> n = n - 1 -> False.
  Proof.
    move=> n; elim: n.
    - done.
    - move=> n IH Hgt Heq.
      rewrite -add1n addl_subK add1n in Heq.
      apply: IH.
      + rewrite -Heq.
        assumption.
      + rewrite -{2}Heq -add1n addl_subK.
        reflexivity.
  Qed.

  Lemma ltn_leq_trans n m p :
    m < n -> n <= p -> m < p.
  Proof.
    move=> Hmn Hnp.
    move/ltP: Hmn => Hmn.
    move/leP: Hnp => Hnp.
    apply/ltP.
    exact: (Lt.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma ltn_addn m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> /ltP H1 /ltP H2. apply/ltP. exact: (Nat.add_lt_mono _ _ _ _ H1 H2).
  Qed.

  Lemma ltb_leq n m :
    (n <? m) = true ->
    n <= m.
  Proof.
    move=> H.
    apply/leP.
    move: (Nat.ltb_lt n m) => [H1 _].
    move: (H1 H) => {H1 H} H.
    auto with arith.
  Qed.

  Lemma div2_succ n :
    Nat.div2 (S n) = Nat.odd n + Nat.div2 n.
  Proof.
    case H: (Nat.odd n).
    - move: (proj1 (Nat.odd_spec n) H) => {H} [m H].
      rewrite {n}H.
      have: (((2 * m) + 1).+1 = 2 * (1 + m)) by ring.
      move=> ->. rewrite Nat.div2_double (plus_comm (2 * m) 1)
                         Nat.div2_succ_double.
      reflexivity.
    - move/negPn: H => H. move: (proj1 (Nat.even_spec n) H) => {H} [m H].
      rewrite {n}H Nat.div2_double Nat.div2_succ_double.
      reflexivity.
  Qed.

  Lemma expn_pow n m : n ^ m = Nat.pow n m.
  Proof.
    elim: m.
    - reflexivity.
    - move=> m IH. rewrite expnS (Nat.pow_succ_r _ _ (Nat.le_0_l m)) IH.
      reflexivity.
  Qed.

  Lemma ssrodd_odd n :
    odd n = Nat.odd n.
  Proof.
    elim: n => /=.
    - reflexivity.
    - move=> n IH. rewrite {}IH Nat.odd_succ Nat.negb_odd. reflexivity.
  Qed.

  Lemma ssrdiv2_succ n :
    (n.+1)./2 = odd n + n./2.
  Proof.
    rewrite /half -/uphalf -/half uphalf_half.
    reflexivity.
  Qed.

  Lemma ssrdiv2_div2 n :
    n./2 = Nat.div2 n.
  Proof.
    elim: n.
    - reflexivity.
    - move=> n IH.
      rewrite div2_succ ssrdiv2_succ ssrodd_odd IH.
      reflexivity.
  Qed.

  Lemma modn_muln2_subn1 n : 0 < n -> (n.*2 - 1) %% n = n - 1.
  Proof.
    move=> Hn. rewrite -addnn -(addnBA _ Hn) modnDl.
    apply: modn_small. rewrite subn1 (prednK Hn).
    exact: leqnn.
  Qed.

  Lemma divn_muln2_subn1 n : 0 < n -> (n.*2 - 1) %/ n = 1.
  Proof.
    move=> Hn. move: (divn_eq (n.*2-1) n).
    rewrite (modn_muln2_subn1 Hn) -addnn -{1}(addnBA _ Hn).
    move/eqP => H. rewrite eqn_add2r -{1}(mul1n n) (eqn_pmul2r Hn) in H.
    apply/eqP. rewrite eq_sym. assumption.
  Qed.

  Lemma divn01 x n :
    x < n.*2 -> x %/ n = 0 \/ x %/ n = 1.
  Proof.
    move=> Hx.
    have Hn: n > 0.
    { case: n Hx; first by move=> H; inversion H. move=> n _.
      exact: ltn0Sn. }
    case Hxn: (x < n).
    - rewrite (divn_small Hxn). left; reflexivity.
    - rewrite ltnNge in Hxn. move/negPn: Hxn => Hxn. right.
      rewrite -add1n in Hx. move: (leq_sub2r 1 Hx).
      rewrite addKn => {Hx} Hx.
      move: (leq_div2r n Hx) (leq_div2r n Hxn).
      rewrite divnn Hn /= (divn_muln2_subn1 Hn) => {Hx Hxn} Hx Hxn.
      apply/eqP; rewrite eqn_leq. by rewrite Hx Hxn.
  Qed.

  Lemma odd_divn x n :
    x < n.*2 -> nat_of_bool (odd (x %/ n)) = x %/ n.
  Proof.
    move=> Hx. by case: (divn01 Hx) => ->.
  Qed.

  Lemma odd_divn_eucl x n :
    x < n.*2 ->
    x = odd (x %/ n) * n + x %% n.
  Proof.
    move=> H. rewrite (odd_divn H) -(divn_eq x n). reflexivity.
  Qed.

  Lemma ltn_ltn_addn_divn x y n :
    x < n -> y < n -> (x + y) %/ n = 0 \/ (x + y) %/ n = 1.
  Proof.
    move=> Hx Hy. apply: divn01. rewrite -addnn. exact: (ltn_addn Hx Hy).
  Qed.

  Lemma divn_eq0 n m :
    n %/ m = 0 -> m = 0 \/ n < m.
  Proof.
    move=> Hdivn. move: (divn_eq n m).
    rewrite Hdivn mul0n add0n. move=> Hmodn. case Hm0: (m == 0).
    - left; by rewrite (eqP Hm0).
    - right; rewrite ltnNge. apply/negP => Hmn. rewrite -divn_gt0 in Hmn.
      + rewrite Hdivn in Hmn; by inversion Hmn.
      + rewrite ltn_neqAle eq_sym. move/idP/negP: Hm0.
        move=> H; rewrite H /=. done.
  Qed.

  Lemma divn_gt0_eq0 n m :
    n %/ m = 0 -> m > 0 -> n < m.
  Proof.
    move=> Hdivn Hm.
    case: (divn_eq0 Hdivn).
    - move=> H; rewrite {}H in Hm *. by inversion Hm.
    - by apply.
  Qed.

  Lemma ltn_1_2expnS n :
    1 < 2 ^ n.+1.
  Proof.
    rewrite expnS. apply: leq_pmulr. rewrite expn_gt0. done.
  Qed.

  Lemma modn_muln_modn_l n x y :
    (n %% (x * y)) %% x = n %% x.
  Proof.
    have: (n %% x) = (n %/ (x * y) * (x * y) + n %% (x * y)) %% x.
    { rewrite -(divn_eq n (x * y)). reflexivity. }
    rewrite -modnDm.
    have: (n %/ (x * y) * (x * y)) %% x = 0.
    { rewrite (mulnC x y) mulnA modnMl. reflexivity. }
    move=> ->. rewrite add0n. rewrite modn_mod. move=> <-. reflexivity.
  Qed.

  Lemma modn_muln_modn_r n x y :
    (n %% (x * y)) %% y = n %% y.
  Proof.
    rewrite (mulnC x y). exact: modn_muln_modn_l.
  Qed.

End NatLemmas.



(** EQTYPE modules. *)

Module NatEqtype <: EQTYPE.
  Definition t := nat_eqType.
End NatEqtype.

Module OptionNatEqtype <: EQTYPE.
  Module OptionNat := MakeOptionReflectable(NatEqtype).
  Definition t := OptionNat.option_eqType.
End OptionNatEqtype.



(** An ordered type for nat with a Boolean equality in mathcomp. *)

Module NatOrderMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := nat_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := fun x y => x < y.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    exact: ltn_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y Hlt.
    apply/negP => Heq.
    apply/idP: Hlt.
    by rewrite /lt (eqP Heq) ltnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case H: (Nat.compare x y).
    - apply: EQ.
      move: (PeanoNat.Nat.compare_eq_iff x y) => [Hc _].
      apply/eqP.
      exact: (Hc H).
    - apply: LT.
      move: (PeanoNat.Nat.compare_lt_iff x y) => [Hc _].
      apply/ltP.
      exact: (Hc H).
    - apply: GT.
      move: (PeanoNat.Nat.compare_gt_iff x y) => [Hc _].
      apply/ltP.
      exact: (Hc H).
  Defined.

End NatOrderMinimal.

Module NatOrder <: SsrOrderedType := MakeSsrOrderedType NatOrderMinimal.
