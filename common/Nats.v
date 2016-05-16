
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
Require Import Types.

Section NatLemmas.

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

End NatLemmas.



(** An ordered type for nat with a Boolean equality in mathcomp. *)

Module NatOrder <: SsrOrderedType <: OrderedType.

  Definition T : eqType := nat_eqType.

  Definition t : Type := T.

  Definition eq : t -> t -> Prop := fun x y : t => x == y.

  Definition lt : t -> t -> Prop := fun x y => x < y.

  Hint Unfold eq lt.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eq_refl.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y.
    by rewrite /eq eq_sym.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z.
    rewrite /eq => Hxy Hyz.
    move/eqP: Hxy => Hxy.
    move/eqP: Hyz => Hyz.
    apply/eqP.
    by rewrite Hxy Hyz.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    exact: ltn_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt.
    move/eqP => Heq.
    apply/idP: Hlt.
    by rewrite Heq ltnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    elim.
    - elim.
      + by apply: EQ.
      + move=> n Hc; by apply: LT.
    - move=> n Hn [].
      + by apply: GT.
      + move=> m.
        case: (Hn m) => Hc.
        * by apply: LT.
        * by apply: EQ.
        * by apply: GT.
  Defined.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    move=> x y.
    apply: eq_comparable.
  Qed.

End NatOrder.
