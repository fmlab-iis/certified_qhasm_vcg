
From mathcomp Require Import ssreflect ssrbool ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma singleton_seq A (l : seq A) :
  size l = 1%N -> exists x : A, l = x :: nil.
Proof.
  elim: l => //=.
  move=> hd tl; elim tl => //=.
  move=> _ _; exists hd.
  reflexivity.
Qed.

Lemma last_decomp A (l : seq A) (n : nat) :
  size l = (n + 1)%N -> exists s x, l = rcons s x.
Proof.
  move: l n. apply: last_ind => /=.
  - by case.
  - move=> l x IH n H. exists l; exists x; reflexivity.
Qed.

Lemma last_default_irrelevant A (l : seq A) (n : nat) b1 b2 :
  size l = (n + 1)%N -> last b1 l = last b2 l.
Proof.
  move: l n b1 b2. apply: last_ind => /=.
  - move=> n b1 b2; by case n.
  - move=> l lst IH n b1 b2 H. rewrite !last_rcons. reflexivity.
Qed.
