
(** * Some auxiliary lemmas for FSets. *)

From Coq Require Import FSets OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Module FSetLemmas (S : FSetInterface.S).

  Module F := Facts(S).
  Module OP := OrdProperties(S).
  Include F.
  Include OP.

  Lemma memP x (s : S.t) : reflect (S.In x s) (S.mem x s).
  Proof.
    case H: (S.mem x s).
    - apply: ReflectT.
      exact: (S.mem_2 H).
    - apply: ReflectF.
      move=> Hin; move: (S.mem_1 Hin).
      rewrite H; discriminate.
  Qed.

  Lemma mem_add_eq :
    forall x y s,
      S.E.eq x y ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s Heq.
    apply: S.mem_1.
    apply: S.add_1.
    apply: S.E.eq_sym.
    assumption.
  Qed.

  Lemma mem_add_neq :
    forall x y s,
      ~ (S.E.eq x y) ->
      S.mem x (S.add y s) = S.mem x s.
  Proof.
    move=> x y s Hne.
    apply: add_neq_b.
    move=> Heq.
    apply: Hne.
    apply: S.E.eq_sym.
    assumption.
  Qed.

  Lemma mem_in_elements :
    forall x s,
      S.mem x s ->
      InA S.E.eq x (S.elements s).
  Proof.
    move=> x s Hmem.
    apply: S.elements_1.
    apply/memP.
    assumption.
  Qed.

  Lemma in_elements_mem :
    forall x s,
      InA S.E.eq x (S.elements s) ->
      S.mem x s.
  Proof.
    move=> x s Hin.
    apply/memP.
    apply: S.elements_2.
    assumption.
  Qed.

End FSetLemmas.

Module Make (V : SsrOrderedType).
  Module S := FSetList.Make V.
  Module Lemmas := FSetLemmas(S).
  Include S.
End Make.