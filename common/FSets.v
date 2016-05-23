
(** * Some auxiliary lemmas for FSets. *)

From Coq Require Import FSets OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.

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

End FSetLemmas.
