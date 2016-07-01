
From Coq Require Import OrderedType FMaps FSets ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype tuple.
Require Import ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Structure with a base type t. *)

Module NatType <: Equalities.Typ.
  Definition t : Set := nat.
End NatType.

Module IntType <: Equalities.Typ.
  Definition t : Set := int.
End IntType.

Module ZType <: Equalities.Typ.
  Definition t : Set := Z.
End ZType.



(** Structure with a base eqType t. *)

Module Type EQTYPE.
  Parameter t : eqType.
End EQTYPE.

Module NatEqtype <: EQTYPE.
  Definition t := nat_eqType.
End NatEqtype.

Module IntEqtype <: EQTYPE.
  Definition t := int_eqType.
End IntEqtype.

Module ZEqtype <: EQTYPE.
  Definition t := Z_eqType.
End ZEqtype.



(** Structure with a base type t equipped with a reflectable Boolean equality. *)

Module Type HAS_REFLECTABLE_EQB (Import X : Equalities.Typ).
  Parameter Inline eqb : t -> t -> bool.
  Parameter Inline eqb_refl : forall x : t, eqb x x.
  Parameter Inline eqb_eq : forall x y : t, eqb x y -> x = y.
End HAS_REFLECTABLE_EQB.

Module Type REFLECTABLE := Equalities.Typ <+ HAS_REFLECTABLE_EQB.

Module MakeReflection (X : REFLECTABLE).

  Lemma eqbP : Equality.axiom X.eqb.
  Proof.
    move=> x y.
    case H: (X.eqb x y).
    - apply: ReflectT.
      apply: X.eqb_eq.
      assumption.
    - apply: ReflectF.
      move/idP/eqP/eqP: H => Hne Heq; apply: Hne.
      rewrite Heq.
      exact: X.eqb_refl.
  Qed.

  Canonical reflectable_Mixin := EqMixin eqbP.
  Canonical reflectable_eqType := Eval hnf in EqType X.t reflectable_Mixin.

End MakeReflection.



(** Make (option t) an eqType given that t is an eqType. *)

Module MakeOptionReflectable (X : EQTYPE).

  Definition option_eqb (x y : option X.t) : bool :=
    match x, y with
    | None, None => true
    | None, Some _ => false
    | Some _, None => false
    | Some a, Some b => a == b
    end.

  Lemma option_eqbP : Equality.axiom option_eqb.
  Proof.
    move=> x y; case: y; case: x => /=.
    - move=> x y.
      case H: (x == y).
      + apply: ReflectT.
        rewrite (eqP H).
        reflexivity.
      + apply: ReflectF.
        move=> Heq.
        move/idP/eqP/eqP: H; apply.
        case: Heq => Heq; rewrite Heq.
        exact: eqxx.
    - move=> y.
      apply: ReflectF.
      move=> H; discriminate.
    - move=> x.
      apply: ReflectF.
      move=> H; discriminate.
    - apply: ReflectT.
      reflexivity.
  Qed.

  Canonical option_Mixin := EqMixin option_eqbP.
  Canonical option_eqType := Eval hnf in EqType (option X.t) option_Mixin.

End MakeOptionReflectable.

Module OptionIntEqtype <: EQTYPE.
  Module OptionInt := MakeOptionReflectable(IntEqtype).
  Definition t := OptionInt.option_eqType.
End OptionIntEqtype.

Module OptionNatEqtype <: EQTYPE.
  Module OptionNat := MakeOptionReflectable(NatEqtype).
  Definition t := OptionNat.option_eqType.
End OptionNatEqtype.



(** Coq OrderedType with Boolean equality. *)

Module Type SsrOrderedType <: OrderedType.
  Parameter T : eqType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Parameter Inline lt : t -> t -> Prop.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End SsrOrderedType.
