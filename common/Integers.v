
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun choice eqtype.
From CompCert Require Import Integers.
From Common Require Import Bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** byte, int, and int64 are eqTypes. *)

Definition byte_eq : byte -> byte -> bool := Byte.eq.
Definition int_eq : int -> int -> bool := Int.eq.
Definition int64_eq : int64 -> int64 -> bool := Int64.eq.

Ltac prove_int_eqtype :=
  let eq :=
      match goal with
      | |- Equality.axiom byte_eq => byte_eq
      | |- Equality.axiom int_eq => int_eq
      | |- Equality.axiom int64_eq => int64_eq
      | |- _ => fail
      end in
  let meq :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.eq
      | |- Equality.axiom int_eq => Int.eq
      | |- Equality.axiom int64_eq => Int64.eq
      | |- _ => fail
      end in
  let unsigned :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.unsigned
      | |- Equality.axiom int_eq => Int.unsigned
      | |- Equality.axiom int64_eq => Int64.unsigned
      | |- _ => fail
      end in
  let repr :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.repr
      | |- Equality.axiom int_eq => Int.repr
      | |- Equality.axiom int64_eq => Int64.repr
      | |- _ => fail
      end in
  let repr_unsigned :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.repr_unsigned
      | |- Equality.axiom int_eq => Int.repr_unsigned
      | |- Equality.axiom int64_eq => Int64.repr_unsigned
      | |- _ => fail
      end in
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in
  let Hnm := fresh "Hnm" in
  rewrite /eq /meq /Coqlib.zeq => n m;
  case: (Z.eq_dec (unsigned n) (unsigned m)) => H;
  [
    apply: ReflectT;
    have: repr (unsigned n) = repr (unsigned m);
    [
      rewrite H; reflexivity |
      rewrite 2!repr_unsigned; move=> Hnm; exact: Hnm
    ] |
    apply: ReflectF; move=> Hnm; apply: H; rewrite Hnm; reflexivity
  ].

Lemma byte_eqP : Equality.axiom byte_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical byte_eqMixin := EqMixin byte_eqP.
Canonical byte_eqType := Eval hnf in EqType byte byte_eqMixin.

Lemma int_eqP : Equality.axiom int_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical int_eqMixin := EqMixin int_eqP.
Canonical int_eqType := Eval hnf in EqType int int_eqMixin.

Lemma int64_eqP : Equality.axiom int64_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical int64_eqMixin := EqMixin int64_eqP.
Canonical int64_eqType := Eval hnf in EqType int64 int64_eqMixin.



(** Conversion from hex strings to CompCert integers. *)

Section HexStrings.

  From Coq Require Import Ascii.

  Lemma bits_range n (x : BITS n) : (-1 < toPosZ x < two_p (Z.of_nat n))%Z.
  Proof.
    split.
    - apply: (Z.lt_le_trans _ 0).
      + done.
      + exact: toPosZ_min.
    - rewrite two_p_correct -two_power_nat_equiv.
      exact: toPosZ_max.
  Qed.

  Definition byte_of_bits8 (n : BITS 8) : byte :=
    {| Byte.intval := toPosZ n; Byte.intrange := bits_range n |}.

  Definition int_of_bits32 (n : BITS 32) : int :=
    {| Int.intval := toPosZ n; Int.intrange := bits_range n |}.

  Definition int64_of_bits64 (n : BITS 64) : int64 :=
    {| Int64.intval := toPosZ n; Int64.intrange := bits_range n |}.

  Definition byte_of_hex (str : 2.-string) : byte :=
    byte_of_bits8 (fromNString str).

  Definition int_of_hex (str : 8.-string) : int :=
    int_of_bits32 (fromNString str).

  Definition int64_of_hex (str : 16.-string) : int64 :=
    int64_of_bits64 (fromNString str).

End HexStrings.
