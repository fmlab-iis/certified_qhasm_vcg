
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Coq OrderedType with Boolean equality. *)

Module Type SsrOrderedTypeMinimal.
  Parameter t : eqType.
  Definition eq : t -> t -> bool := fun x y => x == y.
  Parameter lt : t -> t -> bool.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> x != y.
  Parameter compare : forall x y : t, Compare lt eq x y.
End SsrOrderedTypeMinimal.

Module Type SsrOrderedType <: OrderedType.
  Parameter T : eqType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Parameter ltb : t -> t -> bool.
  Definition lt : t -> t -> Prop := fun x y => ltb x y.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End SsrOrderedType.

Module MakeSsrOrderedType (M : SsrOrderedTypeMinimal) <: SsrOrderedType.
  Definition T : eqType := M.t.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Definition ltb : t -> t -> bool := M.lt.
  Definition lt : t -> t -> Prop := fun x y => ltb x y.
  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eqxx.
  Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y H.
    rewrite /eq eq_sym.
    exact: H.
  Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z Hxy Hyz.
    rewrite (eqP Hxy).
    exact: Hyz.
  Qed.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z :=
    M.lt_trans.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt Heq.
    move/negP: (M.lt_not_eq Hlt).
    apply.
    assumption.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y := M.compare.
  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.
End MakeSsrOrderedType.



(** Product of ordered types. *)

Module MakeProdEqType (O1 O2 : EQTYPE).
  Definition t : Type := (O1.t * O2.t).
  Definition eq : t -> t -> bool :=
    fun x y => (fst x == fst y) && (snd x == snd y).
  Lemma eqP : Equality.axiom eq.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    rewrite /eq /=.
    case H1: (x1 == y1); case H2: (x2 == y2).
    - apply: ReflectT.
      rewrite (eqP H1) (eqP H2).
      reflexivity.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H2.
      rewrite H2'.
      exact: eqxx.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H1.
      rewrite H1'.
      exact: eqxx.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H1.
      rewrite H1'.
      exact: eqxx.
  Qed.
  Definition prod_eqMixin := EqMixin eqP.
  Canonical prod_eqType := Eval hnf in EqType t prod_eqMixin.
End MakeProdEqType.

Module MakeProdOrderedMinimal (O1 O2 : SsrOrderedType) <: SsrOrderedTypeMinimal.

  Module E1 <: EQTYPE.
    Definition t : eqType := O1.T.
  End E1.

  Module E2 <: EQTYPE.
    Definition t : eqType := O2.T.
  End E2.

  Module P := MakeProdEqType E1 E2.

  Definition t : eqType := P.prod_eqType.

  Definition eq : t -> t -> bool := fun x y => x == y.

  Definition lt : t -> t -> bool :=
    fun x y =>
      if O1.ltb (fst x) (fst y) then true
      else if (fst x) == (fst y) then O2.ltb (snd x) (snd y)
           else false.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> [] x1 x2 [] y1 y2 [] z1 z2.
    rewrite /lt /=.
    case Hx1y1: (O1.ltb x1 y1).
    - case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        move: (O1.lt_trans Hx1y1 Hy1z1) => Hx1z1'.
        rewrite /O1.lt Hx1z1 in Hx1z1'.
        done.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * rewrite (eqP Ex1z1) -(eqP Ey1z1) in Hx1y1.
          apply: False_ind.
          apply: (O1.lt_not_eq Hx1y1).
          exact: O1.eq_refl.
        * rewrite (eqP Ey1z1) in Hx1y1.
          rewrite Hx1y1 in Hx1z1.
          discriminate.
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        rewrite (eqP Ex1y1) Hy1z1 in Hx1z1.
        discriminate.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * move=> _ _; exact: (O2.lt_trans Hx2y2 Hy2z2).
        * move: (O1.eq_trans Ex1y1 Ey1z1).
          rewrite /O1.eq Ex1z1.
          done.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    rewrite /lt /=.
    case Hx1y1: (O1.ltb x1 y1).
    - move=> _.
      apply/eqP => H.
      case: H => H1 _.
      apply: (O1.lt_not_eq Hx1y1).
      by apply/eqP.
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      move=> _.
      apply/eqP => H.
      case: H => _ H2.
      apply: (O2.lt_not_eq Hx2y2).
      by apply/eqP.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    move: (O1.compare x1 y1) (O2.compare x2 y2) => Hc1 Hc2.
    inversion_clear Hc1.
    - apply: LT.
      rewrite /lt /=.
      rewrite /O1.lt in H.
      by rewrite H.
    - inversion_clear Hc2.
      + apply: LT.
        rewrite /lt /=.
        case Hx1y1: (O1.ltb x1 y1); [done | idtac].
        rewrite H.
        exact: H0.
      + apply: EQ.
        rewrite /eq /=.
        by apply/andP; split; assumption.
      + apply: GT.
        rewrite /lt /=.
        case Hy1x1: (O1.ltb y1 x1); [done | idtac].
        rewrite (O1.eq_sym H).
        exact: H0.
    - apply: GT.
      rewrite /lt /=.
      by rewrite H.
  Defined.

End MakeProdOrderedMinimal.

Module MakeProdOrdered (O1 O2 : SsrOrderedType) <: SsrOrderedType.
  Module M := MakeProdOrderedMinimal O1 O2.
  Module P := MakeSsrOrderedType M.
  Include P.
End MakeProdOrdered.



(** Union of ordered types. *)

Module MakeUnionOrderedMinimal
       (V1 : SsrOrderedType) (V2 : SsrOrderedType) <: SsrOrderedTypeMinimal.

  Inductive ut : Type :=
  | C1 : V1.t -> ut
  | C2 : V2.t -> ut.

  Definition uo_eqb (x y : ut) : bool :=
    match x, y with
    | C1 x, C1 y => x == y
    | C2 x, C2 y => x == y
    | _, _ => false
    end.

  Lemma uo_eqP : Equality.axiom uo_eqb.
  Proof.
    move=> x y.
    case H: (uo_eqb x y).
    - apply: ReflectT.
      move: H; case: y; case: x => //=.
      + move=> x y H.
        rewrite (eqP H).
        reflexivity.
      + move=> x y H.
        rewrite (eqP H).
        reflexivity.
    - apply: ReflectF.
      move: H; case: y; case: x => //=.
      + move=> x y H1 [] H2.
        apply/negPf: H1.
        rewrite H2; exact: eqxx.
      + move=> x y H1 [] H2.
        apply/negPf: H1.
        rewrite H2; exact: eqxx.
  Qed.

  Canonical uo_eqMixin := EqMixin uo_eqP.
  Canonical uo_eqType := Eval hnf in EqType ut uo_eqMixin.

  Definition t : eqType := uo_eqType.

  Definition eq : t -> t -> bool := uo_eqb.

  Definition lt (x y : t) : bool :=
    match x, y with
    | C1 x, C1 y => V1.ltb x y
    | C1 _, C2 _ => true
    | C2 _, C1 _ => false
    | C2 x, C2 y => V2.ltb x y
    end.

  Lemma lt_trans :
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    case: z; case: y; case: x => //=.
    - exact: V1.lt_trans.
    - exact: V2.lt_trans.
  Qed.

  Lemma lt_not_eq :
    forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y; case: y; case: x => //=.
    - move=> x y H.
      apply/negP.
      exact: V1.lt_not_eq.
    - move=> x y H.
      apply/negP.
      exact: V2.lt_not_eq.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case: y; case: x.
    - move=> x y.
      case H: (V1.compare x y).
      + apply: LT; assumption.
      + apply: EQ; assumption.
      + apply: GT; assumption.
    - move=> x y.
      by apply: GT.
    - move=> x y.
      by apply: LT.
    - move=> x y.
      case H: (V2.compare x y).
      + apply: LT; assumption.
      + apply: EQ; assumption.
      + apply: GT; assumption.
  Defined.

End MakeUnionOrderedMinimal.

Module MakeUnionOrdered
       (V1 : SsrOrderedType) (V2 : SsrOrderedType) <: SsrOrderedType.
  Module M := MakeUnionOrderedMinimal V1 V2.
  Module O := MakeSsrOrderedType M.
  Include O.
  Definition c1 (x : V1.t) : t := M.C1 x.
  Definition c2 (x : V2.t) : t := M.C2 x.
End MakeUnionOrdered.



(** A singleton ordered type. *)

Module UnitOrderedMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := unit_eqType.

  Definition eq (x y : t) : bool := x == y.

  Definition lt (x y : t) : bool := false.

  Lemma lt_trans :
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    done.
  Qed.

  Lemma lt_not_eq :
    forall x y : t, lt x y -> x != y.
  Proof.
    done.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    by apply: EQ.
  Defined.

End UnitOrderedMinimal.

Module UnitOrdered <: SsrOrderedType.
  Module O := MakeSsrOrderedType UnitOrderedMinimal.
  Include O.
End UnitOrdered.
