
From Coq Require Import OrderedType ZArith String.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun.
From mathcomp Require Import eqtype div zmodp.
From mathcomp Require Export tuple seq.
From Bits Require Export bits.
From Common Require Import Nats ZAriths Seqs Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Close Scope bits_scope.

Notation "x + y" := (addB x y) : bits_scope.
Notation "x - y" := (subB x y) : bits_scope.
Notation "x * y" := (mulB x y) : bits_scope.
Notation "x < y" := (ltB x y) : bits_scope.
Notation "x <= y" := (leB x y) : bits_scope.



(** Constants *)

Inductive nstring (n : nat) : Set :=
| NString : forall s : string, String.length s = n -> nstring n.

Notation "n .-string" := (nstring n) (at level 4, format "n .-string") : type_scope.

Definition fromNString (n : nat) (s : n.-string) : BITS (n * 4).
Proof.
  destruct s as [s Hlen].
  rewrite -Hlen.
  exact: (fromHex s).
Defined.



(** Lemmas *)

Section BitsLemmas.

  Set Implicit Arguments.

  Lemma ltBnn : forall (n : nat) (x : BITS n), ltB x x = false.
  Proof.
    move=> n x.
    rewrite ltB_nat.
    apply: ltnn.
  Qed.

  Ltac have_incB_m n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n = incB m; [by rewrite (decBK n) | ].

  Ltac have_incB_b n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n == incB m; [by rewrite (decBK n) | ].

  Ltac have_decB_m n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n = decB m; [by rewrite (incBK n) | ].

  Ltac have_decB_b n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n == decB m; [by rewrite (incBK n) | ].

  Inductive bounded_nat (n : nat) : nat -> Set :=
  | BoundedNat : forall m : nat, (m < n) -> bounded_nat n m.

  Lemma bits_bounded : forall (n : nat) (x : BITS n), bounded_nat (2^n) (toNat x).
  Proof.
    move=> n x.
    apply: BoundedNat.
    exact: (toNatBounded x).
  Qed.

  Lemma bits_rect :
    forall (n : nat) (P : BITS n -> Type),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    move=> n P Hbase Hind x.
    move: (bits_bounded x) => Hbounded.
    rewrite -(toNatK x).
    induction Hbounded.
    elim: m i.
    - move=> Hlt.
      rewrite fromNat0.
      exact: Hbase.
    - move=> m IHm Hlt.
      rewrite -incB_fromNat.
      apply: Hind.
      apply: IHm.
      exact: (ltnW Hlt).
  Qed.

  Lemma bits_ind :
    forall (n : nat) (P : BITS n -> Prop),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma bits_rec :
    forall (n : nat) (P : BITS n -> Set),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma behead_tuple_zero : forall n : nat, behead_tuple (zero n.+1) == zero n.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_fromNat0 : forall n : nat, behead_tuple (n:=n.+1) #0 == #0.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_zero : forall n : nat, thead (zero n.+1) == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_fromNat0 : forall n : nat, thead (n:=n.+1) #0 == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_ones : forall n : nat, behead_tuple (ones n.+1) == ones n.
  Proof.
    move=>n.
    apply: eqxx.
  Qed.

  Lemma thead_ones : forall n : nat, thead (ones n.+1) == true.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma bits_ne0_toNat_gt0 :
    forall (n : nat) (x : BITS n), (x != #0) == (0 < toNat x).
  Proof.
    move=> n x.
    rewrite -{1}(toNatK x).
    set m := toNat x.
    have nat_eq0_gt0: forall n : nat, (n == 0) || (n > 0) by move=> i; elim: i.
    case: (orP (nat_eq0_gt0 m)) => {nat_eq0_gt0} Hm.
    - rewrite (eqP Hm) => {x m Hm}.
      rewrite ltnn.
      apply/eqP/negPf/negPf.
      exact: eqxx.
    - rewrite Hm.
      apply/eqP/negP.
      rewrite -fromNatBounded_eq.
      + move=> Heq.
        rewrite (eqP Heq) in Hm.
        done.
      + exact: toNatBounded.
      + rewrite expn_gt0.
        apply/orP; by left.
  Qed.

  Lemma fromNatK w n : n < 2^w -> toNat (@fromNat w n) = n.
  Proof.
    move=> Hn; rewrite toNat_fromNat (modn_small Hn). reflexivity.
  Qed.

  Lemma eta_expand_eq (A B : Type) (x : A * B) : eta_expand x = x.
  Proof.
    destruct x as [a b]; reflexivity.
  Qed.

  Lemma msb_nil : msb nilB = false.
  Proof.
    reflexivity.
  Qed.

  Lemma msb_fromNat_nonnil n m :
    msb (@fromNat (n.+1) m) = odd (m %/ 2^n).
  Proof.
    rewrite -splitmsb_msb splitmsb_fromNat. reflexivity.
  Qed.

  Lemma msb_fromNat n m :
    m < 2^n ->
    msb (@fromNat n m) = odd (m %/ 2^(n.-1)).
  Proof.
    case: n => /=.
    - rewrite /fromNat expn0 divn1 /=. move/ltP=> H.
      rewrite (proj1 (Nat.lt_1_r m) H) /=. reflexivity.
    - move=> n _; exact: msb_fromNat_nonnil.
  Qed.

  Lemma msb_toNat_nonnil n (p : BITS (n.+1)) :
    msb p = odd (toNat p %/ 2^n).
  Proof.
    rewrite -{1}(toNatK p) msb_fromNat_nonnil. reflexivity.
  Qed.

  Lemma msb_toNat n (p : BITS n) :
    msb p = odd (toNat p %/ 2^(n.-1)).
  Proof.
    rewrite -{1}(toNatK p) (msb_fromNat (toNatBounded p)). reflexivity.
  Qed.

  Lemma catB_consB n1 n2 (p1 : BITS n1) b (p2 : BITS n2) :
    catB p1 (consB b p2) = consB b (catB p1 p2).
  Proof.
    rewrite /catB /consB. apply: val_inj => /=. reflexivity.
  Qed.

  Lemma catB_nilBr n (p : BITS n) :
    catB p nilB = p.
  Proof.
    by apply: val_inj.
  Qed.

  Lemma catB_high_low n1 n2 (p : BITS (n2 + n1)) :
    p = catB (high n1 p) (low n2 p).
  Proof.
    exact: (split2eta p).
  Qed.



  (* Operations *)

  Lemma adcBmain_addB n (p1 p2 : BITS n) :
    adcBmain false p1 p2 = joinmsb (carry_addB p1 p2, addB p1 p2).
  Proof.
    rewrite /adcB eta_expand_eq splitmsbK. reflexivity.
  Qed.

  Remark toNat_addn_bounded n (p1 p2 : BITS n) :
    toNat p1 + toNat p2 < 2^n.+1.
  Proof.
    move: (ltn_addn (toNatBounded p1) (toNatBounded p2)).
    rewrite addnn -mul2n -expnS. by apply.
  Qed.

  Lemma high1_msb n (p : BITS (n + 1)%N) : high 1 p = singleBit (msb p).
  Proof.
    rewrite /msb. elim: n p => /=.
    - move=> p. destruct p; apply: val_inj => /=.
      rewrite add0n in i. move/eqP: i => i.
      move: (singleton_seq i) => [b Hb]. rewrite Hb; reflexivity.
    - move=> n IH; case/tupleP => /=. rewrite -/addn.
      move=> b p. rewrite tuple.beheadCons IH. destruct p => /=.
      rewrite (@last_default_irrelevant _ tval _ false b (eqP i)).
      reflexivity.
  Qed.

  Lemma toNat_splitmsb1 n (p : BITS (n.+1)) :
    (splitmsb p).1 = odd (toNat p %/ 2^n).
  Proof.
    rewrite splitmsb_msb. exact: msb_toNat_nonnil.
  Qed.

  Lemma toNat_splitmsb2 n (p : BITS (n.+1)) :
    toNat (splitmsb p).2 = toNat p %% 2^n.
  Proof.
    rewrite -{1}(toNatK p) splitmsb_fromNat /= toNat_fromNat.
    reflexivity.
  Qed.

  Lemma toNat_addB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ carry_addB x y ->
      toNat (addB x y) = (toNat x + toNat y).
  Proof.
    move=> n x y. rewrite /adcB -(toNat_adcBmain false x y)
                  -{3}(splitmsbK (adcBmain false x y)).
    case: (splitmsb (adcBmain false x y)). move=> carry p.
    case: carry => //=. rewrite toNat_joinmsb => _.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_high n (p1 p2 : BITS n) :
    high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    singleBit (carry_addB p1 p2).
  Proof.
    rewrite high1_msb msb_toNat toNat_splitmsb2 toNat_adcBmain
            add0n {3 4}addn1 /= !toNat_zeroExtend
            (modn_small (toNat_addn_bounded p1 p2)).
    rewrite /adcB splitmsb_msb msb_toNat_nonnil toNat_adcBmain add0n.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_high_ext n (p1 p2 : BITS n) :
    (fromNat (carry_addB p1 p2)) =
    zeroExtend (n - 1) (high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2))).
  Proof.
    rewrite addB_zeroExtend1_high.
    apply: toNat_inj. rewrite toNat_zeroExtend.
    case: (carry_addB p1 p2).
    - rewrite fromNatK; first by reflexivity.
      rewrite expnD expn1. apply leq_pmulr. by rewrite expn_gt0.
    - rewrite fromNatK; first by reflexivity.
      by rewrite expn_gt0.
  Qed.

  Lemma addB_zeroExtend1_low n (p1 p2 : BITS n) :
    low n (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    addB p1 p2.
  Proof.
    apply: toNat_inj.
    rewrite toNat_low !toNat_addB !toNat_zeroExtend (addn1 n)
            (modn_small (toNat_addn_bounded p1 p2)).
    reflexivity.
  Qed.

  Lemma carry_subB_ltB :
    forall (n : nat) (x y : BITS n), ~~ carry_subB x y -> (y <= x)%bits.
  Proof.
    move=> n x y. move: (sbbB_ltB_leB x y). case: (sbbB false x y).
    move=> carry p /=. by case: carry.
  Qed.

  Lemma toNat_subB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ carry_subB x y ->
      toNat (subB x y) = (toNat x - toNat y).
  Proof.
    move=> n x y H. apply: toNat_subB. by apply: carry_subB_ltB.
  Qed.

  Lemma Zof_nat_toNat_bounded (n : nat) (p : BITS n) :
    (0 <= Z.of_nat (toNat p) < 2 ^ Z.of_nat n)%Z.
  Proof.
    split.
    - exact: Nat2Z.is_nonneg.
    - replace 2%Z with (Z.of_nat 2%N) by reflexivity.
      rewrite -Nat2Z_inj_pow.
      apply: (proj1 (Nat2Z.inj_lt (toNat p) (Nat.pow 2 n))).
      rewrite -expn_pow. apply/ltP. exact: toNatBounded.
  Qed.



  (* toPosZ *)

  Local Open Scope Z_scope.

  Lemma toPosZCons n b (p : BITS n) :
    toPosZ (consB b p) = Z.b2z b + (toPosZ p) * 2.
  Proof.
    rewrite /toPosZ /= -/(toPosZ p).
    case: b.
    - rewrite Z.double_spec Z.add_comm Z.mul_comm. reflexivity.
    - rewrite /= Z.double_spec Z.mul_comm. reflexivity.
  Qed.

  Lemma toPosZNil (x : BITS 0) : toPosZ x = 0%Z.
  Proof.
    by rewrite (tuple0 x).
  Qed.

  Lemma toPosZ_toNat n (x : BITS n) :
    toPosZ x = Z.of_nat (toNat x).
  Proof.
    elim: n x.
    - move=> x. rewrite toPosZNil toNatNil. reflexivity.
    - move=> n IH; case/tupleP => b x.
      rewrite toPosZCons toNatCons Nat2Z.inj_add -muln2 Nat2Z.inj_mul IH.
      case: b; reflexivity.
  Qed.

  Lemma fromPosZ_fromNat n (m : nat) :
    @fromPosZ n (Z.of_nat m) = @fromNat n m.
  Proof.
    elim: n m.
    - reflexivity.
    - move=> n IH m /=.
      rewrite Z.negb_even /fromNat -/fromNat.
      rewrite -nat_N_Z -N2Z.inj_div2 -Nnat.Nat2N.inj_div2 nat_N_Z IH.
      rewrite nat_N_Z Nat2Z_inj_odd ssrodd_odd ssrdiv2_div2.
      reflexivity.
  Qed.

  Lemma toPosZK n : cancel (@toPosZ n) (@fromPosZ n).
  Proof.
    elim: n.
    - move=> x /=. exact: trivialBits.
    - move=> n IH. case/tupleP => b x.
      rewrite toPosZCons /fromPosZ -/fromPosZ /= Zhalf_bit_double.
      rewrite IH Z.negb_even Z.mul_comm Z.odd_add_mul_2. by case b.
  Qed.

  Definition toPosZ_inj n := can_inj (@toPosZK n).

  Lemma toPosZ_min n (x : BITS n) : 0 <= toPosZ x.
  Proof.
    destruct x as [x Hsize].
    rewrite /toPosZ => {Hsize n} /=.
    elim: x => /=.
    - done.
    - move=> b x.
      set n := (seq.foldr
                  (fun (b : bool) (z : Z) =>
                     if b then Z.succ (Z.double z) else Z.double z) (0%Z) x).
      move=> Hind /=.
      move: (Zdouble_positive Hind) => H.
      case Hb: b.
      + apply: (Zle_trans _ _ _ Hind).
        apply: (Zle_trans _ _ _ H).
        exact: Zle_succ.
      + exact: (Zle_trans _ _ _ Hind H).
  Qed.

  Lemma toPosZ_max n : forall (x : BITS n), toPosZ x < two_power_nat n.
  Proof.
    elim: n.
    - move=> x.
      rewrite toPosZNil.
      exact: zero_lt_two_power_nat.
    - move=> n IHn.
      case/tupleP => [b x].
      case Hb: b; rewrite /toPosZ /=; fold (toPosZ x).
      + rewrite /Z.succ Z.double_spec two_power_nat_S.
        apply: ltn_Sdouble.
        exact: IHn.
      + rewrite Z.double_spec two_power_nat_S.
        apply: (Zmult_gt_0_lt_compat_l _ _ _ _ (IHn x)).
        done.
  Qed.

  Definition toPosZBounded := toPosZ_max.

  Lemma toPosZ_fromPosZBounded_nat n m :
    (m < 2^n)%N ->
    toPosZ (fromPosZ (n:=n) (Z.of_nat m)) = (Z.of_nat m).
  Proof.
    rewrite toPosZ_toNat fromPosZ_fromNat => H.
    apply: (proj2 (Nat2Z.inj_iff (toNat (@fromNat n m)) m)).
    exact: toNat_fromNatBounded.
  Qed.

  Lemma toPosZ_fromPosZBounded n m :
    (0 <= m < Zpower_nat 2 n)%Z ->
    toPosZ (fromPosZ (n:=n) m) = m.
  Proof.
    move=> [H1 H2]. rewrite -{1}(Z2Nat.id m H1) toPosZ_fromPosZBounded_nat.
    - rewrite (Z2Nat.id m H1). reflexivity.
    - apply: lt_ltn. apply: (proj2 (Nat2Z.inj_lt (Z.to_nat m) (2^n)%N)).
      rewrite (Z2Nat.id _ H1). rewrite expn_pow Nat2Z_inj_pow /= -Zpower_nat_Z.
      exact: H2.
  Qed.

  Lemma toPosZ_zero n : toPosZ (zero n) = 0%Z.
  Proof.
    rewrite /toPosZ. elim: n => /=.
    - reflexivity.
    - move=> n Hind. rewrite Hind Z.double_spec. reflexivity.
  Qed.

  Lemma fromPosZBounded_eq m1 m2 n :
    (m1 < 2^n)%N -> (m2 < 2^n)%N ->
    (m1 == m2) = (@fromPosZ n (Z.of_nat m1) == @fromPosZ n (Z.of_nat m2)).
  Proof.
    move=> H1 H2. rewrite !fromPosZ_fromNat. exact: fromNatBounded_eq.
  Qed.

  Lemma fromPosZHalf n m :
    cons_tuple (odd m) (@fromPosZ n (Z.of_nat (m./2))) = fromPosZ (Z.of_nat m).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNatHalf.
  Qed.

  Lemma fromPosZ_wrap n m :
    @fromPosZ n (Z.of_nat m) = @fromPosZ n (Z.of_nat (m + 2^n)).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNat_wrap.
  Qed.

  Lemma fromPosZ_wrapMany (n c m : nat) :
    @fromPosZ n (Z.of_nat m) = @fromPosZ n (Z.of_nat (m + c * 2^n)).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNat_wrapMany.
  Qed.

  Lemma toPosZ_joinlsb n (p : BITS n) b :
    toPosZ (joinlsb (p, b)) = (Z.b2z b + (toPosZ p) * 2)%Z.
  Proof.
    exact: toPosZCons.
  Qed.

  Lemma toPosZ_zeroExtend extra n (p : BITS n) :
    toPosZ (zeroExtend extra p) = toPosZ p.
  Proof.
    rewrite !toPosZ_toNat toNat_zeroExtend; reflexivity.
  Qed.

  Local Close Scope Z_scope.

End BitsLemmas.



(** Ordering *)

Module BitsOrder <: OrderedType.

  Variable n : nat.

  Definition t := BITS n.

  Definition eq : t -> t -> Prop := fun x y : t => x == y.

  Definition lt : t -> t -> Prop := fun x y : t => ltB x y.

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
    exact: ltB_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt.
    move/eqP => Heq.
    apply/idP: Hlt.
    by rewrite Heq ltBnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    apply: bits_rec.
    - move=> y.
      case Hy0: (y == #0).
      + move/eqP: Hy0 => Hy0; rewrite Hy0.
        rewrite fromNat0.
        apply: EQ.
        exact: eq_refl.
      + apply: LT.
        rewrite /lt ltB_nat.
        rewrite toNat_zero.
        rewrite -(eqP (bits_ne0_toNat_gt0 y)).
        apply/negP.
        by rewrite Hy0.
    - move=> x Hind y.
      move: (toNat_incB x).
      case Hx: (x == ones n) => /= Hincx.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: EQ.
          rewrite /eq (eqP Hx) (eqP Hy) incB_ones fromNat0.
          exact: eqxx.
        * apply: LT.
          rewrite /lt ltB_nat Hincx.
          rewrite -(eqP (bits_ne0_toNat_gt0 y)).
          apply/negPf.
          exact: Hy.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: GT.
          rewrite /lt ltB_nat Hincx (eqP Hy) toNat_fromNat0.
          done.
        * move: (Hind (decB y)) => {Hind} Hind.
          case: Hind => Hcomp.
          -- apply: LT.
             rewrite /lt (ltB_nat x (decB y)) Hdecy in Hcomp.
             rewrite /lt (ltB_nat (incB x) y) Hincx.
             by rewrite -(eqP (lt_sub1r_add1l (toNat x) (toNat y))).
          -- apply: EQ.
             rewrite /eq in Hcomp *.
             rewrite (eqP Hcomp).
             by rewrite (decBK y).
          -- apply: GT.
             rewrite /lt ltB_nat Hdecy in Hcomp.
             rewrite /lt ltB_nat Hincx.
             rewrite -(ltn_add2r 1 ((toNat y).-1) (toNat x)) in Hcomp.
             have: (0 < toNat y).
             ++ rewrite -(eqP (bits_ne0_toNat_gt0 y)).
                apply/negP.
                by rewrite Hy.
             ++ move=> H0y.
                rewrite addn1 addn1 in Hcomp.
                rewrite (prednK H0y) in Hcomp.
                done.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    move=> x y.
    apply: eq_comparable.
  Qed.

End BitsOrder.



(** Overflows *)

Section BitsOverflow.

  Lemma leB_addB_ovf :
    forall (n : nat) (x y a b : BITS n),
      (a <= x)%bits -> (b <= y)%bits -> ~~ carry_addB x y -> ~~ carry_addB a b.
  Proof.
  Abort.

  (* Test if x * y will overflow. *)
  Definition mulB_ovf (n : nat) (x y : BITS n) : bool :=
    high n (fullmulB x y) != #0.

  Definition toNat_mulB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ mulB_ovf x y ->
      toNat (mulB x y) == (toNat x) * (toNat y).
  Proof.
    move=> n x y.
    rewrite /mulB_ovf /mulB => Hh.
    move: (toNat_fullmulB x y).
    move/negPn/eqP: Hh.
    rewrite toNat_low.
    rewrite {2 3}(split2eta (fullmulB x y)).
    set h := high n (fullmulB x y).
    set l := low n (fullmulB x y).
    rewrite toNatCat => Hh.
    rewrite Hh toNat_fromNat0 mul0n add0n.
    move=> Hxy; rewrite -Hxy.
    move: (toNatBounded l) => Hbounded.
    rewrite (modn_small Hbounded).
    exact: eqxx.
  Qed.

End BitsOverflow.



(** Intervals *)

Section BitsInterval.

  Local Open Scope bits_scope.

  Definition min (n : nat) (x y : BITS n) :=
    if x < y then x else y.

  Definition max (n : nat) (x y : BITS n) :=
    if x < y then y else x.

  Inductive intv_op : Set :=
  | LT
  | LE.

  Definition eval_intv_op (op : intv_op) (n : nat) : BITS n -> BITS n -> bool :=
    match op with
    | LT => ltB (n := n)
    | LE => leB (n := n)
    end.

  Definition interval (n : nat) (a : BITS n) (op1 : intv_op) (x : BITS n) (op2 : intv_op) (b : BITS n) : bool :=
    eval_intv_op op1 a x && eval_intv_op op2 x b.

  Notation "x ∈ [ a , b ]" := (interval a LE x LE b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b ]" := (interval a LT x LE b) (at level 20) : bits_scope.
  Notation "x ∈ [ a , b )" := (interval a LE x LT b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b )" := (interval a LT x LT b) (at level 20) : bits_scope.

  Ltac case_intv H :=
    move: H; rewrite /interval /eval_intv_op => H; caseP H.

  Definition intv_op_join (op1 op2 : intv_op) :=
    match op1, op2 with
    | LE, LE => LE
    | LT, LE
    | LE, LT
    | LT, LT => LT
    end.

  Lemma intv_addB (n : nat) (a : BITS n) op1 x op2 b c op3 y op4 d :
    interval a op1 x op2 b -> interval c op3 y op4 d ->
    ~~ carry_addB a b -> ~~ carry_addB b d ->
    interval (a + c) (intv_op_join op1 op3) (x + y) (intv_op_join op2 op4) (b + d).
  Proof.
  Abort.

End BitsInterval.


Global Transparent adcB sbbB.
Ltac bvsimpl :=
  lazy beta iota zeta delta -[
    adcB adcBmain sbbB fullmulB mulB ltB leB
         rorB rolB shrB shrBn shlB shlBn
         zeroExtend signExtend high low
         fromNat toNat fromPosZ toPosZ fromZ toZ
  ].
Ltac bvzsimpl :=
  lazy beta iota zeta delta -[
    Zmult Zplus Zpower Z.pow_pos Zpower_nat Zminus Zopp Zdiv Zmod
          adcB adcBmain sbbB fullmulB mulB ltB leB
          rorB rolB shrB shrBn shlB shlBn
          zeroExtend signExtend high low
          fromNat toNat fromPosZ toPosZ fromZ toZ
  ].
Global Opaque adcB sbbB.

(* Don't simplify fullmulB. Otherwise, Coq freezes. *)
Global Opaque low high fullmulB mulB ltB leB shlBn shrBn.
