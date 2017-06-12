

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

  Lemma toNatBounded_leq n (p : BITS n) :
    toNat p <= 2^n - 1.
  Proof.
    move: (toNatBounded p). exact: ltn_leq_sub.
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

  Lemma singleBit_fromNat (b : bool) :
    singleBit b = fromNat b.
  Proof.
    rewrite /fromNat /singleBit. rewrite oddb. reflexivity.
  Qed.

  Lemma catB_eucl n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat p1) /\ r = Z.of_nat (toNat p2).
  Proof.
    rewrite toNatCat Nat2Z.inj_add Nat2Z.inj_mul expn_pow Nat2Z_inj_pow /=.
    move=> H. split.
    - rewrite (Zdiv_eucl_q H).
      rewrite (Z_div_plus_full_l _ _ _ (@two_power_of_nat_ne0 n2)).
      rewrite (Z.div_small _ _ (Zof_nat_toNat_bounded p2)).
      rewrite Z.add_0_r. reflexivity.
    - rewrite (Zdiv_eucl_r H).
      rewrite Z.add_comm Z_mod_plus_full
              (Z.mod_small _ _ (Zof_nat_toNat_bounded p2)).
      reflexivity.
  Qed.

  Lemma catB_eucl_high n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat p1).
  Proof.
    move=> H. exact: (proj1 (catB_eucl H)).
  Qed.

  Lemma catB_eucl_low n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    r = Z.of_nat (toNat p2).
  Proof.
    move=> H. exact: (proj2 (catB_eucl H)).
  Qed.

  Lemma toNat_eucl n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat (high n1 p)) /\ r = Z.of_nat (toNat (low n2 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl.
  Qed.

  Lemma toNat_eucl_high n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat (high n1 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl_high.
  Qed.

  Lemma toNat_eucl_low n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    r = Z.of_nat (toNat (low n2 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl_low.
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

  Lemma zeroExtend_catB n1 n2 (p : BITS n1) :
    zeroExtend n2 p = (zero n2) ## p.
  Proof.
    apply: toNat_inj. rewrite toNat_zeroExtend. reflexivity.
  Qed.

  Lemma low_zeroExtend n1 n2 (p : BITS n1) :
    low n1 (zeroExtend n2 p) = p.
  Proof.
    apply: toNat_inj. rewrite toNat_low toNat_zeroExtend -toNat_mod.
    reflexivity.
  Qed.

  Lemma high_zeroExtend n1 n2 (p : BITS n1) :
    high n2 (zeroExtend n2 p) = zero n2.
  Proof.
    rewrite zeroExtend_catB high_catB. reflexivity.
  Qed.

  Lemma toNat_high n1 n2 (p : BITS (n1 + n2)) :
    toNat (high n2 p) = (toNat p) %/ (2 ^ n1).
  Proof.
    have: (toNat p = toNat (high n2 p ## low n1 p)) by
        rewrite -(catB_high_low p). rewrite toNatCat => H.
    have: (toNat p) %/ (2 ^ n1) =
          (toNat (high n2 p) * 2 ^ n1 + toNat (low n1 p)) %/ (2 ^ n1)
      by rewrite -H. rewrite (divnMDl _ _ (expn2_gt0 n1)).
    rewrite (@divn_small (toNat (low n1 p))).
    - rewrite addn0 => ->; reflexivity.
    - exact: toNatBounded.
  Qed.



  (* Operations *)

  Lemma carry_addB_nil (p1 p2 : BITS 0) :
    carry_addB p1 p2 = false.
  Proof.
    reflexivity.
  Qed.

  Lemma carry_addB_bounded n (p1 p2 : BITS n) :
    carry_addB p1 p2 < 2^n.
  Proof.
    case: n p1 p2.
    - done.
    - move=> n p1 p2.
      case: (carry_addB p1 p2) => /=.
      + exact: ltn_1_2expnS.
      + by rewrite expn_gt0.
  Qed.

  Lemma carry_addB_toNatn_toNat1 n (p1 p2 : BITS n) :
    @toNat n # (carry_addB p1 p2) = @toNat 1 # (carry_addB p1 p2).
  Proof.
    case: n p1 p2.
    - move=> p1 p2. reflexivity.
    - move=> n p1 p2.
      case: (carry_addB p1 p2) => /=.
      + rewrite fromNatK; first by reflexivity. exact: ltn_1_2expnS.
      + rewrite fromNatK; first by reflexivity. by rewrite expn_gt0.
  Qed.

  Lemma adcBmain_addB n (p1 p2 : BITS n) :
    adcBmain false p1 p2 = joinmsb (carry_addB p1 p2, addB p1 p2).
  Proof.
    rewrite /adcB eta_expand_eq splitmsbK. reflexivity.
  Qed.

  Lemma toNat_addn_bounded n (p1 p2 : BITS n) :
    toNat p1 + toNat p2 < 2^n.+1.
  Proof.
    move: (ltn_addn (toNatBounded p1) (toNatBounded p2)).
    rewrite addnn -mul2n -expnS. by apply.
  Qed.

  Lemma toNat_addn_ltn_two_power n (p1 p2 : BITS n.+1) :
    toNat p1 + toNat p2 < 2 ^ (n.+1 + n.+1).
  Proof.
    apply: (ltn_leq_trans (toNat_addn_bounded p1 p2)).
    rewrite (@leq_exp2l 2 _ _ is_true_true).
    rewrite -{1}(add0n (n.+1)) ltn_add2r. done.
  Qed.

  Lemma carry_addB_odd n (p1 p2 : BITS n) :
    nat_of_bool (carry_addB p1 p2) = odd ((toNat p1 + toNat p2) %/ 2^n).
  Proof.
    rewrite /adcB toNat_splitmsb1 toNat_adcBmain add0n.
    reflexivity.
  Qed.

  Lemma carry_addB_divn n (p1 p2 : BITS n) :
    nat_of_bool (carry_addB p1 p2) = (toNat p1 + toNat p2) %/ 2^n.
  Proof.
    rewrite carry_addB_odd odd_divn; first reflexivity.
    rewrite -mul2n -expnS. exact: toNat_addn_bounded.
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

  Lemma toNat_addB_zeroExtend1 n (p1 p2 : BITS n) :
    toNat (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) = toNat p1 + toNat p2.
  Proof.
    rewrite toNat_addB !toNat_zeroExtend modn_small.
    - reflexivity.
    - rewrite addn1. exact: (toNat_addn_bounded p1 p2).
  Qed.

  Lemma toNat_addB_zeroExtend n (p1 p2 : BITS n) :
    toNat (addB (zeroExtend n p1) (zeroExtend n p2)) = toNat p1 + toNat p2.
  Proof.
    case: n p1 p2.
    - move=> p1 p2. rewrite toNat_addB !toNat_zeroExtend modn_small;
      first reflexivity. rewrite !toNatNil. done.
    - move=> n p1 p2. rewrite toNat_addB !toNat_zeroExtend modn_small;
                        first reflexivity. exact: toNat_addn_ltn_two_power.
  Qed.

  Lemma low_addB_distr n1 n2 (p1 p2 : BITS (n1 + n2)) :
    low n1 (addB p1 p2) = addB (low n1 p1) (low n1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_low toNat_addB expnD modn_muln_modn_l.
    rewrite toNat_addB 2!toNat_low modnDm. reflexivity.
  Qed.

  Lemma addB_zeroExtend1_catB n (p1 p2 : BITS n) :
    addB (zeroExtend 1 p1) (zeroExtend 1 p2) =
    (fromNat (carry_addB p1 p2)) ## (addB p1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_addB_zeroExtend1.
    rewrite toNatCat. have Hc: carry_addB p1 p2 < 2 ^ 1.
    { by case: (carry_addB p1 p2). }
    rewrite (fromNatK Hc) => {Hc}. rewrite /adcB adcBmain_nat /= add0n.
    rewrite splitmsb_fromNat /=. rewrite toNat_fromNat.
    apply: odd_divn_eucl. rewrite -mul2n -expnS.
    exact: toNat_addn_bounded.
  Qed.

  Lemma addB_zeroExtend_catB n (p1 p2 : BITS n) :
    addB (zeroExtend n p1) (zeroExtend n p2) =
    (fromNat (carry_addB p1 p2)) ## (addB p1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_addB_zeroExtend.
    rewrite toNatCat. have Hc: carry_addB p1 p2 < 2 ^ n.
    { case: n p1 p2.
      - done.
      - move=> n p1 p2. apply: (@leq_ltn_trans 1).
        + by case: (carry_addB p1 p2).
        + exact: ltn_1_2expnS. }
    rewrite (fromNatK Hc) => {Hc}. rewrite /adcB adcBmain_nat /= add0n.
    rewrite splitmsb_fromNat /=. rewrite toNat_fromNat.
    apply: odd_divn_eucl. rewrite -mul2n -expnS.
    exact: toNat_addn_bounded.
  Qed.

  Lemma addB_zeroExtend1_high n (p1 p2 : BITS n) :
    high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    singleBit (carry_addB p1 p2).
  Proof.
    rewrite addB_zeroExtend1_catB high_catB /=. rewrite singleBit_fromNat.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_high_ext n (p1 p2 : BITS n) :
    zeroExtend (n - 1) (high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2))) =
    (fromNat (carry_addB p1 p2)).
  Proof.
    rewrite addB_zeroExtend1_high.
    apply: toNat_inj. rewrite toNat_zeroExtend.
    case: (carry_addB p1 p2).
    - rewrite fromNatK; first by reflexivity.
      exact: ltn_1_2expnS.
    - rewrite fromNatK; first by reflexivity.
      by rewrite expn_gt0.
  Qed.

  Lemma addB_zeroExtend_high n (p1 p2 : BITS n) :
    high n (addB (zeroExtend n p1) (zeroExtend n p2)) =
    fromNat (carry_addB p1 p2).
  Proof.
    rewrite addB_zeroExtend_catB high_catB.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_low n (p1 p2 : BITS n) :
    low n (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    addB p1 p2.
  Proof.
    rewrite addB_zeroExtend1_catB low_catB. reflexivity.
  Qed.

  Lemma addB_zeroExtend_low n (p1 p2 : BITS n) :
    low n (addB (zeroExtend n p1) (zeroExtend n p2)) =
    addB p1 p2.
  Proof.
    rewrite addB_zeroExtend_catB low_catB. reflexivity.
  Qed.

  Lemma addB3_zeroExtend_low n (p1 p2 p3 : BITS n) :
    low n (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3)) =
    addB (addB p1 p2) p3.
  Proof.
    rewrite 2!low_addB_distr. rewrite 3!low_zeroExtend. reflexivity.
  Qed.

  Lemma toNat_addB_zeroExtend_bounded n (p1 p2 : BITS n) :
    high n (addB (zeroExtend n p1) (zeroExtend n p2)) = zero n ->
    toNat (low n (addB (zeroExtend n p1) (zeroExtend n p2))) =
    toNat p1 + toNat p2.
  Proof.
    rewrite addB_zeroExtend_low. case: n p1 p2.
    - move=> p1 p2 Hc. rewrite !toNatNil. reflexivity.
    - move=> n p1 p2. rewrite addB_zeroExtend_high.
      case Hc: (carry_addB p1 p2) => /=.
      + move=> H0; have: toNat (@fromNat n.+1 1) = toNat (zero n.+1)
                 by rewrite H0. rewrite fromNatK.
        * rewrite toNat_zero. discriminate.
        * done.
      + move=> _. move/negP/idP: Hc => Hc. exact: (toNat_addB_bounded Hc).
  Qed.

  Lemma toNat_addB3_zeroExtend_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 ->
    ~~ carry_addB (addB p1 p2) p3 ->
    toNat (low n (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3))) = toNat p1 + toNat p2 + toNat p3.
  Proof.
    move=> H1 H2. rewrite addB3_zeroExtend_low. rewrite (toNat_addB_bounded H2).
    rewrite (toNat_addB_bounded H1). reflexivity.
  Qed.

  Lemma toNat_addn3_bounded_lt (n : nat) :
    3 * (2^n - 1) < 4^n.
  Proof.
    elim: n.
    - done.
    - move=> n IH. rewrite !expnS.
      have: 3 * (2 * 2 ^ n - 1) = 2 * 3 * (2^n - 1) + 3.
      { rewrite 2!mulnBr. change (3 * 1) with 3. rewrite mulnA.
        change (3 * 2) with 6. change (2 * 3) with 6. change (6 * 1) with 6.
        rewrite addnC addnBA.
        - rewrite addnC -subnBA; last by done. change (6 - 3) with 3.
          reflexivity.
        - rewrite -{1}(muln1 5). apply: ltn_leq_mul_ltn.
          + done.
          + done.
          + rewrite expn_gt0. done. }
      move=> ->. move: (ltn_leq_sub IH) => {IH} H.
      move: (leq_mul2l 2 (3 * (2^n - 1)) (4^n - 1)). rewrite H /= => {H} H.
      rewrite -(leq_add2r 3) mulnA in H. apply: (leq_ltn_trans H).
      rewrite mulnBr. change (2 * 1) with 2.
      have H1: 1 < 2 * 4 ^ n.
      { rewrite -{1}(muln1 1). apply: ltn_leq_mul_ltn.
        - done.
        - done.
        - rewrite expn_gt0. done. }
      rewrite addnC (addnBA _ H1) => {H1}. have H1: 1 < 3 by done.
      rewrite -addnC -(addnBA _ H1) => {H1}. change (3 - 2) with 1.
      change 4 with (2 + 2) at 2. rewrite mulnDl ltn_add2l.
      change 1 with (1 * 1) at 1. apply: ltn_leq_mul_ltn.
      + done.
      + done.
      + rewrite expn_gt0. done.
  Qed.

  Lemma toNat_addn3_ltn_two_power n (p1 p2 p3 : BITS n.+1) :
    toNat p1 + toNat p2 + toNat p3 < 2 ^ (n.+1 + n.+1).
  Proof.
    rewrite addnn -mul2n expnM.
    change (2^2) with 4.
    apply: (leq_ltn_trans _ (toNat_addn3_bounded_lt (n.+1))).
    move: (leq_add (leq_add (toNatBounded_leq p1) (toNatBounded_leq p2)) (toNatBounded_leq p3)).
    have Hlt: 0 < 2 ^ n.+1 by rewrite expn_gt0.
    rewrite 2!(addnBA _ Hlt) (addnC (2^n.+1 - 1) (2^n.+1)) (addnBA _ Hlt).
    rewrite addnn -mul2n -subnDA (addnC _ (2^n.+1)).
    have Hle: 1 + 1 <= 2 * 2 ^ n.+1.
    { change (1+1) with 2. apply: (leq_ltn_trans Hlt).
      rewrite -{1}(mul1n (2^n.+1)) ltn_mul2r Hlt. done. }
    rewrite (addnBA _ Hle) -subnDA -{1}(mul1n (2^n.+1)) -mulnDl.
    change (1+2) with 3. change (1+1+1) with 3. rewrite -{2}(muln1 3) -mulnBr.
    done.
  Qed.

  Lemma toNat_addB3_zeroExtend n (p1 p2 p3 : BITS n) :
    toNat (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3)) =
    toNat p1 + toNat p2 + toNat p3.
  Proof.
    case: n p1 p2 p3.
    - move=> p1 p2 p3. rewrite !toNat_addB !toNat_zeroExtend !modn_small;
                         first reflexivity; by rewrite !toNatNil.
    - move=> n p1 p2 p3. rewrite !toNat_addB !toNat_zeroExtend !modn_small;
                           first reflexivity.
      * exact: toNat_addn_ltn_two_power.
      * exact: toNat_addn3_ltn_two_power.
      * exact: toNat_addn_ltn_two_power.
  Qed.

  Lemma carry_subB_leB :
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
    move=> n x y H. apply: toNat_subB. by apply: carry_subB_leB.
  Qed.

  Lemma toNat_high_addB_extn_ext1 n (p1 p2 : BITS n) :
    toNat (high n (addB (zeroExtend n p1) (zeroExtend n p2))) =
    toNat (high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2))).
  Proof.
    rewrite addB_zeroExtend_catB addB_zeroExtend1_catB !high_catB.
    exact: carry_addB_toNatn_toNat1.
  Qed.

  Lemma toNat_mulB_zeroExtend n (p1 p2 : BITS n) :
    toNat (mulB (zeroExtend n p1) (zeroExtend n p2)) = toNat p1 * toNat p2.
  Proof.
    rewrite toNat_mulB !toNat_zeroExtend modn_small.
    - reflexivity.
    - rewrite expnD. apply: ltn_mul; exact: toNatBounded.
  Qed.

  Lemma mulB_zeroExtend_fullmulB n (p1 p2 : BITS n) :
    mulB (zeroExtend n p1) (zeroExtend n p2) = fullmulB p1 p2.
  Proof.
    apply: toNat_inj. rewrite toNat_mulB_zeroExtend toNat_fullmulB.
    reflexivity.
  Qed.

  Lemma mulB_zeroExtend_low n (p1 p2 : BITS n) :
    low n (mulB (zeroExtend n p1) (zeroExtend n p2)) = mulB p1 p2.
  Proof.
    rewrite mulB_zeroExtend_fullmulB. reflexivity.
  Qed.

  Lemma toNat_mulB_bounded n (p1 p2 : BITS n) :
    high n (fullmulB p1 p2) = zero n ->
    toNat (mulB p1 p2) = (toNat p1 * toNat p2).
  Proof.
    rewrite -mulB_zeroExtend_fullmulB => H.
    move: (toNatCat (high n (zeroExtend n p1 * zeroExtend n p2))
                    (low n (zeroExtend n p1 * zeroExtend n p2))).
    rewrite -(catB_high_low (zeroExtend n p1 * zeroExtend n p2)) H.
    rewrite toNat_mulB_zeroExtend toNat_zero mul0n add0n. move=> ->.
    rewrite mulB_zeroExtend_low. reflexivity.
  Qed.

  Lemma shlBn_mulB n i (p : BITS n) :
    shlBn p i = mulB p (fromNat (2^i)).
  Proof.
    elim: i n p => /=.
    - move=> n p. rewrite expn0. rewrite mulB1. reflexivity.
    - move=> i IH n p. rewrite shlB_asMul IH. rewrite -mulB_muln.
      rewrite -expnSr. reflexivity.
  Qed.

  Lemma toNat_shlB_bounded n (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - 1))%bits ->
    toNat (shlB p) = (toNat p * 2).
  Proof.
    case: n p.
    - done.
    - move=> n p. have H: n.+1 - 1 < n.+1.
      { rewrite subn1 succn_predn. done. }
      rewrite ltB_nat toNat_shlB (toNat_shlBn H). rewrite subn1 succn_predn.
      rewrite -muln2. move=> {H} H. rewrite modn_small; first by reflexivity.
      rewrite expnSr. apply: ltn_leq_mul_ltn; done.
  Qed.

  Lemma ltn_expn_subn_ltn i n : 0 < i < n -> 2 ^ (n - i) < 2 ^ n.
  Proof.
    move=> /andP [H0i Hin]. rewrite ltn_exp2l; last by done. rewrite -subn_gt0.
    rewrite (subKn (ltnW Hin)). assumption.
  Qed.

  Lemma shlBn0 n (p : BITS n) : shlBn p 0 = p.
  Proof.
    reflexivity.
  Qed.

  Lemma toNat_shlBn_bounded n i (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - i))%bits ->
    toNat (shlBn p i) = (toNat p * 2 ^ i).
  Proof.
    rewrite !shlBn_mulB. rewrite fromNat_mulBn mul1n.
    case Hi0: (i == 0).
    - rewrite (eqP Hi0) subn0 expn0 muln1 mulB1. reflexivity.
    - move/negP/idP: Hi0 => Hi0. case Hin: (i < n).
      + have Hlt1: 2 ^ (n - i) < 2 ^ n.
        { apply: ltn_expn_subn_ltn. rewrite Hin lt0n Hi0. done. }
        rewrite ltB_nat (fromNatK Hlt1) => Hp.
        have Hlt2: 2^i < 2^n.
        { by rewrite ltn_exp2l. }
        rewrite toNat_mulB (fromNatK Hlt2).
        rewrite modn_small; first by reflexivity.
        move: Hp => {Hlt1 Hlt2}. set m := toNat p. move: m => {p} m Hm.
        rewrite -(subnK (ltnW Hin)) expnD.
        apply: (ltn_leq_mul_ltn _ Hm (leqnn (2^i))).
        by rewrite expn_gt0.
      + move/negP/idP: Hin. rewrite -leqNgt => Hni.
        rewrite (eqP Hni) expn0 ltB_nat.
        case: n p Hni.
        * move=> p _ _. rewrite !toNatNil. reflexivity.
        * move=> n p Hni. move: (expn2_gt1 n) => H.
          rewrite (fromNatK H) toNat_mulB => Hlt.
          move: (ltn_leq_sub Hlt). change (1-1) with 0. rewrite leqn0.
          move=> Hp; rewrite (eqP Hp).
          rewrite !mul0n modn_small; first reflexivity. exact: expn2_gt0.
  Qed.

  Lemma toNat_shrBn n i (p : BITS n) :
    toNat (shrBn p i) = (toNat p) %/ (2^i).
  Proof.
    elim: i n p => /=.
    - move=> n p. rewrite expn0 divn1. reflexivity.
    - move=> i IH n p. rewrite toNat_shrB IH -divn2 -divnMA expnSr.
      reflexivity.
  Qed.

  Lemma toNat_shlBn_shrBn n i (p : BITS n) :
    toNat (shrBn (shlBn p (n - i)) (n - i)) = (toNat p) %% (2^i).
  Proof.
    rewrite toNat_shrBn. rewrite shlBn_mulB toNat_mulB.
    case Hi0: (i == 0).
    - rewrite (eqP Hi0) subn0 expn0 modn1. rewrite divn_small; first reflexivity.
      rewrite ltn_mod expn_gt0. done.
    - move/negP/idP: Hi0=> Hi0. case Hin: (i < n).
      + have Hlt1: 2 ^ (n - i) < 2 ^ n.
        { apply: ltn_expn_subn_ltn. rewrite Hin lt0n Hi0. done. }
        rewrite (fromNatK Hlt1) mulnC. set m := toNat p.
        move: m Hi0 Hin Hlt1 => {p} m Hi0 Hin Hlt1.
        rewrite -{2}(subnK (ltnW Hin)). rewrite expnD.
        move: (expn2_gt0 (n - i)) => Hlt2.
        rewrite -(muln_modr Hlt2). rewrite (mulKn _ Hlt2). reflexivity.
      + move/negP/idP: Hin. rewrite -leqNgt => Hni.
        rewrite (eqP Hni) expn0 divn1.
        case: n p Hni.
        * move=> p _. rewrite toNatNil mul0n !mod0n. reflexivity.
        * move=> n p Hni. move: (expn2_gt1 n) => H.
          rewrite (fromNatK H) muln1. rewrite !modn_small; first reflexivity.
          -- apply: (ltn_leq_trans (toNatBounded p)).
             rewrite (leq_exp2l); last done. exact: Hni.
          -- exact: toNatBounded.
  Qed.

  Lemma catB_shlBn_bounded n i (p1 p2 : BITS n) :
    i <= n ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (p1 ## p2 < shlBn # (1) (n + n - i))%bits.
  Proof.
    move=> Hin. rewrite 2!ltB_nat toNatCat. case Hi0: (i == 0).
    - rewrite (eqP Hi0) 2!subn0 2!shlBn_overflow. rewrite fromNatK; first done.
      rewrite expn_gt0; done.
    - move/negP/idP: Hi0 => Hi0. rewrite -lt0n in Hi0.
      have H1: n - i < n.
      { rewrite -{2}(subn0 n). apply: (ltn_sub2l _ Hi0).
        exact: (ltn_leq_trans Hi0 Hin). }
      have H2: n + n - i < n + n.
      { rewrite -{2}(subn0 (n + n)). apply: (ltn_sub2l _ Hi0).
        apply: ltn_addr. exact: (ltn_leq_trans Hi0 Hin). }
      rewrite (toNat_shlBn H1) (toNat_shlBn H2). move=> H.
      move: (ltn_leq_sub H) => {H} H.
      move: (leq_mul2r (2^n) (toNat p1) (2^(n-i)-1)).
      rewrite H orbT => {H} H. move: (leq_add H (toNatBounded_leq p2)).
      rewrite mulnBl mul1n.
      have H3: 2 ^ n <= 2 ^ (n - i) * 2 ^ n.
      { apply: leq_pmull. exact: expn2_gt0. }
      rewrite (addnC _ (2^n - 1)) (addnBA _ H3).
      rewrite (addnC (2^n - 1)) -(subnBA _ (leq_subr 1 (2^n))).
      rewrite (subKn (expn2_gt0 n)) -expnD (addnC (n - i)) (addnBA _ Hin).
      move=> {Hi0 Hin H1 H2 H H3} H; apply: (leq_ltn_trans H).
      rewrite -{2}(subn0 (2^(n + n - i))). apply: ltn_sub2l; last done.
      exact: expn2_gt0.
  Qed.

  Lemma toNat_catB_shlBn n i (p1 p2 : BITS n) :
    i <= n ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    toNat (shlBn (p1 ## p2) i) = (toNat p1 * (2 ^ n) + toNat p2) * (2 ^ i).
  Proof.
    move=> Hin Hp1. rewrite toNat_shlBn_bounded.
    - rewrite toNatCat. reflexivity.
    - exact: catB_shlBn_bounded.
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

  Lemma toPosZ_max n : forall (x : BITS n), toPosZ x < 2 ^ Z.of_nat n.
  Proof.
    rewrite -two_power_nat_equiv. elim: n.
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

  Lemma toPosZ_low n1 n2 (p : BITS (n1 + n2)) :
    toPosZ (low n1 p) = (toPosZ p) mod (2 ^ Z.of_nat n1).
  Proof.
    rewrite toPosZ_toNat toNat_low. have H: (2 ^ n1)%N != 0%N.
    { rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Nat2Z_inj_modn _ H). rewrite expn_pow Nat2Z_inj_pow.
    rewrite -toPosZ_toNat. reflexivity.
  Qed.

  Lemma toPosZ_high n1 n2 (p : BITS (n1 + n2)) :
    toPosZ (high n2 p) = (toPosZ p) / (2 ^ Z.of_nat n1).
  Proof.
    rewrite toPosZ_toNat toNat_high.
    rewrite Nat2Z_inj_divn. rewrite expn_pow Nat2Z_inj_pow.
    rewrite -toPosZ_toNat. reflexivity.
  Qed.



  (* toPosZ and operations *)

  Lemma toPosZ_addB_bounded n (p1 p2 : BITS n) :
    ~~ carry_addB p1 p2 ->
    toPosZ (p1 + p2) = toPosZ p1 + toPosZ p2.
  Proof.
    move=> Hc.
    rewrite {1}toPosZ_toNat (toNat_addB_bounded Hc).
    rewrite Nat2Z.inj_add -!toPosZ_toNat. reflexivity.
  Qed.

  Lemma toPosZ_addB_zeroExtend_high n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (high n (zeroExtend n p1 + zeroExtend n p2)) = q.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_add -addn_add -toNat_addB_zeroExtend => H.
    rewrite -(toNat_eucl_high H). reflexivity.
  Qed.

  Lemma toPosZ_addB_zeroExtend_low n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (low n (zeroExtend n p1 + zeroExtend n p2)) = r.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_add -addn_add -toNat_addB_zeroExtend => H.
    rewrite -(toNat_eucl_low H). reflexivity.
  Qed.

  Lemma toPosZ_addB3_zeroExtend_high n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2 + toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (high n ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)) = q.
  Proof.
    rewrite !toPosZ_toNat -2!Nat2Z.inj_add -2!addn_add -toNat_addB3_zeroExtend.
    set p := ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)%bits.
    move=> H. symmetry. exact: (toNat_eucl_high H).
  Qed.

  Lemma toPosZ_addB3_zeroExtend_low n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2 + toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (low n ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)) = r.
  Proof.
    rewrite !toPosZ_toNat -2!Nat2Z.inj_add -2!addn_add -toNat_addB3_zeroExtend.
    set p := ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)%bits.
    move=> H. symmetry. exact: (toNat_eucl_low H).
  Qed.

  Lemma toPosZ_addB3_zeroExtend_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 -> ~~ carry_addB (p1 + p2)%bits p3 ->
    toPosZ (low n ((zeroExtend n p1 + zeroExtend n p2) + zeroExtend n p3))%bits =
    (toPosZ p1 + toPosZ p2 + toPosZ p3)%Z.
  Proof.
    move=> H1 H2. rewrite !toPosZ_toNat (toNat_addB3_zeroExtend_bounded H1 H2).
    rewrite !Nat2Z.inj_add. reflexivity.
  Qed.

  Lemma toPosZ_subB_bounded n (p1 p2 : BITS n) :
    ~~ carry_subB p1 p2 ->
    toPosZ (subB p1 p2) = toPosZ p1 - toPosZ p2.
  Proof.
    move/negPf=> Hc. move: (sbbB_ltB_leB p1 p2). rewrite Hc.
    move=> H. rewrite !toPosZ_toNat (toNat_subB H).
    rewrite leB_nat in H. move: (leq_le H) => {H} H.
    rewrite -(Nat2Z.inj_sub _ _ H) subn_sub. reflexivity.
  Qed.

  Lemma toPosZ_mulB_bounded n (p1 p2 : BITS n) :
    high n (fullmulB p1 p2) = zero n ->
    toPosZ (mulB p1 p2) = (toPosZ p1 * toPosZ p2).
  Proof.
    move=> H. rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite (toNat_mulB_bounded H). reflexivity.
  Qed.

  Lemma toPosZ_fullmulB_high n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 * toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (high n (fullmulB p1 p2)) = q.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite -toNat_mulB_zeroExtend mulB_zeroExtend_fullmulB. move=> H.
    rewrite -(toNat_eucl_high H). reflexivity.
  Qed.

  Lemma toPosZ_fullmulB_low n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 * toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (low n (fullmulB p1 p2)) = r.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite -toNat_mulB_zeroExtend mulB_zeroExtend_fullmulB. move=> H.
    rewrite -(toNat_eucl_low H). reflexivity.
  Qed.

  Lemma toPosZ_shlBn_bounded n i (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - i))%bits ->
    toPosZ (shlBn p i) = (toPosZ p * 2 ^ (Z.of_nat i)).
  Proof.
    move=> H. rewrite !toPosZ_toNat (toNat_shlBn_bounded H).
    rewrite Nat2Z.inj_mul expn_pow Nat2Z_inj_pow. reflexivity.
  Qed.

  Lemma toPosZ_shrBn n i (p : BITS n) :
    toPosZ (shrBn p i) = (toPosZ p) / (2 ^ Z.of_nat i).
  Proof.
    rewrite toPosZ_toNat toNat_shrBn.
    rewrite Nat2Z_inj_divn expn_pow Nat2Z_inj_pow -toPosZ_toNat.
    reflexivity.
  Qed.

  Lemma toPosZ_shrBn_high n q r i (p : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat i) ->
    toPosZ (shrBn p i) = q.
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_shrBn.
    set m := (toNat p). move: m => {p n} m H.
    rewrite (Zdiv_eucl_q H) => {H q r}.
    rewrite {2}(divn_eq m (2^i)) Nat2Z.inj_add Nat2Z.inj_mul.
    rewrite expn_pow Nat2Z_inj_pow /= -expn_pow.
    rewrite Z_div_plus_full_l.
    - rewrite Zdiv_small; first by rewrite Zplus_0_r; reflexivity. split.
      + change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_le 0 (m %% 2^i))).
        apply: leq_le. done.
      + change 2 with (Z.of_nat 2). rewrite expn_pow -Nat2Z_inj_pow -expn_pow.
        apply: (proj1 (Nat2Z.inj_lt (m %% 2^i) (2^i))).
        apply: ltn_lt. rewrite ltn_mod expn_gt0. done.
    - change 2 with (Z.of_nat 2). rewrite -Nat2Z_inj_pow -expn_pow.
      change 0 with (Z.of_nat 0). move=> H. move: (Nat2Z.inj _ _ H).
      apply/eqP. rewrite -lt0n expn_gt0. done.
  Qed.

  Lemma toPosZ_shrBn_low n q r i (p : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat i) ->
    toPosZ (shrBn (shlBn p (n - i)) (n - i)) = r.
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_shlBn_shrBn.
    set m := (toNat p). move: m => {p n} m H.
    rewrite (Zdiv_eucl_r H) => {H q r}.
    rewrite {2}(divn_eq m (2^i)) Nat2Z.inj_add Nat2Z.inj_mul.
    rewrite expn_pow Nat2Z_inj_pow /= -expn_pow.
    rewrite Zplus_comm Z_mod_plus_full. rewrite Zmod_small; first reflexivity.
    split.
    - change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_le 0 (m %% 2^i))).
      apply: leq_le. done.
    - change 2 with (Z.of_nat 2). rewrite expn_pow -Nat2Z_inj_pow -expn_pow.
      apply: (proj1 (Nat2Z.inj_lt (m %% 2^i) (2^i))).
      apply: ltn_lt. rewrite ltn_pmod; first done.
      by rewrite expn_gt0.
  Qed.

  Lemma toPosZ_catB_shlBn_high n q r i (p1 p2 : BITS n) :
    (i <= n)%N ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (q, r) =
    Z.div_eucl (toPosZ p1 * 2 ^ Z.of_nat n + toPosZ p2) (2 ^ Z.of_nat (n - i)) ->
    toPosZ (high n (shlBn (p1 ## p2) i)) = q.
  Proof.
    move=> Hin Hp1. rewrite !toPosZ_toNat => Heucl.
    rewrite toNat_high (toNat_catB_shlBn _ Hin Hp1).
    rewrite mulnDl -mulnA (mulnC (2^n)%N (2^i)%N) mulnA.
    rewrite (divnMDl _ _ (expn2_gt0 n)).
    move: (dvdn_exp2l 2 Hin) => H.
    rewrite -(divnA _ H) => {H}. have H1: (0 < 2)%N by done.
    rewrite -(expnB H1 Hin) => {H1}.
    rewrite (Zdiv_eucl_q Heucl).
    rewrite Nat2Z.inj_add Nat2Z.inj_mul expn_pow Nat2Z_inj_pow /=.
    rewrite Nat2Z_inj_divn expn_pow Nat2Z_inj_pow /=.
    set a := toNat p1; set b := toNat p2. move=> {Hp1 Heucl q r}.
    rewrite -{2}(subnK Hin). rewrite Nat2Z.inj_add.
    rewrite (Zpower_exp _ _ _
                        (Z.le_ge _ _ (Nat2Z.is_nonneg (n - i)))
                        (Z.le_ge _ _ (Nat2Z.is_nonneg i))).
    rewrite (Z.mul_comm (2^Z.of_nat(n-i)) (2^Z.of_nat i)) Z.mul_assoc.
    have Hne: 2 ^ Z.of_nat (n - i) <> 0.
    { change 2 with (Z.of_nat 2). rewrite -Nat2Z_inj_pow -expn_pow.
      change 0 with (Z.of_nat 0). move=> H; move: (Nat2Z.inj _ _ H).
      apply/eqP. rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Z_div_plus_full_l _ _ _ Hne).
    reflexivity.
  Qed.

  Lemma toPosZ_catB_shlBn_low_shrBn n q r i (p1 p2 : BITS n) :
    (i <= n)%N ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (q, r) =
    Z.div_eucl (toPosZ p1 * 2 ^ Z.of_nat n + toPosZ p2) (2 ^ Z.of_nat (n - i)) ->
    toPosZ (shrBn (low n (shlBn (p1 ## p2) i)) i) = r.
  Proof.
    move=> Hin Hp1. rewrite !toPosZ_toNat => Heucl.
    rewrite toNat_shrBn toNat_low (toNat_catB_shlBn _ Hin Hp1).
    rewrite mulnDl -mulnA (mulnC (2 ^ n)%N (2 ^ i)%N) mulnA modnMDl.
    rewrite (Zdiv_eucl_r Heucl).
    set a := toNat p1; set b := toNat p2. move: a b.
    move=> {q r p1 p2 Hp1 Heucl} a b.
    have Hn: (n = (n - i) + i)%N.
    { symmetry. apply: subnK. exact: Hin. }
    rewrite {2}Hn. rewrite Nat2Z.inj_add.
    rewrite (Zpower_exp _ _ _
                        (Z.le_ge _ _ (Nat2Z.is_nonneg (n - i)))
                        (Z.le_ge _ _ (Nat2Z.is_nonneg i))).
    rewrite (Z.mul_comm (2^Z.of_nat(n-i)) (2^Z.of_nat i)) Z.mul_assoc.
    rewrite Z.add_comm Z_mod_plus_full.
    rewrite {1}Hn expnD -(muln_modl (expn2_gt0 i)) (mulnK _ (expn2_gt0 i)).
    have Hne: (2 ^ (n - i))%N != 0%N. { rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Nat2Z_inj_modn _ Hne) expn_pow Nat2Z_inj_pow.
    reflexivity.
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
