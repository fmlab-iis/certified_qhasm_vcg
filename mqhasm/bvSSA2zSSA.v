
From Coq Require Import Arith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Common Require Import Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
From mQhasm Require Import QFBV zSSA bvSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation wordsize := AMD64.wordsize.

Opaque wordsize.

Import zSSA.
Import bv64SSA.



(** Convert instructions and programs. *)

Definition bv2z_atomic (a : atomic) : zSSA.exp :=
  match a with
  | bvVar v => zVar v
  | bvConst c => zConst (toPosZ c)
  end.

Definition bv2z_instr (i : instr) : seq zSSA.instr :=
  match i with
  | bvAssign v a => [:: zAssign v (bv2z_atomic a)]
(*  | bvNeg v a => [:: zAssign v (zUnop zNeg (bv2z_atomic a))] *)
  | bvAdd v a1 a2 => [:: zAssign v (zadd (bv2z_atomic a1) (bv2z_atomic a2))]
  | bvAddC c v a1 a2 =>
    [:: zSplit c v (zadd (bv2z_atomic a1) (bv2z_atomic a2)) wordsize]
  | bvSub v a1 a2 => [:: zAssign v (zsub (bv2z_atomic a1) (bv2z_atomic a2))]
(*  | bvSubC c v a1 a2 =>
    [:: zSplit
        c
        v
        (zsub (zadd (zpow2 wordsize) (bv2z_atomic a1)) (bv2z_atomic a2))
        wordsize;
       zAssign c (zsub zone (zVar c))] *)
  | bvMul v a1 a2 => [:: zAssign v (zmul (bv2z_atomic a1) (bv2z_atomic a2))]
  | bvMulf vh vl a1 a2 =>
    [:: zSplit vh vl (zmul (bv2z_atomic a1) (bv2z_atomic a2)) wordsize]
  | bvShl v a n => [:: zAssign v (zmul2p (bv2z_atomic a) (toNat n))]
  | bvSplit vh vl a n => [:: zSplit vh vl (bv2z_atomic a) (toNat n)]
  | bvConcatShl vh vl a1 a2 n =>
    [:: zSplit vh vl
        (zadd (zmul2p (bv2z_atomic a1) wordsize) (bv2z_atomic a2))
        (wordsize - (toNat n))]
  end.

Fixpoint bv2z_program (p : program) : zSSA.program :=
  match p with
  | [::] => [::]
  | hd::tl => (bv2z_instr hd) ++ (bv2z_program tl)
  end.

Definition addB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_addB bv1 bv2.

Definition subB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_subB bv1 bv2.

Definition mulB_safe w (bv1 bv2 : BITS w) : bool :=
  high w (fullmulB bv1 bv2) == fromNat 0.

Definition shlBn_safe w (bv : BITS w) n : bool :=
  ltB bv (shlBn (@fromNat w 1) (w - n)).

Definition concatshl_safe w (bv1 bv2 : BITS w) n : bool :=
  shlBn_safe bv1 n.

Definition bv2z_instr_safe_at (i : instr) (s : bv64SSA.State.t) : bool :=
  match i with
  | bvAssign _ _ => true
(*  | bvNeg _ _ => true *)
  | bvAdd _ a1 a2 => addB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvAddC _ _ _ _ => true
  | bvSub _ a1 a2 => subB_safe (eval_atomic a1 s) (eval_atomic a2 s)
(*  | bvSubC _ _ _ _ => true *)
  | bvMul _ a1 a2 => mulB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvMulf _ _ _ _ => true
  | bvShl _ a n => shlBn_safe (eval_atomic a s) (toNat n)
  | bvSplit _ _ _ _ => true
  | bvConcatShl _ _ a1 a2 n =>
    concatshl_safe (eval_atomic a1 s) (eval_atomic a1 s) (toNat n)
  end.

Fixpoint bv2z_program_safe_at p s : bool :=
  match p with
  | [::] => true
  | hd::tl => bv2z_instr_safe_at hd s && bv2z_program_safe_at tl (eval_instr s hd)
  end.

Definition bv2z_program_safe p : Prop :=
  forall s, bv2z_program_safe_at p s.



(** State equivalence. *)

Definition bvz_eq (sb : State.t) (sz : zSSA.State.t) : Prop :=
  forall x, toPosZ (State.acc x sb) = zSSA.State.acc x sz.

Lemma bvz_eq_upd v bv zv sb sz :
  bvz_eq sb sz ->
  toPosZ bv = zv ->
  bvz_eq (State.upd v bv sb) (zSSA.State.upd v zv sz).
Proof.
  move=> Heq Hbv x.
  case Hxv: (x == v).
  - rewrite (State.acc_upd_eq _ _ Hxv) (zSSA.State.acc_upd_eq _ _ Hxv).
    exact: Hbv.
  - move/idP/negP: Hxv => Hxv.
    rewrite (State.acc_upd_neq _ _ Hxv) (zSSA.State.acc_upd_neq _ _ Hxv).
    exact: Heq.
Qed.

Lemma bvz_eq_upd2 vh vl bvh bvl zvh zvl sb sz :
  bvz_eq sb sz ->
  toPosZ bvh = zvh ->
  toPosZ bvl = zvl ->
  bvz_eq (State.upd2 vh bvh vl bvl sb) (zSSA.State.upd2 vh zvh vl zvl sz).
Proof.
  move=> Heq Hbvh Hbvl x.
  case Hxvl: (x == vl).
  - rewrite (State.acc_upd_eq _ _ Hxvl) (zSSA.State.acc_upd_eq _ _ Hxvl).
    exact: Hbvl.
  - move/idP/negP: Hxvl => Hxvl.
    rewrite (State.acc_upd_neq _ _ Hxvl) (zSSA.State.acc_upd_neq _ _ Hxvl).
    case Hxvh: (x == vh).
    + rewrite (State.acc_upd_eq _ _ Hxvh) (zSSA.State.acc_upd_eq _ _ Hxvh).
      exact: Hbvh.
    + move/idP/negP: Hxvh => Hxvh.
      rewrite (State.acc_upd_neq _ _ Hxvh) (zSSA.State.acc_upd_neq _ _ Hxvh).
      exact: Heq.
Qed.



(** Properties of program conversion. *)

Lemma bvz_eq_eval_atomic a sb sz :
  bvz_eq sb sz ->
  toPosZ (eval_atomic a sb) = (zSSA.eval_exp (bv2z_atomic a) sz).
Proof.
  move=> Heq; case: a => /=.
  - move=> x.
    exact: Heq.
  - reflexivity.
Qed.

Lemma toPosZ_addB1 w (bv1 bv2 : BITS w) :
  ~~ carry_addB bv1 bv2 ->
  toPosZ (bv1 + bv2) = (toPosZ bv1 + toPosZ bv2)%Z.
Proof.
  move=> Hc.
  rewrite {1}toPosZ_toNat (toNat_addB_bounded Hc).
  rewrite Nat2Z.inj_add -!toPosZ_toNat. reflexivity.
Qed.

Lemma toPosZ_addB2 w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (@fromNat (1 + (w - 1)) (carry_addB bv1 bv2)) = q.
Proof.
  rewrite !toPosZ_toNat addB_zeroExtend1_high_ext toNat_zeroExtend.
  rewrite addB_zeroExtend1_high /adcB toNat_splitmsb1 toNat_adcBmain add0n.
  set n1 := toNat bv1; set n2 := toNat bv2.
  move=> Hediv.
  have: (2 ^ Z.of_nat w > 0)%Z.
  { apply: Z.lt_gt. apply: Z.pow_pos_nonneg; first by done.
    exact: Nat2Z.is_nonneg. }
  move=> H2wz.
  move: (Z_div_mod (Z.of_nat n1 + Z.of_nat n2) (2 ^ Z.of_nat w) H2wz).
  rewrite -Hediv -Nat2Z.inj_add.
  move=> [Hqr Hr].
  move: (Zdiv_unique _ _ _ _ Hr Hqr) => Hq.

  have: (0 <= q)%Z.
  { move: (Zdiv_eucl_q_ge0 (Z.of_nat n1 + Z.of_nat n2) (2 ^ Z.of_nat w)).
    rewrite -Hediv. apply; last exact: (Z.lt_le_incl _ _ (Z.gt_lt _ _ H2wz)).
    rewrite -Nat2Z.inj_add. exact: Nat2Z.is_nonneg. }
  move=> {Hediv H2wz} H0leq.

  have: 0 < 2 ^ w.
  { by rewrite expn_gt0. }
  move=> H2wn.

  have: Z.to_nat r < 2 ^ w.
  { apply/ltP. apply: (proj2 (Nat2Z.inj_lt (Z.to_nat r) (2 ^ w))).
    rewrite (Z2Nat.id _ (proj1 Hr)) expn_pow Nat2Z_inj_pow.
    exact: (proj2 Hr). }
  move=> Hrw.

  have: (2^Z.of_nat w * q + r)%Z = Z.of_nat (2 ^ w * Z.to_nat q + Z.to_nat r).
  { rewrite Nat2Z.inj_add Nat2Z.inj_mul expn_pow Nat2Z_inj_pow
            (Z2Nat.id _ H0leq) (Z2Nat.id r (proj1 Hr)) /=.
    reflexivity. }
  move=> Heq; rewrite Heq in Hqr => {Heq H0leq Hr}.
  move: (Nat2Z.inj _ _ Hqr) => {Hqr} Hqr.
  rewrite addn_add Hqr mulnC (divnMDl _ _ H2wn) (divn_small Hrw) addn0.
  rewrite Nat2Z.inj_add in Hq.
  move=> {H2wn Hrw Hqr}.

  case: (ltn_ltn_addn_divn (Zof_nat_toNat_bounded bv1)
                           (Zof_nat_toNat_bounded bv2)).
  - rewrite -{1}Hq => ->. reflexivity.
  - rewrite -{1}Hq => ->. reflexivity.
Qed.

Lemma toPosZ_addB3 w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (bv1 + bv2) = r.
Proof.
Admitted.

Lemma toPosZ_subB1 w (b1 b2 : BITS w) :
  ~~ carry_subB b1 b2 ->
  toPosZ (b1 - b2) = (toPosZ b1 - toPosZ b2)%Z.
Proof.
Admitted.

Lemma toPosZ_mulB w (bv1 bv2 : BITS w) :
  high w (fullmulB bv1 bv2) == fromNat 0 ->
  toPosZ (bv1 * bv2) = (toPosZ bv1 * toPosZ bv2)%Z.
Proof.
Admitted.

Lemma toPosZ_fullmulB1 w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 * toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (high w (fullmulB bv1 bv2)) = q.
Proof.
Admitted.

Lemma toPosZ_fullmulB2 w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 * toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (low w (fullmulB bv1 bv2)) = r.
Proof.
Admitted.

Lemma toPosZ_shlBn w n (bv : BITS w) :
  (bv < shlBn (@fromNat w 1) (w - n))%bits ->
  toPosZ (shlBn bv n) = (toPosZ bv * 2 ^ Z.of_nat n)%Z.
Proof.
Admitted.

Lemma toPosZ_shrBn1 w q r n (bv : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv) (2 ^ Z.of_nat n) ->
  toPosZ (shrBn bv n) = q.
Proof.
Admitted.

Lemma toPosZ_shrBn2 w q r n (bv : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv) (2 ^ Z.of_nat n) ->
  toPosZ (shrBn (shlBn bv (ssrnat.subn w n)) (ssrnat.subn w n)) = r.
Proof.
Admitted.

Lemma toPosZ_catB1 w q r n (bv1 bv2 : BITS w) :
  (bv1 < shlBn (@fromNat w 1) (w - n))%bits ->
  (q, r) =
  Z.div_eucl (toPosZ bv1 * 2 ^ Z.of_nat w + toPosZ bv2) (2 ^ Z.of_nat (w - n)) ->
  toPosZ (high w (shlBn (bv1 ## bv2) n)) = q.
Proof.
Admitted.

Lemma toPosZ_catB2 w q r n (bv1 bv2 : BITS w) :
  (bv1 < shlBn (@fromNat w 1) (w - n))%bits ->
  (q, r) =
  Z.div_eucl (toPosZ bv1 * 2 ^ Z.of_nat w + toPosZ bv2) (2 ^ Z.of_nat (w - n)) ->
  toPosZ (shrBn (low w (shlBn (bv1 ## bv2) n)) n) = r.
Proof.
Admitted.

Lemma bvz_eq_eval_instr i sb sz :
  bvz_eq sb sz ->
  bv2z_instr_safe_at i sb ->
  bvz_eq (eval_instr sb i) (zSSA.eval_program sz (bv2z_instr i)).
Proof.
  move=> Heq; case: i => /=.
  - move=> v a _ x.
    apply: (bvz_eq_upd _ Heq).
    exact: bvz_eq_eval_atomic.
  - move=> v a1 a2 Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_addB1.
  - move=> vh vl a1 a2 _ x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    set tmp :=
      Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                 (2 ^ Z.of_nat wordsize).
    have: tmp =
          Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                     (2 ^ Z.of_nat wordsize) by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_addB2 Hqr).
    + exact: (toPosZ_addB3 Hqr).
  - move=> v a1 a2 Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_subB1.
  - move=> v a1 a2 Hsafe x.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_mulB.
  - move=> vh vl a1 a2 _ x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    set tmp :=
      Z.div_eucl (toPosZ (eval_atomic a1 sb) * toPosZ (eval_atomic a2 sb))
                 (2 ^ Z.of_nat wordsize).
    have: tmp =
          Z.div_eucl (toPosZ (eval_atomic a1 sb) * toPosZ (eval_atomic a2 sb))
                     (2 ^ Z.of_nat wordsize) by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_fullmulB1 Hqr).
    + exact: (toPosZ_fullmulB2 Hqr).
  - move=> v a n Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a Heq).
    exact: toPosZ_shlBn.
  - move=> vh vl a n _ x.
    rewrite -(bvz_eq_eval_atomic a Heq).
    set tmp := Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n)).
    have: tmp = Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n))
      by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_shrBn1 Hqr).
    + exact: (toPosZ_shrBn2 Hqr).
  - move=> vh vl a1 a2 n Hsafe x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    set tmp :=
      Z.div_eucl
        (toPosZ (eval_atomic a1 sb) *
         2 ^ Z.of_nat wordsize +
             toPosZ (eval_atomic a2 sb)) (2 ^ Z.of_nat (wordsize - (toNat n))).
    have: tmp =
          Z.div_eucl
            (toPosZ (eval_atomic a1 sb) *
             2 ^ Z.of_nat wordsize +
                 toPosZ (eval_atomic a2 sb)) (2 ^ Z.of_nat (wordsize - (toNat n)))
      by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_catB1 Hsafe Hqr).
    + exact: (toPosZ_catB2 Hsafe Hqr).
Qed.

Lemma bvz_eq_eval_program p sb sz :
  bvz_eq sb sz ->
  bv2z_program_safe_at p sb ->
  bvz_eq (eval_program sb p) (zSSA.eval_program sz (bv2z_program p)).
Proof.
  elim: p sb sz => /=.
  - move=> sb sz Heq _; exact: Heq.
  - move=> hd tl IH sb sz Heq /andP [Hhd Htl].
    rewrite zSSA.eval_program_concat_step.
    apply: (IH _ _ _ Htl).
    exact: bvz_eq_eval_instr.
Qed.



(** Convert specifications. *)

Definition bv2z_binop (op : binop) : zSSA.binop :=
  match op with
  | bvAddOp => zSSA.zAdd
  | bvSubOp => zSSA.zSub
  | bvMulOp => zSSA.zMul
  end.

Fixpoint bv2z_exp n (e : exp n) : zSSA.exp :=
  match e with
  | bvVarE v => zVar v
  | bvConstE _ c => zConst (toPosZ c)
  | bvBinop _ op e1 e2 => zBinop (bv2z_binop op) (bv2z_exp e1) (bv2z_exp e2)
  | bvExt _ e _ => bv2z_exp e
  end.

Inductive ebexp :=
  | bvETrue : ebexp
  | bvEEq : forall n : nat, exp n -> exp n -> ebexp
  | bvEEqMod : forall n : nat, exp n -> exp n -> exp n -> ebexp
  | bvEAnd : ebexp -> ebexp -> ebexp.

Inductive cbexp :=
  | bvCTrue : cbexp
  | bvCCmp : forall n : nat, cmpop -> exp n -> exp n -> cbexp
  | bvCAnd : cbexp -> cbexp -> cbexp.

Fixpoint split_bexp (e : bexp) : ebexp * cbexp :=
  match e with
  | bvTrue => (bvETrue, bvCTrue)
  | bvEq _ e1 e2 => (bvEEq e1 e2, bvCTrue)
  | bvEqMod _ e1 e2 p => (bvEEqMod e1 e2 p, bvCTrue)
  | bvCmp _ op e1 e2 => (bvETrue, bvCCmp op e1 e2)
  | bvAnd e1 e2 =>
    (bvEAnd (fst (split_bexp e1)) (fst (split_bexp e2)),
     bvCAnd (snd (split_bexp e1)) (snd (split_bexp e2)))
  end.

Fixpoint bv2z_ebexp e : zSSA.bexp :=
  match e with
  | bvETrue => zSSA.zTrue
  | bvEEq _ e1 e2 => zSSA.zEq (bv2z_exp e1) (bv2z_exp e2)
  | bvEEqMod _ e1 e2 p =>
    zSSA.zEqMod (bv2z_exp e1) (bv2z_exp e2) (bv2z_exp p)
  | bvEAnd e1 e2 => zSSA.zAnd (bv2z_ebexp e1) (bv2z_ebexp e2)
  end.

Fixpoint bexp_of_cbexp e : bexp :=
  match e with
  | bvCTrue => bvTrue
  | bvCCmp _ op e1 e2 => bvCmp op e1 e2
  | bvCAnd e1 e2 => bvAnd (bexp_of_cbexp e1) (bexp_of_cbexp e2)
  end.

Definition bv2z_binop_safe w op (bv1 bv2 : BITS w) : bool :=
  match op with
  | bvAddOp => addB_safe bv1 bv2
  | bvSubOp => subB_safe bv1 bv2
  | bvMulOp => mulB_safe bv1 bv2
  end.

Fixpoint bv2z_exp_safe_at n (e : exp n) s : bool :=
  match e with
  | bvVarE _
  | bvConstE _ _ => true
  | bvBinop _ op e1 e2 =>
    bv2z_exp_safe_at e1 s &&
    bv2z_exp_safe_at e2 s &&
    bv2z_binop_safe op (eval_exp e1 s) (eval_exp e2 s)
  | bvExt _ e _ => bv2z_exp_safe_at e s
  end.

Fixpoint bv2z_bexp_safe_at (e : bexp) s : bool :=
  match e with
  | bvTrue => true
  | bvEq _ e1 e2 => bv2z_exp_safe_at e1 s && bv2z_exp_safe_at e2 s
  | bvEqMod _ e1 e2 p => bv2z_exp_safe_at e1 s
                                          && bv2z_exp_safe_at e2 s
                                          && bv2z_exp_safe_at p s
  | bvCmp _ op e1 e2 => bv2z_exp_safe_at e1 s && bv2z_exp_safe_at e2 s
  | bvAnd e1 e2 => bv2z_bexp_safe_at e1 s && bv2z_bexp_safe_at e2 s
  end.

Definition bv2z_spec_rng s : spec :=
  {| spre := spre s;
     sprog := sprog s;
     spost := bexp_of_cbexp (snd (split_bexp (spost s))) |}.

Definition bv2z_spec_poly s : zSSA.spec :=
  {| zSSA.spre := bv2z_ebexp (fst (split_bexp (spre s)));
     zSSA.sprog := bv2z_program (sprog s);
     zSSA.spost := bv2z_ebexp (fst (split_bexp (spost s))) |}.

Definition bv2z_spre_safe f : Prop :=
  forall s, eval_bexp f s -> bv2z_bexp_safe_at f s.

Definition bv2z_sprog_safe f p : Prop :=
  forall s, eval_bexp f s -> bv2z_program_safe_at p s.

Definition bv2z_spost_safe f p g : Prop :=
  forall s1 s2, eval_bexp f s1 -> eval_program s1 p = s2 ->
                bv2z_bexp_safe_at g s2.

Definition bv2z_spec_safe sp :=
  bv2z_spre_safe (spre sp) /\
  bv2z_sprog_safe (spre sp) (sprog sp) /\
  bv2z_spost_safe (spre sp) (sprog sp) (spost sp).



(** Properties of specification conversion. *)

Lemma bvz_eq_eval_binop w op (bv1 bv2 : BITS w) :
  bv2z_binop_safe op bv1 bv2 ->
  toPosZ (eval_binop op bv1 bv2) =
  zSSA.eval_binop (bv2z_binop op) (toPosZ bv1) (toPosZ bv2).
Proof.
  case: op => /= Hsafe.
  - exact: toPosZ_addB1.
  - exact: toPosZ_subB1.
  - exact: toPosZ_mulB.
Qed.

Lemma bvz_eq_eval_exp w (e : exp w) bs zs :
  bv2z_exp_safe_at e bs ->
  bvz_eq bs zs ->
  toPosZ (eval_exp e bs) = zSSA.eval_exp (bv2z_exp e) zs.
Proof.
  elim: e => {w} /=.
  - move=> a _ Heq. exact: Heq.
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2 /andP [/andP [Hsafe1 Hsafe2] Hsafeop] Heq.
    rewrite -(IH1 Hsafe1 Heq) -(IH2 Hsafe2 Heq).
    exact: bvz_eq_eval_binop.
  - move=> w e IH m Hsafe Heq.
    rewrite -(IH Hsafe Heq).
    exact: toPosZ_zeroExtend.
Qed.

Lemma bvz_eq_eval_bexp e bs zs :
  bv2z_bexp_safe_at e bs ->
  bvz_eq bs zs ->
  eval_bexp e bs ->
  zSSA.eval_bexp (bv2z_ebexp (fst (split_bexp e))) zs.
Proof.
  elim: e => /=.
  - done.
  - move=> w e1 e2 /andP [Hsafe1 Hsafe2] Heq Heval.
    rewrite -(bvz_eq_eval_exp Hsafe1 Heq) -(bvz_eq_eval_exp Hsafe2 Heq).
    rewrite Heval; reflexivity.
  - move=> w e1 e2 p /andP [/andP [Hsafe1 Hsafe2] Hsafep] Heq Heval.
    rewrite -(bvz_eq_eval_exp Hsafe1 Heq) -(bvz_eq_eval_exp Hsafe2 Heq)
            -(bvz_eq_eval_exp Hsafep Heq).
    exact: Heval.
  - done.
  - move=> e1 IH1 e2 IH2 /andP [Hsafe1 Hsafe2] Heq [Heval1 Heval2].
    split; [exact: (IH1 Hsafe1 Heq Heval1) | exact: (IH2 Hsafe2 Heq Heval2)].
Qed.

Lemma split_bexp_combine e bs zs :
  bv2z_bexp_safe_at e bs ->
  bvz_eq bs zs ->
  eval_bexp (bexp_of_cbexp (snd (split_bexp e))) bs ->
  zSSA.eval_bexp (bv2z_ebexp (fst (split_bexp e))) zs ->
  eval_bexp e bs.
Proof.
  elim: e => /=.
  - done.
  - move=> w e1 e2 /andP [Hsafe1 Hsafe2] Heq _ Heval.
    rewrite -(bvz_eq_eval_exp Hsafe1 Heq) -(bvz_eq_eval_exp Hsafe2 Heq) in Heval.
    exact: (toPosZ_inj Heval).
  - move=> w e1 e2 p /andP [/andP [Hsafe1 Hsafe2] Hsafep] Heq _ Heval.
    rewrite -(bvz_eq_eval_exp Hsafe1 Heq) -(bvz_eq_eval_exp Hsafe2 Heq)
            -(bvz_eq_eval_exp Hsafep Heq) in Heval.
    exact: Heval.
  - move=> w op e1 e2 /andP [Hsafe1 Hsafe2] Heq Heval _.
    exact: Heval.
  - move=> e1 IH1 e2 IH2 /andP [Hsafe1 Hsafe2] Heq [Hsnd1 Hsnd2] [Hfst1 Hfst2].
    split; [ exact: (IH1 Hsafe1 Heq Hsnd1 Hfst1) |
             exact: (IH2 Hsafe2 Heq Hsnd2 Hfst2) ].
Qed.



(** Convert bvState to zState. *)

Definition bv2z_state bs : zSSA.State.t :=
  fun v => toPosZ (State.acc v bs).

Lemma bv2z_state_eq bs :
  bvz_eq bs (bv2z_state bs).
Proof.
  move=> x; reflexivity.
Qed.



(** Well-formedness *)

Module M2 := Map2 VS zSSA.VS.

Definition bv2z_vars vs : zSSA.VS.t :=
  M2.map2 id vs.

Definition bv2z_vars_well : M2.well_map2 id.
Proof.
  split.
  - move=> x y Heq.
    rewrite (eqP Heq); exact: eqxx.
  - move=> x y Heq.
    exact: Heq.
Qed.

Lemma bv2z_vars_mem v vs :
  VS.mem v vs = zSSA.VS.mem v (bv2z_vars vs).
Proof.
  rewrite (M2.map2_mem1 bv2z_vars_well).
  reflexivity.
Qed.

Lemma bv2z_vars_mem1 v vs :
  VS.mem v vs -> zSSA.VS.mem v (bv2z_vars vs).
Proof.
  by rewrite bv2z_vars_mem.
Qed.

Lemma bv2z_vars_mem2 v vs :
  zSSA.VS.mem v (bv2z_vars vs) -> VS.mem v vs.
Proof.
  by rewrite bv2z_vars_mem.
Qed.

Lemma bv2z_vars_singleton v :
  zSSA.VS.Equal (zSSA.VS.singleton v) (bv2z_vars (VS.singleton v)).
Proof.
  done.
Qed.

Lemma bv2z_vars_add v vs :
  zSSA.VS.Equal (bv2z_vars (VS.add v vs)) (zSSA.VS.add v (bv2z_vars vs)).
Proof.
  rewrite /bv2z_vars (M2.map2_add bv2z_vars_well).
  reflexivity.
Qed.

Lemma bv2z_vars_add_singleton v1 v2 :
  zSSA.VS.Equal (zSSA.VS.add v1 (zSSA.VS.singleton v2))
                (bv2z_vars (VS.add v1 (VS.singleton v2))).
Proof.
  move=> x; split => Hin;
  move/zSSA.VSLemmas.memP: Hin => Hmem;
  apply/zSSA.VSLemmas.memP.
  - rewrite -bv2z_vars_mem.
    case: (zSSA.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
    + apply: VSLemmas.mem_add2; assumption.
    + apply: VSLemmas.mem_add3.
      rewrite bv2z_vars_mem; assumption.
  - rewrite -bv2z_vars_mem in Hmem.
    case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
    + apply: zSSA.VSLemmas.mem_add2; assumption.
    + apply: zSSA.VSLemmas.mem_add3; assumption.
Qed.

Lemma bv2z_vars_union vs1 vs2 :
  zSSA.VS.Equal (bv2z_vars (VS.union vs1 vs2))
                (zSSA.VS.union (bv2z_vars vs1) (bv2z_vars vs2)).
Proof.
  move=> x; split => Hin;
  move/zSSA.VSLemmas.memP: Hin => Hmem;
  apply/zSSA.VSLemmas.memP.
  - rewrite -bv2z_vars_mem in Hmem.
    case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
    rewrite bv2z_vars_mem in Hmem.
    + apply: zSSA.VSLemmas.mem_union2; assumption.
    + apply: zSSA.VSLemmas.mem_union3; assumption.
  - rewrite -bv2z_vars_mem.
    case: (zSSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
    rewrite -bv2z_vars_mem in Hmem.
    + apply: VSLemmas.mem_union2; assumption.
    + apply: VSLemmas.mem_union3; assumption.
Qed.

Lemma bv2z_vars_subset vs1 vs2 :
  zSSA.VS.subset (bv2z_vars vs1) (bv2z_vars vs2) = VS.subset vs1 vs2.
Proof.
  exact: (M2.map2_subset bv2z_vars_well).
Qed.

Lemma bv2z_vars_subset_atomic vs a :
  VS.subset (vars_atomic a) vs ->
  zSSA.VS.subset (zSSA.vars_exp (bv2z_atomic a)) (bv2z_vars vs).
Proof.
  case: a => /=.
  - move=> v Hsubset.
    move: (VSLemmas.subset_singleton1 Hsubset) => {Hsubset} Hmem.
    apply: zSSA.VSLemmas.subset_singleton2.
    rewrite -bv2z_vars_mem.
    exact: Hmem.
  - move=> _ _.
    exact: zSSA.VSLemmas.subset_empty.
Qed.

Lemma lvs_bv2z_instr i :
  zSSA.VS.Equal (zSSA.lvs_program (bv2z_instr i)) (bv2z_vars (lvs_instr i)).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- context f [zSSA.VS.union _ zSSA.VS.empty] =>
         rewrite zSSA.VSLemmas.union_emptyr; tac
       | |- zSSA.VS.Equal (zSSA.VS.singleton ?v) (bv2z_vars (VS.singleton ?v)) =>
         exact: bv2z_vars_singleton
       | |- zSSA.VS.Equal (zSSA.VS.add ?v1 (zSSA.VS.singleton ?v2))
                          (bv2z_vars (VS.add ?v1 (VS.singleton ?v2))) =>
         exact: bv2z_vars_add_singleton
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma vars_bv2z_atomic a :
  zSSA.VS.Equal (zSSA.vars_exp (bv2z_atomic a))
                (bv2z_vars (vars_atomic a)).
Proof.
  case: a => /=.
  - move=> v.
    exact: bv2z_vars_singleton.
  - reflexivity.
Qed.

Lemma vars_bv2z_instr i :
  zSSA.VS.Equal (zSSA.vars_program (bv2z_instr i))
                (bv2z_vars (vars_instr i)).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- context f [zSSA.VS.union _ zSSA.VS.empty] =>
         rewrite zSSA.VSLemmas.union_emptyr; tac
       | |- context f [bv2z_vars (VS.add _ _)] =>
         rewrite bv2z_vars_add; tac
       | |- context f [bv2z_vars (VS.union _ _)] =>
         rewrite bv2z_vars_union; tac
       | |- context f [bv2z_vars (vars_atomic _)] =>
         rewrite vars_bv2z_atomic; tac
       | |- zSSA.VS.Equal ?vs ?vs =>
         reflexivity
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma vars_bv2z_program p :
  zSSA.VS.Equal (zSSA.vars_program (bv2z_program p))
                (bv2z_vars (vars_program p)).
Proof.
  elim: p => /=.
  - reflexivity.
  - move=> hd tl IH.
    rewrite bv2z_vars_union (zSSA.vars_program_concat) IH vars_bv2z_instr.
    reflexivity.
Qed.

Lemma bv2z_exp_vars w (e : exp w) :
  zSSA.VS.Equal (zSSA.vars_exp (bv2z_exp e)) (bv2z_vars (vars_exp e)).
Proof.
  elim: e => {w} /=.
  - move=> a. exact: bv2z_vars_singleton.
  - reflexivity.
  - move=> w _ e1 IH1 e2 IH2.
    rewrite IH1 IH2 bv2z_vars_union.
    reflexivity.
  - move=> w e IH _.
    assumption.
Qed.

Lemma split_bexp_vars_subset1 f :
  zSSA.VS.subset (zSSA.vars_bexp (bv2z_ebexp (fst (split_bexp f))))
                 (bv2z_vars (vars_bexp f)).
Proof.
  elim: f => /=; intros;
  (let rec tac :=
       match goal with
       | |- is_true (zSSA.VS.subset zSSA.VS.empty _) =>
         exact: zSSA.VSLemmas.subset_empty
       | |- is_true (zSSA.VS.subset _ (bv2z_vars (VS.union _ _))) =>
         rewrite !bv2z_vars_union;
         repeat (apply: zSSA.VSLemmas.subset_union3);
         tac
       | |- is_true (zSSA.VS.subset
                       (zSSA.vars_exp (bv2z_exp ?e))
                       (zSSA.VS.union (bv2z_vars (vars_exp ?e)) _)) =>
         apply: zSSA.VSLemmas.subset_union1;
         rewrite bv2z_exp_vars;
         exact: zSSA.VSLemmas.subset_refl
       | |- is_true (zSSA.VS.subset
                       (zSSA.vars_exp (bv2z_exp ?e))
                       (zSSA.VS.union _ (bv2z_vars (vars_exp ?e)))) =>
         apply: zSSA.VSLemmas.subset_union2;
         rewrite bv2z_exp_vars;
         exact: zSSA.VSLemmas.subset_refl
       | |- is_true (zSSA.VS.subset
                       (zSSA.vars_exp (bv2z_exp ?e))
                       (zSSA.VS.union _ (zSSA.VS.union _ _))) =>
         apply: zSSA.VSLemmas.subset_union2; tac
       | H : is_true (zSSA.VS.subset ?vs1 ?vs2) |-
         is_true (zSSA.VS.subset ?vs1 (zSSA.VS.union ?vs2 _)) =>
         apply: zSSA.VSLemmas.subset_union1;
         assumption
       | H : is_true (zSSA.VS.subset ?vs1 ?vs2) |-
         is_true (zSSA.VS.subset ?vs1 (zSSA.VS.union _ ?vs2)) =>
         apply: zSSA.VSLemmas.subset_union2;
         assumption
       | |- is_true (zSSA.VS.subset
                       (zSSA.VS.union
                          (zSSA.vars_exp (bv2z_exp ?e1))
                          (zSSA.vars_exp (bv2z_exp ?e2)))
                       (bv2z_vars (VS.union (vars_exp ?e1)
                                            (vars_exp ?e2)))) =>
         rewrite bv2z_vars_union;
         apply: zSSA.VSLemmas.subset_union3;
         [ apply: zSSA.VSLemmas.subset_union1;
           rewrite bv2z_exp_vars;
           exact: zSSA.VSLemmas.subset_refl
         | apply: zSSA.VSLemmas.subset_union2;
           rewrite bv2z_exp_vars;
           exact: zSSA.VSLemmas.subset_refl ]
       | |- _ => idtac
       end in
  tac).
Qed.

Lemma split_bexp_vars_subset2 f :
  VS.subset (vars_bexp (bexp_of_cbexp (snd (split_bexp f))))
            (vars_bexp f).
Proof.
  elim: f => /=.
  - exact: VSLemmas.subset_empty.
  - move=> w e1 e2; exact: VSLemmas.subset_empty.
  - move=> w e1 e2 p; exact: VSLemmas.subset_empty.
  - move=> w _ e1 e2.
    exact: VSLemmas.subset_refl.
  - move=> e1 IH1 e2 IH2.
    apply: VSLemmas.subset_union3.
    + apply: VSLemmas.subset_union1; assumption.
    + apply: VSLemmas.subset_union2; assumption.
Qed.

Lemma bv2z_instr_well_formed vs i :
  well_formed_instr vs i ->
  zSSA.well_formed_program (bv2z_vars vs) (bv2z_instr i).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- is_true true => done
       | |- is_true (_ && _) => apply/andP; split; tac
       | H : is_true (_ && _) |- _ =>
         let H1 := fresh in
         let H2 := fresh in
         move/andP: H => [H1 H2]; tac
       | H : is_true (VS.subset (vars_atomic ?a) ?vs) |-
         is_true (zSSA.VS.subset
                    (zSSA.vars_exp (bv2z_atomic ?a)) (bv2z_vars ?vs)) =>
           by rewrite (bv2z_vars_subset_atomic H)
       | |- is_true (zSSA.VS.subset (zSSA.VS.union ?vs1 ?vs2) ?vs3) =>
         apply: zSSA.VSLemmas.subset_union3; tac
       | |- is_true (zSSA.VS.subset zSSA.VS.empty _) =>
         exact: zSSA.VSLemmas.subset_empty
       | H : is_true (?x != ?y) |- is_true (?x != ?y) => exact: H
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_well_formed vs p :
  well_formed_program vs p ->
  zSSA.well_formed_program (bv2z_vars vs) (bv2z_program p).
Proof.
  elim: p vs => /=.
  - done.
  - move=> hd tl IH vs /andP [Hwellhd Hwelltl].
    rewrite zSSA.well_formed_program_concat.
    rewrite (bv2z_instr_well_formed Hwellhd) /=.
    apply: (@zSSA.well_formed_program_replace (bv2z_vars (VS.union vs (lvs_instr hd)))).
  - exact: (IH _ Hwelltl).
  - rewrite lvs_bv2z_instr -bv2z_vars_union.
    reflexivity.
Qed.

Lemma bv2z_vars_unchanged_instr vs i :
  ssa_vars_unchanged_instr vs i ->
  zSSA.ssa_vars_unchanged_program (bv2z_vars vs) (bv2z_instr i).
Proof.
  case: i => /=; intros;
  (match goal with
   | H : is_true (ssa_vars_unchanged_instr ?vs _) |-
     is_true (zSSA.ssa_vars_unchanged_program (bv2z_vars ?vs) [:: _]) =>
     let x := fresh in let Hx := fresh in
     apply: zSSA.ssa_unchanged_program_global => x Hx /=;
     move: (ssa_unchanged_instr_local H (bv2z_vars_mem2 Hx));
     rewrite /ssa_var_unchanged_instr /zSSA.ssa_var_unchanged_instr /=;
     move=> ->; done
   | |- _ => idtac
   end).
Qed.

Lemma bv2z_vars_unchanged_program vs p :
  ssa_vars_unchanged_program vs p ->
  zSSA.ssa_vars_unchanged_program (bv2z_vars vs) (bv2z_program p).
Proof.
  elim: p vs => /=.
  - move=> vs _. exact: zSSA.ssa_unchanged_program_empty.
  - move=> i p IH vs Hun.
    move: (ssa_unchanged_program_cons1 Hun) => {Hun} [Hi Hp].
    apply: zSSA.ssa_unchanged_program_concat2.
    + exact: bv2z_vars_unchanged_instr Hi.
    + exact: (IH _ Hp).
Qed.

Lemma bv2z_instr_single_assignment i :
  zSSA.ssa_single_assignment (bv2z_instr i).
Proof.
  by case: i => /=; intros; try rewrite zSSA.ssa_unchanged_program_empty.
Qed.

Lemma bv2z_program_single_assignment p :
  ssa_single_assignment p ->
  zSSA.ssa_single_assignment (bv2z_program p).
Proof.
  elim: p => /=.
  - done.
  - move=> i p IH /andP [Hi Hp].
    apply: zSSA.ssa_single_assignment_concat2.
    + exact: bv2z_instr_single_assignment.
    + exact: (IH Hp).
    + apply: (zSSA.ssa_unchanged_program_replace).
      * move: (lvs_bv2z_instr i) => ->. reflexivity.
      * exact: (bv2z_vars_unchanged_program Hi).
Qed.

Lemma bv2z_program_well_formed_ssa vs p :
  well_formed_ssa_program vs p ->
  zSSA.well_formed_ssa_program (bv2z_vars vs) (bv2z_program p).
Proof.
  move=> /andP [/andP [Hwf Hun] Hssa].
  apply/andP; split; first (apply/andP; split).
  - exact: bv2z_program_well_formed.
  - exact: bv2z_vars_unchanged_program.
  - exact: bv2z_program_single_assignment.
Qed.

Lemma bv2z_spec_rng_well_formed vs sp :
  well_formed_spec vs sp ->
  well_formed_spec vs (bv2z_spec_rng sp).
Proof.
  destruct sp as [f p g].
  move=> /andP /= [/andP [Hf Hp] Hg].
  rewrite /well_formed_spec /=.
  rewrite Hf Hp /=.
  apply: (VSLemmas.subset_trans _ Hg).
  exact: split_bexp_vars_subset2.
Qed.

Lemma bv2z_spec_poly_well_formed vs sp :
  well_formed_spec vs sp ->
  zSSA.well_formed_spec (bv2z_vars vs) (bv2z_spec_poly sp).
Proof.
  destruct sp as [f p g].
  move=> /andP /= [/andP [Hf Hp] Hg].
  apply/andP => /=; split; first (apply/andP; split).
  - apply: (@zSSA.VSLemmas.subset_trans _ (bv2z_vars (vars_bexp f))).
    + exact: split_bexp_vars_subset1.
    + rewrite bv2z_vars_subset; assumption.
  - exact: bv2z_program_well_formed.
  - apply: (zSSA.VSLemmas.subset_trans (split_bexp_vars_subset1 g)).
    rewrite vars_bv2z_program -bv2z_vars_union bv2z_vars_subset.
    assumption.
Qed.

Theorem bv2z_spec_poly_well_formed_ssa vs sp :
  well_formed_ssa_spec vs sp ->
  zSSA.well_formed_ssa_spec (bv2z_vars vs) (bv2z_spec_poly sp).
Proof.
  destruct sp as [f p g].
  move=> /andP /= [/andP [Hf Hp] Hg].
  apply/andP => /=; split; first (apply/andP; split).
  - exact: bv2z_spec_poly_well_formed.
  - exact: bv2z_vars_unchanged_program.
  - exact: bv2z_program_single_assignment.
Qed.



(** Soundness *)

Theorem bv2z_spec_sound sp :
  bv2z_spec_safe sp ->
  valid_spec (bv2z_spec_rng sp) ->
  zSSA.valid_spec (bv2z_spec_poly sp) ->
  valid_spec sp.
Proof.
  destruct sp as [f p g] => /=.
  move=> [/= Hsafef [Hsafep Hsafeg]] Hrng Heqn bs1 bs2 /= Hbf Hbp.
  move: (Hrng bs1 bs2 Hbf Hbp) => {Hrng} /= Hrng.
  set zs1 := bv2z_state bs1.
  set zs2 := zSSA.eval_program zs1 (bv2z_program p).
  move: (Heqn zs1 zs2
              (bvz_eq_eval_bexp (Hsafef bs1 Hbf) (bv2z_state_eq bs1) Hbf)
              (Logic.eq_refl zs2)) => {Heqn} /= Heqn.
  apply: (@split_bexp_combine g bs2 zs2 (Hsafeg bs1 bs2 Hbf Hbp) _ Hrng Heqn).
  rewrite -Hbp.
  exact: (bvz_eq_eval_program (bv2z_state_eq bs1) (Hsafep _ Hbf)).
Qed.
