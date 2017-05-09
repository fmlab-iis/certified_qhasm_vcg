
From Coq Require Import Arith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Common Require Import Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
From mQhasm Require Import zDSL bvDSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation wordsize := AMD64.wordsize.

Opaque wordsize.



(** Convert instructions and programs. *)

Definition bv2z_atomic (a : atomic) : zDSL.exp :=
  match a with
  | bvVar v => zDSL.zVar v
  | bvConst c => zConst (toPosZ c)
  end.

Definition bv2z_instr (i : instr) : seq zDSL.instr :=
  match i with
  | bvAssign v a => [:: zAssign v (bv2z_atomic a)]
(*  | bvNeg v a => [:: zAssign v (zUnop zNeg (bv2z_atomic a))] *)
  | bvAdd v a1 a2 => [:: zAssign v (zadd (bv2z_atomic a1) (bv2z_atomic a2))]
  | bvAddC c v a1 a2 =>
    [:: zSplit c v (zadd (bv2z_atomic a1) (bv2z_atomic a2)) wordsize]
  | bvAdc v a1 a2 c =>
    [:: zAssign v (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar c))]
  | bvAdcC c v a1 a2 a =>
    [:: zSplit c v (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar a)) wordsize]
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

Fixpoint bv2z_program (p : program) : zDSL.program :=
  match p with
  | [::] => [::]
  | hd::tl => (bv2z_instr hd) ++ (bv2z_program tl)
  end.

Definition addB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_addB bv1 bv2.

Definition adcB_safe w (bv1 bv2 c : BITS w) : bool :=
  high w (addB (addB (zeroExtend w bv1)
                     (zeroExtend w bv2))
               (zeroExtend w c)) == fromNat 0.

Definition subB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_subB bv1 bv2.

Definition mulB_safe w (bv1 bv2 : BITS w) : bool :=
  high w (fullmulB bv1 bv2) == fromNat 0.

Definition shlBn_safe w (bv : BITS w) n : bool :=
  ltB bv (shlBn (@fromNat w 1) (w - n)).

Definition concatshl_safe w (bv : BITS w) n : bool :=
    ltB bv (shlBn (@fromNat w 1) (w - n)).

Definition bv2z_instr_safe_at (i : instr) (s : bv64DSL.State.t) : bool :=
  match i with
  | bvAssign _ _ => true
(*  | bvNeg _ _ => true *)
  | bvAdd _ a1 a2 => addB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvAddC _ _ _ _ => true
  | bvAdc _ a1 a2 c => adcB_safe (eval_atomic a1 s) (eval_atomic a2 s)
                                 (bv64DSL.State.acc c s)
  | bvAdcC _ _ _ _ _ => true
  | bvSub _ a1 a2 => subB_safe (eval_atomic a1 s) (eval_atomic a2 s)
(*  | bvSubC _ _ _ _ => true *)
  | bvMul _ a1 a2 => mulB_safe (eval_atomic a1 s) (eval_atomic a2 s)
  | bvMulf _ _ _ _ => true
  | bvShl _ a n => shlBn_safe (eval_atomic a s) (toNat n)
  | bvSplit _ _ _ _ => true
  | bvConcatShl _ _ a1 a2 n => concatshl_safe (eval_atomic a1 s) (toNat n)
  end.

Fixpoint bv2z_program_safe_at p s : bool :=
  match p with
  | [::] => true
  | hd::tl => bv2z_instr_safe_at hd s && bv2z_program_safe_at tl (eval_instr s hd)
  end.

Definition bv2z_program_safe p : Prop :=
  forall s, bv2z_program_safe_at p s.



(** State equivalence. *)

Definition bvz_eq (sb : State.t) (sz : zDSL.State.t) : Prop :=
  forall x, toPosZ (State.acc x sb) = zDSL.State.acc x sz.

Lemma bvz_eq_upd v bv zv sb sz :
  bvz_eq sb sz ->
  toPosZ bv = zv ->
  bvz_eq (State.upd v bv sb) (zDSL.State.upd v zv sz).
Proof.
  move=> Heq Hbv x.
  case Hxv: (x == v).
  - rewrite (State.acc_upd_eq _ _ Hxv) (zDSL.State.acc_upd_eq _ _ Hxv).
    exact: Hbv.
  - move/idP/negP: Hxv => Hxv.
    rewrite (State.acc_upd_neq _ _ Hxv) (zDSL.State.acc_upd_neq _ _ Hxv).
    exact: Heq.
Qed.

Lemma bvz_eq_upd2 vh vl bvh bvl zvh zvl sb sz :
  bvz_eq sb sz ->
  toPosZ bvh = zvh ->
  toPosZ bvl = zvl ->
  bvz_eq (State.upd2 vh bvh vl bvl sb) (zDSL.State.upd2 vh zvh vl zvl sz).
Proof.
  move=> Heq Hbvh Hbvl x.
  case Hxvl: (x == vl).
  - rewrite (State.acc_upd_eq _ _ Hxvl) (zDSL.State.acc_upd_eq _ _ Hxvl).
    exact: Hbvl.
  - move/idP/negP: Hxvl => Hxvl.
    rewrite (State.acc_upd_neq _ _ Hxvl) (zDSL.State.acc_upd_neq _ _ Hxvl).
    case Hxvh: (x == vh).
    + rewrite (State.acc_upd_eq _ _ Hxvh) (zDSL.State.acc_upd_eq _ _ Hxvh).
      exact: Hbvh.
    + move/idP/negP: Hxvh => Hxvh.
      rewrite (State.acc_upd_neq _ _ Hxvh) (zDSL.State.acc_upd_neq _ _ Hxvh).
      exact: Heq.
Qed.



(** Properties of program conversion. *)

Lemma bvz_eq_eval_atomic a sb sz :
  bvz_eq sb sz ->
  toPosZ (eval_atomic a sb) = (zDSL.eval_exp (bv2z_atomic a) sz).
Proof.
  move=> Heq; case: a => /=.
  - move=> x.
    exact: Heq.
  - reflexivity.
Qed.

Lemma toPosZ_addB2' w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (@fromNat (1 + (w - 1)) (carry_addB bv1 bv2)) = q.
Proof.
  rewrite !toPosZ_toNat -addB_zeroExtend1_high_ext toNat_zeroExtend.
  rewrite addB_zeroExtend1_high singleBit_fromNat.
  have H: carry_addB bv1 bv2 < 2 ^ 1.
  { by case: (carry_addB bv1 bv2). }
  rewrite (fromNatK H). rewrite carry_addB_divn.
  exact: (bounded_div_eucl1 (toNatBounded bv1) (toNatBounded bv2)).
Qed.

Lemma toPosZ_addB3' w q r (bv1 bv2 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2) (2 ^ Z.of_nat w) ->
  toPosZ (bv1 + bv2) = r.
Proof.
  rewrite -addB_zeroExtend_low.
  exact: toPosZ_low_ext.
Qed.

Lemma toPosZ_adcB1 w (bv1 bv2 bv3 : BITS w) :
  toPosZ (low w ((zeroExtend w bv1 + zeroExtend w bv2) + zeroExtend w bv3))%bits =
  (toPosZ bv1 + toPosZ bv2 + toPosZ bv3)%Z.
Proof.
Admitted.

Lemma toPosZ_adcB2 w q r (bv1 bv2 bv3 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2 + toPosZ bv3) (2 ^ Z.of_nat w) ->
  toPosZ (high w ((zeroExtend w bv1 + zeroExtend w bv2)%bits + zeroExtend w bv3)) = q.
Proof.
Admitted.

Lemma toPosZ_adcB3 w q r (bv1 bv2 bv3 : BITS w) :
  (q, r) = Z.div_eucl (toPosZ bv1 + toPosZ bv2 + toPosZ bv3) (2 ^ Z.of_nat w) ->
  toPosZ (low w ((zeroExtend w bv1 + zeroExtend w bv2)%bits + zeroExtend w bv3)) = r.
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
  bvz_eq (eval_instr sb i) (zDSL.eval_program sz (bv2z_instr i)).
Proof.
  move=> Heq; case: i => /=.
  - (* bvAssign *)
    move=> v a _ x.
    apply: (bvz_eq_upd _ Heq).
    exact: bvz_eq_eval_atomic.
  - (* bvAdd *)
    move=> v a1 a2 Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_addB.
  - (* bvAddC *)
    move=> vh vl a1 a2 _ x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    set tmp :=
      Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                 (2 ^ Z.of_nat wordsize).
    have: tmp =
          Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                     (2 ^ Z.of_nat wordsize) by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_high_ext Hqr).
    + exact: (toPosZ_low_ext Hqr).
  - (* bvAdc *)
    move=> v a1 a2 c Hsafe. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq) -(Heq c).
    exact: toPosZ_adcB1.
  - (* bvAdcC *)
    move=> c v a1 a2 a _.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq) -(Heq a).
    set tmp :=
      Z.div_eucl
         (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb) +
          toPosZ (State.acc a sb)) (2 ^ Z.of_nat wordsize).
    have: tmp =
          Z.div_eucl
            (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb) +
             toPosZ (State.acc a sb)) (2 ^ Z.of_nat wordsize) by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_adcB2 Hqr).
    + exact: (toPosZ_adcB3 Hqr).
  - (* bvSub *)
    move=> v a1 a2 Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_subB1.
  - (* bvMul *)
    move=> v a1 a2 Hsafe x.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_mulB.
  - (* bvMulf *)
    move=> vh vl a1 a2 _ x.
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
  - (* bvShl *)
    move=> v a n Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a Heq).
    exact: toPosZ_shlBn.
  - (* bvSplit *)
    move=> vh vl a n _ x.
    rewrite -(bvz_eq_eval_atomic a Heq).
    set tmp := Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n)).
    have: tmp = Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n))
      by reflexivity.
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_shrBn1 Hqr).
    + exact: (toPosZ_shrBn2 Hqr).
  - (* bvConcatShl *)
    move=> vh vl a1 a2 n Hsafe x.
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
  bvz_eq (eval_program sb p) (zDSL.eval_program sz (bv2z_program p)).
Proof.
  elim: p sb sz => /=.
  - move=> sb sz Heq _; exact: Heq.
  - move=> hd tl IH sb sz Heq /andP [Hhd Htl].
    rewrite zDSL.eval_program_concat_step.
    apply: (IH _ _ _ Htl).
    exact: bvz_eq_eval_instr.
Qed.



(** Convert specifications. *)

Definition bv2z_unop (op : unop) : zDSL.unop :=
  match op with
  | bvNegOp => zDSL.zNeg
  end.

Definition bv2z_binop (op : binop) : zDSL.binop :=
  match op with
  | bvAddOp => zDSL.zAdd
  | bvSubOp => zDSL.zSub
  | bvMulOp => zDSL.zMul
  end.

Fixpoint bv2z_eexp (e : eexp) : zDSL.exp :=
  match e with
  | bveVar v => zVar v
  | bveConst c => zConst c
  | bveUnop op e => zUnop (bv2z_unop op) (bv2z_eexp e)
  | bveBinop op e1 e2 => zBinop (bv2z_binop op) (bv2z_eexp e1) (bv2z_eexp e2)
  end.

Fixpoint bv2z_ebexp e : zDSL.bexp :=
  match e with
  | bveTrue => zDSL.zTrue
  | bveEq e1 e2 => zDSL.zEq (bv2z_eexp e1) (bv2z_eexp e2)
  | bveEqMod e1 e2 p => zDSL.zEqMod (bv2z_eexp e1) (bv2z_eexp e2) (bv2z_eexp p)
  | bveAnd e1 e2 => zDSL.zAnd (bv2z_ebexp e1) (bv2z_ebexp e2)
  end.

Definition bv2z_spec_rng s : rspec :=
  {| rspre := rng_bexp (spre s);
     rsprog := sprog s;
     rspost := rng_bexp (spost s) |}.

Definition bv2z_spec_eqn s : zDSL.spec :=
  {| zDSL.spre := bv2z_ebexp (eqn_bexp (spre s));
     zDSL.sprog := bv2z_program (sprog s);
     zDSL.spost := bv2z_ebexp (eqn_bexp (spost s)) |}.

Definition bv2z_spec_safe sp :=
  forall s, eval_rbexp (rng_bexp (spre sp)) s ->
            bv2z_program_safe_at (sprog sp) s.



(** Properties of specification conversion. *)

Lemma bvz_eq_eval_eunop op (v : Z) :
  eval_eunop op v =
  zDSL.eval_unop (bv2z_unop op) v.
Proof.
  case: op; reflexivity.
Qed.

Lemma bvz_eq_eval_ebinop op (v1 v2 : Z) :
  eval_ebinop op v1 v2 =
  zDSL.eval_binop (bv2z_binop op) v1 v2.
Proof.
  case: op; reflexivity.
Qed.

Lemma bvz_eq_eval_eexp (e : eexp) bs zs :
  bvz_eq bs zs ->
  eval_eexp e bs = zDSL.eval_exp (bv2z_eexp e) zs.
Proof.
  elim: e => /=.
  - move=> a Heq. exact: Heq.
  - reflexivity.
  - move=> op e IH Heq. rewrite -(IH Heq). exact: bvz_eq_eval_eunop.
  - move=> op e1 IH1 e2 IH2 Heq. rewrite -(IH1 Heq) -(IH2 Heq).
    exact: bvz_eq_eval_ebinop.
Qed.

Lemma bvz_eq_eval_ebexp1 e bs zs :
  bvz_eq bs zs ->
  eval_ebexp e bs ->
  zDSL.eval_bexp (bv2z_ebexp e) zs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heq Heval.
    rewrite -(bvz_eq_eval_eexp e1 Heq) -(bvz_eq_eval_eexp e2 Heq). exact: Heval.
  - move=> e1 e2 p Heq Heval.
    rewrite -(bvz_eq_eval_eexp e1 Heq) -(bvz_eq_eval_eexp e2 Heq)
            -(bvz_eq_eval_eexp p Heq). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heq [Heval1 Heval2].
    split; [exact: (IH1 Heq Heval1) | exact: (IH2 Heq Heval2)].
Qed.

Lemma bvz_eq_eval_ebexp2 e bs zs :
  bvz_eq bs zs ->
  zDSL.eval_bexp (bv2z_ebexp e) zs ->
  eval_ebexp e bs.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Heq Heval.
    rewrite (bvz_eq_eval_eexp e1 Heq) (bvz_eq_eval_eexp e2 Heq). exact: Heval.
  - move=> e1 e2 p Heq Heval.
    rewrite (bvz_eq_eval_eexp e1 Heq) (bvz_eq_eval_eexp e2 Heq)
            (bvz_eq_eval_eexp p Heq). exact: Heval.
  - move=> e1 IH1 e2 IH2 Heq [Heval1 Heval2].
    split; [exact: (IH1 Heq Heval1) | exact: (IH2 Heq Heval2)].
Qed.

Lemma eval_bexp_combine e bs zs :
  bvz_eq bs zs ->
  eval_rbexp (rng_bexp e) bs ->
  zDSL.eval_bexp (bv2z_ebexp (eqn_bexp e)) zs ->
  eval_bexp e bs.
Proof.
  move=> Heq Her Hee. split.
  - exact: (bvz_eq_eval_ebexp2 Heq Hee).
  - exact: Her.
Qed.



(** Convert bvState to zState. *)

Definition bv2z_state bs : zDSL.State.t :=
  fun v => toPosZ (State.acc v bs).

Lemma bv2z_state_eq bs :
  bvz_eq bs (bv2z_state bs).
Proof.
  move=> x; reflexivity.
Qed.



(** Well-formedness *)

Module M2 := Map2 VS zDSL.VS.

Definition bv2z_vars vs : zDSL.VS.t :=
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
  VS.mem v vs = zDSL.VS.mem v (bv2z_vars vs).
Proof.
  rewrite (M2.map2_mem1 bv2z_vars_well).
  reflexivity.
Qed.

Lemma bv2z_vars_singleton v :
  zDSL.VS.Equal (zDSL.VS.singleton v) (bv2z_vars (VS.singleton v)).
Proof.
  done.
Qed.

Lemma bv2z_vars_add v vs :
  zDSL.VS.Equal (bv2z_vars (VS.add v vs)) (zDSL.VS.add v (bv2z_vars vs)).
Proof.
  rewrite /bv2z_vars (M2.map2_add bv2z_vars_well).
  reflexivity.
Qed.

Lemma bv2z_vars_add_singleton v1 v2 :
  zDSL.VS.Equal (zDSL.VS.add v1 (zDSL.VS.singleton v2))
                (bv2z_vars (VS.add v1 (VS.singleton v2))).
Proof.
  move=> x; split => Hin;
  move/zDSL.VSLemmas.memP: Hin => Hmem;
  apply/zDSL.VSLemmas.memP.
  - rewrite -bv2z_vars_mem.
    case: (zDSL.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
    + apply: VSLemmas.mem_add2; assumption.
    + apply: VSLemmas.mem_add3.
      rewrite bv2z_vars_mem; assumption.
  - rewrite -bv2z_vars_mem in Hmem.
    case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
    + apply: zDSL.VSLemmas.mem_add2; assumption.
    + apply: zDSL.VSLemmas.mem_add3; assumption.
Qed.

Lemma bv2z_vars_union vs1 vs2 :
  zDSL.VS.Equal (bv2z_vars (VS.union vs1 vs2))
                (zDSL.VS.union (bv2z_vars vs1) (bv2z_vars vs2)).
Proof.
  move=> x; split => Hin;
  move/zDSL.VSLemmas.memP: Hin => Hmem;
  apply/zDSL.VSLemmas.memP.
  - rewrite -bv2z_vars_mem in Hmem.
    case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
    rewrite bv2z_vars_mem in Hmem.
    + apply: zDSL.VSLemmas.mem_union2; assumption.
    + apply: zDSL.VSLemmas.mem_union3; assumption.
  - rewrite -bv2z_vars_mem.
    case: (zDSL.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
    rewrite -bv2z_vars_mem in Hmem.
    + apply: VSLemmas.mem_union2; assumption.
    + apply: VSLemmas.mem_union3; assumption.
Qed.

Lemma bv2z_vars_subset vs1 vs2 :
  zDSL.VS.subset (bv2z_vars vs1) (bv2z_vars vs2) = VS.subset vs1 vs2.
Proof.
  exact: (M2.map2_subset bv2z_vars_well).
Qed.

Lemma bv2z_vars_subset_atomic vs a :
  VS.subset (vars_atomic a) vs ->
  zDSL.VS.subset (zDSL.vars_exp (bv2z_atomic a)) (bv2z_vars vs).
Proof.
  case: a => /=.
  - move=> v Hsubset.
    move: (VSLemmas.subset_singleton1 Hsubset) => {Hsubset} Hmem.
    apply: zDSL.VSLemmas.subset_singleton2.
    rewrite -bv2z_vars_mem.
    exact: Hmem.
  - move=> _ _.
    exact: zDSL.VSLemmas.subset_empty.
Qed.

Lemma lvs_bv2z_instr i :
  zDSL.VS.Equal (zDSL.lvs_program (bv2z_instr i)) (bv2z_vars (lvs_instr i)).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- context f [zDSL.VS.union _ zDSL.VS.empty] =>
         rewrite zDSL.VSLemmas.union_emptyr; tac
       | |- zDSL.VS.Equal (zDSL.VS.singleton ?v) (bv2z_vars (VS.singleton ?v)) =>
         exact: bv2z_vars_singleton
       | |- zDSL.VS.Equal (zDSL.VS.add ?v1 (zDSL.VS.singleton ?v2))
                          (bv2z_vars (VS.add ?v1 (VS.singleton ?v2))) =>
         exact: bv2z_vars_add_singleton
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma vars_bv2z_atomic a :
  zDSL.VS.Equal (zDSL.vars_exp (bv2z_atomic a))
                (bv2z_vars (vars_atomic a)).
Proof.
  case: a => /=.
  - move=> v.
    exact: bv2z_vars_singleton.
  - reflexivity.
Qed.

Lemma vars_bv2z_instr i :
  zDSL.VS.Equal (zDSL.vars_program (bv2z_instr i))
                (bv2z_vars (vars_instr i)).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- context f [zDSL.VS.union _ zDSL.VS.empty] =>
         rewrite zDSL.VSLemmas.union_emptyr; tac
       | |- context f [bv2z_vars (VS.add _ _)] =>
         rewrite bv2z_vars_add; tac
       | |- context f [bv2z_vars (VS.union _ _)] =>
         rewrite bv2z_vars_union; tac
       | |- context f [bv2z_vars (vars_atomic _)] =>
         rewrite vars_bv2z_atomic; tac
       | |- zDSL.VS.Equal ?vs ?vs =>
         reflexivity
       | |- _ => idtac
       end in
   tac).
  - rewrite -zDSL.VSLemmas.add_union_singleton2 zDSL.VSLemmas.OP.P.add_add.
    reflexivity.
  - rewrite -zDSL.VSLemmas.add_union_singleton2.
    rewrite (zDSL.VSLemmas.OP.P.add_add _ t0 t1).
    rewrite (zDSL.VSLemmas.OP.P.add_add _ t1 t).
    reflexivity.
Qed.

Lemma vars_bv2z_program p :
  zDSL.VS.Equal (zDSL.vars_program (bv2z_program p))
                (bv2z_vars (vars_program p)).
Proof.
  elim: p => /=.
  - reflexivity.
  - move=> hd tl IH.
    rewrite bv2z_vars_union (zDSL.vars_program_concat) IH vars_bv2z_instr.
    reflexivity.
Qed.

Lemma bv2z_eexp_vars (e : eexp) :
  zDSL.VS.Equal (zDSL.vars_exp (bv2z_eexp e)) (bv2z_vars (vars_eexp e)).
Proof.
  elim: e => /=.
  - move=> a. exact: bv2z_vars_singleton.
  - reflexivity.
  - move=> _ e IH. rewrite IH. reflexivity.
  - move=> _ e1 IH1 e2 IH2. rewrite IH1 IH2 bv2z_vars_union. reflexivity.
Qed.

Lemma eqn_bexp_vars_subset f :
  zDSL.VS.subset (zDSL.vars_bexp (bv2z_ebexp (eqn_bexp f)))
                 (bv2z_vars (vars_bexp f)).
Proof.
  case: f => e r /=. rewrite bv2z_vars_union /=.
  apply: zDSL.VSLemmas.subset_union1 => {r}.
  elim: e => /=; intros;
  (let rec tac :=
       match goal with
       | |- is_true (zDSL.VS.subset zDSL.VS.empty _) =>
         exact: zDSL.VSLemmas.subset_empty
       | |- is_true (zDSL.VS.subset _ (bv2z_vars (VS.union _ _))) =>
         rewrite !bv2z_vars_union;
         repeat (apply: zDSL.VSLemmas.subset_union3);
         tac
       | |- is_true (zDSL.VS.subset
                       (zDSL.vars_exp (bv2z_eexp ?e))
                       (zDSL.VS.union (bv2z_vars (vars_eexp ?e)) _)) =>
         apply: zDSL.VSLemmas.subset_union1;
         rewrite bv2z_eexp_vars;
         exact: zDSL.VSLemmas.subset_refl
       | |- is_true (zDSL.VS.subset
                       (zDSL.vars_exp (bv2z_eexp ?e))
                       (zDSL.VS.union _ (bv2z_vars (vars_eexp ?e)))) =>
         apply: zDSL.VSLemmas.subset_union2;
         rewrite bv2z_eexp_vars;
         exact: zDSL.VSLemmas.subset_refl
       | |- is_true (zDSL.VS.subset
                       (zDSL.vars_exp (bv2z_eexp ?e))
                       (zDSL.VS.union _ (zDSL.VS.union _ _))) =>
         apply: zDSL.VSLemmas.subset_union2; tac
       | H : is_true (zDSL.VS.subset ?vs1 ?vs2) |-
         is_true (zDSL.VS.subset ?vs1 (zDSL.VS.union ?vs2 _)) =>
         apply: zDSL.VSLemmas.subset_union1;
         assumption
       | H : is_true (zDSL.VS.subset ?vs1 ?vs2) |-
         is_true (zDSL.VS.subset ?vs1 (zDSL.VS.union _ ?vs2)) =>
         apply: zDSL.VSLemmas.subset_union2;
         assumption
       | |- _ => idtac
       end in
  tac).
Qed.

Lemma bv2z_instr_well_formed vs i :
  well_formed_instr vs i ->
  zDSL.well_formed_program (bv2z_vars vs) (bv2z_instr i).
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
         is_true (zDSL.VS.subset
                    (zDSL.vars_exp (bv2z_atomic ?a)) (bv2z_vars ?vs)) =>
           by rewrite (bv2z_vars_subset_atomic H)
       | |- is_true (zDSL.VS.subset (zDSL.VS.union ?vs1 ?vs2) ?vs3) =>
         apply: zDSL.VSLemmas.subset_union3; tac
       | |- is_true (zDSL.VS.subset zDSL.VS.empty _) =>
         exact: zDSL.VSLemmas.subset_empty
       | H : is_true (?x != ?y) |- is_true (?x != ?y) => exact: H
       | |- is_true (zDSL.VS.subset (zDSL.VS.singleton _) _) =>
         apply: zDSL.VSLemmas.subset_singleton2; tac
       | H : is_true (VS.mem ?v ?vs) |-
         is_true (zDSL.VS.mem ?v (bv2z_vars ?vs)) =>
         by rewrite -bv2z_vars_mem
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_well_formed vs p :
  well_formed_program vs p ->
  zDSL.well_formed_program (bv2z_vars vs) (bv2z_program p).
Proof.
  elim: p vs => /=.
  - done.
  - move=> hd tl IH vs /andP [Hwellhd Hwelltl].
    rewrite zDSL.well_formed_program_concat.
    rewrite (bv2z_instr_well_formed Hwellhd) /=.
    apply: (@zDSL.well_formed_program_replace (bv2z_vars (VS.union vs (lvs_instr hd)))).
  - exact: (IH _ Hwelltl).
  - rewrite lvs_bv2z_instr -bv2z_vars_union.
    reflexivity.
Qed.

Lemma bv2z_spec_rng_well_formed vs sp :
  well_formed_spec vs sp ->
  well_formed_spec vs (bv2z_spec_rng sp).
Proof.
  destruct sp as [f p g]. move=> /andP /= [/andP [Hf Hp] Hg].
  rewrite /well_formed_spec /=. rewrite /vars_bexp /=.
  rewrite 2!VSLemmas.union_emptyl Hp.
  rewrite (VSLemmas.subset_trans (vars_rbexp_subset f) Hf).
  rewrite (VSLemmas.subset_trans (vars_rbexp_subset g) Hg).
  done.
Qed.

Lemma bv2z_spec_eqn_well_formed vs sp :
  well_formed_spec vs sp ->
  zDSL.well_formed_spec (bv2z_vars vs) (bv2z_spec_eqn sp).
Proof.
  destruct sp as [f p g].
  move=> /andP /= [/andP [Hf Hp] Hg].
  apply/andP => /=; split; first (apply/andP; split).
  - apply: (@zDSL.VSLemmas.subset_trans _ (bv2z_vars (vars_bexp f))).
    + exact: eqn_bexp_vars_subset.
    + rewrite bv2z_vars_subset; assumption.
  - exact: bv2z_program_well_formed.
  - apply: (zDSL.VSLemmas.subset_trans (eqn_bexp_vars_subset g)).
    rewrite vars_bv2z_program -bv2z_vars_union bv2z_vars_subset.
    assumption.
Qed.



(** Soundness *)

Theorem bv2z_spec_sound sp :
  bv2z_spec_safe sp ->
  valid_rspec (bv2z_spec_rng sp) ->
  zDSL.valid_spec (bv2z_spec_eqn sp) ->
  valid_spec sp.
Proof.
  destruct sp as [f p g] => /=.
  move=> Hsafe Hrng Heqn bs1 bs2 /= Hbf Hbp.
  move: (Hrng bs1 bs2 (eval_bexp_rng Hbf) Hbp) => {Hrng} /= Hrng.
  set zs1 := bv2z_state bs1.
  set zs2 := zDSL.eval_program zs1 (bv2z_program p).
  move: (Heqn zs1 zs2
              (bvz_eq_eval_ebexp1 (bv2z_state_eq bs1) (eval_bexp_eqn Hbf))
              (Logic.eq_refl zs2)) => {Heqn} /= Heqn.
  apply: (@eval_bexp_combine g bs2 zs2 _ Hrng Heqn). rewrite -Hbp.
  exact: (bvz_eq_eval_program (bv2z_state_eq bs1) (Hsafe _ (eval_bexp_rng Hbf))).
Qed.
