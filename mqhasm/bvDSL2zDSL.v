
From Coq Require Import Arith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Common Require Import Tactics Arch Types SsrOrdered Bits Lists FSets Bools Nats ZAriths Var Store.
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
  | bvAdc v a1 a2 y =>
    [:: zAssign v (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y))]
  | bvAdcC c v a1 a2 y =>
    [:: zSplit c v (zadd (zadd (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y)) wordsize]
  | bvSub v a1 a2 => [:: zAssign v (zsub (bv2z_atomic a1) (bv2z_atomic a2))]
  | bvSubC c v a1 a2 =>
    [:: zSplit c v
        (zsub (bv2z_atomic a1) (bv2z_atomic a2)) wordsize;
       zAssign c (zneg (zVar c))]
  | bvSbb v a1 a2 y =>
    [:: zAssign v (zsub (zsub (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y))]
  | bvSbbC c v a1 a2 y =>
    [:: zSplit c v
        (zsub (zsub (bv2z_atomic a1) (bv2z_atomic a2)) (zVar y)) wordsize;
       zAssign c (zneg (zVar c))]
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
  ~~ carry_addB bv1 bv2 && ~~ carry_addB (addB bv1 bv2) c.

Definition subB_safe w (bv1 bv2 : BITS w) : bool :=
  ~~ carry_subB bv1 bv2.

Definition sbbB_safe w (bv1 bv2 c : BITS w) : bool :=
  ~~ carry_subB bv1 bv2 && ~~ carry_subB (subB bv1 bv2) c.

Definition mulB_safe w (bv1 bv2 : BITS w) : bool :=
  high w (fullmulB bv1 bv2) == fromNat 0.

Definition shlBn_safe w (bv : BITS w) n : bool :=
  ltB bv (shlBn (@fromNat w 1) (w - n)).

Definition concatshl_safe w (bv : BITS w) n : bool :=
  (n <= w) && ltB bv (shlBn (@fromNat w 1) (w - n)).

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
  | bvSubC _ _ _ _ => true
  | bvSbb _ a1 a2 y => sbbB_safe (eval_atomic a1 s) (eval_atomic a2 s)
                                 (bv64DSL.State.acc y s)
  | bvSbbC _ _ _ _ _ => true
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

Lemma bvz_eq_upd2_aux c v bvc bvv zvc zvv zvt sb sz :
  bvz_eq sb sz ->
  toPosZ bvc = zvc ->
  toPosZ bvv = zvv ->
  bvz_eq (State.upd2 v bvv c bvc sb)
         (zDSL.State.upd c
                         zvc
                         (zDSL.State.upd2 v zvv c zvt sz)).
Proof.
  move=> Heq Hc Hv x.
  case Hxc: (x == c).
  - rewrite (zDSL.State.acc_upd_eq _ _ Hxc) (State.acc_upd2_eq2 _ _ _ _ Hxc).
    exact: Hc.
  - move/idP/negP: Hxc => Hxc. rewrite (zDSL.State.acc_upd_neq _ _ Hxc).
    case Hxv: (x == v).
    + rewrite (State.acc_upd2_eq1 _ _ _ Hxv Hxc).
      rewrite (zDSL.State.acc_upd2_eq1 _ _ _ Hxv Hxc). exact: Hv.
    + move/idP/negP: Hxv => Hxv.
      rewrite (State.acc_upd2_neq _ _ _ Hxv Hxc).
      rewrite (zDSL.State.acc_upd2_neq _ _ _ Hxv Hxc).
      exact: (Heq x).
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

Lemma bvz_eq_eval_instr i sb sz :
  bvz_eq sb sz ->
  bv2z_instr_safe_at i sb ->
  bvz_eq (eval_instr sb i) (zDSL.eval_program sz (bv2z_instr i)).
Proof.
  move=> Heq; case: i => /=.
  - (* bvAssign *)
    move=> v a _ x. apply: (bvz_eq_upd _ Heq). exact: bvz_eq_eval_atomic.
  - (* bvAdd *)
    move=> v a1 a2 Hsafe. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_addB_bounded.
  - (* bvAddC *)
    move=> vh vl a1 a2 _ x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    sethave tmp
            (Z.div_eucl (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb))
                 (2 ^ Z.of_nat wordsize)).
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_addB_zeroExtend_low Hqr).
    + exact: (toPosZ_addB_zeroExtend_high Hqr).
  - (* bvAdc *)
    move=> v a1 a2 c Hsafe. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq) -(Heq c).
    move: Hsafe => /andP [Hsafe1 Hsafe2].
    exact: toPosZ_addB3_bounded.
  - (* bvAdcC *)
    move=> c v a1 a2 a _.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq) -(Heq a).
    sethave tmp
            (Z.div_eucl
               (toPosZ (eval_atomic a1 sb) + toPosZ (eval_atomic a2 sb) +
                toPosZ (State.acc a sb)) (2 ^ Z.of_nat wordsize)).
    destruct tmp as [q r] => Hqr.
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_addB3_zeroExtend_low Hqr).
    + exact: (toPosZ_addB3_zeroExtend_high Hqr).
  - (* bvSub *)
    move=> v a1 a2 Hsafe.
    apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    exact: toPosZ_subB_bounded.
  - (* bvSubC *)
    move=> c v a1 a2 _.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    sethave temp (Z.div_eucl
                    (toPosZ (eval_atomic a1 sb) - toPosZ (eval_atomic a2 sb))
                    (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr.
    apply: (bvz_eq_upd2_aux _ _ _ Heq).
    + rewrite (zDSL.State.acc_upd2_eq2 _ _ _ _ (eqxx c)).
      exact: (toPosZ_subB_zeroExtend_high Hqr).
    + exact: (toPosZ_subB_zeroExtend_low Hqr).
  - (* bvSbb *)
    move=> v a1 a2 y Hsafe. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq)
            -(Heq y).
    move: Hsafe => /andP [Hsafe1 Hsafe2].
    exact: toPosZ_subB3_bounded.
  - (* bvSbbC *)
    move=> c v a1 a2 y _.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq)
            -(Heq y).
    sethave temp (Z.div_eucl
                    (toPosZ (eval_atomic a1 sb) - toPosZ (eval_atomic a2 sb) -
                     toPosZ (State.acc y sb)) (2 ^ Z.of_nat wordsize)).
    destruct temp as [q r] => Hqr.
    apply: (bvz_eq_upd2_aux _ _ _ Heq).
    + rewrite (zDSL.State.acc_upd2_eq2 _ _ _ _ (eqxx c)).
      exact: (toPosZ_subB3_zeroExtend_high Hqr).
    + exact: (toPosZ_subB3_zeroExtend_low Hqr).
  - (* bvMul *)
    move=> v a1 a2 Hsafe x. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    apply: toPosZ_mulB_bounded. rewrite -fromNat0. apply/eqP.
    exact: Hsafe.
  - (* bvMulf *)
    move=> vh vl a1 a2 _ x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    sethave tmp
            (Z.div_eucl (toPosZ (eval_atomic a1 sb) * toPosZ (eval_atomic a2 sb))
                        (2 ^ Z.of_nat wordsize)).
    destruct tmp as [q r] => Hqr. apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_fullmulB_low Hqr).
    + exact: (toPosZ_fullmulB_high Hqr).
  - (* bvShl *)
    move=> v a n Hsafe. apply: (bvz_eq_upd _ Heq).
    rewrite -(bvz_eq_eval_atomic a Heq). exact: toPosZ_shlBn_bounded.
  - (* bvSplit *)
    move=> vh vl a n _ x. rewrite -(bvz_eq_eval_atomic a Heq).
    sethave tmp (Z.div_eucl (toPosZ (eval_atomic a sb)) (2 ^ Z.of_nat (toNat n))).
    destruct tmp as [q r] => Hqr. apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_shrBn_low Hqr).
    + exact: (toPosZ_shrBn_high Hqr).
  - (* bvConcatShl *)
    move=> vh vl a1 a2 n Hsafe x.
    rewrite -(bvz_eq_eval_atomic a1 Heq) -(bvz_eq_eval_atomic a2 Heq).
    sethave tmp
            (Z.div_eucl
               (toPosZ (eval_atomic a1 sb) *
                2 ^ Z.of_nat wordsize +
                    toPosZ (eval_atomic a2 sb))
               (2 ^ Z.of_nat (wordsize - (toNat n)))).
    destruct tmp as [q r] => Hqr. move/andP: Hsafe => [Hle Hsafe].
    apply: (bvz_eq_upd2 _ _ Heq).
    + exact: (toPosZ_catB_shlBn_low_shrBn Hle Hsafe Hqr).
    + exact: (toPosZ_catB_shlBn_high Hle Hsafe Hqr).
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

Lemma lvs_bv2z_instr i :
  VS.Equal (zDSL.lvs_program (bv2z_instr i)) (lvs_instr i).
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | |- context f [VS.union _ VS.empty] =>
         rewrite zDSL.VSLemmas.union_emptyr; tac
       | |- VS.Equal ?s ?s => reflexivity
       | |- VS.Equal
              (VS.union
                 (VS.add ?v1 (VS.singleton ?v2))
                 (VS.singleton ?v1))
              (VS.add ?v1 (VS.singleton ?v2)) =>
         rewrite VSLemmas.union_add1 zDSL.VSLemmas.OP.P.union_sym
                 -VSLemmas.union_add1
                 (VSLemmas.add_equal
                    (VSLemmas.mem_singleton2 (eqxx v1)))
                 -VSLemmas.OP.P.add_union_singleton;
         reflexivity
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_atomic_vars a :
  VS.Equal (zDSL.vars_exp (bv2z_atomic a)) (vars_atomic a).
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma bv2z_eexp_vars (e : eexp) : VS.Equal (zDSL.vars_exp (bv2z_eexp e)) (vars_eexp e).
Proof.
  elim: e => /=.
  - reflexivity.
  - reflexivity.
  - move=> _ e IH. exact: IH.
  - move=> _ e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
Qed.

(* Convert (vars_* (bv2z_* _)) to (vars_* _). *)
Ltac vars_to_bvdsl :=
  match goal with
  | |- context f [VS.union _ VS.empty] =>
    rewrite VSLemmas.union_emptyr; vars_to_bvdsl
  | |- context f [vars_exp (bv2z_atomic _)] =>
    rewrite !bv2z_atomic_vars; vars_to_bvdsl
  | |- context f [vars_exp (bv2z_eexp _)] =>
    rewrite !bv2z_eexp_vars; vars_to_bvdsl
  | |- _ => idtac
  end.

Lemma vars_bv2z_instr i :
  VS.Equal (zDSL.vars_program (bv2z_instr i)) (vars_instr i).
Proof.
  case: i => /=; intros; vars_to_bvdsl; VSLemmas.dp_Equal.
Qed.

Lemma vars_bv2z_program p :
  VS.Equal (zDSL.vars_program (bv2z_program p)) (vars_program p).
Proof.
  elim: p => /=.
  - reflexivity.
  - move=> hd tl IH. rewrite (zDSL.vars_program_concat) IH vars_bv2z_instr.
    reflexivity.
Qed.

Lemma eqn_bexp_vars_subset f :
  VS.subset (zDSL.vars_bexp (bv2z_ebexp (eqn_bexp f))) (vars_bexp f).
Proof.
  case: f => e r /=. apply: VSLemmas.subset_union1 => /= {r}.
  elim: e => /=; intros; vars_to_bvdsl; VSLemmas.dp_subset.
Qed.

Lemma bv2z_instr_well_formed vs i :
  well_formed_instr vs i ->
  zDSL.well_formed_program vs (bv2z_instr i).
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
       | H : is_true (?x != ?y) |- is_true (?x != ?y) => exact: H
       | |- is_true (VS.subset _ _) => vars_to_bvdsl; VSLemmas.dp_subset
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma bv2z_program_well_formed vs p :
  well_formed_program vs p ->
  zDSL.well_formed_program vs (bv2z_program p).
Proof.
  elim: p vs => /=.
  - done.
  - move=> hd tl IH vs /andP [Hwellhd Hwelltl].
    rewrite zDSL.well_formed_program_concat.
    rewrite (bv2z_instr_well_formed Hwellhd) /=.
    apply: (@zDSL.well_formed_program_replace (VS.union vs (lvs_instr hd))).
  - exact: (IH _ Hwelltl).
  - rewrite lvs_bv2z_instr. reflexivity.
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
  zDSL.well_formed_spec vs (bv2z_spec_eqn sp).
Proof.
  destruct sp as [f p g].
  move=> /andP /= [/andP [Hf Hp] Hg].
  apply/andP => /=; split; first (apply/andP; split).
  - apply: (@VSLemmas.subset_trans _ (vars_bexp f) _ _ Hf).
    exact: eqn_bexp_vars_subset.
  - exact: bv2z_program_well_formed.
  - apply: (VSLemmas.subset_trans (eqn_bexp_vars_subset g)).
    rewrite vars_bv2z_program. assumption.
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
