
(** * Conversion from MiniQhasm+ programs to sequential integer programs. *)

From Coq Require Import ZArith FMaps String OrderedType.
From Coq Require Import Program Program.Tactics.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
From Common Require Import Notations Tactics Arch Nats ZRing Types Env Var Store Bits.
From Qhasm Require Import IProg MiniQhasmPlusAMD64.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section Conversion.

  Variable E : SEnv.t.
  Notation pvar := SEnv.pvar.
  Notation pvar_var := SEnv.pvar_var.



  (** Conversions. *)

  (* The carry in the integer program. *)
  Definition icarry_var : var := SEnv.new_var E.

  (* The environment of the integer program. *)
  Definition E' : SEnv.t := SEnv.add icarry_var E.

  Definition icarry : pvar E'.
  Proof.
    exists icarry_var.
    apply: VS.mem_1.
    apply: VS.add_1.
    exact: eqxx.
  Defined.

  Definition z2p64 : IProg.exp E' := IConst E' (toZ (fromHex "10000000000000000")).

  Definition conv_pvar (x : pvar E) : pvar E'.
  Proof.
    elim: x.
    move=> x Hmem.
    exists x.
    move: (VS.mem_2 Hmem) => {Hmem} Hin.
    apply: VS.mem_1.
    move: (VS.add_2 icarry_var Hin).
    move=> H; exact: H.
  Defined.

  Lemma carry_var_neq :
    forall x : pvar E,
      icarry_var != pvar_var (conv_pvar x).
  Proof.
    move=> [] x Hx /=.
    apply/eqP => Hc.
    rewrite -Hc in Hx.
    move: (SEnv.new_var_is_new E) => Hne.
    apply: (negP Hne).
    exact: Hx.
  Qed.

  Lemma conv_pvar_eq :
    forall x y : pvar E,
      pvar_var x == pvar_var y ->
      pvar_var (conv_pvar x) == pvar_var (conv_pvar y).
  Proof.
    move=> x y.
    elim: y.
    elim: x.
    move=> /= x Hx y Hy Hxy.
    exact: Hxy.
  Qed.

  Lemma conv_pvar_neq :
    forall x y : pvar E,
      pvar_var x != pvar_var y ->
      pvar_var (conv_pvar x) != pvar_var (conv_pvar y).
  Proof.
    move=> x y.
    elim: y.
    elim: x.
    move=> /= x Hx y Hy Hxy.
    exact: Hxy.
  Qed.

  Definition conv_atomic (a : atomic E) : IProg.exp E' :=
    match a with
    | QVar v => IVar (conv_pvar v)
    | QConst n => IConst E' (toZ n)
    end.

  Definition conv_instr (i : instr E) : IProg.program E' :=
    match i with
    | QAssign r s =>
      [:: IAssign (conv_pvar r) (conv_atomic s) ]
    | QAdd r s t => [::] (* tbd *)
    | QAddC r s t => [::] (* tbd *)
    | QAdc r s t =>
      let sum := IBinop IAdd (conv_atomic s) (conv_atomic t) in
      [:: IAssign (conv_pvar r) (IBinop IMod sum z2p64);
        IAssign icarry (IBinop IDiv sum z2p64)]
    | QAdcC r s t => [::] (* tbd *)
    | QSub r s t => [::] (* tbd *)
    | QSubC r s t => [::] (* tbd *)
    | QSbb r s t => [::] (* tbd *)
    | QSbbC r s t => [::] (* tbd *)
    | QMul r s t => [::] (* tbd *)
    | QMulf r s t u => [::] (* tbd *)
    | QShl r s n => [::] (* tbd *)
    | QShr r s n => [::] (* tbd *)
    | QMod2n r s n => [::] (* tbd *)
    end.

  Fixpoint conv_program (p : program E) : IProg.program E' :=
    match p with
    | nil => [::]
    | hd::tl => conv_instr hd ++ conv_program tl
    end.

  Definition conv_unop (op : unop) : IProg.unop :=
    match op with
    | ONeg => INeg
    end.

  Definition conv_binop (op : binop) : IProg.binop :=
    match op with
    | OAdd => IAdd
    | OSub => ISub
    | OMul => IMul
    | ODiv => IDiv
    | OMod => IMod
    end.

  Fixpoint conv_exp (e : exp E) : IProg.exp E' :=
    match e with
    | EVar v => IVar (conv_pvar v)
    | EConst n => IConst E' n
    | ECarry => IVar icarry
    | EUnop op e' => IUnop (conv_unop op) (conv_exp e')
    | EBinop op e1 e2 => IBinop (conv_binop op) (conv_exp e1) (conv_exp e2)
    end.

  Definition conv_cop (op : cop) : IProg.cop :=
    match op with
    | CEq => IEq
    | CLt => ILt
    | CLe => ILe
    | CGt => IGt
    | CGe => IGe
    end.

  Fixpoint conv_bexp (e : bexp E) : IProg.bexp E' :=
    match e with
    | BComp op e1 e2 => IComp (conv_cop op) (conv_exp e1) (conv_exp e2)
    | BNot e' => INot (conv_bexp e')
    | BAnd e1 e2 => IAnd (conv_bexp e1) (conv_bexp e2)
    | BOr e1 e2 => IOr (conv_bexp e1) (conv_bexp e2)
    end.



  (** Relations between states. *)

  Definition veq (v1 : option value) (v2 : option IProg.value) : bool :=
    match v1, v2 with
    | Some n1, Some n2 => vtoZ n1 == n2
    | Some _, None => false
    | None, Some _ => false
    | None, None => true
    end.

  Definition ceq (c : bool) (v : option IProg.value) : bool :=
    match v with
    | Some n => toZ c == n
    | None => false
    end.

  Definition values_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    forall (x : pvar E),
      veq (State.acc (pvar_var x) qst) (IProg.State.acc (pvar_var (conv_pvar x)) ist).

  Definition carry_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    ceq (State.carry qst) (IProg.State.acc icarry_var ist).

  (* Program variables have the same values. *)
  Definition state_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    values_eqmod qst ist /\ carry_eqmod qst ist.

  Lemma state_eqmod_upd x n qst ist :
    state_eqmod qst ist ->
    state_eqmod (State.upd (pvar_var x) n qst) (IProg.State.upd (pvar_var (conv_pvar x)) (vtoZ n) ist).
  Proof.
    move=> [Heqv Heqc].
    split.
    - move=> y.
      case Hyx: (pvar_var y == pvar_var x).
      + move/idP: Hyx => Hyx.
        rewrite (State.acc_upd_eq _ qst Hyx).
        rewrite (IProg.State.acc_upd_eq _ ist (conv_pvar_eq Hyx)).
        exact: eqxx.
      + move/idP/negP: Hyx => Hyx.
        rewrite (State.acc_upd_neq _ qst Hyx).
        rewrite (IProg.State.acc_upd_neq _ ist (conv_pvar_neq Hyx)).
        exact: Heqv.
    - rewrite /carry_eqmod => /=.
      rewrite (IProg.State.acc_upd_neq _ ist (carry_var_neq x)).
      exact: Heqc.
  Qed.

  Lemma istate_eqmod_acc_some x n qst ist :
    state_eqmod qst ist ->
    State.acc (pvar_var x) qst = Some n ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some (vtoZ n).
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x). rewrite /veq Hq.
    case: (IProg.State.acc (pvar_var (conv_pvar x)) ist).
    - move=> m Hnm.
      rewrite (eqP Hnm); reflexivity.
    - discriminate.
  Qed.

  Lemma istate_eqmod_acc_none x qst ist :
    state_eqmod qst ist ->
    State.acc (pvar_var x) qst = None ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = None.
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x). rewrite /veq Hq.
    case: (IProg.State.acc (pvar_var (conv_pvar x)) ist).
    - discriminate.
    - reflexivity.
  Qed.

  Lemma qstate_eqmod_acc_some x n qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some n ->
    exists m, State.acc (pvar_var x) qst = Some m /\ vtoZ m == n.
  Proof.
    move=> [Heqv _] Hi.
    move: (Heqv x). rewrite /veq Hi.
    case Hq: (State.acc (pvar_var x) qst).
    - move=> Hn; rewrite -(eqP Hn).
      eexists; split.
      + reflexivity.
      + exact: eqxx.
    - discriminate.
  Qed.

  Lemma qstate_eqmod_acc_none x qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = None ->
    State.acc (pvar_var x) qst = None.
  Proof.
    move=> [Heqv _] Hi.
    move: (Heqv x). rewrite /veq Hi.
    case: (State.acc (pvar_var x) qst).
    - discriminate.
    - reflexivity.
  Qed.

  Lemma state_eqmod_acc x qst ist :
    state_eqmod qst ist ->
    (State.acc (pvar_var x) qst = None /\
     IProg.State.acc (pvar_var (conv_pvar x)) ist = None) \/
    (exists n m, State.acc (pvar_var x) qst = Some n /\
                 IProg.State.acc (pvar_var (conv_pvar x)) ist = Some m /\
                 vtoZ n == m).
  Proof.
    move=> Heqm.
    case Hqx: (State.acc (pvar_var x) qst).
    - right.
      eexists; eexists; split; [idtac | split].
      + reflexivity.
      + exact: (istate_eqmod_acc_some Heqm Hqx).
      + exact: eqxx.
    - left; split.
      + reflexivity.
      + exact: (istate_eqmod_acc_none Heqm Hqx).
  Qed.

  Lemma state_eqmod_carry qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var icarry) ist = Some (toZ (State.carry qst)).
  Proof.
    move=> [_ Heqc].
    rewrite /carry_eqmod /ceq in Heqc.
    move: Heqc.
    case: (IProg.State.acc icarry_var ist).
    - move=> c H.
      rewrite (eqP H).
      reflexivity.
    - discriminate.
  Qed.



  (** Properties of program conversion. *)

  Lemma istate_eqmod_qvar x qv qst ist:
    let a := QVar x in
    state_eqmod qst ist ->
    eval_atomic a qv qst ->
    IProg.eval_exp (conv_atomic a) (vtoZ qv) ist.
  Proof.
    move=> a Heqm Ha.
    inversion_clear Ha => /=.
    apply: EIVar.
    exact: (istate_eqmod_acc_some Heqm H).
  Qed.

  Lemma istate_eqmod_qconst n qv qst ist :
    let a := QConst E n in
    state_eqmod qst ist ->
    eval_atomic a qv qst ->
    IProg.eval_exp (conv_atomic a) (vtoZ qv) ist.
  Proof.
    move=> a Heqm Ha /=.
    inversion_clear Ha.
    exact: EIConst.
  Qed.

  Lemma istate_eqmod_atomic a qv qst ist :
    state_eqmod qst ist ->
    eval_atomic a qv qst ->
    IProg.eval_exp (conv_atomic a) (vtoZ qv) ist.
  Proof.
    elim: a qv qst ist.
    - (* QVar *)
      exact: istate_eqmod_qvar.
    - (* QConst *)
      exact: istate_eqmod_qconst.
  Qed.

  Lemma state_eqmod_qassign r s (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QAssign r s in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
    move=> i Heqm Hsafe Hi Hp.
    move: (Heqm) => [Heqv Heqc].
    inversion_clear Hi.
    rewrite /conv_instr /= in Hp.
    move: (IProg.eval_program_singleton Hp) => {Hp} Hp.
    inversion_clear Hp.
    move: (istate_eqmod_atomic Heqm H) => H1.
    move: (IProg.eval_exp_unique H0 H1) => Heq.
    rewrite (eqP Heq) => {H0 H1 Heq n}.
    exact: state_eqmod_upd.
  Qed.

  Lemma state_eqmod_qadd r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QAdd r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qaddc r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QAddC r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qadc r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QAdc r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
    move=> i Heqm Hsafe Hi Hp.
    inversion_clear Hi.
  Admitted.

  Lemma state_eqmod_qadcc r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QAdcC r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qsub r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QSub r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qsubc r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QSubC r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qsbb r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QSbb r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qsbbc r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QSbbC r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qmul r s t (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QMul r s t in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qmulf r s t u (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QMulf r s t u in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qshl r s n (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QShl r s n in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qshr r s n (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QShr r s n in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_qmod2n r s n (qst qst' : State.t) (ist ist' : IProg.State.t) :
    let i := QMod2n r s n in
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
  Admitted.

  Lemma state_eqmod_instr (i : instr E) (qst qst' : State.t) (ist ist' : IProg.State.t) :
    state_eqmod qst ist -> instr_safe i qst ->
    eval_instr qst i qst' -> IProg.eval_program ist (conv_instr i) ist' ->
    state_eqmod qst' ist'.
  Proof.
    elim: i qst qst' ist ist'.
    - (* QAssign *)
      exact: state_eqmod_qassign.
    - (* QAdd *)
      exact: state_eqmod_qadd.
    - (* QAddC *)
      exact: state_eqmod_qaddc.
    - (* QAdc *)
      exact: state_eqmod_qadc.
    - (* QAdcC *)
      exact: state_eqmod_qadcc.
    - (* QSub *)
      exact: state_eqmod_qsub.
    - (* QSubC *)
      exact: state_eqmod_qsubc.
    - (* QSbb *)
      exact: state_eqmod_qsbb.
    - (* QSbbC *)
      exact: state_eqmod_qsbbc.
    - (* QMul *)
      exact: state_eqmod_qmul.
    - (* QMulf *)
      exact: state_eqmod_qmulf.
    - (* QShl *)
      exact: state_eqmod_qshl.
    - (* QShr *)
      exact: state_eqmod_qshr.
    - (* QMod2n *)
      exact: state_eqmod_qmod2n.
  Qed.

  Lemma state_eqmod_program (p : program E) (qst qst' : State.t) (ist ist' : IProg.State.t) :
    state_eqmod qst ist -> program_safe p qst ->
    eval_program qst p qst' -> IProg.eval_program ist (conv_program p) ist' ->
    state_eqmod qst' ist'.
  Proof.
    elim: p qst qst' ist ist'.
    - move=> qst qst' ist ist' Heqm Hqs Hqe Hie.
      move: Heqm {Hqs}.
      move: (eval_program_empty Hqe) => {Hqe} Hqe.
      move: (IProg.eval_program_empty Hie) => {Hie} Hie.
      rewrite Hqe Hie.
      move=> H; exact: H.
    - move=> hd tl H qst qst' ist ist' Heqm Hqs Hqe Hie.
      move: (eval_program_cons Hqe) => {Hqe} [qst'' [Hqe Hqe'']].
      move: (IProg.eval_program_split Hie) => {Hie} [ist'' [Hie Hie'']].
      move: (program_safe_hd Hqs) => Hqs_hd.
      move: (state_eqmod_instr Heqm Hqs_hd Hqe Hie) => Heqm''.
      apply: (H _ _ _ _ Heqm'').
      + exact: (program_safe_tl Hqs Hqe).
      + exact: Hqe''.
      + exact: Hie''.
  Qed.



  (** Properties of expression conversion. *)

  Lemma istate_eqmod_evar x n (qst : State.t) (ist : IProg.State.t) :
    let e := EVar x in
    state_eqmod qst ist ->
    eval_exp e n qst ->
    IProg.eval_exp (conv_exp e) n ist.
  Proof.
    move=> e Heqm He /=.
    inversion_clear He.
    apply: EIVar.
    exact: (istate_eqmod_acc_some Heqm H).
  Qed.

  Lemma istate_eqmod_econst n m (qst : State.t) (ist : IProg.State.t) :
    let e := EConst E n in
    state_eqmod qst ist ->
    eval_exp e m qst ->
    IProg.eval_exp (conv_exp e) m ist.
  Proof.
    move=> e Heqm He /=.
    inversion_clear He.
    exact: EIConst.
  Qed.

  Lemma istate_eqmod_ecarry n (qst : State.t) (ist : IProg.State.t) :
    let e := ECarry E in
    state_eqmod qst ist ->
    eval_exp e n qst ->
    IProg.eval_exp (conv_exp e) n ist.
  Proof.
    move=> e Heqm He /=.
    inversion_clear He.
    apply: EIVar.
    exact: (state_eqmod_carry Heqm).
  Qed.

  Lemma istate_eqmod_eunop :
    forall (op : unop) (e : exp E),
      (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_exp e n qst -> IProg.eval_exp (conv_exp e) n ist) ->
      forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
        state_eqmod qst ist ->
        eval_exp (EUnop op e) n qst ->
        IProg.eval_exp (conv_exp (EUnop op e)) n ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_ebinop :
    forall (op : binop) (e1 : exp E),
      (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_exp e1 n qst -> IProg.eval_exp (conv_exp e1) n ist) ->
      forall e2 : exp E,
        (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            eval_exp e2 n qst -> IProg.eval_exp (conv_exp e2) n ist) ->
        forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_exp (EBinop op e1 e2) n qst ->
          IProg.eval_exp (conv_exp (EBinop op e1 e2)) n ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_exp e n (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist ->
    eval_exp e n qst ->
    IProg.eval_exp (conv_exp e) n ist.
  Proof.
    elim: e n qst ist.
    - exact: istate_eqmod_evar.
    - exact: istate_eqmod_econst.
    - exact: istate_eqmod_ecarry.
    - exact: istate_eqmod_eunop.
    - exact: istate_eqmod_ebinop.
  Qed.

  Lemma qstate_eqmod_evar x n (qst : State.t) (ist : IProg.State.t) :
    let e := EVar x in
    state_eqmod qst ist ->
    IProg.eval_exp (conv_exp e) n ist ->
    eval_exp e n qst.
  Proof.
    move=> e Heqm He /=.
    inversion_clear He.
    move: (qstate_eqmod_acc_some Heqm H) => [m [Hm Hmn]].
    rewrite -(eqP Hmn); apply: EEVar.
    exact: Hm.
  Qed.

  Lemma qstate_eqmod_econst n m (qst : State.t) (ist : IProg.State.t) :
    let e := EConst E n in
    state_eqmod qst ist ->
    IProg.eval_exp (conv_exp e) m ist ->
    eval_exp e m qst.
  Proof.
    move=> e Heqm He.
    have: n = m.
    - inversion_clear He.
      reflexivity.
    - move=> Hnm; inversion_clear He.
      rewrite -Hnm; exact: EEConst.
  Qed.

  Lemma qstate_eqmod_ecarry n (qst : State.t) (ist : IProg.State.t) :
    let e := ECarry E in
    state_eqmod qst ist ->
    IProg.eval_exp (conv_exp e) n ist ->
    eval_exp e n qst.
  Proof.
    move=> e Heqm He.
    inversion_clear He.
    rewrite (state_eqmod_carry Heqm) in H.
    case: H => H.
    rewrite -H.
    exact: EECarry.
  Qed.

  Lemma qstate_eqmod_eunop :
    forall (op : unop) (e : exp E),
      (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_exp (conv_exp e) n ist -> eval_exp e n qst) ->
      forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
        state_eqmod qst ist ->
        IProg.eval_exp (conv_exp (EUnop op e)) n ist ->
        eval_exp (EUnop op e) n qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_ebinop :
    forall (op : binop) (e1 : exp E),
      (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_exp (conv_exp e1) n ist -> eval_exp e1 n qst) ->
      forall e2 : exp E,
        (forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            IProg.eval_exp (conv_exp e2) n ist -> eval_exp e2 n qst) ->
        forall (n : IProg.value) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_exp (conv_exp (EBinop op e1 e2)) n ist ->
          eval_exp (EBinop op e1 e2) n qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_exp e n (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist ->
    IProg.eval_exp (conv_exp e) n ist ->
    eval_exp e n qst.
  Proof.
    elim: e n qst ist.
    - exact: qstate_eqmod_evar.
    - exact: qstate_eqmod_econst.
    - exact: qstate_eqmod_ecarry.
    - exact: qstate_eqmod_eunop.
    - exact: qstate_eqmod_ebinop.
  Qed.



  (** Properties of Boolean expression conversion. *)

  Lemma istate_eqmod_bcomp :
    forall (op : cop) (e1 e2 : exp E) (b : bool) (qst : State.t)
           (ist : IProg.State.t),
      state_eqmod qst ist ->
      eval_bexp (BComp op e1 e2) b qst ->
      IProg.eval_bexp (conv_bexp (BComp op e1 e2)) b ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_bnot :
    forall e : bexp E,
      (forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_bexp e b qst -> IProg.eval_bexp (conv_bexp e) b ist) ->
      forall (b : bool) (qst : State.t) (ist : IProg.State.t),
        state_eqmod qst ist ->
        eval_bexp (BNot e) b qst -> IProg.eval_bexp (conv_bexp (BNot e)) b ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_band :
    forall e1 : bexp E,
      (forall (b1 : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_bexp e1 b1 qst -> IProg.eval_bexp (conv_bexp e1) b1 ist) ->
      forall e2 : bexp E,
        (forall (b2 : bool) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            eval_bexp e2 b2 qst -> IProg.eval_bexp (conv_bexp e2) b2 ist) ->
        forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_bexp (BAnd e1 e2) b qst ->
          IProg.eval_bexp (conv_bexp (BAnd e1 e2)) b ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_bor :
    forall e1 : bexp E,
      (forall (b1 : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_bexp e1 b1 qst -> IProg.eval_bexp (conv_bexp e1) b1 ist) ->
      forall e2 : bexp E,
        (forall (b2 : bool) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            eval_bexp e2 b2 qst -> IProg.eval_bexp (conv_bexp e2) b2 ist) ->
        forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          eval_bexp (BOr e1 e2) b qst ->
          IProg.eval_bexp (conv_bexp (BOr e1 e2)) b ist.
  Proof.
  Admitted.

  Lemma istate_eqmod_bexp e b (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist ->
    eval_bexp e b qst ->
    IProg.eval_bexp (conv_bexp e) b ist.
  Proof.
    elim: e b qst ist.
    - exact: istate_eqmod_bcomp.
    - exact: istate_eqmod_bnot.
    - exact: istate_eqmod_band.
    - exact: istate_eqmod_bor.
  Qed.

  Lemma qstate_eqmod_bcomp :
    forall (op : cop) (e1 e2 : exp E) (b : bool) (qst : State.t)
           (ist : IProg.State.t),
      state_eqmod qst ist ->
      IProg.eval_bexp (conv_bexp (BComp op e1 e2)) b ist ->
      eval_bexp (BComp op e1 e2) b qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_bnot :
    forall e : bexp E,
      (forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_bexp (conv_bexp e) b ist -> eval_bexp e b qst) ->
      forall (b : bool) (qst : State.t) (ist : IProg.State.t),
        state_eqmod qst ist ->
        IProg.eval_bexp (conv_bexp (BNot e)) b ist -> eval_bexp (BNot e) b qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_band :
    forall e1 : bexp E,
      (forall (b1 : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_bexp (conv_bexp e1) b1 ist -> eval_bexp e1 b1 qst) ->
      forall e2 : bexp E,
        (forall (b2 : bool) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            IProg.eval_bexp (conv_bexp e2) b2 ist -> eval_bexp e2 b2 qst) ->
        forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_bexp (conv_bexp (BAnd e1 e2)) b ist ->
          eval_bexp (BAnd e1 e2) b qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_bor :
    forall e1 : bexp E,
      (forall (b1 : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_bexp (conv_bexp e1) b1 ist -> eval_bexp e1 b1 qst) ->
      forall e2 : bexp E,
        (forall (b2 : bool) (qst : State.t) (ist : IProg.State.t),
            state_eqmod qst ist ->
            IProg.eval_bexp (conv_bexp e2) b2 ist -> eval_bexp e2 b2 qst) ->
        forall (b : bool) (qst : State.t) (ist : IProg.State.t),
          state_eqmod qst ist ->
          IProg.eval_bexp (conv_bexp (BOr e1 e2)) b ist ->
          eval_bexp (BOr e1 e2) b qst.
  Proof.
  Admitted.

  Lemma qstate_eqmod_bexp e b (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist ->
    IProg.eval_bexp (conv_bexp e) b ist ->
    eval_bexp e b qst.
  Proof.
    elim: e b qst ist.
    - exact: qstate_eqmod_bcomp.
    - exact: qstate_eqmod_bnot.
    - exact: qstate_eqmod_band.
    - exact: qstate_eqmod_bor.
  Qed.



  (** State conversion. *)

  Definition conv_store (s : VStore.t value) : VStore.t IProg.value :=
    VStore.M.map (fun x => vtoZ x) s.

  Lemma conv_store_acc_some (x : pvar E) n s :
    VStore.acc (pvar_var x) s = Some n ->
    IProg.State.acc (pvar_var (conv_pvar x)) (conv_store s) = Some (vtoZ n).
  Proof.
    destruct x as [x Hmem] => Hx /=.
    exact: (VStore.L.find_some_map vtoZ Hx).
  Qed.

  Lemma conv_store_acc_none (x : pvar E) s :
    VStore.acc (pvar_var x) s = None ->
    IProg.State.acc (pvar_var (conv_pvar x)) (conv_store s) = None.
  Proof.
    destruct x as [x Hmem] => Hx /=.
    exact: (VStore.L.find_none_map vtoZ Hx).
  Qed.

  Definition conv_state (s : State.t) : IProg.State.t :=
    IProg.State.upd icarry_var (toZ (State.carry s)) (conv_store (State.store s)).

  Lemma conv_state_eqmod (s : State.t) :
    state_eqmod s (conv_state s).
  Proof.
    split.
    - rewrite /values_eqmod /conv_state /veq => x.
      move: (carry_var_neq x) => Hne.
      rewrite eq_sym in Hne.
      rewrite (IProg.State.acc_upd_neq _ _ Hne).
      case H: (State.acc (pvar_var x) s).
      + rewrite (conv_store_acc_some H).
        exact: eqxx.
      + rewrite (conv_store_acc_none H).
        exact: is_true_true.
    - rewrite /carry_eqmod /conv_state /ceq.
      rewrite (IProg.State.acc_upd_eq _ _ (eqxx icarry_var)).
      exact: eqxx.
  Qed.

  Lemma conv_state_qassign r s s1 s2 :
    let i := QAssign r s in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qadd r s t s1 s2 :
    let i := QAdd r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qadc r s t s1 s2 :
    let i := QAdc r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qsub r s t s1 s2 :
    let i := QSub r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qmul r s t s1 s2 :
    let i := QMul r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qshl r s n s1 s2 :
    let i := QShl r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qshr r s n s1 s2 :
    let i := QShr r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
  Admitted.

  Lemma conv_state_instr i s1 s2 :
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_state s1) (conv_instr i) (conv_state s2).
  Proof.
    elim: i s1 s2.
    - exact: conv_state_qassign.
    - exact: conv_state_qadd.
    - exact: conv_state_qaddc.
    - exact: conv_state_qadc.
    - exact: conv_state_qadcc.
    - exact: conv_state_qsub.
    - exact: conv_state_qsubc.
    - exact: conv_state_qsbb.
    - exact: conv_state_qsbbc.
    - exact: conv_state_qmul.
    - exact: conv_state_qmulf.
    - exact: conv_state_qshl.
    - exact: conv_state_qshr.
    - exact: conv_state_qmod2n.
  Qed.

  Lemma conv_state_program p s1 s2 :
    program_safe p s1 ->
    eval_program s1 p s2 ->
    IProg.eval_program (conv_state s1) (conv_program p) (conv_state s2).
  Proof.
    elim: p s1 s2.
    - move=> s1 s2 Hsafe Hp.
      move: (eval_program_empty Hp) => Hs.
      rewrite Hs.
      exact: IProg.EIEmpty.
    - move=> hd tl Hind s1 s2 Hsafe Hp.
      inversion_clear Hp.
      move: (conv_state_instr (program_safe_hd Hsafe) H) => Hhd.
      move: (Hind st2 s2 (program_safe_tl Hsafe H) H0) => Htl.
      apply: IProg.eval_program_concat.
      + exact: Hhd.
      + exact: Htl.
  Qed.

  Lemma qconv_state_exp e n s :
    IProg.eval_exp (conv_exp e) n (conv_state s) ->
    eval_exp e n s.
  Proof.
    move=> H.
    exact: (qstate_eqmod_exp (conv_state_eqmod s) H).
  Qed.

  Lemma qconv_state_bexp b s :
    (conv_state s |= conv_bexp b)%iprog ->
    (s |= b)%qhasm.
  Proof.
    move=> H.
    exact: (qstate_eqmod_bexp (conv_state_eqmod s) H).
  Qed.

  Lemma iconv_state_exp e n s :
    eval_exp e n s ->
    IProg.eval_exp (conv_exp e) n (conv_state s).
  Proof.
    move=> H.
    exact: (istate_eqmod_exp (conv_state_eqmod s) H).
  Qed.

  Lemma iconv_state_bexp b s :
    (s |= b)%qhasm ->
    (conv_state s |= conv_bexp b)%iprog.
  Proof.
    move=> H.
    exact: (istate_eqmod_bexp (conv_state_eqmod s) H).
  Qed.



  (** Specification preservation. *)

  Lemma qspec_preserved p f g :
    program_safe_under p f ->
    ({{ conv_bexp f }} conv_program p {{ conv_bexp g }})%iprog ->
    ({{ f }} p {{ g }})%qhasm.
  Proof.
    move=> Hsafe H s1 s2 Hf Hp.
    move: (conv_state_program (Hsafe s1 Hf) Hp) => {Hsafe Hp} Hip.
    move: (istate_eqmod_bexp (conv_state_eqmod s1) Hf) => {Hf} Hif.
    move: (H (conv_state s1) (conv_state s2) Hif Hip) => {H Hip Hif} Hig.
    exact: (qconv_state_bexp Hig).
  Qed.

  Lemma ispec_preserved p f g :
    program_safe_under p f ->
    ({{ f }} p {{ g }})%qhasm ->
    ({{ conv_bexp f }} conv_program p {{ conv_bexp g }})%iprog.
  Proof.
    move=> Hsafe H s1 s2 Hf Hp.
  Abort.

End Conversion.
