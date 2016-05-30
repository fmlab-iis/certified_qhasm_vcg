
(** * Conversion from MiniQhasm+ programs to sequential integer programs. *)

From Coq Require Import ZArith FMaps String OrderedType.
From Coq Require Import Program Program.Tactics.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
From CompCert Require Import Integers.
From Common Require Import Notations Tactics Nats ZRing Types Env Var Store Integers.
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

  Definition z2p64 : IProg.exp E' := IConst E' (two_power_nat 64).

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

  Lemma var_carry_neq :
    forall x : pvar E,
      pvar_var (conv_pvar x) != icarry_var.
  Proof.
    move=> x.
    apply/negP => Heq.
    move/negP: (carry_var_neq x); rewrite (eqP Heq).
    apply.
    exact: eqxx.
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

  Notation ivalue := Int64.unsigned.

  Definition conv_ocarry (c : option bool) : option IProg.value :=
    match c with
    | Some c' => Some (ctoZ c')
    | None => None
    end.

  Definition conv_ovalue (n : option value) : option IProg.value :=
    match n with
    | Some m => Some (ivalue m)
    | None => None
    end.

  Definition conv_atomic (a : atomic E) : IProg.exp E' :=
    match a with
    | QVar v => IVar (conv_pvar v)
    | QConst n => IConst E' (ivalue n)
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

  Definition values_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    forall (x : pvar E),
      conv_ovalue (State.acc (pvar_var x) qst) = (IProg.State.acc (pvar_var (conv_pvar x)) ist).

  Definition carry_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    conv_ocarry (State.carry qst) = (IProg.State.acc icarry_var ist).

  (* Program variables have the same values. *)
  Definition state_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    values_eqmod qst ist /\ carry_eqmod qst ist.

  Lemma state_eqmod_upd x n qst ist :
    state_eqmod qst ist ->
    state_eqmod (State.upd (pvar_var x) n qst) (IProg.State.upd (pvar_var (conv_pvar x)) (ivalue n) ist).
  Proof.
    move=> [Heqv Heqc].
    split.
    - move=> y.
      case Hyx: (pvar_var y == pvar_var x).
      + move/idP: Hyx => Hyx.
        rewrite (State.acc_upd_eq _ qst Hyx).
        rewrite (IProg.State.acc_upd_eq _ ist (conv_pvar_eq Hyx)).
        reflexivity.
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
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some (ivalue n).
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x). rewrite /conv_ovalue Hq => Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma istate_eqmod_acc_none x qst ist :
    state_eqmod qst ist ->
    State.acc (pvar_var x) qst = None ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = None.
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x) => /=. rewrite /conv_ovalue Hq => Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma qstate_eqmod_acc_some x n qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some n ->
    exists m, State.acc (pvar_var x) qst = Some m /\ ivalue m = n.
  Proof.
    move=> [Heqv _] Hi.
    move: (Heqv x). rewrite /conv_ovalue Hi.
    case Hq: (State.acc (pvar_var x) qst).
    - move=> [] Hn; rewrite -Hn.
      eexists; split.
      + reflexivity.
      + reflexivity.
    - discriminate.
  Qed.

  Lemma qstate_eqmod_acc_none x qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = None ->
    State.acc (pvar_var x) qst = None.
  Proof.
    move=> [Heqv _] Hi.
    move: (Heqv x). rewrite /conv_ovalue Hi.
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
                 ivalue n = m).
  Proof.
    move=> Heqm.
    case Hqx: (State.acc (pvar_var x) qst).
    - right.
      eexists; eexists; split; [idtac | split].
      + reflexivity.
      + exact: (istate_eqmod_acc_some Heqm Hqx).
      + reflexivity.
    - left; split.
      + reflexivity.
      + exact: (istate_eqmod_acc_none Heqm Hqx).
  Qed.

  Lemma istate_eqmod_carry_some qst ist qc :
    state_eqmod qst ist ->
    State.carry qst = Some qc ->
    exists ic,
      IProg.State.acc (pvar_var icarry) ist = Some ic /\ ctoZ qc = ic.
  Proof.
    move=> [_ Heqc] Hqc /=.
    rewrite /carry_eqmod /conv_ocarry in Heqc.
    rewrite Hqc in Heqc.
    rewrite -Heqc.
    by exists (ctoZ qc).
  Qed.

  Lemma istate_eqmod_carry_none qst ist :
    state_eqmod qst ist ->
    State.carry qst = None ->
    IProg.State.acc (pvar_var icarry) ist = None.
  Proof.
    move=> [_ Heqc] Hqc /=.
    rewrite /carry_eqmod /conv_ocarry in Heqc.
    rewrite Hqc in Heqc.
    by rewrite -Heqc.
  Qed.

  Lemma qstate_eqmod_carry_some qst ist ic :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var icarry) ist = Some ic ->
    exists qc,
      State.carry qst = Some qc /\ ctoZ qc = ic.
  Proof.
    move=> [_ Heqc] Hic /=.
    rewrite /carry_eqmod /conv_ocarry in Heqc.
    rewrite Hic in Heqc.
    move: Heqc.
    case: (State.carry qst).
    - move=> qc [] Hqi.
      by exists qc.
    - discriminate.
  Qed.

  Lemma qstate_eqmod_carry_none qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var icarry) ist = None ->
    State.carry qst = None.
  Proof.
    move=> [_ Heqc] Hic /=.
    rewrite /carry_eqmod /conv_ocarry in Heqc.
    rewrite Hic in Heqc.
    move: Heqc.
    case: (State.carry qst).
    - move=> qc; discriminate.
    - reflexivity.
  Qed.



  (** Properties of program conversion. *)

  Lemma istate_eqmod_qvar x qv qst ist:
    let a := QVar x in
    state_eqmod qst ist ->
    eval_atomic a qv qst ->
    IProg.eval_exp (conv_atomic a) (ivalue qv) ist.
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
    IProg.eval_exp (conv_atomic a) (ivalue qv) ist.
  Proof.
    move=> a Heqm Ha /=.
    inversion_clear Ha.
    exact: EIConst.
  Qed.

  Lemma istate_eqmod_qatomic a qv qst ist :
    state_eqmod qst ist ->
    eval_atomic a qv qst ->
    IProg.eval_exp (conv_atomic a) (ivalue qv) ist.
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
    move: (istate_eqmod_qatomic Heqm H) => H1.
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
    move: (istate_eqmod_carry_some Heqm H) => [ic [Hic HicZ]].
    rewrite Hic HicZ.
    reflexivity.
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
    rewrite -Hmn; apply: EEVar.
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
    move: (qstate_eqmod_carry_some Heqm H) => [qc [Hqc HqcZ]].
    rewrite -HqcZ.
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



  (** Conversion from State.t to IProg.State.t. *)

  Definition conv_qstore (s : VStore.t value) : VStore.t IProg.value :=
    VStore.M.map ivalue s.

  Lemma conv_qstore_acc (x : pvar E) s :
    conv_ovalue (VStore.acc (pvar_var x) s) =
    IProg.State.acc (pvar_var (conv_pvar x)) (conv_qstore s).
  Proof.
    destruct x as [x Hmem] => /=.
    rewrite /conv_ovalue /conv_qstore.
    case H: (VStore.acc x s).
    - rewrite /IProg.State.acc /VStore.acc (VStore.L.find_some_map ivalue H).
      reflexivity.
    - rewrite /IProg.State.acc /VStore.acc (VStore.L.find_none_map ivalue H).
      reflexivity.
  Qed.

  Definition conv_qcarry (c : option bool) (s : VStore.t IProg.value) :=
    match conv_ocarry c with
    | None => VStore.unset icarry_var s
    | Some n => VStore.upd icarry_var n s
    end.

  Lemma conv_qcarry_acc (x : pvar E) (c : option bool) s :
    IProg.State.acc (pvar_var (conv_pvar x)) (conv_qcarry c s) =
    IProg.State.acc (pvar_var (conv_pvar x)) s.
  Proof.
    rewrite /conv_qcarry /conv_ocarry.
    case: c.
    - move=> c.
      rewrite IProg.State.acc_upd_neq.
      + reflexivity.
      + exact: var_carry_neq.
    - rewrite IProg.State.acc_unset_neq.
      + reflexivity.
      + exact: var_carry_neq.
  Qed.

  Definition conv_qcarry_carry (c : option bool) s :
    IProg.State.acc icarry_var (conv_qcarry c s) = conv_ocarry c.
  Proof.
    rewrite /conv_qcarry.
    case: (conv_ocarry c).
    - move=> a; rewrite (IProg.State.acc_upd_eq _ _ (eqxx icarry_var)).
      reflexivity.
    - rewrite (IProg.State.acc_unset_eq _ (eqxx icarry_var)).
      reflexivity.
  Qed.

  Definition conv_qstate (s : State.t) : IProg.State.t :=
    conv_qcarry (State.carry s) (conv_qstore (State.store s)).

  Lemma conv_qstate_acc (x : pvar E) (s : State.t) :
    conv_ovalue (State.acc (pvar_var x) s) = IProg.State.acc (pvar_var (conv_pvar x)) (conv_qstate s).
  Proof.
    rewrite /conv_qstate.
    rewrite conv_qcarry_acc.
    rewrite conv_qstore_acc.
    reflexivity.
  Qed.

  Lemma conv_qstate_carry (s : State.t) :
    conv_ocarry (State.carry s) = IProg.State.acc icarry_var (conv_qstate s).
  Proof.
    rewrite /conv_qstate.
    rewrite conv_qcarry_carry.
    reflexivity.
  Qed.

  Lemma conv_qstate_eqmod (s : State.t) :
    state_eqmod s (conv_qstate s).
  Proof.
    split.
    - move=> x.
      exact: conv_qstate_acc.
    - exact: conv_qstate_carry.
  Qed.

  Lemma iconv_qstate_qassign r s s1 s2 :
    let i := QAssign r s in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qadd r s t s1 s2 :
    let i := QAdd r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qadc r s t s1 s2 :
    let i := QAdc r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qsub r s t s1 s2 :
    let i := QSub r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qmul r s t s1 s2 :
    let i := QMul r s t in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qshl r s n s1 s2 :
    let i := QShl r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qshr r s n s1 s2 :
    let i := QShr r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
  Admitted.

  Lemma iconv_qstate_instr i s1 s2 :
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
    elim: i s1 s2.
    - exact: iconv_qstate_qassign.
    - exact: iconv_qstate_qadd.
    - exact: iconv_qstate_qaddc.
    - exact: iconv_qstate_qadc.
    - exact: iconv_qstate_qadcc.
    - exact: iconv_qstate_qsub.
    - exact: iconv_qstate_qsubc.
    - exact: iconv_qstate_qsbb.
    - exact: iconv_qstate_qsbbc.
    - exact: iconv_qstate_qmul.
    - exact: iconv_qstate_qmulf.
    - exact: iconv_qstate_qshl.
    - exact: iconv_qstate_qshr.
    - exact: iconv_qstate_qmod2n.
  Qed.

  Lemma iconv_qstate_program p s1 s2 :
    program_safe p s1 ->
    eval_program s1 p s2 ->
    IProg.eval_program (conv_qstate s1) (conv_program p) (conv_qstate s2).
  Proof.
    elim: p s1 s2.
    - move=> s1 s2 Hsafe Hp.
      move: (eval_program_empty Hp) => Hs.
      rewrite Hs.
      exact: IProg.EIEmpty.
    - move=> hd tl Hind s1 s2 Hsafe Hp.
      inversion_clear Hp.
      move: (iconv_qstate_instr (program_safe_hd Hsafe) H) => Hhd.
      move: (Hind st2 s2 (program_safe_tl Hsafe H) H0) => Htl.
      apply: IProg.eval_program_concat.
      + exact: Hhd.
      + exact: Htl.
  Qed.

  Lemma qconv_qstate_exp e n s :
    IProg.eval_exp (conv_exp e) n (conv_qstate s) ->
    eval_exp e n s.
  Proof.
    move=> H.
    exact: (qstate_eqmod_exp (conv_qstate_eqmod s) H).
  Qed.

  Lemma qconv_qstate_bexp b s :
    (conv_qstate s |= conv_bexp b)%iprog ->
    (s |= b)%qhasm.
  Proof.
    move=> H.
    exact: (qstate_eqmod_bexp (conv_qstate_eqmod s) H).
  Qed.

  Lemma iconv_qstate_exp e n s :
    eval_exp e n s ->
    IProg.eval_exp (conv_exp e) n (conv_qstate s).
  Proof.
    move=> H.
    exact: (istate_eqmod_exp (conv_qstate_eqmod s) H).
  Qed.

  Lemma iconv_qstate_bexp b s :
    (s |= b)%qhasm ->
    (conv_qstate s |= conv_bexp b)%iprog.
  Proof.
    move=> H.
    exact: (istate_eqmod_bexp (conv_qstate_eqmod s) H).
  Qed.



  (** Specification preservation. *)

  Lemma qspec_preserved p f g :
    program_safe_under p f ->
    ({{ conv_bexp f }} conv_program p {{ conv_bexp g }})%iprog ->
    ({{ f }} p {{ g }})%qhasm.
  Proof.
    move=> Hsafe H s1 s2 Hf Hp.
    move: (iconv_qstate_program (Hsafe s1 Hf) Hp) => {Hsafe Hp} Hip.
    move: (istate_eqmod_bexp (conv_qstate_eqmod s1) Hf) => {Hf} Hif.
    move: (H (conv_qstate s1) (conv_qstate s2) Hif Hip) => {H Hip Hif} Hig.
    exact: (qconv_qstate_bexp Hig).
  Qed.



  (** Conversion from IProg.State.t. to State.t *)

  Definition qvalue := Int64.repr.

  Definition conv_istore (ist : IProg.State.t) : VStore.t value :=
    VStore.M.map qvalue ist.

  Definition conv_icarry (ist : IProg.State.t) : option bool :=
    match IProg.State.acc icarry_var ist with
    | None => None
    | Some b => Some (if b == 0%Z then false else true)
    end.

  Definition conv_istate (ist : IProg.State.t) : State.t :=
    {| State.store := conv_istore ist;
       State.carry := conv_icarry ist |}.

  Definition value_in_range n : Prop :=
    (0 <= n < two_power_nat 64)%Z.

  Definition values_in_range (ist : IProg.State.t) : Prop :=
    forall (x : pvar E) n,
      IProg.State.acc (pvar_var (conv_pvar x)) ist = Some n ->
      value_in_range n.

  Definition carry_in_range (ist : IProg.State.t) : Prop :=
    forall b,
      IProg.State.acc icarry_var ist = Some b ->
      b = 0%Z \/ b = 1%Z.

  Definition valid_istate (ist : IProg.State.t) : Prop :=
    values_in_range ist /\ carry_in_range ist.

  Lemma ivalue_in_range n :
    value_in_range (ivalue n).
  Proof.
    rewrite /value_in_range /ivalue.
    move: (Int64.intrange n) => [Hmin Hmax].
    split.
    - move: (Zlt_le_succ _ _ Hmin).
      by apply.
    - exact: Hmax.
  Qed.

  Lemma values_in_range_upd (x : pvar E) n ist :
    value_in_range n ->
    values_in_range ist ->
    values_in_range (IProg.State.upd (pvar_var (conv_pvar x)) n ist).
  Proof.
    move=> Hn Hr y m.
    case Hyx: (pvar_var (conv_pvar y) == pvar_var (conv_pvar x)).
    - rewrite (IProg.State.acc_upd_eq _ _ Hyx).
      case=> Hnm; rewrite -Hnm; exact: Hn.
    - move/idP/negP: Hyx => Hyx.
      rewrite (IProg.State.acc_upd_neq _ _ Hyx).
      move=> Hy.
      exact: (Hr _ _ Hy).
  Qed.

  Lemma carry_in_range_upd (x : pvar E) n ist :
    carry_in_range ist ->
    carry_in_range (IProg.State.upd (pvar_var (conv_pvar x)) n ist).
  Proof.
    move=> Hc b.
    rewrite (IProg.State.acc_upd_neq _ _ (carry_var_neq x)).
    move=> Hb.
    exact: (Hc _ Hb).
  Qed.

  Lemma valid_istate_upd (x : pvar E) n ist :
    value_in_range n ->
    valid_istate ist ->
    valid_istate (IProg.State.upd (pvar_var (conv_pvar x)) n ist).
  Proof.
    move=> Hrn [Hvs Hcs].
    split.
    - exact: (values_in_range_upd Hrn Hvs).
    - exact: (carry_in_range_upd Hcs).
  Qed.

  Lemma ivalueK (x : pvar E) n s :
    values_in_range s ->
    VStore.acc (pvar_var (conv_pvar x)) s = Some n ->
    ivalue (qvalue n) = n.
  Proof.
    move=> Hvr Hacc.
    move: (Hvr x n Hacc) => [Hmin Hmax].
    rewrite /ivalue /qvalue.
    apply: Int64.unsigned_repr.
    split.
    - exact: Hmin.
    - rewrite /Int64.max_unsigned /Int64.modulus.
      apply: Zlt_succ_le.
      exact: Hmax.
  Qed.

  Lemma conv_istore_acc (x : pvar E) s :
    valid_istate s ->
    conv_ovalue (VStore.acc (pvar_var x) (conv_istore s)) =
    VStore.acc (pvar_var (conv_pvar x)) s.
  Proof.
    move=> [Hvs Hcs].
    pose y := x.
    destruct x as [x Hmem] => /=.
    rewrite /conv_ovalue.
    case H: (VStore.acc x (conv_istore s)).
    - rewrite /VStore.acc /conv_istore in H.
      move: (VStore.L.find_map_some H) => {H} [i [Hi Hfind]].
      rewrite /VStore.acc Hfind Hi.
      have Hfind': VStore.M.find (pvar_var (conv_pvar y)) s = Some i by exact: Hfind.
      move: (ivalueK Hvs Hfind') => Heq; rewrite Heq.
      reflexivity.
    - rewrite /conv_istore in H.
      move: (VStore.L.find_map_none H).
      move=> Heq; rewrite /VStore.acc Heq.
      reflexivity.
  Qed.

  Lemma conv_istore_upd x n s :
    valid_istate s ->
    conv_istore (VStore.upd (pvar_var (conv_pvar x)) n s) =
    VStore.upd (pvar_var x) (qvalue n) (conv_istore s).
  Proof.
  Abort.

  Lemma conv_icarry_carry s :
    valid_istate s ->
    conv_ocarry (conv_icarry s) = IProg.State.acc icarry_var s.
  Proof.
    move=> [_ Hcs].
    rewrite /conv_ocarry /conv_icarry.
    case H: (IProg.State.acc icarry_var s).
    - move: (Hcs _ H).
      case => Heq; rewrite Heq /=; reflexivity.
    - reflexivity.
  Qed.

  Lemma conv_istate_acc (x : pvar E) s :
    valid_istate s ->
    conv_ovalue (State.acc (pvar_var x) (conv_istate s)) =
    IProg.State.acc (pvar_var (conv_pvar x)) s.
  Proof.
    move=> Hvs.
    exact: (conv_istore_acc _ Hvs).
  Qed.

  Lemma conv_istate_eqmod s :
    valid_istate s ->
    state_eqmod (conv_istate s) s.
  Proof.
    move=> Hvs; split.
    - move=> x.
      exact: conv_istate_acc.
    - rewrite /carry_eqmod /=.
      exact: conv_icarry_carry.
  Qed.

  Lemma valid_istate_qvar r n x s :
    let a := QVar r in
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) n s ->
    valid_istate (IProg.State.upd (pvar_var (conv_pvar x)) n s).
  Proof.
    move=> a Hv Ha.
    move: (Hv) => [Hvs _].
    inversion_clear Ha.
    move: (Hvs r n H) => {Hvs} Hrn.
    exact: (valid_istate_upd _ Hrn Hv).
  Qed.

  Lemma valid_istate_qconst n m x s :
    let a := QConst E n in
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) m s ->
    valid_istate (IProg.State.upd (pvar_var (conv_pvar x)) m s).
  Proof.
    move=> a Hv Ha.
    inversion_clear Ha.
    exact: (valid_istate_upd _ (ivalue_in_range n) Hv).
  Qed.

  Lemma valid_istate_qatomic a n x s :
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) n s ->
    valid_istate (IProg.State.upd (pvar_var (conv_pvar x)) n s).
  Proof.
    elim: a n x s.
    - exact: valid_istate_qvar.
    - exact: valid_istate_qconst.
  Qed.

  Lemma valid_istate_qassign r s s1 s2 :
    let i := QAssign r s in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
    move=> i Hvs1 Hi.
    inversion_clear Hi.
    rewrite (IProg.eval_program_empty H0) in H => {H0 s3}.
    inversion_clear H.
    exact: (valid_istate_qatomic _ Hvs1 H0).
  Qed.

  Lemma valid_istate_qadd r s t s1 s2 :
    let i := QAdd r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qadc r s t s1 s2 :
    let i := QAdc r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsub r s t s1 s2 :
    let i := QSub r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmul r s t s1 s2 :
    let i := QMul r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qshl r s n s1 s2 :
    let i := QShl r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qshr r s n s1 s2 :
    let i := QShr r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 -> valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_instr i s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
    elim: i s1 s2.
    - exact: valid_istate_qassign.
    - exact: valid_istate_qadd.
    - exact: valid_istate_qaddc.
    - exact: valid_istate_qadc.
    - exact: valid_istate_qadcc.
    - exact: valid_istate_qsub.
    - exact: valid_istate_qsubc.
    - exact: valid_istate_qsbb.
    - exact: valid_istate_qsbbc.
    - exact: valid_istate_qmul.
    - exact: valid_istate_qmulf.
    - exact: valid_istate_qshl.
    - exact: valid_istate_qshr.
    - exact: valid_istate_qmod2n.
  Qed.

  Lemma valid_istate_program p s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_program p) s2 ->
    valid_istate s2.
  Proof.
    elim: p s1 s2.
    - move=> s1 s2 Hvs1 Hp.
      rewrite -(IProg.eval_program_empty Hp).
      exact: Hvs1.
    - move => /= i p IH s1 s2 Hvs1 Hip.
      move: (IProg.eval_program_split Hip) => [s3 [Hi Hp]].
      apply: (IH s3 _ _ Hp).
      exact: (valid_istate_instr Hvs1 Hi).
  Qed.

  Lemma qconv_istate_qvar r n x s :
    let a := QVar r in
    IProg.eval_exp (conv_atomic a) n s ->
    conv_istate (IProg.State.upd (pvar_var (conv_pvar x)) n s) =
    State.upd (pvar_var x) (qvalue n) (conv_istate s).
  Proof.
  Abort.

  Lemma qconv_istate_qconst n m x s :
    let a := QConst E n in
    IProg.eval_exp (conv_atomic a) m s ->
    conv_istate (IProg.State.upd (pvar_var (conv_pvar x)) m s) =
    State.upd (pvar_var x) (qvalue m) (conv_istate s).
  Proof.
  Abort.

  Lemma qconv_istate_qatomic a n x s :
    IProg.eval_exp (conv_atomic a) n s ->
    conv_istate (IProg.State.upd (pvar_var (conv_pvar x)) n s) =
    State.upd (pvar_var x) (qvalue n) (conv_istate s).
  Proof.
    elim: a n x s.
  Abort.

  Lemma qconv_istate_qassign r s s1 s2 :
    let i := QAssign r s in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qadd r s t s1 s2 :
    let i := QAdd r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qadc r s t s1 s2 :
    let i := QAdc r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qsub r s t s1 s2 :
    let i := QSub r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qmul r s t s1 s2 :
    let i := QMul r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qshl r s n s1 s2 :
    let i := QShl r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qshr r s n s1 s2 :
    let i := QShr r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_instr i s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
    elim: i s1 s2.
  Abort.

  Lemma qconv_istate_program p s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_program p) s2 ->
    eval_program (conv_istate s1) p (conv_istate s2).
  Proof.
  Abort.

  Lemma qconv_istate_exp e n s :
        valid_istate s ->
    IProg.eval_exp (conv_exp e) n s ->
    eval_exp e n (conv_istate s).
  Proof.
    move=> Hvs H.
    exact: (qstate_eqmod_exp (conv_istate_eqmod Hvs) H).
  Qed.

  Lemma qconv_istate_bexp b s :
    valid_istate s ->
    (s |= conv_bexp b)%iprog ->
    (conv_istate s |= b)%qhasm.
  Proof.
    move=> Hvs H.
    exact: (qstate_eqmod_bexp (conv_istate_eqmod Hvs) H).
  Qed.

  Lemma qce_preserved p f g ist :
    valid_istate ist ->
    program_safe_under p f ->
    IProg.counterexample (conv_bexp f) (conv_program p) (conv_bexp g) ist ->
    counterexample f p g (conv_istate ist).
  Proof.
    move=> Hvs Hsafe [Hif [ist' [Hip Hig]]].
    split.
    - exact: (qconv_istate_bexp Hvs Hif).
    - exists (conv_istate ist'); split.
      +
      +
  Abort.


End Conversion.
