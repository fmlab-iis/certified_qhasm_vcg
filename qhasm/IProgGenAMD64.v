
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

  Lemma conv_pvar_var (x : pvar E) :
    pvar_var (conv_pvar x) == pvar_var x.
  Proof.
    destruct x as [x Hmem] => /=.
    exact: eqxx.
  Qed.

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

  Definition conv_qcarry (c : option bool) : option IProg.value :=
    match c with
    | Some c' => Some (ctoZ c')
    | None => None
    end.

  Definition conv_qvalue (n : option value) : option IProg.value :=
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
      conv_qvalue (State.acc (pvar_var x) qst) = (IProg.State.acc (pvar_var (conv_pvar x)) ist).

  Definition carry_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    conv_qcarry (State.carry qst) = (IProg.State.acc icarry_var ist).

  (* Program variables have the same values. *)
  Definition state_eqmod (qst : State.t) (ist : IProg.State.t) : Prop :=
    values_eqmod qst ist /\ carry_eqmod qst ist.

  Lemma state_eqmod_values (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist -> values_eqmod qst ist.
  Proof.
    move=> [H _]; exact: H.
  Qed.

  Lemma state_eqmod_carry (qst : State.t) (ist : IProg.State.t) :
    state_eqmod qst ist -> carry_eqmod qst ist.
  Proof.
    move=> [_ H]; exact: H.
  Qed.

  Lemma state_eqmod_Upd x n qst1 qst2 ist1 ist2 :
    state_eqmod qst1 ist1 ->
    State.Upd (pvar_var x) n qst1 qst2 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) (ivalue n) ist1 ist2 ->
    state_eqmod qst2 ist2.
  Proof.
    move=> Heqm [Hqv Hqc] Hiv; split.
    - move=> y.
      rewrite Hqv Hiv.
      case Hyx: (pvar_var y == pvar_var x).
      + move/idP: Hyx => Hyx.
        rewrite (State.acc_upd_eq _ _ Hyx).
        rewrite (IProg.State.acc_upd_eq _ _ (conv_pvar_eq Hyx)).
        reflexivity.
      + move/idP/negP: Hyx => Hyx.
        rewrite (State.acc_upd_neq _ _ Hyx).
        rewrite (IProg.State.acc_upd_neq _ _ (conv_pvar_neq Hyx)).
        exact: (state_eqmod_values Heqm).
    - rewrite /carry_eqmod.
      rewrite -Hqc Hiv.
      rewrite (IProg.State.acc_upd_neq _ _ (carry_var_neq x)).
      exact: (state_eqmod_carry Heqm).
  Qed.

  Lemma state_eqmod_upd x n qst ist :
    state_eqmod qst ist ->
    state_eqmod (State.upd (pvar_var x) n qst) (IProg.State.upd (pvar_var (conv_pvar x)) (ivalue n) ist).
  Proof.
    move=> Heqm.
    exact: (state_eqmod_Upd Heqm
                            (State.Upd_upd (pvar_var x) n qst)
                            (IProg.State.Upd_upd (pvar_var (conv_pvar x)) (ivalue n) ist)).
  Qed.

  Lemma istate_eqmod_acc_some x n qst ist :
    state_eqmod qst ist ->
    State.acc (pvar_var x) qst = Some n ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some (ivalue n).
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x). rewrite /conv_qvalue Hq => Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma istate_eqmod_acc_none x qst ist :
    state_eqmod qst ist ->
    State.acc (pvar_var x) qst = None ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = None.
  Proof.
    move=> [Heqv _] Hq.
    move: (Heqv x) => /=. rewrite /conv_qvalue Hq => Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma qstate_eqmod_acc_some x n qst ist :
    state_eqmod qst ist ->
    IProg.State.acc (pvar_var (conv_pvar x)) ist = Some n ->
    exists m, State.acc (pvar_var x) qst = Some m /\ ivalue m = n.
  Proof.
    move=> [Heqv _] Hi.
    move: (Heqv x). rewrite /conv_qvalue Hi.
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
    move: (Heqv x). rewrite /conv_qvalue Hi.
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
    rewrite /carry_eqmod /conv_qcarry in Heqc.
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
    rewrite /carry_eqmod /conv_qcarry in Heqc.
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
    rewrite /carry_eqmod /conv_qcarry in Heqc.
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
    rewrite /carry_eqmod /conv_qcarry in Heqc.
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

  Lemma state_eqmod_qassign r s (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QAssign r s in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
    move=> i Heqm Hsafe Hi Hp.
    inversion_clear Hi.
    rewrite /conv_instr /= in Hp.
    move: (IProg.eval_program_singleton Hp) => {Hp} Hp.
    inversion_clear Hp.
    move: (istate_eqmod_qatomic Heqm H) => Hvs.
    move: (IProg.eval_exp_unique H1 Hvs) => Heq.
    apply: (state_eqmod_Upd Heqm).
    - exact: H0.
    - rewrite -(eqP Heq).
      exact: H2.
  Qed.

  Lemma state_eqmod_qadd r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QAdd r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qaddc r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QAddC r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qadc r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QAdc r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qadcc r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QAdcC r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qsub r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QSub r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qsubc r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QSubC r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qsbb r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QSbb r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qsbbc r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QSbbC r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qmul r s t (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QMul r s t in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qmulf r s t u (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QMulf r s t u in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qshl r s n (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QShl r s n in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qshr r s n (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QShr r s n in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_qmod2n r s n (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    let i := QMod2n r s n in
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
  Admitted.

  Lemma state_eqmod_instr (i : instr E) (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    state_eqmod qst1 ist1 -> instr_safe i qst1 ->
    eval_instr qst1 i qst2 -> IProg.eval_program ist1 (conv_instr i) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
    elim: i qst1 qst2 ist1 ist2.
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

  Lemma state_eqmod_program (p : program E) (qst1 qst2 : State.t) (ist1 ist2 : IProg.State.t) :
    state_eqmod qst1 ist1 -> program_safe p qst1 ->
    eval_program qst1 p qst2 -> IProg.eval_program ist1 (conv_program p) ist2 ->
    state_eqmod qst2 ist2.
  Proof.
    elim: p qst1 qst2 ist1 ist2.
    - move=> qst1 qst2 ist1 ist2 Heqm Hqs Hqe Hie.
      move: Heqm {Hqs}.
      move: (eval_program_empty Hqe) => {Hqe} Hqe.
      move: (IProg.eval_program_empty Hie) => {Hie} Hie.
      rewrite Hqe Hie.
      move=> H; exact: H.
    - move=> hd tl H qst1 qst2 ist1 ist2 Heqm Hqs Hqe Hie.
      move: (eval_program_cons Hqe) => {Hqe} [qst3 [Hqe Hqe3]].
      move: (IProg.eval_program_split Hie) => {Hie} [ist3 [Hie Hie3]].
      move: (program_safe_hd Hqs) => Hqs_hd.
      move: (state_eqmod_instr Heqm Hqs_hd Hqe Hie) => Heqm3.
      apply: (H _ _ _ _ Heqm3).
      + exact: (program_safe_tl Hqs Hqe).
      + exact: Hqe3.
      + exact: Hie3.
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

  Definition set_qcarry (c : option bool) (s : VStore.t IProg.value) :=
    match conv_qcarry c with
    | None => VStore.unset icarry_var s
    | Some n => VStore.upd icarry_var n s
    end.

  Definition conv_qstate (s : State.t) : IProg.State.t :=
    set_qcarry (State.carry s) (conv_qstore (State.store s)).

  Lemma conv_qstore_acc x s :
    conv_qvalue (VStore.acc x s) = IProg.State.acc x (conv_qstore s).
  Proof.
    rewrite /conv_qvalue /conv_qstore.
    case H: (VStore.acc x s).
    - rewrite /IProg.State.acc /VStore.acc (VStore.L.find_some_map ivalue H).
      reflexivity.
    - rewrite /IProg.State.acc /VStore.acc (VStore.L.find_none_map ivalue H).
      reflexivity.
  Qed.

  Lemma conv_qcarry_acc x (c : option bool) s :
    x != icarry_var ->
    IProg.State.acc x (set_qcarry c s) = IProg.State.acc x s.
  Proof.
    move=> Hne.
    rewrite /conv_qcarry /conv_qcarry.
    case: c.
    - move=> c.
      rewrite (IProg.State.acc_upd_neq _ _ Hne).
      reflexivity.
    - rewrite (IProg.State.acc_unset_neq _ Hne).
      reflexivity.
  Qed.

  Definition conv_qcarry_carry (c : option bool) s :
    IProg.State.acc icarry_var (set_qcarry c s) = conv_qcarry c.
  Proof.
    rewrite /set_qcarry.
    case: (conv_qcarry c).
    - move=> a; rewrite (IProg.State.acc_upd_eq _ _ (eqxx icarry_var)).
      reflexivity.
    - rewrite (IProg.State.acc_unset_eq _ (eqxx icarry_var)).
      reflexivity.
  Qed.

  Lemma conv_qstate_acc x (s : State.t) :
    x != icarry_var ->
    conv_qvalue (State.acc x s) = IProg.State.acc x (conv_qstate s).
  Proof.
    rewrite /conv_qstate => Hne.
    rewrite (conv_qcarry_acc _ _ Hne).
    rewrite conv_qstore_acc.
    reflexivity.
  Qed.

  Lemma conv_qstate_carry (s : State.t) :
    conv_qcarry (State.carry s) = IProg.State.acc icarry_var (conv_qstate s).
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
      move: (var_carry_neq x).
      destruct x as [x Hmem] => /= Hne.
      exact: (conv_qstate_acc _ Hne).
    - exact: conv_qstate_carry.
  Qed.

  Lemma conv_qstate_Upd x v qst1 qst2 :
    State.Upd (pvar_var x) v qst1 qst2 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) (ivalue v) (conv_qstate qst1) (conv_qstate qst2).
  Proof.
    move=> [Hqu Hqc].
    move=> y.
    case Hyc: (y == icarry_var).
    - rewrite (eqP Hyc).
      rewrite -conv_qstate_carry -Hqc.
      rewrite (IProg.State.acc_upd_neq _ _ (carry_var_neq x)).
      exact: conv_qstate_carry.
    - move/idP/negP: Hyc => Hyc.
      rewrite -(conv_qstate_acc _ Hyc) Hqu.
      case Hyx: (y == pvar_var (conv_pvar x)).
      + move/idP: Hyx => Hyx.
        rewrite (IProg.State.acc_upd_eq _ _ Hyx).
        rewrite (eqP (conv_pvar_var x)) in Hyx.
        rewrite (State.acc_upd_eq _ _ Hyx).
        reflexivity.
      + move/idP/negP: Hyx => Hyx.
        rewrite (IProg.State.acc_upd_neq _ _ Hyx).
        rewrite (eqP (conv_pvar_var x)) in Hyx.
        rewrite (State.acc_upd_neq _ _ Hyx).
        exact: (conv_qstate_acc _ Hyc).
  Qed.

  Lemma iconv_qstate_qassign r s s1 s2 :
    let i := QAssign r s in
    instr_safe i s1 ->
    eval_instr s1 i s2 ->
    IProg.eval_program (conv_qstate s1) (conv_instr i) (conv_qstate s2).
  Proof.
    move=> i Hsafe Hi /=.
    apply: (IProg.EICons (s2:=(conv_qstate s2))).
    - inversion_clear Hi.
      apply: EIAssign.
      + exact: (istate_eqmod_qatomic (conv_qstate_eqmod s1) H).
      + exact: (conv_qstate_Upd H0).
    - exact: IProg.EIEmpty.
  Qed.

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

  Lemma values_in_range_Upd x n ist1 ist2 :
    value_in_range n ->
    values_in_range ist1 ->
    IProg.State.Upd x n ist1 ist2 ->
    values_in_range ist2.
  Proof.
    move=> Hn Hr Hupd y m.
    rewrite (Hupd (pvar_var (conv_pvar y))).
    case Hyx: (pvar_var (conv_pvar y) == x).
    - rewrite (IProg.State.acc_upd_eq _ _ Hyx).
      case=> Hnm; rewrite -Hnm; exact: Hn.
    - move/idP/negP: Hyx => Hyx.
      rewrite (IProg.State.acc_upd_neq _ _ Hyx).
      move=> Hy.
      exact: (Hr _ _ Hy).
  Qed.

  Lemma values_in_range_upd x n ist :
    value_in_range n ->
    values_in_range ist ->
    values_in_range (IProg.State.upd x n ist).
  Proof.
    move=> Hn Hr.
    apply: (values_in_range_Upd Hn Hr).
    exact: IProg.State.Upd_upd.
  Qed.

  Lemma carry_in_range_Upd x n ist1 ist2 :
    x != icarry_var ->
    carry_in_range ist1 ->
    IProg.State.Upd x n ist1 ist2 ->
    carry_in_range ist2.
  Proof.
    move=> Hne Hc Hupd b.
    rewrite (Hupd icarry_var).
    rewrite IProg.State.acc_upd_neq.
    - move=> Hb.
      exact: (Hc _ Hb).
    - apply/idP/negP.
      move/idP/negP: Hne.
      move=> Hne Heq; apply: Hne.
      rewrite eq_sym.
      exact: Heq.
  Qed.

  Lemma carry_in_range_upd x n ist :
    x != icarry_var ->
    carry_in_range ist ->
    carry_in_range (IProg.State.upd x n ist).
  Proof.
    move=> Hne Hc.
    apply: (carry_in_range_Upd Hne Hc).
    exact: IProg.State.Upd_upd.
  Qed.

  Lemma valid_istate_Upd x n ist1 ist2 :
    x != icarry_var ->
    value_in_range n ->
    valid_istate ist1 ->
    IProg.State.Upd x n ist1 ist2 ->
    valid_istate ist2.
  Proof.
    move=> Hne Hrn [Hv1 Hc1] Hupd.
    split.
    - exact: (values_in_range_Upd Hrn Hv1 Hupd).
    - exact: (carry_in_range_Upd Hne Hc1 Hupd).
  Qed.

  Lemma valid_istate_Upd_pvar (x : pvar E) n ist1 ist2 :
    value_in_range n ->
    valid_istate ist1 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) n ist1 ist2 ->
    valid_istate ist2.
  Proof.
    move=> Hrn Hvs Hupd.
    apply: (valid_istate_Upd _ Hrn Hvs Hupd).
    exact: var_carry_neq.
  Qed.

  Lemma valid_istate_upd x n ist :
    x != icarry_var ->
    value_in_range n ->
    valid_istate ist ->
    valid_istate (IProg.State.upd x n ist).
  Proof.
    move=> Hne Hvn Hv.
    apply: (valid_istate_Upd Hne Hvn Hv).
    exact: IProg.State.Upd_upd.
  Qed.

  Lemma valid_istate_upd_pvar (x : pvar E) n ist :
    value_in_range n ->
    valid_istate ist ->
    valid_istate (IProg.State.upd (pvar_var (conv_pvar x)) n ist).
  Proof.
    apply: valid_istate_upd.
    exact: var_carry_neq.
  Qed.

  Lemma ivalueK (n : IProg.value) :
    value_in_range n ->
    ivalue (qvalue n) = n.
  Proof.
    move=> [Hmin Hmax].
    rewrite /ivalue /qvalue.
    apply: Int64.unsigned_repr.
    split.
    - exact: Hmin.
    - rewrite /Int64.max_unsigned /Int64.modulus.
      apply: Zlt_succ_le.
      exact: Hmax.
  Qed.

  Lemma qvalueK (n : value) :
    qvalue (ivalue n) = n.
  Proof.
    rewrite /qvalue /ivalue.
    exact: Int64.repr_unsigned.
  Qed.

  Definition conv_ivalue (n : option IProg.value) : option value :=
    match n with
    | None => None
    | Some m => Some (qvalue m)
    end.

  Lemma conv_ivalueK n :
    conv_ivalue (conv_qvalue n) = n.
  Proof.
    case: n => /=.
    - move=> n; rewrite qvalueK.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma conv_qvalueK_some n :
    value_in_range n ->
    conv_qvalue (conv_ivalue (Some n)) = Some n.
  Proof.
    move=> Hr /=.
    rewrite (ivalueK Hr).
    reflexivity.
  Qed.

  Lemma conv_qvalueK_none :
    conv_qvalue (conv_ivalue None) = None.
  Proof.
    reflexivity.
  Qed.

  Lemma conv_istore_acc_i x s :
    VStore.acc x (conv_istore s) = conv_ivalue (VStore.acc x s).
  Proof.
    rewrite /VStore.acc /conv_istore.
    case H: (VStore.M.find x s).
    - rewrite (VStore.L.find_some_map _ H).
      reflexivity.
    - rewrite (VStore.L.find_none_map _ H).
      reflexivity.
  Qed.

  Lemma conv_istore_acc_some_q x n s :
    VStore.acc x s = Some n ->
    value_in_range n ->
    conv_qvalue (VStore.acc x (conv_istore s)) = Some n.
  Proof.
    move=> Hacc Hr.
    rewrite conv_istore_acc_i Hacc.
    exact: conv_qvalueK_some.
  Qed.

  Lemma conv_istore_acc_none_q x s :
    VStore.acc x s = None ->
    conv_qvalue (VStore.acc x (conv_istore s)) = None.
  Proof.
    move=> Hacc.
    rewrite conv_istore_acc_i Hacc.
    exact: conv_qvalueK_none.
  Qed.

  Lemma conv_istore_acc_q x s :
    (forall n, VStore.acc x s = Some n -> value_in_range n) ->
    conv_qvalue (VStore.acc x (conv_istore s)) = VStore.acc x s.
  Proof.
    case H: (VStore.acc x s).
    - move=> Hn.
      apply: conv_istore_acc_some_q.
      + rewrite H; reflexivity.
      + apply: Hn.
        reflexivity.
    - rewrite (conv_istore_acc_none_q H).
      reflexivity.
  Qed.

  Lemma conv_istore_Upd x n s1 s2 :
    VStore.Upd x n s1 s2 ->
    VStore.Upd x (qvalue n) (conv_istore s1) (conv_istore s2).
  Proof.
    move=> Hiupd y.
    rewrite conv_istore_acc_i.
    rewrite (Hiupd y).
    case Hyx: (y == x).
    - move/idP: Hyx => Hyx.
      rewrite 2!(VStore.acc_upd_eq _ _ Hyx).
      reflexivity.
    - move/idP/negP: Hyx => Hyx.
      rewrite 2!(VStore.acc_upd_neq _ _ Hyx).
      rewrite conv_istore_acc_i.
      reflexivity.
  Qed.

  Lemma conv_icarry_carry s :
    valid_istate s ->
    conv_qcarry (conv_icarry s) = IProg.State.acc icarry_var s.
  Proof.
    move=> [_ Hcs].
    rewrite /conv_qcarry /conv_icarry.
    case H: (IProg.State.acc icarry_var s).
    - move: (Hcs _ H).
      case => Heq; rewrite Heq /=; reflexivity.
    - reflexivity.
  Qed.

  Lemma conv_istate_acc_q (x : pvar E) s :
    valid_istate s ->
    conv_qvalue (State.acc (pvar_var x) (conv_istate s)) =
    IProg.State.acc (pvar_var (conv_pvar x)) s.
  Proof.
    move=> [Hvs _].
    move: (Hvs x) => {Hvs}.
    destruct x as [x Hmem] => /=.
    exact: conv_istore_acc_q.
  Qed.

  Lemma conv_istate_acc_i (x : pvar E) s :
    valid_istate s ->
    State.acc (pvar_var x) (conv_istate s) =
    conv_ivalue (IProg.State.acc (pvar_var (conv_pvar x)) s).
  Proof.
    move=> Hvs.
    rewrite -(conv_istate_acc_q _ Hvs).
    rewrite conv_ivalueK.
    reflexivity.
  Qed.

  Lemma conv_istate_Upd (x : pvar E) n s1 s2 :
    IProg.State.Upd (pvar_var (conv_pvar x)) n s1 s2 ->
    State.Upd (pvar_var x) (qvalue n) (conv_istate s1) (conv_istate s2).
  Proof.
    move=> Hupd; split => /=.
    - apply: conv_istore_Upd.
      destruct x as [x Hmem]; rewrite /= in Hupd *.
      exact: Hupd.
    - rewrite /conv_icarry.
      case Hc: (IProg.State.acc icarry_var s1).
      + rewrite (IProg.State.acc_Upd_neq (carry_var_neq x) Hupd).
        rewrite Hc.
        reflexivity.
      + rewrite (IProg.State.acc_Upd_neq (carry_var_neq x) Hupd).
        rewrite Hc.
        reflexivity.
  Qed.

  Lemma conv_istate_eqmod s :
    valid_istate s ->
    state_eqmod (conv_istate s) s.
  Proof.
    move=> Hvs; split.
    - move=> x.
      exact: conv_istate_acc_q.
    - rewrite /carry_eqmod /=.
      exact: conv_icarry_carry.
  Qed.

  Lemma valid_istate_qvar r n x s1 s2 :
    let a := QVar r in
    valid_istate s1 ->
    IProg.eval_exp (conv_atomic a) n s1 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) n s1 s2 ->
    valid_istate s2.
  Proof.
    move=> a Hv Ha Hupd.
    apply: (valid_istate_Upd_pvar _ Hv Hupd).
    move: Hv => [Hv _].
    inversion_clear Ha.
    exact: (Hv r n H).
  Qed.

  Lemma valid_istate_qconst n m x s1 s2 :
    let a := QConst E n in
    valid_istate s1 ->
    IProg.eval_exp (conv_atomic a) m s1 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) m s1 s2 ->
    valid_istate s2.
  Proof.
    move=> a Hv Ha Hupd.
    apply: (valid_istate_Upd_pvar _ Hv Hupd).
    inversion_clear Ha.
    exact: ivalue_in_range.
  Qed.

  Lemma valid_istate_qatomic a n x s1 s2 :
    valid_istate s1 ->
    IProg.eval_exp (conv_atomic a) n s1 ->
    IProg.State.Upd (pvar_var (conv_pvar x)) n s1 s2 ->
    valid_istate s2.
  Proof.
    elim: a n x s1 s2.
    - exact: valid_istate_qvar.
    - exact: valid_istate_qconst.
  Qed.

  Lemma valid_istate_qassign r s s1 s2 :
    let i := QAssign r s in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
    move=> i Hvs1 Hi.
    inversion_clear Hi.
    rewrite (IProg.eval_program_empty H0) in H => {H0 s3}.
    inversion_clear H.
    exact: (valid_istate_qatomic Hvs1 H0 H1).
  Qed.

  Lemma valid_istate_qadd r s t s1 s2 :
    let i := QAdd r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qadc r s t s1 s2 :
    let i := QAdc r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsub r s t s1 s2 :
    let i := QSub r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmul r s t s1 s2 :
    let i := QMul r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qshl r s n s1 s2 :
    let i := QShl r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qshr r s n s1 s2 :
    let i := QShr r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
  Proof.
  Admitted.

  Lemma valid_istate_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    valid_istate s2.
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

  Lemma qconv_istate_qvar n s x :
    let a := QVar x in
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) n s ->
    eval_atomic a (qvalue n) (conv_istate s).
  Proof.
    move=> a Hvs Ha.
    inversion_clear Ha.
    apply: EQVar.
    rewrite (conv_istate_acc_i _ Hvs).
    rewrite H.
    reflexivity.
  Qed.

  Lemma qconv_istate_qconst n s m :
    let a := QConst E m in
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) n s ->
    eval_atomic a (qvalue n) (conv_istate s).
  Proof.
    move=> a _ Ha.
    inversion_clear Ha.
    rewrite qvalueK.
    exact: EQConst.
  Qed.

  Lemma qconv_istate_qatomic a n s :
    valid_istate s ->
    IProg.eval_exp (conv_atomic a) n s ->
    eval_atomic a (qvalue n) (conv_istate s).
  Proof.
    elim: a.
    - exact: qconv_istate_qvar.
    - exact: qconv_istate_qconst.
  Qed.

  Lemma qconv_istate_qassign r s s1 s2 :
    let i := QAssign r s in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
    move=> i Hv1 Hi.
    inversion_clear Hi.
    rewrite (IProg.eval_program_empty H0) in H => {H0 s3}.
    inversion_clear H.
    apply: EQAssign.
    - exact: (qconv_istate_qatomic Hv1 H0).
    - exact: conv_istate_Upd.
  Qed.

  Lemma qconv_istate_qadd r s t s1 s2 :
    let i := QAdd r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qaddc r s t s1 s2 :
    let i := QAddC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qadc r s t s1 s2 :
    let i := QAdc r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qadcc r s t s1 s2 :
    let i := QAdcC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qsub r s t s1 s2 :
    let i := QSub r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qsubc r s t s1 s2 :
    let i := QSubC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qsbb r s t s1 s2 :
    let i := QSbb r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qsbbc r s t s1 s2 :
    let i := QSbbC r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qmul r s t s1 s2 :
    let i := QMul r s t in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qmulf r s t u s1 s2 :
    let i := QMulf r s t u in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qshl r s n s1 s2 :
    let i := QShl r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qshr r s n s1 s2 :
    let i := QShr r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_qmod2n r s n s1 s2 :
    let i := QMod2n r s n in
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
  Admitted.

  Lemma qconv_istate_instr i s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_instr i) s2 ->
    eval_instr (conv_istate s1) i (conv_istate s2).
  Proof.
    elim: i s1 s2.
    - exact: qconv_istate_qassign.
    - exact: qconv_istate_qadd.
    - exact: qconv_istate_qaddc.
    - exact: qconv_istate_qadc.
    - exact: qconv_istate_qadcc.
    - exact: qconv_istate_qsub.
    - exact: qconv_istate_qsubc.
    - exact: qconv_istate_qsbb.
    - exact: qconv_istate_qsbbc.
    - exact: qconv_istate_qmul.
    - exact: qconv_istate_qmulf.
    - exact: qconv_istate_qshl.
    - exact: qconv_istate_qshr.
    - exact: qconv_istate_qmod2n.
  Qed.

  Lemma qconv_istate_program p s1 s2 :
    valid_istate s1 ->
    IProg.eval_program s1 (conv_program p) s2 ->
    eval_program (conv_istate s1) p (conv_istate s2).
  Proof.
    elim: p s1 s2 => /=.
    - move=> s1 s2 Hv1 Hp.
      rewrite (IProg.eval_program_empty Hp).
      exact: EQEmpty.
    - move=> i p IH s1 s2 Hv1 Hp.
      move: (IProg.eval_program_split Hp) => [s3 [H12 H32]].
      apply: EQCons.
      + exact: (qconv_istate_instr Hv1 H12).
      + apply: (IH _ _ _ H32).
        exact: (valid_istate_instr Hv1 H12).
  Qed.

  Lemma qconv_istate_exp e n s :
        valid_istate s ->
    IProg.eval_exp (conv_exp e) n s ->
    eval_exp e n (conv_istate s).
  Proof.
    move=> Hvs H.
    exact: (qstate_eqmod_exp (conv_istate_eqmod Hvs) H).
  Qed.

  Lemma qconv_istate_bexp e b s :
    valid_istate s ->
    IProg.eval_bexp (conv_bexp e) b s ->
    eval_bexp e b (conv_istate s).
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
      + exact: (qconv_istate_program Hvs Hip).
      + apply: (qconv_istate_bexp _ Hig).
        exact: (valid_istate_program Hvs Hip).
  Qed.

End Conversion.
