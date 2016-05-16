
(** * MiniQhasm+ for AMD64 *)

From Coq Require Import ZArith FMaps String OrderedType.
From Coq Require Import Program Program.Tactics.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
From Common Require Import Tactics Arch Nats Bits ZRing HList Var Env Store.
From sQhasm Require Import IProg.
Import HEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope qhasm_scope with qhasm.

Definition WORDSIZE : nat := AMD64.wordsize.



(** Syntax *)

(* Constants *)
Definition const : Set := BITS WORDSIZE.

(* Types *)
Inductive vtype : Set :=
| Int32
| Int64
| Int3232
| Int6464
| Float80
| Stack32
| Stack64
| Stack128
| Stack256
| Stack512.

Definition vtype_eqb (t1 t2 : vtype) : bool :=
  match t1, t2 with
  | Int32, Int32 => true
  | Int64, Int64 => true
  | Int3232, Int3232 => true
  | Int6464, Int6464 => true
  | Float80, Float80 => true
  | Stack32, Stack32 => true
  | Stack64, Stack64 => true
  | Stack128, Stack128 => true
  | Stack256, Stack256 => true
  | Stack512, Stack512 => true
  | _, _ => false
  end.

Lemma vtype_eqP : Equality.axiom vtype_eqb.
Proof.
  move=> x y.
  case Heqb : (vtype_eqb x y).
  - apply: ReflectT.
    by destruct x; destruct y.
  - apply: ReflectF.
    by destruct x; destruct y.
Qed.

Canonical vtype_eqMixin := EqMixin vtype_eqP.
Canonical vtype_eqType := Eval hnf in EqType vtype vtype_eqMixin.

Definition size_of_vtype (ty : vtype) : nat :=
  match ty with
  | Int64 => 64
  | Int32 => 32
  | Int3232 => 64
  | Int6464 => 128
  | Float80 => 80
  | Stack32 => 32
  | Stack64 => 64
  | Stack128 => 128
  | Stack256 => 256
  | Stack512 => 512
  end.

Definition value_of_vtype (ty : vtype) : Set := BITS (size_of_vtype ty).

(* Types for casting *)
Inductive vtypec : Set :=
| CastInt8
| CastInt16
| CastInt32
| CastInt64
| CastInt128
| CastUInt8
| CastUInt16
| CastUInt32
| CastUInt64
| CastUInt128.

Definition vtypec_eqb (t1 t2 : vtypec) : bool :=
  match t1, t2 with
  | CastInt8, CastInt8 => true
  | CastInt16, CastInt16 => true
  | CastInt32, CastInt32 => true
  | CastInt64, CastInt64 => true
  | CastInt128, CastInt128 => true
  | CastUInt8, CastUInt8 => true
  | CastUInt16, CastUInt16 => true
  | CastUInt32, CastUInt32 => true
  | CastUInt64, CastUInt64 => true
  | CastUInt128, CastUInt128 => true
  | _, _ => false
  end.

Lemma vtypec_eqP : Equality.axiom vtypec_eqb.
Proof.
  move=> x y.
  case Heqb : (vtypec_eqb x y).
  - apply: ReflectT.
    by destruct x; destruct y.
  - apply: ReflectF.
    by destruct x; destruct y.
Qed.

Canonical vtypec_eqMixin := EqMixin vtypec_eqP.
Canonical vtypec_eqType := Eval hnf in EqType vtypec vtypec_eqMixin.

Definition size_of_vtypec (ty : vtypec) : nat :=
  match ty with
  | CastInt8
  | CastUInt8 => 8
  | CastInt16
  | CastUInt16 => 16
  | CastInt32
  | CastUInt32 => 32
  | CastInt64
  | CastUInt64 => 64
  | CastInt128
  | CastUInt128 => 128
  end.

Definition value_of_vtypec (ty : vtypec) : Set := BITS (size_of_vtypec ty).

(* Variables of different types. *)
Definition int32 E : Set := pvar E Int32.
Definition int64 E : Set := pvar E Int64.
Definition int3232 E : Set := pvar E Int3232.
Definition int6464 E : Set := pvar E Int6464.
Definition float80 E : Set := pvar E Float80.
Definition stack32 E : Set := pvar E Stack32.
Definition stack64 E : Set := pvar E Stack64.
Definition stack128 E : Set := pvar E Stack128.
Definition stack256 E : Set := pvar E Stack256.
Definition stack512 E : Set := pvar E Stack512.

(* Decide the type of x from y given that pvar_var x == pvar_var y. *)
Ltac decide_vtype x y :=
  match type of x with
  | pvar ?E ?tyx =>
    match type of y with
    | pvar ?E ?tyy => match_goal x y
    | int32 ?E => match_goal x y
    | int64 ?E => match_goal x y
    | int3232 ?E => match_goal x y
    | int6464 ?E => match_goal x y
    | float80 ?E => match_goal x y
    | stack32 ?E => match_goal x y
    | stack64 ?E => match_goal x y
    | stack128 ?E => match_goal x y
    | stack256 ?E => match_goal x y
    | stack512 ?E => match_goal x y
    end
  end with
  match_goal x y :=
    match goal with
    | H : (pvar_var x == pvar_var y) = true |- _ =>
      let Hxy := fresh in
      move/eqP/eqP: (H) => Hxy;
      move: (pvar_vtype_eq Hxy) => {Hxy} Hxy;
      move: x H; rewrite Hxy => {Hxy} x H
    | H : is_true (pvar_var x == pvar_var y) |- _ =>
      let Heq := fresh in
      move: (pvar_vtype_eq H) => Heq;
      move: x H; rewrite Heq => {Heq} x H
    end.



Local Notation env := (HEnv.t vtype).

(* Atomics can be variables or constants. *)
Inductive atomic (E : env) : Set :=
| QVar : int64 E -> atomic E
| QConst : const -> atomic E.

(* Instructions.
   Below is the list of instructions:
   - QAssign r s: r = s
   - QAdd r s t: r = s + t
   - QAddC r s t: r = s + t + carry
   - QAdc r s t: carry? r = s + t
   - QAdcC r s t: carry? r = s + t + carry
   - QSub r s t: r = s - t
   - QSubC r s t: r = s - t - carry
   - QSbb r s t: carry? r = s - t
   - QSbbC r s t: carry? r = s - t - carry
   - QMul r s t: r = s * t
   - QMulf r s t u: r s = t * u
   - QShl r s n: r = s $<<$#&lt;&lt;# n
   - QShr r s n: r = s $>>$#&gt;&gt;# n
   - QMod2n r s n: r = s $\%$#%# 2%\textasciicircum%#^#n
 *)
Inductive instr (E : env) : Set :=
| QAssign : int64 E -> atomic E -> instr E
| QAdd : int64 E -> atomic E -> atomic E -> instr E
| QAddC : int64 E -> atomic E -> atomic E -> instr E
| QAdc : int64 E -> atomic E -> atomic E -> instr E
| QAdcC : int64 E -> atomic E -> atomic E -> instr E
| QSub : int64 E -> atomic E -> atomic E -> instr E
| QSubC : int64 E -> atomic E -> atomic E -> instr E
| QSbb : int64 E -> atomic E -> atomic E -> instr E
| QSbbC : int64 E -> atomic E -> atomic E -> instr E
| QMul : int64 E -> atomic E -> atomic E -> instr E
| QMulf : int64 E -> int64 E -> atomic E -> atomic E -> instr E
| QShl : int64 E -> atomic E -> nat -> instr E
| QShr : int64 E -> atomic E -> nat -> instr E
| QMod2n : int64 E -> atomic E -> nat -> instr E.

Definition program (E : env) : Set := seq (instr E).

(** Semantics *)

Module HeterogeneousBits <: HETEROGENEOUS.
  Definition T : Set := vtype.
  Definition V : T -> Set := fun t : T => value_of_vtype t.
  Definition default (x : T) : V x := fromNat 0.
End HeterogeneousBits.

Module State.

  Local Open Scope hlist_scope.

  Module Store := MakeHStore HeterogeneousBits.

  Record t (E : env) : Type :=
    mkState { store: Store.t E;
              carry: bool }.

  Definition acc E ty (x : pvar E ty) (s : t E) : value_of_vtype ty :=
    Store.acc x (store s).

  Definition upd E ty (x : pvar E ty) (v : value_of_vtype ty) (s : t E) : t E :=
    {| store := Store.upd x v (store s);
       carry := carry s |}.

  Definition set_carry E c (s : t E) : t E :=
    {| store := store s;
       carry := c |}.

  Definition acc_upd_heq E tyx tyy (x : pvar E tyx) (y : pvar E tyy)
             (e : value_of_vtype tyy) (s : t E) :
    pvar_var x == pvar_var y ->
    acc x (upd y e s) =v e := Store.acc_upd_heq e (store s).

  Definition acc_upd_eq E ty (x y : pvar E ty)
             (e : value_of_vtype ty) (s : t E) :
    pvar_var x == pvar_var y ->
    acc x (upd y e s) = e := Store.acc_upd_eq e (store s).

  Definition acc_upd_neq E tyx tyy (x : pvar E tyx) (y : pvar E tyy)
        (e : value_of_vtype tyy) (s : t E) :
    pvar_var x != pvar_var y ->
    acc x (upd y e s) = acc x s := Store.acc_upd_neq e (store s).

End State.

Definition eval_atomic E (a : atomic E) (st : State.t E) : BITS WORDSIZE :=
  match a with
  | QVar v => State.acc v st
  | QConst n => n
  end.

Definition eval_instr E (i : instr E) (st : State.t E) : State.t E :=
  match i with
  | QAssign r s => State.upd r (eval_atomic s st) st
  | QAdd r s t => st (* tbd *)
  | QAddC r s t => st (* tbd *)
  | QAdc r s t =>
    let vs := eval_atomic s st in
    let vt := eval_atomic t st in
    let c := carry_addB vs vt in
    let v := (vs + vt)%bits in
    State.set_carry c (State.upd r v st)
  | QAdcC r s t => st (* tbd *)
  | QSub r s t => st (* tbd *)
  | QSubC r s t => st (* tbd *)
  | QSbb r s t => st (* tbd *)
  | QSbbC r s t => st (* tbd *)
  | QMul r s t => st (* tbd *)
  | QMulf r s t u => st (* tbd *)
  | QShl r s n => st (* tbd *)
  | QShr r s n => st (* tbd *)
  | QMod2n r s n => st (* tbd *)
  end.

Fixpoint eval_program E (p : program E) (st : State.t E) : State.t E :=
  match p with
  | nil => st
  | hd::tl => eval_program tl (eval_instr hd st)
  end.

(** Overflow *)

(* Detect if an instruction will cause uncaught carry. *)
Definition instr_ovf E (i : instr E) (st: State.t E) : bool :=
  match i with
  | QAssign r s => false
  | QAdd r s t => addB_ovf (eval_atomic s st) (eval_atomic t st)
  | QAddC r s t => false (* tbd *)
  | QAdc r s t => false
  | QAdcC r s t => false (* tbd *)
  | QSub r s t => false (* tbd *)
  | QSubC r s t => false (* tbd *)
  | QSbb r s t => false (* tbd *)
  | QSbbC r s t => false (* tbd *)
  | QMul r s t => false (* tbd *)
  | QMulf r s t u => false (* tbd *)
  | QShl r s n => false (* tbd *)
  | QShr r s n => false (* tbd *)
  | QMod2n r s n => false (* tbd *)
  end.

Fixpoint program_ovf E (p : program E) (st: State.t E) : bool :=
  match p with
  | nil => false
  | hd::tl => instr_ovf hd st || program_ovf tl (eval_instr hd st)
  end.



(** Convert a MiniQhasm+ program to a sequential integer program. *)

Definition z2p64 : exp := SConst (toZ (fromHex "10000000000000000")).

Variable carry_var : env -> var.

Parameter carry_var_neq :
  forall E ty (x : pvar E ty), carry_var E != pvar_var x.

Definition conv_atomic E (a : atomic E) : IProg.exp :=
  match a with
  | QVar v => SVar (pvar_var v)
  | QConst n => SConst (toZ n)
  end.

Definition conv_instr E (i : instr E) : IProg.program :=
  match i with
  | QAssign r s =>
    [:: SAssign (pvar_var r) (conv_atomic s) ]
  | QAdd r s t => [::] (* tbd *)
  | QAddC r s t => [::] (* tbd *)
  | QAdc r s t =>
    let sum := SAdd (conv_atomic s) (conv_atomic t) in
    [:: SAssign (pvar_var r) (SMod sum z2p64);
      SAssign (carry_var E) (SDiv sum z2p64)]
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

Fixpoint conv_program E (p : program E) : IProg.program :=
  match p with
  | nil => [::]
  | hd::tl => conv_instr hd ++ conv_program tl
  end.

Program Definition state_eqmod E (qst : State.t E) (ist : IProg.State.t) : Prop :=
  (forall ty (x : pvar E ty),
     (toZ (n:=(size_of_vtype ty).-1) (State.acc x qst))%Z == IProg.State.acc (pvar_var x) ist) /\
  ((toZ (State.carry qst))%Z == IProg.State.acc (carry_var E) ist).
Next Obligation.
  rewrite prednK.
  - reflexivity.
  - move=> {x qst ist}.
    by elim: ty.
Qed.

Lemma state_eqmod_qvar E (x : int64 E) (qst : State.t E) (ist : IProg.State.t) :
  let a := QVar x in
  state_eqmod qst ist ->
  (toZ (eval_atomic a qst))%Z == eval_exp (conv_atomic a) ist.
Proof.
  move=> a [Hs Hc].
  move: (Hs Int64 x) => {Hs} Hs.
  rewrite -{1}eq_rect_eq in Hs.
  exact: Hs.
Qed.

Lemma state_eqmod_qconst E (n : const) (qst : State.t E) (ist : IProg.State.t) :
  let a := QConst E n in
  state_eqmod qst ist ->
  (toZ (eval_atomic a qst))%Z == eval_exp (conv_atomic a) ist.
Proof.
Admitted.

Lemma state_eqmod_atomic E (a : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  state_eqmod qst ist ->
  (toZ (eval_atomic a qst))%Z == eval_exp (conv_atomic a) ist.
Proof.
  elim: a qst ist.
  - (* QVar *)
    exact: state_eqmod_qvar.
  - (* QConst *)
    exact: state_eqmod_qconst.
Qed.

Lemma state_eqmod_qassign E (r : int64 E) (s : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QAssign r s in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
  move=> i Heqm _.
  move: (Heqm) => [Hst Hc].
  split => /=.
  - move=> ty x.
    case Hxr: (pvar_var x == pvar_var r).
    + decide_vtype x r.
      rewrite -{1}eq_rect_eq.
      move/idP: Hxr => Hxr.
      rewrite (State.acc_upd_eq _ qst Hxr).
      rewrite (IProg.State.acc_upd_eq _ ist Hxr).
      exact: (state_eqmod_atomic _ Heqm).
    + move/idP/negP: Hxr => Hxr.
      rewrite (State.acc_upd_neq _ qst Hxr).
      rewrite (IProg.State.acc_upd_neq _ ist Hxr).
      rewrite -(eqP (Hst ty x)).
      dependent destruction ty => /=; do 2 rewrite -eq_rect_eq; exact: eqxx.
  - move: (carry_var_neq r) => Hcr.
    rewrite (IProg.State.acc_upd_neq _ ist Hcr).
    exact: Hc.
Qed.

Lemma state_eqmod_qadd E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QAdd r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qaddc E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QAddC r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qadc E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QAdc r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qadcc E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QAdcC r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qsub E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QSub r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qsubc E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QSubC r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qsbb E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QSbb r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qsbbc E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QSbbC r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qmul E (r : int64 E) (s t : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QMul r s t in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qmulf E (r s : int64 E) (t u : atomic E) (qst : State.t E) (ist : IProg.State.t) :
  let i := QMulf r s t u in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qshl E (r : int64 E) (s : atomic E) (n : nat) (qst : State.t E) (ist : IProg.State.t) :
  let i := QShl r s n in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qshr E (r : int64 E) (s : atomic E) (n : nat) (qst : State.t E) (ist : IProg.State.t) :
  let i := QShr r s n in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_qmod2n E (r : int64 E) (s : atomic E) (n : nat) (qst : State.t E) (ist : IProg.State.t) :
  let i := QMod2n r s n in
  state_eqmod qst ist -> ~~ instr_ovf i qst ->
  state_eqmod (eval_instr i qst) (IProg.eval_program (conv_instr i) ist).
Proof.
Admitted.

Lemma state_eqmod_instr E (i : instr E) (s : State.t E) (t : IProg.State.t) :
  state_eqmod s t -> ~~ instr_ovf i s ->
  state_eqmod (eval_instr i s) (IProg.eval_program (conv_instr i) t).
Proof.
  elim: i s t.
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

Lemma state_eqmod_program E (p : program E) (qst : State.t E) (ist : IProg.State.t) :
  state_eqmod qst ist -> ~~ program_ovf p qst ->
  state_eqmod (eval_program p qst) (IProg.eval_program (conv_program p) ist).
Proof.
  elim: p qst ist.
  - done.
  - move=> hd tl H qst ist Heqm Hovf.
    rewrite eval_program_concat.
    apply: H.
    + apply: (state_eqmod_instr Heqm).
      applyP Hovf => {Hovf} Hovf.
      apply/orP; left; exact: Hovf.
    + applyP Hovf => {Hovf} Hovf.
      apply/orP; right; exact: Hovf.
Qed.
