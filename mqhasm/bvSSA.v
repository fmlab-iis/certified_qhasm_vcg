
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From Common Require Import Arch Types SsrOrdered Bits Lists FSets Bools ZAriths Var Store.
From mQhasm Require Import bvDSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Delimit Scope bvssa_scope with bvssa.

Local Open Scope bvssa_scope.

Module MakeBVSSA (A : ARCH) (VO : SsrOrderedType) (IO : SsrOrderedType) (V : SsrOrderedType with Definition T := prod_eqType VO.T IO.T) (Import VS : SsrFSet with Module E := V).
  Module Q := MakeBVDSL A V VS.
  Include Q.
End MakeBVSSA.

Module bv64SSA := MakeBVSSA AMD64 VarOrder NOrder SSAVarOrder SSAVS.

Arguments bv64SSA.bvVar v%N.

Notation "'-e' x" := (bv64SSA.bveneg x) (at level 35, right associativity) : bvssa_scope.
Notation "x '+e' y" := (bv64SSA.bveadd x y) (at level 50, left associativity) : bvssa_scope.
Notation "x '-e' y" := (bv64SSA.bvesub x y)  (at level 50, left associativity) : bvssa_scope.
Notation "x '*e' y" := (bv64SSA.bvemul x y)  (at level 40, left associativity) : bvssa_scope.
Notation "x @:= y" := (bv64SSA.bvAssign x%N y) (at level 70, no associativity) : bvssa_scope.
Notation "x '=e' y" := (bv64SSA.bveEq x y) (at level 70, no associativity) : bvssa_scope.
Notation "x '=e' y 'mod' z" := (bv64SSA.bveEqMod x y z) (at level 70, y at next level, no associativity) : bvssa_scope.
Notation "x '&&e' y" := (bv64SSA.bveand x y) (at level 70, no associativity) : bvssa_scope.

Notation "x '+r' y" := (bv64SSA.bvradd x y) (at level 50, left associativity) : bvssa_scope.
Notation "x '-r' y" := (bv64SSA.bvrsub x y)  (at level 50, left associativity) : bvssa_scope.
Notation "x '*r' y" := (bv64SSA.bvrmul x y)  (at level 40, left associativity) : bvssa_scope.
Notation "x '&&r' y" := (bv64SSA.bvrand x y) (at level 70, no associativity) : bvssa_scope.
Notation "x '<r' y" := (bv64SSA.bvult x y)  (at level 40, left associativity) : bvssa_scope.
Notation "x '<=r' y" := (bv64SSA.bvule x y)  (at level 40, left associativity) : bvssa_scope.
Notation "x '>r' y" := (bv64SSA.bvugt x y)  (at level 40, left associativity) : bvssa_scope.
Notation "x '>=r' y" := (bv64SSA.bvuge x y)  (at level 40, left associativity) : bvssa_scope.

Notation "s |= f" := (bv64SSA.eval_bexp f true s) (at level 74, no associativity) : bvssa_scope.
Notation "s '|=e' f" := (bv64SSA.eval_ebexp f true s) (at level 74, no associativity) : bvssa_scope.
Notation "s '|=r' f" := (bv64SSA.eval_rbexp f true s) (at level 74, no associativity) : bvssa_scope.
Notation "f ===> g" := (bv64SSA.entails f g) (at level 82, no associativity) : bvssa_scope.
Notation "{{ f }} p {{ g }}" := ({| bv64SSA.spre := f; bv64SSA.sprog := p; bv64SSA.spost := g |}) (at level 82, no associativity) : bvssa_scope.
Notation "|= s" := (bv64SSA.valid_spec s) (at level 83, no associativity) : bvssa_scope.
Notation "'|=e' s" := (bv64SSA.valid_espec s) (at level 83, no associativity) : bvssa_scope.
Notation "'|=r' s" := (bv64SSA.valid_rspec s) (at level 83, no associativity) : bvssa_scope.

Definition svar (x : bv64SSA.var) := fst x.
Definition sidx (x : bv64SSA.var) := snd x.
Hint Unfold svar sidx.

Module M2 := Map2 VS SSAVS.

Lemma svar_ne v1 v2 : svar v1 != svar v2 -> v1 != v2.
Proof.
  move/negP => H. apply/negP => Heq; apply: H.
  destruct v1 as [v1 i1]; destruct v2 as [v2 i2] => /=.
  case: (eqP Heq). move=> -> _; exact: eqxx.
Qed.

Lemma sidx_ne v1 v2 : sidx v1 != sidx v2 -> v1 != v2.
Proof.
  move/negP => H. apply/negP => Heq; apply: H.
  destruct v1 as [v1 i1]; destruct v2 as [v2 i2] => /=.
  case: (eqP Heq). move=> _ ->; exact: eqxx.
Qed.

Lemma svar_sidx_eq v1 v2 : sidx v1 = sidx v2 -> svar v1 = svar v2 -> v1 = v2.
Proof.
  destruct v1 as [v1 i1]; destruct v2 as [v2 i2] => /=.
  move=> -> ->; reflexivity.
Qed.



Open Scope N_scope.

(** Conversion to SSA *)

Definition index : Type := N.

(* A map from a DSL variable to its current index. *)
Definition vmap : Type := VM.t index.

Definition empty_vmap : vmap := VM.empty index.

Definition initial_index : index := 0.

Definition first_assigned_index : index := 1.

(* Find the current index of a DSL variable. *)
Definition get_index (v : var) (m : vmap) : index :=
  match VM.find v m with
  | None => initial_index
  | Some i => i
  end.

(* Increment the current index of a DSL variable. *)
Definition upd_index (v : var) (m : vmap) : vmap :=
  match VM.find v m with
  | None => VM.add v first_assigned_index m
  | Some i => VM.add v (i + 1) m
  end.

Definition ssa_var (m : vmap) (v : var) : bv64SSA.var := (v, get_index v m).

Lemma ssa_var_preserve m : M2.preserve (ssa_var m).
Proof.
  move=> x y H.
  rewrite (eqP H).
  exact: eqxx.
Qed.

Lemma ssa_var_injective m : M2.injective (ssa_var m).
Proof.
  move=> x y /eqP H.
  case: H => H _.
  rewrite H; exact: eqxx.
Qed.

Definition ssa_var_well m :=
  M2.mkWellMap2 (ssa_var_preserve m) (ssa_var_injective (m:=m)).

Definition ssa_vars (m : vmap) (vs : VS.t) : SSAVS.t :=
  M2.map2 (ssa_var m) vs.

Definition ssa_unop (op : unop) : bv64SSA.unop :=
  match op with
  | bvNegOp => bv64SSA.bvNegOp
  end.

Definition ssa_binop (op : binop) : bv64SSA.binop :=
  match op with
  | bvAddOp => bv64SSA.bvAddOp
  | bvSubOp => bv64SSA.bvSubOp
  | bvMulOp => bv64SSA.bvMulOp
  end.

Definition ssa_cmpop (op : cmpop) : bv64SSA.cmpop :=
  match op with
  | bvUltOp => bv64SSA.bvUltOp
  | bvUleOp => bv64SSA.bvUleOp
  | bvUgtOp => bv64SSA.bvUgtOp
  | bvUgeOp => bv64SSA.bvUgeOp
  end.

Definition ssa_atomic (m : vmap) (a : atomic) : bv64SSA.atomic :=
  match a with
  | bvVar v => bv64SSA.bvVar (ssa_var m v)
  | bvConst n => bv64SSA.bvConst n
  end.

Definition ssa_instr (m : vmap) (i : instr) : vmap * bv64SSA.instr :=
  match i with
  | bvAssign v e =>
    let e := ssa_atomic m e in
    let m := upd_index v m in
    (m, bv64SSA.bvAssign (ssa_var m v) e)
(*  | bvNeg v e =>
    let e := ssa_atomic m e in
    let m := upd_index v m in
    (m, bv64SSA.bvNeg (ssa_var m v) e) *)
  | bvAdd v e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let m := upd_index v m in
    (m, bv64SSA.bvAdd (ssa_var m v) e1 e2)
  | bvAddC c v e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let mv := upd_index v m in
    let mc := upd_index c mv in
    (mc, bv64SSA.bvAddC (ssa_var mc c) (ssa_var mv v) e1 e2)
  | bvAdc v e1 e2 y =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let y := ssa_var m y in
    let m := upd_index v m in
    (m, bv64SSA.bvAdc (ssa_var m v) e1 e2 y)
  | bvAdcC c v e1 e2 y =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let y := ssa_var m y in
    let mv := upd_index v m in
    let mc := upd_index c mv in
    (mc, bv64SSA.bvAdcC (ssa_var mc c) (ssa_var mv v) e1 e2 y)
  | bvSub v e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let m := upd_index v m in
    (m, bv64SSA.bvSub (ssa_var m v) e1 e2)
  | bvSubC c v e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let mv := upd_index v m in
    let mc := upd_index c mv in
    (mc, bv64SSA.bvSubC (ssa_var mc c) (ssa_var mv v) e1 e2)
  | bvSbb v e1 e2 y =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let y := ssa_var m y in
    let m := upd_index v m in
    (m, bv64SSA.bvSbb (ssa_var m v) e1 e2 y)
  | bvSbbC c v e1 e2 y =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let y := ssa_var m y in
    let mv := upd_index v m in
    let mc := upd_index c mv in
    (mc, bv64SSA.bvSbbC (ssa_var mc c) (ssa_var mv v) e1 e2 y)
  | bvMul v e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let m := upd_index v m in
    (m, bv64SSA.bvMul (ssa_var m v) e1 e2)
  | bvMulf vh vl e1 e2 =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let ml := upd_index vl m in
    let mh := upd_index vh ml in
    (mh, bv64SSA.bvMulf (ssa_var mh vh) (ssa_var ml vl) e1 e2)
  | bvShl v e p =>
    let e := ssa_atomic m e in
    let m := upd_index v m in
    (m, bv64SSA.bvShl (ssa_var m v) e p)
  | bvSplit vh vl e p =>
    let e := ssa_atomic m e in
    let ml := upd_index vl m in
    let mh := upd_index vh ml in
    (mh, bv64SSA.bvSplit (ssa_var mh vh) (ssa_var ml vl) e p)
  | bvConcatShl vh vl e1 e2 p =>
    let e1 := ssa_atomic m e1 in
    let e2 := ssa_atomic m e2 in
    let ml := upd_index vl m in
    let mh := upd_index vh ml in
    (mh, bv64SSA.bvConcatShl (ssa_var mh vh) (ssa_var ml vl) e1 e2 p)
  end.

Fixpoint ssa_program (m : vmap) (p : program) : (vmap * bv64SSA.program) :=
  match p with
  | [::] => (m, [::])
  | hd::tl =>
    let (m, hd) := ssa_instr m hd in
    let (m, tl) := ssa_program m tl in
    (m, hd::tl)
  end.

Fixpoint ssa_eexp (m : vmap) (e : eexp) : bv64SSA.eexp :=
  match e with
  | bveVar v => bv64SSA.bveVar (ssa_var m v)
  | bveConst c => @bv64SSA.bveConst c
  | bveUnop op e => bv64SSA.bveUnop (ssa_unop op) (ssa_eexp m e)
  | bveBinop op e1 e2 => bv64SSA.bveBinop (ssa_binop op) (ssa_eexp m e1) (ssa_eexp m e2)
  end.

Fixpoint ssa_rexp (n : nat) (m : vmap) (e : rexp n) : bv64SSA.rexp n :=
  match e with
  | bvrVar v => bv64SSA.bvrVar (ssa_var m v)
  | bvrConst w c => @bv64SSA.bvrConst w c
  | bvrBinop _ op e1 e2 => bv64SSA.bvrBinop (ssa_binop op) (ssa_rexp m e1) (ssa_rexp m e2)
  | bvrExt _ e i => bv64SSA.bvrExt (ssa_rexp m e) i
  end.

Fixpoint ssa_ebexp (m : vmap) (e : ebexp) : bv64SSA.ebexp :=
  match e with
  | bveTrue => bv64SSA.bveTrue
  | bveEq e1 e2 => bv64SSA.bveEq (ssa_eexp m e1) (ssa_eexp m e2)
  | bveEqMod e1 e2 p => bv64SSA.bveEqMod (ssa_eexp m e1) (ssa_eexp m e2)
                                         (ssa_eexp m p)
  | bveAnd e1 e2 => bv64SSA.bveAnd (ssa_ebexp m e1) (ssa_ebexp m e2)
  end.

Fixpoint ssa_rbexp (m : vmap) (e : rbexp) : bv64SSA.rbexp :=
  match e with
  | bvrFalse => bv64SSA.bvrFalse
  | bvrTrue => bv64SSA.bvrTrue
  | bvrCmp _ op e1 e2 => bv64SSA.bvrCmp (ssa_cmpop op) (ssa_rexp m e1) (ssa_rexp m e2)
  | bvrAnd e1 e2 => bv64SSA.bvrAnd (ssa_rbexp m e1) (ssa_rbexp m e2)
  | bvrOr e1 e2  => bv64SSA.bvrOr (ssa_rbexp m e1) (ssa_rbexp m e2)
  end.

Definition ssa_bexp (m : vmap) (e : bexp) : bv64SSA.bexp :=
  (ssa_ebexp m (eqn_bexp e), ssa_rbexp m (rng_bexp e)).

Definition ssa_spec (s : spec) : bv64SSA.spec :=
  let m := empty_vmap in
  let f := ssa_bexp m (spre s) in
  let (m, p) := ssa_program m (sprog s) in
  let g := ssa_bexp m (spost s) in
  {| bv64SSA.spre := f; bv64SSA.sprog := p; bv64SSA.spost := g |}.

Lemma ssa_program_empty : forall m, ssa_program m [::] = (m, [::]).
Proof.
  reflexivity.
Qed.

Lemma ssa_program_cons :
  forall m1 m2 hd tl p,
    ssa_program m1 (hd::tl) = (m2, p) ->
    exists m3 h t,
      ssa_instr m1 hd = (m3, h) /\ ssa_program m3 tl = (m2, t) /\ p = h::t.
Proof.
  move=> m1 m2 hd tl p /=.
  set tmp := ssa_instr m1 hd.
  have: (tmp = ssa_instr m1 hd) by reflexivity.
  destruct tmp as [m3 h].
  set tmp := ssa_program m3 tl.
  have: (tmp = ssa_program m3 tl) by reflexivity.
  destruct tmp as [m4 t].
  move=> Htl Hhd [] Hm Hp.
  exists m3; exists h; exists t; split; [idtac | split].
  - reflexivity.
  - rewrite -Htl Hm.
    reflexivity.
  - symmetry; exact: Hp.
Qed.

Lemma ssa_spec_unfold s :
  exists m, bv64SSA.spre (ssa_spec s) = ssa_bexp empty_vmap (spre s) /\
            (m, bv64SSA.sprog (ssa_spec s)) = ssa_program empty_vmap (sprog s) /\
            bv64SSA.spost (ssa_spec s) = ssa_bexp m (spost s).
Proof.
  destruct s as [f p g] => /=.
  rewrite /ssa_spec /=.
  set tmp := ssa_program empty_vmap p.
  destruct tmp as [m sp] => /=.
  exists m; split; [idtac | split]; reflexivity.
Qed.

Lemma get_index_empty v :
  get_index v empty_vmap = 0.
Proof.
  done.
Qed.

Lemma get_index_add_eq x y i s :
  x == y ->
  get_index x (VM.add y i s) = i.
Proof.
  move=> Heq.
  rewrite (eqP Heq) /get_index (VM.Lemmas.find_add_eq _ _ (eqxx y)).
  reflexivity.
Qed.

Lemma get_index_add_neq x y i s :
  x != y ->
  get_index x (VM.add y i s) = get_index x s.
Proof.
  move=> /negP Hne.
  rewrite /get_index (VM.Lemmas.find_add_neq _ _ Hne).
  reflexivity.
Qed.

Lemma get_upd_index_gt0 :
  forall (m : vmap) (v : var),
    0 <? get_index v (upd_index v m).
Proof.
  move=> m v; rewrite /upd_index.
  case: (VM.find v m) => /=.
  - move=> a.
    rewrite (get_index_add_eq _ _ (eqxx v)).
    exact: Nltn0Sn.
  - rewrite (get_index_add_eq _ _ (eqxx v)).
    done.
Qed.

Lemma get_upd_index_lt :
  forall (m : vmap) (v : var),
    get_index v m <? get_index v (upd_index v m).
Proof.
  move=> m v; rewrite /upd_index /get_index.
  case: (VM.find v m) => /=.
  - move=> a.
    rewrite (VM.Lemmas.find_add_eq _ _ (eqxx v)).
    exact: NltnSn.
  - rewrite (VM.Lemmas.find_add_eq _ _ (eqxx v)).
    done.
Qed.

Lemma get_upd_index_leF :
  forall (m : vmap) (v : var),
    get_index v (upd_index v m) <=? get_index v m -> False.
Proof.
  move=> m v Hle.
  move: (get_upd_index_lt m v) => Hlt.
  move: (Nleq_ltn_trans Hle Hlt).
  rewrite Nltnn.
  done.
Qed.

Lemma get_upd_index_eq :
  forall (m : vmap) (v : var),
    get_index v (upd_index v m) = get_index v m + 1.
Proof.
  move=> m v.
  rewrite /upd_index.
  case H: (VM.find v m).
  - rewrite /get_index.
    rewrite (VM.Lemmas.find_add_eq m _ (eqxx v)).
    rewrite H.
    reflexivity.
  - rewrite /get_index.
    rewrite (VM.Lemmas.find_add_eq m _ (eqxx v)).
    rewrite H.
    reflexivity.
Qed.

Lemma get_upd_index_neq :
  forall (m : vmap) (x v : var),
    x != v ->
    get_index x (upd_index v m) = get_index x m.
Proof.
  move=> m x v => /negP Hne.
  rewrite /upd_index /get_index.
  case: (VM.find v m).
  - move=> a.
    rewrite (VM.Lemmas.find_add_neq _ _ Hne).
    reflexivity.
  - rewrite (VM.Lemmas.find_add_neq _ _ Hne).
    reflexivity.
Qed.

Lemma get_upd_index_le :
  forall (m : vmap) (x v : var),
    get_index x m <=? get_index x (upd_index v m).
Proof.
  move=> m x v.
  case Hxv: (x == v).
  - move: (get_upd_index_lt m v) => Hlt.
    rewrite (eqP Hxv).
    exact: (NltnW Hlt).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv).
    exact: Nleqnn.
Qed.

Lemma ssa_instr_index_le :
  forall m1 m2 v i si,
    ssa_instr m1 i = (m2, si) ->
    get_index v m1 <=? get_index v m2.
Proof.
  move=> m1 m2 v i si.
  elim: i m1 m2 v si; intros;
  (let rec tac :=
       match goal with
       | H: ssa_instr _ _ = (_, _) |- _ =>
         case: H => <- Hsi; tac
       | |- is_true (get_index ?v ?m1 <=? get_index ?v (upd_index ?t ?m1)) =>
         exact: get_upd_index_le
       | |- is_true (get_index ?v ?m1 <=? get_index ?v (upd_index ?vl (upd_index ?vh m1))) =>
         move: (get_upd_index_le m1 v vh) => Hle1;
         move: (get_upd_index_le (upd_index vh m1) v vl) => Hle2;
         exact: (Nleq_trans Hle1 Hle2)
       | |- _ => idtac
       end in
   tac).
Qed.

Lemma ssa_program_index_le :
  forall m1 m2 v p sp,
    ssa_program m1 p = (m2, sp) ->
    get_index v m1 <=? get_index v m2.
Proof.
  move=> m1 m2 v p sp.
  elim: p m1 m2 v sp.
  - move=> m1 m2 v sp Hsp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm1 Hsp.
    rewrite Hm1; exact: Nleqnn.
  - move=> hd tl IH m1 m2 v sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    move: (ssa_instr_index_le v Hshd) => Hle1.
    move: (IH _ _ v _ Hstl) => Hle2.
    exact: (Nleq_trans Hle1 Hle2).
Qed.

Lemma ssa_eval_eunop :
  forall (op : unop) (v : Z),
    bv64SSA.eval_eunop (ssa_unop op) v = eval_eunop op v.
Proof.
  by case.
Qed.

Lemma ssa_eval_runop :
  forall (op : unop) (w : nat) (v : BITS w),
    bv64SSA.eval_runop (ssa_unop op) v = eval_runop op v.
Proof.
  by case.
Qed.

Lemma ssa_eval_ebinop :
  forall (op : binop) (v1 v2 : Z),
    bv64SSA.eval_ebinop (ssa_binop op) v1 v2 = eval_ebinop op v1 v2.
Proof.
  by case.
Qed.

Lemma ssa_eval_rbinop :
  forall (op : binop) (w : nat) (v1 v2 : BITS w),
    bv64SSA.eval_rbinop (ssa_binop op) v1 v2 = eval_rbinop op v1 v2.
Proof.
  by case.
Qed.

Lemma ssa_eval_cmpop :
  forall (op : cmpop) (w : nat) (v1 v2 : BITS w),
    bv64SSA.eval_cmpop (ssa_cmpop op) v1 v2 = eval_cmpop op v1 v2.
Proof.
  by case.
Qed.

Lemma ssa_var_upd_eq v m :
  ssa_var (upd_index v m) v = (v, get_index v (upd_index v m)).
Proof.
  reflexivity.
Qed.

Lemma ssa_var_upd_neq x v m :
  x != v ->
  ssa_var (upd_index v m) x = ssa_var m x.
Proof.
  move=> Hxv.
  rewrite /ssa_var.
  rewrite (get_upd_index_neq _ Hxv).
  reflexivity.
Qed.

Lemma ssa_vars_mem_elements m v vs :
  SSAVS.mem v (ssa_vars m vs) = (v \in (SSAVS.elements (ssa_vars m vs))).
Proof.
  move: (bv64SSA.VSLemmas.F.elements_iff (ssa_vars m vs) v) => [HinA Hin].
  case Hv: (v \in SSAVS.elements (ssa_vars m vs)).
  - move/InAP: Hv => Hv.
    apply/bv64SSA.VSLemmas.memP.
    apply: Hin.
    assumption.
  - move/negP: Hv => Hv.
    apply/negP => /bv64SSA.VSLemmas.memP Hmem.
    apply: Hv.
    apply/InAP.
    apply: HinA.
    assumption.
Qed.

Lemma ssa_vars_Empty m vs :
  VS.Empty vs ->
  SSAVS.Empty (ssa_vars m vs).
Proof.
  exact: M2.map2_Empty1.
Qed.

Lemma ssa_vars_mem1 m v vs :
  SSAVS.mem (ssa_var m v) (ssa_vars m vs) = VS.mem v vs.
Proof.
  exact: (M2.map2_mem1 (ssa_var_well m)).
Qed.

Lemma ssa_vars_mem2 m v vs :
  SSAVS.mem v (ssa_vars m vs) ->
  exists x, v = ssa_var m x /\ VS.mem x vs.
Proof.
  move=> Hmem; move: (M2.map2_mem2 Hmem) => [y [/eqP Hy Hmemy]].
  rewrite Hy.
  by exists y.
Qed.

Lemma ssa_vars_mem3 m v i vs :
  VS.mem v vs ->
  i = get_index v m ->
  SSAVS.mem (v, i) (ssa_vars m vs).
Proof.
  move=> Hmem Hidx.
  rewrite Hidx.
  rewrite ssa_vars_mem1.
  assumption.
Qed.

Lemma ssa_vars_mem_2vmap m1 m2 v vs :
  SSAVS.mem (ssa_var m1 v) (ssa_vars m2 vs) = VS.mem v vs && (get_index v m1 == get_index v m2).
Proof.
  case Hmem: (VS.mem v vs) => /=.
  - case Hidx: (get_index v m1 == get_index v m2) => /=.
    + rewrite /ssa_var (eqP Hidx) ssa_vars_mem1.
      assumption.
    + apply/negP => H.
      move/negP: Hidx; apply.
      move: (ssa_vars_mem2 H) => [y [[Hvy /eqP Hidx] Hy]].
      rewrite {2}Hvy; assumption.
  - apply/negP => H.
    move/negP: Hmem; apply.
    move: (ssa_vars_mem2 H) => [y [[Hvy _] Hy]].
    rewrite Hvy; assumption.
Qed.

Lemma ssa_vars_add m v vs :
  SSAVS.Equal (ssa_vars m (VS.add v vs))
                   (SSAVS.add (ssa_var m v) (ssa_vars m vs)).
Proof.
  rewrite /ssa_vars (M2.map2_add (ssa_var_well m)).
  reflexivity.
Qed.

Lemma ssa_vars_upd_mem1 m x v vs :
  SSAVS.mem x (ssa_vars (upd_index v m) vs) ->
  x == ssa_var (upd_index v m) v \/
  svar x != v /\ SSAVS.mem x (ssa_vars m vs).
Proof.
  move=> Hmem.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy.
  case Hyv: (y == v).
  - left; rewrite (eqP Hyv); exact: eqxx.
  - right; split; first by done.
    move/idP/negP: Hyv => Hyv.
    rewrite (ssa_var_upd_neq _ Hyv) ssa_vars_mem1.
    assumption.
Qed.

Lemma ssa_vars_upd_mem2 m x v vs :
  x == ssa_var (upd_index v m) v ->
  VS.mem v vs ->
  SSAVS.mem x (ssa_vars (upd_index v m) vs).
Proof.
  move=> /eqP Heq Hmem.
  rewrite Heq ssa_vars_mem1.
  assumption.
Qed.

Lemma ssa_vars_upd_mem3 m x v vs :
  svar x != v ->
  SSAVS.mem x (ssa_vars m vs) ->
  SSAVS.mem x (ssa_vars (upd_index v m) vs).
Proof.
  destruct x as [x i] => /=.
  move=> Hneq Hmem.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
  rewrite Hxy.
  rewrite ssa_vars_mem_2vmap.
  apply/andP; split.
  - assumption.
  - case: Hxy => [Hxy Hidx].
    rewrite Hxy in Hneq.
    rewrite (get_upd_index_neq _ Hneq).
    exact: eqxx.
Qed.

Lemma ssa_vars_singleton m v :
  SSAVS.Equal (ssa_vars m (VS.singleton v))
                   (SSAVS.singleton (ssa_var m v)).
Proof.
  rewrite /ssa_vars (M2.map2_singleton (ssa_var_well m)).
  reflexivity.
Qed.

Lemma ssa_vars_union m vs1 vs2 :
  SSAVS.Equal (ssa_vars m (VS.union vs1 vs2))
                   (SSAVS.union (ssa_vars m vs1) (ssa_vars m vs2)).
Proof.
  rewrite /ssa_vars (M2.map2_union (ssa_var_well m)).
  reflexivity.
Qed.

Lemma ssa_vars_atomic_comm  m (e : atomic) :
  SSAVS.Equal (ssa_vars m (vars_atomic e))
                   (bv64SSA.vars_atomic (ssa_atomic m e)).
Proof.
  case: e.
  - move=> v.
    exact: ssa_vars_singleton.
  - reflexivity.
Qed.

Lemma ssa_vars_eexp_comm m (e : eexp) :
  SSAVS.Equal (ssa_vars m (vars_eexp e))
                   (bv64SSA.vars_eexp (ssa_eexp m e)).
Proof.
  elim: e => /=.
  - exact: ssa_vars_singleton.
  - reflexivity.
  - move=> op e IH.
    assumption.
  - move=> op e1 IH1 e2 IH2.
    rewrite -IH1 -IH2 ssa_vars_union.
    reflexivity.
Qed.

Lemma ssa_vars_rexp_comm w m (e : rexp w) :
  SSAVS.Equal (ssa_vars m (vars_rexp e))
                   (bv64SSA.vars_rexp (ssa_rexp m e)).
Proof.
  elim: e => {w} /=.
  - exact: ssa_vars_singleton.
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2.
    rewrite -IH1 -IH2 ssa_vars_union.
    reflexivity.
  - move=> w e IH _.
    assumption.
Qed.

Lemma ssa_vars_eexp_union m (e1 e2 : eexp) :
 SSAVS.Equal (ssa_vars m (VS.union (vars_eexp e1) (vars_eexp e2)))
                  (SSAVS.union (bv64SSA.vars_eexp (ssa_eexp m e1))
                                    (bv64SSA.vars_eexp (ssa_eexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_eexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_rexp_union w m (e1 e2 : rexp w) :
 SSAVS.Equal (ssa_vars m (VS.union (vars_rexp e1) (vars_rexp e2)))
                  (SSAVS.union (bv64SSA.vars_rexp (ssa_rexp m e1))
                                    (bv64SSA.vars_rexp (ssa_rexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_rexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_subset m s1 s2 :
  SSAVS.subset (ssa_vars m s1) (ssa_vars m s2) = VS.subset s1 s2.
Proof.
  case Hsub: (VS.subset s1 s2).
  - apply: SSAVS.subset_1 => x /bv64SSA.VSLemmas.memP Hmem.
    apply/bv64SSA.VSLemmas.memP.
    move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
    rewrite Hxy ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemy Hsub).
  - apply/negP => H.
    move/negP: Hsub; apply.
  - apply: VS.subset_1 => x /VSLemmas.memP Hmem.
    apply/VSLemmas.memP.
    rewrite -2!(ssa_vars_mem1 m) in Hmem *.
    exact: (bv64SSA.VSLemmas.mem_subset Hmem H).
Qed.

Lemma ssa_vars_ebexp_comm m e :
  SSAVS.Equal (ssa_vars m (vars_ebexp e))
                   (bv64SSA.vars_ebexp (ssa_ebexp m e)).
Proof.
  elim: e => /=.
  - reflexivity.
  - move=> e1 e2. rewrite ssa_vars_eexp_union; reflexivity.
  - move=> e1 e2 e3. rewrite ssa_vars_union ssa_vars_eexp_union
                             ssa_vars_eexp_comm. reflexivity.
  - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
Qed.

Lemma ssa_vars_rbexp_comm m e :
  SSAVS.Equal (ssa_vars m (vars_rbexp e))
                   (bv64SSA.vars_rbexp (ssa_rbexp m e)).
Proof.
  elim: e => /=.
  - reflexivity.
  - reflexivity.
  - move=> w op e1 e2. rewrite ssa_vars_rexp_union; reflexivity.
  - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
  - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
Qed.

Lemma ssa_vars_bexp_comm m e :
  SSAVS.Equal (ssa_vars m (vars_bexp e))
                   (bv64SSA.vars_bexp (ssa_bexp m e)).
Proof.
  rewrite /ssa_bexp /vars_bexp /bv64SSA.vars_bexp /=.
  rewrite ssa_vars_union ssa_vars_ebexp_comm ssa_vars_rbexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_ebexp_union m e1 e2 :
  SSAVS.Equal (ssa_vars m (VS.union (vars_ebexp e1) (vars_ebexp e2)))
                   (SSAVS.union (bv64SSA.vars_ebexp (ssa_ebexp m e1))
                                     (bv64SSA.vars_ebexp (ssa_ebexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_ebexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_rbexp_union m e1 e2 :
  SSAVS.Equal (ssa_vars m (VS.union (vars_rbexp e1) (vars_rbexp e2)))
                   (SSAVS.union (bv64SSA.vars_rbexp (ssa_rbexp m e1))
                                     (bv64SSA.vars_rbexp (ssa_rbexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_rbexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_bexp_union m e1 e2 :
  SSAVS.Equal (ssa_vars m (VS.union (vars_bexp e1) (vars_bexp e2)))
                   (SSAVS.union (bv64SSA.vars_bexp (ssa_bexp m e1))
                                     (bv64SSA.vars_bexp (ssa_bexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_bexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_atomic_subset m e vs :
  SSAVS.subset (bv64SSA.vars_atomic (ssa_atomic m e)) (ssa_vars m vs) =
  VS.subset (vars_atomic e) vs.
Proof.
  case: e => /=.
  - move=> v.
    rewrite VSLemmas.subset_singleton bv64SSA.VSLemmas.subset_singleton
            ssa_vars_mem1.
    reflexivity.
  - move=> _.
    rewrite VSLemmas.subset_empty bv64SSA.VSLemmas.subset_empty.
    reflexivity.
Qed.

Lemma ssa_vars_eexp_subset m (e : eexp) vs :
  SSAVS.subset (bv64SSA.vars_eexp (ssa_eexp m e)) (ssa_vars m vs) =
  VS.subset (vars_eexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_eexp e) vs).
  - apply: SSAVS.subset_1 => x.
    rewrite -ssa_vars_eexp_comm => /bv64SSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/bv64SSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_eexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (bv64SSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_rexp_subset w m (e : rexp w) vs :
  SSAVS.subset (bv64SSA.vars_rexp (ssa_rexp m e)) (ssa_vars m vs) =
  VS.subset (vars_rexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_rexp e) vs).
  - apply: SSAVS.subset_1 => x.
    rewrite -ssa_vars_rexp_comm => /bv64SSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/bv64SSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_rexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (bv64SSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_ebexp_subset m e vs :
  SSAVS.subset (bv64SSA.vars_ebexp (ssa_ebexp m e)) (ssa_vars m vs) =
  VS.subset (vars_ebexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_ebexp e) vs).
  - apply: SSAVS.subset_1 => x.
    rewrite -ssa_vars_ebexp_comm => /bv64SSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/bv64SSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_ebexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (bv64SSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_rbexp_subset m e vs :
  SSAVS.subset (bv64SSA.vars_rbexp (ssa_rbexp m e)) (ssa_vars m vs) =
  VS.subset (vars_rbexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_rbexp e) vs).
  - apply: SSAVS.subset_1 => x.
    rewrite -ssa_vars_rbexp_comm => /bv64SSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/bv64SSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_rbexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (bv64SSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_bexp_subset m e vs :
  SSAVS.subset (bv64SSA.vars_bexp (ssa_bexp m e)) (ssa_vars m vs) =
  VS.subset (vars_bexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_bexp e) vs).
  - apply: SSAVS.subset_1 => x.
    rewrite -ssa_vars_bexp_comm => /bv64SSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/bv64SSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_bexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (bv64SSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_upd_index_subset1 m v vs :
  SSAVS.subset (ssa_vars (upd_index v m) vs)
                    (SSAVS.add (ssa_var (upd_index v m) v) (ssa_vars m vs)).
Proof.
  apply: SSAVS.subset_1 => x /bv64SSA.VSLemmas.memP Hmem.
  apply/bv64SSA.VSLemmas.memP.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy.
  case Hyv: (y == v).
  - apply: bv64SSA.VSLemmas.mem_add2.
    rewrite (eqP Hyv).
    exact: eqxx.
  - apply: bv64SSA.VSLemmas.mem_add3.
    rewrite ssa_vars_mem_2vmap.
    apply/andP; split.
    + assumption.
    + move/idP/negP: Hyv => Hyv.
      rewrite (get_upd_index_neq _ Hyv).
      exact: eqxx.
Qed.

Lemma ssa_vars_upd_index_subset2 m vh vl vs :
  SSAVS.subset
    (ssa_vars (upd_index vh (upd_index vl m)) vs)
    (SSAVS.add
       (ssa_var (upd_index vh (upd_index vl m)) vh)
       (SSAVS.add
          (ssa_var (upd_index vl m) vl) (ssa_vars m vs))).
Proof.
  apply: SSAVS.subset_1 => x /bv64SSA.VSLemmas.memP Hmem.
  apply/bv64SSA.VSLemmas.memP. move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy. case Hyvl: (y == vh).
  - apply: bv64SSA.VSLemmas.mem_add2. rewrite (eqP Hyvl). exact: eqxx.
  - move/idP/negP: Hyvl => Hyvl. rewrite (ssa_var_upd_neq _ Hyvl).
    case Hyvh: (y == vl).
    + apply: bv64SSA.VSLemmas.mem_add3. apply: bv64SSA.VSLemmas.mem_add2.
      rewrite (eqP Hyvh). exact: eqxx.
    + move/idP/negP: Hyvh => Hyvh. rewrite (ssa_var_upd_neq _ Hyvh).
      apply: bv64SSA.VSLemmas.mem_add3. apply: bv64SSA.VSLemmas.mem_add3.
      rewrite ssa_vars_mem1. assumption.
Qed.

(* one lval, one atomic *)
Lemma ssa_vars_instr_subset11 m1 vs v e :
  let m2 := upd_index v m1 in
  SSAVS.subset
    (ssa_vars m2 (VS.union vs (VS.add v (vars_atomic e))))
    (SSAVS.union (ssa_vars m1 vs)
                      (SSAVS.add (ssa_var m2 v)
                                      (bv64SSA.vars_atomic (ssa_atomic m1 e)))).
Proof.
  move=> /=.
  set m2 := upd_index v m1.
  set vse := vars_atomic e.
  set ssam1vs := ssa_vars m1 vs.
  set ssam2v := ssa_var m2 v.
  set ssam1e := ssa_atomic m1 e.
  move: (ssa_vars_upd_index_subset1 m1 v vs) => Hsub1.
  move: (ssa_vars_upd_index_subset1 m1 v vse) => Hsub2.
  have: SSAVS.mem ssam2v (SSAVS.add ssam2v ssam1vs) by
      apply: bv64SSA.VSLemmas.mem_add2; exact: eqxx.
  move=> Hmem.
  move: (bv64SSA.VSLemmas.subset_add3 Hmem Hsub1) => {Hmem Hsub1} Hsub1.
  move: (bv64SSA.VSLemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
  rewrite -{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
  have: SSAVS.subset (ssa_vars m2 (VS.union vs (VS.add v vse)))
                          (ssa_vars m2 (VS.union (VS.add v vs) vse)).
  { rewrite ssa_vars_subset VSLemmas.OP.P.union_sym VSLemmas.OP.P.union_add
            VSLemmas.OP.P.union_sym -VSLemmas.OP.P.union_add.
    exact: VSLemmas.subset_refl. }
  move=> Hsub1.
  move: (bv64SSA.VSLemmas.subset_trans Hsub1 Hsub) => {Hsub1 Hsub} Hsub.
  have: SSAVS.subset
          (SSAVS.union
             (SSAVS.add ssam2v ssam1vs)
             (SSAVS.add ssam2v (ssa_vars m1 vse)))
          (SSAVS.union
             ssam1vs
             (SSAVS.add ssam2v (bv64SSA.vars_atomic ssam1e))).
  { rewrite bv64SSA.VSLemmas.OP.P.union_add.
    apply: bv64SSA.VSLemmas.subset_add3.
    - apply: bv64SSA.VSLemmas.mem_union3.
      apply: bv64SSA.VSLemmas.mem_add2.
      exact: eqxx.
    - rewrite ssa_vars_atomic_comm.
      exact: bv64SSA.VSLemmas.subset_refl. }
  move=> Hsub2.
  move: (bv64SSA.VSLemmas.subset_trans Hsub Hsub2) => {Hsub Hsub2} Hsub.
  assumption.
Qed.

(* one lval, two atomics *)
Lemma ssa_vars_instr_subset12 m1 vs v e1 e2 :
  let m2 := upd_index v m1 in
  let vse1 := vars_atomic e1 in
  let vse2 := vars_atomic e2 in
  let ssam1vs := ssa_vars m1 vs in
  let ssam2v := ssa_var m2 v in
  let vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1) in
  let vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2) in
  SSAVS.subset
    (ssa_vars m2 (VS.union vs (VS.add v (VS.union vse1 vse2))))
    (SSAVS.union
       ssam1vs
       (SSAVS.add ssam2v (SSAVS.union vsssam1e1 vsssam1e2))).
Proof.
  move=> /=.
  set m2 := upd_index v m1.
  set vse1 := vars_atomic e1.
  set vse2 := vars_atomic e2.
  set ssam1vs := ssa_vars m1 vs.
  set ssam2v := ssa_var m2 v.
  set vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1).
  set vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2).

  have: SSAVS.Equal
          (ssa_vars m2 (VS.union vs (VS.add v (VS.union vse1 vse2))))
          (SSAVS.union (ssa_vars m2 (VS.union vs (VS.add v vse1)))
                            (ssa_vars m2 (VS.union vs (VS.add v vse2)))).
  { rewrite !ssa_vars_union !ssa_vars_add !ssa_vars_union.
    rewrite bv64SSA.VSLemmas.union2_same1 bv64SSA.VSLemmas.add2_same.
    reflexivity. }
  move=> ->.

  have: SSAVS.Equal
          (SSAVS.union
             ssam1vs
             (SSAVS.add ssam2v (SSAVS.union vsssam1e1 vsssam1e2)))
          (SSAVS.union
             (SSAVS.union ssam1vs
                               (SSAVS.add ssam2v vsssam1e1))
             (SSAVS.union ssam1vs
                               (SSAVS.add ssam2v vsssam1e2))).
  { rewrite bv64SSA.VSLemmas.union2_same1 bv64SSA.VSLemmas.add2_same.
    reflexivity. }
  move=> ->.

  apply: bv64SSA.VSLemmas.union_subsets; exact: ssa_vars_instr_subset11.
Qed.

(* one lval, two atomics plus one rval *)
Lemma ssa_vars_instr_subset13 m1 vs v e1 e2 c :
  let m2 := upd_index v m1 in
  let vse1 := vars_atomic e1 in
  let vse2 := vars_atomic e2 in
  let ssam1vs := ssa_vars m1 vs in
  let ssam2v := ssa_var m2 v in
  let ssam1c := ssa_var m1 c in
  let vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1) in
  let vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2) in
  SSAVS.subset
    (ssa_vars m2 (VS.union vs (VS.add c (VS.add v (VS.union vse1 vse2)))))
    (SSAVS.union
       ssam1vs
       (SSAVS.add
          ssam1c
          (SSAVS.add ssam2v (SSAVS.union vsssam1e1 vsssam1e2)))).
Proof.
  move=> /=.
  set m2 := upd_index v m1.
  set vse1 := vars_atomic e1.
  set vse2 := vars_atomic e2.
  set ssam1vs := ssa_vars m1 vs.
  set ssam2v := ssa_var m2 v.
  set ssam1c := ssa_var m1 c.
  set vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1).
  set vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2).
  set ssavs :=
    (SSAVS.union ssam1vs
       (SSAVS.add ssam1c
          (SSAVS.add ssam2v (SSAVS.union vsssam1e1 vsssam1e2)))).
  have: SSAVS.mem (ssa_var m2 c) ssavs.
  { case Hcv: (c == v).
    - rewrite (eqP Hcv). apply: bv64SSA.VSLemmas.mem_union3.
      apply: bv64SSA.VSLemmas.mem_add3. apply: bv64SSA.VSLemmas.mem_add2.
      exact: eqxx.
    - move/idP/negP: Hcv => Hcv. rewrite (ssa_var_upd_neq _ Hcv).
      apply: bv64SSA.VSLemmas.mem_union3. apply: bv64SSA.VSLemmas.mem_add2.
      exact: eqxx. }
  move=> Hc.
  rewrite ssa_vars_union ssa_vars_add bv64SSA.VSLemmas.union_add2
          -ssa_vars_union.
  apply: (bv64SSA.VSLemmas.subset_add3 Hc).
  rewrite /ssavs bv64SSA.VSLemmas.union_add2.
  apply: bv64SSA.VSLemmas.subset_add2.
  exact: ssa_vars_instr_subset12.
Qed.


(* two lvals, one atomic *)
Lemma ssa_vars_instr_subset21 m1 vs v1 v2 e :
  let m2 := upd_index v2 m1 in
  let m3 := upd_index v1 m2 in
  let vse := vars_atomic e in
  let ssam1vs := ssa_vars m1 vs in
  let ssam2v2 := ssa_var m2 v2 in
  let ssam3v1 := ssa_var m3 v1 in
  let vsssam1e := bv64SSA.vars_atomic (ssa_atomic m1 e) in
  SSAVS.subset
    (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse))))
    (SSAVS.union
       ssam1vs
       (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 vsssam1e))).
Proof.
  move=> /=.
  set m2 := upd_index v2 m1.
  set m3 := upd_index v1 m2.
  set vse := vars_atomic e.
  set ssam1vs := ssa_vars m1 vs.
  set ssam2v2 := ssa_var m2 v2.
  set ssam3v1 := ssa_var m3 v1.
  set ssam3v2 := ssa_var m3 v2.
  set ssam1e := ssa_vars m1 (vars_atomic e).
  set vsssam1e := bv64SSA.vars_atomic (ssa_atomic m1 e).
  move: (ssa_vars_upd_index_subset2 m1 v1 v2 vs) => Hsub1.
  move: (ssa_vars_upd_index_subset2 m1 v1 v2 vse) => Hsub2.
  have: SSAVS.mem ssam3v1
                       (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 ssam1vs))
                       by apply: bv64SSA.VSLemmas.mem_add2; exact: eqxx.
  have: SSAVS.mem ssam3v2
                       (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 ssam1vs)).
  { case H12: (v2 == v1).
    - (* case true *)
      apply: bv64SSA.VSLemmas.mem_add2. rewrite /ssam3v2 /ssam3v1 (eqP H12).
      exact: eqxx.
    - (* case false *)
      move/idP/negP: H12 => H12. rewrite /ssam3v2 (ssa_var_upd_neq _ H12).
      apply: bv64SSA.VSLemmas.mem_add3; apply: bv64SSA.VSLemmas.mem_add2.
      exact: eqxx. }
  move=> Hmemv2 Hmemv1.
  move: (bv64SSA.VSLemmas.subset_add3 Hmemv2 Hsub1) => {Hmemv2 Hsub1} Hsub1.
  move: (bv64SSA.VSLemmas.subset_add3 Hmemv1 Hsub1) => {Hmemv1 Hsub1} Hsub1.
  move: (bv64SSA.VSLemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
  rewrite -2!{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
  have: SSAVS.subset
          (SSAVS.union
             (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 ssam1vs))
             (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 (ssa_vars m1 vse))))
          (SSAVS.union
             ssam1vs
             (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 vsssam1e))).
  { rewrite /vsssam1e -ssa_vars_atomic_comm.
    rewrite bv64SSA.VSLemmas.OP.P.union_add.
    have: SSAVS.mem
            ssam3v1
            (SSAVS.union
               ssam1vs
               (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 ssam1e)))
      by apply: bv64SSA.VSLemmas.mem_union3;
         apply: bv64SSA.VSLemmas.mem_add2;
         exact: eqxx.
    move=> Hmem; apply: (bv64SSA.VSLemmas.subset_add3 Hmem) => {Hmem}.
    rewrite bv64SSA.VSLemmas.OP.P.union_add.
    have: SSAVS.mem
            ssam2v2
            (SSAVS.union
               ssam1vs
               (SSAVS.add ssam3v1 (SSAVS.add ssam2v2 ssam1e)))
      by apply: bv64SSA.VSLemmas.mem_union3;
         apply: bv64SSA.VSLemmas.mem_add3;
         apply: bv64SSA.VSLemmas.mem_add2;
         exact: eqxx.
    move=> Hmem; apply: (bv64SSA.VSLemmas.subset_add3 Hmem) => {Hmem}.
    exact: bv64SSA.VSLemmas.subset_refl. }
  move=> Hsub1.
  move: (bv64SSA.VSLemmas.subset_trans Hsub Hsub1) => {Hsub1 Hsub} Hsub.
  have: SSAVS.subset
          (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse))))
          (ssa_vars m3 (VS.union (VS.add v1 (VS.add v2 vs)) vse)).
  { rewrite ssa_vars_subset VSLemmas.OP.P.union_sym
            4!VSLemmas.OP.P.union_add VSLemmas.OP.P.union_sym.
    exact: VSLemmas.subset_refl. }
  move=> Hsub2.
  move: (bv64SSA.VSLemmas.subset_trans Hsub2 Hsub) => {Hsub Hsub2} Hsub.
  assumption.
Qed.

(* two lvals, two atomics *)
Lemma ssa_vars_instr_subset22 m1 vs v1 v2 e1 e2 :
  let m2 := upd_index v2 m1 in
  let m3 := upd_index v1 m2 in
  let vse1 := vars_atomic e1 in
  let vse2 := vars_atomic e2 in
  let ssam1vs := ssa_vars m1 vs in
  let ssam2v2 := ssa_var m2 v2 in
  let ssam3v1 := ssa_var m3 v1 in
  let vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1) in
  let vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2) in
  SSAVS.subset
    (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 (VS.union vse1 vse2)))))
    (SSAVS.union
       ssam1vs
       (SSAVS.add ssam3v1
                       (SSAVS.add ssam2v2
                                       (SSAVS.union vsssam1e1 vsssam1e2)))).
Proof.
  move=> /=.
  set m2 := upd_index v2 m1.
  set m3 := upd_index v1 m2.
  set vse1 := (vars_atomic e1).
  set vse2 := (vars_atomic e2).
  set ssam1vs := (ssa_vars m1 vs).
  set ssam2v2 := ssa_var m2 v2.
  set ssam3v1 := ssa_var m3 v1.
  set ssam3v2 := ssa_var m3 v2.
  set ssam1e1 := ssa_vars m1 (vars_atomic e1).
  set ssam1e2 := ssa_vars m1 (vars_atomic e2).
  set vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1).
  set vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2).

  have: SSAVS.Equal
          (ssa_vars m3
                    (VS.union vs (VS.add v1 (VS.add v2 (VS.union vse1 vse2)))))
          (SSAVS.union
             (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse1))))
             (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse2))))).
  { rewrite !ssa_vars_union !ssa_vars_add !ssa_vars_union.
    rewrite bv64SSA.VSLemmas.union2_same1 bv64SSA.VSLemmas.add2_same
            bv64SSA.VSLemmas.add2_same. reflexivity. }
  move=> ->.

  have: SSAVS.Equal
          (SSAVS.union
             ssam1vs
             (SSAVS.add
                ssam3v1
                (SSAVS.add ssam2v2 (SSAVS.union vsssam1e1 vsssam1e2))))
          (SSAVS.union
             (SSAVS.union
                ssam1vs
                (SSAVS.add ssam3v1
                                (SSAVS.add ssam2v2 vsssam1e1)))
             (SSAVS.union
                ssam1vs
                (SSAVS.add ssam3v1
                                (SSAVS.add ssam2v2 vsssam1e2)))).
  { rewrite bv64SSA.VSLemmas.union2_same1 bv64SSA.VSLemmas.add2_same
            bv64SSA.VSLemmas.add2_same. reflexivity. }
  move=> ->.

  apply: bv64SSA.VSLemmas.union_subsets; exact: ssa_vars_instr_subset21.
Qed.

(* two lvals, two atomics plus one rval *)
Lemma ssa_vars_instr_subset23 m1 vs v1 v2 e1 e2 a :
  let m2 := upd_index v2 m1 in
  let m3 := upd_index v1 m2 in
  let vse1 := vars_atomic e1 in
  let vse2 := vars_atomic e2 in
  let ssam1vs := ssa_vars m1 vs in
  let ssam2v2 := ssa_var m2 v2 in
  let ssam3v1 := ssa_var m3 v1 in
  let ssam1a := ssa_var m1 a in
  let vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1) in
  let vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2) in
  SSAVS.subset
    (ssa_vars m3 (VS.union vs (VS.add a (VS.add v1 (VS.add v2 (VS.union vse1 vse2))))))
    (SSAVS.union
       ssam1vs
       (SSAVS.add
          ssam1a
          (SSAVS.add
             ssam3v1
             (SSAVS.add ssam2v2 (SSAVS.union vsssam1e1 vsssam1e2))))).
Proof.
  move=> /=.
  set m2 := upd_index v2 m1.
  set m3 := upd_index v1 m2.
  set vse1 := (vars_atomic e1).
  set vse2 := (vars_atomic e2).
  set ssam1vs := (ssa_vars m1 vs).
  set ssam2v2 := ssa_var m2 v2.
  set ssam3v1 := ssa_var m3 v1.
  set ssam3v2 := ssa_var m3 v2.
  set ssam1e1 := ssa_vars m1 (vars_atomic e1).
  set ssam1e2 := ssa_vars m1 (vars_atomic e2).
  set ssam1a := ssa_var m1 a.
  set vsssam1e1 := bv64SSA.vars_atomic (ssa_atomic m1 e1).
  set vsssam1e2 := bv64SSA.vars_atomic (ssa_atomic m1 e2).
  set ssavs :=
    (SSAVS.union ssam1vs
       (SSAVS.add ssam1a
          (SSAVS.add ssam3v1
             (SSAVS.add ssam2v2 (SSAVS.union vsssam1e1 vsssam1e2))))).
  have: SSAVS.mem (ssa_var m3 a) ssavs.
  { case Hav1: (a == v1).
    - rewrite (eqP Hav1). apply: bv64SSA.VSLemmas.mem_union3.
      apply: bv64SSA.VSLemmas.mem_add3. apply: bv64SSA.VSLemmas.mem_add2.
      exact: eqxx.
    - move/idP/negP: Hav1 => Hav1. rewrite /m3 (ssa_var_upd_neq _ Hav1).
      case Hav2: (a == v2).
      + rewrite (eqP Hav2). apply: bv64SSA.VSLemmas.mem_union3.
        apply: bv64SSA.VSLemmas.mem_add3. apply: bv64SSA.VSLemmas.mem_add3.
        apply: bv64SSA.VSLemmas.mem_add2. exact: eqxx.
      + move/idP/negP: Hav2 => Hav2.
        rewrite /m2 (ssa_var_upd_neq _ Hav2). apply: bv64SSA.VSLemmas.mem_union3.
        apply: bv64SSA.VSLemmas.mem_add2. exact: eqxx. }
  move=> Ha.
  rewrite ssa_vars_union ssa_vars_add bv64SSA.VSLemmas.union_add2 -ssa_vars_union.
  apply: (bv64SSA.VSLemmas.subset_add3 Ha).
  apply: bv64SSA.VSLemmas.subset_trans; first by exact: ssa_vars_instr_subset22.
  have: SSAVS.Equal
          ssavs
          (SSAVS.add ssam1a
              (SSAVS.union ssam1vs
                  (SSAVS.add ssam3v1
                     (SSAVS.add ssam2v2 (SSAVS.union vsssam1e1 vsssam1e2))))).
  { rewrite -bv64SSA.VSLemmas.union_add2. reflexivity. }
  move=> ->.
  apply: bv64SSA.VSLemmas.subset_add2.
  exact: bv64SSA.VSLemmas.subset_refl.
Qed.

Lemma ssa_vars_instr_subset m1 m2 vs i si :
  ssa_instr m1 i = (m2, si) ->
  SSAVS.subset (ssa_vars m2 (VS.union vs (vars_instr i)))
                    (SSAVS.union (ssa_vars m1 vs) (bv64SSA.vars_instr si)).
Proof.
  case: i => /=; intros;
  (match goal with
   | H : (_, _) = (_, _) |- _ => case: H => <- <- /=
   end
  );
  try first [
    exact: ssa_vars_instr_subset11 |
    exact: ssa_vars_instr_subset12 |
    exact: ssa_vars_instr_subset13 |
    exact: ssa_vars_instr_subset21 |
    exact: ssa_vars_instr_subset22 |
    exact: ssa_vars_instr_subset23
  ].
Qed.

Lemma ssa_vars_post_subset vs m1 m2 p sp g :
  VS.subset (vars_bexp g) (VS.union vs (vars_program p)) ->
  ssa_program m1 p = (m2, sp) ->
  SSAVS.subset (bv64SSA.vars_bexp (ssa_bexp m2 g)) (SSAVS.union (ssa_vars m1 vs) (bv64SSA.vars_program sp)).
Proof.
  elim: p vs m1 m2 sp g => /=.
  - move=> vs m1 m2 sp g Hsub [] Hm Hsp.
    rewrite -Hsp -Hm /=.
    rewrite (bv64SSA.VSLemmas.OP.P.empty_union_2 _ SSAVS.empty_1).
    rewrite ssa_vars_bexp_subset.
    rewrite -(VSLemmas.OP.P.empty_union_2 vs VS.empty_1).
    assumption.
  - move=> hd tl IH vs m1 m2 sp g Hsub Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp /= => {Hsp}.
    move: Hsub; rewrite -VSLemmas.OP.P.union_assoc => Hsub.
    move: (IH _ _ _ _ _ Hsub Hstl) => {IH Hsub Hstl} H0.
    move: (SSAVS.subset_2 H0) => {H0} H0.
    move: (ssa_vars_instr_subset vs Hshd) => {Hshd} H1.
    move: (SSAVS.subset_2 H1) => {H1} H1.
    move: (bv64SSA.VSLemmas.OP.P.union_subset_4 (s'':=bv64SSA.vars_program stl) H1) => {H1} H1.
    rewrite -bv64SSA.VSLemmas.OP.P.union_assoc.
    move: (bv64SSA.VSLemmas.OP.P.subset_trans H0 H1) => {H0 H1} H2.
    apply: SSAVS.subset_1.
    assumption.
Qed.



(** State equivalence *)

Definition state_equiv (m : vmap) (s : State.t) (ss : bv64SSA.State.t) : Prop :=
  forall x, State.acc x s = bv64SSA.State.acc (x, get_index x m) ss.

Lemma pair_neq1 :
  forall (T : eqType) (a b c d : T),
    a != c -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hac; exact: eqxx.
Qed.

Lemma pair_neq2 :
  forall (T : eqType) (a b c d : T),
    b != d -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hbd; exact: eqxx.
Qed.

Lemma ssa_eval_atomic m s ss a :
  state_equiv m s ss ->
  bv64SSA.eval_atomic (ssa_atomic m a) ss = eval_atomic a s.
Proof.
  move=> Heq; elim: a => /=.
  - move=> v.
    rewrite (Heq v).
    reflexivity.
  - reflexivity.
Qed.

Lemma ssa_eval_eexp m s ss (e : eexp) :
  state_equiv m s ss ->
  bv64SSA.eval_eexp (ssa_eexp m e) ss = eval_eexp e s.
Proof.
  move=> Heq; elim: e => /=.
  - move=> v. rewrite (Heq v). reflexivity.
  - reflexivity.
  - move=> op e IH. rewrite ssa_eval_eunop IH. reflexivity.
  - move=> op e1 IH1 e2 IH2. rewrite ssa_eval_ebinop IH1 IH2. reflexivity.
Qed.

Lemma ssa_eval_rexp w m s ss (e : rexp w) :
  state_equiv m s ss ->
  bv64SSA.eval_rexp (ssa_rexp m e) ss = eval_rexp e s.
Proof.
  move=> Heq; elim: e => {w} /=.
  - move=> v. exact: (Logic.eq_sym (Heq v)).
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2. rewrite ssa_eval_rbinop IH1 IH2. reflexivity.
  - move=> w e IH p. rewrite IH. reflexivity.
Qed.

Lemma ssa_eval_ebexp m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_ebexp (ssa_ebexp m e) ss <-> eval_ebexp e s.
Proof.
  move=> Heq; elim: e => /=.
  - done.
  - move=> e1 e2. rewrite 2!(ssa_eval_eexp _ Heq). done.
  - move=> e1 e2 p. rewrite 3!(ssa_eval_eexp _ Heq). done.
  - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
Qed.

Lemma ssa_eval_ebexp1 m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_ebexp (ssa_ebexp m e) ss -> eval_ebexp e s.
Proof.
  move=> Heq He.
  move: (ssa_eval_ebexp e Heq) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_eval_ebexp2 m s ss e :
  state_equiv m s ss ->
  eval_ebexp e s -> bv64SSA.eval_ebexp (ssa_ebexp m e) ss.
Proof.
  move=> Heq He.
  move: (ssa_eval_ebexp e Heq) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma ssa_eval_rbexp m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_rbexp (ssa_rbexp m e) ss <-> eval_rbexp e s.
Proof.
  move=> Heq; elim: e => /=.
  - done.
  - done.
  - move=> w op e1 e2. rewrite 2!(ssa_eval_rexp _ Heq) ssa_eval_cmpop. done.
  - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
  - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
Qed.

Lemma ssa_eval_rbexp1 m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_rbexp (ssa_rbexp m e) ss -> eval_rbexp e s.
Proof.
  move=> Heq He.
  move: (ssa_eval_rbexp e Heq) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_eval_rbexp2 m s ss e :
  state_equiv m s ss ->
  eval_rbexp e s -> bv64SSA.eval_rbexp (ssa_rbexp m e) ss.
Proof.
  move=> Heq He.
  move: (ssa_eval_rbexp e Heq) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma ssa_eval_bexp m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_bexp (ssa_bexp m e) ss <-> eval_bexp e s.
Proof.
  move=> Heq. split; move=> [H1 H2].
  - exact: (conj (ssa_eval_ebexp1 Heq H1) (ssa_eval_rbexp1 Heq H2)).
  - exact: (conj (ssa_eval_ebexp2 Heq H1) (ssa_eval_rbexp2 Heq H2)).
Qed.

Lemma ssa_eval_bexp1 m s ss e :
  state_equiv m s ss ->
  bv64SSA.eval_bexp (ssa_bexp m e) ss -> eval_bexp e s.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_eval_bexp2 m s ss e :
  state_equiv m s ss ->
  eval_bexp e s -> bv64SSA.eval_bexp (ssa_bexp m e) ss.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma state_equiv_upd m s ss x v :
  state_equiv m s ss ->
  state_equiv (upd_index x m)
              (State.upd x v s)
              (bv64SSA.State.upd (ssa_var (upd_index x m) x) v ss).
Proof.
  move=> Heq y.
  case Hyx: (y == x) => /=.
  - rewrite (State.acc_upd_eq _ _ Hyx).
    rewrite (eqP Hyx) (bv64SSA.State.acc_upd_eq _ _ (eqxx (ssa_var _ x))).
    reflexivity.
  - move/idP/negP: Hyx => Hyx.
    rewrite (State.acc_upd_neq _ _ Hyx).
    rewrite (bv64SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hyx)).
    rewrite (get_upd_index_neq _ Hyx).
    exact: Heq.
Qed.

Lemma state_equiv_upd2 m s ss x vx y vy :
  state_equiv m s ss ->
  state_equiv (upd_index y (upd_index x m))
              (State.upd2 x vx y vy s)
              (bv64SSA.State.upd2
                 (ssa_var (upd_index x m) x) vx
                 (ssa_var (upd_index y (upd_index x m)) y) vy
                 ss).
Proof.
  move=> Heq z.
  case Hzy: (z == y) => /=.
  - rewrite (State.acc_upd_eq _ _ Hzy).
    rewrite (eqP Hzy) (bv64SSA.State.acc_upd_eq _ _ (eqxx (ssa_var _ y))).
    reflexivity.
  - move/idP/negP: Hzy => Hzy.
    rewrite (State.acc_upd_neq _ _ Hzy).
    rewrite (bv64SSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hzy)).
    rewrite (get_upd_index_neq _ Hzy).
    exact: state_equiv_upd.
Qed.

Ltac ssa_eval_state_equiv_tac :=
  simpl; intros;
  let rec tac :=
      lazymatch goal with
      | H : (_, _) = (_, _) |- _ =>
        case: H; intros; subst; simpl; tac
      | H : state_equiv ?m ?s ?ss
        |- context f [bv64SSA.eval_atomic (ssa_atomic ?m ?a) ?ss] =>
        rewrite (ssa_eval_atomic a H); tac
      | H : state_equiv ?m ?s ?ss
        |- context f [bv64SSA.State.acc (ssa_var ?m ?a) ?ss] =>
        rewrite -(H a); tac
      | H : state_equiv ?m ?s ?ss |- _ =>
          try first [ exact: (state_equiv_upd _ _ H) |
                      exact: (state_equiv_upd2 _ _ _ _ H) ]
      end in
  tac.

Lemma ssa_eval_instr :
  forall m1 m2 s1 s2 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i = s2 ->
    bv64SSA.eval_instr ss1 si = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 i.
  case: i; by ssa_eval_state_equiv_tac.
Qed.

Lemma ssa_eval_instr_succ :
  forall m1 m2 s1 s2 ss1 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i = s2 ->
    exists ss2,
      bv64SSA.eval_instr ss1 si = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 i si Hi Heq Hei.
  exists (bv64SSA.eval_instr ss1 si); split.
  - reflexivity.
  - exact: (ssa_eval_instr Hi Heq Hei).
Qed.

Lemma ssa_eval_program :
  forall m1 m2 s1 s2 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    bv64SSA.eval_program ss1 sp = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 p.
  elim: p m1 m2 s1 s2 ss1 ss2 => /=.
  - move=> m1 m2 s1 s2 ss1 ss2 p [Hm Hp] Heq Hep Hesp.
    rewrite -Hp in Hesp.
    rewrite -Hep -Hesp -Hm.
    exact: Heq.
  - move=> hd tl IH m1 m2 s1 s2 ss1 ss2 sp Hsp Heq Hep Hesp.
    move: (eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [h [t [Hh [Ht Hht]]]]].
    rewrite Hht in Hesp.
    move: (bv64SSA.eval_program_cons Hesp) => [ss3 [Heshd Hestl]].
    move: (ssa_eval_instr Hh Heq Hehd Heshd) => Heq'.
    exact: (IH _ _ _ _ _ _ _ Ht Heq' Hetl Hestl).
Qed.

Lemma ssa_eval_program_succ :
  forall m1 m2 s1 s2 ss1 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    exists ss2,
      bv64SSA.eval_program ss1 sp = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 p sp Hp Heq Hep.
  exists (bv64SSA.eval_program ss1 sp); split.
  - reflexivity.
  - exact: (ssa_eval_program Hp Heq Hep).
Qed.

Lemma dessa_eval_instr_succ :
  forall m1 m2 s1 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    bv64SSA.eval_instr ss1 si = ss2 ->
    exists s2,
      eval_instr s1 i = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 i si Hi Heq Hesi.
  exists (eval_instr s1 i); split.
  - reflexivity.
  - apply: (ssa_eval_instr Hi Heq _ Hesi).
    reflexivity.
Qed.

Lemma dessa_eval_program_succ :
  forall m1 m2 s1 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    bv64SSA.eval_program ss1 sp = ss2 ->
    exists s2,
      eval_program s1 p = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 p sp Hp Heq Hesp.
  exists (eval_program s1 p); split.
  - reflexivity.
  - apply: (ssa_eval_program Hp Heq _ Hesp).
    reflexivity.
Qed.



(** Convert a DSL state to an SSA state. *)

Definition ssa_state (m : vmap) (s : State.t) : bv64SSA.State.t :=
  fun v =>
    if (sidx v) == get_index (svar v) m
    then State.acc (svar v) s
    else State.acc (svar v) State.empty.

Lemma acc_ssa_state_eq :
  forall (m : vmap) (s : State.t) (v : var) (i : index),
    i == get_index v m ->
    bv64SSA.State.acc (v, i) (ssa_state m s) = State.acc v s.
Proof.
  move=> m s v i Heq.
  rewrite /ssa_state /bv64SSA.State.acc /bv64SSA.State.S.acc /=.
  rewrite Heq.
  reflexivity.
Qed.

Lemma ssa_state_equiv :
  forall m s, state_equiv m s (ssa_state m s).
Proof.
  move=> m s x.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
  reflexivity.
Qed.



(** Convert an SSA state to a DSL state. *)

Definition dessa_state (m : vmap) (s : bv64SSA.State.t) : State.t :=
  fun v => bv64SSA.State.acc (v, get_index v m) s.

Lemma acc_dessa_state :
  forall (m : vmap) (s : bv64SSA.State.t) (v : var),
    State.acc v (dessa_state m s) = bv64SSA.State.acc (v, get_index v m) s.
Proof.
  reflexivity.
Qed.

Lemma ssa_dessaK :
  forall (m : vmap) (s : State.t) (x : var),
    State.acc x (dessa_state m (ssa_state m s)) = State.acc x s.
Proof.
  move=> m s x.
  rewrite acc_dessa_state.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
  reflexivity.
Qed.

Corollary dessa_state_equiv :
  forall m s, state_equiv m (dessa_state m s) s.
Proof.
  move=> m s x.
  exact: acc_dessa_state.
Qed.



(** Soundness and completeness *)

Theorem ssa_spec_sound (s : spec) :
  bv64SSA.valid_spec (ssa_spec s) -> valid_spec s.
Proof.
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec s1 s2 /= Hf Hep.
  pose ss1 := ssa_state empty_vmap s1.
  pose Heq1 := (ssa_state_equiv empty_vmap s1).
  move: (ssa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hep) => [ss2 [Hesp Heq2]].
  move: (ssa_eval_bexp2 Heq1 Hf) => Hsf.
  move: (Hspec ss1 ss2 Hsf Hesp) => /= Hsg.
  exact: (ssa_eval_bexp1 Heq2 Hsg).
Qed.

Theorem ssa_spec_complete (s : spec) :
  valid_spec s -> bv64SSA.valid_spec (ssa_spec s).
Proof.
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec ss1 ss2 /= Hsf Hesp.
  pose s1 := dessa_state empty_vmap ss1.
  pose Heq1 := (dessa_state_equiv empty_vmap ss1).
  move: (dessa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hesp) => [s2 [Hep Heq2]].
  move: (ssa_eval_bexp1 Heq1 Hsf) => Hf.
  move: (Hspec s1 s2 Hf Hep) => /= Hg.
  exact: (ssa_eval_bexp2 Heq2 Hg).
Qed.



(** Well-formed SSA *)

Definition ssa_var_unchanged_instr (v : bv64SSA.var) (i : bv64SSA.instr) : bool :=
  ~~ (SSAVS.mem v (bv64SSA.lvs_instr i)).

Definition ssa_unchanged_instr_var (i : bv64SSA.instr) (v : bv64SSA.var) : bool :=
  ~~ (SSAVS.mem v (bv64SSA.lvs_instr i)).

Definition ssa_vars_unchanged_instr (vs : SSAVS.t) (i : bv64SSA.instr) : bool :=
  SSAVS.for_all (ssa_unchanged_instr_var i) vs.

Definition ssa_var_unchanged_program (v : bv64SSA.var) (p : bv64SSA.program) : bool :=
  all (ssa_var_unchanged_instr v) p.

Definition ssa_unchanged_program_var (p : bv64SSA.program) (v : bv64SSA.var) : bool :=
  ssa_var_unchanged_program v p.

Definition ssa_vars_unchanged_program (vs : SSAVS.t) (p : bv64SSA.program) : bool :=
  SSAVS.for_all (ssa_unchanged_program_var p) vs.

Fixpoint ssa_single_assignment (p : bv64SSA.program) : bool :=
  match p with
  | [::] => true
  | hd::tl =>
    (ssa_vars_unchanged_program (bv64SSA.lvs_instr hd) tl) &&
    (ssa_single_assignment tl)
  end.

Definition well_formed_ssa_program (vs : SSAVS.t) (p : bv64SSA.program) : bool :=
  bv64SSA.well_formed_program vs p &&
  ssa_vars_unchanged_program vs p &&
  ssa_single_assignment p.

Definition well_formed_ssa_spec (vs : SSAVS.t) (s : bv64SSA.spec) : bool :=
  bv64SSA.well_formed_spec vs s &&
  ssa_vars_unchanged_program vs (bv64SSA.sprog s) &&
  ssa_single_assignment (bv64SSA.sprog s).

(* Given that (ssa_var_unchanged_instr x i), prove that (x != v) where
   v is an lval of i.*)
Ltac ssa_var_unchanged_lv_neq :=
  match goal with
  | H : is_true (ssa_var_unchanged_instr ?x ?i) |- is_true (?x != ?v) =>
    rewrite /ssa_var_unchanged_instr /= in H;
    apply/negP;
    first [
        move: (bv64SSA.VSLemmas.not_mem_singleton1 H) => {H} H |
        let Hm1 := fresh in
        let Hm2 := fresh in
        move: (bv64SSA.VSLemmas.not_mem_add1 H) => {H} [Hm1 Hm2];
        move: (bv64SSA.VSLemmas.not_mem_singleton1 Hm2) => {Hm2} Hm2
    ];
    assumption
  end.

Ltac acc_unchanged_instr_upd :=
  match goal with
  | Hi : is_true (ssa_var_unchanged_instr ?x ?i),
    Hu : bv64SSA.State.upd ?v ?e ?s1 = ?s2
    |- bv64SSA.State.acc ?x ?s1 = bv64SSA.State.acc ?x ?s2 =>
    rewrite -Hu;
    rewrite bv64SSA.State.acc_upd_neq;
    [ reflexivity | by ssa_var_unchanged_lv_neq ]
  | Hi : is_true (ssa_var_unchanged_instr ?x ?i),
    Hu : bv64SSA.State.upd2 ?v1 ?e1 ?v2 ?e2 ?s1 = ?s2
    |- bv64SSA.State.acc ?x ?s1 = bv64SSA.State.acc ?x ?s2 =>
    rewrite -Hu;
    rewrite bv64SSA.State.acc_upd_neq; [
      rewrite bv64SSA.State.acc_upd_neq;
      [ reflexivity | by ssa_var_unchanged_lv_neq ] |
      by ssa_var_unchanged_lv_neq
    ]
  end.

Lemma acc_unchanged_instr v i s1 s2 :
  ssa_var_unchanged_instr v i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.State.acc v s1 = bv64SSA.State.acc v s2.
Proof.
  elim: i => /=; intros; by acc_unchanged_instr_upd.
Qed.

Lemma acc_unchanged_program v p s1 s2 :
  ssa_var_unchanged_program v p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.State.acc v s1 = bv64SSA.State.acc v s2.
Proof.
  elim: p s1 s2 => /=.
  - move=> s1 s2 _ Hep.
    rewrite Hep.
    reflexivity.
  - move=> hd tl IH s1 s2 /andP [Huchd Huctl] Hep.
    move: (bv64SSA.eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    rewrite (acc_unchanged_instr Huchd Hehd).
    exact: (IH _ _ Huctl Hetl).
Qed.

Lemma ssa_var_unchanged_program_cons1 v hd tl :
  ssa_var_unchanged_program v (hd::tl) ->
  ssa_var_unchanged_instr v hd /\ ssa_var_unchanged_program v tl.
Proof.
  move => /andP H.
  exact: H.
Qed.

Lemma ssa_var_unchanged_program_cons2 v hd tl :
  ssa_var_unchanged_instr v hd ->
  ssa_var_unchanged_program v tl ->
  ssa_var_unchanged_program v (hd::tl).
Proof.
  move=> Hhd Htl.
  rewrite /ssa_var_unchanged_program /= -/(ssa_var_unchanged_program v tl).
  by rewrite Hhd Htl.
Qed.

Lemma ssa_var_unchanged_program_concat1 v p1 p2 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  ssa_var_unchanged_program v p1 /\ ssa_var_unchanged_program v p2.
Proof.
  elim: p1 p2.
  - move=> /= p2 H.
    by rewrite H.
  - move=> hd tl IH p2 /andP [Hhd Htlp2].
    move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2].
    by rewrite /= Hhd Htl Hp2.
Qed.

Lemma ssa_var_unchanged_program_concat2 v p1 p2 :
  ssa_var_unchanged_program v p1 ->
  ssa_var_unchanged_program v p2 ->
  ssa_var_unchanged_program v (p1 ++ p2).
Proof.
  elim: p1 p2.
  - move=> /= p2 _ Hp2. exact: Hp2.
  - move=> hd tl IH p2 [Hhdtl Hp2].
    move: (ssa_var_unchanged_program_cons1 Hhdtl) => {Hhdtl} [Hhd Htl].
    apply/andP; split.
    + exact: Hhd.
    + exact: (IH _ Htl Hp2).
Qed.

Lemma acc_unchanged_program_cons v hd tl s1 s2 s3 :
  ssa_var_unchanged_program v (hd::tl) ->
  bv64SSA.eval_instr s1 hd = s2 ->
  bv64SSA.eval_program s2 tl = s3 ->
  bv64SSA.State.acc v s2 = bv64SSA.State.acc v s1 /\
  bv64SSA.State.acc v s3 = bv64SSA.State.acc v s1.
Proof.
  move=> /andP [Hunhd Huntl] Hehd Hetl.
  move: (acc_unchanged_instr Hunhd Hehd) (acc_unchanged_program Huntl Hetl) =>
    H21 H32.
  rewrite -H32 -H21.
  split; reflexivity.
Qed.

Lemma acc_unchanged_program_concat v p1 p2 s1 s2 s3 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  bv64SSA.eval_program s1 p1 = s2 ->
  bv64SSA.eval_program s2 p2 = s3 ->
  bv64SSA.State.acc v s2 = bv64SSA.State.acc v s1 /\
  bv64SSA.State.acc v s3 = bv64SSA.State.acc v s1.
Proof.
  move=> Hun12 Hep1 Hep2.
  move: (ssa_var_unchanged_program_concat1 Hun12) => {Hun12} [Hun1 Hun2].
  rewrite -(acc_unchanged_program Hun2 Hep2) -(acc_unchanged_program Hun1 Hep1).
  split; reflexivity.
Qed.

Lemma ssa_unchanged_instr_var_compat i :
  SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_instr_var i).
Proof.
  move=> x y Heq.
  rewrite (eqP Heq).
  reflexivity.
Qed.

Lemma ssa_unchanged_program_var_compat p :
  SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_program_var p).
Proof.
  move=> x y Heq.
  rewrite (eqP Heq).
  reflexivity.
Qed.

Lemma ssa_unchanged_instr_mem v vs i :
  ssa_vars_unchanged_instr vs i ->
  SSAVS.mem v vs ->
  ssa_var_unchanged_instr v i.
Proof.
  move=> Hun Hmem.
  apply: (SSAVS.for_all_2 (ssa_unchanged_instr_var_compat i) Hun).
  apply/bv64SSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_mem v vs p :
  ssa_vars_unchanged_program vs p ->
  SSAVS.mem v vs ->
  ssa_var_unchanged_program v p.
Proof.
  move=> Hun Hmem.
  apply: (SSAVS.for_all_2 (ssa_unchanged_program_var_compat p) Hun).
  apply/bv64SSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_var_unchanged_instr_not_mem v i :
  ssa_var_unchanged_instr v i = ~~ SSAVS.mem v (bv64SSA.lvs_instr i).
Proof.
  case Hmem: (SSAVS.mem v (bv64SSA.lvs_instr i)) => /=.
  - apply/negPn. exact: Hmem.
  - move/negP/idP: Hmem. by apply.
Qed.

Lemma ssa_var_unchanged_program_not_mem v p :
  ssa_var_unchanged_program v p = ~~ SSAVS.mem v (bv64SSA.lvs_program p).
Proof.
  case Hmem: (SSAVS.mem v (bv64SSA.lvs_program p)) => /=.
  - elim: p Hmem => /=.
    + done.
    + move=> hd tl IH Hmem. case: (bv64SSA.VSLemmas.mem_union1 Hmem) =>
                            {Hmem} Hmem.
      * rewrite /ssa_var_unchanged_instr Hmem. done.
      * rewrite (IH Hmem). by case: (ssa_var_unchanged_instr v hd).
  - move/negP/idP: Hmem => Hmem. elim: p Hmem => /=.
    + done.
    + move=> hd tl IH Hmem. move: (bv64SSA.VSLemmas.not_mem_union1 Hmem) =>
                            {Hmem} [Hmem1 Hmem2]. move: (IH Hmem2) => Hun.
      rewrite ssa_var_unchanged_instr_not_mem Hmem1 Hun. done.
Qed.

Lemma ssa_unchanged_instr_global vs i :
  (forall v, SSAVS.mem v vs -> ssa_var_unchanged_instr v i) ->
  ssa_vars_unchanged_instr vs i.
Proof.
  move=> H.
  apply: (SSAVS.for_all_1 (ssa_unchanged_instr_var_compat i)).
  move=> v Hin.
  apply: H; apply/bv64SSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_global vs p :
  (forall v, SSAVS.mem v vs -> ssa_var_unchanged_program v p) ->
  ssa_vars_unchanged_program vs p.
Proof.
  move=> H.
  apply: (SSAVS.for_all_1 (ssa_unchanged_program_var_compat p)).
  move=> v Hin.
  apply: H; apply/bv64SSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_instr_local vs i :
  ssa_vars_unchanged_instr vs i ->
  (forall v, SSAVS.mem v vs -> ssa_var_unchanged_instr v i).
Proof.
  move=> H v Hmem.
  apply: (SSAVS.for_all_2 (ssa_unchanged_instr_var_compat i) H).
  apply/bv64SSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_local vs p :
  ssa_vars_unchanged_program vs p ->
  (forall v, SSAVS.mem v vs -> ssa_var_unchanged_program v p).
Proof.
  move=> H v Hmem.
  exact: (ssa_unchanged_program_mem H Hmem).
Qed.

Lemma ssa_unchanged_program_cons1 vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_instr vs hd /\ ssa_vars_unchanged_program vs tl.
Proof.
  move=> H. move: (ssa_unchanged_program_local H) => {H} H. split.
  - apply: ssa_unchanged_instr_global => v Hmem.
    move: (H v Hmem) => {H} H.
    exact: (proj1 (ssa_var_unchanged_program_cons1 H)).
  - apply: ssa_unchanged_program_global => v Hmem.
    move: (H v Hmem) => {H} H.
    exact: (proj2 (ssa_var_unchanged_program_cons1 H)).
Qed.

Lemma ssa_unchanged_program_cons2 vs hd tl :
  ssa_vars_unchanged_instr vs hd ->
  ssa_vars_unchanged_program vs tl ->
  ssa_vars_unchanged_program vs (hd::tl).
Proof.
  move=> [Hhd Htl]. apply: ssa_unchanged_program_global => v Hmem.
  apply/andP; split.
  - exact: (ssa_unchanged_instr_local Hhd Hmem).
  - exact: (ssa_unchanged_program_local Htl Hmem).
Qed.

Lemma ssa_unchanged_program_concat1 vs p1 p2 :
  ssa_vars_unchanged_program vs (p1 ++ p2) ->
  ssa_vars_unchanged_program vs p1 /\ ssa_vars_unchanged_program vs p2.
Proof.
  move=> H; split; apply: ssa_unchanged_program_global => v Hmem.
  - exact: (proj1 (ssa_var_unchanged_program_concat1
                     (ssa_unchanged_program_local H Hmem))).
  - exact: (proj2 (ssa_var_unchanged_program_concat1
                     (ssa_unchanged_program_local H Hmem))).
Qed.

Lemma ssa_unchanged_program_concat2 vs p1 p2 :
  ssa_vars_unchanged_program vs p1 ->
  ssa_vars_unchanged_program vs p2 ->
  ssa_vars_unchanged_program vs (p1 ++ p2).
Proof.
  move=> Hp1 Hp2. apply: ssa_unchanged_program_global => v Hmem.
  apply: ssa_var_unchanged_program_concat2.
  - exact: (ssa_unchanged_program_local Hp1 Hmem).
  - exact: (ssa_unchanged_program_local Hp2 Hmem).
Qed.

Lemma ssa_unchanged_program_hd vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_instr vs hd.
Proof.
  move=> Hun; move: (ssa_unchanged_program_cons1 Hun) => [Hhd Htl]; assumption.
Qed.

Lemma ssa_unchanged_program_tl vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_program vs tl.
Proof.
  move=> Hun; move: (ssa_unchanged_program_cons1 Hun) => [Hhd Htl]; assumption.
Qed.

Lemma ssa_unchanged_instr_singleton1 v i :
  ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
  ssa_var_unchanged_instr v i.
Proof.
  move=> Hun.
  apply: (ssa_unchanged_instr_mem Hun).
  apply: bv64SSA.VSLemmas.mem_singleton2.
  exact: eqxx.
Qed.

Lemma ssa_unchanged_program_singleton1 v p :
  ssa_vars_unchanged_program (SSAVS.singleton v) p ->
  ssa_var_unchanged_program v p.
Proof.
  move=> Hun.
  apply: (ssa_unchanged_program_mem Hun).
  apply: bv64SSA.VSLemmas.mem_singleton2.
  exact: eqxx.
Qed.

Lemma ssa_unchanged_instr_singleton2 v i :
  ssa_var_unchanged_instr v i ->
  ssa_vars_unchanged_instr (SSAVS.singleton v) i.
Proof.
  move=> Hun.
  apply: ssa_unchanged_instr_global => x Hmem.
  move: (bv64SSA.VSLemmas.mem_singleton1 Hmem) => Heq.
  rewrite (eqP Heq); assumption.
Qed.

Lemma ssa_unchanged_program_singleton2 v p :
  ssa_var_unchanged_program v p ->
  ssa_vars_unchanged_program (SSAVS.singleton v) p.
Proof.
  move=> Hun.
  apply: ssa_unchanged_program_global => x Hmem.
  move: (bv64SSA.VSLemmas.mem_singleton1 Hmem) => Heq.
  rewrite (eqP Heq); assumption.
Qed.

Lemma ssa_unchanged_instr_union1 s1 s2 i :
  ssa_vars_unchanged_instr (SSAVS.union s1 s2) i ->
  ssa_vars_unchanged_instr s1 i /\ ssa_vars_unchanged_instr s2 i.
Proof.
  move=> Hun.
  move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
  split; apply: ssa_unchanged_instr_global => v Hmem.
  - apply: Hun.
    exact: bv64SSA.VSLemmas.mem_union2.
  - apply: Hun.
    exact: bv64SSA.VSLemmas.mem_union3.
Qed.

Lemma ssa_unchanged_program_union1 s1 s2 p :
  ssa_vars_unchanged_program (SSAVS.union s1 s2) p ->
  ssa_vars_unchanged_program s1 p /\ ssa_vars_unchanged_program s2 p.
Proof.
  move=> Hun.
  move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
  split; apply: ssa_unchanged_program_global => v Hmem.
  - apply: Hun.
    exact: bv64SSA.VSLemmas.mem_union2.
  - apply: Hun.
    exact: bv64SSA.VSLemmas.mem_union3.
Qed.

Lemma ssa_unchanged_instr_union2 s1 s2 i :
  ssa_vars_unchanged_instr s1 i -> ssa_vars_unchanged_instr s2 i ->
  ssa_vars_unchanged_instr (SSAVS.union s1 s2) i.
Proof.
  move=> Hun1 Hun2.
  apply: ssa_unchanged_instr_global => x Hmem.
  move: (bv64SSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
  - exact: (ssa_unchanged_instr_mem Hun1 Hmem).
  - exact: (ssa_unchanged_instr_mem Hun2 Hmem).
Qed.

Lemma ssa_unchanged_program_union2 s1 s2 p :
  ssa_vars_unchanged_program s1 p -> ssa_vars_unchanged_program s2 p ->
  ssa_vars_unchanged_program (SSAVS.union s1 s2) p.
Proof.
  move=> Hun1 Hun2.
  apply: ssa_unchanged_program_global => x Hmem.
  move: (bv64SSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
  - exact: (ssa_unchanged_program_mem Hun1 Hmem).
  - exact: (ssa_unchanged_program_mem Hun2 Hmem).
Qed.

Lemma ssa_unchanged_instr_subset vs1 vs2 i :
  ssa_vars_unchanged_instr vs2 i ->
  SSAVS.subset vs1 vs2 ->
  ssa_vars_unchanged_instr vs1 i.
Proof.
  move=> Hun Hsub.
  move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
  apply: ssa_unchanged_instr_global.
  move=> v Hmem; apply: Hun.
  exact: (bv64SSA.VSLemmas.mem_subset Hmem Hsub).
Qed.

Lemma ssa_unchanged_program_subset vs1 vs2 p :
  ssa_vars_unchanged_program vs2 p ->
  SSAVS.subset vs1 vs2 ->
  ssa_vars_unchanged_program vs1 p.
Proof.
  move=> Hun Hsub.
  move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
  apply: ssa_unchanged_program_global.
  move=> v Hmem; apply: Hun.
  exact: (bv64SSA.VSLemmas.mem_subset Hmem Hsub).
Qed.

Lemma ssa_unchanged_instr_add1 v s p :
  ssa_vars_unchanged_instr (SSAVS.add v s) p ->
  ssa_var_unchanged_instr v p /\ ssa_vars_unchanged_instr s p.
Proof.
  move=> H; split.
  - apply: (ssa_unchanged_instr_mem H).
    apply: bv64SSA.VSLemmas.mem_add2.
    exact: SSAVS.E.eq_refl.
  - apply: (ssa_unchanged_instr_subset H).
    exact: (bv64SSA.VSLemmas.subset_add _ (bv64SSA.VSLemmas.subset_refl s)).
Qed.

Lemma ssa_unchanged_instr_add2 v s p :
  ssa_var_unchanged_instr v p /\ ssa_vars_unchanged_instr s p ->
  ssa_vars_unchanged_instr (SSAVS.add v s) p.
Proof.
  move=> [H1 H2].
  apply: ssa_unchanged_instr_global => x Hmem.
  case: (bv64SSA.VSLemmas.mem_add1 Hmem) => {Hmem}.
  - move=> Heq. by rewrite (eqP Heq).
  - move=> Hmem. exact: (ssa_unchanged_instr_mem H2 Hmem).
Qed.

Lemma ssa_unchanged_program_add1 v s p :
  ssa_vars_unchanged_program (SSAVS.add v s) p ->
  ssa_var_unchanged_program v p /\ ssa_vars_unchanged_program s p.
Proof.
  move=> H; split.
  - apply: (ssa_unchanged_program_mem H).
    apply: bv64SSA.VSLemmas.mem_add2.
    exact: SSAVS.E.eq_refl.
  - apply: (ssa_unchanged_program_subset H).
    exact: (bv64SSA.VSLemmas.subset_add _ (bv64SSA.VSLemmas.subset_refl s)).
Qed.

Lemma ssa_unchanged_program_add2 v s p :
  ssa_var_unchanged_program v p /\ ssa_vars_unchanged_program s p ->
  ssa_vars_unchanged_program (SSAVS.add v s) p.
Proof.
  move=> [H1 H2].
  apply: ssa_unchanged_program_global => x Hmem.
  case: (bv64SSA.VSLemmas.mem_add1 Hmem) => {Hmem}.
  - move=> Heq.
    by rewrite (eqP Heq).
  - move=> Hmem.
    exact: (ssa_unchanged_program_mem H2 Hmem).
Qed.

Lemma ssa_unchanged_program_empty vs :
  ssa_vars_unchanged_program vs [::].
Proof.
  apply: ssa_unchanged_program_global => v Hv.
  done.
Qed.

Lemma ssa_unchanged_instr_disjoint_lvs vs i :
  ssa_vars_unchanged_instr vs i =
  bv64SSA.VSLemmas.disjoint vs (bv64SSA.lvs_instr i).
Proof.
  case Hdisj: (bv64SSA.VSLemmas.disjoint vs (bv64SSA.lvs_instr i)).
  - apply: ssa_unchanged_instr_global => v Hmem.
    exact: (bv64SSA.VSLemmas.mem_disjoint1 Hdisj Hmem).
  - apply/negP => Hunch. move/negP: Hdisj; apply.
    move: (ssa_unchanged_instr_local Hunch) => {Hunch} Hunch.
    exact: (bv64SSA.VSLemmas.mem_disjoint3 Hunch).
Qed.

Lemma ssa_unchanged_program_disjoint_lvs vs p :
  ssa_vars_unchanged_program vs p =
  bv64SSA.VSLemmas.disjoint vs (bv64SSA.lvs_program p).
Proof.
  case Hdisj: (bv64SSA.VSLemmas.disjoint vs (bv64SSA.lvs_program p)).
  - elim: p vs Hdisj => /=.
    + move=> vs _. exact: ssa_unchanged_program_empty.
    + move=> hd tl IH vs Hdisj. rewrite bv64SSA.VSLemmas.disjoint_union in Hdisj.
      move/andP: Hdisj => [Hdisjhd Hdisjtl]. apply: ssa_unchanged_program_cons2.
      * rewrite ssa_unchanged_instr_disjoint_lvs. exact: Hdisjhd.
      * exact: (IH _ Hdisjtl).
  - apply/negP => Hunch. move/negP: Hdisj; apply.
    move: (ssa_unchanged_program_local Hunch) => {Hunch} Hunch.
    apply: bv64SSA.VSLemmas.mem_disjoint3. move=> x Hmem.
    move: (Hunch x Hmem). rewrite ssa_var_unchanged_program_not_mem. done.
Qed.

Lemma ssa_unchanged_program_replace vs1 vs2 p :
  SSAVS.Equal vs1 vs2 ->
  ssa_vars_unchanged_program vs1 p ->
  ssa_vars_unchanged_program vs2 p.
Proof.
  move=> Heq H.
  move: (ssa_unchanged_program_local H) => {H} H.
  apply: ssa_unchanged_program_global => v Hv.
  apply: H.
  rewrite Heq.
  assumption.
Qed.

Lemma ssa_single_assignment_cons1 i p :
  ssa_single_assignment (i::p) ->
  (ssa_vars_unchanged_program (bv64SSA.lvs_instr i) p) /\
  (ssa_single_assignment p).
Proof.
  move=> H; apply/andP; exact: H.
Qed.

Lemma ssa_single_assignment_cons2 i p :
  (ssa_vars_unchanged_program (bv64SSA.lvs_instr i) p) ->
  (ssa_single_assignment p) ->
  ssa_single_assignment (i::p).
Proof.
  move=> Hi Hp; by rewrite /ssa_single_assignment -/ssa_single_assignment Hi Hp.
Qed.

Lemma ssa_single_assignment_concat1 p1 p2 :
  ssa_single_assignment (p1 ++ p2) ->
  ssa_single_assignment p1 /\ ssa_single_assignment p2 /\
  (ssa_vars_unchanged_program (bv64SSA.lvs_program p1) p2).
Proof.
  elim: p1 => /=.
  - move=> Hp2; repeat split. exact: Hp2.
  - move=> i p1 IH /andP [Hun12 Hssa12].
    move: (IH Hssa12) => [Hssa1 [Hssa2 Hun2]] => {Hssa12 IH}. repeat split.
    + by rewrite (proj1 (ssa_unchanged_program_concat1 Hun12)) Hssa1.
    + exact: Hssa2.
    + apply: ssa_unchanged_program_union2.
      * exact: (proj2 (ssa_unchanged_program_concat1 Hun12)).
      * exact: Hun2.
Qed.

Lemma ssa_single_assignment_concat2 p1 p2 :
  ssa_single_assignment p1 -> ssa_single_assignment p2 ->
  (ssa_vars_unchanged_program (bv64SSA.lvs_program p1) p2) ->
  ssa_single_assignment (p1 ++ p2).
Proof.
  elim: p1 => /=.
  - move=> _ Hssa2 _. exact: Hssa2.
  - move=> i p1 IH /andP [Hun1 Hssa1] Hssa2 Hun12.
    apply/andP; split.
    + apply: ssa_unchanged_program_concat2.
      * exact: Hun1.
      * apply: (ssa_unchanged_program_subset Hun12).
        apply: bv64SSA.VSLemmas.subset_union1. exact: bv64SSA.VSLemmas.subset_refl.
    + apply: (IH Hssa1 Hssa2). apply: (ssa_unchanged_program_subset Hun12).
      apply: bv64SSA.VSLemmas.subset_union2. exact: bv64SSA.VSLemmas.subset_refl.
Qed.

Lemma well_formed_ssa_vars_unchanged_hd vs hd tl :
  well_formed_ssa_program vs (hd::tl) ->
  ssa_vars_unchanged_program (bv64SSA.vars_instr hd) tl.
Proof.
  move => /andP [/andP [Hwf Huc] Hssa].
  apply: (@ssa_unchanged_program_replace
            (SSAVS.union (bv64SSA.lvs_instr hd) (bv64SSA.rvs_instr hd))).
  - rewrite -bv64SSA.vars_instr_split.
    reflexivity.
  - apply: ssa_unchanged_program_union2.
    + move/andP: Hssa => [Hssa1 Hssa2].
      exact: Hssa1.
    + apply: (@ssa_unchanged_program_subset _ vs).
      * exact: (ssa_unchanged_program_tl Huc).
      * apply: bv64SSA.well_formed_instr_subset_rvs.
        exact: (bv64SSA.well_formed_program_cons1 Hwf).
Qed.

Lemma well_formed_ssa_tl vs hd tl :
  well_formed_ssa_program vs (hd::tl) ->
  well_formed_ssa_program (SSAVS.union vs (bv64SSA.lvs_instr hd)) tl.
Proof.
  move=> Hwfssa.
  move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
  apply/andP; split; first (apply/andP; split).
  - exact: (bv64SSA.well_formed_program_cons2 Hwf).
  - apply: ssa_unchanged_program_union2.
    + exact: (ssa_unchanged_program_tl Huc).
    + move/andP: Hssa => [H _].
      exact: H.
  - move/andP: Hssa => [_ H].
    exact: H.
Qed.

Lemma well_formed_instr_rvs_unchanged_instr vs i i' :
  bv64SSA.well_formed_instr vs i -> ssa_vars_unchanged_instr vs i' ->
  ssa_vars_unchanged_instr (bv64SSA.rvs_instr i) i'.
Proof.
  move=> Hwell Hun. apply: (ssa_unchanged_instr_subset Hun).
  exact: bv64SSA.well_formed_instr_subset_rvs.
Qed.

Lemma well_formed_instr_rvs_unchanged_program vs i p :
  bv64SSA.well_formed_instr vs i -> ssa_vars_unchanged_program vs p ->
  ssa_vars_unchanged_program (bv64SSA.rvs_instr i) p.
Proof.
  move=> Hwell Hun. apply: (ssa_unchanged_program_subset Hun).
  exact: bv64SSA.well_formed_instr_subset_rvs.
Qed.

Lemma ssa_unchanged_instr_eval_singleton v s1 s2 i :
  ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.State.acc v s1 = bv64SSA.State.acc v s2.
Proof.
  move=> Hun Hei.
  move: (ssa_unchanged_instr_singleton1 Hun) => {Hun} Hun.
  exact: (acc_unchanged_instr Hun Hei).
Qed.

Lemma ssa_unchanged_instr_eval_atomic a s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_atomic a) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_atomic a s1 = bv64SSA.eval_atomic a s2.
Proof.
  case: a => /=.
  - move=> v. exact: ssa_unchanged_instr_eval_singleton.
  - reflexivity.
Qed.

Lemma ssa_unchanged_instr_eval_eexp (e : bv64SSA.eexp) s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_eexp e) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_eexp e s1 = bv64SSA.eval_eexp e s2.
Proof.
  elim: e => /=.
  - move=> a Hun Hei. rewrite (ssa_unchanged_instr_eval_singleton Hun Hei).
    reflexivity.
  - reflexivity.
  - move=> op e IH Hun Hei. rewrite (IH Hun Hei); reflexivity.
  - move=> op e1 IH1 e2 IH2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei); reflexivity.
Qed.

Lemma ssa_unchanged_instr_eval_rexp w (e : bv64SSA.rexp w) s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_rexp e) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_rexp e s1 = bv64SSA.eval_rexp e s2.
Proof.
  elim: e => {w} /=.
  - move=> a. exact: ssa_unchanged_instr_eval_singleton.
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei); reflexivity.
  - move=> w e IH n Hun Hei. rewrite (IH Hun Hei); reflexivity.
Qed.

Lemma ssa_unchanged_program_eval_singleton v s1 s2 p :
  ssa_vars_unchanged_program (SSAVS.singleton v) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.State.acc v s1 = bv64SSA.State.acc v s2.
Proof.
  move=> Hun Hep.
  move: (ssa_unchanged_program_singleton1 Hun) => {Hun} Hun.
  exact: (acc_unchanged_program Hun Hep).
Qed.

Lemma ssa_unchanged_program_eval_atomic a s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_atomic a) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_atomic a s1 = bv64SSA.eval_atomic a s2.
Proof.
  case: a => /=.
  - move=> v. exact: ssa_unchanged_program_eval_singleton.
  - reflexivity.
Qed.

Lemma ssa_unchanged_program_eval_eexp (e : bv64SSA.eexp) s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_eexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_eexp e s1 = bv64SSA.eval_eexp e s2.
Proof.
  elim: e => /=.
  - move=> a Hun Hep. rewrite (ssa_unchanged_program_eval_singleton Hun Hep).
    reflexivity.
  - reflexivity.
  - move=> op e IH Hun Hep. rewrite (IH Hun Hep); reflexivity.
  - move=> op e1 IH1 e2 IH2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep); reflexivity.
Qed.

Lemma ssa_unchanged_program_eval_rexp w (e : bv64SSA.rexp w) s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_rexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_rexp e s1 = bv64SSA.eval_rexp e s2.
Proof.
  elim: e => {w} /=.
  - move=> a Hun Hep.
    exact: (ssa_unchanged_program_eval_singleton Hun Hep).
  - reflexivity.
  - move=> w op e1 IH1 e2 IH2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep); reflexivity.
  - move=> w e IH n Hun Hep.
    rewrite (IH Hun Hep); reflexivity.
Qed.

Lemma ssa_unchanged_instr_eval_ebexp e s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_ebexp e) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_ebexp e s1 <-> bv64SSA.eval_ebexp e s2.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_instr_eval_eexp Hun1 Hei)
            (ssa_unchanged_instr_eval_eexp Hun2 Hei).
    done.
  - move=> e1 e2 p Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    move: (ssa_unchanged_instr_union1 Hun2) => {Hun2} [Hun2 Hunp].
    rewrite (ssa_unchanged_instr_eval_eexp Hun1 Hei)
            (ssa_unchanged_instr_eval_eexp Hun2 Hei)
            (ssa_unchanged_instr_eval_eexp Hunp Hei).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei).
    done.
Qed.

Lemma ssa_unchanged_instr_eval_rbexp e s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_rbexp e) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_rbexp e s1 <-> bv64SSA.eval_rbexp e s2.
Proof.
  elim: e => /=.
  - done.
  - done.
  - move=> w op e1 e2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_instr_eval_rexp Hun1 Hei)
            (ssa_unchanged_instr_eval_rexp Hun2 Hei).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hei.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei).
    done.
Qed.

Lemma ssa_unchanged_instr_eval_bexp e s1 s2 i :
  ssa_vars_unchanged_instr (bv64SSA.vars_bexp e) i ->
  bv64SSA.eval_instr s1 i = s2 ->
  bv64SSA.eval_bexp e s1 <-> bv64SSA.eval_bexp e s2.
Proof.
  move=> Hun Hei. move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
  split; move => [H1 H2].
  - exact: (conj (proj1 (ssa_unchanged_instr_eval_ebexp Hun1 Hei) H1)
                 (proj1 (ssa_unchanged_instr_eval_rbexp Hun2 Hei) H2)).
  - exact: (conj (proj2 (ssa_unchanged_instr_eval_ebexp Hun1 Hei) H1)
                 (proj2 (ssa_unchanged_instr_eval_rbexp Hun2 Hei) H2)).
Qed.

Lemma ssa_unchanged_program_eval_ebexp e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_ebexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_ebexp e s1 <-> bv64SSA.eval_ebexp e s2.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_program_eval_eexp Hun1 Hep)
            (ssa_unchanged_program_eval_eexp Hun2 Hep).
    done.
  - move=> e1 e2 n Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    move: (ssa_unchanged_program_union1 Hun2) => {Hun2} [Hun2 Hunp].
    rewrite (ssa_unchanged_program_eval_eexp Hun1 Hep)
            (ssa_unchanged_program_eval_eexp Hun2 Hep)
            (ssa_unchanged_program_eval_eexp Hunp Hep).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep).
    done.
Qed.

Lemma ssa_unchanged_program_eval_ebexp1 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_ebexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_ebexp e s1 -> bv64SSA.eval_ebexp e s2.
Proof.
  move=> Hun Hep He.
  exact: (proj1 (ssa_unchanged_program_eval_ebexp Hun Hep) He).
Qed.

Lemma ssa_unchanged_program_eval_ebexp2 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_ebexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_ebexp e s2 -> bv64SSA.eval_ebexp e s1.
Proof.
  move=> Hun Hep He.
  exact: (proj2 (ssa_unchanged_program_eval_ebexp Hun Hep) He).
Qed.

Lemma ssa_unchanged_program_eval_rbexp e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_rbexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_rbexp e s1 <-> bv64SSA.eval_rbexp e s2.
Proof.
  elim: e => /=.
  - done.
  - done.
  - move=> w op e1 e2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_program_eval_rexp Hun1 Hep)
            (ssa_unchanged_program_eval_rexp Hun2 Hep).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hep.
    move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep).
    done.
Qed.

Lemma ssa_unchanged_program_eval_rbexp1 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_rbexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_rbexp e s1 -> bv64SSA.eval_rbexp e s2.
Proof.
  move=> Hun Hep He.
  exact: (proj1 (ssa_unchanged_program_eval_rbexp Hun Hep) He).
Qed.

Lemma ssa_unchanged_program_eval_rbexp2 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_rbexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_rbexp e s2 -> bv64SSA.eval_rbexp e s1.
Proof.
  move=> Hun Hep He.
  exact: (proj2 (ssa_unchanged_program_eval_rbexp Hun Hep) He).
Qed.

Lemma ssa_unchanged_program_eval_bexp e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_bexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_bexp e s1 <-> bv64SSA.eval_bexp e s2.
Proof.
  move=> Hun Hep. move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
  split; move=> [H1 H2].
  - exact: (conj (proj1 (ssa_unchanged_program_eval_ebexp Hun1 Hep) H1)
                 (proj1 (ssa_unchanged_program_eval_rbexp Hun2 Hep) H2)).
  - exact: (conj (proj2 (ssa_unchanged_program_eval_ebexp Hun1 Hep) H1)
                 (proj2 (ssa_unchanged_program_eval_rbexp Hun2 Hep) H2)).
Qed.

Lemma ssa_unchanged_program_eval_bexp1 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_bexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_bexp e s1 -> bv64SSA.eval_bexp e s2.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_unchanged_program_eval_bexp2 e s1 s2 p :
  ssa_vars_unchanged_program (bv64SSA.vars_bexp e) p ->
  bv64SSA.eval_program s1 p = s2 ->
  bv64SSA.eval_bexp e s2 -> bv64SSA.eval_bexp e s1.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H2 He).
Qed.

Corollary well_formed_ssa_spec_program vs s :
  well_formed_ssa_spec vs s ->
  well_formed_ssa_program vs (bv64SSA.sprog s).
Proof.
  move=> /andP [/andP [/andP [/andP [Hpre Hwell] Hprog] Hvs] Hssa].
  rewrite /well_formed_ssa_program Hwell Hvs Hssa.
  done.
Qed.

Corollary well_formed_ssa_spec_pre_unchanged vs s :
  well_formed_ssa_spec vs s ->
  ssa_vars_unchanged_program (bv64SSA.vars_bexp (bv64SSA.spre s)) (bv64SSA.sprog s).
Proof.
  move=> /andP [/andP [/andP [/andP [Hf Hp] Hg] Hun] Hssa].
  exact: (ssa_unchanged_program_subset Hun Hf).
Qed.

Corollary well_formed_ssa_spec_post_subset vs s :
  well_formed_ssa_spec vs s ->
  SSAVS.subset (bv64SSA.vars_bexp (bv64SSA.spost s))
                    (SSAVS.union vs (bv64SSA.vars_program (bv64SSA.sprog s))).
Proof.
  move=> /andP [/andP [/andP [/andP [Hf Hp] Hg] Hun] Hssa].
  exact: Hg.
Qed.

Ltac le_ssa_var_unchanged_instr :=
  match goal with
  | H : ssa_instr _ _ = (_, _) |- _ =>
    case: H; move=> _ <-; le_ssa_var_unchanged_instr
  | |- is_true (ssa_var_unchanged_instr (?v, ?iv) ?i) =>
    rewrite /ssa_var_unchanged_instr /=; le_ssa_var_unchanged_instr
  | H : is_true (?iv <=? get_index ?v ?m)
    |- is_true (~~ SSAVS.mem (?v, ?iv)
                   (SSAVS.singleton (ssa_var (upd_index ?x ?m) ?x))) =>
    let Hmem := fresh in
    let Heq := fresh in
    let Hv := fresh in
    let Hi := fresh in
    apply/negP => /= Hmem;
    move: (bv64SSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} => Heq;
    move/eqP: Heq => [Hv Hi];
    rewrite Hv Hi in H;
    exact: (get_upd_index_leF H)
  | H : is_true (?iv <=? get_index ?v ?m)
    |- is_true (~~ SSAVS.mem (?v, ?iv)
                   (SSAVS.add
                      (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1)
                      (SSAVS.singleton (ssa_var (upd_index ?v2 ?m) ?v2)))) =>
    let Hmem := fresh in
    let Hv := fresh in
    let Hi := fresh in
    apply/negP => /= Hmem;
    move: (bv64SSA.VSLemmas.mem_add1 Hmem); case => {Hmem} Hmem;
    [ move/eqP: Hmem => [Hv Hi]; rewrite Hv Hi in H;
      apply: (@get_upd_index_leF (upd_index v2 m) v1);
      apply: (Nleq_trans H); exact: get_upd_index_le
    |
      move: (bv64SSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} Hmem;
      move/eqP: Hmem => [Hv Hi]; rewrite Hv Hi in H;
      exact: (@get_upd_index_leF m v2)
    ]
  | |- _ => idtac
  end.

Lemma ssa_instr_le_unchanged m1 m2 i si :
  forall v iv,
    iv <=? get_index v m1 ->
    ssa_instr m1 i = (m2, si) ->
    ssa_var_unchanged_instr (v, iv) si.
Proof.
  elim: i m1 m2 si; intros; by le_ssa_var_unchanged_instr.
Qed.

Lemma ssa_program_le_unchanged m1 m2 p sp :
  forall v i,
    i <=? get_index v m1 ->
    ssa_program m1 p = (m2, sp) ->
    ssa_var_unchanged_program (v, i) sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp v i Hi /= [Hm Hp].
    by rewrite -Hp.
  - move=> hd tl IH m1 m2 sp v i Hle Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp => {Hsp sp} /=.
    apply/andP; split.
    + exact: (ssa_instr_le_unchanged Hle Hshd).
    + move: (ssa_instr_index_le v Hshd) => Hle2.
      move: (Nleq_trans Hle Hle2) => {Hle Hle2} Hle.
      exact: (IH _ _ _ _ _ Hle Hstl).
Qed.

Ltac ssa_lv_hd_unchanged_tl :=
  match goal with
  | Hstl : ssa_program ?m3 ?tl = (?m2, ?stl),
    H : ssa_instr ?m1 ?hd = (?m3, ?shd)
    |- _ =>
    move: Hstl; case: H => <- <- /= Hstl; ssa_lv_hd_unchanged_tl
  | Hstl : ssa_program (upd_index ?v ?m1) ?tl = (?m2, ?stl)
    |- is_true (ssa_vars_unchanged_program
                  (SSAVS.singleton (ssa_var (upd_index ?v ?m1) ?v)) ?stl) =>
    apply: ssa_unchanged_program_singleton2;
    apply: (ssa_program_le_unchanged _ Hstl);
    exact: Nleqnn
  | Hstl : ssa_program (upd_index ?v1 (upd_index ?v2 ?m1)) ?tl = (?m2, ?stl)
    |- is_true (ssa_vars_unchanged_program
                  (SSAVS.add
                     (ssa_var (upd_index ?v1 (upd_index ?v2 ?m1)) ?v1)
                     (SSAVS.singleton
                        (ssa_var (upd_index ?v2 ?m1) ?v2))) ?stl) =>
    apply: ssa_unchanged_program_add2; split;
    [ apply: (ssa_program_le_unchanged _ Hstl);
      exact: Nleqnn
    | apply ssa_unchanged_program_singleton2;
      apply: (ssa_program_le_unchanged _ Hstl);
      exact: get_upd_index_le ]
  | |- _ => idtac
  end.

Theorem ssa_program_single_assignment m1 m2 p sp :
  ssa_program m1 p = (m2, sp) ->
  ssa_single_assignment sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp [] _ <-.
    done.
  - move=> hd tl IH m1 m2 sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl ->]]]]].
    apply/andP; split.
    + case: hd Hshd; intros; by ssa_lv_hd_unchanged_tl.
    + exact: (IH _ _ _ Hstl).
Qed.

Lemma ssa_instr_well_formed vs m1 m2 i si :
  well_formed_instr vs i ->
  ssa_instr m1 i = (m2, si) ->
  bv64SSA.well_formed_instr (ssa_vars m1 vs) si.
Proof.
  case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ => case: H => _ <- /=; tac
       | H : is_true (_ && _) |- _ =>
         let H1 := fresh in
         let H2 := fresh in
         move/andP: H => [H1 H2]; tac
       | |- is_true (_ && _) => apply/andP; split; tac
       | H : is_true (VS.subset (vars_atomic ?a) ?vs)
         |- is_true (SSAVS.subset
                       (bv64SSA.vars_atomic (ssa_atomic ?m ?a))
                       (ssa_vars ?m ?vs)) =>
         rewrite ssa_vars_atomic_subset; assumption
       | H : is_true (?v1 != ?v2)
         |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                             ssa_var (upd_index ?v2 ?m) ?v2) =>
         exact: (pair_neq1 _ _ H)
       | H : is_true (VS.mem ?v ?vs) |-
         is_true (SSAVS.mem (ssa_var ?m ?v) (ssa_vars ?m ?vs)) =>
         rewrite ssa_vars_mem1; exact: H
       | |- _ => idtac
       end in
   tac).
Qed.

Definition dclosed m ivs lvs svs : Prop :=
  (* Indices of unused variables should not be updated. *)
  (forall v, ~~ VS.mem v (VS.union ivs lvs) -> get_index v m = 0) /\
  (* The index of a variable in lvs should start from 1. *)
  (forall v, VS.mem v lvs -> 0 <? get_index v m) /\
  (* svs contains all versions of ivs and lvs. *)
  (forall v i, SSAVS.mem (v, i) svs = (VS.mem v ivs) && (i <=? get_index v m) || (VS.mem v lvs) && (0 <? i <=? get_index v m)).

Lemma dclosed_lvs_idx_gt0 m ivs lvs svs v :
  dclosed m ivs lvs svs -> VS.mem v lvs -> 0 <? get_index v m.
Proof.
  move=> [_ [H _]]. exact: H.
Qed.

Lemma dclosed_not_mem m ivs lvs svs v :
  dclosed m ivs lvs svs ->
  ~~ VS.mem v (VS.union ivs lvs) ->
  get_index v m = 0.
Proof.
  move=> [Hd _] Hmem.
  exact: (Hd v Hmem).
Qed.

Lemma dclosed_mem1 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  SSAVS.mem (v, i) svs ->
  (VS.mem v ivs) /\ (i <=? get_index v m) \/
                    (VS.mem v lvs) /\ (0 <? i <=? get_index v m).
Proof.
  move=> [_ [_ Hd]] Hmem.
  rewrite Hd in Hmem.
  case: (orP Hmem) => {Hmem} /andP H.
  - left; assumption.
  - right; assumption.
Qed.

Lemma dclosed_mem2 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  VS.mem v ivs -> i <=? get_index v m ->
  SSAVS.mem (v, i) svs.
Proof.
  move=> [_ [_ Hd]] Hmem Hi.
  rewrite Hd.
  apply/orP; left; apply/andP; split; assumption.
Qed.

Lemma dclosed_mem3 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  VS.mem v lvs -> 0 <? i <=? get_index v m ->
  SSAVS.mem (v, i) svs.
Proof.
  move=> [_ [_ Hd]] Hmem Hi.
  rewrite Hd.
  apply/orP; right; apply/andP; split; assumption.
Qed.

Lemma dclosed_mem4 m ivs lvs svs v :
  dclosed m ivs lvs svs ->
  VS.mem v lvs -> 0 <? get_index v m.
Proof.
  move=> [_ [Hd _]] Hmem.
  exact: (Hd _ Hmem).
Qed.

Lemma dclosed_mem5 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index v m ->
  SSAVS.mem (v, i) svs.
Proof.
  move=> Hd Hi.
  case Hmem: (VS.mem v (VS.union ivs lvs)).
  - case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + move/andP: Hi => [Hi1 Hi2].
      exact: (dclosed_mem2 Hd Hmem Hi2).
    + exact: (dclosed_mem3 Hd Hmem Hi).
  - move/idP/negP: Hmem => Hmem.
    rewrite (dclosed_not_mem Hd Hmem) in Hi.
    move/andP: Hi => [Hi1 Hi2].
    rewrite Nleqn0 in Hi2.
    rewrite (eqP Hi2) Nltnn in Hi1.
    discriminate.
Qed.

Lemma dclosed_mem6 m ivs lvs svs v :
  dclosed m ivs lvs svs ->
  VS.mem v (VS.union ivs lvs) ->
  SSAVS.mem (ssa_var m v) svs.
Proof.
  move=> Hd Hmv. set sv := ssa_var m v. have: sv = ssa_var m v by reflexivity.
  destruct sv as [x i]. move=> [] -> ->. case: (VSLemmas.mem_union1 Hmv) => {Hmv} Hmv.
  - apply: (dclosed_mem2 Hd Hmv). exact: N.leb_refl.
  - apply: (dclosed_mem3 Hd Hmv). rewrite (dclosed_lvs_idx_gt0 Hd Hmv) N.leb_refl.
    done.
Qed.

Lemma dclosed_empty vs :
  dclosed empty_vmap vs VS.empty (ssa_vars empty_vmap vs).
Proof.
  split; first by reflexivity.
  split; first by discriminate.
  move=> v i.
  case Hmem: (VS.mem v vs && (i <=? get_index v empty_vmap)
              || [&& VS.mem v VS.empty, 0 <? i & i <=? get_index v empty_vmap]).
  - case: (orP Hmem) => {Hmem} /andP [Hmem Hidx].
    + apply: (ssa_vars_mem3 Hmem).
      rewrite get_index_empty Nleqn0 in Hidx *.
      exact: (eqP Hidx).
    + discriminate.
  - apply/negP => H.
    move/negP: Hmem; apply.
    move: (ssa_vars_mem2 H) => [y [[Hy Hidy] Hmemy]].
    apply/orP; left; apply/andP; split.
    + rewrite Hy; exact: Hmemy.
    + rewrite Hidy Hy; exact: Nleqnn.
Qed.

Lemma dclosed_subset m ivs lvs svs :
  dclosed m ivs lvs svs ->
  SSAVS.subset (ssa_vars m (VS.union ivs lvs)) svs.
Proof.
  move=> [Hd1 [Hd2 Hd3]].
  apply: SSAVS.subset_1 => x /bv64SSA.VSLemmas.memP Hmem.
  apply/bv64SSA.VSLemmas.memP.
  move: Hmem; rewrite ssa_vars_union => Hmem.
  destruct x as [x i].
  rewrite Hd3; apply/orP.
  case: (bv64SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
  - left.
    move: (ssa_vars_mem2 Hmem) => [y [[Hxy Hidx] Hmemy]].
    apply/andP; split.
    + rewrite Hxy; exact: Hmemy.
    + rewrite Hidx Hxy; exact: Nleqnn.
  - right.
    move: (ssa_vars_mem2 Hmem) => [y [[Hxy Hidx] Hmemy]].
    apply/andP; split.
    + rewrite Hxy; exact: Hmemy.
    + move: (Hd2 _ Hmemy) => H.
      rewrite Hxy Hidx; apply/andP; split.
      * assumption.
      * exact: Nleqnn.
Qed.

Ltac dclosed_instr_well_formed_tac :=
  match goal with
  | H : (_, _) = (_, _) |- _ =>
    case: H => _ <- /=; dclosed_instr_well_formed_tac
  | H : is_true (_ && _) |- _ =>
    let H1 := fresh in
    let H2 := fresh in
    move/andP: H => [H1 H2]; dclosed_instr_well_formed_tac
  | |- is_true (_ && _) => apply/andP; split; dclosed_instr_well_formed_tac
  | Hs : is_true (VS.subset (vars_atomic ?a) (VS.union ?ivs ?lvs)),
    Hd : dclosed ?m1 ?ivs ?lvs ?svs
    |- is_true (SSAVS.subset
                  (bv64SSA.vars_atomic (ssa_atomic ?m1 ?a))
                  ?svs) =>
    apply: (bv64SSA.VSLemmas.subset_trans (s2:=ssa_vars m1 (VS.union ivs lvs)));
    [ rewrite ssa_vars_atomic_subset;
      assumption
    | exact: dclosed_subset ]
  | H : is_true (?v1 != ?v2)
    |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                        ssa_var (upd_index ?v2 ?m) ?v2) =>
    exact: (pair_neq1 _ _ H)
  | H1 : dclosed ?m ?ivs ?lvs ?svs,
    H2 : is_true (VS.mem ?v (VS.union ?ivs ?lvs)) |-
    is_true (SSAVS.mem (ssa_var ?m ?v) ?svs) =>
    exact: (dclosed_mem6 H1 H2)
  | |- _ => idtac
  end.

Lemma dclosed_instr_well_formed ivs lvs svs m1 m2 i si :
  well_formed_instr (VS.union ivs lvs) i ->
  ssa_instr m1 i = (m2, si) ->
  dclosed m1 ivs lvs svs ->
  bv64SSA.well_formed_instr svs si.
Proof.
  case: i => /=; intros; by dclosed_instr_well_formed_tac.
Qed.

Lemma dclosed_upd1 m ivs lvs svs v x i :
  dclosed m ivs lvs svs ->
  VS.mem x ivs ->
  i <=? get_index x (upd_index v m) ->
  SSAVS.mem (x, i) (SSAVS.add (ssa_var (upd_index v m) v) svs).
Proof.
  move=> Hd Hmem Hi.
  case Hxv: (x == v).
  - rewrite (eqP Hxv) in Hmem Hi *.
    rewrite Nleq_eqVlt in Hi.
    case: (orP Hi) => {Hi} Hi.
    + rewrite /ssa_var -(eqP Hi).
      apply: bv64SSA.VSLemmas.mem_add2.
      exact: SSAVS.E.eq_refl.
    + rewrite get_upd_index_eq NltnS in Hi.
      apply: bv64SSA.VSLemmas.mem_add3.
      exact: (dclosed_mem2 Hd Hmem Hi).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv) in Hi.
    apply: bv64SSA.VSLemmas.mem_add3.
    exact: (dclosed_mem2 Hd Hmem Hi).
Qed.

Lemma dclosed_upd2 m ivs lvs svs v x i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index x (upd_index v m) ->
  SSAVS.mem (x, i) (SSAVS.add (ssa_var (upd_index v m) v) svs).
Proof.
  move=> Hd /andP [Hi1 Hi2].
  case Hxv: (x == v).
  - rewrite (eqP Hxv) in Hi2 * => {x Hxv}.
    rewrite Nleq_eqVlt in Hi2.
    case: (orP Hi2) => {Hi2} Hi2.
    + apply: bv64SSA.VSLemmas.mem_add2.
      rewrite /ssa_var -(eqP Hi2).
      exact: eqxx.
    + rewrite get_upd_index_eq NltnS in Hi2.
      apply: bv64SSA.VSLemmas.mem_add3.
      have: 0 <? i <=? get_index v m by rewrite Hi1 Hi2.
      move=> Hi.
      exact: (dclosed_mem5 Hd Hi).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv) in Hi2.
    have: 0 <? i <=? get_index x m by rewrite Hi1 Hi2.
    move=> Hi.
    apply: bv64SSA.VSLemmas.mem_add3.
    exact: (dclosed_mem5 Hd Hi).
Qed.

Lemma dclosed_upd3 m ivs lvs svs vh vl x i :
  dclosed m ivs lvs svs ->
  VS.mem x ivs ->
  i <=? get_index x (upd_index vh (upd_index vl m)) ->
  SSAVS.mem (x, i)
             (SSAVS.add (ssa_var (upd_index vh (upd_index vl m)) vh)
                         (SSAVS.add (ssa_var (upd_index vl m) vl) svs)).
Proof.
  move=> Hd Hmem Hi. case Hxh: (x == vh).
  - rewrite (eqP Hxh) in Hi Hmem * => {x Hxh}. rewrite Nleq_eqVlt in Hi.
    case: (orP Hi) => {Hi} Hi.
    + apply: bv64SSA.VSLemmas.mem_add2. rewrite /ssa_var -(eqP Hi). exact: eqxx.
    + apply: bv64SSA.VSLemmas.mem_add3. rewrite get_upd_index_eq NltnS in Hi.
      exact: (dclosed_upd1 Hd Hmem Hi).
  - move/idP/negP: Hxh => Hxh. rewrite (get_upd_index_neq _ Hxh) in Hi.
    apply: bv64SSA.VSLemmas.mem_add3. exact: (dclosed_upd1 Hd Hmem Hi).
Qed.

Lemma dclosed_upd4 m ivs lvs svs vh vl x i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index x (upd_index vh (upd_index vl m)) ->
  SSAVS.mem (x, i)
             (SSAVS.add (ssa_var (upd_index vh (upd_index vl m)) vh)
                         (SSAVS.add (ssa_var (upd_index vl m) vl) svs)).
Proof.
  move=> Hd /andP [Hi1 Hi2]. case Hxh: (x == vh).
  - rewrite (eqP Hxh) in Hi2 * => {x Hxh}. rewrite Nleq_eqVlt in Hi2.
    case: (orP Hi2) => {Hi2} Hi2.
    + apply: bv64SSA.VSLemmas.mem_add2. rewrite /ssa_var -(eqP Hi2).
      exact: eqxx.
    + rewrite get_upd_index_eq NltnS in Hi2.
      have: 0 <? i <=? get_index vh (upd_index vl m) by rewrite Hi1 Hi2.
      move=> Hi. apply: bv64SSA.VSLemmas.mem_add3. exact: (dclosed_upd2 Hd Hi).
  - move/idP/negP: Hxh => Hxh.
    rewrite (get_upd_index_neq _ Hxh) in Hi2.
    have: 0 <? i <=? get_index x (upd_index vl m) by rewrite Hi1 Hi2.
    move=> Hi.
    apply: bv64SSA.VSLemmas.mem_add3. exact: (dclosed_upd2 Hd Hi).
Qed.

Lemma dclosed_upd_cond1 m ivs lvs svs v x :
  dclosed m ivs lvs svs ->
  ~~ VS.mem x (VS.union ivs (VS.union lvs (VS.singleton v))) ->
  get_index x (upd_index v m) = 0.
Proof.
  move=> Hd.
  rewrite -VSLemmas.OP.P.union_assoc => Hm.
  move: (VSLemmas.not_mem_union1 Hm) => {Hm} [Hm1 Hm2].
  move: (VSLemmas.not_mem_singleton1 Hm2) => /negP Hne.
  rewrite (get_upd_index_neq _ Hne).
  exact: (dclosed_not_mem Hd Hm1).
Qed.

Lemma dclosed_upd2_cond1 m ivs lvs svs v1 v2 x :
  dclosed m ivs lvs svs ->
  ~~ VS.mem x (VS.union ivs (VS.union lvs (VS.add v1 (VS.singleton v2)))) ->
  get_index x (upd_index v1 (upd_index v2 m)) = 0.
Proof.
  move=> Hd.
  rewrite -VSLemmas.OP.P.union_assoc => Hm.
  move: (VSLemmas.not_mem_union1 Hm) => {Hm} [Hm0 Hm].
  move: (VSLemmas.not_mem_add1 Hm) => {Hm} [/negP Hne1 Hm].
  move: (VSLemmas.not_mem_singleton1 Hm) => {Hm} /negP Hne2.
  rewrite (get_upd_index_neq _ Hne1) (get_upd_index_neq _ Hne2).
  exact: (dclosed_not_mem Hd Hm0).
Qed.

Lemma dclosed_upd_cond2 m ivs lvs svs v x :
  dclosed m ivs lvs svs ->
  VS.mem x (VS.union lvs (VS.singleton v)) ->
  0 <? get_index x (upd_index v m).
Proof.
  move=> Hd Hm.
  case: (VSLemmas.mem_union1 Hm) => {Hm} Hm.
  - move: (dclosed_mem4 Hd Hm) => Hlt.
    exact: (Nltn_leq_trans Hlt (get_upd_index_le m x v)).
  - move: (VSLemmas.mem_singleton1 Hm) => /eqP ->.
    exact: get_upd_index_gt0.
Qed.

Lemma dclosed_upd2_cond2 m ivs lvs svs v1 v2 x  :
  dclosed m ivs lvs svs ->
  VS.mem x (VS.union lvs (VS.add v1 (VS.singleton v2))) ->
  0 <? get_index x (upd_index v1 (upd_index v2 m)).
Proof.
  move=> Hd Hm.
  case: (VSLemmas.mem_union1 Hm) => {Hm} Hm.
  - move: (dclosed_mem4 Hd Hm) => Hlt.
    move: (Nltn_leq_trans Hlt (get_upd_index_le m x v2)) => {Hlt} Hlt.
    exact: (Nltn_leq_trans Hlt (get_upd_index_le (upd_index v2 m) x v1)).
  - move: (VSLemmas.mem_add1 Hm) => {Hm} [] Hm.
    + rewrite (eqP Hm).
      exact: (get_upd_index_gt0 (upd_index v2 m) v1) => Hlt.
    + move: (VSLemmas.mem_singleton1 Hm) => /eqP ->.
      move: (get_upd_index_le (upd_index v2 m) v2 v1) => Hle.
      move: (get_upd_index_gt0 m v2) => Hlt.
      exact: (Nltn_leq_trans Hlt Hle).
Qed.

Lemma dclosed_upd_cond3 m ivs lvs svs v x i :
  dclosed m ivs lvs svs ->
  SSAVS.mem (x, i)
                 (SSAVS.union
                    svs
                    (SSAVS.singleton (ssa_var (upd_index v m) v))) =
  VS.mem x ivs && (i <=? get_index x (upd_index v m))
  || [&& VS.mem x (VS.union lvs (VS.singleton v)),
      0 <? i & i <=? get_index x (upd_index v m)].
Proof.
  move=> Hd.
  set m2 := upd_index v m.
  case H: (VS.mem x ivs && (i <=? get_index x m2) ||
           [&& VS.mem x (VS.union lvs (VS.singleton v)),
            0 <? i & i <=? get_index x m2]).
  - case: (orP H) => {H} /andP [Hm Hi].
    + rewrite bv64SSA.VSLemmas.OP.P.union_sym
              -bv64SSA.VSLemmas.OP.P.add_union_singleton.
      exact: (dclosed_upd1 Hd Hm Hi).
    + rewrite bv64SSA.VSLemmas.OP.P.union_sym
              -bv64SSA.VSLemmas.OP.P.add_union_singleton.
      exact: (dclosed_upd2 Hd Hi).
  - apply/negP => Hmemx.
    move/negP: H; apply.
    apply/orP.
    case: (bv64SSA.VSLemmas.mem_union1 Hmemx) => {Hmemx} Hmemx.
    + move: (dclosed_mem1 Hd Hmemx); case; move => [Hx Hi].
      * left; apply/andP; split; first by exact: Hx.
        exact: (Nleq_trans Hi (get_upd_index_le m x v)).
      * right; apply/andP; split;
          first by apply: VSLemmas.mem_union2; exact: Hx.
        move/andP: Hi => [Hi1 Hi2].
        apply/andP; split; first by exact: Hi1.
        exact: (Nleq_trans Hi2 (get_upd_index_le m x v)).
    + move: (bv64SSA.VSLemmas.mem_singleton1 Hmemx) => {Hmemx} /eqP [Hx Hi].
      right; apply/andP; split.
      * rewrite Hx; apply: VSLemmas.mem_union3;
          exact: VSLemmas.mem_singleton2.
      * rewrite Hx; apply/andP; split; last by rewrite Hi; exact: Nleqnn.
        rewrite Hi.
        exact: (get_upd_index_gt0).
Qed.

Lemma dclosed_upd2_cond3 m ivs lvs svs v1 v2 x i :
  dclosed m ivs lvs svs ->
  SSAVS.mem
    (x, i)
    (SSAVS.union
       svs
       (SSAVS.add
          (ssa_var (upd_index v1 (upd_index v2 m)) v1)
          (SSAVS.singleton (ssa_var (upd_index v2 m) v2)))) =
  VS.mem x ivs &&
         (i <=? get_index x (upd_index v1 (upd_index v2 m)))
  || [&& VS.mem x (VS.union lvs (VS.add v1 (VS.singleton v2))),
      0 <? i & i <=? get_index x (upd_index v1 (upd_index v2 m))].
Proof.
  move=> Hd.
  rewrite bv64SSA.VSLemmas.OP.P.add_union_singleton.
  rewrite (bv64SSA.VSLemmas.OP.P.union_sym (SSAVS.singleton _)).
  rewrite -bv64SSA.VSLemmas.OP.P.union_assoc.
  rewrite (bv64SSA.VSLemmas.OP.P.union_sym svs).
  rewrite (bv64SSA.VSLemmas.OP.P.union_sym _ (SSAVS.singleton _)).
  rewrite -bv64SSA.VSLemmas.OP.P.add_union_singleton.
  rewrite -bv64SSA.VSLemmas.OP.P.add_union_singleton.
  set m3 := upd_index v2 m.
  set m2 := (upd_index v1 (upd_index v2 m)).
  case H:  (VS.mem x ivs && (i <=? get_index x m2) ||
            [&& VS.mem x (VS.union lvs (VS.add v1 (VS.singleton v2))),
             0 <? i & i <=? get_index x m2]).
  - case: (orP H) => {H} /andP [Hmem Hi].
    + exact: (dclosed_upd3 Hd Hmem Hi).
    + exact: (dclosed_upd4 Hd Hi).
  - apply/negP => Hmem. move/negP: H; apply. apply/orP.
    case: (bv64SSA.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem;
    [ idtac | case: (bv64SSA.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem ].
    + move/eqP: Hmem => [Hv Hi]. right; apply/andP; split.
      * apply: VSLemmas.mem_union3. apply: VSLemmas.mem_add2.
        rewrite Hv; exact: eqxx.
      * rewrite Hi. apply/andP; split.
        -- exact: get_upd_index_gt0.
        -- rewrite Hv. exact: Nleqnn.
    + move/eqP: Hmem => [Hv Hi]. right; apply/andP; split.
      * apply: VSLemmas.mem_union3. apply: VSLemmas.mem_add3.
        apply: VSLemmas.mem_singleton2. rewrite Hv; exact: eqxx.
      * rewrite Hi. apply/andP; split.
        -- exact: get_upd_index_gt0.
        -- rewrite Hv. exact: get_upd_index_le.
    + move: (get_upd_index_le m x v2) => Hle1.
      move: (get_upd_index_le (upd_index v2 m) x v1) => Hle2.
      move: (Nleq_trans Hle1 Hle2) => {Hle1 Hle2} Hle.
      case: (dclosed_mem1 Hd Hmem); move=> [Hv Hi].
      * left; apply/andP; split; first by assumption.
        exact: (Nleq_trans Hi Hle).
      * right; apply/andP; split; first by apply: VSLemmas.mem_union2.
        move/andP: Hi => [Hi1 Hi2]. apply/andP; split; first by assumption.
        exact: (Nleq_trans Hi2 Hle).
Qed.

(* one lval *)
Lemma dclosed_succ1 v ivs lvs svs m :
  dclosed m ivs lvs svs ->
  dclosed (upd_index v m) ivs (VS.union lvs (VS.singleton v))
          (SSAVS.union
             svs
             (SSAVS.singleton (ssa_var (upd_index v m) v))).
Proof.
  move=> Hd; split;
  [ move=> x Hm; exact: (dclosed_upd_cond1 Hd Hm) |
    split;
    [ move=> x Hm; exact: (dclosed_upd_cond2 Hd Hm)
    | move=> x n; exact: (dclosed_upd_cond3 _ _ _ Hd)
    ]
  ].
Qed.

(* two lvals *)
Lemma dclosed_succ2 v1 v2 ivs lvs svs m  :
  dclosed m ivs lvs svs ->
  dclosed (upd_index v1 (upd_index v2 m)) ivs
    (VS.union lvs (VS.add v1 (VS.singleton v2)))
    (SSAVS.union
       svs
       (SSAVS.add
          (ssa_var (upd_index v1 (upd_index v2 m)) v1)
          (SSAVS.singleton (ssa_var (upd_index v2 m) v2)))).
Proof.
  move=> Hd; split;
  [ move=> x Hm; exact: (dclosed_upd2_cond1 Hd Hm)
  | split;
    [ move=> x Hm; exact: (dclosed_upd2_cond2 Hd Hm)
    | move=> x n; exact: (dclosed_upd2_cond3 _ _ _ _ Hd)
    ]
  ].
Qed.

Corollary dclosed_instr_succ ivs lvs svs m1 m2 i si :
  dclosed m1 ivs lvs svs ->
  ssa_instr m1 i = (m2, si) ->
  dclosed m2 ivs (VS.union lvs (lvs_instr i)) (SSAVS.union svs (bv64SSA.lvs_instr si)).
Proof.
  move=> Hd; case: i => /=; intros;
  (let rec tac :=
       match goal with
       | H : (_, _) = (_, _) |- _ =>
         case: H => <- <- /=; tac
       | H : dclosed ?m1 ?ivs ?lvs ?svs
         |- dclosed ?m2 ?ivs (VS.union ?lvs (VS.singleton ?v))
                    (SSAVS.union
                       ?svs (SSAVS.singleton (ssa_var ?m2 ?v))) =>
         exact: dclosed_succ1
       | H : dclosed ?m1 ?ivs ?lvs ?svs
         |- dclosed
              ?m3 ?ivs
              (VS.union ?lvs (VS.add ?v1 (VS.singleton ?v2)))
              (SSAVS.union
                 ?svs
                 (SSAVS.add (ssa_var ?m3 ?v1)
                                 (SSAVS.singleton (ssa_var ?m2 ?v2)))) =>
         exact: dclosed_succ2
       | |- _ => idtac
       end in
   tac).
Qed.

Theorem dclosed_program_well_formed ivs lvs svs m1 m2 p sp :
  well_formed_program (VS.union ivs lvs) p ->
  ssa_program m1 p = (m2, sp) ->
  dclosed m1 ivs lvs svs ->
  well_formed_ssa_program svs sp.
Proof.
  move=> Hwell Hssa Hd.
  apply/andP; split; [apply/andP; split | idtac].
  - elim: p ivs lvs svs m1 m2 sp Hwell Hssa Hd => /=.
    + move=> ivs lvs svs m1 m2 sp _ [Hm Hsp] Hd.
      rewrite -Hsp.
      done.
    + move=> hd tl IH ivs lvs svs m1 m2 sp /andP [Hhd Htl] Hsp Hd.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
      rewrite Hsp => {Hsp sp}.
      apply/andP; split.
      * exact: (dclosed_instr_well_formed Hhd Hshd).
      * apply: (IH ivs (VS.union lvs (lvs_instr hd)) _ _ _ _ _ Hstl);
          last by exact: (dclosed_instr_succ Hd Hshd).
        apply: (well_formed_program_replace Htl).
        rewrite VSLemmas.OP.P.union_assoc.
        rewrite (VSLemmas.OP.P.union_sym lvs (lvs_instr hd)).
        reflexivity.
  - apply: ssa_unchanged_program_global => v Hmem.
    destruct v as [v i].
    apply: (ssa_program_le_unchanged _ Hssa).
    case: (dclosed_mem1 Hd Hmem) => {Hmem}; case => Hmem Hi.
    + exact: Hi.
    + move/andP: Hi => [Hi1 Hi2].
      exact: Hi2.
  - exact: (ssa_program_single_assignment Hssa).
Qed.

Corollary ssa_program_well_formed vs m p sp :
  well_formed_program vs p ->
  ssa_program empty_vmap p = (m, sp) ->
  well_formed_ssa_program (ssa_vars empty_vmap vs) sp.
Proof.
  move=> Hwell Hsp.
  have: well_formed_program (VS.union vs VS.empty) p
    by apply: (well_formed_program_replace Hwell);
    rewrite (VSLemmas.OP.P.empty_union_2 vs VS.empty_1);
    reflexivity.
  move=> {Hwell} Hwell.
  apply: (dclosed_program_well_formed Hwell Hsp).
  exact: dclosed_empty.
Qed.

Lemma ssa_singleton_var_index m t v i :
  SSAVS.mem (v, i) (SSAVS.singleton (ssa_var m t)) ->
  get_index v m = i.
Proof.
  move=> Hmem.
  move: (bv64SSA.VSLemmas.mem_singleton1 Hmem) => /eqP [] <- <-.
  reflexivity.
Qed.

Lemma ssa_atomic_var_index m a v i :
  SSAVS.mem (v, i) (bv64SSA.vars_atomic (ssa_atomic m a)) ->
  get_index v m = i.
Proof.
  case: a => /=.
  - move=> x. exact: ssa_singleton_var_index.
  - move=> _ H.
    rewrite bv64SSA.VSLemmas.mem_empty in H.
    discriminate.
Qed.

Lemma ssa_eexp_var_index m (e : eexp) v i :
  SSAVS.mem (v, i) (bv64SSA.vars_eexp (ssa_eexp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i => /=.
  - move=> a m x i Hmem. exact: (ssa_singleton_var_index Hmem).
  - move=> c m v i H. rewrite bv64SSA.VSLemmas.mem_empty in H. discriminate.
  - move=> op e IH m v i Hmem. exact: IH.
  - move=> op e1 IH1 e2 IH2 m v i Hmem.
    case: (bv64SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + exact: IH1.
    + exact: IH2.
Qed.

Lemma ssa_rexp_var_index w m (e : rexp w) v i :
  SSAVS.mem (v, i) (bv64SSA.vars_rexp (ssa_rexp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i => {w} /=.
  - move=> a m x i Hmem. exact: (ssa_singleton_var_index Hmem).
  - move=> w c m v i H. rewrite bv64SSA.VSLemmas.mem_empty in H. discriminate.
  - move=> w op e1 IH1 e2 IH2 m v i Hmem.
    case: (bv64SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + exact: IH1.
    + exact: IH2.
  - move=> w e IH p m v i Hmem. exact: IH.
Qed.

Lemma ssa_ebexp_var_index m e v i :
  SSAVS.mem (v, i) (bv64SSA.vars_ebexp (ssa_ebexp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i => /=.
  - move=> m v i Hmem.
    discriminate.
  - move=> e1 e2 m v i Hmem.
    rewrite bv64SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_eexp_var_index Hmem); reflexivity.
  - move=> e1 e2 p m v i Hmem.
    rewrite !bv64SSA.VSLemmas.union_b in Hmem.
    repeat (move/orP: Hmem; case=> Hmem);
    exact: (ssa_eexp_var_index Hmem).
  - move=> e1 IH1 e2 IH2 m v i Hmem.
    rewrite bv64SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem.
    + exact: IH1.
    + exact: IH2.
Qed.

Lemma ssa_rbexp_var_index m e v i :
  SSAVS.mem (v, i) (bv64SSA.vars_rbexp (ssa_rbexp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i => /=.
  - move=> m v i Hmem.
    discriminate.
  - move=> m v i Hmem.
    discriminate.
  - move=> w op e1 e2 m v i Hmem.
    rewrite bv64SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_rexp_var_index Hmem); reflexivity.
  - move=> e1 IH1 e2 IH2 m v i Hmem.
    rewrite bv64SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem.
    + exact: IH1.
    + exact: IH2.
  - move=> e1 IH1 e2 IH2 m v i Hmem.
    rewrite bv64SSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem.
    + exact: IH1.
    + exact: IH2.
Qed.

Lemma ssa_bexp_var_index m e v i :
  SSAVS.mem (v, i) (bv64SSA.vars_bexp (ssa_bexp m e)) ->
  get_index v m = i.
Proof.
  move=> Hmem. case: (bv64SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
  - exact: (ssa_ebexp_var_index Hmem).
  - exact: (ssa_rbexp_var_index Hmem).
Qed.

Lemma ssa_spec_in_pre_unchanged s v :
  SSAVS.mem v (bv64SSA.vars_bexp (bv64SSA.spre (ssa_spec s))) ->
  ssa_var_unchanged_program v (bv64SSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  move=> Hmem.
  rewrite Hpre in Hmem.
  destruct v as [v i].
  move: (ssa_bexp_var_index Hmem) => Hidx.
  apply: (ssa_program_le_unchanged (m1:=empty_vmap)).
  - rewrite Hidx.
    exact: Nleqnn.
  - symmetry; exact: Hprog.
Qed.

Lemma ssa_spec_unchanged_pre s :
  ssa_vars_unchanged_program (bv64SSA.vars_bexp (bv64SSA.spre (ssa_spec s))) (bv64SSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  destruct s as [f p g]; rewrite /= in Hpre Hprog Hpost *.
  apply: ssa_unchanged_program_global => v Hmem.
  exact: ssa_spec_in_pre_unchanged.
Qed.

Theorem ssa_spec_well_formed vs s :
  well_formed_spec vs s ->
  well_formed_ssa_spec (ssa_vars empty_vmap vs) (ssa_spec s).
Proof.
  move=> /andP [/andP [Hsubpre Hwellprog] Hsubpost].
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  move: (ssa_program_well_formed Hwellprog (Logic.eq_sym Hprog)) => /andP [/andP [Hwell Hvs] Hsingle].
  apply/andP; split; [apply/andP; split | idtac].
  - apply/andP; split; [apply/andP; split | idtac].
    + rewrite Hpre ssa_vars_bexp_subset.
      assumption.
    + assumption.
    + rewrite Hpost.
      exact: (ssa_vars_post_subset Hsubpost (Logic.eq_sym Hprog)).
  - assumption.
  - exact: (ssa_program_single_assignment (Logic.eq_sym Hprog)).
Qed.

Close Scope N_scope.