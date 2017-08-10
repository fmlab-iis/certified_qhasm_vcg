
(** * Variables *)

From Coq Require Import FMaps FSets ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import FMaps FSets ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.

Definition var : Set := N.

Module VarOrder := NOrder.

(* Variable sets. *)

Module VS.
  Module S := FSets.Make(NOrder).
  Include S.

  (* Generate a new variable. *)
  Definition new_var (s : t) : var :=
    match max_elt s with
    | Some v => v + 1
    | None => 0
    end.

  Lemma new_var_is_new :
    forall (s : t), ~~ mem (new_var s) s.
  Proof.
    move=> s.
    apply/negP => Hmem.
    move: (mem_2 Hmem) => {Hmem}.
    rewrite /new_var.
    case H: (max_elt s).
    - move=> Hin.
      move: (max_elt_2 H Hin) => Hfalse.
      apply: Hfalse.
      exact: NltnSn.
    - move: (max_elt_3 H) => {H} H Hin.
      move: (H 0) => Hnotin; apply: Hnotin; exact: Hin.
  Qed.

End VS.

Module VSLemmas := FSetLemmas VS.



(* Variable maps. *)

Module VM.
   Module M := FMapList.Make(NOrder).
   Module Lemmas := FMapLemmas(M).
   Include M.

   Section Aux.

     Variable elt : Type.

     (* Convert a variable map to a variable set. *)
     Definition vset (m : M.t elt) : VS.t :=
       fold (fun x _ s => VS.add x s) m VS.empty.

     Lemma mem_vset E :
       forall x, mem x E -> VS.mem x (vset E).
     Proof.
       rewrite /vset.
       eapply Lemmas.P.fold_rec.
       - move=> m Hempty x Hmem.
         apply: False_ind.
         exact: (Lemmas.empty_mem Hempty Hmem).
       - move=> x e m E1 E2 _ _ Hadd Hind y Hmem.
         case Hyx: (y == x).
         + exact: (VSLemmas.mem_add_eq _ Hyx).
         + move/negP: Hyx => Hyx.
           rewrite (VSLemmas.mem_add_neq _ Hyx).
           apply: Hind.
           move: (Hadd y) => {Hadd}.
           rewrite (VM.Lemmas.find_add_neq _ _ Hyx) => {Hyx} Hfind.
           rewrite -(VM.Lemmas.find_eq_mem_eq Hfind).
           exact: Hmem.
     Qed.

     (* Generate a new variable. *)
     Definition new_var (m : t elt) : var :=
       match Lemmas.max_elt m with
       | Some (v, _) => v + 1
       | None => 0
       end.

     Lemma new_var_is_new :
       forall (m : t elt), ~~ mem (new_var m) m.
     Proof.
       move=> m.
       apply/negP => Hmem.
       move: (mem_2 Hmem) => {Hmem}.
       rewrite /new_var.
       move: (refl_equal (Lemmas.max_elt m)).
       move: {2}(Lemmas.max_elt m) => x.
       destruct x.
       - destruct p as [x ty].
         move=> Hmax; rewrite Hmax => Hin.
         move: (Lemmas.max_elt_Above Hmax) => Habove.
         have: In (x + 1) (remove x m).
         + case: Hin => ty1 Hmapsto.
           exists ty1.
           apply: (remove_2 _ Hmapsto).
           move=> {Hmax Habove Hmapsto ty ty1 m} Heq.
           move: (NltnSn x).
           rewrite {1}(eqP Heq).
           rewrite Nltnn.
           discriminate.
         + move=> Hin1.
           move: (Habove _ Hin1) => Hlt.
           move: (Nltn_trans Hlt (NltnSn x)).
           rewrite Nltnn.
           discriminate.
       - move=> Hmax; rewrite Hmax => Hin.
         move: (Lemmas.max_elt_Empty Hmax) => Hempty.
         case: Hin => ty Hmapsto.
         move: (Hempty 0 ty).
         apply; assumption.
     Qed.

   End Aux.

End VM.

Close Scope N_scope.



(** Variables for SSA *)

From Common Require Import SsrOrdered.

Module SSAVarOrder := (MakeProdOrdered VarOrder NOrder).

Module SSAVS := FSets.Make SSAVarOrder.

Module SSAVSLemmas := FSetLemmas SSAVS.

Definition svar (x : SSAVarOrder.t) := fst x.

Definition sidx (x : SSAVarOrder.t) := snd x.

Hint Unfold svar sidx.

Definition svar_notin v vs : Prop := forall i, ~~ SSAVS.mem (v, i) vs.

Lemma svar_notin_singleton1 v x :
  svar_notin v (SSAVS.singleton x) -> v != svar x.
Proof.
  destruct x as [x i]. move=> /= H; move: (SSAVSLemmas.not_mem_singleton1 (H i)).
  move=> Hne; apply/negP => Heq; apply: Hne. rewrite (eqP Heq).
  exact: SSAVS.E.eq_refl.
Qed.

Lemma svar_notin_singleton2 v x :
  v != svar x -> svar_notin v (SSAVS.singleton x).
Proof.
  move/negP=> Hne i. apply/negP => Heq; apply: Hne.
  move: (SSAVSLemmas.mem_singleton1 Heq) => {Heq}. destruct x as [x j] => /=.
  move/eqP => [Hv Hi]. by rewrite Hv.
Qed.

Lemma svar_notin_union1 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs1.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj1 (SSAVSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union2 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs2.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj2 (SSAVSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union3 v vs1 vs2 :
  svar_notin v vs1 -> svar_notin v vs2 ->
  svar_notin v (SSAVS.union vs1 vs2).
Proof.
  move=> H1 H2 i. move: (H1 i) (H2 i) => {H1 H2} H1 H2.
  exact: (SSAVSLemmas.not_mem_union2 H1 H2).
Qed.

Lemma svar_notin_add1 v x vs :
  svar_notin v (SSAVS.add x vs) -> v != svar x.
Proof.
  destruct x as [x i] => /= H. move: (H i) => {H} H.
  move: (SSAVSLemmas.not_mem_add1 H) => {H}. move=> [H _]; apply/negP => Heq.
  apply: H. rewrite (eqP Heq); exact: eqxx.
Qed.

Lemma svar_notin_add2 v x vs :
  svar_notin v (SSAVS.add x vs) -> svar_notin v vs.
Proof.
  move=> H i. move: (H i) => {H} H. move: (SSAVSLemmas.not_mem_add1 H) => {H}.
  move=> [_ H]; exact: H.
Qed.

Lemma svar_notin_replace v vs1 vs2 :
  SSAVS.Equal vs1 vs2 -> svar_notin v vs1 -> svar_notin v vs2.
Proof.
  move=> H H1 x. rewrite -H. exact: H1.
Qed.

Lemma svar_notin_subset v vs1 vs2 :
  SSAVS.subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
Proof.
  move=> H H2 x. apply/negP => H1. move: (SSAVSLemmas.mem_subset H1 H) => Hmem.
  move/negP: (H2 x). apply. exact: Hmem.
Qed.



(** Generate new SSA variables *)

From Common Require Import Nats.

Definition max_svar (vs : SSAVS.t) : VarOrder.t :=
  match SSAVS.max_elt vs with
  | Some v => svar v
  | None => 0%N
  end.

Definition new_svar (vs : SSAVS.t) : VarOrder.t :=
  N.succ (max_svar vs).

Lemma N_ltb_succ v : (v <? N.succ v)%N.
Proof.
  apply: (proj2 (N.ltb_lt v (N.succ v))). exact: N.lt_succ_diag_r.
Qed.

Lemma V_ltb_succ v i j : SSAVarOrder.ltb (v, j) ((N.succ v), i).
Proof.
  rewrite /SSAVarOrder.ltb /SSAVarOrder.M.lt /VarOrder.ltb /NOrderMinimal.lt /=.
  rewrite N_ltb_succ. exact: is_true_true.
Qed.

Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
Proof.
  rewrite /new_svar /max_svar. set x := SSAVS.max_elt vs.
  have: SSAVS.max_elt vs = x by reflexivity. case x.
  - move=> v Hmax i. apply/negP => Hmem. apply: (SSAVSLemmas.max_elt2 Hmax Hmem).
    exact: V_ltb_succ.
  - move=> Hnone i. apply: SSAVSLemmas.is_empty_mem.
    exact: (SSAVSLemmas.max_elt3 Hnone).
Qed.
