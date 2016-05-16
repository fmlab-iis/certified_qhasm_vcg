
From Coq Require Import List.
From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive nonempty_list A : Type :=
| NonemptyList : forall (hd : A) (tl : list A), nonempty_list A.

Definition nonempty_list_to_list A (l : nonempty_list A) : list A :=
  match l with
  | NonemptyList hd tl => hd::tl
  end.

Coercion nonempty_list_to_list : nonempty_list >-> list.

Definition nonempty_hd A (l : nonempty_list A) : A :=
  match l with
  | NonemptyList hd tl => hd
  end.
