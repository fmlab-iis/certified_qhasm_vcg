
(** * Variables *)

From Coq Require Import FMaps FSets.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From Common Require Import FMaps FSets Nats.

Definition var : Set := nat.

Module VM := FMapList.Make(NatOrder).

Module VMLemmas := FMapLemmas(VM).

Module VS := FSetList.Make(NatOrder).

Module VSLemmas := FSetLemmas(VS).
