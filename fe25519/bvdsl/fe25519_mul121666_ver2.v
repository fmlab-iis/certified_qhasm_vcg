
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Var Bits.
From mQhasm Require Import bvDSL bvVerify Options zVerify.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.
Open Scope bvdsl_scope.

(* This is an alternative implementation of fe25519_mul121666. *)

Definition fe25519_mul121666 : program :=

let         wsize :=   64%nat in

let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in

let            r0 :=  10 in
let            r1 :=  11 in
let            r2 :=  12 in
let            r3 :=  13 in
let            r4 :=  14 in

let           rax :=  20 in
let           rdx :=  21 in

[::
bvAssign rax (bvVar x0);
bvMulf rdx rax (bvVar rax) (bvConst (fromPosZ 121666%Z));
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
bvAssign r0 (bvVar rax);
bvAssign r1 (bvVar rdx);
      (*    *)
bvAssign rax (bvVar x1);
bvMulf rdx rax (bvVar rax) (bvConst (fromPosZ 121666));
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
bvAdd r1 (bvVar r1) (bvVar rax);
bvAssign r2 (bvVar rdx);
      (*    *)
bvAssign rax (bvVar x2);
bvMulf rdx rax (bvVar rax) (bvConst (fromPosZ 121666));
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
bvAdd r2 (bvVar r2) (bvVar rax);
bvAssign r3 (bvVar rdx);
      (*    *)
bvAssign rax (bvVar x3);
bvMulf rdx rax (bvVar rax) (bvConst (fromPosZ 121666));
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
bvAdd r3 (bvVar r3) (bvVar rax);
bvAssign r4 (bvVar rdx);
      (*    *)
bvAssign rax (bvVar x4);
bvMulf rdx rax (bvVar rax) (bvConst (fromPosZ 121666));
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
bvAdd r4 (bvVar r4) (bvVar rax);
bvMul rdx (bvVar rdx) (bvConst (fromPosZ 19%Z));
bvAdd r0 (bvVar r0) (bvVar rdx)
] .

Definition fe25519_mul121666_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_mul121666_pre : bexp := bvTrue.

Definition radix51 := @limbs 51.

Definition fe25519_mul121666_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            r0 :=  10 in
let            r1 :=  11 in
let            r2 :=  12 in
let            r3 :=  13 in
let            r4 :=  14 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
bvands2
  [::
     bveEqMod (
       (radix51 [::bvevar x0; bvevar x1; bvevar x2; bvevar x3; bvevar x4])
       *e
       (bveconst 121666%Z)
     )
     (radix51 [::bvevar r0; bvevar r1; bvevar r2; bvevar r3; bvevar r4])
     (bvconst n25519)
  ]
  [::
     (bvrvar r0) <=r (bvposz (2^52)%Z);
     (bvrvar r1) <=r (bvposz (2^52)%Z);
     (bvrvar r2) <=r (bvposz (2^52)%Z);
     (bvrvar r3) <=r (bvposz (2^52)%Z);
     (bvrvar r4) <=r (bvposz (2^52)%Z)
  ].

Definition fe25519_mul121666_spec :=
  {| spre := fe25519_mul121666_pre;
     sprog := fe25519_mul121666;
     spost := fe25519_mul121666_post |}.

Lemma valid_fe25519_mul121666 : valid_bvspec (fe25519_mul121666_inputs, fe25519_mul121666_spec).
Proof.
  time "valid_fe25519_mul121666" verify_bvspec.
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
