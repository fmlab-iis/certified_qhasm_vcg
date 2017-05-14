
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Bits.
From mQhasm Require Import bvDSL bvVerify Options.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.
Open Scope bvdsl_scope.

Definition fe25519_sq : program :=
let         wsize :=   64%nat in

let            x0 :=   0 in (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in (* *[uint64 *](xp + 32) *)

let            z0 :=   5 in (* *[uint64 *](rp +  0) *)
let            z1 :=   6 in (* *[uint64 *](rp +  8) *)
let            z2 :=   7 in (* *[uint64 *](rp + 16) *)
let            z3 :=   8 in (* *[uint64 *](rp + 24) *)
let            z4 :=   9 in (* *[uint64 *](rp + 32) *)

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in

let            c1 :=  31 in
let            c2 :=  32 in
let            c3 :=  33 in
let            c4 :=  34 in
let            c5 :=  35 in
let            c6 :=  36 in
let            c7 :=  37 in

let          x119 :=  41 in
let          x219 :=  42 in
let          x319 :=  43 in
let          x419 :=  44 in

let           r01 :=  50 in
let           r11 :=  51 in
let           r21 :=  52 in
let           r31 :=  53 in
let           r41 :=  54 in
let           rax :=  55 in
let           rdx :=  56 in

let             t :=  60 in
let       redmask :=  61 in

let           tmp := 998 in
let         carry := 999 in

[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (*  *)
      (* input rp *)
      (* input xp *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* int64 c1 *)
      (* int64 c2 *)
      (* int64 c3 *)
      (* int64 c4 *)
      (* int64 c5 *)
      (* int64 c6 *)
      (* int64 c7 *)
      (* caller c1 *)
      (* caller c2 *)
      (* caller c3 *)
      (* caller c4 *)
      (* caller c5 *)
      (* caller c6 *)
      (* caller c7 *)
      (* stack64 c1_stack *)
      (* stack64 c2_stack *)
      (* stack64 c3_stack *)
      (* stack64 c4_stack *)
      (* stack64 c5_stack *)
      (* stack64 c6_stack *)
      (* stack64 c7_stack *)
      (* stack64 x119_stack *)
      (* stack64 x219_stack *)
      (* stack64 x319_stack *)
      (* stack64 x419_stack *)
      (*  *)

      (* #required for  macro *)

      (* int64 r01 *)
      (* int64 r11 *)
      (* int64 r21 *)
      (* int64 r31 *)
      (* int64 r41 *)
      (* int64 rax *)
      (* int64 rdx *)

      (* int64 t *)
      (* int64 redmask *)

      (*  *)
      (* enter fe25519_sq *)
      (*  *)
      (* c1_stack = c1 *)
      (* c2_stack = c2 *)
      (* c3_stack = c3 *)
      (* c4_stack = c4 *)
      (* c5_stack = c5 *)
      (* c6_stack = c6 *)
      (* c7_stack = c7 *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 0) *)
      (*   r0 = rax *)
      (*   r01 = rdx *)
bvAssign rax (bvVar x0);
bvMulf rdx rax (bvVar rax) (bvVar x0);
bvAssign r0 (bvVar rax);
bvAssign r01 (bvVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   r1 = rax *)
      (*   r11 = rdx *)
bvAssign rax (bvVar x0);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x1);
bvAssign r1 (bvVar rax);
bvAssign r11 (bvVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   r2 = rax *)
      (*   r21 = rdx *)
bvAssign rax (bvVar x0);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x2);
bvAssign r2 (bvVar rax);
bvAssign r21 (bvVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   r3 = rax *)
      (*   r31 = rdx *)
bvAssign rax (bvVar x0);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x3);
bvAssign r3 (bvVar rax);
bvAssign r31 (bvVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   r4 = rax *)
      (*   r41 = rdx *)
bvAssign rax (bvVar x0);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x4);
bvAssign r4 (bvVar rax);
bvAssign r41 (bvVar rdx);
      (*  *)
      (*   rax = *[uint64 *](xp + 8) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
bvAssign rax (bvVar x1);
bvMulf rdx rax (bvVar rax) (bvVar x1);
bvAddC carry r2 (bvVar r2) (bvVar rax);
bvAdc r21 (bvVar r21) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
bvAssign rax (bvVar x1);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x2);
bvAddC carry r3 (bvVar r3) (bvVar rax);
bvAdc r31 (bvVar r31) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
bvAssign rax (bvVar x1);
bvMul rax (bvVar rax) (bvConst (fromPosZ 2%Z));
bvMulf rdx rax (bvVar rax) (bvVar x3);
bvAddC carry r4 (bvVar r4) (bvVar rax);
bvAdc r41 (bvVar r41) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
bvAssign rax (bvVar x1);
bvMul rax (bvVar rax) (bvConst (fromPosZ 38%Z));
bvMulf rdx rax (bvVar rax) (bvVar x4);
bvAddC carry r0 (bvVar r0) (bvVar rax);
bvAdc r01 (bvVar r01) (bvVar rdx) carry;
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
bvAssign rax (bvVar x2);
bvMulf rdx rax (bvVar rax) (bvVar x2);
bvAddC carry r4 (bvVar r4) (bvVar rax);
bvAdc r41 (bvVar r41) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
bvAssign rax (bvVar x2);
bvMul rax (bvVar rax) (bvConst (fromPosZ 38%Z));
bvMulf rdx rax (bvVar rax) (bvVar x3);
bvAddC carry r0 (bvVar r0) (bvVar rax);
bvAdc r01 (bvVar r01) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
bvAssign rax (bvVar x2);
bvMul rax (bvVar rax) (bvConst (fromPosZ 38%Z));
bvMulf rdx rax (bvVar rax) (bvVar x4);
bvAddC carry r1 (bvVar r1) (bvVar rax);
bvAdc r11 (bvVar r11) (bvVar rdx) carry;
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
bvAssign rax (bvVar x3);
bvMul rax (bvVar rax) (bvConst (fromPosZ 19%Z));
bvMulf rdx rax (bvVar rax) (bvVar x3);
bvAddC carry r1 (bvVar r1) (bvVar rax);
bvAdc r11 (bvVar r11) (bvVar rdx) carry;
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
bvAssign rax (bvVar x3);
bvMul rax (bvVar rax) (bvConst (fromPosZ 38%Z));
bvMulf rdx rax (bvVar rax) (bvVar x4);
bvAddC carry r2 (bvVar r2) (bvVar rax);
bvAdc r21 (bvVar r21) (bvVar rdx) carry;
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
bvAssign rax (bvVar x4);
bvMul rax (bvVar rax) (bvConst (fromPosZ 19%Z));
bvMulf rdx rax (bvVar rax) (bvVar x4);
bvAddC carry r3 (bvVar r3) (bvVar rax);
bvAdc r31 (bvVar r31) (bvVar rdx) carry;
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   r01 = (r01.r0) << 13 *)
      (*   r0 &= redmask *)
bvConcatShl r01 r0 (bvVar r01) (bvVar r0) (fromNat 13);
      (*    *)
      (*   r11 = (r11.r1) << 13 *)
      (*   r1 &= redmask *)
      (*   r1 += r01 *)
bvConcatShl r11 r1 (bvVar r11) (bvVar r1) (fromNat 13);
bvAdd r1 (bvVar r1) (bvVar r01);
      (*    *)
      (*   r21 = (r21.r2) << 13 *)
      (*   r2 &= redmask *)
      (*   r2 += r11 *)
bvConcatShl r21 r2 (bvVar r21) (bvVar r2) (fromNat 13);
bvAdd r2 (bvVar r2) (bvVar r11);
      (*    *)
      (*   r31 = (r31.r3) << 13 *)
      (*   r3 &= redmask *)
      (*   r3 += r21 *)
bvConcatShl r31 r3 (bvVar r31) (bvVar r3) (fromNat 13);
bvAdd r3 (bvVar r3) (bvVar r21);
      (*    *)
      (*   r41 = (r41.r4) << 13 *)
      (*   r4 &= redmask *)
      (*   r4 += r31 *)
bvConcatShl r41 r4 (bvVar r41) (bvVar r4) (fromNat 13);
bvAdd r4 (bvVar r4) (bvVar r31);
      (*   r41 = r41 * 19 *)
bvMul r41 (bvVar r41) (bvConst (fromPosZ 19%Z));
      (*   r0 += r41 *)
bvAdd r0 (bvVar r0) (bvVar r41);
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   t = r0 *)
      (*   (uint64) t >>= 51 *)
      (*   t += r1 *)
      (*   r0 &= redmask *)
bvAssign t (bvVar r0);
bvSplit t tmp (bvVar t) (fromNat 51);
bvAdd t (bvVar t) (bvVar r1);
bvAssign r0 (bvVar tmp);
      (*    *)
      (*   r1 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r2 *)
      (*   r1 &= redmask *)
bvAssign r1 (bvVar t);
bvSplit t tmp (bvVar t) (fromNat 51);
bvAdd t (bvVar t) (bvVar r2);
bvAssign r1 (bvVar tmp);
      (*    *)
      (*   r2 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r3 *)
      (*   r2 &= redmask *)
bvAssign r2 (bvVar t);
bvSplit t tmp (bvVar t) (fromNat 51);
bvAdd t (bvVar t) (bvVar r3);
bvAssign r2 (bvVar tmp);
      (*    *)
      (*   r3 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r4 *)
      (*   r3 &= redmask *)
bvAssign r3 (bvVar t);
bvSplit t tmp (bvVar t) (fromNat 51);
bvAdd t (bvVar t) (bvVar r4);
bvAssign r3 (bvVar tmp);
      (*    *)
      (*   r4 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t *= 19 *)
      (*   r0 += t *)
      (*   r4 &= redmask *)
bvAssign r4 (bvVar t);
bvSplit t tmp (bvVar t) (fromNat 51);
bvMul t (bvVar t) (bvConst (fromPosZ 19%Z));
bvAdd r0 (bvVar r0) (bvVar t);
bvAssign r4 (bvVar tmp);
      (*   #END MACRO  *)
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
bvAssign z0 (bvVar r0);
      (* *[uint64 *](rp + 8) = r1 *)
bvAssign z1 (bvVar r1);
      (* *[uint64 *](rp + 16) = r2 *)
bvAssign z2 (bvVar r2);
      (* *[uint64 *](rp + 24) = r3 *)
bvAssign z3 (bvVar r3);
      (* *[uint64 *](rp + 32) = r4 *)
bvAssign z4 (bvVar r4)
      (*   *)
      (*  *)
      (* c1 =c1_stack *)
      (* c2 =c2_stack *)
      (* c3 =c3_stack *)
      (* c4 =c4_stack *)
      (* c5 =c5_stack *)
      (* c6 =c6_stack *)
      (* c7 =c7_stack *)
      (*  *)
      (* leave *)
] .

Definition fe25519_sq_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_sq_pre : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
bvrands
  [::
     (bvrvar x0) <r (bvposz (2^54)%Z);
     (bvrvar x1) <r (bvposz (2^54)%Z);
     (bvrvar x2) <r (bvposz (2^54)%Z);
     (bvrvar x3) <r (bvposz (2^54)%Z);
     (bvrvar x4) <r (bvposz (2^54)%Z)
  ].

Definition radix51 := @limbs 51.

Definition fe25519_sq_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            z0 :=   5 in
let            z1 :=   6 in
let            z2 :=   7 in
let            z3 :=   8 in
let            z4 :=   9 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
bvands2
  [::
     bveEqMod
     (bvesq (radix51 [::bvevar x0; bvevar x1; bvevar x2; bvevar x3; bvevar x4]))
     (radix51 [::bvevar z0; bvevar z1; bvevar z2; bvevar z3; bvevar z4])
     (bvconst n25519)
  ]
  [::
     (bvrvar z0) <=r (bvposz (2^51+2^15)%Z);
     (bvrvar z1) <=r (bvposz (2^51+2^15)%Z);
     (bvrvar z2) <=r (bvposz (2^51+2^15)%Z);
     (bvrvar z3) <=r (bvposz (2^51+2^15)%Z);
     (bvrvar z4) <=r (bvposz (2^51+2^15)%Z)
  ].

Definition fe25519_sq_spec :=
  {| spre := fe25519_sq_pre;
     sprog := fe25519_sq;
     spost := fe25519_sq_post |}.

Lemma valid_fe25519_sq : valid_bvspec (fe25519_sq_inputs, fe25519_sq_spec).
Proof.
  time "valid_fe25519_sq" verify_bvspec.
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.

