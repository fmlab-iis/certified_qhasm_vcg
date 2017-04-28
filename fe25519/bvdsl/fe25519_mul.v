
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Bits.
From mQhasm Require Import bvDSL bvVerify Options.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.
Open Scope bvdsl_scope.

Definition fe25519_mul : program :=

let         wsize :=   64%nat in

let            x0 :=   0 in (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in (* *[uint64 *](xp + 32) *)
let            y0 :=   5 in (* *[uint64 *](yp +  0) *)
let            y1 :=   6 in (* *[uint64 *](yp +  8) *)
let            y2 :=   7 in (* *[uint64 *](yp + 16) *)
let            y3 :=   8 in (* *[uint64 *](yp + 24) *)
let            y4 :=   9 in (* *[uint64 *](yp + 32) *)
let            z0 :=  10 in (* *[uint64 *](rp +  0) *)
let            z1 :=  11 in (* *[uint64 *](rp +  8) *)
let            z2 :=  12 in (* *[uint64 *](rp + 16) *)
let            z3 :=  13 in (* *[uint64 *](rp + 24) *)
let            z4 :=  14 in (* *[uint64 *](rp + 32) *)
let         carry := 999 in
let           tmp := 998 in
let          tmp2 := 997 in

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in

let            c0 :=  30 in
let            c1 :=  31 in
let            c2 :=  32 in
let            c3 :=  33 in
let            c4 :=  34 in

let        mulr01 :=  40 in
let        mulr11 :=  41 in
let        mulr21 :=  42 in
let        mulr31 :=  43 in
let        mulr41 :=  44 in

let        mulrax :=  50 in
let        mulrdx :=  51 in
let          mult :=  52 in
let    mulredmask :=  53 in
let       mulx219 :=  54 in
let       mulx319 :=  55 in
let       mulx419 :=  56 in
[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (* int64 yp *)
      (*  *)
      (* input rp *)
      (* input xp *)
      (* input yp *)
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
      (* stack64 rp_stack *)
      (*  *)
      (* # required for the mul template *)
      (* int64 mulr01 *)
      (* int64 mulr11 *)
      (* int64 mulr21 *)
      (* int64 mulr31 *)
      (* int64 mulr41 *)
      (* int64 mulrax *)
      (* int64 mulrdx *)
      (* int64 mult *)
      (* int64 mulredmask *)
      (* stack64 mulx219_stack *)
      (* stack64 mulx319_stack *)
      (* stack64 mulx419_stack *)

      (*  *)

      (* enter crypto_sign_ed25519_amd64_51_fe25519_mul *)

      (*  *)

      (*   c1_stack = c1 *)
      (*   c2_stack = c2 *)
      (*   c3_stack = c3 *)
      (*   c4_stack = c4 *)
      (*   c5_stack = c5 *)
      (*   c6_stack = c6 *)
      (*   c7_stack = c7 *)
      (*   rp_stack = rp *)

      (*  *)
      (* yp = yp *)
      (*  *)
      (*  *)

      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   mulrax *= 19 *)
      (*   mulx319_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r0 = mulrax *)
      (*   mulr01 = mulrdx *)
bvAssign mulrax (bvVar x3);
bvMul mulrax (bvVar mulrax) (bvConst (fromPosZ 19%Z));
bvAssign mulx319 (bvVar mulrax);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y2);
bvAssign r0 (bvVar mulrax);
bvAssign mulr01 (bvVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
bvAssign mulrax (bvVar x4);
bvMul mulrax (bvVar mulrax) (bvConst (fromPosZ 19%Z));
bvAssign mulx419 (bvVar mulrax);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y1);
bvAddC carry r0 (bvVar r0) (bvVar mulrax);
bvAdc mulr01 (bvVar mulr01) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
bvAssign mulrax (bvVar x0);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y0);
bvAddC carry r0 (bvVar r0) (bvVar mulrax);
bvAdc mulr01 (bvVar mulr01) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
bvAssign mulrax (bvVar x0);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y1);
bvAssign r1 (bvVar mulrax);
bvAssign mulr11 (bvVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
bvAssign mulrax (bvVar x0);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y2);
bvAssign r2 (bvVar mulrax);
bvAssign mulr21 (bvVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
bvAssign mulrax (bvVar x0);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y3);
bvAssign r3 (bvVar mulrax);
bvAssign mulr31 (bvVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
bvAssign mulrax (bvVar x0);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y4);
bvAssign r4 (bvVar mulrax);
bvAssign mulr41 (bvVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
bvAssign mulrax (bvVar x1);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y0);
bvAddC carry r1 (bvVar r1) (bvVar mulrax);
bvAdc mulr11 (bvVar mulr11) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
bvAssign mulrax (bvVar x1);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y1);
bvAddC carry r2 (bvVar r2) (bvVar mulrax);
bvAdc mulr21 (bvVar mulr21) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
bvAssign mulrax (bvVar x1);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y2);
bvAddC carry r3 (bvVar r3) (bvVar mulrax);
bvAdc mulr31 (bvVar mulr31) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
bvAssign mulrax (bvVar x1);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y3);
bvAddC carry r4 (bvVar r4) (bvVar mulrax);
bvAdc mulr41 (bvVar mulr41) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
bvAssign mulrax (bvVar x1);
bvMul mulrax (bvVar mulrax) (bvConst (fromPosZ 19%Z));
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y4);
bvAddC carry r0 (bvVar r0) (bvVar mulrax);
bvAdc mulr01 (bvVar mulr01) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
bvAssign mulrax (bvVar x2);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y0);
bvAddC carry r2 (bvVar r2) (bvVar mulrax);
bvAdc mulr21 (bvVar mulr21) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
bvAssign mulrax (bvVar x2);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y1);
bvAddC carry r3 (bvVar r3) (bvVar mulrax);
bvAdc mulr31 (bvVar mulr31) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
bvAssign mulrax (bvVar x2);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y2);
bvAddC carry r4 (bvVar r4) (bvVar mulrax);
bvAdc mulr41 (bvVar mulr41) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
bvAssign mulrax (bvVar x2);
bvMul mulrax (bvVar mulrax) (bvConst (fromPosZ 19%Z));
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y3);
bvAddC carry r0 (bvVar r0) (bvVar mulrax);
bvAdc mulr01 (bvVar mulr01) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
bvAssign mulrax (bvVar x2);
bvMul mulrax (bvVar mulrax) (bvConst (fromPosZ 19%Z));
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y4);
bvAddC carry r1 (bvVar r1) (bvVar mulrax);
bvAdc mulr11 (bvVar mulr11) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
bvAssign mulrax (bvVar x3);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y0);
bvAddC carry r3 (bvVar r3) (bvVar mulrax);
bvAdc mulr31 (bvVar mulr31) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
bvAssign mulrax (bvVar x3);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y1);
bvAddC carry r4 (bvVar r4) (bvVar mulrax);
bvAdc mulr41 (bvVar mulr41) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
bvAssign mulrax (bvVar mulx319);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y3);
bvAddC carry r1 (bvVar r1) (bvVar mulrax);
bvAdc mulr11 (bvVar mulr11) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
bvAssign mulrax (bvVar mulx319);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y4);
bvAddC carry r2 (bvVar r2) (bvVar mulrax);
bvAdc mulr21 (bvVar mulr21) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
bvAssign mulrax (bvVar x4);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y0);
bvAddC carry r4 (bvVar r4) (bvVar mulrax);
bvAdc mulr41 (bvVar mulr41) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
bvAssign mulrax (bvVar mulx419);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y2);
bvAddC carry r1 (bvVar r1) (bvVar mulrax);
bvAdc mulr11 (bvVar mulr11) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
bvAssign mulrax (bvVar mulx419);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y3);
bvAddC carry r2 (bvVar r2) (bvVar mulrax);
bvAdc mulr21 (bvVar mulr21) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
bvAssign mulrax (bvVar mulx419);
bvMulf mulrdx mulrax (bvVar mulrax) (bvVar y4);
bvAddC carry r3 (bvVar r3) (bvVar mulrax);
bvAdc mulr31 (bvVar mulr31) (bvVar mulrdx) carry;
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mulredmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
bvConcatShl mulr01 r0 (bvVar mulr01) (bvVar r0) (fromNat 13);
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
bvConcatShl mulr11 r1 (bvVar mulr11) (bvVar r1) (fromNat 13);
bvAdd r1 (bvVar r1) (bvVar mulr01);
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
bvConcatShl mulr21 r2 (bvVar mulr21) (bvVar r2) (fromNat 13);
bvAdd r2 (bvVar r2) (bvVar mulr11);
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
bvConcatShl mulr31 r3 (bvVar mulr31) (bvVar r3) (fromNat 13);
bvAdd r3 (bvVar r3) (bvVar mulr21);
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
bvConcatShl mulr41 r4 (bvVar mulr41) (bvVar r4) (fromNat 13);
bvAdd r4 (bvVar r4) (bvVar mulr31);
      (*   mulr41 = mulr41 * 19 *)
bvMul mulr41 (bvVar mulr41) (bvConst (fromPosZ 19%Z));
      (*   r0 += mulr41 *)
bvAdd r0 (bvVar r0) (bvVar mulr41);
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mult = r0 *)
      (*   (uint64) mult >>= 51 *)
      (*   mult += r1 *)
bvAssign mult (bvVar r0);
bvSplit mult tmp (bvVar mult) (fromNat 51);
bvAdd mult (bvVar mult) (bvVar r1);
      (*   r1 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r0 &= mulredmask *)
      (*   mult += r2 *)
bvAssign r1 (bvVar mult);
bvSplit mult tmp2 (bvVar mult) (fromNat 51);
bvAssign r0 (bvVar tmp);
bvAdd mult (bvVar mult) (bvVar r2);
      (*   r2 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r1 &= mulredmask *)
      (*   mult += r3 *)
bvAssign r2 (bvVar mult);
bvSplit mult tmp (bvVar mult) (fromNat 51);
bvAssign r1 (bvVar tmp2);
bvAdd mult (bvVar mult) (bvVar r3);
      (*   r3 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r2 &= mulredmask *)
      (*   mult += r4 *)
bvAssign r3 (bvVar mult);
bvSplit mult tmp2 (bvVar mult) (fromNat 51);
bvAssign r2 (bvVar tmp);
bvAdd mult (bvVar mult) (bvVar r4);
      (*   r4 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r3 &= mulredmask *)
bvAssign r4 (bvVar mult);
bvSplit mult tmp (bvVar mult) (fromNat 51);
bvAssign r3 (bvVar tmp2);
      (*   mult *= 19 *)
      (*   r0 += mult *)
      (*   r4 &= mulredmask *)
bvMul mult (bvVar mult) (bvConst (fromPosZ 19%Z));
bvAdd r0 (bvVar r0) (bvVar mult);
bvAssign r4 (bvVar tmp);
      (*   #END MACRO mul *)

      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
      (* *[uint64 *](rp + 8) = r1 *)
      (* *[uint64 *](rp + 16) = r2 *)
      (* *[uint64 *](rp + 24) = r3 *)
      (* *[uint64 *](rp + 32) = r4 *)
bvAssign z0 (bvVar r0);
bvAssign z1 (bvVar r1);
bvAssign z2 (bvVar r2);
bvAssign z3 (bvVar r3);
bvAssign z4 (bvVar r4)
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

Definition fe25519_mul_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4; y0; y1; y2; y3; y4].

Definition fe25519_mul_pre : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
bvands
  [::
     bvult (bvvar x0) (bvposz (2^52)%Z);
     bvult (bvvar x1) (bvposz (2^52)%Z);
     bvult (bvvar x2) (bvposz (2^52)%Z);
     bvult (bvvar x3) (bvposz (2^52)%Z);
     bvult (bvvar x4) (bvposz (2^52)%Z);
     bvult (bvvar y0) (bvposz (2^52)%Z);
     bvult (bvvar y1) (bvposz (2^52)%Z);
     bvult (bvvar y2) (bvposz (2^52)%Z);
     bvult (bvvar y3) (bvposz (2^52)%Z);
     bvult (bvvar y4) (bvposz (2^52)%Z)
  ].

Definition radix51 := @limbs 51 520.

Definition fe25519_mul_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
bvands [::
          bvEqMod
          (
            (radix51 [:: bvvar x0; bvvar x1; bvvar x2; bvvar x3; bvvar x4])
              @*
              (radix51 [:: bvvar y0; bvvar y1; bvvar y2; bvvar y3; bvvar y4])
          )
          (radix51 [:: bvvar r0; bvvar r1; bvvar r2; bvvar r3; bvvar r4])
          (bvposz n25519);
          bvult (bvvar r0) (bvposz (2^52)%Z);
          bvult (bvvar r1) (bvposz (2^52)%Z);
          bvult (bvvar r2) (bvposz (2^52)%Z);
          bvult (bvvar r3) (bvposz (2^52)%Z);
          bvult (bvvar r4) (bvposz (2^52)%Z)
       ].

Definition fe25519_mul_spec :=
  {| spre := fe25519_mul_pre;
     sprog := fe25519_mul;
     spost := fe25519_mul_post |}.

Lemma valid_fe25519_mul : valid_bvspec (fe25519_mul_inputs, fe25519_mul_spec).
Proof.
  time "valid_fe25519_mul" verify_bvspec with [:: With Boolector].
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
