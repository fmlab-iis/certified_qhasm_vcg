From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Bits.
From mQhasm Require Import bvDSL bvVerify Options.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.
Open Scope bvdsl_scope.

Definition radix51 := @limbs 51 1032.

Definition bi : Set := N * N * N * N * N.

Definition bi_list (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  [:: x0; x1; x2; x3; x4].

Definition bi_limbs (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  radix51 [:: bvvar x0; bvvar x1; bvvar x2; bvvar x3; bvvar x4].

Definition fe25519_add (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
[::
      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): 0m16.349s *)
      (*  *)
      (* int64 x0 *)
      (* int64 x1 *)
      (* int64 x2 *)
      (* int64 x3 *)
      (* int64 x4 *)
      (*  *)
      (* int64 y0 *)
      (* int64 y1 *)
      (* int64 y2 *)
      (* int64 y3 *)
      (* int64 y4 *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* #// assume 0 <=u x0, x1, x2, x3, x4, y0, y1, y2, y3, y4 <=u 2**51 + 2**15 *)
      (*  *)
      (* r0 = x0 *)
bvAssign r0 (bvVar x0);
      (* r1 = x1 *)
bvAssign r1 (bvVar x1);
      (* r2 = x2 *)
bvAssign r2 (bvVar x2);
      (* r3 = x3 *)
bvAssign r3 (bvVar x3);
      (* r4 = x4 *)
bvAssign r4 (bvVar x4);
      (* r0 += y0 *)
bvAdd r0 (bvVar r0) (bvVar y0);
      (* r1 += y1 *)
bvAdd r1 (bvVar r1) (bvVar y1);
      (* r2 += y2 *)
bvAdd r2 (bvVar r2) (bvVar y2);
      (* r3 += y3 *)
bvAdd r3 (bvVar r3) (bvVar y3);
      (* r4 += y4 *)
bvAdd r4 (bvVar r4) (bvVar y4)
      (*  *)
      (* #// var sum_x = x0@u320 + x1@u320 * 2**51 + x2@u320 * 2**102 + x3@u320 * 2**153 + x4@u320 * 2**204 *)
      (* #//     sum_y = y0@u320 + y1@u320 * 2**51 + y2@u320 * 2**102 + y3@u320 * 2**153 + y4@u320 * 2**204 *)
      (* #//     sum_r = r0@u320 + r1@u320 * 2**51 + r2@u320 * 2**102 + r3@u320 * 2**153 + r4@u320 * 2**204 *)
      (* #// assert (sum_r - (sum_x + sum_y)) % (2**255 - 19) = 0 && *)
      (* #//        0 <=u r0, r1, r2, r3, r4 <u 2**53 *)
] .

Definition fe25519_sub (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
let crypto_sign_ed25519_amd64_51_2P0 :=
                       4503599627370458%Z in (* 0xFFFFFFFFFFFDA from consts *)
let crypto_sign_ed25519_amd64_51_2P1234 :=
                       4503599627370494%Z in (* 0xFFFFFFFFFFFFE from consts *)
[::
      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): 3m38.621s *)
      (*  *)
      (* int64 x0 *)
      (* int64 x1 *)
      (* int64 x2 *)
      (* int64 x3 *)
      (* int64 x4 *)
      (*  *)
      (* int64 y0 *)
      (* int64 y1 *)
      (* int64 y2 *)
      (* int64 y3 *)
      (* int64 y4 *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* #// assume 0 <=u x0, x1, x2, x3, x4, y0, y1, y2, y3, y4 <=u 2**51 + 2**15 *)
      (*  *)
      (* r0 = x0 *)
bvAssign r0 (bvVar x0);
      (* r1 = x1 *)
bvAssign r1 (bvVar x1);
      (* r2 = x2 *)
bvAssign r2 (bvVar x2);
      (* r3 = x3 *)
bvAssign r3 (bvVar x3);
      (* r4 = x4 *)
bvAssign r4 (bvVar x4);
      (* r0 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P0 *)
bvAdd r0 (bvVar r0) (bvConst (fromPosZ crypto_sign_ed25519_amd64_51_2P0));
      (* r1 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
bvAdd r1 (bvVar r1) (bvConst (fromPosZ crypto_sign_ed25519_amd64_51_2P1234));
      (* r2 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
bvAdd r2 (bvVar r2) (bvConst (fromPosZ crypto_sign_ed25519_amd64_51_2P1234));
      (* r3 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
bvAdd r3 (bvVar r3) (bvConst (fromPosZ crypto_sign_ed25519_amd64_51_2P1234));
      (* r4 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
bvAdd r4 (bvVar r4) (bvConst (fromPosZ crypto_sign_ed25519_amd64_51_2P1234));
      (* r0 -= y0 *)
bvSub r0 (bvVar r0) (bvVar y0);
      (* r1 -= y1 *)
bvSub r1 (bvVar r1) (bvVar y1);
      (* r2 -= y2 *)
bvSub r2 (bvVar r2) (bvVar y2);
      (* r3 -= y3 *)
bvSub r3 (bvVar r3) (bvVar y3);
      (* r4 -= y4 *)
bvSub r4 (bvVar r4) (bvVar y4)
      (*  *)
      (* #// var sum_x = x0@u320 + x1@u320 * 2**51 + x2@u320 * 2**102 + x3@u320 * 2**153 + x4@u320 * 2**204 *)
      (* #//     sum_y = y0@u320 + y1@u320 * 2**51 + y2@u320 * 2**102 + y3@u320 * 2**153 + y4@u320 * 2**204 *)
      (* #//     sum_r = r0@u320 + r1@u320 * 2**51 + r2@u320 * 2**102 + r3@u320 * 2**153 + r4@u320 * 2**204 *)
      (* #// assert (sum_r - (sum_x - sum_y)) % (2**255 - 19) = 0 && *)
      (* #//        0 <=u r0, r1, r2, r3, r4 <u 2**54 *)
] .

Definition fe25519_mul121666 (X R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(r0, r1, r2, r3, r4) := R in
let           rax :=  1000 in
let           rdx :=  1001 in

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

Definition fe25519_mul (X Y Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(z0, z1, z2, z3, z4) := Z in
let         carry :=  9999 in
let           tmp :=  9998 in
let          tmp2 :=  9997 in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c0 :=  1010 in
let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in

let        mulr01 :=  1020 in
let        mulr11 :=  1021 in
let        mulr21 :=  1022 in
let        mulr31 :=  1023 in
let        mulr41 :=  1024 in

let        mulrax :=  1030 in
let        mulrdx :=  1031 in
let          mult :=  1032 in
let    mulredmask :=  1033 in
let       mulx219 :=  1034 in
let       mulx319 :=  1035 in
let       mulx419 :=  1036 in
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

Definition fe25519_sq (X Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(z0, z1, z2, z3, z4) := Z in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in
let            c5 :=  1015 in
let            c6 :=  1016 in
let            c7 :=  1017 in

let          x119 :=  1021 in
let          x219 :=  1022 in
let          x319 :=  1023 in
let          x419 :=  1024 in

let           r01 :=  1030 in
let           r11 :=  1031 in
let           r21 :=  1032 in
let           r31 :=  1033 in
let           r41 :=  1034 in
let           rax :=  1035 in
let           rdx :=  1036 in

let             t :=  1040 in
let       redmask :=  1041 in

let           tmp :=  9998 in
let         carry :=  9999 in

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

Definition fe25519_ladderstep : program :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
fe25519_add X2 Z2 T1 ++
fe25519_sub X2 Z2 T2 ++
fe25519_sq T2 T7 ++
fe25519_sq T1 T6 ++
fe25519_sub T6 T7 T5 ++
fe25519_add X3 Z3 T3 ++
fe25519_sub X3 Z3 T4 ++
fe25519_mul T3 T2 T9 ++
fe25519_mul T4 T1 T8 ++
fe25519_add T8 T9 X3_1 ++
fe25519_sub T8 T9 Z3_1 ++
fe25519_sq X3_1 X3' ++
fe25519_sq Z3_1 Z3_2 ++
fe25519_mul Z3_2 X1 Z3' ++
fe25519_mul T6 T7 X2' ++
fe25519_mul121666 T5 Z2_1 ++
fe25519_add Z2_1 T7 Z2_2 ++
fe25519_mul Z2_2 T5 Z2'.

Definition fe25519_ladderstep_inputs : VS.t :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
VSLemmas.OP.P.of_list (bi_list X1 ++ bi_list X2 ++ bi_list Z2 ++
                               bi_list X3 ++ bi_list Z3).

Definition bi_range (X : bi) max :=
  let '(x0, x1, x2, x3, x4) := X in
  bvands [::
            bvult (bvvar x0) max;
            bvult (bvvar x1) max;
            bvult (bvvar x2) max;
            bvult (bvvar x3) max;
            bvult (bvvar x4) max
         ].

Definition fe25519_ladderstep_pre : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bi_range X1 max;
          bi_range X2 max;
          bi_range Z2 max;
          bi_range X3 max;
          bi_range Z3 max
       ].

Definition fe25519_ladderstep_post1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bvEqMod
          (bi_limbs X2')
          (bvsq (bvsub (bvsq (bi_limbs X2)) (bvsq (bi_limbs Z2))))
          (bvposz n25519);
          bi_range X2' max
       ].

Definition fe25519_ladderstep_post2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bvEqMod
          (bi_limbs Z2')
          (bvmuls [:: bvposz 4%Z;
                     bi_limbs X2;
                     bi_limbs Z2;
                     bvadds [:: bvsq (bi_limbs X2);
                               bvmuls [:: bvposz 486662%Z; bi_limbs X2; bi_limbs Z2];
                               bvsq (bi_limbs Z2)]
          ])
          (bvposz n25519);
          bi_range Z2' max
       ].

Definition fe25519_ladderstep_post3 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bvEqMod
          (bvmul (bi_limbs X3')
                 (bvmul (bi_limbs X1)
                        (bvsq (bvsub (bvmul (bi_limbs X3) (bi_limbs Z2))
                                     (bvmul (bi_limbs X2) (bi_limbs Z3))))))
          (bvmul (bi_limbs Z3')
                 (bvsq (bvsub (bvmul (bi_limbs X2) (bi_limbs X3))
                              (bvmul (bi_limbs Z2) (bi_limbs Z3)))))
          (bvposz n25519);
          bi_range X3' max;
          bi_range Z3' max
       ].

Definition fe25519_ladderstep_post3_1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bvEqMod
          (bi_limbs X3')
          (bvmul (bvposz 4%Z)
                 (bvsq (bvsub (bvmul (bi_limbs X2) (bi_limbs X3))
                              (bvmul (bi_limbs Z2) (bi_limbs Z3)))))
          (bvposz n25519);
          bi_range X3' max
       ].

Definition fe25519_ladderstep_post3_2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
let max  := bvposz (2^51+2^15)%Z in
bvands [::
          bvEqMod
          (bi_limbs Z3')
          (bvmul (bvposz 4%Z)
                 (bvmul (bi_limbs X1)
                        (bvsq (bvsub (bvmul (bi_limbs X3) (bi_limbs Z2))
                                     (bvmul (bi_limbs X2) (bi_limbs Z3))))))
          (bvposz n25519);
          bi_range Z3' max
       ].

Definition fe25519_ladderstep_post : bexp :=
  bvands [:: fe25519_ladderstep_post1;
            fe25519_ladderstep_post2;
            fe25519_ladderstep_post3 ].

Definition fe25519_ladderstep_spec :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post |}.

Definition fe25519_ladderstep_spec1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post1 |}.

Definition fe25519_ladderstep_spec2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post2 |}.

Definition fe25519_ladderstep_spec3 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3 |}.

Definition fe25519_ladderstep_spec3_1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_1 |}.

Definition fe25519_ladderstep_spec3_2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_2 |}.

Lemma valid_fe25519_ladderstep3_2 : valid_bvspec (fe25519_ladderstep_inputs, fe25519_ladderstep_spec3_2).
Proof.
  time "valid_fe25519_ladderstep3_2" verify_bvspec.
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
