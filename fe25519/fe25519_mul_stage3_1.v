From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_mul_stage3_1 : program :=

let          qtwo :=   QConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := QBinop QMul x (QPow qtwo n) in

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
let           tmp := 998 in

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
QAssign z0 (QBinop QAdd (QVar r0) (pow2 (QVar mulr01) 64%positive));
QAssign z1 (QBinop QAdd (QVar r1) (pow2 (QVar mulr11) 64%positive));
QAssign z2 (QBinop QAdd (QVar r2) (pow2 (QVar mulr21) 64%positive));
QAssign z3 (QBinop QAdd (QVar r3) (pow2 (QVar mulr31) 64%positive));
QAssign z4 (QBinop QAdd (QVar r4) (pow2 (QVar mulr41) 64%positive));
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
QSplit tmp r0 (QVar r0) 51%positive;
QAssign mulr01 (QBinop QAdd (pow2 (QVar mulr01) 13%positive) (QVar tmp));
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
QSplit tmp r1 (QVar r1) 51%positive;
QAssign mulr11 (QBinop QAdd (pow2 (QVar mulr11) 13%positive) (QVar tmp));
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulr01));
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
QSplit tmp r2 (QVar r2) 51%positive;
QAssign mulr21 (QBinop QAdd (pow2 (QVar mulr21) 13%positive) (QVar tmp));
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulr11));
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
QSplit tmp r3 (QVar r3) 51%positive;
QAssign mulr31 (QBinop QAdd (pow2 (QVar mulr31) 13%positive) (QVar tmp));
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulr21));
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
QSplit tmp r4 (QVar r4) 51%positive;
QAssign mulr41 (QBinop QAdd (pow2 (QVar mulr41) 13%positive) (QVar tmp));
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulr31));
      (*   mulr41 = mulr41 * 19 *)
QAssign mulr41 (QBinop QMul (QVar mulr41) (QConst 19%Z));
      (*   r0 += mulr41 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulr41))
      (*  *)
      (*  *)
      (*  *)
      (*  *)
] .

Definition fe25519_mul_stage3_1_inputs : VS.t :=
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
VSLemmas.OP.P.of_list [:: mulr01; r0; mulr11; r1; mulr21; r2; mulr31; r3; mulr41; r4].

Definition fe25519_mul_stage3_1_pre : bexp := QTrue.

Definition fe25519_mul_stage3_1_post : bexp :=
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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (radix51 [::QVar z0; QVar z1; QVar z2; QVar z3; QVar z4])
  (radix51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (n25519).

Definition fe25519_mul_stage3_1_spec :=
  {| spre := fe25519_mul_stage3_1_pre;
     sprog := fe25519_mul_stage3_1;
     spost := fe25519_mul_stage3_1_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul_stage3_1 : valid_ispec (fe25519_mul_stage3_1_inputs, fe25519_mul_stage3_1_spec).
Proof.
  time "valid_fe25519_mul_stage3_1" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
