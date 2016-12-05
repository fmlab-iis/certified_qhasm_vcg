From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_mul_stage3_2 : program :=

let          qtwo :=   QConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := QBinop QMul x (QPow qtwo n) in
let concat_shift hi lo w :=       (* (hi.lo) << w *)
      QBinop QMul (QBinop QAdd (QBinop QMul hi (QPow qtwo wsize)) lo)
                  (QPow qtwo w) in

let crypto_sign_ed25519_amd64_51_REDMASK51 :=
                       2251799813685247%Z in (* 0x7FFFFFFFFFFFF from consts *)
let crypto_sign_ed25519_amd64_51_REDMASK51_width :=
                       51%positive in        (* 51 bits *)

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
QAssign z0 (QVar r0);
QAssign z1 (QVar r1);
QAssign z2 (QVar r2);
QAssign z3 (QVar r3);
QAssign z4 (QVar r4);
      (*  *)
      (*   mult = r0 *)
      (*   (uint64) mult >>= 51 *)
      (*   mult += r1 *)
QAssign mult (QVar r0);
QSplit mult tmp (QVar mult) (51%positive);
QAssign mult (QBinop QAdd (QVar mult) (QVar r1));
      (*   r1 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r0 &= mulredmask *)
      (*   mult += r2 *)
QAssign r1 (QVar mult);
QSplit mult tmp2 (QVar mult) (51%positive);
QAssign r0 (QVar tmp);
QAssign mult (QBinop QAdd (QVar mult) (QVar r2));
      (*   r2 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r1 &= mulredmask *)
      (*   mult += r3 *)
QAssign r2 (QVar mult);
QSplit mult tmp (QVar mult) (51%positive);
QAssign r1 (QVar tmp2);
QAssign mult (QBinop QAdd (QVar mult) (QVar r3));
      (*   r3 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r2 &= mulredmask *)
      (*   mult += r4 *)
QAssign r3 (QVar mult);
QSplit mult tmp2 (QVar mult) (51%positive);
QAssign r2 (QVar tmp);
QAssign mult (QBinop QAdd (QVar mult) (QVar r4));
      (*   r4 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r3 &= mulredmask *)
QAssign r4 (QVar mult);
QSplit mult tmp (QVar mult) (51%positive);
QAssign r3 (QVar tmp2);
      (*   mult *= 19 *)
      (*   r0 += mult *)
      (*   r4 &= mulredmask *)
QAssign mult (QBinop QMul (QVar mult) (QConst 19%Z));
QAssign r0 (QBinop QAdd (QVar r0) (QVar mult));
QAssign r4 (QVar tmp)
      (*   #END MACRO mul *)

      (*  *)
      (*   #// var lhs = r0_512 + r1_512 * 2**51 + r2_512 * 2**102 + r3_512 * 2**153 + r4_512 * 2**204 *)
      (*   #//     rhs = r0@u512 + r1@u512 * 2**51 + r2@u512 * 2**102 + r3@u512 * 2**153 + r4@u512 * 2**204 *)
      (*  *)
      (*   #// assert 0 <=u r0 <=u 2**52 && *)
      (*   #//        0 <=u r1 <=u 2**52 && *)
      (*   #//        0 <=u r2 <=u 2**52 && *)
      (*   #//        0 <=u r3 <=u 2**52 && *)
      (*   #//        0 <=u r4 <=u 2**52 && *)
      (*   #//        (lhs - rhs) %u (2**255 - 19) = 0 *)
      (*  *)
] .

Definition fe25519_mul_stage3_2_inputs : VS.t :=
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
VSLemmas.OP.P.of_list [:: r0; r1; r2; r3; r4].

Definition fe25519_mul_stage3_2_pre : bexp := QTrue.

Definition fe25519_mul_stage3_2_post : bexp :=
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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (radix51 [::QVar z0; QVar z1; QVar z2; QVar z3; QVar z4])
  (radix51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (n25519).

Definition fe25519_mul_stage3_2_spec :=
  {| spre := fe25519_mul_stage3_2_pre;
     sprog := fe25519_mul_stage3_2;
     spost := fe25519_mul_stage3_2_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul_stage3_2 : valid_ispec (fe25519_mul_stage3_2_inputs, fe25519_mul_stage3_2_spec).
Proof.
  time "valid_fe25519_mul_stage3_2" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
