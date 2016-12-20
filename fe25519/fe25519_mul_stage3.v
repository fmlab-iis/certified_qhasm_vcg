From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul_stage3 : program :=

let          qtwo :=   zConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in
let concat_shift hi lo w :=       (* (hi.lo) << w *)
      zBinop zMul (zBinop zAdd (zBinop zMul hi (zPow qtwo wsize)) lo)
                  (zPow qtwo w) in

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
zAssign z0 (zBinop zAdd (zVar r0) (pow2 (zVar mulr01) 64%positive));
zAssign z1 (zBinop zAdd (zVar r1) (pow2 (zVar mulr11) 64%positive));
zAssign z2 (zBinop zAdd (zVar r2) (pow2 (zVar mulr21) 64%positive));
zAssign z3 (zBinop zAdd (zVar r3) (pow2 (zVar mulr31) 64%positive));
zAssign z4 (zBinop zAdd (zVar r4) (pow2 (zVar mulr41) 64%positive));
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
zSplit tmp r0 (zVar r0) 51%positive;
zAssign mulr01 (zBinop zAdd (pow2 (zVar mulr01) 13%positive) (zVar tmp));
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
zSplit tmp r1 (zVar r1) 51%positive;
zAssign mulr11 (zBinop zAdd (pow2 (zVar mulr11) 13%positive) (zVar tmp));
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulr01));
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
zSplit tmp r2 (zVar r2) 51%positive;
zAssign mulr21 (zBinop zAdd (pow2 (zVar mulr21) 13%positive) (zVar tmp));
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulr11));
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
zSplit tmp r3 (zVar r3) 51%positive;
zAssign mulr31 (zBinop zAdd (pow2 (zVar mulr31) 13%positive) (zVar tmp));
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulr21));
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
zSplit tmp r4 (zVar r4) 51%positive;
zAssign mulr41 (zBinop zAdd (pow2 (zVar mulr41) 13%positive) (zVar tmp));
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulr31));
      (*   mulr41 = mulr41 * 19 *)
zAssign mulr41 (zBinop zMul (zVar mulr41) (zConst 19%Z));
      (*   r0 += mulr41 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulr41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mult = r0 *)
      (*   (uint64) mult >>= 51 *)
      (*   mult += r1 *)
zAssign mult (zVar r0);
zSplit mult tmp (zVar mult) (51%positive);
zAssign mult (zBinop zAdd (zVar mult) (zVar r1));
      (*   r1 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r0 &= mulredmask *)
      (*   mult += r2 *)
zAssign r1 (zVar mult);
zSplit mult tmp2 (zVar mult) (51%positive);
zAssign r0 (zVar tmp);
zAssign mult (zBinop zAdd (zVar mult) (zVar r2));
      (*   r2 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r1 &= mulredmask *)
      (*   mult += r3 *)
zAssign r2 (zVar mult);
zSplit mult tmp (zVar mult) (51%positive);
zAssign r1 (zVar tmp2);
zAssign mult (zBinop zAdd (zVar mult) (zVar r3));
      (*   r3 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r2 &= mulredmask *)
      (*   mult += r4 *)
zAssign r3 (zVar mult);
zSplit mult tmp2 (zVar mult) (51%positive);
zAssign r2 (zVar tmp);
zAssign mult (zBinop zAdd (zVar mult) (zVar r4));
      (*   r4 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r3 &= mulredmask *)
zAssign r4 (zVar mult);
zSplit mult tmp (zVar mult) (51%positive);
zAssign r3 (zVar tmp2);
      (*   mult *= 19 *)
      (*   r0 += mult *)
      (*   r4 &= mulredmask *)
zAssign mult (zBinop zMul (zVar mult) (zConst 19%Z));
zAssign r0 (zBinop zAdd (zVar r0) (zVar mult));
zAssign r4 (zVar tmp)
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

Definition fe25519_mul_stage3_inputs : VS.t :=
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
VSLemmas.OP.P.of_list [:: mulr01; r0; mulr11; r1; mulr21; r2; mulr31; r3; mulr41; r4].

Definition fe25519_mul_stage3_pre : bexp := zTrue.

Definition fe25519_mul_stage3_post : bexp :=
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
zEqMod
  (radix51 [::zVar z0; zVar z1; zVar z2; zVar z3; zVar z4])
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (n25519).

Definition fe25519_mul_stage3_spec :=
  {| spre := fe25519_mul_stage3_pre;
     sprog := fe25519_mul_stage3;
     spost := fe25519_mul_stage3_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul_stage3 : valid_ispec (fe25519_mul_stage3_inputs, fe25519_mul_stage3_spec).
Proof.
  time "valid_fe25519_mul_stage3" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
