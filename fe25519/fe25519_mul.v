From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Definition fe25519_mul : program :=

let          qtwo :=   QConst (2%Z) in
let         wsize :=   64%positive in

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
      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): 620m14.276s *)
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

      (*   #// inv 0 <=u mem64[xp + 0]@u128, mem64[xp + 8]@u128, mem64[xp + 16]@u128, mem64[xp + 24]@u128, mem64[xp + 32]@u128 <=u 2**52 && *)

      (*   #//     0 <=u mem64[yp + 0]@u128, mem64[yp + 8]@u128, mem64[yp + 16]@u128, mem64[yp + 24]@u128, mem64[yp + 32]@u128 <=u 2**52 *)

      (*  *)

      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (*   mulrax *= 19 *)
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
      (*   mulx319_stack = mulrax *)
QAssign mulx319 (QVar mulrax);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   r0 = mulrax *)
QAssign r0 (QVar mulrax);
      (*   mulr01 = mulrdx *)
QAssign mulr01 (QVar mulrdx);
      (*  *)
      (*   #// inv mulx319_stack = 19 * mem64[xp + 24] *)
      (*  *)
      (*   #// var r0_0 = mulr01.r0 *)
      (*   #//     mulx319_128 = 19 * mem64[xp + 24]@u128 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (*   mulrax *= 19 *)
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
      (*   mulx419_stack = mulrax *)
QAssign mulx419 (QVar mulrax);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r0 += mulrax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
      (*   mulr01 += mulrdx + carry *)
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// inv mulx419_stack = 19 * mem64[xp + 32] *)
      (*  *)
      (*   #// var r0_1 = mulr01.r0 *)
      (*   #//     mulx419_128 = 19 * mem64[xp + 32]@u128 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     mulr01.r0 = r0_1 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r0 += mulrax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
      (*   mulr01 += mulrdx + carry *)
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   r1 = mulrax *)
QAssign r1 (QVar mulrax);
      (*   mulr11 = mulrdx *)
QAssign mulr11 (QVar mulrdx);
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_0 = mulr11.r1 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   r2 = mulrax *)
QAssign r2 (QVar mulrax);
      (*   mulr21 = mulrdx *)
QAssign mulr21 (QVar mulrdx);
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_0 = mulr11.r1 *)
      (*   #//     r2_0 = mulr21.r2 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_0 && *)
      (*   #//     mulr21.r2 = r2_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   r3 = mulrax *)
QAssign r3 (QVar mulrax);
      (*   mulr31 = mulrdx *)
QAssign mulr31 (QVar mulrdx);
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_0 = mulr11.r1 *)
      (*   #//     r2_0 = mulr21.r2 *)
      (*   #//     r3_0 = mulr31.r3 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_0 && *)
      (*   #//     mulr21.r2 = r2_0 && *)
      (*   #//     mulr31.r3 = r3_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   r4 = mulrax *)
QAssign r4 (QVar mulrax);
      (*   mulr41 = mulrdx *)
QAssign mulr41 (QVar mulrdx);
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_0 = mulr11.r1 *)
      (*   #//     r2_0 = mulr21.r2 *)
      (*   #//     r3_0 = mulr31.r3 *)
      (*   #//     r4_0 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_0 && *)
      (*   #//     mulr21.r2 = r2_0 && *)
      (*   #//     mulr31.r3 = r3_0 && *)
      (*   #//     mulr41.r4 = r4_0 *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r1 += mulrax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
      (*   mulr11 += mulrdx + carry *)
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_0 = mulr21.r2 *)
      (*   #//     r3_0 = mulr31.r3 *)
      (*   #//     r4_0 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_0 && *)
      (*   #//     mulr31.r3 = r3_0 && *)
      (*   #//     mulr41.r4 = r4_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r2 += mulrax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
      (*   mulr21 += mulrdx + carry *)
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_1 = mulr21.r2 *)
      (*   #//     r3_0 = mulr31.r3 *)
      (*   #//     r4_0 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_1 && *)
      (*   #//     mulr31.r3 = r3_0 && *)
      (*   #//     mulr41.r4 = r4_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r3 += mulrax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
      (*   mulr31 += mulrdx + carry *)
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_1 = mulr21.r2 *)
      (*   #//     r3_1 = mulr31.r3 *)
      (*   #//     r4_0 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_1 && *)
      (*   #//     mulr31.r3 = r3_1 && *)
      (*   #//     mulr41.r4 = r4_0 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r4 += mulrax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
      (*   mulr41 += mulrdx + carry *)
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_2 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_1 = mulr21.r2 *)
      (*   #//     r3_1 = mulr31.r3 *)
      (*   #//     r4_1 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_2 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_1 && *)
      (*   #//     mulr31.r3 = r3_1 && *)
      (*   #//     mulr41.r4 = r4_1 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (*   mulrax *= 19 *)
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r0 += mulrax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
      (*   mulr01 += mulrdx + carry *)
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_3 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_1 = mulr21.r2 *)
      (*   #//     r3_1 = mulr31.r3 *)
      (*   #//     r4_1 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + 19 * mem64[xp + 8]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_3 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_1 && *)
      (*   #//     mulr31.r3 = r3_1 && *)
      (*   #//     mulr41.r4 = r4_1 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r2 += mulrax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
      (*   mulr21 += mulrdx + carry *)
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_3 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_1 = mulr31.r3 *)
      (*   #//     r4_1 = mulr41.r4 *)
      (*   #//     mulx119_128 = 19 * mem64[xp + 8]@u128 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_3 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_1 && *)
      (*   #//     mulr41.r4 = r4_1 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r3 += mulrax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
      (*   mulr31 += mulrdx + carry *)
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_3 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_2 = mulr31.r3 *)
      (*   #//     r4_1 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     mulr01.r0 = r0_3 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_2 && *)
      (*   #//     mulr41.r4 = r4_1 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r4 += mulrax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
      (*   mulr41 += mulrdx + carry *)
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_3 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_2 = mulr31.r3 *)
      (*   #//     r4_2 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     mulr01.r0 = r0_3 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_2 && *)
      (*   #//     mulr41.r4 = r4_2 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (*   mulrax *= 19 *)
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r0 += mulrax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
      (*   mulr01 += mulrdx + carry *)
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_1 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_2 = mulr31.r3 *)
      (*   #//     r4_2 = mulr41.r4 *)
      (*   #//     mulx219_128 = 19 * mem64[xp + 16]@u128 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_1 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_2 && *)
      (*   #//     mulr41.r4 = r4_2 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (*   mulrax *= 19 *)
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r1 += mulrax *)
QAssign r1 (QBinop QMul (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
      (*   mulr11 += mulrdx + carry *)
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_2 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_2 = mulr31.r3 *)
      (*   #//     r4_2 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_2 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_2 && *)
      (*   #//     mulr41.r4 = r4_2 *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r3 += mulrax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
      (*   mulr31 += mulrdx + carry *)
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_2 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_2 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_2 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_2 *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r4 += mulrax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
      (*   mulr41 += mulrdx + carry *)
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_2 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_3 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_2 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_3 *)
      (*  *)
      (*   mulrax = mulx319_stack *)
QAssign mulrax (QVar mulx319);
      (*   #mulrax *= 19 *)
(* TODO: really? *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r1 += mulrax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
      (*   mulr11 += mulrdx + carry *)
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_3 = mulr11.r1 *)
      (*   #//     r2_2 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_3 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_3 && *)
      (*   #//     mulr21.r2 = r2_2 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_3 *)
      (*  *)
      (*   mulrax = mulx319_stack *)
QAssign mulrax (QVar mulx319);
      (*   #mulrax *= 19 *)
(* TODO: really? *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r2 += mulrax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
      (*   mulr21 += mulrdx + carry *)
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_3 = mulr11.r1 *)
      (*   #//     r2_3 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_3 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_3 = r2_2 + mulx319_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_3 && *)
      (*   #//     mulr21.r2 = r2_3 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_3 *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrdx (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r4 += mulrax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
      (*   mulr41 += mulrdx + carry *)
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_3 = mulr11.r1 *)
      (*   #//     r2_3 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_4 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_3 = r2_2 + mulx319_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_4 = r4_3 + mem64[xp + 32]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_3 && *)
      (*   #//     mulr21.r2 = r2_3 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_4 *)
      (*  *)
      (*   mulrax = mulx419_stack *)
QAssign mulrax (QVar mulx419);
      (*   #mulrax *= 19 *)
(* TODO: really? *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r1 += mulrax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
      (*   mulr11 += mulrdx + carry *)
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_4 = mulr11.r1 *)
      (*   #//     r2_3 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_4 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r1_4 = r1_3 + mulx419_128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_3 = r2_2 + mulx319_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_4 = r4_3 + mem64[xp + 32]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_4 && *)
      (*   #//     mulr21.r2 = r2_3 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_4 *)
      (*  *)
      (*   mulrax = mulx419_stack *)
QAssign mulrax (QVar mulx419);
      (*   #mulrax *= 19 *)
(* TODO: really? *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r2 += mulrax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
      (*   mulr21 += mulrdx + carry *)
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_4 = mulr11.r1 *)
      (*   #//     r2_4 = mulr21.r2 *)
      (*   #//     r3_3 = mulr31.r3 *)
      (*   #//     r4_4 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r1_4 = r1_3 + mulx419_128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_3 = r2_2 + mulx319_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r2_4 = r2_3 + mulx419_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_4 = r4_3 + mem64[xp + 32]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_4 && *)
      (*   #//     mulr21.r2 = r2_4 && *)
      (*   #//     mulr31.r3 = r3_3 && *)
      (*   #//     mulr41.r4 = r4_4 *)
      (*  *)
      (*   mulrax = mulx419_stack *)
QAssign mulrax (QVar mulx419);
      (*   #mulrax *= 19 *)
(* TODO: really? *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r3 += mulrax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
      (*   mulr31 += mulrdx + carry *)
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   #// var r0_4 = mulr01.r0 *)
      (*   #//     r1_4 = mulr11.r1 *)
      (*   #//     r2_4 = mulr21.r2 *)
      (*   #//     r3_4 = mulr31.r3 *)
      (*   #//     r4_4 = mulr41.r4 *)
      (*   #// cut r0_0 = mulx319_128 * mem64[yp + 16]@u128 && mulx319_128 = 19 * mem64[xp + 24]@u128 && *)
      (*   #//     r0_1 = r0_0 + mulx419_128 * mem64[yp + 8]@u128 && mulx419_128 = 19 * mem64[xp + 32]@u128 && *)
      (*   #//     r0_2 = r0_1 + mem64[xp + 0]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r0_3 = r0_2 + mulx119_128 * mem64[yp + 32]@u128 && mulx119_128 = 19 * mem64[xp + 8]@u128 && *)
      (*   #//     r0_4 = r0_3 + mulx219_128 * mem64[yp + 24]@u128 && mulx219_128 = 19 * mem64[xp + 16]@u128 && *)
      (*   #//     r1_0 = mem64[xp + 0]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r1_1 = r1_0 + mem64[xp + 8]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r1_2 = r1_1 + mulx219_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r1_3 = r1_2 + mulx319_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r1_4 = r1_3 + mulx419_128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_0 = mem64[xp + 0]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r2_1 = r2_0 + mem64[xp + 8]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r2_2 = r2_1 + mem64[xp + 16]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r2_3 = r2_2 + mulx319_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r2_4 = r2_3 + mulx419_128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_0 = mem64[xp + 0]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r3_1 = r3_0 + mem64[xp + 8]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r3_2 = r3_1 + mem64[xp + 16]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r3_3 = r3_2 + mem64[xp + 24]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     r3_4 = r3_3 + mulx419_128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_0 = mem64[xp + 0]@u128 * mem64[yp + 32]@u128 && *)
      (*   #//     r4_1 = r4_0 + mem64[xp + 8]@u128 * mem64[yp + 24]@u128 && *)
      (*   #//     r4_2 = r4_1 + mem64[xp + 16]@u128 * mem64[yp + 16]@u128 && *)
      (*   #//     r4_3 = r4_2 + mem64[xp + 24]@u128 * mem64[yp + 8]@u128 && *)
      (*   #//     r4_4 = r4_3 + mem64[xp + 32]@u128 * mem64[yp + 0]@u128 && *)
      (*   #//     mulr01.r0 = r0_4 && *)
      (*   #//     mulr11.r1 = r1_4 && *)
      (*   #//     mulr21.r2 = r2_4 && *)
      (*   #//     mulr31.r3 = r3_4 && *)
      (*   #//     mulr41.r4 = r4_4 *)
      (*  *)
      (*   # assert (mulr01.r0) = x0y0 + 19 * (x4y1 + x3y2 + x2y3 + x1y4) && *)
      (*   #        (mulr11.r1) = (x1y0 + x0y1) + 19 * (x4y2 + x3y3 + x2y4) && *)
      (*   #        (mulr21.r2) = (x2y0 + x1y1 + x0y2) + 19 * (x4y3 + x3y4) && *)
      (*   #        (mulr31.r3) = (x3y0 + x2y1 + x1y2 + x0y3) + 19 * (x4y4) && *)
      (*   #        (mulr41.r4) = (x4y0 + x3y1 + x2y2 + x1y3 + x0y4) *)
      (*  *)
      (*   #// cut 0 <=u mulr01.r0 <=u 2**52 * 2**52 + 19 * 2**52 * 2**52 * 4 && *)
      (*   #//     0 <=u mulr11.r1 <=u 2**52 * 2**52 * 2 + 19 * 2**52 * 2**52 * 3 && *)
      (*   #//     0 <=u mulr21.r2 <=u 2**52 * 2**52 * 3 + 19 * 2**52 * 2**52 * 2 && *)
      (*   #//     0 <=u mulr31.r3 <=u 2**52 * 2**52 * 4 + 19 * 2**52 * 2**52 && *)
      (*   #//     0 <=u mulr41.r4 <=u 2**52 * 2**52 * 5 *)
      (*  *)
      (*   #// var r0_512 = (mulr01.r0)@u512 *)
      (*   #//     r1_512 = (mulr11.r1)@u512 *)
      (*   #//     r2_512 = (mulr21.r2)@u512 *)
      (*   #//     r3_512 = (mulr31.r3)@u512 *)
      (*   #//     r4_512 = (mulr41.r4)@u512 *)
      (*  *)
      (*   mulredmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
QAssign mulredmask (QConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*    *)
      (*   mulr01 = (mulr01.r0) << 13 *)
QAssign tmp (concat_shift (QVar mulr01) (QVar r0) (13%positive));
QSplit mulr01 tmp (QVar tmp) wsize;
QSplit tmp mulr01 (QVar mulr01) wsize;
      (*   #mult = r0 *)
(* TODO: really? *)
      (*   r0 &= mulredmask *)
QSplit tmp r0 (QVar r0) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   #(uint64) mult >>= 51 *)
      (*   #mulr01 ^= mult *)
(* TODO: really? *)
      (*    *)
      (*   mulr11 = (mulr11.r1) << 13 *)
QAssign tmp (concat_shift (QVar mulr11) (QVar r1) (13%positive));
QSplit mulr11 tmp (QVar tmp) wsize;
QSplit tmp mulr11 (QVar mulr11) wsize;
      (*   #mult = r1 *)
(* TODO: really? *)
      (*   r1 &= mulredmask *)
QSplit tmp r1 (QVar r1) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1 += mulr01 *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulr01));
      (*   #(uint64) mult >>= 51 *)
      (*   #mulr11 ^= mult *)
(* TODO: really? *)
      (*    *)
      (*   mulr21 = (mulr21.r2) << 13 *)
QAssign tmp (concat_shift (QVar mulr21) (QVar r2) (13%positive));
QSplit mulr21 tmp (QVar tmp) wsize;
QSplit tmp mulr21 (QVar mulr21) wsize;
      (*   #mult = r2 *)
(* TODO: really? *)
      (*   r2 &= mulredmask *)
QSplit tmp r2 (QVar r2) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2 += mulr11 *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulr11));
      (*   #(uint64) mult >>= 51 *)
      (*   #mulr21 ^= mult *)
(* TODO: really? *)
      (*    *)
      (*   mulr31 = (mulr31.r3) << 13 *)
QAssign tmp (concat_shift (QVar mulr31) (QVar r3) (13%positive));
QSplit mulr31 tmp (QVar tmp) wsize;
QSplit tmp mulr31 (QVar mulr31) wsize;
      (*   #mult = r3 *)
(* TODO: really? *)
      (*   r3 &= mulredmask *)
QSplit tmp r3 (QVar r3) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r3 += mulr21 *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulr21));
      (*   #(uint64) mult >>= 51 *)
      (*   #mulr31 ^= mult *)
(* TODO: really? *)
      (*    *)
      (*   mulr41 = (mulr41.r4) << 13 *)
QAssign tmp (concat_shift (QVar mulr41) (QVar r4) (13%positive));
QSplit mulr41 tmp (QVar tmp) wsize;
QSplit tmp mulr41 (QVar mulr41) wsize;
      (*   #mult = r4 *)
(* TODO: really? *)
      (*   r4 &= mulredmask *)
QSplit tmp r4 (QVar r4) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4 += mulr31 *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulr31));
      (*   #(uint64) mult >>= 51 *)
      (*   #mulr41 ^= mult *)
(* TODO: really? *)
      (*   mulr41 = mulr41 * 19 *)
QAssign mulr41 (QBinop QMul (QVar mulr41) (QConst 19%Z));
      (*   r0 += mulr41 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulr41));
      (*  *)

      (*   #// var r0_512' = r0@u512 *)
      (*   #//     r1_512' = r1@u512 *)
      (*   #//     r2_512' = r2@u512 *)
      (*   #//     r3_512' = r3@u512 *)
      (*   #//     r4_512' = r4@u512 *)
      (*   #//     lhs = r0_512 + 2**51 * r1_512 + 2**102 * r2_512 + 2**153 * r3_512 + 2**204 * r4_512 *)
      (*   #//     rhs = r0_512' + 2**51 * r1_512' + 2**102 * r2_512' + 2**153 * r3_512' + 2**204 * r4_512' *)
      (*   #// assert (lhs - rhs) %u (2**255 - 19) = 0 *)
      (*  *)
      (*   #// cut 0 <=u r0 <=u 2**60 && *)
      (*   #//     0 <=u r1 <=u 2**60 && *)
      (*   #//     0 <=u r2 <=u 2**60 && *)
      (*   #//     0 <=u r3 <=u 2**60 && *)
      (*   #//     0 <=u r4 <=u 2**60 && *)
      (*   #//     mulredmask = mem64[crypto_sign_ed25519_amd64_51_REDMASK51] *)
      (*  *)
      (*   #// var r0_512 = r0@u512 *)
      (*   #//     r1_512 = r1@u512 *)
      (*   #//     r2_512 = r2@u512 *)
      (*   #//     r3_512 = r3@u512 *)
      (*   #//     r4_512 = r4@u512 *)
      (*  *)
      (*   mult = r0 *)
QAssign mult (QVar r0);
      (*   (uint64) mult >>= 51 *)
QSplit mult tmp (QVar mult) (51%positive);
      (*   mult += r1 *)
QAssign mult (QBinop QAdd (QVar mult) (QVar r1));
      (*   r1 = mult *)
QAssign r1 (QVar mult);
      (*   (uint64) mult >>= 51 *)
QSplit mult tmp (QVar mult) (51%positive);
      (*   r0 &= mulredmask *)
QSplit tmp r0 (QVar r0) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   mult += r2 *)
QAssign mult (QBinop QAdd (QVar mult) (QVar r2));
      (*   r2 = mult *)
QAssign r2 (QVar mult);
      (*   (uint64) mult >>= 51 *)
QSplit mult tmp (QVar mult) (51%positive);
      (*   r1 &= mulredmask *)
QSplit tmp r1 (QVar r1) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   mult += r3 *)
QAssign mult (QBinop QAdd (QVar mult) (QVar r3));
      (*   r3 = mult *)
QAssign r3 (QVar mult);
      (*   (uint64) mult >>= 51 *)
QSplit mult tmp (QVar mult) (51%positive);
      (*   r2 &= mulredmask *)
QSplit tmp r2 (QVar r2) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   mult += r4 *)
QAssign mult (QBinop QAdd (QVar mult) (QVar r4));
      (*   r4 = mult *)
QAssign r4 (QVar mult);
      (*   (uint64) mult >>= 51 *)
QSplit mult tmp (QVar mult) (51%positive);
      (*   r3 &= mulredmask *)
QSplit tmp r3 (QVar r3) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   mult *= 19 *)
QAssign mult (QBinop QMul (QVar mult) (QConst 19%Z));
      (*   r0 += mult *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mult));
      (*   r4 &= mulredmask *)
QSplit tmp r4 (QVar r4) crypto_sign_ed25519_amd64_51_REDMASK51_width;
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
      (* *[uint64 *](rp + 0) = r0 *)
QAssign z0 (QVar r0);
      (* *[uint64 *](rp + 8) = r1 *)
QAssign z1 (QVar r1);
      (* *[uint64 *](rp + 16) = r2 *)
QAssign z2 (QVar r2);
      (* *[uint64 *](rp + 24) = r3 *)
QAssign z3 (QVar r3);
      (* *[uint64 *](rp + 32) = r4 *)
QAssign z4 (QVar r4)
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
