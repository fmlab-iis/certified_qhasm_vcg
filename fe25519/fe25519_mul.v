From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_mul : program :=

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
QAssign mulrax (QVar x3);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QAssign mulx319 (QVar mulrax);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r0 (QVar mulrax);
QAssign mulr01 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x4);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QAssign mulx419 (QVar mulrax);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r1 (QVar mulrax);
QAssign mulr11 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r2 (QVar mulrax);
QAssign mulr21 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r3 (QVar mulrax);
QAssign mulr31 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r4 (QVar mulrax);
QAssign mulr41 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar mulx319);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar mulx319);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mulredmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
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
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulr41));
      (*  *)
      (*  *)
      (*  *)
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
QAssign r4 (QVar tmp);
      (*   #END MACRO mul *)

      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
      (* *[uint64 *](rp + 8) = r1 *)
      (* *[uint64 *](rp + 16) = r2 *)
      (* *[uint64 *](rp + 24) = r3 *)
      (* *[uint64 *](rp + 32) = r4 *)
QAssign z0 (QVar r0);
QAssign z1 (QVar r1);
QAssign z2 (QVar r2);
QAssign z3 (QVar r3);
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

Definition fe25519_mul_pre : bexp := QTrue.

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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (
    (radix51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @*
    (radix51 [::QVar y0; QVar y1; QVar y2; QVar y3; QVar y4])
  )
  (radix51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (n25519).

Definition fe25519_mul_spec :=
  {| spre := fe25519_mul_pre;
     sprog := fe25519_mul;
     spost := fe25519_mul_post |}.

Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".
From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul : valid_ispec (fe25519_mul_inputs, fe25519_mul_spec).
Proof.
  time "valid_fe25519_mul" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
