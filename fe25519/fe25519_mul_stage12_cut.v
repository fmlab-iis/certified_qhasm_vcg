From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import ssreflect seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul_stage12 : program :=

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

      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   mulrax *= 19 *)
      (*   mulx319_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r0 = mulrax *)
      (*   mulr01 = mulrdx *)
zAssign mulrax (zVar x3);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx319 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r0 (zVar mulrax);
zAssign mulr01 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx419 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r1 (zVar mulrax);
zAssign mulr11 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r2 (zVar mulrax);
zAssign mulr21 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r3 (zVar mulrax);
zAssign mulr31 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r4 (zVar mulrax);
zAssign mulr41 (zVar mulrdx);
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)))
      (*  *)
      (*  *)
      (*   # assert (mulr01.r0) = x0y0 + 19 * (x4y1 + x3y2 + x2y3 + x1y4) && *)
      (*   #        (mulr11.r1) = (x1y0 + x0y1) + 19 * (x4y2 + x3y3 + x2y4) && *)
      (*   #        (mulr21.r2) = (x2y0 + x1y1 + x0y2) + 19 * (x4y3 + x3y4) && *)
      (*   #        (mulr31.r3) = (x3y0 + x2y1 + x1y2 + x0y3) + 19 * (x4y4) && *)
      (*   #        (mulr41.r4) = (x4y0 + x3y1 + x2y2 + x1y3 + x0y4) *)
      (*  *)
] .

Definition fe25519_mul_stage12_inputs : VS.t :=
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

Definition fe25519_mul_stage12_pre : bexp := zTrue.

Definition fe25519_mul_stage12_post : bexp :=
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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
zEqMod
  (
    zmul (radix51 [:: zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
         (radix51 [:: zVar y0; zVar y1; zVar y2; zVar y3; zVar y4])
  )
  (
    radix51 [:: zBinop zAdd (zVar r0) (zmul2p (zVar mulr01) 64);
                zBinop zAdd (zVar r1) (zmul2p (zVar mulr11) 64);
                zBinop zAdd (zVar r2) (zmul2p (zVar mulr21) 64);
                zBinop zAdd (zVar r3) (zmul2p (zVar mulr31) 64);
                zBinop zAdd (zVar r4) (zmul2p (zVar mulr41) 64) ]
  )
  (zConst n25519).

Definition fe25519_mul_stage12_spec :=
  {| spre := fe25519_mul_stage12_pre;
     sprog := fe25519_mul_stage12;
     spost := fe25519_mul_stage12_post |}.



(* The first part. *)

Definition fe25519_mul_stage12_part1 : program :=

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
      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   mulrax *= 19 *)
      (*   mulx319_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r0 = mulrax *)
      (*   mulr01 = mulrdx *)
zAssign mulrax (zVar x3);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx319 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r0 (zVar mulrax);
zAssign mulr01 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx419 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r1 (zVar mulrax);
zAssign mulr11 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r2 (zVar mulrax);
zAssign mulr21 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r3 (zVar mulrax);
zAssign mulr31 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r4 (zVar mulrax);
zAssign mulr41 (zVar mulrdx);
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)))
] .

Definition fe25519_mul_stage12_part1_inputs : VS.t :=
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

Definition fe25519_mul_stage12_part1_pre : bexp := zTrue.

Definition fe25519_mul_stage12_part1_post : bexp :=
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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
zands [::
zEq
  (
    radix51 [:: zBinop zAdd (zVar r0) (zmul2p (zVar mulr01) 64);
                zBinop zAdd (zVar r1) (zmul2p (zVar mulr11) 64);
                zBinop zAdd (zVar r2) (zmul2p (zVar mulr21) 64);
                zBinop zAdd (zVar r3) (zmul2p (zVar mulr31) 64);
                zBinop zAdd (zVar r4) (zmul2p (zVar mulr41) 64)
            ]
  )
  (
    radix51 [:: zadds [:: zmul (zVar x0) (zVar y0);
                          zmuls [:: zVar x4; zVar y1; zConst 19];
                          zmuls [:: zVar x3; zVar y2; zConst 19];
                          zmuls [:: zVar x1; zVar y4; zConst 19] ];
                zadds [:: zmul (zVar x1) (zVar y0);
                          zmul (zVar x0) (zVar y1) ];
                zadds [:: zmul (zVar x2) (zVar y0);
                          zmul (zVar x1) (zVar y1);
                          zmul (zVar x0) (zVar y2) ];
                zadds [:: zmul (zVar x1) (zVar y2);
                          zmul (zVar x0) (zVar y3) ];
                zadds [:: zmul (zVar x1) (zVar y3);
                          zmul (zVar x0) (zVar y4) ]
            ]
  );
  zEq (zVar mulx319) (zmul (zVar x3) (zConst 19));
  zEq (zVar mulx419) (zmul (zVar x4) (zConst 19))
].

Definition fe25519_mul_stage12_part1_spec :=
  {| spre := fe25519_mul_stage12_part1_pre;
     sprog := fe25519_mul_stage12_part1;
     spost := fe25519_mul_stage12_part1_post |}.



(* The second part. *)

Definition fe25519_mul_stage12_part2 : program :=

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
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*    *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)))
      (*  *)
      (*  *)
      (*   # assert (mulr01.r0) = x0y0 + 19 * (x4y1 + x3y2 + x2y3 + x1y4) && *)
      (*   #        (mulr11.r1) = (x1y0 + x0y1) + 19 * (x4y2 + x3y3 + x2y4) && *)
      (*   #        (mulr21.r2) = (x2y0 + x1y1 + x0y2) + 19 * (x4y3 + x3y4) && *)
      (*   #        (mulr31.r3) = (x3y0 + x2y1 + x1y2 + x0y3) + 19 * (x4y4) && *)
      (*   #        (mulr41.r4) = (x4y0 + x3y1 + x2y2 + x1y3 + x0y4) *)
      (*  *)
] .

Definition fe25519_mul_stage12_part2_inputs : VS.t :=
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
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4; y0; y1; y2; y3; y4;
                          r0; mulr01; r1; mulr11; r2; mulr21; r3; mulr31; r4; mulr41;
                          mulx319; mulx419].

Definition fe25519_mul_stage12_part2_pre : bexp := fe25519_mul_stage12_part1_post.

Definition fe25519_mul_stage12_part2_post : bexp :=
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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
zEq
  (
    radix51 [:: zBinop zAdd (zVar r0) (zmul2p (zVar mulr01) 64);
                zBinop zAdd (zVar r1) (zmul2p (zVar mulr11) 64);
                zBinop zAdd (zVar r2) (zmul2p (zVar mulr21) 64);
                zBinop zAdd (zVar r3) (zmul2p (zVar mulr31) 64);
                zBinop zAdd (zVar r4) (zmul2p (zVar mulr41) 64)
            ]
  )
  (
    radix51 [:: zadds [:: zmul (zVar x0) (zVar y0);
                          zmul (zmul (zVar x4) (zVar y1)) (zConst 19);
                          zmul (zmul (zVar x3) (zVar y2)) (zConst 19);
                          zmul (zmul (zVar x2) (zVar y3)) (zConst 19);
                          zmul (zmul (zVar x1) (zVar y4)) (zConst 19) ];
                zadds [:: zmul (zVar x1) (zVar y0);
                          zmul (zVar x0) (zVar y1);
                          zmul (zmul (zVar x4) (zVar y2)) (zConst 19);
                          zmul (zmul (zVar x3) (zVar y3)) (zConst 19);
                          zmul (zmul (zVar x2) (zVar y4)) (zConst 19) ];
                zadds [:: zmul (zVar x2) (zVar y0);
                          zmul (zVar x1) (zVar y1);
                          zmul (zVar x0) (zVar y2);
                          zmul (zmul (zVar x4) (zVar y3)) (zConst 19);
                          zmul (zmul (zVar x3) (zVar y4)) (zConst 19) ];
                zadds [:: zmul (zVar x3) (zVar y0);
                          zmul (zVar x2) (zVar y1);
                          zmul (zVar x1) (zVar y2);
                          zmul (zVar x0) (zVar y3);
                          zmul (zmul (zVar x4) (zVar y4)) (zConst 19) ];
                zadds [:: zmul (zVar x4) (zVar y0);
                          zmul (zVar x3) (zVar y1);
                          zmul (zVar x2) (zVar y2);
                          zmul (zVar x1) (zVar y3);
                          zmul (zVar x0) (zVar y4) ]
            ]
  ).

Definition fe25519_mul_stage12_part2_spec :=
  {| spre := fe25519_mul_stage12_part2_pre;
     sprog := fe25519_mul_stage12_part2;
     spost := fe25519_mul_stage12_part2_post |}.



(* Verification. *)

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul_stage12_part1 :
  valid_spec fe25519_mul_stage12_part1_spec.
Proof.
  time "valid_fe25519_mul_stage12_part1" verify_spec fe25519_mul_stage12_part1_inputs.
Qed.

Lemma valid_fe25519_mul_stage12_part2 :
  valid_spec fe25519_mul_stage12_part2_spec.
Proof.
  time "valid_fe25519_mul_stage12_part2" verify_spec fe25519_mul_stage12_part2_inputs.
Qed.

Lemma post2_cong :
  fe25519_mul_stage12_part2_post ===> fe25519_mul_stage12_post.
Proof.
  time "post2_cong" verify_entail.
Qed.

Lemma valid_fe25519_mul_stage12 :
  valid_ispec (fe25519_mul_stage12_inputs, fe25519_mul_stage12_spec).
Proof.
  split; first by done.
  simpl.
  apply: (spec_weakening _ post2_cong).
  exact: (spec_concat
            valid_fe25519_mul_stage12_part1
            valid_fe25519_mul_stage12_part2).
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
