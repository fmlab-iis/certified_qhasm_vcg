From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul_stage3_1 : program :=

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
zAssign z0 (zBinop zAdd (zVar r0) (zmul2p (zVar mulr01) 64));
zAssign z1 (zBinop zAdd (zVar r1) (zmul2p (zVar mulr11) 64));
zAssign z2 (zBinop zAdd (zVar r2) (zmul2p (zVar mulr21) 64));
zAssign z3 (zBinop zAdd (zVar r3) (zmul2p (zVar mulr31) 64));
zAssign z4 (zBinop zAdd (zVar r4) (zmul2p (zVar mulr41) 64));
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
zSplit tmp r0 (zVar r0) 51;
zAssign mulr01 (zBinop zAdd (zmul2p (zVar mulr01) 13) (zVar tmp));
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
zSplit tmp r1 (zVar r1) 51;
zAssign mulr11 (zBinop zAdd (zmul2p (zVar mulr11) 13) (zVar tmp));
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulr01));
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
zSplit tmp r2 (zVar r2) 51;
zAssign mulr21 (zBinop zAdd (zmul2p (zVar mulr21) 13) (zVar tmp));
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulr11));
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
zSplit tmp r3 (zVar r3) 51;
zAssign mulr31 (zBinop zAdd (zmul2p (zVar mulr31) 13) (zVar tmp));
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulr21));
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
zSplit tmp r4 (zVar r4) 51;
zAssign mulr41 (zBinop zAdd (zmul2p (zVar mulr41) 13) (zVar tmp));
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulr31));
      (*   mulr41 = mulr41 * 19 *)
zAssign mulr41 (zBinop zMul (zVar mulr41) (zConst 19%Z));
      (*   r0 += mulr41 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulr41))
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

Definition fe25519_mul_stage3_1_pre : bexp := zTrue.

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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
zEqMod
  (radix51 [::zVar z0; zVar z1; zVar z2; zVar z3; zVar z4])
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (zConst n25519).

Definition fe25519_mul_stage3_1_spec :=
  {| spre := fe25519_mul_stage3_1_pre;
     sprog := fe25519_mul_stage3_1;
     spost := fe25519_mul_stage3_1_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import zVerify.

Lemma valid_fe25519_mul_stage3_1 : valid_zspec (fe25519_mul_stage3_1_inputs, fe25519_mul_stage3_1_spec).
Proof.
  time "valid_fe25519_mul_stage3_1" verify_zspec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
