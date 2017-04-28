
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Bits.
From mQhasm Require Import bvDSL bvVerify Options.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.
Open Scope bvdsl_scope.

Definition fe25519_add : program :=

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

Definition fe25519_add_inputs : VS.t :=
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

Definition fe25519_add_pre : bexp :=
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
     bvult (bvvar x0) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar x1) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar x2) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar x3) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar x4) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar y0) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar y1) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar y2) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar y3) (bvposz (2^51 + 2^15)%Z);
     bvult (bvvar y4) (bvposz (2^51 + 2^15)%Z)
  ].

Definition radix51 := @limbs 51 320.

Definition fe25519_add_post : bexp :=
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
              @+
              (radix51 [:: bvvar y0; bvvar y1; bvvar y2; bvvar y3; bvvar y4])
          )
          (radix51 [:: bvvar r0; bvvar r1; bvvar r2; bvvar r3; bvvar r4])
          (bvposz n25519);
          bvult (bvvar r0) (bvposz (2^53)%Z);
          bvult (bvvar r1) (bvposz (2^53)%Z);
          bvult (bvvar r2) (bvposz (2^53)%Z);
          bvult (bvvar r3) (bvposz (2^53)%Z);
          bvult (bvvar r4) (bvposz (2^53)%Z)
       ].

Definition fe25519_add_spec :=
  {| spre := fe25519_add_pre;
     sprog := fe25519_add;
     spost := fe25519_add_post |}.

Lemma valid_fe25519_add : valid_bvspec (fe25519_add_inputs, fe25519_add_spec).
Proof.
  time "valid_fe25519_add" verify_bvspec.
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
