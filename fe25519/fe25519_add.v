From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

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
QAssign r0 (QVar x0);
      (* r1 = x1 *)
QAssign r1 (QVar x1);
      (* r2 = x2 *)
QAssign r2 (QVar x2);
      (* r3 = x3 *)
QAssign r3 (QVar x3);
      (* r4 = x4 *)
QAssign r4 (QVar x4);
      (* r0 += y0 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar y0));
      (* r1 += y1 *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar y1));
      (* r2 += y2 *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar y2));
      (* r3 += y3 *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar y3));
      (* r4 += y4 *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar y4))
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

Definition fe25519_add_pre : bexp := QTrue.

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
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (
    (radix51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @+
    (radix51 [::QVar y0; QVar y1; QVar y2; QVar y3; QVar y4])
  )
  (radix51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (n25519).

Definition fe25519_add_spec :=
  {| spre := fe25519_add_pre;
     sprog := fe25519_add;
     spost := fe25519_add_post |}.

From mathcomp Require Import ssreflect eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_add : valid_ispec (fe25519_add_inputs, fe25519_add_spec).
Proof.
  time "valid_fe25519_add" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
