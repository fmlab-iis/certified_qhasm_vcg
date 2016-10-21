From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Open Scope mqhasm_scope.

Definition fe25519_sub : program :=

let crypto_sign_ed25519_amd64_51_2P0 :=
                       4503599627370458%Z in (* 0xFFFFFFFFFFFDA from consts *)
let crypto_sign_ed25519_amd64_51_2P1234 :=
                       4503599627370494%Z in (* 0xFFFFFFFFFFFFE from consts *)

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
QAssign r0 (QVar x0);
      (* r1 = x1 *)
QAssign r1 (QVar x1);
      (* r2 = x2 *)
QAssign r2 (QVar x2);
      (* r3 = x3 *)
QAssign r3 (QVar x3);
      (* r4 = x4 *)
QAssign r4 (QVar x4);
      (* r0 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P0 *)
QAssign r0 (QBinop QAdd (QVar r0) (QConst crypto_sign_ed25519_amd64_51_2P0));
      (* r1 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
QAssign r1 (QBinop QAdd (QVar r1) (QConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r2 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
QAssign r2 (QBinop QAdd (QVar r2) (QConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r3 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
QAssign r3 (QBinop QAdd (QVar r3) (QConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r4 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
QAssign r4 (QBinop QAdd (QVar r4) (QConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r0 -= y0 *)
QAssign r0 (QBinop QSub (QVar r0) (QVar y0));
      (* r1 -= y1 *)
QAssign r1 (QBinop QSub (QVar r1) (QVar y1));
      (* r2 -= y2 *)
QAssign r2 (QBinop QSub (QVar r2) (QVar y2));
      (* r3 -= y3 *)
QAssign r3 (QBinop QSub (QVar r3) (QVar y3));
      (* r4 -= y4 *)
QAssign r4 (QBinop QSub (QVar r4) (QVar y4))
      (*  *)
      (* #// var sum_x = x0@u320 + x1@u320 * 2**51 + x2@u320 * 2**102 + x3@u320 * 2**153 + x4@u320 * 2**204 *)
      (* #//     sum_y = y0@u320 + y1@u320 * 2**51 + y2@u320 * 2**102 + y3@u320 * 2**153 + y4@u320 * 2**204 *)
      (* #//     sum_r = r0@u320 + r1@u320 * 2**51 + r2@u320 * 2**102 + r3@u320 * 2**153 + r4@u320 * 2**204 *)
      (* #// assert (sum_r - (sum_x - sum_y)) % (2**255 - 19) = 0 && *)
      (* #//        0 <=u r0, r1, r2, r3, r4 <u 2**54 *)
] .

Definition fe25519_sub_inputs : VS.t :=
let            x0 :=   0%nat in
let            x1 :=   1%nat in
let            x2 :=   2%nat in
let            x3 :=   3%nat in
let            x4 :=   4%nat in
let            y0 :=   5%nat in
let            y1 :=   6%nat in
let            y2 :=   7%nat in
let            y3 :=   8%nat in
let            y4 :=   9%nat in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4; y0; y1; y2; y3; y4].

Definition fe25519_sub_pre : bexp := QTrue.

Definition fe25519_sub_post : bexp :=
let            x0 :=   0%nat in
let            x1 :=   1%nat in
let            x2 :=   2%nat in
let            x3 :=   3%nat in
let            x4 :=   4%nat in
let            y0 :=   5%nat in
let            y1 :=   6%nat in
let            y2 :=   7%nat in
let            y3 :=   8%nat in
let            y4 :=   9%nat in
let            r0 :=  20%nat in
let            r1 :=  21%nat in
let            r2 :=  22%nat in
let            r3 :=  23%nat in
let            r4 :=  24%nat in
QCong
  (
    (limbs 51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @-
    (limbs 51 [::QVar y0; QVar y1; QVar y2; QVar y3; QVar y4])
  )
  (limbs 51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (2^255 - 19).

Definition fe25519_sub_spec :=
  {| spre := fe25519_sub_pre;
     sprog := fe25519_sub;
     spost := fe25519_sub_post |}.

Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".
From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_sub : valid_ispec (fe25519_sub_inputs, fe25519_sub_spec).
Proof.
  Time verify_ispec.
  (* 519.67s *)
Qed.
