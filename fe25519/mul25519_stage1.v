From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition mul25519_stage1 : program :=

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
let         carry := 999 in
let           tmp := 998 in

let           r0l :=  20 in
let           r1l :=  21 in
let           r2l :=  22 in
let           r3l :=  23 in
let           r4l :=  24 in
let           r5l :=  25 in
let           r6l :=  26 in
let           r7l :=  27 in
let           r8l :=  28 in

let           r0h :=  40 in
let           r1h :=  41 in
let           r2h :=  42 in
let           r3h :=  43 in
let           r4h :=  44 in
let           r5h :=  45 in
let           r6h :=  46 in
let           r7h :=  47 in
let           r8h :=  48 in

let        mulrax :=  50 in
let        mulrdx :=  51 in
[::

      (*  mulrax = *[uint64 *](xp + 0) *)
      (*  (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*  r0l = mulrax *)
      (*  r0h = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r0l (QVar mulrax);
QAssign r0h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r1l = mulrax *)
      (* r1h = mulrdx *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r1l (QVar mulrax);
QAssign r1h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r1l += mulrax *)
      (* r1h += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r1l (QBinop QAdd (QVar r1l) (QVar mulrax));
QSplit carry r1l (QVar r1l) wsize;
QAssign r1h (QBinop QAdd (QVar r1h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r2l = mulrax *)
      (* r2h = mulrdx *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r2l (QVar mulrax);
QAssign r2h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r2l += mulrax *)
      (* r2h += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r2l += mulrax *)
      (* r2h += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r3l = mulrax *)
      (* r3h = mulrdx *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r3l (QVar mulrax);
QAssign r3h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r4l = mulrax *)
      (* r4h = mulrdx *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r4l (QVar mulrax);
QAssign r4h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* r5l = mulrax *)
      (* r5h = mulrdx *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r5l (QVar mulrax);
QAssign r5h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* r6l = mulrax *)
      (* r6h = mulrdx *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r6l (QVar mulrax);
QAssign r6h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r6l += mulrax *)
      (* r6h += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r6l (QBinop QAdd (QVar r6l) (QVar mulrax));
QSplit carry r6l (QVar r6l) wsize;
QAssign r6h (QBinop QAdd (QVar r6h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r6l += mulrax *)
      (* r6h += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r6l (QBinop QAdd (QVar r6l) (QVar mulrax));
QSplit carry r6l (QVar r6l) wsize;
QAssign r6h (QBinop QAdd (QVar r6h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* r7l = mulrax *)
      (* r7h = mulrdx *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r7l (QVar mulrax);
QAssign r7h (QVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r7l += mulrax *)
      (* r7h += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r7l (QBinop QAdd (QVar r7l) (QVar mulrax));
QSplit carry r7l (QVar r7l) wsize;
QAssign r7h (QBinop QAdd (QVar r7h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* r8l = mulrax *)
      (* r8h = mulrdx *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r8l (QVar mulrax);
QAssign r8h (QVar mulrdx)
] .

Definition mul25519_stage1_inputs : VS.t :=
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

Definition mul25519_stage1_pre : bexp := QTrue.

Definition mul25519_stage1_post : bexp :=
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
let         carry := 999 in
let           tmp := 998 in

let           r0l :=  20 in
let           r1l :=  21 in
let           r2l :=  22 in
let           r3l :=  23 in
let           r4l :=  24 in
let           r5l :=  25 in
let           r6l :=  26 in
let           r7l :=  27 in
let           r8l :=  28 in

let           r0h :=  40 in
let           r1h :=  41 in
let           r2h :=  42 in
let           r3h :=  43 in
let           r4h :=  44 in
let           r5h :=  45 in
let           r6h :=  46 in
let           r7h :=  47 in
let           r8h :=  48 in

let        mulrax :=  50 in
let        mulrdx :=  51 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEq
  (
    (radix51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @*
    (radix51 [::QVar y0; QVar y1; QVar y2; QVar y3; QVar y4])
  )
  (
    radix51 [:: QBinop QAdd (QVar r0l) (pow2 (QVar r0h) 64%positive);
                QBinop QAdd (QVar r1l) (pow2 (QVar r1h) 64%positive);
                QBinop QAdd (QVar r2l) (pow2 (QVar r2h) 64%positive);
                QBinop QAdd (QVar r3l) (pow2 (QVar r3h) 64%positive);
                QBinop QAdd (QVar r4l) (pow2 (QVar r4h) 64%positive);
                QBinop QAdd (QVar r5l) (pow2 (QVar r5h) 64%positive);
                QBinop QAdd (QVar r6l) (pow2 (QVar r6h) 64%positive);
                QBinop QAdd (QVar r7l) (pow2 (QVar r7h) 64%positive);
                QBinop QAdd (QVar r8l) (pow2 (QVar r8h) 64%positive)
            ]
  ).

Definition mul25519_stage1_spec :=
  {| spre := mul25519_stage1_pre;
     sprog := mul25519_stage1;
     spost := mul25519_stage1_post |}.

Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".
From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_mul25519_stage1 : valid_ispec (mul25519_stage1_inputs, mul25519_stage1_spec).
Proof.
  Time verify_ispec.
  (* 843.868s *)
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
