From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition mul25519_stage1 : program :=

let          qtwo :=   zConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in

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
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r0l (zVar mulrax);
zAssign r0h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r1l = mulrax *)
      (* r1h = mulrdx *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r1l (zVar mulrax);
zAssign r1h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r1l += mulrax *)
      (* r1h += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r1l (zBinop zAdd (zVar r1l) (zVar mulrax));
zSplit carry r1l (zVar r1l) wsize;
zAssign r1h (zBinop zAdd (zVar r1h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r2l = mulrax *)
      (* r2h = mulrdx *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r2l (zVar mulrax);
zAssign r2h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r2l += mulrax *)
      (* r2h += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r2l += mulrax *)
      (* r2h += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r3l = mulrax *)
      (* r3h = mulrdx *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r3l (zVar mulrax);
zAssign r3h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r3l += mulrax *)
      (* r3h += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (* r4l = mulrax *)
      (* r4h = mulrdx *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r4l (zVar mulrax);
zAssign r4h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 0) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r4l += mulrax *)
      (* r4h += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (* r5l = mulrax *)
      (* r5h = mulrdx *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r5l (zVar mulrax);
zAssign r5h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 8) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r5l += mulrax *)
      (* r5h += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (* r6l = mulrax *)
      (* r6h = mulrdx *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r6l (zVar mulrax);
zAssign r6h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* carry? r6l += mulrax *)
      (* r6h += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r6l (zBinop zAdd (zVar r6l) (zVar mulrax));
zSplit carry r6l (zVar r6l) wsize;
zAssign r6h (zBinop zAdd (zVar r6h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 16) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r6l += mulrax *)
      (* r6h += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r6l (zBinop zAdd (zVar r6l) (zVar mulrax));
zSplit carry r6l (zVar r6l) wsize;
zAssign r6h (zBinop zAdd (zVar r6h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (* r7l = mulrax *)
      (* r7h = mulrdx *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r7l (zVar mulrax);
zAssign r7h (zVar mulrdx);
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 24) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* carry? r7l += mulrax *)
      (* r7h += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r7l (zBinop zAdd (zVar r7l) (zVar mulrax));
zSplit carry r7l (zVar r7l) wsize;
zAssign r7h (zBinop zAdd (zVar r7h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (* mulrax = *[uint64 *](xp + 32) *)
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (* r8l = mulrax *)
      (* r8h = mulrdx *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r8l (zVar mulrax);
zAssign r8h (zVar mulrdx)
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

Definition mul25519_stage1_pre : bexp := zTrue.

Definition mul25519_stage1_post : bexp :=
let      pow2 x n := zBinop zMul x (zPow qtwo n) in
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
zEq
  (
    (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
    @*
    (radix51 [::zVar y0; zVar y1; zVar y2; zVar y3; zVar y4])
  )
  (
    radix51 [:: zBinop zAdd (zVar r0l) (pow2 (zVar r0h) 64%positive);
                zBinop zAdd (zVar r1l) (pow2 (zVar r1h) 64%positive);
                zBinop zAdd (zVar r2l) (pow2 (zVar r2h) 64%positive);
                zBinop zAdd (zVar r3l) (pow2 (zVar r3h) 64%positive);
                zBinop zAdd (zVar r4l) (pow2 (zVar r4h) 64%positive);
                zBinop zAdd (zVar r5l) (pow2 (zVar r5h) 64%positive);
                zBinop zAdd (zVar r6l) (pow2 (zVar r6h) 64%positive);
                zBinop zAdd (zVar r7l) (pow2 (zVar r7h) 64%positive);
                zBinop zAdd (zVar r8l) (pow2 (zVar r8h) 64%positive)
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

Close Scope zdsl_scope.
Close Scope N_scope.
