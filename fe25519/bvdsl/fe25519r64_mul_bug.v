
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From Common Require Import Var Bits.
From mQhasm Require Import bvDSL bvVerify Options zVerify.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This is a buggy implementation of fe25519_mul with
   radix 2^64 representation. *)

Open Scope N_scope.
Open Scope bvdsl_scope.

Definition fe25519r64_mul_bug : program :=

let         wsize :=   64%nat in

let            xp0 :=   0 in (* *[uint64 *](xp +  0) *)
let            xp1 :=   1 in (* *[uint64 *](xp +  8) *)
let            xp2 :=   2 in (* *[uint64 *](xp + 16) *)
let            xp3 :=   3 in (* *[uint64 *](xp + 24) *)
let            yp0 :=   4 in (* *[uint64 *](yp +  0) *)
let            yp1 :=   5 in (* *[uint64 *](yp +  8) *)
let            yp2 :=   6 in (* *[uint64 *](yp + 16) *)
let            yp3 :=   7 in (* *[uint64 *](yp + 24) *)
let         carry := 999 in

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in

let         mulr4 := 30 in
let         mulr5 := 31 in
let         mulr6 := 32 in
let         mulr7 := 33 in

let        mulrax := 40 in
let        mulrdx := 41 in

let         mulx0 := 50 in
let         mulx1 := 51 in
let         mulx2 := 52 in
let         mulx3 := 53 in

let          mulc := 60 in
let       mulzero := 61 in
let        muli38 := 62 in
[::

   (* int64 rp *)
   (* int64 xp *)
   (* int64 yp *)

   (* input rp *)
   (* input xp *)
   (* input yp *)

   (* int64 r0 *)
   (* int64 r1 *)
   (* int64 r2 *)
   (* int64 r3 *)

   (* #BEGIN MACRO callerregs_declare *)
   (* int64 caller1 *)
   (* int64 caller2 *)
   (* int64 caller3 *)
   (* int64 caller4 *)
   (* int64 caller5 *)
   (* int64 caller6 *)
   (* int64 caller7 *)
   (* caller caller1 *)
   (* caller caller2 *)
   (* caller caller3 *)
   (* caller caller4 *)
   (* caller caller5 *)
   (* caller caller6 *)
   (* caller caller7 *)
   (* stack64 caller1_stack *)
   (* stack64 caller2_stack *)
   (* stack64 caller3_stack *)
   (* stack64 caller4_stack *)
   (* stack64 caller5_stack *)
   (* stack64 caller6_stack *)
   (* stack64 caller7_stack *)
   (* #END MACRO callerregs_declare *)

   (* # Required for the mul template *)
   (* int64 mulr4 *)
   (* int64 mulr5 *)
   (* int64 mulr6 *)
   (* int64 mulr7 *)
   (* int64 mulrax *)
   (* int64 mulrdx *)
   (* int64 mulx0 *)
   (* int64 mulx1 *)
   (* int64 mulx2 *)
   (* int64 mulx3 *)
   (* int64 mulc *)
   (* int64 mulzero *)
   (* int64 muli38 *)

   (* enter fe25519_mul *)

   (* #BEGIN MACRO callerregs_save *)
   (* caller1_stack = caller1 *)
   (* caller2_stack = caller2 *)
   (* caller3_stack = caller3 *)
   (* caller4_stack = caller4 *)
   (* caller5_stack = caller5 *)
   (* caller6_stack = caller6 *)
   (* caller7_stack = caller7 *)
   (* #END MACRO callerregs_save *)

   (* yp = yp *)

   (* #BEGIN MACRO mul *)

   (* mulr4 = 0 *)
   (* mulr5 = 0 *)
   (* mulr6 = 0 *)
   (* mulr7 = 0 *)
   bvAssign mulr4 (bvConst 0);
   bvAssign mulr5 (bvConst 0);
   bvAssign mulr6 (bvConst 0);
   bvAssign mulr7 (bvConst 0);

   (* mulx0 = *[uint64 *](xp + 0) *)
   (* mulrax = *[uint64 *](yp + 0) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx0 *)
   (* r0 = mulrax *)
   (* r1 = mulrdx *)
   bvAssign mulx0 (bvVar xp0);
   bvAssign mulrax (bvVar yp0);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx0);
   bvAssign r0 (bvVar mulrax);
   bvAssign r1 (bvVar mulrdx);

   (* mulrax = *[uint64 *](yp + 8) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx0 *)
   (* carry? r1 += mulrax *)
   (* r2 = 0 *)
   (* r2 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp1);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx0);
   bvAddC carry r1 (bvVar r1) (bvVar mulrax);
   bvAssign r2 (bvConst 0);
   bvAdc r2 (bvVar r2) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 16) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx0 *)
   (* carry? r2 += mulrax *)
   (* r3 = 0 *)
   (* r3 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp2);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx0);
   bvAddC carry r2 (bvVar r2) (bvVar mulrax);
   bvAssign r3 (bvConst 0);
   bvAdc r3 (bvVar r3) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 24) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx0 *)
   (* carry? r3 += mulrax *)
   (* mulr4 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp3);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx0);
   bvAddC carry r3 (bvVar r3) (bvVar mulrax);
   bvAdc mulr4 (bvVar mulr4) (bvVar mulrdx) carry;

   (* mulx1 = *[uint64 *](xp + 8) *)
   (* mulrax = *[uint64 *](yp + 0) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx1 *)
   (* carry? r1 += mulrax *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulx1 (bvVar xp1);
   bvAssign mulrax (bvVar yp0);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx1);
   bvAddC carry r1 (bvVar r1) (bvVar mulrax);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 8) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx1 *)
   (* carry? r2 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? r2 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp1);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx1);
   bvAddC carry r2 (bvVar r2) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry r2 (bvVar r2) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 16) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx1 *)
   (* carry? r3 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? r3 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp2);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx1);
   bvAddC carry r3 (bvVar r3) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry r3 (bvVar r3) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 24) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx1 *)
   (* carry? mulr4 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr4 += mulc *)
   (* mulr5 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp3);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx1);
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulc);
   bvAdc mulr5 (bvVar mulr5) (bvVar mulrdx) carry;

   (* mulx2 = *[uint64 *](xp + 16) *)
   (* mulrax = *[uint64 *](yp + 0) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx2 *)
   (* carry? r2 += mulrax *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulx2 (bvVar xp2);
   bvAssign mulrax (bvVar yp0);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx2);
   bvAddC carry r2 (bvVar r2) (bvVar mulrax);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 8) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx2 *)
   (* carry? r3 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? r3 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp1);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx2);
   bvAddC carry r3 (bvVar r3) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry r3 (bvVar r3) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 16) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx2 *)
   (* carry? mulr4 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr4 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp2);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx2);
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 24) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx2 *)
   (* carry? mulr5 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr5 += mulc *)
   (* mulr6 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp3);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx2);
   bvAddC carry mulr5 (bvVar mulr5) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr5 (bvVar mulr5) (bvVar mulc);
   bvAdc mulr6 (bvVar mulr6) (bvVar mulrdx) carry;

   (* mulx3 = *[uint64 *](xp + 24) *)
   (* mulrax = *[uint64 *](yp + 0) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx3 *)
   (* carry? r3 += mulrax *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulx3 (bvVar xp3);
   bvAssign mulrax (bvVar yp0);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx3);
   bvAddC carry r3 (bvVar r3) (bvVar mulrax);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 8) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx3 *)
   (* carry? mulr4 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr4 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp1);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx3);
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr4 (bvVar mulr4) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 16) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx3 *)
   (* carry? mulr5 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr5 += mulc *)
   (* mulc = 0 *)
   (* mulc += mulrdx + carry *)
   bvAssign mulrax (bvVar yp2);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx3);
   bvAddC carry mulr5 (bvVar mulr5) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr5 (bvVar mulr5) (bvVar mulc);
   bvAssign mulc (bvConst 0);
   bvAdc mulc (bvVar mulc) (bvVar mulrdx) carry;

   (* mulrax = *[uint64 *](yp + 24) *)
   (* (uint128) mulrdx mulrax = mulrax * mulx3 *)
   (* carry? mulr6 += mulrax *)
   (* mulrdx += 0 + carry *)
   (* carry? mulr6 += mulc *)
   (* mulr7 += mulrdx + carry *)
   bvAssign mulrax (bvVar yp3);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvVar mulx3);
   bvAddC carry mulr6 (bvVar mulr6) (bvVar mulrax);
   bvAdc mulrdx (bvVar mulrdx) (bvConst 0) carry;
   bvAddC carry mulr6 (bvVar mulr6) (bvVar mulc);
   bvAdc mulr7 (bvVar mulr7) (bvVar mulrdx) carry;

   (* mulrax = mulr4 *)
   (* (uint128) mulrdx mulrax = mulrax * *[uint64 *]&crypto_sign_ed25519_amd64_64_38 *)
   (* carry? r0 += mulrax *)
   (* carry? r1 += mulrdx + carry *)
   (* r1 += 0 + carry *)
   bvAssign mulrax (bvVar mulr4);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvConst (fromPosZ 38%Z));
   bvAddC carry r0 (bvVar r0) (bvVar mulrax);
   bvAdcC carry r1 (bvVar r1) (bvVar mulrdx) carry;
   bvAdc r1 (bvVar r1) (bvConst 0) carry;

   (* mulrax = mulr5 *)
   (* (uint128) mulrdx mulrax = mulrax * *[uint64 *]&crypto_sign_ed25519_amd64_64_38 *)
   (* carry? r1 += mulrax *)
   (* carry? r2 += mulrdx + carry *)
   (* r2 += 0 + carry *)
   bvAssign mulrax (bvVar mulr5);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvConst (fromPosZ 38%Z));
   bvAddC carry r1 (bvVar r1) (bvVar mulrax);
   bvAdcC carry r2 (bvVar r2) (bvVar mulrdx) carry;
   bvAdc r2 (bvVar r2) (bvConst 0) carry;

   (* mulrax = mulr6 *)
   (* (uint128) mulrdx mulrax = mulrax * *[uint64 *]&crypto_sign_ed25519_amd64_64_38 *)
   (* carry? r2 += mulrax *)
   (* carry? r3 += mulrdx + carry *)
   (* r3 += 0 + carry *)
   bvAssign mulrax (bvVar mulr6);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvConst (fromPosZ 38%Z));
   bvAddC carry r2 (bvVar r2) (bvVar mulrax);
   bvAdcC carry r3 (bvVar r3) (bvVar mulrdx) carry;
   bvAdc r3 (bvVar r3) (bvConst 0) carry;

   (* mulrax = mulr7 *)
   (* (uint128) mulrdx mulrax = mulrax * *[uint64 *]&crypto_sign_ed25519_amd64_64_38 *)
   (* carry? r3 += mulrax *)
   (* mulr4 = 0 *)
   (* mulr4 += mulrdx + carry *)
   bvAssign mulrax (bvVar mulr7);
   bvMulf mulrdx mulrax (bvVar mulrax) (bvConst (fromPosZ 38%Z));
   bvAddC carry r3 (bvVar r3) (bvVar mulrax);
   bvAssign mulr4 (bvConst 0);
   bvAdc mulr4 (bvVar mulr4) (bvVar mulrdx) carry;

   (* mulr4 *= 38 *)
   bvMul mulr4 (bvVar mulr4) (bvConst (fromPosZ 38%Z));

   (* carry? r0 += mulr4 *)
   (* carry? r1 += 0 + carry *)
   (* carry? r2 += 0 + carry *)
   (* carry? r3 += 0 + carry *)
   bvAddC carry r0 (bvVar r0) (bvVar mulr4);
   bvAdcC carry r1 (bvVar r1) (bvConst 0) carry;
   bvAdcC carry r2 (bvVar r2) (bvConst 0) carry;
   bvAdcC carry r3 (bvVar r3) (bvConst 0) carry;

   (* mulzero = 0 *)
   (* muli38 = 38 *)
   (* mulzero = muli38 if carry *)
   (* r0 += mulzero *)
   bvAssign mulzero (bvConst (fromPosZ 0%Z));
   bvAssign muli38 (bvConst (fromPosZ 38%Z));
   bvMul mulzero (bvVar muli38) (bvVar carry);
   bvAdd r0 (bvVar r0) (bvVar mulzero)

   (* #END MACRO mul *)

] .

Definition fe25519r64_mul_bug_inputs : VS.t :=
let            xp0 :=   0 in
let            xp1 :=   1 in
let            xp2 :=   2 in
let            xp3 :=   3 in
let            yp0 :=   4 in
let            yp1 :=   5 in
let            yp2 :=   6 in
let            yp3 :=   7 in
VSLemmas.OP.P.of_list [:: xp0; xp1; xp2; xp3; yp0; yp1; yp2; yp3].

Definition fe25519r64_mul_bug_pre : bexp := bvTrue.

Definition radix64 := @limbs 64.

Definition fe25519r64_mul_bug_post : bexp :=
let            xp0 :=   0 in
let            xp1 :=   1 in
let            xp2 :=   2 in
let            xp3 :=   3 in
let            yp0 :=   4 in
let            yp1 :=   5 in
let            yp2 :=   6 in
let            yp3 :=   7 in
let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z in
bvands2
  [::
     bveEqMod
     (
       (radix64 [:: bvevar xp0; bvevar xp1; bvevar xp2; bvevar xp3])
       *e
       (radix64 [:: bvevar yp0; bvevar yp1; bvevar yp2; bvevar yp3])
     )
     (radix64 [:: bvevar r0; bvevar r1; bvevar r2; bvevar r3])
     (bvconst n25519)
  ]
  [:: ].

Definition fe25519r64_mul_bug_spec :=
  {| spre := fe25519r64_mul_bug_pre;
     sprog := fe25519r64_mul_bug;
     spost := fe25519r64_mul_bug_post |}.

Lemma valid_fe25519r64_mul_bug :
  valid_bvspec (fe25519r64_mul_bug_inputs, fe25519r64_mul_bug_spec).
Proof.
  time "valid_fe25519r64_mul_bug" verify_bvspec.
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
