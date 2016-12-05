From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_sq : program :=
let         wsize :=   64%positive in
let          qtwo :=   QConst (2%Z) in
let      pow2 x n := QBinop QMul x (QPow qtwo n) in

let            x0 :=   0 in (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in (* *[uint64 *](xp + 32) *)

let            z0 :=   5 in (* *[uint64 *](rp +  0) *)
let            z1 :=   6 in (* *[uint64 *](rp +  8) *)
let            z2 :=   7 in (* *[uint64 *](rp + 16) *)
let            z3 :=   8 in (* *[uint64 *](rp + 24) *)
let            z4 :=   9 in (* *[uint64 *](rp + 32) *)

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in

let            c1 :=  31 in
let            c2 :=  32 in
let            c3 :=  33 in
let            c4 :=  34 in
let            c5 :=  35 in
let            c6 :=  36 in
let            c7 :=  37 in

let          x119 :=  41 in
let          x219 :=  42 in
let          x319 :=  43 in
let          x419 :=  44 in

let           r01 :=  50 in
let           r11 :=  51 in
let           r21 :=  52 in
let           r31 :=  53 in
let           r41 :=  54 in
let           rax :=  55 in
let           rdx :=  56 in

let             t :=  60 in
let       redmask :=  61 in

let           tmp := 998 in
let         carry := 999 in

[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (*  *)
      (* input rp *)
      (* input xp *)
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

      (* #required for  macro *)

      (* int64 r01 *)
      (* int64 r11 *)
      (* int64 r21 *)
      (* int64 r31 *)
      (* int64 r41 *)
      (* int64 rax *)
      (* int64 rdx *)

      (* int64 t *)
      (* int64 redmask *)

      (*  *)
      (* enter fe25519_sq *)
      (*  *)
      (* c1_stack = c1 *)
      (* c2_stack = c2 *)
      (* c3_stack = c3 *)
      (* c4_stack = c4 *)
      (* c5_stack = c5 *)
      (* c6_stack = c6 *)
      (* c7_stack = c7 *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 0) *)
      (*   r0 = rax *)
      (*   r01 = rdx *)
QAssign rax (QVar x0);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x0)) wsize;
QAssign r0 (QVar rax);
QAssign r01 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   r1 = rax *)
      (*   r11 = rdx *)
QAssign rax (QVar x0);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x1)) wsize;
QAssign r1 (QVar rax);
QAssign r11 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   r2 = rax *)
      (*   r21 = rdx *)
QAssign rax (QVar x0);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
QAssign r2 (QVar rax);
QAssign r21 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   r3 = rax *)
      (*   r31 = rdx *)
QAssign rax (QVar x0);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
QAssign r3 (QVar rax);
QAssign r31 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   r4 = rax *)
      (*   r41 = rdx *)
QAssign rax (QVar x0);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
QAssign r4 (QVar rax);
QAssign r41 (QVar rdx);
      (*  *)
      (*   rax = *[uint64 *](xp + 8) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
QAssign rax (QVar x1);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x1)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
QSplit carry r2 (QVar r2) wsize;
QAssign r21 (QBinop QAdd (QVar r21) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
QAssign rax (QVar x1);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
QSplit carry r3 (QVar r3) wsize;
QAssign r31 (QBinop QAdd (QVar r31) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
QAssign rax (QVar x1);
QAssign rax (QBinop QMul (QVar rax) qtwo);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
QSplit carry r4 (QVar r4) wsize;
QAssign r41 (QBinop QAdd (QVar r41) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
QAssign rax (QVar x1);
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar rax));
QSplit carry r0 (QVar r0) wsize;
QAssign r01 (QBinop QAdd (QVar r01) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
QAssign rax (QVar x2);
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
QSplit carry r4 (QVar r4) wsize;
QAssign r41 (QBinop QAdd (QVar r41) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
QAssign rax (QVar x2);
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar rax));
QSplit carry r0 (QVar r0) wsize;
QAssign r01 (QBinop QAdd (QVar r01) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
QAssign rax (QVar x2);
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
QSplit carry r1 (QVar r1) wsize;
QAssign r11 (QBinop QAdd (QVar r11) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
QAssign rax (QVar x3);
QAssign rax (QBinop QMul (QVar rax) (QConst 19%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
QSplit carry r1 (QVar r1) wsize;
QAssign r11 (QBinop QAdd (QVar r11) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
QAssign rax (QVar x3);
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
QSplit carry r2 (QVar r2) wsize;
QAssign r21 (QBinop QAdd (QVar r21) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
QAssign rax (QVar x4);
QAssign rax (QBinop QMul (QVar rax) (QConst 19%Z));
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
QSplit carry r3 (QVar r3) wsize;
QAssign r31 (QBinop QAdd (QVar r31) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   r01 = (r01.r0) << 13 *)
      (*   r0 &= redmask *)
QSplit tmp r0 (QVar r0) 51%positive;
QAssign r01 (QBinop QAdd (pow2 (QVar r01) 13%positive) (QVar tmp));
      (*    *)
      (*   r11 = (r11.r1) << 13 *)
      (*   r1 &= redmask *)
      (*   r1 += r01 *)
QSplit tmp r1 (QVar r1) 51%positive;
QAssign r11 (QBinop QAdd (pow2 (QVar r11) 13%positive) (QVar tmp));
QAssign r1 (QBinop QAdd (QVar r1) (QVar r01));
      (*    *)
      (*   r21 = (r21.r2) << 13 *)
      (*   r2 &= redmask *)
      (*   r2 += r11 *)
QSplit tmp r2 (QVar r2) 51%positive;
QAssign r21 (QBinop QAdd (pow2 (QVar r21) 13%positive) (QVar tmp));
QAssign r2 (QBinop QAdd (QVar r2) (QVar r11));
      (*    *)
      (*   r31 = (r31.r3) << 13 *)
      (*   r3 &= redmask *)
      (*   r3 += r21 *)
QSplit tmp r3 (QVar r3) 51%positive;
QAssign r31 (QBinop QAdd (pow2 (QVar r31) 13%positive) (QVar tmp));
QAssign r3 (QBinop QAdd (QVar r3) (QVar r21));
      (*    *)
      (*   r41 = (r41.r4) << 13 *)
      (*   r4 &= redmask *)
      (*   r4 += r31 *)
QSplit tmp r4 (QVar r4) 51%positive;
QAssign r41 (QBinop QAdd (pow2 (QVar r41) 13%positive) (QVar tmp));
QAssign r4 (QBinop QAdd (QVar r4) (QVar r31));
      (*   r41 = r41 * 19 *)
QAssign r41 (QBinop QMul (QVar r41) (QConst 19%Z));
      (*   r0 += r41 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar r41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   t = r0 *)
      (*   (uint64) t >>= 51 *)
      (*   t += r1 *)
      (*   r0 &= redmask *)
QAssign t (QVar r0);
QSplit t tmp (QVar t) (51%positive);
QAssign t (QBinop QAdd (QVar t) (QVar r1));
QAssign r0 (QVar tmp);
      (*    *)
      (*   r1 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r2 *)
      (*   r1 &= redmask *)
QAssign r1 (QVar t);
QSplit t tmp (QVar t) (51%positive);
QAssign t (QBinop QAdd (QVar t) (QVar r2));
QAssign r1 (QVar tmp);
      (*    *)
      (*   r2 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r3 *)
      (*   r2 &= redmask *)
QAssign r2 (QVar t);
QSplit t tmp (QVar t) (51%positive);
QAssign t (QBinop QAdd (QVar t) (QVar r3));
QAssign r2 (QVar tmp);
      (*    *)
      (*   r3 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r4 *)
      (*   r3 &= redmask *)
QAssign r3 (QVar t);
QSplit t tmp (QVar t) (51%positive);
QAssign t (QBinop QAdd (QVar t) (QVar r4));
QAssign r3 (QVar tmp);
      (*    *)
      (*   r4 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t *= 19 *)
      (*   r0 += t *)
      (*   r4 &= redmask *)
QAssign r4 (QVar t);
QSplit t tmp (QVar t) (51%positive);
QAssign t (QBinop QMul (QVar t) (QConst 19%Z));
QAssign r0 (QBinop QAdd (QVar r0) (QVar t));
QAssign r4 (QVar tmp);
      (*   #END MACRO  *)
      (*  *)
      (*  *)
      (*  *)
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
      (*   *)
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

Definition fe25519_sq_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_sq_pre : bexp := QTrue.

Definition fe25519_sq_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            z0 :=   5 in
let            z1 :=   6 in
let            z2 :=   7 in
let            z3 :=   8 in
let            z4 :=   9 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (
    QPow (radix51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4]) 2
  )
  (radix51 [::QVar z0; QVar z1; QVar z2; QVar z3; QVar z4])
  (n25519).

Definition fe25519_sq_spec :=
  {| spre := fe25519_sq_pre;
     sprog := fe25519_sq;
     spost := fe25519_sq_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_sq : valid_ispec (fe25519_sq_inputs, fe25519_sq_spec).
Proof.
  time "valid_fe25519_sq" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.

