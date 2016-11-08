From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_mul121666 : program :=

let          qtwo :=   QConst 2%Z in
let         wsize :=   64%positive in

let concat_shift hi lo w :=       (* (hi.lo) << w *)
      QBinop QMul (QBinop QAdd (QBinop QMul hi (QPow qtwo wsize)) lo)
                  (QPow qtwo w) in

let crypto_sign_ed25519_amd64_51_121666_213 :=
                       996687872%Z in (* from consts *)
let crypto_sign_ed25519_amd64_51_REDMASK51_width :=
                       51%positive in        (* 51 bits *)

let            x0 :=   0 in     (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in     (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in     (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in     (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in     (* *[uint64 *](xp + 32) *)

let            z0 :=   5 in     (* *[uint64 *](rp +  0) *)
let            z1 :=   6 in     (* *[uint64 *](rp +  8) *)
let            z2 :=   7 in     (* *[uint64 *](rp + 16) *)
let            z3 :=   8 in     (* *[uint64 *](rp + 24) *)
let            z4 :=   9 in     (* *[uint64 *](rp + 32) *)

let            r0 :=  10 in     (* *[uint64 *](rp +  0) *)
let            r1 :=  11 in     (* *[uint64 *](rp +  8) *)
let            r2 :=  12 in     (* *[uint64 *](rp + 16) *)
let            r3 :=  13 in     (* *[uint64 *](rp + 24) *)
let            r4 :=  14 in     (* *[uint64 *](rp + 32) *)

let           rax :=  20 in
let           rdx :=  21 in

let           tmp := 998 in
let         carry := 999 in

[::

      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): ? *)
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
      (* #required for  macro *)
      (* int64 rax *)
      (* int64 rdx *)
      (*  *)
      (*  *)
      (*   #BEGIN MACRO callerregs_declare *)
      (*   int64 caller1 *)
      (*   int64 caller2 *)
      (*   int64 caller3 *)
      (*   int64 caller4 *)
      (*   int64 caller5 *)
      (*   int64 caller6 *)
      (*   int64 caller7 *)
      (*   caller caller1 *)
      (*   caller caller2 *)
      (*   caller caller3 *)
      (*   caller caller4 *)
      (*   caller caller5 *)
      (*   caller caller6 *)
      (*   caller caller7 *)
      (*   stack64 caller1_stack *)
      (*   stack64 caller2_stack *)
      (*   stack64 caller3_stack *)
      (*   stack64 caller4_stack *)
      (*   stack64 caller5_stack *)
      (*   stack64 caller6_stack *)
      (*   stack64 caller7_stack *)
      (*   #END MACRO callerregs_declare *)
      (*  *)
      (*  *)
      (* enter fe25519_mul121666 *)
      (*  *)
      (*  *)
      (*   #BEGIN MACRO callerregs_save *)
      (*   caller1_stack = caller1 *)
      (*   caller2_stack = caller2 *)
      (*   caller3_stack = caller3 *)
      (*   caller4_stack = caller4 *)
      (*   caller5_stack = caller5 *)
      (*   caller6_stack = caller6 *)
      (*   caller7_stack = caller7 *)
      (*   #END MACRO callerregs_save *)
      (*  *)
      (* ################################################################### *)
      (* # Conditions on the inputs: x0 = *[uint64 *](xp +  0), *)
      (* #                           x1 = *[uint64 *](xp +  8), *)
      (* #                           x2 = *[uint64 *](xp + 16), *)
      (* #                           x3 = *[uint64 *](xp + 24), *)
      (* #                           x4 = *[uint64 *](xp + 32), are all in [0,2^64-1] (whole uint64 range) *)
      (* # *)
      (* ################################################################### *)
      (*  *)
      (*  *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x0);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
QSplit rdx rax (QBinop QMul (QVar rax) (QConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
QSplit rax tmp (QVar rax) 13%positive;
      (*   r0 = rax *)
QAssign r0 (QVar rax);
      (*   r1 = rdx *)
QAssign r1 (QVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 8) *)
QAssign rax (QVar x1);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
QSplit rdx rax (QBinop QMul (QVar rax) (QConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
QSplit rax tmp (QVar rax) 13%positive;
      (*   r1 += rax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
      (*   r2 = rdx *)
QAssign r2 (QVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
QAssign rax (QVar x2);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
QSplit rdx rax (QBinop QMul (QVar rax) (QConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
QSplit rax tmp (QVar rax) 13%positive;
      (*   r2 += rax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
      (*   r3 = rdx *)
QAssign r3 (QVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
QAssign rax (QVar x3);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
QSplit rdx rax (QBinop QMul (QVar rax) (QConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
QSplit rax tmp (QVar rax) 13%positive;
      (*   r3 += rax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
      (*   r4 = rdx *)
QAssign r4 (QVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
QAssign rax (QVar x4);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
QSplit rdx rax (QBinop QMul (QVar rax) (QConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
QSplit rax tmp (QVar rax) 13%positive;
      (*   r4 += rax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
      (*   rdx *= 19 *)
QAssign rdx (QBinop QMul (QVar rdx) (QConst 19%Z));
      (*   r0 += rdx *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar rdx));
      (*   #END MACRO  *)
      (*  *)
      (*   #// var x0 = mem64[xp + 0]@u320 *)
      (*   #//     x1 = mem64[xp + 8]@u320 *)
      (*   #//     x2 = mem64[xp + 16]@u320 *)
      (*   #//     x3 = mem64[xp + 24]@u320 *)
      (*   #//     x4 = mem64[xp + 32]@u320 *)
      (*   #//     lhs = (x0 + x1 * 2**51 + x2 * 2**102 + x3 * 2**153 + x4 * 2**204) * 121666 *)
      (*   #//     rhs = r0@u320 + r1@u320 * 2**51 + r2@u320 * 2**102 + r3@u320 * 2**153 + r4@u320 * 2**204 *)
      (*   #// assert lhs >=u rhs && (lhs - rhs) %u (2**255 - 19) = 0 && *)
      (*   #//        0 <=u r0 <u 2**52 && *)
      (*   #//        0 <=u r1 <u 2**52 && *)
      (*   #//        0 <=u r2 <u 2**52 && *)
      (*   #//        0 <=u r3 <u 2**52 && *)
      (*   #//        0 <=u r4 <u 2**52 *)
      (*  *)
      (* ################################################################### *)
      (* # The following should hold at this point: *)
      (* # *)
      (* # (x0 + 2^51*x1 + 2^102*x2 + 2^153*x3 + 2^204*x4) * 121666 congruent to (r0 + r1*2^51 + r2*2^102 + r3*2^153 + r4*2^204)  [modulo 2^255-19] *)
      (* # *)
      (* # r0l,r1l,r2l,r3l,r4l are all in [0,2^52] *)
      (* # *)
      (* ################################################################### *)
      (*   *)
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
      (*  *)
      (*  *)
      (*   #BEGIN MACRO callerregs_restore *)
      (*   caller1 = caller1_stack *)
      (*   caller2 = caller2_stack *)
      (*   caller3 = caller3_stack *)
      (*   caller4 = caller4_stack *)
      (*   caller5 = caller5_stack *)
      (*   caller6 = caller6_stack *)
      (*   caller7 = caller7_stack *)
      (*   #END MACRO callerregs_restore *)
      (*  *)
      (*  *)
      (* leave *)
] .

Definition fe25519_mul121666_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_mul121666_pre : bexp := QTrue.

Definition fe25519_mul121666_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            r0 :=  10 in
let            r1 :=  11 in
let            r2 :=  12 in
let            r3 :=  13 in
let            r4 :=  14 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QCong
  (
    (radix51 [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @*
    (QConst 121666)
  )
  (radix51 [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
  (n25519).

Definition fe25519_mul121666_spec :=
  {| spre := fe25519_mul121666_pre;
     sprog := fe25519_mul121666;
     spost := fe25519_mul121666_post |}.

Add Rec LoadPath "../lib/gbarith/src/" as GBArith.
Add ML Path "../lib/gbarith/src/".
From mathcomp Require Import ssreflect eqtype ssrbool.
From mQhasm Require Import mQhasm SSA PolyGen Verify.

Lemma valid_fe25519_mul121666 : valid_ispec (fe25519_mul121666_inputs, fe25519_mul121666_spec).
Proof.
  Time verify_ispec.
  (* *)
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
