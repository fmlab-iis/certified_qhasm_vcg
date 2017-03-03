From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul121666 : program :=

let         wsize :=   64%nat in

let crypto_sign_ed25519_amd64_51_121666_213 :=
                       996687872%Z in (* from consts *)
let crypto_sign_ed25519_amd64_51_REDMASK51_width :=
                       51 in        (* 51 bits *)

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
zAssign rax (zVar x0);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
zSplit rdx rax (zBinop zMul (zVar rax) (zConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
zSplit rax tmp (zVar rax) 13;
      (*   r0 = rax *)
zAssign r0 (zVar rax);
      (*   r1 = rdx *)
zAssign r1 (zVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 8) *)
zAssign rax (zVar x1);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
zSplit rdx rax (zBinop zMul (zVar rax) (zConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
zSplit rax tmp (zVar rax) 13;
      (*   r1 += rax *)
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
      (*   r2 = rdx *)
zAssign r2 (zVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
zAssign rax (zVar x2);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
zSplit rdx rax (zBinop zMul (zVar rax) (zConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
zSplit rax tmp (zVar rax) 13;
      (*   r2 += rax *)
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
      (*   r3 = rdx *)
zAssign r3 (zVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
zAssign rax (zVar x3);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
zSplit rdx rax (zBinop zMul (zVar rax) (zConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
zSplit rax tmp (zVar rax) 13;
      (*   r3 += rax *)
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
      (*   r4 = rdx *)
zAssign r4 (zVar rdx);
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
zAssign rax (zVar x4);
      (*   (uint128) rdx rax = rax * *[uint64 *] &crypto_sign_ed25519_amd64_51_121666_213 *)
zSplit rdx rax (zBinop zMul (zVar rax) (zConst crypto_sign_ed25519_amd64_51_121666_213)) wsize;
      (*   (uint64) rax >>= 13 *)
zSplit rax tmp (zVar rax) 13;
      (*   r4 += rax *)
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
      (*   rdx *= 19 *)
zAssign rdx (zBinop zMul (zVar rdx) (zConst 19%Z));
      (*   r0 += rdx *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar rdx));
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
zAssign z0 (zVar r0);
      (* *[uint64 *](rp + 8) = r1 *)
zAssign z1 (zVar r1);
      (* *[uint64 *](rp + 16) = r2 *)
zAssign z2 (zVar r2);
      (* *[uint64 *](rp + 24) = r3 *)
zAssign z3 (zVar r3);
      (* *[uint64 *](rp + 32) = r4 *)
zAssign z4 (zVar r4)
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

Definition fe25519_mul121666_pre : bexp := zTrue.

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
zEqMod
  (
    (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
    @*
    (zConst 121666)
  )
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (n25519).

Definition fe25519_mul121666_spec :=
  {| spre := fe25519_mul121666_pre;
     sprog := fe25519_mul121666;
     spost := fe25519_mul121666_post |}.

From mathcomp Require Import ssreflect eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul121666 : valid_ispec (fe25519_mul121666_inputs, fe25519_mul121666_spec).
Proof.
  Time verify_ispec.
  (* *)
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
