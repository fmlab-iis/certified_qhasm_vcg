From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

(* This is an alternative implementation of fe25519_mul121666. *)

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition fe25519_mul121666 : program :=

let          qtwo :=   QConst 2%Z in
let         wsize :=   64%positive in

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

let           rax :=  20 in
let           rdx :=  21 in

[::
QAssign rax (QVar x0);
QSplit rdx rax (QBinop QMul (QVar rax) (QConst 121666)) 51;
QAssign r0 (QVar rax);
QAssign r1 (QVar rdx);
      (*    *)
QAssign rax (QVar x1);
QSplit rdx rax (QBinop QMul (QVar rax) (QConst 121666)) 51;
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
QAssign r2 (QVar rdx);
      (*    *)
QAssign rax (QVar x2);
QSplit rdx rax (QBinop QMul (QVar rax) (QConst 121666)) 51;
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
QAssign r3 (QVar rdx);
      (*    *)
QAssign rax (QVar x3);
QSplit rdx rax (QBinop QMul (QVar rax) (QConst 121666)) 51;
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
QAssign r4 (QVar rdx);
      (*    *)
QAssign rax (QVar x4);
QSplit rdx rax (QBinop QMul (QVar rax) (QConst 121666)) 51;
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
QAssign rdx (QBinop QMul (QVar rdx) (QConst 19));
QAssign r0 (QBinop QAdd (QVar r0) (QVar rdx))
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
    (Radix51.limbs [::QVar x0; QVar x1; QVar x2; QVar x3; QVar x4])
    @*
    (QConst 121666)
  )
  (Radix51.limbs [::QVar r0; QVar r1; QVar r2; QVar r3; QVar r4])
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
  (* 35.703s *)
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
