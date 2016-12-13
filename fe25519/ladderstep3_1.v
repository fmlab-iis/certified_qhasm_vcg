From Coq Require Import ZArith .
From mQhasm Require Import mQhasm Radix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope mqhasm_scope.

Definition bi : Set := N * N * N * N * N.

Definition bi_list (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  [:: x0; x1; x2; x3; x4].

Definition bi_limbs (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  radix51 [:: QVar x0; QVar x1; QVar x2; QVar x3; QVar x4].

Definition fe25519_add (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
[::
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
] .

Definition fe25519_sub (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
let crypto_sign_ed25519_amd64_51_2P0 :=
                       4503599627370458%Z in (* 0xFFFFFFFFFFFDA from consts *)
let crypto_sign_ed25519_amd64_51_2P1234 :=
                       4503599627370494%Z in (* 0xFFFFFFFFFFFFE from consts *)
[::
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
] .

Definition fe25519_mul121666 (X R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(r0, r1, r2, r3, r4) := R in
let          qtwo :=   QConst 2%Z in
let         wsize :=   64%positive in
let           rax :=  1000 in
let           rdx :=  1001 in

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

Definition fe25519_mul (X Y Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(z0, z1, z2, z3, z4) := Z in

let          qtwo :=   QConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := QBinop QMul x (QPow qtwo n) in

let         carry := 9999 in
let           tmp := 9998 in
let          tmp2 := 9997 in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c0 :=  1010 in
let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in

let        mulr01 :=  1020 in
let        mulr11 :=  1021 in
let        mulr21 :=  1022 in
let        mulr31 :=  1023 in
let        mulr41 :=  1024 in

let        mulrax :=  1030 in
let        mulrdx :=  1031 in
let          mult :=  1032 in
let    mulredmask :=  1033 in
let       mulx219 :=  1034 in
let       mulx319 :=  1035 in
let       mulx419 :=  1036 in
[::
      (*  *)
      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   mulrax *= 19 *)
      (*   mulx319_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r0 = mulrax *)
      (*   mulr01 = mulrdx *)
QAssign mulrax (QVar x3);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QAssign mulx319 (QVar mulrax);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r0 (QVar mulrax);
QAssign mulr01 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x4);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QAssign mulx419 (QVar mulrax);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r1 (QVar mulrax);
QAssign mulr11 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r2 (QVar mulrax);
QAssign mulr21 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r3 (QVar mulrax);
QAssign mulr31 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
QAssign mulrax (QVar x0);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r4 (QVar mulrax);
QAssign mulr41 (QVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x1);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulrax));
QSplit carry r0 (QVar r0) wsize;
QAssign mulr01 (QBinop QAdd (QVar mulr01) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar x2);
QAssign mulrax (QBinop QMul (QVar mulrax) (QConst 19%Z));
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x3);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar mulx319);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar mulx319);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
QAssign mulrax (QVar x4);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulrax));
QSplit carry r4 (QVar r4) wsize;
QAssign mulr41 (QBinop QAdd (QVar mulr41) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulrax));
QSplit carry r1 (QVar r1) wsize;
QAssign mulr11 (QBinop QAdd (QVar mulr11) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulrax));
QSplit carry r2 (QVar r2) wsize;
QAssign mulr21 (QBinop QAdd (QVar mulr21) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
QAssign mulrax (QVar mulx419);
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulrax));
QSplit carry r3 (QVar r3) wsize;
QAssign mulr31 (QBinop QAdd (QVar mulr31) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mulredmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
QSplit tmp r0 (QVar r0) 51%positive;
QAssign mulr01 (QBinop QAdd (pow2 (QVar mulr01) 13%positive) (QVar tmp));
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
QSplit tmp r1 (QVar r1) 51%positive;
QAssign mulr11 (QBinop QAdd (pow2 (QVar mulr11) 13%positive) (QVar tmp));
QAssign r1 (QBinop QAdd (QVar r1) (QVar mulr01));
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
QSplit tmp r2 (QVar r2) 51%positive;
QAssign mulr21 (QBinop QAdd (pow2 (QVar mulr21) 13%positive) (QVar tmp));
QAssign r2 (QBinop QAdd (QVar r2) (QVar mulr11));
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
QSplit tmp r3 (QVar r3) 51%positive;
QAssign mulr31 (QBinop QAdd (pow2 (QVar mulr31) 13%positive) (QVar tmp));
QAssign r3 (QBinop QAdd (QVar r3) (QVar mulr21));
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
QSplit tmp r4 (QVar r4) 51%positive;
QAssign mulr41 (QBinop QAdd (pow2 (QVar mulr41) 13%positive) (QVar tmp));
QAssign r4 (QBinop QAdd (QVar r4) (QVar mulr31));
      (*   mulr41 = mulr41 * 19 *)
QAssign mulr41 (QBinop QMul (QVar mulr41) (QConst 19%Z));
      (*   r0 += mulr41 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar mulr41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mult = r0 *)
      (*   (uint64) mult >>= 51 *)
      (*   mult += r1 *)
QAssign mult (QVar r0);
QSplit mult tmp (QVar mult) (51%positive);
QAssign mult (QBinop QAdd (QVar mult) (QVar r1));
      (*   r1 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r0 &= mulredmask *)
      (*   mult += r2 *)
QAssign r1 (QVar mult);
QSplit mult tmp2 (QVar mult) (51%positive);
QAssign r0 (QVar tmp);
QAssign mult (QBinop QAdd (QVar mult) (QVar r2));
      (*   r2 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r1 &= mulredmask *)
      (*   mult += r3 *)
QAssign r2 (QVar mult);
QSplit mult tmp (QVar mult) (51%positive);
QAssign r1 (QVar tmp2);
QAssign mult (QBinop QAdd (QVar mult) (QVar r3));
      (*   r3 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r2 &= mulredmask *)
      (*   mult += r4 *)
QAssign r3 (QVar mult);
QSplit mult tmp2 (QVar mult) (51%positive);
QAssign r2 (QVar tmp);
QAssign mult (QBinop QAdd (QVar mult) (QVar r4));
      (*   r4 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r3 &= mulredmask *)
QAssign r4 (QVar mult);
QSplit mult tmp (QVar mult) (51%positive);
QAssign r3 (QVar tmp2);
      (*   mult *= 19 *)
      (*   r0 += mult *)
      (*   r4 &= mulredmask *)
QAssign mult (QBinop QMul (QVar mult) (QConst 19%Z));
QAssign r0 (QBinop QAdd (QVar r0) (QVar mult));
QAssign r4 (QVar tmp);
      (*   #END MACRO mul *)

      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
      (* *[uint64 *](rp + 8) = r1 *)
      (* *[uint64 *](rp + 16) = r2 *)
      (* *[uint64 *](rp + 24) = r3 *)
      (* *[uint64 *](rp + 32) = r4 *)
QAssign z0 (QVar r0);
QAssign z1 (QVar r1);
QAssign z2 (QVar r2);
QAssign z3 (QVar r3);
QAssign z4 (QVar r4)
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

Definition fe25519_sq (X Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(z0, z1, z2, z3, z4) := Z in

let         wsize :=   64%positive in
let          qtwo :=   QConst (2%Z) in
let      pow2 x n := QBinop QMul x (QPow qtwo n) in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in
let            c5 :=  1015 in
let            c6 :=  1016 in
let            c7 :=  1017 in

let          x119 :=  1021 in
let          x219 :=  1022 in
let          x319 :=  1023 in
let          x419 :=  1024 in

let           r01 :=  1030 in
let           r11 :=  1031 in
let           r21 :=  1032 in
let           r31 :=  1033 in
let           r41 :=  1034 in
let           rax :=  1035 in
let           rdx :=  1036 in

let             t :=  1040 in
let       redmask :=  1041 in

let           tmp := 9998 in
let         carry := 9999 in

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

Definition fe25519_ladderstep : program :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
fe25519_add X2 Z2 T1 ++
fe25519_sub X2 Z2 T2 ++
fe25519_sq T2 T7 ++
fe25519_sq T1 T6 ++
fe25519_sub T6 T7 T5 ++
fe25519_add X3 Z3 T3 ++
fe25519_sub X3 Z3 T4 ++
fe25519_mul T3 T2 T9 ++
fe25519_mul T4 T1 T8 ++
fe25519_add T8 T9 X3_1 ++
fe25519_sub T8 T9 Z3_1 ++
fe25519_sq X3_1 X3' ++
fe25519_sq Z3_1 Z3_2 ++
fe25519_mul Z3_2 X1 Z3' ++
fe25519_mul T6 T7 X2' ++
fe25519_mul121666 T5 Z2_1 ++
fe25519_add Z2_1 T7 Z2_2 ++
fe25519_mul Z2_2 T5 Z2'.

Definition fe25519_ladderstep_inputs : VS.t :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
VSLemmas.OP.P.of_list (bi_list X1 ++ bi_list X2 ++ bi_list Z2 ++
                               bi_list X3 ++ bi_list Z3).

Definition fe25519_ladderstep_pre : bexp := QTrue.

Definition fe25519_ladderstep_post1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (bi_limbs X2')
  (QPow (qsub (QPow (bi_limbs X2) 2) (QPow (bi_limbs Z2) 2)) 2)
  n25519.

Definition fe25519_ladderstep_post2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (bi_limbs Z2')
  (qmuls [:: QConst 4;
            bi_limbs X2;
            bi_limbs Z2;
            qadds [:: QPow (bi_limbs X2) 2;
                     qmuls [:: QConst 486662; bi_limbs X2; bi_limbs Z2];
                     QPow (bi_limbs Z2) 2]
         ])
  n25519.

Definition fe25519_ladderstep_post3 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (qmul (bi_limbs X3')
        (qmul (bi_limbs X1)
              (QPow (qsub (qmul (bi_limbs X3) (bi_limbs Z2))
                          (qmul (bi_limbs X2) (bi_limbs Z3))) 2)))
  (qmul (bi_limbs Z3')
        (QPow (qsub (qmul (bi_limbs X2) (bi_limbs X3))
                    (qmul (bi_limbs Z2) (bi_limbs Z3))) 2))
  n25519.

Definition fe25519_ladderstep_post3_1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (bi_limbs X3')
  (qmul (QConst 4)
        (QPow (qsub (qmul (bi_limbs X2) (bi_limbs X3))
                    (qmul (bi_limbs Z2) (bi_limbs Z3))) 2))
  n25519.

Definition fe25519_ladderstep_post3_2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
QEqMod
  (bi_limbs Z3')
  (qmul (QConst 4)
        (qmul (bi_limbs X1)
              (QPow (qsub (qmul (bi_limbs X3) (bi_limbs Z2))
                          (qmul (bi_limbs X2) (bi_limbs Z3))) 2)))
  n25519.

Definition fe25519_ladderstep_post : bexp :=
  qands [:: fe25519_ladderstep_post1;
            fe25519_ladderstep_post2;
            fe25519_ladderstep_post3 ].

Definition fe25519_ladderstep_spec :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post |}.

Definition fe25519_ladderstep_spec1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post1 |}.

Definition fe25519_ladderstep_spec2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post2 |}.

Definition fe25519_ladderstep_spec3 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3 |}.

Definition fe25519_ladderstep_spec3_1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_1 |}.

Definition fe25519_ladderstep_spec3_2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_2 |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_ladderstep3_1 : valid_ispec (fe25519_ladderstep_inputs, fe25519_ladderstep_spec3_1).
Proof.
  time "valid_fe25519_ladderstep3_1" verify_ispec.
Qed.

Close Scope mqhasm_scope.
Close Scope N_scope.
