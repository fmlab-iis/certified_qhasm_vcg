From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Definition fe25519_sq : program :=
  
let         wsize :=   64%positive in
let          qtwo :=   QConst (2%Z) in

let concat_shift hi lo w :=       (* (hi.lo) << w *)
      QBinop QMul (QBinop QAdd (QBinop QMul hi (QPow qtwo wsize)) lo)
                  (QPow qtwo w) in

let crypto_sign_ed25519_amd64_51_REDMASK51 :=
                       2251799813685247%Z in (* 0x7FFFFFFFFFFFF from consts *)
let crypto_sign_ed25519_amd64_51_REDMASK51_width :=
                       51%positive in        (* 51 bits *)

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
      (* ################################################################### *)
      (* # Conditions on the inputs: x0 = *[uint64 *](xp +  0), *)
      (* #                           x1 = *[uint64 *](xp +  8), *)
      (* #                           x2 = *[uint64 *](xp + 16), *)
      (* #                           x3 = *[uint64 *](xp + 24), *)
      (* #                           x4 = *[uint64 *](xp + 32), are all in [0,2^54-1] *)
      (* # *)
      (* ################################################################### *)
      (*  *)
      (*   #// var x0 = mem64[xp + 0]@u520 *)
      (*   #//     x1 = mem64[xp + 8]@u520 *)
      (*   #//     x2 = mem64[xp + 16]@u520 *)
      (*   #//     x3 = mem64[xp + 24]@u520 *)
      (*   #//     x4 = mem64[xp + 32]@u520 *)
      (*  *)
      (*   #// assume 0 <=u x0, x1, x2, x3, x4 <u 2**54 *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x0);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 0) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x0)) wsize;
      (*   r0 = rax *)
QAssign r0 (QVar rax);
      (*   r01 = rdx *)
QAssign r01 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x0);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x1)) wsize;
      (*   r1 = rax *)
QAssign r1 (QVar rax);
      (*   r11 = rdx *)
QAssign r11 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x0);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
      (*   r2 = rax *)
QAssign r2 (QVar rax);
      (*   r21 = rdx *)
QAssign r21 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x0);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
      (*   r3 = rax *)
QAssign r3 (QVar rax);
      (*   r31 = rdx *)
QAssign r31 (QVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
QAssign rax (QVar x1);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
      (*   r4 = rax *)
QAssign r4 (QVar rax);
      (*   r41 = rdx *)
QAssign r41 (QVar rdx);
      (*  *)
      (*   rax = *[uint64 *](xp + 8) *)
QAssign rax (QVar x1);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x1)) wsize;
      (*   carry? r2 += rax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
QSplit carry r2 (QVar r2) wsize;
      (*   r21 += rdx + carry *)
QAssign r21 (QBinop QAdd (QVar r21) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
QAssign rax (QVar x1);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
      (*   carry? r3 += rax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
QSplit carry r3 (QVar r3) wsize;
      (*   r31 += rdx + carry *)
QAssign r31 (QBinop QAdd (QVar r31) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
QAssign rax (QVar x1);
      (*   rax <<= 1 *)
QAssign rax (QBinop QMul (QVar rax) qtwo);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
      (*   carry? r4 += rax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
QSplit carry r4 (QVar r4) wsize;
      (*   r41 += rdx + carry *)
QAssign r41 (QBinop QAdd (QVar r41) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
QAssign rax (QVar x1);
      (*   rax *= 38 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
      (*   carry? r0 += rax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar rax));
QSplit carry r0 (QVar r0) wsize;
      (*   r01 += rdx + carry *)
QAssign r01 (QBinop QAdd (QVar r01) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
QAssign rax (QVar x2);
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x2)) wsize;
      (*   carry? r4 += rax *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar rax));
QSplit carry r4 (QVar r4) wsize;
      (*   r41 += rdx + carry *)
QAssign r41 (QBinop QAdd (QVar r41) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
QAssign rax (QVar x2);
      (*   rax *= 38 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
      (*   carry? r0 += rax *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar rax));
QSplit carry r0 (QVar r0) wsize;
      (*   r01 += rdx + carry *)
QAssign r01 (QBinop QAdd (QVar r01) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
QAssign rax (QVar x2);
      (*   rax *= 38 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
      (*   carry? r1 += rax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
QSplit carry r1 (QVar r1) wsize;
      (*   r11 += rdx + carry *)
QAssign r11 (QBinop QAdd (QVar r11) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
QAssign rax (QVar x3);
      (*   rax *= 19 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 19%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x3)) wsize;
      (*   carry? r1 += rax *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar rax));
QSplit carry r1 (QVar r1) wsize;
      (*   r11 += rdx + carry *)
QAssign r11 (QBinop QAdd (QVar r11) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*   rax = *[uint64 *](xp + 24) *)
QAssign rax (QVar x3);
      (*   rax *= 38 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 38%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
      (*   carry? r2 += rax *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar rax));
QSplit carry r2 (QVar r2) wsize;
      (*   r21 += rdx + carry *)
QAssign r21 (QBinop QAdd (QVar r21) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
QAssign rax (QVar x4);
      (*   rax *= 19 *)
QAssign rax (QBinop QMul (QVar rax) (QConst 19%Z));
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
QSplit rdx rax (QBinop QMul (QVar rax) (QVar x4)) wsize;
      (*   carry? r3 += rax *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar rax));
QSplit carry r3 (QVar r3) wsize;
      (*   r31 += rdx + carry *)
QAssign r31 (QBinop QAdd (QVar r31) (QBinop QAdd (QVar rdx) (QVar carry)));
      (*  *)
      (*   #     lhs_520 = (x0 + x1 * 2**51 + x2 * 2**102 + x3 * 2**153 + x4 * 2**204) * (x0 + x1 * 2**51 + x2 * 2**102 + x3 * 2**153 + x4 * 2**204) *)
      (*  *)
      (*   #// var r0_520 = (r01@u128.r0@u128)@u520 *)
      (*   #//     r1_520 = (r11@u128.r1@u128)@u520 *)
      (*   #//     r2_520 = (r21@u128.r2@u128)@u520 *)
      (*   #//     r3_520 = (r31@u128.r3@u128)@u520 *)
      (*   #//     r4_520 = (r41@u128.r4@u128)@u520 *)
      (*   #//     lhs_520 = x0 * x0 + (2 * x0 * x1) * 2**51 + (2 * x0 * x2 + x1 * x1) * 2**102 + (2 * x0 * x3 + 2 * x1 * x2) * 2**153 + *)
      (*   #//               (2 * x0 * x4 + 2 * x1 * x3 + x2 * x2) * 2**204 + (2 * x1 * x4 + 2 * x2 * x3) * 2**255 + (2 * x2 * x4 + x3 * x3) * 2**306 + *)
      (*   #//               (2 * x3 * x4) * 2**357 + (x4 * x4) * 2**408 *)
      (*   #//     rhs_520 = r0_520 + r1_520 * 2**51 + r2_520 * 2**102 + r3_520 * 2**153 + r4_520 * 2**204 *)
      (*   #// assert lhs_520 >=u rhs_520 && (lhs_520 - rhs_520) %u (2**255 - 19) = 0 *)
      (*   #// cut 0 <=u r01.r0 <u 2**54 * 2**54 + 19 * 2**54 * 2**54 * 4 && *)
      (*   #//     0 <=u r11.r1 <u 2**54 * 2**54 * 2 + 19 * 2**54 * 2**54 * 3 && *)
      (*   #//     0 <=u r21.r2 <u 2**54 * 2**54 * 3 + 19 * 2**54 * 2**54 * 2 && *)
      (*   #//     0 <=u r31.r3 <u 2**54 * 2**54 * 4 + 19 * 2**54 * 2**54 * 1 && *)
      (*   #//     0 <=u r41.r4 <u 2**54 * 2**54 * 5 *)
      (*  *)
      (* ################################################################### *)
      (* # The following should hold at this point: *)
      (* # *)
      (* # (x0 + 2^51*x1 + 2^102*x2 + 2^153*x3 + 2^204*x4) * (x0 + 2^51*x1 + 2^102*x2 + 2^153*x3 + 2^204*x4) congruent to (r0h.r0l) + (r1h.r1l)*2^51 + (r2h.r2l)*2^102 + (r3h.r3l)*2^153 + (r4h.r4l)*2^204  [modulo 2^255-19] *)
      (* #  *)
      (* # Notation: (X.Y) stands for a 128-bit value with the least significant 64 bits in Y and the 64 most significant bits in X *)
      (* # *)
      (* ################################################################### *)
      (*  *)
      (*   #// var r0_512 = (r01@u128.r0@u128)@u512 *)
      (*   #//     r1_512 = (r11@u128.r1@u128)@u512 *)
      (*   #//     r2_512 = (r21@u128.r2@u128)@u512 *)
      (*   #//     r3_512 = (r31@u128.r3@u128)@u512 *)
      (*   #//     r4_512 = (r41@u128.r4@u128)@u512 *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
QAssign redmask (QConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*    *)
      (*   r01 = (r01.r0) << 13 *)
QAssign tmp (concat_shift (QVar r01) (QVar r0) (13%positive));
QSplit r01 tmp (QVar tmp) wsize;
QSplit tmp r01 (QVar r01) wsize;
      (*   r0 &= redmask *)
QSplit tmp r0 (QVar r0) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*    *)
      (*   r11 = (r11.r1) << 13 *)
QAssign tmp (concat_shift (QVar r11) (QVar r1) (13%positive));
QSplit r11 tmp (QVar tmp) wsize;
QSplit tmp r11 (QVar r11) wsize;
      (*   r1 &= redmask *)
QSplit tmp r1 (QVar r1) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1 += r01 *)
QAssign r1 (QBinop QAdd (QVar r1) (QVar r01));
      (*    *)
      (*   r21 = (r21.r2) << 13 *)
QAssign tmp (concat_shift (QVar r21) (QVar r2) (13%positive));
QSplit r21 tmp (QVar tmp) wsize;
QSplit tmp r21 (QVar r21) wsize;
      (*   r2 &= redmask *)
QSplit tmp r2 (QVar r2) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2 += r11 *)
QAssign r2 (QBinop QAdd (QVar r2) (QVar r11));
      (*    *)
      (*   r31 = (r31.r3) << 13 *)
QAssign tmp (concat_shift (QVar r31) (QVar r3) (13%positive));
QSplit r31 tmp (QVar tmp) wsize;
QSplit tmp r31 (QVar r31) wsize;
       (*   r3 &= redmask *)
QSplit tmp r3 (QVar r3) wsize;
      (*   r3 += r21 *)
QAssign r3 (QBinop QAdd (QVar r3) (QVar r21));
      (*    *)
      (*   r41 = (r41.r4) << 13 *)
QAssign tmp (concat_shift (QVar r41) (QVar r4) (13%positive));
QSplit r41 tmp (QVar tmp) wsize;
QSplit tmp r41 (QVar r41) wsize;
      (*   r4 &= redmask *)
QSplit tmp r4 (QVar r4) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4 += r31 *)
QAssign r4 (QBinop QAdd (QVar r4) (QVar r31));
      (*   r41 = r41 * 19 *)
QAssign r41 (QBinop QMul (QVar r41) (QConst 19%Z));
      (*   r0 += r41 *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar r41));
      (*  *)
      (*   #// var lhs = r0_512 + r1_512 * 2**51 + r2_512 * 2**102 + r3_512 * 2**153 + r4_512 * 2**204 *)
      (*   #//     rhs = r0@u512 + r1@u512 * 2**51 + r2@u512 * 2**102 + r3@u512 * 2**153 + r4@u512 * 2**204 *)
      (*   #// assert lhs >=u rhs && (lhs - rhs) %u (2**255 - 19) = 0 *)
      (*   #// cut 0 <=u r0 <u 2**64 - 2**63 + 2**62 && *)
      (*   #//     0 <=u r1 <u 2**64 - 2**63 + 2**61 && *)
      (*   #//     0 <=u r2 <u 2**63 - 2**60 + 2**59 && *)
      (*   #//     0 <=u r3 <u 2**62 + 2**61 - 2**59 && *)
      (*   #//     0 <=u r4 <u 2**61 + 2**60 - 2**56 && *)
      (*   #//     redmask = mem64[crypto_sign_ed25519_amd64_51_REDMASK51] *)
      (*  *)
      (*   #// var r0_512 = r0@u512 *)
      (*   #//     r1_512 = r1@u512 *)
      (*   #//     r2_512 = r2@u512 *)
      (*   #//     r3_512 = r3@u512 *)
      (*   #//     r4_512 = r4@u512 *)
      (*  *)
      (*   t = r0 *)
QAssign t (QVar r0);
      (*   (uint64) t >>= 51 *)
QSplit t tmp (QVar t) (51%positive);
      (*   t += r1 *)
QAssign t (QBinop QAdd (QVar t) (QVar r1));
      (*   r0 &= redmask *)
QSplit tmp r0 (QVar r0) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*    *)
      (*   r1 = t *)
QAssign r1 (QVar t);
      (*   (uint64) t >>= 51 *)
QSplit t tmp (QVar t) (51%positive);
      (*   t += r2 *)
QAssign t (QBinop QAdd (QVar t) (QVar r2));
      (*   r1 &= redmask *)
QSplit tmp r1 (QVar r1) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*    *)
      (*   r2 = t *)
QAssign r2 (QVar t);
      (*   (uint64) t >>= 51 *)
QSplit t tmp (QVar t) (51%positive);
      (*   t += r3 *)
QAssign t (QBinop QAdd (QVar t) (QVar r3));
      (*   r2 &= redmask *)
QSplit tmp r2 (QVar r2) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*    *)
      (*   r3 = t *)
QAssign r3 (QVar t);
      (*   (uint64) t >>= 51 *)
QSplit t tmp (QVar t) (51%positive);
      (*   t += r4 *)
QAssign t (QBinop QAdd (QVar t) (QVar r4));
      (*   r3 &= redmask *)
QSplit tmp r3 (QVar r3) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*    *)
      (*   r4 = t *)
QAssign r4 (QVar t);
      (*   (uint64) t >>= 51 *)
QSplit t tmp (QVar t) (51%positive);
      (*   t *= 19 *)
QAssign t (QBinop QMul (QVar t) (QConst 19%Z));
      (*   r0 += t *)
QAssign r0 (QBinop QAdd (QVar r0) (QVar t));
      (*   r4 &= redmask *)
QSplit tmp r4 (QVar r4) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   #END MACRO  *)
      (*  *)
      (*   #// var lhs = r0_512 + r1_512 * 2**51 + r2_512 * 2**102 + r3_512 * 2**153 + r4_512 * 2**204 *)
      (*   #//     rhs = r0@u512 + r1@u512 * 2**51 + r2@u512 * 2**102 + r3@u512 * 2**153 + r4@u512 * 2**204 *)
      (*   #// assert lhs >=u rhs && (lhs - rhs) %u (2**255 - 19) = 0 && *)
      (*   #//        0 <=u r0 <u 2**51 + 2**15 && *)
      (*   #//        0 <=u r1 <u 2**51 && *)
      (*   #//        0 <=u r2 <u 2**51 && *)
      (*   #//        0 <=u r3 <u 2**51 && *)
      (*   #//        0 <=u r4 <u 2**51 *)
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
      (* ################################################################### *)
      (* # The following should hold at this point: *)
      (* # *)
      (* # (x0 + 2^51*x1 + 2^102*x2 + 2^153*x3 + 2^204*x4) * (x0 + 2^51*x1 + 2^102*x2 + 2^153*x3 + 2^204*x4) congruent to (r0l + r1l*2^51 + r2l*2^102 + r3l*2^153 + r4l*2^204)  [modulo 2^255-19] *)
      (* # *)
      (* # r0l,r1l,r2l,r3l,r4l are all in [0,2^51+2^15] *)
      (* # *)
      (* ################################################################### *)
      (*    *)
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

