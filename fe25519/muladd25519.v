From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Definition muladd25519 : program :=

let          qtwo :=   QConst 2%Z in
let         wsize :=   64%positive in

let concat_shift hi lo w :=       (* (hi.lo) << w *)
      QBinop QMul (QBinop QAdd (QBinop QMul hi (QPow qtwo wsize)) lo)
                  (QPow qtwo w) in

let crypto_sign_ed25519_amd64_51_REDMASK51 :=
                       2251799813685247%Z in (* 0x7FFFFFFFFFFFF from consts *)
let crypto_sign_ed25519_amd64_51_REDMASK51_width :=
                       51%positive in        (* 51 bits *)

let            x0 :=   0 in     (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in     (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in     (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in     (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in     (* *[uint64 *](xp + 32) *)

let            y0 :=   5 in     (* *[uint64 *](yp +  0) *)
let            y1 :=   6 in     (* *[uint64 *](yp +  8) *)
let            y2 :=   7 in     (* *[uint64 *](yp + 16) *)
let            y3 :=   8 in     (* *[uint64 *](yp + 24) *)
let            y4 :=   9 in     (* *[uint64 *](yp + 32) *)

let            r0 :=  10 in     (* *[uint64 *](rp +  0) *)
let            r1 :=  11 in     (* *[uint64 *](rp +  8) *)
let            r2 :=  12 in     (* *[uint64 *](rp + 16) *)
let            r3 :=  13 in     (* *[uint64 *](rp + 24) *)
let            r4 :=  14 in     (* *[uint64 *](rp + 32) *)

let           r0l :=  20 in
let           r0h :=  21 in
let           r1l :=  22 in
let           r1h :=  23 in
let           r2l :=  24 in
let           r2h :=  25 in
let           r3l :=  26 in
let           r3h :=  27 in
let           r4l :=  28 in
let           r4h :=  29 in
let           r5l :=  30 in
let           r5h :=  31 in
let           r6l :=  32 in
let           r6h :=  33 in
let           r7l :=  34 in
let           r7h :=  35 in
let           r8l :=  36 in
let           r8h :=  37 in

let            c1 :=  41 in
let            c2 :=  42 in
let            c3 :=  43 in
let            c4 :=  44 in
let            c5 :=  45 in
let            c6 :=  46 in
let            c7 :=  47 in

let        mulrax :=  50 in
let        mulrdx :=  51 in
let       redmask :=  52 in
let      nineteen :=  53 in

let           tmp := 998 in
let         carry := 999 in

[::
      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): 15423m2.999s *)
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (* int64 yp *)
      (*  *)
      (* input rp *)
      (* input xp *)
      (* input yp *)
      (*  *)
      (* int64 r0l *)
      (* int64 r0h *)
      (* int64 r1l *)
      (* int64 r1h *)
      (* int64 r2l *)
      (* int64 r2h *)
      (* int64 r3l *)
      (* int64 r3h *)
      (* int64 r4l *)
      (* int64 r4h *)
      (* int64 r5l *)
      (* int64 r5h *)
      (* int64 r6l *)
      (* int64 r6h *)
      (* int64 r7l *)
      (* int64 r7h *)
      (* int64 r8l *)
      (* int64 r8h *)

      (*  *)

      (* stack64 r0l_stack *)
      (* stack64 r0h_stack *)
      (* stack64 r1l_stack *)
      (* stack64 r1h_stack *)
      (* stack64 r2l_stack *)
      (* stack64 r2h_stack *)
      (* stack64 r3l_stack *)
      (* stack64 r3h_stack *)
      (* stack64 r4l_stack *)
      (* stack64 r4h_stack *)
      (* stack64 r5l_stack *)
      (* stack64 r5h_stack *)
      (* stack64 r6l_stack *)
      (* stack64 r6h_stack *)
      (* stack64 r7l_stack *)
      (* stack64 r7h_stack *)
      (* stack64 r8l_stack *)
      (* stack64 r8h_stack *)
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
      (*  *)
      (* int64 mulrax *)
      (* int64 mulrdx *)
      (* int64 redmask *)
      (* int64 nineteen *)
      (*  *)
      (* enter muladd25519 *)
      (*  *)
      (* c1_stack = c1 *)
      (* c2_stack = c2 *)
      (* c3_stack = c3 *)
      (* c4_stack = c4 *)
      (* c5_stack = c5 *)
      (* c6_stack = c6 *)
      (* c7_stack = c7 *)
      (* yp = yp *)
      (* nineteen=19 *)
QAssign nineteen (QConst 19%Z);
      (*  *)
      (* ################################################################### *)
      (* # Conditions on the inputs: x0 = *[uint64 *](xp +  0), *)
      (* #                           x1 = *[uint64 *](xp +  8), *)
      (* #                           x2 = *[uint64 *](xp + 16), *)
      (* #                           x3 = *[uint64 *](xp + 24), *)
      (* #                           x4 = *[uint64 *](xp + 32), *)
      (* #                           y0 = *[uint64 *](yp +  0), *)
      (* #                           y1 = *[uint64 *](yp +  8), *)
      (* #                           y2 = *[uint64 *](yp + 16)   *)
      (* #                           y3 = *[uint64 *](yp + 24)   *)
      (* #                           y4 = *[uint64 *](yp + 32)  are all in [0,2^52] *)
      (* # *)
      (* ################################################################### *)
      (*  *)
      (* #// var x0 = mem64[xp +  0]@u128 *)
      (* #//     x1 = mem64[xp +  8]@u128 *)
      (* #//     x2 = mem64[xp +  16]@u128 *)
      (* #//     x3 = mem64[xp +  24]@u128 *)
      (* #//     x4 = mem64[xp +  32]@u128 *)
      (* #//     y0 = mem64[yp +  0]@u128 *)
      (* #//     y1 = mem64[yp +  8]@u128 *)
      (* #//     y2 = mem64[yp +  16]@u128 *)
      (* #//     y3 = mem64[yp +  24]@u128 *)
      (* #//     y4 = mem64[yp +  32]@u128 *)
      (* #//     r0 = mem64[rp +  0]@u128 *)
      (* #//     r1 = mem64[rp +  8]@u128 *)
      (* #//     r2 = mem64[rp +  16]@u128 *)
      (* #//     r3 = mem64[rp +  24]@u128 *)
      (* #//     r4 = mem64[rp +  32]@u128 *)
      (*  *)
      (* #// assume 0 <=u x0, x1, x2, x3, x4 <=u 2**52 && *)
      (* #//        0 <=u y0, y1, y2, y3, y4 <=u 2**52 && *)
      (* #//        0 <=u r0, r1, r2, r3, r4 <=u 2**52 *)
      (*  *)
      (* # Compute r0 += (r0h.r0l) = x0*y0 *)
      (*   r0l = *[uint64 *](rp + 0) *)
QAssign r0l (QVar r0);
      (*   r0h = 0 *)
QAssign r0h (QConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r0l += mulrax *)
QAssign r0l (QBinop QAdd (QVar r0l) (QVar mulrax));
QSplit carry r0l (QVar r0l) wsize;
      (*   r0h += mulrdx + carry *)
QAssign r0h (QBinop QAdd (QVar r0h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r0l_stack = r0l *)
      (*   r0h_stack = r0h *)
      (*  *)
      (* # Compute r1 += (r1h.r1l) = x1*y0 + x0*y1 *)
      (*   r1l = *[uint64 *](rp + 8) *)
QAssign r1l (QVar r1);
      (*   r1h = 0 *)
QAssign r1h (QConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r1l += mulrax *)
QAssign r1l (QBinop QAdd (QVar r1l) (QVar mulrax));
QSplit carry r1l (QVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
QAssign r1h (QBinop QAdd (QVar r1h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r1l += mulrax *)
QAssign r1l (QBinop QAdd (QVar r1l) (QVar mulrax));
QSplit carry r1l (QVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
QAssign r1h (QBinop QAdd (QVar r1h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r1l_stack = r1l *)
      (*   r1h_stack = r1h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r2 += (r2h.r2l) = x2*y0 + + x1*y1 + x0*y2 *)
      (*   r2l = *[uint64 *](rp + 16) *)
QAssign r2l (QVar r2);
      (*   r2h = 0 *)
QAssign r2h (QConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r2l += mulrax *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r2l += mulrax *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r2l += mulrax *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r2l_stack = r2l *)
      (*   r2h_stack = r2h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r3 += (r3h.r3l) = x3*y0 + x2*y1 + x1*y2 + x0*y3 *)
      (*   r3l = *[uint64 *](rp + 24) *)
QAssign r3l (QVar r3);
      (*   r3h = 0 *)
QAssign r2h (QConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r3l += mulrax *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r3l += mulrax *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r3l += mulrax *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r3l += mulrax *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r3l_stack = r3l *)
      (*   r3h_stack = r3h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r4 += (r4h.r4l) = x4*y0 + x3*y1 + x2*y2 + x1*y3 + x0*y4 *)
      (*   r4l = *[uint64 *](rp + 32) *)
QAssign r4l (QVar r4);
      (*   r4h = 0 *)
QAssign r4h (QConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y0)) wsize;
      (*   carry? r4l += mulrax *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   carry? r4l += mulrax *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r4l += mulrax *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r4l += mulrax *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
QAssign mulrax (QVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r4l += mulrax *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar mulrax));
QSplit carry r4l (QVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
QAssign r4h (QBinop QAdd (QVar r4h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r4l_stack = r4l *)
      (*   r4h_stack = r4h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r5 += (r5h.r5l) = x4*y1 + x3*y2 + x2*y3 + x1*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y1)) wsize;
      (*   r5l = mulrax *)
QAssign r5l (QVar mulrax);
      (*   r5h = mulrdx *)
QAssign r5h (QVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   carry? r5l += mulrax *)
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r5l += mulrax *)
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
QAssign mulrax (QVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r5l += mulrax *)
QAssign r5l (QBinop QAdd (QVar r5l) (QVar mulrax));
QSplit carry r5l (QVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
QAssign r5h (QBinop QAdd (QVar r5h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r5l_stack = r5l *)
      (*   r5h_stack = r5h *)
(* TODO: skip? *)
      (*  *)
      (*  *)
      (* # Compute r6 += (r6h.r6l) = x4*y2 + x3*y3 + x2*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y2)) wsize;
      (*   r6l = mulrax *)
QAssign r6l (QVar mulrax);
      (*   r6h = mulrdx *)
QAssign r6h (QVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   carry? r6l += mulrax *)
QAssign r6l (QBinop QAdd (QVar r6l) (QVar mulrax));
QSplit carry r6l (QVar r6l) wsize;
      (*   r6h += mulrdx + carry *)
QAssign r6h (QBinop QAdd (QVar r6h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
QAssign mulrax (QVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r6l += mulrax *)
QAssign r6l (QBinop QAdd (QVar r6l) (QVar mulrax));
QSplit carry r6l (QVar r6l) wsize;
      (*   r6h += mulrdx + carry *)
QAssign r6h (QBinop QAdd (QVar r6h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r6l_stack = r6l *)
      (*   r6h_stack = r6h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r7 += (r7h.r7l) = x4*y3 + x3*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y3)) wsize;
      (*   r7l = mulrax *)
QAssign r7l (QVar mulrax);
      (*   r7h = mulrdx *)
QAssign r7h (QVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
QAssign mulrax (QVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   carry? r7l += mulrax *)
QAssign r7l (QBinop QAdd (QVar r7l) (QVar mulrax));
QSplit carry r7l (QVar r7l) wsize;
      (*   r7h += mulrdx + carry *)
QAssign r7h (QBinop QAdd (QVar r7h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*  *)
      (*   r7l_stack = r7l *)
      (*   r7h_stack = r7h *)
(* TODO: skip? *)
      (*  *)
      (*  *)
      (* # Compute r8 += (r8h.r8l) = x4*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
QAssign mulrax (QVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar y4)) wsize;
      (*   r8l = mulrax *)
QAssign r8l (QVar mulrax);
      (*   r8h = mulrdx *)
QAssign r8h (QVar mulrdx);
      (*  *)
      (*   r8l_stack = r8l *)
      (*   r8h_stack = r8h *)
(* TODO: skip? *)
      (*  *)
      (* #// assert r0h.r0l = (x0 * y0) + r0 && *)
      (* #//        r1h.r1l = (x1 * y0 + x0 * y1) + r1 && *)
      (* #//        r2h.r2l = (x2 * y0 + x1 * y1 + x0 * y2) + r2 && *)
      (* #//        r3h.r3l = (x3 * y0 + x2 * y1 + x1 * y2 + x0 * y3) + r3 && *)
      (* #//        r4h.r4l = (x4 * y0 + x3 * y1 + x2 * y2 + x1 * y3 + x0 * y4) + r4 && *)
      (* #//        r5h.r5l = x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4 && *)
      (* #//        r6h.r6l = x4 * y2 + x3 * y3 + x2 * y4 && *)
      (* #//        r7h.r7l = x4 * y3 + x3 * y4 && *)
      (* #//        r8h.r8l = x4 * y4 *)
      (*  *)
      (* #// cut 0 <=u r0h.r0l <=u 2**52 * 2**52 + 2**52 && *)
      (* #//     0 <=u r1h.r1l <=u 2**52 * 2**52 * 2 + 2**52 && *)
      (* #//     0 <=u r2h.r2l <=u 2**52 * 2**52 * 3 + 2**52 && *)
      (* #//     0 <=u r3h.r3l <=u 2**52 * 2**52 * 4 + 2**52 && *)
      (* #//     0 <=u r4h.r4l <=u 2**52 * 2**52 * 5 + 2**52 && *)
      (* #//     0 <=u r5h.r5l <=u 2**52 * 2**52 * 4 && *)
      (* #//     0 <=u r6h.r6l <=u 2**52 * 2**52 * 3 && *)
      (* #//     0 <=u r7h.r7l <=u 2**52 * 2**52 * 2 && *)
      (* #//     0 <=u r8h.r8l <=u 2**52 * 2**52 && *)
      (* #//     r0l_stack = r0l && r0h_stack = r0h && *)
      (* #//     r1l_stack = r1l && r1h_stack = r1h && *)
      (* #//     r2l_stack = r2l && r2h_stack = r2h && *)
      (* #//     r3l_stack = r3l && r3h_stack = r3h && *)
      (* #//     r4l_stack = r4l && r4h_stack = r4h && *)
      (* #//     r5l_stack = r5l && r5h_stack = r5h && *)
      (* #//     r6l_stack = r6l && r6h_stack = r6h && *)
      (* #//     r7l_stack = r7l && r7h_stack = r7h && *)
      (* #//     r8l_stack = r8l && r8h_stack = r8h && *)
      (* #//     nineteen = 19 *)
      (*  *)
      (* # Reduction modulo 2^255-19 *)
      (*  *)
      (*   #// var r0_128 = r0h.r0l *)
      (*   #//     r1_128 = r1h.r1l *)
      (*   #//     r2_128 = r2h.r2l *)
      (*   #//     r3_128 = r3h.r3l *)
      (*   #//     r4_128 = r4h.r4l *)
      (*   #//     r5_128 = r5h.r5l *)
      (*   #//     r6_128 = r6h.r6l *)
      (*   #//     r7_128 = r7h.r7l *)
      (*   #//     r8_128 = r8h.r8l *)
      (*  *)
      (*   r5l = r5l_stack *)
      (*   r5h = r5h_stack *)
      (*   r0l = r0l_stack *)
      (*   r0h = r0h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   mulrax = r5l *)
QAssign mulrax (QVar r5l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar nineteen)) wsize;
      (*   carry? r0l += mulrax *)
QAssign r0l (QBinop QAdd (QVar r0l) (QVar mulrax));
QSplit carry r0l (QVar r0l) wsize;
      (*   r0h += mulrdx + carry *)
QAssign r0h (QBinop QAdd (QVar r0h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*   r5h *= 19 *)
QAssign r5h (QBinop QMul (QVar r5h) (QConst 19%Z));
      (*   r0h += r5h *)
QAssign r0h (QBinop QAdd (QVar r0h) (QVar r5h));
      (*  *)
      (*   r0l_stack = r0l *)
      (*   r0h_stack = r0h *)
(* TODO: skip? *)
      (*  *)
      (*   r6l = r6l_stack *)
      (*   r6h = r6h_stack *)
      (*   r1l = r1l_stack *)
      (*   r1h = r1h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   mulrax = r6l *)
QAssign mulrax (QVar r6l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar nineteen)) wsize;
      (*   carry? r1l += mulrax *)
QAssign r1l (QBinop QAdd (QVar r1l) (QVar mulrax));
QSplit carry r1l (QVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
QAssign r1h (QBinop QAdd (QVar r1h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*   r6h *= 19 *)
QAssign r6h (QBinop QMul (QVar r6h) (QConst 19%Z));
      (*   r1h += r6h *)
QAssign r1h (QBinop QAdd (QVar r1h) (QVar r6h));
      (*  *)
      (*   r1l_stack = r1l *)
      (*   r1h_stack = r1h *)
(* TODO: skip? *)
      (*  *)
      (*   r7l = r7l_stack *)
      (*   r7h = r7h_stack *)
      (*   r2l = r2l_stack *)
      (*   r2h = r2h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   mulrax = r7l *)
QAssign mulrax (QVar r7l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar nineteen)) wsize;
      (*   carry? r2l += mulrax *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar mulrax));
QSplit carry r2l (QVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
QAssign r2h (QBinop QAdd (QVar r2h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*   r7h *= 19 *)
QAssign r7h (QBinop QMul (QVar r7h) (QConst 19%Z));
      (*   r2h += r7h *)
QAssign r2h (QBinop QAdd (QVar r2h) (QVar r7h));
      (*  *)
      (*   r2l_stack = r2l *)
      (*   r2h_stack = r2h *)
(* TODO: skip? *)
      (*  *)
      (*   r8l = r8l_stack *)
      (*   r8h = r8h_stack *)
      (*   r3l = r3l_stack *)
      (*   r3h = r3h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   mulrax = r8l *)
QAssign mulrax (QVar r8l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
QSplit mulrdx mulrax (QBinop QMul (QVar mulrax) (QVar nineteen)) wsize;
      (*   carry? r3l += mulrax *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar mulrax));
QSplit carry r3l (QVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
QAssign r3h (QBinop QAdd (QVar r3h) (QBinop QAdd (QVar mulrdx) (QVar carry)));
      (*   r8h *= 19 *)
QAssign r8h (QBinop QMul (QVar r8h) (QConst 19%Z));
      (*   r3h += r8h *)
QAssign r3h (QBinop QAdd (QVar r3h) (QVar r8h));
      (*  *)
      (*   r3l_stack = r3l *)
      (*   r3h_stack = r3h *)
(* TODO: skip? *)
      (*  *)
      (*   # lhs = r0_128@u512 + r1_128@u512 * 2**51 + r2_128@u512 * 2**102 + r3_128@u512 * 2**153 + *)
      (*   #       r4_128@u512 * 2**204 + r5_128@u512 * 2**255 + r3_128@u512 * 2**306 + *)
      (*   #       r7_128@u512 * 2**357 + r8_128@u512 * 2**408 *)
      (*   # rhs = (r0h.r0l)@u512 + (r1h.r1l)@u512 * 2**51 + (r2h.r2l)@u512 * 2**102 + *)
      (*   #       (r3h.r3l)@u512 * 2**153 + (r4h.r4l)@u512 * 2**204 *)
      (*  *)
      (*   #// assert ((r0_128@u512 + r5_128@u512 * 2**255) - (r0h.r0l)@u512) %u (2**255 - 19) = 0 && *)
      (*   #//        ((r1_128@u512 * 2**51 + r6_128@u512 * 2**306) - (r1h.r1l)@u512 * 2**51) %u (2**255 - 19) = 0 && *)
      (*   #//        ((r2_128@u512 * 2**102 + r7_128@u512 * 2**357) - (r2h.r2l)@u512 * 2**102) %u (2**255 - 19) = 0 && *)
      (*   #//        ((r3_128@u512 * 2**153 + r8_128@u512 * 2**408) - (r3h.r3l)@u512 * 2**153) %u (2**255 - 19) = 0 && *)
      (*   #//        (r4_128@u512 * 2**204 - (r4h.r4l)@u512 * 2**204) %u (2**255 - 19) = 0 *)
      (*  *)
      (*   #// cut 0 <=u r0h.r0l <=u 2**52 * 2**52 + 2**52 + 19 * 2**52 * 2**52 * 4 && *)
      (*   #//     0 <=u r1h.r1l <=u 2**52 * 2**52 * 2 + 2**52 + 19 * 2**52 * 2**52 * 3 && *)
      (*   #//     0 <=u r2h.r2l <=u 2**52 * 2**52 * 3 + 2**52 + 19 * 2**52 * 2**52 * 2 && *)
      (*   #//     0 <=u r3h.r3l <=u 2**52 * 2**52 * 4 + 2**52 + 19 * 2**52 * 2**52 && *)
      (*   #//     0 <=u r4h.r4l <=u 2**52 * 2**52 * 5 + 2**52 && *)
      (*   #//     r0l_stack = r0l && r0h_stack = r0h && *)
      (*   #//     r1l_stack = r1l && r1h_stack = r1h && *)
      (*   #//     r2l_stack = r2l && r2h_stack = r2h && *)
      (*   #//     r3l_stack = r3l && r3h_stack = r3h && *)
      (*   #//     r4l_stack = r4l && r4h_stack = r4h *)
      (*  *)
      (*   #// var r0_512 = (r0h.r0l)@u512 *)
      (*   #//     r1_512 = (r1h.r1l)@u512 *)
      (*   #//     r2_512 = (r2h.r2l)@u512 *)
      (*   #//     r3_512 = (r3h.r3l)@u512 *)
      (*   #//     r4_512 = (r4h.r4l)@u512 *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
QAssign redmask (QConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*  *)
      (* # Carry chain *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
QAssign redmask (QConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*  *)
      (*   r0l = r0l_stack *)
      (*   r0h = r0h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r0h = (r0h.r0l) << 13 *)
QAssign tmp (concat_shift (QVar r0h) (QVar r0l) (13%positive));
QSplit r0h tmp (QVar tmp) wsize;
QSplit tmp r0h (QVar r0h) wsize;
      (*   r0l &= redmask *)
QSplit tmp r0l (QVar r0l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*  *)
      (*   r1l = r1l_stack *)
      (*   r1h = r1h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r1h = (r1h.r1l) << 13 *)
QAssign tmp (concat_shift (QVar r1h) (QVar r1l) (13%positive));
QSplit r1h tmp (QVar tmp) wsize;
QSplit tmp r1h (QVar r1h) wsize;
      (*   r1l &= redmask *)
QSplit tmp r1l (QVar r1l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1l += r0h *)
QAssign r1l (QBinop QAdd (QVar r1l) (QVar r0h));
      (*  *)
      (*   r2l = r2l_stack *)
      (*   r2h = r2h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r2h = (r2h.r2l) << 13 *)
QAssign tmp (concat_shift (QVar r2h) (QVar r2l) (13%positive));
QSplit r2h tmp (QVar tmp) wsize;
QSplit tmp r2h (QVar r2h) wsize;
      (*   r2l &= redmask *)
QSplit tmp r2l (QVar r2l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2l += r1h *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar r1h));
      (*  *)
      (*   r3l = r3l_stack *)
      (*   r3h = r3h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r3h = (r3h.r3l) << 13 *)
QAssign tmp (concat_shift (QVar r3h) (QVar r3l) (13%positive));
QSplit r3h tmp (QVar tmp) wsize;
QSplit tmp r3h (QVar r3h) wsize;
      (*   r3l &= redmask *)
QSplit tmp r3l (QVar r3l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r3l += r2h *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar r2h));
      (*  *)
      (*   r4l = r4l_stack *)
      (*   r4h = r4h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r4h = (r4h.r4l) << 13 *)
QAssign tmp (concat_shift (QVar r4h) (QVar r4l) (13%positive));
QSplit r4h tmp (QVar tmp) wsize;
QSplit tmp r4h (QVar r4h) wsize;
      (*   r4l &= redmask *)
QSplit tmp r4l (QVar r4l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4l += r3h *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar r3h));
      (*  *)
      (*   r4h = r4h * 19 *)
QAssign r4h (QBinop QMul (QVar r4h) (QConst 19%Z));
      (*   r0l += r4h *)
QAssign r0l (QBinop QAdd (QVar r0l) (QVar r4h));
      (*  *)
      (*   #// var r0l_512' = r0l@u512 *)
      (*   #//     r1l_512' = r1l@u512 *)
      (*   #//     r2l_512' = r2l@u512 *)
      (*   #//     r3l_512' = r3l@u512 *)
      (*   #//     r4l_512' = r4l@u512 *)
      (*   #//     lhs = r0_512 + r1_512 * 2**51 + r2_512 * 2**102 + r3_512 * 2**153 + r4_512 * 2**204 *)
      (*   #//     rhs = r0l_512' + r1l_512' * 2**51 + r2l_512' * 2**102 + r3l_512' * 2**153 + r4l_512' * 2**204 *)
      (*  *)
      (*   #// assert (lhs - rhs) %u (2**255 - 19) = 0 *)
      (*  *)
      (*   #// cut 0 <=u r0l <=u 2**60 && *)
      (*   #//     0 <=u r1l <=u 2**60 && *)
      (*   #//     0 <=u r2l <=u 2**60 && *)
      (*   #//     0 <=u r3l <=u 2**60 && *)
      (*   #//     0 <=u r4l <=u 2**60 && *)
      (*   #//     redmask = mem64[crypto_sign_ed25519_amd64_51_REDMASK51] *)
      (*  *)
      (*   #// var r0l_512 = r0l@u512 *)
      (*   #//     r1l_512 = r1l@u512 *)
      (*   #//     r2l_512 = r2l@u512 *)
      (*   #//     r3l_512 = r3l@u512 *)
      (*   #//     r4l_512 = r4l@u512 *)
      (*  *)
      (*   r0h = r0l *)
QAssign r0h (QVar r0l);
      (*   (uint64) r0h >>= 51 *)
QSplit r0h tmp (QVar r0h) (51%positive);
      (*   r0l &= redmask *)
QSplit tmp r0l (QVar r0l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1l += r0h *)
QAssign r1l (QBinop QAdd (QVar r1l) (QVar r0h));
      (*  *)
      (*   r1h = r1l *)
QAssign r1h (QVar r1l);
      (*   (uint64) r1h >>= 51 *)
QSplit r1h tmp (QVar r1h) (51%positive);
      (*   r1l &= redmask *)
QSplit tmp r1l (QVar r1l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2l += r1h *)
QAssign r2l (QBinop QAdd (QVar r2l) (QVar r1h));
      (*  *)
      (*   r2h = r2l *)
QAssign r2h (QVar r2l);
      (*   (uint64) r2h >>= 51 *)
QSplit r2h tmp (QVar r2h) (51%positive);
      (*   r2l &= redmask *)
QSplit tmp r2l (QVar r2l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r3l += r2h *)
QAssign r3l (QBinop QAdd (QVar r3l) (QVar r2h));
      (*  *)
      (*   r3h = r3l *)
QAssign r3h (QVar r3l);
      (*   (uint64) r3h >>= 51 *)
QSplit r3h tmp (QVar r3h) (51%positive);
      (*   r3l &= redmask *)
QSplit tmp r3l (QVar r3l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4l += r3h *)
QAssign r4l (QBinop QAdd (QVar r4l) (QVar r3h));
      (*  *)
      (*   r4h = r4l *)
QAssign r4h (QVar r4l);
      (*   (uint64) r4h >>= 51 *)
QSplit r4h tmp (QVar r4h) (51%positive);
      (*   r4l &= redmask *)
QSplit tmp r4l (QVar r4l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4h *= 19 *)
QAssign r4h (QBinop QMul (QVar r4h) (QConst 19%Z));
      (*   r0l += r4h *)
QAssign r0l (QBinop QAdd (QVar r0l) (QVar r4h));
      (*  *)
      (*   #// var lhs = r0l_512 + r1l_512 * 2**51 + r2l_512 * 2**102 + r3l_512 * 2**153 + r4l_512 * 2**204 *)
      (*   #//     rhs = r0l@u512 + r1l@u512 * 2**51 + r2l@u512 * 2**102 + r3l@u512 * 2**153 + r4l@u512 * 2**204 *)
      (*  *)
      (*   #// assert 0 <=u r0l <=u 2**52 && *)
      (*   #//        0 <=u r1l <=u 2**52 && *)
      (*   #//        0 <=u r2l <=u 2**52 && *)
      (*   #//        0 <=u r3l <=u 2**52 && *)
      (*   #//        0 <=u r4l <=u 2**52 && *)
      (*   #//        (lhs - rhs) %u (2**255 - 19) = 0 *)
      (*  *)
      (*   *[uint64 *](rp + 0) = r0l *)
QAssign r0 (QVar r0l);
      (*   *[uint64 *](rp + 8) = r1l *)
QAssign r1 (QVar r1l);
      (*   *[uint64 *](rp + 16) = r2l *)
QAssign r2 (QVar r2l);
      (*   *[uint64 *](rp + 24) = r3l *)
QAssign r3 (QVar r3l);
      (*   *[uint64 *](rp + 32) = r4l *)
QAssign r4 (QVar r4l)
      (*  *)
      (*   c1 =c1_stack *)
      (*   c2 =c2_stack *)
      (*   c3 =c3_stack *)
      (*   c4 =c4_stack *)
      (*   c5 =c5_stack *)
      (*   c6 =c6_stack *)
      (*   c7 =c7_stack *)
      (*  *)
      (*   leave *)
] .

