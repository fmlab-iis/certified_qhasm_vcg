From Coq Require Import ZArith .
From mQhasm Require Import mQhasm .
From mathcomp Require Import seq .

Definition muladd25519 : program :=

let          qtwo :=   zConst 2%Z in
let         wsize :=   64%positive in

let concat_shift hi lo w :=       (* (hi.lo) << w *)
      zBinop zMul (zBinop zAdd (zBinop zMul hi (zPow qtwo wsize)) lo)
                  (zPow qtwo w) in

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
zAssign nineteen (zConst 19%Z);
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
zAssign r0l (zVar r0);
      (*   r0h = 0 *)
zAssign r0h (zConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 0) *)
zAssign mulrax (zVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
      (*   carry? r0l += mulrax *)
zAssign r0l (zBinop zAdd (zVar r0l) (zVar mulrax));
zSplit carry r0l (zVar r0l) wsize;
      (*   r0h += mulrdx + carry *)
zAssign r0h (zBinop zAdd (zVar r0h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r0l_stack = r0l *)
      (*   r0h_stack = r0h *)
      (*  *)
      (* # Compute r1 += (r1h.r1l) = x1*y0 + x0*y1 *)
      (*   r1l = *[uint64 *](rp + 8) *)
zAssign r1l (zVar r1);
      (*   r1h = 0 *)
zAssign r1h (zConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 8) *)
zAssign mulrax (zVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
      (*   carry? r1l += mulrax *)
zAssign r1l (zBinop zAdd (zVar r1l) (zVar mulrax));
zSplit carry r1l (zVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
zAssign r1h (zBinop zAdd (zVar r1h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
zAssign mulrax (zVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
      (*   carry? r1l += mulrax *)
zAssign r1l (zBinop zAdd (zVar r1l) (zVar mulrax));
zSplit carry r1l (zVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
zAssign r1h (zBinop zAdd (zVar r1h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r1l_stack = r1l *)
      (*   r1h_stack = r1h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r2 += (r2h.r2l) = x2*y0 + + x1*y1 + x0*y2 *)
      (*   r2l = *[uint64 *](rp + 16) *)
zAssign r2l (zVar r2);
      (*   r2h = 0 *)
zAssign r2h (zConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 16) *)
zAssign mulrax (zVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
      (*   carry? r2l += mulrax *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
zAssign mulrax (zVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
      (*   carry? r2l += mulrax *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
zAssign mulrax (zVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
      (*   carry? r2l += mulrax *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r2l_stack = r2l *)
      (*   r2h_stack = r2h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r3 += (r3h.r3l) = x3*y0 + x2*y1 + x1*y2 + x0*y3 *)
      (*   r3l = *[uint64 *](rp + 24) *)
zAssign r3l (zVar r3);
      (*   r3h = 0 *)
zAssign r2h (zConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 24) *)
zAssign mulrax (zVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
      (*   carry? r3l += mulrax *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
zAssign mulrax (zVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
      (*   carry? r3l += mulrax *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
zAssign mulrax (zVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
      (*   carry? r3l += mulrax *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
zAssign mulrax (zVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
      (*   carry? r3l += mulrax *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r3l_stack = r3l *)
      (*   r3h_stack = r3h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r4 += (r4h.r4l) = x4*y0 + x3*y1 + x2*y2 + x1*y3 + x0*y4 *)
      (*   r4l = *[uint64 *](rp + 32) *)
zAssign r4l (zVar r4);
      (*   r4h = 0 *)
zAssign r4h (zConst 0%Z);
      (*   mulrax = *[uint64 *](xp + 32) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
      (*   carry? r4l += mulrax *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
zAssign mulrax (zVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
      (*   carry? r4l += mulrax *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
zAssign mulrax (zVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
      (*   carry? r4l += mulrax *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
zAssign mulrax (zVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
      (*   carry? r4l += mulrax *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
zAssign mulrax (zVar x0);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
      (*   carry? r4l += mulrax *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar mulrax));
zSplit carry r4l (zVar r4l) wsize;
      (*   r4h += mulrdx + carry *)
zAssign r4h (zBinop zAdd (zVar r4h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r4l_stack = r4l *)
      (*   r4h_stack = r4h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r5 += (r5h.r5l) = x4*y1 + x3*y2 + x2*y3 + x1*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
      (*   r5l = mulrax *)
zAssign r5l (zVar mulrax);
      (*   r5h = mulrdx *)
zAssign r5h (zVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
      (*   carry? r5l += mulrax *)
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
zAssign mulrax (zVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
      (*   carry? r5l += mulrax *)
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
zAssign mulrax (zVar x1);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
      (*   carry? r5l += mulrax *)
zAssign r5l (zBinop zAdd (zVar r5l) (zVar mulrax));
zSplit carry r5l (zVar r5l) wsize;
      (*   r5h += mulrdx + carry *)
zAssign r5h (zBinop zAdd (zVar r5h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r5l_stack = r5l *)
      (*   r5h_stack = r5h *)
(* TODO: skip? *)
      (*  *)
      (*  *)
      (* # Compute r6 += (r6h.r6l) = x4*y2 + x3*y3 + x2*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
      (*   r6l = mulrax *)
zAssign r6l (zVar mulrax);
      (*   r6h = mulrdx *)
zAssign r6h (zVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
zAssign mulrax (zVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
      (*   carry? r6l += mulrax *)
zAssign r6l (zBinop zAdd (zVar r6l) (zVar mulrax));
zSplit carry r6l (zVar r6l) wsize;
      (*   r6h += mulrdx + carry *)
zAssign r6h (zBinop zAdd (zVar r6h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
zAssign mulrax (zVar x2);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
      (*   carry? r6l += mulrax *)
zAssign r6l (zBinop zAdd (zVar r6l) (zVar mulrax));
zSplit carry r6l (zVar r6l) wsize;
      (*   r6h += mulrdx + carry *)
zAssign r6h (zBinop zAdd (zVar r6h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r6l_stack = r6l *)
      (*   r6h_stack = r6h *)
(* TODO: skip? *)
      (*  *)
      (* # Compute r7 += (r7h.r7l) = x4*y3 + x3*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
      (*   r7l = mulrax *)
zAssign r7l (zVar mulrax);
      (*   r7h = mulrdx *)
zAssign r7h (zVar mulrdx);
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
zAssign mulrax (zVar x3);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
      (*   carry? r7l += mulrax *)
zAssign r7l (zBinop zAdd (zVar r7l) (zVar mulrax));
zSplit carry r7l (zVar r7l) wsize;
      (*   r7h += mulrdx + carry *)
zAssign r7h (zBinop zAdd (zVar r7h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*   r7l_stack = r7l *)
      (*   r7h_stack = r7h *)
(* TODO: skip? *)
      (*  *)
      (*  *)
      (* # Compute r8 += (r8h.r8l) = x4*y4 *)
      (*   mulrax = *[uint64 *](xp + 32) *)
zAssign mulrax (zVar x4);
      (* (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
      (*   r8l = mulrax *)
zAssign r8l (zVar mulrax);
      (*   r8h = mulrdx *)
zAssign r8h (zVar mulrdx);
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
zAssign mulrax (zVar r5l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar nineteen)) wsize;
      (*   carry? r0l += mulrax *)
zAssign r0l (zBinop zAdd (zVar r0l) (zVar mulrax));
zSplit carry r0l (zVar r0l) wsize;
      (*   r0h += mulrdx + carry *)
zAssign r0h (zBinop zAdd (zVar r0h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*   r5h *= 19 *)
zAssign r5h (zBinop zMul (zVar r5h) (zConst 19%Z));
      (*   r0h += r5h *)
zAssign r0h (zBinop zAdd (zVar r0h) (zVar r5h));
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
zAssign mulrax (zVar r6l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar nineteen)) wsize;
      (*   carry? r1l += mulrax *)
zAssign r1l (zBinop zAdd (zVar r1l) (zVar mulrax));
zSplit carry r1l (zVar r1l) wsize;
      (*   r1h += mulrdx + carry *)
zAssign r1h (zBinop zAdd (zVar r1h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*   r6h *= 19 *)
zAssign r6h (zBinop zMul (zVar r6h) (zConst 19%Z));
      (*   r1h += r6h *)
zAssign r1h (zBinop zAdd (zVar r1h) (zVar r6h));
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
zAssign mulrax (zVar r7l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar nineteen)) wsize;
      (*   carry? r2l += mulrax *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar mulrax));
zSplit carry r2l (zVar r2l) wsize;
      (*   r2h += mulrdx + carry *)
zAssign r2h (zBinop zAdd (zVar r2h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*   r7h *= 19 *)
zAssign r7h (zBinop zMul (zVar r7h) (zConst 19%Z));
      (*   r2h += r7h *)
zAssign r2h (zBinop zAdd (zVar r2h) (zVar r7h));
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
zAssign mulrax (zVar r8l);
      (*   (uint128) mulrdx mulrax = mulrax * nineteen *)
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar nineteen)) wsize;
      (*   carry? r3l += mulrax *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar mulrax));
zSplit carry r3l (zVar r3l) wsize;
      (*   r3h += mulrdx + carry *)
zAssign r3h (zBinop zAdd (zVar r3h) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*   r8h *= 19 *)
zAssign r8h (zBinop zMul (zVar r8h) (zConst 19%Z));
      (*   r3h += r8h *)
zAssign r3h (zBinop zAdd (zVar r3h) (zVar r8h));
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
zAssign redmask (zConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*  *)
      (* # Carry chain *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
zAssign redmask (zConst crypto_sign_ed25519_amd64_51_REDMASK51);
      (*  *)
      (*   r0l = r0l_stack *)
      (*   r0h = r0h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r0h = (r0h.r0l) << 13 *)
zAssign tmp (concat_shift (zVar r0h) (zVar r0l) (13%positive));
zSplit r0h tmp (zVar tmp) wsize;
zSplit tmp r0h (zVar r0h) wsize;
      (*   r0l &= redmask *)
zSplit tmp r0l (zVar r0l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*  *)
      (*   r1l = r1l_stack *)
      (*   r1h = r1h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r1h = (r1h.r1l) << 13 *)
zAssign tmp (concat_shift (zVar r1h) (zVar r1l) (13%positive));
zSplit r1h tmp (zVar tmp) wsize;
zSplit tmp r1h (zVar r1h) wsize;
      (*   r1l &= redmask *)
zSplit tmp r1l (zVar r1l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1l += r0h *)
zAssign r1l (zBinop zAdd (zVar r1l) (zVar r0h));
      (*  *)
      (*   r2l = r2l_stack *)
      (*   r2h = r2h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r2h = (r2h.r2l) << 13 *)
zAssign tmp (concat_shift (zVar r2h) (zVar r2l) (13%positive));
zSplit r2h tmp (zVar tmp) wsize;
zSplit tmp r2h (zVar r2h) wsize;
      (*   r2l &= redmask *)
zSplit tmp r2l (zVar r2l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2l += r1h *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar r1h));
      (*  *)
      (*   r3l = r3l_stack *)
      (*   r3h = r3h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r3h = (r3h.r3l) << 13 *)
zAssign tmp (concat_shift (zVar r3h) (zVar r3l) (13%positive));
zSplit r3h tmp (zVar tmp) wsize;
zSplit tmp r3h (zVar r3h) wsize;
      (*   r3l &= redmask *)
zSplit tmp r3l (zVar r3l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r3l += r2h *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar r2h));
      (*  *)
      (*   r4l = r4l_stack *)
      (*   r4h = r4h_stack *)
(* TODO: skip? *)
      (*  *)
      (*   r4h = (r4h.r4l) << 13 *)
zAssign tmp (concat_shift (zVar r4h) (zVar r4l) (13%positive));
zSplit r4h tmp (zVar tmp) wsize;
zSplit tmp r4h (zVar r4h) wsize;
      (*   r4l &= redmask *)
zSplit tmp r4l (zVar r4l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4l += r3h *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar r3h));
      (*  *)
      (*   r4h = r4h * 19 *)
zAssign r4h (zBinop zMul (zVar r4h) (zConst 19%Z));
      (*   r0l += r4h *)
zAssign r0l (zBinop zAdd (zVar r0l) (zVar r4h));
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
zAssign r0h (zVar r0l);
      (*   (uint64) r0h >>= 51 *)
zSplit r0h tmp (zVar r0h) (51%positive);
      (*   r0l &= redmask *)
zSplit tmp r0l (zVar r0l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r1l += r0h *)
zAssign r1l (zBinop zAdd (zVar r1l) (zVar r0h));
      (*  *)
      (*   r1h = r1l *)
zAssign r1h (zVar r1l);
      (*   (uint64) r1h >>= 51 *)
zSplit r1h tmp (zVar r1h) (51%positive);
      (*   r1l &= redmask *)
zSplit tmp r1l (zVar r1l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r2l += r1h *)
zAssign r2l (zBinop zAdd (zVar r2l) (zVar r1h));
      (*  *)
      (*   r2h = r2l *)
zAssign r2h (zVar r2l);
      (*   (uint64) r2h >>= 51 *)
zSplit r2h tmp (zVar r2h) (51%positive);
      (*   r2l &= redmask *)
zSplit tmp r2l (zVar r2l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r3l += r2h *)
zAssign r3l (zBinop zAdd (zVar r3l) (zVar r2h));
      (*  *)
      (*   r3h = r3l *)
zAssign r3h (zVar r3l);
      (*   (uint64) r3h >>= 51 *)
zSplit r3h tmp (zVar r3h) (51%positive);
      (*   r3l &= redmask *)
zSplit tmp r3l (zVar r3l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4l += r3h *)
zAssign r4l (zBinop zAdd (zVar r4l) (zVar r3h));
      (*  *)
      (*   r4h = r4l *)
zAssign r4h (zVar r4l);
      (*   (uint64) r4h >>= 51 *)
zSplit r4h tmp (zVar r4h) (51%positive);
      (*   r4l &= redmask *)
zSplit tmp r4l (zVar r4l) crypto_sign_ed25519_amd64_51_REDMASK51_width;
      (*   r4h *= 19 *)
zAssign r4h (zBinop zMul (zVar r4h) (zConst 19%Z));
      (*   r0l += r4h *)
zAssign r0l (zBinop zAdd (zVar r0l) (zVar r4h));
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
zAssign r0 (zVar r0l);
      (*   *[uint64 *](rp + 8) = r1l *)
zAssign r1 (zVar r1l);
      (*   *[uint64 *](rp + 16) = r2l *)
zAssign r2 (zVar r2l);
      (*   *[uint64 *](rp + 24) = r3l *)
zAssign r3 (zVar r3l);
      (*   *[uint64 *](rp + 32) = r4l *)
zAssign r4 (zVar r4l)
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

