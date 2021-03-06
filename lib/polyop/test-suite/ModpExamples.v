Add Rec LoadPath "../src/" as PolyOp.
Add ML Path "../src/".

From Coq Require Import ZArith.
From PolyOp Require Import Modp.

Open Scope Z_scope.

Goal forall x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : Z,
    exists k : Z,
    ((x + (x0 * 2 ^ 51 + (x1 * 2 ^ 102 + (x2 * 2 ^ 153 + x3 * 2 ^ 204)))) *
     (x4 + (x5 * 2 ^ 51 + (x6 * 2 ^ 102 + (x7 * 2 ^ 153 + x8 * 2 ^ 204)))) -
     (x2 * 19 * x6 - x9 * 2 ^ 64 + (x3 * 19 * x5 - x10 * 2 ^ 64) -
      x11 * 2 ^ 64 + (x * x4 - x12 * 2 ^ 64) - x13 * 2 ^ 64 +
      (x0 * 19 * x8 - x14 * 2 ^ 64) - x15 * 2 ^ 64 +
      (x1 * 19 * x7 - x16 * 2 ^ 64) - x17 * 2 ^ 64 -
      x18 * 2 ^ 51 +
      ((x19 + (x20 + x21) + (x22 + x23) + (x24 + x25) + (x26 + x27)) * 2 ^ 13 +
       x28) * 19 - x29 * 2 ^ 51 + x30 * 19 +
      ((x29 +
        (x * x5 - x31 * 2 ^ 64 + (x0 * x4 - x32 * 2 ^ 64) - x33 * 2 ^ 64 +
         (x1 * 19 * x8 - x34 * 2 ^ 64) - x35 * 2 ^ 64 +
         (x2 * 19 * x7 - x36 * 2 ^ 64) - x37 * 2 ^ 64 +
         (x3 * 19 * x6 - x38 * 2 ^ 64) - x39 * 2 ^ 64 -
         x40 * 2 ^ 51 +
         ((x9 + (x10 + x11) + (x12 + x13) + (x14 + x15) + (x16 + x17)) *
          2 ^ 13 + x18)) - x41 * 2 ^ 51) * 2 ^ 51 +
       ((x41 +
         (x * x6 - x42 * 2 ^ 64 + (x0 * x5 - x43 * 2 ^ 64) - x44 * 2 ^ 64 +
          (x1 * x4 - x45 * 2 ^ 64) - x46 * 2 ^ 64 +
          (x2 * 19 * x8 - x47 * 2 ^ 64) - x48 * 2 ^ 64 +
          (x3 * 19 * x7 - x49 * 2 ^ 64) - x50 * 2 ^ 64 -
          x51 * 2 ^ 51 +
          ((x31 + (x32 + x33) + (x34 + x35) + (x36 + x37) + (x38 + x39)) *
           2 ^ 13 + x40)) - x52 * 2 ^ 51) * 2 ^ 102 +
        ((x52 +
          (x * x7 - x53 * 2 ^ 64 + (x0 * x6 - x54 * 2 ^ 64) - x55 * 2 ^ 64 +
           (x1 * x5 - x56 * 2 ^ 64) - x57 * 2 ^ 64 +
           (x2 * x4 - x58 * 2 ^ 64) - x59 * 2 ^ 64 +
           (x3 * 19 * x8 - x60 * 2 ^ 64) - x61 * 2 ^ 64 -
           x62 * 2 ^ 51 +
           ((x42 + (x43 + x44) + (x45 + x46) + (x47 + x48) + (x49 + x50)) *
            2 ^ 13 + x51)) - x63 * 2 ^ 51) * 2 ^ 153 +
         (x63 +
          (x * x8 - x19 * 2 ^ 64 + (x0 * x7 - x20 * 2 ^ 64) - x21 * 2 ^ 64 +
           (x1 * x6 - x22 * 2 ^ 64) - x23 * 2 ^ 64 +
           (x2 * x5 - x24 * 2 ^ 64) - x25 * 2 ^ 64 +
           (x3 * x4 - x26 * 2 ^ 64) - x27 * 2 ^ 64 -
           x28 * 2 ^ 51 +
           ((x53 + (x54 + x55) + (x56 + x57) + (x58 + x59) + (x60 + x61)) *
            2 ^ 13 + x62)) - x30 * 2 ^ 51) * 2 ^ 204)))))%Z =
    (k *
     57896044618658097711785492504343953926634992332820282019728792003956564819949)%Z.
Proof.
  intros.
  modp_find_witness.
Qed.
