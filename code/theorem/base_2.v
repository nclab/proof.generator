Require Import Omega Reals Psatz.

Open Scope R_scope.

Lemma base x y : 4 * (x * y) <= (x + y) * (x + y).
Proof.
  apply Rminus_le.
  ring_simplify.
  apply Rge_le.
  replace (- x ^ 2 + 2 * x * y - y ^ 2) with (-(x - y) ^2).
