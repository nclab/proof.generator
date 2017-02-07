Require Import Arith.

Definition sum f := fix s n := match n with O => f O | S x => f n + s x end.

Theorem arith_sum a b n : 2 * sum (fun i => a + i * b) n = S n * (2 * a + n * b).
Proof.
  induction n.
  simpl.
  ring.
  ring_simplify.
  rewrite mult_comm.
  eapply eq_sym.
  simpl.
  rewrite -> plus_0_r.
  ring_simplify.
  rewrite IHn.
  ring_simplify.
  ring.
Qed.
