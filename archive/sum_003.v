Require Import Arith.

Definition sum f := fix s n := match n with O => f O | S x => f n + s x end.

Theorem arith_sum a b n : 2 * sum (fun i => a + i * b) n = S n * (2 * a + n * b).
Proof.
  induction n.
  simpl.
  rewrite plus_comm.
  ring_simplify.
  ring.
  eapply eq_sym.
  rewrite -> plus_n_O.
  rewrite plus_comm.
  simpl.
  rewrite <- plus_n_O.
  ring_simplify.
  rewrite IHn.
  ring.
Qed.
