Require Import Arith.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
intros.
apply (NPeano.Nat.add_cancel_r (n * 10) (10 * n) m).
rewrite <- mult_comm. 
reflexivity.
Qed.
