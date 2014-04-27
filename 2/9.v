Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
intros.
apply plus_permute_2_in_4.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
intros.
rewrite -> mult_plus_distr_r.
rewrite -> mult_plus_distr_l.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
apply NPeano.Nat.add_cancel_l.
rewrite -> mult_plus_distr_l.
replace (m*n) with (n*m).
rewrite -> plus_assoc.
replace (2*n*m) with (n*m+n*m).
rewrite -> plus_comm.
reflexivity.
simpl.
rewrite -> mult_plus_distr_r.
apply NPeano.Nat.add_cancel_l.
rewrite -> mult_plus_distr_r.
rewrite -> mult_0_l.
rewrite -> plus_0_r.
reflexivity.
apply mult_comm.
Qed.