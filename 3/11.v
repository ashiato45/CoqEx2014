Require Import Arith.

Fixpoint sum_odd(n:nat):nat :=
match n with
|O=>O
|S m => 1 + m + m + sum_odd m
end.

Goal forall n, sum_odd n = n*n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
replace (n+n*S n) with (n + n + n*n).
reflexivity.
rewrite <- plus_assoc.
apply NPeano.Nat.add_cancel_l.
replace (S n) with (n + 1).
rewrite -> mult_plus_distr_l.
rewrite -> mult_1_r.
apply (plus_comm n (n*n)).
apply (NPeano.Nat.add_1_r n).
Qed.
