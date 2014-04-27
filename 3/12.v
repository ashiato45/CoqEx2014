Require Import Lists.List.

Fixpoint sum (xs : list nat) : nat :=
match xs with
|nil => 0
| x ::  xs => x + sum xs
end.

Theorem Pigeon_Hole_Principle:
forall (xs : list nat), length xs < sum xs -> (exists x, 1 < x /\ In x xs).
Proof.
intros.
induction xs.
contradict H.
simpl.
apply Lt.lt_irrefl.

Require Import Omega.
assert (a = 0 \/ a = 1 \/ a > 1).
omega.
destruct H0.
destruct IHxs.
replace (sum xs) with (sum (a :: xs)).
apply (Lt.le_lt_trans (length xs) (length (a :: xs)) (sum (a::xs))).
simpl.
apply (Le.le_n_Sn (length xs)).
apply H.
simpl.
replace a with 0.
reflexivity.
exists x.
split.
apply H1.
simpl.
right.
apply H1.
destruct H0.
destruct IHxs.
apply (plus_lt_reg_l (length xs) (sum xs) a).
apply (NPeano.Nat.lt_stepl (length (a :: xs)) (sum (a :: xs)) (a + length xs)).
apply H.
simpl.
replace a with 1.
reflexivity.
exists x.
split.
apply H1.
simpl.
right.
apply H1.
exists a.
split.
apply H0.
simpl.
left.
reflexivity.
Qed.



