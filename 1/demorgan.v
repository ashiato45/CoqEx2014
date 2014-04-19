Theorem DeMorgan1: forall P Q: Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
intros.
intro.
case H.
intros.
apply H1.
apply H0.
intros.
apply H1.
apply H0.
Qed.

Theorem DeMorgan2: forall P Q: Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
intros.
intro.
case H0.
destruct H.
intro.
apply H.
apply H2.
intro.
apply H.
apply H1.
Qed.

Theorem DeMorgan2': forall P Q: Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
intros.
intro.
destruct H0.
destruct H.
apply H.
apply H0.
destruct H.
apply H1.
apply H0.
Qed.

Theorem DeMorgan3: forall P Q: Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
intros.
split.
intro.
apply H.
left.
apply H0.
intro.
apply H.
right.
apply H0.
Qed.
