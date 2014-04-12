Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P-> Q) -> ~P.
Proof.
intros.
intro.
apply H.
apply H.
apply H0.
Qed.