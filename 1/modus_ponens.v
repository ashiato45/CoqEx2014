Theorem Modus_ponens: forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
intros.
apply H0.
apply H.
Qed.