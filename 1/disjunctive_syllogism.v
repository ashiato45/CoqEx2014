Theorem Disjunctive_syllogism : forall P Q: Prop, (P \/ Q) -> ~P -> Q.
intros.
case H.
intros.
exfalso.
apply H0.
apply H1.
intros.
apply H1.
Qed.