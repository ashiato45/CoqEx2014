Definition tautology :  forall P : Prop, P -> P
:=
fun P x => x.

Definition Modus_tollens' : forall P Q : Prop, ~Q /\ (P-> Q) -> ~P.
Proof.
Show Proof.
intros.
Show Proof.
intro.
Show Proof.
apply H.
Show Proof.
apply H.
Show Proof.
apply H0.
Show Proof.
Qed.

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
:=
fun (P Q : Prop) (H1 : ~Q /\ (P -> Q)) (H2 : P) =>
((match H1 with | conj notq _ => notq end) ((match H1 with | conj _ ptoq => ptoq end) H2)).

Definition Disjunctive_syllogism' : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
intros.
case H.
intros.
exfalso.
apply H0.
apply H1.
intros.
apply H1.
Qed.

Print Disjunctive_syllogism'.

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
:=
fun (P Q : Prop) (PorQ : P \/ Q) (notP : ~P) =>
match PorQ with
| or_introl P => False_ind Q (notP P)
| or_intror Q => Q
end.

Definition tautology_on_Set' : forall A : Set, A -> A.
Proof.
intros.
apply H.
Qed.

Definition tautology_on_Set : forall A : Set, A -> A
:=
fun (A : Set) (A : A)
=> A.

Definition Modus_tollens_on_Set' : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set).
Proof.
intros.
apply H.
apply H.
apply H0.
Qed.

Print Modus_tollens_on_Set'.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B)-> (A -> Empty_set)
:=
fun (A B : Set) (BtoEMPTYprodAtoB : (B -> Empty_set)*(A->B)) (A : A)
=>
((let (BtoEMPTY, _) := BtoEMPTYprodAtoB in BtoEMPTY) ((let (_, AtoB) := BtoEMPTYprodAtoB in AtoB) A)).

Definition Disjunctive_syllogism_on_Set' : forall A B : Set, (A + B) -> (A -> Empty_set) -> B.
Proof.
intros.
case H.
intros.
contradiction.
intros.
apply b.
Qed.

Print Disjunctive_syllogism_on_Set'.

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
:=
fun (A B : Set) (AplusB : A + B) (AtoEMPTY : A -> Empty_set) =>
match AplusB with
| inl A => Empty_set_rec (fun _ : Empty_set => B) (AtoEMPTY A)
| inr B => B
end.
