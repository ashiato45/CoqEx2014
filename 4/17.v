Theorem hoge : forall P Q R : Prop, P \/ ~(Q \/ R) -> (P \/ ~Q) /\ (P \/ ~R).
Proof.
refine (fun P Q R => _).
refine (fun PornotQorR => _).
refine (match PornotQorR with
|or_introl P => _
|or_intror notQorR => _
end).
refine (conj _ _).
refine (or_introl _).
refine P0.
refine (or_introl _).
refine P0.
refine (conj _ _).
refine (or_intror _).
refine (fun Q => _).
refine (notQorR _).
refine (or_introl _).
refine Q0.
refine (or_intror _).
refine (fun R => _).
refine (notQorR _).
refine (or_intror _).
refine R0.
Qed.
