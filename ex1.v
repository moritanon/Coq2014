Theorem tautology: forall P : Prop, P -> P.
Proof.
 intros P H.
 assumption.
Qed.

Theorem wrong: forall P : Prop, P.
Proof.
 intros P.
Admitted.

Theorem Modus_ponens : forall P Q : Prop, 
P->(P->Q)->Q.
Proof.
intros P Q.
intros H1.
intros H2.
apply H2. 
assumption.
Qed.

Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P->Q) -> ~P.
Proof.
intros P Q.
unfold not.
intros.
apply H.
apply H. 
assumption.
Qed.


(* 課題3 *)
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
intros.
unfold not in H0.
destruct H.
apply H0 in H.
inversion H.
assumption.
Qed.

(* 課題4 *)
Theorem DeMorgan1 : forall P Q : Prop,  ~P \/ ~Q -> ~(P /\ Q).
Proof.
unfold not.
intros.
inversion H. 
apply H1.
apply H0.
apply H1.

apply H0. 

Qed.


Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
unfold not.
intros.
inversion H.
apply H1. destruct H0. assumption.
apply H2 in H0. inversion H0.
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros.
  apply conj.
  intros.
  destruct H. left.
  assumption.
  intros.  apply H. right. assumption.
Qed.

Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  unfold not.
  intros. apply H.
  right. intros.
  apply H. left. assumption.
Qed.

Require Import Arith.

SearchAbout lt _ _.