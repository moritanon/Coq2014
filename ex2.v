Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.

SearchAbout (_ + _ < _ + _).

intros.
apply NPeano.Nat.add_lt_mono_r.
assumption.
Qed.

Goal forall P Q: nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  intros.
  apply H0 . apply H.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros.
  exists 1.
  simpl.
  apply H.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros. 
  destruct H0.
  apply (H x).
  assumption.
Qed.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
intros.
assert(n * 10 = 10 * n).
apply mult_comm.
rewrite H. reflexivity.
Qed.
(* SearchAbout (_ * _ = _ * _). *)


Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  SearchAbout (_ + _ = _ + _).
  apply plus_permute_2_in_4.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
SearchAbout ((_ + _) * _).
intros.
rewrite mult_plus_distr_l.
rewrite mult_plus_distr_r.
rewrite mult_plus_distr_r.
assert(H: m * n = n * m).
rewrite mult_comm.
reflexivity.
rewrite H.
assert(H2: n * m + n * m = 2 * n * m). 
simpl.  rewrite mult_plus_distr_r.
rewrite mult_plus_distr_r.
simpl.  SearchAbout (_ + 0).
rewrite <- plus_n_O.
reflexivity.
rewrite <- H2.
SearchAbout (_ + _ + _).
rewrite -> plus_assoc.
rewrite -> plus_assoc.
assert(H3:n * m + m * m = m * m + n * m).
rewrite -> plus_comm. reflexivity.
rewrite <- plus_assoc. rewrite H3.
SearchAbout (_ + _ + _).
rewrite <- plus_permute_2_in_4.
rewrite -> plus_assoc.
reflexivity.
Qed.

(* 課題10 *)

Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
Notation "x / y" := (mult x (inv y)).
Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  assert(H: //x/x=1).
  rewrite inv_l. reflexivity.
(*

1 subgoals, subgoal 1 (ID 150)
  
  x : G
  H : / / x / x = 1
  ============================
   x / x = 1
 ここで、//x = xが示せれば、証明終わりなんだけど・・・
 考え方が違うのだろうか。
 *)
Admitted.
(*
  assert(H1: //x/x*x=x).
 rewrite -> H. rewrite one_unit_l. reflexivity. 
  assert(H1: 1 * / (/ x) * / x = 1). 
  rewrite one_unit_l. apply H.
  rewrite <-  mult_assoc in H1.
  
  assert(H2: (//x/x) * x = x).
  rewrite  H. apply one_unit_l.
  rewrite <- mult_assoc in H2.
  assert(H3: //x=x).
  rewrite -> inv_l in H2.
  
  rewrite <- one_unit_l in H.
  assumption.
 
  rewrite -> inv_l. reflexivity.
  rewrite <- mult_assoc in H1. 
  rewite -> 
*)