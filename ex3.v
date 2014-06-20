Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
 match n with
 | O => O
 | S m =>  1 + m + m + sum_odd m
end.

Eval compute in sum_odd 0. (* 0 *)
Eval compute in sum_odd 1. (* 1 + 0 = 1 *)
Eval compute in sum_odd 2. (* 3 + 1 + 0 = 4 *)
Eval compute in sum_odd 3. (* 5 + 3 + 1 + 0 = 9 *)

(* 課題11 *)
Goal forall n, sum_odd n = n * n.
Proof.
 intros.
 induction n.
 (* Case O *)
   compute. reflexivity.
 (* Case S n' *)
   SearchAbout (S _ *  _ ).
   rewrite mult_succ_l.
   rewrite mult_succ_r. simpl. rewrite IHn. 
   ring. 
Qed.

(* 課題12 *)
Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

(*
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Definition lt (n m:nat) := S n <= m.
Infix "<" := lt : nat_scope.
*)

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
 intros.
 induction xs as [|x' xs'].
  simpl in H.
  inversion H.
simpl in H.
simpl In. unfold lt in H.
exists 2.
split. unfold lt. apply le_n. right.
apply IHxs'.
 SearchAbout nth.