(* Define the natural numbers *)
Inductive nat : Type :=
  | O
  | S  (n:nat).


Definition pred(n:nat) : nat :=
  match n with
  | O : O
  | S n => n
  end.

(* Define the natural numbers *)


(* Define addition *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

(* Notation for plus *)
Infix "+" := plus.

(* Example: 2 + 2 = 4 *)
Example plus_2_2 : (S (S O)) + (S (S O)) = S (S (S (S O))).
Proof. simpl. reflexivity. Qed.

(* Define a function to check if a number is even *)
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S p) => even p
  end.

(* Example: 4 is even *)
Example four_is_even : even (S (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.

(* Theorem: n + 0 = n *)
Theorem plus_O_n : forall n : nat, n + O = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S p => p
  end.


Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.
Infix "-" := minus.


Example test_minus1: (S (S (S O))) - (S O) + (S O) = (S (S (S O))).
Example test_minus1: (S (S (S O))) - (S O) + (S O) = (S (S (S O))).
Example test_minus1: (S (S (S O))) - (S O) + (S O) = (S (S (S O))).
Example test_minus1: (S (S (S O))) - (S O) + (S O) = (S (S (S O))).