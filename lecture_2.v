Require Import Unicode.Utf8.


Fixpoint eqb (n m : nat ) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => eqb n' m'
  end.


Notation "x == y" := (eqb x y) (at level 70).

Compute 5 == 5.


Fixpoint leb (n m : nat) : bool := 
    match n, m with
        | O, _ => true
        | S n', O => false
        | S n', S m' => leb n' m' 
    end.
Notation "x <= y" := (leb x y) (at level 70).
Compute S O<= 1.
Compute 5<= 5.
Compute 7<= 5.


Fixpoint my_plus(n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (my_plus n' m)
end.

Compute (my_plus 5 7).



Theorem plus_id_example: forall n m:nat,
n=m -> n+n = m+m.
Proof. 
    intros n m H. simpl. rewrite -> H. reflexivity. Qed.



Theorem plus_id_example_2: forall n m k:nat,
n=m -> m=k -> n+n = m+k.
Proof. 
    intros n m k. intros H1 H2. rewrite <- H2. rewrite <- H1. reflexivity. Qed.


Theorem plus_1_neq_0: forall n : nat,
    ((n+1) == 0 = false).
Proof. 
    intros n. 
    destruct n as [|n'].    (* adding the star makes the cases turn into subgoals *)
    * simpl. reflexivity. (* case: (0 + 1 == 0) = false *)
    * simpl. reflexivity. (* case: (S n' + 1 == 0) = false *)
Qed.


Theorem simpl_the_: forall n: nat, 0+n=n.
Proof. simpl. reflexivity. Qed.


Theorem simpl_the: forall n: nat, n+0=n.
Proof. (* simpl wont work because of how plus works *)
    intros n.
    induction n as [|n' IHn]. (* Ihn is inductive hypothsis introduced *)
    - simpl. reflexivity.
    - simpl. rewrite -> IHn. reflexivity.
Qed.

