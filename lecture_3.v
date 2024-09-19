Theorem add_0_r : forall n:nat,
n+0 =n.
Proof.
    intros n.
    induction n as [| n' IHn' ].
        + simpl. reflexivity.
        + simpl. rewrite IHn'. reflexivity.
Qed.


Theorem plus_n_Sm: forall n m : nat,
    S(n + m) = n + S(m).
Proof.
    intros. induction n.
        - simpl. reflexivity.
        - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros. induction n.
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.
Theorem mult_0_plus: forall n m: nat,
    (n+0+0) * m = n*m.
Proof.
    intros n m.
    repeat rewrite add_0_r.
    reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q: nat,
    (n+m) + (p+q) = (m+n) + (p + q).
Proof. intros.
    rewrite (add_comm n).
    reflexivity.
Qed.


Check pair.
Check pair 3 4.

Inductive natprod : Type :=
    | pair (n1 n2 :nat).

Check (pair 5 6) : natprod.

Definition fst (p : natprod) : nat :=
    match p with
        pair x y => x
    end.

Definition snd (p : natprod) : nat :=
    match p with
        pair x y => y
    end.
Notation "( x , y )" := (pair x y).

Theorem subjective_pairing : forall n m : nat,
(n,m) = (fst (n,m), snd (n,m)).
Proof.
    simpl. reflexivity. Qed.

Theorem subjective_pairing_2 : forall p: natprod,
    p = (fst p, snd p).
Proof.
    intros.
    destruct p.
    rewrite <- subjective_pairing.
    reflexivity.
    Qed.


Inductive natlist : Type :=
| nil
| cons (n: nat) (l: natlist).

Definition mylist := cons 1 (cons 2 ( cons 3 nil)).


Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := cons(x .. (cons y nil) ..).

Fixpoint repeat( n count : nat) : natlist :=
match count with 
|0 => nil
| S c' => n :: (repeat n c')
end.

Fixpoint length (l: natlist) : nat :=
match l with
    | nil => 0
    | cons n l' => S (length l')
end.

Fixpoint app(l1 l2 : natlist) : natlist:=
match l1 with
    | nil => l2
    | cons n l1' => cons n (app l1' l2)
end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Theorem nil_app : forall l:natlist,
    [] ++ l = l.
Proof.
    intros l.
    simpl.
    reflexivity.
    Qed.



Theorem nil_app_2 : forall l:natlist,
    l ++ [] = l.
Proof.
    intros l.
    induction l as [| n' l' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
    Qed.

Theorem app_assoc : forall l1 l2 l3:natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros.
    induction l1.
    - simpl. reflexivity.
    - simpl. rewrite IHl1. reflexivity.
Qed.


Fixpoint rev(l:natlist) : natlist :=
match l with
| nil => nil
| cons n l' => (rev l') ++ (cons n nil)
end.

Compute (rev (cons 1 (cons 2 (cons 3 nil)))).

Theorem app_length : forall l1 l2 : natlist,
length (l1 ++ l2) = length (l1) + length (l2).
Proof.
    intros.
    induction l1.
    - simpl. reflexivity. 
    - simpl. rewrite IHl1. reflexivity.
Qed. 


Theorem S_l_1 : forall l : natlist,
    length l + 1 = S (length l).
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite app_length. rewrite IHl. simpl. rewrite S_l_1. reflexivity.
Qed.


