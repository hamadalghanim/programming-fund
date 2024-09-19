Require Import Lia.

Theorem hamad2: forall n m : nat,
n < m -> exists k : nat, m = n + k.
Proof.
    intros.
    exists (m - n).
    lia.
Qed.




Module ListPlayground.

(* 
  Real Numbers
  https://en.wikipedia.org/wiki/Cauchy_sequence
  https://en.wikipedia.org/wiki/Dedekind_cut
 *)


Inductive List(A : Type) : Type :=
  | nil : List A
  | cons : A -> List A -> List A.
Check List.
Check cons.

(* (List: nat). *)
Check cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Notation "x :: l" := (cons _ x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).





(* 

  Continuned on lecture 5
 *)