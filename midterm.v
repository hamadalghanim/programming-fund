Check fun x => x+1.
Check if true then False else True.
Check True.
Check true.

Inductive ev : nat -> Prop := 
    | ev_0 : ev 0
    | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Check (fun n (H:ev n) => Nat.div n 2).
(* can be n -> ev n -> nat *)

Check fun (X:Type) (Y:Type) (f: X -> Y) (x:X) => f x.
(* X:Type -> Y:Type -> (X -> Y) -> X -> Y *)

From Coq Require Import List.


(* 

    In x l
    means that x belongs to l
        l=x::t
        ------- [x_head]
        x ∈ l


        l=h::t      x ∈ t
        ------------------ [x_tail]
                x ∈ l

 *)
Inductive In {A:Type} : A -> list A -> Prop :=
    | x_head: forall(x:A)(l t: list A), (l = x::t) -> In x l
    | x_tail: forall(x h :A)(l t: list A), (l = h::t) -> In x t -> In x l.


Import ListNotations.
Example in_ex: In 3 [1;2;3;4].
Proof.
    apply x_tail with (h:=1)(t:=[2;3;4]). reflexivity.
    apply x_tail with (h:=2)(t:=[3;4]). reflexivity.
    apply x_head with (t:=[4]). reflexivity.
Qed.



(* 
    Ord x y l is valid iff x is ordered before y in l


    l=x::t     y ∈ t
    ---------------- [x_y_head]
        ord x y l


    l=h::t     ord x y t
    -------------------- [x_y_tail]
        ord x y l

 *)

Inductive Ord {A:Type}: A -> A -> list A -> Prop :=
| x_y_head: forall(x y:A)(l t: list A), (l = x::t) -> In y t -> Ord x y l
| x_y_tail: forall(x y h:A)(l t: list A), (l = h::t) -> Ord x y t -> Ord x y l.




Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E. inversion E. inversion H0. inversion H2.  Qed.




(** 
A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove that
       forall l, pal (l ++ rev l).
    - Prove that
       forall l, pal l -> l = rev l.

*)
Inductive pal {X : Type} : (list X) -> Prop :=
| l_empty: forall(l: list X), l=nil -> pal l
| l_one: forall(a:X)(l: list X), l= a::nil -> pal l
| l_other: forall(a:X)(l_x: list X), pal l_x -> pal (a :: l_x ++ [a]).

Check [1].

Check  pal [1;2;3;4;3].



(* 
            P
    -------------
        P /\ Q

        Q
    -------------
        P /\ Q

 *)

Inductive or (P Q : Prop) : Prop :=
|l_or: P ->   or P Q
|r_or: Q -> or P Q.


(* 

    P      Q
    ---------
      P /\ Q
 *)

Inductive and (P Q : Prop) : Prop :=
| and_one: P -> Q ->  and P Q.





Inductive tree (V : Type ) : Type :=
| E
| T (l : tree V) (v : V) (r : tree V ).


Arguments E {V }.
Arguments T {V }.
Example ex_tree : tree nat :=
(T (T E 1 E) 2 (T E 1 E )).

Print ex_tree.

(* 


 *)
Inductive is_empty {V : Type } : tree V -> Prop :=
| t_empty_1: forall (t: tree V), t=E -> is_empty t.


(* 
(4 points) A prefix of a list is a sub-list that occurs at the beginning of a larger list. For
example, these are all the prefixes of [1;2;3] (i.e., all the lists s such that 


prefix s [1;2;3]):
[]
[1]
[1;2]
[1;2;3]


Complete the following inductive definition so that prefix s l is provable exactly when s is
a prefix of l.
Inductive prefix {X : Type} : list X -> list X -> Prop :



 s         l
[1;2]  [1;2;3] (pre_head) 
[2]     [2;3]  (pre_head)
[]       [3]    (pre_empty)
Qed.
  
 
 
            s=[]
    ----------------- [pre_empty]
        prefix s l

    s=h1::t1 l=h2::t2 h1=h2 prefix t1 t2
    ---------------------------------- [pre_head]
        prefix s l
 *)

Inductive prefix {X : Type} : list X -> list X -> Prop :=
|pre_empty: forall(s l: list X),  (s=[]) -> prefix s l
|pre_head: forall(t1 t2: list X)(h :X), prefix t1 t2 ->  prefix (h::t1) (h::t2).


Theorem pre_1: prefix [1;2] [1;2;3].
Proof.
    apply pre_head.
    apply pre_head.
    apply pre_empty.
    reflexivity.
Qed.


(* 
        n = 1
    ----------------
        odd n

       n>2 odd n - 2
    -------------------
        odd n
*)

Inductive odd_n: nat -> Prop :=
| n_one: forall(n:nat), n=1 -> odd_n n
| n_greater_than_2: forall(n:nat), odd_n (n-2) -> odd_n n.

Theorem threeisodd: odd_n 3.
Proof.
    apply n_greater_than_2.
    apply n_one. reflexivity.
Qed.
Require Import Lia.

Theorem test: forall (n:nat), odd_n (1+2*n).
Proof.
    intros n. induction n. simpl. apply n_one. reflexivity.
    simpl. repeat rewrite plus_n_Sm. apply n_greater_than_2.
    assert(H: n + (n + 3) - 2 = 1+2*n).
    - lia.
    - rewrite H. apply IHn.
    Qed.