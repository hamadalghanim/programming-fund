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
(* 
Notation "x :: l" := (cons _ x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons _ x .. (cons _ y (nil _)) ..).

Check [1;2;3]. *)

(* 

  Continuned on lecture 5
 *)

 (* We can do the type inference such as *)

Arguments nil {A}.
Arguments cons {A}.


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y (nil)) ..).

Check [1;2;3].
Check 1::2::1::2::3::[].

(* using {A: Type} instead of (A: Type) it will infer it *)
Fixpoint append {A: Type}(l1: List A)(l2: List A) : List A :=
match l1 with
| [] => l2
| x::xs => x::(append xs l2)
end.


Notation "x ++ y" := (append x y).
Compute ([11;22;33] ++  [55;33;66]).


Theorem app_is_associative: forall (X: Type) (l1 l2 l3: List X),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof. intros.
  induction l1 as [| x xs IHxs]. (* Ihn is inductive hypothsis introduced *)
    - simpl. reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed.

Inductive prod (X:Type)(Y:Type):=
  | pair (x:X)(y:Y).

Arguments pair {X}{Y}.

Notation "( x , y )" := (pair x y)(at level 60).

Notation "X * Y" := (prod X Y) : type_scope.

Definition simple_pair: nat * bool := (1, true).
Check simple_pair.
Compute simple_pair.

Inductive optional(A: Type) : Type :=
 | none
 | some(v: A).

Arguments some {A}.
Arguments none {A}.
Fixpoint lookup_non_zero (l : List nat) : optional nat :=
  match l with
  | [] => none  (* Specify the type nat for none *)
  | cons (S x) xs => some (S x)
  | cons 0 xs => lookup_non_zero xs
  end.
(* lookup : map k v -> k -> optional v *)
Definition doit3times {X: Type } (f: X -> X) (x:X) :
X := f(f(f x)).

Check doit3times.
Check @doit3times.

Definition minus_two(x:nat): nat := x-2.

Compute doit3times minus_two 9.

Definition square (x: nat) : nat := x*x.

Compute doit3times square 2.


(* lets do anonymous functions *)

Fixpoint filter {A: Type}(l1: List A)(f : A-> bool): List A :=
  match l1 with 
  | [] => []
  | cons x xs => if f x then
                   cons x (filter xs f)
                  else filter xs f
  end.
