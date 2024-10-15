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
    | _tail: forall(x h:A)(l t: list A), (l = h::t) -> In x t -> In x l.


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