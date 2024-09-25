From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
Import ListNotations.
Fixpoint filter {A: Type}(f : A-> bool)
    (l1: list A): list A :=
  match l1 with 
  | [] => []
  | x::xs => if f x then
                   x::(filter f xs)
                  else filter f xs
  end.

Definition list1 : list nat := [1;2;3;4;4].

Definition isEven(x:nat):bool :=
x mod 2 =? 0.

Compute filter isEven list1.
Compute filter (fun (x:nat) => x mod 2 =? 1) list1. 
(* anonymous functions *)

Fixpoint fold_left {A: Type}(l1: list A)(bin_op : A -> A -> A)(acc: A)
    : A :=
    match l1 with
    | []=> acc
    | x::xs => fold_left xs bin_op (bin_op acc x)
    end.


Compute fold_left [1;2;3;4;5] (fun (acc val: nat ) => acc + val) 0.
Compute fold_left [1;2;3;4;5] (fun (acc: nat )=> fun(val: nat) => acc + val) 0.



Definition add(x: nat)(y: nat) : nat := x+y.
Definition add'(x y: nat) : nat := x+y.
Check add.
Check add'.
(* currying *)
Compute add' _ 54.
Definition add'' := 
fun (p: nat * nat) => match p with
    | (x,y) => x+y
    end.
Check add''. (* here we send one argument which is a pair *)
Compute add'' (4,5).

Definition add_2: nat -> nat := add 2.
Compute add_2 3.
From Coq Require Import Strings.String.

Definition check_pwd: string -> bool:=
    let secret: string := "abracadabra"%string in 
    fun (usr_pwd: string) => (usr_pwd =? secret)%string.
Compute check_pwd.
Compute check_pwd "hello"%string.
Compute check_pwd "abracadabra"%string.

Definition better_check_pwd: string -> string -> bool:= fun(secret:string) =>
    fun (usr_pwd: string) => (usr_pwd =? secret)%string.

Definition check_hello := better_check_pwd "Hello"%string.

Compute check_hello "hey".

(* define total map A type *)

(* ([1->2; 2-> 3] *)

Definition total_map (A: Type) : Type :=
string -> A.

Definition t_empty {A: Type} (default:A) :
 total_map A:= 
 fun(x:string) => default.
Check @t_empty.
 Check (t_empty 0).
Definition nat_map := (t_empty 0).

Compute nat_map "hello"%string.

Definition t_update {A: Type} (m: total_map A)
    (k: string)(v: A) : total_map A:=
    (* let curr_val := m k in  (just as how it works)*)
    fun (x:string) => if(x=?k)%string then v else m x.



(* ["foo" !-> true; "bar" !-> true, _ !-> false] NEXT LECTURE*)