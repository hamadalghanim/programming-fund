From Coq Require Import Strings.String.

(* 
(* MAP LECTURE *)
 *)
(* define total map A type *)

(* ([1->2; 2-> 3] *)

Definition total_map (A: Type) : Type :=
string -> A.

Definition t_empty {A: Type} (default:A) :
 total_map A:= 
 fun(x:string) => default.
Check @t_empty.
 Check (t_empty 0).
Definition map_1 := (t_empty 0).

Compute map_1 "hello"%string.

Definition t_update {A: Type} (m: total_map A)
    (k: string)(v: A) : total_map A:=
    (* let curr_val := m k in  (just as how it works)*)
    fun (x:string) => if(x=?k)%string then v else m x.

Definition a := t_update map_1 "hello"%string 1.


Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Definition map1' := _ !-> 0.

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition map2 := "hello" !-> 1; "world" !-> 420 ; _ !-> 0.
(* This is like
    map2 := t_update (t_update (t_empty 0) "hello" 1) "world" 420
 *)

Compute map2 "world"%string.
Print map2.

Lemma t_apply_empty : forall (A : Type) (m: total_map A) (x: string) (v: A),
    (_ !-> v) x = v.
Proof.
    intros.
    unfold t_empty.
    reflexivity.
Qed.



Lemma t_update_eq : forall (A : Type) (m: total_map A) x v,
    (x !-> v; m) x = v.
Proof.
    intros.
    unfold t_update.
    rewrite -> String.eqb_refl.

    reflexivity.

Qed.

From Coq Require Import Logic.FunctionalExtensionality.
(* basically to allow us to prove two functions are the same
and we can prove that by saying they are equal if all inputs map to the 
same output in the same function *)
(* https://coq.inria.fr/doc/v8.9/stdlib/Coq.Logic.FunctionalExtensionality.html *)
Theorem t_update_same : forall (A: Type) (m: total_map A) x,
    (x !-> m x; m) = m.
Proof.
    intros.
    apply functional_extensionality. (* Apply is usually used for implications, using rewrite doesn't work *)
    intros. (* this is to basically now we can atleast match x0 to x and prove this*)
    unfold t_update.
    destruct (x0 =? x)%string eqn:E. (* we can use eqb_spec *)
     + apply String.eqb_eq in E.
       rewrite -> E.
       reflexivity.
    + reflexivity.
    Qed.



     
Theorem t_update_same_2 : forall (A: Type) (m: total_map A) x,
    (x !-> m x; m) = m.
Proof.
    intros.
    apply functional_extensionality. (* Apply is usually used for implications, using rewrite doesn't work *)
    intros. (* this is to basically now we can atleast match x0 to x and prove this*)
    unfold t_update.
    destruct String.eqb_spec with (s1:=x0)(s2:=x).
    - intros. rewrite -> e. reflexivity.
    - reflexivity.
Qed.

(* Logic *)
Example and_example: 3+4 = 7 /\ 2*2 = 4.
Proof.
    split. (* only works on conjuctions *)
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma and_example2: forall (n m:nat),
    n=0 /\ m=0 -> n+m =0.
Proof.
    intros.
    destruct H as [H1 H2].
    rewrite H1;
    rewrite H2;
    simpl;
    reflexivity.
Qed.

Lemma or_intro_1: forall A B : Prop,
A -> A \/ B.
Proof.
    intros.
    left.
    apply H.
Qed.
