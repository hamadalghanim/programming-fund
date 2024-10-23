

Inductive ev: nat -> Prop :=
    | ev_0: ev 0
    | ev_SS: forall n:nat, ev n -> ev(S (S n)).

Check ev_SS.
Check 2:nat.

(* 
    This can be read "ev_SS is a constructor that takes two
    arguments, a natural number n and evidence that n is even"



    *Curry–Howard correspondence*
 *)
 (* mentioned in the file https://github.com/coq-contribs/firing-squad/blob/master/bib.v *)
Definition ev_4_po: ev 4 :=
    ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_4 : ev 4.
Proof.
    apply ev_SS.
    apply ev_SS.
    apply ev_0.
Qed.
Print ev_4.
Print ev_4_po.


Theorem ev_plus4 : forall n, ev n -> ev (4+n).
Proof.
    intros n H. simpl.
    apply ev_SS.
    apply ev_SS.
    apply H.
Qed.

Theorem ev_plus_m : forall n m, ev n -> ev m -> ev (m+n).
Proof.
    intros n m H1 H2.
    induction H2.
    - simpl. apply H1.
    - simpl. apply ev_SS. apply IHev.
Qed.

From Coq Require Import Arith.
Definition is_even : nat -> bool :=
    fun n => n mod 2 =? 0.

Check ev_plus4.
Print ev_plus4.

Definition intersting_fun (H: ev 4) : ev 8 :=
    ev_plus4 4 H.
Print intersting_fun.
Check intersting_fun (ev_SS 2 (ev_SS 0 ev_0)).
Check intersting_fun ev_4.



(* ------------------------------------------------------------ *)
(* 
    "one man's code is another man's data" - Alan Perlis
*)
(* 
    In this chapter we will define a language called Imp, which is a simple imperative language
    https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
*)
(* 
Z := X;
Y := 1;
while Z ≠ 0 do
    Y := Y × Z;
    Z := Z - 1
end

 *)

 (* 
    Heres a conventional BNF (Backus-Naur Form) grammar defining
    https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
    a: nat 
       | a + a
       | a - a
       | a * a

    b: true
       | false
       | a = a
       | a <= a
       | b && b
       | b || b
       | ~b
  *)

Module AExp.

(* These two definitions specify the _abstarct syntax tree_ for arithmetic expressions *)
Inductive aexp : Type :=
    | ANum (n : nat)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).

(* (1*2)+3 ---> concrete syntax *)
(* APlus (AMult (ANum 1) (ANum 2)) (ANum 3) ---> abstract syntax *)
Inductive bexp: Type :=
    | BTrue
    | BFalse
    | BEq (a1 a2 : aexp)
    | BLe (a1 a2 : aexp)
    | BNot (b : bexp)
    | BAnd (b1 b2 : bexp)
    | BOr (b1 b2 : bexp).


(* 
    ~(1+2 = 6-3)
    BNot(
        BEq 
            (APlus (ANum 1) (ANum 2))
            (AMinus (ANum 6) (ANum 3)
        )
    )
 *)


Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.
Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => (beval b1) && (beval b2)
    | BOr b1 b2 => (beval b1) && (beval b2)
    end.

(* 2+2 = 4 *)
Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Example test_beval1:
    beval (BEq (ANum 2) (ANum 2)) = true.
Proof. reflexivity. Qed.

(* we want to rewrite 0 + e to e *)
Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum n => a
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 (ANum 0) => optimize_0plus e1
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2) (APlus (ANum 0)( ANum 1))) = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.


(* Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. destruct a2 eqn:Ea2.
        -- simpl. apply IHa2.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed. *)



(* 
    defining the operations inductively

        n=m
     ---------- [E_aNum]
      ANum n ==> m

        e1 ==> n1   e2==>=> n2
    ----------------------------- [E_aPlus]
     aPlus e1 e2 ==> n1 + n2

        e1 ==> n1   e2 ==> n2
    ----------------------------- [E_aMinus]
     aMinus e1 e2 ==> n1 - n2

        e1 ==> n1   e2 ==> n2
    ----------------------------- [E_aMult]
     aMult e1 e2 ==> n1 * n2
 *)


Reserved Notation "e '==>' n" (at level 90, left associativity).


Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    +  (* E_APlus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* 
https://www.cs.princeton.edu/courses/archive/spring21/cos510/sf/lf/Imp.v

-> this diraction is soundness
<- this direction is completeness

 *)