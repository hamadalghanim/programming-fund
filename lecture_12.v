(* import string *)
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
Open Scope string_scope.
From LF Require Import Maps.



(* define map *)
Definition total_map (A : Type) := string -> A.
Definition t_empty {A:Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A:Type} (m : total_map A) (x : string) (v : A) :=
    fun x' => if string_dec x x' then v else m x'.


Notation "x '!->' v" := (t_update (t_empty v) x v) (at level 100).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse maps from the [Maps] chapter, and
    [string]s will be used to represent variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from strings to [nat], and will use [0] as default value
    in the store. For more complex programming languages, the state
    might have more structure. *)

Definition state := total_map nat.
(* import maps *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  You do not need to understand
    exactly what these declarations do.  Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Coq to create a new
         "custom grammar" for parsing Imp expressions and
         programs. The first notation declaration after this tells Coq
         that anything between [<{] and [}>] should be parsed using
         the Imp grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.
Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.
Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.
(** One downside of these and notation tricks -- coercions in
    particular -- is that they can make it a little harder for humans
    to calculate the types of expressions.  If you ever find yourself
    confused, try doing [Set Printing Coercions] to see exactly what
    is going on. *)

Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
(* dunno why this doesnt work *)
Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (((aeval st) a1) =? (aeval st a2))
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.