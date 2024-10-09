From Coq Require Import List.
Import ListNotations.
(* 
Theorem p_q_rational: Exists irrational numbers P Q s.t p^Q is a rational number
Proof.
    Let P = Q = √2.
    Consider R = (√2)^(√2).
    Two cases:
    * Case 1: R is rational.
        P = Q = √2. Done.
    * Case 2: R is irrational.
        Consider R^√2 = (√2)^(√2)^^√2 = (√2)^2 = 2.
Qed.
 *)

(* 
    compute_prime_factors: {y: int} -> {x: list nat | 
                                        every x[i] is primate /\
                                        y =  ∏x[i] /\ x != [] }
    
    Theorem prime_factors_exists: forall y:nat, exists l: list nat,
    ~(l = []) /\  every x[i] is primate /\ y =  ∏x[i] /\ x != []
 *)
(* 
    Algorithms are computational content for proofs.
 *)




Definition law_of_excluded_middle: Prop := forall (P:Prop), P \/ ~P.
(* 
we cannot prove this,
basically we cannot go through cases to prove something
*)


(* Theorem lem: law_of_excluded_middle.
Proof.
    unfold law_of_excluded_middle.
    intros.
    admit.
Admitted. *)


Inductive ev: nat -> Prop :=
    | ev_0: ev 0
    | ev_SS: forall n:nat, ev n -> ev(S (S n)).

Check ev_0.
Check ev_SS.

Definition nat_add(x:nat)(y:nat) : nat := x+y.

Check nat_add.

(* 
    ev_SS: (n : nat) -> ev n -> ev(S(S n))
    (ev_SS 4): ev 4 -> ev(S(S 4))
    Curry–Howard correspondence

*)
Check ev 4.
Theorem ev_4 : ev 4.
Proof.
    apply ev_SS.
    Show Proof.
    apply ev_SS.
    Show Proof.
    apply ev_0. 
    Show Proof.
Qed.
Theorem ev_plus4 : forall n, ev n -> ev (4+n).
Proof.
    intros n H. simpl.
    apply ev_SS.
    apply ev_SS.
    apply H.
Qed.

Definition my_list2: list nat.
apply []. Show Proof. Qed.

Definition ev_4' : ev 4 := (ev_SS 2 (ev_SS 0 ev_0)).
