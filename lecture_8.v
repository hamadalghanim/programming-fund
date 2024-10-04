Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
    intros.
    split.
    - destruct H. assumption.
    - destruct H. assumption.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.



(* From LF Require Export Logic. *)
From Coq Require Export Lia.

Fixpoint is_even (n:nat) : bool :=
    match n with
    | 0 => true
    | 1 => false
    | S(S n') => is_even n'
    end.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
    unfold Even.
    exists 2.
    reflexivity.
Qed.
Definition Even2 x:= is_even x = true.

Print Even2.


(* 
    ev n : natural number n is even

        -               ev n
    ------- [ev_0]       --------------- [ev_ss]
      ev 0          ev (S (S n))
 *)
 (*

        ------------ [ev_0]
             ev 0
        ---------- [ev_ss]
            ev 2
        --------- [ev_ss]
          ev 4
  *)

Inductive ev: nat -> Prop :=
    | ev_0: ev 0
    | ev_SS: forall n:nat, ev n -> ev(S (S n)).

Theorem ev_4 : ev 4.
Proof.
    intros.
    repeat apply ev_SS.
    apply ev_0. 
Qed.

Print ev_ind.


Theorem ev_inversion :
    forall (n: nat), ev n -> 
        (n=0) \/ (exists n', n = S( S n') /\ ev n').
Proof.
    intros n H.
    destruct H.
    + left. reflexivity.
    + right. exists n. split.
        - reflexivity.
        - assumption.
Qed. 

Theorem ev_double : 
    forall (n:nat), ev n -> ev (double n).
Proof.
    intros n H.
    induction H as [| n' Hn IHn].
        + simpl. apply ev_0.
        + simpl. repeat apply ev_SS. assumption.
Qed.  


