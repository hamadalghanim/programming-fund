Definition not(p: Prop) := p -> False.


Theorem ex_falso_quod_libet: forall (P:Prop), False -> P.
Proof.
    intros.
    destruct H.
Qed.


(* same as the one above *)
Theorem not_implies_our_not : forall (P: Prop),
    not P -> (forall (Q: Prop), P -> Q).
Proof.
    intros.
    unfold not in H.
    apply H in H0.
    destruct H0.
Qed.


Fixpoint double (n:nat) :=
    match n with 
    | 0 => 0
    | S(n') => S(S(double n'))
    end.

Theorem double_is_injective : forall (m n:nat), 
    double(n) = double(m) -> n = m.
Proof.
    intros m n. (* or we can not intro the variable we want to keep general *)
    generalize dependent m.
    (* 
     * induction on n
     * + base case: n = 0.
     * + inductive case:
         H0: n = S n'
         IH: (double n') = (double m) -> n' = m
         we need an m that scales with n
     *)
    induction n as [| n' IHn'].
    - intros m H. simpl in H.
      destruct m.
        + reflexivity.
        + discriminate.
    - intros m H. simpl in H. destruct m.
        + simpl in H. inversion H. (** discriminate *)
        + simpl in H. inversion H. (* injection H. intros H1. *)
            specialize IHn' with (m:=m). (* can be not used here *)
            apply IHn' in H1. rewrite H1. reflexivity.
Qed. 

Fixpoint is_even (n:nat): bool :=
    match n with 
    | 0 => true
    | S n' => is_odd(n')
    end
    with is_odd(n:nat):bool :=
        match n with
        | 0 => false
        | S n' => is_even(n')
        end.

(* this is to demonstrate *)
(* should be harder next lecture will discuss *)
Theorem is_even_bla: forall (n:nat),
    is_even(S (S n)) = true -> is_even n = true.
Proof.
    simpl. intros.
    exact H.
    Qed.