Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-intuition-auto-with-star".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
Set Default Goal Selector "!".

(* from hoare 2 *)
Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _|- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

Ltac apply_hoare :=
    match goal with 
    | [ |- {{ _ }} if _ then _ else _ end {{ _ }} ] => apply hoare_if
    | [ |- {{ _  }} _ := _ {{ _ }} ] => apply hoare_asgn
    | [ |- {{ _  }} _ := _ {{ _ }} ] => eapply hoare_consequence_pre
    end.


Example if_example:
  {{ True }} 
    if (X=0)
    then Y := 2
    else Y := X + Y
    end
    {{ X <= Y }}.
Proof.
    repeat apply_hoare; verify_assertion.
Qed.

