Require Import Unicode.Utf8.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Notation "¬ x" := (negb x).

Example negb_involutive : (¬ (¬ true)) = true.
Proof.
  - simpl. reflexivity. Qed.

Example negb_test : (¬ false) = true.
Proof.
  - simpl. reflexivity. Qed.


Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb)
  | custom (r g b : nat).

Definition make_custom_color (r g b : nat) : color :=
  custom (min r 255) (min g 255) (min b 255).


Definition orange := make_custom_color 255 165 0.

(* Function to check if a color is a primary color *)
Definition is_primary (c : color) : bool :=
  match c with
  | primary _ => true
  | _ => false
  end.

(* Function to extract RGB values from any color *)
Definition extract_rgb (c : color) : nat * nat * nat :=
  match c with
  | black => (0, 0, 0)
  | white => (255, 255, 255)
  | primary red => (255, 0, 0)
  | primary green => (0, 255, 0)
  | primary blue => (0, 0, 255)
  | custom r g b => (r, g, b)
  end.

Check (primary red).
Check primary.
(* Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end. *)