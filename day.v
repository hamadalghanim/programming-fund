(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* New is_weekend function *)
Definition is_weekend (d:day) : bool :=
  match d with
  | saturday => true
  | sunday => true
  | _ => false
  end.

 Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Example test_weekend_saturday:
  (is_weekend saturday) = true.

Example test_weekend_monday:
  (is_weekend monday) = false.

 Proof. simpl. reflexivity. Qed.
