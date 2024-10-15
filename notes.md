# Lecure 3

## Previous lecture futher reading:

[natural deduction for propositional logic](https://leanprover.github.io/logic_and_proof_lean3/natural_deduction_for_propositional_logic.html)

## Coq Syntax

`Inductive` is when you want to define a type like an enum

`Definition` is used when defining a function
`Fixpoint` defines a function that uses recursive definition and it will reach an endpoint

`Lemma`/`Example` used when we want to start a proof

`Proof` i stated when we want to specify the proof types such as:

- `simpl.` simplify the term
- `reflexivity.` checks if lhs = rhs, sometimes it will simplify and try to unfold the term
- `Qed.` ending the proof

for more info we can check this [cheat sheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html)

futher reading [paper by per martin lof](https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf)
