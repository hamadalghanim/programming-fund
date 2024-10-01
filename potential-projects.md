# Potential Course Projects

## Rust

1. Formalize the core features (Calculus) of Rust Language, including its type and borrow checker.
2. Prove Type and Borrow Safety theorem
3. Extend it to concurrency and prove the absence of data races
4. RefL Pearce, A lightweight formalism for Ref lifetimes and borrowing in Rust TOPLAS'21

## Liquid Types

<!-- https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf -->

1. Embed "liquid types" (Rondon et ak PLDI'08)
2. Denibstrare deep and shallow embeddings
3. Write LTac-based proof automation scripts that automate (most of) liquid type checking.
4. Bonus: extend the type system to handle "structural relations" (Kaki et al '14)

## Distributed Protocol Verification

1. Formalize models of well-known distributed protocols in Coq.
   - One-shot leader election.
   - Leader elections in a ring, and
   - Paxos.
2. In each case verify that the safety property:
   - Leader, if any, is unique.
   - No Tow nodes make different decisions.
3. Write LTac-based proof automations scripts that partially automate verification

## C-lite to JVM Byte Code
1. Formmalize lightweight C language (with variables, pointers, assignments, while loop, and function calls) in Coq. Define its operationsl semantics.
2. Formalize an equivalent subtset of JVM instructions and define its operational semantics.
3. write a "compiler" from C-lite to JVM. Prove its correctness by showing the observational equivalence (bi-simulation) of source (C-lite) and target programs (JVM).
