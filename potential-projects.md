# Potential Course Projects

## Rust

1. Formalize the core features (Calculus) of Rust Language, including its type and borrow checker.
2. Prove Type and Borrow Safety theorem
3. Extend it to concurrency and prove the absence of data races
4. RefL Pearce, A lightweight formalism for Ref lifetimes and borrowing in Rust TOPLAS'21
   [paper](https://dl.acm.org/doi/10.1145/3443420)

## Liquid Types

[paper link](https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf)

1. Embed "liquid types" (Rondon et ak PLDI'08)
2. Denitrate deep and shallow embeddings
3. Write LTac-based proof automation scripts that automate (most of) liquid type checking.
4. Bonus: extend the type system to handle "structural relations" (Kaki et al '14)

## Distributed Protocol Verification

1. Formalize models of well-known distributed protocols in Coq.
   - One-shot leader election.
   - Leader elections in a ring, and
   - Paxos.
2. In each case verify that the safety property:
   - Leader, if any, is unique.
   - No Two nodes make different decisions.
3. Write LTac-based proof automation scripts that partially automate verification
   [https://https://medium.com/the-sixt-india-blog/raft-and-paxos-a-brief-introduction-to-the-basic-consensus-protocols-powering-distributed-systems-1a0ef7ca3acb](https://medium.com/the-sixt-india-blog/raft-and-paxos-a-brief-introduction-to-the-basic-consensus-protocols-powering-distributed-systems-1a0ef7ca3acb)

   [https://news.ycombinator.com/item?id=10017549](https://news.ycombinator.com/item?id=10017549)

   [https://arxiv.org/pdf/1606.01387](https://arxiv.org/pdf/1606.01387)

## C-lite to JVM Byte Code

1. Formalize lightweight C language (with variables, pointers, assignments, while loop, and function calls) in Coq. Define its operational semantics.
2. Formalize an equivalent subset of JVM instructions and define its operational semantics.
3. write a "compiler" from C-lite to JVM. Prove its correctness by showing the observational equivalence [(bi-simulation)](https://en.wikipedia.org/wiki/Bisimulation) of source (C-lite) and target programs (JVM).

[https://xavierleroy.org/publi/bytecode-verification-JAR.pdf](https://xavierleroy.org/publi/bytecode-verification-JAR.pdf)
[https://bentnib.org/coqjvm.pdf](https://bentnib.org/coqjvm.pdf)
