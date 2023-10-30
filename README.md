# Mechanized consistency proof for MLTT
This repository contains a very short consistency proof of Martin-Löf type theory in Coq. You need [Autosubst2](https://github.com/uds-psl/autosubst2) and [CoqHammer](https://github.com/lukaszcz/coqhammer) to build the project. The repository is known to compile with Coq 8.16.

The semantic interpretation is adapted from <https://dl.acm.org/doi/10.1145/3167091> but greatly simplified to present the technique of leveraging impredicativity to replace induction-recursion in its purest form. The system in this repo also has an infinite universe hierarchy and therefore does not require duplicating the interpretation for small and big universes.

## Language specification
The syntactic typing rules can be found in [typing.v](typing.v).

The equality is untyped because I like being able to derive $\Pi$-injectivity early on through syntactic means.

## Build
Simply run the following command:
```sh
make
```
