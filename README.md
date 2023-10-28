# Mechanized consistency proof for MLTT
This repository contains a very short consistency proof of Martin-Löf type theory in Coq. You need [Autosubst2](https://github.com/uds-psl/autosubst2) and [CoqHammer](https://github.com/lukaszcz/coqhammer) to build the project. The repository is known to compile with Coq 8.16.

The semantic interpretation is adapted from <https://dl.acm.org/doi/10.1145/3167091> but greatly simplified to present the technique of leveraging impredicativity to replace induction-recursion in its purest form.

## Language specification
The syntactic typing rules can be found in [typing.v](typing.v). The language only has one universe, but is expressive enough to do large elimination (see `large_elim_example` in [soundness.v](soundness.v)) through the boolean type (named as `Switch`, with `on` and `off` as inhabitants since `False` has been taken by the empty type).

I believe the same impredicativity technique can be generalized to handle an infinite universe hierarchy and may even remove the `*Type` and `*Univ` duplication found in [semtyping.v](semtyping.v).

## Build
Simply run the following command:
```sh
make
```
