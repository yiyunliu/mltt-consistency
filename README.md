# Mechanized consistency proof for MLTT
This repository contains a very short consistency proof of Martin-Löf type theory in Coq. You need [Autosubst2](https://github.com/uds-psl/autosubst2) (only needed if you plan to change [syntax.sig](syntax.sig)) and [CoqHammer](https://github.com/lukaszcz/coqhammer) to build the project. The repository is known to compile with Coq 8.17.1. Notably, it does not compile with Coq 8.16.1.

The semantic interpretation is adapted from <https://dl.acm.org/doi/10.1145/3167091> but greatly simplified to present the technique of leveraging impredicativity to replace induction-recursion in its purest form. The system in this repo also has a universe hierarchy and therefore does not require duplicating the interpretation of small and big universes.

## Language specification
The syntactic typing rules can be found in [typing.v](typing.v).

The equality is untyped because I like being able to derive $\Pi$-injectivity early on through syntactic means.

## Install dependencies
The [opam.switch](opam.switch) file allows you to recreate an opam switch that is identical to the one I use on my machine. To create a switch named `mltt`, run the following command when you have [opam.switch](opam.switch) available in your working directory:
```
opam switch import opam.swtich --switch mltt --repositories=coq-released=https://coq.inria.fr/opam/released,default=https://opam.ocaml.org
```

## Build
Simply run the following command:
```sh
make
```
