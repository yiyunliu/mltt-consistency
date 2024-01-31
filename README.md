# Mechanized consistency proof for MLTT
This repository contains a very short consistency proof of Martin-Löf
type theory in Coq (< 1000 LoC excluding code produced by autosubst2). You need
[Autosubst2](https://github.com/uds-psl/autosubst2) (only if
you plan to change [syntax.sig](syntax.sig)),
[stdpp](https://gitlab.mpi-sws.org/iris/stdpp), and
[CoqHammer](https://github.com/lukaszcz/coqhammer) to build the
project. The repository is known to compile with Coq 8.18.0. It
won't compile with earlier versions because I'm using a feature
related to universe unification that wasn't introduced until
8.18.0. If you annotate terms whose type involves `Prop`, then you
might be able to compile the code with an older Coq version.

The semantic interpretation is adapted from <https://dl.acm.org/doi/10.1145/3167091> but greatly simplified to present the technique of leveraging impredicativity to replace induction-recursion in its purest form. The system in this repo also has a universe hierarchy and therefore does not require duplicating the interpretation of small and big universes.

## Language specification
The syntactic typing rules can be found in [typing.v](typing.v). You
can also find a pdf rendering of the grammar, statics, and dynamics of
the system in [paper/spec-out.pdf](paper/spec-out.pdf). I'll try to
keep the latter as up-to-date to the actual Coq development as
possible. If you find any discrepancies, feel free to create a github
issue.

The equality is untyped because I like being able to derive
$\Pi$-injectivity early on through syntactic means.

There are various ways to present the rules of a dependent type
theory. I used the typing rules from [Coq's official documentation](https://coq.inria.fr/refman/language/cic.html) as my
reference when designing the syntactic typing rules.

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

## Axioms
Both syntactic and semantic soundness proofs rely on functional
extensionality because it is required by the autosubst 2
infrastructure.

The semantic soundness proof additionally requires propositional
extensionality. Propositional extensionality is not neccesssary, but
it makes automation more tractable.
f
The repository is otherwise free of axioms. Notably, manual
generalization is favored over the `dependent induction` tactic to avoid
reliance on axioms related to proof irrelevance.

## Todos
Some of the features below are orthogonal and therefore can be
developed independently from each other (e.g. strong normalization and
existentials).

- [x] Infinite universe hierarchy
- [x] Identity types
- [ ] Existentials
- [ ] Alternative system with typed conversion and additional eta
	  rules
- [x] Existence of normal form for open terms
- [ ] Extensional model (see the `per` branch)
- [ ] Impredicative `Prop`
- [ ] Proof irrelevance (see the `dcoi` branch)
