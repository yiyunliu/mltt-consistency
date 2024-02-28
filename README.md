# Mechanized consistency proof for MLTT
This repository contains a very short consistency proof of Martin-Löf
type theory in Coq (< 1000 LoC excluding code produced by autosubst2). You need
[Autosubst2](https://github.com/uds-psl/autosubst2) (only if
you plan to change [syntax.sig](syntax.sig)),
[stdpp](https://gitlab.mpi-sws.org/iris/stdpp), and
[CoqHammer](https://github.com/lukaszcz/coqhammer) to build the
project. 

The repository is known to compile with Coq 8.18.0. It
won't compile with earlier versions because I'm using a feature
related to universe unification that wasn't introduced until
8.18.0. If you annotate terms whose type involves `Prop`, then you
might be able to compile the code with an older Coq version.

The semantic interpretation is adapted from
<https://dl.acm.org/doi/10.1145/3167091> but greatly simplified to present the
technique of leveraging impredicativity to replace induction-recursion in its
purest form. The system in this repo also has a universe hierarchy and
therefore does not require duplicating the interpretation of small and big
universes.

## Language specification
The syntactic typing rules can be found in [typing.v](typing.v). You
can also find a pdf rendering of the grammar, statics, and dynamics of
the system in [paper/spec-out.pdf](paper/spec-out.pdf). I'll try to
keep the latter as up-to-date to the actual Coq development as
possible. If you find any discrepancies, feel free to create a github
issue.

## Install dependencies
The [opam.switch](opam.switch) file allows you to recreate an opam switch that is identical to the one I use on my machine. To create a switch named `mltt`, run the following command when you have [opam.switch](opam.switch) available in your working directory:
```
opam switch import opam.switch --switch mltt --repositories=coq-released=https://coq.inria.fr/opam/released,default=https://opam.ocaml.org
```

## Build
Simply run the following command:
```sh
make
```

## Axioms
Both syntactic and semantic soundness proofs rely on functional
extensionality because it is required by the Autosubst 2
infrastructure.

The semantic soundness proof additionally requires propositional
extensionality. Propositional extensionality is not neccesssary, but
it makes automation more tractable.

The repository is otherwise free of axioms. Notably, manual
generalization is favored over the `dependent induction` tactic to avoid
reliance on axioms related to proof irrelevance.


## Contents 

```
  axioms.v   - funext, from autosubst library
  imports.v  - library dependencies

* Section 2
  syntax.v   - Fig 1. generated by autosubst
  unscoped.v - autosubst library
  join.v     - Fig 2. parallel reduction and its properties
  typing.v   - Fig 3. specification of the type system

* Section 3 
  semtyping.v - Fig 4. definition of logical relation
  soundness.v - semantic typing, semantic soundness, consistency

* Section 4 
  normalform.v     - normal and neutral terms, antirenaming lemma
  semtypingopen.v  - logical relation for open terms
  soundnessopen.v  - soundness of open terms, normalizing

* Other
  syntactic_soundness.v - preservation & progress
```



## Todos
Some of the features below are orthogonal and therefore can be
developed independently from each other (e.g. strong normalization and
existentials).

- [x] Infinite universe hierarchy
- [x] Identity types
- [ ] Existentials
- [ ] Alternative system with typed conversion and additional eta
	  rules
- [ ] Strong normalization (through Kripke semantics)
- [ ] Extensional model (see the `per` branch)
- [ ] Impredicative `Prop`
- [ ] Proof irrelevance (see the `dcoi` branch)


