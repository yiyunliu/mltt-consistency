# Mechanized consistency proof for MLTT
This repository contains a very short consistency&normalization proof of Martin-Löf
type theory in Coq (~ 1000 LoC excluding code produced by autosubst2). You need
[Autosubst2](https://github.com/uds-psl/autosubst2) (only if
you plan to change [syntax.sig](syntax.sig)),
[stdpp](https://gitlab.mpi-sws.org/iris/stdpp), [Coq-Equations](https://github.com/mattam82/Coq-Equations),
and [CoqHammer](https://github.com/lukaszcz/coqhammer) to build the
project.

The repository is known to compile with Coq 8.18.0. It
won't compile with earlier versions because I'm using a feature
related to universe unification that wasn't introduced until
8.18.0. If you annotate terms whose type involves `Prop`, then you
might be able to compile the code with an older Coq version.

The semantic interpretation is heavily inspired by
<https://dl.acm.org/doi/10.1145/3167091>. However, we leverage
impredicativity to define a countable universe hierarchy, rather than
defining a single predicative universe, where impredicativity turns
out to be unnecessary (see <https://dl.acm.org/doi/10.1145/3636501.3636951>).

## Language specification
The syntactic typing rules can be found in [typing.v](theories/PCCOmega/typing.v).

In short, the system is most similar to the predicative part of
$CC^\omega$, which is notable for its untyped conversion rule and
cumulativity.
We add extensions such as an intensional identity type, a
boolean base type, and a Void type.

Our subtyping relation is contravariant on the argument, unlike
$CC^\omega$ or Coq. The semantic model is enough to justify this more
flexible design.

The $\eta$-law for functions is supported (see the `eta` branch),
though it's not yet merged to the main branch because we need some
minor clean-ups.

## Install dependencies
The [opam.switch](opam.switch) file allows you to recreate an opam
switch that is identical to our environment. To create a switch named `mltt`, run the following command when you have [opam.switch](opam.switch) available in your working directory:
```
opam update
opam switch import opam.switch --switch mltt --repositories=coq-released=https://coq.inria.fr/opam/released,default=https://opam.ocaml.org
```

## Build
Simply run the following command:
```sh
make
```
You can pass the `-j[PROC]` flag to speed up the compilation by
spawning multiple `Coq` processes at the same time to validate the
files. Replace `[PROC]` with a positive integer that represents the
number of processes you want to spawn, though you might want to lower
that number to reduce the memory consumption.

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
- [syntax.sig](syntax.sig): Syntax specification written in
higher-order abstract syntax. Used by the `as2-exe` executable to
produce the Coq syntax file [syntax.v](theories/Autosubst2/syntax.v)
- [theories/Autosubst2](theories/Autosubst2): Header files/auto-generated syntax file from/by Autosubst 2
- [join.v](theories/PCCOmega/join.v): Reduction and subtyping
- [typing.v](theories/PCCOmega/typing.v): Syntactic typing rules
- [normalform.v](theories/PCCOmega/normalform.v): Properties related
  to normal and neutral terms
- [semtyping.v](theories/PCCOmega/semtyping.v): Definition of the
  logical relation and its properties
- [soundness.v](theories/PCCOmega/soundness.v): Semantic typing,
  semantic soundness (i.e. the fundamental theorem), normalizaiton,
  and consistency
