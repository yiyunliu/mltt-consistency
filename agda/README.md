# Mechanization of consistency

This is a mechanization of a minimal type theory with predicative universes.
It has been checked with Agda 2.7.0 using agda-stdlib 2.2.
The top-level file can be checked by `agda consistency.agda`.

## Type Theory

The object theory is a type theory with universes à la Russell,
dependent functions, an empty type, booleans, equality types, and untyped conversion.
The below is an overview of the typing and conversion rules with variable names,
although the mechanization uses de Bruijn indexing and simultaneous substitution.

```
                Γ ⊢ B : 𝒰 k
x : A ∈ Γ    Γ ⊢ a : A    A ≈ B       ⊢ Γ    j < k
---------    ------------------    -------------------
Γ ⊢ x : A        Γ ⊢ a : B         Γ ⊢ 𝒰 j : Γ ⊢ 𝒰 k

    Γ ⊢ A : 𝒰 k            Γ ⊢ Πx : A. B           Γ ⊢ b : Πx: A. B
Γ, x : A ⊢ B : 𝒰 k        Γ, x : A ⊢ b : B            Γ ⊢ a : A
--------------------    ----------------------    -------------------
Γ ⊢ Πx : A. B : 𝒰 k     Γ ⊢ λx. b : Πx : A. B     Γ ⊢ b a : B{x ↦ a}

    ⊢ Γ         Γ ⊢ A : 𝒰 k    Γ ⊢ b : ⊥
------------    -------------------------
Γ ⊢ ⊥ : 𝒰 k          Γ ⊢ abs b : A
                                                           Γ ⊢ p : eq A a b
     Γ ⊢ A : 𝒰 k                                  Γ, y : A, q : eq A a y ⊢ B : 𝒰 k
Γ ⊢ a : A    Γ ⊢ b : A         Γ ⊢ a : A              Γ ⊢ d : B{y ↦ a, q ↦ refl}
----------------------    --------------------    ----------------------------------
  Γ ⊢ eq A a b : 𝒰 k      Γ ⊢ refl : eq A a a        Γ ⊢ J d p : B{y ↦ b, q ↦ p}

                                                   Γ, x : 𝔹 ⊢ A : 𝒰 k
                                                   Γ ⊢ b : 𝔹
                                                   Γ ⊢ a : A{x ↦ true}
    ⊢ Γ             ⊢ Γ              ⊢ Γ           Γ ⊢ c : A{x ↦ false}
------------    ------------    -------------    -----------------------
Γ ⊢ 𝔹 : 𝒰 k    Γ ⊢ true : 𝔹    Γ ⊢ false : 𝔹    Γ ⊢ if b a c : A{x ↦ b}

--------------------    ------------    ---------------    ----------------
(λx. b) a ≈ b{x ↦ a}    J d refl ≈ d    if true a c ≃ a    if false a c ≃ c

+ reflexivity,  symmetry,
  transitivity, congruence
```

## Logical Relation

The semantic model of the type theory is a logical relation
split into an inductive and a recursive part:
the inductive part defines the interpretation of universes,
while the recursive part defines the interpretation of types.
Both are parametrized over a universe level,
an accessibility proof of that level,
and an abstract interpretation of universe for all lower levels.
The top-level interpretations at a given accessible level
is defined by well-founded induction using the parametrized interpretations.
Below is a simplified sketch of the logical relation,
omitting these accessibility details.
There is also an inductive–recursive interpretation of contexts as predicates on substitutions,
but its conceptual meaning is given below informally.

```
j < k                        A ⇒ B    ⟦B⟧ₖ
------    -----    -----    --------------
⟦𝒰 j⟧ₖ    ⟦⊥⟧ₖ     ⟦𝔹⟧ₖ     ⟦A⟧ₖ

 ⟦A⟧ₖ    ∀a ∈ ⟦A⟧ₖ. ⟦B{x ↦ a}⟧ₖ
-------------------------------
         ⟦Πx : A. B⟧ₖ

⟦A⟧ₖ    a ∈ ⟦A⟧ₖ    b ∈ ⟦A⟧ₖ
----------------------------
        ⟦eq A a b⟧ₖ

A ∈ ⟦𝒰 j⟧ₖ       = ⟦A⟧ⱼ
b ∉ ⟦⊥⟧ₖ
f ∈ ⟦Πx : A. B⟧ₖ = ∀a ∈ ⟦A⟧ₖ. f a ∈ ⟦B{x ↦ a}⟧ₖ
p ∈ ⟦eq A a b⟧ₖ  = p ⇒⋆ refl ∧ a ⇔ b
b ∈ ⟦𝔹⟧ₖ         = b ⇒⋆ true ∨ b ⇒⋆ false
x ∈ ⟦A⟧ₖ         = x ∈ ⟦B⟧ₖ    (where A ⇒ B)

σ ∈ ⟦Γ⟧ = x : A ∈ Γ → σ(x) ∈ ⟦A{σ}⟧ₖ
```

## Axioms

The only axiom used is function extensionality,
which is located in the `ext` module of `accessibility.agda`
as private postulates (one for an implicit and one for an explicit domain).
Function extensionality is used to prove two extensional principles:
* mere propositionality of the accessibility predicate,
  which is used to prove `accU≡` in `semantics.agda`; and
* congruence of dependent function types,
  which is needed to prove cumulativity of the logical relation in `semantics.agda`.

## Contents

Most of the modules are parametrized over an abstract `Level`
and its strict transitive order with all strict upper bounds,
only to be instantiated at the very end by the naturals.

* `common.agda`: Reëxports all the necessary agda-stdlib modules,
  and defines common definitions.
* `accessibility.agda`: The accessibility predicate and its mere propositionality.
* `syntactics.agda`: Syntax, substitution, contexts, and context membership.
* `reduction.agda`: Parallel reduction, substitution lemmas, confluence, and conversion.
* `typing.agda`: Definitional equality, context well-formedness, and well-typedness.
* `semantics.agda`: Logical relations stating semantic typing and semantic context formation,
  along with important properties.
* `soundness.agda`: The fundamental theorem of soundness of typing —
  syntactic well-typedness implies semantic well-typedness.
* `consistency.agda`: Strict order on the naturals, well-foundedness of the naturals
  with respect to its strict order, and logical consistency using the naturals as levels.

## Statistics

```
$ tokei -ft=Agda

================================================================================
 Language             Files        Lines         Code     Comments       Blanks
================================================================================
 Agda                     8         1709         1293          190          226
--------------------------------------------------------------------------------
 ./accessibility.agda                 35           23            3            9
 ./soundness.agda                    149          144            1            4
 ./consistency.agda                  109           67           16           26
 ./syntactics.agda                   349          261           38           50
 ./typing.agda                       211          161           37           13
 ./common.agda                        19           16            0            3
 ./reduction.agda                    500          387           42           71
 ./semantics.agda                    337          234           53           50
================================================================================
 Total                    8         1709         1293          190          226
================================================================================
```