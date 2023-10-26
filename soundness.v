From WR Require Import syntax join semtyping typing.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.


Definition γ_ok n Γ γ := forall i, i < n -> forall PA, InterpType (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt n Γ a A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA /\ PA a.
Definition SemUWf n Γ A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA.

Theorem soundness n Γ a A (h : Wt n Γ a A) : SemWt n Γ a A.
Proof.
  elim : n Γ a A / h; eauto.
  - rewrite /SemWt.
    move => n Γ i hi γ hγ.
    rewrite /γ_ok in hγ.
    move /(_ i hi) in hγ.
    admit.
  - hauto l:on.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
