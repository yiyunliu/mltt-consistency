Require Import conv par geq imports typing.

Module typing_conv_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).
Module pfacts := par_facts lattice syntax par.
Import pfacts.

Module ifacts := geq_facts lattice syntax ieq.
Import ifacts.

Module lfacts := Lattice.All.Properties lattice.
Import lfacts.

Module cfacts := conv_facts lattice syntax par ieq conv.
Import cfacts.

Lemma lookup_elookup : forall  Γ (i : fin) (ℓ : T) (A : tm),
      lookup i Γ ℓ A -> elookup i (c2e Γ) ℓ.
Proof. induction 1; rewrite /elookup //=. Qed.

Lemma elookup_lookup : forall  Γ (i : fin) (ℓ : T),
    elookup i (c2e Γ) ℓ -> exists A, lookup i Γ ℓ A.
Proof.
  elim.
  - rewrite /elookup //=; by case=>//=.
  - move => [ℓ0 a] Γ ih [|i] ℓ /= h.
    + rewrite /elookup //= in h. move : h => [?]. subst.
      hauto l:on.
    + hauto lq:on ctrs:lookup.
Qed.

Lemma typing_iok Γ ℓ a A (h : Wt Γ ℓ a A) : IOk (c2e Γ) ℓ a.
Proof.
  elim : Γ ℓ a A / h; try qauto use:lookup_elookup ctrs:IOk.
Qed.

Lemma typing_conv Γ ℓ a A (h : Wt Γ ℓ a A) : conv (c2e Γ) a a.
Proof.
  by move /typing_iok /iok_ieq /(_ ℓ ltac:(by rewrite meet_idempotent)) /ieq_conv : h.
Qed.

Lemma lookup_good_renaming_iok_subst_ok ξ Γ Δ :
  lookup_good_renaming ξ Γ Δ ->
  iok_ren_ok ξ (c2e Γ) (c2e Δ).
Proof.
  rewrite /lookup_good_renaming /iok_ren_ok.
  hauto lq:on use:lookup_elookup, elookup_lookup.
Qed.

End typing_conv_facts.
