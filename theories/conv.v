Require Import imports par geq.
From Hammer Require Import Hammer.

Module Type conv_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax).

  Definition conv Ξ a b := exists c0 c1 ℓ, a ⇒* c0 /\ b ⇒* c1 /\ IEq Ξ ℓ c0 c1.
End conv_sig.

Module conv_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq).

Module pfacts := par_facts lattice syntax par.
Module ifacts := geq_facts lattice syntax ieq.
Import pfacts.
Import ifacts.

Lemma iok_preservation Ξ ℓ a (h : IOk Ξ ℓ a) : forall b, a ⇒ b -> IOk Ξ ℓ b.
Proof.
  elim : Ξ ℓ a / h; try qauto inv:Par ctrs:IOk.
  (* App *)
  - move => Ξ ℓ a ℓ0 b ha iha hb ihb b0.
    elim /Par_inv=>//.
    + hauto lq:on ctrs:IOk.
    + move => _ a0 a1 b1 b2 ℓ1 ha0 hb1 [*]. subst.
      apply : iok_subst; eauto.
      have /iha : tAbs ℓ0 a0 ⇒ tAbs ℓ0 a1 by eauto with par.
      by inversion 1.
Qed.

Lemma simulation : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall a', Par a a' ->
            exists b', Par b b' /\ IEq Ξ ℓ a' b') /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall a', Par a a' ->
            exists b', Par b b' /\ GIEq Ξ ℓ ℓ0 a' b').
Proof.
  apply IEq_mutual; try qauto ctrs:IEq, Par, GIEq inv:Par.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - move => Ξ ℓ ℓ0 a0 a1 h0 ih0 a'.
    elim /Par_inv => // h1 ℓ1 a2 a3 h2 [*]; subst.
    case /ih0 : (h2) => a2 h.
    exists (tAbs ℓ0 a2).
    hauto lq:on ctrs:IEq, Par use:Par_refl.
  - move => Ξ ℓ a0 a1 ℓ0 b0 b1 h0 ih0 h1 ih1 a'.
    elim /Par_inv => //.
    + hauto lq:on ctrs:Par, IEq.
    + move => hp a2 a3 b2 b3 ℓ1 h2 h3 [*]; subst.
      case /ih1 : h3 => b4 [h30 h31].
      elim /IEq_inv : h0 => // _ ℓ1 a0 a4 he [*]. subst.
      have /ih0 : tAbs ℓ0 a2 ⇒ tAbs ℓ0 a3 by eauto with par.
      move => [? []].
      elim /Par_inv => // _ ℓ1 a0 a1 ? [? ? ?]. subst.
      elim /IEq_inv => // _ ℓ1 a0 a5 ?[? ?][? ?]. subst.
      exists (a1[b4..]). split.
      by auto using Par_refl with par.
      eapply ieq_morphing_mutual; eauto.
      rewrite /ieq_good_morphing.
      case => [|i]//=.
      scongruence unfold:elookup.
      move => ℓ1 ?.
      apply gieq_refl. sfirstorder.
  - hauto lq:on ctrs:IEq inv:Par use:Par_refl.
  - hauto l:on ctrs:Par use:Par_refl.
Qed.

Lemma simulation_star Ξ ℓ a b a' (h : IEq Ξ ℓ a b) (h0 : a ⇒* a') :
    exists b', b ⇒* b' /\ IEq Ξ ℓ a' b'.
Proof.
  move : b h.
  elim : a a' / h0.
  - sfirstorder.
  - move => a a0 a1 ha ha0 ih b hab.
    suff : exists b0,Par b b0 /\ IEq Ξ ℓ a0 b0; hauto lq:on use:simulation ctrs:rtc.
Qed.

Lemma conv_sym Ξ a b : conv Ξ a b -> conv Ξ b a.
Proof.
  strivial use: ieq_sym_mutual, I_Void unfold:conv.
Qed.

Lemma ieq_trans_heterogeneous Ξ ℓ ℓ0 a b c :
  IEq Ξ ℓ a b ->
  IEq Ξ ℓ0 b c ->
  IEq Ξ (ℓ ∩ ℓ0) a c.
Proof.
  move => h0 h1.
  apply ieq_trans with (B := b).
  - apply ieq_sym_mutual.
    apply ieq_sym_mutual in h0.
    eapply ieq_downgrade_mutual; eauto.
  - apply ieq_sym_mutual in h0.
    rewrite meet_commutative.
    eapply ieq_downgrade_mutual; eauto.
Qed.

Lemma conv_trans Ξ a b c : conv Ξ a b -> conv Ξ b c -> conv Ξ a c.
Proof.
  rewrite /conv.
  move => [a0 [b0 [ℓ0 [h0 [h1 h2]]]]].
  move => [b1 [c0 [ℓ1 [h3 [h4 h5]]]]].
  move : Pars_confluent (h1) (h3). repeat move/[apply].
  move => [q [h6 h7]].
  move /ieq_sym in h2.
  move : simulation_star (h2) (h6). repeat move/[apply].
  move => [p0][? ?].
  move : simulation_star (h5) (h7). repeat move/[apply].
  move => [p1][? ?].
  exists p0, p1. hauto lq:on use:ieq_sym, ieq_trans_heterogeneous, rtc_transitive.
Qed.

End conv_facts.
