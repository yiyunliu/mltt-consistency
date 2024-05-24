Require Import imports par geq.

Module Type conv_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax).

  Definition conv Ξ ℓ a b := exists c0 c1, a ⇒ c0 /\ b ⇒ c1 /\ IEq Ξ ℓ c0 c1.
End conv_sig.

Module Type conv_sig_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq).

Module pfacts := par_facts lattice syntax par.
Module ifacts := geq_facts lattice syntax ieq.
Import pfacts.
Import ifacts.

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
      exists (a4[b4..]). split.
      by auto using Par_refl with par.
      apply IEq_


      exists (subst_tm (b3..) a5).
      split.
      * hauto q:on ctrs:Par.
      * apply ieq_morphing with (Ξ := ℓ0 :: Ξ); eauto.
        case => /= [|n /Arith_prebase.lt_S_n ?]; first by asimpl.
        asimpl.
        by apply gieq_refl.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - hauto l:on ctrs:Par use:Par_refl.
Qed.


End conv_sig_facts.
