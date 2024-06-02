Require Import imports par geq.
From Hammer Require Import Hammer.

Module Type conv_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax).

  Definition iconv Ξ ℓ a b := exists c0 c1, a ⇒* c0 /\ b ⇒* c1 /\ IEq Ξ ℓ c0 c1.
  Definition conv Ξ a b := exists ℓ, iconv Ξ ℓ a b.
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

Lemma ieq_iconv Ξ ℓ a b : IEq Ξ ℓ a b -> iconv Ξ ℓ a b.
Proof. sfirstorder use:rtc_refl unfold:iconv. Qed.

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
  (* Let *)
  - move => Ξ ℓ ℓ0 ℓ1 a b ? ha iha hb ihb ?.
    elim /Par_inv=>//_.
    + hauto lq:on ctrs:IOk.
    + move => ? ℓ2 a0 b0 c0 a1 b1 c1 ? ? ? [*]. subst.
      apply : iok_morphing; eauto.
      rewrite /iok_subst_ok.
      have /iha {}iha  : tPack ℓ0 a0 b0 ⇒ tPack ℓ0 a1 b1 by eauto with par. inversion iha.
      case; rewrite /elookup //=.
      * scongruence.
      * case => /=.
        scongruence.
        sfirstorder use:meet_idempotent,IO_Var.
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
  - move => Ξ ℓ ℓ0 a0 a1 b0 b1 A0 A1 ? ha iha hb ihb hc ihc ?.
    elim /Par_inv=>// _ ? ? ? ? a2 b2 A2 + + + [*]. subst.
    move /iha => {iha}?.
    move /ihb => {ihb}?.
    move /ihc => {ihc}?.
    hauto lq:on ctrs:Par, IEq.
  - move => Ξ ℓ C0 C1 t0 t1 p0 p1 ? ht ? hp q.
    elim /Par_inv=>// _.
    + move => ? C2  ? ? t2 p2 + + + [*]. subst.
      move /ht => {}ht ?.
      move /hp => {}hp.
      move : ht => [t']?.
      move : hp => [p']?.
      exists (tJ C1 t' p').
      hauto lq:on ctrs:IEq, Par use:Par_refl.
    + move => ? t2 t3 + [*]. subst.
      have ? : p1 = tRefl by qauto l:on inv:IEq. subst.
      hauto l:on ctrs:Par, IEq.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - move => Ξ ℓ ℓ0 ℓ1 a0 b0 a1 b1 ha iha hb ihb a'.
    elim /Par_inv => //= _.
    + hauto lq:on ctrs:IEq, Par.
    + move => ? ? a2 b2 c0 a3 b3 c1 ? ? hbc [*]. subst.
      elim /IEq_inv : ha=>//= hp ℓ2 a0 b4 a4 b5 ? ? [*]. subst.
      have /iha : tPack ℓ0 a2 b2 ⇒ tPack ℓ0 a3 b3 by auto using P_Pack.
      move => [b'][hp'].
      elim /IEq_inv=>//= _ ℓ2 a0 b4 a1 b6 ? ? [*]. subst.
      move /ihb : hbc.
      have {hp}[? ?] : a4 ⇒ a1 /\ b5 ⇒ b6 by inversion hp'.
      move => [b'][?]?.
      exists (b'[b6.:a1..]).
      split. by eauto using P_LetPack.
      eapply ieq_morphing_mutual; eauto.
      case => [|i]//=.
      * rewrite /elookup => //=.
        move => ℓ2 [*]. subst.
        case : (lprop.sub_eqdec ℓ2 ℓ) => ?;
               by eauto with ieq.
      * move => ℓ2.
        rewrite /elookup//=.
        case : i=>[|i]//=.
        scongruence.
        case : (lprop.sub_eqdec ℓ2 ℓ) => ?;
               by eauto with ieq.
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

Lemma iconv_sym Ξ ℓ a b : iconv Ξ ℓ a b -> iconv Ξ ℓ b a.
Proof. hauto lq:on use:ieq_sym_mutual unfold:conv, iconv. Qed.

Lemma conv_sym Ξ a b : conv Ξ a b -> conv Ξ b a.
Proof. hauto lq:on use:iconv_sym unfold:conv. Qed.

Lemma iconv_par Ξ ℓ a b a0  :
  iconv Ξ ℓ a b -> a ⇒ a0 -> iconv Ξ ℓ a0 b.
Proof.
  rewrite /iconv.
  move => [c0][c1][h0][h1]h2 h3.
  apply rtc_once in h3.
  move : Pars_confluent (h0) (h3). repeat move/[apply].
  move => [ca][h5]h6.
  move : simulation_star (h2) (h5). repeat move/[apply].
  move /ieq_sym in h2.
  move => [c1' [h7 h8]].
  exists ca, c1'.
  hauto l:on use:rtc_transitive.
Qed.

Lemma iconv_par2 Ξ ℓ a b a0 b0 :
  iconv Ξ ℓ a b -> a ⇒ a0 -> b ⇒ b0 -> iconv Ξ ℓ a0 b0.
Proof. hauto lq:on use:iconv_par, iconv_sym. Qed.

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

Lemma ieq_trans_heterogeneous_leq Ξ ℓ ℓ0 a b c :
  ℓ ⊆ ℓ0 ->
  IEq Ξ ℓ a b ->
  IEq Ξ ℓ0 b c ->
  IEq Ξ ℓ a c.
Proof.
  hauto l:on drew:off use:ieq_trans_heterogeneous, meet_commutative.
Qed.

Lemma ieq_trans_heterogeneous_leq' Ξ ℓ ℓ0 a b c :
  ℓ ⊆ ℓ0 ->
  IEq Ξ ℓ0 a b ->
  IEq Ξ ℓ b c ->
  IEq Ξ ℓ a c.
Proof.
  move => h.
  move /ieq_trans_heterogeneous /[apply].
  rewrite meet_commutative. congruence.
Qed.

Lemma iconv_trans_heterogeneous Ξ ℓ0 ℓ1 a b c :
  iconv Ξ ℓ0 a b -> iconv Ξ ℓ1 b c -> iconv Ξ (ℓ0 ∩ ℓ1) a c.
Proof.
  rewrite /iconv.
  move => [a0 [b0 [h0 [h1 h2]]]].
  move => [b1 [c0 [h3 [h4 h5]]]].
  move : Pars_confluent (h1) (h3). repeat move/[apply].
  move => [q [h6 h7]].
  move /ieq_sym in h2.
  move : simulation_star (h2) (h6). repeat move/[apply].
  move => [p0][? ?].
  move : simulation_star (h5) (h7). repeat move/[apply].
  move => [p1][? ?].
  exists p0, p1.  hauto lq:on use:ieq_sym, ieq_trans_heterogeneous, rtc_transitive.
Qed.

Lemma iconv_trans_heterogeneous_leq Ξ ℓ ℓ0 a b c :
  ℓ ⊆ ℓ0 ->
  iconv Ξ ℓ a b ->
  iconv Ξ ℓ0 b c ->
  iconv Ξ ℓ a c.
Proof.
  hauto l:on drew:off use:iconv_trans_heterogeneous, meet_commutative.
Qed.

Lemma iconv_trans_heterogeneous_leq' Ξ ℓ ℓ0 a b c :
  ℓ ⊆ ℓ0 ->
  iconv Ξ ℓ0 a b ->
  iconv Ξ ℓ b c ->
  iconv Ξ ℓ a c.
Proof.
  move => h.
  move /iconv_trans_heterogeneous /[apply].
  rewrite meet_commutative. congruence.
Qed.

Lemma iconv_trans Ξ ℓ a b c :
  iconv Ξ ℓ a b -> iconv Ξ ℓ b c -> iconv Ξ ℓ a c.
Proof.
  hauto l:on use:iconv_trans_heterogeneous_leq, meet_idempotent.
Qed.

Lemma conv_trans Ξ a b c : conv Ξ a b -> conv Ξ b c -> conv Ξ a c.
Proof.
  hauto lq:on use:iconv_trans_heterogeneous unfold:conv.
Qed.

Lemma iconv_subst Ξ ℓ Δ ρ (h : iok_subst_ok ρ Ξ Δ) a b (h0 : iconv Ξ ℓ a b) :
  iconv Δ ℓ a[ρ] b[ρ].
Proof.
  rewrite /iconv in h0 *.
  move : h0 => [c0][c1][h0][h1]h2.
  exists c0[ρ], c1[ρ].
  sfirstorder use:ieq_morphing_iok, Par_subst_star.
Qed.

Lemma conv_subst Ξ Δ ρ (h : iok_subst_ok ρ Ξ Δ) a b (h0 : conv Ξ a b) :
  conv Δ a[ρ] b[ρ].
Proof. hauto lq:on use:iconv_subst unfold:conv. Qed.

End conv_facts.
