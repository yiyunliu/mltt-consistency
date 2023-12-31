From WR Require Import syntax join semtyping typing common imports.

Definition γ_ok Γ γ := forall i, i < length Γ -> forall m PA, InterpUnivN m (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt Γ a A := forall γ, γ_ok Γ γ -> exists m PA, InterpUnivN m (subst_tm γ A) PA /\ PA (subst_tm γ a).
Definition SemWff Γ := forall i, i < length Γ -> exists F, SemWt (skipn (S i) Γ) (ith Γ i) (tUniv (F i)).

Lemma γ_ok_cons {i Γ γ a PA A} :
  InterpUnivN i (subst_tm γ A) PA ->
  PA a ->
  γ_ok Γ γ ->
  γ_ok (A :: Γ) (a .: γ).
Proof.
  move => h0 h1 h2.
  case => /= [_ | m ? PA0].
  - move => j PA0 hPA0.
    asimpl in hPA0.
    suff : PA = PA0 by congruence.
    hauto l:on use:InterpUnivN_deterministic'.
  - asimpl.
    apply h2.
    lia.
Qed.

Lemma γ_ok_renaming Γ γ :
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    γ_ok Δ γ ->
    γ_ok Γ (ξ >> γ).
Proof.
  move => Δ ξ hscope h1.
  rewrite /γ_ok => i hi j PA.
  replace (subst_tm (ξ >> γ) (dep_ith Γ i)) with
    (subst_tm γ (ren_tm ξ (dep_ith Γ i))); last by asimpl.
  rewrite /good_renaming in hscope.
  case /(_ i hi) : hscope => ? h0.
  rewrite -h0; auto.
  by apply h1.
Qed.

Lemma renaming_SemWt Γ a A :
  SemWt Γ a A ->
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    SemWt Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  rewrite /SemWt => h Δ ξ hξ γ hγ.
  have hγ' : (γ_ok Γ (ξ >> γ)) by eauto using γ_ok_renaming.
  case /(_ _ hγ') : h => PA hPA.
  exists PA.
  by asimpl.
Qed.

Lemma SemWt_Univ Γ A i :
  SemWt Γ A (tUniv i) <->
  forall γ, γ_ok Γ γ -> exists PA , InterpUnivN i (subst_tm γ A) PA.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUnivN_Univ_inv'.
  - move => /[swap] γ /[apply].
    case => PA hPA.
    exists (S i). eexists.
    split.
    + simp InterpUniv. apply InterpExt_Univ. lia.
    + simpl. eauto.
Qed.

Lemma P_AppAbs_cbn (A a b b0 : tm) :
  b0 = subst_tm (b..) a ->
  Par (tApp (tAbs A a) b) b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

Theorem soundness Γ :
  (forall a A, Wt Γ a A -> SemWt Γ a A) /\
  (Wff Γ -> SemWff Γ).
Proof.
  move : Γ.
  apply wt_mutual.
  - move => Γ i h ih ? γ hγ.
    move /(_ i ltac:(done)) in ih.
    case : ih => F ih.
    suff ih' : SemWt Γ (dep_ith Γ i) (tUniv (F i)).
    + case /(_ _ hγ) : ih' => j [PA [hPA hi]].
      simpl in hPA.
      simp InterpUniv in hPA.
      move /InterpExt_Univ_inv : hPA => [? h0]; subst.
      move : hi; intros (PA & hi).
      exists (F i), PA; sfirstorder.
    + hauto l:on use:dep_ith_shift, good_renaming_truncate, renaming_SemWt.
  - hauto l:on use:SemWt_Univ.
  - move => Γ i A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => γ hγ.
    move /(_ γ hγ) : h0; intros (PA & hPA).
    eexists => /=.
    apply InterpUnivN_Fun; eauto.
    move => *; asimpl. eauto using γ_ok_cons.
  - move => Γ A b B i _ /SemWt_Univ hB _ hb γ hγ.
    case /(_ γ hγ) : hB => /= PPi hPPi.
    exists i, PPi; split => //.
    move /InterpUnivN_Fun_inv' : hPPi.
    intros (PA & hPA & _ & ? ); subst.
    move => a ha.
    have : γ_ok (A :: Γ) (a .: γ) by hauto l:on use:γ_ok_cons.
    rewrite /SemWt in hb.
    move /hb.
    intros (m & PB0 & hPB0 & hPB0').
    exists m, PB0.
    split => //. by asimpl.
    apply : InterpUnivN_back_clos; eauto.
    apply P_AppAbs_cbn; by asimpl.
  - move => Γ f A B b _ ihf _ ihb γ hγ.
    rewrite /SemWt in ihf ihb.
    move /(_ γ hγ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ γ hγ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    move /InterpUnivN_Fun_inv' : hPi.
    intros (PA0 & hPA0 & h0 & ?). subst.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'. subst.
    move /hf : (hb). intros (m & PB & h).
    move : h. asimpl. hauto l:on.
  - move => Γ a A B i _ hA _ /SemWt_Univ hB [C [? ?]] γ hγ.
    case : (hA γ hγ) => j [PA [hPA hPAa]].
    case : (hB γ hγ) => PB hPB.
    simpl in hPB.
    exists i, PA.
    split; auto.
    have [*] : Pars (subst_tm γ A) (subst_tm γ C) /\
                 Pars (subst_tm γ B) (subst_tm γ C)
      by sfirstorder use:par_subst_star.
    have ? :InterpUnivN i (subst_tm γ C) PB by sfirstorder use:InterpUnivN_preservation_star.
    have ? :InterpUnivN i (subst_tm γ A) PB by sfirstorder use:InterpUnivN_back_preservation_star.
    suff : PA = PB by congruence.
    eauto using InterpUnivN_deterministic'.
  - hauto l:on.
  - hauto l:on.
  - rewrite /SemWt => Γ a b c A _ ha _ hb _ hc γ hγ.
    case /(_ γ hγ) : ha => i [? [/InterpUnivN_Bool_inv ? ha']]; subst.
    case /(_ γ hγ) : hb => j [PA [hPA hb']].
    case /(_ γ hγ) : hc => k [PB [hPB hc']].
    have ? : PA = PB by hauto lq:on rew:off use:InterpUnivN_deterministic'.
    subst.
    exists j, PB; split; auto.
    simpl.
    case : ha' => v [hred hv].
    case : v hred hv => // ha0 _.
    + apply (InterpUnivN_back_clos_star j) with (A := (subst_tm γ A)) (b := (subst_tm γ b)) => //.
      eauto using P_IfTrue_star.
    + apply (InterpUnivN_back_clos_star k) with (A := (subst_tm γ A)) (b := (subst_tm γ c)) => //.
      eauto using P_IfFalse_star.
  - hauto l:on use:SemWt_Univ.
  - hauto lq:on use:InterpUnivN_Univ_inv, SemWt_Univ.
  - hauto l:on.
  - hauto l:on use:SemWt_Univ.
  - move => Γ t a b p A i j C _ _ _ _ _ _ _ hp _ hC _ ht γ hγ.
    move : hp (hγ); move/[apply] => hp.
    move : ht (hγ); move/[apply]. intros (m & PA & hPA & ht).
    have [? [q ?]] : Pars (subst_tm γ p) tRefl /\ Coherent (subst_tm γ a) (subst_tm γ b) by
      sauto lq:on  rew:db:InterpUniv use:InterpExt_Eq_inv.
    exists m, PA.
    split.
    + asimpl in hPA.
      apply : InterpUnivN_Coherent; eauto.
      exists (subst_tm (tRefl .: (q .: γ)) C).
      hauto lq:on ctrs:good_pars_morphing use:pars_morphing_star, @rtc_refl, good_pars_morphing_ext2.
    + asimpl.
      eapply InterpUnivN_back_clos_star with (b := subst_tm γ t); eauto.
      sfirstorder use: P_JRefl_star.
  - hauto l:on.
Qed.

Lemma consistency a : ~Wt nil a tVoid.
Proof.
  move => h.
  apply soundness in h.
  rewrite /SemWt in h.
  move : (h var_tm).
  case.
  rewrite /γ_ok; sauto lq:on.
  asimpl.
  move => i [PA [hPA ha]].
  simp InterpUniv in hPA.
  apply InterpExt_Void_inv in hPA; subst.
  apply ha.
Qed.
