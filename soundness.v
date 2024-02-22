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
  - asimpl. hauto lq:on unfold:γ_ok solve+:lia.
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
  rewrite -h0 => //.
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
  exists PA. by asimpl.
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

Theorem soundness Γ :
  (forall a A, Wt Γ a A -> SemWt Γ a A) /\
  (Wff Γ -> SemWff Γ).
Proof.
  move : Γ.
  apply wt_mutual.
  - move => Γ i h ih ? γ hγ.
    move /(_ i ltac:(done)) in ih.
    case : ih => F ih.
    suff /SemWt_Univ ih'  : SemWt Γ (dep_ith Γ i) (tUniv (F i)).
    + move /ih' : (hγ) {ih'} => [PA hPA].
      exists (F i), PA. sfirstorder.
    + hauto l:on use:dep_ith_shift, good_renaming_truncate, renaming_SemWt.
  - hauto l:on use:SemWt_Univ.
  - move => Γ i A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => γ hγ.
    move /(_ γ hγ) : h0; intros (PA & hPA).
    eexists => /=.
    apply InterpUnivN_Fun_nopf; eauto.
    move => *; asimpl. eauto using γ_ok_cons.
  - move => Γ A b B i _ /SemWt_Univ hB _ hb γ hγ.
    case /(_ γ hγ) : hB => /= PPi hPPi.
    exists i, PPi. split => //.
    move /InterpUnivN_Fun_inv_nopf : hPPi.
    intros (PA & hPA & hTot & ?). subst.
    rewrite /ProdSpace.
    move => a PB ha. asimpl => hPB.
    have : γ_ok (A :: Γ) (a .: γ) by eauto using γ_ok_cons.
    move /hb.
    intros (m & PB0 & hPB0 & hPB0').
    replace PB0 with PB in * by hauto l:on use:InterpUnivN_deterministic'.
    qauto l:on use:P_AppAbs_cbn,InterpUnivN_back_clos  solve+:(by asimpl).
  - move => Γ f A B b _ ihf _ ihb γ hγ.
    rewrite /SemWt in ihf ihb.
    move /(_ γ hγ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ γ hγ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    move /InterpUnivN_Fun_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'. subst.
    move  : hf (hb). move/[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  - move => Γ a A B i _ hA _ /SemWt_Univ hB ? γ hγ.
    have ? : Coherent (subst_tm γ A) (subst_tm γ B)
      by eauto using Coherent_subst_star.
    qauto l:on use:InterpUnivN_Coherent unfold:SemWt.
  - hauto l:on.
  - hauto l:on.
  - rewrite /SemWt => Γ a b c A i _ /SemWt_Univ hA _ ha _ hb _ hc γ hγ.
    case /(_ γ hγ) : ha => ? [PBool [hPBool ha']]; subst.
    have hγ' : γ_ok (tBool :: Γ) (subst_tm γ a .: γ) by eauto using γ_ok_cons.
    move /InterpUnivN_Bool_inv : hPBool => ?. subst.
    case /(_ γ hγ) : hb => ia [PA [hPA hb']].
    case /(_ γ hγ) : hc => ib [PB [hPB hc']].
    move : hA hγ'; move/[apply]. move  => [PA0 hPA0].
    exists i, PA0.
    split; first by asimpl.
    case : ha' => v [hred hv].
    asimpl in *.
    case : v hred hv => // ha0 _.
    + move => [:t].
      apply (InterpUnivN_back_clos_star i) with (A := (subst_tm (tTrue .: γ) A)) (b := (subst_tm γ b)) => //.
      abstract : t.
      apply InterpUnivN_preservation_star with (B := subst_tm (tTrue .: γ) A) in hPA0=>//.
      hauto lq:on ctrs:good_pars_morphing use:pars_morphing_star, good_pars_morphing_ext.
      by apply P_IfTrue_star.
      suff : PA = PA0 by congruence.
      hauto lq:on use:InterpUnivN_deterministic'.
    + move => [:t].
      apply (InterpUnivN_back_clos_star i) with (A := (subst_tm (tFalse .: γ) A)) (b := (subst_tm γ c)) => //.
      abstract : t.
      apply InterpUnivN_preservation_star with (B := subst_tm (tFalse .: γ) A) in hPA0=>//.
      hauto lq:on ctrs:good_pars_morphing use:pars_morphing_star, good_pars_morphing_ext.
      by apply P_IfFalse_star.
      suff : PB = PA0 by congruence.
      hauto lq:on use:InterpUnivN_deterministic'.
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
