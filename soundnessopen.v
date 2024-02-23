From WR Require Import syntax join semtypingopen normalform typing common imports.

Definition γ_ok Γ γ := forall i, i < length Γ -> forall m PA, InterpUnivN m (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt Γ a A := forall γ, γ_ok Γ γ -> exists m PA, InterpUnivN m (subst_tm γ A) PA /\ PA (subst_tm γ a).
Definition SemWff Γ := forall i, i < length Γ -> exists F, SemWt (skipn (S i) Γ) (ith Γ i) (tUniv (F i)).

Lemma γ_ok_cons i Γ γ a PA A :
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
    + hauto lq:on.
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
    move  : hf (hb) => /[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  - move => Γ a A B i _ hA _ /SemWt_Univ hB ? γ hγ.
    have ? : Coherent (subst_tm γ A) (subst_tm γ B)
      by eauto using Coherent_subst_star.
    qauto l:on use:InterpUnivN_Coherent unfold:SemWt.
  - hauto l:on.
  - hauto l:on.
  - move => Γ a b c A l _ /SemWt_Univ hA _ ha _ hb _ hc γ hγ.
    case /(_ γ hγ) : ha => i [? [/InterpUnivN_Bool_inv ? ha']]; subst.
    case /(_ γ hγ) : hb => j [PA [hPA hb']].
    case /(_ γ hγ) : hc => k [PB [hPB hc']].
    move : ha' => [v [hred [hv|hv]]].
    + case : v hred hv => // ha0 _.
      * exists j, PA.
        split.
        move /InterpUnivN_back_preservation_star  : hPA.
        apply. asimpl. qauto l:on use:pars_morphing, good_pars_morphing_ext, good_pars_morphing_one, Par_refl.
        apply : InterpUnivN_back_clos_star; eauto.
        eauto using P_IfTrue_star.
      * exists k, PB.
        split.
        move /InterpUnivN_back_preservation_star  : hPB.
        apply. asimpl. qauto l:on use:pars_morphing, good_pars_morphing_ext, good_pars_morphing_one, Par_refl.
        apply : InterpUnivN_back_clos_star; eauto.
        eauto using P_IfFalse_star.
    (* New case for when the scrutinee is neutral *)
    + have ? : wne (subst_tm γ a) by hauto lq:on use:wne_if, adequacy.
      have : γ_ok (tBool :: Γ) (subst_tm γ a .: γ). apply : (γ_ok_cons i); hauto l:on ctrs:InterpExt.
      move /hA => [PN hPN]. exists l, PN. split; first by asimpl.
      qauto l:on use:adequacy, wne_if unfold:CR .
  - hauto l:on use:SemWt_Univ.
  - hauto lq:on use:InterpUnivN_Univ_inv, SemWt_Univ.
  - move => Γ a A _ _ _ ha γ.
    move : ha. move/[apply]. move => [m [PA [h0 h1]]].
    exists 0. eexists.
    split => /=.
    + apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty, InterpUnivN_Eq unfold:CR.
    + qauto l:on ctrs:rtc use:Coherent_reflexive inv:Par .
  - move => Γ a b A i j _ ha _ hb _ /SemWt_Univ hA.
    apply SemWt_Univ => γ hγ.
    eexists => /=. apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty unfold:SemWt, CR.
  - move => Γ t a b p A i j C _ ha _ hb _ _ _ hp _ /SemWt_Univ hC _ ht γ hγ.
    move : hp (hγ); move/[apply] => /=. intros (m & PA & hPA & hp).
    move  /InterpUnivN_Eq_inv : hPA. intros (-> & ? & ? & ?).
    move : ht (hγ); move/[apply]. intros (k & PA & hPA & ht).
    move : hp.
    move =>[[hp hco] | ?].
    + exists k, PA.
      split.
      * asimpl in hPA.
        apply : InterpUnivN_Coherent; eauto.
        rewrite /Coherent.
        case : hco => ab ?.
        exists (subst_tm (tRefl .: (ab .: γ)) C).
        split.
        ** apply pars_morphing_star; last by apply rtc_refl.
           apply good_pars_morphing_ext2;
             hauto lq:on ctrs:good_pars_morphing.
        ** apply pars_morphing_star; last by apply rtc_refl.
           apply good_pars_morphing_ext2. apply rtc_refl.
           tauto. apply good_pars_morphing_one.
      * asimpl.
        eapply InterpUnivN_back_clos_star with (b := subst_tm γ t); eauto.
        sfirstorder use: P_JRefl_star.
    + asimpl.
      move /(_ (subst_tm γ p .: (subst_tm γ b .: γ))) : hC.
      case.
      * eapply γ_ok_cons with (i := 0).
        asimpl.
        apply InterpUnivN_Eq; eauto.
        right. auto.
        move : hb (hγ). move/[apply].
        move => [i0 [PA0 hb0]].
        hauto l:on use:γ_ok_cons.
      * move => PC hPC.
        exists i, PC. split; first tauto.
        qauto l:on use:adequacy,wne_j unfold:CR.
  - hauto l:on.
Qed.

Lemma mltt_normalizing Γ a A : Wt Γ a A -> wn a /\ wn A.
Proof.
  move => h.
  apply soundness in h.
  move : h.
  rewrite /SemWt.
  move /(_ var_tm).
  elim.
  - asimpl.
    hauto l:on use:adequacy, InterpUniv_wn_ty unfold:CR.
  - rewrite /γ_ok.
    move=> i ? m PA. asimpl.
    hauto q:on ctrs:rtc use:adequacy.
Qed.
