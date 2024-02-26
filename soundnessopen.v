From WR Require Import syntax join semtypingopen normalform typing common imports.

Definition ρ_ok Γ ρ := forall i, i < length Γ -> forall m PA, InterpUnivN m (subst_tm ρ (dep_ith Γ i)) PA -> PA (ρ i).
Definition SemWt Γ a A := forall ρ, ρ_ok Γ ρ -> exists m PA, InterpUnivN m (subst_tm ρ A) PA /\ PA (subst_tm ρ a).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

Definition SemWff Γ := forall i, i < length Γ -> exists F, SemWt (skipn (S i) Γ) (ith Γ i) (tUniv (F i)).
Notation "⊨ Γ" := (SemWff Γ) (at level 70).

Lemma ρ_ok_cons i Γ ρ a PA A :
 ⟦ A [ρ] ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (A :: Γ) (a .: ρ).
Proof.
  move => h0 h1 h2.
  case => /= [_ | m ? PA0].
  - move => j PA0 hPA0.
    asimpl in hPA0.
    suff : PA = PA0 by congruence.
    hauto l:on use:InterpUnivN_deterministic'.
  - asimpl. hauto lq:on unfold:ρ_ok solve+:lia.
Qed.

Lemma ρ_ok_renaming Γ ρ :
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    ρ_ok Δ ρ ->
    ρ_ok Γ (ξ >> ρ).
Proof.
  move => Δ ξ hscope h1.
  rewrite /ρ_ok => i hi j PA.
  replace (subst_tm (ξ >> ρ) (dep_ith Γ i)) with
    (subst_tm ρ (ren_tm ξ (dep_ith Γ i))); last by asimpl.
  rewrite /good_renaming in hscope.
  case /(_ i hi) : hscope => ? h0.
  rewrite -h0 => //.
  by apply h1.
Qed.

Lemma renaming_SemWt Γ a A :
  (Γ ⊨ a ∈ A) ->
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    Δ ⊨ a⟨ξ⟩ ∈ A⟨ξ⟩ .
Proof.
  rewrite /SemWt => h Δ ξ hξ ρ hρ.
  have hρ' : (ρ_ok Γ (ξ >> ρ)) by eauto using ρ_ok_renaming.
  case /(_ _ hρ') : h => PA hPA.
  exists PA.
  by asimpl.
Qed.


(* Well-formed types have interpretations *)
Lemma SemWt_Univ Γ A i :
  (Γ ⊨ A ∈ tUniv i) <->
  forall ρ, ρ_ok Γ ρ -> exists S , ⟦ A[ρ] ⟧ i ↘ S.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUnivN_Univ_inv'.
  - move => /[swap] ρ /[apply].
    case => PA hPA.
    exists (S i). eexists.
    split.
    + simp InterpUniv. apply InterpExt_Univ. lia.
    + hauto lq:on.
Qed.

(* Fundamental theorem: Syntactic typing implies semantic typing *)
Theorem soundness Γ :
  (forall a A, (Γ ⊢ a ∈ A) -> (Γ ⊨ a ∈ A)) /\
  ((⊢ Γ) -> (⊨ Γ)).
Proof.
  move : Γ.
  apply wt_mutual.
  - move => Γ i h ih ? ρ hρ.
    move /(_ i ltac:(done)) in ih.
    case : ih => F ih.
    suff ih' : SemWt Γ (dep_ith Γ i) (tUniv (F i)).
    + case /(_ _ hρ) : ih' => j [PA [hPA hi]].
      simpl in hPA.
      simp InterpUniv in hPA.
      move /InterpExt_Univ_inv : hPA => [? h0]; subst.
      move : hi; intros (PA & hi).
      exists (F i), PA; sfirstorder.
    + hauto l:on use:dep_ith_shift, good_renaming_truncate, renaming_SemWt.
  - hauto l:on use:SemWt_Univ.
  - move => Γ i A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => ρ hρ.
    move /(_ ρ hρ) : h0; intros (PA & hPA).
    eexists => /=.
    apply InterpUnivN_Fun_nopf; eauto.
    move => *; asimpl. eauto using ρ_ok_cons.
  - move => Γ A b B i _ /SemWt_Univ hB _ hb ρ hρ.
    case /(_ ρ hρ) : hB => /= PPi hPPi.
    exists i, PPi. split => //.
    move /InterpUnivN_Fun_inv_nopf : hPPi.
    intros (PA & hPA & hTot & ?). subst.
    rewrite /ProdSpace.
    move => a PB ha. asimpl => hPB.
    have : ρ_ok (A :: Γ) (a .: ρ) by eauto using ρ_ok_cons.
    move /hb.
    intros (m & PB0 & hPB0 & hPB0').
    replace PB0 with PB in * by hauto l:on use:InterpUnivN_deterministic'.
    qauto l:on use:P_AppAbs_cbn,InterpUnivN_back_clos  solve+:(by asimpl).
  - move => Γ f A B b _ ihf _ ihb ρ hρ.
    rewrite /SemWt in ihf ihb.
    move /(_ ρ hρ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ ρ hρ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    move /InterpUnivN_Fun_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'. subst.
    move  : hf (hb) => /[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  - move => Γ a A B i _ hA _ /SemWt_Univ hB ? ρ hρ.
    have ? : Coherent (subst_tm ρ A) (subst_tm ρ B)
      by eauto using Coherent_subst_star.
    qauto l:on use:InterpUnivN_Coherent unfold:SemWt.
  - hauto l:on.
  - hauto l:on.
  - move => Γ a b c A l _ /SemWt_Univ hA _ ha _ hb _ hc ρ hρ.
    case /(_ ρ hρ) : ha => i [? [/InterpUnivN_Bool_inv ? ha']]; subst.
    case /(_ ρ hρ) : hb => j [PA [hPA hb']].
    case /(_ ρ hρ) : hc => k [PB [hPB hc']].
    move : ha' => [v [hred [hv|hv]]].
    + case : v hred hv => // ha0 _.
      * exists j, PA.
        split.
        move /InterpUnivN_back_preservation_star  : hPA.
        apply. asimpl. qauto l:on ctrs:rtc use:Pars_morphing, good_Pars_morphing_ext, Par_refl.
        apply : InterpUnivN_back_clos_star; eauto.
        eauto using P_IfTrue_star.
      * exists k, PB.
        split.
        move /InterpUnivN_back_preservation_star  : hPB.
        apply. asimpl. qauto l:on ctrs:rtc use:Pars_morphing, good_Pars_morphing_ext, Par_refl.
        apply : InterpUnivN_back_clos_star; eauto.
        eauto using P_IfFalse_star.
    (* New case for when the scrutinee is neutral *)
    + have ? : wne (subst_tm ρ a) by hauto lq:on use:wne_if, adequacy.
      have : ρ_ok (tBool :: Γ) (subst_tm ρ a .: ρ). apply : (ρ_ok_cons i); hauto l:on ctrs:InterpExt.
      move /hA => [PN hPN]. exists l, PN. split; first by asimpl.
      qauto l:on use:adequacy, wne_if unfold:CR .
  - hauto l:on use:SemWt_Univ.
  - hauto lq:on use:InterpUnivN_Univ_inv, SemWt_Univ.
  - move => Γ a A _ _ _ ha ρ.
    move : ha. move/[apply]. move => [m [PA [h0 h1]]].
    exists 0. eexists.
    split => /=.
    + apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty, InterpUnivN_Eq unfold:CR.
    + qauto l:on ctrs:rtc use:Coherent_reflexive inv:Par .
  - move => Γ a b A i j _ ha _ hb _ /SemWt_Univ hA.
    apply SemWt_Univ => ρ hρ.
    eexists => /=. apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty unfold:SemWt, CR.
  - move => Γ t a b p A i j C _ ha _ hb _ _ _ hp _ /SemWt_Univ hC _ ht ρ hρ.
    move : hp (hρ); move/[apply] => /=. intros (m & PA & hPA & hp).
    move  /InterpUnivN_Eq_inv : hPA. intros (-> & ? & ? & ?).
    move : ht (hρ); move/[apply]. intros (k & PA & hPA & ht).
    move : hp.
    move =>[[hp hco] | ?].
    + exists k, PA.
      split.
      * asimpl in hPA.
        apply : InterpUnivN_Coherent; eauto.
        rewrite /Coherent.
        case : hco => ab ?.
        exists (subst_tm (tRefl .: (ab .: ρ)) C).
        split.
        ** apply Pars_morphing_star; last by apply rtc_refl.
           apply good_Pars_morphing_ext2;
             hauto lq:on ctrs:rtc.
        ** apply Pars_morphing_star; last by apply rtc_refl.
           apply good_Pars_morphing_ext2. apply rtc_refl.
           tauto. apply rtc_refl.
      * asimpl.
        eapply InterpUnivN_back_clos_star with (b := subst_tm ρ t); eauto.
        sfirstorder use: P_JRefl_star.
    + asimpl.
      move /(_ (subst_tm ρ p .: (subst_tm ρ b .: ρ))) : hC.
      case.
      * eapply ρ_ok_cons with (i := 0).
        asimpl.
        apply InterpUnivN_Eq; eauto.
        right. auto.
        move : hb (hρ). move/[apply].
        move => [i0 [PA0 hb0]].
        hauto l:on use:ρ_ok_cons.
      * move => PC hPC.
        exists i, PC. split; first tauto.
        qauto l:on use:adequacy,wne_j unfold:CR.
  - hauto l:on.
Qed.

Lemma mltt_normalizing Γ a A : (Γ ⊢ a ∈ A) -> wn a /\ wn A.
Proof.
  move => h.
  apply soundness in h.
  move : h.
  rewrite /SemWt.
  move /(_ var_tm).
  elim.
  - asimpl.
    hauto l:on use:adequacy, InterpUniv_wn_ty unfold:CR.
  - rewrite /ρ_ok.
    move=> i ? m PA. asimpl.
    hauto q:on ctrs:rtc use:adequacy.
Qed.
