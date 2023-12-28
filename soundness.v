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
  - move => Γ i γ hγ.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    hauto l:on use:InterpUnivN_Univ_inv.
  - rewrite /SemWt.
    move => // Γ i A B _ h0 _ h1 γ hγ.
    move /(_ γ hγ) : h0; intros (m & P_Univ & hP_Univ & hP_Univ').
    move /InterpUnivN_Univ_inv' : hP_Univ => [*]; subst.
    case : hP_Univ' => PA hPA.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    split; first by eauto using InterpUnivN_Univ_inv.
    exists (ProdSpace PA (fun a PB => InterpUnivN i (subst_tm (a .: γ) B) PB)).
    simp InterpUniv.
    simpl.
    apply InterpExt_Fun.
    + simp InterpUniv in hPA.
    + move => a ha.
      move /(_ _ ltac:(qauto use:γ_ok_cons)) in h1.
      move : h1; intros (x & PB & hPB & h).
      move /InterpUnivN_Univ_inv' : hPB => [*]; subst.
      hauto lq:on rew:db:InterpUniv.
    + move => a PB ha.
      by asimpl.
  - rewrite /SemWt.
    move => Γ A a B i _ hB _ ha.
    move => γ hγ.
    move /(_ γ hγ) : hB; intros (l & PPi & hPPi & hPi).
    move /InterpUnivN_Univ_inv' : hPPi => [*]; subst.
    case  : hPi => /= PPi hPPi.
    simp InterpUniv in hPPi.
    move /InterpExt_Fun_inv : hPPi. intros (PA & PF & hPA & hTot & hPF & ?); subst.
    exists i, (ProdSpace PA (fun a PB => InterpUnivN i (subst_tm (a .: γ) B) PB)).
    split.
    + simpl; simp InterpUniv.
      apply InterpExt_Fun; first by [].
      * move => a0 ha0.
        case /(_ a0 ha0) : hTot => PB hPB.
        move /(_ a0 PB hPB) in hPF.
        exists PB.
        by asimpl in hPF.
      * move => *.
        by asimpl.
    + rewrite /ProdSpace => b PB hb hPB.
      have ? : γ_ok (A :: Γ) (b .: γ) by apply : γ_ok_cons; eauto; simp InterpUniv.
      move /(_ (b .: γ) ltac:(done)) : ha.
      intros (j & PB0 & hPB0 & ha).
      have ? : PB0 = PB by hauto l:on use:InterpUnivN_deterministic'. subst.
      rewrite -InterpUnivN_nolt in hPF.
      apply : InterpUnivN_back_clos; eauto.
      apply P_AppAbs_cbn; by asimpl.
  - move => Γ f A B b _ ihf _ ihb γ hγ.
    rewrite /SemWt in ihf ihb.
    move /(_ γ hγ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ γ hγ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    rewrite InterpUnivN_nolt in hPi.
    move /InterpExt_Fun_inv : hPi;
      intros (PA0 & PF & hPA0 & hPFTot & hPF & ?); subst.
    rewrite -InterpUnivN_nolt in hPA0.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'.
    subst.
    have hPA0b : PA (subst_tm γ b) by sfirstorder.
    move /(_ _ hPA0b) : hPFTot; intros (PB & hPB).
    have hPB' := hPF _ PB hPB.
    rewrite -InterpUnivN_nolt in hPB'.
    rewrite /ProdSpace in hf.
    asimpl in *.
    hauto lq:on.
  - rewrite /SemWt => Γ a A B i _ hA _ hB [C [? ?]] γ hγ.
    case : (hA γ hγ) => j [PA [hPA hPAa]].
    case : (hB γ hγ) => k [PB [hPB hPB']].
    simpl in hPB.
    case /InterpUnivN_Univ_inv' : hPB => ? ?. subst.
    case : hPB' =>  PA0 hPA0.
    exists i, PA0.
    split; auto.
    have [*] : Pars (subst_tm γ A) (subst_tm γ C) /\
                 Pars (subst_tm γ B) (subst_tm γ C)
      by sfirstorder use:par_subst_star.
    have ? :InterpUnivN i (subst_tm γ C) PA0 by sfirstorder use:InterpUnivN_preservation_star.
    have ? :InterpUnivN i (subst_tm γ A) PA0 by sfirstorder use:InterpUnivN_back_preservation_star.
    suff : PA = PA0 by congruence.
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
      eauto using P_IfTrue_star with sets.
    + apply (InterpUnivN_back_clos_star k) with (A := (subst_tm γ A)) (b := (subst_tm γ c)) => //.
      eauto using P_IfFalse_star with sets.
  - rewrite /SemWt => Γ i γ hγ.
    simpl.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    hauto l:on use:InterpUnivN_Univ_inv.
  - move => Γ i j ? γ hγ /=.
    exists (S j), (fun A => exists PA, InterpUnivN j A PA).
    sfirstorder use:InterpUnivN_Univ_inv.
  - hauto l:on.
  - move => Γ a b A i j _ ha _ hb _ hA γ hγ/=.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    hauto l:on use:InterpUnivN_Univ_inv.
  - move => Γ t a b p A i j C _ ha _ hb _ hA _ hp _ hC _ ht.
    move => γ hγ.
    move : ha (hγ); move/[apply] => ha.
    move : hb (hγ); move/[apply] => hb.
    move : hA (hγ); move/[apply] => hA.
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
    + (* would a negative interp for tEq be possible & potentially
         simplify the proof? *)
      (* how would that affect the universe level? *)
      asimpl.
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
