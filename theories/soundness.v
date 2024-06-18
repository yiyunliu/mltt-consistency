Require Import conv par geq imports semtyping typing typing_conv normalform.

Module soundness
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import nf : normalform_sig lattice syntax par)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv)
  (Import lr : lr_sig lattice syntax par nf ieq conv).

Module pfacts := par_facts lattice syntax par.
Import pfacts.

Module lfacts := Lattice.All.Properties lattice.
Import lfacts.

Module tcfacts := typing_conv_facts lattice syntax par ieq conv typing.
Import tcfacts.

(* Semantic substitution well-formedness *)
(* Try use the existential version of ρ_ok and then derive the universal version of ρ_ok as a lemma *)
Definition ρ_ok Γ Δ ρ := forall i ℓ A, lookup i Γ ℓ A -> exists m PA, ⟦ c2e Δ ⊨ A [ρ] ⟧ m ↘ PA /\ PA ℓ (ρ i).

Lemma ρ_ok_forall Γ Δ ρ :
  ρ_ok Γ Δ ρ -> forall i ℓ A, lookup i Γ ℓ A -> forall m PA, ⟦ c2e Δ ⊨ A [ρ] ⟧ m ↘ PA -> PA ℓ (ρ i).
Proof.
  rewrite /ρ_ok => hρ.
  move => i ℓ A + m PA hPA.
  move /hρ => [m0][PA0][h0]h1.
  by have -> : PA = PA0 by eauto using InterpUnivN_deterministic'.
Qed.

(* Semantic typing, written Γ ⊨ a : A in the paper *)
Definition SemWt Γ ℓ a A := forall Δ ρ, ρ_ok Γ Δ ρ -> exists m PA, ( ⟦ c2e Δ ⊨ A [ρ] ⟧ m ↘ PA)  /\ PA ℓ (a [ρ]).

(* Semantic context wellformedness *)
Inductive SemWff : context -> Prop :=
| SemWff_nil :
(* ----------------- *)
  SemWff nil
| SemWff_cons Γ ℓ0 ℓ A i :
  SemWff Γ ->
  SemWt Γ ℓ A (tUniv i) ->
(* ----------------- *)
  SemWff ((ℓ0, A) :: Γ).

(* TODO: Fix the order of the arguments of iok_subst_ok *)
Lemma ρ_ok_iok Γ Δ ρ (h : ρ_ok Γ Δ ρ) :
  iok_subst_ok ρ (c2e Γ) (c2e Δ).
Proof.
  rewrite /ρ_ok in h.
  rewrite /iok_subst_ok.
  hauto l:on use:InterpUniv_Ok, elookup_lookup.
Qed.

Lemma ρ_ok_nil ρ : ρ_ok nil nil ρ.
Proof.  rewrite /ρ_ok. inversion 1; subst. Qed.

Lemma ρ_ok_cons i Γ Δ ℓ0 ρ a PA A :
 (⟦ c2e Δ ⊨ A [ρ] ⟧ i ↘ PA) -> PA ℓ0 a ->
  ρ_ok Γ Δ ρ ->
  ρ_ok ((ℓ0, A) :: Γ) Δ (a .: ρ).
Proof.
  move => h0 h1 h2.
  rewrite /ρ_ok. move => i0 ℓ A0.
  elim /lookup_inv=>//=.
  - move => _ ℓ1 A1 Γ0 ? [*]. subst.
    exists i, PA.
    asimpl.
    tauto.
  - move => ? n A1 Γ0 ℓ1 [ℓ2 B] ? ? [*]. subst.
    asimpl.
    sfirstorder.
Qed.

(* Well-formed substitutions are stable under renaming *)
Lemma ρ_ok_renaming Γ Ξ ρ :
  forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    ρ_ok Δ Ξ ρ ->
    ρ_ok Γ Ξ (ξ >> ρ).
Proof.
  move => Δ ξ hscope h1.
  rewrite /ρ_ok => i ℓ A hi.
  move /hscope: hi => ld.
  move /h1 : ld.
  by asimpl.
Qed.

(* Typing is stable under renaming *)
Lemma renaming_SemWt Γ ℓ a A :
  (SemWt Γ ℓ a A) ->
  forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    SemWt Δ ℓ a⟨ξ⟩ A⟨ξ⟩ .
Proof.
  rewrite /SemWt => h Δ ξ hξ Ξ ρ hρ.
  have hρ' : (ρ_ok Γ Ξ (ξ >> ρ)) by eauto using ρ_ok_renaming.
  case /(_ _ _ hρ') : h => PA hPA.
  exists PA. by asimpl.
Qed.

Lemma weakening_Sem Γ ℓ ℓ0 ℓ1 a A B i
  (h0 : SemWt Γ ℓ0 B (tUniv i))
  (h1 : SemWt Γ ℓ a A) :
   SemWt ((ℓ1, B) :: Γ) ℓ (a ⟨S⟩) (A ⟨S⟩).
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on ctrs:lookup unfold:lookup_good_renaming.
Qed.

(* Well-formed types have interpretations *)
Lemma SemWt_Univ Γ ℓ A i :
  (SemWt Γ ℓ A (tUniv i)) <->
  forall Ξ ρ, ρ_ok Γ Ξ ρ -> IOk (c2e Ξ) ℓ A[ρ] /\ exists S , ⟦ c2e Ξ ⊨ A[ρ] ⟧ i ↘ S.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUnivN_Univ_inv.
  - move => /[swap] Δ /[swap]  ρ /[apply].
    case => PA hPA.
    exists (S i). eexists.
    split.
    + simp InterpUniv. apply InterpExt_Univ. lia.
    + hauto lq:on.
Qed.

Lemma SemWff_lookup Γ (h : SemWff Γ) : forall i ℓ A, lookup i Γ ℓ A -> exists ℓ0 j, SemWt Γ ℓ0 A (tUniv j).
Proof.
  elim : Γ / h.
  - inversion 1.
  - move => Γ ℓ0 ℓ A i hΓ ihΓ hA i0 ℓ1 A0.
    elim/lookup_inv=>_.
    + move => ℓ2 A1 Γ0 ? [*]. subst.
      exists ℓ, i.
      change (tUniv i) with (tUniv i)⟨S⟩.
      apply : renaming_SemWt; eauto.
      rewrite /lookup_good_renaming.
      hauto l:on.
    + move => n A1 Γ0 ℓ2 B + ? [*]. subst.
      move /ihΓ.
      move => [ℓ2][j]h.
      exists ℓ2, j.
      change (tUniv j) with (tUniv j)⟨S⟩.
      apply : renaming_SemWt; eauto.
      rewrite /lookup_good_renaming.
      hauto l:on.
Qed.

Lemma wt_ρ_ok_morphing_iok Γ Δ ρ ℓ a A (h : Γ ⊢ a ; ℓ ∈ A) (h0 : ρ_ok Γ Δ ρ) : IOk (c2e Δ) ℓ a[ρ].
Proof.
  eauto using cfacts.ifacts.iok_morphing, typing_iok, ρ_ok_iok.
Qed.

(* Fundamental theorem: Syntactic typing implies semantic typing *)
Theorem soundness :
  (forall Γ ℓ a A, Wt Γ ℓ a A -> SemWt Γ ℓ a A) /\
  (forall Γ, Wff Γ -> SemWff Γ).
Proof.
  apply wt_mutual.
  (* Var *)
  - move => Γ ℓ0 ℓ i A h /SemWff_lookup ih l hℓ Ξ ρ hρ.
    rewrite /SemWff in ih.
    move /ih : (l) {ih} => [ℓ1 [j ih]].
    rewrite SemWt_Univ in ih.
    move /ih : (hρ) => {ih} [? [PA h1]].
    exists j, PA. split=>//.
    asimpl.
    move /ρ_ok_forall : hρ l (h1) => /[apply]/[apply].
    hauto lq:on use:InterpUnivN_subsumption.
  (* Pi *)
  - move => Γ i j ℓ ℓ0 A B ? /SemWt_Univ h0 ? /SemWt_Univ h1.
    apply SemWt_Univ.
    move => Ξ ρ hρ.
    move /(_ Ξ ρ hρ) : h0; intros (? & PA & hPA).
    split.
    + have /typing_iok : Wt Γ ℓ (tPi ℓ0 A B) (tUniv (max i j)) by hauto lq:on ctrs:Wt.
      move /ρ_ok_iok : hρ.
      by move /cfacts.ifacts.iok_morphing /[apply].
    + eexists => //=.
      apply InterpUnivN_Fun_nopf.
      move /InterpUnivN_cumulative : hPA. apply. lia.
      move => *; asimpl.
      hauto lq:on use:ρ_ok_cons, InterpUnivN_cumulative solve+:(lia).
  (* Abs *)
  - move => Γ ℓ ℓ0 ℓ1 A b B i ? /SemWt_Univ hB ? hb Δ ρ hρ.
    move /(_ _ ρ hρ) : hB => /= [? [PPi hPPi]].
    exists i, PPi. split => //.
    move /InterpUnivN_Fun_inv_nopf : hPPi.
    move => [PA][?][hTot]?. subst.
    rewrite /ProdSpace.
    move => [:habs].
    split.
    + abstract : habs.
      suff : Wt Γ ℓ (tAbs ℓ0 b) (tPi ℓ0 A B) by hauto lq:on use:wt_ρ_ok_morphing_iok.
      qauto l:on ctrs:Wt.
    + move => a PB ha. asimpl => hPB.
      have : ρ_ok ((ℓ0, A) :: Γ) Δ (a .: ρ) by eauto using ρ_ok_cons.
      move /hb.
      intros (m & PB0 & hPB0 & hPB0').
      replace PB0 with PB in * by hauto l:on use:InterpUnivN_deterministic'.
      apply : InterpUnivN_back_clos; eauto.
      have ? : IOk (c2e Δ) ℓ0 a by hauto l:on use:InterpUniv_Ok.
      apply IO_App; auto.
      apply : P_AppAbs_cbn. by asimpl.
  (* App *)
  - move => Γ ℓ ℓ0 f A B b _ ihf _ ihb Δ ρ hρ.
    rewrite /SemWt in ihf ihb.
    move /(_ _ _ hρ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ _ _ hρ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    move /InterpUnivN_Fun_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'. subst.
    move : hf => [?].
    move  : (hb) => /[swap] /[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  (* Conv *)
  - move => Γ ℓ ℓ0 a A B i _ ha _ /SemWt_Univ hB hconv Δ ρ hρ.
    move /ρ_ok_iok : (hρ) => ?.
    move : hB (hρ) => /[apply].
    move : ha hρ => /[apply].
    move => [m][PA][hPA]ha.
    move => [?][PB]hPB.
    have hs : conv (c2e Δ) (subst_tm ρ A) (subst_tm ρ B).
    by hauto l:on use:cfacts.conv_subst.
    have [j [hm hi]] : exists j,  m <= j /\ i <= j by exists (S (max m i)); lia.
    move : InterpUnivN_cumulative hPA hm; repeat move/[apply].
    move : InterpUnivN_cumulative hPB hi; repeat move/[apply].
    move => *.
    have ? : PB = PA by eauto using InterpUnivN_Conv. subst.
    hauto lq:on.
  (* Univ *)
  - move => Γ ℓ i _ hΓ.
    rewrite SemWt_Univ.
    move => Ξ ρ hρ.
    split.
    hauto l:on.
    eexists=>/=.
    apply : InterpUnivN_Univ. lia.
  (* Void *)
  - hauto lq:on ctrs:IOk use:InterpUnivN_Void, SemWt_Univ.
  (* Absurd *)
  - move => Γ ℓ ℓ0 ℓ1 i a A ha iha hA /SemWt_Univ ihA Δ ρ hρ /=.
    move /iha : (hρ).
    move => [m][PA][/InterpUnivN_Void_inv hPA]ha'. subst.
    move /ihA : (hρ).
    move => [hA'][PA]hPA.
    exists i,PA. split => //.
    hauto lq:on use:nfacts.wne_absurd, adequacy unfold:SemWt.
  (* Refl *)
  - move => Γ ℓ a ℓ0 A hΓ _ /typing_iok /cfacts.ifacts.iok_ieq.
    rewrite /SemWt.
    move => ha iha Δ ρ hρ.
    move /iha : (hρ) {iha} => [m][PA][hPA]ha'.
    have ? : wn a[ρ] by hauto lq:on use:adequacy.
    have ? : wn A[ρ] by hauto lq:on use:adequacy.
    do 2 eexists.
    split => //=. apply (InterpUnivN_Eq _ 0)=>//.
    simpl.
    repeat split.
    sfirstorder.
    left.
    split.
    by apply rtc_refl.
    move /ρ_ok_iok : hρ.
    move /(_ ℓ0 ltac:(by rewrite meet_idempotent)) : ha.
    move /cfacts.ieq_iconv.
    hauto lq:on use:cfacts.iconv_subst.
  (* Eq *)
  - move => Γ ℓ ℓ0 a b A i j hℓ ha iha hb ihb hA /SemWt_Univ ihA.
    rewrite SemWt_Univ.
    move => Ξ ρ hρ.
    move : iha (hρ) => /[apply] ?.
    move : ihb (hρ) => /[apply] ?.
    move : ihA (hρ) => /[apply] ?.
    split.
    + have /typing_iok : Γ ⊢ tEq ℓ0 a b A ; ℓ ∈ tUniv i by hauto l:on use:T_Eq.
      hauto lq:on ctrs:IEq use:cfacts.ifacts.iok_morphing, cfacts.iconv_subst, ρ_ok_iok.
    + eexists => //=. apply InterpUnivN_Eq; hauto lq:on dep:on use:adequacy.
  (* J *)
  - move => Γ t a b p A i j C ℓ ℓp ℓA ℓ0 ℓ1 ? ?.
    move => _ha ha _hb hb hA ihA _hp hp hC /SemWt_Univ ihC _t ht.
    have hJ : exists A, Γ ⊢ tJ t p; ℓ ∈ A by hauto l:on use:T_J.
    move => Δ ρ hρ.
    move : hp (hρ); move/[apply] => /=. intros (m & PA & hPA & hp).
    move  /InterpUnivN_Eq_inv : (hPA) (hp) ->.  move => [?].
    have hρ' : ρ_ok  ((ℓp, tEq ℓ0 a ⟨S⟩ (var_tm 0) A ⟨S⟩) :: (ℓ1, A) :: Γ) Δ (p[ρ] .: (b[ρ] .: ρ)).
    {
      apply : ρ_ok_cons => //=.
      asimpl.
      by apply hPA.
      by eauto.
      move : hb (hρ) => /[apply].
      move => [m0][PA0][hb0]hb1.
      apply : ρ_ok_cons => //=.
      apply hb0.
      done.
    }
    move /ihC : (hρ').
    move => [hCp][PC]hPC.
    case.
    + move => [?]hab{hp}{hPA}{PA}.
       move : ht (hρ); move/[apply]. intros (k & PA & hPA & ht).
       exists i, PA.
       split.
      * move : hPA. asimpl => /[dup] hPA.
        have : iconv (c2e Δ) ℓ0 C[p[ρ] .: (b[ρ] .: ρ)] C[tRefl .: (a[ρ] .: ρ)].
        rewrite /iconv.
        move : hab => [a'][b']hab.
        exists C[tRefl .: (b' .: ρ)], C[tRefl .: (a' .: ρ)].
        repeat split.
        ** apply : Pars_morphing_star; auto using rtc_refl.
           apply good_Pars_morphing_ext2; hauto lq:on ctrs:rtc.
        ** apply : Pars_morphing_star; auto using rtc_refl.
           apply good_Pars_morphing_ext2; hauto lq:on ctrs:rtc.
        ** move /typing_iok : hC.
           simpl.
           move /cfacts.ifacts.iok_ieq => /[dup] hC.
           move  /(_ ℓ0 ltac:(by rewrite meet_idempotent)) /(proj1 (cfacts.ifacts.ieq_morphing_mutual _ _)).
           apply.
           rewrite /cfacts.ifacts.ieq_good_morphing.
           rewrite /elookup.
           case => //=.
           *** move => ℓ2 [*]. subst.
               apply cfacts.ifacts.ieq_gieq.
               hauto lq:on ctrs:IEq.
           *** case => ℓ2 //=.
               **** move => [?]. subst.
                    case : (sub_eqdec ℓ2 ℓ0).
                    move => ?.
                    apply GI_Dist=>//.
                    apply cfacts.ifacts.ieq_sym_mutual. tauto.
                    move => ?. apply GI_InDist=>//.
               **** suff : iok_subst_ok ρ (c2e Γ) (c2e Δ).
                    rewrite /iok_subst_ok.
                    rewrite /elookup.
                    sauto lq:on rew:off use:cfacts.ifacts.iok_gieq.
                    hauto l:on use:ρ_ok_iok.
        ** move /cfacts.iconv_conv.
           move /cfacts.conv_sym.
           move : InterpUnivN_Conv (hPC); repeat move/[apply].
           by move => <-.
      * eapply InterpUnivN_back_clos_star with (b := subst_tm ρ t); eauto. simpl.
      apply : IO_J; eauto.
      move /typing_iok : _t.
      hauto lq:on use:ρ_ok_iok, cfacts.ifacts.iok_morphing.
      sfirstorder use: P_JRefl_star.
    + move => h.
      do 2 eexists.
      split.
      asimpl. apply hPC.
      suff : wne (tJ t[ρ] p[ρ]) /\ IOk (c2e Δ) ℓ (tJ t p)[ρ] by hauto q:on use:adequacy.
      split.
      apply nfacts.wne_j => //.
      move /ht : (hρ).
      hauto q:on use:adequacy.
      hauto l:on use:wt_ρ_ok_morphing_iok.
  (* Sig *)
  - move => Γ i j ℓ ℓ0 A B ? /SemWt_Univ h0 ? /SemWt_Univ h1.
    apply SemWt_Univ.
    move => Ξ ρ hρ.
    move /(_ Ξ ρ hρ) : h0; intros (? & PA & hPA).
    split.
    + have /typing_iok : Wt Γ ℓ (tSig ℓ0 A B) (tUniv (max i j)) by hauto lq:on ctrs:Wt.
      move /ρ_ok_iok : hρ.
      by move /cfacts.ifacts.iok_morphing /[apply].
    + eexists => //=.
      apply InterpUnivN_Sig_nopf; eauto.
      hauto lq:on use:InterpUnivN_cumulative solve+:lia.
      move => *; asimpl.
      hauto lq:on use:ρ_ok_cons,InterpUnivN_cumulative solve+:lia.
  (* Pack *)
  - move => Γ ℓ ℓ0 a A b B ℓT i _ ha _ hb _ /SemWt_Univ hB Δ ρ hρ.
    move /ha : (hρ) => [m][PA][ha0]ha1.
    move /hb : (hρ) => [m0][PB][hb0]hb1.
    move /hB : (hρ) => [hS'][S]/=hS.
    exists i, S => /=.
    split => //.
    move /InterpUnivN_Sig_inv_nopf : hS => [PA0][hPA0][hPB0]?. subst.
    rewrite /SumSpace.
    split => //.
    qauto l:on use:InterpUniv_Ok, IO_Pack. left.
    do 2 eexists. split; first by apply rtc_refl.
    have ? : PA = PA0 by eauto using InterpUnivN_deterministic'. subst.
    split => // PB0. asimpl.
    move /hPB0 :ha1.
    move => [PB1]. asimpl => *.
    asimpl in hb0.
    have [*] : PB = PB1 /\ PB0 = PB1 by  eauto using InterpUnivN_deterministic'.
    congruence.
  (* Let *)
  - move => Γ ℓ ℓp ℓ0 t b ℓT A B C i ?  ? ? ? ? ? ? ht ? hb ? /SemWt_Univ hC Δ ρ hρ.
    move /ht : (hρ) {ht} => [m][PA][/= /[dup] hSig /InterpUnivN_Sig_inv_nopf].
    move => [PA0][h0][h1]?. subst.
    rewrite /SumSpace.
    move => [?].
    case.
    + move => [a0][b0][h2][h3]h4.
      have : ρ_ok ((ℓp , tSig ℓ0 A B) :: Γ) Δ ((tPack ℓ0 a0 b0) .: ρ).
      {
        apply : ρ_ok_cons; eauto.
        rewrite /SumSpace.
        split; last by hauto l:on use:InterpUnivN_Sig_nopf.
        hauto q:on ctrs:IOk use:InterpUniv_Ok.
      }
      move /hC => [?][S] hS {hC}.
      exists i, S. split=>//.
      asimpl.
      move /InterpUnivN_back_preservation_star : (hS). apply.
      qauto l:on use:Pars_morphing_star,good_Pars_morphing_ext ctrs:rtc.
      apply : InterpUnivN_back_clos_star; eauto.
      * suff : exists A, Wt Γ ℓ (tLet ℓ0 ℓp t b) A by hauto lq:on use:wt_ρ_ok_morphing_iok.
        hauto q:on ctrs:Wt.
      * apply P_LetPack_star; eauto.
      * asimpl.
        have ?: ρ_ok ((ℓ0, A) :: Γ) Δ (a0 .: ρ) by eauto using ρ_ok_cons.
        move /h1 : (h3) => [PB] /[dup] hPB.
        move /h4 => ?.
        asimpl in hPB.
        have : ρ_ok ((ℓp, B) :: (ℓ0, A) :: Γ) Δ (b0 .: (a0 .: ρ)) by eauto using ρ_ok_cons.
        move /hb => [m0][PA]. asimpl. move => [hPA] hPA0.
        by have <- : PA = S by eauto using InterpUnivN_deterministic'.
    + move => h.
      have /hC : ρ_ok ((ℓp, tSig ℓ0 A B) :: Γ) Δ (t[ρ] .: ρ) by
        apply : ρ_ok_cons; hauto lq:on use:adequacy.
      move => [? [S hS]].
      exists i, S. asimpl; split => //.
      set a := (X in S ℓ X).
      suff : wne a /\ IOk (c2e Δ) ℓ a by hauto q:on use:adequacy.
      subst a.
      split.
      * apply nfacts.wne_let=>//.
        have hz : wne tD by hauto lq:on ctrs:rtc.
        have hz' : PA0 ℓ0 tD by move : h0 hz; clear; hauto lq:on ctrs:IOk use:adequacy unfold:CR.
        apply nfacts.wn_antirenaming with (ξ := tD .: (tD ..)).
        by do 2 case => //=.
        asimpl.
        have hρ' : ρ_ok ((ℓ0, A) :: Γ) Δ (tD .: ρ) by eauto using ρ_ok_cons.
        move /h1 : hz' => [PB /ltac:(asimpl) hPB].
        have hz'' : PB ℓp tD by move : hPB hz; clear; hauto lq:on use:adequacy unfold:CR.
        have : ρ_ok ((ℓp, B) :: (ℓ0, A) :: Γ) Δ (tD .: (tD .: ρ)) by eauto using ρ_ok_cons.
        move /hb. clear.
        hauto l:on use:adequacy unfold:CR.
      * lazymatch goal with
        | [|- context[IOk _ _ ?a]] =>
            have -> : a = (tLet ℓ0 ℓp t b)[ρ] by asimpl
        end.
        apply : wt_ρ_ok_morphing_iok; eauto.
        sfirstorder use:T_Let.
  (* Nil *)
  - apply SemWff_nil.
  (* Cons *)
  - eauto using SemWff_cons.
Qed.

Lemma comp_const (ξ0 : fin -> fin) (a : tm) : ξ0 >> (const a) = const a.
Proof.
  fext => x. asimpl => //=.
Qed.

Lemma ρ_ok_id Γ : ⊢ Γ -> ρ_ok Γ nil (const tD).
Proof.
  move => h.
  have {}h : SemWff Γ by firstorder using soundness.
  elim : Γ / h.
  - inversion 1.
  - move => Γ ℓ0 ℓ A i hΓ ihΓ hA.
    rewrite /ρ_ok.
    move => i0 ℓ1 A0.
    elim/lookup_inv => _.
    + move => ℓ2 A1 Γ0 ? [*]. subst.
      move : (hA) (ihΓ) => /[apply].
      simpl. asimpl.
      move => [m][PA][hPA]hA'.
      exists m,PA. rewrite comp_const.

      suff : exists PA, InterpUnivN (ℓ1 :: c2e Γ) m A⟨S⟩ PA.
      move => [PA0]hPA0.
      exists m, PA0.
      split => //.
      eapply adequacy in hPA0.
      eapply hPA0.
      hauto lq:on ctrs:rtc.
      apply : IO_Var.
      sfirstorder unfold:elookup.
      by rewrite meet_idempotent.
      split; last by best use:adequacy.
      apply :
    best use:


Lemma mltt_normalizing Γ a ℓ A : Γ ⊢ a ; ℓ ∈ A -> wn a /\ wn A.
Proof.
  move /(proj1 soundness) /(_ Γ var_tm).
  elim.
  - asimpl.
    hauto l:on use:adequacy unfold:CR.
  - rewrite /ρ_ok=>i ? m PA. asimpl.
    hauto q:on ctrs:rtc use:adequacy.
Qed.


Lemma consistency ℓ a : ~ nil ⊢ a ; ℓ ∈ tVoid.
  move /(proj1 soundness).
  have := (ρ_ok_nil var_tm) => /[swap]/[apply].
  sfirstorder use:InterpUnivN_Void_inv.
Qed.


(* (* Need to prove something about scoping before we can recover consistency *) *)
(* Inductive stm (n : nat) : tm -> Prop := *)
(* | SC_Var i : *)
(*   i < n -> *)
(*   (* ----- *) *)
(*   stm n (var_tm i) *)

(* | SC_Abs b : *)
(*   stm (S n) b -> *)
(*   (* ------------ *) *)
(*   stm n (tAbs b) *)

(* | SC_App a b : *)
(*   stm n a -> *)
(*   stm n b -> *)
(*   (* ---------- *) *)
(*   stm n (tApp a b) *)

(* | SC_Pi A B : *)
(*   stm n A -> *)
(*   stm (S n) B -> *)
(*   (* ------------ *) *)
(*   stm n (tPi A B) *)

(* | SC_Univ i : *)
(*   (* ----------- *) *)
(*   stm n (tUniv i) *)

(* | SC_Zero : *)
(*   (* --------- *) *)
(*   stm n tZero *)

(* | SC_Suc a : *)
(*   stm n a -> *)
(*   (* -------------- *) *)
(*   stm n (tSuc a) *)

(* | SC_Nat : *)
(*   (* -------------- *) *)
(*   stm n tNat *)

(* | SC_Eq a b A : *)
(*   stm n a -> *)
(*   stm n b -> *)
(*   stm n A -> *)
(*   (* ---------------- *) *)
(*   stm n (tEq a b A) *)

(* | SC_J t a b p : *)
(*   stm n t -> *)
(*   stm n a -> *)
(*   stm n b -> *)
(*   stm n p -> *)
(*   (* ------------- *) *)
(*   stm n (tJ t a b p) *)

(* | SC_Ind a b c : *)
(*   stm n a -> *)
(*   stm (2 + n) b -> *)
(*   stm n c -> *)
(*   stm n (tInd a b c) *)

(* | SC_Refl : *)
(*   (* --------- *) *)
(*   stm n tRefl *)

(* | SC_Pack a b : *)
(*   stm n a -> *)
(*   stm n b -> *)
(*   (* ------------- *) *)
(*   stm n (tPack a b) *)

(* | SC_Sig A B : *)
(*   stm n A -> *)
(*   stm (S n) B -> *)
(*   (* ------------ *) *)
(*   stm n (tSig A B) *)

(* | SC_Let a b : *)
(*   stm n a -> *)
(*   stm (S (S n)) b -> *)
(*   (* -------------- *) *)
(*   stm n (tLet a b). *)

(* #[export]Hint Constructors stm : stm. *)


(* Lemma scope_lt n a : stm n a -> forall m, n <= m -> stm m a. *)
(* Proof. move => h. elim : a / h; hauto lq:on ctrs:stm solve+:lia. Qed. *)

(* Lemma ne_scope a : ne a -> forall n, stm n a -> n > 0. *)
(* Proof. elim : a; hauto q:on inv:stm b:on solve+:lia. Qed. *)

(* Lemma lookup_lt i A Γ : lookup i Γ A -> i < length Γ. *)
(* Proof. move => h. elim : i Γ A / h; sfirstorder. Qed. *)

(* Lemma wt_scope Γ a A : Γ ⊢ a ∈ A -> stm (length Γ) a. *)
(* Proof. move => h. elim : Γ a A / h; hauto use:lookup_lt q:on ctrs:stm. Qed. *)

(* Lemma scope_ren_up n m ξ : *)
(*   (forall i, i < n -> ξ i < m) ->  forall i, i < S n -> upRen_tm_tm ξ i < S m. *)
(* Proof. *)
(*   move => h. *)
(*   case => [|p]. *)
(*   - asimpl. lia. *)
(*   - move : (h p). asimpl. lia. *)
(* Qed. *)

(* Lemma scope_renaming n a (h : stm n a) : *)
(*   forall m ξ, (forall i, i < n -> ξ i < m) -> stm m (ren_tm ξ a). *)
(* Proof. *)
(*   elim : a / h=>//=; eauto 10 using scope_ren_up with stm. *)
(* Qed. *)

(* Lemma scope_weaken m a : stm m a -> stm (S m) (ren_tm shift a). *)
(* Proof. move /scope_renaming. apply. lia. Qed. *)

(* Lemma scope_morphing_up n m ρ : *)
(*   (forall i, i < n -> stm m (ρ i)) -> *)
(*   forall i, i < S n -> stm (S m) (up_tm_tm ρ i). *)
(* Proof. *)
(*   move => h. *)
(*   case. *)
(*   asimpl. hauto lq:on ctrs:stm solve+:lia. *)
(*   hauto lq:on use:scope_weaken simp+:asimpl solve+:lia. *)
(* Qed. *)

(* Lemma scope_morphing n a (h : stm n a) : *)
(*   forall m ρ, (forall i, i < n -> stm m (ρ i)) -> stm m (subst_tm ρ a). *)
(* Proof. *)
(*   elim : n a / h=>//=; eauto 10 using scope_morphing_up with stm. *)
(* Qed. *)

(* Lemma scope_subst n a b (h : stm (S n) a) (h0 : stm n b) : *)
(*   stm n (subst_tm (b..) a). *)
(* Proof. *)
(*   apply scope_morphing with (n := S n)=>//. *)
(*   case. *)
(*   by asimpl. move => p. asimpl. *)
(*   hauto lq:on ctrs:stm solve+:lia. *)
(* Qed. *)

(* Lemma Par_scope a b (h : a ⇒ b) : forall n, stm n a -> stm n b. *)
(* Proof. *)
(*   elim : a b / h; *)
(*     match goal with *)
(*     | [|-context[subst_tm]] => idtac *)
(*     | _ => hauto lq:on inv:stm ctrs:stm *)
(*     end. *)
(*   - hauto lq:on inv:stm ctrs:stm use:scope_subst. *)
(*   - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc n hi. *)
(*     inversion hi; subst. *)
(*     apply scope_morphing with (n := 2 +  n);simpl;  eauto. *)
(*     case => [_|]. *)
(*     + hauto lq:on inv:stm ctrs:stm. *)
(*     + case => [_|]/=. *)
(*       hauto lq:on inv:stm. *)
(*       move => n0 h. *)
(*       have {h}: n0 < n by lia. *)
(*       hauto lq:on ctrs:stm. *)
(*   - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc n hi. *)
(*     inversion hi; subst. *)
(*     apply scope_morphing with (n := 2 +  n);simpl;  eauto. *)
(*     case => [_|]. *)
(*     + asimpl. apply ihb. move : hi. clear. qauto l:on inv:stm. *)
(*     + case => [_|]/=. apply iha. *)
(*       move : hi. clear. qauto l:on inv:stm. *)
(*       move => m h. *)
(*       have {}h : m < n by lia. *)
(*       hauto lq:on ctrs:stm. *)
(* Qed. *)

(* Lemma Pars_scope a b (h : a ⇒* b) : forall n, stm n a -> stm n b. *)
(* Proof. elim : a b / h; sfirstorder use:Par_scope. Qed. *)

(* Lemma consistency a : ~ nil ⊢ a ∈ tEq tZero (tSuc tZero) tNat. *)
(* Proof. *)
(*   move => /[dup] /wt_scope /= h. *)
(*   move /(proj1 soundness). *)
(*   rewrite /SemWt. *)
(*   have : ρ_ok nil var_tm by *)
(*     hauto lq:on inv:lookup unfold:ρ_ok. *)
(*   move/[swap]/[apply]. *)
(*   move => [m][PA][]. *)
(*   move /InterpUnivN_Eq_inv => [->]_[[_/Coherent_consistent]|[v[/Pars_scope]]]//. *)
(*   asimpl. move /(_ 0 h). move/ne_scope/[apply]. lia. *)
(* Qed. *)
End soundness.
