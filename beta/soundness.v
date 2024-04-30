From WR Require Import syntax join semtyping typing imports.


(* Semantic substitution well-formedness *)
Definition ρ_ok Γ ρ := forall i A, lookup i Γ A -> forall m PA, ⟦ A [ρ] ⟧ m ↘ PA -> PA (ρ i).

(* Semantic typing, written Γ ⊨ a : A in the paper *)
Definition SemWt Γ a A := forall ρ, ρ_ok Γ ρ -> exists m PA, ( ⟦ A [ρ] ⟧ m ↘ PA)  /\ PA (a [ρ]).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

(* Semantic context wellformedness *)
Definition SemWff Γ := forall i A, lookup i Γ A -> exists j, Γ ⊨ A ∈ tUniv j.
Notation "⊨ Γ" := (SemWff Γ) (at level 70).


Lemma ρ_ok_nil ρ :
  ρ_ok nil ρ.
Proof.  rewrite /ρ_ok. inversion 1; subst. Qed.

(* Extending a well-formed substitution *)
Lemma ρ_ok_cons {i Γ ρ a PA A} :
  ⟦ A [ρ] ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (A :: Γ) (a .: ρ).
Proof.
  move => h0 h1 h2 m B.
  intros l. inversion l; subst.
  - move=> m PA0 hPA0.
    asimpl in hPA0.
    suff : PA = PA0 by congruence.
    hauto lq:on use:InterpUnivN_deterministic'.
  - asimpl.
    hauto lq:on unfold:ρ_ok.
Qed.

(* Well-formed substitutions are stable under renaming *)
Lemma ρ_ok_renaming Γ ρ :
  forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    ρ_ok Δ ρ ->
    ρ_ok Γ (ξ >> ρ).
Proof.
  move => Δ ξ hscope h1.
  rewrite /ρ_ok => i A hi j PA.
  move: (hscope _ _ hi) => ld.
  move: (h1 _ _ ld j PA).
  by asimpl.
Qed.

(* Typing is stable under renaming *)
Lemma renaming_SemWt Γ a A :
  (Γ ⊨ a ∈ A) ->
  forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    Δ ⊨ a⟨ξ⟩ ∈ A⟨ξ⟩ .
Proof.
  rewrite /SemWt => h Δ ξ hξ ρ hρ.
  have hρ' : (ρ_ok Γ (ξ >> ρ)) by eauto using ρ_ok_renaming.
  case /(_ _ hρ') : h => PA hPA.
  exists PA. by asimpl.
Qed.

Lemma weakening_Sem Γ a A B i
  (h0 : Γ ⊨ B ∈ tUniv i)
  (h1 : Γ ⊨ a ∈ A) :
   B :: Γ ⊨ a ⟨↑⟩ ∈ A ⟨↑⟩.
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on ctrs:lookup unfold:lookup_good_renaming.
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
    + simpl. eauto.
Qed.

(* Structural laws for Semantic context wellformedness *)
Lemma SemWff_nil : SemWff nil. inversion 1. Qed.

Lemma SemWff_cons Γ A i :
    ⊨ Γ ->
    Γ ⊨ A ∈ tUniv i ->
    (* -------------- *)
    ⊨ A :: Γ.
Proof.
  move => h h0.
  move => k h1. elim/lookup_inv.
  - hauto q:on use:weakening_Sem.
  - move => _ n A0 Γ0 B + ? []*. subst. move /h => [j ?].
    exists j. change (tUniv j) with (tUniv j) ⟨↑⟩.
    eauto using weakening_Sem.
Qed.

Lemma InterpUnivN_cumulative' i A PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  move => ? j h.
  have {}h : i < j \/ i = j by lia.
  hauto q:on use:InterpUnivN_cumulative.
Qed.

(* Fundamental theorem: Syntactic typing implies semantic typing *)
Theorem soundness :
  (forall Γ a A, Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A) /\
  (forall Γ, ⊢ Γ -> ⊨ Γ).
Proof.
  apply wt_mutual.
  (* Var *)
  - move => Γ i A h ih l ρ hρ.
    move /(_ i ltac:(done) ltac:(auto)) in ih.
    case : ih => j ih.
    rewrite -> SemWt_Univ in ih.
    move: (ih _ hρ) => [PA h1].
    exists j. exists PA. split. auto.
    move: (hρ _ _ l _ _ h1).
    by asimpl.
  (* Void *)
  - hauto l:on use:SemWt_Univ.
  (* Pi *)
  - move => Γ i j A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => ρ hρ.
    move /(_ ρ hρ) : h0; intros (PA & hPA).
    eexists => /=.
    have ? : i <= max i j /\ j <= max i j by lia.
    apply InterpUnivN_Fun_nopf; eauto.
    hauto l:on use:InterpUnivN_cumulative'.
    move => *; asimpl.
    hauto lq:on use:InterpUnivN_cumulative', ρ_ok_cons.
  (* Abs *)
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
  (* App *)
  - move => Γ f A B b _ ihf _ ihb ρ hρ.
    rewrite /SemWt in ihf ihb.
    move /(_ ρ hρ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ ρ hρ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    move /InterpUnivN_Fun_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'. subst.
    move  : hf (hb). move/[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  (* Conv *)
  - move => Γ a A B i _ hA _ /SemWt_Univ hB ? ρ hρ.
    have ? : Coherent (subst_tm ρ A) (subst_tm ρ B)
      by eauto using Coherent_subst_star.
    qauto l:on use:InterpUnivN_Coherent unfold:SemWt.
  (* True *)
  - hauto l:on.
  (* False *)
  - hauto l:on.
  (* If *)
  - rewrite /SemWt => Γ a b c A i _ /SemWt_Univ hA _ ha _ hb _ hc ρ hρ.
    case /(_ ρ hρ) : ha => ? [PBool [hPBool ha']]; subst.
    have hρ' : ρ_ok (tBool :: Γ) (subst_tm ρ a .: ρ) by eauto using ρ_ok_cons.
    move /InterpUnivN_Bool_inv : hPBool => ?. subst.
    case /(_ ρ hρ) : hb => ia [PA [hPA hb']].
    case /(_ ρ hρ) : hc => ib [PB [hPB hc']].
    move : hA hρ'; move/[apply]. move  => [PA0 hPA0].
    exists i, PA0.
    split; first by asimpl.
    case : ha' => v [hred hv].
    asimpl in *.
    case : v hred hv => // ha0 _.
    + move => [:t].
      apply (InterpUnivN_back_clos_star i) with (A := (subst_tm (tTrue .: ρ) A)) (b := (subst_tm ρ b)) => //.
      abstract : t.
      apply InterpUnivN_preservation_star with (B := subst_tm (tTrue .: ρ) A) in hPA0=>//.
      hauto lq:on ctrs:rtc use:Pars_morphing_star, good_Pars_morphing_ext.
      by apply P_IfTrue_star.
      suff : PA = PA0 by congruence.
      hauto lq:on use:InterpUnivN_deterministic'.
    + move => [:t].
      apply (InterpUnivN_back_clos_star i) with (A := (subst_tm (tFalse .: ρ) A)) (b := (subst_tm ρ c)) => //.
      abstract : t.
      apply InterpUnivN_preservation_star with (B := subst_tm (tFalse .: ρ) A) in hPA0=>//.
      hauto lq:on ctrs:rtc use:Pars_morphing_star, good_Pars_morphing_ext.
      by apply P_IfFalse_star.
      suff : PB = PA0 by congruence.
      hauto lq:on use:InterpUnivN_deterministic'.
  (* Bool *)
  - hauto l:on use:SemWt_Univ.
  (* Univ *)
  - hauto lq:on use:InterpUnivN_Univ_inv, SemWt_Univ.
  (* Refl *)
  - hauto l:on.
  (* Eq *)
  - hauto l:on use:SemWt_Univ.
  (* J *)
  - move => Γ t a b p A i j C _ _ _ _ _ _ _ hp _ hC _ ht ρ hρ.
    move : hp (hρ); move/[apply] => hp.
    move : ht (hρ); move/[apply]. intros (m & PA & hPA & ht).
    have [? [q ?]] : (subst_tm ρ p) ⇒* tRefl /\ Coherent (subst_tm ρ a) (subst_tm ρ b) by
      sauto lq:on  rew:db:InterpUniv use:InterpExt_Eq_inv.
    exists m, PA.
    split.
    + asimpl in hPA.
      apply : InterpUnivN_Coherent; eauto.
      exists (subst_tm (tRefl .: (q .: ρ)) C).
      hauto lq:on ctrs:rtc use:Pars_morphing_star, @rtc_refl, good_Pars_morphing_ext2.
    + asimpl.
      eapply InterpUnivN_back_clos_star with (b := subst_tm ρ t); eauto.
      sfirstorder use: P_JRefl_star.
  (* Nil *)
  - apply SemWff_nil.
  (* Cons *)
  - eauto using SemWff_cons.
Qed.

(* Void is an empty type *)
Lemma consistency a : ~ (nil ⊢ a ∈ tVoid).
Proof.
  move /(proj1 soundness) /(_ var_tm ltac:(eauto using ρ_ok_nil)).
  asimpl. move => [m][PA][].
  simp InterpUniv. move/InterpExt_Void_inv=>->. done.
Qed.

(* A Bool evaluates either true or false *)
Lemma canonicity a :
  nil ⊢ a ∈ tBool -> (a ⇒* tTrue) \/ (a ⇒* tFalse).
Proof.
  move /(proj1 soundness) /(_ var_tm ltac:(eauto using ρ_ok_nil)).
  move => [m][PA][/InterpUnivN_Bool_inv] -> []+[].
  case => //; asimpl; tauto.
Qed.
