Require Import join semtyping normalform typing imports.

(* Semantic substitution well-formedness *)
Definition ρ_ok Γ ρ := forall i A, lookup i Γ A -> forall m PA, ⟦ A [ρ] ⟧ m ↘ PA -> PA (ρ i).

(* Semantic typing, written Γ ⊨ a : A in the paper *)
Definition SemWt Γ a A := forall ρ, ρ_ok Γ ρ -> exists m PA, ( ⟦ A [ρ] ⟧ m ↘ PA)  /\ PA (a [ρ]).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

(* Semantic context wellformedness *)
Definition SemWff Γ := forall i A, lookup i Γ A -> exists j, Γ ⊨ A ∈ tUniv j.
Notation "⊨ Γ" := (SemWff Γ) (at level 70).

Lemma ρ_ok_nil ρ : ρ_ok nil ρ.
Proof.  rewrite /ρ_ok. inversion 1; subst. Qed.

Lemma ρ_ok_cons i Γ ρ a PA A :
 ⟦ A [ρ] ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (A :: Γ) (a .: ρ).
Proof.
  move => h0 h1 h2.
  rewrite /ρ_ok. inversion 1; subst.
  - move => j PA0 hPA0.
    asimpl in hPA0.
    suff : PA = PA0 by congruence.
    hauto l:on use:InterpUnivN_deterministic'.
  - asimpl. hauto lq:on unfold:ρ_ok solve+:lia.
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
    + hauto lq:on.
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
    rewrite SemWt_Univ in ih.
    move: (ih _ hρ) => [PA h1].
    exists j. exists PA. split. auto.
    move: (hρ _ _ l _ _ h1).
    by asimpl.
  (* Void *)
  - hauto l:on use:SemWt_Univ.
  (* Pi *)
  - move => Γ i A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => ρ hρ.
    move /(_ ρ hρ) : h0; intros (PA & hPA).
    eexists => /=.
    apply InterpUnivN_Fun_nopf; eauto.
    move => *; asimpl. eauto using ρ_ok_cons.
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
    move  : hf (hb) => /[apply].
    move : hTot hb. move/[apply].
    asimpl. hauto lq:on.
  (* Conv *)
  - move => Γ a A B i _ hA _ /SemWt_Univ hB ? ρ hρ.
    have hs : subst_tm ρ A <: subst_tm ρ B
      by hauto l:on use:Sub_morphing.
    move /hB : (hρ) {hB}.
    move => [PB]hPB.
    move /hA : hρ {hA}.
    move => [j][PA][hPA]ha.
    have : PB a[ρ] by hauto q:on use:InterpUnivN_Sub.
    hauto lq:on.
  (* True *)
  - hauto l:on.
  (* False *)
  - hauto l:on.
  (* If *)
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
  (* Bool *)
  - hauto l:on use:SemWt_Univ.
  (* Univ *)
  - hauto lq:on use:InterpUnivN_Univ_inv, SemWt_Univ.
  (* Refl *)
  - move => Γ a A _ _ _ ha ρ.
    move : ha. move/[apply]. move => [m [PA [h0 h1]]].
    exists 0. eexists.
    split => /=.
    + apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty, InterpUnivN_Eq unfold:CR.
    + qauto l:on ctrs:rtc use:Coherent_reflexive inv:Par .
  (* Eq *)
  - move => Γ a b A i j _ ha _ hb _ /SemWt_Univ hA.
    apply SemWt_Univ => ρ hρ.
    eexists => /=. apply InterpUnivN_Eq;
      hauto l:on use:adequacy, InterpUniv_wn_ty unfold:SemWt, CR.
  (* J *)
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
  (* Nil *)
  - apply SemWff_nil.
  (* Cons *)
  - eauto using SemWff_cons.
Qed.

Lemma mltt_normalizing Γ a A : Γ ⊢ a ∈ A -> wn a /\ wn A.
Proof.
  move /(proj1 soundness) /(_ var_tm).
  elim.
  - asimpl.
    hauto l:on use:adequacy, InterpUniv_wn_ty unfold:CR.
  - rewrite /ρ_ok=>i ? m PA. asimpl.
    hauto q:on ctrs:rtc use:adequacy.
Qed.

(* Need to prove something about scoping before we can recover consistency *)
Inductive stm (n : nat) : tm -> Prop :=
| SC_Var i :
  i < n ->
  (* ----- *)
  stm n (var_tm i)

| SC_Abs b :
  stm (S n) b ->
  (* ------------ *)
  stm n (tAbs b)

| SC_App a b :
  stm n a ->
  stm n b ->
  (* ---------- *)
  stm n (tApp a b)

| SC_Pi A B :
  stm n A ->
  stm (S n) B ->
  (* ------------ *)
  stm n (tPi A B)

| SC_Void :
  (* ------------ *)
  stm n tVoid

| SC_Univ i :
  (* ----------- *)
  stm n (tUniv i)

| SC_True :
  (* --------- *)
  stm n tTrue

| SC_False :
  (* -------------- *)
  stm n tFalse

| SC_Bool :
  (* -------------- *)
  stm n tBool

| SC_Eq a b A :
  stm n a ->
  stm n b ->
  stm n A ->
  (* ---------------- *)
  stm n (tEq a b A)

| SC_J t a b p :
  stm n t ->
  stm n a ->
  stm n b ->
  stm n p ->
  (* ------------- *)
  stm n (tJ t a b p)

| SC_If a b c :
  stm n a ->
  stm n b ->
  stm n c ->
  stm n (tIf a b c)

| SC_Refl :
  (* --------- *)
  stm n tRefl.

#[export]Hint Constructors stm : stm.

Lemma scope_lt n a : stm n a -> forall m, n <= m -> stm m a.
Proof. move => h. elim : a / h; hauto lq:on ctrs:stm solve+:lia. Qed.

Lemma ne_scope a : ne a -> forall n, stm n a -> n > 0.
Proof. elim : a; hauto q:on inv:stm b:on solve+:lia. Qed.

Lemma lookup_lt i A Γ : lookup i Γ A -> i < length Γ.
Proof. move => h. elim : i Γ A / h; sfirstorder. Qed.

Lemma wt_scope Γ a A : Γ ⊢ a ∈ A -> stm (length Γ) a.
Proof. move => h. elim : Γ a A / h; hauto use:lookup_lt q:on ctrs:stm. Qed.

Lemma scope_ren_up n m ξ :
  (forall i, i < n -> ξ i < m) ->  forall i, i < S n -> upRen_tm_tm ξ i < S m.
Proof.
  move => h.
  case => [|p].
  - asimpl. lia.
  - move : (h p). asimpl. lia.
Qed.

Lemma scope_renaming n a (h : stm n a) :
  forall m ξ, (forall i, i < n -> ξ i < m) -> stm m (ren_tm ξ a).
Proof.
  elim : a / h=>//=; eauto 10 using scope_ren_up with stm.
Qed.

Lemma scope_weaken m a : stm m a -> stm (S m) (ren_tm shift a).
Proof. move /scope_renaming. apply. lia. Qed.

Lemma scope_morphing_up n m ρ :
  (forall i, i < n -> stm m (ρ i)) ->
  forall i, i < S n -> stm (S m) (up_tm_tm ρ i).
Proof.
  move => h.
  case. asimpl.
  hauto l:on ctrs:stm use:scope_weaken.
  move => p ?. asimpl.
  apply scope_weaken.
  apply h. lia.
Qed.

Lemma scope_morphing n a (h : stm n a) :
  forall m ρ, (forall i, i < n -> stm m (ρ i)) -> stm m (subst_tm ρ a).
Proof.
  elim : n a / h=>//=; eauto 10 using scope_morphing_up with stm.
Qed.

Lemma scope_subst n a b (h : stm (S n) a) (h0 : stm n b) :
  stm n (subst_tm (b..) a).
Proof.
  apply scope_morphing with (n := S n)=>//.
  case.
  by asimpl. move => p. asimpl.
  hauto lq:on ctrs:stm solve+:lia.
Qed.

Lemma Par_scope a b (h : a ⇒ b) : forall n, stm n a -> stm n b.
Proof. elim : a b / h; hauto lq:on inv:stm ctrs:stm use:scope_subst. Qed.

Lemma Pars_scope a b (h : a ⇒* b) : forall n, stm n a -> stm n b.
Proof. elim : a b / h; sfirstorder use:Par_scope. Qed.

Lemma consistency a : ~ nil ⊢ a ∈ tVoid.
Proof.
  move => /[dup] /wt_scope /= h.
  move /(proj1 soundness).
  rewrite /SemWt.
  have : ρ_ok nil var_tm by
    hauto lq:on inv:lookup unfold:ρ_ok.
  move/[swap]/[apply].
  move => [m][PA][]. simp InterpUniv. asimpl.
  move/InterpExt_Void_inv => ->.
  rewrite /wne.
  move => [b][]. move : h.
  move /Pars_scope. move/[apply].
  hauto lq:on use:ne_scope solve+:lia.
Qed.
