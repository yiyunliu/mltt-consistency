Require Import join par_consistency semtyping normalform typing imports.

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
   B :: Γ ⊨ a ⟨S⟩ ∈ A ⟨S⟩.
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
  - hauto lq:on rew:off use:InterpUnivN_Univ_inv.
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
    exists j. change (tUniv j) with (tUniv j) ⟨S⟩.
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
  (* Zero *)
  - hauto l:on.
  (* Suc *)
  - move => Γ a _ ha _ hΓ ρ hρ.
    move /(_ ρ hρ) : ha.
    move => [m][PA][h] h0.
    exists m, PA. split=>//.
    move /InterpUnivN_Nat_inv in h.
    hauto lq:on use:S_Suc.
  (* Ind *)
  - move => Γ a b c A l _ /SemWt_Univ hA _ ha _ hb _ hc ρ hρ.
    move /(_ ρ hρ) : ha => [m][PA][ha0]ha1.
    move /(_ ρ hρ) : hc => [n][PA0][/InterpUnivN_Nat_inv ->][v[hc1 hc2]]/=.
    asimpl.
    set bs := (X in tInd _ X _).
    move : {c} (c[ρ]) hc1 hc2.
    apply is_nat_val_ind => {v}.
    + move => ? ? c hc _. subst.
      exists m, PA. split.
      * apply : InterpUnivN_back_preservation_star;eauto.
        asimpl.
        qauto l:on use:Pars_morphing_star,good_Pars_morphing_ext ctrs:rtc.
      * simpl.
        apply : InterpUnivN_back_clos_star; eauto.
        by apply P_IndZero_star.
    + move => ? a0 ? ih c hc ha. subst.
      move /(_ a0 ltac:(apply rtc_refl) ha) : ih => [m0][PA1][hPA1]hr.
      have hρ' : ρ_ok (tNat :: Γ) (a0 .: ρ).
      {
        apply : ρ_ok_cons; auto.
        apply InterpUnivN_Nat.
        hauto lq:on ctrs:rtc.
      }
      have : ρ_ok (A :: tNat :: Γ) ((tInd a[ρ] bs a0) .: (a0 .: ρ))
        by eauto using ρ_ok_cons.
      move /hb => {hb} [m1][PA2][hPA2]h.
      exists m1, PA2.
      split.
      * move : hPA2. asimpl.
        move /InterpUnivN_back_preservation_star. apply.
        qauto l:on use:Pars_morphing_star,good_Pars_morphing_ext ctrs:rtc.
      * move : h.
        move /InterpUnivN_back_clos_star. apply; eauto.
        subst bs.
        apply : P_IndSuc_star'; eauto.
        by asimpl.
    + move => a0 ? <- _ a1 *.
      have ? : wne a1 by hauto lq:on.
      suff  /hA : ρ_ok (tNat :: Γ) (a1 .: ρ).
      move => [S hS].
      exists l, S. split=>//.
      suff ? : wn bs.
      have ? : wn a[ρ] by sfirstorder use:adequacy.
      have : wne (tInd a[ρ] bs a1) by auto using wne_ind.
      eapply adequacy; eauto.

      subst bs.
      rewrite /SemWt in hb.
      have /hA : ρ_ok (tNat :: Γ) (var_tm 0 .: ρ).
      {
        apply : ρ_ok_cons; auto.
        apply InterpUnivN_Nat.
        hauto lq:on ctrs:rtc.
      }
      move => [S1 hS1].
      have /hb : ρ_ok (A :: tNat :: Γ) (var_tm 0 .: (var_tm 0 .: ρ)).
      {
        apply : ρ_ok_cons; cycle 2; eauto.
        apply : ρ_ok_cons; cycle 2; eauto.
        apply InterpUnivN_Nat.
        hauto lq:on ctrs:rtc.
        hauto q:on ctrs:rtc use:adequacy.
      }
      move =>[m0][PA1][h1]h2.
      have : wn b[var_tm 0 .: (var_tm 0 .: ρ)] by hauto q:on use:adequacy.
      clear => h.
      apply wn_antirenaming with (ξ :=  var_zero .: (var_zero .: id)).
      by asimpl.

      apply : ρ_ok_cons; auto.
      apply InterpUnivN_Nat.
      hauto lq:on use:adequacy db:nfne.
  (* Bool *)
  - hauto l:on use:SemWt_Univ.
  (* Univ *)
  - hauto lq:on use:InterpUnivN_Univ, SemWt_Univ.
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
        apply InterpUnivN_Eq; eauto. rewrite-/subst_tm. asimpl.
        by auto. rewrite -/subst_tm. by asimpl.
        rewrite -/subst_tm. right. by auto.
        move : hb (hρ). move/[apply].
        move => [i0 [PA0 hb0]].
        hauto l:on use:ρ_ok_cons.
      * move => PC hPC.
        exists i, PC. split; first tauto.
        qauto l:on use:adequacy,wne_j unfold:CR.
  (* Sig *)
  - move => Γ i A B _ /SemWt_Univ h0 _ /SemWt_Univ h1.
    apply SemWt_Univ.
    move => ρ hρ.
    move /(_ ρ hρ) : h0; intros (PA & hPA).
    eexists => /=.
    apply InterpUnivN_Sig_nopf; eauto.
    move => *; asimpl. eauto using ρ_ok_cons.
  (* Pack *)
  - move => Γ a A b B i _ ha _ hb _ /SemWt_Univ hB ρ hρ.
    move /ha : (hρ) => [m][PA][ha0]ha1.
    move /hb : (hρ) => [m0][PB][hb0]hb1.
    move /hB : (hρ) => [S]/=hS.
    exists i, S => /=.
    split => //.
    move /InterpUnivN_Sig_inv_nopf : hS => [PA0][hPA0][hPB0]?. subst.
    rewrite /SumSpace.
    left. do 2 eexists. split; first by apply rtc_refl.
    have ? : PA = PA0 by eauto using InterpUnivN_deterministic'. subst.
    split => // PB0. asimpl.
    move /hPB0 :ha1.
    move => [PB1]. asimpl => *.
    asimpl in hb0.
    have [*] : PB = PB1 /\ PB0 = PB1 by  eauto using InterpUnivN_deterministic'.
    congruence.
  (* Let Pack *)
  - move => Γ t b A B C i _ _ _ _ _ _ ht _ hb _ /SemWt_Univ hC ρ hρ.
    move /ht : (hρ) {ht} => [m][PA][/= /[dup] hSig /InterpUnivN_Sig_inv_nopf].
    move => [PA0][h0][h1]?. subst.
    rewrite /SumSpace.
    case.
    + move => [a0][b0][h2][h3]h4.
      have : ρ_ok (tSig A B :: Γ) ((tPack a0 b0) .: ρ) by
        hauto  use:ρ_ok_cons,InterpUnivN_Sig_nopf  unfold:SumSpace.
      move /hC => [S] hS {hC}.
      exists i, S. split=>//.
      asimpl.
      move /InterpUnivN_back_preservation_star : (hS). apply.
      qauto l:on use:Pars_morphing_star,good_Pars_morphing_ext ctrs:rtc.
      apply : InterpUnivN_back_clos_star; eauto.
      apply P_LetPack_star; eauto.
      asimpl.
      have ?: ρ_ok (A :: Γ) (a0 .: ρ) by eauto using ρ_ok_cons.
      move /h1 : (h3) => [PB] /[dup] hPB.
      move /h4 => ?.
      asimpl in hPB.
      have : ρ_ok (B :: A :: Γ) (b0 .: (a0 .: ρ)) by eauto using ρ_ok_cons.
      move /hb => [m0][PA]. asimpl. move => [hPA] hPA0.
      by have <- : PA = S by eauto using InterpUnivN_deterministic'.
    + move => h.
      have /hC : ρ_ok (tSig A B :: Γ) (t[ρ] .: ρ) by
        apply : ρ_ok_cons; hauto lq:on use:adequacy.
      move => [S hS].
      exists i, S. asimpl; split => //.
      set a := (X in S X).
      suff : wne a by hauto q:on use:adequacy.
      subst a.
      apply wne_let=>//.
      have hz : wne (var_tm 0) by hauto lq:on ctrs:rtc.
      have hz' : PA0 (var_tm 0) by move : h0 hz; clear; hauto lq:on use:adequacy unfold:CR.
      apply wn_antirenaming with (ξ := var_zero .: (var_zero .: id)).
      asimpl.
      have hρ' : ρ_ok (A :: Γ) (var_tm 0 .: ρ) by eauto using ρ_ok_cons.
      move /h1 : hz' => [PB /ltac:(asimpl) hPB].
      have hz'' : PB (var_tm 0) by move : hPB hz; clear; hauto lq:on use:adequacy unfold:CR.
      have : ρ_ok (B :: A :: Γ) (var_tm 0 .: (var_tm 0 .: ρ)) by eauto using ρ_ok_cons.
      move /hb. clear.
      hauto l:on use:adequacy unfold:CR.
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

| SC_Univ i :
  (* ----------- *)
  stm n (tUniv i)

| SC_Zero :
  (* --------- *)
  stm n tZero

| SC_Suc a :
  stm n a ->
  (* -------------- *)
  stm n (tSuc a)

| SC_Nat :
  (* -------------- *)
  stm n tNat

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

| SC_Ind a b c :
  stm n a ->
  stm (2 + n) b ->
  stm n c ->
  stm n (tInd a b c)

| SC_Refl :
  (* --------- *)
  stm n tRefl

| SC_Pack a b :
  stm n a ->
  stm n b ->
  (* ------------- *)
  stm n (tPack a b)

| SC_Sig A B :
  stm n A ->
  stm (S n) B ->
  (* ------------ *)
  stm n (tSig A B)

| SC_Let a b :
  stm n a ->
  stm (S (S n)) b ->
  (* -------------- *)
  stm n (tLet a b).

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
  - move : (h p). asimpl. rewrite /funcomp. lia.
Qed.

Lemma scope_renaming n a (h : stm n a) :
  forall m ξ, (forall i, i < n -> ξ i < m) -> stm m (ren_tm ξ a).
Proof.
  elim : a / h=>//=; eauto 10 using scope_ren_up with stm.
Qed.

Lemma scope_weaken m a : stm m a -> stm (S m) (ren_tm shift a).
Proof. move /scope_renaming. apply. rewrite/shift. lia. Qed.

Lemma scope_morphing_up n m ρ :
  (forall i, i < n -> stm m (ρ i)) ->
  forall i, i < S n -> stm (S m) (up_tm_tm ρ i).
Proof.
  move => h.
  case.
  asimpl. hauto lq:on ctrs:stm solve+:lia.
  move => j /PeanoNat.lt_S_n {}/h.
  hauto lq:on use:scope_weaken.
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
Proof.
  elim : a b / h;
    match goal with
    | [|-context[subst_tm]] => idtac
    | _ => hauto lq:on inv:stm ctrs:stm
    end.
  - hauto lq:on inv:stm ctrs:stm use:scope_subst.
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc n hi.
    inversion hi; subst.
    apply scope_morphing with (n := 2 +  n);simpl;  eauto.
    case => [_|].
    + hauto lq:on inv:stm ctrs:stm.
    + case => [_|]/=.
      hauto lq:on inv:stm.
      move => n0 h.
      have {h}: n0 < n by lia.
      hauto lq:on ctrs:stm.
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc n hi.
    inversion hi; subst.
    apply scope_morphing with (n := 2 +  n);simpl;  eauto.
    case => [_|].
    + asimpl. apply ihb. move : hi. clear. qauto l:on inv:stm.
    + case => [_|]/=. apply iha.
      move : hi. clear. qauto l:on inv:stm.
      move => m h.
      have {}h : m < n by lia.
      hauto lq:on ctrs:stm.
Qed.

Lemma Pars_scope a b (h : a ⇒* b) : forall n, stm n a -> stm n b.
Proof. elim : a b / h; sfirstorder use:Par_scope. Qed.

Lemma consistency a : ~ nil ⊢ a ∈ tEq tZero (tSuc tZero) tNat.
Proof.
  move => /[dup] /wt_scope /= h.
  move /(proj1 soundness).
  rewrite /SemWt.
  have : ρ_ok nil var_tm by
    hauto lq:on inv:lookup unfold:ρ_ok.
  move/[swap]/[apply].
  move => [m][PA][].
  move /InterpUnivN_Eq_inv => [->]_[[_/Coherent_consistent]|[v[/Pars_scope]]]//.
  asimpl. move /(_ 0 h). move/ne_scope/[apply]. lia.
Qed.
