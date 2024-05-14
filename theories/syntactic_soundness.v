(* For comparison, this file shows the syntactic metatheory of the language.
   The main lemmas are preservation and progress. Together, these lemmas
   imply that well-typed terms either diverge or produce values.
   However, from our logical relation, we can already see that closed,
   well-typed terms reduce to normal forms (and we know that closed normal
   forms are values).
 *)

Require Import imports join par_consistency typing.

(* -------------------------------------------------- *)

Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

Lemma good_renaming_up ξ Γ Δ A :
  ren_ok ξ Γ Δ ->
  ren_ok (upRen_tm_tm ξ)  (A :: Γ) (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /ren_ok => h.
  move => i B.
  inversion 1 =>*; subst.
  - apply here'. by asimpl.
  - asimpl. apply : there'; eauto. by asimpl.
Qed.

Lemma good_renaming_suc ξ Γ A Δ
  (h : ren_ok ξ Γ Δ) :
  ren_ok (ξ >> S) Γ (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /ren_ok in h *.
  move => i A0 /h ?.
  asimpl. apply : there'; eauto. by asimpl.
Qed.
(* -------------------------------------------------- *)

Lemma T_Ind' Γ a b c A i T :
  T = A [c..] ->
  tNat :: Γ ⊢ A ∈ tUniv i ->
  Γ ⊢ a ∈ A [tZero..] ->
  A :: tNat :: Γ ⊢ b ∈ A[tSuc (var_tm 0) .: S >> var_tm]⟨S⟩ ->
  Γ ⊢ c ∈ tNat ->
  (* ------------ *)
  Γ ⊢ tInd a b c ∈ T.
Proof. move  =>> ->. apply T_Ind. Qed.

Lemma T_App' Γ a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Γ ⊢ a ∈ (tPi A B) ->
  Γ ⊢ b ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a b) ∈ B0.
Proof. move =>> ->. apply T_App. Qed.

Lemma T_J' (Γ : context) (t a b p A : tm) (i j : fin) (C C0 : tm) :
  C0 = (subst_tm (p .: b..) C) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ A ∈ (tUniv j) ->
  Γ ⊢ p ∈ (tEq a b A) ->
  (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) ⊢ C ∈ (tUniv i) ->
  Γ ⊢ t ∈ (subst_tm (tRefl .: a..) C) ->
  Γ ⊢ (tJ t a b p) ∈ C0.
Proof. move =>> ->. apply T_J. Qed.

Lemma T_Pack' Γ a A b B B0 i :
  B0 = (subst_tm (a..) B) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ B0 ->
  Γ ⊢ tSig A B ∈ tUniv i ->
  (* -------------------- *)
  Γ ⊢ (tPack a b) ∈ tSig A B.
Proof. move =>> ->. apply T_Pack. Qed.

Lemma T_Let' Γ a b A B C C0 C1 i j :
  C0 = (subst_tm (a..) C) ->
  C1 = (subst_tm ((tPack (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)) C) ->
  Γ ⊢ A ∈ tUniv j ->
  A :: Γ ⊢ B ∈ tUniv j ->
  Γ ⊢ a ∈ tSig A B ->
  B :: A :: Γ ⊢ b ∈ C1 ->
  tSig A B :: Γ ⊢ C ∈ tUniv i ->
  Γ ⊢ tLet a b ∈ C0.
Proof. move =>> -> ->. apply T_Let. Qed.

(* ------------------------------------- *)
(* If a term is well-typed, then the context must be well-formed. *)

Lemma Wt_Wff Γ a A (h : Γ ⊢ a ∈ A) : ⊢ Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.
#[export]Hint Constructors Wff : wff.

(* -------------------------------------------------- *)
(* Inversion lemmas for well-typed terms. *)

Lemma Wt_Univ Γ a A i
  (h : Γ ⊢ a ∈ A) :
  exists j, Γ ⊢ (tUniv i) ∈ (tUniv j).
Proof.
  exists (S i).
  qauto l:on use:Wt_Wff ctrs:Wt.
Qed.

Lemma Wt_Pi_inv Γ A B U (h : Γ ⊢ (tPi A B) ∈ U) :
  exists i, Γ ⊢ A ∈ (tUniv i) /\
         (A :: Γ) ⊢ B ∈ (tUniv i) /\
         tUniv i <: U /\
         exists i, Γ ⊢ U ∈ (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim :  Γ T U / h => //.
  - hauto lq:on use:Wt_Univ, Sub_reflexive.
  - qauto l:on use:Sub_transitive.
Qed.

Lemma Wt_Sig_inv Γ A B U (h : Γ ⊢ (tSig A B) ∈ U) :
  exists i, Γ ⊢ A ∈ (tUniv i) /\
         (A :: Γ) ⊢ B ∈ (tUniv i) /\
         tUniv i <: U /\
         exists i, Γ ⊢ U ∈ (tUniv i).
Proof.
  move E : (tSig A B) h => T h.
  move : A B E.
  elim : Γ T U / h => //.
  - hauto lq:on rew:off use:Sub_transitive.
  - hauto lq:on use:Wt_Univ, Sub_reflexive.
Qed.

Lemma Wt_Pi_Univ_inv Γ A B i (h : Γ ⊢ (tPi A B) ∈ (tUniv i)) :
  Γ ⊢ A ∈ (tUniv i) /\
  (A :: Γ) ⊢ B ∈ (tUniv i).
Proof.
  move /Wt_Pi_inv : h.
  move => [j][hA][hB][h1][k]h2.
  have ? : j <= i by hauto l:on use:Sub_univ_inj.
  split.
  hauto lq:on ctrs:Wt.
  have : A :: Γ ⊢ tUniv i ∈ tUniv (S i) by hauto lq:on ctrs:Wt db:wff.
  hauto lq:on ctrs:Wt.
Qed.

Lemma Wt_Abs_inv Γ a T (h : Γ ⊢ (tAbs a) ∈ T) :
  exists A B i, Γ ⊢ (tPi A B) ∈ (tUniv i) /\
         (A :: Γ) ⊢ a ∈ B /\
         tPi A B <: T /\
         exists i, (Γ ⊢ T ∈ (tUniv i)).
Proof.
  move E : (tAbs a) h => a0 h.
  move : a E.
  elim : Γ a0 T / h => //.
  - hauto lq:on use:Sub_reflexive.
  - hauto lq:on use:Sub_transitive.
Qed.

Lemma Wt_Sig_Univ_inv Γ A B i (h : Γ ⊢ (tSig A B) ∈ (tUniv i)) :
  Γ ⊢ A ∈ (tUniv i) /\
  (A :: Γ) ⊢ B ∈ (tUniv i).
Proof.
  move /Wt_Sig_inv : h.
  move => [j][hA][hB][h1][k]h2.
  have ? : j <= i by hauto lq:on use:Sub_univ_inj.
  split.
  hauto lq:on ctrs:Wt.
  have : A :: Γ ⊢ tUniv i ∈ tUniv (S i) by hauto lq:on ctrs:Wt db:wff.
  hauto lq:on ctrs:Wt.
Qed.

Lemma Wt_Pack_inv Γ a b T (h : Γ ⊢ tPack a b ∈ T) :
  exists A B i, Γ ⊢ a ∈ A /\
    Γ ⊢ b ∈ B[a..] /\
    Γ ⊢ tSig A B ∈ tUniv i /\
    tSig A B <: T /\
    exists j, (Γ ⊢ T ∈ tUniv j).
Proof.
  move E : (tPack a b) h => p h.
  move : a b E.
  elim : Γ p T / h => //.
  - hauto lq:on use:Sub_transitive.
  - hauto lq:on use:Sub_reflexive.
Qed.

(* -------------------------------------------------- *)

Lemma renaming_Syn_helper ξ a b C :
  subst_tm (a ⟨ξ⟩ .: (b⟨ξ⟩)..) (ren_tm (upRen_tm_tm (upRen_tm_tm ξ)) C) = ren_tm ξ (subst_tm (a .: b ..) C).
Proof. by asimpl. Qed.

Lemma renaming_Syn
  Γ a A (h : Γ ⊢ a ∈ A) : forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ∈ A⟨ξ⟩.
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt,lookup unfold:ren_ok.
  - hauto q:on ctrs:Wt,Wff use:good_renaming_up.
  - hauto lq:on ctrs:Wt use:good_renaming_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:Sub_renaming.
  - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ξ hξ hΔ /=.
    apply  T_Ind' with (a := ren_tm ξ a) (A := ren_tm (upRen_tm_tm ξ) A) (i := i).
    + by asimpl.
    + apply ihA. by apply good_renaming_up.
      apply Wff_cons with (i := 0); qauto l:on ctrs:Wt.
    + have -> : A ⟨upRen_tm_tm ξ⟩[tZero..] = A[tZero..]⟨ξ⟩ by asimpl. auto.
    + move /(_ (A ⟨upRen_tm_tm ξ⟩ :: tNat :: Δ) (upRen_tm_tm (upRen_tm_tm ξ)))
        : ihb. asimpl. apply.
      * case => [A0|[A0|n]].
        inversion 1; subst. asimpl.
        apply here'. by asimpl.

        elim /lookup_inv=>// _ []// A1 Γ0 B  h _ [*]. subst.
        have -> : A1 = tNat by hauto lq:on inv:lookup.
        asimpl. apply : there'; last by sfirstorder ctrs:lookup. by asimpl.

        move => A0 h.
        have {h} : exists A1, lookup n Γ A1 /\ A0 = A1 ⟨S⟩ ⟨S⟩ by hauto lq:on inv:lookup.
        move => [A1 [hA1 hA1']]. subst.
        simpl. asimpl.
        apply : there'; cycle 1. apply : there'; cycle 1.
        sfirstorder.
        done.
        by asimpl.
      * have ? : ⊢ tNat :: Δ by hauto lq:on ctrs:Wt db:wff.
        eauto using good_renaming_up with wff.
    + auto.
  - move => Γ t a b p A i j C ha iha hA ihA hb ihb hp
             ihp hC ihC ht iht Δ ξ hξ hΔ /=.
    rewrite -renaming_Syn_helper.
    eapply T_J; try qauto ctrs:Wt.
    + apply ihC.
      * move /good_renaming_up in hξ.
        move /(_ A) in hξ.
        move /good_renaming_up in hξ.
        move /(_ (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A))) in hξ.
        by asimpl in hξ.
      * move => [:hwff].
        apply : Wff_cons; first by (abstract : hwff; hauto q:on ctrs:Wff).
        eapply T_Eq with (i := 0).  asimpl.
        sfirstorder use:good_renaming_suc.
        apply :T_Var; sfirstorder ctrs:Wt.
        asimpl.
        sfirstorder use:good_renaming_suc.
    + move : iht hξ hΔ. repeat move/[apply]. by asimpl.
  - hauto lq:on ctrs:Wt, Wff use:good_renaming_up, Wt_Sig_Univ_inv.
  - move => Γ a A b B i hA ihA hB ihB hS ihS Δ ξ hξ hΔ /=.
    eapply T_Pack' with (B0 := B[a..] ⟨ξ⟩); eauto. by asimpl.
  - move => Γ a b A B C i j hA ihA hB ihB ha iha hb ihb hS ihS Δ ξ hξ hΔ /=.
    eapply T_Let' with
      (C := C ⟨upRen_tm_tm ξ⟩)
      (C1 := C[(tPack (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] ⟨upRen_tm_tm (upRen_tm_tm ξ)⟩);
      eauto.
    1-2: by asimpl.
    + sauto q:on dep:on use:good_renaming_up.
    + hauto q:on use:Wff_cons, good_renaming_up.
    + hauto q:on ctrs:Wt use:Wff_cons, good_renaming_up.
Qed.

Lemma weakening_Syn Γ a A B i
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ∈ A) :
  (B :: Γ) ⊢ (ren_tm shift a) ∈ (ren_tm shift A).
Proof.
  apply : renaming_Syn; eauto with wff.
  hauto lq:on ctrs:lookup unfold:ren_ok.
Qed.

Lemma weakening_Syn' Γ a A A0 B i
  (he : A0 = ren_tm shift A)
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ∈ A) :
  (B :: Γ) ⊢ (ren_tm shift a) ∈ A0.
Proof. sfirstorder use:weakening_Syn. Qed.

Definition lookup_good_morphing ρ Γ Δ :=
  forall i A, lookup i Γ A -> Δ ⊢ ρ i ∈ A [ ρ ].

Lemma good_morphing_suc Γ Δ A j ρ (h : lookup_good_morphing ρ Γ Δ)
  (hh : Δ ⊢ A [ρ] ∈ tUniv j) :
  lookup_good_morphing (ρ >> ren_tm S) Γ (A [ρ] :: Δ).
Proof.
  rewrite /lookup_good_morphing in h * => i A0 /h /weakening_Syn.
  asimpl. eauto.
Qed.

Lemma good_morphing_up ρ k Γ Δ A
  (h : lookup_good_morphing ρ Γ Δ) :
  Δ ⊢ A[ρ] ∈ tUniv k ->
  lookup_good_morphing (up_tm_tm ρ) (A :: Γ) (A [ρ] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply T_Var => /=.
    + eauto with wff.
    + asimpl. apply : here'. by asimpl.
  - apply : weakening_Syn'; cycle 2.
    rewrite /lookup_good_morphing in h.
    + sfirstorder unfold:lookup_good_morphing.
    + by asimpl.
    + sfirstorder.
Qed.

Lemma morphing_Syn Γ a A (h : Γ ⊢ a ∈ A) : forall Δ ρ,
    lookup_good_morphing ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ∈ A[ρ].
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:lookup_good_morphing.
  - move => *.
    apply T_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  - move => *.
    apply : T_Abs; eauto.
    hauto q:on use:good_morphing_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - hauto q:on ctrs:Wt use:Sub_morphing.
  - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ρ hρ hΔ /=.
    have ? : Wff (tNat :: Δ) by apply Wff_cons with (i := 0); eauto using T_Nat.
    apply T_Ind' with (A := subst_tm (up_tm_tm ρ) A) (i := i); first by asimpl.
    + hauto lq:on ctrs:Wt use:good_morphing_up.
    + move /iha : hρ {iha}.
      asimpl. tauto.
    + have hw : lookup_good_morphing (up_tm_tm ρ) (tNat :: Γ) (tNat :: Δ)
        by hauto lq:on ctrs:Wt use:good_morphing_up db:wff.
      have /ihb : lookup_good_morphing (up_tm_tm (up_tm_tm ρ)) (A :: tNat :: Γ) (A[up_tm_tm ρ] :: tNat :: Δ) by hauto lq:on ctrs:Wt use:good_morphing_up db:wff.
      asimpl. substify. apply.
      apply : Wff_cons=>//.
      apply ihA=>//.
      move : hw. asimpl. by substify.
    + auto.
  - move => Γ t a b p A i j C ha iha hb ihb hA ihA  hp
             ihp hC ihC ht iht Δ ξ hξ hΔ /=.
    have ? : Wt Δ (subst_tm ξ a) (subst_tm ξ A) by hauto l:on.
    have hwff : Wff (subst_tm ξ A :: Δ) by eauto using Wff_cons.
    eapply T_J' with (i := i) (C := (subst_tm (up_tm_tm (up_tm_tm ξ)) C)); eauto; first by asimpl.
    + move => [:hwteq].
      apply ihC.
      * move : ihA (hξ) (hΔ); repeat move/[apply].
        move : good_morphing_up (hξ). repeat move/[apply].
        move : good_morphing_up. move/[apply].
        move /(_ 0 (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A))).
        asimpl. apply. abstract:hwteq. apply T_Eq with (j := j).
        ** hauto lq:on use:good_morphing_suc.
        ** apply T_Var => //. apply here'. by asimpl.
        ** hauto lq:on use:good_morphing_suc.
      * qauto l:on use:Wff_cons simp+:asimpl.
    + move : iht hξ hΔ. repeat move/[apply]. by asimpl.
  - move => *. apply T_Sig; eauto.
    hauto lq:on use:good_morphing_up, Wff_cons.
  - move => Γ a A b B i hA ihA hB ihB hS ihS Δ ρ hρ hΔ.
    eapply T_Pack' with (B0 := B[a .: var_tm][ρ]); eauto. by asimpl.
  - move => Γ a b A B C i j hA ihA hB ihB ha iha hb ihb hS ihS Δ ρ hρ hΔ.
    eapply T_Let' with
      (C := C[up_tm_tm ρ])
      (C1 := C[tPack (var_tm 1) (var_tm 0) .: (S >> S) >> var_tm][up_tm_tm (up_tm_tm ρ)]);
      eauto.
    + by asimpl.
    + by asimpl; substify.
    + hauto lq:on use:good_morphing_up, Wff_cons.
    + hauto lq:on use:good_morphing_up, Wff_cons.
    + hauto q:on ctrs:Wt, tm use:good_morphing_up, Wff_cons.
Qed.

Lemma subst_Syn Γ A a b B
  (h0 : (A :: Γ) ⊢ b ∈ B)
  (h1 : Γ ⊢ a ∈ A) :
  Γ ⊢ (subst_tm (a..) b) ∈ (subst_tm (a..) B).
Proof.
  apply : morphing_Syn; eauto with wff.
  inversion 1; subst.
  - by asimpl.
  - asimpl; eauto using T_Var with wff.
Qed.

Lemma subst_Syn_Univ Γ A a b i :
  (A :: Γ) ⊢ b ∈ tUniv i ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b[a..] ∈ tUniv i.
Proof.
  change (tUniv i) with (tUniv i)[a..].
  apply subst_Syn.
Qed.

Lemma Wff_lookup : forall Γ i A,
    ⊢ Γ -> lookup i Γ A -> exists j, Γ ⊢ A ∈ tUniv j.
Proof.
  move => Γ + + h.
  elim : Γ / h.
  - inversion 1.
  - move => Γ A i h ih h0.
    move => i0 A0.
    elim /lookup_inv.
    + hauto l:on inv:lookup use:weakening_Syn.
    + move => h1 n A1 Γ0 B + ? []*. subst.
      move /ih => [j ?].
      exists j. apply : weakening_Syn'; eauto. done.
Qed.

Lemma Wt_regularity Γ a A
  (h : Γ ⊢ a ∈ A) :
  exists i, Γ ⊢ A ∈ (tUniv i).
Proof.
  elim: Γ a A/h; try qauto ctrs:Wt depth:2.
  - apply Wff_lookup.
  - hauto q:on use:subst_Syn, Wt_Pi_Univ_inv.
  - eauto using subst_Syn_Univ.
  - hauto lq:on ctrs:Wt db:wff.
  - move => Γ t a b p A i j C ha iha hb ihb hA ihA hp ihp hC ihC ht iht.
    exists i. change (tUniv i) with (subst_tm (p .: b..) (tUniv i)).
    apply : morphing_Syn; eauto with wff.
    move => k A0.
    elim /lookup_inv.
    + move => ? > ? [] *. subst. by asimpl.
    + move => _ n A1 Γ0 B + ? [] *. subst. simpl.
      inversion 1; subst.
      * by asimpl.
      * asimpl. eauto using T_Var with wff.
  - eauto using subst_Syn_Univ.
Qed.

Lemma Wt_App_inv Γ b a T (h : Γ ⊢ (tApp b a) ∈ T) :
  exists A B, Γ ⊢ b ∈ tPi A B /\
         Γ ⊢ a ∈ A /\
         subst_tm (a..) B <: T /\
         exists i, Γ ⊢ T ∈ tUniv i.
Proof.
  move E : (tApp b a) h => ba h.
  move : b a E.
  elim : Γ ba T /h => //.
  - move => Γ a A B b h0 _ h1 _ ? ? [] *; subst.
    exists A, B; repeat split => //.
    + apply Sub_morphing. apply Sub_reflexive.
    + qauto ctrs:Wt use:Wt_Pi_Univ_inv, subst_Syn_Univ, Wt_regularity.
  - hauto lq:on rew:off use:Sub_transitive.
Qed.

Lemma Wt_Ind_inv Γ a b c T (h : Γ ⊢ (tInd a b c) ∈ T) :
  exists A, Γ ⊢ a ∈ A[tZero..] /\
       A :: tNat :: Γ ⊢ b ∈ A [tSuc (var_tm 0) .: S >> var_tm]⟨S⟩  /\
         Γ ⊢ c ∈ tNat /\
         A[c..] <: T /\
         (exists j, tNat :: Γ ⊢ A ∈ tUniv j) /\
         exists i, Γ ⊢ T ∈ tUniv i.
Proof.
  move E : (tInd a b c) h => a0 h.
  move : a b c E.
  elim : Γ a0 T / h => //.
  - hauto lq:on rew:off use:Sub_transitive.
  - move => Γ a b c A i hA _ ha _ hb _ hc _ ? ? ?[*]. subst.
    exists A. repeat split=>//.
    + apply Sub_reflexive.
    + eauto using subst_Syn_Univ.
    + eauto using subst_Syn_Univ.
Qed.

Lemma Wt_Eq_inv Γ a b A U (h : Γ ⊢ (tEq a b A) ∈ U) :
  Γ ⊢ a ∈ A /\
  Γ ⊢ b ∈ A /\
  (exists q,
  Γ ⊢ A ∈ (tUniv q)) /\
  (exists i, Sub (tUniv i) U) /\ exists j, Γ ⊢ U ∈ (tUniv j).
Proof.
  move E : (tEq a b A) h => T h.
  move : a b A E.
  elim :  Γ T U / h => //.
  - hauto l:on use:Sub_transitive.
  - hauto l:on use:T_Univ, Sub_reflexive db:wff.
Qed.

Lemma Wt_Let_inv Γ a b T (h : Γ ⊢ tLet a b ∈ T) :
  exists i j A B C,
    Γ ⊢ A ∈ tUniv j /\
    A :: Γ ⊢ B ∈ tUniv j /\
    Γ ⊢ a ∈ tSig A B /\
    B :: A :: Γ ⊢ b ∈ C[(tPack (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] /\
    tSig A B :: Γ ⊢ C ∈ tUniv i /\
    C[a..] <: T /\
    (exists i, Γ ⊢ T ∈ tUniv i).
Proof.
  move E : (tLet a b) h => a0 h.
  move : a b E.
  elim : Γ a0 T / h => //.
  - move => Γ a0 T U i ha0 ih0 hU _ hSub a b E.
    destruct (ih0 a b E) as (j & k & A & B & C & hA & hB & ha & hb & hC & hCoherent & hT).
    exists j, k. (* not sure why these need to be explicit for CoqHammer to work *)
    hauto l:on use:Sub_transitive.
  - move => *.
    hauto q:on use:subst_Syn, Sub_reflexive.
Qed.

(* ------------------------------------------------- *)
(* Simpler forms of typing rules *)

Lemma T_Eq_simpl Γ a b A i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ (tEq a b A) ∈ (tUniv i).
Proof. hauto lq:on use:T_Eq, Wt_regularity. Qed.

Lemma T_J_simpl Γ t a b p A C i
  (h : Γ ⊢ p ∈ (tEq a b A)) :
  (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) ⊢ C ∈ (tUniv i) ->
  Γ ⊢ t ∈ (subst_tm (tRefl .: a ..) C) ->
  Γ ⊢ (tJ t a b p) ∈ (subst_tm (p .: b..) C).
Proof.
  case /Wt_regularity : (h) => j /Wt_Eq_inv ?.
  have [? ?] : exists i, Γ ⊢ A ∈ (tUniv i)
      by sfirstorder use:Wt_regularity ctrs:Wt.
       hauto l:on use:T_J.
Qed.

Lemma T_Abs_simple Γ A a B :
  A :: Γ ⊢ a ∈ B ->
  (* -------------------- *)
  Γ ⊢ tAbs a ∈ tPi A B.
Proof.
  move => h.
  have hΓ : ⊢ A :: Γ by sfirstorder use:Wt_Wff.
  have hΓ' : ⊢ Γ by inversion hΓ.
  have [i hA] : exists i, Γ ⊢ A ∈ tUniv i by hauto lq:on inv:Wff.
  have [j hB] : exists j, A::Γ ⊢ B ∈ tUniv j by sfirstorder use:Wt_regularity.
  apply T_Abs with (i := max i j)=>//.
  have : Γ ⊢ tUniv (Nat.max i j) ∈ tUniv (S (Nat.max i j))
    by qauto l:on ctrs:Wt.
  have : A::Γ ⊢ tUniv (Nat.max i j) ∈ tUniv (S (Nat.max i j))
    by qauto l:on ctrs:Wt.
  have ? : i <= Nat.max i j  by lia.
  have ? : j <= Nat.max i j  by lia.
  hauto lq:on ctrs:Sub1 use:Sub1_Sub, T_Conv, T_Pi.
Qed.

Lemma Wt_J_inv Γ t a b p U (h : Γ ⊢ (tJ t a b p) ∈ U) :
  exists A C i,
    Γ ⊢ p ∈ (tEq a b A) /\
    Γ ⊢ a ∈ A /\
    Γ ⊢ b ∈A /\
    (exists j, Γ ⊢ A ∈ (tUniv j)) /\
    (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) ⊢ C ∈ (tUniv i) /\
    Γ ⊢ t ∈ (subst_tm (tRefl .: a ..) C) /\
    C[p .: b..] <: U /\
    exists j, Γ ⊢ U ∈ (tUniv j).
Proof.
  move E : (tJ t a b p) h => T h.
  move : t a b p E.
  elim :  Γ T U / h => //.
  - hauto lq:on rew:off use:Sub_transitive.
  - move => Γ t a b p A i j C ha _ hb _ hA _ hp _ hC _ ht _ ? ? ? ? [] *; subst.
    exists A, C, i. repeat split => //.
    sfirstorder.
    sfirstorder use:Sub_reflexive.
    have ? : Γ ⊢ (tJ t a b p) ∈ (subst_tm (p .: b..) C) by hauto l:on use:T_J.
    sfirstorder ctrs:Wt use:Wt_regularity.
Qed.

Lemma preservation_helper A0 A1 i j Γ a A :
  (A0 :: Γ) ⊢ a ∈ A ->
  Γ ⊢ A0 ∈ (tUniv i) ->
  Γ ⊢ A1 ∈ (tUniv j) ->
  A1 <: A0 ->
  (A1 :: Γ) ⊢ a ∈ A.
Proof.
  move => h0 h1 h2 h3.
  replace a with (subst_tm ids a); last by asimpl.
  replace A with (subst_tm ids A); last by asimpl.
  apply morphing_Syn with (Γ := A0 :: Γ).
  - done.
  - move => k h. elim/lookup_inv.
    + move => ? A2 Γ0 ? [] *. subst. asimpl.
      apply T_Conv with (A := ren_tm shift A1) (i := i).
      * apply T_Var; hauto l:on db:wff.
      * change (tUniv i) with (ren_tm shift (tUniv i)).
        apply weakening_Syn with (i := j) => //.
      * hauto lq:on use:Sub_renaming.
    + move => _ n A2 Γ0 B ? ? [] *. subst. asimpl.
      change (var_tm (S n)) with (ren_tm shift (var_tm n)).
      apply weakening_Syn with (i := j) => //.
      apply T_Var; hauto lq:on db:wff.
  - eauto with wff.
Qed.

Lemma preservation_helper2 A0 A1 B0 B1 i j k l Γ a A :
  (B0 :: A0 :: Γ) ⊢ a ∈ A ->
  Γ ⊢ A0 ∈ tUniv i ->
  Γ ⊢ A1 ∈ tUniv j ->
  A0 :: Γ ⊢ B0 ∈ tUniv k ->
  A1 :: Γ ⊢ B1 ∈ tUniv l ->
  A1 <: A0 -> B1 <: B0 ->
  (B1 :: A1 :: Γ ⊢ a ∈ A).
Proof.
  move => ha hA0 hA1 hB0 hB1 hSubA hSubB.
  replace a with (a[ids]); last by asimpl.
  replace A with (A[ids]); last by asimpl.
  apply morphing_Syn with (Γ := B0 :: A0 :: Γ);
    auto; last by eauto with wff.
  move => m C. elim /lookup_inv.
  - move => lookm B0' Γ' _ E _. inversion E. asimpl.
    apply T_Conv with (A := B1 ⟨S⟩) (i := k).
    + apply T_Var; hauto lq:on ctrs:lookup db:wff.
    + eapply weakening_Syn' with (A := tUniv k); eauto.
      eapply preservation_helper; eauto.
    + apply Sub_renaming; auto.
  - move => lookm n C' Γ' B' lookn _ E _. asimpl.
    elim /lookup_inv : lookn.
    + move => lookn A0' Γ'' _ E' _. subst. inversion E.
      apply T_Conv with (A := A1 ⟨S⟩ ⟨S⟩) (i := i).
      * apply T_Var; hauto lq:on ctrs:lookup db:wff.
      * repeat eapply weakening_Syn' with (A := tUniv i); eauto.
      * repeat apply Sub_renaming; auto.
    + move => *. apply T_Var; hauto lq:on ctrs:lookup db:wff.
Qed.

Lemma T_Refl' Γ a0 a1 A
  (hΓ : ⊢ Γ)
  (h : a0 ⇒ a1) :
  Γ ⊢ a0 ∈ A ->
  Γ ⊢ a1 ∈ A ->
  Γ ⊢ tRefl ∈ (tEq a0 a1 A).
Proof.
  move => *.
  apply T_Conv with (A := tEq a0 a0 A) (i := 0).
  - by apply T_Refl.
  - by apply T_Eq_simpl.
  - hauto lq:on use:P_Eq,Par_refl, Par_Sub.
Qed.

Lemma Wt_Refl_inv Γ T (h : Γ ⊢ tRefl ∈ T) :
  exists a A, Γ ⊢ tRefl ∈ (tEq a a A)  /\
         Γ ⊢ a ∈ A /\
         tEq a a A <: T /\ exists i, Γ ⊢ T ∈ (tUniv i).
Proof.
  move E : tRefl h => p h.
  move : E.
  elim : p T / h=>//.
  - hauto lq:on rew:off use:Sub_transitive.
  - hauto lq:on ctrs:Wt use:T_Eq_simpl, Sub_reflexive.
Qed.

Lemma Wt_Suc_inv Γ a T (h : Γ ⊢ tSuc a ∈ T) :
  Γ ⊢ a ∈ tNat /\
  tNat <: T /\ exists i, Γ ⊢ T ∈ tUniv i.
Proof.
  move E : (tSuc a) h => a0 h.
  move : a E.
  elim : Γ a0 T / h=>//.
  - hauto lq:on rew:off use:Sub_transitive.
  - hauto lq:on ctrs:Wt use:T_Nat, Sub_reflexive.
Qed.

Lemma Wt_Refl_Coherent Γ a b A (h : Γ ⊢ tRefl ∈ (tEq a b A)) :
  Coherent a b.
Proof.
  qauto l:on use:Wt_Refl_inv, Sub_eq_inj, Coherent_transitive, Coherent_symmetric.
Qed.

Lemma subject_reduction a b (h : a ⇒ b) : forall Γ A,
    Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A.
Proof.
  elim : a b /h => //.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hACoherent & j & hA).
    have ? : ⊢ Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    qauto l:on ctrs:Wt use:preservation_helper, Par_Sub.
  - move => a0 a1 h0 ih0 Γ A /Wt_Abs_inv.
    intros (A1 & B & i & hPi & ha0 & hCoherent & j & hA).
    case /Wt_Pi_Univ_inv : hPi => hA0 hB.
    apply T_Conv with (A := tPi A1 B) (i := j) => //.
    apply T_Abs with (i := i).
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Sub.
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Sub.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 Γ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hCoherent & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : Sub_transitive; eauto.
    have : B[b0..] ⇒ B[b1..]; last by hauto l:on use:Par_Sub.
    apply Par_morphing; last by apply Par_refl.
    hauto q:on unfold:Par_m ctrs:Par inv:nat simp:asimpl.
  - move => a a0 b0 b1 haa0 iha hbb0 ihb Γ A0 /Wt_App_inv.
    intros (A1 & B & ha & hb0 & hCoherent & i & hA0).
    have /Wt_Abs_inv := ha; intros (A & B0 & k & hPi & ha0 & hCoherent' & j & hPi').
    case /Sub_pi_inj : hCoherent' => *.
    case /Wt_Pi_Univ_inv : hPi => *.
    move /Wt_regularity : ha => [i0 /Wt_Pi_Univ_inv] [hA1 hB].
    move /ihb in hb0.
    eapply T_Conv with (A := subst_tm (b1..) B0); eauto.
    + apply : subst_Syn; eauto.
      eapply T_Conv with (A := A1); eauto.
    + apply : Sub_transitive; eauto.
      apply Sub_transitive with (B := B0[b0..]).
      have : B0[b0..] ⇒ B0[b1..]; last by hauto l:on use:Par_Sub.
      sfirstorder use:Par_cong, Par_refl.
      hauto l:on use:Sub_morphing.
  - move => a b h ih Γ A /Wt_Suc_inv.
    move => [h0][h1][i]h2.
    apply : T_Conv; eauto.
    have : ⊢ Γ by eauto with wff.
    have : Γ ⊢ b ∈ tNat by auto.
    apply T_Suc.
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc Γ A /Wt_Ind_inv.
    move => [A0][ha0][hb0][hc0][hC][[i hA0]][j hAj].
    apply : T_Conv. apply T_Ind with (i := i); eauto. eauto.
    apply : Sub_transitive; eauto.
    have : A0[c0..] ⇒ A0[c1..]; last by hauto l:on use:Par_Sub.
    sfirstorder use:Par_cong, Par_refl.
  - qauto l:on use:Wt_Ind_inv ctrs:Wt.
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc Γ A /Wt_Ind_inv.
    move => [A0][ha0][hb0][hc0][hA0][[j hA0']][i hA'].
    apply : T_Conv; eauto.
    have : A0[(tSuc c1)..] <: A0[(tSuc c0)..].
    apply Par_Sub.
    apply Par_morphing. case => //=; hauto l:on ctrs:Par. apply Par_refl.
    move/T_Conv. apply.
    have /morphing_Syn /(_ Γ (tInd a1 b1 c1 .: c1..))  := ihb _ _ hb0.
    asimpl. apply; eauto with wff.
    rewrite /lookup_good_morphing.
    have ? : Γ ⊢ c0 ∈ tNat by hauto l:on use:Wt_Suc_inv.
    move => i0 A1. elim/lookup_inv => _.
    + move => A2 Γ0 ? []*. subst.
      asimpl.
      apply : T_Ind; eauto.
    + move => n A2 Γ0 B + ? [*]. subst.
      elim/lookup_inv => _.
      move => A1 Γ0 ? [*]. subst. by asimpl; auto.
      move => n0 A1 Γ0 B ? ? [*]. subst.
      asimpl.  hauto lq:on ctrs:Wt db:wff.
    + eauto using subst_Syn_Univ.
  - move => a0 b0 A0 a1 b1 A1 ha0 iha0 ha1 iha1 hA0 ihA0 Γ A /Wt_Eq_inv.
    intros (ha0' & hb0' & (q & hA0') & (i & eq) & (j & hA)).
    apply T_Conv with (A := (tUniv i)) (i := j); eauto.
    apply T_Eq_simpl;
      hauto lq:on rew:off ctrs:Wt use:Par_Sub.
  - move => t0 a0 b0 p0 t1 a1 b1 p1 ht iht ha iha hb ihb hp ihp Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (k & hA) & hC0 & ht0 & heq & (j & hU)).
    have ? : (tEq a0 b0 A ⇒ tEq a1 b1 A) by hauto lq:on ctrs:Par use:Par_refl.
    have ? : Coherent (tEq a0 b0 A) (tEq a1 b1 A) by hauto l:on use:@rtc_once.
    apply T_Conv with (A := subst_tm (p1 .: b1..) C) (i := j) => //.
    apply T_J_simpl with (A := A) (i := i).
    + hauto lq:on use:T_Eq_simpl, T_Conv, Par_Sub.
    + eapply preservation_helper with (i := 0) (j := 0); eauto.
      * hauto drew:off ctrs:Wt,lookup use:T_Eq_simpl, weakening_Syn' db:wff.
      * hauto drew:off ctrs:Wt,lookup use:T_Eq_simpl, weakening_Syn' db:wff.
      * hauto lq:on use:Par_Sub, P_Eq, Par_renaming, Par_refl.
    + apply T_Conv with (A := subst_tm (tRefl .: a0..) C) (i := i);auto.
      * move : morphing_Syn hC0. move/[apply].
        move /(_ Γ (tRefl .: a1..)).
        move => [:hwff].
        asimpl. apply; last by (abstract : hwff; eauto using Wt_Wff).
        move => l h. elim/lookup_inv.
        ** move => _ A0 Γ0 ? [] *. subst=>/=. asimpl.
           apply T_Refl'; eauto.
        ** move => _. inversion 1; subst;
             asimpl; hauto q:on ctrs:Wt.
      * have : C[tRefl .: a0..] ⇒ C[tRefl .: a1..] by
          apply Par_morphing; hauto lq:on unfold:Par_m use:Par_refl inv:nat.
        hauto l:on use:Par_Sub.
    + apply : Sub_transitive; eauto.
      have : C[p0 .: b0..] ⇔ C[p1 .: b1..]; last by hauto l:on use:Coherent_Sub.
      apply Par_Coherent.
      apply Par_morphing; last by apply Par_refl.
      hauto lq:on unfold:Par_m inv:nat use:Par_refl.
  - move => t0 a b t1 ht iht Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (j & hA) & hC & ht0 & heq & (k & hU')).
    apply iht.
    move : T_Conv ht0. move/[apply]. apply; eauto.
    apply : Sub_transitive;eauto.
    have ? : Coherent a b by eauto using Wt_Refl_Coherent.
    have : C[tRefl .: a..] ⇔ C[tRefl .: b..]; last by hauto l:on use:Coherent_Sub.
    replace (subst_tm (tRefl .: a..) C)
      with (subst_tm (a..)(subst_tm (tRefl..) C)); last by asimpl.
    replace (subst_tm (tRefl .: b..) C)
      with (subst_tm (b..)(subst_tm (tRefl..) C)); last by asimpl.
    apply Coherent_cong. apply Coherent_reflexive. auto.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 Γ A /Wt_Sig_inv.
    intros (i & hA0 & hB0 & hACoherent & j & hA).
    have ? : ⊢ Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    hauto q:on ctrs:Wt use:preservation_helper, Par_Sub.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 Γ A /Wt_Pack_inv.
    intros (A0 & B0 & i & ha & hb & hSig & hCoherent & j & hA).
    apply T_Conv with (A := tSig A0 B0) (i := j) => //.
    eapply T_Pack; eauto.
    apply ih1.
    have ? : B0[a0..] <: B0[a1..] by hauto lq:on use:Par_cong, Par_refl, Par_Sub.
    apply T_Conv with (A := B0[a0..]) (i := i) => //.
    change (tUniv i) with (tUniv i)[a1..].
    eapply subst_Syn; eauto.
    apply Wt_Sig_Univ_inv => //.
  - move => a0 b0 a1 b1 h0 ih0 h1 ih1 Γ A /Wt_Let_inv.
    intros (i & j & A0 & B0 & C & hA0 & hB0 & ha & hb & hC & hCoherent & k & hA).
    apply T_Conv with (A := C[a1..]) (i := k) => //.
    + eapply T_Let' with (j := j); eauto.
    + apply : Sub_transitive; eauto.
      hauto lq:on drew:off
        use:Sub_transitive, Coherent_Sub, Coherent_cong,
            Coherent_reflexive, Coherent_symmetric, Par_Coherent.
  - move => a0 b0 c0 a1 b1 c1 h0 ih0 h1 ih1 h2 ih2 Γ A /Wt_Let_inv.
    intros (i & j & A0 & B0 & C & hA0 & hB0 & hPack & hc0 & hC & hCoherent & k & hA).
    move /Wt_Pack_inv : hPack.
    intros (A1 & B1 & l & ha0 & hb0 & hSig & hSub & _).
    move /Wt_Sig_Univ_inv : hSig => [hA1 hB1].
    move /Sub_sig_inj : hSub => [hSubA hSubB].
    apply ih0 in ha0.
    apply ih1 in hb0.
    apply ih2 in hc0.
    have hb1 : Γ ⊢ b1 ∈ B1[a1..]. {
      apply T_Conv with (A := B1[a0..]) (i := l); auto.
      + change (tUniv l) with (tUniv l)[a1..].
        eapply subst_Syn with (a := a1); eauto.
      + hauto lq:on use:Par_cong, Par_refl, Par_Sub.
    }
    eapply T_Conv with (A := C[(tPack a1 b1)..]); eauto.
    + have -> : C[(tPack a1 b1)..] = C[tPack (var_tm 1) (var_tm 0) .: shift >> shift >> var_tm][b1 .: a1..]
        by asimpl.
      eapply preservation_helper2 with
        (A0 := A0) (A1 := A1) (B0 := B0) (B1 := B1) in hc0; eauto.
      move : morphing_Syn hc0. move /[apply].
      apply; last by hauto lq:on db:wff.
      move => m D. elim/lookup_inv.
      * move => *. asimpl. scongruence.
      * inversion 2; asimpl;
        hauto lq:on ctrs:Wt db:wff.
    + eapply Sub_transitive; eauto.
      sauto lq:on use:Par_cong, Par_refl, Par_Sub.
Qed.

(* ----------------------------------------------- *)
Definition is_value (a : tm) :=
  match a with
  | tPi A B => true
  | tAbs a => true
  | tNat => true
  | tSuc _ => true
  | tZero => true
  | tInd a b c => false
  | tApp a b => false
  | tUniv _ => true
  | tRefl => true
  | tJ _ _ _ _ => false
  | tEq _ _ _ => true
  | tSig _ _ => true
  | tPack _ _ => true
  | tLet _ _ => false
  | var_tm _ => false
  end.

Definition head_inhab (a : tm) : head :=
  match a with
  | tAbs _ => hPi
  | tSuc _ => hNat
  | tZero => hNat
  | tRefl => hEq
  | tPi _ _ => hUniv
  | tEq _ _ _ => hUniv
  | tUniv _ => hUniv
  | tNat => hUniv
  | tSig _ _ => hUniv
  | tPack _ _ => hSig
  | _ => hBot
  end.

Lemma wt_winv Γ A T (h : Γ ⊢ A ∈ T) :
  ~~ (head_inhab A \≤ hBot) ->
  exists B, tm_to_head B = head_inhab A /\ B <: T.
Proof.
  elim : Γ A T / h => //=; solve [sfirstorder use:Sub_reflexive | hauto lq:on use:Sub_reflexive, Sub_transitive].
Qed.

Lemma bot_is_bot a : hBot \≤ a.
Proof. case : a => //. Qed.

Lemma hleq_bot a : a \≤ hBot -> a = hBot.
Proof. auto using bot_is_bot, hleq_antisym. Qed.

Lemma wt_wrong_hf_contra Γ a A (h : Γ ⊢ a ∈ A) :
  (head_inhab a \≤ tm_to_head A) || (tm_to_head A \≤ head_inhab a).
Proof.
  case E : (head_inhab a \≤ hBot)=>//; qauto l:on use:wt_winv, Sub_consistent, hleq_bot.
Qed.

(* Canonical forms lemmas *)
Definition canon_prop (U : tm) (a : tm) : Prop :=
  is_value a ->
  match U with
  | tPi A B => exists a0, a = tAbs a0
  | tEq _ _ _ => a = tRefl
  | tNat => a = tZero \/ exists b, a = tSuc b
  | tSig _ _ => exists a0 b0, a = tPack a0 b0
  | _ => True
  end.

Lemma wt_canon a U :
  nil ⊢ a ∈ U -> canon_prop U a.
Proof.
  move /wt_wrong_hf_contra; hauto drew:off ctrs:tm inv:tm unfold:canon_prop.
Qed.

(* Call by name reduction *)
Reserved Infix "⇝" (at level 60, right associativity).
Inductive CBN : tm -> tm -> Prop :=
| N_App a0 a1 b :
  (a0 ⇝ a1) ->
  (* ------------------- *)
  (tApp a0 b) ⇝ (tApp a1 b)
| N_AppAbs a b :
  (* -------------------- *)
  (tApp (tAbs a) b) ⇝ a[b..]
| N_Ind a b c0 c1 :
  (c0 ⇝ c1) ->
  (* ----------------------- *)
  (tInd a b c0) ⇝ (tInd a b c1)
| N_IndZero a b :
  (* -------------- *)
  (tInd a b tZero) ⇝ a
| N_IndSuc a b c :
  (* -------------------------------------- *)
  (tInd a b (tSuc c)) ⇝ b[(tInd a b c) .: c..]
| N_J t a b p0 p1 :
  (p0 ⇝ p1) ->
  (* ----------------------- *)
  (tJ t a b p0) ⇝ (tJ t a b p1)
| N_JRefl t a b :
  (* --------------- *)
  (tJ t a b tRefl) ⇝ t
| N_Let a0 a1 b :
  (a0 ⇝ a1) ->
  (* ------------------- *)
  (tLet a0 b) ⇝ (tLet a1 b)
| N_LetPack a b c :
  (* ---------------------------- *)
  (tLet (tPack a b) c) ⇝ c[b .: a..]
where "A ⇝ B" := (CBN A B).
#[export]Hint Constructors CBN : cbn.

Lemma wt_progress a A (h : nil ⊢ a ∈ A) : is_value a \/ exists a0, a ⇝ a0.
Proof.
  move E : nil h => Γ h.
  move : E.
  elim: Γ a A/h; auto.
  - hauto lq:on inv:lookup.
  - hauto lq:on use:wt_canon ctrs:CBN unfold:canon_prop.
  - move => > _ _ _ _ _ _.
    hauto lq: on use: wt_canon ctrs: CBN unfold: canon_prop.
  - move => > _ _ _ _ _ _ + + _ _ _ _.
    hauto lq: on use: wt_canon ctrs: CBN unfold: canon_prop.
  - move => > _ _ _ _ + + _ _ _ _.
    hauto lq: on use: wt_canon ctrs: CBN unfold: canon_prop.
Qed.

Lemma CBN_Par a0 a1 (h : a0 ⇝ a1) : a0 ⇒ a1.
Proof.
  elim: h; hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma wt_preservation Γ a b A (r : a ⇝ b) (h : Γ ⊢ a ∈ A) : Γ ⊢ b ∈ A.
Proof.
  sfirstorder use:CBN_Par, subject_reduction.
Qed.

(* Evaluation will either step to a value or diverge *)
CoInductive Eval a : Prop :=
| E_Value : is_value a -> Eval a
| E_Step b : a ⇝ b -> Eval b -> Eval a.

(* We need evaluation to be coinductive to express divergence of e.g. (λx. x x) (λx. x x) *)
CoFixpoint Omega (omega := tAbs (tApp (var_tm 0) (var_tm 0))) :
  Eval (tApp omega omega).
Proof.
  eapply E_Step; last by (exact Omega).
  apply N_AppAbs.
Qed.

(* Well typed terms don't get stuck, i.e. will always evaluate *)
CoFixpoint wt_safety a A (h : nil ⊢ a ∈ A) : Eval a.
Proof.
  destruct (wt_progress _ _ h) as [va | [a' ra]].
  - apply E_Value; auto.
  - eapply E_Step; eauto.
    have ha' : nil ⊢ a' ∈ A by eapply wt_preservation; eauto.
    eapply wt_safety; eauto.
Qed.
