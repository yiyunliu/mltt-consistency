From WR Require Import syntax imports join typing common.

Lemma good_renaming_up ξ Γ Δ A :
  good_renaming ξ Γ Δ ->
  good_renaming (upRen_tm_tm ξ)  (A :: Γ) (ren_tm ξ A :: Δ).
Proof.
  move => h.
  rewrite /good_renaming.
  case => /= [ ?| i /Arith_prebase.lt_S_n h0].
  - asimpl;
    sfirstorder.
  - split.
    + asimpl; sfirstorder.
    + case /h : h0 => h0 h1 /=.
      rewrite h1.
      by asimpl.
Qed.

Lemma T_App' Γ a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Wt Γ a (tPi A B) ->
  Wt Γ b A ->
  (* -------------------- *)
  Wt Γ (tApp a b) B0.
Proof. qauto ctrs:Wt. Qed.

Lemma T_J' (Γ : context) (t a b p A : tm) (i j : fin) (C C0 : tm) :
  C0 = (subst_tm (p .: b..) C) ->
  Wt Γ a A ->
  Wt Γ b A ->
  Wt Γ A (tUniv j) ->
  Wt Γ p (tEq a b A) ->
  Wt (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) C (tUniv i) ->
  Wt Γ t (subst_tm (tRefl .: a..) C) ->
  Wt Γ (tJ t a b p) C0.
Proof. hauto lq:on use:T_J. Qed.


Lemma wff_nil :
  Wff nil.
Proof.
  apply Wff_intro with (F := fun x => x) => /= //.
  lia.
Qed.

Lemma wff_cons Γ A i
  (h0 : Wt Γ A (tUniv i))
  (h1 : Wff Γ) :
  Wff (A :: Γ).
Proof.
  inversion h1 as [F h].
  apply Wff_intro with (F := i .: F).
  case => [? | p /Arith_prebase.lt_S_n ? ];
         sfirstorder ctrs:Wff.
Qed.

#[export]Hint Resolve wff_nil wff_cons : wff.

Lemma Wt_Wff Γ a A (h : Wt Γ a A) : Wff Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.

Lemma Wt_Univ Γ a A i
  (h : Wt Γ a A) :
  exists j, Wt Γ (tUniv i) (tUniv j).
Proof.
  exists (S i).
  qauto l:on use:Wt_Wff ctrs:Wt.
Qed.

Lemma Wt_Pi_inv Γ A B U (h : Wt Γ (tPi A B) U) :
  exists i, Wt Γ A (tUniv i) /\
         Wt (A :: Γ) B (tUniv i) /\
         Coherent (tUniv i) U /\
         exists i, Wt Γ U (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim :  Γ T U / h => //.
  - hauto l:on use:Wt_Univ.
  - qauto l:on use:Coherent_transitive.
Qed.

Lemma Wt_Pi_Univ_inv Γ A B i (h : Wt Γ (tPi A B) (tUniv i)) :
  Wt Γ A (tUniv i) /\
  Wt (A :: Γ) B (tUniv i).
Proof.
  qauto l:on use:Coherent_univ_inj, Wt_Pi_inv.
 Qed.

Lemma Wt_Abs_inv Γ A a T (h : Wt Γ (tAbs A a) T) :
  exists B i, Wt Γ (tPi A B) (tUniv i) /\
         Wt (A :: Γ) a B /\
         Coherent (tPi A B) T /\
         exists i, (Wt Γ T (tUniv i)).
Proof.
  move E : (tAbs A a) h => a0 h.
  move : A a E.
  elim : Γ a0 T / h => //.
  - hauto lq:on use:Coherent_reflexive.
  - hauto lq:on use:Coherent_transitive.
Qed.

Lemma good_renaming_suc ξ Γ A Δ
  (h : good_renaming ξ Γ Δ) :
  good_renaming (ξ >> S) Γ (ren_tm ξ A :: Δ).
Proof.
  move => i h0.
  rewrite /good_renaming in h.
  specialize h with (1 := h0).
  case : h => ? h.
  split.
  - simpl.
    asimpl.
    lia.
  - asimpl.
    simpl.
    rewrite h.
    by asimpl.
Qed.

Lemma renaming_Syn_helper ξ a b C :
  subst_tm (ren_tm ξ a .: (ren_tm ξ b)..) (ren_tm (upRen_tm_tm (upRen_tm_tm ξ)) C) = ren_tm ξ (subst_tm (a .: b ..) C).
Proof. by asimpl. Qed.

Lemma renaming_Syn Γ a A (h : Wt Γ a A) : forall Δ ξ,
    good_renaming ξ Γ Δ ->
    Wff Δ ->
    Wt Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:good_renaming.
  - hauto lq:on ctrs:Wt use:good_renaming_up db:wff.
  - hauto lq:on ctrs:Wt use:good_renaming_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:Coherent_renaming.
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
        apply : wff_cons; last by (abstract : hwff; hauto q:on use:wff_cons).
        eapply T_Eq with (i := 0).  asimpl.
        sfirstorder use:good_renaming_suc.
        apply :T_Var; sfirstorder ctrs:Wt.
        asimpl.
        sfirstorder use:good_renaming_suc.
    + move : iht hξ hΔ. repeat move/[apply]. by asimpl.
Qed.

Lemma weakening_Syn Γ a A B i
  (h0 : Wt Γ B (tUniv i))
  (h1 : Wt Γ a A) :
  Wt (B :: Γ) (ren_tm shift a) (ren_tm shift A).
Proof.
  apply : renaming_Syn; eauto with wff.
  sfirstorder unfold:good_renaming.
Qed.

Lemma weakening_Syn' Γ a A A0 B i
  (he : A0 = ren_tm shift A)
  (h0 : Wt Γ B (tUniv i))
  (h1 : Wt Γ a A) :
  Wt (B :: Γ) (ren_tm shift a) A0.
Proof. sfirstorder use:weakening_Syn. Qed.

Definition good_morphing ρ Γ Δ :=
  forall i, i < length Γ -> Wt Δ (ρ i) (subst_tm ρ (dep_ith Γ i)).

Lemma good_morphing_suc Γ Δ A j ξ (h : good_morphing ξ Γ Δ)
  (hh : Wt Δ (subst_tm ξ A) (tUniv j)) :
  good_morphing (ξ >> ren_tm S) Γ (subst_tm ξ A :: Δ).
Proof.
  move => i h0.
  rewrite /good_morphing in h.
  specialize h with (1 := h0).
  eapply weakening_Syn in h; eauto.
  move : h. asimpl. by apply.
Qed.

Lemma T_Var' Γ i A :
  A = dep_ith Γ i ->
  Wff Γ ->
  i < length Γ ->
  (* ------ *)
  Wt Γ (var_tm i) A.
Proof. qauto ctrs:Wt. Qed.

Lemma good_morphing_up ρ k Γ Δ A
  (h : good_morphing ρ Γ Δ) :
  Wt Δ (subst_tm ρ A) (tUniv k) ->
  good_morphing (up_tm_tm ρ) (A :: Γ) (subst_tm ρ A :: Δ).
Proof.
  rewrite /good_morphing => h1.
  case => [_ | i /Arith_prebase.lt_S_n ?].
  - apply T_Var' => /=.
    + by asimpl.
    + eauto with wff.
    + asimpl. lia.
  - simpl.
    apply : weakening_Syn'; cycle 2.
    rewrite /good_morphing in h.
    + sfirstorder unfold:good_morphing.
    + by asimpl.
    + sfirstorder.
Qed.

Lemma morphing_Syn Γ a A (h : Wt Γ a A) : forall Δ ρ,
    good_morphing ρ Γ Δ ->
    Wff Δ ->
    Wt Δ (subst_tm ρ a) (subst_tm ρ A).
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:good_morphing.
  - move => *.
    apply T_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  - move => *.
    apply : T_Abs; eauto.
    hauto q:on use:good_morphing_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - hauto q:on ctrs:Wt use:Coherent_subst_star.
  - move => Γ t a b p A i j C ha iha hb ihb hA ihA  hp
             ihp hC ihC ht iht Δ ξ hξ hΔ /=.
    have ? : Wt Δ (subst_tm ξ a) (subst_tm ξ A) by hauto l:on.
    have hwff : Wff (subst_tm ξ A :: Δ) by eauto using wff_cons.
    eapply T_J' with (i := i) (C := (subst_tm (up_tm_tm (up_tm_tm ξ)) C)); eauto; first by asimpl.
    + move => [:hwteq].
      apply ihC.
      * move : ihA (hξ) (hΔ); repeat move/[apply].
        move : good_morphing_up (hξ). repeat move/[apply].
        move : good_morphing_up. move/[apply].
        move /(_ 0 (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A))).
        asimpl. apply. abstract:hwteq. apply T_Eq with (j := j).
        ** hauto lq:on use:good_morphing_suc.
        ** apply T_Var' => //; hauto l:on simp+:asimpl.
        ** hauto lq:on use:good_morphing_suc.
      * qauto l:on use:wff_cons simp+:asimpl.
    + move : iht hξ hΔ. repeat move/[apply]. by asimpl.
Qed.

Lemma subst_Syn Γ A a b B
  (h0 : Wt (A :: Γ) b B)
  (h1 : Wt Γ a A) :
  Wt Γ (subst_tm (a..) b) (subst_tm (a..) B).
Proof.
  apply : morphing_Syn; eauto with wff.
  case => [_ | i /Arith_prebase.lt_S_n ?] /=.
  - by asimpl.
  - asimpl; eauto using T_Var with wff.
Qed.

Lemma T_UnivSuc Γ i :
  Wff Γ ->
  Wt Γ (tUniv i) (tUniv (S i)).
Proof. sfirstorder use:T_Univ. Qed.

Lemma Wt_regularity Γ a A
  (h : Wt Γ a A) :
  exists i, Wt Γ A (tUniv i).
Proof.
  elim: Γ a A/h; try qauto ctrs:Wt depth:2.
  - inversion 1.
    hauto l:on use:dep_ith_shift,good_renaming_truncate, renaming_Syn.
  - hauto q:on use:subst_Syn, Wt_Pi_Univ_inv.
  - hauto lq:on use:T_UnivSuc db:wff.
  - move => Γ t a b p A i j C ha iha hb ihb hA ihA hp ihp hC ihC ht iht.
    exists i. change (tUniv i) with (subst_tm (p .: b..) (tUniv i)).
    apply : morphing_Syn; eauto with wff.
    rewrite /good_morphing.
    case => [_ /= | /= k /Arith_prebase.lt_S_n].
    + by asimpl.
    + case : k => [ | /= k /Arith_prebase.lt_S_n ?].
      * by asimpl.
      * asimpl.
        eauto using T_Var with wff.
Qed.

Lemma Wt_App_inv Γ b a T (h : Wt Γ (tApp b a) T) :
  exists A B, Wt Γ b (tPi A B) /\
         Wt Γ a A /\
         Coherent (subst_tm (a..) B) T /\
         exists i, Wt Γ T (tUniv i).
Proof.
  move E : (tApp b a) h => ba h.
  move : b a E.
  elim : Γ ba T /h => //.
  - move => Γ a A B b h0 _ h1 _ ? ? [] *; subst.
    exists A, B; repeat split => //.
    + apply Coherent_subst_star. apply Coherent_reflexive.
    + move /Wt_regularity : h0.
      move => [i /Wt_Pi_Univ_inv] [hA hB].
      exists i.
      change (tUniv i) with (subst_tm (b..) (tUniv i)).
      apply : subst_Syn; eauto.
  - hauto lq:on rew:off use:Coherent_transitive.
Qed.

Lemma Wt_If_inv Γ a b c T (h : Wt Γ (tIf a b c) T) :
  exists A, Wt Γ a tBool /\
         Wt Γ b A /\
         Wt Γ c A /\
         Coherent A T /\
         exists i, Wt Γ T (tUniv i).
Proof.
  move E : (tIf a b c) h => a0 h.
  move : a b c E.
  elim : Γ a0 T / h => //.
  - hauto lq:on rew:off use:Coherent_transitive.
  - qauto l:on use:Coherent_reflexive, Wt_regularity.
Qed.

Lemma Wt_Eq_inv Γ a b A U (h : Wt Γ (tEq a b A) U) :
  Wt Γ a A /\
  Wt Γ b A /\
  (exists q,
  Wt Γ A (tUniv q)) /\
  (exists i, Coherent (tUniv i) U) /\ exists j, Wt Γ U (tUniv j).
Proof.
  move E : (tEq a b A) h => T h.
  move : a b A E.
  elim :  Γ T U / h => //.
  - qauto l:on use:Coherent_transitive.
  - hauto l:on use:Wt_Univ.
Qed.

Lemma T_Eq_simpl Γ a b A i :
  Wt Γ a A ->
  Wt Γ b A ->
  Wt Γ (tEq a b A) (tUniv i).
Proof. hauto lq:on use:T_Eq, Wt_regularity. Qed.

Lemma T_J_simpl Γ t a b p A C i
  (h : Wt Γ p (tEq a b A)) :
  Wt (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) C (tUniv i) ->
  Wt Γ t (subst_tm (tRefl .: a ..) C) ->
  Wt Γ (tJ t a b p) (subst_tm (p .: b..) C).
Proof.
  case /Wt_regularity : (h) => j /Wt_Eq_inv ?.
  have [? ?] : exists i, Wt Γ A (tUniv i)
      by sfirstorder use:Wt_regularity ctrs:Wt.
       hauto l:on use:T_J.
Qed.

Lemma Wt_J_inv Γ t a b p U (h : Wt Γ (tJ t a b p) U) :
  exists A C i,
    Wt Γ p (tEq a b A) /\
    Wt Γ a A /\
    Wt Γ b A /\
    (exists j, Wt Γ A (tUniv j)) /\
    Wt (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) C (tUniv i) /\
    Wt Γ t (subst_tm (tRefl .: a ..) C) /\
    Coherent (subst_tm (p .: b..) C) U /\
    exists j, Wt Γ U (tUniv j).
Proof.
  move E : (tJ t a b p) h => T h.
  move : t a b p E.
  elim :  Γ T U / h => //.
  - hauto lq:on rew:off use:Coherent_transitive.
  - move => Γ t a b p A i j C ha _ hb _ hA _ hp _ hC _ ht _ ? ? ? ? [] *; subst.
    exists A, C, i. repeat split => //.
    sfirstorder.
    sfirstorder use:Coherent_reflexive.
    have ? : Wt Γ (tJ t a b p) (subst_tm (p .: b..) C) by hauto l:on use:T_J.
    sfirstorder ctrs:Wt use:Wt_regularity.
Qed.

Lemma preservation_helper A0 A1 i j Γ a A :
  Wt (A0 :: Γ) a A ->
  Wt Γ A0 (tUniv i) ->
  Wt Γ A1 (tUniv j) ->
  Coherent A0 A1 ->
  Wt (A1 :: Γ) a A.
Proof.
  move => h0 h1 h2 h3.
  replace a with (subst_tm ids a); last by asimpl.
  replace A with (subst_tm ids A); last by asimpl.
  apply morphing_Syn with (Γ := A0 :: Γ).
  - done.
  - case => [_ | k /Arith_prebase.lt_S_n ?].
    + simpl; asimpl.
      apply T_Conv with (A := ren_tm shift A1) (i := i).
      * apply T_Var; hauto l:on db:wff.
      * change (tUniv i) with (ren_tm shift (tUniv i)).
        apply weakening_Syn with (i := j) => //.
      * hauto lq:on use:Coherent_symmetric, Coherent_renaming.
    + asimpl.
      change (var_tm (S k)) with (ren_tm shift (var_tm k)).
      apply weakening_Syn with (i := j) => //.
      apply T_Var; hauto lq:on db:wff.
  - eauto with wff.
Qed.

Lemma T_Refl' Γ a0 a1 A
  (hΓ : Wff Γ)
  (h : Par a0 a1) :
  Wt Γ a0 A ->
  Wt Γ a1 A ->
  Wt Γ tRefl (tEq a0 a1 A).
Proof.
  move => *.
  apply T_Conv with (A := tEq a0 a0 A) (i := 0).
  - by apply T_Refl.
  - by apply T_Eq_simpl.
  - apply Par_Coherent.
    sfirstorder use:P_Eq,Par_refl.
Qed.

Lemma subject_reduction a b (h : Par a b) : forall Γ A,
    Wt Γ a A -> Wt Γ b A.
Proof.
  elim : a b /h => //.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hACoherent & j & hA).
    have ? : Wff Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
  - move => A0 A1 a0 a1 h0 ih0 h1 ih1 Γ A /Wt_Abs_inv.
    intros (B & i & hPi & ha0 & hCoherent & j & hA).
    case /Wt_Pi_Univ_inv : hPi => hA0 hB.
    apply T_Conv with (A := tPi A1 B) (i := j) => //.
    apply T_Abs with (i := i).
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
    + suff : Coherent (tPi A1 B) (tPi A0 B) by hauto l:on use:Coherent_transitive.
      apply Coherent_symmetric.
      apply Par_Coherent.
      hauto lq:on ctrs:Par use:Par_refl.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 Γ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hCoherent & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : Coherent_transitive; eauto.
    apply Coherent_symmetric.
    apply Par_Coherent.
    apply par_morphing; last by apply Par_refl.
    hauto q:on ctrs:Par inv:nat simp:asimpl.
  - move => a A a0 b0 b1 haa0 iha hbb0 ihb Γ A0 /Wt_App_inv.
    intros (A1 & B & ha & hb0 & hCoherent & i & hA0).
    have /iha /Wt_Abs_inv := ha; intros (B0 & k & hPi & ha0 & hCoherent' & j & hPi').
    case /Coherent_pi_inj : hCoherent' => *.
    case /Wt_Pi_Univ_inv : hPi => *.
    move /Wt_regularity : ha => [i0 /Wt_Pi_Univ_inv] [hA1 hB].
    move /ihb in hb0.
    eapply T_Conv with (A := subst_tm (b1..) B0); eauto.
    + apply : subst_Syn; eauto.
      eapply T_Conv with (A := A1); eauto.
      qauto l:on use:Coherent_symmetric.
    + apply : Coherent_transitive; eauto.
      apply Coherent_symmetric.
      apply Coherent_morphing.
      * by apply Coherent_symmetric.
      * case; [by asimpl | sfirstorder use:Par_refl].
  - hauto lq:on use:Wt_If_inv ctrs:Wt.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
  - move => a0 b0 A0 a1 b1 A1 ha0 iha0 ha1 iha1 hA0 ihA0 Γ A /Wt_Eq_inv.
    intros (ha0' & hb0' & (q & hA0') & (i & eq) & (j & hA)).
    apply T_Conv with (A := (tUniv i)) (i := j); eauto.
    hauto l:on ctrs:Wt use:@rtc_once.
  - move => t0 a0 b0 p0 t1 a1 b1 p1 ht iht ha iha hb ihb hp ihp Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (k & hA) & hC0 & ht0 & heq & (j & hU)).
    have ? : Par (tEq a0 b0 A) (tEq a1 b1 A) by hauto lq:on ctrs:Par use:Par_refl.
    have ? : Coherent (tEq a0 b0 A) (tEq a1 b1 A) by hauto l:on use:@rtc_once.
    apply T_Conv with (A := subst_tm (p1 .: b1..) C) (i := j) => //.
    apply T_J_simpl with (A := A) (i := i).
    + hauto lq:on use:T_Eq_simpl, T_Conv.
    + eapply preservation_helper with (i := 0) (j := 0); eauto.
      * hauto drew:off ctrs:Wt use:T_Eq_simpl, weakening_Syn' db:wff.
      * hauto drew:off ctrs:Wt use:T_Eq_simpl, weakening_Syn' db:wff.
      * sfirstorder use:Par_Coherent, P_Eq, par_renaming, Par_refl.
    + apply T_Conv with (A := subst_tm (tRefl .: a0..) C) (i := i);auto.
      * move : morphing_Syn hC0. move/[apply].
        move /(_ Γ (tRefl .: a1..)).
        move => [:hwff].
        asimpl. apply; last by (abstract : hwff; eauto using Wt_Wff).
        (* Use proof by reflection to generalize subst_Syn *)
        case => [_ |/= q /Arith_prebase.lt_S_n].
        ** simpl; asimpl.
           apply T_Refl'; eauto.
        ** case : q => [_ | /= q /Arith_prebase.lt_S_n ?] /=;
                        asimpl; hauto q:on ctrs:Wt.
      * apply Par_Coherent.
        apply par_morphing; hauto lq:on use:Par_refl inv:nat.
    + apply : Coherent_transitive; eauto.
      apply Coherent_symmetric.
      apply Par_Coherent.
      apply par_morphing; last by apply Par_refl.
      hauto lq:on inv:nat use:Par_refl.
  - move => t0 a0 b0 p t1 a1 b1 ht iht ha iha hb ihb hp ihp Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (j & hA) & hC & ht0 & heq & (k & hU')).
    move : ihp (hp0). move/[apply] => hRefl.
    apply iht.
    move : T_Conv ht0. move/[apply]. apply; eauto.
    apply : Coherent_transitive;eauto.
Admitted.

Definition is_value (a : tm) :=
  match a with
  | tPi A B => true
  | tAbs A a => true
  | tBool => true
  | tTrue => true
  | tFalse => true
  | tVoid => true
  | tIf a b c => false
  | tApp a b => false
  | tUniv _ => true
  | tRefl => true
  | tJ _ _ _ _ => false
  | tEq _ _ _ => true
  | var_tm _ => false
  end.

Inductive head := hPi | hAbs | hBool | hTrue | hVoid | hFalse | hUniv | hVar.

Definition tm_to_head (a : tm) :=
  match a with
  | tPi A B => Some hPi
  | tAbs A a => Some hAbs
  | tBool => Some hBool
  | tTrue => Some hTrue
  | tFalse => Some hFalse
  | tVoid => Some hVoid
  | tIf a b c => None
  | tApp a b => None
  | tUniv _ => Some hUniv
  | var_tm _ => Some hVar
  end.

Lemma par_head a b (h : Par a b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h => //. Qed.

Lemma par_head_star a b (h : Pars a b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h; eauto using par_head. Qed.

Lemma Coherent_consistent a b (h : Coherent a b) :
  forall hd hd1, tm_to_head a = Some hd ->
            tm_to_head b = Some hd1 ->
            hd = hd1.
Proof. qblast use:par_head_star. Qed.

Lemma Wt_Univ_winv Γ i U :
  Wt Γ (tUniv i) U ->
  exists j, Coherent (tUniv j) U.
Proof.
  move E : (tUniv i) => U0 h.
  move : i E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

Lemma Wt_Void_winv Γ U :
  Wt Γ tVoid U ->
  exists j, Coherent (tUniv j) U.
Proof.
  move E : tVoid => U0 h.
  move : E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

Lemma Wt_True_False_winv Γ a A (h : Wt Γ a A) :
  is_bool_val a -> Coherent tBool A.
Proof. induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive. Qed.

Lemma Wt_Bool_winv Γ A :
  Wt Γ tBool A ->
  exists i, Coherent (tUniv i) A.
Proof.
  move E : tBool => a h. move : E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

Lemma wt_pi_canon a A B :
  Wt nil a (tPi A B) ->
  is_value a ->
  exists A a0, a = tAbs A a0.
Proof.
  case : a => //.
  - hauto lq:on.
  - qauto l:on use:Wt_Pi_inv, Coherent_consistent.
  - qauto l:on use:Wt_Void_winv, Coherent_consistent.
  - qauto l:on use:Wt_Univ_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_Bool_winv, Coherent_consistent.
Qed.

Lemma wt_switch_canon a :
  Wt nil a tBool ->
  is_value a ->
  is_bool_val a.
Proof.
  case : a => //.
  - qauto l:on use:Wt_Abs_inv, Coherent_consistent.
  - qauto l:on use:Wt_Pi_inv, Coherent_consistent.
  - qauto l:on use:Wt_Void_winv, Coherent_consistent.
  - qauto l:on use:Wt_Univ_winv, Coherent_consistent.
  - qauto l:on use:Wt_Bool_winv, Coherent_consistent.
Qed.

Lemma wt_progress a A (h :Wt nil a A) : is_value a \/ exists a0, Par a a0.
Proof.
  move E : nil h => Γ h.
  move : E.
  elim: Γ a A/h; try hauto q:on depth:2.
  - hauto lq:on rew:off ctrs:Par use:wt_pi_canon, Par_refl.
  - hauto lq:on rew:off use:wt_switch_canon, Par_refl.
Qed.
