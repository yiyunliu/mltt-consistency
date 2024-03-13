(* For comparison, this file shows the syntactic metatheory of the language.
   The main lemmas are preservation and progress. Together, these lemmas
   imply that well-typed terms either diverge or produce values.
   However, from our logical relation, we can already see that closed,
   well-typed terms reduce to normal forms (and we know that closed normal
   forms are values).
 *)

From WR Require Import syntax imports join typing.


(* -------------------------------------------------- *)
(* Parallel reduction preserves head forms. We use this
   to show that Coherent terms have the same head form.
*)

Inductive head
  := hPi | hAbs | hBool | hTrue | hVoid
| hFalse | hUniv | hVar | hEq | hRefl.

Definition tm_to_head (a : tm) :=
  match a with
  | tPi A B => Some hPi
  | tAbs a => Some hAbs
  | tBool => Some hBool
  | tTrue => Some hTrue
  | tFalse => Some hFalse
  | tVoid => Some hVoid
  | tIf a b c => None
  | tApp a b => None
  | tUniv _ => Some hUniv
  | var_tm _ => Some hVar
  | tEq _ _ _ => Some hEq
  | tRefl => Some hRefl
  | tJ _ _ _ _ => None
  end.

Lemma Par_head a b (h : a ⇒ b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h => //. Qed.

Lemma Par_head_star a b (h : a ⇒* b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h; eauto using Par_head. Qed.

Lemma Coherent_consistent a b (h : Coherent a b) :
  forall hd hd1, tm_to_head a = Some hd ->
            tm_to_head b = Some hd1 ->
            hd = hd1.
Proof. qblast use:Par_head_star. Qed.

(* -------------------------------------------------- *)

Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

Lemma good_renaming_up ξ Γ Δ A :
  lookup_good_renaming ξ Γ Δ ->
  lookup_good_renaming (upRen_tm_tm ξ)  (A :: Γ) (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /lookup_good_renaming => h.
  move => i B.
  inversion 1 =>*; subst.
  - apply here'. by asimpl.
  - asimpl. apply : there'; eauto. by asimpl.
Qed.

Lemma good_renaming_suc ξ Γ A Δ
  (h : lookup_good_renaming ξ Γ Δ) :
  lookup_good_renaming (ξ >> S) Γ (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /lookup_good_renaming in h *.
  move => i A0 /h ?.
  asimpl. apply : there'; eauto. by asimpl.
Qed.
(* -------------------------------------------------- *)

Lemma T_If' Γ t a b c A i :
  t = (subst_tm (a..) A) ->
  Wt (tBool :: Γ) A (tUniv i) ->
  Γ ⊢ a ∈ tBool ->
  Γ ⊢ b ∈ (subst_tm (tTrue..) A) ->
  Γ ⊢ c ∈ (subst_tm (tFalse..) A) ->
  (* ------------ *)
  Γ ⊢ (tIf a b c) ∈ t.
Proof. move =>> ->. apply T_If. Qed.

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
         (A :: Γ) ⊢ B ∈(tUniv i) /\
         tUniv i <: U /\
         exists i, Γ ⊢ U ∈ (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim :  Γ T U / h => //.
  - hauto lq:on ctrs:Wt, Sub1, rtc use:Wt_Univ.
  - qauto l:on use:Sub_transitive.
Qed.

Lemma Wt_Pi_Univ_inv Γ A B i (h : Γ ⊢ (tPi A B) ∈ (tUniv i)) :
  Γ ⊢ A ∈ (tUniv i) /\
  (A :: Γ) ⊢ B ∈ (tUniv i).
Proof.
  qauto l:on use:Coherent_univ_inj, Wt_Pi_inv.
Qed.

Lemma Wt_Abs_inv Γ a T (h : Γ ⊢ (tAbs a) ∈ T) :
  exists A B i, Γ ⊢ (tPi A B) ∈ (tUniv i) /\
         (A :: Γ) ⊢ a ∈ B /\
         Coherent (tPi A B) T /\
         exists i, (Γ ⊢ T ∈ (tUniv i)).
Proof.
  move E : (tAbs a) h => a0 h.
  move : a E.
  elim : Γ a0 T / h => //.
  - hauto lq:on use:Coherent_reflexive.
  - hauto lq:on use:Coherent_transitive.
Qed.

(* -------------------------------------------------- *)

Lemma renaming_Syn_helper ξ a b C :
  subst_tm (a ⟨ξ⟩ .: (b⟨ξ⟩)..) (ren_tm (upRen_tm_tm (upRen_tm_tm ξ)) C) = ren_tm ξ (subst_tm (a .: b ..) C).
Proof. by asimpl. Qed.

Lemma renaming_Syn
  Γ a A (h : Γ ⊢ a ∈ A) : forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ∈ A⟨ξ⟩.
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt,lookup unfold:lookup_good_renaming.
  - hauto q:on ctrs:Wt,Wff use:good_renaming_up.
  - hauto lq:on ctrs:Wt use:good_renaming_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:Coherent_renaming.
  - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ξ hξ hΔ /=.
    apply  T_If' with (a := ren_tm ξ a) (A := ren_tm (upRen_tm_tm ξ) A) (i := i).
    + by asimpl.
    + apply ihA. by apply good_renaming_up.
      apply Wff_cons with (i := 0); qauto l:on ctrs:Wt.
    + hauto l:on.
    + set q := (subst_tm _ _).
      replace q with (ren_tm ξ (subst_tm (tTrue..) A)); auto.
      subst q; by asimpl.
    + set q := (subst_tm _ _).
      replace q with (ren_tm ξ (subst_tm (tFalse..) A)); auto.
      subst q; by asimpl.
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
Qed.

Lemma weakening_Syn Γ a A B i
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ∈ A) :
  (B :: Γ) ⊢ (ren_tm shift a) ∈ (ren_tm shift A).
Proof.
  apply : renaming_Syn; eauto with wff.
  hauto lq:on ctrs:lookup unfold:lookup_good_renaming.
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
  - hauto q:on ctrs:Wt use:Coherent_subst_star.
  - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ρ hρ hΔ /=.
    have ? : Wff (tBool :: Δ) by apply Wff_cons with (i := 0); eauto using T_Bool.
    apply T_If' with (A := subst_tm (up_tm_tm ρ) A) (i := i); first by asimpl.
    + hauto lq:on ctrs:Wt use:good_morphing_up.
    + hauto l:on.
    + set q := subst_tm (tTrue..) _.
      replace q with (subst_tm ρ (subst_tm (tTrue..) A)).
      hauto l:on.
      subst q; by asimpl.
    + set q := subst_tm (tFalse..) _.
      replace q with (subst_tm ρ (subst_tm (tFalse..) A)).
      hauto l:on.
      subst q; by asimpl.
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
  - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc.
    exists i. change (tUniv i) with (subst_tm (a..) (tUniv i)).
    eauto using subst_Syn.
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
Qed.

Lemma Wt_App_inv Γ b a T (h : Γ ⊢ (tApp b a) ∈ T) :
  exists A B, Γ ⊢ b ∈ (tPi A B) /\
         Γ ⊢ a ∈ A /\
         Coherent (subst_tm (a..) B) T /\
         exists i, Γ ⊢ T ∈ (tUniv i).
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
      change (tUniv i) with (tUniv i)[b..].
      apply : subst_Syn; eauto.
  - hauto lq:on rew:off use:Coherent_transitive.
Qed.

Lemma Wt_If_inv Γ a b c T (h : Γ ⊢ (tIf a b c) ∈ T) :
  exists A, Γ ⊢ a ∈ tBool /\
         Γ ⊢ b ∈ A [tTrue..] /\
         Γ ⊢ c ∈ A [tFalse..] /\
         Coherent A[a..] T /\
         (exists j, tBool :: Γ ⊢ A ∈ tUniv j) /\
         exists i, Γ ⊢ T ∈ tUniv i.
Proof.
  move E : (tIf a b c) h => a0 h.
  move : a b c E.
  elim : Γ a0 T / h => //.
  - hauto lq:on rew:off use:Coherent_transitive.
  - move => Γ a b c A i hA _ ha _ hb _ hc _ ? ? ?[*]. subst.
    exists A. repeat split=>//.
    + apply Coherent_reflexive.
    + exists i. change (tUniv i) with (subst_tm (a..) (tUniv i)).
      eauto using subst_Syn.
    + exists i. change (tUniv i) with (subst_tm (a..) (tUniv i)).
      eauto using subst_Syn.
Qed.

Lemma Wt_Eq_inv Γ a b A U (h : Γ ⊢ (tEq a b A) ∈ U) :
  Γ ⊢ a ∈ A /\
  Γ ⊢ b ∈A /\
  (exists q,
  Γ ⊢ A ∈ (tUniv q)) /\
  (exists i, Coherent (tUniv i) U) /\ exists j, Γ ⊢ U ∈ (tUniv j).
Proof.
  move E : (tEq a b A) h => T h.
  move : a b A E.
  elim :  Γ T U / h => //.
  - qauto l:on use:Coherent_transitive.
  - hauto l:on use:Wt_Univ.
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

Lemma Wt_J_inv Γ t a b p U (h : Γ ⊢ (tJ t a b p) ∈ U) :
  exists A C i,
    Γ ⊢ p ∈ (tEq a b A) /\
    Γ ⊢ a ∈ A /\
    Γ ⊢ b ∈A /\
    (exists j, Γ ⊢ A ∈ (tUniv j)) /\
    (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) ⊢ C ∈ (tUniv i) /\
    Γ ⊢ t ∈ (subst_tm (tRefl .: a ..) C) /\
    Coherent (subst_tm (p .: b..) C) U /\
    exists j, Γ ⊢ U ∈ (tUniv j).
Proof.
  move E : (tJ t a b p) h => T h.
  move : t a b p E.
  elim :  Γ T U / h => //.
  - hauto lq:on rew:off use:Coherent_transitive.
  - move => Γ t a b p A i j C ha _ hb _ hA _ hp _ hC _ ht _ ? ? ? ? [] *; subst.
    exists A, C, i. repeat split => //.
    sfirstorder.
    sfirstorder use:Coherent_reflexive.
    have ? : Γ ⊢ (tJ t a b p) ∈ (subst_tm (p .: b..) C) by hauto l:on use:T_J.
    sfirstorder ctrs:Wt use:Wt_regularity.
Qed.

Lemma preservation_helper A0 A1 i j Γ a A :
  (A0 :: Γ) ⊢ a ∈ A ->
  Γ ⊢ A0 ∈ (tUniv i) ->
  Γ ⊢ A1 ∈ (tUniv j) ->
  Coherent A0 A1 ->
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
      * hauto lq:on use:Coherent_symmetric, Coherent_renaming.
    + move => _ n A2 Γ0 B ? ? [] *. subst. asimpl.
      change (var_tm (S n)) with (ren_tm shift (var_tm n)).
      apply weakening_Syn with (i := j) => //.
      apply T_Var; hauto lq:on db:wff.
  - eauto with wff.
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
  - apply Par_Coherent.
    sfirstorder use:P_Eq,Par_refl.
Qed.

Lemma Wt_Refl_inv Γ T (h : Γ ⊢ tRefl ∈ T) :
  exists a A, Γ ⊢ tRefl ∈ (tEq a a A)  /\
         Γ ⊢ a ∈ A /\
         Coherent (tEq a a A) T /\ exists i, Γ ⊢ T ∈ (tUniv i).
Proof.
  move E : tRefl h => p h.
  move : E.
  elim : p T / h=>//.
  - hauto lq:on rew:off use:Coherent_transitive.
  - hauto lq:on ctrs:Wt use:T_Eq_simpl, Coherent_reflexive.
Qed.

Lemma Wt_Refl_Coherent Γ a b A (h : Γ ⊢ tRefl ∈ (tEq a b A)) :
  Coherent a b.
Proof.
  qauto l:on use:Wt_Refl_inv, Coherent_eq_inj, Coherent_transitive, Coherent_symmetric.
Qed.

Lemma subject_reduction a b (h : a ⇒ b) : forall Γ A,
    Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A.
Proof.
  elim : a b /h => //.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hACoherent & j & hA).
    have ? : ⊢ Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
  - move => a0 a1 h0 ih0 Γ A /Wt_Abs_inv.
    intros (A1 & B & i & hPi & ha0 & hCoherent & j & hA).
    case /Wt_Pi_Univ_inv : hPi => hA0 hB.
    apply T_Conv with (A := tPi A1 B) (i := j) => //.
    apply T_Abs with (i := i).
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
    + qauto l:on ctrs:Wt use:preservation_helper, Par_Coherent.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 Γ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hCoherent & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : Coherent_transitive; eauto.
    apply Coherent_symmetric.
    apply Par_Coherent.
    apply Par_morphing; last by apply Par_refl.
    hauto q:on unfold:Par_m ctrs:Par inv:nat simp:asimpl.
  - move => a a0 b0 b1 haa0 iha hbb0 ihb Γ A0 /Wt_App_inv.
    intros (A1 & B & ha & hb0 & hCoherent & i & hA0).
    have /Wt_Abs_inv := ha; intros (A & B0 & k & hPi & ha0 & hCoherent' & j & hPi').
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
      * case; [by asimpl | sfirstorder use:Par_refl simp:asimpl].
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc Γ A /Wt_If_inv.
    move => [A0][ha0][hb0][hc0][hC][[i hA0]][j hAj].
    apply : T_Conv. apply T_If with (i := i); eauto. eauto.
    transitivity (subst_tm (a0..) A0)=>//.
    symmetry.
    apply Coherent_morphing. reflexivity. hauto lq:on inv:nat unfold:Par_m.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
  - move => a0 b0 A0 a1 b1 A1 ha0 iha0 ha1 iha1 hA0 ihA0 Γ A /Wt_Eq_inv.
    intros (ha0' & hb0' & (q & hA0') & (i & eq) & (j & hA)).
    apply T_Conv with (A := (tUniv i)) (i := j); eauto.
    hauto l:on ctrs:Wt use:@rtc_once.
  - move => t0 a0 b0 p0 t1 a1 b1 p1 ht iht ha iha hb ihb hp ihp Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (k & hA) & hC0 & ht0 & heq & (j & hU)).
    have ? : (tEq a0 b0 A ⇒ tEq a1 b1 A) by hauto lq:on ctrs:Par use:Par_refl.
    have ? : Coherent (tEq a0 b0 A) (tEq a1 b1 A) by hauto l:on use:@rtc_once.
    apply T_Conv with (A := subst_tm (p1 .: b1..) C) (i := j) => //.
    apply T_J_simpl with (A := A) (i := i).
    + hauto lq:on use:T_Eq_simpl, T_Conv.
    + eapply preservation_helper with (i := 0) (j := 0); eauto.
      * hauto drew:off ctrs:Wt,lookup use:T_Eq_simpl, weakening_Syn' db:wff.
      * hauto drew:off ctrs:Wt,lookup use:T_Eq_simpl, weakening_Syn' db:wff.
      * sfirstorder use:Par_Coherent, P_Eq, Par_renaming, Par_refl.
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
      * apply Par_Coherent.
        apply Par_morphing; hauto lq:on unfold:Par_m use:Par_refl inv:nat.
    + apply : Coherent_transitive; eauto.
      apply Coherent_symmetric.
      apply Par_Coherent.
      apply Par_morphing; last by apply Par_refl.
      hauto lq:on unfold:Par_m inv:nat use:Par_refl.
  - move => t0 a b t1 ht iht Γ U /Wt_J_inv.
    intros (A & C & i & hp0 & ha0 & hb0 & (j & hA) & hC & ht0 & heq & (k & hU')).
    apply iht.
    move : T_Conv ht0. move/[apply]. apply; eauto.
    apply : Coherent_transitive;eauto.
    have ? : Coherent a b by eauto using Wt_Refl_Coherent.
    replace (subst_tm (tRefl .: a..) C)
      with (subst_tm (a..)(subst_tm (tRefl..) C)); last by asimpl.
    replace (subst_tm (tRefl .: b..) C)
      with (subst_tm (b..)(subst_tm (tRefl..) C)); last by asimpl.
    apply Coherent_cong. reflexivity. auto.
Qed.


(* ----------------------------------------------- *)

Definition is_value (a : tm) :=
  match a with
  | tPi A B => true
  | tAbs a => true
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



Lemma Wt_Univ_winv Γ i U :
  Γ ⊢ (tUniv i) ∈ U ->
  exists j, Coherent (tUniv j)  U.
Proof.
  move E : (tUniv i) => U0 h.
  move : i E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

Lemma Wt_Void_winv Γ U :
  Γ ⊢ tVoid∈ U ->
  exists j, Coherent (tUniv j) U.
Proof.
  move E : tVoid => U0 h.
  move : E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

Lemma Wt_True_False_winv Γ a A (h : Γ ⊢ a ∈ A) :
  is_bool_val a -> Coherent tBool A.
Proof. induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive. Qed.

Lemma Wt_Bool_winv Γ A :
  Γ ⊢ tBool ∈ A ->
  exists i, Coherent (tUniv i) A.
Proof.
  move E : tBool => a h. move : E.
  induction h => //; qauto l:on ctrs:Wt use:Coherent_transitive, Coherent_reflexive.
Qed.

(* Canonical forms lemmas *)

Lemma wt_pi_canon a A B :
  nil ⊢ a ∈ (tPi A B) ->
  is_value a ->
  exists a0, a = tAbs a0.
Proof.
  case : a => //.
  - hauto lq:on.
  - qauto l:on use:Wt_Pi_inv, Coherent_consistent.
  - qauto l:on use:Wt_Void_winv, Coherent_consistent.
  - qauto l:on use:Wt_Univ_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_Bool_winv, Coherent_consistent.
  - qauto l:on use:Wt_Eq_inv, Coherent_consistent.
  - qauto l:on use:Wt_Refl_inv, Coherent_consistent.
Qed.

Lemma wt_switch_canon a :
  nil ⊢ a ∈ tBool ->
  is_value a ->
  is_bool_val a.
Proof.
  case : a => //.
  - qauto l:on use:Wt_Abs_inv, Coherent_consistent.
  - qauto l:on use:Wt_Pi_inv, Coherent_consistent.
  - qauto l:on use:Wt_Void_winv, Coherent_consistent.
  - qauto l:on use:Wt_Univ_winv, Coherent_consistent.
  - qauto l:on use:Wt_Bool_winv, Coherent_consistent.
  - qauto l:on use:Wt_Eq_inv, Coherent_consistent.
  - qauto l:on use:Wt_Refl_inv, Coherent_consistent.
Qed.

Lemma wt_refl_canon p a b A :
  nil ⊢ p ∈ (tEq a b A) ->
  is_value p ->
  p = tRefl.
Proof.
  case : p => //.
  - qauto l:on use:Wt_Abs_inv, Coherent_consistent.
  - qauto l:on use:Wt_Pi_inv, Coherent_consistent.
  - qauto l:on use:Wt_Void_winv, Coherent_consistent.
  - qauto l:on use:Wt_Univ_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_True_False_winv, Coherent_consistent.
  - qauto l:on use:Wt_Bool_winv, Coherent_consistent.
  - qauto l:on use:Wt_Eq_inv, Coherent_consistent.
Qed.

Lemma wt_progress a A (h :nil ⊢ a ∈ A) : is_value a \/ exists a0, a ⇒ a0.
Proof.
  move E : nil h => Γ h.
  move : E.
  elim: Γ a A/h; try hauto q:on depth:2.
  - hauto lq:on rew:off ctrs:Par use:wt_pi_canon, Par_refl.
  - hauto lq:on rew:off use:wt_switch_canon, Par_refl.
  - hauto lq:on rew:off ctrs:Par use:wt_refl_canon, Par_refl.
Qed.
