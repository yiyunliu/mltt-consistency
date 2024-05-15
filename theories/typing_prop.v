Require Import imports typing.

Lemma Red_WtL Γ a b A (h : Γ ⊢ a ⤳ b ∈ A) : Γ ⊢ a ∈ A.
Proof.
  induction h; hauto lq:on ctrs:Wt.
Qed.

Lemma Reds_Wt Γ a b A (h : Γ ⊢ a ⤳* b ∈ A) : Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
Proof. induction h; sfirstorder use:Red_WtL. Qed.

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

Lemma T_App' Γ a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Γ ⊢ a ∈ (tPi A B) ->
  Γ ⊢ b ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a b) ∈ B0.
Proof. move =>> ->. apply T_App. Qed.

Lemma E_App' Γ a0 b0 a1 b1 A B T:
  T = B[a0..] ->
  Γ ⊢ b0 ≡ b1 ∈ tPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  (* ----------------- *)
  Γ ⊢ tApp b0 a0 ≡ tApp b1 a1 ∈ T.
Proof. move =>> ->. apply E_App. Qed.

Lemma E_Beta' Γ A B a b i t T:
  t = b[a..] ->
  T = B[a..] ->
  Γ ⊢ tPi A B ∈ tUniv i ->
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp (tAbs A b) a ≡ t ∈ T.
Proof. move =>> -> ->. apply E_Beta. Qed.

(* ------------------------------------- *)
(* If a term is well-typed, then the context must be well-formed. *)

Lemma Wt_Wff Γ a A (h : Γ ⊢ a ∈ A) : ⊢ Γ.
Proof. elim : Γ a A / h => //. Qed.

Lemma renaming_Syn_helper ξ a b C :
  subst_tm (a ⟨ξ⟩ .: (b⟨ξ⟩)..) (ren_tm (upRen_tm_tm (upRen_tm_tm ξ)) C) = ren_tm ξ (subst_tm (a .: b ..) C).
Proof. by asimpl. Qed.

Lemma Wt_Univ Γ a A i
  (h : Γ ⊢ a ∈ A) :
  exists j, Γ ⊢ (tUniv i) ∈ (tUniv j).
Proof.
  exists (S i).
  qauto l:on use:Wt_Wff ctrs:Wt solve+:lia.
Qed.

Lemma Wt_Pi_inv Γ A B U (h : Γ ⊢ (tPi A B) ∈ U) :
  exists i, Γ ⊢ A ∈ (tUniv i) /\
         (A :: Γ) ⊢ B ∈ (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim :  Γ T U / h => //.
  - hauto lq:on use:Wt_Univ.
Qed.

Lemma renaming_wt_equiv :
  (forall Γ a A, Γ ⊢ a ∈ A -> forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ∈ A⟨ξ⟩) /\
  (forall Γ a b A, Γ ⊢ a ≡ b ∈ A -> forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ≡ b⟨ξ⟩ ∈ A⟨ξ⟩).
Proof.
  apply wt_mutual; try qauto l:on depth:1 ctrs:Wt,Equiv, lookup unfold:ren_ok.
  - hauto q:on ctrs:Wt,Wff use:good_renaming_up.
  - move => > _.
    hauto q:on ctrs:Wt, Wff use:good_renaming_up, Wt_Pi_inv.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - hauto q:on ctrs:Wff,Equiv use:good_renaming_up.
  - move => > + + _.
    hauto q:on ctrs:Wt,Wff,Equiv use:good_renaming_up, Wt_Pi_inv.
  - move => * /=. apply : E_App'; eauto; by asimpl.
  - move => > _ * /=. apply : E_Beta'; eauto. by asimpl. by asimpl.
    rewrite -/ren_tm.
    hauto lq:on ctrs:Wff use:good_renaming_up, Wt_Pi_inv.
Qed.

Lemma renaming_wt : forall Γ a A, Γ ⊢ a ∈ A -> forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ∈ A⟨ξ⟩.
Proof. have := renaming_wt_equiv. tauto. Qed.

Lemma renaming_wt_univ : forall Γ A i, Γ ⊢ A ∈ tUniv i -> forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ A⟨ξ⟩ ∈ tUniv i.
Proof. sfirstorder use:renaming_wt. Qed.

Lemma renaming_equiv : forall Γ a b A, Γ ⊢ a ≡ b ∈ A -> forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ≡ b⟨ξ⟩ ∈ A⟨ξ⟩.
Proof. have := renaming_wt_equiv. tauto. Qed.

Lemma R_App' Γ b0 b1 a A B T :
  T = B[a..] ->
  Γ ⊢ b0 ⤳ b1 ∈ tPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp b0 a ⤳ tApp b1 a ∈ T.
Proof. move => ->. apply R_App. Qed.

Lemma R_Beta' Γ A B a b i t T :
  t = b[a..] ->
  T = B[a..] ->
  Γ ⊢ tPi A B ∈ tUniv i ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp (tAbs A b) a ⤳ t ∈ T.
Proof. move => -> ->. apply R_Beta. Qed.

Lemma renaming_Red Γ a b A (h : Γ ⊢ a ⤳ b ∈ A) : forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ⤳ b⟨ξ⟩ ∈ A⟨ξ⟩.
Proof.
  elim : a b A / h.
  - move => *. apply : R_App'; eauto using renaming_wt. by asimpl.
  - move => A B a b i hPi hA hb ha Δ ξ hξ hΔ /=.
    apply R_Beta' with (B := ren_tm (upRen_tm_tm ξ) B) (i := i); try by asimpl.
    move /renaming_wt_univ : hPi. apply=>//.
    move /renaming_wt_univ : hA. apply=>//.
    have /= /Wt_Pi_inv : Δ ⊢  (tPi A B) ⟨ξ⟩ ∈ tUniv i by eauto using renaming_wt_univ.
    hauto lq:on ctrs:Wt,Wff use:renaming_wt, good_renaming_up.
    eauto using renaming_wt.
  - move => a b A B i h ih hAB Δ ξ hξ hΔ.
    have /= /R_Conv : Δ ⊢ A⟨ξ⟩  ≡ B⟨ξ⟩ ∈ (tUniv i)⟨ξ⟩ by hauto l:on use:renaming_equiv. apply.
    by apply ih.
Qed.

Lemma Wt_Equiv Γ a A : Γ ⊢ a ∈ A -> Γ ⊢ a ≡ a ∈ A.
Proof. induction 1; qauto depth:1 ctrs:Equiv. Qed.

Lemma Red_inj_Equiv Γ a b A : Γ ⊢ a ⤳ b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Proof. induction 1; qauto depth:1 use:Wt_Equiv ctrs:Equiv. Qed.

Lemma Reds_inj_Equiv Γ a b A : Γ ⊢ a ⤳* b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Proof.
  induction 1; hauto lq:on ctrs:Equiv use:Wt_Equiv, Red_inj_Equiv.
Qed.

Lemma morphing_wt_equiv