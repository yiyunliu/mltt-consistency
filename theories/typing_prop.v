Require Import imports typing.

(* Lemma Red_WtL Γ a b A (h : Γ ⊢ a ⤳ b ∈ A) : Γ ⊢ a ∈ A. *)
(* Proof. *)
(*   induction h; hauto lq:on ctrs:Wt. *)
(* Qed. *)

(* Lemma Reds_Wt Γ a b A (h : Γ ⊢ a ⤳* b ∈ A) : Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A. *)
(* Proof. induction h; sfirstorder use:Red_WtL. Qed. *)

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

Lemma T_App' Γ i a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Γ ⊢ a ∈ (tPi A B) ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ B ∈ tUniv i ->
  (* -------------------- *)
  Γ ⊢ (tApp a b) ∈ B0.
Proof. move =>> ->. apply T_App. Qed.

Lemma E_App' Γ a0 b0 a1 b1 A B T i :
  T = B[a0..] ->
  Γ ⊢ b0 ≡ b1 ∈ tPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ B ∈ tUniv i ->
  (* ----------------- *)
  Γ ⊢ tApp b0 a0 ≡ tApp b1 a1 ∈ T.
Proof. move =>> ->. apply E_App. Qed.

Lemma E_Beta' Γ A B a b i t T:
  t = b[a..] ->
  T = B[a..] ->
  Γ ⊢ tPi A B ∈ tUniv i ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp (tAbs A b) a ≡ t ∈ T.
Proof. move =>> -> ->. apply E_Beta. Qed.

(* ------------------------------------- *)
(* If a term is well-typed, then the context must be well-formed. *)

Lemma Wt_Wff Γ a A (h : Γ ⊢ a ∈ A) : ⊢ Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.
#[export]Hint Constructors Wff : wff.


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
  - move => * /=. apply : T_App'; eauto. by asimpl.
    rewrite -/ren_tm. hauto q:on ctrs:Wt use:good_renaming_up db:wff.
  - hauto q:on ctrs:Wff,Equiv use:good_renaming_up.
  - move => Γ A0 A1 a0 a1 B i hA ihA hA0 ihA0 hPi ihPi ha iha Δ ξ hξ hΔ /=.
    apply E_Abs with (i := i); eauto.
    apply iha.
    hauto q:on ctrs:Wt,Wff,Equiv use:good_renaming_up, Wt_Pi_inv.
    hauto q:on db:wff.
  - move => Γ a0 b0 a1 b1 A B i hb ihb ha iha hA ihA hB ihB Δ ξ hξ hΔ /=.
    apply : E_App'; eauto. by asimpl.
    rewrite -/ren_tm. hauto q:on use:good_renaming_up ctrs:Wff.
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
Proof. induction 1; hauto lq:on ctrs:Equiv, Wt. Qed.

Lemma Red_inj_Equiv Γ a b A : Γ ⊢ a ⤳ b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Admitted.
(* Proof. induction 1; try qauto depth:1 use:Wt_Equiv ctrs:Equiv. *)
(*        apply : E_App; eauto using Wt_Equiv. *)
(*        apply : T_App; eauto. *)
(* Qed. *)

Lemma Reds_inj_Equiv Γ a b A : Γ ⊢ a ⤳* b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Proof.
  induction 1; hauto lq:on ctrs:Equiv use:Wt_Equiv, Red_inj_Equiv.
Qed.

Definition subst_ok ρ Γ Δ :=
  forall i A, lookup i Γ A -> Δ ⊢ ρ i ∈ A [ ρ ].

Lemma weakening_wt Γ a A B i
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ∈ A) :
  (B :: Γ) ⊢ (ren_tm shift a) ∈ (ren_tm shift A).
Proof.
  apply : renaming_wt; eauto with wff.
  hauto lq:on ctrs:lookup unfold:ren_ok.
Qed.

Lemma weakening_equiv Γ a b A B i
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ≡ b ∈ A) :
  (B :: Γ) ⊢ (ren_tm shift a) ≡ ren_tm shift b ∈ (ren_tm shift A).
Proof.
  apply : renaming_equiv; eauto with wff.
  hauto lq:on ctrs:lookup unfold:ren_ok.
Qed.

Lemma weakening_equiv_univ Γ a b j B i
  (h0 : Γ ⊢ B ∈ (tUniv i))
  (h1 : Γ ⊢ a ≡ b ∈ tUniv j) :
  (B :: Γ) ⊢ (ren_tm shift a) ≡ ren_tm shift b ∈ tUniv j.
Proof.
  hauto lq:on use:weakening_equiv.
Qed.

Lemma subst_ok_suc Γ Δ A j ρ (h : subst_ok ρ Γ Δ)
  (hh : Δ ⊢ A [ρ] ∈ tUniv j) :
  subst_ok (ρ >> ren_tm S) Γ (A [ρ] :: Δ).
Proof.
  rewrite /subst_ok in h * => i A0 /h /weakening_wt.
  asimpl. eauto.
Qed.

Lemma good_morphing_up ρ k Γ Δ A
  (h : subst_ok ρ Γ Δ) :
  Δ ⊢ A[ρ] ∈ tUniv k ->
  subst_ok (up_tm_tm ρ) (A :: Γ) (A [ρ] :: Δ).
Proof.
  rewrite /subst_ok => h1.
  inversion 1=>*; subst.
  - apply T_Var => /=.
    + eauto with wff.
    + asimpl. apply : here'. by asimpl.
  - asimpl. have -> : A1[ρ >> ren_tm S] = A1[ρ]⟨S⟩ by asimpl.
    apply : weakening_wt; sfirstorder unfold:subst_ok.
Qed.

Lemma morphing_Syn :
  (forall Γ a A,  Γ ⊢ a ∈ A -> forall Δ ρ,
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ∈ A[ρ]) /\
  (forall Γ a b A,  Γ ⊢ a ≡ b ∈ A -> forall Δ ρ,
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ≡ b[ρ] ∈ A[ρ]).
Proof.
  apply wt_mutual; rewrite /subst_ok.
  (* --- Wt ------ *)
  (* Var *)
  - sfirstorder.
  (* Pi *)
  - move => *.
    apply T_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  (* Abs *)
  - move => *.
    apply : T_Abs; eauto.
    hauto q:on use:good_morphing_up, Wt_Pi_inv db:wff.
  (* App *)
  - move => * /=. apply : T_App'; eauto. by asimpl.
    rewrite -/subst_tm.
    hauto q:on use:good_morphing_up db:wff.
  (* Conv *)
  - hauto q:on ctrs:Equiv,Wt.
  (* Univ *)
  - hauto lq:on ctrs:Wt.

  (* ----- Equiv ------ *)
  (* Var *)
  - firstorder using Wt_Equiv.
  (* Sym *)
  - hauto lq:on ctrs:Equiv.
  (* Trans *)
  - hauto lq:on ctrs:Equiv.
  (* Pi *)
  - move => *.
    apply E_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  (* Abs *)
  - move => > ? ? _ ? _ * /=.
    apply : E_Abs; eauto.
    hauto l:on use:good_morphing_up, Wt_Pi_inv db:wff.
  (* App *)
  - move => Γ a0 b0 a1 b1 A B i hb ihb ha iha hba ihba hA ihA Δ ρ hρ hΔ /=.
    apply : E_App'; eauto. by asimpl.
    rewrite -/subst_tm. hauto q:on use:good_morphing_up db:wff.
  (* Beta *)
  - move => > _ /= *. apply : E_Beta'; eauto.
    by asimpl.
    by asimpl.
    hauto lq:on use:good_morphing_up, Wt_Pi_inv db:wff.
  (* Univ *)
  - hauto lq:on ctrs:Equiv.
  (* Conv *)
  - hauto q:on ctrs:Equiv.
Qed.

Lemma morphing_wt ρ Δ:
  (forall Γ a A,  Γ ⊢ a ∈ A ->
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ∈ A[ρ]).
Proof. sfirstorder use:morphing_Syn. Qed.

Lemma subst_wt Γ A a b B
  (h0 : (A :: Γ) ⊢ b ∈ B)
  (h1 : Γ ⊢ a ∈ A) :
  Γ ⊢ (subst_tm (a..) b) ∈ (subst_tm (a..) B).
Proof.
  apply : morphing_wt; eauto with wff.
  inversion 1; subst.
  - by asimpl.
  - asimpl; eauto using T_Var with wff.
Qed.

Lemma morphing_wt_univ ρ Δ:
  (forall Γ a i,  Γ ⊢ a ∈ tUniv i ->
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ∈ tUniv i).
Proof. hauto lq:on use:morphing_wt. Qed.

Lemma morphing_equiv ρ Δ:
  (forall Γ a b A,  Γ ⊢ a ≡ b ∈ A ->
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ≡ b[ρ] ∈ A[ρ]).
Proof. sfirstorder use:morphing_Syn. Qed.

Lemma morphing_equiv_univ ρ Δ :
  (forall Γ a b i,  Γ ⊢ a ≡ b ∈ tUniv i->
    subst_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ≡ b[ρ] ∈ tUniv i).
Proof. hauto lq:on use:morphing_equiv. Qed.

Lemma lookup_inv_cons i B Γ A (P : nat -> list tm -> tm -> Prop) :
  P 0 Γ B⟨S⟩ ->
  (forall j B, i = S j -> A = B⟨S⟩ -> lookup j Γ B -> P (S j) Γ A) ->
  lookup i (B:: Γ) A -> P i Γ A.
  move => h0 h1.
  elim/lookup_inv.
  - scongruence.
  - hauto lq:on.
Qed.

Lemma ctx_morph Γ A0 A1 a i B
  (h0 : Γ ⊢ A0 ≡ A1 ∈ tUniv i)
  (h1 : A0 :: Γ ⊢ a ∈ B)
  (h2 : Γ ⊢ A1 ∈ tUniv i) :
  A1 :: Γ ⊢ a ∈ B.
Proof.
  move : h1.
  move /(morphing_wt var_tm).
  asimpl. apply.
  - rewrite /subst_ok => i0 A.
    elim /lookup_inv_cons.
    + asimpl.
      apply T_Conv with (A := A1 ⟨S⟩) (i := i).
      apply T_Var. by eauto with wff.
      by constructor.
      apply weakening_equiv_univ with (i := i)=>//.
      by apply E_Sym.
    + move => j B0 ? ? ?. subst.
      asimpl.
      apply T_Var.
      by eauto with wff.
      by constructor.
  - eauto with wff.
Qed.

Lemma Equiv_Wt Γ a b A : Γ ⊢ a ≡ b ∈ A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
Proof.
  move => h. elim : Γ a b A / h.
  - hauto lq:on ctrs:Wt.
  - sfirstorder.
  - sfirstorder.
  - move => Γ i A0 B0 A1 B1 h0 [ih00 ih01] h1 [ih10 ih11] h.
    split. hauto lq:on ctrs:Equiv, Wt.
    apply T_Pi => //.
    move /(morphing_wt var_tm (A1 :: Γ)) : ih11. asimpl.
    apply; last by eauto with wff.
    rewrite /subst_ok.
    inversion 1; subst; asimpl.
    eapply T_Conv with (A := A1 ⟨S⟩) (i := i); eauto.
    hauto lq:on ctrs:Wt,lookup db:wff.
    apply E_Sym. change (tUniv i) with (tUniv i)⟨S⟩.
    by apply : weakening_equiv; eauto with wff.
    change (var_tm (S n)) with (var_tm n)⟨S⟩.
    apply weakening_wt with (i := i)=>//.
    hauto lq:on ctrs:Wt db:wff.
  - move => Γ A0 A1 a0 a1 B i hA [ihA0 ihA1] h0 ha [iha0 iha1].
    split.
    hauto lq:on ctrs:Wt.
    apply T_Conv with (A := tPi A1 B) (i := i).
    apply : T_Abs; eauto.
    (* morphing context *)
    sfirstorder use: ctx_morph.
    hauto lq:on ctrs:Equiv.
  - move => Γ a0 b0 a1 b1 A B i hb [ihb0 ihb1] ha [iha0 iha1] hA hB.
    split; first by eauto using T_App.
    apply T_Conv with (A := B[a1..]) (i := i);
      first by eauto using T_App.
    (* Need cong2 *)
    admit.
  - move => Γ A B a b i hT hb ha.
    move /Wt_Pi_inv : (hT) => [j][h0]h1 h2.
    split.
    + eapply T_App with (i := j); eauto.
      by apply : T_Abs; eauto.
    + eauto using subst_wt.
  - hauto lq:on ctrs:Wt.
  - hauto lq:on ctrs:Wt.
Admitted.

Definition subst2_ok ρ0 ρ1 Γ Δ :=
  forall i A, lookup i Γ A -> Δ ⊢ ρ0 i ≡ ρ1 i ∈ A [ ρ0 ].

(* Lemma subst2_lrefl ρ0 ρ1 Γ Δ : *)
(*   subst2_ok ρ0 ρ1 Γ Δ -> subst_ok ρ0 Γ Δ. *)
(* Proof. *)
(*   hauto lq:on use:Wt_Equiv, Equiv_Wt unfold:subst2_ok, subst_ok. *)
(* Qed. *)

Lemma subst2_up ρ0 ρ1 k Γ Δ A
  (h : subst2_ok ρ0 ρ1 Γ Δ) :
  Δ ⊢ A[ρ0] ∈ tUniv k ->
  subst2_ok (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A[ρ0] :: Δ).
Proof.
  rewrite /subst2_ok => h0 i A0.
  elim /lookup_inv_cons. asimpl.
  have -> : A[ρ0 >> ren_tm S] = A[ρ0]⟨S⟩ by asimpl.
  apply E_Var.
  hauto lq:on db:wff.
  by constructor.
  move => j B ? ? ?. subst.
  asimpl.
  have -> : B[ρ0 >> ren_tm S] = B[ρ0]⟨S⟩ by asimpl.
  apply weakening_equiv with (i := k)=>//.
  by apply h.
Qed.

Lemma morphing2_Syn :
  (forall Γ a A,  Γ ⊢ a ∈ A -> forall Δ ρ0 ρ1,
    subst2_ok ρ0 ρ1 Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ0] ≡ a[ρ1] ∈ A[ρ0]) /\
  (forall Γ a b A,  Γ ⊢ a ≡ b ∈ A -> forall Δ ρ0 ρ1,
    subst2_ok ρ0 ρ1 Γ Δ ->
    ⊢ Δ ->
  (* experimental version *)
    Δ ⊢ a[ρ0] ≡ a[ρ1] ∈ A[ρ0] /\
    Δ ⊢ b[ρ0] ≡ b[ρ1] ∈ A[ρ1]

  (* the most "intuitive" def *)
    (* Δ ⊢ a[ρ0] ≡ b[ρ1] ∈ A[ρ0] *)).
Proof.
  apply wt_mutual; rewrite /subst2_ok /=.
  (* Var *)
  - sfirstorder.
  (* Pi *)
  - move => Γ i A B hA ihA hB ihB Δ ρ0 ρ1 hρ hΔ.
    (* have ? : Δ ⊢ A[ρ0] ∈ tUniv i by sfirstorder use:morphing_wt_univ. *)
    apply E_Pi; eauto with wff.
    + apply ihB=>//.
      move => i0 A0.
      elim /lookup_inv_cons.
      * asimpl.
        have -> : A[ρ0 >> ren_tm S] = A[ρ0]⟨S⟩ by asimpl.
        apply E_Var.
        admit.
        (* hauto lq:on db:wff. *)
        by constructor.
      * move => j B0 ? ? ?. subst. asimpl.
        have -> : B0[ρ0 >> ren_tm S] = B0[ρ0]⟨S⟩ by asimpl.
        apply : weakening_equiv; eauto.
        admit.
      * (* hauto lq:on use:morphing_wt_univ db:wff. *)
        admit.
    + admit.
  (* Abs *)
  - admit.
  (* App *)
  - move => Γ a A B b i ha iha hb ihb hA ihA hB ihB Δ ρ0 ρ1 hρ hΔ.
    asimpl.
    eapply E_App' with (i := i); eauto. by asimpl.
    admit.
    (* have -> : B[b[ρ0] .: ρ0] = B[b..][ρ0] by asimpl. *)

    (* have -> : B[b[ρ1] .: ρ0] = B[b..][ρ1] by asimpl. *)
    (* apply T_App. *)
  (* Conv *)
  - move => Γ a A B i ha iha hE ihE Δ ρ0 *.
    apply E_Conv with (A := A[ρ0]) (i := i); eauto.
    sfirstorder use:morphing_equiv_univ.
  (* Univ *)
  - hauto lq:on ctrs:Equiv.
  - sfirstorder.
  - move => Γ a b A h ih Δ ρ0 ρ1 hρ0 hρ1 hρ hΔ.
    apply E_Trans with (b := a[ρ0]).
    + apply E_Sym.
      hauto lq:on ctrs:Equiv.
    +
Admitted.
