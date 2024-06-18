(* For comparison, this file shows the syntactic metatheory of the language.
   The main lemmas are preservation and progress. Together, these lemmas
   imply that well-typed terms either diverge or produce values.
   However, from our logical relation, we can already see that closed,
   well-typed terms reduce to normal forms (and we know that closed normal
   forms are values).
 *)

Require Import imports par geq conv typing typing_conv.

Module preservation
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).

Module ifacts := geq_facts lattice syntax ieq.
Import ifacts.

Module tcfacts := typing_conv_facts lattice syntax par ieq conv typing.
Import tcfacts.

Module solver := Solver lattice.
Import solver.

Import pfacts.

(* -------------------------------------------------- *)

Lemma here' : forall ℓ0 A Γ T, T = A ⟨shift⟩ ->  lookup 0 ((ℓ0, A) :: Γ) ℓ0 T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall ℓ0 ℓ1 n A Γ B T, T = A ⟨shift⟩ ->
      lookup n Γ ℓ0 A -> lookup (S n) ((ℓ1, B) :: Γ) ℓ0 T.
Proof. move => > ->. by apply there. Qed.

Lemma good_renaming_up ℓ0 ξ Γ Δ A :
  lookup_good_renaming ξ Γ Δ ->
  lookup_good_renaming (upRen_tm_tm ξ)  ((ℓ0, A) :: Γ) ((ℓ0, A⟨ξ⟩) :: Δ).
Proof.
  rewrite /lookup_good_renaming => h.
  move => i B.
  inversion 1 =>*; subst.
  - apply here'. by asimpl.
  - asimpl. apply : there'; eauto. by asimpl.
Qed.

Lemma good_renaming_suc ℓ0 ξ Γ A Δ
  (h : lookup_good_renaming ξ Γ Δ) :
  lookup_good_renaming (ξ >> S) Γ ((ℓ0, A⟨ξ⟩) :: Δ).
Proof.
  rewrite /lookup_good_renaming in h *.
  move => i ℓ A0 /h ?.
  asimpl. apply : there'; eauto. by asimpl.
Qed.
(* -------------------------------------------------- *)

(* Lemma T_Ind' Γ a b c A i T : *)
(*   T = A [c..] -> *)
(*   tNat :: Γ ⊢ A ∈ tUniv i -> *)
(*   Γ ⊢ a ∈ A [tZero..] -> *)
(*   A :: tNat :: Γ ⊢ b ∈ A[tSuc (var_tm 0) .: S >> var_tm]⟨S⟩ -> *)
(*   Γ ⊢ c ∈ tNat -> *)
(*   (* ------------ *) *)
(*   Γ ⊢ tInd a b c ∈ T. *)
(* Proof. move  =>> ->. apply T_Ind. Qed. *)

Lemma T_App' Γ ℓ ℓ0 a A B b T :
  T = (B [ b.. ]) ->
  Γ ⊢ a ; ℓ ∈ (tPi ℓ0 A B) ->
  Γ ⊢ b ; ℓ0 ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a ℓ0 b) ; ℓ ∈ T.
Proof. move =>> ->. apply T_App. Qed.

Lemma T_J'  Γ t a b p A i j C ℓ ℓp ℓT ℓ0 ℓ1 T :
  T = (C [p .: b..]) ->
  ℓ1 ⊆ ℓ0 ->
  ℓp ⊆ ℓ ->
  Γ ⊢ a ; ℓ1 ∈ A ->
  Γ ⊢ b ; ℓ1 ∈ A ->
  Γ ⊢ A ; ℓT ∈ (tUniv j) ->
  Γ ⊢ p ; ℓp ∈ (tEq ℓ0 a b A) ->
  ((ℓp, tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A)) :: (ℓ1, A) :: Γ) ⊢ C ; ℓ0 ∈ (tUniv i) ->
  Γ ⊢ t ; ℓ ∈ (C [tRefl .: a ..]) ->
  Γ ⊢ (tJ t p) ; ℓ ∈ T.
Proof. move =>> ->. apply T_J. Qed.

Lemma T_Pack' Γ ℓ ℓ0 a A b B ℓT i B0:
  B0 = (subst_tm (a..) B) ->
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b ; ℓ ∈ B0 ->
  Γ ⊢ tSig ℓ0 A B ; ℓT ∈ tUniv i ->
  (* -------------------- *)
  Γ ⊢ tPack ℓ0 a b ; ℓ ∈ tSig ℓ0 A B.
Proof. move =>> ->. apply T_Pack. Qed.

Lemma T_Let' Γ ℓ ℓp ℓ0 a b ℓT A B C i j C0 C1 :
  C0 = (subst_tm (a..) C) ->
  C1 = (subst_tm ((tPack ℓ0 (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)) C) ->
  ℓp ⊆ ℓ ->
  Γ ⊢ A ; ℓT ∈ tUniv j ->
  (ℓ0, A) :: Γ ⊢ B ; ℓT ∈ tUniv j ->
  Γ ⊢ a ; ℓp ∈ tSig ℓ0 A B ->
  (ℓp, B) :: (ℓ0, A) :: Γ ⊢ b ; ℓ ∈ C1 ->
  (ℓp, tSig ℓ0 A B) :: Γ ⊢ C ; ℓT ∈ tUniv i ->
  (* ----------------------- *)
  Γ ⊢ tLet ℓ0 ℓp a b ; ℓ ∈ C0.
Proof. move => ->->. apply T_Let. Qed.

(* ------------------------------------- *)
(* If a term is well-typed, then the context must be well-formed. *)

Lemma Wt_Wff Γ ℓ a A (h : Γ ⊢ a ; ℓ ∈ A) : ⊢ Γ.
Proof. elim : Γ ℓ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.
#[export]Hint Constructors Wff : wff.

(* -------------------------------------------------- *)
(* Inversion lemmas for well-typed terms. *)

Lemma Wt_Univ Γ ℓ a A i
  (h : Γ ⊢ a ; ℓ ∈ A) :
  exists ℓ0 j, Γ ⊢ (tUniv i) ; ℓ0 ∈ (tUniv j).
Proof.
  exists ℓ,  (S i).
  qauto l:on use:Wt_Wff ctrs:Wt.
Qed.

Lemma Wt_Pi_inv Γ ℓ ℓ0 A B U (h : Γ ⊢ tPi ℓ0 A B ; ℓ ∈ U) :
  exists i j, Γ ⊢ A ; ℓ ∈ (tUniv i) /\
         ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv j) /\
         conv (c2e Γ) (tUniv (max i j)) U /\
         exists ℓ i, Γ ⊢ U ; ℓ ∈ (tUniv i).
Proof.
  move E : (tPi ℓ0 A B) h => T h.
  move : A B E.
  elim :  Γ ℓ T U / h => //.
  - move => Γ i j ℓ ℓ1 A B hA _ hB _ ? ? [*]. subst.
    do 2 eexists. repeat split; eauto using Wt_Univ.
    hauto l:on ctrs:Wt use:typing_conv.
  - hauto lq:on rew:off use:cfacts.conv_trans.
Qed.

Lemma Wt_Sig_inv Γ ℓ ℓ0 A B U (h : Γ ⊢ (tSig ℓ0 A B) ; ℓ ∈ U) :
  exists i j, Γ ⊢ A ; ℓ ∈ (tUniv i) /\
         ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv j) /\
         conv (c2e Γ) (tUniv (max i j)) U /\
         exists ℓ i, Γ ⊢ U ; ℓ ∈ (tUniv i).
Proof.
  move E : (tSig ℓ0 A B) h => T h.
  move : A B E.
  elim : Γ ℓ T U / h => //.
  - hauto lq:on rew:off use:cfacts.conv_trans.
  - move => Γ i j ℓ ℓ1 A B hA _ hB _ ? ? [*]. subst.
    exists i, j. repeat split; eauto using Wt_Univ.
    hauto l:on ctrs:Wt use:typing_conv.
Qed.

Lemma Wt_Pi_Univ_inv Γ ℓ ℓ0 A B n (h : Γ ⊢ (tPi ℓ0 A B) ; ℓ ∈ (tUniv n)) :
  exists i j,
  n = max i j /\
  Γ ⊢ A ; ℓ ∈ (tUniv i) /\
  ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv j).
Proof.
  move /Wt_Pi_inv : h.
  move => [i][j][hA][hB][h1][ℓ1][k]h2.
  exists i, j.
  have ? : n = max i j by hauto l:on use:cfacts.conv_univ_inj. subst.
  split=>//.
Qed.

Lemma Wt_Abs_inv Γ ℓ ℓ0 a T (h : Γ ⊢ (tAbs ℓ0 a) ; ℓ ∈ T) :
  exists ℓ1 A B i, Γ ⊢ (tPi ℓ0 A B) ; ℓ1 ∈ (tUniv i) /\
         ((ℓ0, A) :: Γ) ⊢ a ; ℓ ∈ B /\
         conv (c2e Γ) (tPi ℓ0 A B) T /\
         exists ℓ i, (Γ ⊢ T ; ℓ ∈ (tUniv i)).
Proof.
  move E : (tAbs ℓ0 a) h => a0 h.
  move : a E.
  elim : Γ ℓ a0 T / h => //.
  - hauto lq:on rew:off use:typing_conv.
  - hauto lq:on use:cfacts.conv_trans.
Qed.

Lemma Wt_Sig_Univ_inv Γ ℓ ℓ0 A B n (h : Γ ⊢ (tSig ℓ0 A B) ; ℓ ∈ (tUniv n)) :
  exists i j,
  n = max i j /\
  Γ ⊢ A ; ℓ ∈ (tUniv i) /\
  ((ℓ0, A) :: Γ) ⊢ B; ℓ ∈ (tUniv j).
Proof.
  move /Wt_Sig_inv : h.
  move => [i][j][hA][hB][h1][ℓ1][k]h2.
  have ? : n = max i j by hauto lq:on use:cfacts.conv_univ_inj. subst.
  sfirstorder.
Qed.

Lemma Wt_Pack_inv Γ ℓ ℓ0 a b T (h : Γ ⊢ tPack ℓ0 a b ; ℓ ∈ T) :
  exists ℓT A B i, Γ ⊢ a ; ℓ0 ∈ A /\
    Γ ⊢ b ; ℓ ∈ B[a..] /\
    Γ ⊢ tSig ℓ0 A B ; ℓT ∈ tUniv i /\
    conv (c2e Γ) (tSig ℓ0 A B) T /\
    exists ℓ j, (Γ ⊢ T ; ℓ ∈ tUniv j).
Proof.
  move E : (tPack ℓ0 a b) h => p h.
  move : a b E.
  elim : Γ ℓ p T / h => //.
  - hauto lq:on use:cfacts.conv_trans.
  - hauto lq:on use:typing_conv.
Qed.

Lemma subsumption Γ ℓ a A (h : Γ ⊢ a ; ℓ ∈ A) :
  forall ℓ', ℓ ⊆ ℓ' -> Γ ⊢ a ; ℓ' ∈ A.
Proof.
  elim : Γ ℓ a A / h; eauto 5 using solver.leq_trans with wt.
Qed.
(* -------------------------------------------------- *)

Lemma renaming_Syn_helper ξ a b C :
  subst_tm (a ⟨ξ⟩ .: (b⟨ξ⟩)..) (ren_tm (upRen_tm_tm (upRen_tm_tm ξ)) C) = ren_tm ξ (subst_tm (a .: b ..) C).
Proof. by asimpl. Qed.

Lemma renaming_Syn
  Γ ℓ a A (h : Γ ⊢ a ; ℓ ∈ A) : forall Δ ξ,
    lookup_good_renaming ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ a⟨ξ⟩ ; ℓ ∈ A⟨ξ⟩.
Proof.
  elim : Γ ℓ a A / h; try qauto l:on depth:1 ctrs:Wt,lookup unfold:lookup_good_renaming.
  (* Pi *)
  - hauto q:on ctrs:Wt,Wff use:good_renaming_up.
  - move => Γ ℓ ℓ0 ℓ1 A a B i hPi ihPi ha iha Δ ξ hξ hΔ //=.
    apply : T_Abs; eauto.
    move : ihPi (hξ) (hΔ) => /[apply]/[apply]/=/Wt_Pi_Univ_inv.
    move => [k0][k1][?][h0]h1. subst.
    hauto l:on use:good_renaming_up db:wff.
  (* App *)
  - move => * /=. apply : T_App'; eauto; by asimpl.
  (* Pi *)
  - qauto l:on ctrs:Wt use:cfacts.conv_renaming, lookup_good_renaming_iok_subst_ok.
  (* J *)
  - move => Γ t a b p A i j C ℓ ℓp ℓA ℓ0 ℓ1 hle0 hle1 ha iha hb ihb hA ihA hp  ihp hC ihC ht iht Δ ξ hξ hΔ /=.
    rewrite -renaming_Syn_helper.
    eapply T_J with (ℓ0 := ℓ0) (ℓ1 := ℓ1) (ℓp := ℓp); eauto.
    + apply ihC.
      * move /good_renaming_up in hξ.
        move /(_ ℓ1 A) in hξ.
        move /good_renaming_up in hξ.
        move /(_ ℓp (tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A))) in hξ.
        by asimpl in hξ.
      * move => [:hwff] [:hleq].
        eapply Wff_cons with (ℓ := ℓ0 ∪ ℓ1 ∪ ℓA); first by (abstract : hwff; hauto q:on ctrs:Wff).
        apply T_Eq with (i := 0) (j:= j);eauto.  asimpl.
        abstract : hleq.
        solve_lattice.

        apply subsumption with (ℓ := ℓ1).
        asimpl. sfirstorder use:good_renaming_suc.
        solve_lattice.

        apply : T_Var=>//. constructor.
        solve_lattice.

        apply subsumption with (ℓ := ℓA).
        asimpl. sfirstorder use:good_renaming_suc.
        solve_lattice.
    + move : iht hξ hΔ. repeat move/[apply]. by asimpl.
  (* Sig *)
  - hauto q:on ctrs:Wt,Wff use:good_renaming_up.
  (* - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ξ hξ hΔ /=. *)
  (*   apply  T_Ind' with (a := ren_tm ξ a) (A := ren_tm (upRen_tm_tm ξ) A) (i := i). *)
  (*   + by asimpl. *)
  (*   + apply ihA. by apply good_renaming_up. *)
  (*     apply Wff_cons with (i := 0); qauto l:on ctrs:Wt. *)
  (*   + have -> : A ⟨upRen_tm_tm ξ⟩[tZero..] = A[tZero..]⟨ξ⟩ by asimpl. auto. *)
  (*   + move /(_ (A ⟨upRen_tm_tm ξ⟩ :: tNat :: Δ) (upRen_tm_tm (upRen_tm_tm ξ))) *)
  (*       : ihb. asimpl. apply. *)
  (*     * case => [A0|[A0|n]]. *)
  (*       inversion 1; subst. asimpl. *)
  (*       apply here'. by asimpl. *)

  (*       elim /lookup_inv=>// _ []// A1 Γ0 B  h _ [*]. subst. *)
  (*       have -> : A1 = tNat by hauto lq:on inv:lookup. *)
  (*       asimpl. apply : there'; last by sfirstorder ctrs:lookup. by asimpl. *)

  (*       move => A0 h. *)
  (*       have {h} : exists A1, lookup n Γ A1 /\ A0 = A1 ⟨S⟩ ⟨S⟩ by hauto lq:on inv:lookup. *)
  (*       move => [A1 [hA1 hA1']]. subst. *)
  (*       simpl. asimpl. *)
  (*       apply : there'; cycle 1. apply : there'; cycle 1. *)
  (*       sfirstorder. *)
  (*       done. *)
  (*       by asimpl. *)
  (*     * have ? : ⊢ tNat :: Δ by hauto lq:on ctrs:Wt db:wff. *)
  (*       eauto using good_renaming_up with wff. *)
  (*   + auto. *)
  - move => Γ ℓ ℓ0 a A b B ℓT i ha iha hb ihb hSig ihSig Δ ξ hξ hΔ /=.
    eapply T_Pack' with (B0 := B[a..] ⟨ξ⟩); eauto. by asimpl.
  - move => Γ ℓ ℓp ℓ0 a b ℓT A B C i j hA ? ihA hB ihB ha iha hb ihb hS ihS Δ ξ hξ hΔ /=.
    eapply T_Let' with
      (C := C ⟨upRen_tm_tm ξ⟩)
      (C1 := C[(tPack ℓ0 (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] ⟨upRen_tm_tm (upRen_tm_tm ξ)⟩);
      eauto => /=.
    1-2: by asimpl.
    + sauto q:on dep:on use:good_renaming_up.
    + hauto q:on use:Wff_cons, good_renaming_up.
    + rewrite -/ren_tm.
      hauto q:on ctrs:Wt use:Wff_cons, good_renaming_up.
Qed.

Lemma weakening_Syn Γ ℓ ℓ0 ℓ1 a A B i
  (h0 : Γ ⊢ B ; ℓ0 ∈ (tUniv i))
  (h1 : Γ ⊢ a ; ℓ ∈ A) :
  ((ℓ1, B) :: Γ) ⊢ (ren_tm shift a) ; ℓ ∈ (ren_tm shift A).
Proof.
  apply : renaming_Syn; eauto with wff.
  hauto lq:on ctrs:lookup unfold:lookup_good_renaming.
Qed.

Lemma weakening_Syn' Γ ℓ ℓ0 ℓ1 a A A0 B i
  (he : A0 = ren_tm shift A)
  (h0 : Γ ⊢ B ; ℓ0 ∈ (tUniv i))
  (h1 : Γ ⊢ a ; ℓ ∈ A) :
  ((ℓ1, B) :: Γ) ⊢ (ren_tm shift a) ; ℓ ∈ A0.
Proof. sfirstorder use:weakening_Syn. Qed.

Definition lookup_good_morphing ρ Γ Δ :=
  forall i ℓ A, lookup i Γ ℓ A -> Δ ⊢ ρ i ; ℓ ∈ A [ ρ ].

Lemma good_morphing_suc Γ ℓ0 ℓ1 Δ A j ρ (h : lookup_good_morphing ρ Γ Δ)
  (hh : Δ ⊢ A [ρ] ; ℓ0 ∈ tUniv j) :
  lookup_good_morphing (ρ >> ren_tm S) Γ ((ℓ1, A [ρ]) :: Δ).
Proof.
  rewrite /lookup_good_morphing in h * => i ℓ A0 /h /weakening_Syn.
  asimpl. eauto.
Qed.

Lemma good_morphing_up ρ k ℓ ℓ0 Γ Δ A
  (h : lookup_good_morphing ρ Γ Δ) :
  Δ ⊢ A[ρ] ; ℓ ∈ tUniv k ->
  lookup_good_morphing (up_tm_tm ρ) ((ℓ0, A) :: Γ) ((ℓ0, A [ρ]) :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply : T_Var => /=.
    + eauto with wff.
    + asimpl. apply : here'. by asimpl.
    + by rewrite meet_idempotent.
  - apply : weakening_Syn'; cycle 2.
    rewrite /lookup_good_morphing in h.
    + sfirstorder unfold:lookup_good_morphing.
    + by asimpl.
    + sfirstorder.
Qed.

Lemma good_morphing_iok_subst_ok ρ Γ Δ :
  lookup_good_morphing ρ Γ Δ ->
  iok_subst_ok ρ (c2e Γ) (c2e Δ).
Proof.
  rewrite /lookup_good_morphing /iok_subst_ok.
  hauto lq:on use:lookup_elookup, elookup_lookup, typing_iok.
Qed.

Lemma morphing_Syn Γ ℓ a A (h : Γ ⊢ a ; ℓ ∈ A) : forall Δ ρ,
    lookup_good_morphing ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ; ℓ ∈ A[ρ].
Proof.
  elim : Γ ℓ a A / h; try qauto l:on depth:1 ctrs:Wt.
  - asimpl.
    sfirstorder use:subsumption.
  - move => *.
    apply T_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  (* Abs *)
  - move => Γ ℓ ℓ0 ℓ1 A a B i hPi ihPi ha iha Δ ξ hξ hΔ /=.
    apply : T_Abs; eauto.
    move : ihPi (hξ) (hΔ); repeat move/[apply].
    rewrite/=. move /Wt_Pi_Univ_inv.
    hauto lq:on use:good_morphing_up db:wff.
  (* App *)
  - move => * /=. apply : T_App'; eauto; by asimpl.
  (* Conv *)
  - qauto l:on use:T_Conv, cfacts.conv_subst, good_morphing_iok_subst_ok.
  (* - move => Γ a b c A i hA ihA ha iha hb ihb hc ihc Δ ρ hρ hΔ /=. *)
  (*   have ? : Wff (tNat :: Δ) by apply Wff_cons with (i := 0); eauto using T_Nat. *)
  (*   apply T_Ind' with (A := subst_tm (up_tm_tm ρ) A) (i := i); first by asimpl. *)
  (*   + hauto lq:on ctrs:Wt use:good_morphing_up. *)
  (*   + move /iha : hρ {iha}. *)
  (*     asimpl. tauto. *)
  (*   + have hw : lookup_good_morphing (up_tm_tm ρ) (tNat :: Γ) (tNat :: Δ) *)
  (*       by hauto lq:on ctrs:Wt use:good_morphing_up db:wff. *)
  (*     have /ihb : lookup_good_morphing (up_tm_tm (up_tm_tm ρ)) (A :: tNat :: Γ) (A[up_tm_tm ρ] :: tNat :: Δ) by hauto lq:on ctrs:Wt use:good_morphing_up db:wff. *)
  (*     asimpl. substify. apply. *)
  (*     apply : Wff_cons=>//. *)
  (*     apply ihA=>//. *)
  (*     move : hw. asimpl. by substify. *)
  (*   + auto. *)
  (* J *)
  - move => Γ t a b p A i j C ℓ ℓp ℓT ℓ0 ℓ1 ? ?
             ha iha hb ihb hA ihA  hp
             ihp hC ihC ht iht Δ ξ hξ hΔ /=.
    have ? : Wt Δ ℓ1 (subst_tm ξ a) (subst_tm ξ A) by hauto l:on.
    have hwff : Wff ((ℓ1, subst_tm ξ A) :: Δ) by eauto using Wff_cons.
    eapply T_J' with (ℓ0 := ℓ0) (ℓp := ℓp) (i := i) (C := (subst_tm (up_tm_tm (up_tm_tm ξ)) C)) (b := b [ξ]); eauto; first by asimpl.
    + move => [:hwteq].
      apply ihC.
      * move : ihA (hξ) (hΔ); repeat move/[apply].
        move : good_morphing_up (hξ). repeat move/[apply]. move/(_ ℓ1).
        move : good_morphing_up. repeat move/[apply].
        move /(_ 0 (ℓT ∪ ℓ1 ∪ ℓ0) ℓp (tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A))).
        asimpl. apply. abstract:hwteq. apply T_Eq with (j := j).
        solve_lattice.

        apply (subsumption _ ℓ1).
        apply : iha=>//.
        hauto lq:on use:good_morphing_suc.
        solve_lattice.

        apply : subsumption; eauto.
        apply : T_Var; eauto.
        apply here'. by asimpl.
        solve_lattice.

        apply (subsumption _ ℓT).
        hauto lq:on use:good_morphing_suc.
        solve_lattice.
      * apply Wff_cons with (ℓ := ℓT ∪ ℓ1 ∪ ℓ0) (i := 0)=>//.
        by asimpl.
    + asimpl.
      have -> : C[tRefl .: (a[ξ] .: ξ)] = C[tRefl .: (a..)][ξ] by asimpl.
      by apply : iht.
  - move => *. apply T_Sig; eauto.
    hauto lq:on use:good_morphing_up, Wff_cons.
  - move => Γ ℓ ℓ0 a A b B ℓT i hA ihA hB ihB hS ihS Δ ρ hρ hΔ.
    eapply T_Pack' with (B0 := B[a .: var_tm][ρ]); eauto. by asimpl.
  - move => Γ ℓ ℓp ℓ0 a b ℓT A B C i j ? hA ihA hB ihB ha iha hb ihb hS ihS Δ ρ hρ hΔ.
    eapply T_Let' with
      (C := C[up_tm_tm ρ])
      (C1 := C[tPack ℓ0 (var_tm 1) (var_tm 0) .: (S >> S) >> var_tm][up_tm_tm (up_tm_tm ρ)]);
      eauto.
    + by asimpl.
    + by asimpl; substify.
    + hauto lq:on use:good_morphing_up, Wff_cons.
    + hauto lq:on use:good_morphing_up, Wff_cons.
    + hauto q:on ctrs:Wt, tm use:good_morphing_up, Wff_cons.
Qed.

Lemma subst_Syn Γ ℓ ℓ0 A a b B
  (h0 : ((ℓ0, A) :: Γ) ⊢ b ; ℓ ∈ B)
  (h1 : Γ ⊢ a ; ℓ0 ∈ A) :
  Γ ⊢ (subst_tm (a..) b) ; ℓ ∈ (subst_tm (a..) B).
Proof.
  apply : morphing_Syn; eauto with wff.
  inversion 1; subst.
  - by asimpl.
  - asimpl;
      hauto lq:on rew:off use:T_Var db:wff solve+:(by solve_lattice).
Qed.

Lemma subst_Syn_Univ Γ ℓ ℓ0 A a b i :
  ((ℓ0, A) :: Γ) ⊢ b ; ℓ ∈ tUniv i ->
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b[a..] ; ℓ ∈ tUniv i.
Proof.
  change (tUniv i) with (tUniv i)[a..].
  apply subst_Syn.
Qed.

Lemma Wff_lookup : forall Γ i ℓ0 A,
    ⊢ Γ -> lookup i Γ ℓ0 A -> exists ℓ j, Γ ⊢ A; ℓ ∈ tUniv j.
Proof.
  move => Γ + + + h.
  elim : Γ / h.
  - inversion 1.
  - move => Γ ℓ0 ℓ A i h ih h0.
    move => i0 ℓ1 A0.
    elim /lookup_inv.
    + hauto l:on inv:lookup use:weakening_Syn.
    + move => _ n A1 Γ0 ℓ2 B + ? []*. subst.
      move /ih => [ℓ2 [j ?]].
      exists ℓ2, j. apply : weakening_Syn'; eauto. done.
Qed.

Lemma Wt_regularity Γ ℓ a A
  (h : Γ ⊢ a ; ℓ ∈ A) :
  exists ℓ0 i, Γ ⊢ A ; ℓ0 ∈ (tUniv i).
Proof.
  elim: Γ ℓ a A/h; try qauto ctrs:Wt depth:2.
  - sfirstorder use:Wff_lookup.
  - hauto lq:on ctrs:Wt db:wff.
  - hauto q:on use:subst_Syn, Wt_Pi_Univ_inv.
  - hauto lq:on ctrs:Wt db:wff.
  - hauto lq:on ctrs:Wt db:wff.
  - move => Γ _ a ℓ0 A hΓ ha [ℓA [i hA]].
    exists (ℓ0 ∪ ℓA), 0.
    hauto use:T_Eq lq:on use:subsumption solve+:(by solve_lattice).
  - hauto lq:on ctrs:Wt db:wff.
  - move => Γ t a b p A i j C ℓ ℓp ℓT ℓ0 ℓ1 ? ha iha hb ihb hA ihA hp ihp hC ihC ht iht.
    exists ℓ0, i. change (tUniv i) with (subst_tm (p .: b..) (tUniv i)).
    apply : morphing_Syn; eauto with wff.
    move => k ℓA A0.
    elim /lookup_inv.
    + move => ? > ? [] *. subst. by asimpl.
    + move => _ n A1 Γ0 ℓ2 B + ? [] *. subst. simpl.
      inversion 1; subst.
      * by asimpl.
      * asimpl. apply : T_Var; eauto with wff. solve_lattice.
  - hauto lq:on ctrs:Wt db:wff.
 - eauto using subst_Syn_Univ.
Qed.

Lemma Wt_App_inv Γ ℓ ℓ0 b a T (h : Γ ⊢ (tApp b ℓ0 a) ; ℓ ∈ T) :
  exists A B, Γ ⊢ b ; ℓ ∈ tPi ℓ0 A B /\
         Γ ⊢ a ; ℓ0 ∈ A /\
         conv (c2e Γ) B[a..]  T /\
         exists ℓ i, Γ ⊢ T; ℓ ∈ tUniv i.
Proof.
  move E : (tApp b ℓ0 a) h => ba h.
  move : b a E.
  elim : Γ ℓ ba T /h => //.
  - move => Γ ℓ ℓ1 a A B b h0 _ h1 _ ? ? [] *; subst.
    exists A, B; repeat split => //.
    + apply cfacts.conv_subst with (Ξ := ℓ1 :: c2e Γ).
      * case.
        rewrite /elookup //=. hauto lq:on use:typing_iok.
        move => n ℓ0 ?.
        have : elookup n (c2e Γ) ℓ0 by sfirstorder unfold:elookup.
        asimpl. sfirstorder use:meet_idempotent, IO_Var.
      * move /Wt_regularity : h0.
        move => [ℓ0][i]/Wt_Pi_Univ_inv.
        sfirstorder use:typing_conv.
    + hauto lq:on ctrs:Wt use:Wt_Pi_Univ_inv, subst_Syn_Univ, Wt_regularity.
  - hauto lq:on rew:off use:cfacts.conv_trans.
Qed.

(* Lemma Wt_Ind_inv Γ a b c T (h : Γ ⊢ (tInd a b c) ∈ T) : *)
(*   exists A, Γ ⊢ a ∈ A[tZero..] /\ *)
(*        A :: tNat :: Γ ⊢ b ∈ A [tSuc (var_tm 0) .: S >> var_tm]⟨S⟩  /\ *)
(*          Γ ⊢ c ∈ tNat /\ *)
(*          A[c..] <: T /\ *)
(*          (exists j, tNat :: Γ ⊢ A ∈ tUniv j) /\ *)
(*          exists i, Γ ⊢ T ∈ tUniv i. *)
(* Proof. *)
(*   move E : (tInd a b c) h => a0 h. *)
(*   move : a b c E. *)
(*   elim : Γ a0 T / h => //. *)
(*   - hauto lq:on rew:off use:Sub_transitive. *)
(*   - move => Γ a b c A i hA _ ha _ hb _ hc _ ? ? ?[*]. subst. *)
(*     exists A. repeat split=>//. *)
(*     + apply Sub_reflexive. *)
(*     + eauto using subst_Syn_Univ. *)
(*     + eauto using subst_Syn_Univ. *)
(* Qed. *)

Lemma Wt_Eq_inv Γ ℓ0 ℓ a b A U (h : Γ ⊢ (tEq ℓ0 a b A) ; ℓ ∈ U) :
  ℓ0 ⊆ ℓ /\
  Γ ⊢ a ; ℓ0 ∈ A /\
  Γ ⊢ b ; ℓ0 ∈ A /\
  (exists q,
  Γ ⊢ A ; ℓ ∈ (tUniv q)) /\
  (exists i, conv (c2e Γ) (tUniv i) U) /\ exists ℓ j, Γ ⊢ U ; ℓ ∈ (tUniv j).
Proof.
  move E : (tEq ℓ0 a b A) h => T h.
  move : a b A ℓ0 E.
  elim :  Γ ℓ T U / h => //.
  - hauto l:on use:cfacts.conv_trans.
  - hauto q:on use:T_Univ, typing_conv db:wff.
Qed.

Lemma Wt_Let_inv Γ ℓ ℓ0 ℓ1 a b T (h : Γ ⊢ tLet ℓ0 ℓ1 a b ; ℓ ∈ T) :
  ℓ1 ⊆ ℓ /\
  exists i j ℓT A B C,
    Γ ⊢ A ; ℓT ∈ tUniv j /\
    (ℓ0, A) :: Γ ⊢ B ; ℓT ∈ tUniv j /\
    Γ ⊢ a ; ℓ1 ∈ tSig ℓ0 A B /\
    (ℓ1, B) :: (ℓ0, A) :: Γ ⊢ b ; ℓ ∈ C[(tPack ℓ0 (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] /\
    (ℓ1, tSig ℓ0 A B) :: Γ ⊢ C ; ℓT ∈ tUniv i /\
    conv (c2e Γ) C[a..] T /\
    (exists ℓ i, Γ ⊢ T ; ℓ ∈ tUniv i).
Proof.
  move E : (tLet ℓ0 ℓ1 a b) h => a0 h.
  move : ℓ0 ℓ1 a b E.
  elim : Γ ℓ a0 T / h => //.
  - move => Γ ℓ ℓ0 a0 T U i ha0 ih0 hU _ hSub ℓ1 ℓ2 a b E. subst.
    specialize ih0 with (1 := eq_refl).
    move : ih0; intros (? & j & k & ℓT & A & B & C & hA & hB & ha & hb & hC & hCoherent & hT).
    split => //.
    exists j, k, ℓT, A,B,C.
    hauto l:on use:cfacts.conv_trans.
  - move => Γ ℓ ℓp ℓ0 a b ℓT A B C i j ? hA _ hB _ ha _ hb _ hC _.
    move => ? ? ? ? [*]. subst.
    split => //.
    exists i, j, ℓT, A , B,C.
    have /Wt_regularity Cwf : Γ ⊢ tLet ℓ0 ℓp a b ; ℓ ∈ C[a..] by eauto using T_Let.
    repeat split => //.
    sfirstorder use:typing_conv.
Qed.

(* ------------------------------------------------- *)
(* Simpler forms of typing rules *)
Lemma T_Eq_simpl Γ ℓ0 a b A i :
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b ; ℓ0 ∈ A ->
  exists ℓ1, Γ ⊢ (tEq ℓ0 a b A) ; ℓ1 ∈ (tUniv i).
Proof.
  move => ha /[dup] hb /Wt_regularity.
  move => [ℓ1][i0]hA.
  exists (ℓ0 ∪ ℓ1).
  hauto q:on use:subsumption, T_Eq solve+:(solve_lattice).
Qed.

(* Weaker than what it could have been but enough for what we need *)
Lemma T_Var_inv Γ ℓ i A (h : Γ ⊢ var_tm i ; ℓ ∈ A) :
  exists ℓ0 B, lookup i Γ ℓ0 B /\ ℓ0 ⊆ ℓ.
Proof.
  move E : (var_tm i) h => t h.
  move : i E.
  elim : Γ ℓ t A / h=>//=.
  hauto lq:on.
Qed.

Lemma lookup_deter Γ ℓ ℓ0 i A A0  : lookup i Γ ℓ A -> lookup i Γ ℓ0 A0 -> ℓ = ℓ0 /\ A = A0.
Proof.
  move => h. move : ℓ0 A0.
  elim : i Γ ℓ A / h; hauto lq:on rew:off inv:lookup ctrs:lookup.
Qed.

Lemma T_J_simpl Γ t a b p A i C ℓ ℓp ℓ0 ℓ1:
  ℓp ⊆ ℓ ->
  Γ ⊢ a ; ℓ1 ∈ A ->
  Γ ⊢ b ; ℓ1 ∈ A ->
  Γ ⊢ p ; ℓp ∈ (tEq ℓ0 a b A) ->
  ((ℓp, tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A)) :: (ℓ1, A) :: Γ) ⊢ C ; ℓ0 ∈ (tUniv i) ->
  Γ ⊢ t ; ℓ ∈ (C [tRefl .: a ..]) ->
  Γ ⊢ (tJ t p) ; ℓ ∈ (C [p .: b..]).
Proof.
  move=> ? ? /[dup] /Wt_regularity.
  move => [ℓ2][i0]hA hb hp hC ht.
  suff : ℓ1 ⊆ ℓ0 by sfirstorder use:T_J.
  move /Wt_Wff : hC; clear => hC.
  have {}hC : exists ℓ i, (ℓ1, A)::Γ ⊢ tEq ℓ0 a ⟨S⟩ (var_tm 0) A ⟨S⟩ ; ℓ ∈ tUniv i by hauto lq:on inv:Wff.
  move : hC => [ℓ][i].
  move /Wt_Eq_inv => [?][?][h]*.
  move : h; clear.
  hauto q:on inv:lookup ctrs:lookup use:T_Var_inv, lookup_deter.
Qed.

Lemma T_Abs_simple Γ ℓ ℓ0 A a B :
  (ℓ0, A) :: Γ ⊢ a ; ℓ ∈ B ->
  (* -------------------- *)
  Γ ⊢ tAbs ℓ0 a ; ℓ ∈ tPi ℓ0 A B.
Proof.
  move => h.
  have hΓ : ⊢ (ℓ0, A) :: Γ by sfirstorder use:Wt_Wff.
  have hΓ' : ⊢ Γ by inversion hΓ.
  have [ℓA [i hA]] : exists ℓ i, Γ ⊢ A ; ℓ ∈ tUniv i by hauto lq:on inv:Wff.
  have [ℓB [j hB]] : exists ℓ j, (ℓ0, A)::Γ ⊢ B ; ℓ ∈ tUniv j by sfirstorder use:Wt_regularity.
  apply T_Abs with (ℓ1 := ℓA ∪ ℓB) (i := max i j)=>//.
  hauto lq:on use:subsumption, T_Pi solve+:(by solve_lattice).
Qed.

Lemma Wt_J_inv Γ ℓ t p U (h : Γ ⊢ (tJ t p) ; ℓ ∈ U) :
  exists ℓp ℓT ℓ0 ℓ1 a b A i C,
    ℓ1 ⊆ ℓ0 /\
    ℓp ⊆ ℓ /\
    Γ ⊢ p ; ℓp ∈ (tEq ℓ0 a b A) /\
    Γ ⊢ a ; ℓ1 ∈ A /\
    Γ ⊢ b ; ℓ1 ∈A /\
    (exists j, Γ ⊢ A ; ℓT ∈ (tUniv j)) /\
    ((ℓp , tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A)) :: (ℓ1, A) :: Γ) ⊢ C ; ℓ0 ∈ (tUniv i) /\
    Γ ⊢ t ; ℓ ∈ C[tRefl .: a..] /\
    conv (c2e Γ) C[p .: b..]  U /\
    exists ℓ j, Γ ⊢ U ; ℓ ∈ (tUniv j).
Proof.
  move E : (tJ t p) h => T h.
  move : t p E.
  elim :  Γ ℓ T U / h => //.
  - move => Γ ℓ ℓB a A B i ha iha hB _ hAB.
    move => t p ?. subst.
    specialize iha with (1 := eq_refl).
    move  : iha => [ℓp][ℓT][ℓ0][ℓ1]?.
    exists ℓp, ℓT, ℓ0, ℓ1. hauto lq:on rew:off use:cfacts.conv_trans.
  - move => Γ t a b p A i j C ℓ ℓp ℓT ℓ0 ℓ1 ? ? ha _ hb _ hA _ hp _ hC _ ht _ ? ?  [] *; subst.
    have /Wt_regularity ? : Γ ⊢ tJ t p ; ℓ ∈ C[p.:b..] by eauto using T_J.
    exists ℓp, ℓT, ℓ0, ℓ1, a, b, A, i, C. repeat split => //.
    sfirstorder.
    sfirstorder use:typing_conv.
Qed.

Lemma preservation_helper ℓ ℓ0 ℓ1 A0 A1 i Γ a A :
  ((ℓ0, A0) :: Γ) ⊢ a ; ℓ ∈ A ->
  Γ ⊢ A1 ; ℓ1 ∈ (tUniv i) ->
  conv (c2e Γ) A1 A0 ->
  ((ℓ0, A1) :: Γ) ⊢ a ; ℓ ∈ A.
Proof.
  move => h0 h1 h2.
  have [j [ℓ2 h3]] : exists j ℓ2, Γ ⊢ A0 ; ℓ2 ∈ tUniv j by
    move /Wt_Wff in h0; hauto lq:on inv:Wff.
  have -> : a = subst_tm ids a by asimpl.
  have -> : A = subst_tm ids A by asimpl.
  apply morphing_Syn with (Γ := (ℓ0, A0) :: Γ).
  - done.
  - move => k ℓ3 h. elim/lookup_inv => _.
    + move => ℓ4 A2 Γ0 ? [] *. subst. asimpl.
      eapply T_Conv with (A := ren_tm shift A1) (i := j).
      * apply : T_Var; hauto l:on use:meet_idempotent db:wff.
      * change (tUniv j) with (ren_tm shift (tUniv j)).
        eapply weakening_Syn with (i := i) => //; eauto.
      * simpl.
        apply cfacts.conv_renaming with (Ξ := c2e Γ)=>//.
    + move => n A2 Γ0 ℓ4 B ? ? [] *. subst. asimpl.
      change (var_tm (S n)) with (ren_tm shift (var_tm n)).
      eapply weakening_Syn with (i := i) => //; eauto.
      apply : T_Var; hauto use:meet_idempotent lq:on db:wff.
  - eauto with wff.
Qed.

Lemma preservation_helper2 ℓ ℓ0 ℓ1 ℓA1 ℓB1 A0 A1  B0 B1 j l Γ a A :
  ((ℓ0, B0) :: (ℓ1, A0) :: Γ) ⊢ a ; ℓ ∈ A ->
  Γ ⊢ A1 ; ℓA1  ∈ tUniv j ->
  (ℓ1, A1) :: Γ ⊢ B1 ; ℓB1 ∈ tUniv l ->
  conv (c2e Γ) A1 A0 -> conv (ℓ1 :: c2e Γ) B1 B0 ->
  ((ℓ0, B1) :: (ℓ1, A1) :: Γ ⊢ a ; ℓ ∈ A).
Proof.
  move => ha hA1 hB1 hSubA hSubB.
  have [i [ℓA0 hA0]] : exists i ℓ, Γ ⊢ A0 ; ℓ ∈ tUniv i by
    move /Wt_Wff in ha; hauto lq:on inv:Wff.
  have [k [ℓB0 hB0]] : exists i ℓ, (ℓ1, A0)::Γ ⊢ B0 ; ℓ ∈ tUniv i by
    move /Wt_Wff in ha; hauto lq:on inv:Wff.
  have -> : a = (a[ids]) by asimpl.
  have -> : A = (A[ids]) by asimpl.
  apply morphing_Syn with (Γ := (ℓ0, B0) :: (ℓ1, A0) :: Γ);
    auto; last by eauto with wff.

  move => m ℓ2 C. elim /lookup_inv.
  - move => lookm ℓ3 B0' Γ' ? [*]. subst.
    apply T_Conv with (A := B1 ⟨S⟩) (i := k) (ℓ0 := ℓB0).
    + apply : T_Var; hauto lq:on use:meet_idempotent ctrs:lookup db:wff.
    + asimpl.
      eapply weakening_Syn' with (A := tUniv k); eauto.
      eapply preservation_helper; eauto.
    + asimpl => /=.
      eapply cfacts.conv_renaming; eauto.
      rewrite /iok_ren_ok.
      sfirstorder inv:nat.
  - move => lookm n C' Γ' ℓ3 B' lookn ? [*]. subst.  asimpl.
    elim /lookup_inv : lookn.
    + move => lookn A0' Γ'' ? E' [*]. subst.
      apply T_Conv with (A := A1 ⟨S⟩ ⟨S⟩) (i := i) (ℓ0 := ℓA0).
      * apply : T_Var; hauto lq:on use:meet_idempotent ctrs:lookup db:wff.
      * repeat eapply weakening_Syn' with (A := tUniv i); eauto.
      * apply cfacts.conv_renaming with (Ξ := ℓ2 :: c2e Γ); eauto.
        apply cfacts.conv_renaming with (Ξ := c2e Γ); eauto.
        rewrite /iok_ren_ok.
        sfirstorder inv:nat.
        sfirstorder inv:nat unfold:elookup.
    + move => *. apply : T_Var; hauto lq:on use:meet_idempotent ctrs:lookup db:wff.
Qed.

Lemma T_Refl' Γ ℓ ℓ0 a0 a1 A
  (hΓ : ⊢ Γ)
  (h : a0 ⇒ a1) :
  Γ ⊢ a0 ; ℓ0 ∈ A ->
  Γ ⊢ a1 ; ℓ0 ∈ A ->
  Γ ⊢ tRefl ; ℓ ∈ (tEq ℓ0 a0 a1 A).
Proof.
  move => ha0 ha1.
  Check T_Eq_simpl.
  move : T_Eq_simpl (ha0) (ha1) => /[apply]/[apply] /(_ 0). move => [ℓ1 ?].
  eapply T_Conv with (A := tEq ℓ0 a0 a0 A) (i := 0).
  - by apply T_Refl.
  - eauto.
  - rewrite /conv.
    exists ℓ1. rewrite/iconv.
    exists (tEq ℓ0 a0 a1 A),(tEq ℓ0 a0 a1 A).
    repeat split; eauto using rtc_refl, rtc_once, cfacts.pfacts.Par_refl with par.
    apply iok_ieq with (ℓ := ℓ1); last by solve_lattice.
    eauto using typing_iok.
Qed.

Lemma Wt_Refl_inv Γ ℓ T (h : Γ ⊢ tRefl ; ℓ ∈ T) :
  exists ℓ0 a A, Γ ⊢ tRefl ; ℓ ∈ (tEq ℓ0 a a A)  /\
         Γ ⊢ a ; ℓ0 ∈ A /\
         conv (c2e Γ) (tEq ℓ0 a a A) T /\ exists ℓ i, Γ ⊢ T ; ℓ ∈ (tUniv i).
Proof.
  move E : tRefl h => p h.
  move : E.
  elim : Γ ℓ p T / h=>//.
  - hauto lq:on rew:off use:cfacts.conv_trans.
  - move => Γ ℓ a ℓ0 A hΓ ha _ _.
    have : exists ℓ, Γ ⊢ tEq ℓ0 a a A ; ℓ ∈ tUniv 0 by eauto using T_Eq_simpl.
    move => [ℓ1 ?].
    exists ℓ0, a , A.
    sfirstorder use:T_Refl, typing_conv.
Qed.

(* Lemma Wt_Suc_inv Γ a T (h : Γ ⊢ tSuc a ∈ T) : *)
(*   Γ ⊢ a ∈ tNat /\ *)
(*   tNat <: T /\ exists i, Γ ⊢ T ∈ tUniv i. *)
(* Proof. *)
(*   move E : (tSuc a) h => a0 h. *)
(*   move : a E. *)
(*   elim : Γ a0 T / h=>//. *)
(*   - hauto lq:on rew:off use:Sub_transitive. *)
(*   - hauto lq:on ctrs:Wt use:T_Nat, Sub_reflexive. *)
(* Qed. *)

Lemma Wt_Refl_Coherent Γ ℓ ℓ0 a b A (h : Γ ⊢ tRefl ; ℓ ∈ (tEq ℓ0 a b A)) :
  iconv (c2e Γ) ℓ0 a b.
Proof.
  move /Wt_Refl_inv : h.
  move => [ℓ1][a0][A0][h0][h1][h2][ℓ2][i]h3.
  move /cfacts.conv_eq_inj : h2.
  move => [?][ℓ3][?][ha][hb]hA. subst.
  move /typing_iok in h1.
  have : iconv (c2e Γ) (ℓ0 ∩ ℓ3) a0 a
    by eauto using meet_commutative, cfacts.iconv_iok_downgrade.
  have : iconv (c2e Γ) (ℓ0 ∩ ℓ3) a0 b
    by eauto using meet_commutative, cfacts.iconv_iok_downgrade.
  qauto l:on use:cfacts.iconv_sym, cfacts.iconv_trans.
Qed.

Lemma Wt_Absurd_inv Γ ℓ a A (h : Γ ⊢ tAbsurd a ; ℓ ∈ A) :
  exists ℓ0 ℓ1 B i, Γ ⊢ a ; ℓ0 ∈ tVoid /\ Γ ⊢ B ; ℓ1 ∈ tUniv i /\
  conv (c2e Γ) B A /\ exists ℓ i, Γ ⊢ A ; ℓ ∈ tUniv i.
Proof.
  move E : (tAbsurd a) h => t h.
  move : a E.
  elim : Γ ℓ t A / h=>//.
  - hauto lq:on use:cfacts.conv_trans.
  - hauto lq:on use:typing_conv.
Qed.

Lemma T_Par Γ ℓ ℓ0 a A B i :
  Γ ⊢ a ; ℓ ∈ A ->
  Γ ⊢ B ; ℓ0 ∈ (tUniv i) ->
  A ⇒ B ->
  (* ----------- *)
  Γ ⊢ a ; ℓ ∈ B.
Proof.
  move => h0 h1 h2.
  suff : iconv (c2e Γ) ℓ0 A B by hauto q:on use:T_Conv unfold:conv.
  rewrite /iconv.
  exists B, B.
  repeat split.
  by move : h2; apply rtc_once.
  by apply rtc_refl.
  apply : iok_ieq;
    [ eauto using typing_iok
    | solve_lattice].
Qed.

Lemma subject_reduction a b (h : a ⇒ b) : forall Γ ℓ A,
    Γ ⊢ a ; ℓ ∈ A -> Γ ⊢ b ; ℓ ∈ A.
Proof.
  elim : a b /h => //.
  (* Pi *)
  - move => ℓ0 A0 A1 B0 B1 h0 ih0 h1 ih1 Γ ℓ A /Wt_Pi_inv.
    intros (i & j & hA0 & hAB0 & hACoherent & ℓ1 & k & hA).
    have ? : ⊢ Γ by eauto with wff.
    eapply T_Conv with  (A := tUniv (max i j))  => //.
    apply T_Pi => //; eauto.
    apply : preservation_helper; eauto.
    move /typing_conv : hA0.
    rewrite /conv.
    hauto lq:on use:cfacts.iconv_par.
    by eauto.
  (* Abs *)
  - move => ℓ0 a0 a1 h0 ih0 Γ ℓ A /Wt_Abs_inv.
    intros (ℓ1 & A1 & B & i & hPi & ha0 & hCoherent & ℓ2 & j & hA).
    case /Wt_Pi_Univ_inv : hPi => k [l [? [hA0 hB]]]. subst.
    apply T_Conv with (A := tPi ℓ0 A1 B) (i := j) (ℓ0 := ℓ2) => //.
    apply T_Abs_simple => //.
    apply : preservation_helper; eauto.
    sfirstorder use:typing_conv.
  - move => a0 a1 ℓ0 b0 b1 h0 ih0 h1 ih1 Γ ℓ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hCoherent & ℓ1 & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : cfacts.conv_trans; eauto.
    have : B[b0..] ⇒ B[b1..].
    apply cfacts.pfacts.Par_morphing; last by apply cfacts.pfacts.Par_refl.
    hauto q:on unfold:cfacts.pfacts.Par_m ctrs:Par inv:nat simp:asimpl.
    have : exists ℓ i, Γ ⊢ B[b0..] ; ℓ ∈ tUniv i by qauto l:on use:T_App, Wt_regularity.
    hauto lq:on use:cfacts.iconv_par, typing_conv.
  (* AppAbs *)
  - move => a a0 b0 b1 ℓ0 haa0 iha hbb0 ihb Γ ℓ A0 /Wt_App_inv.
    intros (A1 & B & ha & hb0 & hCoherent & ℓ1 & i & hA0).
    have /Wt_Abs_inv := ha; intros (ℓ2 & A & B0 & k & hPi & ha0 & hCoherent' & ℓ3 & j & hPi').
    case /cfacts.conv_pi_inj : hCoherent' => ? [hh hh']. subst.
    case /Wt_Pi_Univ_inv : hPi => [p [p0 [? [? ?]]]]. subst.
    move /Wt_regularity : ha => [ℓ4 [i0 /Wt_Pi_Univ_inv]] [iA [iB [? [hA1 hB]]]]. subst.
    have hbok : IOk (c2e Γ) ℓ0 b0 by eauto using typing_iok.
    move /ihb in hb0.
    eapply T_Conv with (A := subst_tm (b1..) B0); eauto.
    + apply : subst_Syn; eauto.
      qauto l:on use:T_Conv, cfacts.conv_sym.
    + apply : cfacts.conv_trans; eauto.
      move : hh'.
      move /cfacts.conv_subst.
      move /(_ (c2e Γ) (b0..)) => ?.
      have ? : B0[b0..] ⇒ B0[b1..] by sfirstorder use:pfacts.Par_cong, pfacts.Par_refl.
      have : iok_subst_ok b0.. (ℓ0 :: c2e Γ) (c2e Γ); last by
        hauto lq:on use:cfacts.iconv_par.
      rewrite /iok_subst_ok.
      case. rewrite/elookup//=. scongruence.
      move => n ℓ5 ?.
      have : elookup n (c2e Γ) ℓ5 by sfirstorder.
      move /IO_Var. apply. solve_lattice.
  (* Suc *)
  (* - move => a b h ih Γ ℓ A /Wt_Suc_inv. *)
  (*   move => [h0][h1][i]h2. *)
  (*   apply : T_Conv; eauto. *)
  (*   have : ⊢ Γ by eauto with wff. *)
  (*   have : Γ ⊢ b ∈ tNat by auto. *)
  (*   apply T_Suc. *)
  (* - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc Γ A /Wt_Ind_inv. *)
  (*   move => [A0][ha0][hb0][hc0][hC][[i hA0]][j hAj]. *)
  (*   apply : T_Conv. apply T_Ind with (i := i); eauto. eauto. *)
  (*   apply : Sub_transitive; eauto. *)
  (*   have : A0[c0..] ⇒ A0[c1..]; last by hauto l:on use:Par_Sub. *)
  (*   sfirstorder use:Par_cong, Par_refl. *)
  (* - qauto l:on use:Wt_Ind_inv ctrs:Wt. *)
  (* - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc Γ A /Wt_Ind_inv. *)
  (*   move => [A0][ha0][hb0][hc0][hA0][[j hA0']][i hA']. *)
  (*   apply : T_Conv; eauto. *)
  (*   have : A0[(tSuc c1)..] <: A0[(tSuc c0)..]. *)
  (*   apply Par_Sub. *)
  (*   apply Par_morphing. case => //=; hauto l:on ctrs:Par. apply Par_refl. *)
  (*   move/T_Conv. apply. *)
  (*   have /morphing_Syn /(_ Γ (tInd a1 b1 c1 .: c1..))  := ihb _ _ hb0. *)
  (*   asimpl. apply; eauto with wff. *)
  (*   rewrite /lookup_good_morphing. *)
  (*   have ? : Γ ⊢ c0 ∈ tNat by hauto l:on use:Wt_Suc_inv. *)
  (*   move => i0 A1. elim/lookup_inv => _. *)
  (*   + move => A2 Γ0 ? []*. subst. *)
  (*     asimpl. *)
  (*     apply : T_Ind; eauto. *)
  (*   + move => n A2 Γ0 B + ? [*]. subst. *)
  (*     elim/lookup_inv => _. *)
  (*     move => A1 Γ0 ? [*]. subst. by asimpl; auto. *)
  (*     move => n0 A1 Γ0 B ? ? [*]. subst. *)
  (*     asimpl.  hauto lq:on ctrs:Wt db:wff. *)
  (*   + eauto using subst_Syn_Univ. *)
  - hauto q:on use:T_Absurd, T_Conv, Wt_Absurd_inv.
  - move => ℓ0 a0 b0 A0 a1 b1 A1 ha0 iha0 ha1 iha1 hA0 ihA0 Γ ℓ A /Wt_Eq_inv.
    intros (? & ha0' & hb0' & (q & hA0') & (i & eq) & (ℓ1 & j & hA)).
    eapply T_Conv with (A := (tUniv i)) (i := j); eauto.
    hauto q:on use:T_Par, T_Eq.
  - move => t0 p0 t1 p1 ht iht hp ihp Γ ℓ U /Wt_J_inv.
    intros (ℓp & ℓT & ℓ0 & ℓ1 & a & b & A & i & C & ? & ? & hp0 & ha0 & hb0 & (k & hA) & hC0 & ht0 & heq & (ℓ2 & j & hU)).
    have ? : ⊢ Γ by eauto with wff.
    have ? : C[p0.:b..] ⇒C[p1.:b..] by
      sfirstorder use:cfacts.pfacts.Par_cong2, cfacts.pfacts.Par_refl.
    have : conv (c2e Γ) C[p1.:b..] U by qauto l:on use:cfacts.iconv_par.
    apply : T_Conv; eauto.
    eapply T_J_simpl with (a := a) (A := A) (ℓ0 := ℓ0) (ℓp := ℓp) (ℓ1 := ℓ1); eauto.
  (* JRefl *)
  - move => t0 t1 ht iht Γ ℓ U /Wt_J_inv.
    intros (ℓp & ℓT & ℓ0 & ℓ1 & a & b & A & i & C & ? & ? & hp0 & ha0 & hb0 & (j & hA) & hC & ht0 & heq & (ℓ2 & k & hU')).
    apply iht.
    move : T_Conv ht0. move/[apply]. apply; eauto.
    apply : cfacts.conv_trans;eauto.
    exists ℓ0.
    move /typing_iok : hC =>/=.
    move /Wt_Refl_Coherent : hp0.
    rewrite /iconv.
    move => [a'][b'][h0][h1]h2.
    move => hC.
    exists C[tRefl .: a'..], C[tRefl .: b'..].
    repeat split => //.
    + apply : cfacts.pfacts.Pars_morphing_star; eauto using rtc_refl.
      apply : cfacts.pfacts.good_Pars_morphing_ext2; eauto using rtc_refl.
    + apply : cfacts.pfacts.Pars_morphing_star; eauto using rtc_refl.
      apply : cfacts.pfacts.good_Pars_morphing_ext2; eauto using rtc_refl.
    + move /iok_ieq /(_ ℓ0 ltac:(by rewrite meet_idempotent)) in hC.
      eapply ieq_morphing_mutual; eauto.
      rewrite /ieq_good_morphing.
      case.
      * hauto lq:on ctrs:IEq, GIEq use:ieq_gieq unfold:elookup.
      * move => n ℓ3 h.
        have {}h: elookup n (ℓ1 :: c2e Γ) ℓ3 by sfirstorder unfold:elookup. simpl.
        case: n h; first by hauto q:on ctrs:IEq, GIEq use:ieq_gieq unfold:elookup.
        move => n h.
        have {}h: elookup n (c2e Γ) ℓ3 by sfirstorder unfold:elookup.
        asimpl.
        apply ieq_gieq. eauto with ieq.
  (* Sig *)
  - move => ℓ0 A0 A1 B0 B1 h0 ih0 h1 ih1 Γ ℓ A /Wt_Sig_inv.
    intros (i & j & hA0 & hAB0 & hACoherent & ℓ1 & k & hA).
    have ? : ⊢ Γ by eauto with wff.
    eapply T_Conv with  (A := tUniv (max i j))  => //.
    apply T_Sig => //; eauto.
    apply : preservation_helper; eauto.
    move /typing_conv : hA0.
    rewrite /conv.
    hauto lq:on use:cfacts.iconv_par.
    by eauto.
  (* Pack *)
  - move => ℓ0 a0 a1 b0 b1 h0 ih0 h1 ih1 Γ ℓ A /Wt_Pack_inv.
    intros (ℓT & A0 & B0 & i & ha & hb & hSig & hCoherent & (ℓ1 & j & hA)).
    apply T_Conv with (A := tSig ℓ0 A0 B0) (i := j) (ℓ0 := ℓ1) => //.
    eapply T_Pack; eauto.
    apply ih1.
    have ? : B0[a0..] ⇒ B0[a1..] by hauto lq:on use:Par_cong, Par_refl.
    move /Wt_Sig_Univ_inv : hSig.
    move => [i0][j0][?][h2]h3. subst.
    eapply T_Par with (ℓ0 := ℓT) (i := j0); eauto.
    eapply subst_Syn_Univ; eauto.
  (* Let *)
  - move => ℓ0 ℓ1 a0 b0 a1 b1 h0 ih0 h1 ih1 Γ ℓ A /Wt_Let_inv.
    intros (? & i & j & ℓT& A0 & B0 & C & hA0 & hB0 & ha & hb & hC & hCoherent & ℓ2 & k & hA).
    apply T_Conv with (A := C[a1..]) (i := k) (ℓ0 := ℓ2)  => //.
    + eapply T_Let' with (j := j); eauto.
    + apply : cfacts.conv_trans; eauto.
      have : conv (c2e Γ) C[a0..] C[a0..] by eauto using cfacts.conv_trans, cfacts.conv_sym.
      have : C[a0..] ⇒ C[a1..] by sfirstorder use:Par_cong, Par_refl.
      rewrite /conv.
      hauto l:on use:cfacts.iconv_par.
  (* LetPack *)
  - move => ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 h0 ih0 h1 ih1 h2 ih2 Γ ℓ A /Wt_Let_inv.
    intros (? & i & j & ℓT  & A0 & B0 & C & hA0 & hB0 & hPack & hc0 & hC & hCoherent & ℓ2 & k & hA).
    move /Wt_Pack_inv : hPack.
    intros (ℓT0 & A1 & B1 & l & ha0 & hb0 & hSig & hSub & _).
    move /Wt_Sig_Univ_inv : hSig => [m][n][?][hA1] hB1. subst.
    move /cfacts.conv_sig_inj : hSub => [? [hSubA hSubB]].
    apply ih0 in ha0.
    apply ih1 in hb0.
    apply ih2 in hc0.
    have hb1 : Γ ⊢ b1 ; ℓ1 ∈ B1[a1..]. {
      eapply T_Conv with (A := B1[a0..]) (i := n); eauto.
      + change (tUniv n) with (tUniv n)[a1..].
        eapply subst_Syn with (a := a1); eauto.
      + move /Wt_regularity : hb0.
        move => [ℓ3][i0].
        move /typing_conv.
        have : B1[a0..] ⇒ B1[a1..] by sfirstorder use:Par_refl, Par_cong.
        rewrite /conv.
        hauto lq:on use:cfacts.iconv_par, cfacts.iconv_sym.
    }
    eapply T_Conv with (A := C[(tPack ℓ0 a1 b1)..]); eauto.
    + have -> : C[(tPack ℓ0 a1 b1)..] = C[tPack ℓ0 (var_tm 1) (var_tm 0) .: shift >> shift >> var_tm][b1 .: a1..]
        by asimpl.
      eapply preservation_helper2 with
        (A0 := A0) (A1 := A1) (B0 := B0) (B1 := B1) in hc0; eauto.
      move : morphing_Syn hc0. move /[apply].
      apply; last by hauto lq:on db:wff.
      move => p ℓp D. elim/lookup_inv.
      * move => *. asimpl. scongruence.
      * move => _ n0 A2 Γ0 ℓ3 B h ? [*]. subst.
        asimpl.
        inversion h; subst.
        asimpl. sfirstorder.
        asimpl. apply : T_Var;eauto with wff.
        solve_lattice.
    + eapply cfacts.conv_trans; eauto.
      have : conv (c2e Γ) C[(tPack ℓ0 a0 b0)..] C[(tPack ℓ0 a0 b0)..]
        by hauto lq:on ctrs:Par use:cfacts.conv_sym, cfacts.conv_trans.
      have ? : tPack ℓ0 a0 b0 ⇒ tPack ℓ0 a1 b1 by eauto with par.
      have : C[(tPack ℓ0 a0 b0)..] ⇒ C[(tPack ℓ0 a1 b1)..] by eauto using Par_refl, Par_cong.
      hauto lq:on use:cfacts.iconv_par unfold:conv.
Qed.

Lemma subject_reduction_star a b (h : a ⇒* b) : forall Γ ℓ A,
    Γ ⊢ a ; ℓ ∈ A -> Γ ⊢ b ; ℓ ∈ A.
Proof.
  induction h; sfirstorder use:subject_reduction ctrs:rtc.
Qed.

End preservation.
