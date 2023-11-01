From WR Require Import syntax join typing inversion.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.
Require Import Psatz.

Definition good_renaming ξ n Γ m Δ :=
  (forall i, i < n -> ξ i < m /\ ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i)).

Lemma good_renaming_up ξ n Γ m Δ A :
  good_renaming ξ n Γ m Δ ->
  good_renaming (upRen_tm_tm ξ) (S n) (A .: Γ) (S m) (ren_tm ξ A .: Δ).
Proof.
  move => h.
  rewrite /good_renaming.
  case => [_ | i ?].
  - split; [sfirstorder | by asimpldep].
  - split.
    + asimpl; suff : ξ i < m; sfirstorder.
    + repeat rewrite dep_ith_ren_tm.
      rewrite /good_renaming in h.
      case /(_ i ltac:(sfirstorder)) : h => h h'.
      rewrite -h'; by asimpl.
Qed.

Lemma T_App' n Γ a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Wt n Γ a (tPi A B) ->
  Wt n Γ b A ->
  (* -------------------- *)
  Wt n Γ (tApp a b) B0.
Proof. qauto ctrs:Wt. Qed.

Lemma wff_nil Γ :
  Wff 0 Γ.
Proof. apply Wff_intro with (F := fun x => x); lia. Qed.

Lemma wff_cons m Γ A i
  (h0 : Wt m Γ A (tUniv i))
  (h1 : Wff m Γ) :
  Wff (S m) (A .: Γ).
Proof.
  inversion h1 as [F h].
  apply Wff_intro with (F := i .: F).
  case => [_ | p /Arith_prebase.lt_S_n hp ].
  + replace (S m - 1) with m; last by lia.
    by asimpl.
  + sfirstorder ctrs:Wff.
Qed.

#[export]Hint Resolve wff_nil wff_cons : wff.

Lemma renaming_Syn n Γ a A (h : Wt n Γ a A) : forall m Δ ξ,
    good_renaming ξ n Γ m Δ ->
    Wff m Δ ->
    Wt m Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  elim : Γ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:good_renaming.
  - hauto lq:on ctrs:Wt use:good_renaming_up db:wff.
  - hauto lq:on ctrs:Wt use:good_renaming_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:join_renaming.
Qed.

Lemma Wt_Wff n Γ a A (h : Wt n Γ a A) : Wff n Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.

Lemma weakening_Syn n Γ a A B i
  (h0 : Wt n Γ B (tUniv i))
  (h1 : Wt n Γ a A) :
  Wt (S n) (B .: Γ) (ren_tm shift a) (ren_tm shift A).
Proof.
  apply renaming_Syn with (n := n) (Γ := Γ); eauto.
  - split; [ rewrite /shift; lia | by rewrite dep_ith_ren_tm].
  - hauto lq:on db:wff.
Qed.

Lemma weakening_Syn' n Γ a A A0 B i
  (he : A0 = ren_tm shift A)
  (h0 : Wt n Γ B (tUniv i))
  (h1 : Wt n Γ a A) :
  Wt (S n) (B .: Γ) (ren_tm shift a) A0.
Proof. sfirstorder use:weakening_Syn. Qed.

Definition good_morphing ρ n Γ m Δ :=
  forall i, i < n -> Wt m Δ (ρ i) (subst_tm ρ (dep_ith Γ i)).

Lemma T_Var' n Γ i A :
  A = dep_ith Γ i ->
  Wff n Γ ->
  i < n ->
  (* ------ *)
  Wt n Γ (var_tm i) A.
Proof. qauto ctrs:Wt. Qed.

Lemma good_morphing_up ρ n k Γ m Δ A
  (h : good_morphing ρ n Γ m Δ) :
  Wff m Δ ->
  Wt m Δ (subst_tm ρ A) (tUniv k) ->
  good_morphing (up_tm_tm ρ) (S n) (A .: Γ) (S m) (subst_tm ρ A .: Δ).
Proof.
  rewrite /good_morphing => h1 h2.
  case => [_ | i /Arith_prebase.lt_S_n ?].
  - apply T_Var'.
    + by asimpldep.
    + eauto with wff.
    + asimpl. lia.
  - rewrite dep_ith_ren_tm.
    apply : weakening_Syn'; cycle 2.
    rewrite /good_morphing in h.
    + sfirstorder unfold:good_morphing.
    + by asimpl.
    + sfirstorder.
Qed.

Lemma morphing_Syn n Γ a A (h : Wt n Γ a A) : forall m Δ ρ,
    good_morphing ρ n Γ m Δ ->
    Wff m Δ ->
    Wt m Δ (subst_tm ρ a) (subst_tm ρ A).
Proof.
  elim : n Γ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:good_morphing.
  - move => *.
    apply T_Pi; eauto.
    hauto q:on use:good_morphing_up db:wff.
  - move => *.
    apply : T_Abs; eauto.
    hauto q:on use:good_morphing_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - hauto q:on ctrs:Wt use:join_subst_star.
Qed.

Lemma preservation a b (h : Par a b) : forall n Γ A,
    Wt n Γ a A -> Wt n Γ b A.
Proof.
  elim : a b /h => //.
Admitted.
