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

Lemma Wt_Wff n Γ a A (h : Wt n Γ a A) : Wff n Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.

Lemma Wt_Univ n Γ a A i
  (h : Wt n Γ a A) :
  exists j, Wt n Γ (tUniv i) (tUniv j).
Proof.
  exists (S i).
  qauto l:on use:Wt_Wff ctrs:Wt.
Qed.

Lemma Wt_Pi_inv n Γ A B U (h : Wt n Γ (tPi A B) U) :
  exists i, Wt n Γ A (tUniv i) /\
         Wt (S n) (A .: Γ) B (tUniv i) /\
         Join (tUniv i) U /\
         exists i, Wt n Γ U (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : n Γ T U / h => //.
  - hauto l:on use:Wt_Univ.
  - hauto lq:on rew:off use:Join_transitive.
Qed.

Lemma Wt_Pi_Univ_inv n Γ A B i (h : Wt n Γ (tPi A B) (tUniv i)) :
  Wt n Γ A (tUniv i) /\
  Wt (S n) (A .: Γ) B (tUniv i).
Proof. hauto lq:on use:Wt_Pi_inv, join_univ_inj. Qed.

Lemma Wt_Abs_inv n Γ A a T (h : Wt n Γ (tAbs A a) T) :
  exists B i, Wt n Γ (tPi A B) (tUniv i) /\
         Wt (S n) (A .: Γ) a B /\
         Join (tPi A B) T /\
         exists i, (Wt n Γ T (tUniv i)).
Proof.
  move E : (tAbs A a) h => a0 h.
  move : A a E.
  elim : n Γ a0 T / h => //.
  - hauto lq:on use:Join_reflexive.
  - hauto lq:on rew:off use:Join_transitive.
Qed.

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
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 n Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hAJoin & j & hA).
    have ? : Wff n Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    apply T_Pi; first by eauto.
    apply ih1.
    replace B0 with (subst_tm ids B0); last by asimpl.
    change (tUniv i) with (subst_tm ids (tUniv i)).
    apply morphing_Syn with (n := S n) (Γ := A0 .: Γ); eauto with wff.
    (* Pull out as a lemma *)
    case => [_ | k /Arith_prebase.lt_S_n ?].
    + rewrite dep_ith_ren_tm0.
      asimpl.
      apply T_Conv with (A := ren_tm shift A1) (i := i); eauto.
      * apply T_Var'; [by asimpldep | eauto with wff | lia].
      * apply :  weakening_Syn'; eauto; by asimpl.
      * sfirstorder use:Par_join, join_renaming, Join_symmetric.
    + asimpl.
      rewrite dep_ith_ren_tm.
      change (var_tm (S k)) with (ren_tm shift (var_tm k)).
      hauto lq:on ctrs:Wt use:weakening_Syn.
  - move => A0 A1 a0 a1 h0 ih0 h1 ih1 n Γ A /Wt_Abs_inv.
    intros (B & i & hPi & ha0 & hJoin & j & hA).
    case /Wt_Pi_Univ_inv : hPi => hA0 hB.
    apply T_Conv with (A := tPi A1 B) (i := j) => //.
    apply T_Abs with (i := i).
    + apply T_Pi; eauto.
      (* reuse the factored out lemma *)
      admit.
    + apply ih1.
      (* reuse the factored out lemma *)
      admit.
    + suff : Join (tPi A1 B) (tPi A0 B) by hauto l:on use:Join_transitive.
      apply Join_symmetric.
      apply Par_join.
      hauto lq:on ctrs:Par use:Par_refl.
  - admit.
  -
Admitted.
