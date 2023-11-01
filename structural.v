From WR Require Import syntax join typing.
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

Lemma subst_Syn n Γ A a b B
  (h0 : Wt (S n) (A .: Γ) b B)
  (h1 : Wt n Γ a A) :
  Wt n Γ (subst_tm (a..) b) (subst_tm (a..) B).
Proof.
  apply : morphing_Syn; eauto with wff.
  case => [_ | i /Arith_prebase.lt_S_n ?].
  - rewrite dep_ith_ren_tm0.
    by asimpl.
  - rewrite dep_ith_ren_tm.
    asimpl.
    eauto using T_Var with wff.
Qed.

Lemma good_renaming_truncate n m Γ :
  good_renaming (Nat.add n) m (Nat.add n >> Γ) (n + m) Γ .
Proof.
  rewrite /good_renaming.
  split.
  - lia.
  - asimpldep.
    f_equal. fext => *; asimpl; lia.
Qed.

Lemma good_renaming_truncate' n m Γ :
  n <= m ->
  good_renaming (Nat.add n) (m - n) (Nat.add n >> Γ) m Γ.
Proof.
  move => h.
  replace m with (n + (m - n)) at 2; last by lia.
  apply good_renaming_truncate.
Qed.

Lemma Wt_regularity n Γ a A
  (h : Wt n Γ a A) :
  exists i, Wt n Γ A (tUniv i).
Proof.
  elim:n Γ a A/h; try qauto ctrs:Wt depth:2.
  - inversion 1; qauto l:on use:good_renaming_truncate', renaming_Syn.
  - hauto q:on use:subst_Syn, Wt_Pi_Univ_inv.
Qed.

Lemma Wt_App_inv n Γ b a T (h : Wt n Γ (tApp b a) T) :
  exists A B, Wt n Γ b (tPi A B) /\
         Wt n Γ a A /\
         Join (subst_tm (a..) B) T /\
         exists i, Wt n Γ T (tUniv i).
Proof.
  move E : (tApp b a) h => ba h.
  move : b a E.
  elim : n Γ ba T /h => //.
  - move => n Γ a A B b h0 _ h1 _ ? ? [] *; subst.
    exists A, B; repeat split => //.
    + apply join_subst_star. apply Join_reflexive.
    + move /Wt_regularity : h0.
      move => [i /Wt_Pi_Univ_inv] [hA hB].
      exists i.
      change (tUniv i) with (subst_tm (b..) (tUniv i)).
      apply : subst_Syn; eauto.
  - hauto lq:on rew:off use:Join_transitive.
Qed.


Lemma Wt_If_inv n Γ a b c T (h : Wt n Γ (tIf a b c) T) :
  exists A, Wt n Γ a tSwitch /\
         Wt n Γ b A /\
         Wt n Γ c A /\
         Join A T /\
         exists i, Wt n Γ T (tUniv i).
Proof.
  move E : (tIf a b c) h => a0 h.
  move : a b c E.
  elim : n Γ a0 T / h => //.
  - hauto lq:on rew:off use:Join_transitive.
  - qauto l:on use:Join_reflexive, Wt_regularity.
Qed.

Lemma preservation_helper n A0 A1 i j Γ a A :
  Wt (S n) (A0, Γ) a A ->
  Wt n Γ A0 (tUniv i) ->
  Wt n Γ A1 (tUniv j) ->
  Join A0 A1 ->
  Wt (S n) (A1, Γ) a A.
Proof.
  move => h0 h1 h2 h3.
  replace a with (subst_tm ids a); last by asimpl.
  replace A with (subst_tm ids A); last by asimpl.
  apply morphing_Syn with (n := S n) (Γ := A0 .: Γ).
  - done.
  - case => [_ | k /Arith_prebase.lt_S_n ?].
    + rewrite dep_ith_ren_tm0; asimpl.
      apply T_Conv with (A := ren_tm shift A1) (i := i).
      * apply T_Var; hauto l:on db:wff.
      * change (tUniv i) with (ren_tm shift (tUniv i)).
        apply weakening_Syn with (i := j) => //.
      * hauto lq:on use:Join_symmetric, join_renaming.
    + rewrite dep_ith_ren_tm.
      asimpl.
      change (var_tm (S k)) with (ren_tm shift (var_tm k)).
      apply weakening_Syn with (i := j) => //.
      apply T_Var; hauto lq:on db:wff.
  - eauto with wff.
Qed.

Lemma subject_reduction a b (h : Par a b) : forall n Γ A,
    Wt n Γ a A -> Wt n Γ b A.
Proof.
  elim : a b /h => //.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 n Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hAJoin & j & hA).
    have ? : Wff n Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    qauto l:on ctrs:Wt use:preservation_helper, Par_join.
  - move => A0 A1 a0 a1 h0 ih0 h1 ih1 n Γ A /Wt_Abs_inv.
    intros (B & i & hPi & ha0 & hJoin & j & hA).
    case /Wt_Pi_Univ_inv : hPi => hA0 hB.
    apply T_Conv with (A := tPi A1 B) (i := j) => //.
    apply T_Abs with (i := i).
    + qauto l:on ctrs:Wt use:preservation_helper, Par_join.
    + qauto l:on ctrs:Wt use:preservation_helper, Par_join.
    + suff : Join (tPi A1 B) (tPi A0 B) by hauto l:on use:Join_transitive.
      apply Join_symmetric.
      apply Par_join.
      hauto lq:on ctrs:Par use:Par_refl.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 n Γ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hJoin & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : Join_transitive; eauto.
    apply Join_symmetric.
    apply Par_join.
    apply par_morphing; last by apply Par_refl.
    hauto q:on ctrs:Par inv:nat simp:asimpl.
  - move => a A a0 b0 b1 haa0 iha hbb0 ihb n Γ A0 /Wt_App_inv.
    intros (A1 & B & ha & hb0 & hJoin & i & hA0).
    have /iha /Wt_Abs_inv := ha; intros (B0 & k & hPi & ha0 & hJoin' & j & hPi').
    case /join_pi_inj : hJoin' => *.
    case /Wt_Pi_Univ_inv : hPi => *.
    move /Wt_regularity : ha => [i0 /Wt_Pi_Univ_inv] [hA1 hB].
    move /ihb in hb0.
    eapply T_Conv with (A := subst_tm (b1..) B0); eauto.
    + apply : subst_Syn; eauto.
      eapply T_Conv with (A := A1); eauto.
      qauto l:on use:Join_symmetric.
    + apply : Join_transitive; eauto.
      apply Join_symmetric.
      apply join_morphing.
      * by apply Join_symmetric.
      * case; [by asimpl | sfirstorder use:Par_refl].
  - hauto lq:on use:Wt_If_inv ctrs:Wt.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
  - qauto l:on use:Wt_If_inv ctrs:Wt.
Qed.
