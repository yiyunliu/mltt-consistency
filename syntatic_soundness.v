From WR Require Import typing.
From Coq Require Import ssreflect Sets.Relations_2 ssrbool Relations.Relation_Operators.
From Hammer Require Import Tactics Hammer.

Module syntactic_soundness
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade)
  (Import common : common_sig grade syntax)
  (Import join : join_sig grade syntax common)
  (Import typing : typing_sig grade syntax common join).

Lemma good_renaming_up ξ Γ Δ ℓ A :
  good_renaming ξ Γ Δ ->
  good_renaming (upRen_tm_tm ξ) ((ℓ, A) :: Γ) ((ℓ, ren_tm ξ A) :: Δ).
Proof.
  move => h.
  rewrite /good_renaming.
  case => /= [ ?| i /Arith_prebase.lt_S_n h0].
  - asimpl;
    sfirstorder.
  - split.
    + asimpl; sfirstorder.
    + case /h : h0 => h0 [h1 h2] /=.
      rewrite h1 h2.
      by asimpl.
Qed.

Lemma T_App' Γ ℓ a ℓ0 A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Wt Γ ℓ a (tPi ℓ0 A B) ->
  Wt Γ ℓ0 b A ->
  (* -------------------- *)
  Wt Γ ℓ (tApp a ℓ0 b) B0.
Proof. qauto ctrs:Wt. Qed.

Lemma wff_nil :
  Wff nil.
Proof.
  apply Wff_intro with (F := fun x => x) (G := fun x => el) => /= //.
  lia.
Qed.

Lemma wff_cons Γ ℓ ℓ0 A i
  (h0 : Wt Γ ℓ0 A (tUniv i))
  (h1 : Wff Γ) :
  Wff ((ℓ, A) :: Γ).
Proof.
  case : h1 => F G h.
  apply Wff_intro with (F := i .: F) (G := ℓ0 .: G).
  case => [? | p /Arith_prebase.lt_S_n ? ] /=;
         hauto lq:on ctrs:Wff use:drop0.
Qed.

#[export]Hint Resolve wff_nil wff_cons : wff.

Lemma Wt_Wff Γ ℓ a A (h : Wt Γ ℓ a A) : Wff Γ.
Proof. elim : Γ ℓ a A / h => //. Qed.

#[export]Hint Resolve Wt_Wff : wff.

Lemma Wt_Univ Γ ℓ ℓ0 a A i
  (h : Wt Γ ℓ a A) :
  exists j, Wt Γ ℓ0 (tUniv i) (tUniv j).
Proof.
  exists (S i).
  qauto l:on use:Wt_Wff ctrs:Wt.
Qed.

Definition icoherentR Ξ := clos_refl _ (icoherent Ξ).

Lemma icoherent_transitive {Ξ a b c} :
  icoherent Ξ a b -> icoherent Ξ b c -> icoherent Ξ a c.
Proof. qauto l:on inv:PER use:icoherent_PER unfold:Transitive. Qed.

Lemma icoherentR_transitive {Ξ a b c} :
  icoherentR Ξ a b -> icoherent Ξ b c -> icoherentR Ξ a c.
Proof.
  hauto ctrs:clos_refl l:on use:icoherent_transitive inv:clos_refl.
Qed.

Lemma Wt_Pi_inv Γ ℓ ℓ0 A B U (h : Wt Γ ℓ (tPi ℓ0 A B) U) :
  exists i, Wt Γ ℓ A (tUniv i) /\
         Wt ((ℓ0, A) :: Γ) ℓ B (tUniv i) /\
         icoherentR (unzip1 Γ) (tUniv i) U /\
         exists ℓ0 i, Wt Γ ℓ0 U (tUniv i).
Proof.
  move E : (tPi ℓ0 A B) h => T h.
  move : ℓ0 A B E.
  elim :  Γ ℓ T U / h => //.
  - hauto l:on use:Wt_Univ.
  - hauto l:on use:@icoherentR_transitive.
Qed.

Lemma icoherentR_univ_inj Ξ i j (h : icoherentR Ξ (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on inv:clos_refl unfold:icoherentR use:icoherent_univ_inj . Qed.

Lemma Wt_Pi_Univ_inv Γ ℓ ℓ0 A B i (h : Wt Γ ℓ (tPi ℓ0 A B) (tUniv i)) :
  Wt Γ ℓ A (tUniv i) /\
  Wt ((ℓ0, A) :: Γ) ℓ B (tUniv i).
Proof. hauto lq:on rew:off use:Wt_Pi_inv, icoherentR_univ_inj. Qed.

Lemma Wt_Abs_inv Γ ℓ ℓ0 A a T (h : Wt Γ ℓ (tAbs ℓ0 A a) T) :
  exists ℓ1 B i, Wt Γ ℓ1 (tPi ℓ0 A B) (tUniv i) /\
         Wt ((ℓ0, A) :: Γ) ℓ a B /\
         icoherentR (unzip1 Γ) (tPi ℓ0 A B) T /\
         exists ℓ2 i, (Wt Γ ℓ2 T (tUniv i)).
Proof.
  move E : (tAbs ℓ0 A a) h => a0 h.
  move : ℓ0 A a E.
  elim : Γ ℓ a0 T / h => //.
  - hauto lq:on ctrs:clos_refl.
  (* Coq hammer doesn't like implicit arguments *)
  - hauto lq: on drew: off use:@icoherentR_transitive.
Qed.

Lemma renaming_ieq_renaming ξ Γ Δ:
  good_renaming ξ Γ Δ ->
  ieq_good_renaming ξ (unzip1 Γ) (unzip1 Δ).
Proof.
  rewrite /good_renaming /ieq_good_renaming => h.
  repeat rewrite size_map.
  sfirstorder.
Qed.

Lemma renaming_Syn Γ ℓ a A (h : Wt Γ ℓ a A) : forall Δ ξ,
    good_renaming ξ Γ Δ ->
    Wff Δ ->
    Wt Δ ℓ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  elim : Γ ℓ a A / h; try qauto l:on depth:1 ctrs:Wt unfold:good_renaming.
  - move => Γ ℓ i hΓ hi hℓ Δ ξ hξ hΔ.
    move /hξ : hi.
    intros (hξi & heq & hℓ').
    rewrite -heq.
    apply T_Var => //.
    move : hℓ' hℓ .
    apply Order.le_trans.
  - hauto lq:on ctrs:Wff, Wt use:good_renaming_up db:wff.
  - hauto lq:on ctrs:Wt use:good_renaming_up, Wt_Pi_Univ_inv db:wff.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:icoherent_renaming, renaming_ieq_renaming.
Qed.

Lemma weakening_Syn Γ ℓ ℓ0 ℓ1 a A B i
  (h0 : Wt Γ ℓ0 B (tUniv i))
  (h1 : Wt Γ ℓ a A) :
  Wt ((ℓ1, B) :: Γ) ℓ (ren_tm shift a) (ren_tm shift A).
Proof.
  hauto l:on use:renaming_Syn db:wff unfold:good_renaming.
Qed.

Lemma weakening_Syn' Γ ℓ ℓ0 ℓ1 a A A0 B i
  (h2 : A0 = (ren_tm shift A))
  (h0 : Wt Γ ℓ0 B (tUniv i))
  (h1 : Wt Γ ℓ a A) :
  Wt ((ℓ1, B) :: Γ) ℓ (ren_tm shift a) A0.
Proof. sfirstorder use:weakening_Syn. Qed.

Lemma subsumption Γ ℓ a A : forall ℓ', (ℓ <= ℓ')%O -> Wt Γ ℓ a A -> Wt Γ ℓ' a A.
Proof.
  move => ℓ' h h1; move : ℓ' h.
  elim : Γ ℓ a A / h1; try qauto l:on ctrs:Wt.
  move => Γ ℓ i hΓ hi hℓ ℓ' hℓ'.
  apply T_Var => //.
  move : hℓ hℓ'.
  apply Order.le_trans.
Qed.

Definition good_morphing ρ Γ Δ :=
  forall i, i < length Γ -> Wt Δ (eith (unzip1 Γ) i) (ρ i) (subst_tm ρ (dep_ith (unzip2 Γ) i)).

Lemma T_Var' Γ ℓ i A :
  A = dep_ith (unzip2 Γ) i ->
  Wff Γ ->
  i < size Γ ->
  (eith (unzip1 Γ) i <= ℓ)%O ->
  (* ------ *)
  Wt Γ ℓ (var_tm i) A.
Proof. qauto ctrs:Wt. Qed.

Lemma good_morphing_up ρ k Γ Δ A
  (h : good_morphing ρ Γ Δ) :
  Wff Δ ->
  Wt Δ (subst_tm ρ A) (tUniv k) ->
  good_morphing (up_tm_tm ρ) (A :: Γ) (subst_tm ρ A :: Δ).
Proof.
  rewrite /good_morphing => h1 h2.
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
  - hauto q:on ctrs:Wt use:join_subst_star.
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

Lemma Wt_regularity Γ a A
  (h : Wt Γ a A) :
  exists i, Wt Γ A (tUniv i).
Proof.
  elim: Γ a A/h; try qauto ctrs:Wt depth:2.
  - inversion 1.
    hauto l:on use:dep_ith_shift,good_renaming_truncate, renaming_Syn.
  - hauto q:on use:subst_Syn, Wt_Pi_Univ_inv.
Qed.

Lemma Wt_App_inv Γ b a T (h : Wt Γ (tApp b a) T) :
  exists A B, Wt Γ b (tPi A B) /\
         Wt Γ a A /\
         Join (subst_tm (a..) B) T /\
         exists i, Wt Γ T (tUniv i).
Proof.
  move E : (tApp b a) h => ba h.
  move : b a E.
  elim : Γ ba T /h => //.
  - move => Γ a A B b h0 _ h1 _ ? ? [] *; subst.
    exists A, B; repeat split => //.
    + apply join_subst_star. apply Join_reflexive.
    + move /Wt_regularity : h0.
      move => [i /Wt_Pi_Univ_inv] [hA hB].
      exists i.
      change (tUniv i) with (subst_tm (b..) (tUniv i)).
      apply : subst_Syn; eauto.
  - hauto lq:on rew:off use:Join_transitive.
Qed.


Lemma Wt_If_inv Γ a b c T (h : Wt Γ (tIf a b c) T) :
  exists A, Wt Γ a tSwitch /\
         Wt Γ b A /\
         Wt Γ c A /\
         Join A T /\
         exists i, Wt Γ T (tUniv i).
Proof.
  move E : (tIf a b c) h => a0 h.
  move : a b c E.
  elim : Γ a0 T / h => //.
  - hauto lq:on rew:off use:Join_transitive.
  - qauto l:on use:Join_reflexive, Wt_regularity.
Qed.

Lemma preservation_helper A0 A1 i j Γ a A :
  Wt (A0 :: Γ) a A ->
  Wt Γ A0 (tUniv i) ->
  Wt Γ A1 (tUniv j) ->
  Join A0 A1 ->
  Wt (A1 :: Γ) a A.
Proof.
  move => h0 h1 h2 h3.
  replace a with (subst_tm ids a); last by asimpl.
  replace A with (subst_tm ids A); last by asimpl.
  apply morphing_Syn with (Γ := A0 :: Γ).
  - done.
  - case => [_ | k /Arith_prebase.lt_S_n ?].
    + rewrite dep_ith_ren_tm0; asimpl.
      apply T_Conv with (A := ren_tm shift A1) (i := i).
      * apply T_Var; hauto l:on db:wff.
      * change (tUniv i) with (ren_tm shift (tUniv i)).
        apply weakening_Syn with (i := j) => //.
      * hauto lq:on use:Join_symmetric, join_renaming.
    + asimpl.
      change (var_tm (S k)) with (ren_tm shift (var_tm k)).
      apply weakening_Syn with (i := j) => //.
      apply T_Var; hauto lq:on db:wff.
  - eauto with wff.
Qed.

Lemma subject_reduction a b (h : Par a b) : forall Γ A,
    Wt Γ a A -> Wt Γ b A.
Proof.
  elim : a b /h => //.
  - move => A0 A1 B0 B1 h0 ih0 h1 ih1 Γ A /Wt_Pi_inv.
    intros (i & hA0 & hAB0 & hAJoin & j & hA).
    have ? : Wff Γ by eauto with wff.
    apply T_Conv with (A := tUniv i) (i := j) => //.
    qauto l:on ctrs:Wt use:preservation_helper, Par_join.
  - move => A0 A1 a0 a1 h0 ih0 h1 ih1 Γ A /Wt_Abs_inv.
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
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 Γ A /Wt_App_inv.
    intros (A0 & B & hPi & hb0 & hJoin & i & hA).
    eapply T_Conv with (A := subst_tm (b1..) B); eauto.
    apply : T_App; eauto.
    apply : Join_transitive; eauto.
    apply Join_symmetric.
    apply Par_join.
    apply par_morphing; last by apply Par_refl.
    hauto q:on ctrs:Par inv:nat simp:asimpl.
  - move => a A a0 b0 b1 haa0 iha hbb0 ihb Γ A0 /Wt_App_inv.
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

Definition is_value (a : tm) :=
  match a with
  | tPi A B => true
  | tAbs A a => true
  | tSwitch => true
  | tOn => true
  | tOff => true
  | tFalse => true
  | tIf a b c => false
  | tApp a b => false
  | tUniv _ => true
  | var_tm _ => false
  end.

Inductive head := hPi | hAbs | hSwitch | hOn | hOff | hFalse | hUniv | hVar.

Definition tm_to_head (a : tm) :=
  match a with
  | tPi A B => Some hPi
  | tAbs A a => Some hAbs
  | tSwitch => Some hSwitch
  | tOn => Some hOn
  | tOff => Some hOff
  | tFalse => Some hFalse
  | tIf a b c => None
  | tApp a b => None
  | tUniv _ => Some hUniv
  | var_tm _ => Some hVar
  end.

Lemma par_head a b (h : Par a b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h => //. Qed.

Lemma par_head_star a b (h : Rstar _ Par a b) :
  forall hd, tm_to_head a = Some hd ->
        tm_to_head b = Some hd.
Proof. induction h; eauto using par_head. Qed.

Lemma join_consistent a b (h : Join a b) :
  forall hd hd1, tm_to_head a = Some hd ->
            tm_to_head b = Some hd1 ->
            hd = hd1.
Proof. qblast use:par_head_star. Qed.

Lemma Wt_Univ_winv Γ i U :
  Wt Γ (tUniv i) U ->
  exists j, Join (tUniv j) U.
Proof.
  move E : (tUniv i) => U0 h.
  move : i E.
  induction h => //; qauto l:on ctrs:Wt use:Join_transitive, Join_reflexive.
Qed.

Lemma Wt_False_winv Γ U :
  Wt Γ tFalse U ->
  exists j, Join (tUniv j) U.
Proof.
  move E : tFalse => U0 h.
  move : E.
  induction h => //; qauto l:on ctrs:Wt use:Join_transitive, Join_reflexive.
Qed.

Lemma Wt_On_Off_winv Γ a A (h : Wt Γ a A) :
  is_bool_val a -> Join tSwitch A.
Proof. induction h => //; qauto l:on ctrs:Wt use:Join_transitive, Join_reflexive. Qed.

Lemma Wt_Switch_winv Γ A :
  Wt Γ tSwitch A ->
  exists i, Join (tUniv i) A.
Proof.
  move E : tSwitch => a h. move : E.
  induction h => //; qauto l:on ctrs:Wt use:Join_transitive, Join_reflexive.
Qed.

Lemma wt_pi_canon a A B :
  Wt nil a (tPi A B) ->
  is_value a ->
  exists A a0, a = tAbs A a0.
Proof.
  case : a => //.
  - hauto lq:on.
  - qauto l:on use:Wt_Pi_inv, join_consistent.
  - qauto l:on use:Wt_False_winv, join_consistent.
  - qauto l:on use:Wt_Univ_winv, join_consistent.
  - qauto l:on use:Wt_On_Off_winv, join_consistent.
  - qauto l:on use:Wt_On_Off_winv, join_consistent.
  - qauto l:on use:Wt_Switch_winv, join_consistent.
Qed.

Lemma wt_switch_canon a :
  Wt nil a tSwitch ->
  is_value a ->
  is_bool_val a.
Proof.
  case : a => //.
  - qauto l:on use:Wt_Abs_inv, join_consistent.
  - qauto l:on use:Wt_Pi_inv, join_consistent.
  - qauto l:on use:Wt_False_winv, join_consistent.
  - qauto l:on use:Wt_Univ_winv, join_consistent.
  - qauto l:on use:Wt_Switch_winv, join_consistent.
Qed.

Lemma wt_progress a A (h :Wt nil a A) : is_value a \/ exists a0, Par a a0.
Proof.
  move E : nil h => Γ h.
  move : E.
  elim: Γ a A/h; try hauto q:on depth:2.
  - hauto lq:on rew:off ctrs:Par use:wt_pi_canon, Par_refl.
  - hauto lq:on rew:off use:wt_switch_canon, Par_refl.
Qed.
