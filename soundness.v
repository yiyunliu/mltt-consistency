From WR Require Import syntax join semtyping typing.
From Coq Require Import ssreflect ssrbool Sets.Relations_2 Sets.Relations_2_facts Sets.Relations_3 Program.Basics.
From Hammer Require Import Tactics.
Require Import Psatz.
From Equations Require Import Equations.

Definition γ_ok n Γ γ := forall i, i < n -> forall m PA, InterpUnivN m (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt n Γ a A := forall γ, γ_ok n Γ γ -> exists m PA, InterpUnivN m (subst_tm γ A) PA /\ PA (subst_tm γ a).

Lemma γ_ok_cons {n i Γ γ a PA A} :
  InterpUnivN i (subst_tm γ A) PA ->
  PA a ->
  γ_ok n Γ γ ->
  γ_ok (S n) (A .: Γ) (a .: γ).
Proof.
  move => h0 h1 h2.
  case => [_ | m ? PA0].
  - asimpldep.
    move => j PA0 hPA0.
    suff : PA = PA0 by congruence.
    hauto l:on use:InterpUnivN_deterministic'.
  - rewrite dep_ith_ren_tm.
    asimpl.
    apply h2.
    lia.
Qed.

Lemma γ_ok_renaming n Γ γ :
  forall m Δ ξ,
    (forall i, i < n -> ξ i < m) ->
    (forall i, i < n -> ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i)) ->
    γ_ok m Δ γ ->
    γ_ok n Γ (ξ >> γ).
Proof.
  move => m Δ ξ hscope h0 h1.
  rewrite /γ_ok => i hi PA.
  asimpl.
  replace (subst_tm (ξ >> γ) (dep_ith Γ i)) with
    (subst_tm γ (ren_tm ξ (dep_ith Γ i))); last by asimpl.
  rewrite h0; auto.
  apply h1.
  firstorder.
Qed.

Lemma renaming_SemWt n Γ a A :
  SemWt n Γ a A ->
  forall m Δ ξ,
    (forall i, i < n -> ξ i < m) ->
    (forall i, i < n -> ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i)) ->
    SemWt m Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  rewrite /SemWt => h m Δ ξ hscope hwf γ hγ.
  have hγ' : (γ_ok n Γ (ξ >> γ)) by eauto using γ_ok_renaming.
  case /(_ _ hγ') : h => PA hPA.
  exists PA.
  by asimpl.
Qed.

Lemma γ_ok_consU {n i Γ γ a PA A} :
  InterpUnivN i (subst_tm γ A) PA ->
  PA a ->
  γ_ok n Γ γ ->
  γ_ok (S n) (A .: Γ) (a .: γ).
Proof.
  hauto q:on use:γ_ok_cons, InterpUnivN_deterministic'.
Qed.

Theorem soundness n Γ a A (h : Wt n Γ a A) : SemWt n Γ a A.
Proof.
  elim : n Γ a A / h.
  - move => n Γ i F h ih ? γ hγ.
    move /(_ i ltac:(done)) in ih.
    suff ih' : SemWt n Γ (dep_ith Γ i) (tUniv (F i)).
    + case /(_ _ hγ) : ih' => j [PA [hPA hi]].
      simpl in hPA.
      simp InterpUnivN in hPA.
      move /InterpExt_Univ_inv : hPA => [? h0]; subst.
      move : hi; intros (PA & hi).
      move /(_ h0) in hi.
      exists (F i), PA; sfirstorder.
    + apply (renaming_SemWt _ _ _ _ ih); first by lia.
      move => i0 ?.
      asimpldep.
      simpl.
      f_equal.
      fext.
      move => *.
      asimpl; lia.
  - move => n Γ i γ hγ.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    hauto l:on use:InterpUnivN_Univ_inv.
  - rewrite /SemWt.
    move => // n Γ i A B _h0 h0 _h1 h1 γ hγ.
    move /(_ γ hγ) : h0; intros (m & P_Univ & hP_Univ & hP_Univ').
    move /InterpUnivN_Univ_inv' : hP_Univ => [*]; subst.
    case : hP_Univ' => PA hPA.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    split; first by eauto using InterpUnivN_Univ_inv.
    exists (ProdSpace PA (fun a PB => InterpUnivN i (subst_tm (a .: γ) B) PB)).
    simp InterpUniv.
    simpl.
    apply InterpExt_Fun.
    + simp InterpUniv in hPA.
    + move => a ha.
      move /(_ _ ltac:(qauto use:γ_ok_consU)) in h1.
      move : h1; intros (x & PB & hPB & h).
      move /InterpUnivN_Univ_inv' : hPB => [*]; subst.
      hauto lq:on rew:db:InterpUniv.
    + move => a PB ha.
      suff hγ_cons : γ_ok (S n) (A .: Γ) (a .: γ) by asimpl.
      qauto use:γ_ok_consU.
  - rewrite /SemWt.
    move => n Γ A a B i _ hB _ ha.
    move => γ hγ.
    move /(_ γ hγ) : hB; intros (l & PPi & hPPi & hPi).
    move /InterpUnivN_Univ_inv' : hPPi => [*]; subst.
    case  : hPi => /= PPi hPPi.
    simp InterpUniv in hPPi.
    move /InterpExt_Fun_inv : hPPi. intros (PA & PF & hPA & hTot & hPF & ?); subst.
    exists i, (ProdSpace PA (fun a PB => InterpUnivN i (subst_tm (a .: γ) B) PB)).
    split.
    + simpl; simp InterpUniv.
      apply InterpExt_Fun; first by [].
      * move => a0 ha0.
        case /(_ a0 ha0) : hTot => PB hPB.
        move /(_ a0 PB ha0 hPB) in hPF.
        exists PB.
        by asimpl in hPF.
      * move => *.
        by asimpl.
    + rewrite /ProdSpace => b hPAb.
      move /(_ (b .: γ) ltac:(hauto l:on use:γ_ok_cons rew:db:InterpUniv)) : ha.
      intros (j & PB & hPB & hPBa).
      case /(_ b hPAb) : hTot => PB0 hPB0.
      move /(_ b PB0 hPAb hPB0) in hPF.
      rewrite -InterpUnivN_nolt in hPF.
      asimpl in hPF.
      have ? : PB0 = PB by best use:InterpUnivN_deterministic'.
      subst.
      exists PB; split; eauto.
      apply : InterpUnivN_back_clos; eauto.
      apply : P_AppAbs'.
      2 : {
        apply Par_refl.
      }
      by asimpl.
      apply Par_refl.
  - move => n Γ f A B b _ ihf _ ihb γ hγ.
    rewrite /SemWt in ihf ihb.
    move /(_ γ hγ) : ihf; intros (PPi & hPi & hf).
    move /(_ γ hγ) : ihb; intros (PA & hPA & hb).
    simpl in hPi.
    move /InterpType_Fun_inv' : hPi;
      intros (PA0 & PF & hPA0 & hPFTot & hPF & ?); subst.
    have ? : forall x, PA x <-> PA0 x by eauto using InterpType_deterministic.
    have hPA0b : PA0 (subst_tm γ b) by sfirstorder.
    move /(_ _ hPA0b) : hPFTot; intros (PB & hPB).
    have hPB' := hPF _ PB hPA0b hPB.
    rewrite /ProdSpace in hf.
    asimpl in *.
    exists PB; split; first done.
    move /(_ _ hPA0b) : hf; intros (PB0 & hPB0 & hPB0').
    have hPB0'' := hPF _ PB0 hPA0b hPB0.
    asimpl in hPB0''.
    qauto l:on use:InterpType_deterministic.
  - rewrite /SemWt /SemUWf /Join /coherent => n Γ a A B _ hA _ hB [C [? ?]] γ hγ.
    move : (hA γ hγ) => [PA [hPA hPAa]].
    move : (hB γ hγ) => [PB hPB].
    exists PB.
    split; auto.
    have [*] : Rstar _ Par (subst_tm γ A) (subst_tm γ C) /\
                 Rstar _ Par (subst_tm γ B) (subst_tm γ C)
      by sfirstorder use:par_subst_star.
    have ? :InterpType (subst_tm γ C) PB by sfirstorder use:InterpType_preservation_star.
    have ? :InterpType (subst_tm γ A) PB by sfirstorder use:InterpType_back_preservation_star.
    suff : forall x, PA x <-> PB x by sfirstorder.
    eauto using InterpType_deterministic.
  - hauto l:on.
  - hauto l:on.
  - rewrite /SemWt => n Γ a b c A _ ha _ hb _ hc γ hγ.
    case : (ha _ hγ) => PS [/InterpType_Switch_inv ? ha']; subst.
    case : (hb _ hγ) => PA [hPA hb'].
    case : (hc _ hγ) => PB [hPB hc'].
    exists PA; split; auto.
    simpl.
    case : ha' => v [hred hv].
    case : v hred hv => // ha0 _.
    + apply InterpType_back_clos_star with (A := (subst_tm γ A)) (b := (subst_tm γ b)) => //.
      eauto using P_IfOn_star with sets.
    + apply InterpType_back_clos_star with (A := (subst_tm γ A)) (b := (subst_tm γ c)) => //.
      eauto using P_IfOff_star with sets.
      suff : forall x, PA x <-> PB x by hauto l:on.
      eauto using InterpType_deterministic.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on.
  - rewrite /SemUWf.
    move => // n Γ A B _ h0 _ h1 γ hγ.
    move /(_ γ hγ) : h0. intros (PA & hPA).
    exists (ProdSpace PA (fun a PB => InterpType (subst_tm (a .: γ) B) PB)).
    simpl.
    apply InterpType_Fun; eauto.
    + move => a ha.
      hauto l:on use:γ_ok_cons.
    + move => a PB ha.
      suff hγ_cons : γ_ok (S n) (A .: Γ) (a .: γ) by asimpl.
      qauto use:γ_ok_cons.
  - rewrite /SemWt /SemUWf.
    move => n Γ A _ ih γ hγ.
    move : (ih γ hγ). intros (PA & hPA & hA).
    move /InterpType_Univ_inv : hPA => ?; subst.
    sfirstorder use:InterpUniv_subset_InterpType.
  - hauto l:on.
Qed.

Lemma consistency a Γ : ~Wt 0 Γ a tFalse.
Proof.
  move => h.
  apply soundness in h.
  rewrite /SemWt in h.
  move : (h var_tm).
  case.
  rewrite /γ_ok; lia.
  asimpl.
  move => PA [hPA ha].
  have ? : InterpType tFalse (const False) by sfirstorder.
  suff : forall x, PA x <-> (const False) x by firstorder.
  eauto using InterpType_deterministic.
Qed.

Example univ_fun := (tAbs tSwitch (tIf (var_tm var_zero) tSwitch (tPi tSwitch tSwitch))).

Example large_elim_example Γ : Wt 0 Γ tOn (tApp univ_fun tOn).
Proof.
  apply T_Conv with (A := tSwitch).
  sfirstorder use:T_On.
  apply U_Embed.
  change (tUniv) with (subst_tm (tOn..) tUniv).
  apply T_App with (A := tSwitch).
  apply T_Abs; eauto.
  apply U_Switch.
  apply T_If.
  apply T_Var.
  case; last by lia.
  asimpl.
  simpl.
  sfirstorder.
  asimpl.
  lia.
  sfirstorder.
  sauto lq:on.
  sfirstorder.
  exists tSwitch.
  split.
  eauto with sets.
  rewrite /univ_fun.
  apply : Rstar_n.
  apply : P_AppAbs; sfirstorder use:Par_refl.
  apply Rstar_contains_R => /=.
  hauto lq:on ctrs:Par use:Par_refl.
Qed.
