From WR Require Import syntax join semtyping typing common.
From Coq Require Import ssreflect ssrbool Sets.Relations_2 Sets.Relations_2_facts Sets.Relations_3 Program.Basics.
From Hammer Require Import Tactics.
From Equations Require Import Equations.

Definition γ_ok Γ γ0 γ1 := forall i, i < length Γ -> forall m PA, InterpUnivN m (subst_tm γ0 (dep_ith Γ i)) (subst_tm γ1 (dep_ith Γ i)) PA -> PA (γ0 i) (γ1 i).

Definition SemWt Γ a A := forall γ0 γ1, γ_ok Γ γ0 γ1 -> exists m PA, InterpUnivN m (subst_tm γ0 A) (subst_tm γ1 A) PA /\ PA (subst_tm γ0 a) (subst_tm γ1 a).

Definition SemWff Γ := forall i, i < length Γ -> exists F, SemWt (skipn (S i) Γ) (ith Γ i) (tUniv (F i)).

Lemma γ_ok_cons {i Γ γ0 γ1 a b PA A B} :
  InterpUnivN i (subst_tm γ0 A) (subst_tm γ1 B) PA ->
  PA a b ->
  γ_ok Γ γ0 γ1 ->
  γ_ok (A :: Γ) (a .: γ0) (b .: γ1).
Proof.
  move => h0 h1 h2.
  case => /= [_ | m ? PA0].
  - move => j PA0 hPA0.
    asimpl in hPA0.
    suff : PA = PA0 by congruence.
    hauto l:on use:InterpUnivN_deterministic'.
  - asimpl.
    apply h2.
    lia.
Qed.

Lemma γ_ok_renaming Γ γ0 γ1 :
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    γ_ok Δ γ0 γ1 ->
    γ_ok Γ (ξ >> γ0) (ξ >> γ1).
Proof.
  move => Δ ξ hscope h1.
  rewrite /γ_ok => i hi j PA.
  replace (subst_tm (ξ >> γ0) (dep_ith Γ i)) with
    (subst_tm γ0 (ren_tm ξ (dep_ith Γ i))); last by asimpl.
  replace (subst_tm (ξ >> γ1) (dep_ith Γ i)) with
    (subst_tm γ1 (ren_tm ξ (dep_ith Γ i))); last by asimpl.
  rewrite /good_renaming in hscope.
  case /(_ i ltac:(lia)) : hscope => ? h0.
  rewrite -h0; auto.
  rewrite /γ_ok in h1.
  by apply h1; lia.
Qed.

Lemma renaming_SemWt Γ a A :
  SemWt Γ a A ->
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    SemWt Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  rewrite /SemWt => h Δ ξ hξ γ0 γ1 hγ.
  have hγ' : (γ_ok Γ (ξ >> γ0) (ξ >> γ1)) by eauto using γ_ok_renaming.
  case /(_ _ _ hγ') : h => PA hPA.
  exists PA.
  by asimpl.
Qed.

Lemma γ_ok_consU {i Γ γ0 γ1 a b PA A B} :
  InterpUnivN i (subst_tm γ0 A) (subst_tm γ1 B) PA ->
  PA a b ->
  γ_ok Γ γ0 γ1 ->
  γ_ok (A :: Γ) (a .: γ0) (b .: γ1).
Proof.
  hauto q:on use:γ_ok_cons, InterpUnivN_deterministic'.
Qed.

Section SemanticTyping.
  Variable Γ : context.

  Variable A B a b : tm.

  Variable m : nat.

  Lemma ST_Var i :
    SemWff Γ ->
    i < length Γ ->
    (* ----------------------------------------------------- *)
    SemWt Γ (var_tm i) (dep_ith Γ i).
  Proof using Γ.
    move => ih ? γ0 γ1 hγ.
    move /(_ i ltac:(done)) in ih.
    case : ih => F ih.
    suff ih' : SemWt Γ (dep_ith Γ i) (tUniv (F i)).
    + case /(_ _ _ hγ) : ih' => j [PA [hPA hi]].
      simpl in hPA.
      case /InterpUnivN_Univ_inv' : hPA => ? ?; subst.
      move : hi; intros (PA & hi).
      exists (F i), PA; sfirstorder.
    + hauto l:on use:dep_ith_shift, good_renaming_truncate, renaming_SemWt.
  Qed.

  Lemma ST_False :
    SemWff Γ ->
    SemWt Γ tFalse (tUniv m).
  Proof using m.
    hauto l:on use:InterpUniv_Univ, InterpUniv_False.
  Qed.

  Lemma ST_Abs :
    SemWt Γ (tPi A B) (tUniv m) ->
    SemWt (A :: Γ) a B ->
    (* ----------------------- *)
    SemWt Γ (tAbs A a) (tPi A B).
  Proof.
    rewrite /SemWt.
    move => //  h0 h1 γ0 γ1 hγ.
    move /(_ γ0 γ1 hγ) : h0; intros (n & P_Univ & hP_Univ & hP_Univ').
    move /InterpUnivN_Univ_inv' : hP_Univ => [*]; subst.
    case : hP_Univ' => PA hPA.
    exists m, PA; split; first by auto.
    simpl in hPA.
    move /InterpUniv_Fun_inv : hPA.
    rename PA into PA0.
    intros (A0 & B0 & PA & PF & ? & hPA0 & hTot & hRes & hPF & ?). subst.
    move => a0 a1 PB ha hPB.
    move /InterpUniv_Refl in hPA0.
    have hγ' : γ_ok (subst_tm γ0 A :: Γ) (a0 .: γ0) (a1 .: γ1) by
    apply : γ_ok_cons ;eauto.
    simpl.
    apply : InterpUnivN_back_clos; eauto.


    move /InterpUnivN_inv_Fun : hPA .
    exists (S m), (fun A B => exists PA, InterpUnivN m A B PA).
    split; first by best use: InterpUnivN_Univ_inv.
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
      suff hγ_cons : γ_ok (A :: Γ) (a .: γ) by asimpl.
      qauto use:γ_ok_consU.

End SemanticTyping.

Theorem soundness Γ :
  (forall a A, Wt Γ a A -> SemWt Γ a a A A) /\
  (Wff Γ -> forall i, i < length Γ -> exists F, SemWt (skipn (S i) Γ) (ith Γ i) (ith Γ i) (tUniv (F i)) (tUniv (F i))).
Proof.
  move : Γ.
  apply wt_mutual.
  -
  -
  - rewrite /SemWt.
    move => // Γ i A B _h0 h0 _h1 h1 γ hγ.
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
      suff hγ_cons : γ_ok (A :: Γ) (a .: γ) by asimpl.
      qauto use:γ_ok_consU.
  - rewrite /SemWt.
    move => Γ A a B i _ hB _ ha.
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
      have ? : PB0 = PB by hauto l:on use:InterpUnivN_deterministic'.
      subst.
      exists PB; split; eauto.
      apply : InterpUnivN_back_clos; eauto.
      apply : P_AppAbs'.
      2 : {
        apply Par_refl.
      }
      by asimpl.
      apply Par_refl.
  - move => Γ f A B b _ ihf _ ihb γ hγ.
    rewrite /SemWt in ihf ihb.
    move /(_ γ hγ) : ihf; intros (i & PPi & hPi & hf).
    move /(_ γ hγ) : ihb; intros (j & PA & hPA & hb).
    simpl in hPi.
    rewrite InterpUnivN_nolt in hPi.
    move /InterpExt_Fun_inv : hPi;
      intros (PA0 & PF & hPA0 & hPFTot & hPF & ?); subst.
    rewrite -InterpUnivN_nolt in hPA0.
    have ? : PA0 = PA by eauto using InterpUnivN_deterministic'.
    subst.
    have hPA0b : PA (subst_tm γ b) by sfirstorder.
    move /(_ _ hPA0b) : hPFTot; intros (PB & hPB).
    have hPB' := hPF _ PB hPA0b hPB.
    rewrite -InterpUnivN_nolt in hPB'.
    rewrite /ProdSpace in hf.
    asimpl in *.
    exists i, PB; split; first done.
    move /(_ _ hPA0b) : hf; intros (PB0 & hPB0 & hPB0').
    have hPB0'' := hPF _ PB0 hPA0b hPB0.
    asimpl in hPB0''.
    rewrite -InterpUnivN_nolt in hPB0''.
    suff : PB = PB0 by congruence.
    sfirstorder use:InterpUnivN_deterministic'.
  - rewrite /SemWt /Join /coherent => Γ a A B i _ hA _ hB [C [? ?]] γ hγ.
    case : (hA γ hγ) => j [PA [hPA hPAa]].
    case : (hB γ hγ) => k [PB [hPB hPB']].
    simpl in hPB.
    case /InterpUnivN_Univ_inv' : hPB => ? ?. subst.
    case : hPB' =>  PA0 hPA0.
    exists i, PA0.
    split; auto.
    have [*] : Rstar _ Par (subst_tm γ A) (subst_tm γ C) /\
                 Rstar _ Par (subst_tm γ B) (subst_tm γ C)
      by sfirstorder use:par_subst_star.
    have ? :InterpUnivN i (subst_tm γ C) PA0 by sfirstorder use:InterpUnivN_preservation_star.
    have ? :InterpUnivN i (subst_tm γ A) PA0 by sfirstorder use:InterpUnivN_back_preservation_star.
    suff : PA = PA0 by congruence.
    eauto using InterpUnivN_deterministic'.
  - hauto l:on.
  - hauto l:on.
  - rewrite /SemWt => Γ a b c A _ ha _ hb _ hc γ hγ.
    case /(_ γ hγ) : ha => i [? [/InterpUnivN_Switch_inv ? ha']]; subst.
    case /(_ γ hγ) : hb => j [PA [hPA hb']].
    case /(_ γ hγ) : hc => k [PB [hPB hc']].
    have ? : PA = PB by hauto lq:on rew:off use:InterpUnivN_deterministic'.
    subst.
    exists j, PB; split; auto.
    simpl.
    case : ha' => v [hred hv].
    case : v hred hv => // ha0 _.
    + apply (InterpUnivN_back_clos_star j) with (A := (subst_tm γ A)) (b := (subst_tm γ b)) => //.
      eauto using P_IfOn_star with sets.
    + apply (InterpUnivN_back_clos_star k) with (A := (subst_tm γ A)) (b := (subst_tm γ c)) => //.
      eauto using P_IfOff_star with sets.
  - rewrite /SemWt => Γ i γ hγ.
    simpl.
    exists (S i), (fun A => exists PA, InterpUnivN i A PA).
    hauto l:on use:InterpUnivN_Univ_inv.
  - move => Γ i j ? γ hγ /=.
    exists (S j), (fun A => exists PA, InterpUnivN j A PA).
    sfirstorder use:InterpUnivN_Univ_inv.
  - hauto l:on.
Qed.

Lemma consistency a : ~Wt nil a tFalse.
Proof.
  move => h.
  apply soundness in h.
  rewrite /SemWt in h.
  move : (h var_tm).
  case.
  rewrite /γ_ok; sauto lq:on.
  asimpl.
  move => i [PA [hPA ha]].
  simp InterpUniv in hPA.
  apply InterpExt_False_inv in hPA; subst.
  apply ha.
Qed.
