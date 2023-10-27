From WR Require Import syntax join semtyping typing.
From Coq Require Import ssreflect Sets.Relations_2 Sets.Relations_3 Program.Basics.
From Hammer Require Import Tactics.
Require Import Psatz.


Definition γ_ok n Γ γ := forall i, i < n -> forall PA, InterpType (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt n Γ a A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA /\ PA (subst_tm γ a).
Definition SemUWf n Γ A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA.

Lemma γ_ok_cons {n Γ γ a PA A} :
  InterpType (subst_tm γ A) PA ->
  PA a ->
  γ_ok n Γ γ ->
  γ_ok (S n) (A .: Γ) (a .: γ).
Proof.
  move => h0 h1 h2.
  case => [_ | m ? PA0].
  - asimpldep.
    move => PA0 hPA0.
    have := InterpType_deterministic _ _ _ h0 hPA0.
    firstorder.
  - rewrite dep_ith_ren_tm.
    asimpl.
    apply h2.
    lia.
Qed.

Lemma γ_ok_consU {n Γ γ a PA A} :
  InterpUniv (subst_tm γ A) PA ->
  PA a ->
  γ_ok n Γ γ ->
  γ_ok (S n) (A .: Γ) (a .: γ).
Proof.
  hauto q:on use:γ_ok_cons, InterpUniv_subset_InterpType.
Qed.

Theorem soundness : forall n Γ,
  (forall a A (h : Wt n Γ a A), SemWt n Γ a A) /\
  (forall A (h : UWf n Γ A), SemUWf n Γ A).
Proof.
  apply  Wt_mutual; eauto.
  - rewrite /SemWt.
    move => n Γ i hi γ hγ.
    rewrite /γ_ok in hγ.
    move /(_ i hi) in hγ.
    admit.
  - hauto l:on.
  - rewrite /SemWt.
    move => // n Γ A B _ h0 _ h1 γ hγ.
    move /(_ γ hγ) : h0; intros (P_Univ & hP_Univ & hP_Univ').
    move /InterpType_Univ_inv : hP_Univ => ?; subst.
    move : hP_Univ'; intros (PA & hPA).
    exists (fun A => exists PA, InterpUniv A PA); simpl; split; first by apply InterpType_Univ.
    exists (ProdSpace PA (fun a PB => InterpUniv (subst_tm (a .: γ) B) PB)).
    apply InterpUniv_Fun; eauto.
    + move => a ha.
      move /(_ _ ltac:(qauto use:γ_ok_consU)) in h1.
      move : h1; intros (? & hPB & h).
      move /InterpType_Univ_inv : hPB => ?; subst.
      firstorder.
    + move => a PB ha.
      suff hγ_cons : γ_ok (S n) (A .: Γ) (a .: γ) by asimpl.
      qauto use:γ_ok_consU.
  - rewrite /SemUWf /SemWt.
    move => n Γ A a B _ hA _ hB.
    move => γ hγ.
    move /(_ γ hγ) : hA; intros (PA & hPA).
    exists (ProdSpace PA (fun a PB => InterpType (subst_tm (a .: γ) B) PB)).
    split.
    + simpl.
      apply InterpType_Fun; first done.
      * move => *.
        qauto l:on ctrs:InterpType use:γ_ok_cons.
      * move => *.
        by asimpl.
    + rewrite /ProdSpace => b hPAb.
      move /(_ _ ltac:(qauto use:γ_ok_cons)) : hB. intros (PB & hPB & hPBa).
      exists PB; split; eauto.
      simpl.
      apply : InterpType_back_clos; eauto.
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
  - rewrite /SemWt /SemUWf /Join /coherent.
    move => n Γ a A B _ hA _ hB [C [? ?]] γ hγ.
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
Admitted.

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
