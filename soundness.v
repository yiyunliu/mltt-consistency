From WR Require Import syntax join semtyping typing.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.


Definition γ_ok n Γ γ := forall i, i < n -> forall PA, InterpType (subst_tm γ (dep_ith Γ i)) PA -> PA (γ i).
Definition SemWt n Γ a A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA /\ PA (subst_tm γ a).
Definition SemUWf n Γ A := forall γ, γ_ok n Γ γ -> exists PA, InterpType (subst_tm γ A) PA.

Theorem soundness n Γ a A (h : Wt n Γ a A) : SemWt n Γ a A.
Proof.
  elim : n Γ a A / h; eauto.
  - rewrite /SemWt.
    move => n Γ i hi γ hγ.
    rewrite /γ_ok in hγ.
    move /(_ i hi) in hγ.
    admit.
  - hauto l:on.
  - admit.
  - admit.
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
    move /(_ _ PB hPA0b hPB) in hPF.
    rewrite /ProdSpace in hf.
    asimpl in *.
    exists PB; split; first done.
    move /(_ _ hPA0b) : hf; intros (PB0 & hPB0 & hPB0').

  - admit.
Admitted.
