Require Import imports.

Module Type geq_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

  Definition econtext := list T.
  Open Scope lattice_scope.

  Definition elookup i Ξ (ℓ : T) := nth_error Ξ i = Some ℓ.

  Inductive IOk (Ξ : econtext) (ℓ : T) : tm -> Prop :=
  | IO_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->
    (* ------- *)
    IOk Ξ ℓ (var_tm i)
  | IO_Univ i :
    (* -------- *)
    IOk Ξ ℓ (tUniv i)
  | IO_Pi ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->
    (* --------------------- *)
    IOk Ξ ℓ (tPi ℓ0 A B)
  | IO_Abs ℓ0 a :
    IOk (ℓ0 :: Ξ) ℓ a ->
    (* -------------------- *)
    IOk Ξ ℓ (tAbs ℓ0 a)
  | IO_App a ℓ0 b :
    IOk Ξ ℓ a ->
    IOk Ξ ℓ0 b ->
    (* ------------------------- *)
    IOk Ξ ℓ (tApp a ℓ0 b)
  | IO_Void :
    IOk Ξ ℓ tVoid
  | IO_Absurd a:
    IOk Ξ ℓ (tAbsurd a)
  | IO_Refl :
    IOk Ξ ℓ tRefl
  | IO_Eq ℓ0 a b A :
    ℓ0 ⊆ ℓ ->
    IOk Ξ ℓ a ->
    IOk Ξ ℓ b ->
    IOk Ξ ℓ A ->
    (* -------------- *)
    IOk Ξ ℓ (tEq ℓ0 a b A)
  | IO_J C ℓp t p :
    ℓp ⊆ ℓ ->
    IOk Ξ ℓ t ->
    IOk Ξ ℓp p ->
    (* --------------- *)
    IOk Ξ ℓ (tJ C t p)

  | IO_Sig ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->
    (* --------------- *)
    IOk Ξ ℓ (tSig ℓ0 A B)

  | IO_Pack ℓ0 a b :
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ b ->
    (* --------------- *)
    IOk Ξ ℓ (tPack ℓ0 a b)

  | IO_Let ℓ0 ℓ1 a b :
    ℓ1 ⊆ ℓ ->
    IOk Ξ ℓ1 a ->
    IOk (ℓ1::ℓ0::Ξ) ℓ b ->
    (* -------------------- *)
    IOk Ξ ℓ (tLet ℓ0 ℓ1 a b).

  Inductive IEq (Ξ : econtext) (ℓ : T) : tm -> tm -> Prop :=
  | I_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->
    (* ------- *)
    IEq Ξ ℓ (var_tm i) (var_tm i)
  | I_Univ i :
    (* -------- *)
    IEq Ξ ℓ (tUniv i) (tUniv i)
  | I_Pi ℓ0 A0 A1 B0 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->
    (* --------------------- *)
    IEq Ξ ℓ (tPi ℓ0 A0 B0) (tPi ℓ0 A1 B1)
  | I_Abs ℓ0 a0 a1 :
    IEq (ℓ0 :: Ξ) ℓ a0 a1 ->
    (* -------------------- *)
    IEq Ξ ℓ (tAbs ℓ0 a0) (tAbs ℓ0 a1)
  | I_App a0 a1 ℓ0 b0 b1 :
    IEq Ξ ℓ a0 a1 ->
    GIEq Ξ ℓ ℓ0 b0 b1 ->
    (* ------------------------- *)
    IEq Ξ ℓ (tApp a0 ℓ0 b0) (tApp a1 ℓ0 b1)
  | I_Void :
    IEq Ξ ℓ tVoid tVoid
  | I_Absurd a b :
    IEq Ξ ℓ (tAbsurd a) (tAbsurd b)
  | I_Refl :
    IEq Ξ ℓ tRefl tRefl
  | I_Eq ℓ0 a0 a1 b0 b1 A0 A1 :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq Ξ ℓ b0 b1 ->
    IEq Ξ ℓ A0 A1 ->
    (* -------------- *)
    IEq Ξ ℓ (tEq ℓ0 a0 b0 A0) (tEq ℓ0 a1 b1 A1)
  | I_J C0 C1 t0 t1 p0 p1 :
    IEq Ξ ℓ t0 t1 ->
    IEq Ξ ℓ p0 p1 ->
    (* --------------- *)
    IEq Ξ ℓ (tJ C0 t0 p0) (tJ C1 t1 p1)
  | I_Sig ℓ0 A0 B0 A1 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->
    (* --------------- *)
    IEq Ξ ℓ (tSig ℓ0 A0 B0) (tSig ℓ0 A1 B1)

  | I_Pack ℓ0 a0 b0 a1 b1 :
    GIEq Ξ ℓ ℓ0 a0 a1 ->
    IEq Ξ ℓ b0 b1 ->
    (* --------------- *)
    IEq Ξ ℓ (tPack ℓ0 a0 b0) (tPack ℓ0 a1 b1)

  | I_Let ℓ0 ℓ1 a0 b0 a1 b1 :
    IEq Ξ ℓ a0 a1 ->
    IEq (ℓ1::ℓ0::Ξ) ℓ b0 b1 ->
    (* -------------------- *)
    IEq Ξ ℓ (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1)

  with GIEq (Ξ : econtext) (ℓ : T) : T -> tm -> tm -> Prop :=
  | GI_Dist ℓ0 A B :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ A B ->
    (* -------------- *)
    GIEq Ξ ℓ ℓ0 A B
  | GI_InDist ℓ0 A B :
    ~ (ℓ0 ⊆ ℓ) ->
    (* -------------- *)
    GIEq Ξ ℓ ℓ0 A B.

  #[export]Hint Constructors IOk IEq GIEq : ieq.

  Scheme IEq_ind' := Induction for IEq Sort Prop
      with GIEq_ind' := Induction for GIEq Sort Prop.

  Combined Scheme IEq_mutual from IEq_ind', GIEq_ind'.

  Derive Inversion IEq_inv with (forall Ξ ℓ a b, IEq Ξ ℓ a b).
  Derive Inversion GIEq_inv with (forall Ξ ℓ ℓ0 a b, GIEq Ξ ℓ ℓ0 a b).

  Definition iok_ren_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> elookup (ρ i) Δ ℓ.

  Definition iok_subst_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> IOk Δ ℓ (ρ i).

End geq_sig.


Module geq_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import geq : geq_sig lattice syntax).

  Module lprop :=  Lattice.All.Properties lattice.
  Import lprop.
  Module solver  :=  Solver lattice.
  Import solver.

  Lemma iok_subsumption Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall ℓ0, ℓ ⊆ ℓ0 -> IOk Ξ ℓ0 a.
  Proof.
    elim : Ξ ℓ a / h; hauto lq:on ctrs:IOk use:leq_trans.
  Qed.

  Lemma iok_ren_ok_suc ρ Ξ Δ (h : iok_ren_ok ρ Ξ Δ) :
    forall ℓ0, iok_ren_ok (upRen_tm_tm ρ) (ℓ0 :: Ξ) (ℓ0 :: Δ).
  Proof.
    move => ℓ0.
    rewrite /iok_ren_ok /elookup.
    case=>//=.
  Qed.

  Lemma iok_renaming Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall Δ ρ, iok_ren_ok ρ Ξ Δ  ->
           IOk Δ ℓ a⟨ρ⟩.
  Proof.
    elim : Ξ ℓ a / h;
      qauto l:on ctrs:IOk use:IO_Let use:iok_ren_ok_suc, iok_subsumption unfold:elookup, iok_ren_ok.
  Qed.

  Lemma iok_subst_ok_suc ρ Ξ Δ (h : iok_subst_ok ρ Ξ Δ) :
    forall ℓ0, iok_subst_ok (up_tm_tm ρ) (ℓ0 :: Ξ) (ℓ0 :: Δ).
  Proof.
    move => ℓ0.
    rewrite /iok_subst_ok.
    case=>//=.
    - move => _ [<-].
      apply : IO_Var.
      rewrite /elookup //=.
      by rewrite meet_idempotent.
    - move => n ℓ ?.
      asimpl. apply : iok_renaming; eauto.
      sfirstorder.
  Qed.

  Lemma iok_morphing Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall Δ ρ, iok_subst_ok ρ Ξ Δ  ->
           IOk Δ ℓ a[ρ].
  Proof.
    elim : Ξ ℓ a / h; qauto l:on ctrs:IOk use:iok_subst_ok_suc, iok_subsumption unfold:iok_subst_ok, elookup.
  Qed.

  Lemma iok_subst Ξ ℓ ℓ0 a b (h : IOk Ξ ℓ0 a)
    (h0 : IOk (ℓ0::Ξ) ℓ b) : IOk Ξ ℓ b[a..].
  Proof.
    apply : iok_morphing; eauto.
    case.
    - rewrite /elookup //=.
      scongruence.
    - move => n ℓ1. asimpl.
      move => ?.
      have : elookup n Ξ ℓ1 by sfirstorder.
      move => h2.
      apply : IO_Var; eauto.
      by rewrite meet_idempotent.
  Qed.

  Lemma iok_ieq Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall ℓ0, ℓ ⊆ ℓ0 -> IEq Ξ ℓ0 a a.
  Proof.
    elim : Ξ ℓ a / h; eauto using leq_trans with ieq.
    (* App *)
    - move => Ξ ℓ a ℓ0 b ha iha hb ihb ℓ1 ?.
      apply I_App; eauto.
      case : (sub_eqdec ℓ0 ℓ1) => //; hauto l:on ctrs:GIEq.
    - move => Ξ ℓ ℓ0 a b A hℓ ha iha hb ihb hA ihA ℓ1 hℓ'.
      have : ℓ0 ⊆ ℓ1 by eauto using leq_trans.
      hauto lq:on ctrs:IEq.
    - move => Ξ ℓ ℓ0 a b ha iha hb ihb ℓ1 ?.
      apply I_Pack; eauto.
      case : (sub_eqdec ℓ0 ℓ1) => //; hauto l:on ctrs:GIEq.
  Qed.

  Lemma ieq_gieq Ξ ℓ ℓ0 a b (h : forall ℓ0, ℓ ⊆ ℓ0 -> IEq Ξ ℓ0 a b) :
    GIEq Ξ ℓ0 ℓ a b.
  Proof.
    case : (sub_eqdec ℓ ℓ0).
    - firstorder using GI_Dist.
    - move /GI_InDist. apply.
  Qed.

  Lemma iok_gieq Ξ ℓ ℓ0 a (h : IOk Ξ ℓ a) :
    GIEq Ξ ℓ0 ℓ a a.
  Proof. sfirstorder use:iok_ieq, ieq_gieq. Qed.

  Lemma ieq_sym_mutual : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A) /\
        (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> GIEq Ξ ℓ ℓ0 B A).
  Proof.
    apply IEq_mutual; eauto with ieq.
  Qed.

  Lemma ieq_sym : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A).
  Proof. sfirstorder use:ieq_sym_mutual. Qed.

  Lemma ieq_trans_mutual : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> forall C, IEq Ξ ℓ B C -> IEq Ξ ℓ A C) /\
        (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> forall C, GIEq Ξ ℓ ℓ0 B C -> GIEq Ξ ℓ ℓ0 A C).
  Proof.
    apply IEq_mutual; hauto lq:on ctrs:IEq, GIEq inv:IEq,GIEq.
  Qed.

  Lemma ieq_trans : forall Ξ ℓ A B C, IEq Ξ ℓ A B -> IEq Ξ ℓ B C -> IEq Ξ ℓ A C.
  Proof. sfirstorder use:ieq_trans_mutual. Qed.

  Lemma ieq_pi_inj Ξ ℓ ℓ0 A B A0 B0 :
    IEq Ξ ℓ (tPi ℓ0 A B) (tPi ℓ0 A0 B0) ->
    IEq Ξ ℓ A A0 /\ IEq (ℓ0 :: Ξ) ℓ B B0.
  Proof. qauto l:on inv:IEq. Qed.

  Definition ieq_weakening_helper : forall ℓ ξ (Ξ Δ : econtext),
      iok_ren_ok ξ Ξ Δ ->
      iok_ren_ok (upRen_tm_tm ξ) (ℓ :: Ξ) (ℓ :: Δ).
  Proof.
    move => ℓ0 ξ Ξ Δ h.
    rewrite /iok_ren_ok.
    case => //.
  Qed.

  Lemma ieq_weakening_mutual : forall Ξ ℓ,
      (forall a b, IEq Ξ ℓ a b ->
              forall ξ Δ, iok_ren_ok ξ Ξ Δ ->
                     IEq Δ ℓ (ren_tm ξ a) (ren_tm ξ b)) /\
        (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                   forall ξ Δ, iok_ren_ok ξ Ξ Δ ->
                          GIEq Δ ℓ ℓ0 (ren_tm ξ a) (ren_tm ξ b)).
  Proof.
    apply IEq_mutual; try qauto l: on ctrs:IEq,GIEq use:ieq_weakening_helper unfold:iok_ren_ok.
    move => *; constructor; first by sfirstorder.
  Qed.

Definition ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ :=
  forall i ℓ0, elookup i Ξ ℓ0 -> GIEq Δ ℓ ℓ0 (ξ0 i ) (ξ1 i).

Lemma gieq_refl n Ξ ℓ ℓ0 :
  elookup n Ξ ℓ0 ->
  GIEq Ξ ℓ ℓ0 (var_tm n) (var_tm n).
Proof.
  case : (sub_eqdec ℓ0 ℓ); hauto lq:on ctrs:IEq, GIEq.
Qed.

Lemma ieq_morphing_helper ℓ ℓ0 ξ0 ξ1 Ξ Δ :
  ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
  ieq_good_morphing ℓ (up_tm_tm ξ0) (up_tm_tm ξ1) (ℓ0 :: Ξ) (ℓ0 :: Δ).
Proof.
  rewrite /ieq_good_morphing => h.
  case => [|i] ℓ1 //=.
  - sfirstorder use:gieq_refl.
  - asimpl.
    sfirstorder use:ieq_weakening_mutual unfold:iok_ren_ok.
Qed.

Lemma ieq_morphing_helper2 ℓ ℓ0 ℓ1 ξ0 ξ1 Ξ Δ :
  ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
  ieq_good_morphing ℓ (up_tm_tm (up_tm_tm ξ0)) (up_tm_tm (up_tm_tm ξ1)) (ℓ1 :: (ℓ0 :: Ξ)) (ℓ1 :: (ℓ0 :: Δ)).
Proof. hauto lq:on use:ieq_morphing_helper. Qed.

Lemma ieq_morphing_mutual : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            IEq Δ ℓ (subst_tm ξ0 a) (subst_tm ξ1 b)) /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            GIEq Δ ℓ ℓ0 (subst_tm ξ0 a) (subst_tm ξ1 b)).
Proof.
  apply IEq_mutual; try qauto ctrs:IEq,GIEq.
  - hauto lq: on inv: GIEq lqb:on unfold:ieq_good_morphing.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper2.
  - hauto lq:on ctrs:GIEq unfold:ieq_good_morphing.
Qed.

Lemma ieq_morphing_iok Ξ Δ ℓ a b (h : IEq Ξ ℓ a b) ρ
  (hρ : forall i ℓ0, elookup i Ξ ℓ0 -> IOk Δ ℓ0 (ρ i)) :
  IEq Δ ℓ a[ρ] b[ρ].
Proof.
  sfirstorder use:ieq_morphing_mutual, iok_gieq unfold:ieq_good_morphing.
Qed.

Lemma gieq_morphing_iok Ξ Δ ℓ ℓ0 a b (h : GIEq Ξ ℓ ℓ0 a b) ρ
  (hρ : forall i ℓ0, elookup i Ξ ℓ0 -> IOk Δ ℓ0 (ρ i)) :
  GIEq Δ ℓ ℓ0 a[ρ] b[ρ].
Proof.
  sfirstorder use:ieq_morphing_mutual, iok_gieq unfold:ieq_good_morphing.
Qed.

Lemma ieq_downgrade_mutual : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ℓ0 c , IEq Ξ ℓ0 a c ->
                     IEq Ξ (ℓ ∩ ℓ0) a b) /\
      (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                 forall ℓ1 c, GIEq Ξ ℓ1 ℓ0 a c ->
                         GIEq Ξ (ℓ ∩ ℓ1) ℓ0 a b).
Proof.
  apply IEq_mutual; try qauto l:on inv:IEq,GIEq ctrs:IEq,GIEq.
  (* Can be compressed if I can figure out how to make ssreflect
  lemmas usable by automation *)
  - move => Ξ ℓ i ℓ0 hi hℓ ℓ1 c h.
    inversion h; subst.
    apply : I_Var; eauto.
    ltac2:(solve_lattice).
    sfirstorder.
  - move => Ξ ℓ ℓ0 a0 a1 b0 b1 A0 A1 ? ha iha hb ihb hA ihA ℓ1 ?.
    elim /IEq_inv=>// _ ? ? a2 ? b2 ? A2 ? ? ? ? [*]. subst.
    apply I_Eq.
    + ltac2:(solve_lattice); tauto.
    + sfirstorder.
    + sfirstorder.
    + sfirstorder.
  - move => Ξ ℓ ℓ0 A B ? h ih ℓ1 C.
    elim /GIEq_inv => hc ℓ2 A0 B0 h2 h3 *; subst.
    + apply ih in h3.
      apply GI_Dist => //.
      ltac2:(solve_lattice).
      tauto.
    + apply GI_InDist.
      move => h3.
      apply h2.
      ltac2:(solve_lattice).
      tauto.
  - move => Ξ ℓ ℓ0 A B h ℓ1 C h2.
    apply GI_InDist => ?.
    apply h.
    ltac2:(solve_lattice).
    tauto.
Qed.

Lemma ieq_trans_heterogeneous Ξ ℓ ℓ0 a b c :
  IEq Ξ ℓ a b ->
  IEq Ξ ℓ0 b c ->
  IEq Ξ (ℓ ∩ ℓ0) a c.
Proof.
  move => h0 h1.
  apply ieq_trans with (B := b).
  - apply ieq_sym_mutual.
    apply ieq_sym_mutual in h0.
    eapply ieq_downgrade_mutual; eauto.
  - apply ieq_sym_mutual in h0.
    rewrite meet_commutative.
    eapply ieq_downgrade_mutual; eauto.
Qed.

End geq_facts.
