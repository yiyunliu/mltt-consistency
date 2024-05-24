Require Import imports.

Module Type geq_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

  Definition econtext := list T.
  Open Scope lattice_scope.

  Definition elookup i Ξ (ℓ : T) := nth_error Ξ i = Some ℓ.

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

  #[export]Hint Constructors IEq GIEq : ieq.

  Scheme IEq_ind' := Induction for IEq Sort Prop
      with GIEq_ind' := Induction for GIEq Sort Prop.

  Combined Scheme IEq_mutual from IEq_ind', GIEq_ind'.

  Derive Inversion IEq_inv with (forall Ξ ℓ a b, IEq Ξ ℓ a b).
  Derive Inversion GIEq_inv with (forall Ξ ℓ ℓ0 a b, GIEq Ξ ℓ ℓ0 a b).

End geq_sig.


Module geq_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import geq : geq_sig lattice syntax).

  Module lprop :=  Lattice.All.Properties lattice.
  Import lprop.
  Module solver  :=  Solver lattice.
  Import solver.

  Lemma ieq_sym_mutual : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A) /\
        (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> GIEq Ξ ℓ ℓ0 B A).
  Proof.
    apply IEq_mutual; eauto with ieq.
  Qed.

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

  Definition ieq_good_renaming ξ (Ξ Δ : econtext) :=
    (forall i ℓ0, elookup i Ξ ℓ0 -> elookup (ξ i) Δ ℓ0).

  Definition ieq_weakening_helper : forall ℓ ξ (Ξ Δ : econtext),
      ieq_good_renaming ξ Ξ Δ ->
      ieq_good_renaming (upRen_tm_tm ξ) (ℓ :: Ξ) (ℓ :: Δ).
  Proof.
    move => ℓ0 ξ Ξ Δ h.
    rewrite /ieq_good_renaming.
    case => //.
  Qed.

  Lemma ieq_weakening_mutual : forall Ξ ℓ,
      (forall a b, IEq Ξ ℓ a b ->
              forall ξ Δ, ieq_good_renaming ξ Ξ Δ ->
                     IEq Δ ℓ (ren_tm ξ a) (ren_tm ξ b)) /\
        (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                   forall ξ Δ, ieq_good_renaming ξ Ξ Δ ->
                          GIEq Δ ℓ ℓ0 (ren_tm ξ a) (ren_tm ξ b)).
  Proof.
    apply IEq_mutual; try qauto l: on ctrs:IEq,GIEq use:ieq_weakening_helper unfold:ieq_good_renaming.
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
    sfirstorder use:ieq_weakening_mutual unfold:ieq_good_renaming.
Qed.

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
  - hauto lq:on ctrs:GIEq unfold:ieq_good_morphing.
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

End geq_facts.
