Require Import imports.

Module Type geq_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

  Definition econtext := list T.
  Open Scope lattice_scope.

  Definition elookup i Ξ (ℓ : T) := nth_error Ξ i = Some ℓ.

  Inductive IEq (Ξ : econtext) (ℓ : T) : tm -> tm -> Prop :=
  | I_Var i ℓ0 :
    elookup i Ξ ℓ ->
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

End geq_sig.


Module geq_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import geq : geq_sig lattice syntax).

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

End geq_facts.
