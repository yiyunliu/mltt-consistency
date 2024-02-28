From WR Require Import imports join.

Definition context := list tm.

Inductive lookup : nat -> context -> tm -> Prop :=
  | here : forall {A Γ}, lookup 0 (A :: Γ) (A ⟨shift⟩)
  | there : forall {n A Γ B},
      lookup n Γ A -> lookup (S n) (B :: Γ) (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i A, lookup i Γ A -> lookup (ξ i) Δ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).

Inductive Wt : context -> tm -> tm -> Prop :=
| T_Var Γ i A :
  ⊢ Γ ->
  lookup i Γ A ->
  (* ------ *)
  Γ ⊢ (var_tm i) ∈ A

| T_Void Γ i :
  ⊢ Γ ->
  (* -------- *)
  Γ ⊢ tVoid ∈ (tUniv i)

| T_Pi Γ i A B :
  Γ ⊢ A ∈ (tUniv i) ->
  (A :: Γ) ⊢ B ∈ (tUniv i) ->
  (* --------------------- *)
  Γ ⊢ (tPi A B) ∈ (tUniv i)

| T_Abs Γ A a B i :
  Γ ⊢ (tPi A B) ∈ (tUniv i) ->
  (A :: Γ) ⊢ a ∈ B ->
  (* -------------------- *)
  Γ ⊢ (tAbs a) ∈ (tPi A B)

| T_App Γ a A B b :
  Γ ⊢ a ∈ (tPi A B) ->
  Γ ⊢ b ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a b) ∈ (B [ b.. ])

| T_Conv Γ a A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ B ∈ (tUniv i) ->
  Coherent A B ->
  (* ----------- *)
  Γ ⊢ a ∈ B

| T_True Γ :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ tTrue ∈ tBool

| T_False Γ :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ tFalse ∈ tBool

| T_If Γ a b c A i :
  (tBool :: Γ) ⊢ A ∈ (tUniv i) ->
  Γ ⊢ a ∈ tBool ->
  Γ ⊢ b ∈ (A [tTrue..]) ->
  Γ ⊢ c ∈ (A [tFalse..]) ->
  (* ------------ *)
  Γ ⊢ (tIf a b c) ∈ (A [a..])

| T_Bool Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ tBool ∈ (tUniv i)

| T_Univ Γ i :
  ⊢ Γ ->
  (* ------------ *)
  Γ ⊢ (tUniv i) ∈ (tUniv (S i))

| T_Refl Γ a A:
  ⊢ Γ ->
  Γ ⊢ a ∈ A ->
  (* ------ *)
  Γ ⊢ tRefl ∈ (tEq a a A)

| T_Eq Γ a b A i j :
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ A ∈ (tUniv j) ->
  (* ----------------------- *)
  Γ ⊢ (tEq a b A) ∈ (tUniv i)

| T_J Γ t a b p A i j C : 
  Γ ⊢ a ∈  A ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ A ∈ (tUniv j) ->
  Γ ⊢ p ∈ (tEq a b A) ->
  (tEq (ren_tm shift a) (var_tm 0) (ren_tm shift A) :: A :: Γ) ⊢ C ∈ (tUniv i) ->
  Γ ⊢ t ∈ (C [tRefl .: a ..]) ->
  Γ ⊢ (tJ t a b p) ∈ (C [p .: b..])

with Wff : context -> Prop :=
| Wff_nil :
(* ----------------- *)
  ⊢ nil
| Wff_cons Γ A i :
  ⊢ Γ ->
  Γ ⊢ A ∈ tUniv i ->
(* ----------------- *)
  ⊢ A :: Γ
where 
  "Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wff Γ).


Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.
