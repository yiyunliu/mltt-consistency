Require Import imports.

Definition context := list tm.

Inductive lookup : nat -> context -> tm -> Prop :=
  | here : forall {A Γ}, lookup 0 (A :: Γ) (A ⟨shift⟩)
  | there : forall {n A Γ B},
      lookup n Γ A -> lookup (S n) (B :: Γ) (A ⟨shift⟩).

Definition ren_ok ξ Γ Δ :=
  forall i A, lookup i Γ A -> lookup (ξ i) Δ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

Reserved Notation "Γ ⊢ a ∈ A" (at level 70, no associativity).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70, no associativity).
Reserved Notation "⊢ Γ" (at level 70, no associativity).

Inductive Wt : context -> tm -> tm -> Prop :=
| T_Var Γ i A :
  ⊢ Γ ->
  lookup i Γ A ->
  (* ------ *)
  Γ ⊢ (var_tm i) ∈ A

| T_Pi Γ i A B :
  Γ ⊢ A ∈ (tUniv i) ->
  (A :: Γ) ⊢ B ∈ (tUniv i) ->
  (* --------------------- *)
  Γ ⊢ (tPi A B) ∈ (tUniv i)

| T_Abs Γ A a B i :
  Γ ⊢ (tPi A B) ∈ (tUniv i) ->
  Γ ⊢ A ∈ tUniv i ->
  (A :: Γ) ⊢ a ∈ B ->
  (* -------------------- *)
  Γ ⊢ (tAbs A a) ∈ (tPi A B)

| T_App Γ a A B b :
  Γ ⊢ a ∈ (tPi A B) ->
  Γ ⊢ b ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a b) ∈ (B [ b.. ])

| T_Conv Γ a A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ tUniv i ->
  (* ----------- *)
  Γ ⊢ a ∈ B

| T_Univ Γ i j :
  ⊢ Γ ->
  i < j ->
  (* ------------ *)
  Γ ⊢ (tUniv i) ∈ (tUniv j)

with Equiv : context -> tm -> tm -> tm -> Prop :=
| E_Var Γ i A :
  ⊢ Γ ->
  lookup i Γ A ->
  (* ------ *)
  Γ ⊢ var_tm i ≡ var_tm i ∈ A

| E_Sym Γ a b A :
  Γ ⊢ a ≡ b ∈ A ->
  (* ----------- *)
  Γ ⊢ b ≡ a ∈ A

| E_Trans Γ a b c A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ c ∈ A ->
  (* ----------- *)
  Γ ⊢ a ≡ c ∈ A

| E_Pi Γ i A0 B0 A1 B1 :
  Γ ⊢ A0 ≡ A1 ∈ tUniv i ->
  A0 :: Γ ⊢ B0 ≡ B1 ∈ tUniv i ->
  Γ ⊢ A0 ∈ tUniv i ->
  (* --------------------- *)
  Γ ⊢ tPi A0 B0 ≡ tPi A1 B1 ∈ tUniv i

| E_Abs Γ A0 A1 a0 a1 B i :
  Γ ⊢ A0 ≡ A1 ∈ tUniv i ->
  Γ ⊢ A0 ∈ tUniv i ->
  Γ ⊢ tPi A0 B ≡ tPi A1 B ∈ tUniv i ->
  A0 :: Γ ⊢ a0 ≡ a1 ∈ B ->
  (* -------------------- *)
  Γ ⊢ tAbs A0 a0 ≡ tAbs A1 a1 ∈ tPi A0 B

| E_App Γ a0 b0 a1 b1 A B :
  Γ ⊢ b0 ≡ b1 ∈ tPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ tApp b1 a1 ∈ B[a0..] ->
  (* ----------------- *)
  Γ ⊢ tApp b0 a0 ≡ tApp b1 a1 ∈ B[a0..]

| E_Beta Γ A B a b i :
  Γ ⊢ tPi A B ∈ tUniv i ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp (tAbs A b) a ≡ b[a..] ∈ B[a..]

| E_Univ Γ i j :
  ⊢ Γ ->
  i < j ->
  (* ------------ *)
  Γ ⊢ tUniv i ≡ tUniv i ∈ tUniv j

| E_Conv Γ a b A B i :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≡ B ∈ tUniv i ->
  (* ----------- *)
  Γ ⊢ a ≡ b ∈ B

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
  "Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wff Γ) and
  "Γ ⊢ a ≡ b ∈ A" := (Equiv Γ a b A).

Scheme wt_ind := Induction for Wt Sort Prop
    with equiv_ind := Induction for Equiv Sort Prop.

Combined Scheme wt_mutual from wt_ind, equiv_ind.

Reserved Notation "Γ ⊢ a ⤳ b ∈ A" (at level 70, no associativity).
Inductive Red Γ : tm -> tm -> tm -> Prop :=
| R_App b0 b1 a A B :
  Γ ⊢ b0 ⤳ b1 ∈ tPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp b0 a ⤳ tApp b1 a ∈ B[a..]
| R_Beta A B a b i :
  Γ ⊢ tPi A B ∈ tUniv i ->
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ tApp (tAbs A b) a ⤳ b[a..] ∈ B[a..]
| R_Conv a b A B i :
  Γ ⊢ a ⤳ b ∈ A ->
  Γ ⊢ A ≡ B ∈ tUniv i ->
  (* ----------- *)
  Γ ⊢ a ⤳ b ∈ B
where  "Γ ⊢ a ⤳ b ∈ A" := (Red Γ a b A).

Reserved Notation "Γ ⊢ a ⤳* b ∈ A" (at level 70, no associativity).
Inductive Reds Γ a : tm -> tm -> Prop :=
| R_Refl A :
  Γ ⊢ a ∈ A ->
  Γ ⊢ a ⤳* a ∈ A
| R_Step b c A :
  Γ ⊢ a ⤳ b ∈ A ->
  Γ ⊢ b ⤳* c ∈ A ->
  (* ----------- *)
  Γ ⊢ a ⤳* c ∈ A
where "Γ ⊢ a ⤳* b ∈ A" := (Reds Γ a b A).
