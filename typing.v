From WR Require Import syntax join common.

Reserved Notation "'⊢' Γ" (at level 10, no associativity).
Reserved Notation "Γ '⊢' a '∈' A" (at level 70, no associativity).
Inductive Wt (Γ : context) : tm -> tm -> Prop :=
| T_Var i :
  ⊢ Γ ->
  i < length Γ ->
  (* ------ *)
  Γ ⊢ var_tm i ∈ dep_ith Γ i

| T_False i :
  ⊢ Γ ->
  (* -------- *)
  Γ ⊢ tFalse ∈ tUniv i

| T_Pi i A B :
  Γ ⊢ A ∈ tUniv i ->
  A :: Γ ⊢ B ∈ tUniv i ->
  (* --------------------- *)
  Γ ⊢ tPi A B ∈ tUniv i

| T_Abs A a B i :
  Γ ⊢ tPi A B ∈ tUniv i ->
  A :: Γ ⊢ a ∈ B ->
  (* -------------------- *)
  Wt Γ (tAbs A a) (tPi A B)

| T_App a A B b :
  Γ ⊢ a ∈ tPi A B ->
  Γ ⊢ b ∈ A ->
  (* -------------------- *)
  Γ ⊢ tApp a b ∈ subst_tm (b..) B

| T_Conv a A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ B ∈ tUniv i ->
  Join A B ->
  (* ----------- *)
  Γ ⊢ a ∈ B

| T_On :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ tOn ∈ tSwitch

| T_Off :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ tOff ∈ tSwitch

| T_If a b c A :
  Γ ⊢ a ∈ tSwitch ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ c ∈ A ->
  (* ------------ *)
  Γ ⊢ tIf a b c ∈ A

| T_Switch i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ tSwitch ∈ tUniv i

| T_Univ i j :
  ⊢ Γ ->
  i < j ->
  (* ------------ *)
  Γ ⊢ tUniv i ∈ tUniv j
where "'⊢' Γ" := (exists F, forall i, i < length Γ -> Wt (skipn (S i) Γ) (ith Γ i) (tUniv (F i)))
and "Γ '⊢' a '∈' A" := (Wt Γ a A).
