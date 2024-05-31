Require Import imports par geq conv syntax.

Module Type typing_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq).

Definition context := list (T * tm).

Inductive lookup : nat -> context -> T -> tm -> Prop :=
  | here ℓ A Γ : lookup 0 ((ℓ, A) :: Γ) ℓ (A ⟨shift⟩)
  | there n A Γ ℓ B :
      lookup n Γ ℓ A -> lookup (S n) (B :: Γ) ℓ (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i ℓ A, lookup i Γ ℓ A -> lookup (ξ i) Δ ℓ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ ℓ A, lookup i Γ ℓ A).

Reserved Notation "Γ ⊢ a ; ℓ ∈ A" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).

Definition c2e : context -> econtext := map (fun '(ℓ, _) => ℓ).

Inductive Wt : context -> T -> tm -> tm -> Prop :=
| T_Var Γ ℓ0 ℓ i A :
  ⊢ Γ ->
  lookup i Γ ℓ0 A ->
  ℓ0 ⊆ ℓ ->
  (* ------ *)
  Γ ⊢ (var_tm i) ; ℓ ∈ A

| T_Pi Γ i ℓ ℓ0 A B :
  Γ ⊢ A ; ℓ ∈ (tUniv i) ->
  ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv i) ->
  (* --------------------- *)
  Γ ⊢ (tPi ℓ0 A B) ; ℓ ∈ (tUniv i)

| T_Abs Γ ℓ ℓ0 ℓ1 A a B i :
  Γ ⊢ (tPi ℓ0 A B) ; ℓ1 ∈ (tUniv i) ->
  ((ℓ0, A) :: Γ) ⊢ a ; ℓ ∈ B ->
  (* -------------------- *)
  Γ ⊢ (tAbs ℓ0 a) ; ℓ ∈ (tPi ℓ0 A B)

| T_App Γ ℓ ℓ0 a A B b :
  Γ ⊢ a ; ℓ ∈ (tPi ℓ0 A B) ->
  Γ ⊢ b ; ℓ0 ∈ A ->
  (* -------------------- *)
  Γ ⊢ (tApp a ℓ0 b) ; ℓ ∈ (B [ b.. ])

| T_Conv Γ ℓ ℓ0 a A B i :
  Γ ⊢ a ; ℓ ∈ A ->
  Γ ⊢ B ; ℓ0 ∈ (tUniv i) ->
  conv (c2e Γ) A B ->
  (* ----------- *)
  Γ ⊢ a ; ℓ ∈ B

(* | T_Zero Γ : *)
(*   ⊢ Γ -> *)
(*   (* --------- *) *)
(*   Γ ⊢ tZero ∈ tNat *)

(* | T_Suc Γ a : *)
(*   Γ ⊢ a ∈ tNat -> *)
(*   ⊢ Γ -> *)
(*   (* --------- *) *)
(*   Γ ⊢ tSuc a ∈ tNat *)

(* | T_Ind Γ a b c A i : *)
(*   tNat :: Γ ⊢ A ∈ tUniv i -> *)
(*   Γ ⊢ a ∈ A [tZero..] -> *)
(*   A :: tNat :: Γ ⊢ b ∈ A[tSuc (var_tm 0) .: S >> var_tm]⟨S⟩ -> *)
(*   Γ ⊢ c ∈ tNat -> *)
(*   (* ------------ *) *)
(*   Γ ⊢ tInd a b c ∈ (A [c..]) *)

(* | T_Nat Γ i : *)
(*   ⊢ Γ -> *)
(*   (* ----------- *) *)
(*   Γ ⊢ tNat ∈ (tUniv i) *)

| T_Univ Γ ℓ i :
  ⊢ Γ ->
  (* ------------ *)
  Γ ⊢ (tUniv i) ; ℓ ∈ (tUniv (S i))

| T_Void Γ ℓ i :
  ⊢ Γ ->
  (* ------------ *)
  Γ ⊢ tVoid ; ℓ ∈ tUniv i

| T_Absurd Γ ℓ ℓ0 ℓ1 i a A :
  Γ ⊢ a ; ℓ0 ∈ tVoid  ->
  Γ ⊢ A ; ℓ1 ∈ tUniv i ->
  (* -------------- *)
  Γ ⊢ tAbsurd a ; ℓ ∈ A

| T_Refl Γ a ℓ0 A:
  ⊢ Γ ->
  Γ ⊢ a ; ℓ0 ∈ A ->
  (* ------ *)
  Γ ⊢ tRefl ∈ (tEq ℓ0 a a A)

| T_Eq Γ ℓ ℓ0 a b A i j :
  ℓ0 ⊆ ℓ ->
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b ; ℓ0 ∈ A ->
  Γ ⊢ A ; ℓ ∈ (tUniv j) ->
  (* ----------------------- *)
  Γ ⊢ (tEq ℓ0 a b A) ; ℓ ∈ (tUniv i)

| T_J Γ t a b p A i j C ℓ ℓp ℓA ℓ0 ℓ1:
  ℓp ⊆ ℓ ->
  ℓ0 ⊆ ℓC ->
  Γ ⊢ a ; ℓ1 ∈ A ->
  Γ ⊢ b ; ℓ1 ∈ A ->
  Γ ⊢ A ; ℓA ∈ (tUniv j) ->
  Γ ⊢ p ; ℓp ∈ (tEq ℓ0 a b A) ->
  ((ℓp, tEq ℓ0 (ren_tm shift a) (var_tm 0) (ren_tm shift A)) :: (ℓ1, A) :: Γ) ⊢ C ; ℓC ∈ (tUniv i) ->
  Γ ⊢ t ; ℓ ∈ (C [tRefl .: a ..]) ->
  Γ ⊢ (tJ C t p) ; ℓ ∈ (C [p .: b..])

(* | T_Sig Γ i A B : *)
(*   Γ ⊢ A ∈ (tUniv i) -> *)
(*   (A :: Γ) ⊢ B ∈ (tUniv i) -> *)
(*   (* --------------------- *) *)
(*   Γ ⊢ (tSig A B) ∈ (tUniv i) *)

(* | T_Pack Γ a A b B i : *)
(*   Γ ⊢ a ∈ A -> *)
(*   Γ ⊢ b ∈ B[a..] -> *)
(*   Γ ⊢ tSig A B ∈ tUniv i -> *)
(*   (* -------------------- *) *)
(*   Γ ⊢ tPack a b ∈ tSig A B *)

(* | T_Let Γ a b A B C i j : *)
(*   Γ ⊢ A ∈ tUniv j -> *)
(*   A :: Γ ⊢ B ∈ tUniv j -> *)
(*   Γ ⊢ a ∈ tSig A B -> *)
(*   B :: A :: Γ ⊢ b ∈ C[(tPack (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] -> *)
(*   tSig A B :: Γ ⊢ C ∈ tUniv i -> *)
(*   (* ----------------------- *) *)
(*   Γ ⊢ tLet a b ∈ C[a ..] *)

with Wff : context -> Prop :=
| Wff_nil :
(* ----------------- *)
  ⊢ nil
| Wff_cons Γ ℓ0 ℓ A i :
  ⊢ Γ ->
  Γ ⊢ A ; ℓ ∈ tUniv i ->
(* ----------------- *)
  ⊢ (ℓ0, A) :: Γ
where 
  "Γ ⊢ a ; ℓ ∈ A" := (Wt Γ ℓ a A) and "⊢ Γ" := (Wff Γ).


Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.
End typing_sig.
