From WR Require Import syntax join common.

Module Type typing_sig
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade)
  (Import common : common_sig grade syntax)
  (Import join : join_sig grade syntax common).

Inductive Wt (Γ : context) (Ξ : econtext) : grade -> tm -> tm -> Prop :=
| T_Var ℓ i :
  Wff Γ Ξ ->
  i < length Γ ->
  (* ------ *)
  Wt Γ Ξ ℓ (var_tm i) (dep_ith Γ i)

| T_False ℓ i :
  Wff Γ Ξ ->
  (* -------- *)
  Wt Γ Ξ ℓ tFalse (tUniv i)

| T_Pi ℓ ℓ0 i A B :
  Wt Γ Ξ ℓ A (tUniv i) ->
  Wt (A :: Γ) (ℓ0 :: Ξ) ℓ B (tUniv i) ->
  (* --------------------- *)
  Wt Γ Ξ ℓ (tPi ℓ0 A B) (tUniv i)

| T_Abs ℓ ℓ0 ℓ1 A a B i :
  Wt Γ Ξ ℓ1 (tPi ℓ0 A B) (tUniv i) ->
  Wt (A :: Γ) (ℓ0 :: Ξ) ℓ a B ->
  (* -------------------- *)
  Wt Γ Ξ ℓ (tAbs ℓ0 A a) (tPi ℓ0 A B)

| T_App ℓ ℓ0 a A B b :
  Wt Γ Ξ ℓ a (tPi ℓ0 A B) ->
  Wt Γ Ξ ℓ0 b A ->
  (* -------------------- *)
  Wt Γ Ξ ℓ (tApp a ℓ0 b) (subst_tm (b..) B)

| T_Conv ℓ ℓ1 a A B i :
  Wt Γ Ξ ℓ a A ->
  Wt Γ Ξ ℓ1 B (tUniv i) ->
  icoherent Ξ A B ->
  (* ----------- *)
  Wt Γ Ξ ℓ a B

| T_On ℓ :
  Wff Γ Ξ ->
  (* --------- *)
  Wt Γ Ξ ℓ tOn tSwitch

| T_Off ℓ :
  Wff Γ Ξ ->
  (* --------- *)
  Wt Γ Ξ ℓ tOff tSwitch

| T_If ℓ a b c A :
  Wt Γ Ξ ℓ a tSwitch ->
  Wt Γ Ξ ℓ b A ->
  Wt Γ Ξ ℓ c A ->
  (* ------------ *)
  Wt Γ Ξ ℓ (tIf a b c) A

| T_Switch ℓ i :
  Wff Γ Ξ ->
  (* ----------- *)
  Wt Γ Ξ ℓ tSwitch (tUniv i)

| T_Univ ℓ i j :
  Wff Γ Ξ ->
  i < j ->
  (* ------------ *)
  Wt Γ Ξ ℓ (tUniv i) (tUniv j)

with Wff (Γ : context) (Ξ : econtext) : Prop :=
| Wff_intro F G :
  length Γ = length Ξ ->
  (forall i, i < length Γ -> Wt (skipn (S i) Γ) (skipn (S i) Ξ) (G i) (ith Γ i) (tUniv (F i))) ->
  (* ---------------------------------------------------------------- *)
  Wff Γ Ξ.

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.

End typing_sig.
