From WR Require Import syntax join common.

(* #[export]Hint Unfold dep_ith : core. *)
Inductive Wt (Γ : context) : tm -> tm -> Prop :=
| T_Var i :
  Wff Γ ->
  i < length Γ ->
  (* ------ *)
  Wt Γ (var_tm i) (dep_ith Γ i)

| T_False i :
  Wff Γ ->
  (* -------- *)
  Wt Γ tFalse (tUniv i)

| T_Pi i A B :
  Wt Γ A (tUniv i) ->
  Wt (A :: Γ) B (tUniv i) ->
  (* --------------------- *)
  Wt Γ (tPi A B) (tUniv i)

| T_Abs A a B i :
  Wt Γ (tPi A B) (tUniv i) ->
  Wt (A :: Γ) a B ->
  (* -------------------- *)
  Wt Γ (tAbs A a) (tPi A B)

| T_App a A B b :
  Wt Γ a (tPi A B) ->
  Wt Γ b A ->
  (* -------------------- *)
  Wt Γ (tApp a b) (subst_tm (b..) B)

| T_Conv a A B i :
  Wt Γ a A ->
  Wt Γ B (tUniv i) ->
  Coherent A B ->
  (* ----------- *)
  Wt Γ a B

| T_On :
  Wff Γ ->
  (* --------- *)
  Wt Γ tOn tSwitch

| T_Off :
  Wff Γ ->
  (* --------- *)
  Wt Γ tOff tSwitch

| T_If a b c A :
  Wt Γ a tSwitch ->
  Wt Γ b A ->
  Wt Γ c A ->
  (* ------------ *)
  Wt Γ (tIf a b c) A

| T_Switch i :
  Wff Γ ->
  (* ----------- *)
  Wt Γ tSwitch (tUniv i)

| T_Univ i j :
  Wff Γ ->
  i < j ->
  (* ------------ *)
  Wt Γ (tUniv i) (tUniv j)

with Wff (Γ : context) : Prop :=
| Wff_intro F :
  (forall i, i < length Γ -> Wt (skipn (S i) Γ) (ith Γ i) (tUniv (F i))) ->
  (* ---------------------------------------------------------------- *)
  Wff Γ.

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.
