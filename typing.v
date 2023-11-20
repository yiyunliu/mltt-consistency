From WR Require Export common join.

Module Type typing_sig
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade)
  (Import common : common_sig grade syntax)
  (Import join : join_sig grade syntax common).

Inductive Wt (Γ : context) : grade -> tm -> tm -> Prop :=
| T_Var ℓ i :
  Wff Γ ->
  i < size Γ ->
  (eith (unzip1 Γ) i <= ℓ)%O ->
  (* ------ *)
  Wt Γ ℓ (var_tm i) (dep_ith (unzip2 Γ) i)

| T_False ℓ i :
  Wff Γ ->
  (* -------- *)
  Wt Γ ℓ tFalse (tUniv i)

| T_Pi ℓ ℓ0 i A B :
  Wt Γ ℓ A (tUniv i) ->
  Wt ((ℓ0, A) :: Γ) ℓ B (tUniv i) ->
  (* --------------------- *)
  Wt Γ ℓ (tPi ℓ0 A B) (tUniv i)

| T_Abs ℓ ℓ0 ℓ1 A a B i :
  Wt Γ ℓ1 (tPi ℓ0 A B) (tUniv i) ->
  Wt ((ℓ0, A) :: Γ) ℓ a B ->
  (* -------------------- *)
  Wt Γ ℓ (tAbs ℓ0 A a) (tPi ℓ0 A B)

| T_App ℓ ℓ0 a A B b :
  Wt Γ ℓ a (tPi ℓ0 A B) ->
  Wt Γ ℓ0 b A ->
  (* -------------------- *)
  Wt Γ ℓ (tApp a ℓ0 b) (subst_tm (b..) B)

| T_Conv ℓ ℓ1 a A B i :
  Wt Γ ℓ a A ->
  Wt Γ ℓ1 B (tUniv i) ->
  icoherent (unzip1 Γ) A B ->
  (* ----------- *)
  Wt Γ ℓ a B

| T_On ℓ :
  Wff Γ ->
  (* --------- *)
  Wt Γ ℓ tOn tSwitch

| T_Off ℓ :
  Wff Γ ->
  (* --------- *)
  Wt Γ ℓ tOff tSwitch

| T_If ℓ a b c A :
  Wt Γ ℓ a tSwitch ->
  Wt Γ ℓ b A ->
  Wt Γ ℓ c A ->
  (* ------------ *)
  Wt Γ ℓ (tIf a b c) A

| T_Switch ℓ i :
  Wff Γ ->
  (* ----------- *)
  Wt Γ ℓ tSwitch (tUniv i)

| T_Univ ℓ i j :
  Wff Γ ->
  i < j ->
  (* ------------ *)
  Wt Γ ℓ (tUniv i) (tUniv j)

with Wff (Γ : context) : Prop :=
| Wff_intro F G :
  (forall i, i < length Γ -> Wt (drop (S i) Γ) (G i) (ith (unzip2 Γ) i) (tUniv (F i))) ->
  (* ---------------------------------------------------------------- *)
  Wff Γ.

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.

End typing_sig.
