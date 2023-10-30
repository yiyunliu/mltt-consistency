From WR Require Import syntax join.
From Coq Require Import ssreflect.

Definition context := nat -> tm.

Definition dep_ith (Γ : context) (x : fin) :=
  ren_tm (Nat.add (S x)) (Γ x).

Lemma dep_ith_ren_tm (Γ : context) (A : tm) (x : fin) :
  dep_ith (A .: Γ) (S x) = ren_tm shift (dep_ith Γ x).
Proof.
  case : x => [|x].
  - rewrite /dep_ith; asimpl.
    reflexivity.
  - rewrite /dep_ith.
    asimpl.
    f_equal.
Qed.

#[export]Hint Unfold dep_ith : core.

Tactic Notation "asimpldep" := repeat (progress ((try (rewrite dep_ith_ren_tm));rewrite /dep_ith; asimpl)).

Inductive Wt (n : nat) (Γ : context) : tm -> tm -> Prop :=
| T_Var i :
  Wff n Γ ->
  i < n ->
  (* ------ *)
  Wt n Γ (var_tm i) (dep_ith Γ i)

| T_False i :
  Wff n Γ ->
  (* -------- *)
  Wt n Γ tFalse (tUniv i)

| T_Pi i A B :
  Wt n Γ A (tUniv i) ->
  Wt (S n) (A .: Γ) B (tUniv i) ->
  (* --------------------- *)
  Wt n Γ (tPi A B) (tUniv i)

| T_Abs A a B i :
  Wt n Γ (tPi A B) (tUniv i) ->
  Wt (S n) (A .: Γ) a B ->
  (* -------------------- *)
  Wt n Γ (tAbs A a) (tPi A B)

| T_App a A B b :
  Wt n Γ a (tPi A B) ->
  Wt n Γ b A ->
  (* -------------------- *)
  Wt n Γ (tApp a b) (subst_tm (b..) B)

| T_Conv a A B i :
  Wt n Γ a A ->
  Wt n Γ B (tUniv i) ->
  Join A B ->
  (* ----------- *)
  Wt n Γ a B

| T_On :
  Wff n Γ ->
  (* --------- *)
  Wt n Γ tOn tSwitch

| T_Off :
  Wff n Γ ->
  (* --------- *)
  Wt n Γ tOff tSwitch

| T_If a b c A :
  Wt n Γ a tSwitch ->
  Wt n Γ b A ->
  Wt n Γ c A ->
  (* ------------ *)
  Wt n Γ (tIf a b c) A

| T_Switch i :
  Wff n Γ ->
  (* ----------- *)
  Wt n Γ tSwitch (tUniv i)

| T_Univ i j :
  Wff n Γ ->
  i < j ->
  (* ------------ *)
  Wt n Γ (tUniv i) (tUniv j)

with Wff (n : nat) (Γ : context) : Prop :=
(* The arithmetic is needed because of the types in the context are scoped differently *)
(* Need to skolemize the existential as F because otherwise the IH is unusable *)
| Wff_intro F :
  (forall i, i < n -> Wt (n - S i) (Nat.add (S i) >> Γ) (Γ i) (tUniv (F i))) ->
  (* ---------------------------------------------------------------- *)
  Wff n Γ.

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.
