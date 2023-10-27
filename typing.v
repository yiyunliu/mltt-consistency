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

Tactic Notation "asimpldep" := repeat (progress (rewrite /dep_ith; asimpl)).

Inductive Wt (n : nat) (Γ : context) : tm -> tm -> Prop :=
| T_Var i :
  (* This mess is the wff condition *)
  (forall j, j < n -> UWf (n - S j) (Nat.add (S j) >> Γ) (Γ j)) ->
  i < n ->
  (* ------ *)
  Wt n Γ (var_tm i) (dep_ith Γ i)
| T_False :
  (* -------- *)
  Wt n Γ tFalse tUniv
| T_Pi A B :
  Wt n Γ A tUniv ->
  Wt (S n) (A .: Γ) B tUniv ->
  (* --------------------- *)
  Wt n Γ (tPi A B) tUniv
| T_Abs A a B :
  UWf n Γ A ->
  Wt (S n) (A .: Γ) a B ->
  (* -------------------- *)
  Wt n Γ (tAbs A a) (tPi A B)
| T_App a A B b :
  Wt n Γ a (tPi A B) ->
  Wt n Γ b A ->
  (* -------------------- *)
  Wt n Γ (tApp a b) (subst_tm (b..) B)
| T_Conv a A B :
  Wt n Γ a A ->
  UWf n Γ B ->
  Join A B ->
  (* ----------- *)
  Wt n Γ a B
with UWf (n : nat) (Γ : context) : tm -> Prop :=
| U_Univ :
  UWf n Γ tUniv
| U_False :
  UWf n Γ tFalse
| U_Pi A B :
  UWf n Γ A ->
  UWf (S n) (A .: Γ) B ->
  UWf n Γ (tPi A B)
| U_Embed A :
  Wt n Γ A tUniv ->
  UWf n Γ A.

Definition Wff n Γ := forall j, j < n -> UWf (n - S j) (Nat.add (S j) >> Γ) (Γ j).


Scheme Wt_ind' := Induction for Wt Sort Prop
  with UWf_ind' := Induction for UWf Sort Prop.

Combined Scheme Wt_mutual from Wt_ind', UWf_ind'.
