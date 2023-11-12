From WR Require Import syntax join.
From Coq Require Import ssreflect.

Definition context := list tm.

Fixpoint dep_ith (Γ : context) : nat -> option tm :=
  match Γ with
  | nil => fun i => None
  | A::Γ => fun i => option_map (ren_tm shift)
            match i with
            | 0 => Some A
            | S i => dep_ith Γ i
            end
  end.

Lemma dep_ith_ren_tm (Γ : context) (A : tm) (x : fin) :
  dep_ith (A :: Γ) (S x) = option_map (ren_tm shift) (dep_ith Γ x).
Proof. done. Qed.

Lemma dep_ith_shift_n (Γ : context) i :
  dep_ith Γ i = option_map (ren_tm (Nat.add (S i))) (nth_error Γ i).
Proof.
  elim : Γ i.
  - destruct i; reflexivity.
  - move => a l ih [|i] //.
    simpl.
    rewrite ih.
    destruct (nth_error l i) => /=; by asimpl.
Qed.

Lemma dep_ith_ren_tm0 (Γ : context) (A : tm) :
  dep_ith (A :: Γ) 0 = Some (ren_tm shift A).
Proof. reflexivity. Qed.

(* #[export]Hint Unfold dep_ith : core. *)
Inductive Wt (Γ : context) : tm -> tm -> Prop :=
| T_Var i A :
  Wff Γ ->
  dep_ith Γ i = Some A ->
  (* ------ *)
  Wt Γ (var_tm i) A

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
  Join A B ->
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
  (forall i A, nth_error Γ i = Some A -> Wt (skipn (S i) Γ) A (tUniv (F i))) ->
  (* ---------------------------------------------------------------- *)
  Wff Γ.

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.
