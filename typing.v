From WR Require Import syntax join.
From Coq Require Vectors.Vector.
From Coq Require Import Logic.StrictProp.
Module V := Vectors.Vector.

Notation "[[ ]]" := (nil _) (format "[[ ]]").
Notation "h ::: t" := (V.cons _ h _ t) (at level 60, right associativity).

Definition context n := V.t tm n.

Definition dep_ith {n x : fin} (Γ : context n) (p : Squash (x < n)) : tm.
  generalize dependent x.
  induction Γ as [|q ? ? rec].
  - intros x p.
    apply sEmpty_rect.
    inversion p as [p0].
    apply False_sind.
    apply PeanoNat.Nat.nlt_0_r in p0.
    assumption.
  - destruct x as [|x].
    + intros ?. exact (ren_tm shift q).
    + intros p.
      apply (ren_tm shift).
      apply rec with (x := x).
      inversion p as [p0].
      apply Arith_prebase.lt_S_n in p0.
      exact (squash p0).
Defined.

(* Lemma dep_ith_ren_tm {n x} (Γ : context n) (A : tm)  (p : x < n) : *)
(*   dep_ith (V.cons _ A _ Γ) (squash (le_n_S _ _ p)) = ren_tm shift (dep_ith Γ (squash p)). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma dep_ith_ren_tm0 {x n} (Γ : context n) (p : Squash (x < n)) (A : tm) : *)
(*   dep_ith (V.cons _ A _ Γ) 0 = ren_tm shift A. *)
(* Proof. *)
(*   by rewrite /dep_ith; asimpl. *)
(* Qed. *)

#[export]Hint Unfold dep_ith : core.

(* Tactic Notation "asimpldep" := repeat (progress ((try (rewrite dep_ith_ren_tm));rewrite /dep_ith; asimpl)). *)

Inductive Wt {n} (Γ : context n) : tm -> tm -> Prop :=
| T_Var i (h : i < n) :
  (* Wff Γ -> *)
  (* ------ *)
  Wt Γ (var_tm i) (dep_ith Γ (squash h))

| T_False i :
  (* Wff Γ -> *)
  (* -------- *)
  Wt Γ tFalse (tUniv i)

| T_Pi i A B :
  Wt Γ A (tUniv i) ->
  Wt (A ::: Γ) B (tUniv i) ->
  (* --------------------- *)
  Wt Γ (tPi A B) (tUniv i)

| T_Abs A a B i :
  Wt Γ (tPi A B) (tUniv i) ->
  Wt (A ::: Γ) a B ->
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
  (* Wff Γ -> *)
  (* --------- *)
  Wt Γ tOn tSwitch

| T_Off :
  (* Wff n Γ -> *)
  (* --------- *)
  Wt Γ tOff tSwitch

| T_If a b c A :
  Wt Γ a tSwitch ->
  Wt Γ b A ->
  Wt Γ c A ->
  (* ------------ *)
  Wt Γ (tIf a b c) A

| T_Switch i :
  (* Wff Γ -> *)
  (* ----------- *)
  Wt Γ tSwitch (tUniv i)

| T_Univ i j :
  (* Wff n Γ -> *)
  i < j ->
  (* ------------ *)
  Wt Γ (tUniv i) (tUniv j).
