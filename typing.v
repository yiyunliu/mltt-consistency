From WR Require Import syntax.
From Coq Require Import ssreflect Sets.Relations_2 Sets.Relations_3.
From Hammer Require Import Tactics.

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

Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  Par (var_tm i) (var_tm i)
| P_Univ :
  (* -------- *)
  Par tUniv tUniv
| P_False :
  (* -------- *)
  Par tFalse tFalse
| P_Pi A0 A1 B0 B1 :
  Par A0 A1 ->
  Par B0 B1 ->
  (* --------------------- *)
  Par (tPi A0 B0) (tPi A1 B1)
| P_Abs A0 A1 a0 a1 :
  Par A0 A1 ->
  Par a0 a1 ->
  (* -------------------- *)
  Par (tAbs A0 a0) (tAbs A1 a1)
| P_App a0 a1 b0 b1 :
  Par a0 a1 ->
  Par b0 b1 ->
  (* ------------------------- *)
  Par (tApp a0 b0) (tApp a1 b1)
| P_AppAbs a A a0 b0 b1 :
  Par a (tAbs A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a b0) (subst_tm (b1..) a0).

#[export]Hint Constructors Par : par.

Definition MultiPar := Rplus _ Par.

Definition MultiPar' := Rstar _ Par.

Definition Join := coherent _ MultiPar'.

Lemma Par_refl (a : tm) : Par a a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma MultiPar_refl (a : tm) : MultiPar a a.
Proof. elim : a; hauto lq:on ctrs:Rplus use:Par_refl. Qed.

Lemma MultiPar_star_plus_equiv a b : MultiPar a b <-> MultiPar' a b.
Proof.
  split.
  induction 1; hauto lq:on ctrs:Rstar.
  induction 1; hauto lq:on ctrs:Rplus use:MultiPar_refl.
Qed.

#[export]Hint Resolve MultiPar_star_plus_equiv : par.
#[export]Hint Unfold Join MultiPar MultiPar' : par.

Lemma P_AppAbs' a A a0 b0 b b1 :
  b = subst_tm (b1..) a0 ->
  Par a (tAbs A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a b0) b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma par_renaming a b (ξ : fin -> fin) :
  Par a b ->
  Par (ren_tm ξ a) (ren_tm ξ b).
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  move => *.
  apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma par_morphing_lift (ξ0 ξ1 : fin -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  forall i, Par (up_tm_tm ξ0 i) (up_tm_tm ξ1 i).
Proof.
  case => [|i]; first by constructor.
  asimpl.
  by apply par_renaming.
Qed.

Lemma par_morphing a b (ξ0 ξ1 : fin -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  Par a b ->
  Par (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  move => h0.
  move : ξ0 ξ1 h.
  elim : a b / h0 => /=; eauto with par.
  - hauto lq:on db:par use:par_morphing_lift.
  - hauto lq:on db:par use:par_morphing_lift.
  - move => *; apply : P_AppAbs'; eauto; by asimpl.
Qed.
