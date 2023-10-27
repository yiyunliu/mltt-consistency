From WR Require Import syntax.
From Coq Require Import
  ssreflect
  Sets.Relations_2
  Sets.Relations_3
  Sets.Relations_3_facts.
From Hammer Require Import Tactics.

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

Definition Join := coherent _ Par.

Lemma Par_refl (a : tm) : Par a a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

#[export]Hint Unfold Join : par.

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

Lemma par_cong a0 a1 b0 b1 (h : Par a0 a1) (h1 : Par b0 b1) :
  Par (subst_tm (b0..) a0) (subst_tm (b1..) a1).
Proof.
  apply par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.

Lemma par_subst a0 a1 (h : Par a0 a1) (ξ : fin -> tm) :
  Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:Par_refl, par_morphing. Qed.

Lemma par_subst_star a0 a1 (h : Rstar _ Par a0 a1) (ξ : fin -> tm) :
  Rstar _ Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof.
  induction h.
  - apply Rstar_0.
  - apply : Rstar_transitive; eauto.
    apply Rstar_contains_R.
    sfirstorder use:par_subst.
Qed.

Derive Inversion Par_inv with (forall a b, Par a b).

Lemma par_confluent : Strongly_confluent _ Par.
Proof.
  rewrite /Strongly_confluent.
  move => a b b0 h.
  move : b0.
  elim : a b / h.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 b2.
    elim /Par_inv; try congruence.
    + qauto l:on ctrs:Par.
    + move => ? a2 A a3 b3 b4 ? ?.
      case => *; subst.
      case /(_ _ ltac:(eassumption)) : ih1 => b [? ?].
      case /(_ _ ltac:(eassumption)) : ih0 => a [? h2].
      elim /Par_inv : h2; try congruence.
      move => ? A0 A1 a2 a4 ? ?.
      case => *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on ctrs:Par use:par_cong.
  - move => a A a0 b0 b1 ? ih0 ? ih1 b2.
    elim /Par_inv; try congruence.
    + move => h a1 a2 b3 b4 ? ? [*]; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 *].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? A0 A1 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par.
    + move => ? a1 A0 a2 b3 b4 ? ? [*] *; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 h1].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? A1 A2 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par inv:Par.
Qed.

Lemma pars_confluent : Confluent _ Par.
Proof.
  apply Strong_confluence.
  apply par_confluent.
Qed.

Lemma Join_reflexive a :
  Join a a.
Proof. hauto l:on ctrs:Rstar. Qed.

Lemma Join_symmetric a b :
  Join a b -> Join b a.
Proof. sfirstorder use:coherent_symmetric. Qed.

Lemma Join_transitive a b c :
  Join a b -> Join b c -> Join a c.
Proof.
  have := pars_confluent.
  rewrite /Confluent /confluent /Join /coherent => h [z0 [? h0]] [z1 [h1 ?]].
  move /(_ b _ _ h0 h1) in h.
  case : h => z [*].
  exists z. split; sfirstorder use:Rstar_transitive.
Qed.
