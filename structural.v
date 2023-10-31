From WR Require Import syntax join typing.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.
Require Import Psatz.

Definition good_renaming ξ n Γ m Δ :=
  (forall i, i < n -> ξ i < m /\ ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i)).

Lemma good_renaming_up ξ n Γ m Δ A :
  good_renaming ξ n Γ m Δ ->
  good_renaming (upRen_tm_tm ξ) (S n) (A .: Γ) (S m) (ren_tm ξ A .: Δ).
Proof.
  move => h.
  rewrite /good_renaming.
  case => [_ | i ?].
  - split; [sfirstorder | by asimpldep].
  - split.
    + asimpl; suff : ξ i < m; sfirstorder.
    + repeat rewrite dep_ith_ren_tm.
      rewrite /good_renaming in h.
      case /(_ i ltac:(sfirstorder)) : h => h h'.
      rewrite -h'; by asimpl.
Qed.

Lemma T_App' n Γ a A B0 B b :
  B0 = (subst_tm (b..) B) ->
  Wt n Γ a (tPi A B) ->
  Wt n Γ b A ->
  (* -------------------- *)
  Wt n Γ (tApp a b) B0.
Proof. qauto ctrs:Wt. Qed.

Lemma wff_nil Γ :
  Wff 0 Γ.
Proof. apply Wff_intro with (F := fun x => x); lia. Qed.

Lemma wff_cons m Γ A i
  (h0 : Wt m Γ A (tUniv i))
  (h1 : Wff m Γ) :
  Wff (S m) (A .: Γ).
Proof.
  inversion h1 as [F h].
  apply Wff_intro with (F := i .: F).
  case => [_ | p /Arith_prebase.lt_S_n hp ].
  + replace (S m - 1) with m; last by lia.
    by asimpl.
  + sfirstorder ctrs:Wff.
Qed.

#[export]Hint Resolve wff_nil wff_cons : wff.

Lemma renaming_Syn_mutual n Γ a A (h : Wt n Γ a A) : forall m Δ ξ,
    good_renaming ξ n Γ m Δ ->
    Wff m Δ ->
    Wt m Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  elim : Γ a A / h; try qauto l:on ctrs:Wt unfold:good_renaming.
  - hauto lq:on ctrs:Wt use:good_renaming_up db:wff.
  - (* hauto lq:on ctrs:Wt use:good_renaming_up db:wff. *) admit.
  - move => * /=. apply : T_App'; eauto; by asimpl.
  - qauto l:on ctrs:Wt use:join_renaming.
Admitted.
