From WR Require Import syntax typing.
From Coq Require Import ssreflect.
Require Import Psatz.
From Hammer Require Import Tactics.

Definition good_renaming ξ Γ Δ :=
  forall i A, dep_ith Γ i = Some A ->
          dep_ith Δ (ξ i) = Some (ren_tm ξ A).


Lemma nth_error_skipn {T : Type} n i Γ (A : T) :
  nth_error (skipn n Γ) i = Some A ->
  nth_error Γ (n + i) = Some A.
  move : n i A.
  elim : Γ.
  - hauto lq:on rew:off inv:nat ctrs:option.
  - hauto lq:on rew:off inv:nat ctrs:option.
Qed.

Lemma good_renaming_truncate n Γ :
  good_renaming (Nat.add n) (skipn n Γ) Γ .
Proof.
  rewrite /good_renaming => i A h.
  rewrite dep_ith_shift_n in h.
  remember (nth_error (skipn n Γ) i) as A0 eqn:eq.
  case : A0 eq h => // A0 eq h.
  apply eq_sym in eq.
  apply nth_error_skipn in eq.
  simpl in h.
  case : h => * /=; subst.
  rewrite dep_ith_shift_n.
  rewrite eq => /=.
  asimpl.
  f_equal.
  f_equal.
  simpl.
  rewrite /funcomp.
  fext. lia.
Qed.

(* Lemma good_renaming_truncate' n m Γ : *)
(*   n <= m -> *)
(*   good_renaming (Nat.add n) (m - n) (Nat.add n >> Γ) m Γ. *)
(* Proof. *)
(*   move => h. *)
(*   replace m with (n + (m - n)) at 2; last by lia. *)
(*   apply good_renaming_truncate. *)
(* Qed. *)
