From WR Require Import imports.

Definition context := list tm.


Inductive lookup : nat -> context -> tm -> Prop :=
  | here : forall {A Γ}, lookup 0 (A :: Γ) (A ⟨shift⟩)
  | there : forall {n A Γ B},
      lookup n Γ A -> lookup (S n) (B :: Γ) (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i A, lookup i Γ A -> lookup (ξ i) Δ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

(*
Fixpoint dep_ith Γ i :=
  match Γ , i with
  | (A :: Γ), 0 => ren_tm shift A
  | (A :: Γ), (S i) => ren_tm shift (dep_ith Γ i)
  | _, _ => tVoid
  end.

Notation ith Γ i := (nth i Γ tVoid).

Lemma dep_ith_ren_tm (Γ : context) (A : tm) (x : fin) :
  dep_ith (A :: Γ) (S x) = ren_tm shift (dep_ith Γ x).
Proof. done. Qed.

Definition good_renaming ξ Γ Δ :=
  forall i, i ∈ dom Γ -> ξ i ∈ dom Δ /\ dep_ith Δ (ξ i) = ren_tm ξ (dep_ith Γ i).

Lemma dep_ith_shift Γ i :
  dep_ith Γ i = ren_tm (Nat.add (S i)) (ith Γ i).
Proof.
  elim : Γ i.
  - hauto q:on.
  - move => A Γ h.
    case => [|i].
    + done.
    + simpl.
      rewrite h.
      by asimpl.
Qed.

Lemma ith_skipn n i (Γ : context) :
  ith (skipn n Γ) i = ith Γ (n + i).
  move : n i.
  elim : Γ.
  - hauto lq:on inv:nat.
  - move => A Γ ih n i.
    case : i; qauto l:on inv:nat.
Qed.

Lemma good_renaming_truncate n Γ :
  good_renaming (Nat.add n) (skipn n Γ) Γ .
Proof.
  rewrite /good_renaming => i h /=.
  repeat rewrite dep_ith_shift.
  rewrite ith_skipn.
  split.
  - rewrite skipn_length in h.
    lia.
  - asimpl. f_equal.
    fext => ?; asimpl; lia.
Qed.
*)
