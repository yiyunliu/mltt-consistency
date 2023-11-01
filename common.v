From WR Require Import syntax typing.
From Coq Require Import ssreflect.
Require Import Psatz.

Definition good_renaming ξ n Γ m Δ :=
  (forall i, i < n -> ξ i < m /\ ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i)).

Lemma good_renaming_truncate n m Γ :
  good_renaming (Nat.add n) m (Nat.add n >> Γ) (n + m) Γ .
Proof.
  rewrite /good_renaming.
  split.
  - lia.
  - asimpldep.
    f_equal. fext => *; asimpl; lia.
Qed.

Lemma good_renaming_truncate' n m Γ :
  n <= m ->
  good_renaming (Nat.add n) (m - n) (Nat.add n >> Γ) m Γ.
Proof.
  move => h.
  replace m with (n + (m - n)) at 2; last by lia.
  apply good_renaming_truncate.
Qed.
