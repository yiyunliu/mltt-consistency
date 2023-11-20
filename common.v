From WR Require Export syntax.
From Coq Require Export ssreflect ssrbool.
From mathcomp Require Export zify.
Export seq.
From Hammer Require Export Tactics.

Module Type common_sig
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade).

Notation eith Ξ i := (nth el Ξ i).

Definition is_bool_val a :=
  match a with
  | tOn => true
  | tOff => true
  | _ => false
  end.

Definition context := list (grade * tm).

Definition econtext := list grade.

Definition levels : context -> econtext := seq.unzip1.

Fixpoint dep_ith (Γ : list tm) i :=
  match Γ , i with
  | (A :: Γ), 0 => ren_tm shift A
  | (_ :: Γ), (S i) => ren_tm shift (dep_ith Γ i)
  | _, _ => tFalse
  end.

Notation ith Γ i := (nth tFalse Γ i).

Lemma dep_ith_ren_tm (Γ : list tm) (A : tm) (x : fin) :
  dep_ith (A :: Γ) (S x) = ren_tm shift (dep_ith Γ x).
Proof. done. Qed.

Lemma dep_ith_ren_tm0 (Γ : list tm) (A : tm) :
  dep_ith (A :: Γ) 0 = ren_tm shift A.
Proof. done. Qed.

Definition good_renaming ξ Γ Δ :=
  let Γ_ty := seq.unzip2 Γ in
  let Γ_ℓ := seq.unzip1 Γ in
  let Δ_ty := seq.unzip2 Δ in
  let Δ_ℓ := seq.unzip1 Δ in
  forall i, i < seq.size Γ -> ξ i < seq.size Δ /\ dep_ith Δ_ty (ξ i) = ren_tm ξ (dep_ith Γ_ty i) /\ (eith Δ_ℓ (ξ i) <= eith Γ_ℓ i)%O.

Lemma dep_ith_shift Γ i :
  dep_ith Γ i = ren_tm (Nat.add (S i)) (ith Γ i).
Proof.
  elim : Γ i.
  - hauto lq:on inv:nat.
  - move => A Γ h.
    case => [|i].
    + done.
    + simpl.
      rewrite h.
      by asimpl.
Qed.

Lemma ith_skipn n i (Γ : list tm) :
  ith (drop n Γ) i = ith Γ (n + i).
Proof. by rewrite nth_drop. Qed.

Lemma eith_skipn n i (Γ : list grade) :
  eith (drop n Γ) i = eith Γ (n + i).
Proof. by rewrite nth_drop. Qed.

Lemma good_renaming_truncate n Γ :
  good_renaming (Nat.add n) (drop n Γ) Γ.
Proof.
  rewrite /good_renaming => i h /=.
  repeat rewrite dep_ith_shift.
  rewrite /unzip1 /unzip2.
  repeat rewrite map_drop.
  repeat rewrite ith_skipn eith_skipn.
  split.
  - rewrite size_drop in h.
    lia.
  - split.
    + asimpl.
      f_equal.
      fext => ?; asimpl; lia.
    + apply Order.le_refl.
Qed.

End common_sig.
