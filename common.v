From WR Require Import syntax.
From Coq Require Import ssreflect ssrbool List.
Require Import Psatz.
From Hammer Require Import Tactics.

Module Type common_sig
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade).

Notation eith Ξ i := (nth i Ξ el).

Definition is_bool_val a :=
  match a with
  | tOn => true
  | tOff => true
  | _ => false
  end.

Definition context := list tm.

Definition econtext := list grade.

Fixpoint dep_ith Γ i :=
  match Γ , i with
  | (A :: Γ), 0 => ren_tm shift A
  | (A :: Γ), (S i) => ren_tm shift (dep_ith Γ i)
  | _, _ => tFalse
  end.

Notation ith Γ i := (nth i Γ tFalse).

Lemma dep_ith_ren_tm (Γ : context) (A : tm) (x : fin) :
  dep_ith (A :: Γ) (S x) = ren_tm shift (dep_ith Γ x).
Proof. done. Qed.

Lemma dep_ith_ren_tm0 (Γ : context) (A : tm) :
  dep_ith (A :: Γ) 0 = ren_tm shift A.
Proof. done. Qed.

Definition good_renaming ξ Γ Ξ Δ Ξ' :=
  forall i, i < length Γ -> ξ i < length Δ /\ dep_ith Δ (ξ i) = ren_tm ξ (dep_ith Γ i) /\ (eith Ξ' (ξ i) <= eith Ξ i)%O.

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

Lemma list_ith_skipn {A : Type} (a : A)
  n i (Γ : list A) :
  nth i (skipn n Γ) a = nth (n + i) Γ a.
Proof.
  elim : Γ n i.
  - hauto lq:on inv:nat.
  - qauto l:on inv:nat.
Qed.

Lemma ith_skipn n i (Γ : context) :
  ith (skipn n Γ) i = ith Γ (n + i).
Proof. sfirstorder use:list_ith_skipn.  Qed.

Lemma eith_skipn n i (Γ : econtext) :
  eith (skipn n Γ) i = eith Γ (n + i).
Proof. sfirstorder use:list_ith_skipn. Qed.

Lemma good_renaming_truncate n Γ Ξ :
  good_renaming (Nat.add n) (skipn n Γ) (skipn n Ξ) Γ Ξ.
Proof.
  rewrite /good_renaming => i h /=.
  repeat rewrite dep_ith_shift.
  repeat rewrite ith_skipn eith_skipn.
  split.
  - rewrite skipn_length in h.
    lia.
  - split.
    + asimpl.
      f_equal.
      fext => ?; asimpl; lia.
    + apply Order.le_refl.
Qed.

End common_sig.
