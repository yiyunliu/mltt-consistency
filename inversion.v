From WR Require Import syntax join typing.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.

Lemma Wt_Pi_inv n Γ A B U (h : Wt n Γ (tPi A B) U) :
  exists i, Wt n Γ A (tUniv i) /\
         Wt (S n) (A .: Γ) B (tUniv i) /\
         Join (tUniv i) U.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : n Γ T U / h => //.
  - hauto l:on.
  - hauto lq:on rew:off use:Join_transitive.
Qed.
