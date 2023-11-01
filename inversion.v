From WR Require Import syntax join typing.
From Coq Require Import ssreflect.
From Hammer Require Import Tactics.


Lemma Wt_Pi_inv n Γ A B U (h : Wt n Γ (tPi A B) U) :
  exists i, Wt n Γ A (tUniv i) /\
         Wt (S n) (A .: Γ) B (tUniv i) /\
         Join (tUniv i) U /\
         exists i, Wt n Γ U (tUniv i).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : n Γ T U / h => //.
  -
  - hauto lq:on rew:off use:Join_transitive.
Qed.

Lemma Wt_Pi_Univ_inv n Γ A B i (h : Wt n Γ (tPi A B) (tUniv i)) :
  Wt n Γ A (tUniv i) /\
  Wt (S n) (A .: Γ) B (tUniv i).
Proof. hauto lq:on use:Wt_Pi_inv, join_univ_inj. Qed.
