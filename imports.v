From Coq Require Export ssreflect ssrbool.
From Coq Require Export Wf_nat (well_founded_ltof, induction_ltof1).
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent).
Require Export Psatz.

Global Set Warnings "-notation-overridden".
From WR Require Export syntax.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "n ∈ 'dom'  Γ " := (n < length Γ) (at level 70, no associativity).

Global Open Scope subst_scope.
