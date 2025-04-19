From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent) base(sum_relation(..)).
Require Export Psatz.

Global Set Warnings "-notation-overridden".
Require Export Autosubst2.syntax Autosubst2.core Autosubst2.unscoped.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.


Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50) : subst_scope.
Notation fin := nat (only parsing).

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope. 
Global Open Scope list_scope.
