From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent) base(sum_relation(..)).
Require Export Psatz.

Global Set Warnings "-notation-overridden".
Require Export Autosubst2.syntax.
