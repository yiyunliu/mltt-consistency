(** * Signature for lattices *)
(** I tried using the lattice library from mathcomp but their whole
set-up felt too heavy and I'm not sure what the best practice is. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From Hammer Require Import Tactics Hammer.
From Ltac2 Require Ltac2.

  Module Type Lattice.
    Declare Scope lattice_scope.
    Local Open Scope lattice_scope.

    Parameter A : Set.
    Parameter meet : A -> A -> A.
    Parameter join : A -> A -> A.

    Infix "∪" := join (at level 65) : lattice_scope.
    Infix "∩" := meet (at level 60) : lattice_scope.

    Notation "a ⊆ b" := (a ∩ b = a) (at level 70, no associativity) : lattice_scope.

    Axiom meet_commutative : forall a b, a ∩ b = b ∩ a.
    Axiom meet_associative : forall a b c, (a ∩ b) ∩ c = a ∩ (b ∩ c).
    Axiom meet_absorptive : forall a b, a ∩ (a ∪ b) = a.
    Axiom meet_idempotent : forall a, a ∩ a = a.
    Axiom join_commutative : forall a b, a ∪ b = b ∪ a.
    Axiom join_associative: forall a b c, (a ∪ b) ∪ c = a ∪ (b ∪ c).
    Axiom join_absorptive : forall a b, a ∪ (a ∩ b) = a.
    Axiom join_idempotent : forall a, a ∪ a = a.
  End Lattice.

  Module Properties (Import lattice : Lattice).

  End Properties.

  (** ** An incomplete solver for lattice formulas  *)
  Module Solver (Import lattice : Lattice).
    Local Open Scope lattice_scope.

    Inductive lexp : Set :=
    | Var : A -> lexp
    | Meet : lexp -> lexp -> lexp
    | Join : lexp -> lexp -> lexp.

    Fixpoint denoteLexp (e : lexp) :=
      match e with
      | Var a => a
      | Meet e1 e2 => meet (denoteLexp e1) (denoteLexp e2)
      | Join e1 e2 => join (denoteLexp e1) (denoteLexp e2)
      end.

    Fixpoint lexp_size (e : lexp) :=
      match e with
      | Var _ => 0
      | Meet e1 e2 => 1 + lexp_size e1 + lexp_size e2
      | Join e1 e2 => 1 + lexp_size e1 + lexp_size e2
      end.

    #[tactic="sfirstorder"]Equations splitLeq (e1 e2 : lexp) : Prop
      by wf (lexp_size e1 + lexp_size e2) lt :=
      splitLeq (Var a1) (Var a2) => a1 ⊆ a2;
      splitLeq (Join e11 e12) e2 => splitLeq e11 e2 /\ splitLeq e12 e2;
      splitLeq e1 (Meet e21 e22) => splitLeq e1 e21 /\ splitLeq e1 e22;
      splitLeq e1 (Join e21 e22) => splitLeq e1 e21 \/ splitLeq e1 e22 \/ denoteLexp e1 ⊆ denoteLexp (Join e21 e22) ;
      splitLeq (Meet e11 e12) e2 => splitLeq e11 e2 \/ splitLeq e12 e2 \/ denoteLexp (Meet e11 e12) ⊆ denoteLexp e2.



    #[tactic="sfirstorder"]Equations splitLeqForward (e1 e2 : lexp) : Prop
      by wf (lexp_size e1 + lexp_size e2) lt :=
      splitLeqForward (Var a1) (Var a2) => a1 ⊆ a2;
      splitLeqForward (Join e11 e12) e2 => splitLeqForward e11 e2 /\ splitLeqForward e12 e2;
      splitLeqForward e1 (Meet e21 e22) => splitLeqForward e1 e21 /\ splitLeqForward e1 e22;
      splitLeqForward e1 e2 => denoteLexp e1 ⊆ denoteLexp e2.

    Lemma leq_lat_leq_lat'_iff :
      forall e1 e2, e1 ⊆ e2 <-> e1 ∪ e2 = e2.
    Proof.
      strivial use: join_commutative, meet_absorptive, meet_commutative, join_absorptive.
    Qed.

    Lemma leq_join e1 e2 :
      e1 ⊆ e1 ∪ e2.
    Proof. sfirstorder use: meet_absorptive. Qed.

    Lemma leq_trans e1 e2 e3 :
      e1 ⊆ e2 -> e2 ⊆ e3 -> e1 ⊆ e3.
    Proof. scongruence use: meet_associative. Qed.

    Lemma leq_meet_iff (e1 e2 e3 : A) :
      e1 ⊆ e2 ∩ e3 <-> e1 ⊆ e2 /\ e1 ⊆ e3.
    Proof.
      split.
      - move : e1 e2 e3.
        wlog : / forall e1 e2 e3, e1 ⊆ e2 ∩ e3 -> e1 ⊆ e3.
        hauto lq:on use: meet_associative, meet_idempotent, leq_trans.
        hauto use: meet_commutative.
      - strivial use: meet_associative.
    Qed.

    Lemma meet_leq e1 e2 :
      e1 ∩ e2 ⊆ e1.
    Proof.
      scongruence use: meet_associative, meet_idempotent, meet_commutative.
    Qed.

    Lemma leq_join_iff (e1 e2 e3 : A) :
      e1 ∪ e2 ⊆ e3 <-> e1 ⊆ e3 /\ e2 ⊆ e3.
    Proof.
      split.
      - move : e1 e2 e3.
        suff : forall e1 e2 e3, e1 ∪ e2 ⊆ e3 -> e1 ⊆ e3 by hauto use: join_commutative.
        sfirstorder use: leq_join, leq_trans.
      - hauto lq: on use: join_associative, leq_lat_leq_lat'_iff.
    Qed.

    (* The other direction is not true.... *)
    Lemma leq_join_prime (e1 e2 e3 : A) :
      e1 ⊆ e2 \/ e1 ⊆ e3 -> e1 ⊆ e2 ∪ e3.
    Proof.
      sfirstorder use: meet_associative, leq_lat_leq_lat'_iff, join_commutative, join_associative, leq_join.
    Qed.

    Lemma leq_meet_prime (e1 e2 e3 : A) :
      e1 ⊆ e3 \/ e2 ⊆ e3 -> e1 ∩ e2 ⊆ e3.
    Proof. hauto use: meet_commutative, meet_associative. Qed.

    (* I don't understand why, but we do need @ for typeclass rewrite rules *)
    #[export] Hint Rewrite -> leq_meet_iff leq_join_iff : lat_db_rew.
    #[export] Hint Resolve leq_join_prime leq_meet_prime : lat_db.


    (* Transforming goal *)
    Theorem splitLeq_sound (e1 e2 : lexp) :
      splitLeq e1 e2 -> denoteLexp e1 ⊆ denoteLexp e2.
    Proof.
      move => H.
      have h0 := splitLeq_graph_correct e1 e2.
      remember (splitLeq e1 e2) as p.
      destruct h0 using splitLeq_graph_rect;
        hauto lq: on rew: off db: lat_db rew:db: lat_db_rew.
    Qed.

    Theorem splitLeq_complete (e1 e2 : lexp) :
      denoteLexp e1 ⊆ denoteLexp e2 -> splitLeq e1 e2.
    Proof.
      intros.
      have h0 := splitLeq_graph_correct e1 e2.
      remember (splitLeq e1 e2) as p.
      destruct h0 using splitLeq_graph_rect;
        hauto lq: on rew: off db: lat_db rew:db: lat_db_rew.
    Qed.

    Theorem splitLeqForward_complete (e1 e2 : lexp) :
      denoteLexp e1 ⊆ denoteLexp e2 -> splitLeqForward e1 e2.
    Proof.
      move => H0.
      have h0 := splitLeqForward_graph_correct e1 e2.
      remember (splitLeqForward e1 e2) as p.
      destruct h0 using splitLeqForward_graph_rect;
        hauto db: lat_db rew:db:lat_db_rew.
    Qed.

    Theorem splitLeq_iff (e1 e2 : lexp) :
      denoteLexp e1 ⊆ denoteLexp e2 <-> splitLeq e1 e2.
    Proof.
      hauto depth:1 use: @splitLeq_sound, @splitLeq_complete.
    Qed.



  End Solver.
