From WR Require Export syntax.
From Hammer Require Export Tactics.
From stdpp Require Export ssreflect relations.

Definition is_bool_val a :=
  match a with
  | tOn => true
  | tOff => true
  | _ => false
  end.

Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  Par (var_tm i) (var_tm i)
| P_Univ n :
  (* -------- *)
  Par (tUniv n) (tUniv n)
| P_False :
  (* -------- *)
  Par tFalse tFalse
| P_Pi A0 A1 B0 B1 :
  Par A0 A1 ->
  Par B0 B1 ->
  (* --------------------- *)
  Par (tPi A0 B0) (tPi A1 B1)
| P_Abs A0 A1 a0 a1 :
  Par A0 A1 ->
  Par a0 a1 ->
  (* -------------------- *)
  Par (tAbs A0 a0) (tAbs A1 a1)
| P_App a0 a1 b0 b1 :
  Par a0 a1 ->
  Par b0 b1 ->
  (* ------------------------- *)
  Par (tApp a0 b0) (tApp a1 b1)
| P_AppAbs a A a0 b0 b1 :
  Par a (tAbs A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a b0) (subst_tm (b1..) a0)
| P_On :
  (* ------- *)
  Par tOn tOn
| P_Off :
  (* ---------- *)
  Par tOff tOff
| P_If a0 a1 b0 b1 c0 c1:
  Par a0 a1 ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a0 b0 c0) (tIf a1 b1 c1)
| P_IfOn a b0 b1 c0 c1 :
  Par a tOn ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) b1
| P_IfOff a b0 b1 c0 c1 :
  Par a tOff ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) c1
| P_Switch :
  Par tSwitch tSwitch.

#[export]Hint Constructors Par : par.

Notation Pars := (rtc Par).

Notation Join a b := (exists c, Pars a c /\ Pars b c).

Lemma pars_pi_inv A B C (h : Pars (tPi A B) C) :
  exists A0 B0, C = tPi A0 B0 /\ Pars A A0 /\ Pars B B0.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:rtc, Par.
Qed.

Lemma join_pi_inj A B A0 B0 (h : Join (tPi A B) (tPi A0 B0)) :
  Join A A0 /\ Join B B0.
Proof. hauto q:on use:pars_pi_inv. Qed.

Lemma pars_univ_inv i A (h : Pars (tUniv i) A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto lq:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma join_univ_inj i j (h : Join (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:rtc use:pars_univ_inv. Qed.

Lemma Par_refl (a : tm) : Par a a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma P_IfOn_star a b c :
  Pars a tOn ->
  Pars (tIf a b c) b.
  move E : tOn => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl,@rtc_once.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    apply : rtc_once.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_IfOff_star a b c :
  Pars a tOff ->
  Pars (tIf a b c) c.
  move E : tOff => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl, @rtc_once.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    apply rtc_once.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_AppAbs' a A a0 b0 b b1 :
  b = subst_tm (b1..) a0 ->
  Par a (tAbs A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a b0) b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma par_renaming a b (ξ : nat -> nat) :
  Par a b ->
  Par (ren_tm ξ a) (ren_tm ξ b).
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  move => *.
  apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma pars_renaming a b (ξ : nat -> nat) :
  Pars a b ->
  Pars (ren_tm ξ a) (ren_tm ξ b).
Proof. induction 1; hauto lq:on ctrs:rtc use:par_renaming. Qed.

Lemma join_renaming a b (ξ : nat -> nat) :
  Join a b ->
  Join (ren_tm ξ a) (ren_tm ξ b).
Proof. hauto lq:on rew:off use:pars_renaming. Qed.

Lemma par_morphing_lift (ξ0 ξ1 : nat -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  forall i, Par (up_tm_tm ξ0 i) (up_tm_tm ξ1 i).
Proof.
  case => [|i]; first by constructor.
  asimpl.
  by apply par_renaming.
Qed.

Lemma par_morphing a b (ξ0 ξ1 : nat -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  Par a b ->
  Par (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  move => h0.
  move : ξ0 ξ1 h.
  elim : a b / h0 => /=; eauto with par.
  - hauto lq:on db:par use:par_morphing_lift.
  - hauto lq:on db:par use:par_morphing_lift.
  - move => *; apply : P_AppAbs'; eauto; by asimpl.
Qed.

Lemma par_cong a0 a1 b0 b1 (h : Par a0 a1) (h1 : Par b0 b1) :
  Par (subst_tm (b0..) a0) (subst_tm (b1..) a1).
Proof.
  apply par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.

Lemma par_subst a0 a1 (h : Par a0 a1) (ξ : nat -> tm) :
  Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:Par_refl, par_morphing. Qed.

Lemma par_morphing_star a0 a1 (h : Pars a0 a1) (ξ0 ξ1 : nat -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Pars (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  induction h.
  - move => h. apply rtc_once. eauto using par_morphing, Par_refl.
  - move => h0.
    apply : rtc_transitive; eauto.
    apply rtc_once.
    sfirstorder use:par_morphing, Par_refl.
Qed.

Lemma Par_join a b :
  Par a b -> Join a b.
Proof. hauto l:on use:@rtc_once. Qed.

Lemma join_morphing a0 a1 (h : Join a0 a1) (ξ0 ξ1 : nat -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Join (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  hauto l:on use:par_morphing_star, Par_refl, Par_join.
Qed.

Lemma par_subst_star a0 a1 (h : Pars a0 a1) (ξ : nat -> tm) :
  Pars (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:par_morphing_star, Par_refl. Qed.

Lemma join_subst_star a0 a1 (h : Join a0 a1) (ξ : nat -> tm) :
  Join (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto lq:on use:join_morphing, Par_refl. Qed.

Derive Inversion Par_inv with (forall a b, Par a b).

Lemma par_diamond : diamond Par.
Proof.
  rewrite /diamond.
  move => a b b0 h.
  move : b0.
  elim : a b / h.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 b2.
    elim /Par_inv; try congruence.
    + qauto l:on ctrs:Par.
    + move => ? a2 A a3 b3 b4 ? ?.
      case => *; subst.
      case /(_ _ ltac:(eassumption)) : ih1 => b [? ?].
      case /(_ _ ltac:(eassumption)) : ih0 => a [? h2].
      elim /Par_inv : h2; try congruence.
      move => ? A0 A1 a2 a4 ? ?.
      case => *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on ctrs:Par use:par_cong.
  - move => a A a0 b0 b1 ? ih0 ? ih1 b2.
    elim /Par_inv; try congruence.
    + move => h a1 a2 b3 b4 ? ? [*]; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 *].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? A0 A1 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par.
    + move => ? a1 A0 a2 b3 b4 ? ? [*] *; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 h1].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? A1 A2 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par inv:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a b0 b1 c0 c1 h0 ih0 h1 ih1 h2 ih2 b2.
    elim /Par_inv => //; hauto depth:3 lq:on rew:off inv:Par ctrs:Par.
  - move => a b0 b1 c0 c1 h0 ih0 h1 ih1 h2 ih2 b2.
    elim /Par_inv => //; hauto depth:3 lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
Qed.

Lemma par_confluent : confluent Par.
Proof. eauto using diamond_confluent, par_diamond. Qed.

Lemma Join_reflexive a :
  Join a a.
Proof. hauto l:on ctrs:rtc. Qed.

Lemma Join_symmetric a b :
  Join a b -> Join b a.
Proof. sfirstorder. Qed.

Lemma Join_transitive a b c :
  Join a b -> Join b c -> Join a c.
Proof.
  have := par_confluent.
  rewrite /confluent => h [z0 [? h0]] [z1 [h1 ?]].
  move /(_ b _ _ h0 h1) in h.
  case : h => z [*].
  exists z. split; sfirstorder use:@rtc_transitive.
Qed.
