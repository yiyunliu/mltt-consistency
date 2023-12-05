Inductive myid (A : Type) (a : A) : A -> Type :=
  | myrefl : myid A a a.

Check myid_rect.

From WR Require Import syntax imports.

Definition is_bool_val a :=
  match a with
  | tTrue => true
  | tFalse => true
  | _ => false
  end.

Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  Par (var_tm i) (var_tm i)
| P_Univ n :
  (* -------- *)
  Par (tUniv n) (tUniv n)
| P_Void :
  (* -------- *)
  Par tVoid tVoid
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
| P_True :
  (* ------- *)
  Par tTrue tTrue
| P_False :
  (* ---------- *)
  Par tFalse tFalse
| P_If a0 a1 b0 b1 c0 c1:
  Par a0 a1 ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a0 b0 c0) (tIf a1 b1 c1)
| P_IfTrue a b0 b1 c0 c1 :
  Par a tTrue ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) b1
| P_IfFalse a b0 b1 c0 c1 :
  Par a tFalse ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) c1
| P_Bool :
  Par tBool tBool
| P_Refl :
  Par tRefl tRefl
| P_Eq a0 b0 A0 a1 b1 A1 :
  Par a0 a1 ->
  Par b0 b1 ->
  Par A0 A1 ->
  Par (tEq a0 b0 A0) (tEq a1 b1 A1)
| P_J t0 a0 b0 p0 t1 a1 b1 p1 :
  Par t0 t1 ->
  Par a0 a1 ->
  Par b0 b1 ->
  Par p0 p1 ->
  Par (tJ t0 a0 b0 p0) (tJ t1 a1 b1 p1)
| P_JRefl t0 a0 b0 p t1 a1 b1 :
  Par t0 t1 ->
  Par a0 a1 ->
  Par b0 b1 ->
  Par p tRefl ->
  Par (tJ t0 a0 b0 p) t1.

#[export]Hint Constructors Par : par.

Notation Pars := (rtc Par).

Definition Coherent a0 a1 := (exists b, Pars a0 b /\ Pars a1 b).

Lemma pars_pi_inv A B C (h : Pars (tPi A B) C) :
  exists A0 B0, C = tPi A0 B0 /\ Pars A A0 /\ Pars B B0.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma pars_eq_inv a b A C (h : Pars (tEq a b A) C) :
  exists a0 b0 A0, C = tEq a0 b0 A0 /\ Pars a a0 /\ Pars b b0 /\ Pars A A0.
Proof.
  move E : (tEq a b A) h => T h.
  move : a b A E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Coherent_pi_inj A B A0 B0 (h : Coherent (tPi A B) (tPi A0 B0)) :
  Coherent A A0 /\ Coherent B B0.
Proof. hauto q:on use:pars_pi_inv. Qed.

Lemma Coherent_eq_inj a b A a0 b0 A0 (h : Coherent (tEq a b A) (tEq a0 b0 A0)) : Coherent a a0 /\ Coherent b b0 /\ Coherent A A0.
Proof. hauto q:on use:pars_eq_inv. Qed.

Lemma pars_univ_inv i A (h : Pars (tUniv i) A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto lq:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma Coherent_univ_inj i j (h : Coherent (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:rtc use:pars_univ_inv. Qed.

Lemma Par_refl (a : tm) : Par a a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma P_IfTrue_star a b c :
  Pars a tTrue ->
  Pars (tIf a b c) b.
  move E : tTrue => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl, @rtc_once.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    hauto lq:on use:@rtc_once,Par_refl ctrs:Par.
Qed.

Lemma P_IfFalse_star a b c :
  Pars a tFalse ->
  Pars (tIf a b c) c.
  move E : tFalse => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl, @rtc_once.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_JRefl_star t a b p :
  Pars p tRefl  ->
  Pars (tJ t a b p) t.
Proof.
  move E : tRefl => v h.
  move : E.
  elim : p v / h.
  - hauto lq:on ctrs:Par use:Par_refl, @rtc_once.
  - move => x y z h0 h1 ih ?; subst.
    move /(_ ltac:(done)) in ih.
    apply : rtc_l; eauto.
    apply P_J; sfirstorder use:Par_refl.
Qed.

Lemma P_AppAbs' a A a0 b0 b b1 :
  b = subst_tm (b1..) a0 ->
  Par a (tAbs A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a b0) b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma par_renaming a b (ξ : fin -> fin) :
  Par a b ->
  Par (ren_tm ξ a) (ren_tm ξ b).
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  - move => *.
    apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma pars_renaming a b (ξ : fin -> fin) :
  Pars a b ->
  Pars (ren_tm ξ a) (ren_tm ξ b).
Proof. induction 1; hauto lq:on ctrs:rtc use:par_renaming. Qed.

Lemma Coherent_renaming a b (ξ : fin -> fin) :
  Coherent a b ->
  Coherent (ren_tm ξ a) (ren_tm ξ b).
Proof. hauto lq:on rew:off use:pars_renaming. Qed.

Lemma par_morphing_lift (ξ0 ξ1 : fin -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  forall i, Par (up_tm_tm ξ0 i) (up_tm_tm ξ1 i).
Proof.
  case => [|i]; first by constructor.
  asimpl.
  by apply par_renaming.
Qed.

Lemma par_morphing a b (ξ0 ξ1 : fin -> tm)
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
  - hauto lq:on db:par use:par_morphing_lift.
  - hauto lq:on db:par use:par_morphing_lift.
Qed.

Inductive good_pars_morphing : (fin -> tm) -> (fin -> tm) -> Prop :=
| good_pars_morphing_one ξ :
  good_pars_morphing ξ ξ
| good_pars_morphing_cons ξ0 ξ1 ξ2 :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  good_pars_morphing ξ1 ξ2 ->
  good_pars_morphing ξ0 ξ2.

(* No idea how to induct on (forall i, Pars (ξ0 i) (ξ1 i) ) *)
Lemma pars_morphing a b (ξ0 ξ1 : fin -> tm)
  (h : good_pars_morphing ξ0 ξ1) :
  Par a b ->
  Pars (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  move : a b.
  elim : ξ0 ξ1 / h.
  - sfirstorder use:par_morphing, @rtc_once, Par_refl.
  - hauto lq:on use:par_morphing, Par_refl ctrs:rtc.
Qed.

Lemma pars_morphing_star a b (ξ0 ξ1 : fin -> tm)
  (h : good_pars_morphing ξ0 ξ1)
  (h0 : Pars a b) :
  Pars (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  elim : a b / h0.
  - sfirstorder use:pars_morphing, Par_refl.
  - move => x y z /[swap] _.
    move : pars_morphing (good_pars_morphing_one ξ0); repeat move /[apply].
    apply rtc_transitive.
Qed.

Definition good_coherent_morphing ξ0 ξ1 :=
  exists ξ, good_pars_morphing ξ0 ξ /\ good_pars_morphing ξ1 ξ.

Lemma coherent_morphing_star a b ξ0 ξ1
  (h : good_coherent_morphing ξ0 ξ1)
  (h0 : Coherent a b) :
  Coherent (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  hauto q:on use:pars_morphing_star unfold:Coherent.
Qed.

Lemma coherent_cong_helper : forall a0 c, Pars a0 c -> good_pars_morphing a0.. c.. .
Proof.
  move => a0 c h2.
  elim : a0 c / h2.
    sfirstorder.
    move => a b c ? ?.
    apply : good_pars_morphing_cons.
    hauto lq:on inv:nat use:Par_refl.
Qed.

Lemma coherent_cong a0 a1 b0 b1
  (h : Coherent a0 b0)
  (h1 : Coherent a1 b1) :
  Coherent (subst_tm (a0..) a1) (subst_tm (b0..) b1).
Proof.
  apply coherent_morphing_star=>//.
  sfirstorder use:coherent_cong_helper.
Qed.

Lemma par_cong a0 a1 b0 b1 (h : Par a0 a1) (h1 : Par b0 b1) :
  Par (subst_tm (b0..) a0) (subst_tm (b1..) a1).
Proof.
  apply par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.

Lemma par_subst a0 a1 (h : Par a0 a1) (ξ : fin -> tm) :
  Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:Par_refl, par_morphing. Qed.

Lemma par_morphing_star a0 a1 (h : Pars a0 a1) (ξ0 ξ1 : fin -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Pars (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  induction h.
  - move => h. apply @rtc_once. eauto using par_morphing, Par_refl.
  - move => h0.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    sfirstorder use:par_morphing, Par_refl.
Qed.

Lemma Par_Coherent a b :
  Par a b -> Coherent a b.
Proof. hauto lq:on use:@rtc_once, @rtc_refl. Qed.

Lemma Coherent_morphing a0 a1 (h : Coherent a0 a1) (ξ0 ξ1 : fin -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Coherent (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  hauto l:on use:par_morphing_star, Par_refl, Par_Coherent unfold:Coherent.
Qed.

Lemma par_subst_star a0 a1 (h : Pars a0 a1) (ξ : fin -> tm) :
  Pars (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:par_morphing_star, Par_refl. Qed.

Lemma Coherent_subst_star a0 a1 (h : Coherent a0 a1) (ξ : fin -> tm) :
  Coherent (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto lq:on use:Coherent_morphing, Par_refl. Qed.

Derive Inversion Par_inv with (forall a b, Par a b).

Lemma par_confluent : diamond Par.
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
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => t0 a0 b0 p t1 a1 b1 ht iht ha iha hb ihb hp ihp ?.
    elim /Par_inv=> //.
    + hauto q:on  ctrs:Par inv:Par.
    + hauto q:on  ctrs:Par.
Qed.

Lemma pars_confluent : confluent Par.
Proof.
  sfirstorder use:par_confluent, @diamond_confluent.
Qed.

Lemma Coherent_reflexive a :
  Coherent a a.
Proof. hauto l:on ctrs:rtc. Qed.

Lemma Coherent_symmetric a b :
  Coherent a b -> Coherent b a.
Proof. sfirstorder. Qed.

Lemma Coherent_transitive a b c :
  Coherent a b -> Coherent b c -> Coherent a c.
Proof.
  have := pars_confluent.
  move => h [z0 [? h0]] [z1 [h1 ?]].
  move /(_ b _ _ h0 h1) in h.
  case : h => z [*].
  exists z. split; sfirstorder use:@rtc_transitive.
Qed.
