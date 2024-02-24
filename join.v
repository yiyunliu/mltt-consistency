From WR Require Import imports.
Require Export Setoid.

Definition is_bool_val a :=
  match a with
  | tTrue => true
  | tFalse => true
  | _ => false
  end.

Reserved Infix "⇒" (at level 60, right associativity).
Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  (var_tm i) ⇒ (var_tm i)
| P_Univ n :
  (* -------- *)
  (tUniv n) ⇒ (tUniv n)
| P_Void :
  (* -------- *)
  tVoid ⇒ tVoid
| P_Pi A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  (tPi A0 B0) ⇒ (tPi A1 B1)
| P_Abs a0 a1 :
  (a0 ⇒ a1) ->
  (* -------------------- *)
  (tAbs a0) ⇒ (tAbs a1)
| P_App a0 a1 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  (tApp a0 b0) ⇒ (tApp a1 b1)
| P_AppAbs a a0 b0 b1 :
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp (tAbs a) b0) ⇒ (a0 [b1..])
| P_True :
  (* ------- *)
  tTrue ⇒ tTrue
| P_False :
  (* ---------- *)
  tFalse ⇒ tFalse
| P_If a0 a1 b0 b1 c0 c1:
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (c0 ⇒ c1) ->
  (* ---------- *)
  (tIf a0 b0 c0) ⇒ (tIf a1 b1 c1)
| P_IfTrue b0 b1 c0 :
  (b0 ⇒ b1) ->
  (* ---------- *)
  (tIf tTrue b0 c0) ⇒ b1
| P_IfFalse b0 c0 c1 :
  (c0 ⇒ c1) ->
  (* ---------- *)
  (tIf tFalse b0 c0) ⇒ c1
| P_Bool :
  tBool ⇒ tBool
| P_Refl :
  tRefl ⇒ tRefl
| P_Eq a0 b0 A0 a1 b1 A1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (A0 ⇒ A1) ->
  (tEq a0 b0 A0) ⇒ (tEq a1 b1 A1)
| P_J t0 a0 b0 p0 t1 a1 b1 p1 :
  (t0 ⇒ t1) ->
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (p0 ⇒ p1) ->
  (tJ t0 a0 b0 p0) ⇒ (tJ t1 a1 b1 p1)
| P_JRefl t0 a b t1 :
  (t0 ⇒ t1) ->
  (tJ t0 a b tRefl) ⇒ t1
where "A ⇒ B" := (Par A B).

#[export]Hint Constructors Par : par.

Infix "⇒*" := (rtc Par) (at level 60, right associativity).

Definition Coherent a0 a1 := (exists b, a0 ⇒* b /\ a1 ⇒* b).

Lemma pars_pi_inv A B C (h : (tPi A B) ⇒* C) :
  exists A0 B0, C = tPi A0 B0 /\ (A ⇒* A0) /\ (B ⇒* B0).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma pars_eq_inv a b A C (h : (tEq a b A) ⇒* C) :
  exists a0 b0 A0, C = tEq a0 b0 A0 /\ a ⇒* a0 /\ b ⇒* b0 /\ A ⇒* A0.
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

Lemma pars_univ_inv i A (h : (tUniv i) ⇒* A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto lq:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma Coherent_univ_inj i j (h : Coherent (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:rtc use:pars_univ_inv. Qed.

Lemma Par_refl (a : tm) : a ⇒ a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma P_AppAbs_cbn (a b b0 : tm) :
  b0 = a [b..] ->
  (tApp (tAbs a) b) ⇒ b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

Lemma P_IfTrue_star a b c :
  (a ⇒* tTrue) ->
  ((tIf a b c) ⇒* b).
  move E : tTrue => v h.
  move : E.
  elim : a v / h.
  - move => *. subst.
    apply rtc_once. apply P_IfTrue. apply Par_refl.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    hauto lq:on use:@rtc_once,Par_refl ctrs:Par.
Qed.

Lemma P_IfFalse_star a b c :
  (a ⇒* tFalse) ->
  ((tIf a b c) ⇒* c).
  move E : tFalse => v h.
  move : E.
  elim : a v / h.
  - move => *. subst.
    apply rtc_once. apply P_IfFalse. apply Par_refl.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_JRefl_star t a b p :
  (p ⇒* tRefl)  ->
  ((tJ t a b p) ⇒* t).
Proof.
  move E : tRefl => v h.
  move : E.
  elim : p v / h.
  - move => *. subst.
    apply rtc_once. apply P_JRefl. apply Par_refl.
  - move => x y z h0 h1 ih ?; subst.
    move /(_ ltac:(done)) in ih.
    apply : rtc_l; eauto.
    apply P_J; sfirstorder use:Par_refl.
Qed.

Lemma P_AppAbs' a a0 b0 b b1 :
  b = a0 [b1..] ->
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp (tAbs a) b0) ⇒ b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma par_renaming a b (ξ : fin -> fin) :
  (a ⇒ b) ->
  a⟨ξ⟩ ⇒ b⟨ξ⟩.
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  - move => *.
    apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma pars_renaming a b (ξ : fin -> fin) :
  (a ⇒* b) ->
  a⟨ξ⟩ ⇒* b⟨ξ⟩.
Proof. induction 1; hauto lq:on ctrs:rtc use:par_renaming. Qed.

Lemma Coherent_renaming a b (ξ : fin -> fin) :
  Coherent a b ->
  Coherent (a ⟨ ξ ⟩) (b ⟨ ξ ⟩).
Proof. hauto lq:on rew:off use:pars_renaming. Qed.

(* TODO: notation for up_tm_tm *)
Lemma par_morphing_lift (ξ0 ξ1 : fin -> tm)
  (h : forall i, (ξ0 i) ⇒ (ξ1 i)) :
  forall i, (up_tm_tm ξ0 i) ⇒ (up_tm_tm ξ1 i).
Proof.
  case => [|i]; first by constructor.
  asimpl.
  by apply par_renaming.
Qed.

Lemma par_morphing a b (σ0 σ1 : fin -> tm)
  (h : forall i, (σ0 i) ⇒ (σ1 i)) :
  (a ⇒ b) ->
  (a[σ0]) ⇒ (b[σ1]).
Proof.
  move => h0.
  move : σ0 σ1 h.
  elim : a b / h0; try solve [simpl; eauto with par].
  - hauto lq:on db:par use:par_morphing_lift.
  - hauto lq:on db:par use:par_morphing_lift.
  - move => a a0 b0 b1 h0 ih0 h1 ih1 σ0 σ h /=.
    apply P_AppAbs' with (a0 := a0 [up_tm_tm σ]) (b1 := b1 [σ]).
    by asimpl. hauto l:on use:par_renaming inv:nat. eauto.
  - hauto lq:on db:par use:par_morphing_lift.
Qed.

Inductive good_pars_morphing : (fin -> tm) -> (fin -> tm) -> Prop :=
| good_pars_morphing_one σ :
  good_pars_morphing σ σ
| good_pars_morphing_cons σ0 σ1 σ2 :
  (forall i, (σ0 i) ⇒ (σ1 i)) ->
  good_pars_morphing σ1 σ2 ->
  good_pars_morphing σ0 σ2.

Lemma good_pars_morphing_ext a b σ0 σ1
  (h : a ⇒* b) :
  good_pars_morphing σ0 σ1 ->
  good_pars_morphing (a .: σ0) (b .: σ1).
Proof.
  elim : a b /h.
  - move => a.
    move => h.
    elim : σ0 σ1 / h; first by sfirstorder.
    move => σ0 σ1 σ2 h h1.
    apply good_pars_morphing_cons.
    hauto lq:on inv:nat use:Par_refl.
  - move => x y z ha hb /[apply].
    apply : good_pars_morphing_cons.
    hauto lq:on inv:nat use:Par_refl.
Qed.

Lemma good_pars_morphing_ext2 a0 b0 a1 b1 σ0 σ1
  (h : a0 ⇒* b0) (h1 : a1 ⇒*  b1) :
  good_pars_morphing σ0 σ1 ->
  good_pars_morphing (a0 .: (a1 .: σ0)) (b0 .: (b1 .: σ1)).
Proof. sfirstorder use:good_pars_morphing_ext. Qed.

(* No idea how to induct on (forall i, Pars (σ0 i) (σ1 i) ) *)
Lemma pars_morphing a b (σ0 σ1 : fin -> tm)
  (h : good_pars_morphing σ0 σ1) :
  (a ⇒ b) ->
  (a [σ0]) ⇒* (b[σ1]).
Proof.
  move : a b.
  elim : σ0 σ1 / h.
  - sfirstorder use:par_morphing, @rtc_once, Par_refl.
  - hauto lq:on use:par_morphing, Par_refl ctrs:rtc.
Qed.

Lemma pars_morphing_star a b (σ0 σ1 : fin -> tm)
  (h : good_pars_morphing σ0 σ1)
  (h0 : a ⇒* b) :
  (a [σ0] ⇒* b[σ1]).
Proof.
  elim : a b / h0.
  - sfirstorder use:pars_morphing, Par_refl.
  - move => x y z /[swap] _.
    move : pars_morphing (good_pars_morphing_one σ0); repeat move /[apply].
    apply rtc_transitive.
Qed.

Definition good_coherent_morphing σ0 σ1 :=
  exists σ, good_pars_morphing σ0 σ /\ good_pars_morphing σ1 σ.

Lemma coherent_morphing_star a b σ0 σ1
  (h : good_coherent_morphing σ0 σ1)
  (h0 : Coherent a b) :
  Coherent (a[σ0]) (b[σ1]).
Proof.
  hauto q:on use:pars_morphing_star unfold:Coherent.
Qed.

Lemma coherent_cong_helper : forall a0 c, (a0 ⇒* c) -> good_pars_morphing a0.. c.. .
Proof.
  move => a0 c h2.
  elim : a0 c / h2.
    sfirstorder.
    move => a b c ? ?.
    apply : good_pars_morphing_cons.
    sauto lq:on inv:nat use:Par_refl. 
Qed.

Lemma coherent_cong a0 a1 b0 b1
  (h : Coherent a0 b0)
  (h1 : Coherent a1 b1) :
  Coherent (a1 [a0..]) (b1 [b0..]).
Proof.
  apply coherent_morphing_star=>//.
  sfirstorder use:coherent_cong_helper.
Qed.

Lemma par_cong a0 a1 b0 b1 (h : a0 ⇒ a1) (h1 : b0 ⇒ b1) :
  (a0 [b0..] ⇒ a1 [b1..]).
Proof.
  apply par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.

Lemma par_subst a0 a1 (h : a0 ⇒ a1) (σ : fin -> tm) :
  (a0[σ] ⇒ a1[σ]).
Proof. hauto l:on use:Par_refl, par_morphing. Qed.

Lemma par_morphing_star a0 a1 (h : a0 ⇒* a1) (σ0 σ1 : fin -> tm) :
  (forall i, (σ0 i) ⇒ (σ1 i)) ->
  (a0[σ0] ⇒* a1 [σ1]).
Proof.
  induction h.
  - move => h. apply @rtc_once. eauto using par_morphing, Par_refl.
  - move => h0.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    sfirstorder use:par_morphing, Par_refl.
Qed.

Lemma Par_Coherent a b :
  (a ⇒ b) -> Coherent a b.
Proof. hauto lq:on use:@rtc_once, @rtc_refl. Qed.

Lemma Coherent_morphing a0 a1 (h : Coherent a0 a1) (σ0 σ1 : fin -> tm) :
  (forall i, (σ0 i) ⇒ (σ1 i)) ->
  Coherent (a0[σ0]) (a1[σ1]).
Proof.
  hauto l:on use:par_morphing_star, Par_refl, Par_Coherent unfold:Coherent.
Qed.

Lemma par_subst_star a0 a1 (h : a0 ⇒* a1) (σ : fin -> tm) :
  (a0 [σ]) ⇒* (a1 [σ]).
Proof. hauto l:on use:par_morphing_star, Par_refl. Qed.

Lemma Coherent_subst_star a0 a1 (h : Coherent a0 a1) (σ : fin -> tm) :
  Coherent (a0[ σ]) (a1 [σ]).
Proof. hauto lq:on use:Coherent_morphing, Par_refl. Qed.

Derive Inversion Par_inv with (forall a b, a ⇒ b).

(* Takahashi translation *)
Function tstar (a : tm) :=
  match a with
  | var_tm i => a
  | tUniv _ => a
  | tVoid => a
  | tPi A B => tPi (tstar A) (tstar B)
  | tAbs a => tAbs (tstar a)
  | tApp (tAbs a) b =>  (tstar a) [(tstar b)..]
  | tApp a b => tApp (tstar a) (tstar b)
  | tTrue => tTrue
  | tFalse => tFalse
  | tIf tTrue b c => tstar b
  | tIf tFalse b c => tstar c
  | tIf a b c => tIf (tstar a) (tstar b) (tstar c)
  | tBool => tBool
  | tRefl => tRefl
  | tEq a b A => tEq (tstar a) (tstar b) (tstar A)
  | tJ t a b tRefl => tstar t
  | tJ t a b p => tJ (tstar t) (tstar a) (tstar b) (tstar p)
  end.

Lemma par_triangle a : forall b, (a ⇒ b) -> (b ⇒ tstar a).
Proof.
  apply tstar_ind; hauto lq:on inv:Par use:Par_refl,par_cong ctrs:Par.
Qed.

Lemma par_confluent : diamond Par.
Proof. hauto lq:on use:par_triangle unfold:diamond. Qed.

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

Add Relation tm Coherent
    reflexivity proved by Coherent_reflexive
    symmetry proved by Coherent_symmetric
    transitivity proved by Coherent_transitive
    as Coherent_rel.
