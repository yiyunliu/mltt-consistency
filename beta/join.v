From WR Require Import imports.
Require Export Setoid.

Definition is_bool_val a :=
  match a with
  | tTrue => true
  | tFalse => true
  | _ => false
  end.

(* ------------------------------------------------------------ *)

(* Parallel reduction: "a ⇒ b" the building block 
   of our untyped, definitional equality.

   This relation nondeterminstically does one-step
   of beta-reduction in parallel throughout the term. 

   Importantly, this relation is confluent (i.e. satisfies 
   the diamond property), which leads to an easy proof of
   confluence for its reflexive-transitive closure "⇒*".

 *)
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
  (* ---------- *)
  tBool ⇒ tBool
| P_Refl :
  (* ---------- *)
  tRefl ⇒ tRefl
| P_Eq a0 b0 A0 a1 b1 A1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (A0 ⇒ A1) ->
  (* ---------- *)
  (tEq a0 b0 A0) ⇒ (tEq a1 b1 A1)
| P_J t0 a0 b0 p0 t1 a1 b1 p1 :
  (t0 ⇒ t1) ->
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (p0 ⇒ p1) ->
  (* ---------- *)
  (tJ t0 a0 b0 p0) ⇒ (tJ t1 a1 b1 p1)
| P_JRefl t0 a b t1 :
  (t0 ⇒ t1) ->
  (* ---------- *)
  (tJ t0 a b tRefl) ⇒ t1
where "A ⇒ B" := (Par A B).

#[export]Hint Constructors Par : par.

(* The reflexive, transitive closure of parallel reduction. *)

Infix "⇒*" := (rtc Par) (at level 60, right associativity).

(* Two types are Coherent when they reduce to a common type. *)

Definition Coherent a0 a1 := (exists b, a0 ⇒* b /\ a1 ⇒* b).
Infix "⇔" := Coherent (at level 70, no associativity).

(* ------------------------------------------------------------ *)

(* Parallel reduction is reflexive *)

Lemma Par_refl (a : tm) : a ⇒ a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

(* Parallel reduction is contained in Coherent *)

Lemma Par_Coherent a b :
  (a ⇒ b) -> Coherent a b.
Proof. hauto lq:on use:@rtc_once, @rtc_refl. Qed.


(* ------------------------------------------------------------ *)

(* A top-level beta-reduction is a parallel reduction *)
Lemma P_AppAbs_cbn (a b b0 : tm) :
  b0 = a [b..] ->
  (tApp (tAbs a) b) ⇒ b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

(* convenience introduction form for P_AppAbs' *)
Lemma P_AppAbs' a a0 b0 b b1 :
  b = a0 [b1..] ->
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp (tAbs a) b0) ⇒ b.
Proof. hauto lq:on use:P_AppAbs. Qed.


(* ------------------------------------------------------------ *)

(* Par (⇒), Pars (⇒* ), and ⇔ are closed under renaming *)

Lemma Par_renaming a b (ξ : fin -> fin) :
  (a ⇒ b) -> (a⟨ξ⟩ ⇒ b⟨ξ⟩).
Proof.
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  - move => *.
    apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma Pars_renaming a b (ξ : fin -> fin) :
  (a ⇒* b) -> (a⟨ξ⟩ ⇒* b⟨ξ⟩).
Proof. induction 1; hauto lq:on ctrs:rtc use:Par_renaming. Qed.

Lemma Coherent_renaming a b (ξ : fin -> fin) :
  Coherent a b ->
  Coherent a⟨ξ⟩ b⟨ξ⟩.
Proof. hauto lq:on rew:off use:Pars_renaming. Qed.

Local Lemma Par_morphing_lift (ξ0 ξ1 : fin -> tm)
  (h : forall i, (ξ0 i ⇒ ξ1 i)) :
  forall i, (up_tm_tm ξ0 i ⇒ up_tm_tm ξ1 i).
Proof. case => [|i]; first by constructor. asimpl. by apply Par_renaming. Qed.

(* ------------------------------------------------------------ *)

(* Now we want to show all of the ways that these relations are closed 
   under substitution. *)

(* First, we extend the Par, Pars and Coherent relations to substitutions *)

Definition Par_m (σ0 σ1 : fin -> tm) := (forall i, (σ0 i) ⇒ (σ1 i)).

Infix "⇒ς"  := Par_m (at level 70, right associativity).
Infix "⇒ς*" := (rtc Par_m) (at level 70, right associativity).

Definition Coherent_m σ0 σ1 :=
  exists σ, (σ0 ⇒ς* σ) /\ (σ1 ⇒ς* σ).

(* Morphing lemmas *)

Lemma Par_morphing a b (σ0 σ1 : fin -> tm)
  (h : σ0 ⇒ς σ1) :
  (a ⇒ b) -> 
  (a[σ0] ⇒ b[σ1]).
Proof.
  move => h0.
  move : σ0 σ1 h.
  elim : a b / h0; try solve [simpl; eauto with par].
  - qauto db:par use: Par_morphing_lift.
  - qauto l:on db:par use:Par_morphing_lift.
  - move => a a0 b0 b1 h0 ih0 h1 ih1 σ0 σ h /=.
    apply P_AppAbs' with (a0 := a0 [up_tm_tm σ]) (b1 := b1 [σ]).
    by asimpl. hauto l:on unfold:Par_m use:Par_renaming inv:nat. eauto.
  - hauto lq:on db:par use:Par_morphing_lift.
Qed.


Lemma Par_morphing_star a0 a1 (h : a0 ⇒* a1) (σ0 σ1 : fin -> tm) :
  (σ0 ⇒ς σ1) ->
  (a0[σ0] ⇒* a1 [σ1]).
Proof.
  induction h.
  - move => h. apply @rtc_once. eauto using Par_morphing, Par_refl.
  - move => h0.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    sfirstorder use:Par_morphing, Par_refl.
Qed.

Lemma Coherent_morphing a0 a1 (h : Coherent a0 a1) (σ0 σ1 : fin -> tm) :
  (σ0 ⇒ς σ1) ->
  Coherent (a0[σ0]) (a1[σ1]).
Proof.
  hauto l:on use:Par_morphing_star, Par_refl, 
    Par_Coherent unfold:Coherent, Par_m.
Qed.

Lemma Pars_morphing a b (σ0 σ1 : fin -> tm)
  (h : σ0 ⇒ς* σ1) :
  (a ⇒ b) ->
  (a [σ0]) ⇒* (b[σ1]).
Proof.
  move : a b.
  elim : σ0 σ1 / h.
  - sfirstorder unfold:Par_m use:Par_morphing, @rtc_once, Par_refl.
  - hauto lq:on unfold:Par_m use:Par_morphing, Par_refl ctrs:rtc.
Qed.


Lemma Pars_morphing_star a b (σ0 σ1 : fin -> tm)
  (h : σ0 ⇒ς* σ1)
  (h0 : a ⇒* b) :
  (a [σ0] ⇒* b[σ1]).
Proof.
  elim : a b / h0.
  - sfirstorder use:Pars_morphing, Par_refl.
  - move => x y z /[swap] _.
    move : Pars_morphing (rtc_refl Par_m σ0); repeat move /[apply].
    apply rtc_transitive.
Qed.

Lemma Coherent_morphing_star a b σ0 σ1
  (h : Coherent_m σ0 σ1)
  (h0 : Coherent a b) :
  Coherent (a[σ0]) (b[σ1]).
Proof.
  hauto q:on use:Pars_morphing_star unfold:Coherent.
Qed.



(* These two lemmas allow us to create substitutions
   that are related by paralell reduction. *)

Lemma good_Pars_morphing_ext a b σ0 σ1
  (h : a ⇒* b) :
  (σ0 ⇒ς* σ1) -> 
  ((a .: σ0) ⇒ς* (b .: σ1)).
Proof.
  elim : a b /h.
  - move => a.
    move => h.
    elim : σ0 σ1 / h; first by sfirstorder.
    move => σ0 σ1 σ2 h h1.
    apply rtc_transitive. apply rtc_once.
    qauto l:on unfold:Par_m ctrs:rtc inv:nat use:Par_refl.
  - move => x y z ha hb /[apply].
    apply rtc_transitive. apply rtc_once.
    hauto lq:on unfold:Par_m inv:nat use:Par_refl.
Qed.

Lemma good_Pars_morphing_ext2 a0 b0 a1 b1 σ0 σ1
  (h : a0 ⇒* b0) (h1 : a1 ⇒*  b1) :
  (σ0 ⇒ς* σ1) -> 
  ((a0 .: (a1 .: σ0)) ⇒ς* (b0 .: (b1 .: σ1))).
Proof. sfirstorder use:good_Pars_morphing_ext. Qed.


(* The three relations are closed under substitution *)

Lemma Par_subst a0 a1 (h : a0 ⇒ a1) (σ : fin -> tm) :
  (a0[σ] ⇒ a1[σ]).
Proof. hauto l:on unfold:Par_m use:Par_refl, Par_morphing. Qed.

Lemma Par_subst_star a0 a1 (h : a0 ⇒* a1) (σ : fin -> tm) :
  (a0 [σ]) ⇒* (a1 [σ]).
Proof. hauto l:on use:Par_morphing_star, Par_refl unfold:Par_m. Qed.

Lemma Coherent_subst_star a0 a1 (h : Coherent a0 a1) (σ : fin -> tm) :
  Coherent (a0[σ]) (a1 [σ]).
Proof. hauto lq:on use:Coherent_morphing, Par_refl unfold:Par_m. Qed.


(* The relations are also closed under single substitution  *)

Lemma Par_cong a0 a1 b0 b1 (h : a0 ⇒ a1) (h1 : b0 ⇒ b1) :
  (a0 [b0..] ⇒ a1 [b1..]).
Proof.
  apply Par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.


Local Lemma Coherent_cong_helper : forall a0 c, (a0 ⇒* c) -> (a0.. ⇒ς* c..).
Proof.
  move => a0 c h2.
  elim : a0 c / h2.
    sfirstorder.
    move => a b c ? ?.
    apply rtc_transitive with (y := b..).
    sauto lq:on unfold:Par_m inv:nat use:Par_refl use:good_Pars_morphing_ext. 
Qed.

Lemma Coherent_cong a0 a1 b0 b1
  (h : Coherent a0 a1)
  (h1 : Coherent b0 b1) :
  Coherent (a0 [b0..]) (a1 [b1..]).
Proof.
  apply Coherent_morphing_star=>//.
  sfirstorder use:Coherent_cong_helper.
Qed.




(* ------------------------------------------------------------ *)

(* Inversion lemmas *)

Lemma Pars_pi_inv A B C (h : (tPi A B) ⇒* C) :
  exists A0 B0, C = tPi A0 B0 /\ (A ⇒* A0) /\ (B ⇒* B0).
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Pars_eq_inv a b A C (h : (tEq a b A) ⇒* C) :
  exists a0 b0 A0, C = tEq a0 b0 A0 /\ a ⇒* a0 /\ b ⇒* b0 /\ A ⇒* A0.
Proof.
  move E : (tEq a b A) h => T h.
  move : a b A E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Coherent_pi_inj A B A0 B0 (h : Coherent (tPi A B) (tPi A0 B0)) :
  Coherent A A0 /\ Coherent B B0.
Proof. hauto q:on use:Pars_pi_inv. Qed.

Lemma Coherent_eq_inj a b A a0 b0 A0 (h : Coherent (tEq a b A) (tEq a0 b0 A0)) : Coherent a a0 /\ Coherent b b0 /\ Coherent A A0.
Proof. hauto q:on use:Pars_eq_inv. Qed.

Lemma Pars_univ_inv i A (h : (tUniv i) ⇒* A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto lq:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma Coherent_univ_inj i j (h : Coherent (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:rtc use:Pars_univ_inv. Qed.


(* ------------------------------------------------------------ *)


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


(* ------------------------------------------------------------ *)

(* Derived inversion principle for "Par" that doesn't 
   generate free names with use. *)
Derive Inversion Par_inv with (forall a b, a ⇒ b).

(* ------------------------------------------------------------ *)

(* We want to show that Coherent is an equivalence relation. But,
   to show that it is transitive, we need to show that parallel 
   reduction is confluent. *)

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

Lemma Par_triangle a : forall b, (a ⇒ b) -> (b ⇒ tstar a).
Proof.
  apply tstar_ind; hauto lq:on inv:Par use:Par_refl,Par_cong ctrs:Par.
Qed.

Lemma Par_confluent : diamond Par.
Proof. hauto lq:on use:Par_triangle unfold:diamond. Qed.

Lemma Pars_confluent : confluent Par.
Proof.
  sfirstorder use:Par_confluent, @diamond_confluent.
Qed.

(* Coherent is an equivalence relation *)

Lemma Coherent_reflexive a :
  Coherent a a.
Proof. hauto l:on ctrs:rtc. Qed.

Lemma Coherent_symmetric a b :
  Coherent a b -> Coherent b a.
Proof. sfirstorder. Qed.

Lemma Coherent_transitive a b c :
  Coherent a b -> Coherent b c -> Coherent a c.
Proof.
  have := Pars_confluent.
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
