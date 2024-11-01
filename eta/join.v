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
  a0 ⇒ a1 ->
  (* -------------------- *)
  tAbs a0 ⇒ tAbs a1
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  tApp a0 b0 ⇒ tApp a1 b1
| P_AppAbs a a0 b0 b1 :
  a ⇒ tAbs a0 ->
  b0 ⇒ b1 ->
  (* ---------------------------- *)
  tApp a b0 ⇒ a0[b1..]
| P_True :
  (* ------- *)
  tTrue ⇒ tTrue
| P_False :
  (* ---------- *)
  tFalse ⇒ tFalse
| P_If a0 a1 b0 b1 c0 c1:
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------- *)
  tIf a0 b0 c0 ⇒ tIf a1 b1 c1
| P_IfTrue a b0 b1 c0 c1 :
  a ⇒ tTrue ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------- *)
  tIf a b0 c0 ⇒ b1
| P_IfFalse a b0 b1 c0 c1 :
  a ⇒ tFalse ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------- *)
  tIf a b0 c0 ⇒ c1
| P_Bool :
  (* ---------- *)
  tBool ⇒ tBool
| P_Refl :
  (* ---------- *)
  tRefl ⇒ tRefl
| P_Eq a0 b0 A0 a1 b1 A1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  A0 ⇒ A1 ->
  (* ----------------------- *)
  tEq a0 b0 A0 ⇒ tEq a1 b1 A1
| P_J t0 p0 t1 p1 :
  t0 ⇒ t1 ->
  p0 ⇒ p1 ->
  (* ----------------------- *)
  tJ t0 p0 ⇒ tJ t1 p1
| P_JRefl t0 p t1 :
  t0 ⇒ t1 ->
  p ⇒ tRefl ->
  (* ------------------ *)
  tJ t0 p ⇒ t1
| P_AbsEta a0 a1 :
  a0 ⇒ a1 ->
  (* -------------------------------------- *)
  tAbs (tApp a0⟨↑⟩ (var_tm var_zero)) ⇒ a1
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

(* convenience introduction form for P_AppAbs',Eta' *)
Lemma P_AppAbs' a a0 b0 b b1 :
  b = a0 [b1..] ->
  (a ⇒ tAbs a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp a b0) ⇒ b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma P_AbsEta' b a0 a1 :
  b = (tAbs (tApp (ren_tm shift a0) (var_tm var_zero))) ->
  Par a0 a1 ->
  Par b a1.
Proof. move => ->. apply P_AbsEta. Qed.

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
  - move => *.
    apply : P_AbsEta'; eauto. by asimpl.
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
  elim : a b / h0 => /=; eauto with par.
  - hauto lq:on db:par use:Par_morphing_lift unfold:Par_m.
  - hauto lq:on db:par use:Par_morphing_lift unfold:Par_m.
  - move => *; apply : P_AppAbs'; eauto; by asimpl.
  - move => *; apply : P_AbsEta'; eauto. by asimpl.
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
    apply rtc_once. apply : P_IfTrue; apply Par_refl.
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
    apply rtc_once. apply : P_IfFalse; apply Par_refl.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    apply @rtc_once.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_JRefl_star t p :
  (p ⇒* tRefl)  ->
  ((tJ t p) ⇒* t).
Proof.
  move E : tRefl => v h.
  move : E.
  elim : p v / h.
  - move => *. subst.
    apply rtc_once. apply : P_JRefl; apply Par_refl.
  - move => x y z h0 h1 ih ?; subst.
    move /(_ ltac:(done)) in ih.
    apply : rtc_l; eauto.
    apply P_J; sfirstorder use:Par_refl.
Qed.


(* ------------------------------------------------------------ *)

(* Derived inversion principle for "Par" that doesn't
   generate free names with use. *)
Derive Inversion Par_inv with (forall a b, a ⇒ b).

(* Induction metric for terms  *)
Definition size_tm : tm -> nat.
  apply tm_rec.
  exact (fun _ => 1).
  exact (fun _ a => 1 + a).
  exact (fun _ a _ b => 1 + a + b).
  exact (fun _ a _ b => 1 + a + b).
  exact 1.
  exact (fun _ => 1).
  exact 1.
  exact 1.
  exact (fun _ a _ b _ c => 1 + a + b + c).
  exact 1.
  exact (fun _ a _ b _ c => 1 + a + b + c).
  exact (fun _ a _ b => 1 + a + b).
  exact 1.
Defined.

Lemma ren_tm_size_tm a ξ : size_tm a = size_tm (ren_tm ξ a).
Proof. elim : a ξ; scongruence. Qed.

Lemma induction_size_tm_lt
  : forall P : tm -> Prop,
       (forall x : tm, (forall y : tm, size_tm y < size_tm x -> P y) -> P x) ->
       forall a : tm, P a.
Proof.
  have := well_founded_ltof  tm size_tm.
  move => + + + a.
  move /(_ a). elim; hauto lq:on.
Qed.

Local Ltac apply_ih ih := move /ih; elim; last by (simpl; lia).

(* Characterization of variable freeness conditions *)
Definition tm_i_free a i := exists ξ ξ0, ξ i <> ξ0 i /\ ren_tm ξ a = ren_tm ξ0 a.

Lemma subst_differ_one_ren_up i ξ0 ξ1 :
  (forall j, i <> j -> ξ0 j = ξ1 j) ->
  (forall j, S i <> j -> upRen_tm_tm ξ0 j =  upRen_tm_tm ξ1 j).
Proof. qauto l:on inv:nat simp+:asimpl. Qed.

Lemma tm_free_ren_any a i :
  tm_i_free a i ->
  forall ξ0 ξ1, (forall j, i <> j -> ξ0 j = ξ1 j) ->
             ren_tm ξ0 a = ren_tm ξ1 a.
Proof.
  rewrite /tm_i_free.
  move => [+ [+ [+ +]]].
  elim : a i=>//.
  - hauto q:on.
  - move => a iha i ρ0 ρ1 hρ [] => h ξ0 ξ1 hξ /=.
    f_equal. move /subst_differ_one_ren_up in hξ.
    move /(_ (S i)) in iha.
    move : iha h; move/[apply].
    apply=>//. asimpl. sfirstorder.
  - hauto lq:on rew:off.
  - move => A ihA a iha i ρ0 ρ1 hρ [] => ? h ξ0 ξ1 hξ /=.
    f_equal; first by eauto.
    move /subst_differ_one_ren_up in hξ.
    move /(_ (S i)) in iha.
    move : iha h; move/[apply].
    apply=>//. asimpl. sfirstorder.
  - hauto lq:on rew:off.
  - hauto lq:on rew:off.
  - hauto lq:on rew:off.
Qed.

(* ------------------ antirenaming ------------------------- *)

(* Next we show that if a renamed term reduces, then
   we can extract the unrenamed term from the derivation. *)

Lemma Par_antirenaming (a b0 : tm) (ξ : nat -> nat)
  (h : Par (ren_tm ξ a) b0) : exists b, b0 = ren_tm ξ b /\ Par a b.
Proof.
  elim /induction_size_tm_lt : a b0 ξ h.
  case => //.
  - move => i _ a ξ. simpl.
    elim /Par_inv=>// h ?[] *. subst.
    exists (var_tm i). eauto with par.
  - move => a ih c ξ.
    elim /Par_inv=>// _.
    + move => a0 a1 + [] *. subst.
      apply_ih ih => a0 [? ?]. subst.
      exists (tAbs a0). eauto with par.
    + move => a0 a1 h0 [].
      case : a ih=>// b0 b1 ih [] h1.
      case : b1 ih =>//.
      case => // ih _ ?. subst.
      move  :(h1).
      move /(f_equal (ren_tm (0 .: id))).
      asimpl => ?. subst.
      asimpl in h1.
      have [b0' ?] : exists b0', ren_tm shift b0' = b0.
      {
        exists (ren_tm (0 .: id) b0).
        asimpl.
        transitivity (ren_tm (0 .: shift) b0); last by (substify; asimpl).
        apply tm_free_ren_any with (i := 0). sfirstorder.
        qauto l:on inv:nat.
      }
      subst.
      asimpl in h0.
      move : h0.
      move /ih.
      elim; cycle 1.
      simpl. rewrite -ren_tm_size_tm. lia.
      move => b1' [? ?]; subst.
      exists b1'. eauto with par.
  - move => b a ih ? ξ.
    elim /Par_inv=>//.
    + move => ? a0 a1 b0 b1 + + [] *. subst.
      apply_ih ih => b0 [? ?].
      apply_ih ih => b2 [? ?]. subst.
      exists (tApp b0 b2). hauto lq:on ctrs:Par.
    + move => ? a0 a1 b0 b1 + + [] *. subst.
      apply_ih ih => t0 [+ +]. case : t0=>// t0 [] ? ?. subst.
      apply_ih ih => t1 [? ?]. subst.
      exists (subst_tm (t1..) t0). split; [by asimpl | eauto using P_AppAbs].
  - move => A B ih? ξ.
    elim /Par_inv => // ? A0 A1 B0 B1 + + [] *; subst.
    apply_ih ih => A0 [? ?].
    apply_ih ih => B0 [? ?]. subst.
    exists (tPi A0 B0). eauto with par.
  - hauto lq:on dep:on inv:Par ctrs:Par.
  - move => n _ ? ?.
    elim /Par_inv=>//.
    move => *. subst. eauto with par.
  - hauto lq:on dep:on inv:Par ctrs:Par.
  - hauto lq:on dep:on inv:Par ctrs:Par.
  - move => a b c ih ? ξ.
    elim /Par_inv=>// ?.
    + move => a0 a1 b0 b1 c0 c1 + + + [] *. subst.
      apply_ih ih =>a2 [? ?].
      apply_ih ih =>b2 [? ?].
      apply_ih ih =>c2 [? ?]. subst.
      exists (tIf a2 b2 c2). eauto with par.
    + move => a0 b0 b1 c0 c1 + + + [] *. subst.
      apply_ih ih => a2 [? ?].
      have ? : a2 = tTrue by hauto q:on drew:off inv:tm.
      apply_ih ih => b2 [? ?].
      apply_ih ih => c2 [? ?]. subst.
      exists (b2). eauto with par.
    + move => a0 b0 b1 c0 c1 + + + [] *. subst.
      apply_ih ih => a2 [? ?].
      have ? : a2 = tFalse by hauto q:on drew:off inv:tm.
      apply_ih ih => b2 [? ?].
      apply_ih ih => c2 [? ?]. subst.
      exists (c2). eauto with par.
  - hauto lq:on dep:on inv:Par ctrs:Par.
  - move => a b A ih ? ξ.
    elim /Par_inv=>// ? ? ? ? a0 b0 A0 + + + [] *. subst.
    apply_ih ih => a1 [? ?].
    apply_ih ih => b1 [? ?].
    apply_ih ih => c1 [? ?]. subst.
    exists (tEq a1 b1 c1). eauto with par.
  - move => t p ih ? ξ.
    elim /Par_inv=>// ?.
    + move => t0 p0 ? ? + + []*. subst.
      apply_ih ih => t1 [? ?].
      apply_ih ih => p1 [? ?]. subst.
      exists (tJ t1 p1). eauto with par.
    + move => ? ? t1 + + [] *. subst.
      apply_ih ih => t2 [? ?].
      apply_ih ih => p2 [+ +]. subst.
      case : p2 => // _ ?.
      exists t2. eauto with par.
  - hauto lq:on dep:on inv:Par ctrs:Par.
Qed.

(* ------------------------------------------------------------ *)

(* We want to show that Coherent is an equivalence relation. But,
   to show that it is transitive, we need to show that parallel
   reduction is confluent. *)

Local Ltac apply_ih' ih :=
  move :(ih); repeat move/[apply]; elim;
  last by (simpl; rewrite -?ren_tm_size_tm; lia).

Local Ltac apply_ih'' ih :=
  move /ih; move /(_ ltac:(simpl; lia)).

(* Simple helper function *)
Lemma par_var_eq i a : Par (var_tm i) a -> a = var_tm i.
Proof. elim /Par_inv=>//. Qed.

Lemma Par_confluent : diamond Par.
Proof.
  rewrite /diamond.
  elim /induction_size_tm_lt.
  move => a ih b b0.
  elim /Par_inv.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h A0 A1 B0 B1 hA0 hB0 ? ?. subst.
    elim /Par_inv=>// => h0 A2 A3 B2 B3 + + [] *. subst.
    move : hA0. apply_ih' ih => A [? ?].
    move : hB0. apply_ih' ih => B [].
    eauto with par.
  - move => h0 a0 a1 h1 ? ?. subst.
    elim /Par_inv=>//.
    + move => h2 a2 a3 + [] *. subst.
      move : h1. apply_ih' ih => + [].
      eauto with par.
    + move => h2 a2 a3 h3 [] *. subst.
      elim /Par_inv : h1=>//.
      * move => h4 a0 a3 b1 b2 h5 + [] *. subst.
        move /par_var_eq =>?. subst.
        move /Par_antirenaming : h5 => [a3' [? +]]. subst.
        move : h3. apply_ih' ih => + [].
        eauto with par.
      * move => h4 a0 a3 b1 b2 + + [] *. subst.
        move /Par_antirenaming => [] + [].
        case =>// a3' [] ?. subst=> + /par_var_eq ?. subst.
        asimpl in h4.
        move : h3. apply_ih' ih => + []. eauto with par.
  - move => h0 a0 a1 b1 b2 h1 h2 ? ?. subst.
    elim /Par_inv =>//.
    + move => h3 a2 a3 b3 b4 + + [] *. subst.
      move : h1. apply_ih' ih => a [? ?].
      move : h2. apply_ih' ih => b [+ +].
      eauto with par.
    + move => h3 a2 a3 b3 b4 + + [] *. subst.
      move : h1. apply_ih' ih => a [h4 h5].
      move : h2. apply_ih' ih => b [h6 h7].
      elim /Par_inv : h5=>//.
      * hauto lq:on rew:off use:Par_cong ctrs:Par.
      * move => h8 a2 a4 h9 [] *. subst.
        asimpl in h3.
        eauto with par.
  - move => h0 a0 a1 b1 b2 h1 h2 ? ?. subst.
    elim /Par_inv =>//.
    + move => h3 a2 a3 b3 b4 + + [] *. subst.
      move : h1. apply_ih' ih => a [h4 h5].
      move : h2. apply_ih' ih => b [? ?] {ih}.
      move : h4. elim /Par_inv=>//.
      * move => h6 a2 a4 h7 [] ? ?. subst.
        hauto lq:on rew:off use:Par_cong ctrs:Par.
      * move => h6 a2 a4 h7 [] *. subst.
        asimpl in h0.
        eauto with par.
    + move => h3 a2 a3 b3 b4 + + [] *. subst.
      move : h1. apply_ih' ih => a [h4 h5].
      move : h2. apply_ih' ih => b [h00 h01].
      elim /Par_inv : h4 =>//; elim /Par_inv : h5 => //.
      * hauto lq:on rew:off use:Par_cong ctrs:Par.
      * move => ? a2 a4 ? [] ? ? ? a5 a6 ? [] *. subst.
        asimpl in h3.
        eauto using Par_cong with par.
      * move => ? a2 a4 ? [?] ? ? a5 a6 ? [] *. subst.
        asimpl.
        eauto using Par_cong with par.
      * move => ? a2 a4 ? [?] ? ? a5 a6 ? [] *. subst.
        asimpl.
        eauto using Par_cong with par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h0 a0 a1 b1 b2 c0 c1 + + + ? ?. subst.
    apply_ih'' ih => iha. apply_ih'' ih => ihb. apply_ih'' ih => ihc.
    hauto lq:on ctrs:Par inv:Par.
  - move => h a0 b1 b2 c0 c1 + + + ? ?. subst.
    do 3 (apply_ih'' ih => ?). move {ih}.
    hauto q:on ctrs:Par inv:Par.
  - move => h a0 b1 b2 c0 c1 + + + ? ?. subst.
    do 3 (apply_ih'' ih => ?). move {ih}.
    hauto q:on ctrs:Par inv:Par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h a0 a1 A0 a2 b3 A1 + + + ? ?. subst.
    do 3 (apply_ih'' ih => ?).
    hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h1 t0 p0 t1 p1 + + ? ? +. subst.
    do 2 (apply_ih'' ih => ?).
    hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h t0 p t1 + + ? ?. subst.
    do 2 (apply_ih'' ih => ?).
    hauto lq:on rew:off inv:Par ctrs:Par.
  - move => h0 a0 a1 h1 ? ?. subst.
    elim /Par_inv=>//.
    + move => h2 a1 a2 h3 [?] ?. subst.
      move : h3.
      elim /Par_inv=>//.
      * move => h4 a1 a3 b0 b1 h5 + [] *. subst.
        move /par_var_eq => ?. subst.
        move /Par_antirenaming : h5 => [a3' [? +]]. subst.
        move : h1. apply_ih' ih => c [? ?].
        eauto with par.
      * move => h4 a1 a3 b0 b1 h5 + [] *. subst.
        move /par_var_eq => ?. subst.
        move / Par_antirenaming : h5 => [+ []].
        case => ///= a3' [?] h6. subst.
        asimpl. move : h1 h6. apply_ih' ih => c [? ?].
        eauto with par.
    + move => h2 a1 a2 h3 [] + ?. subst.
      move/(f_equal (ren_tm (0 .: id))).
      asimpl => ?. subst.
      move : h1 h3. apply_ih' ih. eauto.
Qed.

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
