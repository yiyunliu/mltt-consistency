Require Import imports.

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
| P_Zero :
  (* ------- *)
  tZero ⇒ tZero
| P_Suc a b :
  a ⇒ b ->
  (* ---------- *)
  tSuc a ⇒ tSuc b
| P_Ind a0 a1 b0 b1 c0 c1:
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------- *)
  tInd a0 b0 c0 ⇒ tInd a1 b1 c1
| P_IndZero a0 a1 b:
  a0 ⇒ a1 ->
  (* ---------- *)
  tInd a0 b tZero ⇒ a1
| P_IndSuc a0 a1 b0 b1 c0 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------------------  *)
  tInd a0 b0 (tSuc c0) ⇒ b1 [(tInd a1 b1 c1) .: c1  ..]
| P_Nat :
  (* ---------- *)
  tNat ⇒ tNat
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
| P_Sig A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  tSig A0 B0 ⇒ tSig A1 B1
| P_Pack a0 a1 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  (tPack a0 b0) ⇒ (tPack a1 b1)
| P_Let a0 b0 a1 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* --------------------- *)
  tLet a0 b0 ⇒ tLet a1 b1
| P_LetPack a0 b0 c0 a1 b1 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  tLet (tPack a0 b0) c0 ⇒ c1[b1 .: a1 ..]
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

Lemma P_IndSuc' a0 a1 b0 b1 c0 c1 t :
  t = b1 [(tInd a1 b1 c1) .: c1 ..] ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  (* ---------------------  *)
  tInd a0 b0 (tSuc c0) ⇒ t.
Proof. move => > ->. apply P_IndSuc. Qed.

Lemma P_LetPack' a0 b0 c0 a1 b1 c1 t :
  t = c1[b1 .: a1 ..] ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  tLet (tPack a0 b0) c0 ⇒ t.
Proof. move => > ->. apply P_LetPack. Qed.

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
    apply : P_IndSuc'; eauto; by asimpl.
  - move => *.
    apply : P_LetPack'; eauto; by asimpl.
Qed.

Lemma Pars_renaming a b (ξ : fin -> fin) :
  (a ⇒* b) -> (a⟨ξ⟩ ⇒* b⟨ξ⟩).
Proof. induction 1; hauto lq:on ctrs:rtc use:Par_renaming. Qed.

Local Fixpoint up_tm_tm_n n ξ :=
  if n is S n then up_tm_tm_n n (up_tm_tm ξ) else ξ.

Local Lemma Par_morphing_lift_n n (ξ0 ξ1 : fin -> tm)
  (h : forall i, (ξ0 i ⇒ ξ1 i)) :
  forall i, (up_tm_tm_n n ξ0 i ⇒ up_tm_tm_n n ξ1 i).
Proof.
  elim : n ξ0 ξ1 h =>//.
  move => n ih ξ0 ξ1 h=>//= i.
  apply : ih. move => [|i0]//=.
  by apply Par_refl.
  by apply Par_renaming.
Qed.

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
  - qauto db:par use: (Par_morphing_lift_n 1).
  - qauto l:on db:par use:(Par_morphing_lift_n 1).
  - move => a a0 b0 b1 h0 ih0 h1 ih1 σ0 σ h /=.
    apply P_AppAbs' with (a0 := a0 [up_tm_tm σ]) (b1 := b1 [σ]).
    by asimpl. hauto l:on unfold:Par_m use:Par_renaming inv:nat. eauto.
  - qauto db:par use:(Par_morphing_lift_n 2).
  - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc σ0 σ1 hσ /=.
    apply P_IndSuc' with
      (b1 := b1[up_tm_tm_n 2 σ1]) (a1 := a1[σ1]) (c1 := c1[σ1]);
      eauto => /=. by asimpl.
    sfirstorder use:(Par_morphing_lift_n 2).
  - hauto lq:on db:par use:(Par_morphing_lift_n 1).
  - qauto db:par use:(Par_morphing_lift_n 1).
  - qauto l:on ctrs:Par use:(Par_morphing_lift_n 2).
  - move => a0 b0 c0 a1 b1 c1 ha iha hb ihb hc ihc σ0 σ1 hσ /=.
    apply P_LetPack' with (a1 := a1[σ1]) (b1 := b1[σ1]) (c1 := c1[up_tm_tm (up_tm_tm σ1)]); eauto.
    by asimpl.
    sfirstorder use:(Par_morphing_lift_n 2).
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

(* Parallel reduction is contained in Coherent *)

Lemma Par_Coherent a b :
  (a ⇒ b) -> Coherent a b.
Proof. hauto lq:on use:@rtc_once, @rtc_refl. Qed.

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

Lemma Par_cong2 a0 a1 b0 b1 c0 c1 (h : a0 ⇒ a1) (h1 : b0 ⇒ b1) (h2 : c0 ⇒ c1) :
  (a0 [b0 .: c0 ..] ⇒ a1 [b1 .: c1 ..]).
Proof.
  apply Par_morphing=>//. case=>//.
  move => n. asimpl.
  case : n => // >. asimpl. apply Par_refl.
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

Lemma Pars_univ_inv i A (h : (tUniv i) ⇒* A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto q:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma Pars_sig_inv A B C (h : tSig A B ⇒* C) :
  exists A0 B0, C = tSig A0 B0 /\ (A ⇒* A0) /\ (B ⇒* B0).
Proof.
  move E : (tSig A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Coherent_univ_inj i j (h : Coherent (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:rtc use:Pars_univ_inv. Qed.


(* ------------------------------------------------------------ *)


Lemma P_IndZero_star a b c :
  (c ⇒* tZero) ->
  (tInd a b c  ⇒* a).
Proof.
  move E : tZero => v h.
  move : E.
  elim : c v / h.
  - move => *. subst.
    apply rtc_once. apply P_IndZero. apply Par_refl.
  - move => c c0 c1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : rtc_transitive; eauto.
    hauto lq:on use:@rtc_once,Par_refl ctrs:Par.
Qed.

Lemma P_IndSuc_star a b c c0 :
  (c ⇒* tSuc c0) ->
  (tInd a b c  ⇒* b[(tInd a b c0) .: c0 ..]).
Proof.
  move E : (tSuc c0) => v h.
  move : E.  elim : c v /h.
  - move=> > <- *.
    apply rtc_once. apply P_IndSuc; apply Par_refl.
  - move => c1 c2 c3 h0 h1 ih ?. subst.
    move /(_ eq_refl) : ih.
    apply rtc_l.
    hauto lq:on use:Par_refl ctrs:Par.
Qed.

Lemma P_IndSuc_star' a b c c0 t :
  b[(tInd a b c0) .: c0 ..] = t ->
  (c ⇒* tSuc c0) ->
  (tInd a b c  ⇒* t).
Proof. move => > <-. apply P_IndSuc_star. Qed.

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

Lemma P_LetPack_star t a b c :
  t ⇒* tPack a b ->
  tLet t c ⇒* c[b .: a ..].
Proof.
  move E : (tPack a b) => v h.
  move : a b c E.
  elim:t v/h.
  - move => *. subst.
    apply rtc_once. apply P_LetPack; apply Par_refl.
  - move => t0 t ? h0 h1 ih a b c ?. subst.
    specialize ih with (1 := eq_refl).
    apply : rtc_l; eauto.
    apply P_Let=>//. apply Par_refl.
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
  | tPi A B => tPi (tstar A) (tstar B)
  | tAbs a => tAbs (tstar a)
  | tApp (tAbs a) b =>  (tstar a) [(tstar b)..]
  | tApp a b => tApp (tstar a) (tstar b)
  | tZero => tZero
  | tSuc a => tSuc (tstar a)
  | tInd a b tZero => tstar a
  | tInd a b (tSuc c) => (tstar b) [(tInd (tstar a) (tstar b) (tstar c)) .: (tstar c)  .. ]
  | tInd a b c => tInd (tstar a) (tstar b) (tstar c)
  | tNat => tNat
  | tRefl => tRefl
  | tEq a b A => tEq (tstar a) (tstar b) (tstar A)
  | tJ t a b tRefl => tstar t
  | tJ t a b p => tJ (tstar t) (tstar a) (tstar b) (tstar p)
  | tLet (tPack a b) c => (tstar c)[(tstar b) .: (tstar a)..]
  | tLet a b => tLet (tstar a) (tstar b)
  | tSig A B => tSig (tstar A) (tstar B)
  | tPack a b => tPack (tstar a) (tstar b)
  end.

Lemma Par_triangle a : forall b, (a ⇒ b) -> (b ⇒ tstar a).
Proof.
  apply tstar_ind; hauto lq:on inv:Par use:Par_refl,Par_cong,Par_cong2 ctrs:Par.
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

Inductive Sub1 : tm -> tm -> Prop :=
| Sub_Var n :
  Sub1 (var_tm n) (var_tm n)
| Sub_Abs b :
  Sub1 (tAbs b) (tAbs b)
| Sub_App b a :
  Sub1 (tApp b a) (tApp b a)
| Sub_Zero :
  Sub1 tZero tZero
| Sub_Suc a :
  Sub1 (tSuc a) (tSuc a)
| Sub_Nat :
  Sub1 tNat tNat
| Sub_Ind a b c:
  Sub1 (tInd a b c) (tInd a b c)
| Sub_Eq a b A :
  Sub1 (tEq a b A) (tEq a b A)
| Sub_J t a b p :
  Sub1 (tJ t a b p) (tJ t a b p)
| Sub_Refl :
  Sub1 tRefl tRefl
| Sub_Univ i j :
  i <= j ->
  Sub1 (tUniv i) (tUniv j)
| Sub_Prod A0 B0 A1 B1 :
  Sub1 A1 A0 ->
  Sub1 B0 B1 ->
  Sub1 (tPi A0 B0) (tPi A1 B1)
| Sub_Sig A0 B0 A1 B1 :
  Sub1 A0 A1 ->
  Sub1 B0 B1 ->
  Sub1 (tSig A0 B0) (tSig A1 B1)
| Sub_Pack a b :
  Sub1 (tPack a b) (tPack a b)
| Sub_Let a b :
  Sub1 (tLet a b) (tLet a b).

Lemma Sub1_refl A : Sub1 A A.
Proof. elim : A; hauto ctrs:Sub1 solve+:lia. Qed.

Lemma Sub1_transitive A B : Sub1 A B -> forall C, (Sub1 C A -> Sub1 C B) /\ (Sub1 B C -> Sub1 A C).
Proof.
  move => h. elim : A B / h; hauto lq:on inv:Sub1 ctrs:Sub1 solve+:lia.
Qed.

Definition Sub A B :=
  exists A0 B0, A ⇒* A0 /\ B ⇒* B0 /\ Sub1 A0 B0.

Notation "A <: B" := (Sub A B)  (at level 70, no associativity).

Lemma Sub_reflexive A : Sub A A.
Proof. hauto lq:on ctrs:rtc use: Sub1_refl unfold:Sub. Qed.

Lemma Sub1_morphing A B (h : Sub1 A B) : forall ρ, Sub1 A[ρ] B[ρ].
Proof. elim : A B /h; hauto lq:on ctrs:Sub1 use:Sub1_refl solve+:lia. Qed.

Lemma Sub_morphing A B (h : Sub A B) : forall ρ, Sub A[ρ] B[ρ].
Proof. hauto lq:on use:Par_subst_star, Sub1_morphing unfold:Sub. Qed.

Derive Inversion sub1_inv with (forall A B, Sub1 A B).

Lemma Sub1_simulation A0 A1 (h : A0 ⇒ A1) : forall B0, (Sub1 A0 B0 -> exists B1, Sub1 A1 B1 /\ B0 ⇒ B1) /\ (Sub1 B0 A0 -> exists B1, Sub1 B1 A1 /\ B0 ⇒ B1).
Proof.
  elim : A0 A1 /h;
    match goal with
    | [|-context[tPi]] =>hauto lq:on rew:off ctrs:Sub1,Par inv:Sub1
    | [|-context[tSig]] =>hauto lq:on rew:off ctrs:Sub1,Par inv:Sub1
    | _ => hauto lq:on ctrs:Sub1, Par use:Sub1_refl inv:Sub1
    end.
Qed.

Lemma Sub1_simulation_reds A0 A1 (h : A0 ⇒* A1) : forall B0, (Sub1 A0 B0 -> exists B1, Sub1 A1 B1 /\ B0 ⇒* B1) /\ (Sub1 B0 A0 -> exists B1, Sub1 B1 A1 /\ B0 ⇒* B1).
Proof.
  elim : A0 A1 /h.
  - sfirstorder.
  - move => A0 A1 A2 hr0 hr1 ih B0.
    split => hB0.
    + move : Sub1_simulation hr0 hB0. repeat move/[apply].
      move /(_ B0) => [+ _]. move/[apply]. hauto lq:on rew:off ctrs:rtc.
    + move : Sub1_simulation hr0 hB0. repeat move/[apply].
      move /(_ B0) => [_]. move/[apply]. hauto lq:on rew:off ctrs:rtc.
Qed.

Lemma Sub_transitive A B C : Sub A B -> Sub B C -> Sub A C.
Proof.
  rewrite /Sub.
  move => [A0][B0][h0][h1]h2[B1][C0][h3][h4]h5.
  have [B'[? ?]] : exists B', B0 ⇒* B' /\ B1 ⇒* B' by sfirstorder use:Pars_confluent.
  have [A' [??]] : exists A',Sub1 A' B' /\ A0 ⇒* A' by hauto l:on use:Sub1_simulation_reds.
  have [C' [??]] : exists C',Sub1 B' C' /\ C0 ⇒* C' by hauto l:on use:Sub1_simulation_reds.
  exists A', C'. repeat split=>//; last by hauto lq:on use:Sub1_transitive.
  all : eauto using rtc_transitive.
Qed.

Lemma Sub_univ_inj i j : tUniv i <: tUniv j -> i <= j.
Proof.
  rewrite /Sub.
  move => [A0][B0][+[]].
  move /Pars_univ_inv => ? /Pars_univ_inv ?. subst.
  by inversion 1.
Qed.

Lemma Sub_pi_inj A B A0 B0 : tPi A B <: tPi A0 B0 ->
  A0 <: A /\ B <: B0.
Proof.
  rewrite /Sub.
  move => [?][?][/Pars_pi_inv].
  move => [A'][B'][?][? ?]. subst.
  move =>[/Pars_pi_inv].
  move => [A''][B''][?][? ?]. subst.
  hauto lq:on ctrs:Sub1 inv:Sub1.
Qed.

Lemma Sub_eq_inj a b A a0 b0 A0 (h : Sub (tEq a b A) (tEq a0 b0 A0)) : Coherent a a0 /\ Coherent b b0 /\ Coherent A A0.
Proof.
  move : h. rewrite /Sub.
  move => [A1][A2][/Pars_eq_inv h0][/Pars_eq_inv h1]h2.
  rewrite /Coherent.
  hauto lq:on rew:off inv:Sub1.
Qed.

Lemma Sub_sig_inj A B A0 B0 : Sub (tSig A B) (tSig A0 B0) ->
  A <: A0 /\ B <: B0.
Proof.
  rewrite /Sub.
  move => [?][?][/Pars_sig_inv].
  move => [A'][B'][->][? ?].
  move => [/Pars_sig_inv].
  move => [A''][B''][->][? ?].
  hauto lq:on inv:Sub1.
Qed.

Lemma Sub_renaming A B : forall ξ, A <: B -> A⟨ξ⟩ <: B⟨ξ⟩.
Proof. move => ξ + /ltac:(substify). move /Sub_morphing. by apply. Qed.

Lemma Sub1_Sub A B : Sub1 A B -> Sub A B.
Proof. sfirstorder ctrs:rtc unfold:Sub. Qed.

Lemma Par_Sub a b :
  a ⇒ b -> a <: b /\ b <: a.
Proof.
  hauto lq:on use:Sub1_refl ctrs:rtc unfold:Sub.
Qed.

Lemma Coherent_Sub a b : a ⇔ b -> a <: b.
Proof. sfirstorder use:Sub1_refl unfold:Coherent, Sub. Qed.

Module HRed.
  Inductive R : tm -> tm ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (tApp (tAbs a) b)  (subst_tm (scons b var_tm) a)

  | IndZero a b :
    R (tInd a b tZero) a

  | IndSuc a b c :
    R (tInd a b (tSuc c)) (subst_tm (scons (tInd a b c) (scons c var_tm)) b)

  | JRefl t a b :
    (* ---------- *)
    R (tJ t a b tRefl) t

  | LetPack a b c :
    R (tLet (tPack a b) c) c[b .: a ..]

  (*************** Congruence ********************)
  | AppCong a0 a1 b :
    R a0 a1 ->
    R (tApp a0 b) (tApp a1 b)

  | IndCong a b c0 c1 :
    R c0 c1 ->
    R (tInd a b c0) (tInd a b c1)

  | JCong t a b p0 p1 :
    R p0 p1 ->
    R (tJ t a b p0) (tJ t a b p1)

  | LetCong a0 a1 b :
    R a0 a1 ->
    R (tLet a0 b) (tLet a1 b).

  Lemma ToPar a b : R a b -> a ⇒ b.
  Proof. induction 1; qauto l:on ctrs:Par use:Par_refl. Qed.

End HRed.

Module HRed01.
  Definition R := clos_refl _ HRed.R.
End HRed01.

Module HRedProp.
  Lemma commutativity a b c :
    HRed.R a b -> Par a c -> exists d, Par b d /\ HRed01.R c d.
  Proof.
    move => h. move : c. elim : a b /h.
    - hauto lq:on ctrs:clos_refl,HRed.R use:Par_cong inv:Par.
    - hauto lq:on ctrs:clos_refl,HRed.R inv:Par.
    - move => a b c u.
      elim /Par_inv => //=_.
      + move => a0 a1 b0 b1 c0 ? ha hb hc [*]. subst.
        elim /Par_inv : hc => //=_.
        move => a0 c1 h [*]. subst.
        exists b1 [tInd a1 b1 c1 .: (c1 ..)].
        hauto lq:on ctrs:clos_refl, HRed.R, Par use:Par_cong2.
      + move => a0 a1 b0 b1 c0 c1 ha hb hc [*]. subst.
        exists b1 [tInd a1 b1 c1 .: (c1 ..)]. split. hauto lq:on ctrs:Par use:Par_cong2.
        apply r_refl.
    - hauto lq:on ctrs:clos_refl,HRed.R inv:Par.
    - hauto lq:on ctrs:clos_refl,HRed.R use:Par_cong2 inv:Par.
    - sauto q:on.
    - sauto q:on.
    - sauto q:on.
    - sauto q:on.
  Qed.
End HRedProp.
