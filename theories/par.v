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
Module Type par_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

Reserved Infix "⇒" (at level 60, right associativity).
Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  (var_tm i) ⇒ (var_tm i)
| P_Univ n :
  (* -------- *)
  (tUniv n) ⇒ (tUniv n)
| P_Pi ℓ0 A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  (tPi ℓ0 A0 B0) ⇒ (tPi ℓ0 A1 B1)
| P_Abs ℓ0 a0 a1 :
  (a0 ⇒ a1) ->
  (* -------------------- *)
  (tAbs ℓ0 a0) ⇒ (tAbs ℓ0 a1)
| P_App a0 a1 ℓ0 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  (tApp a0 ℓ0 b0) ⇒ (tApp a1 ℓ0 b1)
| P_AppAbs a a0 b0 b1 ℓ0 :
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp (tAbs ℓ0 a) ℓ0 b0) ⇒ (a0 [b1..])

| P_Void :
  tVoid ⇒ tVoid

| P_Absurd a b :
  a ⇒ b ->
  (* ---------- *)
  tAbsurd a ⇒ tAbsurd b

| P_Refl :
  (* ---------- *)
  tRefl ⇒ tRefl

| P_Eq ℓ0 a0 b0 A0 a1 b1 A1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (A0 ⇒ A1) ->
  (* ---------- *)
  (tEq ℓ0 a0 b0 A0) ⇒ (tEq ℓ0 a1 b1 A1)

| P_J t0 p0 t1 p1 :
  (t0 ⇒ t1) ->
  (p0 ⇒ p1) ->
  (* ---------- *)
  (tJ t0 p0) ⇒ (tJ t1 p1)

| P_JRefl t0 t1 :
  (t0 ⇒ t1) ->
  (* ---------- *)
  (tJ t0 tRefl) ⇒ t1

| P_Sig ℓ A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  tSig ℓ A0 B0 ⇒ tSig ℓ A1 B1

| P_Pack ℓ a0 a1 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  (tPack ℓ a0 b0) ⇒ (tPack ℓ a1 b1)

| P_Let ℓ0 ℓ1 a0 b0 a1 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* --------------------- *)
  tLet ℓ0 ℓ1 a0 b0 ⇒ tLet ℓ0 ℓ1 a1 b1

| P_LetPack ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  tLet ℓ0 ℓ1 (tPack ℓ0 a0 b0) c0 ⇒ c1[b1 .: a1 ..]

where "A ⇒ B" := (Par A B).
#[export]Hint Constructors Par : par.

(* The reflexive, transitive closure of parallel reduction. *)

Infix "⇒*" := (rtc Par) (at level 60, right associativity).

(* Derived inversion principle for "Par" that doesn't
   generate free names with use. *)
Derive Inversion Par_inv with (forall a b, a ⇒ b).

End par_sig.

Module par_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import join : par_sig lattice syntax).

(* ------------------------------------------------------------ *)

(* Parallel reduction is reflexive *)

Lemma Par_refl (a : tm) : a ⇒ a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

(* ------------------------------------------------------------ *)

(* A top-level beta-reduction is a parallel reduction *)
Lemma P_AppAbs_cbn (a b b0 : tm) ℓ0 :
  b0 = a [b..] ->
  (tApp (tAbs ℓ0 a) ℓ0 b) ⇒ b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

(* convenience introduction form for P_AppAbs' *)
Lemma P_AppAbs' a a0 b0 b b1 ℓ0 :
  b = a0 [b1..] ->
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->
  (* ---------------------------- *)
  (tApp (tAbs ℓ0 a) ℓ0 b0) ⇒ b.
Proof. hauto lq:on use:P_AppAbs. Qed.


(* Lemma P_IndSuc' a0 a1 b0 b1 c0 c1 t : *)
(*   t = b1 [(tInd a1 b1 c1) .: c1 ..] -> *)
(*   a0 ⇒ a1 -> *)
(*   b0 ⇒ b1 -> *)
(*   c0 ⇒ c1 -> *)
(*   (* ---------------------  *) *)
(*   tInd a0 b0 (tSuc c0) ⇒ t. *)
(* Proof. move => > ->. apply P_IndSuc. Qed. *)

Lemma P_LetPack' ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 t :
  t = c1[b1 .: a1 ..] ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  tLet ℓ0 ℓ1 (tPack ℓ0 a0 b0) c0 ⇒ t.
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
  (* - move => *. *)
  (*   apply : P_IndSuc'; eauto; by asimpl. *)
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
  elim : a b / h0 .
  - move => //=; eauto with par.
  - move => //=; eauto with par.
  - qauto db:par use: (Par_morphing_lift_n 1).
  - qauto l:on db:par use:(Par_morphing_lift_n 1).
  - simpl; eauto with par.
  - move => a a0 b0 b1 ℓ0 h0 ih0 h1 ih1 σ0 σ h /=.
    apply P_AppAbs' with (a0 := a0 [up_tm_tm σ]) (b1 := b1 [σ]).
    by asimpl. hauto l:on unfold:Par_m use:Par_renaming inv:nat. eauto.
  - move => //=; eauto with par.
  - move => //=; eauto with par.
  - move => //=; eauto with par.
  - move => //=; eauto with par.
  - qauto db:par use: (Par_morphing_lift_n 2).
  - qauto db:par use: (Par_morphing_lift_n 2).
  (* - hauto lq:on db:par use:(Par_morphing_lift_n 1). *)
  - qauto db:par use:(Par_morphing_lift_n 1).
  - qauto l:on ctrs:Par use:(Par_morphing_lift_n 2).
  - qauto l:on ctrs:Par use:(Par_morphing_lift_n 2).
  - move => ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 ha iha hb ihb hc ihc σ0 σ1 hσ /=.
    apply P_LetPack' with (a1 := a1[σ1]) (b1 := b1[σ1]) (c1 := c1[up_tm_tm (up_tm_tm σ1)]); eauto.
    by asimpl.
    sfirstorder use:(Par_morphing_lift_n 2).
Qed.

  (* - qauto db:par use:(Par_morphing_lift_n 2). *)
  (* - move => a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc σ0 σ1 hσ /=. *)
  (*   apply P_IndSuc' with *)
  (*     (b1 := b1[up_tm_tm_n 2 σ1]) (a1 := a1[σ1]) (c1 := c1[σ1]); *)
  (*     eauto => /=. by asimpl. *)
  (*   sfirstorder use:(Par_morphing_lift_n 2). *)

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

(* ------------------------------------------------------------ *)

(* Inversion lemmas *)

Lemma Pars_pi_inv A B ℓ0 C (h : (tPi ℓ0 A B) ⇒* C) :
  exists A0 B0, C = tPi ℓ0 A0 B0 /\ (A ⇒* A0) /\ (B ⇒* B0).
Proof.
  move E : (tPi ℓ0 A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Pars_eq_inv ℓ a b A C (h : (tEq ℓ a b A) ⇒* C) :
  exists a0 b0 A0, C = tEq ℓ a0 b0 A0 /\ a ⇒* a0 /\ b ⇒* b0 /\ A ⇒* A0.
Proof.
  move E : (tEq ℓ a b A) h => T h.
  move : ℓ a b A E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

Lemma Pars_univ_inv i A (h : (tUniv i) ⇒* A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto q:on rew:off ctrs:rtc, Par inv:Par.
Qed.

Lemma Pars_sig_inv ℓ0 A B C (h : tSig ℓ0 A B ⇒* C) :
  exists A0 B0, C = tSig ℓ0 A0 B0 /\ (A ⇒* A0) /\ (B ⇒* B0).
Proof.
  move E : (tSig ℓ0 A B) h => T h.
  move : ℓ0 A B E.
  elim : T C / h; hecrush inv:Par ctrs:Par, rtc.
Qed.

(* ------------------------------------------------------------ *)


(* Lemma P_IndZero_star a b c : *)
(*   (c ⇒* tZero) -> *)
(*   (tInd a b c  ⇒* a). *)
(* Proof. *)
(*   move E : tZero => v h. *)
(*   move : E. *)
(*   elim : c v / h. *)
(*   - move => *. subst. *)
(*     apply rtc_once. apply P_IndZero. apply Par_refl. *)
(*   - move => c c0 c1 h0 h1 h2 ?; subst. *)
(*     move /(_ eq_refl) in h2. *)
(*     apply : rtc_transitive; eauto. *)
(*     hauto lq:on use:@rtc_once,Par_refl ctrs:Par. *)
(* Qed. *)

(* Lemma P_IndSuc_star a b c c0 : *)
(*   (c ⇒* tSuc c0) -> *)
(*   (tInd a b c  ⇒* b[(tInd a b c0) .: c0 ..]). *)
(* Proof. *)
(*   move E : (tSuc c0) => v h. *)
(*   move : E.  elim : c v /h. *)
(*   - move=> > <- *. *)
(*     apply rtc_once. apply P_IndSuc; apply Par_refl. *)
(*   - move => c1 c2 c3 h0 h1 ih ?. subst. *)
(*     move /(_ eq_refl) : ih. *)
(*     apply rtc_l. *)
(*     hauto lq:on use:Par_refl ctrs:Par. *)
(* Qed. *)

(* Lemma P_IndSuc_star' a b c c0 t : *)
(*   b[(tInd a b c0) .: c0 ..] = t -> *)
(*   (c ⇒* tSuc c0) -> *)
(*   (tInd a b c  ⇒* t). *)
(* Proof. move => > <-. apply P_IndSuc_star. Qed. *)

Lemma P_JRefl_star t p :
  (p ⇒* tRefl)  ->
  ((tJ t p) ⇒* t).
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

Lemma P_LetPack_star t ℓ0 ℓ1 a b c :
  t ⇒* tPack ℓ0 a b ->
  tLet ℓ0 ℓ1 t c ⇒* c[b .: a ..].
Proof.
  move E : (tPack ℓ0 a b) => v h.
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
  | tPi ℓ0 A B => tPi ℓ0 (tstar A) (tstar B)
  | tAbs ℓ0 a => tAbs ℓ0 (tstar a)
  | tApp (tAbs ℓ0 a) ℓ1 b =>
       if T_eqb ℓ0 ℓ1
       then (tstar a) [(tstar b)..]
       else tApp (tAbs ℓ0 (tstar a)) ℓ1 (tstar b)
  | tApp a ℓ0 b => tApp (tstar a) ℓ0 (tstar b)
  (* | tZero => tZero *)
  (* | tSuc a => tSuc (tstar a) *)
  (* | tInd a b tZero => tstar a *)
  (* | tInd a b (tSuc c) => (tstar b) [(tInd (tstar a) (tstar b) (tstar c)) .: (tstar c)  .. ] *)
  (* | tInd a b c => tInd (tstar a) (tstar b) (tstar c) *)
  (* | tNat => tNat *)
  | tRefl => tRefl
  | tEq ℓ a b A => tEq ℓ (tstar a) (tstar b) (tstar A)
  | tJ t tRefl => tstar t
  | tJ t p => tJ (tstar t) (tstar p)
  | tLet ℓ0 ℓ1 (tPack ℓ2 a b) c =>
      if T_eqb ℓ0 ℓ2
      then (tstar c)[(tstar b) .: (tstar a)..]
      else tLet ℓ0 ℓ1 (tPack ℓ2 (tstar a) (tstar b)) (tstar c)
  | tLet ℓ0 ℓ1 a b => tLet ℓ0 ℓ1 (tstar a) (tstar b)
  | tSig ℓ A B => tSig ℓ (tstar A) (tstar B)
  | tPack ℓ a b => tPack ℓ (tstar a) (tstar b)
  | tVoid => tVoid
  | tAbsurd a => tAbsurd (tstar a)
  end.

Lemma Par_triangle a : forall b, (a ⇒ b) -> (b ⇒ tstar a).
Proof.
  apply tstar_ind.
  - hauto l:on inv:Par.
  - hauto l:on inv:Par.
  - hauto lq:on ctrs:Par inv:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => > ? /T_eqdec.
    hauto lq:on use:Par_refl, Par_cong, Par_cong2 ctrs:Par inv:Par.
  - move => b ℓ0 a0 ℓ1 b0 ? ? ? h0. subst.
    move => ih0 ih1 b h1.
    elim /Par_inv : h1=>//=.
    + hauto lq:on ctrs:Par inv:Par.
    + move => h2 a1 a2 b1 b2 ℓ2 h3 h4 [*]. subst.
      case : T_eqdec h0 =>//.
  - hauto lq:on ctrs:Par inv:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => > ? /T_eqdec.
    hauto lq:on inv:Par use:Par_refl,Par_cong,Par_cong2 ctrs:Par.
  - move => > ? ? ?. subst.
    case : T_eqdec=>//.
    hauto lq:on inv:Par use:Par_refl,Par_cong,Par_cong2 ctrs:Par.
  - hauto lq:on inv:Par use:Par_refl,Par_cong,Par_cong2 ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
Qed.

Lemma Par_confluent : diamond Par.
Proof. hauto lq:on use:Par_triangle unfold:diamond. Qed.

Lemma Pars_confluent : confluent Par.
Proof.
  sfirstorder use:Par_confluent, @diamond_confluent.
Qed.

End par_facts.
