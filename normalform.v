From WR Require Import syntax join imports.

(* Identifying neutral (ne) and normal (nf) terms *)
Fixpoint ne (a : tm) : bool :=
  match a with
  | var_tm _ => true
  | tApp a b => ne a && nf b
  | tAbs _ => false
  | tPi A B => false
  | tVoid => false
  | tJ t a b p => nf t && nf a && nf b && ne p
  | tUniv _ => false
  | tTrue => false
  | tFalse => false
  | tIf a b c => ne a && nf b && nf c
  | tBool => false
  | tEq a b A => false
  | tRefl => false
  end
with nf (a : tm) : bool :=
  match a with
  | var_tm _ => true
  | tApp a b => ne a && nf b
  | tAbs a => nf a
  | tPi A B => nf A && nf B
  | tVoid => true
  | tJ t a b p => nf t && nf a && nf b && ne p
  | tUniv _ => true
  | tTrue => true
  | tFalse => true
  | tIf a b c => ne a && nf b && nf c
  | tBool => true
  | tEq a b A => nf a && nf b && nf A
  | tRefl => true
  end.

(* Terms that are weakly normalizing to a neutral or normal form. *)
Definition wn (a : tm) := exists b, a ⇒* b /\ nf b.
Definition wne (a : tm) := exists b, a ⇒* b /\ ne b.

(* All neutral terms are normal forms *)
Lemma ne_nf (a : tm) : ne a -> nf a.
Proof. elim : a =>//; hauto q:on unfold:nf inv:Par. Qed.

(* Weakly neutral implies weakly normal *)
Lemma wne_wn a : wne a -> wn a.
Proof. sfirstorder use:ne_nf. Qed.

(* Normal implies weakly normal *)
Lemma nf_wn v : nf v -> wn v.
Proof. sfirstorder ctrs:rtc. Qed.

(* booleans are normal *)
Lemma bool_val_nf v : is_bool_val v -> nf v.
Proof. case : v =>// _; hauto lq:on unfold:nf inv:Par. Qed.

(* Neutral and normal forms are stable under renaming *)
Lemma ne_nf_renaming (a : tm) :
  forall (ξ : nat -> nat),
    (ne a <-> ne (a⟨ξ⟩)) /\ (nf a <-> nf (a⟨ξ⟩)).
Proof.
  elim : a; solve [auto; hauto b:on].
Qed.


(* Normal and neural forms are preserved by parallel reduction. *)
Lemma nf_ne_preservation a b (h : Par a b) : (nf a ==> nf b) /\ (ne a ==> ne b).
Proof.
  elim : a b / h => //; try hauto lqb:on depth:2.
  hauto q:on b:on use:ne_nf, ne_nf_renaming.
Qed.

Lemma nf_preservation : forall a b, (a ⇒ b) -> nf a -> nf b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Lemma ne_preservation : forall a b, (a ⇒ b) -> ne a -> ne b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Create HintDb nfne.
#[export]Hint Resolve nf_wn bool_val_nf ne_nf wne_wn ne_preservation nf_preservation : nfne.

Local Lemma Pars_antirenaming (a b0 : tm) (ξ : nat -> nat)
  (h : (a⟨ξ⟩ ⇒* b0)) : exists b, b0 = b⟨ξ⟩ /\ (a ⇒* b).
Proof.
  move E : (a⟨ξ⟩) h => a0 h.
  move : a E.
  elim : a0 b0 / h.
  - hauto lq:on ctrs:rtc.
  - move => a b c h0 h ih a0 ?. subst.
    move /Par_antirenaming : h0.
    hauto lq:on ctrs:rtc, eq.
Qed.

Lemma wn_antirenaming a (ξ : nat -> nat) : wn (a⟨ξ⟩) -> wn a.
Proof.
  rewrite /wn.
  move => [v [rv nfv]].
  move /Pars_antirenaming : rv => [b [hb ?]]. subst.
  sfirstorder use:ne_nf_renaming.
Qed.

(* ------------------------------------------------------------- *)

(* The next set of lemmas are congruence rules for multiple steps
   of parallel reduction. *)

#[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
  hauto lq:on ctrs:Par use:Par_refl.

Lemma S_AppLR (a a0 b b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tApp a b) ⇒* (tApp a0 b0).
Proof.
  move => h. move :  b b0.
  elim : a a0 / h.
  - move => a a0 b h.
    elim : a0 b / h.
    + auto using rtc_refl.
    + solve_s_rec.
  - solve_s_rec.
Qed.

Lemma S_If a0 a1 : forall b0 b1 c0 c1,
    a0 ⇒* a1 ->
    b0 ⇒* b1 ->
    c0 ⇒* c1 ->
    (tIf a0 b0 c0) ⇒* (tIf a1 b1 c1).
Proof.
  move => + + + + h.
  elim : a0 a1 /h.
  - move => + b0 b1 + + h.
    elim : b0 b1 /h.
    + move => + + c0 c1 h.
      elim : c0 c1 /h.
      * auto using rtc_refl.
      * solve_s_rec.
    + solve_s_rec.
  - solve_s_rec.
Qed.

Lemma S_J t0 t1 : forall a0 a1 b0 b1 p0 p1,
    t0 ⇒* t1 ->
    a0 ⇒* a1 ->
    b0 ⇒* b1 ->
    p0 ⇒* p1 ->
    (tJ t0 a0 b0 p0) ⇒* (tJ t1 a1 b1 p1).
Proof.
  move => + + + + + + h.
  elim : t0 t1 /h; last by solve_s_rec.
  move => + a0 a1 + +  + + h.
  elim : a0 a1 /h; last by solve_s_rec.
  move => + + b0 b1 + + h.
  elim : b0 b1 /h; last by solve_s_rec.
  move => + + + p0 p1 h.
  elim : p0 p1 / h; last by solve_s_rec.
  auto using rtc_refl.
Qed.

Lemma S_Pi (a a0 b b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tPi a b) ⇒* (tPi a0 b0).
Proof.
  move => h.
  move : b b0.
  elim : a a0/h.
  - move => + b b0 h.
    elim : b b0/h.
    + auto using rtc_refl.
    + solve_s_rec.
  - solve_s_rec.
Qed.

Lemma S_Abs (a b : tm)
  (h : a ⇒* b) :
  (tAbs a) ⇒* (tAbs b).
Proof. elim : a b /h; hauto lq:on ctrs:Par,rtc. Qed.

Lemma S_Eq a0 a1 b0 b1 A0 A1 :
  a0 ⇒* a1 ->
  b0 ⇒* b1 ->
  A0 ⇒* A1 ->
  (tEq a0 b0 A0) ⇒* (tEq a1 b1 A1).
Proof.
  move => h.
  move : b0 b1 A0 A1.
  elim : a0 a1 /h.
  - move => + b0 b1 + + h.
    elim : b0 b1 /h.
    + move => + + A0 A1 h.
      elim : A0 A1 /h.
      * auto using rtc_refl.
      * solve_s_rec.
    + solve_s_rec.
  - solve_s_rec.
Qed.

(* ------------------------------------------------------ *)

(* We can construct proofs that terms are weakly neutral
   and weakly normal compositionally. *)

Lemma wne_j (t a b p : tm) :
  wn t -> wn a -> wn b -> wne p -> wne (tJ t a b p).
Proof.
  move => [t0 [? ?]] [a0 [? ?]] [b0 [? ?]] [p0 [? ?]].
  exists (tJ t0 a0 b0 p0).
  hauto lq:on b:on use:S_J.
Qed.

Lemma wne_if (a b c : tm) :
  wne a -> wn b -> wn c -> wne (tIf a b c).
Proof.
  move => [a0 [? ?]] [b0 [? ?]] [c0 [? ?]].
  exists (tIf a0 b0 c0).
  qauto l:on use:S_If b:on.
Qed.

Lemma wne_app (a b : tm) :
  wne a -> wn b -> wne (tApp a b).
Proof.
  move => [a0 [? ?]] [b0 [? ?]].
  exists (tApp a0 b0).
  hauto b:on use:S_AppLR.
Qed.

Lemma wn_abs (a : tm) (h : wn a) : wn (tAbs a).
Proof.
  move : h => [v [? ?]].
  exists (tAbs v).
  eauto using S_Abs.
Qed.

Lemma wn_pi A B : wn A -> wn B -> wn (tPi A B).
Proof.
  move => [A0 [? ?]] [B0 [? ?]].
  exists (tPi A0 B0).
  hauto lqb:on use:S_Pi.
Qed.

Lemma wn_eq a b A : wn a -> wn b -> wn A -> wn (tEq a b A).
Proof.
  rewrite /wn.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  exists (tEq va vb vA).
  split.
  - by apply S_Eq.
  - hauto lqb:on.
Qed.

(* --------------------------------------------------------------- *)

(* This lemma is is like an
   inversion principle for terms with normal forms. If a term applied to a
   variable is normal, then the term itself is normal. *)

Lemma ext_wn (a : tm) i :
    wn (tApp a (var_tm i)) ->
    wn a.
Proof.
  move E : (tApp a (var_tm i)) => a0 [v [hr hv]].
  move : a E.
  move : hv.
  elim : a0 v / hr.
  - hauto q:on inv:tm ctrs:rtc b:on db: nfne.
  - move => a0 a1 a2 hr0 hr1 ih hnfa2.
    move /(_ hnfa2) in ih.
    move => a.
    case : a0 hr0=>// => b0 b1.
    elim /Par_inv=>//.
    + hauto q:on inv:Par ctrs:rtc b:on.
    + move => ? a0 a3 b2 b3 ? ? [? ?] ? [? ?]. subst.
      have ? : b3 = var_tm i by hauto lq:on inv:Par. subst.
      suff : wn (tAbs a3) by hauto lq:on ctrs:Par, rtc unfold:wn.
      have : wn (subst_tm ((var_tm i) ..) a3) by sfirstorder.
      replace (subst_tm ((var_tm i) ..) a3) with (ren_tm (i..) a3).
      move /wn_antirenaming.
      by apply : wn_abs.
      substify. by asimpl.
Qed.
