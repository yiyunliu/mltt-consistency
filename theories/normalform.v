Require Import syntax par imports.

Module Type normalform_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax).

Module pf := par_facts lattice syntax par.

(* Identifying neutral (ne) and normal (nf) terms *)
Fixpoint ne (a : tm) : bool :=
  match a with
  | var_tm _ => true
  | tApp a ℓ0 b => ne a && nf b
  | tAbs _ _ => false
  | tPi _ A B => false
  | tJ t p => nf t &&  ne p
  | tUniv _ => false
  (* | tZero => false *)
  (* | tSuc _ => false *)
  (* | tInd a b c => nf a && nf b && ne c *)
  (* | tNat => false *)
  | tEq _ _ _ _ => false
  | tRefl => false
  | tSig _ _ _ => false
  | tPack _ _ _ => false
  | tLet _ _ a b => ne a && nf b
  | tVoid => false
  | tAbsurd a => ne a
  | tD => true
  | tDown _ a => ne a
  end
with nf (a : tm) : bool :=
  match a with
  | var_tm _ => true
  | tApp a ℓ0 b => ne a && nf b
  | tAbs _ a => nf a
  | tPi _ A B => nf A && nf B
  | tJ t p => nf t && ne p
  | tUniv _ => true
  (* | tZero => true *)
  (* | tSuc a => nf a *)
  (* | tInd a b c => nf a && nf b && ne c *)
  (* | tNat => true *)
  | tEq _ a b A => nf a && nf b && nf A
  | tRefl => true
  | tSig _ A B => nf A && nf B
  | tPack _ a b => nf a && nf b
  | tLet _ _ a b => ne a && nf b
  | tVoid => true
  | tAbsurd a => ne a
  | tD => true
  | tDown _ a => ne a
  end.

(* Terms that are weakly normalizing to a neutral or normal form. *)
Definition wn (a : tm) := exists b, a ⇒* b /\ nf b.
Definition wne (a : tm) := exists b, a ⇒* b /\ ne b.

Definition var_or_d a :=
  match a with
  | tD => true
  | var_tm _ => true
  | _ => false
  end.

Definition ren_with_d (ξ : nat -> tm) :=
  forall i, var_or_d (ξ i).

End normalform_sig.

Module normalform_fact
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import normalform : normalform_sig lattice syntax par).

(* All neutral terms are normal forms *)
Lemma ne_nf (a : tm) : ne a -> nf a.
Proof. elim : a =>//; hauto q:on unfold:nf inv:Par. Qed.

(* Weakly neutral implies weakly normal *)
Lemma wne_wn a : wne a -> wn a.
Proof. sfirstorder use:ne_nf. Qed.

(* Normal implies weakly normal *)
Lemma nf_wn v : nf v -> wn v.
Proof. sfirstorder ctrs:rtc. Qed.

(* (* natural number values are normal *) *)
(* Lemma nat_val_nf v : is_nat_val v -> nf v. *)
(* Proof. elim : v =>//=. Qed. *)

(* Lemma ne_nat_val v : ne v -> is_nat_val v. *)
(* Proof. elim : v =>//=. Qed. *)

(* Neutral and normal forms are stable under renaming *)
Lemma ne_nf_renaming (a : tm) :
  forall (ξ : nat -> nat),
    (ne a <-> ne (a⟨ξ⟩)) /\ (nf a <-> nf (a⟨ξ⟩)).
Proof.
  elim : a; solve [auto; hauto b:on].
Qed.

Lemma nf_refl a b (h: a ⇒ b) : (nf a -> b = a) /\ (ne a -> b = a).
Proof.
  elim : a b / h => // ; hauto b:on.
Qed.

(* Normal and neural forms are preserved by parallel reduction. *)
Lemma nf_ne_preservation a b (h : a ⇒ b) : (nf a ==> nf b) /\ (ne a ==> ne b).
Proof.
  elim : a b / h => //; hauto lqb:on depth:2.
Qed.

Lemma nf_preservation : forall a b, (a ⇒ b) -> nf a -> nf b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Lemma ne_preservation : forall a b, (a ⇒ b) -> ne a -> ne b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Create HintDb nfne.
#[export]Hint Resolve (* ne_nat_val *) nf_wn (* nat_val_nf *) ne_nf wne_wn ne_preservation nf_preservation : nfne.


(* ------------------ antirenaming ------------------------- *)

Lemma ren_var_or_d ξ a : var_or_d a = var_or_d a⟨ξ⟩.
Proof. case : a => //=. Qed.

Lemma var_or_d_ne a : var_or_d a -> ne a && nf a.
Proof. case : a => //=. Qed.

Lemma ren_with_d_ne ξ i : ren_with_d ξ -> ne (ξ i) && nf (ξ i).
Proof. sfirstorder use:var_or_d_ne unfold:ren_with_d. Qed.

Lemma ren_with_d_up_tm ξ (h : ren_with_d ξ) :
  ren_with_d (up_tm_tm ξ).
Proof.
  rewrite /ren_with_d in h *.
  case => //= n.
  asimpl.
  move /(_ n) : h.
  by rewrite -ren_var_or_d.
Qed.

Lemma ren_with_d_imp ξ i a :
  ren_with_d ξ ->
  ξ i = a ->
  var_or_d a.
Proof. scongruence. Qed.

Lemma ne_nf_renaming_with_d (a : tm) :
  forall ξ, ren_with_d ξ ->
    (ne a = ne (a[ξ])) /\ (nf a = nf (a[ξ])).
Proof.
  elim : a; try solve [auto; hauto use:ren_with_d_ne, ren_with_d_up_tm b:on].
Qed.

(* Next we show that if a renamed term reduces, then
   we can extract the unrenamed term from the derivation. *)
Local Lemma Par_antirenaming (a b0 : tm) ξ
  (hξ : ren_with_d ξ)
  (h : a[ξ] ⇒ b0) : exists b, (a ⇒ b) /\ b0 = b[ξ].
Proof.
  move E : (a[ξ]) h hξ => a0 h.
  move : a ξ E.
  elim : a0 b0 / h.
  - move => + []//. eauto with par.
  - move => + []//=; eauto with par.
  - move => ℓ0 A0 A1 B0 B1 h0 ih0 h1 ih1 [] // /=.
    hauto q:on use:ren_with_d_imp.
    qauto l:on ctrs:Par use:ren_with_d_up_tm.
  - move => ℓ0 a0 a1 h ih [] //.
    hauto q:on use:ren_with_d_imp.
    move => ℓ1 a ξ [] ?.
    qauto l:on ctrs:Par use:ren_with_d_up_tm.
  - move => a0 a1 ℓ0 b0 b1  + + + + []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par.
  - move => a a0 b0 b1 ℓ0 ha iha hb ihb []//.
    hauto q:on use:ren_with_d_imp.
    move => []//.
    hauto q:on use:ren_with_d_imp.
    move => ℓ1 t t0 t1 ξ [] *. subst.
    specialize iha with (1 := eq_refl).
    specialize ihb with (1 := eq_refl).
    move : (iha ltac:(by auto using ren_with_d_up_tm)) => [a [? ?]]. subst.
    move : (ihb ltac:(by auto)) => [b [? ?]]. subst.
    exists (subst_tm (b..) a).
    split; last by asimpl.
    hauto lq:on ctrs:Par.
  - hauto q:on ctrs:Par inv:tm.
  - move => + + + + []//=.
    hauto q:on use:ren_with_d_imp.
    qauto l:on ctrs:Par.
  - hauto q:on inv:tm ctrs:Par.
  - move => > ++++++ [] //.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par.
  - move => > + + + + []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par.
  - move => t0 t1 h0 h1 []//.
    hauto q:on use:ren_with_d_imp.
    move => t []//.
    hauto q:on use:ren_with_d_imp.
    move => ξ [?]. subst.
    hauto q:on ctrs:Par.
  - move => > + + + + []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par use:ren_with_d_up_tm.
  - move => > + + + + []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par use:ren_with_d_up_tm.
  - move => > + + + + []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par use:ren_with_d_up_tm.
  - move => ℓ0 ℓ1 ? ? ? a1 b1 c1 ha iha hb ihb hc ihc []//=.
    hauto q:on use:ren_with_d_imp.
    move => ℓ2 ℓ3 []//=.
    hauto q:on use:ren_with_d_imp.
    move => ℓ4 a0 b0 c0 ξ [*]. subst.
    specialize iha with (1 := eq_refl).
    specialize ihb with (1 := eq_refl).
    specialize ihc with (1 := eq_refl).
    move /(_ ltac:(auto)) : iha => [a2 [iha ?]].
    move /(_ ltac:(auto)) : ihb => [b2 [ihb ?]].
    move /(_ ltac:(auto using ren_with_d_up_tm)) : ihc => [c2 [ihc ?]]. subst.
    exists (c2[b2 .: a2 ..]).
    split; [by auto with par | by asimpl].
  - hauto q:on inv:tm ctrs:Par.
  - move => ℓ0 p0 p1 h ih []//.
    hauto q:on use:ren_with_d_imp.
    hauto q:on ctrs:Par.
  - move => + []//=.
    hauto q:on use:ren_with_d_imp.
    move => ℓ0 ℓ1 t0 ξ [*]. subst.
    have ? : t0 = tRefl by hauto q:on inv:tm use:ren_with_d_imp. subst.
    hauto l:on.
Qed.

Local Lemma Pars_antirenaming (a b0 : tm) ξ
  (hξ : ren_with_d ξ)
  (h : (a[ξ] ⇒* b0)) : exists b, b0 = b[ξ] /\ (a ⇒* b).
Proof.
  move E : (a[ξ]) h => a0 h.
  move : a E.
  elim : a0 b0 / h.
  - hauto lq:on ctrs:rtc.
  - move => a b c h0 h ih a0 ?. subst.
    move /Par_antirenaming : h0.
    hauto lq:on ctrs:rtc, eq.
Qed.

Lemma wn_antirenaming a (ξ : nat -> tm) (hξ : ren_with_d ξ) : wn (a[ξ]) -> wn a.
Proof.
  rewrite /wn.
  move => [v [rv nfv]].
  move: Pars_antirenaming (hξ) (rv); repeat move/[apply]. move => [b [hb ?]]. subst.
  hauto q:on use:ne_nf_renaming_with_d.
Qed.

(* ------------------------------------------------------------- *)

(* The next set of lemmas are congruence rules for multiple steps
   of parallel reduction. *)

#[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
  hauto lq:on ctrs:Par use:pf.Par_refl.

Lemma S_AppLR ℓ0 (a a0 b b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tApp a ℓ0 b) ⇒* (tApp a0 ℓ0 b0).
Proof.
  move => h. move :  b b0.
  elim : a a0 / h.
  - move => a a0 b h.
    elim : a0 b / h.
    + auto using rtc_refl.
    + solve_s_rec.
  - solve_s_rec.
Qed.

(* Lemma S_Ind a0 a1 : forall b0 b1 c0 c1, *)
(*     a0 ⇒* a1 -> *)
(*     b0 ⇒* b1 -> *)
(*     c0 ⇒* c1 -> *)
(*     (tInd a0 b0 c0) ⇒* (tInd a1 b1 c1). *)
(* Proof. *)
(*   move => + + + + h. *)
(*   elim : a0 a1 /h. *)
(*   - move => + b0 b1 + + h. *)
(*     elim : b0 b1 /h. *)
(*     + move => + + c0 c1 h. *)
(*       elim : c0 c1 /h. *)
(*       * auto using rtc_refl. *)
(*       * solve_s_rec. *)
(*     + solve_s_rec. *)
(*   - solve_s_rec. *)
(* Qed. *)

Lemma S_J t0 t1 : forall p0 p1,
    t0 ⇒* t1 ->
    p0 ⇒* p1 ->
    (tJ t0 p0) ⇒* (tJ t1 p1).
Proof.
  move => + + h.
  elim : t0 t1 /h; last by solve_s_rec.
  move => ? p0 p1 h.
  elim : p0 p1 /h; last by solve_s_rec.
  auto using rtc_refl.
Qed.

Lemma S_Let ℓ0 ℓ1 a0 a1 : forall b0 b1,
    a0 ⇒* a1 ->
    b0 ⇒* b1 ->
    tLet ℓ0 ℓ1 a0 b0 ⇒* tLet ℓ0 ℓ1 a1 b1.
Proof.
  move => + + h.
  elim : a0 a1 /h; last by solve_s_rec.
  move => + b0 b1 h.
  elim : b0 b1 /h; last by solve_s_rec.
  auto using rtc_refl.
Qed.

Lemma S_Down ℓ0 a b :
  a ⇒* b ->
  tDown ℓ0 a ⇒* tDown ℓ0 b.
Proof.
  move => h.
  elim : a b / h; last by solve_s_rec.
  auto using rtc_refl.
Qed.

Lemma S_Pi ℓ0 (a a0 b b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tPi ℓ0 a b) ⇒* (tPi ℓ0 a0 b0).
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

Lemma S_Sig ℓ0 (a a0 b b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tSig ℓ0 a b) ⇒* (tSig ℓ0 a0 b0).
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

Lemma S_Abs ℓ0 (a b : tm)
  (h : a ⇒* b) :
  (tAbs ℓ0 a) ⇒* (tAbs ℓ0 b).
Proof. elim : a b /h; hauto lq:on ctrs:Par,rtc. Qed.

Lemma S_Absurd (a b : tm)
  (h : a ⇒* b) :
  (tAbsurd a) ⇒* (tAbsurd b).
Proof. elim : a b /h; hauto lq:on ctrs:Par,rtc. Qed.

Lemma S_Eq ℓ0 a0 a1 b0 b1 A0 A1 :
  a0 ⇒* a1 ->
  b0 ⇒* b1 ->
  A0 ⇒* A1 ->
  (tEq ℓ0 a0 b0 A0) ⇒* (tEq ℓ0 a1 b1 A1).
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

Lemma S_Pack ℓ0 (a b a0 b0 : tm) :
  a ⇒* a0 ->
  b ⇒* b0 ->
  (tPack ℓ0 a b) ⇒* (tPack ℓ0 a0 b0).
Proof.
  move => h.
  move : b b0.
  elim : a a0/h; last by solve_s_rec.
  move => ? b b0 h.
  elim : b b0/h; last by solve_s_rec.
  auto using rtc_refl.
Qed.

(* Lemma S_Suc a b (h : a ⇒* b) : tSuc a ⇒* tSuc b. *)
(* Proof. *)
(*   elim : a b / h; last by solve_s_rec. *)
(*   move => ?; apply rtc_refl. *)
(* Qed. *)

(* ------------------------------------------------------ *)

(* We can construct proofs that terms are weakly neutral
   and weakly normal compositionally. *)

Lemma wne_absurd a :
  wne a -> wne (tAbsurd a).
Proof.
  move => [a0 [? ?]].
  exists (tAbsurd a0).
  sfirstorder use:S_Absurd.
Qed.

Lemma wne_j (t p : tm) :
  wn t -> wne p -> wne (tJ t p).
Proof.
  move => [t0 [? ?]] [p0 [? ?]].
  exists (tJ t0 p0).
  hauto lq:on b:on use:S_J.
Qed.

(* Lemma wne_ind (a b c : tm) : *)
(*   wn a -> wn b -> wne c -> wne (tInd a b c). *)
(* Proof. *)
(*   move => [a0 [? ?]] [b0 [? ?]] [c0 [? ?]]. *)
(*   exists (tInd a0 b0 c0). *)
(*   qauto l:on use:S_Ind b:on. *)
(* Qed. *)

Lemma wne_app ℓ0 (a b : tm) :
  wne a -> wn b -> wne (tApp a ℓ0 b).
Proof.
  move => [a0 [? ?]] [b0 [? ?]].
  exists (tApp a0 ℓ0 b0).
  hauto b:on use:S_AppLR.
Qed.

Lemma wne_let ℓ0 ℓ1 (a b : tm) :
  wne a -> wn b -> wne (tLet ℓ0 ℓ1 a b).
Proof.
  move => [a0 [? ?]] [b0 [? ?]].
  exists (tLet ℓ0 ℓ1 a0 b0).
  hauto b:on use:S_Let.
Qed.

Lemma wne_down ℓ0 (a : tm) :
  wne a -> wne (tDown ℓ0 a).
Proof.
  move => [a0 [? ?]].
  exists (tDown ℓ0 a0).
  sfirstorder b:on use:S_Down.
Qed.

Lemma wn_abs ℓ0 (a : tm) (h : wn a) : wn (tAbs ℓ0 a).
Proof.
  move : h => [v [? ?]].
  exists (tAbs ℓ0 v).
  eauto using S_Abs.
Qed.

Lemma wn_pi ℓ0 A B : wn A -> wn B -> wn (tPi ℓ0 A B).
Proof.
  move => [A0 [? ?]] [B0 [? ?]].
  exists (tPi ℓ0 A0 B0).
  hauto lqb:on use:S_Pi.
Qed.

Lemma wn_sig ℓ0 A B : wn A -> wn B -> wn (tSig ℓ0 A B).
Proof.
  move => [A0 [? ?]] [B0 [? ?]].
  exists (tSig ℓ0 A0 B0).
  hauto lqb:on use:S_Sig.
Qed.

Lemma wn_pack ℓ0 A B : wn A -> wn B -> wn (tPack ℓ0 A B).
Proof.
  move => [A0 [? ?]] [B0 [? ?]].
  exists (tPack ℓ0 A0 B0).
  hauto lqb:on use:S_Pack.
Qed.

Lemma wn_eq ℓ0 a b A : wn a -> wn b -> wn A -> wn (tEq ℓ0 a b A).
Proof.
  rewrite /wn.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  exists (tEq ℓ0 va vb vA).
  split.
  - by apply S_Eq.
  - hauto lqb:on.
Qed.

(* --------------------------------------------------------------- *)

(* This lemma is is like an
   inversion principle for terms with normal forms. If a term applied to a
   variable is normal, then the term itself is normal. *)

Lemma ext_wn ℓ0 (a : tm) :
    wn (tApp a ℓ0 tD) ->
    wn a.
Proof.
  move E : (tApp a ℓ0 tD) => a0 [v [hr hv]].
  move : a E.
  move : hv.
  elim : a0 v / hr.
  - hauto q:on inv:tm ctrs:rtc b:on db: nfne.
  - move => a0 a1 a2 hr0 hr1 ih hnfa2.
    move /(_ hnfa2) in ih.
    move => a.
    case : a0 hr0=>// => b0 ℓ b1.
    elim /Par_inv=>//.
    + hauto q:on inv:Par ctrs:rtc b:on.
    + move => ? a0 a3 b2 b3 ℓ1 ? ? [? ? ?] ? [? ? ?]. subst.
      have ? : b3 = tD by hauto lq:on inv:Par. subst.
      suff : wn (tAbs ℓ a3) by hauto lq:on ctrs:Par, rtc unfold:wn.
      have : wn (subst_tm (tD ..) a3) by sfirstorder.
      move /wn_antirenaming => h.
      apply : wn_abs.
      apply h.
      case => //=.
Qed.

End normalform_fact.
