From WR Require Import syntax join imports.
(* The semantic definition for function is in sufficient for eta reduction *)
(* λ 1 0 reduces to 0 but (λ 1 0) 0 reduces to a neutral term *)
(* but maybe nf and ne doesn't have to change thanks to facotrization of eta rules? *)
Fixpoint ne (a : tm) :=
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
with nf (a : tm) :=
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

Definition wn (a : tm) := exists b, Pars a b /\ nf b.
Definition wne (a : tm) := exists b, Pars a b /\ ne b.

Lemma bool_val_nf v : is_bool_val v -> nf v.
Proof. case : v =>// _; hauto lq:on unfold:nf inv:Par. Qed.

Lemma ne_nf (a : tm) : ne a -> nf a.
Proof. elim : a =>//; hauto q:on unfold:nf inv:Par. Qed.

Lemma ne_nf_renaming (a : tm) :
  forall (ξ : nat -> nat),
    (ne a <-> ne (ren_tm ξ a)) /\ (nf a <-> nf (ren_tm ξ a)).
Proof.
  elim : a; solve [auto; hauto b:on].
Qed.

Create HintDb nfne.
Lemma nf_ne_preservation a b (h : Par a b) : (nf a ==> nf b) /\ (ne a ==> ne b).
Proof.
  elim : a b / h => //; try hauto lqb:on depth:2.
  hauto q:on b:on use:ne_nf, ne_nf_renaming.
Qed.

Lemma nf_preservation : forall a b, Par a b -> nf a -> nf b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Lemma ne_preservation : forall a b, Par a b -> ne a -> ne b.
Proof. sfirstorder use:nf_ne_preservation b:on. Qed.

Lemma nf_ne_eval_size a b (h : Par a b) : nf a || ne a -> a = b \/ size_tm b < size_tm a.
Proof.
  elim : a b /h; try (move => /=/=; hauto b:on depth:2).
  - move => a a0 b0 b1 ? + + + /= h.
    rewrite Bool.orb_diag in h.
    suff : ne (tAbs a0) by done.
    hauto use:ne_nf, nf_ne_preservation lqb:on.
  - move => /= a0 a1 h h1 h2.
    have h3 : ne (ren_tm shift a0) by scongruence b:on.
    eapply ne_nf_renaming in h3.
    rewrite -ren_tm_size_tm.
    hauto lb:on.
Qed.

Lemma nf_wn v : nf v -> wn v.
Proof. sfirstorder ctrs:rtc. Qed.

Lemma wne_wn a : wne a -> wn a.
Proof. sfirstorder use:ne_nf. Qed.


#[export]Hint Resolve nf_wn bool_val_nf ne_nf wne_wn ne_preservation nf_preservation : nfne.

(* If nf a, a => b, then size b < size a *)
Lemma preservation_wn (a : tm) : wn a -> forall b, Par a b -> wn b.
Proof.
  rewrite /wn. move => [v [hv]].
  elim : a v / hv.
  - sfirstorder use:nf_ne_preservation b:on.
  - move => a0 a1 a2 hr0 hr1 /[apply] h a1' hr'.
    move : par_confluent hr0 hr'. repeat move/[apply].
    hauto lq:on ctrs:rtc.
Qed.

Lemma wn_antirenaming a (ξ : nat -> nat) : wn (ren_tm ξ a) -> wn a.
Proof.
  rewrite /wn.
  move => [v [rv nfv]].
  move /Pars_antirenaming : rv => [b [? hb]]. subst.
  sfirstorder use:ne_nf_renaming.
Qed.

Definition SBool (a : tm) := exists v, Pars a v /\ (is_bool_val v \/ ne v).
Definition SUniv (I : nat -> tm -> (tm -> Prop) -> Prop) m A := exists PA, I m A PA.
Definition SEq a b p := (Pars p tRefl /\ Coherent a b) \/ wne p.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

Inductive InterpExt n (I : nat -> tm -> (tm -> Prop) -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_Ne A : ne A -> InterpExt n I A wne
| InterpExt_Void : InterpExt n I tVoid wne
| InterpExt_Bool : InterpExt n I tBool SBool
| InterpExt_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpExt n I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> InterpExt n I (subst_tm (a..) B) PB) ->
  InterpExt n I (tPi A B) (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  InterpExt n I (tUniv m) (SUniv I m)
| InterpExt_Eq a b A :
  nf a ->
  nf b ->
  nf A ->
  InterpExt n I (tEq a b A) (SEq a b)
| InterpExt_Step A A0 PA :
  Par A A0 ->
  InterpExt n I A0 PA ->
  InterpExt n I A PA.

Hint Constructors InterpExt : iext.

#[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
  hauto lq:on ctrs:Par use:Par_refl.

Lemma S_AppLR (a a0 b b0 : tm) :
  Pars a a0 ->
  Pars b b0 ->
  Pars (tApp a b) (tApp a0 b0).
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
    Pars a0 a1 ->
    Pars b0 b1 ->
    Pars c0 c1 ->
    Pars (tIf a0 b0 c0) (tIf a1 b1 c1).
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
    Pars t0 t1 ->
    Pars a0 a1 ->
    Pars b0 b1 ->
    Pars p0 p1 ->
    Pars (tJ t0 a0 b0 p0) (tJ t1 a1 b1 p1).
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

Lemma S_Pi (a a0 b b0 : tm) :
  Pars a a0 ->
  Pars b b0 ->
  Pars (tPi a b) (tPi a0 b0).
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
  (h : Pars a b) :
  Pars (tAbs a) (tAbs b).
Proof. elim : a b /h; hauto lq:on ctrs:Par,rtc. Qed.

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

Definition CR (P : tm -> Prop) :=
  (forall a, P a -> wn a) /\
    (forall a, wne a -> P a).

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
      suff : wn (tAbs a3) by hauto lq:on unfold:wn ctrs:rtc.
      have : wn (subst_tm ((var_tm i) ..) a3) by sfirstorder.
      replace (subst_tm ((var_tm i) ..) a3) with (ren_tm (i..) a3).
      move /wn_antirenaming.
      by apply : wn_abs.
      substify. by asimpl.
Qed.

Lemma adequacy n I (h0 : forall m, m < n -> CR (SUniv I m)) A PA
  (h : InterpExt n I A PA)  :
  CR PA.
Proof.
  elim : A PA / h=>//.
  - firstorder with nfne.
  - firstorder with nfne.
  - hauto q:on db:nfne.
  - move => A B PA PF hA ihA hTot hRes ih.
    split.
    + rewrite /ProdSpace => b hb.
      have hzero : PA (var_tm var_zero) by hauto lq:on ctrs:rtc.
      move : hTot (hzero); move/[apply]. move => [PB ?].
      apply ext_wn with (i := var_zero).
      hauto q:on.
    + rewrite /ProdSpace => b wneb a PB ha hPB.
      suff : wn a by hauto q:on use:wne_app. firstorder.
  - hauto lq:on db:nfne.
Qed.

Lemma S_Eq a0 a1 b0 b1 A0 A1 :
  Pars a0 a1 ->
  Pars b0 b1 ->
  Pars A0 A1 ->
  Pars (tEq a0 b0 A0) (tEq a1 b1 A1).
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

Lemma wn_eq a b A : wn a -> wn b -> wn A -> wn (tEq a b A).
Proof.
  rewrite /wn.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  exists (tEq va vb vA).
  split.
  - by apply S_Eq.
  - hauto lqb:on.
Qed.

Lemma InterpExt_wn_ty n I A PA
  (h0 : forall m, m < n -> CR (SUniv I m))
  (h : InterpExt n I A PA) :
  wn A.
Proof.
  elim : A PA / h; auto with nfne.
  - move => A B PA PF hPA wnA hTot hRes ih.
    apply wn_pi; first by auto.
    have hzero : PA (var_tm var_zero) by hauto q:on ctrs:rtc use:adequacy.
    move : hTot (hzero); move/[apply]. move => [PB].
    move /ih.
    match goal with [|- wn ?Q -> _] => replace Q with (ren_tm (var_zero..) B) end.
    eauto using wn_antirenaming.
    substify. by asimpl.
  - hauto lq:on use:wn_eq ctrs:rtc.
  - hauto lq:on ctrs:rtc.
Qed.

Lemma InterpExt_Eq' n I PA a b A :
  nf a ->
  nf b ->
  nf A ->
  PA = SEq a b ->
  InterpExt n I (tEq a b A) PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' n I m PF :
  PF = (SUniv I m) ->
  m < n ->
  InterpExt n I (tUniv m) PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A PA =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => InterpUnivN m A PA
                                  | right _ => False
                                  end).

Lemma InterpExt_preservation n I A B P (h : InterpExt n I A P) :
  Par A B ->
  InterpExt n I B P.
Proof.
  move : B.
  elim : A P / h; auto.
  - eauto with iext nfne.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv : hT=>// ? A0 A1 B0 B1 ? ? [] *; subst.
    apply InterpExt_Fun; eauto with nfne.
    eauto using par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => a b A ?  ? ? B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpExt_Eq'; eauto using preservation_wn with nfne.
    (* Should have one goal remaining *)
    rewrite /SEq.
    fext => p. do 2 f_equal.
    apply propositional_extensionality.
    hauto lq:on use:Par_Coherent, Coherent_transitive, Coherent_symmetric.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation n A B P (h : InterpUnivN n A P) :
  Par A B ->
  InterpUnivN n B P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I A B P (h : InterpExt i I B P) :
  Pars A B ->
  InterpExt i I A P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star n I A B P (h : InterpExt n I A P) :
  Pars A B ->
  InterpExt n I B P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star n A B P (h : InterpUnivN n A P) :
  Pars A B ->
  InterpUnivN n B P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star n A B P (h : InterpUnivN n B P) :
  Pars A B ->
  InterpUnivN n A P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

Lemma InterpUnivN_Coherent n A B P (h : InterpUnivN n B P) :
  Coherent A B ->
  InterpUnivN n A P.
Proof.
  hauto l:on unfold:Coherent use:InterpUnivN_back_preservation_star, InterpUnivN_preservation_star.
Qed.

Lemma InterpExt_Bool_inv n I P :
  InterpExt n I tBool P ->
  P = SBool.
Proof.
  move E : tBool => A h.
  move : E.
  elim : A P / h=> //; hauto q:on inv:tm,Par.
Qed.

Lemma InterpExt_Ne_inv n I A P :
  ne A ->
  InterpExt n I A P ->
  P = wne.
Proof.
  move => + h0.
  elim : A P /h0 =>//.
  hauto l:on inv:- db:nfne.
Qed.

Lemma InterpExt_Void_inv n I P :
  InterpExt n I tVoid P ->
  P = wne.
Proof.
  move E : tVoid => A h.
  move : E.
  elim : A P / h; hauto q:on inv:Par,tm.
Qed.

Lemma InterpExt_Univ_inv n I P m :
  InterpExt n I (tUniv m) P ->
  P = SUniv I m /\ m < n.
Proof.
  move E : (tUniv m) => A h.
  move : E.
  elim : A P / h; hauto q:on inv:Par, tm.
Qed.

Lemma InterpUnivN_Bool_inv n P :
  InterpUnivN n tBool P ->
  P = SBool.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Bool_inv. Qed.

Lemma InterpExt_Eq_inv n I a b A P :
  InterpExt n I (tEq a b A) P ->
  P = SEq a b /\ wn a /\ wn b /\ wn A.
Proof.
  move E : (tEq a b A) => T h.
  move : a b A E.
  elim : T P /h => //.
  - hauto q:on inv:tm.
  - hauto lq:on ctrs:rtc.
  - move => A A0 PA hred hA0 ih a b A1 ?. subst.
    elim /Par_inv : hred=>//.
    move => hred ? ? ? a2 b2 A2 ? ? ? [] *;subst.
    split; last by hauto lq:on rew:off ctrs:rtc.
    specialize ih with (1 := eq_refl).
    move : ih => [->] *.
    fext => A. rewrite /SEq. do 2 f_equal.
    apply propositional_extensionality.
    hauto lq:on use:Par_Coherent, Coherent_symmetric, Coherent_transitive.
Qed.

Lemma wn_pi_inj A B : wn (tPi A B) -> wn A /\ wn B.
Proof.
  move => [T []].
  move /pars_pi_inv.
  move => [A0 [B0 [ ? *]]].
  hauto q:on ctrs:rtc b:on.
Qed.

Lemma InterpExt_Fun_inv n Interp A B P  (h : InterpExt n Interp (tPi A B) P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpExt n Interp A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> InterpExt n Interp (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - move => *. by subst.
  - hauto l:on.
  - move => A A0 PT hr0 hA0 ih A1 B ?. subst.
    elim /Par_inv : hr0=>// hr0 A2 A3 B0 B1 ? ?[] *. subst.
    specialize ih with (1 := eq_refl).
    move : ih => [PA [PF [hPA [hTot [hRes ?]]] ]]. subst.
    exists PA, PF. repeat split.
    by eauto with iext.
    eauto.
    move => a PB hPB.
    have : Par (subst_tm (a..) B) (subst_tm (a..) B1) by sfirstorder use:Par_refl, par_cong.
    eauto with iext.
Qed.

Lemma InterpExt_deterministic n I A PA PB :
  InterpExt n I A PA ->
  InterpExt n I A PB ->
  PA = PB.
Proof.
  move => h.
  move : PB.
  elim : A PA / h.
  - hauto lq:on inv:InterpExt ctrs:InterpExt use:InterpExt_Ne_inv.
  - hauto lq:on inv:InterpExt ctrs:InterpExt use:InterpExt_Void_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Bool_inv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Fun_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    rewrite /ProdSpace.
    fext => b. f_equal.
    fext =>  a PB ha.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Eq_inv.
  - hauto l:on use:InterpExt_preservation.
Qed.

Lemma InterpExt_Fun_inv_nopf n I A B P  (h : InterpExt n I (tPi A B) P) :
  exists (PA : tm -> Prop),
    InterpExt n I A PA /\
    (forall a, PA a -> exists PB, InterpExt n I (subst_tm (a..) B) PB) /\
      P = ProdSpace PA (fun a => InterpExt n I (subst_tm (a..) B)).
Proof.
  move /InterpExt_Fun_inv : h. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
  exists PA. repeat split => //.
  - sfirstorder.
  - fext => b. rewrite /ProdSpace. f_equal. fext => a PB ha.
    apply propositional_extensionality.
    split.
    + move  : hPF ha . move /[apply]. intros (PB0 & hPB0). move => *.
      have ? : PB0 = PB by eauto using InterpExt_deterministic. sfirstorder.
    + sfirstorder.
Qed.

Lemma InterpUnivN_deterministic n A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN n A PB ->
  PA = PB.
Proof.
  simp InterpUnivN.
  eauto using InterpExt_deterministic.
Qed.

Lemma InterpExt_cumulative n m I A PA :
  n < m ->
  InterpExt n I A PA ->
  InterpExt m I A PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.lt_trans.
Qed.

Lemma InterpExt_lt_redundant n I A PA
  (h : InterpExt n I A PA) :
      InterpExt n (fun m A PA =>
                     match Compare_dec.lt_dec m n with
                     | left h => I m A PA
                     | right _ => False
                     end) A PA.
Proof.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    rewrite /SUniv.
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 n (I :fin -> tm -> (tm -> Prop) -> Prop ) A PA
  (h : InterpExt n (fun m A PA =>
                      match Compare_dec.lt_dec m n with
                     | left h => I m A PA
                     | right _ => False
                     end) A PA) :
  InterpExt n I A PA.
Proof.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m ?.
    apply InterpExt_Univ' => //.
    rewrite /SUniv.
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_nolt n :
  InterpUnivN n = InterpExt n InterpUnivN.
Proof.
  simp InterpUnivN.
  fext => A P.
  apply propositional_extensionality.
  hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpExt_Fun_nopf n I A B PA  :
  InterpExt n I A PA ->
  (forall a, PA a -> exists PB, InterpExt n I (subst_tm (a..) B) PB) ->
  InterpExt n I (tPi A B) (ProdSpace PA (fun a => InterpExt n I (subst_tm (a..) B))).
Proof.
  move => h0 h1. apply InterpExt_Fun =>//.
Qed.

Lemma InterpUnivN_Fun n A B PA :
  InterpUnivN n A PA ->
  (forall a, PA a -> exists PB, InterpUnivN n (subst_tm (a..) B) PB) ->
  InterpUnivN n (tPi A B) (ProdSpace PA (fun a => InterpUnivN n (subst_tm (a..) B))).
Proof.
  hauto l:on use:InterpExt_Fun_nopf rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Fun_inv_nopf n A B P  (h : InterpUnivN n (tPi A B) P) :
  exists (PA : tm -> Prop),
    InterpUnivN n A PA /\
    (forall a, PA a -> exists PB, InterpUnivN n (subst_tm (a..) B) PB) /\
      P = ProdSpace PA (fun a => InterpUnivN n (subst_tm (a..) B)).
Proof.
  qauto use:InterpExt_Fun_inv_nopf l:on rew:db:InterpUniv.
Qed.

Lemma InterpExt_deterministic' n m I A PA PB :
  InterpExt n I A PA ->
  InterpExt m I A PB ->
  PA = PB.
Proof.
  move => h0 h1.
  case : (Coq.Arith.Compare_dec.lt_eq_lt_dec m n); first case.
  - hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
  - move => *; subst.
    sfirstorder use:InterpExt_deterministic.
  - move => ?.
    symmetry.
    hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
Qed.

Lemma InterpUnivN_cumulative n A PA :
  InterpUnivN n A PA -> forall m, n < m ->
  InterpUnivN m A PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Lemma InterpUnivN_deterministic' n m  A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN m A PB ->
  PA = PB.
Proof. hauto lq:on rew:off use:InterpExt_deterministic' rew:db:InterpUniv. Qed.

Lemma InterpExt_back_clos n (I : nat -> tm -> (tm -> Prop) -> Prop) A PA
  (hI : forall m, m < n -> forall a b, Par a b -> forall PA, I m b PA -> I m a PA ):
  InterpExt n I A PA ->
  forall a b, Par a b ->
         PA b -> PA a.
Proof.
  move => h.
  elim : A PA / h.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF b0 b1 hb01.
    rewrite /ProdSpace.
    move => hPB a PB ha hPFa.
    have ? : Par (tApp b0 a)(tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
    hauto lq:on ctrs:Par.
  - hauto lq:on.
  - hauto lq:on ctrs:rtc.
  - sfirstorder.
Qed.

Lemma InterpUnivN_back_clos n A PA :
    InterpUnivN n A PA ->
    forall a b, Par a b ->
           PA b -> PA a.
Proof.
  simp InterpUniv.
  apply InterpExt_back_clos.
  qauto l:on rew:db:InterpUniv ctrs:InterpExt.
Qed.

Lemma InterpUnivN_back_clos_star n A PA :
    InterpUnivN n A PA ->
    forall a b, Pars a b ->
           PA b -> PA a.
Proof.
  move => h a b.
  induction 1; sfirstorder use:InterpUnivN_back_clos.
Qed.

Lemma InterpUnivN_Univ_inv i j :
  j < i ->
  InterpUnivN i (tUniv j) (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [|//].
  rewrite /SUniv.
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_Eq_inv n a b A P :
  InterpUnivN n (tEq a b A) P ->
  P = SEq a b /\ wn a /\ wn b /\ wn A.
Proof.
  simp InterpUniv.
  hauto l:on use:InterpExt_Eq_inv.
Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  InterpUnivN i (tUniv j) P ->
  P = (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv unfold:SUniv.
Qed.

Lemma InterpExt_WNe n I A : wne A -> InterpExt n I A wne.
Proof.
  rewrite /wne.
  move => [B [h0]].
  elim : A B / h0; eauto with iext.
Qed.

Lemma InterpUniv_wn_ty n A PA
  (h : InterpUnivN n A PA) :
  wn A.
Proof.
  move : n A PA h.
  elim /Wf_nat.lt_wf_ind => n ih A PA /[dup] hPA.
  simp InterpUniv.
  apply InterpExt_wn_ty.
  move => m /[dup] ?.
  move : ih. move/[apply] => ih.
  split.
  - sfirstorder.
  - rewrite /SUniv.
    simp InterpUniv.
    hauto l:on use:InterpExt_WNe.
Qed.

Lemma InterpUniv_adequacy n A PA
  (h : InterpUnivN n A PA)  :
  CR PA.
Proof.
  move : h.
  simp InterpUniv.
  apply adequacy.
  move => m ?.
  split.
  - hauto l:on use:InterpUniv_wn_ty unfold:SUniv.
  - rewrite /SUniv.
    move => A0 ?.
    simp InterpUniv.
    hauto lq:on use:InterpExt_WNe.
Qed.

Lemma InterpUniv_wn n A PA
  (h : InterpUnivN n A PA) :
  forall a, PA a -> wn a.
Proof. hauto q:on use:InterpUniv_adequacy unfold:wn. Qed.

Lemma InterpUniv_wne n A PA
  (h : InterpUnivN n A PA) :
  forall a, wne a -> PA a.
Proof. hauto q:on use:InterpUniv_adequacy unfold:wn. Qed.

Lemma InterpUnivN_Eq n a b A:
  wn a -> wn b -> wn A ->
  InterpUnivN n (tEq a b A) (SEq a b).
Proof.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  have ? : InterpUnivN n (tEq va vb vA) (SEq va vb)
    by hauto lq:on ctrs:InterpExt rew:db:InterpUniv.
  have ? : Pars (tEq a b A) (tEq va vb vA) by auto using S_Eq.
  have : InterpUnivN n (tEq a b A) (SEq va vb) by eauto using InterpUnivN_back_preservation_star.
  move /[dup] /InterpUnivN_Eq_inv. move => [?]. congruence.
Qed.
