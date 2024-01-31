From WR Require Import syntax join imports.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

Fixpoint ne (a : tm) :=
  match a with
  | var_tm _ => true
  | tApp a b => ne a && nf b
  | tAbs _ _ => false
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
  | tAbs A a => nf A && nf a
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
Proof. hauto lq: on inv: tm unfold:is_bool_val. Qed.

Lemma nf_wn v : nf v -> wn v.
Proof. sfirstorder ctrs:rtc. Qed.

Lemma ne_nf (a : tm) : ne a -> nf a.
Proof. elim : a =>//. Qed.

Create HintDb nfne.
#[export]Hint Resolve nf_wn bool_val_nf ne_nf : nfne.

Lemma nf_ne_step_eq (a : tm) : (nf a || ne a) -> forall b, Par a b -> a = b.
Proof.
  move => + b h.
  elim : a b /h=>///=;
    hauto lq:on inv:Par rew:off lqb:on db:nfne.
Qed.

Lemma ne_step_eq (a : tm) : ne a -> forall b, Par a b -> a = b.
Proof. sfirstorder use:nf_ne_step_eq b:on. Qed.

Lemma preservation_wn (a : tm) : wn a -> forall b, Par a b -> wn b.
Proof.
  rewrite /wn. move => [v [hv]].
  elim : a v / hv.
  - move => v hv b *.
    have ? : v = b by sfirstorder use:nf_ne_step_eq b:on. subst.
    eauto using rtc_refl.
  - move => a0 a1 a2 hr0 hr1 /[apply] h a1' hr'.
    move : par_confluent hr0 hr'. repeat move/[apply].
    hauto lq:on ctrs:rtc.
Qed.

Lemma ne_nf_renaming (a : tm) :
  forall (ξ : nat -> nat),
    (ne a <-> ne (ren_tm ξ a)) /\ (nf a <-> nf (ren_tm ξ a)).
Proof.
  elim : a; solve [auto; hauto b:on].
Qed.

Lemma wn_antirenaming a (ξ : nat -> nat) : wn (ren_tm ξ a) -> wn a.
Proof.
  rewrite /wn.
  move => [v [rv nfv]].
  move /Pars_antirenaming : rv => [b [? hb]]. subst.
  sfirstorder use:ne_nf_renaming.
Qed.

(* Lemma ext_wn (a : tm) i : *)
(*     wn (tApp a (var_tm i)) -> *)
(*     wn a. *)
(* Proof. *)
(*   move E : (tApp a (var_tm i)) => a0 [v [hr hv]]. *)
(*   move : a E. *)
(*   move : hv. *)
(*   elim : a0 v / hr. *)
(*   - hauto q:on inv:tm ctrs:rtc b:on db: nfne. *)
(*   - move => a0 a1 a2 hr0 hr1 ih hnfa2. *)
(*     move /(_ hnfa2) in ih. *)
(*     move => a. *)
(*     case : a0 hr0=>// => b0 b1. *)
(*     elim /Par_inv=>//. *)
(*     + hauto q:on inv:Par ctrs:rtc b:on. *)
(*     + move => ? a0 A a3 b2 b3 ? ? [? ?] ? [? ?]. subst. *)
(*       have ? : b3 = var_tm i by hauto lq:on inv:Par. subst. *)
(*       suff : wn (tAbs A a3) by hauto lq:on unfold:wn ctrs:rtc. *)
(*       have : wn (subst_tm ((var_tm i) ..) a3) by sfirstorder. *)
(*       replace (subst_tm ((var_tm i) ..) a3) with (ren_tm (i..) a3). *)
(*       move /wn_antirenaming. *)
(*       admit. *)
(*       substify; by asimpl. *)
(* Admitted. *)

Definition SBool (a : tm) := exists v, Pars a v /\ (is_bool_val v \/ ne v).
Definition SUniv (I : nat -> tm -> (tm -> Prop) -> Prop) m A := exists PA, I m A PA.
Definition SEq a b p := (Pars p tRefl /\ Coherent a b) \/ wne p.

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
  wn a ->
  wn b ->
  wn A ->
  InterpExt n I (tEq a b A) (SEq a b)
| InterpExt_Step A A0 PA :
  Par A A0 ->
  InterpExt n I A0 PA ->
  InterpExt n I A PA.

Hint Constructors InterpExt : iext.


Definition CR (P : tm -> Prop) :=
  (forall a, P a -> wn a) /\
    (forall a, wne a -> P a).

Lemma S_AppLR (a a0 b b0 : tm) :
  Pars a a0 ->
  Pars b b0 ->
  Pars (tApp a b) (tApp a0 b0).
Proof.
  move => h. move :  b b0.
  elim : a a0 / h.
  - move => a a0 b h.
    elim : a0 b / h.
    + sfirstorder ctrs:rtc use:Par_refl.
    + move => b0 b1 b2 h0 h1 h2.
      eapply rtc_l; eauto.
      hauto lq:on ctrs:rtc,Par use:Par_refl.
  - move => a0 a1 a2 h0 h1 ih b0 b1 h2.
    eapply rtc_l; eauto.
    hauto lq:on ctrs:rtc, Par use:Par_refl.
Qed.

Lemma wne_app (a b : tm) :
  wne a -> wn b -> wne (tApp a b).
Proof.
  case => a0 [h00 h01].
  case => b0 [h10 h11].
  rewrite /wne.
  exists (tApp a0 b0).
  hauto b:on use:S_AppLR.
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
    + rewrite /ProdSpace => b wnea a PB ha hPB.
      suff : wn a by hauto q:on use:wne_app. firstorder.
  - hauto lq:on db:nfne.
Qed.

Lemma InterpExt_Fun_nopf n I A B PA  :
  InterpExt n I A PA ->
  (forall a, PA a -> exists PB, InterpExt n I (subst_tm (a..) B) PB) ->
  InterpExt n I (tPi A B) (ProdSpace PA (fun a => InterpExt n I (subst_tm (a..) B))).
Proof.
  move => h0 h1. apply InterpExt_Fun =>//.
Qed.

Lemma InterpExt_Eq' n I PA a b A :
  wn a ->
  wn b ->
  wn A ->
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
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:par_subst.
Qed.

Lemma InterpExt_preservation n I A B P (h : InterpExt n I A P) :
  Par A B ->
  InterpExt n I B P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto l:on inv:- use:ne_step_eq ctrs:InterpExt.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpExt_Fun; auto.
    move => a PB hPB0.
    apply : ihPB; eauto.
    sfirstorder use:par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => a b A ?  ? ? B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpExt_Eq'; eauto using preservation_wn.
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
  hauto l:on inv:- use:ne_step_eq.
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
  - hauto lq:on rew:off inv:Par.
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
    fext => b a PB ha.
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
  - fext => b a PB ha.
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
    rewrite /ProdSpace => hPB a PB ha hPFa.
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

Lemma S_Eq a0 a1 b0 b1 A0 A1 :
  Pars a0 a1 ->
  Pars b0 b1 ->
  Pars A0 A1 ->
  Pars (tEq a0 b0 A0) (tEq a1 b1 A1).
Proof.
  move => h.
  move : b0 b1 A0 A1.
  elim : a0 a1 /h.
  - admit.
  - move => a0 a1 a2 ih b0 b1 A0 A1 A2 A3 hr0 hr1.
    eapply rtc_l; eauto.
    hauto lq:on ctrs:Par use:Par_refl.
Admitted.

Lemma wn_eq a b A : wn a -> wn b -> wn A -> wn (tEq a b A).
Proof.
  rewrite /wn.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  exists (tEq va vb vA).
  split.
  - by apply S_Eq.
  - hauto lqb:on.
Qed.

Lemma wn_pi A B : wn A -> wn B -> wn (tPi A B).
Admitted.

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
  - exact wn_eq.
  - hauto lq:on ctrs:rtc.
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
