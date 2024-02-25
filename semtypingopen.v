From WR Require Import syntax join normalform imports.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

(* Logical Relation:

  InterpUnivN i A P  holds when
   - A is a Set i
   - P is a predicate on terms that act like type A

  We define this in two parts: one that generalizes over
  smaller interpretations and then tie the knot
  with the real definition below.

 *)

Inductive InterpExt n (I : nat -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_Ne A : ne A -> InterpExt n I A wne
| InterpExt_Void : InterpExt n I tVoid wne
| InterpExt_Bool : InterpExt n I tBool (fun a => exists v, a ⇒* v /\ (is_bool_val v \/ ne v))
| InterpExt_Fun A B PA PF :
  InterpExt n I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> InterpExt n I (subst_tm (a..) B) PB) ->
  InterpExt n I (tPi A B) (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  InterpExt n I (tUniv m) (I m)
| InterpExt_Eq a b A :
  nf a ->
  nf b ->
  nf A ->
  InterpExt n I (tEq a b A) (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p)
| InterpExt_Step A A0 PA :
  (A ⇒ A0) ->
  InterpExt n I A0 PA ->
  InterpExt n I A PA.

Lemma InterpExt_Eq' n I PA a b A :
  nf a ->
  nf b ->
  nf A ->
  PA = (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p) ->
  InterpExt n I (tEq a b A) PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' n I m PF :
  PF = I m ->
  m < n ->
  InterpExt n I (tUniv m) PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => exists PA, InterpUnivN m A PA
                                  | right _ => False
                                  end).

(* TODO: use this notation in the definition of InterpExt *)
Notation "⟦ A ⟧ i , I ↘ S" := (InterpExt i I A S) (at level 70).
Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

(* ---------------------------------------------------- *)

(* The definition of InterpUnivN is more complicated than
   it needs to be. We show that that we can
   simplify the unfolding above to just mention InterpUnivN
   without doing the case analysis.
*)
Lemma InterpExt_lt_redundant n I A PA
  (h : InterpExt n I A PA) :
      InterpExt n (fun m A =>
                     match Compare_dec.lt_dec m n with
                     | left h => I m A
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
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 n I A PA
  (h : InterpExt n (fun m A =>
                      match Compare_dec.lt_dec m n with
                     | left h => I m A
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
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_nolt n :
  InterpUnivN n = InterpExt n (fun m A => exists PA, InterpUnivN m A PA).
Proof.
  simp InterpUnivN.
  fext => A P.
  apply propositional_extensionality.
  hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpExt_Fun_inv n I A B P  (h : InterpExt n I (tPi A B) P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpExt n I A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> InterpExt n I (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto q:on inv:tm.
  - hauto l:on.
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:Par_subst.
Qed.


(* For all of the proofs about InterpUnivN below, we need to
   do them in two steps. Once for InterpExt, and then tie the
   knot for the full definition. *)

(* -----  I-PiAlt is admissible (free of PF, the relation R on paper)  ---- *)

Lemma InterpExt_Fun_nopf n I A B PA  :
  InterpExt n I A PA ->
  (forall a, PA a -> exists PB, InterpExt n I (subst_tm (a..) B) PB) ->
  InterpExt n I (tPi A B) (ProdSpace PA (fun a => InterpExt n I (subst_tm (a..) B))).
Proof.
  move => h0 h1. apply InterpExt_Fun =>//.
Qed.

Lemma InterpUnivN_Fun_nopf n A B PA :
  InterpUnivN n A PA ->
  (forall a, PA a -> exists PB, InterpUnivN n (subst_tm (a..) B) PB) ->
  InterpUnivN n (tPi A B) (ProdSpace PA (fun a => InterpUnivN n (subst_tm (a..) B))).
Proof.
  hauto l:on use:InterpExt_Fun_nopf rew:db:InterpUniv.
Qed.

(* --------------- relation is cumulative ----------------- *)

Lemma InterpExt_cumulative n m I A PA :
  n < m ->
  InterpExt n I A PA ->
  InterpExt m I A PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.lt_trans.
Qed.

Lemma InterpUnivN_cumulative n A PA :
  InterpUnivN n A PA -> forall m, n < m ->
  InterpUnivN m A PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

(* ------------------------------------------------------- *)

(* The logical relation is closed under parallel reduction,
   forwards and backwards. *)

Lemma InterpExt_preservation n I A B P (h : InterpExt n I A P) :
  (A ⇒ B) ->
  InterpExt n I B P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto lq:on ctrs:InterpExt db:nfne.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpExt_Fun; auto.
    move => a PB hPB0.
    apply : ihPB; eauto.
    sfirstorder use:Par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => a b A  ? ? ? B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpExt_Eq'; eauto with nfne.
    fext => p.
    f_equal.
    apply propositional_extensionality.
    hauto lq:on use:Par_Coherent, Coherent_transitive, Coherent_symmetric.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := Par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation n A B P (h : InterpUnivN n A P) :
  (A ⇒ B) ->
  InterpUnivN n B P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I A B P (h : InterpExt i I B P) :
  A ⇒* B ->
  InterpExt i I A P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star n I A B P (h : InterpExt n I A P) :
  A ⇒* B ->
  InterpExt n I B P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star n A B P (h : InterpUnivN n A P) :
  A ⇒* B ->
  InterpUnivN n B P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star n A B P (h : InterpUnivN n B P) :
  A ⇒* B ->
  InterpUnivN n A P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

(* ---------------------------------------------------------- *)

Lemma InterpUnivN_Coherent n A B P (h : InterpUnivN n B P) :
  Coherent A B ->
  InterpUnivN n A P.
Proof.
  hauto l:on unfold:Coherent use:InterpUnivN_back_preservation_star, InterpUnivN_preservation_star.
Qed.

(* ---------------------------------------------------------- *)
(* inversion lemmas for InterpExt. To invert the InterpExt
   judgment, we have to be careful about the step case. *)

Lemma InterpExt_Ne_inv n I A P :
  ne A ->
  InterpExt n I A P ->
  P = wne.
Proof.
  move => + h0.
  elim : A P /h0 =>//.
  hauto l:on inv:- db:nfne.
Qed.

Lemma InterpExt_Bool_inv n I P :
  InterpExt n I tBool P ->
  P = fun a => exists v, a ⇒* v /\ (is_bool_val v \/ ne v).
Proof.
  move E : tBool => A h.
  move : E.
  elim : A P / h; hauto q:on inv:tm,Par.
Qed.

Lemma InterpExt_Void_inv n I P :
  InterpExt n I tVoid P ->
  P = wne.
Proof.
  move E : tVoid => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Univ_inv n I P m :
  InterpExt n I (tUniv m) P ->
  P = I m /\ m < n.
Proof.
  move E : (tUniv m) => A h.
  move : E.
  elim : A P / h; hauto q:on rew:off inv:Par,tm.
Qed.

Lemma InterpUnivN_Bool_inv n P :
  InterpUnivN n tBool P ->
  P = fun a => exists v, a ⇒* v /\ (is_bool_val v \/ ne v).
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Bool_inv. Qed.

Lemma InterpExt_Eq_inv n I a b A P :
  InterpExt n I (tEq a b A) P ->
  (P = fun A => A ⇒* tRefl /\ Coherent a b \/ wne A) /\ wn a /\ wn b /\ wn A.
Proof.
  move E : (tEq a b A) => T h.
  move : a b A E.
  elim : T P /h => //.
  hauto q:on inv:tm.
  hauto lq:on ctrs:rtc.
  move => A A0 PA hred hA0 ih a b A1 ?. subst.
  elim /Par_inv : hred=>//.
  move => hred ? ? ? a2 b2 A2 ? ? ? [] *;subst.
  split; last by hauto lq:on rew:off ctrs:rtc.
  specialize ih with (1 := eq_refl).
  move : ih => [->] *.
  fext => A. do 2 f_equal.
  apply propositional_extensionality.
  hauto lq:on use:Par_Coherent, Coherent_symmetric, Coherent_transitive.
Qed.

Lemma InterpUnivN_Eq_inv n a b A P :
  InterpUnivN n (tEq a b A) P ->
  P = (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p) /\ wn a /\ wn b /\ wn A.
Proof.
  simp InterpUniv.
  hauto l:on use:InterpExt_Eq_inv.
Qed.

(* ------------- relation is deterministic ---------------- *)

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

Lemma InterpUnivN_deterministic n A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN n A PB ->
  PA = PB.
Proof.
  simp InterpUnivN. apply InterpExt_deterministic.
Qed.

(* slight generalization to work with any levels using cumulativity. *)

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

Lemma InterpUnivN_deterministic' n m  A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN m A PB ->
  PA = PB.
Proof. hauto lq:on rew:off use:InterpExt_deterministic' rew:db:InterpUniv. Qed.

(* ----- Improved inversion lemma for functions (Pi Inv Alt) ---------- *)

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

Lemma InterpUnivN_Fun_inv_nopf n A B P  (h : InterpUnivN n (tPi A B) P) :
  exists (PA : tm -> Prop),
    InterpUnivN n A PA /\
    (forall a, PA a -> exists PB, InterpUnivN n (subst_tm (a..) B) PB) /\
      P = ProdSpace PA (fun a => InterpUnivN n (subst_tm (a..) B)).
Proof.
  qauto use:InterpExt_Fun_inv_nopf l:on rew:db:InterpUniv.
Qed.

(* ---- Alternative intro rule for Eq ----------- *)
Lemma InterpUnivN_Eq n a b A:
  wn a -> wn b -> wn A ->
  InterpUnivN n (tEq a b A) (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p).
Proof.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  have ? : InterpUnivN n (tEq va vb vA) (fun p => (p ⇒* tRefl /\ Coherent va vb) \/ wne p)
    by hauto lq:on ctrs:InterpExt rew:db:InterpUniv.
  have ? : (tEq a b A) ⇒* (tEq va vb vA) by auto using S_Eq.
  have : InterpUnivN n (tEq a b A) (fun p => (p ⇒* tRefl /\ Coherent va vb) \/ wne p) by eauto using InterpUnivN_back_preservation_star.
  move /[dup] /InterpUnivN_Eq_inv. move => [?]. congruence.
Qed.


(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos n A PA :
    InterpUnivN n A PA ->
    forall a b, (a ⇒ b) ->
           PA b -> PA a.
Proof.
  simp InterpUniv => h.
  elim : A PA /h.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF b0 b1 hb01.
    rewrite /ProdSpace => hPB a PB ha hPFa.
    have ? : (tApp b0 a ⇒ tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
    hauto lq:on ctrs:Par.
  - qauto l:on rew:db:InterpUniv ctrs:InterpExt.
  - hauto lq:on ctrs:rtc.
  - sfirstorder.
Qed.

Lemma InterpUnivN_back_clos_star n A PA :
    InterpUnivN n A PA ->
    forall a b, a ⇒* b ->
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
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  InterpUnivN i (tUniv j) P ->
  P = (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv.
Qed.

(* ------------------------ adequacy ------------------------------- *)

(* P identifies a set of "reducibility candidates" *)
Definition CR (P : tm -> Prop) :=
  (forall a, P a -> wn a) /\
    (forall a, wne a -> P a).

(* Every interpretation of types is a reducibility candidate *)
Lemma adequacy n A PA
  (h : InterpUnivN n A PA) :
  CR PA.
Proof.
  elim /Wf_nat.lt_wf_ind : n A PA h.
  move => n ihn A PA h.
  simp  InterpUniv in h.
  elim : A PA / h =>//.
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
  - move => m hlt.
    split.
    + move => A [PA h].
      simp InterpUniv in h.
      elim : A PA / h; auto with nfne.
      * move => A B PA PF hPA wnA hTot hRes ih.
        apply wn_pi; first by auto.
        have ? : CR PA by hauto lq:on rew:db:InterpUniv.
        have hzero : PA (var_tm var_zero) by hauto q:on ctrs:rtc.
        move : hTot (hzero); move/[apply]. move => [PB].
        move /ih.
        match goal with [|- wn ?Q -> _] => replace Q with (ren_tm (var_zero..) B) end.
        eauto using wn_antirenaming.
        substify. by asimpl.
      * hauto lq:on use:wn_eq ctrs:rtc.
      * hauto lq:on ctrs:rtc.
    + hauto lq:on ctrs:InterpExt use:InterpExt_back_preservation_star rew:db:InterpUniv unfold:wne.
  - hauto lq:on db:nfne.
Qed.

Corollary InterpUniv_wn_ty n A PA
  (h : InterpUnivN n A PA) :
  wn A.
Proof.
  suff : exists PA, InterpUnivN (S n) (tUniv n) PA /\ PA A by hauto q:on use:adequacy.
  eexists.
  split.
  qauto l:on ctrs:InterpExt rew:db:InterpUniv.
  move =>//. eauto.
Qed.
