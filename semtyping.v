From WR Require Import syntax join imports.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

Infix "⇒*" := Pars (at level 60, right associativity).
Infix "⇒" := Par (at level 60, right associativity).

(* Logical Relation:

  InterpUnivN i A P  holds when
   - A is a Set i
   - P is a predicate on terms that act like type A

  We define this in two parts: one that generalizes over
  smaller interpretations and then tie the knot
  with the real definition below.

 *)

Reserved Notation "⟦ A ⟧ n , I ↘ S" (at level 70).
Inductive InterpExt n (I : nat -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_Void : 
  ⟦ tVoid ⟧ n , I ↘ (const False)
| InterpExt_Bool : 
  ⟦ tBool ⟧ n , I ↘ (fun a => exists v, a ⇒* v /\ is_bool_val v)
| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ n , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_tm (a..) B ⟧ n , I ↘ PB) ->
  ⟦ tPi A B ⟧ n , I ↘ (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  ⟦ tUniv m ⟧ n , I ↘ (I m)
| InterpExt_Eq a b A :
  ⟦ tEq a b A ⟧ n , I ↘ (fun p => p ⇒* tRefl /\ Coherent a b)
| InterpExt_Step A A0 PA :
  A ⇒ A0 ->
  ⟦ A0 ⟧ n , I ↘ PA ->
  ⟦ A ⟧ n , I ↘ PA
where "⟦ A ⟧ n , I ↘ S" := (InterpExt n I A S).

Notation "a ~ b @ A"   := (tEq a b A) (at level 70, right associativity).


Lemma InterpExt_Eq' n I PA a b A :
  PA = (fun p => Pars p tRefl /\ Coherent a b) ->
  ⟦ a ~ b @ A ⟧ n , I ↘ PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' n I m PF :
  PF = I m ->
  m < n ->
  ⟦ tUniv m ⟧ n , I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => exists PA, InterpUnivN m A PA
                                  | right _ => False
                                  end).

Notation "⟦ A ⟧ n ↘ S" := (InterpUnivN n A S) (at level 70).

(* ---------------------------------------------------- *)

(* The definition of InterpUnivN is more complicated than
   it needs to be. We show that that we can
   simplify the unfolding above to just mention InterpUnivN
   without doing the case analysis.
*)
Lemma InterpExt_lt_redundant n I A PA
  (h : ⟦ A ⟧ n , I ↘ PA) :
       ⟦ A ⟧ n , (fun m A =>
                     match Compare_dec.lt_dec m n with
                     | left h => I m A
                     | right _ => False
                     end) ↘ PA.
Proof.
  elim : A PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on.
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
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m ?.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on.
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

Lemma InterpExt_Fun_inv n I A B P  
  (h : InterpExt n I (tPi A B) P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpExt n I A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> InterpExt n I (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto l:on.
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:par_subst.
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
  ⟦ A ⟧ n ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_tm (a..) B ⟧ n ↘ PB) ->
  ⟦ tPi A B ⟧ n ↘ (ProdSpace PA (fun a PB => ⟦ subst_tm (a..) B ⟧ n ↘ PB)).
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
  Par A B ->
  InterpExt n I B P.
Proof.
  move : B.
  elim : A P / h; auto.
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
  - move => a b A B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpExt_Eq'.
    fext => p.
    f_equal.
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

Lemma InterpExt_Bool_inv n I P :
  InterpExt n I tBool P ->
  P = fun a => exists v, Pars a v /\ is_bool_val v.
Proof.
  move E : tBool => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Void_inv n I P :
  InterpExt n I tVoid P ->
  P = (const False).
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
  elim : A P / h; hauto lq:on rew:off inv:Par.
Qed.

Lemma InterpUnivN_Bool_inv n P :
  InterpUnivN n tBool P ->
  P = fun a => exists v, Pars a v /\ is_bool_val v.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Bool_inv. Qed.

Lemma InterpExt_Eq_inv n I a b A P :
  InterpExt n I (tEq a b A) P ->
  P = (fun A => Pars A tRefl /\ Coherent a b).
Proof.
  move E : (tEq a b A) => T h.
  move : a b A E.
  elim : T P /h => //. hauto lq:on rew:off inv:Par.
  move => A A0 PA hred hA0 ih a b A1 ?. subst.
  elim /Par_inv : hred=>//.
  move => hred ? ? ? a2 b2 A2 ? ? ? [] *;subst.
  specialize ih with (1 := eq_refl).
  rewrite ih.
  fext => A. f_equal.
  apply propositional_extensionality.
  hauto lq:on use:Par_Coherent, Coherent_symmetric, Coherent_transitive.
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

(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos n A PA :
    InterpUnivN n A PA ->
    forall a b, Par a b ->
           PA b -> PA a.
Proof.
  simp InterpUniv => h.
  elim : A PA /h.
  - sfirstorder.
  - hauto lq:on ctrs:rtc.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF b0 b1 hb01.
    rewrite /ProdSpace => hPB a PB ha hPFa.
    have ? : Par (tApp b0 a)(tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
    hauto lq:on ctrs:Par.
  - qauto l:on rew:db:InterpUniv ctrs:InterpExt.
  - hauto lq:on ctrs:rtc.
  - sfirstorder.
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
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  InterpUnivN i (tUniv j) P ->
  P = (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv.
Qed.
