From WR Require Import syntax join imports.

(* Construct a predicate on terms that act like functions, 
   given a predicate on domains (PA) and an indexed predicate (PF)
   selects codomain predictates (PB) that correspond to arguments (a).
*)
Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) : tm -> Prop :=
  fun b => forall a PB, PA a -> PF a PB -> PB (tApp b a).

Notation "a ~ b @ A"   := (tEq a b A) (at level 70, right associativity).

(* Logical Relation: 

  InterpExp i I S

     written 

  ⟦ A ⟧ i , I ↘ S  

  holds when
   - A is a Set j <= i
   - S is a predicate on terms that act like type A
   - I is the interpretation of "Set j" for j < i

  We define this in two parts: one that generalizes over
  smaller interpretations and then tie the knot
  with the real definition below.

 *)

Reserved Notation "⟦ A ⟧ i , I ↘ S" (at level 70).
Inductive InterpExt i (I : nat -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=

| InterpExt_Void : 
  ⟦ tVoid ⟧ i , I ↘ (const False)

| InterpExt_Bool : 
  ⟦ tBool ⟧ i , I ↘ (fun a => exists v, a ⇒* v /\ is_bool_val v)

| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tPi A B ⟧ i , I ↘ (ProdSpace PA PF)

| InterpExt_Univ j :
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ (I m)

| InterpExt_Eq a b A :
  ⟦ tEq a b A ⟧ i , I ↘ (fun p => p ⇒* tRefl /\ Coherent a b)

| InterpExt_Step A A0 PA :
  (A ⇒ A0) ->
  ⟦ A0 ⟧ i , I ↘ PA ->
  ⟦ A ⟧ i , I ↘ PA
where "⟦ A ⟧ i , I ↘ S" := (InterpExt i I A S).


Lemma InterpExt_Eq' i I PA a b A :
  PA = (fun p => p ⇒* tRefl /\ Coherent a b) ->
  ⟦ a ~ b @ A ⟧ i , I ↘ PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' i I j PF :
  PF = I j ->
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Infix "<?" := Compare_dec.lt_dec (at level 60).

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf i lt :=
  InterpUnivN i := InterpExt i (fun j A =>
                                  match j <? i with
                                  | left _ => exists PA, InterpUnivN j A PA
                                  | right _ => False
                                  end).

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

(* ---------------------------------------------------- *)

(* The definition of InterpUnivN is more complicated than
   it needs to be. We show that that we can
   simplify the unfolding above to just mention InterpUnivN
   without doing the case analysis.
*)
Lemma InterpExt_lt_redundant i I A PA
  (h : ⟦ A ⟧ i , I ↘ PA) :
       ⟦ A ⟧ i , (fun j A =>
                     match j <? i with
                     | left h => I j A
                     | right _ => False
                     end) ↘ PA.
Proof.
  elim : A PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => j h.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 i I A PA
  (h : ⟦ A ⟧ i , (fun j A =>
                      match j <? i with
                     | left h => I j A
                     | right _ => False
                     end) ↘ PA) :
  ⟦ A ⟧ i , I ↘ PA.
Proof.
  elim : A PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => j ?.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_nolt i :
  InterpUnivN i = InterpExt i (fun j A => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUnivN.
  fext => A P.
  apply propositional_extensionality.
  hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpExt_Fun_inv i I A B P  
  (h :  ⟦ tPi A B ⟧ i , I ↘ P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
     ⟦ A ⟧ i , I ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) /\
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

Lemma InterpExt_Fun_nopf i I A B PA  :
   ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i , I ↘  PB) ->
  InterpExt i I (tPi A B) (ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i , I ↘ PB)).
Proof.
  move => h0 h1. apply InterpExt_Fun =>//.
Qed.

Lemma InterpUnivN_Fun_nopf i A B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB) ->
  ⟦ tPi A B ⟧ i ↘ (ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB)).
Proof.
  hauto l:on use:InterpExt_Fun_nopf rew:db:InterpUniv.
Qed.

(* --------------- relation is cumulative ----------------- *)

Lemma InterpExt_cumulative i j I A PA :
  i < j ->
   ⟦ A ⟧ i , I ↘ PA ->
  InterpExt j I A PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.lt_trans.
Qed.

Lemma InterpUnivN_cumulative i A PA :
  InterpUnivN i A PA -> forall m, i < j ->
  InterpUnivN j A PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

(* ------------------------------------------------------- *)

(* The logical relation is closed under parallel reduction,
   forwards and backwards. *)

Lemma InterpExt_preservation i I A B P (h : InterpExt i I A P) :
  A ⇒ B ->
  InterpExt i I B P.
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

Lemma InterpUnivN_preservation i A B P (h : InterpUnivN i A P) :
  A ⇒ B ->
  InterpUnivN i B P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I A B P (h : InterpExt i I B P) :
  A ⇒* B ->
  InterpExt i I A P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star i I A B P (h : InterpExt i I A P) :
  A ⇒* B ->
  InterpExt i I B P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star i A B P (h : InterpUnivN i A P) :
  A ⇒* B ->
  InterpUnivN i B P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star i A B P (h : InterpUnivN i B P) :
  A ⇒* B ->
  InterpUnivN i A P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

(* ---------------------------------------------------------- *)

Lemma InterpUnivN_Coherent i A B P (h : InterpUnivN i B P) :
  Coherent A B ->
  InterpUnivN i A P.
Proof.
  hauto l:on unfold:Coherent use:InterpUnivN_back_preservation_star, InterpUnivN_preservation_star.
Qed.

(* ---------------------------------------------------------- *)
(* inversion lemmas for InterpExt. To invert the InterpExt
   judgment, we have to be careful about the step case. *)

Lemma InterpExt_Bool_inv i I P :
  InterpExt i I tBool P ->
  P = fun a => exists v, a ⇒* v /\ is_bool_val v.
Proof.
  move E : tBool => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Void_inv i I P :
  InterpExt i I tVoid P ->
  P = (const False).
Proof.
  move E : tVoid => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Univ_inv i I P j :
  InterpExt i I (tUniv m) P ->
  P = I j /\ j < n.
Proof.
  move E : (tUniv m) => A h.
  move : E.
  elim : A P / h; hauto lq:on rew:off inv:Par.
Qed.

Lemma InterpUnivN_Bool_inv i P :
  InterpUnivN i tBool P ->
  P = fun a => exists v, a ⇒* v /\ is_bool_val v.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Bool_inv. Qed.

Lemma InterpExt_Eq_inv i I a b A P :
  InterpExt i I (tEq a b A) P ->
  P = (fun A => A ⇒* tRefl /\ Coherent a b).
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

Lemma InterpExt_deterministic i I A PA PB :
  ⟦ A ⟧ i , I ↘ PA ->
  ⟦ A ⟧ i , I ↘ PB ->
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

Lemma InterpUnivN_deterministic i A PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PB ->
  PA = PB.
Proof.
  simp InterpUnivN. apply InterpExt_deterministic.
Qed.

(* slight generalization to work with any levels using cumulativity. *)

Lemma InterpExt_deterministic' i j I A PA PB :
   ⟦ A ⟧ i , I ↘ PA ->
   ⟦ A ⟧ j , I ↘ PB ->
  PA = PB.
Proof.
  move => h0 h1.
  case : (j <? n); first case.
  - hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
  - move => *; subst.
    sfirstorder use:InterpExt_deterministic.
  - move => ?.
    symmetry.
    hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
Qed.

Lemma InterpUnivN_deterministic' i j  A PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ j ↘ PB ->
  PA = PB.
Proof. hauto lq:on rew:off use:InterpExt_deterministic' rew:db:InterpUniv. Qed.

(* ----- Improved inversion lemma for functions (Pi Inv Alt) ---------- *)

Lemma InterpExt_Fun_inv_nopf i I A B P  (h : InterpExt i I (tPi A B) P) :
  exists (PA : tm -> Prop),
     ⟦ A ⟧ i , I ↘ PA /\
    (forall a, PA a -> exists PB, InterpExt i I (B[a..]) PB) /\
      P = ProdSpace PA (fun a PB => InterpExt i I (B[a..]) PB).
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

Lemma InterpUnivN_Fun_inv_nopf i A B P  (h : InterpUnivN i (tPi A B) P) :
  exists (PA : tm -> Prop),
    InterpUnivN i A PA /\
    (forall a, PA a -> exists PB, InterpUnivN i (B[a..]) PB) /\
      P = ProdSpace PA (fun a PB => InterpUnivN i (B[a..]) PB).
Proof.
  qauto use:InterpExt_Fun_inv_nopf l:on rew:db:InterpUniv.
Qed.

(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos i A PA :
    InterpUnivN i A PA ->
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

Lemma InterpUnivN_back_clos_star i A PA :
    InterpUnivN i A PA ->
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
