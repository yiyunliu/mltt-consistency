From WR Require Import syntax join imports.

(* Construct a predicate on terms that act like functions, 
   given a predicate on domains (PA) and an indexed predicate (PF)
   selects codomain predictates (PB) that correspond to arguments (a).
*)
Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) : tm -> Prop :=
  fun b => forall a PB, PA a -> PF a PB -> PB (tApp b a).

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
Inductive InterpExt i (I : forall j, j < i -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=

| InterpExt_Void : 
  ⟦ tVoid ⟧ i , I ↘ (const False)

| InterpExt_Bool : 
  ⟦ tBool ⟧ i , I ↘ (fun a => exists v, a ⇒* v /\ is_bool_val v)

| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tPi A B ⟧ i , I ↘ (ProdSpace PA PF)

| InterpExt_Univ j lt :
  ⟦ tUniv j ⟧ i , I ↘ (I j lt)

| InterpExt_Eq a b A :
  ⟦ tEq a b A ⟧ i , I ↘ (fun p => p ⇒* tRefl /\ Coherent a b)

| InterpExt_Step A A0 PA :
  (A ⇒ A0) ->
  ⟦ A0 ⟧ i , I ↘ PA ->
  ⟦ A ⟧ i , I ↘ PA
where "⟦ A ⟧ i , I ↘ S" := (InterpExt i I A S).

Lemma InterpExt_Eq' i I PA a b A :
  PA = (fun p => p ⇒* tRefl /\ Coherent a b) ->
  ⟦ tEq a b A ⟧ i , I ↘ PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' i I j PF lt :
  PF = I j lt ->
  ⟦ tUniv j ⟧ i , I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (i : nat) : tm -> (tm -> Prop) -> Prop by wf i lt :=
  InterpUnivN i := InterpExt i (fun j lt A => exists PA, InterpUnivN j A PA).

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

(* ---------------------------------------------------- *)

Lemma InterpUnivN_nolt i :
  InterpUnivN i = InterpExt i (fun j lt A => exists PA, ⟦ A ⟧ j ↘ PA).
Proof. simp InterpUnivN. reflexivity. Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

(* Properties of < on naturals that seem to be missing from the stdlib *)

Lemma lt_unique {n m} (lt1 lt2 : n < m) : lt1 = lt2.
Proof. apply Peano_dec.le_unique. Qed.

Lemma lt_trans {n m p} : n < m -> m < p -> n < p.
Proof. lia. Qed.

Lemma lt_max_l {n m} : n < S (max n m).
Proof. lia. Qed.

Lemma lt_max_r {n m} : m < S (max n m).
Proof. lia. Qed.

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
    hauto lq:on inv:Par ctrs:InterpExt use:Par_subst.
Qed.

(* For all of the proofs about InterpUnivN below, we need to
   do them in two steps. Once for InterpExt, and then tie the
   knot for the full definition. *)

(* -----  I-PiAlt is admissible (free of PF, the relation R on paper)  ---- *)

Lemma InterpExt_Fun_nopf i I A B PA  :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i , I ↘  PB) ->
  ⟦ tPi A B ⟧ i , I ↘ (ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i , I ↘ PB)).
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

Lemma InterpExt_cumulative i j I A PA ltij :
   ⟦ A ⟧ i , (fun k ltki => I k (lt_trans ltki ltij)) ↘ PA ->
   ⟦ A ⟧ j , I ↘ PA.
Proof.
  move => h.
  elim : A PA /h;
    hauto l:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_cumulative i A PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i < j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

(* ------------------------------------------------------- *)

(* The logical relation is closed under parallel reduction,
   forwards and backwards. *)

Lemma InterpExt_preservation i I A B P (h : InterpExt i I A P) :
  A ⇒ B ->
  ⟦ B ⟧ i , I ↘ P.
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
    sfirstorder use:Par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => a b A B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpExt_Eq'.
    fext => p.
    f_equal.
    apply propositional_extensionality.
    hauto lq:on use:Par_Coherent, Coherent_transitive, Coherent_symmetric.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := Par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation i A B P (h : ⟦ A ⟧ i ↘ P) :
  A ⇒ B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I A B P (h : ⟦ B ⟧ i , I ↘ P) :
  A ⇒* B ->
  ⟦ A ⟧ i , I ↘ P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star i I A B P (h : ⟦ A ⟧ i , I ↘ P) :
  A ⇒* B ->
  ⟦ B ⟧ i , I ↘ P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star i A B P (h : ⟦ A ⟧ i ↘ P) :
  A ⇒* B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star i A B P (h : ⟦ B ⟧ i ↘ P) :
  A ⇒* B ->
  ⟦ A ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

(* ---------------------------------------------------------- *)

Lemma InterpUnivN_Coherent i A B P (h : ⟦ B ⟧ i ↘ P) :
  Coherent A B ->
  ⟦ A ⟧ i ↘ P.
Proof.
  hauto l:on unfold:Coherent use:InterpUnivN_back_preservation_star, InterpUnivN_preservation_star.
Qed.

(* ---------------------------------------------------------- *)
(* inversion lemmas for InterpExt. To invert the InterpExt
   judgment, we have to be careful about the step case. *)

Lemma InterpExt_Bool_inv i I P :
  ⟦ tBool ⟧ i , I ↘ P ->
  P = fun a => exists v, a ⇒* v /\ is_bool_val v.
Proof.
  move E : tBool => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Void_inv i I P :
  ⟦ tVoid ⟧ i , I ↘ P ->
  P = (const False).
Proof.
  move E : tVoid => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Univ_inv i I P j :
  ⟦ tUniv j ⟧ i , I ↘ P ->
  exists lt, P = I j lt.
Proof.
  move E : (tUniv j) => A h.
  move : E.
  elim : A P / h; hauto lq:on rew:off inv:Par.
Qed.

Lemma InterpUnivN_Bool_inv i P :
  ⟦ tBool ⟧ i ↘ P ->
  P = fun a => exists v, a ⇒* v /\ is_bool_val v.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Bool_inv. Qed.

Lemma InterpExt_Eq_inv i I a b A P :
  ⟦ tEq a b A ⟧ i , I ↘ P ->
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
  - move => j lt PB /InterpExt_Univ_inv => [[lt']] ->.
    rewrite (lt_unique lt lt') => //.
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
   ⟦ A ⟧ i , (fun k ltki => I k (lt_trans ltki lt_max_l)) ↘ PA ->
   ⟦ A ⟧ j , (fun k ltkj => I k (lt_trans ltkj lt_max_r)) ↘ PB ->
  PA = PB.
Proof.
  move => /InterpExt_cumulative + /InterpExt_cumulative.
  apply /InterpExt_deterministic.
Qed.

Lemma InterpUnivN_deterministic' i j A PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ j ↘ PB ->
  PA = PB.
Proof.
  move => h0 h1. simp InterpUnivN in h0, h1.
  eapply InterpExt_deterministic' with (I := fun k _ A => exists PA, ⟦ A ⟧ k ↘ PA); eauto.
Qed.

(* ----- Improved inversion lemma for functions (Pi Inv Alt) ---------- *)

Lemma InterpExt_Fun_inv_nopf i I A B P  (h : InterpExt i I (tPi A B) P) :
  exists (PA : tm -> Prop),
     ⟦ A ⟧ i , I ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i , I ↘ PB) /\
      P = ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i , I ↘ PB).
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
    ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB) /\
      P = ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB).
Proof.
  qauto use:InterpExt_Fun_inv_nopf l:on rew:db:InterpUniv.
Qed.

(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos i A PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, (a ⇒ b) ->
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
    ⟦ A ⟧ i ↘ PA ->
    forall a b, a ⇒* b ->
           PA b -> PA a.
Proof.
  move => h a b.
  induction 1; sfirstorder use:InterpUnivN_back_clos.
Qed.

Lemma InterpUnivN_Univ_inv i j :
  j < i ->
  ⟦ tUniv j ⟧ i ↘ (fun A : tm => exists (PA : tm -> Prop), ⟦ A ⟧ j ↘ PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [//|].
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  ⟦ tUniv j ⟧ i ↘ P ->
  P = (fun A : tm => exists (PA : tm -> Prop), ⟦ A ⟧ j ↘ PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv.
Qed.
