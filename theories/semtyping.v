Require Import join normalform imports.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

Definition SumSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) t :=
  (exists a b, t ⇒* tPack a b /\ PA a /\ (forall PB, PF a PB -> PB b)) \/ wne t.

(* Logical Relation:

  InterpUnivN i A P  holds when
   - A is a Set i
   - P is a predicate on terms that act like type A

  We define this in two parts: one that generalizes over
  smaller interpretations and then tie the knot
  with the real definition below.

 *)

Reserved Notation "⟦ A ⟧ i , I ↘ S" (at level 70).
Inductive InterpExt i (I : nat -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_Ne A : ne A -> ⟦ A ⟧ i , I ↘ wne
| InterpExt_Nat : ⟦ tNat ⟧ i , I ↘ (fun a => exists v, a ⇒* v /\ is_nat_val v)
| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tPi A B ⟧ i , I ↘ (ProdSpace PA PF)
| InterpExt_Univ j :
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ (I j)
| InterpExt_Eq a b A :
  nf a ->
  nf b ->
  nf A ->
   ⟦ tEq a b A ⟧ i , I ↘ (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p)
| InterpExt_Sig A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tSig A B ⟧ i , I ↘ SumSpace PA PF
| InterpExt_Step A A0 PA :
  (A ⇒ A0) ->
  ⟦ A0 ⟧ i , I ↘ PA ->
  ⟦ A ⟧ i , I ↘ PA
where "⟦ A ⟧ i , I ↘ S" := (InterpExt i I A S).

Lemma InterpExt_Eq' i I PA a b A :
  nf a ->
  nf b ->
  nf A ->
  PA = (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p) ->
  ⟦ tEq a b A ⟧ i , I ↘ PA.
Proof. hauto lq:on use:InterpExt_Eq. Qed.

Lemma InterpExt_Univ' i I j PF :
  PF = I j ->
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => exists PA, InterpUnivN m A PA
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
                     match Compare_dec.lt_dec j i with
                     | left h => I j A
                     | right _ => False
                     end) ↘ PA.
Proof.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto l:on ctrs:InterpExt.
  - hauto l:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 i I A PA
 (h : ⟦ A ⟧ i , (fun j A =>
                      match Compare_dec.lt_dec j i with
                     | left h => I j A
                     | right _ => False
                     end) ↘ PA) :
  ⟦ A ⟧ i , I ↘ PA.
Proof.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m ?.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto l:on ctrs:InterpExt.
  - hauto l:on ctrs:InterpExt.
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
  - hauto q:on inv:tm.
  - hauto l:on.
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:Par_subst.
Qed.

Lemma InterpExt_Sig_inv i I A B P  
  (h :  ⟦ tSig A B ⟧ i , I ↘ P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
     ⟦ A ⟧ i , I ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) /\
    P = SumSpace PA PF.
Proof.
  move E : (tSig A B) h => T h.
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


Lemma InterpExt_cumulative i j I A PA :
  i <= j ->
   ⟦ A ⟧ i , I ↘ PA ->
   ⟦ A ⟧ j , I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.le_trans.
Qed.

Lemma InterpUnivN_cumulative i A PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

(* ------------------------------------------------------- *)

(* The logical relation is closed under parallel reduction,
   forwards and backwards. *)

Lemma InterpExt_preservation i I A B P (h : ⟦ A ⟧ i , I ↘ P) :
  (A ⇒ B) ->
  ⟦ B ⟧ i , I ↘ P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto lq:on ctrs:InterpExt db:nfne.
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
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpExt_Sig; auto.
    move => a PB hPB0.
    apply : ihPB; eauto.
    sfirstorder use:Par_cong, Par_refl.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := Par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.


Lemma InterpUnivN_preservation i A B P (h : ⟦ A ⟧ i ↘ P) :
  (A ⇒ B) ->
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

Lemma InterpExt_Ne_inv i I A P :
  ne A ->
  ⟦ A ⟧ i , I ↘ P ->
  P = wne.
Proof.
  move => + h0.
  elim : A P /h0 =>//.
  hauto l:on inv:- db:nfne.
Qed.

Lemma InterpExt_Nat_inv i I P :
  ⟦ tNat ⟧ i , I ↘ P ->
  P = fun a => exists v, a ⇒* v /\ is_nat_val v.
Proof.
  move E : tNat => A h.
  move : E.
  elim : A P / h; hauto q:on inv:tm,Par.
Qed.

Lemma InterpExt_Univ_inv i I P j :
  ⟦ tUniv j ⟧ i , I ↘ P ->
  P = I j /\ j < i.
Proof.
  move E : (tUniv j) => A h.
  move : E.
  elim : A P / h; hauto q:on rew:off inv:Par,tm.
Qed.

Lemma InterpUnivN_Nat_inv i P :
  ⟦ tNat ⟧ i ↘ P ->
  P = fun a => exists v, a ⇒* v /\ (is_nat_val v).
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Nat_inv. Qed.

Lemma InterpExt_Eq_inv i I a b A P :
  ⟦ tEq a b A ⟧ i , I ↘ P ->
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

Lemma InterpUnivN_Eq_inv i a b A P :
  ⟦ tEq a b A ⟧ i ↘ P ->
  P = (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p) /\ wn a /\ wn b /\ wn A.
Proof.
  simp InterpUniv.
  hauto l:on use:InterpExt_Eq_inv.
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
  - hauto lq:on inv:InterpExt ctrs:InterpExt use:InterpExt_Ne_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Nat_inv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Fun_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    fext => b a PB ha.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Eq_inv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Sig_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    rewrite /SumSpace.
    fext => t.
    apply propositional_extensionality.
    hauto lq:on rew:off.
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
  case : (Coq.Arith.Compare_dec.le_le_S_dec i j).
  - hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
  - move => ?. have : j <= i by lia. hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
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

Lemma InterpExt_Sig_inv_nopf i I A B P  (h : InterpExt i I (tSig A B) P) :
  exists (PA : tm -> Prop),
     ⟦ A ⟧ i , I ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i , I ↘ PB) /\
      P = SumSpace PA (fun a PB => ⟦ B[a..] ⟧ i , I ↘ PB).
Proof.
  move /InterpExt_Sig_inv : h. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
  exists PA. repeat split => //.
  - sfirstorder.
  - fext => b.
    apply propositional_extensionality.
    split.
    + rewrite /SumSpace.
      move => []; last by tauto.
      move => [a][b0][h0][+]h1.
      move/[dup] => ? /hPF.
      move => [PB]hPB.
      left.
      exists a, b0. (repeat split)=>// PB0 ?.
      suff : PB0 = PB by hauto lq:on.
      eauto using InterpExt_deterministic.
    + sfirstorder.
Qed.

(* ---- Alternative intro rule for Eq ----------- *)
Lemma InterpUnivN_Eq i a b A:
  wn a -> wn b -> wn A ->
  ⟦ tEq a b A ⟧ i ↘ (fun p => (p ⇒* tRefl /\ Coherent a b) \/ wne p).
Proof.
  move => [va [? ?]] [vb [? ?]] [vA [? ?]].
  have ? : InterpUnivN i (tEq va vb vA) (fun p => (p ⇒* tRefl /\ Coherent va vb) \/ wne p)
    by hauto lq:on ctrs:InterpExt rew:db:InterpUniv.
  have ? : (tEq a b A) ⇒* (tEq va vb vA) by auto using S_Eq.
  have : InterpUnivN i (tEq a b A) (fun p => (p ⇒* tRefl /\ Coherent va vb) \/ wne p) by eauto using InterpUnivN_back_preservation_star.
  move /[dup] /InterpUnivN_Eq_inv. move => [?]. congruence.
Qed.


(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos i A PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, (a ⇒ b) ->
           PA b -> PA a.
Proof.
  simp InterpUniv => h.
  elim : A PA /h.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF b0 b1 hb01.
    rewrite /ProdSpace => hPB a PB ha hPFa.
    have ? : (tApp b0 a ⇒ tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
    hauto lq:on ctrs:Par.
  - qauto l:on rew:db:InterpUniv ctrs:InterpExt.
  - hauto lq:on ctrs:rtc.
  - hauto q:on ctrs:rtc unfold:SumSpace.
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
  ⟦ tUniv j ⟧ i ↘  (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [|//].
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  ⟦ tUniv j ⟧ i ↘ P ->
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
Lemma adequacy i A PA
  (h :  ⟦ A ⟧ i ↘ PA) :
  CR PA.
Proof.
  elim /Wf_nat.lt_wf_ind : i A PA h.
  move => i ihn A PA h.
  simp  InterpUniv in h.
  elim : A PA / h =>//.
  - firstorder with nfne.
  - firstorder with nfne.
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
      * move => A B PA PF hPA wnA hTot hRes ih.
        apply wn_sig; first by auto.
        have ? : CR PA by hauto lq:on rew:db:InterpUniv.
        have hzero : PA (var_tm var_zero) by hauto q:on ctrs:rtc.
        move : hTot (hzero); move/[apply]. move => [PB].
        move /ih.
        match goal with [|- wn ?Q -> _] => replace Q with (ren_tm (var_zero..) B) end.
        eauto using wn_antirenaming. 
        substify. by asimpl.
      * hauto lq:on ctrs:rtc.
    + hauto lq:on ctrs:InterpExt use:InterpExt_back_preservation_star rew:db:InterpUniv unfold:wne.
  - hauto lq:on db:nfne.
  - rewrite /SumSpace => A B PA PF hA ihA hTot hRes ih.
    split => [a []| /ltac:(tauto)].
    + move => [a0][b] [h0 [h1 h2]].
      rewrite /wn.
      suff : wn (tPack a0 b) by qauto l:on use:rtc_transitive.
      have : wn b by hauto q:on.
      have : wn a0 by sfirstorder.
      apply wn_pack.
    + auto with nfne.
Qed.

Corollary InterpUniv_wn_ty i A PA
  (h : ⟦ A ⟧ i ↘ PA) :
  wn A.
Proof.
  suff : exists PA,  ⟦ tUniv i ⟧ (S i) ↘  PA /\ PA A by hauto q:on use:adequacy.
  eexists.
  split.
  qauto l:on ctrs:InterpExt rew:db:InterpUniv.
  move =>//. eauto.
Qed.

Derive Inversion sub1_inv with (forall A B, Sub1 A B).

Lemma Sub1_ne A B : Sub1 A B -> ne A = ne B /\ nf A = nf B.
Proof. elim; sfirstorder. Qed.

Lemma InterpExt_Sub1 I i j A B PA PB (_I : forall i j A, i <= j -> I i A -> I j A) (h : ⟦ A ⟧ i , I ↘ PA) (h2 : ⟦ B ⟧ j , I ↘ PB) :
  (Sub1 A B ->
  forall a, PA a -> PB a) /\ (Sub1 B A -> forall a, PB a -> PA a).
Proof.
  move : j B PB h2.
  elim : A PA / h.
  - move => A h j B PB hPB.
    split => ?; have : ne B by hauto l:on use:Sub1_ne inv:Sub1.
    hauto lq:on rew:off inv:Sub1 use:InterpExt_Ne_inv.
    hauto lq:on rew:off inv:Sub1 use:InterpExt_Ne_inv.
  - hauto lq:on inv:Sub1, InterpExt use:InterpExt_Nat_inv.
  - move => A0 B0 PA0 PF0 hPA0 ihA0 hTot hPF ihPF j ? PB hPB.
    have ? : ⟦ tPi A0 B0 ⟧ i, I ↘ (ProdSpace PA0 PF0) by hauto l:on ctrs:InterpExt.
    split.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 []? ? ?. subst.
      move /InterpExt_Fun_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA1 a -> PA0 a by hauto l:on.
      move => b hb a PB2 ha hPB2.
      have [ PB0 [hPB0 hPB1] ] : exists PB, PF0 a PB /\ ⟦ B0[a..] ⟧ i , I ↘ PB
        by qauto l:on.
      have : Sub1 B0[a..] B2[a..] by sfirstorder use:Sub1_morphing.
      (* specialize ihPF with (1 := hPB0). *)
      move /ihPF : hPB2 (hPB0). move/[apply].
      sfirstorder unfold:ProdSpace.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 ?[] ? ?. subst.
      move /InterpExt_Fun_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA0 a -> PA1 a by hauto l:on.
      move => b hb a PB0 ha hPB0.
      have ? : Sub1 B1[a..] B0[a..] by sfirstorder use:Sub1_morphing.
      move /ihPF : hPB0 {ihPF}.
      move /(_ _ ltac:(sfirstorder)) : hTot'  => [PB1 hPB1].
      move /(_ _ _ _ hPB1) => [_].
      sfirstorder.
  - move => j ? j0 B PB hPB.
    split.
    + elim /sub1_inv=>//.
      move => _ p q ? []? ? a ha. subst.
      move /InterpExt_Univ_inv  : hPB.
      move => [? ?]. subst. firstorder.
    + elim /sub1_inv=>//.
      move => _ p q ? ? [?] a ha. subst.
      move /InterpExt_Univ_inv  : hPB => [? ?]. subst.
      hauto l:on.
  - move => > h0 h1 h2 > h.
    split. inversion 1; subst. move /InterpExt_Eq_inv : h => [? ?]. subst. auto.
    inversion 1; subst. move /InterpExt_Eq_inv : h => [? ?]. subst. auto.
  - move => A0 B0 PA0 PF0 hPA0 ihA0 hTot hPF ihPF j ? PB hPB.
    have ? : ⟦ tSig A0 B0 ⟧ i, I ↘ (SumSpace PA0 PF0) by hauto l:on ctrs:InterpExt.
    split.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 []? ? ?. subst.
      move /InterpExt_Sig_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA0 a -> PA1 a by hauto l:on.
      move => t. rewrite /SumSpace.
      move => []; last by tauto.
      move => [a][b][h0][h1]h2.
      left. exists a,b. (repeat split) => //. by firstorder.
      have [ PB0 [hPB0 hPB1] ] : (exists PB, PF0 a PB /\ ⟦ B0[a..] ⟧ i , I ↘ PB)
        by qauto l:on.
      have : Sub1 B0[a..] B2[a..] by sfirstorder use:Sub1_morphing.
      move /ihPF : hPB1 (hPB0). move/[apply].
      qauto l:on.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 ? [? ?] t. subst.
      move /InterpExt_Sig_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA1 a -> PA0 a by hauto l:on.
      rewrite /SumSpace. move => []; last by tauto.
      qauto l:on use:Sub1_morphing.
  - move => A A0 PA hred hPA ih j B PB hPB.
    split.
    + move => hSub a ha.
      have : exists B0, B ⇒ B0 /\ Sub1 A0 B0 by qauto l:on use:Sub1_simulation.
      move => [B0][h0]h1.
      have /ih : ⟦ B0 ⟧ j, I ↘ PB by eauto using InterpExt_preservation.
      sfirstorder.
    + move => hSub a ha.
      have : exists B0, B ⇒ B0 /\ Sub1 B0 A0 by qauto l:on use:Sub1_simulation.
      move => [B0][h0]h1.
      have /ih : ⟦ B0 ⟧ j, I ↘ PB by eauto using InterpExt_preservation.
      sfirstorder.
Qed.

Lemma InterpUnivN_Sub1 i j A B PA PB (h : ⟦ A ⟧ i ↘ PA) (h2 : ⟦ B ⟧ j ↘ PB) :
  (Sub1 A B -> forall a, PA a -> PB a) /\ (Sub1 B A -> forall a, PB a -> PA a).
Proof.
  move : h h2.
  simp InterpUniv.
  apply InterpExt_Sub1.
  move => i0 j0 A0 h [PA0 hPA0].
  exists PA0.
  move /InterpUnivN_cumulative : hPA0.
  apply. lia.
Qed.

Lemma InterpUnivN_Sub1' i j A B PA PB (h : ⟦ A ⟧ i ↘ PA) (h2 : ⟦ B ⟧ j ↘ PB) :
  (Sub1 A B -> forall a, PA a -> PB a).
Proof.
  move /InterpUnivN_Sub1 : h h2.
  move /[apply]. move => [+ _].
  apply.
Qed.

Lemma InterpUnivN_Sub i j A B PA PB (h0 : ⟦ A ⟧ i ↘ PA) (h1 : ⟦ B ⟧ j ↘ PB) (h2 : Sub A B) :
  forall a, PA a -> PB a.
Proof.
  move : h2. rewrite /Sub.
  move => [A0][B0][h2][h3]+.
  have : ⟦ B0 ⟧ j ↘ PB by hauto lq:on use:InterpUnivN_Coherent ctrs:rtc.
  have : ⟦ A0 ⟧ i ↘ PA by hauto lq:on use:InterpUnivN_Coherent ctrs:rtc.
  apply InterpUnivN_Sub1'.
Qed.

Lemma InterpUnivN_Nat : ⟦ tNat ⟧ 0 ↘ (fun a => exists v, a ⇒* v /\ is_nat_val v).
Proof. simp InterpUniv. apply InterpExt_Nat. Qed.
