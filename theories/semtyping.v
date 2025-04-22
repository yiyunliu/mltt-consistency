Require Import join normalform imports.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a PB, PA a -> PF a PB -> PB (tApp b a).

Definition SumSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) t :=
  (exists a b, HReds.R t (tPack a b) /\ PA a /\ (forall PB, PF a PB -> PB b)) \/ wh_ne t.

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
| InterpExt_Ne A : whne A -> ⟦ A ⟧ i , I ↘ wh_ne
| InterpExt_Nat : ⟦ tNat ⟧ i , I ↘ wh_nat
| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tPi A B ⟧ i , I ↘ (ProdSpace PA PF)
| InterpExt_Univ j :
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ (I j)
| InterpExt_Eq a b A :
   ⟦ tEq a b A ⟧ i , I ↘ (fun p => (HReds.R p tRefl /\ Coherent a b) \/ wh_ne p)
| InterpExt_Sig A B PA PF :
  ⟦ A ⟧ i , I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ B[a..] ⟧ i , I ↘ PB) ->
  ⟦ tSig A B ⟧ i , I ↘ SumSpace PA PF
| InterpExt_Step A A0 PA :
  HRed.R A A0 ->
  ⟦ A0 ⟧ i , I ↘ PA ->
  ⟦ A ⟧ i , I ↘ PA
where "⟦ A ⟧ i , I ↘ S" := (InterpExt i I A S).

Derive Inversion iinv with (forall i I A S, InterpExt i I A S).

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => exists PA, InterpUnivN m A PA
                                  | right _ => False
                                  end).

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

(* ---------------------------------------------------- *)

Lemma InterpExt_Univ' i I j PF :
  PF = I j ->
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

(* The definition of InterpUnivN is more complicated than
   it needs to be. We show that that we can
   simplify the unfolding above to just mention InterpUnivN
   without doing the case analysis.
*)
Lemma InterpExt_lt_impl i I0 I1 A PA :
  (forall j, j < i -> I0 j = I1 j) ->
  ⟦ A ⟧ i , I0 ↘ PA ->
  ⟦ A ⟧ i , I1 ↘ PA.
Proof.
  move => hI h.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    by rewrite hI.
  - hauto l:on ctrs:InterpExt.
  - hauto l:on ctrs:InterpExt.
  - hauto l:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_iff i I0 I1 A PA :
  (forall j, j < i -> I0 j = I1 j) ->
  ⟦ A ⟧ i , I0 ↘ PA <->
  ⟦ A ⟧ i , I1 ↘ PA.
Proof.
  move => h.
  have h' : (forall j : nat, j < i -> I1 j = I0 j) by firstorder.
  split; eauto using InterpExt_lt_impl.
Qed.

Lemma InterpUnivN_nolt i :
  InterpUnivN i = InterpExt i (fun j A => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUnivN.
  extensionality A. extensionality P.
  apply propositional_extensionality.
  apply InterpExt_lt_iff.
  move => j hj. extensionality A0. apply propositional_extensionality.
  case : Compare_dec.lt_dec => //.
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
  - hauto lq:on inv:HRed.R.
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
    hauto lq:on inv:HRed.R.
Qed.

(* For all of the proofs about InterpUnivN below, we need to
   do them in two steps. Once for InterpExt, and then tie the
   knot for the full definition. *)

(* -----  I-PiAlt is admissible (free of PF, the relation R on paper)  ---- *)


Lemma InterpUnivN_Fun_nopf i A B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB) ->
  ⟦ tPi A B ⟧ i ↘ (ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB)).
Proof.
  hauto l:on ctrs:InterpExt rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Sig_nopf i A B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB) ->
  ⟦ tSig A B ⟧ i ↘ (SumSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB)).
Proof.
  hauto l:on ctrs:InterpExt rew:db:InterpUniv.
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

Lemma InterpExt_back_preservation_star i I A B P (h : ⟦ B ⟧ i , I ↘ P) :
  HReds.R A B ->
  ⟦ A ⟧ i , I ↘ P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

(* Lemma InterpExt_preservation_star i I A B P (h : ⟦ A ⟧ i , I ↘ P) : *)
(*   HReds.R A B -> *)
(*   ⟦ B ⟧ i , I ↘ P. *)
(* Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed. *)

(* Lemma InterpUnivN_preservation_star i A B P (h : ⟦ A ⟧ i ↘ P) : *)
(*   A ⇒* B -> *)
(*   ⟦ B ⟧ i ↘ P. *)
(* Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed. *)

Lemma InterpUnivN_back_preservation_star i A B P (h : ⟦ B ⟧ i ↘ P) :
  HReds.R A B ->
  ⟦ A ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

(* ---------------------------------------------------------- *)
(* inversion lemmas for InterpExt. To invert the InterpExt
   judgment, we have to be careful about the step case. *)

Lemma whne_stuck a b : whne a -> HRed.R a b -> False.
Proof. elim : a b => //=; hauto l:on inv:HRed.R. Qed.

Lemma InterpExt_Ne_inv i I A P :
  whne A ->
  ⟦ A ⟧ i , I ↘ P ->
  P = wh_ne.
Proof.
  move => + h0.
  elim : A P /h0 =>//.
  sfirstorder use:whne_stuck.
Qed.

Lemma InterpExt_Nat_inv i I P :
  ⟦ tNat ⟧ i , I ↘ P ->
  P = wh_nat .
Proof.
  move E : tNat => A h.
  move : E.
  elim : A P / h; hauto q:on inv:tm,HRed.R.
Qed.

Lemma InterpExt_Univ_inv i I P j :
  ⟦ tUniv j ⟧ i , I ↘ P ->
  P = I j /\ j < i.
Proof.
  move E : (tUniv j) => A h.
  move : E.
  elim : A P / h; hauto q:on rew:off inv:HRed.R, tm.
Qed.

Lemma InterpUnivN_Ne_inv i A P :
  whne A ->
  ⟦ A ⟧ i ↘ P ->
  P = wh_ne.
Proof.
  sfirstorder use:InterpExt_Ne_inv rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Nat_inv i P :
  ⟦ tNat ⟧ i ↘ P ->
  P = wh_nat.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Nat_inv. Qed.

Lemma InterpExt_Eq_inv i I a b A P :
  ⟦ tEq a b A ⟧ i , I ↘ P ->
  (P = fun A => HReds.R A tRefl /\ Coherent a b \/ wh_ne A).
Proof.
  move E : (tEq a b A) => T h.
  move : a b A E.
  elim : T P /h => //.
  hauto q:on inv:tm.
  hauto lq:on ctrs:rtc.
  hauto q:on inv:HRed.R.
Qed.

Lemma InterpUnivN_Eq_inv i a b A P :
  ⟦ tEq a b A ⟧ i ↘ P ->
  P = (fun p => (HReds.R p tRefl /\ Coherent a b) \/ wh_ne p).
Proof.
  simp InterpUniv.
  hauto l:on use:InterpExt_Eq_inv.
Qed.

Lemma HRed_deterministic A B C :
  HRed.R A B -> HRed.R A C -> B = C.
Proof. move => h. move : C. elim : A B /h ; hauto lq:on inv:HRed.R. Qed.

Lemma InterpExt_preservation i I A B PA :
  ⟦ A ⟧ i , I ↘ PA ->
  HRed.R A B ->
  ⟦ B ⟧ i , I ↘ PA.
Proof.
  move => h. move : B. elim : A PA / h.
  - sfirstorder use:whne_stuck.
  - qauto inv:HRed.R.
  - qauto inv:HRed.R.
  - qauto inv:HRed.R.
  - qauto inv:HRed.R.
  - qauto inv:HRed.R.
  - move => A A0 S hr hS ih B hB.
    have ? : A0 = B by eauto using HRed_deterministic. subst.
    done.
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
    extensionality b. extensionality a. extensionality PB. extensionality ha.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Eq_inv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Sig_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    rewrite /SumSpace.
    extensionality t.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - sfirstorder use:InterpExt_preservation.
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
  - extensionality b. extensionality a. extensionality PB. extensionality ha.
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
  - extensionality b.
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

Lemma InterpUnivN_Sig_inv_nopf i A B P  (h : InterpUnivN i (tSig A B) P) :
  exists (PA : tm -> Prop),
    ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB) /\
      P = SumSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB).
Proof.
  qauto use:InterpExt_Sig_inv_nopf l:on rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Univ_inv i j P :
  ⟦ tUniv j ⟧ i ↘ P ->
  P = (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv.
Qed.

Lemma InterpUniv_ind (P : nat -> tm -> (tm -> Prop) -> Prop) :
  (* Ne *)
  (forall i A, whne A -> P i A wh_ne) ->
  (* Nat *)
  (forall i, P i tNat wh_nat) ->
  (* Pi *)
  (forall i A B PA,
      ⟦ A ⟧ i ↘ PA ->
      P i A PA ->
      (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB /\ P i (B[a..]) PB) ->
      (forall a, PA a -> forall PB, ⟦ B[a..] ⟧ i ↘ PB -> P i (B[a..]) PB) ->
      P i (tPi A B) (ProdSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB))) ->
  (* Univ *)
  (forall i j : fin, j < i -> (forall k A PA, k < i -> ⟦ A ⟧ k ↘ PA -> P k A PA) ->
              P i (tUniv j) (fun A => exists PA, ⟦ A ⟧ j ↘ PA)) ->
  (* Eq *)
  (forall i a b A,
      P i (tEq a b A) (fun p : tm => HReds.R p tRefl /\ a ⇔ b \/ wh_ne p)) ->
  (* Sig *)
  (forall i A B PA,
      ⟦ A ⟧ i ↘ PA ->
      P i A PA ->
      (forall a, PA a -> exists PB, ⟦ B[a..] ⟧ i ↘ PB /\ P i (B[a..]) PB) ->
      (forall a, PA a -> forall PB, ⟦ B[a..] ⟧ i ↘ PB -> P i (B[a..]) PB) ->
      P i (tSig A B) (SumSpace PA (fun a PB => ⟦ B[a..] ⟧ i ↘ PB))) ->
  (* Red *)
  (forall i A A0 PA,
      HRed.R A A0 -> ⟦ A0 ⟧ i ↘ PA -> P i A0 PA -> P i A PA) ->
  forall i A S, ⟦ A ⟧ i ↘ S -> P i A S.
Proof.
  move => hNe hNat hFun hUniv hEq hSig hStep.
  elim /Wf_nat.lt_wf_ind => i ihOM A S h.
  simp InterpUniv in h.
  elim : A S / h; eauto.
  - repeat rewrite <- InterpUnivN_nolt in *.
    move => A B PA PF hPA ihPA hTot hPF ihPF.
    have <- : (ProdSpace PA (fun (a : tm) (PB : tm -> Prop) => ⟦ B[a..] ⟧ i ↘ PB)) = ProdSpace PA PF.
    rewrite /ProdSpace.
    extensionality b. extensionality a. extensionality PB. extensionality ha.
    apply propositional_extensionality.
    split.
    hauto l:on.
    move => h hPB.
    move /hTot : ha => [PB0 /[dup] ? /hPF].
    have ? : PB0 = PB by eauto using InterpUnivN_deterministic. subst.
    tauto.

    apply hFun; auto.
    hauto lq:on.
    move => a /[dup] ha /hTot. move => [PB hPB].
    move /hPF : (hPB). move => ? PB0 *.
    suff : PB = PB0 by hauto lq:on.
    eauto using InterpUnivN_deterministic.
  - move => A B PA PF hPA ihPA hTot hPF ihPF.
    rewrite -InterpUnivN_nolt in hPF ihPF hPA.
    have <- : (SumSpace PA (fun (a : tm) (PB : tm -> Prop) => ⟦ B[a..] ⟧ i ↘ PB)) = SumSpace PA PF.

    rewrite /SumSpace. extensionality t.
    apply propositional_extensionality.
    split.
    case; last by tauto.
    hauto lq:on.
    case; last by tauto.
    move => [a][b][h0][h1]h2. left.
    exists a,b.
    (repeat split) =>// PB hPB.
    move /hTot : (h1) => [PB0 /[dup] ? /hPF ?].
    have -> : PB = PB0 by eauto using InterpUnivN_deterministic.
    by firstorder.

    apply hSig; eauto.
    hauto lq:on.
    move => a ha PB ?.
    move /hTot  : (ha) => [PB0 /[dup] /hPF] *.
    have -> : PB = PB0 by eauto using InterpUnivN_deterministic.
    hauto l:on.
  - rewrite -!InterpUnivN_nolt.
    sfirstorder.
Qed.

(* ---- Alternative intro rule for Eq ----------- *)
Lemma InterpUnivN_Eq i a b A:
  ⟦ tEq a b A ⟧ i ↘ (fun p => (HReds.R p tRefl /\ Coherent a b) \/ wh_ne p).
Proof.
  sfirstorder rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Univ i j :
  j < i ->
  ⟦ tUniv j ⟧ i ↘  (fun A : tm => exists (PA : tm -> Prop), InterpUnivN j A PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [|//].
  by simp InterpUniv.
Qed.

Lemma InterpUnivN_WNe i A  : whne A -> ⟦ A ⟧  i  ↘ wh_ne.
Proof.
  sauto lq:on rew:db:InterpUniv.
Qed.

(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpUnivN_back_clos i A PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, (a ⇒ b) ->
           PA b -> PA a.
Proof.
  move : i A PA.
  apply : InterpUniv_ind.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - have ? : forall b0 b1 a, b0 ⇒ b1 -> tApp b0 a ⇒ tApp b1 a
        by hauto lq:on ctrs:Par use:Par_refl.
    hauto lq:on unfold:ProdSpace.
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

(* ------------------------ adequacy ------------------------------- *)

(* P identifies a set of "reducibility candidates" *)
Definition CR (P : tm -> Prop) :=
  (forall a, P a -> wn a) /\
    (forall a, wne a -> P a).

(* Every interpretation of types is a reducibility candidate *)
Lemma adequacy i A PA
  (h :  ⟦ A ⟧ i ↘ PA) :
  CR PA /\ wn A.
Proof.
  move : i A PA h.
  apply InterpUniv_ind.
  - firstorder with nfne.
  - hauto lq:on db:nfne.
  - move => i A B PA hPA ihPA hPB ihPB.
    have hzero : PA (var_tm var_zero) by hauto lq:on ctrs:rtc.
    repeat split.
    + rewrite /ProdSpace => b hb.
      move /hPB : (hzero) => [PB][ih0]ih1.
      apply ext_wn with (i := var_zero). hauto lq:on.
    + rewrite /ProdSpace => b hb a PB ha.
      suff : wn a by hauto q:on use:wne_app. hauto q:on.
    + apply wn_pi.
      sfirstorder.
      move /hPB : (hzero).
      move => [_][_][_]h.
      apply wn_antirenaming with (ξ := (0..)).
      move : h. substify. by asimpl.
  - move => m i hlt ih.
    repeat split.
    + sfirstorder.
    + hauto lq:on use:InterpUnivN_WNe.
    + hauto lq:on ctrs:rtc.
  - hauto lq:on use:wn_eq ctrs:rtc db:nfne.
  - move => i A B PA hPA [[ihA0 ihA1] ihA2] ihPB ihPB'.
    rewrite /SumSpace.
    repeat split.
    + move => t []; last by apply wne_wn.
      move => [a][b][h0 [h1 h2]].
      rewrite /wn.
      suff : wn (tPack a b) by qauto l:on use:rtc_transitive.
      have : wn b by hauto q:on.
      have : wn a by sfirstorder.
      apply wn_pack.
    + tauto.
    + apply wn_sig; first by auto.
      have /ihPB : PA (var_tm 0) by hauto q:on ctrs:rtc.
      set q := (X in wn X).
      move => ?. have : wn q by sfirstorder.
      have -> : q = B⟨0..⟩.
      subst q. substify; by asimpl.
      apply wn_antirenaming.
  - hauto lq:on ctrs:rtc unfold:CR.
Qed.

Corollary InterpUniv_wn_ty i A PA
  (h : ⟦ A ⟧ i ↘ PA) :
  wn A.
Proof. firstorder using adequacy. Qed.

Derive Inversion sub1_inv with (forall A B, Sub1 A B).

Lemma Sub1_ne A B : Sub1 A B -> ne A = ne B /\ nf A = nf B.
Proof. elim; sfirstorder. Qed.

Lemma InterpUnivN_Sub1 : forall i  A PA,
   ⟦ A ⟧ i  ↘ PA ->  forall j B PB, ⟦ B ⟧ j  ↘ PB ->
  (Sub1 A B ->
  forall a, PA a -> PB a) /\ (Sub1 B A -> forall a, PB a -> PA a).
Proof.
  apply : InterpUniv_ind.
  - move => _ A h j B PB hPB.
    split => ?;
      (have : ne B by hauto l:on use:Sub1_ne inv:Sub1);
      hauto lq:on rew:off inv:Sub1 use:InterpUnivN_Ne_inv.
  - move => _ j B PB hB.
    split;inversion 1; subst; move/InterpUnivN_Nat_inv in hB;
      sfirstorder.
  - move => i A0 B0 PA0 hPA0 ihA0 hTot ihPF j B PB hPB.
    have ? : ⟦ tPi A0 B0 ⟧ i ↘ (ProdSpace PA0 (fun (a0 : tm) (PB0 : tm -> Prop) => ⟦ B0[a0..] ⟧ i ↘ PB0)) by hauto l:on use:InterpUnivN_Fun_nopf.
    split.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 []? ? ?. subst.
      move /InterpUnivN_Fun_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA1 a -> PA0 a by hauto l:on.
      move => b hb a PB2 ha hPB2.
      have [ PB0 hPB0 ] : exists PB, ⟦ B0[a..] ⟧ i  ↘ PB
        by qauto l:on.
      have : Sub1 B0[a..] B2[a..] by sfirstorder use:Sub1_morphing.
      rewrite /ProdSpace in hb.
      move /ihPF : hPB2 (hPB0). move/[apply].
      hauto lq:on unfold:ProdSpace.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 ?[] ? ?. subst.
      move /InterpUnivN_Fun_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA0 a -> PA1 a by hauto l:on.
      move => b hb a PB0 ha hPB0.
      have ? : Sub1 B1[a..] B0[a..] by sfirstorder use:Sub1_morphing.
      move /ihPF : hPB0 {ihPF}.
      move /(_ _ ltac:(sfirstorder)) : hTot'  => [PB1 hPB1].
      move => h. eapply h; eauto.
      sfirstorder.
  - move => j j0 ? ? j1 B PB hPB.
    split.
    + elim /sub1_inv=>//.
      move => _ p q ? []? ? a ha. subst.
      move /InterpUnivN_Univ_inv  : hPB.
      hauto l:on use:InterpUnivN_cumulative.
    + elim /sub1_inv=>//.
      move => _ p q ? ? [?] a ha. subst.
      move /InterpUnivN_Univ_inv  : hPB.
      move => [? ?]. subst.
      hauto l:on use:InterpUnivN_cumulative.
  - move => i  > h0 h1 h2 > h.
    split; inversion 1; subst;
      move /InterpUnivN_Eq_inv : h => [? ?]; subst; auto.
  - move => i A0 B0 PA0 hPA0 ihPA0 hPF ihPF j B PB hPB.
    have ? : ⟦ tSig A0 B0 ⟧ i ↘ (SumSpace PA0 (fun (a0 : tm) (PB0 : tm -> Prop) => ⟦ B0[a0..] ⟧ i ↘ PB0)) by hauto l:on use:InterpUnivN_Sig_nopf.
    split.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 []? ? ?. subst.
      move /InterpUnivN_Sig_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA0 a -> PA1 a by hauto l:on.
      move => t. rewrite /SumSpace.
      move => []; last by tauto.
      move => [a][b][h0][h1]h2.
      left. exists a,b. (repeat split) => //. by firstorder.
      move => PB hPB.
      have [ PB0 hPB0 ] : (exists PB, ⟦ B0[a..] ⟧ i  ↘ PB)
        by qauto l:on.
      have : Sub1 B0[a..] B2[a..] by sfirstorder use:Sub1_morphing.
      qauto l:on.
    + elim /sub1_inv=>//.
      move => _ A1 B1 A2 B2 hs1 hs2 ? [? ?] t. subst.
      move /InterpUnivN_Sig_inv_nopf : hPB => [PA1][hPA1][hTot']?. subst.
      have {}ihA0 : forall a, PA1 a -> PA0 a by hauto l:on.
      rewrite /SumSpace. move => []; last by tauto.
      qauto l:on use:Sub1_morphing.
  - move => i A A0 PA hred hPA ih j B PB hPB.
    split.
    + move => hSub a ha.
      have : exists B0, B ⇒ B0 /\ Sub1 A0 B0 by qauto l:on use:Sub1_simulation.
      move => [B0][h0]h1.
      have /ih : ⟦ B0 ⟧ j ↘ PB by eauto using InterpUnivN_preservation.
      sfirstorder.
    + move => hSub a ha.
      have : exists B0, B ⇒ B0 /\ Sub1 B0 A0 by qauto l:on use:Sub1_simulation.
      move => [B0][h0]h1.
      have /ih : ⟦ B0 ⟧ j ↘ PB by eauto using InterpUnivN_preservation.
      sfirstorder.
Qed.

Lemma InterpUnivN_Sub1' i j A B PA PB (h : ⟦ A ⟧ i ↘ PA) (h2 : ⟦ B ⟧ j ↘ PB) :
  (Sub1 A B -> forall a, PA a -> PB a).
Proof. hauto l:on use:InterpUnivN_Sub1. Qed.

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
