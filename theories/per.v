Require Import typing typing_prop imports.

(* Identifying neutral (ne) and normal (nf) terms *)
Fixpoint ne (a : tm) : bool :=
  match a with
  | var_tm _ => true
  | tApp a b => ne a
  | tAbs _ _ => false
  | tPi A B => false
  | tUniv _ => false
  end.

Lemma ne_renaming a ξ : ne a <-> ne a⟨ξ⟩.
Proof. elim : a ξ => //=. Qed.

(* Definition whnf (a : tm) : bool := *)
(*   match a with *)
(*   | var_tm _ => true *)
(*   | tApp a b => ne a && nf b *)
(*   | tAbs A a => nf A && nf a *)
(*   | tPi A B => nf A && nf B *)
(*   | tUniv _ => true *)
(*   end. *)

Definition tm_rel := tm -> tm -> Prop.

Definition ProdSpace Γ (FA : context -> tm_rel) (FB : context -> tm -> tm_rel) (b0 b1 : tm) :=
  forall ξ Δ, ren_ok ξ Γ Δ ->  ⊢ Δ ->
  forall a0 a1, FA Δ a0 a1 -> FB Δ a0 = FB Δ a1 -> FB Δ a0 (tApp b0⟨ξ⟩ a0) (tApp b1⟨ξ⟩ a1).

Definition wne_coherent Γ A a b :=
  Γ ⊢ a ≡ b ∈ A.

Reserved Notation "⟦ Γ ⊨ A ⟧ i ; I ↘ R" (at level 70, no associativity).
Inductive InterpExt (Γ : context) (i : nat) (I : context -> nat -> tm_rel) : tm -> tm_rel -> Prop :=
| InterpExt_Ne A : 
  Γ ⊢ A ∈ tUniv i ->
  ne A -> ⟦ Γ ⊨ A ⟧ i ; I ↘ wne_coherent Γ A
| InterpExt_Fun A B FA FB :
  (forall ξ Δ, ren_ok ξ Γ Δ -> ⊢ Δ ->
      ⟦ Δ ⊨ ren_tm ξ A ⟧ i ; I ↘ FA Δ) ->
  (forall ξ Δ, ren_ok ξ Γ Δ -> ⊢ Δ ->
          forall a0 a1, FA Δ a0 a1 -> ⟦ Δ ⊨ (ren_tm (upRen_tm_tm ξ) B)[a0..] ⟧ i ; I ↘ FB Δ a0) ->
  ⟦ Γ ⊨ tPi A B ⟧ i ; I ↘ ProdSpace Γ FA FB
| InterpExt_Univ j :
  j < i ->
  ⟦ Γ ⊨ tUniv j ⟧ i ; I ↘ (I Γ j)
| InterpExt_Step A0 A1 RA :
  Γ ⊢ A0 ⤳ A1 ∈ tUniv i ->
  ⟦ Γ ⊨ A1 ⟧ i ; I ↘ RA ->
  ⟦ Γ ⊨ A0 ⟧ i ; I ↘ RA
where "⟦ Γ ⊨ A ⟧ i ; I ↘ R" := (InterpExt Γ i I A R).
Reserved Notation "Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i ; I" (at level 70, i at next level).

Inductive PerType (Γ : context) (i : nat) I : tm_rel :=
| PerType_Ne A B :
  ne A ->
  ne B ->
  Γ ⊢ A ≡ B ∈ tUniv i ->
  Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i ; I
| PerType_Fun A0 A1 B0 B1 RA :
  (forall ξ Δ, ren_ok ξ Γ Δ -> ⊢ Δ -> Δ ⊨ ⟦ A0⟨ξ⟩ ⟧ ~ ⟦ A1⟨ξ⟩ ⟧ i ; I ) ->
  (forall ξ Δ, ren_ok ξ Γ Δ -> ⊢ Δ -> 
          ⟦ Δ ⊨ A0⟨ξ⟩ ⟧ i ; I ↘ RA -> 
          ⟦ Δ ⊨ A1⟨ξ⟩ ⟧ i ; I ↘ RA -> 
     forall a0 a1, RA a0 a1 -> Δ ⊨ ⟦ (ren_tm (upRen_tm_tm ξ) B0)[a0..] ⟧ ~ ⟦ (ren_tm (upRen_tm_tm ξ) B1)[a1..] ⟧ i ; I) ->
  Γ ⊨ ⟦ tPi A0 B0 ⟧ ~ ⟦ tPi A1 B1 ⟧ i ; I
| PerType_Univ j :
  ⊢ Γ ->
  j < i ->
  Γ ⊨ ⟦ tUniv j ⟧ ~ ⟦ tUniv j ⟧ i ; I
| PerType_Step A0 A1 B0 B1 :
  Γ ⊢ A0 ⤳* A1 ∈ tUniv i -> 
  Γ ⊢ B0 ⤳* B1 ∈ tUniv i -> 
  Γ ⊨ ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i ; I ->
  Γ ⊨ ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i ; I
where "Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i ; I" := (PerType Γ i I A B).

Equations PerTypeN (Γ : context) (n : nat) : tm_rel by wf n lt :=
  PerTypeN Γ n := PerType Γ n
    (fun Γ m A0 A1 =>
      match Compare_dec.lt_dec m n with
      | left h => PerTypeN Γ m A0 A1
      | right _ => False
      end).

Definition InterpUnivN Γ (n : nat) : tm -> tm_rel -> Prop :=
  InterpExt Γ n PerTypeN.

Notation "Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i" := (PerTypeN Γ i A B) (at level 70).
Notation "⟦ Γ ⊨ A ⟧ i ↘ S" := (InterpUnivN Γ i A S) (at level 70).

(* InterpUnivN and PerTypeN are symmetric *)

Lemma InterpExt_sym Γ i I A R
  (h : ⟦ Γ ⊨ A ⟧ i ; I ↘ R)
  (ih : forall Γ j A B, j < i -> I Γ j A B -> I Γ j B A) :
  forall a b, R a b -> R b a.
Proof.
  move : ih.
  elim :  Γ i I A R /h.
  - hauto lq:on ctrs:Equiv.
  - qauto l:on unfold:ProdSpace.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma PerType_sym Γ i I A B
  (ih : forall Γ j A B, j < i -> I Γ j A B -> I Γ j B A)
  (h : Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i ; I) : Γ ⊨ ⟦ B ⟧ ~ ⟦ A ⟧ i ; I.
Proof.
  move : ih.
  elim : Γ i I A B /h.
  - hauto lq:on ctrs:Equiv, PerType.
  - hauto l:on ctrs:PerType use:InterpExt_sym.
  - hauto lq:on ctrs:PerType.
  - hauto q:on ctrs:PerType.
Qed.

Lemma PerTypeN_sym Γ i : forall A B, PerTypeN Γ i A B -> PerTypeN Γ i B A.
Proof.
  move : Γ.
  have h : Acc (fun x y => x < y) i by sfirstorder use:wellfounded.
  elim : i /h.
  move => j h ih Γ A B hAB.
  simp PerTypeN in hAB |- *.
  apply PerType_sym; auto.
  hauto lq:on use:Compare_dec.lt_dec.
Qed.
  
Lemma InterpUnivN_sym Γ i A R (h : ⟦ Γ ⊨ A ⟧ i ↘ R) :
  forall a b, R a b -> R b a.
Proof.
  hauto lq:on use:InterpExt_sym, PerTypeN_sym.
Qed.

Lemma Wt_Equiv Γ a A : Γ ⊢ a ∈ A -> Γ ⊢ a ≡ a ∈ A.
Proof. induction 1; qauto depth:1 ctrs:Equiv. Qed.

Lemma Red_inj_Equiv Γ a b A : Γ ⊢ a ⤳ b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Proof. induction 1; qauto depth:1 use:Wt_Equiv ctrs:Equiv. Qed.

Lemma Reds_inj_Equiv Γ a b A : Γ ⊢ a ⤳* b ∈ A -> Γ ⊢ a ≡ b ∈ A.
Proof.
  induction 1; hauto lq:on ctrs:Equiv use:Wt_Equiv, Red_inj_Equiv.
Qed.

Definition wne Γ a A := exists v, ne a /\ Γ ⊢ a ⤳* v ∈ A.

Definition wnEquiv Γ a b A := exists v0 v1, ne v0 /\ ne v1 /\ Γ ⊢ v0 ≡ v1 ∈ A /\ Γ ⊢ a ⤳* v0 ∈ A /\ Γ ⊢ b ⤳* v1 ∈ A.

Lemma neutral_pertype Γ i A B (h : wnEquiv Γ A B (tUniv i)) :
  forall I, Γ ⊨ ⟦ A ⟧ ~ ⟦ B ⟧ i ; I.
Proof.
  rewrite /wnEquiv in h.
  move : h => [v0][v1][hv0][hv1][hv][hA]hB.
  move => I.
  apply : PerType_Step; eauto.
  by apply PerType_Ne.
Qed.

Lemma neutral_interpext Γ i I A R
  (h :  ⟦ Γ ⊨  A ⟧ i ; I ↘ R) 
  (hI : forall Γ j, j < i -> forall A B, wnEquiv Γ A B (tUniv j) -> I Γ j A B) :
  forall b0 b1, wnEquiv Γ b0 b1 A -> R b0 b1.
Proof.
  move : hI.
  elim : Γ i I A R / h.
  - hauto q:on ctrs:Equiv use:Reds_inj_Equiv unfold:wne_coherent, wnEquiv.
  - move => Γ i I A B FA FB hFA ihFA hFB ihFB hI b0 b1 hb.
    rewrite /ProdSpace => ξ Δ hξ hΔ a0 a1 ha he.
    apply : ihFB; eauto.
    rewrite /wnEquiv in hb *.
    move : hb => [v0][v1][hv0][hv1][hv][hbv0]hbv1.
    exists (tApp (ren_tm ξ v0) a0), (tApp (ren_tm ξ v1) a1) => /=.
    repeat split.
    (* morphing *)
    (* renaming for ne *)
    hauto l:on use:ne_renaming.
    hauto l:on use:ne_renaming.
    (* renaming for equiv? *)
    apply : E_App.
    move : renaming_equiv hv hξ. repeat move/[apply] => //=.
    apply=>//. 
    (* Lemma needs to be mutually defined with escape *)
    admit.
    (* renaming for app? *)
    admit.
    admit.
  - hauto lq:on.
  - move => Γ i I A0 A1 RA hA01 hA1 ihA1 hI.
    move /(_ hI) in ihA1.
    (* Use some sort of Conv rule? *)
Admitted.

Lemma neutral_interpuniv Γ i A R (h :  ⟦ Γ ⊨  A ⟧ i ↘ R) :
  forall b0 b1, wnEquiv Γ b0 b1 A -> R b0 b1.
Proof.
  move : h. rewrite /InterpUnivN.
  move /neutral_interpext. apply.
  move => *. simp PerTypeN.
  hauto lq:on use:neutral_pertype.
Qed.
  

Lemma ren_ok_id Γ : ren_ok id Γ Γ.
Proof. hauto lq:on unfold:ren_ok simp+:asimpl. Qed.

Lemma ren_ok_S Γ A : ren_ok S Γ (A::Γ).
Proof.
  rewrite /ren_ok => *.
  by constructor.
Qed.

Lemma InterpExt_ty_escape Γ i I A R (h : ⟦ Γ ⊨ A ⟧ i ; I ↘ R) :
  (forall Γ j, j < i -> forall A B, wnEquiv Γ A B (tUniv j) -> I Γ j A B) ->
  ⊢ Γ -> Γ ⊢ A ∈ tUniv i.
Proof.
  elim : Γ i I A R / h => //.
  - move => Γ i I A B FA FB hFA ihFA hFB ihFB hI hΓ [:hA].
    apply T_Pi.
    + abstract : hA.
      have -> : A = A⟨id⟩ by asimpl.
      apply ihFA; eauto.
      apply ren_ok_id.
    + have hΓ' : ⊢ A :: Γ by hauto q:on ctrs:Wff.
      move /(_ S (A::Γ) ltac:(apply ren_ok_S) hΓ' (var_tm 0) (var_tm 0)) : ihFB.
      asimpl. apply=>//.
      apply : neutral_interpext; eauto.
      apply hFA => //.
      apply ren_ok_S.
      rewrite /wnEquiv.
      exists (var_tm 0), (var_tm 0). repeat split => //=.
      apply E_Var=>//. by constructor.
      apply R_Refl. apply T_Var=>//. by constructor.
      apply R_Refl. apply T_Var=>//. by constructor.
  - hauto lq:on ctrs:Wt.
  - sfirstorder use:Red_WtL.
Qed.

(* Constructors *)

Lemma InterpExt_Univ' i I j R :
  R = I j ->
  j < i ->
  ⟦ tUniv j ⟧ i , I ↘ R.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Lemma InterpExt_Steps A0 A1 i I R (rA : A0 ⇒* A1) :
  ⟦ A1 ⟧ i , I ↘ R -> ⟦ A0 ⟧ i , I ↘ R.
Proof.
  elim : A0 A1 /rA; auto.
  sfirstorder use:InterpExt_Step.
Qed.

Lemma PerType_Steps A0 A1 B0 B1 i I (rA : A0 ⇒* A1) (rB : B0 ⇒* B1) :
  ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i , I -> ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i , I.
Proof.
  elim : A0 A1 /rA; elim : B0 B1 /rB; auto;
  sfirstorder use:PerType_Step, Par_refl.
Qed.

(* Inversion lemmas *)

Lemma InterpExt_Fun_inv i I A B R
  (h :  ⟦ tPi A B ⟧ i , I ↘ R) :
  exists (RA : tm_rel) (RF : tm -> tm_rel -> Prop),
    ⟦ A ⟧ i , I ↘ RA /\
    (forall a0 a1, RA a0 a1 -> exists RB, RF a0 RB /\ RF a1 RB) /\
    (forall a RB, RF a RB -> ⟦ B[a..] ⟧ i , I ↘ RB) /\
    R = ProdSpace RA RF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T R / h => //.
  - hauto lq:on.
  - move => *; subst.
    hauto lq:on rew:off inv:Par ctrs:InterpExt use:Par_subst.
Qed.

Lemma InterpExt_Univ_inv i I R j :
  ⟦ tUniv j ⟧ i , I ↘ R ->
  R = I j /\ j < i.
Proof.
  move E : (tUniv j) => A h.
  move : E.
  elim : A R / h; hauto q:on rew:off inv:Par,tm.
Qed.

(* Level comparisons are irrelevant *)

Lemma InterpExt_lt_redundant i I A RA
  (h : ⟦ A ⟧ i , I ↘ RA) :
  ⟦ A ⟧ i , (fun j A0 A1 =>
             match Compare_dec.lt_dec j i with
             | left h => I j A0 A1
             | right _ => False
             end) ↘ RA.
Proof.
  elim : A RA /h.
  - hauto lq:on ctrs:InterpExt.
  - move => j ji.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 i I A RA
  (h : ⟦ A ⟧ i , (fun j A0 A1 =>
                  match Compare_dec.lt_dec j i with
                  | left h => I j A0 A1
                  | right _ => False
                  end) ↘ RA) :
  ⟦ A ⟧ i , I ↘ RA.
Proof.
  elim : A RA /h.
  - hauto l:on ctrs:InterpExt.
  - move => *.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_Univ_inv i j R (h : ⟦ tUniv j ⟧ i ↘ R) :
  R = (fun A0 A1 : tm => ⟦ A0 ⟧ ~ ⟦ A1 ⟧ j) /\ j < i.
Proof.
  hauto l:on use:InterpExt_Univ_inv, InterpExt_lt_redundant.
Qed.

Lemma PerType_lt_redundant i I A0 A1
  (h : ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i , I) :
  ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i ,
    (fun j A0 A1 =>
      match Compare_dec.lt_dec j i with
      | left h => I j A0 A1
      | right _ => False
      end).
Proof.
  elim : A0 A1 /h;
  hauto lq:on ctrs:PerType use:InterpExt_lt_redundant.
Qed.

Lemma PerType_lt_redundant2 i I A0 A1
  (h : ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i ,
    (fun j A0 A1 =>
      match Compare_dec.lt_dec j i with
      | left h => I j A0 A1
      | right _ => False
      end)) :
  ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i , I.
Proof.
  elim : A0 A1 /h;
  hauto lq:on ctrs:PerType use:InterpExt_lt_redundant2.
Qed.

Lemma PerTypeN_nolt n :
  PerTypeN n = PerType n PerTypeN.
Proof.
  simp PerTypeN.
  fext => A0 A1.
  apply propositional_extensionality.
  sfirstorder use:PerType_lt_redundant, PerType_lt_redundant2.
Qed.

(* PerTypeN constructors *)

Lemma PerTypeN_Fun i A0 A1 B0 B1 R :
  ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i ->
  ⟦ A0 ⟧ i ↘ R ->
  ⟦ A1 ⟧ i ↘ R ->
  (forall a0 a1, R a0 a1 -> ⟦ B0[a0..] ⟧ ~ ⟦ B1[a1..] ⟧ i) ->
  ⟦ tPi A0 B0 ⟧ ~ ⟦ tPi A1 B1 ⟧ i.
Proof. hauto lq:on ctrs:PerType use:PerTypeN_nolt. Qed.

Lemma PerTypeN_Univ i j : j < i -> ⟦ tUniv j ⟧ ~ ⟦ tUniv j ⟧ i.
Proof. hauto lq:on ctrs:PerType use:PerTypeN_nolt. Qed.

Lemma PerTypeN_Step A0 A1 B0 B1 i (rA : A0 ⇒ A1) (rB : B0 ⇒ B1) :
  ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i -> ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i.
Proof. hauto lq:on use:PerTypeN_nolt, PerType_Step. Qed.

(* Forward preservation *)

Lemma InterpExt_preservation i I A B R (r : A ⇒ B) :
  ⟦ A ⟧ i , I ↘ R ->
  ⟦ B ⟧ i , I ↘ R.
Proof.
  move => h. move : B r.
  elim : A R /h.
  - hauto l:on ctrs:InterpExt inv:Par use:Par_subst.
  - hauto lq:on ctrs:InterpExt inv:Par.
  - move => A0 A1 RA rA01 hA1 ih A2 rA02.
    have [B3 [rA13 rA23]] := Par_confluent _ _ _ rA01 rA02.
    eapply InterpExt_Step; eauto.
Qed.

Lemma PerType_preservation i I A0 A1 B0 B1 (rA : A0 ⇒ A1) (rB : B0 ⇒ B1) :
  ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i , I -> ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i , I.
Proof.
  move => h. move : A1 B1 rA rB.
  elim : A0 B0 /h.
  - move => A0 A1 B0 B1 RA hA ihA hRA1 hRA2 hB ihB C1 C2 rC1 rC2.
    elim /Par_inv : rC1 => //.
    elim /Par_inv : rC2 => //.
    hauto lq:on ctrs:PerType use:Par_subst, InterpExt_preservation.
  - hauto lq:on ctrs:PerType inv:Par.
  - move => A0 A1 B0 B1 rA01 rB01 h ih A2 B2 rA02 rB02.
    have [A3 [rA13 rA23]] := Par_confluent _ _ _ rA01 rA02.
    have [B3 [rB13 rB23]] := Par_confluent _ _ _ rB01 rB02.
    eapply PerType_Step; eauto.
Qed.

Lemma InterpExt_preservations i I A B R (r : A ⇒* B) :
  ⟦ A ⟧ i , I ↘ R ->
  ⟦ B ⟧ i , I ↘ R.
Proof. elim : A B /r; sfirstorder use:InterpExt_preservation. Qed.

Lemma PerType_preservations i I A0 A1 B0 B1 (rA : A0 ⇒* A1) (rB : B0 ⇒* B1) :
  ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i , I -> ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i , I.
Proof.
  elim : A0 A1 /rA; elim : B0 B1 /rB;
  hauto lq:on use:PerType_preservation, Par_refl.
Qed.

(* Backward preservation *)

Lemma InterpExt_noitavreserp i I A R
  (h : ⟦ A ⟧ i , I ↘ R)
  (hI : forall j, j < i ->
        forall a0 a1 b0 b1,
        a0 ⇒ a1 -> b0 ⇒ b1 ->
        I j a1 b1 -> I j a0 b0) :
  forall a0 a1 b0 b1, a0 ⇒ a1 -> b0 ⇒ b1 -> R a1 b1 -> R a0 b0.
Proof.
  elim : A R /h; auto.
  qauto l:on use:P_App, Par_refl unfold:ProdSpace.
Qed.

(* (* I guess this one wasn't needed *)
Lemma InterpExt_snoitavreserp i I A R
  (h : ⟦ A ⟧ i , I ↘ R)
  (hI : forall j, j < i ->
        forall a0 a1 b0 b1,
        a0 ⇒* a1 -> b0 ⇒* b1 ->
        I j a1 b1 -> I j a0 b0) :
  forall a0 a1 b0 b1, a0 ⇒* a1 -> b0 ⇒* b1 -> R a1 b1 -> R a0 b0.
Proof.
  move => a0 a1 b0 b1 ra rb.
  elim : a0 a1 /ra; elim : b0 b1 /rb; auto.
  - move => *.
    eapply InterpExt_noitavreserp;
    hauto lq:on use:Par_refl, rtc_once.
  - move => *. eapply InterpExt_noitavreserp; eauto using Par_refl.
    move => *. eapply hI; eauto; sfirstorder use:rtc_once.
  - move => a *.
    eapply InterpExt_noitavreserp with (b0 := a) (b1 := a);
    eauto using Par_refl.
    move => *. eapply hI; eauto; sfirstorder use:rtc_once.
Qed.
*)

Lemma InterpUnivN_noitavreserp i A R (h : ⟦ A ⟧ i ↘ R) :
  forall a0 a1 b0 b1, a0 ⇒ a1 -> b0 ⇒ b1 -> R a1 b1 -> R a0 b0.
Proof. hauto lq:on use:InterpExt_noitavreserp, PerTypeN_Step. Qed.

(* Coherence preservation *)

Lemma InterpExt_coherent i I A B R (r : A ⇔ B) :
  ⟦ A ⟧ i , I ↘ R ->
  ⟦ B ⟧ i , I ↘ R.
Proof.
  move => h. case : r => [C [rA rB]].
  eapply InterpExt_Steps; eauto. clear rB.
  eapply InterpExt_preservations; eauto.
Qed.

Lemma PerType_coherent i I A0 A1 B0 B1 (rA : A0 ⇔ A1) (rB : B0 ⇔ B1) :
  ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i , I -> ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i , I.
Proof.
  move => h.
  case : rA => [A [rA0 rA1]].
  case : rB => [B [rB0 rB1]].
  eapply PerType_Steps; eauto. clear rA1 rB1.
  eapply PerType_preservations; eauto.
Qed.

Lemma InterpUnivN_coherent i A B R (r : A ⇔ B) :
  ⟦ A ⟧ i ↘ R -> ⟦ B ⟧ i ↘ R.
Proof. hauto lq:on use:InterpExt_coherent. Qed.

Lemma PerTypeN_coherent i A0 A1 B0 B1 (rA : A0 ⇔ A1) (rB : B0 ⇔ B1) :
  ⟦ A0 ⟧ ~ ⟦ B0 ⟧ i -> ⟦ A1 ⟧ ~ ⟦ B1 ⟧ i.
Proof. hauto lq:on use:PerType_coherent, PerTypeN_nolt. Qed.

(* PerType_Fun inversion lemmas *)

Lemma PerType_Fun_inv i I A0 B0 T
  (h : ⟦ tPi A0 B0 ⟧ ~ ⟦ T ⟧ i , I) :
  exists A1 B1 RA,
    T ⇒* tPi A1 B1 /\
    ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i , I /\
    ⟦ A0 ⟧ i , I ↘ RA /\
    ⟦ A1 ⟧ i , I ↘ RA /\
    (forall a0 a1, RA a0 a1 -> ⟦ B0[a0..] ⟧ ~ ⟦ B1[a1..] ⟧ i , I).
Proof.
  move E : (tPi A0 B0) h => T0 h.
  move : A0 B0 E.
  elim : T0 T /h => //.
  - sauto lq:on.
  - move => C0 C1 D0 D1 rC rD h ih A0 B0 E; subst.
    elim /Par_inv : rC => //.
    move => ? ? A1 ? B1 rA rB.
    case => ? ? ?; subst.
    case : (ih A1 B1) => // A2 [B2] [RA] [r] [hA] [hRA1] [hRA2] hB.
    exists A2, B2, RA. repeat split; auto.
    + eapply rtc_transitive; eauto using rtc_once.
    + eapply PerType_Step; eauto using Par_refl.
    + eapply InterpExt_Step; eauto.
    + qauto l:on use:PerType_Step, Par_subst, Par_refl, InterpExt_preservation.
Qed.

Lemma PerType_Fun_inv' i I A0 B0 A1 B1
  (h : ⟦ tPi A0 B0 ⟧ ~ ⟦ tPi A1 B1 ⟧ i , I) :
  exists RA,
    ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i , I /\
    ⟦ A0 ⟧ i , I ↘ RA /\
    ⟦ A1 ⟧ i , I ↘ RA /\
    (forall a0 a1, RA a0 a1 -> ⟦ B0[a0..] ⟧ ~ ⟦ B1[a1..] ⟧ i , I).
Proof.
  move /PerType_Fun_inv : h => [A2] [B2] [RA] [r] [hA] [hRA0] [hRA2] hB.
  case /Pars_pi_inv : r => [A3] [B3] [E] [rA] rB. inversion E. subst.
  exists RA. repeat split; auto.
  - eapply PerType_Steps; eauto using rtc_refl.
  - eapply InterpExt_Steps; eauto.
  - hauto lq:on use:PerType_Steps, rtc_refl, Par_subst_star.
Qed.

Lemma PerTypeN_Fun_inv i A0 B0 T
  (h : ⟦ tPi A0 B0 ⟧ ~ ⟦ T ⟧ i) :
  exists A1 B1 RA,
    T ⇒* tPi A1 B1 /\
    ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i /\
    ⟦ A0 ⟧ i ↘ RA /\
    ⟦ A1 ⟧ i ↘ RA /\
    (forall a0 a1, RA a0 a1 -> ⟦ B0[a0..] ⟧ ~ ⟦ B1[a1..] ⟧ i).
Proof. hauto lq:on use:PerTypeN_nolt, PerType_Fun_inv. Qed.

Lemma PerTypeN_Fun_inv' i A0 B0 A1 B1
  (h : ⟦ tPi A0 B0 ⟧ ~ ⟦ tPi A1 B1 ⟧ i) :
  exists RA,
    ⟦ A0 ⟧ ~ ⟦ A1 ⟧ i /\
    ⟦ A0 ⟧ i ↘ RA /\
    ⟦ A1 ⟧ i ↘ RA /\
    (forall a0 a1, RA a0 a1 -> ⟦ B0[a0..] ⟧ ~ ⟦ B1[a1..] ⟧ i).
Proof. hauto lq:on use:PerTypeN_nolt, PerType_Fun_inv'. Qed.

(* Interpretations are cumulative *)

Lemma InterpExt_cumulative i j I A RA :
  i <= j ->
  ⟦ A ⟧ i , I ↘ RA ->
  ⟦ A ⟧ j , I ↘ RA.
Proof.
  move => ij hi.
  elim : A RA /hi;
  hauto l:on ctrs:InterpExt use:PeanoNat.Nat.le_trans.
Qed.

Lemma PerType_cumulative i j I A B :
  i <= j ->
  (⟦ A ⟧ ~ ⟦ B ⟧ i , I) ->
  (⟦ A ⟧ ~ ⟦ B ⟧ j , I).
Proof.
  move => ij hi.
  elim : A B /hi;
  hauto lq:on ctrs:PerType use:PeanoNat.Nat.le_trans, InterpExt_cumulative.
Qed.

Lemma PerTypeN_cumulative i j A B :
  i <= j ->
  ⟦ A ⟧ ~ ⟦ B ⟧ i ->
  ⟦ A ⟧ ~ ⟦ B ⟧ j.
Proof.
  have h : Acc (fun x y => x < y) i by sfirstorder use:wellfounded.
  elim : i /h.
  hauto lq:on use:PerType_cumulative, PerTypeN_nolt.
Qed.

Lemma InterpUnivN_cumulative i j A RA :
  i <= j ->
  ⟦ A ⟧ i ↘ RA ->
  ⟦ A ⟧ j ↘ RA.
Proof. hauto lq:on use:InterpExt_cumulative, PerTypeN_cumulative. Qed.

(* Interpretations are deterministic *)

Lemma InterpExt_deterministic i I A RA RB :
  ⟦ A ⟧ i , I ↘ RA ->
  ⟦ A ⟧ i , I ↘ RB ->
  RA = RB.
Proof.
  move => h.
  move : RB.
  elim : A RA / h.
  - move => A B RA RF hRA ihRA hRF hRB ihRB R hR.
    move /InterpExt_Fun_inv : hR => [RA' [RF' [hRA' [hRF' [hRB' ->]]]]].
    fext => b0 b1 a0 a1 RB'.
    specialize (ihRA RA' hRA'); subst.
    apply propositional_extensionality.
    hauto lq:on rew:off. (* slow *)
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - sfirstorder use:InterpExt_preservation.
Qed.

Lemma InterpUnivN_deterministic i A RA RB :
  ⟦ A ⟧ i ↘ RA ->
  ⟦ A ⟧ i ↘ RB ->
  RA = RB.
Proof. sfirstorder use:InterpExt_deterministic. Qed.

Lemma InterpUnivN_deterministic' i j A RA RB :
  ⟦ A ⟧ i ↘ RA ->
  ⟦ A ⟧ j ↘ RB ->
  RA = RB.
Proof.
  move => hRA hRB.
  case : (Coq.Arith.Compare_dec.le_le_S_dec i j).
  - hauto l:on use:InterpUnivN_cumulative, InterpUnivN_deterministic.
  - move => ?. have : j <= i by lia.
    hauto l:on use:InterpUnivN_cumulative, InterpUnivN_deterministic.
Qed.

Lemma InterpExt_Fun'_inv i I A B R
  (h : ⟦ tPi A B ⟧ i , I ↘ R) :
  exists (RA : tm_rel),
    ⟦ A ⟧ i , I ↘ RA /\
    (forall a0 a1, RA a0 a1 -> exists RB, ⟦ B[a0..] ⟧ i , I ↘ RB /\ ⟦ B[a1..] ⟧ i , I ↘ RB) /\
    R = ProdSpace RA (fun a RB => ⟦ B[a..] ⟧ i , I ↘ RB).
Proof.
  move /InterpExt_Fun_inv : h => [RA [RF [hRA [hRF [hRB ->]]]]].
  exists RA. repeat split => //.
  - hauto lq:on.
  - fext => b0 b1 a0 a1 RB Ra.
    apply propositional_extensionality.
    split.
    + move : hRF Ra. move /[apply] => [[RB' [RF0 RF1]] RBba] hRB0 _.
      have hRB0' : ⟦ B[a0..] ⟧ i , I ↘ RB' by auto.
      have RBRB' : RB = RB' by eauto using InterpExt_deterministic.
      sfirstorder.
    + sfirstorder.
Qed.

(* InterpUnivN and PerTypeN are transitive and reflexive *)

Lemma InterpExt_trans i I A R
  (h : ⟦ A ⟧ i , I ↘ R)
  (hsym : forall j A B, j < i -> I j A B -> I j B A)
  (htrans : forall j A B C, j < i -> I j A B -> I j B C -> I j A C) :
  forall a b c, R a b -> R b c -> R a c.
Proof.
  elim : A R /h;
  hauto l:on use:InterpExt_sym unfold:ProdSpace.
Qed.

Lemma InterpExt_refl i I A R
  (h : ⟦ A ⟧ i , I ↘ R)
  (hsym : forall j A B, j < i -> I j A B -> I j B A)
  (htrans : forall j A B C, j < i -> I j A B -> I j B C -> I j A C) :
  forall a b, R a b -> R a a /\ R b b.
Proof. hauto lq:on use:InterpExt_sym, InterpExt_trans. Qed.

Lemma PerType_trans i I
  (hsym : forall A B, (⟦ A ⟧ ~ ⟦ B ⟧ i , I) -> (⟦ B ⟧ ~ ⟦ A ⟧ i , I))
  (Isym : forall j A B, j < i -> I j A B -> I j B A)
  (Itrans : forall j A B C, j < i -> I j A B -> I j B C -> I j A C) :
  forall A B C, (⟦ A ⟧ ~ ⟦ B ⟧ i , I) -> (⟦ B ⟧ ~ ⟦ C ⟧ i , I) -> (⟦ A ⟧ ~ ⟦ C ⟧ i , I).
Proof.
  move => A B C h. move : C.
  elim : A B /h.
  - move => A0 A1 B0 B1 RA hA01 ihA hRA0 hRA1 hB01 ihB C hC.
    move /PerType_Fun_inv : hC => [A2 [B2 [RA' [hC [hA12 [hRA1' [hRA2' hB12]]]]]]].
    eapply PerType_Steps with (A1 := tPi A0 B0) (B1 := tPi A2 B2); auto.
    + apply rtc_refl.
    + have E : RA = RA' by eapply InterpExt_deterministic; eauto.
      qauto l:on ctrs:PerType use:InterpExt_refl.
  - sfirstorder.
  - hauto lq:on ctrs:PerType use:Par_refl, PerType_preservation.
Qed.

Lemma PerTypeN_trans i : forall A B C,
  PerTypeN i A B -> PerTypeN i B C -> PerTypeN i A C.
Proof.
  have h : Acc (fun x y => x < y) i by sfirstorder use:wellfounded.
  elim : i /h.
  move => j h ih A B C hAB hBC.
  simp PerTypeN in * |- *.
  eapply PerType_trans; eauto.
  - hauto l:on use:PerType_sym, PerTypeN_sym.
  - hauto q:on use:PerTypeN_sym, Compare_dec.lt_dec.
  - hauto l:on use:Compare_dec.lt_dec.
Qed.

Lemma InterpUnivN_trans i A R (h : ⟦ A ⟧ i ↘ R) :
  forall a b c, R a b -> R b c -> R a c.
Proof.
  elim : A R /h;
  hauto l:on use:InterpExt_sym, PerTypeN_sym, PerTypeN_trans unfold:ProdSpace.
Qed.

Lemma InterpUnivN_refl i A R (h : ⟦ A ⟧ i ↘ R) :
  forall a b, R a b -> R a a /\ R b b.
Proof. hauto lq:on use:InterpUnivN_sym, InterpUnivN_trans. Qed.

Lemma PerTypeN_refl i : forall A B, ⟦ A ⟧ ~ ⟦ B ⟧ i ->
  ⟦ A ⟧ ~ ⟦ A ⟧ i /\ ⟦ B ⟧ ~ ⟦ B ⟧ i.
Proof. hauto lq:on use:PerTypeN_sym, PerTypeN_trans. Qed.

(* Related types have common interpretations *)

Lemma PerType_InterpExt i I A B
  (h : ⟦ A ⟧ ~ ⟦ B ⟧ i , I)
  (Isym : forall j A B, j < i -> I j A B -> I j B A)
  (Itrans : forall j A B C, j < i -> I j A B -> I j B C -> I j A C) :
  exists R, ⟦ A ⟧ i , I ↘ R /\ ⟦ B ⟧ i , I ↘ R.
Proof.
  elim : A B /h.
  - move => A0 A1 B0 B1 RA hA ihA hRA0 hRA1 hB ihB.
    eexists. split;
    eapply InterpExt_Fun with (RF := fun a RB => ⟦ B0[a..] ⟧ i , I ↘ RB /\ ⟦ B1[a..] ⟧ i , I ↘ RB); eauto.
    + move => a0 a1 hRA01.
      have hRA11 : RA a1 a1 by eapply InterpExt_refl; eauto.
      have hRA10 : RA a1 a0 by eapply InterpExt_sym; eauto.
      case : (ihB a0 a1 hRA01) => // R01 [hR00] hR11.
      case : (ihB a1 a1 hRA11) => // R11 [hR01] hR11'.
      case : (ihB a1 a0 hRA10) => // R10 [hR01'] hR10.
      have E0 : R01 = R11 by apply (InterpExt_deterministic _ _ _ _ _ hR11 hR11').
      have E1 : R11 = R10 by apply (InterpExt_deterministic _ _ _ _ _ hR01 hR01').
      hauto lq:on.
    + sfirstorder.
    + move => a0 a1 hRA01.
      have hRA11 : RA a1 a1 by eapply InterpExt_refl; eauto.
      have hRA10 : RA a1 a0 by eapply InterpExt_sym; eauto.
      case : (ihB a0 a1 hRA01) => // R01 [hR00] hR11.
      case : (ihB a1 a1 hRA11) => // R11 [hR01] hR11'.
      case : (ihB a1 a0 hRA10) => // R10 [hR01'] hR10.
      have E0 : R01 = R11 by apply (InterpExt_deterministic _ _ _ _ _ hR11 hR11').
      have E1 : R11 = R10 by apply (InterpExt_deterministic _ _ _ _ _ hR01 hR01').
      hauto lq:on.
    + sfirstorder.
  - hauto lq:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma PerTypeN_InterpUnivN i A B
  (h : ⟦ A ⟧ ~ ⟦ B ⟧ i) :
  exists R, ⟦ A ⟧ i ↘ R /\ ⟦ B ⟧ i ↘ R.
Proof.
  best unfold:InterpUnivN use:PerType_InterpExt, PerTypeN_nolt, PerTypeN_sym, PerTypeN_trans.
Qed.

(* Soundness *)

Require Import typing.

Definition ρ_ok Γ ρ0 ρ1 := forall i A, lookup i Γ A ->
  forall m RA, ⟦ A[ρ0] ⟧ ~ ⟦ A[ρ1] ⟧ m ->
    ⟦ A[ρ0] ⟧ m ↘ RA -> ⟦ A [ρ1] ⟧ m ↘ RA ->
    RA (ρ0 i) (ρ1 i).

Definition SemWt Γ a A := forall ρ0 ρ1, ρ_ok Γ ρ0 ρ1 ->
  exists m RA, (⟦ A[ρ0] ⟧ ~ ⟦ A[ρ1] ⟧ m) /\
    (⟦ A [ρ0] ⟧ m ↘ RA) /\ (⟦ A [ρ1] ⟧ m ↘ RA) /\
    RA (a [ρ0]) (a [ρ1]).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

Definition SemWff Γ := forall i A, lookup i Γ A -> exists j, Γ ⊨ A ∈ tUniv j.
Notation "⊨ Γ" := (SemWff Γ) (at level 70).

Lemma ρ_ok_nil ρ0 ρ1 : ρ_ok nil ρ0 ρ1.
Proof. rewrite /ρ_ok. inversion 1; subst. Qed.

Lemma ρ_ok_cons i Γ ρ0 ρ1 a0 a1 RA A :
  ⟦ A [ρ0] ⟧ i ↘ RA -> ⟦ A [ρ1] ⟧ i ↘ RA -> RA a0 a1 ->
  ρ_ok Γ ρ0 ρ1 ->
  ρ_ok (A :: Γ) (a0 .: ρ0) (a1 .: ρ1).
Proof.
  move => h0 h1 hR hρ.
  rewrite /ρ_ok. inversion 1; subst.
  - move => j RA' hA h0' h1'.
    asimpl in hA. asimpl in h0'. asimpl in h1'.
    suff : RA = RA' by congruence.
    hauto l:on drew:off use:InterpUnivN_deterministic'.
  - asimpl. hauto lq:on unfold:ρ_ok solve+:lia.
Qed.

Lemma ρ_ok_renaming Γ ρ0 ρ1 :
  forall Δ ξ,
    ren_ok ξ Γ Δ ->
    ρ_ok Δ ρ0 ρ1 ->
    ρ_ok Γ (ξ >> ρ0) (ξ >> ρ1).
Proof.
  move => Δ ξ hscope h1.
  rewrite /ρ_ok => i A hi j RA.
  move: (hscope _ _ hi) => ld.
  move: (h1 _ _ ld j RA).
  by asimpl.
Qed.

Lemma renaming_SemWt Γ a A :
  (Γ ⊨ a ∈ A) ->
  forall Δ ξ,
    ren_ok ξ Γ Δ ->
    Δ ⊨ a⟨ξ⟩ ∈ A⟨ξ⟩ .
Proof.
  rewrite /SemWt => h Δ ξ hξ ρ0 ρ1 hρ.
  have hρ' : (ρ_ok Γ (ξ >> ρ0) (ξ >> ρ1)) by eauto using ρ_ok_renaming.
  case /(_ _ _ hρ') : h => m [RA hRA].
  exists m, RA. by asimpl.
Qed.

Lemma weakening_Sem Γ a A B i
  (h0 : Γ ⊨ B ∈ tUniv i)
  (h1 : Γ ⊨ a ∈ A) :
   B :: Γ ⊨ a⟨S⟩ ∈ A⟨S⟩.
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on ctrs:lookup unfold:ren_ok.
Qed.

Lemma SemWt_Univ Γ A i :
  (Γ ⊨ A ∈ tUniv i) <->
  forall ρ0 ρ1, ρ_ok Γ ρ0 ρ1 -> ⟦ A[ρ0] ⟧ ~ ⟦ A[ρ1] ⟧ i.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUnivN_Univ_inv.
  - move => /[swap] ρ0 /[swap] ρ1 /[apply] h.
    exists (S i). exists (PerTypeN i).
    have ? : i < S i by lia. 
    repeat split; auto. simp PerTypeN.
    all: hauto lq:on ctrs:InterpExt, PerType.
Qed.

Lemma SemWff_nil : SemWff nil. inversion 1. Qed.

Lemma SemWff_cons Γ A i :
  ⊨ Γ ->
  Γ ⊨ A ∈ tUniv i ->
  (* ------------ *)
  ⊨ A :: Γ.
Proof.
  move => wf wt k hscope.
  elim/lookup_inv.
  - hauto q:on use:weakening_Sem.
  - move => _ n B ? ? + ? []*. subst. move /wf => [j ?].
    exists j. change (tUniv j) with (tUniv j) ⟨S⟩.
    eauto using weakening_Sem.
Qed.

Theorem soundness :
  (forall Γ a A, Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A) /\
  (forall Γ, ⊢ Γ -> ⊨ Γ).
Proof.
  apply wt_mutual.
  (* Var *)
  1: { 
    move => Γ i A _ wf hscope ρ0 ρ1 hρ.
    case /(_ _ _ hscope) : wf => j hA.
    move /SemWt_Univ : hA => /(_ ρ0 ρ1 hρ) hA.
    have [R [hRA0 hRA1]] := PerTypeN_InterpUnivN _ _ _ hA.
    move /(_ _ _ hscope j R) : hρ => /(_ hA hRA0 hRA1) hRρ.
    exists j, R. repeat split; auto.
  }
  (* Pi *)
  1: {
    move => Γ i A B hA /SemWt_Univ ihA hB /SemWt_Univ ihB ρ0 ρ1 hρ.
    specialize (ihA ρ0 ρ1 hρ).
    exists (S i). exists (PerTypeN i).
    repeat split.
    - apply PerTypeN_Univ. lia.
    - apply InterpExt_Univ. lia.
    - apply InterpExt_Univ. lia.
    - have [R [hRA0 hRA1]] := PerTypeN_InterpUnivN _ _ _ ihA.
      asimpl. eapply PerTypeN_Fun; eauto.
      move => a0 a1 hR. asimpl.
      hauto lq:on use:ρ_ok_cons.
  }
  (* Abs *)
  1: {
    move => Γ A b B i _ ihPi _ ihb ρ0 ρ1 hρ.
    case : (ihPi ρ0 ρ1 hρ) => // k [R] [_] [hR] [_] /ltac:(asimpl) hRPi.
    case /InterpUnivN_Univ_inv : hR => E /ltac:(subst) _. clear k ihPi.
    have [R [hR0 hR1]] := PerTypeN_InterpUnivN _ _ _ hRPi.
    exists i, R. repeat split; auto.
    case /InterpExt_Fun'_inv : hR0 => RA [hRA] [_] ->.
    move => a0 a1 RB' hRAa /ltac:(asimpl) hRB0' hRB1'.
    have hρa : ρ_ok (A :: Γ) (a0 .: ρ0) (a1 .: ρ1). {
      have [_ [hA _]] := PerTypeN_Fun_inv' _ _ _ _ _ hRPi.
      case /PerTypeN_InterpUnivN : hA => [RA'] [?] ?.
      have ERA : RA = RA' by eapply InterpExt_deterministic; eauto. subst.
      eapply ρ_ok_cons; eauto.
    }
    case /(_ (a0 .: ρ0) (a1 .: ρ1) hρa) : ihb => j [RB] [hB] [hRB0] [hRB1] hRBb.
    have <- : RB = RB' by hauto l:on use:InterpUnivN_deterministic'.
    clear R hRPi hR1 hRA hRAa RA hρ hρa RB' hB hRB0' hRB1' i.
    eapply InterpUnivN_noitavreserp; eauto;
    eapply P_AppAbs'; auto using Par_refl; by asimpl.
  }
  (* App *)
  1: {
    move => Γ f A B a _ ihf _ iha ρ0 ρ1 hρ.
    case /(_ ρ0 ρ1 hρ) : iha => i [RA] [_] [hRA0] [hRA1] hRAa.
    case /(_ ρ0 ρ1 hρ) : ihf => /ltac:(asimpl) j [R] [hPi] [hR0] [hR1] hRf.
    case /InterpExt_Fun'_inv : hR0 => RA0 [hRA0'] [hRB0] E.
    case /InterpExt_Fun'_inv : hR1 => RA1 [hRA1'] [_] _.
    subst. unfold ProdSpace in hRf.
    rewrite PerTypeN_nolt in hPi.
    case /PerType_Fun_inv' : hPi => RA'' [_] [hRA0''] [hRA1''] hB.
    have ERA0 : RA0 = RA by hauto l:on use:InterpUnivN_deterministic'.
    have ERA1 : RA1 = RA by hauto l:on use:InterpUnivN_deterministic'.
    have ERA'' : RA'' = RA by hauto l:on use:InterpUnivN_deterministic'.
    subst. clear hRA0 hRA0' hRA0'' hRA1 hRA1' hRA1'' hρ i.
    move /(_ _ _ hRAa) : hB => hB.
    move /(_ _ _ hRAa) : hRB0 => [RB0] [hRB0'] hRB01.
    rewrite <- PerTypeN_nolt in hB.
    have [RB [hRB0 hRB1]] := PerTypeN_InterpUnivN _ _ _ hB.
    have ERB0 : RB0 = RB by hauto l:on use:InterpUnivN_deterministic.
    subst. move /(_ _ _ RB hRAa hRB0 hRB01) : hRf => hRBfa.
    asimpl in *. exists j, RB. repeat split; auto.
  }
  (* Conv (ew, subtyping...) *)
  1: {
    move => Γ a A B i _ iha _ ihB hsub ρ0 ρ1 hρ.
    case /(_ ρ0 ρ1 hρ) : iha => j [R] [hA] [hR1] [hR2] hRa.
    exists j, R. repeat split; auto.
    (* best use:Coherent_subst_star, InterpUnivN_coherent, PerTypeN_coherent. *)
  }
  (* Univ *)
  5: qauto l:on ctrs:PerType use:SemWt_Univ, PerTypeN_nolt.
  (* Nil *)
  11: apply SemWff_nil.
  (* Cons *)
  11: eauto using SemWff_cons.
  (* skip the rest *)
  all: admit.
Admitted.
