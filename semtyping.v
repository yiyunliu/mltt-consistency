From WR Require Import syntax join imports common.

Definition candidate (P : tm -> Prop) : Prop :=
  forall a b, Par a b -> P b -> P a.

Definition PropSpace (PA : tm -> Prop) (PF : (tm -> Prop) -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a, PA a ->
       forall PA0 PB, candidate PA0 -> PF PA0 PB -> PB (tApp b a).

Inductive InterpProp (γ : nat -> (tm -> Prop)) : tm -> (tm -> Prop) -> Prop :=
| InterpProp_Var i : InterpProp γ (var_tm i) (γ i)
| InterpProp_Void : InterpProp γ tVoid (const False)
| InterpProp_Bool : InterpProp γ tBool (fun a => exists v, Pars a v /\ is_bool_val v)
| InterpProp_Fun A B PA PF :
  (* Is this really impredicative? *)
  (* Can the input type really be interpreted? *)
  (* What if A : Type 1? *)
  InterpProp γ A PA ->
  (forall PA, candidate PA -> exists PB, PF PA PB) ->
  (forall PA PB, candidate PA -> PF PA PB -> InterpProp (PA .: γ) B PB) ->
  InterpProp γ (tPi A B) (PropSpace PA PF)
| InterpProp_Eq a b A :
  InterpProp γ (tEq a b A) (fun p => Pars p tRefl /\ Coherent a b)
| InterpProp_Step A A0 PA :
  Par A A0 ->
  InterpProp γ A0 PA ->
  InterpProp γ A PA.

Lemma InterpProp_Eq' γ PA a b A :
  PA = (fun p => Pars p tRefl /\ Coherent a b) ->
  InterpProp γ (tEq a b A) PA.
Proof. hauto lq:on use:InterpProp_Eq. Qed.

Lemma InterpProp_Fun_inv γ A B P  (h : InterpProp γ (tPi A B) P) :
  exists PA (PF : (tm -> Prop) -> (tm -> Prop) -> Prop),
    InterpProp γ A PA /\
    (forall PA, candidate PA -> exists PB, PF PA PB) /\
    (forall PA PB, candidate PA -> PF PA PB -> InterpProp (PA .: γ) B PB) /\
    P = PropSpace PA PF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : γ T P / h => //.
  - hauto l:on.
  - move => γ A A0 PA hA hPA ihPA A1 B ?; subst.
    elim /Par_inv : hA=>//.
    hauto lq:on rew:off ctrs:InterpProp.
Qed.

Lemma InterpProp_preservation γ A B P (h : InterpProp γ A P) :
  Par A B ->
  InterpProp γ B P.
Proof.
  move : B.
  elim : γ A P / h; auto.
  - hauto lq:on inv:Par ctrs:InterpProp.
  - hauto lq:on inv:Par ctrs:InterpProp.
  - hauto lq:on inv:Par ctrs:InterpProp.
  - hauto l:on ctrs:InterpProp inv:Par.
  - move => γ a b A B.
    elim /Par_inv=>// h ? ? ? a0 b0 A0 ? ? ? [] *. subst.
    apply InterpProp_Eq'.
    fext => p.
    f_equal.
    apply propositional_extensionality.
    hauto lq:on use:Par_Coherent, Coherent_transitive, Coherent_symmetric.
  - move => γ A B P h0 h1 ih1 C hC.
    move:par_confluent h0 hC. repeat move/[apply].
    hauto lq:on ctrs:InterpProp.
Qed.

Lemma candidate_cons γ (h : forall i, candidate (γ i)) PA :
  candidate PA ->
  (forall i, candidate ((PA .: γ) i)).
Proof. qauto l:on inv:nat. Qed.

Lemma InterpProp_back_clos γ A PA :
  (forall i, candidate (γ i)) ->
  InterpProp γ A PA ->
  forall a b, Par a b ->
         PA b -> PA a.
Proof.
  move/[swap] => h.
  elim : γ A PA / h.
  - sfirstorder.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - move => γ A B PA PF hPA ihPA hPFTot hPF ihPF hγ b0 b1 hb01.
    rewrite /PropSpace => hPB a Pa PA0 PB hPA0 hPB0.
    have ? : Par (tApp b0 a)(tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
    apply : ihPF;
    qauto l:on ctrs:rtc use:candidate_cons.
  - hauto lq:on ctrs:rtc.
  - sfirstorder.
Qed.

Lemma InterpProp_back_preservation_star γ A B P (h : InterpProp γ B P) :
  Pars A B ->
  InterpProp γ A P.
Proof. induction 1; hauto l:on ctrs:InterpProp. Qed.

Lemma InterpProp_preservation_star γ A B P (h : InterpProp γ A P) :
  Pars A B ->
  InterpProp γ B P.
Proof. induction 1; hauto l:on use:InterpProp_preservation. Qed.

Lemma InterpProp_Coherent γ A B P (h : InterpProp γ B P) :
  Coherent A B ->
  InterpProp γ A P.
Proof.
  hauto l:on unfold:Coherent use:InterpProp_back_preservation_star, InterpProp_preservation_star.
Qed.

Lemma InterpProp_Bool_inv γ P :
  InterpProp γ tBool P ->
  P = fun a => exists v, Pars a v /\ is_bool_val v.
Proof.
  move E : tBool => A h.
  move : E.
  elim : γ A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpProp_Void_inv γ P :
  InterpProp γ tVoid P ->
  P = (const False).
Proof.
  move E : tVoid => A h.
  move : E.
  elim : γ A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpProp_Eq_inv γ a b A P :
  InterpProp γ (tEq a b A) P ->
  P = (fun A => Pars A tRefl /\ Coherent a b).
Proof.
  move E : (tEq a b A) => T h.
  move : a b A E.
  elim : γ T P /h => //. hauto lq:on rew:off inv:Par.
  move => γ A A0 PA hred hA0 ih a b A1 ?. subst.
  elim /Par_inv : hred=>//.
  move => hred ? ? ? a2 b2 A2 ? ? ? [] *;subst.
  specialize ih with (1 := eq_refl).
  rewrite ih.
  fext => A. f_equal.
  apply propositional_extensionality.
  hauto lq:on use:Par_Coherent, Coherent_symmetric, Coherent_transitive.
Qed.

Lemma InterpProp_Var_inv γ i P :
  InterpProp γ (var_tm i) P ->
  P = γ i.
Proof.
  move E : (var_tm i) => A h.
  move : i E.
  elim : γ A P / h=>//.
  sfirstorder.
  hauto lq:on rew:off inv:Par.
Qed.

Lemma InterpProp_deterministic γ A PA PB :
  InterpProp γ A PA ->
  InterpProp γ A PB ->
  PA = PB.
Proof.
  move => h.
  move : PB.
  elim : γ A PA / h.
  - sfirstorder use:InterpProp_Var_inv.
  - hauto lq:on inv:InterpProp ctrs:InterpProp use:InterpProp_Void_inv.
  - hauto lq:on inv:InterpProp use:InterpProp_Bool_inv.
  - move => γ A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpProp_Fun_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB1 & ?); subst.
    fext => b a.
    have ? : PA0 = PA by sfirstorder. subst.
    apply propositional_extensionality.
    have ? : forall PA PB, candidate PA -> PF PA PB -> InterpProp (PA .: γ) B PB by sfirstorder.
    have ? : forall PA PB, candidate PA -> PF0 PA PB -> InterpProp (PA .: γ) B PB by sfirstorder.
    split.
    + move => h ha PA0 PB hcand hh.
      move : hPB (hcand); move/[apply]. case => PB0 ?.
      have ? : PB0 = PB by sfirstorder. subst.
      firstorder.
    + move => h ha PA0 PB hcand hPB2.
      move : (hPB0) (hcand). move/[apply]. case => PB0 ?.
      have ? : PB = PB0 by sfirstorder. subst.
      firstorder.
  - hauto lq:on inv:InterpProp use:InterpProp_Eq_inv.
  - hauto l:on use:InterpProp_preservation.
Qed.

Lemma InterpProp_back_clos_star γ A PA :
  (forall i, candidate (γ i)) ->
  InterpProp γ A PA ->
    forall a b, Pars a b ->
           PA b -> PA a.
Proof.
  move => h a b.
  induction 1 => // /ltac:(sfirstorder use:InterpProp_back_clos).
Qed.

Definition ργ_ok (Γ : list tm) (ρ : nat -> tm) (γ : nat -> (tm -> Prop)) := forall i , candidate (γ i) /\ (i < length Γ -> forall PA, InterpProp γ (dep_ith Γ i) PA -> PA (ρ i)).
Definition SemWt Γ a A := forall ρ γ, ργ_ok Γ ρ γ  -> exists PA, InterpProp γ A PA /\ PA (subst_tm ρ a).
Definition SemTWt A := forall γ, (forall i, candidate (γ i))  ->  exists PA, InterpProp γ A PA.


Lemma P_AppAbs_cbn (A a b b0 : tm) :
  b0 = subst_tm (b..) a ->
  Par (tApp (tAbs A a) b) b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

Lemma InterpProp_renaming ξ γ A PA :
  InterpProp (ξ >> γ) A PA -> InterpProp γ (ren_tm ξ A) PA.
Proof.
  move E : (ξ >> γ) => γ' h.
  move : ξ γ E.
  elim : γ'  A PA  / h.
  - move => *. subst. asimpl. sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => ? A B PA PF hPA ihPA PFTot PFRes ihPF ξ γ ?; subst.
    asimpl.
    apply InterpProp_Fun; eauto.
    move => *.
    apply : ihPF; eauto.
    by asimpl.
  - move => ? a b A ξ γ ?; subst.
    asimpl.
    apply InterpProp_Eq'.
    fext => p.
    apply propositional_extensionality.
    split.
    hauto l:on use:Coherent_renaming.
    move => ?.
    split; first by tauto.
    admit.
  - admit.
Admitted.

Lemma InterpProp_anti_renaming ξ γ A PA :
  InterpProp γ (ren_tm ξ A) PA -> InterpProp (ξ >> γ) A PA.
Proof.
  move E : (ren_tm ξ A) => T h.
  move : ξ A E.
  elim : γ T PA /h.
  - move => γ i ξ A eq.
    case : A eq => //.
    move => n. case => ?; subst.
    replace (γ (ξ n)) with ((ξ >> γ) n); last by asimpl.
    apply InterpProp_Var.
  - hauto q:on ctrs:InterpProp inv:tm.
  - hauto q:on ctrs:InterpProp inv:tm.
  - admit.
  - admit.
  - admit.
Admitted.



Lemma ργ_ok_renaming Γ ρ γ :
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    ργ_ok Δ ρ γ ->
    ργ_ok Γ (ξ >> ρ) (ξ >> γ).
Proof.
  move => Δ ξ hscope h1.
  rewrite /ργ_ok => i.
  split; first by sfirstorder.
  move => h PA.
  asimpl.
  move : hscope h. move/[apply] .
  case => h2 h3.
  move /InterpProp_renaming.
  rewrite -h3.
  sfirstorder.
Qed.

Lemma renaming_SemWt Γ a A :
  SemWt Γ a A ->
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    SemWt Δ (ren_tm ξ a) (ren_tm ξ A).
Proof.
  rewrite /SemWt => h Δ ξ hξ ρ γ hργ.
  have : ργ_ok Γ (ξ >> ρ) (ξ >> γ) by eauto using ργ_ok_renaming.
  move :h. move/[apply].
  asimpl.
  intros (PA & h0 & h1).
  exists PA. move : h0.
  split; last by auto.
  sfirstorder use:InterpProp_renaming.
Qed.

Definition renaming_SemTWt ξ A :
  SemTWt A ->
  SemTWt (ren_tm ξ A).
Proof.
  rewrite /SemTWt => h γ h0.
  have : (forall i, candidate (γ (ξ i))) by firstorder.
  move :h. move/[apply].
  hauto l:on use:InterpProp_renaming.
Qed.

(* Lemma ργ_ok_cons A Γ a ρ PA γ *)
(*   (h0 : candidate PA) *)
(*   (h1 : PA a) *)
(*   (h2 : ) *)
(* ργ_ok (A :: Γ) (a .: ρ) (PA .: γ) *)

Definition SemWff Γ := forall i, i < length Γ -> SemTWt (ith Γ i).

Section SemTyping.
  Context (Γ : list tm).

  Lemma ST_Var i
    (h0 : SemWff Γ)
    (h1 : i < length Γ) :
    SemWt Γ (var_tm i) (dep_ith Γ i).
  Proof using Type.
    move : (h0) (h1). move/[apply].
    move : renaming_SemTWt . repeat move/[apply].
    move /(_ (Nat.add (S i))).
    rewrite -dep_ith_shift.
    move => h.
    move => ρ γ h2.
    move : h (h2).
    rewrite /SemTWt.
    move : h1.
    move/[swap].
    move /(_ γ ltac:(sfirstorder)).
    sfirstorder.
  Qed.

  Lemma ST_Void :
    SemTWt tVoid.
  Proof using Type. hauto l:on. Qed.

  Lemma ST_Pi A B :
    SemTWt A ->
    SemTWt B ->
    SemTWt (tPi A B).
  Proof using Type.
    rewrite /SemTWt => hA hB γ hγ.
     move : hA (hγ); move/[apply]. intros (PA & hPA).
    exists (PropSpace PA (fun PA PB => InterpProp (PA .: γ) B PB)).
    apply InterpProp_Fun; eauto.
    move => PA0 hPA0.
    move /(_ (PA0 .: γ)) : hB.
    case.
    - hauto q:on inv:nat.
    - sfirstorder.
  Qed.

  Lemma ST_Abs A a B :
    SemTWt (tPi A B) ->
    SemWt (A :: Γ) a B ->
    SemWt Γ (tAbs A a) (tPi A B).
  Proof using Type.
    rewrite /SemTWt /SemWt => hPi ha ρ γ hργ.
    have ? : forall i, candidate (γ i) by sfirstorder.
    move /(_ γ ltac:(sfirstorder)) : hPi. intros (PPi & hPPi).
    exists PPi.
    move /InterpProp_Fun_inv : (hPPi).
    intros (PA & PF & hPA & PFTot & (hPF & ?)). subst.
    split;first by auto.
    asimpl.
    move => a0 ha0 PA0 PB /[dup] hPA0.
    move : hPF. (repeat move/[apply]) => h.
    move : (h).
    move : InterpProp_back_clos. repeat move/[apply].
    apply; eauto using P_AppAbs_cbn.
    qauto l:on inv:nat.
    asimpl.
    move /(_ (a0 .: ρ) (PA0 .: γ)) in ha.
    case : ha.
    - case.
      + asimpl. simpl. split; auto.
        move => ? PA1.
        move => h2.
        have ? : InterpProp γ A PA1 by sfirstorder use:InterpProp_anti_renaming.
        have ? : PA = PA1 by sfirstorder use:InterpProp_deterministic. subst.
        sfirstorder.
      + move => n.
        asimpl.
        split; auto.
        simpl.
        move /Arith_prebase.lt_S_n => ? PA1.
        move => h2.
        have ? : InterpProp γ (dep_ith Γ n) PA1 by sfirstorder use:InterpProp_anti_renaming.
        sfirstorder.
    - move => PB0.
      case => *.
      have ? : PB= PB0 by sfirstorder use:InterpProp_deterministic.  by subst.
  Qed.
