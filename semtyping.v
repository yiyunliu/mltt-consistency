From WR Require Import syntax join imports common.

Definition candidate (P : tm -> Prop) : Prop :=
  forall a b, Par a b -> P b -> P a.

Definition PropSpace (PF : (tm -> Prop) -> (tm -> Prop) -> Prop) (b : tm) :=
  forall PA a PB, PA a -> candidate PA -> PF PA PB -> PB (tApp b a).

Inductive InterpProp (γ : nat -> (tm -> Prop)) : tm -> (tm -> Prop) -> Prop :=
| InterpProp_Var i : InterpProp γ (var_tm i) (γ i)
| InterpProp_Void : InterpProp γ tVoid (const False)
| InterpProp_Bool : InterpProp γ tBool (fun a => exists v, Pars a v /\ is_bool_val v)
| InterpProp_Fun A B PF :
  (forall PA, candidate PA -> exists PB, PF PA PB) ->
  (forall PA PB, candidate PA -> PF PA PB -> InterpProp (PA .: γ) B PB) ->
  InterpProp γ (tPi A B) (PropSpace PF)
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
  exists (PF : (tm -> Prop) -> (tm -> Prop) -> Prop),
    (forall PA, candidate PA -> exists PB, PF PA PB) /\
    (forall PA PB, candidate PA -> PF PA PB -> InterpProp (PA .: γ) B PB) /\
    P = PropSpace PF.
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
  - move => γ A B PF hPFTot hPF ihPF hγ b0 b1 hb01.
    rewrite /PropSpace => hPB PA a PB hPFa.
    have ? : Par (tApp b0 a)(tApp b1 a) by hauto lq:on ctrs:Par use:Par_refl.
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
  - move => γ A B PF hPB hPB' ihPB P hP.
    move /InterpProp_Fun_inv : hP.
    intros (PF0 & hPA0 & hPB0 & ?); subst.
    fext.
    move => b PA a PB hPA ha.
    apply propositional_extensionality.
    sblast.
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
Definition SemTWt Γ A := forall ρ γ, ργ_ok Γ ρ γ  ->  exists PA, InterpProp γ A PA.

Lemma InterpProp_renaming ξ γ A PA :
  InterpProp (ξ >> γ) A PA -> InterpProp γ (ren_tm ξ A) PA.
Proof.
  move E : (ξ >> γ) => γ' h.
  move : ξ γ E.
  elim : γ'  A PA  / h.
  - move => *. subst. asimpl. sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => ? A B PF PFTot PFRes ihPF ξ γ ?; subst.
    asimpl.
    apply InterpProp_Fun.
    sfirstorder.
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
Admitted.

Lemma γ_ok_renaming Γ ρ γ :
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
  have : ργ_ok Γ (ξ >> ρ) (ξ >> γ) by eauto using γ_ok_renaming.
  move :h. move/[apply].
  asimpl.
  intros (PA & h0 & h1).
  exists PA. move : h0.
  split; last by auto.
  sfirstorder use:InterpProp_renaming.
Qed.

Definition renaming_SemTWt Γ A :
  SemTWt Γ A ->
  forall Δ ξ,
    good_renaming ξ Γ Δ ->
    SemTWt Δ (ren_tm ξ A).
Proof.
  rewrite /SemWt => h Δ ξ hξ ρ γ hργ.
  have : ργ_ok Γ (ξ >> ρ) (ξ >> γ) by eauto using γ_ok_renaming.
  move :h. move/[apply].
  asimpl.
  intros (PA & h0).
  exists PA. move : h0.
  sfirstorder use:InterpProp_renaming.
Qed.

Definition SemWff Γ := forall i, i < length Γ -> SemTWt (skipn (S i) Γ) (ith Γ i).

Section SemTyping.
  Context (Γ : list tm).

  Lemma ST_Var i
    (h0 : SemWff Γ)
    (h1 : i < length Γ) :
    SemWt Γ (var_tm i) (dep_ith Γ i).
  Proof using Type.
    move : (h0) (h1). move/[apply].
    move : renaming_SemTWt (good_renaming_truncate (S i) Γ). repeat move/[apply].
    rewrite -dep_ith_shift.
    move => h.
    move => ρ γ h2.
    move : h (h2). move/[apply].
    case => PA h.
    exists PA; split=>//.
    asimpl.
    case /(_ i) : h2 => h2 h3.
    sfirstorder.
  Qed.

  Lemma ST_Void :
    SemTWt Γ tVoid.
  Proof using Type. hauto l:on. Qed.

  Lemma ST_Pi A B :
    SemTWt Γ A ->
    SemTWt (A :: Γ) B ->
    SemTWt Γ (tPi A B).
  Proof using Type.
    rewrite /SemTWt => hA hB ρ γ hργ.
    move : hA (hργ); move/[apply]. intros (PA & hPA).
    exists (PropSpace (fun a PB => forall PA,  candidate PA -> PA a -> InterpProp (PA .: γ) (subst_tm (a..) B) PB)).
    apply InterpProp_Fun.
    best.
    best.
    best.
