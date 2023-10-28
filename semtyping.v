From WR Require Import syntax join.
From Coq Require Import
  Sets.Relations_2
  Sets.Relations_2_facts
  ssreflect
  ssrbool
  Program.Basics.
From Hammer Require Import Tactics.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a, PA a -> exists PB, PF a PB /\ PB (tApp b a).


Inductive InterpExt n (Interp : nat -> tm -> (tm -> Prop) -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_False : InterpExt n Interp tFalse (const False)
| InterpExt_Switch : InterpExt n Interp tSwitch (fun a => exists v, Rstar _ Par a v /\ is_bool_val v)
| InterpExt_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpExt n Interp A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExt n Interp (subst_tm (a..) B) PB) ->
  InterpExt n Interp (tPi A B) (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  InterpExt n Interp (tUniv m) (fun A => exists PA, Interp m A PA)
| InterpExt_Step A A0 PA :
  Par A A0 ->
  InterpExt n Interp A0 PA ->
  InterpExt n Interp A PA.

(* (n : nat) -> fin n -> (tm -> Prop) -> Prop*)

Fixpoint InterpUnivN (n : nat) : nat -> tm -> (tm -> Prop) -> Prop :=
  match n with
  | 0 => fun m => InterpExt 0 (fun _ _ _ => False)
  | S n => fun m => InterpExt n (InterpUnivN n)
  end.

Inductive InterpUniv : tm -> (tm -> Prop) -> Prop :=
| InterpUniv_False : InterpUniv tFalse (const False)
| InterpUniv_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpUniv A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpUniv (subst_tm (a..) B) PB) ->
  InterpUniv (tPi A B) (ProdSpace PA PF)
| InterpUniv_Step A0 A1 PA1 :
  Par A0 A1 ->
  InterpUniv A1 PA1 ->
  InterpUniv A0 PA1
| InterpUniv_Switch :
  InterpUniv tSwitch (fun a => exists v, Rstar _ Par a v /\ is_bool_val v).

(* Lemma InterpUniv0_InterpUniv : forall A PA, InterpUnivN 0 A PA -> InterpUniv A PA. *)
(* Proof. *)
(*   move => A PA /= h. *)
(*   elim : A PA / h. *)
(*   - sfirstorder. *)
(*   - sfirstorder. *)
(*   - hauto l:on ctrs:InterpUniv. *)
(*   - *)



Inductive InterpType : tm -> (tm -> Prop) -> Prop :=
| InterpType_False : InterpType tFalse (const False)
| InterpType_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpType A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpType (subst_tm (a..) B) PB) ->
  InterpType (tPi A B) (ProdSpace PA PF)
| InterpType_Univ :
  InterpType tUniv (fun A => exists PA, InterpUniv A PA)
| InterpType_Step A0 A1 PA1 :
  Par A0 A1 ->
  InterpType A1 PA1 ->
  InterpType A0 PA1
| InterpType_Switch :
  InterpType tSwitch (fun a => exists v, Rstar _ Par a v /\ is_bool_val v).

Lemma InterpUniv_NotVar i P : ~ InterpUniv (var_tm i) P.
Proof.
  move E : (var_tm i) => a0 h.
  move : i E.
  elim : a0 P / h; hauto inv:InterpUniv, Par.
Qed.

Lemma InterpType_NotVar i P : ~ InterpType (var_tm i) P.
Proof.
  move E : (var_tm i) => a0 h.
  move : i E.
  elim : a0 P / h; hauto inv:InterpType, Par.
Qed.

Lemma InterpUniv_NotAbs A a P : ~ InterpUniv (tAbs A a) P.
Proof.
  move E : (tAbs A a) => a0 h.
  move : A a E.
  elim : a0 P / h; hauto inv:InterpUniv, Par.
Qed.

Lemma InterpType_NotAbs A a P : ~ InterpType (tAbs A a) P.
Proof.
  move E : (tAbs A a) => a0 h.
  move : A a E.
  elim : a0 P / h; hauto inv:InterpType, Par.
Qed.

Lemma InterpUniv_Fun_inv A0 B0 P  (h : InterpUniv (tPi A0 B0) P) :
  exists A1 B1, Rstar _ Par A0 A1 /\ Rstar _ Par B0 B1 /\ exists PA PF,
      P = ProdSpace PA PF /\ InterpUniv A1 PA /\
        (forall a PB, PA a -> PF a PB -> InterpUniv (subst_tm (a..) B1) PB) /\
        (forall a, PA a -> exists PB, PF a PB).
Proof.
  move E : (tPi A0 B0) h => T h.
  move : A0 B0 E.
  elim : T P / h => //.
  - hauto lq:on ctrs:InterpUniv, Rstar.
  - move => A0 A1 PA1 h0 h1 ih A2 B2 ?; subst.
    elim /Par_inv : h0 => //.
    move => h2 A0 A3 B0 B1 h3 h4 [? ?] ?; subst.
    move /(_ A3 B1 ltac:(done)) : ih.
    intros (A1 & B3 & h5 & h6 & h7).
    have [*] : Rstar _ Par A2 A1 /\ Rstar _ Par B2 B3
      by hauto lq:on rew:off ctrs:Rstar use:Relations_2_facts.Rstar_transitive.
    hauto lq:on rew:off ctrs:InterpUniv.
Qed.

Lemma InterpType_Fun_inv A0 B0 P  (h : InterpType (tPi A0 B0) P) :
  exists A1 B1, Rstar _ Par A0 A1 /\ Rstar _ Par B0 B1 /\ exists PA PF,
      P = ProdSpace PA PF /\ InterpType A1 PA /\
        (forall a PB, PA a -> PF a PB -> InterpType (subst_tm (a..) B1) PB) /\
        (forall a, PA a -> exists PB, PF a PB).
Proof.
  move E : (tPi A0 B0) h => T h.
  move : A0 B0 E.
  elim : T P / h => //.
  - hauto lq:on ctrs:InterpType, Rstar.
  - move => A0 A1 PA1 h0 h1 ih A2 B2 ?; subst.
    elim /Par_inv : h0 => //.
    move => h2 A0 A3 B0 B1 h3 h4 [? ?] ?; subst.
    move /(_ A3 B1 ltac:(done)) : ih.
    intros (A1 & B3 & h5 & h6 & h7).
    have [*] : Rstar _ Par A2 A1 /\ Rstar _ Par B2 B3
      by hauto lq:on rew:off ctrs:Rstar use:Relations_2_facts.Rstar_transitive.
    hauto lq:on rew:off ctrs:InterpType.
Qed.

Lemma InterpUniv_preservation A B P (h : InterpUniv A P) :
  Par A B ->
  InterpUniv B P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto lq:on inv:Par ctrs:InterpUniv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpUniv_Fun; auto.
    move => a PB ha hPB0.
    apply : ihPB; eauto.
    sfirstorder use:par_cong, Par_refl.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpUniv.
  - hauto lq:on inv:Par ctrs:InterpUniv.
Qed.

Lemma InterpType_preservation A B P (h : InterpType A P) :
  Par A B ->
  InterpType B P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto lq:on inv:Par ctrs:InterpType.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpType_Fun; auto.
    move => a PB ha hPB0.
    apply : ihPB; eauto.
    sfirstorder use:par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpType.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpType.
  - hauto lq:on inv:Par ctrs:InterpType.
Qed.

Lemma InterpUniv_preservation_star A B P (h : InterpUniv A P) :
  Rstar _ Par A B ->
  InterpUniv B P.
Proof. induction 1; hauto l:on use:InterpUniv_preservation. Qed.

Lemma InterpType_preservation_star A B P (h : InterpType A P) :
  Rstar _ Par A B ->
  InterpType B P.
Proof. induction 1; hauto l:on use:InterpType_preservation. Qed.

Lemma InterpUniv_back_preservation_star A B P (h : InterpUniv B P) :
  Rstar _ Par A B ->
  InterpUniv A P.
Proof. induction 1; hauto l:on ctrs:InterpUniv. Qed.

Lemma InterpType_back_preservation_star A B P (h : InterpType B P) :
  Rstar _ Par A B ->
  InterpType A P.
Proof. induction 1; hauto l:on ctrs:InterpType. Qed.

Lemma InterpUniv_Fun_inv' A B P :
  InterpUniv (tPi A B) P ->
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpUniv A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PA a -> PF a PB -> InterpUniv (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move /InterpUniv_Fun_inv.
  intros (A1 & B1 & hP1 & hP2 & PA & PF & ? & hPA & hPF & hPFTotal).
  exists PA, PF; split; eauto;
  qauto l:on use:par_subst_star, InterpUniv_back_preservation_star.
Qed.

Lemma InterpType_Fun_inv' A B P :
  InterpType (tPi A B) P ->
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpType A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PA a -> PF a PB -> InterpType (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move /InterpType_Fun_inv.
  intros (A1 & B1 & hP1 & hP2 & PA & PF & ? & hPA & hPF & hPFTotal).
  exists PA, PF; split; eauto;
  qauto l:on use:par_subst_star, InterpType_back_preservation_star.
Qed.

Lemma InterpUniv_Switch_inv P :
  InterpUniv tSwitch P ->
  P = fun a => exists v, Rstar _ Par a v /\ is_bool_val v.
Proof.
  move E : tSwitch => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpType_Switch_inv P :
  InterpType tSwitch P ->
  P = fun a => exists v, Rstar _ Par a v /\ is_bool_val v.
Proof.
  move E : tSwitch => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpUniv_deterministic A PA PB :
  InterpUniv A PA ->
  InterpUniv A PB ->
  forall x, PA x <-> PB x.
Proof.
  move => h.
  move : PB.
  elim : A PA / h.
  - suff : forall P, InterpUniv tFalse P -> P = (const False) by sauto lq:on rew:off.
    move E : tFalse => a P h.
    move : E.
    elim : a P / h; sauto lq:on rew:off.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpUniv_Fun_inv' : hP.
    qauto l:on unfold:ProdSpace.
  - hauto l:on use:InterpUniv_preservation.
  - hauto lq:on inv:InterpUniv use:InterpUniv_Switch_inv.
Qed.


Lemma InterpType_Univ_inv P :
  InterpType tUniv P ->
  P = (fun A => exists PA, InterpUniv A PA).
Proof.
  move E : tUniv => a h.
  move : E.
  elim : a P / h; hauto lq:on rew:off ctrs:InterpUniv inv:Par.
Qed.

Lemma InterpType_deterministic A PA PB :
  InterpType A PA ->
  InterpType A PB ->
  forall x, PA x <-> PB x.
Proof.
  move => h.
  move : PB.
  elim : A PA / h.
  - suff : forall P, InterpType tFalse P -> P = (const False) by sauto lq:on rew:off.
    move E : tFalse => a P h.
    move : E.
    elim : a P / h; sauto lq:on rew:off.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpType_Fun_inv' : hP.
    qauto l:on unfold:ProdSpace.
  - hauto lq:on rew:off inv:InterpType use:InterpType_Univ_inv.
  - hauto l:on use:InterpType_preservation.
  - hauto lq:on inv:InterpType use:InterpType_Switch_inv.
Qed.

Lemma InterpUniv_subset_InterpType A PA :
  InterpUniv A PA ->
  InterpType A PA.
Proof.
  move => h.
  elim : A PA / h; hauto l:on ctrs:InterpType.
Qed.

Lemma InterpUniv_back_clos A PA :
  InterpUniv A PA ->
  forall a b, Par a b ->
         PA b -> PA a.
Proof.
  move => h.
  elim : A PA / h.
  - sfirstorder.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF a b hab.
    rewrite /ProdSpace => hb.
    move => a0 ha0.
    move : (hb _ ha0). intros (PB & hPB & hPB').
    exists PB; split; auto.
    apply : ihPF; eauto.
    hauto l:on ctrs:Par use:Par_refl.
  - sfirstorder.
  - hauto lq:on ctrs:Rstar use:Rstar_transitive.
Qed.

Lemma InterpType_back_clos A PA :
  InterpType A PA ->
  forall a b, Par a b ->
         PA b -> PA a.
Proof.
  move => h.
  elim : A PA / h.
  - sfirstorder.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF a b hab.
    rewrite /ProdSpace => hb.
    move => a0 ha0.
    move : (hb _ ha0). intros (PB & hPB & hPB').
    exists PB; split; auto.
    apply : ihPF; eauto.
    hauto l:on ctrs:Par use:Par_refl.
  - qauto l:on ctrs:InterpUniv use:InterpUniv_back_clos.
  - sfirstorder.
  - hauto lq:on ctrs:Rstar use:Rstar_transitive.
Qed.

Lemma InterpType_back_clos_star A PA :
  InterpType A PA ->
  forall a b, Rstar _ Par a b ->
         PA b -> PA a.
Proof.
  move => h a b R.
  elim : a b /R; [done | sfirstorder use:InterpType_back_clos].
Qed.
