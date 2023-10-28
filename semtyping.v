From WR Require Import syntax join.
From Coq Require Import
  Sets.Relations_2
  Sets.Relations_2_facts
  ssreflect
  ssrbool
  Program.Basics.
From Hammer Require Import Tactics.
Require Import Psatz.

Definition ProdSpace (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop) (b : tm) :=
  forall a, PA a -> exists PB, PF a PB /\ PB (tApp b a).

Inductive InterpExt n (Interp : tm -> (tm -> Prop) -> Prop) : tm -> (tm -> Prop) -> Prop :=
| InterpExt_False : InterpExt n Interp tFalse (const False)
| InterpExt_Switch : InterpExt n Interp tSwitch (fun a => exists v, Rstar _ Par a v /\ is_bool_val v)
| InterpExt_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpExt n Interp A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExt n Interp (subst_tm (a..) B) PB) ->
  InterpExt n Interp (tPi A B) (ProdSpace PA PF)
| InterpExt_Univ m :
  (* This is a join *)
  m < n ->
  InterpExt n Interp (tUniv m) (fun A => exists PA, Interp A PA)
| InterpExt_Step A A0 PA :
  Par A A0 ->
  InterpExt n Interp A0 PA ->
  InterpExt n Interp A PA.

Fixpoint InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop :=
  match n with
  | 0 => InterpExt 0 (fun _ _ => False)
  | S n => InterpExt (S n) (InterpUnivN n)
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

(* Some basic unit tests *)
Example InterpUniv0_InterpUniv : forall A PA, InterpUnivN 0 A PA -> InterpUniv A PA.
Proof.
  move => A PA /= h.
  elim : A PA / h; sauto lq:on ctrs:InterpUniv.
Qed.

Example InterpUniv_InterpUniv0 : forall A PA, InterpUniv A PA -> InterpUnivN 0 A PA.
Proof.
  move => A PA h.
  elim : A PA / h; sauto lq:on.
Qed.

Inductive InterpType : tm -> (tm -> Prop) -> Prop :=
| InterpType_False : InterpType tFalse (const False)
| InterpType_Fun A B PA (PF : tm -> (tm -> Prop) -> Prop) :
  InterpType A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpType (subst_tm (a..) B) PB) ->
  InterpType (tPi A B) (ProdSpace PA PF)
| InterpType_Univ :
  InterpType (tUniv 0) (fun A => exists PA, InterpUnivN 0 A PA)
| InterpType_Step A0 A1 PA1 :
  Par A0 A1 ->
  InterpType A1 PA1 ->
  InterpType A0 PA1
| InterpType_Switch :
  InterpType tSwitch (fun a => exists v, Rstar _ Par a v /\ is_bool_val v).

Example InterpUniv1_InterpType : forall A PA, InterpType A PA -> InterpUnivN 1 A PA.
Proof.
  induction 1.
  - sfirstorder.
  - sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - sfirstorder.
Qed.

Lemma InterpExt_NotVar Interp n i P : ~InterpExt n Interp (var_tm i) P.
Proof.
  move E : (var_tm i) => a0 h.
  move : i E.
  elim : a0 P / h; hauto inv:InterpExt, Par.
Qed.

Lemma InterpUnivN_NotVar n i P : ~ InterpUnivN n (var_tm i) P.
Proof.
  case : n; eauto using InterpExt_NotVar.
Qed.

Lemma InterpExt_NotAbs Interp n A a P : ~ InterpExt n Interp (tAbs A a) P.
Proof.
  move E : (tAbs A a) => a0 h.
  move : A a E.
  elim : a0 P / h; hauto inv:InterpUniv, Par.
Qed.

Lemma InterpUnivN_NotAbs n A a P : ~ InterpUnivN n (tAbs A a) P.
Proof.
  case : n; eauto using InterpExt_NotAbs.
Qed.

Lemma InterpExt_Fun_inv n Interp A B P  (h : InterpExt n Interp (tPi A B) P) :
  exists (PA : tm -> Prop) (PF : tm -> (tm -> Prop) -> Prop),
    InterpExt n Interp A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PA a -> PF a PB -> InterpExt n Interp (subst_tm (a..) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (tPi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto l:on ctrs:InterpUniv.
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:par_subst.
Qed.

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
    move => a PB ha hPB0.
    apply : ihPB; eauto.
    sfirstorder use:par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation n A B P (h : InterpUnivN n A P) :
  Par A B ->
  InterpUnivN n B P.
Proof. case : n h; sfirstorder use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I A B P (h : InterpExt i I B P) :
  Rstar _ Par A B ->
  InterpExt i I A P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star n I A B P (h : InterpExt n I A P) :
  Rstar _ Par A B ->
  InterpExt n I B P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star n A B P (h : InterpUnivN n A P) :
  Rstar _ Par A B ->
  InterpUnivN n B P.
Proof. case : n h; sfirstorder use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star n A B P (h : InterpUnivN n B P) :
  Rstar _ Par A B ->
  InterpUnivN n A P.
Proof. case : n h; sfirstorder use:InterpExt_back_preservation_star. Qed.

Lemma InterpExt_Switch_inv n I P :
  InterpExt n I tSwitch P ->
  P = fun a => exists v, Rstar _ Par a v /\ is_bool_val v.
Proof.
  move E : tSwitch => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_False_inv n I P :
  InterpExt n I tFalse P ->
  P = (const False).
Proof.
  move E : tFalse => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpExt_Univ_inv n I P m :
  InterpExt n I (tUniv m) P ->
  P = (fun A => exists PA, I A PA) /\ m < n.
Proof.
  move E : (tUniv m) => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpUnivN_Switch_inv n P :
  InterpUnivN n tSwitch P ->
  P = fun a => exists v, Rstar _ Par a v /\ is_bool_val v.
Proof. case : n; sfirstorder use:InterpExt_Switch_inv. Qed.

Lemma InterpExt_deterministic n I A PA PB :
  InterpExt n I A PA ->
  InterpExt n I A PB ->
  forall x, PA x <-> PB x.
Proof.
  move => h.
  move : PB.
  elim : A PA / h.
  - hauto lq:on inv:InterpExt ctrs:InterpExt use:InterpExt_False_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Switch_inv.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Fun_inv : hP.
    qauto l:on unfold:ProdSpace.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto l:on use:InterpExt_preservation.
Qed.

Lemma InterpUnivN_deterministic n A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN n A PB ->
  forall x, PA x <-> PB x.
Proof. case : n => /=; eauto using InterpExt_deterministic. Qed.

Lemma InterpExt_mono_I n (I0 I1 : tm -> (tm -> Prop) -> Prop) :
  (forall A PA, I0 A PA -> I1 A PA) ->
  forall A PA, InterpExt n I0 A PA ->
          exists PB, InterpExt n I1 A PB /\ forall a, PA a -> PB a.
Proof.
  move => h A PA h0.
  elim : A PA / h0.
  - hauto l:on.
  - hauto l:on.
  - move => A B PA PF hPA.
    (* ih *)
    intros (PA0 & ih0 & ih1).
    move => PFTot PFOut ihPF.
    exists (ProdSpace PA0 (InterpExt n I1)).
  - move => m hm.
  - hauto lq:on ctrs:InterpExt.

Lemma InterpExt_mono n I :
  forall A PA, InterpExt n I A PA ->
          InterpExt (S n) (InterpExt n I) A PA.
Proof.
  move => A PA h0.
  elim : A PA /h0.
  - sfirstorder.
  - sfirstorder.
  - hauto l:on ctrs:InterpExt.
  - move => m hm.
    have h : InterpExt (S n) (InterpExt n I) (tUniv m)
               (fun A => exists PA, InterpExt n I A PA) by sauto lq:on.

Lemma InterpUnivN_cumulative n A PA :

Lemma InterpUnivN_cumulative n A PA :
  InterpUnivN n A PA ->
  exists PB, InterpUnivN (S n) A PB /\ forall x, PA x -> PB x.
Proof.
  elim : n.
  - simpl => h.
    elim : A PA /h.
    + hauto l:on.
    + hauto l:on.
    + sauto l:on.

  move => m hm ih A PA /ih hPA {ih}.
  simpl.

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
