From HB Require Import structures.
From mathcomp Require Import ssrnat eqtype.
Set Bullet Behavior "Strict Subproofs".
From WR Require Import syntax join.
From Coq Require Import
  Sets.Relations_2
  Sets.Relations_2_facts
  ssreflect
  ssrbool
  Program.Basics
  Logic.PropExtensionality.
From Hammer Require Import Tactics.
From Equations Require Import Equations.

Fixpoint tm_eqb (a b : tm) : bool :=
  match a, b with
  | var_tm m, var_tm n => m == n
  | tAbs A a, tAbs B b => tm_eqb A B && tm_eqb a b
  | tPi A0 A1, tPi B0 B1 => tm_eqb A0 B0 && tm_eqb A1 B1
  | tApp a0 a1, tApp b0 b1 => tm_eqb a0 b0 && tm_eqb a1 b1
  | tFalse, tFalse => true
  | tUniv i, tUniv j => i == j
  | tOn, tOn => true
  | tOff, tOff => true
  | tIf a0 a1 a2, tIf b0 b1 b2 => tm_eqb a0 b0 && tm_eqb a1 b1 && tm_eqb a2 b2
  | tSwitch, tSwitch => true
  | _, _ => false
  end.

Lemma tm_eqP : Equality.axiom tm_eqb.
Proof.
  move => a.
  elim : a; try qauto ctrs:Bool.reflect.
  - move => n.
    case => /ltac:(try qauto ctrs:Bool.reflect) m.
    suff : reflect (n = m) (n == m)
      by hauto q:on ctrs:Bool.reflect inv:Bool.reflect.
     sfirstorder use:eqnP.
  - move => A ihA a iha.
    case => /ltac:(try qauto ctrs:Bool.reflect) B b.
    move /(_ B) in ihA.
    move /(_ b) in iha.
    apply Bool.iff_reflect.
    hauto q:on  inv:Bool.reflect.
  - move => a0 iha0 a1 iha1.
    case => /ltac:(try qauto ctrs:Bool.reflect) b0 b1 /=.
    move /(_ b0) in iha0. move /(_ b1) in iha1.
    apply Bool.iff_reflect.
    hauto q:on  inv:Bool.reflect.
  - move => A ihA a iha.
    case => /ltac:(try qauto ctrs:Bool.reflect) B b.
    move /(_ B) in ihA.
    move /(_ b) in iha.
    apply Bool.iff_reflect.
    hauto q:on  inv:Bool.reflect.
  - move => n.
    case => /ltac:(try qauto ctrs:Bool.reflect) m.
    suff : reflect (n = m) (n == m)
      by hauto q:on ctrs:Bool.reflect inv:Bool.reflect.
    sfirstorder use:eqnP.
  - move => a0 iha0 a1 iha1 a2 iha2.
    case => /ltac:(try qauto ctrs:Bool.reflect) b0 b1 b2.
    move /(_ b0) in iha0. move /(_ b1) in iha1. move /(_ b2) in iha2.
    apply Bool.iff_reflect.
    hauto q:on  inv:Bool.reflect.
Qed.

HB.instance Definition _ := hasDecEq.Build _ tm_eqP.

Definition tm_rel := tm -> tm -> Prop.

Definition ProdSpace (PA : tm_rel) (PF : tm -> tm_rel -> Prop) (b0 b1 : tm)  :=
  forall a0 a1, PA a0 a1 -> exists PB, PF a0 PB /\ PB (tApp b0 a0) (tApp b1 a1).

Inductive InterpExt (n : nat) (Interp : nat -> tm -> tm -> tm_rel -> Prop) : tm -> tm -> tm_rel -> Prop :=
| InterpExt_False : InterpExt n Interp tFalse tFalse
                      (fun _ _ => False)
| InterpExt_Switch : InterpExt n Interp tSwitch tSwitch
                       (fun a b => exists v, Rstar _ Par a v /\ Rstar _ Par b v /\ is_bool_val v)
| InterpExt_Fun A0 B0 A1 B1 PA (PF : tm -> tm_rel -> Prop) :
  InterpExt n Interp A0 A1 PA ->
  (forall a0 a1, PA a0 a1 -> (exists PB, PF a0 PB) /\ (exists PB, PF a1 PB)) ->
  (forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> InterpExt n Interp (subst_tm (a0..) B0) (subst_tm (a1..) B1) PB) ->
  InterpExt n Interp (tPi A0 B0) (tPi A1 B1) (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  InterpExt n Interp (tUniv m) (tUniv m) (fun A0 A1 => exists PA, Interp m A0 A1 PA)
| InterpExt_Step A0 A1 B0 B1 PA :
  Rstar _ Par A0 A1 ->
  Rstar _ Par B0 B1 ->
  InterpExt n Interp A1 B1 PA ->
  InterpExt n Interp A0 B0 PA.

Lemma InterpExt_Univ' n Interp m PF :
  PF = (fun A => exists PA, Interp m A PA \/ ) ->
  m < n ->
  InterpExt n Interp (tUniv m) PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Equations InterpUnivN (n : nat) : tm -> (tm -> Prop) -> Prop by wf n lt :=
  InterpUnivN n := InterpExt n (fun m A PA =>
                                  match Compare_dec.lt_dec m n with
                                  | left h => InterpUnivN m A PA
                                  | right _ => False
                                  end).

Lemma InterpExt_NotVar Interp n i P : ~InterpExt n Interp (var_tm i) P.
Proof.
  move E : (var_tm i) => a0 h.
  move : i E.
  elim : a0 P / h; hauto inv:InterpExt, Par.
Qed.

Lemma InterpUnivN_NotVar n i P : ~ InterpUnivN n (var_tm i) P.
Proof.
  hauto l:on rew:db:InterpUnivN use:InterpExt_NotVar.
Qed.

Lemma InterpExt_NotAbs Interp n A a P : ~ InterpExt n Interp (tAbs A a) P.
Proof.
  move E : (tAbs A a) => a0 h.
  move : A a E.
  elim : a0 P / h; hauto inv:Par.
Qed.

Lemma InterpUnivN_NotAbs n A a P : ~ InterpUnivN n (tAbs A a) P.
Proof.
  hauto l:on rew:db:InterpUnivN use:InterpExt_NotAbs.
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
  - hauto l:on.
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
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

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
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star n A B P (h : InterpUnivN n B P) :
  Rstar _ Par A B ->
  InterpUnivN n A P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

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
  P = (fun A => exists PA, I m A PA) /\ m < n.
Proof.
  move E : (tUniv m) => A h.
  move : E.
  elim : A P / h; hauto lq:on inv:Par.
Qed.

Lemma InterpUnivN_Switch_inv n P :
  InterpUnivN n tSwitch P ->
  P = fun a => exists v, Rstar _ Par a v /\ is_bool_val v.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Switch_inv. Qed.

Lemma InterpExt_deterministic n I A PA PB :
  InterpExt n I A PA ->
  InterpExt n I A PB ->
  PA = PB.
Proof.
  move => h.
  suff ? : InterpExt n I A PB -> forall x, PA x <-> PB x.
  move => *; fext. sfirstorder use:propositional_extensionality.
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
  PA = PB.
Proof.
  simp InterpUnivN.
  eauto using InterpExt_deterministic.
Qed.

Lemma InterpExt_Lift n m I A PA :
  n < m ->
  InterpExt n I A PA ->
  InterpExt m I A PA.
Proof.
  move => h h0.
  elim : A PA /h0; sauto l:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant n I A PA
  (h : InterpExt n I A PA) :
      InterpExt n (fun m A PA =>
                     match Compare_dec.lt_dec m n with
                     | left h => I m A PA
                     | right _ => False
                     end) A PA.
Proof.
  elim : A PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    case : Compare_dec.lt_dec => //.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 n (I :fin -> tm -> (tm -> Prop) -> Prop ) A PA
  (h : InterpExt n (fun m A PA =>
                      match Compare_dec.lt_dec m n with
                     | left h => I m A PA
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
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_nolt n :
  InterpUnivN n = InterpExt n InterpUnivN.
Proof.
  simp InterpUnivN.
  fext => A P.
  apply propositional_extensionality.
  hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpUnivN_cumulative n A PA :
  InterpUnivN n A PA -> forall m, n < m ->
  InterpUnivN m A PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_Lift.
Qed.

Lemma InterpUnivN_deterministic' n m A PA PB :
  InterpUnivN n A PA ->
  InterpUnivN m A PB ->
  PA = PB.
Proof.
  move => h0 h1.
  move : (Coq.Arith.Compare_dec.lt_eq_lt_dec m n).
  case; first case.
  - hauto l:on use:InterpUnivN_cumulative, InterpUnivN_deterministic.
  - move => *; subst.
    sfirstorder use:InterpUnivN_deterministic.
  - move => ?.
    symmetry.
    hauto l:on use:InterpUnivN_cumulative, InterpUnivN_deterministic.
Qed.

Lemma InterpExt_back_clos n (I : nat -> tm -> (tm -> Prop) -> Prop) A PA
  (hI : forall m, m < n -> forall a b, Par a b -> forall PA, I m b PA -> I m a PA ):
  InterpExt n I A PA ->
  forall a b, Par a b ->
         PA b -> PA a.
Proof.
  move => h.
  elim : A PA / h.
  - sfirstorder.
  - hauto lq:on ctrs:Rstar use:Rstar_transitive.
  - move => A B PA PF hPA ihA hPFTot hPF ihPF a b hab.
    rewrite /ProdSpace => hb.
    move => a0 ha0.
    move : (hb _ ha0). intros (PB & hPB & hPB').
    exists PB; split; auto.
    apply : ihPF; eauto.
    hauto l:on ctrs:Par use:Par_refl.
  - hauto lq:on.
  - sfirstorder.
Qed.

Lemma InterpUnivN_back_clos n A PA :
    InterpUnivN n A PA ->
    forall a b, Par a b ->
           PA b -> PA a.
Proof.
  elim /Wf_nat.lt_wf_ind : n => n ih.
  simp InterpUniv.
  apply InterpExt_back_clos.
  ecrush.
Qed.

Lemma InterpUnivN_back_clos_star n A PA :
    InterpUnivN n A PA ->
    forall a b, Rstar _ Par a b ->
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
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv, InterpUnivN_Univ_inv, InterpUnivN_deterministic.
Qed.
