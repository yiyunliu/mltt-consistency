From HB Require Import structures.
From WR Require Import join.
From mathcomp Require Export ssrnat eqtype ssrbool zify.
From Hammer Require Import Tactics Hammer.
#[export] Set Bullet Behavior "Strict Subproofs".
From Coq Require Import Logic.PropExtensionality.
From Equations Require Import Equations.
Import stdpp.relations (rtc_refl).

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
  forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> PB (tApp b0 a0) (tApp b1 a1).

Lemma ProdSpace_El_Sym (PA : tm_rel) (PF : tm -> tm_rel -> Prop) (b0 b1 : tm)
  (h0 : forall a0 a1, PA a0 a1 -> PA a1 a0)
  (h3 : forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> PF a1 PB)
  (h1 : ProdSpace PA PF b0 b1)
  (h2 : forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> forall b0 b1, PB b0 b1 -> PB b1 b0) :
  ProdSpace PA PF b1 b0.
Proof. qauto l:on unfold:ProdSpace. Qed.

(* Would it be cleaner to factor out the PER relation out? *)
Inductive InterpExt (n : nat) (Interp : nat -> tm -> tm -> tm_rel -> Prop) : tm -> tm -> tm_rel -> Prop :=
| InterpExt_False : InterpExt n Interp tFalse tFalse
                      (fun _ _ => False)
| InterpExt_Switch : InterpExt n Interp tSwitch tSwitch
                       (fun a b => exists v, Pars a v /\ Pars b v /\ is_bool_val v)
| InterpExt_Fun A0 B0 A1 B1 PA (PF : tm -> tm_rel -> Prop) :
  InterpExt n Interp A0 A1 PA ->
  (forall a0 a1, PA a0 a1 -> exists PB, PF a0 PB) ->
  (forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> PF a1 PB) ->
  (forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> InterpExt n Interp (subst_tm (a0..) B0) (subst_tm (a1..) B1) PB) ->
  InterpExt n Interp (tPi A0 B0) (tPi A1 B1) (ProdSpace PA PF)
| InterpExt_Univ m :
  m < n ->
  InterpExt n Interp (tUniv m) (tUniv m) (fun A0 A1 => exists PA, Interp m A0 A1 PA)
| InterpExt_Step A0 A1 B0 B1 PA :
  Par A0 A1 ->
  Par B0 B1 ->
  InterpExt n Interp A1 B1 PA ->
  InterpExt n Interp A0 B0 PA.

Lemma InterpExt_Fun' n Interp A0 B0 A1 B1 PA (PF : tm -> tm_rel -> Prop) :
  InterpExt n Interp A0 A1 PA ->
  (forall a0 a1 PB, PA a0 a1 -> (exists PB, PF a0 PB) /\ (PF a0 PB -> PF a1 PB /\ InterpExt n Interp (subst_tm (a0..) B0) (subst_tm (a1..) B1) PB)) ->
  InterpExt n Interp (tPi A0 B0) (tPi A1 B1) (ProdSpace PA PF).
Proof. hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_El_Sym n Interp A A0 PA
  (h0 : forall m A0 A1 PA, m < n -> Interp m A0 A1 PA -> Interp m A1 A0 PA)
  (h : InterpExt n Interp A A0 PA) :
  forall a b, PA a b -> PA b a.
Proof.
  elim : A A0 PA / h.
  - sfirstorder.
  - sfirstorder.
  - move => A0 B0 A1 B1 PA PF hPA ihPA PFTot PFRes hPF ihPF b0 b1 hb.
    hauto l:on use:ProdSpace_El_Sym.
  - hauto lq:on.
  - sfirstorder.
Qed.

Lemma InterpExt_Sym n Interp A A0 PA
  (hl : forall m A0 A1 PA, m < n -> Interp m A0 A1 PA -> Interp m A1 A0 PA)
  (h : InterpExt n Interp A A0 PA) :
  InterpExt n Interp A0 A PA.
Proof.
  elim : A A0 PA / h.
  - sfirstorder ctrs:InterpExt.
  - sfirstorder ctrs:InterpExt.
  - hauto l:on use:InterpExt_El_Sym ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_Univ' n Interp m PF :
  PF = (fun A0 A1 => exists PA, Interp m A0 A1 PA) ->
  m < n ->
  InterpExt n Interp (tUniv m) (tUniv m) PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Lemma ltb_acc : forall a : nat, Acc (fun x y => x < y) a.
Proof.
  constructor.
  elim : a => [|a].
  - lia.
  - move => ih.
    case => [_|b h].
    + constructor. lia.
    + have ? : b < a by done.
      constructor => y h1.
      apply ih.
      simpl in *.
      lia.
Qed.

#[export]Instance ltb_wf : WellFounded (fun x y => x < y) := ltb_acc.

(* wf is over coq's lt but not ssreflect's *)
Equations InterpUnivN (n : nat) : tm -> tm -> tm_rel -> Prop by wf n (fun x y => x < y) :=
  InterpUnivN n := InterpExt n (fun m A0 A1 PA =>
                                  match @idP (m < n) with
                                  | Bool.ReflectT h => InterpUnivN m A0 A1 PA
                                  | _ => False
                                  end).

Lemma InterpExt_lt_redundant n I A0 A1 PA
  (h : InterpExt n I A0 A1 PA) :
      InterpExt n (fun m A0 A1 PA =>
                     match @idP (m < n) with
                     | ReflectT h => I m A0 A1 PA
                     | _ => False
                     end) A0 A1 PA.
Proof.
  elim : A0 A1 PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m h.
    apply InterpExt_Univ' => //.
    destruct idP => //.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant2 n I A0 A1 PA
  (h : InterpExt n (fun m A0 A1 PA =>
                      match @idP (m < n) with
                     | ReflectT h => I m A0 A1 PA
                     | _ => False
                     end) A0 A1 PA) :
  InterpExt n I A0 A1 PA.
Proof.
  elim : A0 A1 PA / h.
  - hauto l:on.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - move => m ?.
    apply InterpExt_Univ' => //.
    destruct idP => //.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_nolt n :
  InterpUnivN n = InterpExt n InterpUnivN.
Proof.
  simp InterpUnivN.
  fext => A0 A1 P.
  apply propositional_extensionality.
  hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpUniv_Sym n : forall A B PA,
    InterpUnivN n A B PA ->
    InterpUnivN n B A PA.
Proof.
  (* See ubnP for a more idiomatic way of doing strong induction with ssreflect *)
  have h : Acc (fun x y => x < y) n by sfirstorder use:wellfounded.
  elim : n /h.
  hauto l:on db:InterpUniv use:InterpExt_Sym.
Qed.

Lemma InterpUniv_El_Sym n A B PA
    (h : InterpUnivN n A B PA) :
    forall a b, PA a b -> PA b a.
Proof.
  hauto lq:on use:InterpUniv_Sym, InterpExt_El_Sym db:InterpUniv.
Qed.

Lemma Par_preserves_false (A B : tm):
  A == tFalse ->
  Par A B ->
  B == tFalse.
Proof.
  case : A => // ?.
  inversion 1 => //.
Qed.

Lemma Par_preserves_switch (A B : tm):
  A == tSwitch ->
  Par A B ->
  B == tSwitch.
Proof.
  case : A => // ?.
  inversion 1 => //.
Qed.

Lemma Par_preserves_univ (A B : tm) (i : nat) :
  A == tUniv i ->
  Par A B ->
  B == tUniv i.
Proof.
  case : A => // ? ?.
  inversion 1 => //.
Qed.

Lemma InterpExt_False_inv n I A0 A1 P :
  (A0 == tFalse) || (A1 == tFalse) ->
  InterpExt n I A0 A1 P ->
  P = (fun a b => False) /\ Pars A0 tFalse /\ Pars A1 tFalse.
Proof.
  move => h1 h.
  move : h1.
  elim : A0 A1 P / h => //.
  hauto lq:on inv:Par ctrs:rtc.
  hauto qb:on ctrs:rtc use:@rtc_refl use:Par_preserves_false.
Qed.

Lemma InterpExt_Switch_inv n I A0 A1 P :
  (A0 == tSwitch) || (A1 == tSwitch) ->
  InterpExt n I A0 A1 P ->
  P = (fun a b => exists v, Pars a v /\ Pars b v /\ is_bool_val v) /\ Pars A0 tSwitch /\ Pars A1 tSwitch.
Proof.
  move => h1 h.
  move : h1.
  elim : A0 A1 P / h => //.
  hauto lq:on inv:Par ctrs:rtc.
  hauto qb:on ctrs:rtc use:@rtc_refl use:Par_preserves_switch.
Qed.

Lemma InterpExt_Univ_inv n I A0 A1 m P :
  (A0 == tUniv m) || (A1 == tUniv m) ->
  InterpExt n I A0 A1 P ->
  P = (fun A0 A1 => exists PA, I m A0 A1 PA) /\ m < n /\ Pars A0 (tUniv m) /\ Pars A1 (tUniv m).
Proof.
  move => /[swap] h.
  elim : A0 A1 P / h => //.
  - move => m0 h /=.
    rewrite Bool.orb_diag => /eqP. hauto lq:on ctrs:rtc.
  - hauto qb:on ctrs:rtc use:@rtc_refl use:Par_preserves_univ.
Qed.

Lemma InterpExt_back_preservation_star i I A0 A1 B P
  (h : InterpExt i I A1 B P) :
  Pars A0 A1 ->
  InterpExt i I A0 B P.
Proof.
  induction 1;
    hauto l:on ctrs:InterpExt use:Par_refl.
Qed.

Lemma InterpExt_back_preservation_star2 i I B A0 A1 P
  (h : InterpExt i I B A1 P) :
  Pars A0 A1 ->
  InterpExt i I B A0 P.
Proof.
  induction 1;
    hauto l:on ctrs:InterpExt use:Par_refl.
Qed.

Lemma InterpExt_preservation n I A0 A1 B0 B1 P (h : InterpExt n I A0 B0 P) :
  Par A0 A1  ->
  Par B0 B1 ->
  InterpExt n I A1 B1 P.
Proof.
  move : A1 B1.
  elim : A0 B0 P / h; auto.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A0 B0 A1 B1 PA PF hPA ihPA hPB hPB' hPB'' ihPB A2 B2.
    elim /Par_inv => //.
    move => ? ? A3 ? B3 h1 h2 [] ? ? ?; subst.
    elim /Par_inv => //.
    move => ? ? A4 ? B4 h3 h4 [] ? ? ?; subst.
    apply InterpExt_Fun'; auto.
    hauto l:on use:par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => A0 A1 B0 B1 P h0 h1 h2 ih A2 B2 h3 h4.
    move /par_diamond /(_ h3) : (h0).
    move /par_diamond /(_ h4) : (h1).
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_preservation_star n I A0 A1 B P
  (h : InterpExt n I A0 B P) :
  Pars A0 A1 ->
  InterpExt n I A1 B P.
Proof. induction 1; hauto l:on use:InterpExt_preservation, Par_refl. Qed.

Lemma InterpExt_preservation_star2 n I B A0 A1 P
  (h : InterpExt n I B A0 P) :
  Pars A0 A1 ->
  InterpExt n I B A1 P.
Proof. induction 1; hauto l:on use:InterpExt_preservation, Par_refl. Qed.

Lemma InterpExt_Fun_inv n Interp A0 B0 T1 P  (h : InterpExt n Interp (tPi A0 B0) T1 P) :
 exists (A1 B1 : tm) (PA : tm_rel) (PF : tm -> tm_rel -> Prop),
   Pars T1 (tPi A1 B1) /\
    InterpExt n Interp A0 A1 PA /\
     (forall a0 a1, PA a0 a1 -> exists PB, PF a0 PB) /\
   (forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> PF a1 PB) /\
   (forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> InterpExt n Interp (subst_tm (a0..) B0) (subst_tm (a1..) B1) PB) /\
     P = ProdSpace PA PF.
Proof.
  move E : (tPi A0 B0) h => T0 h.
  move : A0 B0 E.
  elim : T0 T1 P / h => //.
  - hauto l:on ctrs:rtc.
  - move => A0 A1 B0 B1 PA hp0 hp1 hPA ihPA A2 B2 ?; subst.
    elim /Par_inv : hp0 => // hp0 A0 A3 B3 B4 hp2 hp3 [] *; subst.
    move /(_ A3 B4 ltac:(done)) in ihPA.
    move : ihPA; intros (A1 & B3 & PA0 & PF & h).
    exists A1, B3, PA0, PF.
    repeat split; try sfirstorder.
    + hauto lq:on ctrs:rtc.
    + hauto lq:on ctrs:InterpExt use:InterpExt_preservation, Par_refl.
    + sblast use: par_subst, @rtc_refl, Par_refl.
Qed.

Lemma is_bool_val_par v0 v1 : is_bool_val v0 -> Pars v0 v1 -> is_bool_val v1.
Proof. induction 2; hauto q:on inv:Par. Qed.


Lemma ProdSpace_El_Trans PA PF b0 b1 b2
  (hPA : forall a0 a1, PA a0 a1 -> PA a1 a0)
  (hPA' : forall a0 a1 a2, PA a0 a1 -> PA a1 a2 -> PA a0 a2)
  (ihPF : forall a0 a1 PB, PA a0 a1 -> PF a0 PB -> forall b0 b1 b2, PB b0 b1 -> PB b1 b2 -> PB b0 b2)
  (h01 : ProdSpace PA PF b0 b1)
  (h12 : ProdSpace PA PF b1 b2) :
  ProdSpace PA PF b0 b2.
Proof.
  rewrite /ProdSpace in h01 h12 * => a0 a2 PB ha02 hPB.
  move /ihPF :(ha02).
  move /(_ PB hPB).
  have : PA a0 a0 by qauto l:on. hauto lq:on rew:off.
Qed.

Lemma InterpExt_El_Trans n Interp A B PA
  (hI0 : forall m A0 A1 PA, m < n -> Interp m A0 A1 PA -> Interp m A1 A0 PA)
  (hI : forall m A B C PA PB, m < n -> Interp m A B PA -> Interp m B C PB -> Interp m A C PA /\ PA = PB)
  (h : InterpExt n Interp A B PA ) :
  forall a0 a1 a2, PA a0 a1 -> PA a1 a2 -> PA a0 a2.
Proof.
  elim : A B PA / h.
  - sfirstorder.
  - move => a0 a1 a2 [v0 ?] [v1 ?].
    have [v ?] : exists v, Pars v0 v /\ Pars v1 v by sfirstorder use:par_confluent.
    exists v.
    sfirstorder use:@relations.rtc_transitive, is_bool_val_par.
  - hauto l:on use:InterpExt_El_Sym, ProdSpace_El_Trans.
  - hauto lq:on.
  - sfirstorder.
Qed.

Lemma InterpExt_Trans n Interp A B C PA PC
  (hI0 : forall m A0 A1 PA, m < n -> Interp m A0 A1 PA -> Interp m A1 A0 PA)
  (hI : forall m A B C PA PB, m < n -> Interp m A B PA -> Interp m B C PB -> Interp m A C PA /\ PA = PB) :
  InterpExt n Interp A B PA ->
  InterpExt n Interp B C PC ->
  PA = PC /\ InterpExt n Interp A C PA.
  move => h.
  move : C PC.
  elim : A B PA / h.
  - move => C PC /InterpExt_False_inv.
    hauto lq:on use:InterpExt_back_preservation_star2.
  - move => C PC /InterpExt_Switch_inv.
    hauto lq:on use:InterpExt_back_preservation_star2.
  - move => A0 B0 A1 B1 PA PF hPA ihPA PFTot PFRes hPF ihPF C PC /InterpExt_Fun_inv.
    intros (A2 & B2 & PA0 & PF0 & hp & hPA0 & PFTot' & PFRes' & hPF' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    have ? : forall a0 a1, PA a0 a1 -> PA a0 a0
        by hauto lq:on use:InterpExt_El_Trans, InterpExt_El_Sym.
    move {hI hI0}.
    rewrite /ProdSpace.
    split; cycle 1.
    + apply : InterpExt_back_preservation_star2; eauto.
      apply InterpExt_Fun'; eauto.
      * sfirstorder.
      * move => a0 a1 PB h0.
        split; first by sfirstorder.
        suff : PA a0 a0; hauto lq:on rew:off.
    + fext.
      move => b0 b1 a0 a1 PB ha01.
      have ? : PA a0 a0 by firstorder.
      apply propositional_extensionality.
      split; hauto lq:on rew:off.
  - move => m h C PC /InterpExt_Univ_inv.
    move /(_ m). rewrite eq_refl.
    hauto lq:on ctrs:InterpExt use:InterpExt_back_preservation_star2.
  - hauto lq:on rew:off ctrs:InterpExt use:InterpExt_preservation, Par_refl.
Qed.

Lemma InterpUniv_TransDeter n : forall A B C PA PB,
    InterpUnivN n A B PA ->
    InterpUnivN n B C PB ->
    PA = PB /\ InterpUnivN n A C PA.
Proof.
  have h : Acc (fun x y => x < y) n by sfirstorder use:wellfounded.
  elim : n /h => n _ ih.
  simp InterpUniv in *.
  move => A B C PA PB.
  apply InterpExt_Trans => //.
  - hauto l:on use:InterpUniv_Sym.
  - hauto lq:on rew:off.
Qed.

Lemma InterpUniv_Refl n : forall A B PA,
    InterpUnivN n A B PA ->
    InterpUnivN n A A PA /\ InterpUnivN n B B PA.
Proof.
  hauto lq:on use:InterpUniv_TransDeter, InterpUniv_Sym.
Qed.

Lemma InterpUnivN_deterministic n A B C PA PB :
    InterpUnivN n A B PA ->
    InterpUnivN n A C PB ->
    PA = PB.
Proof.
  move => ? /InterpUniv_Sym ?.
  hauto lq:on use:InterpUniv_TransDeter.
Qed.

Lemma InterpExt_Lift n m I A B PA :
  n <= m ->
  InterpExt n I A B PA ->
  InterpExt m I A B PA.
Proof.
  move => h h0.
  elim : A B PA /h0.
  - sfirstorder.
  - sfirstorder.
  - hauto l:on ctrs:InterpExt.
  - move => m0 ?.
    have : m0 < m by lia. hauto lq:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_cumulative n A B PA :
  InterpUnivN n A B PA -> forall m, n <= m ->
  InterpUnivN m A B PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_Lift.
Qed.

Lemma InterpUnivN_deterministic' n m A B C PA PB
    (h0 : InterpUnivN n A B PA)
    (h1 : InterpUnivN m A C PB) :
    PA = PB.
Proof.
  have ? : m <= n \/ n <= m by lia.
  have ? : exists n, InterpUnivN n A B PA /\ InterpUnivN n A C PB
      by sfirstorder use:InterpUnivN_cumulative.
  hauto l:on use:InterpUnivN_deterministic.
Qed.

Lemma InterpUnivN_preservation n A0 B0 A1 B1 P (h : InterpUnivN n A0 B0 P) :
  Par A0 A1 ->
  Par B0 B1 ->
  InterpUnivN n A1 B1 P.
Proof. hauto l:on rew:db:InterpUniv use: InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star n A0 A1 B P
  (h : InterpUnivN n A0 B P) :
  Pars A0 A1 ->
  InterpUnivN n A1 B P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation n A0 A1 B0 B1 P
  (h : InterpUnivN n A0 B0 P) :
  Par A1 A0 ->
  Par B1 B0 ->
  InterpUnivN n A1 B1 P.
Proof.
  simp InterpUniv in *; hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation_star2 n B A0 A1 P
  (h : InterpUnivN n B A0 P) :
  Pars A0 A1 ->
  InterpUnivN n B A1 P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star2. Qed.

Lemma InterpUnivN_back_preservation_star I A0 A1 B P
  (h : InterpUnivN I A1 B P) :
  Pars A0 A1 ->
  InterpUnivN I A0 B P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star2 I B A0 A1 P
  (h : InterpUnivN I B A1 P) :
  Pars A0 A1 ->
  InterpUnivN I B A0 P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star2. Qed.

Lemma InterpExt_back_clos n I A B PA
  (hI : forall m, m < n -> forall a0 a1 b0 b1, Par a0 a1 -> Par b0 b1 ->
                                     forall PA, I m a1 b1 PA -> I m a0 b0 PA ):
  InterpExt n I A B PA ->
  forall a0 a1 b0 b1,
    Par a0 a1 ->
    Par b0 b1 ->
    PA a1 b1 -> PA a0 b0.
Proof.
  move => h.
  elim : A B PA / h.
  - sfirstorder.
  - hauto lq:on ctrs:rtc.
  - move => A0 B0 A1 B1 PA PF hPA ihPA PFTot PFRes hPF ihPF a0 a1 b0 b1 ha hb.
    rewrite /ProdSpace => hab.
    move => e0 e1 PB he hPB.
    have ? : Par (tApp a0 e0) (tApp a1 e0) by hauto lq:on use:Par_refl ctrs:Par.
    have ? : Par (tApp b0 e1) (tApp b1 e1) by hauto lq:on use:Par_refl ctrs:Par.
    hauto lq:on.
  - hauto lq:on.
  - sfirstorder.
Qed.

Lemma InterpUnivN_back_clos n A B PA :
    InterpUnivN n A B PA ->
    forall a0 a1 b0 b1,
      Par a0 a1 ->
      Par b0 b1 ->
      PA a1 b1 -> PA a0 b0.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpUnivN_back_preservation, InterpExt_back_clos.
Qed.

Lemma InterpUnivN_back_clos_star n A B PA :
    InterpUnivN n A B PA ->
    forall a0 a1 b,
      Pars a0 a1 ->
      PA a1 b -> PA a0 b.
Proof.
  move => h a b.
  induction 1; hauto lq:on use:InterpUnivN_back_clos, Par_refl.
Qed.

Lemma InterpUnivN_back_clos_star2 n A B PA :
    InterpUnivN n A B PA ->
    forall b a0 a1,
      Pars a0 a1 ->
      PA b a1 -> PA b a0.
Proof.
  move => h a b.
  induction 1; hauto lq:on use:InterpUnivN_back_clos, Par_refl.
Qed.

Lemma InterpUnivN_Univ_inv i j :
  j < i ->
  InterpUnivN i (tUniv j) (tUniv j)
    (fun A B : tm => exists PA, InterpUnivN j A B PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [|//].
  by simp InterpUniv.
Qed.

Lemma InterpExt_Univ_inv1 n I m P :
  InterpExt n I (tUniv m) (tUniv m) P ->
  P = (fun A0 A1 => exists PA, I m A0 A1 PA) /\ m < n.
Proof. hauto lqb:on use:@eq_refl, InterpExt_Univ_inv. Qed.

Lemma InterpUnivN_Univ_inv' i j P :
  InterpUnivN i (tUniv j) (tUniv j) P ->
  P = (fun A B : tm => exists PA, InterpUnivN j A B PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv1, InterpUnivN_Univ_inv, InterpUnivN_deterministic.
Qed.
