From WR Require Import syntax.
From Coq Require Import
  ssreflect
  ssrbool
  Sets.Relations_2
  Sets.Relations_3
  Sets.Relations_3_facts.
From Hammer Require Import Tactics Reflect.
Import Order.Theory.


Local Open Scope bool_scope.

Module Type join_sig
  (Import grade : grade_sig)
  (Import syntax : syntax_sig grade).

Notation eith Ξ i := (nth i Ξ el).

Definition is_bool_val a :=
  match a with
  | tOn => true
  | tOff => true
  | _ => false
  end.

Definition econtext := list grade.

Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  (* ------- *)
  Par (var_tm i) (var_tm i)
| P_Univ n :
  (* -------- *)
  Par (tUniv n) (tUniv n)
| P_False :
  (* -------- *)
  Par tFalse tFalse
| P_Pi ℓ A0 A1 B0 B1 :
  Par A0 A1 ->
  Par B0 B1 ->
  (* --------------------- *)
  Par (tPi ℓ A0 B0) (tPi ℓ A1 B1)
| P_Abs ℓ A0 A1 a0 a1 :
  Par a0 a1 ->
  (* -------------------- *)
  Par (tAbs ℓ A0 a0) (tAbs ℓ A1 a1)
| P_App a0 a1 ℓ b0 b1 :
  Par a0 a1 ->
  Par b0 b1 ->
  (* ------------------------- *)
  Par (tApp a0 ℓ b0) (tApp a1 ℓ b1)
| P_AppAbs a ℓ A a0 b0 b1 :
  Par a (tAbs ℓ A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a ℓ b0) (subst_tm (b1..) a0)
| P_On :
  (* ------- *)
  Par tOn tOn
| P_Off :
  (* ---------- *)
  Par tOff tOff
| P_If a0 a1 b0 b1 c0 c1:
  Par a0 a1 ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a0 b0 c0) (tIf a1 b1 c1)
| P_IfOn a b0 b1 c0 c1 :
  Par a tOn ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) b1
| P_IfOff a b0 b1 c0 c1 :
  Par a tOff ->
  Par b0 b1 ->
  Par c0 c1 ->
  (* ---------- *)
  Par (tIf a b0 c0) c1
| P_Switch :
  Par tSwitch tSwitch.

#[export]Hint Constructors Par : par.

Inductive IEq (Ξ : econtext) (ℓ : grade) : tm -> tm -> Prop :=
| I_Var i :
  i < length Ξ ->
  (eith Ξ i <= ℓ)%O ->
  (* ------- *)
  IEq Ξ ℓ (var_tm i) (var_tm i)
| I_Univ i :
  (* -------- *)
  IEq Ξ ℓ (tUniv i) (tUniv i)
| I_False :
  (* -------- *)
  IEq Ξ ℓ tFalse tFalse
| I_Pi ℓ0 A0 A1 B0 B1 :
  IEq Ξ ℓ A0 A1 ->
  IEq (ℓ0 :: Ξ) ℓ B0 B1 ->
  (* --------------------- *)
  IEq Ξ ℓ (tPi ℓ0 A0 B0) (tPi ℓ0 A1 B1)
| I_Abs ℓ0 A0 A1 a0 a1 :
  IEq (ℓ0 :: Ξ) ℓ a0 a1 ->
  (* -------------------- *)
  IEq Ξ ℓ (tAbs ℓ0 A0 a0) (tAbs ℓ0 A1 a1)
| I_App a0 a1 ℓ0 b0 b1 :
  IEq Ξ ℓ a0 a1 ->
  GIEq Ξ ℓ ℓ0 b0 b1 ->
  (* ------------------------- *)
  IEq Ξ ℓ (tApp a0 ℓ0 b0) (tApp a1 ℓ0 b1)
| I_On :
  (* ------- *)
  IEq Ξ ℓ tOn tOn
| I_Off :
  (* ---------- *)
  IEq Ξ ℓ tOff tOff
| I_If a0 a1 b0 b1 c0 c1:
  IEq Ξ ℓ a0 a1 ->
  IEq Ξ ℓ b0 b1 ->
  IEq Ξ ℓ c0 c1 ->
  (* ---------- *)
  IEq Ξ ℓ (tIf a0 b0 c0) (tIf a1 b1 c1)
| I_Switch :
  IEq Ξ ℓ tSwitch tSwitch
with GIEq (Ξ : econtext) (ℓ : grade) : grade -> tm -> tm -> Prop :=
| GI_Dist ℓ0 A B :
  (ℓ0 <= ℓ)%O ->
  IEq Ξ ℓ A B ->
  (* -------------- *)
  GIEq Ξ ℓ ℓ0 A B
| GI_InDist ℓ0 A B :
  (~~ (ℓ0 <= ℓ))%O ->
  (* -------------- *)
  GIEq Ξ ℓ ℓ0 A B.

#[export]Hint Constructors IEq GIEq : indist.

Definition Join := coherent _ Par.

Scheme IEq_ind' := Induction for IEq Sort Prop
    with GIEq_ind' := Induction for GIEq Sort Prop.

Combined Scheme IEq_mutual from IEq_ind', GIEq_ind'.

Lemma ieq_sym_mutual : forall Ξ ℓ,
  (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A) /\
  (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> GIEq Ξ ℓ ℓ0 B A).
Proof.
  apply IEq_mutual; eauto with indist.
Qed.

Lemma ieq_trans_mutual : forall Ξ ℓ,
  (forall A B, IEq Ξ ℓ A B -> forall C, IEq Ξ ℓ B C -> IEq Ξ ℓ A C) /\
  (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> forall C, GIEq Ξ ℓ ℓ0 B C -> GIEq Ξ ℓ ℓ0 A C).
Proof.
  apply IEq_mutual; hauto lq:on ctrs:IEq, GIEq inv:IEq,GIEq.
Qed.

Lemma ieq_trans : forall Ξ ℓ A B C, IEq Ξ ℓ A B -> IEq Ξ ℓ B C -> IEq Ξ ℓ A C.
Proof. sfirstorder use:ieq_trans_mutual. Qed.


Lemma pars_pi_inv ℓ A B C (h : Rstar _ Par (tPi ℓ A B) C) :
  exists A0 B0, C = tPi ℓ A0 B0 /\ Rstar _ Par A A0 /\ Rstar _ Par B B0.
Proof.
  move E : (tPi ℓ A B) h => T h.
  move : A B E.
  elim : T C / h; hecrush inv:Par ctrs:Rstar, Par.
Qed.

Lemma join_pi_inj ℓ A B A0 B0 (h : Join (tPi ℓ A B) (tPi ℓ A0 B0)) :
  Join A A0 /\ Join B B0.
Proof. hauto q:on use:pars_pi_inv unfold:Join, coherent. Qed.

Lemma pars_univ_inv i A (h : Rstar _ Par (tUniv i) A) :
  A = tUniv i.
Proof.
  move E : (tUniv i) h => A0 h.
  move : E.
  elim : A0 A / h; hauto lq:on rew:off ctrs:Rstar, Par inv:Par.
Qed.

Lemma join_univ_inj i j (h : Join (tUniv i) (tUniv j)) : i = j.
Proof. hauto lq:on rew:off inv:Rstar use:pars_univ_inv unfold:Join, coherent. Qed.

Lemma Par_refl (a : tm) : Par a a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma P_IfOn_star a b c :
  Rstar _ Par a tOn ->
  Rstar _ Par (tIf a b c) b.
  move E : tOn => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl, Rstar_contains_R unfold:contains.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : Rstar_transitive; eauto.
    apply Rstar_contains_R.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

Lemma P_IfOff_star a b c :
  Rstar _ Par a tOff ->
  Rstar _ Par (tIf a b c) c.
  move E : tOff => v h.
  move : E.
  elim : a v / h.
  - hauto lq:on ctrs:Par use:Par_refl, Rstar_contains_R unfold:contains.
  - move => a a0 a1 h0 h1 h2 ?; subst.
    move /(_ eq_refl) in h2.
    apply : Rstar_transitive; eauto.
    apply Rstar_contains_R.
    hauto lq:on ctrs:Par use:Par_refl.
Qed.

#[export]Hint Unfold Join : par.

Lemma P_AppAbs' a ℓ A a0 b0 b b1 :
  b = subst_tm (b1..) a0 ->
  Par a (tAbs ℓ A a0) ->
  Par b0 b1 ->
  (* ---------------------------- *)
  Par (tApp a ℓ b0) b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma par_renaming a b (ξ : fin -> fin) :
  Par a b ->
  Par (ren_tm ξ a) (ren_tm ξ b).
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  move => *.
  apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma pars_renaming a b (ξ : fin -> fin) :
  Rstar _ Par a b ->
  Rstar _ Par (ren_tm ξ a) (ren_tm ξ b).
Proof. induction 1; hauto lq:on ctrs:Rstar use:par_renaming. Qed.

Lemma join_renaming a b (ξ : fin -> fin) :
  Join a b ->
  Join (ren_tm ξ a) (ren_tm ξ b).
Proof. hauto lq:on rew:off unfold:Join, coherent use:pars_renaming. Qed.

Lemma par_morphing_lift (ξ0 ξ1 : fin -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  forall i, Par (up_tm_tm ξ0 i) (up_tm_tm ξ1 i).
Proof.
  case => [|i]; first by constructor.
  asimpl.
  by apply par_renaming.
Qed.

Lemma par_morphing a b (ξ0 ξ1 : fin -> tm)
  (h : forall i, Par (ξ0 i) (ξ1 i)) :
  Par a b ->
  Par (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof.
  move => h0.
  move : ξ0 ξ1 h.
  elim : a b / h0 => /=; eauto with par.
  - hauto lq:on db:par use:par_morphing_lift.
  - hauto lq:on db:par use:par_morphing_lift.
  - move => *; apply : P_AppAbs'; eauto; by asimpl.
Qed.

Lemma par_cong a0 a1 b0 b1 (h : Par a0 a1) (h1 : Par b0 b1) :
  Par (subst_tm (b0..) a0) (subst_tm (b1..) a1).
Proof.
  apply par_morphing; auto.
  case; auto.
  sfirstorder use:Par_refl.
Qed.

Lemma par_subst a0 a1 (h : Par a0 a1) (ξ : fin -> tm) :
  Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:Par_refl, par_morphing. Qed.

Lemma par_morphing_star a0 a1 (h : Rstar _ Par a0 a1) (ξ0 ξ1 : fin -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Rstar _ Par (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  induction h.
  - move => h. apply Rstar_contains_R. eauto using par_morphing, Par_refl.
  - move => h0.
    apply : Rstar_transitive; eauto.
    apply Rstar_contains_R.
    sfirstorder use:par_morphing, Par_refl.
Qed.

Lemma Par_join a b :
  Par a b -> Join a b.
Proof. sfirstorder use:Rstar_contains_R unfold:Join. Qed.

Lemma join_morphing a0 a1 (h : Join a0 a1) (ξ0 ξ1 : fin -> tm) :
  (forall i, Par (ξ0 i) (ξ1 i)) ->
  Join (subst_tm ξ0 a0) (subst_tm ξ1 a1).
Proof.
  hauto l:on unfold:Join,coherent use:par_morphing_star, Par_refl, Par_join.
Qed.

Lemma par_subst_star a0 a1 (h : Rstar _ Par a0 a1) (ξ : fin -> tm) :
  Rstar _ Par (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto l:on use:par_morphing_star, Par_refl. Qed.

Lemma join_subst_star a0 a1 (h : Join a0 a1) (ξ : fin -> tm) :
  Join (subst_tm ξ a0) (subst_tm ξ a1).
Proof. hauto lq:on use:join_morphing, Par_refl unfold:Join, coherent. Qed.

Derive Inversion Par_inv with (forall a b, Par a b).

Derive Inversion IEq_inv with (forall Ξ ℓ a b, IEq Ξ ℓ a b).

Derive Inversion GIEq_inv with (forall Ξ ℓ ℓ0 a b, GIEq Ξ ℓ ℓ0 a b).


Lemma par_confluent : Strongly_confluent _ Par.
Proof.
  rewrite /Strongly_confluent.
  move => a b b0 h.
  move : b0.
  elim : a b / h.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a0 a1 ℓ b0 b1 h0 ih0 h1 ih1 b2.
    elim /Par_inv => //.
    + qauto l:on ctrs:Par.
    + move => ? a2 ℓ0 A a3 b3 b4 ? ?.
      case => *; subst.
      case /(_ _ ltac:(eassumption)) : ih1 => b [? ?].
      case /(_ _ ltac:(eassumption)) : ih0 => a [? h2].
      elim /Par_inv : h2 => //.
      move => ? ℓ0 A0 A1 a2 a4 ? ?.
      case => *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on ctrs:Par use:par_cong.
  - move => a ℓ A a0 b0 b1 ? ih0 ? ih1 b2.
    elim /Par_inv => //.
    + move => h a1 a2 ℓ0 b3 b4 ? ? [*]; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 *].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? ℓ0 A0 A1 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par.
    + move => ? a1 ℓ0 A0 a2 b3 b4 ? ? [*] *; subst.
      case /(_ _ ltac:(eassumption)) : ih0 => a1 [h0 h1].
      case /(_ _ ltac:(eassumption)) : ih1 => b [*].
      elim /Par_inv : h0; try congruence.
      move => ? ℓ0 A1 A2 a3 a4 ? ? [*] *; subst.
      exists (subst_tm (b..) a4).
      hauto lq:on use:par_cong ctrs:Par inv:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a b0 b1 c0 c1 h0 ih0 h1 ih1 h2 ih2 b2.
    elim /Par_inv => //; hauto depth:3 lq:on rew:off inv:Par ctrs:Par.
  - move => a b0 b1 c0 c1 h0 ih0 h1 ih1 h2 ih2 b2.
    elim /Par_inv => //; hauto depth:3 lq:on rew:off inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
Qed.

Lemma pars_confluent : Confluent _ Par.
Proof.
  apply Strong_confluence.
  apply par_confluent.
Qed.

Lemma Join_reflexive a :
  Join a a.
Proof. hauto l:on ctrs:Rstar. Qed.

Lemma Join_symmetric a b :
  Join a b -> Join b a.
Proof. sfirstorder use:coherent_symmetric. Qed.

Lemma Join_transitive a b c :
  Join a b -> Join b c -> Join a c.
Proof.
  have := pars_confluent.
  rewrite /Confluent /confluent /Join /coherent => h [z0 [? h0]] [z1 [h1 ?]].
  move /(_ b _ _ h0 h1) in h.
  case : h => z [*].
  exists z. split; sfirstorder use:Rstar_transitive.
Qed.

Definition ieq_good_renaming ξ (Ξ Δ : econtext) :=
    (forall i, i < length Ξ -> eith Ξ i = eith Δ (ξ i)) /\
    (forall i, i < length Ξ -> ξ i < length Δ).

Lemma ieq_good_renaming_iff ξ (Ξ Δ : econtext) :
  ieq_good_renaming ξ Ξ Δ <->
    (forall i, i < length Ξ -> ξ i < length Δ /\ eith Ξ i = eith Δ (ξ i)).
Proof.
  sfirstorder.
Qed.

Definition ieq_weakening_helper : forall ℓ ξ (Ξ Δ : econtext),
    ieq_good_renaming ξ Ξ Δ ->
    ieq_good_renaming (upRen_tm_tm ξ) (ℓ :: Ξ) (ℓ :: Δ).
Proof.
  move => *.
  apply ieq_good_renaming_iff.
  case => /= [|i /Arith_prebase.lt_S_n].
  - sfirstorder.
  - move => *. asimpl.
    sfirstorder.
Qed.

Lemma ieq_weakening_mutual : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ξ Δ, ieq_good_renaming ξ Ξ Δ ->
            IEq Δ ℓ (ren_tm ξ a) (ren_tm ξ b)) /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall ξ Δ, ieq_good_renaming ξ Ξ Δ ->
            GIEq Δ ℓ ℓ0 (ren_tm ξ a) (ren_tm ξ b)).
Proof.
  apply IEq_mutual; qauto l: on ctrs:IEq,GIEq use:ieq_weakening_helper.
Qed.

Lemma gieq_refl n Ξ ℓ :
  n < length Ξ ->
  GIEq Ξ ℓ (eith Ξ n) (var_tm n) (var_tm n).
Proof.
  case E : ((eith Ξ n) <= ℓ)%O; hauto lq:on ctrs:GIEq, IEq.
Qed.

Definition ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ :=
  forall i, i < length Ξ -> GIEq Δ ℓ (eith Ξ i) (ξ0 i) (ξ1 i).

Lemma ieq_morphing_helper ℓ ℓ0 ξ0 ξ1 Ξ Δ :
  ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
  ieq_good_morphing ℓ (up_tm_tm ξ0) (up_tm_tm ξ1) (ℓ0 :: Ξ) (ℓ0 :: Δ).
Proof.
  rewrite /ieq_good_morphing => h.
  case => /= [_ | i /Arith_prebase.lt_S_n ?]; asimpl.
  - apply (gieq_refl 0 (ℓ0 :: Δ) ℓ); sfirstorder.
  - hauto l:on use:ieq_weakening_mutual.
Qed.

Lemma ieq_morphing_mutual : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            IEq Δ ℓ (subst_tm ξ0 a) (subst_tm ξ1 b)) /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            GIEq Δ ℓ ℓ0 (subst_tm ξ0 a) (subst_tm ξ1 b)).
Proof.
  apply IEq_mutual; try qauto ctrs:IEq,GIEq.
  - hauto lq: on inv: GIEq lqb:on unfold:ieq_good_morphing.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
Qed.

Lemma ieq_morphing Ξ ℓ a b : IEq Ξ ℓ a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            IEq Δ ℓ (subst_tm ξ0 a) (subst_tm ξ1 b).
Proof. hauto l:on use:ieq_morphing_mutual. Qed.

Lemma simulation : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall a', Par a a' ->
            exists b', Par b b' /\ IEq Ξ ℓ a' b') /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall a', Par a a' ->
            exists b', Par b b' /\ GIEq Ξ ℓ ℓ0 a' b').
Proof.
  apply IEq_mutual; try qauto ctrs:IEq, Par, GIEq inv:Par.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - move => Ξ ℓ a0 a1 ℓ0 b0 b1 h0 ih0 h1 ih1 a'.
    elim /Par_inv => //.
    + hauto lq:on ctrs:Par, IEq.
    + move => hp ? ? A a2 ? b2 h2 h3 [*]; subst.
      case /ih1 : h3 => b3 [h30 h31].
      case /ih0 : h2 => a3 [h40].
      elim /IEq_inv => // ? ? A0 A1 a4 a5 h5 [] *; subst.
      exists (subst_tm (b3..) a5).
      split.
      * hauto q:on ctrs:Par.
      * apply ieq_morphing with (Ξ := ℓ0 :: Ξ); eauto.
        case => /= [|n /Arith_prebase.lt_S_n ?]; first by asimpl.
        asimpl.
        by apply gieq_refl.
  - hauto lq:on ctrs:IEq, Par inv:Par, IEq.
  - hauto l:on ctrs:Par use:Par_refl.
Qed.

Lemma simulation_star Ξ ℓ a b a' (h : IEq Ξ ℓ a b) (h0 : Rstar _ Par a a') :
    exists b', Rstar _ Par b b' /\ IEq Ξ ℓ a' b'.
Proof.
  move : b h.
  elim : a a' / h0.
  - sfirstorder.
  - move => a a0 a1 ha ha0 ih b hab.
    suff : exists b0,Par b b0 /\ IEq Ξ ℓ a0 b0; hauto lq:on use:simulation ctrs:Rstar.
Qed.

Lemma ieq_downgrade_mutual Ξ ℓ :
  (forall a b, IEq Ξ ℓ a b ->
          forall ℓ0 c , (ℓ0 <= ℓ)%O ->
                   IEq Ξ ℓ0 a c ->
                   IEq Ξ ℓ0 a b) /\
  (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
          forall ℓ1 c, (ℓ1 <= ℓ)%O ->
                  GIEq Ξ ℓ1 ℓ0 a c ->
                  GIEq Ξ ℓ1 ℓ0 a b).
Proof.
  move : Ξ ℓ.
  apply IEq_mutual; try qauto l:on inv:IEq,GIEq ctrs:IEq,GIEq.
  - hauto lq:on inv:IEq,GIEq ctrs:IEq,GIEq.
  - move => Ξ ℓ ℓ0 A B h ℓ1 c hℓ hc.
    case E : (ℓ0 <= ℓ1)%O.
    + suff : (ℓ0 <= ℓ)%O by hauto lqb:on.
      hauto l:on use:Order.le_trans.
    + hauto lq:on ctrs:GIEq.
Qed.

Lemma ieq_downgrade_mutual' : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ℓ0 c , IEq Ξ ℓ0 a c ->
                     IEq Ξ (ℓ `&` ℓ0)%O a b) /\
      (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                 forall ℓ1 c, GIEq Ξ ℓ1 ℓ0 a c ->
                         GIEq Ξ (ℓ `&` ℓ1)%O ℓ0 a b).
Proof.
  apply IEq_mutual; try qauto l:on inv:IEq,GIEq ctrs:IEq,GIEq.
  (* Can be compressed if I can figure out how to make ssreflect
  lemmas usable by automation *)
  - move => Ξ ℓ i hi hℓ ℓ0 c h.
    inversion h; subst.
    constructor => //.
    rewrite lexI.
    sfirstorder brefl:on.
  - move => Ξ ℓ ℓ0 A B ? h ih ℓ1 C.
    elim /GIEq_inv => hc ℓ2 A0 B0 h2 h3 *; subst.
    + apply ih in h3.
      apply GI_Dist => //.
      rewrite lexI.
      sfirstorder brefl:on.
    + apply GI_InDist.
      move : h2.
      apply contraNN.
      rewrite lexI.
      sfirstorder b:on.
  - move => Ξ ℓ ℓ0 A B h ℓ1 C h2.
    apply GI_InDist.
    move : h.
    apply contraNN.
    rewrite lexI.
    sfirstorder b:on.
Qed.

Lemma ieq_trans_heterogeneous Ξ ℓ ℓ0 a b c :
  IEq Ξ ℓ a b ->
  IEq Ξ ℓ0 b c ->
  IEq Ξ (ℓ `&` ℓ0)%O a c.
Proof.
  move => h0 h1.
  apply ieq_trans with (B := b).
  - apply ieq_sym_mutual.
    apply ieq_sym_mutual in h0.
    eapply ieq_downgrade_mutual'; eauto.
  - apply ieq_sym_mutual in h0.
    rewrite meetC.
    eapply ieq_downgrade_mutual'; eauto.
Qed.
