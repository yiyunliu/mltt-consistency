Require Import imports join.

(* -------------------------------------------------- *)
(* Parallel reduction preserves head forms. We use this
   to show that Coherent terms have the same head form.
*)

Inductive head := hPi | hNat | hUniv | hEq | hBot | hZero | hSuc | hSig | hPack.

Definition tm_to_head (a : tm) :=
  match a with
  | tPi A B => hPi
  | tAbs a => hBot
  | tNat => hNat
  | tZero => hZero
  | tSuc _ => hSuc
  | tInd a b c => hBot
  | tApp a b => hBot
  | tUniv _ => hUniv
  | var_tm _ => hBot
  | tEq _ _ _ => hEq
  | tRefl => hBot
  | tLet _ _ => hBot
  | tJ _ _ _ _ => hBot
  | tSig _ _ => hSig
  | tPack _ _ => hPack
  end.

Function hleq (a b : head) :=
  match a, b with
  | hBot , _ => true
  | hPi, hPi => true
  | hNat, hNat => true
  | hUniv, hUniv => true
  | hEq, hEq => true
  | hSuc, hSuc => true
  | hZero, hZero => true
  | hPack, hPack => true
  | hSig, hSig => true
  | _, _ => false
  end.

Notation "a \≤ b" := (hleq a b) (at level 80, no associativity).

Lemma hleq_refl a : a \≤ a.
Proof. elim : a=>//. Qed.

Lemma hleq_trans a b c : a \≤ b -> b \≤ c -> a \≤ c.
Proof. case : a; case : b; case : c => //. Qed.

Lemma hleq_antisym a b : a \≤ b -> b \≤ a -> a = b.
Proof. case : a; case : b =>//. Qed.

Lemma Par_head a b (h : a ⇒ b) :
  tm_to_head a \≤ tm_to_head b.
Proof. induction h => //. Qed.

Lemma Par_head_star a b (h : a ⇒* b) :
  tm_to_head a \≤ tm_to_head b.
Proof. induction h; eauto using Par_head, hleq_refl, hleq_trans.  Qed.

Lemma Sub1_consistent A B (h : Sub1 A B) :
  tm_to_head A = tm_to_head B.
Proof. elim : A B / h=>//. Qed.


Lemma Sub_consistent' a b (h : a <: b) :
  exists c, (tm_to_head a \≤ c) && (tm_to_head b \≤ c).
Proof. hauto lq:on use:Par_head_star, Sub1_consistent b:on unfold:Sub. Qed.

Lemma Sub_consistent_helper a b :
  (exists c, (a \≤ c) && (b \≤ c)) -> (a \≤ b) || (b \≤ a).
Proof. case : a ; case : b; hauto lq:on rew:off. Qed.

Lemma Sub_consistent a b (h : a <: b) :
  (tm_to_head a \≤ tm_to_head b) || (tm_to_head b \≤ tm_to_head a).
Proof. auto using Sub_consistent', Sub_consistent_helper. Qed.

Lemma Coherent_consistent : forall a b,
  Coherent a b -> (tm_to_head a \≤ tm_to_head b) || (tm_to_head b \≤ tm_to_head a).
Proof. hauto lq:on use:Sub_consistent, Coherent_Sub. Qed.
