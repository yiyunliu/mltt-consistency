Require Import conv par geq imports semtyping typing typing_conv normalform soundness preservation.

Module consistency
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import nf : normalform_sig lattice syntax par)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv)
  (Import lr : lr_sig lattice syntax par nf ieq conv).

Module soundness := soundness lattice syntax par nf ieq conv typing lr.
Module preservation := preservation lattice syntax par ieq conv typing.
Import soundness.
Import preservation.

Fixpoint debruijnDepth a : nat :=
  match a with
  | var_tm i => 1 + i
  | tAbs _ b => debruijnDepth b - 1
  | tApp a _ b => max (debruijnDepth a) (debruijnDepth b)
  | tPi _ A B => max (debruijnDepth A) (debruijnDepth B - 1)
  | tSig _ A B => max (debruijnDepth A) (debruijnDepth B - 1)
  | tUniv _ => 0
  | tEq _ a b A => max (debruijnDepth a) (max (debruijnDepth b) (debruijnDepth A))
  | tRefl => 0
  | tJ t p => max (debruijnDepth t - 2) (debruijnDepth p)
  | tD => 1
  | tVoid => 0
  | tLet _ _ a b => max (debruijnDepth a) (debruijnDepth b - 2)
  | tPack _ a b => max (debruijnDepth a) (debruijnDepth b)
  | tAbsurd a => debruijnDepth a
  end.

Lemma lookup_lt i Γ ℓ A : lookup i Γ ℓ A -> i < length Γ.
Proof. induction 1; sfirstorder. Qed.

Lemma wt_dbound Γ ℓ a A : Γ ⊢ a ; ℓ ∈ A -> debruijnDepth a <= length Γ.
Proof.
  move => h.
  elim : Γ ℓ a A / h => /=; try lia.
  hauto lq:on use:lookup_lt.
Qed.

Lemma ne_depth_gt0 a : ne a -> debruijnDepth a > 0.
  elim : a => //=; try lia; sfirstorder b:on.
Qed.

Lemma consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.
Proof.
  move => /[dup] h /(proj1 soundness) /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_nil)).
  move => [m][PA][].
  asimpl. move /InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]].
  move : subject_reduction_star h hr; repeat move/[apply].
  move /wt_dbound.
  move /ne_depth_gt0 : hv => /=. lia.
Qed.

End consistency.
