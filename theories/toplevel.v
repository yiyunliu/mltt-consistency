Require Import conv par geq imports normalform semtyping typing soundness preservation consistency.

Module MkAll
  (Import lattice : Lattice).

  Module syntax <: syntax_sig lattice.
    Include syntax_sig lattice.
  End syntax.

  Module par <: par_sig lattice syntax.
    Include par_sig lattice syntax.
  End par.

  Module ieq <: geq_sig lattice syntax.
    Include geq_sig lattice syntax.
  End ieq.

  Module conv <: conv_sig lattice syntax par ieq.
    Include conv_sig lattice syntax par ieq.
  End conv.

  Module typing <: typing_sig lattice syntax par ieq conv.
    Include typing_sig lattice syntax par ieq conv.
  End typing.

  Module nf <: normalform_sig lattice syntax par.
    Include normalform_sig lattice syntax par.
  End nf.

  Module lr <: lr_sig lattice syntax par nf ieq conv.
    Include lr_sig lattice syntax par nf ieq conv.
  End lr.

  Module soundness := soundness lattice syntax par nf ieq conv typing lr.

  Module preservation := preservation lattice syntax par ieq conv typing.

  Module consistency := consistency lattice syntax par nf ieq conv typing lr.
End MkAll.

Module nat_lattice <: Lattice.

  Definition T := nat.
  Definition meet := min.
  Definition join := max.
  Local Infix "∪" := join (at level 65).
  Local Infix "∩" := meet (at level 60).
  Definition T_eqb := PeanoNat.Nat.eqb.
  Lemma meet_commutative : forall a b, a ∩ b = b ∩ a.
    rewrite /meet /join; lia.
  Qed.

  Lemma meet_associative : forall a b c, (a ∩ b) ∩ c = a ∩ (b ∩ c).
    rewrite /meet /join; lia.
  Qed.
  Lemma meet_absorptive : forall a b, a ∩ (a ∪ b) = a.
    rewrite /meet /join; lia.
  Qed.
  Lemma meet_idempotent : forall a, a ∩ a = a.
    rewrite /meet /join; lia.
  Qed.
  Lemma join_commutative : forall a b, a ∪ b = b ∪ a.
    rewrite /meet /join; lia.
  Qed.
  Lemma join_associative: forall a b c, (a ∪ b) ∪ c = a ∪ (b ∪ c).
    rewrite /meet /join; lia.
  Qed.
  Lemma join_absorptive : forall a b, a ∪ (a ∩ b) = a.
    rewrite /meet /join; lia.
  Qed.
  Lemma join_idempotent : forall a, a ∪ a = a.
    rewrite /meet /join; lia.
  Qed.
  Lemma T_eqdec : forall a b, Bool.reflect (a = b) (T_eqb a b).
    move => a b.
    rewrite /T_eqb.
    case E : (PeanoNat.Nat.eqb a b).
    - apply PeanoNat.Nat.eqb_eq in E. hauto l:on.
    - constructor.
      move => h.
      apply PeanoNat.Nat.eqb_eq in h. sfirstorder.
  Qed.
End nat_lattice.

Module dcoi_with_nat_lattice := MkAll nat_lattice.

Check dcoi_with_nat_lattice.consistency.consistency.
Print Assumptions dcoi_with_nat_lattice.consistency.consistency.
Check dcoi_with_nat_lattice.preservation.subject_reduction.
Print Assumptions dcoi_with_nat_lattice.preservation.subject_reduction.
Check dcoi_with_nat_lattice.soundness.normalization.
Print Assumptions dcoi_with_nat_lattice.soundness.normalization.
