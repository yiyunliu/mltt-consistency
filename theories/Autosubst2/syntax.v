Require Export Lattice.All.
Require Export unscoped.

Module Type syntax_sig
  (Export lattice : Lattice).





Section tm.
Inductive tm  : Type :=
  | var_tm : ( fin ) -> tm 
  | tAbs : ( T   ) -> ( tm   ) -> tm 
  | tApp : ( tm   ) -> ( T   ) -> ( tm   ) -> tm 
  | tPi : ( T   ) -> ( tm   ) -> ( tm   ) -> tm 
  | tUniv : ( nat   ) -> tm 
  | tVoid : tm 
  | tAbsurd : ( tm   ) -> tm 
  | tEq : ( T   ) -> ( tm   ) -> ( tm   ) -> ( tm   ) -> tm 
  | tJ : ( tm   ) -> ( tm   ) -> tm 
  | tRefl : tm 
  | tSig : ( T   ) -> ( tm   ) -> ( tm   ) -> tm 
  | tPack : ( T   ) -> ( tm   ) -> ( tm   ) -> tm 
  | tLet : ( T   ) -> ( T   ) -> ( tm   ) -> ( tm   ) -> tm 
  | tD : tm .

Lemma congr_tAbs  { s0 : T   } { s1 : tm   } { t0 : T   } { t1 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) : tAbs  s0 s1 = tAbs  t0 t1 .
Proof. congruence. Qed.

Lemma congr_tApp  { s0 : tm   } { s1 : T   } { s2 : tm   } { t0 : tm   } { t1 : T   } { t2 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : tApp  s0 s1 s2 = tApp  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_tPi  { s0 : T   } { s1 : tm   } { s2 : tm   } { t0 : T   } { t1 : tm   } { t2 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : tPi  s0 s1 s2 = tPi  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_tUniv  { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : tUniv  s0 = tUniv  t0 .
Proof. congruence. Qed.

Lemma congr_tVoid  : tVoid  = tVoid  .
Proof. congruence. Qed.

Lemma congr_tAbsurd  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : tAbsurd  s0 = tAbsurd  t0 .
Proof. congruence. Qed.

Lemma congr_tEq  { s0 : T   } { s1 : tm   } { s2 : tm   } { s3 : tm   } { t0 : T   } { t1 : tm   } { t2 : tm   } { t3 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : tEq  s0 s1 s2 s3 = tEq  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_tJ  { s0 : tm   } { s1 : tm   } { t0 : tm   } { t1 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) : tJ  s0 s1 = tJ  t0 t1 .
Proof. congruence. Qed.

Lemma congr_tRefl  : tRefl  = tRefl  .
Proof. congruence. Qed.

Lemma congr_tSig  { s0 : T   } { s1 : tm   } { s2 : tm   } { t0 : T   } { t1 : tm   } { t2 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : tSig  s0 s1 s2 = tSig  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_tPack  { s0 : T   } { s1 : tm   } { s2 : tm   } { t0 : T   } { t1 : tm   } { t2 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : tPack  s0 s1 s2 = tPack  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_tLet  { s0 : T   } { s1 : T   } { s2 : tm   } { s3 : tm   } { t0 : T   } { t1 : T   } { t2 : tm   } { t3 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : tLet  s0 s1 s2 s3 = tLet  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_tD  : tD  = tD  .
Proof. congruence. Qed.

Definition upRen_tm_tm   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_tm   (xitm : ( fin ) -> fin) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => (var_tm ) (xitm s)
    | tAbs  s0 s1 => tAbs  ((fun x => x) s0) ((ren_tm (upRen_tm_tm xitm)) s1)
    | tApp  s0 s1 s2 => tApp  ((ren_tm xitm) s0) ((fun x => x) s1) ((ren_tm xitm) s2)
    | tPi  s0 s1 s2 => tPi  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm (upRen_tm_tm xitm)) s2)
    | tUniv  s0 => tUniv  ((fun x => x) s0)
    | tVoid   => tVoid 
    | tAbsurd  s0 => tAbsurd  ((ren_tm xitm) s0)
    | tEq  s0 s1 s2 s3 => tEq  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2) ((ren_tm xitm) s3)
    | tJ  s0 s1 => tJ  ((ren_tm xitm) s0) ((ren_tm xitm) s1)
    | tRefl   => tRefl 
    | tSig  s0 s1 s2 => tSig  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm (upRen_tm_tm xitm)) s2)
    | tPack  s0 s1 s2 => tPack  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2)
    | tLet  s0 s1 s2 s3 => tLet  ((fun x => x) s0) ((fun x => x) s1) ((ren_tm xitm) s2) ((ren_tm (upRen_tm_tm (upRen_tm_tm xitm))) s3)
    | tD   => tD 
    end.

Definition up_tm_tm   (sigma : ( fin ) -> tm ) : ( fin ) -> tm  :=
  (scons) ((var_tm ) (var_zero)) ((funcomp) (ren_tm (shift)) sigma).

Fixpoint subst_tm   (sigmatm : ( fin ) -> tm ) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => sigmatm s
    | tAbs  s0 s1 => tAbs  ((fun x => x) s0) ((subst_tm (up_tm_tm sigmatm)) s1)
    | tApp  s0 s1 s2 => tApp  ((subst_tm sigmatm) s0) ((fun x => x) s1) ((subst_tm sigmatm) s2)
    | tPi  s0 s1 s2 => tPi  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm (up_tm_tm sigmatm)) s2)
    | tUniv  s0 => tUniv  ((fun x => x) s0)
    | tVoid   => tVoid 
    | tAbsurd  s0 => tAbsurd  ((subst_tm sigmatm) s0)
    | tEq  s0 s1 s2 s3 => tEq  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2) ((subst_tm sigmatm) s3)
    | tJ  s0 s1 => tJ  ((subst_tm sigmatm) s0) ((subst_tm sigmatm) s1)
    | tRefl   => tRefl 
    | tSig  s0 s1 s2 => tSig  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm (up_tm_tm sigmatm)) s2)
    | tPack  s0 s1 s2 => tPack  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2)
    | tLet  s0 s1 s2 s3 => tLet  ((fun x => x) s0) ((fun x => x) s1) ((subst_tm sigmatm) s2) ((subst_tm (up_tm_tm (up_tm_tm sigmatm))) s3)
    | tD   => tD 
    end.

Definition upId_tm_tm  (sigma : ( fin ) -> tm ) (Eq : forall x, sigma x = (var_tm ) x) : forall x, (up_tm_tm sigma) x = (var_tm ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_tm  (sigmatm : ( fin ) -> tm ) (Eqtm : forall x, sigmatm x = (var_tm ) x) (s : tm ) : subst_tm sigmatm s = s :=
    match s return subst_tm sigmatm s = s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((idSubst_tm sigmatm Eqtm) s0) eq_refl ((idSubst_tm sigmatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((idSubst_tm sigmatm Eqtm) s1) ((idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((idSubst_tm sigmatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((idSubst_tm sigmatm Eqtm) s1) ((idSubst_tm sigmatm Eqtm) s2) ((idSubst_tm sigmatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_tm sigmatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((idSubst_tm sigmatm Eqtm) s1) ((idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((idSubst_tm sigmatm Eqtm) s1) ((idSubst_tm sigmatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((idSubst_tm sigmatm Eqtm) s2) ((idSubst_tm (up_tm_tm (up_tm_tm sigmatm)) (upId_tm_tm (_) (upId_tm_tm (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition upExtRen_tm_tm   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_tm   (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (Eqtm : forall x, xitm x = zetatm x) (s : tm ) : ren_tm xitm s = ren_tm zetatm s :=
    match s return ren_tm xitm s = ren_tm zetatm s with
    | var_tm  s => (ap) (var_tm ) (Eqtm s)
    | tAbs  s0 s1 => congr_tAbs eq_refl ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((extRen_tm xitm zetatm Eqtm) s0) eq_refl ((extRen_tm xitm zetatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((extRen_tm xitm zetatm Eqtm) s1) ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((extRen_tm xitm zetatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((extRen_tm xitm zetatm Eqtm) s1) ((extRen_tm xitm zetatm Eqtm) s2) ((extRen_tm xitm zetatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_tm xitm zetatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((extRen_tm xitm zetatm Eqtm) s1) ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((extRen_tm xitm zetatm Eqtm) s1) ((extRen_tm xitm zetatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((extRen_tm xitm zetatm Eqtm) s2) ((extRen_tm (upRen_tm_tm (upRen_tm_tm xitm)) (upRen_tm_tm (upRen_tm_tm zetatm)) (upExtRen_tm_tm (_) (_) (upExtRen_tm_tm (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition upExt_tm_tm   (sigma : ( fin ) -> tm ) (tau : ( fin ) -> tm ) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_tm   (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (Eqtm : forall x, sigmatm x = tautm x) (s : tm ) : subst_tm sigmatm s = subst_tm tautm s :=
    match s return subst_tm sigmatm s = subst_tm tautm s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((ext_tm sigmatm tautm Eqtm) s0) eq_refl ((ext_tm sigmatm tautm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((ext_tm sigmatm tautm Eqtm) s1) ((ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((ext_tm sigmatm tautm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((ext_tm sigmatm tautm Eqtm) s1) ((ext_tm sigmatm tautm Eqtm) s2) ((ext_tm sigmatm tautm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((ext_tm sigmatm tautm Eqtm) s0) ((ext_tm sigmatm tautm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((ext_tm sigmatm tautm Eqtm) s1) ((ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((ext_tm sigmatm tautm Eqtm) s1) ((ext_tm sigmatm tautm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((ext_tm sigmatm tautm Eqtm) s2) ((ext_tm (up_tm_tm (up_tm_tm sigmatm)) (up_tm_tm (up_tm_tm tautm)) (upExt_tm_tm (_) (_) (upExt_tm_tm (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition up_ren_ren_tm_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (rhotm : ( fin ) -> fin) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm ) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s return ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s with
    | var_tm  s => (ap) (var_tm ) (Eqtm s)
    | tAbs  s0 s1 => congr_tAbs eq_refl ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s1) ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((compRenRen_tm xitm zetatm rhotm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s1) ((compRenRen_tm xitm zetatm rhotm Eqtm) s2) ((compRenRen_tm xitm zetatm rhotm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_tm xitm zetatm rhotm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s1) ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s1) ((compRenRen_tm xitm zetatm rhotm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((compRenRen_tm xitm zetatm rhotm Eqtm) s2) ((compRenRen_tm (upRen_tm_tm (upRen_tm_tm xitm)) (upRen_tm_tm (upRen_tm_tm zetatm)) (upRen_tm_tm (upRen_tm_tm rhotm)) (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition up_ren_subst_tm_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm ) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s1) ((compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((compRenSubst_tm xitm tautm thetatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s1) ((compRenSubst_tm xitm tautm thetatm Eqtm) s2) ((compRenSubst_tm xitm tautm thetatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_tm xitm tautm thetatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s1) ((compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s1) ((compRenSubst_tm xitm tautm thetatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((compRenSubst_tm xitm tautm thetatm Eqtm) s2) ((compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xitm)) (up_tm_tm (up_tm_tm tautm)) (up_tm_tm (up_tm_tm thetatm)) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_tm_tm (_) (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition up_subst_ren_tm_tm    (sigma : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_tm (shift) (upRen_tm_tm zetatm) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm ) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((compSubstRen_tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1) ((compSubstRen_tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s2) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1) ((compSubstRen_tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s2) ((compSubstRen_tm (up_tm_tm (up_tm_tm sigmatm)) (upRen_tm_tm (upRen_tm_tm zetatm)) (up_tm_tm (up_tm_tm thetatm)) (up_subst_ren_tm_tm (_) (_) (_) (up_subst_ren_tm_tm (_) (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition up_subst_subst_tm_tm    (sigma : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_tm (shift) (up_tm_tm tautm) ((funcomp) (up_tm_tm tautm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift) ((funcomp) (ren_tm (shift)) tautm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (s : tm ) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1) ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s2) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1) ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s2) ((compSubstSubst_tm (up_tm_tm (up_tm_tm sigmatm)) (up_tm_tm (up_tm_tm tautm)) (up_tm_tm (up_tm_tm thetatm)) (up_subst_subst_tm_tm (_) (_) (_) (up_subst_subst_tm_tm (_) (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Definition rinstInst_up_tm_tm   (xi : ( fin ) -> fin) (sigma : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (var_tm ) xi) x = sigma x) : forall x, ((funcomp) (var_tm ) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_tm   (xitm : ( fin ) -> fin) (sigmatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (var_tm ) xitm) x = sigmatm x) (s : tm ) : ren_tm xitm s = subst_tm sigmatm s :=
    match s return ren_tm xitm s = subst_tm sigmatm s with
    | var_tm  s => Eqtm s
    | tAbs  s0 s1 => congr_tAbs eq_refl ((rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm)) s1)
    | tApp  s0 s1 s2 => congr_tApp ((rinst_inst_tm xitm sigmatm Eqtm) s0) eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s2)
    | tPi  s0 s1 s2 => congr_tPi eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s1) ((rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm)) s2)
    | tUniv  s0 => congr_tUniv eq_refl
    | tVoid   => congr_tVoid 
    | tAbsurd  s0 => congr_tAbsurd ((rinst_inst_tm xitm sigmatm Eqtm) s0)
    | tEq  s0 s1 s2 s3 => congr_tEq eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s1) ((rinst_inst_tm xitm sigmatm Eqtm) s2) ((rinst_inst_tm xitm sigmatm Eqtm) s3)
    | tJ  s0 s1 => congr_tJ ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_tm xitm sigmatm Eqtm) s1)
    | tRefl   => congr_tRefl 
    | tSig  s0 s1 s2 => congr_tSig eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s1) ((rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm)) s2)
    | tPack  s0 s1 s2 => congr_tPack eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s1) ((rinst_inst_tm xitm sigmatm Eqtm) s2)
    | tLet  s0 s1 s2 s3 => congr_tLet eq_refl eq_refl ((rinst_inst_tm xitm sigmatm Eqtm) s2) ((rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xitm)) (up_tm_tm (up_tm_tm sigmatm)) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_tm_tm (_) (_) Eqtm))) s3)
    | tD   => congr_tD 
    end.

Lemma rinstInst_tm   (xitm : ( fin ) -> fin) : ren_tm xitm = subst_tm ((funcomp) (var_tm ) xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm  : subst_tm (var_tm ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm  : @ren_tm   (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_))) instId_tm). Qed.

Lemma varL_tm   (sigmatm : ( fin ) -> tm ) : (funcomp) (subst_tm sigmatm) (var_tm ) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm   (xitm : ( fin ) -> fin) : (funcomp) (ren_tm xitm) (var_tm ) = (funcomp) (var_tm ) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (s : tm ) : subst_tm tautm (subst_tm sigmatm s) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmatm tautm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) : (funcomp) (subst_tm tautm) (subst_tm sigmatm) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm tautm n)). Qed.

Lemma compRen_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (s : tm ) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) s .
Proof. exact (compSubstRen_tm sigmatm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) : (funcomp) (ren_tm zetatm) (subst_tm sigmatm) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm zetatm n)). Qed.

Lemma renComp_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (s : tm ) : subst_tm tautm (ren_tm xitm s) = subst_tm ((funcomp) tautm xitm) s .
Proof. exact (compRenSubst_tm xitm tautm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) : (funcomp) (subst_tm tautm) (ren_tm xitm) = subst_tm ((funcomp) tautm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm tautm n)). Qed.

Lemma renRen_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (s : tm ) : ren_tm zetatm (ren_tm xitm s) = ren_tm ((funcomp) zetatm xitm) s .
Proof. exact (compRenRen_tm xitm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) : (funcomp) (ren_tm zetatm) (ren_tm xitm) = ren_tm ((funcomp) zetatm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm zetatm n)). Qed.

End tm.





























Global Instance Subst_tm   : Subst1 (( fin ) -> tm ) (tm ) (tm ) := @subst_tm   .

Global Instance Ren_tm   : Ren1 (( fin ) -> fin) (tm ) (tm ) := @ren_tm   .

Global Instance VarInstance_tm  : Var (fin) (tm ) := @var_tm  .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : ( X ) -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm   : Up_tm (_) (_) := @up_tm_tm   .

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_tm_tm, up_tm_tm)| progress (cbn [subst_tm ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_tm_tm, up_tm_tm in *)| progress (cbn [subst_tm ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).


Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope.

End syntax_sig.
