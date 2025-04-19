Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | tAbs : tm -> tm
  | tApp : tm -> tm -> tm
  | tPi : tm -> tm -> tm
  | tUniv : nat -> tm
  | tEq : tm -> tm -> tm -> tm
  | tJ : tm -> tm -> tm -> tm -> tm
  | tRefl : tm
  | tZero : tm
  | tSuc : tm -> tm
  | tInd : tm -> tm -> tm -> tm
  | tNat : tm
  | tSig : tm -> tm -> tm
  | tPack : tm -> tm -> tm
  | tLet : tm -> tm -> tm.

Lemma congr_tAbs {s0 : tm} {t0 : tm} (H0 : s0 = t0) : tAbs s0 = tAbs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tAbs x) H0)).
Qed.

Lemma congr_tApp {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tApp s0 s1 = tApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tApp x s1) H0))
         (ap (fun x => tApp t0 x) H1)).
Qed.

Lemma congr_tPi {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tPi s0 s1 = tPi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tPi x s1) H0))
         (ap (fun x => tPi t0 x) H1)).
Qed.

Lemma congr_tUniv {s0 : nat} {t0 : nat} (H0 : s0 = t0) : tUniv s0 = tUniv t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tUniv x) H0)).
Qed.

Lemma congr_tEq {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : tEq s0 s1 s2 = tEq t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tEq x s1 s2) H0))
            (ap (fun x => tEq t0 x s2) H1)) (ap (fun x => tEq t0 t1 x) H2)).
Qed.

Lemma congr_tJ {s0 : tm} {s1 : tm} {s2 : tm} {s3 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : tJ s0 s1 s2 s3 = tJ t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => tJ x s1 s2 s3) H0))
               (ap (fun x => tJ t0 x s2 s3) H1))
            (ap (fun x => tJ t0 t1 x s3) H2))
         (ap (fun x => tJ t0 t1 t2 x) H3)).
Qed.

Lemma congr_tRefl : tRefl = tRefl.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tZero : tZero = tZero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSuc {s0 : tm} {t0 : tm} (H0 : s0 = t0) : tSuc s0 = tSuc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tSuc x) H0)).
Qed.

Lemma congr_tInd {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tInd s0 s1 s2 = tInd t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tInd x s1 s2) H0))
            (ap (fun x => tInd t0 x s2) H1)) (ap (fun x => tInd t0 t1 x) H2)).
Qed.

Lemma congr_tNat : tNat = tNat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSig {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tSig s0 s1 = tSig t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tSig x s1) H0))
         (ap (fun x => tSig t0 x) H1)).
Qed.

Lemma congr_tPack {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tPack s0 s1 = tPack t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tPack x s1) H0))
         (ap (fun x => tPack t0 x) H1)).
Qed.

Lemma congr_tLet {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tLet s0 s1 = tLet t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tLet x s1) H0))
         (ap (fun x => tLet t0 x) H1)).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | tAbs s0 => tAbs (ren_tm (upRen_tm_tm xi_tm) s0)
  | tApp s0 s1 => tApp (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | tPi s0 s1 => tPi (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | tUniv s0 => tUniv s0
  | tEq s0 s1 s2 => tEq (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tJ s0 s1 s2 s3 =>
      tJ (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
        (ren_tm xi_tm s3)
  | tRefl => tRefl
  | tZero => tZero
  | tSuc s0 => tSuc (ren_tm xi_tm s0)
  | tInd s0 s1 s2 =>
      tInd (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm (upRen_tm_tm xi_tm)) s1)
        (ren_tm xi_tm s2)
  | tNat => tNat
  | tSig s0 s1 => tSig (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | tPack s0 s1 => tPack (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | tLet s0 s1 =>
      tLet (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm (upRen_tm_tm xi_tm)) s1)
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | tAbs s0 => tAbs (subst_tm (up_tm_tm sigma_tm) s0)
  | tApp s0 s1 => tApp (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | tPi s0 s1 => tPi (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | tUniv s0 => tUniv s0
  | tEq s0 s1 s2 =>
      tEq (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  | tJ s0 s1 s2 s3 =>
      tJ (subst_tm sigma_tm s0) (subst_tm sigma_tm s1) (subst_tm sigma_tm s2)
        (subst_tm sigma_tm s3)
  | tRefl => tRefl
  | tZero => tZero
  | tSuc s0 => tSuc (subst_tm sigma_tm s0)
  | tInd s0 s1 s2 =>
      tInd (subst_tm sigma_tm s0)
        (subst_tm (up_tm_tm (up_tm_tm sigma_tm)) s1) (subst_tm sigma_tm s2)
  | tNat => tNat
  | tSig s0 s1 =>
      tSig (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | tPack s0 s1 => tPack (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | tLet s0 s1 =>
      tLet (subst_tm sigma_tm s0)
        (subst_tm (up_tm_tm (up_tm_tm sigma_tm)) s1)
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2) (idSubst_tm sigma_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (idSubst_tm sigma_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s1)
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | tAbs s0 =>
      congr_tAbs
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
        (extRen_tm xi_tm zeta_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s1)
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  | tApp s0 s1 =>
      congr_tApp (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
        (ext_tm sigma_tm tau_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (ext_tm sigma_tm tau_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm (up_tm_tm sigma_tm)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | tPack s0 s1 =>
      congr_tPack (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm (up_tm_tm sigma_tm)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s1)
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | tAbs s0 =>
      congr_tAbs
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_tm (upRen_tm_tm rho_tm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_tm (upRen_tm_tm rho_tm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s1)
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s1)
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 =>
      congr_tSuc (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eq_tm)) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eq_tm)) s1)
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 =>
      congr_tSuc (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eq_tm)) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eq_tm)) s1)
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 =>
      congr_tAbs
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  | tApp s0 s1 =>
      congr_tApp (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | tPi s0 s1 =>
      congr_tPi (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tEq s0 s1 s2 =>
      congr_tEq (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tJ s0 s1 s2 s3 =>
      congr_tJ (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
  | tRefl => congr_tRefl
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | tInd s0 s1 s2 =>
      congr_tInd (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tNat => congr_tNat
  | tSig s0 s1 =>
      congr_tSig (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | tPack s0 s1 =>
      congr_tPack (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | tLet s0 s1 =>
      congr_tLet (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s1)
  end.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_tm) (subst_tm (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise : pointwise_relation _ eq (subst_tm (var_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

#[global] Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

#[global] Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[global] Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

#[global]
Instance VarInstance_tm : (Var _ _) := @var_tm.

Notation "[ sigma_tm ]" := (subst_tm sigma_tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.

#[global]
Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

