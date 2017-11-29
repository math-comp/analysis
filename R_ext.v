(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
From mathcomp Require Import ssreflect ssrbool.
Require Import Reals.

Local Open Scope R_scope.

(** Automatic inference of some positivity conditions *)
Hint Resolve cond_pos.

Canonical IZRpos_posreal (n : positive) :=
  mkposreal (IZR (Zpos n)) (IZR_lt _ _ (Pos2Z.is_pos _)).

Lemma Rmin_positive (x : posreal) (y : posreal) : Rmin x y > 0.
Proof. exact: Rmin_pos. Qed.
Canonical Rmin_posreal (x : posreal) (y : posreal) :=
  mkposreal (Rmin x y) (@Rmin_positive x y).

Lemma Rplus_positive (x : posreal) (y : posreal) : 0 < x + y.
Proof. exact: Rplus_lt_0_compat. Qed.
Canonical Rplus_posreal (x : posreal) (y : posreal) :=
  mkposreal (x + y) (Rplus_positive x y).

Lemma Rmult_positive (x : posreal) (y : posreal) : 0 < x * y.
Proof. exact: Rmult_lt_0_compat. Qed.
Canonical Rmult_posreal (x : posreal) (y : posreal) :=
  mkposreal (x * y) (Rmult_positive x y).

Lemma Rinv_positive (x : posreal) : 0 < /x.
Proof. exact: Rinv_0_lt_compat. Qed.
Canonical Rinv_posreal (x : posreal) := mkposreal (/ x) (Rinv_positive x).

Lemma Rdiv_positive (x : posreal) (y : posreal) : 0 < x / y.
Proof. by rewrite /Rdiv. Qed.
Canonical Rdiv_posreal (x : posreal) (y : posreal) :=
  mkposreal (x / y) (Rdiv_positive x y).

Definition positive_of (x : R) (y : posreal) of x = y := y.
Notation "[ 'posreal' 'of' x ]" := (positive_of x _ eq_refl)
  (format "[ 'posreal'  'of'  x ]") : R_scope.

Require Import Rbar.

Notation "'+oo'" := p_infty : R_scope.
Notation "'-oo'" := m_infty : R_scope.
