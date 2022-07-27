(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
Require Reals.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import interval zmodp.
From mathcomp.classical Require Import boolp classical_sets.
Require Import ereal reals.
Require Import Rstruct signed topology normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(** For Pierre-Yves : definition of sums *)

From mathcomp Require fintype bigop finmap.

Section totally.

Import fintype bigop finmap.
Local Open Scope fset_scope.
(* :TODO: when eventually is generalized to any lattice *)
(* totally can just be replaced by eventually *)
Definition totally {I : choiceType} : set (set {fset I}) :=
  filter_from setT (fun A => [set B | A `<=` B]).

HB.instance Definition _ {I : choiceType} X :=
  IsSource.Build X _ {fset I} (fun f => f @ totally).

Instance totally_filter {I : choiceType} : ProperFilter (@totally I).
Proof.
eapply filter_from_proper; last by move=> A _; exists A; rewrite /= fsubset_refl.
apply: filter_fromT_filter; first by exists fset0.
by move=> A B /=; exists (A `|` B) => P /=; rewrite fsubUset => /andP[].
Qed.

Definition partial_sum {I : choiceType} {R : zmodType}
  (x : I -> R) (A : {fset I}) : R := \sum_(i : A) x (val i).

Definition sum (I : choiceType) {K : numDomainType} {R : normedModType K}
   (x : I -> R) : R := lim (partial_sum x).

Definition summable (I : choiceType) {K : realType} {R : normedModType K}
   (x : I -> R) :=
   \forall M \near +oo%R, \forall J \near totally,
   (partial_sum (fun i => `|x i|) J <= M)%R.

End totally.
