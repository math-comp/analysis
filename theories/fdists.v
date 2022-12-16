From mathcomp Require Import all_ssreflect all_algebra vector reals normedtype.
From mathcomp Require Import classical_sets boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.
(* on the model of infotheo *)
Module FDist.
Section fdist.
Variables (R : numDomainType) (A : finType).
Local Open Scope ring_scope.
Record t := mk {
  f :> A -> R ;
  _ : [forall a, 0 <= f a] && (\sum_(a in A) f a == 1) }.
Lemma ge0 (d : t) a : 0 <= d a.
Proof. by case: d => ? /= /andP[/forallP ]. Qed.
Lemma f1 (d : t) : \sum_(a in A) d a = 1.
Proof. by case: d => ? /= /andP[? /eqP]. Qed.
Program Definition make (f : {ffun A -> R}) (H0 : forall a, 0 <= f a)
  (H1 : \sum_(a in A) f a = 1) := @mk f _.
Next Obligation.
by move=> f f0 f1; apply/andP; split; [exact/forallP|exact/eqP].
Qed.
End fdist.
Module Exports.
Notation fdist := t.
End Exports.
End FDist.
Export FDist.Exports.
Coercion FDist.f : fdist >-> Funclass.
Canonical fdist_subType R A := Eval hnf in [subType for @FDist.f R A].
Definition fdist_eqMixin R A := [eqMixin of fdist R A by <:].
Canonical fdist_eqType R A := Eval hnf in EqType _ (fdist_eqMixin R A).

Definition fdist_of (R : numDomainType) (A : finType) := fun phT : phant (Finite.sort A) => fdist R A.
Notation "{ 'fdist' T }" := (fdist_of _ (Phant T)).
