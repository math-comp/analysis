From HB Require Import structures.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect ssralg vector ring_quotient.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import finmap boolp functions classical_sets.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

HB.mixin Record isMultilinear (I : eqType) (R : pzSemiRingType)
    (V : I -> lSemiModType R) (W : lSemiModType R)
    (f : (forall i, V i) -> W) := {
  ilinear : forall i : I, forall v :(forall i, V i),
    linear (f \o (fun x : V i => dfwith v x))
}.
