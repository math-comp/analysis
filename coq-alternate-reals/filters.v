(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Require Import boolp reals.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Local Open Scope real_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Record mixin_of (R : realType) (T : eqType) := Mixin {
  d : T -> T -> {ereal R};
  _ : forall x y, (0%:E <= d x y)%E;
  _ : forall x y, (d x y == 0%:E) = (x == y);
  _ : forall x y, d x y = d y x;
  _ : forall x y z, (d x z <= d x y + d y z)%E;
}.

Local Notation choice_for T b := (@Choice.Pack T b T).

Module PreMetricSpace.

Section ClassDef.

Variable (R : realType).

Record class_of T := Class {
  base  : Choice.class_of T;
  mixin : mixin_of R (choice_for T base)
}.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.

Local Coercion base : class_of >-> Choice.class_of.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class :=
  let: Pack _ c _  as cT' := cT return class_of cT' in c.

Let xT := let: Pack T _ _ := cT in T.
Local Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : mixin_of R (choice_for T b0)) :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
End ClassDef.

(* -------------------------------------------------------------------- *)
Module Exports.
Coercion base  : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort  : type >-> Sortclass.

Bind Scope ring_scope with sort.

Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.

Notation preMetricSpaceType := type.
Notation PreMetricSpaceMixin := Mixin.
Notation PreMetricType R T m := (@pack R T _ m _ _ id _ id).
Notation "[ 'preMetricSpaceType' 'of' T 'for' cT ]" := (@clone _ T cT _ idfun)
  (at level 0, format "[ 'preMetricSpaceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'preMetricSpaceType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'preMetricSpaceType'  'of'  T ]") : form_scope.
End Exports.

End PreMetricSpace.
Import PreMetricSpace.Exports.

(* -------------------------------------------------------------------- *)
