(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg ssrnum ssrint rat.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Ltac done := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope    with RR.
Delimit Scope realset_scope with Rset.

Local Open Scope real_scope.
Local Open Scope ring_scope.
(* -------------------------------------------------------------------- *)
Module Real.

Section Mixin.

Variable (R : archiFieldType).
Variable (Rsup : (R -> Prop) -> R).

Local Notation "{ x | P }" := (fun x : R => P : Prop) : realset_scope.

(* Real set non-emptyness. *)

Definition nonempty (E :  R -> Prop) :=
  exists x : R, E x.

(* Real upper bound set. *)
Definition ub  (E : R -> Prop) : R -> Prop :=
  { z | forall y : R, E y -> y <= z }%Rset.
(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down  (E : R -> Prop) : R -> Prop :=
  { x | exists2 y : R, E y & x <= y }%Rset.

Set Printing All.

(* Real set supremum existence condition. *)
Definition has_ub (E : R -> Prop) := nonempty (ub E).
Definition has_sup (E : R -> Prop) :=
  nonempty E /\ has_ub E.


Record mixin_of : Type := Mixin {
  sup : (R -> Prop) -> R;
   _  : forall E :  Num.ArchimedeanField.sort R -> Prop, has_sup E -> ub E (sup E);
   _  :
    forall (E :  Num.ArchimedeanField.sort R -> Prop) (eps : R), has_sup E -> 0 < eps ->
      exists2 e : R, E e & (sup E - eps) < e
}.

End Mixin.

Definition EtaMixin R sup sup_upper_bound sup_adherent :=
  let _ := @Mixin R sup sup_upper_bound sup_adherent in
  @Mixin (Num.ArchimedeanField.Pack (Num.ArchimedeanField.class R) R)
         sup sup_upper_bound sup_adherent.


Global Arguments ub      {R}%type _%realset_scope _%real_scope.
Global Arguments has_ub  {R}%type _%realset_scope.
Global Arguments has_sup {R}%type _%realset_scope.
Global Arguments down    {R}%type _%realset_scope _%real_scope.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Num.ArchimedeanField.class_of R;
  mixin : mixin_of (Num.ArchimedeanField.Pack base R)
}.

Local Coercion base : class_of >-> Num.ArchimedeanField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Num.ArchimedeanField.Pack T b0 T)) :=
  fun bT b & phant_id (Num.ArchimedeanField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition join_numDomainType := @Num.NumDomain.Pack fieldType xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition join_realDomainType := @Num.RealDomain.Pack numFieldType xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archimedeanFieldType := @Num.ArchimedeanField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.ArchimedeanField.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Canonical join_numDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Coercion archimedeanFieldType : type >-> Num.ArchimedeanField.type.
Canonical archimedeanFieldType.

Notation realType := type.
Notation RealType T m := (@pack T _ m _ _ id _ id).
Notation RealMixin := EtaMixin.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.

End Exports.

End Real.
Import Real.Exports.

(* -------------------------------------------------------------------- *)
Definition sup {R : realType} : (R -> Prop) -> R := Real.sup (Real.class R).

Definition nonempty {R : realType} := @Real.nonempty R.
Definition ub {R : realType} := @Real.ub R.
Definition down  {R : realType} := @Real.down R.
Definition has_ub  {R : realType} := @Real.has_ub R.
Definition has_sup  {R : realType} := @Real.has_sup R.

Lemma sup_upper_bound {R : realType} (E : Real.sort R -> Prop) :
  has_sup E -> ub E (sup E).
Proof. (* does not work *) Admitted.
(* -------------------------------------------------------------------- *)
Section RealDerivedOps.

Variable R : realType.

Local Notation "{ x | P }" := (fun x : R => P : Prop) : realset_scope.

Definition pickR_set P1 P2 (x1 x2 : R) :=
  { y | P1 /\ y = x1 \/ P2 /\ y = x2 }%Rset.

Definition pickR P1 P2 x1 x2 := sup (pickR_set P1 P2 x1 x2).

Definition selectR P := pickR P (~ P).

Definition min x1 x2 := pickR (x1 <= x2) (x2 <= x1) x1 x2.

Definition max x1 x2 := pickR (x1 <= x2) (x2 <= x1) x2 x1.

Inductive floor_set (x : R) : R -> Prop :=
  FloorSet (m : int) of m%:~R <= x : floor_set x m%:~R.

Definition floor x := sup (floor_set x).

Definition range1 (x y : R) := x <= y < x + 1.


End RealDerivedOps.


Notation "'select' { x1 'if' P1 , x2 'if' P2 }" := (pickR P1 P2 x1 x2)
   (at level 10, x1, x2, P1, P2 at level 100,
    format "'select'  { x1  'if'  P1 ,  x2  'if'  P2 }") : real_scope.

Notation "'select' { x1 'if' P , 'else' x2 }" := (selectR P x1 x2)
   (at level 10, x1, x2, P at level 100,
    format "'select'  { x1  'if'  P ,  'else'  x2 }") : real_scope.

Prenex Implicits min max.
(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType) (E : R -> Prop).

(* Lemma sup_ub : has_ub E -> ub E (sup E). *)
(* Proof. *)
(* move=> ubE x E_x; apply: (sup_upper_bound R) (E_x). *)
(* by split; first by exists x. *)
(* Qed. *)

(* Lemma sup_total E x : has_sup E -> down E x \/ sup E <= x. *)
(* Proof. *)
(* move=> has_supE; case: (le_total R (sup E) x) => hx //; left. *)
(* have /(sup_adherent R has_supE) : 0 < sup E - x by apply/subR_gt0. *)
(* case=> e Ee hlte; exists e => //. *)
(* by move: hlte; rewrite oppRB addRCA subRR addR0 => /ltRW. *)
(* Qed. *)

End RealLemmas.
(* -------------------------------------------------------------------- *)

Section RealInstancesTheory.

Variables (R R' : realType).

Definition image (phi : R -> R') (E : R -> Prop) (x' : R') :=
  exists2 x : R, E x & x' = (phi x).

Record morphism (phi : R -> R') : Prop := Morphism {
  morph_le   : forall x y, phi x <= phi y <-> x <= y;
  morph_sup  : forall (E : R -> Prop),
                 has_sup E -> phi (sup E) = (sup (image phi E));
  morph_add  : forall x y, phi (x + y) = phi x + phi y;
  morph_zero : phi 0 = 0;
  morph_opp  : forall x, phi (-x) = -(phi x);
  morph_mul  : forall x y, phi (x * y) = (phi x) * (phi y);
  morph_one  : phi 1 = 1;
  morph_inv  : forall x, x <> 0 -> phi x^-1 = (phi x)^-1
}.

End RealInstancesTheory.
