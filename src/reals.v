(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finset bigop ssralg ssrnum ssrint rat poly bigenough.
Require Import ssrprop collections Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

Local Ltac idone := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope    with RR.
Delimit Scope realset_scope with Rset.

Local Open Scope real_scope.
Local Open Scope ring_scope.

Reserved Notation "c %:F"
  (at level 2, format "c %:F").
Reserved Notation "f \* g"
  (at level 45, left associativity).
Reserved Notation "f \^+ n"
  (at level 29, left associativity).

(* -------------------------------------------------------------------- *)
Module Real.
Section Mixin.

Variable (R : archiFieldType).

(* Real set non-emptyness. *)
Definition nonempty (E : {rset R}) :=
  exists x : R, x \mem E.

(* Real upper bound set. *)
Definition ub  (E : {rset R}) :=
  {{ z | forall y : R, E y -> y <= z }}.

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down  (E : {rset R}) :=
  {{ x | exists2 y : R, E y & x <= y }}.

(* Real set supremum existence condition. *)
Definition has_ub  (E : {rset R}) := nonempty (ub E).
Definition has_sup (E : {rset R}) := nonempty E /\ has_ub E.

Record mixin_of : Type := Mixin {
  sup : {rset R} -> R;
   _  :
    forall E : {rset Num.ArchimedeanField.sort R},
      has_sup E -> sup E \mem ub E;
   _  :
    forall (E : {rset Num.ArchimedeanField.sort R}) (eps : R),
      has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e
}.

End Mixin.

Definition EtaMixin R sup sup_upper_bound sup_adherent :=
  let _ := @Mixin R sup sup_upper_bound sup_adherent in
  @Mixin (Num.ArchimedeanField.Pack (Num.ArchimedeanField.class R) R)
         sup sup_upper_bound sup_adherent.

Global Arguments ub      {R}%type _%realset_scope.
Global Arguments has_ub  {R}%type _%realset_scope.
Global Arguments has_sup {R}%type _%realset_scope.
Global Arguments down    {R}%type _%realset_scope.

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

Export Real.Exports.

(* -------------------------------------------------------------------- *)
Definition sup {R : realType} := Real.sup (Real.class R).

Definition nonempty {R : realType} := @Real.nonempty R.
Definition ub       {R : realType} := @Real.ub R.
Definition down     {R : realType} := @Real.down R.
Definition has_ub   {R : realType} := @Real.has_ub R.
Definition has_sup  {R : realType} := @Real.has_sup R.

(* -------------------------------------------------------------------- *)
Section BaseReflect.
Context {R : realType}.

Implicit Types E : {rset R}.
Implicit Types x : R.

Lemma nonemptyP E : nonempty E <-> exists x, E x.
Proof. by []. Qed.

Lemma ubP E x : x \mem ub E <-> (forall y, y \mem E -> y <= x).
Proof. by rewrite !in_rset. Qed.

Lemma downP E x : x \mem down E <-> exists2 y, y \mem E & x <= y.
Proof. by rewrite !in_rset. Qed.

Lemma has_ubP E : has_ub E <-> nonempty (ub E).
Proof. by []. Qed.

Lemma has_supP E : has_sup E <-> (nonempty E /\ nonempty (ub E)).
Proof. by []. Qed.
End BaseReflect.

(* -------------------------------------------------------------------- *)
Lemma sup_upper_bound {R : realType} (E : {rset R}) :
  has_sup E -> (forall x, x \mem E -> x <= sup E).
Proof. by move=> supE; apply/ubP; case: R E supE=> ? [? []]. Qed.

Lemma sup_adherent {R : realType} (E : {rset R}) (eps : R) :
  has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e.
Proof. by case: R E eps=> ? [? []]. Qed.

(* -------------------------------------------------------------------- *)
Section RealDerivedOps.

Variable R : realType.

Definition pickR_set P1 P2 (x1 x2 : R) :=
  {{ y | P1 /\ y = x1 \/ P2 /\ y = x2 }}.

Definition pickR P1 P2 x1 x2 := sup (pickR_set P1 P2 x1 x2).

Definition selectR P : R -> R -> R := pickR P (~ P).

Definition min x1 x2 := pickR (x1 <= x2) (x2 <= x1) x1 x2.

Definition max x1 x2 := pickR (x1 <= x2) (x2 <= x1) x2 x1.

Inductive floor_set (x : R) : R -> Prop :=
  FloorSet (m : int) of m%:~R <= x : floor_set x m%:~R.

Definition floor x : R := sup (Collection (floor_set x)).

Definition range1 (x : R) := { y | x <= y < x + 1 }%Rset.
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

Variables (R : realType).

Implicit Types E : {rset R}.
Implicit Types x : R.

Lemma sup_ub E : has_ub E -> sup E \mem ub E.
Proof.
move=> ubE; apply/ubP=> x x_in_E; apply/sup_upper_bound=> //.
by apply/has_supP; split; first by exists x.
Qed.

Lemma sup_total E x : has_sup E -> x \mem down E \/ sup E <= x.
Proof.
move=> has_supE; case: (lerP (sup E) x)=> hx; [idone|left].
have /(sup_adherent has_supE) : 0 < sup E - x by rewrite subr_gt0.
case=> e Ee hlte; apply/downP; exists e => //; move: hlte.
by rewrite opprB addrCA subrr addr0 => /ltrW.
Qed.

Lemma sup_le_ub E x : nonempty E -> x \mem ub E -> sup E <= x.
Proof.
move=> hasE /ubP leEx; set y := sup E; pose z := (x + y) / 2%:R.
have Dz: 2%:R * z = x + y.
  by rewrite mulrCA divff ?mulr1 // pnatr_eq0.
have ubE: has_sup E by split; last by exists x; apply/ubP.
have [/in_rset [t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(ler_add2l x) -Dz -mulr2n -[X in _<=X]mulr_natl.
  rewrite ler_pmul2l ?ltr0Sn //; exact/(ler_trans lezt)/leEx.
rewrite -(ler_add2r y) -Dz -mulr2n -[X in X<=_]mulr_natl.
by rewrite ler_pmul2l ?ltr0Sn.
Qed.
End RealLemmas.
