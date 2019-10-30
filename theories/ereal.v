(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

(* NB: taken out from reals.v and generalized in 2019 *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Section ExtendedReals.
Variable (R : numDomainType).

Inductive er := ERFin of R | ERPInf | ERNInf.

Coercion real_of_er x :=
  if x is ERFin v then v else 0%R.
End ExtendedReals.

(*Notation "\+inf" := (@ERPInf _).*)
Notation "+oo" := (@ERPInf _).
(*Notation "\-inf" := (@ERNInf _).*)
Notation "-oo" := (@ERNInf _).
Notation "x %:E" := (@ERFin _ x) (at level 2, format "x %:E").

Notation "{ 'ereal' R }" := (er R) (format "{ 'ereal'  R }").

Bind    Scope ereal_scope with er.
Delimit Scope ereal_scope with E.

Section ERealCode.
Variable (R : numDomainType).

Definition code (x : {ereal R}) :=
  match x with
  | x%:E  => GenTree.Node 0 [:: GenTree.Leaf x]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option {ereal R} :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf x] => Some x%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode.
Proof. by case. Qed.

Definition ereal_eqMixin := PcanEqMixin codeK.
Canonical  ereal_eqType  := EqType {ereal R} ereal_eqMixin.
Definition ereal_choiceMixin := PcanChoiceMixin codeK.
Canonical  ereal_choiceType  := ChoiceType {ereal R} ereal_choiceMixin.

End ERealCode.

Lemma eqe {R : numDomainType} (x1 x2 : R) :
  (x1%:E == x2%:E) = (x1 == x2).
Proof. by apply/eqP/eqP=> [[]|->]. Qed.

Section ERealOrder.
Context {R : realDomainType}.
Implicit Types (x y : {ereal R}).

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, _ | _, +oo => true
  | +oo, _ | _, -oo => false

  | x1%:E, x2%:E => (x1 <= x2)%O
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, -oo | +oo, +oo => false
  | -oo, _   | _  , +oo => true
  | +oo, _   | _  , -oo => false

  | x1%:E, x2%:E => (x1 < x2)%O
  end.

Definition min_ereal x1 x2 :=
  match x1, x2 with
  | -oo, _ | _, -oo => -oo
  | +oo, x | x, +oo => x

  | x1%:E, x2%:E => (Num.Def.minr x1 x2)%:E
  end.

Definition max_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x | x, -oo => x
  | +oo, _ | _, +oo => +oo

  | x1%:E, x2%:E => (Num.Def.maxr x1 x2)%:E
  end.

Lemma lt_def_ereal x y : lt_ereal x y = (y != x) && le_ereal x y.
Proof. by case: x y => [?||][?||] //=; rewrite lt_def eqe. Qed.

Lemma minE_ereal x y : min_ereal x y = if le_ereal x y then x else y.
Proof. by case: x y => [?||][?||] //=; case: leP. Qed.

Lemma maxE_ereal x y : max_ereal x y = if le_ereal y x then x else y.
Proof. by case: x y => [?||][?||] //=; case: ltP. Qed.

Lemma le_anti_ereal : ssrbool.antisymmetric le_ereal.
Proof. by case=> [?||][?||] //= /le_anti ->. Qed.

Lemma le_trans_ereal : ssrbool.transitive le_ereal.
Proof. by case=> [?||][?||][?||] //=; exact: le_trans. Qed.

Lemma le_total_ereal : total le_ereal.
Proof. by case=> [?||][?||] //=; exact: le_total. Qed.

Definition ereal_porderMixin :=
  @LeOrderMixin _ le_ereal lt_ereal min_ereal max_ereal
                lt_def_ereal minE_ereal maxE_ereal
                le_anti_ereal le_trans_ereal le_total_ereal.

Fact ereal_display : unit. Proof. by []. Qed.

Canonical ereal_porderType :=
  POrderType ereal_display {ereal R} ereal_porderMixin.
Canonical ereal_latticeType := DistrLatticeType {ereal R} ereal_porderMixin.
Canonical ereal_totalType := OrderType {ereal R} ereal_porderMixin.

End ERealOrder.

Notation lee := (@Order.le ereal_display _) (only parsing).
Notation "@ 'lee' R" :=
  (@Order.le ereal_display R) (at level 10, R at level 8, only parsing).
Notation lte := (@Order.lt ereal_display _) (only parsing).
Notation "@ 'lte' R" :=
  (@Order.lt ereal_display R) (at level 10, R at level 8, only parsing).

Notation "x <= y" := (lee x y) : ereal_scope.
Notation "x < y"  := (lte x y) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) : ereal_scope.

Section ERealArith.
Context {R : numDomainType}.

Implicit Types (x y z : {ereal R}).

Definition eadd x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.

Definition eopp x :=
  match x with
  | x%:E  => (-x)%:E
  | -oo => +oo
  | +oo => -oo
  end.
End ERealArith.

Notation "+%E"   := eadd.
Notation "-%E"   := eopp.
Notation "x + y" := (eadd x y) : ereal_scope.
Notation "x - y" := (eadd x (eopp y)) : ereal_scope.
Notation "- x"   := (eopp x) : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%:E]_(i <- r | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%:E]_(i <- r) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%:E]_(m <= i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%:E]_(m <= i < n) F%R) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%:E]_(i | P%B) F%R) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%:E]_i F%R) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%:E]_(i : t | P%B) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%:E]_(i : t) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%:E]_(i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%:E]_(i < n) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%:E]_(i in A | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%:E]_(i in A) F%R) : ereal_scope.

Local Open Scope ereal_scope.

Section ERealArithTh.
Context {R : numDomainType}.

Implicit Types (x y z : {ereal R}).

Lemma adde0 : right_id (0%:E : {ereal R}) +%E.
Proof. by case=> //= x; rewrite addr0. Qed.

Lemma add0e : left_id (S := {ereal R}) 0%:E +%E.
Proof. by case=> //= x; rewrite add0r. Qed.

Lemma addeC : commutative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] //=; rewrite addrC. Qed.

Lemma addeA : associative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] [z||] //=; rewrite addrA. Qed.

Canonical adde_monoid := Monoid.Law addeA add0e adde0.
Canonical adde_comoid := Monoid.ComLaw addeC.

Lemma oppe0 : - (0%:E) = 0%:E :> {ereal R}.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := {ereal R}) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.
End ERealArithTh.
