(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect fingroup ssralg poly ssrnum.
Require Import boolp.

(******************************************************************************)
(* This file develops tools to make the manipulation of non-negative numbers  *)
(* easier, on the model of posnum.v. This is WIP.                             *)
(*                                                                            *)
(*   {nonneg R} == interface types for elements in R that are non-negative; R *)
(*                 must have a numDomainType structure. Automatically solves  *)
(*                 goals of the form x >= 0. {nonneg R} is stable by          *)
(*                 addition, multiplication. All natural numbers n%:R are     *)
(*                 also canonically in {nonneg R}.                            *)
(*                 This type is also shown to be a latticeType, a             *)
(*                 distrLatticeType, and an orderType,                        *)
(*  NngNum xge0 == packs the proof xge0 : x >= 0, for x : R, to build a       *)
(*                 {nonneg R}                                                 *)
(*       x%:nng == explicitly casts x to {nonneg R}, triggers the inference   *)
(*                 of a {nngum R} structure for x                             *)
(*    x%:nngnum == explicit cast from {nonneg R} to R                         *)
(*                                                                            *)
(* The module BigmaxrNonneg contains a theory about bigops of the form        *)
(* \big[maxr/x]_(i | P i) F i where F : I -> {nonneg R} which is used in      *)
(* normedtype.v to develop the topology of matrices.                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Reserved Notation "'{nonneg' R }" (at level 0, format "'{nonneg'  R }").
Reserved Notation "x %:nng" (at level 2, left associativity, format "x %:nng").
Reserved Notation "x %:nngnum" (at level 2, left associativity, format "x %:nngnum").
Module Nonneg.
Section nonnegative_numbers.

Record nngnum_of (R : numDomainType) (phR : phant R) := NngNumDef {
  num_of_nng : R ;
  nngnum_ge0 :> num_of_nng >= 0
}.
Hint Resolve nngnum_ge0 : core.
Hint Extern 0 ((0 <= _)%R = true) => exact: nngnum_ge0 : core.
Local Notation "'{nonneg' R }" := (nngnum_of (@Phant R)).
Definition NngNum (R : numDomainType) x x_ge0 : {nonneg R} :=
  @NngNumDef _ (Phant R) x x_ge0.
Arguments NngNum {R}.

Local Notation "x %:nngnum" := (num_of_nng x) : ring_scope.
Definition nng_of_num (R : numDomainType) (x : {nonneg R})
   (phx : phantom R x%:nngnum) := x.
Local Notation "x %:nng" := (nng_of_num (Phantom _ x)) : ring_scope.

Section Order.
Variable (R : numDomainType).

Canonical nngnum_subType := [subType for @num_of_nng R (Phant R)].
Definition nngnum_eqMixin := [eqMixin of {nonneg R} by <:].
Canonical nngnum_eqType := EqType {nonneg R} nngnum_eqMixin.
Definition nngnum_choiceMixin := [choiceMixin of {nonneg R} by <:].
Canonical nngnum_choiceType := ChoiceType {nonneg R} nngnum_choiceMixin.
Definition nngnum_porderMixin := [porderMixin of {nonneg R} by <:].
Canonical nngnum_porderType :=
  POrderType ring_display {nonneg R} nngnum_porderMixin.

Lemma nngnum_le_total : totalPOrderMixin [porderType of {nonneg R}].
Proof. by move=> x y; apply/real_comparable; apply/ger0_real. Qed.

Canonical nngnum_latticeType := LatticeType {nonneg R} nngnum_le_total.
Canonical nngnum_distrLatticeType := DistrLatticeType {nonneg R} nngnum_le_total.
Canonical nngnum_orderType := OrderType {nonneg R} nngnum_le_total.

End Order.

End nonnegative_numbers.

Module Exports.
Arguments NngNum {R}.
Notation "'{nonneg' R }" := (nngnum_of (@Phant R)) : type_scope.
Notation nngnum R := (@num_of_nng _ (@Phant R)).
Notation "x %:nngnum" := (num_of_nng x) : ring_scope.
#[export] Hint Extern 0 ((0 <= _)%R = true) => exact: nngnum_ge0 : core.
Notation "x %:nng" := (nng_of_num (Phantom _ x)) : ring_scope.
Canonical nngnum_subType.
Canonical nngnum_eqType.
Canonical nngnum_choiceType.
Canonical nngnum_porderType.
Canonical nngnum_latticeType.
Canonical nngnum_orderType.
End Exports.

End Nonneg.
Export Nonneg.Exports.

Section NngNum.
Context {R : numDomainType}.
Implicit Types a : R.
Implicit Types x y : {nonneg R}.
Import Nonneg.

Canonical addr_nngnum x y := NngNum (x%:nngnum + y%:nngnum) (addr_ge0 x y).
Canonical mulr_nngnum x y := NngNum (x%:nngnum * y%:nngnum) (mulr_ge0 x y).
Canonical mulrn_nngnum x n := NngNum (x%:nngnum *+ n) (mulrn_wge0 n x).
Canonical zeror_nngnum := @NngNum R 0 (lexx 0).
Canonical oner_nngnum := @NngNum R 1 ler01.

Lemma inv_nng_ge0 (x : R) : 0 <= x -> 0 <= x^-1.
Proof. by rewrite invr_ge0. Qed.
Canonical invr_nngnum x := NngNum (x%:nngnum^-1) (inv_nng_ge0 x).

Lemma nngnum_lt0 x : (x%:nngnum < 0 :> R) = false.
Proof. by rewrite le_gtF. Qed.

Lemma nngnum_real x : x%:nngnum \is Num.real.
Proof. by rewrite ger0_real. Qed.
Hint Resolve nngnum_real : core.

Lemma nng_eq : {mono nngnum R : x y / x == y}. Proof. by []. Qed.
Lemma nng_le : {mono nngnum R : x y / x <= y}. Proof. by []. Qed.
Lemma nng_lt : {mono nngnum R : x y / x < y}. Proof. by []. Qed.

Lemma nng_eq0 x : (x%:nngnum == 0) = (x == 0%:nng).
Proof. by []. Qed.

Lemma nng_min : {morph nngnum R : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle nng_le -fun_if. Qed.

Lemma nng_max : {morph nngnum R : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle nng_le -fun_if. Qed.

Lemma nng_le_maxr a x y :
  a <= Num.max x%:nngnum y%:nngnum = (a <= x%:nngnum) || (a <= y%:nngnum).
Proof. by rewrite -comparable_le_maxr// real_comparable. Qed.

Lemma nng_le_maxl a x y :
  Num.max x%:nngnum  y%:nngnum <= a = (x%:nngnum <= a) && (y%:nngnum <= a).
Proof. by rewrite -comparable_le_maxl// real_comparable. Qed.

Lemma nng_le_minr a x y :
  a <= Num.min x%:nngnum y%:nngnum = (a <= x%:nngnum) && (a <= y%:nngnum).
Proof. by rewrite -comparable_le_minr// real_comparable. Qed.

Lemma nng_le_minl a x y :
  Num.min x%:nngnum y%:nngnum <= a = (x%:nngnum <= a) || (y%:nngnum <= a).
Proof. by rewrite -comparable_le_minl// real_comparable. Qed.

Lemma max_ge0 x y : Num.max x%:nngnum y%:nngnum >= 0.
Proof. by rewrite comparable_le_maxr ?real_comparable// ?nngnum_ge0. Qed.

Lemma min_ge0 x y : Num.min x%:nngnum y%:nngnum >= 0.
Proof. by rewrite comparable_le_minr ?real_comparable// ?nngnum_ge0. Qed.

Canonical max_nngnum x y := NngNum (Num.max x%:nngnum y%:nngnum) (max_ge0 x y).
Canonical min_nngnum x y := NngNum (Num.min x%:nngnum y%:nngnum) (min_ge0 x y).

Canonical normr_nngnum (V : normedZmodType R) (x : V) :=
  NngNum `|x| (normr_ge0 x).

Lemma nng_abs_eq0 a : (`|a|%:nng == 0%:nng) = (a == 0).
Proof. by rewrite -normr_eq0. Qed.

Lemma nng_abs_le a x : 0 <= a -> (`|a|%:nng <= x) = (a <= x%:nngnum).
Proof. by move=> a0; rewrite -nng_le//= ger0_norm. Qed.

Lemma nng_abs_lt a x : 0 <= a -> (`|a|%:nng < x) = (a < x%:nngnum).
Proof. by move=> a0; rewrite -nng_lt/= ger0_norm. Qed.

(* Cyril: remove *)
Lemma nonneg_maxr a x y : `|a| * (Num.max x y)%:nngnum =
  (Num.max (`|a| * x%:nngnum)%:nng (`|a| * y%:nngnum)%:nng)%:nngnum.
Proof. by rewrite !nng_max maxr_pmulr. Qed.

End NngNum.

Import Num.Def.
