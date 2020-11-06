From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

(* NB: wip, this is inspired from posnum.v in analysis,
  the idea is to give a type of non-negative numbers for
  any numDomainType, the type constructed being total ordered  *)
Reserved Notation "'{nonneg' R }" (at level 0, format "'{nonneg'  R }").
Reserved Notation "x %:nng" (at level 0, format "x %:nng").
Reserved Notation "x %:nngnum" (at level 0, format "x %:nngnum").
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
Hint Extern 0 ((0 <= _)%R = true) => exact: nngnum_ge0 : core.
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

(*************)
(* INSTANCES *)
(*************)

Module ProdNormedZmodule.
Section ProdNormedZmodule.
Context {R : numDomainType} {U V : normedZmodType R}.

Definition norm (x : U * V) : R := Num.max `|x.1| `|x.2|.

Lemma normD x y : norm (x + y) <= norm x + norm y.
Proof.
rewrite /norm nng_le_maxl !(le_trans (ler_norm_add _ _)) ?ler_add//;
by rewrite comparable_le_maxr ?lexx ?orbT// real_comparable.
Qed.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Proof.
case: x => x1 x2 /eqP; rewrite eq_le nng_le_maxl 2!normr_le0 -andbA/=.
by case/and3P => /eqP -> /eqP ->.
Qed.

Lemma normMn x n : norm (x *+ n) = (norm x) *+ n.
Proof. by rewrite /norm pairMnE -mulr_natl maxr_pmulr ?mulr_natl ?normrMn. Qed.

Lemma normrN x : norm (- x) = norm x.
Proof. by rewrite /norm/= !normrN. Qed.

Definition normedZmodMixin :
  @Num.normed_mixin_of R [zmodType of U * V] (Num.NumDomain.class R) :=
  @Num.NormedMixin _ _ _ norm normD norm_eq0 normMn normrN.

Canonical normedZmodType := NormedZmodType R (U * V) normedZmodMixin.

Lemma prod_normE (x : normedZmodType) : `|x| = Num.max `|x.1| `|x.2|.
Proof. by []. Qed.

End ProdNormedZmodule.

Module Exports.
Canonical normedZmodType.
Definition prod_normE := @prod_normE.
End Exports.

End ProdNormedZmodule.
Export ProdNormedZmodule.Exports.
