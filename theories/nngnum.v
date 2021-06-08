From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly ssrnum.
Require Import boolp.

(******************************************************************************)
(* This file develops tools to make the manipulation of non-negative numbers  *)
(* easier, on the model of posnum.v. This is WIP.                             *)
(*                                                                            *)
(*   {nngnum R} == interface types for elements in R that are non-negative; R *)
(*                 must have a numDomainType structure. Automatically solves  *)
(*                 goals of the form x >= 0. {nngnum R} is stable by          *)
(*                 addition, multiplication. All natural numbers n%:R are     *)
(*                 also canonically in {nngnum R}.                            *)
(*                 This type is also shown to be a latticeType, a             *)
(*                 distrLatticeType, and an orderType,                        *)
(*  NngNum xge0 == packs the proof xge0 : x >= 0, for x : R, to build a       *)
(*                 {nngnum R}                                                 *)
(*       x%:nng == explicitly casts x to {nngnum R}, triggers the inference   *)
(*                 of a {nngum R} structure for x                             *)
(*    x%:nngnum == explicit cast from {nngnum R} to R                         *)
(*                                                                            *)
(* The module BigmaxrNonneg contains a theory about bigops of the form        *)
(* \big[maxr/x]_(i | P i) F i where F : I -> {nngnum R} which is used in      *)
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

(* TODO: general purpose lemma? add to mathcomp? *)
Lemma filter_andb I r (a P : pred I) :
  [seq i <- r | P i && a i] = [seq i <- [seq j <- r | P j] | a i].
Proof. by elim: r => //= i r ->; case P. Qed.

Import Num.Def.

Module BigmaxrNonneg.
Section bigmaxr_nonneg.
Variable (R : numDomainType).

Lemma bigmaxr_mkcond I r (P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i =
     \big[maxr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite unlock; elim: r x => //= i r ihr x.
case P; rewrite ihr // max_r //; elim: r {ihr} => //= j r ihr.
by rewrite le_maxr ihr orbT.
Qed.

Lemma bigmaxr_split I r (P : pred I) (F1 F2 : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) (maxr (F1 i) (F2 i)) =
  maxr (\big[maxr/x]_(i <- r | P i) F1 i) (\big[maxr/x]_(i <- r | P i) F2 i).
Proof.
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?maxxx //.
by rewrite maxCA -!maxA maxCA.
Qed.

Lemma bigmaxr_idl I r (P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i = maxr x (\big[maxr/x]_(i <- r | P i) F i).
Proof.
rewrite -big_filter; elim: [seq i <- r | P i] => [|i l ihl].
  by rewrite big_nil maxxx.
by rewrite big_cons maxCA -ihl.
Qed.

Lemma bigmaxrID I r (a P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i =
  maxr (\big[maxr/x]_(i <- r | P i && a i) F i)
    (\big[maxr/x]_(i <- r | P i && ~~ a i) F i).
Proof.
rewrite -!(big_filter _ (fun _ => _ && _)) !filter_andb !big_filter.
rewrite ![in RHS](bigmaxr_mkcond _ _ F) !big_filter -bigmaxr_split.
have eqmax : forall i, P i ->
  maxr (if a i then F i else x) (if ~~ a i then F i else x) = maxr (F i) x.
  by move=> i _; case: (a i) => //=; rewrite maxC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -maxA -bigmaxr_idl ihl.
Qed.

Lemma bigmaxr_seq1 I (i : I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(j <- [:: i]) F j = maxr (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigmaxr_pred1_eq (I : finType) (i : I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(j | j == i) F j = maxr (F i) x.
Proof.
have [e1 <- _ [e_enum _]] := big_enumP (pred1 i).
by rewrite (perm_small_eq _ e_enum) enum1 ?bigmaxr_seq1.
Qed.

Lemma bigmaxr_pred1 (I : finType) i (P : pred I) (F : I -> {nonneg R}) x :
  P =1 pred1 i -> \big[maxr/x]_(j | P j) F j = maxr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigmaxr_pred1_eq. Qed.

Lemma bigmaxrD1 (I : finType) j (P : pred I) (F : I -> {nonneg R}) x :
  P j -> \big[maxr/x]_(i | P i) F i
    = maxr (F j) (\big[maxr/x]_(i | P i && (i != j)) F i).
Proof.
move=> Pj; rewrite (bigmaxrID _ (pred1 j)) [in RHS]bigmaxr_idl maxA.
by congr maxr; apply: bigmaxr_pred1 => i; rewrite /= andbC; case: eqP => //->.
Qed.

Lemma ler_bigmaxr_cond (I : finType) (P : pred I) (F : I -> {nonneg R}) x i0 :
  P i0 -> F i0 <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigmaxrD1 _ _ Pi0) le_maxr lexx. Qed.

Lemma ler_bigmaxr (I : finType) (F : I -> {nonneg R}) (i0 : I) x :
  F i0 <= \big[maxr/x]_i F i.
Proof. exact: ler_bigmaxr_cond. Qed.

Lemma bigmaxr_lerP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (x <= m /\ forall i, P i -> F i <= m)
    (\big[maxr/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[lexm leFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite le_maxl =>->.
rewrite bigmaxr_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigmaxr_sup (I : finType) i0 (P : pred I) m (F : I -> {nonneg R}) x :
  P i0 -> m <= F i0 -> m <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0 ?; apply: le_trans (ler_bigmaxr_cond _ _ Pi0). Qed.

Lemma bigmaxr_ltrP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (x < m /\ forall i, P i -> F i < m)
    (\big[maxr/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[ltxm ltFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite lt_maxl =>->.
rewrite bigmaxr_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigmaxr_gerP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (m <= x \/ exists2 i, P i & m <= F i)
  (m <= \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[lemx|[i Pi lemFi]]]; last 2 first.
- by rewrite bigmaxr_idl le_maxr lemx.
- by rewrite (bigmaxrD1 _ _ Pi) le_maxr lemFi.
rewrite leNgt => /bigmaxr_ltrP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -leNgt; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -leNgt; right; exists i.
Qed.

Lemma bigmaxr_gtrP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (m < x \/ exists2 i, P i & m < F i)
  (m < \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[ltmx|[i Pi ltmFi]]]; last 2 first.
- by rewrite bigmaxr_idl lt_maxr ltmx.
- by rewrite (bigmaxrD1 _ _ Pi) lt_maxr ltmFi.
rewrite ltNge => /bigmaxr_lerP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -ltNge; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -ltNge; right; exists i.
Qed.

End bigmaxr_nonneg.
Module Exports.
Arguments bigmaxr_mkcond {R I r}.
Arguments bigmaxrID {R I r}.
Arguments bigmaxr_pred1 {R I} i {P F}.
Arguments bigmaxrD1 {R I} j {P F}.
Arguments ler_bigmaxr_cond {R I P F}.
Arguments ler_bigmaxr {R I F}.
Arguments bigmaxr_sup {R I} i0 {P m F}.
End Exports.
End BigmaxrNonneg.
Export BigmaxrNonneg.Exports.
