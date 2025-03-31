(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import finset interval.

(**md**************************************************************************)
(* # MathComp extra                                                           *)
(*                                                                            *)
(* This files contains lemmas and definitions recently added in mathcomp,     *)
(* in order to be able to compile analysis with older versions of mathcomp.   *)
(*                                                                            *)
(* ```                                                                        *)
(*               proj i f == f i, where f : forall i, T i                     *)
(*             dfwith f x == fun j => x if j = i, and f j otherwise           *)
(*                           given x : T i                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(**************************)
(* MathComp 2.2 additions *)
(**************************)

Notation "f \min g" := (Order.min_fun f g) : function_scope.
Notation "f \max g" := (Order.max_fun f g) : function_scope.

Lemma ler_sqrt {R : rcfType} (a b : R) :
  (0 <= b -> (Num.sqrt a <= Num.sqrt b) = (a <= b))%R.
Proof.
have [b_gt0 _|//|<- _] := ltgtP; last first.
  by rewrite sqrtr0 -[RHS]sqrtr_eq0 le_eqVlt ltNge sqrtr_ge0 orbF.
have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt// ?qualifE/= ?ltW.
by rewrite ler0_sqrtr // sqrtr_ge0 (le_trans a_le0) ?ltW.
Qed.

(**************************)
(* MathComp 2.3 additions *)
(**************************)

(* Compatibility layer for Order.disp_t introduced in MathComp 2.3            *)
(* TODO: remove when we drop the support for MathComp 2.2                     *)
Module Order.
Import Order.
Definition disp_t : Set.
Proof. exact: disp_t || exact: unit. Defined.
Definition default_display : disp_t.
Proof. exact: tt || exact: Disp tt tt. Defined.
End Order.

Lemma invf_plt (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x^-1 < y)%R = (y^-1 < x)%R}.
Proof.
by move=> x y ? ?; rewrite -[in LHS](@invrK _ y) ltf_pV2// posrE invr_gt0.
Qed.

Lemma invf_ltp (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x < y^-1)%R = (y < x^-1)%R}.
Proof.
by move=> x y ? ?; rewrite -(invrK x) invf_plt ?posrE ?invr_gt0// !invrK.
Qed.

Lemma invf_ple (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x^-1 <= y)%R = (y^-1 <= x)%R}.
Proof.
by move=> x y ? ?; rewrite -[in LHS](@invrK _ y) lef_pV2// posrE invr_gt0.
Qed.

Lemma invf_lep (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x <= y^-1)%R = (y <= x^-1)%R}.
Proof.
by move=> x y ? ?; rewrite -(invrK x) invf_ple ?posrE ?invr_gt0// !invrK.
Qed.

Definition proj {I} {T : I -> Type} i (f : forall i, T i) := f i.

Section DFunWith.
Variables (I : eqType) (T : I -> Type) (f : forall i, T i).

Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.

Lemma dfwithin i x : dfwith x i = x.
Proof. by rewrite /dfwith; case: eqP => // ii; rewrite eq_axiomK. Qed.

Lemma dfwithout i (x : T i) j : i != j -> dfwith x j = f j.
Proof. by rewrite /dfwith; case: eqP. Qed.

Variant dfwith_spec i (x : T i) : forall j, T j -> Type :=
  | DFunWithin : dfwith_spec x x
  | DFunWithout j : i != j -> dfwith_spec x (f j).

Lemma dfwithP i (x : T i) (j : I) : dfwith_spec x (dfwith x j).
Proof.
by case: (eqVneq i j) => [<-|nij];
   [rewrite dfwithin|rewrite dfwithout//]; constructor.
Qed.

Lemma projK i (x : T i) : cancel (@dfwith i) (proj i).
Proof. by move=> z; rewrite /proj dfwithin. Qed.

End DFunWith.
Arguments dfwith {I T} f i x.

Definition idempotent_fun (U : Type) (f : U -> U) := f \o f =1 f.

Section intrN.

Variable R : ringType.

Implicit Types n : int.

Lemma intrN n : (- n)%:~R = - n%:~R :> R. Proof. exact: mulrNz. Qed.

End intrN.

From mathcomp Require Import archimedean.
Import Num.Theory.

Section num_floor_ceil.
Context {R : archiNumDomainType}.
Implicit Type x : R.

Lemma real_floor_itv x : x \is Num.real ->
  (Num.floor x)%:~R <= x < (Num.floor x + 1)%:~R.
Proof. by case: (x \is _) (archimedean.Num.Theory.floorP x). Qed.

Lemma real_ge_floor x : x \is Num.real -> (Num.floor x)%:~R <= x.
Proof. by move=> /real_floor_itv /andP[]. Qed.

Lemma real_ceil_itv x : x \is Num.real ->
  (Num.ceil x - 1)%:~R < x <= (Num.ceil x)%:~R.
Proof.
move=> Rx.
by rewrite ?ceilNfloor -opprD !mulrNz ltrNl lerNr andbC real_floor_itv ?realN.
Qed.

End num_floor_ceil.

Section floor_ceil.
Context {R : archiDomainType}.
Implicit Type x : R.

Lemma ge_floor x : (Num.floor x)%:~R <= x.
Proof. exact: Num.Theory.ge_floor. Qed.

Lemma floor_ge_int x (z : int) : (z%:~R <= x) = (z <= Num.floor x).
Proof. exact: Num.Theory.floor_ge_int. Qed.

Lemma lt_succ_floor x : x < (Num.floor x + 1)%:~R.
Proof. exact: Num.Theory.lt_succ_floor. Qed.

#[deprecated(since="mathcomp-analysis 1.3.0", note="use `Num.Theory.le_ceil` instead")]
Lemma ceil_ge x : x <= (Num.ceil x)%:~R.
Proof. exact: Num.Theory.le_ceil. Qed.

#[deprecated(since="mathcomp-analysis 1.3.0", note="use `Num.Theory.ceil_le_int`")]
Lemma ceil_ge_int x (z : int) : (x <= z%:~R) = (Num.ceil x <= z).
Proof. exact: Num.Theory.ceil_le_int. Qed.

Lemma ceilN x : Num.ceil (- x) = - Num.floor x.
Proof. by rewrite ?ceilNfloor /Num.ceil opprK. Qed.

Lemma floorN x : Num.floor (- x) = - Num.ceil x.
Proof. by rewrite ?ceilNfloor /Num.ceil opprK. Qed.

End floor_ceil.

(**************************)
(* MathComp 2.4 additions *)
(**************************)

Lemma comparable_BSide_min d (T : porderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. by rewrite !minEle bnd_simp => /comparable_leP[]. Qed.

Lemma comparable_BSide_max d (T : porderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. by rewrite !maxEle bnd_simp => /comparable_leP[]. Qed.

Lemma BSide_min d (T : orderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. exact: comparable_BSide_min. Qed.

Lemma BSide_max d (T : orderType d) b (x y : T) : (x >=< y)%O ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. exact: comparable_BSide_max. Qed.

Section NumDomainType.

Variable (R : numDomainType).

Lemma real_BSide_min b (x y : R) : x \in Num.real -> y \in Num.real ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_min/real_comparable. Qed.

Lemma real_BSide_max b (x y : R) : x \in Num.real -> y \in Num.real ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_max/real_comparable. Qed.

Lemma natr_min (m n : nat) : (Order.min m n)%:R = Order.min m%:R n%:R :> R.
Proof. by rewrite !minElt ltr_nat /Order.lt/= -fun_if. Qed.

Lemma natr_max (m n : nat) : (Order.max m n)%:R = Order.max m%:R n%:R :> R.
Proof. by rewrite !maxElt ltr_nat /Order.lt/= -fun_if. Qed.

End NumDomainType.

Lemma comparable_le_min2 d (T : porderType d) (x y z t : T) :
    (x >=< y)%O -> (z >=< t)%O ->
  (x <= z)%O -> (y <= t)%O -> (Order.min x y <= Order.min z t)%O.
Proof.
move=> + + xz yt => /comparable_leP[] xy /comparable_leP[] zt //.
- exact: le_trans xy yt.
- exact: le_trans (ltW xy) xz.
Qed.
#[deprecated(since="mathcomp-analysis 1.10.0",
  note="use `comparable_le_min2` instead")]
Notation comparable_min_le_min := comparable_le_min2.

Lemma comparable_le_max2 d (T : porderType d) (x y z t : T) :
    (x >=< y)%O -> (z >=< t)%O ->
  (x <= z)%O -> (y <= t)%O -> (Order.max x y <= Order.max z t)%O.
Proof.
move=> + + xz yt => /comparable_leP[] xy /comparable_leP[] zt //.
- exact: le_trans yt (ltW zt).
- exact: le_trans xz zt.
Qed.
#[deprecated(since="mathcomp-analysis 1.10.0",
  note="use `comparable_le_max2` instead")]
Notation comparable_max_le_max := comparable_le_max2.

Lemma le_min2 d (T : orderType d) (x y z t : T) :
  (x <= z)%O -> (y <= t)%O -> (Order.min x y <= Order.min z t)%O.
Proof. exact: comparable_min_le_min. Qed.
#[deprecated(since="mathcomp-analysis 1.10.0", note="use `le_min2` instead")]
Notation min_le_min := le_min2.

Lemma le_max2 d (T : orderType d) (x y z t : T) :
  (x <= z)%O -> (y <= t)%O -> (Order.max x y <= Order.max z t)%O.
Proof. exact: comparable_max_le_max. Qed.
#[deprecated(since="mathcomp-analysis 1.10.0", note="use `le_max2` instead")]
Notation max_le_max := le_max2.

Lemma sqrtC_real {R : numClosedFieldType} (x : R) : 0 <= x ->
  sqrtC x \in Num.real.
Proof. by rewrite -sqrtC_ge0; apply: ger0_real. Qed.
#[deprecated(since="mathcomp-analysis 1.10.0", note="use `sqrtC_real` instead")]
Notation real_sqrtC := sqrtC_real.

Lemma exprz_ge0 [R : numDomainType] n (x : R) (hx : 0 <= x) : (0 <= x ^ n).
Proof. by case: n => n; rewrite ?invr_ge0 exprn_ge0. Qed.

Lemma exprz_gt0 [R : numDomainType] n (x : R) (hx : 0 < x) : (0 < x ^ n).
Proof. by case: n => n; rewrite ?invr_gt0 exprn_gt0. Qed.
