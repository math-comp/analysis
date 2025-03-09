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

#[deprecated(since="mathcomp 2.4.0", note="Use floor_ge_int_tmp instead.")]
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
Proof. exact: comparable_le_min2. Qed.
#[deprecated(since="mathcomp-analysis 1.10.0", note="use `le_min2` instead")]
Notation min_le_min := le_min2.

Lemma le_max2 d (T : orderType d) (x y z t : T) :
  (x <= z)%O -> (y <= t)%O -> (Order.max x y <= Order.max z t)%O.
Proof. exact: comparable_le_max2. Qed.
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

Section num_trunc_floor_ceil.
Context {R : archiNumDomainType}.
Implicit Type x : R.

Lemma truncn_le x : ((Num.trunc x)%:R <= x) = (0 <= x).
Proof.
by have := trunc_floor x; case: ifP => [/trunc_itv/andP[] | _ -> //].
Qed.

Lemma real_truncnS_gt x : x \is Num.real -> x < (Num.trunc x).+1%:R.
Proof. by move/real_ge0P => [/trunc_itv/andP[]|/lt_le_trans->]. Qed.

Lemma truncn_ge_nat x n : 0 <= x -> (n <= Num.trunc x)%N = (n%:R <= x).
Proof.
move=> /trunc_itv /andP[letx ltxt1]; apply/idP/idP => lenx.
  by apply: le_trans letx; rewrite ler_nat.
by rewrite -ltnS -(ltr_nat R); apply: le_lt_trans ltxt1.
Qed.

Lemma truncn_gt_nat x n : (n < Num.trunc x)%N = (n.+1%:R <= x).
Proof.
have := trunc_floor x; case: ifP => [x0 _ | x0 ->].
  by rewrite truncn_ge_nat.
by rewrite ltn0; apply/esym/(contraFF _ x0)/le_trans.
Qed.

Lemma truncn_lt_nat x n : 0 <= x -> (Num.trunc x < n)%N = (x < n%:R).
Proof. by move=> ?; rewrite real_ltNge ?ger0_real// ltnNge truncn_ge_nat. Qed.

Lemma real_truncn_le_nat x n : x \is Num.real ->
  (Num.trunc x <= n)%N = (x < n.+1%:R).
Proof. by move=> ?; rewrite real_ltNge// leqNgt truncn_gt_nat. Qed.

Lemma truncn_eq x n : 0 <= x -> (Num.trunc x == n) = (n%:R <= x < n.+1%:R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: trunc_itv|exact: trunc_def].
Qed.

Lemma le_truncn : {homo Num.trunc : x y / x <= y :> R >-> (x <= y)%N}.
Proof.
move=> x y lexy.
move: (trunc_floor x) (trunc_floor y).
case: ifP => [x0 _ | x0->//].
case: ifP => [y0 _ | + ->]; [|by rewrite (le_trans x0 lexy)].
move: (trunc_itv y0) => /andP[_ /(le_lt_trans lexy)].
move: (trunc_itv x0) => /andP[+ _] => /le_lt_trans/[apply].
by rewrite ltr_nat ltnS.
Qed.

Lemma real_floorD1_gt x : x \is Num.real -> x < (Num.floor x + 1)%:~R.
Proof. by move=> /real_floor_itv /andP[]. Qed.

Lemma real_floor_ge_int_tmp x n : x \is Num.real ->
  (n <= Num.floor x) = (n%:~R <= x).
Proof.
move=> /real_floor_itv /andP[lefx ltxf1]; apply/idP/idP => lenx.
  by apply: le_trans lefx; rewrite ler_int.
by rewrite -ltzD1 -(ltr_int R); apply: le_lt_trans ltxf1.
Qed.

#[deprecated(since="mathcomp 2.4.0",
  note="Use real_floor_ge_int_tmp instead.")]
Lemma real_floor_ge_int x n : x \is Num.real -> (n%:~R <= x) = (n <= Num.floor x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma real_floor_lt_int x n : x \is Num.real -> (Num.floor x < n) = (x < n%:~R).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_floor_ge_int_tmp -?ltNge.
Qed.

Lemma le_floor : {homo (@Num.floor R) : x y / x <= y}.
Proof. exact: floor_le. Qed.

Lemma real_floor_eq x n : x \is Num.real ->
  (Num.floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_floor_itv|exact: floor_def].
Qed.

Lemma real_floor_ge0 x : x \is Num.real -> (0 <= Num.floor x) = (0 <= x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma floor_lt0 x : (Num.floor x < 0) = (x < 0).
Proof.
have := archimedean.Num.Theory.floorP x; case: ifP => [xr _ | xr /eqP].
  by rewrite real_floor_lt_int.
rewrite -?[0%Z]/(@GRing.zero int) => <-.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ltr0_real.
Qed.

Lemma real_floor_le0 x : x \is Num.real -> (Num.floor x <= 0) = (x < 1).
Proof. by move=> ?; rewrite -ltzD1 add0r real_floor_lt_int. Qed.

Lemma floor_gt0 x : (Num.floor x > 0) = (x >= 1).
Proof.
have := archimedean.Num.Theory.floorP x; case: ifP => [xr _ | xr /eqP->].
  by rewrite gtz0_ge1 real_floor_ge_int_tmp.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ger1_real.
Qed.

Lemma floor_neq0 x : (Num.floor x != 0) = (x < 0) || (x >= 1).
Proof.
have := archimedean.Num.Theory.floorP x.
case: ifP => [xr _ | xr /eqP->]; rewrite ?eqxx/=.
  by rewrite neq_lt floor_lt0 floor_gt0.
by apply/esym/(contraFF _ xr) => /orP[]; [exact: ltr0_real|exact: ger1_real].
Qed.

Lemma real_ceil_le_int_tmp x n : x \is Num.real ->
  (Num.ceil x <= n) = (x <= n%:~R).
Proof.
rewrite -realN; move=> /(real_floor_ge_int_tmp (- n)).
by rewrite ?ceilNfloor mulrNz lerNl => ->; rewrite lerN2.
Qed.

#[deprecated(since="mathcomp 2.4.0",
  note="Use real_ceil_le_int_tmp instead.")]
Lemma real_ceil_le_int x n : x \is Num.real -> (x <= n%:~R) = (Num.ceil x <= n).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma real_ceil_gt_int x n : x \is Num.real -> (n < Num.ceil x) = (n%:~R < x).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_ceil_le_int_tmp ?ltNge.
Qed.

Lemma real_ceil_eq x n : x \is Num.real ->
  (Num.ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_ceil_itv|exact: ceil_def].
Qed.

Lemma le_ceil_tmp : {homo (@Num.ceil R) : x y / x <= y}.
Proof. exact: ceil_le. Qed.

Lemma real_ceil_ge0 x : x \is Num.real -> (0 <= Num.ceil x) = (-1 < x).
Proof.
by move=> ?; rewrite ?ceilNfloor oppr_ge0 real_floor_le0 ?realN// ltrNl.
Qed.

Lemma ceil_lt0 x : Num.ceil x < 0 = (x <= -1).
Proof. by rewrite ?ceilNfloor oppr_lt0 floor_gt0 lerNr. Qed.

Lemma real_ceil_le0 x : x \is Num.real -> (Num.ceil x <= 0) = (x <= 0).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma ceil_gt0 x : (Num.ceil x > 0) = (x > 0).
Proof. by rewrite ?ceilNfloor oppr_gt0 floor_lt0 oppr_lt0. Qed.

Lemma ceil_neq0 x : (Num.ceil x != 0) = (x <= -1) || (x > 0).
Proof. by rewrite ?ceilNfloor oppr_eq0 floor_neq0 oppr_lt0 lerNr orbC. Qed.

End num_trunc_floor_ceil.

Section trunc_floor_ceil.
Context {R : archiDomainType}.
Implicit Type x : R.

Lemma truncnS_gt x : x < (Num.trunc x).+1%:R.
Proof. exact: real_truncnS_gt. Qed.

Lemma truncn_le_nat x n : (Num.trunc x <= n)%N = (x < n.+1%:R).
Proof. exact: real_truncn_le_nat. Qed.

Lemma floorD1_gt x : x < (Num.floor x + 1)%:~R.
Proof. exact: real_floorD1_gt. Qed.

Lemma floor_ge_int_tmp x n : (n <= Num.floor x) = (n%:~R <= x).
Proof. exact: real_floor_ge_int_tmp. Qed.

Lemma floor_lt_int x n : (Num.floor x < n) = (x < n%:~R).
Proof. exact: real_floor_lt_int. Qed.

Lemma floor_eq x n : (Num.floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof. exact: real_floor_eq. Qed.

Lemma floor_ge0 x : (0 <= Num.floor x) = (0 <= x).
Proof. exact: real_floor_ge0. Qed.

Lemma floor_le0 x : (Num.floor x <= 0) = (x < 1).
Proof. exact: real_floor_le0. Qed.

#[deprecated(since="mathcomp 2.4.0", note="Use ceil_le_int_tmp instead.")]
Lemma ceil_le_int x n : x <= n%:~R = (Num.ceil x <= n).
Proof. exact: real_ceil_le_int. Qed.

Lemma ceil_le_int_tmp x n : (Num.ceil x <= n) = (x <= n%:~R).
Proof. exact: real_ceil_le_int_tmp. Qed.

Lemma ceil_gt_int x n : (n < Num.ceil x) = (n%:~R < x).
Proof. exact: real_ceil_gt_int. Qed.

Lemma ceil_eq x n : (Num.ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof. exact: real_ceil_eq. Qed.

Lemma ceil_ge0 x : (0 <= Num.ceil x) = (-1 < x).
Proof. exact: real_ceil_ge0. Qed.

Lemma ceil_le0 x : (Num.ceil x <= 0) = (x <= 0).
Proof. exact: real_ceil_le0. Qed.

End trunc_floor_ceil.

Lemma natr_int {R : archiNumDomainType} n : n%:R \is a @Num.int R.
Proof. by rewrite Num.Theory.intrEge0. Qed.

Lemma inr_inj {A B} : injective (@inr A B).
Proof. by move=>  ? ? []. Qed.

Lemma inl_inj {A B} : injective (@inl A B).
Proof. by move=>  ? ? []. Qed.

Lemma eq_exists2l (A : Type) (P P' Q : A -> Prop) :
  (forall x, P x <-> P' x) ->
  (exists2 x, P x & Q x) <-> (exists2 x, P' x & Q x).
Proof.
by move=> eqQ; split=> -[x p q]; exists x; move: p q; rewrite ?eqQ.
Qed.

Lemma eq_exists2r (A : Type) (P Q Q' : A -> Prop) :
  (forall x, Q x <-> Q' x) ->
  (exists2 x, P x & Q x) <-> (exists2 x, P x & Q' x).
Proof.
by move=> eqP; split=> -[x p q]; exists x; move: p q; rewrite ?eqP.
Qed.
