(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals interval_inference ereal.
From mathcomp Require Import topology normedtype sequences esum measure.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral.

(**md**************************************************************************)
(* # Kernels                                                                  *)
(*                                                                            *)
(* This file provides a formation of kernels, s-finite kernels,               *)
(* sigma-finite kernels, finite transition kernels, finite kernels,           *)
(* subprobability kernels, and probability kernels, organized as a hierarchy  *)
(* of mathematical structures. The main formalized results are stability by   *)
(* composition for s-finite kernels [Lemma 3, Staton, ESOP 2017] and          *)
(* subprobability kernels [Theorem 14.26, Klenke 2014].                       *)
(*                                                                            *)
(* References:                                                                *)
(* - R. Affeldt, C. Cohen, A. Saito. Semantics of probabilistic programs      *)
(*   using s-finite kernels in Coq. CPP 2023                                  *)
(* - S. Staton. Commutative Semantics for Probabilistic Programming.          *)
(*   ESOP 2017                                                                *)
(* - A. Klenke. Probability theory: A comprehensive course. 2014              *)
(*                                                                            *)
(* ```                                                                        *)
(*       R.-ker X ~> Y == kernel from X to Y where X and Y are of type        *)
(*                        measurableType                                      *)
(*                        The HB class is Kernel.                             *)
(*             kseries == countable sum of kernels                            *)
(*                        It is declared as an instance of the structure      *)
(*                        Kernel. It will also be shown to be an instance of  *)
(*                        SFiniteKernel if the sum is over s-finite kernels.  *)
(*   measure_fam_uub k == the kernel k is uniformly upper-bounded             *)
(*     R.-sfker X ~> Y == s-finite kernel                                     *)
(*                        The HB class is SFiniteKernel.                      *)
(*               kzero == kernel defined using the mzero measure              *)
(* R.-sigmafker X ~> Y == sigma-finite transition kernel                      *)
(*                        The HB class is SigmaFiniteTransitionKernel.        *)
(*     R.-ftker X ~> Y == finite transition kernel                            *)
(*                        The HB class is FiniteTransitionKernel.             *)
(*      R.-fker X ~> Y == finite kernel                                       *)
(*                        The HB class is FiniteKernel.                       *)
(*     R.-spker X ~> Y == subprobability kernel                               *)
(*                        The HB class is SubProbabilityKernel.               *)
(*      R.-pker X ~> Y == probability kernel                                  *)
(*                        The HB class is ProbabilityKernel.                  *)
(*           kdirac mf == kernel defined by a measurable function             *)
(*      kprobability m == kernel defined by a probability measure             *)
(*          kadd k1 k2 == lifting of the addition of measures to kernels      *)
(*      knormalize f P := fun x => mnormalize (f x) P                         *)
(*           kcomp l k == "parameterized" composition for kernels             *)
(*                        l has type X -> {measure set Y -> \bar R}           *)
(*                        k has type X * Y -> {measure set Z -> \bar R}       *)
(*                        kcomp l k as type X -> set Z -> \bar R              *)
(*              l \; k == same as kcomp l k but equipped with the type        *)
(*                        X -> {measure set Z -> \bar R}                      *)
(*          kfcomp k f == composition of a "kernel" and a function            *)
(*                        k has type X -> {measure set Y -> \bar R}.          *)
(*      kproduct k1 k2 == "parameterized" product of kernels                  *)
(*                        k1 has type T0 -> {measure set T1 -> \bar R}.       *)
(*                        k2 has type T0 * T1 -> {measure set T2 -> \bar R}.  *)
(*                        The result has type T0 -> set (T1 * T2) -> \bar R.  *)
(*     mkproduct k1 k2 == same as kproduct k1 k2 but equipped with the type   *)
(*                        T0 -> {measure set (T1 * T2) -> \bar R}             *)
(*  kproduct_snd k1 k2 := kproduct k1 (k2 \o snd)                             *)
(*                        k2 has T1 -> {measure set T2 -> \bar R}             *)
(*                        It "ignores" the first argument of k2.              *)
(* kcomp_noparam k1 k2 := composition of kernels                              *)
(*                        k1 has type T0 -> {measure set T1 -> \bar R}.       *)
(*                        k2 has type T1 -> {measure set T2 -> \bar R}.       *)
(*                        The return type is T0 -> set (T1 * T2) -> \bar R    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Reserved Notation "R .-ker X ~> Y"
  (at level 42, format "R .-ker  X  ~>  Y").
Reserved Notation "R .-sfker X ~> Y"
  (at level 42, format "R .-sfker  X  ~>  Y").
Reserved Notation "R .-sigmafker X ~> Y"
  (at level 42, format "R .-sigmafker  X  ~>  Y").
Reserved Notation "R .-ftker X ~> Y"
  (at level 42, format "R .-ftker  X  ~>  Y").
Reserved Notation "R .-fker X ~> Y"
  (at level 42, format "R .-fker  X  ~>  Y").
Reserved Notation "R .-spker X ~> Y"
  (at level 42, format "R .-spker  X  ~>  Y").
Reserved Notation "R .-pker X ~> Y"
  (at level 42, format "R .-pker  X  ~>  Y").

HB.mixin Record isKernel d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  measurable_kernel :
    forall U, measurable U -> measurable_fun [set: X] (k ^~ U) }.

#[short(type=kernel)]
HB.structure Definition Kernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k & isKernel _ _ X Y R k }.
Notation "R .-ker X ~> Y" := (kernel X%type Y R).

Arguments measurable_kernel {_ _ _ _ _} _.

Lemma kernel_measurable_eq_cst d d' (T : measurableType d)
    (T' : measurableType d') (R : realType) (f : R.-ker T ~> T') k :
  measurable [set t | f t [set: T'] == k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` [set k]); last first.
  by apply/seteqP; split => t/= /eqP.
have /(_ measurableT [set k]) := measurable_kernel f setT measurableT.
by rewrite setTI; exact.
Qed.

Lemma kernel_measurable_neq_cst d d' (T : measurableType d)
    (T' : measurableType d') (R : realType)  (f : R.-ker T ~> T') k :
  measurable [set t | f t [set: T'] != k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` [set~ k]); last first.
  by apply/seteqP; split => t /eqP.
have /(_ measurableT [set~ k]) := measurable_kernel f setT measurableT.
by rewrite setTI; apply => //; exact: measurableC.
Qed.

Lemma kernel_measurable_fun_eq_cst d d' (T : measurableType d)
    (T' : measurableType d') (R : realType) (f : R.-ker T ~> T') k :
  measurable_fun [set: T] (fun t => f t [set: T'] == k).
Proof.
move=> _ /= B mB; rewrite setTI.
have [/eqP->|/eqP->|/eqP->|/eqP->] := set_bool B.
- exact: kernel_measurable_eq_cst.
- rewrite (_ : _ @^-1` _ = [set b | f b setT != k]); last first.
    by apply/seteqP; split => [t /negbT//|t /negbTE].
  exact: kernel_measurable_neq_cst.
- by rewrite preimage_set0.
- by rewrite preimage_setT.
Qed.

Lemma eq_kernel d d' (T : measurableType d) (T' : measurableType d')
    (R : realType) (k1 k2 : R.-ker T ~> T') :
  (forall x U, k1 x U = k2 x U) -> k1 = k2.
Proof.
move: k1 k2 => [m1 [[?]]] [m2 [[?]]] /= k12.
have ? : m1 = m2.
  by apply/funext => t; apply/eq_measure; apply/funext => U; rewrite k12.
by subst m1; f_equal; f_equal; f_equal; apply/Prop_irrelevance.
Qed.

Section kseries.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable k : (R.-ker X ~> Y)^nat.

Definition kseries (x : X) : {measure set Y -> \bar R} := mseries (k ^~ x) 0.

Lemma measurable_fun_kseries (U : set Y) :
  measurable U -> measurable_fun [set: X] (kseries ^~ U).
Proof.
by move=> mU; apply: ge0_emeasurable_sum => // n _; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ kseries measurable_fun_kseries.

End kseries.

Lemma integral_kseries d d' (X : measurableType d) (Y : measurableType d')
  (R : realType) (k : (R.-ker X ~> Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun [set: Y] f ->
  \int[kseries k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /kseries/= ge0_integral_measure_series.
Qed.

Section measure_fam_uub.
Context d d' (X : measurableType d) (Y : measurableType d') (R : numFieldType).
Variable k : X -> {measure set Y -> \bar R}.

Definition measure_fam_uub := exists r, forall x, k x [set: Y] < r%:E.

Lemma measure_fam_uubP : measure_fam_uub <->
  exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E.
Proof.
split => [|] [r kr]; last by exists r%:num.
suff r_gt0 : (0 < r)%R by exists (PosNum r_gt0).
by rewrite -lte_fin; exact: le_lt_trans (kr point).
Qed.

End measure_fam_uub.

HB.mixin Record isSFiniteKernel_subdef d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) := {
  sfinite_kernel_subdef : exists2 s : (R.-ker X ~> Y)^nat,
    forall n, measure_fam_uub (s n) &
    forall x U, measurable U -> k x U = kseries s x U }.

#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isSFiniteKernel_subdef instead.")]
Notation Kernel_isSFinite_subdef x1 x2 x3 x4 x5 x6 :=
  (isSFiniteKernel_subdef x1 x2 x3 x4 x5 x6).

Module Kernel_isSFinite_subdef.
#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isSFiniteKernel_subdef.Build instead.")]
Notation Build x1 x2 x3 x4 x5 x6 :=
  (isSFiniteKernel_subdef.Build x1 x2 x3 x4 x5 x6) (only parsing).
End Kernel_isSFinite_subdef.

HB.structure Definition SFiniteKernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ R k &
         isSFiniteKernel_subdef _ _ X Y R k }.
Notation "R .-sfker X ~> Y" := (SFiniteKernel.type X%type Y R).
Arguments sfinite_kernel_subdef {_ _ _ _ _} _.

Lemma eq_sfkernel d d' (T : measurableType d) (T' : measurableType d')
    (R : realType) (k1 k2 : R.-sfker T ~> T') :
  (forall x U, k1 x U = k2 x U) -> k1 = k2.
Proof.
move: k1 k2 => [m1 [[?] [?]]] [m2 [[?] [?]]] /= k12.
have ? : m1 = m2.
  by apply/funext => t; apply/eq_measure; apply/funext => U; rewrite k12.
by subst m1; f_equal; f_equal; f_equal; apply/Prop_irrelevance.
Qed.

Section kzero.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition kzero (_ : X) : {measure set Y -> \bar R} := mzero.

Let measurable_fun_kzero U : measurable U ->
  measurable_fun [set: X] (kzero ^~ U).
Proof. by move=> ?/=; exact: measurable_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ X Y R kzero measurable_fun_kzero.

Lemma kzero_uub : measure_fam_uub kzero.
Proof. by exists 1%R => /= t; rewrite /mzero/=. Qed.

End kzero.

(* interface for sigma-finite kernel *)
HB.mixin Record isSigmaFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  kernel_sigma_finite : forall x, sigma_finite [set: Y] (k x) }.

#[short(type=sigma_finite_kernel)]
HB.structure Definition SigmaFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ _ k &
         isSigmaFiniteTransitionKernel _ _ X Y R k }.

Notation "R .-sigmafker X ~> Y" := (sigma_finite_kernel X%type Y R).

(* interface for finite transition kernel *)
HB.mixin Record isFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  kernel_finite_transition : forall x, fin_num_fun (k x) }.

#[deprecated(since="mathcomp-analysis 1.11.0",
             note="Use isFiniteTransitionKernel instead.")]
Notation isFiniteTransition x1 x2 x3 x4 x5 x6 :=
  (isFiniteTransitionKernel x1 x2 x3 x4 x5 x6).

#[short(type=finite_transition_kernel)]
HB.structure Definition FiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @SFiniteKernel _ _ _ _ _ k &
         isFiniteTransitionKernel _ _ X Y R k }.

Module isFiniteTransition.
#[deprecated(since="mathcomp-analysis 1.11.0",
             note="Use isFiniteTransitionKernel.Build instead.")]
Notation Build x1 x2 x3 x4 x5 x6 :=
  (isFiniteTransitionKernel.Build x1 x2 x3 x4 x5 x6) (only parsing).
End isFiniteTransition.

Notation "R .-ftker X ~> Y" := (finite_transition_kernel X%type Y R).

HB.mixin Record isMeasureFamUub d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) := {
  measure_uub : measure_fam_uub k }.

#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isMeasureFamUub instead.")]
Notation SFiniteKernel_isFinite x1 x2 x3 x4 x5 x6 :=
  (isMeasureFamUub x1 x2 x3 x4 x5 x6).

Module SFiniteKernel_isFinite.
#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isMeasureFamUub.Build instead.")]
Notation Build x1 x2 x3 x4 x5 x6 :=
  (isMeasureFamUub.Build x1 x2 x3 x4 x5 x6) (only parsing).
End SFiniteKernel_isFinite.

#[short(type=finite_kernel)]
HB.structure Definition FiniteKernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @FiniteTransitionKernel _ _ _ _ _ k &
         isMeasureFamUub _ _ X Y R k }.
Notation "R .-fker X ~> Y" := (finite_kernel X%type Y R).
Arguments measure_uub {_ _ _ _ _} _.

HB.factory Record Kernel_isFinite d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) of isKernel _ _ _ _ _ k := {
  measure_uub : measure_fam_uub k }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
  (R : realType) k of Kernel_isFinite d d' X Y R k.

Let sfinite_finite :
  exists2 k_ : (R.-ker _ ~> _)^nat, forall n, measure_fam_uub (k_ n) &
    forall x U, measurable U -> k x U = mseries (k_ ^~ x) 0 U.
Proof.
exists (fun n => if n is O return R.-ker X ~> Y then k else @kzero _ _ X Y R).
  by case => [|_]; [exact: measure_uub|exact: kzero_uub].
move=> t U mU/=; rewrite /mseries.
rewrite (nneseries_split _ 1%N)// big_mkord big_ord_recl/= big_ord0 adde0.
rewrite ereal_series (@eq_eseriesr _ _ (fun=> 0)); last by case.
by rewrite eseries0// adde0.
Qed.

HB.instance Definition _ :=
  @isSFiniteKernel_subdef.Build d d' X Y R k sfinite_finite.

Let kernel_sigma_finite x : sigma_finite setT (k x).
Proof.
apply: fin_num_fun_sigma_finite; first by rewrite measure0.
apply: lty_fin_num_fun.
by have [r kr] := measure_uub; rewrite (lt_trans (kr x)) ?ltry.
Qed.

HB.instance Definition _ :=
  @isSigmaFiniteTransitionKernel.Build d d' X Y R k kernel_sigma_finite.

Let finite_transition_finite : forall x, fin_num_fun (k x).
Proof.
move=> x U mU.
have [r kr] := measure_uub.
rewrite ge0_fin_numE//.
rewrite (@le_lt_trans _ _ (k x setT)) ?le_measure ?inE//.
by rewrite (lt_trans (kr x)) ?ltry.
Qed.

HB.instance Definition _ :=
  @isFiniteTransitionKernel.Build d d' X Y R k finite_transition_finite.

HB.instance Definition _ :=
  @isMeasureFamUub.Build d d' X Y R k measure_uub.

HB.end.

Section sfinite.
Context d d' (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-sfker X ~> Y).

Let s : (X -> {measure set Y -> \bar R})^nat :=
  let: exist2 x _ _ := cid2 (sfinite_kernel_subdef k) in x.

Let ms n : @isKernel d d' X Y R (s n).
Proof.
split; rewrite /s; case: cid2 => /= s' s'_uub kE.
exact: measurable_kernel.
Qed.

HB.instance Definition _ n := ms n.

Let s_uub n : measure_fam_uub (s n).
Proof. by rewrite /s; case: cid2. Qed.

HB.instance Definition _ n := @Kernel_isFinite.Build d d' X Y R (s n) (s_uub n).

Lemma sfinite_kernel : exists s : (R.-fker X ~> Y)^nat,
  forall x U, measurable U -> k x U = kseries s x U.
Proof. by exists s => x U mU; rewrite /s /= /s; case: cid2 => ? ? ->. Qed.

End sfinite.

Lemma sfinite_kernel_measure d d' (Z : measurableType d) (X : measurableType d')
    (R : realType) (k : R.-sfker Z ~> X) (z : Z) :
  sfinite_measure (k z).
Proof.
have [s ks] := sfinite_kernel k.
exists (s ^~ z).
  move=> n; have [r snr] := measure_uub (s n).
  by apply: lty_fin_num_fun; rewrite (lt_le_trans (snr _))// leey.
by move=> U mU; rewrite ks.
Qed.

HB.instance Definition _
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  @Kernel_isFinite.Build _ _ _ _ R (@kzero _ _ X Y R)
                                   (@kzero_uub _ _ X Y R).

HB.factory Record Kernel_isSFinite d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) of isKernel _ _ _ _ _ k := {
  sfinite : exists s : (R.-fker X ~> Y)^nat,
    forall x U, measurable U -> k x U = kseries s x U }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
  (R : realType) k of Kernel_isSFinite d d' X Y R k.

Lemma sfinite_subdef : isSFiniteKernel_subdef d d' X Y R k.
Proof.
split; have [s sE] := sfinite; exists s => //.
by move=> n; exact: measure_uub.
Qed.

HB.instance Definition _ := sfinite_subdef.

HB.end.

Section sfkseries.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables k : (R.-sfker X ~> Y)^nat.

Let sfinite_kseries : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kseries k x U = mseries (k_ ^~ x) 0 U.
Proof.
have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
  by rewrite card_eq_sym; exact: card_nat2.
pose p n : (R.-fker X ~> Y)^nat := sval (cid (sfinite_kernel (k n))).
exists (fun i => p (f i).1 (f i).2).
  move=> n; have [r Hr] := measure_uub (p (f n).1 (f n).2).
  by exists r => x /=; exact: Hr.
move=> x U mU; rewrite /kseries /mseries/= /mseries/=.
have kE i : k i x U = \sum_(j <oo) p i j x U.
  by rewrite /p /sval/=; case: cid => k_ ->.
transitivity (\esum_(l in [set: nat] `*` [set: nat]) p l.1 l.2 x U).
  rewrite (_ : _ `*` _ = setT `*`` (fun=> setT)); last by apply/seteqP; split.
  rewrite -(@esum_esum _ _ _ _ _ (fun i j => p i j x U))//.
  rewrite nneseries_esumT//; apply: eq_esum => i _.
  by rewrite kE// nneseries_esumT.
rewrite (reindex_esum [set: nat] _ f)//; last first.
  have := @bijTT _ _ f.
  by rewrite -setTT_bijective/= -[in X in set_bij _ X _ -> _](@setXTT nat nat).
by rewrite nneseries_esumT//; exact: eq_esum.
Qed.

HB.instance Definition _ :=
  isSFiniteKernel_subdef.Build _ _ _ _ R (kseries k) sfinite_kseries.
End sfkseries.

HB.mixin Record isSubProbabilityKernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) := {
  sprob_kernel : ereal_sup [set k x [set: Y] | x in [set: X]] <= 1 }.

#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isSubProbabilityKernel instead.")]
Notation FiniteKernel_isSubProbability x1 x2 x3 x4 x5 x6 :=
  (isSubProbabilityKernel x1 x2 x3 x4 x5 x6).

Module FiniteKernel_isSubProbability.
#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isSubProbabilityKernel.Build instead.")]
Notation Build x1 x2 x3 x4 x5 x6 :=
  (isSubProbabilityKernel.Build x1 x2 x3 x4 x5 x6) (only parsing).
End FiniteKernel_isSubProbability.

#[short(type=sprobability_kernel)]
HB.structure Definition SubProbabilityKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @FiniteKernel _ _ _ _ _ k &
         isSubProbabilityKernel _ _ X Y R k }.
Notation "R .-spker X ~> Y" := (sprobability_kernel X%type Y R).

Lemma sprob_kernelP d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> set Y -> \bar R) :
  ereal_sup [set k x [set: _] | x in [set: _]] <= 1 <->
  forall x, k x [set: Y] <= 1.
Proof.
split => [+ x|k1]; last by apply: ge_ereal_sup => _ /= [z _ <-]; exact: k1.
by apply/le_trans/ereal_sup_ubound => /=; exists x.
Qed.

Lemma sprob_kernel_le1 d d' (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-spker X ~> Y) x :
  k x [set: Y] <= 1.
Proof. by apply: (sprob_kernelP (fun x A => k x A)).1; exact: sprob_kernel. Qed.

HB.factory Record Kernel_isSubProbability d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) of isKernel _ _ X Y R k := {
  sprob_kernel : ereal_sup [set k x [set: Y] | x in [set: X]] <= 1 }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
  (R : realType) k of Kernel_isSubProbability d d' X Y R k.

Let finite : @Kernel_isFinite d d' X Y R k.
Proof.
split; exists 2%R => /= ?; rewrite (@le_lt_trans _ _ 1%:E) ?lte_fin ?ltr1n//.
by rewrite (le_trans _ sprob_kernel)//; exact: ereal_sup_ubound.
Qed.

HB.instance Definition _ := finite.

HB.instance Definition _ :=
  @isSubProbabilityKernel.Build _ _ _ _ _ k sprob_kernel.

HB.end.

HB.mixin Record isProbabilityKernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) := {
  prob_kernel : forall x, k x [set: Y] = 1 }.

#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isProbabilityKernel instead.")]
Notation SubProbability_isProbability x1 x2 x3 x4 x5 x6 :=
  (isProbabilityKernel x1 x2 x3 x4 x5 x6).

Module SubProbability_isProbability.
#[deprecated(since="mathcomp-analysis 1.10.0",
             note="Use isProbabilityKernel.Build instead.")]
Notation Build x1 x2 x3 x4 x5 x6 :=
  (isProbabilityKernel.Build x1 x2 x3 x4 x5 x6) (only parsing).
End SubProbability_isProbability.

#[short(type=probability_kernel)]
HB.structure Definition ProbabilityKernel d d'
    (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @SubProbabilityKernel _ _ _ _ _ k &
         isProbabilityKernel _ _ X Y R k }.
Notation "R .-pker X ~> Y" := (probability_kernel X%type Y R).

HB.factory Record Kernel_isProbability d d'
    (X : measurableType d) (Y : measurableType d') (R : realType)
    (k : X -> {measure set Y -> \bar R}) of isKernel _ _ X Y R k := {
  prob_kernel : forall x, k x [set: Y] = 1 }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
  (R : realType) k of Kernel_isProbability d d' X Y R k.

Let sprob_kernel : @Kernel_isSubProbability d d' X Y R k.
Proof.
by split; apply: ge_ereal_sup => x [y _ <-{x}]; rewrite prob_kernel.
Qed.

HB.instance Definition _ := sprob_kernel.

HB.instance Definition _ :=
  @isProbabilityKernel.Build _ _ _ _ _ k prob_kernel.

HB.end.

Lemma finite_kernel_measure d d' (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-fker X ~> Y) (x : X) :
  fin_num_fun (k x).
Proof.
have [r k_r] := measure_uub k.
by apply: lty_fin_num_fun; rewrite (@lt_trans _ _ r%:E) ?ltey.
Qed.

(* see measurable_prod_subset in lebesgue_integral.v;
   the differences between the two are:
   - m2 is a kernel instead of a measure (the proof uses the
     measurability of each measure of the family)
   - as a consequence, m2D_bounded holds for all x *)
Section measurable_prod_subset_kernel.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Implicit Types A : set (X * Y).

Section xsection_kernel.
Variable (k : R.-ker X ~> Y) (D : set Y) (mD : measurable D).
Let kD x := mrestr (k x) mD.
HB.instance Definition _ x := Measure.on (kD x).
Let phi A := fun x => kD x (xsection A x).
Let XY := [set A | measurable A /\ measurable_fun [set: X] (phi A)].

Let phiM (A : set X) B : phi (A `*` B) = (fun x => kD x B * (\1_A x)%:E).
Proof.
rewrite funeqE => x; rewrite indicE /phi/=.
have [xA|xA] := boolP (x \in A); first by rewrite mule1 in_xsectionX.
by rewrite mule0 notin_xsectionX// set0I measure0.
Qed.

Lemma measurable_prod_subset_xsection_kernel :
    (forall x, exists M, forall X, measurable X -> kD x X < M%:E) ->
  measurable `<=` XY.
Proof.
move=> kD_ub; rewrite measurable_prod_measurableType.
set C := [set A `*` B | A in measurable & B in measurable].
have CI : setI_closed C.
  move=> _ _ [X1 mX1 [X2 mX2 <-]] [Y1 mY1 [Y2 mY2 <-]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setXTT.
have CXY : C `<=` XY.
  move=> _ [A mA [B mB <-]]; split; first exact: measurableX.
  rewrite phiM.
  apply: emeasurable_funM => //; first exact/measurable_kernel/measurableI.
  by apply/measurable_EFinP; rewrite (_ : \1_ _ = mindic R mA).
suff lsystemB : lambda_system setT XY by exact: lambda_system_subset.
split => //; [exact: CXY| |exact: xsection_ndseq_closed].
move=> A B BA [mA mphiA] [mB mphiB]; split; first exact: measurableD.
suff : phi (A `\` B) = (fun x => phi A x - phi B x).
  by move=> ->; exact: emeasurable_funB.
rewrite funeqE => x; rewrite /phi/= xsectionD// measureD.
- by rewrite setIidr//; exact: le_xsection.
- exact: measurable_xsection.
- exact: measurable_xsection.
- have [M kM] := kD_ub x.
  rewrite (lt_le_trans (kM (xsection A x) _)) ?leey//.
  exact: measurable_xsection.
Qed.

End xsection_kernel.

End measurable_prod_subset_kernel.

(* see measurable_fun_xsection in lebesgue_integral.v
   the difference is that this section uses a finite kernel m2
   instead of a sigma-finite measure m2 *)
Section measurable_fun_xsection_finite_kernel.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable k : R.-fker X ~> Y.
Implicit Types A : set (X * Y).

Let phi A := fun x => k x (xsection A x).
Let XY := [set A | measurable A /\ measurable_fun [set: X] (phi A)].

Lemma measurable_fun_xsection_finite_kernel A :
  A \in measurable -> measurable_fun [set: X] (phi A).
Proof.
move: A; suff : measurable `<=` XY by move=> + A; rewrite inE => /[apply] -[].
move=> /= A mA; rewrite /XY/=; split => //; rewrite (_ : phi _ =
    (fun x => mrestr (k x) measurableT (xsection A x))); last first.
  by apply/funext => x//=; rewrite /mrestr setIT.
apply measurable_prod_subset_xsection_kernel => // x.
have [r hr] := measure_uub k; exists r => B mB.
by rewrite (le_lt_trans _ (hr x)) // /mrestr /= setIT le_measure// inE.
Qed.

End measurable_fun_xsection_finite_kernel.

Section measurable_fun_integral_finite_sfinite.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable k : X * Y -> \bar R.

Import HBNNSimple.

Lemma measurable_fun_xsection_integral
    (l : X -> {measure set Y -> \bar R})
    (k_ : {nnsfun (X * Y) >-> R}^nat)
    (ndk_ : nondecreasing_seq (k_ : (X * Y -> R)^nat))
    (k_k : forall z, (k_ n z)%:E @[n --> \oo] --> k z) :
  (forall n r,
    measurable_fun [set: X] (fun x => l x (xsection (k_ n @^-1` [set r]) x))) ->
  measurable_fun [set: X] (fun x => \int[l x]_y k (x, y)).
Proof.
move=> h.
rewrite (_ : (fun x => _) =
    (fun x => limn_esup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funext => x.
  transitivity (lim (\int[l x]_y (k_ n (x, y))%:E @[n --> \oo])); last first.
    rewrite is_cvg_limn_esupE//.
    apply: ereal_nondecreasing_is_cvgn => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y _; rewrite lee_fin.
    - exact/measurable_EFinP/measurableT_comp.
    - exact/measurable_EFinP/measurableT_comp.
    - by move=> y _; rewrite lee_fin; exact/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/measurable_EFinP/measurableT_comp.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/ndk_.
apply: measurable_fun_limn_esup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \int[l x]_y
    (\sum_(r \in range (k_ n))
      r * \1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \sum_(r \in range (k_ n))
    (\int[l x]_y (r * \1_(k_ n @^-1` [set r]) (x, y))%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_fsum//.
  - by apply: eq_integral => y _; rewrite -fsumEFin.
  - move=> r.
    apply/measurable_EFinP/measurableT_comp => [//|].
    exact/measurableT_comp.
  - by move=> m y _; rewrite nnfun_muleindic_ge0.
apply: emeasurable_fsum => // r.
rewrite [X in measurable_fun _ X](_ : _ = fun x => r%:E *
    \int[l x]_y (\1_(k_ n @^-1` [set r]) (x, y))%:E); last first.
  apply/funext => x; under eq_integral do rewrite EFinM.
  have [r0|r0] := leP 0%R r.
    by rewrite ge0_integralZl//; exact/measurable_EFinP/measurableT_comp.
  rewrite integral0_eq; last first.
    by move=> y _; rewrite preimage_nnfun0// indic0 mule0.
  by rewrite integral0_eq ?mule0// => y _; rewrite preimage_nnfun0// indic0.
apply/measurable_funeM.
rewrite (_ : (fun x => _) = (fun x => l x (xsection (k_ n @^-1` [set r]) x))).
  exact/h.
apply/funext => x; rewrite integral_indic//; last first.
  rewrite (_ : (fun x => _) = xsection (k_ n @^-1` [set r]) x).
    exact: measurable_xsection.
  by rewrite /xsection; apply/seteqP; split=> y/= /[!inE].
congr (l x _); apply/funext => y1/=; rewrite /xsection/= inE.
by apply/propext; tauto.
Qed.

Lemma measurable_fun_integral_finite_kernel (l : R.-fker X ~> Y)
    (k0 : forall z, 0 <= k z) (mk : measurable_fun [set: X * Y] k) :
  measurable_fun [set: X] (fun x => \int[l x]_y k (x, y)).
Proof.
pose k_ := nnsfun_approx measurableT mk.
apply: (@measurable_fun_xsection_integral _ k_).
- by move=> a b ab; exact/nd_nnsfun_approx.
- by move=> z; exact/cvg_nnsfun_approx.
- move => n r.
  have [l_ hl_] := measure_uub l.
  by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

Lemma measurable_fun_integral_sfinite_kernel (l : R.-sfker X ~> Y)
    (k0 : forall t, 0 <= k t) (mk : measurable_fun [set: X * Y] k) :
  measurable_fun [set: X] (fun x => \int[l x]_y k (x, y)).
Proof.
pose k_ := nnsfun_approx measurableT mk.
apply: (@measurable_fun_xsection_integral _ k_).
- by move=> a b ab; exact/nd_nnsfun_approx.
- by move=> z; exact/cvg_nnsfun_approx.
- move => n r.
  have [l_ hl_] := sfinite_kernel l.
  rewrite (_ : (fun x => _) = (fun x =>
      mseries (l_ ^~ x) 0 (xsection (k_ n @^-1` [set r]) x))); last first.
    by apply/funext => x; rewrite hl_//; exact/measurable_xsection.
  apply: ge0_emeasurable_sum => // m _.
  by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

End measurable_fun_integral_finite_sfinite.
Arguments measurable_fun_xsection_integral {_ _ _ _ _} k l.
Arguments measurable_fun_integral_finite_kernel {_ _ _ _ _} k l.
Arguments measurable_fun_integral_sfinite_kernel {_ _ _ _ _} k l.

Section kdirac.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable f : X -> Y.

Definition kdirac (mf : measurable_fun [set: X] f) (x : X) :
  {measure set Y -> \bar R} := dirac (f x).

Hypothesis mf : measurable_fun [set: X] f.

Let measurable_fun_kdirac U : measurable U ->
  measurable_fun [set: X] (kdirac mf ^~ U).
Proof.
move=> mU; apply/measurable_EFinP.
by rewrite (_ : (fun x => _) = mindic R mU \o f)//; exact/measurableT_comp.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (kdirac mf)
  measurable_fun_kdirac.

Let kdirac_prob x : kdirac mf x [set: Y] = 1.
Proof. by rewrite /kdirac/= diracT. Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ _
  (kdirac mf) kdirac_prob.

End kdirac.
Arguments kdirac {d d' X Y R f}.

Section kprobability.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable P : X -> pprobability Y R.

Definition kprobability (mP : measurable_fun [set: X] P)
  : X -> {measure set Y -> \bar R} := P.

Hypothesis mP : measurable_fun [set: X] P.

Let measurable_fun_kprobability U : measurable U ->
  measurable_fun [set: X] (kprobability mP ^~ U).
Proof.
move=> mU.
apply: (measurability _ (ErealGenInftyO.measurableE R)) => _ /= -[_ [r ->] <-].
rewrite setTI preimage_itvNyo -/(P @^-1` mset U r).
have [r0|r0] := leP 0%R r; last by rewrite lt0_mset// preimage_set0.
have [r1|r1] := leP r 1%R; last by rewrite gt1_mset// preimage_setT.
move: mP => /(_ measurableT (mset U r)); rewrite setTI; apply.
by apply: sub_sigma_algebra; exists r => /=; [rewrite in_itv/= r0|exists U].
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ X Y R (kprobability mP) measurable_fun_kprobability.

Let kprobability_prob x : kprobability mP x [set: Y] = 1.
Proof. by rewrite /kprobability/= probability_setT. Qed.

HB.instance Definition _ :=
  @Kernel_isProbability.Build _ _ X Y R (kprobability mP) kprobability_prob.

End kprobability.

Section kadd.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables k1 k2 : R.-ker X ~> Y.

Definition kadd (x : X) : {measure set Y -> \bar R} :=
  measure_add (k1 x) (k2 x).

Let measurable_fun_kadd U : measurable U -> measurable_fun [set: X] (kadd ^~ U).
Proof.
move=> mU; rewrite /kadd.
rewrite (_ : (fun _ => _) = (fun x => k1 x U + k2 x U)); last first.
  by apply/funext => x; rewrite -measure_addE.
by apply: emeasurable_funD; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ _ _ _ kadd measurable_fun_kadd.

End kadd.

Section sfkadd.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables k1 k2 : R.-sfker X ~> Y.

Let sfinite_kadd : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U ->
    kadd k1 k2 x U = mseries (k_ ^~ x) 0 U.
Proof.
have [f1 hk1] := sfinite_kernel k1; have [f2 hk2] := sfinite_kernel k2.
exists (fun n => kadd (f1 n) (f2 n)).
  move=> n.
  have [r1 f1r1] := measure_uub (f1 n).
  have [r2 f2r2] := measure_uub (f2 n).
  exists (r1 + r2)%R => x/=.
  by rewrite /msum !big_ord_recr/= big_ord0 add0e EFinD lteD.
move=> x U mU.
rewrite /kadd/= -/(measure_add (k1 x) (k2 x)) measure_addE hk1//= hk2//=.
rewrite /mseries -nneseriesD//; apply: eq_eseriesr => n _ /=.
by rewrite -/(measure_add (f1 n x) (f2 n x)) measure_addE.
Qed.

HB.instance Definition _ t :=
  isSFiniteKernel_subdef.Build _ _ _ _ R (kadd k1 k2) sfinite_kadd.

End sfkadd.

Section fkadd.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables k1 k2 : R.-fker X ~> Y.

Let kadd_finite_uub : measure_fam_uub (kadd k1 k2).
Proof.
have [f1 hk1] := measure_uub k1; have [f2 hk2] := measure_uub k2.
exists (f1 + f2)%R => x; rewrite /kadd /=.
rewrite -/(measure_add (k1 x) (k2 x)).
by rewrite measure_addE EFinD; exact: lteD.
Qed.

HB.instance Definition _ t :=
  Kernel_isFinite.Build _ _ _ _ R (kadd k1 k2) kadd_finite_uub.

End fkadd.

Section knormalize.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variable f : R.-ker X ~> Y.

Definition knormalize (P : probability Y R) : X -> {measure set Y -> \bar R} :=
  fun x => mnormalize (f x) P.

Let measurable_knormalize (P : probability Y R) U :
  measurable U -> measurable_fun [set: X] (knormalize P ^~ U).
Proof.
move=> mU; rewrite /knormalize/= /mnormalize /=.
rewrite (_ : (fun _ => _) = (fun x =>
     if f x setT == 0 then P U else if f x setT == +oo then P U
     else f x U * (fine (f x setT))^-1%:E)); last first.
  apply/funext => x; case: ifPn => [/orP[->//|->]|]; first by case: ifPn.
  by rewrite negb_or=> /andP[/negbTE -> /negbTE ->].
apply: measurable_fun_if => //; [exact: kernel_measurable_fun_eq_cst|].
apply: measurable_fun_if => //.
- rewrite setTI [X in measurable X](_ : _ = [set t | f t setT != 0]).
    exact: kernel_measurable_neq_cst.
  by apply/seteqP; split => [x /negbT//|x /negbTE].
- apply: (@measurable_funS _ _ _ _ setT) => //.
  exact: kernel_measurable_fun_eq_cst.
- apply: emeasurable_funM.
    exact: measurable_funS (measurable_kernel f U mU).
  apply/measurable_EFinP.
  apply: (@measurable_comp _ _ _ _ _ _ [set r : R | r != 0%R]) => //.
  + exact: open_measurable.
  + move=> /= r [t] [] [_ ft0] ftoo ftr; apply/eqP => r0.
    move: (ftr); rewrite r0 => /eqP; rewrite fine_eq0 ?ft0//.
    by rewrite ge0_fin_numE// lt_neqAle leey ftoo.
  + apply: open_continuous_measurable_fun => //; apply/in_setP => x /= x0.
    exact: inv_continuous.
  + apply: measurableT_comp => //=.
    by have := measurable_kernel f _ measurableT; exact: measurable_funS.
Qed.

HB.instance Definition _ (P : probability Y R) :=
  isKernel.Build _ _ _ _ R (knormalize P) (measurable_knormalize P).

Let knormalize1 (P : probability Y R) x : knormalize P x [set: Y] = 1.
Proof. by rewrite /knormalize/= probability_setT. Qed.

HB.instance Definition _ (P : probability Y R):=
  @Kernel_isProbability.Build _ _ _ _ _ (knormalize P) (knormalize1 P).

End knormalize.

Lemma measurable_fun_mnormalize d d' (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-ker X ~> Y) :
  measurable_fun [set: X] (fun x => mnormalize (k x) point : pprobability Y R).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability Y R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-.
rewrite /mnormalize /mset /preimage/=.
apply: emeasurable_fun_infty_o => //.
rewrite /mnormalize/=.
rewrite (_ : (fun x => _) = (fun x => if (k x setT == 0) || (k x setT == +oo)
    then \d_point Ys else k x Ys * ((fine (k x setT))^-1)%:E)); last first.
  by apply/funext => x/=; case: ifPn.
apply: measurable_fun_if => //.
- apply: (measurable_fun_bool true) => //.
  rewrite (_ : _ @^-1` _ = [set t | k t setT == 0] `|`
                           [set t | k t setT == +oo]); last first.
    by apply/seteqP; split=> x /= /orP.
  by rewrite setTI; apply: measurableU; exact: kernel_measurable_eq_cst.
- apply/emeasurable_funM; first exact/measurable_funTS/measurable_kernel.
  apply/measurable_EFinP; rewrite setTI.
  apply: (@measurable_comp _ _ _ _ _ _ [set r : R | r != 0%R]).
  + exact: open_measurable.
  + by move=> /= _ [x /norP[s0 soo]] <-; rewrite -eqe fineK ?ge0_fin_numE ?ltey.
  + apply: open_continuous_measurable_fun => //; apply/in_setP => x /= x0.
    exact: inv_continuous.
  + by apply: measurableT_comp => //; exact/measurable_funS/measurable_kernel.
Qed.

(* "parameterized composition" of kernels [Lemma 3, Staton ESOP 2017]
   return type: X -> set Z -> \bar R *)
Section kcomp_def.
Context d1 d2 d3 (X : measurableType d1) (Y : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variable l : X -> {measure set Y -> \bar R}.
Variable k : X * Y -> {measure set Z -> \bar R}.

Definition kcomp x (U : set Z) := \int[l x]_y k (x, y) U.

End kcomp_def.

(* [Lemma 3, Staton 2017 ESOP] (1/4) *)
Section kcomp_is_measure.
Context d1 d2 d3 (X : measurableType d1) (Y : measurableType d2)
 (Z : measurableType d3) (R : realType).
Variables (l : R.-ker X ~> Y) (k : R.-ker (X * Y) ~> Z).

Let kcomp0 x : kcomp l k x set0 = 0.
Proof.
by rewrite /kcomp (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let kcomp_ge0 x U : 0 <= kcomp l k x U. Proof. exact: integral_ge0. Qed.

Let kcomp_sigma_additive x : semi_sigma_additive (kcomp l k x).
Proof.
move=> U mU tU mUU; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (U n))); last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _ _; exact: integral_ge0.
rewrite closeE// integral_nneseries// => n.
exact: measurableT_comp (measurable_kernel k _ (mU n)) _.
Qed.

HB.instance Definition _ x := isMeasure.Build _ _ R
  (kcomp l k x) (kcomp0 x) (kcomp_ge0 x) (@kcomp_sigma_additive x).

Definition mkcomp : X -> {measure set Z -> \bar R} := kcomp l k.

End kcomp_is_measure.

Notation "l \; k" := (mkcomp l k) : ereal_scope.

(* [Lemma 3, Staton 2017 ESOP] (2/4) *)
Module KCOMP_FINITE_KERNEL.

Section kcomp_finite_kernel_kernel.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType) (l : R.-fker X ~> Y)
  (k : R.-ker (X * Y) ~> Z).

Lemma measurable_fun_kcomp_finite U :
  measurable U -> measurable_fun [set: X] ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_finite_kernel (k ^~ U)) => //=.
exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) measurable_fun_kcomp_finite.

End kcomp_finite_kernel_kernel.

Section kcomp_finite_kernel_finite.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).
Variables (l : R.-fker X ~> Y) (k : R.-fker (X * Y) ~> Z).

Let mkcomp_finite : measure_fam_uub (kcomp l k).
Proof.
have /measure_fam_uubP[r hr] := measure_uub k.
have /measure_fam_uubP[s hs] := measure_uub l.
apply/measure_fam_uubP; exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x /=.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply: ge0_le_integral => //.
  - exact: measurableT_comp (measurable_kernel k _ measurableT) _.
  - by move=> y _; exact/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ X Z R (l \; k) mkcomp_finite.

End kcomp_finite_kernel_finite.
End KCOMP_FINITE_KERNEL.

(* [Lemma 3, Staton 2017 ESOP] (3/4) *)
Section kcomp_sfinite_kernel.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).
Variable (l : R.-sfker X ~> Y) (k : R.-sfker (X * Y) ~> Z).

Import KCOMP_FINITE_KERNEL.

Lemma mkcomp_sfinite : exists k_ : (R.-fker X ~> Z)^nat,
  forall x U, measurable U -> (l \; k) x U = kseries k_ x U.
Proof.
have [k_ hk_] := sfinite_kernel k; have [l_ hl_] := sfinite_kernel l.
have [kl hkl] : exists kl : (R.-fker X ~> Z) ^nat, forall x U,
    \esum_(i in setT) (l_ i.2 \; k_ i.1) x U = \sum_(i <oo) kl i x U.
  have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
    by rewrite card_eq_sym; exact: card_nat2.
  exists (fun i => l_ (f i).2 \; k_ (f i).1) => x U.
  by rewrite (reindex_esum [set: nat] _ f)// nneseries_esumT.
exists kl => x U mU.
transitivity ((kseries l_ \; kseries k_) x U).
  rewrite /= /kcomp [in RHS](eq_measure_integral (l x)); last first.
    by move=> *; rewrite hl_.
  by apply: eq_integral => y _; rewrite hk_.
rewrite /= /kcomp/= integral_nneseries//=; last first.
  by move=> n; exact: measurableT_comp (measurable_kernel (k_ n) _ mU) _.
transitivity (\sum_(i <oo) \sum_(j <oo) (l_ j \; k_ i) x U).
  apply: eq_eseriesr => i _; rewrite integral_kseries//.
  by exact: measurableT_comp (measurable_kernel (k_ i) _ mU) _.
rewrite /mseries -hkl/=.
rewrite (_ : setT = setT `*`` (fun=> setT)); last by apply/seteqP; split.
rewrite -(@esum_esum _ _ _ _ _ (fun i j => (l_ j \; k_ i) x U))//.
rewrite nneseries_esumT; last by move=> *; exact: nneseries_ge0.
by apply: eq_esum => /= i _; rewrite nneseries_esumT.
Qed.

Lemma measurable_fun_mkcomp_sfinite U : measurable U ->
  measurable_fun [set: X] ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_sfinite_kernel (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

End kcomp_sfinite_kernel.

Module KCOMP_SFINITE_KERNEL.
Section kcomp_sfinite_kernel.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).
Variables (l : R.-sfker X ~> Y) (k : R.-sfker (X * Y) ~> Z).

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) (measurable_fun_mkcomp_sfinite l k).

#[export]
HB.instance Definition _ :=
  Kernel_isSFinite.Build _ _ X Z R (l \; k) (mkcomp_sfinite l k).

End kcomp_sfinite_kernel.
End KCOMP_SFINITE_KERNEL.
HB.export KCOMP_SFINITE_KERNEL.

Section measurable_fun_preimage_integral.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Import HBNNSimple.
Variables (k : Y -> \bar R)
  (k_ : ({nnsfun Y >-> R}) ^nat)
  (ndk_ : nondecreasing_seq (k_ : (Y -> R)^nat))
  (k_k : forall z, [set: Y] z -> (k_ n z)%:E @[n --> \oo] --> k z).

Let k_2 : (X * Y -> R)^nat := fun n => k_ n \o snd.

Let k_2_ge0 n x : (0 <= k_2 n x)%R. Proof. by []. Qed.

HB.instance Definition _ n := @isNonNegFun.Build _ _ _ (k_2_ge0 n).

Let mk_2 n : measurable_fun [set: X * Y] (k_2 n).
Proof. by apply: measurableT_comp => //; exact: measurable_snd. Qed.

HB.instance Definition _ n := @isMeasurableFun.Build _ _ _ _ _ (mk_2 n).

Let fk_2 n : finite_set (range (k_2 n)).
Proof.
have := fimfunP (k_ n).
suff : range (k_ n) = range (k_2 n) by move=> <-.
by apply/seteqP; split => r [y ?] <-; [exists (point, y)|exists y.2].
Qed.

HB.instance Definition _ n := @FiniteImage.Build _ _ _ (fk_2 n).

Lemma measurable_fun_preimage_integral (l : X -> {measure set Y -> \bar R}) :
  (forall n r, measurable_fun [set: X] (l ^~ (k_ n @^-1` [set r]))) ->
  measurable_fun [set: X] (fun x => \int[l x]_z k z).
Proof.
move=> h; apply: (measurable_fun_xsection_integral (k \o snd) l k_2) => /=.
- by rewrite /k_2 => m n mn; apply/lefP => -[x y] /=; exact/lefP/ndk_.
- by move=> [x y]; exact: k_k.
- move=> n r _ /= B mB.
  have := h n r measurableT B mB; rewrite !setTI.
  suff : (l ^~ (k_ n @^-1` [set r])) @^-1` B =
         (fun x => l x (xsection (k_2 n @^-1` [set r]) x)) @^-1` B by move=> ->.
  by apply/seteqP; split => x/=;
    rewrite (comp_preimage _ snd (k_ n)) xsection_preimage_snd.
Qed.

End measurable_fun_preimage_integral.

Section measurable_fun_integral_kernel.

Import HBNNSimple.

Lemma measurable_fun_integral_kernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType)
    (l : X -> {measure set Y -> \bar R})
    (ml : forall U, measurable U -> measurable_fun [set: X] (l ^~ U))
    (* NB: l is really just a kernel *)
    (k : Y -> \bar R) (k0 : forall z, 0 <= k z) (mk : measurable_fun [set: Y] k) :
  measurable_fun [set: X] (fun x => \int[l x]_y k y).
Proof.
pose k_ := nnsfun_approx measurableT mk.
apply: (@measurable_fun_preimage_integral _ _ _ _ _ _ k_) => //.
- by move=> a b ab; exact/nd_nnsfun_approx.
- by move=> z _; exact/cvg_nnsfun_approx.
- by move=> n r; exact/ml.
Qed.

End measurable_fun_integral_kernel.

Section integral_kcomp.
Context d d2 d3 (X : measurableType d) (Y : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variables (l : R.-sfker X ~> Y) (k : R.-sfker (X * Y) ~> Z).

Let integral_kcomp_indic x E (mE : measurable E) :
  \int[kcomp l k x]_z (\1_E z)%:E = \int[l x]_y (\int[k (x, y)]_z (\1_E z)%:E).
Proof.
rewrite integral_indic//= /kcomp.
by apply: eq_integral => y _; rewrite integral_indic.
Qed.

Import HBNNSimple.

Let integral_kcomp_nnsfun x (f : {nnsfun Z >-> R}) :
  \int[kcomp l k x]_z (f z)%:E = \int[l x]_y (\int[k (x, y)]_z (f z)%:E).
Proof.
under [in LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> r z _; rewrite EFinM nnfun_muleindic_ge0.
under [in RHS]eq_integral.
  move=> y _.
  under eq_integral.
    by move=> z _; rewrite fimfunE -fsumEFin//; over.
  rewrite /= ge0_integral_fsum//; last 2 first.
    - by move=> r; exact/measurable_EFinP/measurableT_comp.
    - by move=> r z _; rewrite EFinM nnfun_muleindic_ge0.
  under eq_fsbigr.
    move=> r _.
    rewrite (integralZl_indic _ (fun r => f @^-1` [set r]))//; last first.
      by move=> r0; rewrite preimage_nnfun0.
    rewrite integral_indic// setIT.
    over.
  over.
rewrite /= ge0_integral_fsum//; last 2 first.
  - move=> r; apply: measurable_funeM.
    exact: measurableT_comp (measurable_kernel k (f @^-1` [set r]) _) _.
  - move=> n y _.
    have := mulemu_ge0 (fun n => f @^-1` [set n]).
    by apply; exact: preimage_nnfun0.
apply: eq_fsbigr => r _.
rewrite (integralZl_indic _ (fun r => f @^-1` [set r]))//; last first.
  exact: preimage_nnfun0.
rewrite /= integral_kcomp_indic//.
have [r0|r0] := leP 0%R r.
  rewrite ge0_integralZl//.
    by under eq_integral do rewrite integral_indic// setIT.
  exact: measurableT_comp (measurable_kernel k (f @^-1` [set r]) _) _.
rewrite integral0_eq ?mule0.
  by rewrite integral0_eq// => y _; rewrite preimage_nnfun0// measure0 mule0.
by move=> y _; rewrite integral0_eq// => z _; rewrite preimage_nnfun0// indic0.
Qed.

(* [Lemma 3, Staton 2017 ESOP] (4/4) *)
Lemma integral_kcomp x f : (forall z, 0 <= f z) -> measurable_fun [set: Z] f ->
  \int[kcomp l k x]_z f z = \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
move=> f0 mf.
pose f_ := nnsfun_approx measurableT mf.
transitivity (\int[kcomp l k x]_z (lim ((f_ n z)%:E @[n --> \oo]))).
  by apply/eq_integral => z _; apply/esym/cvg_lim => //=; exact: cvg_nnsfun_approx.
rewrite monotone_convergence//; last 3 first.
  by move=> n; exact/measurable_EFinP.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite (_ : (fun _ => _) =
    (fun n => \int[l x]_y (\int[k (x, y)]_z (f_ n z)%:E)))//; last first.
  by apply/funext => n; rewrite integral_kcomp_nnsfun.
transitivity (\int[l x]_y lim ((\int[k (x, y)]_z (f_ n z)%:E) @[n --> \oo])).
  rewrite -monotone_convergence//; last 3 first.
  - move=> n; apply: measurable_fun_integral_kernel => //.
    + by move=> U mU; exact: measurableT_comp (measurable_kernel k _ mU) _.
    + by move=> z; rewrite lee_fin.
    + exact/measurable_EFinP.
  - by move=> n y _; apply: integral_ge0 => // z _; rewrite lee_fin.
  - move=> y _ a b ab; apply: ge0_le_integral => //.
    + by move=> z _; rewrite lee_fin.
    + exact/measurable_EFinP.
    + exact/measurable_EFinP.
    + by move=> z _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
apply: eq_integral => y _; rewrite -monotone_convergence//; last 3 first.
  - by move=> n; exact/measurable_EFinP.
  - by move=> n z _; rewrite lee_fin.
  - by move=> z _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
by apply: eq_integral => z _; apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.

End integral_kcomp.

Section kfcomp.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

(* [Definition 14.20, Klenke 2014 ]*)
Definition kfcomp (k : T1 -> {measure set T2 -> \bar R})
    (f : T1 * T2 -> \bar R) : T1 -> \bar R :=
  fun x => \int[k x]_y f (x, y).
(* NB: the difference with kcomp is that f is not of type
   T1 * T2 -> {measure set T3 -> \bar R} *)

Lemma kfcompk1 (k : T1 -> {measure set T2 -> \bar R}) :
  kfcomp k (EFin \o cst 1%R) = (k ^~ [set: T2]).
Proof. by apply/funext => x/=; rewrite /kfcomp/= integral_cst// mul1e. Qed.

Lemma kfcompkindic (k : T1 -> {measure set T2 -> \bar R}) A : measurable A ->
  kfcomp k (EFin \o \1_A) = (fun x => k x (xsection A x)).
Proof.
move=> mA; apply/funext=> x; rewrite /kfcomp /= integral_indic// ?setIT//.
- by rewrite -[X in k x X = _]/(_ @^-1` _) -xsectionE.
- rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
  exact: measurable_xsection.
Qed.

End kfcomp.

Section measurable_kfcomp.

Let finite_measure_sigma_finite d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) :
  fin_num_fun mu -> sigma_finite [set: T] mu.
Proof.
by move=> fmu; apply: fin_num_fun_sigma_finite => //; rewrite measure0.
Qed.

Let finite_measure_sfinite d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) :
  fin_num_fun mu -> sfinite_measure mu.
Proof.
move=> fmu.
exists (fun n => if n is O then mu else mzero) => [[]//|U mU].
by rewrite /mseries nneseries_recl// eseries0 ?adde0// => -[|].
Qed.

Let setI_closedX (d1 d2 : measure_display) (T1 : measurableType d1)
    (T2 : measurableType d2) : @setI_closed (T1 * T2)
  [set A `*` B | A in d1.-measurable & B in d2.-measurable].
Proof.
move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
exists (X1 `&` Y1); first exact: measurableI.
by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
Qed.

Variables (d1 d2 : measure_display) (T1 : measurableType d1)
  (T2 : measurableType d2) (R : realType) (k : R.-ftker T1 ~> T2)
  (f : T1 * T2 -> \bar R).

Let g (A1 : set T1) (A2 : set T2) : T1 * T2 -> \bar R := EFin \o \1_(A1 `*` A2).

Let kfcompkg (A1 : set T1) (A2 : set T2) : measurable A1 -> measurable A2 ->
  kfcomp k (g A1 A2) = (fun x => (\1_A1 x)%:E * k x A2).
Proof.
move=> mA1 mA2; apply/funext => x.
rewrite /kfcomp /g/= integral_indic//; last first.
  rewrite [X in measurable X](_ : _ = xsection (A1 `*` A2) x); last first.
    by rewrite xsectionE.
  by apply: measurable_xsection; exact: measurableX.
have [xA1|xA1] := boolP (x \in A1).
  by rewrite indicE xA1 mul1e setIT -[X in _ _ X = _]xsectionE in_xsectionX.
rewrite indicE (negbTE xA1) mul0e setIT.
by rewrite -[X in _ _ X = _]xsectionE notin_xsectionX.
Qed.

Let D := [set A | measurable A /\ measurable_fun setT (kfcomp k (EFin \o \1_A))].

Let setSD_D : setSD_closed D.
Proof.
move=> B A AB; rewrite /D/= => -[mB mIB] [mA mIA].
suff KE : kfcomp k (EFin \o \1_(B `\` A)) =
    kfcomp k (EFin \o \1_B) \- kfcomp k(EFin \o \1_A).
  by split; [exact: measurableD|rewrite KE; exact: emeasurable_funB].
apply/funext => x/=.
pose kx : {measure set T2 -> \bar R} := k x.
pose H1 := isFinite.Build _ _ _ _ (@kernel_finite_transition _ _ _ _ R k x).
pose H2 := isSFinite.Build _ _ _ _ (finite_measure_sfinite
  (@kernel_finite_transition _ _ _ _ R k x)).
pose H3 := isSigmaFinite.Build _ _ _ _ (finite_measure_sigma_finite
  (@kernel_finite_transition _ _ _ _ R k x)).
pose kx' := HB.pack_for (FiniteMeasure.type T2 R) (Measure.sort kx) H1 H2 H3.
have kxE : kx = kx' by exact: eq_measure.
rewrite [in RHS]/kfcomp -integralB_EFin//; last 2 first.
- rewrite -/kx kxE; apply: integrable_indic => //.
  by rewrite -[X in measurable X]xsectionE; exact: measurable_xsection.
- rewrite -/kx kxE; apply: integrable_indic => //.
  by rewrite -[X in measurable X]xsectionE; exact: measurable_xsection.
apply: eq_integral => y _/=; rewrite setDE indicI indicC/=.
rewrite -[in RHS](setCK A) indicC in_setC.
have [xyA|xyA] := boolP (_ \in A); rewrite /= ?mulr1 ?mulr0 ?oppr0 ?adde0//.
by move/set_mem : xyA => /AB Bxy; rewrite indicE mem_set//= EFinN subee.
Qed.

Let lambda_D : lambda_system setT D.
Proof.
split => //.
- by rewrite /D/= indicT kfcompk1; split => //; exact: measurable_kernel.
- suff: D = [set A | (d1, d2).-prod.-measurable A /\
         measurable_fun [set: T1] ((fun C x => k x (xsection C x)) A)].
    by move=> ->; exact: xsection_ndseq_closed.
  apply/seteqP; split=> [/= A [mA /= mIA]|/= A [/= mA mIA]].
  + by split => //; rewrite -kfcompkindic.
  + by split => //; rewrite kfcompkindic.
Qed.

Import HBNNSimple.

(* [Lemma 14.20, Klenke 2014]  *)
Lemma measurable_kfcomp : measurable_fun [set: T1 * T2] f ->
  (forall t, 0 <= f t) -> measurable_fun [set: T1] (kfcomp k f).
Proof.
move=> mf f0.
pose f_ := nnsfun_approx measurableT mf.
pose K := kfcomp k.
have Kf_cvg x : K (EFin \o f_ n) x @[n --> \oo] --> K f x.
  pose g' n y := (EFin \o f_ n) (x, y).
  rewrite [X in _ --> X](_ : _ =
      \int[k x]_y (fun t => limn (g' ^~ t)) y); last first.
    apply: eq_integral => y _.
    by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP; exact: measurableT_comp.
  - by move=> n y _; rewrite /= lee_fin.
  - by move=> y _ a b ab/=; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
apply: (emeasurable_fun_cvg (fun n => K (EFin \o f_ n))); last first.
  by move=> ? _; exact: Kf_cvg.
move=> m.
have DE : D = @measurable _ (T1 * T2)%type.
  apply/seteqP; split => [/= A []//|].
  rewrite measurable_prod_measurableType.
  apply: lambda_system_subset => //= C [A mA [B mB] <-].
  split; [exact: measurableX|rewrite /K kfcompkg//].
  apply: emeasurable_funM; first exact/measurable_EFinP.
  exact: measurable_kernel.
have mK1 (A : set (T1 * T2)) : measurable A ->
    measurable_fun setT (K (EFin \o \1_A)).
  by rewrite -DE => -[].
rewrite [X in measurable_fun _ X](_ : _ = K
    (EFin \o (fun x => \sum_(y \in range (f_ m)) y *
                       \1_(f_ m @^-1` [set y]) x))%R); last first.
  by apply/funext => x/=; apply: eq_integral => y _ /=; rewrite fimfunE.
rewrite /I/= [X in measurable_fun _ X](_ : _ = (fun x =>
   \sum_(y \in range (f_ m))
     (\int[k x]_w2 (y * \1_(f_ m @^-1` [set y]) (x, w2))%:E))); last first.
  apply/funext => x; rewrite /K /kfcomp.
  under eq_integral do rewrite /= -fsumEFin//.
  rewrite /= ge0_integral_fsum//=.
    move=> r.
    under eq_fun do rewrite EFinM.
    apply: emeasurable_funM => //.
    by apply/measurable_EFinP; exact: measurableT_comp.
  by move=> r y _; rewrite EFinM nnfun_muleindic_ge0.
apply: emeasurable_fsum => // r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x =>
    (r%:E * \int[k x]_y (\1_(f_ m @^-1` [set r]) (x, y))%:E))); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite integralZl//.
  pose kx : {measure set T2 -> \bar R} := k x.
  pose H1 := isFinite.Build _ _ _ _ (@kernel_finite_transition _ _ _ _ R k x).
  pose H2 := isSFinite.Build _ _ _ _ (finite_measure_sfinite
    (@kernel_finite_transition _ _ _ _ R k x)).
  pose H3 := isSigmaFinite.Build _ _ _ _ (finite_measure_sigma_finite
    (@kernel_finite_transition _ _ _ _ R k x)).
  pose kx' := HB.pack_for (FiniteMeasure.type T2 R) (Measure.sort kx) H1 H2 H3.
  have kxE : kx = kx' by apply: eq_measure.
  rewrite -/kx kxE; apply: integrable_indic => //.
  by rewrite -[X in measurable X]xsectionE; exact: measurable_xsection.
by apply: emeasurable_funM => //; exact: mK1.
Qed.

End measurable_kfcomp.

(* [Theorem 14.22, Klenke 2014]
   return type : T0 -> set (T1 * T2) -> \bar R *)
Section kproduct_def.
Context d0 d1 d2 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) {R : realType}.
Variable k1 : T0 -> {measure set T1 -> \bar R}.
Variable k2 : T0 * T1 -> {measure set T2 -> \bar R}.

Local Definition intker_indic (k : T0 * T1 -> {measure set T2 -> \bar R}) A :=
  fun xy => \int[k xy]_z (\1_A (xy.2, z))%:E.

Definition kproduct x (A : set (T1 * T2)) :=
  \int[k1 x]_y intker_indic k2 A (x, y).

End kproduct_def.

Section intker_indic_lemmas.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}.
Variable k : R.-ftker T0 * T1 ~> T2.

Local Lemma measurable_intker_indic A : measurable A ->
  measurable_fun [set: T0 * T1] (intker_indic k A).
Proof.
move=> mA; apply: (@measurable_kfcomp _ _ (T0 * T1)%type T2 R k
    (fun abc => (\1_A (abc.1.2, abc.2))%:E)) => //.
apply/measurable_EFinP => //=; apply: measurableT_comp => //=.
apply/measurable_fun_pairP; split => /=.
  rewrite [X in measurable_fun _ X](_ : _ = snd \o fst)//.
  exact: measurableT_comp.
by rewrite [X in measurable_fun _ X](_ : _ = snd).
Qed.

Local Lemma intker_indicE A x y : measurable A ->
  intker_indic k A (x, y) = k (x, y) (xsection A y).
Proof.
move=> mA; rewrite /intker_indic(*NB:lemma?*) integral_indic//; last first.
  by rewrite -[X in measurable X]xsectionE; exact: measurable_xsection.
by rewrite setIT xsectionE.
Qed.

Local Lemma intker_indic_bigcup x y (A : (set (T1 * T2)) ^nat) :
  trivIset [set: nat] A -> (forall n, measurable (A n)) ->
  intker_indic k (\bigcup_n A n) (x, y) =
  \big[+%R/0%R]_(0 <= i <oo) intker_indic k (A i) (x, y).
Proof.
move=> tA mA.
rewrite /intker_indic -(@integral_nneseries _ _ R (k (x, y)) _ measurableT
  (fun i z => (\1_(A i) (y, z))%:E))//.
- by apply: eq_integral => z _ /=; rewrite indic_bigcup.
- move=> n; apply/measurable_EFinP => //; apply: measurable_indic.
  by rewrite -[X in measurable X]xsectionE; exact: measurable_xsection.
Qed.

End intker_indic_lemmas.

Section kproduct_snd_def.
Context d0 d1 d2 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) {R : realType}.
Variable k1 : T0 -> {measure set T1 -> \bar R}.
Variable k2 : T1 -> {measure set T2 -> \bar R}.

Definition kproduct_snd  : T0 -> set (T1 * T2) -> \bar R :=
  kproduct k1 (k2 \o snd).

End kproduct_snd_def.

(* [Theorem 14.22, Klenke 2014] (1/3) *)
Theorem measurable_kproduct d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) A :
  measurable A -> measurable_fun [set: T0] (kproduct k1 k2 ^~ A).
Proof.
move=> mA; apply: measurable_kfcomp => // t.
  exact: measurable_intker_indic.
by apply: integral_ge0 => y _; rewrite lee_fin.
Qed.

(* [Theorem 14.22, Klenke 2014] (2/3) *)
Theorem semi_sigma_additive_kproduct d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) x :
  semi_sigma_additive (kproduct k1 k2 x).
Proof.
move=> /= A mA tA mbigcup.
rewrite (_ : (fun n => _) = (fun n =>
    \int[k1 x]_y (\sum_(0 <= i < n) intker_indic k2 (A i) (x, y)))); last first.
  apply/funext => n; rewrite ge0_integral_sum//.
    by move=> m; exact: measurable_fun_pair2 (measurable_intker_indic k2 _).
  by move=> m y _; rewrite intker_indicE.
pose g n y := \sum_(0 <= i < n) intker_indic k2 (A i) (x, y).
rewrite [X in _ --> X](_ : _ = \int[k1 x]_y limn (g ^~ y)); last first.
  by apply: eq_integral => y _; rewrite /g intker_indic_bigcup.
apply: (@cvg_monotone_convergence _ _ _ (k1 x) _ measurableT g) => //.
- move=> n; apply: (@emeasurable_sum _ _ R setT _ _
    (fun i t => intker_indic k2 (A i) (x, t))) => m.
  exact: measurable_fun_pair2 (measurable_intker_indic k2 (mA m)).
- by move=> n y _; apply: sume_ge0 => m _; rewrite intker_indicE.
- move=> y _ a b ab; apply: lee_sum_nneg_natr => // m _ _.
  by rewrite intker_indicE.
Qed.

Section kproduct_measure.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
  (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2).

Let kproduct0 x : kproduct k1 k2 x set0 = 0.
Proof.
by apply: integral0_eq => y _; apply: integral0_eq => z _; rewrite indic0.
Qed.

Let kproduct_ge0 x A : 0 <= kproduct k1 k2 x A.
Proof.
by apply: integral_ge0 => y _; apply: integral_ge0 => z _; rewrite lee_fin.
Qed.

Let kproduct_additive x : semi_sigma_additive (kproduct k1 k2 x).
Proof. exact: semi_sigma_additive_kproduct. Qed.

HB.instance Definition _ x := isMeasure.Build
  (measure_prod_display (d1, d2)) (T1 * T2)%type R (kproduct k1 k2 x)
  (kproduct0 x) (kproduct_ge0 x) (@kproduct_additive x).

Definition mkproduct :=
  (kproduct k1 k2 : T0 -> {measure set (T1 * T2) -> \bar R}).

End kproduct_measure.

HB.instance Definition _ d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) :=
  @isKernel.Build _ _ T0 (T1 * T2)%type R
    (mkproduct k1 k2) (measurable_kproduct k1 k2).

(* [Theorem 14.22, Klenke 2014] (3/3): the composition of finite transition
  kernels is sigma-finite *)
Section sigma_finite_kproduct.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
  (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2).

Theorem sigma_finite_mkproduct x :
  sigma_finite [set: T1 * T2] (mkproduct k1 k2 x).
Proof.
pose A n := [set w1 | k2 (x, w1) setT < n%:R%:E].
have mA n : measurable (A n).
  rewrite /A -[X in measurable X]setTI.
  apply: emeasurable_fun_infty_o => //.
  have := @measurable_kernel _ _ _ _ R k2 _ measurableT.
  exact: measurable_fun_pair2.
have bigcupA : \bigcup_n A n = setT.
  have fink2 xy : fin_num_fun (k2 xy) by exact: kernel_finite_transition.
  apply/seteqP; split => // y _.
  have {}fink2 := fink2 (x, y) _ measurableT.
  exists (Num.truncn (fine (k2 (x, y) setT))).+1 => //=.
  have : (0 <= fine (k2 (x, y) [set: T2]))%R by rewrite fine_ge0.
  by move=> /truncn_itv/andP[_]; rewrite -lte_fin fineK.
have lty n : kproduct k1 k2 x (A n `*` setT) < +oo.
  have fink1 : fin_num_fun (k1 x) by exact: kernel_finite_transition.
  apply: (@le_lt_trans _ _ (n%:R%:E * k1 x (A n))) => /=.
    rewrite [leLHS](_ : _ = \int[k1 x]_(y in A n) k2 (x, y) setT); last first.
      rewrite /kproduct [RHS]integral_mkcond; apply: eq_integral => y _.
      rewrite intker_indicE//; last exact: measurableX.
      rewrite patchE; case: ifPn => [Anx|Anx].
        by rewrite in_xsectionX.
      by rewrite notin_xsectionX// measure0.
    apply: (@le_trans _ _ (\int[k1 x]_(x in A n) n%:R%:E)).
      apply: ge0_le_integral => //.
      - apply: measurable_funTS.
        have := @measurable_kernel _ _ _ _ _ k2 _ measurableT.
        exact: measurable_fun_pair2.
      - by move=> y; rewrite /A/= => /ltW.
      - by rewrite integral_cst.
    by rewrite lte_mul_pinfty// ltey_eq fink1.
exists (fun n => A n `*` setT) => /=.
  by rewrite -setX_bigcupl bigcupA setXTT.
by move=> n; split => //; exact: measurableX.
Qed.

HB.instance Definition _ x := @isSigmaFiniteTransitionKernel.Build d0
  (measure_prod_display (d1, d2)) T0 (T1 * T2)%type R
    (mkproduct k1 k2) sigma_finite_mkproduct.

End sigma_finite_kproduct.

(* [Definition 14.25, Klenke 2014]
   return type: T0 -> set T2 -> \bar R *)
Section kcomp_noparam_def.
Context d0 d1 d2 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) {R : realType}.
Variable k1 : T0 -> {measure set T1 -> \bar R}.
Variable k2 : T1 -> {measure set T2 -> \bar R}.

Definition kcomp_noparam (x : T0) (A : set T2) : \bar R :=
  \int[k1 x]_y (k2 y A).

End kcomp_noparam_def.

(* a parameterized subprobability kernel that ignores its first argument *)
Section spker_snd.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
  (k : R.-spker T1 ~> T2).

Local Definition kernel_snd : (T0 * T1)%type -> {measure set T2 -> \bar R} :=
  k \o snd.

Let measurable_kernel U : measurable U ->
  measurable_fun [set: _] (kernel_snd ^~ U).
Proof.
move=> mU; have /= mk1 := measurable_kernel k _ mU.
move=> _ /= Y mY; have {}mk1 := mk1 measurableT _ mY.
have -> : [set: T0 * T1] `&` (kernel_snd ^~ U) @^-1` Y =
    setT `*` ([set: T1] `&` (k ^~ U) @^-1` Y).
  by rewrite !setTI setTX.
exact: measurableX.
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ _ _ _ kernel_snd measurable_kernel.

Let measure_uub : measure_fam_uub kernel_snd.
Proof.
exists 2%R => /= -[x y].
rewrite /kernel_snd/= (@le_lt_trans _ _ 1%:E) ?lte1n//.
exact: sprob_kernel_le1.
Qed.

HB.instance Definition _ :=
  @Kernel_isFinite.Build _ _ _ _ _ kernel_snd measure_uub.

Let sprob_kernel :
  ereal_sup [set kernel_snd z [set: _] | z in [set: _]] <= 1.
Proof.
by apply: (sprob_kernelP kernel_snd).2 => -[x y]; exact: sprob_kernel_le1.
Qed.

HB.instance Definition _ := isSubProbabilityKernel.Build _ _ _ _ _
  kernel_snd sprob_kernel.

Local Lemma intker_indic_snd (A : set T2) x y : measurable A ->
  intker_indic kernel_snd ([set: _] `*` A) (x, y) = k y A.
Proof.
move=> mA; rewrite intker_indicE//=; last exact: measurableX.
by congr (k y _); rewrite xsectionE//= setTX.
Qed.

End spker_snd.

(* [Theorem 14.26, Klenke 2014] (1/2) *)
Lemma kcomp_noparamE d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : T0 -> {measure set T1 -> \bar R})
    (k2 : T1 -> {measure set T2 -> \bar R}) x A :
  measurable A ->
  kcomp_noparam k1 k2 x A = kproduct_snd k1 k2 x (snd @^-1` A).
Proof.
move=> mA; rewrite /kcomp_noparam /kproduct_snd /kproduct.
apply: eq_integral => y _ /=.
by rewrite /intker_indic/= integral_indic// setIT.
Qed.

Section kcomp_noparam_measure.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
  (k1 : R.-spker T0 ~> T1) (k2 : R.-spker T1 ~> T2).

Let kcomp_noparam0 x : kcomp_noparam k1 k2 x set0 = 0.
Proof. by apply: integral0_eq => y _; rewrite measure0. Qed.

Let kcomp_noparam_ge0 x A : 0 <= kcomp_noparam k1 k2 x A.
Proof. by apply: integral_ge0 => y _; exact: measure_ge0. Qed.

Let kcomp_noparam_additive x : semi_sigma_additive (kcomp_noparam k1 k2 x).
Proof.
move=> F mF tF mUF.
rewrite kcomp_noparamE// (_ : (fun _ => _) = (fun n =>
    \sum_(0 <= i < n) kproduct_snd k1 k2 x (snd @^-1` F i))); last first.
  by apply/funext => n; apply: eq_bigr => k _; rewrite kcomp_noparamE.
pose F' n := [set: T1] `*` F n.
have kcomp_noparam_bigcup : kcomp_noparam k1 k2 x (\bigcup_n F n) =
    kproduct k1 (kernel_snd k2) x (\bigcup_n F' n).
  by apply: eq_integral => y _; rewrite -setX_bigcupr intker_indic_snd.
rewrite -kcomp_noparamE// kcomp_noparam_bigcup.
rewrite (_ : (fun n => _) = (fun n =>
    \sum_(0 <= i < n) kproduct k1 (kernel_snd k2) x (F' i))); last first.
  apply/funext => n; apply: eq_bigr => i _.
  apply: eq_integral => y _; apply: eq_integral => z _.
  by rewrite /F' setTX.
apply: semi_sigma_additive_kproduct => //.
- by move=> i; exact: measurableX.
- apply/trivIsetP => i j _ _ ij.
  rewrite /F' -setXI setTI.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij) ->.
  by rewrite setX0.
- by apply: bigcup_measurable => k _; exact: measurableX.
Qed.

HB.instance Definition _ x := isMeasure.Build d2 T2 R (kcomp_noparam k1 k2 x)
  (kcomp_noparam0 x) (kcomp_noparam_ge0 x) (@kcomp_noparam_additive x).

Definition mkcomp_noparam :=
  (kcomp_noparam k1 k2 : T0 -> {measure set T2 -> \bar R}).

Let measurable_kernel U :
  measurable U -> measurable_fun [set: _] (mkcomp_noparam ^~ U).
Proof.
move=> mU.
rewrite [X in measurable_fun _ X](_ : _ =
    (kproduct k1 (kernel_snd k2))^~ ([set: T1] `*` U)); last first.
  apply/funext => x.
  by apply: eq_integral => y _; rewrite intker_indic_snd.
by apply: measurable_kproduct; exact: measurableX.
Qed.

HB.instance Definition _ := @isKernel.Build _ _ _ _ R
  mkcomp_noparam measurable_kernel.

End kcomp_noparam_measure.

(* the composition of subprobability kernels is a subprobability kernel *)
Section subprobability_kcomp_noparam.
Context d0 d1 d2 (T0 : measurableType d0)
  (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
  (k1 : R.-spker T0 ~> T1) (k2 : R.-spker T1 ~> T2).

(* [Theorem 14.26, Klenke 2014] (2/2) *)
Lemma sprob_mkcomp_noparam x : mkcomp_noparam k1 k2 x setT <= 1.
Proof.
rewrite /mkcomp_noparam [leLHS]kcomp_noparamE// preimage_setT.
rewrite /kproduct_snd /kproduct.
rewrite [leLHS](_ : _ = \int[k1 x]_y k2 y setT); last first.
  apply: eq_integral => y _.
  rewrite /intker_indic integral_indic//; last first.
    rewrite [X in measurable X](_ : _ = ysection setT y).
      exact: measurable_ysection.
    by rewrite ysectionE.
  by rewrite setIT.
apply: (@le_trans _ _ (\int[k1 x]__ 1)); last first.
  by rewrite integral_cst// mul1e; exact: sprob_kernel_le1.
apply: ge0_le_integral => //; first exact: measurable_kernel.
by move=> y _; exact: sprob_kernel_le1.
Qed.

Let sprob_kernel :
  ereal_sup [set (kcomp_noparam k1 k2) x setT | x in [set: T0]] <= 1.
Proof. by apply/sprob_kernelP => x; exact: sprob_mkcomp_noparam. Qed.

HB.instance Definition _ := Kernel_isSubProbability.Build
  _ _ _ _ R (mkcomp_noparam k1 k2) sprob_kernel.

End subprobability_kcomp_noparam.
