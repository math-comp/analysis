From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure  numfun lebesgue_integral exp kernel trigo.
Require Import prob_lang.

(******************************************************************************)
(*  Semantics of a probabilistic programming language using s-finite kernels  *)
(*       (wip about definition of Lebesgue and counting measures)             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section gauss.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for gauss *)
Definition gauss_density m s x : R :=
  (s * sqrtr (pi *+ 2))^-1 * expR (- ((x - m) / s) ^+ 2 / 2%:R).

Lemma gauss_density_ge0 m s x : 0 <= s -> 0 <= gauss_density m s x.
Proof. by move=> s0; rewrite mulr_ge0 ?expR_ge0// invr_ge0 mulr_ge0. Qed.

Lemma gauss_density_gt0 m s x : 0 < s -> 0 < gauss_density m s x.
Proof.
move=> s0; rewrite mulr_gt0 ?expR_gt0// invr_gt0 mulr_gt0//.
by rewrite sqrtr_gt0 pmulrn_rgt0// pi_gt0.
Qed.

Definition gauss01_density : R -> R := gauss_density 0 1.

Hypothesis integral_gauss01_density :
  (\int[lebesgue_measure]_x (gauss01_density x)%:E = 1%E)%E.

Lemma gauss01_densityE x :
  gauss01_density x = (sqrtr (pi *+ 2))^-1 * expR (- (x ^+ 2) / 2%:R).
Proof. by rewrite /gauss01_density /gauss_density mul1r subr0 divr1. Qed.

Definition mgauss01 (V : set R) :=
  (\int[lebesgue_measure]_(x in V) (gauss01_density x)%:E)%E.

Lemma measurable_fun_gauss_density m s :
  measurable_fun setT (gauss_density m s).
Proof.
apply: measurable_funM => //=.
apply: measurableT_comp => //=.
apply: measurable_funM => //=.
apply: measurableT_comp => //=.
apply: measurableT_comp (measurable_exprn _) _ => /=.
apply: measurable_funM => //=.
exact: measurable_funD.
Qed.

Let mgauss010 : mgauss01 set0 = 0%E.
Proof. by rewrite /mgauss01 integral_set0. Qed.

Let mgauss01_ge0 A : (0 <= mgauss01 A)%E.
Proof.
by rewrite /mgauss01 integral_ge0//= => x _; rewrite lee_fin gauss_density_ge0.
Qed.

Let mgauss01_sigma_additive : semi_sigma_additive mgauss01.
Proof.
move=> /= F mF tF mUF.
rewrite /mgauss01/= integral_bigcup//=; last first.
  apply/integrableP; split.
    apply/EFin_measurable_fun.
    exact: measurable_funS (measurable_fun_gauss_density 0 1).
  rewrite (_ : (fun x => _) = (EFin \o gauss01_density)); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin gauss_density_ge0.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      apply/EFin_measurable_fun.
      exact: measurable_fun_gauss_density.
    by move=> ? _; rewrite lee_fin gauss_density_ge0.
  by rewrite integral_gauss01_density// ltey.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin gauss_density_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  mgauss01 mgauss010 mgauss01_ge0 mgauss01_sigma_additive.

Let mgauss01_setT : mgauss01 [set: _] = 1%E.
Proof. by rewrite /mgauss01 integral_gauss01_density. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R mgauss01 mgauss01_setT.

Definition gauss01 := [the probability _ _ of mgauss01].

End gauss.

Section gauss_lebesgue.
Import Notations.
Context d (T : measurableType d) (R : realType).
Hypothesis integral_gauss01_density :
  (\int[@lebesgue_measure R]_x (gauss01_density x)%:E = 1%E)%E.

Let f1 (x : R) := (gauss01_density x) ^-1.

Hypothesis integral_mgauss01 : forall U, measurable U ->
  \int[mgauss01 (R:=R)]_(y in U) (f1 y)%:E =
  \int[lebesgue_measure]_(x0 in U) (gauss01_density x0 * f1 x0)%:E.

Let mf1 : measurable_fun setT f1.
Proof.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- by move=> /= r [t _ <-]; rewrite gt_eqF// gauss_density_gt0.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_fun_gauss_density.
Qed.

Variable mu : {measure set mR R -> \bar R}.

Definition staton_lebesgue : R.-sfker T ~> _ :=
  letin (sample_cst (gauss01 integral_gauss01_density : pprobability _ _))
  (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

Lemma staton_lebesgueE x U : measurable U ->
  staton_lebesgue x U = lebesgue_measure U.
Proof.
move=> mU; rewrite [in LHS]/staton_lebesgue/=.
rewrite [in LHS]letinE /=.
transitivity (\int[@mgauss01 R]_(y in U) (f1 y)%:E).
  rewrite -[in RHS](setTI U) integral_setI_indic//=.
  apply: eq_integral => //= r.
  rewrite letinE/= ge0_integral_mscale//= ger0_norm//; last first.
    by rewrite invr_ge0// gauss_density_ge0.
  by rewrite integral_dirac// diracT mul1e diracE indicE.
rewrite integral_mgauss01//.
transitivity (\int[lebesgue_measure]_(x in U) (\1_U x)%:E).
  apply: eq_integral => /= y yU.
  by rewrite /f1 divrr ?indicE ?yU// unitfE gt_eqF// gauss_density_gt0.
by rewrite integral_indic//= setIid.
Qed.

End gauss_lebesgue.

(* TODO: move this elsewhere *)
(* assuming x > 0 *)
Definition Gamma {R : realType} (x : R) : \bar R :=
  \int[lebesgue_measure]_(t in `[0%R, +oo[%classic) (expR (- t) * powR t (x - 1))%:E.

Definition Rfact {R : realType} (x : R) := Gamma (x + 1)%R.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.
Hypothesis integral_poisson_density : forall k,
  (\int[lebesgue_measure]_x (@poisson R k x)%:E = 1%E)%E.

(* density function for poisson *)
Definition poisson1 := @poisson R 1%N.

Lemma poisson1_ge0 (x : R) : 0 <= poisson1 x.
Proof. exact: poisson_ge0. Qed.

Definition mpoisson1 (V : set R) : \bar R :=
  (\int[lebesgue_measure]_(x in V) (poisson1 x)%:E)%E.

Lemma measurable_fun_poisson1 : measurable_fun setT poisson1.
Proof. exact: measurable_poisson. Qed.

Let mpoisson10 : mpoisson1 set0 = 0%E.
Proof. by rewrite /mpoisson1 integral_set0. Qed.

Lemma mpoisson1_ge0 A : (0 <= mpoisson1 A)%E.
Proof.
apply: integral_ge0 => x Ax.
by rewrite lee_fin poisson1_ge0.
Qed.

Let mpoisson1_sigma_additive : semi_sigma_additive mpoisson1.
Proof.
move=> /= F mF tF mUF.
rewrite /mpoisson1/= integral_bigcup//=; last first.
  apply/integrableP; split.
    apply/EFin_measurable_fun.
    exact: measurable_funS (measurable_poisson _).
  rewrite (_ : (fun x => _) = (EFin \o poisson1)); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin poisson1_ge0//.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/EFin_measurable_fun; exact: measurable_poisson.
    by move=> ? _; rewrite lee_fin poisson1_ge0//.
  by rewrite /= integral_poisson_density// ltry.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin poisson1_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  mpoisson1 mpoisson10 mpoisson1_ge0 mpoisson1_sigma_additive.

Let mpoisson1_setT : mpoisson1 [set: _] = 1%E.
Proof.
rewrite /mpoisson1.
rewrite /poisson1.
by rewrite integral_poisson_density.
Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R mpoisson1 mpoisson1_setT.

Definition poisson' := [the probability _ _ of mpoisson1].

End poisson.

(* Staton's definition of the counting measure
   Staton ESOP 2017, Sect. 4.2, equation (13)  *)
Section staton_counting.
Context d (X : measurableType d).
Variable R : realType.
Import Notations.
Hypothesis integral_poisson_density : forall k,
  (\int[lebesgue_measure]_x (@poisson R k x)%:E = 1%E)%E.

Let f1 x := (poisson1 (x : R)) ^-1.

Let mf1 : measurable_fun setT f1.
rewrite /f1 /poisson1 /poisson.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- move=> /= r [t ? <-].
  by case: ifPn => // t0; rewrite gt_eqF ?mulr_gt0 ?expR_gt0//= invrK ltr0n.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_poisson.
Qed.

Definition staton_counting : R.-sfker X ~> _ :=
  letin (sample_cst (@poisson' R integral_poisson_density : pprobability _ _))
    (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

End staton_counting.
