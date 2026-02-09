(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
From mathcomp Require Import boolp classical_sets reals ereal topology.
From mathcomp Require Import normedtype sequences exp esum measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

(**md**************************************************************************)
(* # Poisson distribution                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      poisson_pmf r k == pmf of the Poisson distribution with parameter r   *)
(*       poisson_prob r == Poisson probability measure                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section poisson_pmf.
Local Open Scope ring_scope.
Context {R : realType}.
Implicit Types (rate : R) (k : nat).

Definition poisson_pmf rate k : R :=
  if rate > 0 then (rate ^+ k) * k`!%:R^-1 * expR (- rate) else 1.

Lemma poisson_pmf_ge0 rate k : 0 <= poisson_pmf rate k.
Proof.
rewrite /poisson_pmf; case: ifPn => // rate0.
by rewrite 2?mulr_ge0// exprn_ge0// ltW.
Qed.

End poisson_pmf.

Lemma measurable_poisson_pmf {R : realType} D k : measurable D ->
  measurable_fun D (@poisson_pmf R ^~ k).
Proof.
move=> mD; rewrite /poisson_pmf; apply: measurable_fun_if => //.
  exact: measurable_fun_ltr.
apply: measurable_funM; first exact: measurable_funM.
by apply: measurable_funTS; exact: measurableT_comp.
Qed.

Definition poisson_prob {R : realType} (rate : R) (k : nat)
   : set nat -> \bar R :=
  fun U => if 0 < rate then
    \esum_(k in U) (poisson_pmf rate k)%:E else \d_0%N U.

Section poisson.
Context {R : realType} (rate : R) (k : nat).
Local Open Scope ereal_scope.

Local Notation poisson := (poisson_prob rate k).

Let poisson0 : poisson set0 = 0.
Proof. by rewrite /poisson measure0; case: ifPn => //; rewrite esum_set0. Qed.

Let poisson_ge0 U : 0 <= poisson U.
Proof.
rewrite /poisson; case: ifPn => // rate0; apply: esum_ge0 => /= n Un.
by rewrite lee_fin poisson_pmf_ge0.
Qed.

Let poisson_sigma_additive : semi_sigma_additive poisson.
Proof.
move=> F mF tF mUF; rewrite /poisson; case: ifPn => rate0; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: lee_sum_nneg_natr => // n _ _.
  by apply: esum_ge0 => /= ? _; exact: poisson_pmf_ge0.
by rewrite nneseries_sum_bigcup// => i; rewrite lee_fin poisson_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ poisson
  poisson0 poisson_ge0 poisson_sigma_additive.

Let poisson_setT : poisson [set: nat] = 1.
Proof.
rewrite /poisson; case: ifPn => [rate0|_]; last by rewrite probability_setT.
rewrite [RHS](_ : _ = (expR (- rate))%:E * (expR rate)%:E); last first.
  by rewrite -EFinM expRN mulVf ?gt_eqF ?expR_gt0.
rewrite -nneseries_esumT; last by move=> *; rewrite lee_fin poisson_pmf_ge0.
under eq_eseriesr.
  move=> n _; rewrite /poisson_pmf rate0 EFinM muleC; over.
rewrite /= nneseriesZl/=; last first.
  by move=> n _; rewrite lee_fin divr_ge0// exprn_ge0// ltW.
congr *%E; rewrite expRE -EFin_lim; last first.
  rewrite /pseries/=; under eq_fun do rewrite mulrC.
  exact: is_cvg_series_exp_coeff.
apply/congr_lim/funext => n/=; rewrite /pseries/= /series/= -sumEFin//.
by under eq_bigr do rewrite mulrC.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R poisson poisson_setT.

End poisson.

Lemma measurable_poisson_prob {R : realType} n :
  measurable_fun setT (poisson_prob ^~ n : R -> pprobability _ _).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_if => //=; first exact: measurable_fun_ltr.
apply: (eq_measurable_fun (fun t =>
    \sum_(k <oo | k \in Ys) (poisson_pmf t k)%:E))%E.
  move=> x /set_mem[_/= x01].
  by rewrite nneseries_esum ?set_mem_set// =>*; rewrite lee_fin poisson_pmf_ge0.
apply: ge0_emeasurable_sum.
  by move=> k x/= [_ x01] _; rewrite lee_fin poisson_pmf_ge0.
move=> k Ysk; apply/measurableT_comp => //.
apply: measurable_poisson_pmf => //.
rewrite setTI (_ : _ @^-1` _ = `]0, +oo[%classic)//.
by apply/seteqP; split => /= x /=; rewrite in_itv/= andbT.
Qed.
