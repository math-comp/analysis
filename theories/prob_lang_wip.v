From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences esum measure lebesgue_measure numfun.
From mathcomp Require Import lebesgue_integral exp kernel trigo prob_lang.
From mathcomp Require Import realfun charge probability derive ftc.
From mathcomp Require Import gauss_integral.

(**md**************************************************************************)
(* wip waiting for the Poisson distribution                                   *)
(*                                                                            *)
(* Another example from Section 4.2 in [Equation (13), Staton, ESOP 2017].    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.
Notation mu := (@lebesgue_measure R).
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pdf R k x)%:E = 1%E)%E.

(* density function for poisson *)
Definition poisson1 := @poisson_pdf R 1%N.

Lemma poisson1_ge0 (x : R) : 0 <= poisson1 x.
Proof. exact: poisson_pdf_ge0. Qed.

Definition mpoisson1 (V : set R) : \bar R :=
  (\int[lebesgue_measure]_(x in V) (poisson1 x)%:E)%E.

Lemma measurable_fun_poisson1 : measurable_fun setT poisson1.
Proof. exact: measurable_poisson_pdf. Qed.

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
    apply/measurable_EFinP.
    exact: measurable_funS (measurable_poisson_pdf _).
  rewrite (_ : (fun x => _) = (EFin \o poisson1)); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin poisson1_ge0//.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/measurable_EFinP; exact: measurable_poisson_pdf.
    by move=> ? _; rewrite lee_fin poisson1_ge0//.
  by rewrite /= integral_poisson_density// ltry.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin poisson1_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  mpoisson1 mpoisson10 mpoisson1_ge0 mpoisson1_sigma_additive.

Let mpoisson1_setT : mpoisson1 [set: _] = 1%E.
Proof. exact: integral_poisson_density. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R
  mpoisson1 mpoisson1_setT.

Definition poisson' := [the probability _ _ of mpoisson1].

End poisson.

(* Staton's definition of the counting measure
   [equation (13), Sect. 4.2, Staton ESOP 2017] *)
Section staton_counting.
Context d (X : measurableType d).
Variable R : realType.
Notation mu := (@lebesgue_measure R).
Import Notations.
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pdf R k x)%:E = 1%E)%E.

Let f1 x := ((poisson1 (x : R))^-1)%R.

Let mf1 : measurable_fun setT f1.
rewrite /f1 /poisson1 /poisson_pdf.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- move=> /= r [t ? <-].
  by case: ifPn => // t0; rewrite gt_eqF ?mulr_gt0 ?expR_gt0//= invrK ltr0n.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_poisson_pdf.
Qed.

Definition staton_counting : R.-sfker X ~> _ :=
  letin (sample_cst (@poisson' R integral_poisson_density : pprobability _ _))
    (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

End staton_counting.
