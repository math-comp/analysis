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

(******************************************************************************)
(*  Semantics of a probabilistic programming language using s-finite kernels  *)
(*            (wip about the definition of Lebesgue measure)                  *)
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

Definition gauss_pdf := @normal_pdf R 0 1.

(* TODO: move to probability.v *)
Lemma normal_pdf_gt0 m s x : 0 < s -> 0 < normal_pdf m s x :> R.
Proof.
move=> s0; rewrite /normal_pdf gt_eqF// mulr_gt0 ?expR_gt0// invr_gt0.
by rewrite sqrtr_gt0 pmulrn_rgt0// mulr_gt0 ?pi_gt0// exprn_gt0.
Qed.

Lemma gauss_pdf_gt0 x : 0 < gauss_pdf x.
Proof. exact: normal_pdf_gt0. Qed.

Definition gauss_prob := @normal_prob R 0 1.

HB.instance Definition _ := Probability.on gauss_prob.

Lemma gauss_prob_dominates : gauss_prob `<< lebesgue_measure.
Proof. exact: normal_prob_dominates. Qed.

Lemma continuous_gauss_pdf x : {for x, continuous gauss_pdf}.
Proof. exact: continuous_normal_pdf. Qed.

End gauss.

Section gauss_lebesgue.
Context d (T : measurableType d) (R : realType).
Notation mu := (@lebesgue_measure R).

Let f1 (x : g_sigma_algebraType (R.-ocitv.-measurable)) := (gauss_pdf x)^-1.

Let f1E (x : R) : f1 x = (Num.sqrt (pi *+ 2) * expR (- (- x ^+ 2 / 2)))%R.
Proof.
rewrite /f1 /gauss_pdf /normal_pdf oner_eq0 subr0 expr1n mul1r.
by rewrite invfM invrK -expRN.
Qed.

Let f1_gt0 (x : R) : (0 < f1 x)%R.
Proof. by rewrite f1E mulr_gt0 ?expR_gt0// sqrtr_gt0 mulrn_wgt0// pi_gt0. Qed.

Lemma measurable_fun_f1 : measurable_fun setT f1.
Proof.
apply: continuous_measurable_fun => x.
apply: (@continuousV _ _ (@gauss_pdf R)).
  by rewrite gt_eqF// gauss_pdf_gt0.
exact: continuous_gauss_pdf.
Qed.

Lemma integral_mgauss01 : forall U, measurable U ->
  \int[(@gauss_prob R)]_(y in U) (f1 y)%:E =
  \int[mu]_(x0 in U) (gauss_pdf x0 * f1 x0)%:E.
Proof.
move=> U mU.
under [in RHS]eq_integral do rewrite EFinM/= muleC.
rewrite /=.
rewrite -(@Radon_Nikodym_SigmaFinite.change_of_variables
    _ _ _ _ (@lebesgue_measure R))//=; last 3 first.
  exact: gauss_prob_dominates.
  by move=> /= x; rewrite lee_fin ltW.
  apply/measurable_EFinP.
  apply: measurable_funTS.
  exact: measurable_fun_f1.
apply: ae_eq_integral => //=.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply: (measurable_int mu).
  apply: (integrableS _ _ (@subsetT _ _)) => //=.
  apply: Radon_Nikodym_SigmaFinite.f_integrable => /=.
  exact: gauss_prob_dominates.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_normal_pdf.
- apply: ae_eq_mul2l => /=.
  rewrite /Radon_Nikodym_SigmaFinite.f/=.
  case: pselect => [gauss_prob_dom|]; last first.
    by move=> /(_ (@gauss_prob_dominates R)).
  case: cid => //= h [h1 h2 h3] gauss_probE.
  apply: integral_ae_eq => //=.
  + exact: integrableS h3.
  + apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_normal_pdf.
  + move=> E EU mE.
    by rewrite -gauss_probE.
Qed.

Let mf1 : measurable_fun setT f1.
Proof.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- by move=> /= r [t _ <-]; rewrite gt_eqF// gauss_pdf_gt0.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_normal_pdf.
Qed.

Definition staton_lebesgue : R.-sfker T ~> _ :=
  letin (sample_cst (@gauss_prob R : pprobability _ _))
  (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

Lemma staton_lebesgueE x U : measurable U ->
  staton_lebesgue x U = lebesgue_measure U.
Proof.
move=> mU; rewrite [in LHS]/staton_lebesgue/=.
rewrite [in LHS]letinE /=.
transitivity (\int[(@gauss_prob R)]_(y in U) (f1 y)%:E).
  rewrite -[in RHS](setTI U) integral_mkcondr/=.
  apply: eq_integral => //= r _.
  rewrite letinE/= ge0_integral_mscale//= ger0_norm//; last first.
    by rewrite invr_ge0// normal_pdf_ge0.
  rewrite integral_dirac// diracT mul1e/= diracE epatch_indic/=.
  by rewrite indicE.
rewrite integral_mgauss01//.
transitivity (\int[lebesgue_measure]_(x in U) (\1_U x)%:E).
  apply: eq_integral => /= y yU.
  by rewrite /f1 divrr ?indicE ?yU// unitfE gt_eqF// gauss_pdf_gt0.
by rewrite integral_indic//= setIid.
Qed.

End gauss_lebesgue.

Notation left_continuous f :=
  (forall x, f%function @ at_left x --> f%function x).

Lemma left_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> left_continuous f.
Proof. by move=> cf x; exact/cvg_at_left_filter/cf. Qed.

Section Gamma.
Context {R : realType}.

Let mu := @lebesgue_measure R.

Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (powR x (a - 1) * expR (- x))%:E)%E.

Let I n := \int[mu]_(x in `[0%R, +oo[) (x ^+ n * expR (- x))%:E.

End Gamma.

Definition Rfact {R : realType} (x : R) := Gamma (x + 1)%R.

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
   Staton ESOP 2017, Sect. 4.2, equation (13)  *)
Section staton_counting.
Context d (X : measurableType d).
Variable R : realType.
Notation mu := (@lebesgue_measure R).
Import Notations.
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pdf R k x)%:E = 1%E)%E.

Let f1 x := (poisson1 (x : R)) ^-1.

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
