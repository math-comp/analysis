From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import signed reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure lebesgue_measure numfun exp trigo.
From mathcomp Require Import realfun lebesgue_integral kernel charge prob_lang.

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

Section gauss_pdf.
Context {R : realType}.
Local Open Scope ring_scope.

Definition gauss_pdf m s x : R :=
  (s * sqrtr (pi *+ 2))^-1 * expR (- ((x - m) / s) ^+ 2 / 2%:R).

Lemma gauss_pdf_ge0 m s x : 0 <= s -> 0 <= gauss_pdf m s x.
Proof. by move=> s0; rewrite mulr_ge0 ?expR_ge0// invr_ge0 mulr_ge0. Qed.

Lemma gauss_pdf_gt0 m s x : 0 < s -> 0 < gauss_pdf m s x.
Proof.
move=> s0; rewrite mulr_gt0 ?expR_gt0// invr_gt0 mulr_gt0//.
by rewrite sqrtr_gt0 pmulrn_rgt0// pi_gt0.
Qed.

Lemma measurable_gauss_pdf m s : measurable_fun setT (gauss_pdf m s).
Proof.
apply: measurable_funM => //=; apply: measurableT_comp => //=.
apply: measurable_funM => //=; apply: measurableT_comp => //=.
apply: measurableT_comp (exprn_measurable _) _ => /=.
by apply: measurable_funM => //=; exact: measurable_funD.
Qed.

Definition gauss_pdf01 : R -> R := gauss_pdf 0 1.

Lemma gauss_pdf01E x :
  gauss_pdf01 x = (sqrtr (pi *+ 2))^-1 * expR (- (x ^+ 2) / 2%:R).
Proof. by rewrite /gauss_pdf01 /gauss_pdf mul1r subr0 divr1. Qed.

Lemma gauss_pdf01_ub x : gauss_pdf01 x <= (Num.sqrt (pi *+ 2))^-1.
Proof.
rewrite -[leRHS]mulr1.
rewrite /gauss_pdf01 /gauss_pdf; last first.
rewrite mul1r subr0 ler_pM2l ?invr_gt0// ?sqrtr_gt0; last by rewrite mulrn_wgt0// pi_gt0.
by rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 mulr_ge0// sqr_ge0.
Qed.

Lemma continuous_gauss_pdf1 x : {for x, continuous gauss_pdf01}.
Proof.
apply: continuousM => //=; first exact: cvg_cst.
apply: continuous_comp => /=; last exact: continuous_expR.
apply: continuousM => //=; last exact: cvg_cst.
apply: continuous_comp => //=; last exact: continuousN.
apply: (@continuous_comp _ _ _ _ (fun x : R => x ^+ 2)%R); last exact: exprn_continuous.
apply: continuousM => //=; last exact: cvg_cst.
by apply: continuousD => //=; exact: cvg_cst.
Qed.

End gauss_pdf.

Definition gauss01 {R : realType}
  of \int[@lebesgue_measure R]_x (gauss_pdf01 x)%:E = 1%E : set _ -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (gauss_pdf01 x)%:E)%E.

Section gauss.
Variable R : realType.
Local Open Scope ring_scope.

Hypothesis integral_gauss_pdf01 :
  (\int[@lebesgue_measure R]_x (gauss_pdf01 x)%:E = 1%E)%E.

Local Notation gauss01 := (gauss01 integral_gauss_pdf01).

Let gauss010 : gauss01 set0 = 0%E.
Proof. by rewrite /gauss01 integral_set0. Qed.

Let gauss01_ge0 A : (0 <= gauss01 A)%E.
Proof.
by rewrite /gauss01 integral_ge0//= => x _; rewrite lee_fin gauss_pdf_ge0.
Qed.

Let gauss01_sigma_additive : semi_sigma_additive gauss01.
Proof.
move=> /= F mF tF mUF.
rewrite /gauss01/= integral_bigcup//=; last first.
  apply/integrableP; split.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_gauss_pdf.
  rewrite (_ : (fun x => _) = EFin \o gauss_pdf01); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin gauss_pdf_ge0.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/EFin_measurable_fun; exact: measurable_gauss_pdf.
    by move=> ? _; rewrite lee_fin gauss_pdf_ge0.
  by rewrite integral_gauss_pdf01 // ltey.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin gauss_pdf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  gauss01 gauss010 gauss01_ge0 gauss01_sigma_additive.

Let gauss01_setT : gauss01 [set: _] = 1%E.
Proof. by rewrite /gauss01 integral_gauss_pdf01. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R gauss01 gauss01_setT.

End gauss.

Section gauss_lebesgue.
Context d (T : measurableType d) (R : realType).
Notation mu := (@lebesgue_measure R).
Hypothesis integral_gauss_pdf01 : \int[mu]_x (gauss_pdf01 x)%:E = 1%E.

Lemma gauss01_dom : gauss01 integral_gauss_pdf01 `<< mu.
Proof.
move=> A mA muA0; rewrite /gauss01.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: integral_ge0 => x _; rewrite lee_fin gauss_pdf_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A) (Num.sqrt (pi *+ 2))^-1%:E))%E; last first.
  by rewrite integral_cst//= muA0 mule0.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin gauss_pdf_ge0.
- apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_gauss_pdf.
- by move=> x _; rewrite lee_fin gauss_pdf01_ub.
Qed.

Let f1 (x : g_sigma_algebraType (R.-ocitv.-measurable)) := (gauss_pdf01 x) ^-1.

Lemma measurable_fun_f1 : measurable_fun setT f1.
Proof.
apply: continuous_measurable_fun => x.
apply: (@continuousV _ _ gauss_pdf01).
  by rewrite gt_eqF// gauss_pdf_gt0.
exact: continuous_gauss_pdf1.
Qed.

Lemma integrable_f1 U : measurable U ->
  (gauss01 integral_gauss_pdf01).-integrable U (fun x : g_sigma_algebraType (R.-ocitv.-measurable) => (f1 x)%:E).
Proof.
Admitted.

Lemma integral_mgauss01 : forall U, measurable U ->
  \int[gauss01 integral_gauss_pdf01]_(y in U) (f1 y)%:E =
  \int[mu]_(x0 in U) (gauss_pdf01 x0 * f1 x0)%:E.
Proof.
move=> U mU.
under [in RHS]eq_integral do rewrite EFinM/= muleC.
rewrite -(Radon_Nikodym_change_of_variables gauss01_dom _ (integrable_f1 mU))//=.
apply: ae_eq_integral => //=.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply: measurable_int.
  apply: integrableS (Radon_Nikodym_integrable _) => //=.
  exact: gauss01_dom.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_gauss_pdf.
- apply: ae_eq_mul2l => /=.
  rewrite Radon_NikodymE//=.
    exact: gauss01_dom.
  move=> gauss01_dom'.
  case: cid => //= h [h1 h2 h3].
  apply: integral_ae_eq => //=.
  + exact: integrableS h2.
  + apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_gauss_pdf.
  + by move=> E EU mE; rewrite -(h3 _ mE).
Qed.

(*Hypothesis integral_mgauss01 : forall U, measurable U ->
  \int[gauss01 integral_gauss_pdf01]_(y in U) (f1 y)%:E =
  \int[mu]_(x0 in U) (gauss_pdf01 x0 * f1 x0)%:E.*)

Let mf1 : measurable_fun setT f1.
Proof.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- by move=> /= r [t _ <-]; rewrite gt_eqF// gauss_pdf_gt0.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_gauss_pdf.
Qed.

Definition staton_lebesgue : R.-sfker T ~> _ :=
  letin (sample_cst (gauss01 integral_gauss_pdf01 : pprobability _ _))
  (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

Lemma staton_lebesgueE x U : measurable U ->
  staton_lebesgue x U = lebesgue_measure U.
Proof.
move=> mU; rewrite [in LHS]/staton_lebesgue/=.
rewrite [in LHS]letinE /=.
transitivity (\int[gauss01 integral_gauss_pdf01]_(y in U) (f1 y)%:E).
  rewrite -[in RHS](setTI U) integral_mkcondr/=.
  apply: eq_integral => //= r _.
  rewrite letinE/= ge0_integral_mscale//= ger0_norm//; last first.
    by rewrite invr_ge0// gauss_pdf_ge0.
  rewrite integral_dirac// diracT mul1e/= diracE epatch_indic/=.
  by rewrite indicE.
rewrite integral_mgauss01//.
transitivity (\int[lebesgue_measure]_(x in U) (\1_U x)%:E).
  apply: eq_integral => /= y yU.
  by rewrite /f1 divrr ?indicE ?yU// unitfE gt_eqF// gauss_pdf_gt0.
by rewrite integral_indic//= setIid.
Qed.

End gauss_lebesgue.

(* assuming x > 0 *)
Definition Gamma {R : realType} (x : R) : \bar R :=
  \int[lebesgue_measure]_(t in `[0%R, +oo[%classic) (expR (- t) * powR t (x - 1))%:E.

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
    apply/EFin_measurable_fun.
    exact: measurable_funS (measurable_poisson_pdf _).
  rewrite (_ : (fun x => _) = (EFin \o poisson1)); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin poisson1_ge0//.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/EFin_measurable_fun; exact: measurable_poisson_pdf.
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
