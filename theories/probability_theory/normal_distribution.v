(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import measure exp trigo numfun realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc gauss_integral.

(**md**************************************************************************)
(* # Normal distribution                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*        normal_peak s := (sqrtr (s ^+ 2 * pi *+ 2))^-1                      *)
(*     normal_fun m s x := expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2))              *)
(*       normal_pdf m s == pdf of the normal distribution with mean m and     *)
(*                         standard deviation s                               *)
(*                         Using normal_peak and normal_pdf.                  *)
(*      normal_prob m s == normal probability measure                         *)
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

Section normal_density.
Context {R : realType}.
Local Open Scope ring_scope.
Local Import Num.ExtraDef.
Implicit Types m s x : R.

Definition normal_fun m s x := expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)).

Lemma measurable_normal_fun m s : measurable_fun [set :R] (normal_fun m s).
Proof.
apply: measurableT_comp => //=; apply: measurable_funM => //=.
apply: measurableT_comp => //=; apply: measurable_funX => //=.
exact: measurable_funB.
Qed.

Lemma normal_fun_ge0 m s x : 0 <= normal_fun m s x.
Proof. exact: expR_ge0. Qed.

Lemma normal_fun_center m s : normal_fun m s = normal_fun 0 s \o center m.
Proof. by apply/funext => x/=; rewrite /normal_fun/= subr0. Qed.

Definition normal_peak s := (sqrtr (s ^+ 2 * pi *+ 2))^-1.

Lemma normal_peak_ge0 s : 0 <= normal_peak s. Proof. by rewrite invr_ge0. Qed.

Lemma normal_peak_gt0 s : s != 0 -> 0 < normal_peak s.
Proof.
move=> s0; rewrite invr_gt0// sqrtr_gt0.
by rewrite mulrn_wgt0// mulr_gt0 ?pi_gt0// exprn_even_gt0/=.
Qed.

Let normal_pdf0 m s x : R := normal_peak s * normal_fun m s x.

Definition normal_pdf m s x :=
  if s == 0 then \1_`[0, 1] x else normal_pdf0 m s x.

Lemma normal_pdfE m s : s != 0 -> normal_pdf m s = normal_pdf0 m s.
Proof. by rewrite /normal_pdf; have [_|s0] := eqVneq s 0. Qed.

Let normal_pdf0_center m s : normal_pdf0 m s = normal_pdf0 0 s \o center m.
Proof. by rewrite /normal_pdf0 normal_fun_center. Qed.

Let normal_pdf0_ge0 m s x : 0 <= normal_pdf0 m s x.
Proof. by rewrite mulr_ge0 ?normal_peak_ge0 ?expR_ge0. Qed.

Let normal_pdf0_gt0 m s x : s != 0 -> 0 < normal_pdf0 m s x.
Proof. by move=> s0; rewrite mulr_gt0 ?expR_gt0// normal_peak_gt0. Qed.

Let measurable_normal_pdf0 m s : measurable_fun setT (normal_pdf0 m s).
Proof. by apply: measurable_funM => //=; exact: measurable_normal_fun. Qed.

Lemma measurable_normal_pdf m s : measurable_fun setT (normal_pdf m s).
Proof.
by rewrite /normal_pdf; have [_|] := eqVneq s 0; first exact: measurable_indic.
Qed.

Let continuous_normal_pdf0 m s : continuous (normal_pdf0 m s).
Proof.
move=> x; apply: cvgM; first exact: cvg_cst.
apply: (cvg_comp _ expR); last exact: continuous_expR.
apply: cvgM; last exact: cvg_cst.
apply: (@cvgN _ R^o).
apply: (cvg_comp (fun x => x - m) (fun x => x ^+ 2)).
  by apply: (@cvgB _ R^o) => //; [exact: cvg_id|exact: cvg_cst].
exact: sqr_continuous.
Qed.

Let normal_pdf0_ub m s x : normal_pdf0 m s x <= normal_peak s.
Proof.
rewrite /normal_pdf0 ler_piMr ?normal_peak_ge0//.
rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 mulr_ge0// ?sqr_ge0//.
by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
Qed.

Lemma normal_pdf_ge0 m s x : 0 <= normal_pdf m s x.
Proof. by rewrite /normal_pdf; case: ifP. Qed.

Lemma continuous_normal_pdf m s : s != 0 -> continuous (normal_pdf m s).
Proof. by rewrite /normal_pdf; have [|] := eqVneq s 0. Qed.

Lemma normal_pdf_ub m s x : s != 0 -> normal_pdf m s x <= normal_peak s.
Proof. by rewrite /normal_pdf; have [|] := eqVneq s 0. Qed.

End normal_density.

Definition normal_prob {R : realType} (m : R) (s : R) : set _ -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (normal_pdf m s x)%:E)%E.

Section normal_probability.
Variables (R : realType) (m sigma : R).
Local Open Scope ring_scope.
Notation mu := lebesgue_measure.

Local Notation normal_peak := (normal_peak sigma).
Local Notation normal_fun := (normal_fun m sigma).

Let F (x : R^o) := (x - m) / (Num.sqrt (sigma ^+ 2 *+ 2)).

Let normal_gauss_fun x : normal_fun x = gauss_fun (F x).
Proof.
congr expR; rewrite mulNr exprMn exprVn; congr (- (_ * _^-1)%R).
by rewrite sqr_sqrtr// pmulrn_lge0// sqr_ge0.
Qed.

Let F'E : F^`()%classic = cst (Num.sqrt (sigma ^+ 2 *+ 2))^-1.
Proof.
apply/funext => x; rewrite /F derive1E deriveM// deriveD// derive_cst scaler0.
by rewrite add0r derive_id derive_cst addr0 scaler1.
Qed.

Let integral_gaussFF' : sigma != 0 ->
  (\int[mu]_x ((((gauss_fun \o F) *
     (F^`())%classic) x)%:E * (Num.sqrt (sigma ^+ 2 *+ 2))%:E))%E =
  normal_peak^-1%:E.
Proof.
move=> s0; rewrite /normal_peak invrK.
rewrite -mulrnAr -[in RHS]mulr_natr sqrtrM ?(sqrtrM 2) ?sqr_ge0 ?pi_ge0// !EFinM.
rewrite muleCA ge0_integralZr//=; first last.
  by move=> x _; rewrite lee_fin mulr_ge0//= ?gauss_fun_ge0// F'E/= invr_ge0.
  rewrite F'E; apply/measurable_EFinP/measurable_funM => //.
  apply/measurableT_comp => //; first exact: measurable_gauss_fun.
  by apply: measurable_funM => //; exact: measurable_funD.
congr *%E; last by rewrite -(mulr_natr (_ ^+ 2)) sqrtrM ?sqr_ge0.
rewrite -increasing_ge0_integration_by_substitutionT//.
- exact: integralT_gauss.
- move=> x y xy; rewrite /F ltr_pM2r ?ltr_leB ?gt_eqF//.
  by rewrite invr_gt0 ?sqrtr_gt0 ?pmulrn_lgt0 ?exprn_even_gt0.
- by rewrite F'E => ?; exact: cvg_cst.
- by rewrite F'E; exact: is_cvg_cst.
- by rewrite F'E; exact: is_cvg_cst.
- apply/gt0_cvgMlNy; last exact: cvg_addrr_Ny.
  by rewrite invr_gt0// sqrtr_gt0 -mulr_natr mulr_gt0// exprn_even_gt0.
- apply/gt0_cvgMly; last exact: cvg_addrr.
  by rewrite invr_gt0// sqrtr_gt0 -mulr_natr mulr_gt0// exprn_even_gt0.
- exact: continuous_gauss_fun.
- by move=> x; rewrite gauss_fun_ge0.
Qed.

Let integral_normal_fun : sigma != 0 ->
  (\int[mu]_x (normal_fun x)%:E)%E = normal_peak^-1%:E.
Proof.
move=> s0; rewrite -integral_gaussFF'//; apply: eq_integral => /= x _.
rewrite F'E !fctE/= -EFinM divfK// ?normal_gauss_fun//.
by rewrite gt_eqF// sqrtr_gt0 pmulrn_lgt0// exprn_even_gt0.
Qed.

Let integrable_normal_fun : sigma != 0 ->
  mu.-integrable [set: R] (EFin \o normal_fun).
Proof.
move=> s0; apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_normal_fun.
under eq_integral do rewrite /= ger0_norm ?expR_ge0//.
by rewrite /= integral_normal_fun// ltry.
Qed.

Lemma integral_normal_pdf : (\int[mu]_x (normal_pdf m sigma x)%:E = 1%E)%E.
Proof.
rewrite /normal_pdf; have [_|s0] := eqVneq sigma 0.
  by rewrite integral_indic//= setIT lebesgue_measure_itv/= lte01 oppr0 adde0.
under eq_integral do rewrite EFinM.
rewrite integralZl//=; last exact: integrable_normal_fun.
by rewrite integral_normal_fun// -EFinM divff// gt_eqF// normal_peak_gt0.
Qed.

Lemma integrable_normal_pdf : mu.-integrable [set: R]
  (fun x => (normal_pdf m sigma x)%:E).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
apply/abse_integralP => //=; last by rewrite integral_normal_pdf abse1 ltry.
by apply/measurable_EFinP; exact: measurable_normal_pdf.
Qed.

Local Notation normal_pdf := (normal_pdf m sigma).
Local Notation normal_prob := (normal_prob m sigma).

Let normal0 : normal_prob set0 = 0%E.
Proof. by rewrite /normal_prob integral_set0. Qed.

Let normal_ge0 A : (0 <= normal_prob A)%E.
Proof.
rewrite /normal_prob integral_ge0//= => x _.
by rewrite lee_fin normal_pdf_ge0 ?ltW.
Qed.

Let normal_sigma_additive : semi_sigma_additive normal_prob.
Proof.
move=> /= A mA tA mUA.
rewrite /normal_prob/= integral_bigcup//=; last first.
  by apply: (integrableS _ _ (subsetT _)) => //; exact: integrable_normal_pdf.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin normal_pdf_ge0 ?ltW.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  normal_prob normal0 normal_ge0 normal_sigma_additive.

Let normal_setT : normal_prob [set: _] = 1%E.
Proof. by rewrite /normal_prob integral_normal_pdf. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R normal_prob normal_setT.

Lemma normal_prob_dominates : normal_prob `<< mu.
Proof.
apply/null_content_dominatesP=> A mA muA0; rewrite /normal_prob /normal_pdf.
have [s0|s0] := eqVneq sigma 0.
  apply: null_set_integral => //=; apply: measurable_funTS => /=.
  exact/measurable_EFinP/measurable_indic.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: integral_ge0 => x _.
  by rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A) (normal_peak)%:E))%E; last first.
  by rewrite integral_cst//= muA0 mule0.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
- apply/measurable_funTS/measurableT_comp => //=.
  by apply: measurable_funM => //; exact: measurable_normal_fun.
- by move=> x _; have := normal_pdf_ub m x s0; rewrite /normal_pdf (negbTE s0).
Qed.

End normal_probability.
