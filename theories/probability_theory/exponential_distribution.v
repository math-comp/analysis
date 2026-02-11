(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import measure exp realfun numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc.

(**md**************************************************************************)
(* # Exponential distribution                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*    exponential_pdf r == pdf of the exponential distribution with rate r    *)
(*   exponential_prob r == exponential probability measure                    *)
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

Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable rate : R.
Hypothesis rate_ge0 : 0 <= rate.

Let exponential_pdfT x := rate * expR (- rate * x).
Definition exponential_pdf := exponential_pdfT \_ `[0, +oo[.

Lemma exponential_pdf_ge0 x : 0 <= exponential_pdf x.
Proof. by apply: restrict_ge0 => {}x _; rewrite  mulr_ge0 ?expR_ge0. Qed.

Lemma lt0_exponential_pdf x : x < 0 -> exponential_pdf x = 0.
Proof.
move=> x0; rewrite /exponential_pdf patchE ifF//.
by apply/negP; rewrite inE/= in_itv/= andbT; apply/negP; rewrite -ltNge.
Qed.

Let continuous_exponential_pdfT : continuous exponential_pdfT.
Proof.
move=> x.
apply: (@continuousM _ R^o (fun=> rate) (fun x => expR (- rate * x))).
  exact: cst_continuous.
apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM => //; apply: (@continuousN _ R^o); exact: cst_continuous.
Qed.

Lemma measurable_exponential_pdf : measurable_fun [set: R] exponential_pdf.
Proof.
apply/measurable_restrict => //; apply: measurable_funTS.
exact: continuous_measurable_fun.
Qed.

Lemma exponential_pdfE x : 0 <= x -> exponential_pdf x = exponential_pdfT x.
Proof.
by move=> x0; rewrite /exponential_pdf patchE ifT// inE/= in_itv/= x0.
Qed.

Lemma in_continuous_exponential_pdf :
  {in `]0, +oo[%R, continuous exponential_pdf}.
Proof.
move=> x; rewrite in_itv/= andbT => x0.
apply/(@cvgrPdist_lt _ R^o) => e e0; near=> y.
rewrite 2?(exponential_pdfE (ltW _))//; last by near: y; exact: lt_nbhsr.
near: y; move: e e0; apply/(@cvgrPdist_lt _ R^o).
by apply: continuous_comp => //; exact: continuous_exponential_pdfT.
Unshelve. end_near. Qed.

Lemma within_continuous_exponential_pdf :
  {within `[0, +oo[%classic, continuous exponential_pdf}.
Proof.
apply/continuous_within_itvcyP; split.
  exact: in_continuous_exponential_pdf.
apply/(@cvgrPdist_le _ R^o) => e e0; near=> t.
rewrite 2?exponential_pdfE//.
near: t; move: e e0; apply/cvgrPdist_le.
by apply: cvg_at_right_filter; exact: continuous_exponential_pdfT.
Unshelve. end_near. Qed.

End exponential_pdf.

Definition exponential_prob {R : realType} (rate : R) :=
  fun V => (\int[lebesgue_measure]_(x in V) (exponential_pdf rate x)%:E)%E.

Section exponential_prob.
Context {R : realType}.
Local Open Scope ring_scope.
Notation mu := lebesgue_measure.
Variable rate : R.

Lemma derive1_exponential_pdf :
  {in `]0, +oo[%R, (fun x => - expR (- rate * x))^`()%classic
                   =1 exponential_pdf rate}.
Proof.
move=> z; rewrite in_itv/= andbT => z0.
rewrite derive1_comp// derive1N// derive1_id mulN1r derive1_comp// derive1E.
have /funeqP -> := @derive_expR R.
by rewrite derive1Ml// derive1_id mulr1 mulrN opprK mulrC exponential_pdfE ?ltW.
Qed.

Let cexpNM : continuous (fun z : R^o => expR (- rate * z)).
Proof.
move=> z; apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM => //; apply: (@continuousN _ R^o); exact: cst_continuous.
Qed.

Lemma exponential_prob_itv0c (x : R) : 0 < x ->
  exponential_prob rate `[0, x] = (1 - (expR (- rate * x))%:E)%E.
Proof.
move=> x0.
rewrite (_ : 1 = - (- expR (- rate * 0))%:E)%E; last first.
  by rewrite mulr0 expR0 EFinN oppeK.
rewrite addeC.
apply: (@continuous_FTC2 _ _ (fun x => - expR (- rate * x))) => //.
- apply: (@continuous_subspaceW R^o _ _ [set` `[0, +oo[%R]).
  + exact: subset_itvl.
  + exact: within_continuous_exponential_pdf.
- split.
  + by move=> z _; exact: ex_derive.
  + by apply/cvg_at_right_filter; apply: cvgN; exact: cexpNM.
  + by apply/cvg_at_left_filter; apply: cvgN; exact: cexpNM.
- move=> z; rewrite in_itv/= => /andP[z0 _].
  by apply: derive1_exponential_pdf; rewrite in_itv/= andbT.
Qed.

Lemma integral_exponential_pdf : 0 < rate ->
  (\int[mu]_x (exponential_pdf rate x)%:E = 1)%E.
Proof.
move=> rate0.
have mEex : measurable_fun setT (EFin \o exponential_pdf rate).
  by apply/measurable_EFinP; exact: measurable_exponential_pdf.
rewrite -(setUv `[0, +oo[%classic) ge0_integral_setU//=; last 4 first.
  exact: measurableC.
  by rewrite setUv.
  by move=> x _; rewrite lee_fin exponential_pdf_ge0// ltW.
  exact/disj_setPCl.
rewrite [X in _ + X]integral0_eq ?adde0; last first.
  by move=> x x0; rewrite /exponential_pdf patchE ifF// memNset.
rewrite (@ge0_continuous_FTC2y _ _
  (fun x => - (expR (- rate * x))) _ 0)//.
- by rewrite mulr0 expR0 EFinN oppeK add0e.
- by move=> x _; apply: exponential_pdf_ge0; exact: ltW.
- exact: within_continuous_exponential_pdf.
- rewrite -oppr0; apply: cvgN.
  rewrite (_ : (fun x => expR (- rate * x)) =
               (fun z => expR (- z)) \o (fun z => rate * z)); last first.
    by apply: eq_fun => x; rewrite mulNr.
  apply: (@cvg_comp _ _ _ _ _ _ (pinfty_nbhs R)); last exact: cvgr_expR.
  exact: gt0_cvgMry.
- by apply: cvgN; apply/cvg_at_right_filter; exact: cexpNM.
- exact: derive1_exponential_pdf.
Qed.

Lemma integrable_exponential_pdf : 0 < rate ->
  mu.-integrable setT (EFin \o (exponential_pdf rate)).
Proof.
move=> rate0.
have mEex : measurable_fun setT (EFin \o exponential_pdf rate).
  by apply/measurable_EFinP; exact: measurable_exponential_pdf.
apply/integrableP; split => //.
under eq_integral do rewrite /= ger0_norm ?(exponential_pdf_ge0 (ltW _))//.
by rewrite /= integral_exponential_pdf// ltry.
Qed.

Hypothesis rate_gt0 : 0 < rate.

Local Notation exponential := (exponential_prob rate).

Let exponential0 : exponential set0 = 0%E.
Proof. by rewrite /exponential integral_set0. Qed.

Let exponential_ge0 A : (0 <= exponential A)%E.
Proof.
rewrite /exponential integral_ge0//= => x _.
by rewrite lee_fin exponential_pdf_ge0// ltW.
Qed.

Let exponential_sigma_additive : semi_sigma_additive exponential.
Proof.
move=> /= F mF tF mUF; rewrite /exponential; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _; apply: integral_ge0 => /= x Fkx.
  by rewrite lee_fin exponential_pdf_ge0// ltW.
rewrite ge0_integral_bigcup//=.
- apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_exponential_pdf.
- by move=> x _; rewrite lee_fin exponential_pdf_ge0// ltW.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  exponential exponential0 exponential_ge0 exponential_sigma_additive.

Let exponential_setT : exponential [set: R] = 1%E.
Proof. by rewrite /exponential integral_exponential_pdf. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R exponential exponential_setT.

End exponential_prob.
