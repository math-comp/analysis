(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference ring.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import measure exp trigo numfun realfun.
From mathcomp Require Import measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc gauss_integral charge.

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

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_peak.
Context {R : realType}.
Local Open Scope ring_scope.
Implicit Types m s x : R.

Definition normal_peak s := (sqrtr (s ^+ 2 * pi *+ 2))^-1.

Lemma normal_peak_ge0 s : 0 <= normal_peak s. Proof. by rewrite invr_ge0. Qed.

Lemma normal_peak_gt0 s : s != 0 -> 0 < normal_peak s.
Proof.
move=> s0; rewrite invr_gt0// sqrtr_gt0.
by rewrite mulrn_wgt0// mulr_gt0 ?pi_gt0// exprn_even_gt0/=.
Qed.

End normal_peak.

Section normal_fun.
Context {R : realType}.
Local Open Scope ring_scope.
Implicit Types m s x : R.

Definition normal_fun m s x := expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)).

Lemma measurable_normal_fun m s : measurable_fun [set: R] (normal_fun m s).
Proof.
apply: measurableT_comp => //=; apply: measurable_funM => //=.
apply: measurableT_comp => //=; apply: measurable_funX => //=.
exact: measurable_funB.
Qed.

Lemma normal_fun_ge0 m s x : 0 <= normal_fun m s x.
Proof. exact: expR_ge0. Qed.

Lemma normal_fun_center0 m s : normal_fun m s = normal_fun 0 s \o center m.
Proof. by apply/funext => x/=; rewrite /normal_fun/= subr0. Qed.

Lemma normal_funN m s x : normal_fun (- m) s (- x) = normal_fun m s x.
Proof. by rewrite /normal_fun -opprD sqrrN. Qed.

Lemma normal_fun_sym m s x : normal_fun m s x = normal_fun x s m.
Proof. by rewrite /normal_fun -(sqrrN (x - _)) opprB. Qed.

Lemma normal_fun0abs s x : normal_fun 0 s `|x| = normal_fun 0 s x.
Proof. by rewrite /normal_fun 2!subr0 real_normK// num_real. Qed.

Lemma normal_fun_shift m s x t :
  normal_fun (shift m t) s (shift x t) = normal_fun m s x.
Proof. by rewrite [in LHS]/normal_fun/= (addrC t x) addrKA. Qed.

#[deprecated(since="mathcomp-analysis 1.17.0", note="to be renamed to `normal_fun_center`")]
Lemma normal_fun_center_new m s x t :
  normal_fun (center m t) s (center x t) = normal_fun m s x.
Proof. by rewrite normal_fun_shift normal_funN. Qed.

End normal_fun.
#[deprecated(since="mathcomp-analysis 1.17.0", note="renamed to `normal_fun_center0`")]
Notation normal_fun_center := normal_fun_center0 (only parsing).

Module NormalPdf0.
(* this module contains facts that are used internally in proofs below*)
Section normal_pdf0.
Context {R : realType}.
Local Open Scope ring_scope.
Implicit Types m s x : R.

Definition normal_pdf0 m s x : R := normal_peak s * normal_fun m s x.

Lemma normal_pdf0_ge0 m s x : 0 <= normal_pdf0 m s x.
Proof. by rewrite mulr_ge0 ?normal_peak_ge0 ?expR_ge0. Qed.

Lemma normal_pdf0_gt0 m s x : s != 0 -> 0 < normal_pdf0 m s x.
Proof. by move=> s0; rewrite mulr_gt0 ?expR_gt0// normal_peak_gt0. Qed.

Lemma measurable_normal_pdf0 m s : measurable_fun setT (normal_pdf0 m s).
Proof. by apply: measurable_funM => //=; exact: measurable_normal_fun. Qed.

Lemma continuous_normal_pdf0 m s : continuous (normal_pdf0 m s).
Proof.
move=> x; apply: cvgM; first exact: cvg_cst.
apply: (cvg_comp _ expR); last exact: continuous_expR.
apply: cvgM; last exact: cvg_cst.
apply: (@cvgN _ R^o).
apply: (cvg_comp (fun x => x - m) (fun x => x ^+ 2)).
  by apply: (@cvgB _ R^o) => //; [exact: cvg_id|exact: cvg_cst].
exact: sqr_continuous.
Qed.

Lemma normal_pdf0_ub m s x : normal_pdf0 m s x <= normal_peak s.
Proof.
rewrite /normal_pdf0 ler_piMr ?normal_peak_ge0//.
rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 mulr_ge0// ?sqr_ge0//.
by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
Qed.

Lemma normal_pdf0xx s e : normal_pdf0 e s e = normal_peak s.
Proof.
by rewrite /normal_pdf0 /normal_fun subrr expr0n/= oppr0 mul0r expR0 mulr1.
Qed.

Lemma normal_pdf0_sym m s x : normal_pdf0 m s x = normal_pdf0 x s m.
Proof. by rewrite /normal_pdf0 normal_fun_sym. Qed.

Lemma normal_pdf0N m s : normal_pdf0 (- m) s (- m) = normal_pdf0 m s m.
Proof. by rewrite /normal_pdf0 normal_funN. Qed.

Lemma normal_pdf0_center m s x t :
  normal_pdf0 (center m t) s (center x t) = normal_pdf0 m s x.
Proof. by rewrite /normal_pdf0 normal_fun_center_new. Qed.

Lemma normal_pdf0_shift m s x t :
  normal_pdf0 (shift m t) s (shift x t) = normal_pdf0 m s x.
Proof. by rewrite /normal_pdf0 normal_fun_shift. Qed.

End normal_pdf0.
End NormalPdf0.

Section normal_density.
Context {R : realType}.
Local Open Scope ring_scope.
Local Import Num.ExtraDef.
Implicit Types m s x : R.

Import NormalPdf0.

Definition normal_pdf m s x :=
  if s == 0 then \1_`[0, 1] x else normal_pdf0 m s x.

Lemma normal_pdfE m s : s != 0 ->
  normal_pdf m s = (fun x => normal_peak s * normal_fun m s x).
Proof. by rewrite /normal_pdf; have [_|s0] := eqVneq s 0. Qed.

Lemma normal_pdf_sym m s x : s != 0 ->
  normal_pdf m s x = normal_pdf x s m.
Proof. by move=> s0; rewrite !normal_pdfE// normal_fun_sym. Qed.

Lemma measurable_normal_pdf m s : measurable_fun setT (normal_pdf m s).
Proof.
rewrite /normal_pdf; have [_|s0] := eqVneq s 0; first exact: measurable_indic.
exact: measurable_normal_pdf0.
Qed.

Lemma normal_pdf_ge0 m s x : 0 <= normal_pdf m s x.
Proof. by rewrite /normal_pdf; case: ifP => // _; exact: normal_pdf0_ge0. Qed.

Lemma continuous_normal_pdf m s : s != 0 -> continuous (normal_pdf m s).
Proof.
rewrite /normal_pdf; have [//|s0 _] := eqVneq s 0.
exact: continuous_normal_pdf0.
Qed.

Lemma normal_pdf_ub m s x : s != 0 -> normal_pdf m s x <= normal_peak s.
Proof.
rewrite /normal_pdf; have [//|s0 _] := eqVneq s 0.
exact: normal_pdf0_ub.
Qed.

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
rewrite muleCA ge0_integralZr//=.
- rewrite F'E; apply/measurable_EFinP/measurable_funM => //.
  apply/measurableT_comp => //; first exact: measurable_gauss_fun.
  by apply: measurable_funM => //; exact: measurable_funD.
- by move=> x _; rewrite lee_fin mulr_ge0//= ?gauss_fun_ge0// F'E/= invr_ge0.
congr *%E; last by rewrite -(mulr_natr (_ ^+ 2)) sqrtrM ?sqr_ge0.
rewrite -increasing_ge0_integration_by_substitutionT//.
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
- exact: integralT_gauss.
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
rewrite integralZl//=; first exact: integrable_normal_fun.
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
rewrite /normal_prob/= integral_bigcup//=.
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

Local Open Scope charge_scope.

Lemma normal_pdf_uniq_ae : ae_eq mu [set: R]
  ('d (charge_of_finite_measure normal_prob) '/d mu)
  (EFin \o normal_pdf).
Proof.
apply: integral_ae_eq => //.
- by apply: Radon_Nikodym_integrable => /=; exact: normal_prob_dominates.
- by apply/measurable_EFinP; exact: measurable_normal_pdf.
- move=> /= E _ mE.
  by rewrite -Radon_Nikodym_integral//=; exact: normal_prob_dominates.
Qed.

Local Close Scope charge_scope.

End normal_probability.

Section normal_prob_continuous.
(* outline of proof:
   1. It is enough to prove that `(fun x => normal_prob x s Ys)` is continuous
      for all measurable set `Ys`.
   2. Continuity is obtained by continuity under integral from continuity of
      `normal_pdf`.
   3. Fix a point `a` in `R` and `e` with `0 < e`. Then take the function
      `g : R -> R` as that `g x` is the maximum value of
      `normal_pdf a s x` at a point within `e` of `x`.
      Then `g x` is equal to `normal_pdf a s 0` if `x` in `ball a e`,
       `normal_pdf a s (x - e)` for x > a + e,
       and `normal_pdf a s (x + e)` for x < a - e.
   4. Integrability of `g` is checked by calculating integration.
      By integration by substitution, the integral of `g` on ]-oo, a - e]
      is equal to the integral of `normal_pdf a s` on `]-oo, a],
      and it on `[a + e, +oo[ similarly.
      So the integral of `g` on ]-oo, +oo[ is the integral of `f` on ]-oo, +oo[
      added by the integral of `normal_pdf a s x` on ]a - e, a + e[
 *)
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Variable s : R.
Hypothesis s0 : s != 0.
Implicit Types a e x : R.

Import NormalPdf0.

Let g' a e x : R := if x \in (ball a e : set R^o) then
  normal_peak s else normal_pdf0 e s `|x - a|.

Let mg' a e : measurable_fun [set: R] (g' a e).
Proof.
apply: measurable_fun_if => //=.
  apply: (measurable_fun_bool true) => /=.
  by rewrite setTI preimage_mem_true; exact: measurable_ball.
apply: measurable_funTS => /=; apply: measurable_funM => //.
apply: measurableT_comp => //; first exact: measurable_normal_fun.
by apply: measurableT_comp => //; exact: measurable_funD.
Qed.

Let g'a0 a : g' a 0 = normal_pdf0 a s.
Proof.
apply/funext => x; rewrite /g' memNset ?le0_ball0//.
by rewrite /normal_pdf0 normal_fun0abs [in RHS]normal_fun_center0.
Qed.

Let ballFE_le a e x : x <= (a - e)%R -> x \notin (ball a e : set R^o).
Proof.
by move=> xae; rewrite memNset// ball_itv/= in_itv/= !ltNge xae/=.
Qed.

Let ballFE_ge a e x : a + e <= x -> x \notin (ball a e : set R^o).
Proof.
by move=> xae; rewrite memNset// ball_itv/= in_itv/= !ltNge xae andbF.
Qed.

Let continuous_g' a e : 0 <= e -> continuous (g' a e).
Proof.
move=> e0.
have aNe k : k < a - e -> (`|k - a| - e) ^+ 2 = (k - (a - e)) ^+ 2.
  move=> kae; rewrite ler0_norm; last by rewrite -sqrrN !opprB addrCA.
  by rewrite subr_le0 (le_trans (ltW kae))// lerBlDl lerDr.
have pdf0B x : x < a - e -> normal_pdf0 e s `|x - a| = normal_pdf0 (a - e) s x.
  by move=> xae; rewrite /normal_pdf0 /normal_fun !aNe.
have aDe k : a + e < k -> (`|k - a| - e) ^+ 2 = (k - (a + e)) ^+ 2.
  move=> kae; rewrite opprD addrA.
  by rewrite ger0_norm// subr_ge0 (le_trans _ (ltW kae))// lerDl.
have pdf0D x : a + e < x -> normal_pdf0 e s `|x - a| = normal_pdf0 (a + e) s x.
  by move=> aex; rewrite /normal_pdf0 /normal_fun !aDe.
apply: in1TT => /=.
rewrite -continuous_open_subspace; first exact: openT.
rewrite (_ : [set: R] =
    `]-oo, (a - e)%R] `|` `[(a - e)%R, a + e] `|` `[a + e, +oo[).
  rewrite -setU_itvob1// -setUA setUAC setUA -itv_bndbnd_setU//.
    by rewrite bnd_simp lerD// ge0_cp.
  rewrite -setU_itvob1// -setUA setUAC setUA -itv_bndbnd_setU//.
  by rewrite set_itvE !setTU.
apply: withinU_continuous.
- rewrite -setU_itvob1// -setUA setUCA -itv_bndbnd_setU//.
    by rewrite bnd_simp lerD// ge0_cp.
  by rewrite setUidr// sub1set inE/= in_itv/= lerD// ge0_cp.
- exact: interval_closed.
- apply: withinU_continuous; [exact: interval_closed..| |].
  + apply/continuous_within_itvNycP; split.
    * move=> x xae; apply/cvgrPdist_le => /= eps eps0; near=> t.
      have tae : t < a - e by near: t; exact: lt_nbhsl.
      rewrite /g' !(negbTE (ballFE_le (ltW _)))// !pdf0B// {tae}.
      by near: t; apply: cvgr_dist_le eps eps0; exact: continuous_normal_pdf0.
    * apply/cvgrPdist_lt => eps eps0; near=> t.
      rewrite /g' !(negPf (ballFE_le _))// (addrC a) addrK normrN.
      rewrite (ger0_norm e0)// -(normal_pdf0_center _ _ _ a) pdf0B//.
      near: t; apply: cvgr_dist_lt eps eps0.
      by apply/cvg_at_left_filter; exact: continuous_normal_pdf0.
  move: e0; rewrite le_eqVlt => /predU1P[<-|e0].
    rewrite g'a0.
    by apply: continuous_subspaceT; exact: continuous_normal_pdf0.
  apply/continuous_within_itvP; first by rewrite -(opprK e) ler_ltB// opprK gtrN.
  split.
  + move=> x xae.
    rewrite /continuous_at /g' ifT; first by rewrite ball_itv inE.
    apply/cvgrPdist_le => eps eps0; near=> t.
    rewrite ifT; last by rewrite subrr normr0 ltW.
    rewrite ball_itv inE/= in_itv/=; apply/andP; split.
    - by near: t; apply: lt_nbhsr; rewrite (itvP xae).
    - by near: t; apply: lt_nbhsl; rewrite (itvP xae).
  + apply/cvgrPdist_le => eps eps0; near=> t.
    rewrite /g' (negPf (ballFE_le _))// ifT.
      rewrite ball_itv inE/= in_itv/=; apply/andP => []; split => //.
      by near: t; apply: nbhs_right_lt; rewrite ltrD2l gtrN.
    rewrite addrAC subrr sub0r normrN (gtr0_norm e0).
    by rewrite normal_pdf0xx subrr normr0 ltW.
  + apply/cvgrPdist_le => eps eps0; near=> t.
    rewrite /g' (negPf (ballFE_ge _))// ifT.
      rewrite ball_itv inE/= in_itv/=; apply/andP => []; split => //.
      by near: t; apply: nbhs_left_gt; rewrite ltrD2l gtrN.
    by rewrite (addrC a) addrK (gtr0_norm e0) normal_pdf0xx subrr normr0 ltW.
- apply/continuous_within_itvcyP; split.
  + move=> x; rewrite in_itv/= andbT => aex.
    apply/cvgrPdist_le => /= eps eps0; near=> t.
    have tae : a + e < t by near: t; exact: lt_nbhsr.
    rewrite /g' !(negPf (ballFE_ge (ltW _)))// !pdf0D//.
    by near: t; apply: cvgr_dist_le eps eps0; exact: continuous_normal_pdf0.
  + apply/cvgrPdist_le => eps eps0; near=> t.
    rewrite /g' !(negPf (ballFE_ge _))//.
    rewrite (addrC a) addrK (ger0_norm e0)//.
    rewrite -(normal_pdf0_shift e s _ a)/= pdf0D//.
    near: t; apply/cvgrPdist_le : eps eps0.
    by apply: cvg_at_right_filter; exact: continuous_normal_pdf0.
Unshelve. all: end_near. Qed.

Let gE_Ny a e : 0 <= e ->
  (\int[mu]_(x in `]-oo, (a - e)%R]) `|g' a e x|%:E =
   \int[mu]_(x in `]-oo, a]) `|normal_pdf a s x|%:E)%E.
Proof.
move=> e0; rewrite ge0_integration_by_substitution_shift_itvNy => /=.
- apply/continuous_subspaceT => x.
  by apply: continuous_comp; [exact: continuous_g'|exact: norm_continuous].
- by move=> ? _; exact: normr_ge0.
apply: eq_integral => /= x; rewrite inE/= in_itv/= => xae.
rewrite /g' (negPf (ballFE_le _)); first exact: lerB.
rewrite -(normrN (x - e - a)) !opprB addrA.
have /normr_idP -> : 0 <= a + e - x by rewrite subr_ge0 ler_wpDr.
rewrite /normal_pdf0 /normal_fun -(addrAC _ (- x)) addrK -(sqrrN (a - x)) opprB.
by rewrite -/(normal_pdf0 _ _ _) normal_pdfE.
Qed.

Let gE_y a e : 0 <= e ->
  (\int[mu]_(x in `[(a + e)%R, +oo[) `|g' a e x|%:E =
   \int[mu]_(x in `[a, +oo[) `|normal_pdf a s x|%:E)%E.
Proof.
move=> e0; rewrite ge0_integration_by_substitution_shift_itvy => /=.
- apply/continuous_subspaceT => /= x.
  by apply: continuous_comp; [exact: continuous_g'|exact: norm_continuous].
- by move=> ? _; exact: normr_ge0.
apply: eq_integral => /= x; rewrite inE/= in_itv/= andbT => aex.
rewrite /g' (negPf (ballFE_ge _))//; first exact: lerD.
have /normr_idP -> : 0 <= x + e - a by rewrite subr_ge0 ler_wpDr.
rewrite /normal_pdf0 /normal_fun -(addrAC _ (- a)) addrK -/(normal_pdf0 _ _ _).
by rewrite normal_pdfE.
Qed.

Lemma normal_prob_continuous (V : set R) : measurable V ->
  continuous (fun m => fine (normal_prob m s V)).
Proof.
move=> mV a.
near (0 : R)^'+ => e.
set g := g' a e.
have mg := mg' a e.
apply: (@continuity_under_integral _ _ _ mu _ _ _ (a - e) (a + e) _ _ g) => //=.
- move=> x _.
  by apply: (integrableS measurableT) => //=; exact: integrable_normal_pdf.
- apply/aeW => y Vy x aex.
  under eq_fun do rewrite normal_pdf_sym// normal_pdfE// -/(normal_pdf0 _ _ _).
  exact: continuous_normal_pdf0.
- apply: (integrableS measurableT) => //=.
  apply/integrableP; split; first exact/measurable_EFinP.
  rewrite -(setUv (ball a e)) ge0_integral_setU//=.
  + exact: measurable_ball.
  + by apply: measurableC; exact: measurable_ball.
  + by rewrite setUv; apply/measurable_EFinP; exact: measurableT_comp.
  + exact/disj_setPCl.
  rewrite lte_add_pinfty//.
    under eq_integral.
      move=> x xae; rewrite /g /g' xae; over.
    rewrite integral_cst/=; first exact: measurable_ball.
    by rewrite lte_mul_pinfty// lebesgue_measure_ball// ltry.
  rewrite [ltLHS](_ : _ = \int[mu]_x `|normal_pdf a s x|%:E)%E.
    rewrite ball_itv setCitv ge0_integral_setU//=.
    + apply: measurable_funTS; apply/measurable_EFinP.
      exact: measurableT_comp.
    + apply/disj_setPRL; rewrite setCitvl.
      by apply: subset_itvr; rewrite bnd_simp ltrD2l gtrN.
    + rewrite gE_Ny// gE_y// -integral_itvob_itvcb.
        apply/measurable_EFinP; apply: measurableT_comp => //.
        by apply: measurable_funTS; exact: measurable_normal_pdf.
      rewrite -ge0_integral_setU/= ?measurable_itv//.
        rewrite -setCitvl setUv.
        apply/measurable_EFinP; apply: measurableT_comp => //.
        exact: measurable_normal_pdf.
      by apply/disj_setPRL; rewrite setCitvl.
    by rewrite -setCitvl setUv.
  under eq_integral do rewrite -abse_EFin.
  apply/abse_integralP => //=.
    by apply/measurable_EFinP; exact: measurable_normal_pdf.
  by rewrite integral_normal_pdf ltry.
- move=> x aex; apply: aeW => /= y Vy.
  rewrite ger0_norm; first exact: normal_pdf_ge0.
  rewrite normal_pdfE// /g /g'.
  case: ifPn => [_|]; first exact: normal_pdf0_ub.
  rewrite notin_setE/= ball_itv/= in_itv/= => aey.
  rewrite /normal_pdf0 ler_pM//;[exact: normal_peak_ge0|exact: normal_fun_ge0|].
  rewrite ler_expR !mulNr lerN2 ler_wpM2r//.
    by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
  move/negP/nandP : aey; rewrite -!leNgt => -[yae|aey].
  + rewrite -normrN opprB ger0_norm.
      by rewrite subr_ge0 (le_trans yae)// gerBl.
    rewrite -[leRHS]sqrrN opprB ler_sqr ?nnegrE.
    * by rewrite addrAC subr_ge0.
    * by rewrite subr_ge0 ltW// (le_lt_trans yae)// (itvP aex).
    * by rewrite addrAC lerD2r (itvP aex).
  + rewrite ger0_norm.
      by rewrite subr_ge0 (le_trans _ aey)// lerDl.
    rewrite ler_sqr ?nnegrE.
    * by rewrite -addrA -opprD subr_ge0.
    * by rewrite subr_ge0 (le_trans _ aey)// (itvP aex).
    * by rewrite -addrA -opprD lerD2l lerN2 (itvP aex).
- by rewrite -ball_itv inE; exact: ballxx.
Unshelve. end_near. Qed.

End normal_prob_continuous.

Section normal_prob_lemmas.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.

Lemma integral_normal_prob (m s : R) f U : measurable U ->
  (normal_prob m s).-integrable U f ->
  \int[@normal_prob _ m s]_(x in U) f x =
  \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E).
Proof.
move=> mU /[dup] intf /integrableP[mf intf_lty].
rewrite -(Radon_Nikodym_change_of_variables (normal_prob_dominates m s))//=.
apply: ae_eq_integral => //=.
- apply: emeasurable_funM => //; apply: measurable_funTS => /=.
  have : charge_of_finite_measure (normal_prob m s) `<< mu.
    exact: normal_prob_dominates m s.
  by move=> /Radon_Nikodym_integrable /integrableP[].
- apply: emeasurable_funM => //; apply/measurable_EFinP.
  by apply/measurable_funTS; exact: measurable_normal_pdf.
- apply: ae_eqe_mul2l => /=; apply: (ae_eq_subset (@subsetT _ _)).
  exact: normal_pdf_uniq_ae.
Qed.

Lemma measurable_normal_prob (s : R) U : measurable U ->
  measurable_fun setT (fun x => normal_prob x s U).
Proof.
have [->/=|s0 mU] := eqVneq s 0%R.
  by rewrite /normal_prob /normal_pdf eqxx => _; exact: measurable_cst.
under [X in _ _ X]eq_fun.
  move=> /= x.
  rewrite -(@fineK _ (_ x _ _)).
    by rewrite fin_num_measure.
  over.
apply/measurable_EFinP; apply: continuous_measurable_fun.
exact: normal_prob_continuous.
Qed.

End normal_prob_lemmas.

Section emeasurable_bounded_integrable.
Context d {T : measurableType d} {R : realType}
  {p : {finite_measure set T -> \bar R}} {f : T -> \bar R}.
Local Open Scope ereal_scope.

(* TODO: move *)
Lemma emeasurable_bounded_integrable :
  (forall x, 0 <= f x) -> (exists M : R, forall x, f x <= M%:E) ->
  measurable_fun [set: T] f -> p.-integrable [set: T] f.
Proof.
move=> f0 [M fleM] mf; apply/integrableP; split => //.
rewrite (@le_lt_trans _ _ (\int[p]_x M%:E))//.
  apply: ge0_le_integral => //=.
    exact: measurableT_comp.
  move=> t _.
  apply: (@le_trans _ _ (f t)) => //.
  by rewrite gee0_abs.
by rewrite integral_cst// muleC lte_mul_pinfty ?ltry//; exact: fin_num_measure.
Qed.

End emeasurable_bounded_integrable.

Section normal_probD.
Local Open Scope ereal_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Import NormalPdf0.

Lemma integrable_normal_probD1 (m1 m2 s1 s2 : R) V : measurable V ->
  (normal_prob m1 s1).-integrable [set: R] (fun x => normal_prob (m2 + x) s2 V).
Proof.
move=> mV; apply: emeasurable_bounded_integrable => //=.
  by exists 1%R => ?; exact: probability_le1.
apply: (@measurableT_comp _ _ _ _ _ _
    (fun x => normal_prob x s2 V) _ (fun x => m2 + x)%R).
  exact: measurable_normal_prob.
exact: measurable_funD.
Qed.

Lemma normal_probD1 (m1 m2 s1 s2 : R) V : measurable V ->
  s1 != 0%R -> s2 != 0%R ->
  \int[normal_prob m1 s1]_x normal_prob (m2 + x) s2 V =
  \int[mu]_(y in V)
    \int[mu]_x (normal_pdf (m2 + x) s2 y * normal_pdf m1 s1 x)%:E.
Proof.
move=> mV s10 s20; rewrite integral_normal_prob//.
  exact: integrable_normal_probD1.
transitivity (\int[mu]_x \int[mu]_y
    ((normal_pdf (m2 + x) s2 y * normal_pdf m1 s1 x)%:E * (\1_V y)%:E)).
  apply: eq_integral => y _.
  rewrite /normal_prob -integralZr//=.
    by apply: (integrableS measurableT) => //; exact: integrable_normal_pdf.
  transitivity (\int[mu]_(x in V)
      (normal_pdf (m2 + y) s2 x * normal_pdf m1 s1 y)%:E).
    by apply: eq_integral => z _; rewrite -EFinM.
  by rewrite integral_mkcond epatch_indic.
rewrite (@fubini_tonelli _ _ _ _ _ mu mu (EFin \o
  (fun xz => (normal_pdf (m2 + xz.1) s2 xz.2 *
              normal_pdf m1 s1 xz.1)%R * \1_V xz.2)%R))/=.
- apply/measurable_EFinP; apply: measurable_funM => /=.
  apply: measurable_funM => /=.
    rewrite [X in measurable_fun _  X](_ : _ = (fun x =>
        normal_pdf0 0 s2 (x.2 - (m2 + x.1)%R)))/=.
      apply/funext => x0.
      by rewrite /normal_pdf0 normal_pdfE// normal_fun_center.
    apply: measurableT_comp => /=; first exact: measurable_normal_pdf0.
    under eq_fun do rewrite opprD.
    by apply: measurable_funD => //=; exact: measurable_funB.
- by apply: measurableT_comp => //; exact: measurable_normal_pdf.
- apply: measurable_indic => /=; rewrite -[X in measurable X]setTX.
  exact: measurableX.
- by move=> x/=; rewrite lee_fin !mulr_ge0 ?normal_pdf_ge0.
transitivity (\int[mu]_x \int[mu]_y
    ((fun y => (normal_pdf (m2 + y) s2 x * normal_pdf m1 s1 y)%:E) \_ (fun=> V x)) y).
  apply: eq_integral => x0 _ /=.
  under eq_integral do rewrite EFinM.
  by rewrite -epatch_indic.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => /= x0 _.
rewrite patchE; case: ifPn => xV.
  by apply: eq_integral => z _/=; rewrite patchE ifT.
apply: integral0_eq => /= z _.
rewrite patchE ifF//; apply/negbTE; rewrite notin_setE/=.
by move/negP : xV; rewrite inE.
Qed.

Lemma normal_probD2 (y m1 m2 s1 s2 : R) : s1 != 0%R -> s2 != 0%R ->
  \int[mu]_x (normal_pdf (m1 + x)%R s1 y * normal_pdf m2 s2 x)%:E =
  (normal_peak s1 * normal_peak s2)%:E *
  \int[mu]_z (normal_fun (m1 + z) s1 y * normal_fun m2 s2 z)%:E.
Proof.
move=> s10 s20; rewrite -ge0_integralZl//=.
- apply/measurable_EFinP => //=; apply: measurable_funM => //=.
  + rewrite /normal_fun. (* TODO: lemma? *)
    under eq_fun do rewrite -(sqrrN (y - _)) opprB (addrC m1) -addrA -opprB.
    exact: measurable_normal_fun.
  + exact: measurable_normal_fun.
- by move=> z _; rewrite lee_fin mulr_ge0// expR_ge0.
- by rewrite lee_fin mulr_ge0// ?normal_peak_ge0.
apply: eq_integral => /= z _.
by rewrite 2?normal_pdfE// /normal_pdf0 mulrACA.
Qed.

(* Variable elimination and integration [Shan, Section 3.5, (9)],
 also known as the reproductive property of normal distribution. *)
Lemma normal_probD (m1 s1 m2 s2 : R) V : s1 != 0%R -> s2 != 0%R ->
  measurable V ->
  \int[normal_prob m1 s1]_x normal_prob (m2 + x) s2 V =
  normal_prob (m1 + m2) (Num.sqrt (s1 ^+ 2 + s2 ^+ 2)) V.
Proof.
move=> s10 s20 mV.
rewrite normal_probD1//; apply: eq_integral => y _.
rewrite {V mV} normal_probD2//.
set S1 := (s1 ^+ 2)%R.
set S2 := (s2 ^+ 2)%R.
have s1s20 : (S1 + S2 != 0)%R.
  by rewrite lt0r_neq0// addr_gt0// exprn_even_gt0.
have sqs1s20 : Num.sqrt (S1 + S2) != 0%R.
  by rewrite lt0r_neq0// sqrtr_gt0 addr_gt0// exprn_even_gt0.
rewrite normal_pdfE//.
transitivity (((Num.sqrt S1 * Num.sqrt S2 * pi *+ 2)^-1)%:E *
  \int[mu]_x (expR
  (- (x - (y * S1 + m1 * S2 - m2 * S1) / (S1 + S2)%R) ^+ 2
   / ((Num.sqrt ((S1 * s2 ^+ 2) / (S1 + S2)%R) ^+ 2) *+ 2)
   - (y - (m1 + m2)) ^+ 2 / ((S1 + S2) *+ 2)))%:E).
  congr *%E.
    rewrite /normal_peak -/S1 -/S2.
    congr EFin.
    rewrite -2!(mulr_natr (_ * pi)).
    rewrite !(sqrtrM 2) ?(@mulr_ge0 _ _ pi) ?sqr_ge0 ?pi_ge0//.
    rewrite !(sqrtrM pi) ?sqr_ge0//.
    rewrite ![in LHS]invfM.
    rewrite mulrACA -(@sqrtrV _ 2)// -(expr2 (_ _^-1)%R).
    rewrite (@sqr_sqrtr _ 2^-1) ?invr_ge0//.
    rewrite mulrACA -(@sqrtrV _ pi) ?pi_ge0//.
    rewrite -(expr2 (_ _^-1)%R) (@sqr_sqrtr _ pi^-1) ?invr_ge0// ?pi_ge0//.
    rewrite -!invfM; congr GRing.inv.
    by rewrite -[in RHS]mulr_natr (mulrC _ (Num.sqrt _)).
  apply: eq_integral => x _.
  rewrite -expRD.
  congr (expR _)%:E.
  rewrite sqr_sqrtr.
    by rewrite mulr_ge0 ?invr_ge0// ?addr_ge0 ?(@mulr_ge0 _ (_ ^+ 2))// ?sqr_ge0.
  rewrite -/S1 -/S2.
  by field; apply/and3P; split => //; rewrite sqrf_eq0.
set DS12 := (S1 + S2)%R.
set MS12 := (S1 * S2)%R.
set C := (((y * S1 + m1 * S2) - m2 * S1) / DS12)%R.
under eq_integral do rewrite expRD EFinM.
rewrite ge0_integralZr//=.
  apply/measurable_EFinP.
  apply: measurableT_comp => //.
  apply: measurable_funM => //.
  apply: measurableT_comp => //.
  apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => t ^+ 2)%R) => //.
  exact: measurable_funD.
rewrite /normal_peak /normal_fun.
rewrite [in RHS]EFinM.
rewrite [in RHS]sqr_sqrtr//; first by rewrite addr_ge0// sqr_ge0.
rewrite muleA; congr *%E; last by rewrite -mulNr.
(* gauss integral *)
have MS12DS12_gt0 : (0 < MS12 / DS12)%R.
  rewrite divr_gt0//.
    by rewrite mulr_gt0// exprn_even_gt0.
  by rewrite addr_gt0// exprn_even_gt0.
transitivity (((Num.sqrt S1 * Num.sqrt S2 * pi *+ 2)^-1)%:E
   * \int[mu]_x ((normal_peak (Num.sqrt (MS12 / DS12)))^-1%:E
     * (normal_pdf C (Num.sqrt (MS12 / DS12)) x)%:E)).
  congr *%E.
  apply: eq_integral => x _.
  rewrite -EFinM; congr EFin.
  rewrite normal_pdfE; first by rewrite lt0r_neq0// sqrtr_gt0.
  rewrite mulrA mulVf// ?mul1r//.
  rewrite lt0r_neq0// invr_gt0 sqrtr_gt0 pmulrn_lgt0// mulr_gt0// ?pi_gt0//.
  by rewrite exprn_even_gt0//= lt0r_neq0// sqrtr_gt0.
rewrite ge0_integralZl//=.
- by apply/measurable_EFinP; exact: measurable_normal_pdf.
- by move=> x _; rewrite lee_fin; exact: normal_pdf_ge0.
- by rewrite lee_fin invr_ge0; exact: normal_peak_ge0.
rewrite integral_normal_pdf mule1 -EFinM; congr EFin.
rewrite -invfM; congr GRing.inv.
rewrite -sqrtrM ?sqr_ge0// /normal_peak sqr_sqrtr; first by rewrite ltW.
rewrite -3!mulrnAr.
rewrite (sqrtrM (pi *+ 2)); first by rewrite ltW.
rewrite invfM mulrCA.
rewrite -{1}(@sqr_sqrtr _ (pi *+ 2)); first by rewrite pmulrn_lge0 ?pi_ge0.
rewrite -2!(mulrA (Num.sqrt _)) divff// ?mulr1.
  by rewrite sqrtr_eq0 -ltNge pmulrn_lgt0 ?pi_gt0.
rewrite (sqrtrM (DS12^-1)); first by rewrite mulr_ge0 ?sqr_ge0.
rewrite sqrtrV; first by rewrite addr_ge0 ?sqr_ge0.
rewrite invfM invrK.
rewrite mulrAC mulrA mulVf ?mul1r.
  by rewrite lt0r_neq0// sqrtr_gt0 mulr_gt0 ?exprn_even_gt0.
by rewrite sqrtrM ?addr_ge0 ?sqr_ge0// mulrC.
Qed.

End normal_probD.
