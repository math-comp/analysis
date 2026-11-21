(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import poly ssrnum ssrint interval archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals interval_inference ereal topology normedtype.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import ftc probability.

(**md**************************************************************************)
(* # gamma function                                                           *)
(*                                                                            *)
(* This file contains a formalization of the Gamma function.                  *)
(* Gamma  == the Gamma function                                               *)
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


Section Gamma.
Context {R : realType}.

Notation mu := (@lebesgue_measure R).

Import MeasurableR.

Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (x`^  (a - 1) * expR (- x))%:E)%E.

Lemma Gamma1 : Gamma 1 = 1%E.
Proof.
transitivity (@exponential_prob R 1 `[0, +oo[).
  apply: eq_integral => x; rewrite inE/= in_itv/= => /andP[x0 _].
  by rewrite subrr powRr0 exponential_pdfE// mulN1r.
transitivity (@exponential_prob R 1 setT).
  rewrite -[LHS]addr0 -(setUv `[0, +oo[) measureU//.
  - exact: measurableC.
  - exact: setICr.
  congr +%E; apply/esym.
  rewrite /=/exponential_prob integral0_eq// => x/=; rewrite in_itv/= andbT.
  by move/negP; rewrite -ltNge => x0; rewrite lt0_exponential_pdf.
exact: probability_setT.
Qed.

Let f0 a : 1 <= a ->
let f := (fun x => (x `^ a * - expR (- x))) : R^o -> R^o in
 f x @[x --> +oo%R] --> @GRing.zero R.
Proof.
move=> a1.
apply/cvgrPdistC_lep; near=> e; near=> x.
rewrite subr0 mulrN normrN expRN.
have /normr_idP -> : 0 <= (x `^ a / expR x).
  by rewrite mulr_ge0 1?expR_ge0 1?powR_ge0.
set A := `|archimedean.Num.Def.ceil a|.+1%N.
have H1DxAgt0 : 0 < (1%R + x `^ A%:R / A`!%:R).
  by rewrite addr_gt0 ?powR_gt0 ?divr_gt0 ?powR_gt0.
apply: (@le_trans _ _ (x `^ a / (1 + x `^ A%:R / A`!%:R))).
  rewrite ler_pM2l ?powR_gt0//.
  rewrite ler_pV2; last by rewrite powR_mulrn// expR_ge1Dxn.
  - rewrite inE/=; apply/andP; split; last by rewrite expR_gt0.
    by rewrite unitfE gt_eqF ?expR_gt0.
  - rewrite inE/=; apply/andP; split => //; rewrite unitfE gt_eqF//.
apply: (@le_trans _ _ (x `^ a / (x `^ A%:R / A`!%:R))).
  rewrite ler_pM2l ?powR_gt0// ler_pV2.
  - rewrite inE/=; apply/andP; split => //.
    by rewrite unitfE gt_eqF ?expR_gt0//.
  - have HxAgt0 : 0 < x `^ A%:R / A`!%:R.
      by rewrite mulr_gt0 ?powR_gt0 ?invr_gt0.
    rewrite inE/=; apply/andP; split => //.
    by rewrite unitfE gt_eqF//.
  by rewrite lerDr.
rewrite invfM mulrA.
rewrite ler_pdivrMr; first by rewrite invr_gt0 -(mulr0n 1) ltr_nat fact_gt0.
rewrite -powRB ?(@gt_eqF _ _ x) ?implybT//-[X in _`^ X]opprK powRN.
rewrite invf_ple ?posrE ?powR_gt0// ?divr_gt0// (@le_trans _ _ x)//.
apply: le1r_powR; first by near: x; exact: nbhs_pinfty_ge.
rewrite lerNr lerBlDl /A -natr1 addrK natr_absz intr_norm -RceilE.
apply: (le_trans (Rceil_ge a)); exact: ler_norm.
Unshelve. all: end_near. Qed.

Lemma Gamma_add1 a : 1 <= a -> (Gamma (a + 1) = a%:E * Gamma a)%E.
Proof.
move=> a1; have a0 : 0 < a by apply: lt_le_trans a1.
have dxa1 : {in `]0, +oo[%R,
  (fun x : R => x `^ a : R^o) ^`()%classic =1 (fun x => a * x `^ (a - 1))}.
  exact: powR_derive1.
have dex : {in `]0, +oo[%R,
  (fun x => - expR (- x) : R^o) ^`()%classic =1 (fun x => expR (- x))}.
  by move=> x _; rewrite derive1E derive_val mulrN mulr1 opprK.
rewrite/Gamma addrK.
have powRMexpR_ge0 b : {in `]0, +oo[,
     forall x, (0 <= (x `^ b * expR (- x))%:E)%E}.
  move=> x; rewrite in_itv/= andbT => x0.
  by rewrite lee_fin mulr_ge0// ltW// ?powR_gt0// expR_gt0.
rewrite (integration_by_partsy_le0_ge0 _ _ dex _ _ dxa1 (f0 a1)); last 5 first.
- move: a1.
  rewrite le_eqVlt => /predU1P[<- |a1].
    apply: continuous_subspaceT => x.
    under [X in continuous_at _ X]eq_fun do rewrite mul1r subrr powRr0.
    exact: cvg_cst.
  apply/continuous_within_itvcyP; split.
    move=> x; rewrite in_itv/= andbT => x0.
    rewrite /continuous_at/=/powR gt_eqF//=; first by rewrite subr_gt0.
    apply: (@cvg_trans _ ((a * expR ((a - 1) * ln x1)) @[x1 --> x])).
      apply: near_eq_cvg; near=> z; rewrite gt_eqF//; near: z.
      exact: lt_nbhsr.
    apply: (@cvgM _ _ (nbhs x)); first exact: cvg_cst.
    apply: (@cvg_comp _ _ _ _ expR _ (nbhs ((a - 1) * ln x))).
      apply: cvgM; first exact: cvg_cst.
      exact: continuous_ln.
    rewrite ifF; first by rewrite gt_eqF.
    exact: continuous_expR.
  apply: cvgM; first exact: cvg_cst.
  rewrite powR0; first by rewrite gt_eqF// subr_gt0.
  by apply: (@powR_cvg0 _ (a - 1)); rewrite subr_gt0.
- split.
  + exact: derivable_powR.
  + rewrite powR0; first by apply: lt0r_neq0.
    apply: (@cvg_trans _ ((expR (a * ln x))@[x --> 0^'+])).
      apply: near_eq_cvg.
      near=> x.
      rewrite /powR ifF//.
      exact/negP/negP/lt0r_neq0.
    have : a * ln x @[x --> 0^'+] --> -oo.
      apply: gt0_cvgMrNy => //; exact: lnNy.
    move/cvg_comp; apply.
    exact/cvgNy_compNP/cvgr_expR.
- move=> ?; rewrite inE/= mulrN EFinN oppe_le0 => ?.
  rewrite -mulrA EFinM mule_ge0//; last exact: powRMexpR_ge0.
  by rewrite lee_fin (le_trans _ a1).
- move=> ?; rewrite inE/= => ?; exact: powRMexpR_ge0.
rewrite sub0r.
rewrite powR0 ?gt_eqF// mul0r EFinN oppe0 sub0e.
under eq_integral do rewrite mulrN EFinN -mulrA EFinM -mulNe.
rewrite ge0_integralZl//=.
- move=> x; rewrite in_itv/= andbT => x0.
  by rewrite lee_fin mulr_ge0// ?powR_ge0 ?expR_ge0.
- apply/measurable_EFinP/measurable_funTS.
  apply: measurable_funM; first exact: measurable_powR.
  exact: measurableT_comp.
by rewrite EFinN mulNe oppeK.
- apply: continuous_subspaceT.
  move=> /= ?; exact/(cvg_compNP expR)/continuous_expR.
- split.
    move=> x _.
    apply: derivableN.
    apply: diff_derivable.
    apply: (@differentiable_comp _ _ R^o) => //.
    apply/derivable1_diffP.
    exact: derivable_expR.
  apply: cvgN; apply: cvg_at_right_filter.
  exact/(cvg_compNP expR)/continuous_expR.
Unshelve. all: end_near. Qed.

End Gamma.

Lemma Gamma_nat {R : realType} (n : nat) : @Gamma R n.+1%:R = n`!%:R%:E.
Proof.
elim: n; first exact: Gamma1.
move=> n IH; rewrite -natr1 Gamma_add1; first by rewrite ler1n.
by rewrite IH factS natrM EFinM.
Qed.
