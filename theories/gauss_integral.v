(* mathcomp analysis (c) 2024 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop signed reals ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure numfun realfun.
From mathcomp Require Import exp trigo lebesgue_integral derive charge ftc.

(**md**************************************************************************)
(* # Gauss integral                                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* NB: move to ftc.v? *)
Section oneDsqr.
Context {R : realType}.
Implicit Type x : R.

Definition oneDsqr x : R := 1 + x ^+ 2.

Lemma oneDsqr_gt0 x : 0 < oneDsqr x :> R.
Proof. by rewrite ltr_pwDl// sqr_ge0. Qed.

Lemma oneDsqr_ge0 x : 0 <= oneDsqr x :> R.
Proof. by rewrite ltW// oneDsqr_gt0. Qed.

Lemma oneDsqr_ge1 x : 1 <= oneDsqr x :> R.
Proof. by rewrite lerDl sqr_ge0. Qed.

Lemma oneDsqr_neq0 x : oneDsqr x != 0.
Proof. by rewrite gt_eqF// oneDsqr_gt0. Qed.

Lemma oneDsqrV_le1 x : oneDsqr\^-1 x <= 1.
Proof. by rewrite invr_le1// ?oneDsqr_ge1 ?unitf_gt0 ?oneDsqr_gt0. Qed.

Lemma continuous_oneDsqr : continuous oneDsqr.
Proof. by move=> x; apply: cvgD; [exact: cvg_cst|exact: exprn_continuous]. Qed.

Lemma continuous_oneDsqrV : continuous (oneDsqr\^-1).
Proof.
by move=> x; apply: cvgV; [exact: oneDsqr_neq0|exact: continuous_oneDsqr].
Qed.

Lemma integral01_atan :
  \int[@lebesgue_measure R]_(x in `[0, 1]) (oneDsqr x)^-1 = atan 1.
Proof.
rewrite /Rintegral (@continuous_FTC2 _ _ atan)//.
- by rewrite atan0 sube0.
- by apply: continuous_in_subspaceT => x ?; exact: continuous_oneDsqrV.
- split.
  + by move=> x _; exact: derivable_atan.
  + by apply: cvg_at_right_filter; exact: continuous_atan.
  + by apply: cvg_at_left_filter; exact: continuous_atan.
- move=> x x01.
  by rewrite derive1_atan// mul1r.
Qed.

End oneDsqr.

#[global] Hint Extern 0 (0 < oneDsqr _)%R => solve[apply: oneDsqr_gt0] : core.
#[global] Hint Extern 0 (0 <= oneDsqr _)%R => solve[apply: oneDsqr_ge0] : core.
#[global] Hint Extern 0 (1 <= oneDsqr _)%R => solve[apply: oneDsqr_ge1] : core.
#[global] Hint Extern 0 (oneDsqr _ != 0)%R => solve[apply: oneDsqr_ge1] : core.

Section gauss.
Context {R : realType}.
Local Open Scope ring_scope.

Definition gauss (x : R) := expR (- x ^+ 2).

Lemma gauss_ge0 (x : R) : 0 <= gauss x. Proof. exact: expR_ge0. Qed.

Lemma gauss_le1 (x : R) : gauss x <= 1.
Proof. by rewrite -expR0 ler_expR lerNl oppr0 sqr_ge0. Qed.

Lemma cvg_gauss : gauss x @[x --> +oo%R] --> (0:R).
Proof.
apply: (@cvg_comp _ _ _ (fun x => x ^+ 2) (fun x => expR (- x))); last first.
  exact: cvgr_expR.
(* NB: should this become a lemma? *)
apply/cvgryPge => M.
near=> x.
rewrite (@le_trans _ _ x)//.
  near: x.
  by apply: nbhs_pinfty_ge => //; rewrite num_real.
by rewrite expr2 ler_peMl.
Unshelve. all: end_near. Qed.

Lemma measurable_gauss : measurable_fun setT gauss.
Proof. by apply: measurableT_comp => //; exact: measurableT_comp. Qed.

Lemma continuous_gauss : continuous gauss.
Proof.
move=> x; apply: (@continuous_comp _ _ _ (fun x : R => - x ^+ 2) expR).
  apply: cvgN; apply: (@cvg_comp _ _ _ (fun z => z) (fun z => z ^+ 2)).
    exact: cvg_id.
  exact: exprn_continuous.
exact: continuous_expR.
Qed.

End gauss.

Module gauss_integral_proof.
Section gauss_integral_proof.
Context {R : realType}.
Local Open Scope ring_scope.
Implicit Type x : R.

Let mu : {measure set _ -> \bar R} := @lebesgue_measure R.

Definition integral0y_gauss := \int[mu]_(x in `[0%R, +oo[) gauss x.

Let integral0y_gauss_ge0 : 0 <= integral0y_gauss.
Proof. by apply: Rintegral_ge0 => //= x _; rewrite gauss_ge0. Qed.

Definition integral0_gauss x := \int[mu]_(t in `[0, x]) gauss t.

Lemma integral0_gauss_ge0 x : 0 <= integral0_gauss x.
Proof. by apply: Rintegral_ge0 => //= r _; rewrite expR_ge0. Qed.

Let continuous_integral0_gauss x : (0 < x)%R ->
  {within `[0, x], continuous integral0_gauss}.
Proof.
move=> x0; rewrite /integral0_gauss.
apply: parameterized_integral_continuous => //=.
apply: continuous_compact_integrable => //; first exact: segment_compact.
by apply: continuous_subspaceT; exact: continuous_gauss.
Qed.

Definition u x t := expR (- x ^+ 2 * oneDsqr t) / oneDsqr t.

Let u_ge0 x t : 0 <= u x t.
Proof. by rewrite /u divr_ge0// ?expR_ge0// oneDsqr_ge0. Qed.

Let measurable_u x : measurable_fun setT (u x).
Proof.
apply: measurable_funM => //=.
  apply: measurableT_comp => //=; apply: measurable_funM => //=.
  exact: measurable_funD.
apply: measurable_funTS.
by apply: continuous_measurable_fun; exact: continuous_oneDsqrV.
Qed.

Let partial1_u x t : ('d1 u t) x = - 2 * x * gauss x * gauss (t * x).
Proof.
rewrite /partial1 /u /= derive1E deriveMr//= -derive1E.
rewrite derive1_comp// [in X in _ * (_ * X)]derive1E deriveMr//=.
rewrite mulrCA (mulrA (oneDsqr _)^-1) mulVf ?oneDsqr_neq0 ?mul1r//.
rewrite deriveN// exp_derive expr1 mulrC !mulNr; congr -%R.
rewrite -mulrA scaler1; congr *%R.
rewrite -expRD /oneDsqr mulrDr mulr1 exprMn opprD mulrC.
by rewrite derive1E -[in RHS]derive_expR.
Qed.

Let continuous_NsqrM x : continuous (fun r : R => - (r * x) ^+ 2).
Proof.
move=> z; apply: cvgN => /=.
apply: (@cvg_comp _ _ _ (fun z => z * x) (fun z => z ^+ 2)).
  by apply: cvgMl; exact: cvg_id.
exact: exprn_continuous.
Qed.

Let continuous_gaussM x : continuous (fun r : R => gauss (r * x)).
Proof.
move=> x0.
apply: (@continuous_comp _ _ _ (fun r : R => - (r * x) ^+ 2) expR).
  exact: continuous_NsqrM.
exact: continuous_expR.
Qed.

Let continuous_u x : continuous (u x).
Proof.
rewrite /u /= => y; rewrite /continuous_at.
apply: cvgM; last exact: continuous_oneDsqrV.
apply: continuous_comp => /=; last exact: continuous_expR.
by apply: cvgMr; exact: continuous_oneDsqr.
Qed.

Definition integral01_u x := \int[mu]_(t in `[0, 1]) u x t.

Let integral01_u_ge0 x : 0 <= integral01_u x.
Proof.
rewrite /Rintegral fine_ge0// integral_ge0//= => t t01.
by rewrite lee_fin u_ge0.
Qed.

Let partial1_u_local_ub c (e : R) : 0 < e ->
  exists2 M : R, 0 < M &
    forall x0 y, x0 \in `](c - e), (c + e)[ -> `|('d1 u) y x0| <= M.
Proof.
move=> e0 /=.
near (pinfty_nbhs R) => M.
exists M => // x y.
rewrite in_itv/= => /andP[cex xce].
rewrite partial1_u !mulNr normrN -!mulrA normrM ger0_norm//.
rewrite -expRD exprMn_comm; last by rewrite /GRing.comm mulrC.
rewrite -opprD.
rewrite -{1}(mul1r (x ^+ 2)) -mulrDl.
rewrite (@le_trans _ _ (2 * `|x * gauss x|))//.
  rewrite ler_pM2l// normrM [leRHS]normrM.
  rewrite ler_wpM2l//.
  do 2 rewrite ger0_norm ?expR_ge0//.
  by rewrite ler_expR// lerN2 ler_peMl ?sqr_ge0// lerDl sqr_ge0.
rewrite normrM (ger0_norm (expR_ge0 _)).
have ? : `|x| <= maxr `|c + e| `|c - e|.
  rewrite le_max.
  have [x0|x0] := lerP 0 x.
    by rewrite ger0_norm// ler_normr (ltW xce).
  rewrite ltr0_norm//; apply/orP; right.
  move/ltW : cex.
  rewrite -lerN2 => /le_trans; apply.
  by rewrite -normrN ler_norm.
rewrite (@le_trans _ _ (2 * ((maxr `|c + e| `|c - e|) * expR (- 0 ^+ 2))))//.
  rewrite ler_pM2l// ler_pM ?expR_ge0//.
  by rewrite expr0n/= oppr0 expR0 gauss_le1.
near: M.
by apply: nbhs_pinfty_ge; rewrite num_real.
Unshelve. all: end_near. Qed.

Let cvg_dintegral01_u x :
  h^-1 *: (integral01_u (h + x)%E - integral01_u x) @[h --> 0^'] -->
  - 2 * x * gauss x * \int[mu]_(t in `[0, 1]) gauss (t * x).
Proof.
have [c [e e0 cex]] : exists c : R, exists2 e : R, 0 < e & ball c e x.
  exists x, 1 => //.
  exact: ballxx.
have [M M0 HM] := partial1_u_local_ub c e0.
rewrite [X in _ --> X](_ : _ =
    \int[mu]_(y in `[0, 1]) ('d1 u) y x)//; last first.
  rewrite /= -RintegralZl//; last first.
    apply: continuous_compact_integrable => /=; first exact: segment_compact.
    by apply/continuous_subspaceT => x0; exact: continuous_gaussM.
  by apply: eq_Rintegral => z z01; rewrite partial1_u.
have /= := @cvg_differentiation_under_integral
  R _ _ mu u `[0, 1] _ x _ _ _ _ _ _ _ _ (fun x y H _ => HM x y H).
apply => //=.
- by rewrite ball_itv/= in cex.
- move=> z z01; apply: continuous_compact_integrable => //.
    exact: segment_compact.
  by apply: continuous_subspaceT; exact: continuous_u.
- by move=> _; exact: ltW.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: cst_continuous.
Unshelve. all: end_near. Qed.

Let derivable_integral01_u x : derivable integral01_u x 1.
Proof.
apply/cvg_ex; eexists.
rewrite /integral01_u/=.
under eq_fun do rewrite scaler1.
exact: cvg_dintegral01_u.
Qed.

Let derive_integral01_u x : integral01_u^`() x =
  - 2 * x * gauss x * \int[mu]_(t in `[0, 1]) gauss (t * x).
Proof. by apply/cvg_lim => //=; exact: cvg_dintegral01_u. Qed.

Let derive_integral0_gauss x : 0 < x ->
  derivable integral0_gauss x 1 /\ integral0_gauss^`() x = gauss x.
Proof.
move=> x0.
apply: (@continuous_FTC1 R gauss (BLeft 0) _ (x + 1) _ _ _ _).
- by rewrite ltrDl.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: continuous_gauss.
- by rewrite /=; rewrite lte_fin.
- by move=> ?; exact: continuous_gauss.
Qed.

Definition h x := integral01_u x + (integral0_gauss x) ^+ 2.

Let derive_h x : 0 < x -> h^`() x = 0.
Proof.
move=> x0.
rewrite /h derive1E deriveD//=; last first.
  apply/diff_derivable.
  apply: (@differentiable_comp _ _ _ _ integral0_gauss (fun x => x ^+ 2)).
    apply/derivable1_diffP.
    by have [] := derive_integral0_gauss x0.
  by apply/derivable1_diffP; exact: exprn_derivable.
rewrite -derive1E derive_integral01_u -derive1E.
rewrite (@derive1_comp _ integral0_gauss (fun z => z ^+ 2))//; last first.
  by have [] := derive_integral0_gauss x0.
rewrite derive1E exp_derive.
rewrite (derive_integral0_gauss _).2//.
rewrite expr1 scaler1.
rewrite addrC !mulNr; apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite -!mulrA; congr *%R.
rewrite [LHS]mulrC.
rewrite [RHS]mulrCA; congr *%R.
rewrite /integral0_gauss [in LHS]/Rintegral.
have derM : ( *%R^~ x)^`() = cst x.
  apply/funext => z.
  by rewrite derive1E deriveMr// derive_id mulr1.
have := @integration_by_substitution_increasing R (fun t => t * x) gauss 0 1 ltr01.
rewrite -/mu mul0r mul1r => ->//=; last 6 first.
  - move=> a b; rewrite !in_itv/= => /andP[a0 a1] /andP[b0 b1] ab.
    by rewrite ltr_pM2r.
  - by rewrite derM => z _; exact: cvg_cst.
  - by rewrite derM; exact: is_cvg_cst.
  - by rewrite derM; exact: is_cvg_cst.
  - split => //.
    + apply: cvg_at_right_filter.
      by apply: cvgM => //; exact: cvg_cst.
    + apply: cvg_at_left_filter.
      by apply: cvgM => //; exact: cvg_cst.
  - by apply: continuous_subspaceT; exact: continuous_gauss.
rewrite derM.
under eq_integral do rewrite fctE/= EFinM.
have ? : mu.-integrable `[0, 1] (fun y => (gauss (y * x))%:E).
  apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT => z; exact: continuous_gaussM.
rewrite integralZr//= fineM//=; last exact: integral_fune_fin_num.
by rewrite mulrC.
Qed.

Let h0 : h 0 = pi / 4.
Proof.
rewrite /h /integral0_gauss set_itv1 Rintegral_set1 expr0n addr0.
rewrite -atan1 /integral01_u.
under eq_Rintegral do rewrite /u expr0n/= oppr0 mul0r expR0 mul1r.
exact: integral01_atan.
Qed.

Let u_gauss t x : u x t <= gauss x.
Proof.
rewrite ler_pdivrMr ?oneDsqr_gt0 //.
rewrite (@le_trans _ _ (gauss x))//.
  by rewrite ler_expR// mulNr lerN2 ler_peMr// ?sqr_ge0 ?oneDsqr_ge1.
by rewrite ler_peMr// ?expR_ge0 ?oneDsqr_ge1.
Qed.

Let integral01_u_gauss x : integral01_u x <= gauss x.
Proof.
have -> : gauss x = \int[mu]_(t in `[0, 1]) gauss x.
  rewrite /Rintegral integral_cst//. (* TODO: lemma Rintegral_cst *)
  by rewrite /mu/= lebesgue_measure_itv//= lte01 oppr0 adde0 mule1.
rewrite fine_le//.
- apply: integral_fune_fin_num => //=.
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_in_subspaceT => z _; exact: continuous_u.
- apply: integral_fune_fin_num => //=.
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_subspaceT => z; exact: cvg_cst.
apply: ge0_le_integral => //=.
- by move=> y _; rewrite lee_fin u_ge0.
- by apply/measurable_EFinP => /=; apply/measurable_funTS; exact: measurable_u.
- by move=> y _; rewrite lee_fin expR_ge0.
- by move=> y _; rewrite lee_fin u_gauss.
Qed.

Let cvg_integral01_u : integral01_u x @[x --> +oo] --> 0.
Proof.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) gauss).
- by near=> n => /=; rewrite integral01_u_gauss integral01_u_ge0.
- exact: cvg_cst.
- exact: cvg_gauss.
Unshelve. all: end_near. Qed.

Lemma cvg_integral0_gauss_sqr : (integral0_gauss x) ^+ 2 @[x --> +oo] --> pi / 4.
Proof.
have h_h0 x : 0 < x -> h x = h 0.
  move=> x0.
  have [] := @MVT _ h h^`() 0 x x0.
  - move=> r; rewrite in_itv/= => /andP[r0 rx].
    apply: DeriveDef.
      apply: derivableD => /=.
        exact: derivable_integral01_u.
      under eq_fun do rewrite expr2//=.
      by apply: derivableM; have [] := derive_integral0_gauss r0.
    by rewrite derive1E.
  - rewrite /h => z.
    apply: continuousD; last first.
      rewrite /prop_for /continuous_at expr2.
      under [X in X @ _ --> _]eq_fun do rewrite expr2.
      by apply: cvgM; exact: continuous_integral0_gauss.
    by apply: derivable_within_continuous => u _; exact: derivable_integral01_u.
  move=> c; rewrite in_itv/= => /andP[c0 cx].
  by rewrite derive_h// mul0r => /eqP; rewrite subr_eq0 => /eqP.
have Ig2 x : 0 < x -> (integral0_gauss x) ^+ 2 = pi / 4 - integral01_u x.
  move/h_h0/eqP; rewrite {1}/h eq_sym addrC -subr_eq => /eqP/esym.
  by rewrite h0.
suff: pi / 4 - integral01_u x @[x --> +oo] --> pi / 4.
  apply: cvg_trans; apply: near_eq_cvg.
  by near=> x; rewrite Ig2.
rewrite -[in X in _ --> X](subr0 (pi / 4)).
by apply: cvgB => //; exact: cvg_cst.
Unshelve. end_near. Qed.

End gauss_integral_proof.
End gauss_integral_proof.

Section gauss_integral.
Context {R : realType}.
Import gauss_integral_proof.
Let mu := @lebesgue_measure R.

Lemma integral0y_gauss_pi2 :
  \int[mu]_(x in `[0%R, +oo[) gauss x = Num.sqrt pi / 2.
Proof.
have cvg_Ig : @integral0_gauss R x @[x --> +oo] --> Num.sqrt pi / 2.
  have : Num.sqrt (@integral0_gauss R x ^+ 2) @[x --> +oo]
      --> Num.sqrt (pi / 4).
    apply: continuous_cvg => //;
      [exact: sqrt_continuous|exact: cvg_integral0_gauss_sqr].
  rewrite sqrtrM ?pi_ge0// sqrtrV// (_ : 4 = 2 ^+ 2); last first.
    by rewrite expr2 -natrM.
  rewrite sqrtr_sqr ger0_norm//.
  rewrite (_ : (fun _ => Num.sqrt _) = integral0_gauss)//.
  apply/funext => r; rewrite sqrtr_sqr// ger0_norm//.
  exact: integral0_gauss_ge0.
have /cvg_lim := @ge0_cvg_integral R mu gauss gauss_ge0 measurable_gauss.
rewrite /integral0y_gauss /Rintegral => <-//.
suff: limn (fun n => (\int[mu]_(x in `[0%R, n%:R]) (gauss x)%:E)%E) =
    (Num.sqrt pi / 2)%:E.
  by move=> ->.
apply/cvg_lim => //.
have H : (n%:R : R) @[n --> \oo] --> +oo.
  (* NB: should this be a lemma? *)
  by apply/cvgryPge => M; exact: nbhs_infty_ger.
move/cvg_pinftyP : cvg_Ig => /(_ _ H).
move/neq0_fine_cvgP; apply.
by rewrite gt_eqF// divr_gt0// sqrtr_gt0 pi_gt0.
Qed.

End gauss_integral.
