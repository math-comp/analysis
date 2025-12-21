(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals interval_inference ereal.
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
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gauss_fun.
Context {R : realType}.
Local Open Scope ring_scope.

Definition gauss_fun (x : R) := expR (- x ^+ 2).

Lemma gauss_fun_ge0 (x : R) : 0 <= gauss_fun x. Proof. exact: expR_ge0. Qed.

Lemma gauss_fun_le1 (x : R) : gauss_fun x <= 1.
Proof. by rewrite -expR0 ler_expR lerNl oppr0 sqr_ge0. Qed.

Lemma cvg_gauss_fun : gauss_fun x @[x --> +oo%R] --> (0:R).
Proof.
by apply: (cvg_comp (fun x => x ^+ 2) (fun x => expR (- x)));
  [exact: cvgr_expr2|exact: cvgr_expR].
Qed.

Lemma measurable_gauss_fun : measurable_fun setT gauss_fun.
Proof. by apply: measurableT_comp => //; exact: measurableT_comp. Qed.

Lemma continuous_gauss_fun : continuous gauss_fun.
Proof.
move=> x; apply: (@continuous_comp _ _ _ (fun x : R => - x ^+ 2) expR).
  apply: cvgN; apply: (cvg_comp (fun z => z) (fun z => z ^+ 2)).
    exact: cvg_id.
  exact: exprn_continuous.
exact: continuous_expR.
Qed.

End gauss_fun.

Module gauss_integral_proof.
Section gauss_integral_proof.
Context {R : realType}.
Local Open Scope ring_scope.
Implicit Type x : R.

Let mu : {measure set _ -> \bar R} := @lebesgue_measure R.

Definition integral0y_gauss := \int[mu]_(x in `[0%R, +oo[) gauss_fun x.

Let integral0y_gauss_ge0 : 0 <= integral0y_gauss.
Proof. by apply: Rintegral_ge0 => //= x _; rewrite gauss_fun_ge0. Qed.

Definition integral0_gauss x := \int[mu]_(t in `[0, x]) gauss_fun t.

Lemma integral0_gauss_ge0 x : 0 <= integral0_gauss x.
Proof. by apply: Rintegral_ge0 => //= r _; rewrite expR_ge0. Qed.

Let continuous_integral0_gauss x : (0 <= x)%R ->
  {within `[0, x], continuous integral0_gauss}.
Proof.
move=> x0; rewrite /integral0_gauss.
apply: parameterized_integral_continuous => //=.
apply: continuous_compact_integrable => //; first exact: segment_compact.
by apply: continuous_subspaceT; exact: continuous_gauss_fun.
Qed.

Definition u x t := expR (- x ^+ 2 * oneDsqr t) / oneDsqr t.

Let u_ge0 x t : 0 <= u x t.
Proof. by rewrite /u divr_ge0// ?expR_ge0. Qed.

Let measurable_u x : measurable_fun setT (u x).
Proof.
apply: measurable_funM => //=.
  apply: measurableT_comp => //=; apply: measurable_funM => //=.
  exact: measurable_funD.
apply: measurable_funTS.
by apply: continuous_measurable_fun; exact: continuous_oneDsqrV.
Qed.

Local Notation "'d1 f" := (partial1of2 f).

Let partial1_u x t : ('d1 u) x t = - 2 * x * gauss_fun x * gauss_fun (t * x).
Proof.
rewrite partial1of2E /u /= deriveMr//= -derive1E.
rewrite derive1_comp// [in X in _ * (_ * X)]derive1Mr//.
rewrite mulrC -!mulrA divff// mulr1 derive1N// exp_derive1 expr1.
rewrite mulrC !mulNr; congr -%R.
rewrite -mulrA; congr (_ * (_ * _))%R.
rewrite -expRD /oneDsqr mulrDr mulr1 exprMn opprD mulrC.
by rewrite derive1E -[in RHS]derive_expR.
Qed.

Let continuous_NsqrM x : continuous (fun r : R => - (r * x) ^+ 2).
Proof.
move=> z; apply: cvgN => /=.
apply: (cvg_comp (fun z => z * x) (fun z => z ^+ 2)).
  by apply: cvgMr_tmp; exact: cvg_id.
exact: exprn_continuous.
Qed.

Let continuous_gaussM x : continuous (fun r : R => gauss_fun (r * x)).
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
by apply: cvgMl_tmp; exact: continuous_oneDsqr.
Qed.

Definition integral01_u x := \int[mu]_(t in `[0, 1]) u x t.

Let integral01_u_ge0 x : 0 <= integral01_u x.
Proof.
rewrite /Rintegral fine_ge0// integral_ge0//= => t t01.
by rewrite lee_fin u_ge0.
Qed.

Let partial1_u_local_ub c (e : R) : 0 < e ->
  exists2 M : R, 0 < M &
    forall x0 y, x0 \in `](c - e), (c + e)[ -> `|('d1 u) x0 y| <= M.
Proof.
move=> e0 /=.
near (pinfty_nbhs R) => M.
exists M => // x y.
rewrite in_itv/= => /andP[cex xce].
rewrite partial1_u !mulNr normrN -!mulrA normrM ger0_norm//.
rewrite -expRD exprMn_comm; last by rewrite /GRing.comm mulrC.
rewrite -opprD.
rewrite -{1}(mul1r (x ^+ 2)) -mulrDl.
rewrite (@le_trans _ _ (2 * `|x * gauss_fun x|))//.
  rewrite ler_pM2l// normrM [leRHS]normrM.
  rewrite ler_wpM2l//.
  do 2 rewrite ger0_norm ?expR_ge0//.
  by rewrite ler_expR// lerN2 ler_peMl ?sqr_ge0// lerDl sqr_ge0.
rewrite normrM (ger0_norm (expR_ge0 _)).
have ? : `|x| <= Num.max `|c + e| `|c - e|.
  rewrite le_max.
  have [x0|x0] := lerP 0 x.
    by rewrite ger0_norm// ler_normr (ltW xce).
  rewrite ltr0_norm//; apply/orP; right.
  move/ltW : cex.
  rewrite -lerN2 => /le_trans; apply.
  by rewrite -normrN ler_norm.
rewrite (@le_trans _ _ (2 * ((Num.max `|c + e| `|c - e|) * expR (- 0 ^+ 2))))//.
rewrite ler_pM2l// ler_pM ?expR_ge0//.
by rewrite expr0n/= oppr0 expR0 gauss_fun_le1.
Unshelve. all: end_near. Qed.

Let cvg_dintegral01_u x :
  h^-1 *: (integral01_u (h + x)%E - integral01_u x) @[h --> 0^'] -->
  - 2 * x * gauss_fun x * \int[mu]_(t in `[0, 1]) gauss_fun (t * x).
Proof.
have [c [e e0 cex]] : exists c : R, exists2 e : R, 0 < e & ball c e x.
  exists x, 1 => //.
  exact: ballxx.
have [M M0 HM] := partial1_u_local_ub c e0.
rewrite [X in _ --> X](_ : _ =
    \int[mu]_(y in `[0, 1]) ('d1 u) x y)//; last first.
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
  - 2 * x * gauss_fun x * \int[mu]_(t in `[0, 1]) gauss_fun (t * x).
Proof. by apply/cvg_lim => //=; exact: cvg_dintegral01_u. Qed.

Let derive_integral0_gauss x : 0 < x ->
  derivable integral0_gauss x 1 /\ integral0_gauss^`() x = gauss_fun x.
Proof.
move=> x0.
apply: (@continuous_FTC1 R gauss_fun (BLeft 0) _ (x + 1) _ _ _ _).
- by rewrite ltrDl.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: continuous_gauss_fun.
- by rewrite /=; rewrite lte_fin.
- by move=> ?; exact: continuous_gauss_fun.
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
  by apply/funext => z; rewrite derive1Mr// derive1_id mul1r.
have := @integration_by_substitution_increasing R (fun t => t * x)
  gauss_fun _ _ ler01.
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
  - by apply: continuous_subspaceT; exact: continuous_gauss_fun.
rewrite derM.
under eq_integral do rewrite fctE/= EFinM.
have ? : mu.-integrable `[0, 1] (fun y => (gauss_fun (y * x))%:E).
  apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT => z; exact: continuous_gaussM.
rewrite integralZr//= fineM//=; last exact: integrable_fin_num.
by rewrite mulrC.
Qed.

Let h0 : h 0 = pi / 4.
Proof.
rewrite /h /integral0_gauss set_itv1 Rintegral_set1 expr0n addr0.
rewrite -atan1 /integral01_u.
under eq_Rintegral do rewrite /u expr0n/= oppr0 mul0r expR0 mul1r.
exact: integral0_oneDsqr.
Qed.

Let u_gauss_fun t x : u x t <= gauss_fun x.
Proof.
rewrite ler_pdivrMr ?oneDsqr_gt0 //.
rewrite (@le_trans _ _ (gauss_fun x))//.
  by rewrite ler_expR// mulNr lerN2 ler_peMr// ?sqr_ge0.
by rewrite ler_peMr// ?expR_ge0.
Qed.

Let integral01_u_gauss_fun x : integral01_u x <= gauss_fun x.
Proof.
have -> : gauss_fun x = \int[mu]_(t in `[0, 1]) cst (gauss_fun x) t.
  rewrite Rintegral_cst//.
  by rewrite /mu/= lebesgue_measure_itv//= lte01 oppr0 addr0 mulr1.
rewrite fine_le//.
- apply: integrable_fin_num => //=.
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_in_subspaceT => z _; exact: continuous_u.
- apply: integrable_fin_num => //=.
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_subspaceT => z; exact: cvg_cst.
apply: ge0_le_integral => //=.
- by move=> y _; rewrite lee_fin u_ge0.
- by apply/measurable_EFinP => /=; apply/measurable_funTS; exact: measurable_u.
- by move=> y _; rewrite lee_fin u_gauss_fun.
Qed.

Let cvg_integral01_u : integral01_u x @[x --> +oo] --> 0.
Proof.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) gauss_fun).
- by near=> n => /=; rewrite integral01_u_gauss_fun integral01_u_ge0.
- exact: cvg_cst.
- exact: cvg_gauss_fun.
Unshelve. all: end_near. Qed.

Lemma cvg_integral0_gauss_sqr :
  (integral0_gauss x) ^+ 2 @[x --> +oo] --> pi / 4.
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
      by apply: cvgM; apply: continuous_integral0_gauss; exact: ltW.
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

Lemma integral0y_gauss :
  (\int[mu]_(x in `[0%R, +oo[) (gauss_fun x)%:E)%E = (Num.sqrt pi / 2)%:E.
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
have /cvg_lim := @ge0_cvgn_integral R mu _ gauss_fun_ge0 measurable_gauss_fun.
rewrite /integral0y_gauss => <-//.
suff: limn (fun n => (\int[mu]_(x in `[0%R, n%:R]) (gauss_fun x)%:E)%E) =
    (Num.sqrt pi / 2)%:E.
  by move=> ->.
apply/cvg_lim => //.
move/cvg_pinftyP : cvg_Ig => /(_ _ cvgr_idn).
move/neq0_fine_cvgP; apply.
by rewrite gt_eqF// divr_gt0// sqrtr_gt0 pi_gt0.
Qed.

Theorem integralT_gauss : (\int[mu]_x (gauss_fun x)%:E)%E = (Num.sqrt pi)%:E.
Proof.
rewrite ge0_symfun_integralT//=.
- rewrite (_ : [set x | _] = `[0, +oo[%classic); last first.
    by apply/seteqP; split => x/=; rewrite in_itv/= andbT.
  by rewrite integral0y_gauss -EFinM mulrCA divff// mulr1.
- by move=> x; exact: gauss_fun_ge0.
- exact: continuous_gauss_fun.
- by move=> x/=; rewrite /gauss_fun sqrrN.
Qed.

Lemma integrableT_gauss : mu.-integrable setT (EFin \o gauss_fun).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP/measurable_funTS; exact: measurable_gauss_fun.
apply/abse_integralP => //=.
  by apply/measurable_EFinP/measurable_funTS; exact: measurable_gauss_fun.
by rewrite integralT_gauss/= ltry.
Qed.

End gauss_integral.
