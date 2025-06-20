From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp measure.
From mathcomp Require Import lebesgue_measure numfun lebesgue_integral.
From mathcomp Require Import interval_inference real_interval realfun derive.
From mathcomp Require Import trigo ftc gauss_integral.

(**md**************************************************************************)
(* # Improper Integral                                                        *)
(* # calculating gauss integrals by limit                                     *)
(* ref: https://www.phys.uconn.edu/~rozman/Courses/P2400_17S/                 *)
(*                                            downloads/gaussian-integral.pdf *)
(*  u (x : R) (y : R) : R == a function dominates gauss_fun over `[0, +oo[    *)
(*     int0yu (x : R) : R == (u x) integrated for y over `[0, +oo[, which is  *)
(*                           J in ref.                                        *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import Num numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section gauss_integral_alternative.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Notation gauss_fun := (@gauss_fun R).
Local Notation u := (@gauss_integral_proof.u R).
Local Notation "'d1 f" := (partial1of2 f).

Section gauss_integral_preliminaries.

Lemma integral0y_gauss_fin_num :
  (\int[mu]_(x in `[0%R, +oo[) (gauss_fun x)%:E)%E \is a fin_num.
Proof.
rewrite ge0_fin_numE//; last first.
  by apply: integral_ge0 => //= x _; rewrite lee_fin gauss_fun_ge0.
rewrite (_: `[0%R, +oo[%classic = `[0%R, 1%R[ `|` `[1%R, +oo[); last first.
  by apply: set_interval.itv_bndbnd_setU; rewrite bnd_simp.
rewrite ge0_integral_setU => //=; last 3 first.
- by apply/measurable_funTS/measurable_EFinP; exact: measurable_gauss_fun.
- by move=> ? _; exact: gauss_fun_ge0.
- apply: lt_disjoint => x y; rewrite !in_itv/= => /andP[_ +] /andP[+ _].
  exact: lt_le_trans.
apply: lte_add_pinfty.
  apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R[) (cst 1) x))%E.
    apply: ge0_le_integral => //; last 2 first.
    - by apply/measurable_funTS/measurable_EFinP; exact: measurable_gauss_fun.
    - by move=> x _; rewrite lee_fin gauss_fun_le1.
    by move=> ? _; rewrite lee_fin gauss_fun_ge0.
  rewrite integral_cst/=; last exact: measurable_itv.
  by rewrite lebesgue_measure_itv/= lte01 oppr0 adde0 mule1 ltry.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[1%R, +oo[) (expR (- x))%:E))%E.
  apply: ge0_le_integral => //=.
  - by move=> x _; rewrite lee_fin gauss_fun_ge0.
  - by apply/measurable_funTS/measurable_EFinP; exact: measurable_gauss_fun.
  - apply/measurable_funTS/measurableT_comp => //; exact: measurableT_comp.
  move=> x; rewrite in_itv/= => /andP[x1 _].
  by rewrite lee_fin ler_expR lerN2 expr2 ler_peMl// (le_trans _ x1).
have cvgr_NexpR : -%R (@expR R (- x)) @[x --> +oo%R] --> 0%R.
  by rewrite -oppr0; apply: cvgN; exact: cvgr_expR.
rewrite (ge0_continuous_FTC2y _ _ cvgr_NexpR); last 5 first.
- by move=> x x0; rewrite expR_ge0.
- apply/continuous_within_itvcyP; split.
    move=> ? _; apply: continuous_comp.
      exact: continuousN.
    exact: continuous_expR.
  apply: cvg_at_right_filter.
  rewrite expRN; under eq_cvg do rewrite expRN; apply: cvgV => //.
  exact: continuous_expR.
- move=> ? _; exact: ex_derive.
- apply: cvg_at_right_filter.
  apply: cvgN => //; rewrite expRN; under eq_cvg do rewrite expRN.
  by apply: cvgV => //; exact: continuous_expR.
- by move=> x x1; rewrite derive1E derive_val mulrN1 opprK.
by rewrite -EFinB ltry.
Qed.

End gauss_integral_preliminaries.

Section u_properties.

Lemma integral0y_u0 :
   (\int[mu]_(y in `[0%R, +oo[) (u 0%R y)%:E = (@pi R / 2)%:E).
Proof.
rewrite /gauss_integral_proof.u expr0n/= oppr0.
under eq_integral do rewrite mul0r expR0 div1r.
exact: integral0y_oneDsqr.
Qed.

Lemma integrable0y_u x : mu.-integrable `[0%R, +oo[ (EFin \o u x).
Proof.
have ? : measurable_fun `[(0%R : R), +oo[ (EFin \o u x).
  apply/measurable_EFinP/measurable_funTS.
  exact: gauss_integral_proof.measurable_u.
apply/integrableP; split => //.
apply/abse_integralP => //.
rewrite -fin_num_abs ge0_fin_numE; last first.
  by apply: integral_ge0 => z z0; rewrite lee_fin gauss_integral_proof.u_ge0.
apply: (@le_lt_trans _ _ (\int[mu]_(y in `[0%R, +oo[) (EFin \o u 0%R) y))%E.
  apply: ge0_le_integral => //.
  - by move=> z _; rewrite lee_fin gauss_integral_proof.u_ge0.
  - by move=> z _; rewrite lee_fin gauss_integral_proof.u_ge0.
  - apply/measurable_EFinP/measurable_funTS.
    exact: gauss_integral_proof.measurable_u.
  move=> z z0; rewrite lee_fin ler_pdivrMr ?oneDsqr_gt0// divfK ?oneDsqr_neq0//.
  rewrite ler_expR expr0n oppr0/= mul0r pmulr_lle0 ?oneDsqr_gt0//.
  by rewrite lerNl oppr0 sqr_ge0.
by rewrite integral0y_u0 ltry.
Qed.

End u_properties.

Section gauss_dominates.
Local Open Scope ring_scope.

Definition max_x : R := (Num.sqrt 2)^-1.

Let max_x_ge0 : (0 <= max_x). Proof. by rewrite invr_ge0. Qed.

Definition max_y : R := 2 / Num.sqrt 2 / Num.sqrt (expR 1).

Lemma max_y_ge0 : (0 <= max_y). Proof. by rewrite mulr_ge0. Qed.

Definition ndgauss (x : R) := (2 * x * expR (- x ^+ 2)).

Definition nd2gauss (x : R) := (expR (- x ^+ 2) * (2 - 4 * x ^+ 2)).

Let ndgaussE : ndgauss^`() = nd2gauss.
Proof.
apply/funext => x; rewrite /ndgauss/= derive1E derive_val/GRing.scale/= 2!mulr1.
rewrite -mulr2n mulrCA mulrN -mulrDr addrC; congr (_ * (_ + - _))%R.
by rewrite expr2 -(mulr_natr x) mulrCA mulrAC -mulrC mulrA -natrM.
Qed.

Let ndgauss_maxE : ndgauss max_x = max_y.
Proof.
rewrite /ndgauss/= /max_x exprVn expRN sqr_sqrtr//.
by rewrite -(div1r 2) expRM powR12_sqrt ?expR_ge0//.
Qed.

Let ndgauss_ub (x : R) : 0 <= x -> ndgauss x <= max_y.
Proof.
rewrite le_eqVlt => /predU1P[<- |x0].
  rewrite /ndgauss mulr0 mul0r; exact: max_y_ge0.
rewrite -ndgauss_maxE.
have [xmax|xmax] := leP x max_x.
- apply: (@ger0_derive1_ndecr _ _ 0 max_x) => //; last exact: ltW; last first.
    exact: derivable_within_continuous.
  move=> y /[!in_itv]/= => /andP[y0 ymax].
  rewrite ndgaussE mulr_ge0 ?expR_ge0// subr_ge0.
  rewrite (natrM _ 2 2) -mulrA ler_piMr// -ler_pdivlMl// mulr1.
  move/ltW : ymax => /(lerXn2r 2); rewrite !nnegrE => /(_ (ltW y0) max_x_ge0).
  by rewrite /max_x exprVn sqr_sqrtr.
- apply: (@ler0_derive1_nincry _ _ max_x) => //; last exact/ltW; last first.
    exact: derivable_within_continuous.
  move=> y /[!in_itv]/= => /andP[ymax _].
  rewrite ndgaussE /nd2gauss mulr_ge0_le0 ?expR_ge0// subr_le0.
  rewrite (natrM _ 2 2) -mulrA ler_peMr// -ler_pdivrMl// mulr1.
  move/ltW : (ymax) => /(lerXn2r 2).
  rewrite !nnegrE => /(_ max_x_ge0 (ltW (le_lt_trans max_x_ge0 ymax))).
  by rewrite /max_x exprVn sqr_sqrtr//.
Qed.

Let d1u_tmp (x' y : R) : 'd1 u x' y = oneDsqr y * - 2 * x' * u x' y.
Proof.
rewrite gauss_integral_proof.partial1_u.
rewrite -![in RHS]mulrA [RHS]mulrC -![in RHS]mulrA.
rewrite mulVf ?oneDsqr_neq0// mulr1 -!mulrA; congr (_ * (_ * _))%R.
rewrite -expRD exprMn_comm//; last by rewrite /GRing.comm mulrC.
by rewrite mulrDr mulr1 mulNr mulrC.
Qed.

Lemma u_dominates (x : R) : (0 < x) ->
  \forall e \near (0:R)^'+,
  let I := (ball x e : set R) : set R in
  let c := (x - e : R) : R in
  forall (x1 : R)
    (y : [the measurableType (R.-ocitv.-measurable).-sigma of
     g_sigma_algebraType R.-ocitv.-measurable]),
  `](x - e)%R, (x + e)[%classic x1 ->
  `[0%R, +oo[%classic y ->
  (normr (('d1 u) x1 y) <= max_y * expR (- c ^+ 2 * y ^+ 2))%R.
Proof.
move=> x0.
near=> e; move=> x' y /=; rewrite in_itv/= d1u_tmp => /andP[/ltW xex' x'xe] y0.
have x'0 : 0 < x'.
  by rewrite (lt_le_trans _ xex')// subr_gt0; near: e; apply: nbhs_right_lt.
rewrite [leLHS](_ : _ = 2 * normr x' * (expR (- x' ^+ 2 * oneDsqr y)));
    last first.
  rewrite /u/gauss_integral_proof.u.
  rewrite -2![in LHS]mulrA mulrC -3![in LHS]mulrA mulVf ?oneDsqr_neq0// mulr1.
  rewrite normrM normrN (@ger0_norm _ 2)//.
  by rewrite normrM (@ger0_norm _ (expR _)) ?expR_ge0// mulrA.
rewrite mulrDr mulr1 expRD mulrA ler_pM//.
  by move: y0; rewrite in_itv/= andbT => y0; rewrite ger0_norm ?ndgauss_ub ?ltW.
rewrite ler_expR 2!mulNr lerN2 ler_wpM2r// ?sqr_ge0//.
by rewrite ler_sqr ?nnegrE// ltW// subr_gt0; near: e; exact: nbhs_right_lt.
Unshelve. end_near. Qed.

End gauss_dominates.

Section derive_and_integral_u.
Local Open Scope ring_scope.
Local Import Num Num.Theory.

Let int0yu (x : R) := \int[mu]_(y in `[0, +oo[) u x y.

Lemma int0yu_fin_num x : (\int[mu]_(x0 in `[0%R, +oo[) (u x x0)%:E)%E \is a fin_num.
Proof.
move: (integrable0y_u x).
have int0yu_ge0 : (0 <= \int[mu]_(x0 in `[0%R, +oo[) (u x x0)%:E)%E.
  by apply: integral_ge0 => y _; rewrite lee_fin gauss_integral_proof.u_ge0.
move/integrableP => [_].
rewrite ge0_fin_numE => //.
have : measurable_fun `[(0 : R), +oo[ (EFin \o u x).
  apply/measurable_EFinP; apply/measurable_funTS.
  exact: gauss_integral_proof.measurable_u.
move/(abse_integralP mu (measurable_itv _)) => [_].
by rewrite -(@ge0_fin_numE _ (`| _|))// abse_fin_num ge0_fin_numE/=.
Qed.

Lemma cvgy_int0yu0 : int0yu x @[x --> +oo] --> 0.
Proof.
apply/cvgrPdist_le => /= e e0; near=> x; rewrite sub0r.
rewrite ler0_norm ?oppr_le0; last first.
  by apply: Rintegral_ge0 => ? ?; exact: gauss_integral_proof.u_ge0.
rewrite opprK (@le_trans _ _ (expR (- x ^+ 2) * int0yu 0))//.
  rewrite [leRHS](_ : _ = fine ((expR (- x ^+ 2))%:E) * int0yu 0) => //.
  rewrite -fineM => //; last exact: int0yu_fin_num.
  rewrite /int0yu/Rintegral fine_le ?fin_numM//.
  - exact: int0yu_fin_num.
  - exact: int0yu_fin_num.
  rewrite -ge0_integralZl//=; last 2 first.
  - apply/measurable_funTS/measurable_EFinP.
    exact: gauss_integral_proof.measurable_u.
  - by move=> ? _; rewrite lee_fin gauss_integral_proof.u_ge0.
  apply: le_integral => //; first exact: integrable0y_u.
    by rewrite integrableZl//; exact: integrable0y_u.
  move=> y _.
  rewrite lee_fin ler_pdivrMr ?oneDsqr_gt0//.
  rewrite mulrA divfK ?oneDsqr_neq0//.
  rewrite expr0n oppr0/= mul0r expR0 mulr1 ler_expR.
  by rewrite ler_neMr ?oneDsqr_ge1// oppr_le0; exact: sqr_ge0.
rewrite /int0yu/Rintegral integral0y_u0/=.
rewrite -ler_pdivlMr; last exact: lt_le_trans (pihalf_ge1 _).
rewrite expRN -[leRHS]invrK lef_pV2 ?posrE; last 2 first.
- exact: expR_gt0.
- by rewrite invr_gt0 divr_gt0//; apply: lt_le_trans (pihalf_ge1 _).
rewrite -[leLHS]lnK ?posrE; last first.
  by rewrite invr_gt0 divr_gt0//; apply: lt_le_trans (pihalf_ge1 _).
rewrite ler_expR -ler_sqrt; last exact: sqr_ge0.
by rewrite sqrtr_sqr ger0_norm.
Unshelve. end_near. Qed.

Let der_mulrE (x : R) : (fun z => x * z)^`() = cst x.
Proof.
under eq_fun do rewrite mulrC.
by apply/funext => z; rewrite (@derive1Mr R id z x)// derive1_id mul1r.
Qed.

Let integrable0y_gaussZl (c : R) : c != 0 -> mu.-integrable `[0, +oo[
  (fun z => (expR (- (c * z) ^+ 2))%:E).
Proof.
suff : (forall c : R, 0 < c -> mu.-integrable `[0, +oo[
   (fun z => (expR (- (c * z) ^+ 2))%:E)).
  move=> Hsuff; rewrite neq_lt => /orP; case => c0.
  - under [X in _.-integrable _ X]eq_fun do rewrite -sqrrN -(mulNr c).
    by apply: Hsuff; rewrite oppr_gt0.
  - exact: Hsuff.
move=> /=  {}c c0.
have mcg : measurable_fun `[@GRing.zero R, +oo[
   (fun x => (expR (- (c * x)^+2))%:E).
  exact/measurable_EFinP/(measurableT_comp measurable_gauss_fun).
apply/integrableP; split => //; apply/abse_integralP => //=.
rewrite -ge0_fin_numE; last exact: abse_ge0.
rewrite abse_fin_num ge0_fin_numE; last first.
  apply: integral_ge0 => z _.
  exact: gauss_fun_ge0.
under eq_integral.
  move=> z _.
  have -> :((expR (- (c * z) ^+ 2))%:E =
   c^-1%:E * (((gauss_fun \o (fun z => c * z)) * (fun z => c * z)^`()) z)%:E)%E.
    rewrite !fctE derive1E derive_val EFinM muleC -muleA -EFinM.
    by rewrite /GRing.scale/= mulr1 mulfV ?mulr1// gt_eqF.
  over.
rewrite ge0_integralZl//; first last.
  - by rewrite lee_fin invr_ge0 ltW.
  - move=> x _.
    rewrite !fctE derive1E derive_val /GRing.scale/= mulr1.
    by rewrite lee_fin mulr_ge0 ?gauss_fun_ge0 ?ltW.
  - under [X in _ _ X]eq_fun.
      move=> x.
      rewrite !fctE derive1E derive_val /GRing.scale/= mulr1.
      over.
    apply/measurable_EFinP.
    rewrite /=.
    apply: (measurableT_comp (mulrr_measurable _)).
    exact: (measurableT_comp measurable_gauss_fun).
rewrite -increasing_ge0_integration_by_substitutiony//= ?der_mulrE; last 8 first.
- by move=> ? ? _ _ +; rewrite ltr_pM2l.
- by move=> ? _; exact: cst_continuous.
- exact: is_cvg_cst.
- exact: is_cvg_cst.
- split => //; apply: cvgZr; exact: cvg_at_right_filter.
- apply/cvgryPge => r; under eq_near do rewrite -ler_pdivrMl//.
  apply: nbhs_pinfty_ge; exact: num_real.
- by apply: continuous_subspaceT; exact: continuous_gauss_fun.
- move=> ? _; exact: gauss_fun_ge0.
have cV_ge0 : (0 <= (c^-1)%:E)%E by rewrite lee_fin invr_ge0 ltW.
apply: lte_mul_pinfty => //.
rewrite -ge0_fin_numE mulr0; first exact: integral0y_gauss_fin_num.
by apply: integral_ge0 => ? _; rewrite lee_fin gauss_fun_ge0.
Qed.

Let derivable_u (x y : R) : derivable (u^~ y) x 1.
Proof.
rewrite /u/gauss_integral_proof.u.
apply/derivable1_diffP/differentiableM; last by apply: differentiableV => //.
by apply: differentiable_comp => //; exact/derivable1_diffP.
Qed.

Let substE x : 0 < x ->
  (\int[mu]_(y in `[0%R, +oo[) (expR (- x ^+ 2 * oneDsqr y))%:E =
  \int[mu]_(y in `[0%R, +oo[)
                    ((((fun z => gauss_fun x / x * gauss_fun z) \o
                    (fun z => x * z)) * (fun z => x * z)^`()) y)%:E)%E.
Proof.
move=> x0; apply: eq_integral => y _.
rewrite !fctE derive1E derive_val /GRing.scale/= mulr1.
rewrite mulrAC divfK//; last by rewrite gt_eqF.
by rewrite mulrDr mulr1 mulNr -exprMn expRD.
Qed.

Let int_substE x : 0 < x ->
  (\int[mu]_(y in `[0%R, +oo[) (expR (- x ^+ 2 * oneDsqr y))%:E
 = \int[mu]_(x1 in `[0%R, +oo[) (gauss_fun x / x * gauss_fun x1)%:E)%E.
Proof.
move=> x0; rewrite substE; last exact: x0.
rewrite -increasing_ge0_integration_by_substitutiony ?der_mulrE; last 8 first.
- by move=> ? ?; rewrite !in_itv/= 2!andbT; rewrite ltr_pM2l.
- by move=> ? _; exact: cst_continuous.
- exact: is_cvg_cst.
- exact: is_cvg_cst.
- by split => //; apply: cvgZr; exact: cvg_at_right_filter.
- apply/cvgryPge => r; near=> t; rewrite -lter_pdivrMl; last exact: x0; near: t.
  by apply:nbhs_pinfty_ge; rewrite num_real.
- apply: continuous_subspaceT.
  by move=> ?; apply: continuousZr; exact: continuous_gauss_fun.
- by move=> y _; rewrite mulr_ge0 ?expR_ge0// divr_ge0 ?expR_ge0// ltW.
by rewrite mulr0.
Unshelve. end_near. Qed.

Let derive1_int0yuE_subproof1 x : 0 < x ->
  int0yu^`() x = \int[mu]_(y in `[0, +oo[) ('d1 u) x y.
Proof.
move=> x0.
near ((0:R)^'+) => e.
have xex : `]x - e, x + e[%classic x by rewrite -ball_itv; exact: ballxx.
pose G := (fun y => (max_y) * expR (- (x - e) ^+ 2 * y ^+ 2)).
rewrite (@differentiation_under_integral R _ _ mu _ _ _ _ _ _ xex _ _ G)//.
- by move=> ? _; exact: integrable0y_u.
- by move=> ?; rewrite mulr_ge0// ?expR_ge0// max_y_ge0.
- under [X in _ _ X]eq_fun do rewrite EFinM mulNr.
  under [X in _ _ X]eq_fun do (rewrite -exprMn_comm; last exact: mulrC).
  apply/integrableZl=> //; rewrite integrable0y_gaussZl ?gt_eqF// subr_gt0.
  by near: e; exact: nbhs_right_lt.
- by rewrite {}/G; near: e; exact: u_dominates.
Unshelve. end_near. Qed.

Let derive1_int0yuE_subproof2 x : (0 < x) ->
  \int[mu]_(y in `[0, +oo[) ('d1 u) x y =
    -2 * x * \int[mu]_(y in `[0, +oo[) (expR ((- x ^+ 2) * oneDsqr y)).
Proof.
move=> x0.
have mexpRVxexpR (D : set R) :
    measurable_fun D (fun y => gauss_fun x / x * gauss_fun y).
  apply: measurable_funM => //; apply: measurable_funTS.
  exact: measurable_gauss_fun.
rewrite /Rintegral (_ : - 2 * x = fine (- 2 * x)%:E)//.
rewrite -fineM//; last first.
  rewrite ge0_fin_numE; last by apply: integral_ge0 => ? _; exact: expR_ge0.
  apply: (@le_lt_trans _ _
       (\int[mu]_(y in `[0%R, +oo[) (gauss_fun (x * y))%:E)%E).
    apply: ge0_le_integral => //.
    - apply/measurable_EFinP/measurable_funTS.
      apply: measurableT_comp => //.
      apply: measurable_funM => //.
      exact: measurable_funD.
    - by move=> y _; exact: gauss_fun_ge0.
    - apply/measurable_EFinP/measurable_funTS.
      apply: measurableT_comp => //.
      exact: measurable_gauss_fun.
    - move=> y _; rewrite lee_fin ler_expR.
      by rewrite mulNr lerN2 mulrDr exprMn lerDr mulr1 sqr_ge0.
  under eq_integral => y _.
    rewrite [X in X%:E](_ : _ =
       ((gauss_fun \o ( *%R x)) \* ( *%R x)^`()) y * x^-1); last first.
     by rewrite der_mulrE/= mulfK ?gt_eqF.
   rewrite EFinM.
   over.
  rewrite ge0_integralZr// ?lee_fin ?invr_ge0 ?ltW//; last 2 first.
  - apply/measurable_EFinP/measurable_funM; last by rewrite der_mulrE.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_gauss_fun.
  - by move=> ? _; rewrite lee_fin der_mulrE mulr_ge0// ?gauss_fun_ge0 ?ltW.
  rewrite -increasing_ge0_integration_by_substitutiony ?der_mulrE; last 8 first.
  - by move=> ? ? _ _; rewrite ?ltr_pM2l ?invr_gt0.
  - by move=> ? _; exact: cst_continuous.
  - exact: is_cvg_cst.
  - exact: is_cvg_cst.
  - split; first (move=> ? _; exact: ex_derive).
    by apply: cvgMr; apply: cvg_at_right_filter; exact: cvg_id.
  - by under eq_cvg do rewrite mulrC; apply: gt0_cvgMly => //; rewrite invr_gt0.
  - apply: continuous_subspaceT => y; exact: continuous_gauss_fun.
  - by move=> y _; exact: gauss_fun_ge0.
  rewrite lte_mul_pinfty ?ltry ?mulr0 ?integral0y_gauss_fin_num//.
  by rewrite integral_ge0// => ? _; rewrite lee_fin gauss_fun_ge0.
rewrite mulNr EFinN mulNe -ge0_integralZl ?lee_fin ?mulr_ge0 ?ltW//; last first.
  apply/measurable_EFinP/measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funD.
rewrite -integral_ge0N; last first.
  by move=> ? _; apply: mulr_ge0; rewrite ?expR_ge0// mulr_ge0// ltW.
congr fine; apply: eq_integral=> y; rewrite inE/= in_itv/= => y0.
rewrite /partial1of2 derive1E derive_val.
rewrite 3!scaler0 2!add0r mulrC scalerA /GRing.scale/= mulrA mulr1.
by rewrite mulVf// mul1r -mulr2n mulNr mulr_natl.
Qed.

Lemma derive1_int0yuE : {in `]0, +oo[,
  int0yu^`() =1
 (fun x => (- 2) * gauss_integral_proof.integral0y_gauss * gauss_fun x)}.
Proof.
move=> x; rewrite in_itv/= => /andP[x0 _].
rewrite derive1_int0yuE_subproof1//.
rewrite derive1_int0yuE_subproof2//.
rewrite /Rintegral int_substE//.
under eq_integral do rewrite EFinM; rewrite ge0_integralZl//=; last 3 first.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_gauss_fun.
- by move=> ? _; exact: gauss_fun_ge0.
- by rewrite lee_fin divr_ge0 ?expR_ge0// ltW.
rewrite fineM//=; last exact: integral0y_gauss_fin_num.
by rewrite -3!mulrA [X in (-2 * X)]mulrCA !mulrA mulfK ?gt_eqF// mulrAC.
Unshelve. all: end_near. Qed.

Let cvg_u (y : R) : u x y @[x --> 0^'] --> u 0 y.
Proof.
apply/cvgrPdist_lep; near=> e; near=> t.
rewrite {1}/u/gauss_integral_proof.u expr0n/= oppr0 mul0r expR0.
have /normr_idP -> : 0 <= 1 / oneDsqr y - u t y.
  rewrite -mulNr -mulrDl divr_ge0 ?oneDsqr_ge0// subr_ge0 -expR0 ler_expR.
  by rewrite mulNr oppr_le0 mulr_ge0// ?sqr_ge0 ?oneDsqr_ge0.
rewrite -mulNr -mulrDl ler_pdivrMr ?oneDsqr_gt0// lerBlDl -lerBlDr.
rewrite -[leLHS]lnK; last by rewrite posrE subr_gt0 -ltr_pdivlMr ?oneDsqr_gt0.
rewrite ler_expR -ler_pdivrMr ?oneDsqr_gt0// lerNr -ler_sqrt; last first.
  rewrite lerNr oppr0 mulr_le0_ge0 ?invr_ge0 ?oneDsqr_ge0// ln_le0//.
  by rewrite gerBl mulr_ge0// oneDsqr_ge0.
rewrite sqrtr_sqr.
near: t; rewrite near_nbhs; apply: dnbhs0_le.
rewrite sqrtr_gt0 oppr_gt0 pmulr_llt0 ?invr_gt0 ?oneDsqr_gt0// ln_lt0//.
apply/andP; split; last by rewrite gtrBl mulr_gt0// oneDsqr_gt0.
by rewrite subr_gt0 -ltr_pdivlMr ?oneDsqr_gt0.
Unshelve. all:end_near. Qed.

Lemma derivable_int0yu : {in `]0, +oo[, forall x, derivable int0yu x 1}.
Proof.
move=> x; rewrite in_itv/= andbT => x0.
near (0:R)^'+ => e.
pose ballx : set R := ball x e.
have ballx_x : `]x - e, x + e[%classic x.
  rewrite -ball_itv.
  exact: ballxx.
pose c : R := x - e.
apply: (@derivable_under_integral _ _ (measurableTypeR R) _ _ _ _ _ _ _ ballx_x
   _ _ (fun y => (max_y) * expR (- c ^+ 2 * y ^+ 2))) => //.
- by move=> ? _; exact: integrable0y_u.
- by move=> /= ?; rewrite mulr_ge0// ?expR_ge0// max_y_ge0.
- rewrite (_ : _ \o _ =
    (fun x=> (max_y)%:E * (expR (- c ^+ 2 * x ^+ 2))%:E)%E)//.
  apply: integrableZl => //=.
  under [X in _.-integrable _ X]eq_fun => z.
    rewrite mulNr -exprMn_comm; last exact: mulrC.
    over.
  apply: integrable0y_gaussZl.
  by rewrite gt_eqF// subr_gt0; near: e; apply: nbhs_right_lt.
- by rewrite {}/ballx {}/c; near: e; exact: u_dominates.
Unshelve. all: end_near. Qed.

Lemma rc_int0yu0 : int0yu x @[x --> 0^'+] --> int0yu 0.
Proof.
apply/cvg_at_rightP.
move=> x_ [x_ge0 x_0].
rewrite /int0yu.
suff : [/\ mu.-integrable `[0%R, +oo[ (EFin \o u 0),
(\int[mu]_(x in `[0%R, +oo[) `|(EFin \o u (x_ n)) x - (EFin \o u 0) x|)%E
   @[n --> \oo] --> 0%E
   & (\int[mu]_(x in `[0%R, +oo[) (EFin \o u (x_ n)) x)%E @[n --> \oo] -->
   (\int[mu]_(x in `[0%R, +oo[) (EFin \o u 0) x)%E].
  move=> [_ lim_norm0 cvgint0yu].
  apply: fine_cvg; rewrite fineK; first exact: cvgint0yu.
  rewrite integral0y_u0 ge0_fin_numE; first by rewrite ltry.
  by rewrite lee_fin divr_ge0// pi_ge0.
have intbl0y_u0 : mu.-integrable `[0%R, +oo[ (EFin \o u 0).
  exact: integrable0y_u.
apply: (dominated_convergence _ _ _ _ intbl0y_u0) => //.
- move=> n; apply/measurable_funTS/measurable_EFinP.
  exact: gauss_integral_proof.measurable_u.
- apply/measurable_funTS/measurable_EFinP.
  exact: gauss_integral_proof.measurable_u.
- apply: aeW => /= y _; apply: cvg_EFin.
    apply: nearW => n; rewrite ge0_fin_numE; first exact: ltry.
    by rewrite lee_fin mulr_ge0// ?expR_ge0// invr_ge0// oneDsqr_ge0.
  apply: (cvgr_dnbhsP (u ^~ y) 0%R (u 0 y)).1; first exact: cvg_u.
  split; last exact: x_0.
  by move=> n; rewrite gt_eqF.
- apply: aeW => /= x n _.
  have /normr_idP -> : (0 <= gauss_integral_proof.u (x_ n) x)%R.
    by rewrite mulr_ge0// ?expR_ge0 ?invr_ge0 ?oneDsqr_ge0.
  rewrite lee_fin.
  apply: ler_pM => //; rewrite ?expR_ge0 ?invr_ge0 ?oneDsqr_ge0//.
  rewrite expr0n oppr0 mul0r ler_expR mulNr oppr_le0.
  by rewrite mulr_ge0 ?sqr_ge0// oneDsqr_ge0.
Qed.

End derive_and_integral_u.

Section Gauss_integration.

Let integrable0y_gauss : mu.-integrable `[0%R, +oo[ (EFin \o gauss_fun).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP/measurableT_comp => //; exact: measurableT_comp.
apply/abse_integralP => //.
  by apply/measurable_EFinP/measurableT_comp => //; exact: measurableT_comp.
rewrite -ge0_fin_numE ?abse_ge0// abse_fin_num.
exact: integral0y_gauss_fin_num.
Qed.

Lemma gauss_integration : (\int[mu]_x (gauss_fun x))%R = Num.sqrt pi.
Proof.
rewrite /Rintegral ge0_symfun_integralT; last 3 first.
- by move=> x; rewrite gauss_fun_ge0.
- exact: continuous_gauss_fun.
- by move=> x; rewrite /gauss_fun fctE sqrrN.
rewrite -set_itvcy fineM//=; last exact: integral0y_gauss_fin_num.
apply: (@mulIf R (2^-1)) => //.
rewrite mulrAC mulfV// mul1r -[LHS]ger0_norm -?sqrtr_sqr; last first.
  exact: gauss_integral_proof.integral0y_gauss_ge0.
rewrite -(@ger0_norm _ 2)// -(@sqrtr_sqr _ 2)//-sqrtrV// -[RHS]sqrtrM ?pi_ge0//.
apply/eqP; rewrite eqr_sqrt ?sqr_ge0 ?divr_ge0 ?pi_ge0//; apply/eqP.
rewrite [in RHS]expr2 invfM// mulrA.
apply: (@mulIf _ (- 2)%R) => //; rewrite [RHS]mulrN divfK// mulrC -[RHS]add0r.
apply: EFin_inj; rewrite EFinB.
have cdint0yu x : {for x, continuous
(fun x1 : R => (- 2 * gauss_integral_proof.integral0y_gauss * gauss_fun x1)%R)}.
  apply: continuousM; first exact: cvg_cst.
  by move=> ?; exact: continuous_gauss_fun.
rewrite -integral0y_u0 -[X in _ = 0%:E - X]fineK; last by rewrite integral0y_u0.
rewrite -(le0_continuous_FTC2y _ _ cvgy_int0yu0 _ _ derive1_int0yuE); last 4 first.
- move=> x x0; rewrite -mulN1r -!mulrA mulN1r lerNl oppr0.
  rewrite pmulr_rge0// mulr_ge0 ?gauss_fun_ge0//.
  exact: gauss_integral_proof.integral0y_gauss_ge0.
- apply/continuous_within_itvcyP; split; first by move=> x _; exact: cdint0yu.
  apply: cvg_at_right_filter; exact: cdint0yu.
- exact: rc_int0yu0.
- by move=> x x0; apply: derivable_int0yu; rewrite in_itv/= andbT.
under [RHS]eq_integral do rewrite !EFinM EFinN !mulNe.
rewrite integral_ge0N; last first.
- move=> x _; rewrite lee_fin mulr_ge0 ?gauss_fun_ge0// mulr_ge0//.
  exact: gauss_integral_proof.integral0y_gauss_ge0.
rewrite ge0_integralZl//; last 3 first.
- apply: measurable_funTS; apply/measurable_EFinP.
  exact: measurable_gauss_fun.
- by move=> x _; apply: gauss_fun_ge0.
- apply: mulr_ge0 => //.
  exact: gauss_integral_proof.integral0y_gauss_ge0.
rewrite expr2 mulrA [LHS]EFinM EFinM EFinN !mulNe; congr (- (_ * _)).
by rewrite fineK// ?integral0y_gauss_fin_num.
Qed.

End Gauss_integration.

End gauss_integral_alternative.
