(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum function_spaces measure lebesgue_measure.
From mathcomp Require Import numfun realfun simple_functions.
From mathcomp Require Import measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.
From mathcomp Require Import lebesgue_integral_nonneg.
From mathcomp Require Import lebesgue_integrable.
From mathcomp Require Import lebesgue_integral_dominated_convergence.
From mathcomp Require Import lebesgue_Rintegral.

(**md**************************************************************************)
(* # Lebesgue's differentiation theorem                                       *)
(*                                                                            *)
(* This file contains a formalization of Lebesgue's differentiation theorem.  *)
(* This includes standard lemmas such as the Hardy–Littlewood maximal         *)
(* inequality.                                                                *)
(*                                                                            *)
(* Main references:                                                           *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(* - R. Affeldt, Z. Stone. A Comprehensive Overview of the Lebesgue           *)
(*   Differentiation Theorem in Coq. ITP 2024                                 *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(* locally_integrable D f == the real number-valued function f is locally     *)
(*                           integrable on D                                  *)
(*               iavg f A := "average" of the real-valued function f over     *)
(*                           the set A                                        *)
(*             HL_maximal == the Hardy–Littlewood maximal operator            *)
(*                           input: real number-valued function               *)
(*                           output: extended real number-valued function     *)
(*             davg f x r == "deviated average" of the real-valued function   *)
(*                           f over ball x r                                  *)
(*       lim_sup_davg f x := lime_sup (davg f x) 0                            *)
(*        lebesgue_pt f x == Lebesgue point at x of the real-valued           *)
(*                           function f                                       *)
(*   nicely_shrinking x E == the sequence of sets E is nicely shrinking to x  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section continuous_compact_integrable.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.
Local Open Scope ereal_scope.

Lemma continuous_compact_integrable (f : R -> R^o) (A : set R^o) :
  compact A -> {within A, continuous f} -> mu.-integrable A (EFin \o f).
Proof.
move=> cptA ctsfA; apply: measurable_bounded_integrable.
- exact: compact_measurable.
- exact: compact_finite_measure.
- by apply: subspace_continuous_measurable_fun => //; exact: compact_measurable.
- have /compact_bounded[M [_ mrt]] := continuous_compact ctsfA cptA.
  by exists M; split; rewrite ?num_real // => ? ? ? ?; exact: mrt.
Qed.

End continuous_compact_integrable.

Section continuous_density_L1.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.
Local Open Scope ereal_scope.

Import HBSimple.

Lemma approximation_continuous_integrable (E : set _) (f : rT -> rT):
  measurable E -> mu E < +oo -> mu.-integrable E (EFin \o f) ->
  exists g_ : (rT -> rT)^nat,
    [/\ forall n, continuous (g_ n),
        forall n, mu.-integrable E (EFin \o g_ n) &
        \int[mu]_(z in E) `|(f z - g_ n z)%:E| @[n --> \oo] --> 0].
Proof.
move=> mE Efin intf.
have mf : measurable_fun E f by case/integrableP : intf => /measurable_EFinP.
suff apxf eps : exists h : rT -> rT, (eps > 0)%R ->
    [/\ continuous h,
        mu.-integrable E (EFin \o h) &
        \int[mu]_(z in E) `|(f z - h z)%:E| < eps%:E].
  pose g_ n := projT1 (cid (apxf n.+1%:R^-1)%R); exists g_; split.
  - by move=> n; have [] := projT2 (cid (apxf n.+1%:R^-1%R)).
  - by move=> n; have [] := projT2 (cid (apxf n.+1%:R^-1%R)).
  apply/cvg_ballP => eps epspos.
  have /cvg_ballP/(_ eps epspos)[N _ Nball] := @cvge_harmonic rT.
  exists N => //; apply: (subset_trans Nball) => n.
  rewrite /ball /= /ereal_ball contract0 !sub0r !normrN => /(lt_trans _); apply.
  rewrite ?ger0_norm; first last.
  - by rewrite -le_expandLR // ?inE ?normr0// expand0 integral_ge0.
  - by rewrite -le_expandLR // ?inE ?normr0// expand0.
  have [] := projT2 (cid (apxf n.+1%:R^-1%R)) => // _ _ ipaxfn.
  by rewrite -lt_expandRL ?contractK// inE contract_le1.
have [|] := ltP 0%R eps; last by exists point.
move: eps => _/posnumP[eps].
have [g [gfe2 ig]] : exists g : {sfun R >-> rT},
    \int[mu]_(z in E) `|(f z - g z)%:E| < (eps%:num / 2)%:E /\
    mu.-integrable E (EFin \o g).
  have [g_ [intG ?]] := approximation_sfun_integrable mE intf.
  move/fine_fcvg/cvg_ballP/(_ (eps%:num / 2)%R) => -[] // n _ Nb; exists (g_ n).
  have fg_fin_num : \int[mu]_(z in E) `|(f z - g_ n z)%:E| \is a fin_num.
    rewrite integrable_fin_num// integrable_abse//.
    by under eq_fun do rewrite EFinB; apply: integrableB => //; exact: intG.
  split; last exact: intG.
  have /= := Nb _ (leqnn n); rewrite /ball/= sub0r normrN -fine_abse// -lte_fin.
  by rewrite fineK ?abse_fin_num// => /le_lt_trans; apply; exact: lee_abs.
have mg : measurable_fun E g by exact: measurable_funTS.
have [M Mpos Mbd] : (exists2 M, 0 < M & forall x, `|g x| <= M)%R.
  have [M [_ /= bdM]] := simple_bounded g.
  exists (`|M| + 1)%R; first exact: ltr_pwDr.
  by move=> x; rewrite bdM// ltr_pwDr// ler_norm.
have [] // := @measurable_almost_continuous _ _ mE _ g (eps%:num / 2 / (M *+ 2)).
  by rewrite divr_gt0// mulrn_wgt0.
move=> A [cptA AE /= muAE ctsAF].
have [] := continuous_bounded_extension _ _ Mpos ctsAF.
- exact: pseudometric_normal.
- by apply: compact_closed => //; exact: Rhausdorff.
- by move=> ? ?; exact: Mbd.
have mA : measurable A := compact_measurable cptA.
move=> h [gh ctsh hbdM]; have mh : measurable_fun E h.
  by apply: subspace_continuous_measurable_fun=> //; exact: continuous_subspaceT.
have intg : mu.-integrable E (EFin \o h).
  apply: measurable_bounded_integrable => //.
  exists M; split; rewrite ?num_real // => x Mx y _ /=.
  by rewrite (le_trans _ (ltW Mx)).
exists h; split => //; rewrite [eps%:num]splitr; apply: le_lt_trans.
  pose fgh x := `|(f x - g x)%:E| + `|(g x - h x)%:E|.
  apply: (@ge0_le_integral _ _ _ mu _ mE _ fgh) => //.
  - apply: (measurable_funS mE) => //; do 2 apply: measurableT_comp => //.
    exact: measurable_funB.
  - apply: measurableT_comp => //; apply: measurable_funD;
      apply: (measurable_funS mE (@subset_refl _ E));
      (apply: measurableT_comp => //);
      exact: measurable_funB.
  - move=> x _; rewrite -(subrK (g x) (f x)) -(addrA (_ + _)%R) lee_fin.
    by rewrite ler_normD.
rewrite integralD//; first last.
- by apply: integrable_abse; under eq_fun do rewrite EFinB; apply: integrableB.
- by apply: integrable_abse; under eq_fun do rewrite EFinB; apply: integrableB.
rewrite EFinD lteD// -(setDKU AE) ge0_integral_setU => //; first last.
- by rewrite /disj_set setDKI.
- rewrite setDKU //; do 2 apply: measurableT_comp => //.
  exact: measurable_funB.
- exact: measurableD.
rewrite (@ae_eq_integral _ _ _ mu A (cst 0)) //; first last.
- by apply: aeW => z Az; rewrite (gh z) ?inE// subrr abse0.
- apply: (measurable_funS mE) => //; do 2 apply: measurableT_comp => //.
  exact: measurable_funB.
rewrite integral0 adde0.
apply: (le_lt_trans (integral_le_bound (M *+ 2)%:E _ _ _ _)) => //.
- exact: measurableD.
- apply: (measurable_funS mE) => //; apply: measurableT_comp => //.
  exact: measurable_funB.
- by rewrite lee_fin mulrn_wge0// ltW.
- apply: aeW => z [Ez _]; rewrite /= lee_fin mulr2n.
  by rewrite (le_trans (ler_normB _ _))// lerD.
by rewrite -lte_pdivlMl ?mulrn_wgt0// muleC -EFinM.
Qed.

End continuous_density_L1.

Section lebesgue_differentiation_continuous.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.

Let ballE (x : R) (r : {posnum rT}) :
  ball x r%:num = `](x - r%:num), (x + r%:num)[%classic :> set rT.
Proof.
rewrite -ball_normE /ball_ set_itvoo.
by under eq_set => ? do rewrite ltr_distlC.
Qed.

Lemma lebesgue_differentiation_continuous (f : R -> rT^o) (A : set R) (x : R) :
  open A -> mu.-integrable A (EFin \o f) -> {for x, continuous f} -> A x ->
  (fun r => (r *+ 2)^-1 * \int[mu]_(z in ball x r) f z) @ 0^'+ -->
  (f x : R^o).
Proof.
have ball_itvr r : 0 < r -> `[x - r, x + r] `\` ball x r = [set x + r; x - r].
  move: r => _/posnumP[r].
  rewrite -setU1itv ?bnd_simp ?lerBlDr -?addrA ?ler_wpDr//.
  rewrite -setUitv1 ?bnd_simp ?ltrBlDr -?addrA ?ltr_pwDr//.
  rewrite setUA setUC setUA setDUl !ballE setDv setU0 setDidl// -subset0.
  by move=> z /= [[]] ->; rewrite in_itv/= ltxx// andbF.
have ball_itv2 r : 0 < r -> ball x r = `[x - r, x + r] `\` [set x + r; x - r].
  move: r => _/posnumP[r].
  rewrite -ball_itvr // setDD setIC; apply/esym/setIidPl.
  by rewrite ballE set_itvcc => ?/=; rewrite in_itv => /andP [/ltW -> /ltW ->].
have ritv r : 0 < r -> mu `[x - r, x + r]%classic = (r *+ 2)%:E.
  move=> /gt0_cp rE; rewrite /= lebesgue_measure_itv/= lte_fin.
  by rewrite ler_ltD// ?rE// -EFinD opprB addrC subrKA.
move=> oA intf ctsfx Ax.
apply: cvg_zero.
apply/cvgrPdist_le => eps epos; apply: filter_app (@nbhs_right_gt rT 0).
move/cvgrPdist_le/(_ eps epos)/at_right_in_segment : ctsfx; apply: filter_app.
apply: filter_app (open_itvcc_subset oA Ax).
have mA : measurable A := open_measurable oA.
near=> r => xrA; rewrite addrfctE opprfctE => feps rp.
have cptxr : compact `[x - r, x + r] := @segment_compact _ _ _.
rewrite distrC subr0.
have -> : \int[mu]_(z in ball x r) f z = \int[mu]_(z in `[x - r, x + r]) f z.
  rewrite ball_itv2 //; congr (fine _); rewrite -negligible_integral //.
  - by apply/measurableU; exact: measurable_set1.
  - exact: (integrableS mA).
  - by rewrite measureU0//; exact: lebesgue_measure_set1.
have r20 : 0 <= (r *+ 2)^-1 by rewrite invr_ge0 mulrn_wge0.
have -> : f x = (r *+ 2)^-1 * \int[mu]_(z in `[x - r, x + r]) cst (f x) z.
  by rewrite Rintegral_cst// ritv//= mulrC mulfK// mulrn_eq0/=.
have intRf : mu.-integrable `[x - r, x + r] (EFin \o f).
  exact: (@integrableS _ _ _ mu _ _ _ _ _ xrA intf).
rewrite /= -mulrBr -fineB; first last.
- rewrite integrable_fin_num// continuous_compact_integrable// => ?.
  exact: cvg_cst.
- by rewrite integrable_fin_num.
rewrite -integralB_EFin //; first last.
  by apply: continuous_compact_integrable => // ?; exact: cvg_cst.
under [fun _ => _ + _ ]eq_fun => ? do rewrite -EFinD.
have int_fx : mu.-integrable `[x - r, x + r] (fun z => (f z - f x)%:E).
  under [fun z => (f z - _)%:E]eq_fun => ? do rewrite EFinB.
  rewrite integrableB// continuous_compact_integrable// => ?.
  exact: cvg_cst.
rewrite normrM ger0_norm // -fine_abse //; first last.
  by rewrite integrable_fin_num.
suff : (\int[mu]_(z in `[(x - r)%R, (x + r)%R]) `|f z - f x|%:E <=
    (r *+ 2 * eps)%:E)%E.
  move=> intfeps; apply: le_trans.
    apply: (ler_pM r20 _ (le_refl _)); first exact: fine_ge0.
    apply: fine_le; last apply: le_abse_integral => //.
    - by rewrite abse_fin_num integrable_fin_num.
    - by rewrite integrable_fin_num// integrable_abse.
    - by case/integrableP : int_fx.
  rewrite ler_pdivrMl ?mulrn_wgt0 // -[_ * _]/(fine (_%:E)).
  by rewrite fine_le// integrable_fin_num// integrable_abse.
apply: le_trans.
- apply: (@integral_le_bound _ _ _ _ _ (fun z => (f z - f x)%:E) eps%:E) => //.
  + by case/integrableP: int_fx.
  + exact: ltW.
  + by apply: aeW => ? ?; rewrite /= lee_fin distrC feps.
by rewrite ritv //= -EFinM lee_fin mulrC.
Unshelve. all: by end_near. Qed.

End lebesgue_differentiation_continuous.

Section locally_integrable.
Context {R : realType}.
Implicit Types (D : set R) (f g : R -> R).
Local Open Scope ereal_scope.

Local Notation mu := lebesgue_measure.

Definition locally_integrable D f := [/\ measurable_fun D f, open D &
  forall K, K `<=` D -> compact K -> \int[mu]_(x in K) `|f x|%:E < +oo].

Lemma open_integrable_locally D f : open D ->
  mu.-integrable D (EFin \o f) -> locally_integrable D f.
Proof.
move=> oD /integrableP[mf foo]; split => //; first exact/measurable_EFinP.
move=> K KD cK; rewrite (le_lt_trans _ foo)// ge0_subset_integral//=.
- exact: compact_measurable.
- exact: open_measurable.
- apply/measurable_EFinP; apply: measurableT_comp => //.
  exact/measurable_EFinP.
Qed.

Lemma locally_integrableN D f :
  locally_integrable D f -> locally_integrable D (\- f)%R.
Proof.
move=> [mf oD foo]; split => //; first exact: measurableT_comp.
by move=> K KD cK; under eq_integral do rewrite normrN; exact: foo.
Qed.

Lemma locally_integrableD D f g :
  locally_integrable D f -> locally_integrable D g ->
  locally_integrable D (f \+ g)%R.
Proof.
move=> [mf oD foo] [mg _ goo]; split => //; first exact: measurable_funD.
move=> K KD cK.
suff : lebesgue_measure.-integrable K ((EFin \o f) \+ (EFin \o g)).
  by case/integrableP.
apply: integrableD => //=; first exact: compact_measurable.
- apply/integrableP; split; last exact: foo.
  apply/measurable_EFinP; apply: measurable_funS mf => //.
  exact: open_measurable.
- apply/integrableP; split; last exact: goo.
  apply/measurable_EFinP; apply: measurable_funS mg => //.
  exact: open_measurable.
Qed.

Lemma locally_integrableB D f g :
  locally_integrable D f -> locally_integrable D g ->
  locally_integrable D (f \- g)%R.
Proof.
by move=> lf lg; apply: locally_integrableD => //; exact: locally_integrableN.
Qed.

Lemma locally_integrable_indic D (A : set R) :
  open D -> measurable A -> locally_integrable D \1_A.
Proof.
move=> oU mA; split => // K KD_ cK.
apply: (@le_lt_trans _ _ (\int[mu]_(x in K) cst 1 x)).
  apply: ge0_le_integral => //=; first exact: compact_measurable.
  - by do 2 apply: measurableT_comp => //.
  - move=> y Kx; rewrite indicE.
    by case: (y \in A) => /=; rewrite ?(normr1,normr0,lexx,lee01).
by rewrite integral_cst//= ?mul1e; [exact: compact_finite_measure|
                                    exact: compact_measurable].
Qed.

Lemma locally_integrableS (A B : set R) f :
  measurable A -> measurable B -> A `<=` B ->
  locally_integrable setT (f \_ B) -> locally_integrable setT (f \_ A).
Proof.
move=> mA mB AB [mfB oT ifB].
have ? : measurable_fun [set: R] (f \_ A).
  apply/(measurable_restrictT _ _).1 => //; apply: (measurable_funS _ AB) => //.
  exact/(measurable_restrictT _ _).2.
split => // K KT cK; apply: le_lt_trans (ifB _ KT cK).
apply: ge0_le_integral => //=; first exact: compact_measurable.
- apply/measurable_EFinP; apply/measurableT_comp => //.
  exact/measurable_funTS.
- apply/measurable_EFinP; apply/measurableT_comp => //.
  exact/measurable_funTS.
- move=> x Kx; rewrite lee_fin !patchE.
  case: ifPn => xA; case: ifPn => xB //; last by rewrite normr0.
  move: AB => /(_ x).
  by move/set_mem : xA => /[swap] /[apply] /mem_set; rewrite (negbTE xB).
Qed.

Lemma integrable_locally_restrict f (A : set R) : measurable A ->
  mu.-integrable A (EFin \o f) -> locally_integrable [set: R] (f \_ A).
Proof.
move=> mA intf; split.
- move/integrableP : intf => [mf _].
  by apply/(measurable_restrictT _ _).1 => //; exact/measurable_EFinP.
- exact: openT.
- move=> K _ cK.
  move/integrableP : intf => [mf].
  rewrite integral_mkcond/=.
  under eq_integral do rewrite restrict_EFin restrict_normr.
  apply: le_lt_trans.
  apply: ge0_subset_integral => //=; first exact: compact_measurable.
  apply/measurable_EFinP/measurableT_comp/measurable_EFinP => //=.
  move/(measurable_restrictT _ _).1 : mf => /=.
  by rewrite restrict_EFin; exact.
Qed.

End locally_integrable.

Section iavg.
Context {R : realType}.
Implicit Types (D A : set R) (f g : R -> R).
Local Open Scope ereal_scope.

Local Notation mu := lebesgue_measure.

Definition iavg f A := (mu A)^-1 * \int[mu]_(y in A) `| (f y)%:E |.

Lemma iavg0 f : iavg f set0 = 0.
Proof. by rewrite /iavg integral_set0 mule0. Qed.

Lemma iavg_ge0 f A : 0 <= iavg f A.
Proof. by rewrite /iavg mule_ge0 ?integral_ge0// inve_ge0. Qed.

Lemma iavg_restrict f D A : measurable D -> measurable A ->
  iavg (f \_ D) A = (mu A)^-1 * \int[mu]_(y in D `&` A) `|f y|%:E.
Proof.
move=> mD mA; rewrite /iavg setIC [in RHS]integral_mkcondr/=; congr *%E.
apply: eq_integral => /= y yx1.
by rewrite [in RHS]restrict_EFin/= restrict_normr.
Qed.

Lemma iavgD f g A : measurable A -> mu A < +oo ->
  measurable_fun A f -> measurable_fun A g ->
  iavg (f \+ g)%R A <= iavg f A + iavg g A.
Proof.
move=> mA Aoo mf mg; have [r0|r0] := eqVneq (mu A) 0.
  rewrite /iavg integral_abs_eq0//= ?mule0; last first.
    exact/measurable_EFinP/measurable_funD.
  rewrite (@integral_abs_eq0 _ _ _ mu _ (EFin \o f))//= ?mule0; last first.
    exact/measurable_EFinP.
  rewrite (@integral_abs_eq0 _ _ _ mu _ (EFin \o g))//= ?mule0 ?adde0//.
  exact: measurableT_comp.
rewrite -muleDr//=; last 2 first.
  by rewrite fin_numV// -ltNye// (@lt_le_trans _ _ 0).
  by rewrite ge0_adde_def// inE integral_ge0.
rewrite lee_pmul2l//; last 2 first.
  by rewrite fin_numV// -ltNye// (@lt_le_trans _ _ 0).
  by rewrite inve_gt0 -?ltey// measure_gt0.
rewrite -ge0_integralD//=; [|by do 2 apply: measurableT_comp..].
apply: ge0_le_integral => //=.
- by do 2 apply: measurableT_comp => //; exact: measurable_funD.
- by apply: measurableT_comp => //; apply: measurable_funD => //;
    exact: measurableT_comp.
- by move=> /= x _; exact: ler_normD.
Qed.

End iavg.

Section hardy_littlewood.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Types (D : set R) (f : R -> R).
Local Open Scope ereal_scope.

Definition HL_maximal f (x : R) : \bar R :=
  ereal_sup [set iavg f (ball x r) | r in `]0, +oo[%classic%R].

Local Notation HL := HL_maximal.

Lemma HL_maximal_ge0 f D : locally_integrable D f ->
  forall x, 0 <= HL (f \_ D) x.
Proof.
move=> Df x; apply: le_ereal_sup_tmp => //=.
pose k := \int[mu]_(x in D `&` ball x 1) `|f x|%:E.
exists ((mu (ball x 1))^-1 * k); last first.
  by rewrite mule_ge0 ?inve_ge0// integral_ge0.
exists 1%R; first by rewrite in_itv/= ltr01.
rewrite iavg_restrict//; last exact: measurable_ball.
by case: Df => _ /open_measurable.
Qed.

Lemma HL_maximalT_ge0 f : locally_integrable setT f -> forall x, 0 <= HL f x.
Proof. by move=> + x => /HL_maximal_ge0 /(_ x); rewrite patch_setT. Qed.

Let locally_integrable_ltbally (f : R -> R) (x r : R) :
  locally_integrable setT f -> \int[mu]_(y in ball x r) `|(f y)%:E| < +oo.
Proof.
move=> [mf _ locf]; have [r0|r0] := leP r 0%R.
  by rewrite (ball0 _ _).2// integral_set0.
rewrite (le_lt_trans _ (locf (closed_ball x r) _ (closed_ballR_compact _)))//.
apply: ge0_subset_integral => //; first exact: measurable_ball.
- by apply: measurable_closed_ball; exact/ltW.
- apply: measurable_funTS; apply/measurableT_comp => //=.
  exact: measurableT_comp.
- exact: subset_closed_ball.
Qed.

Lemma lower_semicontinuous_HL_maximal f :
  locally_integrable setT f -> lower_semicontinuous (HL f).
Proof.
move=> [mf ? locf]; apply/lower_semicontinuousP => a.
have [a0|a0] := lerP 0 a; last first.
  rewrite [X in open X](_ : _ = setT); first exact: openT.
  by apply/seteqP; split=> // x _; exact: (lt_le_trans _ (HL_maximalT_ge0 _ _)).
rewrite openE /= => x /= /ereal_sup_gt[_ [r r0] <-] afxr.
rewrite /= in_itv /= andbT in r0.
rewrite /iavg in afxr; set k := \int[_]_(_ in _) _ in afxr.
apply: nbhs_singleton; apply: nbhs_interior; rewrite nbhsE /=.
have k_gt0 : 0 < k.
  rewrite lt0e integral_ge0// andbT; apply/negP => /eqP k0.
  by move: afxr; rewrite k0 mule0 lte_fin ltNge a0.
move: a0; rewrite le_eqVlt => /predU1P[a0|a0].
  move: afxr; rewrite -{a}a0 => xrk.
  near (0%R : R)^'+ => d.
  have xrdk : 0 < (mu (ball x (r + d)))^-1 * k.
    rewrite mule_gt0// lebesgue_measure_ball; last by rewrite addr_ge0// ltW.
    rewrite inver mulrn_eq0/= gt_eqF; last by rewrite addr_gt0.
    by rewrite lte_fin// invr_gt0// pmulrn_lgt0// addr_gt0.
  exists (ball x d); first by split; [exact: ball_open|exact: ballxx].
  move=> y; rewrite /ball/= => xyd.
  have ? : ball x r `<=` ball y (r + d).
    move=> /= z; rewrite /ball/= => xzr; rewrite -(subrK x y) -(addrA (y - x)%R).
    by rewrite (le_lt_trans (ler_normD _ _))// [ltLHS]addrC ltrD// distrC.
  have ? : k <= \int[mu]_(y in ball y (r + d)) `|(f y)%:E|.
    apply: ge0_subset_integral =>//; [exact:measurable_ball|
                                      exact:measurable_ball|].
    exact/measurable_funTS/measurableT_comp/measurableT_comp.
  have : iavg f (ball y (r + d)) <= HL f y.
    apply: ereal_sup_ubound => /=; exists (r + d)%R => //.
    by rewrite in_itv/= andbT addr_gt0.
  apply/lt_le_trans/(lt_le_trans xrdk); rewrite /iavg.
  do 2 (rewrite lebesgue_measure_ball; last by rewrite addr_ge0// ltW).
  by rewrite lee_wpmul2l// inve_ge0 lee_fin pmulrn_rge0// addr_gt0.
have ka_pos : (fine k / a)%R \is Num.pos.
  by rewrite posrE divr_gt0// fine_gt0 // k_gt0/= locally_integrable_ltbally.
have k_fin_num : k \is a fin_num.
  by rewrite ge0_fin_numE ?locally_integrable_ltbally ?integral_ge0.
have kar : (0 < 2^-1 * (fine k / a) - r)%R.
  move: afxr; rewrite -{1}(fineK k_fin_num) -lte_pdivrMr; last first.
    by rewrite fine_gt0// k_gt0/= ltey_eq k_fin_num.
  rewrite (lebesgue_measure_ball _ (ltW r0))//.
  rewrite -!EFinM inver mulrn_eq0/= gt_eqF// lte_fin -invf_div.
  rewrite ltf_pV2 ?posrE ?pmulrn_lgt0//.
  rewrite /= -[in X in X -> _]mulr_natl -ltr_pdivlMl//.
  by rewrite -[in X in X -> _]subr_gt0.
near (0%R : R)^'+ => d.
have axrdk : a%:E < (mu (ball x (r + d)))^-1 * k.
  rewrite lebesgue_measure_ball//; last by rewrite addr_ge0// ltW.
  rewrite inver mulrn_eq0/= gt_eqF ?addr_gt0//.
  rewrite -(fineK k_fin_num) -lte_pdivrMr; last first.
    by rewrite fine_gt0// k_gt0/= locally_integrable_ltbally.
  rewrite -!EFinM !lte_fin -invf_div ltf_pV2//; last first.
    by rewrite posrE// pmulrn_lgt0// addr_gt0.
  rewrite -mulr_natl -ltr_pdivlMl// -ltrBrDl.
  by near: d; exact: nbhs_right_lt.
exists (ball x d).
  by split; [exact: ball_open|exact: ballxx].
move=> y; rewrite /ball/= => xyd.
have ? : ball x r `<=` ball y (r + d).
  move=> /= z; rewrite /ball/= => xzr; rewrite -(subrK x y) -(addrA (y - x)%R).
  by rewrite (le_lt_trans (ler_normD _ _))// [ltLHS]addrC ltrD// distrC.
have ? : k <= \int[mu]_(z in ball y (r + d)) `|(f z)%:E|.
  apply: ge0_subset_integral => //; [exact: measurable_ball|
                                     exact: measurable_ball|].
  exact/measurable_funTS/measurableT_comp/measurableT_comp.
have afxrdi : a%:E < (mu (ball x (r + d)))^-1 *
    \int[mu]_(z in ball y (r + d)) `|(f z)%:E|.
  by apply/(lt_le_trans axrdk)/lee_wpmul2l => //; rewrite inve_ge0.
have /lt_le_trans : a%:E < iavg f (ball y (r + d)).
  apply: (lt_le_trans afxrdi); rewrite /iavg.
  do 2 (rewrite lebesgue_measure_ball; last by rewrite addr_ge0// ltW).
  by rewrite inver.
apply; apply: ereal_sup_ubound => /=.
by exists (r + d)%R => //; rewrite in_itv/= andbT addr_gt0.
Unshelve. all: by end_near. Qed.

Lemma measurable_HL_maximal f :
  locally_integrable setT f -> measurable_fun setT (HL f).
Proof.
move=> lf; apply: lower_semicontinuous_measurable.
exact: lower_semicontinuous_HL_maximal.
Qed.

Let norm1 D f := \int[mu]_(y in D) `|(f y)%:E|.

Lemma maximal_inequality f c :
  locally_integrable setT f -> (0 < c)%R ->
  mu [set x | HL f x > c%:E] <= (3 / c)%:E * norm1 setT f.
Proof.
move=> /= locf c0.
rewrite lebesgue_regularity_inner_sup//; last first.
  rewrite -[X in measurable X]setTI; apply: emeasurable_fun_o_infty => //.
  exact: measurable_HL_maximal.
apply: ge_ereal_sup => /= x /= [K [cK Kcmf <-{x}]].
have r_proof x : HL f x > c%:E -> {r | (0 < r)%R & iavg f (ball x r) > c%:E}.
  move=> /ereal_sup_gt/cid2[y /= /cid2[r]].
  by rewrite in_itv/= andbT => rg0 <-{y} Hc; exists r.
pose r_ x :=
  if pselect (HL f x > c%:E) is left H then s2val (r_proof _ H) else 1%R.
have r_pos (x : R) : (0 < r_ x)%R.
  by rewrite /r_; case: pselect => //= cMfx; case: (r_proof _ cMfx).
have cMfx_int x : c%:E < HL f x ->
    \int[mu]_(y in ball x (r_ x)) `|(f y)|%:E > c%:E * mu (ball x (r_ x)).
  move=> cMfx; rewrite /r_; case: pselect => //= => {}cMfx.
  case: (r_proof _ cMfx) => /= r r0.
  rewrite /iavg (lebesgue_measure_ball _ (ltW r0)) inver mulrn_eq0//= gt_eqF//.
  rewrite -(@lte_pmul2r _ (r *+ 2)%:E)//; last by rewrite lte_fin// mulrn_wgt0.
  by rewrite muleAC -[in X in _ < X]EFinM mulVf ?gt_eqF ?mulrn_wgt0// mul1e.
set B := fun r => ball r (r_ r).
have {}Kcmf : K `<=` cover [set i | HL f i > c%:E] (fun i => ball i (r_ i)).
  by move=> r /Kcmf /= cMfr; exists r => //; exact: ballxx.
have {Kcmf}[D Dsub Kcover] : finite_subset_cover [set i | c%:E < HL f i]
    (fun i => ball i (r_ i)) K.
  move: cK; rewrite compact_cover => /(_ _ _ _ _ Kcmf); apply.
  by move=> /= x cMfx; exact/ball_open/r_pos.
have KDB : K `<=` cover [set` D] B.
  by apply: (subset_trans Kcover) => /= x [r Dr] rx; exists r.
have is_ballB i : is_ball (B i) by exact: is_ball_ball.
have Bset0 i : B i !=set0 by exists i; exact: ballxx.
have [E [uE ED tEB DE]] := @vitali_lemma_finite_cover _ _ B is_ballB Bset0 D.
rewrite (@le_trans _ _ (3%:E * \sum_(i <- E) mu (B i)))//.
  have {}DE := subset_trans KDB DE.
  apply: (le_trans (@content_subadditive _ _ _ mu K
      (fun i => 3 *` B (nth 0%R E i)) (size E) _ _ _)) => //.
  - by move=> k ?; rewrite scale_ballE//; exact: measurable_ball.
  - by apply: closed_measurable; apply: compact_closed => //; exact: Rhausdorff.
  - apply: (subset_trans DE); rewrite /cover bigcup_seq.
    by rewrite (big_nth 0%R)//= big_mkord.
  - rewrite ge0_sume_distrr//= (big_nth 0%R) big_mkord; apply: lee_sum => i _.
    rewrite scale_ballE// !lebesgue_measure_ball ?mulr_ge0 ?(ltW (r_pos _))//.
    by rewrite -mulrnAr EFinM.
rewrite !EFinM -muleA lee_wpmul2l//=.
apply: (@le_trans _ _ (\sum_(i <- E) c^-1%:E * \int[mu]_(y in B i) `|f y|%:E)).
  rewrite [in leLHS]big_seq [in leRHS]big_seq; apply: lee_sum => r /ED /Dsub /[!inE] rD.
  by rewrite -lee_pdivrMl ?invr_gt0// invrK /B/=; exact/ltW/cMfx_int.
rewrite -ge0_sume_distrr; last by move=> x _; rewrite integral_ge0.
rewrite lee_wpmul2l//; first by rewrite lee_fin invr_ge0 ltW.
rewrite -ge0_integral_bigsetU//=.
- apply/ge0_subset_integral => //.
  + by apply/bigsetU_measurable => ? ?; exact: measurable_ball.
  + by apply/measurableT_comp/measurableT_comp; last case: locf.
- by move=> n; exact: measurable_ball.
- apply: measurableT_comp => //; apply: measurable_funTS.
  by apply: measurableT_comp => //; case: locf.
Qed.

End hardy_littlewood.

Section davg.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types f g : R -> R.

Definition davg f x (r : R) := iavg (center (f x) \o f) (ball x r).

Lemma davg0 f x (r : R) : (r <= 0)%R -> davg f x r = 0.
Proof. by move=> r0; rewrite /davg/= (ball0 _ _).2//= iavg0. Qed.

Lemma davg_ge0 f x (r : R) : 0 <= davg f x r. Proof. exact: iavg_ge0. Qed.

Lemma davgD f g (x r : R) :
  measurable_fun (ball x r) f -> measurable_fun (ball x r) g ->
  davg (f \+ g)%R x r <= (davg f x \+ davg g x) r.
Proof.
move=> mf mg; rewrite (le_trans _ (iavgD _ _ _ _)) //.
- rewrite le_eqVlt; apply/orP; left; apply/eqP => /=; congr iavg.
  by apply/funext => e /=; rewrite opprD addrACA.
- exact: measurable_ball.
- have [r0|r0] := leP r 0%R; first by rewrite (ball0 _ _).2// measure0.
  by rewrite (lebesgue_measure_ball _ (ltW r0)) ltry.
- exact: measurable_funB.
- exact: measurable_funB.
Qed.

Lemma near_davg f (a : itv_bound R) x (u : R) : (x < u)%R -> (a < BRight x)%E ->
  \forall r \near 0^'+,
    davg f x r = davg (f \_ [set` Interval a (BRight u)]) x r.
Proof.
move=> xu; move: a => [b a /=|[_|//]].
- move=> ax; near=> r.
  have fauf : {in ball x r : set R,
      f \_ [set` Interval (BSide b a) (BRight u)] =1 f}.
    move=> y.
    rewrite ball_itv/= inE/= => yxr; rewrite patchE/= mem_set//=.
    apply: subset_itvW yxr.
      rewrite lerBrDl -lerBrDr.
      by near: r; apply: nbhs_right_ltW; rewrite subr_gt0.
    rewrite -lerBrDl.
    by near: r; apply: nbhs_right_le; rewrite subr_gt0.
  congr *%E; apply: eq_integral => y yxr /=.
  by rewrite fauf// fauf// inE; exact: ballxx.
- near=> r.
  have foouf : {in (ball x r : set R), f \_ `]-oo, u] =1 f}.
    move=> y.
    rewrite ball_itv/= inE/= => yxr; rewrite patchE/= mem_set//=.
    move: yxr; rewrite !in_itv/= => /andP[_ /ltW/le_trans]; apply.
    rewrite -lerBrDl.
    by near: r; apply: nbhs_right_ltW; rewrite subr_gt0.
  congr *%E; apply: eq_integral => y yxr /=.
  by rewrite foouf// foouf// inE; exact: ballxx.
Unshelve. all: by end_near. Qed.

Section continuous_cvg_davg.
Context f (x : R) (U : set R).
Hypotheses (xU : open_nbhs x U) (mU : measurable U) (mUf : measurable_fun U f)
           (fx : {for x, continuous f}).

Let continuous_integralB_fin_num :
  \forall t \near 0%R,
    \int[mu]_(y in ball x t) `|(f y)%:E - (f x)%:E| \is a fin_num.
Proof.
move: fx => /cvgrPdist_le /= fx'.
near (0%R:R)^'+ => e.
have e0 : (0 < e)%R by near: e; exact: nbhs_right_gt.
have [r /= r0 {}fx'] := fx' _ e0.
have [d/= d0 dxU] := open_subball xU.1 xU.2.
near=> t; rewrite ge0_fin_numE ?integral_ge0//.
have [t0|t0] := leP t 0%R; first by rewrite ((ball0 _ _).2 t0) integral_set0.
have xtU : ball x t `<=` U by apply: dxU => //=.
rewrite (@le_lt_trans _ _ (\int[mu]_(y in ball x t) e%:E))//; last first.
  rewrite integral_cst//=; last exact: measurable_ball.
  by rewrite (lebesgue_measure_ball _ (ltW t0)) ltry.
apply: ge0_le_integral => //=; first exact: measurable_ball.
- by do 2 apply: measurableT_comp => //=; apply: measurable_funB;
    [exact: measurable_funS mUf|exact: measurable_cst].
- move=> y xry; rewrite lee_fin distrC fx'//=; apply: (lt_le_trans xry).
  by near: t; exact: nbhs0_ltW.
Unshelve. all: by end_near. Qed.

Let continuous_davg_fin_num :
  \forall A \near 0%R, davg f x A \is a fin_num.
Proof.
have [e /= e0 exf] := continuous_integralB_fin_num.
move: fx => /cvgrPdist_le fx'.
near (0%R:R)^'+ => r.
have r0 : (0 < r)%R by near: r; exact: nbhs_right_gt.
have [d /= d0 {}fx'] := fx' _ e0.
near=> t; have [t0|t0] := leP t 0%R; first by rewrite davg0.
rewrite fin_numM ?exf//=.
by rewrite (lebesgue_measure_ball _ (ltW _))// inver mulrn_eq0/= gt_eqF.
Unshelve. all: by end_near. Qed.

Lemma continuous_cvg_davg : davg f x r @[r --> 0%R] --> 0.
Proof.
apply/fine_cvgP; split; first exact: continuous_davg_fin_num.
apply/cvgrPdist_le => e e0.
move: fx => /cvgrPdist_le /= fx'.
have [r /= r0 {}fx'] := fx' _ e0.
have [d /= d0 dfx] := continuous_davg_fin_num.
have [l/= l0 lxU] := open_subball xU.1 xU.2.
near=> t.
have [t0|t0] := leP t 0%R; first by rewrite /= davg0//= subrr normr0 ltW.
rewrite sub0r normrN /= ger0_norm; last by rewrite fine_ge0// davg_ge0.
rewrite -lee_fin fineK//; last by rewrite dfx//= sub0r normrN gtr0_norm.
rewrite /davg/= /iavg/= (lebesgue_measure_ball _ (ltW t0))//.
rewrite inver mulrn_eq0/= gt_eqF// lee_pdivrMl//; last by rewrite mulrn_wgt0.
rewrite (@le_trans _ _ (\int[mu]_(y in ball x t) e%:E))//.
  apply: ge0_le_integral => //=.
  - exact: measurable_ball.
  - do 2 apply: measurableT_comp => //=; apply: measurable_funB => //.
    by apply: measurable_funS mUf => //; apply: lxU => //=.
  - move=> y xty; rewrite lee_fin distrC fx'//; apply: (lt_le_trans xty).
    by near: t; exact: nbhs0_ltW.
rewrite integral_cst//=; last exact: measurable_ball.
by rewrite muleC (lebesgue_measure_ball _ (ltW t0)).
Unshelve. all: by end_near. Qed.

End continuous_cvg_davg.

End davg.

Section lim_sup_davg.
Context {R : realType}.
Local Open Scope ereal_scope.
Implicit Types f g : R -> R.

Definition lim_sup_davg f x := lime_sup (davg f x) 0.

Local Notation "f ^*" := (lim_sup_davg f).

Lemma lim_sup_davg_ge0 f x : 0 <= f^* x.
Proof. by apply: limf_esup_ge0 => // => y; exact: iavg_ge0. Qed.

Lemma lim_sup_davg_le f g x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> measurable_fun U g ->
  (f \+ g)%R^* x <= (f^* \+ g^*) x.
Proof.
move=> xU mY mf /= mg; apply: le_trans (lime_supD _); last first.
  by rewrite ge0_adde_def// inE; exact: lim_sup_davg_ge0.
have [e/= e0 exU] := open_subball xU.1 xU.2.
apply: lime_sup_le; near=> r => y; rewrite neq_lt => /orP[y0|y0 ry].
  by rewrite !davg0 ?adde0// ltW.
apply: davgD.
  apply: measurable_funS mf => //; apply: exU => //=.
  by rewrite (lt_le_trans ry)//; near: r; exact: nbhs_right_le.
apply: measurable_funS mg => //; apply: exU => //=.
by rewrite (lt_le_trans ry)//; near: r; exact: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma continuous_lim_sup_davg f x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> {for x, continuous f} ->
  f^* x = 0.
Proof.
move=> xU mU mUf ctsf.
by have /lim_lime_sup := continuous_cvg_davg xU mU mUf ctsf.
Qed.

Lemma lim_sup_davgB f g x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> {for x, continuous g} ->
  locally_integrable [set: R] g -> (f \- g)%R^* x = f^* x.
Proof.
move=> xU mU mUf cg locg; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite [leRHS](_ : _ = f^* x + (\- g)%R^* x).
    apply: (lim_sup_davg_le xU) => //.
    apply/(measurable_comp measurableT) => //.
    by case: locg => + _ _; exact: measurable_funS.
  rewrite (@continuous_lim_sup_davg (- g)%R _ _ xU mU); first by rewrite adde0.
  - apply/(measurable_comp measurableT) => //.
    by case: locg => + _ _; apply: measurable_funS.
  + by move=> y; exact/continuousN/cg.
- rewrite [leRHS](_ : _ = ((f \- g)%R^* \+ g^*) x)//.
    rewrite {1}(_ : f = f \- g + g)%R; last by apply/funext => y; rewrite subrK.
    apply: (lim_sup_davg_le xU mU).
      apply: measurable_funB; [exact: mUf|].
      by case: locg => + _ _; exact: measurable_funS.
    by case: locg => + _ _; exact: measurable_funS.
  rewrite [X in _ + X](@continuous_lim_sup_davg _ _ _ xU mU); [by rewrite adde0| |by[]].
  by case: locg => + _ _; exact: measurable_funS.
Qed.

Local Notation mu := (@lebesgue_measure R).

Let is_cvg_ereal_sup_davg f x :
  cvg (ereal_sup [set davg f x y | y in ball 0%R e `\ 0%R] @[e --> 0^'+]).
Proof.
apply: nondecreasing_at_right_is_cvge; near=> e => y z.
rewrite !in_itv/= => /andP[y0 ye] /andP[z0 ze] yz.
apply: ereal_sup_le => _ /= -[b [yb b0]] <-.
by exists b => //; split => //; exact: le_ball yb.
Unshelve. all: by end_near. Qed.

Lemma lim_sup_davgT_HL_maximal f (x : R) : locally_integrable setT f ->
  f^* x <= HL_maximal f x + `|f x|%:E.
Proof.
move=> [mf _ locf]; rewrite /lim_sup_davg lime_sup_lim; apply: lime_le.
  exact: is_cvg_ereal_sup_davg.
near=> e.
apply: ge_ereal_sup => _ [b [eb] /= b0] <-.
suff : forall r, davg f x r <= HL_maximal f x + `|f x|%:E by exact.
move=> r.
apply: (@le_trans _ _ ((mu (ball x r))^-1 *
    \int[mu]_(y in ball x r) (`|(f y)%:E| + `|(f x)%:E|))).
  - rewrite /davg lee_wpmul2l ?inve_ge0//; apply: ge0_le_integral => //.
    + exact: measurable_ball.
    + do 2 apply: measurableT_comp => //=; apply: measurable_funB => //.
      exact: measurableT_comp.
    + apply: emeasurable_funD => //; do 2 apply: measurableT_comp => //.
      exact: measurable_funS mf.
  by move=> /= y xry; rewrite -EFinD lee_fin// ler_normB.
rewrite [leLHS](_ : _ = (mu (ball x r))^-1 *
  (\int[mu]_(y in ball x r) `|(f y)%:E| +
   \int[mu]_(y in ball x r) `|(f x)%:E|)); last first.
  congr *%E; rewrite ge0_integralD//=; first exact: measurable_ball.
  by do 2 apply: measurableT_comp => //; exact: measurable_funS mf.
have [r0|r0] := lerP r 0.
  rewrite (ball0 _ _).2// !integral_set0 adde0 mule0 adde_ge0//.
  by apply: HL_maximalT_ge0; split => //; exact: openT.
rewrite muleDr//; last 2 first.
  by rewrite (lebesgue_measure_ball _ (ltW r0)) inver mulrn_eq0//= gt_eqF.
  by rewrite ge0_adde_def// inE integral_ge0.
rewrite leeD//.
   by apply: ereal_sup_ubound => /=; exists r => //; rewrite in_itv/= r0.
under eq_integral do rewrite -(mule1 `| _ |).
rewrite ge0_integralZl//; last exact: measurable_ball.
rewrite integral_cst//=; last exact: measurable_ball.
rewrite mul1e (lebesgue_measure_ball _ (ltW r0)).
by rewrite inver mulrn_eq0 ?gt_eqF//= -!EFinM mulrC mulfK// mulrn_eq0/= gt_eqF.
Unshelve. all: by end_near. Qed.

End lim_sup_davg.

Definition lebesgue_pt {R : realType} (f : R -> R) (x : R) :=
  davg f x r @[r --> (0%R:R)^'+] --> 0%E.

Lemma continuous_lebesgue_pt {R : realType} (f : R -> R) x (U : set R) :
  open_nbhs x U -> measurable U -> measurable_fun U f ->
  {for x, continuous f} -> lebesgue_pt f x.
Proof.
move=> xU mU mUf xf; rewrite /lebesgue_pt -[X in _ --> X](@davg0 _ f x 0)//.
apply: cvg_at_right_filter; rewrite davg0//.
exact: (continuous_cvg_davg xU mU mUf).
Qed.

Lemma lebesgue_pt_restrict {R : realType} (f : R -> R) (a : itv_bound R) x u :
  (x < u)%R -> (a < BRight x)%E ->
  lebesgue_pt f x -> lebesgue_pt (f \_ [set` Interval a (BRight u)]) x.
Proof.
by move=> xu ax; apply: cvg_trans; apply: near_eq_cvg; exact: near_davg.
Qed.

Section lebesgue_differentiation.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types f : R -> R.

Local Notation "f ^*" := (lim_sup_davg f).

Let lebesgue_differentiation_suff (E : set R) f :
  (forall a, (0 < a)%R -> mu.-negligible (E `&` [set x | a%:E < f^* x])) ->
  {ae mu, forall x : R, E x -> lebesgue_pt f x}.
Proof.
move=> Ef; have {Ef} : mu.-negligible (E `&` [set x | 0 < f^* x]).
  suff -> : E `&` [set x | 0 < f^* x] =
            E `&` \bigcup_n [set x | n.+1%:R^-1%:E < f^* x].
    rewrite setI_bigcupr;  apply: negligible_bigcup => k/=.
    by apply: Ef; rewrite invr_gt0.
  apply/seteqP; split; last first.
    by move=> r [Er] [k ?] /=; split => //; exact: le_lt_trans q.
  move=> x /= [Ex] fx0; split => //.
  have [fxoo|fxoo] := eqVneq (f^* x) +oo.
    by exists 1%N => //=; rewrite fxoo ltry.
  near \oo => m; exists m => //=.
  rewrite -(@fineK _ (f^* x)) ?gt0_fin_numE ?ltey// lte_fin.
  rewrite invf_plt ?posrE//; last by rewrite fine_gt0// ltey fx0.
  set r := _^-1%R; rewrite (lt_le_trans (truncnS_gt _))//.
  by rewrite ler_nat ltnS; near: m; exact: nbhs_infty_ge.
apply: negligibleS => z /= /not_implyP[Ez H]; split => //.
rewrite ltNge; apply: contra_notN H.
rewrite le_eqVlt ltNge limf_esup_ge0/= ?orbF//; last first.
  by move=> x; exact: iavg_ge0.
move=> /eqP fz0.
suff: lime_inf (davg f z) 0 = 0 by exact: lime_sup_inf_at_right.
apply/eqP; rewrite eq_le -[X in _ <= X <= _]fz0 lime_inf_sup/= fz0.
by apply: lime_inf_ge0 => x; exact: iavg_ge0.
Unshelve. all: by end_near. Qed.

Let lebesgue_differentiation_bounded f :
  let B k : set R^o := ball 0%R k.+1.*2%:R in
  let f_ k := f \_ (B k) in
  (forall k, mu.-integrable setT (EFin \o f_ k)) ->
  forall k, {ae mu, forall x, B k x -> lebesgue_pt (f_ k) x}.
Proof.
move=> B f_ intf_ k; apply: lebesgue_differentiation_suff => e e0.
have mE : measurable (B k) by exact: measurable_ball.
have ex_g_ : exists g_ : (R -> R)^nat,
  [/\ (forall n, continuous (g_ n)),
      (forall n, mu.-integrable (B k) (EFin \o g_ n)) &
      \int[mu]_(z in B k) `|f_ k z - g_ n z|%:E @[n --> \oo] --> 0 ].
  apply: approximation_continuous_integrable => //=.
    by rewrite lebesgue_measure_ball//= ltry.
  exact: integrableS (intf_ _).
have {ex_g_} ex_gn n : exists gn : R -> R,
    [/\ continuous gn,
        mu.-integrable (B k) (EFin \o gn) &
        \int[mu]_(z in B k) `|f_ k z - gn z|%:E <= n.+1%:R^-1%:E].
  case: ex_g_ => g_ [cg intg] /fine_cvgP[] [m _ fgfin] /cvgrPdist_le.
  move=> /(_ n.+1%:R^-1%R ltac:(by []))[p _] /(_ _ (leq_addr m p)).
  rewrite sub0r normrN -lee_fin => /= fg0.
  exists (g_ (p + m)%N); split => //.
  rewrite (le_trans _ fg0)// ger0_norm ?fine_ge0 ?integral_ge0// fineK//.
  by rewrite fgfin//= leq_addl.
pose g_ n : R -> R := sval (cid (ex_gn n)).
have cg_ n : continuous (g_ n) by rewrite /g_ /sval /=; case: cid => // x [].
have intg n : mu.-integrable (B k) (EFin \o g_ n).
  by rewrite /g_ /sval /=; case: cid => // x [].
have ifg_ub n : \int[mu]_(z in B k) `|f_ k z - g_ n z|%:E <= n.+1%:R^-1%:E.
  by rewrite /g_ /sval /=; case: cid => // x [].
pose g_B n := g_ n \_ (B k).
have cg_B n : {in B k, continuous (g_B n)}.
  move=> x xBk; rewrite /g_B patch_indic/=.
  by apply: cvgM => //; [exact: cg_|exact: cvg_indic].
pose f_g_Be n : set _ := [set x | `| (f_ k \- g_B n) x |%:E >= (e / 2)%:E].
pose HLf_g_Be n : set _ :=
  [set x | HL_maximal (f_ k \- g_B n)%R x > (e / 2)%:E].
pose Ee := \bigcap_n (B k `&` (HLf_g_Be n `|` f_g_Be n)).
case/integrableP: (intf_ k) => mf intf.
have mfg n : measurable_fun setT (f_ k \- g_ n)%R.
  apply: measurable_funB; first by move/measurable_EFinP : mf.
  by apply: continuous_measurable_fun; exact: cg_.
have locg_B n : locally_integrable [set: R] (g_B n).
  split; [|exact: openT|].
  - apply/(measurable_restrictT _ _).1 => //.
    exact: measurable_funS (continuous_measurable_fun (cg_ n)).
  - move=> K _ cK.
    rewrite (@le_lt_trans _ _ (\int[mu]_(x in K) `|g_ n x|%:E))//; last first.
      have : {within K, continuous (g_ n)} by apply: continuous_subspaceT.
      by move/(continuous_compact_integrable cK) => /integrableP[_ /=].
    apply: ge0_le_integral => //=.
    + exact: compact_measurable.
    + do 2 apply: measurableT_comp => //; apply/measurable_restrict => //.
        exact: compact_measurable.
      exact: measurable_funS (continuous_measurable_fun (cg_ n)).
    + do 2 apply: measurableT_comp => //; apply: measurable_funTS.
      exact: continuous_measurable_fun.
    + move=> /= x Kx; rewrite /g_B patchE; case: ifPn => //=.
      by rewrite normr0 lee_fin.
have locf_g_B n : locally_integrable setT (f_ k \- g_B n)%R.
  apply: locally_integrableB => //; split.
  - by move/measurable_EFinP : mf.
  - exact: openT.
  - move=> K _ cK; rewrite (le_lt_trans _ intf)//=.
    apply: ge0_subset_integral => //.
    + exact: compact_measurable.
    + by do 2 apply: measurableT_comp => //; move/measurable_EFinP : mf.
have mEHL i : measurable (HLf_g_Be i).
  rewrite /HLf_g_Be -[X in measurable X]setTI.
  apply: emeasurable_fun_o_infty => //.
  by apply: measurable_HL_maximal; exact: locf_g_B.
have mfge i : measurable (f_g_Be i).
  rewrite /f_g_Be -[X in measurable X]setTI.
  apply: emeasurable_fun_c_infty => //.
  by do 2 apply: measurableT_comp => //; case: (locf_g_B i).
have mEe : measurable Ee.
  apply: bigcapT_measurable => i.
  by apply: measurableI; [exact: measurable_ball|exact: measurableU].
have davgfEe : B k `&` [set x | (f_ k)^* x > e%:E] `<=` Ee.
  suff: forall n, B k `&` [set x | e%:E < (f_ k)^* x] `<=`
                  B k `&` (HLf_g_Be n `|` f_g_Be n).
    by move=> suf r /= /suf hr n _; exact: hr.
  move=> n; rewrite [X in X `<=`_](_ : _ =
      B k `&` [set x | e%:E < (f_ k \- g_B n)%R^* x]); last first.
    apply/seteqP; split => [x [Ex] /=|x [Ex] /=].
      rewrite (@lim_sup_davgB _ _ _ _ (B k))//.
      by split; [exact: ball_open|exact: Ex].
      by move/measurable_EFinP : mf; apply: measurable_funS.
      by apply: cg_B; rewrite inE.
    rewrite (@lim_sup_davgB _ _ _ _ (B k))//.
    by split; [exact: ball_open|exact: Ex].
    by move/measurable_EFinP : mf; apply: measurable_funS.
    by apply: cg_B; rewrite inE.
  move=> r /= [Er] efgnr; split => //.
  have {}efgnr := lt_le_trans efgnr (lim_sup_davgT_HL_maximal r (locf_g_B n)).
  have [|h] := ltP (e / 2)%:E (HL_maximal (f_ k \- g_B n)%R r); first by left.
  right; move: efgnr.
  rewrite {1}(splitr e) EFinD -lteBrDl// => /ltW/le_trans; apply.
  by rewrite leeBlDl// leeD.
suff: mu Ee = 0 by exists Ee.
have HL_null n : mu (HLf_g_Be n) <= (3 / (e / 2))%:E * n.+1%:R^-1%:E.
  rewrite (le_trans (maximal_inequality _ _ )) ?divr_gt0//.
  rewrite lee_pmul2l ?lte_fin ?divr_gt0//.
  set h := (fun x => `|(f_ k \- g_ n) x|%:E) \_ (B k).
  rewrite (@eq_integral _ _ _ mu setT h)//=.
    by rewrite -integral_mkcond/=; exact: ifg_ub.
  move=> x _; rewrite /h restrict_EFin restrict_normr/= /g_B /f_ !patchE.
  by case: ifPn => /=; [rewrite patchE => ->|rewrite subrr].
have fgn_null n : mu [set x | `|(f_ k \- g_B n) x|%:E >= (e / 2)%:E] <=
                     (e / 2)^-1%:E * n.+1%:R^-1%:E.
  rewrite lee_pdivlMl ?invr_gt0 ?divr_gt0// -[X in mu X]setTI.
  apply: le_trans.
    apply: (@le_integral_comp_abse _ _ _ mu _ measurableT
        (EFin \o (f_ k \- g_B n)%R) (e / 2)%R id) => //=.
      by apply: measurableT_comp => //; case: (locf_g_B n).
    by rewrite divr_gt0.
  set h := (fun x => `|(f_ k \- g_ n) x|%:E) \_ (B k).
  rewrite (@eq_integral _ _ _ mu setT h)//=.
    by rewrite -integral_mkcond/=; exact: ifg_ub.
  move=> x _; rewrite /h restrict_EFin restrict_normr/= /g_B /f_ !patchE.
  by case: ifPn => /=; [rewrite patchE => ->|rewrite subrr].
apply/eqP; rewrite eq_le measure_ge0 andbT.
apply/lee_addgt0Pr => r r0; rewrite add0e.
have incl n : Ee `<=` B k `&` (HLf_g_Be n `|` f_g_Be n) by move=> ?; apply.
near \oo => n.
rewrite (@le_trans _ _ (mu (B k `&` (HLf_g_Be n `|` f_g_Be n))))//.
  rewrite le_measure// inE//; apply: measurableI; first exact: measurable_ball.
  by apply: measurableU => //; [exact: mEHL|exact: mfge].
rewrite (@le_trans _ _ ((4 / (e / 2))%:E * n.+1%:R^-1%:E))//.
  rewrite (@le_trans _ _ (mu (HLf_g_Be n `|` f_g_Be n)))//.
    rewrite le_measure// inE//.
      apply: measurableI => //.
      by apply: measurableU => //; [exact: mEHL|exact: mfge].
    by apply: measurableU => //; [exact: mEHL|exact: mfge].
  rewrite (le_trans (measureU2 _ _ _))//=; [exact: mEHL|exact: mfge|].
  apply: le_trans; first by apply: leeD; [exact: HL_null|exact: fgn_null].
  rewrite -muleDl// lee_pmul2r// -EFinD lee_fin -{2}(mul1r (_^-1)%R).
  by rewrite -mulrDl natr1.
rewrite -lee_pdivlMl ?divr_gt0// -EFinM lee_fin -(@invrK _ r).
rewrite -invfM lef_pV2 ?posrE ?divr_gt0// -(@natr1 _ n) -lerBlDr.
by near: n; exact: nbhs_infty_ger.
Unshelve. all: by end_near. Qed.

Lemma lebesgue_differentiation f : locally_integrable setT f ->
  {ae mu, forall x, lebesgue_pt f x}.
Proof.
move=> locf.
pose B k : set R^o := ball 0%R (k.+1.*2)%:R.
pose fk k := f \_ (B k).
have mfk k : mu.-integrable setT (EFin \o fk k).
  case: locf => mf _ intf.
  apply/integrableP; split => /=.
    by apply/measurable_EFinP/(measurable_restrictT _ _).1 => //=;
      [exact: measurable_ball|exact: measurable_funS mf].
  rewrite (_ : (fun x => _) = (EFin \o normr \o f) \_ (B k)); last first.
    by apply/funext => x; rewrite restrict_EFin/= restrict_normr.
  rewrite -integral_mkcond/= -ge0_integral_closed_ball//.
    by rewrite intf//; exact: closed_ballR_compact.
  by apply: measurable_funTS; do 2 apply: measurableT_comp.
have suf k : {ae mu, forall x, B k x -> lebesgue_pt (fk k) x}.
  exact: lebesgue_differentiation_bounded.
pose E k : set _ := sval (cid (suf k)).
rewrite /= in E.
have HE k : mu (E k) = 0 /\ ~` [set x | B k x -> lebesgue_pt (fk k) x] `<=` E k.
  by rewrite /E /sval; case: cid => // A [].
suff: ~` [set x | lebesgue_pt f x] `<=`
      \bigcup_k (~` [set x | B k x -> lebesgue_pt (fk k) x]).
  move/(@negligibleS _ _ _ mu); apply => /=.
  by apply: negligible_bigcup => k /=; exact: suf.
move=> x /= fx; rewrite -setC_bigcap => h; apply: fx.
have fE y k r : (ball 0%R k.+1%:R) y -> (r < 1)%R ->
    forall t, ball y r t -> f t = fk k t.
  rewrite /ball/= sub0r normrN => yk1 r1 t.
  rewrite ltr_distlC => /andP[xrt txr].
  rewrite /fk patchE mem_set// /B /ball/= sub0r normrN.
  have [t0|t0] := ger0P.
    rewrite (lt_le_trans txr)// -lerBrDr.
    rewrite (le_trans (ler_norm _))// (le_trans (ltW yk1))//.
    by rewrite lerBrDr -addnn natrD lerD2 (le_trans (ltW r1))// ler1n.
  rewrite -opprB ltrNl in xrt.
  rewrite (lt_le_trans xrt)// lerBlDl (le_trans (ltW r1))//.
  rewrite -lerBlDl addrC -lerBrDr (le_trans (ler_norm _))// normrN.
  by rewrite (le_trans (ltW yk1))// lerBrDr natr1 ler_nat -muln2 ltn_Pmulr.
have := h `|ceil x|.+1%N Logic.I.
have Bxx : B `|ceil x|.+1 x.
  rewrite /B /ball/= sub0r normrN (le_lt_trans (unstable.abs_ceil_ge _))// ltr_nat.
  by rewrite -addnn addSnnS ltn_addl.
move=> /(_ Bxx)/fine_cvgP[davg_fk_fin_num davg_fk0].
have f_fk_ceil : \forall t \near 0^'+,
  \int[mu]_(y in ball x t) `|(f y)%:E - (f x)%:E| =
  \int[mu]_(y in ball x t) `|fk `|ceil x|.+1 y - fk `|ceil x|.+1 x|%:E.
  near=> t.
  apply: eq_integral => /= y /[1!inE] xty.
  rewrite -(fE x _ t)//; last first.
    by rewrite /ball/= sub0r normrN (le_lt_trans (unstable.abs_ceil_ge _))// ltr_nat.
  rewrite -(fE x _ t)//; last first.
    by apply: ballxx; near: t; exact: nbhs_right_gt.
  by rewrite /ball/= sub0r normrN (le_lt_trans (unstable.abs_ceil_ge _))// ltr_nat.
apply/fine_cvgP; split=> [{davg_fk0}|{davg_fk_fin_num}].
- move: davg_fk_fin_num => -[M /= M0] davg_fk_fin_num.
  apply: filter_app f_fk_ceil; near=> t => Ht.
  by rewrite /davg /iavg Ht davg_fk_fin_num//= sub0r normrN gtr0_norm.
- move/cvgrPdist_le in davg_fk0; apply/cvgrPdist_le => e e0.
  have [M /= M0 {}davg_fk0] := davg_fk0 _ e0.
  apply: filter_app f_fk_ceil; near=> t; move=> Ht.
  by rewrite /davg /iavg Ht// davg_fk0//= sub0r normrN gtr0_norm.
Unshelve. all: by end_near. Qed.

End lebesgue_differentiation.

Section density.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.

Lemma lebesgue_density (A : set R) : measurable A ->
  {ae mu, forall x, mu (A `&` ball x r) * (mu (ball x r))^-1
                      @[r --> 0^'+] --> (\1_A x)%:E}.
Proof.
move=> mA; have := lebesgue_differentiation (locally_integrable_indic openT mA).
apply: filter_app; first exact: (ae_filter_ringOfSetsType mu).
apply: aeW => /= x Ax.
apply: (sube_cvg0 _ _).1 => //.
move: Ax; rewrite /lebesgue_pt /davg /= -/mu => Ax.
have : (mu (ball x r))^-1 *
       `|\int[mu]_(y in ball x r) (\1_A y - \1_A x)%:E | @[r --> 0^'+] --> 0.
  apply: (@squeeze_cvge _ _ _ R (cst 0) _ _ _ _ _ Ax) => //; [|exact: cvg_cst].
  near=> a; rewrite mule_ge0 ?inve_ge0///= lee_pmul2l//; last 2 first.
    by rewrite lebesgue_measure_ball// fin_numV// eqe mulrn_eq0/= gt_eqF.
    rewrite lebesgue_measure_ball// inver mulrn_eq0/= gt_eqF// lte_fin.
    by rewrite invr_gt0// mulrn_wgt0.
  apply: le_abse_integral => //; first exact: measurable_ball.
  exact/measurable_EFinP/measurable_funB.
set f := (f in f r @[r --> 0^'+] --> _ -> _).
rewrite (_ : f = fun r => (mu (ball x r))^-1 *
   `|mu (A `&` ball x r) - (\1_A x)%:E * mu (ball x r)|); last first.
  apply/funext => r; rewrite /f integralB_EFin//=; last 3 first.
    - exact: measurable_ball.
    - apply/integrableP; split.
        exact/measurable_EFinP/measurable_indic.
      under eq_integral do rewrite /= ger0_norm//=.
      rewrite integral_indic//=; last exact: measurable_ball.
      rewrite -/mu (@le_lt_trans _ _ (mu (ball x r)))// ?le_measure// ?inE.
      + by apply: measurableI => //; exact: measurable_ball.
      + exact: measurable_ball.
      + have [r0|r0] := ltP r 0%R.
          by rewrite ((ball0 _ _).2 (ltW r0))// /mu measure0.
        by rewrite lebesgue_measure_ball//= ?ltry.
    - apply/integrableP; split; first exact/measurable_EFinP/measurable_cst.
      rewrite /= integral_cst//=; last exact: measurable_ball.
      have [r0|r0] := ltP r 0%R.
        by rewrite ((ball0 _ _).2 (ltW r0))// /mu measure0 mule0.
      by rewrite lebesgue_measure_ball//= ?ltry.
  rewrite integral_indic//=; last exact: measurable_ball.
  by rewrite -/mu integral_cst//; exact: measurable_ball.
rewrite indicE; have [xA xrA0|xA] := boolP (x \in A); last first.
  apply: iffRL; apply/propeqP; apply: eq_cvg => r.
  by rewrite -mulNrn mulr0n adde0 mul0e sube0 gee0_abs// muleC.
have {xrA0} /cvgeN : (mu (ball x r))^-1 *
    (mu (ball x r) - mu (A `&` ball x r)) @[r --> 0^'+] --> 0.
  move: xrA0; apply: cvg_trans; apply: near_eq_cvg; near=> r.
  rewrite mul1e lee0_abs; last first.
    rewrite sube_le0 le_measure// ?inE/=; last exact: measurable_ball.
    by apply: measurableI => //; exact: measurable_ball.
  rewrite oppeB//; first by rewrite addeC.
  rewrite fin_num_adde_defl// fin_numN ge0_fin_numE//.
  by rewrite lebesgue_measure_ball// ltry.
rewrite oppe0; apply: cvg_trans; apply: near_eq_cvg; near=> r.
rewrite -mulNrn mulr1n muleBr//; last 2 first.
  by rewrite lebesgue_measure_ball// inver mulrn_eq0//= gt_eqF.
  by rewrite fin_num_adde_defr// ge0_fin_numE// lebesgue_measure_ball//= ?ltry.
rewrite (_ : (mu (ball x r))^-1 * mu (ball x r) = 1); last first.
  rewrite lebesgue_measure_ball// inver mulrn_eq0//= gt_eqF//.
  by rewrite -EFinM mulVf// mulrn_eq0/= gt_eqF.
by rewrite oppeB// addeC EFinN muleC.
Unshelve. all: by end_near. Qed.

End density.

Section nicely_shrinking.
Context {R : realType}.
Implicit Types (x : R) (E : (set R)^nat).
Local Notation mu := lebesgue_measure.

Definition nicely_shrinking x E :=
  (forall n, measurable (E n)) /\
  exists Cr : R * {posnum R}^nat, [/\ Cr.1 > 0,
    (Cr.2 n)%:num @[n --> \oo] --> 0,
    (forall n, E n `<=` ball x (Cr.2 n)%:num) &
    (forall n, mu (ball x (Cr.2 n)%:num) <= Cr.1%:E * mu (E n))%E].

Lemma nicely_shrinking_gt0 x E : nicely_shrinking x E ->
  forall n, (0 < mu (E n))%E.
Proof.
move=> [mE [[C r_]]] [/= C_gt0 _ _ + ] n => /(_ n).
rewrite lebesgue_measure_ball// -lee_pdivrMl//.
apply: lt_le_trans.
by rewrite mule_gt0// lte_fin invr_gt0.
Qed.

Lemma nicely_shrinking_lty x E : nicely_shrinking x E ->
  forall n, (mu (E n) < +oo)%E.
Proof.
move=> [mE [[C r_]]] [/= C_gt0 _ + _] n => /(_ n) Er_.
rewrite (@le_lt_trans _ _ (lebesgue_measure (ball x (r_ n)%:num)))//.
  by rewrite le_measure// inE; [exact: mE|exact: measurable_ball].
by rewrite lebesgue_measure_ball// ltry.
Qed.

Lemma nicely_shrinking_fin_num x E : nicely_shrinking x E ->
  forall n, mu (E n) \is a fin_num.
Proof. by move=> xE n; rewrite ge0_fin_numE// (nicely_shrinking_lty xE). Qed.

End nicely_shrinking.

Section nice_lebesgue_differentiation.
Local Open Scope ereal_scope.
Context {R : realType}.
Variable E : R -> (set R)^nat.
Hypothesis hE : forall x, nicely_shrinking x (E x).
Local Notation mu := lebesgue_measure.


Lemma nice_lebesgue_differentiation (f : R -> R) :
  locally_integrable setT f -> forall x, lebesgue_pt f x ->
  (mu (E x n))^-1 * \int[mu]_(y in E x n) (f y)%:E
    @[n --> \oo] --> (f x)%:E.
Proof.
move=> locf x fx; apply: (sube_cvg0 _ _).1 => //=; apply/cvg_abse0P.
pose r_ x : {posnum R} ^nat := (sval (cid (hE x).2)).2.
pose C := (sval (cid (hE x).2)).1.
have C_gt0 : (0 < C)%R by rewrite /C /sval/=; case: cid => -[? ?] [].
have r_0 y : (r_ y n)%:num @[n --> \oo] --> (0%R : R).
  by rewrite /r_ /sval/=; case: cid => -[? ?] [].
have E_r_ n : E x n `<=` ball x (r_ x n)%:num.
  by rewrite /r_ /sval/=; case: cid => -[? ?] [].
have muEr_ n : mu (ball x (r_ x n)%:num) <= C%:E * mu (E x n).
  by rewrite /C /r_ /sval/=; case: cid => -[? ?] [].
apply: (@squeeze_cvge _ _ _ _ (cst 0) _
  (fun n => C%:E * davg f x (r_ x n)%:num)); last 2 first.
  exact: cvg_cst.
  move/cvge_at_rightP: fx => /(_ (fun r => (r_ x r)%:num)) fx.
  by rewrite -(mule0 C%:E); apply: cvgeM => //;
    [exact: cvg_cst | apply: fx; split => //; exact: r_0].
near=> n.
apply/andP; split => //=.
apply: (@le_trans _ _ ((mu (E x n))^-1 *
                       `| \int[mu]_(y in E x n) ((f y)%:E + (- f x)%:E) |)).
  have fxE : (- f x)%:E =
             (mu (E x n))^-1 * \int[mu]_(y in E x n) (- f x)%:E.
    rewrite integral_cst//=; last exact: (hE _).1.
    rewrite muleCA mulVe ?mule1 ?(nicely_shrinking_fin_num (hE x))//.
    by rewrite gt_eqF// (nicely_shrinking_gt0 (hE x)).
  rewrite [in leLHS]fxE -muleDr//; last 2 first.
    rewrite fin_numV//.
      by rewrite -measure_gt0/= (nicely_shrinking_gt0 (hE x)).
    by rewrite -ltNye (@lt_le_trans _ _ 0).
    rewrite integral_cst//=; last exact: (hE _).1.
    by rewrite fin_num_adde_defl// fin_numM// (nicely_shrinking_fin_num (hE x)).
  rewrite abseM gee0_abs; last by rewrite inve_ge0.
  rewrite lee_pmul ?inve_ge0// integralD//=.
  - exact: (hE x).1.
  - apply/integrableP; split.
      by apply/measurable_EFinP; case: locf => + _ _; exact: measurable_funS.
    rewrite (@le_lt_trans _ _
      (\int[mu]_(y in closed_ball x (r_ x n)%:num) `|(f y)%:E|))//.
      apply: ge0_subset_integral => //.
      + exact: (hE _).1.
      + exact: measurable_closed_ball.
      + apply: measurableT_comp => //; apply/measurable_EFinP => //.
        by case: locf => + _ _; exact: measurable_funS.
      + by apply: (subset_trans (E_r_ n)) => //; exact: subset_closed_ball.
    by case: locf => _ _; apply => //; exact: closed_ballR_compact.
  apply/integrableP; split; first exact: measurable_cst.
  rewrite integral_cst //=; last exact: (hE _).1.
  by rewrite lte_mul_pinfty// (nicely_shrinking_lty (hE x)).
rewrite muleA lee_pmul//.
- by rewrite inve_ge0.
- rewrite -(fineK (nicely_shrinking_fin_num (hE x) _)) inver gt_eqF; last first.
    rewrite fine_gt0// (nicely_shrinking_gt0 (hE x))//=.
    by rewrite (nicely_shrinking_lty (hE x)).
  rewrite lebesgue_measure_ball// inver mulrn_eq0/= gt_eqF// -EFinM.
  rewrite -(@invrK _ C) -invfM lee_fin lef_pV2//; last 2 first.
    rewrite posrE fine_gt0// (nicely_shrinking_gt0 (hE x))//=.
    by rewrite (nicely_shrinking_lty (hE x)).
    by rewrite posrE mulr_gt0// ?invr_gt0// fine_gt0//.
  rewrite lter_pdivrMl // -lee_fin EFinM fineK; last first.
    by rewrite (nicely_shrinking_fin_num (hE x)).
  by have := muEr_ n; rewrite lebesgue_measure_ball.
- apply: le_trans.
  + apply: le_abse_integral => //; first exact: (hE x).1.
    apply/measurable_EFinP; apply/measurable_funB => //.
    by case: locf => + _ _; exact: measurable_funS.
  + apply: ge0_subset_integral => //; first exact: (hE x).1.
    exact: measurable_ball.
  + apply/measurable_EFinP; apply: measurableT_comp => //.
    apply/measurable_funB => //.
    by case: locf => + _ _; exact: measurable_funS.
Unshelve. all: by end_near. Qed.

End nice_lebesgue_differentiation.
