From Coq Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp.
From mathcomp Require Import ring lra.
From mathcomp Require Import classical_sets functions cardinality fsbigop.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences esum measure lebesgue_measure numfun exp.
From mathcomp Require Import trigo realfun charge lebesgue_integral kernel.
From mathcomp Require Import probability prob_lang.
From mathcomp Require Import lang_syntax_util lang_syntax lang_syntax_examples.

(**md**************************************************************************)
(* # Observing a noisy draw from a normal distribution                        *)
(*                                                                            *)
(* Formalization of the HelloRight example (Sect. 2.3 of [Shan, POPL 2018]).  *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - Praveen Narayanan. Verifiable and reusable conditioning. PhD thesis,     *)
(*   Indiana University, 2019.                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*   noisy0 == distribution of the next noisy measurement of a normally       *)
(*             distributed quantity                                           *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope string_scope.

(* TODO: PR *)
Section ge0_fin_measurable_probability_integrable.
Context d {T : measurableType d} {R : realType} {p : probability T R}
   {f : T -> \bar R}.

Lemma ge0_fin_measurable_probability_integrable :
  (forall x, 0 <= f x) ->
  (exists M : R, forall x, f x <= M%:E) ->
  measurable_fun setT f ->
  p.-integrable setT f.
Proof.
move=> f0 [M fleM] mf.
apply/integrableP; split => //.
apply (@le_lt_trans _ _ (\int[p]_x M%:E)).
  apply: ge0_le_integral => //=.
      exact: measurableT_comp.
    move=> t _.
    exact: (@le_trans _ _ (f t)).
  move=> t _.
  by rewrite gee0_abs.
by rewrite integral_cst// probability_setT mule1 ltry.
Qed.

End ge0_fin_measurable_probability_integrable.

(* TODO: PR *)
Section pkernel_probability_integrable.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  {p : probability T R} {f : R.-pker T ~> T'}.

Lemma pkernel_probability_integrable V : measurable V ->
  p.-integrable setT (fun x => f x V).
Proof.
move=> mV.
apply: ge0_fin_measurable_probability_integrable => //.
  exists 1%R.
  move=> x.
  apply: (@le_trans _ _ (f x setT)).
    by apply: le_measure; rewrite ?inE.
  by rewrite prob_kernel.
exact: measurable_kernel.
Qed.

End pkernel_probability_integrable.

(* TODO: move to probability.v *)
Section normal_prob_properties.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Local Open Scope charge_scope.

Lemma normal_pdf_uniq_ae (m s : R) (s0 : (0 < s)%R) :
  ae_eq mu setT
   ('d ((charge_of_finite_measure (@normal_prob R m s))) '/d mu)
               (EFin \o (@normal_pdf R m s)).
Proof.
apply: integral_ae_eq => //.
    apply: Radon_Nikodym_integrable => /=.
    exact: normal_prob_dominates.
  apply/measurable_EFinP.
  exact: measurable_normal_pdf.
move=> /= E _ mE.
by rewrite -Radon_Nikodym_integral//=; apply: normal_prob_dominates.
Qed.

End normal_prob_properties.

(* TODO: move *)
Section normal_prob_lemmas.
Context {R: realType}.
Local Notation mu := lebesgue_measure.

Lemma emeasurable_normal_prob (s : R) U : s != 0%R -> measurable U ->
   measurable_fun setT (fun x => normal_prob x s U).
Proof.
move=> s0 mU.
under [X in _ _ X]eq_fun.
  move=> x.
  rewrite -(@fineK _ (_ x _ _)); last first.
    rewrite ge0_fin_numE//.
    apply: (@le_lt_trans _ _ (normal_prob x s setT)).
      by apply: le_measure; rewrite ?inE.
    by rewrite probability_setT ltry.
  over.
apply/measurable_EFinP.
apply: (continuous_measurable_fun).
exact: normal_prob_continuous.
Qed.

(* TODO: s != 0 *)
Lemma integral_normal_prob (m s : R) (s0 : (0 < s)%R) f U :
  measurable U ->
  (normal_prob m s).-integrable U f ->
  \int[@normal_prob _ m s]_(x in U) f x =
  \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E).
Proof.
move=> mU intf.
move/integrableP : (intf) => [mf intf_lty].
rewrite -(Radon_Nikodym_change_of_variables (normal_prob_dominates m s))//=.
apply: ae_eq_integral => //=.
    apply: emeasurable_funM => //.
    apply: measurable_funTS.
    have : charge_of_finite_measure (normal_prob m s) `<< mu.
      exact: normal_prob_dominates m s.
    move/Radon_Nikodym_integrable.
    by move/integrableP => [].
  apply: emeasurable_funM => //.
  apply/measurable_EFinP.
  apply: measurable_funTS.
  exact: measurable_normal_pdf.
apply: ae_eqe_mul2l.
apply: (ae_eq_subset (@subsetT _ U)).
exact: (normal_pdf_uniq_ae m s0).
Qed.

Lemma normal_prob_integrable_dirac (m s : R) (V : set R): measurable V ->
  (normal_prob m s).-integrable setT (fun x => \d_x V).
Proof.
move=> mV.
apply/integrableP; split; first exact: measurable_fun_dirac.
rewrite -(setUv V).
rewrite ge0_integral_setU => //; first last.
      exact/disj_setPCl.
    rewrite setUv.
    apply: measurableT_comp => //.
    exact: measurable_fun_dirac.
  exact: measurableC.
under eq_integral.
  move=> x Vx.
  rewrite diracE Vx/= normr1.
  over.
under [X in _ + X < _]eq_integral.
  move=> x.
  rewrite inE/= => nVx.
  have {}nVx := (memNset nVx).
  rewrite indicE nVx/= normr0.
  over.
rewrite !integral_cst//=; last exact: measurableC.
rewrite mul1e mul0e adde0.
apply: (le_lt_trans (probability_le1 (normal_prob m s) mV)).
exact: ltey.
Qed.

Lemma integral_normal_prob_dirac (s : R) (m : R) V :
  (0 < s)%R ->
  measurable V ->
  \int[normal_prob m s]_x0 (\d_x0 V) = normal_prob m s V.
Proof.
move=> s0 mV.
rewrite integral_normal_prob => //; last first.
  exact: (normal_prob_integrable_dirac m s).
under eq_integral do rewrite diracE.
rewrite /normal_prob.
rewrite [in RHS]integral_mkcond.
under [in RHS]eq_integral do rewrite patchE.
rewrite /=.
apply: eq_integral => x _.
by case: ifP => xV/=; rewrite ?mul1e ?mul0e.
Qed.

End normal_prob_lemmas.

Section noisy_programs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Definition exp_normal1 {R g} := @exp_normal R g _ (@oner_neq0 R).

(* NB: exp_powR level setting is mistaken? *)
(*     ((_ `^ _) * _) cannot write as (_ `^ _ * _) *)
Definition noisy0' : @exp R P [:: ("y0", Real)] Real :=
  [let "x" := Sample {exp_normal1 [{0}:R]} in
   let "_" := Score ({expR 1} `^
                       ({0}:R - (#{"y0"} - #{"x"}) ^+ {2%R} * {2^-1}:R))
                     * {(Num.sqrt (2 * pi))^-1}:R in
   let "z" := Sample {exp_normal1 [#{"x"}]} in
   return #{"z"}].

Definition noisy0 : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisy0'}].

(* other programs from Sect. 2.3 of [Shan, POPL 2018],
   nothing proved about them yet, just for the sake of completeness *)
Definition guard_real {g} str (r : R) :
 @exp R P [:: (str, _) ; g] _ :=
  [if #{str} ==R {r}:R then return TT else Score {0}:R].

Definition helloWrong (y0 : R) : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal1 (exp_real 0)} in
  let "y" := Sample {exp_normal1 [#{"x"}]} in
  let "_" := {guard_real "y" y0} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
  return #{"z"}].

Definition helloJoint : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal1 (exp_real 0)} in
  let "y" := Sample {exp_normal1 [#{"x"}]} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
 return (#{"y"}, #{"z"})].

End noisy_programs.

(* The following section contains the mathematical facts that are used
   to verify the noisy program. They are proved beforehand to
   optimize the time spent by the Qed command of Rocq. *)
Section noisy_subproofs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Local Definition int_normal_noisy0
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[normal_prob 0 1]_x (fun z =>
    `|expR (- ((y.1 - z) ^+ 2%R / 2)) / Num.sqrt (2 * pi)|%:E *
     normal_prob z 1 V) x.

Local Definition int_mu_noisy0
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[mu]_x
     (`|expR (- ((y.1 - x) ^+ 2%R / 2)) / Num.sqrt (2 * pi)|%:E *
      normal_prob x 1 V *
      (normal_pdf 0 1 x)%:E).

Local Definition int_normal_noisy1
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
    ((NngNum (normr_ge0 (expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))))%:num%:E *
      normal_prob x 1 V)%E.

Local Definition int_mu_noisy1
   (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[mu]_x
     (`|expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi)|%:E *
      (normal_prob x 1 V * (normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 x)%:E)).

Local Definition int_normal_noisy2
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x normal_prob x 1 V.

Local Definition int_mu_noisy2
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  normal_prob (y.1 / 2) (Num.sqrt (3 / 2)) V.

Lemma int_normal_mu_noisy0 y V : measurable V ->
  int_normal_noisy0 y V = int_mu_noisy0 y V.
Proof.
move=> mV; rewrite /int_normal_noisy0.
rewrite integral_normal_prob//.
apply: integrableMr => //.
    apply: (@measurableT_comp _ _ _ _ _ _ (@normr _ R^o)) => //.
    apply: measurable_funM => //.
    apply: measurableT_comp => //.
    apply: measurableT_comp => //.
    apply: measurable_funM => //.
    apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => (t ^+ 2%R)%R)) => //.
    exact: measurable_funB.
  exists (Num.sqrt (2 * pi))^-1%R; split; first exact: num_real.
  move=> x x_gt.
  move=> p _.
  rewrite /= normr_id.
  have /normr_idP -> : (0 <= expR (- ((y.1 - p) ^+ 2%R / 2)) / (Num.sqrt (2 * pi)))%R.
    apply: mulr_ge0; first exact: expR_ge0.
    by rewrite invr_ge0 sqrtr_ge0// mulr_ge0// pi_ge0.
  apply/ltW.
  apply: le_lt_trans x_gt.
  rewrite -[leRHS]mul1r ler_pM//.
  by rewrite -expR0 ler_expR oppr_le0 mulr_ge0// ?sqr_ge0// expR0 invr_ge0.
apply/integrableP; split.
  exact: emeasurable_normal_prob.
apply/abse_integralP => //.
  exact: emeasurable_normal_prob.
have/gee0_abs -> : 0 <= \int[normal_prob 0 1]_x normal_prob x 1 V.
  exact: integral_ge0.
apply: (@le_lt_trans _ _ (\int[normal_prob 0 1]_x (cst 1%R x)%:E)).
  apply: ge0_le_integral => //.
      exact: emeasurable_normal_prob.
    apply/measurable_EFinP.
    exact: measurable_cst.
  move=> x _.
  exact: probability_le1.
by rewrite /= integral_cst// mul1e probability_setT ltry.
Qed.

Lemma int_normal_mu_noisy1 y V : measurable V ->
  int_normal_noisy1 y V = int_mu_noisy1 y V.
Proof.
move=> mV; rewrite /int_normal_noisy1 integral_normal_prob//.
  by under eq_integral do rewrite -muleA.
apply/integrableP; split.
  apply: measurable_funeM.
  exact: emeasurable_normal_prob.
apply: (@le_lt_trans _ _ (\int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
  ((NngNum (normr_ge0 (expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))))%:num%:E
   * (cst 1%R x)%:E))).
apply: ge0_le_integral; [by []|by []| | | |].
- apply: measurableT_comp => //.
  apply: measurable_funeM.
  exact: emeasurable_normal_prob.
- by move=> x _; rewrite /= mule1.
- rewrite /= mule1.
  exact/measurable_EFinP.
- move=> x _/=.
  rewrite gee0_abs; last exact: mule_ge0.
  by rewrite lee_pmul// probability_le1.
- rewrite integralZr//; last exact: finite_measure_integrable_cst.
  by rewrite integral_cst// mule1 probability_setT ltry.
Qed.

(* TODO: generalize and move outside *)
Section conjugate_normal_property.

Lemma conjugate_normal1 (m1 m2 s1 s2 : R) V : measurable V ->
  (0 < s1)%R -> s2 != 0%R ->
  \int[normal_prob m1 s1]_x normal_prob (m2 + x) s2 V =
  \int[mu]_(y in V) \int[mu]_x (normal_pdf (m2 + x) s2 y * normal_pdf m1 s1 x)%:E.
Proof.
move=> mV s10 s20; rewrite integral_normal_prob//; last first.
  apply: ge0_fin_measurable_probability_integrable => //=.
    by exists 1%R => ?; exact: probability_le1.
  apply: (@measurableT_comp _ _ _ _ _ _
      (fun x => normal_prob x s2 V) _ (fun x => m2 + x)).
    exact: emeasurable_normal_prob.
  exact: measurable_funD.
transitivity (\int[mu]_x
  \int[mu]_y ((normal_pdf (m2 + x) s2 y *
               normal_pdf m1 s1 x)%:E * (\1_V y)%:E)).
  apply: eq_integral => y _.
  rewrite /normal_prob.
  rewrite -integralZr//; last first.
    apply: (integrableS measurableT) => //.
    exact: integrable_normal_pdf.
  transitivity (\int[mu]_(x in V) (normal_pdf (m2 + y) s2 x *
                                   normal_pdf m1 s1 y)%:E).
    apply: eq_integral => z _.
    by rewrite -EFinM.
  rewrite integral_mkcond.
  by rewrite epatch_indic.
rewrite (@fubini_tonelli _ _ _ _ _ mu mu (EFin \o
  ((fun xz : R * R => (normal_pdf (m2 + xz.1) s2 xz.2 *
                       normal_pdf m1 s1 xz.1)%R
   * \1_V xz.2)%R)))/=; last 2 first.
  apply/measurable_EFinP; apply: measurable_funM => /=; last first.
    apply: measurable_indic.
    rewrite -[X in measurable X]setTX.
    exact: measurableX.
  apply: measurable_funM.
    rewrite [X in measurable_fun _  X](_ : _ = (fun x0 =>
        normal_pdf0 0 s2 (x0.2 - (m2 + x0.1)%E))) /=; last first.
      apply/funext=> x0.
      rewrite /normal_pdf0.
      rewrite normal_pdfE//.
      by rewrite normal_fun_center.
    apply: measurableT_comp.
      exact: measurable_normal_pdf0.
    rewrite /=.
    under eq_fun do rewrite opprD.
    apply: measurable_funD => //=.
    exact: measurable_funB.
  by apply: measurableT_comp => //; exact: measurable_normal_pdf.
  move=> x/=.
  by rewrite lee_fin !mulr_ge0 ?normal_pdf_ge0.
transitivity (\int[mu]_x
   \int[mu]_x0
      ((fun x0 =>
        (normal_pdf (m2 + x0) s2 x * normal_pdf m1 s1 x0)%:E) \_ (fun=> V x)) x0).
  apply: eq_integral => x0 _.
  rewrite /=.
  under eq_integral do rewrite EFinM.
  by rewrite -epatch_indic.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => /= x0 _.
rewrite patchE.
case: ifPn => xV.
  apply: eq_integral => z _/=.
  rewrite patchE.
  by rewrite ifT.
apply: integral0_eq => /= z _.
rewrite patchE ifF//; apply/negbTE.
rewrite notin_setE/=.
move/negP in xV.
by move/mem_set.
Qed.

Lemma conjugate_normal2 (y m1 m2 s1 s2 : R) : s1 != 0%R -> (0 < s2)%R ->
  \int[mu]_x (normal_pdf (m1 + x)%E s1 y * normal_pdf m2 s2 x)%:E =
  (normal_peak s1 * normal_peak s2)%:E *
  \int[mu]_z (normal_fun (m1 + z) s1 y * normal_fun m2 s2 z)%:E.
Proof.
move=> s10 s20.
rewrite -ge0_integralZl//=; last 3 first.
- apply/measurable_EFinP => //=; apply: measurable_funM => //=.
  + apply: measurableT_comp => //=; apply: measurable_funM => //=.
    apply/measurableT_comp => //; apply: measurable_funX.
    under eq_fun do rewrite opprD.
    apply: measurable_funD => //=.
    exact: measurable_funB.
  + apply: measurableT_comp => //=.
    apply: measurable_funM => //.
    apply: measurableT_comp => //.
    by apply: measurable_funX; exact: measurable_funD.
- by move=> z _; rewrite lee_fin mulr_ge0// expR_ge0.
- by rewrite lee_fin mulr_ge0// ?normal_peak_ge0.
apply: eq_integral => /= z _.
rewrite /normal_pdf (negbTE s10) gt_eqF//.
rewrite /normal_pdf0.
rewrite mulrACA.
rewrite /normal_fun.
by congr EFin.
Qed.

Lemma normal_peak1 : normal_peak 1 = (Num.sqrt (pi *+ 2))^-1%R :> R.
Proof. by rewrite /normal_peak expr1n mul1r. Qed.

Lemma conjugate_normal (m2 y : R) V : measurable V ->
  \int[normal_prob y (Num.sqrt 2)^-1]_x normal_prob (m2 + x) 1 V =
  normal_prob (y + m2) (Num.sqrt (3 / 2)) V.
Proof.
move=> mV.
rewrite conjugate_normal1//; apply: eq_integral => x1 _.
clear V mV.
rewrite conjugate_normal2//.
rewrite normal_pdfE// /normal_pdf0.
transitivity ((pi * Num.sqrt 2)^-1%:E *
  \int[mu]_x0 (expR (- (Num.sqrt (3 / 2) ^+ 2)%R * (x0 - (x1 + 2 * y - m2) / 3) ^+ 2 - (x1 - (y + m2)) ^+ 2 / ((Num.sqrt (3 / 2) ^+ 2) *+ 2)))%:E).
  congr *%E.
    rewrite normal_peak1.
    rewrite /normal_peak.
    congr EFin.
    rewrite exprVn sqr_sqrtr//.
    rewrite -mulr_natl mulrA divff// mul1r.
    rewrite -(mulr_natl pi) sqrtrM// invfM.
    rewrite invfM.
    rewrite -mulrA mulrC.
    rewrite -(invfM (Num.sqrt pi)) -expr2.
    by rewrite sqr_sqrtr// pi_ge0.
  apply: eq_integral.
  move=> z _.
  rewrite -expRD.
  congr EFin.
  congr expR.
  rewrite !sqrrD.
  rewrite exprVn sqr_sqrtr//.
  rewrite sqr_sqrtr//.
  lra.
(* gauss integral *)
under eq_integral do rewrite expRD EFinM.
rewrite ge0_integralZr//=; last first.
  apply/measurable_EFinP.
  apply: measurableT_comp => //.
  apply: measurable_funM => //.
  apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => t ^+ 2)%R) => //.
  exact: measurable_funD.
rewrite /=.
rewrite /normal_peak /normal_fun.
rewrite [in RHS]sqr_sqrtr//.
rewrite -[in RHS]mulr_natr [in RHS]mulrAC divfK//.
rewrite mulNr EFinM muleA.
congr *%E; last first.
  by rewrite sqr_sqrtr//.
rewrite [X in _ * X = _](_ : _ = (Num.sqrt ((1 / 3) * pi *+ 2))%:E *
   \int[mu]_z (normal_pdf ((x1 + 2 * y - m2) / 3) (Num.sqrt (1 / 3)) z)%:E); last first.
  rewrite -ge0_integralZl//=; last 2 first.
    by apply/measurable_EFinP; exact: measurable_normal_pdf.
    by move=> /= z _; rewrite lee_fin normal_pdf_ge0.
  apply: eq_integral => /= z _.
  rewrite /normal_pdf gt_eqF// /normal_pdf0 /normal_peak /normal_fun.
  rewrite (@sqr_sqrtr _ (1 / 3))// -EFinM; congr EFin.
  rewrite [RHS]mulrA -[LHS]mul1r; congr (_ * expR _)%R.
    by rewrite divff// gt_eqF// sqrtr_gt0 pmulrn_rgt0// mulr_gt0// pi_gt0.
  rewrite -(mulr_natl (1 / 3)) mul1r.
  rewrite sqr_sqrtr//.
  by rewrite !mulNr (mulrC (3 / 2)%R) invfM invrK (mulrC 2^-1%R).
rewrite integral_normal_pdf.
rewrite mule1 -EFinM mul1r; congr EFin.
rewrite -(mulr_natr (_ * pi)) sqrtrM ?mulr_ge0 ?pi_ge0//.
rewrite invfM mulrCA -mulrA mulVf ?mulr1 ?gt_eqF//.
rewrite !sqrtrM// invfM sqrtrV// -mulrA; congr *%R.
rewrite -[X in (_ / X)%R]sqr_sqrtr ?pi_ge0//.
by rewrite expr2 invfM mulrA divff ?div1r// gt_eqF// sqrtr_gt0 pi_gt0.
Qed.

End conjugate_normal_property.

Lemma int_normal_mu_noisy2 y V : measurable V ->
  int_normal_noisy2 y V = int_mu_noisy2 y V.
Proof.
move=> mV.
have := @conjugate_normal 0 (y.1 / 2) _ mV.
under eq_integral do rewrite add0r.
rewrite /int_normal_noisy2.
rewrite addr0.
exact.
Qed.

End noisy_subproofs.

(* this section contains the verification of the noisy program per se *)
Section noisy_verification.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

(* definition of intermediate programs *)
Definition neq0Vsqrt2 : ((Num.sqrt 2)^-1 != 0 :> R)%R.
Proof. exact: lt0r_neq0. Qed.
Definition exp_normal_Vsqrt2 {g} := @exp_normal R g _ neq0Vsqrt2.

Definition noisy1' : @exp R _ [:: ("y0", Real)] Real :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2%R} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
 return #{"z"}].

Definition noisy1 : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisy1'}].

Definition neq0sqrt32 : (Num.sqrt (3 / 2) != 0 :> R)%R.
Proof. exact: lt0r_neq0. Qed.
Definition exp_normal_sqrt32 {g} := @exp_normal R g _ neq0sqrt32.

Definition noisy2' : @exp R _ [:: ("y0", Real)] _ :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2%R} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  Sample {exp_normal_sqrt32 [#{"y0"} * {2^-1}:R]}].

Definition noisy2 : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisy2'}].

(* from (7) to (9) in [Shan, POPL 2018] *)
Lemma execP_noisy'12 y V : measurable V ->
 @execP R [:: ("_", Unit); ("y0", Real)] _
   [let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
    let "z" := Sample {exp_normal1 [#{"x"}]} in
    return #{"z"}] y V =
 @execP R [:: ("_", Unit); ("y0", Real)] _
 [Sample {exp_normal_sqrt32 [#{"y0"} * {2^-1}:R]}] y V.
Proof.
move=> mV.
(* execute syntax *)
rewrite !execP_letin.
rewrite !execP_sample !execD_normal/=.
rewrite (@execD_bin _ _ binop_mult) execD_real/=.
rewrite execP_return.
rewrite !exp_var'E (execD_var_erefl "y0") (execD_var_erefl "x") (execD_var_erefl "z")/=.
rewrite !letin'E/=.
under eq_integral do rewrite letin'E/=.
rewrite /=.
(* prove semantics *)
under eq_integral do rewrite integral_normal_prob_dirac//=.
exact: (int_normal_mu_noisy2 _ mV).
Qed.

(* semantics of noisy0 (turned into a local definition as an attempt to optimize Qed) *)
Local Definition executed_noisy0' :=
  (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
   letin'
    (sample (fun=> normal_prob 0 1)
       (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0) (kr 0)))
    (letin'
       (score
          (measurable_funM
             (measurableT_comp (measurable_powRr (expR 1))
                (measurable_funB (kr 0)
                   (measurable_funM
                      (measurable_funX 2%R
                         (measurable_funB (measurable_acc_typ [:: Real; Real] 1)
                            (measurable_acc_typ [:: Real; Real] 0)))
                      (kr 2^-1)))) (kr (Num.sqrt (2 * pi))^-1)))
       (letin'
          (sample
             (fun
                x : unit *
                    (g_sigma_algebraType R.-ocitv.-measurable *
                     (g_sigma_algebraType R.-ocitv.-measurable * unit)) =>
              normal_prob x.2.1 1)
             (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0)
                (measurable_acc_typ [:: Unit; Real; Real] 1)))
        (ret (measurable_acc_typ [:: Real; Unit; Real; Real] 0)))) y V : \bar R).

(* semantics of noisy1 (turned into a local definition as a attempt to optimized Qed) *)
Local Definition executed_noisy1' :=
 (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  letin'
    (score
       (measurable_funM
          (measurableT_comp (measurable_powRr (expR 1))
             (measurable_funB (kr 0)
                (measurable_funM
                   (measurable_funX 2%R (measurable_acc_typ [:: Real] 0)) (kr 4^-1))))
          (kr (Num.sqrt (4 * pi))^-1)))
    (letin'
       (sample
          (fun x : unit * (g_sigma_algebraType R.-ocitv.-measurable * unit) =>
           normal_prob (x.2.1 / 2) (Num.sqrt 2)^-1)
          (measurableT_comp (measurable_normal_prob2 neq0Vsqrt2)
             (measurable_funM (measurable_acc_typ [:: Unit; Real] 1) (kr 2^-1))))
       (letin'
          (sample
             (fun
                x : g_sigma_algebraType R.-ocitv.-measurable *
                    (unit * (g_sigma_algebraType R.-ocitv.-measurable * unit)) =>
              normal_prob x.1 1)
             (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0)
                (measurable_acc_typ [:: Real; Unit; Real] 0)))
          (ret (measurable_acc_typ [:: Real; Real; Unit; Real] 0)))) y V : \bar R).

Lemma execP_noisy0'E y V : execP noisy0' y V = executed_noisy0' y V.
Proof.
rewrite !execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite execD_real/=.
rewrite execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execD_real/=.
rewrite execD_real/=.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return/=.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
done.
Qed.

Lemma executed_noisy0'_semantics y V : measurable V ->
  executed_noisy0' y V = int_normal_noisy0 y V.
Proof.
move=> mV.
rewrite /executed_noisy0'.
rewrite [in LHS]letin'E/=.
under [in LHS]eq_integral.
  move=> x _.
  rewrite letin'E/=.
  under eq_integral.
    move=> u _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//.
    over.
  rewrite /=.
  rewrite ge0_integral_mscale/=; first last.
  - by move=> ? _.
  - by [].
  - exact: measurableT.
  rewrite integral_dirac; first last.
  - by [].
  - exact: measurableT.
  rewrite diracT mul1e.
  rewrite sub0r.
  rewrite -expRM mul1r.
  over.
by rewrite /=.
Qed.

Lemma execP_noisy1'E y V : execP noisy1' y V = executed_noisy1' y V.
Proof.
rewrite execP_letin.
rewrite execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite execD_real/=.
rewrite execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
done.
Qed.

Lemma executed_noisy1'_semantics y V : measurable V ->
  executed_noisy1' y V = int_normal_noisy1 y V.
Proof.
move=> mV; rewrite /executed_noisy1'.
rewrite letin'E/=.
under eq_integral.
  move=> u _.
  rewrite letin'E/=.
  under eq_integral.
    move=> x _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//.
    over.
  over.
rewrite ge0_integral_mscale//; first last.
  move=> ? _.
  exact: integral_ge0.
rewrite integral_dirac//.
rewrite diracT mul1e.
rewrite sub0r -expRM mul1r.
rewrite /=.
rewrite -(@ge0_integralZl _ _ R (normal_prob _ _) _ measurableT _ _
  (`|expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi)|%:E))//.
exact: emeasurable_normal_prob.
Qed.

Lemma noisy'01 y V : measurable V -> execP noisy0' y V = execP noisy1' y V.
Proof.
move=> mV.
(* lhs *)
rewrite execP_noisy0'E.
rewrite (executed_noisy0'_semantics _ mV).
(* rhs *)
rewrite execP_noisy1'E.
rewrite (executed_noisy1'_semantics _ mV).
(* semantics *)
rewrite (int_normal_mu_noisy0 _ mV).
rewrite (int_normal_mu_noisy1 _ mV).
(* eq_integral *)
apply: eq_integral.
move=> x _.
rewrite [in LHS]muleAC.
rewrite [in RHS](muleC (normal_prob x 1 V)) muleA.
congr (fun t => t * normal_prob x 1 V)%E.
rewrite [in LHS]ger0_norm; last by rewrite mulr_ge0// expR_ge0.
rewrite [in RHS]ger0_norm; last by rewrite mulr_ge0// expR_ge0.
rewrite -!EFinM; congr EFin.
rewrite !normal_pdfE// /normal_pdf0.
rewrite mulrA.
rewrite mulrAC.
rewrite -(@sqrtrV _ 2)//.
rewrite /normal_peak.
rewrite sqr_sqrtr; last by rewrite invr_ge0.
rewrite /normal_fun.
rewrite subr0.
rewrite sqr_sqrtr; last by rewrite invr_ge0.
rewrite [X in (X / _)%R = _]mulrC mulrA -expRD -mulrA -invfM.
rewrite [RHS]mulrAC [X in _ = (_ * X / _)%R]mulrC mulrA -mulrA -expRD -invfM.
congr *%R.
  congr expR.
  lra.
congr GRing.inv.
rewrite expr1n mul1r -mulrnAr -(mulr_natl pi) mulrA mulVf// mul1r -expr2.
rewrite sqr_sqrtr; last by rewrite mulr_ge0// pi_ge0.
rewrite !sqrtrM// mulrCA -expr2 sqr_sqrtr; last exact: pi_ge0.
congr *%R.
rewrite -[LHS]gtr0_norm//.
rewrite -(sqrtr_sqr 2%R).
congr Num.sqrt.
lra.
Qed.

Lemma noisy'12 y V : measurable V -> execP noisy1' y V = execP noisy2' y V.
Proof.
move=> mV.
rewrite /noisy1' /noisy2'.
rewrite execP_letin/= [in RHS]execP_letin/=.
rewrite letin'E [RHS]letin'E.
by under eq_integral do rewrite execP_noisy'12//.
Qed.

Lemma noisy'02 y V : measurable V -> execP noisy0' y V = execP noisy2' y V.
Proof. by move=> mV; rewrite noisy'01// noisy'12. Qed.

End noisy_verification.
