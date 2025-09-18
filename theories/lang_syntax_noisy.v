Require Import String.
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
(* Formalization of Shan's HelloRight example (Sec. 2.3 of [Shan, POPL 2018]).*)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - Praveen Narayanan. Verifiable and reusable conditioning. PhD thesis,     *)
(*   Indiana University, 2019.                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*   noisyA == distribution of the next noisy measurement of a normally       *)
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

(* TODO: PR? *)
Section ge0_bounded_measurable_probability_integrable.
Context d {T : measurableType d} {R : realType} {p : probability T R}
   {f : T -> \bar R}.

Lemma ge0_bounded_measurable_probability_integrable :
  (forall x, 0 <= f x) -> (exists M : R, forall x, f x <= M%:E) ->
  measurable_fun setT f -> p.-integrable setT f.
Proof.
move=> f0 [M fleM] mf.
apply/integrableP; split => //.
rewrite (@le_lt_trans _ _ (\int[p]_x M%:E))//.
  apply: ge0_le_integral => //=.
    exact: measurableT_comp.
  move=> t _.
  apply: (@le_trans _ _ (f t)) => //.
  by rewrite gee0_abs.
by rewrite integral_cst// probability_setT mule1 ltry.
Qed.

End ge0_bounded_measurable_probability_integrable.

(* TODO: PR *)
Section pkernel_probability_integrable.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  {p : probability T R} {f : R.-pker T ~> T'}.

Lemma pkernel_probability_integrable V : measurable V ->
  p.-integrable setT (fun x => f x V).
Proof.
move=> mV.
apply: ge0_bounded_measurable_probability_integrable => //.
  exists 1%R => x.
  rewrite (@le_trans _ _ (f x setT))//.
    by rewrite le_measure ?inE.
  by rewrite prob_kernel.
exact: measurable_kernel.
Qed.

End pkernel_probability_integrable.

(* TODO: move to probability.v? *)
Section normal_prob_lemmas.
Context {R: realType}.
Local Notation mu := lebesgue_measure.

Local Open Scope charge_scope.

Lemma normal_pdf_uniq_ae (m s : R) (s0 : (s != 0)%R) :
  ae_eq mu setT
   ('d ((charge_of_finite_measure (@normal_prob R m s))) '/d mu)
               (EFin \o (@normal_pdf R m s)).
Proof.
apply: integral_ae_eq => //.
- by apply: Radon_Nikodym_integrable => /=; exact: normal_prob_dominates.
- by apply/measurable_EFinP; exact: measurable_normal_pdf.
- move=> /= E _ mE.
  by rewrite -Radon_Nikodym_integral//=; exact: normal_prob_dominates.
Qed.

Local Close Scope charge_scope.

Lemma measurable_normal_prob (s : R) U : s != 0%R -> measurable U ->
  measurable_fun setT (fun x => normal_prob x s U).
Proof.
move=> s0 mU.
under [X in _ _ X]eq_fun.
  move=> /= x.
  rewrite -(@fineK _ (_ x _ _)); last first.
    rewrite ge0_fin_numE//.
    rewrite (@le_lt_trans _ _ (normal_prob x s setT))//.
      by rewrite le_measure ?inE.
    by rewrite probability_setT ltry.
  over.
apply/measurable_EFinP.
apply: (continuous_measurable_fun).
exact: normal_prob_continuous.
Qed.

Lemma integral_normal_prob (m s : R) (s0 : (s != 0)%R) f U :
  measurable U ->
  (normal_prob m s).-integrable U f ->
  \int[@normal_prob _ m s]_(x in U) f x =
  \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E).
Proof.
move=> mU intf.
move/integrableP : (intf) => [mf intf_lty].
rewrite -(Radon_Nikodym_change_of_variables (normal_prob_dominates m s))//=.
apply: ae_eq_integral => //=.
- apply: emeasurable_funM => //.
  apply: measurable_funTS.
  have : charge_of_finite_measure (normal_prob m s) `<< mu.
    exact: normal_prob_dominates m s.
  by move=> /Radon_Nikodym_integrable /integrableP[].
- apply: emeasurable_funM => //.
  apply/measurable_EFinP.
  apply: measurable_funTS.
  exact: measurable_normal_pdf.
- apply: ae_eqe_mul2l.
  apply: (ae_eq_subset (@subsetT _ U)).
  exact: (normal_pdf_uniq_ae m s0).
Qed.

Lemma normal_prob_integrable_dirac (m s : R) (V : set R): measurable V ->
  (normal_prob m s).-integrable setT (fun x => \d_x V).
Proof.
move=> mV.
apply/integrableP; split; first exact: measurable_fun_dirac.
rewrite -(setUv V) ge0_integral_setU//; last 3 first.
  exact: measurableC.
  rewrite setUv.
  apply: measurableT_comp => //.
  exact: measurable_fun_dirac.
  exact/disj_setPCl.
under eq_integral.
  move=> x Vx.
  rewrite diracE Vx/= normr1.
  over.
under [X in _ + X < _]eq_integral.
  move=> /= x.
  rewrite inE/= => nVx.
  have {}nVx := memNset nVx.
  rewrite indicE nVx/= normr0.
  over.
rewrite !integral_cst//=; last exact: measurableC.
rewrite mul1e mul0e adde0.
apply: (le_lt_trans (probability_le1 (normal_prob m s) mV)).
exact: ltey.
Qed.

Lemma integral_normal_prob_dirac (s : R) (m : R) V :
  (s != 0)%R -> measurable V ->
  \int[normal_prob m s]_x (\d_x V) = normal_prob m s V.
Proof.
move=> s0 mV.
rewrite integral_normal_prob//; last exact: normal_prob_integrable_dirac.
under eq_integral do rewrite diracE.
rewrite /= /normal_prob [in RHS]integral_mkcond.
under [in RHS]eq_integral do rewrite patchE.
rewrite /=.
apply: eq_integral => x _.
by case: ifP => xV/=; rewrite ?mul1e ?mul0e.
Qed.

End normal_prob_lemmas.

(* TODO: move to probability.v *)
Section normal_probD.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Let normal_pdf0 m s x : R := normal_peak s * normal_fun m s x.

Let measurable_normal_pdf0 m s : measurable_fun setT (normal_pdf0 m s).
Proof. by apply: measurable_funM => //=; exact: measurable_normal_fun. Qed.

Lemma normal_probD1 (m1 m2 s1 s2 : R) V : measurable V ->
  s1 != 0%R -> s2 != 0%R ->
  \int[normal_prob m1 s1]_x normal_prob (m2 + x) s2 V =
  \int[mu]_(y in V) \int[mu]_x (normal_pdf (m2 + x) s2 y * normal_pdf m1 s1 x)%:E.
Proof.
move=> mV s10 s20; rewrite integral_normal_prob//; last first.
  apply: ge0_bounded_measurable_probability_integrable => //=.
    by exists 1%R => ?; exact: probability_le1.
  apply: (@measurableT_comp _ _ _ _ _ _
      (fun x => normal_prob x s2 V) _ (fun x => m2 + x)).
    exact: measurable_normal_prob.
  exact: measurable_funD.
transitivity (\int[mu]_x \int[mu]_y
    ((normal_pdf (m2 + x) s2 y * normal_pdf m1 s1 x)%:E * (\1_V y)%:E)).
  apply: eq_integral => y _.
  rewrite /normal_prob -integralZr//; last first.
    by apply: (integrableS measurableT) => //; exact: integrable_normal_pdf.
  transitivity (\int[mu]_(x in V)
      (normal_pdf (m2 + y) s2 x * normal_pdf m1 s1 y)%:E).
    by apply: eq_integral => z _; rewrite -EFinM.
  by rewrite integral_mkcond epatch_indic.
rewrite (@fubini_tonelli _ _ _ _ _ mu mu (EFin \o
  ((fun xz : R * R => (normal_pdf (m2 + xz.1) s2 xz.2 *
                       normal_pdf m1 s1 xz.1)%R * \1_V xz.2)%R)))/=; last 2 first.
  apply/measurable_EFinP; apply: measurable_funM => /=; last first.
    apply: measurable_indic; rewrite -[X in measurable X]setTX.
    exact: measurableX.
  apply: measurable_funM => /=.
    rewrite [X in measurable_fun _  X](_ : _ = (fun x =>
        normal_pdf0 0 s2 (x.2 - (m2 + x.1)%E)))/=; last first.
      by apply/funext=> x0; rewrite /normal_pdf0 normal_pdfE// normal_fun_center.
    apply: measurableT_comp => /=; first exact: measurable_normal_pdf0.
    under eq_fun do rewrite opprD.
    by apply: measurable_funD => //=; exact: measurable_funB.
  by apply: measurableT_comp => //; exact: measurable_normal_pdf.
  by move=> x/=; rewrite lee_fin !mulr_ge0 ?normal_pdf_ge0.
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
  \int[mu]_x (normal_pdf (m1 + x)%E s1 y * normal_pdf m2 s2 x)%:E =
  (normal_peak s1 * normal_peak s2)%:E *
  \int[mu]_z (normal_fun (m1 + z) s1 y * normal_fun m2 s2 z)%:E.
Proof.
move=> s10 s20.
rewrite -ge0_integralZl//=; last 3 first.
  apply/measurable_EFinP => //=; apply: measurable_funM => //=.
  - rewrite /normal_fun.
    under eq_fun do rewrite -(sqrrN (y - _)) opprB (addrC m1) -addrA -opprB.
    exact: measurable_normal_fun.
  - exact: measurable_normal_fun.
  by move=> z _; rewrite lee_fin mulr_ge0// expR_ge0.
  by rewrite lee_fin mulr_ge0// ?normal_peak_ge0.
apply: eq_integral => /= z _.
by rewrite 2?normal_pdfE// /normal_pdf0 mulrACA /normal_fun.
Qed.

Lemma normal_peak1 : normal_peak 1 = (Num.sqrt (pi *+ 2))^-1%R :> R.
Proof. by rewrite /normal_peak expr1n mul1r. Qed.

(* Variable elimination and integration [Shan, Section 3.5, (9)],
 * also known as the reproductive property of normal distribution.
 *)
Lemma normal_probD (m1 s1 m2 s2 : R) V : s1 != 0%R -> s2 != 0%R ->
  measurable V ->
  \int[normal_prob m1 s1]_x normal_prob (m2 + x) s2 V =
  normal_prob (m1 + m2) (Num.sqrt (s1 ^+ 2 + s2 ^+ 2)) V.
Proof.
move=> s10 s20 mV.
rewrite normal_probD1//; apply: eq_integral => y _.
clear V mV.
rewrite normal_probD2//.
have s1s20 : (s1 ^+ 2 + s2 ^+ 2 != 0)%R.
  by rewrite lt0r_neq0// addr_gt0// exprn_even_gt0.
have sqs1s20 : Num.sqrt (s1 ^+ 2 + s2 ^+ 2) != 0%R.
  by rewrite lt0r_neq0// sqrtr_gt0 addr_gt0// exprn_even_gt0.
rewrite normal_pdfE /normal_pdf0//.
set S1 := (s1 ^+ 2)%R.
set S2 := (s2 ^+ 2)%R.
transitivity (((Num.sqrt S1 * Num.sqrt S2 * pi *+ 2)^-1)%:E *
  \int[mu]_x (expR
  (- (x - (y * s1 ^+ 2 + m1 * s2 ^+ 2 - m2 * s1 ^+ 2)
         / (s1 ^+ 2 + s2 ^+ 2)%R ) ^+ 2
   / ((Num.sqrt ((s1 ^+ 2 * s2 ^+ 2) / (s1 ^+ 2 + s2 ^+ 2)%R) ^+ 2) *+ 2)
 - (y - (m1 + m2)) ^+ 2 / ((s1 ^+ 2 + s2 ^+ 2) *+ 2)))%:E).
  congr *%E.
    rewrite /normal_peak.
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
  apply: eq_integral.
  move=> x _.
  rewrite -expRD.
  congr ((expR _)%:E).
  rewrite sqr_sqrtr; last first.
    rewrite mulr_ge0 ?invr_ge0// ?addr_ge0 ?(@mulr_ge0 _ (_ ^+ 2))// ?sqr_ge0//.
  by field; do ?[apply/and3P; split].
set DS12 := S1 + S2.
set MS12 := (S1 * S2)%R.
set C := ((((y * s1 ^+ 2)%R + (m1 * s2 ^+ 2)%R)%E - m2 * s1 ^+ 2) / DS12)%R.
under eq_integral do rewrite expRD EFinM.
rewrite ge0_integralZr//=; last first.
 apply/measurable_EFinP.
 apply: measurableT_comp => //.
 apply: measurable_funM => //.
 apply: measurableT_comp => //.
 apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => t ^+ 2)%R) => //.
 exact: measurable_funD.
rewrite /normal_peak /normal_fun.
rewrite [in RHS]EFinM.
rewrite [in RHS]sqr_sqrtr//; last first.
  by rewrite addr_ge0// sqr_ge0.
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
  rewrite normal_pdfE; last first.
    apply: lt0r_neq0.
    by rewrite sqrtr_gt0.
  rewrite mulrA mulVf// ?mul1r//.
  rewrite lt0r_neq0// invr_gt0 sqrtr_gt0 pmulrn_lgt0// mulr_gt0// ?pi_gt0//.
  rewrite exprn_even_gt0//=.
  by rewrite lt0r_neq0// sqrtr_gt0.
rewrite ge0_integralZl//; last 3 first.
  apply/measurable_EFinP.
  exact: measurable_normal_pdf.
  move=> x _.
  rewrite lee_fin.
  exact: normal_pdf_ge0.
  rewrite lee_fin invr_ge0.
  exact: normal_peak_ge0.
rewrite integral_normal_pdf.
rewrite mule1 -EFinM; congr EFin.
rewrite -invfM; congr GRing.inv.
rewrite -sqrtrM ?sqr_ge0//.
rewrite /normal_peak sqr_sqrtr; last by rewrite ltW.
rewrite -3!mulrnAr.
rewrite (sqrtrM (pi *+ 2)); last by rewrite ltW.
rewrite invfM mulrCA.
rewrite -{1}(@sqr_sqrtr _ (pi *+ 2)); last by rewrite pmulrn_lge0 ?pi_ge0.
rewrite -2!(mulrA (Num.sqrt _)) divff// ?mulr1; last first.
  by rewrite lt0r_neq0// sqrtr_gt0 pmulrn_lgt0 ?pi_gt0.
rewrite (sqrtrM (DS12^-1)); last by rewrite mulr_ge0 ?sqr_ge0.
rewrite sqrtrV; last by rewrite addr_ge0 ?sqr_ge0.
rewrite invfM invrK.
rewrite mulrAC mulrA mulVf ?mul1r; last first.
  by rewrite lt0r_neq0// sqrtr_gt0 mulr_gt0 ?exprn_even_gt0.
rewrite sqrtrM; last by rewrite addr_ge0 ?sqr_ge0.
by rewrite mulrC.
Qed.

End normal_probD.

Section noisy_programs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Definition exp_normal1 {g} (e : exp D g Real) :=
  [Normal e {1%R} {oner_neq0 R}].

(* NB: exp_powR level setting is mistaken? *)
(*     ((_ `^ _) * _) cannot write as (_ `^ _ * _) *)
Definition noisyA' : @exp R P [:: ("y0", Real)] Real :=
  [let "x" := Sample {exp_normal1 [{0}:R]} in
   let "_" := Score ({expR 1} `^
                       ({0}:R - (#{"y0"} - #{"x"}) ^+ {2%R} * {2^-1}:R))
                     * {(Num.sqrt (2 * pi))^-1}:R in
   let "z" := Sample {exp_normal1 [#{"x"}]} in
   return #{"z"}].

Definition noisyA : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisyA'}].

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
   to verify the noisy program. They are proved beforehand as an attempt
   to optimize the time spent by the Qed command of Rocq. *)
Section noisy_subproofs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Local Definition noisyA_semantics_normal
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[normal_prob 0 1]_x (fun z =>
    (expR (- ((y.1 - z) ^+ 2%R / 2)) / Num.sqrt (2 * pi))%:E *
     normal_prob z 1 V) x.

Lemma noisyA_semantics_normalE y V : measurable V ->
  noisyA_semantics_normal y V =
  \int[mu]_x
     ((expR (- ((y.1 - x) ^+ 2%R / 2)) / Num.sqrt (2 * pi))%:E *
      normal_prob x 1 V *
      (normal_pdf 0 1 x)%:E).
Proof.
move=> mV; rewrite /noisyA_semantics_normal.
rewrite integral_normal_prob//.
apply: integrableMr => //.
    apply: measurable_funM => //.
    under eq_fun do rewrite -sqrrN opprB -mulNr.
    rewrite [X in fun _ => expR (_ / X)%R](_:2 = 1 ^+ 2 *+ 2)%R; last first.
      by rewrite expr1n.
    exact: measurable_normal_fun.
  exists (Num.sqrt (2 * pi))^-1%R; split; first exact: num_real.
  move=> x x_gt p _.
  rewrite /= ger0_norm; last by rewrite mulr_ge0// expR_ge0.
  apply/ltW; apply: le_lt_trans x_gt.
  rewrite -[leRHS]mul1r ler_pM ?expR_ge0//.
  by rewrite -expR0 ler_expR oppr_le0 mulr_ge0// ?sqr_ge0// expR0 invr_ge0.
apply/integrableP; split; first exact: measurable_normal_prob.
apply/abse_integralP => //; first exact: measurable_normal_prob.
rewrite gee0_abs//; last exact: integral_ge0.
apply: (@le_lt_trans _ _ (\int[normal_prob 0 1]_x (cst 1%R x)%:E)).
  apply: ge0_le_integral => //; first exact: measurable_normal_prob.
    by apply/measurable_EFinP; exact: measurable_cst.
  by move=> x _; exact: probability_le1.
by rewrite /= integral_cst// mul1e probability_setT ltry.
Qed.

Local Definition noisyB_semantics_normal
    (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) :=
  \int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
    ((expR (- (y.1 ^+ 2%R / 4)) /
                         Num.sqrt (4 * pi))%:E *
      normal_prob x 1 V)%E.

Lemma noisyB_semantics_normalE y V : measurable V ->
  noisyB_semantics_normal y V =
  \int[mu]_x
     ((expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))%:E *
      (normal_prob x 1 V * (normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 x)%:E)).
Proof.
move=> mV; rewrite /noisyB_semantics_normal integral_normal_prob//.
  by under eq_integral do rewrite -muleA.
apply/integrableP; split.
  by apply: measurable_funeM; exact: measurable_normal_prob.
apply: (@le_lt_trans _ _ (\int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
  ((NngNum (normr_ge0 (expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))))%:num%:E
   * (cst 1%R x)%:E))).
apply: ge0_le_integral; [by []|by []| | |].
- apply: measurableT_comp => //.
  by apply: measurable_funeM; exact: measurable_normal_prob.
- by rewrite /= mule1; exact/measurable_EFinP.
- move=> x _/=.
  rewrite abseM/= lee_pmul//.
  rewrite gee0_abs; last exact: measure_ge0.
  by rewrite probability_le1.
- rewrite integralZr//; last exact: finite_measure_integrable_cst.
  by rewrite integral_cst// mule1 probability_setT ltry.
Qed.

Local Definition noisyA'_part
    (y : (@mctx R [:: ("y0", Real)])) (x : R) :=
  ((expR (- ((y.1 - x) ^+ 2%R / 2)) / Num.sqrt (2 * pi)) * (normal_pdf 0 1 x))%R.

Local Definition noisyB'_part
    (y : (@mctx R [:: ("y0", Real)])) (x : R) :=
  ((expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi)) * (normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 x))%R.

Lemma noisyAB'_rearrange (y : (@mctx R [:: ("y0", Real)])) x :
  noisyA'_part y x = noisyB'_part y x.
Proof.
rewrite /noisyA'_part/noisyB'_part !normal_pdfE//.
rewrite mulrA mulrAC -(@sqrtrV _ 2)//.
rewrite /normal_peak sqr_sqrtr; last by rewrite invr_ge0.
rewrite /normal_fun subr0 sqr_sqrtr; last by rewrite invr_ge0.
rewrite -mulrA mulrAC mulrA.
rewrite [X in (X / _ / _)%R = _](_ : _ =
    expR (- x ^+ 2 / (1 ^+ 2 *+ 2) - (y.1 - x) ^+ 2%R / 2)); last first.
  by rewrite mulrC -expRD -mulrA.
rewrite [RHS]mulrAC [X in _ = (_ * X / _)%R]mulrC mulrA -mulrA -[RHS]mulrA.
rewrite -expRD -2!invfM.
congr ((expR _) * _^-1)%R.
  lra.
rewrite -2?sqrtrM; last 2 first.
  by rewrite -mulr_natr mulrAC mulVf// mul1r pi_ge0.
  by rewrite expr1n mul1r mulrn_wge0// pi_ge0.
congr Num.sqrt.
lra.
Qed.

Lemma noisyC_semanticsE (y : R) V : measurable V ->
  \int[normal_prob y (Num.sqrt 2)^-1]_x normal_prob x 1 V =
  normal_prob y (Num.sqrt (3 / 2)) V.
Proof.
move=> mV.
have := @normal_probD R (y ) (Num.sqrt 2)^-1 0 1 _ _ _ mV.
under eq_integral do rewrite add0r.
rewrite addr0.
rewrite (_ : ((Num.sqrt 2)^-1 ^+ 2 + 1 ^+ 2 = 3 / 2)%R)//; last first.
  rewrite exprVn sqr_sqrtr// expr1n -[in LHS]div1r -{3}(@divff _ 1%R)//.
  rewrite addf_div// 2!mulr1 mul1r (_:1%R = 1%:R)// -natrD.
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

Definition exp_normal_Vsqrt2 {g} (e : exp D g Real) :=
  [Normal e {(Num.sqrt 2)^-1%R} {neq0Vsqrt2}].

Definition tailB : @exp R _ [:: ("_", Unit); ("y0", Real)] Real :=
  [let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R]} in
   let "z" := Sample {exp_normal1 [#{"x"}]} in
   return #{"z"}].
Definition noisyB' : @exp R _ [:: ("y0", Real)] Real :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2%R} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  {tailB}].
Definition noisyB : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisyB'}].

Definition neq0sqrt32 : (Num.sqrt (3 / 2) != 0 :> R)%R.
Proof. exact: lt0r_neq0. Qed.
Definition exp_normal_sqrt32 {g} (e : exp D g Real) :=
  [Normal e {Num.sqrt (3 / 2)} {neq0sqrt32}].

Definition tailC : @exp R _ [:: ("_", Unit); ("y0", Real)] Real :=
 [Sample {exp_normal_sqrt32 [#{"y0"} * {2^-1}:R]}].
Definition noisyC' : @exp R _ [:: ("y0", Real)] _ :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2%R} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  {tailC}].
Definition noisyC : @exp R _ [:: ("y0", Real)] _ := [Normalize {noisyC'}].

Lemma noisyAB' y V : measurable V -> execP noisyA' y V = execP noisyB' y V.
Proof.
move=> mV.
(* reduce the lhs *)
rewrite 3![in LHS]execP_letin.
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
rewrite 2!execD_real/=.
rewrite execP_sample/=.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return/=.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
(* reduce the rhs *)
rewrite [in RHS]execP_letin.
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
(* semantics *)
transitivity (noisyA_semantics_normal y V).
  rewrite [in LHS]letin'E/=.
  apply: eq_integral => x _.
  rewrite letin'E/=.
    under eq_integral.
    move=> u _.
    rewrite letin'E/= integral_normal_prob_dirac//.
    over.
  rewrite /= ge0_integral_mscale//.
  rewrite integral_dirac// diracT mul1e sub0r -expRM mul1r/=.
  by rewrite ger0_norm; last by rewrite mulr_ge0// expR_ge0.
transitivity (noisyB_semantics_normal y V); last first.
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
  rewrite /= ge0_integral_mscale//; first last.
    by move=> ? _; exact: integral_ge0.
  rewrite integral_dirac// diracT mul1e sub0r -expRM mul1r/=.
  rewrite ger0_norm; last by rewrite mulr_ge0// expR_ge0.
  rewrite -(@ge0_integralZl _ _ R (normal_prob _ _) _ measurableT _ _
    (expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))%:E)//.
  exact: measurable_normal_prob.
rewrite noisyA_semantics_normalE//.
rewrite noisyB_semantics_normalE//.
apply: eq_integral => x _.
transitivity ((noisyA'_part y x)%:E * normal_prob x 1 V).
  by rewrite muleAC.
transitivity ((noisyB'_part y x)%:E * normal_prob x 1 V); last first.
  by rewrite (muleC (normal_prob x 1 V)) muleA.
congr (fun t => t%:E * normal_prob x 1 V)%E.
exact: noisyAB'_rearrange.
Qed.

(* from (7) to (9) in [Shan, POPL 2018] *)
Lemma tailBC y V : measurable V ->
  @execP R [:: ("_", Unit); ("y0", Real)] _ tailB y V =
  @execP R [:: ("_", Unit); ("y0", Real)] _ tailC y V.
Proof.
move=> mV.
(* execute lhs *)
rewrite 2![in LHS]execP_letin.
rewrite 2![in LHS]execP_sample.
rewrite 2!execD_normal/=.
rewrite (@execD_bin _ _ binop_mult) execD_real/=.
rewrite execP_return.
rewrite exp_var'E (execD_var_erefl "y0")/=.
rewrite exp_var'E (execD_var_erefl "x")/=.
rewrite exp_var'E (execD_var_erefl "z")/=.
rewrite ![in LHS]letin'E/=.
under eq_integral do rewrite letin'E/=.
(* execute rhs *)
rewrite [in RHS]execP_sample/=.
rewrite execD_normal/=.
rewrite (@execD_bin _ _ binop_mult) execD_real/=.
rewrite exp_var'E (execD_var_erefl "y0")/=.
(* prove semantics *)
under eq_integral do rewrite integral_normal_prob_dirac//=.
by rewrite noisyC_semanticsE.
Qed.

Lemma noisyBC' y V : measurable V -> execP noisyB' y V = execP noisyC' y V.
Proof.
move=> mV.
rewrite /noisyB' /noisyC'.
rewrite execP_letin/= [in RHS]execP_letin/=.
rewrite letin'E [RHS]letin'E.
by under eq_integral do rewrite tailBC//.
Qed.

Lemma noisyAC' y V : measurable V -> execP noisyA' y V = execP noisyC' y V.
Proof. by move=> mV; rewrite noisyAB'// noisyBC'. Qed.

End noisy_verification.

(* Trying to show why rewriting noisyB to noisyC is reproductive property *)
(*
Section rewrite noisyB'_to_variable_addition.

Definition noisyB'_alter : @exp R _ [:: ("y0", Real)] Real :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R]} in
  let "x1" := Sample {exp_normal1 [{0}:R]} in
 return #{"x"} + #{"x1"}].

Definition noisyB_alter : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize {noisyB'_alter}].

Lemma execP_noisyB'_alterE y V :
@execP R [:: ("y0", Real)] Real noisyB'_alter y V = executed_noisyB'_alter y V.
Proof.
rewrite 3!execP_letin.
rewrite execP_return/=.
rewrite (@execD_bin _ _ binop_add)/=.
rewrite (exp_var'E "x") (exp_var'E "x1").
rewrite (execD_var_erefl "x") (execD_var_erefl "x1")/=.
rewrite 2!execP_sample.
rewrite 2!execD_normal/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_real/=.
rewrite execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite 2!execD_real/=.
rewrite 2!(exp_var'E "y0") 2!(execD_var_erefl "y0")/=.
rewrite /executed_noisyB'_alter.
rewrite /=.
Abort.

Lemma noisyB_alterE y V : measurable V ->
  @execP R [:: ("y0", Real)] Real noisyB' y V =
  @execP R [:: ("y0", Real)] Real noisyB'_alter y V.
Proof.
move=> mV.
rewrite 3![in RHS]execP_letin.
rewrite [in RHS]execP_return/=.
rewrite [in RHS](@execD_bin _ _ binop_add)/=.
rewrite [in RHS](exp_var'E "x") (exp_var'E "x1").
rewrite [in RHS](execD_var_erefl "x") (execD_var_erefl "x1")/=.
rewrite 2![in RHS]execP_sample.
rewrite 2![in RHS]execD_normal/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS]execP_score.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS]execD_pow_real/=.
rewrite [in RHS](@execD_bin _ _ binop_minus)/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS]execD_pow/=.
rewrite 2![in RHS]execD_real/=.
rewrite 2![in RHS](exp_var'E "y0") 2!(execD_var_erefl "y0")/=.
rewrite [in RHS]letin'E/=.
under [RHS]eq_integral.
  move=> x _.
  rewrite letin'E/=.
  under eq_integral.
    move=> z _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//; last first.
      admit. (* standard property of measurable sets *)
    rewrite (_ : (fun x0 => V (z + x0)) = ((fun x0 => z + x0) @^-1` V)); last by [].
    rewrite (_ : normal_prob 0 1 ((fun x0 => z + x0) @^-1` V) = normal_prob z 1 V); last first.
      admit. (* general version of integration by substitution *)
    over.
  over.
rewrite ge0_integral_mscale//; last first.
  move=> x _.
  apply: integral_ge0.
  by move=> z _.
rewrite integral_dirac// diracT mul1e.
rewrite -ge0_integralZl//; last first.
  exact: emeasurable_normal_prob.
rewrite sub0r.
rewrite -expRM mul1r.

rewrite execP_noisyB'E.
by rewrite executed_noisyB'_semantics.
Abort.

End rewrite noisyB'_to_variable_addition.
*)
