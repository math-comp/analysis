From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals topology esum sequences normedtype ereal.
From mathcomp Require Import numfun measure measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral counting_distr random_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} {T : choiceType} (f : T -> \bar R) :
  \esum_(x in [set: discrete_measurable_space T]) f x =
  \esum_(x in [set: T]) f x.
Proof.
by apply: (@reindex_esum R T (discrete_measurable_space T)
          [set: T] [set: discrete_measurable_space T] id f); split.
Qed.

Section SubProbability_measure_subpmf.
Context {R : realType} {T : choiceType} (mu : R.-pmf T).

Definition measure_of_pmf (S : set (discrete_measurable_space T)) :=
  \esum_(x in S) (EFin \o mu) x.

Let P0 : measure_of_pmf set0 = 0%E.
Proof. by rewrite /measure_of_pmf esum_set0. Qed.

Let P_ge0 (S : set (discrete_measurable_space T)) : (0 <= measure_of_pmf S)%E.
Proof. by apply: esum_ge0 => x _; rewrite lee_fin. Qed.

Let P_sigma_additive : semi_sigma_additive measure_of_pmf.
Proof.
move=> F _ tF _.
rewrite [X in _ --> X](_ : _ = \sum_(i <oo) measure_of_pmf (F i)).
  rewrite nneseries_esumT; first by move=> n; exact: P_ge0.
  apply: esum_bigcup => //=.
    exact: (sub_trivIset (@subsetT _ _) tF).
  by move=> x; rewrite lee_fin.
apply: cvg_toP => //.
apply: is_cvg_nneseries => n _ _; rewrite /measure_of_pmf.
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ measure_of_pmf
  P0 P_ge0 P_sigma_additive.

Let P_setT : (measure_of_pmf [set: discrete_measurable_space T] <= 1)%E.
Proof. by rewrite /measure_of_pmf esum_setT_discrete; exact: subpmf_sum_le1. Qed.

HB.instance Definition _ :=
  @Measure_isSubProbability.Build _ _ R measure_of_pmf P_setT.

End SubProbability_measure_subpmf.

Section Expectation.
Context {R : realType} {T : choiceType} (mu : R.-pmf T).

Lemma integral_espe (f : T -> \bar R) : (forall x, 0 <= f x)%E ->
  \int[measure_of_pmf mu]_x f x = \Ee_[mu] f.
Proof.
move=> f0; rewrite /eexpectation_pmf -esum_setT_discrete -integral_counting_esum//=.
rewrite -(@integral_measure_of_density _ (discrete_measurable_space T) R
  (@counting (discrete_measurable_space T) R) mu)//=.
move => H; apply: eq_measure_integral => A mA _ /=.
by rewrite /measure_of_density /measure_of_pmf integral_counting_esum.
Qed.

Lemma eexpectationE (f : T ->  R) :
  'E_(measure_of_pmf mu)[f] = \Ee_[mu] (EFin \o f).
Proof.
rewrite expectation_def integralE /eexpectation_pmf esumE; congr (_ - _).
- transitivity (\Ee_[mu] ((EFin \o f)^\+)).
    by rewrite integral_espe// => x; exact: funepos_ge0.
  rewrite /eexpectation_pmf; apply: eq_esum => x _; rewrite !funeposE.
  by rewrite maxe_pMl ?mul0e// lee_fin.
- transitivity (\Ee_[mu] ((EFin \o f)^\-)).
    by rewrite integral_espe// => x; exact: funeneg_ge0.
  rewrite /eexpectation_pmf; apply: eq_esum => x _; rewrite !funenegE.
  by rewrite maxe_pMl ?mul0e ?mulNe// lee_fin.
Qed.

End Expectation.

Section pmf_subpmf.
Import MeasurableR.
Context {d} {T : measurableType d} {R : realType} (P : probability T R)
  (X : {RV P >-> R}).

Lemma pmf_fin_bigcup (J : seq R) : uniq J ->
  \sum_(j <- J) (pmf X j)%:E = P (\bigcup_(j in [set` J]) X @^-1` [set j]).
Proof.
move=> uJ.
rewrite (@measure_fin_bigcup _ _ _ P _ [set` J] (fun j : R => X @^-1` [set j]))//.
- exact: finite_seq.
- exact: trivIset_preimage1.
- rewrite fsbig_seq//; apply: eq_fsbigr => j _.
  by rewrite /pmf fineK// fin_num_measure.
Qed.

Let pmf_uniq_le1 (J : seq R) : uniq J -> (\sum_(j <- J) pmf X j <= 1)%R.
Proof.
move=> uJ; rewrite -lee_fin -sumEFin pmf_fin_bigcup//.
by rewrite probability_le1//; exact: fin_bigcup_measurable.
Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R R (pmf X) (@pmf_ge0 _ _ _ P X) pmf_uniq_le1.

End pmf_subpmf.

Section pr_pmf.
Import MeasurableR.
Context {d} {T : pmeasurableType d} {R : realType} (P : probability T R)
  (X : {dRV P >-> R}).

Local Notation pmfX := (@pmf _ _ _ P X).

Lemma esum_pmf_range :
  esum [set: R] (EFin \o pmfX) = \esum_(r in range X) (pmfX r)%:E.
Proof.
rewrite (esumID (range X) [set: R] (EFin \o pmfX)).
- by move=> i _; rewrite lee_fin.
rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
by rewrite not_range_pmf0.
Qed.

Lemma esum_pmf_dRV : esum [set: R] (EFin \o pmfX) = 1.
Proof.
rewrite esum_pmf_range.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X))//.
transitivity (\esum_(k in dRV_dom X) enum_prob X k).
  apply: eq_esum => k kd/=.
  by rewrite /enum_prob patchE mem_set// /pmf fineK// fin_num_measure.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- by move=> n _; rewrite /enum_prob patchE; case: ifP.
- rewrite eseries_mkcond -[RHS](sum_enum_prob X measurable_set1).
  apply: eq_eseriesr => k _; case: ifPn => // kd.
  by rewrite /enum_prob patchE (negbTE kd).
Qed.

Lemma esum_pmf_pred (A : set R) :
  esum [set: R] (EFin \o (fun r => (r \in A)%:R * pmfX r))%R =
  \esum_(r in A) (pmfX r)%:E.
Proof.
rewrite [RHS]esum_mkcond; apply: eq_esum => r _.
by case: (r \in A) => /=; rewrite ?mul1r ?mul0r.
Qed.

Lemma pr_pmf_dRV (A : set R) : measurable A ->
  (\P_[pmfX] (mem A))%:E = distribution P X A.
Proof.
move=> mA; rewrite /pr esum_pmf_pred dRV_esum_pmf_distribution// fineK//.
by rewrite fin_num_measure.
Qed.

End pr_pmf.

Section espe_pmf.
Import MeasurableR.
Context {d} {T : pmeasurableType d} {R : realType} (P : probability T R)
  (X : {dRV P >-> R}).

Local Notation pmfX := (@pmf _ _ _ P X).

Lemma distribution_integral_counting (A : set R) : measurable A ->
  distribution P X A = \int[@counting R R]_(r in A) (pmfX r)%:E.
Proof.
move=> mA.
rewrite -dRV_esum_pmf_distribution// integral_counting_esum//=.
by apply/measurable_EFinP; exact: pmf_measurable.
Qed.

Lemma ge0_espe_pmf (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall r, 0 <= f r) ->
  \Ee_[pmfX] f = \int[P]_w f (X w).
Proof.
move=> mf f0.
have mfh : measurable_fun [set: R] (fun r => f r * (pmfX r)%:E).
  by apply: emeasurable_funM => //; apply/measurable_EFinP; exact: pmf_measurable.
have fh0 r : 0 <= f r * (pmfX r)%:E.
  by apply: mule_ge0; [exact: f0|rewrite lee_fin pmf_ge0].
have -> : \Ee_[pmfX] f = \int[@counting R R]_r (f r * (pmfX r)%:E).
  by rewrite /eexpectation_pmf -integral_counting_esum//; exact: measurable_set1.
have <- : \int[distribution P X]_r f r =
          \int[@counting R R]_r (f r * (pmfX r)%:E).
  rewrite -(integral_measure_of_density _ (pmf_measurable X))//=.
  apply: eq_measure_integral =>  A mA _ /=.
  exact: distribution_integral_counting.
by rewrite /distribution ge0_integral_pushforward.
Qed.

Lemma espe_pmf_dRV : \Ee_[pmfX] EFin = 'E_P[X].
Proof.
rewrite /eexpectation_pmf esumE expectation_def integralE; congr (_ - _).
- transitivity (\Ee_[pmfX] EFin^\+).
    by apply: eq_esum => r _; rewrite !funeposE maxe_pMl ?lee_fin// mul0e.
  rewrite ge0_espe_pmf => //=; first exact: measurable_funepos.
  by apply: eq_integral => w _; rewrite !funeposE.
- transitivity (\Ee_[pmfX] (EFin^\-)).
    by apply: eq_esum => r _; rewrite !funenegE maxe_pMl ?lee_fin// mul0e mulNe.
  rewrite ge0_espe_pmf//=; first exact: measurable_funeneg.
  by apply: eq_integral => w _; rewrite !funenegE.
Qed.

End espe_pmf.
