From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra functions.
From mathcomp Require Import xfinmap constructive_ereal reals discrete.
From mathcomp Require Import realseq realsum.
From mathcomp Require Import topology esum sequences normedtype ereal.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import numfun measurable_realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import counting_distr.
From mathcomp Require Import random_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Notation simpm := Monoid.simpm.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Import HBNNSimple.
Import MeasurableR.

(* -------------------------------------------------------------------- *)
Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} (T : choiceType) (f : T -> \bar R) :
  (\esum_(x in [set: discrete_measurable_space T]) f x
     = \esum_(x in [set: T]) f x)%E.
Proof.
by apply: (@reindex_esum R T (discrete_measurable_space T)
          [set: T] [set: discrete_measurable_space T] id f); split.
Qed.

(* -------------------------------------------------------------------- *)
Section SubProbability_measure_subpmf.
Context (R : realType) (T : choiceType) (mu : R.-pmf T).

Definition measure_of_pmf (S : set (discrete_measurable_space T)) :=
  \esum_(x in S) (EFin \o mu) x.

Let P0 : measure_of_pmf set0 = 0%E.
Proof. by rewrite /measure_of_pmf esum_set0. Qed.

Let P_ge0 (S : set (discrete_measurable_space T)) : (0 <= measure_of_pmf S)%E.
Proof. by apply: esum_ge0 => x _; rewrite lee_fin. Qed.

Let P_sigma_additive : semi_sigma_additive measure_of_pmf.
Proof.
move=> F _ tF _.
have -> : measure_of_pmf (\bigcup_n F n) = (\sum_(i <oo) measure_of_pmf (F i))%E.
  rewrite nneseries_esumT; first by move=> n; exact: P_ge0.
  apply: esum_bigcup => //=.
  + by apply: (sub_trivIset (@subsetT _ _) tF).
  + by move=> x; rewrite lee_fin.
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

(* -------------------------------------------------------------------- *)
Section maxe.
Context (R : realType) (T : choiceType) (mu : R.-pmf T).

Lemma maxe_pmfM (a : \bar R) x :
  (maxe (a * (mu x)%:E) 0 = maxe a 0 * (mu x)%:E)%E.
Proof.
rewrite [in LHS]muleC [in RHS]muleC maxe_pMr => //=.
- by rewrite lee_fin.
- by rewrite mule0.
Qed.

Lemma maxeN_pmfM (a : \bar R) x :
  (maxe (- (a * (mu x)%:E)) 0 = maxe (- a) 0 * (mu x)%:E)%E.
Proof. by rewrite -mulNe maxe_pmfM. Qed.

End maxe.

(* -------------------------------------------------------------------- *)
Section Expectation.
Context (R : realType) (T : choiceType) (mu : R.-pmf T).

Lemma integral_espe (f : T -> \bar R) : (forall x, 0 <= f x)%E ->
  \int[measure_of_pmf mu]_x f x = \Ee_[mu] f.
Proof.
move=> f0; rewrite /eexpectation_pmf -esum_setT_discrete -integral_counting_esum => //=.
rewrite - (@integral_measure_of_density _ (discrete_measurable_space T) R
             (@counting (discrete_measurable_space T) R)  mu) //=.
move => H; apply: eq_measure_integral => A mA _ /=.
by rewrite /measure_of_density /measure_of_pmf integral_counting_esum.
Qed.

Lemma espeE (f : T ->  R) :  ('E_(measure_of_pmf mu)[f] = \Ee_[mu] (EFin \o f)).
Proof.
rewrite expectation_def integralE /eexpectation_pmf esumE; congr (_ - _).
- transitivity (\Ee_[mu] ((EFin \o f)^\+)).
    by rewrite integral_espe// => x; exact: funepos_ge0.
  by rewrite /eexpectation_pmf; apply: eq_esum => x _; rewrite !funeposE maxe_pmfM.
- transitivity (\Ee_[mu] ((EFin \o f)^\-)).
    by rewrite integral_espe// => x; exact: funeneg_ge0.
  by rewrite /eexpectation_pmf; apply: eq_esum => x _; rewrite !funenegE maxeN_pmfM.
Qed.

End Expectation.

(* -------------------------------------------------------------------- *)
Section pmf_subpmf.
Context d (T : measurableType d) (R : realType) (Pr : probability T R).
Variable X : {RV Pr >-> R}.

Lemma pmf_fin_bigcup (J : seq R) : uniq J ->
  \sum_(j <- J) (pmf X j)%:E
    = Pr (\bigcup_(j in [set` J]) X @^-1` [set j]).
Proof.
move=> uJ.
rewrite (@measure_fin_bigcup _ _ _ Pr _ [set` J] (fun j : R => X @^-1` [set j])).
- exact: finite_seq.
- exact: trivIset_preimage1.
- by move=> j _; exact: measurable_funPTI.
- rewrite fsbig_seq//; apply: eq_fsbigr => j _.
  by rewrite /pmf fineK// fin_num_measure.
Qed.

Lemma pmf_uniq_le1 (J : seq R) : uniq J -> (\sum_(j <- J) pmf X j <= 1)%R.
Proof.
move=> uJ; rewrite -lee_fin -sumEFin pmf_fin_bigcup//.
apply: probability_le1; apply: fin_bigcup_measurable.
- exact: finite_seq.
- by move=> j _; exact: measurable_funPTI.
Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R R (pmf X) (@pmf_ge0 _ _ _ Pr X) pmf_uniq_le1.

End pmf_subpmf.

(* -------------------------------------------------------------------- *)
Section pr_pmf.
Context d (T : pmeasurableType d) (R : realType) (Pr : probability T R).
Variable X : {dRV Pr >-> R}.

Local Notation pmfX := (@pmf _ _ _ Pr X).

Lemma pmf_out (r : R) : ~ range X r -> pmfX r = 0%R.
Proof. by move=> nr; rewrite /pmf preimage10// measure0. Qed.

Lemma esum_pmf_range :
  esum [set: R] (EFin \o pmfX) = \esum_(r in range X) (pmfX r)%:E.
Proof.
rewrite (esumID (range X) [set: R] (EFin \o pmfX)).
- by move=> i _; rewrite lee_fin pmf_ge0.
- rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
  by rewrite pmf_out.
Qed.

Lemma esum_pmf_dRV : esum [set: R] (EFin \o pmfX) = 1.
Proof.
rewrite esum_pmf_range.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X)
          (fun r => (pmfX r)%:E))//.
transitivity (\esum_(k in dRV_dom X) enum_prob X k).
  apply: eq_esum => k kd.
  by rewrite /enum_prob patchE mem_set// /pmf fineK// fin_num_measure.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- by move=> n _; rewrite /enum_prob patchE; case: ifP.
- rewrite eseries_mkcond -[RHS](@sum_enum_prob _ _ _ _ _ Pr X measurable_set1).
  apply: eq_eseriesr => k _.
  case: ifPn => // kd.
  by rewrite /enum_prob patchE (negbTE kd).
Qed.

Lemma esum_pmf_set_dRV (A : set R) : measurable A ->
  \esum_(r in A) (pmfX r)%:E = distribution Pr X A.
Proof.
move=> mA.
pose g (r : R) := if r \in A then (pmfX r)%:E else 0.
have g0 r : ~ range X r -> g r = 0.
  by move=> nr; rewrite /g pmf_out//; case: ifP.
transitivity (\esum_(r in [set: R]) g r); first exact: esum_mkcond.
transitivity (\esum_(r in range X) g r).
  rewrite (esumID (range X) [set: R] g).
  - move=> i _; rewrite /g; case: ifPn => // _.
    by rewrite lee_fin pmf_ge0.
  - rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
    exact: g0.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X) g)//.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- move=> n _; rewrite /g; case: ifPn => // _.
  by rewrite lee_fin pmf_ge0.
- rewrite eseries_mkcond.
  rewrite [RHS](@distribution_dRV _ _ _ _ _ Pr X measurable_set1 A mA).
  apply: eq_eseriesr => k _.
  rewrite /g /enum_prob patchE diracE; case: ifPn => kd; last by rewrite mul0e.
  rewrite /pmf fineK ?fin_num_measure//.
  by case: ifPn => _; rewrite ?mule1 ?mule0.
Qed.

Lemma esum_pmf_pred (A : set R) :
  esum [set: R] (EFin \o (fun r : R => ((r \in A)%:R * pmfX r)%R))
    = \esum_(r in A) (pmfX r)%:E.
Proof.
rewrite [RHS]esum_mkcond; apply: eq_esum => r _.
by case: (r \in A) => /=; rewrite ?mul1r ?mul0r.
Qed.

Lemma pr_pmf_dRV (A : set R) : measurable A ->
  (\P_[pmfX] (fun r => r \in A))%:E = distribution Pr X A.
Proof.
by move=> mA; rewrite /pr esum_pmf_pred esum_pmf_set_dRV// fineK ?fin_num_measure.
Qed.

End pr_pmf.

(* -------------------------------------------------------------------- *)
Section espe_pmf.
Context d (T : pmeasurableType d) (R : realType) (Pr : probability T R).
Variable X : {dRV Pr >-> R}.

Local Notation pmfX := (@pmf _ _ _ Pr X).

Lemma distribution_integral_counting (A : set R) : measurable A ->
  distribution Pr X A = \int[@counting R R]_(r in A) (pmfX r)%:E.
Proof.
move=> mA; rewrite integral_counting_esum => //=.
- by apply/measurable_EFinP; exact: pmf_measurable.
- by rewrite esum_pmf_set_dRV.
Qed.

Lemma ge0_espe_pmf (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall r, 0 <= f r) ->
  \Ee_[pmfX] f = \int[Pr]_w f (X w).
Proof.
move=> mf f0.
have mfh : measurable_fun [set: R] (fun r => f r * (pmfX r)%:E).
  by apply: emeasurable_funM => //; apply/measurable_EFinP; exact: pmf_measurable.
have fh0 r : 0 <= f r * (pmfX r)%:E.
  by apply: mule_ge0; [exact: f0|rewrite lee_fin pmf_ge0].
have step1 : \Ee_[pmfX] f = \int[@counting R R]_r (f r * (pmfX r)%:E).
  by rewrite /eexpectation_pmf -integral_counting_esum//; exact: measurable_set1.
have step2 : \int[distribution Pr X]_r f r
           = \int[@counting R R]_r (f r * (pmfX r)%:E).
rewrite -(@integral_measure_of_density _ R R (@counting R R) pmfX) //=.
+ move => H. apply: eq_measure_integral =>  A mA _ /=.
  exact: distribution_integral_counting.
+ exact: pmf_measurable.
have step3 : \int[distribution Pr X]_r f r = \int[Pr]_w f (X w).
  by rewrite /distribution ge0_integral_pushforward.
by rewrite step1 -step2 step3.
Qed.

Lemma espe_pmf_dRV : \Ee_[pmfX] EFin = 'E_Pr[X].
Proof.
have mE : measurable_fun [set: R] (EFin : R -> \bar R) by apply/measurable_EFinP.
rewrite /eexpectation_pmf esumE expectation_def integralE; congr (_ - _).
- transitivity (\Ee_[pmfX] (EFin^\+)).
    by rewrite /eexpectation_pmf; apply: eq_esum => r _; rewrite !funeposE maxe_pmfM.
  rewrite ge0_espe_pmf => //=.
  + exact: measurable_funepos.
  + by apply: eq_integral => w _; rewrite !funeposE.
- transitivity (\Ee_[pmfX] (EFin^\-)).
    by rewrite /eexpectation_pmf; apply: eq_esum => r _; rewrite !funenegE maxeN_pmfM.
  rewrite ge0_espe_pmf => //=.
  + exact: measurable_funeneg.
  + by apply: eq_integral => w _; rewrite !funenegE.
Qed.

End espe_pmf.
