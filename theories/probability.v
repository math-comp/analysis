(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import poly ssrnum ssrint interval archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals interval_inference ereal topology normedtype.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
From mathcomp Require Import ftc gauss_integral hoelder.

(**md**************************************************************************)
(* # Probability                                                              *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(* About integrability: as a rule of thumb, in this file, we favor the use    *)
(* of `Lfun P n` hypotheses instead of the `integrable` predicate from        *)
(* `lebesgue_integral.v`.                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      {RV P >-> T'} == random variable: a measurable function to the        *)
(*                       measurableType T' from the measured space            *)
(*                       characterized by the probability P                   *)
(*   distribution P X == measure image of the probability measure P by the    *)
(*                       random variable X : {RV P -> T'}                     *)
(*                       P as type probability T R with T of type             *)
(*                       measurableType.                                      *)
(*                       Declared as an instance of probability measure.      *)
(*            'E_P[X] == expectation of the real measurable function X        *)
(*     covariance X Y == covariance between real random variable X and Y      *)
(*            'V_P[X] == variance of the real random variable X               *)
(*             'M_P X == moment generating function of the random variable X  *)
(*                       with sample space corresponding to the probability   *)
(*                       measure P                                            *)
(*    {dmfun T >-> R} == type of discrete real-valued measurable functions    *)
(*      {dRV P >-> R} == real-valued discrete random variable                 *)
(*          dRV_dom X == domain of the discrete random variable X             *)
(*         dRV_enum X == bijection between the domain and the range of X      *)
(*            pmf X r := fine (P (X @^-1` [set r]))                           *)
(*            cdf X r == cumulative distribution function of X                *)
(*                    := distribution P X `]-oo, r]                           *)
(*           ccdf X r == complementary cumulative distribution function of X  *)
(*                    := distribution P X `]r, +oo[                           *)
(*      enum_prob X k == probability of the kth value in the range of X       *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*      bernoulli_pmf p == Bernoulli pmf with parameter p : R                 *)
(*          bernoulli p == Bernoulli probability measure when 0 <= p <= 1     *)
(*                         and \d_false otherwise                             *)
(*     binomial_pmf n p == binomial pmf with parameters n : nat and p : R     *)
(*    binomial_prob n p == binomial probability measure when 0 <= p <= 1      *)
(*                         and \d_0%N otherwise                               *)
(*       bin_prob n k p == $\binom{n}{k}p^k (1-p)^(n-k)$                      *)
(*                         Computes a binomial distribution term for          *)
(*                         k successes in n trials with success rate p        *)
(*      uniform_pdf a b == uniform pdf over the interval [a,b]                *)
(*  uniform_prob a b ab == uniform probability over the interval [a,b]        *)
(*                         where ab0 a proof that 0 < b - a                   *)
(*        normal_peak s := (sqrtr (s ^+ 2 * pi *+ 2))^-1                      *)
(*     normal_fun m s x := expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2))              *)
(*       normal_pdf m s == pdf of the normal distribution with mean m and     *)
(*                         standard deviation s                               *)
(*                         Using normal_peak and normal_pdf.                  *)
(*      normal_prob m s == normal probability measure                         *)
(*    exponential_pdf r == pdf of the exponential distribution with rate r    *)
(*   exponential_prob r == exponential probability measure                    *)
(*      poisson_pmf r k == pmf of the Poisson distribution with parameter r   *)
(*       poisson_prob r == Poisson probability measure                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E_' P [ X ]"
  (at level 5, P, X at level 4, format "''E_' P [ X ]").
Reserved Notation "''V_' P [ X ]"
  (at level 5, P, X at level 4, format "''V_' P [ X ]").
Reserved Notation "'M_ P X" (at level 5, P, X at level 4, format "''M_' P  X").
Reserved Notation "{ 'dmfun' aT >-> T }" (format "{ 'dmfun'  aT  >->  T }").
Reserved Notation "'{' 'dRV' P >-> R '}'" (format "'{' 'dRV'  P  '>->'  R '}'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition random_variable d d' (T : measurableType d) (T' : measurableType d')
  (R : realType) (P : probability T R) := {mfun T >-> T'}.

Notation "{ 'RV' P >-> T' }" := (@random_variable _ _ _ T' _ P) : form_scope.

Lemma notin_range_measure d d' (T : measurableType d) (T' : measurableType d')
    (R : realType) (P : {measure set T -> \bar R}) (X : T -> R) r :
  r \notin range X -> P (X @^-1` [set r]) = 0%E.
Proof. by rewrite notin_setE => hr; rewrite preimage10. Qed.

Lemma probability_range d d' (T : measurableType d) (T' : measurableType d')
    (R : realType) (P : probability T R) (X : {RV P >-> R}) :
  P (X @^-1` range X) = 1%E.
Proof. by rewrite preimage_range probability_setT. Qed.

Definition distribution d d' (T : measurableType d) (T' : measurableType d')
    (R : realType) (P : probability T R) (X : {mfun T >-> T'}) :=
  pushforward P X.

Section distribution_is_probability.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  {P : probability T R}.
Variable X : {mfun T >-> T'}.

Let distribution0 : distribution P X set0 = 0%E.
Proof. exact: measure0. Qed.

Let distribution_ge0 A : (0 <= distribution P X A)%E.
Proof. exact: measure_ge0. Qed.

Let distribution_sigma_additive : semi_sigma_additive (distribution P X).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (distribution P X)
  distribution0 distribution_ge0 distribution_sigma_additive.

Let distribution_is_probability : distribution P X [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  (distribution P X) distribution_is_probability.

End distribution_is_probability.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  (P : probability T R).

Lemma probability_distribution (X : {RV P >-> T'}) r :
  P [set x | X x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma ge0_integral_distribution (X : {RV P >-> T'}) (f : T' -> \bar R) :
    measurable_fun [set: T'] f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite ge0_integral_pushforward. Qed.

Lemma integral_distribution (X : {RV P >-> T'}) (f : T' -> \bar R) :
    measurable_fun [set: T'] f -> P.-integrable [set: T] (f \o X) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf intf; rewrite integral_pushforward. Qed.

End transfer_probability.

Definition cdf d (T : measurableType d) (R : realType) (P : probability T R)
  (X : {RV P >-> R}) (r : R) := distribution P X `]-oo, r].

Section cumulative_distribution_function.
Context d {T : measurableType d} {R : realType} (P : probability T R).
Variable X : {RV P >-> R}.
Local Open Scope ereal_scope.

Lemma cdf_ge0 r : 0 <= cdf X r. Proof. by []. Qed.

Lemma cdf_le1 r : cdf X r <= 1. Proof. exact: probability_le1. Qed.

Lemma cdf_fin_num r : cdf X r \is a fin_num.
Proof.
by rewrite ge0_fin_numE ?cdf_ge0//; exact/(le_lt_trans (cdf_le1 r))/ltry.
Qed.

Lemma cdf_nondecreasing : nondecreasing_fun (cdf X).
Proof. by move=> r s rs; rewrite le_measure ?inE//; exact: subitvPr. Qed.

Lemma cvg_cdfy1 : cdf X @ +oo%R --> 1.
Proof.
pose s : \bar R := ereal_sup (range (cdf X)).
have cdf_s : cdf X r @[r --> +oo%R] --> s.
  exact: nondecreasing_cvge cdf_nondecreasing.
have cdf_ns : cdf X n%:R @[n --> \oo%R] --> s.
  by move/cvge_pinftyP : cdf_s; apply; exact/cvgryPge/nbhs_infty_ger.
have cdf_n1 : cdf X n%:R @[n --> \oo] --> 1.
  rewrite -(probability_setT P).
  pose F n := X @^-1` `]-oo, n%:R].
  have <- : \bigcup_n F n = setT.
    rewrite -preimage_bigcup -subTset => t _/=.
    by exists (trunc (X t)).+1 => //=; rewrite in_itv/= ltW// truncnS_gt.
  apply: nondecreasing_cvg_mu => //; first exact: bigcup_measurable.
  move=> n m nm; apply/subsetPset => x/=; rewrite !in_itv/= => /le_trans.
  by apply; rewrite ler_nat.
by rewrite -(cvg_unique _ cdf_ns cdf_n1).
Qed.

Lemma cvg_cdfNy0 : cdf X @ -oo%R --> 0.
Proof.
rewrite cvgNy_compNP.
have cdf_opp_noninc : {homo cdf X \o -%R : q r / (q <= r)%R >-> q >= r}.
  by move=> q r; rewrite -lterN2; exact: cdf_nondecreasing.
pose s := ereal_inf (range (cdf X \o -%R)).
have cdf_opp_s : (cdf X \o -%R) r @[r --> +oo%R] --> s.
  exact: nonincreasing_cvge cdf_opp_noninc.
have cdf_opp_ns : (cdf X \o -%R) n%:R @[n --> \oo] --> s.
  by move/cvge_pinftyP : cdf_opp_s; apply; exact/cvgryPge/nbhs_infty_ger.
have cdf_opp_n0 : (cdf X \o -%R) n%:R @[n --> \oo] --> 0.
  rewrite -(measure0 P).
  pose F n := X @^-1` `]-oo, (- n%:R)%R].
  have <- : \bigcap_n F n = set0.
    rewrite -subset0 => t.
    set m := (trunc `|X t|).+1.
    move=> /(_ m I); rewrite /F/= in_itv/= leNgt => /negP; apply.
    by rewrite ltrNl /m (le_lt_trans (ler_norm _))// normrN truncnS_gt.
  apply: nonincreasing_cvg_mu => //=.
  + by rewrite (le_lt_trans (probability_le1 _ _)) ?ltry.
  + exact: bigcap_measurable.
  + move=> m n mn; apply/subsetPset => x/=; rewrite !in_itv => /le_trans; apply.
    by rewrite lerN2 ler_nat.
by rewrite (_ : 0%E = s)// (cvg_unique _ cdf_opp_ns cdf_opp_n0).
Qed.

Lemma cdf_right_continuous : right_continuous (cdf X).
Proof.
move=> a.
pose s := fine (ereal_inf (cdf X @` `]a, a + 1%R]%classic)).
have cdf_s : cdf X r @[r --> a^'+] --> s%:E.
  rewrite /s fineK.
  - apply: nondecreasing_at_right_cvge; first by rewrite ltBSide /= ?ltrDl.
    by move=> *; exact: cdf_nondecreasing.
  - apply/fin_numPlt/andP; split=>//.
    + by rewrite (lt_le_trans (ltNyr 0%R)) ?lb_ereal_inf//= => l[? _] <-.
    + rewrite (le_lt_trans _ (ltry 1%R))// ereal_inf_le//=.
      exists (cdf X (a + 1)); last exact: cdf_le1.
      by exists (a + 1%R) => //; rewrite in_itv /=; apply/andP; rewrite ltrDl.
have cdf_ns : cdf X (a + n.+1%:R^-1) @[n --> \oo] --> s%:E.
  move/cvge_at_rightP : cdf_s; apply; split=> [n|]; rewrite ?ltrDl //.
  rewrite -[X in _ --> X]addr0; apply: (@cvgD _ R^o); first exact: cvg_cst.
  by rewrite gtr0_cvgV0 ?cvg_shiftS; [exact: cvgr_idn | near=> n].
have cdf_na : cdf X (a + n.+1%:R^-1) @[n --> \oo] --> cdf X a.
  pose F n := X @^-1` `]-oo, a + n.+1%:R^-1%R].
  suff : P (F n) @[n --> \oo] --> P (\bigcap_n F n).
    by rewrite [in X in _ --> X -> _]/F -preimage_bigcap -itvNycEbigcap.
  apply: nonincreasing_cvg_mu => [| | |m n mn].
  - by rewrite -ge0_fin_numE// fin_num_measure//; exact: measurable_funPTI.
  - by move=> ?; exact: measurable_funPTI.
  - by apply: bigcap_measurable => // ? _; exact: measurable_funPTI.
  - apply/subsetPset; apply: preimage_subset; apply: subset_itvl.
    by rewrite bnd_simp lerD2l lef_pV2 ?posrE// ler_nat.
by rewrite -(cvg_unique _ cdf_ns cdf_na).
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := isCumulative.Build R _ (\bar R) (cdf X)
  cdf_nondecreasing cdf_right_continuous.

End cumulative_distribution_function.

Section cdf_of_lebesgue_stieltjes_measure.
Context {R : realType} (f : cumulativeBounded (0:R) (1:R)).
Local Open Scope measure_display_scope.

Let idTR : measurableTypeR R -> R := idfun.

#[local] HB.instance Definition _ :=
  @isMeasurableFun.Build _ _ _ _ idTR (@measurable_id _ _ setT).

Let lsf := lebesgue_stieltjes_measure f.

Lemma cdf_lebesgue_stieltjes_id r : cdf (idTR : {RV lsf >-> R}) r = (f r)%:E.
Proof.
rewrite /= preimage_id itvNybndEbigcup.
have : lsf `]-n%:R, r] @[n --> \oo] --> (f r)%:E.
  suff : ((f r)%:E - (f (-n%:R))%:E)%E @[n --> \oo] --> (f r)%:E.
    apply: cvg_trans; apply: near_eq_cvg; near=> n.
    rewrite /lsf /lebesgue_stieltjes_measure /measure_extension/=.
    rewrite measurable_mu_extE/= ?wlength_itv_bnd//; last exact: is_ocitv.
    by rewrite lerNl; near: n; exact: nbhs_infty_ger.
  rewrite -[X in _ --> X](sube0 (f r)%:E); apply: (cvgeB _ (cvg_cst _ )) => //.
  apply: (cvg_comp _ _ (cvg_comp _ _ _ (cumulativeNy f))) => //.
  by apply: (cvg_comp _ _ cvgr_idn); rewrite ninfty.
have : lsf `]- n%:R, r] @[n --> \oo] --> lsf (\bigcup_n `]-n%:R, r]%classic).
  apply: nondecreasing_cvg_mu => //; first exact: bigcup_measurable.
  by move=> *; apply/subsetPset/subset_itv; rewrite leBSide//= lerN2 ler_nat.
exact: cvg_unique.
Unshelve. all: by end_near. Qed.

End cdf_of_lebesgue_stieltjes_measure.

Section lebesgue_stieltjes_measure_of_cdf.
Context {R : realType} (P : probability (measurableTypeR R) R).
Local Open Scope measure_display_scope.

Let idTR : measurableTypeR R -> R := idfun.

#[local] HB.instance Definition _ :=
  @isMeasurableFun.Build _ _ _ _ idTR (@measurable_id _ _ setT).

Let fcdf r := fine (cdf (idTR : {RV P >-> R}) r).

Let fcdf_nd : nondecreasing fcdf.
Proof.
by move=> *; apply: fine_le; [exact: cdf_fin_num.. | exact: cdf_nondecreasing].
Qed.

Let fcdf_rc : right_continuous fcdf.
Proof.
move=> a; apply: fine_cvg.
by rewrite fineK; [exact: cdf_right_continuous | exact: cdf_fin_num].
Qed.

#[local] HB.instance Definition _ :=
  isCumulative.Build R _ R fcdf fcdf_nd fcdf_rc.

Let fcdf_Ny0 : fcdf @ -oo --> (0:R).
Proof. exact/fine_cvg/cvg_cdfNy0. Qed.

Let fcdf_y1 : fcdf @ +oo --> (1:R).
Proof. exact/fine_cvg/cvg_cdfy1. Qed.

#[local] HB.instance Definition _ :=
  isCumulativeBounded.Build R 0 1 fcdf fcdf_Ny0 fcdf_y1.

Let lscdf := lebesgue_stieltjes_measure fcdf.

Lemma lebesgue_stieltjes_cdf_id (A : set _) (mA : measurable A) : lscdf A = P A.
Proof.
apply: lebesgue_stieltjes_measure_unique => [I [[a b]]/= _ <- | //].
rewrite /lebesgue_stieltjes_measure /measure_extension/=.
rewrite measurable_mu_extE/=; last exact: is_ocitv.
have [ab | ba] := leP a b; last first.
  by rewrite set_itv_ge ?wlength0 ?measure0// bnd_simp -leNgt ltW.
rewrite wlength_itv_bnd// EFinB !fineK ?cdf_fin_num//.
rewrite /cdf /distribution /pushforward !preimage_id.
have : `]a, b]%classic = `]-oo, b] `\` `]-oo, a] => [|->].
  by rewrite -[RHS]setCK setCD setCitvl setUC -[LHS]setCK setCitv.
rewrite measureD ?setIidr//; first exact: subset_itvl.
by rewrite -ge0_fin_numE// fin_num_measure.
Qed.

End lebesgue_stieltjes_measure_of_cdf.

Definition ccdf d (T : measurableType d) (R : realType) (P : probability T R)
  (X : {RV P >-> R}) (r : R) := distribution P X `]r, +oo[.

Section complementary_cumulative_distribution_function.
Context d {T : measurableType d} {R : realType} (P : probability T R).
Variable X : {RV P >-> R}.
Local Open Scope ereal_scope.

Lemma cdf_ccdf_1 r : cdf X r + ccdf X r = 1.
Proof.
rewrite /cdf/ccdf -measureU//= -eq_opE; last exact: disjoint_rays.
by rewrite itv_setU_setT probability_setT.
Qed.

Corollary ccdf_cdf_1 r : ccdf X r + cdf X r = 1.
Proof. by rewrite -(cdf_ccdf_1 r) addeC. Qed.

Corollary ccdf_1_cdf r : ccdf X r = 1 - cdf X r.
Proof. by rewrite -(ccdf_cdf_1 r) addeK ?cdf_fin_num. Qed.

Lemma ccdf_fin_num r : ccdf X r \is a fin_num.
Proof. by rewrite ccdf_1_cdf fin_numB cdf_fin_num -fine1. Qed.

Corollary cdf_1_ccdf r : cdf X r = 1 - ccdf X r.
Proof. by rewrite -(cdf_ccdf_1 r) addeK ?ccdf_fin_num. Qed.

Lemma ccdf_nonincreasing : nonincreasing_fun (ccdf X).
Proof. by move=> r s rs; rewrite le_measure ?inE//; exact: subitvPl. Qed.

Lemma cvg_ccdfy0 : ccdf X @ +oo%R --> 0.
Proof.
have : 1 - cdf X r @[r --> +oo%R] --> 1 - 1.
  by apply: cvgeB; [| exact: cvg_cst | exact: cvg_cdfy1].
by rewrite subee// (eq_cvg _ _ ccdf_1_cdf).
Qed.

Lemma cvg_ccdfNy1 : ccdf X @ -oo%R --> 1.
Proof.
have : 1 - cdf X r @[r --> -oo%R] --> 1 - 0.
  by apply: cvgeB; [| exact: cvg_cst | exact: cvg_cdfNy0].
by rewrite sube0 (eq_cvg _ _ ccdf_1_cdf).
Qed.

Lemma ccdf_right_continuous : right_continuous (ccdf X).
Proof.
move=> r.
have : 1 - cdf X s @[s --> r^'+] --> 1 - cdf X r.
  by apply: cvgeB; [| exact: cvg_cst | exact: cdf_right_continuous].
by rewrite ccdf_1_cdf (eq_cvg _ _ ccdf_1_cdf).
Qed.

End complementary_cumulative_distribution_function.

HB.lock Definition expectation {d} {T : measurableType d} {R : realType}
  (P : probability T R) (X : T -> R) := (\int[P]_w (X w)%:E)%E.
Canonical expectation_unlockable := Unlockable expectation.unlock.
Arguments expectation {d T R} P _%_R.
Notation "''E_' P [ X ]" := (@expectation _ _ _ P X) : ereal_scope.

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_def (X : {RV P >-> R}) : 'E_P[X] = (\int[P]_w (X w)%:E)%E.
Proof. by rewrite unlock. Qed.

Lemma expectation_fin_num (X : T -> R) : X \in Lfun P 1 ->
  'E_P[X] \is a fin_num.
Proof.
by move=> ?; rewrite unlock integrable_fin_num//; exact/Lfun1_integrable.
Qed.

Lemma expectation_cst r : 'E_P[cst r] = r%:E.
Proof. by rewrite unlock/= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) : 'E_P[\1_A] = P A.
Proof. by rewrite unlock integral_indic// setIT. Qed.

Lemma integrable_expectation (X : {RV P >-> R})
  (iX : P.-integrable [set: T] (EFin \o X)) : `| 'E_P[X] | < +oo.
Proof.
move: iX => /integrableP[? Xoo]; rewrite (le_lt_trans _ Xoo)// unlock.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationZl (X : T -> R) (k : R) : X \in Lfun P 1 ->
  'E_P[k \o* X] = k%:E * 'E_P[X].
Proof.
by move=> ?; rewrite unlock muleC -integralZr//; exact/Lfun1_integrable.
Qed.

Lemma expectation_ge0 (X : T -> R) : (forall x, 0 <= X x)%R ->
  0 <= 'E_P[X].
Proof.
by move=> ?; rewrite unlock integral_ge0// => x _; rewrite lee_fin.
Qed.

Lemma expectation_le (X Y : T -> R) :
    measurable_fun [set: T] X -> measurable_fun [set: T] Y ->
    (forall x, 0 <= X x)%R -> (forall x, 0 <= Y x)%R ->
  {ae P, (forall x, X x <= Y x)%R} -> 'E_P[X] <= 'E_P[Y].
Proof.
move=> mX mY X0 Y0 XY; rewrite unlock ae_ge0_le_integral => //.
- by move=> t _; apply: X0.
- exact/measurable_EFinP.
- by move=> t _; apply: Y0.
- exact/measurable_EFinP.
- move: XY => [N [mN PN XYN]]; exists N; split => // t /= h.
  by apply: XYN => /=; apply: contra_not h; rewrite lee_fin.
Qed.

Lemma expectationD (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
  'E_P[X \+ Y] = 'E_P[X] + 'E_P[Y].
Proof.
by move=> ? ?; rewrite unlock integralD_EFin//; exact/Lfun1_integrable.
Qed.

Lemma expectationB (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
  'E_P[X \- Y] = 'E_P[X] - 'E_P[Y].
Proof.
by move=> ? ?; rewrite unlock integralB_EFin//; exact/Lfun1_integrable.
Qed.

Lemma expectation_sum (X : seq (T -> R)) :
    (forall Xi, Xi \in X -> Xi \in Lfun P 1) ->
  'E_P[\sum_(Xi <- X) Xi] = \sum_(Xi <- X) 'E_P[Xi].
Proof.
elim: X => [|X0 X IHX] intX; first by rewrite !big_nil expectation_cst.
rewrite !big_cons expectationD; last 2 first.
  by rewrite intX// mem_head.
  by rewrite big_seq rpred_sum// => Y YX/=; rewrite intX// inE YX orbT.
by rewrite IHX//= => Xi XiX; rewrite intX// inE XiX orbT.
Qed.

End expectation_lemmas.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `expectationZl`")]
Notation expectationM := expectationZl (only parsing).

HB.lock Definition covariance {d} {T : measurableType d} {R : realType}
    (P : probability T R) (X Y : T -> R) :=
  'E_P[(X \- cst (fine 'E_P[X])) * (Y \- cst (fine 'E_P[Y]))]%E.
Canonical covariance_unlockable := Unlockable covariance.unlock.
Arguments covariance {d T R} P _%_R _%_R.

Hint Extern 0 (fin_num_fun _) =>
  (apply: fin_num_measure) : core.

Section covariance_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma covarianceE (X Y : T -> R) :
    X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P X Y = 'E_P[X * Y] - 'E_P[X] * 'E_P[Y].
Proof.
move=> l1X l1Y l1XY.
rewrite unlock [X in 'E_P[X]](_ : _ = (X \* Y \- fine 'E_P[X] \o* Y
    \- fine 'E_P[Y] \o* X \+ fine ('E_P[X] * 'E_P[Y]) \o* cst 1)%R); last first.
  apply/funeqP => x /=; rewrite mulrDr !mulrDl/= mul1r.
  rewrite fineM ?expectation_fin_num// mulrNN addrA.
  by rewrite mulrN mulNr [Z in (X x * Y x - Z)%R]mulrC.
rewrite expectationD/= ?rpredB//= ?Lfun_scale ?Lfun_cst//.
rewrite 2?expectationB//= ?rpredB ?Lfun_scale// 3?expectationZl//= ?Lfun_cst//.
rewrite expectation_cst mule1 fineM ?expectation_fin_num// EFinM.
rewrite !fineK ?expectation_fin_num//.
by rewrite muleC subeK ?fin_numM ?expectation_fin_num.
Qed.

Lemma covarianceC (X Y : T -> R) : covariance P X Y = covariance P Y X.
Proof.
by rewrite unlock; congr expectation; apply/funeqP => x /=; rewrite mulrC.
Qed.

Lemma covariance_fin_num (X Y : T -> R) :
    X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P X Y \is a fin_num.
Proof.
by move=> ? ? ?; rewrite covarianceE// fin_numB fin_numM expectation_fin_num.
Qed.

Lemma covariance_cst_l c (X : T -> R) : covariance P (cst c) X = 0.
Proof.
rewrite unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funeqP => x; rewrite /GRing.mul/= subrr mul0r.
Qed.

Lemma covariance_cst_r (X : T -> R) c : covariance P X (cst c) = 0.
Proof. by rewrite covarianceC covariance_cst_l. Qed.

Lemma covarianceZl a (X Y : T -> R) :
    X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P (a \o* X)%R Y = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have aXY : (a \o* X * Y = a \o* (X * Y))%R by apply/funeqP => x; rewrite mulrAC.
rewrite [LHS]covarianceE => [||//|] //=; last 2 first.
- by rewrite Lfun_scale.
- by rewrite aXY Lfun_scale.
rewrite covarianceE// aXY !expectationZl//.
by rewrite -muleA -muleBr// fin_num_adde_defr// expectation_fin_num.
Qed.

Lemma covarianceZr a (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P X (a \o* Y)%R = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
by rewrite [in RHS]covarianceC covarianceC covarianceZl; last rewrite mulrC.
Qed.

Lemma covarianceNl (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P (\- X)%R Y = - covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have -> : (\- X = -1 \o* X)%R by apply/funeqP => x /=; rewrite mulrN mulr1.
by rewrite covarianceZl// EFinN mulNe mul1e.
Qed.

Lemma covarianceNr (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P X (\- Y)%R = - covariance P X Y.
Proof. by move=> X1 Y1 XY1; rewrite !(covarianceC X) covarianceNl 1?mulrC. Qed.

Lemma covarianceNN (X Y : T -> R) : X \in Lfun P 1 -> Y \in Lfun P 1 ->
    (X * Y)%R \in Lfun P 1 ->
  covariance P (\- X)%R (\- Y)%R = covariance P X Y.
Proof.
by move=> ? ? ?; rewrite covarianceNl//= ?covarianceNr ?oppeK ?mulrN//= ?rpredN.
Qed.

Lemma covarianceDl (X Y Z : T -> R) :
    X \in Lfun P 2%:E -> Y \in Lfun P 2%:E -> Z \in Lfun P 2%:E ->
  covariance P (X \+ Y)%R Z = covariance P X Z + covariance P Y Z.
Proof.
move=> X2 Y2 Z2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have X1 := Lfun_subset12 Pfin X2.
have Y1 := Lfun_subset12 Pfin Y2.
have Z1 := Lfun_subset12 Pfin Z2.
have XY1 := Lfun2_mul_Lfun1 X2 Y2.
have YZ1 := Lfun2_mul_Lfun1 Y2 Z2.
have XZ1 := Lfun2_mul_Lfun1 X2 Z2.
rewrite [LHS]covarianceE//= ?mulrDl ?compreDr ?rpredD//= 2?expectationD//=.
rewrite muleDl ?fin_num_adde_defr ?expectation_fin_num//.
rewrite oppeD ?fin_num_adde_defr ?fin_numM ?expectation_fin_num//.
by rewrite addeACA 2?covarianceE.
Qed.

Lemma covarianceDr (X Y Z : T -> R) :
    X \in Lfun P 2%:E -> Y \in Lfun P 2%:E -> Z \in Lfun P 2%:E ->
  covariance P X (Y \+ Z)%R = covariance P X Y + covariance P X Z.
Proof.
by move=> X2 Y2 Z2; rewrite covarianceC covarianceDl ?(covarianceC X) 1?mulrC.
Qed.

Lemma covarianceBl (X Y Z : T -> R) :
    X \in Lfun P 2%:E -> Y \in Lfun P 2%:E -> Z \in Lfun P 2%:E ->
  covariance P (X \- Y)%R Z = covariance P X Z - covariance P Y Z.
Proof.
move=> X2 Y2 Z2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have Y1 := Lfun_subset12 Pfin Y2.
have Z1 := Lfun_subset12 Pfin Z2.
have YZ1 := Lfun2_mul_Lfun1 Y2 Z2.
by rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R covarianceDl ?covarianceNl ?rpredN.
Qed.

Lemma covarianceBr (X Y Z : T -> R) :
    X \in Lfun P 2%:E -> Y \in Lfun P 2%:E -> Z \in Lfun P 2%:E ->
  covariance P X (Y \- Z)%R = covariance P X Y - covariance P X Z.
Proof.
move=> X2 Y2 Z2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have Y1 := Lfun_subset12 Pfin Y2.
have Z1 := Lfun_subset12 Pfin Z2.
have YZ1 := Lfun2_mul_Lfun1 Y2 Z2.
by rewrite !(covarianceC X) covarianceBl 1?(mulrC _ X).
Qed.

End covariance_lemmas.

Section variance.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : T -> R) := covariance P X X.
Local Notation "''V_' P [ X ]" := (variance X).

Lemma varianceE (X : T -> R) : X \in Lfun P 2%:E ->
  'V_P[X] = 'E_P[X ^+ 2] - ('E_P[X]) ^+ 2.
Proof.
move=> X2; rewrite /variance.
by rewrite covarianceE ?Lfun2_mul_Lfun1// Lfun_subset12 ?fin_num_measure.
Qed.

Lemma variance_fin_num (X : T -> R) : X \in Lfun P 2%:E ->
  'V_P[X] \is a fin_num.
Proof.
move=> X2.
by rewrite covariance_fin_num ?Lfun2_mul_Lfun1// Lfun_subset12 ?fin_num_measure.
Qed.

Lemma variance_ge0 (X : T -> R) : 0 <= 'V_P[X].
Proof.
by rewrite /variance unlock; apply: expectation_ge0 => x; exact: sqr_ge0.
Qed.

Lemma variance_cst r : 'V_P[cst r] = 0%E.
Proof.
rewrite /variance unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funext => x; rewrite /GRing.exp/GRing.mul/= subrr mulr0.
Qed.

Lemma varianceZ a (X : T -> R) : X \in Lfun P 2%:E ->
  'V_P[(a \o* X)%R] = (a ^+ 2)%:E * 'V_P[X].
Proof.
move=> X2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have X1 := Lfun_subset12 Pfin X2.
rewrite /variance covarianceZl//=.
- by rewrite covarianceZr// ?muleA ?EFinM// Lfun2_mul_Lfun1.
- by rewrite Lfun_scale.
- by rewrite Lfun2_mul_Lfun1// Lfun_scale// ler1n.
Qed.

Lemma varianceN (X : T -> R) : X \in Lfun P 2%:E -> 'V_P[(\- X)%R] = 'V_P[X].
Proof.
move=> X2; rewrite /variance.
by rewrite covarianceNN ?Lfun2_mul_Lfun1 ?Lfun_subset12 ?fin_num_measure.
Qed.

Lemma varianceD (X Y : T -> R) : X \in Lfun P 2%:E -> Y \in Lfun P 2%:E ->
  'V_P[X \+ Y]%R = 'V_P[X] + 'V_P[Y] + 2%:E * covariance P X Y.
Proof.
move=> X2 Y2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have X1 := Lfun_subset12 Pfin X2.
have Y1 := Lfun_subset12 Pfin Y2.
have XY1 := Lfun2_mul_Lfun1 X2 Y2.
rewrite -['V_P[_]]/(covariance P (X \+ Y)%R (X \+ Y)%R).
rewrite covarianceDl ?rpredD ?lee1n//= covarianceDr// covarianceDr//.
rewrite (covarianceC P Y X) [LHS]addeA [LHS](ACl (1*4*(2*3)))/=.
by rewrite -[2%R]/(1 + 1)%R EFinD muleDl ?mul1e// covariance_fin_num.
Qed.

Lemma varianceB (X Y : T -> R) : X \in Lfun P 2%:E -> Y \in Lfun P 2%:E ->
  'V_P[(X \- Y)%R] = 'V_P[X] + 'V_P[Y] - 2%:E * covariance P X Y.
Proof.
move=> X2 Y2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have X1 := Lfun_subset12 Pfin X2.
have Y1 := Lfun_subset12 Pfin Y2.
have XY1 := Lfun2_mul_Lfun1 X2 Y2.
rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R.
by rewrite varianceD/= ?varianceN ?covarianceNr ?muleN ?rpredN.
Qed.

Lemma varianceD_cst_l c (X : T -> R) : X \in Lfun P 2%:E ->
  'V_P[(cst c \+ X)%R] = 'V_P[X].
Proof.
move=> X2.
by rewrite varianceD ?Lfun_cst// variance_cst add0e covariance_cst_l mule0 adde0.
Qed.

Lemma varianceD_cst_r (X : T -> R) c : X \in Lfun P 2%:E ->
  'V_P[(X \+ cst c)%R] = 'V_P[X].
Proof.
move=> X2.
have -> : (X \+ cst c = cst c \+ X)%R by apply/funeqP => x /=; rewrite addrC.
exact: varianceD_cst_l.
Qed.

Lemma varianceB_cst_l c (X : T -> R) : X \in Lfun P 2%:E ->
  'V_P[(cst c \- X)%R] = 'V_P[X].
Proof.
move=> X2; rewrite -[(cst c \- X)%R]/(cst c \+ (\- X))%R.
by rewrite varianceD_cst_l/= ?rpredN// varianceN.
Qed.

Lemma varianceB_cst_r (X : T -> R) c : X \in Lfun P 2%:E ->
  'V_P[(X \- cst c)%R] = 'V_P[X].
Proof.
by move=> X2; rewrite -[(X \- cst c)%R]/(X \+ (cst (- c)))%R varianceD_cst_r.
Qed.

Lemma covariance_le (X Y : T -> R) : X \in Lfun P 2%:E -> Y \in Lfun P 2%:E ->
  covariance P X Y <= sqrte 'V_P[X] * sqrte 'V_P[Y].
Proof.
move=> X2 Y2.
have Pfin : P setT \is a fin_num := fin_num_measure P _ measurableT.
have X1 := Lfun_subset12 Pfin X2.
have Y1 := Lfun_subset12 Pfin Y2.
have XY1 := Lfun2_mul_Lfun1 X2 Y2.
rewrite -sqrteM ?variance_ge0//.
rewrite lee_sqrE ?sqrte_ge0// sqr_sqrte ?mule_ge0 ?variance_ge0//.
rewrite -(fineK (variance_fin_num X2)) -(fineK (variance_fin_num Y2)).
rewrite -(fineK (covariance_fin_num X1 Y1 XY1)).
rewrite -EFin_expe -EFinM lee_fin -(@ler_pM2l _ 4) ?ltr0n// [leRHS]mulrA.
rewrite [in leLHS](_ : 4 = 2 * 2)%R -natrM// [in leLHS]natrM mulrACA -expr2.
rewrite -subr_le0.
set a := fine (variance X).
set b := (2 * fine (covariance P X Y))%R.
set c := fine (variance Y).
pose p := Poly [:: c; b; a].
have -> : a = p`_2 by rewrite !coefE.
have -> : b = p`_1 by rewrite !coefE.
have -> : c = p`_0 by rewrite !coefE.
rewrite deg_le2_poly_ge0 ?size_Poly// => r.
rewrite horner_Poly/= mul0r add0r mulrDl -mulrA -expr2.
rewrite -lee_fin !EFinD EFinM fineK ?variance_fin_num// muleC -varianceZ//.
rewrite 2!EFinM ?fineK ?variance_fin_num// ?covariance_fin_num//.
rewrite -muleA [_ * r%:E]muleC -covarianceZl//.
rewrite addeAC -varianceD ?variance_ge0//=.
by rewrite Lfun_scale// ler1n.
Qed.

End variance.
Notation "'V_ P [ X ]" := (variance P X).

Definition mmt_gen_fun d (T : measurableType d) (R : realType)
  (P : probability T R) (X : T -> R) (t : R) := ('E_P[expR \o t \o* X])%E.
Notation "'M_ P X" := (@mmt_gen_fun _ _ _ P X).

Section markov_chebyshev_cantelli.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma markov (X : {RV P >-> R}) (f : R -> R) (eps : R) : (0 < eps)%R ->
    measurable_fun [set: R] f -> (forall r, 0 <= r -> 0 <= f r)%R ->
    {in Num.nneg &, {homo f : x y / x <= y}}%R ->
  (f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ] <=
    'E_P[f \o (fun x => `| x |%R) \o X].
Proof.
move=> e0 mf f0 f_nd; rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse _ _ _ P _ measurableT (EFin \o X)
  eps (er_map f) _ _ _ _ e0)) => //=.
- exact: measurable_er_map.
- by case => //= r _; exact: f0.
- move=> [x| |] [y| |]; rewrite !inE/= !in_itv/= ?andbT ?lee_fin ?leey//.
  by move=> ? ? ?; rewrite f_nd.
- exact/measurable_EFinP.
- by rewrite unlock.
Qed.

Lemma chernoff (X : {RV P >-> R}) (r a : R) : (0 < r)%R ->
  P [set x | X x >= a]%R <= 'M_P X r * (expR (- (r * a)))%:E.
Proof.
move=> t0; rewrite /mmt_gen_fun.
have -> : expR \o r \o* X = (normr \o normr) \o (expR \o r \o* X).
  by apply: funext => t /=; rewrite normr_id ger0_norm ?expR_ge0.
rewrite expRN lee_pdivlMr ?expR_gt0//.
rewrite (le_trans _ (markov _ (expR_gt0 (r * a)) _ _ _))//; last first.
  exact: (monoW_in (@ger0_le_norm _)).
rewrite ger0_norm ?expR_ge0// muleC lee_pmul2l// ?lte_fin ?expR_gt0//.
rewrite [X in _ <= P X](_ : _ = [set x | a <= X x]%R)//; apply: eq_set => t/=.
by rewrite ger0_norm ?expR_ge0// lee_fin ler_expR  mulrC ler_pM2r.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E_P[X])|)%R ] <= (eps ^- 2)%:E * 'V_P[X].
Proof.
move => heps; have [->|hv] := eqVneq 'V_P[X] +oo.
  by rewrite mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[Y ^+ 2].
  rewrite -lee_pdivrMl; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  apply: (@le_trans _ _ ('E_P[(@GRing.exp R ^~ 2%N \o normr) \o Y])).
    apply: (@markov Y (@GRing.exp R ^~ 2%N)) => //.
    - by move=> r _; exact: sqr_ge0.
    - move=> x y; rewrite !nnegrE => x0 y0.
      by rewrite ler_sqr.
  apply: expectation_le.
    - by apply: measurableT_comp => //; exact: measurableT_comp.
  - by [].
  - by move=> x /=; exact: sqr_ge0.
  - by move=> x /=; exact: sqr_ge0.
  - by apply/aeW => t /=; rewrite real_normK// num_real.
have := h (X \- cst (fine ('E_P[X])))%R.
by move=> /le_trans; apply; rewrite /variance [in leRHS]unlock.
Qed.

Lemma cantelli (X : {RV P >-> R}) (lambda : R) :
    (X : T -> R) \in Lfun P 2%:E -> (0 < lambda)%R ->
  P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
  <= (fine 'V_P[X] / (fine 'V_P[X] + lambda^2))%:E.
Proof.
move=> /[dup] X2.
move=> /(Lfun_subset12 (fin_num_measure P _ measurableT)) X1 lambda_gt0.
have finEK : (fine 'E_P[X])%:E = 'E_P[X] by rewrite fineK ?expectation_fin_num.
have finVK : (fine 'V_P[X])%:E = 'V_P[X] by rewrite fineK ?variance_fin_num.
pose Y := (X \- cst (fine 'E_P[X]))%R.
have Y2 : (Y : T -> R) \in Lfun P 2%:E.
  by rewrite /Y rpredB ?lee1n//= => _; rewrite Lfun_cst.
have EY : 'E_P[Y] = 0.
  rewrite expectationB ?Lfun_cst//= expectation_cst.
  by rewrite finEK subee// expectation_fin_num.
have VY : 'V_P[Y] = 'V_P[X] by rewrite varianceB_cst_r.
have le (u : R) : (0 <= u)%R ->
    P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
    <= ((fine 'V_P[X] + u^2) / (lambda + u)^2)%:E.
  move=> uge0; rewrite EFinM.
  have -> : (fine 'V_P[X] + u^2)%:E = 'E_P[(Y \+ cst u)^+2]%R.
    rewrite -VY -[RHS](@subeK _ _ (('E_P[(Y \+ cst u)%R])^+2)); last first.
      rewrite fin_numX// expectation_fin_num//= rpredD ?Lfun_cst//.
      by rewrite rpredB// Lfun_cst.
    rewrite -varianceE/=; last first.
      by rewrite rpredD ?lee1n//= => _; rewrite Lfun_cst.
    rewrite -expe2 expectationD/= ?Lfun_cst//; last by rewrite rpredB ?Lfun_cst.
    rewrite EY// add0e expectation_cst -EFinM.
    by rewrite (varianceD_cst_r _ Y2) EFinD fineK ?variance_fin_num.
  have le : [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
      `<=` [set x | ((lambda + u)^2)%:E <= ((Y x + u)^+2)%:E].
    move=> x /= le; rewrite lee_fin; apply: lerXn2r.
    - exact: addr_ge0 (ltW lambda_gt0) _.
    - apply/(addr_ge0 _ uge0)/(le_trans (ltW lambda_gt0) _).
      by rewrite -lee_fin EFinB finEK.
    - by rewrite lerD2r -lee_fin EFinB finEK.
  apply: (le_trans (le_measure _ _ _ le)).
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    apply: emeasurable_funB=> //.
    by move/Lfun1_integrable : X1 => /measurable_int.
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    rewrite measurable_EFinP [X in measurable_fun _ X](_ : _ =
      (fun x => x ^+ 2) \o (fun x => Y x + u))%R//.
    by apply/measurableT_comp => //; exact/measurable_funD.
  set eps := ((lambda + u) ^ 2)%R.
  have peps : (0 < eps)%R by rewrite exprz_gt0 ?ltr_wpDr.
  rewrite (lee_pdivlMr _ _ peps) muleC.
  under eq_set => x.
    rewrite -[leRHS]gee0_abs ?lee_fin ?sqr_ge0 -?lee_fin => [|//].
    rewrite -[(_ ^+ 2)%R]/(((Y \+ cst u) ^+ 2) x)%R; over.
  rewrite -[X in X%:E * _]gtr0_norm => [|//].
  apply: (le_trans (markov _ peps _ _ _)) => //=.
    by move=> x y /[!nnegrE] /ger0_norm-> /ger0_norm->.
  rewrite -/Y le_eqVlt; apply/orP; left; apply/eqP; congr expectation.
  by apply/funeqP => x /=; rewrite -expr2 normr_id ger0_norm ?sqr_ge0.
pose u0 := (fine 'V_P[X] / lambda)%R.
have u0ge0 : (0 <= u0)%R.
  by apply: divr_ge0 (ltW lambda_gt0); rewrite -lee_fin finVK variance_ge0.
apply: le_trans (le _ u0ge0) _; rewrite lee_fin le_eqVlt; apply/orP; left.
rewrite eqr_div; [|apply: lt0r_neq0..]; last 2 first.
- by rewrite exprz_gt0 -1?[ltLHS]addr0 ?ltr_leD.
- by rewrite ltr_wpDl ?fine_ge0 ?variance_ge0 ?exprz_gt0.
apply/eqP; have -> : fine 'V_P[X] = (u0 * lambda)%R.
  by rewrite /u0 -mulrA mulVf ?mulr1 ?gt_eqF.
by rewrite -mulrDl -mulrDr (addrC u0) [in RHS](mulrAC u0) -exprnP expr2 !mulrA.
Qed.

End markov_chebyshev_cantelli.

HB.mixin Record MeasurableFun_isDiscrete d d' (T : measurableType d)
    (T' : measurableType d') (X : T -> T') of @MeasurableFun d d' T T' X := {
  countable_range : countable (range X)
}.

HB.structure Definition discreteMeasurableFun d d' (T : measurableType d)
    (T' : measurableType d') := {
  X of isMeasurableFun d d' T T' X & MeasurableFun_isDiscrete d d' T T' X
}.

Notation "{ 'dmfun' aT >-> T }" :=
  (@discreteMeasurableFun.type _ _ aT T) : form_scope.

Definition discrete_random_variable d d' (T : measurableType d)
    (T' : measurableType d') (R : realType) (P : probability T R) :=
  {dmfun T >-> T'}.

Notation "{ 'dRV' P >-> T }" :=
  (@discrete_random_variable _ _ _ T _ P) : form_scope.

Section dRV_definitions.
Context {d} {d'} {T : measurableType d} {T' : measurableType d'} {R : realType}
  (P : probability T R).

Lemma dRV_dom_enum (X : {dRV P >-> T'}) :
  { B : set nat & {splitbij B >-> range X}}.
Proof.
have /countable_bijP/cid[B] := @countable_range _ _ _ _ X.
move/card_esym/ppcard_eqP/unsquash => f.
exists B; exact: f.
Qed.

Definition dRV_dom (X : {dRV P >-> T'}) : set nat := projT1 (dRV_dom_enum X).

Definition dRV_enum (X : {dRV P >-> T'}) : {splitbij (dRV_dom X) >-> range X} :=
  projT2 (dRV_dom_enum X).

Definition enum_prob (X : {dRV P >-> T'}) :=
  (fun k => P (X @^-1` [set dRV_enum X k])) \_ (dRV_dom X).

End dRV_definitions.

Section distribution_dRV.
Local Open Scope ereal_scope.
Context d d' (T : measurableType d) (T' : measurableType d') (R : realType)
  (P : probability T R).
Variable X : {dRV P >-> T'}.

Lemma distribution_dRV_enum (n : nat) : n \in dRV_dom X ->
  distribution P X [set dRV_enum X n] = enum_prob X n.
Proof.
by move=> nX; rewrite /distribution/= /enum_prob/= patchE nX.
Qed.

Hypothesis measurable_set1T' : forall x : T', measurable [set x].

Lemma distribution_dRV A : measurable A ->
  distribution P X A = \sum_(k <oo) enum_prob X k * \d_ (dRV_enum X k) A.
Proof.
move=> mA; rewrite /distribution /pushforward.
have mAX i : dRV_dom X i -> measurable (X @^-1` (A `&` [set dRV_enum X i])).
  move=> domXi; rewrite preimage_setI.
  by apply: measurableI; rewrite //-[X in _ X]setTI; exact/measurable_funP.
have tAX : trivIset (dRV_dom X) (fun k => X @^-1` (A `&` [set dRV_enum X k])).
  under eq_fun do rewrite preimage_setI; rewrite -/(trivIset _ _).
  apply: trivIset_setIl; apply/trivIsetP => i j iX jX /eqP ij.
  rewrite -preimage_setI (_ : _ `&` _ = set0)//.
  by apply/seteqP; split => //= x [] -> {x} /inj; rewrite inE inE => /(_ iX jX).
have := measure_bigcup P _ (fun k => X @^-1` (A `&` [set dRV_enum X k])) mAX tAX.
rewrite -preimage_bigcup => {mAX tAX}PXU.
rewrite -{1}(setIT A) -(setUv (\bigcup_(i in dRV_dom X) [set dRV_enum X i])).
rewrite setIUr preimage_setU measureU; last 3 first.
  - by rewrite preimage_setI; apply: measurableI; rewrite //-[X in _ X]setTI;
      apply/measurable_funP => //; exact: bigcup_measurable.
  - by rewrite preimage_setI; apply: measurableI; rewrite //-[X in _ X]setTI;
      apply/measurable_funP => //; apply: measurableC; exact: bigcup_measurable.
  - by rewrite -preimage_setI -setIIr setIA setICK preimage_set0.
rewrite [X in _ + X = _](_ : _ = 0) ?adde0; last first.
  rewrite (_ : _ @^-1` _ = set0) ?measure0//; apply/disjoints_subset => x AXx.
  rewrite setCK /bigcup /=; exists ((dRV_enum X)^-1 (X x))%function.
    exact: funS.
  by rewrite invK// inE.
rewrite setI_bigcupr; etransitivity; first exact: PXU.
rewrite eseries_mkcond; apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => nX; rewrite ?mul0e//.
rewrite diracE; have [kA|] := boolP (_ \in A).
  by rewrite mule1 setIidr// => _ /= ->; exact: set_mem.
rewrite notin_setE => kA.
rewrite mule0 (disjoints_subset _ _).2 ?preimage_set0 ?measure0//.
by apply: subsetCr; rewrite sub1set inE.
Qed.

Lemma sum_enum_prob : \sum_(n <oo) (enum_prob X) n = 1.
Proof.
have := distribution_dRV measurableT.
rewrite probability_setT/= => /esym; apply: eq_trans.
by rewrite [RHS]eseries_mkcond; apply: eq_eseriesr => k _; rewrite diracT mule1.
Qed.

End distribution_dRV.

Section discrete_distribution.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma dRV_expectation (X : {dRV P >-> R}) :
  P.-integrable [set: T] (EFin \o X) ->
  'E_P[X] = \sum_(n <oo) enum_prob X n * (dRV_enum X n)%:E.
Proof.
move=> ix; rewrite unlock.
rewrite -[in LHS](_ : \bigcup_k (if k \in dRV_dom X then
    X @^-1` [set dRV_enum X k] else set0) = setT); last first.
  apply/seteqP; split => // t _.
  exists ((dRV_enum X)^-1%function (X t)) => //.
  case: ifPn=> [_|].
    by rewrite invK// inE.
  by rewrite notin_setE/=; apply; apply: funS.
have tA : trivIset (dRV_dom X) (fun k => [set dRV_enum X k]).
  by move=> i j iX jX [r [/= ->{r}]] /inj; rewrite !inE; exact.
have {tA}/trivIset_mkcond tXA :
    trivIset (dRV_dom X) (fun k => X @^-1` [set dRV_enum X k]).
  apply/trivIsetP => /= i j iX jX ij.
  move/trivIsetP : tA => /(_ i j iX jX) Aij.
  by rewrite -preimage_setI Aij ?preimage_set0.
rewrite integral_bigcup //; last 2 first.
  - by move=> k; case: ifPn.
  - apply: (integrableS measurableT) => //.
    by rewrite -bigcup_mkcond; exact: bigcup_measurable.
transitivity (\sum_(i <oo)
  \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
    (dRV_enum X i)%:E).
  apply: eq_eseriesr => i _; case: ifPn => iX.
    by apply: eq_integral => t; rewrite in_setE/= => ->.
  by rewrite !integral_set0.
transitivity (\sum_(i <oo) (dRV_enum X i)%:E *
  \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
    1).
  apply: eq_eseriesr => i _; rewrite -integralZl//; last 2 first.
    - by case: ifPn.
    - apply/integrableP; split => //.
      rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
      rewrite integral_cst//; last by case: ifPn.
      rewrite mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
      by case: ifPn => // _; exact: probability_le1.
  by apply: eq_integral => y _; rewrite mule1.
apply: eq_eseriesr => k _; case: ifPn => kX.
  rewrite /= integral_cst//= mul1e probability_distribution muleC.
  by rewrite distribution_dRV_enum.
by rewrite integral_set0 mule0 /enum_prob patchE (negbTE kX) mul0e.
Qed.

Definition pmf (X : {RV P >-> R}) (r : R) : R := fine (P (X @^-1` [set r])).

Lemma expectation_pmf (X : {dRV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> 'E_P[X] =
  \sum_(n <oo | n \in dRV_dom X) (pmf X (dRV_enum X n))%:E * (dRV_enum X n)%:E.
Proof.
move=> iX; rewrite dRV_expectation// [in RHS]eseries_mkcond.
apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => kX; last by rewrite mul0e.
by rewrite /pmf fineK// fin_num_measure.
Qed.

End discrete_distribution.

Section bernoulli_pmf.
Context {R : realType} (p : R).
Local Open Scope ring_scope.

Definition bernoulli_pmf b := if b then p else 1 - p.

Lemma bernoulli_pmf_ge0 (p01 : 0 <= p <= 1) b : 0 <= bernoulli_pmf b.
Proof.
rewrite /bernoulli_pmf.
by move: p01 => /andP[p0 p1]; case: ifPn => // _; rewrite subr_ge0.
Qed.

Lemma bernoulli_pmf1 (p01 : 0 <= p <= 1) :
  \sum_(i \in [set: bool]) (bernoulli_pmf i)%:E = 1%E.
Proof.
rewrite setT_bool fsbigU//=; last by move=> x [/= ->].
by rewrite !fsbig_set1/= -EFinD addrCA subrr addr0.
Qed.

End bernoulli_pmf.

Lemma measurable_bernoulli_pmf {R : realType} D n :
  measurable_fun D (@bernoulli_pmf R ^~ n).
Proof.
by apply/measurable_funTS/measurable_fun_if => //=; exact: measurable_funB.
Qed.

Definition bernoulli {R : realType} (p : R) : set bool -> \bar R := fun A =>
  if (0 <= p <= 1)%R then \sum_(b \in A) (bernoulli_pmf p b)%:E else \d_false A.

Section bernoulli.
Context {R : realType} (p : R).

Local Notation bernoulli := (bernoulli p).

Let bernoulli0 : bernoulli set0 = 0.
Proof.
by rewrite /bernoulli; case: ifPn => // p01; rewrite fsbig_set0.
Qed.

Let bernoulli_ge0 U : (0 <= bernoulli U)%E.
Proof.
rewrite /bernoulli; case: ifPn => // p01.
rewrite fsbig_finite//= sumEFin lee_fin.
by apply: sumr_ge0 => /= b _; exact: bernoulli_pmf_ge0.
Qed.

Let bernoulli_sigma_additive : semi_sigma_additive bernoulli.
Proof.
move=> F mF tF mUF; rewrite /bernoulli; case: ifPn => p01; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _.
  rewrite fsbig_finite//= sumEFin lee_fin.
  by apply: sumr_ge0 => /= b _; exact: bernoulli_pmf_ge0.
transitivity (\sum_(0 <= i <oo) (\esum_(j in F i) (bernoulli_pmf p j)%:E)%R)%E.
apply: eq_eseriesr => k _; rewrite esum_fset//= => b _.
  by rewrite lee_fin bernoulli_pmf_ge0.
rewrite -nneseries_sum_bigcup//=; last first.
  by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
by rewrite esum_fset//= => b _; rewrite lee_fin bernoulli_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ bernoulli
  bernoulli0 bernoulli_ge0 bernoulli_sigma_additive.

Let bernoulli_setT : bernoulli [set: _] = 1%E.
Proof.
rewrite /bernoulli/=; case: ifPn => p01; last by rewrite probability_setT.
by rewrite bernoulli_pmf1.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

Lemma eq_bernoulli (P : probability bool R) :
  P [set true] = p%:E -> P =1 bernoulli.
Proof.
move=> Ptrue sb; rewrite /bernoulli /bernoulli_pmf.
have Pfalse: P [set false] = (1 - p%:E)%E.
  rewrite -Ptrue -(probability_setT P) setT_bool measureU//; last first.
    by rewrite disjoints_subset => -[]//.
  by rewrite addeAC subee ?add0e//= Ptrue.
have: (0 <= p%:E <= 1)%E by rewrite -Ptrue measure_ge0 probability_le1.
rewrite !lee_fin => ->.
have eq_sb := etrans (bigcup_imset1 (_ : set bool) id) (image_id _).
rewrite -[in LHS](eq_sb sb)/= measure_fin_bigcup//; last 2 first.
- exact: finite_finset.
- by move=> [] [] _ _ [[]]//= [].
- by apply: eq_fsbigr => /= -[].
Qed.

End bernoulli.

Section bernoulli_measure.
Context {R : realType}.
Variables (p : R) (p0 : (0 <= p)%R) (p1 : ((NngNum p0)%:num <= 1)%R).

Lemma bernoulli_dirac : bernoulli p = measure_add
  (mscale (NngNum p0) \d_true) (mscale (1 - (Itv01 p0 p1)%:num)%:nng \d_false).
Proof.
apply/funext => U; rewrite /bernoulli; case: ifPn => [p01|]; last first.
  by rewrite p0/= p1.
rewrite measure_addE/= /mscale/=.
have := @subsetT _ U; rewrite setT_bool => UT.
have [->|->|->|->] /= := subset_set2 UT.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  by rewrite esum_set0 2!measure0 2!mule0 adde0.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  rewrite esum_set1/= ?lee_fin// 2!diracE mem_set//= memNset//= mule0 adde0.
  by rewrite mule1.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  rewrite esum_set1/= ?lee_fin ?subr_ge0// 2!diracE memNset//= mem_set//=.
  by rewrite mule0 add0e mule1.
- rewrite fsbigU//=; last by move=> x [->].
  by rewrite 2!fsbig_set1/= -setT_bool 2!diracT !mule1.
Qed.

End bernoulli_measure.
Arguments bernoulli {R}.

Lemma eq_bernoulliV2 {R : realType} (P : probability bool R) :
  P [set true] = P [set false] -> P =1 bernoulli 2^-1.
Proof.
move=> Ptrue_eq_false; apply/eq_bernoulli.
have : P [set: bool] = 1%E := probability_setT P.
rewrite setT_bool measureU//=; last first.
  by rewrite disjoints_subset => -[]//.
rewrite Ptrue_eq_false -mule2n; move/esym/eqP.
by rewrite -mule_natl -eqe_pdivrMl// mule1 => /eqP<-.
Qed.

Section integral_bernoulli.
Context {R : realType}.
Variables (p : R) (p01 : (0 <= p <= 1)%R).
Local Open Scope ereal_scope.

Lemma bernoulliE A : bernoulli p A = p%:E * \d_true A + (`1-p)%:E * \d_false A.
Proof. by case/andP : p01 => p0 p1; rewrite bernoulli_dirac// measure_addE. Qed.

Lemma integral_bernoulli (f : bool -> \bar R) : (forall x, 0 <= f x) ->
  \int[bernoulli p]_y (f y) = p%:E * f true + (`1-p)%:E * f false.
Proof.
move=> f0; case/andP : p01 => p0 p1; rewrite bernoulli_dirac/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= !diracT !mul1e.
Qed.

End integral_bernoulli.

Section measurable_bernoulli.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Type p : R.

Lemma measurable_bernoulli :
  measurable_fun setT (bernoulli : R -> pprobability bool R).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_if => //=.
  by apply: measurable_and => //; exact: measurable_fun_ler.
apply: (eq_measurable_fun (fun t =>
    \sum_(b <- fset_set Ys) (bernoulli_pmf t b)%:E)).
  move=> x /set_mem[_/= x01].
  by rewrite fsbig_finite//=.
apply: emeasurable_sum => n; move=> k Ysk; apply/measurableT_comp => //.
exact: measurable_bernoulli_pmf.
Qed.

Lemma measurable_bernoulli2 U : measurable U ->
  measurable_fun setT (bernoulli ^~ U : R -> \bar R).
Proof.
by move=> ?; exact: (measurable_kernel (kprobability measurable_bernoulli)).
Qed.

End measurable_bernoulli.
Arguments measurable_bernoulli {R}.

Section binomial_pmf.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : R).

Definition binomial_pmf k := p ^+ k * (`1-p) ^+ (n - k) *+ 'C(n, k).

Lemma binomial_pmf_ge0 k (p01 : (0 <= p <= 1)%R) : 0 <= binomial_pmf k.
Proof.
move: p01 => /andP[p0 p1]; rewrite mulrn_wge0// mulr_ge0// ?exprn_ge0//.
exact: onem_ge0.
Qed.

End binomial_pmf.

Lemma measurable_binomial_pmf {R : realType} D n k :
  measurable_fun D (@binomial_pmf R n ^~ k).
Proof.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x : R => x *+ 'C(n, k))%R) => /=.
  exact: natmul_measurable.
by apply: measurable_funM => //; apply: measurable_funX; exact: measurable_funB.
Qed.

Definition binomial_prob {R : realType} (n : nat) (p : R) : set nat -> \bar R :=
  fun U => if (0 <= p <= 1)%R then
    \esum_(k in U) (binomial_pmf n p k)%:E else \d_0%N U.

Section binomial.
Context {R : realType} (n : nat) (p : R).
Local Open Scope ereal_scope.

Local Notation binomial := (binomial_prob n p).

Let binomial0 : binomial set0 = 0.
Proof. by rewrite /binomial measure0; case: ifPn => //; rewrite esum_set0. Qed.

Let binomial_ge0 U : 0 <= binomial U.
Proof.
rewrite /binomial; case: ifPn => // p01; apply: esum_ge0 => /= k Uk.
by rewrite lee_fin binomial_pmf_ge0.
Qed.

Let binomial_sigma_additive : semi_sigma_additive binomial.
Proof.
move=> F mF tF mUF; rewrite /binomial; case: ifPn => p01; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: lee_sum_nneg_natr => // k _ _.
  by apply: esum_ge0 => /= ? _; exact: binomial_pmf_ge0.
by rewrite nneseries_sum_bigcup// => i; rewrite lee_fin binomial_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ binomial
  binomial0 binomial_ge0 binomial_sigma_additive.

Let binomial_setT : binomial [set: _] = 1.
Proof.
rewrite /binomial; case: ifPn; last by move=> _; rewrite probability_setT.
move=> p01; rewrite /binomial_pmf.
have pkn k : 0%R <= (p ^+ k * `1-p ^+ (n - k) *+ 'C(n, k))%:E.
  case/andP : p01 => p0 p1.
  by rewrite lee_fin mulrn_wge0// mulr_ge0 ?exprn_ge0 ?subr_ge0.
rewrite (esumID `I_n.+1)// [X in _ + X]esum1 ?adde0; last first.
  by move=> /= k [_ /negP]; rewrite -leqNgt => nk; rewrite bin_small.
rewrite setTI esum_fset// -fsbig_ord//=.
under eq_bigr do rewrite mulrC.
rewrite sumEFin -exprDn_comm; last exact: mulrC.
by rewrite addrC add_onemK expr1n.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R binomial binomial_setT.

End binomial.

Section binomial_probability.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : R)
        (p0 : (0 <= p)%R) (p1 : ((NngNum p0)%:num <= 1)%R).

Definition bin_prob (k : nat) : {nonneg R} :=
  ((NngNum p0)%:num ^+ k * (NngNum (onem_ge0 p1))%:num ^+ (n - k)%N *+ 'C(n, k))%:nng.

Lemma bin_prob0 : bin_prob 0 = ((NngNum (onem_ge0 p1))%:num^+n)%:nng.
Proof.
rewrite /bin_prob bin0 subn0/=; apply/val_inj => /=.
by rewrite expr0 mul1r mulr1n.
Qed.

Lemma bin_prob1 : bin_prob 1 =
  ((NngNum p0)%:num * (NngNum (onem_ge0 p1))%:num ^+ n.-1 *+ n)%:nng.
Proof.
by rewrite /bin_prob bin1/=; apply/val_inj => /=; rewrite expr1 subn1.
Qed.

Lemma binomial_msum :
  binomial_prob n p = msum (fun k => mscale (bin_prob k) \d_k) n.+1.
Proof.
apply/funext => U.
rewrite /binomial_prob; case: ifPn => [_|]; last by rewrite p1 p0.
rewrite /msum/= /mscale/= /binomial_pmf.
have pkn k : (0%R <= (p ^+ k * `1-p ^+ (n - k) *+ 'C(n, k))%:E)%E.
  by rewrite lee_fin mulrn_wge0// mulr_ge0 ?exprn_ge0 ?subr_ge0.
rewrite (esumID `I_n.+1)//= [X in _ + X]esum1 ?adde0; last first.
  by move=> /= k [_ /negP]; rewrite -leqNgt => nk; rewrite bin_small.
rewrite esum_mkcondl esum_fset//; last by move=> i /= _; case: ifPn.
rewrite -fsbig_ord//=; apply: eq_bigr => i _.
by rewrite diracE; case: ifPn => /= iU; [rewrite mule1|rewrite mule0].
Qed.

Lemma binomial_probE U : binomial_prob n p U =
  (\sum_(k < n.+1) (bin_prob k)%:num%:E * (\d_(nat_of_ord k) U))%E.
Proof. by rewrite binomial_msum. Qed.

Lemma integral_binomial (f : nat -> \bar R) : (forall x, 0 <= f x)%E ->
  (\int[binomial_prob n p]_y (f y) =
   \sum_(k < n.+1) (bin_prob k)%:num%:E * f k)%E.
Proof.
move=> f0; rewrite binomial_msum ge0_integral_measure_sum//=.
apply: eq_bigr => i _.
by rewrite ge0_integral_mscale//= integral_dirac//= diracT mul1e.
Qed.

End binomial_probability.

Lemma integral_binomial_prob (R : realType) n p U : (0 <= p <= 1)%R ->
  (\int[binomial_prob n p]_y \d_(0 < y)%N U =
  bernoulli (1 - `1-p ^+ n) U :> \bar R)%E.
Proof.
move=> /andP[p0 p1]; rewrite bernoulliE//=; last first.
  rewrite subr_ge0 exprn_ile1//=; [|exact/onem_ge0|exact/onem_le1].
  by rewrite lerBlDr addrC -lerBlDr subrr; exact/exprn_ge0/onem_ge0.
rewrite (@integral_binomial _ n p _ _ (fun y => \d_(1 <= y)%N U))//.
rewrite !big_ord_recl/=.
rewrite expr0 mul1r subn0 bin0 ltnn mulr1n addrC.
rewrite onemD opprK onem1 add0r; congr +%E.
rewrite /bump; under eq_bigr do rewrite leq0n add1n ltnS leq0n.
rewrite -ge0_sume_distrl; last first.
  move=> i _.
  by apply/mulrn_wge0/mulr_ge0; apply/exprn_ge0 => //; exact/onem_ge0.
congr *%E.
transitivity (\sum_(i < n.+1) (`1-p ^+ (n - i) * p ^+ i *+ 'C(n, i))%:E -
              (`1-p ^+ n)%:E)%E.
  rewrite big_ord_recl/=.
  rewrite expr0 mulr1 subn0 bin0 mulr1n addrAC -EFinD subrr add0e.
  by rewrite /bump; under [RHS]eq_bigr do rewrite leq0n add1n mulrC.
rewrite sumEFin -(@exprDn_comm _ `1-p p n)//.
  by rewrite subrK expr1n.
by rewrite /GRing.comm/onem mulrC.
Qed.

Lemma measurable_binomial_prob (R : realType) (n : nat) :
  measurable_fun setT (binomial_prob n : R -> pprobability _ _).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_if => //=.
  by apply: measurable_and => //; exact: measurable_fun_ler.
apply: (eq_measurable_fun (fun t =>
    \sum_(k <oo | k \in Ys) (binomial_pmf n t k)%:E))%E.
  move=> x /set_mem[_/= x01].
  rewrite nneseries_esum//; last by move=> *; rewrite lee_fin binomial_pmf_ge0.
  by rewrite set_mem_set.
apply: ge0_emeasurable_sum.
  by move=> k x/= [_ x01] _; rewrite lee_fin binomial_pmf_ge0.
by move=> k Ysk; apply/measurableT_comp => //; exact: measurable_binomial_pmf.
Qed.

Section uniform_probability.
Local Open Scope ring_scope.
Context (R : realType) (a b : R).

Definition uniform_pdf x := if a <= x <= b then (b - a)^-1 else 0.

Lemma uniform_pdf_ge0 x : a < b -> 0 <= uniform_pdf x.
Proof.
move=> ab; rewrite /uniform_pdf; case: ifPn => // axb.
by rewrite invr_ge0// ltW// subr_gt0.
Qed.

Lemma measurable_uniform_pdf : measurable_fun setT uniform_pdf.
Proof.
rewrite /uniform_pdf /=; apply: measurable_fun_if => //=.
by apply: measurable_and => //; exact: measurable_fun_ler.
Qed.

Local Notation mu := lebesgue_measure.

Lemma integral_uniform_pdf U :
  (\int[mu]_(x in U) (uniform_pdf x)%:E =
   \int[mu]_(x in U `&` `[a, b]) (uniform_pdf x)%:E)%E.
Proof.
rewrite [RHS]integral_mkcondr/=; apply: eq_integral => x xU.
rewrite patchE; case: ifPn => //.
rewrite notin_setE/= in_itv/= => /negP/negbTE xab.
by rewrite /uniform_pdf xab.
Qed.

Lemma integral_uniform_pdf1 A (ab : a < b) : `[a, b] `<=` A ->
  (\int[mu]_(x in A) (uniform_pdf x)%:E = 1)%E.
Proof.
move=> abA; rewrite integral_uniform_pdf setIidr//.
rewrite (eq_integral (fun=> (b - a)^-1%:E)); last first.
  by move=> x; rewrite inE/= in_itv/= /uniform_pdf => ->.
rewrite integral_cst//= lebesgue_measure_itv/= lte_fin.
by rewrite ab -EFinD -EFinM mulVf// gt_eqF// subr_gt0.
Qed.

Definition uniform_prob (ab : a < b) : set _ -> \bar R :=
  fun U => (\int[mu]_(x in U) (uniform_pdf x)%:E)%E.

Hypothesis ab : (a < b)%R.

Let uniform0 : uniform_prob ab set0 = 0.
Proof. by rewrite /uniform_prob integral_set0. Qed.

Let uniform_ge0 U : (0 <= uniform_prob ab U)%E.
Proof.
by apply: integral_ge0 => /= x Ux; rewrite lee_fin uniform_pdf_ge0.
Qed.

Lemma integrable_uniform_pdf :
  mu.-integrable setT (fun x => (uniform_pdf x)%:E).
Proof.
apply/integrableP; split.
  by apply: measurableT_comp => //; exact: measurable_uniform_pdf.
under eq_integral.
  move=> x _; rewrite gee0_abs//; last by rewrite lee_fin uniform_pdf_ge0.
  over.
by rewrite /= integral_uniform_pdf1 ?ltry// -subr_gt0.
Qed.

Let uniform_sigma_additive : semi_sigma_additive (uniform_prob ab).
Proof.
move=> /= F mF tF mUF; rewrite /uniform_prob; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _.
  by apply: integral_ge0 => /= x Fkx; rewrite lee_fin uniform_pdf_ge0.
rewrite ge0_integral_bigcup//=.
- apply: measurable_funTS; apply: measurableT_comp => //.
  exact: measurable_uniform_pdf.
- by move=> x _; rewrite lee_fin uniform_pdf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (uniform_prob ab)
  uniform0 uniform_ge0 uniform_sigma_additive.

Let uniform_setT : uniform_prob ab [set: _] = 1%:E.
Proof. by rewrite /uniform_prob /mscale/= integral_uniform_pdf1. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R
  (uniform_prob ab) uniform_setT.

Lemma dominates_uniform_prob : uniform_prob ab `<< mu.
Proof.
move=> A mA muA0; rewrite /uniform_prob integral_uniform_pdf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: integral_ge0 => x [Ax /=]; rewrite in_itv /= => xab.
  by rewrite lee_fin uniform_pdf_ge0.
apply: (@le_trans _ _
    (\int[mu]_(x in A `&` `[a, b]%classic) (b - a)^-1%:E))%E; last first.
  rewrite integral_cst//= ?mul1e//.
    by rewrite pmule_rle0 ?lte_fin ?invr_gt0// ?subr_gt0// -muA0 measureIl.
  exact: measurableI.
apply: ge0_le_integral => //=.
- exact: measurableI.
- by move=> x [Ax]; rewrite /= in_itv/= => axb; rewrite lee_fin uniform_pdf_ge0.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_uniform_pdf.
- by move=> x [Ax _]; rewrite lee_fin invr_ge0// ltW// subr_gt0.
- by move=> x [Ax]; rewrite in_itv/= /uniform_pdf => ->.
Qed.

Let integral_uniform_indic E : measurable E ->
  (\int[uniform_prob ab]_x (\1_E x)%:E =
   (b - a)^-1%:E * \int[mu]_(x in `[a, b]) (\1_E x)%:E)%E.
Proof.
move=> mE; rewrite integral_indic//= /uniform_prob setIT -ge0_integralZl//=.
- rewrite [LHS]integral_mkcond/= [RHS]integral_mkcond/=.
  apply: eq_integral => x _; rewrite !patchE; case: ifPn => xE.
    case: ifPn.
      rewrite inE/= in_itv/= => xab.
      by rewrite /uniform_pdf xab indicE xE mule1.
    by rewrite notin_setE/= in_itv/= => /negP/negbTE; rewrite /uniform_pdf => ->.
  case: ifPn => //.
  by rewrite inE/= in_itv/= => axb; rewrite indicE (negbTE xE) mule0.
- exact/measurable_EFinP/measurable_indic.
- by rewrite lee_fin invr_ge0// ltW// subr_gt0.
Qed.

Import HBNNSimple.

Let integral_uniform_nnsfun (f : {nnsfun _ >-> R}) :
  (\int[uniform_prob ab]_x (f x)%:E =
   (b - a)^-1%:E * \int[mu]_(x in `[a, b]) (f x)%:E)%E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralZl//; last 3 first.
  - exact/measurable_EFinP/measurable_funTS.
  - by move=> x _; rewrite lee_fin.
  - by rewrite lee_fin invr_ge0// ltW// subr_gt0.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/measurable_EFinP; do 2 apply/measurableT_comp => //.
  - move=> n x _; rewrite EFinM mule_ge0//; last by rewrite nnfun_muleindic_ge0.
    by rewrite lee_fin invr_ge0// ltW// subr_gt0.
apply: eq_fsbigr => r _; rewrite ge0_integralZl//.
- by rewrite !integralZl_indic_nnsfun//= integral_uniform_indic// muleCA.
- exact/measurable_EFinP/measurableT_comp.
- by move=> t _; rewrite nnfun_muleindic_ge0.
- by rewrite lee_fin invr_ge0// ltW// subr_gt0.
Qed.

Lemma integral_uniform (f : _ -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x)%E ->
  (\int[uniform_prob ab]_x f x = (b - a)^-1%:E * \int[mu]_(x in `[a, b]) f x)%E.
Proof.
move=> mf f0.
pose f_ := nnsfun_approx measurableT mf.
transitivity (lim (\int[uniform_prob ab]_x (f_ n x)%:E @[n --> \oo])%E).
  rewrite -monotone_convergence//=.
  - apply: eq_integral => ? /[!inE] xD; apply/esym/cvg_lim => //=.
    exact: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> n ? _; rewrite lee_fin.
  - by move=> ? _ ? ? mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite [X in _ = (_ * X)%E](_ : _ = lim
    (\int[mu]_(x in `[a, b]) (f_ n x)%:E @[n --> \oo])%E); last first.
  rewrite -monotone_convergence//=.
  - apply: eq_integral => ? /[!inE] xD; apply/esym/cvg_lim => //.
    exact: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> n ? _; rewrite lee_fin.
  - by move=> ? _ ? ? ?; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite -limeMl//.
  by apply: congr_lim; apply/funext => n /=; exact: integral_uniform_nnsfun.
apply/ereal_nondecreasing_is_cvgn => x y xy; apply: ge0_le_integral => //=.
- by move=> ? _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> ? _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> ? _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

End uniform_probability.

Section normal_density.
Context {R : realType}.
Local Open Scope ring_scope.
Local Import Num.ExtraDef.
Implicit Types m s x : R.

Definition normal_fun m s x := expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)).

Lemma measurable_normal_fun m s : measurable_fun [set :R] (normal_fun m s).
Proof.
apply: measurableT_comp => //=; apply: measurable_funM => //=.
apply: measurableT_comp => //=; apply: measurable_funX => //=.
exact: measurable_funB.
Qed.

Lemma normal_fun_ge0 m s x : 0 <= normal_fun m s x.
Proof. exact: expR_ge0. Qed.

Lemma normal_fun_center m s : normal_fun m s = normal_fun 0 s \o center m.
Proof. by apply/funext => x/=; rewrite /normal_fun/= subr0. Qed.

Definition normal_peak s := (sqrtr (s ^+ 2 * pi *+ 2))^-1.

Lemma normal_peak_ge0 s : 0 <= normal_peak s. Proof. by rewrite invr_ge0. Qed.

Lemma normal_peak_gt0 s : s != 0 -> 0 < normal_peak s.
Proof.
move=> s0; rewrite invr_gt0// sqrtr_gt0.
by rewrite pmulrn_rgt0// mulr_gt0 ?pi_gt0// exprn_even_gt0/=.
Qed.

Let normal_pdf0 m s x : R := normal_peak s * normal_fun m s x.

Definition normal_pdf m s x :=
  if s == 0 then \1_`[0, 1] x else normal_pdf0 m s x.

Lemma normal_pdfE m s : s != 0 -> normal_pdf m s = normal_pdf0 m s.
Proof. by rewrite /normal_pdf; have [_|s0] := eqVneq s 0. Qed.

Let normal_pdf0_center m s : normal_pdf0 m s = normal_pdf0 0 s \o center m.
Proof. by rewrite /normal_pdf0 normal_fun_center. Qed.

Let normal_pdf0_ge0 m s x : 0 <= normal_pdf0 m s x.
Proof. by rewrite mulr_ge0 ?normal_peak_ge0 ?expR_ge0. Qed.

Let normal_pdf0_gt0 m s x : s != 0 -> 0 < normal_pdf0 m s x.
Proof. by move=> s0; rewrite mulr_gt0 ?expR_gt0// normal_peak_gt0. Qed.

Let measurable_normal_pdf0 m s : measurable_fun setT (normal_pdf0 m s).
Proof. by apply: measurable_funM => //=; exact: measurable_normal_fun. Qed.

Lemma measurable_normal_pdf m s : measurable_fun setT (normal_pdf m s).
Proof.
by rewrite /normal_pdf; have [_|] := eqVneq s 0; first exact: measurable_indic.
Qed.

Let continuous_normal_pdf0 m s : continuous (normal_pdf0 m s).
Proof.
move=> x; apply: cvgM; first exact: cvg_cst.
apply: (cvg_comp _ expR); last exact: continuous_expR.
apply: cvgM; last exact: cvg_cst.
apply: (@cvgN _ R^o).
apply: (cvg_comp (fun x => x - m) (fun x => x ^+ 2)).
  by apply: (@cvgB _ R^o) => //; [exact: cvg_id|exact: cvg_cst].
exact: sqr_continuous.
Qed.

Let normal_pdf0_ub m s x : normal_pdf0 m s x <= normal_peak s.
Proof.
rewrite /normal_pdf0 ler_piMr ?normal_peak_ge0//.
rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 mulr_ge0// ?sqr_ge0//.
by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
Qed.

Lemma normal_pdf_ge0 m s x : 0 <= normal_pdf m s x.
Proof. by rewrite /normal_pdf; case: ifP. Qed.

Lemma continuous_normal_pdf m s : s != 0 -> continuous (normal_pdf m s).
Proof. by rewrite /normal_pdf; have [|] := eqVneq s 0. Qed.

Lemma normal_pdf_ub m s x : s != 0 -> normal_pdf m s x <= normal_peak s.
Proof. by rewrite /normal_pdf; have [|] := eqVneq s 0. Qed.

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
rewrite muleCA ge0_integralZr//=; first last.
  by move=> x _; rewrite lee_fin mulr_ge0//= ?gauss_fun_ge0// F'E/= invr_ge0.
  rewrite F'E; apply/measurable_EFinP/measurable_funM => //.
  apply/measurableT_comp => //; first exact: measurable_gauss_fun.
  by apply: measurable_funM => //; exact: measurable_funD.
congr *%E; last by rewrite -(mulr_natr (_ ^+ 2)) sqrtrM ?sqr_ge0.
rewrite -increasing_ge0_integration_by_substitutionT//.
- exact: integralT_gauss.
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
Qed.

Let integral_normal_fun : sigma != 0 ->
  (\int[mu]_x (normal_fun x)%:E)%E = normal_peak^-1%:E.
Proof.
move=> s0; rewrite -integral_gaussFF'//; apply: eq_integral => /= x _.
rewrite F'E !fctE/= EFinM -muleA -EFinM mulVf ?mulr1 ?mule1.
  by rewrite normal_gauss_fun.
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
rewrite integralZl//=; last exact: integrable_normal_fun.
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
rewrite /normal_prob/= integral_bigcup//=; last first.
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
move=> A mA muA0; rewrite /normal_prob /normal_pdf.
have [s0|s0] := eqVneq sigma 0.
  apply: null_set_integral => //=; apply: (integrableS measurableT) => //=.
  exact: integrable_indic_itv.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: integral_ge0 => x _.
  by rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A) (normal_peak)%:E))%E; last first.
  by rewrite integral_cst//= muA0 mule0.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
- apply/measurable_funTS/measurableT_comp => //=.
  by apply: measurable_funM => //; exact: measurable_normal_fun.
- by move=> x _; rewrite lee_fin normal_peak_ge0.
- by move=> x _; have := normal_pdf_ub m x s0; rewrite /normal_pdf (negbTE s0).
Qed.

End normal_probability.

Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable rate : R.
Hypothesis rate_gt0 : 0 <= rate.

Let exponential_pdfT x := rate * expR (- rate * x).
Definition exponential_pdf := exponential_pdfT \_ `[0%R, +oo[.

Lemma exponential_pdf_ge0 x : 0 <= exponential_pdf x.
Proof.
by apply: restrict_ge0 => {}x _; apply: mulr_ge0 => //; exact: expR_ge0.
Qed.

Lemma lt0_exponential_pdf x : x < 0 -> exponential_pdf x = 0.
Proof.
move=> x0; rewrite /exponential_pdf patchE ifF//.
by apply/negP; rewrite inE/= in_itv/= andbT; apply/negP; rewrite -ltNge.
Qed.

Let continuous_exponential_pdfT : continuous exponential_pdfT.
Proof.
move=> x.
apply: (@continuousM _ R^o (fun=> rate) (fun x => expR (- rate * x))).
  exact: cst_continuous.
apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM => //; apply: (@continuousN _ R^o); exact: cst_continuous.
Qed.

Lemma measurable_exponential_pdf : measurable_fun [set: R] exponential_pdf.
Proof.
apply/measurable_restrict => //; apply: measurable_funTS.
exact: continuous_measurable_fun.
Qed.

Lemma exponential_pdfE x : 0 <= x -> exponential_pdf x = exponential_pdfT x.
Proof.
by move=> x0; rewrite /exponential_pdf patchE ifT// inE/= in_itv/= x0.
Qed.

Lemma in_continuous_exponential_pdf :
  {in `]0, +oo[%R, continuous exponential_pdf}.
Proof.
move=> x; rewrite in_itv/= andbT => x0.
apply/(@cvgrPdist_lt _ R^o) => e e0; near=> y.
rewrite 2?(exponential_pdfE (ltW _))//; last by near: y; exact: lt_nbhsr.
near: y; move: e e0; apply/(@cvgrPdist_lt _ R^o).
by apply: continuous_comp => //; exact: continuous_exponential_pdfT.
Unshelve. end_near. Qed.

Lemma within_continuous_exponential_pdf :
  {within [set` `[0, +oo[%R], continuous exponential_pdf}.
Proof.
apply/continuous_within_itvcyP; split.
  exact: in_continuous_exponential_pdf.
apply/(@cvgrPdist_le _ R^o) => e e0; near=> t.
rewrite 2?exponential_pdfE//.
near: t; move: e e0; apply/cvgrPdist_le.
by apply: cvg_at_right_filter; exact: continuous_exponential_pdfT.
Unshelve. end_near. Qed.

End exponential_pdf.

Definition exponential_prob {R : realType} (rate : R) :=
  fun V => (\int[lebesgue_measure]_(x in V) (exponential_pdf rate x)%:E)%E.

Section exponential_prob.
Context {R : realType}.
Local Open Scope ring_scope.
Notation mu := lebesgue_measure.
Variable rate : R.

Lemma derive1_exponential_pdf :
  {in `]0, +oo[%R, (fun x => - (expR : R^o -> R^o) (- rate * x))^`()%classic
                   =1 exponential_pdf rate}.
Proof.
move=> z; rewrite in_itv/= andbT => z0.
rewrite derive1_comp// derive1N// derive1_id mulN1r derive1_comp// derive1E.
have/funeqP -> := @derive_expR R.
by rewrite derive1Ml// derive1_id mulr1 mulrN opprK mulrC exponential_pdfE ?ltW.
Qed.

Let cexpNM : continuous (fun z : R^o => expR (- rate * z)).
Proof.
move=> z; apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM => //; apply: (@continuousN _ R^o); exact: cst_continuous.
Qed.

Lemma exponential_prob_itv0c (x : R) : 0 < x ->
  exponential_prob rate `[0, x] = (1 - (expR (- rate * x))%:E)%E.
Proof.
move=> x0.
rewrite (_: 1 = - (- expR (- rate * 0))%:E)%E; last first.
  by rewrite mulr0 expR0 EFinN oppeK.
rewrite addeC.
apply: (@continuous_FTC2 _ _ (fun x => - expR (- rate * x))) => //.
- apply: (@continuous_subspaceW R^o _ _ [set` `[0, +oo[%R]).
  + exact: subset_itvl.
  + exact: within_continuous_exponential_pdf.
- split.
  + by move=> z _; exact: ex_derive.
  + by apply/cvg_at_right_filter; apply: cvgN; exact: cexpNM.
  + by apply/cvg_at_left_filter; apply: cvgN; exact: cexpNM.
- move=> z; rewrite in_itv/= => /andP[z0 _].
  by apply: derive1_exponential_pdf; rewrite in_itv/= andbT.
Qed.

Lemma integral_exponential_pdf (rate_gt0 : 0 < rate) :
  (\int[mu]_x (exponential_pdf rate x)%:E = 1)%E.
Proof.
have mEex : measurable_fun setT (EFin \o exponential_pdf rate).
  by apply/measurable_EFinP; exact: measurable_exponential_pdf.
rewrite -(setUv `[0, +oo[%classic) ge0_integral_setU//=; last 4 first.
  exact: measurableC.
  by rewrite setUv.
  by move=> x _; rewrite lee_fin exponential_pdf_ge0// ltW.
  exact/disj_setPCl.
rewrite [X in _ + X]integral0_eq ?adde0; last first.
  by move=> x x0; rewrite /exponential_pdf patchE ifF// memNset.
rewrite (@ge0_continuous_FTC2y _ _
  (fun x => - (expR (- rate * x))) _ 0)//.
- by rewrite mulr0 expR0 EFinN oppeK add0e.
- by move=> x _; apply: exponential_pdf_ge0; exact: ltW.
- exact: within_continuous_exponential_pdf.
- rewrite -oppr0; apply: (@cvgN _ R^o).
  rewrite (_ : (fun x => expR (- rate * x)) =
               (fun z => expR (- z)) \o (fun z => rate * z)); last first.
    by apply: eq_fun => x; rewrite mulNr.
  apply: (@cvg_comp _ R^o _ _ _ _ (pinfty_nbhs R)); last exact: cvgr_expR.
  exact: gt0_cvgMry.
- by apply: (@cvgN _ R^o); apply: cvg_at_right_filter; exact: cexpNM.
- exact: derive1_exponential_pdf.
Qed.

Lemma integrable_exponential_pdf (rate_gt0 : 0 < rate) :
  mu.-integrable setT (EFin \o (exponential_pdf rate)).
Proof.
have mEex : measurable_fun setT (EFin \o exponential_pdf rate).
  by apply/measurable_EFinP; exact: measurable_exponential_pdf.
apply/integrableP; split => //.
under eq_integral do rewrite /= ger0_norm ?(exponential_pdf_ge0 (ltW rate_gt0))//.
by rewrite /= integral_exponential_pdf// ltry.
Qed.

Hypothesis rate_gt0 : 0 < rate.

Local Notation exponential := (exponential_prob rate).

Let exponential0 : exponential set0 = 0%E.
Proof. by rewrite /exponential integral_set0. Qed.

Let exponential_ge0 A : (0 <= exponential A)%E.
Proof.
rewrite /exponential integral_ge0//= => x _.
by rewrite lee_fin exponential_pdf_ge0// ltW.
Qed.

Let exponential_sigma_additive : semi_sigma_additive exponential.
Proof.
move=> /= F mF tF mUF; rewrite /exponential; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _; apply: integral_ge0 => /= x Fkx.
  by rewrite lee_fin exponential_pdf_ge0// ltW.
rewrite ge0_integral_bigcup//=.
- apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_exponential_pdf.
- by move=> x _; rewrite lee_fin exponential_pdf_ge0// ltW.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  exponential exponential0 exponential_ge0 exponential_sigma_additive.

Let exponential_setT : exponential [set: R] = 1%E.
Proof. by rewrite /exponential integral_exponential_pdf. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R exponential exponential_setT.

End exponential_prob.

Section poisson_pmf.
Local Open Scope ring_scope.
Context {R : realType}.
Implicit Types (rate : R) (k : nat).

Definition poisson_pmf rate k : R :=
  if rate > 0 then (rate ^+ k) * k`!%:R^-1 * expR (- rate) else 1.

Lemma poisson_pmf_ge0 rate k : 0 <= poisson_pmf rate k.
Proof.
rewrite /poisson_pmf; case: ifPn => // rate0.
by rewrite 2?mulr_ge0// exprn_ge0// ltW.
Qed.

End poisson_pmf.

Lemma measurable_poisson_pmf {R : realType} D k : measurable D ->
  measurable_fun D (@poisson_pmf R ^~ k).
Proof.
move=> mD; rewrite /poisson_pmf; apply: measurable_fun_if => //.
  exact: measurable_fun_ltr.
apply: measurable_funM; first exact: measurable_funM.
by apply: measurable_funTS; exact: measurableT_comp.
Qed.

Definition poisson_prob {R : realType} (rate : R) (k : nat)
   : set nat -> \bar R :=
  fun U => if 0 < rate then
    \esum_(k in U) (poisson_pmf rate k)%:E else \d_0%N U.

Section poisson.
Context {R : realType} (rate : R) (k : nat).
Local Open Scope ereal_scope.

Local Notation poisson := (poisson_prob rate k).

Let poisson0 : poisson set0 = 0.
Proof. by rewrite /poisson measure0; case: ifPn => //; rewrite esum_set0. Qed.

Let poisson_ge0 U : 0 <= poisson U.
Proof.
rewrite /poisson; case: ifPn => // rate0; apply: esum_ge0 => /= n Un.
by rewrite lee_fin poisson_pmf_ge0.
Qed.

Let poisson_sigma_additive : semi_sigma_additive poisson.
Proof.
move=> F mF tF mUF; rewrite /poisson; case: ifPn => rate0; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: lee_sum_nneg_natr => // n _ _.
  by apply: esum_ge0 => /= ? _; exact: poisson_pmf_ge0.
by rewrite nneseries_sum_bigcup// => i; rewrite lee_fin poisson_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ poisson
  poisson0 poisson_ge0 poisson_sigma_additive.

Let poisson_setT : poisson [set: nat] = 1.
Proof.
rewrite /poisson; case: ifPn => [rate0|_]; last by rewrite probability_setT.
rewrite [RHS](_ : _ = (expR (- rate))%:E * (expR rate)%:E); last first.
  by rewrite -EFinM expRN mulVf ?gt_eqF ?expR_gt0.
rewrite -nneseries_esumT; last by move=> *; rewrite lee_fin poisson_pmf_ge0.
under eq_eseriesr.
  move=> n _.
  rewrite /poisson_pmf rate0 EFinM muleC.
  over.
rewrite /= nneseriesZl/=; last first.
  move=> n _.
  by rewrite lee_fin divr_ge0// exprn_ge0// ltW.
congr *%E; rewrite expRE -EFin_lim; last first.
  rewrite /pseries/=; under eq_fun do rewrite mulrC.
  exact: is_cvg_series_exp_coeff.
apply/congr_lim/funext => n/=; rewrite /pseries/= /series/= -sumEFin//.
by under eq_bigr do rewrite mulrC.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R poisson poisson_setT.

End poisson.

Lemma measurable_poisson_prob {R : realType} n :
  measurable_fun setT (poisson_prob ^~ n : R -> pprobability _ _).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_if => //=; first exact: measurable_fun_ltr.
apply: (eq_measurable_fun (fun t =>
    \sum_(k <oo | k \in Ys) (poisson_pmf t k)%:E))%E.
  move=> x /set_mem[_/= x01].
  by rewrite nneseries_esum ?set_mem_set// =>*; rewrite lee_fin poisson_pmf_ge0.
apply: ge0_emeasurable_sum.
  by move=> k x/= [_ x01] _; rewrite lee_fin poisson_pmf_ge0.
move=> k Ysk; apply/measurableT_comp => //.
apply: measurable_poisson_pmf => //.
rewrite setTI.
rewrite (_ : _ @^-1` _ = `]0, +oo[%classic)//.
by apply/seteqP; split => /= x /=; rewrite in_itv/= andbT.
Qed.

Section near_lt_lim.
Variable R : realFieldType.
Implicit Types u : R ^nat.

Lemma near_lt_lim u (M : R) :
  (\forall N \near \oo, {in [set n | (N <= n)%N] &, nondecreasing_seq u}) ->
  cvgn u -> M < limn u -> \forall n \near \oo, M <= u n.
Proof.
move=> [] N _ Hnear.
move=> cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, M <= u n).
  exists (maxn N n) => //.
  move=> k/=.
  rewrite geq_max => /andP.
(*
  near=> m; suff : u n <= u m by exact: le_trans.
  apply/(Hnear m).
  near: m; exists n.+1 => // p q; apply/(Hnear n)/ltnW => //.

 
have {}Mu : forall x, M > u x by move=> x; rewrite ltNge; apply/negP.
have : limn u <= M by apply: limr_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near. Qed.
*)
Abort.

End near_lt_lim.

Section near_ereal_nondecreasing_is_cvgn.

Let G N := ([set n | (N <= n)%N]).

Lemma near_ereal_nondecreasing_is_cvgn (R : realType) (u_ : (\bar R) ^nat) :
  (\forall N \near \oo, {in G N &, nondecreasing_seq u_ }) -> cvgn u_.
Proof.
move=> [N _ H].
apply/cvg_ex.
exists (ereal_sup (range (fun n =>  u_ (n + N)))).
rewrite -(cvg_shiftn N).
apply: ereal_nondecreasing_cvgn.
move=> n m nm.
apply: (H N); rewrite /G ?inE//=.
- exact: leq_addl.
- exact: leq_addl.
- exact: leq_add.
Qed.

Lemma near_ereal_nondecreasing_cvgn (R : realType) (u_ : (\bar R)^nat) :
(*
   (\forall N \near \oo, {in G N &, nondecreasing_seq u_ })
      -> u_ @ \oo --> limn u_. (* ereal_sup range ? *)
*)
\forall N \near \oo, {in G N &, nondecreasing_seq u_ }
      -> u_ @ \oo --> ereal_sup (range (fun n => u_ (n + N))).
Proof.
near=> N.
(*
move=> [N _ H].
apply/cvg_ex.
exists (limn (fun n => u_ (n + N))).
rewrite -(cvg_shiftn N).
apply: ereal_nondecreasing_cvgn.
*)
Abort.


End near_ereal_nondecreasing_is_cvgn.

Section near_monotone_convergence.
Local Open Scope ereal_scope.

Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g' : (T -> \bar R)^nat).
Hypothesis mg' : forall n, measurable_fun D (g' n).
Hypothesis near_g'0 : \forall n \near \oo, forall x, D x -> 0 <= g' n x.
Hypothesis near_nd_g' : \forall N \near \oo, (forall x : T, D x ->
  {in [set k| (N <= k)%N]&,  {homo g'^~ x : n m / (n <= m)%N >-> (n <= m)%E}}).
Let f' := fun x => limn (g'^~ x).

Lemma near_monotone_convergence :
(\int[mu]_(x in D) (fun x0 : T => limn (g'^~ x0)) x)%E =
limn (fun n : nat => (\int[mu]_(x in D) g' n x)%E).
Proof.
have [N0 _ H0] := near_g'0.
have [N1 _ H1] := near_nd_g'.
pose N := maxn N0 N1.
under eq_integral.
  move=> x; rewrite inE/= => Dx.
  have <- : limn (fun n : nat => g' (n + N) x) = limn (g'^~ x).
    apply/cvg_lim => //.
    rewrite (cvg_shiftn _ (g'^~ x) _).
    apply: (@near_ereal_nondecreasing_is_cvgn _ (g'^~ x)).
    exists N1 => //.
    move=> n /= N1n.
    exact: H1.
  over.
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn N).
apply: cvg_monotone_convergence => //.
  move=> n x Dx.
  apply: H0 => //=.
  apply: (leq_trans (leq_maxl N0 N1)).
  exact: leq_addl.
move=> x Dx n m nm.
apply: (H1 N) => //; rewrite ?inE/=.
- exact: leq_maxr.
- exact: leq_addl.
- exact: leq_addl.
- exact: leq_add.
Qed.

Lemma cvg_near_monotone_convergence :
  \int[mu]_(x in D) g' n x @[n \oo] --> \int[mu]_(x in D) f' x.
Proof.
have [N0 _ Hg'0] := near_g'0.
have [N1 _ Hndg'] := near_nd_g'.
pose N := maxn N0 N1.
have N0N : (N0 <= N)%N by apply: (leq_maxl N0 N1).
have N1N : (N1 <= N)%N by apply: (leq_maxr N0 N1).
have g'_ge0 n x : D x -> (N <= n)%N -> 0 <= g' n x.
  move=> + Nn.
  apply: Hg'0 => /=.
  exact: (leq_trans N0N).
have ndg' n m x : D x -> (N <= n)%N -> (n <= m)%N -> g' n x <= g' m x.
  move=> Dx Nn nm.
  apply: (Hndg' N); rewrite ?inE//=.
  exact: leq_trans nm.
rewrite near_monotone_convergence.
apply: near_ereal_nondecreasing_is_cvgn.
exists N => //.
move=> k/= Nk n m; rewrite !inE/= => kn km nm.
apply: ge0_le_integral => // t Dt; [| |].
- apply: g'_ge0 => //.
  exact: leq_trans kn.
- apply: g'_ge0 => //.
  exact: leq_trans km.
- apply: ndg' => //.
  exact: leq_trans kn.
Qed.

End near_monotone_convergence.

Section exp_coeff_properties.
Context {R : realType}.

(* not used, TODO:PR *)
Lemma exp_coeff_gt0 (x : R) n : 0 < x -> 0 < exp_coeff x n.
Proof.
move=> x0.
rewrite /exp_coeff/=.
apply: divr_gt0.
  exact: exprn_gt0.
rewrite (_:0%R = 0%:R)// ltr_nat.
exact: fact_gt0.
Abort.

Lemma series_exp_coeff_near_ge0 (x : R) :
  \forall n \near \oo, 0 <= (series (exp_coeff x)) n.
Proof.
apply: (cvgr_ge (expR x)); last exact: expR_gt0.
exact: is_cvg_series_exp_coeff.
Abort.

Lemma normr_exp_coeff_near_nonincreasing (x : R) :
  \forall n \near \oo,
  `|exp_coeff x n.+1| <= `|exp_coeff x n|.
Proof.
exists `|archimedean.Num.Def.ceil x |%N => //.
move=> n/= H.
rewrite exp_coeffE.
rewrite exprS mulrA normrM [leRHS]normrM ler_pM//.
rewrite factS mulnC natrM invfM -mulrA normrM ger_pMr; last first.
  rewrite normr_gt0.
  by rewrite invr_neq0//.
rewrite normrM normfV.
rewrite ler_pdivrMl; last first.
  rewrite normr_gt0.
  by rewrite lt0r_neq0.
rewrite mulr1.
apply: (le_trans (abs_ceil_ge _)).
rewrite gtr0_norm//.
by rewrite ler_nat ltnS.
Qed.

Lemma exp_coeff2_near_nondecreasing (x : R) :
 \forall N \near \oo, nondecreasing_seq (fun n => (series (exp_coeff x) (2 * (n + N))%N)).
Proof.
have := normr_exp_coeff_near_nonincreasing x.
move=> [N _] Hnear.
exists N => //n/= Nn.
apply/nondecreasing_seqP => k.
rewrite /series/=.
have N0 : (0 <= N)%N by [].
rewrite addSn mulnS add2n.
rewrite !big_nat_recr//=.
rewrite -addrA lerDl.
rewrite -[X in _ <= _ + X]opprK subr_ge0.
rewrite (le_trans (ler_norm _))// normrN.
have : (N <= (2 * (k + n)))%N.
  rewrite mulnDr -(add0n N) leq_add//.
  by rewrite mulSn mul1n -(add0n N) leq_add.
move/Hnear => H.
apply: (le_trans H).
rewrite ler_norml lexx andbT.
suff Hsuff : 0 <= exp_coeff x (2 * (k + n))%N.
  by apply: (le_trans _ Hsuff); rewrite lerNl oppr0.
rewrite /exp_coeff/=.
apply: mulr_ge0 => //.
apply: exprn_even_ge0.
by rewrite mul2n odd_double.
Qed.

Lemma exp_coeff2_near_in_increasing (x : R) :
 \forall N \near \oo, {in [set k | (N <= k)%N] &,
nondecreasing_seq (fun n => (series (exp_coeff x) (2 * n)%N))}.
Proof.
have := normr_exp_coeff_near_nonincreasing x.
move=> [N _] Hnear.
exists N => //k/= Nk.
move=> n m; rewrite !inE/= => kn km nm.
have kn2 : (2 * k <= 2 * n)%N by rewrite leq_pmul2l.
have km2 : (2 * k <= 2 * m)%N by rewrite leq_pmul2l.
rewrite /series/=.
rewrite (big_cat_nat _ kn2)//=.
rewrite (big_cat_nat _ km2)//=.
rewrite lerD2.
have nm2 : (2 * n <= 2 * m)%N by rewrite leq_pmul2l.
rewrite (big_cat_nat _ nm2)//=.
rewrite lerDl.
rewrite -(add0n (2 * n)%N).
rewrite big_addn.
rewrite -mulnBr.
elim: (m - n)%N.
  rewrite muln0.
  rewrite big_mkord.
  by rewrite big_ord0.
move=> {km nm km2 nm2} {}m IH.
rewrite mul2n.
rewrite doubleS.
rewrite big_nat_recr//=.
rewrite big_nat_recr//=.
rewrite -addrA.
rewrite addr_ge0//.
  by rewrite -mul2n.
rewrite -[X in _ <= _ + X]opprK subr_ge0.
rewrite (le_trans (ler_norm _))// normrN.
rewrite -mul2n addSn -mulnDr.
have : (N <= (2 * (m + n)))%N.
  rewrite mulnDr -(add0n N) leq_add//.
  by rewrite (leq_trans _ kn2)// (leq_trans Nk)// leq_pmull.
move/Hnear => H.
apply: (le_trans H).
rewrite ler_norml lexx andbT.
suff Hsuff : 0 <= exp_coeff x (2 * (m + n))%N.
  by apply: (le_trans _ Hsuff); rewrite lerNl oppr0.
rewrite /exp_coeff/=.
apply: mulr_ge0 => //.
apply: exprn_even_ge0.
by rewrite mul2n odd_double.
Qed.

End exp_coeff_properties.

Section normal_density.
Context {R : realType}.
Local Open Scope ring_scope.
Local Import Num.ExtraDef.

(* NB: If s = 0 then normal_pdf0 is cst 0 for all m and x
 *     because divr is defined by x / 0 = 0.
 *)
Definition normal_pdf0 (m s x : R) : R :=
   (sqrtr (s ^+2 * pi *+ 2))^-1 * expR (- (x - m) ^+ 2 / (s ^+ 2*+ 2)).

Lemma normal_pdf0_center m s : normal_pdf0 m s = normal_pdf0 0 s \o center m.
Proof.
apply/funext => x/=.
by rewrite /normal_pdf0 subr0.
Qed.

Lemma normal_pdf0_ge0 m s x : 0 <= normal_pdf0 m s x.
Proof. by rewrite mulr_ge0 ?expR_ge0// invr_ge0 mulr_ge0. Qed.

Lemma normal_pdf0_gt0 m s x : s != 0 -> 0 < normal_pdf0 m s x.
Proof.
move=> s0.
rewrite mulr_gt0 ?expR_gt0// invr_gt0//.
by rewrite sqrtr_gt0 pmulrn_rgt0// pmulr_rgt0// ?pi_gt0// exprn_even_gt0/=.
Qed.

Lemma measurable_normal_pdf0 m s : measurable_fun setT (normal_pdf0 m s).
Proof.
apply: measurable_funM => //=; apply: measurableT_comp => //=.
apply: measurable_funM => //=; apply: measurableT_comp => //=.
apply: measurableT_comp (exprn_measurable _) _ => /=.
exact: measurable_funD.
Qed.

Lemma continuous_normal_pdf0 m s : continuous (normal_pdf0 m s).
Proof.
move=> x.
apply: cvgM; first exact: cvg_cst.
apply: (@cvg_comp _ R^o _ _ _ _
   (nbhs (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)))); last exact: continuous_expR.
apply: cvgM; last exact: cvg_cst.
apply: (@cvgN _ _ _ _ _ _ ((x - m) ^+ 2 : R^o)).
apply: (@cvg_comp _ _ _ _ (fun x : R => x ^+ 2)%R _ (nbhs (x - m))).
  apply: (@cvgB _ R^o) => //.
  exact: cvg_cst.
exact: sqr_continuous.
Qed.

Lemma normal_pdf0_ub m s x : normal_pdf0 m s x <= (sqrtr (s ^+ 2 * pi *+ 2))^-1.
Proof.
rewrite -[leRHS]mulr1.
rewrite ler_wpM2l ?invr_ge0// ?sqrtr_ge0.
rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 mulr_ge0// ?sqr_ge0//.
by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
Qed.

End normal_density.

Section normal_probability.
Variables (R : realType) (m sigma : R).
Local Open Scope ring_scope.
Notation mu := lebesgue_measure.

Definition normal_pdf_part x := (expR (- (x - m) ^+ 2 / (sigma ^+ 2 *+ 2))).

Let measurable_normal_pdf_part : measurable_fun setT normal_pdf_part.
Proof.
apply: measurableT_comp => //=.
apply: measurable_funM => //=.
apply: measurableT_comp => //=.
apply: measurable_funX => //=.
exact: measurable_funD.
Qed.

Let integral_normal_pdf_part : sigma != 0 ->
  (\int[mu]_x (normal_pdf_part x)%:E =
  (Num.sqrt (sigma ^+ 2 * pi *+ 2))%:E)%E.
Proof.
move=> sigma_gt0.
pose F (x : R^o) := (x - m) / (`|sigma| * Num.sqrt 2).
have F'E : F^`()%classic = cst (`|sigma| * Num.sqrt 2)^-1.
  apply/funext => x; rewrite /F derive1E deriveM// deriveD// derive_cst scaler0.
  by rewrite add0r derive_id derive_cst addr0 scaler1.
have := @integralT_gauss R.
rewrite (@increasing_ge0_integration_by_substitutionT _ F gauss_fun)//=; first last.
- by move=> x; rewrite gauss_fun_ge0.
- exact: continuous_gauss_fun.
- apply/gt0_cvgMly; last exact: cvg_addrr.
  by rewrite invr_gt0// mulr_gt0// normr_gt0.
- apply/gt0_cvgMlNy; last exact: cvg_addrr_Ny.
  by rewrite invr_gt0// mulr_gt0// normr_gt0.
- by rewrite F'E; exact: is_cvg_cst.
- by rewrite F'E; exact: is_cvg_cst.
- by rewrite F'E => ?; exact: cvg_cst.
- by move=> x y; rewrite /F ltr_pM2r ?invr_gt0 ?mulr_gt0 ?normr_gt0// ltrBlDr subrK.
move=> /(congr1 (fun x => x * (`|sigma| * Num.sqrt 2)%:E)%E).
rewrite -ge0_integralZr//=; last first.
  by move=> x _; rewrite lee_fin mulr_ge0//= ?gauss_fun_ge0// F'E/= invr_ge0.
  rewrite F'E; apply/measurable_EFinP/measurable_funM => //.
  apply/measurableT_comp => //; first exact: measurable_gauss_fun.
  by apply: measurable_funM => //; exact: measurable_funD.
move=> int_gauss.
apply: eq_trans.
  apply: eq_trans; last exact: int_gauss.
  apply: eq_integral => /= x _.
  rewrite F'E !fctE/= EFinM -muleA -EFinM mulVf ?mulr1; last first.
    by rewrite gt_eqF ?mulr_gt0 ?normr_gt0.
  rewrite /gauss_fun /F exprMn exprVn -[in RHS]mulNr.
  by rewrite exprMn real_normK ?num_real// sqr_sqrtr// mulr_natr.
rewrite -mulrnAl sqrtrM ?mulrn_wge0 ?sqr_ge0//.
by rewrite -[in RHS]mulr_natr sqrtrM ?sqr_ge0// sqrtr_sqr !EFinM muleC.
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
move=> /= F mF tF mUF.
rewrite /normal_prob/= integral_bigcup//=; last first.
  apply/integrableP; split.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_normal_pdf.
  rewrite (_ : (fun x => _) = EFin \o normal_pdf); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin normal_pdf_ge0 ?ltW.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/measurable_EFinP; exact: measurable_normal_pdf.
    by move=> ? _; rewrite lee_fin normal_pdf_ge0 ?ltW.
  by rewrite integral_normal_pdf // ltey.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin normal_pdf_ge0 ?ltW.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  normal_prob normal0 normal_ge0 normal_sigma_additive.

Let normal_setT : normal_prob [set: _] = 1%E.
Proof. by rewrite /normal_prob integral_normal_pdf. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R normal_prob normal_setT.

End normal_probability.

(* TODO: PR *)
Section shift_properties.

Variable R : realType.

Local Open Scope ring_scope.

Notation mu := lebesgue_measure.

Lemma derive_shift (v k : R) : 'D_v (shift k : R^o -> R^o) = cst v.
Proof.
apply/funext => x/=.
by rewrite deriveD// derive_id derive_cst addr0.
Qed.

Lemma is_derive_shift x v (k : R) : is_derive x v (shift k : R^o -> R^o) v.
Proof.
split => //.
by rewrite derive_val addr0.
Qed.

(* TODO: In integration_by_substitution, (f : R -> R) => (f : R -> \bar R) *)
Lemma ge0_integration_by_substitution_shift_itvNy (f : R -> R) (r e : R) :
{within `]-oo, r + e], continuous f} ->
{in `]-oo, r + e[, forall x : R, 0 <= f x} ->
(\int[mu]_(x in `]-oo, (r + e)%R]) (f x)%:E =
\int[mu]_(x in `]-oo, r]) ((f \o (shift e)) x)%:E)%E.
Proof.
move=> cf f0.
have := (derive_shift 1 e).
have <- := (funext (@derive1E R _ (shift e : R^o -> R^o))).
move=> dshiftE.
rewrite (@increasing_ge0_integration_by_substitutionNy _ (shift e))//; first last.
- exact: cvg_addrr_Ny.
- split.
    move=> x _.
    exact/ex_derive.
  apply: cvg_at_left_filter.
  apply: cvgD => //.
  exact: cvg_cst.
- rewrite dshiftE.
  exact: cvg_cst.
- rewrite dshiftE.
  exact: is_cvg_cst.
- rewrite dshiftE.
  move=> ? _; apply: cst_continuous.
- by move=> x y _ _ xy; rewrite ltr_leD.
by rewrite dshiftE mulr1/=.
Qed.

Lemma ge0_integration_by_substitution_shift_itvy (f : R -> R) (r e : R) :
{within `[r + e, +oo[, continuous f} ->
{in `]r + e, +oo[, forall x : R, 0 <= f x} ->
(\int[mu]_(x in `[r + e, +oo[) (f x)%:E =
\int[mu]_(x in `[r, +oo[) ((f \o (shift e)) x)%:E)%E.
Proof.
move=> cf f0.
have := (derive_shift 1 e).
have <- := (funext (@derive1E R _ (shift e : R^o -> R^o))).
move=> dshiftE.
rewrite (@increasing_ge0_integration_by_substitutiony _ (shift e))//=; first last.
- exact: cvg_addrr.
- split.
    move=> x _.
    exact/ex_derive.
  apply: cvg_at_right_filter.
  apply: cvgD => //.
  exact: cvg_cst.
- rewrite dshiftE.
  exact: is_cvg_cst.
- rewrite dshiftE.
  exact: is_cvg_cst.
- rewrite dshiftE.
  move=> ? _; apply: cst_continuous.
- by move=> x y _ _ xy; rewrite ltr_leD.
by rewrite dshiftE mulr1/=.
Qed.

End shift_properties.

Section normal_kernel.

Variable R : realType.
Variables s : R.
Hypothesis s0 : s != 0.
Local Open Scope ring_scope.
Notation mu := lebesgue_measure.

Let normal_pdfE m x : normal_pdf m s x =
 (Num.sqrt (s^+2 * pi *+ 2))^-1 * expR (- (x - m) ^+ 2 / (s^+2 *+ 2)).
Proof.
rewrite /normal_pdf ifF//.
exact/negP/negP.
Qed.

Local Definition normal_prob2 := (fun m => normal_prob m s) : _ -> pprobability _ _.

Lemma bij_shift x : bijective (id \+ @cst R R x).
Proof.
apply: (@Bijective _ _ _ (id \- cst x)).
- by move=> z;rewrite /=addrK.
- by move=> z; rewrite /= subrK.
Qed.

Lemma shift_ocitv (x a b : R) :
  (shift x) @` `]a, b]%classic = `]a + x, b + x]%classic.
Proof.
rewrite eqEsubset; split => r/=.
  move=> [r' + <-].
  rewrite in_itv/=; move/andP => [ar' r'b].
  by rewrite in_itv/=; apply/andP; split; rewrite ?lerD2 ?ltrD2.
rewrite in_itv/=; move/andP => [axr rbx].
exists (r - x); last by rewrite subrK.
rewrite in_itv/=; apply/andP; split.
- by rewrite ltrBrDr.
- by rewrite lerBlDr.
Qed.

Lemma shift_preimage (x : R) U :
  (shift x) @^-1` U = (shift (- x)) @` U.
Proof.
rewrite eqEsubset; split => r.
  rewrite /= => Urx.
  by exists (r + x) => //; rewrite addrK.
by move=> [z Uz <-]/=; rewrite subrK.
Qed.

Lemma pushforward_shift_itv (mu : measure (measurableTypeR R) R) (a b x : R) :
 (pushforward mu (fun z => z + x)
           `]a, b]) =
  mu `]a - x, b - x]%classic.
Proof.
rewrite /pushforward.
rewrite shift_preimage.
by rewrite shift_ocitv.
Qed.

Lemma pushforward_shift_measurable (mu : measure (measurableTypeR R) R) (x : R) (U : set R) :
 (pushforward mu (fun z => z + x)
           U) =
  mu ((center x) @` U).
Proof.
by rewrite /pushforward shift_preimage.
Qed.

From mathcomp Require Import charge.
Open Scope charge_scope.

(*
Lemma radon_nikodym_crestr_fin U (mU : measurable U)
(Uoo : (@lebesgue_measure R U < +oo)%E) :
 ae_eq lebesgue_measure setT ('d charge_of_finite_measure (mfrestr mU Uoo) '/d
 [the sigma_finite_measure _ _ of @lebesgue_measure R])
 (EFin \o \1_U).
Proof.
apply: integral_ae_eq => //=.
- admit.
- admit.
move=> E _ mE.
rewrite -Radon_Nikodym_integral.
rewrite integral_indic/=.
by rewrite /mfrestr/mrestr setIC.
Admitted.
*)

(*
Lemma radon_nikodym_crestr U (mU : measurable U) :
 ae_eq lebesgue_measure setT ('d charge_of_finite_measure (mfrestr mU Uoo) '/d
 [the sigma_finite_measure _ _ of @lebesgue_measure R])
 (EFin \o \1_U).
Proof.
*)

(*
rewrite [RHS](_:_= ('d charge_of_finite_measure (mfrestr mU Uoo) '/d
 [the sigma_finite_measure _ _ of @lebesgue_measure R])
 (EFin \o \1_U)
  move=> x _.
  rewrite epatch_indic.
  rewrite -radon_nikodym_crestr.
rewrite [RHS]integral_mkcond.
under [RHS]eq_integral do rewrite epatch_indic.

rewrite -integral_pushforward.
apply: eq_integral.
move=> x _.
Admitted.
*)

(*
Lemma normal_shift0 x : 
normal_prob2 x =
  @pushforward _ _ _
  (measurableTypeR R) _ (normal_prob2 0%R) (fun z => z + x)
     :> (set R -> \bar R).
Proof.
apply: funext.
move=> U.
rewrite /normal_prob2/=.
rewrite /pushforward/=.
rewrite /normal_prob.
rewrite shift_preimage.
rewrite integration_by_substitution_shift/=.
apply: eq_integral.
move=> z Uz.
congr EFin.
rewrite /normal_pdf/=.
rewrite ifF; last exact/negP/negP.
rewrite ifF; last exact/negP/negP.
rewrite {2}/normal_fun.
by rewrite subr0.
Qed.
*)

(*
Lemma measurable_normal_prob2_ocitv a b:
 measurable_fun [set: R] (normal_prob2 ^~ `]a, b]%classic).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.

rewrite /normal_prob2/=.
rewrite /normal_prob.

under [X in measurable_fun _ X]eq_fun.
  move=> x.
  rewrite (_: normal_kernel _ _ = (fine (normal_kernel x `]a, b]%classic))%:E); last first.
      rewrite fineK//.
      rewrite ge0_fin_numE//.
      apply: (@le_lt_trans _ _ 1%E); last exact: ltey.
      exact: probability_le1.
    rewrite normal_shift0/=.
  over.
apply: measurableT_comp; last by [].
apply: measurableT_comp; first exact: EFin_measurable.
rewrite /=.
under [X in measurable_fun _ X]eq_fun.
  move=> x.
  rewrite /normal_prob.
(pushforward_shift_itv (normal_kernel 0) a b x).
apply: continuous_measurable_fun.
*)

Local Open Scope ereal_scope.

Lemma integral_normal_prob (f : R -> \bar R) (m : R) U : measurable U -> measurable_fun U f ->
  \int[normal_prob2 m]_(x in U) `|f x| < +oo ->
  \int[normal_prob2 m]_(x in U) f x = \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E) :> \bar R.
Proof.
Abort.

Local Close Scope ereal_scope.

(*
Lemma continuousT_integralT (f : R -> R -> R) :
(forall l, mu.-integrable setT (fun x => (f l x)%:E)) ->
{ae mu, forall x, {for x, continuous (fun l => f l x)}} ->
(exists g : R -> R, forall l x, `|f l x| <= g x) ->
continuous (fun l => \int[mu]_x f l x).
Proof.
Abort.
*)


Lemma normal_prob_fin_num (m : R) U : normal_prob m s U \is a fin_num.
Proof.
Admitted.

Lemma integrable_normal_pdf0 U z :  mu.-integrable U
    (fun x : R => (normal_pdf 0 s (x - z))%:E).
Proof.
Abort.

(*
Lemma shift_continuous (x : R) : continuous (shift x).
Proof.
Admitted.

Lemma add_continuous (x : R) : continuous (+%R x).
Proof.
Admitted.
*)

Local Import Num.ExtraDef.

Local Definition f (m x : R) :=
  (fun n => let sigma := s ^+ 2 in
  ((sqrtr (sigma * pi *+ 2))^-1 *
  series (exp_coeff (- ((x - m) ) ^+ 2 / (sigma *+ 2))) (2 * n)%N)%:E).

Lemma near_f_ge0 : \forall n \near \oo, forall m x, (0 <= f m x n)%E.
Proof.
Admitted.
(*
apply: lt_lim.
- move => n0 n1 n01.
  rewrite ler_pM2l; last first.
    rewrite invr_gt0.
    rewrite sqrtr_gt0.
    rewrite pmulrn_rgt0//.
    rewrite mulr_gt0//.
      by rewrite exprn_even_gt0.
    exact: pi_gt0.
  set X := (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)).
  have [N] := (exp_coeff2_near_in_increasing X).
(*
near=> n.
apply: mulr_ge0.
  rewrite invr_ge0.
  exact: sqrtr_ge0.
have : series (exp_coeff (- (x - m) ^+ 2 / (s ^+ 2 *+ 2))) (2 * n)%N @[n --> \oo] --> expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)).
*)
  admit.
  admit.
rewrite /expR.
Admitted.
*)

Lemma near_nd_f : \forall N \near \oo, forall m x,
  {in [set n | (N <= n)%N]&, nondecreasing (f m x)}.
Proof.
near=> N.
move=> m x n0 n1; rewrite !inE/= => Nn0 Nn1 n01.
rewrite /f lee_fin ler_pM2l; last first.
  rewrite invr_gt0 sqrtr_gt0.
  rewrite pmulrn_lgt0//.
  rewrite mulr_gt0//.
    by rewrite exprn_even_gt0.
  exact: pi_gt0.
Admitted.

Lemma f_first_continuous (n : nat) (x : R) :
  continuous (fun m => fine (f m x n)).
Proof.
Admitted.

Lemma f_second_continuous (n : nat) (x : R) :
  continuous (fine \o (f x ^~ n)).
Proof.
Admitted.

Lemma measurable_f_second (m : R) n : measurable_fun setT (f m ^~ n).
Proof.
Abort.

Lemma cvg_f m x : (f m x n) @[n --> \oo] --> (normal_pdf m s x)%:E.
Proof.
rewrite /f/normal_pdf.
rewrite ifF; last exact/negP/negP.
apply/cvg_EFin.
  exact/nearW.
apply: cvgMr.
have : (2 * n)%N @[n --> \oo] --> \oo.
  under eq_cvg do rewrite mulnC.
  exact: cvg_mulnr.
move/cvg_comp; apply.
exact: is_cvg_series_exp_coeff.
Qed.


Lemma integral_f_fin_num x Ys n : (\int[mu]_(x0 in Ys) f x x0 n)%E \is a fin_num.
Admitted.

Lemma cvg_integral_f m Ys : measurable Ys ->
 (\int[mu]_(x in Ys) f m x n)%E @[n --> \oo] --> normal_prob m s Ys.
Proof.
move=> mYs.
rewrite /normal_prob.
rewrite [X in _ --> X](_ : _ = (\int[mu]_(x in Ys) (limn (f m x)))%E); last first.
  apply: eq_integral => y _.
  apply/esym/cvg_lim => //.
  exact: cvg_f.
apply: cvg_near_monotone_convergence => //.
move=> n.
rewrite /f.
(* ge0_emeasurable_sum *)
- admit.
- near=> n.
  move=> x Ysx.
  rewrite /f.
admit.
near=> n.
move=> x Ysx.
Admitted.

Lemma integrable_f x Ys n : mu.-integrable Ys ((f x)^~ n).
Admitted.

(* outline of proof:
   1. It is enough to prove that `(fun x => normal_prob x s Ys)` is continuous for
      all measurable set `Ys`.
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

Let g' a e : R -> R := fun x => if (x \in (ball a e : set R^o)) then
  (Num.sqrt (s ^+ 2 * pi *+ 2))^-1 *
          expR (- 0%R ^+ 2 / (s ^+ 2 *+ 2))
else
  (Num.sqrt (s ^+ 2 * pi *+ 2))^-1 *
          expR (- (`|x - a| - e) ^+ 2 / (s ^+ 2 *+ 2)).

Let ballFE_le (a e x : R) : x <= (a - e)%R -> (x \in (ball a e : set R^o)) = false.
Proof.
move=> xae.
apply: memNset.
rewrite ball_itv/= in_itv/=; apply/negP/andP/not_andP; left.
by apply/negP; rewrite -leNgt.
Qed.

Let ballFE_ge (a e x : R) : a + e <= x -> (x \in (ball a e : set R^o)) = false.
Proof.
move=> xae.
apply: memNset.
rewrite ball_itv/= in_itv/=; apply/negP/andP/not_andP; right.
by apply/negP; rewrite -leNgt.
Qed.

Lemma g'a0 (a : R) : g' a 0 = normal_pdf0 a s.
Proof.
rewrite /g'.
apply/funext => x.
have /orP [x0|x0] := le_total x a.
  rewrite ballFE_le; last by rewrite subr0.
  by rewrite subr0 real_normK// num_real.
rewrite ballFE_ge; last by rewrite addr0.
by rewrite subr0 real_normK// num_real.
Qed.

Lemma mg' a e : measurable_fun setT (g' a e).
Proof.
apply: measurable_fun_if => //.
  apply: (measurable_fun_bool true) => /=.
  rewrite setTI preimage_mem_true.
  exact: measurable_ball.
apply: measurable_funTS => /=.
apply: measurableT_comp => //.
apply: measurableT_comp => //.
apply: measurable_funM => //.
apply: measurableT_comp => //.
apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => t ^+ 2)) => //.
apply: measurable_funB => //.
apply: measurableT_comp => //.
exact: measurable_funD.
Qed.

Lemma g'_ge0 a e x : 0 <= g' a e x.
Proof.
rewrite /g'; case: ifP => _.
  rewrite -[in leRHS](@subr0 _ 0) -normal_pdfE ?subr0; apply: normal_pdf_ge0.
rewrite -normal_pdfE; exact: normal_pdf_ge0.
Qed.

Lemma continuous_g' (a e : R) : (0 <= e) -> continuous (g' a e).
Proof.
move=> e0.
have tmp k : k < a - e -> ((`|k - a| - e) ^+ 2 = (k - (a - e)) ^+ 2).
  move=> kae.
  rewrite -normrN opprB.
  have /normr_idP -> : (0 <= a - k).
    by rewrite subr_ge0 ltW// (lt_le_trans kae)// gerBl.
  by rewrite -sqrrN !opprB addrCA.
have tmp2 k : a + e < k -> ((`|k - a| - e) ^+ 2 = (k - (a + e)) ^+ 2).
  move=> kae; rewrite opprD addrA.
  have /normr_idP -> // : (0 <= k - a).
  by rewrite subr_ge0 ltW// (le_lt_trans _ kae)// lerDl.
apply: (@in1TT R).
rewrite -continuous_open_subspace; last exact: openT.
rewrite (_:[set: R] =
 `]-oo, (a - e)%R] `|` `[(a - e)%R, a + e] `|` `[a + e, +oo[); last first.
  rewrite -setUitv1// -setUA setUAC setUA -itv_bndbnd_setU//; last first.
    by rewrite bnd_simp lerD// ge0_cp.
  rewrite -setUitv1// -setUA setUAC setUA -itv_bndbnd_setU//.
  by rewrite set_itvE !setTU.
apply: withinU_continuous.
      rewrite -setUitv1//.
      rewrite -setUA setUCA.
      rewrite -itv_bndbnd_setU//; last first.
        by rewrite bnd_simp lerD// ge0_cp.
      rewrite setUidr//.
      move=> _/= ->; rewrite in_itv/=.
      by rewrite lerD// ge0_cp.
    by apply: interval_closed.
  apply: withinU_continuous; first exact: interval_closed.
      exact: interval_closed.
    apply/continuous_within_itvNycP; split.
      move=> x.
      rewrite in_itv/= => xae.
      apply/(@cvgrPdist_le _ R^o R _ _ (g' a e) (g' a e x)).
      rewrite /=.
      move=> eps eps0.
      near=> t.
      have tae : t < a - e.
        near: t.
        exact: lt_nbhsl.
      rewrite /g'.
      rewrite !ballFE_le ?(@ltW _ _ _ (a - e))//.
      rewrite !tmp//.
      move=> {tae}; near: t.
      move: eps eps0.
      apply/(@cvgrPdist_le _ _ _ (nbhs x)).
      exact: continuous_normal_pdf0.
    apply/(@cvgrPdist_lt _ R^o).
    move=> eps eps0.
    near=> t.
    rewrite /g' !ballFE_le//.
    rewrite -addrAC subrr sub0r normrN; have /normr_idP -> := e0.
    rewrite subrr -(subrr (a - e)) tmp//.
    near: t; move: eps eps0.
    apply/(@cvgrPdist_lt _ R^o).
    apply: cvg_at_left_filter.
    exact: continuous_normal_pdf0.
  move: e0; rewrite le_eqVlt => /predU1P; case => [<- | e0].
    rewrite g'a0.
    apply: continuous_subspaceT.
    exact: continuous_normal_pdf0.
  apply/continuous_within_itvP; first by rewrite -(opprK e) ler_ltB// opprK gtrN.
  split.
      move=> x xae.
      rewrite /continuous_at.
      rewrite /g' ifT; last by rewrite ball_itv inE/=.
      apply/(@cvgrPdist_le _ R^o).
      move=> eps eps0.
      near=> t.
      rewrite ifT; first by rewrite subrr normr0 ltW.
      rewrite ball_itv inE/= in_itv/=; apply/andP; split.
        near: t.
        apply: lt_nbhsr.
        by move: xae; rewrite in_itv/= => /andP[].
      near: t.
      apply: lt_nbhsl.
      by move: xae; rewrite in_itv/= => /andP[].
    apply/(@cvgrPdist_le _ R^o).
    move=> eps eps0.
    near=> t.
    rewrite /g' ballFE_le// ifT; last first.
      rewrite ball_itv inE/= in_itv/=; apply/andP => []; split => //.
      near: t.
      apply: nbhs_right_lt.
      by rewrite -(opprK e) ler_ltB// opprK gtrN.
    rewrite addrAC subrr sub0r normrN; have /ltW/normr_idP -> := e0.
    by rewrite !subrr normr0 ltW.
  apply/(@cvgrPdist_le _ R^o).
  move=> eps eps0.
  near=> t.
  rewrite /g' ballFE_ge// ifT; last first.
    rewrite ball_itv inE/= in_itv/=; apply/andP => []; split => //.
    near: t.
    apply: nbhs_left_gt.
    by rewrite -(opprK e) ler_ltB// opprK gtrN.
  rewrite addrAC subrr add0r; have /ltW/normr_idP -> := e0.
  by rewrite !subrr normr0 ltW.
apply/continuous_within_itvcyP; split.
  move=> x.
  rewrite in_itv/= andbT => aex.
  apply/(@cvgrPdist_le _ R^o).
  rewrite /=.
  move=> eps eps0.
  near=> t.
  have tae : a + e < t.
    near: t.
    exact: lt_nbhsr.
  rewrite /g'.
  rewrite !ballFE_ge ?(@ltW _ _ (a + e)%E)//.
  rewrite !tmp2// ?(@ltW _ _ (a + e)).
  move=> {tae}; near: t.
  move: eps eps0.
  apply/(@cvgrPdist_le _ _ _ (nbhs x)).
  exact: continuous_normal_pdf0.
apply/(@cvgrPdist_le _ R^o).
move=> eps eps0.
near=> t.
rewrite /g' !ballFE_ge//.
rewrite addrAC subrr add0r; have /normr_idP -> := e0.
rewrite subrr -(subrr (a + e)).
rewrite tmp2//.
near: t.
move: eps eps0.
apply/cvgrPdist_le.
apply: cvg_at_right_filter.
apply: continuous_normal_pdf0.
Unshelve. all: end_near. Qed.

Lemma gE_Ny a e : (0 <= e) ->
  (\int[mu]_(x in `]-oo, (a - e)%R]) `|g' a e x|%:E =
    \int[mu]_(x in `]-oo, a]) `|normal_pdf a s x|%:E)%E.
Proof.
move=> e0.
rewrite ge0_integration_by_substitution_shift_itvNy => /=; first last.
- move=> ? _; exact: normr_ge0.
- apply/continuous_subspaceT.
  move=> x.
  apply: continuous_comp; first exact: continuous_g'.
  exact: (@norm_continuous _ R^o) .
under eq_integral.
  move=> x.
  rewrite inE/= in_itv/= => xae.
  rewrite /g' ballFE_le//; last exact: lerB.
  rewrite -(normrN (x - e - a)) !opprB addrA.
  have /normr_idP -> : 0 <= a + e - x by rewrite subr_ge0 ler_wpDr.
  rewrite -(addrAC _ (- x)) addrK.
  rewrite -(sqrrN (a - x)) opprB.
  over.
by under [RHS]eq_integral do rewrite normal_pdfE.
Qed.

Lemma gE_y a e : (0 <= e) ->
  (\int[mu]_(x in `[a + e, +oo[) `|g' a e x|%:E =
    \int[mu]_(x in `[a, +oo[) `|normal_pdf a s x|%:E)%E.
Proof.
move=> e0.
rewrite ge0_integration_by_substitution_shift_itvy => /=; first last.
- move=> ? _.
  exact: normr_ge0.
- apply/continuous_subspaceT.
  move=> x.
  apply: continuous_comp; first exact: continuous_g'.
  exact: (@norm_continuous _ R^o).
under eq_integral.
  move=> x.
  rewrite inE/= in_itv/= andbT => aex.
  rewrite /g' ballFE_ge//; last exact: lerD.
  have /normr_idP -> : 0 <= x + e - a by rewrite subr_ge0 ler_wpDr.
  rewrite -(addrAC _ (- a)) addrK.
  over.
by under [RHS]eq_integral do rewrite normal_pdfE.
Qed.

Lemma normal_prob_continuous (V : set R) : measurable V ->
 continuous (fun m => fine (normal_prob m s V)).
Proof.
move=> mV a.
near (0 : R)^'+ => e.
set g := g' a e.
have mg := mg' a e.
apply: (@continuity_under_integral _ _ _ mu _ _ _ _ (a - e) (a + e) _ _ _ g) => //=.
- rewrite in_itv/=.
  by rewrite ltrDl gtrBl andbb.
- move=> x _.
  apply: (integrableS measurableT) => //.
  exact: integrable_normal_pdf.
- apply/aeW => y _.
  move=> x.
  under [X in _ _ X]eq_fun do rewrite normal_pdfE -(sqrrN (y - _)) opprB.
  exact: continuous_normal_pdf0.
- apply: (integrableS measurableT) => //=.
  apply/integrableP; split.
    exact/measurable_EFinP.
  rewrite -(setUv (ball a e)).
  rewrite ge0_integral_setU//=; first last.
          exact/disj_setPCl.
        rewrite setUv.
        apply/measurable_EFinP.
        exact: measurableT_comp.
      apply: measurableC.
      exact: measurable_ball.
    exact: measurable_ball.
  apply: lte_add_pinfty.
    under eq_integral.
      move=> x xae.
      rewrite /g/g' xae.
      rewrite expr0n/= oppr0 mul0r expR0 mulr1.
      over.
    rewrite integral_cst/=.
      apply: lte_mul_pinfty => //.
      rewrite ball_itv lebesgue_measure_itv/= ifT -?EFinD ?ltry// lte_fin.
      by rewrite ltrBlDr -addrA -ltrBlDl subrr -mulr2n mulrn_wgt0.
    exact: measurable_ball.
  have -> : (\int[mu]_(x in ~` ball a e) `|g x|%:E = \int[mu]_x `|normal_pdf a s x|%:E)%E.
    rewrite ball_itv setCitv ge0_integral_setU//=; first last.
        apply/disj_setPRL.
        rewrite setCitvl.
        apply: subset_itvr; rewrite bnd_simp.
        rewrite -{2}(opprK e); apply: ler_ltB => //.
        exact: gtrN.
      apply: measurable_funTS.
      apply/measurable_EFinP.
      exact: measurableT_comp.
    rewrite gE_Ny// gE_y//.
    rewrite -integral_itv_obnd_cbnd; last first.
      apply: measurableT_comp => //.
      apply: measurable_funTS.
      exact: measurable_normal_pdf.
    rewrite -ge0_integral_setU/= ?measurable_itv//; first last.
        apply/disj_setPRL.
        by rewrite setCitvl.
      rewrite -setCitvl setUv.
      apply/measurable_EFinP.
      apply: measurableT_comp => //.
      exact: measurable_normal_pdf.
    by rewrite -setCitvl setUv.
  under eq_integral => x do rewrite (_:_%:E = `|(normal_pdf a s x)%:E|%E)//.
  apply/abse_integralP; rewrite //=.
    apply/measurable_EFinP.
    exact: measurable_normal_pdf.
  by rewrite integral_normal_pdf ltry.
move=> x ax.
apply/aeW => y Vy.
have /normr_idP -> : 0 <= normal_pdf x s y by apply: normal_pdf_ge0.
rewrite normal_pdfE /g/g'.
case: ifP.
  move=> _.
  rewrite ler_pM//.
  rewrite expr0n/= oppr0 mul0r ler_expR.
  apply: mulr_le0_ge0.
    rewrite oppr_le0.
    exact: sqr_ge0.
  by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
move/negP/negP; rewrite notin_setE/= ball_itv/= in_itv/= => Hy.
rewrite ler_pM//.
rewrite ler_expR.
rewrite !mulNr lerN2.
rewrite ler_pM => //.
    exact: sqr_ge0.
  by rewrite invr_ge0 mulrn_wge0// sqr_ge0.
move: Hy; move/negP/nandP; rewrite -!leNgt; case => [yae|aey].
  rewrite -normrN opprB.
  have /normr_idP -> : 0 <= a - y.
    rewrite subr_ge0.
    apply: (le_trans yae).
    by rewrite gerBl.
  rewrite -[leRHS]sqrrN opprB.
  rewrite ler_sqr ?nnegrE; first last.
      rewrite subr_ge0.
      apply/ltW; apply: (le_lt_trans yae).
      by move: ax; rewrite in_itv/= => /andP[].
    by rewrite addrAC subr_ge0.
  rewrite addrAC lerD2r.
  by apply/ltW; move: ax; rewrite in_itv/= => /andP[].
have /normr_idP -> : 0 <= y - a.
  rewrite subr_ge0; apply: le_trans aey.
  by rewrite lerDl.
rewrite ler_sqr ?nnegrE; first last.
    rewrite subr_ge0.
    apply: le_trans aey.
    apply/ltW.
    by move: ax; rewrite in_itv/= => /andP[].
  by rewrite -addrA -opprD subr_ge0.
rewrite -addrA -opprD.
rewrite lerD2l lerN2.
by rewrite ltW//; move: ax; rewrite in_itv/= => /andP[].
Unshelve. end_near.

(* (note for 3.)
have mlimf : measurable_fun Ys (fun x0 => limn [eta f x x0])%E.
  admit.
have H1 : {ae mu, forall x0, Ys x0 -> f x x0 x1 @[x1 --> \oo] --> (limn [eta f x x0])%E}.
  admit. 
    have e x : \bar R := (expR (- x ^+ 2 / (s^+2 *+ 2)))%:E.
have : forall M x0, exists x, (`| f x x0 1 | > M)%E.
move=> M x0.
    have H2 : mu.-integrable Ys e.
      admit.
    have H3 : \forall N \near \oo, {ae mu, forall x0 n, (N <= n)%N ->  Ys x0 -> (`|f x x0 n| <= e x0)%E}.
      admit.
    have [Hdc1 Hdc2 Hdc3] := dominated_convergence mYs mf mlimf H1 H2 H3.
    exact: Hdc3.
*)
Admitted.

(* (note for 1.)
    admit.
  under [X in limn X]eq_fun do rewrite (fineK (integral_f_fin_num _ _ _)).
  over.
rewrite /=.
apply: (emeasurable_fun_cvg (fun n : nat => fun x => (\int[mu]_(x0 in Ys) f x x0 n)%E)).
  move=> m/=.
  under [X in _ _ X]eq_fun do rewrite -(fineK (integral_f_fin_num _ _ _)); apply/measurable_EFinP => /=.
  apply: continuous_measurable_fun.
  apply: continuousT_integral => /=.
  - admit.
  - apply: aeW => /= x.
    admit.
  - exists (cst (Num.sqrt (s^+2 * pi *+ 2))^-1 * 1).
    admit.
move=> x _.
rewrite /f.
rewrite -near_monotone_convergence//; first last.
- admit.
- admit.
- move=> n; apply: measurable_funTS; exact: (measurable_f_second x n).
apply: cvg_near_monotone_convergence => //.
- admit.
- admit.
move=> /= y _.
have := exp_coeff2_near_in_increasing (- (y - x) ^+ 2 / (s ^+ 2 *+ 2)).
move=> [] N _ Hnear.
exists N => //.
move=> k/= Nk n' m'; rewrite !inE/= => kn' km' n'm'.
rewrite lee_fin.
rewrite ler_pM2l; last first.
  rewrite invr_gt0.
  rewrite sqrtr_gt0.
  rewrite pmulrn_lgt0//.
  rewrite mulr_gt0//.
    by rewrite exprn_even_gt0.
  exact: pi_gt0.
by apply: (Hnear k) => //; rewrite !inE/=.
Admitted.

(*
under [X in _ _ X]eq_fun do rewrite -(fineK (normal_prob_fin_num _ Ys)).
apply/measurable_EFinP.
apply: (@measurability _ _ _ _ _ _ (@RGenOpens.G R)).
  by rewrite /measurable/=/measurableR RGenOpens.measurableE.
move=> _ -[_ [a [b ->]] <-].
rewrite setTI.
apply: is_interval_measurable.
move=> x y/=.
*)
move=> _ -[_ [r r01] [Ys mYs <-]] <-.
apply: emeasurable_fun_infty_o => //=.
under [X in _ _ X]eq_fun.
  move=> x.
  rewrite -(fineK (normal_prob_fin_num x Ys)).
  rewrite normal_shift0//=.
  rewrite /pushforward.
  rewrite shift_preimage.
  rewrite /normal_prob/=.
  rewrite integration_by_substitution_shift/=. (* TODO *)
  over.
apply: measurableT_comp => //=.
apply/measurable_EFinP => /=.
apply: continuous_measurable_fun => /=.
apply: (@continuousT_integral (fun x0 x1 : R => normal_pdf 0 s (x1 - x0)) Ys).
- move=> z.
  exact: integrable_normal_pdf0.
- apply: aeW => /=.
  rewrite /measurable/=/g_sigma_algebraType/ocitv_type.
  move=> x.
  apply: continuous_comp => //=.
    apply: continuous_comp.
      exact: (@opp_continuous _ R^o).
    exact: (@add_continuous x).
  exact: continuous_normal_pdf.
exists (cst ((Num.sqrt (s^+2 * pi *+ 2))^-1)).
move=> x _ y/=.
rewrite /normal_pdf; case: ifP => [|_]; first by move/negP: s0.

admit.
Admitted.
*)

(*
Lemma measurable_normal_prob2' :
forall U : set R, measurable U -> measurable_fun [set: R] (normal_prob2 ^~ U).
Proof.
move=> U mU.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
rewrite /normal_kernel/=.


under [X in measurable_fun _ X]eq_fun.
  move=> x.
  rewrite (_: normal_kernel _ _ = (fine (normal_kernel x U))%:E); last first.
    admit.
    rewrite normal_shift0/=.
  over.
apply: measurableT_comp; last by [].
apply: measurableT_comp; first exact: EFin_measurable.
rewrite /=.
apply: continuous_measurable_fun.
(*
apply: continuous_comp.
under [X in continuous X]eq_fun.
  move=> x.
  rewrite normal_shift0/=.
  over.
+\*)
Admitted.
*)

(*
HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ normal_prob2 measurable_normal_prob2.
*)

Lemma measurable_normal_prob2 :
  measurable_fun setT (normal_prob2 : R -> pprobability _ _).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=>_  -[_ [r r01] [Ys mYs <-]] <-.
apply: emeasurable_fun_infty_o => //=.
under [X in _ _ X]eq_fun.
  move=> x.
  rewrite -(@fineK _ (normal_prob x s Ys)); last first.
(*  rewrite -(@fineK _ (\int[_]_(_ in Ys) _)%E); last exact: integral_f_fin_num. *)
    rewrite ge0_fin_numE => //.
    apply: (@le_lt_trans _ _ (normal_prob x s setT)).
      by apply: le_measure => //; rewrite inE/=.
    apply: (@le_lt_trans _ _ 1%E).
      exact: probability_le1.
    exact: ltey.
  over.
apply/measurable_EFinP.
apply: continuous_measurable_fun.
exact: normal_prob_continuous.
Qed.

End normal_kernel.

Section normal_probability.
Context {R : realType}.

Lemma measurable_normal_s_prob (s : R) :
  measurable_fun setT
  (fun m : R => normal_prob m s : pprobability _ _).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
Admitted.
(*
have := measurable_normal_prob2 (integral_normal^~ s) mYs.
Qed.
*)

End normal_probability.

Section dirac_delta.
Local Open Scope ereal_scope.
Context {R: realType}.
Local Notation mu := lebesgue_measure.

Hypothesis integral_normal : forall (m : R) (s : {posnum R}),
  (\int[@lebesgue_measure R]_x (normal_pdf m s%:num x)%:E = 1%E)%E.

Definition dirac_delta (m x : R) : \bar R := lim ((normal_pdf m s x)%:E @[s --> 0^'+]).

Lemma integralT_dirac_delta m :
  \int[mu]_x dirac_delta m x = 1.
Proof.
rewrite [LHS](_:_= lim ((\int[mu]_x (normal_pdf m s x)%:E) @[s --> 0^'+])); last first.
  rewrite /dirac_delta.
  (* rewrite monotone_convergence *)
  admit.
apply: lim_near_cst => //.
near=> s.
have [s0 s0s]: exists s' : {posnum R}, s'%:num = s.
  have s0 : (0 < s)%R by [].
  by exists (PosNum s0).
rewrite -s0s.
apply: integral_normal.
Abort.

Lemma dirac_deltaE x A :
  \int[mu]_(y in A) dirac_delta x y = \d_x A.
Proof.
rewrite diracE.
Abort.

End dirac_delta.
