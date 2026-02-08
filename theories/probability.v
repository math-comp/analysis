(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import poly ssrnum ssrint interval archimedean finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals interval_inference ereal topology normedtype.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
From mathcomp Require Import charge ftc gauss_integral hoelder.

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
(*     bernoulli_prob p == Bernoulli probability measure when 0 <= p <= 1     *)
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
(*          XMonemX a b := x ^+ a * x.~ ^+ b                                  *)
(*         beta_fun a b := \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1] x)          *)
(*             beta_pdf == probability density function for beta              *)
(*            beta_prob == beta probability measure                           *)
(* div_beta_fun a b c d := beta_fun (a + c) (b + d) / beta_fun a b            *)
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
    by exists (truncn (X t)).+1 => //=; rewrite in_itv/= ltW// truncnS_gt.
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
    set m := (truncn `|X t|).+1.
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
    + by rewrite (lt_le_trans (ltNyr 0%R)) ?le_ereal_inf_tmp//= => l[? _] <-.
    + rewrite (le_lt_trans _ (ltry 1%R))// ge_ereal_inf//=.
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
by move=> *; rewrite fine_le ?fin_num_measure// cdf_nondecreasing.
Qed.

Let fcdf_rc : right_continuous fcdf.
Proof.
move=> a; apply: fine_cvg.
by rewrite fineK ?fin_num_measure//; exact: cdf_right_continuous.
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
rewrite wlength_itv_bnd// EFinB !fineK ?fin_num_measure//.
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
rewrite /cdf /ccdf -measureU//= -eq_opE; last exact: disjoint_rays.
by rewrite itv_setU_setT probability_setT.
Qed.

Corollary ccdf_cdf_1 r : ccdf X r + cdf X r = 1.
Proof. by rewrite -(cdf_ccdf_1 r) addeC. Qed.

Corollary ccdf_1_cdf r : ccdf X r = 1 - cdf X r.
Proof. by rewrite -(ccdf_cdf_1 r) addeK ?fin_num_measure. Qed.

Corollary cdf_1_ccdf r : cdf X r = 1 - ccdf X r.
Proof. by rewrite -(cdf_ccdf_1 r) addeK ?fin_num_measure. Qed.

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

Section tail_expectation_formula.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Let mu : {measure set _ -> \bar R} := @lebesgue_measure R.

Lemma ge0_expectation_ccdf (X : {RV P >-> R}) : (forall x, 0 <= X x)%R ->
  'E_P[X] = \int[mu]_(r in `[0%R, +oo[) ccdf X r.
Proof.
pose GR := measurableTypeR R.
pose distrX := distribution P X.
pose D : set R := `[0%R, +oo[%classic.
move=> X_ge0.
transitivity (\int[P]_x ((EFin \_ D) \o X) x).
  rewrite expectation_def; apply: eq_integral => x _ /=.
  by rewrite /D patchE ifT// set_itvE inE /=.
transitivity (\int[distrX]_r (EFin \_ D) r).
  rewrite ge0_integral_distribution// -?measurable_restrictT /D// => r.
  by apply: erestrict_ge0 => s /=; rewrite in_itv/= andbT lee_fin.
transitivity (\int[distrX]_r (\int[mu]_(s in D) (\1_`]-oo, r[ s)%:E)).
  apply: eq_integral => r _.
  rewrite integral_indic /D//= setIC -(set_itv_splitI `[0%R, r[).
  rewrite lebesgue_measure_itv/= lte_fin patchE.
  have [r_pos | r_neg | <-] := ltgtP.
  - by rewrite mem_set ?EFinN ?sube0//= in_itv/= ltW.
  - by rewrite memNset//= in_itv/= leNgt r_neg.
  - by rewrite mem_set//= in_itv/= lexx.
transitivity (\int[distrX]_r (\int[mu]_s (\1_`[0, r[ s)%:E)).
  apply: eq_integral => r _; rewrite /D integral_mkcond.
  apply: eq_integral => /= s _.
  have [s_ge0 | s_lt0] := leP 0%R s.
  - have [s_ltr | s_ger] := ltP s r.
    + rewrite indicE mem_set/=; last by rewrite in_itv/= s_ge0 s_ltr.
      by rewrite patchE/= ifT ?indicE mem_set//= in_itv/= andbT.
    + rewrite indicE memNset/=; last by rewrite in_itv/= s_ge0 ltNge s_ger.
      rewrite patchE ifT//; last by rewrite mem_set//= in_itv/= andbT.
      by rewrite indicE memNset//= in_itv/= ltNge s_ger.
  - rewrite indicE memNset/=; last by rewrite in_itv/= leNgt s_lt0.
    by rewrite patchE/= ifF// memNset//= in_itv/= andbT leNgt s_lt0.
transitivity (\int[mu]_s (\int[distrX]_r (\1_`[0, r[ s)%:E)).
  rewrite (fubini_tonelli (fun p : R * GR => (\1_`[0, p.1[ p.2)%:E))//=.
  apply/measurable_EFinP/measurable_indic => /=.
  pose fsnd (p : R * GR) := (0 <= p.2)%R.
  pose f21 (p : R * GR) := (p.2 < p.1)%R.
  rewrite [X in measurable X](_ : _ =
      fsnd @^-1` [set true] `&` f21 @^-1` [set true]); last first.
    by apply/seteqP; split => p; rewrite in_itv/= => /andP.
  apply: measurableI.
  - have : measurable_fun setT fsnd by exact: measurable_fun_ler.
    by move=> /(_ measurableT [set true]); rewrite setTI; exact.
  - have : measurable_fun setT f21 by exact: measurable_fun_ltr.
    by move=> /(_ measurableT [set true]); rewrite setTI; exact.
transitivity (\int[mu]_(s in D) (\int[distrX]_r (\1_`[0, r[ s)%:E)).
  rewrite [in RHS]integral_mkcond/=.
  apply: eq_integral => s _; rewrite patchE /D.
  have [s0|s0] := leP 0%R s; first by rewrite mem_set//= in_itv/= s0.
  rewrite memNset//= ?in_itv/= ?leNgt ?s0//.
  by apply: integral0_eq => r _; rewrite indicE/= memNset//= in_itv/= leNgt s0.
apply: eq_integral => s; rewrite /D inE/= in_itv/= andbT => s_ge0.
rewrite integral_indic//=.
  rewrite /ccdf setIT set_itvoy; congr distribution.
  by apply/funext => r/=; rewrite in_itv/= s_ge0.
pose fgts (r : R) := (s < r)%R.
have : measurable_fun setT fgts by exact: measurable_fun_ltr.
rewrite [X in measurable X](_ : _ = fgts @^-1` [set true]).
  by move=> /(_ measurableT [set true]); rewrite setTI; exact.
by apply: eq_set => r; rewrite in_itv/= s_ge0.
Qed.

End tail_expectation_formula.

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
by apply/funeqP => x; rewrite !fctE/= subrr mul0r.
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
by apply/funext => x; rewrite !fctE/= subrr mulr0.
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
apply/eqP; have -> : fine 'V_P[X] = (u0 * lambda)%R by rewrite divfK ?gt_eqF.
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

Section pmf_definition.
Context {d} {T : measurableType d} {R : realType}.
Variables (P : probability T R).

Definition pmf (X : {RV P >-> R}) (r : R) : R := fine (P (X @^-1` [set r])).

Lemma pmf_ge0 (X : {RV P >-> R}) (r : R) : 0 <= pmf X r.
Proof. by rewrite fine_ge0. Qed.

End pmf_definition.

Section pmf_measurable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (P : probability T R) (X : {RV P >-> R}).

Lemma pmf_gt0_countable : countable [set r | 0 < pmf X r]%R.
Proof.
rewrite [X in countable X](_ : _ =
    \bigcup_n [set r | n.+1%:R^-1 < pmf X r]%R); last first.
  by apply/seteqP; split=> [r/= /ltr_add_invr[k /[!add0r] kXr]|r/= [k _]];
    [exists k|exact: lt_trans].
apply: bigcup_countable => // n _; apply: finite_set_countable.
apply: contrapT => /infiniteP/pcard_leP/injfunPex[/= q q_fun q_inj].
have /(probability_le1 P) : measurable (\bigcup_k X @^-1` [set q k]).
  by apply: bigcup_measurable => k _; exact: measurable_funPTI.
rewrite leNgt => /negP; apply.
rewrite [ltRHS](_ : _ = \sum_(0 <= k <oo) P (X @^-1` [set q k])); last first.
  rewrite measure_bigcup//; first by apply: eq_eseriesl =>// i; rewrite in_setT.
  rewrite (trivIset_comp (fun r => X@^-1` [set r]))//.
  exact: trivIset_preimage1.
apply: (lt_le_trans _ (nneseries_lim_ge n.+1 _)) => //.
rewrite -EFin_sum_fine//; last by move=> ? _; rewrite fin_num_measure.
under eq_bigr do rewrite -/(pmf X (q _)).
rewrite lte_fin (_ : 1%R = (\sum_(0 <= k < n.+1) n.+1%:R^-1:R)%R); last first.
  by rewrite sumr_const_nat subn0 -[RHS]mulr_natr mulVf.
by apply: ltr_sum => // k _; exact: q_fun.
Qed.

Lemma pmf_measurable : measurable_fun [set: R] (pmf X).
Proof.
have /countable_bijP[S] := pmf_gt0_countable.
rewrite card_eq_sym => /pcard_eqP/bijPex[/= h h_bij].
have pmf1_ge0 k s : 0 <= (pmf X (h k) * \1_[set h k] s)%:E.
  by rewrite EFinM mule_ge0// lee_fin pmf_ge0.
pose sfun r := \sum_(0 <= k <oo | k \in S) (pmf X (h k) * \1_[set h k] r)%:E.
apply/measurable_EFinP; apply: (eq_measurable_fun sfun) => [r _|]; last first.
  by apply: ge0_emeasurable_sum => // *; exact/measurable_EFinP/measurable_funM.
have [rS|nrS] := boolP (r \in [set h k | k in S]).
- pose kr := pinv S h r.
  have neqh k : k \in S /\ k != kr -> r != h k.
    move=> [Sk]; apply: contra_neq.
    by rewrite /kr => ->; rewrite pinvKV//; exact: (set_bij_inj h_bij).
  rewrite /sfun (@nneseriesD1 _ _ kr)//; last by rewrite inE; exact/invS/set_mem.
  by rewrite eseries0 => [| k k_ge0 /andP/neqh]; rewrite indicE in_set1_eq;
    [rewrite pinvK// eqxx mulr1 addr0|move/negPf => ->; rewrite mulr0].
- rewrite /sfun eseries0 => [|k k_ge0 Sk]/=.
    apply: le_anti; rewrite !lee_fin pmf_ge0/= leNgt; apply: contraNN nrS.
    by rewrite (surj_image_eq _ (set_bij_surj h_bij)) ?inE//; exact:set_bij_sub.
  rewrite indicE in_set1_eq (_ : (r == h k) = false) ?mulr0//.
  by apply: contraNF nrS => /eqP ->; exact/image_f.
Qed.

End pmf_measurable.

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

Lemma expectation_pmf (X : {dRV P >-> R}) :
  P.-integrable [set: T] (EFin \o X) ->
  'E_P[X] = \sum_(n <oo | n \in dRV_dom X)
              (@pmf _ _ _ P X (dRV_enum X n))%:E * (dRV_enum X n)%:E.
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
by rewrite !fsbig_set1/= -EFinD subrKC.
Qed.

End bernoulli_pmf.

Lemma measurable_bernoulli_pmf {R : realType} D n :
  measurable_fun D (@bernoulli_pmf R ^~ n).
Proof.
by apply/measurable_funTS/measurable_fun_if => //=; exact: measurable_funB.
Qed.

Definition bernoulli_prob {R : realType} (p : R) : set bool -> \bar R :=
  fun A => if (0 <= p <= 1)%R then
    \sum_(b \in A) (bernoulli_pmf p b)%:E
  else
    \d_false A.

Section bernoulli.
Context {R : realType} (p : R).

Local Notation bernoulli := (bernoulli_prob p).

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

Lemma bernoulli_dirac : bernoulli_prob p = measure_add
  (mscale (NngNum p0) \d_true) (mscale (1 - (Itv01 p0 p1)%:num)%:nng \d_false).
Proof.
apply/funext => U; rewrite /bernoulli_prob; case: ifPn => [p01|]; last first.
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
Arguments bernoulli_prob {R}.

Lemma eq_bernoulliV2 {R : realType} (P : probability bool R) :
  P [set true] = P [set false] -> P =1 bernoulli_prob 2^-1.
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

Lemma bernoulli_probE A :
  bernoulli_prob p A = p%:E * \d_true A + p.~%:E * \d_false A.
Proof. by case/andP : p01 => p0 p1; rewrite bernoulli_dirac// measure_addE. Qed.

Lemma integral_bernoulli_prob (f : bool -> \bar R) : (forall x, 0 <= f x) ->
  \int[bernoulli_prob p]_y (f y) = p%:E * f true + p.~%:E * f false.
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

Lemma measurable_bernoulli_prob :
  measurable_fun setT (bernoulli_prob : R -> pprobability bool R).
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

Lemma measurable_bernoulli_prob2 U : measurable U ->
  measurable_fun setT (bernoulli_prob ^~ U : R -> \bar R).
Proof.
move=> mU.
exact: (measurable_kernel (kprobability measurable_bernoulli_prob)).
Qed.

End measurable_bernoulli.
Arguments measurable_bernoulli_prob {R}.

Section binomial_pmf.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : R).

Definition binomial_pmf k := p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k).

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
have pkn k : 0%R <= (p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k))%:E.
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
have pkn k : (0%R <= (p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k))%:E)%E.
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
  bernoulli_prob (1 - p.~ ^+ n) U :> \bar R)%E.
Proof.
move=> /andP[p0 p1]; rewrite bernoulli_probE//=; last first.
  rewrite subr_ge0 exprn_ile1//=; [|exact/onem_ge0|exact/onem_le1].
  by rewrite -subr_ge0 opprB subrKC; exact/exprn_ge0/onem_ge0.
rewrite (@integral_binomial _ n p _ _ (fun y => \d_(1 <= y)%N U))//.
rewrite !big_ord_recl/=.
rewrite expr0 mul1r subn0 bin0 ltnn mulr1n addrC.
rewrite onemD opprK onem1 add0r; congr +%E.
rewrite /bump; under eq_bigr do rewrite leq0n add1n ltnS leq0n.
rewrite -ge0_sume_distrl; last first.
  move=> i _.
  by apply/mulrn_wge0/mulr_ge0; apply/exprn_ge0 => //; exact/onem_ge0.
congr *%E.
transitivity (\sum_(i < n.+1) (p.~ ^+ (n - i) * p ^+ i *+ 'C(n, i))%:E -
              (p.~ ^+ n)%:E)%E.
  rewrite big_ord_recl/=.
  rewrite expr0 mulr1 subn0 bin0 mulr1n addrAC -EFinD subrr add0e.
  by rewrite /bump; under [RHS]eq_bigr do rewrite leq0n add1n mulrC.
rewrite sumEFin -(@exprDn_comm _ p.~ p n)//.
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
apply/null_content_dominatesP.
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
by rewrite mulrn_wgt0// mulr_gt0 ?pi_gt0// exprn_even_gt0/=.
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
rewrite F'E !fctE/= -EFinM divfK// ?normal_gauss_fun//.
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
apply/null_content_dominatesP=> A mA muA0; rewrite /normal_prob /normal_pdf.
have [s0|s0] := eqVneq sigma 0.
  apply: null_set_integral => //=; apply: measurable_funTS => /=.
  exact/measurable_EFinP/measurable_indic.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: integral_ge0 => x _.
  by rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A) (normal_peak)%:E))%E; last first.
  by rewrite integral_cst//= muA0 mule0.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin mulr_ge0 ?normal_peak_ge0 ?normal_fun_ge0.
- apply/measurable_funTS/measurableT_comp => //=.
  by apply: measurable_funM => //; exact: measurable_normal_fun.
- by move=> x _; have := normal_pdf_ub m x s0; rewrite /normal_pdf (negbTE s0).
Qed.

End normal_probability.

Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable rate : R.
Hypothesis rate_ge0 : 0 <= rate.

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
under eq_integral do rewrite /= ger0_norm ?(exponential_pdf_ge0 (ltW _))//.
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
  move=> n _; rewrite /poisson_pmf rate0 EFinM muleC; over.
rewrite /= nneseriesZl/=; last first.
  by move=> n _; rewrite lee_fin divr_ge0// exprn_ge0// ltW.
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
rewrite setTI (_ : _ @^-1` _ = `]0, +oo[%classic)//.
by apply/seteqP; split => /= x /=; rewrite in_itv/= andbT.
Qed.

(**md lemmas about the function $x \mapsto (1 - x)^n$ *)
Section about_onemXn.
Context {R : realType}.
Implicit Types x y : R.

Lemma continuous_onemXn n x : {for x, continuous (fun y => y.~ ^+ n)}.
Proof.
apply: (@continuous_comp _ _ _ (@onem R) (fun x => x ^+ n)).
  by apply: (@cvgB _ R^o); [exact: cvg_cst|exact: cvg_id].
exact: exprn_continuous.
Qed.

Lemma onemXn_derivable n x : derivable (fun y => y.~ ^+ n) x 1.
Proof.
have := @derivableX _ _ (@onem R) n x 1.
by rewrite fctE; apply; exact: derivableB.
Qed.

Lemma derivable_oo_LRcontinuous_onemXnMr n x :
  derivable_oo_LRcontinuous (fun y => y.~ ^+ n * x) 0 1.
Proof.
split.
- by move=> y y01; apply: derivableM => //=; exact: onemXn_derivable.
- apply: cvgM; last exact: cvg_cst.
  apply: cvg_at_right_filter.
  apply: (@cvg_comp _ _ _ onem (fun x => x ^+ n)).
    by apply: cvgB; [exact: cvg_cst|exact: cvg_id].
  exact: exprn_continuous.
- apply: cvg_at_left_filter.
  apply: cvgM; last exact: cvg_cst.
  apply: (@cvg_comp _ _ _ onem (fun x => x ^+ n)).
    by apply: cvgB; [exact: cvg_cst|exact: cvg_id].
  exact: exprn_continuous.
Qed.

Lemma derive_onemXn n x :
  (fun y => y.~ ^+ n)^`()%classic x = - n%:R * x.~ ^+ n.-1.
Proof.
rewrite (@derive1_comp _ (@onem _) (fun x => x ^+ n))//; last first.
  exact: exprn_derivable.
rewrite derive1E exp_derive// derive1E deriveB// -derive1E.
by rewrite derive1_cst derive_id sub0r mulrN1 [in RHS]mulNr scaler1.
Qed.

Lemma Rintegral_onemXn n :
  \int[lebesgue_measure]_(x in `[0, 1]) (x.~ ^+ n) = n.+1%:R^-1 :> R.
Proof.
rewrite /Rintegral.
rewrite (@continuous_FTC2 _ _ (fun x => x.~ ^+ n.+1 / - n.+1%:R))//=.
- rewrite onem1 expr0n/= mul0r onem0 expr1n mul1r sub0r.
  by rewrite -invrN -2!mulNrn opprK.
- by apply: continuous_in_subspaceT => x x01; exact: continuous_onemXn.
- exact: derivable_oo_LRcontinuous_onemXnMr.
- move=> x x01; rewrite derive1Mr//; last exact: onemXn_derivable.
  by rewrite derive_onemXn mulrAC divff// mul1r.
Qed.

End about_onemXn.
#[deprecated(since="mathcomp-analysis 1.15.0", note="renamed to `derivable_oo_LRcontinuous_onemXnMr`")]
Notation derivable_oo_continuous_bnd_onemXnMr := derivable_oo_LRcontinuous_onemXnMr (only parsing).

(**md about the function $x \mapsto x^a  (1 - x)^b$ *)
Section XMonemX.
Context {R : numDomainType}.
Implicit Types (x : R) (a b : nat).

Definition XMonemX a b := fun x => x ^+ a * x.~ ^+ b.

Lemma XMonemX_ge0 a b x : x \in `[0, 1] -> 0 <= XMonemX a b x.
Proof.
by rewrite in_itv=> /andP[? ?]; rewrite mulr_ge0 ?exprn_ge0 ?subr_ge0.
Qed.

Lemma XMonemX_le1 a b x : x \in `[0, 1] -> XMonemX a b x <= 1.
Proof.
rewrite in_itv/= => /andP[t0 t1].
by rewrite mulr_ile1// ?(exprn_ge0,onem_ge0,exprn_ile1,onem_le1).
Qed.

Lemma XMonemX0n n x : XMonemX 0 n x = x.~ ^+ n.
Proof. by rewrite /XMonemX/= expr0 mul1r. Qed.

Lemma XMonemXn0 n x : XMonemX n 0 x = x ^+ n.
Proof. by rewrite /XMonemX/= expr0 mulr1. Qed.

Lemma XMonemX00 x : XMonemX 0 0 x = 1.
Proof. by rewrite XMonemX0n expr0. Qed.

Lemma XMonemXC a b x : XMonemX a b (1 - x) = XMonemX b a x.
Proof. by rewrite /XMonemX [in LHS]/onem opprB subrKC mulrC. Qed.

Lemma XMonemXM a b a' b' x :
  XMonemX a' b' x * XMonemX a b x = XMonemX (a + a') (b + b') x.
Proof. by rewrite mulrCA -mulrA -exprD mulrA -exprD (addnC b'). Qed.

End XMonemX.

Section XMonemX_realType.
Context {R : realType}.
Local Notation XMonemX := (@XMonemX R).

Lemma continuous_XMonemX a b : continuous (XMonemX a b).
Proof.
by move=> x; apply: cvgM; [exact: exprn_continuous|exact: continuous_onemXn].
Qed.

Lemma within_continuous_XMonemX A a b : {within A, continuous (XMonemX a b)}.
Proof. by apply: continuous_in_subspaceT => x _; exact: continuous_XMonemX. Qed.

Lemma measurable_XMonemX A a b : measurable_fun A (XMonemX a b).
Proof.
apply/measurable_funM => //; apply/measurable_funX => //.
exact: measurable_funB.
Qed.

Lemma bounded_XMonemX a b : [bounded XMonemX a b x | x in `[0, 1]%classic].
Proof.
exists 1; split; [by rewrite num_real|move=> x x1 /= y y01].
rewrite ger0_norm//; last by rewrite XMonemX_ge0.
move: y01; rewrite in_itv/= => /andP[? ?].
rewrite (le_trans _ (ltW x1))// mulr_ile1 ?exprn_ge0//.
- by rewrite subr_ge0.
- by rewrite exprn_ile1.
- by rewrite exprn_ile1 ?subr_ge0// -subr_ge0 opprB subrKC.
Qed.

Local Notation mu := lebesgue_measure.

Lemma integrable_XMonemX a b : mu.-integrable `[0, 1] (EFin \o XMonemX a b).
Proof.
apply: continuous_compact_integrable => //; first exact: segment_compact.
by apply: continuous_in_subspaceT => x _; exact: continuous_XMonemX.
Qed.

Lemma integrable_XMonemX_restrict a b :
  mu.-integrable [set: R] (EFin \o XMonemX a.-1 b.-1 \_`[0,1]).
Proof.
rewrite -restrict_EFin; apply/integrable_restrict => //=.
by rewrite setTI; exact: integrable_XMonemX.
Qed.

Local Open Scope ereal_scope.

Lemma integral_XMonemX_restrict U a b :
  \int[mu]_(x in U) (XMonemX a b \_ `[0, 1] x)%:E =
  \int[mu]_(x in U `&` `[0%R, 1%R]) (XMonemX a b x)%:E.
Proof.
rewrite [RHS]integral_mkcondr /=; apply: eq_integral => x xU /=.
by rewrite restrict_EFin.
Qed.

End XMonemX_realType.

Section beta_fun.
Context {R : realType}.
Notation mu := (@lebesgue_measure _).
Local Open Scope ring_scope.
Local Notation XMonemX := (@XMonemX R).

Definition beta_fun a b : R := \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1]) x.

Local Open Scope ereal_scope.

Lemma EFin_beta_fun a b :
  (beta_fun a b)%:E = \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1] x)%:E.
Proof.
rewrite fineK//; apply: integrable_fin_num => //=.
under eq_fun.
  move=> x.
  rewrite /= -/((EFin \o ((XMonemX a.-1 b.-1) \_ _)) x) -restrict_EFin.
  over.
by apply/integrable_restrict => //=; rewrite setTI; exact: integrable_XMonemX.
Qed.

Local Close Scope ereal_scope.

Lemma beta_fun_sym a b : beta_fun a b = beta_fun b a.
Proof.
rewrite -[LHS]Rintegral_mkcond Rintegration_by_substitution_onem//=.
- rewrite onem1 -[RHS]Rintegral_mkcond; apply: eq_Rintegral => x x01.
  by rewrite XMonemXC.
- by rewrite ler01 lexx.
- exact: within_continuous_XMonemX.
Qed.

Lemma beta_fun0n b : (0 < b)%N -> beta_fun 0 b = b%:R^-1.
Proof.
move=> b0; rewrite -[LHS]Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX0n.
by rewrite Rintegral_onemXn// prednK.
Qed.

Lemma beta_fun00 : beta_fun 0 0 = 1%R.
Proof.
rewrite -[LHS]Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX00.
rewrite Rintegral_cst//= mul1r lebesgue_measure_itv/= lte_fin ltr01.
by rewrite oppr0 adde0.
Qed.

Lemma beta_fun1Sn b : beta_fun 1 b.+1 = b.+1%:R^-1.
Proof.
rewrite /beta_fun -Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX0n.
by rewrite Rintegral_onemXn.
Qed.

Lemma beta_fun11 : beta_fun 1 1 = 1.
Proof. by rewrite (beta_fun1Sn O) invr1. Qed.

Lemma beta_funSSnSm a b :
  beta_fun a.+2 b.+1 = a.+1%:R / b.+1%:R * beta_fun a.+1 b.+2.
Proof.
rewrite -[LHS]Rintegral_mkcond.
rewrite (@Rintegration_by_parts _ _ (fun x => x.~ ^+ b.+1 / - b.+1%:R)
    (fun x => a.+1%:R * x ^+ a)); last 7 first.
  exact: ltr01.
  apply/continuous_subspaceT => x.
  by apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
  split.
    by move=> x x01; exact: exprn_derivable.
    by apply: cvg_at_right_filter; exact: exprn_continuous.
    by apply: cvg_at_left_filter; exact: exprn_continuous.
  by move=> x x01; rewrite derive1E exp_derive scaler1.
  by apply/continuous_subspaceT => x x01; exact: continuous_onemXn.
  exact: derivable_oo_LRcontinuous_onemXnMr.
  move=> x x01; rewrite derive1Mr; last exact: onemXn_derivable.
  by rewrite derive_onemXn mulrAC divff// mul1r.
rewrite {1}/onem !(expr1n,mul1r,expr0n,subr0,subrr,mul0r,oppr0,sub0r)/=.
transitivity (a.+1%:R / b.+1%:R * \int[mu]_(x in `[0, 1]) XMonemX a b.+1 x).
  under [in LHS]eq_Rintegral.
    move=> x x01.
    rewrite mulrA mulrC mulrA (mulrA _ a.+1%:R) -(mulrA (_ * _)%R).
    over.
  rewrite /=.
  rewrite RintegralZl//=; last exact: integrable_XMonemX.
  by rewrite -mulNrn -2!mulNr -invrN -mulNrn opprK (mulrC _ a.+1%:R).
by rewrite Rintegral_mkcond.
Qed.

Lemma beta_funSnSm a b : beta_fun a.+1 b.+1 =
  a`!%:R / (\prod_(b.+1 <= i < (a + b).+1) i)%:R * beta_fun 1 (a + b).+1.
Proof.
elim: a b => [b|a ih b].
  by rewrite fact0 mul1r add0n /index_iota subnn big_nil invr1 mul1r.
rewrite beta_funSSnSm [in LHS]ih !mulrA; congr *%R; last by rewrite addSnnS.
rewrite -mulrA mulrCA 2!mulrA.
rewrite -natrM (mulnC a`!) -factS -mulrA -invfM; congr (_ / _).
rewrite big_add1 [in RHS]big_nat_recl/=; last by rewrite addSn ltnS leq_addl.
by rewrite -natrM addSnnS.
Qed.

Lemma beta_fun_fact a b :
  beta_fun a.+1 b.+1 = (a`! * b`!)%:R / (a + b).+1`!%:R.
Proof.
rewrite beta_funSnSm beta_fun1Sn natrM -!mulrA; congr *%R.
(* (b+1 b+2 ... b+1 b+a)^-1 / (a+b+1) = b! / (a+b+1)! *)
rewrite factS [in RHS]mulnC natrM invfM mulrA; congr (_ / _).
rewrite -(@invrK _ b`!%:R) -invfM; congr (_^-1).
apply: (@mulfI _ b`!%:R).
  by rewrite gt_eqF// ltr0n fact_gt0.
rewrite mulrA divff// ?gt_eqF// ?ltr0n ?fact_gt0 ?mul1r//.
rewrite [in RHS]fact_prod -natrM; congr (_%:R).
rewrite fact_prod -big_cat/= /index_iota subn1 -iotaD.
by rewrite subSS addnK subn1 addnC.
Qed.

Lemma beta_funE a b : beta_fun a b =
  if (a == 0)%N && (0 < b)%N then
    b%:R^-1
  else if (b == 0)%N && (0 < a)%N then
    a%:R^-1
  else
    a.-1`!%:R * b.-1`!%:R / (a + b).-1`!%:R.
Proof.
case: a => [|a].
  rewrite eqxx/=; case: ifPn => [|].
    by case: b => [|b _] //; rewrite beta_fun0n.
  rewrite -leqNgt leqn0 => /eqP ->.
  by rewrite beta_fun00 eqxx ltnn/= fact0 mul1r divr1.
case: b => [|b].
  by rewrite beta_fun_sym beta_fun0n// fact0 addn0/= mulr1 divff.
by rewrite beta_fun_fact natrM// addnS.
Qed.

Lemma beta_fun_gt0 a b : 0 < beta_fun a b.
Proof.
rewrite beta_funE.
case: ifPn => [/andP[_ b0]|]; first by rewrite invr_gt0 ltr0n.
rewrite negb_and => /orP[a0|].
  case: ifPn => [/andP[_]|]; first by rewrite invr_gt0// ltr0n.
  rewrite negb_and => /orP[b0|].
    by rewrite divr_gt0// ?mulr_gt0 ?ltr0n ?fact_gt0.
  by rewrite -leqNgt leqn0 (negbTE a0).
rewrite -leqNgt leqn0 => /eqP ->; rewrite eqxx/=.
case: ifPn; first by rewrite invr_gt0 ltr0n.
by rewrite -leqNgt leqn0 => /eqP ->; rewrite fact0 mul1r divr1.
Qed.

Lemma beta_fun_ge0 a b : 0 <= beta_fun a b.
Proof. exact/ltW/beta_fun_gt0. Qed.

End beta_fun.

Section beta_pdf.
Local Open Scope ring_scope.
Context {R : realType}.
Variables a b : nat.

Local Notation XMonemX := (@XMonemX R).

Definition beta_pdf t : R := XMonemX a.-1 b.-1 \_`[0,1] t / beta_fun a b.

Lemma measurable_beta_pdf : measurable_fun [set: R] beta_pdf.
Proof.
apply: measurable_funM => //; apply/measurable_restrict => //.
by rewrite setTI; exact: measurable_XMonemX.
Qed.

Lemma beta_pdf_ge0 t : 0 <= beta_pdf t.
Proof.
rewrite /beta_pdf divr_ge0 ?beta_fun_ge0//.
rewrite patchE; case: ifPn => //=.
by rewrite inE/= => ?; exact: XMonemX_ge0.
Qed.

Lemma beta_pdf_le_beta_funV x : beta_pdf x <= (beta_fun a b)^-1.
Proof.
rewrite /beta_pdf ler_pdivrMr ?beta_fun_gt0// mulVf ?gt_eqF ?beta_fun_gt0//.
by rewrite patchE; case: ifPn => //; rewrite inE/= => ?; exact: XMonemX_le1.
Qed.

Local Notation mu := lebesgue_measure.

Local Open Scope ereal_scope.

Let int_beta_pdf01 : \int[mu]_(x in `[0%R, 1%R]) (beta_pdf x)%:E =
                     \int[mu]_x (beta_pdf x)%:E :> \bar R.
Proof.
rewrite integral_mkcond/=; apply: eq_integral => /=x _.
by rewrite /beta_pdf/= !patchE; case: ifPn => [->//|_]; rewrite mul0r.
Qed.

Local Close Scope ereal_scope.

Lemma integrable_beta_pdf : mu.-integrable [set: _] (EFin \o beta_pdf).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_beta_pdf.
under eq_integral=> /= x _ do rewrite ger0_norm ?beta_pdf_ge0//.
rewrite /= -int_beta_pdf01.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R]) (beta_fun a b)^-1%:E)%E).
  apply: ge0_le_integral => //=.
  - by move=> x _; rewrite lee_fin beta_pdf_ge0.
  - apply/measurable_funTS/measurable_EFinP => /=.
    exact: measurable_beta_pdf.
  - by move=> x _; rewrite lee_fin beta_pdf_le_beta_funV.
rewrite integral_cst//= lebesgue_measure_itv//=.
by rewrite lte01 oppr0 adde0 mule1 ltry.
Qed.

Lemma bounded_beta_pdf_01 : [bounded beta_pdf x | x in `[0%R, 1%R]%classic].
Proof.
exists (beta_fun a b)^-1; split; first by rewrite num_real.
move=> // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M => M /=; rewrite in_itv/= => /andP[M0 M1].
rewrite ler_norml; apply/andP; split.
  rewrite lerNl (@le_trans _ _ 0%R)// ?invr_ge0 ?beta_fun_ge0//.
  by rewrite lerNl oppr0 beta_pdf_ge0.
rewrite /beta_pdf ler_pdivrMr ?beta_fun_gt0//.
rewrite mulVf ?gt_eqF ?beta_fun_gt0//.
by rewrite patchE; case: ifPn => //; rewrite inE => ?; exact: XMonemX_le1.
Unshelve. all: by end_near. Qed.

End beta_pdf.

Section beta.
Local Open Scope ring_scope.
Context {R : realType}.
Variables a b : nat.

Local Notation mu := (@lebesgue_measure R).
Local Notation XMonemX := (@XMonemX R).

Let beta_num (U : set (measurableTypeR R)) : \bar R :=
  \int[mu]_(x in U) (XMonemX a.-1 b.-1 \_`[0,1] x)%:E.

Let beta_numT : beta_num [set: (measurableTypeR R)] = (beta_fun a b)%:E.
Proof. by rewrite /beta_num/= EFin_beta_fun. Qed.

Let beta_num_lty U : measurable U -> (beta_num U < +oo)%E.
Proof.
move=> mU.
apply: (@le_lt_trans _ _ (\int[mu]_(x in U `&` `[0%R, 1%R]) 1)%E); last first.
  rewrite integral_cst//= ?mul1e//.
    rewrite (le_lt_trans (measureIr _ _ _))//= lebesgue_measure_itv//= lte01//.
    by rewrite EFinN sube0 ltry.
  exact: measurableI.
rewrite /beta_num integral_XMonemX_restrict ge0_le_integral//=.
- exact: measurableI.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_XMonemX.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_le1.
Qed.

Let beta_num0 : beta_num set0 = 0%:E.
Proof. by rewrite /beta_num integral_set0. Qed.

Let beta_num_ge0 U : (0 <= beta_num U)%E.
Proof.
rewrite /beta_num integral_ge0//= => x Ux; rewrite lee_fin.
by rewrite patchE; case: ifPn => //; rewrite inE/= => x01; exact: XMonemX_ge0.
Qed.

Let beta_num_sigma_additive : semi_sigma_additive beta_num.
Proof.
move=> /= F mF tF mUF; rewrite /beta_num; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _; apply: integral_ge0 => /= x Fkx.
  rewrite patchE; case: ifPn => //; rewrite inE/= => x01.
  by rewrite lee_fin XMonemX_ge0.
rewrite ge0_integral_bigcup//=.
- apply/measurable_funTS/measurableT_comp => //=.
  by apply/measurable_restrict => //=; rewrite setTI; exact: measurable_XMonemX.
- move=> x [? _ ?]; rewrite lee_fin.
  by rewrite patchE; case: ifPn => //; rewrite inE/= => x0; exact: XMonemX_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ beta_num
  beta_num0 beta_num_ge0 beta_num_sigma_additive.

Definition beta_prob :=
  mscale ((NngNum (beta_fun_ge0 a b))%:num^-1)%:nng beta_num.

HB.instance Definition _ := Measure.on beta_prob.

Let beta_prob_setT : beta_prob setT = 1%:E.
Proof.
rewrite /beta_prob /= /mscale /= beta_numT.
by rewrite -EFinM mulVf// gt_eqF// beta_fun_gt0.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ _ beta_prob beta_prob_setT.

Lemma integral_beta_pdf U : measurable U ->
  (\int[mu]_(x in U) (beta_pdf a b x)%:E = beta_prob U :> \bar R)%E.
Proof.
move=> mU.
rewrite /beta_pdf.
under eq_integral do rewrite EFinM/=.
rewrite ge0_integralZr//=.
- by rewrite /beta_prob/= /mscale/= muleC.
- apply/measurable_funTS/measurableT_comp => //.
  by apply/measurable_restrict => //=; rewrite setTI; exact: measurable_XMonemX.
- move=> x Ux; rewrite patchE; case: ifPn => //; rewrite inE/= => x01.
  by rewrite lee_fin XMonemX_ge0.
- by rewrite lee_fin invr_ge0// beta_fun_ge0.
Qed.

Lemma beta_prob01 : beta_prob `[0, 1] = 1%:E.
Proof.
rewrite -beta_prob_setT/= /beta_prob/= /mscale/= /beta_num/=.
rewrite [in RHS]integral_XMonemX_restrict/= setTI.
by rewrite [in LHS]integral_XMonemX_restrict/= setIid.
Qed.

Lemma beta_prob_fin_num U : measurable U -> beta_prob U \is a fin_num.
Proof.
move=> mU; rewrite ge0_fin_numE//.
rewrite (@le_lt_trans _ _ (beta_prob setT))//=.
  by rewrite le_measure// inE.
by rewrite probability_setT ltry.
Qed.

Lemma beta_prob_dom : beta_prob `<< mu.
Proof.
apply/null_content_dominatesP => A mA muA0; rewrite /beta_prob /mscale/=.
apply/eqP; rewrite mule_eq0 eqe invr_eq0 gt_eqF/= ?beta_fun_gt0//; apply/eqP.
rewrite /beta_num integral_XMonemX_restrict.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: integral_ge0 => x [_ ?]; rewrite lee_fin XMonemX_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A `&` `[0%R, 1%R]) 1)%E); last first.
  rewrite integral_cst ?mul1e//=; last exact: measurableI.
  by rewrite -[leRHS]muA0 measureIl.
apply: ge0_le_integral => //=; first exact: measurableI.
- by move=> x [_ x01]; rewrite lee_fin XMonemX_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_XMonemX.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_le1.
Qed.

End beta.
Arguments beta_prob {R}.

Lemma beta_prob_uniform {R : realType} :
  beta_prob 1 1 = uniform_prob (@ltr01 R).
Proof.
apply/funext => U.
rewrite /beta_prob /uniform_prob.
rewrite /mscale/= beta_fun11 invr1 !mul1e.
rewrite integral_XMonemX_restrict integral_uniform_pdf.
apply: eq_integral => /= x.
rewrite inE => -[Ux/=]; rewrite in_itv/= => x10.
rewrite /XMonemX !expr0 mul1r.
by rewrite /uniform_pdf x10 subr0 invr1.
Qed.

Local Open Scope ereal_scope.

Lemma integral_beta_prob_bernoulli_prob_lty {R : realType} a b (f : R -> R) U :
  measurable_fun setT f ->
  (forall x, x \in `[0, 1]%R -> 0 <= f x <= 1)%R ->
  \int[beta_prob a b]_x `|bernoulli_prob (f x) U| < +oo.
Proof.
move=> mf /= f01.
apply: (@le_lt_trans _ _ (\int[beta_prob a b]_x cst 1 x)).
  apply: ge0_le_integral => //=.
    apply: measurableT_comp => //=.
    by apply: (measurableT_comp (measurable_bernoulli_prob2 _)).
  by move=> x _; rewrite gee0_abs// probability_le1.
by rewrite integral_cst//= mul1e -ge0_fin_numE// beta_prob_fin_num.
Qed.

Local Close Scope ereal_scope.

Lemma integral_beta_prob_bernoulli_prob_onemX_lty {R : realType} n a b U :
  (\int[beta_prob a b]_x `|bernoulli_prob (x.~ ^+ n) U| < +oo :> \bar R)%E.
Proof.
apply: integral_beta_prob_bernoulli_prob_lty => //=.
  by apply: measurable_funX => //; exact: measurable_funB.
move=> x; rewrite in_itv/= => /andP[x0 x1].
rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
by rewrite lerBlDl -lerBlDr subrr.
Qed.

Lemma integral_beta_prob_bernoulli_prob_onem_lty {R : realType} n a b U :
  (\int[beta_prob a b]_x `|bernoulli_prob (1 - x.~ ^+ n) U| < +oo :> \bar R)%E.
Proof.
apply: integral_beta_prob_bernoulli_prob_lty => //=.
  apply: measurable_funB => //.
  by apply: measurable_funX => //; exact: measurable_funB.
move=> x; rewrite in_itv/= => /andP[x0 x1].
rewrite -[_ <= 1]subr_ge0 opprB subrKC subr_ge0 andbC.
rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
by rewrite lerBlDl -lerBlDr subrr.
Qed.

Lemma beta_prob_integrable {R :realType} a b a' b' :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x)%:E).
Proof.
apply/integrableP; split.
  by apply/measurableT_comp => //; exact: measurable_XMonemX.
apply: (@le_lt_trans _ _ (\int[beta_prob a b]_(x in `[0%R, 1%R]) 1)%E).
  apply: ge0_le_integral => //=.
    by do 2 apply/measurableT_comp => //; exact: measurable_XMonemX.
  move=> x; rewrite in_itv/= => /andP[x0 x1].
  rewrite lee_fin ger0_norm; last first.
    by rewrite !mulr_ge0// exprn_ge0// onem_ge0.
  rewrite mulr_ile1// ?exprn_ge0 ?onem_ge0// exprn_ile1// ?onem_ge0//.
  exact: onem_le1.
rewrite integral_cst//= mul1e.
by rewrite -ge0_fin_numE// beta_prob_fin_num.
Qed.

Lemma beta_prob_integrable_onem {R : realType} a b a' b' :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x).~%:E).
Proof.
apply: (eq_integrable _ (cst 1 \- (fun x : measurableTypeR R =>
  (XMonemX a' b' x)%:E))%E) => //.
apply: integrableB => //=.
  apply/integrableP; split => //.
  rewrite (eq_integral (fun x => (\1_setT x)%:E))/=; last first.
    by move=> x _; rewrite /= indicT normr1.
  rewrite integral_indic//= setTI /beta_prob /mscale/= lte_mul_pinfty//.
    by rewrite lee_fin invr_ge0 beta_fun_ge0.
  rewrite (_ : integral _ _ _ = \int[lebesgue_measure]_x
    (((@XMonemX R a.-1 b.-1) \_ `[0, 1]) x)%:E)%E; last first.
    rewrite [LHS]integral_mkcond/=; apply: eq_integral => /= x _.
    by rewrite !patchE; case: ifPn => // ->.
  have /integrableP[_] := @integrable_XMonemX_restrict R a b.
  under eq_integral.
    move=> x _.
    rewrite gee0_abs//; last first.
      rewrite lee_fin patchE; case: ifPn => //; rewrite inE/= => x01.
      by rewrite XMonemX_ge0.
    over.
  by [].
exact: beta_prob_integrable.
Qed.

Lemma beta_prob_integrable_dirac {R : realType} a b a' b' (c : bool) U :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x)%:E * \d_c U)%E.
Proof.
apply: integrableMl => //=; last first.
  exists 1; split => // x x1/= _ _; rewrite (le_trans _ (ltW x1))//.
  by rewrite ger0_norm// indicE; case: (_ \in _).
exact: beta_prob_integrable.
Qed.

Lemma beta_prob_integrable_onem_dirac {R : realType} a b a' b' (c : bool) U :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x).~%:E * \d_c U)%E.
Proof.
apply: integrableMl => //=; last first.
  exists 1; split => // x x1/= _ _; rewrite (le_trans _ (ltW x1))//.
  by rewrite ger0_norm// indicE; case: (_ \in _).
exact: beta_prob_integrable_onem.
Qed.

Section integral_beta_prob.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

Lemma integral_beta_prob a b f U : measurable U -> measurable_fun U f ->
  (\int[beta_prob a b]_(x in U) `|f x| < +oo)%E ->
  (\int[beta_prob a b]_(x in U) f x =
   \int[mu]_(x in U) (f x * (beta_pdf a b x)%:E))%E.
Proof.
move=> mU mf finf.
rewrite -(Radon_Nikodym_change_of_variables (beta_prob_dom a b))//=; last first.
  by apply/integrableP; split.
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //; apply: (measurable_int mu).
  apply: (integrableS _ _ (@subsetT _ _)) => //=.
  by apply: Radon_Nikodym_integrable; exact: beta_prob_dom.
- apply: emeasurable_funM => //=; apply/measurableT_comp => //=.
  by apply/measurable_funTS; exact: measurable_beta_pdf.
- apply: ae_eqe_mul2l => /=.
  rewrite Radon_NikodymE//=; first exact: beta_prob_dom.
  move=> ?.
  case: cid => /= h [h1 h2 h3].
(* uniqueness of Radon-Nikodym derivative up to equal on non null sets of mu *)
  apply: integral_ae_eq => //=.
  + apply: integrableS h2 => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_beta_pdf.
  + by move=> E E01 mE; rewrite -h3//= integral_beta_pdf.
Qed.

End integral_beta_prob.

Section beta_prob_bernoulliE.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Open Scope ring_scope.

Definition div_beta_fun a b c d : R := beta_fun (a + c) (b + d) / beta_fun a b.

Lemma div_beta_fun_ge0 a b c d : 0 <= div_beta_fun a b c d.
Proof. by rewrite /div_beta_fun divr_ge0// beta_fun_ge0. Qed.

Lemma div_beta_fun_le1 a b c d : (0 < a)%N -> (0 < b)%N ->
  div_beta_fun a b c d <= 1.
Proof.
move=> a0 b0.
rewrite /div_beta_fun ler_pdivrMr// ?mul1r ?beta_fun_gt0//.
rewrite !beta_funE.
rewrite addn_eq0 (gtn_eqF a0)/=.
rewrite addn_eq0 (gtn_eqF b0)/=.
rewrite ler_pdivrMr ?ltr0n ?fact_gt0//.
rewrite mulrAC.
rewrite ler_pdivlMr ?ltr0n ?fact_gt0//.
rewrite -!natrM ler_nat.
move: a a0 => [//|a _].
rewrite addSn.
move: b b0 => [//|b _].
rewrite [(a + c).+1.-1]/=.
rewrite [a.+1.-1]/=.
rewrite [b.+1.-1]/=.
rewrite addnS.
rewrite [(_ + b).+1.-1]/=.
rewrite (addSn b d).
rewrite [(b + _).+1.-1]/=.
rewrite (addSn (a + c)).
rewrite [_.+1.-1]/=.
rewrite addSn addnS.
by rewrite leq_fact2// leq_addr.
Qed.

Definition beta_prob_bernoulli_prob a b c d U : \bar R :=
  \int[beta_prob a b]_(y in `[0, 1])
    bernoulli_prob ((@XMonemX R c d \_`[0, 1])%R y) U.

Lemma beta_prob_bernoulli_probE a b c d U : (a > 0)%N -> (b > 0)%N ->
  beta_prob_bernoulli_prob a b c d U = bernoulli_prob (div_beta_fun a b c d) U.
Proof.
move=> a0 b0.
rewrite /beta_prob_bernoulli_prob.
under eq_integral => x.
  rewrite inE/= in_itv/= => x01.
  rewrite bernoulli_probE/=; last first.
  rewrite patchE; case: ifPn => x01'.
    by rewrite XMonemX_ge0//= XMonemX_le1.
  by rewrite lexx ler01.
  over.
rewrite /= [in RHS]bernoulli_probE/= ?div_beta_fun_ge0 ?div_beta_fun_le1//=.
under eq_integral => x x01.
  rewrite patchE x01/=.
  over.
rewrite /= integralD//=; last 2 first.
  exact: beta_prob_integrable_dirac.
  exact: beta_prob_integrable_onem_dirac.
congr (_ + _).
  rewrite integralZr//=; last exact: beta_prob_integrable.
  congr (_ * _)%E.
  rewrite integral_beta_prob//; last 2 first.
    by apply/measurableT_comp => //; exact: measurable_XMonemX.
    by have /integrableP[_] := @beta_prob_integrable R a b c d.
  transitivity ((\int[mu]_(x in `[0%R, 1%R])
      ((x.~ ^+ d)%:E * ((beta_pdf a b x)%:E * (x ^+ c)%:E)))%E : \bar R).
    apply: eq_integral => /= x _.
    by rewrite [in LHS]EFinM -[LHS]muleA [LHS]muleC -[LHS]muleA.
  transitivity ((beta_fun a b)^-1%:E * \int[mu]_(x in `[0%R, 1%R])
      (@XMonemX R (a + c).-1 (b + d).-1 \_`[0,1] x)%:E)%E.
    rewrite -integralZl//=; last first.
      by apply: (integrableS measurableT) => //=; exact: integrable_XMonemX_restrict.
    apply: eq_integral => x x01.
    rewrite muleA muleC muleA -(EFinM (x ^+ c)) -/(XMonemX c d x) -EFinM mulrA.
    rewrite !patchE x01 XMonemXM// -EFinM mulrC.
    by move: a a0 b b0 => [//|a] _ [|b].
  rewrite /div_beta_fun mulrC EFinM; congr (_ * _)%E.
  rewrite /beta_fun integral_mkcond/= fineK; last first.
    by apply: integrable_fin_num => //; exact: integrable_XMonemX_restrict.
  by apply: eq_integral => /= x _; rewrite !patchE; case: ifPn => // ->.
under eq_integral do rewrite muleC.
rewrite /= integralZl//=; last exact: beta_prob_integrable_onem.
rewrite muleC; congr (_ * _)%E.
rewrite integral_beta_prob//=; last 2 first.
  apply/measurableT_comp => //=.
  by apply/measurable_funB => //; exact: measurable_XMonemX.
  by have /integrableP[] := @beta_prob_integrable_onem R a b c d.
rewrite /beta_pdf.
under eq_integral do rewrite EFinM muleA.
rewrite integralZr//=; last first.
  apply: integrableMr => //=.
  - by apply/measurable_funB => //=; exact: measurable_XMonemX.
  - apply/ex_bound => //.
    + apply: (@globally_properfilter _ _ 0%R) => //=.
      by apply: inferP; rewrite in_itv/= lexx ler01.
    + exists 1 => t.
      rewrite /= in_itv/= => t01.
      apply: normr_onem; apply/andP; split.
        by rewrite mulr_ge0// exprn_ge0// ?onem_ge0//; case/andP: t01.
      by rewrite mulr_ile1// ?exprn_ge0 ?exprn_ile1// ?onem_ge0 ?onem_le1//;
        case/andP: t01.
  - exact: integrableS (integrable_XMonemX_restrict _ _).
transitivity ((\int[mu]_x ((@XMonemX R a.-1 b.-1 \_`[0,1] x)%:E -
   (@XMonemX R (a + c).-1 (b + d).-1 \_`[0,1] x)%:E)) * (beta_fun a b)^-1%:E)%E.
  congr (_ * _)%E; rewrite [LHS]integral_mkcond/=; apply eq_integral => x _.
  rewrite !patchE; case: ifPn => [->|]; last by rewrite EFinN subee.
  rewrite /onem -EFinM mulrBl mul1r EFinB EFinN; congr (_ - _)%E.
  rewrite XMonemXM.
  by move: a a0 b b0 => [|a]// _ [|b].
rewrite integralB_EFin//=; last 2 first.
  exact: integrableS (integrable_XMonemX_restrict _ _).
  exact: integrableS (integrable_XMonemX_restrict _ _).
rewrite EFinB muleBl//; last by rewrite -!EFin_beta_fun.
by rewrite -!EFin_beta_fun -EFinM divff// gt_eqF// beta_fun_gt0.
Qed.

End beta_prob_bernoulliE.
