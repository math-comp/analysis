(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals interval_inference ereal topology normedtype.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
From mathcomp Require Import ftc gauss_integral.

(**md**************************************************************************)
(* # Probability                                                              *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(* ```                                                                        *)
(*        {RV P >-> T'} == random variable: a measurable function to the      *)
(*                         measurableType T' from the measured space          *)
(*                         characterized by the probability P                 *)
(*     distribution P X == measure image of the probability measure P by the  *)
(*                         random variable X : {RV P -> T'}                   *)
(*                         P as type probability T R with T of type           *)
(*                         measurableType.                                    *)
(*                         Declared as an instance of probability measure.    *)
(*              'E_P[X] == expectation of the real measurable function X      *)
(*       covariance X Y == covariance between real random variable X and Y    *)
(*              'V_P[X] == variance of the real random variable X             *)
(*                'M_ X == moment generating function of the random variable  *)
(*                         X                                                  *)
(*      {dmfun T >-> R} == type of discrete real-valued measurable functions  *)
(*        {dRV P >-> R} == real-valued discrete random variable               *)
(*            dRV_dom X == domain of the discrete random variable X           *)
(*           dRV_enum X == bijection between the domain and the range of X    *)
(*              pmf X r := fine (P (X @^-1` [set r]))                         *)
(*              cdf X r == cumulative distribution function of X              *)
(*                      := distribution P X `]-oo, r]                         *)
(*        enum_prob X k == probability of the kth value in the range of X     *)
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
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E_' P [ X ]" (format "''E_' P [ X ]", at level 5).
Reserved Notation "''V_' P [ X ]" (format "''V_' P [ X ]", at level 5).
Reserved Notation "'M_ X t" (format "''M_' X  t",
  at level 5, t, X at next level).
Reserved Notation "{ 'dmfun' aT >-> T }"
  (at level 0, format "{ 'dmfun'  aT  >->  T }").
Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

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
  pushforward P (@measurable_funP _ _ _ _ _ X).

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
  rewrite -(@probability_setT _ _ _ P).
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
  - by rewrite -ge0_fin_numE// fin_num_measure//; exact: measurable_sfunP.
  - by move=> ?; exact: measurable_sfunP.
  - by apply: bigcap_measurable => // ? _; exact: measurable_sfunP.
  - apply/subsetPset; apply: preimage_subset; apply: subset_itvl.
    by rewrite bnd_simp lerD2l lef_pV2 ?posrE// ler_nat.
by rewrite -(cvg_unique _ cdf_ns cdf_na).
Unshelve. all: by end_near. Qed.

End cumulative_distribution_function.

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

Lemma expectation_fin_num (X : {RV P >-> R}) : P.-integrable setT (EFin \o X) ->
  'E_P[X] \is a fin_num.
Proof. by move=> ?; rewrite unlock integral_fune_fin_num. Qed.

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

Lemma expectationZl (X : {RV P >-> R}) (iX : P.-integrable [set: T] (EFin \o X))
  (k : R) : 'E_P[k \o* X] = k%:E * 'E_P [X].
Proof. by rewrite unlock muleC -integralZr. Qed.

Lemma expectation_ge0 (X : {RV P >-> R}) :
  (forall x, 0 <= X x)%R -> 0 <= 'E_P[X].
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

Lemma expectationD (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \+ Y] = 'E_P[X] + 'E_P[Y].
Proof. by move=> ? ?; rewrite unlock integralD_EFin. Qed.

Lemma expectationB (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \- Y] = 'E_P[X] - 'E_P[Y].
Proof. by move=> ? ?; rewrite unlock integralB_EFin. Qed.

Lemma expectation_sum (X : seq {RV P >-> R}) :
    (forall Xi, Xi \in X -> P.-integrable [set: T] (EFin \o Xi)) ->
  'E_P[\sum_(Xi <- X) Xi] = \sum_(Xi <- X) 'E_P[Xi].
Proof.
elim: X => [|X0 X IHX] intX; first by rewrite !big_nil expectation_cst.
have intX0 : P.-integrable [set: T] (EFin \o X0).
  by apply: intX; rewrite in_cons eqxx.
have {}intX Xi : Xi \in X -> P.-integrable [set: T] (EFin \o Xi).
  by move=> XiX; apply: intX; rewrite in_cons XiX orbT.
rewrite !big_cons expectationD ?IHX// (_ : _ \o _ = fun x =>
    \sum_(f <- map (fun x : {RV P >-> R} => EFin \o x) X) f x).
  by apply: integrable_sum => // _ /mapP[h hX ->]; exact: intX.
by apply/funext => t/=; rewrite big_map sumEFin mfun_sum.
Qed.

End expectation_lemmas.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `expectationZl`")]
Notation expectationM := expectationZl (only parsing).

HB.lock Definition covariance {d} {T : measurableType d} {R : realType}
    (P : probability T R) (X Y : T -> R) :=
  'E_P[(X \- cst (fine 'E_P[X])) * (Y \- cst (fine 'E_P[Y]))]%E.
Canonical covariance_unlockable := Unlockable covariance.unlock.
Arguments covariance {d T R} P _%_R _%_R.

Section covariance_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma covarianceE (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y = 'E_P[X * Y] - 'E_P[X] * 'E_P[Y].
Proof.
move=> X1 Y1 XY1.
have ? : 'E_P[X] \is a fin_num by rewrite fin_num_abs// integrable_expectation.
have ? : 'E_P[Y] \is a fin_num by rewrite fin_num_abs// integrable_expectation.
rewrite unlock [X in 'E_P[X]](_ : _ = (X \* Y \- fine 'E_P[X] \o* Y
    \- fine 'E_P[Y] \o* X \+ fine ('E_P[X] * 'E_P[Y]) \o* cst 1)%R); last first.
  apply/funeqP => x /=; rewrite mulrDr !mulrDl/= mul1r fineM// mulrNN addrA.
  by rewrite mulrN mulNr [Z in (X x * Y x - Z)%R]mulrC.
have ? : P.-integrable [set: T] (EFin \o (X \* Y \- fine 'E_P[X] \o* Y)%R).
  by rewrite compreBr ?integrableB// compre_scale ?integrableZl.
rewrite expectationD/=; last 2 first.
  - by rewrite compreBr// integrableB// compre_scale ?integrableZl.
  - by rewrite compre_scale// integrableZl// finite_measure_integrable_cst.
rewrite 2?expectationB//= ?compre_scale// ?integrableZl//.
rewrite 3?expectationZl//= ?finite_measure_integrable_cst//.
by rewrite expectation_cst mule1 fineM// EFinM !fineK// muleC subeK ?fin_numM.
Qed.

Lemma covarianceC (X Y : T -> R) : covariance P X Y = covariance P Y X.
Proof.
by rewrite unlock; congr expectation; apply/funeqP => x /=; rewrite mulrC.
Qed.

Lemma covariance_fin_num (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y \is a fin_num.
Proof.
by move=> X1 Y1 XY1; rewrite covarianceE// fin_numB fin_numM expectation_fin_num.
Qed.

Lemma covariance_cst_l c (X : {RV P >-> R}) : covariance P (cst c) X = 0.
Proof.
rewrite unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funeqP => x; rewrite /GRing.mul/= subrr mul0r.
Qed.

Lemma covariance_cst_r (X : {RV P >-> R}) c : covariance P X (cst c) = 0.
Proof. by rewrite covarianceC covariance_cst_l. Qed.

Lemma covarianceZl a (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (a \o* X)%R Y = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have aXY : (a \o* X * Y = a \o* (X * Y))%R.
  by apply/funeqP => x; rewrite mulrAC.
rewrite [LHS]covarianceE => [||//|] /=; last 2 first.
- by rewrite compre_scale ?integrableZl.
- by rewrite aXY compre_scale ?integrableZl.
rewrite covarianceE// aXY !expectationZl//.
by rewrite -muleA -muleBr// fin_num_adde_defr// expectation_fin_num.
Qed.

Lemma covarianceZr a (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X (a \o* Y)%R = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
by rewrite [in RHS]covarianceC covarianceC covarianceZl; last rewrite mulrC.
Qed.

Lemma covarianceNl (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (\- X)%R Y = - covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have -> : (\- X = -1 \o* X)%R by apply/funeqP => x /=; rewrite mulrN mulr1.
by rewrite covarianceZl// EFinN mulNe mul1e.
Qed.

Lemma covarianceNr (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X (\- Y)%R = - covariance P X Y.
Proof. by move=> X1 Y1 XY1; rewrite !(covarianceC X) covarianceNl 1?mulrC. Qed.

Lemma covarianceNN (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (\- X)%R (\- Y)%R = covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have NY : P.-integrable setT (EFin \o (\- Y)%R) by rewrite compreN ?integrableN.
by rewrite covarianceNl ?covarianceNr ?oppeK//= mulrN compreN ?integrableN.
Qed.

Lemma covarianceDl (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
    P.-integrable setT (EFin \o (Y * Z)%R) ->
  covariance P (X \+ Y)%R Z = covariance P X Z + covariance P Y Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XZ1 YZ1.
rewrite [LHS]covarianceE//= ?mulrDl ?compreDr// ?integrableD//.
rewrite 2?expectationD//=.
rewrite muleDl ?fin_num_adde_defr ?expectation_fin_num//.
rewrite oppeD ?fin_num_adde_defr ?fin_numM ?expectation_fin_num//.
by rewrite addeACA 2?covarianceE.
Qed.

Lemma covarianceDr (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
  covariance P X (Y \+ Z)%R = covariance P X Y + covariance P X Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XY1 XZ1.
by rewrite covarianceC covarianceDl ?(covarianceC X) 1?mulrC.
Qed.

Lemma covarianceBl (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
    P.-integrable setT (EFin \o (Y * Z)%R) ->
  covariance P (X \- Y)%R Z = covariance P X Z - covariance P Y Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XZ1 YZ1.
rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R covarianceDl ?covarianceNl//=.
- by rewrite compreN// integrableN.
- by rewrite mulrNN.
- by rewrite mulNr compreN// integrableN.
Qed.

Lemma covarianceBr (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
  covariance P X (Y \- Z)%R = covariance P X Y - covariance P X Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XY1 XZ1.
by rewrite !(covarianceC X) covarianceBl 1?(mulrC _ X).
Qed.

End covariance_lemmas.

Section variance.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : T -> R) := covariance P X X.
Local Notation "''V_' P [ X ]" := (variance X).

Lemma varianceE (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[X] = 'E_P[X ^+ 2] - ('E_P[X]) ^+ 2.
Proof. by move=> X1 X2; rewrite /variance covarianceE. Qed.

Lemma variance_fin_num (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o X ^+ 2)%R ->
  'V_P[X] \is a fin_num.
Proof. by move=> /[dup]; apply: covariance_fin_num. Qed.

Lemma variance_ge0 (X : {RV P >-> R}) : (0 <= 'V_P[X])%E.
Proof.
by rewrite /variance unlock; apply: expectation_ge0 => x; apply: sqr_ge0.
Qed.

Lemma variance_cst r : 'V_P[cst r] = 0%E.
Proof.
rewrite /variance unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funext => x; rewrite /GRing.exp/GRing.mul/= subrr mulr0.
Qed.

Lemma varianceZ a (X : {RV P >-> R}) :
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(a \o* X)%R] = (a ^+ 2)%:E * 'V_P[X].
Proof.
move=> X1 X2; rewrite /variance covarianceZl//=.
- by rewrite covarianceZr// muleA.
- by rewrite compre_scale// integrableZl.
- rewrite [X in EFin \o X](_ : _ = (a \o* X ^+ 2)%R); last first.
    by apply/funeqP => x; rewrite mulrA.
  by rewrite compre_scale// integrableZl.
Qed.

Lemma varianceN (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(\- X)%R] = 'V_P[X].
Proof. by move=> X1 X2; rewrite /variance covarianceNN. Qed.

Lemma varianceD (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  'V_P[X \+ Y]%R = 'V_P[X] + 'V_P[Y] + 2%:E * covariance P X Y.
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -['V_P[_]]/(covariance P (X \+ Y)%R (X \+ Y)%R).
have XY : P.-integrable [set: T] (EFin \o (X \+ Y)%R).
  by rewrite compreDr// integrableD.
rewrite covarianceDl//=; last 3 first.
- rewrite -expr2 sqrrD compreDr ?integrableD// compreDr// integrableD//.
  rewrite -mulr_natr -[(_ * 2)%R]/(2 \o* (X * Y))%R compre_scale//.
  exact: integrableZl.
- by rewrite mulrDr compreDr ?integrableD.
- by rewrite mulrDr mulrC compreDr ?integrableD.
rewrite covarianceDr// covarianceDr; [|by []..|by rewrite mulrC |exact: Y2].
rewrite (covarianceC P Y X) [LHS]addeA [LHS](ACl (1*4*(2*3)))/=.
by rewrite -[2%R]/(1 + 1)%R EFinD muleDl ?mul1e// covariance_fin_num.
Qed.

Lemma varianceB (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  'V_P[(X \- Y)%R] = 'V_P[X] + 'V_P[Y] - 2%:E * covariance P X Y.
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R.
rewrite varianceD/= ?varianceN ?covarianceNr ?muleN//.
- by rewrite compreN ?integrableN.
- by rewrite mulrNN.
- by rewrite mulrN compreN ?integrableN.
Qed.

Lemma varianceD_cst_l c (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(cst c \+ X)%R] = 'V_P[X].
Proof.
move=> X1 X2.
rewrite varianceD//=; last 3 first.
- exact: finite_measure_integrable_cst.
- by rewrite compre_scale// integrableZl// finite_measure_integrable_cst.
- by rewrite mulrC compre_scale ?integrableZl.
by rewrite variance_cst add0e covariance_cst_l mule0 adde0.
Qed.

Lemma varianceD_cst_r (X : {RV P >-> R}) c :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(X \+ cst c)%R] = 'V_P[X].
Proof.
move=> X1 X2.
have -> : (X \+ cst c = cst c \+ X)%R by apply/funeqP => x /=; rewrite addrC.
exact: varianceD_cst_l.
Qed.

Lemma varianceB_cst_l c (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(cst c \- X)%R] = 'V_P[X].
Proof.
move=> X1 X2.
rewrite -[(cst c \- X)%R]/(cst c \+ (\- X))%R varianceD_cst_l/=; last 2 first.
- by rewrite compreN ?integrableN.
- by rewrite mulrNN; apply: X2.
by rewrite varianceN.
Qed.

Lemma varianceB_cst_r (X : {RV P >-> R}) c :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(X \- cst c)%R] = 'V_P[X].
Proof.
by move=> X1 X2; rewrite -[(X \- cst c)%R]/(X \+ (cst (- c)))%R varianceD_cst_r.
Qed.

Lemma covariance_le (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y <= sqrte 'V_P[X] * sqrte 'V_P[Y].
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -sqrteM ?variance_ge0//.
rewrite lee_sqrE ?sqrte_ge0// sqr_sqrte ?mule_ge0 ?variance_ge0//.
rewrite -(fineK (variance_fin_num X1 X2)) -(fineK (variance_fin_num Y1 Y2)).
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
- by rewrite compre_scale ?integrableZl.
- rewrite [X in EFin \o X](_ : _ = r ^+2 \o* X ^+ 2)%R 1?mulrACA//.
  by rewrite compre_scale ?integrableZl.
- by rewrite -mulrAC compre_scale// integrableZl.
Qed.

End variance.
Notation "'V_ P [ X ]" := (variance P X).

Section markov_chebyshev_cantelli.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma markov (X : {RV P >-> R}) (f : R -> R) (eps : R) :
    (0 < eps)%R ->
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

Definition mmt_gen_fun (X : {RV P >-> R}) (t : R) := 'E_P[expR \o t \o* X].
Local Notation "'M_ X t" := (mmt_gen_fun X t).

Lemma chernoff (X : {RV P >-> R}) (r a : R) : (0 < r)%R ->
  P [set x | X x >= a]%R <= 'M_X r * (expR (- (r * a)))%:E.
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
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    (0 < lambda)%R ->
  P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
  <= (fine 'V_P[X] / (fine 'V_P[X] + lambda^2))%:E.
Proof.
move=> X1 X2 lambda_gt0.
have finEK : (fine 'E_P[X])%:E = 'E_P[X].
  by rewrite fineK ?unlock ?integral_fune_fin_num.
have finVK : (fine 'V_P[X])%:E = 'V_P[X] by rewrite fineK ?variance_fin_num.
pose Y := (X \- cst (fine 'E_P[X]))%R.
have Y1 : P.-integrable [set: T] (EFin \o Y).
  rewrite compreBr => [|//]; apply: integrableB X1 _ => [//|].
  exact: finite_measure_integrable_cst.
have Y2 : P.-integrable [set: T] (EFin \o (Y ^+ 2)%R).
  rewrite sqrrD/= compreDr => [|//].
  apply: integrableD => [//||]; last first.
    rewrite -[(_ ^+ 2)%R]/(cst ((- fine 'E_P[X]) ^+ 2)%R).
    exact: finite_measure_integrable_cst.
  rewrite compreDr => [|//]; apply: integrableD X2 _ => [//|].
  rewrite [X in EFin \o X](_ : _ = (- fine 'E_P[X] * 2) \o* X)%R; last first.
    by apply/funeqP => x /=; rewrite -mulr_natl mulrC mulrA.
  by rewrite compre_scale => [|//]; apply: integrableZl X1.
have EY : 'E_P[Y] = 0.
  rewrite expectationB/= ?finite_measure_integrable_cst//.
  rewrite expectation_cst finEK subee//.
  by rewrite unlock; apply: integral_fune_fin_num X1.
have VY : 'V_P[Y] = 'V_P[X] by rewrite varianceB_cst_r.
have le (u : R) : (0 <= u)%R ->
    P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
    <= ((fine 'V_P[X] + u^2) / (lambda + u)^2)%:E.
  move=> uge0; rewrite EFinM.
  have YU1 : P.-integrable [set: T] (EFin \o (Y \+ cst u)%R).
    rewrite compreDr => [|//]; apply: integrableD Y1 _ => [//|].
    exact: finite_measure_integrable_cst.
  have YU2 : P.-integrable [set: T] (EFin \o ((Y \+ cst u) ^+ 2)%R).
    rewrite sqrrD/= compreDr => [|//].
    apply: integrableD => [//||]; last first.
      rewrite -[(_ ^+ 2)%R]/(cst (u ^+ 2))%R.
      exact: finite_measure_integrable_cst.
    rewrite compreDr => [|//]; apply: integrableD Y2 _ => [//|].
    rewrite [X in EFin \o X](_ : _ = (2 * u) \o* Y)%R; last first.
      by apply/funeqP => x /=; rewrite -mulr_natl mulrCA.
    by rewrite compre_scale => [|//]; apply: integrableZl Y1.
  have -> : (fine 'V_P[X] + u^2)%:E = 'E_P[(Y \+ cst u)^+2]%R.
    rewrite -VY -[RHS](@subeK _ _ (('E_P[(Y \+ cst u)%R])^+2)); last first.
      by rewrite fin_numX ?unlock ?integral_fune_fin_num.
    rewrite -varianceE/= -/Y -?expe2//.
    rewrite expectationD/= ?EY ?add0e ?expectation_cst -?EFinM; last 2 first.
    - rewrite compreBr => [|//]; apply: integrableB X1 _ => [//|].
      exact: finite_measure_integrable_cst.
    - exact: finite_measure_integrable_cst.
    by rewrite (varianceD_cst_r _ Y1 Y2) EFinD fineK ?(variance_fin_num Y1 Y2).
  have le : [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
      `<=` [set x | ((lambda + u)^2)%:E <= ((Y x + u)^+2)%:E].
    move=> x /= le; rewrite lee_fin; apply: lerXn2r.
    - exact: addr_ge0 (ltW lambda_gt0) _.
    - apply/(addr_ge0 _ uge0)/(le_trans (ltW lambda_gt0) _).
      by rewrite -lee_fin EFinB finEK.
    - by rewrite lerD2r -lee_fin EFinB finEK.
  apply: (le_trans (le_measure _ _ _ le)).
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    by apply: emeasurable_funB => //; exact: measurable_int X1.
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    rewrite measurable_EFinP [X in measurable_fun _ X](_ : _ =
      (fun x => x ^+ 2) \o (fun x => Y x + u))%R//.
    by apply/measurableT_comp => //; apply/measurable_funD.
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
  by rewrite /u0 -mulrA mulVr ?mulr1 ?unitfE ?gt_eqF.
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
  rewrite -Ptrue -(@probability_setT _ _ _ P) setT_bool measureU//; last first.
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
have : P [set: bool] = 1%E := probability_setT.
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
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
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
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
rewrite /binomial_prob/=.
set f := (X in measurable_fun _ X).
apply: measurable_fun_if => //=.
  by apply: measurable_and => //; exact: measurable_fun_ler.
apply: (eq_measurable_fun (fun t =>
    \sum_(k <oo | k \in Ys) (binomial_pmf n t k)%:E))%E.
  move=> x /set_mem[_/= x01].
  rewrite nneseries_esum// -1?[in RHS](set_mem_set Ys)// => k kYs.
  by rewrite lee_fin binomial_pmf_ge0.
apply: ge0_emeasurable_sum.
  by move=> k x/= [_ x01] _; rewrite lee_fin binomial_pmf_ge0.
move=> k Ysk; apply/measurableT_comp => //.
exact: measurable_binomial_pmf.
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
rewrite F'E !fctE/= EFinM -muleA -EFinM mulVf ?mulr1.
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
