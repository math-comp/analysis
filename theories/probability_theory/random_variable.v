(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint poly interval.
From mathcomp Require Import archimedean finmap interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences measure.
From mathcomp Require Import exp numfun realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral hoelder.

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

Lemma integrable_expectation (X : {RV P >-> R}) :
  (X : T -> R) \in Lfun P 1 -> `| 'E_P[X] | < +oo.
Proof.
move/Lfun1_integrable => /integrableP[? Xoo]; rewrite (le_lt_trans _ Xoo)//.
by rewrite expectation_def (le_trans (le_abse_integral _ _ _)).
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
    - by move=> x y; rewrite !nnegrE => x0 y0; rewrite ler_sqr.
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
