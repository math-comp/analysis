(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets signed functions topology normedtype cardinality.
Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.

(******************************************************************************)
(*                       Probability (experimental)                           *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(*               convn R == the type of sequence f : R^nat s.t.               *)
(*                          \sum_(n <oo) (f n)%:E = 1, the convex combination *)
(*                          of the point (f n)                                *)
(*          {RV P >-> R} == real random variable: a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*                  'E X == expectation of the real random variable X         *)
(*              'E_P [X] == expectation of the real measurable function X     *)
(*          mu.-Lspace p := [set f : T -> R | measurable_fun setT f /\        *)
(*                            \int[mu]_(x in D) (`|f x| ^+ p)%:E < +oo]       *)
(*                  'V X == variance of the real random variable X            *)
(*        distribution X == measure image of P by X : {RV P -> R}, declared   *)
(*                          as an instance of probability measure             *)
(*       {dmfun T >-> R} == type of discrete real-valued measurable functions *)
(*         {dRV P >-> R} == real-valued discrete random variable              *)
(*             dRV_dom X == domain of the random variable X                   *)
(*          enum_range X == bijection between the domain and the range of X   *)
(*         enum_prob X k == probability of the kth value in the range of X    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E' X" (format "''E'  X", at level 5).
Reserved Notation "''E_' P [ X ]" (format "''E_' P [ X ]", at level 5).
Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").
Reserved Notation "''V' X" (format "''V'  X", at level 5).
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

(* NB: available in lebesgue-stieltjes PR as EFinf *)
Definition funEFin {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma measurable_fun_funEFin (R : realType) (f : {mfun _ >-> R}) :
  measurable_fun [set: \bar R] (@funEFin R f).
Proof.
rewrite (_ : funEFin _ =
  fun x => if x \is a fin_num then (f (fine x))%:E else x); last first.
  by apply: funext=> -[].
apply: measurable_fun_ifT => /=.
+ apply: (@emeasurable_fun_bool _ _ _ _ true).
  rewrite /preimage/= -[X in measurable X]setTI.
  by apply/emeasurable_fin_num => //; exact: measurable_fun_id.
+ apply/EFin_measurable_fun/measurable_funT_comp => //.
  exact/measurable_fun_fine.
+ exact: measurable_fun_id.
Qed.

Lemma le_funEFin (R : realType) (f : R -> R) :
  {in `[0, +oo[%classic%R &, {homo f : x y / (x <= y)}} ->
  {in `[0, +oo[%classic%E &, {homo funEFin f : x y / (x <= y)%E}}.
Proof.
move=> f_nd x y; rewrite !inE/= !in_itv/= !andbT.
move: x y => [x| |] [y| |] x0 y0 xy//=.
  by rewrite lee_fin f_nd// inE /= in_itv/= andbT -lee_fin.
by rewrite leey.
Qed.

Section finite_measure_lemma.
Context d (T : measurableType d) (R : realType).
Variable (P : {finite_measure set T -> \bar R}).

Lemma finite_measure_integrable_cst k : P.-integrable [set: T] (EFin \o cst k).
Proof.
split; first exact/EFin_measurable_fun/measurable_fun_cst.
have [k0|k0] := leP 0 k.
- under eq_integral do rewrite /= ger0_norm//.
  rewrite integral_cst//= lte_mul_pinfty// fin_num_fun_lty//.
  exact: fin_num_measure.
- under eq_integral do rewrite /= ltr0_norm//.
  rewrite integral_cst//= lte_mul_pinfty//.
    by rewrite lee_fin ler_oppr oppr0 ltW.
  by rewrite fin_num_fun_lty//; exact: fin_num_measure.
Qed.

End finite_measure_lemma.

Section mfun.
Variable R : realType.

Definition mexp n : R -> R := @GRing.exp R ^~ n.

Let measurable_fun_mexp n : measurable_fun setT (mexp n).
Proof. exact/measurable_fun_exprn/measurable_fun_id. Qed.

HB.instance Definition _ (n : nat) := @isMeasurableFun.Build _ _ R
  (mexp n) (measurable_fun_mexp n).

Definition mabs : R -> R := fun x => `| x |.

Let measurable_fun_mabs : measurable_fun setT mabs.
Proof. exact: measurable_fun_normr. Qed.

HB.instance Definition _ := @isMeasurableFun.Build _ _ R
  mabs (measurable_fun_mabs).

Let measurable_fun_mmul d (T : measurableType d) (f g : {mfun T >-> R}) :
  measurable_fun setT (f \* g).
Proof. exact: measurable_funM. Qed.

HB.instance Definition _ d (T : measurableType d) (f g : {mfun T >-> R}) :=
  @isMeasurableFun.Build _ _ R (f \* g) (measurable_fun_mmul f g).

End mfun.

Section comp_mfun.
Context d (T : measurableType d) (R : realType)
  (f : {mfun Real_sort__canonical__measure_Measurable R >-> R})
  (g : {mfun T >-> R}).

Let measurable_fun_comp : measurable_fun [set: T] (f \o g).
Proof. exact: measurable_funT_comp. Qed.

HB.instance Definition _ := @isMeasurableFun.Build _ _ R (f \o g)
  measurable_fun_comp.

End comp_mfun.

Definition random_variable (d : _) (T : measurableType d) (R : realType)
  (P : probability T R) := {mfun T >-> R}.

Notation "{ 'RV' P >-> R }" := (@random_variable _ _ R P) : form_scope.

Lemma notin_range_probability d (T : measurableType d) (R : realType)
    (P : probability T R) (X : {RV P >-> R}) r :
  r \notin range X -> P (X @^-1` [set r]) = 0%E.
Proof. by rewrite notin_set => hr; rewrite preimage10. Qed.

Lemma probability_range d (T : measurableType d) (R : realType)
  (P : probability T R) (X : {RV P >-> R}) : P (X @^-1` range X) = 1%E.
Proof. by rewrite preimage_range probability_setT. Qed.

Section expectation.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition expectation (X : {RV P >-> R}) := \int[P]_w (X w)%:E.

End expectation.
Notation "''E' X" := (expectation X).
Notation "''E_' P [ X ]" := (@expectation _ _ _ P X).

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_cst r : 'E_P[cst_mfun r] = r%:E.
Proof. by rewrite /expectation /= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) :
  'E_P[indic_mfun A mA] = P A.
Proof. by rewrite /expectation integral_indic// setIT. Qed.

Lemma integrable_expectation (X : {RV P >-> R})
  (iX : P.-integrable setT (EFin \o X)) : `| 'E_P[X] | < +oo.
Proof.
move: iX => [? Xoo]; rewrite (le_lt_trans _ Xoo)//.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (X : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
  (k : R) : 'E_P[[the {mfun _ >-> _} of k \o* X]] = k%:E * 'E X.
Proof.
rewrite /expectation.
under eq_integral do rewrite EFinM.
rewrite -integralM//.
by under eq_integral do rewrite muleC.
Qed.

Lemma expectation_ge0 (X : {RV P >-> R}) : (forall x, 0 <= X x)%R -> 0 <= 'E X.
Proof.
by move=> ?; rewrite /expectation integral_ge0// => x _; rewrite lee_fin.
Qed.

Lemma expectation_le (X Y : {mfun T >-> R}) : (forall x, 0 <= X x)%R ->
  (forall x, X x <= Y x)%R -> 'E_P[X] <= 'E_P[Y].
Proof.
move => X0 XY; rewrite /expectation ge0_le_integral => //.
- by move=> t _; apply: X0.
- by apply EFin_measurable_fun.
- by move=> t _; rewrite lee_fin (le_trans _ (XY _)).
- by apply EFin_measurable_fun.
- by move=> t _; rewrite lee_fin.
Qed.

Lemma expectationD (X Y : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
    (iY : P.-integrable setT (EFin \o Y)) :
  'E_P[[the {mfun _ >-> _} of X \+ Y]]%R = 'E X + 'E Y.
Proof. by rewrite /expectation integralD_EFin. Qed.

Lemma expectationB (X Y : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
    (iY : P.-integrable setT (EFin \o Y)) :
  'E_P[[the {mfun _ >-> _} of X \- Y]]%R = 'E X - 'E Y.
Proof. by rewrite /expectation integralB_EFin. Qed.

End expectation_lemmas.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p := [set f : T -> R |
  measurable_fun setT f /\ (\int[mu]_x (`|f x| ^+ p)%:E < +oo)%E].

Lemma Lspace1 : Lspace 1 =
  [set f : T -> R | mu.-integrable setT (EFin \o f)].
Proof.
by rewrite /Lspace; apply/seteqP; split=> [f/= [mf foo]|f/= [mf foo]];
  split=> //; exact/EFin_measurable_fun.
Qed.

Lemma Lspace2 : Lspace 2 `<=`
  [set f : T -> R | mu.-integrable setT (EFin \o (fun x => f x ^+ 2))].
Proof.
move=> f/= [mf foo]; split.
- exact/EFin_measurable_fun/measurable_fun_exprn.
- rewrite (le_lt_trans _ foo)// ge0_le_integral//.
  + apply: measurable_funT_comp => //.
    exact/EFin_measurable_fun/measurable_fun_exprn.
  + apply/EFin_measurable_fun/measurable_fun_exprn.
    exact: measurable_funT_comp.
  + by move=> t _/=; rewrite lee_fin normrX.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (Lspace mu p) : type_scope.

Section variance.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : {RV P >-> R}) :=
  'E_P[[the {mfun _ >-> _} of (X \- cst (fine 'E X)) ^+ 2]]%R.
Local Notation "''V' X" := (variance X).

Lemma varianceE (X : {RV P >-> R}) : P.-Lspace 1 X -> P.-Lspace 2 X ->
  'V X = 'E_P[X ^+ 2]%R - ('E X) ^+ 2.
Proof.
move=> X1 X2.
have ? : P.-integrable [set: T] (EFin \o X) by rewrite Lspace1 in X1.
have ? : P.-integrable [set: T] (EFin \o (X ^+ 2)%R)  by apply: Lspace2.
have ? : 'E X \is a fin_num by rewrite fin_num_abs// integrable_expectation.
rewrite /variance.
rewrite [X in 'E_P[X]](_ : _ = [the {mfun _ >-> _} of
    (X ^+ 2 \- (2 * fine 'E X) \o* X \+ fine ('E X ^+ 2) \o* cst 1)%R]); last first.
  apply/mfuneqP => x /=.
  by rewrite -expr2 sqrrB mulr_natl -mulrnAr mul1r fineM.
rewrite expectationD/=; last 2 first.
  - rewrite (_ : _ \o _ =
      (fun x => (EFin \o (X ^+ 2)%R) x - (EFin \o (2 * fine 'E X \o* X)) x)) //.
    apply: integrableB => //.
    apply: (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E)) => //.
      by move=> t _ /=; rewrite muleC EFinM.
    exact: integrablerM.
  - apply: (eq_integrable _ (fun x => (fine ('E X ^+ 2))%:E * (cst 1 x)%:E)) => //.
      by move=> t _ /=; rewrite mul1r mule1.
    by apply: integrablerM => //; exact: probability_integrable_cst.
(* NB: display broken *)
rewrite expectationB //; last first.
  apply: (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E)) => //.
    by move=> t _ /=; rewrite !EFinM [in RHS]muleC.
  exact: integrablerM.
rewrite expectationM// expectationM; last exact: probability_integrable_cst.
rewrite expectation_cst mule1 EFinM fineK// fineK ?fin_numM// -muleA -expe2.
rewrite mule_natl mule2n oppeD; last by rewrite fin_num_adde_defl// fin_numX.
by rewrite addeA subeK// fin_numX.
Qed.

End variance.
Notation "''V' X" := (variance X).

Definition distribution (d : _) (T : measurableType d) (R : realType)
    (P : probability T R) (X : {mfun T >-> R}) :=
  pushforward P (@measurable_funP _ _ _ X).

Section distribution_is_probability.
Context d (T : measurableType d) (R : realType) (P : probability T R)
        (X : {mfun T >-> R}).

Let distribution0 : distribution P X set0 = 0%E.
Proof. exact: measure0. Qed.

Let distribution_ge0 A : (0 <= distribution P X A)%E.
Proof. exact: measure_ge0. Qed.

Let distribution_sigma_additive : semi_sigma_additive (distribution P X).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ R _ (distribution P X)
  distribution0 distribution_ge0 distribution_sigma_additive.

Let distribution_is_probability : distribution P X [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ R
  (distribution P X) distribution_is_probability.

End distribution_is_probability.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma integral_distribution (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite integral_pushforward. Qed.

End transfer_probability.

Section markov_chebyshev.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma markov (X : {RV P >-> R}) (f : {mfun _ >-> R}) (eps : R) :
    (0 < eps)%R -> (forall r : R, 0 <= f r)%R ->
    {in `[0, +oo[%classic &, {homo f : x y / x <= y}}%R ->
  (f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ] <=
    'E_P[[the {mfun _ >-> R} of f \o @mabs R \o X]].
Proof.
move=> e0 f0 f_nd; rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse d T R P setT measurableT (EFin \o X)
  eps (funEFin f) _ _ _ _ e0)) => //=.
- exact: measurable_fun_funEFin.
- by case => //= r _; exact: f0.
- exact: le_funEFin.
- exact/EFin_measurable_fun.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E X)|)%R ] <= (eps ^- 2)%:E * 'V X.
Proof.
move => heps; have [hv|hv] := eqVneq ('V X)%E +oo%E.
  by rewrite hv mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[(Y ^+ 2)%R].
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  have : {in `[0, +oo[%classic &, {homo mexp 2 : x y / x <= y :> R}}%R.
    move=> x y; rewrite !inE !mksetE !in_itv/= !andbT => x0 y0.
    by rewrite ler_sqr.
  move=> /(@markov Y [the {mfun _ >-> R} of @mexp R 2] _ heps (@sqr_ge0 _)) /=.
  move=> /le_trans; apply => /=.
  apply: expectation_le => //=.
  - by move=> x; rewrite /mexp /mabs sqr_ge0.
  - by move=> x; rewrite /mexp /mexp /mabs real_normK// num_real.
have := h [the {mfun T >-> R} of (X \- cst (fine ('E X)))%R].
by move=> /le_trans; apply; rewrite lee_pmul2l// lte_fin invr_gt0 exprn_gt0.
Qed.

End markov_chebyshev.

HB.mixin Record MeasurableFun_isDiscrete d (T : measurableType d) (R : realType)
    (X : T -> R) of @MeasurableFun d T R X := {
  countable_range : countable (range X)
}.

HB.structure Definition discreteMeasurableFun d (T : measurableType d)
    (R : realType) := {
  X of isMeasurableFun d T R X & MeasurableFun_isDiscrete d T R X
}.

Notation "{ 'dmfun' aT >-> T }" :=
  (@discreteMeasurableFun.type _ aT T) : form_scope.

Definition discrete_random_variable (d : _) (T : measurableType d)
  (R : realType) (P : probability T R) := {dmfun T >-> R}.

Notation "{ 'dRV' P >-> R }" :=
  (@discrete_random_variable _ _ R P) : form_scope.

Section dRV_definitions.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition dRV_dom_enum (X : {dRV P >-> R}) :
  { B : set nat & {splitbij B >-> range X}}.
have /countable_bijP/cid[B] := @countable_range _ _ _ X.
move/card_esym/ppcard_eqP/unsquash => f.
exists B; exact: f.
Qed.

Definition dRV_dom (X : {dRV P >-> R}) : set nat := projT1 (dRV_dom_enum X).

Definition dRV_enum (X : {dRV P >-> R}) : {splitbij (dRV_dom X) >-> range X} :=
  projT2 (dRV_dom_enum X).

Definition enum_prob (X : {dRV P >-> R}) :=
  (fun k => P (X @^-1` [set dRV_enum X k])) \_ (dRV_dom X).

End dRV_definitions.

Section distribution_dRV.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable X : {dRV P >-> R}.

Lemma distribution_dRV_enum (n : nat) : n \in dRV_dom X ->
  distribution P X [set dRV_enum X n] = enum_prob X n.
Proof.
by move=> nX; rewrite /distribution/= /enum_prob/= patchE nX.
Qed.

Lemma distribution_dRV A : measurable A ->
  distribution P X A = \sum_(k <oo) enum_prob X k * \d_ (dRV_enum X k) A.
Proof.
move=> mA; rewrite /distribution /pushforward.
have mAX i : dRV_dom X i -> measurable (X @^-1` (A `&` [set dRV_enum X i])).
  move=> _; rewrite preimage_setI; apply: measurableI => //.
  exact/measurable_sfunP.
have tAX : trivIset (dRV_dom X) (fun k => X @^-1` (A `&` [set dRV_enum X k])).
  under eq_fun do rewrite preimage_setI; rewrite -/(trivIset _ _).
  apply: trivIset_setIl; apply/trivIsetP => i j iX jX /eqP ij.
  rewrite -preimage_setI (_ : _ `&` _ = set0)//.
  by apply/seteqP; split => //= x [] -> {x} /inj; rewrite inE inE => /(_ iX jX).
have := measure_bigcup P _ (fun k => X @^-1` (A `&` [set dRV_enum X k])) mAX tAX.
rewrite -preimage_bigcup => {mAX tAX}PXU.
rewrite -{1}(setIT A) -(setUv (\bigcup_(i in dRV_dom X) [set dRV_enum X i])).
rewrite setIUr preimage_setU measureU; last 3 first.
  - rewrite preimage_setI; apply: measurableI => //.
      exact: measurable_sfunP.
    by apply: measurable_sfunP; exact: bigcup_measurable.
  - apply: measurable_sfunP; apply: measurableI => //.
    by apply: measurableC; exact: bigcup_measurable.
  - rewrite 2!preimage_setI setIACA -!setIA -preimage_setI.
    by rewrite setICr preimage_set0 2!setI0.
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
rewrite notin_set => kA.
rewrite mule0 (disjoints_subset _ _).2 ?preimage_set0 ?measure0//.
by apply: subsetCr; rewrite sub1set inE.
Qed.

Lemma convn_enum_prob : (\sum_(n <oo) (enum_prob X) n = 1)%E.
Proof.
have := distribution_dRV measurableT.
rewrite probability_setT/= => /esym; apply: eq_trans.
by rewrite [RHS]eseries_mkcond; apply: eq_eseriesr => k _; rewrite diracT mule1.
Qed.

End distribution_dRV.

Section discrete_distribution.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_distribution (X : {dRV P >-> R}) r :
  P [set x | X x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma dRV_expectation (X : {dRV P >-> R}) : P.-integrable setT (EFin \o X) ->
  'E (X : {RV P >-> R}) = (\sum_(n <oo) enum_prob X n * (dRV_enum X n)%:E)%E.
Proof.
move=> ix; rewrite /expectation.
rewrite -[in LHS](_ : \bigcup_k (if k \in dRV_dom X then
    X @^-1` [set dRV_enum X k] else set0) = setT); last first.
  apply/seteqP; split => // t _.
  exists ((dRV_enum X)^-1%function (X t)) => //.
  case: ifPn=> [_|].
    by rewrite invK// inE.
  by rewrite notin_set/=; apply; apply: funS.
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
      (dRV_enum X i)%:E)%E.
  apply: eq_eseriesr => i _; case: ifPn => iX.
    by apply: eq_integral => t; rewrite in_setE/= => ->.
  by rewrite !integral_set0.
transitivity (\sum_(i <oo) (dRV_enum X i)%:E *
    \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
      1)%E.
  apply: eq_eseriesr => i _; rewrite -integralM//; last 2 first.
    - by case: ifPn.
    - split; first exact: measurable_fun_cst.
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

Definition pmf (X : {dRV P >-> R}) (r : R) : R := fine (P (X @^-1` [set r])).

Lemma expectation_pmf (X : {dRV P >-> R}) : P.-integrable setT (EFin \o X) ->
  'E_P[X] =
  (\sum_(n <oo | n \in dRV_dom X) (pmf X (dRV_enum X n))%:E * (dRV_enum X n)%:E)%E.
Proof.
move=> iX; rewrite dRV_expectation// [in RHS]eseries_mkcond.
apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => kX; last by rewrite mul0e.
by rewrite /pmf fineK// fin_num_measure.
Qed.

End discrete_distribution.
