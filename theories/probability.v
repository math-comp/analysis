(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From HB Require Import structures.
Require Import exp numfun lebesgue_measure lebesgue_integral.
Require Import reals ereal signed topology normedtype sequences esum measure.
Require Import hoelder.

(******************************************************************************)
(*                       Probability (experimental)                           *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(*          {RV P >-> R} == real random variable: a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*        distribution X == measure image of P by X : {RV P -> R}, declared   *)
(*                          as an instance of probability measure             *)
(*               'E_P[X] == expectation of the real measurable function X     *)
(*        covariance X Y == covariance between real random variable X and Y   *)
(*               'V_P[X] == variance of the real random variable X            *)
(*         mmt_gen_fun X == moment generating function of the random variable *)
(*                          X *)
(*       {dmfun T >-> R} == type of discrete real-valued measurable functions *)
(*         {dRV P >-> R} == real-valued discrete random variable              *)
(*             dRV_dom X == domain of the discrete random variable X          *)
(*            dRV_enum X == bijection between the domain and the range of X   *)
(*               pmf X r := fine (P (X @^-1` [set r]))                        *)
(*         enum_prob X k == probability of the kth value in the range of X    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E_' P [ X ]" (format "''E_' P [ X ]", at level 5).
Reserved Notation "''V_' P [ X ]" (format "''V_' P [ X ]", at level 5).
Reserved Notation "{ 'dmfun' aT >-> T }"
  (at level 0, format "{ 'dmfun'  aT  >->  T }").
Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%E/1%:E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%E/1%:E]_(i <- r) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%E/1%:E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%E/1%:E]_(m <= i < n) F%E) : ereal_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%E/1%:E]_(i | P%B) F%E) : ereal_scope.
Notation "\prod_ i F" :=
  (\big[*%E/1%:E]_i F%E) : ereal_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%E/1%:E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%E/1%:E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%E/1%:E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%E/1%:E]_(i < n) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%E/1%:E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%E/1%:E]_(i in A) F%E) : ereal_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition random_variable (d : _) (T : measurableType d) (R : realType)
  (P : probability T R) := {mfun T >-> R}.

Notation "{ 'RV' P >-> R }" := (@random_variable _ _ R P) : form_scope.

Lemma notin_range_measure d (T : measurableType d) (R : realType)
    (P : {measure set T -> \bar R}) (X : T -> R) r :
  r \notin range X -> P (X @^-1` [set r]) = 0%E.
Proof. by rewrite notin_set => hr; rewrite preimage10. Qed.

Lemma probability_range d (T : measurableType d) (R : realType)
  (P : probability T R) (X : {RV P >-> R}) : P (X @^-1` range X) = 1%E.
Proof. by rewrite preimage_range probability_setT. Qed.

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

HB.instance Definition _ := isMeasure.Build _ _ R (distribution P X)
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

Lemma probability_distribution (X : {RV P >-> R}) r :
  P [set x | X x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma integral_distribution (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite integral_pushforward. Qed.

End transfer_probability.

HB.lock Definition expectation {d} {T : measurableType d} {R : realType}
  (P : probability T R) (X : T -> R) := (\int[P]_w (X w)%:E)%E.
Canonical expectation_unlockable := Unlockable expectation.unlock.
Arguments expectation {d T R} P _%R.
Notation "''E_' P [ X ]" := (@expectation _ _ _ P X) : ereal_scope.

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

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

Lemma expectationM (X : {RV P >-> R}) (iX : P.-integrable [set: T] (EFin \o X))
  (k : R) : 'E_P[k \o* X] = k%:E * 'E_P [X].
Proof.
rewrite unlock; under eq_integral do rewrite EFinM.
by rewrite -integralZl//; under eq_integral do rewrite muleC.
Qed.

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
- exact/EFin_measurable_fun.
- by move=> t _; apply: Y0.
- exact/EFin_measurable_fun.
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

Lemma sum_RV_ge0 (X : seq {RV P >-> R}) x :
    (forall Xi, Xi \in X -> 0 <= Xi x)%R ->
    (0 <= (\sum_(Xi <- X) Xi) x)%R.
Proof.
elim: X => [|X0 X IHX] Xi_ge0; first by rewrite big_nil.
rewrite big_cons.
rewrite addr_ge0//=; first by rewrite Xi_ge0// in_cons eq_refl.
by rewrite IHX// => Xi XiX; rewrite Xi_ge0// in_cons XiX orbT.
Qed.

End expectation_lemmas.

HB.lock Definition covariance {d} {T : measurableType d} {R : realType}
    (P : probability T R) (X Y : T -> R) :=
  'E_P[(X \- cst (fine 'E_P[X])) * (Y \- cst (fine 'E_P[Y]))]%E.
Canonical covariance_unlockable := Unlockable covariance.unlock.
Arguments covariance {d T R} P _%R _%R.

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
rewrite 3?expectationM//= ?finite_measure_integrable_cst//.
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
rewrite covarianceE// aXY !expectationM//.
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
rewrite covarianceDr// covarianceDr ?(mulrC Y X)//.
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
rewrite -EFin_expe -EFinM lee_fin -(@ler_pmul2l _ 4%:R) ?ltr0n// [leRHS]mulrA.
rewrite [in leLHS](natrM _ 2 2) mulrACA -expr2 -subr_le0.
apply: deg_le2_ge0 => r; rewrite -lee_fin !EFinD.
rewrite EFinM fineK ?variance_fin_num// muleC -varianceZ//.
rewrite -mulrA EFinM mulrC EFinM ?fineK ?covariance_fin_num// -covarianceZl//.
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
- by move=> [x| |] [y| |]; rewrite !set_interval.set_itvE !inE ?lee_fin => //= x0 y0 xy; rewrite ?f_nd ?leey.
- exact/EFin_measurable_fun.
- by rewrite unlock.
Qed.

Definition mmt_gen_fun (X : {RV P >-> R}) (t : R) := 'E_P[expR \o t \o* X].

Lemma chernoff (X : {RV P >-> R}) (r a : R) : (0 < r)%R ->
  P [set x | X x >= a]%R <= mmt_gen_fun X r * (expR (- (r * a)))%:E.
Proof.
move=> t0.
rewrite /mmt_gen_fun; have -> : expR \o r \o* X =
    (normr \o normr) \o [the {mfun T >-> R} of expR \o r \o* X].
  by apply: funext => t /=; rewrite normr_id ger0_norm ?expR_ge0.
rewrite expRN lee_pdivl_mulr ?expR_gt0//.
rewrite (le_trans _ (markov _ (expR_gt0 (r * a)) _ _ _))//; last first.
  exact: (monoW_in (@ger0_le_norm _)).
rewrite ger0_norm ?expR_ge0// muleC lee_pmul2l// ?lte_fin ?expR_gt0//.
rewrite [X in _ <= P X](_ : _ = [set x | a <= X x]%R)//; apply: eq_set => t/=.
by rewrite ger0_norm ?expR_ge0// lee_fin ler_expR  mulrC ler_pmul2r.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E_P[X])|)%R ] <= (eps ^- 2)%:E * 'V_P[X].
Proof.
move => heps; have [->|hv] := eqVneq 'V_P[X] +oo.
  by rewrite mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[Y ^+ 2].
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  apply: (@le_trans _ _ ('E_P[(@GRing.exp R ^~ 2%N \o normr) \o Y])).
    apply: (@markov Y (@GRing.exp R ^~ 2%N)) => //.
    - by move=> r _; apply: sqr_ge0.
    - move=> x y; rewrite !nnegrE => x0 y0.
      by rewrite ler_sqr.
  apply: expectation_le => //.
    - by apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> x /=; apply: sqr_ge0.
  - by move=> x /=; apply: sqr_ge0.
  - by apply/aeW => t /=; rewrite real_normK// num_real.
have := h [the {mfun T >-> R} of (X \- cst (fine ('E_P[X])))%R].
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
    move=> x /= le; rewrite lee_fin; apply: ler_expn2r.
    - exact: addr_ge0 (ltW lambda_gt0) _.
    - apply/(addr_ge0 _ uge0)/(le_trans (ltW lambda_gt0) _).
      by rewrite -lee_fin EFinB finEK.
    - by rewrite ler_add2r -lee_fin EFinB finEK.
  apply: (le_trans (le_measure _ _ _ le)).
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    by apply: emeasurable_funB => //; exact: measurable_int X1.
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    rewrite EFin_measurable_fun [X in measurable_fun _ X](_ : _ =
      (fun x => x ^+ 2) \o (fun x => Y x + u))%R//.
    apply/measurableT_comp => //; apply/measurable_funD => //.
    by rewrite -EFin_measurable_fun; apply: measurable_int Y1.
  set eps := ((lambda + u) ^ 2)%R.
  have peps : (0 < eps)%R by rewrite exprz_gt0 ?ltr_paddr.
  rewrite (lee_pdivl_mulr _ _ peps) muleC.
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
rewrite GRing.eqr_div; [|apply: lt0r_neq0..]; last 2 first.
- by rewrite exprz_gt0 -1?[ltLHS]addr0 ?ltr_le_add.
- by rewrite ltr_paddl ?fine_ge0 ?variance_ge0 ?exprz_gt0.
apply/eqP; have -> : fine 'V_P[X] = (u0 * lambda)%R.
  by rewrite /u0 -mulrA mulVr ?mulr1 ?unitfE ?gt_eqF.
by rewrite -mulrDl -mulrDr (addrC u0) [in RHS](mulrAC u0) -exprnP expr2 !mulrA.
Qed.

End markov_chebyshev_cantelli.

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

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition bernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac (1%R:R)]]
    [the measure _ _ of mscale (NngNum (onem_ge0 p1)) [the measure _ _ of dirac (0%R:R)]].

HB.instance Definition _ := Measure.on bernoulli.

Local Close Scope ring_scope.

Let bernoulli_setT : bernoulli [set: _] = 1%E.
Proof.
rewrite /bernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracT !mule1 -EFinD add_onemK.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

End bernoulli.

Local Open Scope ereal_scope.
Lemma integral_bernoulli {R : realType}
    (p : {nonneg R}) (p1 : (p%:num <= 1)%R) (f : R -> \bar R) :
  measurable_fun setT f ->
  (forall x, 0 <= f x) ->
  \int[bernoulli p1]_y (f y) = p%:num%:E * f 1%R + (`1-(p%:num))%:E * f 0%R.
Proof.
move=> mf f0.
rewrite ge0_integral_measure_sum//= 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= 2!diracT 2!mul1e.
Qed.

Section integrable_comp.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variable phi : X -> Y.
Hypothesis mphi : measurable_fun [set: X] phi.
Variable mu : {measure set X -> \bar R}.
Variable f : Y -> \bar R.
Hypothesis mf : measurable_fun [set: Y] f.
Hypothesis intf : mu.-integrable [set: X] (f \o phi).
Local Open Scope ereal_scope.

Lemma integrable_comp_funeneg : (pushforward mu mphi).-integrable [set: Y] f^\-.
Proof.
apply/integrableP; split.
  exact: measurable_funeneg.
move/integrableP : (intf) => [_].
apply: le_lt_trans.
rewrite integral_pushforward//=; last first.
  apply: measurableT_comp => //=.
  exact: measurable_funeneg.
apply: ge0_le_integral => //=.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
exact: measurable_funeneg.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
move=> x _.
rewrite -/((abse \o (f \o phi)) x).
rewrite (fune_abse (f \o phi)) /=.
rewrite gee0_abs//.
by rewrite lee_addr//.
Qed.

Lemma integrable_comp_funepos : (pushforward mu mphi).-integrable [set: Y] f^\+.
Proof.
apply/integrableP; split.
  exact: measurable_funepos.
move/integrableP : (intf) => [_].
apply: le_lt_trans.
rewrite integral_pushforward//=; last first.
  apply: measurableT_comp => //=.
  exact: measurable_funepos.
apply: ge0_le_integral => //=.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
exact: measurable_funepos.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
move=> x _.
rewrite -/((abse \o (f \o phi)) x).
rewrite (fune_abse (f \o phi)) /=.
rewrite gee0_abs//.
by rewrite lee_addl//.
Qed.

End integrable_comp.

Section transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (mu : {measure set X -> \bar R}).

Lemma integral_pushforward_new (f : Y -> \bar R) :
  measurable_fun setT f ->
  mu.-integrable setT (f \o phi) ->
  \int[pushforward mu mphi]_y f y = \int[mu]_x (f \o phi) x.
Proof.
move=> mf intf.
transitivity (\int[mu]_y ((f^\+ \o phi) \- (f^\- \o phi)) y); last first.
  by apply: eq_integral => x _; rewrite [in RHS](funeposneg (f \o phi)).
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite -[X in _ = X - _]integral_pushforward//; last first.
  exact: measurable_funepos.
rewrite -[X in _ = _ - X]integral_pushforward//; last first.
  exact: measurable_funeneg.
rewrite -integralB//=; last first.
- apply: integrable_comp_funepos => //.
    exact: measurableT_comp.
  exact: integrableN.
- exact: integrable_comp_funepos.
- apply/eq_integral => x _.
  by rewrite /= [in LHS](funeposneg f).
Qed.

End transfer.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma integral_distribution_new (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun setT f ->
    P.-integrable [set: T] (f \o X) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf intf; rewrite integral_pushforward_new. Qed.

End transfer_probability.

Section integral_measure_add_new.
Context d (T : measurableType d) (R : realType)
  (m1 m2 : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Variable f : T -> \bar R.
Hypothesis intf1 : m1.-integrable D f.
Hypothesis intf2 : m2.-integrable D f.
Hypothesis mf : measurable_fun D f.

Lemma integral_measure_add_new :
  \int[measure_add m1 m2]_(x in D) f x = \int[m1]_(x in D) f x + \int[m2]_(x in D) f x.
transitivity (\int[m1]_(x in D) (f^\+ \- f^\-) x +
              \int[m2]_(x in D) (f^\+ \- f^\-) x); last first.
  by congr +%E; apply: eq_integral => x _; rewrite [in RHS](funeposneg f).
rewrite integralB//; last 2 first.
  exact: integrable_funepos.
  exact: integrable_funeneg.
rewrite integralB//; last 2 first.
  exact: integrable_funepos.
  exact: integrable_funeneg.
rewrite addeACA.
rewrite -integral_measure_add//; last first.
  apply: measurable_funepos.
  exact: measurable_int intf1.
rewrite -oppeD; last first.
  by rewrite ge0_adde_def// inE integral_ge0.
rewrite -integral_measure_add//; last first.
  apply: measurable_funeneg.
  exact: measurable_int intf1.
by rewrite integralE.
Qed.

End integral_measure_add_new.

Section bernoulli.

Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : {nonneg R}.
Hypothesis p1 : (p%:num <= 1)%R.

Definition bernoulli_RV (X : {RV P >-> R}) :=
  distribution P X = bernoulli p1 /\ (range X = [set 0; 1])%R.

Lemma bernoulli_RV1 (X : {RV P >-> R}) : bernoulli_RV X ->
  P [set i | X i == 1%R] == p%:num%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 1%:R]))]].
rewrite /bernoulli/=.
rewrite measure_addE/=.
rewrite /mscale/=.
rewrite diracE/= mem_set// mule1// diracE/= memNset//; last first.
  rewrite /=.
  apply/eqP.
  by rewrite eq_sym oner_eq0.
rewrite mule0 adde0.
rewrite /distribution /= => <- _.
apply/eqP; congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_RV2 (X : {RV P >-> R}) : bernoulli_RV X ->
  P [set i | X i == 0%R] == (`1-(p%:num))%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 0%:R]))]].
rewrite /bernoulli/=.
rewrite measure_addE/=.
rewrite /mscale/=.
rewrite diracE/= memNset//; last first.
  rewrite /=.
  apply/eqP.
  by rewrite oner_eq0.
rewrite mule0// diracE/= mem_set// add0e mule1.
rewrite /distribution /= => <- _.
apply/eqP; congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_ge0 (X : {RV P >-> R}) : bernoulli_RV X ->
  forall t, (X t >= 0)%R.
Proof.
move=> bX t.
suff: (range X) (X t) by rewrite bX.2 => -[] ->.
by exists t.
Qed.

Lemma bernoulli_expectation (X : {RV P >-> R}) :
  bernoulli_RV X -> 'E_P[X] = p%:num%:E.
Proof.
move=> bX.
rewrite unlock.
transitivity (\int[P]_w `|X w|%:E).
  apply: eq_integral => t _.
  by rewrite ger0_norm// bernoulli_ge0.
rewrite -(@integral_distribution _ _ _ _ _ (EFin \o normr))//; last first.
  by move=> y //=.
  exact: measurableT_comp.
rewrite bX.1.
rewrite /bernoulli/=.
rewrite integral_measure_add//=; last first.
  by apply: measurableT_comp.
rewrite ge0_integral_mscale//=; last first.
  by apply: measurableT_comp.
rewrite ge0_integral_mscale//=; last first.
  by apply: measurableT_comp.
rewrite !integral_dirac//=; last 2 first.
  by apply: measurableT_comp.
  by apply: measurableT_comp.
by rewrite normr1 normr0 !mule0 adde0 mule1 diracT mule1.
Qed.

Lemma bernoulli_sqr (X : {RV P >-> R}) :
  bernoulli_RV X -> bernoulli_RV (X ^+ 2 : {RV P >-> R})%R.
Proof.
rewrite /bernoulli_RV => -[Xp1 X01]; split.
  rewrite -Xp1; apply/funext => A.
  rewrite /distribution /pushforward/=; congr (P _).
  by apply/seteqP; split => [t|t];
    (have : (range X) (X t) by exists t);
    rewrite X01/= /GRing.mul/= => -[] ->; rewrite ?(mul0r,mul1r).
rewrite -X01; apply/seteqP; split => [x|x].
- move=> [t _] /=; rewrite /GRing.mul/= -expr2 => <-;
  (have : (range X) (X t) by exists t);
  by rewrite X01/= /GRing.mul/= => -[] Xt;
    exists t => //; rewrite Xt ?(expr0n,expr1n).
- move=> [t _] /=; rewrite /GRing.mul/= => <-;
  (have : (range X) (X t) by exists t);
  by rewrite X01/= => -[] Xt;
    exists t => //=; rewrite Xt/= ?(mulr0,mulr1).
Qed.

Lemma integrable_bernoulli (X : {RV P >-> R}) :
  bernoulli_RV X -> P.-integrable [set: T] (EFin \o X).
Proof.
move=> bX.
apply/integrableP; split; first by apply: measurableT_comp.
have -> : \int[P]_x `|(EFin \o X) x| = 'E_P[X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  rewrite gee0_abs //= lee_fin.
  by rewrite bernoulli_ge0//.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma bernoulli_variance (X : {RV P >-> R}) :
(* NB(rei): no need for that?
   P.-integrable setT (EFin \o X) ->
   P.-integrable [set: T] (EFin \o (X ^+ 2)%R) ->*)
bernoulli_RV X -> 'V_P[X] = (p%:num * (`1-(p%:num)))%:E.
move=> b.
rewrite varianceE; last 2 first.
  exact: integrable_bernoulli.
  exact: integrable_bernoulli (bernoulli_sqr b).
rewrite (bernoulli_expectation b).
have b2 := bernoulli_sqr b.
rewrite (bernoulli_expectation b2) /=.
by rewrite -EFinD mulrDr mulr1 mulrN.
Qed.

Lemma probability_setC A : d.-measurable A -> P (~` A) = 1 - P A.
Proof.
move=> mA; rewrite -(@probability_setT _ _ _ P) -[in RHS](setTI A) -measureD ?setTD ?setCK//.
by rewrite [ltLHS](@probability_setT _ _ _ P) ltry.
Qed.

Lemma probability_setC' A : d.-measurable A -> P A = 1 - P (~` A).
Proof.
move=> mA. rewrite -(@probability_setT _ _ _ P) -[in RHS](setTI (~` A)) -measureD ?setTD ?setCK//; first exact: measurableC.
by rewrite [ltLHS](@probability_setT _ _ _ P) ltry.
Qed.

Definition independent_RVs (X : seq {RV P >-> R}) := forall t,
    (fine ('E_P[expR \o t \o* \sum_(Xi <- X) Xi]) = \prod_(Xi <- X) fine ('E_P[expR \o t \o* Xi]))%R.

Definition is_bernoulli_trial (X : seq {RV P >-> R}) n :=
  (forall Xi, Xi \in X -> bernoulli_RV Xi) /\
    independent_RVs X /\
    size X = n(*NB: used n.-tuple instead of seq*).

Definition bernoulli_trial (X : seq {RV P >-> R}) :=
  (\sum_(Xi <- X) Xi)%R.

Lemma expectation_bernoulli_trial (X : seq {RV P >-> R}) n :
  is_bernoulli_trial X n -> 'E_P[@bernoulli_trial X] = (n%:R * p%:num)%:E.
Proof.
move=> [bRV [_ Xn]]; rewrite expectation_sum; last first.
  by move=> Xi XiX; exact: (integrable_bernoulli (bRV _ XiX)).
under eq_big_seq => Xi XiX.
  by rewrite (bernoulli_expectation (bRV Xi _))//; over.
rewrite /= -Xn -sum1_size natr_sum big_distrl/= sumEFin; congr EFin.
by under [RHS]eq_bigr do rewrite mul1r.
Qed.

Lemma bernoulli_trial_ge0 (X : seq {RV P >-> R}) n : is_bernoulli_trial X n ->
  (forall t, 0 <= bernoulli_trial X t)%R.
Proof.
move=> [bRV Xn] t.
rewrite /bernoulli_trial [leRHS](_ : _ = \sum_(Xi <- X) Xi t)%R; last first.
  by rewrite {bRV Xn}; elim/big_ind2 : _ => //= _ f _ g <- <-.
  (* NB: this maybe need to be a lemma*)
by rewrite big_seq; apply: sumr_ge0 => i iX; exact/bernoulli_ge0/bRV.
Qed.

(* this seems to be provable like in https://www.cs.purdue.edu/homes/spa/courses/pg17/mu-book.pdf page 65 *)
Axiom taylor_ln_le : forall (delta : R), ((1 + delta) * ln (1 + delta) >= delta + delta^+2 / 3)%R.

Lemma expR_prod (X : seq {RV P >-> R}) (f : {RV P >-> R} -> R) :
  (\prod_(x <- X) expR (f x) = expR (\sum_(x <- X) f x))%R.
Proof.
elim: X => [|h t ih]; first by rewrite !big_nil expR0.
by rewrite !big_cons ih expRD.
Qed.

Lemma bernoulli_mmt_gen_fun (X : {RV P >-> R}) (t : R) :
  bernoulli_RV X -> 'E_P[expR \o t \o* X] = (p%:num * expR t + (1-p%:num))%:E.
Admitted.

Lemma binomial_mmt_gen_fun (X_ : seq {RV P >-> R}) n (t : R) :
  is_bernoulli_trial X_ n ->
  let X := bernoulli_trial X_ : {RV P >-> R} in
  mmt_gen_fun X t = ((p%:num * expR t + (1-p%:num))`^(n%:R))%:E.
Proof.
rewrite /is_bernoulli_trial /independent_RVs /bernoulli_trial.
move=> [bX1 [bX2 bX3]] /=.
rewrite -[LHS]fineK; last admit.
rewrite bX2 big_seq.
apply: congr1.
under eq_bigr => Xi XiX do rewrite (bernoulli_mmt_gen_fun _ (bX1 _ _))//=.
Admitted.

Lemma lm23 (X_ : seq {RV P >-> R}) (t : R) n :
  (0 <= t)%R ->
  is_bernoulli_trial X_ n ->
  let X := bernoulli_trial X_ : {RV P >-> R} in
  let mu := 'E_P[X] in
  mmt_gen_fun X t <= (expR (fine mu * (expR t - 1)))%:E.
Proof.
rewrite /= => t0 bX. (*[bX1 [bX2 bX3]].*)
set X := bernoulli_trial X_.
set mu := 'E_P[X].
have -> : @mmt_gen_fun _ _ _ P X t = (\prod_(Xi <- X_) fine (mmt_gen_fun Xi t))%:E.
  rewrite -[LHS]fineK; last rewrite (binomial_mmt_gen_fun _ bX)//.
  apply: congr1; apply: bX.2.1 => //.
under eq_big_seq => Xi XiX.
  have -> : @mmt_gen_fun _ _ _ P Xi t = (1 + p%:num * (expR t - 1))%:E.
    rewrite /mmt_gen_fun.
    rewrite bernoulli_mmt_gen_fun//; last exact: bX.1.
    apply: congr1.
    by rewrite mulrBr mulr1 addrCA.
  over.
rewrite lee_fin /=.
apply: (le_trans (@ler_prod _ _ _ _ _ (fun x => expR (p%:num * (expR t - 1)))%R _)).
  move=> Xi _.
  rewrite addr_ge0 ?mulr_ge0 ?subr_ge0 ?andTb//; last first.
    rewrite -expR0 ler_expR//.
  by rewrite expR_ge1Dx ?mulr_ge0// subr_ge0 -expR0 ler_expR.
rewrite expR_prod -mulr_suml.
move: t0; rewrite le_eqVlt => /predU1P[<-|t0].
  by rewrite expR0 subrr !mulr0.
rewrite ler_expR ler_pmul2r; last first.
  by rewrite subr_gt0 -expR0 ltr_expR.
rewrite /mu big_seq expectation_sum; last first.
  move=> Xi XiX; apply: integrable_bernoulli; exact: bX.1.
rewrite big_seq -sum_fine.
  by apply: ler_sum => Xi XiX; rewrite bernoulli_expectation //=; exact: bX.1.
move=> Xi XiX. rewrite bernoulli_expectation //=; exact: bX.1.
Qed.

Lemma expR_powR (x y : R) : (expR (x * y) = (expR x) `^ y)%R.
Proof. by rewrite /powR gt_eqF ?expR_gt0// expRK mulrC. Qed.

Lemma end_thm24 (X_ : seq {RV P >-> R}) n (t delta : R) :
  is_bernoulli_trial X_ n ->
  (0 < delta)%R ->
  let X := @bernoulli_trial X_ in
  let mu := 'E_P[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> bX d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite mulr_ge0// expR_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpmul2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expR_powR lnK// posrE addr_gt0.
Qed.

(* theorem 2.4 *)
Theorem thm24 (X_ : seq {RV P >-> R}) n (delta : R) :
  is_bernoulli_trial X_ n ->
  (0 < delta)%R ->
  let X := @bernoulli_trial X_ in
  let mu := 'E_P[X] in
  P [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => bX delta0.
set X := @bernoulli_trial X_.
set mu := 'E_P[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltr_addl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expR (fine mu * (expR t - 1)))%:E *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  by apply: (lm23 _ bX); rewrite le_eqVlt t0 orbT.
rewrite mulrC expR_powR -mulNr mulrA expR_powR.
exact: (end_thm24 _ bX).
Qed.

(* theorem 2.5 *)
Theorem poisson_ineq (X : seq {RV P >-> R}) (delta : R) n :
  is_bernoulli_trial X n ->
  let X' := @bernoulli_trial X in
  let mu := 'E_P[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  P [set i | X' i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> bX X' mu n0 /andP[delta0 delta1].
apply: (@le_trans _ _ (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expR_powR expRB (mulrC _ (ln _)) expR_powR lnK; last rewrite posrE addr_gt0//.
  apply: (thm24 bX) => //.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpmul2r//.
    by rewrite fine_ge0//; apply: expectation_ge0 => t; exact: (bernoulli_trial_ge0 bX).
  rewrite ler_sub//.
  exact: taylor_ln_le.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

(* TODO: move *)
Lemma ln_div : {in Num.pos &, {morph ln (R:=R) : x y / (x / y)%R >-> (x - y)%R}}.
Proof.
by move=> x y; rewrite !posrE => x0 y0; rewrite lnM ?posrE ?invr_gt0// lnV ?posrE.
Qed.

Lemma norm_expR : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

Theorem thm26 (X : seq {RV P >-> R}) (delta : R) n :
  is_bernoulli_trial X n -> (0 < delta < 1)%R ->
  let X' := @bernoulli_trial X : {RV P >-> R} in
  let mu := 'E_P[X'] in
  P [set i | X' i <= (1 - delta) * fine mu]%R <= (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> bX /andP[delta0 delta1] /=.
set X' := @bernoulli_trial X : {RV P >-> R}.
set mu := 'E_P[X'].
apply: (@le_trans _ _ (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    P [set i | (X' i <= (1 - delta) * fine mu)%R] = P [set i | `|(expR \o t \o* X') i|%:E >= (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltr_oppr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltr_subl_addr ltr_addl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ (((fine 'E_P[normr \o expR \o t \o* X']) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite EFinM lee_pdivl_mulr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ P (expR \o t \o* X' : {RV P >-> R}) id (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - apply: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_P[expR \o t \o* X'] = mmt_gen_fun X' t by [].
      by rewrite (binomial_mmt_gen_fun _ bX).
  apply: (@le_trans _ _ (((expR ((expR t - 1) * fine mu)) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite norm_expR lee_fin ler_wpmul2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_P[expR \o t \o* X'] = mmt_gen_fun X' t by [].
    rewrite (binomial_mmt_gen_fun _ bX)/=.
    rewrite /mu /X' (expectation_bernoulli_trial bX)/=.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expR_powR powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      by rewrite addr_ge0 ?mulr_ge0// subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expR_powR.
    rewrite addrCA -{2}(mulr1 (p%:num)) -mulrBr addrAC subrr sub0r mulrC mulNr.
    rewrite expR_ge1Dx//.
    (* 0 <= - (delta * p%:num) ?! *)
    admit. (* alessandro: we maybe already dealt with something similar *)
  rewrite !lnK ?posrE ?subr_gt0//.
  rewrite -addrAC subrr sub0r -mulrA [X in (_ / X)%R]expR_powR lnK ?posrE ?subr_gt0//.
  rewrite -[in leRHS]powR_inv1 ?powR_ge0// powRM// ?expR_ge0 ?invr_ge0 ?powR_ge0//.
  by rewrite powRAC powR_inv1 ?powR_ge0// powRrM expR_powR.
rewrite lee_fin.
rewrite -mulrN -mulrA [in leRHS]mulrC expR_powR ge0_ler_powR// ?nnegrE.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- by rewrite expR_ge0.
- rewrite -ler_ln ?posrE ?divr_gt0 ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_div ?posrE ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK//.
  rewrite /powR (*TODO: lemma ln of powR*) gt_eqF ?subr_gt0// expRK.
  (* requires analytical argument: see p.66 of mu's book *)
  admit.
Admitted.

Lemma measurable_fun_le D (f g : T -> R) : d.-measurable D -> measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]%R).
Proof.
move=> mD mf mg.
under eq_set => x do rewrite -lee_fin.
apply: emeasurable_fun_le => //; apply: measurableT_comp => //.
Qed.

Corollary cor27 (X : seq {RV P >-> R}) (delta : R) n :
  is_bernoulli_trial X n -> (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (0 < p%:num)%R ->
  let X' := @bernoulli_trial X in
  let mu := 'E_P[X'] in
  P [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> bX delta01 n0 p0 /=.
set X' := @bernoulli_trial X.
set mu := 'E_P[X'].
under eq_set => x.
  rewrite ler_normr.
  rewrite ler_subr_addl opprD opprK -{1}(mul1r (fine mu)) -mulrDl.
  rewrite -ler_sub_addr -(ler_opp2 (- _)%R) opprK opprB.
  rewrite -{2}(mul1r (fine mu)) -mulrBl.
  rewrite -!lee_fin.
  over.
rewrite /=.
rewrite set_orb.
rewrite measureU; last 3 first.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply: measurableT_comp => //.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply: measurableT_comp => //.
- rewrite disjoints_subset => x /=.
  rewrite /mem /in_mem/= => X0; apply/negP.
  rewrite -ltNge.
  apply: (@lt_le_trans _ _ _ _ _ _ X0).
  rewrite !EFinM.
  rewrite lte_pmul2r//.
    move: delta01 => /andP[d0 d1]; rewrite lte_fin ltr_add2l gt0_cp//.
  by rewrite fineK /mu/X' (expectation_bernoulli_trial bX)// lte_fin  mulr_gt0 ?ltr0n.
rewrite mulr2n EFinD lee_add//=.
- apply: (poisson_ineq bX) => //.
- apply: (le_trans (thm26 bX delta01)).
  rewrite lee_fin ler_expR !mulNr ler_opp2.
  rewrite ler_pmul//; last by rewrite lef_pinv ?posrE ?ler_nat.
  move: delta01 => /andP [delta0 delta1].
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  rewrite /X' lee_fin; apply: (bernoulli_trial_ge0 bX).
Qed.

(* TODO: formalize https://math.uchicago.edu/~may/REU2019/REUPapers/Rajani.pdf *)
Theorem sampling (X : seq {RV P >-> R}) (theta delta : R) :
  let n := size X in
  let X_sum := bernoulli_trial X in
  let X' x := (X_sum x) / n%:R in
  (0 < p%:num)%R ->
  is_bernoulli_trial X n ->
  (0 < delta <= 1)%R -> (0 < theta)%R -> (0 < n)%nat ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  P [set i | `| X' i - p%:num | <= theta]%R >= 1 - delta%:E.
Proof.
move=> n X_sum X' p0 bX /andP[delta0 delta1] theta0 n0 tdn.
have E_X_sum: 'E_P[X_sum] = (p%:num * n%:R)%:E.
  rewrite expectation_sum/=; last first.
    by move=> Xi XiX; exact: integrable_bernoulli (bX.1 Xi XiX).
  rewrite big_seq.
  under eq_bigr.
    move=> Xi XiX; rewrite (bernoulli_expectation (bX.1 _ XiX)); over.
  rewrite /= sumEFin big_const_seq iter_addr_0/= mulr_natr; congr ((_ *+ _)%:E).
  by rewrite /n -count_predT; apply: eq_in_count => x ->.
set epsilon := theta / p%:num.
have epsilon01 : (0 < epsilon < 1)%R.
  apply/andP; split.
    by rewrite /epsilon divr_gt0.
  rewrite /epsilon.
  rewrite ltr_pdivr_mulr// mul1r.
  (* theta < p ?! *)
  admit.
have thetaE : theta = (epsilon * p%:num)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : P [set i | `| X' i - p%:num | >= epsilon * p%:num]%R <=
    ((expR (- (p%:num * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in P X <= _](_ : _ =
      [set i | `| X_sum i - p%:num * n%:R | >= epsilon * p%:num * n%:R]%R); last first.
    apply/seteqP; split => [t|t]/=.
      move/(@ler_wpmul2r _ n%:R (ler0n _ _)) => /le_trans; apply.
      rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R)// -normrM mulrBl.
      by rewrite -mulrA mulVf ?mulr1// gt_eqF ?ltr0n.
    move/(@ler_wpmul2r _ n%:R^-1); rewrite invr_ge0// ler0n => /(_ erefl).
    rewrite -(mulrA _ _ n%:R^-1) divff ?mulr1 ?gt_eqF ?ltr0n//.
    move=> /le_trans; apply.
    rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R^-1)// -normrM mulrBl.
    by rewrite -mulrA divff ?mulr1// gt_eqF// ltr0n.
  rewrite -mulrA.
  have -> : (p%:num * n%:R)%R = fine (p%:num * n%:R)%:E by [].
  rewrite -E_X_sum.
  apply: (@cor27 X epsilon _ bX) => //.
have step2 : P [set i | `| X' i - p%:num | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wmuln2r// ler_expR mulNr ler_oppl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA -[in leLHS]mulrA ler_wpmul2l//.
  rewrite (mulrC epsilon) exprMn -mulrA ler_wpmul2r//.
    by rewrite divr_ge0// sqr_ge0.
  by rewrite expr2 ler_pimull.
suff : delta%:E >= P [set i | (`|X' i - p%:num| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in P X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p%:num| < theta)%R]); last first.
    apply/seteqP; split => [t|t]/=.
      by rewrite leNgt => /negP.
    by rewrite ltNge => /negP/negPn.
  have ? : measurable [set i | (`|X' i - p%:num| < theta)%R].
    under eq_set => x do rewrite -lte_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_lt => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  rewrite probability_setC// lee_subel_addr//.
  rewrite -lee_subel_addl//; last by rewrite fin_num_measure.
  move=> /le_trans; apply.
  rewrite le_measure ?inE//.
    under eq_set => x do rewrite -lee_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_le => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  by move=> t/= /ltW.
(* NB: last step in the pdf *)
apply: (le_trans step2).
rewrite lee_fin -(mulr_natr _ 2) -ler_pdivl_mulr//.
rewrite -(@lnK _ (delta / 2)); last by rewrite posrE divr_gt0.
rewrite ler_expR mulNr ler_oppl -lnV; last by rewrite posrE divr_gt0.
rewrite invf_div ler_pdivl_mulr// mulrC.
rewrite -ler_pdivr_mulr; last by rewrite exprn_gt0.
by rewrite mulrAC.
Admitted.

End bernoulli.
