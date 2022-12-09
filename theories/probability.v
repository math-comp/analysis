(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets signed functions topology normedtype cardinality.
Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.

(******************************************************************************)
(*                              Probability                                   *)
(*                                                                            *)
(* This file provides basic notions of probability theory.                    *)
(*                                                                            *)
(*               convn R == the type of sequence f : R^nat s.t.               *)
(*                          \sum_(n <oo) (f n)%:E = 1                         *)
(*       probability T R == a measure that sums to 1                          *)
(*          {RV P >-> R} == real random variable: a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*                f `o X == composition of a measurable function and a R.V.   *)
(*               X `^+ n := (fun x => x ^+ n) `o X                            *)
(*        X `+ Y, X `- Y == addition, subtraction of R.V.                     *)
(*              k `\o* X := k \o* X                                           *)
(*                  'E X == expectation of of the real random variable X      *)
(* square_integrable D f := mu.-integrable D (fun x => (`|f x| ^+ 2)%:E)      *)
(*                  'V X == variance of the real random variable X            *)
(*        distribution X == measure image of P by X : {RV P -> R}             *)
(*         {dRV P >-> R} == discrete real random variable                     *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "f `o X" (at level 50, format "f  `o '/ '  X").
Reserved Notation "X '`^+' n" (at level 11).
Reserved Notation "X `+ Y" (at level 50).
Reserved Notation "X `- Y" (at level 50).
Reserved Notation "X `* Y" (at level 49).
Reserved Notation "k `\o* X" (at level 49).
Reserved Notation "''E' X" (format "''E'  X", at level 5).
Reserved Notation "''V' X" (format "''V'  X", at level 5).
Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record isConvn (R : realType) (f : nat -> R) of IsNonNegFun nat R f :=
  { convn1 : (\sum_(n <oo) (f n)%:E = 1)%E }.

#[short(type=convn)]
HB.structure Definition Convn (R : realType) :=
  { f of isConvn R f & IsNonNegFun nat R f }.

HB.mixin Record isProbability d (T : measurableType d)
  (R : realType) (P : set T -> \bar R) of isMeasure d R T P :=
  {  probability_setT : P setT = 1%E }.

#[short(type=probability)]
HB.structure Definition Probability d (T : measurableType d) (R : realType) :=
  {P of isProbability d T R P & isMeasure d R T P }.

Section probability_lemmas.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability0 : P set0 = 0%E. Proof. exact: measure0. Qed.

Lemma probability_not_empty : [set: T] !=set0.
Proof.
apply/set0P/negP => /eqP setT0; have := probability0.
by rewrite -setT0 probability_setT; apply/eqP; rewrite oner_neq0.
Qed.

Lemma probability_ge0 (A : set T) : (0 <= P A)%E.
Proof. exact: measure_ge0. Qed.

Lemma probability_le1 (A : set T) : measurable A -> (P A <= 1)%E.
Proof.
move=> mA; rewrite -(@probability_setT _ _ _ P).
by apply: le_measure => //; rewrite ?in_setE.
Qed.

Lemma probability_fin (A : set T) : measurable A -> (P A \is a fin_num).
Proof.
move=> mA; apply/fin_real/andP; split.
  by apply: lt_le_trans; [|exact: probability_ge0].
  by apply: le_lt_trans; [exact: probability_le1|exact: ltry].
Qed.

Lemma probability_integrable_cst k : P.-integrable [set: T] (EFin \o cst k).
Proof.
split; first exact/EFin_measurable_fun/measurable_fun_cst.
have [k0|k0] := leP 0 k.
- rewrite (eq_integral (EFin \o cst_mfun k))//; last first.
    by move=> x _ /=; rewrite ger0_norm.
  by rewrite /= integral_cst//= probability_setT mule1 ltey.
- rewrite (eq_integral (EFin \o cst_mfun (- k)))//; last first.
    by move=> x _ /=; rewrite ltr0_norm.
  by rewrite /= integral_cst//= probability_setT mule1 ltey.
Qed.

End probability_lemmas.

(* equip some functions with the measurable_fun interface to define R.V. *)
Section mfun.
Variable R : realType.

Definition mexp n : R -> R := @GRing.exp R ^~ n.

Let measurable_fun_mexp n : measurable_fun setT (mexp n).
Proof. exact/measurable_fun_exprn/measurable_fun_id. Qed.

HB.instance Definition _ (n : nat) := @IsMeasurableFun.Build _ _ R
  (mexp n) (measurable_fun_mexp n).

Definition subr m : R -> R := fun x => x - m.

Lemma subr_mfun_subproof m : @IsMeasurableFun _ _ R (subr m).
Proof.
split => _; apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; apply: measurableI => //.
rewrite (_ : _ @^-1` _ = `](x + m),+oo[)%classic; first exact: measurable_itv.
by apply/seteqP; split => r;
  rewrite preimage_itv in_itv/= in_itv/= !andbT ltr_subr_addr.
Qed.
HB.instance Definition _ m := subr_mfun_subproof m.
Definition subr_mfun m := [the {mfun _ >-> R} of subr m].

Definition mid : R -> R := id.

Lemma measurable_fun_mid : measurable_fun setT (mid).
Proof. exact: measurable_fun_id. Qed.

HB.instance Definition _ := @IsMeasurableFun.Build _ _ R
  (mid) (measurable_fun_mid).

Definition mabs : R -> R := fun x => `| x |.

Lemma measurable_fun_mabs : measurable_fun setT (mabs).
Proof. exact: measurable_fun_normr. Qed.

HB.instance Definition _ := @IsMeasurableFun.Build _ _ R
  (mabs) (measurable_fun_mabs).

Let measurable_fun_mmul d (T : measurableType d) (f g : {mfun T >-> R}) :
  measurable_fun setT (f \* g).
Proof. exact/measurable_funM. Qed.

HB.instance Definition _ d (T : measurableType d) (f g : {mfun T >-> R}) :=
  @IsMeasurableFun.Build _ _ R (f \* g) (measurable_fun_mmul f g).

End mfun.

Section comp_mfun.
Variables (d : _) (T : measurableType d) (R : realType)
  (f : {mfun Real_sort__canonical__measure_Measurable R >-> R})
  (g : {mfun T >-> R}).

Lemma comp_mfun_subproof : @IsMeasurableFun _ _ _ (f \o g).
Proof. by split; exact: measurable_fun_comp. Qed.
HB.instance Definition _ := comp_mfun_subproof.
Definition comp_mfun := [the {mfun _ >-> R} of (f \o g)].
End comp_mfun.

Definition random_variable (d : _) (T : measurableType d) (R : realType)
  (P : probability T R) := {mfun T >-> R}.

Notation "{ 'RV' P >-> R }" := (@random_variable _ _ R P) : form_scope.

Section random_variables.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Definition comp_RV (f : {mfun _ >-> R}) (X : {RV P >-> R}) : {RV P >-> R} :=
  [the {RV P >-> R} of f \o X].

Local Notation "f `o X" := (comp_RV f X).

Definition exp_RV (X : {RV P >-> R}) n : {RV P >-> R} :=
  [the {mfun _ >-> R} of @mexp R n] `o X.

Definition add_RV (X Y : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of X + Y].

Definition sub_RV (X Y : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of X - Y].

Definition scale_RV k (X : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of k \o* X].

Definition mul_RV (X Y : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of (X \* Y)].

End random_variables.
Notation "f `o X" := (comp_RV f X).
Notation "X '`^+' n" := (exp_RV X n).
Notation "X `+ Y" := (add_RV X Y).
Notation "X `- Y" := (sub_RV X Y).
Notation "X `* Y" := (mul_RV X Y).
Notation "k `\o* X" := (scale_RV k X).

Section expectation.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Definition expectation (X : {RV P >-> R}) := \int[P]_w (X w)%:E.
End expectation.
Notation "''E' X" := (expectation X).

(* TODO: wip *)
Section integrable_pred.
Context {d : _ } {T : measurableType d} {R : realType} (mu : {measure set T -> \bar R}).
Definition ifun : {pred T -> \bar R} := mem [set f | `[< mu.-integrable setT f >]].
(* NB: avoid Prop to define integrable? *)
Definition ifun_key : pred_key ifun. Proof. exact. Qed.
Canonical ifun_keyed := KeyedPred ifun_key.
End integrable_pred.

Section expectation_lemmas.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_cst r : 'E (cst_mfun r : {RV P >-> R}) = r%:E.
Proof. by rewrite /expectation /= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) :
  'E (indic_mfun A mA : {RV P >-> R}) = P A.
Proof. by rewrite /expectation integral_indic// setIT. Qed.

Variables (X : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X)).

Lemma integrable_expectation : `| 'E X | < +oo.
Proof.
move: iX => [? Xoo]; rewrite (le_lt_trans _ Xoo)//.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (k : R) : 'E (k `\o* X) = k%:E * 'E X.
Proof.
rewrite /expectation.
under eq_integral do rewrite EFinM.
rewrite -integralM//.
by under eq_integral do rewrite muleC.
Qed.

Lemma expectation_ge0 : (forall x, 0 <= X x)%R -> 0 <= 'E X.
Proof.
by move=> ?; rewrite /expectation integral_ge0// => x _; rewrite lee_fin.
Qed.

Variables (Y : {RV P >-> R}) (iY : P.-integrable setT (EFin \o Y)).

Lemma expectation_le : (forall x, 0 <= X x)%R ->
  (forall x, X x <= Y x)%R -> ('E X <= 'E Y).
Proof.
  move => hXpos hXleY.
  rewrite /expectation ge0_le_integral => //.
    move => ? _; apply: hXpos.
    apply EFin_measurable_fun => //.
    move => x ?; apply: (le_trans (y:=X x)) => //; apply: hXleY.
    apply EFin_measurable_fun => //.
    move => x ?; apply: lee_tofin => //.
Qed.

Lemma expectationD : 'E (X `+ Y) = 'E X + 'E Y.
Proof. by rewrite /expectation integralD_EFin. Qed.

Lemma expectationB : 'E (X `- Y) = 'E X - 'E Y.
Proof. by rewrite /expectation integralB_EFin. Qed.

End expectation_lemmas.

Section square_integrable.
Variables (d : _) (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition square_integrable (D : set T) (f : T -> R) :=
  mu.-integrable D (EFin \o (fun x => `|f x| ^+ 2)).

End square_integrable.

Section variance.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : {RV P >-> R}) :=
  'E ((X `- cst_mfun (fine 'E X)) `^+ 2).
Local Notation "''V' X" := (variance X).

Lemma varianceE (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> square_integrable P setT X ->
  'V X = 'E (X `^+ 2) - ('E X) ^+ 2.
Proof.
move=> iX siX.
rewrite /variance (_ : _ `^+ 2 = X `^+ 2 `- (2 * fine 'E X) `\o* X
    `+ fine ('E X ^+ 2) `\o* cst_mfun 1); last first.
  apply/mfuneqP => x /=; rewrite /mexp /subr/= sqrrB -[RHS]/(_ - _ + _)%R /=.
  congr (_ - _ +  _)%R.
    by rewrite mulr_natl -mulrnAr mulrC.
  rewrite -[RHS]/(_ * _)%R mul1r.
  have [Efin|] := boolP ('E X \is a fin_num); first by rewrite fineM.
  by rewrite fin_numElt -(lte_absl ('E X) +oo) (integrable_expectation iX).
have ? : P.-integrable [set: T] (EFin \o X `^+ 2).
  rewrite (_ : EFin \o X `^+ 2 = (fun x => (`| X x | ^+ 2)%:E))//.
  by rewrite funeqE => p /=; rewrite real_normK// num_real.
rewrite expectationD; last 2 first.
  - rewrite (_ : _ \o _ =
      (fun x => (EFin \o (X `^+ 2)) x - (EFin \o (2 * fine 'E X `\o* X)) x)) //.
    apply: integrableB => //.
    apply: (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E)) => //.
      by move=> t _ /=; rewrite muleC EFinM.
    exact: integrablerM.
  - apply: (eq_integrable _ (fun x => (fine ('E X ^+ 2))%:E * (cst_mfun 1 x)%:E)) => //.
      by move=> t _ /=; rewrite mul1r mule1.
    by apply: integrablerM => //; exact: probability_integrable_cst.
rewrite expectationB //; last first.
  apply: (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E)) => //.
    by move=> t _ /=; rewrite !EFinM [in RHS]muleC.
  exact: integrablerM.
rewrite expectationM// expectationM; last exact: probability_integrable_cst.
rewrite expectation_cst mule1.
have ? : 'E X \is a fin_num.
  by rewrite fin_numElt -(lte_absl ('E X) +oo) integrable_expectation.
rewrite EFinM fineK// expe2 fineM// EFinM fineK//.
rewrite -muleA mule_natl mule2n oppeD ?fin_numM//.
by rewrite addeA subeK// fin_numM.
Qed.

End variance.
Notation "''V' X" := (variance X).

Section distribution.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R)
          (X : {mfun T >-> R}).

Definition distribution := pushforward P (@measurable_funP _ _ _ X).

Lemma distribution_is_probability : distribution [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ :=
  isProbability.Build _ _ R distribution distribution_is_probability.

End distribution.

Section transfer_probability.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma integral_distribution (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite integral_pushforward. Qed.

End transfer_probability.

HB.mixin Record isDiscreteRV (d : _) (T : measurableType d) (R : realType)
    (P : probability T R) (X : T -> R) of @MeasurableFun d T R X := {
  weight : convn R ;
  values : {injfun [set: nat] >-> [set: R]} ;
  values_cover : forall t, exists n, X t = values n ;
  distributionE : distribution P [the {mfun T >-> R} of X] =1
    (fun A : set R => \sum_(n <oo) (weight n)%:E * \d_ (values n) A)%E
}.

#[short(type=discrete_random_variable)]
HB.structure Definition DiscreteRV (d : _)
  (T : measurableType d) (R : realType) (P : probability T R) := {
  X of IsMeasurableFun d T R X & isDiscreteRV d T R P X
}.

Arguments weight {d T R P} s.
Arguments values {d T R P} s.
Arguments values_cover {d T R P} _ t.

Notation "{ 'dRV' P >-> R }" := (@discrete_random_variable _ _ R P) : form_scope.

Module DiscreteDistribution.
Section discrete_distribution.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R)
  (X : {dRV P >-> R}).

Lemma probability_distribution r :
  P [set x | (X : {RV P >-> R}) x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma distribution_values (n : nat) :
  distribution P X [set values X n] = (weight X n)%:E.
Proof.
rewrite (@distributionE _ _ _ _ X) nneseries_esum; last first.
  by move=> m _; rewrite mule_ge0// lee_fin.
rewrite (esumID [set n]); last first.
  by move=> m _; rewrite mule_ge0// lee_fin.
rewrite addeC esum1 ?add0e; last first.
  move=> m [_ /= mn].
  rewrite /dirac indicE memNset ?mule0//=.
  by apply: contra_not mn; exact/injT.
rewrite (_ : _ `&` _ = [set n]); last exact/seteqP.
rewrite esum_set1.
  by rewrite /= /dirac indicE mem_set// mule1.
by rewrite mule_ge0// lee_fin.
Qed.

Lemma dRV_expectation : P.-integrable setT (EFin \o (X : {RV P >-> R})) ->
  'E (X : {RV P >-> R}) = (\sum_(n <oo) (weight X n)%:E * (values X n)%:E)%E.
Proof.
move=> ix.
rewrite /expectation.
rewrite -[in LHS](_ : \bigcup_k (X : {RV P >-> R}) @^-1` [set values X k] = setT); last first.
  apply/seteqP; split => // t _.
  by have [n XAtn] := values_cover X t; exists n.
have tA : trivIset setT (fun k => [set values X k]).
  by move=> i j _ _ [/= r []] ->; exact/injT.
have tXA : trivIset setT (fun k => (X : {RV P >-> R}) @^-1` [set values X k]).
  apply/trivIsetP => /= i j _ _ ij.
  move/trivIsetP : tA => /(_ i j Logic.I Logic.I ij) Aij.
  by rewrite -preimage_setI Aij preimage_set0.
rewrite integral_bigcup//; last first.
  by apply: (integrableS measurableT) => //; exact: bigcup_measurable.
transitivity (\sum_(i <oo) \int[P]_(x in (X : {RV P >-> R}) @^-1` [set values X i])
               (values X i)%:E)%E.
  by apply eq_eseries => i _; apply eq_integral => t; rewrite in_setE/= => ->.
transitivity (\sum_(i <oo) (values X i)%:E *
                \int[P]_(x in (X : {RV P >-> R}) @^-1` [set values X i]) 1)%E.
  apply eq_eseries => i _; rewrite -integralM//; last first.
    split; first exact: measurable_fun_cst.
    rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
    rewrite integral_cst// mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
    exact: probability_le1.
  by apply eq_integral => y _; rewrite mule1.
apply eq_eseries => k _.
by rewrite integral_cst//= mul1e probability_distribution distribution_values muleC.
Qed.

End discrete_distribution.

(* NB: available in lebesgue-stieltjes PR *)
Section from_lebesgue_stieltjes.
Definition EFinf {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma nondecreasing_EFinf (R : realDomainType) (f : R -> R) :
  {homo f : x y / (x <= y)%R} -> {homo EFinf f : x y / (x <= y)%E}.
Proof.
move=> ndf.
by move=> [r| |] [l| |]//=; rewrite ?leey ?leNye// !lee_fin; exact: ndf.
Qed.

Lemma nondecreasing_EFinf' (R : realDomainType) (f : R -> R) {D : set R} :
  {in D &, {homo f : x y / (x <= y)%R}} -> {in (@EFin R) @` D &, {homo EFinf f : x y / (x <= y)%E}}.
Proof.
move=> ndf [r| |] [l| |] rD lD //= rl; rewrite ?leey ?leNye// lee_fin ndf //.
  by move: rD; rewrite inE /= => -[] x /mem_set ? [] <-.
by move: lD; rewrite inE /= => -[] x /mem_set ? [] <-.
Qed.
End from_lebesgue_stieltjes.

Section markov_chebyshev.

Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma mul_cst (k : R) (X : {RV P >-> R})
  : k `\o* X = (cst_mfun k) `* X.
Proof.
  rewrite /scale_RV /mul_RV.
  apply /mfuneqP => x /=.
  exact: mulrC.
Qed.

Lemma markov (X : {RV P >-> R}) (f : {mfun R >-> R}) (eps : R) :
  0 < eps -> (forall r : R, 0 <= f r) -> {in `[0, +oo[%classic &, {homo f : x y / x <= y}} ->
 ((f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ]%E <=
  'E ([the {mfun _ >-> R} of f \o @mabs R] `o X))%E.
Proof.
move=> e0 f0 f_nd.
rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse d T R P setT measurableT (EFin \o X) eps
  (EFinf f) _ _ _ _ e0)) => //=.
- rewrite (_ : EFinf _ = fun x => if x \is a fin_num then (f (fine x))%:E else x); last first.
    by apply: funext=> -[].
  apply: measurable_fun_ifT => /=.
  + apply: (measurable_fun_bool true).
    rewrite /preimage/= -[X in measurable X]setTI.
    by apply/emeasurable_fin_num => //; exact: measurable_fun_id.
  + apply/EFin_measurable_fun/measurable_fun_comp => //.
    exact/measurable_fun_fine.
  + exact: measurable_fun_id.
- by case => //= r _; exact: f0.
- move=> x y.
  rewrite !inE/= !in_itv/= !andbT.
  move: x y => [x| |] [y| |] x0 y0 xy//=.
  by rewrite lee_fin f_nd// inE /= in_itv/= andbT -lee_fin.
  by rewrite leey.
- exact/EFin_measurable_fun.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : 0 < eps ->
  (P [set x | (eps <= `| X x - fine ('E X)|)%R ] <= (eps ^- 2)%:E * 'V X)%E.
Proof.
move => heps.
have [hv|hv] := eqVneq ('V X)%E (+oo)%E.
  by rewrite hv mulr_infty gtr0_sg; [rewrite mul1e; apply: leey |rewrite invr_gt0// exprn_gt0].
have h (Y : {RV P >-> R}) : (P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E (Y `^+ 2))%E.
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  have : {in `[0, +oo[%classic &, {homo mexp 2 : x y / x <= y :> R}}.
    by move=> x y; rewrite !inE !mksetE !in_itv/= !andbT => x0 y0; rewrite /mexp ler_sqr.
  move=> /(@markov Y [the {mfun _ >-> R} of @mexp R 2] _ heps (@sqr_ge0 _)) /=.
  move=> /le_trans; apply => /=.
  apply: expectation_le => //=.
  - by move=> x; rewrite /mexp /mabs sqr_ge0.
  - by move=> x; rewrite /mexp /mexp /mabs real_normK// num_real.
have := h [the {RV P >-> R} of X `- cst_mfun (fine ('E X))].
by move=> /le_trans; apply; rewrite lee_pmul2l// lte_fin invr_gt0 exprn_gt0.
Qed.

End markov_chebyshev.

Section cvg_random_variable.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Definition probabilistic_cvg (X : {RV P >-> R}^nat) (Y : {RV P >-> R})
  := forall a : {posnum R}, [sequence (fine \o P) [set x | a%:num <= `| X n x - Y x | ] ]_n --> (0%R:R).

Definition norm1 (X : {RV P >-> R})
  := fine ('E ((@mabs R) `o X)).

Lemma prop_23_1 (X : {RV P >-> R}^nat) (Y : {RV P >-> R})
  : (norm1 (X n `- Y) @[n --> \oo]--> (0:R)%R) -> probabilistic_cvg X Y.
Proof.
rewrite /norm1.
move => h a /=.
apply/(@cvg_distP _ [pseudoMetricNormedZmodType R of R^o]).
move => eps heps.
rewrite near_map /=.
move /(@cvgr0Pnorm_lt _ [pseudoMetricNormedZmodType R of R^o]) : h.
have a0: 0 < a%:num by [].
move /(_ (a%:num) a0) => h1.
case: h1 => m _ h1 .
near=> n.
rewrite sub0r.
rewrite normrN.
rewrite ger0_norm; last first.
  apply: fine_ge0; apply: probability_ge0.
change eps with (fine eps%:E).
rewrite fine_lt => //; first apply probability_fin.
  admit.
(* have -> : P [set x | (a%:num <= `|X n x - Y x|)%R] = 0%E.
  have mn : (m <= n)%N.
  near: n.
  exists m => //.
  have := h1 _ mn.
  unfold norm1.
  rewrite /=.
  have := (@markov _ T R P (X n - Y) [the {mfun R >-> R} of (@mid R)] (a%:num) a0).
  move => /=. *)
  (* apply: le_lt_trans. *)
  (* move: x.
  near: n.
  by [].
  have := h x.
  move => [m] _.
  have mn : (m <= n)%N.
  move /(_ m) => /=.
  move /(_ (leqnn m)).
  rewrite normr_id.
  rewrite ltNge. *)
  (* admit.
apply: le_lt_trans.
  rewrite le_eqVlt.
  apply /orP. left.
  apply /eqP.
  apply probability0.
apply heps. *)
Abort.

End cvg_random_variable.

End DiscreteDistribution.
