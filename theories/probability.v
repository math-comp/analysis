(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
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
(*                f `o X == composition of a measurable function and a R.V.   *)
(*               X `^+ n := (fun x => x ^+ n) `o X                            *)
(*        X `+ Y, X `- Y == addition, subtraction of R.V.                     *)
(*              k `\o* X := k \o* X                                           *)
(*                  'E X == expectation of of the real random variable X      *)
(*          mu.-Lspace p := [set f : T -> R | measurable_fun setT f /\        *)
(*                            \int[mu]_(x in D) (`|f x| ^+ p)%:E < +oo]       *)
(*                  'V X == variance of the real random variable X            *)
(*        distribution X == measure image of P by X : {RV P -> R}, declared   *)
(*                          as a probability measure                          *)
(*         {dRV P >-> R} == real-valued discrete random variable              *)
(*             dRV_dom X == domain of the random variable X                   *)
(*          enum_range X == bijection between the domain and the range of X   *)
(*         enum_prob X k == probability of the kth value in the range of X    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").
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

(******************************************************************************)
(* PR in progress/move                                                        *)
(******************************************************************************)

(* TODO: PR in progress *)
Lemma countable_bijP T (A : set T) :
  reflect (exists B : set nat, (A #= B)%card) (countable A).
Proof.
apply: (iffP idP); last by move=> [B] /eq_countable ->.
move=> /pcard_leP[f]; exists (f @` A).
by apply/pcard_eqP; squash [fun f in A].
Qed.

Lemma patchE aT (rT : pointedType) (f : aT -> rT) (B : set aT) x :
  (f \_ B) x = if x \in B then f x else point.
Proof. by []. Qed.

Lemma preimage_range T1 T2 (f : T1 -> T2) : f @^-1` range f = setT.
Proof. by apply/seteqP; split => // t _; exists t. Qed.

(* NB: available in lebesgue-stieltjes PR as EFinf *)
Definition funEFin {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma expeS (R : numDomainType) (x : \bar R) n : (x ^+ n.+1 = x * x ^+ n)%E.
Proof. by case: n => //=; rewrite mule1. Qed.

Lemma fin_numX (R : numDomainType) (x : \bar R) n :
  (x \is a fin_num -> x ^+ n \is a fin_num)%E.
Proof. by elim: n x => // n ih x finx; rewrite expeS fin_numM// ih. Qed.

(******************************************************************************)
(* PR in progress/move                                                        *)
(******************************************************************************)

HB.mixin Record isConvn (R : realType) (f : nat -> R) of isNonNegFun nat R f :=
  { convn1 : (\sum_(n <oo) (f n)%:E = 1)%E }.

#[short(type=convn)]
HB.structure Definition Convn (R : realType) :=
  { f of isConvn R f & isNonNegFun nat R f }.

Section probability_lemmas.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_fin_num (A : set T) : measurable A -> P A \is a fin_num.
Proof.
move=> mA; apply/fin_real; rewrite (lt_le_trans _ (measure_ge0 _ _))//=.
by rewrite (le_lt_trans (probability_le1 _ _))// ltry.
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

(* equip functions with the isMeasurableFun interface to define R.V. *)
Section mfun.
Variable R : realType.

Definition mexp n : R -> R := @GRing.exp R ^~ n.

Let measurable_fun_mexp n : measurable_fun setT (mexp n).
Proof. exact/measurable_fun_exprn/measurable_fun_id. Qed.

HB.instance Definition _ (n : nat) := @isMeasurableFun.Build _ _ R
  (mexp n) (measurable_fun_mexp n).

Definition subr m : R -> R := fun x => x - m.

Let measurable_fun_subr m : measurable_fun setT (subr m).
Proof.
apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; apply: measurableI => //.
rewrite (_ : _ @^-1` _ = `](x + m),+oo[)%classic; first exact: measurable_itv.
by apply/seteqP; split => r;
  rewrite preimage_itv in_itv/= in_itv/= !andbT ltr_subr_addr.
Qed.

HB.instance Definition _ m := @isMeasurableFun.Build _ _ R
  (subr m) (measurable_fun_subr m).

Definition mabs : R -> R := fun x => `| x |.

Let measurable_fun_mabs : measurable_fun setT (mabs).
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

Section random_variables.
Context d (T : measurableType d) (R : realType) (P : probability T R).

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

Lemma mul_cst d (T : measurableType d) (R : realType)
  (P : probability T R)(k : R) (X : {RV P >-> R}) : k `\o* X = (cst_mfun k) `* X.
Proof. by apply/mfuneqP => x /=; exact: mulrC. Qed.

Section expectation.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition expectation (X : {RV P >-> R}) := \int[P]_w (X w)%:E.
End expectation.
Notation "''E' X" := (expectation X).

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_cst r : 'E (cst_mfun r : {RV P >-> R}) = r%:E.
Proof. by rewrite /expectation /= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) :
  'E (indic_mfun A mA : {RV P >-> R}) = P A.
Proof. by rewrite /expectation integral_indic// setIT. Qed.

Lemma integrable_expectation (X : {RV P >-> R})
  (iX : P.-integrable setT (EFin \o X)) : `| 'E X | < +oo.
Proof.
move: iX => [? Xoo]; rewrite (le_lt_trans _ Xoo)//.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (X : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
  (k : R) : 'E (k `\o* X) = k%:E * 'E X.
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

Lemma expectation_le (X Y : {RV P >-> R}) : (forall x, 0 <= X x)%R ->
  (forall x, X x <= Y x)%R -> 'E X <= 'E Y.
Proof.
move => X0 XY; rewrite /expectation ge0_le_integral => //.
- by move=> t _; apply: X0.
- by apply EFin_measurable_fun.
- by move=> t _; rewrite lee_fin (le_trans _ (XY _)).
- by apply EFin_measurable_fun.
- by move=> t _; rewrite lee_fin.
Qed.

Lemma expectationD (X Y : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
    (iY : P.-integrable setT (EFin \o Y)) : 'E (X `+ Y) = 'E X + 'E Y.
Proof. by rewrite /expectation integralD_EFin. Qed.

Lemma expectationB (X Y : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X))
    (iY : P.-integrable setT (EFin \o Y)) : 'E (X `- Y) = 'E X - 'E Y.
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
  'E ((X `- cst_mfun (fine 'E X)) `^+ 2).
Local Notation "''V' X" := (variance X).

Lemma varianceE (X : {RV P >-> R}) : P.-Lspace 1 X -> P.-Lspace 2 X ->
  'V X = 'E (X `^+ 2) - ('E X) ^+ 2.
Proof.
move=> X1 X2.
have ? : P.-integrable [set: T] (EFin \o X) by rewrite Lspace1 in X1.
have ? : P.-integrable [set: T] (EFin \o X `^+ 2)  by apply: Lspace2.
have ? : 'E X \is a fin_num by rewrite fin_num_abs// integrable_expectation.
rewrite /variance (_ : _ `^+ 2 = X `^+ 2 `- (2 * fine 'E X) `\o* X
    `+ fine ('E X ^+ 2) `\o* cst_mfun 1); last first.
  apply/mfuneqP => x /=; rewrite /mexp /subr/= sqrrB -[RHS]/(_ - _ + _)%R /=.
  by rewrite mulr_natl -mulrnAr mul1r fineM.
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
rewrite expectation_cst mule1 EFinM fineK// fineK ?fin_numX// -muleA -expe2.
by rewrite mule_natl mule2n oppeD ?fin_numX// addeA subeK// fin_numX.
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
Proof.
exact: (measure0
  [the measure _ _ of pushforward P (@measurable_funP _ _ _ X)]).
Qed.

Let distribution_ge0 A : (0 <= distribution P X A)%E.
Proof.
exact: (measure_ge0
  [the measure _ _ of pushforward P (@measurable_funP _ _ _ X)]).
Qed.

Let distribution_sigma_additive : semi_sigma_additive (distribution P X).
Proof.
exact: @measure_semi_sigma_additive _ _ _
  [the measure _ _ of pushforward P (@measurable_funP _ _ _ X)].
Qed.

HB.instance Definition _ := isMeasure.Build _ R _ (distribution P X)
  distribution0 distribution_ge0 distribution_sigma_additive.

Let distribution_is_probability : distribution P X [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ :=
  isProbability.Build _ _ R (distribution P X) distribution_is_probability.

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
    'E ([the {mfun _ >-> R} of f \o @mabs R] `o X).
Proof.
move=> e0 f0 f_nd.
rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse d T R P setT measurableT (EFin \o X)
  eps (funEFin f) _ _ _ _ e0)) => //=.
- rewrite (_ : funEFin _ =
    fun x => if x \is a fin_num then (f (fine x))%:E else x); last first.
    by apply: funext=> -[].
  apply: measurable_fun_ifT => /=.
  + apply: (@emeasurable_fun_bool _ _ _ _ true).
    rewrite /preimage/= -[X in measurable X]setTI.
    by apply/emeasurable_fin_num => //; exact: measurable_fun_id.
  + apply/EFin_measurable_fun/measurable_funT_comp => //.
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

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E X)|)%R ] <= (eps ^- 2)%:E * 'V X.
Proof.
move => heps.
have [hv|hv] := eqVneq ('V X)%E (+oo)%E.
  by rewrite hv mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E (Y `^+ 2).
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
have := h [the {RV P >-> R} of X `- cst_mfun (fine ('E X))].
by move=> /le_trans; apply; rewrite lee_pmul2l// lte_fin invr_gt0 exprn_gt0.
Qed.

End markov_chebyshev.

HB.mixin Record isDiscreteRV d (T : measurableType d) (R : realType)
    (P : probability T R) (X : T -> R) of @MeasurableFun d T R X := {
  countable_range : countable (range X)
}.

#[short(type=discrete_random_variable)]
HB.structure Definition DiscreteRV d (T : measurableType d) (R : realType)
    (P : probability T R) := {
  X of isMeasurableFun d T R X & isDiscreteRV d T R P X
}.

Notation "{ 'dRV' P >-> R }" :=
  (@discrete_random_variable _ _ R P) : form_scope.

Section dRV_definitions.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition dRV_dom_enum (X : {dRV P >-> R}) :
  { B : set nat & {splitbij B >-> range X}}.
have /countable_bijP/cid[B] := @countable_range _ _ _ P X.
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
  - rewrite preimage_setI; apply: measurableI => //; first exact: measurable_sfunP.
    by apply: measurable_sfunP; apply: bigcup_measurable.
  - apply: measurable_sfunP; apply: measurableI => //.
    by apply: measurableC; apply: bigcup_measurable.
  - rewrite 2!preimage_setI setIACA -!setIA -preimage_setI.
    by rewrite setICr preimage_set0 2!setI0.
rewrite [X in _ + X = _](_ : _ = 0) ?adde0; last first.
  rewrite (_ : _ @^-1` _ = set0) ?measure0//; apply/disjoints_subset => x AXx.
  rewrite setCK /bigcup /=; exists ((dRV_enum X)^-1 (X x))%function.
    exact: funS.
  by rewrite invK// inE.
rewrite setI_bigcupr; etransitivity; first exact: PXU.
rewrite eseries_mkcond; apply: eq_eseries => k _.
rewrite /enum_prob patchE; case: ifPn => nX; rewrite ?mul0e//.
rewrite diracE; have [kA|] := boolP (_ \in A).
  by rewrite mule1 setIidr// => _ /= ->; exact: set_mem.
rewrite notin_set => kA.
rewrite mule0 (disjoints_subset _ _).2 ?preimage_set0 ?measure0// => r + /= rE.
by rewrite rE.
Qed.

Lemma convn_enum_prob : (\sum_(n <oo) (enum_prob X) n = 1)%E.
Proof.
have := distribution_dRV measurableT.
rewrite probability_setT/= => /esym; apply: eq_trans.
rewrite [RHS]eseries_mkcond; apply: eq_eseries => k _.
by rewrite (*NB: PR in progress diracT*) diracE in_setT mule1.
Qed.

End distribution_dRV.

Section discrete_distribution.
Context d (T : measurableType d) (R : realType) (P : probability T R)
        (X : {dRV P >-> R}).

Lemma probability_distribution r :
  P [set x | (X : {RV P >-> R}) x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma dRV_expectation : P.-integrable setT (EFin \o (X : {RV P >-> R})) ->
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
  apply eq_eseries => i _; case: ifPn => iX.
    by apply eq_integral => t; rewrite in_setE/= => ->.
  by rewrite !integral_set0.
transitivity (\sum_(i <oo) (dRV_enum X i)%:E *
    \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
      1)%E.
  apply eq_eseries => i _; rewrite -integralM//; last 2 first.
    - by case: ifPn.
    - split; first exact: measurable_fun_cst.
      rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
      rewrite integral_cst//; last first.
        by case: ifPn.
      rewrite mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
      by case: ifPn => // _; exact: probability_le1.
  by apply eq_integral => y _; rewrite mule1.
apply: eq_eseries => k _; case: ifPn => kX.
  rewrite /= integral_cst//= mul1e probability_distribution muleC.
  by rewrite distribution_dRV_enum.
by rewrite integral_set0 mule0 /enum_prob patchE (negbTE kX) mul0e.
Qed.

Definition pmf (X : {dRV P >-> R}) (r : R) : R :=
  fine (P (X @^-1` [set r])).

Lemma expectation_pmf : P.-integrable setT (EFin \o (X : {RV P >-> R})) ->
  'E (X : {RV P >-> R}) =
  (\sum_(n <oo | n \in dRV_dom X) (pmf X (dRV_enum X n))%:E * (dRV_enum X n)%:E)%E.
Proof.
move=> iX; rewrite dRV_expectation// [in RHS]eseries_mkcond.
apply: eq_eseries => k _.
rewrite /enum_prob patchE; case: ifPn => kX; last by rewrite mul0e.
by rewrite /pmf fineK// probability_fin_num.
Qed.

End discrete_distribution.
