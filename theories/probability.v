(* -*- company-coq-local-symbols: (("\\int_" . ?∫) ("'d" . ?𝑑) ("\\d_" . ?δ)); -*- *)
(* intersection U+2229; union U+222A, set U+2205, delta U+03B4 *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets signed topology normedtype cardinality sequences.
Require Import esum measure lebesgue_measure lebesgue_integral functions numfun.

(******************************************************************************)
(*                             Probability (WIP)                              *)
(*                                                                            *)
(* This file provides a tentative definition of basic notions of probability  *)
(* theory.                                                                    *)
(*                                                                            *)
(*       probability T R == a measure that sums to 1                          *)
(*          {RV P >-> R} == real random variable, a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*                  'E X == expectation of of the real random variable X      *)
(*                  'V X == variance of the real random variable X            *)
(*        distribution X == measure image of P by X : {RV P -> R}             *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "''E' X" (format "''E'  X", at level 5).
Reserved Notation "''V' X" (format "''V'  X", at level 5).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

#[global] Hint Extern 0 (measurable_fun _ normr) =>
  solve [exact: measurable_fun_normr] : core.

Notation integrablerM := integrableK.

Section integrable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Lemma integrableMr (D : set T) : measurable D ->
  forall (k : R) (f : T -> \bar R), mu.-integrable D f ->
  mu.-integrable D (f \* cst k%:E)%E.
Proof.
move=> mD k f mf; apply: eq_integrable (integrablerM mD k mf) => //.
by move=> x _; rewrite muleC.
Qed.

Lemma eq_integrable (D : set T) : measurable D -> forall f2 f1 : T -> \bar R,
  {in D, f1 =1 f2} -> mu.-integrable D f1 = mu.-integrable D f2.
Proof.
move=> mD f2 f1 f12.
apply: propext; split; apply: eq_integrable => // x xD.
by rewrite f12.
Qed.

End integrable.
Arguments eq_integrable {T R mu D} _ f2 f1.

From mathcomp.finmap Require Import finmap.

Lemma integralM_indic (T : measurableType) (R : realType)
    (m : {measure set T -> \bar R}) (D : set T) (f : R -> set T) k :
  (k < 0 -> f k = set0) ->
  measurable (f k) ->
  measurable D ->
  (\int[m]_(x in D) (k * \1_(f k) x)%:E =
   k%:E * \int[m]_(x in D) (\1_(f k) x)%:E)%E.
Proof.
move=> fk0 mfk mD; have [k0|k0] := ltP k 0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    move=> x _.
    by rewrite fk0// indic0 mulr0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralM//.
- apply/EFin_measurable_fun/(@measurable_funS _ _ setT) => //.
  by rewrite (_ : \1_(f k) = mindic R mfk).
- by move=> y _; rewrite lee_fin.
Qed.

Lemma integralM_indic' (T : measurableType) (R : realType)
    (m : {measure set T -> \bar R}) (D : set T) (f : {nnsfun T >-> R}) k :
  measurable D ->
  (\int[m]_(x in D) (k * \1_(f @^-1` [set k]) x)%:E=
   k%:E * \int[m]_(x in D) (\1_(f @^-1` [set k]) x)%:E)%E.
Proof.
move=> mD.
rewrite (@integralM_indic _ _ _ _ (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

(* TODO: move to measure.v? *)
Section transfer.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (phi : T1 -> T2).
Hypothesis mphi : measurable_fun setT phi.
Variables (R : realType) (mu : {measure set T1 -> \bar R}).

Lemma transfer (f : T2 -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[pushforward_measure mphi mu]_y f y =
  \int[mu]_x (f \o phi) x.
Proof.
move=> mf f0.
pose pt2 := phi point.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity
    (lim (fun n => \int[pushforward_measure mphi mu]_x (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; apply/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => \int[mu]_x (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; apply: measurable_fun_comp; first exact: measurable_fun_EFin.
      by apply: measurable_fun_comp => //; exact: measurable_sfun.
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
  by apply: eq_integral => x _ /=; apply/cvg_lim => //; exact: f_f.
rewrite funeqE => n.
have mfnphi : forall r, measurable (f_ n @^-1` [set r] \o phi).
  move=> r.
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k <- fset_set (range (f_ n)))
  \int[mu]_x (k * \1_(((f_ n) @^-1` [set k]) \o phi) x)%:E).
  under eq_integral do rewrite fimfunE -sumEFin.
  rewrite ge0_integral_sum//; last 2 first.
    - move=> y; apply/EFin_measurable_fun; apply: measurable_funM.
        exact: measurable_fun_cst.
      by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) y)).
    - by move=> y x _; rewrite muleindic_ge0.
  apply eq_bigr => r _; rewrite integralM_indic'// integral_indic//.
  rewrite /= /pushforward.
  rewrite (@integralM_indic _ _ _ _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _)%E; rewrite [RHS](@integral_indic).
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_sum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun; apply: measurable_funM.
      exact: measurable_fun_cst.
    by rewrite (_ : \1_ _ = mindic R (mfnphi r)).
  - by move=> r x _; rewrite muleindic_ge0.
by apply eq_integral => x _; rewrite sumEFin -fimfunE.
Qed.

End transfer.

Module Probability.
Section probability.
Variable (T : measurableType) (R : realType).
Record t := mk {
  P : {measure set T -> \bar R} ;
  _ : P setT = 1%E }.
End probability.
Module Exports.
Definition probability (T : measurableType) (R : realType) := (t T R).
Coercion P : t >-> Measure.map.
End Exports.
End Probability.
Export Probability.Exports.

Section probability_lemmas.
Variables (T : measurableType) (R : realType) (P : probability T R).

Lemma probability_setT : P setT = 1%:E.
Proof. by case: P. Qed.

Lemma probability_set0 : P set0 = 0%E.
Proof. exact: measure0. Qed.

Lemma probability_not_empty : [set: T] !=set0.
Proof.
apply/set0P/negP => /eqP setT0; have := probability_set0.
by rewrite -setT0 probability_setT; apply/eqP; rewrite oner_neq0.
Qed.

Lemma probability_le1 (A : set T) : measurable A -> (P A <= 1)%E.
Proof.
move=> mA; rewrite -probability_setT.
by apply: le_measure => //; rewrite ?in_setE.
Qed.

Lemma probability_integrable_cst k : P.-integrable [set: T] (EFin \o cst_mfun k).
Proof.
split; first exact/EFin_measurable_fun/measurable_fun_cst.
have [k0|k0] := leP 0 k.
- rewrite (eq_integral (EFin \o cst_mfun k))//; last first.
    by move=> x _ /=; rewrite ger0_norm.
  by rewrite integral_cst// probability_setT mule1 ltey.
- rewrite (eq_integral (EFin \o cst_mfun (- k)))//; last first.
    by move=> x _ /=; rewrite ltr0_norm.
  by rewrite integral_cst// probability_setT mule1 ltey.
Qed.

End probability_lemmas.

Reserved Notation "f `o X" (at level 50, format "f  `o '/ '  X").
Reserved Notation "X '`^2' " (at level 49).
Reserved Notation "X '`-cst' m" (at level 50).
Reserved Notation "X `+ Y" (at level 50).
Reserved Notation "X `- Y" (at level 50).
Reserved Notation "k `cst* X" (at level 49).

Section mfun.
Variable R : realType.

Definition sqr : R -> R := fun x => x ^+ 2.

Lemma sqr_mfun_subproof : @IsMeasurableFun _ R sqr.
Proof. by split; apply: measurable_fun_sqr; exact: measurable_fun_id. Qed.
HB.instance Definition _ := sqr_mfun_subproof.
Definition sqr_mfun := [the {mfun _ >-> R} of sqr].

Definition subr m : R -> R := fun x => x - m.

Lemma subr_mfun_subproof m : @IsMeasurableFun _ R (subr m).
Proof.
split => _; apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; apply: measurableI => //.
rewrite (_ : _ @^-1` _ = `](x + m),+oo[)%classic; first exact: measurable_itv.
by apply/seteqP; split => r;
  rewrite preimage_itv in_itv/= in_itv/= !andbT ltr_subr_addr.
Qed.
HB.instance Definition _ m := subr_mfun_subproof m.
Definition subr_mfun m := [the {mfun _ >-> R} of subr m].

End mfun.

Section comp_mfun.
Variables(T : measurableType) (R : realType)
  (f : {mfun Real_sort__canonical__measure_Measurable R >-> R})
  (g : {mfun T >-> R}).

Lemma comp_mfun_subproof : @IsMeasurableFun _ _ (f \o g).
Proof. by split; exact: measurable_fun_comp. Qed.
HB.instance Definition _ := comp_mfun_subproof.
Definition comp_mfun := [the {mfun _ >-> R} of (f \o g)].
End comp_mfun.

(*Reserved Notation "{ 'RV' P >-> R }"
  (at level 0, format "{ 'RV'  P  >->  R }").
Module RandomVariable.
Section random_variable.
Record t (R : realType) (P : probability R) := mk {
  f : {mfun P >-> R} (*;
  _ : P.-integrable [set: P] (EFin \o f)*)
}.
End random_variable.
Module Exports.
Coercion f : t >-> MeasurableFun.type.
Notation "{ 'RV'  P >-> R }" := (@t R P) : form_scope.
End Exports.
End RandomVariable.
Export RandomVariable.Exports.*)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Definition random_variable (T : measurableType) (R : realType) (P : probability T R) :=
  {mfun T >-> R}.
Notation "{ 'RV' P >-> R }" := (@random_variable _ R P) : form_scope.

Section random_variables.
Variables (T : measurableType) (R : realType) (P : probability T R).

Definition comp_RV (f : {mfun _ >-> R}) (X : {RV P >-> R}) : {RV P >-> R} :=
  [the {RV P >-> R} of f \o X].

Local Notation "f `o X" := (comp_RV f X).

Definition sq_RV (X : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> R} of @sqr R] `o X.

Definition RV_sub (X : {RV P >-> R}) m : {RV P >-> R} :=
  [the {mfun _ >-> _} of @subr R m] `o X.

Definition sub_RV (X Y : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of X - Y].

Definition add_RV (X Y : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of X + Y].

Definition scale_RV k (X : {RV P >-> R}) : {RV P >-> R} :=
  [the {mfun _ >-> _} of k \o* X].

End random_variables.
Notation "f `o X" := (comp_RV f X).
Notation "X '`^2' " := (sq_RV X).
Notation "X '`-cst' m" := (RV_sub X m).
Notation "X `- Y" := (sub_RV X Y).
Notation "X `+ Y" := (add_RV X Y).
Notation "k `cst* X" := (scale_RV k X).

Section expectation.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (P : probability T R).

Definition expectation (X : {RV P >-> R}) := \int[P]_w (X w)%:E.
End expectation.
Notation "''E' X" := (expectation X).

Section integrable_pred.
Context {T : measurableType} {R : realType} (mu : {measure set T -> \bar R}).
Definition ifun : {pred T -> \bar R} := mem [set f | `[< mu.-integrable setT f >]].
(* NB: avoid Prop to define integrable? *)
Definition ifun_key : pred_key ifun. Proof. exact. Qed.
Canonical ifun_keyed := KeyedPred ifun_key.
End integrable_pred.

Section expectation_lemmas.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (P : probability T R).

(* TODO: generalize *)
Lemma expectation1 : 'E (cst_mfun 1 : {RV P >-> R}) = 1.
Proof. by rewrite /expectation integral_cst// probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) :
  'E ((*\1_A*) indic_mfun A mA : {RV P >-> R}) = P A.
Proof. by rewrite /expectation integral_indic// setIT. Qed.

Variables (X : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X)).

Lemma integrable_expectation : `| 'E X | < +oo.
Proof.
move: iX => [? Xoo]; rewrite (le_lt_trans _ Xoo)//.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (k : R) : 'E (k `cst* X) = k%:E * 'E X.
Proof.
rewrite /expectation. (*TODO: expectationE lemma*)
under eq_integral do rewrite EFinM.
rewrite -integralM//.
by under eq_integral do rewrite muleC.
Qed.

Lemma expectation_ge0 : (forall x, 0 <= X x)%R -> 0 <= 'E X.
Proof.
by move=> ?; rewrite /expectation integral_ge0// => x _; rewrite lee_fin.
Qed.

Variables (Y : {RV P >-> R}) (iY : P.-integrable setT (EFin \o Y)).

Lemma expectationD : 'E (X `+ Y) = 'E X + 'E Y.
Proof. by rewrite /expectation integralD_EFin. Qed.

Lemma expectationB : 'E (X `- Y) = 'E X - 'E Y.
Proof. by rewrite /expectation integralB_EFin. Qed.

End expectation_lemmas.

Section square_integrable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Definition square_integrable (D : set T) (f : T -> R) :=
  (\int[mu]_(x in D) (`| f x | ^+ 2)%:E < +oo)%E.

Lemma square_integrableP (D : set T) (f : T -> R) :
  measurable D -> measurable_fun D f ->
  square_integrable(*TODO: generalize*) D f <-> mu.-integrable D (EFin \o (fun x => `|f x| ^+ 2)).
Proof.
move=> mD mf; rewrite /square_integrable; split.
  move=> foo; split.
    exact/EFin_measurable_fun/measurable_fun_sqr/measurable_fun_comp.
  apply: le_lt_trans foo; apply ge0_le_integral => //.
  - apply/EFin_measurable_fun => //; apply: measurable_fun_comp => //.
    exact/measurable_fun_sqr/measurable_fun_comp.
  - apply/EFin_measurable_fun => //; apply: measurable_fun_sqr => //.
    exact: measurable_fun_comp.
  - by move=> x Dx /=; rewrite ger0_norm.
move=> [mf' foo].
rewrite (eq_integral (fun x => `|(EFin \o (fun y => (`|f y| ^+ 2)%R)) x|)%E)// => x xD.
by rewrite gee0_abs// lee_fin.
Qed.

End square_integrable.

Section variance.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (P : probability T R).

Definition variance (X : {RV P >-> R}) := 'E ((X `-cst fine 'E X) `^2).
Local Notation "''V' X" := (variance X).

Variables (X : {RV P >-> R}) (iX : P.-integrable setT (EFin \o X)).

Lemma varianceE : square_integrable P setT X ->
  'V X = 'E (X `^2) - ('E X) ^+ 2.
Proof.
move=> PX.
rewrite /variance (_ : _ `^2 = X `^2 `- (2 * fine 'E X) `cst* X
    `+ fine ('E X ^+ 2) `cst* cst_mfun 1); last first.
  apply/mfuneqP => x /=; rewrite /sqr /subr/= sqrrB -[RHS]/(_ - _ + _)%R /=.
  congr (_ - _ +  _)%R.
    by rewrite mulr_natl -mulrnAr mulrC.
  rewrite -[RHS]/(_ * _)%R mul1r.
  have [Efin|] := boolP ('E X \is a fin_num); first by rewrite fineM.
  by rewrite fin_numElt -(lte_absl ('E X) +oo) (integrable_expectation iX).
have ? : P.-integrable [set: T] (EFin \o X `^2).
  rewrite (_ : EFin \o X `^2 = (fun x => (`| X x | ^+ 2)%:E)).
    exact/square_integrableP.
  by rewrite funeqE => p /=; rewrite real_normK// num_real.
rewrite expectationD; last 2 first.
  - rewrite (_ : _ \o _ =
      (fun x => (EFin \o (X `^2)) x - (EFin \o (2 * fine 'E X `cst* X)) x)) //.
    apply: integrableB => //.
    rewrite (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E))//.
    exact: integrableK.
    move=> t _ /=.
    by rewrite muleC EFinM.
  - rewrite (eq_integrable _ (fun x => (fine ('E X ^+ 2))%:E * (cst_mfun 1 x)%:E))//.
      by apply: integrableK => //; exact: probability_integrable_cst.
    move=> t _ /=.
    by rewrite mul1r mule1.
rewrite expectationB //; last first.
  rewrite (eq_integrable _ (fun x => (2 * fine 'E X)%:E * (X x)%:E))//.
    exact: integrableK.
  move=> t _ /=.
  by rewrite mulrC EFinM.
rewrite expectationM// expectationM; last exact: probability_integrable_cst.
rewrite expectation1 mule1.
have ? : 'E X \is a fin_num.
  by rewrite fin_numElt -(lte_absl ('E X) +oo) integrable_expectation.
rewrite EFinM fineK// expe2 fineM// EFinM fineK//.
rewrite -muleA mule_natl mule2n oppeD ?fin_numM//.
by rewrite addeA subeK// fin_numM.
Qed.

End variance.
Notation "''V' X" := (variance X).

Section distribution.
Variables (T : measurableType) (R : realType) (P : probability T R) (X : {RV P >-> R}).

Definition distribution : {measure set R -> \bar R} :=
  pushforward_measure (@measurable_funP _ _ X) P.

Lemma distribution_is_probability : distribution [set: R] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

Definition probability_of_distribution : probability _ R :=
  Probability.mk distribution_is_probability.

End distribution.

Section transfer_probability.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (P : probability T R) (X : {RV P >-> R}).

Lemma transfer_probability (f : R -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[distribution X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite transfer. Qed.

End transfer_probability.

Require Import functions.

Section subadditive_countable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Local Open Scope ereal_scope.

(* PR: in progress *)
Lemma integral_set0 (f : T -> \bar R) : \int[mu]_(x in set0) f x = 0.
Proof.
Admitted.

Lemma restrict_lee {aT} {rT : numFieldType} (D E : set aT) (f : aT -> \bar rT) :
  (forall x, E x -> 0 <= f x) ->
  D `<=` E -> forall x, ((f \_ D) x <= (f \_ E) x)%E.
Proof.
Admitted.

Lemma ge0_integral_bigsetU (F : (set T)^nat) (mF : forall n, measurable (F n))
    (f : T -> \bar R) n :
  let D := \big[setU/set0]_(i < n) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset `I_n F ->
  \int[mu]_(x in D) f x = \sum_(i < n) \int[mu]_(x in F i) f x.
Proof.
Admitted.

Lemma ge0_integral_bigcup (F : (set _)^nat) (f : T -> \bar R) :
  (forall x, 0 <= f x)%E ->
  trivIset setT F ->
  (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) f ->
  (\int[mu]_(x in \bigcup_i F i) f x =
   \sum_(i <oo) \int[mu]_(x in F i) f x)%E.
Proof.
Admitted.

Definition summable (R' : realType) (T' : choiceType) (D : set T') (f : T' -> \bar R') :=
  \esum_(x in D) `| f x | < +oo.

Lemma esumB :
forall [R' : realType] [T' : choiceType] [D : set T'] [f g : T' -> \bar R'],
summable D f ->
summable D g ->
(forall i : T', D i -> (0 <= f i)%E) ->
(forall i : T', D i -> (0 <= g i)%E) ->
(\esum_(i in D) (f \- g)^\+ i - \esum_(i in D) (f \- g)^\- i)%E =
(\esum_(i in D) f i - \esum_(i in D) g i)%E.
Admitted.

Lemma summable_ereal_pseries (f : nat -> \bar R) (P : pred nat) :
  summable P f ->
  \sum_(i <oo | P i) (f i) = \sum_(i <oo | P i) f^\+ i - \sum_(i <oo | P i) f^\- i.
Admitted.

Lemma integrable_abse [T' : measurableType] [R' : realType]
    [m : {measure set T' -> \bar R'}] [D : set T'] :
  measurable D -> forall f : T' -> \bar R', m.-integrable D f -> m.-integrable D (abse \o f).
Proof.
Admitted.

Lemma integrable_summable (F : (set T)^nat) (g : T -> \bar R):
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  summable [set: nat] (fun i => \int[mu]_(x in F i) g x).
Proof.
Admitted.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int[mu]_(x in \bigcup_i F i) g x = \sum_(i <oo) \int[mu]_(x in F i) g x)%E.
Proof.
Admitted.
End subadditive_countable.

Lemma preimage10' {T R : Type} {f : T -> R} {x : R} :
  f @^-1` [set x] = set0 -> ~ range f x.
Proof.
rewrite /image /=.
apply: contraPnot => -[t _ <-].
rewrite /preimage/=.
by move/seteqP => -[+ _] => /(_ t) /=.
Qed.
(* /PR in progress *)

(* Convoo? *)
Module Convn.
Record t (R : realType) := {
  f : nat -> R ;
  f0 : forall n, (0 <= f n)%R ;
  f1 : (\sum_(n <oo) (f n)%:E = 1)%E }.
End Convn.
Notation convn := Convn.t.
Coercion Convn.f : convn >-> Funclass.

#[global] Hint Resolve Convn.f0 : core.

Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

Module DiscreteRV.
Section discreterv.
Local Open Scope form_scope.
Variables (T : measurableType) (R : realType) (P : probability T R).
Record t := mk {
  X : {RV P >-> R} ;
  weight : convn R ;
  values : {injfun [set: nat] >-> [set: R]} ;
  Xvalues : forall t, exists n, X t = values n ;
  distributionE : distribution X =1
    (fun A : set R => \sum_(n <oo) (weight n)%:E * \d_ (values n) A)%E
}.
End discreterv.
Module Exports.
Notation discrete_random_variable := t.
Coercion X : t >-> random_variable.
Notation "{ 'dRV' P >-> R }" := (@discrete_random_variable _ R P) : form_scope.
End Exports.
End DiscreteRV.
Export DiscreteRV.Exports.

Section discreterv_lemmas.
Variables (T : measurableType) (R : realType) (P : probability T R).

Let c (X : {dRV P >-> R}) := DiscreteRV.weight X.
Let a (X : {dRV P >-> R}) := DiscreteRV.values X.

Lemma dRV_values (X : {dRV P >-> R}): forall x, exists n, (X : {RV P >-> R}) x = a X n.
Proof. by case: X. Qed.

Lemma dRV_distributionE (X : {dRV P >-> R}) :
  distribution X =1
    (fun A : set R => \sum_(n <oo) (c X n)%:E * \d_ (a X n) A)%E.
Proof. by case: X. Qed.

End discreterv_lemmas.

Section discrete_distribution.
Variables (T : measurableType) (R : realType) (P : probability T R)
  (X : {dRV P >-> R}).

Notation c := (DiscreteRV.weight X).
Notation a := (DiscreteRV.values X).

Lemma probability_distribution r :
  P [set x | (X : {RV P >-> R}) x = r] = distribution X [set r].
Proof. by rewrite /distribution /= /pushforward. Qed.

Lemma distribution_values (n : nat) : distribution X [set a n] = (c n)%:E.
Proof.
rewrite (dRV_distributionE X) nneseries_esum; last first.
  by move=> m _; rewrite mule_ge0// lee_fin.
rewrite (esumID [set n]); last first.
  by move=> m _; rewrite mule_ge0// lee_fin.
rewrite addeC esum0 ?add0e; last first.
  move=> m [_ /= mn].
  rewrite /dirac indicE memNset ?mule0//=.
  by apply: contra_not mn; exact/injT.
rewrite (_ : _ `&` _ = [set n]); last exact/seteqP.
rewrite esum_set1.
  by rewrite /= /dirac indicE mem_set// mule1.
by rewrite mule_ge0// lee_fin.
Qed.

Lemma dRV_expectation : P.-integrable setT (EFin \o (X : {RV P >-> R})) ->
  'E X = (\sum_(n <oo) (c n)%:E * (a n)%:E)%E.
Proof.
move=> ix.
rewrite /expectation.
rewrite -[in LHS](_ : \bigcup_k (X : {RV P >-> R}) @^-1` [set a k] = setT); last first.
  apply/seteqP; split => // t _.
  by have [n XAtn] := dRV_values X t; exists n.
have tA : trivIset setT (fun k => [set a k]).
  by move=> i j _ _ [/= r []] ->; exact/injT.
have tXA : trivIset setT (fun k => (X : {RV P >-> R}) @^-1` [set a k]).
  apply/trivIsetP => /= i j _ _ ij.
  move/trivIsetP : tA => /(_ i j Logic.I Logic.I ij) Aij.
  by rewrite -preimage_setI Aij preimage_set0.
rewrite integral_bigcup//; last first.
  by apply: (integrableS measurableT) => //; exact: bigcup_measurable.
transitivity (\sum_(i <oo) \int[P]_(x in (X : {RV P >-> R}) @^-1` [set a i]) (a i)%:E)%E.
  by apply eq_nneseries => i _; apply eq_integral => t; rewrite in_setE/= => ->.
transitivity (\sum_(i <oo) (a i)%:E * \int[P]_(x in (X : {RV P >-> R}) @^-1` [set a i]) 1)%E.
  apply eq_nneseries => i _; rewrite -integralM//; last first.
    split; first exact: measurable_fun_cst.
    rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
    rewrite integral_cst// mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
    exact: probability_le1.
  by apply eq_integral => y _; rewrite mule1.
apply eq_nneseries => k _.
by rewrite integral_cst//= mul1e probability_distribution distribution_values muleC.
Qed.

End discrete_distribution.

(* PR in progress *)
Section discrete_measurable.
(*Variable T : pointedType.*)

Definition discrete_measurable : set (set nat) := [set: set nat].

Let discrete_measurable0 : discrete_measurable set0. Proof. by []. Qed.

Let discrete_measurableC X :
  discrete_measurable X -> discrete_measurable (~` X).
Proof. by []. Qed.

Let discrete_measurableU (F : (set nat)^nat) :
  (forall i, discrete_measurable (F i)) ->
  discrete_measurable (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build nat (Pointed.class _)
  discrete_measurable discrete_measurable0 discrete_measurableC
  discrete_measurableU.

End discrete_measurable.

Lemma lebesgue_measure_itv (R : realType) (i : interval R) :
  lebesgue_measure [set` i] = hlength [set` i].
Admitted.

Lemma lebesgue_measure_set1 (R : realType) (r : R) :
  lebesgue_measure [set r] = 0%E.
Admitted.
(* /PR in progress *)

Lemma lte01 (R : numDomainType) : (0 < (1 : \bar R))%E.
Proof. by rewrite lte_fin ltr01. Qed.

Lemma new_eq_nneseries (R : realFieldType) (f g : (\bar R)^nat) (P : pred nat) k :
    (forall i, (k <= i)%N -> P i -> f i = g i) ->
  (\sum_(k <= i <oo | P i) f i = \sum_(k <= i <oo | P i) g i)%E.
Proof.
move=> efg; congr (lim _); apply/funext => n; rewrite big_nat_cond.
rewrite [RHS]big_nat_cond; apply: eq_bigr => i /andP[/andP[ki ni] Pi].
exact: efg.
Qed.

Lemma new_nneseries0 (R : realFieldType) (f : (\bar R)^nat) k (P : pred nat) :
  (forall i, (k <= i)%N -> P i -> f i = 0%E) -> (\sum_(k <= i <oo | P i) f i = 0)%E.
Proof.
move=> f0.
rewrite ereal_series_cond nneseries0// => i /andP[].
exact: f0.
Qed.

Lemma floor_natz (R : realType) (k : nat) : floor (k%:R : R) = k%:~R.
Proof. by rewrite /floor (Rfloor_natz R k) Rtointz intz. Qed.

Section measure_scale.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realFieldType).
Variables (r : {nonneg R}) (m : {measure set T -> \bar R}).

Definition mscale (A : set T) : \bar R := r%:num%:E * m A.

Let mscale0 : mscale set0 = 0. Proof. by rewrite /mscale measure0 mule0. Qed.

Let mscale_ge0 B : 0 <= mscale B.
Proof. by rewrite /mscale mule_ge0. Qed.

Let mscale_sigma_additive : semi_sigma_additive mscale.
Proof.
move=> F mF tF mUF; rewrite [X in X --> _](_ : _ =
    (fun n => (r%:num)%:E * \sum_(0 <= i < n) m (F i))); last first.
  by apply/funext => k; rewrite ge0_sume_distrr.
rewrite /mscale; have [->|r0] := eqVneq r%:num 0%R.
  rewrite mul0e [X in X --> _](_ : _ = (fun=> 0)); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: ereal_cvgrM => //; exact: measure_semi_sigma_additive.
Qed.

Canonical measure_scale : {measure set T -> \bar R} :=
  Measure.Pack _ (Measure.Axioms mscale0 mscale_ge0 mscale_sigma_additive).

End measure_scale.
Arguments mscale {T R}.
Arguments measure_scale {T R}.

Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "p '.~'" (format "p .~", at level 5).

Module Prob.
Section prob.
Variable (R : numDomainType).
Record t := mk {
  p :> R ;
  Op1 : 0 <= p <= 1 }.
Definition O1 (p : t) := Op1 p.
Arguments O1 : simpl never.
End prob.
Module Exports.
Section exports.
Variables (R : numDomainType).
Canonical prob_subType := Eval hnf in [subType for @p R].
Local Notation prob := (t R).
Definition prob_eqMixin := [eqMixin of prob by <:].
Canonical prob_eqType := Eval hnf in EqType _ prob_eqMixin.
Definition prob_choiceMixin := [choiceMixin of prob by <:].
Canonical prob_choiceType := ChoiceType prob prob_choiceMixin.
Definition prob_porderMixin := [porderMixin of prob by <:].
Canonical prob_porderType := POrderType ring_display prob prob_porderMixin.
End exports.
End Exports.
End Prob.
Export Prob.Exports.
Notation prob := Prob.t.
Notation "q %:pr" := (@Prob.mk _ q (@Prob.O1 _ _)).
Coercion Prob.p : prob >-> Num.NumDomain.sort.

Lemma prob_le1 (R : numDomainType) (p : prob R) : (p : R) <= (1 : R).
Proof. by case: p => p /= /andP[]. Qed.
Global Hint Resolve prob_le1 : core.

Definition onem (R : numDomainType) (r : R) := 1 - r.
Notation "p '.~'" := (onem p).

Lemma OO1 (R : numDomainType) : 0 <= (0 : R) <= 1.
Proof. by rewrite lexx ler01. Qed.
Canonical prob0 (R : numDomainType) := Eval hnf in Prob.mk (OO1 R).

Lemma O11 (R : numDomainType) : 0 <= (1 : R) <= 1.
Proof. by rewrite lexx ler01. Qed.
Canonical prob1 (R : numDomainType) := Eval hnf in Prob.mk (O11 R).

Lemma onem_prob (R : numDomainType) (r : R) : 0 <= r <= 1 -> 0 <= r.~ <= 1.
Proof.
move=> /andP[r0 r1].
by rewrite /onem subr_ge0 r1/= ler_subl_addr ler_addl.
Qed.
Canonical probcplt (R : numDomainType) (p : prob R) :=
  Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma ge0_prob_subproof (R : numDomainType) (p : prob R) :
  Signed.spec 0 ?=0 >=0 (p : R).
Proof.
case: p => p /= p01.
rewrite /prob0 /Order.le /= /Order.CanMixin.le /=.
by case/andP : p01.
Qed.
Canonical prob0_nonneg (R : numDomainType) (p : prob R) : {nonneg R} :=
  Signed.mk (ge0_prob_subproof p).

Lemma ge0_onem_prob_subproof (R : numDomainType) (p : prob R) :
  Signed.spec 0 ?=0 >=0 (probcplt p : R).
Proof.
rewrite /=.
case: p => p /= /andP[p0 p1].
by rewrite subr_ge0.
Qed.
Canonical probonem_nonneg (R : numDomainType) (p : prob R) :=
  Signed.mk (ge0_onem_prob_subproof p).

Lemma prob_mulR (R : numDomainType) (p q : prob R) :
  (0 <= (p : R) * (q : R) <= 1)%R.
Proof.
apply/andP; split; first exact/mulr_ge0.
by rewrite -(mulr1 1); exact: ler_pmul.
Qed.
Canonical probmulR (R : numDomainType) (p q : prob R) :=
  Eval hnf in @Prob.mk _ _ (prob_mulR p q).

Axiom R : numDomainType.
Check ((0 * 0)%:pr : prob R).

(* P_X = (1 - p)\dirac_0 + p\dirac_1 *)

(* (1 - p) *: \dirac_0 + p *: \dirac_1 *)

Definition Bernoulli_distribution (R : realType) (p : prob R) :
    {measure set nat -> \bar R} :=
  measure_add (measure_scale (prob0_nonneg p) (@dirac_measure _ 0%N R))
              (measure_scale (probonem_nonneg p) (@dirac_measure _ 1%N R)).

Section bernoulli.
Variables (R : realType) (p : R).
Hypothesis p01 : 0 <= p <= 1.
Let f n := if n is 0%N then 1 - p else if n is 1%N then p else 0.
Let f0 : forall n, (0 <= f n)%R.
Proof.
move=> n; rewrite /f; case: n => [|[|//]].
- by move/andP : p01 => [p0 p1]; rewrite subr_ge0.
- by move/andP : p01 => [].
Qed.
Let f1 : (\sum_(n <oo) (f n)%:E = 1)%E.
Proof.
rewrite (nneseries_split 2)// 2!big_ord_recr/= big_ord0 add0e -EFinD subrK.
by rewrite new_nneseries0 ?adde0//; case=> [//|[]//].
Qed.
Let c : convn R := Convn.Build_t f0 f1.
Definition natR := (fun n => n%:R : R).
Lemma homo_natR : {homo natR : x / setT x >-> setT x}.
Proof. by []. Qed.
HB.instance Definition _ := @IsFun.Build nat R setT setT natR homo_natR.
Let natR_oinv : R -> option nat := fun r => some `|floor r|%N.
HB.instance Definition _ := @OInv.Build nat R natR natR_oinv.
Lemma natRK : {in @setT nat, pcancel natR 'oinv_natR}.
Proof.
move=> k _.
rewrite /'oinv_natR.
rewrite /oinv/=.
rewrite /natR_oinv /natR.
by rewrite floor_natz intz.
Qed.
HB.instance Definition _ := @OInv_Can.Build _ _ setT natR natRK.
Let values := [the {injfun [set: nat] >-> [set: R]} of natR].
Let P'' : set nat -> \bar R := fun (A : set nat) =>
  (\sum_(i <oo) (f i)%:E * dirac i A)%E.
Let P''proof : semi_sigma_additive P''.
Proof.
move=> /= F mF tF mUF.
rewrite /P''.
Admitted.
Let P' : {measure set nat -> \bar R}. (* X {0} = 1 - p, X {1} = p*)
(*P : set nat -> \bar R
if 0 \in X then 1 - p
if 1 \in X then 1
else 0*)
Admitted.
Let P'1 : P' setT = 1%:E.
Proof.
Admitted.
Let P := Probability.mk P'1.
Let X' : nat -> R := fun n => if n == 0%N then 1 - p else if n == 1%N then p else 0.
Let X : {RV P >-> R}.
Admitted.
Lemma Xa : (forall t : nat, exists n : nat, X t = values n).
Proof.
move=> n.
exists n.
rewrite /values/=.
Admitted.
Let H1 : distribution X =1
         (fun A : set R => \sum_(n <oo) (c n)%:E * (\d_ (values n) A))%E.
Proof.
move=> /= A.
rewrite /pushforward.
Admitted.
End bernoulli.

Section RV_of_distribution.
Variable (R : realType).
Let T : measurableType := g_measurableType (@ocitv R).
Definition distribution_function
    (P : probability T R) (X : {RV P >-> R}) : R -> \bar R :=
  fun x => P (X @^-1` (`]-oo, x]%classic)). (* P[X <= x] *)

Definition ginv (F : R -> R) : R -> R :=
  fun t => inf [set x : R | (F x >= t)%R]. (* NB: for t in Omega *)

Lemma measurable_fun_ginv (F : R -> R) : measurable_fun setT (ginv F).
Proof.
rewrite /= /ginv.
Abort.

Lemma infP (P : set R) : forall x, P x -> inf P <= x.
Proof.
move=> x Px.
rewrite /inf.
rewrite ler_oppl.
Admitted.

Lemma RV_of_distribution_function (F : R -> R) :
  {homo F : x y / (x <= y) >-> (x <= y)%R} ->
  exists (P : probability T R) (X : {RV P >-> R}),
    distribution_function X = EFin \o F.
Proof.
move=> ndF.
pose Omega : set R := `]0, 1[%classic.
pose A : set (set R) := [set X `&` Omega | X in @measurable (measurableTypeR R)].
have mOmega : measurable Omega by exact: measurable_itv.
pose P : {measure set _ -> _} := measure_restr (@lebesgue_measure R) mOmega.
have PT : P setT = 1%E.
  rewrite /P measure_restrE.
  rewrite (_ : _ `&` _ = Omega);last by apply/seteqP; split => [? []//|].
  by rewrite lebesgue_measure_itv hlength_itv/= lte01 oppr0 adde0.
exists (Probability.mk PT).
pose F1 : R -> R := ginv F.
(* t \in Omega *)
have H1 : forall (x t : R), F1 t <= x <-> t <= F x.
  move=> x t; split.
    rewrite /F1 /ginv => tFx.
    set S := [set x | t <= F x] in tFx.
    have S0 : S !=set0.
      admit. (* by properties of F *)
    have lbS : has_lbound S.
      admit. (* by properties of F *)
    have hiS : has_inf S by [].
    move: tFx.
    rewrite le_eqVlt => /orP[/eqP|].
      move=> <-.
      rewrite /S.
      rewrite leNgt.
      apply/negP.
      rewrite -subr_gt0 => tF0.
      have H := divr_gt0 tF0 (ltr0n R 2%N).
      have [s Ss sStF] := inf_adherent hiS H.
      rewrite -/S in sStF.
      (* F (inf S) is an inf of F @` S (needs a lemma, using monotonicity and right continuity) see contract_inf *)
      have H1 : F (inf S) = inf (F @` S). admit.
      (*there must be an x' such that F (inf S) < F x' < t with x' in S.
       by definition of S, contradiction because F x' should be greater than t*)
      admit.
    move/ltW.
    move/ndF.
    apply: le_trans.
    have -> : F (inf S) = inf (F @` S). admit.
    rewrite /S.
    have H2 : [set F x | x in [set x0 | t <= F x0]] `<=` [set` `[t, +oo[].
      by move=> _/= [r tFr <-] /[!in_itv]/=; rewrite tFr.
    have : inf [set` `[t, +oo[] <= inf [set F x | x in [set x0 | t <= F x0]].
      admit.
    apply: le_trans.
    by rewrite set_interval.inf_itv//.
    rewrite /F1 /ginv => tFx.
    by apply: infP.
have H2 : forall x : R, [set t | t in [set t | (F1 t <= x)%R]] =
               `]0, (F x)]%classic `&` Omega.
  admit.
have mF1 : measurable_fun setT F1.
  move=> _ B /= mB.
  rewrite setTI.
  rewrite /F1 /ginv.
  admit.
have @X : {RV Probability.mk PT >-> R}.
  apply: MeasurableFun.Pack.
  apply: MeasurableFun.Class.
  apply: IsMeasurableFun.Axioms_.
  by apply: mF1.
exists X.
apply/funext => x.
rewrite /=.
rewrite /distribution_function.
Admitted.

End RV_of_distribution.

Module Density.
Section density.
Local Open Scope form_scope.
Variables (R : realType) (P : probability (g_measurableType (@ocitv R)) R)
          (X : {RV P >-> R}).
Record t := mk {
  f : {mfun (g_measurableType (@ocitv R)) >-> R} ;
  f0 : forall r, 0 <= f r ;
  support : distribution X =1 (fun A => \int[lebesgue_measure]_(x in A) (f x)%:E)%E
}.
End density.
End Density.
