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
(*       measure_dirac a == Dirac measure of a                                *)
(* measure_image f mf mu == image of measure mu : {measure set T1 -> \bar R}  *)
(*                          by f : T1 -> T2; mf is a proof that f is          *)
(*                          measurable                                        *)
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

(******************************************************************************)
(*                             Probability (WIP)                              *)
(*                                                                            *)
(* measure_dirac                                                              *)
(* measure_image                                                              *)
(* probability                                                                *)
(* random_variable                                                            *)
(* expectation                                                                *)
(* distribution                                                               *)
(******************************************************************************)

(* TODO: PR in progress *)
Hint Extern 0 (measurable_fun _ normr) =>
  solve [exact: measurable_fun_normr] : core.

Definition sqe (R : numDomainType) (x : \bar R) := (x ^+ 2)%E.

Lemma csum_set1 [R : realType] [T : choiceType] (t : T) (a : T -> \bar R) :
  (forall t, 0 <= a t)%E ->
  \esum_(i in [set t]) a i = a t.
Proof.
Admitted.
(* /TODO: PR in progress *)

Notation integralrM := integrableK.

Section integrable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Lemma integrableMr (D : set T) : measurable D ->
  forall (k : R) (f : T -> \bar R), mu.-integrable D f ->
  mu.-integrable D (f \* cst k%:E)%E.
Proof.
move=> mD k f mf; apply: eq_integrable (integralrM mD k mf) => //.
by move=> x _; rewrite muleC.
Qed.

(*NB: check eq_integrable may not need measurable D *)
Lemma eq_integrable (D : set T) : measurable D -> forall f2 f1 : T -> \bar R,
  {in D, f1 =1 f2} -> mu.-integrable D f1 = mu.-integrable D f2.
Proof.
move=> mD f2 f1 f12.
apply: propext; split; apply: eq_integrable => // x xD.
by rewrite f12.
Qed.

End integrable.
Arguments eq_integrable {T R mu D} _ f2 f1.
(******************************************************************************)
(* /TODO: backport                                                            *)
(******************************************************************************)

(* NB: PR in progress *)
Section measure_dirac.
Local Open Scope ereal_scope.
Variables (T : measurableType) (a : T) (R : realType).

Definition measure_dirac' (A : set T) : \bar R := (\1_A a)%:E.

Lemma measure_dirac'0 : measure_dirac' set0 = 0.
Proof. by rewrite /measure_dirac' indic0. Qed.

Lemma measure_dirac'_ge0 B : 0 <= measure_dirac' B.
Proof. by rewrite /measure_dirac' lee_fin. Qed.

Lemma measure_dirac'_sigma_additive : semi_sigma_additive measure_dirac'.
Proof.
red.
move=> F mF tF mUF; rewrite /measure_dirac' indicE.
have [|aFn] /= := boolP (a \in \bigcup_n F n).
  rewrite inE => -[n _ Fna].
  have naF m : m != n -> a \notin F m.
    move=> mn; rewrite notin_set => Fma.
    move/trivIsetP : tF => /(_ _ _ Logic.I Logic.I mn).
    by rewrite predeqE => /(_ a)[+ _]; exact.
  apply/cvg_ballP => _/posnumP[e]; rewrite near_map; near=> m.
  have mn : (n < m)%N by near: m; exists n.+1.
  rewrite big_mkord (bigID (xpred1 (Ordinal mn)))//= big_pred1_eq/= big1/=.
    by rewrite adde0 (indicE (F n) a) mem_set//; exact: ballxx.
  by move=> j ij; rewrite indicE (negbTE (naF _ _)).
rewrite [X in X --> _](_ : _ = cst 0%E); first exact: cvg_cst.
rewrite funeqE => n /=; rewrite big1// => i _; rewrite indicE.
have [|//] := boolP (a \in F i); rewrite inE => Fia.
move: aFn; rewrite notin_set -[X in X -> _]/((~` (\bigcup_n0 F n0)) a).
by rewrite setC_bigcup => /(_ i Logic.I).
Unshelve. all: by end_near. Qed.

Definition measure_dirac : {measure set T -> \bar R} :=
  locked (Measure.Pack _ (Measure.Axioms
    measure_dirac'0 measure_dirac'_ge0 measure_dirac'_sigma_additive)).

Lemma measure_diracE A : measure_dirac A = (a \in A)%:R%:E.
Proof. by rewrite /measure_dirac; unlock. Qed.

End measure_dirac.
Arguments measure_dirac {T} _ {R}.

Reserved Notation "'\d_' a" (at level 9, format "'\d_'  a").

Notation "\d_ a" := (measure_dirac a).

From mathcomp.finmap Require Import finmap.

Lemma integralM_indic (T : measurableType) (R : realType)
    (m : {measure set T -> \bar R}) (D : set T) (f : R -> set T) k :
  (k < 0 -> f k = set0) ->
  measurable (f k) ->
  measurable D ->
  (\int_ D (k * \1_(f k) x)%:E 'd m[x] =
   k%:E * \int_ D (\1_(f k) x)%:E 'd m[x])%E.
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
  (\int_ D (k * \1_(f @^-1` [set k]) x)%:E 'd m[x] =
   k%:E * \int_ D (\1_(f @^-1` [set k]) x)%:E 'd m[x])%E.
Proof.
move=> mD.
rewrite (@integralM_indic _ _ _ _ (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

Section integral_dirac.
Variables (T : measurableType) (a : T) (R : realType).
Variables (f : T -> R) (mf : measurable_fun setT (EFin \o f)).
Hypothesis f0 : forall x, (0 <= f x)%R.

Lemma integral_dirac :
  (\int_ setT (f x)%:E 'd (\d_ a)[x] = (f a)%:E)%E.
Proof.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity (lim (fun n => \int_ setT (f_ n x)%:E 'd (\d_ a)[x]))%E.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; apply/EFin_measurable_fun; exact/(@measurable_funS _ _ setT).
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: f_f.
rewrite funeqE => n.
under eq_integral do rewrite fimfunE -sumEFin.
rewrite ge0_integral_sum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun.
    apply: measurable_funM => //; first exact: measurable_fun_cst.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) r)).
  - by move=> r x _; rewrite muleindic_ge0.
under eq_bigr; first by move=> r _; rewrite integralM_indic'//; over.
rewrite /= (big_fsetD1 (f_ n a))/=; last first.
  by rewrite in_fset_set// in_setE; exists a.
rewrite integral_indic// measure_diracE setIT mem_set// mule1.
rewrite big1_fset ?adde0// => r; rewrite !inE => /andP[rfna _] _.
rewrite integral_indic// measure_diracE setIT memNset ?mule0//=.
by move=> /esym; apply/eqP.
Qed.

End integral_dirac.

Section measure_image.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (f : T1 -> T2).
Hypothesis mf : measurable_fun setT f.
Variables (R : realType) (m : {measure set T1 -> \bar R}).

Definition measure_image' A := m (f @^-1` A).

Lemma measure_image'0 : measure_image' set0 = 0.
Proof. by rewrite /measure_image' preimage_set0 measure0. Qed.

Lemma measure_image'_ge0 A : 0 <= measure_image' A.
Proof. by apply: measure_ge0; rewrite -[X in measurable X]setIT; apply: mf. Qed.

Lemma measure_image'_sigma_additive : semi_sigma_additive measure_image'.
Proof.
move=> F mF tF mUF; rewrite /measure_image' preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: mf.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mf.
Qed.

Definition measure_image : {measure set T2 -> \bar R} :=
  locked (Measure.Pack _ (Measure.Axioms
    measure_image'0 measure_image'_ge0 measure_image'_sigma_additive)).

Lemma measure_imageE A : measure_image A = m (f @^-1` A).
Proof. by rewrite /measure_image; unlock. Qed.

End measure_image.
(* /NB: PR in progress *)

(* TODO: move to measure.v? *)
Section transfer.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (phi : T1 -> T2).
Hypothesis mphi : measurable_fun setT phi.
Variables (R : realType) (mu : {measure set T1 -> \bar R}).

Lemma transfer (f : T2 -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int_ setT (f y) 'd (measure_image mphi mu)[y] =
  \int_ setT ((f \o phi) x) 'd mu[x].
Proof.
move=> mf f0.
pose pt2 := phi point.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity
    (lim (fun n => \int_ setT (f_ n x)%:E 'd (measure_image mphi mu)[x])).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; apply/lefP/ndf_.
rewrite (_ : (fun _ => _) =
    (fun n => \int_ setT ((EFin \o f_ n \o phi) x) 'd mu[x])).
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
transitivity (\sum_(k <- fset_set [set of f_ n])
  \int (k * \1_(((f_ n) @^-1` [set k]) \o phi) x)%:E 'd mu[x]).
  under eq_integral do rewrite fimfunE -sumEFin.
  rewrite ge0_integral_sum//; last 2 first.
    - move=> y; apply/EFin_measurable_fun; apply: measurable_funM.
        exact: measurable_fun_cst.
      by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) y)).
    - by move=> y x _; rewrite muleindic_ge0.
  apply eq_bigr => r _; rewrite integralM_indic'// integral_indic//.
  rewrite measure_imageE.
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
  by rewrite integral_cst// probability_setT mule1 lte_pinfty.
- rewrite (eq_integral (EFin \o cst_mfun (- k)))//; last first.
    by move=> x _ /=; rewrite ltr0_norm.
  rewrite integral_cst//.
  by rewrite probability_setT mule1 lte_pinfty.
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

Definition expectation (X : {RV P >-> R}) := \int (X w)%:E 'd P[w].
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

Lemma expectationD : 'E (X `+ Y) = 'E X + 'E Y.
Proof. by rewrite /expectation integralD_EFin. Qed.

Lemma expectationB : 'E (X `- Y) = 'E X - 'E Y.
Proof. by rewrite /expectation integralB_EFin. Qed.

End expectation_lemmas.

Section square_integrable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Definition square_integrable (D : set T) (f : T -> R) :=
  (\int_ D (`| f x | ^+ 2)%:E 'd mu[x] < +oo)%E.
Lemma square_integrableP (D : set T) (f : T -> R) :
  measurable D -> measurable_fun D f ->
  square_integrable D f <-> mu.-integrable D (EFin \o (fun x => `|f x| ^+ 2)).
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
  measure_image (@measurable_funP _ _ X) P.

Lemma distribution_is_probability : distribution [set: R] = 1%:E.
Proof.
by rewrite /distribution /= measure_imageE preimage_setT probability_setT.
Qed.

Definition probability_of_distribution : probability _ R :=
  Probability.mk distribution_is_probability.

End distribution.

Section transfer_probability.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (P : probability T R) (X : {RV P >-> R}).

Lemma transfer_probability (f : R -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int_ setT (f y) 'd (distribution X)[y] =
  \int_ setT ((f \o X) x) 'd P[x].
Proof.
by move=> mf f0; rewrite transfer.
Qed.

End transfer_probability.

Require Import functions.

Section subadditive_countable.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Local Open Scope ereal_scope.

(* PR: in progress *)
Lemma integral_set0 (f : T -> \bar R) : \int_ set0 (f x) 'd mu[x] = 0.
Proof.
Admitted.

Lemma restrict_lee {aT} {rT : numFieldType} (D E : set aT) (f : aT -> \bar rT) :
  (forall x, E x -> 0 <= f x) ->
  D `<=` E -> forall x, ((f \_ D) x <= (f \_ E) x)%E.
Proof.
Admitted.

Lemma integral_bigsetU (F : (set T)^nat) (mF : forall n, measurable (F n))
    (f : T -> \bar R) n :
  let D := \big[setU/set0]_(i < n) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset `I_n F ->
  \int_ D (f x) 'd mu[x] = \sum_(i < n) \int_ (F i) (f x) 'd mu[x].
Proof.
Admitted.

Lemma ge0_integral_bigcup (F : (set _)^nat) (f : T -> \bar R) :
  (forall x, 0 <= f x)%E ->
  trivIset setT F ->
  (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) f ->
  (\int_ (\bigcup_i F i) (f x) 'd mu[x] =
   \sum_(i <oo) \int_ (F i) (f x) 'd mu[x])%E.
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
  summable [set: nat] (fun i => \int_ (F i) g x 'd mu[x]).
Proof.
Admitted.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int_ (\bigcup_i F i) (g x) 'd mu[x] = \sum_(i <oo) \int_ (F i) (g x) 'd mu[x])%E.
Proof.
(* /PR in progress *)
Admitted.
End subadditive_countable.

Module DiscreteDistribution.
Section discrete_distribution.
Local Open Scope form_scope.
Variables (T : measurableType) (R : realType) (P : probability T R)
          (X : {RV P >-> R}).
Record t := mk {
  c : R^nat ; c0 : forall n, (0 <= c n)%R ; c1 : (\sum_(n <oo) (c n)%:E = 1)%E ;
  a : {injfun [set: nat] >-> [set: R]} ;
  E : distribution X =1 (fun A => \sum_(n <oo) (c n)%:E * (\d_ (a n) A))%E
}.
(*Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Record t := mk {
  c : R^nat ; c0 : forall n, (0 <= c n)%R ; c1 : (\sum_(n <oo) (c n)%:E = 1)%E ;
  a : {injfun [set: nat] >-> [set: T]} ;
  E : mu =1 (fun A => \sum_(n <oo) (c n)%:E * (\d_ (a n) A))%E
}.*)
End discrete_distribution.
Module Exports.
Notation discrete_distribution := t.
End Exports.
End DiscreteDistribution.
Export DiscreteDistribution.Exports.

Lemma nneseries0 (R : realFieldType) (f : (\bar R)^nat) :
  (forall i, f i = 0%E) -> (\sum_(i <oo) f i = 0)%E.
Admitted. (*NB: this is in master*)

Lemma preimage10' {T R : Type} {f : T -> R} {x : R} :
  f @^-1` [set x] = set0 -> ~ range f x.
Proof.
rewrite /image /=.
apply: contraPnot => -[t _ <-].
rewrite /preimage/=.
by move/seteqP => -[+ _] => /(_ t) /=.
Qed.

Section discrete_distribution.
Variables (T : measurableType) (R : realType) (P : probability T R)
  (X : {RV P >-> R}) (d : discrete_distribution X).

Notation C := (DiscreteDistribution.c d).
Notation A := (DiscreteDistribution.a d).

Lemma test0 r : P [set x | X x = r] = distribution X [set r].
Proof. by rewrite /distribution /= measure_imageE. Qed.

Lemma test1 (n : nat) : distribution X [set A n] = (C n)%:E.
Proof.
rewrite (DiscreteDistribution.E d).
rewrite ereal_pseries_esum; last first.
  by move=> m _; rewrite mule_ge0// lee_fin DiscreteDistribution.c0.
rewrite (esumID [set n]); last first.
  by move=> m _; rewrite mule_ge0// lee_fin DiscreteDistribution.c0.
rewrite addeC esum0 ?add0e; last first.
  move=> m [_ /= mn].
  rewrite measure_diracE/=.
  rewrite memNset ?mule0//=.
  apply: contra_not mn.
  exact/injT.
rewrite (_ : _ `&` _ = [set n]); last exact/seteqP.
rewrite csum_set1.
  by rewrite measure_diracE /= mem_set ?mule1//.
move=> t.
by rewrite mule_ge0// lee_fin DiscreteDistribution.c0.
Qed.

Lemma abse1 : `|1|%E = 1%E :> \bar R.
Proof. by rewrite /abse normr1. Qed.

Lemma discrete_expectation :
   (forall t, exists n, X t = A n) (*X takes only the values A n*) ->
   P.-integrable setT (EFin \o X) ->
  'E X = (\sum_(n <oo) (C n)%:E * (A n)%:E)%E.
Proof.
move=> XA ix.
rewrite /expectation.
have H1 : \bigcup_k X @^-1` [set A k] = setT.
  apply/seteqP; split => // t _.
  rewrite /bigcup /=.
  by have [n XtAn] := XA t; exists n.
rewrite -H1.
have H2 : trivIset setT (fun k => [set A k]).
  move=> i j _ _ [/= r []]; case: d => c c0 c1 /= a dXE rai raj.
  by apply: (@injT _ _ a) => /=; rewrite -rai -raj.
have H3 : trivIset [set: nat] (fun i : nat => X @^-1` [set A i]).
  apply/trivIsetP => /= i j _ _ ij.
  move/trivIsetP : H2 => /(_ i j Logic.I Logic.I ij) Aij.
  by rewrite -preimage_setI Aij preimage_set0.
rewrite integral_bigcup//; last first.
  apply: (integrableS measurableT) => //.
  exact: bigcup_measurable.
transitivity ((\sum_(i <oo) \int_ (X @^-1` [set A i]) (A i)%:E 'd P[x])%E).
  apply eq_ereal_pseries => i.
  apply eq_integral => t.
  by rewrite in_setE/= => ->.
transitivity ((\sum_(i <oo) (A i)%:E * \int_ (X @^-1` [set A i]) 1 'd P[x])%E).
  apply eq_ereal_pseries => i.
  rewrite -integralM//; last first.
    split => //.
      exact: measurable_fun_cst.
    rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
    rewrite integral_cst// mul1e (@le_lt_trans _ _ 1%E) ?lte_pinfty//.
    exact: probability_le1.
  congr integral.
  apply funext => y.
  by rewrite mule1.
apply eq_ereal_pseries => k.
rewrite muleC.
congr (_ * _)%E.
by rewrite integral_cst//= mul1e test0 test1.
Qed.

End discrete_distribution.
