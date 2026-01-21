From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat interval_inference.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences esum measure lebesgue_measure numfun.
From mathcomp Require Import lebesgue_integral exp kernel trigo prob_lang.
From mathcomp Require Import realfun charge probability derive ftc.
From mathcomp Require Import gauss_integral.

(**md**************************************************************************)
(* wip waiting for the Poisson distribution                                   *)
(*                                                                            *)
(* Another example from Section 4.2 in [Equation (13), Staton, ESOP 2017].    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* Staton's definition of the counting measure
   [equation (13), Sect. 4.2, Staton ESOP 2017] *)
Section staton_counting.
Context d (X : measurableType d).
Variable R : realType.
Notation mu := (@lebesgue_measure R).
Import Notations.
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pmf R x k)%:E = 1%E)%E.

Let f1 n := (@poisson_pmf R 1%R n)^-1%R.

Let mf1 : measurable_fun setT f1.
Proof.
rewrite /f1 /poisson_pmf.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- move=> /= r [t ? <-].
  by case: ifPn => // t0; rewrite gt_eqF ?mulr_gt0 ?expR_gt0//= invrK ltr0n.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
Qed.

Definition staton_counting (r : R) : R.-sfker X ~> _ :=
  letin (sample_cst (@poisson_prob R r 1%N))
    (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

End staton_counting.
