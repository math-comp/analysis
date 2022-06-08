(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

HB.mixin Record isKernel
    (R : realType) (X Y : measurableType)
    (k : X -> {measure set Y -> \bar R}) := {
  kernel_measurable_fun :
    forall U, measurable_fun setT (k ^~ U)
}.

#[short(type=kernel)]
HB.structure Definition Kernel
    (R : realType) (X Y : measurableType) :=
  {k & isKernel R X Y k}.
Notation "X ^^> Y" := (kernel _ X Y) (at level 42).

HB.mixin Record isProbabilityKernel
    (R : realType) (X Y : measurableType)
    (k : X -> {measure set Y -> \bar R})
    of isKernel R X Y k := {
  prob_kernel : forall x : X, k x setT = 1
}.

HB.structure Definition ProbKernel
    (R : realType) (X Y : measurableType) :=
  {k & isProbabilityKernel R X Y k }.
(* TODO: warning *)

Definition sum_of_kernels
    (R : realType) (X Y : measurableType)
    (k : (X ^^> Y)^nat) : X -> {measure set Y -> \bar R} :=
  fun x => [the {measure _ -> _} of mseries (k ^~ x) 0].

Lemma kernel_measurable_fun_sum_of_kernels
    (R : realType) (X Y : measurableType)
    (k : (kernel R X Y)^nat) :
  forall U, measurable_fun setT ((sum_of_kernels k) ^~ U).
Proof.
Admitted.

HB.instance Definition _
    (R : realType) (X Y : measurableType)
    (k : (kernel R X Y)^nat) :=
  isKernel.Build R X Y (sum_of_kernels k)
    (kernel_measurable_fun_sum_of_kernels k).

Lemma proposition1
  (R : realType) (X Y : measurableType)
  (k : (kernel R X Y)^nat) (f : Y -> \bar R) x :
 \int[sum_of_kernels k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
(* TODO *)
Abort.
