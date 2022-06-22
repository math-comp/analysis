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
move=> U; rewrite /sum_of_kernels /= /mseries.
rewrite [X in measurable_fun _ X](_ : _ =
  (fun x => elim_sup (fun n => \sum_(0 <= i < n) k i x U))); last first.
  apply/funext => x; rewrite -lim_mkord is_cvg_elim_supE.
    by rewrite -lim_mkord.
  exact: is_cvg_nneseries.
apply: measurable_fun_elim_sup => n.
by apply: measurable_fun_sum => *; exact/kernel_measurable_fun.
Qed.

HB.instance Definition _
    (R : realType) (X Y : measurableType)
    (k : (kernel R X Y)^nat) :=
  isKernel.Build R X Y (sum_of_kernels k)
    (kernel_measurable_fun_sum_of_kernels k).

(* PR in progress *)
Section ge0_integral_measure_series.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (m_ : {measure set T -> \bar R}^nat).
Let m := measure_series m_ O.

Lemma ge0_integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall t, D t -> 0 <= f t) ->
  measurable_fun D f ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Admitted.
End ge0_integral_measure_series.

Lemma proposition1
  (R : realType) (X Y : measurableType)
  (k : (kernel R X Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun setT f ->
  \int[sum_of_kernels k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /sum_of_kernels/= ge0_integral_measure_series.
Qed.

HB.mixin Record isFiniteKernel
    (R : realType) (X Y : measurableType)
    (k : X -> {measure set Y -> \bar R})
    of isKernel R X Y k := {
  finite_kernel : exists r : R, forall x : X, k x setT < r%:E
}.

HB.structure Definition FiniteKernel
    (R : realType) (X Y : measurableType) :=
  {k & isFiniteKernel R X Y k }.

HB.mixin Record isSFiniteKernel
    (R : realType) (X Y : measurableType)
    (k : X -> {measure set Y -> \bar R})
    of isKernel R X Y k := {
  finite_kernel : exists k_ : (X ^^> Y)^nat, forall x U,
    k x U = \sum_(i <oo) k_ i x U
}.

#[short(type=sfinitekernel)]
HB.structure Definition SFiniteKernel
    (R : realType) (X Y : measurableType) :=
  {k & isSFiniteKernel R X Y k}.

Section starkernel.
Variables (R : realType) (X Y Z : measurableType).
Variable k : sfinitekernel R [the measurableType of (X * Y)%type] Z.
Variable l : sfinitekernel R X Y.

Definition star_kernel' : X -> set Z -> \bar R :=
  fun x => fun U => \int[l x]_y k (x, y) U.

Let star_kernel'0 (x : X) : star_kernel' x set0 = 0.
Proof.
rewrite /star_kernel' (eq_integral (cst 0)) ?integral0// => y _.
by rewrite measure0.
Qed.

Let star_kernel'_ge0 (x : X) (U : set Z) : 0 <= star_kernel' x U.
Proof. by apply: integral_ge0 => y _; exact: measure_ge0. Qed.

Let star_kernel'_sigma_additive (x : X) : semi_sigma_additive (star_kernel' x).
Proof.
move=> F mF tF mUF; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (F n)))%E; last first.
  apply: eq_integral => U _.
  by apply/esym/cvg_lim => //; apply/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE// integral_sum// => n.
move: (@kernel_measurable_fun R _ _ k (F n)) => /measurable_fun_prod1.
exact.
Qed.

Canonical star_kernel : X -> {measure set Z -> \bar R} :=
  fun x => Measure.Pack _ (Measure.Axioms (star_kernel'0 x) (star_kernel'_ge0 x)
    (@star_kernel'_sigma_additive x)).

End starkernel.

Lemma lemma3 (R : realType) (X Y Z : measurableType)
  (k : sfinitekernel R [the measurableType of (X * Y)%type] Z)
  (l : sfinitekernel R X Y) : forall x f,
  \int[star_kernel k l x]_z f z =
  \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
(* TODO *)
Admitted.
