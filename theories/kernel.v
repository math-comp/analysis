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
  (fun x => elim_sup (fun n => \sum_(i < n) k i x U))); last first.
  apply/funext => x.
  rewrite -lim_mkord.
  (* TODO: see cvg_lim_supE *)
  admit.
apply: measurable_fun_elim_sup => n.
(*TODO: use measurable_funD *)
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
rewrite /sum_of_kernels/=.
(* TODO *)
Abort.

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

Definition star_kernel' (R : realType) (X Y Z : measurableType)
  (k : sfinitekernel R [the measurableType of (X * Y)%type] Z)
  (l : sfinitekernel R X Y) : X -> set Z -> \bar R :=
  fun x => fun U => \int[l x]_y k (x, y) U.

Definition star_kernel (R : realType) (X Y Z : measurableType)
  (k : sfinitekernel R [the measurableType of (X * Y)%type] Z)
  (l : sfinitekernel R X Y) : X -> {measure set Z -> \bar R}.
(* TODO *)
Admitted.

Lemma lemma3 (R : realType) (X Y Z : measurableType)
  (k : sfinitekernel R [the measurableType of (X * Y)%type] Z)
  (l : sfinitekernel R X Y) : forall x f,
  \int[star_kernel k l x]_z f z =
  \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
(* TODO *)
Admitted.
