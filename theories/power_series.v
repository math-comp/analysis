(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat poly.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.

(******************************************************************************)
(* This file is a scratch file with the goal of defining power series (wip).  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*           ??? == notation for power series,                                *)
(*           ??? == radius of convergence                                     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def  Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "p `.[ x ]"
  (at level 2, left associativity, format "p `.[ x ]").

Section formal_power_series.
Variable R : realType.

(*TODO: Definition formal_power_series := R^nat.*)

Definition fps_add (f g : R^nat) := (f \+ g).

Definition cauchy_product (a b : R^nat) : R^nat :=
  [sequence \sum_(0 <= k < n) (a k * b (n - k)%N)]_n.

End formal_power_series.
(* TODO: this forms a ringType *)

Section power_series_definition.
Variable R : realType.
Implicit Types f g : R^nat.

Definition power_series f (x : R) : R^nat :=
  series (fun i => (f i *: 'X^i).[x]).

Local Notation "f `.[ x ]" := (power_series f x).

End power_series_definition.
Notation "p `.[ x ]" := (power_series p x) : ring_scope.

Section examples.
Variable R : realType.

Local Definition exp_coeff : R^nat := [sequence 1 / n`!%:R]_n.
Local Definition expR x : R := lim exp_coeff`.[x].

Local Definition sin_coeff : R^nat :=
  [sequence (odd n)%:R * (- 1) ^+ n.-1./2 * n`!%:R^-1]_n.
Local Definition sin x : R := lim sin_coeff`.[x].

End examples.

Section radius.
Variable R : realType.
Implicit Types f g : R^nat.

Definition power_series_radius (f : R^nat) : set R := fun r =>
  forall x, (`|x| < r -> cvg [normed f`.[x] ]) /\
       (`|x| > r -> ~ cvg f`.[x]).

Lemma power_series_radius_exists f : exists r, power_series_radius f r.
Proof.
Admitted.

Definition radius_of_convergence f : R := get (power_series_radius f).

Lemma radius_normed_convergenceP f x :
  `|x| < radius_of_convergence f -> cvg [normed f`.[x] ].
Proof.
Abort.

Lemma power_series_mul_cvg f g x : cvg f`.[x] -> cvg g`.[x] ->
  cvg (cauchy_product f g)`.[x] /\
  lim (cauchy_product f g)`.[x] = lim f`.[x] * lim g`.[x].
Proof.
Abort.

(* TODO: Lemma ratio_test : ... *)

End radius.
