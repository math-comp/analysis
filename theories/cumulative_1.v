(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat archimedean.
From HB Require Import structures.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions fsbigop cardinality.
From mathcomp Require Import reals ereal interval_inference topology numfun.
From mathcomp Require Import normedtype sequences esum real_interval measure.
From mathcomp Require Import realfun.

(**md**************************************************************************)
(* # Lebesgue Stieltjes Measure                                               *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue-Stieltjes measure using *)
(* the Measure Extension theorem from measure.v.                              *)
(*                                                                            *)
(* References:                                                                *)
(* - Achim Klenke. Probability Theory 2nd edition. 2014                       *)
(* - Y. Ishiguro, R. Affeldt. The Radon-Nikodym Theorem and the Lebesgue-     *)
(*   Stieltjes measure in Coq. Computer Software 41(2).2024                   *)
(*                                                                            *)
(* ```                                                                        *)
(*           right_continuous f == the function f is right-continuous         *)
(*                 cumulative R == type of non-decreasing, right-continuous   *)
(*                                 functions (with R : numFieldType)          *)
(*                                 The HB class is Cumulative.                *)
(*                                 instance: idfun                            *)
(*                 ocitv_type R == alias for R : realType                     *)
(*                        ocitv == set of open-closed intervals ]x, y] where  *)
(*                                 x and y are real numbers                   *)
(*                     R.-ocitv == display for ocitv_type R                   *)
(*         R.-ocitv.-measurable == semiring of sets of open-closed intervals  *)
(*                  wlength f A := f b - f a with the hull of the set of real *)
(*                                 numbers A being delimited by a and b       *)
(* lebesgue_stieltjes_measure f == Lebesgue-Stieltjes measure for f           *)
(*                                 f is a cumulative function.                *)
(* completed_lebesgue_stieltjes_measure f == the completed Lebesgue-Stieltjes *)
(*                                 measure                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "R .-ocitv" (at level 1, format "R .-ocitv").
Reserved Notation "R .-ocitv.-measurable"
 (at level 2, format "R .-ocitv.-measurable").

(* TODO: move? *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

Lemma right_continuousW (R : numFieldType) {d} (U : orderTopologicalType d)
  (f : R -> U) : continuous f -> right_continuous f.
Proof. by move=> cf x; apply: cvg_within_filter; exact/cf. Qed.

HB.mixin Record isCumulative (R : numFieldType) {d} (U : orderTopologicalType d)
  (f : R -> U) := {
  cumulative_is_nondecreasing : nondecreasing f ;
  cumulative_is_right_continuous : right_continuous f }.

#[short(type=cumulative)]
HB.structure Definition Cumulative
  (R : numFieldType) {d} (U : orderTopologicalType d) := { f of isCumulative R d U f }.

Arguments cumulative_is_nondecreasing {R d U} _.
Arguments cumulative_is_right_continuous {R d U} _.

Section id_is_cumulative.
Variable R : realType.

Let id_nd : {homo @idfun R : x y / x <= y}.
Proof. by []. Qed.

Let id_rc : right_continuous (@idfun R). 
Proof. apply: right_continuousW=> x; exact: cvg_id. Qed. (* fail *)

HB.instance Definition _ := isCumulative.Build R _ R idfun id_nd id_rc.
End id_is_cumulative.
