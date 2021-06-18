(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.

(******************************************************************************)
(*                Definitions and lemmas about power series                   *)
(*                                                                            *)
(* The purpose of this file is to gather generic definitions and lemmas about *)
(* power series.                                                              *)
(* Definitions:                                                               *)
(*           ??? == notation for power series,                                *)
(*           ??? == radius of convergence *)
(*                                                                            *)
(******************************************************************************)

(* Power series *)
(*   we want a notation for the following pattern:
     series (fun i =>    f i * x ^+ i) *)

power_series f := series (fun i => f i * 'X ^ i)
fun_defined_by_power_series f := lim (series (fun i => f i * 'X ^+ i))

for a power_series ps,
ps.[(x:R)] := series (fun i => (ps i).[x])


(* possible example usage *)
Definition exp_coeff' := [sequence 1 / n`!%:R]_n.
Definition expR := [power_series exp_coeff'].

Lemma power_series_has_a_radius_of_convergence :
  forall ps : power_series_T, exists rad : R,
      (forall x, x < rad -> cvg ps.[x]) /\
      (forall x, x > rad -> ~ cvg ps.[x]).

Definition radius_of_convergence (ps : power_series_T) : R :=
  get (power_series_has_a_radius_of_convergence ps). (* = rad *)

Lemma ratio_test : ...
