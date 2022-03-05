(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect fingroup ssralg poly ssrnum.
Require Import boolp.
Require Export signed.

(******************************************************************************)
(* This file develops tools to make the manipulation of non-negative numbers  *)
(* easier, on the model of posnum.v. This is WIP.                             *)
(*                                                                            *)
(*   {nonneg R} == interface types for elements in R that are non-negative; R *)
(*                 must have a numDomainType structure. Automatically solves  *)
(*                 goals of the form x >= 0. {nonneg R} is stable by          *)
(*                 addition, multiplication. All natural numbers n%:R are     *)
(*                 also canonically in {nonneg R}.                            *)
(*                 This type is also shown to be a latticeType, a             *)
(*                 distrLatticeType, and an orderType,                        *)
(*  NngNum xge0 == packs the proof xge0 : x >= 0, for x : R, to build a       *)
(*                 {nonneg R}                                                 *)
(*       x%:nng == explicitly casts x to {nonneg R}, triggers the inference   *)
(*                 of a {nngum R} structure for x                             *)
(*    x%:nngnum == explicit cast from {nonneg R} to R                         *)
(*                                                                            *)
(* The module BigmaxrNonneg contains a theory about bigops of the form        *)
(* \big[maxr/x]_(i | P i) F i where F : I -> {nonneg R} which is used in      *)
(* normedtype.v to develop the topology of matrices.                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Reserved Notation "x %:nngnum" (at level 2, left associativity, format "x %:nngnum").

Notation nngnum := (@num _ _ 0 ?=0 >=0).
Notation "x %:nngnum" := (nngnum x).

Import Num.Def.
