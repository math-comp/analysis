(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Export signed.
Require Import boolp nngnum.

(******************************************************************************)
(* This file develops tools to make the manipulation of positive numbers      *)
(* easier, thanks to canonical structures.                                    *)
(*                                                                            *)
(*          !! x == triggers pretyping to fill the holes of the term x. The   *)
(*                  main use case is to trigger typeclass inference in the    *)
(*                  body of a ssreflect have := !! body.                      *)
(*                  Credits: Enrico Tassi.                                    *)
(*    {posnum R} == interface type for elements in R that are positive; R     *)
(*                  must have a numDomainType structure.                      *)
(*                  Allows to solve automatically goals of the form x > 0 if  *)
(*                  x is canonically a {posnum R}. {posnum R} is canonically  *)
(*                  stable by addition, multiplication, inverse, min and sqrt *)
(*                  All positive natural numbers ((n.+1)%:R) are also         *)
(*                  canonically in {posnum R}                                 *)
(*   PosNum xgt0 == packs the proof xgt0 : x > 0, for x : R, to build a       *)
(*                  {posnum R}.                                               *)
(*        x%:pos == explicitly casts x to {posnum R}, triggers the inference  *)
(*                  of a {posnum R} structure for x.                          *)
(*        x%:num == explicit cast from {posnum R} to R.                       *)
(*       posreal == notation for {posnum R}, where R is the type of real      *)
(*                  numbers.                                                  *)
(*             2 == notation for 2%:R.                                        *)
(*    [gt0 of x] == infers a {posnum R} structure for x and outputs the proof *)
(*                  that x is positive.                                       *)
(******************************************************************************)

Reserved Notation "x %:numpos" (at level 2, left associativity, format "x %:numpos").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Notation numpos := (@num _ _ 0 !=0 >=0).
Notation "x %:numpos" := (numpos x).
