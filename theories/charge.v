(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference finmap fingroup perm rat.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets cardinality.
From mathcomp Require Import functions fsbigop set_interval reals ereal.
From mathcomp Require Import topology numfun normedtype derive sequences esum.
From mathcomp Require Import measure realfun measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

Attributes deprecated(since="mathcomp-analysis 1.17.0",
  note="use `measure.v` (which exports `signed_measure.v`)
  or/and `lebesgue_integral.v` (which exports `radon_nikodym.v`)
  instead.").
