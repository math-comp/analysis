DST=$1
coqtop -Q classical mathcomp.classical -Q reals mathcomp.reals -Q reals_stdlib mathcomp.reals_stdlib -Q experimental_reals mathcomp.experimental_reals -Q theories mathcomp.analysis -Q analysis_stdlib mathcomp.analysis_stdlib <<EOF
From HB Require Import structures.
Require Import mathcomp.classical.all_classical.
Require Import mathcomp.analysis.all_analysis.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.all_reals.
Import mathcomp.analysis.lebesgue_integral_theory.simple_functions.HBSimple.
Import mathcomp.analysis.lebesgue_integral_theory.simple_functions.HBNNSimple.
Require Import mathcomp.analysis_stdlib.Rstruct_topology.
HB.graph "$DST".
EOF
