(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals topology.
From mathcomp Require Import function_spaces prodnormedzmodule real_interval.
From mathcomp Require Import tvs pseudometric_normed_Zmodule normed_module.

(**md**************************************************************************)
(* # Complete normed modules                                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*      completeNormedModType K == interface type for a complete normed       *)
(*                                 module structure over a realFieldType K    *)
(*                                 The HB class is CompleteNormedModule.      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

#[short(type="completeNormedModType")]
HB.structure Definition CompleteNormedModule (K : numFieldType) :=
  {T of NormedModule K T & Complete T}.

Lemma R_complete (R : realType) (F : set_system R) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchy_ballP F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) down A.
have /cauchy_ballP /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup D; first split.
- exists (x0 - 1) => A FA.
  near F => x.
  apply/downP; exists x; first by near: x.
  by rewrite ler_distlBl // ltW //; near: x.
- exists (x0 + 1); apply/ubP => x /(_ _ x01) /downP [y].
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltrBlDr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup D).
apply/cvgrPdist_le => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl; move/ubP: (sup_upper_bound D_has_sup) => -> //=.
  apply: ge_sup => //; first by case: D_has_sup.
  have Fxeps : F (ball_ [eta normr] x eps%:num).
    by near: x; apply: nearP_dep; apply: F_cauchy.
  apply/ubP => y /(_ _ Fxeps) /downP[z].
  rewrite /ball_/= ltr_distl ltrBlDr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite /D /= => A FA; near F => y.
apply/downP; exists y.
  by near: y.
rewrite lerBlDl -lerBlDr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ (R : realType) := Uniform_isComplete.Build R^o
  (@R_complete R). (* TODO: delete *)

HB.instance Definition _ (R : realType) := Complete.copy R R^o.
