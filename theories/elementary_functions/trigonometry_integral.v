(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrint ssrnum matrix
  interval_inference interval rat.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals topology ereal normedtype.
From mathcomp Require Import landau sequences derive realfun exp realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral ftc.
From mathcomp Require Import trigonometry_functions.

(**md**************************************************************************)
(* # Theory of trigonometric functions (integral)                             *)
(*                                                                            *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Atan.
Context {R : realType}.
Implicit Type x : R.

Let mu := @lebesgue_measure R.

Lemma integral0_oneDsqr b : 0 <= b ->
  \int[mu]_(x in `[0, b]) (oneDsqr x)^-1 = atan b.
Proof.
rewrite le_eqVlt => /predU1P[<-|b0].
  by rewrite set_itv1 Rintegral_set1 atan0.
rewrite /Rintegral (@continuous_FTC2 _ _ atan)//.
- by apply: continuous_in_subspaceT => x ?; exact: continuous_oneDsqrV.
- split.
  + by move=> x _; exact: derivable_atan.
  + by apply: cvg_at_right_filter; exact: continuous_atan.
  + by apply: cvg_at_left_filter; exact: continuous_atan.
- by move=> x x01; rewrite derive1_atan// mul1r.
- by rewrite atan0 sube0.
Qed.

Import MeasurableR.

Lemma integral0y_oneDsqr :
  (\int[mu]_(x in `[0%R, +oo[) (oneDsqr x)^-1%:E = (pi / 2)%:E)%E.
Proof.
rewrite (ge0_continuous_FTC2y _ _ cvgy_atan)/=.
- by move=> x _; rewrite invr_ge0.
- apply/continuous_within_itvcyP; split.
    by move=> x x0; apply: continuous_oneDsqrV.
  by apply: cvg_at_right_filter; exact: continuous_oneDsqrV.
- move=> x x0; apply: ex_derive.
- by apply: cvg_at_right_filter; exact: continuous_atan.
- by move=> x _; rewrite derive1E; exact: derive_val.
- by rewrite atan0 oppr0 addr0.
Qed.

End Atan.
