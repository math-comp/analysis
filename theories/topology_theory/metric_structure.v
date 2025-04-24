(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals topology.
From mathcomp Require Import function_spaces real_interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record PseudoMetric_isMetric (K : realFieldType) M of PseudoMetric K M := {
  mdist : M -> M -> K ;
  mdist_ge0 : forall x y, 0 <= mdist x y ;
  mdist_positivity : forall x y, mdist x y = 0 -> x = y;
  ballEmdist : forall x d, ball x d = [set y | mdist x y < d]
}.

#[short(type="metricType")]
HB.structure Definition MetricType (K : realFieldType) :=
  { M of PseudoMetric K M & PseudoMetric_isMetric K M }.

Section metric_lemmas.
Variables (K : realFieldType) (M : metricType K).

Let dist := @mdist K M.

Lemma metric_sym x y : dist x y = dist y x.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; rewrite leNgt; apply/negP => xy.
- have := @ball_sym _ _ y x (dist x y); rewrite !ballEmdist/= => /(_ xy).
  by rewrite ltxx.
- have := @ball_sym _ _ x y (dist y x); rewrite !ballEmdist/= => /(_ xy).
  by rewrite ltxx.
Qed.

Lemma metricxx x : dist x x = 0.
Proof.
apply/eqP; rewrite eq_le mdist_ge0 andbT; apply/ler_addgt0Pl => /= e e0.
rewrite addr0 leNgt; apply/negP => exx.
by have := @ball_center _ _ x (PosNum e0); rewrite ballEmdist/= ltNge (ltW exx).
Qed.

Lemma metric_triangle x y z : dist x z <= dist x y + dist y z.
Proof.
apply/ler_addgt0Pl => /= e e0; rewrite leNgt; apply/negP => xyz.
have := @ball_triangle _ _ y x z (dist x y + e / 2) (dist y z + e / 2).
rewrite !ballEmdist/= addrACA -splitr !ltrDl !divr_gt0// => /(_ isT isT).
by rewrite ltNge => /negP; apply; rewrite addrC ltW.
Qed.

Lemma metric_hausdorff : hausdorff_space M.
Proof.
move=> p q pq; apply: contrapT => qp; move: pq.
pose D := dist p q / 2; have D0 : 0 < D.
  rewrite divr_gt0// lt_neqAle mdist_ge0 andbT eq_sym.
  by move/eqP: qp; apply: contra => /eqP/mdist_positivity ->.
have p2Dq : ~ ball p (dist p q) q by rewrite ballEmdist/= ltxx.
move=> /(_ (ball p _) (ball q _) (nbhsx_ballx _ _ D0) (nbhsx_ballx _ _ D0)).
move/set0P/eqP; apply; rewrite -subset0 => x [pDx /ball_sym qDx].
by have := ball_triangle pDx qDx; rewrite -splitr.
Qed.

End metric_lemmas.
