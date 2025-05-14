(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import interval_inference reals topology_structure.
From mathcomp Require Import uniform_structure pseudometric_structure.
From mathcomp Require Import num_topology product_topology separation_axioms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record isMetric (K : numDomainType) M of PseudoMetric K M := {
  mdist : M -> M -> K ;
  mdist_ge0 : forall x y, 0 <= mdist x y ;
  mdist_positivity : forall x y, mdist x y = 0 -> x = y;
  ballEmdist : forall x d, ball x d = [set y | mdist x y < d]
}.

#[short(type="metricType")]
HB.structure Definition Metric (K : numDomainType) :=
  { M of PseudoMetric K M & isMetric K M }.

Section metric_lemmas.
Context {R : realFieldType} (T : metricType R).

Let dist := @mdist R T.

Lemma metric_sym x y : dist x y = dist y x.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; rewrite leNgt; apply/negP => xy.
- have := @ball_sym _ _ y x (dist x y); rewrite !ballEmdist/= => /(_ xy).
  by rewrite ltxx.
- have := @ball_sym _ _ x y (dist y x); rewrite !ballEmdist/= => /(_ xy).
  by rewrite ltxx.
Qed.

Lemma mdistxx x : dist x x = 0.
Proof.
apply/eqP; rewrite eq_le mdist_ge0 andbT; apply/ler_addgt0Pl => /= e e0.
rewrite addr0 leNgt; apply/negP => exx.
by have := @ball_center _ _ x (PosNum e0); rewrite ballEmdist/= ltNge (ltW exx).
Qed.

Lemma mdist_gt0 x y : (0 < dist x y) = (x != y).
Proof.
rewrite lt_neqAle mdist_ge0 andbT.
apply/negPn/negPn => [/eqP/esym/mdist_positivity/eqP//|/eqP ->].
by rewrite mdistxx.
Qed.

Lemma metric_triangle x y z : dist x z <= dist x y + dist y z.
Proof.
apply/ler_addgt0Pl => /= e e0; rewrite leNgt; apply/negP => xyz.
have := @ball_triangle _ _ y x z (dist x y + e / 2) (dist y z + e / 2).
rewrite !ballEmdist/= addrACA -splitr !ltrDl !divr_gt0// => /(_ isT isT).
by rewrite ltNge => /negP; apply; rewrite addrC ltW.
Qed.

Lemma metric_hausdorff : hausdorff_space T.
Proof.
move=> p q pq; apply: contrapT => qp; move: pq.
pose D := dist p q / 2; have D0 : 0 < D.
  by rewrite divr_gt0// mdist_gt0; exact/eqP.
have p2Dq : ~ ball p (dist p q) q by rewrite ballEmdist/= ltxx.
move=> /(_ (ball p _) (ball q _) (nbhsx_ballx _ _ D0) (nbhsx_ballx _ _ D0)).
move/set0P/eqP; apply; rewrite -subset0 => x [pDx /ball_sym qDx].
by have := ball_triangle pDx qDx; rewrite -splitr.
Qed.

End metric_lemmas.

Section numFieldType_metric.
Context {R : numFieldType}.
Implicit Type x y : R.

Let dist x y := `|y - x|.

Let dist_ge0 x y : 0 <= dist x y.
Proof. exact: normr_ge0. Qed.

Let dist_positivity x y : dist x y = 0 -> x = y.
Proof. by move/normr0_eq0/eqP; rewrite subr_eq0 => /eqP. Qed.

Let ballEmdist x d : ball x d = [set y | dist x y < d].
Proof. by apply/seteqP; split => [|]/= A; rewrite /ball/= distrC. Qed.

Fail Check R^o : metricType R.

HB.instance Definition _ :=
  @isMetric.Build R R^o dist dist_ge0 dist_positivity ballEmdist.

Check R^o : metricType R.

End numFieldType_metric.

Module metricType_numDomainType.
(* tentative generalization of the section
pseudoMetricNormedZmod_numDomainType
from pseudoMetricNormedZmod_numDomainType
to
metricType *)
Section tmp.
Context {K : numDomainType} {V : metricType K}.

Local Notation ball_mdist := (fun x d => [set y : V | mdist x y < d]).

Lemma ball_mdistE : ball_mdist = ball.
Proof. by apply/funext => x; apply/funext=> d; rewrite - ballEmdist. Qed.

Local Notation nbhs_mdist := (nbhs_ball_ ball_mdist).

Lemma nbhs_nbhs_mdist : nbhs_mdist = nbhs.
Proof.
apply/funext => x.
rewrite /nbhs_ball_.
rewrite -filter_from_ballE.
by rewrite -ball_mdistE.
Qed.

Lemma nbhs_mdistP x (P : V -> Prop) : (\near x, P x) <-> nbhs_mdist x P.
Proof. by rewrite nbhs_nbhs_mdist. Qed.

Lemma filter_from_mdist_nbhs (y : V) :
  filter_from (fun i : K => 0 < i) (fun (i : K) (y' : V) => mdist y y' < i)
  = nbhs y.
Proof.
rewrite -filter_from_ballE; apply/seteqP; split => [A|A]/=.
  by move=> [x x0 yxA]; exists x => //; rewrite ballEmdist.
by move=> [x x0 yxA]; exists x => //; rewrite ballEmdist in yxA.
Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_mdist,@filter_from_mdist_nbhs).

Lemma fcvgrPdist_lt {F : set_system V} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, mdist y y' < eps.
Proof. by rewrite -filter_fromP/= !nbhs_simpl. Qed.

Lemma cvgrPdist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, mdist y (f t) < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgr_dist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, mdist y (f t) < eps.
Proof. by move=> /cvgrPdist_lt. Qed.

Lemma cvgr_dist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, mdist y (f t) <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

End tmp.

Section tmp2.
(* tentative generalization of the section
at_left_right_pseudoMetricNormedZmod
from
pseudoMetricNormedZmodType
to
metricType *)
Variables (R : numFieldType) (V : metricType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, mdist x y <= e -> P y).
Proof.
rewrite (*nbhs0P*)/= near_withinE !near_simpl.
split.
  move => /nbhs_mdistP[/= _/posnumP[e] /(_ _) Px].
  apply/(@nbhs_mdistP R R^o).
  exists e%:num => //= r /= re yr y xyr.
  apply: Px => /=.
  rewrite (le_lt_trans _ re)//.
  rewrite (le_trans xyr)//.
  by rewrite /mdist/= subr0 real_ler_norm// gtr0_real.
move => /(@nbhs_mdistP R R^o)[/= _/posnumP[e] /(_ _) Px].
apply/(@nbhs_mdistP R V).
exists (e%:num / 2) => //= r /= re; apply: (Px (e%:num / 2)) => //=.
  by rewrite /mdist/= subr0 gtr0_norm// ltr_pdivrMr// ltr_pMr// ltr1n.
by rewrite ltW.
Qed.

Let cvgrP {F : set_system V} {FF : Filter F} (y : V) : [<->
  F --> y;
  forall eps, 0 < eps -> \forall t \near F, mdist y t <= eps;
  \forall eps \near 0^'+, \forall t \near F, mdist y t <= eps;
  \forall eps \near 0^'+, \forall t \near F, mdist y t < eps].
Proof.
tfae; first by move=> *; apply: cvgr_dist_le.
- by move=> Fy; near do apply: Fy; apply: nbhs_right_gt.
- move=> Fy; near=> e; near (0:R)^'+ => d; near=> x.
  rewrite (@le_lt_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_lt; near: e; apply: nbhs_right_gt.
- move=> Fy; apply/cvgrPdist_lt => e e_gt0; near (0:R)^'+ => d.
  near=> x; rewrite (@lt_le_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma cvgrPdist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, mdist y (f t) <= eps.
Proof. exact: (cvgrP _ 0 1)%N. Qed.

End tmp2.

Section tmp3.
Variables (R : realType) (V : metricType R).

Lemma cvg_nbhsP (f : V -> V) (p l : V) : f x @[x --> p] --> l <->
  (forall u : nat -> V, (u n @[n --> \oo] --> p) -> f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le /= fpl u /cvgrPdist_lt /= uyp|pfl].
  apply/cvgrPdist_le => e /fpl.
  rewrite -filter_from_mdist_nbhs.
  move=> [d d0 pdf].
  by apply: filterS (uyp d d0) => t /pdf.
apply: contrapT => fpl; move: pfl; apply/existsNP.
suff: exists2 x : nat -> V,
    x n @[n --> \oo] --> p & ~ f (x n) @[n --> \oo] --> l.
  by move=> [x_] hp; exists x_; exact/not_implyP.
have [e He] : exists e : {posnum R}, forall d : {posnum R},
    exists xn, mdist xn p < d%:num /\ mdist (f xn) l >= e%:num.
  apply: contrapT; apply: contra_not fpl => /forallNP h.
  apply/cvgrPdist_le => e e0; have /existsNP[d] := h (PosNum e0).
  move/forallNP => {}h; near=> t.
  have /not_andP[abs|/negP] := h t.
  - exfalso; apply: abs.
    near: t.
    rewrite !near_simpl.
    rewrite /prop_near1.
    rewrite -nbhs_nbhs_mdist.
    exists d%:num => //= z/=.
    by rewrite metric_sym.
  - by rewrite -ltNge metric_sym => /ltW.
have invn n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
exists (fun n => sval (cid (He (PosNum (invn n))))).
  apply/cvgrPdist_lt => r r0; near=> t.
  rewrite /sval/=; case: cid => x [xpt _].
  rewrite metric_sym (lt_le_trans xpt)// -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0//.
  near: t; exists (trunc r^-1) => // s /= rs.
  by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
move=> /cvgrPdist_lt/(_ e%:num (ltac:(by [])))[] n _ /(_ _ (leqnn _)).
rewrite /sval/=; case: cid => // x [px xpn].
by rewrite ltNge metric_sym => /negP.
Unshelve. all: end_near. Qed.

End tmp3.

End metricType_numDomainType.
