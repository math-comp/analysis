(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum archimedean.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality contra ereal reals itv.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype derive.
From mathcomp Require Import sequences real_interval.

(**md**************************************************************************)
(* # Real-valued functions over reals                                         *)
(*                                                                            *)
(* This file provides properties of standard real-valued functions over real  *)
(* numbers (e.g., the continuity of the inverse of a continuous function).    *)
(*                                                                            *)
(* ```                                                                        *)
(*      nondecreasing_fun f == the function f is non-decreasing               *)
(*      nonincreasing_fun f == the function f is non-increasing               *)
(*         increasing_fun f == the function f is (strictly) increasing        *)
(*         decreasing_fun f == the function f is (strictly) decreasing        *)
(*                                                                            *)
(*   derivable_oo_continuous_bnd f x y == f is derivable in `]x, y[ and       *)
(*                             continuous up to the boundary, i.e.,           *)
(*                             f @ x^'+ --> f x  and  f @ y^'- --> f y        *)
(*                                                                            *)
(*      itv_partition a b s == s is a partition of the interval `[a, b]       *)
(*       itv_partitionL s c == the left side of splitting a partition at c    *)
(*       itv_partitionR s c == the right side of splitting a partition at c   *)
(*        variation a b f s == the sum of f at all points in the partition s  *)
(*         variations a b f == the set of all variations of f between a and b *)
(*  bounded_variation a b f == all variations of f are bounded                *)
(*    total_variation a b f == the sup over all variations of f from a to b   *)
(*             neg_tv a f x == the decreasing component of f                  *)
(*             pos_tv a f x == the increasing component of f                  *)
(*                                                                            *)
(* ```                                                                        *)
(*                                                                            *)
(* Limit superior and inferior for functions:                                 *)
(* ```                                                                        *)
(*   lime_sup f a/lime_inf f a == limit sup/inferior of the extended real-    *)
(*                             valued function f at point a                   *)
(* ```                                                                        *)
(*                                                                            *)
(* Discontinuities:                                                           *)
(* ```                                                                        *)
(*   discontinuity f r == r is a discontinuity of function f                  *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

Notation "'nondecreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).

Lemma nondecreasing_funN {R : realType} a b (f : R -> R) :
  {in `[a, b] &, nondecreasing_fun f} <->
  {in `[a, b] &, nonincreasing_fun (\- f)}.
Proof.
split=> [h m n mab nab mn|h m n mab nab mn]; first by rewrite lerNr opprK h.
by rewrite -(opprK (f n)) -lerNr h.
Qed.

Lemma nonincreasing_funN {R : realType} a b (f : R -> R) :
  {in `[a, b] &, nonincreasing_fun f} <->
  {in `[a, b] &, nondecreasing_fun (\- f)}.
Proof.
apply: iff_sym; apply: (iff_trans (nondecreasing_funN a b (\- f))).
rewrite [in X in _ <-> X](_ : f = \- (\- f))//.
by apply/funext => x /=; rewrite opprK.
Qed.

Section fun_cvg.

Section fun_cvg_realFieldType.
Context {R : realFieldType}.

(* NB: see cvg_addnl in topology.v *)
Lemma cvg_addrl (M : R) : M + r @[r --> +oo] --> +oo.
Proof.
move=> P [r [rreal rP]]; exists (r - M); split.
  by rewrite realB// num_real.
by move=> m; rewrite ltrBlDl => /rP.
Qed.

(* NB: see cvg_addnr in topology.v *)
Lemma cvg_addrr (M : R) : (r + M) @[r --> +oo] --> +oo.
Proof. by under [X in X @ _]funext => n do rewrite addrC; exact: cvg_addrl. Qed.

(* NB: see cvg_centern in sequences.v *)
Lemma cvg_centerr (M : R) (T : topologicalType) (f : R -> T) (l : T) :
  (f (n - M) @[n --> +oo] --> l) = (f r @[r --> +oo] --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; exact: cvg_addrr.
gen have cD : f l / f r @[r --> +oo] --> l -> f (n + M) @[n --> +oo] --> l.
   by apply: cvg_comp; exact: cvg_addrr.
move=> /cD /=.
by under [X in X @ _ --> l]funext => n do rewrite addrK.
Qed.

(* NB: see cvg_shiftn in sequence.v *)
Lemma cvg_shiftr (M : R) (T : topologicalType) (f : R -> T) (l : T) :
  (f (n + M) @[n --> +oo]--> l) = (f r @[r --> +oo] --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; exact: cvg_addrr.
rewrite -[X in X -> _](cvg_centerr M); apply: cvg_trans => /=.
apply: near_eq_cvg; near do rewrite subrK; exists M.
by rewrite num_real.
Unshelve. all: by end_near. Qed.

Lemma left_right_continuousP {T : topologicalType} (f : R -> T) x :
  f @ x^'- --> f x /\ f @ x^'+ --> f x <-> f @ x --> f x.
Proof.
split; last by move=> cts; split; exact: cvg_within_filter.
move=> [+ +] U /= Uz => /(_ U Uz) + /(_ U Uz); near_simpl.
rewrite !near_withinE => lf rf; apply: filter_app lf; apply: filter_app rf.
near=> t => xlt xgt; have := @real_leVge R x t; rewrite !num_real.
move=> /(_ isT isT) /orP; rewrite !le_eqVlt => -[|] /predU1P[|//].
- by move=> <-; exact: nbhs_singleton.
- by move=> ->; exact: nbhs_singleton.
Unshelve. all: by end_near. Qed.

Lemma cvg_at_right_left_dnbhs (f : R -> R) (p : R) (l : R) :
  f x @[x --> p^'+] --> l -> f x @[x --> p^'-] --> l ->
  f x @[x --> p^'] --> l.
Proof.
move=> /cvgrPdist_le fppl /cvgrPdist_le fpnl; apply/cvgrPdist_le => e e0.
have {fppl}[a /= a0 fppl] := fppl _ e0; have {fpnl}[b /= b0 fpnl] := fpnl _ e0.
near=> t.
have : t != p by near: t; exact: nbhs_dnbhs_neq.
rewrite neq_lt => /orP[tp|pt].
- apply: fpnl => //=; near: t.
  exists (b / 2) => //=; first by rewrite divr_gt0.
  move=> z/= + _ => /lt_le_trans; apply.
  by rewrite ler_pdivrMr// ler_pMr// ler1n.
- apply: fppl =>//=; near: t.
  exists (a / 2) => //=; first by rewrite divr_gt0.
  move=> z/= + _ => /lt_le_trans; apply.
  by rewrite ler_pdivrMr// ler_pMr// ler1n.
Unshelve. all: by end_near. Qed.
End fun_cvg_realFieldType.

Section cvgr_fun_cvg_seq.
Context {R : realType}.
Implicit Types (f : R -> R) (p l : R).

Lemma cvg_at_rightP f p l : f x @[x --> p^'+] --> l <->
  (forall u : R^nat, (forall n, u n > p) /\ (u n @[n --> \oo] --> p) ->
    f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le fpl u [up /cvgrPdist_lt ucvg]|pfl].
  apply/cvgrPdist_le => e e0.
  have [r /= r0 {}fpl] := fpl _ e0; have [s /= s0 {}ucvg] := ucvg _ r0.
  near=> t; apply: fpl => //=; apply: ucvg => /=.
  by near: t; exists s.
apply: contrapT => fpl; move: pfl; apply/existsNP.
suff: exists2 x : R ^nat,
    (forall k, x k > p) /\ x n @[n --> \oo] --> p & ~ f (x n) @[n --> \oo] --> l.
  by move=> [x_] h; exists x_; exact/not_implyP.
have [e He] : exists e : {posnum R}, forall d : {posnum R},
    exists xn : R, [/\ xn > p, `|xn - p| < d%:num & `|f xn - l| >= e%:num].
  apply: contrapT; apply: contra_not fpl => /forallNP h.
  apply/cvgrPdist_le => e e0; have /existsNP[d] := h (PosNum e0).
  move/forallNP => {}h; near=> t.
  have /not_and3P[abs|abs|/negP] := h t.
  - by exfalso; apply: abs; near: t; exact: nbhs_right_gt.
  - exfalso; apply: abs.
    by near: t;  by exists d%:num => //= z/=; rewrite distrC.
  - by rewrite -ltNge distrC => /ltW.
have invn n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
exists (fun n => sval (cid (He (PosNum (invn n))))).
  split => [k|]; first by rewrite /sval/=; case: cid => x [].
  apply/cvgrPdist_lt => r r0; near=> t.
  rewrite /sval/=; case: cid => x [px xpt _].
  rewrite distrC (lt_le_trans xpt)// -(@invrK _ r) lef_pV2 ?posrE ?invr_gt0//.
  near: t; exists `|ceil r^-1|%N => // s /=.
  rewrite -ltnS -(@ltr_nat R) => /ltW; apply: le_trans.
  by rewrite natr_absz gtr0_norm -?ceil_gt0 ?invr_gt0// ceil_ge.
move=> /cvgrPdist_lt/(_ e%:num (ltac:(by [])))[] n _ /(_ _ (leqnn _)).
rewrite /sval/=; case: cid => // x [px xpn].
by rewrite leNgt distrC => /negP.
Unshelve. all: by end_near. Qed.

Lemma cvg_at_leftP f p l : f x @[x --> p^'-] --> l <->
  (forall u : R^nat, (forall n, u n < p) /\ u n @[n --> \oo] --> p ->
    f (u n) @[n --> \oo] --> l).
Proof.
apply: (iff_trans (cvg_at_leftNP f p l)).
apply: (iff_trans (cvg_at_rightP _ _ _)).
split=> [pfl u [pu up]|pfl u [pu up]].
  rewrite -(opprK u); apply: pfl.
  by split; [move=> k; rewrite ltrNr opprK//|exact/cvgNP].
apply: pfl.
by split; [move=> k; rewrite ltrNl//|apply/cvgNP => /=; rewrite opprK].
Qed.

Lemma cvgr_dnbhsP f p l : f x @[x --> p^'] --> l <->
  (forall u : R^nat, (forall n, u n != p) /\ (u n @[n --> \oo] --> p) ->
    f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le fpl u [up /cvgrPdist_lt put]|pfl].
  apply/cvgrPdist_le => e /fpl [r /=] /put[n _ {}put] {}fpl.
  near=> t; apply: fpl => //=; apply: put.
  by near: t; exact: nbhs_infty_ge.
apply: cvg_at_right_left_dnbhs.
- by apply/cvg_at_rightP => u [pu ?]; apply: pfl; split => // n; rewrite gt_eqF.
- by apply/cvg_at_leftP => u [pu ?]; apply: pfl; split => // n; rewrite lt_eqF.
Unshelve. all: end_near. Qed.

Lemma cvg_nbhsP f p l : f x @[x --> p] --> l <->
  (forall u : R^nat, (u n @[n --> \oo] --> p) -> f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le /= fpl u /cvgrPdist_lt /= uyp|pfl].
  apply/cvgrPdist_le => e /fpl[d d0 pdf].
  by apply: filterS (uyp d d0) => t /pdf.
apply: contrapT => fpl; move: pfl; apply/existsNP.
suff: exists2 x : R ^nat,
    x n @[n --> \oo] --> p & ~ f (x n) @[n --> \oo] --> l.
  by move=> [x_] hp; exists x_; exact/not_implyP.
have [e He] : exists e : {posnum R}, forall d : {posnum R},
    exists xn, `|xn - p| < d%:num /\ `|f xn - l| >= e%:num.
  apply: contrapT; apply: contra_not fpl => /forallNP h.
  apply/cvgrPdist_le => e e0; have /existsNP[d] := h (PosNum e0).
  move/forallNP => {}h; near=> t.
  have /not_andP[abs|/negP] := h t.
  - exfalso; apply: abs.
    by near: t; exists d%:num => //= z/=; rewrite distrC.
  - by rewrite -ltNge distrC => /ltW.
have invn n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
exists (fun n => sval (cid (He (PosNum (invn n))))).
  apply/cvgrPdist_lt => r r0; near=> t.
  rewrite /sval/=; case: cid => x [xpt _].
  rewrite distrC (lt_le_trans xpt)// -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0//.
  near: t; exists `|ceil r^-1|%N => // s /=.
  rewrite -ltnS -(@ltr_nat R) => /ltW; apply: le_trans.
  by rewrite natr_absz gtr0_norm -?ceil_gt0 ?invr_gt0 ?le_ceil ?num_real.
move=> /cvgrPdist_lt/(_ e%:num (ltac:(by [])))[] n _ /(_ _ (leqnn _)).
rewrite /sval/=; case: cid => // x [px xpn].
by rewrite ltNge distrC => /negP.
Unshelve. all: end_near. Qed.

End cvgr_fun_cvg_seq.

Section cvge_fun_cvg_seq.
Context {R : realType}.

Lemma cvge_at_rightP (f : R -> \bar R) (p l : R) :
  f x @[x --> p^'+] --> l%:E <->
  (forall u : R^nat, (forall n, u n > p) /\ u n @[n --> \oo] --> p ->
    f (u n) @[n --> \oo] --> l%:E).
Proof.
split=> [/fine_cvgP [ffin_num fpl] u [pu up]|h].
  apply/fine_cvgP; split; last by move/cvg_at_rightP : fpl; exact.
  have [e /= e0 {}ffin_num] := ffin_num.
  move/cvgrPdist_lt : up => /(_ _ e0)[s /= s0 {}up]; near=> t.
  by apply: ffin_num => //=; apply: up => /=; near: t; exists s.
suff H : \forall F \near p^'+, f F \is a fin_num.
  by apply/fine_cvgP; split => //; apply/cvg_at_rightP => u /h /fine_cvgP[].
apply: contrapT => /not_near_at_rightP abs.
have invn n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
pose y_ n := sval (cid2 (abs (PosNum (invn n)))).
have py_ k : p < y_ k by rewrite /y_ /sval/=; case: cid2 => //= x /andP[].
have y_p : y_ n @[n --> \oo] --> p.
  apply/cvgrPdist_lt => e e0; near=> t.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  rewrite /y_ /sval/=; case: cid2 => //= x /andP[_ + _].
  rewrite -ltrBlDl => /lt_le_trans; apply.
  rewrite -(invrK e) lef_pV2// ?posrE ?invr_gt0//.
  near: t.
  exists `|ceil e^-1|%N => // k /=; rewrite pmulrn ceil_ge_int// -lez_nat abszE.
  by move=> /(le_trans (ler_norm _)) /le_trans; apply; rewrite lez_nat leqnSn.
have /fine_cvgP[[m _ mfy_] /= _] := h _ (conj py_ y_p).
near \oo => n.
have mn : (m <= n)%N by near: n; exists m.
have {mn} := mfy_ _ mn.
by rewrite /y_ /sval; case: cid2 => /= x _.
Unshelve. all: by end_near. Qed.

Lemma cvge_at_leftP (f : R -> \bar R) (p l : R) :
  f x @[x --> p^'-] --> l%:E <->
  (forall u : R^nat, (forall n, u n < p) /\ u n @[n --> \oo] --> p ->
    f (u n) @[n --> \oo] --> l%:E).
Proof.
apply: (iff_trans (cvg_at_leftNP f p l%:E)).
apply: (iff_trans (cvge_at_rightP _ _ l)); split=> h u [up pu].
- rewrite (_ : u = \- (\- u))%R; last by apply/funext => ?/=; rewrite opprK.
  by apply: h; split; [by move=> n; rewrite ltrNl opprK|exact: cvgN].
- by apply: h; split => [n|]; [rewrite ltrNl|move/cvgN : pu; rewrite opprK].
Qed.

End cvge_fun_cvg_seq.

Section cvgr_fun_dvg_seq.
Context {R : realType}.

Lemma cvg_pinftyP (f : R -> R) (l : R) :
  f x @[x --> +oo] --> l <->
    forall u : R^nat, (u n @[n --> \oo] --> +oo) -> f (u n) @[n --> \oo] --> l.
Proof.
split; first by move=> ? ? /cvg_comp; exact.
apply: contraPP => noncvg_f; apply/existsNP.
under eq_exists do rewrite not_implyE; apply/exists2P.
suff [e e_sep] : exists e : {posnum R},
    forall A, exists2 un, A < un & e%:num <= `|f un - l|.
  exists (fun n => sval (cid2 (e_sep n%:R))).
    apply/cvgryPgt => A; near=> n; case: cid2 => //= r nr _.
    by rewrite (le_lt_trans _ nr)//; near: n; exact: nbhs_infty_ger.
  apply/cvgrPdistC_lt => /= /(_ e%:num ltac:(by []))[N _ /(_ _ (leqnn N))].
  by case: cid2 => uN/= _ /le_lt_trans /[apply]; rewrite ltxx.
move: noncvg_f => /cvgrPdistC_lt /=; rewrite -existsPNP => -[eps eps_gt0].
move=> /not_near_inftyP eps_sep; exists (PosNum eps_gt0) => A /=.
have [x x_ltA /negP fxleps] := eps_sep _ (num_real A).
by exists x => //; rewrite leNgt.
Unshelve. all: by end_near. Qed.

Lemma cvg_ninftyP (f : R -> R) (l : R) :
  f x @[x --> -oo] --> l <->
    forall u : R^nat, (u n @[n --> \oo] --> -oo) -> f (u n) @[n --> \oo] --> l.
Proof.
rewrite cvgNy_compNP cvg_pinftyP/= (@bij_forall R^nat _ -%R)//.
have u_opp (u : R^nat) :
    ((- u) n @[n --> \oo] --> +oo) = (u n @[n --> \oo] --> -oo).
  by rewrite propeqE cvgNry.
by under eq_forall do
  (rewrite u_opp; under (eq_cvg _ (nbhs l)) do rewrite opprK).
Qed.

End cvgr_fun_dvg_seq.

Section fun_cvg_realType.
Context {R : realType}.
Implicit Types f : R -> R.

(* NB: see nondecreasing_cvgn in sequences.v *)
Lemma nondecreasing_cvgr f : nondecreasing_fun f -> has_ubound (range f) ->
  f r @[r --> +oo] --> sup (range f).
Proof.
move=> ndf ubf; set M := sup (range f).
have supf : has_sup (range f) by split => //; exists (f 0), 0.
apply/cvgrPdist_le => _/posnumP[e].
have [p Mefp] : exists p, M - e%:num <= f p.
  have [_ -[p _] <- /ltW efp] := sup_adherent (gt0 e) supf.
  by exists p; rewrite efp.
near=> n; have pn : p <= n by near: n; apply: nbhs_pinfty_ge; rewrite num_real.
rewrite ler_distlC (le_trans Mefp (ndf _ _ _))//= (@le_trans _ _ M) ?lerDl//.
by have /ubP := sup_upper_bound supf; apply; exists n.
Unshelve. all: by end_near. Qed.

(***md This covers the cases where the interval is
   $]a, +\infty[$, $]a, b[$, or $]a, b]$. *)
Lemma nonincreasing_at_right_cvgr f a (b : itv_bound R) : (BRight a < b)%O ->
    {in Interval (BRight a) b &, nonincreasing_fun f} ->
    has_ubound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> sup (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab lef ubf; set M := sup _.
have supf : has_sup [set f x | x in [set` Interval (BRight a) b]].
  split => //; case: b ab {lef ubf M} => [[|] t ta|[]] //=.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    by rewrite in_itv/= !midf_lt.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    by rewrite in_itv/= midf_lt// midf_le// ltW.
  - by exists (f (a + 1)), (a + 1) => //=; rewrite in_itv/= ltrDl andbT.
apply/cvgrPdist_le => _/posnumP[e].
have {supf} [p [ap pb]] :
    exists p, [/\ a < p, (BLeft p < b)%O & M - e%:num <= f p].
  have [_ -[p apb] <- /ltW efp] := sup_adherent (gt0 e) supf.
  move: apb; rewrite /= in_itv/= -[X in _ && X]/(BLeft p < b)%O => /andP[ap pb].
  by exists p; split.
rewrite lerBlDr {}/M.
move: b ab pb lef ubf => [[|] b|[//|]] ab pb lef ubf; set M := sup _ => Mefp.
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
    apply: sup_ubound => //=; exists r => //; rewrite in_itv/=.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_lt].
  + rewrite (le_trans Mefp)// lerD2r lef//=; last 2 first.
      by rewrite in_itv/= ap.
      by near: r; exact: nbhs_right_le.
    apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_lt].
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
    apply: sup_ubound => //=; exists r => //; rewrite in_itv/=.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_le].
  + rewrite (le_trans Mefp)// lerD2r lef//=; last 2 first.
      by rewrite in_itv/= ap.
      by near: r; exact: nbhs_right_le.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_le].
- near=> r; rewrite ler_distl; apply/andP; split.
  suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
  apply: sup_ubound => //=; exists r => //; rewrite in_itv/= andbT.
    by near: r; apply: nbhs_right_gt.
  rewrite (le_trans Mefp)// lerD2r lef//.
  - by rewrite in_itv/= andbT; near: r; exact: nbhs_right_gt.
  - by rewrite in_itv/= ap.
  - by near: r; exact: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma nonincreasing_at_right_is_cvgr f a :
    (\forall x \near a^'+, {in `]a, x[ &, nonincreasing_fun f}) ->
    (\forall x \near a^'+, has_ubound (f @` `]a, x[)) ->
  cvg (f x @[x --> a ^'+]).
Proof.
move=> nif ubf; apply/cvg_ex; near a^'+ => b.
by eexists; apply: (@nonincreasing_at_right_cvgr _ _ (BLeft b));
  [rewrite bnd_simp|near: b..].
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_at_right_cvgr f a (b : itv_bound R) : (BRight a < b)%O ->
    {in Interval (BRight a) b &, nondecreasing_fun f} ->
    has_lbound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> inf (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab nif hlb; set M := inf _.
have ndNf : {in Interval (BRight a) b &, nonincreasing_fun (\- f)}.
  by move=> r s rab sab /nif; rewrite lerN2; exact.
have hub : has_ubound [set (\- f) x | x in [set` Interval (BRight a) b]].
  apply/has_ub_lbN; rewrite image_comp/=.
  rewrite [X in has_lbound X](_ : _ = f @` [set` Interval (BRight a) b])//.
  by apply: eq_imagel => y _ /=; rewrite opprK.
have /cvgN := nonincreasing_at_right_cvgr ab ndNf hub.
rewrite opprK [X in _ --> X -> _](_ : _ =
    inf (f @` [set` Interval (BRight a) b]))//.
by rewrite /inf; congr (- sup _); rewrite image_comp/=; exact: eq_imagel.
Qed.

Lemma nondecreasing_at_right_is_cvgr f a :
    (\forall x \near a^'+, {in `]a, x[ &, nondecreasing_fun f}) ->
    (\forall x \near a^'+, has_lbound (f @` `]a, x[)) ->
  cvg (f x @[x --> a ^'+]).
Proof.
move=> ndf lbf; apply/cvg_ex; near a^'+ => b.
by eexists; apply: (@nondecreasing_at_right_cvgr _ _ (BLeft b));
  [rewrite bnd_simp|near: b..].
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_at_left_is_cvgr f a :
    (\forall x \near a^'-, {in `]x, a[ &, {homo f : n m / n <= m}}) ->
    (\forall x \near a^'-, has_ubound [set f y | y in `]x, a[]) ->
  cvg (f x @[x --> a^'-]).
Proof.
move=> ndf ubf; suff: cvg ((f \o -%R) x @[x --> (- a)^'+]).
  move=> /cvg_ex[/= l fal].
  by apply/cvg_ex; exists l; exact/cvg_at_leftNP.
apply: @nonincreasing_at_right_is_cvgr.
- rewrite at_rightN near_simpl; apply: filterS ndf => x ndf y z.
  by rewrite -2!oppr_itvoo => yxa zxa yz; rewrite ndf// lerNr opprK.
- rewrite at_rightN near_simpl; apply: filterS ubf => x [r ubf].
  exists r => _/= [s sax <-]; rewrite ubf//=; exists (- s) => //.
  by rewrite oppr_itvoo.
Qed.

Let nondecreasing_at_right_is_cvgrW f a b r : a < r -> r < b ->
  {in `[a, b] &, nondecreasing_fun f} -> cvg (f x @[x --> r^'+]).
Proof.
move=> ar rb ndf H; apply: nondecreasing_at_right_is_cvgr.
- near=> s => x y xrs yrs xy; rewrite ndf//.
  + by apply: subset_itvW xrs; exact/ltW.
  + by apply: subset_itvW yrs; exact/ltW.
- near=> x; exists (f r) => _ /= [s srx <-]; rewrite ndf//.
  + by apply: subset_itv_oo_cc; rewrite in_itv/= ar.
  + by apply: subset_itvW srx; exact/ltW.
  + by move: srx; rewrite in_itv/= => /andP[/ltW].
Unshelve. all: by end_near. Qed.

Let nondecreasing_at_left_is_cvgrW f a b r : a < r -> r < b ->
  {in `[a, b] &, nondecreasing_fun f} -> cvg (f x @[x --> r^'-]).
Proof.
move=> ar rb ndf H; apply: nondecreasing_at_left_is_cvgr.
- near=> s => x y xrs yrs xy; rewrite ndf//.
  + by apply: subset_itvW xrs; exact/ltW.
  + by apply: subset_itvW yrs; exact/ltW.
- near=> x; exists (f r) => _ /= [s srx <-]; rewrite ndf//.
  + by apply: subset_itvW srx; exact/ltW.
  + by apply: subset_itv_oo_cc; rewrite in_itv/= ar.
  + by move: srx; rewrite in_itv/= => /andP[_ /ltW].
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_at_left_at_right f a b :
  {in `[a, b] &, nondecreasing_fun f} ->
  {in `]a, b[, forall r, lim (f x @[x --> r^'-]) <= lim (f x @[x --> r^'+])}.
Proof.
move=> ndf r; rewrite in_itv/= => /andP[ar rb]; apply: limr_ge.
  exact: nondecreasing_at_right_is_cvgrW ndf.
near=> x; apply: limr_le; first exact: nondecreasing_at_left_is_cvgrW ndf.
near=> y; rewrite ndf// ?in_itv/=.
- apply/andP; split; first by near: y; apply: nbhs_left_ge.
  exact: (le_trans _ (ltW rb)).
- by rewrite (le_trans (ltW ar))/= ltW.
- exact: (@le_trans _ _ r).
Unshelve. all: by end_near. Qed.

Lemma nonincreasing_at_left_at_right f a b :
  {in `[a, b] &, nonincreasing_fun f} ->
  {in `]a, b[, forall r, lim (f x @[x --> r^'-]) >= lim (f x @[x --> r^'+])}.
Proof.
move=> nif; have ndNf : {in `[a, b] &, nondecreasing_fun (-%R \o f)}.
  by move=> x y xab yab xy /=; rewrite lerNl opprK nif.
move/nondecreasing_at_left_at_right : (ndNf) => H x.
rewrite in_itv/= => /andP[ax xb]; rewrite -[leLHS]opprK lerNl -!limN//.
- by apply: H; rewrite !in_itv/= ax.
- rewrite -(opprK f); apply: is_cvgN.
  exact: nondecreasing_at_right_is_cvgrW ndNf.
- rewrite -(opprK f);apply: is_cvgN.
  exact: nondecreasing_at_left_is_cvgrW ndNf.
Qed.

End fun_cvg_realType.
Arguments nondecreasing_at_right_cvgr {R f a} b.

Section fun_cvg_ereal.
Context {R : realType}.
Local Open Scope ereal_scope.

(* NB: see ereal_nondecreasing_cvgn in sequences.v *)
Lemma nondecreasing_cvge (f : R -> \bar R) :
  nondecreasing_fun f -> f r @[r --> +oo%R] --> ereal_sup (range f).
Proof.
move=> ndf; set S := range f; set l := ereal_sup S.
have [Spoo|Spoo] := pselect (S +oo).
  have [N Nf] : exists N, forall n, (n >= N)%R -> f n = +oo.
    case: Spoo => N _ uNoo; exists N => n Nn.
    by have := ndf _ _ Nn; rewrite uNoo leye_eq => /eqP.
  have -> : l = +oo by rewrite /l /ereal_sup; exact: supremum_pinfty.
  rewrite -(cvg_shiftr `|N|); apply: cvg_near_cst.
  exists N; split; first by rewrite num_real.
  by move=> x /ltW Nx; rewrite Nf// ler_wpDr.
have [lpoo|lpoo] := eqVneq l +oo.
  rewrite lpoo; apply/cvgeyPge => M.
  have /ereal_sup_gt[_ [n _] <- Mun] : M%:E < l by rewrite lpoo// ltry.
  exists n; split; first by rewrite num_real.
  by move=> m /= nm; rewrite (le_trans (ltW Mun))// ndf// ltW.
have [fnoo|fnoo] := pselect (f = cst -oo).
  rewrite /l (_ : S = [set -oo]).
    by rewrite ereal_sup1 fnoo; exact: cvg_cst.
  apply/seteqP; split => [_ [n _] <- /[!fnoo]//|_ ->].
  by rewrite /S fnoo; exists 0%R.
have [/ereal_sup_ninfty lnoo|lnoo] := eqVneq l -oo.
  by exfalso; apply/fnoo/funext => n; rewrite (lnoo (f n))//; exists n.
have l_fin_num : l \is a fin_num by rewrite fin_numE lpoo lnoo.
set A := [set n | f n = -oo]; set B := [set n | f n != -oo].
have f_fin_num n : B n -> f n \is a fin_num.
  move=> Bn; rewrite fin_numE Bn/=.
  by apply: contra_notN Spoo => /eqP unpoo; exists n.
have [x Bx] : B !=set0.
  apply/set0P/negP => /eqP B0; apply/fnoo/funext => n.
  apply/eqP/negPn/negP => unnoo.
  by move/seteqP : B0 => [+ _] => /(_ n); apply.
have xB r : (x <= r)%R -> B r.
  move=> /ndf xr; apply/negP => /eqP urnoo.
  by move: xr; rewrite urnoo leeNy_eq; exact/negP.
rewrite -(@fineK _ l)//; apply/fine_cvgP; split.
  exists x; split; first by rewrite num_real.
  by move=> r A1r; rewrite f_fin_num //; exact/xB/ltW.
set g := fun n => if (n < x)%R then fine (f x) else fine (f n).
have <- : sup (range g) = fine l.
  apply: EFin_inj; rewrite -ereal_sup_EFin//; last 2 first.
    - exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
      have [mx|xm] := ltP m x.
        by rewrite fine_le// ?f_fin_num//; apply: ereal_sup_ubound; exists x.
      rewrite fine_le// ?f_fin_num//; first exact/xB.
      by apply: ereal_sup_ubound; exists m.
    - by exists (g 0%R), 0%R.
  rewrite fineK//; apply/eqP; rewrite eq_le; apply/andP; split.
    apply: le_ereal_sup => _ /= [_ [m _] <-] <-.
    rewrite /g; have [_|xm] := ltP m x.
      by rewrite fineK// ?f_fin_num//; exists x.
    by rewrite fineK// ?f_fin_num//; [exists m|exact/xB].
  apply: ub_ereal_sup => /= _ [m _] <-.
  have [mx|xm] := ltP m x.
    rewrite (le_trans (ndf _ _ (ltW mx)))//.
    apply: ereal_sup_ubound => /=; exists (fine (f x)); last first.
      by rewrite fineK// f_fin_num.
    by exists m => //; rewrite /g mx.
  apply: ereal_sup_ubound => /=; exists (fine (f m)) => //.
    by exists m => //; rewrite /g ltNge xm.
  by rewrite fineK ?f_fin_num//; exact: xB.
suff: g x @[x --> +oo%R] --> sup (range g).
  apply: cvg_trans; apply: near_eq_cvg; near=> n.
  rewrite /g ifF//; apply/negbTE; rewrite -leNgt.
  by near: n; apply: nbhs_pinfty_ge; rewrite num_real.
apply: nondecreasing_cvgr.
- move=> m n mn; rewrite /g /=; have [_|xm] := ltP m x.
  + have [nx|nx] := ltP n x; first by rewrite fine_le// f_fin_num.
    by rewrite fine_le// ?f_fin_num//; [exact: xB|exact: ndf].
  + rewrite ltNge (le_trans xm mn)//= fine_le ?f_fin_num//.
    * exact: xB.
    * by apply: xB; rewrite (le_trans xm).
    * exact/ndf.
- exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
  rewrite -lee_fin (fineK l_fin_num); apply: ereal_sup_ubound.
  have [_|xm] := ltP m x; first by rewrite fineK// ?f_fin_num//; eexists.
  by rewrite fineK// ?f_fin_num//; [exists m|exact/xB].
Unshelve. all: by end_near. Qed.

(* NB: see ereal_nondecreasing_is_cvgn in sequences.v *)
Lemma nondecreasing_is_cvge (f : R -> \bar R) :
  nondecreasing_fun f -> (cvg (f r @[r --> +oo]))%R.
Proof. by move=> u_nd u_ub; apply: cvgP; exact: nondecreasing_cvge. Qed.

Lemma nondecreasing_at_right_cvge (f : R -> \bar R) a (b : itv_bound R) :
    (BRight a < b)%O ->
    {in Interval (BRight a) b &, nondecreasing_fun f} ->
  f x @[x --> a ^'+] --> ereal_inf (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab ndf; set S := (X in ereal_inf X); set l := ereal_inf S.
have [Snoo|Snoo] := pselect (S -oo).
  case: (Snoo) => N/=.
  rewrite in_itv/= -[X in _ && X]/(BLeft N < b)%O => /andP[aN Nb] fNpoo.
  have Nf n : (a < n <= N)%R -> f n = -oo.
    move=> /andP[an nN]; apply/eqP.
    rewrite eq_le leNye andbT -fNpoo ndf//.
      by rewrite in_itv/= -[X in _ && X]/(BLeft n < b)%O an (le_lt_trans _ Nb).
    by rewrite in_itv/= -[X in _ && X]/(BLeft N < b)%O (lt_le_trans an nN).
  have -> : l = -oo.
    by rewrite /l /ereal_inf /ereal_sup supremum_pinfty//=; exists -oo.
  apply: cvg_near_cst; exists (N - a)%R => /=; first by rewrite subr_gt0.
  move=> y /= + ay; rewrite ltr0_norm ?subr_lt0// opprB => ayNa.
  by rewrite Nf// ay/= -(subrK a y) -lerBrDr ltW.
have [lnoo|lnoo] := eqVneq l -oo.
  rewrite lnoo; apply/cvgeNyPle => M.
  have /ereal_inf_lt[x [y]]/= : M%:E > l by rewrite lnoo ltNyr.
  rewrite in_itv/= -[X in _ && X]/(BLeft y < b)%O/= => /andP[ay yb] <- fyM.
  exists (y - a)%R => /=; first by rewrite subr_gt0.
  move=> z /= + az.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr subrK => zy.
  rewrite (le_trans _ (ltW fyM))// ndf ?ltW//.
    by rewrite in_itv/= -[X in _ && X]/(BLeft z < b)%O/= az/= (lt_trans _ yb).
  by rewrite in_itv/= -[X in _ && X]/(BLeft y < b)%O/= (lt_trans az zy).
have [fpoo|fpoo] := pselect {in Interval (BRight a) b, forall x, f x = +oo}.
  rewrite {}/l in lnoo *; rewrite {}/S in Snoo lnoo *.
  rewrite [X in ereal_inf X](_ : _ = [set +oo]).
    rewrite ereal_inf1; apply/cvgeyPgey; near=> M.
    move: b ab {ndf lnoo Snoo} fpoo => [[|] b|[//|]] ab fpoo.
    - near=> x; rewrite fpoo ?leey// in_itv/=.
      by apply/andP; split; near: x; [exact: nbhs_right_gt|exact: nbhs_right_lt].
    - near=> x; rewrite fpoo ?leey// in_itv/=.
      by apply/andP; split; near: x; [exact: nbhs_right_gt|exact: nbhs_right_le].
    - near=> x; rewrite fpoo ?leey// in_itv/= andbT.
      by near: x; exact: nbhs_right_gt.
  apply/seteqP; split => [_ [n _] <- /[!fpoo]//|_ ->].
  move: b ab ndf lnoo Snoo fpoo => [[|] s|[//|]] ab ndf lnoo Snoo fpoo /=.
  - by exists ((a + s) / 2)%R; rewrite ?fpoo// in_itv/= !midf_lt.
  - by exists ((a + s) / 2)%R; rewrite ?fpoo// in_itv/= !(midf_lt, midf_le)// ltW.
  - by exists (a + 1)%R; rewrite ?fpoo// in_itv/= andbT ltrDl.
have [/ereal_inf_pinfty lpoo|lpoo] := eqVneq l +oo.
  by exfalso; apply/fpoo => r rab; rewrite (lpoo (f r))//; exists r.
have l_fin_num : l \is a fin_num by rewrite fin_numE lpoo lnoo.
set A := [set r | [/\ (a < r)%R, (BLeft r < b)%O & f r != +oo]].
have f_fin_num r : r \in A -> f r \is a fin_num.
  rewrite inE /A/= => -[ar rb] frnoo; rewrite fin_numE frnoo andbT.
  apply: contra_notN Snoo => /eqP frpoo.
  by exists r => //=; rewrite in_itv/= -[X in _ && X]/(BLeft r < b)%O ar rb.
have [x [ax xb fxpoo]] : A !=set0.
  apply/set0P/negP => /eqP A0; apply/fpoo => x.
  rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O => /andP[ax xb].
  apply/eqP/negPn/negP => unnoo.
  by move/seteqP : A0 => [+ _] => /(_ x); apply; rewrite /A/= ax.
have axA r : (a < r <= x)%R -> r \in A.
  move=> /andP[ar rx]; move: (rx) => /ndf rafx; rewrite /A /= inE; split => //.
    by rewrite (le_lt_trans _ xb).
  apply/negP => /eqP urnoo.
  move: rafx; rewrite urnoo.
  rewrite in_itv/= -[X in _ && X]/(BLeft r < b)%O ar/=.
  rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax/=.
  by rewrite leye_eq (negbTE fxpoo) -falseE; apply; rewrite (le_lt_trans _ xb).
rewrite -(@fineK _ l)//; apply/fine_cvgP; split.
  exists (x - a)%R => /=; first by rewrite subr_gt0.
  move=> z /= + az.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr subrK// => zx.
  by rewrite f_fin_num// axA// az/= ltW.
set g := fun n => if (a < n < x)%R then fine (f n) else fine (f x).
have <- : inf [set g x | x in [set` Interval (BRight a) b]] = fine l.
  apply: EFin_inj; rewrite -ereal_inf_EFin//; last 2 first.
    - exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
      case: ifPn => [/andP[am mx]|].
        rewrite fine_le// ?f_fin_num//; first by rewrite axA// am (ltW mx).
        apply: ereal_inf_lbound; exists m => //=.
        rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am/=.
        by rewrite (le_lt_trans _ xb) ?ltW.
      rewrite negb_and -!leNgt => /orP[ma|xm].
        rewrite fine_le// ?f_fin_num ?inE//.
        apply: ereal_inf_lbound; exists x => //=.
        by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.
      rewrite fine_le// ?f_fin_num ?inE//.
      apply: ereal_inf_lbound; exists x => //=.
      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.
    - rewrite {}/l in lnoo lpoo l_fin_num *.
      rewrite {}/S in Snoo lnoo lpoo l_fin_num *.
      rewrite {}/A in f_fin_num axA *.
      move: b ab {xb ndf lnoo lpoo l_fin_num f_fin_num Snoo fpoo axA} =>
            [[|] s|[//|]] ab /=.
      + exists (g ((a + s) / 2))%R, ((a + s) / 2)%R => //=.
        by rewrite /= in_itv/= !midf_lt.
      + exists (g ((a + s) / 2))%R, ((a + s) / 2)%R => //=.
        by rewrite /= in_itv/= !(midf_lt, midf_le)// ltW.
      + exists (g (a + 1)%R), (a + 1)%R => //=.
        by rewrite in_itv/= andbT ltrDl.
  rewrite fineK//; apply/eqP; rewrite eq_le; apply/andP; split; last first.
    apply: le_ereal_inf => _ /= [_ [m _] <-] <-.
    rewrite /g; case: ifPn => [/andP[am mx]|].
      rewrite fineK// ?f_fin_num//; last by rewrite axA// am ltW.
      exists m => //=.
      by rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am/= (lt_trans _ xb).
    rewrite negb_and -!leNgt => /orP[ma|xm].
      rewrite fineK//; last by rewrite f_fin_num ?inE.
      exists x => //=.
      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.
    exists x => /=.
      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.
    by rewrite fineK// f_fin_num ?inE.
  apply: lb_ereal_inf => /= y [m] /=.
  rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O => /andP[am mb] <-{y}.
  have [mx|xm] := ltP m x.
    apply: ereal_inf_lbound => /=; exists (fine (f m)); last first.
      by rewrite fineK// f_fin_num// axA// am (ltW mx).
    by exists m; [rewrite in_itv/= am|rewrite /g am mx].
  rewrite (@le_trans _ _ (f x))//; last first.
    by apply: ndf => //; rewrite in_itv//= ?ax ?am.
  apply: ereal_inf_lbound => /=; exists (fine (f x)); last first.
    by rewrite fineK// f_fin_num ?inE.
  by exists x; [rewrite in_itv/= ax|rewrite /g ltxx andbF].
suff: g x @[x --> a^'+] --> inf [set g x | x in [set` Interval (BRight a) b]].
  apply: cvg_trans; apply: near_eq_cvg; near=> n.
  rewrite /g /=; case: ifPn => [//|].
  rewrite negb_and -!leNgt => /orP[na|xn].
    exfalso.
    move: na; rewrite leNgt => /negP; apply.
    by near: n; exact: nbhs_right_gt.
  suff nx : (n < x)%R by rewrite ltNge xn in nx.
  near: n; exists ((x - a) / 2)%R; first by rewrite /= divr_gt0// subr_gt0.
  move=> y /= /[swap] ay.
  rewrite ltr0_norm// ?subr_lt0// opprB ltrBlDr => /lt_le_trans; apply.
  by rewrite -lerBrDr ler_pdivrMr// ler_pMr// ?ler1n// subr_gt0.
apply: nondecreasing_at_right_cvgr => //.
- move=> m n; rewrite !in_itv/= -[X in _ && X]/(BLeft m < b)%O.
  rewrite -[X in _ -> _ && X -> _]/(BLeft n < b)%O.
  move=> /andP[am mb] /andP[an nb] mn.
  rewrite /g /=; case: ifPn => [/andP[_ mx]|].
    rewrite (lt_le_trans am mn) /=; have [nx|nn0] := ltP n x.
      rewrite fine_le ?f_fin_num ?ndf//; first by rewrite axA// am (ltW mx).
      by rewrite axA// (ltW nx) andbT (lt_le_trans am).
      by rewrite in_itv/= am.
      by rewrite in_itv/= an.
    rewrite fine_le ?f_fin_num//.
    + by rewrite axA// am (ltW (lt_le_trans mx _)).
    + by rewrite inE.
    + rewrite ndf//; last exact/ltW.
      by rewrite !in_itv/= am.
      by rewrite !in_itv/= ax.
  rewrite negb_and -!leNgt => /orP[|xm]; first by rewrite leNgt am.
  by rewrite (lt_le_trans am mn)/= ltNge (le_trans xm mn).
- exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
  rewrite -lee_fin (fineK l_fin_num); apply: ereal_inf_lbound.
  case: ifPn => [/andP[am mn0]|].
    rewrite fineK//; last by rewrite f_fin_num// axA// am (ltW mn0).
    exists m => //=.
    by rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am (lt_trans _ xb).
  rewrite negb_and -!leNgt => /orP[ma|xm].
    rewrite fineK//; first by exists x => //=; rewrite in_itv/= ax.
    by rewrite f_fin_num ?inE.
  by rewrite fineK// ?f_fin_num ?inE//; exists x => //=; rewrite in_itv/= ax.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_at_right_is_cvge (f : R -> \bar R) (a : R) :
    (\forall x \near a^'+, {in `]a, x[ &, nondecreasing_fun f}) ->
  cvg (f x @[x --> a ^'+]).
Proof.
move=> ndf; apply/cvg_ex; near a^'+ => b.
by eexists; apply: (@nondecreasing_at_right_cvge _ _ (BLeft b));
  [rewrite bnd_simp|near: b..].
Unshelve. all: by end_near. Qed.

Lemma nonincreasing_at_right_cvge (f : R -> \bar R) a (b : itv_bound R) :
    (BRight a < b)%O -> {in Interval (BRight a) b &, nonincreasing_fun f} ->
  f x @[x --> a ^'+] --> ereal_sup (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab nif; have ndNf : {in Interval (BRight a) b &,
    {homo (\- f) : n m / (n <= m)%R >-> n <= m}}.
  by move=> r s rab sab /nif; rewrite leeN2; exact.
have /cvgeN := nondecreasing_at_right_cvge ab ndNf.
under eq_fun do rewrite oppeK.
set lhs := (X in _ --> X -> _); set rhs := (X in _ -> _ --> X).
suff : lhs = rhs by move=> ->.
rewrite {}/rhs {}/lhs; rewrite /ereal_inf oppeK; congr ereal_sup.
by rewrite image_comp/=; apply: eq_imagel => x _ /=; rewrite oppeK.
Qed.

Lemma nonincreasing_at_right_is_cvge (f : R -> \bar R) a :
    (\forall x \near a^'+, {in `]a, x[ &, nonincreasing_fun f}) ->
  cvg (f x @[x --> a ^'+]).
Proof.
move=> nif; apply/cvg_ex; near a^'+ => b.
by eexists; apply: (@nonincreasing_at_right_cvge _ _ (BLeft b));
  [rewrite bnd_simp|near: b..].
Unshelve. all: by end_near. Qed.

End fun_cvg_ereal.

End fun_cvg.
Arguments nondecreasing_at_right_cvge {R f a} b.
Arguments nondecreasing_at_right_is_cvge {R f a}.
Arguments nonincreasing_at_right_cvge {R f a} b.
Arguments nonincreasing_at_right_is_cvge {R f a}.

Section lime_sup_inf.
Variable R : realType.
Local Open Scope ereal_scope.
Implicit Types (f g : R -> \bar R) (a r s l : R).

Definition lime_sup f a : \bar R := limf_esup f a^'.

Definition lime_inf f a : \bar R := - lime_sup (\- f) a.

Let sup_ball f a r := ereal_sup [set f x | x in ball a r `\ a].

Let sup_ball_le f a r s : (r <= s)%R -> sup_ball f a r <= sup_ball f a s.
Proof.
move=> rs; apply: ub_ereal_sup => /= _ /= [t [rt ta] <-].
by apply: ereal_sup_ubound => /=; exists t => //; split => //; exact: le_ball rt.
Qed.

Let sup_ball_is_cvg f a : cvg (sup_ball f a e @[e --> 0^'+]).
Proof.
apply: nondecreasing_at_right_is_cvge; near=> e.
by move=> x y; rewrite !in_itv/= => /andP[x0 xe] /andP[y0 ye] /sup_ball_le.
Unshelve. all: by end_near. Qed.

Let inf_ball f a r := - sup_ball (\- f) a r.

Let inf_ballE f a r : inf_ball f a r = ereal_inf [set f x | x in ball a r `\ a].
Proof.
by rewrite /inf_ball /ereal_inf; congr (- _); rewrite /sup_ball -image_comp.
Qed.

Let inf_ball_le f a r s : (s <= r)%R -> inf_ball f a r <= inf_ball f a s.
Proof. by move=> sr; rewrite /inf_ball leeNl oppeK sup_ball_le. Qed.

Let inf_ball_is_cvg f a : cvg (inf_ball f a e @[e --> 0^'+]).
Proof.
apply: nonincreasing_at_right_is_cvge; near=> e.
by move=> x y; rewrite !in_itv/= => /andP[x0 xe] /andP[y0 ye] /inf_ball_le.
Unshelve. all: by end_near. Qed.

Let le_sup_ball f g a :
  (\forall r \near 0^'+, forall y : R, y != a -> ball a r y -> f y <= g y) ->
  \forall r \near 0^'+, sup_ball f a r <= sup_ball g a r.
Proof.
move=> [e/= e0 fg].
near=> r; apply: ub_ereal_sup => /= _ [s [pas /= /eqP ps]] <-.
rewrite (@le_trans _ _ (g s))//.
  by rewrite (fg r)//= sub0r normrN gtr0_norm.
by apply: ereal_sup_ubound => /=; exists s => //; split => //; exact/eqP.
Unshelve. all: by end_near. Qed.

Lemma lime_sup_lim f a : lime_sup f a = lim (sup_ball f a e @[e --> 0^'+]).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: lime_ge => //; near=> e; apply: ereal_inf_lbound => /=.
  by exists (ball a e `\ a) => //=; exact: dnbhs_ball.
apply: lb_ereal_inf => /= _ [A [r /= r0 arA] <-].
apply: lime_le => //; near=> e.
apply: le_ereal_sup => _ [s [ase /eqP sa] <- /=].
exists s => //; apply: arA => //=; apply: (lt_le_trans ase).
by near: e; exact: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma lime_inf_lim f a : lime_inf f a = lim (inf_ball f a e @[e --> 0^'+]).
Proof.
rewrite /lime_inf lime_sup_lim -limeN; last exact: sup_ball_is_cvg.
by rewrite /sup_ball; under eq_fun do rewrite -image_comp.
Qed.

Lemma lime_supE f a :
  lime_sup f a = ereal_inf [set sup_ball f a e | e in `]0, +oo[ ]%R.
Proof.
rewrite lime_sup_lim; apply/cvg_lim => //.
apply: nondecreasing_at_right_cvge => //.
by move=> x y; rewrite !in_itv/= !andbT => x0 y0; exact: sup_ball_le.
Qed.

Lemma lime_infE f a :
  lime_inf f a = ereal_sup [set inf_ball f a e | e in `]0, +oo[ ]%R.
Proof. by rewrite /lime_inf lime_supE /ereal_inf oppeK image_comp. Qed.

Lemma lime_infN f a : lime_inf (\- f) a = - lime_sup f a.
Proof. by rewrite /lime_sup -limf_einfN. Qed.

Lemma lime_supN f a : lime_sup (\- f) a = - lime_inf f a.
Proof. by rewrite /lime_inf oppeK. Qed.

Lemma __deprecated__lime_sup_ge0 f a : (forall x, 0 <= f x) -> 0 <= lime_sup f a.
Proof. by move=> f0; exact: limf_esup_ge0. Qed.

Lemma lime_inf_ge0 f a : (forall x, 0 <= f x) -> 0 <= lime_inf f a.
Proof.
move=> f0; rewrite lime_inf_lim; apply: lime_ge; first exact: inf_ball_is_cvg.
near=> b; rewrite inf_ballE.
by apply: lb_ereal_inf => /= _ [r [abr/= ra]] <-; exact: f0.
Unshelve. all: by end_near. Qed.

Lemma lime_supD f g a : lime_sup f a +? lime_sup g a ->
  lime_sup (f \+ g)%E a <= lime_sup f a + lime_sup g a.
Proof.
move=> fg; rewrite !lime_sup_lim -limeD//; last first.
  by rewrite -!lime_sup_lim.
apply: lee_lim => //.
- apply: nondecreasing_at_right_is_cvge; near=> e => x y; rewrite !in_itv/=.
  by move=> /andP[? ?] /andP[? ?] xy; apply: leeD => //; exact: sup_ball_le.
- near=> a0; apply: ub_ereal_sup => _ /= [a1 [a1ae a1a]] <-.
  by apply: leeD; apply: ereal_sup_ubound => /=; exists a1.
Unshelve. all: by end_near. Qed.

Lemma lime_sup_le f g a :
  (\forall r \near 0^'+, forall y, y != a -> ball a r y -> f y <= g y) ->
  lime_sup f a <= lime_sup g a.
Proof.
by move=> fg; rewrite !lime_sup_lim; apply: lee_lim => //; exact: le_sup_ball.
Qed.

Lemma lime_inf_sup f a : lime_inf f a <= lime_sup f a.
Proof.
rewrite lime_inf_lim lime_sup_lim; apply: lee_lim => //.
near=> r; rewrite ereal_sup_le//.
have ? : exists2 x, ball a r x /\ x <> a & f x = f (a + r / 2)%R.
  exists (a + r / 2)%R => //; split.
    rewrite /ball/= opprD addrA subrr sub0r normrN gtr0_norm ?divr_gt0//.
    by rewrite ltr_pdivrMr// ltr_pMr// ltr1n.
  by apply/eqP; rewrite gt_eqF// ltr_pwDr// divr_gt0.
by exists (f (a + r / 2)) => //=; rewrite inf_ballE ereal_inf_lbound.
Unshelve. all: by end_near. Qed.

Local Lemma lim_lime_sup' f a l :
  f r @[r --> a] --> l%:E -> lime_sup f a <= l%:E.
Proof.
move=> fpA; apply/lee_addgt0Pr => e e0; rewrite lime_sup_lim.
apply: lime_le => //.
move/fine_cvg : (fpA) => /cvgrPdist_le fpA1.
move/fcvg_is_fine : (fpA); rewrite near_map => -[d d0] fpA2.
have := fpA1 _ e0 => -[q /= q0] H.
near=> x; apply: ub_ereal_sup => //= _ [y [pry /= yp <-]].
have ? : f y \is a fin_num.
  apply: fpA2.
  rewrite /ball_ /= (lt_le_trans pry)//.
  by near: x; exact: nbhs_right_le.
rewrite -lee_subel_addl// -(@fineK _ (f y)) // -EFinB lee_fin.
rewrite (le_trans (ler_norm _))// distrC H// /ball_/= ltr_distlC.
move: pry; rewrite /ball/= ltr_distlC => /andP[pay ypa].
have xq : (x <= q)%R by near: x; exact: nbhs_right_le.
apply/andP; split.
  by rewrite (le_lt_trans _ pay)// lerB.
by rewrite (lt_le_trans ypa)// lerD2l.
Unshelve. all: by end_near.
Qed.

Local Lemma lim_lime_inf' f a (l : R) :
  f r @[r --> a] --> l%:E -> l%:E <= lime_inf f a.
Proof.
move=> fpA; apply/lee_subgt0Pr => e e0; rewrite lime_inf_lim.
apply: lime_ge => //.
move/fine_cvg : (fpA) => /cvgrPdist_le fpA1.
move/fcvg_is_fine : (fpA); rewrite near_map => -[d d0] fpA2.
have := fpA1 _ e0 => -[q /= q0] H.
near=> x.
rewrite inf_ballE.
apply: lb_ereal_inf => //= _ [y [pry /= yp <-]].
have ? : f y \is a fin_num.
  apply: fpA2.
  rewrite /ball_ /= (lt_le_trans pry)//.
  by near: x; exact: nbhs_right_le.
rewrite -(@fineK _ (f y)) // -EFinB lee_fin lerBlDr -lerBlDl.
rewrite (le_trans (ler_norm _))// H// /ball_/= ltr_distlC.
move: pry; rewrite /ball/= ltr_distlC => /andP[pay ypa].
have xq : (x <= q)%R by near: x; exact: nbhs_right_le.
apply/andP; split.
  by rewrite (le_lt_trans _ pay)// lerB.
by rewrite (lt_le_trans ypa)// lerD2l.
Unshelve. all: by end_near.
Qed.

Lemma lim_lime_inf f a (l : R) :
  f r @[r --> a] --> l%:E -> lime_inf f a = l%:E.
Proof.
move=> h; apply/eqP; rewrite eq_le.
by rewrite lim_lime_inf'// andbT (le_trans (lime_inf_sup _ _))// lim_lime_sup'.
Qed.

Lemma lim_lime_sup f a (l : R) :
  f r @[r --> a] --> l%:E -> lime_sup f a = l%:E.
Proof.
move=> h; apply/eqP; rewrite eq_le.
by rewrite lim_lime_sup'//= (le_trans _ (lime_inf_sup _ _))// lim_lime_inf'.
Qed.

Local Lemma lime_supP f a l :
  lime_sup f a = l%:E -> forall e : {posnum R}, exists d : {posnum R},
  forall x, (ball a d%:num `\ a) x -> f x < l%:E + e%:num%:E.
Proof.
rewrite lime_supE => fal.
have H (e : {posnum R}) :
    exists d : {posnum R}, l%:E <= sup_ball f a d%:num < l%:E + e%:num%:E.
  apply: contrapT => /forallNP H.
  have : ereal_inf [set sup_ball f a r | r in `]0%R, +oo[] \is a fin_num.
    by rewrite fal.
  move=> /lb_ereal_inf_adherent-/(_ e%:num ltac:(by []))[y] /=.
  case=> r; rewrite in_itv/= andbT => r0 <-{y}.
  rewrite ltNge => /negP; apply.
  have /negP := H (PosNum r0).
  rewrite negb_and => /orP[|].
    rewrite -ltNge => farl.
    have : ereal_inf [set sup_ball f a r | r in `]0%R, +oo[] < l%:E.
      rewrite (le_lt_trans _ farl)//; apply: ereal_inf_lbound => /=; exists r => //.
      by rewrite in_itv/= r0.
    by rewrite fal ltxx.
  by rewrite -leNgt; apply: le_trans; rewrite leeD2r// fal.
move=> e; have [d /andP[lfp fpe]] := H e.
exists d => r /= [] prd rp.
by rewrite (le_lt_trans _ fpe)//; apply: ereal_sup_ubound => /=; exists r.
Qed.

Local Lemma lime_infP f a l :
  lime_inf f a = l%:E -> forall e : {posnum R}, exists d : {posnum R},
  forall x, (ball a d%:num `\ a) x -> l%:E - e%:num%:E < f x.
Proof.
move=> /(congr1 oppe); rewrite -lime_supN => /lime_supP => H e.
have [d {}H] := H e.
by exists d => r /H; rewrite lteNl oppeD// EFinN oppeK.
Qed.

Lemma lime_sup_inf_at_right f a l :
  lime_sup f a = l%:E -> lime_inf f a = l%:E -> f x @[x --> a^'+] --> l%:E.
Proof.
move=> supfpl inffpl; apply/cvge_at_rightP => u [pu up].
have fu : \forall n \near \oo, f (u n) \is a fin_num.
  have [dsup Hdsup] := lime_supP supfpl (PosNum ltr01).
  have [dinf Hdinf] := lime_infP inffpl (PosNum ltr01).
  near=> n; rewrite fin_numE; apply/andP; split.
    apply/eqP => fxnoo.
    suff : (ball a dinf%:num `\ a) (u n) by move=> /Hdinf; rewrite fxnoo.
    split; last by apply/eqP; rewrite gt_eqF.
    by near: n; move/cvgrPdist_lt : up; exact.
  apply/eqP => fxnoo.
  suff : (ball a dsup%:num `\ a) (u n) by move=> /Hdsup; rewrite fxnoo.
  split; last by apply/eqP; rewrite gt_eqF.
  by near: n; move/cvgrPdist_lt : up; exact.
apply/fine_cvgP; split => /=; first exact: fu.
apply/cvgrPdist_le => _/posnumP[e].
have [d1 Hd1] : exists d1 : {posnum R},
    l%:E - e%:num%:E <= ereal_inf [set f x | x in ball a d1%:num `\ a].
  have : l%:E - e%:num%:E < lime_inf f a.
    by rewrite inffpl lteBlDr// lteDl.
  rewrite lime_infE => /ereal_sup_gt[x /= [r]]; rewrite in_itv/= andbT.
  move=> r0 <-{x} H; exists (PosNum r0); rewrite ltW//.
  by rewrite -inf_ballE.
have [d2 Hd2] : exists d2 : {posnum R},
    ereal_sup [set f x | x in ball a d2%:num `\ a] <= l%:E + e%:num%:E.
  have : lime_sup f a < l%:E + e%:num%:E by rewrite supfpl lteDl.
  rewrite lime_supE => /ereal_inf_lt[x /= [r]]; rewrite in_itv/= andbT.
  by move=> r0 <-{x} H; exists (PosNum r0); rewrite ltW.
pose d := minr d1%:num d2%:num.
have d0 : (0 < d)%R by rewrite lt_min; apply/andP; split => //=.
move/cvgrPdist_lt : up => /(_ _ d0)[m _] {}ucvg.
near=> n.
rewrite /= ler_distlC; apply/andP; split.
  rewrite -lee_fin EFinB (le_trans Hd1)//.
  rewrite (@le_trans _ _ (ereal_inf [set f x | x in ball a d `\ a]))//.
    apply: le_ereal_inf => _/= [r [adr ra] <-]; exists r => //; split => //.
    by rewrite /ball/= (lt_le_trans adr)// /d ge_min lexx.
  apply: ereal_inf_lbound => /=; exists (u n).
    split; last by apply/eqP; rewrite eq_sym lt_eqF.
    by apply: ucvg => //=; near: n; exists m.
  by rewrite fineK//; by near: n.
rewrite -lee_fin EFinD (le_trans _ Hd2)//.
rewrite (@le_trans _ _ (ereal_sup [set f x | x in ball a d `\ a]))//; last first.
  apply: le_ereal_sup => z/= [r [adr rp] <-{z}]; exists r => //; split => //.
  by rewrite /ball/= (lt_le_trans adr)// /d ge_min lexx orbT.
apply: ereal_sup_ubound => /=; exists (u n).
  split; last by apply/eqP; rewrite eq_sym lt_eqF.
  by apply: ucvg => //=; near: n; exists m.
by rewrite fineK//; near: n.
Unshelve. all: by end_near. Qed.

Lemma lime_sup_inf_at_left f a l :
  lime_sup f a = l%:E -> lime_inf f a = l%:E -> f x @[x --> a^'-] --> l%:E.
Proof.
move=> supfal inffal; apply/cvg_at_leftNP/lime_sup_inf_at_right.
- by rewrite /lime_sup -limf_esup_dnbhsN.
- by rewrite /lime_inf /lime_sup -(limf_esup_dnbhsN (-%E \o f)) limf_esupN oppeK.
Qed.

End lime_sup_inf.
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `limf_esup_ge0` instead")]
Notation lime_sup_ge0 := __deprecated__lime_sup_ge0 (only parsing).

Section derivable_oo_continuous_bnd.
Context {R : numFieldType} {V : normedModType R}.

Definition derivable_oo_continuous_bnd (f : R -> V) (x y : R) :=
  [/\ {in `]x, y[, forall x, derivable f x 1},
      f @ x^'+ --> f x & f @ y^'- --> f y].

Lemma derivable_oo_continuous_bnd_within (f : R -> V) (x y : R) :
  derivable_oo_continuous_bnd f x y -> {within `[x, y], continuous f}.
Proof.
move=> [fxy fxr fyl]; apply/subspace_continuousP => z /=.
rewrite in_itv/= => /andP[]; rewrite le_eqVlt => /predU1P[<-{z} xy|].
  have := cvg_at_right_within fxr; apply: cvg_trans; apply: cvg_app.
  by apply: within_subset => z/=; rewrite in_itv/= => /andP[].
move=> /[swap].
rewrite le_eqVlt => /predU1P[->{z} xy|zy xz].
  have := cvg_at_left_within fyl; apply: cvg_trans; apply: cvg_app.
  by apply: within_subset => z/=; rewrite in_itv/= => /andP[].
apply: cvg_within_filter.
apply/differentiable_continuous; rewrite -derivable1_diffP.
by apply: fxy; rewrite in_itv/= xz zy.
Qed.

End derivable_oo_continuous_bnd.

Section real_inverse_functions.
Variable R : realType.
Implicit Types (a b : R) (f g : R -> R).

(** This lemma should be used with caution. Generally `{within I, continuous f}`
   is what one would intend. So having `{in I, continuous f}` as a condition
   may indicate potential issues at the endpoints of the interval. *)
Lemma continuous_subspace_itv (I : interval R) (f : R -> R) :
  {in I, continuous f} -> {within [set` I], continuous f}.
Proof.
move=> ctsf; apply: continuous_in_subspaceT => x Ix; apply: ctsf.
by move: Ix; rewrite inE.
Qed.

Lemma itv_continuous_inj_le f (I : interval R) :
  (exists x y, [/\ x \in I, y \in I, x < y & f x <= f y]) ->
  {within [set` I], continuous f} -> {in I &, injective f} ->
  {in I &, {mono f : x y / x <= y}}.
Proof.
gen have fxy : f / {in I &, injective f} ->
    {in I &, forall x y, x < y -> f x != f y}.
  move=> fI x y xI yI xLy; apply/negP => /eqP /fI => /(_ xI yI) xy.
  by move: xLy; rewrite xy ltxx.
gen have main : f / forall c, {within [set` I], continuous f} ->
    {in I &, injective f} ->
    {in I &, forall a b, f a < f b -> a < c -> c < b -> f a < f c /\ f c < f b}.
  move=> c fC fI a b aI bI faLfb aLc cLb.
  have intP := interval_is_interval aI bI.
  have cI : c \in I by rewrite intP// (ltW aLc) ltW.
  have ctsACf : {within `[a, c], continuous f}.
    apply: (continuous_subspaceW _ fC) => x; rewrite /= inE => /itvP axc.
    by rewrite intP// axc/= (le_trans _ (ltW cLb))// axc.
  have ctsCBf : {within `[c, b], continuous f}.
    apply: (continuous_subspaceW _ fC) => x /=; rewrite inE => /itvP axc.
    by rewrite intP// axc andbT (le_trans (ltW aLc)) ?axc.
  have [aLb alb'] : a < b /\ a <= b by rewrite ltW (lt_trans aLc).
  have [faLfc|fcLfa|/eqP faEfc] /= := ltrgtP (f a) (f c).
  - split; rewrite // lt_neqAle fxy // leNgt; apply/negP => fbLfc.
    have := fbLfc; suff /eqP -> : c == b by rewrite ltxx.
    rewrite eq_le (ltW cLb) /=.
    have [d /andP[ad dc] fdEfb] : exists2 d, a <= d <= c & f d = f b.
      have aLc' : a <= c by rewrite ltW.
      apply: IVT => //; last first.
        by case: ltrgtP faLfc; rewrite // (ltW faLfb) // ltW.
    rewrite -(fI _ _ _ _ fdEfb) //.
    move: ad dc; rewrite le_eqVlt =>/predU1P[<-//| /ltW L] dc.
    by rewrite intP// L (le_trans _ (ltW cLb)).
  - have [fbLfc | fcLfb | fbEfc] /= := ltrgtP (f b) (f c).
    + by have := lt_trans fbLfc fcLfa; rewrite ltNge (ltW faLfb).
    + have [d /andP[cLd dLb] /eqP] : exists2 d, c <= d <= b & f d = f a.
        have cLb' : c <= b by rewrite ltW.
        apply: IVT => //; last by case: ltrgtP fcLfb; rewrite // !ltW.
      have /(fxy f fI) : a < d by rewrite (lt_le_trans aLc).
      suff dI' : d \in I by rewrite eq_sym=> /(_ aI dI') => /negbTE ->.
      move: dLb; rewrite le_eqVlt => /predU1P[->//|/ltW db].
      by rewrite intP// db  (le_trans (ltW aLc)).
    + by move: fcLfa; rewrite -fbEfc ltNge (ltW faLfb).
  by move/(fxy _ fI) : aLc=> /(_ aI cI); rewrite faEfc.
move=> [u [v [uI vI ulv +]]] fC fI; rewrite le_eqVlt => /predU1P[fufv|fuLfv].
  by move/fI: fufv => /(_ uI vI) uv; move: ulv; rewrite uv ltxx.
have aux a c b : a \in I -> b \in I -> a < c -> c < b ->
   (f a < f c -> f a < f b /\ f c < f b) /\
   (f c < f b -> f a < f b /\ f a < f c).
  move=> aI bI aLc cLb; have aLb := lt_trans aLc cLb.
  have cI : c \in I by rewrite (interval_is_interval aI bI)// (ltW aLc)/= ltW.
  have fanfb : f a != f b by apply: (fxy f fI).
  have decr : f b  < f a -> f b < f c /\ f c < f a.
    have ofC : {within [set` I], continuous (-f)}.
      move=> ?; apply: continuous_comp; [exact: fC | exact: continuousN].
    have ofI : {in I &, injective (-f)} by move=>> ? ? /oppr_inj/fI ->.
    rewrite -[X in X < _ -> _](opprK (f b)) ltrNl => ofaLofb.
    have := main _ c ofC ofI a b aI bI ofaLofb aLc cLb.
    by (do 2 rewrite ltrNl opprK); rewrite and_comm.
  split=> [faLfc|fcLfb].
    suff L : f a < f b by have [] := main f c fC fI a b aI bI L aLc cLb.
    by case: ltgtP decr fanfb => // fbfa []//; case: ltgtP faLfc.
  suff L : f a < f b by have [] := main f c fC fI a b aI bI L aLc cLb.
  by case: ltgtP decr fanfb => // fbfa []//; case: ltgtP fcLfb.
have{main fC} whole a c b := main f c fC fI a b.
have low a c b : f a < f c -> a \in I -> b \in I ->
       a < c -> c < b -> f a < f b /\ f c < f b.
  by move=> L aI bI ac cb; case: (aux a c b aI bI ac cb)=> [/(_ L)].
have high a c b : f c < f b -> a \in I -> b \in I ->
     a < c -> c < b -> f a < f b /\ f a < f c.
  by move=> L aI bI ac cb; case: (aux a c b aI bI ac cb)=> [_ /(_ L)].
apply: le_mono_in => x y xI yI xLy.
have [uLx | xLu | xu] := ltrgtP u x.
- suff fuLfx : f u < f x by have [] := low u x y fuLfx uI yI uLx xLy.
  have [xLv | vLx | -> //] := ltrgtP x v; first by case: (whole u x v).
  by case: (low u v x).
- have fxLfu : f x < f u by have [] := high x u v fuLfv xI vI xLu ulv.
  have [yLu | uLy | -> //] := ltrgtP y u; first by case: (whole x y u).
  by case: (low x u y).
move: xLy; rewrite -xu => uLy.
have [yLv | vLy | -> //] := ltrgtP y v; first by case: (whole u y v).
by case: (low u v y).
Qed.

Lemma itv_continuous_inj_ge f (I : interval R) :
  (exists x y, [/\ x \in I, y \in I, x < y & f y <= f x]) ->
  {within [set` I], continuous f} -> {in I &, injective f} ->
  {in I &, {mono f : x y /~ x <= y}}.
Proof.
move=> [a [b [aI bI ab fbfa]]] fC fI x y xI yI.
suff : (- f) y <= (- f) x = (y <= x) by rewrite lerNl opprK.
apply: itv_continuous_inj_le xI => // [|x1 x1I | x1 x2 x1I x2I].
- by exists a, b; split => //; rewrite lerNl opprK.
- by apply/continuousN/fC.
by move/oppr_inj; apply/fI.
Qed.

Lemma itv_continuous_inj_mono f (I : interval R) :
    {within [set` I], continuous f} -> {in I &, injective f} -> monotonous I f.
Proof.
move=> fC fI.
case: (pselect (exists a b, [/\ a \in I , b \in I & a < b])); last first.
  move=> N2I; left => x y xI yI; suff -> : x = y by rewrite ?lexx.
  by apply: contra_notP N2I => /eqP; case: ltgtP; [exists x, y|exists y, x|].
move=> [a [b [aI bI lt_ab]]].
have /orP[faLfb|fbLfa] := le_total (f a) (f b).
  by left; apply: itv_continuous_inj_le => //; exists a, b; rewrite ?faLfb.
by right; apply: itv_continuous_inj_ge => //; exists a, b; rewrite ?fbLfa.
Qed.

Lemma segment_continuous_inj_le f a b :
    f a <= f b -> {within `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y / x <= y}}.
Proof.
move=> fafb fct finj; have [//|] := itv_continuous_inj_mono fct finj.
have [aLb|bLa|<-] := ltrgtP a b; first 1 last.
- by move=> _ x ?; rewrite itv_ge// -ltNge.
- by move=> _ x y /itvxxP-> /itvxxP->; rewrite !lexx.
move=> /(_ a b); rewrite !bound_itvE fafb.
by move=> /(_ (ltW aLb) (ltW aLb)); rewrite lt_geF.
Qed.

Lemma segment_continuous_inj_ge f a b :
    f a >= f b -> {within `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y /~ x <= y}}.
Proof.
move=> fafb fct finj; have [|//] := itv_continuous_inj_mono fct finj.
have [aLb|bLa|<-] := ltrgtP a b; first 1 last.
- by move=> _ x ?; rewrite itv_ge// -ltNge.
- by move=> _ x y /itvxxP-> /itvxxP->; rewrite !lexx.
move=> /(_ b a); rewrite !bound_itvE fafb.
by move=> /(_ (ltW aLb) (ltW aLb)); rewrite lt_geF.
Qed.

(** The condition "f a <= f b" is unnecessary because the last
    interval condition is vacuously true otherwise. *)
Lemma segment_can_le a b f g : a <= b ->
    {within `[a, b], continuous f} ->
    {in `[a, b], cancel f g} ->
  {in `[f a, f b] &, {mono g : x y / x <= y}}.
Proof.
move=> aLb ctf fK; have [fbLfa | faLfb] := ltrP (f b) (f a).
  by move=> x y; rewrite itv_ge// -ltNge.
have [aab bab] : a \in `[a, b] /\ b \in `[a, b] by rewrite !bound_itvE.
case: ltgtP faLfb => // [faLfb _|-> _ _ _ /itvxxP-> /itvxxP->]; rewrite ?lexx//.
have lt_ab : a < b by case: (ltgtP a b) aLb faLfb => // ->; rewrite ltxx.
have w : exists x y, [/\ x \in `[a, b], y \in `[a, b], x < y & f x <= f y].
  by exists a, b; rewrite !bound_itvE (ltW faLfb).
have fle := itv_continuous_inj_le w ctf (can_in_inj fK).
move=> x y xin yin; have := IVT aLb ctf.
case: (ltrgtP (f a) (f b)) faLfb => // _ _ ivt.
by have [[u uin <-] [v vin <-]] := (ivt _ xin, ivt _ yin); rewrite !fK// !fle.
Qed.

Section negation_itv.
Local Definition itvN_oppr a b := @GRing.opp R.
Local Lemma itv_oppr_is_fun a b :
  isFun _ _ `[- b, - a]%classic `[a, b]%classic (itvN_oppr a b).
Proof. by split=> x /=; rewrite oppr_itvcc. Qed.
HB.instance Definition _ a b := itv_oppr_is_fun a b.
End negation_itv.

(** The condition "f b <= f a" is unnecessary---see seg...increasing above    *)
Lemma segment_can_ge a b f g : a <= b ->
    {within `[a, b], continuous f} ->
    {in `[a, b], cancel f g} ->
  {in `[f b, f a] &, {mono g : x y /~ x <= y}}.
Proof.
move=> aLb fC fK x y xfbfa yfbfa; rewrite -lerN2.
apply: (@segment_can_le (- b) (- a) (f \o -%R) (- g));
    rewrite /= ?lerN2 ?opprK //.
  pose fun_neg : subspace `[-b,-a] -> subspace `[a,b] := itvN_oppr a b.
  move=> z; apply: (@continuous_comp _ _ _ [fun of fun_neg]); last exact: fC.
  exact/subspaceT_continuous/continuous_subspaceT/opp_continuous.
by move=> z zab; rewrite -[- g]/(@GRing.opp _ \o g)/= fK ?opprK// oppr_itvcc.
Qed.

Lemma segment_can_mono a b f g : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  monotonous (f @`[a, b]) g.
Proof.
move=> le_ab fct fK; rewrite /monotonous/=; case: ltrgtP => fab; [left|right..];
  do ?by [apply: segment_can_le|apply: segment_can_ge].
by move=> x y /itvxxP<- /itvxxP<-; rewrite !lexx.
Qed.

Lemma segment_continuous_surjective a b f : a <= b ->
  {within `[a, b], continuous f} -> set_surj `[a, b] (f @`[a, b]) f.
Proof. by move=> ? fct y/= /IVT[]// x; exists x. Qed.

Lemma segment_continuous_le_surjective a b f : a <= b -> f a <= f b ->
  {within `[a, b], continuous f} -> set_surj `[a, b] `[f a, f b] f.
Proof.
move=> le_ab f_ab /(segment_continuous_surjective le_ab).
by rewrite (min_idPl _)// (max_idPr _).
Qed.

Lemma segment_continuous_ge_surjective a b f : a <= b -> f b <= f a ->
  {within `[a, b], continuous f} -> set_surj `[a, b] `[f b, f a] f.
Proof.
move=> le_ab f_ab /(segment_continuous_surjective le_ab).
by rewrite (min_idPr _)// (max_idPl _).
Qed.

Lemma continuous_inj_image_segment a b f : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  f @` `[a, b] = f @`[a, b]%classic.
Proof.
move=> leab fct finj; apply: mono_surj_image_segment => //.
  exact: itv_continuous_inj_mono.
exact: segment_continuous_surjective.
Qed.

Lemma continuous_inj_image_segmentP a b f : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in f @`[a, b]).
Proof.
move=> /continuous_inj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) faby.
by apply/(equivP idP); symmetry.
Qed.

Lemma segment_continuous_can_sym a b f g : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in f @`[a, b], cancel g f}.
Proof.
move=> aLb ctf fK; have g_mono := segment_can_mono aLb ctf fK.
have f_mono := itv_continuous_inj_mono ctf (can_in_inj fK).
have f_surj := segment_continuous_surjective aLb ctf.
have fIP := mono_surj_image_segmentP aLb f_mono f_surj.
suff: {in f @`[a, b], {on `[a, b], cancel g & f}}.
  by move=> gK _ /fIP[x xab <-]; rewrite fK.
have: {in f @`[a, b] &, {on `[a, b]  &, injective g}}.
  by move=> _ _ /fIP [x xab <-] /fIP[y yab <-]; rewrite !fK// => _ _ ->.
by apply/ssrbool.inj_can_sym_in_on => x xab; rewrite ?fK ?mono_mem_image_segment.
Qed.

Lemma segment_continuous_le_can_sym a b f g : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in `[f a, f b], cancel g f}.
Proof.
move=> aLb fct fK x xfafb; apply: (segment_continuous_can_sym aLb fct fK).
have : f a <= f b by rewrite (itvP xfafb).
by case: ltrgtP xfafb => // ->.
Qed.

Lemma segment_continuous_ge_can_sym a b f g : a <= b ->
    {within `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in `[f b, f a], cancel g f}.
Proof.
move=> aLb fct fK x xfafb; apply: (segment_continuous_can_sym aLb fct fK).
have : f a >= f b by rewrite (itvP xfafb).
by case: ltrgtP xfafb => // ->.
Qed.

Lemma segment_inc_surj_continuous a b f :
    {in `[a, b] &, {mono f : x y / x <= y}} -> set_surj `[a, b] `[f a, f b] f ->
  {within `[a, b], continuous f}.
Proof.
move=> fle f_surj; have [f_inj flt] := (inc_inj_in fle, leW_mono_in fle).
have [aLb|bLa|] := ltgtP a b; first last.
- by move=> ->; rewrite set_itv1; exact: continuous_subspace1.
- rewrite continuous_subspace_in => z /set_mem /=; rewrite in_itv /=.
  by move=> /andP[/le_trans] /[apply]; rewrite leNgt bLa.
have le_ab : a <= b by rewrite ltW.
have [aab bab] : a \in `[a, b] /\ b \in `[a, b] by rewrite !bound_itvE ltW.
have fab : f @` `[a, b] = `[f a, f b]%classic by exact:inc_surj_image_segment.
pose g := pinv `[a, b] f; have fK : {in `[a, b], cancel f g}.
  by rewrite -[mem _]mem_setE; apply: pinvKV; rewrite !mem_setE.
have gK : {in `[f a, f b], cancel g f} by move=> z zab; rewrite pinvK// fab inE.
have gle : {in `[f a, f b] &, {mono g : x y / x <= y}}.
  apply: can_mono_in (fle); first by move=> *; rewrite gK.
  move=> z zfab; have {zfab} : `[f a, f b]%classic z by [].
  by rewrite -fab => -[x xab <-]; rewrite fK.
have glt := leW_mono_in gle.
rewrite continuous_subspace_in => x xab.
have xabcc : x \in `[a, b] by move: xab; rewrite mem_setE.
have fxab : f x \in `[f a, f b] by rewrite in_itv/= !fle.
have := xabcc; rewrite in_itv //= => /andP [ax xb].
apply/cvgrPdist_lt => _ /posnumP[e]; rewrite !near_simpl; near=> y.
rewrite (@le_lt_trans _ _ (e%:num / 2%:R))//; last first.
  by rewrite ltr_pdivrMr// ltr_pMr// ltr1n.
rewrite ler_distlC; near: y.
pose u := minr (f x + e%:num / 2) (f b).
pose l := maxr (f x - e%:num / 2) (f a).
have ufab : u \in `[f a, f b].
  rewrite !in_itv /= ge_min ?le_min lexx ?fle // le_ab orbT ?andbT.
  by rewrite ler_wpDr // fle.
have lfab : l \in `[f a, f b].
  rewrite !in_itv/= ge_max ?le_max lexx ?fle// le_ab orbT ?andbT.
  by rewrite lerBlDr ler_wpDr// fle // lexx.
have guab : g u \in `[a, b].
  rewrite !in_itv; apply/andP; split; have := ufab; rewrite in_itv => /andP.
    by case; rewrite /= -[f _ <= _]gle // ?fK // bound_itvE fle.
  by case => _; rewrite /= -[_ <= f _]gle // ?fK // bound_itvE fle.
have glab : g l \in `[a, b].
  rewrite !in_itv; apply/andP; split; have := lfab; rewrite in_itv /= => /andP.
    by case; rewrite -[f _ <= _]gle // ?fK // bound_itvE fle.
  by case => _; rewrite -[_ <= f _]gle // ?fK // bound_itvE fle.
have faltu : f a < u.
  rewrite /u comparable_lt_min ?real_comparable ?num_real// flt// aLb andbT.
  by rewrite (@le_lt_trans _ _ (f x)) ?fle// ltrDl.
have lltfb : l < f b.
  rewrite /u comparable_gt_max ?real_comparable ?num_real// flt// aLb andbT.
  by rewrite (@lt_le_trans _ _ (f x)) ?fle// ltrBlDr ltrDl.
case: pselect => // _; rewrite near_withinE; near_simpl.
have Fnbhs : Filter (nbhs x) by apply: nbhs_filter.
have := ax; rewrite le_eqVlt => /orP[/eqP|] {}ax.
  near=> y => /[dup] yab; rewrite /= in_itv => /andP[ay yb]; apply/andP; split.
    by rewrite (@le_trans _ _ (f a)) ?fle// lerBlDr ax ler_wpDr.
  apply: ltW; suff : f y < u by rewrite lt_min => /andP[->].
  rewrite -?[f y < _]glt// ?fK//; last by rewrite in_itv /= !fle.
  by near: y; near_simpl; apply: open_lt; rewrite /= -flt ?gK// -ax.
have := xb; rewrite le_eqVlt => /orP[/eqP {}xb {ax}|{}xb].
  near=> y => /[dup] yab; rewrite /= in_itv /= => /andP[ay yb].
  apply/andP; split; last by rewrite (@le_trans _ _ (f b)) ?fle// xb ler_wpDr.
  apply: ltW; suff : l < f y by rewrite gt_max => /andP[->].
  rewrite -?[_ < f y]glt// ?fK//; last by rewrite in_itv /= !fle.
  by near: y; near_simpl; apply: open_gt; rewrite /= -flt// gK// xb.
have xoab : x \in `]a, b[ by rewrite in_itv /=; apply/andP; split.
near=> y; suff: l <= f y <= u.
  by rewrite ge_max le_min -!andbA => /and4P[-> _ ->].
have ? : y \in `[a, b] by apply: subset_itv_oo_cc; near: y; exact: near_in_itvoo.
have fyab : f y \in `[f a, f b] by rewrite in_itv/= !fle// ?ltW.
rewrite -[l <= _]gle -?[_ <= u]gle// ?fK //.
apply: subset_itv_oo_cc; near: y; apply: near_in_itvoo; rewrite in_itv /=.
rewrite -[x]fK // !glt//= lt_min gt_max ?andbT ltrBlDr ltr_pwDr //.
by apply/and3P; split; rewrite // flt.
Unshelve. all: by end_near. Qed.

Lemma segment_dec_surj_continuous a b f :
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  {within `[a, b], continuous f}.
Proof.
move=> fge f_surj; suff: {within `[a, b], continuous (- f)}.
  move=> contNf x xab; rewrite -[f]opprK.
  exact/continuous_comp/opp_continuous/contNf.
apply: segment_inc_surj_continuous.
  by move=> x y xab yab; rewrite lerN2 fge.
by move=> y /=; rewrite -oppr_itvcc => /f_surj[x ? /(canLR opprK)<-]; exists x.
Qed.

Lemma segment_mono_surj_continuous a b f :
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  {within `[a, b], continuous f}.
Proof.
rewrite continuous_subspace_in => -[fle|fge] f_surj x /set_mem /= xab.
  have leab : a <= b by rewrite (itvP xab).
  have fafb : f a <= f b by rewrite fle // ?bound_itvE.
  by apply: segment_inc_surj_continuous => //; case: ltrP f_surj fafb.
have leab : a <= b by rewrite (itvP xab).
have fafb : f b <= f a by rewrite fge // ?bound_itvE.
by apply: segment_dec_surj_continuous => //; case: ltrP f_surj fafb.
Qed.

Lemma segment_can_le_continuous a b f g : a <= b ->
  {within `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {within `[(f a), (f b)], continuous g}.
Proof.
move=> aLb ctf; rewrite continuous_subspace_in => fK x /set_mem /= xab.
have faLfb : f a <= f b by rewrite (itvP xab).
apply: segment_inc_surj_continuous; first exact: segment_can_le.
rewrite !fK ?bound_itvE//=; apply: (@can_surj _ _ f); first by rewrite mem_setE.
exact/image_subP/mem_inc_segment/segment_continuous_inj_le/(can_in_inj fK).
Qed.

Lemma segment_can_ge_continuous a b f g : a <= b ->
  {within `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {within `[(f b), (f a)], continuous g}.
Proof.
move=> aLb ctf; rewrite continuous_subspace_in => fK x /set_mem /= xab.
have fbLfa : f b <= f a by rewrite (itvP xab).
apply: segment_dec_surj_continuous; first exact: segment_can_ge.
rewrite !fK ?bound_itvE//=; apply: (@can_surj _ _ f); first by rewrite mem_setE.
exact/image_subP/mem_dec_segment/segment_continuous_inj_ge/(can_in_inj fK).
Qed.

Lemma segment_can_continuous a b f g : a <= b ->
  {within `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {within f @`[a, b], continuous g}.
Proof.
move=> aLb crf fK x; case: lerP => // _;
  by [apply: segment_can_ge_continuous|apply: segment_can_le_continuous].
Qed.

Lemma near_can_continuousAcan_sym f g (x : R) :
    {near x, cancel f g} -> {near x, continuous f} ->
  {near f x, continuous g} /\ {near f x, cancel g f}.
Proof.
move=> fK fct; near (0 : R)^'+ => e; have e_gt0 : 0 < e by [].
have xBeLxDe : x - e <= x + e by rewrite lerD2l gt0_cp.
have fcte : {in `[x - e, x + e], continuous f}.
  by near: e; apply/at_right_in_segment.
have fwcte : {within `[x - e, x + e], continuous f}.
  apply: continuous_in_subspaceT => y yI.
  by apply: fcte; move/set_mem: yI.
have fKe : {in `[x - e, x + e], cancel f g}
  by near: e; apply/at_right_in_segment.
have nearfx : \forall y \near f x, y \in f @`](x - e), (x + e)[.
  apply: near_in_itvoo; apply: mono_mem_image_itvoo; last first.
    by rewrite in_itv/= -ltr_distlC subrr normr0.
  apply: itv_continuous_inj_mono => //.
  by apply: (@can_in_inj _ _ _ _ g); near: e; apply/at_right_in_segment.
have fxI : f x \in f @`]x - e, x + e[ by exact: (nbhs_singleton nearfx).
split; near=> y; first last.
  rewrite (@segment_continuous_can_sym (x - e) (x + e))//.
  by apply: subset_itv_oo_cc; near: y.
near: y; apply: (filter_app _ _ nearfx); near_simpl; near=> y => yfe.
have : {within f @`]x - e, (x + e)[, continuous g}.
  apply: continuous_subspaceW; last exact: (segment_can_continuous _ fwcte _).
  exact: subset_itv_oo_cc.
rewrite continuous_open_subspace; first by apply; exact: mem_set.
exact: interval_open.
Unshelve. all: by end_near. Qed.

Lemma near_can_continuous f g (x : R) :
  {near x, cancel f g} -> {near x, continuous f} -> {near f x, continuous g}.
Proof. by move=> fK fct; have [] := near_can_continuousAcan_sym fK fct. Qed.

Lemma near_continuous_can_sym f g (x : R) :
  {near x, continuous f} -> {near x, cancel f g} -> {near f x, cancel g f}.
Proof. by move=> fct fK; have [] := near_can_continuousAcan_sym fK fct. Qed.

End real_inverse_functions.

Section real_inverse_function_instances.
Variable R : realType.

Lemma exprn_continuous n : continuous (@GRing.exp R ^~ n).
Proof.
move=> x; elim: n=> [|n /(continuousM cvg_id) ih]; first exact: cst_continuous.
by rewrite /continuous_at exprS; under eq_fun do rewrite exprS; exact: ih.
Qed.

Lemma sqr_continuous : continuous (@exprz R ^~ 2).
Proof. exact: (@exprn_continuous 2%N). Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x; case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0).
  by near do rewrite ltr0_sqrtr//; apply: (cvgr_lt x).
  pose I b : set R := [set` `]0 ^+ 2, b ^+ 2[].
  suff main b : 0 <= b -> {in I b, continuous (@Num.sqrt R)}.
    near +oo_R => M; apply: (main M); rewrite // /I !inE/= in_itv/= expr0n xgt0.
    by rewrite -ltr_sqrt ?exprn_gt0// sqrtr_sqr gtr0_norm/=.
  move=> b0; rewrite -continuous_open_subspace; last exact: interval_open.
  apply: continuous_subspaceW; first exact: subset_itv_oo_cc.
  apply: (@segment_can_le_continuous _ _ _ (@GRing.exp _^~ _)) => //.
    by apply: continuous_subspaceT; exact: exprn_continuous.
  by move=> y y0b; rewrite sqrtr_sqr ger0_norm// (itvP y0b).
- rewrite /continuous_at sqrtr0; apply/cvgr0Pnorm_lt => _ /posnumP[e]; near=> y.
  have [ylt0|yge0] := ltrP y 0; first by rewrite ltr0_sqrtr ?normr0.
  rewrite ger0_norm ?sqrtr_ge0//; have: `|y| < e%:num ^+ 2 by [].
  by rewrite -ltr_sqrt// ger0_norm// sqrtr_sqr ger0_norm.
Unshelve. all: by end_near. Qed.

End real_inverse_function_instances.

Section is_derive_inverse.
Variable R : realType.

(* Attempt to prove the diff of inverse *)
Lemma is_derive1_caratheodory (f : R -> R) (x a : R) :
  is_derive x 1 f a <->
  exists g, [/\ forall z, f z - f x = g z * (z - x),
        {for x, continuous g} & g x = a].
Proof.
split => [Hd|[g [fxE Cg gxE]]].
  exists (fun z => if z == x then a else (f(z) - f(x)) / (z - x)); split.
  - move=> z; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
    by rewrite -subr_eq0 => /divfK->.
  - apply/continuous_withinNshiftx; rewrite eqxx /=.
    pose g1 h := (h^-1 *: ((f \o shift x) h%:A - f x)).
    have F1 : g1 @ 0^' --> a by case: Hd => H1 <-.
    apply: cvg_trans F1; apply: near_eq_cvg; rewrite /g1 !fctE.
    near=> i.
    rewrite ifN; first by rewrite addrK mulrC /= [_%:A]mulr1.
    rewrite -subr_eq0 addrK.
    by near: i; rewrite near_withinE /= near_simpl; near=> x1.
  by rewrite eqxx.
suff Hf : h^-1 *: ((f \o shift x) h%:A - f x) @[h --> 0^'] --> a.
  have F1 : 'D_1 f x = a by apply: cvg_lim.
  rewrite -F1 in Hf.
    by constructor.
  have F1 :  (g \o shift x) y @[y --> 0^'] --> a.
  by rewrite -gxE; apply/continuous_withinNshiftx.
apply: cvg_trans F1; apply: near_eq_cvg.
near=> y.
rewrite /= fxE /= addrK [_%:A]mulr1.
suff yNZ : y != 0 by rewrite [RHS]mulrC mulfK.
by near: y; rewrite near_withinE /= near_simpl; near=> x1.
Unshelve. all: by end_near. Qed.

Lemma is_derive_0_is_cst (f : R -> R) x y :
  (forall x, is_derive x (1 : R) f 0) -> f x = f y.
Proof.
move=> Hd.
wlog xLy : x y / x <= y by move=> H; case: (leP x y) => [/H |/ltW /H].
rewrite -(subKr (f y) (f x)).
have [| _ _] := MVT_segment xLy; last by rewrite mul0r => ->; rewrite subr0.
apply/continuous_subspaceT=> r.
exact/differentiable_continuous/derivable1_diffP.
Qed.

Global Instance is_derive1_comp (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b ->
  is_derive x 1 (f \o g) (a * b).
Proof.
move=> [fgxv <-{a}] [gv <-{b}]; apply: (@DeriveDef _ _ _ _ _ (f \o g)).
  apply/derivable1_diffP/differentiable_comp; first exact/derivable1_diffP.
  by move/derivable1_diffP in fgxv.
by rewrite -derive1E (derive1_comp gv fgxv) 2!derive1E.
Qed.

Lemma is_deriveV (f : R -> R) (x t v : R) :
  f x != 0 -> is_derive x v f t ->
  is_derive x v (fun y => (f y)^-1) (- (f x) ^- 2 *: t).
Proof.
move=> fxNZ Df.
constructor; first by apply: derivableV => //; case: Df.
by rewrite deriveV //; case: Df => _ ->.
Qed.

Lemma is_derive_inverse (f g : R -> R) l x :
  {near x, cancel f g}  ->
  {near x, continuous f}  ->
  is_derive x 1 f l -> l != 0 -> is_derive (f x) 1 g l^-1.
Proof.
move=> fgK fC fD lNZ.
have /is_derive1_caratheodory [h [fE hC hxE]] := fD.
(* There should be something simpler *)
have gfxE : g (f x) = x by have [d Hd]:= nbhs_ex fgK; apply: Hd.
pose g1 y := if y == f x then (h (g y))^-1
             else (g y - g (f x)) / (y - f x).
apply/is_derive1_caratheodory.
exists g1; split; first 2 last.
- by rewrite /g1 eqxx gfxE hxE.
- move=> z; rewrite /g1; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
  by rewrite -subr_eq0 => /divfK.
have F1 : (h (g x))^-1 @[x --> f x] --> g1 (f x).
  rewrite /g1 eqxx; apply: continuousV; first by rewrite /= gfxE hxE.
  apply: continuous_comp; last by rewrite gfxE.
  by apply: nbhs_singleton (near_can_continuous _ _).
apply: cvg_sub0 F1.
apply/cvgrPdist_lt => eps eps_gt0 /=; rewrite !near_simpl /=.
near=> y; rewrite sub0r normrN !fctE.
have fgyE : f (g y) = y by near: y; apply: near_continuous_can_sym.
rewrite /g1; case: eqP => [_|/eqP x1Dfx]; first by rewrite subrr normr0.
have -> : y - f x  = h (g y) * (g y - x) by rewrite -fE fgyE.
rewrite gfxE invfM mulrC divfK ?subrr ?normr0 // subr_eq0.
by apply: contra x1Dfx => /eqP<-; apply/eqP.
Unshelve. all: by end_near. Qed.

End is_derive_inverse.

#[global] Hint Extern 0 (is_derive _ _ (fun _ => (_ _)^-1) _) =>
  (eapply is_deriveV; first by []) : typeclass_instances.

Section interval_partition.
Context {R : realType}.
Implicit Type (a b : R) (s : seq R).

(** a :: s is a partition of the interval [a, b] *)
Definition itv_partition a b s := [/\ path <%R a s & last a s == b].

Lemma itv_partition_nil a b : itv_partition a b [::] -> a = b.
Proof. by move=> [_ /eqP <-]. Qed.

Lemma itv_partition_cons a b x s :
  itv_partition a b (x :: s) -> itv_partition x b s.
Proof. by rewrite /itv_partition/= => -[/andP[]]. Qed.

Lemma itv_partition1 a b : a < b -> itv_partition a b [:: b].
Proof. by rewrite /itv_partition /= => ->. Qed.

Lemma itv_partition_size_neq0 a b s :
  (size s > 0)%N -> itv_partition a b s -> a < b.
Proof.
elim: s a => // x [_ a _|h t ih a _]; rewrite /itv_partition /=.
  by rewrite andbT => -[ax /eqP <-].
move=> [] /andP[ax /andP[xy] ht /eqP tb].
by rewrite (lt_trans ax)// ih// /itv_partition /= xy/= tb.
Qed.

Lemma itv_partitionxx a s : itv_partition a a s -> s = [::].
Proof.
case: s => //= h t [/= /andP[ah /lt_path_min/allP ht] /eqP hta].
suff : h < a by move/lt_trans => /(_ _ ah); rewrite ltxx.
apply/ht; rewrite -hta.
by have := mem_last h t; rewrite inE hta lt_eqF.
Qed.

Lemma itv_partition_le a b s : itv_partition a b s -> a <= b.
Proof.
case: s => [/itv_partition_nil ->//|h t /itv_partition_size_neq0 - /(_ _)/ltW].
exact.
Qed.

Lemma itv_partition_cat a b c s t :
  itv_partition a b s -> itv_partition b c t -> itv_partition a c (s ++ t).
Proof.
rewrite /itv_partition => -[sa /eqP asb] [bt btc].
by rewrite cat_path// sa /= last_cat asb.
Qed.

Lemma itv_partition_nth_size def a b s : itv_partition a b s ->
  nth def (a :: s) (size s) = b.
Proof.
by elim: s a => [a/= /itv_partition_nil//|y t ih a /= /itv_partition_cons/ih].
Qed.

Lemma itv_partition_nth_ge a b s m : (m < (size s).+1)%N ->
  itv_partition a b s -> a <= nth b (a :: s) m.
Proof.
elim: m s a b => [s a b _//|n ih [//|h t] a b].
rewrite ltnS => nh [/= /andP[ah ht] lb].
by rewrite (le_trans (ltW ah))// ih.
Qed.

Lemma itv_partition_nth_le a b s m : (m < (size s).+1)%N ->
  itv_partition a b s -> nth b (a :: s) m <= b.
Proof.
elim: m s a => [s a _|n ih]; first exact: itv_partition_le.
by move=> [//|a h t /= nt] H; rewrite ih//; exact: itv_partition_cons H.
Qed.

Lemma nondecreasing_fun_itv_partition a b f s :
  {in `[a, b] &, nondecreasing_fun f} -> itv_partition a b s ->
  let F : nat -> R := f \o nth b (a :: s) in
  forall k, (k < size s)%N -> F k <= F k.+1.
Proof.
move=> ndf abs F k ks.
have [_] := nondecreasing_seqP F; apply => m n mn; rewrite /F/=.
have [ms|ms] := ltnP m (size s).+1; last first.
  rewrite nth_default//.
  have [|ns] := ltnP n (size s).+1; last by rewrite nth_default.
  by move=> /(leq_ltn_trans mn); rewrite ltnS leqNgt ms.
have [ns|ns] := ltnP n (size s).+1; last first.
  rewrite [in leRHS]nth_default//=; apply/ndf/itv_partition_nth_le => //.
    by rewrite in_itv/= itv_partition_nth_le// andbT itv_partition_nth_ge.
  by rewrite in_itv/= lexx andbT; exact: (itv_partition_le abs).
move: abs; rewrite /itv_partition => -[] sa sab.
move: mn; rewrite leq_eqVlt => /predU1P[->//|mn].
apply/ndf/ltW/sorted_ltn_nth => //=; last exact: lt_trans.
  by rewrite in_itv/= itv_partition_nth_le// andbT itv_partition_nth_ge.
by rewrite in_itv/= itv_partition_nth_le// andbT itv_partition_nth_ge.
Qed.

Lemma nonincreasing_fun_itv_partition a b f s :
  {in `[a, b] &, nonincreasing_fun f} -> itv_partition a b s ->
  let F : nat -> R := f \o nth b (a :: s) in
  forall k, (k < size s)%N -> F k.+1 <= F k.
Proof.
move/nonincreasing_funN => ndNf abs F k ks; rewrite -(opprK (F k)) lerNr.
exact: (nondecreasing_fun_itv_partition ndNf abs).
Qed.

(** given a partition of [a, b] and c, returns a partition of [a, c] *)
Definition itv_partitionL s c := rcons [seq x <- s | x < c] c.

Lemma itv_partitionLP a b c s : a < c -> c < b -> itv_partition a b s ->
  itv_partition a c (itv_partitionL s c).
Proof.
move=> ac bc [] al /eqP htb; split.
  rewrite /itv_partitionL rcons_path/=; apply/andP; split.
    by apply: path_filter => //; exact: lt_trans.
  exact: (last_filterP [pred x | x < c]).
by rewrite /itv_partitionL last_rcons.
Qed.

(** given a partition of [a, b] and c, returns a partition of [c, b] *)
Definition itv_partitionR s c := [seq x <- s | c < x].

Lemma itv_partitionRP a b c s : a < c -> c < b -> itv_partition a b s ->
  itv_partition c b (itv_partitionR s c).
Proof.
move=> ac cb [] sa /eqP alb; rewrite /itv_partition; split.
  move: sa; rewrite lt_path_sortedE => /andP[allas ss].
  rewrite lt_path_sortedE filter_all/=.
  by apply: sorted_filter => //; exact: lt_trans.
exact/eqP/(path_lt_last_filter ac).
Qed.

Lemma in_itv_partition c s : sorted <%R s -> c \in s ->
  s = itv_partitionL s c ++ itv_partitionR s c.
Proof.
elim: s c => // h t ih c /= ht.
rewrite inE => /predU1P[->{c}/=|ct].
  rewrite ltxx /itv_partitionL /= ltxx /itv_partitionR/= path_lt_filter0//=.
  by rewrite path_lt_filterT.
rewrite /itv_partitionL/=; case: ifPn => [hc|].
  by rewrite ltNge (ltW hc)/= /= [in LHS](ih _ _ ct)//; exact: path_sorted ht.
rewrite -leNgt le_eqVlt => /predU1P[ch|ch].
  by rewrite ch ltxx path_lt_filter0//= /itv_partitionR path_lt_filterT.
move: ht; rewrite lt_path_sortedE => /andP[/allP/(_ _ ct)].
by move=> /lt_trans-/(_ _ ch); rewrite ltxx.
Qed.

Lemma notin_itv_partition c s : sorted <%R s -> c \notin s ->
  s = [seq x <- s | x < c] ++ itv_partitionR s c.
Proof.
elim: s c => // h t ih c /= ht.
rewrite inE negb_or => /andP[]; rewrite neq_lt => /orP[ch|ch] ct.
  rewrite ch ltNge (ltW ch)/= path_lt_filter0/= /itv_partitionR; last first.
    exact: path_lt_head ht.
  by rewrite path_lt_filterT//; exact: path_lt_head ht.
by rewrite ch/= ltNge (ltW ch)/= -ih//; exact: path_sorted ht.
Qed.

Lemma itv_partition_rev a b s : itv_partition a b s ->
  itv_partition (- b) (- a) (rev (belast (- a) (map -%R s))).
Proof.
move=> [sa /eqP alb]; split.
  rewrite (_ : - b = last (- a) (map -%R s)); last by rewrite last_map alb.
  rewrite rev_path// path_map.
  by apply: sub_path sa => x y xy/=; rewrite ltrNr opprK.
case: s sa alb => [_ <-//|h t] /= /andP[ah ht] <-{b}.
by rewrite rev_cons last_rcons.
Qed.

End interval_partition.

Section variation.
Context {R : realType}.
Implicit Types (a b : R) (f g : R -> R).

Definition variation a b f s := let F := f \o nth b (a :: s) in
  \sum_(0 <= n < size s) `|F n.+1 - F n|%R.

Lemma variation_zip a b f s : itv_partition a b s ->
  variation a b f s = \sum_(x <- zip s (a :: s)) `|f x.1 - f x.2|.
Proof.
elim: s a b => // [a b|h t ih a b].
  by rewrite /itv_partition /= => -[_ /eqP <-]; rewrite /variation/= !big_nil.
rewrite /itv_partition /variation => -[]/= /andP[ah ht] /eqP htb.
rewrite big_nat_recl//= big_cons/=; congr +%R.
have /ih : itv_partition h b t by split => //; exact/eqP.
by rewrite /variation => ->; rewrite !big_seq; apply/eq_bigr => r rt.
Qed.

(* NB: not used yet but should allow for "term-by-term" comparisons *)
Lemma variation_prev a b f s : itv_partition a b s ->
  variation a b f s = \sum_(x <- s) `|f x - f (prev (locked (a :: s)) x)|.
Proof.
move=> [] sa /eqP asb; rewrite /variation [in LHS]/= (big_nth b) !big_nat.
apply: eq_bigr => i /andP[_ si]; congr (`| _ - f _ |).
rewrite -lock.
rewrite prev_nth inE gt_eqF; last first.
  rewrite -[a]/(nth b (a :: s) 0) -[ltRHS]/(nth b (a :: s) i.+1).
  exact: lt_sorted_ltn_nth.
rewrite orFb mem_nth// index_uniq//.
  by apply: set_nth_default => /=; rewrite ltnS ltnW.
by apply: (sorted_uniq lt_trans) => //; apply: path_sorted sa.
Qed.

Lemma variation_next a b f s : itv_partition a b s ->
  variation a b f s =
  \sum_(x <- belast a s) `|f (next (locked (a :: s)) x) - f x|.
Proof.
move=> [] sa /eqP asb; rewrite /variation [in LHS]/= (big_nth b) !big_nat.
rewrite size_belast; apply: eq_bigr => i /andP[_ si].
congr (`| f _ - f _ |); last first.
  by rewrite lastI -cats1 nth_cat size_belast// si.
rewrite -lock next_nth.
rewrite {1}lastI mem_rcons inE mem_nth ?size_belast// orbT.
rewrite lastI -cats1 index_cat mem_nth ?size_belast//.
rewrite index_uniq ?size_belast//.
  exact: set_nth_default.
have /lt_sorted_uniq : sorted <%R (a :: s) by [].
by rewrite lastI rcons_uniq => /andP[].
Qed.

Lemma variation_nil a b f : variation a b f [::] = 0.
Proof. by rewrite /variation/= big_nil. Qed.

Lemma variation_ge0 a b f s : 0 <= variation a b f s.
Proof. exact/sumr_ge0. Qed.

Lemma variationN a b f s : variation a b (\- f) s = variation a b f s.
Proof.
by rewrite /variation; apply: eq_bigr => k _ /=; rewrite -opprD normrN.
Qed.

Lemma variation_le a b f g s :
  variation a b (f \+ g)%R s <= variation a b f s + variation a b g s.
Proof.
rewrite [in leRHS]/variation -big_split/=.
apply: ler_sum => k _; apply: le_trans; last exact: ler_normD.
by rewrite /= addrACA addrA opprD addrA.
Qed.

Lemma nondecreasing_variation a b f s : {in `[a, b] &, nondecreasing_fun f} ->
  itv_partition a b s -> variation a b f s = f b - f a.
Proof.
move=> ndf abs; rewrite /variation; set F : nat -> R := f \o nth _ (a :: s).
transitivity (\sum_(0 <= n < size s) (F n.+1 - F n)).
  rewrite !big_nat; apply: eq_bigr => k; rewrite leq0n/= => ks.
  by rewrite ger0_norm// subr_ge0; exact: nondecreasing_fun_itv_partition.
by rewrite telescope_sumr// /F/= (itv_partition_nth_size _ abs).
Qed.

Lemma nonincreasing_variation a b f s : {in `[a, b] &, nonincreasing_fun f} ->
  itv_partition a b s -> variation a b f s = f a - f b.
Proof.
move=> /nonincreasing_funN ndNf abs; have := nondecreasing_variation ndNf abs.
by rewrite opprK addrC => <-; rewrite variationN.
Qed.

Lemma variationD a b c f s t : a <= c -> c <= b ->
  itv_partition a c s -> itv_partition c b t ->
  variation a c f s + variation c b f t = variation a b f (s ++ t).
Proof.
rewrite le_eqVlt => /predU1P[<-{c} cb|ac].
  by move=> /itv_partitionxx ->; rewrite variation_nil add0r.
rewrite le_eqVlt => /predU1P[<-{b}|cb].
  by move=> ? /itv_partitionxx ->; rewrite variation_nil addr0 cats0.
move=> acs cbt; rewrite /variation /= [in RHS]/index_iota subn0 size_cat.
rewrite iotaD add0n big_cat/= -[in X in _ = X + _](subn0 (size s)); congr +%R.
  rewrite -/(index_iota 0 (size s)) 2!big_nat.
  apply: eq_bigr => k /[!leq0n] /= ks.
  rewrite nth_cat ks -cat_cons nth_cat /= ltnS (ltnW ks).
  by rewrite !(set_nth_default b c)//= ltnS ltnW.
rewrite -[in RHS](addnK (size s) (size t)).
rewrite -/(index_iota (size s) (size t + size s)).
rewrite -{1}[in RHS](add0n (size s)) big_addn addnK 2!big_nat; apply: eq_bigr.
move=> k /[!leq0n]/= kt.
rewrite nth_cat {1}(addnC k) -ltn_subRL subnn ltn0 addnK.
case: k kt => [t0 /=|k kt].
  rewrite add0n -cat_cons nth_cat/= ltnS leqnn -last_nth.
  by case: acs => _ /eqP ->.
rewrite addSnnS (addnC k) -cat_cons nth_cat/= -ltn_subRL subnn ltn0.
by rewrite -(addnC k) addnK.
Qed.

(* NB: this is the only lemma that uses variation_zip *)
Lemma variation_itv_partitionLR a b c f s : a < c -> c < b ->
  itv_partition a b s ->
  variation a b f s <= variation a b f (itv_partitionL s c ++ itv_partitionR s c).
Proof.
move=> ac bc abs; have [cl|cl] := boolP (c \in s).
  by rewrite -in_itv_partition//; case: abs => /path_sorted.
rewrite /itv_partitionL [in leLHS](notin_itv_partition _ cl)//; last first.
  by apply: path_sorted; case: abs => + _; exact.
rewrite -notin_itv_partition//; last first.
  by apply: path_sorted; case: abs => /= + _; exact.
rewrite !variation_zip//; last first.
  by apply: itv_partition_cat;
    [exact: (itv_partitionLP _ bc)|exact: (itv_partitionRP ac)].
rewrite [in leLHS](notin_itv_partition _ cl); last first.
  by apply: path_sorted; case: abs => + _; exact.
set L := [seq x <- s | x < c].
rewrite -cats1 -catA.
move: L => L.
set B := itv_partitionR s c.
move: B => B.
elim/last_ind : L => [|L0 L1 _].
  rewrite !cat0s /=; case: B => [|B0 B1].
    by rewrite big_nil big_cons/= big_nil addr0.
  rewrite !big_cons/= addrA lerD// [leRHS]addrC.
  by rewrite (le_trans _ (ler_normD _ _))// addrA subrK.
rewrite -cats1.
rewrite (_ : a :: _ ++ B = (a :: L0) ++ [:: L1] ++ B)//; last first.
  by rewrite -!catA -cat_cons.
rewrite zip_cat; last by rewrite cats1 size_rcons.
rewrite (_ : a :: _ ++ _ ++ B = (a :: L0) ++ [:: L1] ++ [:: c] ++ B); last first.
  by rewrite -!catA -cat_cons.
rewrite zip_cat; last by rewrite cats1 size_rcons.
rewrite !big_cat lerD//.
case: B => [|B0 B1].
  by rewrite /= big_nil big_cons big_nil addr0.
rewrite -cat1s zip_cat// catA.
rewrite (_ : [:: L1] ++ _ ++ B1 = ([:: L1] ++ [:: c]) ++ [:: B0] ++ B1); last first.
  by rewrite catA.
rewrite zip_cat// !big_cat lerD//= !big_cons !big_nil !addr0/= [leRHS]addrC.
  by rewrite (le_trans _ (ler_normD _ _))// addrA subrK.
Qed.

Lemma le_variation a b f s x : variation a b f s <= variation a b f (x :: s).
Proof.
case: s => [|h t].
  by rewrite variation_nil /variation/= big_nat_recl//= big_nil addr0.
rewrite /variation/= !big_nat_recl//= addrA lerD2r.
by rewrite (le_trans _ (ler_normD _ _))// (addrC (f x - _)) addrA subrK.
Qed.

Lemma variation_opp_rev a b f s : itv_partition a b s ->
  variation a b f s =
  variation (- b) (- a) (f \o -%R) (rev (belast (- a) (map -%R s))).
Proof.
move=> abl; rewrite belast_map /variation /= [LHS]big_nat_rev/= add0n.
rewrite size_rev size_map size_belast 2!big_nat.
apply: eq_bigr => k; rewrite leq0n /= => ks.
rewrite nth_rev ?size_map ?size_belast// [in RHS]distrC.
rewrite (nth_map a); last first.
  by rewrite size_belast ltn_subLR// addSn ltnS leq_addl.
rewrite opprK -rev_rcons nth_rev ?size_rcons ?size_map ?size_belast 1?ltnW//.
rewrite subSn// -map_rcons (nth_map b) ?size_rcons ?size_belast; last first.
  by rewrite ltnS ltn_subLR// addSn ltnS leq_addl.
rewrite opprK nth_rcons size_belast -subSn// subSS.
rewrite (ltn_subLR _ (ltnW ks)) if_same.
case: k => [|k] in ks *.
  rewrite add0n ltnn subn1 (_ : nth b s _ = b); last first.
    case: abl ks => _.
    elim/last_ind : s => // h t _; rewrite last_rcons => /eqP -> _.
    by rewrite nth_rcons size_rcons ltnn eqxx.
  rewrite (_ : nth b (a :: s) _ = nth a (belast a s) (size s).-1)//.
  case: abl ks => _.
  elim/last_ind : s => // h t _; rewrite last_rcons => /eqP -> _.
  rewrite belast_rcons size_rcons/= -rcons_cons nth_rcons/= ltnS leqnn.
  exact: set_nth_default.
rewrite addSn ltnS leq_addl//; congr (`| f _ - f _ |).
  elim/last_ind : s ks {abl} => // h t _; rewrite size_rcons ltnS => kh.
  rewrite belast_rcons nth_rcons subSS ltn_subLR//.
  by rewrite addSn ltnS leq_addl// subSn.
elim/last_ind : s ks {abl} => // h t _; rewrite size_rcons ltnS => kh.
rewrite belast_rcons subSS -rcons_cons nth_rcons /= ltn_subLR//.
rewrite addnS ltnS leq_addl; apply: set_nth_default => //.
by rewrite /= ltnS leq_subLR leq_addl.
Qed.

Lemma variation_rev_opp a b f s : itv_partition (- b) (- a) s ->
  variation a b f (rev (belast b (map -%R s))) =
  variation (- b) (- a) (f \o -%R) s.
Proof.
move=> abs; rewrite [in RHS]variation_opp_rev ?opprK//.
suff: (f \o -%R) \o -%R = f by move=> ->.
by apply/funext=> ? /=; rewrite opprK.
Qed.

Lemma variation_subseq a b f (s t : list R) :
  itv_partition a b s -> itv_partition a b t ->
  subseq s t ->
  variation a b f s <= variation a b f t.
Proof.
elim: t s a => [? ? ? /= _ /eqP ->//|a s IH [|x t] w].
  by rewrite variation_nil // variation_ge0.
move=> /[dup] /itv_partition_cons itvxb /[dup] /itv_partition_le wb itvxt.
move=> /[dup] /itv_partition_cons itvas itvws /=.
have ab : a <= b by exact: (itv_partition_le itvas).
have wa : w < a by case: itvws => /= /andP[].
have waW : w <= a := ltW wa.
case: ifPn => [|] nXA.
  move/eqP : nXA itvxt itvxb => -> itvat itvt /= ta.
  rewrite -[_ :: t]cat1s -[_ :: s]cat1s.
  rewrite -?(@variationD _ _ a)//; [|exact: itv_partition1..].
  by rewrite lerD// IH.
move=> xts; rewrite -[_ :: s]cat1s -(@variationD _ _ a) => //; last first.
  exact: itv_partition1.
have [y [s' s'E]] : exists y s', s = y :: s'.
  by case: {itvas itvws IH} s xts => // y s' ?; exists y, s'.
apply: (@le_trans _ _ (variation w b f s)).
  rewrite IH//.
  case: itvws => /= /andP[_]; rewrite s'E /= => /andP[ay ys' lyb].
  by split => //; rewrite (path_lt_head wa)//= ys' andbT.
by rewrite variationD //; [exact: le_variation | exact: itv_partition1].
Qed.

End variation.

Section bounded_variation.
Context {R : realType}.
Implicit Type (a b : R) (f : R -> R).

Definition variations a b f := [set variation a b f l | l in itv_partition a b].

Lemma variations_variation a b f s : itv_partition a b s ->
  variations a b f (variation a b f s).
Proof. by move=> abs; exists s. Qed.

Lemma variations_neq0 a b f : a < b -> variations a b f !=set0.
Proof.
move=> ab; exists (variation a b f [:: b]); exists [:: b] => //.
exact: itv_partition1.
Qed.

Lemma variationsN a b f : variations a b (\- f) = variations a b f.
Proof.
apply/seteqP; split => [_ [s abs] <-|r [s abs]].
  by rewrite variationN; exact: variations_variation.
by rewrite -variationN => <-; exact: variations_variation.
Qed.

Lemma variationsxx a f : variations a a f = [set 0].
Proof.
apply/seteqP; split => [x [_ /itv_partitionxx ->]|x ->].
  by rewrite /variation big_nil => <-.
by exists [::] => //=; rewrite /variation /= big_nil.
Qed.

Definition bounded_variation a b f := has_ubound (variations a b f).

Notation BV := bounded_variation.

Lemma bounded_variationxx a f : BV a a f.
Proof. by exists 0 => r; rewrite variationsxx => ->. Qed.

Lemma bounded_variationD a b f g : a < b ->
  BV a b f -> BV a b g -> BV a b (f \+ g).
Proof.
move=> ab [r abfr] [s abgs]; exists (r + s) => _ [l abl] <-.
apply: le_trans; first exact: variation_le.
rewrite lerD//.
- by apply: abfr; exact: variations_variation.
- by apply: abgs; exact: variations_variation.
Qed.

Lemma bounded_variationN a b f : BV a b f -> BV a b (\- f).
Proof. by rewrite /bounded_variation variationsN. Qed.

Lemma bounded_variationl a c b f : a <= c -> c <= b -> BV a b f -> BV a c f.
Proof.
rewrite le_eqVlt => /predU1P[<-{c} ? ?|ac]; first exact: bounded_variationxx.
rewrite le_eqVlt => /predU1P[<-{b}//|cb].
move=> [x Hx]; exists x => _ [s acs] <-.
rewrite (@le_trans _ _ (variation a b f (rcons s b)))//; last first.
  apply/Hx/variations_variation; case: acs => sa /eqP asc.
  by rewrite /itv_partition rcons_path last_rcons sa/= asc.
rewrite {2}/variation size_rcons -[leLHS]addr0 big_nat_recr//= lerD//.
rewrite /variation !big_nat ler_sum// => k; rewrite leq0n /= => ks.
rewrite nth_rcons// ks -cats1 -cat_cons nth_cat /= ltnS (ltnW ks).
by rewrite ![in leRHS](set_nth_default c)//= ltnS ltnW.
Qed.

Lemma bounded_variationr a c b f : a <= c -> c <= b -> BV a b f -> BV c b f.
Proof.
rewrite le_eqVlt => /predU1P[<-{c}//|ac].
rewrite le_eqVlt => /predU1P[<-{b} ?|cb]; first exact: bounded_variationxx.
move=> [x Hx]; exists x => _ [s cbs] <-.
rewrite (@le_trans _ _ (variation a b f (c :: s)))//; last first.
  apply/Hx/variations_variation; case: cbs => cs csb.
  by rewrite /itv_partition/= ac/= cs.
by rewrite {2}/variation/= -[leLHS]add0r big_nat_recl//= lerD.
Qed.

Lemma variations_opp a b f :
  variations (- b) (- a) (f \o -%R) = variations a b f.
Proof.
rewrite eqEsubset; split=> [_ [s bas <-]| _ [s abs <-]].
  eexists; last exact: variation_rev_opp.
  by move/itv_partition_rev : bas; rewrite !opprK.
eexists; last by exact/esym/variation_opp_rev.
exact: itv_partition_rev abs.
Qed.

Lemma nondecreasing_bounded_variation a b f :
  {in `[a, b] &, {homo f : x y / x <= y}} -> BV a b f.
Proof.
move=> incf; exists (f b - f a) => ? [l pabl <-]; rewrite le_eqVlt.
by rewrite nondecreasing_variation// eqxx.
Qed.

End bounded_variation.

Section total_variation.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).

Definition total_variation a b f :=
  ereal_sup [set x%:E | x in variations a b f].

Notation BV := bounded_variation.
Notation TV := total_variation.

Lemma total_variationxx a f : TV a a f = 0%E.
Proof. by rewrite /total_variation variationsxx image_set1 ereal_sup1. Qed.

Lemma total_variation_ge a b f : a <= b -> (`|f b - f a|%:E <= TV a b f)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite total_variationxx subrr normr0.
apply: ereal_sup_ubound => /=; exists (variation a b f [:: b]).
  exact/variations_variation/itv_partition1.
by rewrite /variation/= big_nat_recr//= big_nil add0r.
Qed.

Lemma total_variation_ge0 a b f : a <= b -> (0 <= TV a b f)%E.
Proof. by move=> ab; rewrite (le_trans _ (total_variation_ge _ ab)). Qed.

Lemma bounded_variationP a b f : a <= b -> BV a b f <-> TV a b f \is a fin_num.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite total_variationxx; split => // ?; exact: bounded_variationxx.
rewrite ge0_fin_numE; last exact/total_variation_ge0/ltW.
split=> [abf|].
  by rewrite /total_variation ereal_sup_EFin ?ltry//; exact: variations_neq0.
rewrite /total_variation /bounded_variation ltey => /eqP; apply: contra_notP.
by move/hasNub_ereal_sup; apply; exact: variations_neq0.
Qed.

Lemma nondecreasing_total_variation a b f : a <= b ->
  {in `[a, b] &, nondecreasing_fun f} -> TV a b f = (f b - f a)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b} ?|ab ndf].
  by rewrite total_variationxx subrr.
rewrite /total_variation [X in ereal_sup X](_ : _ = [set (f b - f a)%:E]).
  by rewrite ereal_sup1.
apply/seteqP; split => [x/= [s [t abt <-{s} <-{x}]]|x/= ->{x}].
  by rewrite nondecreasing_variation.
exists (variation a b f [:: b]) => //.
  exact/variations_variation/itv_partition1.
by rewrite nondecreasing_variation//; exact: itv_partition1.
Qed.

Lemma total_variationN a b f : TV a b (\- f) = TV a b f.
Proof. by rewrite /TV; rewrite variationsN. Qed.

Lemma total_variation_le a b f g : a <= b ->
  (TV a b (f \+ g)%R <= TV a b f + TV a b g)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite !total_variationxx adde0.
have [abf|abf] := pselect (BV a b f); last first.
  rewrite {2}/total_variation hasNub_ereal_sup//; last first.
    exact: variations_neq0.
  rewrite addye ?leey// -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
have [abg|abg] := pselect (BV a b g); last first.
  rewrite {3}/total_variation hasNub_ereal_sup//; last first.
    exact: variations_neq0.
  rewrite addey ?leey// -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
move: abf abg => [r abfr] [s abgs].
have BVabfg : BV a b (f \+ g).
  by apply: bounded_variationD => //; [exists r|exists s].
apply: ub_ereal_sup => y /= [r' [s' abs <-{r'} <-{y}]].
apply: (@le_trans _ _ (variation a b f s' + variation a b g s')%:E).
  exact: variation_le.
by rewrite EFinD leeD// ereal_sup_le//;
  (eexists; last exact: lexx); (eexists; last reflexivity);
  exact: variations_variation.
Qed.

Let total_variationD1 a b c f : a <= c -> c <= b ->
  (TV a b f >= TV a c f + TV c b f)%E.
Proof.
rewrite le_eqVlt=> /predU1P[<-{c}|ac]; first by rewrite total_variationxx add0e.
rewrite le_eqVlt=> /predU1P[<-{b}|cb]; first by rewrite total_variationxx adde0.
have [abf|abf] := pselect (BV a b f); last first.
  rewrite {3}/total_variation hasNub_ereal_sup ?leey//.
  by apply: variations_neq0 => //; rewrite (lt_trans ac).
have H s t : itv_partition a c s -> itv_partition c b t ->
    (TV a b f >= (variation a c f s)%:E + (variation c b f t)%:E)%E.
  move=> acs cbt; rewrite -EFinD; apply: ereal_sup_le.
  exists (variation a b f (s ++ t))%:E.
    eexists; last reflexivity.
    by exists (s ++ t) => //; exact: itv_partition_cat acs cbt.
  by rewrite variationD// ltW.
rewrite [leRHS]ereal_sup_EFin//; last first.
  by apply: variations_neq0; rewrite (lt_trans ac).
have acf : BV a c f := bounded_variationl (ltW ac) (ltW cb) abf.
have cbf : BV c b f := bounded_variationr (ltW ac) (ltW cb) abf.
rewrite {1 2}/total_variation ereal_sup_EFin//; last exact: variations_neq0.
rewrite ereal_sup_EFin//; last exact: variations_neq0.
rewrite -EFinD -sup_sumE; last 2 first.
  by split => //; exact: variations_neq0.
  by split => //; exact: variations_neq0.
apply: le_sup.
- move=> r/= [s [l' acl' <-{s}]] [t [l cbl] <-{t} <-{r}].
  exists (variation a b f (l' ++ l)); split; last by rewrite variationD// ltW.
  exact/variations_variation/(itv_partition_cat acl' cbl).
- have [r acfr] := variations_neq0 f ac.
  have [s cbfs] := variations_neq0 f cb.
  by exists (r + s); exists r => //; exists s.
- by split => //; apply: variations_neq0; rewrite (lt_trans ac).
Qed.

Let total_variationD2 a b c f : a <= c -> c <= b ->
  (TV a b f <= TV a c f + TV c b f)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{c}|ac]; first by rewrite total_variationxx add0e.
rewrite le_eqVlt => /predU1P[<-{b}|cb]; first by rewrite total_variationxx adde0.
case : (pselect (bounded_variation a c f)); first last.
  move=> nbdac; have /eqP -> : TV a c f == +oo%E.
    have: (-oo < TV a c f)%E by apply: (lt_le_trans _ (total_variation_ge0 f (ltW ac))).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ (ltW ac)).
  by rewrite addye ?leey // -ltNye (@lt_le_trans _ _ 0)%E // ?total_variation_ge0 // ltW.
case : (pselect (bounded_variation c b f)); first last.
  move=> nbdac; have /eqP -> : TV c b f == +oo%E.
    have: (-oo < TV c b f)%E.
      exact: (lt_le_trans _ (total_variation_ge0 f (ltW cb))).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ (ltW cb)).
  rewrite addey ?leey // -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
move=> bdAB bdAC.
rewrite /total_variation [x in (x + _)%E]ereal_sup_EFin //; last first.
  exact: variations_neq0.
rewrite [x in (_ + x)%E]ereal_sup_EFin //; last exact: variations_neq0.
rewrite -EFinD -sup_sumE /has_sup; [|(by split => //; exact: variations_neq0)..].
apply: ub_ereal_sup => ? [? [l pacl <- <-]]; rewrite lee_fin.
apply: (le_trans (variation_itv_partitionLR _ ac _ _)) => //.
apply: sup_ubound => /=.
  case: bdAB => M ubdM; case: bdAC => N ubdN; exists (N + M).
  move=> q [?] [i pabi <-] [? [j pbcj <-]] <-.
  by apply: lerD; [apply: ubdN;exists i|apply:ubdM;exists j].
exists (variation a c f (itv_partitionL l c)).
  by apply: variations_variation; exact: itv_partitionLP pacl.
exists (variation c b f (itv_partitionR l c)).
  by apply: variations_variation; exact: itv_partitionRP pacl.
by rewrite variationD// ?ltW//;
  [exact: itv_partitionLP pacl|exact: itv_partitionRP pacl].
Qed.

Lemma total_variationD a b c f : a <= c -> c <= b ->
  (TV a b f = TV a c f + TV c b f)%E.
Proof.
by move=> ac cb; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: total_variationD2|exact: total_variationD1].
Qed.

End total_variation.

Section variation_continuity.
Context {R : realType}.
Implicit Type f : R -> R.

Notation BV := bounded_variation.
Notation TV := total_variation.

Definition neg_tv a f (x : R) : \bar R := ((TV a x f - (f x)%:E) * 2^-1%:E)%E.

Definition pos_tv a f (x : R) : \bar R := neg_tv a (\- f) x.

Lemma total_variation_nondecreasing a b f :
  {in `[a, b] &, nondecreasing_fun (TV a ^~ f)}.
Proof.
move=> x y; rewrite !in_itv/= => /andP[ax xb] /andP[ay yb] xy.
by rewrite (total_variationD f ax xy)// leeDl// total_variation_ge0.
Qed.

Lemma total_variation_bounded_variation a b (f : R -> R) : a <= b ->
  BV a b f ->
  BV a b (fine \o TV a ^~ f).
Proof.
move=> ab BVf; apply/bounded_variationP => //.
rewrite ge0_fin_numE; last exact: total_variation_ge0.
rewrite nondecreasing_total_variation/= ?ltry//.
move=> x y; rewrite !in_itv!/= => /andP[ax xb] /andP[ay yb] xy.
apply: fine_le.
- exact/(bounded_variationP _ ax)/(bounded_variationl ax xb).
- exact/(bounded_variationP _ ay)/(bounded_variationl ay yb).
- by apply: (@total_variation_nondecreasing _ b); rewrite ?in_itv //= ?ax ?ay.
Qed.

Lemma neg_tv_nondecreasing a b f :
  {in `[a, b] &, nondecreasing_fun (neg_tv a f)}.
Proof.
move=> x y xab yab xy; have ax : a <= x.
  by move: xab; rewrite in_itv //= => /andP [].
rewrite /neg_tv lee_pmul2r // leeBrDl // addeCA -EFinB.
rewrite [TV a y _](total_variationD _ ax xy) //.
apply: leeD => //; apply: le_trans; last exact: total_variation_ge.
by rewrite lee_fin ler_norm.
Qed.

Lemma bounded_variation_pos_neg_tvE a b f : BV a b f ->
  {in `[a, b], f =1 (fine \o pos_tv a f) \- (fine \o neg_tv a f)}.
Proof.
move=> bdabf x; rewrite in_itv /= => /andP [ax xb].
have ffin: TV a x f \is a fin_num.
   apply/bounded_variationP => //.
   exact: (bounded_variationl _ xb).
have Nffin : TV a x (\- f) \is a fin_num.
  apply/bounded_variationP => //; apply/bounded_variationN.
  exact: (bounded_variationl ax xb).
rewrite /pos_tv /neg_tv /= total_variationN -fineB -?muleBl // ?fineM //.
- rewrite addeAC oppeD //= ?fin_num_adde_defl //.
  by rewrite addeA subee // add0e -EFinD //= opprK mulrDl -splitr.
- by rewrite fin_numB ?fin_numD ?ffin; apply/andP; split.
- by apply: fin_num_adde_defl; rewrite fin_numN fin_numD; apply/andP; split.
- by rewrite fin_numM // fin_numD; apply/andP; split.
- by rewrite fin_numM // fin_numD; apply/andP; split.
Qed.

Lemma fine_neg_tv_nondecreasing a b f : BV a b f ->
  {in `[a, b] &, nondecreasing_fun (fine \o neg_tv a f)}.
Proof.
move=> bdv p q pab qab pq /=.
move: (pab) (qab); rewrite ?in_itv /= => /andP[ap pb] /andP[aq qb].
apply: fine_le; rewrite /neg_tv ?fin_numM // ?fin_numB /=.
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variationl _ pb).
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variationl _ qb).
exact: (neg_tv_nondecreasing _ pab).
Qed.

Lemma neg_tv_bounded_variation a b f : BV a b f -> BV a b (fine \o neg_tv a f).
Proof.
move=> ?; apply: nondecreasing_bounded_variation.
exact: fine_neg_tv_nondecreasing.
Qed.

Lemma total_variation_right_continuous a b x f : a <= x -> x < b ->
  f @ x^'+ --> f x ->
  BV a b f ->
  fine \o TV a ^~ f @ x^'+ --> fine (TV a x f).
Proof.
move=> ax xb ctsf bvf; have ? : a <= b by apply:ltW; apply: (le_lt_trans ax).
apply/cvgrPdist_lt=> _/posnumP[eps].
have ? : Filter (nbhs x^'+) by exact: at_right_proper_filter.
have xbl := ltW xb.
have xbfin : TV x b f \is a fin_num.
  by apply/bounded_variationP => //; exact: (bounded_variationr _ _ bvf).
have [//|?] := @ub_ereal_sup_adherent R _ (eps%:num / 2) _ xbfin.
case=> ? [l + <- <-]; rewrite -/(total_variation x b f).
move: l => [|i j].
  by move=> /itv_partition_nil /eqP; rewrite lt_eqF.
move=> [/= /andP[xi ij /eqP ijb]] tv_eps.
apply: (filter_app _ _ (nbhs_right_ge _)).
apply: filter_app (nbhs_right_lt xi).
have e20 : 0 < eps%:num / 2 by [].
move/cvgrPdist_lt/(_ (eps%:num/2) e20) : ctsf; apply: filter_app.
near=> t => fxt ti xt; have ta : a <= t by exact: (le_trans ax).
have tb : t <= b by rewrite (le_trans (ltW ti))// -ijb path_lt_le_last.
rewrite -fineB; last 2 first.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
rewrite (total_variationD _ ax xt).
have tbfin : TV t b f \is a fin_num.
  by apply/bounded_variationP => //; exact: (@bounded_variationr _ a).
have xtfin : TV x t f \is a fin_num.
  apply/bounded_variationP => //; apply: (@bounded_variationl _ _ _ b) => //.
  exact: (@bounded_variationr _ a).
rewrite oppeD ?fin_num_adde_defl// addeA subee //; first last.
  by apply/bounded_variationP => //; exact: (@bounded_variationl _ _ _ b).
rewrite sub0e fineN normrN ger0_norm; last first.
  by rewrite fine_ge0// total_variation_ge0.
move: (tv_eps); rewrite (total_variationD f _ tb) //.
move: xt; rewrite le_eqVlt => /predU1P[->|xt].
  by rewrite total_variationxx/=.
have : variation x b f (i :: j) <= variation x t f (t :: nil) +
                                   variation t b f (i :: j).
  rewrite variationD//; last 2 first.
    exact: itv_partition1.
    by rewrite /itv_partition/= ti ij ijb.
  exact: le_variation.
rewrite -lee_fin => /lt_le_trans /[apply].
rewrite {1}variation_prev; last exact: itv_partition1.
rewrite /= -addeA -lteBrDr; last by rewrite fin_numD; apply/andP.
rewrite EFinD -lte_fin ?fineK // oppeD //= ?fin_num_adde_defl // opprK addeA.
move/lt_trans; apply.
rewrite [in ltRHS](splitr (eps%:num)) EFinD lteD2rE// -addeA.
apply: (@le_lt_trans _ _ (variation x t f (t :: nil))%:E).
  rewrite [in leRHS]variation_prev; last exact: itv_partition1.
  rewrite geeDl// sube_le0; apply: ereal_sup_ubound => /=.
  exists (variation t b f (i :: j)) => //; apply: variations_variation.
  by rewrite /itv_partition/= ijb ij ti.
by rewrite /variation/= big_nat_recr//= big_nil add0r distrC lte_fin.
Unshelve. all: by end_near. Qed.

Lemma neg_tv_right_continuous a x b f : a <= x -> x < b ->
  BV a b f ->
  f @ x^'+ --> f x ->
  fine \o neg_tv a f @ x^'+ --> fine (neg_tv a f x).
Proof.
move=> ax ? bvf fcts; have xb : x <= b by exact: ltW.
have xbfin : TV a x f \is a fin_num.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
apply: fine_cvg; rewrite /neg_tv fineM // ?fin_numB ?xbfin //= EFinM.
under eq_fun => i do rewrite EFinN.
apply: (@cvg_trans _ (((TV a n f - (f n)%:E) * 2^-1%:E)%E @[n --> x^'+])).
  exact: cvg_id.
apply: cvgeMr; first by [].
rewrite fineD; [|by []..].
rewrite EFinB; apply: cvgeB; [by []| |].
  apply/ fine_cvgP; split; first exists (b - x).
  - by rewrite /= subr_gt0.
  - move=> t /= xtbx xt; have ? : a <= t.
      by apply: ltW; apply: (le_lt_trans ax).
    apply/bounded_variationP => //.
    apply: bounded_variationl bvf => //.
    move: xtbx; rewrite distrC ger0_norm ?subr_ge0; last by exact: ltW.
    by rewrite ltrBrDr -addrA [-_ + _]addrC subrr addr0 => /ltW.
  by apply: total_variation_right_continuous => //; last exact: bvf.
apply: cvg_comp; first exact: fcts.
apply/ fine_cvgP; split; first by near=> t => //.
by have -> : fine \o EFin = id by move=> ?; rewrite funeqE => ? /=.
Unshelve. all: by end_near. Qed.

Lemma total_variation_opp a b f : TV a b f = TV (- b) (- a) (f \o -%R).
Proof. by rewrite /total_variation variations_opp. Qed.

Lemma total_variation_left_continuous a b x f : a < x -> x <= b ->
  f @ x^'- --> f x ->
  BV a b f ->
  fine \o TV a ^~ f @ x^'- --> fine (TV a x f).
Proof.
move=> ax xb fNcts bvf.
apply/cvg_at_leftNP; rewrite total_variation_opp.
have bvNf : BV (-b) (-a) (f \o -%R).
  by case: bvf => M; rewrite -variations_opp => ?; exists M.
have bx : - b <= - x by rewrite lerNl opprK.
have xa : - x < - a by rewrite ltrNl opprK.
have ? : - x <= - a by exact: ltW.
have ? : Filter (nbhs (-x)^'+) by exact: at_right_proper_filter.
have -> : fine (TV (-x) (-a) (f \o -%R)) =
    fine (TV (-b) (-a) (f \o -%R)) - fine (TV (-b) (-x) (f \o -%R)).
  apply/eqP; rewrite -subr_eq opprK addrC.
  rewrite -fineD; last 2 first.
    by apply/bounded_variationP => //; exact: bounded_variationl bvNf.
    by apply/bounded_variationP => //; exact: bounded_variationr bvNf.
  by rewrite -total_variationD.
have /near_eq_cvg/cvg_trans : {near (- x)^'+,
    (fun t => fine (TV (- b) (- a) (f \o -%R)) - fine (TV (- b) t (f \o -%R))) =1
    (fine \o (TV a)^~ f) \o -%R}.
  apply: filter_app (nbhs_right_lt xa).
  apply: (filter_app _ _ (nbhs_right_ge _)).
  near=> t => xt ta; have ? : -b <= t by exact: (le_trans bx).
  have ? : t <= -a by exact: ltW.
  apply/eqP; rewrite eq_sym -subr_eq opprK addrC.
  rewrite /= [TV a _ f]total_variation_opp opprK -fineD; last first.
    by apply/bounded_variationP => //; apply: bounded_variationr bvNf.
    by apply/bounded_variationP => //; apply: bounded_variationl bvNf.
  by rewrite -total_variationD.
apply.
apply: cvgB; first exact: cvg_cst.
apply: (total_variation_right_continuous _ _ _ bvNf).
- by rewrite lerNl opprK //.
- by rewrite ltrNl opprK //.
by apply/cvg_at_leftNP; rewrite /= opprK.
Unshelve. all: by end_near. Qed.

Lemma total_variation_continuous a b (f : R -> R) : a < b ->
  {within `[a,b], continuous f} ->
  BV a b f ->
  {within `[a,b], continuous (fine \o TV a ^~ f)}.
Proof.
move=> ab /(@continuous_within_itvP _ _ _ _ ab) [int l r] bdf.
apply/continuous_within_itvP => //; split.
- move=> x /[dup] xab; rewrite in_itv /= => /andP [ax xb].
  apply/left_right_continuousP; split.
    apply: (total_variation_left_continuous _ (ltW xb)) => //.
    by have /left_right_continuousP[] := int x xab.
  apply: (total_variation_right_continuous _ xb) => //; first exact: ltW.
  by have /left_right_continuousP[] := int x xab.
- exact: (total_variation_right_continuous _ ab).
- exact: (total_variation_left_continuous ab).
Qed.

End variation_continuity.

Definition discontinuity {R : realType} (f : R -> R) (r : R) :=
  [/\ cvg (f x @[x --> r^'-]),
      cvg (f x @[x --> r^'+]) &
      lim (f x @[x --> r^'-]) != lim (f x @[x --> r^'+]) ].

Section discontinuity_countable.
Context {R : realType}.
Variables (a b : R) (F : R -> R).
Hypothesis ndF : {in `[a, b] &, nondecreasing_fun F}.

Let Fr z := lim (F x @[x --> z^'+]).
Let Fl z := lim (F x @[x --> z^'-]).

Lemma nondecreasing_fun_sum_le (s : seq R) :
  itv_partition a b s ->
  \sum_(1 <= i < size s) (Fr (nth b (a :: s) i) - Fl (nth b (a :: s) i))
  <= F b - F a.
Proof.
move=> abs; have [s0|s0] := eqVneq s [::].
  by move: abs; rewrite s0/= big_nil => /itv_partition_nil ->; rewrite subrr.
have [s' ss'b] : exists s', s = rcons s' b.
  move: s abs s0; apply: last_ind => // s x ih [_ +] sx0.
  by move/eqP; rewrite last_rcons => <-; exists s.
pose x_ : R^nat := nth b (a :: s).
set t := map (fun n => (x_ n + x_ n.+1) / 2) (iota 0%N (size s)).
have [path_at sizets asts] : [/\ path <%R a t, size t = size s &
    (forall k, (k < size s)%N -> nth b (a :: s) k < nth b t k < nth b s k)].
  split.
  - apply/(pathP b) => -[|n].
    + rewrite [in X in X -> _]size_map [in X in X -> _]size_iota => {}s0/=.
      rewrite /t ss'b size_rcons/= midf_lt// -[a]/(nth b (a :: s) 0%N).
      by have /pathP := abs.1; exact.
    + rewrite [in X in X -> _]size_map [in X in X -> _]size_iota => ns/=.
      rewrite !(nth_map 0%N) ?size_iota//; last exact: (leq_trans _ ns).
      rewrite !nth_iota// ?add0n; last exact: (leq_trans _ ns).
      rewrite (@lt_trans _ _ (x_ n.+1))// midf_lt//.
        by have /pathP := abs.1; apply; exact: (leq_trans _ ns).
      by have /pathP := abs.1; exact.
  - by rewrite size_map size_iota.
  - move=> k ks; apply/andP; split.
      rewrite (nth_map 0%N) ?size_iota// nth_iota// add0n midf_lt//.
      by have /pathP := abs.1; exact.
    rewrite (nth_map 0%N _ (fun n => (x_ n + x_ n.+1) / 2)) ?size_iota//.
    rewrite nth_iota// add0n midf_lt//.
    by have /pathP := abs.1; exact.
pose y_ : R^nat := nth b (a :: t).
have ast k : (k < size s)%N -> nth b (a :: s) k < nth b t k.
  by move=> /asts /andP[].
have ts k : (k < size s)%N -> nth b t k < nth b s k by move=> /asts /andP[].
have yxl i : (0 < i)%N -> (i < size (a :: s))%N -> F (y_ i) <= Fl (x_ i).
  move=> i0 ias; apply: limr_ge.
  - have near_subab : \forall x \near (x_ i)^'-, `]x, (x_ i)[ `<=` `[a, b].
      near=> x; apply: subset_itvW; last exact: itv_partition_nth_le.
      near: x; apply: nbhs_left_ge.
      rewrite -[a]/(x_ 0%N).
      move: abs.1.
      by rewrite lt_path_pairwise => /pairwiseP; exact.
    apply: nondecreasing_at_left_is_cvgr.
      by near do apply: itv_sub_in2 ndF.
    near=> x.
    exists (F b) => _ /= [z zxxi <-].
    apply: ndF.
    + by move: z zxxi; near: x.
    + by rewrite in_itv/= lexx andbT (itv_partition_le abs).
    + move: zxxi; rewrite in_itv/= => /andP [_ /ltW] /le_trans; apply.
      exact: itv_partition_nth_le.
  - near=> x; apply: ndF.
    + rewrite in_itv/=; apply/andP; split.
        apply/ltW.
        have /allP := lt_path_min path_at; apply.
        by rewrite /y_ /= -(prednK i0)/= mem_nth// prednK// sizets.
      apply: (@le_trans _ _ (x_ i)); last exact: itv_partition_nth_le.
      by rewrite ltW// -(prednK i0)/= ts// prednK.
    + rewrite in_itv/=; apply/andP; split.
      * near: x; apply: nbhs_left_ge.
        have /allP := lt_path_min abs.1; apply.
        by rewrite /x_ -(prednK i0)/= mem_nth// prednK.
      * by rewrite (@le_trans _ _ (x_ i))//; exact: itv_partition_nth_le.
    + near: x; apply: nbhs_left_ge.
      by rewrite -(prednK i0)/= ts// prednK.
have xry i : (0 < i)%N -> (i < size s)%N -> Fr (x_ i) <= F (y_ i.+1).
  move=> i0 ilts; apply: limr_le.
  - apply: nondecreasing_at_right_is_cvgr.
    + near=> x; apply: (@itv_sub_in2 _ _ _ `[a, b]) ndF.
      apply: subset_itvW.
        by apply: itv_partition_nth_ge (abs); rewrite ltnS ltnW.
      near: x; apply: nbhs_right_le.
      apply: (@lt_le_trans _ _ (y_ i.+1)); first exact: ast.
      apply: (@le_trans _ _ (x_ i.+1)); first exact/ltW/ts.
      exact: itv_partition_nth_le.
    + near=> x.
      exists (F (x_ i)) => _/= [z + <-] => /[!in_itv]/= /andP[xiz zx].
      apply: ndF; last exact: ltW.
      * rewrite in_itv/=; apply/andP; split.
          by apply: itv_partition_nth_ge (abs); exact: (ltn_trans ilts).
        by apply: itv_partition_nth_le (abs); exact: (ltn_trans ilts).
      * rewrite in_itv/=; apply/andP; split.
          apply: le_trans (ltW xiz).
          apply: itv_partition_nth_ge (abs).
          exact: (ltn_trans ilts).
        apply: (le_trans (ltW zx)).
        apply: (@le_trans _ _ (x_ i.+1)) => //.
          near: x; apply: nbhs_right_le.
          by have /pathP := abs.1; exact.
        by apply: itv_partition_nth_le (abs); exact: ilts.
  - near=> x; apply: ndF.
    + rewrite in_itv/=; apply/andP; split.
        apply: (@le_trans _ _ (x_ i)) => //.
        by apply: itv_partition_nth_ge (abs); exact: (@leq_trans (size s)).
      near: x; apply: nbhs_right_le.
      apply: (@lt_le_trans _ _ (x_ i.+1)); last exact: itv_partition_nth_le.
      by have /pathP := abs.1; exact.
    + rewrite in_itv/=; apply/andP; split.
        rewrite ltW//.
        have /allP := lt_path_min path_at; apply.
        by apply: mem_nth; rewrite sizets.
      apply: (@le_trans _ _ (x_ i.+1)); first exact/ltW/ts.
      exact: itv_partition_nth_le.
  - by near: x; apply: nbhs_right_le; exact: ast.
apply: (@le_trans _ _ (\sum_(1 <= i < size s) (F (y_ i.+1) - F (y_ i)))).
  rewrite big_nat_cond [leRHS]big_nat_cond; apply: ler_sum => n.
  rewrite andbT => /andP[n0 ns].
  by apply: lerB; [exact: xry|rewrite yxl//= ltnS ltnW].
have sizes0 : (0 < size s)%N.
  by rewrite lt0n; apply: contra s0 => /eqP/size0nil ->.
rewrite telescope_sumr// lerB//.
- apply: ndF.
  + rewrite in_itv/=; apply/andP; split.
    * rewrite ltW//.
      have /allP := lt_path_min path_at; apply.
      rewrite -sizets /y_ -last_nth//.
      have [ht [r ->]] : exists x t', t = rcons x t'.
        move: t path_at sizets asts y_ ast ts yxl xry.
        apply: last_ind => //.
          by move=> _ /esym /= /size0nil; move/eqP : s0.
        by move=> ht tt _ _ _ _ _ _ _ _ _; exists ht, tt.
      by rewrite mem_rcons last_rcons mem_head.
    * rewrite /y_ /t.
      have /pathP := abs.1 => /(_ b).
      move: (sizes0) => /prednK.
      set m := (size s).-1 => <- H.
      rewrite -[leLHS]/(nth b [seq ((x_ i + x_ i.+1) / 2) | i <- iota 0 m.+1] m).
      rewrite (nth_map 0%N).
        rewrite nth_iota// add0n.
        apply: (@le_trans _ _ (x_ m.+1)).
          by rewrite midf_le// ltW// H.
        by apply: itv_partition_nth_le abs; rewrite prednK.
      by rewrite size_iota.
  + by rewrite in_itv/= lexx andbT; exact: itv_partition_le abs.
  + have /eqP := abs.2.
    rewrite (last_nth b) => <-.
    rewrite /y_ /t.
    move: (sizes0) => /prednK <-.
    set m := (size s).-1.
    rewrite -[leLHS]/(nth b [seq ((x_ i + x_ i.+1) / 2) | i <- iota 0 m.+1] m).
    rewrite (nth_map 0%N).
      rewrite nth_iota// add0n midf_le// ltW//.
      have /pathP := abs.1; apply.
      by rewrite (prednK sizes0).
    by rewrite size_iota.
have ay1 : a <= y_ 1%N by rewrite -[a]/(nth b (a :: s) 0%N) ltW// ast.
apply: ndF => //.
  by rewrite in_itv/= lexx andTb; exact: itv_partition_le abs.
rewrite in_itv/=; apply/andP; split => //.
apply: (@le_trans _ _ (x_ 1%N)); last exact: itv_partition_nth_le.
by rewrite /y_/x_ ltW//= ts.
Unshelve. all: end_near. Qed.

Lemma discontinuity_countable :
  countable [set x | x \in `]a, b[ /\ discontinuity F x].
Proof.
have [|ab] := leP b a.
  rewrite le_eqVlt => /predU1P[->|ba].
    set S := (X in countable X).
    suff Sa : S `<=` [set a] by exact/finite_set_countable/(sub_finite_set Sa).
    move=> x; rewrite /S/= in_itv/= => [[/andP[/ltW]]].
    by rewrite ltNge => ->.
  set S := (X in countable X).
  rewrite (_ : S = set0)// -subset0 => x.
  rewrite /S/= in_itv/= => -[/andP[]] /lt_trans /[apply].
  by rewrite ltNge ltW.
set A : set R := [set x | _].
pose elt_type := set_type A.
have FrBFl (x : elt_type) : exists m, m.+1%:R ^-1 < Fr (sval x) - Fl (sval x).
  have [Fc Fd cd] : discontinuity F (sval x) by case: x => /= r /[!inE] => -[].
  have FlFr : Fl (sval x) <= Fr (sval x).
    apply: (@nondecreasing_at_left_at_right _ _ a b) => //.
    by case: x {Fc Fd cd} => x/= /[1!inE] -[].
  have {}FlFr : Fl (sval x) < Fr (sval x) by rewrite lt_neqAle FlFr andbT.
  exists (`|floor (Fr (sval x) - Fl (sval x))^-1|)%N.
  rewrite invf_plt ?posrE ?subr_gt0// -natr1 natr_absz ger0_norm; last first.
    by rewrite floor_ge0 invr_ge0// subr_ge0 ltW.
  by rewrite intrD1 mathcomp_extra.lt_succ_floor// realE.
pose S m := [set x | x \in `]a, b[ /\ m.+1%:R ^-1 < Fr x - Fl x].
have jumpfafb m (s : seq R) : (forall i, (i < size s)%N -> nth b s i \in S m) ->
  path <%R a s ->
    \sum_(0 <= i < size s) (Fr (nth b s i) - Fl (nth b s i)) <= F b - F a.
  move=> Hs pas.
  have : itv_partition a b (rcons s b).
    split; last by rewrite last_rcons.
    move: s Hs pas; apply: last_ind => /=; first by rewrite ab.
    move=> s ls _ H.
    rewrite rcons_path => /andP[pas lasls].
    rewrite !rcons_path pas lasls/= last_rcons.
    have := nth_rcons b s ls (size s).
    rewrite ltnn eq_refl => <-.
    have := H (size s).
    rewrite size_rcons => /(_ (ltnSn (size s))).
    by rewrite inE => -[+ _] => /[!in_itv]/= /andP[].
  move/nondecreasing_fun_sum_le.
  rewrite size_rcons (big_addn 0%N _ 1%N) subn1/= big_nat/=.
  under eq_bigr.
    move=> i si.
    rewrite addn1/= nth_rcons si.
    over.
  by rewrite -big_nat.
have fin_S m : finite_set (S m).
  apply: contrapT => /infinite_set_fset.
  move=> /(_ (m.+1 * `|ceil (F b - F a)|).+1)[B BSm mFbFaB].
  set s := sort <=%R B.
  have := jumpfafb m s.
  have HsSm n : (n < size s)%N -> nth b s n \in S m.
    move=> ns; apply/mem_set/BSm/set_mem.
    by rewrite mem_setE -(@mem_sort _ <=%R) mem_nth.
  move/(_ HsSm){HsSm}.
  have Hpas : path <%R a s.
    rewrite lt_path_sortedE; apply/andP; split.
      apply/allP => x.
      rewrite mem_sort => /BSm[+ _].
      by rewrite in_itv/= => /andP[].
    by rewrite sort_lt_sorted; exact: fset_uniq.
  move/(_ Hpas){Hpas}.
  contra; rewrite -ltNge => _.
  apply: (@le_lt_trans _ _`|ceil (F b - F a)|%:R).
    by rewrite natr_absz intr_norm ler_normr ceil_ge.
  apply: (@lt_trans _ _ (m.+1%:R^-1 * #|` B|%:R)).
    by rewrite ltr_pdivlMl// -natrM ltr_nat.
  rewrite card_fset_sum1 natr_sum mulr_sumr mulr1 big_tnth cardfE.
  rewrite -(big_mkord xpredT (fun=> m.+1%:R^-1)) size_sort cardfE.
  rewrite ltr_sum_nat//; first by rewrite -cardfE (leq_trans _ mFbFaB).
  move=> k; rewrite leq0n/= => kB.
  have : nth b s k \in S m.
    apply/mem_set/BSm => /=; rewrite -(@mem_sort _ <=%R).
    by apply/mem_nth; rewrite size_sort cardfE.
  by rewrite inE => -[].
suff -> : A = \bigcup_m S m.
  by apply: bigcup_countable => // n _; exact: finite_set_countable.
rewrite eqEsubset; split.
- move=> x Ax.
  pose z : elt_type := exist (fun x => x \in A) x (mem_set Ax).
  have [m Hz] := FrBFl z.
  exists m => //.
  by split; [move: (Ax) => -[]|exact: Hz].
- move=> x [m _ []] /[dup] xab /[!in_itv]/= /andP[ax xb] mx.
  split => //; split.
  + apply: nondecreasing_at_left_is_cvgr; near=> r.
    * apply: itv_sub_in2 ndF.
      apply: (subset_itvW _ _ _ (ltW xb)).
      by near: r; exact: nbhs_left_ge.
    * exists (F x) => _/= [z zrx <-].
      apply: ndF.
      - apply: (subset_itvW _ _ _ (ltW xb) zrx).
        by near: r; exact: nbhs_left_ge.
      - exact: subset_itv_oo_cc.
      - by move: zrx => /[!in_itv]/= /andP[_ /ltW].
  + apply: nondecreasing_at_right_is_cvgr; near=> r.
    * apply: itv_sub_in2 ndF.
      apply: (subset_itvW _ _ (ltW ax)).
      by near: r; exact: nbhs_right_le.
    * exists (F x) => _/= [z zxr <-].
      apply: ndF.
      - exact: subset_itv_oo_cc.
      - apply: (subset_itvW _ _ (ltW ax) _ zxr).
        by near: r; exact: nbhs_right_le.
      - by move: zxr => /[!in_itv]/= /andP[/ltW].
  + apply/negP => /eqP Fxlr.
    contra: mx; rewrite -leNgt => _.
    by rewrite /Fl Fxlr subrr.
Unshelve. all: end_near. Qed.

End discontinuity_countable.
