(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
Require Import ereal reals signed topology prodnormedzmodule normedtype derive.
Require Import sequences real_interval.
From HB Require Import structures.

(**md**************************************************************************)
(* # Real-valued functions over reals                                         *)
(*                                                                            *)
(* This file provides properties of standard real-valued functions over real  *)
(* numbers (e.g., the continuity of the inverse of a continuous function).    *)
(*                                                                            *)
(* ```                                                                        *)
(*        nondecreasing_fun f == the function f is non-decreasing             *)
(*        nonincreasing_fun f == the function f is non-increasing             *)
(*           increasing_fun f == the function f is (strictly) increasing      *)
(*           decreasing_fun f == the function f is (strictly) decreasing      *)
(*                                                                            *)
(*  lime_sup f a/lime_inf f a == limit sup/inferior of the extended           *)
(*                               real-valued function f at point a            *)
(*                                                                            *)
(* derivable_oo_continuous_bnd f x y == f is derivable on `]x, y[ and         *)
(*                               continuous up to the boundary                *)
(* ```                                                                        *)
(*                                                                            *)
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

Section fun_cvg.

Section fun_cvg_realFieldType.
Context {R : realFieldType}.

(* NB: see cvg_addnl in topology.v *)
Lemma cvg_addrl (M : R) : M + r @[r --> +oo] --> +oo.
Proof.
move=> P [r [rreal rP]]; exists (r - M); split.
  by rewrite realB// num_real.
by move=> m; rewrite ltr_subl_addl => /rP.
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
  by rewrite ler_pdivr_mulr// ler_pmulr// ler1n.
- apply: fppl =>//=; near: t.
  exists (a / 2) => //=; first by rewrite divr_gt0.
  move=> z/= + _ => /lt_le_trans; apply.
  by rewrite ler_pdivr_mulr// ler_pmulr// ler1n.
Unshelve. all: by end_near. Qed.

End fun_cvg_realFieldType.

Section cvgr_fun_cvg_seq.
Context {R : realType}.

Lemma cvg_at_rightP (f : R -> R) (p l : R) :
  f x @[x --> p^'+] --> l <->
  (forall u : R^nat, (forall n, u n > p) /\ (u --> p) ->
    f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le fpl u [up /cvgrPdist_lt ucvg]|pfl].
  apply/cvgrPdist_le => e e0.
  have [r /= r0 {}fpl] := fpl _ e0; have [s /= s0 {}ucvg] := ucvg _ r0.
  near=> t; apply: fpl => //=; apply: ucvg => /=.
  by near: t; exists s.
apply: contrapT => fpl; move: pfl; apply/existsNP.
suff: exists2 x : R ^nat,
    (forall k, x k > p) /\ x --> p & ~ f (x n) @[n --> \oo] --> l.
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
  rewrite distrC (lt_le_trans xpt)// -(@invrK _ r) lef_pinv ?posrE ?invr_gt0//.
  near: t; exists `|ceil (r^-1)|%N => // s /=.
  rewrite -ltnS -(@ltr_nat R) => /ltW; apply: le_trans.
  by rewrite natr_absz gtr0_norm ?ceil_gt0 ?invr_gt0// ceil_ge.
move=> /cvgrPdist_lt/(_ e%:num (ltac:(by [])))[] n _ /(_ _ (leqnn _)).
rewrite /sval/=; case: cid => // x [px xpn].
by rewrite leNgt distrC => /negP.
Unshelve. all: by end_near. Qed.

Lemma cvg_at_leftP (f : R -> R) (p l : R) :
  f x @[x --> p^'-] --> l <->
  (forall u : R^nat, (forall n, u n < p) /\ (u --> p) ->
    f (u n) @[n --> \oo] --> l).
Proof.
apply: (iff_trans (cvg_at_leftNP f p l)).
apply: (iff_trans (cvg_at_rightP _ _ _)).
split=> [pfl u [pu up]|pfl u [pu up]].
  rewrite -(opprK u); apply: pfl.
  by split; [move=> k; rewrite ltr_oppr opprK//|exact/cvgNP].
apply: pfl.
by split; [move=> k; rewrite ltr_oppl//|apply/cvgNP => /=; rewrite opprK].
Qed.

End cvgr_fun_cvg_seq.

Section cvge_fun_cvg_seq.
Context {R : realType}.

Lemma cvge_at_rightP (f : R -> \bar R) (p l : R) :
  f x @[x --> p^'+] --> l%:E <->
  (forall u : R^nat, (forall n, u n > p) /\ u --> p ->
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
have y_p : y_ --> p.
  apply/cvgrPdist_lt => e e0; near=> t.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  rewrite /y_ /sval/=; case: cid2 => //= x /andP[_ + _].
  rewrite ltr_subl_addr => /lt_le_trans; apply.
  rewrite addrC ler_add2r -(invrK e) lef_pinv// ?posrE ?invr_gt0//.
  near: t.
  exists `|ceil e^-1|%N => // k /= ek.
  rewrite (le_trans (ceil_ge _))// (@le_trans _ _ `|ceil e^-1|%:~R)//.
    by rewrite ger0_norm// ?ceil_ge0// ?invr_ge0// ltW.
  by move: ek;rewrite -(leq_add2r 1) !addn1 -(ltr_nat R) => /ltW.
have /fine_cvgP[[m _ mfy_] /= _] := h _ (conj py_ y_p).
near \oo => n.
have mn : (m <= n)%N by near: n; exists m.
have {mn} := mfy_ _ mn.
rewrite /y_ /sval; case: cid2 => /= x _.
Unshelve. all: by end_near. Qed.

Lemma cvge_at_leftP (f : R -> \bar R) (p l : R) :
  f x @[x --> p^'-] --> l%:E <->
  (forall u : R^nat, (forall n, u n < p) /\ u --> p ->
    f (u n) @[n --> \oo] --> l%:E).
Proof.
apply: (iff_trans (cvg_at_leftNP f p l%:E)).
apply: (iff_trans (cvge_at_rightP _ _ l)); split=> h u [up pu].
- rewrite (_ : u = \- (\- u))%R; last by apply/funext => ?/=; rewrite opprK.
  by apply: h; split; [by move=> n; rewrite ltr_oppl opprK|exact: cvgN].
- by apply: h; split => [n|]; [rewrite ltr_oppl|move/cvgN : pu; rewrite opprK].
Qed.

End cvge_fun_cvg_seq.

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
rewrite ler_distlC (le_trans Mefp (ndf _ _ _))//= (@le_trans _ _ M) ?ler_addl//.
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
  split => //; case: b ab {lef ubf M} => [[|] t ta|[]] /=.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    by rewrite in_itv/= !midf_lt.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    by rewrite in_itv/= midf_lt// midf_le// ltW.
  - by exists (f (a + 1)), (a + 1).
  - by exists (f (a + 1)), (a + 1) => //=; rewrite in_itv/= ltr_addl andbT.
apply/cvgrPdist_le => _/posnumP[e].
have {supf} [p [ap pb]] :
    exists p, [/\ a < p, (BLeft p < b)%O & M - e%:num <= f p].
  have [_ -[p apb] <- /ltW efp] := sup_adherent (gt0 e) supf.
  move: apb; rewrite /= in_itv/= -[X in _ && X]/(BLeft p < b)%O => /andP[ap pb].
  by exists p; split.
rewrite ler_subl_addr {}/M.
move: b ab pb lef ubf => [[|] b|[//|]] ab pb lef ubf; set M := sup _ => Mefp.
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite ler_subl_addr ler_addl.
    apply: sup_ub => //=; exists r => //; rewrite in_itv/=.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_lt].
  + rewrite (le_trans Mefp)// ler_add2r lef//=; last 2 first.
      by rewrite in_itv/= ap.
      by near: r; exact: nbhs_right_le.
    apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_lt].
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite ler_subl_addr ler_addl.
    apply: sup_ub => //=; exists r => //; rewrite in_itv/=.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_le].
  + rewrite (le_trans Mefp)// ler_add2r lef//=; last 2 first.
      by rewrite in_itv/= ap.
      by near: r; exact: nbhs_right_le.
    by apply/andP; split; near: r; [exact: nbhs_right_gt|exact: nbhs_right_le].
- near=> r; rewrite ler_distl; apply/andP; split.
  suff: f r <= M by apply: le_trans; rewrite ler_subl_addr ler_addl.
  apply: sup_ub => //=; exists r => //; rewrite in_itv/= andbT.
    by near: r; apply: nbhs_right_gt.
  rewrite (le_trans Mefp)// ler_add2r lef//.
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
  by move=> r s rab sab /nif; rewrite ler_opp2; exact.
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

End fun_cvg_realType.
Arguments nondecreasing_at_right_cvgr {R f a} b.
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
  by move=> x /ltW Nx; rewrite Nf// ler_paddr.
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
        by rewrite fine_le// ?f_fin_num//; apply: ereal_sup_ub; exists x.
      rewrite fine_le// ?f_fin_num//; first exact/xB.
      by apply: ereal_sup_ub; exists m.
    - by exists (g 0%R), 0%R.
  rewrite fineK//; apply/eqP; rewrite eq_le; apply/andP; split.
    apply: le_ereal_sup => _ /= [_ [m _] <-] <-.
    rewrite /g; have [_|xm] := ltP m x.
      by rewrite fineK// ?f_fin_num//; exists x.
    by rewrite fineK// ?f_fin_num//; [exists m|exact/xB].
  apply: ub_ereal_sup => /= _ [m _] <-.
  have [mx|xm] := ltP m x.
    rewrite (le_trans (ndf _ _ (ltW mx)))//.
    apply: ereal_sup_ub => /=; exists (fine (f x)); last first.
      by rewrite fineK// f_fin_num.
    by exists m => //; rewrite /g mx.
  apply: ereal_sup_ub => /=; exists (fine (f m)) => //.
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
  rewrite -lee_fin (fineK l_fin_num); apply: ereal_sup_ub.
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
  by rewrite Nf// ay/= -(subrK a y) -ler_subr_addr ltW.
have [lnoo|lnoo] := eqVneq l -oo.
  rewrite lnoo; apply/cvgeNyPle => M.
  have /ereal_inf_lt[x [y]]/= : M%:E > l by rewrite lnoo ltNyr.
  rewrite in_itv/= -[X in _ && X]/(BLeft y < b)%O/= => /andP[ay yb] <- fyM.
  exists (y - a)%R => /=; first by rewrite subr_gt0.
  move=> z /= + az.
  rewrite ltr0_norm ?subr_lt0// opprB ltr_subl_addr subrK => zy.
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
  - by exists (a + 1)%R; rewrite ?fpoo// in_itv/= andbT ltr_addl.
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
  rewrite ltr0_norm ?subr_lt0// opprB ltr_subl_addr subrK// => zx.
  by rewrite f_fin_num// axA// az/= ltW.
set g := fun n => if (a < n < x)%R then fine (f n) else fine (f x).
have <- : inf [set g x | x in [set` Interval (BRight a) b]] = fine l.
  apply: EFin_inj; rewrite -ereal_inf_EFin//; last 2 first.
    - exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
      case: ifPn => [/andP[am mx]|].
        rewrite fine_le// ?f_fin_num//; first by rewrite axA// am (ltW mx).
        apply: ereal_inf_lb; exists m => //=.
        rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am/=.
        by rewrite (le_lt_trans _ xb) ?ltW.
      rewrite negb_and -!leNgt => /orP[ma|xm].
        rewrite fine_le// ?f_fin_num ?inE//.
        apply: ereal_inf_lb; exists x => //=.
        by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.
      rewrite fine_le// ?f_fin_num ?inE//.
      apply: ereal_inf_lb; exists x => //=.
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
        by rewrite in_itv/= andbT ltr_addl.
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
    apply: ereal_inf_lb => /=; exists (fine (f m)); last first.
      by rewrite fineK// f_fin_num// axA// am (ltW mx).
    by exists m; [rewrite in_itv/= am|rewrite /g am mx].
  rewrite (@le_trans _ _ (f x))//; last first.
    by apply: ndf => //; rewrite in_itv//= ?ax ?am.
  apply: ereal_inf_lb => /=; exists (fine (f x)); last first.
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
  rewrite ltr0_norm// ?subr_lt0// opprB ltr_subl_addr => /lt_le_trans; apply.
  by rewrite -ler_subr_addr ler_pdivr_mulr// ler_pmulr// ?ler1n// subr_gt0.
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
  rewrite -lee_fin (fineK l_fin_num); apply: ereal_inf_lb.
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
by apply: ereal_sup_ub => /=; exists t => //; split => //; exact: le_ball rt.
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
Proof. by move=> sr; rewrite /inf_ball lee_oppl oppeK sup_ball_le. Qed.

Let inf_ball_is_cvg f a : cvg (inf_ball f a e @[e --> 0^'+]).
Proof.
apply: nonincreasing_at_right_is_cvge; near=> e.
by move=> x y; rewrite !in_itv/= => /andP[x0 xe] /andP[y0 ye] /inf_ball_le.
Unshelve. all: by end_near. Qed.

Let le_sup_ball f g a :
  (forall r, (0 < r)%R -> forall y : R, y != a -> ball a r y -> f y <= g y) ->
  \forall r \near 0^'+, sup_ball f a r <= sup_ball g a r.
Proof.
move=> fg; near=> r; apply: ub_ereal_sup => /= _ [s [pas /= /eqP ps]] <-.
apply: (@le_trans _ _ (g s)); first exact: (fg r).
by apply: ereal_sup_ub => /=; exists s => //; split => //; exact/eqP.
Unshelve. all: by end_near. Qed.

Lemma lime_sup_lim f a : lime_sup f a = lim (sup_ball f a e @[e --> 0^'+]).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: lime_ge => //; near=> e; apply: ereal_inf_lb => /=.
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

Lemma lime_sup_ge0 f a : (forall x, 0 <= f x) -> 0 <= lime_sup f a.
Proof.
move=> f0; rewrite lime_supE; apply: lb_ereal_inf => /= x [e /=].
rewrite in_itv/= andbT => e0 <-{x}; rewrite -(ereal_sup1 0) ereal_sup_le //=.
exists (f (a + e / 2)%R); last by rewrite ereal_sup1 f0.
exists (a + e / 2)%R => //=; split.
  rewrite /ball/= opprD addrA subrr sub0r normrN gtr0_norm ?divr_gt0//.
  by rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n.
by apply/eqP; rewrite gt_eqF// ltr_spaddr// divr_gt0.
Qed.

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
  by move=> /andP[? ?] /andP[? ?] xy; apply: lee_add => //; exact: sup_ball_le.
- near=> a0; apply: ub_ereal_sup => _ /= [a1 [a1ae a1a]] <-.
  by apply: lee_add; apply: ereal_sup_ub => /=; exists a1.
Unshelve. all: by end_near. Qed.

Lemma lime_sup_le f g a :
  (forall r, (0 < r)%R -> forall y, y != a -> ball a r y -> f y <= g y) ->
  lime_sup f a <= lime_sup g a.
Proof.
by move=> fg; rewrite !lime_sup_lim; apply: lee_lim => //; exact: le_sup_ball.
Qed.

Lemma lime_inf_sup f a : lime_inf f a <= lime_sup f a.
Proof.
rewrite lime_inf_lim lime_sup_lim; apply: lee_lim => //.
near=> r.
rewrite ereal_sup_le//.
have ? : exists2 x, ball a r x /\ x <> a & f x = f (a + r / 2)%R.
  exists (a + r / 2)%R => //;  split.
    rewrite /ball/= opprD addrA subrr sub0r normrN gtr0_norm ?divr_gt0//.
    by rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n.
  by apply/eqP; rewrite gt_eqF// ltr_spaddr// divr_gt0.
by exists (f (a + r / 2)%R) => //=; rewrite inf_ballE ereal_inf_lb.
Unshelve. all: by end_near. Qed.

Local Lemma lim_lime_sup' f a (l : R) :
  f r @[r --> a] --> l%:E -> lime_sup f a <= l%:E.
Proof.
move=> fpA; apply/lee_addgt0Pr => e e0; rewrite lime_sup_lim.
apply: lime_le => //.
move/fine_cvg : (fpA) => /cvgrPdist_le fpA1.
move/fcvg_is_fine : (fpA); rewrite near_map => -[d d0] fpA2.
have := fpA1 _ e0 => -[q /= q0] H.
near=> x.
apply: ub_ereal_sup => //= _ [y [pry /= yp <-]].
have ? : f y \is a fin_num.
  apply: fpA2.
  rewrite /ball_ /= (lt_le_trans pry)//.
  by near: x; exact: nbhs_right_le.
rewrite -lee_subel_addl// -(@fineK _ (f y)) // -EFinB lee_fin.
rewrite (le_trans (ler_norm _))// distrC H// /ball_/= ltr_distlC.
move: pry; rewrite /ball/= ltr_distlC => /andP[pay ypa].
have xq : (x <= q)%R by near: x; exact: nbhs_right_le.
apply/andP; split.
  by rewrite (le_lt_trans _ pay)// ler_sub.
by rewrite (lt_le_trans ypa)// ler_add2l.
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
rewrite -(@fineK _ (f y)) // -EFinB lee_fin ler_subl_addr -ler_subl_addl.
rewrite (le_trans (ler_norm _))// H// /ball_/= ltr_distlC.
move: pry; rewrite /ball/= ltr_distlC => /andP[pay ypa].
have xq : (x <= q)%R by near: x; exact: nbhs_right_le.
apply/andP; split.
  by rewrite (le_lt_trans _ pay)// ler_sub.
by rewrite (lt_le_trans ypa)// ler_add2l.
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
      rewrite (le_lt_trans _ farl)//; apply: ereal_inf_lb => /=; exists r => //.
      by rewrite in_itv/= r0.
    by rewrite fal ltxx.
  by rewrite -leNgt; apply: le_trans; rewrite lee_add2r// fal.
move=> e; have [d /andP[lfp fpe]] := H e.
exists d => r /= [] prd rp.
by rewrite (le_lt_trans _ fpe)//; apply: ereal_sup_ub => /=; exists r.
Qed.

Local Lemma lime_infP f a l :
  lime_inf f a = l%:E -> forall e : {posnum R}, exists d : {posnum R},
  forall x, (ball a d%:num `\ a) x -> l%:E - e%:num%:E < f x.
Proof.
move=> /(congr1 oppe); rewrite -lime_supN => /lime_supP => H e.
have [d {}H] := H e.
by exists d => r /H; rewrite lte_oppl oppeD// EFinN oppeK.
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
    by rewrite inffpl lte_subl_addr// lte_addl.
  rewrite lime_infE => /ereal_sup_gt[x /= [r]]; rewrite in_itv/= andbT.
  move=> r0 <-{x} H; exists (PosNum r0); rewrite ltW//.
  by rewrite -inf_ballE.
have [d2 Hd2] : exists d2 : {posnum R},
    ereal_sup [set f x | x in ball a d2%:num `\ a] <= l%:E + e%:num%:E.
  have : lime_sup f a < l%:E + e%:num%:E by rewrite supfpl lte_addl.
  rewrite lime_supE => /ereal_inf_lt[x /= [r]]; rewrite in_itv/= andbT.
  by move=> r0 <-{x} H; exists (PosNum r0); rewrite ltW.
pose d := minr d1%:num d2%:num.
have d0 : (0 < d)%R by rewrite lt_minr; apply/andP; split => //=.
move/cvgrPdist_lt : up => /(_ _ d0)[m _] {}ucvg.
near=> n.
rewrite /= ler_distlC; apply/andP; split.
  rewrite -lee_fin EFinB (le_trans Hd1)//.
  rewrite (@le_trans _ _ (ereal_inf [set f x | x in ball a d `\ a]))//.
    apply: le_ereal_inf => _/= [r [adr ra] <-]; exists r => //; split => //.
    by rewrite /ball/= (lt_le_trans adr)// /d le_minl lexx.
  apply: ereal_inf_lb => /=; exists (u n).
    split; last by apply/eqP; rewrite eq_sym lt_eqF.
    by apply: ucvg => //=; near: n; by exists m.
  by rewrite fineK//; by near: n.
rewrite -lee_fin EFinD (le_trans _ Hd2)//.
rewrite (@le_trans _ _ (ereal_sup [set f x | x in ball a d `\ a]))//; last first.
  apply: le_ereal_sup => z/= [r [adr rp] <-{z}]; exists r => //; split => //.
  by rewrite /ball/= (lt_le_trans adr)// /d le_minl lexx orbT.
apply: ereal_sup_ub => /=; exists (u n).
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
    rewrite -[X in X < _ -> _](opprK (f b)) ltr_oppl => ofaLofb.
    have := main _ c ofC ofI a b aI bI ofaLofb aLc cLb.
    by (do 2 rewrite ltr_oppl opprK); rewrite and_comm.
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
suff : (- f) y <= (- f) x = (y <= x) by rewrite ler_oppl opprK.
apply: itv_continuous_inj_le xI => // [|x1 x1I | x1 x2 x1I x2I].
- by exists a, b; split => //; rewrite ler_oppl opprK.
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
move=> aLb fC fK x y xfbfa yfbfa; rewrite -ler_opp2.
apply: (@segment_can_le (- b) (- a) (f \o -%R) (- g));
    rewrite /= ?ler_opp2 ?opprK //.
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
  by rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n.
rewrite ler_distlC; near: y.
pose u := minr (f x + e%:num / 2) (f b).
pose l := maxr (f x - e%:num / 2) (f a).
have ufab : u \in `[f a, f b].
  rewrite !in_itv /= le_minl ?le_minr lexx ?fle // le_ab orbT ?andbT.
  by rewrite ler_paddr // fle.
have lfab : l \in `[f a, f b].
  rewrite !in_itv/= le_maxl ?le_maxr lexx ?fle// le_ab orbT ?andbT.
  by rewrite ler_subl_addr ler_paddr// fle // lexx.
have guab : g u \in `[a, b].
  rewrite !in_itv; apply/andP; split; have := ufab; rewrite in_itv => /andP.
    by case; rewrite /= -gle // ?fK // bound_itvE fle.
  by case => _; rewrite /= -gle // ?fK // bound_itvE fle.
have glab : g l \in `[a, b].
  rewrite !in_itv; apply/andP; split; have := lfab; rewrite in_itv /= => /andP.
    by case; rewrite -gle // ?fK // bound_itvE fle.
  by case => _; rewrite -gle // ?fK // bound_itvE fle.
have faltu : f a < u.
  rewrite /u comparable_lt_minr ?real_comparable ?num_real// flt// aLb andbT.
  by rewrite (@le_lt_trans _ _ (f x)) ?fle// ltr_addl.
have lltfb : l < f b.
  rewrite /u comparable_lt_maxl ?real_comparable ?num_real// flt// aLb andbT.
  by rewrite (@lt_le_trans _ _ (f x)) ?fle// ltr_subl_addr ltr_addl.
case: pselect => // _; rewrite near_withinE; near_simpl.
have Fnbhs : Filter (nbhs x) by apply: nbhs_filter.
have := ax; rewrite le_eqVlt => /orP[/eqP|] {}ax.
  near=> y => /[dup] yab; rewrite /= in_itv => /andP[ay yb]; apply/andP; split.
    by rewrite (@le_trans _ _ (f a)) ?fle// ler_subl_addr ax ler_paddr.
  apply: ltW; suff : f y < u by rewrite lt_minr => /andP[->].
  rewrite -?[f y < _]glt// ?fK//; last by rewrite in_itv /= !fle.
  by near: y; near_simpl; apply: open_lt; rewrite /= -flt ?gK// -ax.
have := xb; rewrite le_eqVlt => /orP[/eqP {}xb {ax}|{}xb].
  near=> y => /[dup] yab; rewrite /= in_itv /= => /andP[ay yb].
  apply/andP; split; last by rewrite (@le_trans _ _ (f b)) ?fle// xb ler_paddr.
  apply: ltW; suff : l < f y by rewrite lt_maxl => /andP[->].
  rewrite -?[_ < f y]glt// ?fK//; last by rewrite in_itv /= !fle.
  by near: y; near_simpl; apply: open_gt; rewrite /= -flt// gK// xb.
have xoab : x \in `]a, b[ by rewrite in_itv /=; apply/andP; split.
near=> y; suff: l <= f y <= u.
  by rewrite le_maxl le_minr -!andbA => /and4P[-> _ ->].
have ? : y \in `[a, b] by apply: subset_itv_oo_cc; near: y; apply: near_in_itv.
have fyab : f y \in `[f a, f b] by rewrite in_itv/= !fle// ?ltW.
rewrite -[l <= _]gle -?[_ <= u]gle// ?fK //.
apply: subset_itv_oo_cc; near: y; apply: near_in_itv; rewrite in_itv /=.
rewrite -[x]fK // !glt//= lt_minr lt_maxl ?andbT ltr_subl_addr ltr_spaddr //.
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
  by move=> x y xab yab; rewrite ler_opp2 fge.
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
have xBeLxDe : x - e <= x + e by rewrite ler_add2l gt0_cp.
have fcte : {in `[x - e, x + e], continuous f}.
  by near: e; apply/at_right_in_segment.
have fwcte : {within `[x - e, x + e], continuous f}.
  apply: continuous_in_subspaceT => y yI.
  by apply: fcte; move/set_mem: yI.
have fKe : {in `[x - e, x + e], cancel f g}
  by near: e; apply/at_right_in_segment.
have nearfx : \forall y \near f x, y \in f @`](x - e), (x + e)[.
  apply: near_in_itv; apply: mono_mem_image_itvoo; last first.
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
by rewrite exprS; under eq_fun do rewrite exprS; exact: ih.
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
- rewrite sqrtr0; apply/cvgr0Pnorm_lt => _ /posnumP[e]; near=> y.
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
  (forall x, is_derive x 1 f 0) -> f x = f y.
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
  
Section bounded_variation.

Context {R : realType}.

Fixpoint partition (a b : R) l := 
  match l with 
  | nil => False
  | p :: nil => p = a /\ p = b
  | p :: ((q :: l) as rest) => p = a /\ p <= q /\ partition q b rest
  end.

Arguments partition _ _ : simpl never.

Lemma partition_head (a b x : R) l : partition a b (x :: l) -> a = x.
Proof. by case: l => [[]|? ? [->]]. Qed.

Lemma partition_le (a b : R) l : partition a b l -> a <= b.
Proof. 
by elim: l a => //= a [_ ? [->->] //| ] x l IH ? [<- [ + /IH]]; exact: le_trans.
Qed.

Lemma partition_tail (a b x y : R) l : 
  partition a b (x :: y :: l) -> partition y b (y :: l).
Proof. by case=> [-> [//]]. Qed.

Lemma partition_consP (a b x y : R) l : partition a b (x :: y :: l) <-> 
  [/\ a = x, a <= y, y <= b & partition y b (y :: l)].
Proof. 
split; last by case => ->.
move=> /[dup]; case => -> [-> ?] /partition_tail/partition_le ->. 
by split.
Qed.


Lemma partitionrr (a b : R) l : partition a b (a :: a :: l) -> partition a b (a :: l).
Proof. by elim: l a => [ ? [_ [//]]| ?] l IH a /= [_ [_ ]]. Qed.

Lemma partition_cons (a b : R) l : partition a b l -> partition a b (a :: l).
Proof. by case: l => //= ? [[-> -> //]|] ? ? [-> [? ?]]. Qed.

Lemma partition_eq a l x : partition a a l -> x \in l -> x = a.
Proof.
elim: l x a => //= x [_ ? ? [-> _ /[!inE]/eqP//]|] a l IH ? ?. 
move=> /partition_consP[-> ? ax]; have -> : x = a by apply/le_anti/andP; split.
by move/IH => P; rewrite in_cons => /orP [/eqP //|]; apply: P.
Qed.

Lemma partition2 a b : a <= b -> partition a b (a :: b :: nil).
Proof. by split; rewrite //= andbT. Qed.

Lemma partition_concat a b c l1 l2: 
  partition a b l1 -> 
  partition b c l2 -> 
  partition a c (l1 ++ l2). 
Proof.
elim: l1 a b l2 => // x [_ ? ? ? [-> ->]|]; first exact: partition_cons.
move=> a l1 IH p b l2 pbxa1 pb2.
rewrite ?cat_cons -(partition_head pbxa1); split => //.
split; first by case: pbxa1 => -> [].
apply: IH; last exact: pb2. 
by case: l1 pbxa1=> [[-> [_ [_ -> //]]]|] ? ? /= [_ [_]].
Qed.

Lemma partition_concat_tl a b c l1 l2: 
  partition a b l1 -> 
  partition b c l2 -> 
  partition a c (l1 ++ List.tl l2). 
Proof.
elim: l1 a b l2 => // x [? ? ? l2 [-> ->]|]. 
  by case: l2 => //= ? [[-> -> //]| ? ? [-> [? ?]]]; split => //.
move=> a l1 IH p b l2 pbxa1 pb2.
rewrite ?cat_cons -(partition_head pbxa1); split => //.
split; first by case: pbxa1 => -> [].
apply: IH; last exact: pb2. 
by case: l1 pbxa1=> [[-> [_ [_ -> //]]]|] ? ? /= [_ [_]].
Qed.

Definition pvar part (f : R -> R)  := 
   \sum_(xy <- zip part (List.tl part)) `|f xy.2 - f xy.1|.

Definition variations a b f := [set pvar l f | l in partition a b].

Definition total_variation a b (f : R -> R) :=
  ereal_sup [set x%:E | x in (variations a b f)].

Local Notation TV := total_variation.

Lemma variations_n0 a b f : a <= b -> variations a b f !=set0.
Proof.
move=> ?; exists (pvar (a :: b :: nil) f), (a::b::nil) => //.
Qed.

Lemma pvar_cons0 f a l : 
  pvar (a :: a :: l) f = pvar (a :: l) f.
Proof. by rewrite /pvar /= big_cons /= subrr normr0 add0r. Qed.

Lemma pvar_consE f a b l : 
  pvar (a :: b :: l) f = `|f b - f a| + pvar (b :: l) f.
Proof. by rewrite /pvar /= big_cons. Qed.

Lemma partition_TV f a b l : 
  partition a b l -> 
  a <= b ->
  ((pvar l f)%:E <= TV a b f)%E.
Proof.
move=> pl alb; rewrite /total_variation/sup/supremum. 
rewrite /ereal_sup/supremum.
case E: (_ == _).
  have /set0P := (@variations_n0 _ _ f alb); move/eqP/image_set0_set0:E ->. 
  by move/eqP.
rewrite /has_ubound; case: xgetP.
  move=> w wE [] /(_ (pvar l f)%:E) + _; apply; exists (pvar l f) => //.
  by exists l.
have [w Qw] := @ereal_supremums_neq0 R [set x%:E | x in variations a b f].
by move => /(_ w).
Qed.

Lemma partition_TV2 a b f: a <= b -> (`|f b - f a|%:E <= TV a b f)%E.
Proof.
move=> ?; suff -> : `|f b - f a| = pvar (a :: b :: nil) f.
  by apply: partition_TV => //; apply: partition2.
by rewrite /pvar /= big_seq1.
Qed.

Lemma total_variation_ge0 a b f: a <= b -> (0 <= TV a b f)%E.
Proof. by move=> ab; apply: le_trans; last exact: partition_TV2. Qed.

Definition bounded_variation a b (f : R -> R) := 
  has_ubound (variations a b f).

Definition bounded_variationT (f : R -> R) :=
  forall a b, bounded_variation a b f.

Lemma hasNrub_ereal_sup (A : set R) : ~ has_ubound A ->
  A !=set0 -> ereal_sup [set x%:E | x in A] = +oo%E.
Proof.
move=> hasNubA /[dup] [][a Aa] A0.
apply/eqP; rewrite eq_le leey /= leNgt; apply: contra_notN hasNubA => Aoo.
exists (sup A); apply: sup_ub.
exists (fine (ereal_sup [set x%:E | x in A])) => w Aw.
have -> : w = fine (ereal_sup [set x%:E | x in [set w]]).
  by rewrite ereal_sup_EFin /= ?sup1 //; exists w => // ? ->.
rewrite fine_le //.
  by rewrite ereal_sup_EFin //=; exists w => // ? ->.
  apply/fin_real/andP; split => //.
  rewrite ltNge leeNy_eq; apply/negP => /eqP/ereal_sup_ninfty/(_ (w%:E)).
  apply/not_implyP; split => //; by exists w. 
by apply: le_ereal_sup => ? [? -> <-]; exists w.
Qed.

Lemma bounded_variationP a b f : a <= b ->
  bounded_variation a b f <-> TV a b f \is a fin_num.
Proof.
split; first by move=> ?; rewrite /TV ereal_sup_EFin //; exact: variations_n0.
rewrite ge0_fin_numE ?total_variation_ge0 //; apply: contraPP => Nbdf.
suff -> : (TV a b f = +oo)%E by [].
apply: hasNrub_ereal_sup => //; exact: variations_n0.
Qed.

Lemma variationN a b f : 
  variations a b (\- f) = variations a b f.
Proof.
rewrite /variations; suff -> : pvar^~ f = pvar ^~ (\- f) by [].
rewrite /pvar /= funeqE => x /=. 
by under eq_bigr => i _ do rewrite -normrN -mulN1r mulrBr ?mulN1r.
Qed.

Lemma total_variationN a b f : TV a b (\- f) = TV a b f.
Proof. by rewrite /TV; rewrite variationN. Qed.

Lemma bounded_variationN a b f : 
  bounded_variation a b f -> bounded_variation a b (\- f).
Proof. by rewrite /bounded_variation variationN. Qed.

Lemma bounded_variation_le a b p q f : 
  bounded_variation a b f -> p <= q -> a <= p -> q <= b -> 
  bounded_variation p q f.
Proof.
move=> + pq ap qb; have ab : a <= b by exact/(le_trans ap)/(le_trans pq).
case=> M ubdM; exists M => ? [l pql <-]. 
apply: (@le_trans _ _ (pvar (a :: l ++ [:: b]) f)).
  rewrite /pvar /=; case: l pql => //. 
  move=> ? l /[dup]/partition_head <- pql /=.
  rewrite /= ?big_cons /=; apply ler_paddl => //. 
  elim: l p a pq {ab ubdM} ap pql => //.
    move=> ?????; rewrite /= ?big_cons; apply ler_paddl => //.
  move=> w l IH p a pq ap pql. 
  rewrite /= ?big_cons; rewrite ler_add //. 
  move: pql => [_ [?] pql]. apply: IH => //.
  exact: (@partition_le w q (w::l)).
apply: ubdM; exists (a :: l ++ [::b]) => //.
rewrite -cat_cons (_ : [:: b] = List.tl (q :: b ::nil)); last by [].
apply: (@partition_concat_tl _ q) => //.
case: l pql => // ? ? /[dup] /partition_head <- Q /=; split => //. 
Qed.

Let total_variation_concat_le a b c f : 
  a <= b -> b <= c -> (TV a b f + TV b c f <= TV a c f)%E.
Proof.
move=> ab bc; have ac : a <= c by exact: (le_trans ab).
case : (pselect (bounded_variation a c f)); first last.
  move=> nbdac; suff /eqP -> : TV a c f == +oo%E by rewrite leey.
  have: (-oo < TV a c f)%E by apply: (lt_le_trans _ (total_variation_ge0 f ac)).
  by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ ac).
move=> bdAC.
have bdf1 : bounded_variation a b f by exact: (bounded_variation_le bdAC).
have bdf2 : bounded_variation b c f by exact: (bounded_variation_le bdAC).
rewrite /total_variation ?ereal_sup_EFin => //; try exact: variations_n0.
rewrite -EFinD -sup_sumE /has_sup; try (by split => //; exact: variations_n0).
apply: le_sup.
- move=> ? [? [l1 pabl2 <-]] [? [l2 pbcl2 <-] <-]; exists (pvar (l1 ++ List.tl l2) f).
  split; first by exists (l1 ++ List.tl l2)=> //=; apply: (partition_concat_tl pabl2).
  rewrite /pvar -big_cat /=.
  rewrite (_ : (zip l1 (List.tl l1) ++ zip l2 (List.tl l2)) = zip (l1 ++ List.tl l2) (List.tl (l1 ++ List.tl l2))) //.
  elim: l1 a {bdf1 bdf2 bdAC ac ab} pabl2 pbcl2 => // x [/= _ ? [-> ->]|].
    by move=> bc2; congr (_ _ _); case: l2 bc2 => // ? ? /partition_head ->.
  move=> z ? IH ? pabl1 pbcl2 /=; congr (_ _); apply: (IH z) => //.
  by case: pabl1 => /= _ [_].
- have [x0 vx0] := (variations_n0 f ab).
  have [y0 vy0] := (variations_n0 f bc).
  exists (x0 + y0); exists x0 => //; exists y0 => //.
- split => //; exact: variations_n0.
Qed.

Fixpoint part_split x (l : seq R) :=
  match l with 
  | [::] => ([::x], [::x]) 
  | y :: tl => if x < y then ([:: x], x :: y :: tl) else 
      let xy := part_split x tl
      in (y :: xy.1, xy.2 )
  end.

Lemma part_splitl a b x l :
  a <= x -> x <= b -> partition a b l ->
  partition a x (part_split x l).1.
Proof.
elim: l a => // a [/= _ ? ax bx|].
  move: ax => /[swap]; move: bx => /[swap] [[-> ->]] ? ?.
  have -> : x = b by apply/ le_anti/andP; split.
  by rewrite lt_irreflexive /=; repeat split.
move=> w l IH ? + xb /partition_consP => /[swap] [[->]] aw wb wbl ax /=.
rewrite ltNge ax /= /=; case Nxw: (x < w) => //=. 
have wx : w <= x by rewrite leNgt Nxw.
apply/partition_consP; split => //.
by have /= := IH w wx xb wbl; rewrite Nxw.
Qed.

Lemma part_splitr a b x l :
  a <= x -> x <= b -> partition a b l ->
  partition x b (part_split x l).2.
Proof.
elim: l a => // a [/= _ ? ax bx|].
  case=> -> ->; move: (bx); rewrite le_eqVlt => /orP.
  by case=> [/eqP ->|->]; rewrite ?lt_irreflexive //=.
move=> w l IH ? + xb /partition_consP => /[swap] [[->]] aw wb wbl ax /=.
rewrite ltNge ax /= /=; case Nxw: (x < w) => //=.
  by apply/partition_consP; split => //; apply: ltW.
have wx : w <= x by rewrite leNgt Nxw.
by have /= := IH w wx xb wbl; rewrite Nxw.
Qed.

Lemma part_split_pvar a b x l f : 
  partition a b l -> 
  a <= x -> x <= b ->
  pvar l f <= pvar (part_split x l).1 f + pvar (part_split x l).2 f.
Proof.
move=> + + xb; elim: l a => // a [_ w [<- -> bx]|].
  by rewrite /pvar [x in x <= _]/= big_nil addr_ge0 //; apply: sumr_ge0 => ?.
move=> w l IH ? /partition_consP [-> aw wb pwbl ax].
rewrite /= ?[x < a]ltNge ?ax /=; case Nxw: (x < w) => /=.
  rewrite /pvar /= ?big_cons /= ?big_nil addr0 addrA.
  by rewrite ler_add2r [x in _ <= x]addrC ler_dist_add.
rewrite /pvar /= ?big_cons /= -?addrA ler_add2l. 
have wx : w <= x by rewrite leNgt Nxw.
by have /= := IH w pwbl wx; rewrite Nxw /=. 
Qed.

Let total_variation_concat_ge a b c f : 
  a <= b -> b <= c -> (TV a b f + TV b c f >= TV a c f)%E.
Proof.
move=> ab bc; have ac : a <= c by exact: (le_trans ab).
case : (pselect (bounded_variation a b f)); first last.
  move=> nbdac; have /eqP -> : TV a b f == +oo%E. 
    have: (-oo < TV a b f)%E by apply: (lt_le_trans _ (total_variation_ge0 f ab)).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ ab).
  by rewrite addye ?leey // -ltNye (@lt_le_trans _ _ 0)%E // ?total_variation_ge0 //.
case : (pselect (bounded_variation b c f)); first last.
  move=> nbdac; have /eqP -> : TV b c f == +oo%E. 
    have: (-oo < TV b c f)%E by apply: (lt_le_trans _ (total_variation_ge0 f bc)).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ bc).
  by rewrite addey ?leey // -ltNye (@lt_le_trans _ _ 0)%E // ?total_variation_ge0 //.
move=> bdAB bdAC.
rewrite /total_variation [x in (x + _)%E]ereal_sup_EFin => //; try exact: variations_n0.
rewrite [x in (_ + x)%E]ereal_sup_EFin => //; try exact: variations_n0.
rewrite -EFinD -sup_sumE /has_sup; try (by split => //; exact: variations_n0).
apply: ub_ereal_sup => ? [? [l pacl <- <-]]; rewrite lee_fin.
apply: le_trans; first exact: (@part_split_pvar a c b).
apply: sup_ub. 
  case: bdAB => M ubdM; case: bdAC => N ubdN; exists (N + M).
  move=> q [?] [i pabi <-] [? [j pbcj <-]] <-.
  by apply: ler_add; [apply: ubdN;exists i|apply:ubdM;exists j]. 
exists (pvar (part_split b l).1 f).
  by exists (part_split b l).1 => //; apply: (@part_splitl a c).
exists (pvar (part_split b l).2 f) => //.
by exists (part_split b l).2 => //; apply: (@part_splitr a c).
Qed.
  
Lemma total_variation_concatE a b c f : 
  a <= b -> b <= c -> (TV a b f + TV b c f = TV a c f)%E.
Proof.
move=> ab bc; apply/le_anti/andP; split.
  exact: total_variation_concat_le.
exact: total_variation_concat_ge.
Qed.


Definition neg_tv a f (x:R) : \bar R := ((TV a x f - (f x)%:E)*2^-1%:E)%E.

Definition pos_tv a f (x:R) : \bar R := neg_tv a (\- f) x.

Lemma neg_TV_increasing a b (f : R -> R) :
  {in `[a,b] &, {homo (neg_tv a f) : x y / x <= y >-> (x <= y)%E}}.
Proof.
move=> x y xab yab xy; have ax : a <= x.
  by move: xab; rewrite in_itv //= => /andP [].
rewrite /neg_tv lee_pmul2r // lee_subr_addl // addeCA -EFinB.
rewrite -[TV a y _](@total_variation_concatE _ x) //.
apply: lee_add => //; apply: le_trans; last exact: partition_TV2.
by rewrite lee_fin ler_norm.
Qed.

Lemma total_variation_jordan_decompE a b f : 
  bounded_variation a b f ->
  {in `[a,b], f =1 (fine \o neg_tv a (\- f)) \- (fine \o neg_tv a f)}.
Proof.
move=> bdabf x; rewrite in_itv /= => /andP [ax xb].
have ffin: TV a x f \is a fin_num.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bdabf).
have Nffin : TV a x (\- f) \is a fin_num.
  apply/bounded_variationP => //; apply/bounded_variationN.
  exact: (bounded_variation_le bdabf).
rewrite /neg_tv /= total_variationN -fineB -?muleBl // ?fineM //; first last.
- by rewrite fin_numM // fin_numD; apply/andP; split.
- by rewrite fin_numM // fin_numD; apply/andP; split.
- by apply: fin_num_adde_defl; rewrite fin_numN fin_numD; apply/andP; split.
- by rewrite fin_numB ?fin_numD ?ffin; apply/andP; split.
rewrite addeAC oppeD //= ?fin_num_adde_defl //.
by rewrite addeA subee // add0e -EFinD //= opprK mulrDl -splitr.
Qed.

Lemma neg_TV_increasing_fin a b (f : R -> R) :
  bounded_variation a b f ->
  {in `[a,b] &, {homo (fine \o neg_tv a f) : x y / x <= y}}.
Proof.
move=> bdv p q pab qab pq /=.
move: (pab) (qab); rewrite ?in_itv /= => /andP [? ?] /andP [? ?].
apply: fine_le; rewrite /neg_tv ?fin_numM // ?fin_numB /=.
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variation_le bdv).
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variation_le bdv).
by apply: (neg_TV_increasing _ pab).
Qed.

Lemma increasing_bounded_variation a b (f : R -> R) :
  {in `[a,b] &, {homo f : x y / x <= y}} ->
  bounded_variation a b f.
Proof.
move=> incf; exists (f b - f a) => ? [l pabl <-]; rewrite le_eqVlt.
apply/orP; left; apply/eqP.
rewrite /pvar; elim: l a incf pabl => // ? [].
  by move=> _ ? _ [-> ->]; rewrite /= big_nil subrr.
move=> w l IH a fi /[dup]/partition_le ab /[dup]/partition_tail/[dup] ?.
move=> /partition_le wb [] => [-> [aw _]]; rewrite /= big_cons /=.
rewrite (IH w) //; first last.
  move=> p q; rewrite in_itv /= => /andP [? ?] /andP [? ?] pq.
  by apply: fi; rewrite //in_itv; apply/andP; split => //; exact: (le_trans aw).
have -> : `|f w - f a| = f w - f a.
  rewrite ger0_norm // subr_ge0; apply: fi => //; rewrite // in_itv /=. 
    by apply/andP; split => //.
  by apply/andP; split => //.
by rewrite addrCA; congr (_ _); rewrite addrC addrA [-_ + _]addrC subrr add0r.
Qed.

Lemma neg_TV_bounded_variation a b f :
  bounded_variation a b f -> 
  bounded_variation a b (fine \o neg_tv a f).
Proof.
by move=> ?; apply increasing_bounded_variation; apply: neg_TV_increasing_fin.
Qed.

Fixpoint collapse_head (l : seq R) := 
  match l with 
  | nil => nil
  | x :: nil => x :: nil
  | x :: ((y :: _) as tl) => if x == y then collapse_head tl else x :: tl
  end.

Lemma collapse_head_consE x l : 
  collapse_head (x :: x :: l) = collapse_head (x :: l).
Proof. by rewrite /= eq_refl. Qed.

Lemma collapse_head_consNE x y l : 
  x != y -> collapse_head (x :: y :: l) = x :: y :: l.
Proof. 
move=> xy; case E: (x == y). 
  by move/eqP: E xy => ->; rewrite eq_refl.
by rewrite /= E. 
Qed. 

Lemma collapse_head_partition a b l :
  a <= b -> partition a b l -> partition a b (collapse_head l).
Proof.
elim: l a => // a [//| w l IH] ? /[swap] /partition_consP [-> + wb wbl ab].
rewrite le_eqVlt => /orP [|]. 
  by move/eqP=> ->; rewrite collapse_head_consE; exact: IH.
move=> aw; rewrite collapse_head_consNE => //.
  by apply/partition_consP; split => //; exact: ltW.
by apply/negP=> E; move /eqP: E aw => ->; rewrite lt_irreflexive.
Qed.

Lemma collapse_head_pvar l f:
  pvar l f = pvar (collapse_head l) f.
Proof.
elim: l => // w [//|] y l; case E: (w == y).
  by move/eqP: E => ->; rewrite pvar_cons0 collapse_head_consE.
by rewrite collapse_head_consNE //; rewrite E.
Qed.

Lemma collapse_head_neq l a b tl:
  (collapse_head l) = a :: b :: tl -> a != b.
Proof.
elim: l a b tl => // w [//=|x l IH] a b tl.
case E: (w == x). 
  move/eqP: E => ->; rewrite collapse_head_consE; apply: IH.
rewrite collapse_head_consNE ?E //.
by case=> <- <- _; rewrite E.
Qed.

Lemma TV_right_continuous a b x (f : R -> R) :
  a <= x -> x < b ->
  (f @ at_right x --> f x) ->
  bounded_variation a b f ->
  (fine \o TV a ^~ f @ at_right x --> fine (TV a x f)).
Proof.
move=> ax xb ctsf bvf; have ? : a <= b by apply:ltW; apply: (le_lt_trans ax).
apply/cvgrPdist_lt=> _/posnumP[eps].
have ? : Filter (nbhs x^'+) by exact: at_right_proper_filter.
have xbl := ltW xb.
have xbfin : TV x b f \is a fin_num.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
have [//|?] := @ub_ereal_sup_adherent R _ (eps%:num/2) _ xbfin.
case=> ? [l + <- <-]; rewrite -/(total_variation x b f).
rewrite collapse_head_pvar => /(collapse_head_partition xbl).
case E : (collapse_head l) => //; move: E.
set i := (w in _ :: w); case: i => //.
  by move=> _ []; move: xb => /[swap] -> /[swap] ->; rewrite lt_irreflexive.
move=> i j /collapse_head_neq /[swap] /[dup] /partition_consP [<-]; rewrite le_eqVlt.
move=> /orP [/eqP ->|]; rewrite ?eq_refl => // xi ib pibj pxij _ tv_eps.
apply: filter_app (nbhs_right_ge _). 
apply: filter_app (nbhs_right_lt xi).
have e20 : 0 < eps%:num/2 by [].
move/cvgrPdist_lt/(_ (eps%:num/2) e20):ctsf; apply: filter_app.
near=> t => fxt ti xt; have ? : a <= t by exact: (le_trans ax).
have ? : x <= b by apply: ltW; exact: (lt_le_trans xi).
have tb : t <= b by apply: ltW; exact: (lt_le_trans ti).
rewrite -fineB; first last.
  apply/bounded_variationP => //; apply: (bounded_variation_le bvf) => //.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
rewrite -(total_variation_concatE _ ax xt).
rewrite oppeD ?fin_num_adde_defl //; first last.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
have xtfin : TV x t f \is a fin_num.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
have tbfin : TV t b f \is a fin_num.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
rewrite addeA subee //; first last.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
rewrite sub0e fineN normrN ger0_norm; first last.
  rewrite fine_ge0 //; exact: total_variation_ge0.
move: (tv_eps); rewrite -(total_variation_concatE f _ tb) //.
pose r := [:: x, i & j].
have := part_split_pvar f pxij xt tb.
rewrite -lee_fin => /lt_le_trans /[apply].
have -> : part_split t [:: x, i & j] = (x :: t :: nil, [:: t, i & j]).
  by rewrite /part_split; rewrite ?ti ltNge xt /=.
rewrite /= -addeA -lte_subr_addr; first last.
  by rewrite fin_numD; apply/andP; split => //.
rewrite EFinD -lte_fin ?fineK // oppeD //= ?fin_num_adde_defl // opprK addeA. 
move/lt_trans; apply.
rewrite [x in (_ < x%:E)%E]splitr EFinD addeC lte_add2lE //. 
rewrite -addeA; apply: (@le_lt_trans _ _ (pvar [::x;t] f)%:E).
  rewrite gee_addl // sube_le0; apply: ereal_sup_ub. 
  exists (pvar [::t,i&j] f) => //; exists [::t,i&j] => //.
  by apply/partition_consP; split => //; apply: ltW.
  by rewrite /pvar /= big_seq1 /= distrC lte_fin.
Unshelve. all: by end_near. Qed.

Lemma neg_TV_right_continuous a x b (f : R -> R) :
  a <= x -> x < b ->
  bounded_variation a b f ->
  (f @ at_right x --> f x) ->
  (fine \o neg_tv a f @ at_right x --> fine (neg_tv a f x)).
Proof.
move=> ax ? bvf fcts; have xb : x <= b by exact: ltW. 
have xbfin : TV a x f \is a fin_num.
  by apply/bounded_variationP => //; apply: (bounded_variation_le bvf).
apply: fine_cvg; rewrite /neg_tv fineM // ?fin_numB ?xbfin //= EFinM.
under eq_fun => i do rewrite EFinN.
apply: cvg_trans; first (apply: cvgeMr => //); last exact: cvg_id. 
rewrite fineD // EFinB; apply: cvgeB => //.
  apply/ fine_cvgP; split; first exists (b-x).
  - by rewrite /= subr_gt0.
  - move=> t /= xtbx xt; have ? : a <= t.
      by apply: ltW; apply: (le_lt_trans ax).
    apply/bounded_variationP => //; apply: (bounded_variation_le bvf) => //. 
    move: xtbx; rewrite distrC ger0_norm ?subr_ge0; last by exact: ltW.
    by rewrite ltr_subr_addr -addrA [-_ + _]addrC subrr addr0 => /ltW.
  by apply: TV_right_continuous => //; last exact: bvf => //.
apply: cvg_comp; first exact: fcts.
apply/ fine_cvgP; split; first by near=> t => //.
by have -> : (fine \o EFin = id) by move=> ?; rewrite funeqE => ? /=.
Unshelve. all: by end_near. Qed.

Lemma pvarNE (l : seq R) f :  
  pvar l f = pvar (map (-%R) l) (f \o (-%R)).
Proof.
elim: l; first by rewrite /pvar /= !big_nil.
move=> a [|]; first by move=> _ /=; rewrite /pvar /= !big_nil.
by move=> w l IH; rewrite /= ?pvar_consE /= ?opprK; congr( _ + _).
Qed.

Lemma pvarNE2 (l : seq R) f :  
  pvar (map (-%R) l) f = pvar l (f \o (-%R)).
Proof.
have NE : (-%R) \o (-%R) = @id R.
  by apply: eq_fun => ?; rewrite opprK.
have compE g : g \o id = g by apply: eq_fun.
by rewrite (_ : f = f \o (-%R) \o (-%R)) -?pvarNE -compA NE compE.
Qed.

Lemma partition_rev a b l :
  partition a b l -> partition (-b) (-a) (rev (map (-%R) l)).
Proof.
elim: l a b => // => w [].
  by move=> /= _ ? ? [] <- <-; split.
move=> y l; set j := y :: l => IH a b /partition_consP [<-] ay yb pyb. 
have /(@partition_concat_tl _ _ _ _ (-y :: -a :: nil)) := IH _ _ pyb. 
rewrite /= rev_cons -cats1 ?rev_cons -?cats1; apply.
by split => //; repeat split => //; rewrite ler_opp2.
Qed.

Lemma pvar_cat a (l1 l2 : seq R) f :  
  pvar (l1 ++ a :: l2) f = pvar (l1 ++ [:: a]) f + pvar (a :: l2) f.
Proof.
elim: l1 a l2; first by move => ? ?; rewrite /= /pvar /= big_nil /= add0r.
move=> w []. 
  by move=> _ ? ? /=; rewrite ?pvar_consE /= /pvar /= big_nil /= -addrA add0r.
move=> y l1 IH a l2. 
by rewrite ?cat_cons ?pvar_consE IH ?cat_cons addrA.
Qed.

Lemma pvar_revE (l : seq R) f :  
  pvar l f = pvar (rev l) f.
Proof.
elim: l; first by rewrite /pvar /= !big_nil.
move=> a [|]; first by move=> _ /=; rewrite /pvar /= !big_nil.
move=> w l IH; rewrite pvar_consE; rewrite distrC IH.
rewrite ?rev_cons -?cats1 -catA [x in _ = x]pvar_cat addrC; congr (_ + _).
by rewrite pvar_consE /pvar big_nil addr0.
Qed.

Lemma variation_revE a b f: 
  variations (-b) (-a) (f \o [eta -%R]) = variations a b f.
Proof.
rewrite eqEsubset; split => ?.
  move=> [l] /partition_rev + <-; rewrite ?opprK => plrev.
  by rewrite -pvarNE2 pvar_revE; exists (rev (map (-%R) l)) => //.
have fNE : f = (f \o -%R) \o -%R.
  by apply: eq_fun => ?; rewrite /= opprK.
rewrite -{1}[a]opprK -{1}[b]opprK fNE.
move=> [l] /partition_rev + <-; rewrite ?opprK => plrev.
rewrite -pvarNE2 pvar_revE; exists (rev (map (-%R) l)) => //.
by rewrite -compA fNE; congr (_ _ ); apply: eq_fun => ?; rewrite /= ?opprK.
Qed.

Lemma total_variation_revE a b f: 
  TV a b f = TV (-b) (-a) (f \o (-%R)). 
Proof. by rewrite /total_variation -variation_revE. Qed.

Lemma at_left_at_rightP {T: topologicalType} (f : R -> T) x (z:T):
  f @ at_left x --> z <-> 
  f \o (-%R) @ at_right (-x) --> z. 
Proof.

suff -> : (- x)^'+ = (-%R) @ x^'-.
  by rewrite -?fmap_comp; under [_ \o _]eq_fun => ? do rewrite /= opprK.
rewrite eqEsubset /=; split.
  move=> E /= [r rpos xb]; exists r => //.
  move=> t /= xtr tx; apply: xb. 
    by rewrite /= -opprB opprK normrN addrC.
  by rewrite ltr_oppr opprK.
move=> E /= [r rpos xb]; exists r => //.
move=> t /= xtr tx; rewrite -[t]opprK; apply: xb. 
  by rewrite /= opprK -normrN opprD.
by rewrite ltr_oppl.
Qed.

Lemma TV_left_continuous a b x (f : R -> R) :
  a < x -> x <= b ->
  (f @ at_left x --> f x) ->
  bounded_variation a b f ->
  (fine \o TV a ^~ f @ at_left x --> fine (TV a x f)).
Proof.
move=> ax xb fNcts bvf.
apply/at_left_at_rightP; rewrite total_variation_revE.
have bvNf : bounded_variation (-b) (-a) (f \o -%R).
  by case:bvf=> M; rewrite -variation_revE => ?; exists M.
have bx : -b <= -x by rewrite ler_oppl opprK.
have xa : -x < -a by rewrite ltr_oppl opprK.
have ? : -x <= -a by apply: ltW.
have ? : Filter (nbhs (-x)^'+) by exact: at_right_proper_filter.
have -> : fine (TV (-x) (-a) (f \o -%R)) = 
    fine (TV (-b) (-a) (f \o -%R)) - fine (TV (-b) (-x) (f \o -%R)).
  apply/eqP; rewrite -subr_eq opprK addrC.
  rewrite -fineD ?total_variation_concatE //.
  - by apply/bounded_variationP => //; apply: (bounded_variation_le bvNf).
  - by apply/bounded_variationP => //; apply: (bounded_variation_le bvNf).
have /near_eq_cvg/cvg_trans : {near ((-x)^'+),
    (fun t => fine (TV (-b) (-a) (f \o -%R)) - fine (TV (-b) t (f\o-%R))) =1
    (fine \o (TV a)^~ f) \o -%R }.
  apply: filter_app (nbhs_right_lt xa).
  apply: filter_app (nbhs_right_ge _).
  near=> t => xt ta; have ? : -b <= t by exact: (le_trans bx).
  have ? : t <= -a by exact: ltW.
  apply/eqP; rewrite eq_sym -subr_eq opprK addrC.
  rewrite /= [TV a _ f]total_variation_revE opprK -fineD ?total_variation_concatE //.
  - by apply/bounded_variationP => //; apply: (bounded_variation_le bvNf) => //.
  - by apply/bounded_variationP => //; apply: (bounded_variation_le bvNf).
apply.
apply: cvgB; first exact: cvg_cst.
apply: (TV_right_continuous _ _ _ bvNf).
- by rewrite ler_oppl opprK //.
- by rewrite ltr_oppl opprK //.
by apply/at_left_at_rightP; rewrite /= opprK.
Unshelve. all: by end_near. Qed.

End bounded_variation.
Unshelve. all: by end_near. Qed.