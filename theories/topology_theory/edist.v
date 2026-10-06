(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order finmap ssralg ssrnum ssrint.
From mathcomp Require Import interval interval_inference archimedean.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import set_interval reals.
From mathcomp Require Import topology ereal.

(**md**************************************************************************)
(* # Extended distance function                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*                          edist == the extended distance function for a     *)
(*                                   pseudometric X, from X * X -> \bar R     *)
(*                    edist_inf A == the infimum of distances to the set A    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section pseudoMetricDist.
Context {R : realType} {X : pseudoMetricType R}.
Implicit Types r : R.

Definition edist (xy : X * X) : \bar R :=
  ereal_inf (EFin @` [set r | 0 < r /\ ball xy.1 r xy.2]).

Lemma edist_ge0 (xy : X * X) : (0 <= edist xy)%E.
Proof.
by apply: le_ereal_inf_tmp => z [+ []] => _/posnumP[r] _ <-; rewrite lee_fin.
Qed.
Hint Resolve edist_ge0 : core.

Lemma edist_neqNy (xy : X * X) : (edist xy != -oo)%E.
Proof. by rewrite -lteNye (@lt_le_trans _ _ 0%E). Qed.
Hint Resolve edist_neqNy : core.

Lemma edist_lt_ball r (xy : X * X) : (edist xy < r%:E)%E -> ball xy.1 r xy.2.
Proof.
case/ereal_inf_lt => ? [+ []] => _/posnumP[eps] bxye <-; rewrite lte_fin.
by move/ltW/le_ball; exact.
Qed.

Lemma edist_fin r (xy : X * X) :
  0 < r -> ball xy.1 r xy.2 -> (edist xy <= r%:E)%E.
Proof.
move: r => _/posnumP[r] => ?; rewrite -(ereal_inf1 r%:num%:E) ereal_inf_le_tmp//.
by move=> ? -> /=; exists r%:num; split.
Qed.

Lemma edist_pinftyP (xy : X * X) :
  (edist xy = +oo)%E <-> (forall r, 0 < r -> ~ ball xy.1 r xy.2).
Proof.
split.
  move/ereal_inf_pinfty => xrb r rpos rb; move: (ltry r); rewrite ltey => /eqP.
  by apply; apply: xrb; exists r.
rewrite /edist=> nrb; suff -> : [set r | 0 < r /\ ball xy.1 r xy.2] = set0.
  by rewrite image_set0 ereal_inf0.
by rewrite -subset0 => r [?] rb; apply: nrb; last exact: rb.
Qed.

Lemma edist_finP (xy : X * X) :
  (edist xy \is a fin_num)%E <-> exists2 r, 0 < r & ball xy.1 r xy.2.
Proof.
rewrite ge0_fin_numE ?edist_ge0// ltey.
rewrite -(rwP (negPP eqP)); apply/iff_not2; rewrite not_notE.
apply: (iff_trans (edist_pinftyP _)); apply: (iff_trans _ (forall2NP _ _)).
by under eq_forall => ? do rewrite implyE.
Qed.

Lemma edist_fin_open : open [set xy : X * X | edist xy \is a fin_num].
Proof.
move=> z /= /edist_finP [] _/posnumP[r] bzr.
exists (ball z.1 r%:num, ball z.2 r%:num); first by split; exact: nbhsx_ballx.
case=> a b [bza bzb]; apply/edist_finP; exists (r%:num + r%:num + r%:num) => //.
exact/(ball_triangle _ bzb)/(ball_triangle _ bzr)/ball_sym.
Qed.

Lemma edist_fin_closed : closed [set xy : X * X | edist xy \is a fin_num].
Proof.
move=> z /= /(_ (ball z 1)) []; first exact: nbhsx_ballx.
move=> w [/edist_finP [] _/posnumP[r] babr [bz1w1 bz2w2]]; apply/edist_finP.
exists (1 + (r%:num + 1)) => //.
exact/(ball_triangle bz1w1)/(ball_triangle babr)/ball_sym.
Qed.

Lemma edist_pinfty_open : open [set xy : X * X | edist xy = +oo]%E.
Proof.
rewrite -closedC; have := edist_fin_closed; congr (_ _).
by rewrite eqEsubset; split => z; rewrite /= ?ge0_fin_numE// ltey => /eqP.
Qed.

Lemma edist_sym (x y : X) : edist (x, y) = edist (y, x).
Proof. by rewrite /edist /=; under eq_fun do rewrite ball_symE. Qed.

Lemma edist_triangle (x y z : X) :
  (edist (x, z) <= edist (x, y) + edist (y, z))%E.
Proof.
have [->|] := eqVneq (edist (x, y)) +oo%E; first by rewrite addye ?leey.
have [->|] := eqVneq (edist (y, z)) +oo%E; first by rewrite addey ?leey.
rewrite -?ltey -?ge0_fin_numE//.
move=> /edist_finP [_/posnumP[r2] /= yz] /edist_finP [_/posnumP[r1] /= xy].
have [|] := eqVneq (edist (x, z)) +oo%E.
  move/edist_pinftyP /(_ (r1%:num + r2%:num) _) => -[//|].
  exact: (ball_triangle xy).
rewrite -ltey -ge0_fin_numE// => /[dup] xzfin.
move/edist_finP => [_/posnumP[del] /= xz].
rewrite /edist /= ?ereal_inf_EFin.
- by exists 0 => ? /= [/ltW].
- by exists (r1%:num + r2%:num); split => //; apply: (ball_triangle xy).
- by exists 0 => ? /= [/ltW].
- by exists r1%:num; split.
- by exists 0 => ? /= [/ltW].
- by exists r2%:num; split.
rewrite -EFinD lee_fin -inf_sumE //.
- by split; [exists r1%:num; split| exists 0 => ? /= [/ltW]].
- by split; [exists r2%:num; split| exists 0 => ? /= [/ltW]].
apply: lb_le_inf.
  by exists (r1%:num + r2%:num); exists r1%:num => //; exists r2%:num.
move=> ? [+ []] => _/posnumP[p] xpy [+ []] => _/posnumP[q] yqz <-.
apply: ge_inf; first by exists 0 => ? /= [/ltW].
by split => //; exact: (ball_triangle xpy).
Qed.

Lemma edist_continuous : continuous edist.
Proof.
move=> [x y]; have [pE U /= Upinf|] := eqVneq (edist (x, y)) +oo%E.
  rewrite nbhs_simpl /=; apply (@filterS _ _ _ [set xy | edist xy = +oo]%E).
    by move=> z /= ->; apply: nbhs_singleton; move: pE Upinf => ->.
  by apply: open_nbhs_nbhs; split => //; exact: edist_pinfty_open.
rewrite -ltey -ge0_fin_numE// => efin.
rewrite /continuous_at -[edist (x, y)]fineK//; apply: cvg_EFin.
  by have := edist_fin_open efin; apply: filter_app; near=> w.
apply/(@metricType_numDomainType.cvgrPdist_le _ R^o) => _/posnumP[eps]/=.
suff: \forall t \near (nbhs x, nbhs y),
   @mdist _ R^o (fine (edist (x, y))) (fine (edist t)) <= eps%:num.
  by [].
rewrite -near2_pair; near=> a b => /=.
have abxy : (edist (a, b) <= edist (x, a) + edist (x, y) + edist (y, b))%E.
  rewrite (edist_sym x a) -addeA.
  by rewrite (le_trans (@edist_triangle _ x _)) ?leeD ?edist_triangle.
have xyab : (edist (x, y) <= edist (x, a) + edist (a, b) + edist (y, b))%E.
  rewrite (edist_sym y b) -addeA.
  by rewrite (le_trans (@edist_triangle _ a _))// ?leeD// ?edist_triangle.
have xafin : edist (x, a) \is a fin_num.
  by apply/edist_finP; exists 1 =>//; near: a; exact: nbhsx_ballx.
have ybfin : edist (y, b) \is a fin_num.
  by apply/edist_finP; exists 1 =>//; near: b; exact: nbhsx_ballx.
have abfin : edist (a, b) \is a fin_num.
  by rewrite ge0_fin_numE// (le_lt_trans abxy) ?lte_add_pinfty// -ge0_fin_numE.
have xyabfin : (edist (x, y) - edist (a, b))%E \is a fin_num
  by rewrite fin_numB abfin efin.
rewrite /mdist/= distrC.
rewrite -fineB// -fine_abse// -lee_fin fineK ?abse_fin_num//.
rewrite (@le_trans _ _ (edist (x, a) + edist (y, b))%E)//; last first.
  by rewrite [eps%:num]splitr/= EFinD leeD//; apply: edist_fin => //=;
       [near: a | near: b]; exact: nbhsx_ballx.
have [ab_le_xy|/ltW xy_le_ab] := leP (edist (a, b)) (edist (x, y)).
  by rewrite gee0_abs ?subre_ge0// leeBlDr// addeAC.
rewrite lee0_abs ?sube_le0// oppeB ?fin_num_adde_defr//.
by rewrite addeC leeBlDr// addeAC.
Unshelve. all: end_near. Qed.

Lemma edist_closeP x y : close x y <-> edist (x, y) = 0%E.
Proof.
rewrite ball_close; split=> [bxy|edist0 eps]; first last.
  by apply: (@edist_lt_ball _ (x, y)); rewrite edist0.
case: ltgtP (edist_ge0 (x, y)) => // dpos _.
have xxfin : edist (x, y) \is a fin_num.
  rewrite ge0_fin_numE// (@le_lt_trans _ _ 1%:E) ?ltey// edist_fin//.
  exact: bxy (widen_itv 1%:itv).
have dpose : fine (edist (x, y)) > 0 by rewrite -lte_fin fineK.
pose eps := PosNum dpose.
have : (edist (x, y) <= (eps%:num / 2)%:E)%E.
  apply: ereal_inf_lbound; exists (eps%:num / 2) => //; split => //.
  exact: (bxy (eps%:num / 2)%:pos).
apply: contra_leP => _.
by rewrite /= EFinM fineK// lte_pdivrMr// lte_pmulr// lte1n.
Qed.

Lemma edist_refl x : edist (x, x) = 0%E. Proof. exact/edist_closeP. Qed.

Lemma edist_closel x y z : close x y -> edist (x, z) = edist (y, z).
Proof.
move=> /edist_closeP xy0; apply: le_anti; apply/andP; split.
  by rewrite -[edist (y, z)]add0e -xy0 edist_triangle.
by rewrite -[edist (x, z)]add0e -xy0 [edist (x, y)]edist_sym edist_triangle.
Qed.

End pseudoMetricDist.
#[global]
Hint Extern 0 (is_true (0%R <= edist _)%E) => solve [apply: edist_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist _ != -oo%E)) => solve [apply: edist_neqNy] : core.

Section edist_inf.
Context {R : realType} {T : pseudoMetricType R} (A : set T).

Definition edist_inf z := ereal_inf [set edist (z, a) | a in A].

Lemma edist_inf_ge0 w : (0 <= edist_inf w)%E.
Proof. by apply: le_ereal_inf_tmp => ? /= [? ? <-]. Qed.
Hint Resolve edist_inf_ge0 : core.

Lemma edist_inf_neqNy w : (edist_inf w != -oo)%E.
Proof. by rewrite -lteNye (@lt_le_trans _ _ 0%E). Qed.
Hint Resolve edist_inf_neqNy : core.

Lemma edist_inf_triangle x y : (edist_inf x <= edist (x, y) + edist_inf y)%E.
Proof.
have [A0|/set0P[a0 Aa0]] := eqVneq A set0.
  by rewrite /edist_inf A0 ?image_set0 ?ereal_inf0 addey.
have [fyn|] := boolP (edist_inf y \is a fin_num); first last.
  by rewrite ge0_fin_numE// ?ltey negbK => /eqP->; rewrite addey ?leey.
have [xyfin|] := boolP (edist (x, y) \is a fin_num); first last.
  by rewrite ge0_fin_numE// ?ltey // negbK => /eqP->; rewrite addye ?leey.
apply/lee_addgt0Pr => _/posnumP[eps].
have [//|? [a Aa <-] yaeps] := @lb_ereal_inf_adherent R _ eps%:num _ fyn.
apply: le_trans.
  by apply: (@ereal_inf_lbound _ _ (edist (x, a))); exists a.
apply: le_trans; first exact: (@edist_triangle _ _ _ y).
by rewrite -addeA leeD2lE // ltW.
Qed.

Lemma edist_inf_continuous : continuous edist_inf.
Proof.
move=> z; have [A0|/= /set0P[a0 Aa0]] := eqVneq A set0.
  rewrite /edist_inf A0.
  under eq_fun do rewrite image_set0 ereal_inf0.
  exact: cvg_cst.
have [] := eqVneq (edist_inf z) +oo%E.
  move=> /[dup] fzp /ereal_inf_pinfty => zAp U /= Ufz.
  have : nbhs z (ball z 1) by exact: nbhsx_ballx.
  apply: filter_app; near_simpl; near=> w => bz1w.
  suff /= -> : (edist_inf w) = +oo%E by apply: nbhs_singleton; rewrite -fzp.
  apply/ereal_inf_pinfty => r [a Aa] war; apply/zAp; exists a => //.
  have /gee0P[|[r' r'pos war']] := edist_ge0 (w, a).
    by rewrite war => ->; apply: zAp; exists a.
  have := @edist_triangle _ _ z w a; rewrite war'; apply: contra_leP => _.
  rewrite (@le_lt_trans _ _ (1 + r'%:E)%E) ?leeD2r ?edist_fin//.
  by rewrite -EFinD [edist (z, a)]zAp ?ltey //; exists a.
rewrite -ltey -ge0_fin_numE ?edist_inf_ge0 // => fz_fin.
rewrite /continuous_at -[edist_inf z]fineK //; apply/fine_cvgP.
have fwfin : \forall w \near z, edist_inf w \is a fin_num.
  (have : nbhs z (ball z 1) by exact: nbhsx_ballx); apply: filter_app.
  near=> t => bz1; rewrite ge0_fin_numE ?edist_inf_ge0 //.
  rewrite (le_lt_trans (edist_inf_triangle _ z))//.
  rewrite -ge0_fin_numE ?adde_ge0 ?edist_inf_ge0 //.
  rewrite fin_numD fz_fin andbT; apply/edist_finP; exists 1 => //.
  exact/ball_sym.
split => //; apply/(@metricType_numDomainType.cvgrPdist_le _ R^o) => _/posnumP[eps].
have : nbhs z (ball z eps%:num) by exact: nbhsx_ballx.
apply: filter_app; near_simpl; move: fwfin; apply: filter_app.
near=> t => tfin /= /[dup] ?.
have ztfin : edist (z, t) \is a fin_num by apply/edist_finP; exists eps%:num.
move=> /(@edist_fin _ _ _ (z, t)) - /(_ trivial).
rewrite -[edist (z, t)]fineK ?lee_fin //; apply: le_trans.
rewrite ler_norml; apply/andP; split.
  rewrite lerBrDr addrC lerBlDr addrC -fineD //.
  rewrite -lee_fin ?fineK // ?fin_numD ?ztfin ?fz_fin // edist_sym.
  by rewrite edist_sym; exact: edist_inf_triangle.
rewrite lerBlDr -fineD // -lee_fin ?fineK // ?fin_numD ?tfin ?ztfin //.
by rewrite edist_sym; exact: edist_inf_triangle.
Unshelve. all: by end_near. Qed.

Lemma edist_inf0 a : A a -> edist_inf a = 0%E.
Proof.
move=> Aa; apply: le_anti; apply/andP; split; last exact: edist_inf_ge0.
by apply: ereal_inf_lbound; exists a => //; exact: edist_refl.
Qed.

End edist_inf.
#[global]
Hint Extern 0 (is_true (0 <= edist_inf _ _)%E) =>
  solve [apply: edist_inf_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist_inf _ _ != -oo%E)) =>
  solve [apply: edist_inf_neqNy] : core.
