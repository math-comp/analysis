(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals real_interval.
From mathcomp Require Import topology function_spaces tvs num_normedtype.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module.

(**md**************************************************************************)
(* # Urysohn's lemma                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*                          edist == the extended distance function for a     *)
(*                                   pseudometric X, from X * X -> \bar R     *)
(*                    edist_inf A == the infimum of distances to the set A    *)
(*          uniform_separator A B == there is a suitable uniform space and    *)
(*                                   entourage separating A and B             *)
(*                    Urysohn A B == a continuous function T -> [0,1] which   *)
(*                                   separates A and B when                   *)
(*                                   `uniform_separator A B`                  *)
(*       completely_regular_space == a space where points and closed sets can *)
(*                                   be separated by a function into R        *)
(*  completely_regular_uniformity == equips a completely_regular_space with   *)
(*                                   the uniformity induced by continuous     *)
(*                                   functions into the reals                 *)
(*                                   note this uniformity is always the only  *)
(*                                   choice, so its placed in a module        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

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
rewrite -(rwP (negPP eqP)); apply/iff_not2; rewrite notE.
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
rewrite /edist /= ?ereal_inf_EFin; first last.
- by exists (r1%:num + r2%:num); split => //; apply: (ball_triangle xy).
- by exists 0 => ? /= [/ltW].
- by exists r1%:num; split.
- by exists 0 => ? /= [/ltW].
- by exists r2%:num; split.
- by exists 0 => ? /= [/ltW].
rewrite -EFinD lee_fin -inf_sumE //; first last.
- by split; [exists r2%:num; split| exists 0 => ? /= [/ltW]].
- by split; [exists r1%:num; split| exists 0 => ? /= [/ltW]].
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
apply/cvgrPdist_le => _/posnumP[eps].
suff: \forall t \near (nbhs x, nbhs y),
   `|fine (edist (x, y)) - fine (edist t)| <= eps%:num by [].
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
split => //; apply/cvgrPdist_le => _/posnumP[eps].
have : nbhs z (ball z eps%:num) by exact: nbhsx_ballx.
apply: filter_app; near_simpl; move: fwfin; apply: filter_app.
near=> t => tfin /= /[dup] ?.
have ztfin : edist (z, t) \is a fin_num by apply/edist_finP; exists eps%:num.
move=> /(@edist_fin _ _ _ (z, t)) - /(_ trivial).
rewrite -[edist (z, t)]fineK ?lee_fin //; apply: le_trans.
rewrite ler_norml; apply/andP; split.
  rewrite lerBrDr addrC lerBlDr  addrC -fineD //.
  rewrite -lee_fin ?fineK // ?fin_numD ?ztfin ?fz_fin // edist_sym.
  exact: edist_inf_triangle.
rewrite lerBlDr -fineD // -lee_fin ?fineK // ?fin_numD ?tfin ?ztfin //.
exact: edist_inf_triangle.
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

Section urysohn_separator.
Context {T : uniformType} {R : realType}.
Context (A B : set T) (E : set (T * T)).
Hypothesis entE : entourage E.
Hypothesis AB0 : A `*` B `&` E = set0.

Local Notation T' := [the pseudoMetricType R of gauge.type entE].

Local Lemma urysohn_separation : exists (f : T -> R),
  [/\ continuous f, range f `<=` `[0, 1],
      f @` A `<=` [set 0] & f @` B `<=` [set 1] ].
Proof.
have [eps exy] : exists (eps : {posnum R}),
    forall (x y : T'), A x -> B y -> ~ ball x eps%:num y.
  have : @entourage T' E by exists O => /=.
  rewrite -entourage_ballE; case=> _/posnumP[eps] epsdiv; exists eps.
  move=> x y Ax By bxy; have divxy := epsdiv (x, y) bxy.
  by have : set0 (x, y) by rewrite -AB0; split.
have [->|/set0P[a A0]] := eqVneq A set0.
  exists (fun=> 1); split; first by move => ?; exact: cvg_cst.
  - by move=> ? [? _ <-]; rewrite /= in_itv /=; apply/andP; split => //.
  - by rewrite image_set0.
  - by move=> ? [? ? <-].
have dfin x : @edist_inf R T' A x \is a fin_num.
  rewrite ge0_fin_numE ?edist_inf_ge0 //; apply: le_lt_trans.
    by apply: ereal_inf_lbound; exists a.
  rewrite -ge0_fin_numE ?edist_ge0 //; apply/edist_finP => /=; exists 2 => //.
  exact: countable_uniform.countable_uniform_bounded.
pose f' := (fun z => fine (@edist_inf R T' A z)) \min (fun=> eps%:num).
pose f z := (f' z)/eps%:num; exists f; split.
- move=> x; rewrite /f; apply: (@cvgM R T (nbhs x)); last exact: cvg_cst.
  suff : {for x, continuous (f' : T' -> R)}.
    move=> Q U; rewrite nbhs_simpl /= => f'U.
    have [J /(gauge.gauge_ent entE) entJ/filterS] := Q _ f'U; apply.
    by rewrite nbhs_simpl /= -nbhs_entourageE /=; exists J.
  apply: continuous_min; last by apply: cvg_cst; exact: nbhs_filter.
  apply: fine_cvg; first exact: nbhs_filter.
  rewrite fineK //; first exact: edist_inf_continuous.
- move=> _ [x _ <-]; rewrite set_itvE /=; apply/andP; split.
    by rewrite /f divr_ge0 // /f' /= le_min fine_ge0//= edist_inf_ge0.
  by rewrite /f ler_pdivrMr // mul1r /f' /= /minr; case: ltP => // /ltW.
- by move=> ? [z Az] <-; rewrite /f/f' /= edist_inf0 // /minr fine0 ifT ?mul0r.
- move=> ? [b Bb] <-; rewrite /f /f'/= /minr/=.
  case: ltP => //; rewrite ?divrr // ?unitf_gt0 // -lte_fin fineK//.
  move => /ereal_inf_lt [_ [z Az <-]] ebz; have [] := exy _ _ Az Bb.
  exact/ball_sym/(@edist_lt_ball R T' _ (b, z)).
Qed.

End urysohn_separator.

Section topological_urysohn_separator.
Context {T : topologicalType} {R : realType}.

Definition uniform_separator (A B : set T) :=
  exists (uT : @Uniform.axioms_ T^o) (E : set (T * T)),
    let UT := Uniform.Pack uT in [/\
      @entourage UT E, A `*` B `&` E = set0 &
      (forall x, @nbhs UT UT x `<=` @nbhs T T x)].

Local Lemma Urysohn' (A B : set T) : exists (f : T -> R),
    [/\ continuous f,
    range f `<=` `[0, 1]
    & uniform_separator A B ->
    f @` A `<=` [set 0] /\ f @` B `<=` [set 1]].
Proof.
have [[? [E [entE ABE0 coarseT]]]|nP] := pselect (uniform_separator A B).
  have [f] := @urysohn_separation _ R _ _ _ entE ABE0.
  by case=> ctsf ? ? ?; exists f; split => // ? ? /= ?; apply/coarseT/ctsf.
exists (fun=>1); split => //; first by move=> ?; exact: cvg_cst.
by move=> ? [? _ <-]; rewrite /= in_itv /=; apply/andP; split => //.
Qed.

Definition Urysohn (A B : set T) : T -> R := projT1 (cid (Urysohn' A B)).

Section urysohn_facts.

Lemma Urysohn_continuous (A B : set T) : continuous (Urysohn A B).
Proof. by have [] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_range (A B : set T) : range (Urysohn A B) `<=` `[0, 1].
Proof. by have [] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_sub0 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` A `<=` [set 0].
Proof. by move=> eE; have [_ _ /(_ eE)[]] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_sub1 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` B `<=` [set 1].
Proof. by move=> eE; have [_ _ /(_ eE)[]] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_eq0 (A B : set T) :
  uniform_separator A B -> A !=set0 -> Urysohn A B @` A = [set 0].
Proof.
move=> eE Aa; have [_ _ /(_ eE)[As0 _]] := projT2 (cid (@Urysohn' A B)).
rewrite eqEsubset; split => // ? ->; case: Aa => a ?; exists a => //.
by apply: As0; exists a.
Qed.

Lemma Urysohn_eq1 (A B : set T) :
  uniform_separator A B -> (B !=set0) -> (Urysohn A B) @` B = [set 1].
Proof.
move=> eE Bb; have [_ _ /(_ eE)[_ Bs0]] := projT2 (cid (@Urysohn' A B)).
rewrite eqEsubset; split => // ? ->; case: Bb => b ?; exists b => //.
by apply: Bs0; exists b.
Qed.

End urysohn_facts.
End topological_urysohn_separator.

Lemma uniform_separatorW {T : uniformType} (A B : set T) :
    (exists2 E, entourage E & A `*` B `&` E = set0) ->
  uniform_separator A B.
Proof. by case=> E entE AB0; exists (Uniform.class T), E; split => // ?. Qed.

Section Urysohn.
Local Open Scope relation_scope.
Context {T : topologicalType}.
Hypothesis normalT : normal_space T.
Section normal_uniform_separators.
Context (A : set T).

(* Urysohn's lemma guarantees a continuous function : T -> R
   where "f @` A = [set 0]" and "f @` B = [set 1]".
   The idea is to leverage countable_uniformity to build that function
   rather than construct it directly.

   The bulk of the work is building a uniformity to measure "distance from A".
   Each pair of "nested" U,V induces an approximation "apxU".
                 A-------)] U
                 A----------------) V (points near A)
                          (------------  ~`closure U (points far from A)
   These make the sub-basis for a filter. That filter is a uniformity
   because normality lets us split

                 A------)] U
                 A-----------)]  V'
                         (---------------  ~`closure U
                 A----------------) V
                              (---------  ~` closure V'
   and (U,V') + (V', V) splits the entourage of (U,V). This uniform space is not
   neccesarily a pseudometric. So we find an entourage which divides A and B,
   then the gauge pseudometric gives us what we want.
*)

Let apxU (UV : set T * set T) : set (T * T) :=
  (UV.2 `*` UV.2) `|` (~` closure UV.1 `*` ~` closure UV.1).

Let nested (UV : set T * set T) :=
  [/\ open UV.1, open UV.2, A `<=` UV.1 & closure UV.1 `<=`UV.2].

Let ury_base := [set apxU UV | UV in nested].

Local Lemma ury_base_refl E : ury_base E -> diagonal `<=` E.
Proof.
case; case=> L R [_ _ _ /= LR] <- [? x /= /diagonalP ->].
case: (pselect (R x)); first by left.
by move/subsetC: LR => /[apply] => ?; right.
Qed.

Local Lemma ury_base_inv E : ury_base E -> ury_base E^-1.
Proof.
case; case=> L R ? <-; exists (L, R) => //.
by rewrite eqEsubset; split => //; (case=> x y [] [? ?]; [left| right]).
Qed.

Local Lemma ury_base_split E : ury_base E ->
  exists E1 E2, [/\ ury_base E1, ury_base E2 &
                    (E1 `&` E2) \; (E1 `&` E2) `<=` E].
Proof.
case; case => L R [/= oL oR AL cLR <-].
have [R' []] : exists R', [/\ open R', closure L `<=` R' & closure R' `<=` R].
  have := @normalT (closure L) (@closed_closure T L).
  case/(_ R); first by move=> x /cLR ?; apply: open_nbhs_nbhs.
  move=> V /set_nbhsP [U] [? ? ? cVR]; exists U; split => //.
  by apply: (subset_trans _ cVR); exact: closure_subset.
move=> oR' cLR' cR'R; exists (apxU (L, R')), (apxU (R', R)).
split; first by exists (L, R').
  exists (R', R) => //; split => //; apply: (subset_trans AL).
  by apply: (subset_trans _ cLR'); exact: subset_closure.
case=> x z /= [y [+ +] []].
(do 4 (case; case=> /= ? ?)); try (by left); try (by right);
  match goal with nG : (~ closure ?S ?y), G : ?S ?y |- _ =>
    by move/subset_closure: G
  end.
Qed.

Let ury_unif := smallest Filter ury_base.

Instance ury_unif_filter : Filter ury_unif.
Proof. exact: smallest_filter_filter. Qed.

Local Lemma ury_unif_refl E : ury_unif E -> diagonal `<=` E.
Proof.
by move/(_ (globally diagonal)); apply; split;
  [exact: globally_filter|exact: ury_base_refl].
Qed.

Local Lemma ury_unif_inv E : ury_unif E -> ury_unif E^-1.
Proof.
move=> ufE F [/filter_inv FF urF]; have [] := ufE [set V^-1 | V in F].
  split => // K /ury_base_inv/urF /= ?; exists (K^-1)%classic => //.
  by rewrite set_prod_invK.
by move=> R FR <-; rewrite set_prod_invK.
Qed.

Local Lemma ury_unif_split_iter E n :
  filterI_iter ury_base n E -> exists2 K : set (T * T),
    filterI_iter ury_base n.+1 K & K \; K `<=` E.
Proof.
elim: n E; first move=> E [].
- move=> ->; exists setT => //; exists setT; first by left.
  by exists setT; rewrite ?setIT; first by left.
- move=> /[dup] /ury_base_split [E1 [E2] [? ? ? ?]]; exists (E1 `&` E2) => //.
  by (exists E1; first by right); exists E2; first by right.
move=> n IH E /= [E1 /IH [F1 F1n1 F1E1]] [E2 /IH [F2 F2n1 F2E2]] E12E.
exists (F1 `&` F2); first by exists F1 => //; exists F2.
move=> /= [x z ] [y /= [K1xy K2xy] [K1yz K2yz]]; rewrite -E12E; split.
  by apply: F1E1; exists y.
by apply: F2E2; exists y.
Qed.

Local Lemma ury_unif_split E : ury_unif E ->
  exists2 K, ury_unif K & K \; K `<=` E.
Proof.
rewrite /ury_unif filterI_iterE; case=> G [n _] /ury_unif_split_iter [].
move=> K SnK KG GE; exists K; first by exists K => //; exists n.+1.
exact: (subset_trans _ GE).
Qed.

Local Lemma ury_unif_covA E : ury_unif E -> A `*` A `<=` E.
Proof.
rewrite /ury_unif filterI_iterE; case=> G [n _] sG /(subset_trans _); apply.
elim: n G sG.
  move=> g [-> //| [[P Q]]] [/= _ _ AP cPQ <-] [x y] [/= /AP ? ?].
  by left; split => //=; apply/cPQ/subset_closure => //; exact: AP.
by move=> n IH G [R] /IH AAR [M] /IH AAM <- z; split; [exact: AAR | exact: AAM].
Qed.

Definition urysohnType : Type := T.

HB.instance Definition _ := Choice.on urysohnType.

HB.instance Definition _ :=
  isUniform.Build urysohnType ury_unif_filter ury_unif_refl ury_unif_inv
  ury_unif_split.
HB.instance Definition _ {p : Pointed T} := Pointed.copy urysohnType (Pointed.Pack p).

Lemma normal_uniform_separator (B : set T) :
  closed A -> closed B -> A `&` B = set0 -> uniform_separator A B.
Proof.
move=> clA clB AB0; have /(_ (~`B))[x Ax|] := normalT clA.
  apply: open_nbhs_nbhs; split => //.
  - exact/closed_openC.
  - by move: x Ax; apply/ disjoints_subset.
move=> V /set_nbhsP [U [oU AU UV]] cVcb.
exists (Uniform.class urysohnType), (apxU (U, ~` B)); split => //.
- move=> ?; apply:sub_gen_smallest; exists (U, ~`B) => //; split => //=.
    exact/closed_openC.
  by move: UV => /closure_subset/subset_trans; apply.
- rewrite eqEsubset; split; case=> // a b [/=[Aa Bb] [[//]|]].
  by have /subset_closure ? := AU _ Aa; case.
move=> x ? [E gE] /(@filterS T); apply; move: gE.
rewrite /= /ury_unif filterI_iterE; case => K /= [i _] /= uiK KE.
suff : @nbhs T T x [set y | K (x, y)] by apply: filterS => y /KE/xsectionP.
elim: i K uiK {E KE}; last by move=> ? H ? [N] /H ? [M] /H ? <-; apply: filterI.
move=> K [->|]; first exact: filterT.
move=> [[/= P Q] [/= oP oQ AP cPQ <-]]; rewrite /apxU /=.
set M := [set y | _ \/ _].
have [Qx|nQx] := pselect (Q x); first last.
  suff -> : M = ~` closure P.
    apply: open_nbhs_nbhs; split; first exact/closed_openC/closed_closure.
    by move/cPQ.
  rewrite eqEsubset /M; split => z; first by do 2!case.
  by move=> ?; right; split => // /cPQ.
have [nPx|cPx] := pselect (closure P x).
  suff -> : M = Q by apply: open_nbhs_nbhs; split.
  rewrite eqEsubset /M; split => z; first by do 2!case.
  by move=> ?; left; split.
suff -> : M = setT by exact: filterT.
rewrite eqEsubset; split => // z _.
by have [Qz|/(subsetC cPQ)] := pselect (Q z); constructor.
Qed.

End normal_uniform_separators.
End Urysohn.

Lemma uniform_separatorP {T : topologicalType} {R : realType} (A B : set T) :
  uniform_separator A B <->
  exists (f : T -> R), [/\ continuous f, range f `<=` `[0, 1],
                           f @` A `<=` [set 0] & f @` B `<=` [set 1]].
Proof.
split; first do [move=> ?; exists (Urysohn A B); split].
- exact: Urysohn_continuous.
- exact: Urysohn_range.
- exact: Urysohn_sub0.
- exact: Urysohn_sub1.
case=> f [ctsf f01 fA0 fB1].
pose T' : uniformType := weak_topology f.
exists (Uniform.class T'), ([set xy | ball (f xy.1) 1 (f xy.2)]); split.
- exists [set xy | ball xy.1 1 xy.2]; last by case.
  by rewrite -entourage_ballE; exists 1 => //=.
- rewrite -subset0 => -[a b [[/= Aa Bb]]].
  by rewrite (imsub1 fA0)// (imsub1 fB1)// /ball/= sub0r normrN normr1 ltxx.
- move=> x U [V [[W oW <- /=]]] ? /filterS; apply.
  by apply: ctsf; exact: open_nbhs_nbhs.
Qed.

Section normalP.
Context {R : realType} {T : topologicalType}.

(* Ideally, R should be an instance of realType here,
   rather than a section variable. *)
Let normal_spaceP : [<->
  (* 0 *) normal_space T;
  (* 1 *) forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    uniform_separator A B;
  (* 2 *) forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0] ].
Proof.
tfae; first by move=> ?; exact: normal_uniform_separator.
- move=> + A B clA clB AB0 => /(_ _ _ clA clB AB0) /(@uniform_separatorP _ R).
  case=> f [cf f01 /imsub1P/subset_trans fa0 /imsub1P/subset_trans fb1].
  exists (f@^-1` `]-1, 1/2[), (f @^-1` `]1/2, 2[); split.
  + by apply: open_comp; [|exact: interval_open].
  + by apply: open_comp; [|exact: interval_open].
  + by apply: fa0 => x/= ->; rewrite (@in_itv _ R)/=; apply/andP; split.
  + apply: fb1 => x/= ->; rewrite (@in_itv _ R)/= ltr_pdivrMr// mul1r.
    by rewrite ltr1n.
  + rewrite -preimage_setI ?set_itvoo -subset0 => t [] /andP [_ +] /andP [+ _].
    by move=> /lt_trans /[apply]; rewrite ltxx.
move=> + A clA B /set_nbhsP [C [oC AC CB]].
have AC0 : A `&` ~` C = set0 by apply/disjoints_subset; rewrite setCK.
case/(_ _ _ clA (open_closedC oC) AC0) => U [V] [oU oV AU nCV UV0].
exists (~` closure V).
  apply/set_nbhsP; exists U; split => //.
  apply/subsetCr; have := open_closedC oU; rewrite closure_id => ->.
  by apply/closure_subset/disjoints_subset; rewrite setIC.
apply/(subset_trans _ CB)/subsetCP; apply: (subset_trans nCV).
apply/subsetCr; have := open_closedC oV; rewrite closure_id => ->.
exact/closure_subset/subsetC/subset_closure.
Qed.

Lemma normal_openP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0].
Proof. exact: (normal_spaceP 0%N 2%N). Qed.

Lemma normal_separatorP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  uniform_separator A B.
Proof. exact: (normal_spaceP 0%N 1%N). Qed.

End normalP.

Section completely_regular.
Context {R : realType}.

(**md This is equivalent to uniformizable. Note there is a subtle
   distinction between being uniformizable and being uniformType.
   There is often more than one possible uniformity, and being a
   uniformType has a specific one.

   If you don't care, you can use the `completely_regular_uniformity.type`
   which builds the uniformity.
*)
Definition completely_regular_space (T : topologicalType) :=
  forall (a : T) (B : set T), closed B -> ~ B a -> uniform_separator [set a] B.

Lemma point_uniform_separator {T : uniformType} (x : T) (B : set T) :
  closed B -> ~ B x -> uniform_separator [set x] B.
Proof.
move=> clB nBx; have : open (~` B) by rewrite openC.
rewrite openE => /(_ _ nBx); rewrite /interior /= -nbhs_entourageE.
case=> E entE EnB.
pose T' : pseudoMetricType R := gauge.type entE.
exists (Uniform.class T); exists E; split => //; last by move => ?.
by rewrite -subset0 => -[? w [/= [-> ? /xsectionP ?]]]; exact: (EnB w).
Qed.

Lemma uniform_completely_regular {T : uniformType} :
  @completely_regular_space T.
Proof. by move=> x B clB Bx; exact: point_uniform_separator. Qed.

Lemma normal_completely_regular {T : topologicalType} :
  normal_space T -> accessible_space T -> completely_regular_space T.
Proof.
move/normal_separatorP => + /accessible_closed_set1 cl1 x A ? ?; apply => //.
by apply/disjoints_subset => ? ->.
Qed.

Lemma uniform_regular {X : uniformType} : @regular_space X.
Proof.
move=> x A; rewrite /= -nbhs_entourageE => -[E entE].
move/(subset_trans (ent_closure entE)) => ExA.
by exists (xsection (split_ent E) x) => //; exists (split_ent E).
Qed.

End completely_regular.

Module completely_regular_uniformity.
Section completely_regular_uniformity.
Context {R : realType} {X : topologicalType}.
Hypothesis crs : completely_regular_space X.

Let X' : uniformType := @sup_topology X {f : X -> R | continuous f}
  (fun f => Uniform.class (weak_topology (projT1 f))).

Let completely_regular_nbhsE : @nbhs X X = nbhs_ (@entourage X').
Proof.
rewrite nbhs_entourageE; apply/funext => x; apply/seteqP; split; first last.
  apply/cvg_sup => -[f ctsf] U [/= _ [[V /= oV <- /= Vfx]]] /filterS.
  by apply; exact/ctsf/open_nbhs_nbhs.
move=> U; wlog oU : U / @open X U.
  move=> WH; rewrite nbhsE => -[V [oV Vx /filterS]].
  apply; first exact: (@nbhs_filter X').
  by apply: WH => //; move: oV; rewrite openE; exact.
move=> /[dup] nUx /nbhs_singleton Ux.
have ufs : uniform_separator [set x] (~` U).
  by apply: crs; [exact: open_closedC | exact].
have /uniform_separatorP := ufs => /(_ R)[f [ctsf f01 fx0 fU1]].
rewrite -nbhs_entourageE /entourage /= /sup_ent /= smallest_filter_finI.
pose E := map_pair f @^-1` (fun pq => ball pq.1 1 pq.2).
exists E; first last.
  move=> z /= /set_mem; rewrite /E /=.
  have -> : f x = 0 by apply: fx0; exists x.
  rewrite /ball /= sub0r normrN; apply: contraPP => cUz.
  suff -> : f z = 1 by rewrite normr1 ltxx.
  by apply: fU1; exists z.
move=> r /= [_]; apply => /=.
pose f' : {classic {f : X -> R | continuous f}} := exist _ f ctsf.
suff /asboolP entE : @entourage (weak_topology f) (f', E).2.
  by exists (exist _ (f', E) entE).
exists (fun pq => ball pq.1 1 pq.2) => //=.
by rewrite /entourage /=; exists 1 => /=.
Qed.

Definition type : Type := let _ := completely_regular_nbhsE in X.

#[export] HB.instance Definition _ := Topological.copy type X.
#[export] HB.instance Definition _ := @Nbhs_isUniform.Build
  type
  (@entourage X')
  (@entourage_filter X')
  (@entourage_diagonal_subproof X')
  (@entourage_inv X')
  (@entourage_split_ex X')
  completely_regular_nbhsE.
#[export] HB.instance Definition _ := Uniform.on type.

End completely_regular_uniformity.
Module Exports. HB.reexport. End Exports.
End completely_regular_uniformity.
Export completely_regular_uniformity.Exports.

Section locally_compact_uniform.
Context {X : topologicalType} {R : realType}.
Hypothesis lcpt : locally_compact [set: X].
Hypothesis hsdf : hausdorff_space X.

Let opc := @one_point_compactification X.

Lemma one_point_compactification_completely_reg :
  completely_regular_space opc.
Proof.
apply: (@normal_completely_regular R).
  apply: compact_normal.
    exact: one_point_compactification_hausdorff.
  exact: one_point_compactification_compact.
by apply: hausdorff_accessible; exact: one_point_compactification_hausdorff.
Qed.

#[local]
HB.instance Definition _ := Uniform.copy opc
  (@completely_regular_uniformity.type R _
    one_point_compactification_completely_reg).

Let X' := @weak_topology X opc Some.
Lemma nbhs_one_point_compactification_weakE : @nbhs X X = nbhs_ (@entourage X').
Proof. by rewrite nbhs_entourageE one_point_compactification_weak_topology. Qed.

#[local, non_forgetful_inheritance]
HB.instance Definition _ := @Nbhs_isUniform.Build
  X
  (@entourage X')
  (@entourage_filter X')
  (@entourage_diagonal_subproof X')
  (@entourage_inv X')
  (@entourage_split_ex X')
  nbhs_one_point_compactification_weakE.

Lemma locally_compact_completely_regular : completely_regular_space X.
Proof. exact: uniform_completely_regular. Qed.

End locally_compact_uniform.

Lemma completely_regular_regular {R : realType} {X : topologicalType} :
  completely_regular_space X -> @regular_space X.
Proof.
move=> crsX; pose P' := @completely_regular_uniformity.type R _ crsX.
exact: (@uniform_regular P').
Qed.

Section pseudometric_normal.

Lemma regular_openP {T : topologicalType} (x : T) :
  {for x, @regular_space T} <-> forall A, closed A -> ~ A x ->
  exists U V : set T, [/\ open U, open V, U x, A `<=` V & U `&` V = set0].
Proof.
split.
  move=> + A clA nAx => /(_ (~` A)) [].
    by apply: open_nbhs_nbhs; split => //; exact: closed_openC.
  move=> U Ux /subsetC; rewrite setCK => AclU; exists U°.
  exists (~` closure U) ; split => //; first exact: open_interior.
    exact/closed_openC/closed_closure.
  apply/disjoints_subset; rewrite setCK.
  exact: (subset_trans (@interior_subset _ _) (@subset_closure _ _)).
move=> + A Ax => /(_ (~` A°)) []; [|exact|].
  exact/open_closedC/open_interior.
move=> U [V] [oU oV Ux /subsetC cAV /disjoints_subset UV]; exists U.
  exact/open_nbhs_nbhs.
apply: (subset_trans (closure_subset UV)).
move/open_closedC/closure_id : oV => <-.
by apply: (subset_trans cAV); rewrite setCK; exact: interior_subset.
Qed.

Lemma pseudometric_normal {R : realType} {X : pseudoMetricType R} :
  normal_space X.
Proof.
apply/(@normal_openP R) => A B clA clB AB0.
have eps' (D : set X) : closed D -> forall x, exists eps : {posnum R}, ~ D x ->
    ball x eps%:num `&` D = set0.
  move=> clD x; have [nDx|?] := pselect (~ D x); last by exists 1%:pos.
  have /regular_openP/(_ _ clD) [//|] := @uniform_regular X x.
  move=> U [V] [+ oV] Ux /subsetC BV /disjoints_subset UV0.
  rewrite openE /interior => /(_ _ Ux); rewrite -nbhs_ballE => -[].
  move => _/posnumP[eps] beU; exists eps => _; apply/disjoints_subset.
  exact: (subset_trans beU (subset_trans UV0 _)).
pose epsA x := projT1 (cid (eps' _ clB x)).
pose epsB x := projT1 (cid (eps' _ clA x)).
exists (\bigcup_(x in A) interior (ball x ((epsA x)%:num / 2)%:pos%:num)).
exists (\bigcup_(x in B) interior (ball x ((epsB x)%:num / 2)%:pos%:num)).
split.
- by apply: bigcup_open => ? ?; exact: open_interior.
- by apply: bigcup_open => ? ?; exact: open_interior.
- by move=> x ?; exists x => //; exact: nbhsx_ballx.
- by move=> y ?; exists y => //; exact: nbhsx_ballx.
- apply/eqP/negPn/negP/set0P => -[z [[x Ax /interior_subset Axe]]].
  case=> y By /interior_subset Bye; have nAy : ~ A y.
    by move: AB0; rewrite setIC => /disjoints_subset; exact.
  have nBx : ~ B x by move/disjoints_subset: AB0; exact.
  have [|/ltW] := leP ((epsA x)%:num / 2) ((epsB y)%:num / 2).
    move/ball_sym: Axe => /[swap] /le_ball /[apply] /(ball_triangle Bye).
    rewrite -splitr => byx; have := projT2 (cid (eps' _ clA y)) nAy.
    by rewrite -subset0; apply; split; [exact: byx|].
  move/ball_sym: Bye =>/[swap] /le_ball /[apply] /(ball_triangle Axe).
  rewrite -splitr => byx; have := projT2 (cid (eps' _ clB x)) nBx.
  by rewrite -subset0; apply; split; [exact: byx|].
Qed.

End pseudometric_normal.
