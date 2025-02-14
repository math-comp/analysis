(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean.
From mathcomp Require Import all_classical.
From mathcomp Require Import itv reals topology_structure uniform_structure.

(**md**************************************************************************)
(* # PseudoMetric Spaces                                                      *)
(* This file provides pseudometric spaces, complete pseudometric spaces,      *)
(* and the corresponding theory. Note that a classic metric space is simply   *)
(* pseudometric + hausdorff. However we will make extensive use of the of the *)
(* non-hausdorff case, such as in our proof of Urysohn's lemma.               *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### PseudoMetrics                                                          *)
(* ```                                                                        *)
(*                entourage_ ball == entourages defined using balls           *)
(*               pseudoMetricType == interface type for pseudo metric space   *)
(*                                   structure: a type equipped with balls    *)
(*                                   The HB class is PseudoMetric.            *)
(*              pseudoPMetricType == a pointed pseudoMetric space             *)
(*                       ball x e == ball of center x and radius e            *)
(*                nbhs_ball_ ball == nbhs defined using the given balls       *)
(*                      nbhs_ball == nbhs defined using balls in a            *)
(*                                   pseudometric space                       *)
(* ```                                                                        *)
(* ### Factories                                                              *)
(* ```                                                                        *)
(*            Nbhs_isPseudoMetric == factory to build a topological space     *)
(*                                   from a mixin for a pseudoMetric space    *)
(* ```                                                                        *)
(* ### Complete Pseudometrics                                                 *)
(* ```                                                                        *)
(*                        ball_ N == balls defined by the norm/absolute       *)
(*                                   value N                                  *)
(*       completePseudoMetricType == interface type for a complete            *)
(*                                   pseudometric space structure             *)
(*                                   The HB class is CompletePseudoMetric.    *)
(*                   cauchy_ex F <-> the set of sets F is a cauchy filter     *)
(*                                   (epsilon-delta definition)               *)
(*                 cauchy_ball F <-> the set of sets F is a cauchy filter     *)
(*                                   (using the near notations)               *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Making sure that [Program] does not automatically introduce *)
#[local]
Obligation Tactic := idtac.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Lemma entourage_E {R : numDomainType} {T T'} (ball : T -> R -> set T') :
  entourage_ ball =
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).
Proof. by []. Qed.

HB.mixin Record Uniform_isPseudoMetric (R : numDomainType) M of Uniform M := {
  ball : M -> R -> M -> Prop ;
  ball_center_subproof : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym_subproof : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle_subproof :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE_subproof : entourage = entourage_ ball
}.

#[short(type="pseudoMetricType")]
HB.structure Definition PseudoMetric (R : numDomainType) :=
  {T of Uniform T & Uniform_isPseudoMetric R T}.

#[short(type="pseudoPMetricType")]
HB.structure Definition PseudoPointedMetric (R : numDomainType) :=
  {T of Pointed T & Uniform T & Uniform_isPseudoMetric R T}.

(* was uniformityOfBallMixin *)
HB.factory Record Nbhs_isPseudoMetric (R : numFieldType) M of Nbhs M := {
  ent : set_system (M * M);
  nbhsE : nbhs = nbhs_ ent;
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : ent = entourage_ ball
}.

HB.builders Context R M of Nbhs_isPseudoMetric R M.
Local Open Scope relation_scope.

Let ball_le x : {homo ball x : e1 e2 / e1 <= e2 >-> e1 `<=` e2}.
Proof.
move=> e1 e2 le12 y xe1_y.
move: le12; rewrite le_eqVlt => /orP [/eqP <- //|].
rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: ball_triangle xe1_y.
suff : ball x (PosNum lt12)%:num x by [].
exact: ball_center.
Qed.

Let entourage_filter_subproof : Filter ent.
Proof.
rewrite entourageE; apply: filter_from_filter; first by exists 1 => /=.
move=> _ _ /posnumP[e1] /posnumP[e2]; exists (Num.min e1 e2)%:num => //=.
by rewrite subsetI; split=> ?; apply: ball_le;
   rewrite num_le// ge_min lexx ?orbT.
Qed.

Let ball_sym_subproof A : ent A -> diagonal `<=` A.
Proof.
rewrite entourageE; move=> [e egt0 sbeA] xy xey.
by apply: sbeA; rewrite /= xey; exact: ball_center.
Qed.

Let ball_triangle_subproof A : ent A -> ent A^-1.
Proof.
rewrite entourageE => - [e egt0 sbeA].
by exists e => // xy xye; apply: sbeA; exact: ball_sym.
Qed.

Let entourageE_subproof A : ent A -> exists2 B, ent B & B \; B `<=` A.
Proof.
rewrite entourageE; move=> [_/posnumP[e] sbeA].
exists [set xy | ball xy.1 (e%:num / 2) xy.2].
  by exists (e%:num / 2) => /=.
move=> xy [z xzhe zyhe]; apply: sbeA.
by rewrite [e%:num]splitr; exact: ball_triangle zyhe.
Qed.

HB.instance Definition _ := Nbhs_isUniform.Build M
  entourage_filter_subproof ball_sym_subproof ball_triangle_subproof
  entourageE_subproof nbhsE.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R M
  ball_center ball_sym ball_triangle entourageE.

HB.end.

Lemma entourage_ballE {R : numDomainType} {M : pseudoMetricType R} :
  entourage_ (@ball R M) = entourage.
Proof. by rewrite entourageE_subproof. Qed.

Lemma entourage_from_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @filter_from R _ [set x : R | 0 < x]
    (fun e => [set xy | @ball R M xy.1 e xy.2]) = entourage.
Proof. by rewrite -entourage_ballE. Qed.

Lemma entourage_ball {R : numDomainType} (M : pseudoMetricType R)
  (e : {posnum R}) : entourage [set xy : M * M | ball xy.1 e%:num xy.2].
Proof. by rewrite -entourage_ballE; exists e%:num => /=. Qed.
#[global] Hint Resolve entourage_ball : core.

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition nbhs_ball {R : numDomainType} {M : pseudoMetricType R} :=
  nbhs_ball_ (@ball R M).

Lemma nbhs_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @nbhs_ball R M = nbhs.
Proof.
rewrite predeq2E => x P; rewrite -nbhs_entourageE; split.
  move=> [_/posnumP[e] sbxeP]; exists [set xy | ball xy.1 e%:num xy.2] => //.
  by move=> y /xsectionP/sbxeP.
rewrite -entourage_ballE; move=> [A [e egt0 sbeA] sAP].
by exists e => // ? ?; exact/sAP/xsectionP/sbeA.
Qed.

Lemma filter_from_ballE {R : numDomainType} {M : pseudoMetricType R} x :
  @filter_from R _ [set x : R | 0 < x] (@ball R M x) = nbhs x.
Proof. by rewrite -nbhs_ballE. Qed.

Module Export NbhsBall.
Definition nbhs_simpl := (nbhs_simpl,@filter_from_ballE,@nbhs_ballE).
End NbhsBall.

Lemma nbhs_ballP {R : numDomainType} {M : pseudoMetricType R} (x : M) P :
  nbhs x P <-> nbhs_ball x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma ball_center {R : numDomainType} (M : pseudoMetricType R) (x : M)
  (e : {posnum R}) : ball x e%:num x.
Proof. exact: ball_center_subproof. Qed.
#[global] Hint Resolve ball_center : core.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.

Lemma ballxx (x : M) (e : R) : 0 < e -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: ball_sym_subproof. Qed.

Lemma ball_symE (x y : M) (e : R) : ball x e y = ball y e x.
Proof. by rewrite propeqE; split; exact/ball_sym. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: ball_triangle_subproof. Qed.

Lemma nbhsx_ballx (x : M) (eps : R) : 0 < eps -> nbhs x (ball x eps).
Proof. by move=> e0; apply/nbhs_ballP; exists eps. Qed.

Lemma open_nbhs_ball (x : M) (eps : {posnum R}) : open_nbhs x (ball x eps%:num)^°.
Proof.
split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; exact: nbhsx_ballx.
Qed.

Lemma le_ball (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y. case: comparableP le12 => [lte12 _|//|//|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma near_ball (y : M) (eps : R) : 0 < eps -> \forall y' \near y, ball y eps y'.
Proof. exact: nbhsx_ballx. Qed.

Lemma dnbhs_ball (a : M) (e : R) : (0 < e)%R -> a^' (ball a e `\ a).
Proof.
move: e => _/posnumP[e]; rewrite /dnbhs /within /=; near=> r => ra.
split => //=; last exact/eqP.
by near: r; rewrite near_simpl; exact: near_ball.
Unshelve. all: by end_near. Qed.

Lemma fcvg_ballP {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by rewrite -filter_fromP !nbhs_simpl /=. Qed.

Lemma __deprecated__cvg_ballPpos {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : {posnum R}, \forall y' \near F, ball y eps%:num y'.
Proof.
split => [/fcvg_ballP + eps|pos]; first exact.
by apply/fcvg_ballP=> _/posnumP[eps] //.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use a combination of `cvg_ballP` and `posnumP`")]
Notation cvg_ballPpos := __deprecated__cvg_ballPpos (only parsing).

Lemma fcvg_ball {F} {FF : Filter F} (y : M) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by move/fcvg_ballP. Qed.

Lemma cvg_ballP {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ballP. Qed.

Lemma cvg_ball {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y -> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ball. Qed.

Lemma cvgi_ballP T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Proof.
split=> [Fy _/posnumP[eps] |Fy P] /=; first exact/Fy/nbhsx_ballx.
move=> /nbhs_ballP[_ /posnumP[eps] subP].
rewrite near_simpl near_mapi; near=> x.
have [//|z [fxz yz]] := near (Fy _ (gt0 eps)) x.
by exists z => //; split => //; apply: subP.
Unshelve. all: end_near. Qed.

#[deprecated(since="mathcomp-analysis 1.6.0", note="use `cvgi_ballP` instead")]
Definition cvg_toi_locally := @cvgi_ballP.

Lemma cvgi_ball T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/cvgi_ballP. Qed.

End pseudoMetricType_numDomainType.

#[global] Hint Resolve nbhsx_ballx : core.

Global Instance entourage_proper_filter {R : numDomainType}
  {M : pseudoPMetricType R} : ProperFilter (@entourage M).
Proof.
apply: Build_ProperFilter_ex; rewrite -entourage_ballE => A [_/posnumP[e] sbeA].
by exists (point, point); apply: sbeA; apply: ballxx.
Qed.

Arguments nbhsx_ballx {R M} x eps.
Arguments near_ball {R M} y eps.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `cvg_ball`")]
Notation app_cvg_locally := cvg_ball (only parsing).

Section pseudoMetricType_numFieldType.
Context {R : numFieldType} {M : pseudoMetricType R}.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2) z -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -splitr. Qed.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2) x -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

End pseudoMetricType_numFieldType.

Section entourages.
Variable R : numDomainType.

Lemma unif_continuousP (U V : pseudoMetricType R) (f : U -> V) :
  unif_continuous f <->
  forall e, e > 0 -> exists2 d, d > 0 &
    forall x, ball x.1 d x.2 -> ball (f x.1) e (f x.2).
Proof.
have fappF : Filter ((fun xy => (f xy.1, f xy.2)) @ entourage_ ball).
  by rewrite entourage_ballE; apply: fmap_filter.
by rewrite /unif_continuous -!entourage_ballE filter_fromP.
Qed.

End entourages.

Lemma countable_uniformity_metric {R : realType} {T : pseudoMetricType R} :
  countable_uniformity T.
Proof.
apply/countable_uniformityP.
exists (fun n => [set xy : T * T | ball xy.1 n.+1%:R^-1 xy.2]); last first.
  by move=> n; exact: (entourage_ball _ n.+1%:R^-1%:pos).
move=> E; rewrite -entourage_ballE => -[e e0 subE].
exists `|Num.floor e^-1|%N; apply: subset_trans subE => xy; apply: le_ball.
rewrite /= -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0// -natr1.
rewrite natr_absz ger0_norm; last first.
  by rewrite -floor_ge_int ?invr_ge0 ?num_real // ltW.
by rewrite intrD1 ltW// lt_succ_floor ?num_real.
Qed.

(** Specific pseudoMetric spaces *)

HB.instance Definition _ (R : zmodType) := isPointed.Build R 0.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%_R y /.

Lemma subset_ball_prop_in_itv (R : realDomainType) (x : R) e P :
  ball_ Num.Def.normr x e `<=` P <->
  {in `](x - e), (x + e)[, forall y, P y}.
Proof.
by split=> exP y /=; rewrite ?in_itv (ltr_distlC, =^~ltr_distlC); apply: exP.
Qed.

Lemma subset_ball_prop_in_itvcc (R : realDomainType) (x : R) e P : 0 < e ->
  ball_ Num.Def.normr x (2 * e) `<=` P ->
  {in `[(x - e), (x + e)], forall y, P y}.
Proof.
move=> e_gt0 PP y; rewrite in_itv/= -ler_distlC => ye; apply: PP => /=.
by rewrite (le_lt_trans ye)// ltr_pMl// ltr1n.
Qed.

Global Instance ball_filter (R : realDomainType) (t : R) : Filter
  [set P | exists2 i : R, 0 < i & ball_ Num.norm t i `<=` P].
Proof.
apply: Build_Filter; [by exists 1 | move=> P Q | move=> P Q PQ]; rewrite /mkset.
- move=> -[x x0 xP] [y ? yQ]; exists (Num.min x y); first by rewrite lt_min x0.
  move=> z tz; split.
    by apply: xP; rewrite /= (lt_le_trans tz) // ge_min lexx.
  by apply: yQ; rewrite /= (lt_le_trans tz) // ge_min lexx orbT.
- by move=> -[x ? xP]; exists x => //; apply: (subset_trans xP).
Qed.

#[global] Hint Extern 0 (Filter [set P | exists2 i, _ & ball_ _ _ i `<=` P]) =>
  (apply: ball_filter) : typeclass_instances.

Section pseudoMetric_of_normedDomain.
Context {K : numDomainType} {R : normedZmodType K}.

Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Proof. by move=> ? /=; rewrite subrr normr0. Qed.

Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Proof. by rewrite /= distrC. Qed.

Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Proof.
move=> /= ? ?; rewrite -(subr0 x) -(subrr y) opprD opprK addrA -(addrA _ y).
by rewrite (le_lt_trans (ler_normD _ _)) // ltrD.
Qed.

Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Proof.
rewrite /nbhs_ entourage_E predeq2E => x A; split.
  move=> [e egt0 sbeA].
  exists [set xy | ball_ Num.norm xy.1 e xy.2]; first by exists e.
  by move=> r /xsectionP; exact: sbeA.
by move=> [E [e egt0 sbeE] sEA]; exists e => // ? ?; exact/sEA/xsectionP/sbeE.
Qed.

End pseudoMetric_of_normedDomain.

HB.instance Definition _ (R : zmodType) := Pointed.on R^o.

#[short(type="completePseudoMetricType")]
HB.structure Definition CompletePseudoMetric R :=
  {T of Complete T & PseudoPointedMetric R T}.

Definition cauchy_ex {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy_ball {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_ballP (R : numDomainType) (T  : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ball F <-> cauchy F.
Proof.
split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply/cauchyF/entourage_ball.
move=> U; rewrite -entourage_ballE => - [_/posnumP[eps] xyepsU].
by near do apply: xyepsU; apply: cauchyF.
Unshelve. all: by end_near. Qed.
Arguments cauchy_ballP {R T} F {FF}.

Lemma cauchy_exP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ex F -> cauchy F.
Proof.
move=> Fc A; rewrite !nbhs_simpl /= -entourage_ballE => -[_/posnumP[e] sdeA].
have /Fc [z /= Fze] := [gt0 of e%:num / 2]; near=> x y; apply: sdeA => /=.
by apply: (@ball_splitr _ _ z); [near: x|near: y].
Unshelve. all: by end_near. Qed.
Arguments cauchy_exP {R T} F {FF}.

Lemma cauchyP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (PF : ProperFilter F) :
  cauchy F <-> cauchy_ex F.
Proof.
split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
near F => x; exists x; near: x; apply: (@nearP_dep _ _ F F).
exact/Fcauchy/entourage_ball.
Unshelve. all: by end_near. Qed.
Arguments cauchyP {R T} F {PF}.
