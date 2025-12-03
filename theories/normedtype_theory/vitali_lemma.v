(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean rat.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import set_interval interval_inference ereal reals.
From mathcomp Require Import topology function_spaces tvs num_normedtype.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module.

(**md**************************************************************************)
(* # Vitali's covering lemmas                                                 *)
(*                                                                            *)
(* Vitali's covering lemma (finite version):                                  *)
(* Given a finite collection of balls $B_i$ with $i\in s$, there exists a     *)
(* subcollection $B_j$ with $j\in D$ of pairwise disjoint balls such that     *)
(* $\cup_{i\in s} B_i \subseteq \cup_{i\in D} 3B_j$.                          *)
(*                                                                            *)
(* This file also provides the infinite version of Vitali's covering lemma.   *)
(*                                                                            *)
(* ```                                                                        *)
(*        cpoint A == the center of the set A when A is an open ball          *)
(*        radius A == the radius of the set A when A is an open ball          *)
(*                    Radius A has type {nonneg R} with R a numDomainType.    *)
(*       is_ball A == boolean predicate that holds when A is an open ball     *)
(*          k *` A == open ball with center cpoint A and radius k * radius A  *)
(*                    when A is an open ball and set0 o.w.                    *)
(*   vitali_collection_partition B V r n == subset of indices of V such the   *)
(*                    the ball B i has a radius between r/2^n+1 and r/2^n     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "k *` A" (at level 40, left associativity, format "k  *`  A").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section center_radius.
Context {R : numDomainType} {M : pseudoPMetricType R}.
Implicit Types A : set M.

(* NB: the identifier "center" is already taken! *)
Definition cpoint A := get [set c | exists r, A = ball c r].

Definition radius A : {nonneg R} :=
  xget 0%:nng [set r | A = ball (cpoint A) r%:num].

Definition is_ball A := A == ball (cpoint A) (radius A)%:num.

Definition scale_ball (k : R) A :=
  if is_ball A then ball (cpoint A) (k * (radius A)%:num) else set0.

Local Notation "k *` B" := (scale_ball k B).

Lemma sub_scale_ball A k l : k <= l -> k *` A `<=` l *` A.
Proof.
move=> kl; rewrite /scale_ball; case: ifPn=> [Aball|_]; last exact: subset_refl.
by apply: le_ball; rewrite ler_wpM2r.
Qed.

Lemma scale_ball1 A : is_ball A -> 1 *` A = A.
Proof. by move=> Aball; rewrite /scale_ball Aball mul1r; move/eqP in Aball. Qed.

Lemma sub1_scale_ball A l : is_ball A -> A `<=` l.+1%:R *` A.
Proof. by move/scale_ball1 => {1}<-; apply: sub_scale_ball; rewrite ler1n. Qed.

End center_radius.
Notation "k *` B" := (scale_ball k B) : classical_set_scope.

Lemma scale_ball0 {R : realFieldType} (A : set R) r : (r <= 0)%R ->
  r *` A = set0.
Proof.
move=> r0; apply/seteqP; split => // x.
rewrite /scale_ball; case: ifPn => // ballA.
by rewrite ((ball0 _ _).2 _)// mulr_le0_ge0.
Qed.

Section center_radius_realFieldType.
Context {R : realFieldType}.
Implicit Types x y r s : R.

Let ball_inj_radius_gt0 x y r s : 0 < r -> ball x r = ball y s -> 0 < s.
Proof.
move=> r0 xrys; rewrite ltNge; apply/negP => /ball0 s0; move: xrys.
by rewrite s0 => /seteqP[+ _] => /(_ x); apply; exact: ballxx.
Qed.

Let ball_inj_center x y r s : 0 < r -> ball x r = ball y s -> x = y.
Proof.
move=> r0 xrys; have s0 := ball_inj_radius_gt0 r0 xrys.
apply/eqP/negPn/negP => xy.
wlog : x y r s xrys r0 s0 xy / x < y.
  move: xy; rewrite neq_lt => /orP[xy|yx].
    by move/(_ _ _ _ _ xrys); apply => //; rewrite lt_eqF.
  by move/esym : xrys => /[swap] /[apply]; apply => //; rewrite lt_eqF.
move=> {}xy; have [rs|sr] := ltP r s.
- suff : ~ ball x r (y + r).
    by apply; rewrite xrys /ball/= ltr_distlC !ltrD2l -ltr_norml gtr0_norm.
  by rewrite /ball/= ltr_distlC ltrD2r (ltNge y) (ltW xy) andbF.
- suff : ~ ball y s (x - r + Num.min ((y - x) / 2) r).
    apply; rewrite -xrys /ball/= ltr_distlC ltrDl lt_min r0 andbT.
    rewrite divr_gt0 ?subr_gt0//= addrAC -addrA ltrD2l ltrBlDl.
    by rewrite gt_min ltrDl r0 orbT.
  have [yx2r|ryx2] := ltP ((y - x) / 2) r.
    rewrite /ball/= ltr_distlC ltNge => /andP[/negP + _]; apply.
    rewrite -(@ler_pM2r _ 2)// !(mulrBl, mulrDl) !divfK// addrAC.
    by rewrite lerB ?ler_pM2r// addrC !mulr_natr subrKA lerD2l ltW.
  rewrite subrK /ball/= ltr_distlC => /andP[].
  rewrite ltrBlDl addrC -ltrBlDl -(@ltr_pM2r _ (2^-1))//.
  move=> /le_lt_trans => /(_ _ ryx2) /le_lt_trans => /(_ _ sr).
  by rewrite ltr_pMr// invf_gt1// ltNge ler1n.
Qed.

Let ball_inj_radius x y r s : 0 < r -> ball x r = ball y s -> r = s.
Proof.
move=> r0 xrys; have s0 := ball_inj_radius_gt0 r0 xrys.
move: (xrys); rewrite (ball_inj_center r0 xrys) => {}xrys.
apply/eqP/negPn/negP; rewrite neq_lt => /orP[rs|sr].
- suff : ball y s (y + r) by rewrite -xrys /ball/= ltr_distlC ltxx andbF.
  rewrite /ball/= ltr_distlC !ltrD2l rs andbT (lt_trans _ r0)//.
  by rewrite ltrNl oppr0 (lt_trans r0).
- suff : ball y r (y + s) by rewrite xrys /ball/= ltr_distlC ltxx andbF.
  rewrite /ball/= ltr_distlC !ltrD2l sr andbT (lt_trans _ s0)//.
  by rewrite ltrNl oppr0 (lt_trans s0).
Qed.

Lemma ball_inj x y r s : 0 < r -> ball x r = ball y s -> x = y /\ r = s.
Proof.
by move=> r0 xrys; split; [exact: (ball_inj_center r0 xrys)|
                           exact: (ball_inj_radius r0 xrys)].
Qed.

Lemma radius0 : radius (@set0 R) = 0%:nng :> {nonneg R}.
Proof.
rewrite /radius/=; case: xgetP => [r _ /= /esym/ball0 r0|]/=.
  by apply/val_inj/eqP; rewrite /= eq_le r0/=.
by move=> /(_ 0%:nng) /nesym /ball0.
Qed.

Lemma is_ball0 : is_ball (@set0 R).
Proof.
rewrite /is_ball; apply/eqP/seteqP; split => // x; rewrite radius0/=.
by rewrite (ball0 _ _).2.
Qed.

Lemma cpoint_ball x r : 0 < r -> cpoint (ball x r) = x.
Proof.
move=> r0; rewrite /cpoint; case: xgetP => [y _ [s] /(ball_inj r0)[]//|].
by move=> /(_ x)/forallNP/(_ r).
Qed.

Lemma radius_ball_num x r : 0 <= r -> (radius (ball x r))%:num = r.
Proof.
rewrite le_eqVlt => /orP[/eqP <-|r0]; first by rewrite (ball0 _ _).2// radius0.
rewrite /radius; case: xgetP => [y _ /(ball_inj r0)[]//|].
by move=> /(_ (NngNum (ltW r0)))/=; rewrite cpoint_ball.
Qed.

Lemma radius_ball x r (r0 : 0 <= r) : radius (ball x r) = NngNum r0.
Proof. by apply/val_inj => //=; rewrite radius_ball_num. Qed.

Lemma is_ballP (A : set R) x : is_ball A ->
  A x -> `|cpoint A - x| < (radius A)%:num.
Proof. by rewrite /is_ball => /eqP {1}-> /lt_le_trans; exact. Qed.

Lemma is_ball_ball x r : is_ball (ball x r).
Proof.
have [r0|/ball0 ->] := ltP 0 r; last exact: is_ball0.
by apply/eqP; rewrite cpoint_ball// (radius_ball _ (ltW r0)).
Qed.

Lemma scale_ball_set0 (k : R) : k *` set0 = set0 :> set R.
Proof. by rewrite /scale_ball is_ball0// radius0/= mulr0 ball0. Qed.

Lemma ballE (A : set R) : is_ball A -> A = ball (cpoint A) (radius A)%:num.
Proof.
move=> ballA; apply/seteqP; split => [x /is_ballP|x Ax]; first exact.
by move: ballA => /eqP ->.
Qed.

Lemma is_ball_closureP (A : set R) x : is_ball A ->
  closure A x -> `|cpoint A - x| <= (radius A)%:num.
Proof.
move=> ballP cAx.
have : closed_ball (cpoint A) (radius A)%:num x by rewrite /closed_ball -ballE.
by have [r0|r0] := ltP 0 (radius A)%:num; [rewrite closed_ballE|
                                           rewrite closed_ball0].
Qed.

Lemma is_ball_closure (A : set R) : is_ball A ->
  closure A = closed_ball (cpoint A) (radius A)%:num.
Proof. by move=> ballA; rewrite /closed_ball -ballE. Qed.

Lemma scale_ballE k x r : 0 <= k -> k *` ball x r = ball x (k * r).
Proof.
move=> k0; have [r0|r0] := ltP 0 r.
  apply/seteqP; split => y.
    rewrite /scale_ball is_ball_ball//= cpoint_ball//.
    by rewrite (radius_ball_num _ (ltW _)).
  by rewrite /scale_ball is_ball_ball cpoint_ball// radius_ball_num// ltW.
rewrite ((ball0 _ _).2 r0) scale_ball_set0; apply/esym/ball0.
by rewrite mulr_ge0_le0.
Qed.

Lemma cpoint_scale_ball A (k : R) : 0 < k -> is_ball A -> 0 < (radius A)%:num ->
  cpoint (k *` A) = cpoint A :> R.
Proof.
move=> k0 ballA r0.
rewrite [in LHS](ballE ballA) (scale_ballE _ _ (ltW k0))// cpoint_ball//.
by rewrite mulr_gt0.
Qed.

Lemma radius_scale_ball (A : set R) (k : R) : 0 <= k -> is_ball A ->
  (radius (k *` A))%:num = k * (radius A)%:num.
Proof.
move=> k0 ballA.
by rewrite [in LHS](ballE ballA) (scale_ballE _ _ k0)// radius_ball// mulr_ge0.
Qed.

Lemma is_scale_ball (A : set R) (k : R) : is_ball A -> is_ball (k *` A).
Proof.
move=> Aball.
have [k0|k0] := leP 0 k.
  by rewrite (ballE Aball) (scale_ballE _ _ k0); exact: is_ball_ball.
rewrite (_ : _ *` _ = set0); first exact: is_ball0.
apply/seteqP; split => // x.
by rewrite /scale_ball Aball (ball0 _ _).2// nmulr_rle0.
Qed.

End center_radius_realFieldType.

Section vitali_lemma_finite.
Context {R : realType} {I : eqType}.
Variable (B : I -> set R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis B_set0 : forall i, B i !=set0.

Lemma vitali_lemma_finite (s : seq I) :
  { D : seq I | [/\ uniq D,
    {subset D <= s}, trivIset [set` D] B &
    forall i, i \in s -> exists j, [/\ j \in D,
      B i `&` B j !=set0,
      radius (B j) >= radius (B i) &
      B i `<=` 3 *` B j] ] }.
Proof.
pose LE x y := radius (B x) <= radius (B y).
have LE_trans : transitive LE by move=> x y z; exact: le_trans.
wlog : s / sorted LE s.
  have : sorted LE (sort LE s) by apply: sort_sorted => x y; exact: le_total.
  move=> /[swap] /[apply] -[D [uD Ds trivIset_DB H]]; exists D; split => //.
  - by move=> x /Ds; rewrite mem_sort.
  - by move=> i; rewrite -(mem_sort LE) => /H.
elim: s => [_|i [/= _ _|j t]]; first by exists nil.
  exists [:: i]; split => //; first by rewrite set_cons1; exact: trivIset1.
  move=> _ /[1!inE] /eqP ->; exists i; split => //; first by rewrite mem_head.
  - by rewrite setIid; exact: B_set0.
  - exact: sub1_scale_ball.
rewrite /= => + /andP[ij jt] => /(_ jt)[u [uu ujt trivIset_uB H]].
have [K|] := pselect (forall j, j \in u -> B j `&` B i = set0).
  have [iu|iu] := boolP (i \in u).
    exists u; split => //.
    - by move=> x /ujt xjt; rewrite inE xjt orbT.
    - move=> k /[1!inE] /predU1P[->{k}|].
        exists i; split; [by []| |exact: lexx|].
          by rewrite setIid; exact: B_set0.
        exact: sub1_scale_ball.
      by move/H => [l [lu lk0 kl k3l]]; exists l; split => //; rewrite inE lu orbT.
  exists (i :: u); split => //.
  - by rewrite /= iu.
  - move=> x /[1!inE] /predU1P[->|]; first by rewrite mem_head.
    by move/ujt => xjt; rewrite in_cons xjt orbT.
  - move=> k l /= /[1!inE] /predU1P[->{k}|ku].
      by move=> /predU1P[->{j}//|js] /set0P; rewrite setIC K// eqxx.
    by move=> /predU1P[->{l} /set0P|lu]; [rewrite K// eqxx|exact: trivIset_uB].
  - move=> k /[1!inE] /predU1P[->{k}|].
      exists i; split; [by rewrite mem_head| |exact: lexx|].
        by rewrite setIid; exact: B_set0.
      exact: sub1_scale_ball.
    by move/H => [l [lu lk0 kl k3l]]; exists l; split => //; rewrite inE lu orbT.
move/existsNP/cid => [k /not_implyP[ku /eqP/set0P ki0]].
exists u; split => //.
  by move=> l /ujt /[!inE] /predU1P[->|->]; rewrite ?eqxx ?orbT.
move=> _ /[1!inE] /predU1P[->|/H//]; exists k; split; [exact: ku| | |].
- by rewrite setIC.
- apply: (le_trans ij); move/ujt : ku => /[1!inE] /predU1P[<-|kt].
    exact: lexx.
  by have /allP := order_path_min LE_trans jt; apply; exact: kt.
- case: ki0 => x [Bkx Bix] y => iy.
  rewrite (ballE (is_ballB k)) scale_ballE// /ball/= -(subrKA x).
  rewrite (le_lt_trans (ler_normD _ _))// -nat1r mulrDl mul1r mulr_natl.
  rewrite (ltrD (is_ballP (is_ballB k) _))// -(subrKA (cpoint (B i))).
  rewrite (le_lt_trans (ler_normD _ _))//.
  apply (@lt_le_trans _ _ ((radius (B j))%:num *+ 2)); last first.
    apply: ler_wMn2r; move/ujt : ku; rewrite inE => /predU1P[<-|kt].
      exact: lexx.
    by have /allP := order_path_min LE_trans jt; apply; exact: kt.
  rewrite mulr2n ltrD//.
    by rewrite distrC (lt_le_trans (is_ballP (is_ballB i) _)).
  by rewrite (lt_le_trans (is_ballP (is_ballB i) _)).
Qed.

Lemma vitali_lemma_finite_cover (s : seq I) :
  { D : seq I | [/\ uniq D, {subset D <= s},
    trivIset [set` D] B &
    cover [set` s] B `<=` cover [set` D] (scale_ball 3%:R \o B)] }.
Proof.
have [D [uD DV tD maxD]] := vitali_lemma_finite s.
exists D; split => // x [i Vi] cBix/=.
by have [j [Dj BiBj ij]] := maxD i Vi; move/(_ _ cBix) => ?; exists j.
Qed.

End vitali_lemma_finite.

Section vitali_collection_partition.
Context {R : realType} {I : eqType}.
Variables (B : I -> set R) (V : set I) (r : R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis B_set0 : forall i, 0 < (radius (B i))%:num.

Definition vitali_collection_partition n :=
  [set i | V i /\ r / (2 ^ n.+1)%:R < (radius (B i))%:num <= r / (2 ^ n)%:R].

Hypothesis VBr : forall i, V i -> (radius (B i))%:num <= r.

Lemma vitali_collection_partition_ub_gt0 i : V i -> 0 < r.
Proof. by move=> Vi; rewrite (lt_le_trans _ (VBr Vi)). Qed.

Notation r_gt0 := vitali_collection_partition_ub_gt0.

Lemma ex_vitali_collection_partition i :
  V i -> exists n, vitali_collection_partition n i.
Proof.
move=> Vi; pose f := Num.truncn (r / (radius (B i))%:num).
have f_ge0 : (0 <= f)%N.
  by rewrite truncn_ge_nat// divr_ge0// (le_trans _ (VBr Vi)).
have [m /andP[mf fm]] := leq_ltn_expn f.-1.
exists m; split => //; apply/andP; split => [{mf}|{fm}].
- rewrite -(@ler_nat R) in fm.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr// (lt_le_trans _ fm)//.
  rewrite (lt_le_trans (truncnS_gt _))//= -/f.
  have [<-|f0] := eqVneq 0 f; first by rewrite /= ler_nat.
  by rewrite prednK// lt0n eq_sym.
- move: m => [|m] in mf *; first by rewrite expn0 divr1 VBr.
  rewrite ler_pdivlMr// mulrC -ler_pdivlMr//.
  rewrite -(@ler_nat R) in mf.
  have [f0|f0] := eqVneq 0 f.
    by move: mf; rewrite -f0 leNgt expnS ltr_nat leq_pmulr// expn_gt0.
  rewrite (le_trans mf)// prednK//; last by rewrite lt0n eq_sym.
  by rewrite /f truncn_le// divr_ge0// (le_trans _ (VBr Vi)).
Qed.

Lemma cover_vitali_collection_partition :
  V = \bigcup_n vitali_collection_partition n.
Proof.
apply/seteqP; split => [|i [n _] []//].
by move=> i Vi; have [n Hn] := ex_vitali_collection_partition Vi; exists n.
Qed.

Lemma disjoint_vitali_collection_partition n m : n != m ->
  vitali_collection_partition n `&`
  vitali_collection_partition m = set0.
Proof.
move=> nm; wlog : n m nm / (n < m)%N.
  move=> wlg; move: nm; rewrite neq_lt => /orP[nm|mn].
    by rewrite wlg// lt_eqF.
  by rewrite setIC wlg// lt_eqF.
move=> {}nm; apply/seteqP; split => // i [] [Vi] /andP[rnB _] [_ /andP[_]].
move/(lt_le_trans rnB); rewrite ltr_pM2l//; last by rewrite (r_gt0 Vi).
rewrite ltf_pV2 ?posrE ?ltr0n ?expn_gt0// ltr_nat.
by move/ltn_pexp2l => /(_ isT); rewrite ltnNge => /negP; apply.
Qed.

End vitali_collection_partition.

Lemma separated_closed_ball_countable
    {R : realType} (I : Type) (B : I -> set R) (D : set I) :
  (forall i, (radius (B i))%:num > 0) ->
  trivIset D (fun i => closed_ball (cpoint (B i)) (radius (B i))%:num) -> countable D.
Proof.
move=> B0 tD.
have : trivIset D (fun i => ball (cpoint (B i)) (radius (B i))%:num).
  move=> i j Di Dj BiBj; apply: tD => //.
  by apply: subsetI_neq0 BiBj => //; exact: subset_closed_ball.
apply: separated_open_countable => //; first by move=> i; exact: ball_open.
by move=> i; eexists; exact: ballxx.
Qed.

Section vitali_lemma_infinite.
Context {R : realType} {I : eqType}.
Variables (B : I -> set R) (V : set I) (r : R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis Bset0 : forall i, (radius (B i))%:num > 0.
Hypothesis VBr : forall i, V i -> (radius (B i))%:num <= r.

Let B_ := vitali_collection_partition B V r.

Let H_ n (U : set I) := [set i | B_ n i /\
  forall j, U j -> i != j -> closure (B i) `&` closure (B j) = set0].

Let elt_prop (x : set I * nat * set I) :=
  x.1.1 `<=` V /\
  maximal_disjoint_subcollection (closure \o B) x.1.1 (H_ x.1.2 x.2).

Let elt_type := {x | elt_prop x}.

Let Rel (x y : elt_type) :=
  (sval y).2 = (sval x).2 `|` (sval x).1.1 /\ (sval x).1.2.+1 = (sval y).1.2.

Lemma vitali_lemma_infinite : { D : set I | [/\ countable D,
  D `<=` V, trivIset D (closure \o B) &
  forall i, V i -> exists j, [/\ D j,
    closure (B i) `&` closure (B j) !=set0,
    (radius (B j))%:num >= (radius (B i))%:num / 2 &
    closure (B i) `<=` closure (5%:R *` B j)] ] }.
Proof.
have [D0 [D0B0 tD0 maxD0]] :=
  ex_maximal_disjoint_subcollection (closure \o B) (B_ O).
have H0 : elt_prop (D0, 0%N, set0).
  split; first by move=> i /D0B0[].
  split => //=.
  - move=> x /= D0x; split; first exact: D0B0.
    by move=> s D0s xs; move/trivIsetP : tD0; exact.
  - by move=> F D0F FH0; apply: maxD0 => // i Fi; exact: (FH0 _ Fi).1.
have [v [Hv0 HvRel]] : {v : nat -> elt_type |
    v 0%N = exist _ _ H0 /\ forall n, Rel (v n) (v n.+1)}.
  apply: dependent_choice => -[[[Dn n] Un] Hn].
  pose Hn1 := H_ n.+1 (Un `|` Dn).
  have [Dn1 maxDn1] :=
    ex_maximal_disjoint_subcollection (closure\o B) Hn1.
  suff: elt_prop (Dn1, n.+1, Un `|` Dn) by move=> H; exists (exist _ _ H).
  by split => //=; case: maxDn1 => + _ _ => /subset_trans; apply => i [[]].
pose D i := (sval (v i)).1.1.
pose U i := (sval (v i)).2.
have UE n : U n = \bigcup_(i < n) D i.
  elim: n => [|n ih]; first by rewrite bigcup_mkord big_ord0 /U /sval /D Hv0.
  by rewrite /U /sval/= (HvRel n).1 bigcup_mkord big_ord_recr -bigcup_mkord -ih.
pose v_ i := (sval (v i)).1.2.
have v_E n : v_ n = n.
  elim: n => /= [|n]; first by rewrite /v_ /sval/= Hv0.
  by move: (HvRel n).2; rewrite -!/(v_ _) => <- ->.
have maxD m : maximal_disjoint_subcollection (closure\o B) (D m)
    (H_ m (\bigcup_(i < m) D i)).
  by rewrite -(UE m) -[m in H_ m _]v_E /v_ /U /D; move: (v m) => [x []].
have DH m : D m `<=` H_ m (\bigcup_(i < m) D i) by have [] := maxD m.
exists (\bigcup_k D k); split.
- apply: bigcup_countable => // n _.
  apply: (@separated_closed_ball_countable R _ B) => //.
  have [_ + _] := maxD n; move=> DB i j Dni Dnj.
  by rewrite -!is_ball_closure//; exact: DB.
- by move=> i [n _ Dni]; have [+ _ _] := maxD n; move/(_ _ Dni) => [[]].
- apply: trivIset_bigcup => m; first by have [] := maxD m.
  move=> n i j mn Dmi Dnj.
  wlog : i j n m mn Dmi Dnj / (m < n)%N.
    move=> wlg ij.
    move: mn; rewrite neq_lt => /orP[mn|nm].
      by rewrite (wlg i j n m)// ?lt_eqF.
    by rewrite (wlg j i m n)// ?lt_eqF// setIC.
  move=> {}mn.
  have [_ {}H] := DH _ _ Dnj.
  move=> /set0P/eqP; apply: contra_notP => /eqP.
  by rewrite eq_sym setIC; apply: H => //; exists m.
move=> i Vi.
have [n Bni] := ex_vitali_collection_partition Bset0 VBr Vi.
have [[j Dj BiBj]|] :=
    pselect (exists2 j, (\bigcup_(i < n.+1) D i) j &
             closure (B i) `&` closure (B j) !=set0); last first.
  move/forall2NP => H.
  have {}H j : (\bigcup_(i < n.+1) D i) j ->
               closure (B i) `&` closure (B j) = set0.
   by have [//|/nonemptyPn] := H j.
  have H_i : (H_ n (\bigcup_(i < n) D i)) i.
    split => // s Hs si; apply: H => //.
    by move: Hs => [m /= nm Dms]; exists m => //=; rewrite (ltn_trans nm).
  have Dn_Bi j : D n j -> closure (B i) `&` closure (B j) = set0.
    by move=> Dnj; apply: H; exists n => //=.
  have [Dni|Dni] := pselect (D n i).
    have := Dn_Bi _ Dni.
      rewrite setIid => /closure_eq0 Bi0.
      by have := Bset0 i; rewrite Bi0 radius0/= ltxx.
  have not_tB : ~ trivIset (D n `|` [set i]) (closure \o B).
    have [_ _] := maxD n.
    apply.
      split; first exact: subsetUl.
      by move=> x; apply/Dni; apply: x; right.
    by rewrite subUset; split; [exact: DH|]; rewrite sub1set inE.
  have [p [q [pq Dnpi Dnqi pq0]]] : exists p q, [/\ p != q,
      D n p \/ p = i, D n q \/ q = i &
      closure (B p) `&` closure (B q) !=set0].
    move/trivIsetP : not_tB => /existsNP[p not_tB]; exists p.
    move/existsNP : not_tB => [q not_tB]; exists q.
    move/not_implyP : not_tB => [Dnip] /not_implyP[Dni1] /not_implyP[pq pq0].
    by split => //; exact/set0P/eqP.
  case: Dnpi => [Dnp|pi].
  - case: Dnqi => [Dnq|qi].
    + case: (maxD n) => _ + _.
      move/trivIsetP => /(_ _ _ Dnp Dnq pq).
      by move/set0P : pq0 => /eqP.
    + have := Dn_Bi _ Dnp.
      by rewrite setIC -qi; move/set0P : pq0 => /eqP.
  - case: Dnqi => [Dnq|qi].
    + have := Dn_Bi _ Dnq.
      by rewrite -pi; move/set0P : pq0 => /eqP.
    + by move: pq; rewrite pi qi eqxx.
have Birn : (radius (B i))%:num <= r / (2 ^ n)%:R.
  by move: Bni; by rewrite /B_ /= => -[_] /andP[].
have Bjrn : (radius (B j))%:num > r / (2 ^ n.+1)%:R.
  have : \bigcup_(i < n.+1) D i `<=` \bigcup_(i < n.+1) (B_ i).
    move=> k [m/= mn] Dmk.
    have [+ _ _] := maxD m.
    by move/(_ _ Dmk) => -[Bmk] _; exists m.
  move/(_ _ Dj) => [m/= mn1] [_] /andP[+ _].
  apply: le_lt_trans.
  rewrite ler_pM2l ?(vitali_collection_partition_ub_gt0 Bset0 VBr Vi)//.
  by rewrite lef_pV2// ?posrE ?ltr0n ?expn_gt0// ler_nat leq_pexp2l.
exists j; split => //.
- by case: Dj => m /= mn Dm; exists m.
- rewrite (le_trans _ (ltW Bjrn))// ler_pdivrMr// expnSr natrM.
  by rewrite invfM -!mulrA mulVf// mulr1.
- move=> x Bix.
  rewrite is_ball_closure//; last first.
    by rewrite (ballE (is_ballB j)) scale_ballE; [exact: is_ball_ball|].
  rewrite closed_ballE; last first.
    rewrite (ballE (is_ballB j)) scale_ballE; last by [].
    by rewrite radius_ball_num ?mulr_ge0// mulr_gt0.
  rewrite /closed_ball_ /= cpoint_scale_ball; [|by []..].
  rewrite radius_scale_ball//.
  apply: (@le_trans _ _ (2 * (radius (B i))%:num + (radius (B j))%:num)).
    case: BiBj => y [Biy Bjy].
    rewrite (le_trans (ler_distD y _ _))// [in leRHS]addrC lerD//.
      exact: is_ball_closureP.
    rewrite (le_trans (ler_distD (cpoint (B i)) _ _))//.
    rewrite (_ : 2 = 1 + 1); last by [].
    rewrite mulrDl !mul1r// lerD; [by []| |exact: is_ball_closureP].
    by rewrite distrC; exact: is_ball_closureP.
  rewrite -lerBrDr// -(@natr1 _ 4).
  rewrite (mulrDl 4%:R) mul1r addrK (natrM _ 2 2) -mulrA ler_pM2l//.
  rewrite (le_trans Birn)// [in leRHS]mulrC -ler_pdivrMr//.
  by rewrite -mulrA -invfM -natrM -expnSr ltW.
Qed.

Lemma vitali_lemma_infinite_cover : { D : set I | [/\ countable D,
  D `<=` V, trivIset D (closure \o B) &
  cover V (closure \o B) `<=` cover D (closure \o scale_ball 5%:R \o B)] }.
Proof.
have [D [cD DV tD maxD]] := vitali_lemma_infinite.
exists D; split => // x [i Vi] cBix/=.
by have [j [Dj BiBj ij]] := maxD i Vi; move/(_ _ cBix) => ?; exists j.
Qed.

End vitali_lemma_infinite.
