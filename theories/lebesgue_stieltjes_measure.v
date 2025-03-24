(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat archimedean.
From HB Require Import structures.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions fsbigop cardinality.
From mathcomp Require Import reals ereal interval_inference topology numfun.
From mathcomp Require Import normedtype sequences esum real_interval measure.
From mathcomp Require Import realfun.

(**md**************************************************************************)
(* # Lebesgue Stieltjes Measure                                               *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue-Stieltjes measure using *)
(* the Measure Extension theorem from measure.v.                              *)
(*                                                                            *)
(* References:                                                                *)
(* - Achim Klenke, Probability Theory 2nd edition, 2014                       *)
(* - Y. Ishiguro, R. Affeldt. The Radon-Nikodym Theorem and the Lebesgue-     *)
(*   Stieltjes measure in Coq. Computer Software 41(2) 2024                   *)
(*                                                                            *)
(* ```                                                                        *)
(*           right_continuous f == the function f is right-continuous         *)
(*                 cumulative R == type of non-decreasing, right-continuous   *)
(*                                 functions (with R : numFieldType)          *)
(*                                 The HB class is Cumulative.                *)
(*                                 instance: idfun                            *)
(*                 ocitv_type R == alias for R : realType                     *)
(*                        ocitv == set of open-closed intervals ]x, y] where  *)
(*                                 x and y are real numbers                   *)
(*                     R.-ocitv == display for ocitv_type R                   *)
(*         R.-ocitv.-measurable == semiring of sets of open-closed intervals  *)
(*                  wlength f A := f b - f a with the hull of the set of real *)
(*                                 numbers A being delimited by a and b       *)
(* lebesgue_stieltjes_measure f == Lebesgue-Stieltjes measure for f           *)
(*                                 f is a cumulative function.                *)
(* completed_lebesgue_stieltjes_measure f == the completed Lebesgue-Stieltjes *)
(*                                 measure                                    *)
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

Reserved Notation "R .-ocitv" (at level 1, format "R .-ocitv").
Reserved Notation "R .-ocitv.-measurable"
 (at level 2, format "R .-ocitv.-measurable").

(* TODO: move? *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

Lemma right_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> right_continuous f.
Proof. by move=> cf x; apply: cvg_within_filter; exact/cf. Qed.

HB.mixin Record isCumulative (R : numFieldType) (f : R -> R) := {
  cumulative_is_nondecreasing : {homo f : x y / x <= y} ;
  cumulative_is_right_continuous : right_continuous f }.

#[short(type=cumulative)]
HB.structure Definition Cumulative (R : numFieldType) :=
  { f of isCumulative R f }.

Arguments cumulative_is_nondecreasing {R} _.
Arguments cumulative_is_right_continuous {R} _.

Lemma nondecreasing_right_continuousP (R : numFieldType) (a : R) (e : R)
    (f : cumulative R) :
  e > 0 -> exists d : {posnum R}, f (a + d%:num) <= f a + e.
Proof.
move=> e0; move: (cumulative_is_right_continuous f).
move=> /(_ a) /(@cvgr_dist_lt _ R^o) /(_ _ e0)[] _ /posnumP[d] => h.
exists (PosNum [gt0 of (d%:num / 2)]) => //=.
move: h => /(_ (a + d%:num / 2)) /=.
rewrite opprD addrA subrr distrC subr0 ger0_norm //.
rewrite ltr_pdivrMr// ltr_pMr// ltr1n => /(_ erefl).
rewrite ltrDl divr_gt0// => /(_ erefl).
rewrite ler0_norm; last first.
  by rewrite subr_le0 (cumulative_is_nondecreasing f)// lerDl.
by rewrite opprB ltrBlDl => fa; exact: ltW.
Qed.

Section id_is_cumulative.
Variable R : realType.

Let id_nd : {homo @idfun R : x y / x <= y}.
Proof. by []. Qed.

Let id_rc : right_continuous (@idfun R).
Proof. by apply/right_continuousW => x; exact: cvg_id. Qed.

HB.instance Definition _ := isCumulative.Build R idfun id_nd id_rc.
End id_is_cumulative.
(* /TODO: move? *)

Section itv_semiRingOfSets.
Variable R : realType.
Implicit Types (I J K : set R).
Definition ocitv_type : Type := R.

Definition ocitv := [set `]x.1, x.2]%classic | x in [set: R * R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Proof. by exists (a, b); split => //=; rewrite in_itv/= andbT. Qed.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma ocitv0 : ocitv set0.
Proof. by exists (1, 0); rewrite //= set_itv_ge ?bnd_simp//= ltr10. Qed.
Hint Resolve ocitv0 : core.

Lemma ocitvP X : ocitv X <-> X = set0 \/ exists2 x, x.1 < x.2 & X = `]x.1, x.2]%classic.
Proof.
split=> [[x _ <-]|[->//|[x xlt ->]]]//.
case: (boolP (x.1 < x.2)) => x12; first by right; exists x.
by left; rewrite set_itv_ge.
Qed.

Lemma ocitvD : semi_setD_closed ocitv.
Proof.
move=> _ _ [a _ <-] /ocitvP[|[b ltb]] ->.
  rewrite setD0; exists [set `]a.1, a.2]%classic].
  by split=> [//|? ->//||? ? -> ->//]; rewrite bigcup_set1.
rewrite setDE setCitv/= setIUr -!set_itvI.
rewrite /Order.meet/= /Order.meet/= /Order.join/=
         ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
rewrite -negb_or le_total/=; set c := minr _ _; set d := maxr _ _.
have inside : a.1 < c -> d < a.2 -> `]a.1, c] `&` `]d, a.2] = set0.
  rewrite -subset0 lt_min gt_max => /andP[a12 ab1] /andP[_ ba2] x /= [].
  have b1a2 : b.1 <= a.2 by rewrite ltW// (lt_trans ltb).
  have a1b2 : a.1 <= b.2 by rewrite ltW// (lt_trans _ ltb).
  rewrite /c /d (min_idPr _)// (max_idPr _)// !in_itv /=.
  move=> /andP[a1x xb1] /andP[b2x xa2].
  by have := lt_le_trans b2x xb1; case: ltgtP ltb.
exists ((if a.1 < c then [set `]a.1, c]%classic] else set0) `|`
        (if d < a.2 then [set `]d, a.2]%classic] else set0)); split.
- by rewrite finite_setU; do! case: ifP.
- by move=> ? []; case: ifP => ? // ->//=.
- by rewrite bigcup_setU; congr (_ `|` _);
     case: ifPn => ?; rewrite ?bigcup_set1 ?bigcup_set0// set_itv_ge.
- move=> I J/=; case: ifP => //= ac; case: ifP => //= da [] // -> []// ->.
    by rewrite inside// => -[].
  by rewrite setIC inside// => -[].
Qed.

Lemma ocitvI : setI_closed ocitv.
Proof.
move=> _ _ [a _ <-] [b _ <-]; rewrite -set_itvI/=.
rewrite /Order.meet/= /Order.meet /Order.join/=
        ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
by rewrite -negb_or le_total/=.
Qed.

Definition ocitv_display : Type -> measure_display. Proof. exact. Qed.

HB.instance Definition _ := Pointed.on ocitv_type.
HB.instance Definition _ :=
  @isSemiRingOfSets.Build (ocitv_display R)
    ocitv_type ocitv ocitv0 ocitvI ocitvD.

End itv_semiRingOfSets.

Notation "R .-ocitv" := (ocitv_display R) : measure_display_scope.
Notation "R .-ocitv.-measurable" := (measurable : set (set (ocitv_type R))) :
  classical_set_scope.

Local Open Scope measure_display_scope.

Section wlength.
Context {R : realType}.
Variable (f : R -> R).
Local Open Scope ereal_scope.
Implicit Types i j : interval R.

Let g : \bar R -> \bar R := er_map f.

Definition wlength (A : set (ocitv_type R)) : \bar R :=
  let i := Rhull A in g i.2 - g i.1.

Lemma wlength0 : wlength (set0 : set R) = 0.
Proof. by rewrite /wlength Rhull0 /= subee. Qed.

Lemma wlength_singleton (r : R) : wlength `[r, r] = 0.
Proof.
rewrite /wlength /= asboolT// sup_itvcc//= asboolT//.
by rewrite asboolT inf_itvcc//= ?subee// inE.
Qed.

Lemma wlength_setT : wlength setT = +oo%E :> \bar R.
Proof. by rewrite /wlength RhullT. Qed.

Lemma wlength_itv i : wlength [set` i] = if i.2 > i.1 then g i.2 - g i.1 else 0.
Proof.
case: ltP => [/lt_ereal_bnd/neitvP i12|]; first by rewrite /wlength set_itvK.
rewrite le_eqVlt => /orP[|/lt_ereal_bnd i12]; last first.
  rewrite -wlength0; congr (wlength _).
  by apply/eqP/negPn; rewrite -/(neitv _) neitvE -leNgt (ltW i12).
case: i => -[ba a|[|]] [bb b|[|]] //=.
- rewrite /= => /eqP[->{b}]; move: ba bb => -[] []; try
    by rewrite set_itvE wlength0.
  by rewrite wlength_singleton.
- by move=> _; rewrite set_itvE wlength0.
- by move=> _; rewrite set_itvE wlength0.
Qed.

Lemma wlength_finite_fin_num i : neitv i -> wlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Proof.
move: i => [[ba a|[]] [bb b|[]]] /neitvP //=; do ?by rewrite ?set_itvE ?eqxx.
by move=> _; rewrite wlength_itv /= ltry.
by move=> _; rewrite wlength_itv /= ltNye.
by move=> _; rewrite wlength_itv.
Qed.

Lemma finite_wlength_itv i : neitv i -> wlength [set` i] < +oo ->
  wlength [set` i] = (fine (g i.2))%:E - (fine (g i.1))%:E.
Proof.
move=> i0 ioo; have [i1f i2f] := wlength_finite_fin_num i0 ioo.
rewrite fineK; last first.
  by rewrite /g; move: i2f; case: (ereal_of_itv_bound i.2).
rewrite fineK; last first.
  by rewrite /g; move: i1f; case: (ereal_of_itv_bound i.1).
rewrite wlength_itv; case: ifPn => //; rewrite -leNgt le_eqVlt => /predU1P[->|].
  by rewrite subee// /g; move: i1f; case: (ereal_of_itv_bound i.1).
by move/lt_ereal_bnd/ltW; rewrite leNgt; move: i0 => /neitvP => ->.
Qed.

Lemma wlength_itv_bnd (a b : R) (x y : bool) : (a <= b)%R ->
  wlength [set` Interval (BSide x a) (BSide y b)] = (f b - f a)%:E.
Proof.
move=> ab; rewrite wlength_itv/= lte_fin lt_neqAle ab andbT.
by have [-> /=|/= ab'] := eqVneq a b; rewrite ?subrr// EFinN EFinB.
Qed.

Lemma wlength_infty_bnd b r :
  wlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Proof. by rewrite wlength_itv /= ltNye. Qed.

Lemma wlength_bnd_infty b r :
  wlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Proof. by rewrite wlength_itv /= ltey. Qed.

Lemma pinfty_wlength_itv i : wlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Proof.
rewrite wlength_itv; case: i => -[ba a|[]] [bb b|[]] //= => [|_|_|].
- by case: ifPn.
- by left; exists ba, a; right.
- by left; exists bb, b; left.
- by right.
Qed.

Lemma wlength_itv_ge0 (ndf : {homo f : x y / (x <= y)%R}) i :
  0 <= wlength [set` i].
Proof.
rewrite wlength_itv; case: ifPn => //; case: (i.1 : \bar _) => [r| |].
- by rewrite suber_ge0// => /ltW /(le_er_map ndf).
- by rewrite ltNge leey.
- case: (i.2 : \bar _) => //=; last by rewrite leey.
  by move=> r _; rewrite leey.
Qed.

Lemma wlength_Rhull (A : set R) : wlength [set` Rhull A] = wlength A.
Proof. by rewrite /wlength Rhull_involutive. Qed.

Lemma le_wlength_itv (ndf : {homo f : x y / (x <= y)%R}) i j :
  {subset i <= j} -> wlength [set` i] <= wlength [set` j].
Proof.
set I := [set` i]; set J := [set` j].
have [->|/set0P I0] := eqVneq I set0; first by rewrite wlength0 wlength_itv_ge0.
have [J0|/set0P J0] := eqVneq J set0.
  by move/subset_itvP; rewrite -/J J0 subset0 -/I => ->.
move=> /subset_itvP ij; apply: leeB => /=.
  have [ui|ui] := asboolP (has_ubound I).
    have [uj /=|uj] := asboolP (has_ubound J); last by rewrite leey.
    rewrite lee_fin; apply: ndf; apply/le_sup => //.
    by move=> r Ir; exists r; split => //; apply: ij.
  have [uj /=|//] := asboolP (has_ubound J).
  by move: ui; have := subset_has_ubound ij uj.
have [lj /=|lj] := asboolP (has_lbound J); last by rewrite leNye.
have [li /=|li] := asboolP (has_lbound I); last first.
  by move: li; have := subset_has_lbound ij lj.
rewrite lee_fin; apply/ndf/le_inf => //.
move=> r [r' Ir' <-{r}]; exists (- r')%R.
by split => //; exists r' => //; apply: ij.
Qed.

Lemma le_wlength (ndf : {homo f : x y / (x <= y)%R}) :
  {homo wlength : A B / A `<=` B >-> A <= B}.
Proof.
move=> a b /le_Rhull /(le_wlength_itv ndf).
by rewrite (wlength_Rhull a) (wlength_Rhull b).
Qed.

End wlength.

Section wlength_extension.
Context {R : realType}.

Lemma wlength_semi_additive (f : R -> R) : measure.semi_additive (wlength f).
Proof.
move=> /= I n /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym-/funext {I}->.
move=> Itriv [[/= a1 a2] _] /esym /[dup] + ->.
rewrite wlength_itv ?lte_fin/= -EFinB.
case: ifPn => a12; last first.
  pose I i := `](b i).1, (b i).2]%classic.
  rewrite set_itv_ge//= -(bigcup_mkord _ I) /I => /bigcup0P I0.
  by under eq_bigr => i _ do rewrite I0//= wlength0; rewrite big1.
set A := `]a1, a2]%classic.
rewrite -bigcup_pred; set P := xpredT; rewrite (eq_bigl P)//.
move: P => P; have [p] := ubnP #|P|; elim: p => // p IHp in P a2 a12 A *.
rewrite ltnS => cP /esym AE.
have : A a2 by rewrite /A /= in_itv/= lexx andbT.
rewrite AE/= => -[i /= Pi] a2bi.
case: (boolP ((b i).1 < (b i).2)) => bi; last by rewrite itv_ge in a2bi.
have {}a2bi : a2 = (b i).2.
  apply/eqP; rewrite eq_le (itvP a2bi)/=.
  suff: A (b i).2 by move=> /itvP->.
  by rewrite AE; exists i=> //=; rewrite in_itv/= lexx andbT.
rewrite {a2}a2bi in a12 A AE *.
rewrite (bigD1 i)//= wlength_itv ?lte_fin/= bi !EFinD -addeA.
congr (_ + _)%E; apply/eqP; rewrite addeC -sube_eq// 1?adde_defC//.
rewrite ?EFinN oppeK addeC; apply/eqP.
have [a1bi|a1bi] := eqVneq a1 (b i).1.
  rewrite {a1}a1bi in a12 A AE {IHp} *; rewrite subee ?big1// => j.
  move=> /andP[Pj Nji]; rewrite wlength_itv ?lte_fin/=; case: ifPn => bj//.
  exfalso; have /trivIsetP/(_ j i I I Nji) := Itriv.
  pose m := ((b j).1 + (b j).2) / 2%:R.
  have mbj : `](b j).1, (b j).2]%classic m.
     by rewrite /= !in_itv/= ?(midf_lt, midf_le)//= ltW.
  rewrite -subset0 => /(_ m); apply; split=> //.
  by suff: A m by []; rewrite AE; exists j.
have a1b2 j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj/=.
have a1b j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).1.
  move=> Pj bj; case: ltP=> // bj1a.
  suff : A a1 by rewrite /A/= in_itv/= ltxx.
  by rewrite AE; exists j; rewrite //= in_itv/= bj1a//= a1b2.
have bbi2 j : P j -> (b j).1 < (b j).2 -> (b j).2 <= (b i).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj/=.
apply/IHp.
- by rewrite lt_neqAle a1bi/= a1b.
- rewrite (leq_trans _ cP)// -(cardID (pred1 i) P).
  rewrite [X in (_ < X + _)%N](@eq_card _ _ (pred1 i)); last first.
    by move=> j; rewrite !inE andbC; case: eqVneq => // ->.
  rewrite ?card1 ?ltnS// subset_leq_card//.
  by apply/fintype.subsetP => j; rewrite -topredE/= !inE andbC.
apply/seteqP; split=> /= [x [j/= /andP[Pj Nji]]|x/= xabi].
  case: (boolP ((b j).1 < (b j).2)) => bj; last by rewrite itv_ge.
  apply: subitvP; rewrite subitvE ?bnd_simp a1b//= leNgt.
  have /trivIsetP/(_ j i I I Nji) := Itriv.
  rewrite -subset0 => /(_ (b j).2); apply: contra_notN => /= bi1j2.
  by rewrite !in_itv/= bj !lexx bi1j2 bbi2.
have: A x.
  rewrite /A/= in_itv/= (itvP xabi)/= ltW//.
  by rewrite (le_lt_trans _ bi) ?(itvP xabi).
rewrite AE => -[j /= Pj xbj].
exists j => //=.
apply/andP; split=> //; apply: contraTneq xbj => ->.
by rewrite in_itv/= le_gtF// (itvP xabi).
Qed.

Lemma wlength_ge0 (f : cumulative R) (I : set (ocitv_type R)) :
  (0 <= wlength f I)%E.
Proof.
by rewrite -(wlength0 f) le_wlength//; exact: cumulative_is_nondecreasing.
Qed.

#[local] Hint Extern 0 (0%:E <= wlength _ _) => solve[apply: wlength_ge0] : core.

HB.instance Definition _ (f : cumulative R) :=
  isContent.Build _ _ R (wlength f)
    (wlength_ge0 f)
    (wlength_semi_additive f).

Hint Extern 0 (measurable _) => solve [apply: is_ocitv] : core.

Lemma cumulative_content_sub_fsum (f : cumulative R) (D : {fset nat}) a0 b0
    (a b : nat -> R) : (forall i, i \in D -> a i <= b i) ->
    `]a0, b0] `<=` \big[setU/set0]_(i <- D) `]a i, b i]%classic ->
  f b0 - f a0 <= \sum_(i <- D) (f (b i) - f (a i)).
Proof.
move=> Dab h; have [ab|ab] := leP a0 b0; last first.
  apply (@le_trans _ _ 0).
    by rewrite subr_le0 cumulative_is_nondecreasing// ltW.
  rewrite big_seq sumr_ge0// => i iD.
  by rewrite subr_ge0 cumulative_is_nondecreasing// Dab.
have mab k : [set` D] k -> R.-ocitv.-measurable `]a k, b k]%classic by [].
move: h; rewrite -bigcup_fset.
move/(content_sub_fsum (wlength f) (finite_fset D) mab (is_ocitv a0 b0)) => /=.
rewrite wlength_itv_bnd// -lee_fin => /le_trans; apply.
rewrite -sumEFin fsbig_finite//= set_fsetK// big_seq [in leRHS]big_seq.
by apply: lee_sum => i iD; rewrite wlength_itv_bnd// Dab.
Qed.

Lemma wlength_sigma_subadditive (f : cumulative R) :
  measurable_subset_sigma_subadditive (wlength f).
Proof.
move=> I A /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym AE => -[a _ <-].
rewrite /subset_sigma_subadditive wlength_itv ?lte_fin/= -EFinB => lebig.
case: ifPn => a12; last by rewrite nneseries_esum ?esum_ge0.
wlog wlogh : b A AE lebig / forall n, (b n).1 <= (b n).2.
  move=> /= h.
  set A' := fun n => if (b n).1 >= (b n).2 then set0 else A n.
  set b' := fun n => if (b n).1 >= (b n).2 then (0, 0) else b n.
  rewrite [leRHS](_ : _ = \sum_(n <oo) wlength f (A' n))%E; last first.
    apply: (@eq_eseriesr _ (wlength f \o A) (wlength f \o A')) => k.
    rewrite /= /A' AE; case: ifPn => // bn.
    by rewrite set_itv_ge//= bnd_simp -leNgt.
  apply: (h b').
  - move=> k; rewrite /A'; case: ifPn => // bk.
    by rewrite set_itv_ge//= bnd_simp -leNgt /b' bk.
  - by rewrite AE /b' (negbTE bk).
  - apply: (subset_trans lebig); apply subset_bigcup => k _.
    rewrite /A' AE; case: ifPn => bk //.
    by rewrite subset0 set_itv_ge//= bnd_simp -leNgt.
  - by move=> k; rewrite /b'; case: ifPn => //; rewrite -ltNge => /ltW.
apply/lee_addgt0Pr => _/posnumP[e].
rewrite [e%:num]splitr [in leRHS]EFinD addeA -leeBlDr//.
apply: le_trans (epsilon_trick _ _ _) => //=.
have [c ce] := nondecreasing_right_continuousP a.1 f [gt0 of e%:num / 2].
have [D De] : exists D : nat -> {posnum R}, forall i,
    f ((b i).2 + (D i)%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
  suff : forall i, exists di : {posnum R},
      f ((b i).2 + di%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
    by move/choice => -[g hg]; exists g.
  by move=> k; apply nondecreasing_right_continuousP.
have acbd : `[ a.1 + c%:num / 2, a.2] `<=`
            \bigcup_i `](b i).1, (b i).2 + (D i)%:num[%classic.
  apply: (@subset_trans _ `]a.1, a.2]).
    move=> r; rewrite /= !in_itv/= => /andP [+ ->].
    by rewrite andbT; apply: lt_le_trans; rewrite ltrDl.
  apply: (subset_trans lebig) => r [n _ Anr]; exists n => //.
  move: Anr; rewrite AE /= !in_itv/= => /andP [->]/= /le_lt_trans.
  by apply; rewrite ltrDl.
have := @segment_compact _ (a.1 + c%:num / 2) a.2; rewrite compact_cover.
have obd k : [set: nat] k -> open `](b k).1, ((b k).2 + (D k)%:num)[%classic.
  by move=> _; exact: interval_open.
move=> /(_ _ _ _ obd acbd){obd acbd}.
case=> X _ acXbd.
rewrite /cover in acXbd.
rewrite -EFinD.
apply: (@le_trans _ _ (\sum_(i <- X) (wlength f `](b i).1, (b i).2]%classic) +
    \sum_(i <- X) (f ((b i).2 + (D i)%:num)%R - f (b i).2)%:E)%E).
  apply: (@le_trans _ _ (f a.2 - f (a.1 + c%:num / 2))%:E).
    rewrite lee_fin -addrA -opprD lerB// (le_trans _ ce)//.
    rewrite cumulative_is_nondecreasing//.
    by rewrite lerD2l ler_pdivrMr// ler_pMr// ler1n.
  apply: (@le_trans _ _
      (\sum_(i <- X) (f ((b i).2 + (D i)%:num) - f (b i).1)%:E)%E).
    rewrite sumEFin lee_fin cumulative_content_sub_fsum//.
      by move=> k kX; rewrite (@le_trans _ _ (b k).2)// lerDl.
    apply: subset_trans.
      exact/(subset_trans _ acXbd)/subset_itv_oc_cc.
    move=> x [k kX] kx; rewrite -bigcup_fset; exists k => //.
    by move: x kx; exact: subset_itv_oo_oc.
  rewrite addeC -big_split/=; apply: lee_sum => k _.
  by rewrite !(EFinB, wlength_itv_bnd)// addeA subeK.
rewrite -big_split/= nneseries_esum//; last by move=> k _; rewrite adde_ge0.
rewrite esum_ge//; exists [set` X] => //; rewrite fsbig_finite//= set_fsetK.
rewrite big_seq [in X in (_ <= X)%E]big_seq; apply: lee_sum => k kX.
by rewrite AE leeD2l// lee_fin lerBlDl natrX De.
Qed.

HB.instance Definition _ (f : cumulative R) :=
  Content_SigmaSubAdditive_isMeasure.Build _ _ _
    (wlength f) (wlength_sigma_subadditive f).

Lemma wlength_sigma_finite (f : R -> R) :
  sigma_finite [set: (ocitv_type R)] (wlength f).
Proof.
exists (fun k => `](- k%:R), k%:R]%classic).
  apply/esym; rewrite -subTset => /= x _ /=.
  exists `|(floor `|x| + 1)%R|%N; rewrite //= in_itv/=.
  rewrite !natr_absz intr_norm intrD.
  suff: `|x| < `|(floor `|x|)%:~R + 1| by rewrite ltr_norml => /andP[-> /ltW->].
  rewrite [ltRHS]ger0_norm//.
    by rewrite intrD1 (le_lt_trans _ (lt_succ_floor _))// ?ler_norm.
  by rewrite addr_ge0// ler0z floor_ge0.
move=> k; split => //; rewrite wlength_itv /= -EFinB.
by case: ifP; rewrite ltey.
Qed.

Definition lebesgue_stieltjes_measure (f : cumulative R) :=
  measure_extension (wlength f).
HB.instance Definition _ (f : cumulative R) :=
  Measure.on (lebesgue_stieltjes_measure f).

Let sigmaT_finite_lebesgue_stieltjes_measure (f : cumulative R) :
  sigma_finite setT (lebesgue_stieltjes_measure f).
Proof. exact/measure_extension_sigma_finite/wlength_sigma_finite. Qed.

HB.instance Definition _ (f : cumulative R) := @Measure_isSigmaFinite.Build _ _ _
  (lebesgue_stieltjes_measure f) (sigmaT_finite_lebesgue_stieltjes_measure f).

End wlength_extension.
Arguments lebesgue_stieltjes_measure {R}.

#[deprecated(since="mathcomp-analysis 1.1.0", note="renamed `wlength_sigma_subadditive`")]
Notation wlength_sigma_sub_additive := wlength_sigma_subadditive (only parsing).

Section lebesgue_stieltjes_measure.
Variable R : realType.
Let gitvs : measurableType _ := g_sigma_algebraType (@ocitv R).

Lemma lebesgue_stieltjes_measure_unique (f : cumulative R)
    (mu : {measure set gitvs -> \bar R}) :
    (forall X, ocitv X -> lebesgue_stieltjes_measure f X = mu X) ->
  forall X, measurable X -> lebesgue_stieltjes_measure f X = mu X.
Proof.
move=> muE X mX; apply: measure_extension_unique => //=.
  exact: wlength_sigma_finite.
by move=> A mA; rewrite -muE// -measurable_mu_extE.
Qed.

End lebesgue_stieltjes_measure.

Section completed_lebesgue_stieltjes_measure.
Context {R : realType}.

Definition completed_lebesgue_stieltjes_measure (f : cumulative R) :=
  @completed_measure_extension _ _ _ (wlength f).

HB.instance Definition _ (f : cumulative R) :=
  Measure.on (@completed_lebesgue_stieltjes_measure f).

Let sigmaT_finite_completed_lebesgue_stieltjes_measure (f : cumulative R) :
  sigma_finite setT (@completed_lebesgue_stieltjes_measure f).
Proof. exact/completed_measure_extension_sigma_finite/wlength_sigma_finite. Qed.

HB.instance Definition _ (f : cumulative R) :=
  @Measure_isSigmaFinite.Build _ _ _
    (@completed_lebesgue_stieltjes_measure f)
    (sigmaT_finite_completed_lebesgue_stieltjes_measure f).

End completed_lebesgue_stieltjes_measure.
Arguments completed_lebesgue_stieltjes_measure {R}.
