(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop reals.
From mathcomp Require Import interval_inference ereal topology numfun tvs.
From mathcomp Require Import normedtype function_spaces sequences esum measure.
From mathcomp Require Import real_interval realfun exp.
From mathcomp Require Export measurable_realfun lebesgue_stieltjes_measure.

(**md**************************************************************************)
(* # Lebesgue Measure                                                         *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue measure using the       *)
(* Measure Extension theorem from measure.v, and proves properties of the     *)
(* Lebesgue measure such as Vitali's theorem, i.e., given a Vitali cover $V$  *)
(* of $A$, there exists a countable subcollection $D \subseteq V$ of pairwise *)
(* disjoint closed balls such that $\lambda(A \setminus \bigcup_k D_k) = 0$.  *)
(*                                                                            *)
(* Main references:                                                           *)
(* - Daniel Li. Intégration et applications. 2016                             *)
(* - Achim Klenke. Probability Theory 2nd edition. 2014                       *)
(* - R. Affeldt, C. Cohen. Measure Construction by Extension in Dependent     *)
(*   Type Theory with Application to Integration. JAR 2023                    *)
(*                                                                            *)
(* ```                                                                        *)
(*           lebesgue_measure == the Lebesgue measure                         *)
(* completed_lebesgue_measure == the completed Lebesgue measure               *)
(*          elebesgue_measure == the Lebesgue measure extended to \bar R      *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*     vitali_cover A B V == V is a Vitali cover of A, here B is a            *)
(*                           collection of non-empty closed balls             *)
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

(* This module contains a direct construction of the Lebesgue measure that is
   kept here for archival purpose. The Lebesgue measure is actually defined as
   an instance of the Lebesgue-Stieltjes measure. *)
Module LebesgueMeasure.
Section hlength.
Context {R : realType}.
Local Open Scope ereal_scope.
Implicit Types i j : interval R.

Definition hlength (A : set (ocitv_type R)) : \bar R :=
  let i := Rhull A in (i.2 : \bar R) - i.1.

Lemma hlength0 : hlength (set0 : set R) = 0.
Proof. by rewrite /hlength Rhull0 /= subee. Qed.

Lemma hlength_singleton (r : R) : hlength `[r, r] = 0.
Proof.
rewrite /hlength /= asboolT// sup_itvcc//= asboolT//.
by rewrite asboolT inf_itvcc//= ?subee// inE.
Qed.

Lemma hlength_setT : hlength setT = +oo%E :> \bar R.
Proof. by rewrite /hlength RhullT. Qed.

Lemma hlength_itv i :
  hlength [set` i] = if i.2 > i.1 then (i.2 : \bar R) - i.1 else 0.
Proof.
case: ltP => [/lt_ereal_bnd/neitvP i12|]; first by rewrite /hlength set_itvK.
rewrite le_eqVlt => /orP[|/lt_ereal_bnd i12]; last first.
  rewrite (_ : [set` i] = set0) ?hlength0//.
  by apply/eqP/negPn; rewrite -/(neitv _) neitvE -leNgt (ltW i12).
case: i => -[ba a|[|]] [bb b|[|]] //=.
- rewrite /= => /eqP[->{b}]; move: ba bb => -[] []; try
    by rewrite set_itvE hlength0.
  by rewrite hlength_singleton.
- by move=> _; rewrite set_itvE hlength0.
- by move=> _; rewrite set_itvE hlength0.
Qed.

Lemma hlength_finite_fin_num i : neitv i -> hlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Proof.
move: i => [[ba a|[]] [bb b|[]]] /neitvP //=; do ?by rewrite ?set_itvE ?eqxx.
by move=> _; rewrite hlength_itv /= ltry.
by move=> _; rewrite hlength_itv /= ltNyr.
by move=> _; rewrite hlength_itv.
Qed.

Lemma finite_hlength_itv i : neitv i -> hlength [set` i] < +oo ->
  hlength [set` i] = (fine i.2)%:E - (fine i.1)%:E.
Proof.
move=> i0 ioo; have [ri1 ri2] := hlength_finite_fin_num i0 ioo.
rewrite !fineK// hlength_itv; case: ifPn => //.
rewrite -leNgt le_eqVlt => /predU1P[->|]; first by rewrite subee.
by move/lt_ereal_bnd/ltW; rewrite leNgt; move: i0 => /neitvP => ->.
Qed.

Lemma hlength_infty_bnd b r :
  hlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltNyr. Qed.

Lemma hlength_bnd_infty b r :
  hlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltry. Qed.

Lemma infinite_hlength_itv i : hlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Proof.
rewrite hlength_itv; case: i => -[ba a|[]] [bb b|[]] //= => [|_|_|].
- by case: ifPn.
- by left; exists ba, a; right.
- by left; exists bb, b; left.
- by right.
Qed.

Lemma hlength_itv_ge0 i : 0 <= hlength [set` i].
Proof.
rewrite hlength_itv; case: ifPn => //; case: (i.1 : \bar _) => [r| |].
- by rewrite suber_ge0//; exact: ltW.
- by rewrite ltNge leey.
- by move=> i2gtNy; rewrite addey//; case: (i.2 : \bar R) i2gtNy.
Qed.

Lemma hlength_Rhull (A : set R) : hlength [set` Rhull A] = hlength A.
Proof. by rewrite /hlength Rhull_involutive. Qed.

Lemma le_hlength_itv i j : {subset i <= j} -> hlength [set` i] <= hlength [set` j].
Proof.
set I := [set` i]; set J := [set` j].
have [->|/set0P I0] := eqVneq I set0; first by rewrite hlength0 hlength_itv_ge0.
have [J0|/set0P J0] := eqVneq J set0.
  by move/subset_itvP; rewrite -/J J0 subset0 -/I => ->.
move=> /subset_itvP ij; apply: leeB => /=.
  have [ui|ui] := asboolP (has_ubound I).
    have [uj /=|uj] := asboolP (has_ubound J); last by rewrite leey.
    by rewrite lee_fin le_sup // => r Ir; exists r; split => //; apply: ij.
  have [uj /=|//] := asboolP (has_ubound J).
  by move: ui; have := subset_has_ubound ij uj.
have [lj /=|lj] := asboolP (has_lbound J); last by rewrite leNye.
have [li /=|li] := asboolP (has_lbound I); last first.
  by move: li; have := subset_has_lbound ij lj.
rewrite lee_fin lerNl opprK le_sup// ?has_inf_supN//; last exact/nonemptyN.
move=> r [r' Ir' <-{r}]; exists (- r')%R.
by split => //; exists r' => //; apply: ij.
Qed.

Lemma le_hlength : {homo hlength : A B / (A `<=` B) >-> A <= B}.
Proof.
move=> a b /le_Rhull /le_hlength_itv.
by rewrite (hlength_Rhull a) (hlength_Rhull b).
Qed.

Lemma hlength_ge0 I : (0 <= hlength I)%E.
Proof. by rewrite -hlength0 le_hlength. Qed.

End hlength.
#[local] Hint Extern 0 (is_true (0%R <= hlength _)) =>
  solve[apply: hlength_ge0] : core.

(* Unused *)
(* Lemma hlength_semi_additive2 : semi_additive2 hlength. *)
(* Proof. *)
(* move=> I J /ocitvP[|[a a12]] ->; first by rewrite set0U hlength0 add0e. *)
(* move=> /ocitvP[|[b b12]] ->; first by rewrite setU0 hlength0 adde0. *)
(* rewrite -subset0 => + ab0 => /ocitvP[|[x x12] abx]. *)
(*   by rewrite setU_eq0 => -[-> ->]; rewrite setU0 hlength0 adde0. *)
(* rewrite abx !hlength_itv//= ?lte_fin a12 b12 x12/= -!EFinB -EFinD. *)
(* wlog ab1 : a a12 b b12 ab0 abx / a.1 <= b.1 => [hwlog|]. *)
(*   have /orP[ab1|ba1] := le_total a.1 b.1; first by apply: hwlog. *)
(*   by rewrite [in RHS]addrC; apply: hwlog => //; rewrite (setIC, setUC). *)
(* have := ab0; rewrite subset0 -set_itv_meet/=. *)
(* rewrite /Order.join /Order.meet/= ?(andbF, orbF)/= ?(meetEtotal, joinEtotal). *)
(* rewrite -negb_or le_total/=; set c := minr _ _; set d := maxr _ _. *)
(* move=> /eqP/neitvP/=; rewrite bnd_simp/= /d/c (max_idPr _)// => /negP. *)
(* rewrite -leNgt le_minl orbC lt_geF//= => {c} {d} a2b1. *)
(* have ab i j : i \in `]a.1, a.2] -> j \in `]b.1, b.2] -> i <= j. *)
(*   by move=> ia jb; rewrite (le_le_trans _ _ a2b1) ?(itvP ia) ?(itvP jb). *)
(* have /(congr1 sup) := abx; rewrite sup_setU// ?sup_itv_bounded// => bx. *)
(* have /(congr1 inf) := abx; rewrite inf_setU// ?inf_itv_bounded// => ax. *)
(* rewrite -{}ax -{x}bx in abx x12 *. *)
(* case: ltgtP a2b1 => // a2b1 _; last first. *)
(*   by rewrite a2b1 [in RHS]addrC subrKA. *)
(* exfalso; pose c := (a.2 + b.1) / 2%:R. *)
(* have /predeqP/(_ c)[_ /(_ _)/Box[]] := abx. *)
(*   apply: subset_itv_oo_oc; have := mid_in_itvoo a2b1. *)
(*   by apply/subitvP; rewrite subitvE ?bnd_simp/= ?ltW. *)
(* apply/not_orP; rewrite /= !in_itv/=. *)
(* by rewrite lt_geF ?midf_lt//= andbF le_gtF ?midf_le//= ltW. *)
(* Qed. *)

Section hlength_extension.
Context {R : realType}.

Notation hlength := (@hlength R).

Lemma hlength_semi_additive : measure.semi_additive hlength.
Proof.
move=> /= I n /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym-/funext {I}->.
move=> Itriv [[/= a1 a2] _] /esym /[dup] + ->.
rewrite hlength_itv ?lte_fin/= -EFinB.
case: ifPn => a12; last first.
  pose I i :=  `](b i).1, (b i).2]%classic.
  rewrite set_itv_ge//= -(bigcup_mkord _ I) /I => /bigcup0P I0.
  by under eq_bigr => i _ do rewrite I0//= hlength0; rewrite big1.
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
rewrite (bigD1 i)//= hlength_itv ?lte_fin/= bi !EFinD -addeA.
congr (_ + _)%E; apply/eqP; rewrite addeC -sube_eq// 1?adde_defC//.
rewrite ?EFinN oppeK addeC; apply/eqP.
case: (eqVneq a1 (b i).1) => a1bi.
  rewrite {a1}a1bi in a12 A AE {IHp} *; rewrite subee ?big1// => j.
  move=> /andP[Pj Nji]; rewrite hlength_itv ?lte_fin/=; case: ifPn => bj//.
  exfalso; have /trivIsetP/(_ j i I I Nji) := Itriv.
  pose m := ((b j).1 + (b j).2) / 2%:R.
  have mbj : `](b j).1, (b j).2]%classic m.
     by rewrite /= !in_itv/= ?(midf_lt, midf_le)//= ltW.
  rewrite -subset0 => /(_ m); apply; split=> //.
  by suff: A m by []; rewrite AE; exists j => //.
have a1b2 j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
have a1b j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).1.
  move=> Pj bj; case: ltP=> // bj1a.
  suff : A a1 by rewrite /A/= in_itv/= ltxx.
  by rewrite AE; exists j; rewrite //= in_itv/= bj1a//= a1b2.
have bbi2 j : P j -> (b j).1 < (b j).2 -> (b j).2 <= (b i).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
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

HB.instance Definition _ := isContent.Build _ _ R
  hlength hlength_ge0 hlength_semi_additive.

Hint Extern 0 ((_ .-ocitv).-measurable _) => solve [apply: is_ocitv] : core.

Lemma hlength_sigma_subadditive : measurable_subset_sigma_subadditive hlength.
Proof.
move=> I A /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym AE => -[a _ <-].
rewrite /subset_sigma_subadditive hlength_itv ?lte_fin/= -EFinB => lebig.
case: ifPn => a12; last by rewrite nneseries_esum// esum_ge0.
apply/lee_addgt0Pr => _ /posnumP[e].
rewrite [e%:num]splitr [in leRHS]EFinD addeA -leeBlDr//.
apply: le_trans (epsilon_trick _ _ _) => //=.
have eVn_gt0 n : 0 < e%:num / 2 / (2 ^ n.+1)%:R.
  by rewrite divr_gt0// ltr0n// expn_gt0.
have eVn_ge0 n := ltW (eVn_gt0 n).
pose Aoo i : set (ocitv_type R) :=
  `](b i).1, (b i).2 + e%:num / 2 / (2 ^ i.+1)%:R[%classic.
pose Aoc i : set (ocitv_type R) :=
  `](b i).1, (b i).2 + e%:num / 2 / (2 ^ i.+1)%:R]%classic.
have: `[a.1 + e%:num / 2, a.2] `<=` \bigcup_i Aoo i.
  apply: (@subset_trans _ `]a.1, a.2]).
    move=> x; rewrite /= !in_itv /= => /andP[+ -> //].
    by move=> /lt_le_trans-> //; rewrite ltrDl.
  apply: (subset_trans lebig); apply: subset_bigcup => i _; rewrite AE /Aoo/=.
  move=> x /=; rewrite !in_itv /= => /andP[-> /le_lt_trans->]//=.
  by rewrite ltrDl.
have := @segment_compact _ (a.1 + e%:num / 2) a.2; rewrite compact_cover.
move=> /[apply]-[i _|X _ Xc]; first exact: interval_open.
have: `](a.1 + e%:num / 2), a.2] `<=` \bigcup_(i in [set` X]) Aoc i.
  move=> x /subset_itv_oc_cc /Xc [i /= Xi] Aooix.
  by exists i => //; apply: subset_itv_oo_oc Aooix.
have /[apply] := @content_sub_fsum _ _ _ hlength _ [set` X].
move=> /(_ _ _ _)/Box[]//=; apply: le_le_trans.
  rewrite hlength_itv ?lte_fin -?EFinD/= -addrA -opprD.
  by case: ltP => //; rewrite lee_fin subr_le0.
rewrite nneseries_esum//; last by move=> *; rewrite adde_ge0//= ?lee_fin.
rewrite esum_ge//; exists [set` X] => //; rewrite fsbig_finite// ?set_fsetK//=.
rewrite fsbig_finite//= set_fsetK//.
rewrite lee_sum // => i _; rewrite ?AE// !hlength_itv/= ?lte_fin -?EFinD/=.
do !case: ifPn => //= ?; do ?by rewrite ?adde_ge0 ?lee_fin// ?subr_ge0// ?ltW.
  by rewrite addrAC.
by rewrite addrAC lee_fin lerD// subr_le0 leNgt.
Qed.

HB.instance Definition _ := Content_SigmaSubAdditive_isMeasure.Build _ _ _
  hlength hlength_sigma_subadditive.

Lemma hlength_sigma_finite : sigma_finite setT hlength.
Proof.
exists (fun k : nat => `] (- k%:R)%R, k%:R]%classic); first by rewrite bigcup_itvT.
by move=> k; split => //; rewrite hlength_itv/= -EFinB; case: ifP; rewrite ltry.
Qed.

Definition lebesgue_measure := measure_extension hlength.
HB.instance Definition _ := Measure.on lebesgue_measure.

Let sigmaT_finite_lebesgue_measure : sigma_finite setT lebesgue_measure.
Proof. exact/measure_extension_sigma_finite/hlength_sigma_finite. Qed.

HB.instance Definition _ := @isSigmaFinite.Build _ _ _
  lebesgue_measure sigmaT_finite_lebesgue_measure.

End hlength_extension.

End LebesgueMeasure.

Definition lebesgue_measure {R : realType} :
  set (g_sigma_algebraType R.-ocitv.-measurable) -> \bar R :=
  lebesgue_stieltjes_measure idfun.
HB.instance Definition _ (R : realType) := Measure.on (@lebesgue_measure R).
HB.instance Definition _ (R : realType) :=
  SigmaFiniteMeasure.on (@lebesgue_measure R).

Definition completed_lebesgue_measure {R : realType} : set _ -> \bar R :=
  completed_lebesgue_stieltjes_measure idfun.
HB.instance Definition _ (R : realType) :=
  Measure.on (@completed_lebesgue_measure R).
HB.instance Definition _ (R : realType) :=
  SigmaFiniteMeasure.on (@completed_lebesgue_measure R).

Lemma completed_lebesgue_measure_is_complete {R : realType} :
  measure_is_complete (@completed_lebesgue_measure R).
Proof. exact: measure_is_complete_caratheodory. Qed.

(* the completed sigma-algebra is the same as the caratheodory sigma-algebra *)
Section completed_algebra_caratheodory.
Context {R : realType}.
Local Open Scope ereal_scope.

Notation hlength := (@wlength R idfun).
Notation mu := (@lebesgue_measure R).
Notation completed_mu := (@completed_lebesgue_measure R).

Let cara_sub_calgebra : hlength^*%mu.-cara.-measurable `<=`
  (completed_algebra_gen mu).-sigma.-measurable.
Proof.
move=> E; wlog : E / completed_mu E < +oo.
  move=> /= wlg.
  have /sigma_finiteP[/= F [UFI ndF mF]] :=
    measure_extension_sigma_finite (@wlength_sigma_finite R idfun).
  move=> mE.
  rewrite -(setIT E)/= UFI setI_bigcupr; apply: bigcupT_measurable => i.
  apply: wlg.
  - rewrite (le_lt_trans _ (mF i).2)//= le_measure// inE/=.
    + by apply: measurableI => //; apply: sub_caratheodory; exact: (mF i).1.
    + by apply: sub_caratheodory; exact: (mF i).1.
  - by apply: measurableI => //; apply: sub_caratheodory; exact: (mF i).1.
move=> mEoo /= mE.
have inv0 n : (0 < n.+1%:R^-1 :> R)%R by rewrite invr_gt0.
set S := [set \sum_(0 <= k <oo) hlength (A k) | A in measurable_cover E].
have coverE s : (0 < s)%R ->
   exists2 A, @measurable_cover _ (ocitv_type R) E A &
   \sum_(0 <= k <oo) hlength (A k) < completed_mu E + s%:E.
  move=> s0; have : mu E \is a fin_num by rewrite ge0_fin_numE.
  by move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [A EA] <-] ?; exists A.
pose A n := projT1 (cid2 (coverE _ (inv0 n))).
have mA k : @measurable_cover _ (ocitv_type R) E (A k).
  by rewrite /A; case: cid2.
have mA_E n :
    \sum_(0 <= k <oo) hlength (A n k) < completed_mu E + n.+1%:R^-1%:E.
  by rewrite /A; case: cid2.
pose F_ n := \bigcup_m (A n m).
have EF_n n : E `<=` F_ n.
  have [/= _] := mA n.
  by move=> /subset_trans; apply; apply: subset_bigcup => i _.
have mF_ m : mu (F_ m) < completed_mu E + m.+1%:R^-1%:E.
  apply: (le_lt_trans _ (mA_E m)).
  apply: (le_trans (outer_measure_sigma_subadditive hlength^*%mu (A m))).
  apply: lee_nneseries => // n _.
  by rewrite -((measurable_mu_extE hlength) (A m n))//; have [/(_ n)] := mA m.
pose F := \bigcap_n (F_ n).
have FM : @measurable _ (g_sigma_algebraType R.-ocitv.-measurable) F.
  apply: bigcapT_measurable => k; apply: bigcupT_measurable => i.
  by apply: sub_sigma_algebra; have [/(_ i)] := mA k.
have EF : E `<=` F by exact: sub_bigcap.
have muEF : completed_mu E = mu F.
  apply/eqP; rewrite eq_le le_outer_measure//=.
  apply/lee_addgt0Pr => /= _/posnumP[e]; near \oo => n.
  apply: (@le_trans _ _ (mu (F_ n))).
    by apply: le_outer_measure; exact: bigcap_inf.
  rewrite (le_trans (ltW (mF_ n)))// leeD// lee_fin ltW//.
  by near: n; apply: near_infty_natSinv_lt.
have coverEF s : (0 < s)%R ->
     exists2 A, @measurable_cover _ (ocitv_type R) (F `\` E) A &
     \sum_(0 <= k <oo) hlength (A k) < completed_mu (F `\` E) + s%:E.
  move=> s0.
  have : mu (F `\` E) \is a fin_num.
    rewrite ge0_fin_numE// (@le_lt_trans _ _ (mu F))//; last by rewrite -muEF.
    by apply: le_outer_measure; exact: subDsetl.
  by move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [B FEB] <-] ?; exists B.
pose B n := projT1 (cid2 (coverEF _ (inv0 n))).
have mB k : @measurable_cover _ (ocitv_type R) (F `\` E) (B k).
  by rewrite /B; case: cid2.
have mB_FE n :
    \sum_(0 <= k <oo) hlength (B n k) < completed_mu (F `\` E) + n.+1%:R^-1%:E.
  by rewrite /B; case: cid2.
pose G_ n := \bigcup_m (B n m).
have FEG_n n : F `\` E `<=` G_ n.
  have [/= _] := mB n.
  by move=> /subset_trans; apply; apply: subset_bigcup => i _.
have mG_ m : mu (G_ m) < completed_mu (F `\` E) + m.+1%:R^-1%:E.
  apply: (le_lt_trans _ (mB_FE m)).
  apply: (le_trans (outer_measure_sigma_subadditive hlength^*%mu (B m))).
  apply: lee_nneseries => // n _.
  by rewrite -((measurable_mu_extE hlength) (B m n))//; have [/(_ n)] := mB m.
pose G := \bigcap_n (G_ n).
have GM : @measurable _ (g_sigma_algebraType R.-ocitv.-measurable) G.
  apply: bigcapT_measurable => k; apply: bigcupT_measurable => i.
  by apply: sub_sigma_algebra; have [/(_ i)] := mB k.
have FEG : F `\` E `<=` G by exact: sub_bigcap.
have muG : mu G = 0.
  transitivity (completed_mu (F `\` E)).
    apply/eqP; rewrite eq_le; apply/andP; split; last exact: le_outer_measure.
    apply/lee_addgt0Pr => _/posnumP[e].
    near \oo => n.
    apply: (@le_trans _ _ (mu (G_ n))).
      by apply: le_outer_measure; exact: bigcap_inf.
    rewrite (le_trans (ltW (mG_ n)))// leeD// lee_fin ltW//.
    by near: n; apply: near_infty_natSinv_lt.
  rewrite measureD//=.
  + by rewrite setIidr// muEF subee// ge0_fin_numE//; move: mEoo; rewrite muEF.
  + exact: sub_caratheodory.
  + by move: mEoo; rewrite muEF.
apply: sub_sigma_algebra; exists (F `\` G); first exact: measurableD.
exists (E `&` G).
  by apply: (@negligibleS _ _ _ mu G _ (@subIsetr _ E G)); exists G; split.
apply/seteqP; split=> [/= x [[Fx Gx]|[]//]|x Ex].
- by rewrite -(notK (E x)) => Ex; apply: Gx; exact: FEG.
- have [|FGx] := pselect ((F `\` G) x); first by left.
  right; split => //.
  move/not_andP : FGx => [|].
    by have := EF _ Ex.
  by rewrite notK.
Unshelve. all: by end_near. Qed.

Lemma g_sigma_completed_algebra_genE :
  (completed_algebra_gen mu).-sigma.-measurable = completed_algebra_gen mu.
Proof.
apply/seteqP; split; last first.
  move=> _ [/= A /= mA [N neglN]] <-.
  by apply: sub_sigma_algebra; exists A => //; exists N.
apply: smallest_sub => //=; split => /=.
- by exists set0 => //; exists set0; [exact: negligible_set0|rewrite setU0].
- move=> G [/= A mA [N negN ANG]]; case: negN => /= F [mF F0 NF].
  have GANA : ~` G = ~` A `\` (N `&` ~` A).
    by rewrite -ANG setCU setDE setCI setCK setIUr setICl setU0.
  pose AA := ~` A `\` (F `&` ~` A).
  pose NN := (F `&` ~` A) `\` (N `&` ~` A).
  have GAANN : ~` G = AA `|` NN.
    rewrite (_ : ~` G = ~` A `\` (N `&` ~` A))//.
    by apply: setDU; [exact: setSI|exact: subIsetr].
  exists AA.
    apply: measurableI => //=; first exact: measurableC.
    by apply: measurableC; apply: measurableI => //; exact: measurableC.
  by exists NN; [exists F; split => // x [] []|rewrite setDE setTI].
- move=> F mF/=.
  pose A n := projT1 (cid2 (mF n)).
  pose N n := projT1 (cid2 (projT2 (cid2 (mF n))).2).
  exists (\bigcup_k A k).
    by apply: bigcupT_measurable => i; rewrite /A; case: cid2.
  exists (\bigcup_k N k).
    apply: negligible_bigcup => /= k.
    by rewrite /N; case: (cid2 (mF k)) => //= *; case: cid2.
  rewrite -bigcupU; apply: eq_bigcup => // i _.
  by rewrite /A /N; case: (cid2 (mF i)) => //= *; case: cid2.
Qed.

Lemma negligible_sub_caratheodory :
  completed_mu.-negligible `<=` hlength^*%mu.-cara.-measurable.
Proof.
move=> N /= [/= A] [mA A0 NA].
apply: le_caratheodory_measurable => /= X.
apply: (@le_trans _ _ (hlength^*%mu N + hlength^*%mu (X `&` ~` N))).
  by rewrite leeD2r// le_outer_measure//; exact: subIsetr.
have -> : hlength^*%mu N = 0.
  by apply/eqP; rewrite eq_le outer_measure_ge0//= andbT -A0 le_outer_measure.
by rewrite add0e// le_outer_measure//; exact: subIsetl.
Qed.

Let calgebra_sub_cara : (completed_algebra_gen mu).-sigma.-measurable `<=`
  hlength^*%mu.-cara.-measurable.
Proof.
rewrite g_sigma_completed_algebra_genE => A -[/= X mX] [N negN] <-{A}.
apply: measurableU => //; first exact: sub_caratheodory.
apply: negligible_sub_caratheodory; case: negN => /= B [mB B0 NB].
by exists B; split => //=; exact: sub_caratheodory.
Qed.

Lemma completed_caratheodory_measurable :
  (completed_algebra_gen mu).-sigma.-measurable =
  hlength^*%mu.-cara.-measurable.
Proof.
by apply/seteqP; split; [exact: calgebra_sub_cara | exact: cara_sub_calgebra].
Qed.

End completed_algebra_caratheodory.

Section elebesgue_measure.
Variable R : realType.

Definition elebesgue_measure : set \bar R -> \bar R :=
  fun S => lebesgue_measure (fine @` (S `\` [set -oo; +oo]%E)).

Lemma elebesgue_measure0 : elebesgue_measure set0 = 0%E.
Proof. by rewrite /elebesgue_measure set0D image_set0 measure0. Qed.

Lemma elebesgue_measure_ge0 X : (0 <= elebesgue_measure X)%E.
Proof. exact/measure_ge0. Qed.

Lemma semi_sigma_additive_elebesgue_measure :
  semi_sigma_additive elebesgue_measure.
Proof.
move=> /= F mF tF mUF; rewrite /elebesgue_measure.
rewrite [X in lebesgue_measure X](_ : _ =
    \bigcup_n (fine @` (F n `\` [set -oo; +oo]%E))); last first.
  rewrite predeqE => r; split.
    by move=> [x [[n _ Fnx xoo <-]]]; exists n => //; exists x.
  by move=> [n _ [x [Fnx xoo <-{r}]]]; exists x => //; split => //; exists n.
apply: (@measure_semi_sigma_additive _ _ _ (@lebesgue_measure R)
  (fun n => fine @` (F n `\` [set -oo; +oo]%E))).
- move=> n; have := mF n.
  move=> [X mX [X' mX']] XX'Fn.
  apply: measurable_image_fine.
  rewrite -XX'Fn.
  apply: measurableU; first exact: measurable_image_EFin.
  by case: mX' => //; exact: measurableU.
- move=> i j _ _ [x [[a [Fia aoo ax] [b [Fjb boo] bx]]]].
  move: tF => /(_ i j Logic.I Logic.I); apply.
  suff ab : a = b by exists a; split => //; rewrite ab.
  move: a b {Fia Fjb} aoo boo ax bx.
  move=> [a| |] [b| |] /=.
  + by move=> _ _ -> ->.
  + by move=> _; rewrite not_orP => -[_]/(_ erefl).
  + by move=> _; rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
- move: mUF.
  rewrite {1}/measurable /emeasurable /= => -[X mX [Y []]] {Y}.
  - rewrite setU0 => h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-{r}]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[x' Xx' <-].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|xoo']; move/not_orP : xoo => -[].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - (* NB: almost the same as the previous one, factorize?*)
    move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|xoo']; move/not_orP : xoo => -[].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ elebesgue_measure
  elebesgue_measure0 elebesgue_measure_ge0
  semi_sigma_additive_elebesgue_measure.

End elebesgue_measure.

Section lebesgue_measure_itv.
Variable R : realType.

Let lebesgue_measure_itvoc (a b : R) :
  (lebesgue_measure (`]a, b] : set R) = wlength idfun `]a, b])%classic.
Proof.
rewrite /lebesgue_measure/= /lebesgue_stieltjes_measure/= /measure_extension/=.
by rewrite measurable_mu_extE//; exact: is_ocitv.
Qed.

Let lebesgue_measure_itvoo_subr1 (a : R) :
  lebesgue_measure (`]a - 1, a[%classic : set R) = 1%E.
Proof.
rewrite itv_bnd_open_bigcup//; transitivity (limn (lebesgue_measure \o
    (fun k => `]a - 1, a - k.+1%:R^-1]%classic : set R))).
  apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
  - by move=> ?; exact: measurable_itv.
  - by apply: bigcup_measurable => k _; exact: measurable_itv.
  - move=> n m nm; apply/subsetPset => x /=; rewrite !in_itv/= => /andP[->/=].
    by move/le_trans; apply; rewrite lerB// ler_pV2 ?ler_nat//;
      rewrite inE ltr0n andbT unitfE.
rewrite (_ : _ \o _ = (fun n => (1 - n.+1%:R^-1)%:E)); last first.
  apply/funext => n /=; rewrite lebesgue_measure_itvoc.
  have [->|n0] := eqVneq n 0%N.
    by rewrite invr1 subrr set_itvoc0 wlength0.
  rewrite wlength_itv/= lte_fin ifT; last first.
    by rewrite ler_ltB// invr_lt1 ?unitfE// ltr1n ltnS lt0n.
  by rewrite !(EFinB,EFinN) fin_num_oppeB// addeAC addeA subee// add0e.
apply/cvg_lim => //=; apply/fine_cvgP; split => /=; first exact: nearW.
apply/(@cvgrPdist_lt _ R^o) => _/posnumP[e].
near=> n; rewrite opprB addrCA subrr addr0 ger0_norm//.
by near: n; exact: near_infty_natSinv_lt.
Unshelve. all: by end_near. Qed.

Lemma lebesgue_measure_set1 (a : R) : lebesgue_measure [set a] = 0%E.
Proof.
suff : (lebesgue_measure (`]a - 1, a]%classic%R : set R) =
        lebesgue_measure (`]a - 1, a[%classic%R : set R) +
        lebesgue_measure [set a])%E.
  rewrite lebesgue_measure_itvoo_subr1 lebesgue_measure_itvoc => /eqP.
  rewrite wlength_itv lte_fin ltrBlDr ltrDl ltr01.
  rewrite [in X in X == _]/= EFinN EFinB fin_num_oppeB// addeA subee// add0e.
  by rewrite addeC -sube_eq ?fin_num_adde_defl// subee// => /eqP.
rewrite -setUitv1// ?bnd_simp; last by rewrite ltrBlDr ltrDl.
rewrite measureU //; apply/seteqP; split => // x []/=.
by rewrite in_itv/= => + xa; rewrite xa ltxx andbF.
Qed.

Let lebesgue_measure_itvoo (a b : R) :
  (lebesgue_measure (`]a, b[ : set R) = wlength idfun `]a, b[)%classic.
Proof.
have [ab|ba] := ltP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_measure_itvoc a b.
rewrite 2!wlength_itv => <-; rewrite -setUitv1// measureU//.
- by have /= -> := lebesgue_measure_set1 b; rewrite adde0.
- by apply/seteqP; split => // x [/= + xb]; rewrite in_itv/= xb ltxx andbF.
Qed.

Let lebesgue_measure_itvcc (a b : R) :
  (lebesgue_measure (`[a, b] : set R) = wlength idfun `[a, b])%classic.
Proof.
have [ab|ba] := leP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_measure_itvoc a b.
rewrite 2!wlength_itv => <-; rewrite -setU1itv// measureU//.
- by have /= -> := lebesgue_measure_set1 a; rewrite add0e.
- by apply/seteqP; split => // x [/= ->]; rewrite in_itv/= ltxx.
Qed.

Let lebesgue_measure_itvco (a b : R) :
  (lebesgue_measure (`[a, b[ : set R) = wlength idfun `[a, b[)%classic.
Proof.
have [ab|ba] := ltP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_measure_itvoo a b.
rewrite 2!wlength_itv => <-; rewrite -setU1itv// measureU//.
- by have /= -> := lebesgue_measure_set1 a; rewrite add0e.
- by apply/seteqP; split => // x [/= ->]; rewrite in_itv/= ltxx.
Qed.

Let lebesgue_measure_itv_bnd (x y : bool) (a b : R) :
  lebesgue_measure ([set` Interval (BSide x a) (BSide y b)] : set R) =
  wlength idfun [set` Interval (BSide x a) (BSide y b)].
Proof.
by move: x y => [|] [|]; [exact: lebesgue_measure_itvco |
  exact: lebesgue_measure_itvcc | exact: lebesgue_measure_itvoo |
  exact: lebesgue_measure_itvoc].
Qed.

Let limnatR : lim (((k%:R)%:E : \bar R) @[k --> \oo]) = +oo%E.
Proof. by apply/cvg_lim => //; apply/cvgenyP. Qed.

Let lebesgue_measure_itv_bnd_infty x (a : R) :
  lebesgue_measure ([set` Interval (BSide x a) +oo%O] : set R) = +oo%E.
Proof.
rewrite itv_bndy_bigcup_BRight; transitivity (limn (lebesgue_measure \o
    (fun k => [set` Interval (BSide x a) (BRight (a + k%:R))] : set R))).
  apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
  + by move=> k; exact: measurable_itv.
  + by apply: bigcup_measurable => k _; exact: measurable_itv.
  + move=> m n mn; apply/subsetPset => r/=; rewrite !in_itv/= => /andP[->/=].
    by move=> /le_trans; apply; rewrite lerD// ler_nat.
rewrite (_ : _ \o _ = (fun k => k%:R%:E))//.
apply/funext => n /=; rewrite lebesgue_measure_itv_bnd wlength_itv/=.
rewrite lte_fin;  have [->|n0] := eqVneq n 0%N; first by rewrite addr0 ltxx.
by rewrite ltrDl ltr0n lt0n n0 EFinD addeAC EFinN subee ?add0e.
Qed.

Let lebesgue_measure_itv_infty_bnd y (b : R) :
  lebesgue_measure ([set` Interval -oo%O (BSide y b)] : set R) = +oo%E.
Proof.
rewrite itvNy_bnd_bigcup_BLeft; transitivity (limn (lebesgue_measure \o
    (fun k => [set` Interval (BLeft (b - k%:R)) (BSide y b)] : set R))).
  apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
  + by move=> k; exact: measurable_itv.
  + by apply: bigcup_measurable => k _; exact: measurable_itv.
  + move=> m n mn; apply/subsetPset => r/=; rewrite !in_itv/= => /andP[+ ->].
    by rewrite andbT; apply: le_trans; rewrite lerB// ler_nat.
rewrite (_ : _ \o _ = (fun k : nat => k%:R%:E))//.
apply/funext => n /=; rewrite lebesgue_measure_itv_bnd wlength_itv/= lte_fin.
have [->|n0] := eqVneq n 0%N; first by rewrite subr0 ltxx.
rewrite ltrBlDr ltrDl ltr0n lt0n n0 EFinN EFinB fin_num_oppeB// addeA.
by rewrite subee// add0e.
Qed.

Let lebesgue_measure_itv_infty_infty :
  lebesgue_measure ([set` Interval -oo%O +oo%O] : set R) = +oo%E.
Proof.
rewrite set_itvNyy -(setUv (`]-oo, 0[)) setCitv.
rewrite [X in _ `|` (X `|` _) ]set_itvE set0U measureU//; last first.
  apply/seteqP; split => //= x [] /= /[swap].
  by rewrite !in_itv/= andbT ltNge => ->//.
rewrite [X in (X + _)%E]lebesgue_measure_itv_infty_bnd.
by rewrite [X in (_ + X)%E]lebesgue_measure_itv_bnd_infty.
Qed.

Lemma lebesgue_measure_itv (i : interval R) :
  lebesgue_measure ([set` i] : set R) =
  (if i.1 < i.2 then (i.2 : \bar R) - i.1 else 0)%E.
Proof.
move: i => [[x a|[|]]] [y b|[|]].
  by rewrite lebesgue_measure_itv_bnd wlength_itv.
- by rewrite set_itvE ?measure0.
- by rewrite lebesgue_measure_itv_bnd_infty/= ltry.
- by rewrite lebesgue_measure_itv_infty_bnd/= ltNyr.
- by rewrite set_itvE ?measure0.
- by rewrite lebesgue_measure_itv_infty_infty.
- by rewrite set_itvE ?measure0.
- by rewrite set_itvE ?measure0.
- by rewrite set_itvE ?measure0.
Qed.

Lemma lebesgue_measure_ball (x r : R) : (0 <= r)%R ->
  lebesgue_measure (ball x r) = (r *+ 2)%:E.
Proof.
rewrite le_eqVlt => /predU1P[ <-|r0].
  by rewrite (ball0 _ _).2// measure0 mul0rn.
rewrite ball_itv lebesgue_measure_itv/= lte_fin ltrBlDr -addrA ltrDl.
by rewrite addr_gt0 // -EFinD addrAC opprD opprK addrA subrr add0r -mulr2n.
Qed.

Lemma lebesgue_measure_closed_ball (x r : R) : 0 <= r ->
  lebesgue_measure (closed_ball x r) = (r *+ 2)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-|r0].
  by rewrite mul0rn closed_ball0// measure0.
rewrite closed_ball_itv// lebesgue_measure_itv/= lte_fin -ltrBlDl addrAC.
rewrite subrr add0r gtrN// ?mulr_gt0// -EFinD; congr (_%:E).
by rewrite opprB addrAC addrCA subrr addr0 -mulr2n.
Qed.

End lebesgue_measure_itv.

Section compact_finite_measure.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.

Lemma compact_finite_measure (A : set R) : compact A -> (mu A < +oo)%E.
Proof.
move=> /[dup]/compact_measurable => mA /compact_bounded[N [_ N1x]].
have AN1 : A `<=` `[- (`|N| + 1), `|N| + 1].
  by move=> z Az; rewrite set_itvcc /= -ler_norml N1x// ltr_pwDr// ler_norm.
rewrite (le_lt_trans (le_measure _ _ _ AN1)) ?inE//=.
by rewrite lebesgue_measure_itv/= lte_fin gtrN// EFinD ltry.
Qed.

End compact_finite_measure.

Lemma lebesgue_measure_rat (R : realType) :
  lebesgue_measure (range ratr : set R) = 0%E.
Proof.
have /pcard_eqP/bijPex[f bijf] := card_rat; set f1 := 'pinv_(fun=> 0) setT f.
rewrite (_ : range _ = \bigcup_n [set ratr (f1 n)]); last first.
  apply/seteqP; split => [_ [q _ <-]|_ [n _ /= ->]]; last by exists (f1 n).
  exists (f q) => //=; rewrite /f1 pinvKV// ?in_setE// => x y _ _.
  by apply: bij_inj; rewrite -setTT_bijective.
rewrite measure_bigcup//; last first.
  apply/trivIsetP => i j _ _ ij; apply/seteqP; split => //= _ [/= ->].
  move=> /fmorph_inj.
  have /set_bij_inj /[apply] := bijpinv_bij (fun=> 0) bijf.
  by rewrite in_setE => /(_ Logic.I Logic.I); exact/eqP.
by rewrite eseries0// => n _ _; exact: lebesgue_measure_set1.
Qed.

Section negligible_outer_measure.
Context {R : realType}.
Implicit Types (A : set R).
Local Open Scope ereal_scope.

Let l := (@wlength R idfun).
Let mu := (@lebesgue_measure R).

Lemma outer_measure_open_le A (e : R) : (0 < e)%R ->
  exists U, [/\ open U, A `<=` U & mu U <= (l^* A)%mu + e%:E].
Proof.
have [|Aoo e0] := leP +oo (l^* A)%mu.
  rewrite leye_eq => /eqP Aoo e0.
  by exists [set: R]; split => //; [exact: openT|rewrite Aoo leey].
have [F AF Fe] : exists2 I_, open_itv_cover A I_ &
    \sum_(0 <= k <oo) l (I_ k) <= (l^* A)%mu + e%:E.
  have : (l^* A)%mu\is a fin_num by rewrite ge0_fin_numE ?outer_measure_ge0.
  rewrite outer_measure_open_itv_cover.
  move=> /lb_ereal_inf_adherent-/(_ _ e0)[_/= [F]] AF <- Fe.
  by exists F => //; exact/ltW.
exists (\bigcup_i F i); split.
- apply: bigcup_open => // i _.
  by case: AF => /(_ i)[ab -> _]; exact: interval_open.
- by case: AF.
- rewrite (le_trans _ Fe)//.
  apply: (le_trans (outer_measure_sigma_subadditive mu F)).
  apply: lee_nneseries => // i _.
  case: AF => /(_ i)[[a b] -> _]/=.
  by rewrite /l wlength_itv/= -(@lebesgue_measure_itv R `]a, b[).
Qed.

Lemma outer_measure_open A : (l^* A)%mu =
  ereal_inf [set (l^* U)%mu | U in [set U | open U /\ A `<=` U]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: lb_ereal_inf => /= _ /= [U [oU AU] <-]; exact: le_outer_measure.
apply/lee_addgt0Pr => /= e e0; apply: ereal_inf_le.
have [U [oU AU UAe]] := @outer_measure_open_le A _ e0.
by exists (mu U) => //=; exists U.
Qed.

Lemma outer_measure_Gdelta A :
  exists G : (set R)^nat, [/\ (forall i, open (G i)),
    A `<=` \bigcap_i G i &
    mu (\bigcap_i G i) = (l^* A)%mu].
Proof.
have inv0 k : (0 < k.+1%:R^-1 :> R)%R by rewrite invr_gt0.
pose F k := projT1 (cid (outer_measure_open_le A (inv0 k))).
have oF k : open (F k) by rewrite /F; case: cid => x /= [].
have AF k : A `<=` F k by rewrite /F; case: cid => x /= [].
have mF k : mu (F k) <= (l^* A)%mu + k.+1%:R^-1%:E.
  by rewrite /F; case: cid => x /= [].
pose G := \bigcap_k (F k).
exists F; split => //; first exact: sub_bigcap.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply/lee_addgt0Pr => /= _/posnumP[e].
  near \oo => k.
  apply: (@le_trans _ _ ((l^* A)%mu + k.+1%:R^-1%:E)).
    by rewrite (le_trans _ (mF k))// le_outer_measure//; exact: bigcap_inf.
  rewrite leeD2l// lee_fin; apply: ltW.
  by near: k; exact: near_infty_natSinv_lt.
rewrite [leRHS](_ : _ = l^* (\bigcap_i F i))%mu// le_outer_measure//.
exact: sub_bigcap.
Unshelve. all: by end_near. Qed.

Lemma negligible_outer_measure (N : set R) : mu.-negligible N <-> (l^* N)%mu = 0.
Proof.
split=> [[/= A [mA mA0 NA]]|N0].
- by apply/eqP; rewrite eq_le outer_measure_ge0 andbT -mA0 le_outer_measure.
- have := @outer_measure_Gdelta N; rewrite N0 => -[F [oF NF mF0]].
  exists (\bigcap_i F i); split => //=.
  by apply: bigcapT_measurable => i; exact: open_measurable.
Qed.

End negligible_outer_measure.

Section lebesgue_regularity.
Local Open Scope ereal_scope.
Context {R : realType}.
Let mu : measure _ _ := @lebesgue_measure R.

Lemma lebesgue_regularity_outer (D : set R) (eps : R) :
  measurable D -> mu D < +oo -> (0 < eps)%R ->
  exists U : set R, [/\ open U , D `<=` U & mu (U `\` D) < eps%:E].
Proof.
move=> mD muDoo epspos.
have /ereal_inf_lt[z [/= M' covDM sMz zDe]] : mu D < mu D + (eps / 2)%:E.
  by rewrite lte_spaddre ?lte_fin ?divr_gt0// ge0_fin_numE.
pose e2 n := ((eps / 2) / (2 ^ n.+1)%:R)%R.
have e2pos n : (0 < e2 n)%R by rewrite ?divr_gt0.
pose M n := if pselect (M' n = set0) then set0 else
            (`] inf (M' n), sup (M' n) + e2 n [%classic)%R.
have muM n : mu (M n) <= mu (M' n) + (e2 n)%:E.
  rewrite /M; case: pselect => /= [->|].
    by rewrite measure0 add0e lee_fin ltW.
  have /ocitvP[-> //| [[a b /= alb -> ab0]]] : ocitv (M' n).
    by case: covDM  => /(_ n).
  rewrite inf_itv// sup_itv//.
  have -> : (`]a, (b + e2 n)%R[ = `]a, b] `|` `]b, (b + e2 n)%R[ )%classic.
    apply: funext=> r /=; rewrite (@itv_splitU _ _ (BRight b)).
      by rewrite propeqE; split=> /orP.
    by rewrite !bnd_simp (ltW alb)/= ltr_pwDr.
  rewrite measureU/=.
  - rewrite !lebesgue_measure_itv/= !lte_fin alb ltr_pwDr//=.
    by rewrite -(EFinD (b + e2 n)) (addrC b) addrK.
  - by apply: sub_sigma_algebra; exact: is_ocitv.
  - by apply: open_measurable; exact: interval_open.
  - rewrite eqEsubset; split => // r []/andP [_ +] /andP[+ _] /=.
    by rewrite !bnd_simp => /le_lt_trans /[apply]; rewrite ltxx.
pose U := \bigcup_n M n.
exists U; have DU : D `<=` U.
  case: (covDM) => _ /subset_trans; apply; apply: subset_bigcup.
  rewrite /M => n _ x; case: pselect => [/= -> //|].
  have /ocitvP [-> //| [[/= a b alb -> mn]]] : ocitv (M' n).
    by case: covDM => /(_ n).
  rewrite /= !in_itv/= => /andP[ax xb]; rewrite ?inf_itv ?sup_itv//.
  by rewrite ax/= (le_lt_trans xb)// ltr_pwDr.
have mM n : measurable (M n).
  rewrite /M; case: pselect; first by move=> /= _; exact: measurable0.
  by move=> /= _; apply: open_measurable; apply: interval_open.
have muU : mu U < mu D + eps%:E.
  apply: (@le_lt_trans _ _ (\sum_(n <oo) mu (M n))).
    exact: outer_measure_sigma_subadditive.
  apply: (@le_lt_trans _ _ (\sum_(n <oo) (mu (M' n) + (e2 n)%:E))).
    by rewrite lee_nneseries.
  apply: le_lt_trans.
    by apply: epsilon_trick => //; rewrite divr_ge0// ltW.
  rewrite {2}[eps]splitr EFinD addeA lte_leD//.
  rewrite (le_lt_trans _ zDe)// -sMz lee_nneseries// => i _.
  rewrite /= -wlength_Rhull wlength_itv !er_map_idfun.
  rewrite -lebesgue_measure_itv le_measure//= ?inE.
  - by case: covDM => /(_ i) + _; exact: sub_sigma_algebra.
  - exact: measurable_itv.
  - exact: sub_Rhull.
split => //.
  apply: bigcup_open => n _.
  by rewrite /M; case: pselect => /= _; [exact: open0|exact: interval_open].
rewrite measureD//=.
- by rewrite setIidr// lte_subel_addl// ge0_fin_numE// (lt_le_trans muU)// leey.
- by apply: bigcup_measurable => k _; exact: mM.
- by rewrite (lt_le_trans muU)// leey.
Qed.

Lemma lebesgue_nearly_bounded (D : set R) (eps : R) :
    measurable D -> mu D < +oo -> (0 < eps)%R ->
  exists ab : R * R, mu (D `\` [set` `[ab.1,ab.2]]) < eps%:E.
Proof.
move=> mD Dfin epspos; pose Dn n := D `&` [set` `[-(n%:R), n%:R]]%R.
have mDn n : measurable (Dn n) by exact: measurableI.
have : mu \o Dn @ \oo --> mu (\bigcup_n Dn n).
  apply: nondecreasing_cvg_mu => //.
  - by apply: bigcup_measurable => // ? _; exact: mDn.
  - move=> n m nm; apply/subsetPset; apply: setIS => z /=; rewrite !in_itv/=.
    move=> /andP[nz zn]; rewrite (le_trans _ nz)/= ?(le_trans zn) ?ler_nat//.
    by rewrite lerNl opprK ler_nat.
rewrite -setI_bigcupr; rewrite bigcup_itvT setIT.
have finDn n : mu (Dn n) \is a fin_num.
  rewrite ge0_fin_numE// (le_lt_trans _ Dfin)//.
  by rewrite le_measure// ?inE//=; [exact: mDn|exact: subIsetl].
have finD : mu D \is a fin_num by rewrite fin_num_abs gee0_abs.
rewrite -[mu D]fineK// => /fine_cvg/(_ (interior (ball (fine (mu D)) eps)))[].
  exact/nbhs_interior/nbhsx_ballx.
move=> n _ /(_ _ (leqnn n))/interior_subset muDN.
exists (-n%:R, n%:R)%R; rewrite measureD//=.
move: muDN; rewrite /ball/= /ereal_ball/= -fineB//=; last exact: finDn.
rewrite -lte_fin; apply: le_lt_trans.
have finDDn : mu D - mu (Dn n) \is a fin_num
  by rewrite ?fin_numB ?finD /= ?(finDn n).
rewrite -fine_abse // gee0_abs ?sube_ge0 ?finD ?(finDn _) //.
  by rewrite -[_ - _]fineK // lte_fin fine.
by rewrite le_measure// ?inE//; [exact: measurableI |exact: subIsetl].
Qed.

Lemma lebesgue_regularity_inner (D : set R) (eps : R) :
  measurable D -> mu D < +oo -> (0 < eps)%R ->
  exists V : set R, [/\ compact V , V `<=` D & mu (D `\` V) < eps%:E].
Proof.
move=> mD finD epspos.
wlog : eps epspos D mD finD / exists ab : R * R, D `<=` `[ab.1, ab.2]%classic.
  move=> WL; have [] := @lebesgue_nearly_bounded _ (eps / 2)%R mD finD.
    by rewrite divr_gt0.
  case=> a b /= muDabe; have [] := WL (eps / 2)%R _ (D `&` `[a,b]).
  - by rewrite divr_gt0.
  - exact: measurableI.
  - by rewrite (le_lt_trans _ finD)// le_measure// inE//; exact: measurableI.
  - by exists (a, b).
  move=> V [/= cptV VDab Dabeps2]; exists (V `&` `[a, b]); split.
  - apply: (subclosed_compact _ cptV) => //; apply: closedI.
      by apply: compact_closed => //; exact: Rhausdorff.
    exact: interval_closed.
  - by move=> ? [/VDab []].
  rewrite setDIr (setU_id2r ((D `&` `[a, b]) `\` V)); last first.
    move=> z ; rewrite setDE setCI setCK => -[?|?];
    by apply/propext; split => [[]|[[]]].
  have mV : measurable V.
    by apply: closed_measurable; apply: compact_closed => //; exact: Rhausdorff.
  rewrite [eps]splitr EFinD (measureU mu) // ?lteD //.
  - by apply: measurableD => //; exact: measurableI.
  - exact: measurableD.
  - by rewrite eqEsubset; split => z // [[[_ + _] [_]]].
case=> -[a b] /= Dab; pose D' := `[a,b] `\` D.
have mD' : measurable D' by exact: measurableD.
have [] := lebesgue_regularity_outer mD' _ epspos.
  rewrite (@le_lt_trans _ _ (mu `[a,b]%classic))//.
    by rewrite le_measure ?inE//; exact: subIsetl.
  by rewrite /= lebesgue_measure_itv/= -EFinD -(fun_if EFin) ltry.
move=> U [oU /subsetC + mDeps]; rewrite setCI setCK => nCD'.
exists (`[a, b] `&` ~` U); split.
- apply: (subclosed_compact _ (@segment_compact _ a b)) => //.
  by apply: closedI; [exact: interval_closed | exact: open_closedC].
- by move=> z [abz] /nCD'[].
- rewrite setDE setCI setIUr setCK.
  rewrite [_ `&` ~` _ ](iffRL (disjoints_subset _ _)) ?setCK // set0U.
  move: mDeps; rewrite /D' ?setDE setCI setIUr setCK [U `&` D]setIC.
  move => /(le_lt_trans _); apply; apply: le_measure; last by move => ?; right.
    by rewrite inE; apply: measurableI => //; exact: open_measurable.
  rewrite inE; apply: measurableU.
    by apply: measurableI; [exact: open_measurable|exact: measurableC].
  by apply: measurableI => //; exact: open_measurable.
Qed.

Let lebesgue_regularity_innerE_bounded (A : set R) : measurable A ->
  mu A < +oo ->
  mu A = ereal_sup [set mu K | K in [set K | compact K /\ K `<=` A]].
Proof.
move=> mA muA; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: ub_ereal_sup => /= x [B /= [cB BA <-{x}]]; exact: le_outer_measure.
apply/lee_addgt0Pr => e e0.
have [B [cB BA /= ABe]] := lebesgue_regularity_inner mA muA e0.
rewrite -{1}(setDKU BA) (@le_trans _ _ (mu B + mu (A `\` B)))//.
  by rewrite setUC outer_measureU2.
by rewrite leeD//; [apply: ereal_sup_ubound => /=; exists B|exact/ltW].
Qed.

Lemma lebesgue_regularity_inner_sup (D : set R) : measurable D ->
  mu D = ereal_sup [set mu K | K in [set K | compact K /\ K `<=` D]].
Proof.
move=> mD; have [?|] := ltP (mu D) +oo.
  exact: lebesgue_regularity_innerE_bounded.
have /sigma_finiteP [F [RFU Fsub ffin]] :=
  sigma_finiteT (lebesgue_stieltjes_measure (@idfun R)).
rewrite leye_eq => /eqP /[dup] + ->.
have {1}-> : D = \bigcup_n (F n `&` D) by rewrite -setI_bigcupl -RFU setTI.
move=> FDp; apply/esym/eq_infty => M.
have : (fun n => mu (F n `&` D)) @ \oo --> +oo.
  rewrite -FDp; apply: nondecreasing_cvg_mu.
  - by move=> i; apply: measurableI => //; exact: (ffin i).1.
  - by apply: bigcup_measurable => i _; exact: (measurableI _ _ (ffin i).1).
  - by move=> n m nm; apply/subsetPset; apply: setSI; exact/subsetPset/Fsub.
move/cvgey_ge => /(_ (M + 1)%R) [N _ /(_ _ (lexx N))].
have [mFN FNoo] := ffin N.
have [] := @lebesgue_regularity_inner (F N `&` D) _ _ _ ltr01.
- exact: measurableI.
- by rewrite (le_lt_trans _ (ffin N).2)//= measureIl.
move=> V [/[dup] /compact_measurable mV cptV VFND] FDV1 M1FD.
rewrite (@le_trans _ _ (mu V))//; last first.
  apply: ereal_sup_ubound; exists V => //=; split => //.
  exact: (subset_trans VFND (@subIsetr _ _ _)).
rewrite -(@leeD2rE _ 1)// -EFinD (le_trans M1FD)//.
rewrite /mu (@measureDI _ _ _ _ (F N `&` D) _ _ mV)/=; last exact: measurableI.
by rewrite addeC leeD//; [rewrite measureIr//; exact: measurableI|exact/ltW].
Qed.

End lebesgue_regularity.

Definition vitali_cover {R : numFieldType} (E : set R) I
    (B : I -> set R) (D : set I) :=
  (forall i, is_ball (B i)) /\
  forall x, E x -> forall e : R, 0 < e -> exists i,
    [/\ D i, B i x & (radius (B i))%:num < e].

Section vitali_theorem.
Context {R : realType} (A : set R) (B : nat -> set R).
Hypothesis B0 : forall i, (0 < (radius (B i))%:num)%R.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma vitali_theorem (V : set nat) : vitali_cover A B V ->
  exists D, [/\ countable D, D `<=` V, trivIset D (closure \o B) &
    mu (A `\` \bigcup_(k in D) closure (B k)) = 0].
Proof.
move=> ABV.
wlog VB1 : V ABV / forall i, V i -> ((radius (B i))%:num <= 1)%R.
  move=> wlg.
  pose V' := V `\` [set i | (radius (B i))%:num > 1]%R.
  have : vitali_cover A B V'.
    split; [exact: ABV.1|move=> x Ax e e0].
    have : (0 < minr e 1)%R by rewrite lt_min// e0/=.
    move=> /(ABV.2 x Ax)[i [Vi ix ie]].
    exists i; split => //.
    - split => //=; rewrite ltNge; apply/negP/negPn.
      by rewrite (le_trans (ltW ie))// ge_min lexx orbT.
    - by rewrite (lt_le_trans ie)// ge_min lexx.
  move/wlg.
  have V'B1 i : V' i -> ((radius (B i))%:num <= 1)%R.
    by move=> [Vi /=]; rewrite ltNge => /negP/negPn.
  move=> /(_ V'B1)[D [cD DV' tD h]].
  by exists D; split => //; apply: (subset_trans DV') => ? [].
have [D [cD DV tDB Dintersect]] := vitali_lemma_infinite ABV.1 B0 VB1.
exists D; split => //.
pose Z r := (A `\` \bigcup_(k in D) closure (B k)) `&` ball (0%R:R) r.
suff: forall r : {posnum R}, mu (Z r%:num) = 0.
  move=> Zr; have {}Zr n : mu (Z n%:R) = 0.
    move: n => [|n]; first by rewrite /Z (ball0 _ _).2// setI0.
    by rewrite (Zr (PosNum (ltr0Sn _ n))).
  set F := fun n => Z n%:R.
  have : mu (\bigcup_n F n) <= \sum_(i <oo) mu (F i).
    exact: outer_measure_sigma_subadditive.
  rewrite eseries0; last by move=> n _; rewrite /F Zr.
  by rewrite /F -setI_bigcupr bigcup_ballT setIT measure_le0 => /eqP.
move=> r.
pose E := [set i | D i /\ closure (B i) `&` ball (0%R:R) r%:num !=set0].
pose F := vitali_collection_partition B E 1.
have E_partition : E = \bigcup_n (F n).
  by rewrite -cover_vitali_collection_partition// => i [] /DV /VB1.
have EBr2 n : E n -> closure (B n) `<=` (ball (0:R) (r%:num + 2))%R.
  move=> [Dn] [x] => -[Bnx rx] y /= Bny.
  move: rx; rewrite /ball /= !sub0r !normrN => rx.
  rewrite -(subrK x y) (le_lt_trans (ler_normD _ _))//.
  rewrite addrC ltr_leD// -(subrK (cpoint (B n)) y) -(addrA (y - _)%R).
  rewrite (le_trans (ler_normD _ _))// (_ : 2 = 1 + 1)%R// lerD//.
    rewrite distrC; have := is_ball_closureP (ABV.1 n) Bny.
    by move=> /le_trans; apply; rewrite VB1//; exact: DV.
  have := is_ball_closureP (ABV.1 n) Bnx.
  by move=> /le_trans; apply; rewrite VB1//; exact: DV.
have measurable_closure (C : set R) : is_ball C -> measurable (closure C).
  by move=> ballC; rewrite is_ball_closure//; exact: measurable_closed_ball.
move: ABV => [is_ballB ABV].
have {}EBr2 : \esum_(i in E) mu (closure (B i)) <=
              mu (ball (0:R) (r%:num + 2))%R.
  rewrite -(set_mem_set E) -nneseries_esum// -measure_bigcup//; last 2 first.
    by move=> *; exact: measurable_closure.
    by apply: sub_trivIset tDB => ? [].
  apply/le_measure; rewrite ?inE; [|exact: measurable_ball|exact: bigcup_sub].
  by apply: bigcup_measurable => *; exact: measurable_closure.
have finite_set_F i : finite_set (F i).
  apply: contrapT.
  pose M := (trunc ((r%:num + 2) *+ 2 / (1 / (2 ^ i.+1)%:R))).+1.
  move/(infinite_set_fset M) => [/= C CsubFi McardC].
  have MC : (M%:R * (1 / (2 ^ i.+1)%:R))%:E <=
            mu (\bigcup_(j in [set` C]) closure (B j)).
    rewrite (measure_bigcup _ [set` C])//; last 2 first.
      by move=> ? _; exact: measurable_closure.
      by apply: sub_trivIset tDB; by apply: (subset_trans CsubFi) => x [[]].
    rewrite /= nneseries_esum//= set_mem_set// esum_fset// fsbig_finite//=.
    rewrite set_fsetK.
    apply: (@le_trans _ _ (\sum_(i0 <- C) (1 / (2 ^ i.+1)%:R)%:E)).
      under eq_bigr do rewrite -(mul1r (_ / _)%R) EFinM.
      rewrite -ge0_sume_distrl// EFinM lee_wpmul2r// sumEFin lee_fin.
      by rewrite -(natr_sum _ _ _ (cst 1%N)) ler_nat -card_fset_sum1.
    rewrite big_seq [in leRHS]big_seq; apply: lee_sum => // j.
    move=> /CsubFi[_ /andP[+ _]].
    rewrite -lte_fin => /ltW/le_trans; apply.
    rewrite (is_ball_closure (is_ballB _))// lebesgue_measure_closed_ball//.
    by rewrite lee_fin mulr2n lerDr.
  have CFi : mu (\bigcup_(j in [set` C]) closure (B j)) <=
             mu (\bigcup_(j in F i) closure (B j)).
    apply: le_measure => //; rewrite ?inE.
    - rewrite bigcup_fset; apply: bigsetU_measurable => *.
      exact: measurable_closure.
    - by apply: bigcup_measurable => *; exact: measurable_closure.
    - apply: bigcup_sub => j Cj.
      exact/(@bigcup_sup _ _ _ _ (closure \o B))/CsubFi.
  have Fir2 : mu (\bigcup_(j in F i) closure (B j)) <=
              mu (ball (0:R) (r%:num + 2))%R.
    rewrite (le_trans _ EBr2)// -(set_mem_set E) -nneseries_esum //.
    rewrite E_partition -measure_bigcup//=; last 2 first.
      by move=> ? _; exact: measurable_closure.
      apply: trivIset_bigcup => //.
        by move=> n; apply: sub_trivIset tDB => ? [[]].
      by move=> n m i0 j nm [[Di0 _] _] [[Dj _] _]; exact: tDB.
    apply: le_measure; rewrite ?inE.
    - by apply: bigcup_measurable => *; exact: measurable_closure.
    - by apply: bigcup_measurable => *; exact: measurable_closure.
    - by move=> /= x [n Fni Bnx]; exists n => //; exists i.
  have {CFi Fir2} := le_trans MC (le_trans CFi Fir2).
  apply/negP; rewrite -ltNge lebesgue_measure_ball// lte_fin.
  by rewrite -ltr_pdivrMr// /M truncnS_gt.
have mur2_fin_num_ : mu (ball (0:R) (r%:num + 2))%R < +oo.
  by rewrite lebesgue_measure_ball// ltry.
have FE : \sum_(n <oo) \esum_(i in F n) mu (closure (B i)) =
          mu (\bigcup_(i in E) closure (B i)).
  rewrite E_partition bigcup_bigcup; apply/esym.
  transitivity (\sum_(n <oo) mu (\bigcup_(i in F n) closure (B i))).
    apply: measure_semi_bigcup => //.
    - by move=> i; apply: bigcup_measurable => *; exact: measurable_closure.
    - apply: trivIsetT_bigcup => //.
        apply/trivIsetP => i j _ _ ij.
        by apply: disjoint_vitali_collection_partition => // k -[] /DV /VB1.
      by rewrite -E_partition; apply: sub_trivIset tDB => x [].
    - rewrite -bigcup_bigcup; apply: bigcup_measurable => k _.
      exact: measurable_closure.
  apply: (@eq_eseriesr _ (fun n => mu (\bigcup_(i in F n) closure (B i)))).
  move=> i _; rewrite bigcup_mkcond measure_semi_bigcup//; last 3 first.
    by move=> j; case: ifPn => // _; exact: measurable_closure.
    by apply/(trivIset_mkcond _ _).1; apply: sub_trivIset tDB => x [[]].
    rewrite -bigcup_mkcond; apply: bigcup_measurable => k _.
    exact: measurable_closure.
  rewrite esum_mkcond//= nneseries_esum// -fun_true//=.
  by under eq_esum do rewrite (fun_if mu) (measure0 mu).
apply/eqP; rewrite -measure_le0.
apply/lee_addgt0Pr => _ /posnumP[e]; rewrite add0e.
have [N F5e] : exists N, \sum_(N <= n <oo) \esum_(i in F n) mu (closure (B i)) <
    5%:R^-1%:E * e%:num%:E.
  pose f n := \bigcup_(i in F n) closure (B i).
  have foo : \sum_(k <oo) (mu \o f) k < +oo.
    rewrite /f /= [ltLHS](_ : _ =
      \sum_(n <oo) \esum_(i in F n) mu (closure (B i))); last first.
    apply: (@eq_eseriesr _
        (fun k => mu (\bigcup_(i in F k) closure (B i)))) => i _.
      rewrite measure_bigcup//=.
      - by rewrite nneseries_esum// set_mem_set.
      - by move=> j D'ij; exact: measurable_closure.
      - by apply: sub_trivIset tDB => // x [[]].
    rewrite FE (@le_lt_trans _ _ (mu (ball (0 : R) (r%:num + 2))%R))//.
    rewrite (le_trans _ EBr2)// measure_bigcup//=.
    + by rewrite nneseries_esum// set_mem_set.
    + by move=> i _; exact: measurable_closure.
    + by apply: sub_trivIset tDB => // x [].
  have : \sum_(N <= k <oo) (mu \o f) k @[N --> \oo] --> 0.
    exact: nneseries_tail_cvg.
  rewrite /f /= => /fine_fcvg /= /cvgrPdist_lt /=.
  have : (0 < 5%:R^-1 * e%:num)%R by rewrite mulr_gt0// invr_gt0// ltr0n.
  move=> /[swap] /[apply].
  rewrite near_map => -[N _]/(_ _ (leqnn N)) h; exists N; move: h.
  rewrite sub0r normrN ger0_norm//; last by rewrite fine_ge0// nneseries_ge0.
  rewrite -lte_fin; apply: le_lt_trans.
  set X : \bar R := (X in fine X).
  have Xoo : X < +oo.
    apply: le_lt_trans foo.
    by rewrite (nneseries_split _ N)// leeDr//; exact: sume_ge0.
  rewrite fineK ?ge0_fin_numE//; last exact: nneseries_ge0.
  apply: lee_nneseries => //; first by move=> i *; exact: esum_ge0.
  move=> n Nn; rewrite measure_bigcup//=.
  - by rewrite nneseries_esum// set_mem_set.
  - by move=> i _; exact: measurable_closure.
  - by apply: sub_trivIset tDB => x [[]].
pose K := \bigcup_(i in `I_N) \bigcup_(j in F i) closure (B j).
have closedK : closed K.
  apply: closed_bigcup => //= i iN; apply: closed_bigcup => //.
  by move=> j Fij; exact: closed_closure.
have ZNF5 : Z r%:num `<=`
    \bigcup_(i in ~` `I_N) \bigcup_(j in F i) closure (5%:R *` B j).
  move=> z Zz.
  have Kz : ~ K z.
    rewrite /K => -[n /= nN [m] [[Dm _] _] Bmz].
    by case: Zz => -[_ + _]; apply; exists m.
  have [i [Vi Biz Bir BiK0]] : exists i, [/\ V i, (closure (B i)) z,
      closure (B i) `<=` ball (0%R:R) r%:num & closure (B i) `&` K = set0].
    case: Zz => -[Az notDBz]; rewrite /ball/= sub0r normrN => rz.
    have [d dzr zdK0] : exists2 d : {posnum R},
        (d%:num < r%:num - `|z|)%R & closed_ball z d%:num `&` K = set0.
      have [d/= d0 dzK] := closed_disjoint_closed_ball closedK Kz.
      have rz0 : (0 < minr ((r%:num - `|z|) / 2) (d / 2))%R.
        by rewrite lt_min (divr_gt0 d0)//= andbT divr_gt0// subr_gt0.
      exists (PosNum rz0) => /=.
        by rewrite gt_min ltr_pdivrMr// ltr_pMr ?subr_gt0// ltr1n.
      apply: dzK => //=.
      rewrite sub0r normrN gtr0_norm// gt_min (ltr_pdivrMr d d)//.
      by rewrite ltr_pMr// ltr1n orbT.
    have N0_gt0 : (0 < d%:num / 2)%R by rewrite divr_gt0.
    have [i [Vi Biz BiN0]] := ABV _ Az _ N0_gt0.
    exists i; split => //.
      exact: subset_closure.
      move=> y Biy; rewrite /ball/= sub0r normrN -(@subrK _ (cpoint (B i)) y).
      rewrite (le_lt_trans (ler_normD _ _))//.
      rewrite (@le_lt_trans _ _ (d%:num / 2 + `|cpoint (B i)|)%R)//.
        rewrite lerD2r// distrC.
        by rewrite (le_trans (is_ball_closureP (is_ballB i) Biy))// ltW.
      rewrite -(@subrK _ z (cpoint (B i))).
      rewrite (@le_lt_trans _ _ (d%:num / 2 + `|cpoint (B i) - z| + `|z|)%R)//.
        by rewrite -[leRHS]addrA lerD2l//; exact: ler_normD.
      rewrite (@le_lt_trans _ _ (d%:num + `|z|)%R)//.
        rewrite [in leRHS](splitr d%:num) -!addrA lerD2l// lerD2r//.
        by rewrite (le_trans (ltW (is_ballP (is_ballB i) Biz)))// ltW.
      by move: dzr; rewrite -ltrBrDr.
    apply: subsetI_eq0 zdK0 => // y Biy.
    rewrite closed_ballE//= /closed_ball_/=.
    rewrite -(@subrK _ (cpoint (B i)) z) -(addrA (z - _)%R).
    rewrite (le_trans (ler_normD _ _))// [in leRHS](splitr d%:num) lerD//.
      by rewrite distrC (le_trans (ltW (is_ballP (is_ballB i) Biz)))// ltW.
    by rewrite (le_trans (is_ball_closureP (is_ballB i) Biy))// ltW.
  have [j [Ej Bij0 Bij5]] : exists j, [/\ E j,
      closure (B i) `&` closure (B j) !=set0 &
      closure (B i) `<=` closure (5%:R *` B j)].
    have [j [Dj Bij0 Bij2 Bij5]] := Dintersect _ Vi.
    exists j; split => //; split => //.
    by move: Bij0; rewrite setIC; exact: subsetI_neq0.
  have BjK : ~ (closure (B j) `<=` K).
    move=> BjK; move/eqP : BiK0.
    by apply/negP/set0P; move: Bij0; exact: subsetI_neq0.
  have [k NK Fkj] : (\bigcup_(i in ~` `I_N) F i) j.
    move: Ej; rewrite E_partition => -[k _ Fkj].
    by exists k => //= kN; apply: BjK => x Bjx; exists k => //; exists j.
  by exists k => //; exists j => //; exact: Bij5.
have {}ZNF5 : mu (Z r%:num) <=
    \sum_(N <= m <oo) \esum_(i in F m) mu (closure (5%:R *` B i)).
  apply: (@le_trans _ _ (mu (\bigcup_(i in ~` `I_N)
      \bigcup_(j in F i) closure (5%:R *` B j)))).
    exact: le_outer_measure.
  apply: (@le_trans _ _ (\sum_(N <= i <oo) mu
                           (\bigcup_(j in F i) closure (5%:R *` B j)))).
    apply: measure_sigma_subadditive_tail => //.
      move=> n; apply: bigcup_measurable => k _.
      by apply: measurable_closure; exact: is_scale_ball.
    apply: bigcup_measurable => k _; apply: bigcup_measurable => k' _.
    by apply: measurable_closure; exact: is_scale_ball.
  apply: lee_nneseries => // n _.
  rewrite -[in leRHS](set_mem_set (F n)) -nneseries_esum// bigcup_mkcond.
  rewrite eseries_mkcond [leRHS](_ : _ = \sum_(i <oo) mu
      (if i \in F n then closure (5%:R *` B i) else set0)); last first.
    congr (limn _); apply/funext => x.
    by under [RHS]eq_bigr do rewrite (fun_if mu) measure0.
  apply: measure_sigma_subadditive => //.
  + move=> m; case: ifPn => // _.
    by apply: measurable_closure; exact: is_scale_ball.
  + apply: bigcup_measurable => k _; case: ifPn => // _.
    by apply: measurable_closure; exact: is_scale_ball.
apply/(le_trans ZNF5).
move/ltW: F5e; rewrite [in X in X -> _](@lee_pdivlMl R 5%:R) ?ltr0n//.
rewrite -nneseriesZl//; last by move=> *; exact: esum_ge0.
apply: le_trans; apply: lee_nneseries => //; first by move=> *; exact: esum_ge0.
move=> n _.
rewrite -(set_mem_set (F n)) -nneseries_esum// -nneseries_esum// -nneseriesZl//.
apply: lee_nneseries => // m mFn.
rewrite (ballE (is_ballB m))// closure_ball lebesgue_measure_closed_ball//.
rewrite scale_ballE// closure_ball lebesgue_measure_closed_ball//.
by rewrite -EFinM mulrnAr.
Qed.

End vitali_theorem.

Lemma vitali_coverS {R : realFieldType} (A : set R) (B : nat -> set R)
    (F : set nat) (O : set R) : open O -> A `<=` O ->
  vitali_cover A B F -> vitali_cover A B (F `&` [set k | B k `<=` O]).
Proof.
move=> oO AO [Bball ABF]; split => // x Ax r r0.
have [d xdO] : exists d : {posnum R}, ball x d%:num `<=` O.
  have [/= d d0 dxO] := open_subball oO (AO _ Ax).
  have d20 : (0 < d / 2)%R by rewrite divr_gt0.
  exists (PosNum d20) => z xdz.
  apply: (dxO (PosNum d20)%:num) => //=.
  by rewrite sub0r normrN gtr0_norm// gtr_pMr// invf_lt1// ltr1n.
pose rd2 : R := minr r (d%:num / 2)%R.
have rd2_gt0 : (0 < rd2)%R by rewrite lt_min r0//= divr_gt0.
have [k [Vk Bkr Bkd]] := ABF _ Ax _ rd2_gt0.
exists k => //; split => //; last by rewrite (lt_le_trans Bkd)// ge_min// lexx.
split => //=.
apply: subset_trans xdO => /= z Bkz.
rewrite /ball/= -(addrKA (- cpoint (B k))).
rewrite (le_lt_trans (ler_normB _ _))//= -(addrC z).
rewrite (splitr d%:num) ltrD//.
  rewrite distrC (lt_le_trans (is_ballP _ _))//.
  by rewrite (le_trans (ltW Bkd))// ge_min lexx orbT.
rewrite distrC (lt_le_trans (is_ballP _ _))//.
by rewrite (le_trans (ltW Bkd))// ge_min lexx orbT.
Qed.

Section vitali_theorem_corollary.
Context {R : realType} (A : set R) (B : nat -> set R).

Let vitali_cover_mclosure (F : set nat) k :
  vitali_cover A B F -> (R.-ocitv.-measurable).-sigma.-measurable (closure (B k)).
Proof.
case => + _ => /(_ k)/ballE ->.
by rewrite closure_ball; exact: measurable_closed_ball.
Qed.

Let vitali_cover_measurable (F : set nat) k :
  vitali_cover A B F -> (R.-ocitv.-measurable).-sigma.-measurable (B k).
Proof. by case => + _ => /(_ k)/ballE ->; exact: measurable_ball. Qed.

Let vitali_cover_ballE (F : set nat) n :
  vitali_cover A B F -> B n = ball (cpoint (B n)) (radius (B n))%:num.
Proof. by case => + _ => /(_ n)/ballE. Qed.

Hypothesis B0 : forall i, (0 < (radius (B i))%:num)%R.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Let bigB (G : set nat) c := G `&` [set k | (radius (B k))%:num >= c]%R.

Let bigBS (G : set nat) r : bigB G r `<=` G.
Proof. by move=> i []. Qed.

Let bigB0 (G : set nat) : bigB G 0%R = G.
Proof. by apply/seteqP; split => [//|x Gx]; split => //=. Qed.

(* references:
   - https://angyansheng.github.io/notes/measure-theory-xvi
   - https://math.stackexchange.com/questions/4606604/a-proof-of-vitalis-covering-theorem
   - https://math-wiki.com/images/2/2f/88341leb_fund_thm.pdf (p.9)
*)
Lemma vitali_theorem_corollary (F : set nat) :
  mu A < +oo%E -> vitali_cover A B F ->
  forall e, (e > 0)%R -> exists G' : {fset nat}, [/\ [set` G'] `<=` F,
    trivIset [set` G'] (closure \o B) &
    ((wlength idfun)^* (A `\` \big[setU/set0]_(k <- G') closure (B k)))%mu
    < e%:E].
Proof.
move=> muAfin ABF e e0.
have [O [oO AO OAoo]] :
    exists O : set R, [/\ open O, A `<=` O & mu O < mu A + 1 < +oo].
  have /(outer_measure_open_le A) : (0 < 1 / 2 :> R)%R by rewrite divr_gt0.
  move=> [O [oA AO OAe]]; exists O; split => //.
  rewrite lte_add_pinfty ?ltry// andbT.
  rewrite (le_lt_trans OAe)// lteD2lE ?ge0_fin_numE ?outer_measure_ge0//.
  by rewrite lte_fin ltr_pdivrMr// mul1r ltr1n.
pose F' := F `&` [set k | B k `<=` O].
have ABF' : vitali_cover A B F' by exact: vitali_coverS.
have [G [cG GV' tB mAG0]] := vitali_theorem B0 ABF'.
have muGSfin C : C `<=` G -> mu (\bigcup_(k in C) closure (B k)) \is a fin_num.
  move=> CG; rewrite ge0_fin_numE// (@le_lt_trans _ _ (mu O))//; last first.
    by move: OAoo => /andP[OA]; exact: lt_trans.
  rewrite (@le_trans _ _ (mu (\bigcup_(k in G) B k)))//; last first.
    by rewrite le_outer_measure//; apply: bigcup_sub => i /GV'[].
  rewrite bigcup_mkcond [in leRHS]bigcup_mkcond measure_bigcup//=; last 2 first.
    by move=> i _; case: ifPn => // iG; exact: vitali_cover_mclosure ABF.
    by apply/(trivIset_mkcond _ _).1; apply: sub_trivIset tB.
  rewrite measure_bigcup//=; last 2 first.
    by move=> i _; case: ifPn => // _; exact: vitali_cover_measurable ABF.
    apply/(trivIset_mkcond _ _).1/trivIsetP => /= i j  Gi Gj ij.
    move/trivIsetP : tB => /(_ _ _ Gi Gj ij).
    by apply: subsetI_eq0; exact: subset_closure.
  apply: lee_nneseries => // n _.
  case: ifPn => [/set_mem nC|]; last by rewrite measure0.
  rewrite (vitali_cover_ballE _ ABF) ifT; last exact/mem_set/CG.
  by rewrite closure_ball lebesgue_measure_closed_ball// lebesgue_measure_ball.
have muGfin : mu (\bigcup_(k in G) closure (B k)) \is a fin_num.
  by rewrite -(bigB0 G) muGSfin.
have [c Hc] : exists c : {posnum R},
    mu (\bigcup_(k in bigB G c%:num) closure (B k)) >
    mu (\bigcup_(k in G) closure (B k)) - e%:E.
  have : \sum_(N <= k <oo | k \in G) mu (closure (B k)) @[N --> \oo] --> 0%E.
    have : \sum_(0 <= i <oo | i \in G) mu (closure (B i)) < +oo.
      rewrite -measure_bigcup -?ge0_fin_numE//=.
      by move=> i _; exact: vitali_cover_mclosure ABF.
    by move/(@nneseries_tail_cvg _ _ (mem G)); exact.
  move/fine_cvgP => [_] /cvgrPdist_lt /(_ _ e0)[n _ /=] nGe.
  have [c nc] : exists c : {posnum R}, forall k,
      (c%:num > (radius (B k))%:num)%R -> (k >= n)%N.
    pose x := (\big[minr/(radius (B 0))%:num]_(i < n.+1) (radius (B i))%:num)%R.
    have x_gt0 : (0 < x)%R by exact: lt_bigmin.
    exists (PosNum x_gt0) => k /=; apply: contraPleq => kn.
    apply/negP; rewrite -leNgt; apply/bigmin_leP => /=; right.
    by exists (widen_ord (@leqnSn _) (Ordinal kn)).
  exists c.
  suff:  mu (\bigcup_(k in G `\` bigB G c%:num) closure (B k)) < e%:E.
    rewrite EFinN lteBlDl// -lteBlDr//; last exact: muGSfin.
    apply: le_lt_trans.
    pose setDbigB := (\bigcup_(k in G) closure (B k)) `\`
                     (\bigcup_(k in bigB G c%:num) closure (B k)).
    have ? : setDbigB `<=` \bigcup_(k in G `\` bigB G c%:num) closure (B k).
      move=> /= x [[k Gk Bkx]].
      rewrite -[X in X -> _]/((~` _) x) setC_bigcup => abs.
      by exists k => //; split=> // /abs.
    apply: (@le_trans _ _ (mu setDbigB)); last first.
      rewrite le_measure ?inE//.
        by apply: measurableD;
          apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
      by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
    rewrite measureD//=; last 3 first.
      by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
      by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
      by rewrite -ge0_fin_numE.
    rewrite leeB// le_measure ?inE//.
      by apply: measurableI;
        apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
    by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
  apply: (@le_lt_trans _ _ (normr (0 -
     fine (\sum_(n <= k <oo | k \in G) mu (closure (B k)))))%:E); last first.
    by rewrite lte_fin; apply: nGe => /=.
  rewrite sub0r normrN ger0_norm/=; last by rewrite fine_ge0// nneseries_ge0.
  rewrite fineK//; last first.
    move: muGfin; rewrite measure_bigcup//=; last first.
      by move=> i _; exact: vitali_cover_mclosure ABF.
    do 2 (rewrite ge0_fin_numE//; last exact: nneseries_ge0).
    apply: le_lt_trans.
    by rewrite [leRHS](nneseries_split_cond 0%N n)// add0n leeDr// sume_ge0.
  rewrite measure_bigcup//=; last 2 first.
    by move=> i _; exact: vitali_cover_mclosure ABF.
    by apply: sub_trivIset tB; exact: subDsetl.
  rewrite [in leRHS]eseries_cond.
  suff: forall i, i \in G `\` bigB G c%:num -> (n <= i)%N.
    move=> GG'n; apply: subset_lee_nneseries => //= m mGG'.
    by rewrite GG'n// andbT; case/set_mem: mGG' => /mem_set ->.
  move=> i iGG'; rewrite nc//.
  by move/set_mem: iGG' => [Gi] /not_andP[//|/negP]; rewrite -ltNge.
have {}Hc : mu (\bigcup_(k in G) closure (B k) `\`
                \bigcup_(k in bigB G c%:num) closure (B k)) < e%:E.
  rewrite measureD//=; first last.
  - by rewrite -ge0_fin_numE.
  - by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
  - by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
  rewrite setIidr; last exact: bigcup_subset.
  by rewrite lteBlDr-?lteBlDl//; exact: muGSfin.
have bigBG_fin (r : {posnum R}) : finite_set (bigB G r%:num).
  pose M := (trunc (fine (mu O) / r%:num)).+1.
  apply: contrapT => /infinite_set_fset /= /(_ M)[G0 G0G'r MG0].
  have : mu O < mu (\bigcup_(k in bigB G r%:num) closure (B k)).
    apply: (@lt_le_trans _ _ (mu (\bigcup_(k in [set` G0]) closure (B k)))).
      rewrite bigcup_fset measure_fbigsetU//=; last 2 first.
        by move=> k _; exact: vitali_cover_mclosure ABF.
        by apply: sub_trivIset tB => x /G0G'r[].
      apply: (@lt_le_trans _ _ (\sum_(i <- G0) r%:num%:E)%R).
        rewrite sumEFin big_const_seq iter_addr addr0 -mulr_natr.
        apply: (@lt_le_trans _ _ (r%:num * M%:R)%:E); last first.
          by rewrite lee_fin ler_wpM2l// ler_nat count_predT.
        rewrite EFinM -lte_pdivrMl// muleC -(@fineK _ (mu O)); last first.
          by rewrite ge0_fin_numE//; case/andP: OAoo => ?; exact: lt_trans.
        by rewrite -EFinM /M lte_fin truncnS_gt.
      rewrite big_seq [in leRHS]big_seq.
      apply: lee_sum => //= i /G0G'r [iG rBi].
      rewrite -[leRHS]fineK//; last first.
        rewrite (vitali_cover_ballE _ ABF).
        by rewrite closure_ball lebesgue_measure_closed_ball.
      rewrite (vitali_cover_ballE _ ABF) closure_ball.
      by rewrite lebesgue_measure_closed_ball// fineK// lee_fin mulr2n ler_wpDl.
    rewrite le_measure? inE//; last exact: bigcup_subset.
    - by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
    - by apply: bigcup_measurable => k _; exact: vitali_cover_mclosure ABF.
  apply/negP; rewrite -leNgt.
  apply: (@le_trans _ _ (mu (\bigcup_(k in bigB G r%:num) B k))).
    rewrite measure_bigcup//; last 2 first.
      by move=> k _; exact: vitali_cover_mclosure ABF.
      exact: sub_trivIset tB.
    rewrite /= measure_bigcup//; last 2 first.
      by move=> k _; exact: vitali_cover_measurable ABF.
      apply/trivIsetP => /= i j [Gi ri] [Gj rj] ij.
      move/trivIsetP : tB => /(_ _ _ Gi Gj ij).
      by apply: subsetI_eq0 => //=; exact: subset_closure.
    rewrite /= lee_nneseries// => n _.
    rewrite (vitali_cover_ballE _ ABF)// closure_ball.
    by rewrite lebesgue_measure_closed_ball// lebesgue_measure_ball.
  rewrite le_measure? inE//.
  + by apply: bigcup_measurable => k _; exact: vitali_cover_measurable ABF.
  + exact: open_measurable.
  + by apply: bigcup_sub => i [/GV'[? ?] cBi].
exists (fset_set (bigB G c%:num)); split.
- by move=> /= k; rewrite in_fset_set// inE /bigB /= => -[] /GV'[].
- by apply: sub_trivIset tB => k/=; rewrite in_fset_set// inE /bigB /= => -[].
- pose UG : set R := \bigcup_(k in G) closure (B k).
  rewrite bigsetU_fset_set//.
  apply: (@le_lt_trans _ _ ((wlength idfun)^*%mu (A `\`UG) +
       mu (UG `\` \bigcup_(k in bigB G c%:num) closure (B k)))); last first.
    by rewrite -[(wlength idfun)^*%mu]/mu mAG0 add0e.
  apply: (@le_trans _ _ ((wlength idfun)^*%mu
      (A `&` (UG `\` \bigcup_(k in bigB G c%:num) closure (B k))) +
      (wlength idfun)^*%mu (A `\` UG))); last first.
    by rewrite addeC leeD2l// le_outer_measure.
  apply: (le_trans _ (outer_measureU2 _ _ _)) => //=; apply: le_outer_measure.
  rewrite !(setDE A) -setIUr; apply: setIS.
  by rewrite setDE setUIl setUv setTI -setCI; exact: subsetC.
Qed.

End vitali_theorem_corollary.
