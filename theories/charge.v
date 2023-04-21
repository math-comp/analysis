(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp.classical Require Import boolp classical_sets cardinality.
From mathcomp.classical Require Import mathcomp_extra functions fsbigop.
From mathcomp.classical Require Import set_interval.
From HB Require Import structures.
Require Import reals ereal signed topology numfun normedtype sequences.
Require Import esum measure realfun lebesgue_measure lebesgue_integral.

(******************************************************************************)
(* This file contains a formalization of charges (a.k.a. signed measures) and *)
(* a proof of the Hahn decomposition theorem.                                 *)
(*                                                                            *)
(*          isAdditiveCharge == mixin for additive charges                    *)
(*            AdditiveCharge == structure of additive charges                 *)
(*  {additive_charge set T -> \bar R} == additive charge over T, a semiring   *)
(*                            of sets                                         *)
(*       additive_charge T R == type of additive charges                      *)
(*                  isCharge == mixin for charges                             *)
(*                    Charge == structure of charges                          *)
(*                charge T R == type of charges                               *)
(*  {charge set T -> \bar R} == charge over T, a semiring of sets             *)
(*              crestr nu mD == restriction of the charge nu to the domain D  *)
(*                              where mD is a proof that D is measurable      *)
(*                     czero == zero charge                                   *)
(*               cscale r nu == charge nu scaled by a factor r                *)
(*         positive_set nu P == P is a positive set                           *)
(*         negative_set nu N == N is a negative set                           *)
(* hahn_decomposition nu P N == the charge nu is decomposed into the positive *)
(*                              set P and the negative set N                  *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'additive_charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'additive_charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'charge'  'set'  T  '->'  '\bar'  R }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

(* NB: in the next releases of Coq, dependent_choice will be
   generalized from Set to Type making the following lemma redundant *)
Section dependent_choice_Type.
Context X (R : X -> X -> Prop).

Lemma dependent_choice_Type : (forall x, {y | R x y}) ->
  forall x0, {f | f 0 = x0 /\ forall n, R (f n) (f n.+1)}.
Proof.
move=> h x0.
set (f := fix f n := if n is n'.+1 then proj1_sig (h (f n')) else x0).
exists f; split => //.
intro n; induction n; simpl; apply proj2_sig.
Qed.
End dependent_choice_Type.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

HB.mixin Record isAdditiveCharge d (T : semiRingOfSetsType d) (R : numFieldType)
  (mu : set T -> \bar R) := { charge_semi_additive : measure.semi_additive mu }.

#[short(type=additive_charge)]
HB.structure Definition AdditiveCharge d (T : semiRingOfSetsType d)
  (R : numFieldType) := { mu of isAdditiveCharge d T R mu & FinNumFun d mu }.

Notation "{ 'additive_charge' 'set' T '->' '\bar' R }" :=
  (additive_charge T R)  : ring_scope.

#[export] Hint Resolve charge_semi_additive : core.

HB.mixin Record isCharge d (T : semiRingOfSetsType d) (R : numFieldType)
    (mu : set T -> \bar R) := {
  charge_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=charge)]
HB.structure Definition Charge d (T : algebraOfSetsType d) (R : numFieldType)
  := { mu of isCharge d T R mu & AdditiveCharge d mu }.

Notation "{ 'charge' 'set' T '->' '\bar' R }" := (charge T R) : ring_scope.

Section charge_lemmas.
Context d (T : measurableType d) (R : numFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma charge0 nu : nu set0 = 0.
Proof.
have /[!big_ord0] ->// := @charge_semi_additive _ _ _ nu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve charge0 : core.

Lemma charge_semi_additiveW nu :
  nu set0 = 0 -> measure.semi_additive nu -> semi_additive2 nu.
Proof.
move=> nu0 anu A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(anu (bigcup2 A B)) ->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- move=> [|[|i]] [|[|j]]/= _ _ //.
  + by rewrite AB => -[].
  + by rewrite setI0 => -[].
  + by rewrite setIC AB => -[].
  + by rewrite setI0 => -[].
  + by rewrite set0I => -[].
  + by rewrite set0I => -[].
  + by rewrite setI0 => -[].
Qed.

Lemma charge_semi_additive2E nu : semi_additive2 nu = additive2 nu.
Proof.
rewrite propeqE; split=> [anu A B ? ? ?|anu A B ? ? _ ?]; last by rewrite anu.
by rewrite anu //; exact: measurableU.
Qed.

Lemma charge_semi_additive2 nu : semi_additive2 nu.
Proof. exact: charge_semi_additiveW. Qed.

Hint Resolve charge_semi_additive2 : core.

Lemma chargeU nu : additive2 nu. Proof. by rewrite -charge_semi_additive2E. Qed.

Lemma chargeDI nu (A B : set T) : measurable A -> measurable B ->
  nu A = nu (A `\` B) + nu (A `&` B).
Proof.
move=> mA mB; rewrite -charge_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma charge_partition nu S P N :
  measurable S -> measurable P -> measurable N ->
  P `|` N = setT -> P `&` N = set0 -> nu S = nu (S `&` P) + nu (S `&` N).
Proof.
move=> mS mP mN PNT PN0; rewrite -{1}(setIT S) -PNT setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

End charge_lemmas.
#[export] Hint Resolve charge0 : core.
#[export] Hint Resolve charge_semi_additive2 : core.

Section charge_lemmas_realFieldType.
Context d (T : measurableType d) (R : realFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma chargeD nu (A B : set T) : measurable A -> measurable B ->
  nu (A `\` B) = nu A - nu (A `&` B).
Proof.
move=> mA mB.
rewrite (chargeDI nu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite ltey_eq fin_num_measure//; exact:measurableI.
- by rewrite ltNye_eq fin_num_measure//; exact:measurableI.
Qed.

End charge_lemmas_realFieldType.

Definition crestr d (T : measurableType d) (R : numDomainType) (D : set T)
  (f : set T -> \bar R) of measurable D := fun X => f (X `&` D).

Section charge_restriction.
Context d (T : measurableType d) (R : numFieldType).
Variables (nu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr nu mD).

Let crestr_finite_measure_function U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(fin_num_measure nu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  restr crestr_finite_measure_function.

Let crestr_semi_additive : measure.semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(charge_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite /crestr /FD big_distrl.
Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ restr crestr_semi_additive.

Let crestr_semi_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /restr setI_bigcupl; apply: charge_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ :=
  isCharge.Build _ _ _ restr crestr_semi_sigma_additive.

End charge_restriction.

Section charge_zero.
Context d (T : measurableType d) (R : realFieldType).
Local Open Scope ereal_scope.

Definition czero (A : set T) : \bar R := 0.

Let czero0 : czero set0 = 0. Proof. by []. Qed.

Let czero_finite_measure_function B : measurable B -> czero B \is a fin_num.
Proof. by []. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  czero czero_finite_measure_function.

Let czero_semi_additive : measure.semi_additive czero.
Proof. by move=> F n mF tF mUF; rewrite /czero big1. Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ czero czero_semi_additive.

Let czero_sigma_additive : semi_sigma_additive czero.
Proof.
move=> F mF tF mUF; rewrite [X in X @ _ --> _](_ : _ = cst 0); first exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ czero czero_sigma_additive.

End charge_zero.
Arguments czero {d T R}.

Section charge_scale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realFieldType).
Variables (r : R) (nu : {charge set T -> \bar R}).

Definition cscale (A : set T) : \bar R := r%:E * nu A.

Let cscale0 : cscale set0 = 0. Proof. by rewrite /cscale charge0 mule0. Qed.

Let cscale_finite_measure_function U : measurable U -> cscale U \is a fin_num.
Proof. by move=> mU; apply: fin_numM => //; exact: fin_num_measure. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  cscale cscale_finite_measure_function.

Let cscale_semi_additive : measure.semi_additive cscale.
Proof.
move=> F n mF tF mU; rewrite /cscale charge_semi_additive//.
rewrite fin_num_sume_distrr// => i j _ _.
by rewrite fin_num_adde_defl// fin_num_measure.
Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ cscale cscale_semi_additive.

Let cscale_sigma_additive : semi_sigma_additive cscale.
Proof.
move=> F mF tF mUF; rewrite /cscale; rewrite [X in X @ _ --> _](_ : _ =
    (fun n => r%:E * \sum_(0 <= i < n) nu (F i))); last first.
  apply/funext => k; rewrite fin_num_sume_distrr// => i j _ _.
  by rewrite fin_num_adde_defl// fin_num_measure.
rewrite /mscale; have [->|r0] := eqVneq r 0%R.
  rewrite mul0e [X in X @ _ --> _](_ : _ = (fun=> 0)); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeMl => //; apply: charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ cscale
  cscale_sigma_additive.

End charge_scale.

Section positive_negative_set.
Context d (R : numDomainType) (T : measurableType d).
Implicit Types nu : set T -> \bar R.

Definition positive_set nu (P : set T) :=
  measurable P /\ forall E, measurable E -> E `<=` P -> nu E >= 0.

Definition negative_set nu (N : set T) :=
  measurable N /\ forall E, measurable E -> E `<=` N -> nu E <= 0.

End positive_negative_set.

Section positive_negative_set_lemmas.
Context d (T : measurableType d) (R : numFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma negative_set_charge_le0 nu N : negative_set nu N -> nu N <= 0.
Proof. by move=> [mN]; exact. Qed.

Lemma negative_set0 nu : negative_set nu set0.
Proof. by split => // E _; rewrite subset0 => ->; rewrite charge0. Qed.

Lemma positive_negative0 nu P N : positive_set nu P -> negative_set nu N ->
  forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> [mP posP] [mN negN] S mS; apply/eqP; rewrite eq_le; apply/andP; split.
  apply negN; first by apply measurableI => //; exact: measurableI.
  by apply setIidPl; rewrite -setIA setIid.
rewrite -setIAC.
apply posP; first by apply measurableI => //; exact: measurableI.
by apply setIidPl; rewrite -setIA setIid.
Qed.

End positive_negative_set_lemmas.

Section positive_negative_set_realFieldType.
Context d (T : measurableType d) (R : realFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma bigcup_negative_set nu (F : (set T)^nat) :
    (forall i, negative_set nu (F i)) ->
  negative_set nu (\bigcup_i F i).
Proof.
move=> hF; have mUF : measurable (\bigcup_k F k).
  by apply: bigcup_measurable => n _; have [] := hF n.
split=> [//|S mS SUF].
pose SF n := (S `&` F n) `\` \bigcup_(k < n) F k.
have SSF : S = \bigcup_i SF i.
  transitivity (\bigcup_k seqDU (fun n => S `&` F n) k); last first.
    by apply: eq_bigcup => // n _; rewrite seqDUIE.
  by rewrite -seqDU_bigcup_eq -setI_bigcupr setIidl.
have mSF n : measurable (SF n).
  apply: measurableD; first by apply: measurableI => //; have [] := hF n.
  by apply: bigcup_measurable => // k _; have [] := hF k.
have SFS : (\sum_(0 <= i < n) nu (SF i)) @[n --> \oo] --> nu S.
  by rewrite SSF; apply: charge_semi_sigma_additive => //;
    [by rewrite /SF -seqDUIE; exact: trivIset_seqDU|exact: bigcup_measurable].
have nuS_ n : nu (SF n) <= 0 by have [_] := hF n; apply => // x -[[]].
move/cvg_lim : (SFS) => <-//; apply: lime_le.
  by apply/cvg_ex => /=; first eexists; exact: SFS.
by apply: nearW => n; exact: sume_le0.
Qed.

Lemma negative_setU nu N M :
  negative_set nu N -> negative_set nu M -> negative_set nu (N `|` M).
Proof.
move=> nN nM; rewrite -bigcup2E; apply: bigcup_negative_set => -[//|[//|/= _]].
exact: negative_set0.
Qed.

End positive_negative_set_realFieldType.

Section hahn_decomposition_lemma.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R}) (D : set T).

Let elt_prop (x : set T * \bar R) := [/\ measurable x.1,
  x.1 `<=` D, 0 <= x.2 & nu x.1 >= mine (x.2 * 2^-1%:E) 1].

Let elt_type := {x : set T * \bar R * set T | elt_prop x.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let d_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?]] []. Qed.
Let A_D x : A_ x `<=` D. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let d_ge0 x : 0 <= d_ x. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let nuA_d_ x : nu (A_ x) >= mine (d_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let nuA_ge0 x : 0 <= nu (A_ x).
Proof. by rewrite (le_trans _ (nuA_d_ _))// le_minr lee01 andbT mule_ge0. Qed.

Let subDD A := [set nu E | E in [set E | measurable E /\ E `<=` D `\` A] ].

Let t_ A := ereal_sup (subDD A).

Lemma t_ge0 X : 0 <= t_ X.
Proof. by apply: ereal_sup_ub => /=; exists set0; rewrite ?charge0. Qed.

Let elt_rel i j :=
  [/\ d_ j = t_ (U_ i),  A_ j `<=` D `\` U_ i & U_ j = U_ i `|` A_ j ].

Let next_elt A : 0 <= t_ A ->
  { B | [/\ measurable B, B `<=` D `\` A & nu B >= mine (t_ A * 2^-1%:E) 1] }.
Proof.
move=> tA0; pose m := mine (t_ A * 2^-1%R%:E) 1; apply/cid.
move: tA0; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite charge0 mul0e minEle lee01.
have /ereal_sup_gt/cid2[_ [B/= [mB BDA <- mnuB]]] : m < t_ A.
  rewrite /m; have [->|dn1oo] := eqVneq (t_ A) +oo.
    by rewrite min_r ?ltey ?gt0_mulye ?leey.
  rewrite -(@fineK _ (t_ A)); last first.
    by rewrite ge0_fin_numE// ?(ltW d_gt0)// lt_neqAle dn1oo leey.
  rewrite -EFinM -fine_min// lte_fin lt_minl; apply/orP; left.
  by rewrite ltr_pdivr_mulr// ltr_pmulr ?ltr1n// fine_gt0// d_gt0/= ltey.
by exists B; split => //; rewrite (le_trans _ (ltW mnuB)).
Qed.

(* TODO: generalize? *)
Let minr_cvg_0_cvg_0 (x : R^nat) : (forall k, 0 <= x k)%R ->
  (minr (x n * 2^-1) 1)%R @[n --> \oo] --> (0:R)%R -> x n @[n --> \oo] --> (0:R)%R.
Proof.
move=> x_ge0 minr_cvg; apply/cvgrPdist_lt => _ /posnumP[e].
have : (0 < minr (e%:num / 2) 1)%R by rewrite lt_minr// ltr01 andbT divr_gt0.
move/cvgrPdist_lt : minr_cvg => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN !ger0_norm// ?le_minr ?divr_ge0//=.
rewrite -[X in minr _ X](@divrr _ 2) ?unitfE -?minr_pmull//.
rewrite -[X in (_ < minr _ X)%R](@divrr _ 2) ?unitfE -?minr_pmull//.
by rewrite ltr_pmul2r//; exact: lt_min_lt.
Unshelve. all: by end_near. Qed.

Let mine_cvg_0_cvg_fin_num (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (mine (x n * (2^-1)%:E) 1) @[n --> \oo] --> 0 ->
  \forall n \near \oo, x n \is a fin_num.
Proof.
move=> x_ge0 /fine_cvgP[_] /cvgrPdist_lt/(_ _ ltr01)[N _ hN].
near=> n; have /hN : (N <= n)%N by near: n; exists N.
rewrite sub0r normrN /= ger0_norm ?fine_ge0//; last first.
  by rewrite le_minr mule_ge0//=.
by have := x_ge0 n; case: (x n) => //=; rewrite gt0_mulye//= ltxx.
Unshelve. all: by end_near. Qed.

Let mine_cvg_minr_cvg (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (mine (x n * (2^-1)%:E) 1) @[n --> \oo] --> 0 ->
  (minr ((fine \o x) n / 2) 1%R) @[n --> \oo] --> (0:R)%R.
Proof.
move=> x_ge0 mine_cvg; apply: (cvg_trans _ (fine_cvg mine_cvg)).
move/fine_cvgP : mine_cvg => [_ /=] /cvgrPdist_lt.
move=> /(_ _ ltr01)[N _ hN]; apply: near_eq_cvg; near=> n.
have xnoo : x n < +oo.
  rewrite ltNge leye_eq; apply/eqP => xnoo.
  have /hN : (N <= n)%N by near: n; exists N.
  by rewrite /= sub0r normrN xnoo gt0_mulye//= normr1 ltxx.
by rewrite /= -(@fineK _ (x n)) ?ge0_fin_numE//= -fine_min.
Unshelve. all: by end_near. Qed.

Let mine_cvg_0_cvg_0 (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (mine (x n * (2^-1)%:E) 1) @[n --> \oo] --> 0 -> x n @[n --> \oo] --> 0.
Proof.
move=> x_ge0 h; apply/fine_cvgP; split; first exact: mine_cvg_0_cvg_fin_num.
apply: (@minr_cvg_0_cvg_0 (fine \o x)) => //; last exact: mine_cvg_minr_cvg.
by move=> k /=; rewrite fine_ge0.
Qed.

Lemma hahn_decomposition_lemma : measurable D ->
  {A | [/\ A `<=` D, negative_set nu A & nu A <= nu D]}.
Proof.
move=> mD; have [A0 [mA0 + A0t0]] := next_elt (t_ge0 set0).
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, t_ set0, A0) (And4 mA0 A0D (t_ge0 set0) A0t0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' ?] U] [/= mA' A'D]].
  have [A1 [mA1 A1DU A1t1] ] := next_elt (t_ge0 U).
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, t_ U, U `|` A1) (And4 mA1 A1D (t_ge0 U) A1t1)).
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n; move/subset_trans; apply.
  by rewrite -setTD; apply: setDSS => //; rewrite Ubig big_ord_recr.
set Aoo := \bigcup_k A_ (v k).
have mAoo : measurable Aoo by exact: bigcup_measurable.
exists (D `\` Aoo).
have cvg_nuA : (\sum_(0 <= i < n) nu (A_ (v i))) @[n --> \oo]--> nu Aoo.
  exact: charge_semi_sigma_additive.
have nuAoo : 0 <= nu Aoo.
  move/cvg_lim : cvg_nuA => <-//=; apply: nneseries_ge0 => n _.
  exact: nuA_ge0.
have A_cvg_0 : nu (A_ (v n)) @[n --> \oo] --> 0.
  rewrite [X in X @ _ --> _](_ : _ = (fun n => (fine (nu (A_ (v n))))%:E)); last first.
    by apply/funext => n/=; rewrite fineK// fin_num_measure.
  apply: continuous_cvg => //; apply: cvg_series_cvg_0.
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) nu (A_ (v i)))); last first.
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite fin_num_measure.
  move: cvg_nuA; rewrite -(@fineK _ (nu Aoo)) ?fin_num_measure//.
  by move=> /fine_cvgP[_ ?]; apply/cvg_ex; exists (fine (nu Aoo)).
have mine_cvg_0 : (mine (d_ (v n) * 2^-1%:E) 1) @[n --> \oo] --> 0.
  apply: (@squeeze_cvge _ _ _ _ _ _ (fun n => nu (A_ (v n))));
    [|exact: cvg_cst|by []].
  by apply: nearW => n /=; rewrite nuA_d_ andbT le_minr lee01 andbT mule_ge0.
have d_cvg_0 : (d_ \o v) n @[n --> \oo] --> 0 by apply: mine_cvg_0_cvg_0 => //=.
have nuDAoo : nu D >= nu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D); last first.
    by apply: bigcup_sub => i _; exact: A_D.
  by rewrite chargeU// ?lee_addr// ?setDIK//; exact: measurableD.
split; [by []| |by []]; split; [exact: measurableD | move=> E mE EDAoo].
pose H n := subDD (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set nu E] `<=` H n.
  have : nu E \in subDD Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply => x/= [F [mF FDAoo ?]].
  exists F => //; split => //.
  by apply: (subset_trans FDAoo); apply: setDS; exact: bigsetU_bigcup.
have nudelta n : nu E <= d_ (v n).
  move: n => [|n].
    rewrite v0/=; apply: ereal_sup_ub => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : nu E <= t_ (U_ (v n)) by have [<- _] := Pv n.
  have /le_ereal_sup := EH n.+1; rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [mA' A'D ?]].
  exists A' => //; split => //.
  by apply: (subset_trans A'D); apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => nu E <= v) _ _ _ d_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_lemma.

Definition hahn_decomposition d (T : measurableType d) (R : realType)
    (nu : {charge set T -> \bar R}) P N :=
  [/\ positive_set nu P, negative_set nu N, P `|` N = setT & P `&` N = set0].

Section hahn_decomposition_theorem.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Let elt_prop (x : set T * \bar R) := [/\ x.2 <= 0,
  negative_set nu x.1 & nu x.1 <= maxe (x.2 * 2^-1%:E) (- 1%E) ].

Let elt_type := {AsU : set T * \bar R * set T | elt_prop AsU.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let z_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?] [/= ? []]]. Qed.
Let negative_set_A_ x : negative_set nu (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.
Let nuA_z_ x : nu (A_ x) <= maxe (z_ x * 2^-1%:E) (- 1%E).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let nuA_le0 x : nu (A_ x) <= 0.
Proof. by move: x => [[[? ?] ?]] [? h ?]; exact: negative_set_charge_le0. Qed.

Let z_le0 x : z_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let subC A := [set nu E | E in [set E | measurable E /\ E `<=` ~` A] ].

Let s_ A := ereal_inf (subC A).

Lemma s_le0 X : s_ X <= 0.
Proof.
by apply: ereal_inf_lb => /=; exists set0; rewrite ?charge0//=; split.
Qed.

Let elt_rel i j :=
  [/\ z_ j = s_ (U_ i), A_ j `<=` ~` U_ i & U_ j = U_ i `|` A_ j].

Let next_elt U : s_ U <= 0 -> { A | [/\ A `<=` ~` U,
  negative_set nu A & nu A <= maxe (s_ U * 2^-1%R%:E) (- 1%E)] }.
Proof.
move=> sU0; pose m := maxe (s_ U * 2^-1%R%:E) (- 1%E); apply/cid.
move: sU0; rewrite le_eqVlt => /predU1P[->|s_lt0].
  exists set0; split => //; rewrite ?charge0 ?mul0e ?maxEle ?lee0N1//.
  exact: negative_set0.
have /ereal_inf_lt/cid2[_ [B/= [mB BU] <-] nuBm] : s_ U < m.
  rewrite /m; have [->|s0oo] := eqVneq (s_ U) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (s_ U)); last first.
    by rewrite le0_fin_numE// ?(ltW s_lt0)// lt_neqAle leNye eq_sym s0oo.
  rewrite -EFinM -fine_max// lte_fin lt_maxr; apply/orP; left.
  by rewrite ltr_pdivl_mulr// gtr_nmulr ?ltr1n// fine_lt0// s_lt0/= ltNye andbT.
have [C [CB nsC nuCB]] := hahn_decomposition_lemma nu mB.
exists C; split => //; first exact: (subset_trans CB).
by rewrite (le_trans nuCB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N, hahn_decomposition nu P N.
Proof.
have [A0 [_ negA0 A0s0]] := next_elt (s_le0 set0).
have [v [v0 Pv]] : {v |
    v 0%N = exist _ (A0, s_ set0, A0) (And3 (s_le0 set0) negA0 A0s0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice_Type => -[[[A s] U] [/= s_le0' nsA]].
  have [A' [? nsA' A's'] ] := next_elt (s_le0 U).
  by exists (exist _ (A', s_ U, U `|` A') (And3 (s_le0 U) nsA' A's')).
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n; move/subset_trans; apply.
  by apply: subsetC; rewrite Ubig big_ord_recr.
set N := \bigcup_k (A_ (v k)).
have mN : measurable N by exact: bigcup_measurable.
have neg_set_N : negative_set nu N.
  by apply: bigcup_negative_set => i; exact: negative_set_A_.
pose P := ~` N.
have mP : measurable P by exact: measurableC.
exists P, N; split; [|exact: neg_set_N|by rewrite /P setvU|by rewrite /P setICl].
split=> // D mD DP; rewrite leNgt; apply/negP => nuD0.
have znuD n : z_ (v n) <= nu D.
  move: n => [|n].
    by rewrite v0 /=; apply: ereal_inf_lb; exists D; split => //; rewrite setC0.
  have [-> _ _] := Pv n; apply: ereal_inf_lb => /=; exists D; split => //.
  apply: (subset_trans DP); apply: subsetC; rewrite Ubig.
  exact: bigsetU_bigcup.
have max_le0 n : maxe (z_ (v n) * 2^-1%:E) (- 1%E) <= 0.
  by rewrite le_maxl leeN10 andbT pmule_lle0.
have not_s_cvg_0 : ~ (z_ \o v) n @[n --> \oo]  --> 0.
  move/fine_cvgP => -[zfin] /cvgrPdist_lt.
  have /[swap] /[apply] -[M _ hM] : (0 < `|fine (nu D)|)%R.
    by rewrite normr_gt0// fine_eq0// ?lt_eqF// fin_num_measure.
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm ?fine_le0// ltr0_norm//; last first.
    by rewrite fine_lt0// nuD0 andbT ltNye_eq fin_num_measure.
  rewrite ltr_opp2; apply/negP; rewrite -leNgt fine_le ?fin_num_measure//.
  by near: n; exact.
have nuN : nu N = \sum_(n <oo) nu (A_ (v n)).
  apply/esym/cvg_lim => //.
  by apply: charge_semi_sigma_additive; [|exact: tA|exact: bigcup_measurable].
have sum_A_maxe : \sum_(n <oo) nu (A_ (v n)) <=
    \sum_(n <oo) maxe (z_ (v n) * 2^-1%:E) (- 1%E) by exact: lee_npeseries.
have : cvg (\sum_(0 <= k < n) maxe (z_ (v k) * 2^-1%:E) (- 1%E) @[n --> \oo]).
  by apply: is_cvg_ereal_npos_natsum_cond => n _ _; exact: max_le0.
move=> /cvg_ex[[l| |]]; first last.
  - move/cvg_lim => limNoo.
    have : nu N <= -oo by rewrite -limNoo// nuN.
    by rewrite leNgt => /negP; apply; rewrite ltNye_eq fin_num_measure.
  - move/cvg_lim => limoo.
    have := @npeseries_le0 _ (fun n => maxe (z_ (v n) * 2^-1%:E) (- 1%E)) xpredT.
    by rewrite limoo// leNgt => /(_ (fun n _ => max_le0 n))/negP; apply.
move/fine_cvgP => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (z_ (v n) * 2^-1%:E) (- 1%E))) n @[n --> \oo]).
  apply/cvg_ex; exists l; move: cvgl.
  rewrite (_ : _ \o _ = (fun n =>
    \sum_(0 <= k < n) fine (maxe (z_ (v k) * 2^-1%:E)%E (- 1%E)%E))%R) //.
  apply/funext => n/=; rewrite sum_fine// => m _.
  rewrite le0_fin_numE; first by rewrite lt_maxr ltNyr orbT.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/cvg_series_cvg_0 => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite (_ : _ \o _ = (fun n => z_ (v n) * 2^-1%:E) \* cst 2%:E); last first.
  by apply/funext => n/=; rewrite -muleA -EFinM mulVr ?mule1// unitfE.
rewrite (_ : 0 = 0 * 2%:E); last by rewrite mul0e.
apply: cvgeM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/fine_cvgP; split.
  move/cvgrPdist_lt : maxe_cvg_0 => /(_ _ ltr01)[M _ hM]; near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN ltNge => maxe_lt1; rewrite fin_numE; apply/andP; split.
    by apply: contra maxe_lt1 => /eqP ->; rewrite max_r ?leNye//= normrN1 lexx.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/cvgrPdist_lt => _ /posnumP[e].
have : (0 < minr e%:num 1)%R by rewrite lt_minr// ltr01 andbT.
move/cvgrPdist_lt : maxe_cvg_0 => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN /maxe/=; case: ifPn => [_|].
  by rewrite normrN normr1 lt_minr ltxx andbF.
by rewrite -leNgt => ? /lt_le_trans; apply; rewrite le_minl lexx.
Unshelve. all: by end_near. Qed.

Lemma Hahn_decomposition_uniq P1 N1 P2 N2 :
  hahn_decomposition nu P1 N1 -> hahn_decomposition nu P2 N2 ->
  forall S, measurable S ->
    nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> [psP1 nsN1 PN1T PN10] [psP2 nsN2 PN2T PN20] S mS.
move: (psP1) (nsN1) (psP2) (nsN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
split.
- transitivity (nu (S `&` P1 `&` P2)).
  + rewrite (charge_partition _ _ mP2 mN2)//; last exact: measurableI.
    by rewrite (positive_negative0 psP1 nsN2 mS) adde0.
  + rewrite [RHS](charge_partition _ _ mP1 mN1)//; last exact: measurableI.
    by rewrite (positive_negative0 psP2 nsN1 mS) adde0 setIAC.
- transitivity (nu (S `&` N1 `&` N2)).
  + rewrite (charge_partition nu _ mP2 mN2)//; last exact: measurableI.
    have := positive_negative0 psP2 nsN1 mS.
    by rewrite setIAC => ->; rewrite add0e.
  + rewrite [RHS](charge_partition nu _ mP1 mN1)//; last exact: measurableI.
    by rewrite (setIAC _ _ P1) (positive_negative0 psP1 nsN2 mS) add0e setIAC.
Qed.

End hahn_decomposition_theorem.
