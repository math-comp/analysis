(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.
Require Import lebesgue_measure lebesgue_integral.

(******************************************************************************)
(* This file contains a formalization of charges and a proof of the Hahn      *)
(* decomposition theorem.                                                     *)
(*                                                                            *)
(* charge (a.k.a. signed measure):                                            *)
(*          isAdditiveCharge == mixin for additive charges                    *)
(*  {additive_charge set T -> \bar R} == additive charge over T, a semiring   *)
(*                            of sets                                         *)
(*                  isCharge == mixin for charges                             *)
(*  {charge set T -> \bar R} == charge over T, a semiring of sets             *)
(*               crestr D mu == restriction of the charge mu to the domain D  *)
(*                     czero == zero charge                                   *)
(*                    cscale == scaled charge                                 *)
(*         positive_set nu P == P is a positive set                           *)
(*         negative_set nu N == N is a negative set                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

(* NB: in the next releases of Coq, dependent_choice should be
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

(* TODO: PR? *)
Lemma lt_trivIset T (F : nat -> set T) :
  (forall n m, (m < n)%N -> F m `&` F n = set0) -> trivIset setT F.
Proof.
move=> h; apply/trivIsetP => m n _ _; rewrite neq_lt => /orP[|]; first exact: h.
by rewrite setIC; exact: h.
Qed.

(* TODO: PR? *)
Lemma subsetC_trivIset T (F : nat -> set T) :
  (forall n, F n.+1 `<=` ~` \big[setU/set0]_(i < n.+1) F i) -> trivIset setT F.
Proof.
move=> ACU; apply: lt_trivIset => n m mn; rewrite setIC; apply/disjoints_subset.
case: n mn => // n mn.
by apply: (subset_trans (ACU n)); exact/subsetC/bigsetU_sup.
Qed.

(* TODO: PR? *)
Lemma fin_num_ltey (R : realDomainType) (x : \bar R) : x \is a fin_num -> x < +oo.
Proof. by move: x => [r| |]// _; rewrite ltey. Qed.

(* TODO: PR? *)
Lemma gt0_fin_numE {R : realDomainType} [x : \bar R] : 0 < x -> (x \is a fin_num) = (x < +oo).
Proof. by move=> /ltW; exact: ge0_fin_numE. Qed.

(* TODO: PR? *)
Lemma seqDUIE X (S : set X) (F : (set X)^nat) :
  seqDU (fun n => S `&` F n) = (fun n => S `&` F n `\` \bigcup_(i < n) F i).
Proof.
apply/funext => n; rewrite -setIDA; apply/seteqP; split.
  by rewrite /seqDU -setIDA bigcup_mkord -big_distrr/= setDIr setIUr setDIK set0U.
move=> x [Sx [Fnx UFx]]; split=> //; apply: contra_not UFx => /=.
by rewrite bigcup_mkord -big_distrr/= => -[].
Qed.

HB.mixin Record isAdditiveCharge d (T : semiRingOfSetsType d) (R : numFieldType)
    (mu : set T -> \bar R) := {
  charge_semi_additive : semi_additive mu }.

#[short(type=additive_charge)]
HB.structure Definition AdditiveCharge d (T : semiRingOfSetsType d)
    (R : numFieldType) :=
  { mu of isAdditiveCharge d T R mu & FinNumFun d mu }.

Notation "{ 'additive_charge' 'set' T '->' '\bar' R }" :=
  (additive_charge T R) (at level 36, T, R at next level,
    format "{ 'additive_charge'  'set'  T  '->'  '\bar'  R }") : ring_scope.

#[export] Hint Resolve charge_semi_additive : core.

HB.mixin Record isCharge d (T : semiRingOfSetsType d) (R : numFieldType)
    (mu : set T -> \bar R) := {
  charge_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=charge)]
HB.structure Definition Charge d (T : algebraOfSetsType d) (R : realFieldType) :=
  { mu of isCharge d T R mu & AdditiveCharge d mu }.

Notation "{ 'charge' 'set' T '->' '\bar' R }" := (charge T R)
  (at level 36, T, R at next level,
    format "{ 'charge'  'set'  T  '->'  '\bar'  R }") : ring_scope.

Section charge_prop.
Context d (T : measurableType d) (R : realType).
Implicit Type mu : {charge set T -> \bar R}.

Lemma charge0 mu : mu set0 = 0.
Proof.
have /[!big_ord0] ->// := @charge_semi_additive _ _ _ mu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve charge0 : core.

Lemma charge_semi_additiveW mu : mu set0 = 0 -> semi_additive mu -> semi_additive2 mu.
Proof.
move=> mu0 amx A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(amx (bigcup2 A B)) ->.
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

Lemma charge_semi_additive2E mu : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma charge_semi_additive2 mu : semi_additive2 mu.
Proof. exact: charge_semi_additiveW. Qed.

Hint Resolve charge_semi_additive2 : core.

Lemma chargeU mu : additive2 mu. Proof. by rewrite -charge_semi_additive2E. Qed.

Lemma chargeDI mu (A B : set T) : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -charge_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma chargeD mu (A B : set T) : measurable A -> measurable B ->
  mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB.
rewrite (chargeDI mu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite ltey_eq fin_num_measure//; exact:measurableI.
- by rewrite ltNye_eq fin_num_measure//; exact:measurableI.
Qed.

Lemma charge_partition mu S P N :
  measurable S -> measurable P -> measurable N ->
  P `|` N = setT -> P `&` N = set0 ->
  mu S = mu (S `&` P) + mu (S `&` N).
Proof.
move=> mS mP mN PNT PN0; rewrite -{1}(setIT S) -PNT setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

End charge_prop.
#[export] Hint Resolve charge0 : core.
#[export] Hint Resolve charge_semi_additive2 : core.

Definition crestr d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) := fun X => f (X `&` D).

Section charge_restriction.
Context d (T : measurableType d) (R : realFieldType).
Variables (mu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr mu mD).

Let crestr_finite_measure_function U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(@fin_num_measure _ _ _ mu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  restr crestr_finite_measure_function.

Let crestr_semi_additive : semi_additive restr.
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

Let czero_semi_additive : semi_additive czero.
Proof. by move=> F n mF tF mUF; rewrite /czero big1. Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ czero czero_semi_additive.

Let czero_sigma_additive : semi_sigma_additive czero.
Proof.
move=> F mF tF mUF; rewrite [X in X --> _](_ : _ = cst 0); first exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ czero czero_sigma_additive.

End charge_zero.
Arguments czero {d T R}.

Section charge_scale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType). (* R : realFieldType? *)
Variables (r : R) (m : {charge set T -> \bar R}).

Definition cscale (A : set T) : \bar R := r%:E * m A.

Let cscale0 : cscale set0 = 0. Proof. by rewrite /cscale charge0 mule0. Qed.

Let cscale_finite_measure_function U : measurable U -> cscale U \is a fin_num.
Proof. by move=> mU; apply: fin_numM => //; exact: fin_num_measure. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  cscale cscale_finite_measure_function.

Let cscale_semi_additive : semi_additive cscale.
Proof.
move=> F n mF tF mU; rewrite /cscale charge_semi_additive//.
rewrite fin_num_sume_distrr// => i j _ _.
by rewrite fin_num_adde_defl// fin_num_measure.
Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ cscale cscale_semi_additive.

Let cscale_sigma_additive : semi_sigma_additive cscale.
Proof.
move=> F mF tF mUF; rewrite /cscale; rewrite [X in X --> _](_ : _ =
    (fun n => r%:E * \sum_(0 <= i < n) m (F i))); last first.
  apply/funext => k; rewrite fin_num_sume_distrr// => i j _ _.
  by rewrite fin_num_adde_defl// fin_num_measure.
rewrite /mscale; have [->|r0] := eqVneq r 0%R.
  rewrite mul0e [X in X --> _](_ : _ = (fun=> 0)); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeMl => //; apply: charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ cscale
  cscale_sigma_additive.

End charge_scale.

Section positive_negative_set.
Context d (R : realType) (T : measurableType d).
Implicit Types nu : set T -> \bar R.

Definition positive_set nu (P : set T) :=
  measurable P /\ forall E, measurable E -> E `<=` P -> nu E >= 0.

Definition negative_set nu (N : set T) :=
  measurable N /\ forall E, measurable E -> E `<=` N -> nu E <= 0.

End positive_negative_set.

Section positive_negative_set_prop.
Context d (T : measurableType d) (R : realType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma negative_set_charge_le0 nu N : negative_set nu N -> nu N <= 0.
Proof. by move=> [mN]; exact. Qed.

Lemma negative_set0 nu : negative_set nu set0.
Proof. by split => // E _; rewrite subset0 => ->; rewrite charge0. Qed.

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
have SFS : (fun n => \sum_(0 <= i < n) nu (SF i)) --> nu S.
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

End positive_negative_set_prop.

Section hahn_decomp_lemma.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Variable D : set T.

Let elt_prop (x : set T * \bar R) := [/\ measurable x.1,
  0 <= x.2,
  x.1 `<=` D &
  nu x.1 >= mine (x.2 * 2^-1%:E) 1].

Let elt_type := {x : set T * \bar R * set T | elt_prop x.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let d_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA x : measurable (A_ x).
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_A_ge0 x : 0 <= nu (A_ x).
Proof.
move: x => [[[? ?] ?]] [/= mA d_ge0 Ad]; apply: le_trans.
by rewrite /mine; case: ifPn => // _; rewrite mule_ge0.
Qed.

Let elt_d_ge0 x : 0 <= d_ x.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_mine x : nu (A_ x) >= mine (d_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_D x : A_ x `<=` D.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let set_mE A :=
  [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` D `\` A] ].

Let dd A := ereal_sup (set_mE A).

Let seq_sup i j := [/\ d_ j = dd (U_ i),
  A_ j `<=` D `\` U_ i & U_ j = U_ i `|` A_ j ].

Let next_elt A : 0 <= dd A -> { B | [/\ measurable B,
  nu B >= 0, B `<=` D `\` A & nu B >= mine (dd A * 2^-1%:E) 1] }.
Proof.
move=> d_ge0; pose m := mine (dd A * 2^-1%R%:E) 1%E; apply/cid.
move: d_ge0; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite charge0.
have m_gt0 : 0 < m by rewrite /m lt_minr lte01 andbT mule_gt0.
have : m < dd A.
  rewrite /m; have [->|dn1oo] := eqVneq (dd A) +oo.
    by rewrite min_r// ?ltey// gt0_mulye// leey.
  rewrite -(@fineK _ (dd A)); last first.
    by rewrite ge0_fin_numE// ?(ltW d_gt0)// lt_neqAle dn1oo leey.
  rewrite -EFinM minEFin lte_fin lt_minl; apply/orP; left.
  rewrite ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// fine_gt0// d_gt0/=.
  by rewrite lt_neqAle dn1oo/= leey.
move=> /ereal_sup_gt/cid2[x/= /cid[B [-> mB BDA mmuB]]].
exists B; split => //.
by rewrite ltW// (lt_trans _ mmuB)//.
by rewrite (le_trans _ (ltW mmuB)).
Qed.

Lemma hahn_decomp_lemma : measurable D -> nu D <= 0 ->
  {A | [/\ A `<=` D, measurable A, negative_set nu A & nu A <= nu D]}.
Proof.
move=> mD nuD_ge0.
have d0_ge0 : 0 <= dd set0.
  by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite charge0.
have [A0 [mA0 nuA0 + A0d0]] := next_elt d0_ge0.
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, dd set0, A0) (And4 mA0 d0_ge0 A0D A0d0) /\
    forall n, seq_sup (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' ?] U] [/= mA' mA'0]].
  have d1_ge0 : 0 <= dd U.
    by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite charge0.
  have [A1 [mA1 muA10 A1DU A1d1] ] := next_elt d1_ge0.
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, dd U, U `|` A1) (And4 mA1 d1_ge0 A1D A1d1)).
set Aoo := \bigcup_k A_ (v k).
have mA_ k : d.-measurable (A_ (v k)) by exact: elt_mA.
have mAoo : measurable Aoo by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n; move/subset_trans; apply.
  by rewrite -setTD; apply: setDSS => //; rewrite Ubig big_ord_recr.
exists (D `\` Aoo).
have cvg_nuA : (fun n => \sum_(0 <= i < n) nu (A_ (v i))) --> nu Aoo.
  exact: charge_semi_sigma_additive.
have nuAoo : 0 <= nu Aoo.
  move/cvg_lim : cvg_nuA => <-//=; apply: nneseries_ge0 => n _.
  exact: elt_A_ge0.
have A_cvg_0 : (fun n => nu (A_ (v n))) --> 0.
  rewrite [X in X --> _](_ : _ = EFin \o (fun n => fine (nu (A_ (v n))))); last first.
    by apply/funext => n/=; rewrite fineK// fin_num_measure.
  apply: continuous_cvg => //.
  apply/(@cvg_series_cvg_0 _ [normedModType R of R^o]).
  move: cvg_nuA.
  rewrite -(@fineK _ (nu Aoo)) ?fin_num_measure//.
  move/fine_cvgP => [_ ?].
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) nu (A_ (v i)))); last first.
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite fin_num_measure.
  by apply/cvg_ex; exists (fine (nu Aoo)).
have mine_cvg_0 : (fun n => mine (d_ (v n) * 2^-1%:E) 1) --> 0.
  apply: (@squeeze_cvge _ _ _ _ (cst 0) _ (fun n => nu (A_ (v n))));
    [|exact: cvg_cst|by []].
  apply: nearW => n /=.
  by rewrite elt_mine andbT le_minr lee01 andbT mule_ge0.
have d_cvg_0 : d_ \o v --> 0.
  move/fine_cvgP : A_cvg_0 => -[_].
  move=> /(@cvgrPdist_lt _ [normedModType R of R^o])/(_ _ ltr01)[N _ hN].
  have d_v_fin_num : \forall x \near \oo, d_ (v x) \is a fin_num.
    near=> n.
    have /hN : (N <= n)%N by near: n; exists N.
    rewrite sub0r normrN /= ger0_norm ?fine_ge0//.
    have := elt_mine (v n).
    rewrite /mine; case: ifPn => [+ _ _|].
      rewrite lte_pdivr_mulr// mul1e => d2.
      by rewrite ge0_fin_numE// (lt_le_trans d2)// leey.
    move=> _ /[swap]; rewrite ltNge => -/[swap].
    by move/fine_le => -> //; rewrite fin_num_measure.
  apply/fine_cvgP; split => //.
  apply/(@cvgrPdist_lt _ [normedModType R of R^o]) => e e0.
  move/fine_cvgP : mine_cvg_0 => -[_].
  move/(@cvgrPdist_lt _ [normedModType R of R^o]).
  have : (0 < minr (e / 2) 1)%R by rewrite lt_minr// ltr01 andbT divr_gt0.
  move=> /[swap] /[apply] -[M _ hM].
  near=> n.
  rewrite sub0r normrN.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /mine/=; case: ifPn => [_|].
    rewrite fineM//=; last by near: n; exact: d_v_fin_num.
    rewrite normrM (@gtr0_norm _ 2^-1%R); last by rewrite invr_gt0.
    rewrite ltr_pdivr_mulr// => /lt_le_trans; apply.
    rewrite /minr; case: ifPn.
      by rewrite -mulrA mulVr// ?mulr1// unitfE.
    by rewrite -leNgt -ler_pdivl_mulr.
  rewrite -leNgt /minr; case: ifPn.
    by rewrite ger0_norm//= => /ltW e21 _; rewrite ltNge e21.
  by rewrite ger0_norm//= ltxx.
have nuDAoo : nu D >= nu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D); last first.
    by apply: bigcup_sub => i _; exact: elt_D.
  by rewrite chargeU// ?lee_addr// ?setDIK//; exact: measurableD.
split; [by []|exact: measurableD| | by []].
split; first exact: measurableD.
move=> E mE EDAoo.
pose H n := set_mE (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set nu E] `<=` H n.
  have : nu E \in set_mE Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply.
  move=> x/= [F [? ? FB]].
  exists F; split => //.
  by apply: (subset_trans FB); apply: setDS; exact: bigsetU_bigcup.
have nudelta n : nu E <= d_ (v n).
  move: n => [|n].
    rewrite v0/=.
    apply: ereal_sup_ub => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : nu E <= dd (U_ (v n)) by have [<- _] := Pv n.
  have /le_ereal_sup := EH n.+1.
  rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [? ? A'D]].
  exists A'; split => //.
  by apply: (subset_trans A'D); apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => nu E <= v) _ _ _ d_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomp_lemma.

Definition hahn_decomp d (T : measurableType d) (R : realType)
    (nu : {charge set T -> \bar R}) P N :=
  [/\ positive_set nu P, negative_set nu N, P `|` N = setT & P `&` N = set0].

Section hahn_decomposition_theorem.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Let elt_prop (x : set T * \bar R) := [/\ x.2 <= 0,
  negative_set nu x.1 &
  nu x.1 <= maxe (x.2 * 2^-1%:E) (- 1%E) ].

Let elt_type := {AsU : set T * \bar R * set T | elt_prop AsU.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let s_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA x : measurable (A_ x).
Proof. by move: x => [[[? ?] ?] [/= ? []]]. Qed.

Let elt_nuA x : nu (A_ x) <= 0.
Proof.
by move: x => [[[? ?] ?]] [/= ? h ?]; exact: negative_set_charge_le0.
Qed.

Let elt_s x : s_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_neg_set x : negative_set nu (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_maxe x : nu (A_ x) <= maxe (s_ x * 2^-1%:E) (- ( 1)).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let set_mE A :=
  [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` setT `\` A] ].

Let ss A := ereal_inf (set_mE A).

Let seq_inf i j := [/\ s_ j = ss (U_ i),
  A_ j `<=` setT `\` U_ i &
  U_ j = U_ i `|` A_ j].

Let next_elt U : ss U <= 0 -> { A | [/\ A `<=` setT `\` U,
  negative_set nu A &
  nu A <= maxe (ss U * 2^-1%R%:E) (- 1%E)] }.
Proof.
move=> s_le0; pose m := maxe (ss U * 2^-1%R%:E) (- 1%E); apply/cid.
move: s_le0; rewrite le_eqVlt => /predU1P[->|s_lt0].
  by exists set0; split => //; rewrite ?charge0//; exact: negative_set0.
have m0_lt0 : m < 0 by rewrite /m lt_maxl lteN10 andbT nmule_rlt0.
have : ss U < m.
  rewrite /m; have [->|s0oo] := eqVneq (ss U) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (ss U)); last first.
    by rewrite le0_fin_numE// ?(ltW s_lt0)// lt_neqAle leNye eq_sym s0oo.
  rewrite -EFinM maxEFin lte_fin lt_maxr; apply/orP; left.
  rewrite ltr_pdivl_mulr// gtr_nmulr ?ltr1n// fine_lt0// s_lt0/=.
  by rewrite lt_neqAle s0oo/= leNye.
move=> /ereal_inf_lt/cid2[_/= /cid[B [-> mB BU nuBm]]].
have nuB_le0 : nu B <= 0.
  by rewrite (le_trans (ltW nuBm))// ltW.
have [C [CB mN1 neg_set_C nuCnuB]] := hahn_decomp_lemma mB nuB_le0.
exists C; split => //.
- exact: (subset_trans CB).
- by rewrite (le_trans nuCnuB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N, hahn_decomp nu P N.
Proof.
have ss0 : ss set0 <= 0.
  by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite charge0.
have [A0 [_ negA0 A0s0]] := next_elt ss0.
have [v [v0 Pv]] : {v |
    v 0%N = exist _ (A0, ss set0, A0) (And3 ss0 negA0 A0s0) /\
    forall n, seq_inf (v n) (v n.+1)}.
  apply: dependent_choice_Type => -[[[A s] U] [/= s_le0 negA]].
  pose s' := ss U.
  have s'_le0 : s' <= 0.
    by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite charge0.
  have [A' [? negA' A's'] ] := next_elt s'_le0.
  by exists (exist _ (A', s', U `|` A') (And3 s'_le0 negA' A's')).
set N := \bigcup_k (A_ (v k)).
have mN : measurable N by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD; apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
have neg_set_N : negative_set nu N.
  by apply: bigcup_negative_set => i; exact: elt_neg_set.
pose P := setT `\` N.
have mP : measurable P by exact: measurableD.
exists P, N; split; first last.
  by rewrite /P setTD setICl.
  by rewrite /P setTD setvU.
  exact: neg_set_N.
split=> // D mD DP; rewrite leNgt; apply/negP => nuD0.
have snuD n : s_ (v n) <= nu D.
  move: n => [|n].
    by rewrite v0 /=; apply: ereal_inf_lb => /=; exists D; rewrite setD0.
  have [-> _ _] := Pv n.
  apply: ereal_inf_lb => /=; exists D; split => //.
  by apply: (subset_trans DP); apply: setDS; rewrite Ubig; exact: bigsetU_bigcup.
have max_le0 n : maxe (s_ (v n) * 2^-1%:E) (- (1)) <= 0.
  rewrite /maxe; case: ifPn => // _.
  by rewrite pmule_lle0// (le_trans (snuD _))// ltW.
have not_s_cvg_0 : ~ s_ \o v --> 0.
  move/fine_cvgP => -[sfin].
  move/(@cvgrPdist_lt _ [normedModType R of R^o]).
  have /[swap] /[apply] -[M _ hM] : (0 < `|fine (nu D)|)%R.
    by rewrite normr_gt0// fine_eq0// ?lt_eqF// fin_num_measure.
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm//; last by rewrite fine_le0.
  rewrite ltr0_norm//; last by rewrite fine_lt0// nuD0 andbT ltNye_eq fin_num_measure.
  rewrite ltr_opp2; apply/negP; rewrite -leNgt; apply: fine_le.
  - near: n; exact.
  - by rewrite fin_num_measure.
  - exact: snuD.
have nuN : nu N = \sum_(n <oo) nu (A_ (v n)).
  apply/esym/cvg_lim => //.
  apply: charge_semi_sigma_additive; [by []|exact: tA|].
  exact: bigcup_measurable.
have sum_A_maxe : \sum_(n <oo) nu (A_ (v n)) <=
    \sum_(n <oo) maxe (s_ (v n) * 2^-1%:E) (- (1)).
  exact: lee_npeseries.
have : cvg (fun n => \sum_(0 <= k < n) maxe (s_ (v k) * 2^-1%:E) (- (1))).
  by apply: is_cvg_ereal_npos_natsum_cond => n _ _; exact: max_le0.
move=> /cvg_ex[[l| |]]; first last.
  - move/cvg_lim => limNoo.
    have : nu N <= -oo by rewrite -limNoo// nuN.
    rewrite leeNy_eq => /eqP nuNoo.
    have := @fin_num_measure _ _ _ nu N mN.
    by rewrite fin_numE => /andP[+ _] => /eqP; apply.
  - move/cvg_lim => limoo.
    have := @npeseries_le0 _ (fun n => maxe (s_ (v n) * 2^-1%:E) (- (1))) xpredT.
    rewrite limoo// leNgt.
    by move=> /(_ (fun n _ => max_le0 n))/negP; apply.
move/fine_cvgP => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (s_ (v n) * 2^-1%:E) (- (1))))).
  apply/cvg_ex; exists l.
  move: cvgl.
  rewrite (_ : _ \o _ = (fun n =>
    \sum_(0 <= k < n) fine (maxe (s_ (v k) * 2^-1%:E)%E (- (1))%E))%R) //.
  apply/funext => n/=; rewrite sum_fine// => m _.
  rewrite le0_fin_numE.
    by rewrite (lt_le_trans _ (elt_maxe _))// -le0_fin_numE// ?fin_num_measure.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/(@cvg_series_cvg_0 _ [normedModType R of R^o]) => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite (_ : _ \o _ = (fun n => s_ (v n) * 2^-1%:E) \* cst 2%:E); last first.
  by apply/funext => n/=; rewrite -muleA -EFinM mulVr ?mule1// unitfE.
rewrite (_ : 0 = 0 * 2%:E); last by rewrite mul0e.
apply: cvgeM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/fine_cvgP; split.
  move/cvgrPdist_lt : maxe_cvg_0 => /(_ _ ltr01)[M _ hM].
  near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN => maxe_lt1; rewrite fin_numE; apply/andP; split.
    apply/negP => /eqP h.
    by rewrite h max_r// ?leNye//= normrN normr1 ltxx in maxe_lt1.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/(@cvgrPdist_lt _ [normedModType R of R^o]) => e e0.
have : (0 < minr e 1)%R by rewrite lt_minr// e0 ltr01.
move/cvgrPdist_lt : maxe_cvg_0 => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN /maxe/=; case: ifPn => [_|].
  rewrite normrN normr1 /minr.
  by case: ifPn; rewrite ?ltxx// ltNge => /[swap] /ltW ->.
rewrite -leNgt => ? /lt_le_trans; apply.
by rewrite /minr; case: ifPn => //; rewrite -leNgt.
Unshelve. all: by end_near. Qed.

Lemma Hahn_decomposition_uniq P1 N1 P2 N2 :
  hahn_decomp nu P1 N1 -> hahn_decomp nu P2 N2 ->
  forall S, measurable S ->
    nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> [posP1 negN1 PN1T PN10] [posP2 negN2 PN2T PN20] S mS.
move: (posP1) (negN1) (posP2) (negN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
split.
  transitivity (nu (S `&` P1 `&` P2)).
    rewrite (charge_partition _ _ mP2 mN2)//; last exact: measurableI.
    by rewrite (positive_negative0 posP1 negN2 mS) adde0.
  rewrite [RHS](charge_partition _ _ mP1 mN1)//; last exact: measurableI.
  by rewrite (positive_negative0 posP2 negN1 mS) adde0 setIAC.
transitivity (nu (S `&` N1 `&` N2)).
   rewrite (charge_partition nu _ mP2 mN2)//; last exact: measurableI.
   have := positive_negative0 posP2 negN1 mS.
   by rewrite setIAC => ->; rewrite add0e.
rewrite [RHS](charge_partition nu _ mP1 mN1)//; last exact: measurableI.
by rewrite (setIAC _ _ P1) (positive_negative0 posP1 negN2 mS) add0e setIAC.
Qed.

End hahn_decomposition_theorem.
