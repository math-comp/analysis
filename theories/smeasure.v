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
(* This file contains a tentative proof of the Hahn decomposition theorem.    *)
(*                                                                            *)
(* signed measures:                                                           *)
(*          isSignedMeasure0 == mixin for measure functions with fin_num      *)
(*                              values                                        *)
(*   isAdditiveSignedMeasure == mixin for additive signed measures            *)
(*   {additive_smeasure set T -> \bar R} == additive signed measure over T,   *)
(*                              a semi ring of sets                           *)
(*           isSignedMeasure == mixin for signed measures                     *)
(*   {smeasure set T -> \bar R} == signed measure over T, a semi ring of sets *)
(*              smrestr D mu == restriction of the signed measured mu to the  *)
(*                              domain D                                      *)
(*                                                                            *)
(* positive_set nu P == P is a positive set                                   *)
(* negative_set nu N == N is a negative set                                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

(* NB: to appear in the next release of Coq *)
Section dependent_choice_Type.
Variables (X : Type) (R : X -> X -> Prop).

Lemma dependent_choice_Type : (forall x : X, {y | R x y}) ->
  forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f n.+1)}.
Proof.
move=> h x0.
set (f := fix f n := if n is n'.+1 then proj1_sig (h (f n')) else x0).
exists f; split => //.
intro n; induction n; simpl; apply proj2_sig.
Qed.
End dependent_choice_Type.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* NB: PR in progress *)
Lemma inv_cvg (R : realType) (u : R ^nat) :
  (forall n, 0 < u n)%R ->
  (fun n => (u n)^-1) --> (0 : R)%R -> u --> +oo%R.
Proof.
move=> u0 uV0; apply/cvgPpinfty => M.
move/(@cvg_distP _ [normedModType R of R^o]) : uV0 => /(_ (`|M| + 1)^-1%R).
rewrite invr_gt0 ltr_paddl// => /(_ erefl); rewrite !near_map.
apply: filterS => n.
rewrite sub0r normrN normrV ?unitfE ?gt_eqF//.
rewrite ger0_norm; last by rewrite ltW.
rewrite ltr_pinv; last 2 first.
  by rewrite inE unitfE u0 andbT gt_eqF.
  by rewrite inE unitfE ltr_paddl// andbT gt_eqF.
move/ltW; apply: le_trans.
by rewrite (le_trans (ler_norm _))// ler_addl.
Qed.

Local Open Scope ereal_scope.

(* NB: PR in progress *)
Lemma nneseries_is_cvg (R : realType) (u : nat -> R) :
  (forall i, 0 <= u i)%R -> \sum_(k <oo) (u k)%:E < +oo -> cvg (series u).
Proof.
move=> ? ?; apply: nondecreasing_is_cvg.
  move=> m n mn; rewrite /series/=.
  rewrite -(subnKC mn) {2}/index_iota subn0 iotaD big_cat/=.
  by rewrite add0n -{2}(subn0 m) -/(index_iota _ _) ler_addl sumr_ge0.
exists (fine (\sum_(k <oo) (u k)%:E)).
rewrite /ubound/= => _ [n _ <-]; rewrite -lee_fin fineK//; last first.
  rewrite fin_num_abs gee0_abs//; apply: nneseries_ge0 => // i _.
  by rewrite lee_fin.
by rewrite -sumEFin; apply: nneseries_lim_ge => i _; rewrite lee_fin.
Qed.

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
Proof. by rewrite lt_neqAle => /andP[_]; exact: ge0_fin_numE. Qed.

(* TODO: rename seqDUE to seqDU_seqD (issue in progress) *)
Lemma seqDUE' X (S : set X) (F : (set X)^nat) :
  (fun n => S `&` F n `\` \bigcup_(i in `I_n) F i) = seqDU (fun n => S `&` F n).
Proof.
apply/funext => n; rewrite -setIDA; apply/seteqP; split.
  move=> x [Sx [Fnx UFx]]; split=> //; apply: contra_not UFx => /=.
  by rewrite bigcup_mkord -big_distrr/= => -[].
by rewrite /seqDU -setIDA bigcup_mkord -big_distrr/= setDIr setIUr setDIK set0U.
Qed.

HB.mixin Record isSignedMeasure0 d (R : numFieldType)
  (T : semiRingOfSetsType d) (mu : set T -> \bar R) := {
    isfinite : forall U, measurable U -> mu U \is a fin_num}.

HB.structure Definition SignedMeasure0 d
    (R : numFieldType) (T : semiRingOfSetsType d) := {
  mu of isSignedMeasure0 d R T mu }.

HB.mixin Record isAdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) mu of isSignedMeasure0 d R T mu := {
  smeasure_semi_additive : semi_additive mu }.

#[short(type=additive_smeasure)]
HB.structure Definition AdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isAdditiveSignedMeasure d R T mu & SignedMeasure0 d mu }.

Notation "{ 'additive_smeasure' 'set' T '->' '\bar' R }" :=
  (additive_smeasure R T) (at level 36, T, R at next level,
    format "{ 'additive_smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

#[export] Hint Resolve smeasure_semi_additive : core.

HB.mixin Record isSignedMeasure d (R : numFieldType) (T : semiRingOfSetsType d)
    mu of isAdditiveSignedMeasure d R T mu & isSignedMeasure0 d R T mu := {
  smeasure_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=smeasure)]
HB.structure Definition SignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isSignedMeasure d R T mu & AdditiveSignedMeasure d mu }.

Notation "{ 'smeasure' 'set' T '->' '\bar' R }" := (smeasure R T)
  (at level 36, T, R at next level,
    format "{ 'smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

Section signed_measure_properties.
Variables (d : _) (R : realType) (X : measurableType d).
Implicit Type mu : {smeasure set X -> \bar R}.

Lemma smeasure0 mu : mu set0 = 0.
Proof.
have /[!big_ord0] ->// := @smeasure_semi_additive _ _ _ mu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve smeasure0 : core.

Lemma ssemi_additiveW mu : mu set0 = 0 -> semi_additive mu -> semi_additive2 mu.
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

Lemma ssemi_additive2E mu : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma smeasure_semi_additive2 mu : semi_additive2 mu.
Proof. exact: ssemi_additiveW. Qed.

Hint Resolve smeasure_semi_additive2 : core.

Lemma smeasureU mu : additive2 mu.
Proof. by rewrite -ssemi_additive2E. Qed.

Lemma smeasureDI mu (A B : set X) : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -smeasure_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma smeasureD mu (A B : set X) : measurable A -> measurable B ->
  mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB.
rewrite (smeasureDI mu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite ltey_eq isfinite //; exact:measurableI.
- by rewrite ltNye_eq isfinite//; exact:measurableI.
Qed.

Lemma s_measure_partition2 mu :
    forall P N, measurable P -> measurable N -> P `|` N = setT -> P `&` N = set0 ->
      forall S, measurable S -> mu S = mu (S `&` P) + mu (S `&` N).
Proof.
move=> P N mP mN PNT PN0 S mS.
rewrite -{1}(setIT S) -PNT setIUr smeasureU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

End signed_measure_properties.
#[export] Hint Resolve smeasure0 : core.
#[export] Hint Resolve smeasure_semi_additive2 : core.

Definition smrestr d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) := fun X => f (X `&` D).

Section signed_measure_restriction.
Variables (d : _) (T : measurableType d) (R : realFieldType).
Variables (mu : {smeasure set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (smrestr mu mD).

Let s_restr_isfinite U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(@isfinite _ _ _ mu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ :=
  isSignedMeasure0.Build _ _ _ restr s_restr_isfinite.

Let s_restr_smeasure_semi_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(smeasure_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite /smrestr /FD big_distrl.
Qed.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ restr s_restr_smeasure_semi_additive.

Let s_restr_smeasure_semi_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /restr setI_bigcupl; apply: smeasure_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ :=
  isSignedMeasure.Build _ _ _ restr s_restr_smeasure_semi_sigma_additive.

End signed_measure_restriction.

Section positive_negative_set.
Variables (d : _) (R : realType) (X : measurableType d).
Implicit Types nu : {smeasure set X -> \bar R}.

Definition positive_set nu (P : set X) :=
  P \in measurable /\ forall E, E \in measurable -> E `<=` P -> (nu E >= 0)%E.

Definition negative_set nu (N : set X) :=
  N \in measurable /\ forall E, E \in measurable -> E `<=` N -> (nu E <= 0)%E.

End positive_negative_set.

Section positive_negative_set_properties.
Variables (d : _) (X : measurableType d) (R : realType).
Implicit Types nu : {smeasure set X -> \bar R}.

Lemma negative_set0 nu : negative_set nu set0.
Proof.
rewrite /negative_set inE; split => // E _.
by rewrite subset0 => ->; rewrite smeasure0.
Qed.

Lemma bigcup_negative_set nu (F : (set X)^nat) :
  (forall i, negative_set nu (F i)) ->
  negative_set nu (\bigcup_i F i).
Proof.
move=> H.
have mUF : measurable (\bigcup_i F i).
  by apply: bigcup_measurable => n _; have [/[1!inE]] := H n.
split=> [/[1!inE]//| S /[1!inE] mS SUF].
pose SF n := (S `&` F n) `\` \bigcup_(i in `I_n) F i.
have SFE : SF = seqDU (fun n => S `&` F n) by rewrite -seqDUE'.
have tS_ : trivIset setT SF by rewrite SFE; exact: trivIset_seqDU.
have SSF : S = \bigcup_i SF i.
  transitivity (\bigcup_i seqDU (fun n => S `&` F n) i); last first.
    by apply: eq_bigcup => // n _; rewrite SFE.
  by rewrite -seqDU_bigcup_eq -setI_bigcupr setIidl.
have mSF : forall n, measurable (SF n).
  move=> n; rewrite /SF; apply: measurableD.
    by apply: measurableI => //; have [/[1!inE]] := H n.
  by apply: bigcup_measurable => // k _; have [/[1!inE]] := H k.
have SFS : (fun n => \sum_(0 <= i < n) nu (SF i)) --> nu S.
  rewrite SSF; apply: smeasure_semi_sigma_additive => //.
  exact: bigcup_measurable.
have nuS_ n : nu (SF n) <= 0.
  have [_] := H n.
  by apply; rewrite ?inE// => x -[[]].
move/cvg_lim : (SFS) => <-//.
apply: ereal_lim_le.
  by apply/cvg_ex => /=; first eexists; exact: SFS.
by apply: nearW => n; exact: sume_le0.
Qed.

Lemma negative_setU nu N M :
  negative_set nu N -> negative_set nu M -> negative_set nu (N `|` M).
Proof.
move=> nN nM.
rewrite -bigcup2E.
apply: bigcup_negative_set => -[//|[//|/= _]].
exact: negative_set0.
Qed.

Lemma negative_set_smeasure_le0 nu N : negative_set nu N -> nu N <= 0.
Proof. by move=> [mN]; exact. Qed.

Lemma negative_set_bound nu S : measurable S ->
    ~ negative_set nu S -> exists l,
  (l != 0%N) &&
  `[< exists F, [/\ F `<=` S, measurable F & nu F >= l%:R^-1%:E] >].
Proof.
move=> mS=> /not_andP[/[1!inE]//|].
move=> /existsNP[F] /not_implyP[/[1!inE] mF] /not_implyP[FS].
move/negP; rewrite -ltNge => nuF0.
exists `|ceil (fine(nu F))^-1|%N; apply/andP; split.
  rewrite -lt0n absz_gt0 gt_eqF// ceil_gt0// invr_gt0// fine_gt0// nuF0/=.
  by rewrite fin_num_ltey// isfinite.
apply/asboolP; exists F; split => //.
rewrite natr_absz ger0_norm; last by rewrite ceil_ge0// invr_ge0 fine_ge0 ?ltW.
rewrite -[leRHS](@fineK _ (nu F)) ?isfinite// lee_fin.
rewrite -[leRHS](invrK (fine (nu F))) ler_pinv; last 2 first.
    rewrite inE unitfE andb_idl; last by move=> ?; rewrite gt_eqF.
    rewrite ltr0z ceil_gt0// invr_gt0// fine_gt0// nuF0/= fin_num_ltey//.
    by rewrite isfinite.
  rewrite inE unitfE andb_idl; last by move/gt_eqF/negbT.
  by rewrite invr_gt0 fine_gt0// nuF0/= fin_num_ltey// isfinite.
by rewrite ceil_ge// ceil_ge0// invr_ge0 fine_ge0// ltW.
Qed.

Lemma positive_negative0 nu P N :
  positive_set nu P -> negative_set nu N ->
  forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> [mP posP] [mN negN] S mS.
rewrite !inE in mP mN mS.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply negN.
    by rewrite inE; apply measurableI => //; exact: measurableI.
  by apply setIidPl; rewrite -setIA setIid.
rewrite -setIAC.
apply posP.
  by rewrite inE; apply measurableI => //; exact: measurableI.
by apply setIidPl; rewrite -setIA setIid.
Qed.

End positive_negative_set_properties.

Section hahn_decomposition_lemma.
Variables (d : _) (X : measurableType d) (R : realType).
Variables (mu : {smeasure set X -> \bar R}).

Variable D : set X.

Let elt_prop (x : set X * \bar R * set X) :=
  [/\ measurable x.1.1,
     0 <= mu x.1.1,
     0 <= x.1.2,
     x.1.1 `<=` D &
     mu x.1.1 >= mine (x.1.2 * 2^-1%:E) 1].

Let elt_type := {x | elt_prop x}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let d_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA (x : elt_type) : measurable (A_ x).
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_A_ge0 (x : elt_type) : 0 <= mu (A_ x).
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_d_ge0 (x : elt_type) : 0 <= d_ x.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_mine (x : elt_type) : mu (A_ x) >= mine (d_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_D (x : elt_type) : A_ x `<=` D.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let set_mE A := [set mE | exists E, [/\ mE = mu E, measurable E & E `<=` D `\` A] ].

Let dd A := ereal_sup (set_mE A).

Let seq_sup (a b : elt_type) :=
  [/\ d_ b = dd (U_ a), A_ b `<=` D `\` U_ a & U_ b = U_ a `|` A_ b ].

Let next_elt A : 0 <= dd A -> {B | [/\ measurable B,
  mu B >= 0, B `<=` D `\` A & mu B >= mine (dd A * 2^-1%:E) 1]}.
Proof.
move=> d_ge0.
pose m := mine (dd A * 2^-1%R%:E) 1%E.
apply/cid.
move: d_ge0; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite smeasure0.
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
  by rewrite (le_trans _ (ltW mmuB))// ltW.
by rewrite (le_trans _ (ltW mmuB)).
Qed.

Lemma hahn_decomposition_lemma : measurable D -> mu D <= 0 ->
  {A | [/\ A `<=` D, measurable A, negative_set mu A & mu A <= mu D] }.
Proof.
move=> mD muD_ge0.
have d0_ge0 : 0 <= dd set0.
  by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite smeasure0.
have [A0 [mA0 muA0 + A0d0]] := next_elt d0_ge0.
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, dd set0, A0) (And5 mA0 muA0 d0_ge0 A0D A0d0) /\
    forall n, seq_sup (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' ?] U] [/= mA' mA'0]].
  have d1_ge0 : 0 <= dd U.
    by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite smeasure0.
  have [A1 [mA1 muA10 A1DU A1d1] ] := next_elt d1_ge0.
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, dd U, U `|` A1) (And5 mA1 muA10 d1_ge0 A1D A1d1)).
set Aoo := \bigcup_k A_ (v k).
have mA_ k : d.-measurable (A_ (v k)) by exact: elt_mA.
have mAoo : measurable Aoo by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD.
  apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
exists (D `\` Aoo).
have cvg_muA : (fun n => \sum_(0 <= i < n) mu (A_ (v i))) --> mu Aoo.
  exact: smeasure_semi_sigma_additive.
have muAoo : 0 <= mu Aoo.
  move/cvg_lim : cvg_muA => <-//=; apply: nneseries_ge0 => n _.
  exact: elt_A_ge0.
have A_cvg_0 : (fun n => mu (A_ (v n))) --> 0.
  rewrite [X in X --> _](_ : _ = EFin \o (fun n => fine (mu (A_ (v n))))); last first.
    by apply/funext => n/=; rewrite fineK// isfinite.
  apply: continuous_cvg => //.
  apply/(@cvg_series_cvg_0 _ [normedModType R of R^o]).
  move: cvg_muA.
  rewrite -(@fineK _ (mu Aoo)) ?isfinite//.
  move/ereal_cvg_real => [_ ?].
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) mu (A_ (v i)))); last first.
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite isfinite.
  by apply/cvg_ex; exists (fine (mu Aoo)).
have mine_cvg_0 : (fun n => mine (d_ (v n) * 2^-1%:E) 1) --> 0.
  apply: (@ereal_squeeze _ (cst 0) _ (fun n => mu (A_ (v n)))); [|exact: cvg_cst|by []].
  apply: nearW => n /=.
  by rewrite elt_mine andbT le_minr lee01 andbT mule_ge0.
have d_cvg_0 : d_ \o v --> 0.
  move/ereal_cvg_real : A_cvg_0 => -[_].
  move/(@cvg_distP _ [normedModType R of R^o]) => /(_ _ ltr01).
  rewrite near_map => -[N _ hN].
  have d_v_fin_num : \forall x \near \oo, d_ (v x) \is a fin_num.
    near=> n.
    have /hN : (N <= n)%N by near: n; exists N.
    rewrite sub0r normrN /= ger0_norm ?fine_ge0//.
    have := elt_mine (v n).
    rewrite /mine; case: ifPn => [+ _ _|].
      rewrite lte_pdivr_mulr// mul1e => d2.
      by rewrite ge0_fin_numE// (lt_le_trans d2)// leey.
    move=> _ /[swap]; rewrite ltNge => -/[swap].
    by move/fine_le => -> //; rewrite isfinite.
  apply/ereal_cvg_real; split => //.
  apply/(@cvg_distP _ [normedModType R of R^o]) => e e0.
  rewrite near_map.
  move/ereal_cvg_real : mine_cvg_0 => -[_].
  move/(@cvg_distP _ [normedModType R of R^o]).
  have : (0 < minr (e / 2) 1)%R by rewrite lt_minr// ltr01 andbT divr_gt0.
  move=> /[swap] /[apply].
  rewrite near_map => -[M _ hM].
  near=> n.
  rewrite sub0r normrN.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /mine/=; case: ifPn => [_|].
    rewrite fineM//=; last by near: n; exact: d_v_fin_num.
    rewrite normrM (@gtr0_norm _ 2^-1%R); last by rewrite invr_gt0.
    rewrite ltr_pdivr_mulr//.
    move/lt_le_trans; apply.
    rewrite /minr; case: ifPn.
      by rewrite -mulrA mulVr// ?mulr1// unitfE.
    by rewrite -leNgt -ler_pdivl_mulr.
  rewrite -leNgt /minr; case: ifPn.
    by rewrite ger0_norm//= => /ltW e21 _; rewrite ltNge e21.
  by rewrite ger0_norm//= ltxx.
have muDAoo : mu D >= mu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D); last by apply: bigcup_sub => i _; exact: elt_D.
  rewrite smeasureU//; last 2 first.
    exact: measurableD.
    by rewrite setDIK.
  by rewrite lee_addr.
split; [by []|exact: measurableD| | by []].
split; first by rewrite inE; exact: measurableD.
move=> E /[1!inE] mE EDAoo.
pose H n := set_mE (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set mu E] `<=` H n.
  have : mu E \in set_mE Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply.
  move=> x/= [F [? ? FB]].
  exists F; split => //.
  apply: (subset_trans FB).
  by apply: setDS; exact: bigsetU_bigcup.
have mudelta n : mu E <= d_ (v n).
  move: n => [|n].
    rewrite v0/=.
    apply: ereal_sup_ub => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : mu E <= dd (U_ (v n)) by have [<- _] := Pv n.
  have /le_ereal_sup := EH n.+1.
  rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [? ? A'D]].
  exists A'; split => //.
  apply: (subset_trans A'D).
  by apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => mu E <= v) _ _ _ d_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_lemma.

Definition is_Hahn_decomposition d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) P N :=
  [/\ positive_set nu P, negative_set nu N, P `|` N = setT & P `&` N = set0].

Section hahn_decomposition_theorem.
Variables (d : _) (X : measurableType d) (R : realType).
Variable nu : {smeasure set X -> \bar R}.

Let elt_prop (A : set X * \bar R * set X) :=
  [/\ measurable A.1.1,
     nu A.1.1 <= 0,
     A.1.2 <= 0,
     negative_set nu A.1.1 &
     nu A.1.1 <= maxe (A.1.2 * 2^-1%:E) (- ( 1)) ].

Let elt_type := {x | elt_prop x}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let s_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA (x : elt_type) : measurable (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_nuA (x : elt_type) : nu (A_ x) <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_s (x : elt_type) : s_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_neg_set (x : elt_type) : negative_set nu (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_maxe (x : elt_type) : nu (A_ x) <= maxe (s_ x * 2^-1%:E) (- ( 1)).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let set_mE A :=
  [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` setT `\` A] ].

Let ss A := ereal_inf (set_mE A).

Let seq_inf (a b : elt_type) :=
  [/\ s_ b = ss (U_ a), A_ b `<=` setT `\` U_ a & U_ b = U_ a `|` A_ b].

Let next_elt A : ss A <= 0 -> {B |
  [/\ measurable B, nu B <= 0, B `<=` setT `\` A, negative_set nu B &
     nu B <= maxe (ss A * 2^-1%R%:E) (- 1%E)] }.
Proof.
move=> s_le0.
pose m := maxe (ss A * 2^-1%R%:E) (- 1%E).
apply/cid.
move: s_le0; rewrite le_eqVlt => /predU1P[->|s_lt0].
  by exists set0; split => //; rewrite ?smeasure0//; exact: negative_set0.
have m0_lt0 : m < 0 by rewrite /m lt_maxl lteN10 andbT nmule_rlt0.
have : ss A < m.
  rewrite /m; have [->|s0oo] := eqVneq (ss A) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (ss A)); last first.
    by rewrite le0_fin_numE// ?(ltW s_lt0)// lt_neqAle leNye eq_sym s0oo.
  rewrite -EFinM maxEFin lte_fin lt_maxr; apply/orP; left.
  rewrite ltr_pdivl_mulr// gtr_nmulr ?ltr1n// fine_lt0// s_lt0/=.
  by rewrite lt_neqAle s0oo/= leNye.
move=> /ereal_inf_lt/cid2[_/= /cid[B [-> mB BA nuBm]]].
have nuB_le0 : nu B <= 0.
  by rewrite (le_trans (ltW nuBm))// ltW.
have [C [CB mN1 neg_set_C nuCnuB]] := hahn_decomposition_lemma mB nuB_le0.
exists C; split => //.
- by rewrite (le_trans nuCnuB).
- exact: (subset_trans CB).
- by rewrite (le_trans nuCnuB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N, is_Hahn_decomposition nu P N.
Proof.
have s0_le0 : ss set0 <= 0.
  by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite smeasure0.
have [A0 [mA0 muA0_le0 _ neg_set_A0 A0d0]] := next_elt s0_le0.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, ss set0, A0) (And5 mA0 muA0_le0 s0_le0 neg_set_A0 A0d0) /\
    forall n, seq_inf (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' d'] U'] [/= mAn [nuAn_le0 neg_set_An]]].
  pose sn1 := ss U'.
  have sn1_le0 : sn1 <= 0.
    by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite smeasure0.
  have [A1 [mA1 nuA1_le0 A1U' neg_set_A1 A1d1] ] := next_elt sn1_le0.
  by exists (exist _ (A1, sn1, U' `|` A1) (And5 mA1 nuA1_le0 sn1_le0 neg_set_A1 A1d1)).
set N := \bigcup_k (A_ (v k)).
have mN : measurable N by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD.
  apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
have neg_set_N : negative_set nu N.
  by apply: bigcup_negative_set => i; exact: elt_neg_set.
pose P := setT `\` N.
have mP : measurable P by exact: measurableD.
exists P, N; split; first last.
  by rewrite /P setTD setvI.
  by rewrite /P setTD setvU.
  exact: neg_set_N.
rewrite /positive_set inE; split=> // D; rewrite inE => mD DP; rewrite leNgt; apply/negP => nuD0.
have snuD n : s_ (v n) <= nu D.
  move: n => [|n].
    by rewrite v0 /=; apply: ereal_inf_lb => /=; exists D; rewrite setD0.
  have [-> _ _] := Pv n.
  apply: ereal_inf_lb => /=; exists D; split => //.
  apply: (subset_trans DP).
  apply: setDS.
  by rewrite Ubig; exact: bigsetU_bigcup.
have max_le0 n : maxe (s_ (v n) * 2^-1%:E) (- (1)) <= 0.
  rewrite /maxe; case: ifPn => // _.
  by rewrite pmule_lle0// (le_trans (snuD _))// ltW.
have not_s_cvg_0 : ~ s_ \o v --> 0.
  move/ereal_cvg_real => -[sfin].
  move/(@cvg_distP _ [normedModType R of R^o]).
  have : (0 < `|fine (nu D)|)%R by rewrite normr_gt0// fine_eq0// ?lt_eqF// isfinite.
  move=> /[swap] /[apply].
  rewrite near_map => -[M _ hM].
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm//; last by rewrite fine_le0.
  rewrite ltr0_norm//; last by rewrite fine_lt0// nuD0 andbT ltNye_eq isfinite.
  rewrite ltr_opp2; apply/negP; rewrite -leNgt; apply: fine_le.
  - near: n; exact.
  - by rewrite isfinite.
  - exact: snuD.
have nuN : nu N = \sum_(n <oo) nu (A_ (v n)).
  apply/esym/cvg_lim => //.
  by apply: smeasure_semi_sigma_additive; [by []|exact: tA|exact: bigcup_measurable].
have sum_A_maxe : \sum_(n <oo) nu (A_ (v n)) <= \sum_(n <oo) maxe (s_ (v n) * 2^-1%:E) (- (1)).
  exact: lee_npeseries.
have : cvg (fun n => \sum_(0 <= k < n) maxe (s_ (v k) * 2^-1%:E) (- (1))).
  by apply: is_cvg_ereal_npos_natsum_cond => n _ _; exact: max_le0.
move=> /cvg_ex[[l| |]]; first last.
  - move/cvg_lim => limNoo.
    have : nu N <= -oo by rewrite -limNoo// nuN.
    rewrite leeNy_eq => /eqP nuNoo.
    have := @isfinite _ _ _ nu N mN.
    by rewrite fin_numE => /andP[+ _] => /eqP; apply.
  - move/cvg_lim => limoo.
    have := @npeseries_le0 _ (fun n => maxe (s_ (v n) * 2^-1%:E) (- (1))) xpredT.
    rewrite limoo// leNgt.
    by move=> /(_ (fun n _ => max_le0 n))/negP; apply.
move/ereal_cvg_real => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (s_ (v n) * 2^-1%:E) (- (1))))).
  apply/cvg_ex; exists l.
  move: cvgl.
  rewrite [X in X --> _](_ : _ =
    (fun n => \sum_(0 <= k < n) fine (maxe (s_ (v k) * 2^-1%:E)%E (- (1))%E))%R) //.
  apply/funext => n/=.
  rewrite sum_fine// => i _.
  rewrite le0_fin_numE.
    by rewrite (lt_le_trans _ (elt_maxe _))// -le0_fin_numE// ?isfinite.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/(@cvg_series_cvg_0 _ [normedModType R of R^o]) => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite [X in X --> _](_ : _ = (fun n => s_ (v n) * 2^-1%:E) \* cst 2%:E); last first.
  apply/funext => n/=.
  by rewrite -muleA -EFinM mulVr ?mule1// unitfE.
rewrite (_ : 0 = 0 * 2%:E); last by rewrite mul0e.
apply: ereal_cvgM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/ereal_cvg_real; split.
  move/(@cvg_distP _ [normedModType R of R^o]) : maxe_cvg_0 => /(_ _ ltr01).
  rewrite near_map => -[M _ hM].
  near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN => maxe_lt1.
  rewrite fin_numE; apply/andP; split.
    apply/negP => /eqP h.
    by rewrite h max_r// ?leNye//= normrN normr1 ltxx in maxe_lt1.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/(@cvg_distP _ [normedModType R of R^o]) => e e0.
rewrite near_map.
move/(@cvg_distP _ [normedModType R of R^o]) : maxe_cvg_0.
have : (0 < minr e 1)%R by rewrite lt_minr// e0 ltr01.
move=> /[swap] /[apply].
rewrite near_map => -[M _ hM].
near=> n.
rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN.
rewrite /maxe/=; case: ifPn => [_|].
  rewrite normrN normr1 /minr.
  by case: ifPn; rewrite ?ltxx// ltNge => /[swap] /ltW ->.
rewrite -leNgt => ?.
move/lt_le_trans; apply.
rewrite /minr; case: ifPn => //.
by rewrite -leNgt.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_theorem.

Lemma Hahn_decomposition_measure_uniq d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  forall P1 N1 P2 N2,
   is_Hahn_decomposition nu P1 N1 -> is_Hahn_decomposition nu P2 N2 ->
 forall S, measurable S ->
    nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> P1 N1 P2 N2 Hahn1 Hahn2 S mS.
move: (Hahn1) (Hahn2) => [posP1 negN1 PN1T PN10] [posP2 negN2 PN2T PN20].
move: (posP1) (negN1) (posP2) (negN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
rewrite !inE in mP1 mN1 mP2 mN2.
have mSP1 := (measurableI S P1 mS mP1).
have mSN1 := (measurableI S N1 mS mN1).
have mSP2 := (measurableI S P2 mS mP2).
have mSN2 := (measurableI S N2 mS mN2).
split.
  apply (@eq_trans _ _ (nu (S `&` P1 `&` P2))).
     by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
       (positive_negative0 posP1 negN2 mS) adde0.
   by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
     (positive_negative0 posP2 negN1 mS) adde0 setIAC.
apply (@eq_trans _ _ (nu (S `&` N1 `&` N2))).
   by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
     {1}setIAC (positive_negative0 posP2 negN1 mS) add0e.
 by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
   (setIAC _ _ P1) (positive_negative0 posP1 negN2 mS) add0e setIAC.
Qed.
