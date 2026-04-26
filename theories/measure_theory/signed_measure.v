(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference finmap fingroup perm rat.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets cardinality.
From mathcomp Require Import functions fsbigop set_interval reals ereal.
From mathcomp Require Import topology numfun normedtype derive sequences esum.
From mathcomp Require Import measurable_structure measurable_function.
From mathcomp Require Import measure_function measure_negligible.

(**md**************************************************************************)
(* # Charges (signed measures)                                                *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file contains a formalization of charges (a.k.a. signed measures) and *)
(* their theory (Hahn decomposition theorem, etc.).                           *)
(*                                                                            *)
(* References:                                                                *)
(* - Y. Ishiguro, R. Affeldt. The Radon-Nikodym Theorem and the Lebesgue-     *)
(*   Stieltjes measure in Coq. Computer Software 41(2) 2024                   *)
(* - R. Affeldt, Y. Ishiguro, Z. Stone. A formal foundation for equational    *)
(*   reasoning on probabilistic programs. APLAS 2025                          *)
(*                                                                            *)
(* ## Structures for functions on classes of sets                             *)
(* ```                                                                        *)
(* {additive_charge set T -> \bar R} == notation for additive charges where   *)
(*                              T is a semiring of sets and R is a            *)
(*                              numFieldType                                  *)
(*                              The HB class is AdditiveCharge.               *)
(*  {charge set T -> \bar R} == type of charges over T a semiring of sets     *)
(*                              where R is a numFieldType                     *)
(*                              The HB class is Charge.                       *)
(*                  isCharge == factory corresponding to the "textbook        *)
(*                              definition" of charges                        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Instances of mathematical structures                                    *)
(* ```                                                                        *)
(*  measure_of_charge nu nu0 == measure corresponding to the charge nu, nu0   *)
(*                              is a proof that nu is non-negative            *)
(*              crestr nu mD == restriction of the charge nu to the domain D  *)
(*                              where mD is a proof that D is measurable      *)
(*             crestr0 nu mD == csrestr nu mD that returns 0 for              *)
(*                              non-measurable sets                           *)
(*                     czero == zero charge                                   *)
(*               cscale r nu == charge nu scaled by a factor r : R            *)
(*                   copp nu == the charge corresponding to the opposite of   *)
(*                              the charges nu                                *)
(*                cadd n1 n2 == the charge corresponding to the sum of        *)
(*                              charges n1 and n2                             *)
(* charge_of_finite_measure mu == charge corresponding to a finite measure mu *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Theory                                                                  *)
(* ```                                                                        *)
(*         nu.-positive_set P == P is a positive set with nu a charge         *)
(*         nu.-negative_set N == N is a negative set with nu a charge         *)
(* hahn_decomposition nu P N == the full set can be decomposed in P and N,    *)
(*                              a positive set and a negative set for the     *)
(*                              charge nu                                     *)
(*           jordan_pos nuPN == the charge obtained by restricting the charge *)
(*                              nu to the positive set P of the Hahn          *)
(*                              decomposition nuPN: hahn_decomposition nu P N *)
(*           jordan_neg nuPN == the charge obtained by restricting the charge *)
(*                              nu to the positive set N of the Hahn          *)
(*                              decomposition nuPN: hahn_decomposition nu P N *)
(*     charge_variation nuPN == variation of the charge nu                    *)
(*                           := jordan_pos nuPN \+ jordan_neg nuPN            *)
(*  charge_dominates mu nuPN := content_dominates mu (charge_variation nuPN)  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'additive_charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'additive_charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "nu .-negative_set" (at level 2, format "nu .-negative_set").
Reserved Notation "nu .-positive_set" (at level 2, format "nu .-positive_set").

Declare Scope charge_scope.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

HB.mixin Record isAdditiveCharge d (T : semiRingOfSetsType d) (R : numFieldType)
  (mu : set T -> \bar R) :=
  { charge_semi_additive : measure_function.semi_additive mu }.

#[short(type=additive_charge)]
HB.structure Definition AdditiveCharge d (T : semiRingOfSetsType d)
  (R : numFieldType) := { mu of isAdditiveCharge d T R mu & FinNumFun d mu }.

Notation "{ 'additive_charge' 'set' T '->' '\bar' R }" :=
  (additive_charge T R) : ring_scope.

#[export] Hint Resolve charge_semi_additive : core.

HB.mixin Record isSemiSigmaAdditive d (T : semiRingOfSetsType d) (R : numFieldType)
    (mu : set T -> \bar R) := {
  charge_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=charge)]
HB.structure Definition Charge d (T : semiRingOfSetsType d) (R : numFieldType)
  := { mu of isSemiSigmaAdditive d T R mu & AdditiveCharge d mu }.

Notation "{ 'charge' 'set' T '->' '\bar' R }" := (charge T R) : ring_scope.

HB.factory Record isCharge d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : set T -> \bar R) := {
  charge0 : mu set0 = 0 ;
  charge_finite : forall x, d.-measurable x -> mu x \is a fin_num ;
  charge_sigma_additive : semi_sigma_additive mu
}.

HB.builders Context d (T : semiRingOfSetsType d) (R : realFieldType)
  mu & isCharge d T R mu.

Let finite : fin_num_fun mu. Proof. exact: charge_finite. Qed.

HB.instance Definition _ := isFinNumFun.Build d T R mu finite.

Let semi_additive : measure_function.semi_additive mu.
Proof.
move=> I n mI trivI mUI.
rewrite (semi_sigma_additive_is_additive charge0)//.
exact: charge_sigma_additive.
Qed.

HB.instance Definition _ := isAdditiveCharge.Build d T R mu semi_additive.

Let semi_sigma_additive : semi_sigma_additive mu.
Proof. exact: charge_sigma_additive. Qed.

HB.instance Definition _ :=
  isSemiSigmaAdditive.Build d T R mu semi_sigma_additive.

HB.end.

Section charge_lemmas.
Context d (T : ringOfSetsType d) (R : numFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma charge0 nu : nu set0 = 0.
Proof.
have /[!big_ord0] ->// := @charge_semi_additive _ _ _ nu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve charge0 : core.

Lemma charge_semi_additiveW nu :
  nu set0 = 0 -> measure_function.semi_additive nu -> semi_additive2 nu.
Proof.
move=> nu0 anu A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(anu (bigcup2 A B)) ->; last 1 first.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
move=> [|[|i]] [|[|j]]/= _ _ //.
- by rewrite AB => -[].
- by rewrite setI0 => -[].
- by rewrite setIC AB => -[].
- by rewrite setI0 => -[].
- by rewrite set0I => -[].
- by rewrite set0I => -[].
- by rewrite setI0 => -[].
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
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
- by rewrite -setDDr setDv setD0.
Qed.

Lemma charge_partition nu S P N :
  measurable S -> measurable P -> measurable N ->
  P `|` N = [set: T] -> P `&` N = set0 -> nu S = nu (S `&` P) + nu (S `&` N).
Proof.
move=> mS mP mN PNT PN0; rewrite -{1}(setIT S) -PNT setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

End charge_lemmas.
#[export] Hint Resolve charge0 : core.
#[export] Hint Resolve charge_semi_additive2 : core.

Definition measure_of_charge d (T : semiRingOfSetsType d) (R : numFieldType)
  (nu : set T -> \bar R) & (forall E, 0 <= nu E) := nu.

Section measure_of_charge.
Context d (T : ringOfSetsType d) (R : realFieldType).
Variables (nu : {charge set T -> \bar R}) (nupos : forall E, 0 <= nu E).

Local Notation mu := (measure_of_charge nupos).

Let mu0 : mu set0 = 0. Proof. exact: charge0. Qed.

Let mu_ge0 S : 0 <= mu S. Proof. by rewrite nupos. Qed.

Let mu_sigma_additive : semi_sigma_additive mu.
Proof. exact: charge_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ T R (measure_of_charge nupos)
  mu0 mu_ge0 mu_sigma_additive.

End measure_of_charge.
Arguments measure_of_charge {d T R}.

Section charge_of_finite_measure.
Context d (T : measurableType d) (R : realType).
Variables (mu : {finite_measure set T -> \bar R}).

Definition charge_of_finite_measure : set T -> \bar R := mu.

Local Notation nu := charge_of_finite_measure.

Let nu0 : nu set0 = 0. Proof. exact: measure0. Qed.

Let nu_finite S : measurable S -> nu S \is a fin_num.
Proof. exact: fin_num_measure. Qed.

Let nu_sigma_additive : semi_sigma_additive nu.
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isCharge.Build _ T R nu
  nu0 nu_finite nu_sigma_additive.

End charge_of_finite_measure.
Arguments charge_of_finite_measure {d T R}.

Section charge_lemmas_realFieldType.
Context d (T : ringOfSetsType d) (R : realFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma chargeD nu (A B : set T) : measurable A -> measurable B ->
  nu (A `\` B) = nu A - nu (A `&` B).
Proof.
move=> mA mB.
rewrite (chargeDI nu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite ltNye_eq fin_num_measure//; exact:measurableI.
- by rewrite ltey_eq fin_num_measure//; exact:measurableI.
Qed.

End charge_lemmas_realFieldType.

Definition crestr d (T : semiRingOfSetsType d) (R : numDomainType) (D : set T)
  (f : set T -> \bar R) & measurable D := fun X => f (X `&` D).

Section charge_restriction.
Context d (T : measurableType d) (R : numFieldType).
Variables (nu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr nu mD).

Let crestr_finite_measure_function U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(fin_num_measure nu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ := isFinNumFun.Build _ _ _
  restr crestr_finite_measure_function.

Let crestr_semi_additive : measure_function.semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(charge_semi_additive _ _ mFD)//; first exact: bigsetU_measurable.
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
  isSemiSigmaAdditive.Build _ _ _ restr crestr_semi_sigma_additive.

End charge_restriction.

Definition crestr0 d (T : semiRingOfSetsType d) (R : numFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) :=
    fun X => if X \in measurable then crestr f mD X else 0.

Section charge_restriction0.
Context d (T : measurableType d) (R : realFieldType).
Variables (nu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr0 nu mD).

Let crestr00 : restr set0 = 0.
Proof.
rewrite/crestr0 ifT ?inE // /crestr set0I.
exact: charge0.
Qed.

Let crestr0_fin_num_fun : fin_num_fun restr.
Proof.
by move=> U mU; rewrite /crestr0 mem_set// fin_num_measure.
Qed.

Let crestr0_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; rewrite /crestr0 mem_set//.
rewrite [X in X @ _ --> _](_ : _ = (fun n => \sum_(0 <= i < n) crestr nu mD (F i))).
  by apply/funext => n; apply: eq_bigr => i _; rewrite mem_set.
exact: charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _
    restr crestr00 crestr0_fin_num_fun crestr0_sigma_additive.

End charge_restriction0.

Section charge_zero.
Context d (T : semiRingOfSetsType d) (R : realFieldType).
Local Open Scope ereal_scope.

Definition czero (A : set T) : \bar R := 0.

Let czero0 : czero set0 = 0. Proof. by []. Qed.

Let czero_finite_measure_function B : measurable B -> czero B \is a fin_num.
Proof. by []. Qed.

Let czero_sigma_additive : semi_sigma_additive czero.
Proof.
move=> F mF tF mUF; rewrite [X in X @ _ --> _](_ : _ = cst 0); last exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ czero
     czero0 czero_finite_measure_function czero_sigma_additive.

End charge_zero.
Arguments czero {d T R}.

Section charge_scale.
Local Open Scope ereal_scope.
Context d (T : ringOfSetsType d) (R : realFieldType).
Variables (r : R) (nu : {charge set T -> \bar R}).

Definition cscale (A : set T) : \bar R := r%:E * nu A.

Let cscale0 : cscale set0 = 0. Proof. by rewrite /cscale charge0 mule0. Qed.

Let cscale_finite_measure_function U : measurable U -> cscale U \is a fin_num.
Proof. by move=> mU; apply: fin_numM => //; exact: fin_num_measure. Qed.

HB.instance Definition _ := isFinNumFun.Build _ _ _
  cscale cscale_finite_measure_function.

Let cscale_semi_additive : measure_function.semi_additive cscale.
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
    (fun n => r%:E * \sum_(0 <= i < n) nu (F i))).
  apply/funext => k; rewrite fin_num_sume_distrr// => i j _ _.
  by rewrite fin_num_adde_defl// fin_num_measure.
rewrite /mscale; have [->|r0] := eqVneq r 0%R.
  rewrite mul0e [X in X @ _ --> _](_ : _ = (fun=> 0)); last exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeZl => //; exact: charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ cscale
  cscale0 cscale_finite_measure_function cscale_sigma_additive.

End charge_scale.

Lemma dominates_cscalel d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R})
  (nu : {charge set T -> \bar R})
  (c : R) : nu `<< mu -> cscale c nu `<< mu.
Proof.
move=> /null_content_dominatesP numu; apply/null_content_dominatesP => E mE.
by move/(numu _ mE) => E0; apply/eqP; rewrite mule_eq0 eqe E0/= eqxx orbT.
Qed.

Lemma dominates_cscaler d (T : measurableType d) (R : realType)
  (nu : {charge set T -> \bar R})
  (mu : set T -> \bar R)
  (c : R) : c != 0%R -> mu `<< nu -> mu `<< cscale c nu.
Proof.
move=> /negbTE c0 /null_dominates_trans; apply => E nE A mA AE.
by have /eqP := nE A mA AE; rewrite mule_eq0 eqe c0/= => /eqP.
Qed.

Section charge_opp.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Definition copp := \- nu.

Let copp0 : copp set0 = 0.
Proof. by rewrite /copp charge0 oppe0. Qed.

Let copp_finite A : measurable A -> copp A \is a fin_num.
Proof. by move=> mA; rewrite fin_numN fin_num_measure. Qed.

Let copp_sigma_additive : semi_sigma_additive copp.
Proof.
move=> F mF tF mUF; rewrite /copp; under eq_fun.
  move=> n; rewrite sumeN.
    by move=> p q _ _; rewrite fin_num_adde_defl// fin_num_measure.
  over.
exact/cvgeN/charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ copp
  copp0 copp_finite copp_sigma_additive.

End charge_opp.

Lemma cscaleN1 {d} {T : ringOfSetsType d} {R : realFieldType}
    (nu : {charge set T -> \bar R}) :
  cscale (-1) nu = \- nu.
Proof. by rewrite /cscale/=; apply/funext => x; rewrite mulN1e. Qed.

Section charge_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (n1 n2 : {charge set T -> \bar R}).

Definition cadd := n1 \+ n2.

Let cadd0 : cadd set0 = 0.
Proof. by rewrite /cadd 2!charge0 adde0. Qed.

Let cadd_finite A : measurable A -> cadd A \is a fin_num.
Proof. by move=> mA; rewrite fin_numD !fin_num_measure. Qed.

Let cadd_sigma_additive : semi_sigma_additive cadd.
Proof.
move=> F mF tF mUF; rewrite /cadd.
under eq_fun do rewrite big_split; apply: cvg_trans.
  apply: (@cvgeD _ _ _ _ _ _ (n1 (\bigcup_n F n)) (n2 (\bigcup_n F n))).
  - by rewrite fin_num_adde_defr// fin_num_measure.
  - exact: charge_semi_sigma_additive.
  - exact: charge_semi_sigma_additive.
exact: cvg_id.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ cadd
  cadd0 cadd_finite cadd_sigma_additive.

End charge_add.

Lemma dominates_cadd d (T : measurableType d) (R : realType)
  (mu : {sigma_finite_measure set T -> \bar R})
  (nu0 nu1 : {charge set T -> \bar R}) :
  nu0 `<< mu -> nu1 `<< mu ->
  cadd nu0 nu1 `<< mu.
Proof.
move=> /null_content_dominatesP nu0mu.
move=> /null_content_dominatesP nu1mu A nA A0 mA0 A0A.
by have muA0 := nA _ mA0 A0A; rewrite /cadd nu0mu// nu1mu// adde0.
Qed.

Section pushforward_charge.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (f : T1 -> T2).
Variables (R : realFieldType) (nu : {charge set T1 -> \bar R}).

Hypothesis mf : measurable_fun setT f.

Let pushforward0 : pushforward nu f set0 = 0.
Proof. by rewrite /pushforward preimage_set0 charge0. Qed.

Let pushforward_finite A : measurable A -> pushforward nu f A \is a fin_num.
Proof.
move=> mA; apply: fin_num_measure.
by rewrite -[X in measurable X]setTI; exact: mf.
Qed.

Let pushforward_sigma_additive : semi_sigma_additive (pushforward nu f).
Proof.
move=> F mF tF mUF; rewrite /pushforward preimage_bigcup.
apply: charge_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: mf.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mf.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ (pushforward nu f)
  pushforward0 pushforward_finite pushforward_sigma_additive.

End pushforward_charge.

HB.builders Context d (T : measurableType d) (R : realType)
  (mu : set T -> \bar R) & Measure_isFinite d T R mu.

Let mu0 : mu set0 = 0.
Proof. by apply: measure0. Qed.

HB.instance Definition _ := isCharge.Build _ _ _
  mu (measure0 mu) fin_num_measure measure_semi_sigma_additive.

HB.end.

Lemma dominates_pushforward d d' (T : measurableType d) (T' : measurableType d')
  (R : realType) (mu : {measure set T -> \bar R})
  (nu : {charge set T -> \bar R}) (f : T -> T') (mf : measurable_fun setT f) :
  nu `<< mu -> pushforward nu f `<< pushforward mu f.
Proof.
move=> /null_content_dominatesP numu; apply/null_content_dominatesP => A mA.
by apply: numu; rewrite -[X in measurable X]setTI; exact: mf.
Qed.

Section positive_negative_set.
Context d (T : semiRingOfSetsType d) (R : numDomainType).
Implicit Types nu : set T -> \bar R.

Definition positive_set nu (P : set T) :=
  measurable P /\ forall A, measurable A -> A `<=` P -> nu A >= 0.

Definition negative_set nu (N : set T) :=
  measurable N /\ forall A, measurable A -> A `<=` N -> nu A <= 0.

End positive_negative_set.

Notation "nu .-negative_set" := (negative_set nu) : charge_scope.
Notation "nu .-positive_set" := (positive_set nu) : charge_scope.

Local Open Scope charge_scope.

Section positive_negative_set_lemmas.
Context d (T : measurableType d) (R : numFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma negative_set_charge_le0 nu N : nu.-negative_set N -> nu N <= 0.
Proof. by move=> [mN]; exact. Qed.

Lemma negative_set0 nu : nu.-negative_set set0.
Proof. by split => // A _; rewrite subset0 => ->; rewrite charge0. Qed.

Lemma positive_negative0 nu P N : nu.-positive_set P -> nu.-negative_set N ->
  forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> [mP posP] [mN negN] S mS; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: negN; first by apply: measurableI => //; exact: measurableI.
  by apply/setIidPl; rewrite -setIA setIid.
rewrite -setIAC.
apply: posP; first by apply: measurableI => //; exact: measurableI.
by apply/setIidPl; rewrite -setIA setIid.
Qed.

End positive_negative_set_lemmas.

Section positive_negative_set_realFieldType.
Context d (T : measurableType d) (R : realFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma bigcup_negative_set nu (F : (set T)^nat) :
    (forall i, nu.-negative_set (F i)) ->
  nu.-negative_set (\bigcup_i F i).
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
  nu.-negative_set N -> nu.-negative_set M -> nu.-negative_set (N `|` M).
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
Let g_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?]] []. Qed.
Let A_D x : A_ x `<=` D. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let g_ge0 x : 0 <= g_ x. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let nuA_g_ x : nu (A_ x) >= mine (g_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let nuA_ge0 x : 0 <= nu (A_ x).
Proof. by rewrite (le_trans _ (nuA_g_ _))// le_min lee01 andbT mule_ge0. Qed.

Let subDD A := [set nu E | E in [set E | measurable E /\ E `<=` D `\` A] ].

Let d_ A := ereal_sup (subDD A).

Let d_ge0 X : 0 <= d_ X.
Proof. by apply: ereal_sup_ubound => /=; exists set0; rewrite ?charge0. Qed.

Let elt_rel i j :=
  [/\ g_ j = d_ (U_ i),  A_ j `<=` D `\` U_ i & U_ j = U_ i `|` A_ j ].

Let next_elt A :
  { B | [/\ measurable B, B `<=` D `\` A & nu B >= mine (d_ A * 2^-1%:E) 1] }.
Proof.
pose m := mine (d_ A * 2^-1%R%:E) 1; apply/cid.
have := d_ge0 A; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite charge0 mul0e minEle lee01.
have /ereal_sup_gt/cid2[_ [B/= [mB BDA <- mnuB]]] : m < d_ A.
  rewrite /m; have [->|dn1oo] := eqVneq (d_ A) +oo.
    by rewrite min_r ?ltey ?gt0_mulye ?leey.
  rewrite -(@fineK _ (d_ A)); first by rewrite gt0_fin_numE// ltey.
  rewrite -EFinM -fine_min// lte_fin gt_min; apply/orP; left.
  by rewrite ltr_pdivrMr// ltr_pMr ?ltr1n// fine_gt0// d_gt0/= ltey.
by exists B; split => //; rewrite (le_trans _ (ltW mnuB)).
Qed.

Let mine2_cvg_0_cvg_0 (u : (\bar R)^nat) : (forall k, 0 <= u k) ->
  mine (u n * 2^-1%:E) 1 @[n --> \oo] --> 0 -> u n @[n --> \oo] --> 0.
Proof.
move=> u0 h.
have u2 n : u n = 2%:E * (u n * 2^-1%:E) by rewrite muleCA -EFinM divff ?mule1.
rewrite (eq_cvg _ _ u2) -[X in _ --> X]/(nbhs 0).
rewrite -(mule0 2%:E); apply: cvgeZl => //.
by apply: (mine_cvg_0_cvg_0 lte01) => // n; rewrite mule_ge0.
Qed.

Lemma hahn_decomposition_lemma : measurable D ->
  {A | [/\ A `<=` D, nu.-negative_set A & nu A <= nu D]}.
Proof.
move=> mD; have [A0 [mA0 + A0d0]] := next_elt set0.
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, d_ set0, A0) (And4 mA0 A0D (d_ge0 set0) A0d0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice => -[[[A' ?] U] [/= mA' A'D]].
  have [A1 [mA1 A1DU A1t1]] := next_elt U.
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, d_ U, U `|` A1) (And4 mA1 A1D (d_ge0 U) A1t1)).
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
  move/cvg_lim : cvg_nuA => <-//=; apply: nneseries_ge0 => n _ _.
  exact: nuA_ge0.
have A_cvg_0 : nu (A_ (v n)) @[n --> \oo] --> 0.
  rewrite [X in X @ _ --> _](_ : _ = (fun n => (fine (nu (A_ (v n))))%:E)).
    by apply/funext => n/=; rewrite fineK// fin_num_measure.
  apply: continuous_cvg => //; apply: cvg_series_cvg_0.
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) nu (A_ (v i)))).
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite fin_num_measure.
  move: cvg_nuA; rewrite -(@fineK _ (nu Aoo)) ?fin_num_measure//.
  by move=> /fine_cvgP[_ ?]; apply/cvg_ex; exists (fine (nu Aoo)).
have mine_cvg_0 : (mine (g_ (v n) * 2^-1%:E) 1) @[n --> \oo] --> 0.
  apply: (@squeeze_cvge _ _ _ _ _ _ (fun n => nu (A_ (v n))));
    [|exact: cvg_cst|by []].
  by apply: nearW => n /=; rewrite nuA_g_ andbT le_min lee01 andbT mule_ge0.
have g_cvg_0 : (g_ \o v) n @[n --> \oo] --> 0 by apply: mine2_cvg_0_cvg_0 => //=.
have nuDAoo : nu D >= nu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D).
    by apply: bigcup_sub => i _; exact: A_D.
  by rewrite chargeU// ?leeDr// ?setDIK//; exact: measurableD.
split; [by []| |by []]; split; [exact: measurableD | move=> E mE EDAoo].
pose H n := subDD (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set nu E] `<=` H n.
  have : nu E \in subDD Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply => x/= [F [mF FDAoo ?]].
  exists F => //; split => //.
  by apply: (subset_trans FDAoo); apply: setDS; exact: bigsetU_bigcup.
have nudelta n : nu E <= g_ (v n).
  move: n => [|n].
    rewrite v0/=; apply: ereal_sup_ubound => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : nu E <= d_ (U_ (v n)) by have [<- _] := Pv n.
  have /ereal_sup_le := EH n.+1; rewrite ereal_sup1 => /le_trans; apply.
  apply/ereal_sup_le => x/= [A' [mA' A'D ?]].
  exists A' => //; split => //.
  by apply: (subset_trans A'D); apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => nu E <= v) _ _ _ g_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_lemma.

Definition hahn_decomposition d (T : semiRingOfSetsType d) (R : numFieldType)
    (nu : {charge set T -> \bar R}) P N :=
  [/\ nu.-positive_set P, nu.-negative_set N, P `|` N = [set: T] & P `&` N = set0].

Section hahn_decomposition_theorem.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Let elt_prop (x : set T * \bar R) := [/\ x.2 <= 0,
  nu.-negative_set x.1 & nu x.1 <= maxe (x.2 * 2^-1%:E) (- 1%E) ].

Let elt_type := {AzU : set T * \bar R * set T | elt_prop AzU.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let z_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?] [/= ? []]]. Qed.
Let negative_set_A_ x : nu.-negative_set (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.
Let nuA_z_ x : nu (A_ x) <= maxe (z_ x * 2^-1%:E) (- 1%E).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let nuA_le0 x : nu (A_ x) <= 0.
Proof. by move: x => [[[? ?] ?]] [? h ?]; exact: negative_set_charge_le0. Qed.

Let z_le0 x : z_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let subC A := [set nu E | E in [set E | measurable E /\ E `<=` ~` A] ].

Let s_ A := ereal_inf (subC A).

Let s_le0 X : s_ X <= 0.
Proof.
by apply: ereal_inf_lbound => /=; exists set0; rewrite ?charge0//=; split.
Qed.

Let elt_rel i j :=
  [/\ z_ j = s_ (U_ i), A_ j `<=` ~` U_ i & U_ j = U_ i `|` A_ j].

Let next_elt U : { A | [/\ A `<=` ~` U,
  negative_set nu A & nu A <= maxe (s_ U * 2^-1%R%:E) (- 1%E)] }.
Proof.
pose m := maxe (s_ U * 2^-1%R%:E) (- 1%E); apply/cid.
have := s_le0 U; rewrite le_eqVlt => /predU1P[->|s_lt0].
  exists set0; split => //; rewrite ?charge0 ?mul0e ?maxEle ?lee0N1//.
  exact: negative_set0.
have /ereal_inf_lt/cid2[_ [B/= [mB BU] <-] nuBm] : s_ U < m.
  rewrite /m; have [->|s0oo] := eqVneq (s_ U) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (s_ U)); first by rewrite lt0_fin_numE// ltNye.
  rewrite -EFinM -fine_max// lte_fin lt_max; apply/orP; left.
  by rewrite ltr_pdivlMr// gtr_nMr ?ltr1n// fine_lt0// s_lt0/= ltNye andbT.
have [C [CB nsC nuCB]] := hahn_decomposition_lemma nu mB.
exists C; split => //; first exact: (subset_trans CB).
by rewrite (le_trans nuCB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N, hahn_decomposition nu P N.
Proof.
have [A0 [_ negA0 A0s0]] := next_elt set0.
have [v [v0 Pv]] : {v |
    v 0%N = exist _ (A0, s_ set0, A0) (And3 (s_le0 set0) negA0 A0s0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice => -[[[A s] U] [/= s_le0' nsA]].
  have [A' [? nsA' A's'] ] := next_elt U.
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
    rewrite v0 /=; apply: ereal_inf_lbound; exists D; split => //.
    by rewrite setC0.
  have [-> _ _] := Pv n; apply: ereal_inf_lbound => /=; exists D; split => //.
  apply: (subset_trans DP); apply: subsetC; rewrite Ubig.
  exact: bigsetU_bigcup.
have max_le0 n : maxe (z_ (v n) * 2^-1%:E) (- 1%E) <= 0.
  by rewrite ge_max leeN10 andbT pmule_lle0.
have not_s_cvg_0 : ~ (z_ \o v) n @[n --> \oo]  --> 0.
  move/fine_cvgP => -[zfin] /cvgrPdist_lt.
  have /[swap] /[apply] -[M _ hM] : (0 < `|fine (nu D)|)%R.
    by rewrite normr_gt0// fine_eq0// ?lt_eqF// fin_num_measure.
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm ?fine_le0// ltr0_norm//.
    by rewrite fine_lt0// nuD0 andbT ltNye_eq fin_num_measure.
  rewrite ltrN2; apply/negP; rewrite -leNgt fine_le ?fin_num_measure//.
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
    have := @npeseries_le0 _ (fun n => maxe (z_ (v n) * 2^-1%:E) (- 1%E)) xpredT 0.
    by rewrite limoo// leNgt => /(_ (fun n _ _ => max_le0 n))/negP; exact.
move/fine_cvgP => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (z_ (v n) * 2^-1%:E) (- 1%E))) n @[n --> \oo]).
  apply/cvg_ex; exists l; move: cvgl.
  rewrite (_ : _ \o _ = (fun n =>
    \sum_(0 <= k < n) fine (maxe (z_ (v k) * 2^-1%:E)%E (- 1%E)%E))%R) //.
  apply/funext => n/=; rewrite sum_fine// => m _.
  rewrite le0_fin_numE; last by rewrite lt_max ltNyr orbT.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/cvg_series_cvg_0 => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite (_ : _ \o _ = (fun n => z_ (v n) * 2^-1%:E) \* cst 2%:E).
  by apply/funext => n/=; rewrite -muleA -EFinM mulVf ?mule1.
rewrite (_ : 0 = 0 * 2%:E); first by rewrite mul0e.
apply: cvgeM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/fine_cvgP; split.
  move/cvgrPdist_lt : maxe_cvg_0 => /(_ _ ltr01)[M _ hM]; near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN ltNge => maxe_lt1; rewrite fin_numE; apply/andP; split.
    by apply: contra maxe_lt1 => /eqP ->; rewrite max_r ?leNye//= normrN1 lexx.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/cvgrPdist_lt => _ /posnumP[e].
have : (0 < Num.min e%:num 1)%R by rewrite lt_min// ltr01 andbT.
move/cvgrPdist_lt : maxe_cvg_0 => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN /maxe/=; case: ifPn => [_|].
  by rewrite normrN normr1 lt_min ltxx andbF.
by rewrite -leNgt => ? /lt_le_trans; apply; rewrite ge_min lexx.
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
  + rewrite (charge_partition _ _ mP2 mN2)//; first exact: measurableI.
    by rewrite (positive_negative0 psP1 nsN2 mS) adde0.
  + rewrite [RHS](charge_partition _ _ mP1 mN1)//; first exact: measurableI.
    by rewrite (positive_negative0 psP2 nsN1 mS) adde0 setIAC.
- transitivity (nu (S `&` N1 `&` N2)).
  + rewrite (charge_partition nu _ mP2 mN2)//; first exact: measurableI.
    have := positive_negative0 psP2 nsN1 mS.
    by rewrite setIAC => ->; rewrite add0e.
  + rewrite [RHS](charge_partition nu _ mP1 mN1)//; first exact: measurableI.
    by rewrite (setIAC _ _ P1) (positive_negative0 psP1 nsN2 mS) add0e setIAC.
Qed.

End hahn_decomposition_theorem.

Section jordan_decomposition.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).

Let mP : measurable P. Proof. by have [[mP _] _ _ _] := nuPN. Qed.

Let mN : measurable N. Proof. by have [_ [mN _] _ _] := nuPN. Qed.

Local Definition cjordan_pos : {charge set T -> \bar R} := crestr0 nu mP.

Lemma cjordan_posE A : cjordan_pos A = crestr0 nu mP A.
Proof. by []. Qed.

Let positive_set_cjordan_pos E : 0 <= cjordan_pos E.
Proof.
have [posP _ _ _] := nuPN.
rewrite cjordan_posE /crestr0/=; case: ifPn => // /[1!inE] mE.
by apply posP; [apply: measurableI|apply: subIsetr].
Qed.

Definition jordan_pos := measure_of_charge _ positive_set_cjordan_pos.

Lemma jordan_posE A : jordan_pos A = cjordan_pos A.
Proof. by []. Qed.

HB.instance Definition _ := Measure.on jordan_pos.

Let finite_jordan_pos : fin_num_fun jordan_pos.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_pos finite_jordan_pos.

Local Definition cjordan_neg : {charge set T -> \bar R} :=
  cscale (-1) (crestr0 nu mN).

Lemma cjordan_negE A : cjordan_neg A = - crestr0 nu mN A.
Proof. by rewrite /= cscaleN1. Qed.

Let positive_set_cjordan_neg E : 0 <= cjordan_neg E.
Proof.
rewrite cjordan_negE /crestr0/=; case: ifPn; rewrite ?oppe0//.
move=> /[!inE] mE; rewrite /crestr leeNr oppe0.
by move: nuPN => [_ [_ +] _ _] => -> //; exact: measurableI.
Qed.

Definition jordan_neg := measure_of_charge _ positive_set_cjordan_neg.

Lemma jordan_negE A : jordan_neg A = cjordan_neg A.
Proof. by []. Qed.

HB.instance Definition _ := Measure.on jordan_neg.

Let finite_jordan_neg : fin_num_fun jordan_neg.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_neg finite_jordan_neg.

Lemma jordan_decomp (A : set T) : measurable A ->
  nu A = cadd jordan_pos (cscale (-1) jordan_neg) A.
Proof.
move=> mA.
rewrite /cadd cjordan_posE/= cscaleN1 cjordan_negE oppeK.
rewrite /crestr0 mem_set// -[in LHS](setIT A).
case: nuPN => _ _ <- PN0; rewrite setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setIACA PN0 setI0.
Qed.

Lemma jordan_pos_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_pos `<< mu.
Proof.
move=> /null_content_dominatesP nu_mu.
apply/null_content_dominatesP => A mA muA0.
have := nu_mu A mA muA0.
rewrite jordan_posE// cjordan_posE /crestr0 mem_set// /crestr/=.
have mAP : measurable (A `&` P) by exact: measurableI.
suff : mu (A `&` P) = 0 by move/(nu_mu _ mAP) => ->.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

Lemma jordan_neg_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_neg `<< mu.
Proof.
move=> /null_content_dominatesP nu_mu.
apply/null_content_dominatesP => A mA muA0.
have := nu_mu A mA muA0.
rewrite jordan_negE// cjordan_negE /crestr0 mem_set// /crestr/=.
have mAN : measurable (A `&` N) by exact: measurableI.
suff : mu (A `&` N) = 0 by move=> /(nu_mu _ mAN) ->; rewrite oppe0.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

End jordan_decomposition.

Section charge_variation.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).
Local Open Scope ereal_scope.

Definition charge_variation := jordan_pos nuPN \+ jordan_neg nuPN.

End charge_variation.

Section charge_variation.
Context {R : realType} d (T : measurableType d).
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).

Local Notation mu := (charge_variation nuPN).

Let mu0 : mu set0 = 0. Proof. by rewrite /mu !charge0 add0e. Qed.

Let mu_ge0 x : (0 <= mu x)%E. Proof. by rewrite adde_ge0. Qed.

Let mu_sigma_additive : semi_sigma_additive mu.
Proof.
move=> F mF tF mUF; under eq_fun do rewrite big_split; apply: cvgeD => //=.
- by rewrite ge0_adde_def// inE.
- exact: measure_semi_sigma_additive.
- exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ mu
  mu0 mu_ge0 mu_sigma_additive.

Let mu_fin A : d.-measurable A -> mu A \is a fin_num.
Proof. by move=> mA; rewrite /mu fin_numD !fin_num_measure. Qed.

HB.instance Definition _ := isCharge.Build _ _ _ mu
  mu0 mu_fin mu_sigma_additive.

End charge_variation.

Definition charge_dominates d (T : measurableType d) {R : realType}
    (mu : {content set T -> \bar R}) (nu : {charge set T -> \bar R})
    (P N : set T) (nuPN : hahn_decomposition nu P N) :=
  content_dominates mu (charge_variation nuPN).

Section charge_variation_continuous.
Local Open Scope ereal_scope.
Context d (T : measurableType d) {R : realType}.
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).

Lemma abse_charge_variation A :
  measurable A -> `|nu A| <= charge_variation nuPN A.
Proof.
move=> mA.
rewrite (jordan_decomp nuPN mA) /cadd/= cscaleN1 /charge_variation.
by rewrite (le_trans (lee_abs_sub _ _))// !gee0_abs.
Qed.

Lemma __deprecated__dominates_charge_variation (mu : {measure set T -> \bar R}) :
  nu `<< mu -> charge_variation nuPN `<< mu.
Proof.
move=> /[dup]numu /null_content_dominatesP nu0mu0.
apply/null_content_dominatesP => A mA muA0; rewrite /charge_variation/=.
have /null_content_dominatesP ->// := jordan_pos_dominates nuPN numu.
rewrite add0e.
by have /null_content_dominatesP -> := jordan_neg_dominates nuPN numu.
Qed.

Lemma null_charge_dominatesP (mu : {measure set T -> \bar R}) :
  nu `<< mu <-> charge_dominates mu nuPN.
Proof.
split => [|numu].
- move=> /[dup]numu /null_content_dominatesP nu0mu0.
  move=> A mA muA0; rewrite /charge_variation/=.
  have /null_content_dominatesP ->// := jordan_pos_dominates nuPN numu.
  rewrite add0e.
  by have /null_content_dominatesP -> := jordan_neg_dominates nuPN numu.
- apply/null_content_dominatesP => A mA /numu => /(_ mA) nuA0.
  apply/eqP; rewrite -abse_eq0 eq_le abse_ge0 andbT.
  by rewrite -nuA0 abse_charge_variation.
Qed.

Lemma content_charge_dominatesP (mu : {measure set T -> \bar R}) :
  content_dominates mu nu <-> charge_dominates mu nuPN.
Proof.
split.
- by move/null_content_dominatesP/null_charge_dominatesP.
- by move/null_charge_dominatesP/null_content_dominatesP.
Qed.

Lemma charge_variation_continuous (mu : {measure set T -> \bar R}) :
  nu `<< mu -> forall e : R, (0 < e)%R ->
  exists d : R, (0 < d)%R /\
  forall A, measurable A -> mu A < d%:E -> charge_variation nuPN A < e%:E.
Proof.
move=> /[dup]nudommu /null_content_dominatesP numu.
apply/not_forallP => -[e] /not_implyP[e0] /forallNP H.
have {H} : forall n, exists A,
    [/\ measurable A, mu A < (2 ^- n.+1)%:E & charge_variation nuPN A >= e%:E].
  move=> n; have /not_andP[|] := H (2 ^- n.+1); first by rewrite invr_gt0.
  move=> /existsNP[A] /not_implyP[mA] /not_implyP[Aab] /negP.
  by rewrite -leNgt => eint; exists A.
move=> /choice[F /= H].
have mF i : measurable (F i) by have [] := H i.
have : mu (lim_sup_set F) = 0.
  apply: lim_sup_set_cvg0 => //.
  have h : \sum_(0 <= n < k) (1 / 2 ^+ n.+1)%:E @[k --> \oo] --> (1%E : \bar R).
    apply/fine_cvgP; split.
      apply: nearW => /= n; rewrite sum_fin_num//.
      by apply/allP => /= r /mapP[/= k _] ->.
    have := @cvg_geometric_series_half R 1 0; rewrite {1}/series/= expr0 divr1.
    under [in X in _ -> X]eq_fun do rewrite sumEFin.
    by under eq_fun do under eq_bigr do rewrite addn1 natrX.
  apply: (@le_lt_trans _ _ (\sum_(0 <= n <oo) (1 / (2 ^ n.+1))%:E)).
    apply: lee_lim.
    - exact: is_cvg_ereal_nneg_natsum_cond.
    - by apply/cvg_ex; exists 1.
    - apply: nearW => /= n; apply: lee_sum => i _.
      by have [_ /ltW + _] := H i; rewrite div1r.
  by move/cvg_lim : h => ->//; rewrite ltry.
have : measurable (lim_sup_set F).
  by apply: bigcap_measurable => // k _; exact: bigcup_measurable.
move/null_charge_dominatesP : nudommu => /[apply] /[apply].
apply/eqP; rewrite neq_lt// ltNge measure_ge0//=.
suff : charge_variation nuPN (lim_sup_set F) >= e%:E by exact: lt_le_trans.
have echarge n : e%:E <= charge_variation nuPN (\bigcup_(j >= n) F j).
  have [_ _ /le_trans] := H n; apply.
  rewrite le_measure// ?inE//; first exact: bigcup_measurable.
  by apply: bigcup_sup => /=.
have /(_ _ _)/cvg_lim <-// := lim_sup_set_cvg (charge_variation nuPN) F.
  by rewrite -ge0_fin_numE// fin_num_measure//; exact: bigcup_measurable.
apply: lime_ge; last by apply: nearW => k; exact: echarge.
apply: ereal_nonincreasing_is_cvgn => a b ab.
rewrite le_measure ?inE//; [exact: bigcup_measurable|exact: bigcup_measurable|].
by apply: bigcup_subset => n/=; exact: leq_trans.
Qed.

End charge_variation_continuous.
#[deprecated(since="mathcomp-analysis 1.15.0", note="use `charge_null_dominatesP` instead")]
Notation dominates_charge_variation := __deprecated__dominates_charge_variation (only parsing).
