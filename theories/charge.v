(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets cardinality.
From mathcomp Require Import functions fsbigop set_interval.
From HB Require Import structures.
From mathcomp Require Import reals interval_inference ereal topology numfun.
From mathcomp Require Import normedtype sequences esum measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

(**md**************************************************************************)
(* # Charges                                                                  *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file contains a formalization of charges (a.k.a. signed measures) and *)
(* their theory (Hahn decomposition theorem, Radon-Nikodym derivative, etc.). *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - Y. Ishiguro, R. Affeldt. The Radon-Nikodym Theorem and the Lebesgue-     *)
(*   Stieltjes measure in Coq. Computer Software 41(2) 2024                   *)
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
(*          charge_add n1 n2 == the charge corresponding to the sum of        *)
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
(*              induced intf == charge induced by a function f : T -> \bar R  *)
(*                              R has type realType; T is a measurableType.   *)
(*                              intf is a proof that f is integrable over     *)
(*                              [set: T]                                      *)
(*              'd nu '/d mu == Radon-Nikodym derivative of nu w.r.t. mu      *)
(*                              (the scope is charge_scope)                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'additive_charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'additive_charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "'d nu '/d mu" (at level 10, nu, mu at next level,
  format "''d'  nu  ''/d'  mu").
Reserved Notation "nu .-negative_set" (at level 2, format "nu .-negative_set").
Reserved Notation "nu .-positive_set" (at level 2, format "nu .-positive_set").

Declare Scope charge_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

HB.mixin Record isAdditiveCharge d (T : semiRingOfSetsType d) (R : numFieldType)
  (mu : set T -> \bar R) := { charge_semi_additive : measure.semi_additive mu }.

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
  mu of isCharge d T R mu.

Let finite : fin_num_fun mu. Proof. exact: charge_finite. Qed.

HB.instance Definition _ := isFinite.Build d T R mu finite.

Let semi_additive : measure.semi_additive mu.
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
  (nu : set T -> \bar R) of (forall E, 0 <= nu E) := nu.

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
- by rewrite ltey_eq fin_num_measure//; exact:measurableI.
- by rewrite ltNye_eq fin_num_measure//; exact:measurableI.
Qed.

End charge_lemmas_realFieldType.

Definition crestr d (T : semiRingOfSetsType d) (R : numDomainType) (D : set T)
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

HB.instance Definition _ := isFinite.Build _ _ _
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
  exact: charge_semi_sigma_additive.
by apply/funext => n; apply: eq_bigr => i _; rewrite mem_set.
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
move=> F mF tF mUF; rewrite [X in X @ _ --> _](_ : _ = cst 0); first exact: cvg_cst.
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

HB.instance Definition _ := isFinite.Build _ _ _
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
  cscale0 cscale_finite_measure_function cscale_sigma_additive.

End charge_scale.

Lemma dominates_cscalel d (T : measurableType d) (R : realType)
  (mu : set T -> \bar R)
  (nu : {charge set T -> \bar R})
  (c : R) : nu `<< mu -> cscale c nu `<< mu.
Proof. by move=> numu E mE /numu; rewrite /cscale => ->//; rewrite mule0. Qed.

Lemma dominates_cscaler d (T : measurableType d) (R : realType)
  (nu : {charge set T -> \bar R})
  (mu : set T -> \bar R)
  (c : R) : c != 0%R -> mu `<< nu -> mu `<< cscale c nu.
Proof.
move=> /negbTE c0 munu E mE /eqP; rewrite /cscale mule_eq0 eqe c0/=.
by move=> /eqP/munu; exact.
Qed.

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
  (* TODO: IIRC explicit arguments were added to please Coq 8.14, rm if not needed anymore *)
  apply: (@cvgeD _ _ _ R (fun x => \sum_(0 <= i < x) (n1 (F i)))
                         (fun x => \sum_(0 <= i < x) (n2 (F i)))
                         (n1 (\bigcup_n F n)) (n2 (\bigcup_n F n))).
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
by move=> nu0mu nu1mu A mA A0; rewrite /cadd nu0mu// nu1mu// adde0.
Qed.

Section pushforward_charge.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (f : T1 -> T2).
Variables (R : realFieldType) (nu : {charge set T1 -> \bar R}).

Hypothesis mf : measurable_fun setT f.

Let pushforward0 : pushforward nu mf set0 = 0.
Proof. by rewrite /pushforward preimage_set0 charge0. Qed.

Let pushforward_finite A : measurable A -> pushforward nu mf A \is a fin_num.
Proof.
move=> mA; apply: fin_num_measure.
by rewrite -[X in measurable X]setTI; exact: mf.
Qed.

Let pushforward_sigma_additive : semi_sigma_additive (pushforward nu mf).
Proof.
move=> F mF tF mUF; rewrite /pushforward preimage_bigcup.
apply: charge_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: mf.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mf.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ (pushforward nu mf)
  pushforward0 pushforward_finite pushforward_sigma_additive.

End pushforward_charge.

HB.builders Context d (T : measurableType d) (R : realType)
  (mu : set T -> \bar R) of Measure_isFinite d T R mu.

Let mu0 : mu set0 = 0.
Proof. by apply: measure0. Qed.

HB.instance Definition _ := isCharge.Build _ _ _
  mu (measure0 mu) fin_num_measure measure_semi_sigma_additive.

HB.end.

Section dominates_pushforward.

Lemma dominates_pushforward d d' (T : measurableType d) (T' : measurableType d')
  (R : realType) (mu : {measure set T -> \bar R})
  (nu : {charge set T -> \bar R}) (f : T -> T') (mf : measurable_fun setT f) :
  nu `<< mu -> pushforward nu mf `<< pushforward mu mf.
Proof.
by move=> numu A mA; apply: numu; rewrite -[X in measurable X]setTI; exact: mf.
Qed.

End dominates_pushforward.

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
  rewrite -(@fineK _ (d_ A)); last by rewrite gt0_fin_numE// ltey.
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
rewrite -(mule0 2%:E); apply: cvgeMl => //.
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
  apply: dependent_choice_Type => -[[[A' ?] U] [/= mA' A'D]].
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
  rewrite [X in X @ _ --> _](_ : _ = (fun n => (fine (nu (A_ (v n))))%:E)); last first.
    by apply/funext => n/=; rewrite fineK// fin_num_measure.
  apply: continuous_cvg => //; apply: cvg_series_cvg_0.
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) nu (A_ (v i)))); last first.
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
  rewrite -[in leRHS](@setDUK _ Aoo D); last first.
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
  have /le_ereal_sup := EH n.+1; rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [mA' A'D ?]].
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
  rewrite -(@fineK _ (s_ U)); last by rewrite lt0_fin_numE// ltNye.
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
  apply: dependent_choice_Type => -[[[A s] U] [/= s_le0' nsA]].
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
  rewrite sub0r normrN /= ler0_norm ?fine_le0// ltr0_norm//; last first.
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
  rewrite le0_fin_numE; first by rewrite lt_max ltNyr orbT.
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
have : (0 < minr e%:num 1)%R by rewrite lt_min// ltr01 andbT.
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
Proof. by rewrite /= /cscale/= EFinN mulN1e. Qed.

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
rewrite /cadd cjordan_posE /= /cscale EFinN mulN1e cjordan_negE oppeK.
rewrite /crestr0 mem_set// -[in LHS](setIT A).
case: nuPN => _ _ <- PN0; rewrite setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setIACA PN0 setI0.
Qed.

Lemma jordan_pos_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_pos `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
rewrite jordan_posE// cjordan_posE /crestr0 mem_set// /crestr/=.
have mAP : measurable (A `&` P) by exact: measurableI.
suff : mu (A `&` P) = 0 by move/(nu_mu _ mAP) => ->.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

Lemma jordan_neg_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_neg `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
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

Lemma abse_charge_variation d (T : measurableType d) (R : realType)
    (nu : {charge set T -> \bar R}) P N (PN : hahn_decomposition nu P N) A :
  measurable A -> `|nu A| <= charge_variation PN A.
Proof.
move=> mA.
rewrite (jordan_decomp PN mA) /cadd/= /cscale/= mulN1e /charge_variation.
by rewrite (le_trans (lee_abs_sub _ _))// !gee0_abs.
Qed.

Section charge_variation_continuous.
Local Open Scope ereal_scope.
Context {R : realType} d (T : measurableType d).
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).

Lemma dominates_charge_variation (mu : {measure set T -> \bar R}) :
  nu `<< mu -> charge_variation nuPN `<< mu.
Proof.
move=> numu A mA muA0.
rewrite /charge_variation/= (jordan_pos_dominates nuPN numu)// add0e.
by rewrite (jordan_neg_dominates nuPN numu).
Qed.

Lemma charge_variation_continuous (mu : {measure set T -> \bar R}) :
  nu `<< mu -> forall e : R, (0 < e)%R ->
  exists d : R, (0 < d)%R /\
  forall A, measurable A -> mu A < d%:E -> charge_variation nuPN A < e%:E.
Proof.
move=> numu; apply/not_forallP => -[e] /not_implyP[e0] /forallNP H.
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
move=> /(dominates_charge_variation numu) /[apply].
apply/eqP; rewrite neq_lt// ltNge measure_ge0//=.
suff : charge_variation nuPN (lim_sup_set F) >= e%:E by exact: lt_le_trans.
have echarge n : e%:E <= charge_variation nuPN (\bigcup_(j >= n) F j).
  have [_ _ /le_trans] := H n; apply.
  rewrite le_measure// ?inE//; first exact: bigcup_measurable.
  by apply: bigcup_sup => /=.
have /(_ _ _)/cvg_lim <-// := lim_sup_set_cvg (charge_variation nuPN) F.
  apply: lime_ge.
    apply: ereal_nonincreasing_is_cvgn => a b ab.
    rewrite le_measure ?inE//; [exact: bigcup_measurable|
                                exact: bigcup_measurable|].
    by apply: bigcup_subset => n/=; exact: leq_trans.
  by apply: nearW => k; exact: echarge.
by rewrite -ge0_fin_numE// fin_num_measure//; exact: bigcup_measurable.
Qed.

End charge_variation_continuous.

Definition induced d (T : measurableType d) {R : realType}
    (mu : {measure set T -> \bar R}) (f : T -> \bar R)
    (intf : mu.-integrable [set: T] f) :=
  fun A => (\int[mu]_(t in A) f t)%E.

Section induced_charge.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Lemma semi_sigma_additive_nng_induced (f : T -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x) ->
  semi_sigma_additive (fun A => \int[mu]_(t in A) f t).
Proof.
move=> mf f0 /= F mF tF mUF; rewrite ge0_integral_bigcup//=; last first.
  exact: measurable_funTS.
by apply: is_cvg_ereal_nneg_natsum_cond => // n _ _; exact: integral_ge0.
Qed.

Variable f : T -> \bar R.
Hypothesis intf : mu.-integrable setT f.

Local Notation nu := (induced intf).

Let nu0 : nu set0 = 0. Proof. by rewrite /nu integral_set0. Qed.

Let finnu A : measurable A -> nu A \is a fin_num.
Proof.
by move=> mA; apply: integral_fune_fin_num => //=; exact: integrableS intf.
Qed.

Let snu : semi_sigma_additive nu.
Proof.
move=> /= F mF tF mUF; set SF := (f in f n @[n --> \oo] --> _).
rewrite (_ : SF = fun n =>
    \sum_(0 <= i < n) (\int[mu]_(x in F i) f^\+ x) -
    \sum_(0 <= i < n) (\int[mu]_(x in F i) f^\- x)); last first.
  apply/funext => n; rewrite /SF; under eq_bigr do rewrite /nu integralE.
  rewrite big_split/= sumeN//= => i j _ _.
  rewrite fin_num_adde_defl// integral_fune_fin_num//= integrable_funeneg//=.
  exact: integrableS intf.
rewrite /nu integralE; apply: cvgeD.
- rewrite fin_num_adde_defr// integral_fune_fin_num//=.
  by apply: integrable_funepos => //=; exact: integrableS intf.
- apply/semi_sigma_additive_nng_induced => //.
  by apply: measurable_funepos; exact: (measurable_int mu).
- apply/cvgeN/semi_sigma_additive_nng_induced => //=.
  by apply: measurable_funeneg; exact: (measurable_int mu).
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ nu nu0 finnu snu.

End induced_charge.

Section dominates_induced.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Variable f : T -> \bar R.
Hypothesis intf : mu.-integrable setT f.

Let intnf : mu.-integrable [set: T] (abse \o f).
Proof. exact: integrable_abse. Qed.

Lemma dominates_induced : induced intnf `<< mu.
Proof.
move=> /= A mA muA.
rewrite /induced; apply/eqP; rewrite -abse_eq0 eq_le abse_ge0 andbT.
rewrite (le_trans (le_abse_integral _ _ _))//=.
  by case/integrableP : intnf => /= + _; exact: measurable_funTS.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
under eq_integral do rewrite abse_id.
by apply: null_set_integral => //=; exact: integrableS intnf.
Qed.

End dominates_induced.

Section integral_normr_continuous.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Variable f : T -> R.
Hypothesis intf : mu.-integrable setT (EFin \o f).

Let intnf : mu.-integrable setT (abse \o EFin \o f).
Proof. exact: integrable_abse. Qed.

Lemma integral_normr_continuous (e : R) : (0 < e)%R ->
  exists d : R, (0 < d)%R /\
  forall A, measurable A -> mu A < d%:E -> (\int[mu]_(x in A) `|f x| < e)%R.
Proof.
move=> e0; have [P [N pn]] := Hahn_decomposition (induced intnf).
have [r [r0 re]] := charge_variation_continuous pn (dominates_induced intf) e0.
exists r; split => //= A mA Ad.
have {re} := re _ mA Ad.
rewrite -lte_fin; apply: le_lt_trans.
rewrite /Rintegral fineK; last first.
  have : mu.-integrable A (abse \o EFin \o f) by exact: integrableS intnf.
  move/integrableP : intf => -[_ intfoo _].
  rewrite ge0_fin_numE//=; last exact: integral_ge0.
  apply: le_lt_trans intfoo.
  apply: ge0_subset_integral => //=.
  apply: measurableT_comp => //.
  by case/integrableP : intnf => /= /measurable_EFinP.
rewrite -[leLHS](gee0_abs)//; last exact: integral_ge0.
exact: (le_trans _ (abse_charge_variation _ _)).
Qed.

End integral_normr_continuous.

(* We put definitions and lemmas used only in the proof of the Radon-Nikodym
   theorem as Definition's and Lemma's in the following modules. See
   https://staff.aist.go.jp/reynald.affeldt/documents/measure-ppl2023.pdf
   for an overview. *)
Module approxRN.
Section approxRN.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {measure set T -> \bar R}.

Definition approxRN := [set g : T -> \bar R | [/\
  forall x, 0 <= g x, mu.-integrable [set: T] g &
  forall E, measurable E -> \int[mu]_(x in E) g x <= nu E] ].

Let approxRN_neq0 : approxRN !=set0.
Proof.
exists (cst 0); split => //; first exact: integrable0.
by move=> E mE; rewrite integral0 measure_ge0.
Qed.

Definition int_approxRN := [set \int[mu]_x g x | g in approxRN].

Definition sup_int_approxRN := ereal_sup int_approxRN.

Lemma sup_int_approxRN_ge0 : 0 <= sup_int_approxRN.
Proof.
rewrite -(ereal_sup1 0) le_ereal_sup// sub1set inE.
exists (fun=> 0); last exact: integral0.
by split => //; [exact: integrable0|move=> E; rewrite integral0].
Qed.

End approxRN.
End approxRN.

Module approxRN_seq.
Section approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let approxRN := approxRN mu nu.
Let int_approxRN := int_approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Let int_approxRN_ub : exists M, forall x, x \in int_approxRN -> x <= M%:E.
Proof.
exists (fine (nu setT)) => x /[1!inE] -[g [g0 g1 g2] <-{x}].
by rewrite fineK ?fin_num_measure// (le_trans (g2 setT _))// inE.
Qed.

Lemma sup_int_approxRN_lty : M < +oo.
Proof.
rewrite /sup_int_approxRN; have [m hm] := int_approxRN_ub.
rewrite (@le_lt_trans _ _ m%:E)// ?ltey// ub_ereal_sup// => x IGx.
by apply: hm; rewrite inE.
Qed.

Lemma sup_int_approxRN_fin_num : M \is a fin_num.
Proof.
rewrite ge0_fin_numE; first exact: sup_int_approxRN_lty.
exact: sup_int_approxRN_ge0.
Qed.

Lemma approxRN_seq_ex : { g : (T -> \bar R)^nat |
  forall k, g k \in approxRN /\ \int[mu]_x g k x > M - k.+1%:R^-1%:E }.
Proof.
pose P m g := g \in approxRN /\ M - m.+1%:R^-1%:E < \int[mu]_x g x.
suff : { g : (T -> \bar R) ^nat & forall m, P m (g m)} by case => g ?; exists g.
apply: (@choice _ _ P) => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ int_approxRN) : (0 < m.+1%:R^-1 :> R)%R.
  by rewrite invr_gt0.
move/(_ sup_int_approxRN_fin_num) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition approxRN_seq : (T -> \bar R)^nat := sval approxRN_seq_ex.

Let g_ := approxRN_seq.

Lemma approxRN_seq_prop : forall m,
  g_ m \in approxRN /\ \int[mu]_x (g_ m x) > M - m.+1%:R^-1%:E.
Proof. exact: (projT2 approxRN_seq_ex). Qed.

Lemma approxRN_seq_ge0 x n : 0 <= g_ n x.
Proof. by have [+ _]:= approxRN_seq_prop n; rewrite inE /= => -[]. Qed.

Lemma measurable_approxRN_seq n : measurable_fun setT (g_ n).
Proof. by have := approxRN_seq_prop n; rewrite inE =>-[[_ /integrableP[]]]. Qed.

Definition max_approxRN_seq n x := \big[maxe/-oo]_(j < n.+1) g_ j x.

Let F_ := max_approxRN_seq.

Lemma measurable_max_approxRN_seq n : measurable_fun [set: T] (F_ n).
Proof.
elim: n => [|n ih].
  rewrite /F_ /max_approxRN_seq.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := approxRN_seq_prop 0%N.
  by rewrite inE /= => -[]// _ _ _; exact: measurable_approxRN_seq.
rewrite /F_ /max_approxRN_seq => m.
under eq_fun do rewrite big_ord_recr.
by apply: measurable_maxe => //; exact: measurable_approxRN_seq.
Qed.

Lemma max_approxRN_seq_ge0 n x : 0 <= F_ n x.
Proof.
by apply/bigmax_geP; right => /=; exists ord0; [|exact: approxRN_seq_ge0].
Qed.

Lemma max_approxRN_seq_ge n x : F_ n x >= g_ n x.
Proof. by apply/bigmax_geP; right => /=; exists ord_max. Qed.

Lemma max_approxRN_seq_nd x : nondecreasing_seq (F_ ^~ x).
Proof. by move=> a b ab; rewrite (le_bigmax_ord xpredT (g_ ^~ x)). Qed.

Lemma is_cvg_max_approxRN_seq n : cvg (F_ ^~ n @ \oo).
Proof. by apply: ereal_nondecreasing_is_cvgn; exact: max_approxRN_seq_nd. Qed.

Lemma is_cvg_int_max_approxRN_seq A :
  measurable A -> cvg ((fun n => \int[mu]_(x in A) F_ n x) @ \oo).
Proof.
move=> mA; apply: ereal_nondecreasing_is_cvgn => a b ab.
apply: ge0_le_integral => //.
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by apply: measurable_funS (measurable_max_approxRN_seq a).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- exact: measurable_funS (measurable_max_approxRN_seq b).
- by move=> x _; exact: max_approxRN_seq_nd.
Qed.

Definition is_max_approxRN m j :=
  [set x | F_ m x = g_ j x /\ forall k, (k < j)%N -> g_ k x < g_ j x].

Let E := is_max_approxRN.

Lemma is_max_approxRNE m j : E m j = [set x| F_ m x = g_ j x] `&`
    [set x |forall k, (k < j)%nat -> g_ k x < g_ j x].
Proof. by apply/seteqP; split. Qed.

Lemma trivIset_is_max_approxRN n : trivIset [set: nat] (E n).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Lemma bigsetU_is_max_approxRN m : \big[setU/set0]_(j < m.+1) E m j = [set: T].
Proof.
apply/seteqP; split => // x _; rewrite -bigcup_mkord.
pose j := [arg max_(j > @ord0 m) g_ j x]%O.
have j0_proof : exists k, (k < m.+1)%N && (g_ k x == g_ j x).
  by exists j => //; rewrite eqxx andbT.
pose j0 := ex_minn j0_proof.
have j0m : (j0 < m.+1)%N by rewrite /j0; case: ex_minnP => // ? /andP[].
have j0max k : (k < j0)%N -> g_ k x < g_ j0 x.
  rewrite /j0; case: ex_minnP => //= j' /andP[j'm j'j] h kj'.
  rewrite lt_neqAle; apply/andP; split; last first.
    rewrite (eqP j'j) /j; case: arg_maxP => //= i _.
    by move/(_ (Ordinal (ltn_trans kj' j'm))); exact.
  apply/negP => /eqP gkj'.
  have := h k; rewrite -(eqP j'j) -gkj' eqxx andbT (ltn_trans kj' j'm).
  by move=> /(_ erefl); rewrite leqNgt kj'.
exists j0 => //; split.
  rewrite /F_ /max_approxRN_seq (bigmax_eq_arg _ ord0)//; last first.
    by move=> ? _; rewrite leNye.
  rewrite /j0/=; case: ex_minnP => //= j' /andP[j'm /eqP].
  by rewrite /g_ => -> h.
by move=> k kj; exact: j0max.
Qed.

Lemma measurable_is_max_approxRN m j : measurable (E m j).
Proof.
rewrite is_max_approxRNE; apply: measurableI => /=.
  rewrite -[X in measurable X]setTI.
  by apply: emeasurable_fun_eq => //; [exact: measurable_max_approxRN_seq|
                                       exact: measurable_approxRN_seq].
rewrite [T in measurable T](_ : _ =
  \bigcap_(k in `I_j) [set x | g_ k x < g_ j x])//.
apply: bigcap_measurableType => k _.
by rewrite -[X in measurable X]setTI; apply: emeasurable_fun_lt => //;
  exact: measurable_approxRN_seq.
Qed.

End approxRN_seq.
End approxRN_seq.

Module lim_max_approxRN_seq.
Section lim_max_approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import approxRN_seq.

Let g := approxRN_seq mu nu.
Let F := max_approxRN_seq mu nu.

Definition fRN := fun x => lim (F ^~ x @ \oo).

Lemma measurable_fun_fRN : measurable_fun [set: T] fRN.
Proof.
rewrite (_ : fRN = fun x => limn_esup (F ^~ x)).
  apply: measurable_fun_limn_esup => // n.
  exact: measurable_max_approxRN_seq.
apply/funext=> n; rewrite is_cvg_limn_esupE//.
exact: is_cvg_max_approxRN_seq.
Qed.

Lemma fRN_ge0 x : 0 <= fRN x.
Proof.
apply: lime_ge => //; first exact: is_cvg_max_approxRN_seq.
by apply: nearW => ?; exact: max_approxRN_seq_ge0.
Qed.

Let int_fRN_lim A : measurable A ->
  \int[mu]_(x in A) fRN x = lim (\int[mu]_(x in A) F n x @[n --> \oo]).
Proof.
move=> mA; rewrite monotone_convergence// => n.
- exact: measurable_funS (measurable_max_approxRN_seq mu nu n).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by move=> ?; exact: max_approxRN_seq_nd.
Qed.

Let E m j := is_max_approxRN mu nu m j.

Let int_F_nu m A (mA : measurable A) : \int[mu]_(x in A) F m x <= nu A.
Proof.
rewrite [leLHS](_ : _ =
    \sum_(j < m.+1) \int[mu]_(x in (A `&` E m j)) F m x); last first.
  rewrite -[in LHS](setIT A) -(bigsetU_is_max_approxRN mu nu m) big_distrr/=.
  rewrite -(@big_mkord _ _ _ m.+1 xpredT (fun i => A `&` is_max_approxRN mu nu m i)).
  rewrite ge0_integral_bigsetU ?big_mkord//.
  - by move=> n; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - exact: iota_uniq.
  - apply: trivIset_setIl; apply: (@sub_trivIset _ _ _ setT (E m)) => //.
    exact: trivIset_is_max_approxRN.
  - by apply: measurable_funTS => //; exact: measurable_max_approxRN_seq.
  - by move=> ? ?; exact: max_approxRN_seq_ge0.
rewrite [leLHS](_ : _ =
    \sum_(j < m.+1) (\int[mu]_(x in (A `&` (E m j))) g j x)); last first.
  apply: eq_bigr => i _; apply:eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite /F Fmgi lexx.
rewrite [leRHS](_ : _ = \sum_(j < m.+1) (nu (A `&` E m j))); last first.
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => A `&` E m i))//.
  - by rewrite -big_distrr/= bigsetU_is_max_approxRN// setIT.
  - by move=> k; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - by apply: trivIset_setIl => //; exact: trivIset_is_max_approxRN.
  - apply: bigsetU_measurable => /= i _; apply: measurableI => //.
    exact: measurable_is_max_approxRN.
apply: lee_sum => //= i _.
have [+ _] := approxRN_seq_prop mu nu i.
rewrite inE /G/= => -[_ _]; apply.
by apply: measurableI => //; exact: measurable_is_max_approxRN.
Qed.

Let F_G m : F m \in G.
Proof.
rewrite inE /G/=; split.
- by move=> ?; exact: max_approxRN_seq_ge0.
- apply/integrableP; split; first exact: measurable_max_approxRN_seq.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; last exact: max_approxRN_seq_ge0; over.
  have /le_lt_trans := int_F_nu m measurableT; apply.
  by apply: fin_num_fun_lty; exact: fin_num_measure.
- by move=> A; exact: int_F_nu.
Qed.

Let M_g_F m : M - m.+1%:R^-1%:E < \int[mu]_x g m x /\
              \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := approxRN_seq_prop mu nu m.
apply/andP; split; last first.
  by apply: ereal_sup_ubound; exists (F m)  => //; have := F_G m; rewrite inE.
apply: ge0_le_integral => //.
- by move=> x _; exact: approxRN_seq_ge0.
- exact: measurable_approxRN_seq.
- by move=> ? *; exact: max_approxRN_seq_ge0.
- exact: measurable_max_approxRN_seq.
- by move=> ? _; exact: max_approxRN_seq_ge.
Qed.

Lemma int_fRN_lty : \int[mu]_x `|fRN x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last exact: sup_int_approxRN_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; last exact: fRN_ge0; over.
rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; have [_ /andP[_ ]] := M_g_F n.
Qed.

Lemma int_fRN_ub A : measurable A -> \int[mu]_(x in A) fRN x <= nu A.
Proof.
move=> mA; rewrite int_fRN_lim// lime_le //.
  exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; exact: int_F_nu.
Qed.

Lemma int_fRNE : \int[mu]_x fRN x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
  by apply: nearW => n; have [_ /andP[_]] := M_g_F n.
rewrite int_fRN_lim//.
have cvgM : (M - m.+1%:R^-1%:E) @[m --> \oo] --> M.
  rewrite -[X in _ --> X]sube0; apply: cvgeB.
  + by rewrite fin_num_adde_defl.
  + exact: cvg_cst.
  + apply/fine_cvgP; split; first exact: nearW.
    rewrite [X in X @ _ --> _](_ : _ = (fun x => x.+1%:R^-1))//.
    apply/gtr0_cvgV0; first exact: nearW.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = fun n => n + 1)%N; first exact: cvg_addnr.
    by apply/funext => n; rewrite addn1.
apply: (@le_trans _ _ (lim (M - m.+1%:R^-1%:E @[m --> \oo]))).
  by move/cvg_lim : cvgM => ->.
apply: lee_lim; [by apply/cvg_ex; exists M|exact: is_cvg_int_max_approxRN_seq|].
apply: nearW => m.
by have [/[swap] /andP[? _] /ltW/le_trans] := M_g_F m; exact.
Qed.

Section ab_absurdo.
Context A (mA : measurable A) (h : \int[mu]_(x in A) fRN x < nu A).

Lemma epsRN_ex :
  {eps : {posnum R} | \int[mu]_(x in A) (fRN x + eps%:num%:E) < nu A}.
Proof.
have [muA0|] := eqVneq (mu A) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _; rewrite -(@gee0_abs _ (_ + _)); last first.
      by rewrite adde_ge0 ?fRN_ge0.
    over.
  rewrite (@integral_abs_eq0 _ _ _ _ setT)//.
    by rewrite (le_lt_trans _ h)// integral_ge0// => x Ax; exact: fRN_ge0.
  by apply: emeasurable_funD => //; exact: measurable_fun_fRN.
rewrite neq_lt ltNge measure_ge0//= => muA_gt0.
pose mid := ((fine (nu A) - fine (\int[mu]_(x in A) fRN x)) / 2)%R.
pose e := (mid / fine (mu A))%R.
have ? : \int[mu]_(x in A) fRN x \is a fin_num.
  rewrite ge0_fin_numE// ?(lt_le_trans h)// ?leey// integral_ge0//.
  by move=> x Ax; exact: fRN_ge0.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last first.
    by rewrite fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
  by rewrite divr_gt0// subr_gt0// fine_lt// fin_num_measure.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  by move=> x Ax; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite integral_cst// -lteBrDr//; last first.
  by rewrite fin_numM// fin_num_measure.
rewrite -[X in _ * X](@fineK _ (mu A)) ?fin_num_measure//.
rewrite -EFinM -mulrA mulVr ?mulr1; last first.
  by rewrite unitfE gt_eqF// fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
rewrite lteBrDl// addeC -lteBrDl//; last first.
rewrite -(@fineK _ (nu A))// ?fin_num_measure// -[X in _ - X](@fineK _)//.
rewrite -EFinB lte_fin /mid ltr_pdivrMr// ltr_pMr// ?ltr1n// subr_gt0.
by rewrite fine_lt// fin_num_measure.
Qed.

Definition epsRN := sval epsRN_ex.

Definition sigmaRN B := nu B - \int[mu]_(x in B) (fRN x + epsRN%:num%:E).

Let sigmaRN0 : sigmaRN set0 = 0.
Proof.
by rewrite /sigmaRN measure0 integral_set0 subee.
Qed.

Let fin_num_int_fRN_eps B : measurable B ->
  \int[mu]_(x in B) (fRN x + epsRN%:num%:E) \is a fin_num.
Proof.
move=> mB; rewrite ge0_integralD//; last 2 first.
  by move=> x Bx; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite fin_numD integral_cst// fin_numM ?fin_num_measure// andbT.
rewrite ge0_fin_numE ?measure_ge0; last first.
  by apply: integral_ge0 => x Bx; exact: fRN_ge0.
rewrite (le_lt_trans _ int_fRN_lty)//.
under [in leRHS]eq_integral.
  move=> x _; rewrite gee0_abs; last first.
    exact: fRN_ge0.
  over.
apply: ge0_subset_integral => //; first exact: measurable_fun_fRN.
by move=> x _; exact: fRN_ge0.
Qed.

Let fin_num_sigmaRN B : measurable B -> sigmaRN B \is a fin_num.
Proof.
move=> mB; rewrite /sigmaRN fin_numB fin_num_measure//=.
exact: fin_num_int_fRN_eps.
Qed.

Let sigmaRN_sigma_additive : semi_sigma_additive sigmaRN.
Proof.
move=> H mH tH mUH.
rewrite [X in X @ _ --> _](_ : _ = (fun n => \sum_(0 <= i < n) nu (H i) -
  \sum_(0 <= i < n) \int[mu]_(x in H i) (fRN x + epsRN%:num%:E))); last first.
  apply/funext => n; rewrite big_split/= fin_num_sumeN// => i _.
  by rewrite fin_num_int_fRN_eps.
apply: cvgeB.
- by rewrite adde_defC fin_num_adde_defl// fin_num_measure.
- exact: measure_semi_sigma_additive.
- rewrite (ge0_integral_bigcup _ mH _ _ tH).
  + have /cvg_ex[/= l hl] : cvg ((fun n =>
        \sum_(0 <= i < n) \int[mu]_(y in H i) (fRN y + epsRN%:num%:E)) @ \oo).
      apply: is_cvg_ereal_nneg_natsum => n _.
      by apply: integral_ge0 => x _; rewrite adde_ge0 ?fRN_ge0.
    by rewrite (@cvg_lim _ _ _ _ _ _ l).
  + apply: emeasurable_funD => //=; apply: measurable_funTS.
    exact: measurable_fun_fRN.
  + by move=> x _; rewrite adde_ge0 ?fRN_ge0.
Qed.

HB.instance Definition _ := @isCharge.Build _ _ _ sigmaRN
  sigmaRN0 fin_num_sigmaRN sigmaRN_sigma_additive.

End ab_absurdo.

End lim_max_approxRN_seq.
End lim_max_approxRN_seq.

Section radon_nikodym_finite.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import lim_max_approxRN_seq.

Let f := fRN mu nu.
Let mf := measurable_fun_fRN.
Let f_ge0 := fRN_ge0.

Lemma radon_nikodym_finite : nu `<< mu -> exists f : T -> \bar R,
  [/\ forall x, f x >= 0, mu.-integrable [set: T] f &
      forall E, measurable E -> nu E = \int[mu]_(x in E) f x].
Proof.
move=> nu_mu; exists f; split.
  - by move=> x; exact: f_ge0.
  - by apply/integrableP; split; [exact: mf|exact: int_fRN_lty].
move=> // A mA.
apply/eqP; rewrite eq_le int_fRN_ub// andbT leNgt; apply/negP => abs.
pose sigma : {charge set T -> \bar R} := sigmaRN mA abs.
have [P [N [[mP posP] [mN negN] PNX PN0]]] := Hahn_decomposition sigma.
pose AP := A `&` P.
have mAP : measurable AP by exact: measurableI.
have muAP_gt0 : 0 < mu AP.
  rewrite lt0e measure_ge0// andbT.
  apply/eqP/(contra_not (nu_mu _ mAP))/eqP; rewrite gt_eqF//.
  rewrite (@lt_le_trans _ _ (sigma AP))//.
    rewrite (@lt_le_trans _ _ (sigma A))//; last first.
      rewrite (charge_partition _ _ mP mN)// geeDl//.
      by apply: negN => //; exact: measurableI.
    by rewrite sube_gt0// (proj2_sig (epsRN_ex mA abs)).
  rewrite /sigma/= /sigmaRN lee_subel_addl ?fin_num_measure//.
  by rewrite lee_paddl// integral_ge0// => x _; rewrite adde_ge0//; exact: f_ge0.
pose h x := if x \in AP then f x + (epsRN mA abs)%:num%:E else f x.
have mh : measurable_fun setT h.
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite setTI preimage_mem_true.
  - by apply: measurable_funTS; apply: emeasurable_funD => //; exact: mf.
  - by apply: measurable_funTS; exact: mf.
have hge0 x : 0 <= h x.
  by rewrite /h; case: ifPn => [_|?]; rewrite ?adde_ge0 ?f_ge0.
have hnuP S : measurable S -> S `<=` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS SAP.
  have : 0 <= sigma S.
    by apply: posP => //; apply: (subset_trans SAP); exact: subIsetr.
  rewrite sube_ge0; last by rewrite fin_num_measure// orbT.
  apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite -{1}(setIid S) integral_mkcondr; apply/eq_integral => x /[!inE] Sx.
  by rewrite /restrict /h !ifT// inE//; exact: SAP.
have hnuN S : measurable S -> S `<=` ~` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS ScAP; rewrite /h; under eq_integral.
    move=> x xS; rewrite ifF; last first.
      by apply/negbTE; rewrite notin_setE; apply: ScAP; apply: set_mem.
    over.
  exact: int_fRN_ub.
have hnu S : measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> mS.
  rewrite -(setD0 S) -(setDv AP) setDDr.
  have mSIAP : measurable (S `&` AP) by exact: measurableI.
  have mSDAP : measurable (S `\` AP) by exact: measurableD.
  rewrite ge0_integral_setU //.
  - rewrite measureU//.
      by apply: leeD; [exact: hnuN|exact: hnuP].
    by rewrite setDE setIACA setICl setI0.
  - exact: measurable_funTS.
  - by rewrite disj_set2E setDE setIACA setICl setI0.
have int_h_M : \int[mu]_x h x > M.
  have mCAP := measurableC mAP.
  have disj_AP : [disjoint AP & ~` AP] by exact/disj_set2P/setICr.
  rewrite -(setUv AP) ge0_integral_setU ?setUv// /h.
  under eq_integral do rewrite ifT//.
  under [X in _ < _ + X]eq_integral.
    by move=> x; rewrite inE /= => xE0p; rewrite memNset//; over.
  rewrite ge0_integralD//; last 2 first.
    - by move=> x _; exact: f_ge0.
    - by apply: measurable_funTS; exact: mf.
  rewrite integral_cst // addeAC -ge0_integral_setU//; last 2 first.
    by rewrite setUv//; exact: mf.
    by move=> x _; exact: f_ge0.
  rewrite setUv int_fRNE -lte_subel_addl; last first.
    rewrite ge0_fin_numE ?sup_int_approxRN_lty.
      exact: approxRN_seq.sup_int_approxRN_lty.
    exact: sup_int_approxRN_ge0.
  by rewrite /M subee ?mule_gt0// approxRN_seq.sup_int_approxRN_fin_num.
have Gh : G h.
  split=> //; apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite (le_lt_trans (hnu _ measurableT))// ltey_eq fin_num_measure.
have : \int[mu]_x h x <= M.
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  rewrite (@le_ereal_sup _ [set \int[mu]_x h x] (int_approxRN mu nu))//.
  by rewrite sub1set inE; exists h.
by rewrite leNgt int_h_M.
Qed.

End radon_nikodym_finite.

Section radon_nikodym_sigma_finite.
Context d (T : measurableType d) (R : realType).
Variables (mu : {sigma_finite_measure set T -> \bar R})
          (nu : {finite_measure set T -> \bar R}).

Lemma radon_nikodym_sigma_finite : nu `<< mu ->
  exists f : T -> \bar R, [/\ forall x, f x >= 0, forall x, f x \is a fin_num,
    mu.-integrable [set: T] f &
    forall A, measurable A -> nu A = \int[mu]_(x in A) f x].
Proof.
move=> nu_mu; have [F TF /all_and2[mF muFoo]] := sigma_finiteT mu.
pose E := seqDU F.
have mE k : measurable (E k).
  by apply: measurableD => //; exact: bigsetU_measurable.
have muEoo k : mu (E k) < +oo.
  by rewrite (le_lt_trans _ (muFoo k))// le_measure ?inE//; exact: subDsetl.
have UET : \bigcup_i E i = [set: T] by rewrite TF [RHS]seqDU_bigcup_eq.
have tE := trivIset_seqDU F.
pose mu_ j : {finite_measure set T -> \bar R} := mfrestr (mE j) (muEoo j).
have nuEoo i : nu (E i) < +oo by rewrite ltey_eq fin_num_measure.
pose nu_ j : {finite_measure set T -> \bar R} := mfrestr (mE j) (nuEoo j).
have nu_mu_ k : nu_ k `<< mu_ k.
  by move=> S mS mu_kS0; apply: nu_mu => //; exact: measurableI.
have [g_] := choice (fun j => radon_nikodym_finite (nu_mu_ j)).
move=> /all_and3[g_ge0 ig_ int_gE].
pose f_ j x := if x \in E j then g_ j x else 0.
have f_ge0 k x : 0 <= f_ k x by rewrite /f_; case: ifP.
have mf_ k : measurable_fun setT (f_ k).
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite setTI preimage_mem_true.
  - rewrite preimage_mem_true.
    by apply: measurable_funTS => //; have /integrableP[] := ig_ k.
have if_T k : integrable mu setT (f_ k).
  apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -(setUv (E k)) ge0_integral_setU //; last 3 first.
    - exact: measurableC.
    - by rewrite setUv.
    - exact/disj_set2P/subsets_disjoint.
  rewrite /f_; under eq_integral do rewrite ifT//.
  rewrite (@eq_measure_integral _ _ _ (E k) (mu_ k)); last first.
    by move=> A mA AEj; rewrite /mu_ /= /mfrestr /mrestr setIidl.
  rewrite -int_gE ?inE//.
  under eq_integral.
    move=> x /[!inE] /= Ekx; rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 ?adde0 ltey_eq fin_num_measure.
have int_f_E j S : measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)) (ge0_integral_setU _ mSIEj mSDEj)//; last 2 first.
    - by rewrite setUIDK; exact: (measurable_funS measurableT).
    - by apply/disj_set2P; rewrite setDE setIACA setICr setI0.
  rewrite /f_ -(eq_integral _ (g_ j)); last first.
    by move=> x /[!inE] SIEjx; rewrite /f_ ifT// inE; exact: (@subIsetr _ S).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)); last first.
    move=> A mA; rewrite subsetI => -[_ ?]; rewrite /mu_ /=.
    by rewrite /mfrestr /mrestr setIidl.
  rewrite -int_gE; last exact: measurableI.
  under eq_integral.
    move=> x; rewrite inE setDE /= => -[_ Ejx].
    rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 adde0 /nu_/= /mfrestr /mrestr -setIA setIid.
pose f x : \bar R := \sum_(j <oo) f_ j x.
have int_f_nuT : \int[mu]_x f x = nu setT.
  rewrite integral_nneseries//.
  transitivity (\sum_(n <oo) nu (E n)).
    by apply: eq_eseriesr => i _; rewrite int_f_E// setTI.
  rewrite -UET measure_bigcup//.
  by apply: eq_eseriesl => // x; rewrite in_setT.
have mf : measurable_fun setT f by exact: ge0_emeasurable_sum.
have fi : mu.-integrable setT f.
  apply/integrableP; split => //.
  under eq_integral do (rewrite gee0_abs; last exact: nneseries_ge0).
  by rewrite int_f_nuT ltey_eq fin_num_measure.
have ae_f := integrable_ae measurableT fi.
pose f' x := if f x \is a fin_num then f x else 0.
have ff' : ae_eq mu setT f f'.
  case: ae_f => N [mN N0 fN]; exists N; split => //.
  apply: subset_trans fN; apply: subsetC => z/= /(_ I) fz _.
  by rewrite /f' fz.
have mf' : measurable_fun setT f'.
  apply: measurable_fun_ifT => //; apply: (measurable_fun_bool true) => /=.
  by have := emeasurable_fin_num measurableT mf; rewrite setTI.
exists f'; split.
- by move=> t; rewrite /f'; case: ifPn => // ?; exact: nneseries_ge0.
- by move=> t; rewrite /f'; case: ifPn.
- apply/integrableP; split => //; apply/abse_integralP => //.
  move/ae_eq_integral : (ff') => /(_ measurableT mf) <-//.
  by apply/abse_integralP => //; move/integrableP : fi => [].
have nuf A : d.-measurable A -> nu A = \int[mu]_(x in A) f x.
  move=> mA; rewrite integral_nneseries//; last first.
    by move=> n; exact: measurable_funTS.
  rewrite nneseries_esum; last by move=> m _; rewrite integral_ge0.
  under eq_esum do rewrite int_f_E//.
  rewrite -nneseries_esum; last first.
    by move=> n; rewrite measure_ge0//; exact: measurableI.
  rewrite (@eq_eseriesl _ _ (fun x => x \in [set: nat])); last first.
    by move=> x; rewrite in_setT.
  rewrite -measure_bigcup//.
  - by rewrite -setI_bigcupr UET setIT.
  - by move=> i _; exact: measurableI.
  - exact: trivIset_setIl.
move=> A mA; rewrite nuf ?inE//; apply: ae_eq_integral => //.
- exact/measurable_funTS.
- exact/measurable_funTS.
- exact: (@ae_eq_subset _ _ _ _ mu setT A f f' (@subsetT _ A)).
Qed.

End radon_nikodym_sigma_finite.

Module Radon_Nikodym_SigmaFinite.
Section radon_nikodym_sigma_finite_def.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).

Definition f : T -> \bar R :=
  match pselect (nu `<< mu) with
  | left nu_mu => sval (cid (radon_nikodym_sigma_finite nu_mu))
  | right _ => cst -oo
  end.

Lemma f_ge0 : nu `<< mu -> forall x, 0 <= f x.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_fin_num : nu `<< mu -> forall x, f x \is a fin_num.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_integrable : nu `<< mu -> mu.-integrable [set: T] f.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_integral : nu `<< mu -> forall A, measurable A ->
    nu A = \int[mu]_(x in A) f x.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

End radon_nikodym_sigma_finite_def.

Section integrableM.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).
Hypothesis numu : nu `<< mu.
Implicit Types f : T -> \bar R.

Local Notation "'d nu '/d mu" := (f nu mu).

Import HBNNSimple.

Lemma change_of_variables f E : (forall x, 0 <= f x) ->
    measurable E -> measurable_fun E f ->
  \int[mu]_(x in E) (f x * ('d nu '/d mu) x) = \int[nu]_(x in E) f x.
Proof.
move=> f0 mE mf; set g := 'd nu '/d mu.
pose h := nnsfun_approx mE mf.
have -> : \int[nu]_(x in E) f x =
    lim (\int[nu]_(x in E) (EFin \o h n) x @[n --> \oo]).
  have fE x : E x -> f x = lim ((EFin \o h n) x @[n --> \oo]).
    by move=> Ex; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  under eq_integral => x /[!inE] /fE -> //.
  apply: monotone_convergence => //.
  - move=> n; apply/measurable_EFinP.
    by apply: (measurable_funS measurableT) => //; exact/measurable_funP.
  - by move=> n x Ex //=; rewrite lee_fin.
  - by move=> x Ex a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
have -> : \int[mu]_(x in E) (f \* g) x =
    lim (\int[mu]_(x in E) ((EFin \o h n) \* g) x @[n --> \oo]).
  have fg x :E x -> f x * g x = lim (((EFin \o h n) \* g) x @[n --> \oo]).
    by move=> Ex; apply/esym/cvg_lim => //; apply: cvgeMr;
      [exact: f_fin_num|exact: cvg_nnsfun_approx].
  under eq_integral => x /[!inE] /fg -> //.
  apply: monotone_convergence => [//| | |].
  - move=> n; apply/emeasurable_funM; apply/measurable_funTS.
      exact/measurable_EFinP.
    exact: measurable_int (f_integrable _).
  - by move=> n x Ex /=; rewrite mule_ge0 ?lee_fin ?f_ge0.
  - by move=> x Ex a b ab/=; rewrite lee_wpmul2r ?lee_fin ?f_ge0//; exact/lefP/nd_nnsfun_approx.
suff suf n : \int[mu]_(x in E) ((EFin \o h n) x * g x) =
    \int[nu]_(x in E) (EFin \o h n) x.
  by under eq_fun do rewrite suf.
transitivity (\int[nu]_(x in E)
   (\sum_(y \in range (h n)) (y * \1_(h n @^-1` [set y]) x)%:E)); last first.
  by apply: eq_integral => t tE; rewrite /= fimfunE -fsumEFin.
have indich m r : measurable_fun E (fun x => (r * \1_(h m @^-1` [set r]) x)%:E).
  by apply: (measurable_comp measurableT) => //; exact: measurable_funM.
rewrite ge0_integral_fsum//; last by move=> m y Ey; exact: nnfun_muleindic_ge0.
transitivity (\int[mu]_(x in E) (\sum_(y \in range (h n))
    (y * \1_(h n @^-1` [set y]) x)%:E * g x)).
  under [RHS]eq_integral => x xE.
    rewrite -ge0_mule_fsuml => [|y]; last exact: nnfun_muleindic_ge0.
    rewrite fsumEFin // -(fimfunE _ x); over.
  by [].
rewrite ge0_integral_fsum//; last 2 first.
  - move=> y; apply: emeasurable_funM => //; apply: measurable_funTS.
    exact: measurable_int (f_integrable _).
  - by move=> m y Ey; rewrite mule_ge0 ?f_ge0// nnfun_muleindic_ge0.
apply: eq_fsbigr => r rhn.
under [RHS]eq_integral do rewrite EFinM.
rewrite integralZl_indic_nnsfun => //.
under eq_integral do rewrite EFinM -muleA.
rewrite ge0_integralZl//.
- under eq_integral do rewrite muleC.
  rewrite (eq_integral (g \_ (h n @^-1` [set r]))); last first.
    by move=> x xE; rewrite epatch_indic.
  by rewrite -integral_mkcondr -f_integral// integral_indic// setIC.
- apply: emeasurable_funM; first exact/measurable_EFinP.
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
- by move=> t Et; rewrite mule_ge0 ?lee_fin ?f_ge0.
- by move: rhn; rewrite inE => -[t _ <-]; rewrite lee_fin.
Qed.

Lemma integrableM f E : (forall x, 0 <= f x) -> measurable E ->
  nu.-integrable E f -> mu.-integrable E (f \* 'd nu '/d mu).
Proof.
move=> f0 mE intEf; apply/integrableP; split.
  apply: emeasurable_funM; first exact: (measurable_int nu).
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
under eq_integral.
  move=> x _; rewrite gee0_abs; last first.
    by apply: mule_ge0=> //; exact: f_ge0.
  over.
rewrite change_of_variables//; last exact: (measurable_int nu).
by move/integrableP : intEf=> [mf +]; under eq_integral do rewrite gee0_abs//.
Qed.

End integrableM.

Section chain_rule.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (la : {sigma_finite_measure set T -> \bar R})
          (mu : {finite_measure set T -> \bar R}).

Local Notation "'d nu '/d mu" := (f nu mu).

Lemma chain_rule E : nu `<< mu -> mu `<< la -> measurable E ->
  ae_eq la E ('d nu '/d la) ('d nu '/d mu \* 'd mu '/d la).
Proof.
move=> numu mula mE.
have mf : measurable_fun E ('d nu '/d mu).
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
apply: integral_ae_eq => //.
- apply: (integrableS measurableT) => //; apply: f_integrable.
  exact: measure_dominates_trans numu mula.
- apply: emeasurable_funM => //.
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
- move=> A AE mA; rewrite change_of_variables//.
  + by rewrite -!f_integral//; exact: measure_dominates_trans numu mula.
  + exact: f_ge0.
  + exact: measurable_funS mf.
Qed.

End chain_rule.
End Radon_Nikodym_SigmaFinite.

Section radon_nikodym.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).

Local Lemma Radon_Nikodym0 : nu `<< mu ->
  exists f : T -> \bar R, [/\ (forall x, f x \is a fin_num),
    mu.-integrable [set: T] f &
    forall A, measurable A -> nu A = \int[mu]_(x in A) f x].
Proof.
move=> nu_mu; have [P [N nuPN]] := Hahn_decomposition nu.
have [fp [fp0 fpfin intfp fpE]] := @radon_nikodym_sigma_finite _ _ _ mu
  (jordan_pos nuPN) (jordan_pos_dominates nuPN nu_mu).
have [fn [fn0 fnfin intfn fnE]] := @radon_nikodym_sigma_finite _ _ _ mu
  (jordan_neg nuPN) (jordan_neg_dominates nuPN nu_mu).
exists (fp \- fn); split; first by move=> x; rewrite fin_numB// fpfin fnfin.
  exact: integrableB.
move=> E mE; rewrite [LHS](jordan_decomp nuPN mE)// integralB//;
  [|exact: (integrableS measurableT)..].
rewrite -fpE ?inE// -fnE ?inE//= /cadd/= jordan_posE jordan_negE.
by rewrite /cscale EFinN mulN1e.
Qed.

Definition Radon_Nikodym : T -> \bar R :=
  match pselect (nu `<< mu) with
  | left nu_mu => sval (cid (Radon_Nikodym0 nu_mu))
  | right _ => cst -oo
  end.

Lemma Radon_NikodymE (numu : nu `<< mu) :
  Radon_Nikodym = sval (cid (Radon_Nikodym0 numu)).
Proof.
rewrite /= /Radon_Nikodym; case: pselect => //= numu'.
by congr (sval (cid (Radon_Nikodym0 _))); exact: Prop_irrelevance.
Qed.

Lemma Radon_Nikodym_fin_num x : nu `<< mu ->
  Radon_Nikodym x \is a fin_num.
Proof. by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? []. Qed.

Lemma Radon_Nikodym_integrable : nu `<< mu ->
  mu.-integrable [set: T] Radon_Nikodym.
Proof. by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? []. Qed.

Lemma Radon_Nikodym_integral A : nu `<< mu ->
  measurable A -> nu A = \int[mu]_(x in A) Radon_Nikodym x.
Proof.
by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? [? ?]; exact.
Qed.

End radon_nikodym.
Notation "'d nu '/d mu" := (Radon_Nikodym nu mu) : charge_scope.

#[global] Hint Extern 0 (_.-integrable setT ('d _ '/d _)) =>
  solve [apply: Radon_Nikodym_integrable] : core.
#[global] Hint Extern 0 (measurable_fun setT ('d _ '/d _)) =>
  solve [apply: measurable_int; exact: Radon_Nikodym_integrable] : core.

Section Radon_Nikodym_charge_of_finite_measure.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).
Hypothesis numu : nu `<< mu.
Implicit Types f : T -> \bar R.

Lemma ae_eq_Radon_Nikodym_SigmaFinite E : measurable E ->
  ae_eq mu E (Radon_Nikodym_SigmaFinite.f nu mu)
             ('d (charge_of_finite_measure nu) '/d mu).
Proof.
move=> mE; apply: integral_ae_eq => //.
- apply: (integrableS measurableT) => //.
  exact: Radon_Nikodym_SigmaFinite.f_integrable.
- exact: measurable_funTS.
- move=> A AE mA; rewrite -Radon_Nikodym_integral//.
  by rewrite -Radon_Nikodym_SigmaFinite.f_integral.
Qed.

(* TODO: move back to measure.v, current version incompatible *)
Lemma ae_eq_mul2l (f g h : T -> \bar R) D : f = g %[ae mu in D] -> (h \* f) = (h \* g) %[ae mu in D].
Proof. by apply: filterS => x /= /[apply] ->. Qed.

Lemma Radon_Nikodym_change_of_variables f E : measurable E ->
    nu.-integrable E f ->
  \int[mu]_(x in E) (f x * ('d (charge_of_finite_measure nu) '/d mu) x) =
  \int[nu]_(x in E) f x.
Proof.
move=> mE mf; rewrite [in RHS](funeposneg f) integralB //; last 2 first.
  - exact: integrable_funepos.
  - exact: integrable_funeneg.
rewrite -(ae_eq_integral _ _ _ _ _
    (ae_eq_mul2l f (ae_eq_Radon_Nikodym_SigmaFinite mE)))//; last 2 first.
- apply: emeasurable_funM => //; first exact: measurable_int mf.
  apply: measurable_funTS.
  exact: measurable_int (Radon_Nikodym_SigmaFinite.f_integrable _).
- apply: emeasurable_funM => //; first exact: measurable_int mf.
  exact: measurable_funTS.
rewrite [in LHS](funeposneg f).
under [in LHS]eq_integral => x xE. rewrite muleBl; last 2 first.
  - exact: Radon_Nikodym_SigmaFinite.f_fin_num.
  - exact: add_def_funeposneg.
  over.
rewrite [in LHS]integralB //; last 2 first.
- apply: Radon_Nikodym_SigmaFinite.integrableM => //.
  exact: integrable_funepos.
- apply: Radon_Nikodym_SigmaFinite.integrableM => //.
  exact: integrable_funeneg.
congr (_ - _) ; rewrite Radon_Nikodym_SigmaFinite.change_of_variables//;
  apply: measurable_int; first exact: integrable_funepos mf.
exact: integrable_funeneg mf.
Qed.

End Radon_Nikodym_charge_of_finite_measure.

Section radon_nikodym_lemmas.
Context d (T : measurableType d) (R : realType).
Implicit Types (nu : {charge set T -> \bar R})
               (mu : {sigma_finite_measure set T -> \bar R}).

Lemma Radon_Nikodym_cscale mu nu c E : measurable E -> nu `<< mu ->
  ae_eq mu E ('d (cscale c nu) '/d mu) (fun x => c%:E * 'd nu '/d mu x).
Proof.
move=> mE numu; apply: integral_ae_eq => [//| | |A AE mA].
- apply: (integrableS measurableT) => //.
  exact/Radon_Nikodym_integrable/dominates_cscalel.
- exact/measurable_funTS/emeasurable_funM.
- rewrite integralZl//; last first.
    by apply: (integrableS measurableT) => //; exact: Radon_Nikodym_integrable.
  rewrite -Radon_Nikodym_integral => //; last exact: dominates_cscalel.
  by rewrite -Radon_Nikodym_integral.
Qed.

Lemma Radon_Nikodym_cadd mu nu0 nu1 E : measurable E ->
  nu0 `<< mu -> nu1 `<< mu ->
  ae_eq mu E ('d (cadd nu0 nu1) '/d mu) ('d nu0 '/d mu \+ 'd nu1 '/d mu).
Proof.
move=> mE nu0mu nu1mu; apply: integral_ae_eq => [//| | |A AE mA].
- apply: (integrableS measurableT) => //.
  by apply: Radon_Nikodym_integrable => /=; exact: dominates_cadd.
- by apply: measurable_funTS => //; exact: emeasurable_funD.
- rewrite integralD //; [|exact: integrableS (Radon_Nikodym_integrable _)..].
  rewrite -Radon_Nikodym_integral //=; last exact: dominates_cadd.
  by rewrite -Radon_Nikodym_integral // -Radon_Nikodym_integral.
Qed.

End radon_nikodym_lemmas.

Section Radon_Nikodym_chain_rule.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R})
          (la : {sigma_finite_measure set T -> \bar R})
          (mu : {finite_measure set T -> \bar R}).

Lemma Radon_Nikodym_chain_rule : nu `<< mu -> mu `<< la ->
  ae_eq la setT ('d nu '/d la)
                ('d nu '/d mu \* 'd (charge_of_finite_measure mu) '/d la).
Proof.
have [Pnu [Nnu nuPN]] := Hahn_decomposition nu.
move=> numu mula; have nula := measure_dominates_trans numu mula.
apply: integral_ae_eq; [exact: measurableT| |exact: emeasurable_funM|].
- exact: Radon_Nikodym_integrable.
- move=> E _ mE.
  rewrite -Radon_Nikodym_integral// Radon_Nikodym_change_of_variables//.
  + exact: Radon_Nikodym_integral.
  + by apply: (integrableS measurableT) => //; exact: Radon_Nikodym_integrable.
Qed.

End Radon_Nikodym_chain_rule.
