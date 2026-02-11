(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences esum.
From mathcomp Require Import measure numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel.

(**md**************************************************************************)
(* # Bernoulli distribution                                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*      bernoulli_pmf p == Bernoulli pmf with parameter p : R                 *)
(*     bernoulli_prob p == Bernoulli probability measure when 0 <= p <= 1     *)
(*                         and \d_false otherwise                             *)
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

Section bernoulli_pmf.
Context {R : numDomainType} (p : R).
Local Open Scope ring_scope.

Definition bernoulli_pmf b := if b then p else 1 - p.

Lemma bernoulli_pmf_ge0 b : 0 <= p <= 1 -> 0 <= bernoulli_pmf b.
Proof.
rewrite /bernoulli_pmf.
by move=> /andP[p0 p1]; case: ifPn => // _; rewrite subr_ge0.
Qed.

Lemma bernoulli_pmf1 : \sum_(i \in [set: bool]) (bernoulli_pmf i)%:E = 1%E.
Proof.
rewrite setT_bool fsbigU//=; last by move=> x [/= ->].
by rewrite !fsbig_set1/= -EFinD subrKC.
Qed.

End bernoulli_pmf.

Lemma measurable_bernoulli_pmf {R : realType} D n :
  measurable_fun D (@bernoulli_pmf R ^~ n).
Proof.
by apply/measurable_funTS/measurable_fun_if => //=; exact: measurable_funB.
Qed.

Definition bernoulli_prob {R : realFieldType} (p : R) : set bool -> \bar R :=
  fun A => if 0 <= p <= 1 then
    \sum_(b \in A) (bernoulli_pmf p b)%:E
  else
    \d_false A.

Section bernoulli.
Context {R : realType} (p : R).

Local Notation bernoulli := (bernoulli_prob p).

Let bernoulli0 : bernoulli set0 = 0.
Proof. by rewrite /bernoulli; case: ifPn => // p01; rewrite fsbig_set0. Qed.

Let bernoulli_ge0 U : (0 <= bernoulli U)%E.
Proof.
rewrite /bernoulli; case: ifPn => // p01.
rewrite fsbig_finite//= sumEFin lee_fin.
by apply: sumr_ge0 => /= b _; exact: bernoulli_pmf_ge0.
Qed.

Let bernoulli_sigma_additive : semi_sigma_additive bernoulli.
Proof.
move=> F mF tF mUF; rewrite /bernoulli; case: ifPn => p01; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _.
  rewrite fsbig_finite//= sumEFin lee_fin.
  by apply: sumr_ge0 => /= b _; exact: bernoulli_pmf_ge0.
transitivity (\sum_(0 <= i <oo) (\esum_(j in F i) (bernoulli_pmf p j)%:E))%E.
apply: eq_eseriesr => k _; rewrite esum_fset//= => b _.
  by rewrite lee_fin bernoulli_pmf_ge0.
rewrite -nneseries_sum_bigcup//=; last first.
  by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
by rewrite esum_fset//= => b _; rewrite lee_fin bernoulli_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ bernoulli
  bernoulli0 bernoulli_ge0 bernoulli_sigma_additive.

Let bernoulli_setT : bernoulli [set: _] = 1%E.
Proof. by rewrite /bernoulli/= probability_setT bernoulli_pmf1 if_same. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

Lemma eq_bernoulli (P : probability bool R) :
  P [set true] = p%:E -> P =1 bernoulli.
Proof.
move=> Ptrue sb; rewrite /bernoulli /bernoulli_pmf.
have Pfalse : P [set false] = (1 - p%:E)%E.
  rewrite -Ptrue -(probability_setT P) setT_bool measureU//; last first.
    by rewrite disjoints_subset => -[].
  by rewrite addeAC subee ?add0e//= Ptrue.
have : (0 <= p%:E <= 1)%E by rewrite -Ptrue measure_ge0 probability_le1.
rewrite !lee_fin => ->.
have eq_sb := etrans (bigcup_imset1 (_ : set bool) id) (image_id _).
rewrite -[in LHS](eq_sb sb)/= measure_fin_bigcup//.
- by apply: eq_fsbigr => /= -[].
- exact: finite_finset.
- by move=> [] [] _ _ [[]]//= [].
Qed.

End bernoulli.

Section bernoulli_measure.
Context {R : realType}.
Variables (p : R) (p0 : 0 <= p) (p1 : (NngNum p0)%:num <= 1).

Lemma bernoulli_dirac : bernoulli_prob p = measure_add
  (mscale (NngNum p0) \d_true) (mscale (1 - (Itv01 p0 p1)%:num)%:nng \d_false).
Proof.
apply/funext => U; rewrite /bernoulli_prob; case: ifPn => [p01|]; last first.
  by rewrite p0/= p1.
rewrite measure_addE/= /mscale/=.
have := @subsetT _ U; rewrite setT_bool => UT.
have [->|->|->|->] /= := subset_set2 UT.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  by rewrite esum_set0 2!measure0 2!mule0 adde0.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  rewrite esum_set1/= ?lee_fin// 2!diracE mem_set//= memNset//= mule0 adde0.
  by rewrite mule1.
- rewrite -esum_fset//=; last by move=> b; rewrite lee_fin bernoulli_pmf_ge0.
  rewrite esum_set1/= ?lee_fin ?subr_ge0// 2!diracE memNset//= mem_set//=.
  by rewrite mule0 add0e mule1.
- rewrite fsbigU//=; last by move=> x [->].
  by rewrite 2!fsbig_set1/= -setT_bool 2!diracT !mule1.
Qed.

End bernoulli_measure.
Arguments bernoulli_prob {R}.

Lemma eq_bernoulliV2 {R : realType} (P : probability bool R) :
  P [set true] = P [set false] -> P =1 bernoulli_prob 2^-1.
Proof.
move=> Ptrue_eq_false; apply/eq_bernoulli.
have : P [set: bool] = 1%E := probability_setT P.
rewrite setT_bool measureU//=; last by rewrite disjoints_subset => -[].
rewrite Ptrue_eq_false -mule2n => /esym/eqP.
by rewrite -mule_natl -eqe_pdivrMl// mule1 => /eqP<-.
Qed.

Section integral_bernoulli.
Context {R : realType}.
Variables (p : R) (p01 : 0 <= p <= 1).
Local Open Scope ereal_scope.

Lemma bernoulli_probE A :
  bernoulli_prob p A = p%:E * \d_true A + p.~%:E * \d_false A.
Proof. by case/andP : p01 => p0 p1; rewrite bernoulli_dirac// measure_addE. Qed.

Lemma integral_bernoulli_prob (f : bool -> \bar R) : (forall x, 0 <= f x) ->
  \int[bernoulli_prob p]_y (f y) = p%:E * f true + p.~%:E * f false.
Proof.
move=> f0; case/andP : p01 => p0 p1; rewrite bernoulli_dirac/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= !diracT !mul1e.
Qed.

End integral_bernoulli.

Section measurable_bernoulli.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Type p : R.

Lemma measurable_bernoulli_prob :
  measurable_fun setT (bernoulli_prob : R -> pprobability bool R).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_ifT => //=.
  by apply: measurable_and => //; exact: measurable_fun_ler.
apply: (eq_measurable_fun (fun t =>
    \sum_(b <- fset_set Ys) (@bernoulli_pmf R t b)%:E)).
  by move=> x _; rewrite fsbig_finite/=.
apply: emeasurable_sum => n; move=> k Ysk; apply/measurableT_comp => //.
exact: measurable_bernoulli_pmf.
Qed.

Lemma measurable_bernoulli_prob2 U : measurable U ->
  measurable_fun setT (bernoulli_prob ^~ U : R -> \bar R).
Proof.
move=> mU.
exact: (measurable_kernel (kprobability measurable_bernoulli_prob)).
Qed.

End measurable_bernoulli.
Arguments measurable_bernoulli_prob {R}.
