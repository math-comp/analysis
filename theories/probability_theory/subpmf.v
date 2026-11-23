From HB Require Import structures.
From mathcomp Require Import boot order algebra.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions filter.
From mathcomp Require Import cardinality fsbigop reals discrete.
From mathcomp Require Import topology normedtype sequences esum ereal numfun.
From mathcomp Require Import measure lebesgue_measure measurable_realfun
  lebesgue_integral giry hoelder random_variable.

(**md**************************************************************************)
(* # Subprobability mass function                                             *)
(*                                                                            *)
(* Caution: This file is experimental. The interface may change in the        *)
(* future.                                                                    *)
(*                                                                            *)
(* `R.-pmf T`                                                                 *)
(* : subprobability mass function for choiceType `T` with values in `R`       *)
(*                                                                            *)
(* `isSubPmf`                                                                 *)
(* : interface for functions that satisfy the property of subprobability      *)
(* : mass function                                                            *)
(*                                                                            *)
(* `\P_[mu] E`                                                                *)
(* : probability of the event `E` w.r.t. the subpmf `mu`                      *)
(*                                                                            *)
(* `\P_[mu, A] E`                                                             *)
(* : probability of the event `E` conditioned on the event `A`                *)
(*                                                                            *)
(* `\E_[mu] f`                                                                *)
(* : expectation of the real-valued function `f` w.r.t. the subpmf `mu`       *)
(*                                                                            *)
(* `subpmf_sum`                                                               *)
(* : alternative characterization of subpmf in terms of uniq lists            *)
(*                                                                            *)
(* `pmf_esummable mu f`                                                       *)
(* : summability of the function `f` weighted by the subpmf `mu`              *)
(*                                                                            *)
(* `pmf_zero`                                                                 *)
(* : the zero subpmf                                                          *)
(*                                                                            *)
(* `pmf_restr p mu`                                                           *)
(* : restriction of `mu` to the predicate `p`, zero outside of it             *)
(*                                                                            *)
(* `pmf_count s`                                                              *)
(* : subpmf on the elements of the sequence `s`, each weighted by its         *)
(* : number of occurrences in `s`                                             *)
(*                                                                            *)
(* `pmf_ret x`                                                                *)
(* : degenerated subpmf                                                       *)
(*                                                                            *)
(* `pmf_uniform s`                                                            *)
(* : uniform subpmf on the elements of the sequence `s`                       *)
(*                                                                            *)
(* `pmf_flip r`                                                               *)
(* : subpmf on booleans, `true` with probability `r` clamped to $[0, 1]$      *)
(*                                                                            *)
(* `\bind_(i <- d) E`                                                         *)
(* : monadic bind for subpmf                                                  *)
(*                                                                            *)
(* `pmf_bindr f`                                                              *)
(* : reverse monadic bind                                                     *)
(*                                                                            *)
(* `pmf_iter n f`                                                             *)
(* : `n`-fold iteration of `pmf_bindr f` from a degenerated subpmf            *)
(*                                                                            *)
(* `\lim_(n) E`                                                               *)
(* : limit for index subpmf                                                   *)
(*                                                                            *)
(* `pmf_margin h mu`                                                          *)
(* : image of the subpmf `mu` along the function `h`                          *)
(*                                                                            *)
(* `pmf_swap mu`                                                              *)
(* : image of a subpmf on pairs under the swapping of the components          *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "R '.-pmf'  T"
  (at level 1, T at level 2, format "R '.-pmf'  T ").
Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").
Reserved Notation "\bind_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \bind_ ( i  <-  d ) '/  '  E ']'").
Reserved Notation "\lim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \lim_ ( n ) '/  '  E ']'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation "f '<=1' g" := (forall x, f x <= g x)
  (at level 70, no associativity).
Local Notation "f '<=2' g" := (forall x y, f x y <= g x y)
  (at level 70, no associativity).

Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display (discrete_measurable_space T)
  discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} {T : choiceType} (f : T -> \bar R) :
  \esum_(x in [set: discrete_measurable_space T]) f x =
  \esum_(x in [set: T]) f x.
Proof.
by apply: (@reindex_esum R T (discrete_measurable_space T) setT setT id); split.
Qed.

Lemma measurable_discrete {T : choiceType}
    (A : set (discrete_measurable_space T)) :
  measurable A.
Proof. by []. Qed.

#[global] Hint Resolve measurable_discrete : core.

Lemma measurable_fun_discrete {T : choiceType} {d'} {U : sigmaRingType d'}
    (D : set (discrete_measurable_space T))
    (f : discrete_measurable_space T -> U) :
  measurable_fun D f.
Proof. by []. Qed.

#[global] Hint Resolve measurable_fun_discrete : core.

Lemma measurable_fun_discreteT {T U : choiceType} (h : T -> U) :
  measurable_fun [set: discrete_measurable_space T]
    (h : discrete_measurable_space T -> discrete_measurable_space U).
Proof. by []. Qed.

HB.mixin Record isSubPmf {R : realType} {T : choiceType} (mu : T -> R) := {
  subpmf_ge0 : forall x, 0 <= mu x ;
  subpmf_summable : esummable [set: T] (EFin \o mu);
  subpmf_sum_le1 : (esum [set: T] (EFin \o mu) <= 1)%E }.

HB.structure Definition SubPmf {R : realType} {T : choiceType} :=
  {f of @isSubPmf R T f}.

Arguments subpmf_ge0 {R T} _.
Arguments subpmf_sum_le1 {R T} _.

#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: subpmf_ge0] : core.
#[global] Hint Resolve subpmf_summable : core.

Notation "R '.-pmf'  T" := (@SubPmf.type R T) : type_scope.

Lemma subpmf_eqP {R : realType} {T : choiceType} (f1 f2 : R.-pmf T) :
  f1 =1 f2 <-> f1 = f2.
Proof.
split=> [|->] //.
case: f1 => f1 [[]ge0_1 s1 le1_1].
case: f2 => f2 [[]ge0_2 s2 le1_2].
move => /funext /= h.
by subst; do 3 f_equal.
Qed.

Definition measure_of_pmf {R : realType} {T : choiceType} (mu : T -> R)
    (S : set (discrete_measurable_space T)) :=
  \esum_(x in S) (EFin \o mu) x.

Section SubProbability_measure_subpmf.
Context {R : realType} {T : choiceType} (mu : R.-pmf T).

Let P0 : measure_of_pmf mu set0 = 0.
Proof. by rewrite /measure_of_pmf esum_set0. Qed.

Let P_ge0 (S : set (discrete_measurable_space T)) : (0 <= measure_of_pmf mu S)%E.
Proof. by apply: esum_ge0 => x _; rewrite lee_fin. Qed.

Let P_sigma_additive : semi_sigma_additive (measure_of_pmf mu).
Proof.
move=> F _ tF _.
rewrite [X in _ --> X](_ : _ = \sum_(i <oo) measure_of_pmf mu (F i))%E.
  rewrite nneseries_esumT//; apply: esum_bigcup => //=.
    exact: (sub_trivIset (@subsetT _ _)).
  by move=> x; rewrite lee_fin.
by apply: is_cvg_nneseries => n _ _; apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (measure_of_pmf mu)
  P0 P_ge0 P_sigma_additive.

Let P_setT : (measure_of_pmf mu [set: discrete_measurable_space T] <= 1)%E.
Proof. by rewrite /measure_of_pmf esum_setT_discrete; exact: subpmf_sum_le1. Qed.

HB.instance Definition _ :=
  @Measure_isSubProbability.Build _ _ R (measure_of_pmf mu) P_setT.

End SubProbability_measure_subpmf.

Section expectation_measure_of_pmf.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T).

Local Open Scope ereal_scope.

Lemma integral_measure_of_pmf mu (f : T -> \bar R) : (forall x, 0 <= f x) ->
  \int[measure_of_pmf mu]_x f x = \esum_(x in [set: T]) (f x * (mu x)%:E).
Proof.
move=> f0; rewrite -esum_setT_discrete -integral_counting_esum//=.
rewrite -(@integral_measure_of_density _ (discrete_measurable_space T) R
  (@counting (discrete_measurable_space T) R) mu)//=.
move => H; apply: eq_measure_integral => A mA _ /=.
by rewrite /measure_of_density /measure_of_pmf integral_counting_esum.
Qed.

Lemma esummable_integrable mu (A : T -> \bar R) :
  esummable [set: T] (fun x : T => A x * (mu x)%:E)%E <->
  (measure_of_pmf mu).-integrable [set: discrete_measurable_space T] A.
Proof.
rewrite esummableE.
under eq_esum do rewrite abseM abse_EFin (@ger0_norm _ (mu _))//.
rewrite ge0_fin_numE//.
  by rewrite esum_ge0// => x _; rewrite mule_ge0 ?lee_fin ?abse_ge0.
split=> [Amu|/integrableP[_]].
  apply/integrableP; split => //.
  by rewrite integral_measure_of_pmf// => x; rewrite abse_ge0.
by rewrite integral_measure_of_pmf// => x; rewrite abse_ge0.
Qed.

Lemma expectation_pmf mu (f : T -> \bar R) :
  'E_(measure_of_pmf mu)[f] = \esum_(x in [set:T]) (f x * (mu x)%:E).
Proof.
rewrite expectation_def integralE esumE; congr (_ - _).
- rewrite integral_measure_of_pmf//; apply: eq_esum => x _.
  by rewrite !funeposE maxe_pMl ?mul0e// lee_fin.
- rewrite integral_measure_of_pmf//; apply: eq_esum => x _.
  by rewrite !funenegE maxe_pMl ?mul0e ?mulNe// lee_fin.
Qed.

Lemma expectation_pmfEFin mu (g : T -> R) :
  'E_(measure_of_pmf mu) [EFin \o g] = \esum_(x in [set: T]) (g x * mu x)%:E.
Proof. by rewrite expectation_pmf. Qed.

Lemma expectation_pmf0 mu : 'E_(measure_of_pmf mu) [cst 0] = 0.
Proof. by rewrite unlock integral0. Qed.

End expectation_measure_of_pmf.

HB.factory Record uniq_isSubPmf {R : realType} {T : choiceType} (mu : T -> R) := {
  subpmf_ge0 : forall x : T, 0 <= mu x ;
  uniq_subpmf_le1 : forall J, uniq J -> \sum_(j <- J) mu j <= 1 }.

HB.builders Context {R : realType} {T : choiceType} (mu : T -> R)
  & @uniq_isSubPmf R T mu.

Local Lemma pmf_ge0 x : 0 <= mu x.
Proof. exact: subpmf_ge0. Qed.

Local Lemma pmf_summable : esummable [set: T] (EFin \o mu).
Proof.
rewrite /esummable (@le_lt_trans _ _ 1%:E) ?ltey// ge0_esum//.
  by move => ? _; rewrite lee_fin.
rewrite ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin// lee_fin fsbig_finite//=.
rewrite (eq_bigr mu) ?uniq_subpmf_le1//.
by move => ? _; rewrite ger0_norm// subpmf_ge0.
Qed.

Local Lemma pmf_le1 : (esum [set: T] (EFin \o mu) <= 1)%E.
Proof.
rewrite ge0_esum.
  by move => ? _; rewrite lee_fin subpmf_ge0.
rewrite ge_ereal_sup//= => _ [X [finX _]] <-.
by rewrite fsumEFin// lee_fin fsbig_finite//= uniq_subpmf_le1.
Qed.

HB.instance Definition _ := @isSubPmf.Build R T mu pmf_ge0 pmf_summable pmf_le1.

HB.end.

Section pmf_subpmf.
Import MeasurableR.
Context {d} {T : measurableType d} {R : realType} (P : probability T R)
  (X : {RV P >-> R}).

Let pmf_fin_bigcup (J : seq R) : uniq J ->
  \sum_(j <- J) (pmf X j)%:E = P (\bigcup_(j in [set` J]) X @^-1` [set j]).
Proof.
move=> uJ.
rewrite (@measure_fin_bigcup _ _ _ P _ [set` J] (fun j => X @^-1` [set j]))//.
- exact: finite_seq.
- exact: trivIset_preimage1.
- rewrite fsbig_seq//; apply: eq_fsbigr => j _.
  by rewrite /pmf fineK// fin_num_measure.
Qed.

Let pmf_uniq_le1 (J : seq R) : uniq J -> (\sum_(j <- J) pmf X j <= 1)%R.
Proof.
move=> uJ; rewrite -lee_fin -sumEFin pmf_fin_bigcup//.
by rewrite probability_le1//; exact: fin_bigcup_measurable.
Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R R (pmf X) (@pmf_ge0 _ _ _ P X) pmf_uniq_le1.

End pmf_subpmf.

Lemma subpmf_le1 {R : realType} {T : choiceType} (mu : R.-pmf T) x : mu x <= 1.
Proof.
rewrite -lee_fin; apply: le_trans; last exact: subpmf_sum_le1 mu.
by rewrite esum_ge1// => ? _; rewrite lee_fin.
Qed.

Section StdDefs.
Context {R : realType} (T : choiceType).
Implicit Types (mu : R.-pmf T) (A B E : pred T) (f : T -> R).

Definition pmf_prob mu E := fine (\esum_(x in [set: T]) ((E x)%:R * mu x)%:E).

Local Notation "\P_[ mu ] E"     := (pmf_prob mu E).

Definition pmf_cprob mu E A := \P_[mu] [predI E & A] / \P_[mu] A.

Local Notation "\P_[ mu , A ] E" := (pmf_cprob mu A E).

Definition pmf_expectation mu f := fine (\esum_(x in [set: T]) (f x * mu x)%:E).

Definition pmf_cexpectation mu f A :=
  fine (\esum_(x in [set: T]) (f x * \P_[mu, pred1 x] A)%:E).

Definition pmf_esummable mu f := esummable [set: T] (EFin \o (f \* mu)).

End StdDefs.

Notation "\P_[ mu ] E"     := (pmf_prob mu E).
Notation "\P_[ mu , A ] E" := (pmf_cprob mu E A).
Notation "\E_[ mu ] f"     := (pmf_expectation mu f).
Notation "\E_[ mu , A ] f" := (pmf_cexpectation mu f A).
Abbreviation dweight mu := (\P_[mu] predT).

Definition subpmf_sum {R : realType} {T : choiceType} (mu : T -> R) :=
  (forall x, 0 <= mu x) /\ (forall J, uniq J -> \sum_(j <- J) mu j <= 1).

Lemma subpmf_sumP {R : realType} {I : finType} (mu : I -> R) :
  subpmf_sum mu <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof.
split=> -[ ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(le_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= lerDl sumr_ge0.
Qed.

Section pmf_zero.
Context {R : realType} {T : choiceType}.

Definition pmf_zero (x : T) : R := 0.

Let subpmf_zero : subpmf_sum pmf_zero.
Proof. by split=> // J _; rewrite big1 ?ler01. Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R T pmf_zero subpmf_zero.1 subpmf_zero.2.

End pmf_zero.

Lemma lef_pmf_zero {R : realType} {T : choiceType} (mu : R.-pmf T) :
  pmf_zero <=1 mu.
Proof. by move=> x /=; rewrite /pmf_zero. Qed.

Lemma measure_of_pmf_zero {R : realType} {T : choiceType}
    (S : set (discrete_measurable_space T)) :
  measure_of_pmf pmf_zero S = mzero S :> \bar R.
Proof. by rewrite /measure_of_pmf esum1// => x _ /=; rewrite pmf_zeroE. Qed.

Section Restr.
Context {R : realType} {T : choiceType} (p : pred T).

Definition pmf_restr (mu : R.-pmf T) := fun x => if p x then mu x else 0.

Let subpmf_restr (mu : R.-pmf T) : subpmf_sum (pmf_restr mu).
Proof.
split=> [x|J]; first by rewrite /pmf_restr; case: ifP.
move=> eqJ; apply/(@le_trans _ _ (\sum_(j <- J) `|mu j|)).
- apply/ler_sum=> i _; rewrite /pmf_restr; case: ifPn => _ //.
  exact: ler_norm.
- rewrite -lee_fin (le_trans _ (subpmf_sum_le1 mu))//.
  rewrite (@eq_esum _ _ _ _ (fun y => `|(EFin \o mu) y|%E))//=.
    by move=> *; rewrite ger0_norm.
  exact: sum_esum_ge.
Qed.

HB.instance Definition _ (mu : R.-pmf T) := @uniq_isSubPmf.Build R T
  (pmf_restr mu) (subpmf_restr mu).1 (subpmf_restr mu).2.

End Restr.

Lemma measure_of_pmf_restr {R : realType} {T : choiceType} (p : pred T)
    (mu : R.-pmf T)
    (mp : measurable ([set` p] : set (discrete_measurable_space T)))
    (S : set (discrete_measurable_space T)) :
  measure_of_pmf (pmf_restr p mu) S = mrestr (measure_of_pmf mu) mp S.
Proof.
rewrite /mrestr /measure_of_pmf esum_mkcondr; apply: eq_esum => x _ /=.
by rewrite /pmf_restr mem_setE unfold_in (fun_if EFin).
Qed.

Section pr_pmf.
Import MeasurableR.
Context {d} {T : pmeasurableType d} {R : realType} (P : probability T R)
  (X : {dRV P >-> R}).

Local Abbreviation pmfX := (@pmf _ _ _ P X).

Lemma esum_pmf_setT :
  esum [set: R] (EFin \o pmfX) = \esum_(r in range X) (pmfX r)%:E.
Proof.
rewrite (esumID (range X) [set: R] (EFin \o pmfX)).
  by move=> i _; rewrite lee_fin.
rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
by rewrite not_range_pmf0.
Qed.

Lemma esum_pmf_range1 : \esum_(r in range X) (pmfX r)%:E = 1%E.
Proof.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X))//.
transitivity (\esum_(k in dRV_dom X) enum_prob X k).
  apply: eq_esum => k kd/=.
  by rewrite /enum_prob patchE mem_set// /pmf fineK// fin_num_measure.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
  by move=> n _; rewrite /enum_prob patchE; case: ifP.
rewrite eseries_mkcond -[RHS](sum_enum_prob X measurable_set1).
apply: eq_eseriesr => k _; case: ifPn => // kd.
by rewrite /enum_prob patchE (negbTE kd).
Qed.

Lemma esum_pmf_pred (A : set R) :
  esum [set: R] (EFin \o (fun r => (r \in A)%:R * pmfX r))%R =
  \esum_(r in A) (pmfX r)%:E.
Proof.
rewrite [RHS]esum_mkcond; apply: eq_esum => r _.
by case: (r \in A) => /=; rewrite ?mul1r ?mul0r.
Qed.

Lemma pmf_prob_dRV (A : set R) : measurable A ->
  (\P_[pmfX] (mem A))%:E = distribution P X A.
Proof.
move=> mA; rewrite /pmf_prob esum_pmf_pred dRV_esum_pmf_distribution// fineK//.
by rewrite fin_num_measure.
Qed.

End pr_pmf.

Section RestrTheory.
Context {R : realType} {T : choiceType}.

Lemma pmf_restrD (mu : R.-pmf T) (p : pred T) x :
  mu x = pmf_restr p mu x + pmf_restr (predC p) mu x.
Proof. by rewrite /= /pmf_restr !inE; case: ifPn; rewrite (addr0, add0r). Qed.

Lemma supp_pmf_restr (mu : R.-pmf T) (p : pred T) x :
  (x \in supp (pmf_restr p mu)) = (x \in supp mu) && p x.
Proof.
apply/mem_suppP/idP.
- by rewrite /= /pmf_restr; case: ifP=> // _ /mem_suppP ->.
- by case/andP; rewrite /= /pmf_restr => /mem_suppP ? ->.
Qed.

End RestrTheory.

Section DCount.
Context {R : realType} (T : choiceType).
Implicit Types (s : seq T).

Definition pmf_count (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma pmf_count_ge0 s x : 0 <= pmf_count s x.
Proof. by rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Lemma pmf_count_sum_le1 s J : uniq J -> \sum_(i <- J) pmf_count s i <= 1.
Proof.
move=> uqJ; rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivrMr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
have -> : (size s = \sum_(i <- undup s) count_mem i s)%N.
  rewrite -sum1_size -big_undup_iterop_count; apply: eq_bigr => i _.
  by rewrite Monoid.iteropE iter_addn addn0 mul1n.
rewrite [X in (_ <= X)%N](bigID (mem J)) /= -ltnS -addSn.
rewrite ltn_addr //= ltnS -big_filter -[X in (_ <= X)%N]big_filter.
rewrite leq_eqVlt; apply/orP; left; apply/eqP/perm_big.
apply/uniq_perm; rewrite ?filter_uniq ?undup_uniq//.
by move=> x; rewrite !mem_filter mem_undup andbC.
Qed.

Lemma pmf_count_sum_eq1 s : (0 < size s)%N ->
  \sum_(i <- undup s) pmf_count s i = 1.
Proof.
move=> gt0_s; rewrite -mulr_suml -natr_sum.
apply/(mulIf (x := (size s)%:R)); first by rewrite pnatr_eq0 -lt0n.
rewrite mul1r divfK ?pnatr_eq0 -?lt0n//; congr (_%:R).
rewrite -sum1_size -[in RHS]big_undup_iterop_count/=; apply: eq_bigr => i _.
by rewrite Monoid.iteropE iter_addn addn0 mul1n.
Qed.

Lemma esummable_pmf_count s : esummable [set :T] (EFin \o (pmf_count s)).
Proof.
rewrite /esummable (@le_lt_trans _ _ 1%:E) ?ltey// ge0_esum.
  by move => *; rewrite lee_fin.
rewrite ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin // lee_fin fsbig_finite //=.
rewrite (eq_bigr (pmf_count s)).
  by move => ? ?; rewrite ger0_norm ?pmf_count_ge0.
exact/pmf_count_sum_le1.
Qed.

Let subpmf_count s : subpmf_sum (pmf_count s).
Proof. by split; [exact/pmf_count_ge0|exact/pmf_count_sum_le1]. Qed.

HB.instance Definition _ (s : seq T) :=
  @uniq_isSubPmf.Build R T (pmf_count s) (subpmf_count s).1 (subpmf_count s).2.

End DCount.

HB.lock Definition pmf_ret {R : realType} {T : choiceType} (x : T) : R.-pmf T :=
  pmf_count [:: x].
Canonical locked_pmf_ret := Unlockable pmf_ret.unlock.

Section pmf_ret.
Context {R : realType} {T : choiceType}.
Implicit Types (x y : T) (s : seq T).

Lemma pmf_retE x y : pmf_ret x y = (x == y)%:R :> R.
Proof. by rewrite unlock/= /pmf_count/= addn0 divr1. Qed.

Lemma pmf_retxx x : pmf_ret x x = 1 :> R.
Proof. by rewrite pmf_retE eqxx. Qed.

Lemma pmf_ret0 x y : x != y -> (pmf_ret x) y = 0 :> R.
Proof. by rewrite unlock/= /pmf_count /= addn0 divr1 => /negPf ->. Qed.

Lemma in_pmf_ret (t t' : T) : t' \in @supp R _ (pmf_ret t) -> t' = t :> T.
Proof.
rewrite mem_supp unlock/= /pmf_count/= addn0 divr1 pnatr_eq0 eqb0 negbK.
by move/eqP.
Qed.

End pmf_ret.

Lemma measure_of_pmf_ret {R : realType} {T : choiceType} (x : T)
    (S : set (discrete_measurable_space T)) :
  measure_of_pmf (pmf_ret x) S = \d_(x : discrete_measurable_space T) S :> \bar R.
Proof.
rewrite /measure_of_pmf diracE esum_mkcond esum_setT_discrete.
rewrite (eq_esum _ _ (fun y => if x == y then (y \in S)%:R%:E else 0)).
  by move=> y _ /=; rewrite pmf_retE; case: ifPn => yS //; case: ifPn.
by rewrite esum_if_eq_op_set1.
Qed.

Definition pmf_uniform {R : realType} {T : choiceType} (s : seq T) : T -> R :=
  pmf_count (undup s).

Lemma pmf_uniformE {R : realType} {T : choiceType} (s : seq T) x :
  (pmf_uniform s) x = (x \in s)%:R / (size (undup s))%:R :> R.
Proof.
by rewrite /pmf_uniform /pmf_count count_uniq_mem ?(mem_undup, undup_uniq).
Qed.

Section Flip.
Context {R : realType}.

Local Abbreviation clamp := (@clamp R 0 1).

Definition pmf_flip (xt : R) := fun b => if b then clamp xt else 1 - clamp xt.

Let subpmf_flip xt : subpmf_sum (pmf_flip xt).
Proof.
apply/subpmf_sumP; split=> [b|].
  by case: b; rewrite ?subr_ge0 clamp_gele.
by rewrite /index_enum !unlock /= addr0 addrC subrK.
Qed.

HB.instance Definition _ (xt : R) :=
  @uniq_isSubPmf.Build R _ (pmf_flip xt) (subpmf_flip xt).1 (subpmf_flip xt).2.

End Flip.

Section Bind.
Context {R : realType} {T U : choiceType} (f : T -> R.-pmf U) (mu : R.-pmf T).

Definition pmf_bind (y : U) := fine (\esum_(x in [set:T]) (mu x * f x y)%:E).

Let pmf_bind_ge0 x : 0 <= fine (\esum_(x0 in [set: T]) (mu x0 * f x0 x)%:E).
Proof.
by rewrite fine_ge0// esum_ge0//= => t _; rewrite lee_fin mulr_ge0.
Qed.

Let subpmf_bind : subpmf_sum pmf_bind.
Proof.
split=> [x|J uqJ]; first exact: pmf_bind_ge0.
rewrite /pmf_bind -lee_fin.
have hpos x i : (0 <= (mu x * f x i)%:E)%E.
  by rewrite EFinM mule_ge0//= lee_fin.
apply: le_trans; first exact: sum_esum_ge.
apply/(le_trans _ (subpmf_sum_le1 mu)).
apply/(le_trans (le_esum_fine _ _ hpos)).
rewrite exchange_esum// le_esum// => i _.
under eq_esum do rewrite EFinM.
rewrite esumZ ?lee_fin// => [?|]; first by rewrite lee_fin.
rewrite muleC gee_pMl ?lee_fin//; last exact: subpmf_sum_le1.
rewrite (eq_esum _ _ (fun x  => `|(EFin \o f i) x|%E)).
  by move=> *; rewrite gee0_abs// lee_fin.
by rewrite -esummableE.
Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R U pmf_bind subpmf_bind.1 subpmf_bind.2.

End Bind.

Notation "\bind_ ( i <- d ) E" := (pmf_bind (fun i => E) d).

Section BindTheory.
Context {R : realType} {T U : choiceType}.
Implicit Types (f g : T -> R.-pmf U) (mu nu : R.-pmf T).

Lemma pmf_bind_zero f : \bind_(x <- pmf_zero) f x =1 pmf_zero.
Proof.
by move=> x /=; rewrite /pmf_bind esum1//  => ? ?; rewrite /= EFinM mul0e.
Qed.

Lemma pmf_ret_bind f v : \bind_(y <- pmf_ret v) f y =1 f v.
Proof.
move=> y; rewrite /pmf_bind (esumID [set v]).
  by move=> *; rewrite lee_fin mulr_ge0.
rewrite setI1//= in_setT esum_set1 esum1/=.
  by move => i [? /eqP h]; rewrite pmf_ret0 ?mul0r//= eq_sym.
by rewrite pmf_retxx addr0 mul1r.
Qed.

Lemma pmf_bind_ret mu : \bind_(t <- mu) (pmf_ret t) =1 mu.
Proof.
move=> v /=; rewrite /pmf_bind.
rewrite (esumID ([set v]%classic)).
  by move=> ? ; rewrite lee_fin mulr_ge0.
rewrite setI1 in_setT esum_set1 esum1/=.
  by move => i [? /eqP h]; rewrite pmf_ret0 ?mulr0.
by rewrite pmf_retxx mulr1 addr0.
Qed.

Lemma supp_eq_pmf_bind f g mu nu : {in supp mu, f =2 g} -> mu =1 nu ->
  pmf_bind f mu =1 pmf_bind g nu.
Proof.
move=> eq_f eq_mu y; rewrite /pmf_bind.
rewrite [X in fine X = _](_ : _ = \esum_(x in [set: T]) (nu x * g x y)%:E)//.
apply/eq_esum => x _; rewrite -eq_mu !EFinM.
case/boolP : (x \in supp mu) => [/eq_f ->//|].
by move/memNsuppP => ->; rewrite !mul0e.
Qed.

Lemma esummable_pmf_bind_elt (f : T -> R.-pmf U) (mu : R.-pmf T) y :
  esummable [set: T] (fun x => (mu x * f x y)%:E).
Proof.
rewrite /esummable.
under eq_esum do rewrite EFinM.
apply: esummableMr => //.
  exists 1%E => // => i _.
  by rewrite gee0_abs lee_fin// subpmf_le1.
exact: subpmf_summable.
Qed.

Lemma pmf_bind_is_fin_num (f : T -> R.-pmf U) (mu : R.-pmf T) y :
  \esum_(x in [set: T]) (mu x * f x y)%:E \is a fin_num.
Proof.
rewrite esum_abse.
  by move => ?; rewrite mulr_ge0.
by rewrite -esummableE; exact: esummable_pmf_bind_elt.
Qed.

Lemma EFin_pmf_bind (f : T -> R.-pmf U) (mu : R.-pmf T) y :
  (pmf_bind f mu y)%:E = \esum_(x in [set: T]) (mu x * f x y)%:E.
Proof. by rewrite /pmf_bind fineK// ?pmf_bind_is_fin_num. Qed.

Lemma supp_le_pmf_bind f g mu : {in supp mu, f <=2 g} ->
  \bind_(i <- mu) f i <=1 \bind_(i <- mu) g i.
Proof.
move=> le_f y; rewrite /pmf_bind fine_le ?pmf_bind_is_fin_num//.
apply: le_esum => x ?.
case/boolP : (x \in supp mu) => [/le_f ?|].
rewrite !EFinM lee_pmul //= lee_tofin //=.
by move/memNsuppP => ->; rewrite !EFinM !mul0e.
Qed.

Lemma le_pmf_bind f mu nu : mu <=1 nu ->
  \bind_(i <- mu) f i <=1 \bind_(i <- nu) f i.
Proof.
move=> le_mu y; rewrite !/pmf_bind fine_le ?pmf_bind_is_fin_num//.
apply: le_esum => x ?.
by rewrite !EFinM lee_pmul //= lee_tofin.
Qed.

Lemma supp_le_pmf_bind2 f g mu nu : mu <=1 nu ->
  {in supp mu, forall x, f x <=1 g x} ->
  \bind_(x <- mu) f x <=1 \bind_(x <- nu) g x.
Proof.
move=> le_mu le_fg x.
exact/(le_trans (supp_le_pmf_bind le_fg _))/le_pmf_bind.
Qed.

Lemma pmf_bindC (mu : R.-pmf T) (nu : R.-pmf U) y :
  (\bind_(_ <- mu) nu) y = dweight mu * nu y.
Proof.
rewrite /pmf_bind.
under eq_esum do rewrite mulrC EFinM.
rewrite esumZ; first by move=> *; rewrite lee_fin.
rewrite fineM// [in LHS]mulrC [in RHS]/pmf_prob.
by under [in RHS]eq_esum do rewrite mul1r.
Qed.

Lemma supp_pmf_bind f mu y : y \in supp (\bind_(x <- mu) f x) ->
  exists2 x, x \in supp mu & f x y != 0.
Proof.
rewrite mem_supp /= /pmf_bind => nz_pmf_bind.
have /esum_neq0[x _] : \esum_(x in [set: T]) (mu x * f x y)%:E != 0.
  by apply: contra nz_pmf_bind => /eqP ->; rewrite fine0.
rewrite eqe mulf_eq0 negb_or => /andP[nz_mu nz_f].
by exists x.
Qed.

Let esum_eq0_pmf_bind_elt (f : T -> R.-pmf U) (mu : R.-pmf T) x y:
  fine (\esum_(x in [set: T]) (mu x * f x y)%:E) = 0 ->
  (mu x * f x y)%:E = 0.
Proof.
move=> h0.
apply /(@esum_eq0P _ _  [set: T] (fun i => (mu i * f i y)%:E)) => //.
+ by move=> i _; rewrite lee_fin mulr_ge0.
+ by rewrite -(fineK (pmf_bind_is_fin_num f mu y)) h0.
Qed.

Lemma pmf_bind_mem_supp f mu x y :
  x \in supp mu -> f x y != 0 -> y \in supp (pmf_bind f mu).
Proof.
move=> /mem_suppP /eqP mux nz_fxy.
apply/memNsuppP => /(esum_eq0_pmf_bind_elt x).
by move=> /eqP; rewrite eqe mulf_eq0 (negbTE nz_fxy) orbF; exact/negP.
Qed.

Lemma pmf_bind_eq0 (f : T -> U) mu y :
  {in supp mu, forall x, f x != y} -> (\bind_(x <- mu) pmf_ret (f x)) y = 0.
Proof.
move=> h /=; rewrite /pmf_bind.
rewrite esum1// => x _.
case/boolP : (x \in supp mu) => [/h|/memNsuppP ->].
- by rewrite pmf_retE => /negbTE ->; rewrite mulr0.
- by rewrite mul0r.
Qed.

Lemma eq0_pmf_bind (mu : R.-pmf T) (F : T -> R.-pmf U ) y :
  (\bind_(x <- mu) F x) y = 0 -> forall x, x \in supp mu -> F x y = 0.
Proof.
move=> /esum_eq0_pmf_bind_elt h x /mem_suppP /eqP mu_x.
by move/eqP : (h x); rewrite eqe mulf_eq0 (negbTE mu_x) /= => /eqP.
Qed.

End BindTheory.

Definition pmf_bindr {R : realType} {T : choiceType} (f : T -> R.-pmf T) :=
  fun d => \bind_(x <- d) f x.

Definition pmf_iter {R : realType} {T : choiceType} n (f : T -> R.-pmf T) :=
  fun a => (iter n (pmf_bindr f) (pmf_ret a)).

Section MeasureOfPmf_Bind.
Context {R : realType} {T U : choiceType}.

Local Open Scope ereal_scope.

Lemma measure_of_pmf_bind (mu : R.-pmf T) (nu : T -> R.-pmf U)
    (S : set (discrete_measurable_space U)) :
  measure_of_pmf (pmf_bind nu mu) S =
  \int[measure_of_pmf mu]_x measure_of_pmf (nu x) S.
Proof.
rewrite integral_measure_of_pmf// /measure_of_pmf.
under eq_esum do rewrite /= EFin_pmf_bind.
rewrite exchange_esum.
  by move=> i j; rewrite lee_fin mulr_ge0.
apply: eq_esum => x _.
by rewrite muleC -esumZ //= => y _; rewrite lee_fin.
Qed.

Lemma measurable_measure_of_pmf (nu : T -> R.-pmf U) :
  measurable_fun [set: discrete_measurable_space T]
    (fun x => (measure_of_pmf (nu x) : giry (discrete_measurable_space U) R)).
Proof. by []. Qed.

Lemma measure_of_pmf_bind_giry (mu : R.-pmf T) (nu : T -> R.-pmf U)
    (S : set (discrete_measurable_space U)) :
  measure_of_pmf (pmf_bind nu mu) S =
  giry_bind (measure_of_pmf mu) (measurable_measure_of_pmf nu) S.
Proof.
rewrite /giry_bind/= giry_int_map//=.
  exact: measurable_giry_ev.
exact: measure_of_pmf_bind.
Qed.

End MeasureOfPmf_Bind.

Section Pmf_BindPmf_Bind.
Context {R : realType} {T U V : choiceType}
  (f1 : T -> R.-pmf U) (f2 : U -> R.-pmf V).

Lemma pmf_bind_pmf_bind (mu : R.-pmf T) :
  \bind_(x <- \bind_(y <- mu) f1 y) f2 x =1
  \bind_(y <- mu) (\bind_(x <- f1 y) f2 x).
Proof.
move=> z /=; rewrite /pmf_bind.
pose S y x := mu x * f1 x y * f2 y z.
rewrite (eq_esum _ _ (fun y => \esum_(x in [set: T]) (S y x)%:E)).
  move=> y _; rewrite EFinM EFin_pmf_bind//.
  rewrite muleC -esumZ ?lee_fin// => [? _|].
    by rewrite EFinM lee_fin mulr_ge0.
  by apply eq_esum => *; rewrite -EFinM mulrC.
rewrite (eq_esum _ _ (fun x => \esum_(y in [set: U]) (S y x)%:E)).
  move=> x _; rewrite EFinM EFin_pmf_bind//.
  rewrite -esumZ ?lee_fin// => [? _|].
    by rewrite EFinM lee_fin mulr_ge0.
  by apply eq_esum => * ; rewrite -EFinM mulrA.
by rewrite exchange_esum// => ? ?; rewrite /S EFinM lee_fin ?mulr_ge0.
Qed.

End Pmf_BindPmf_Bind.

Section Pmf_BindAlg.
Context {R : realType} {T U : choiceType} (mu mu1 mu2 : R.-pmf T).

Lemma pmf_bind_additive (f : T -> R.-pmf U) z :
  (forall x, mu x = mu1 x + mu2 x) ->
  (\bind_(x <- mu) f x) z = (\bind_(x <- mu1) f x) z + (\bind_(x <- mu2) f x) z.
Proof.
move=> muD /=; rewrite /pmf_bind.
under eq_esum do rewrite muD mulrDl EFinD.
rewrite esumD; [by move=> ? ?; rewrite /S EFinM lee_tofin ?mulr_ge0..|].
by rewrite fineD//= pmf_bind_is_fin_num.
Qed.

End Pmf_BindAlg.

Section pmf_lim.
Context {R : realType} (T : choiceType).
Implicit Types (f g : nat -> R.-pmf T).

Import numFieldNormedType.Exports.

Definition pmf_lim f : T -> R :=
  fun x => fine (limn_einf (fun n => (f n x)%:E)).

Local Lemma pmf_lim_ge0' f x : (0 <= limn_einf (fun n => (f n x)%:E))%E.
Proof.
rewrite limn_einf_lim; apply: lime_ge; first exact: is_cvg_einfs.
apply: nearW => n; apply: le_ereal_inf_tmp => _ [m _] <-.
by rewrite lee_fin.
Qed.

Local Lemma pmf_lim_le1' f x : (limn_einf (fun n => (f n x)%:E) <= 1%:E)%E.
Proof.
rewrite limn_einf_lim; apply: lime_le; first exact: is_cvg_einfs.
apply: nearW => n; apply: (@le_trans _ _ (f n x)%:E); first exact: ge_einfs.
by rewrite lee_fin subpmf_le1.
Qed.

Let limn_einf_fin_num f x : limn_einf (fun n => (f n x)%:E) \is a fin_num.
Proof.
have h0 : (0 <= limn_einf (fun n => (f n x)%:E))%E by exact: pmf_lim_ge0'.
rewrite ge0_fin_numE//.
by apply: le_lt_trans; [exact: pmf_lim_le1' |exact: ltry].
Qed.

Lemma EFin_pmf_lim f x : (pmf_lim f x)%:E = limn_einf (fun n => (f n x)%:E).
Proof. by rewrite /lim fineK// fin_liminf. Qed.

Let subpmf_lim f : subpmf_sum (pmf_lim f).
Proof.
split=> [x|J uqJ]; first by rewrite /lim; exact/fine_ge0/pmf_lim_ge0'.
rewrite -lee_fin -sumEFin.
under eq_bigr => j _ do rewrite EFin_pmf_lim limn_einf_lim.
have ndE j : nondecreasing_seq (einfs (fun n => (f n j)%:E)).
  exact: nondecreasing_einfs.
have finE j : limn (einfs (fun n => (f n j)%:E)) \is a fin_num.
  by rewrite -limn_einf_lim limn_einf_fin_num.
rewrite (ereal_nondecreasing_sum_limn ndE finE); apply: lime_le.
  apply: ereal_nondecreasing_is_cvgn => n m nm.
  by apply: lee_sum => j _; exact: ndE.
apply: nearW => n; apply: (@le_trans _ _ (\sum_(j <- J) (f n j)%:E)).
  by apply: lee_sum => j _; exact: ge_einfs.
rewrite sumEFin; apply: le_trans (subpmf_sum_le1 (f n)).
exact: sum_esum_ge.
Qed.

HB.instance Definition _ f :=
  @uniq_isSubPmf.Build R T (pmf_lim f) (subpmf_lim f).1 (subpmf_lim f).2.

Lemma pmf_limE f : nondecreasing_fun (f : _ -> _ -> R) ->
  forall x, pmf_lim f x = fine (limn (fun n => (f n x)%:E)).
Proof.
move=> ndf x /=; rewrite /pmf_lim is_cvg_limn_einfE//=.
apply: ereal_nondecreasing_is_cvgn => m n mn.
by rewrite lee_fin; exact/lefP/ndf.
Qed.

Lemma EFin_pmf_lim_limn f : nondecreasing_fun (f : _ -> _ -> R) ->
  forall x, (pmf_lim f x)%:E = limn (fun n => (f n x)%:E).
Proof.
move=> ndf x; rewrite EFin_pmf_lim is_cvg_limn_einfE//.
apply: ereal_nondecreasing_is_cvgn => m n mn.
by rewrite lee_fin; exact/lefP/ndf.
Qed.

Lemma EFin_pmf_lim_sup f : nondecreasing_fun (f : _ -> _ -> R) ->
  forall x, (pmf_lim f x)%:E = ereal_sup (range (fun n => (f n x)%:E)).
Proof.
move=> ndf x.
rewrite (EFin_pmf_lim_limn ndf) -sup_range_lim// => m n mn.
by rewrite lee_fin; exact/lefP/ndf.
Qed.

End pmf_lim.

Notation "\lim_ ( n ) E" := (pmf_lim (fun n => E)).

Section Pmf_LimTheory.
Context {R : realType} {T U : choiceType}.
Implicit Types (f g : nat -> R.-pmf T) (h : T -> R.-pmf U) (mu : R.-pmf T).

Lemma pmf_limC mu : \lim_(n) mu =1 mu.
Proof. by move=> x /=; rewrite /pmf_lim limn_einf_cst. Qed.

Lemma pmf_lim_bump f : \lim_(n) f n.+1 =1 pmf_lim f.
Proof.
by move=> x /=; rewrite /pmf_lim (limn_einf_shiftS (fun n => (f n x)%:E)).
Qed.

Lemma pmf_lim_lift f p : \lim_(n) f (n + p)%N =1 pmf_lim f.
Proof.
by move=> x /=; rewrite /pmf_lim (limn_einf_shift_new (fun n => (f n x)%:E) p).
Qed.

Lemma pmf_lim_ge0 f x : 0 <= pmf_lim f x.
Proof. by []. Qed.

Lemma pmf_lim_le1 f x : pmf_lim f x <= 1.
Proof. by rewrite -lee_fin EFin_pmf_lim; exact: pmf_lim_le1'. Qed.

Lemma le_pmf_lim f g : (forall n, f n <=1 g n) -> pmf_lim f <=1 pmf_lim g.
Proof.
move=> le x; rewrite -lee_fin !EFin_pmf_lim !limn_einf_lim.
apply: lee_lim; [exact: is_cvg_einfs..|].
apply: nearW => n; apply: le_ereal_inf_tmp => _ [m /= nm] <-.
by apply: (@le_trans _ _ ((f m x)%:E)); [exact: ge_einfs|rewrite lee_fin].
Qed.

Lemma eq_pmf_lim f g : (forall n, f n =1 g n) -> pmf_lim f =1 pmf_lim g.
Proof.
move=> eq_fg x.
apply/eqP; rewrite eq_le; apply/andP.
by split; apply: le_pmf_lim =>  ??; rewrite eq_fg.
Qed.

Lemma leub_pmf_lim f mu : (forall n, f n <=1 mu) -> pmf_lim f <=1 mu.
Proof. by move => le x; rewrite -(pmf_limC mu x) le_pmf_lim. Qed.

Lemma pmf_lim_ub f k : nondecreasing_fun (f : nat -> T -> R) -> f k <=1 pmf_lim f.
Proof.
move=> hf x; rewrite -lee_fin (EFin_pmf_lim_limn hf).
apply: lime_ge.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  by rewrite lee_fin; exact/lefP/hf.
near do (rewrite lee_fin; apply/lefP/hf).
exact: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

End Pmf_LimTheory.

Section Pmf_BindPmf_Lim.
Context {R : realType} {T U : choiceType}.

Implicit Types (f : (R.-pmf T)^nat) (h : T -> R.-pmf R).

Lemma pmf_limM_sup f (hf : nondecreasing_fun (f : _ -> _ -> _)) (c : R) x :
  0 <= c ->
  (pmf_lim f x * c)%:E = ereal_sup (range (fun n => (f n x * c)%:E)).
Proof.
move=> c0.
rewrite EFinM (EFin_pmf_lim_sup hf) muleC.
rewrite (@ge0_ereal_supZl_range R T (fun t n => (f n t)%:E)) //=.
  by move=> t n; rewrite lee_fin.
congr ereal_sup; apply/seteqP; split.
- by move=> ? [x0 ?]; rewrite -EFinM mulrC=> <- //=; exists x0.
- by move=> ? [x0 ?]; rewrite mulrC EFinM => <- //=; exists x0.
Qed.

Lemma pmf_bind_lim f h : nondecreasing_fun (f : _ -> _ -> _) ->
  \bind_(x <- pmf_lim f) h x =1 \lim_(n) (\bind_(x <- f n) h x).
Proof.
move=> ndf y; apply: EFin_inj.
have nd : nondecreasing_fun (fun n => \bind_(i <- f n) h i).
  move=> n m hnm; apply/lefP => x.
  by apply: le_pmf_bind => ?; exact/lefP/ndf.
rewrite EFin_pmf_bind (EFin_pmf_lim_sup nd).
under eq_esum => x _ do rewrite (pmf_limM_sup ndf)//.
rewrite (@exchange_esum_ereal_sup _ _ (fun x n => (f n x * h x y)%:E))/=.
- by move=> t n; rewrite lee_fin mulr_ge0.
- by move=> x n m nm; rewrite lee_fin ler_wpM2r//; exact/lefP/ndf.
congr ereal_sup; apply/seteqP; split.
- by move=> ? [x0 ?]; rewrite -EFin_pmf_bind => <- //=; exists x0.
- by move=> ? [x0 ?]; rewrite EFin_pmf_bind => <- //=; exists x0.
Qed.

End Pmf_BindPmf_Lim.

Section Pmf_LimPmf_Bind.
Context {R : realType} {T U : choiceType} (f : nat -> T -> R.-pmf U).
Hypothesis hmono : forall x n m, (n <= m)%N -> f n x <=1 f m x.

Lemma pmf_lim_bind (mu : R.-pmf T) :
  \lim_(n) \bind_(x <- mu) (f n x) =1 \bind_(x <- mu) \lim_(n) (f n x).
Proof.
have nd1 y : nondecreasing_fun (f ^~ y : _ -> _ -> _).
  by move=> n m hnm; apply/lefP => x; exact: hmono.
have nd2 : nondecreasing_fun (fun n => \bind_(i <- mu) f n i).
  move=> n m hnm; apply/lefP => x.
  by apply: supp_le_pmf_bind => z _; exact: hmono.
move=> z; apply: EFin_inj.
rewrite (EFin_pmf_lim_sup nd2) EFin_pmf_bind.
under eq_esum => t _ do rewrite mulrC (pmf_limM_sup (nd1 t))//.
rewrite (@exchange_esum_ereal_sup _ _ (fun t n => (f n t z * mu t)%:E))/=.
- by move=> t n; rewrite lee_fin mulr_ge0.
- by move=> n m nm t; rewrite lee_fin ler_wpM2r// hmono.
congr ereal_sup; apply/seteqP; split.
- move=> ? [x0 ?]; rewrite EFin_pmf_bind => <-//=; exists x0 => //=.
  by under eq_esum do rewrite  mulrC.
- move=> ? [x0 ?]; under eq_esum do rewrite mulrC.
  by move => <- //=; exists x0 => //=; rewrite -EFin_pmf_bind.
Qed.

End Pmf_LimPmf_Bind.

Section Pmf_LimPmf_Lim.
Context {R : realType} {T : choiceType} (f : nat -> nat -> R.-pmf T).
Hypotheses (hmono1 : forall k n1 n2, (n1 <= n2)%N -> f n1 k <=1 f n2 k)
           (hmono2 : forall k n1 n2, (n1 <= n2)%N -> f k n1 <=1 f k n2).

Local Lemma dhomo_apply2 : nondecreasing_fun (fun n => f n n : _ -> R).
Proof.
move=> n m hnm; apply/lefP => x.
apply/le_trans.
  exact/hmono1/hnm.
exact: hmono2.
Qed.

Lemma leub_pmf_lim_pmf_lim1 : \lim_(n) pmf_lim (f n) <=1 \lim_(n) f n n.
Proof.
apply: leub_pmf_lim => n; apply: leub_pmf_lim => m x.
apply: (@le_trans _ _ (f (maxn n m) (maxn n m) x)).
  apply: (@le_trans _ _ (f (maxn n m) m x)).
  - by rewrite hmono1// leq_maxl.
  - by rewrite hmono2// leq_maxr.
by rewrite pmf_lim_ub//; exact : dhomo_apply2.
Qed.

Lemma pmf_lim_pmf_lim_ub1 : \lim_(n) (f n n) <=1 \lim_(n) \lim_(m) f n m.
Proof.
apply: leub_pmf_lim => n x; apply: (@le_trans _ _ (pmf_lim (f n) x)).
- apply: pmf_lim_ub => ? ? ?.
  by apply/lefP => ?; exact: hmono2.
- apply: pmf_lim_ub => ? ? ?.
  by apply/lefP => ?; apply le_pmf_lim => ? ?; exact: hmono1.
Qed.

Lemma leub_pmf_lim_pmf_lim2 : \lim_(m) (\lim_(n) (f n m)) <=1 \lim_(n) f n n.
Proof.
apply: leub_pmf_lim => n; apply: leub_pmf_lim => m x.
apply: (@le_trans _ _ (f (maxn n m) (maxn n m) x)).
  apply: (@le_trans _ _ (f (maxn n m) n x)).
  - by rewrite hmono1// leq_maxr.
  - by rewrite hmono2// leq_maxl.
by apply: pmf_lim_ub; exact : dhomo_apply2.
Qed.

Lemma pmf_lim_pmf_lim_ub2 : \lim_(n) (f n n) <=1 \lim_(m) (\lim_(n) f n m).
Proof.
apply: leub_pmf_lim => n x; apply: (@le_trans _ _ (pmf_lim (fun k => f k n) x)).
- apply: pmf_lim_ub => ? ? ?.
  by apply/lefP => ?; exact: hmono1.
- apply: pmf_lim_ub => ? ? ?.
  by apply/lefP => y; apply le_pmf_lim => ? ?; exact: hmono2.
Qed.

Lemma pmf_lim_pmf_lim :
  \lim_(n) (\lim_(m) (f n m)) =1 \lim_(m) (\lim_(n) f n m).
Proof.
move=> x; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (le_trans (leub_pmf_lim_pmf_lim1 x) (pmf_lim_pmf_lim_ub2 x)).
- exact: (le_trans (leub_pmf_lim_pmf_lim2 x) (pmf_lim_pmf_lim_ub1 x)).
Qed.

End Pmf_LimPmf_Lim.

Section pmf_bind_pmf_lim_diag.
Context {R : realType} {T U : choiceType}
  (d : (R.-pmf T)^nat) (h : nat -> T -> R.-pmf R).
Hypotheses (hd : nondecreasing_fun (d : nat -> _ -> R))
           (Hmono: forall k n1 n2, (n1 <= n2)%N -> h n1 k <=1 h n2 k).

Lemma nondecreasing_pmf_bind (nmu : nat -> R.-pmf T) :
  nondecreasing_fun (nmu : nat -> _ -> R) ->
  nondecreasing_fun (fun n => \bind_(i <- nmu n) h n i).
Proof.
move=> hnmu n m hnm; apply/lefP => x; apply: supp_le_pmf_bind2.
  by move=> ?; exact/lefP/hnmu.
by move=> ? ? ?; exact: Hmono.
Qed.

Let pmf_bind_pmf_lim_diag_n n :
  \bind_(x <- d n) (\lim_(n) (h n x)) <=1 \lim_(n) (\bind_(x <- d n) h n x).
Proof.
move=> u; rewrite -(pmf_lim_bind Hmono); apply: leub_pmf_lim => m w.
apply: (@le_trans _ _ ((\bind_(i <- d (maxn m n)) h (maxn m n) i) w)).
  apply: supp_le_pmf_bind2.
    by move=> x; exact/lefP/hd/leq_maxr.
  by move=> ? _; apply: Hmono; exact: leq_maxl.
exact: (@pmf_lim_ub _ _ (fun n => \bind_(x <- d n) h n x) (maxn m n)
  (nondecreasing_pmf_bind hd)).
Qed.

Lemma pmf_bind_pmf_lim_diag :
  \bind_(x <- \lim_(n) d n) (\lim_(n) (h n x)) =1
  \lim_(n) (\bind_(x <- d n) h n x).
Proof.
move=> z; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite pmf_bind_lim//; apply: leub_pmf_lim => n.
  exact: pmf_bind_pmf_lim_diag_n.
apply: leub_pmf_lim => n; apply: supp_le_pmf_bind2.
  exact: (@pmf_lim_ub _ _ d n hd).
move=> x _; apply: pmf_lim_ub => ? ? ?.
by apply/lefP => ?; exact: Hmono.
Qed.

End pmf_bind_pmf_lim_diag.

Section Marginals.
Context {R : realType} {T U : choiceType} (h : T -> U) (mu : R.-pmf T).

Definition pmf_margin : R.-pmf U := \bind_(x <- mu) (pmf_ret (h x)).

End Marginals.

Section MarginalsTh.
Context {R : realType} {T U V : choiceType}.

Lemma pmf_marginE (mu : R.-pmf T) (f : T -> U) y :
  (pmf_margin f mu) y = fine (\esum_(x in [set: T]) ((f x == y)%:R * mu x)%:E).
Proof.
by congr fine; apply/eq_esum => x _; rewrite mulrC pmf_retE.
Qed.

Lemma pmf_bind_margin (mu : R.-pmf T) (f : T -> U) (g : U -> R.-pmf V):
  \bind_(u <- pmf_margin f mu) g u =1 \bind_(t <- mu) (g (f t)).
Proof.
move=> x; rewrite pmf_bind_pmf_bind; apply: supp_eq_pmf_bind=> //.
by move=> y _ z /=; rewrite pmf_ret_bind.
Qed.

Lemma pmf_margin_bind (mu : R.-pmf T) (f : U -> V) (g : T -> R.-pmf U):
  pmf_margin f (\bind_(t <- mu) g t) =1 \bind_(t <- mu) (pmf_margin f (g t)).
Proof. exact/pmf_bind_pmf_bind. Qed.

Lemma pmf_margin_ret (t : T) (f : T -> U):
  pmf_margin f (pmf_ret t) =1 pmf_ret (f t) :> R.-pmf U.
Proof. exact/pmf_ret_bind. Qed.

End MarginalsTh.

Lemma measure_of_pmf_margin {R : realType} {T U : choiceType} (h : T -> U)
    (mu : R.-pmf T) (S : set (discrete_measurable_space U)) :
  measure_of_pmf (pmf_margin h mu) S
    = giry_map (measurable_fun_discreteT h) (measure_of_pmf mu) S.
Proof.
rewrite /pmf_margin measure_of_pmf_bind.
under eq_integral do rewrite measure_of_pmf_ret diracE.
by rewrite /giry_map/= /pushforward -(setIT (h @^-1` S)) -integral_indic.
Qed.

Abbreviation pmf1 mu := (pmf_margin fst mu).
Abbreviation pmf2 mu := (pmf_margin snd mu).

Section DSwap.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Definition pmf_swap : R.-pmf (B * A)%type :=
  pmf_margin (fun xy => (xy.2, xy.1)) mu.

End DSwap.

Section DSwapCoreTheory.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Lemma pmf_swapE xy : pmf_swap mu xy = mu (xy.2, xy.1).
Proof.
rewrite /pmf_swap/= /= /pmf_bind (esumID [set (xy.2, xy.1)]).
  by move=> ? ?; rewrite lee_fin mulr_ge0.
rewrite setI1 //= in_setT esum_set1 esum1 //=.
  move=> ab [_ /eqP h] /=.
  rewrite pmf_ret0 ?mulr0 //.
  apply: contra h => /eqP <-/=.
  by rewrite -surjective_pairing.
by case: xy => x y /=; rewrite pmf_retxx mulr1 addr0.
Qed.

End DSwapCoreTheory.

Section DSwapTheory.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Lemma pmf_swapK : pmf_swap (pmf_swap mu) =1 mu.
Proof. by case=> x y; rewrite !pmf_swapE. Qed.

Lemma supp_pmf_swap xy : (xy.2, xy.1) \in supp mu ->
  xy \in supp (pmf_swap mu).
Proof. by move=> h; apply/mem_suppP; rewrite pmf_swapE; exact/memNsuppP. Qed.

Lemma pmf1_swap : pmf1 (pmf_swap mu) =1 pmf2 mu.
Proof.
move=> z; rewrite /pmf_margin [LHS]pmf_bind_pmf_bind => /=.
by apply/supp_eq_pmf_bind => // -[x y] _ t /=; rewrite pmf_ret_bind.
Qed.

Lemma pmf2_swap : pmf2 (pmf_swap mu) =1 pmf1 mu.
Proof.
move=> z; rewrite /pmf_margin [LHS]pmf_bind_pmf_bind.
by apply/supp_eq_pmf_bind => // -[x y] _ t /=; rewrite pmf_ret_bind.
Qed.

End DSwapTheory.

Section DFst.
Context {R : realType} {T U : choiceType}.

Lemma pmf1E (mu : R.-pmf (T * U)%type) x :
  pmf1 mu x = fine (\esum_(y in [set: U]) (mu (x, y))%:E).
Proof.
rewrite /pmf_margin /pmf_bind; congr fine.
rewrite (esumID [set z : T * U | z.1 = x])/=.
  by move=> z _; rewrite lee_fin mulr_ge0.
rewrite [X in _ + X]esum1 ?adde0.
  by move=> z [_ /= /eqP zx]; rewrite pmf_ret0 ?mulr0.
rewrite (reindex_esum [set: U] _ (fun y => (x, y))).
  split => //.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z [_ /= zx]; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
by apply: eq_esum => y _ /=; rewrite pmf_retxx mulr1.
Qed.

Lemma esummable_fst (mu : R.-pmf (T * U)%type) x :
  esummable [set: U] (fun y => (mu (x, y))%:E).
Proof.
rewrite /esummable; apply: le_lt_trans (@subpmf_summable _ _ mu).
rewrite -(reindex_esum [set:U] [set z : T * U | z.1 = x]
  (fun y => (x, y)) (fun z => (`|(mu z)%:E|)%E)).
  split => //.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z /= zx; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
by apply: subset_esum => //= z _; rewrite lee_tofin // mulr_ge0.
Qed.

End DFst.

Section DSnd.
Context {R : realType} {T U : choiceType}.

Lemma pmf2E (mu : R.-pmf (T * U)%type) y :
  pmf2 mu y = fine (esum [set:T] (fun x => (mu (x, y))%:E)).
Proof.
by rewrite -pmf1_swap pmf1E; congr fine; apply/eq_esum=> x; rewrite pmf_swapE.
Qed.

Lemma esummable_snd (mu : R.-pmf (T * U)%type) y :
  esummable [set: T] (fun x => (mu (x, y))%:E).
Proof.
have := esummable_fst (pmf_swap mu) y; apply/eq_esummable.
by move=> x /=; rewrite pmf_swapE.
Qed.

End DSnd.

Section pmf_esummable_lemmas.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T).

Lemma pmf_esummable_cst mu c : pmf_esummable mu (cst c).
Proof.
have : esummable setT (fun x => c%:E * (mu x)%:E)%E.
  by apply: esummableZl => //; exact: subpmf_summable.
by apply/eq_esummable => x /= _; rewrite EFinM.
Qed.

Lemma pmf_esummableZ mu c F : pmf_esummable mu F -> pmf_esummable mu (c \*o F).
Proof.
move=> heF; rewrite /pmf_esummable.
have := esummableZl (f := EFin \o (fun x => F x * mu x)) (c := c%:E) erefl heF.
apply/eq_esummable => x /=.
by rewrite -EFinM mulrA.
Qed.

Lemma bounded_pmf_esummable mu F :
  (exists M, forall x, `|F x| <= M) -> pmf_esummable mu F.
Proof.
case=> M leM; rewrite /pmf_esummable /esummable.
rewrite (eq_esum _ _ (fun x => `|(F x)%:E * (mu x)%:E|)%E).
  by move=> x _; rewrite -EFinM.
apply: esummableMl; last exact: subpmf_summable.
by exists M%:E => [x ?|//]; rewrite /= lee_fin leM.
Qed.

Lemma esummable_pmf mu F : esummable [set: T] (EFin \o F) -> pmf_esummable mu F.
Proof.
move=> smF; rewrite /pmf_esummable /esummable.
rewrite (eq_esum _ _ (fun x => `|(F x)%:E * (mu x)%:E|)%E).
  by move=> x _; rewrite -EFinM.
apply: esummableMr; last exact: smF.
by exists 1%:E => [x ?|//]; rewrite /= lee_fin ger0_norm// subpmf_le1.
Qed.

End pmf_esummable_lemmas.

Section pmf_expectation_lemmas.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T).

Lemma pmf_expectationZ mu f c : (forall x, 0 <= f x) ->
  \E_[mu] (fun x => c * (f x)) = c * (\E_[mu] f).
Proof.
move=> h1; rewrite /pmf_expectation.
under eq_esum => x do rewrite /= -mulrA EFinM.
have hnneg x : (0 <= (f x * mu x)%:E)%E by rewrite lee_fin mulr_ge0 ?h1.
by rewrite esumZ//= fineM.
Qed.

Lemma pmf_expectation_cst mu r : \E_[mu] (fun=> r) = \P_[mu] predT * r.
Proof.
have := pmf_expectationZ mu (f := fun=> 1%R) r.
by rewrite mulr1 => -> //=; rewrite mulrC.
Qed.

Lemma pmf_expectation0 mu : \E_[mu] (fun=> 0) = 0.
Proof. by rewrite pmf_expectation_cst mulr0. Qed.

Lemma supp_eq_pmf_expectation mu (f1 f2 : T -> R):
  {in supp mu, f1 =1 f2} -> \E_[mu] f1 = \E_[mu] f2.
Proof.
move=> eq_f; rewrite /pmf_expectation; congr fine; apply/eq_esum => x /=.
have [/eq_f -> //|] := boolP (x \in supp mu).
by move/memNsuppP => ->; rewrite !mulr0.
Qed.

Lemma pmf_expectationE mu (g : T -> R) :
  \E_[mu] g = fine ('E_(measure_of_pmf mu) [EFin \o g]).
Proof. by rewrite expectation_pmf. Qed.

Lemma pmf_expectationB mu (f g : T -> R) :
    pmf_esummable mu f -> pmf_esummable mu g ->
  \E_[mu] (f \- g) = \E_[mu] f - \E_[mu] g.
Proof.
move=> sf sg; rewrite !pmf_expectationE.
rewrite expectationB//; [exact/Lfun1_integrable/esummable_integrable..|].
by rewrite fineB// expectation_pmfEFin esummable_esum_fin_num.
Qed.

Lemma pmf_expectation_ge0 mu (g : T -> R) :
  (forall y, 0 <= g y) -> 0 <= \E_[mu] g.
Proof.
move=> g0; rewrite /pmf_expectation fine_ge0// esum_ge0// => x _.
by rewrite lee_fin mulr_ge0.
Qed.

End pmf_expectation_lemmas.

Section pmf_expectation_theory.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T) (A B E : pred T).

Local Open Scope ereal_scope.

Lemma expectation_pmf_ret (f : T -> \bar R) (x : T) :
  'E_(measure_of_pmf (pmf_ret x)) [f] = f x.
Proof.
rewrite expectation_def.
rewrite (eq_measure_integral (\d_(x : discrete_measurable_space T))).
  by move=> A _ _; exact: measure_of_pmf_ret.
by rewrite integral_dirac//= diracT mul1e.
Qed.

Lemma expectation_pmf_zero (f : T -> \bar R) :
  'E_(measure_of_pmf pmf_zero) [f] = 0.
Proof.
rewrite expectation_def (eq_measure_integral mzero)/= ?integral_measure_zero//.
by move=> A _ _; exact: measure_of_pmf_zero.
Qed.

Lemma expectation_pmf_bind {U : choiceType} mu (nu : T -> R.-pmf U) F :
  (forall x, 0 <= F x)%E ->
  'E_(measure_of_pmf (pmf_bind nu mu)) [F] =
  'E_(measure_of_pmf mu) [fun x => 'E_(measure_of_pmf (nu x)) [F]].
Proof.
move=> HF; rewrite !expectation_def.
under [in RHS]eq_integral do rewrite expectation_def.
rewrite (eq_measure_integral
    (giry_bind (measure_of_pmf mu) (measurable_measure_of_pmf nu))).
  by move=> A _ _; exact: measure_of_pmf_bind_giry.
exact: giry_int_bind.
Qed.

Lemma expectation_pmf_margin {U : choiceType} (h : T -> U) mu (F : U -> \bar R) :
  (forall y, 0 <= F y)%E ->
  'E_(measure_of_pmf (pmf_margin h mu)) [F] = 'E_(measure_of_pmf mu) [F \o h].
Proof.
move=> F0; rewrite !expectation_def.
rewrite (eq_measure_integral
    (giry_map (measurable_fun_discreteT h) (measure_of_pmf mu))).
  by move=> A _ _; exact: measure_of_pmf_margin.
exact: giry_int_map.
Qed.

Local Open Scope ereal_scope.

Lemma expectation_pmf_bind_EFin {U : choiceType} mu (nu : T -> R.-pmf U)
    (g : U -> R) :
  (forall y, 0 <= g y)%R -> (forall eta, pmf_esummable eta g) ->
  'E_(measure_of_pmf (pmf_bind nu mu)) [EFin \o g] =
  'E_(measure_of_pmf mu) [EFin \o (fun x => \E_[nu x] g)].
Proof.
move=> g0 sg; rewrite (expectation_pmf_bind mu nu)//= !expectation_pmf.
apply: eq_esum => t _ //=; rewrite expectation_pmf; congr (_ * _)%E.
by rewrite /pmf_expectation fineK// (esummable_esum_fin_num (sg (nu _))).
Qed.

End pmf_expectation_theory.

Section pmf_expectation_dRV.
Import MeasurableR.
Context {d} {T : pmeasurableType d} {R : realType} (P : probability T R)
  (X : {dRV P >-> R}).

Local Abbreviation pmfX := (@pmf d T R P X).

Local Open Scope ereal_scope.

Lemma measure_of_pmf_distribution (A : set R) :
  measurable A ->
  measure_of_pmf pmfX A = distribution P X A.
Proof. exact: dRV_esum_pmf_distribution. Qed.

Lemma ge0_expectation_pmf (f : R -> \bar R) :
  measurable_fun [set: R] f -> (forall r, 0 <= f r) ->
 'E_(measure_of_pmf pmfX) [f] = \int[P]_w f (X w).
Proof.
move=> mf f0; rewrite unlock /= -ge0_integral_distribution//.
have mid : measurable_fun [set: discrete_measurable_space R]
    (idfun : discrete_measurable_space R -> R) by [].
transitivity (\int[giry_map mid (measure_of_pmf pmfX)]_y f y).
  exact/esym/giry_int_map.
by apply: eq_measure_integral => A mA _; exact: measure_of_pmf_distribution.
Qed.

Lemma expectation_pmf_integral (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  'E_(measure_of_pmf pmfX) [f] = \int[P]_w f (X w).
Proof.
move=> mf; rewrite unlock integralE [RHS]integralE; congr (_ - _).
- rewrite -[LHS]expectation_def ge0_expectation_pmf => //=.
    exact: measurable_funepos.
  by apply: eq_integral => w _; rewrite !funeposE.
- rewrite -[LHS]expectation_def ge0_expectation_pmf => //=.
     exact: measurable_funeneg.
  by apply: eq_integral => w _; rewrite !funenegE.
Qed.

Lemma expectation_pmf_expectation :
  'E_(measure_of_pmf pmfX) [EFin] = 'E_P[EFin \o X].
Proof. by rewrite expectation_pmf_integral //= unlock. Qed.

End pmf_expectation_dRV.

Section PrCoreTheory.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T) (A B E : pred T).

Lemma prE E mu : (\P_[mu] E)%:E = \esum_(x in [set: T]) ((E x)%:R * mu x)%:E.
Proof.
rewrite fineK//.
rewrite esum_abse; first by move=> ?; rewrite mulr_ge0.
rewrite -esummableE.
apply/(@le_esummable _ _ _ _ (EFin \o mu)) => [x _|//].
rewrite !lee_fin// mulr_ge0//=.
by rewrite ler_piMl //= lern1 leq_b1.
Qed.

Lemma prE_measure mu E : (\P_[mu] E)%:E = measure_of_pmf mu [set` E].
Proof.
rewrite prE /measure_of_pmf [RHS]esum_mkcond esum_setT_discrete.
apply: eq_esum => x _ /=; rewrite mem_setE unfold_in.
by case: (E x); rewrite ?mul1r ?mul0r.
Qed.

Lemma pmf_prob_pred0 mu : \P_[mu] pred0 = 0.
Proof. by rewrite /pmf_prob esum1 // => x /=; rewrite mul0r. Qed.

Lemma pmf_prob_pred1 mu x : \P_[mu] (pred1 x) = mu x.
Proof.
rewrite /pmf_prob.
rewrite (eq_esum _ _ (fun y => if x == y then (mu y)%:E else 0)); last first.
 by rewrite esum_if_eq_op_set1.
move=> y _ /=; rewrite [y == x]eq_sym.
by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
Qed.

Lemma pmf_prob_expectation mu (Q : pred T) :
  \P_[mu] Q = \E_[mu] (fun m => (Q m)%:R).
Proof. by []. Qed.

Lemma pmf_prob_predT mu : \P_[mu] predT = fine (esum [set: T] (EFin \o mu)).
Proof.
rewrite /pmf_prob /pmf_expectation; congr fine.
by apply/eq_esum=> x; rewrite mul1r.
Qed.

Lemma expectation_pmf_cst mu r :
  ('E_(measure_of_pmf mu) [cst r] = (\P_[mu] predT)%:E * r)%E.
Proof.
rewrite expectation_pmf esumZ; first by move=> ?; rewrite lee_fin.
rewrite muleC; congr (_ * _)%E.
rewrite pmf_prob_predT fineK//= esum_abse//=.
have := @subpmf_summable _ _ mu.
by rewrite esummableE.
Qed.

Lemma pmf_expectation_ret (f : T -> R) (x : T) : \E_[pmf_ret x] f = f x.
Proof. by rewrite /pmf_expectation -expectation_pmfEFin expectation_pmf_ret. Qed.

Lemma pmf_prob_ret E x : \P_[pmf_ret x] E = (E x)%:R :> R.
Proof. by rewrite pmf_prob_expectation pmf_expectation_ret. Qed.

Lemma pmf_expectation_zero (f : T -> R) : \E_[pmf_zero] f = 0.
Proof. by rewrite /pmf_expectation -expectation_pmfEFin expectation_pmf_zero. Qed.

Lemma pmf_prob_zero E : \P_[pmf_zero : R.-pmf T] E = 0.
Proof. by rewrite pmf_prob_expectation pmf_expectation_zero. Qed.

Lemma dweight_pmf_zero : dweight (@pmf_zero R T) = 0.
Proof. exact: pmf_prob_zero. Qed.

Lemma pmf_expectation_margin {U : choiceType} (h : T -> U) mu (g : U -> R) :
    (forall y, 0 <= g y) ->
  \E_[pmf_margin h mu] g = \E_[mu] (g \o h).
Proof.
move=> g0.
have g0E y : (0 <= (EFin \o g) y)%E by rewrite /= lee_fin.
by rewrite /pmf_expectation -!expectation_pmfEFin (expectation_pmf_margin h mu).
Qed.

Lemma pmf_prob_ge0 A mu : 0 <= \P_[mu] A.
Proof. by rewrite -lee_fin prE_measure. Qed.

Lemma pmf_cprob_ge0 A B mu : 0 <= \P_[mu, B] A.
Proof. by rewrite /pmf_cprob mulr_ge0 ?invr_ge0 // pmf_prob_ge0. Qed.

Lemma supp_eq_pmf_prob A B mu : {in supp mu, A =i B} -> \P_[mu] A = \P_[mu] B.
Proof.
move=> eq_AB; rewrite /pmf_prob; congr fine.
apply/eq_esum => x _ /=; case/boolP : (x \in supp mu).
- by move/eq_AB; rewrite -!topredE => /= ->.
- by move/memNsuppP => ->; rewrite !mulr0.
Qed.

Lemma eq_pmf_prob A B mu : A =i B -> \P_[mu] A = \P_[mu] B.
Proof. by move=> eq_AB; apply/supp_eq_pmf_prob => x _; exact/eq_AB. Qed.

Lemma pred0_pmf_prob_eq0 (mu : R.-pmf T) (E : pred T) :
  E =1 pred0 -> \P_[mu] E = 0.
Proof. by move=> eq; rewrite -(pmf_prob_pred0 mu); exact/eq_pmf_prob. Qed.

End PrCoreTheory.

Section PrTheory.
Context {R : realType} {T U : choiceType} {I : eqType}.
Implicit Types (mu : R.-pmf T) (A B E : pred T).

Lemma pmf_prob_eq0 A mu :
  (forall x, x \in supp mu -> x \notin A) -> \P_[mu] A = 0.
Proof.
move=> h; rewrite /pmf_prob esum1 //= => x ?; congr EFin.
apply/eqP; rewrite mulf_eq0 orbC; have [//|/=] := eqVneq (mu x) 0.
by move/h; rewrite -topredE /= => /negbTE ->.
Qed.

Lemma pmf_cprob_eq0 A B mu :
  (forall x, x \in supp mu -> x \in B -> x \notin A) ->
  \P_[mu, B] A = 0.
Proof.
move=> h; rewrite /pmf_cprob pmf_prob_eq0 ?mul0r // => x /h {h} /orb_idl.
by rewrite negb_and /= => <-; rewrite orbAC orbN.
Qed.

Lemma subset_pmf_prob A B mu : {subset B <= A} -> \P_[mu] B <= \P_[mu] A.
Proof.
move=> le_BA; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
rewrite ler_wpM2r // ?ge0_mu.
rewrite ler_nat; have := le_BA x; rewrite -!topredE /=.
by case: (B x) => // ->.
Qed.

Lemma pmf_prob_le1 A mu : \P_[mu] A <= 1.
Proof.
apply: (@le_trans _ _ \P_[mu] predT); first by apply/subset_pmf_prob.
rewrite pmf_prob_predT -fine1 fine_le//; [|exact: subpmf_sum_le1].
rewrite ge0_fin_numE.
  by apply: esum_ge0 => x _; rewrite lee_fin.
by apply: le_lt_trans; [exact: subpmf_sum_le1|rewrite ltey].
Qed.

Lemma pmf_prob_bind E f (mu : R.-pmf U) :
  \P_[pmf_bind f mu] E = \E_[mu] (fun x => \P_[f x] E).
Proof.
have fin : esummable [set: U] (fun x => ((\P_[f x] E) * mu x)%:E).
  apply/(le_esummable (g := EFin \o mu)) => [x _|//].
  by rewrite !lee_fin mulr_ge0 ?pmf_prob_ge0//= ler_piMl ?pmf_prob_le1.
apply: EFin_inj; rewrite prE_measure measure_of_pmf_bind.
under eq_integral do rewrite -prE_measure.
rewrite -expectation_def expectation_pmfEFin /pmf_expectation fineK//.
exact: esummable_esum_fin_num.
Qed.

Lemma pmf_prob_margin E f (mu : R.-pmf U) :
  \P_[pmf_margin f mu] E = \P_[mu] [pred x | f x \in E].
Proof.
rewrite /pmf_margin pmf_prob_bind pmf_prob_expectation.
by apply/supp_eq_pmf_expectation=> x _; rewrite pmf_prob_ret.
Qed.

Lemma pmf_expectation_le mu f1 f2 :
    pmf_esummable mu f1 -> pmf_esummable mu f2 -> f1 <=1 f2 ->
  \E_[mu] f1 <= \E_[mu] f2.
Proof.
move=> sm1 sm2 le_f; rewrite /pmf_expectation; apply: fine_le.
- exact: (esummable_esum_fin_num sm1).
- exact: (esummable_esum_fin_num sm2).
- by apply: le_esum => x /=; rewrite lee_fin ler_wpM2r ?ge0_mu.
Qed.

Lemma le_mem_pmf_prob E1 E2 mu :
    (forall x, x \in supp mu -> x \in E1 -> x \in E2) ->
  \P_[mu] E1 <= \P_[mu] E2.
Proof.
move=> le; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP: (x \in supp mu) => [xin|/memNsuppP ->]; last by rewrite !mulr0.
have hE : (E1 x)%:R <= (E2 x)%:R :> R.
  rewrite ler_nat; have := le x xin; rewrite -!topredE /=.
  by case: (E1 x) => // ->.
by rewrite ler_wpM2r // ?ge0_mu.
Qed.

Lemma le_pmf_pmf_prob A (mu nu : R.-pmf T) :
    (forall x, x \in supp nu -> x \in A -> nu x <= mu x) ->
  \P_[nu] A <= \P_[mu] A.
Proof.
move=> h; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP : (x \in supp nu) => [/h {}h|]; last first.
  by move/memNsuppP => ->; rewrite mulr0 mulr_ge0// ler0n.
by case/boolP: (A x) => [/h|]; rewrite ?(mul0r, mul1r).
Qed.

Lemma pmf_cprob_le1 A B mu : \P_[mu, B] A <= 1.
Proof.
move: (pmf_prob_ge0 B mu); rewrite /pmf_cprob le_eqVlt.
case/predU1P => [<-|]; first by rewrite invr0 mulr0 ler01.
move/ler_pdivrMr=> ->; rewrite mul1r.
by apply: le_mem_pmf_prob => x _ /andP[].
Qed.

Lemma pmf_cprob_sum A mu : 0 < \P_[mu] A ->
  fine (\esum_(x in [set: T]) (\P_[mu, A] (pred1 x))%:E) = 1.
Proof.
move=> gt0.
have a0 i : 0 <= (A i)%:R * mu i by rewrite mulr_ge0// ler0n.
have hpr1 x : \P_[mu] [predI pred1 x & A] = (A x)%:R * mu x.
  rewrite /pmf_prob.
  rewrite (eq_esum _ _ ( fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
    move=> y _ /=; rewrite !inE [y == x]eq_sym.
    by case: ifP => xy; rewrite ?mul0r.
  by rewrite esum_if_eq_op_set1.
rewrite (eq_esum _ _ (fun x => ((\P_[mu] A)^-1 * ((A x)%:R * mu x))%:E)).
  by move=> x _; rewrite /pmf_cprob hpr1; congr (_ %:E); rewrite mulrC.
rewrite (EFin_esumZ _ _ a0).
  by rewrite invr_ge0// pmf_prob_ge0.
by rewrite -prE -EFinM mulVf// gt_eqF.
Qed.

Lemma eq0_pmf_prob mu E : \P_[mu] E = 0 -> forall x, x \in E -> mu x = 0.
Proof.
move=> hE x xE.
have hle : \P_[mu] (pred1 x) <= \P_[mu] E.
  by apply: subset_pmf_prob => y; rewrite !inE => /eqP ->.
move: hle; rewrite hE pmf_prob_pred1 => h.
by apply/eqP; rewrite eq_le h /=.
Qed.

Lemma pmf_probID A B mu :
  \P_[mu] A = \P_[mu] [predI A & B] + \P_[mu] [predI A & predC B].
Proof.
have ge0 (P : pred T) i : (0 <= ((P i)%:R * mu i)%:E)%E.
  by rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
by case: (A x); case: (B x).
Qed.

Lemma pmf_prob_predU_indep (A B : pred T) (mu : R.-pmf T) :
    (forall x, x \in A -> x \notin B) ->
  \P_[mu] [predU A & B] = \P_[mu] A + \P_[mu] B.
Proof.
move=> dsj.
have ge0 (P : pred T) i : (0 <= ((P i)%:R * mu i)%:E)%E.
  by rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
case/boolP: (A x) => Ax; case/boolP: (B x) => Bx //=.
by move/dsj: Ax; rewrite -topredE /= Bx.
Qed.

Lemma pmf_prob_mem_map f mu (r : seq U) : uniq r ->
  \P_[mu] [pred x | f x \in r] =
  \sum_(y <- r) \P_[mu] [pred x | f x == y].
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pred0_pmf_prob_eq0.
case/andP => yNr /ih {ih}h; rewrite big_cons -h -pmf_prob_predU_indep.
  by move=> x; rewrite !inE => /eqP ->.
exact/eq_pmf_prob.
Qed.

Lemma pmf_prob_mem mu (r : seq T) : uniq r ->
  \P_[mu] [pred x | x \in r] = \sum_(x <- r) mu x.
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pred0_pmf_prob_eq0//.
case/andP=> yNr /ih {ih}h; rewrite big_cons /= -pmf_prob_pred1.
by rewrite -h -pmf_prob_predU_indep // => x /eqP ->.
Qed.

Lemma pmf_prob_bigor_indep mu (P : I -> pred T) (r : seq I) : uniq r ->
  (forall p1 p2 x,
    p1 != p2 -> p1 \in r -> p2 \in r -> x \in P p1 -> x \notin P p2) ->
  \P_[mu] [pred x | has [pred p | x \in P p] r] =
  \sum_(p <- r) \P_[mu] (P p).
Proof.
move=> uq_r dj; pose S x := \big[orb/false]_(p <- r) (x \in P p).
rewrite (@eq_pmf_prob _ _ _ S) => [x|]; first by rewrite !inE -big_has.
rewrite {}/S; elim: r uq_r dj => [_|p r ih /andP[pNr /ih {ih}h]] dj.
 by rewrite big_nil pred0_pmf_prob_eq0 // => x; rewrite big_nil.
rewrite big_cons -h => [p1 p2 x ne_p p1r p2r|].
  by apply/dj=> //; rewrite in_cons (p1r, p2r) orbT.
rewrite -pmf_prob_predU_indep => [x xNPp|].
  rewrite -topredE /= big_has; apply/hasPn => y y_in_r.
  apply/(dj p); rewrite ?in_cons ?(eqxx, y_in_r, orbT) //.
  by apply: contra pNr => /eqP ->.
by apply/eq_pmf_prob => x; rewrite -!topredE /= big_cons.
Qed.

Lemma pmf_prob_predU A B mu : \P_[mu] [predU A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predI A & B].
Proof.
apply/eqP; rewrite eq_sym subr_eq [in X in _==X]addrC; apply/eqP.
rewrite (pmf_probID _ B) -addrA -pmf_prob_predU_indep => [x|].
  by rewrite !inE => /andP[].
congr (_ + _); apply/eq_pmf_prob => x; rewrite !inE -!topredE /=.
by apply/orb_id2r => /negbTE ->; rewrite andbT.
Qed.

Lemma pmf_prob_predI A B mu : \P_[mu] [predI A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predU A & B].
Proof. by rewrite pmf_prob_predU subKr. Qed.

Lemma le_pmf_prob_predU A B mu : \P_[mu] [predU A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pmf_prob_predU lerBlDr lerDl pmf_prob_ge0. Qed.

Lemma le_pmf_prob_predI A B mu : \P_[mu] [predI A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pmf_prob_predI lerBlDr lerDl pmf_prob_ge0. Qed.

Lemma pmf_prob_predC E mu: \P_[mu](predC E) = \P_[mu] predT - \P_[mu] E.
Proof.
apply/esym/eqP; rewrite subr_eq -pmf_prob_predU_indep//.
by apply/eqP/eq_pmf_prob => x; rewrite !inE orNb.
Qed.

Lemma pmf_prob_split B A mu : \P_[mu] A =
    \P_[mu]        B  * \P_[mu,       B] A
  + \P_[mu] (predC B) * \P_[mu, predC B] A.
Proof.
suff h A' B': \P_[mu] [predI A' & B'] = \P_[mu] B' * \P_[mu, B'] A'.
  by rewrite (pmf_probID _ B); congr (_ + _); exact/h.
rewrite /pmf_cprob mulrCA; have [] := eqVneq (\P_[mu] B') 0; last first.
  by move=> nzPB'; rewrite divff // mulr1.
move=> zPB'; rewrite zPB' invr0 !mulr0; apply/pmf_prob_eq0.
move=> x mux; move/eq0_pmf_prob: zPB' => /(_ x) h; rewrite !inE.
by apply/negP=> /andP[_ /h] /mem_suppP.
Qed.

Lemma pmf_cprob_pred1 (mu : R.-pmf T) x A :
  \P_[mu, A] (pred1 x) = (A x)%:R * mu x / \P_[mu] A.
Proof.
rewrite /pmf_cprob; congr (_ / _); rewrite /pmf_prob.
rewrite (eq_esum _ _ (fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
  move=> y _ /=; rewrite !inE [y == x]eq_sym.
  by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
by rewrite esum_if_eq_op_set1.
Qed.

Lemma esummable_pmf_prob_f f mu (P : pred T):
  pmf_esummable mu f ->
  esummable [set: T] (EFin \o (fun x => (P x)%:R * (f x * mu x))).
Proof.
move=> sm; rewrite /esummable //= .
rewrite (eq_esum _ _ (fun x => `|((P x)%:R)%:E * (f x * mu x)%:E|)%E).
  by move => i _ //; rewrite -abseM.
apply: esummableMl; last exact: sm.
exists 1%:E => [x|//].
by rewrite gee0_abs ?lee_fin ?ler0n// lern1 leq_b1.
Qed.

Lemma esum_is_fin_num_mu_f f mu (P : pred T):
  pmf_esummable mu f ->
  \esum_(x in [set: T]) ((P x)%:R * (f x * mu x))%:E \is a fin_num.
Proof.
by move=> ?; apply: esummable_esum_fin_num; exact: esummable_pmf_prob_f.
Qed.

Lemma pmf_prob_cexpectation_esum mu f (P : pred T):
    pmf_esummable mu f ->
  \P_[mu] P * \E_[mu, P] f =
  fine (\esum_(x in [set: T]) ((P x)%:R * (f x * mu x))%:E).
Proof.
move=> sm.
have [c0|cn0] := eqVneq (\P_[mu] P) 0.
  rewrite c0 mul0r [X in fine X](_ : _ = 0) ?fine0//.
  rewrite esum1// => x _.
  apply/eqP; rewrite eqe mulrCA mulf_eq0; apply/orP; right.
  have [Px|]/= := boolP (P x); last by rewrite mul0r.
  by rewrite mul1r (eq0_pmf_prob _ Px).
rewrite /pmf_cexpectation.
rewrite (eq_esum _ _ (fun x => (\P_[mu] P)^-1 %:E * ((P x)%:R * (f x * mu x))%:E)%E).
  move=> x ?.
  rewrite /= pmf_cprob_pred1 -EFinM; congr (_ %:E).
  by rewrite mulrA mulrC; congr (_ * _); exact: mulrCA.
rewrite (esummable_esumZ _ (esummable_pmf_prob_f P sm)).
  by rewrite abse_fin_num.
by rewrite fineM ?abse_fin_num ?sum_fin_num_mu_f// mulVKf.
Qed.

Lemma pmf_expectation_split A f mu : pmf_esummable mu f ->
  \E_[mu] f = \P_[mu]        A  * \E_[mu,       A] f
            + \P_[mu] (predC A) * \E_[mu, predC A] f.
Proof.
move=> sm.
rewrite [in RHS](pmf_prob_cexpectation_esum A)//.
rewrite [in RHS](pmf_prob_cexpectation_esum (predC A))//.
rewrite [in LHS]/pmf_expectation -fineD ?esum_is_fin_num_mu_f//.
congr fine.
rewrite -esummable_esumD//; [exact: esummable_pmf_prob_f..|].
apply: eq_esum => x ? /=; rewrite -EFinD; congr EFin.
by rewrite -mulrDl -natrD addnC addn_negb mul1r.
Qed.

Lemma bounded_pmf_expectation_le mu F (M : R) :
  0 <= M -> (forall x, `|F x| <= M) -> \E_[mu] F <= M.
Proof.
move=> ge0M bd; apply/(@le_trans _ _ (\E_[mu] (fun _ => M))).
  apply/pmf_expectation_le.
  - by apply/bounded_pmf_esummable; exists M.
  - exact/pmf_esummable_cst.
  - by move=> x; apply/(le_trans _ (bd x))/ler_norm.
by rewrite pmf_expectation_cst ler_piMl // pmf_prob_le1.
Qed.

Lemma ge0_pmf_expectation_bind (mu : R.-pmf T) (nu : T -> R.-pmf U) (g : U -> R) :
    (forall y, 0 <= g y) -> (forall eta, pmf_esummable eta g) ->
  \E_[pmf_bind nu mu] g = \E_[mu] (fun x => \E_[nu x] g).
Proof.
move=> g0 sg; rewrite [LHS]pmf_expectationE expectation_pmf_bind_EFin//.
by rewrite -pmf_expectationE.
Qed.

Lemma le_pmf_esummable {V : choiceType} (mu : R.-pmf V) (k h : V -> R) :
  (forall x, `|k x| <= `|h x|) -> pmf_esummable mu h -> pmf_esummable mu k.
Proof.
move=> kh; rewrite /pmf_esummable => fh.
rewrite esummableE ge0_fin_numE.
  by apply: esum_ge0 => i _; exact: abse_ge0.
apply: (le_lt_trans _ fh); apply: le_esum.
by move => ? ?; rewrite lee_fin !normrM ler_wpM2r.
Qed.

Lemma pmf_esummable_expectation (mu : R.-pmf T) (nu : T -> R.-pmf U) (g : U -> R) :
    (forall y, 0 <= g y) -> (forall eta, pmf_esummable eta g) ->
  pmf_esummable mu (fun x => \E_[nu x] g).
Proof.
move=> g0 sg.
have hge0 x : 0 <= \E_[nu x] g * mu x by rewrite mulr_ge0// pmf_expectation_ge0.
rewrite /pmf_esummable esummableE.
rewrite (eq_esum _ _ (EFin \o (fun x => \E_[nu x] g * mu x))).
  by move=> x _ /=; rewrite ger0_norm.
rewrite -expectation_pmfEFin -(expectation_pmf_bind_EFin mu nu g0 sg).
rewrite expectation_pmfEFin.
exact: (esummable_esum_fin_num (sg (pmf_bind nu mu))).
Qed.

Lemma pmf_expectation_bind mu (nu : T -> R.-pmf U ) F :
    (forall eta, pmf_esummable eta F) ->
  \E_[pmf_bind nu mu] F = \E_[mu] (fun x => \E_[nu x] F).
Proof.
move=> sF.
have spF eta : pmf_esummable eta F^\+.
  exact: (le_pmf_esummable (le_funrpos F) (sF eta)).
have snF eta : pmf_esummable eta F^\-.
  exact: (le_pmf_esummable (le_funrneg F) (sF eta)).
transitivity (\E_[mu] (fun x => \E_[nu x] F^\+)
            - \E_[mu] (fun x => \E_[nu x] F^\-)).
  rewrite -(ge0_pmf_expectation_bind mu nu _ spF)//.
  rewrite -(ge0_pmf_expectation_bind mu nu _ snF) //.
  rewrite -(pmf_expectationB (spF _) (snF _)); congr (\E_[pmf_bind nu mu] _).
  exact/esym/funrposBneg.
rewrite -(pmf_expectationB (pmf_esummable_expectation mu nu _ spF)
  (pmf_esummable_expectation mu nu _ snF))//.
apply: supp_eq_pmf_expectation => x _ /=.
rewrite -(pmf_expectationB (spF _) (snF _)).
by congr (\E_[nu x] _); exact: funrposBneg.
Qed.

End PrTheory.

Section mono_esum.
Context {R : realType} {T : choiceType} {f : (R.-pmf T)^nat}.
Hypothesis ndf : nondecreasing_fun (f : _ -> _ -> _).

Lemma nondecreasing_esum_Efn (E : T -> \bar R):
  (forall m, 0 <= E m)%E ->
  forall m n, (m <= n)%N ->
  (\esum_(x in [set:T]) (E x * (f m x)%:E) <=
   \esum_(x in [set:T]) (E x * (f n x)%:E))%E.
Proof.
move=> hE m n le_mn.
by apply/le_esum => x _; rewrite lee_pmul ?lee_fin//=; exact/lefP/ndf.
Qed.

Lemma esum_pmf_lim_r [E : T -> \bar R] [r : \bar R]:
  (forall m, 0 <= E m)%E ->
  (forall n, \esum_(x in [set: T]) (E x * (f n x)%:E) <= r)%E ->
  (\esum_(x in [set: T]) (E x * ((pmf_lim f) x)%:E) <= r)%E.
Proof.
move => hE h.
rewrite (@eq_esum _ _ _ _ (fun x => ereal_sup (range (fun n =>  E x * (f n x)%:E)%E))).
   move => ? ?; rewrite EFin_pmf_lim_sup//.
  rewrite (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
  by move => ? ?; rewrite lee_fin.
rewrite exchange_esum_ereal_sup//.
- by move => ? ?; rewrite mule_ge0 ?lee_fin.
- by move => ? ? ? ?; rewrite lee_pmul ?lee_fin //; exact/lefP/ndf.
by rewrite ge_ereal_sup//= => x [n s] <-; exact: h.
Qed.

Lemma esum_pmf_lim_r_r [E : T -> R] [r : \bar R]:
  (forall m, 0 <= E m) ->
  (forall n, \esum_(x in [set: T]) ((E x * f n x)%:E) <= r)%E ->
  (\esum_(x in [set: T]) (E x * (pmf_lim f) x)%:E <= r)%E.
Proof.
move=> hE h.
rewrite (eq_esum _ _ (fun x : T => ((E x)%:E * ((pmf_lim f) x)%:E)%E)).
  by move => ? _; rewrite EFinM.
apply: (esum_pmf_lim_r (E := fun x => (E x)%:E)).
  by move=> m; rewrite lee_fin.
move=> n; under eq_esum => x _ do rewrite -EFinM.
exact: h n.
Qed.

Lemma esum_pmf_lim (E : pred T) :
  \esum_(x in [set: T]) ((E x)%:R * (pmf_lim f) x)%:E =
  limn (fun n => \esum_(x in [set: T]) ((E x)%:R * f n x)%:E).
Proof.
have hmono n m : (n <= m)%N -> forall x,
    (((E x)%:R * f n x)%:E <= ((E x)%:R * f m x)%:E)%E.
  move=> nm x; rewrite lee_fin ler_wpM2l ?ler0n//.
  exact/lefP/ndf.
transitivity (ereal_sup (range
    (fun n => \esum_(x in [set: T]) ((E x)%:R * f n x)%:E))); last first.
  apply: sup_range_lim => n m nm; apply: le_esum => x _.
  exact: (hmono n m nm x).
rewrite -(@exchange_esum_ereal_sup _ _ (fun x n => ((E x)%:R * f n x)%:E))//.
- by move=> x n; rewrite lee_fin mulr_ge0// ler0n.
- by move => x n m nm; exact: hmono.
apply: eq_esum => x _.
rewrite EFinM EFin_pmf_lim_sup//.
rewrite (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
  by move=> t n; rewrite lee_fin.
by rewrite lee_fin.
Qed.

End mono_esum.
