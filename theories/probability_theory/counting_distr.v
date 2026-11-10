From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets functions filter.
From mathcomp Require Import constructive_ereal reals discrete.
From mathcomp Require Import esum ereal.
From mathcomp Require Import cardinality fsbigop topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun lebesgue_integral giry hoelder random_variable.
From mathcomp Require Import unstable.

(* Should be removed *)
From mathcomp Require Import numfun.

(**md**************************************************************************)
(* # Subprobability mass function                                             *)
(*                                                                            *)
(* `SubPmf T R`                                                               *)
(* : subprobability mass function for choicetype `T` with values in `R`       *)
(*                                                                            *)
(* `isSubpmf`                                                                 *)
(* : interface for functions that satisfy the property of subprobability mass *)
(* : function                                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*                      dnull == the zero distribution (null distribution)    *)
(*                      dunit == degenerate distribution                      *)
(*                       dlet == monadic bind for distribution                *)
(*                       dlim == limit for index distribution                 *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "R .-pmf  T" (at level 1, T at level 2, format "R .-pmf  T ").
Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").
Reserved Notation "\dlet_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dlet_ ( i  <-  d ) '/  '  E ']'").
Reserved Notation "\dlim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \dlim_ ( n ) '/  '  E ']'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Notation "f '<=1' g" := (forall x, f x <= g x)
  (at level 70, no associativity).
Notation "f '<=2' g" := (forall x y, f x y <= g x y)
  (at level 70, no associativity).
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} {T : choiceType} (f : T -> \bar R) :
  \esum_(x in [set: discrete_measurable_space T]) f x =
  \esum_(x in [set: T]) f x.
Proof.
by apply: (@reindex_esum R T (discrete_measurable_space T)
          [set: T] [set: discrete_measurable_space T] id f); split.
Qed.

Lemma measurable_fun_discrete {T : choiceType} {d'} {U : sigmaRingType d'}
    (D : set (discrete_measurable_space T))
    (f : discrete_measurable_space T -> U) :
  measurable_fun D f.
Proof. by move=> _ Y _. Qed.

#[global] Hint Resolve measurable_fun_discrete : core.

Lemma measurable_fun_discreteT {T U : choiceType} (h : T -> U) :
  measurable_fun [set: discrete_measurable_space T]
    (h : discrete_measurable_space T -> discrete_measurable_space U).
Proof. by move=> _ Y _. Qed.

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

Notation "R .-pmf  T" := (@SubPmf.type R T) : type_scope.

Section SubProbability_measure_subpmf.
Context {R : realType} {T : choiceType} (mu : R.-pmf T).

Definition measure_of_pmf (S : set (discrete_measurable_space T)) :=
  \esum_(x in S) (EFin \o mu) x.

Let P0 : measure_of_pmf set0 = 0%E.
Proof. by rewrite /measure_of_pmf esum_set0. Qed.

Let P_ge0 (S : set (discrete_measurable_space T)) : (0 <= measure_of_pmf S)%E.
Proof. by apply: esum_ge0 => x _; rewrite lee_fin. Qed.

Let P_sigma_additive : semi_sigma_additive measure_of_pmf.
Proof.
move=> F _ tF _.
rewrite [X in _ --> X](_ : _ = \sum_(i <oo) measure_of_pmf (F i))%E.
  rewrite nneseries_esumT; first by move=> n; exact: P_ge0.
  apply: esum_bigcup => //=.
    exact: (sub_trivIset (@subsetT _ _) tF).
  by move=> x; rewrite lee_fin.
apply: cvg_toP => //.
apply: is_cvg_nneseries => n _ _; rewrite /measure_of_pmf.
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ measure_of_pmf
  P0 P_ge0 P_sigma_additive.

Let P_setT : (measure_of_pmf [set: discrete_measurable_space T] <= 1)%E.
Proof. by rewrite /measure_of_pmf esum_setT_discrete; exact: subpmf_sum_le1. Qed.

HB.instance Definition _ :=
  @Measure_isSubProbability.Build _ _ R measure_of_pmf P_setT.

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

Lemma integrable_esummable_new mu (A : T -> \bar R) :
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
- rewrite integral_measure_of_pmf//.
  apply: eq_esum => x _.
  by rewrite !funeposE maxe_pMl ?mul0e// lee_fin.
- rewrite integral_measure_of_pmf//.
  apply: eq_esum => x _.
  by rewrite !funenegE maxe_pMl ?mul0e ?mulNe// lee_fin.
Qed.

Lemma expectation_pmfEFin mu (g : T -> R) :
  'E_(measure_of_pmf mu) [EFin \o g] = esum [set: T] (EFin \o (fun x => g x * mu x))%R.
Proof. by rewrite expectation_pmf. Qed.

Lemma expectation_pmf0 mu : 'E_(measure_of_pmf mu) [cst 0] = 0.
Proof. by rewrite unlock integral0. Qed.

(* NB: not used *)
(* Lemma expection_pmfZ mu F c : (forall x, 0%:E <= F x)%E -> *)
(*   'E_(measure_of_pmf mu)[fun x => c * F x] = c * 'E_(measure_of_pmf mu) [F]. *)
(* Proof. by move=> /= F0; rewrite unlock ge0_integralZl. Qed. *)

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

Lemma pmf_fin_bigcup (J : seq R) : uniq J ->
  \sum_(j <- J) (pmf X j)%:E = P (\bigcup_(j in [set` J]) X @^-1` [set j]).
Proof.
move=> uJ.
rewrite (@measure_fin_bigcup _ _ _ P _ [set` J] (fun j : R => X @^-1` [set j]))//.
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

Definition dinsupp mu := fun x => mu x != 0 :> R.

Lemma in_dinsupp x (mu : R.-pmf T) : (x \in dinsupp mu) = (mu x != 0).
Proof. by []. Qed.

Lemma dinsuppP mu x : reflect (mu x <> 0) (x \in dinsupp mu).
Proof. by apply: (iffP idP) => /eqP. Qed.

Lemma dinsuppPn mu x : reflect (mu x = 0) (x \notin dinsupp mu).
Proof. by rewrite -topredE /dinsupp /= negbK; apply/eqP. Qed.

Definition pr mu E := fine (\esum_(x in [set: T]) ((E x)%:R * mu x)%:E).
Definition prc mu E A := pr mu [predI E & A] / pr mu A.
Definition pmf_expectation mu f := fine (\esum_(x in [set: T]) (f x * mu x)%:E).
Definition espc mu f A := fine (\esum_(x in [set: T]) (f x * prc mu (pred1 x) A)%:E).

Definition pmf_esummable mu f := esummable [set: T] (EFin \o (f \* mu)).

End StdDefs.

Notation "\P_[ mu ] E"     := (pr mu E).
Notation "\P_[ mu , A ] E" := (prc mu E A).
Notation "\E_[ mu ] f"     := (pmf_expectation mu f).
Notation "\E_[ mu , A ] f" := (espc mu f A).
Abbreviation dweight mu        := (\P_[mu] predT).

(* NB: not used *)
(*Section Esp.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T) (f : T -> \bar R).

Definition epmf_expectation mu f := \esum_(x in [set:T]) (f x * (mu x)%:E)%E.

End Esp.*)

Definition sub_distr {R : realType} {T : choiceType} (mu : T -> R) :=
  (forall x, 0 <= mu x) /\ (forall J, uniq J -> \sum_(j <- J) mu j <= 1).

Lemma isdistr_finP {R : realType} {I : finType} (mu : I -> R) :
  (sub_distr mu) <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof.
split=> -[ ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(le_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= lerDl sumr_ge0.
Qed.

(* -------------------------------------------------------------------- *)
Section DistrD.
Context {R : realType} {T : choiceType}.

Definition dnull_fun := fun x : T => (0 : R).

Lemma isd_mnull : sub_distr dnull_fun.
Proof. by split=> // J _; rewrite big1 ?ler01. Qed.

HB.instance Definition _ :=
  @uniq_isSubPmf.Build R T dnull_fun (proj1 isd_mnull) (proj2 isd_mnull).

Definition dnull := @locked R.-pmf T dnull_fun.

Lemma dnullE x : dnull x = 0.
Proof. by unlock dnull. Qed.

End DistrD.

(* -------------------------------------------------------------------- *)
Lemma lef_dnull {R : realType} {T : choiceType} (mu : R.-pmf T) :
  dnull <=1 mu.
Proof. by move=> x; rewrite dnullE. Qed.

(* -------------------------------------------------------------------- *)
Section MeasureOfDnull.
Context {R : realType} {T : choiceType}.

Local Open Scope ereal_scope.

Lemma measure_of_pmf_dnull (S : set (discrete_measurable_space T)) :
  measure_of_pmf (dnull : R.-pmf T) S = mzero S :> \bar R.
Proof. by rewrite /measure_of_pmf esum1// => x _ /=; rewrite dnullE. Qed.

End MeasureOfDnull.

(* -------------------------------------------------------------------- *)
Section Restr.
Context (R : realType) (T : choiceType) (p : pred T).

Definition drestr_fun (mu : R.-pmf T) :=
  fun x => if p x then mu x else 0.

Lemma isd_drestr (mu : R.-pmf T) : sub_distr (drestr_fun mu).
Proof.
split=> [x|J]; first by rewrite /drestr_fun; case: ifP.
move=> eqJ; apply/(@le_trans _ _ (\sum_(j <- J) `|mu j|)).
+ apply/ler_sum=> i _; rewrite /drestr_fun; case: ifPn=> _.
  by apply/ler_norm. by apply/normr_ge0.
+ rewrite -lee_fin.
  apply/(le_trans _ (subpmf_sum_le1 mu)).
  case mu => //= {}mu [[?]]; rewrite esummableE => ? _.
  rewrite (@eq_esum _ _ _ _ (fun y : T => `|(EFin \o mu) y|%E)) //=.
   +  by move => ??; rewrite ger0_norm.
  exact: sum_esum_ge.
Qed.

HB.instance Definition _ (mu : R.-pmf T) :=
  @uniq_isSubPmf.Build R T (drestr_fun mu) (proj1 (isd_drestr mu)) (proj2 (isd_drestr mu)).

Definition drestr (mu : R.-pmf T) := @locked R.-pmf T (drestr_fun mu).

Lemma drestrE (mu : R.-pmf T) x :
  drestr mu x = if p x then mu x else 0.
Proof. by unlock drestr. Qed.
End Restr.

Section pr_pmf.
Import MeasurableR.
Context {d} {T : pmeasurableType d} {R : realType} (P : probability T R)
  (X : {dRV P >-> R}).

Local Abbreviation pmfX := (@pmf _ _ _ P X).

Lemma esum_pmf_range :
  esum [set: R] (EFin \o pmfX) = \esum_(r in range X) (pmfX r)%:E.
Proof.
rewrite (esumID (range X) [set: R] (EFin \o pmfX)).
- by move=> i _; rewrite lee_fin.
rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
by rewrite not_range_pmf0.
Qed.

Lemma esum_pmf_dRV : esum [set: R] (EFin \o pmfX) = 1%E.
Proof.
rewrite esum_pmf_range.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X))//.
transitivity (\esum_(k in dRV_dom X) enum_prob X k).
  apply: eq_esum => k kd/=.
  by rewrite /enum_prob patchE mem_set// /pmf fineK// fin_num_measure.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- by move=> n _; rewrite /enum_prob patchE; case: ifP.
- rewrite eseries_mkcond -[RHS](sum_enum_prob X measurable_set1).
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

Lemma pr_pmf_dRV (A : set R) : measurable A ->
  (\P_[pmfX] (mem A))%:E = distribution P X A.
Proof.
move=> mA; rewrite /pr esum_pmf_pred dRV_esum_pmf_distribution// fineK//.
by rewrite fin_num_measure.
Qed.

End pr_pmf.

(* -------------------------------------------------------------------- *)
Section RestrTheory.
Context {R : realType} {T : choiceType}.

Lemma drestrD (mu : R.-pmf T) (p : pred T) x :
  mu x = drestr p mu x + drestr (predC p) mu x.
Proof. by rewrite !drestrE !inE; case: ifPn; rewrite /= (addr0, add0r). Qed.

Lemma dinsupp_restr (mu : R.-pmf T) (p : pred T) x :
  (x \in dinsupp (drestr p mu)) = (x \in dinsupp mu) && p x.
Proof.
apply/dinsuppP/idP.
- by rewrite /= drestrE; case: ifP=> // _ /dinsuppP ->.
- by case/andP; rewrite /= drestrE => /dinsuppP ? ->.
Qed.
End RestrTheory.

(* -------------------------------------------------------------------- *)
Section DRat.
Context {R : realType} (T : choiceType).

Local Abbreviation distr := R.-pmf T.

Implicit Types (s : seq T).

Definition drat_fun (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma drat_ge0 s : forall x, 0 <= drat_fun s x.
Proof. by move=> x; rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Lemma has_sup_drat s J : uniq J -> \sum_(i <- J) drat_fun s i <= 1.
Proof.
move=> uqJ; rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivrMr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
have ->: (size s = \sum_(i <- undup s) count_mem i s)%N.
  rewrite -sum1_size -big_undup_iterop_count; apply: eq_bigr => i _.
  by rewrite Monoid.iteropE iter_addn addn0 mul1n.
rewrite [X in (_<=X)%N](bigID (mem J)) /= -ltnS -addSn.
rewrite ltn_addr //= ltnS -big_filter -[X in (_<=X)%N]big_filter.
rewrite leq_eqVlt; apply/orP; left; apply/eqP/perm_big.
apply/uniq_perm; rewrite ?filter_uniq ?undup_uniq //.
by move=> x; rewrite !mem_filter mem_undup andbC.
Qed.

Lemma drat_sup s : (0 < size s)%N ->
  \sum_(i <- undup s) drat_fun s i = 1.
Proof.
move=> gt0_s; rewrite -mulr_suml -natr_sum.
apply/(mulIf (x := (size s)%:R)); first by rewrite pnatr_eq0 -lt0n.
rewrite mul1r divfK ?pnatr_eq0 -?lt0n//; congr (_%:R).
rewrite -sum1_size -[in RHS]big_undup_iterop_count/=; apply: eq_bigr => i _.
by rewrite Monoid.iteropE iter_addn addn0 mul1n.
Qed.

Lemma summable_drat s: esummable [set :T] (EFin \o (drat_fun s)).
Proof.
rewrite /esummable (@le_lt_trans _ _ 1%:E) ?ltey//.
rewrite ge0_esum.
+ by move => ? _;rewrite lee_fin.
rewrite ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin // lee_fin fsbig_finite //=.
rewrite (eq_bigr (drat_fun s)).
+ move => ??; rewrite ger0_norm ?drat_ge0 //.
by apply/has_sup_drat.
Qed.

Lemma isd_drat s : sub_distr (drat_fun s).
Proof. by split; [exact/drat_ge0|exact/has_sup_drat]. Qed.

HB.instance Definition _ (s : seq T) :=
  @uniq_isSubPmf.Build R T (drat_fun s) (proj1 (isd_drat s)) (proj2 (isd_drat s)).

Definition drat (s : seq T) := @locked R.-pmf T (drat_fun s).

Lemma drat1E s x :
  drat s x = (count_mem x s)%:R / (size s)%:R.
Proof. by unlock drat. Qed.

Definition dunit x := drat [:: x].
Definition duni  s := drat (undup s).

Lemma dunit1E x y : (dunit x) y = (x == y)%:R.
Proof. by rewrite /dunit drat1E /= addn0 divr1. Qed.

Lemma dunit_id x : (dunit x) x = 1.
Proof. by rewrite /dunit drat1E /= addn0 divr1 eqxx. Qed.

Lemma dunit_diff x y: x <> y -> (dunit x) y = 0.
Proof. by rewrite /dunit drat1E /= addn0 divr1 => /eqP /negPf ->. Qed.

Lemma duni1E s x : (duni s) x = (x \in s)%:R / (size (undup s))%:R.
Proof. by rewrite /duni drat1E count_uniq_mem ?(mem_undup, undup_uniq). Qed.

Lemma in_dunit t t' : t' \in dinsupp (dunit t) -> t' = t :> T.
Proof. by rewrite in_dinsupp /= dunit1E  pnatr_eq0 eqb0 negbK => /eqP. Qed.
End DRat.

(* -------------------------------------------------------------------- *)
Section MeasureOfDunit.
Context {R : realType} {T : choiceType}.

Local Open Scope ereal_scope.

Lemma measure_of_pmf_dunit (x : T) (S : set (discrete_measurable_space T)) :
  measure_of_pmf (dunit x) S = \d_(x : discrete_measurable_space T) S :> \bar R.
Proof.
rewrite /measure_of_pmf diracE esum_mkcond esum_setT_discrete.
rewrite (eq_esum _ _ (fun y => if x == y then ((y \in S)%:R)%:E else 0)).
  move=> y _ /=; rewrite dunit1E.
  by case: (x =P y) => [<-|_]; rewrite ?eqxx; case: ifPn.
by rewrite esum_if_eq_op_set1.
Qed.

End MeasureOfDunit.

(* -------------------------------------------------------------------- *)
Section Flip.
Context {R : realType}.

Local Abbreviation clamp := (@clamp R 0 1).

Definition dflip_fun (xt : R) :=
  fun b => if b then clamp xt else 1 - clamp xt.

Lemma isd_dflip xt : sub_distr (dflip_fun xt).
Proof.
apply/isdistr_finP; split=> [b|].
+ by case: b; rewrite ?subr_ge0 clamp_gele.
+ by rewrite /index_enum !unlock /= addr0 addrC subrK.
Qed.

HB.instance Definition _ (xt : R) :=
  @uniq_isSubPmf.Build R _ (dflip_fun xt) (proj1 (isd_dflip xt)) (proj2 (isd_dflip xt)).

Definition dflip (xt : R) := @locked R.-pmf bool (dflip_fun xt).

Lemma dflip1E xt : dflip xt =1 (fun b => if b then clamp xt else 1 - clamp xt).
Proof. by unlock dflip. Qed.
End Flip.

(* -------------------------------------------------------------------- *)
Section Bind.
Context {R : realType} {T U : choiceType} (f : T -> R.-pmf U) (mu : R.-pmf T).

Definition dlet_fun := fun y : U => fine (esum [set:T] (fun x => EFin (mu x * f x y))).

Lemma dlet_pos x : 0 <= fine (\esum_(x0 in [set: T]) (mu x0 * f x0 x)%:E).
Proof.
rewrite /fine.
case h : (\esum_(i in [set: T]) _) => //=.
rewrite -lee_fin -{}h esum_ge0 // => ??.
by rewrite EFinM mule_ge0 //= lee_tofin.
Qed.

Lemma isd_dlet : sub_distr dlet_fun.
Proof.
split=> [x|J uqJ].
+ exact: dlet_pos.
+ rewrite /dlet_fun -lee_fin.
  have hpos : (forall x i, 0 <= (mu x * f x i)%:E )%E.
  + by move => ?? ;rewrite EFinM mule_ge0  //= lee_tofin.
  apply /le_trans.
  + apply sum_esum_ge => // x.
    exact: dlet_pos.
  apply/(le_trans _ (subpmf_sum_le1 mu)).
  apply/(le_trans (le_esum_fine _ _ hpos)).
  rewrite exchange_esum // le_esum //  => i ?.
  under eq_esum do rewrite EFinM.
  rewrite esumZ // ?lee_tofin // => [? |]; rewrite ?lee_tofin //=.
  rewrite muleC gee_pMl // ?lee_tofin //;last exact: subpmf_sum_le1.
  rewrite (eq_esum _ _ (fun x  => `|(EFin \o f i) x|%E)) //.
  + by move => ??; rewrite gee0_abs //= lee_tofin.
  by rewrite -esummableE.
Qed.

HB.instance Definition _ :=  @uniq_isSubPmf.Build R U dlet_fun (proj1 isd_dlet) (proj2 isd_dlet).

Definition dlet := @locked R.-pmf U dlet_fun.

Lemma dletE y : dlet y = fine (esum [set:T] (fun x => EFin (mu x * f x y))).
Proof. by unlock dlet. Qed.
End Bind.

Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).

Definition dlift {R : realType} {T : choiceType} (f : T -> R.-pmf T) :=
  fun d => \dlet_(x <- d) f x.

Definition diter {R : realType} {T : choiceType} n (f : T -> R.-pmf T) :=
  fun a => (iter n (dlift f) (dunit a)).

(* TODO: move (generic lemma) *)
Lemma esum_abse {R : realType} {T : choiceType} (f : T -> R) :
  (forall i, 0 <= f i)%R ->
  (\esum_(x in [set: T]) (f x)%:E = \esum_(x in [set: T]) `|(f x)%:E|)%E.
Proof. by move => ?; apply eq_esum => ?? ; rewrite gee0_abs // lee_tofin. Qed.

Lemma summable_mu_wgtd {R : realType} {T : choiceType}
  (f : T -> R) (mu : R.-pmf T)  :
  (forall x, 0 <= f x <= 1) -> esummable [set: T] (fun x => EFin (mu x * f x)).
Proof.
rewrite /esummable => h.
under eq_esum do rewrite EFinM.
apply: esummableMr => //.
+ exists 1%E => // => i.
  case /andP: (h i) => ?? ; rewrite lee_tofin // ger0_norm //.
exact: subpmf_summable.
Qed.

(* -------------------------------------------------------------------- *)
Section BindTheory.
Variables (R : realType) (T U : choiceType).

Implicit Types (f g : T -> R.-pmf U) (mu nu : R.-pmf T).

Lemma dlet_null f : dlet f dnull =1 dnull.
Proof.
move=> x; rewrite dletE esum1; last first.
+ by rewrite dnullE.
by move => ? ?; rewrite /= dnullE /= EFinM mul0e.
Qed.

Lemma dlet_unit f v : \dlet_(y <- dunit v) f y =1 f v.
Proof.
move=> y; rewrite dletE.
rewrite  (esumID ([set v]%classic)).
+ by move => ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move => i [? h]; rewrite dunit_diff // ?mul0r //=.
  by apply nesym.
by rewrite dunit_id addr0 mul1r.
Qed.

Lemma dlet_dunit_id mu : \dlet_(t <- mu) (dunit t) =1 mu.
Proof.
move=> v; rewrite dletE.
rewrite  (esumID ([set v]%classic)).
+ by move => ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move => i [? h]; rewrite dunit_diff // ?mulr0 //=.
by rewrite dunit_id  mulr1 addr0.
Qed.

Lemma eq_in_dlet f g mu nu : {in dinsupp mu, f =2 g} -> mu =1 nu ->
  dlet f mu =1 dlet g nu.
Proof.
move=> eq_f eq_mu y; rewrite !dletE.
have -> //= : (\esum_(x in [set: T]) (mu x * f x y)%:E =
            \esum_(x in [set: T]) (nu x * g x y)%:E).
apply /eq_esum.
move => x ?.
rewrite -eq_mu !EFinM.
case /boolP: (x \in dinsupp mu) => [/eq_f ->//|].
by move/dinsuppPn => ->; rewrite !mul0e.
Qed.

Lemma summable_dlet (f : T -> R.-pmf U) (mu : R.-pmf T) y :
  esummable [set: T] (fun x : T => (mu x * (f x) y)%:E).
Proof. by apply/summable_mu_wgtd=> x; rewrite subpmf_ge0 subpmf_le1. Qed.

Lemma fin_esum (f : T -> R.-pmf U) (mu : R.-pmf T) y:
  \esum_(x' in [set: T]) (mu x' * f x' y)%:E \is a fin_num.
Proof.
rewrite esum_abse.
+ by move => ?; rewrite mulr_ge0.
by  have := (summable_dlet f mu y); rewrite esummableE.
Qed.

Lemma dlet_EFin (f : T -> R.-pmf U) (mu : R.-pmf T) y :
  (dlet f mu y)%:E = esum [set:T] (fun x => (mu x * f x y)%:E).
Proof. by rewrite dletE fineK// ?fin_esum. Qed.

Lemma le_in_dlet f g mu : {in dinsupp mu, f <=2 g} ->
  dlet f mu <=1 dlet g mu.
Proof.
move=> le_f y; rewrite !dletE fine_le // ?fin_esum //.
apply: le_esum => x ?.
case /boolP: (x \in dinsupp mu) => [/le_f ?|].
rewrite !EFinM lee_pmul //= lee_tofin //=.
by move/dinsuppPn => ->; rewrite !EFinM !mul0e.
Qed.

Lemma le_mu_dlet f mu nu : mu <=1 nu -> dlet f mu <=1 dlet f nu.
Proof.
move => le_mu y; rewrite !dletE fine_le //= ?fin_esum //.
apply: le_esum => x ?.
by rewrite !EFinM lee_pmul //= lee_tofin.
Qed.

Lemma le_dlet f g mu nu :
    mu <=1 nu
  -> {in dinsupp mu, forall x, f x <=1 g x}
  -> \dlet_(x <- mu) f x <=1 \dlet_(x <- nu) g x.
Proof.
move=> le_mu le_fg x.
by apply/(le_trans (le_in_dlet le_fg _))/le_mu_dlet.
Qed.

Lemma dletC (mu : R.-pmf T) (nu : R.-pmf U) y :
  (\dlet_(_ <- mu) nu) y = (dweight mu) * (nu y).
Proof.
rewrite dletE /pr //=.
under eq_esum do rewrite mulrC EFinM.
rewrite esumZ ?lee_tofin //= => [?| ]; rewrite ?lee_tofin //.
rewrite fineM => //=;last first.
+ rewrite mulrC. symmetry.
  by under eq_esum do rewrite mul1r.
by rewrite esum_abse// -esummableE subpmf_summable.
Qed.

Lemma dinsupp_dlet f mu y :
  y \in dinsupp (\dlet_(x <- mu) f x) ->
    exists2 x, x \in dinsupp mu & f x y != 0.
Proof.
rewrite in_dinsupp /= dletE => nz_dlet.
have /esum_neq0[x _] : \esum_(x in [set: T]) (mu x * f x y)%:E != 0.
+ by apply: contra nz_dlet => /eqP ->; rewrite fine0.
rewrite eqe mulf_eq0 negb_or => /andP[nz_mu nz_f].
by exists x; rewrite ?in_dinsupp.
Qed.

Lemma fine_esum0 (f : T -> R.-pmf U) (mu : R.-pmf T) x y:
  fine (\esum_(x in [set: T]) (mu x * f x y)%:E) = 0 ->
  ((mu x * f x y)%:E = 0).
Proof.
move => h0.
apply /(@esum_eq0P _ _  [set: T] (fun i => (mu i * f i y)%:E)) => //.
+ by move=> i _; rewrite lee_fin mulr_ge0.
+ by rewrite -(fineK (fin_esum f mu y)) h0.
Qed.

Lemma dlet_dinsupp f mu x y :
  x \in dinsupp mu -> f x y != 0 -> y \in dinsupp (dlet f mu).
Proof.
move => /dinsuppP mux nz_fxy.
apply /dinsuppP; rewrite /= dletE => /(fine_esum0 x).
move=> /eqP; rewrite eqe mulf_eq0 (negbTE nz_fxy) orbF => /eqP.
exact: mux.
Qed.

Lemma dlet_eq0 (f : T -> U) mu y :
  {in dinsupp mu, forall x, f x != y} -> (\dlet_(x <- mu) dunit (f x)) y = 0.
Proof.
move=> h; rewrite dletE.
have -> : \esum_(x in [set: T]) (mu x * dunit (f x) y)%:E = 0.
+ apply: esum1 => x _.
  case/boolP: (x \in dinsupp mu) => [xin|/dinsuppPn ->].
  - by have := h _ xin; rewrite dunit1E => /negbTE ->; rewrite mulr0.
  - by rewrite mul0r.
by [].
Qed.

Lemma eq0_dlet (mu : R.-pmf T) (F : T -> R.-pmf U ) y :
  (\dlet_(x <- mu) F x) y = 0 -> forall x, x \in dinsupp mu -> F x y = 0.
Proof.
rewrite dletE => /fine_esum0 => h x.
move => /dinsuppP /eqP mu_x. move: (h x).
by  move=> /eqP ; rewrite eqe mulf_eq0 (negbTE mu_x) /= => /eqP.
Qed.

End BindTheory.

(* -------------------------------------------------------------------- *)
Section MeasureOfDlet.
Context {R : realType} {T U : choiceType}.

Local Open Scope ereal_scope.

Lemma measure_of_pmf_dlet (mu : R.-pmf T) (nu : T -> R.-pmf U)
    (S : set (discrete_measurable_space U)) :
  measure_of_pmf (dlet nu mu) S
    = \int[measure_of_pmf mu]_x measure_of_pmf (nu x) S.
Proof.
rewrite integral_measure_of_pmf // /measure_of_pmf.
under eq_esum do rewrite /= dlet_EFin.
rewrite exchange_esum .
+ by move=> i j; rewrite lee_fin mulr_ge0.
apply: eq_esum => x _.
rewrite muleC -esumZ //=.
by move=> y _; rewrite lee_fin.
Qed.

Lemma measurable_measure_of_pmf (nu : T -> R.-pmf U) :
  measurable_fun [set: discrete_measurable_space T]
    (fun x => (measure_of_pmf (nu x) : giry (discrete_measurable_space U) R)).
Proof. by move=> _ Y _. Qed.

Lemma measure_of_pmf_dlet_bind (mu : R.-pmf T) (nu : T -> R.-pmf U)
    (S : set (discrete_measurable_space U)) :
  measure_of_pmf (dlet nu mu) S = giry_bind (measure_of_pmf mu) (measurable_measure_of_pmf nu) S.
Proof.
rewrite /giry_bind/= giry_int_map//=.
+ by apply: measurable_giry_ev.
exact: measure_of_pmf_dlet.
Qed.

End MeasureOfDlet.

(* -------------------------------------------------------------------- *)
Section DLetDLet.
Context {R : realType} {T U V : choiceType}
  (f1 : T -> R.-pmf U) (f2 : U -> R.-pmf V).

Lemma dlet_dlet (mu : R.-pmf T) :
     \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x
  =1 \dlet_(y <- mu) (\dlet_(x <- f1 y) f2 x).
Proof.
move=> z; rewrite !dletE.
pose S y x := mu x * f1 x y * f2 y z.
rewrite (eq_esum _ _ (fun y => \esum_(x in [set: T]) (S y x)%:E)%E).
+ move => y ?; subst S; rewrite EFinM dlet_EFin //.
  + rewrite muleC -esumZ // ?lee_tofin // => [? |].
    + by rewrite EFinM lee_tofin // mulr_ge0.
    + by apply eq_esum => ??; rewrite -EFinM mulrC.
rewrite (eq_esum _ _ (fun x => \esum_(y in [set: U]) (S y x)%:E)%E).
+ move => x ?; subst S; rewrite EFinM dlet_EFin //.
  + rewrite -esumZ // ?lee_tofin // => [? |].
    + by rewrite EFinM lee_tofin // mulr_ge0.
    + by apply eq_esum => ??; rewrite -EFinM mulrA.
by rewrite exchange_esum // => ??; rewrite /S EFinM lee_tofin // !mulr_ge0.
Qed.
End DLetDLet.

(* -------------------------------------------------------------------- *)
Section DLetAlg.
Context {R : realType} {T U : choiceType} (mu mu1 mu2 : R.-pmf T).

Lemma dlet_additive (f : T -> R.-pmf U) z :
  (forall x, mu x = mu1 x + mu2 x) -> (\dlet_(x <- mu) f x) z =
    (\dlet_(x <- mu1) f x) z + (\dlet_(x <- mu2) f x) z.
Proof.
move=> muD; rewrite !dletE.
under eq_esum do rewrite muD mulrDl EFinD.
rewrite esumD.
1-2: by move => ??; rewrite /S EFinM lee_tofin // !mulr_ge0.
by rewrite fineD //= fin_esum .
Qed.
End DLetAlg.

(* -------------------------------------------------------------------- *)
Lemma mono_nondecressing {R : realType} (T : choiceType) (f : nat -> T -> R)
  (hmono : forall n m, (n <= m)%N -> forall x, f n x <= f m x) :
  forall x, nondecreasing_seq (fun n => (f n x)%:E).
Proof. by move=> x n m nm; rewrite lee_fin; exact: hmono. Qed.

Lemma sup_range_lim {R : realType} (u : (\bar R)^nat) :
  nondecreasing_seq u -> ereal_sup (range u) = limn u.
Proof.
by move=> ndu; apply/esym/cvg_lim => //; exact: ereal_nondecreasing_cvgn.
Qed.

(* -------------------------------------------------------------------- *)
Section dlim.
Context {R : realType} (T : choiceType).

Implicit Types (f g : nat -> R.-pmf T).

Import numFieldNormedType.Exports.

Definition dlim_fun f : T -> R :=
  fun x => fine (limn_einf (fun n : nat => (f n x)%:E)).

Lemma liminf_ge0 f x : (0 <= limn_einf (fun n => (f n x)%:E))%E.
Proof.
rewrite limn_einf_lim; apply: lime_ge; first exact: is_cvg_einfs.
apply: nearW => n; apply: le_ereal_inf_tmp => _ [m _] <-.
by rewrite lee_fin.
Qed.

Lemma liminf_le1 f x : (limn_einf (fun n => (f n x)%:E) <= 1%:E)%E.
Proof.
rewrite limn_einf_lim; apply: lime_le; first exact: is_cvg_einfs.
apply: nearW => n; apply: (@le_trans _ _ (f n x)%:E); first exact: ge_einfs.
by rewrite lee_fin subpmf_le1.
Qed.

Lemma fin_liminf f x : limn_einf (fun n => (f n x)%:E) \is a fin_num.
Proof.
have h0 : (0 <= limn_einf (fun n => (f n x)%:E))%E by exact: liminf_ge0.
rewrite ge0_fin_numE//.
by apply: le_lt_trans; [exact: liminf_le1 |exact: ltry].
Qed.

Lemma dlim_fun_EFin f x : (dlim_fun f x)%:E = limn_einf (fun n => (f n x)%:E).
Proof. by rewrite /dlim_fun fineK// fin_liminf. Qed.

Lemma sumlim {u : T -> (\bar R)^nat} :
  (forall j, nondecreasing_seq (u j)) -> (forall j, limn (u j) \is a fin_num) ->
  forall L, (\sum_(j <- L) limn (u j) = limn (fun n => \sum_(j <- L) u j n))%E.
Proof.
move=> ndu fu; elim => [|a L IH].
- rewrite big_nil; apply/esym/cvg_lim => //.
  by apply: cvg_near_cst; apply: nearW => n; rewrite big_nil.
- rewrite big_cons IH.
  under [in RHS]eq_fun => n do rewrite big_cons.
  apply/esym/cvg_lim => //.
  apply: cvgeD.
  + by apply: fin_num_adde_defr; exact: fu.
  + by apply: ereal_nondecreasing_is_cvgn; exact: ndu.
  + apply: ereal_nondecreasing_is_cvgn => n m nm.
    by apply: lee_sum => j _; exact: ndu.
Qed.

Lemma isd_dlim f : sub_distr (dlim_fun f).
Proof.
split=> [x|J uqJ].
  by rewrite /dlim_fun; apply: fine_ge0; exact: liminf_ge0.
have ndE (j : T) : nondecreasing_seq (einfs (fun n => (f n j)%:E)).
  exact: nondecreasing_einfs.
have finE (j : T) : limn (einfs (fun n => (f n j)%:E)) \is a fin_num.
  by rewrite -limn_einf_lim fin_liminf.
rewrite -lee_fin -sumEFin.
under eq_bigr => j _ do rewrite dlim_fun_EFin limn_einf_lim.
rewrite (sumlim ndE finE); apply: lime_le.
  apply: ereal_nondecreasing_is_cvgn => n m nm.
  by apply: lee_sum => j _; exact: ndE.
apply: nearW => n; apply: (@le_trans _ _ (\sum_(j <- J) (f n j)%:E)).
  by apply: lee_sum => j _; exact: ge_einfs.
rewrite sumEFin.
apply: le_trans (subpmf_sum_le1 (f n)).
exact: sum_esum_ge.
Qed.

HB.instance Definition _ f :=
  @uniq_isSubPmf.Build R T (dlim_fun f) (proj1 (isd_dlim f)) (proj2 (isd_dlim f)).

Definition dlim f := @locked R.-pmf T (dlim_fun f).

Lemma dlimE f x : dlim f x = fine (limn_einf (fun n => (f n x)%:E)).
Proof. by unlock dlim. Qed.

Lemma dlim_EFin f x : (dlim f x)%:E = limn_einf (fun n => (f n x)%:E).
Proof. by unlock dlim; exact: dlim_fun_EFin. Qed.

Definition homo (f : nat -> R.-pmf T) :=
  forall n m, (n <= m)%N -> f n <=1 f m.

Definition nd (f : nat -> R.-pmf T) :=
  forall x, nondecreasing_seq (fun n => (f n x)%:E).

Lemma dhomo_dnd f : homo f -> nd f.
Proof. by move=> hf; apply: mono_nondecressing => n m nm x; exact: hf. Qed.

Lemma cvg_dlim f : nd f -> forall x, cvgn (fun n => (f n x)%:E).
Proof. by move=> ndf x; apply: ereal_nondecreasing_is_cvgn; exact: ndf. Qed.

Lemma dlim_limE f : nd f ->
  forall x, dlim f x = fine (limn (fun n => (f n x)%:E)).
Proof.
by move=> ndf x; rewrite dlimE is_cvg_limn_einfE//; exact: cvg_dlim.
Qed.

Lemma dlim_limEFin f : nd f ->
  forall x, (dlim f x)%:E = limn (fun n => (f n x)%:E).
Proof.
by move=> ndf x; rewrite dlim_EFin is_cvg_limn_einfE//; exact: cvg_dlim.
Qed.

Lemma dlim_sup f : nd f ->
  forall x, (dlim f x)%:E = ereal_sup (range (fun n => (f n x)%:E)).
Proof. by move=> ndf x; rewrite (dlim_limEFin ndf) -(sup_range_lim (ndf x)). Qed.

End dlim.

Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).

(* -------------------------------------------------------------------- *)
Section DLimTheory.
Variables (R : realType) (T U : choiceType).

Implicit Types (f g : nat -> R.-pmf T) (h : T -> R.-pmf U).
Implicit Types (mu : R.-pmf T).

Lemma dlimC mu : \dlim_(n) mu =1 mu.
Proof.
by move=> x; rewrite dlimE limn_einf_cst.
Qed.

Lemma dlim_bump f : \dlim_(n) f n.+1 =1 dlim f.
Proof. by move=> x; rewrite !dlimE (limn_einf_shiftS (fun n => (f n x)%:E)). Qed.

Lemma dlim_lift f p : \dlim_(n) f (n + p)%N =1 dlim f.
Proof. by move=> x; rewrite !dlimE (limn_einf_shift_new (fun n => (f n x)%:E) p). Qed.

Lemma dlim_ge0 f x : 0 <= dlim f x.
Proof. by []. Qed.

Lemma dlim_le1 f : forall x, dlim f x <= 1.
Proof. by move=> x; rewrite -lee_fin dlim_EFin; exact: liminf_le1. Qed.

Lemma le_dlim f g :
  (forall n, f n <=1 g n) -> dlim f <=1 dlim g.
Proof.
move=> le x; rewrite -lee_fin !dlim_EFin !limn_einf_lim.
apply: lee_lim; [exact: is_cvg_einfs | exact: is_cvg_einfs |].
apply: nearW => n; apply: le_ereal_inf_tmp => _ [m /= nm] <-.
apply: (@le_trans _ _ ((f m x)%:E)); first exact: ge_einfs.
by rewrite lee_fin; exact: le.
Qed.

Lemma eq_dlim f g :  (forall n, f n =1 g n) -> dlim f =1 dlim g.
Proof.
move=> eq_fg x.
apply/eqP; rewrite eq_le; apply/andP; split.
1-2 : by apply le_dlim; move => ??; rewrite eq_fg.
Qed.

Lemma leub_dlim f mu : (forall n, f n <=1 mu) -> dlim f <=1 mu.
Proof.
move => le x; rewrite -(dlimC mu x).
by apply : le_dlim => n y.
Qed.

Lemma dlim_ub f k : homo f -> f k <=1 dlim f.
Proof.
move=> hf x; rewrite -lee_fin (dlim_limEFin (dhomo_dnd hf)).
apply: lime_ge; first exact: (cvg_dlim (dhomo_dnd hf)).
near=> n; apply: (dhomo_dnd hf x).
by near: n; apply: nbhs_infty_ge.
Unshelve. all: by end_near.
Qed.

End DLimTheory.

Section DletDLim.
Context {R : realType} {T U : choiceType}.

Implicit Types (f : (R.-pmf T)^nat) (h : T -> R.-pmf R).

Lemma sup_mul f (hf : nd f) (c : R) x : 0 <= c ->
  ((dlim f x) * c)%:E = ereal_sup (range (fun n => (f n x * c)%:E)).
Proof.
move=> c0.
rewrite EFinM (dlim_sup hf) muleC.
rewrite (@ge0_ereal_supZl_range R T (fun t n => (f n t)%:E)) //=.
  by move=> t n; rewrite lee_fin.
have -> :
  [set (c%:E * (f i x)%:E)%E | i in [set: nat]]%classic =
    [set (f i x * c)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  - by move=> ? [x0 ?]; rewrite -EFinM mulrC=> <- //=; exists x0.
  - by move=> ? [x0 ?]; rewrite mulrC EFinM => <- //=; exists x0.
reflexivity.
Qed.

Lemma dlet_lim f h : nd f -> dlet h (dlim f) =1 \dlim_(n) (dlet h (f n)).
Proof.
move=> ndf y; apply: EFin_inj.
have nd : nd (fun n => dlet h (f n)).
+ apply: mono_nondecressing => n m hnm x.
  apply: le_mu_dlet => ?; rewrite -lee_fin; exact: ndf.
rewrite dlet_EFin (dlim_sup nd).
under eq_esum => x _ do rewrite (sup_mul ndf)//.
rewrite (@exchange_esum_ereal_sup R T (fun x n => (f n x * h x y)%:E)) /=.
+ by move=> t n; rewrite lee_fin; exact: mulr_ge0.
+ move=> n m nm t; rewrite lee_fin ler_wpM2r//.
  by rewrite -lee_fin; exact: ndf.
have -> :
[set \esum_(x in [set: T]) (f i x * h x y)%:E | i in [set: nat]]%classic =
[set ((\dlet_(i <- f i) h i) y)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  - by move=> ? [x0 ?]; rewrite -dlet_EFin => <- //=; exists x0.
  - by move=> ? [x0 ?]; rewrite dlet_EFin => <- //=; exists x0.
reflexivity.
Qed.

End DletDLim.

Section DLimDlet.
Context (R : realType) (T U : choiceType) (f : nat -> T -> R.-pmf U).
Context (hmono: forall x n m, (n <= m)%N -> f n x <=1 f m x).

Lemma dlim_let (mu : R.-pmf T) :
  \dlim_(n) \dlet_(x <- mu) (f n x) =1 \dlet_(x <- mu) \dlim_(n) (f n x).
Proof.
have nd1 y : nd (fun n => f n y).
+ apply: mono_nondecressing => n m hnm x.
  exact: hmono.
have nd2 : nd (fun n => dlet (f n) mu).
+ apply: mono_nondecressing => n m hnm x.
  apply: le_in_dlet => z _.
  exact: hmono.
move=> z; apply: EFin_inj.
rewrite (dlim_sup nd2 ) dlet_EFin.
under eq_esum => t _ do rewrite mulrC (sup_mul (nd1 t))//.
rewrite (@exchange_esum_ereal_sup R T (fun t n => (f n t z * mu t)%:E)) /=.
+ by move=> t n; rewrite  lee_fin; exact: mulr_ge0.
+ move=> n m nm t; rewrite lee_fin ler_wpM2r//.
  exact: hmono.
have ->:
  [set ((\dlet_(i0 <- mu) f i i0) z)%:E | i in [set: nat]]%classic =
  [set \esum_(x in [set: T]) (f i x z * mu x)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  -  move=> ? [x0 ?]; rewrite dlet_EFin=> <-//=; exists x0 => //=.
     by under eq_esum do rewrite  mulrC.
  - move=> ? [x0 ?]; under eq_esum do rewrite mulrC.
    by move => <- //=; exists x0 => //=; rewrite -dlet_EFin.
reflexivity.
Qed.

End DLimDlet.

Section DLimDLim.
Context (R : realType) (T : choiceType) (f : nat -> nat -> R.-pmf T).
Context (hmono1: (forall k n1 n2, (n1 <= n2)%N -> f n1 k <=1 f n2 k)).
Context (hmono2: (forall k n1 n2, (n1 <= n2)%N -> f k n1 <=1 f k n2)).

Lemma dhomo_apply2 : homo (fun n => f n n).
Proof.
move=> n m hnm x.
apply /le_trans.
+ apply hmono1.  exact: hnm.
by apply: hmono2.
Qed.

Lemma leub_dlim_dlim1 :
  \dlim_(n) dlim (f n) <=1 \dlim_(n) (f n n).
Proof.
apply: leub_dlim => n.
apply: leub_dlim => m x.
apply: (@le_trans _ _ (f (maxn n m) (maxn n m) x)).
  apply: (@le_trans _ _ (f (maxn n m) m x)).
  - apply: hmono1; exact: leq_maxl.
  - apply: hmono2; exact: leq_maxr.
apply: dlim_ub.
exact : dhomo_apply2.
Qed.

Lemma dlim_dlim_ub1 :
  \dlim_(n) (f n n) <=1 \dlim_(n) dlim (f n).
Proof.
apply: leub_dlim => n x.
apply: (@le_trans _ _ (dlim (f n) x)).
- apply: dlim_ub.
  by move=> *; apply: hmono2.
- apply: dlim_ub.
  move => *.
  apply le_dlim => ??.
  by apply: hmono1.
Qed.

Lemma leub_dlim_dlim2 :
  \dlim_(m) (\dlim_(n) (f n m)) <=1 \dlim_(n) (f n n).
Proof.
apply: leub_dlim => n.
apply: leub_dlim => m x.
apply: (@le_trans _ _ (f (maxn n m) (maxn n m) x)).
  apply: (@le_trans _ _ (f (maxn n m) n x)).
  - apply: hmono1; exact: leq_maxr.
  - apply: hmono2; exact: leq_maxl.
apply: dlim_ub.
exact : dhomo_apply2.
Qed.

Lemma dlim_dlim_ub2 :
\dlim_(n) (f n n) <=1 \dlim_(m) (\dlim_(n) (f n m)).
Proof.
apply: leub_dlim => n x.
apply: (@le_trans _ _ (dlim (fun k => f k n) x)).
- apply: dlim_ub.
  by move=> *; apply: hmono1.
- apply: dlim_ub.
  move=> * ;apply le_dlim => ??.
  by apply: hmono2.
Qed.

Lemma dlim_dlim_com :
\dlim_(n) (dlim (f n)) =1 \dlim_(m) (\dlim_(n) (f n m)).
Proof.
move=> x; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (le_trans (leub_dlim_dlim1 x) (dlim_dlim_ub2 x)).
- exact: (le_trans (leub_dlim_dlim2 x) (dlim_dlim_ub1 x)).
Qed.

End DLimDLim.

Section dlet_dlim_diag.
Context {R : realType} {T U : choiceType}.
Context (d : (R.-pmf T)^nat) (h : nat -> T -> R.-pmf R).
Context (hd : homo d).
Context (hmono: (forall k n1 n2, (n1 <= n2)%N -> h n1 k <=1 h n2 k)).

Lemma dhomo_nmu_dlet (nmu : nat -> R.-pmf T) :
  homo nmu -> homo (fun n => dlet (h n) (nmu n)).
Proof.
move=> hnmu n m hnm x.
apply: le_dlet.
+ by move => ?; apply: hnmu.
move => ???; exact: hmono.
Qed.

Lemma dlet_dlim_diag_n :
  forall n, \dlet_(x <- d n) (\dlim_(n) (h n x))  <=1 \dlim_(n) (dlet (h n) (d n)).
Proof.
move=> n u; rewrite -(dlim_let hmono).
apply: leub_dlim => m w.
apply: (@le_trans _ _ ((\dlet_(i <- d (maxn m n)) h (maxn m n) i) w));
  last exact: (@dlim_ub _ _ (fun n => dlet (h n) (d n)) (maxn m n) (dhomo_nmu_dlet hd)).
apply: le_dlet.
+ move=> x; apply: hd; exact: leq_maxr.
by move=> ? _; apply: hmono; exact: leq_maxl.
Qed.

Lemma dlet_dlim_diag :
  \dlet_(x <- dlim d) (\dlim_(n) (h n x)) =1 \dlim_(n) (dlet (h n) (d n)).
Proof.
have hnd := dhomo_dnd hd.
move=> z; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite dlet_lim//; apply: leub_dlim => n.
  exact: dlet_dlim_diag_n.
- apply: leub_dlim => n; apply: le_dlet.
  + exact: (@dlim_ub _ _ d n hd).
move=> x _.
apply: dlim_ub.
by move=> *; exact: hmono.
Qed.

End dlet_dlim_diag.

(* -------------------------------------------------------------------- *)
Section Marginals.
Variable (R : realType) (T U : choiceType) (h : T -> U) (mu : R.-pmf T).

Definition dmargin := \dlet_(x <- mu) (dunit (h x)).

Lemma dmarginE : dmargin = \dlet_(y <- mu) (dunit (h y)).
Proof. by []. Qed.
End Marginals.

(* -------------------------------------------------------------------- *)
Section MarginalsTh.
Context {R : realType} {T U V : choiceType}.

Lemma dmargin_psumE (mu : R.-pmf T) (f : T -> U) y :
  (dmargin f mu) y = fine (esum [set:T] (fun x => ((f x == y)%:R * mu x)%:E)).
Proof.
rewrite dmarginE dletE.
congr fine.
apply/eq_esum => x _.
by rewrite mulrC dunit1E.
Qed.

Lemma dlet_dmargin (mu : R.-pmf T) (f : T -> U) (g : U -> R.-pmf V):
  \dlet_(u <- dmargin f mu) g u =1 \dlet_(t <- mu) (g (f t)).
Proof.
move=> x; rewrite dlet_dlet; apply: eq_in_dlet=> //.
by move=> y _ z /=; rewrite dlet_unit.
Qed.

Lemma dmargin_dlet (mu : R.-pmf T) (f : U -> V) (g : T -> R.-pmf U):
  dmargin f (\dlet_(t <- mu) g t) =1 \dlet_(t <- mu) (dmargin f (g t)).
Proof. by apply/dlet_dlet. Qed.

Lemma dmargin_dunit (t : T) (f : T -> U):
  dmargin f (dunit t) =1 dunit (f t) :> R.-pmf U.
Proof. by apply/dlet_unit. Qed.
End MarginalsTh.

(* -------------------------------------------------------------------- *)
Section MeasureOfDmargin.
Context {R : realType} {T U : choiceType}.

Local Open Scope ereal_scope.

Lemma measure_of_pmf_dmargin (h : T -> U) (mu : R.-pmf T)
    (S : set (discrete_measurable_space U)) :
  measure_of_pmf (dmargin h mu) S
    = giry_map (measurable_fun_discreteT h) (measure_of_pmf mu) S.
Proof.
rewrite /dmargin measure_of_pmf_dlet.
under eq_integral do rewrite measure_of_pmf_dunit diracE.
by rewrite /giry_map/= /pushforward -(setIT (h @^-1` S)) -integral_indic.
Qed.

End MeasureOfDmargin.

Abbreviation dfst mu := (dmargin fst mu).
Abbreviation dsnd mu := (dmargin snd mu).

(* -------------------------------------------------------------------- *)
Section DSwap.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Definition dswap : R.-pmf (B * A)%type :=
  dmargin (fun xy => (xy.2, xy.1)) mu.
End DSwap.

(* -------------------------------------------------------------------- *)
Section DSwapCoreTheory.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Lemma dswapE xy : dswap mu xy = mu (xy.2, xy.1).
Proof.
rewrite /= dletE (esumID ([set (xy.2, xy.1)]%classic)).
+ by move=> ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move=> ab [_ h] /=.
  rewrite dunit_diff ?mulr0 // => heq; apply: h.
  by rewrite -heq /= -surjective_pairing.
by case: xy => x y /=; rewrite dunit_id mulr1 addr0.
Qed.

End DSwapCoreTheory.

(* -------------------------------------------------------------------- *)
Section DSwapTheory.
Context {R : realType} {A B : choiceType} (mu : R.-pmf (A * B)%type).

Lemma dswapK : dswap (dswap mu) =1 mu.
Proof. by case=> x y; rewrite !dswapE. Qed.

Lemma dinsupp_swap xy : (xy.2, xy.1) \in dinsupp mu ->
  xy \in dinsupp (dswap mu).
Proof.
by move=> h; apply/dinsuppP; rewrite dswapE; apply/dinsuppPn.
Qed.

Lemma dfst_dswap : dfst (dswap mu) =1 dsnd mu.
Proof.
move=> z; rewrite /dmargin dlet_dlet => /= .
apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.

Lemma dsnd_dswap : dsnd (dswap mu) =1 dfst mu.
Proof.
move=> z; rewrite /dmargin dlet_dlet; apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.
End DSwapTheory.

(* -------------------------------------------------------------------- *)
Section DFst.
Context {R : realType} {T U : choiceType}.

Lemma dfstE (mu : R.-pmf (T * U)%type) x :
  dfst mu x = fine (esum [set:U] (fun y => (mu (x, y))%:E)).
Proof.
rewrite dmarginE dletE; congr fine.
rewrite (esumID [set z : T * U | z.1 = x]).
+ by move=> z _; rewrite lee_tofin // mulr_ge0.
rewrite [X in _ + X]esum1.
+ by move=> z [_ /= zx]; rewrite dunit_diff // ?mulr0 //=.
rewrite adde0.
rewrite (reindex_esum [set: U] _ (fun y => (x, y))).
  split.
  - by move=> y _; split.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z [_ /= zx]; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
by apply: eq_esum => y _ /=; rewrite dunit_id mulr1.
Qed.

Lemma summable_fst (mu : R.-pmf (T * U)%type) x :
  esummable [set:U] (fun y => (mu (x, y))%:E).
Proof.
rewrite /esummable; apply: le_lt_trans (@subpmf_summable _ _ mu).
rewrite -(reindex_esum [set:U] [set z : T * U | z.1 = x]
  (fun y => (x, y)) (fun z => (`|(mu z)%:E|)%E)).
+ split.
  - by move=> y _.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z /= zx; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
apply: subset_esum => //=.
by move=> z _; rewrite lee_tofin // mulr_ge0.
Qed.
End DFst.

(* -------------------------------------------------------------------- *)
Section DSnd.
Context {R : realType} {T U : choiceType}.

Lemma dsndE (mu : R.-pmf (T * U)%type) y :
  dsnd mu y = fine (esum [set:T] (fun x => (mu (x, y))%:E)).
Proof.
  by rewrite -dfst_dswap dfstE; congr fine; apply/eq_esum=> x; rewrite dswapE.
Qed.

Lemma summable_snd (mu : R.-pmf (T * U)%type) y :
  esummable [set:T] (fun x => (mu (x, y))%:E).
Proof.
have := summable_fst (dswap mu) y; apply/eq_esummable.
by move=> x /=; rewrite dswapE.
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
rewrite (eq_esum _ _ (fun x=> `|(F x)%:E * (mu x)%:E|)%E).
  move=> x _; rewrite -EFinM //=.
apply: esummableMl; last exact: subpmf_summable.
exists M%:E => [x ?|]; last by [].
by rewrite /= lee_fin; exact: leM x.
Qed.

Lemma esummable_pmf mu F : esummable [set: T] (EFin \o F) -> pmf_esummable mu F.
Proof.
move=> smF; rewrite /pmf_esummable /esummable.
rewrite (eq_esum _ _ (fun x=> `|(F x)%:E * (mu x)%:E|)%E).
  by move=> x _; rewrite -EFinM.
apply: esummableMr; last exact: smF.
exists 1%:E => [x ?|]; last by [].
by rewrite /= lee_fin ger0_norm// subpmf_le1.
Qed.

End pmf_esummable_lemmas.

(* TODO: move (generic lemma) *)
Lemma fineMK {R : realDomainType} (a b : \bar R):
  (0 <= b)%E -> a \is a fin_num ->
  fine (a * b) = fine a * fine b.
Proof.
move => hp.
move /(elimT (EFin_fin_numP a)) => [r] ->.
case h: b => //=; last first. by move : hp; rewrite h.
have [hc|hc|->] := comparable_ltgtP (comparableT r 0).
+ rewrite lt0_muley => //=.
  by rewrite mulr0.
+ rewrite  gt0_muley => //=.
  by rewrite mulr0.
by rewrite mul0e //= mulr0.
Qed.

Section pmf_expectation_lemmas.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T).

Lemma pmf_expectationZ mu f c : (forall x, 0 <= f x) ->
  \E_[mu] (fun x => c * (f x)) = c * (\E_[mu] f).
Proof.
move => h1; rewrite /pmf_expectation.
under eq_esum => x do rewrite /= -mulrA EFinM.
have hpos :  forall x : T, (0%R <= (f x * mu x)%:E)%E.
+ by move=> x; rewrite lee_fin; apply: mulr_ge0; [exact: h1|].
rewrite esumZ //=.
have hsum : (0 <= \esum_(i in [set: T]) (f i * mu i)%:E)%E.
+ by apply esum_ge0 => ??.
by rewrite fineMK.
Qed.

Lemma pmf_expectation_cst mu r : \E_[mu] (fun=> r) = \P_[mu] predT * r.
Proof.
have := pmf_expectationZ mu (f := fun=> 1%R) r.
rewrite mulr1 => -> //=.
by rewrite mulrC; congr (_ * _).
Qed.

Lemma pmf_expectation0 mu : \E_[mu] (fun=> 0) = 0.
Proof. by rewrite pmf_expectation_cst mulr0. Qed.

Lemma eq_pmf_expectation mu (f1 f2 : T -> R):
   {in dinsupp mu, f1 =1 f2} -> \E_[mu] f1 = \E_[mu] f2.
Proof.
move=> eq_f; rewrite /pmf_expectation; congr fine.
apply/eq_esum => x /=.
case/boolP: (x \in dinsupp mu).
+ by move/eq_f => ->.
+ by move/dinsuppPn => ->; rewrite !mulr0.
Qed.

Lemma pmf_expectationE mu (g : T -> R) :
  \E_[mu] g = fine ('E_(measure_of_pmf mu) [EFin \o g]).
Proof. by rewrite expectation_pmf. Qed.

Lemma pmf_expectationB mu (f g : T -> R) :
  pmf_esummable mu f -> pmf_esummable mu g ->
  \E_[mu] (f \- g) = \E_[mu] f - \E_[mu] g.
Proof.
move=> sf sg.
rewrite !pmf_expectationE.
rewrite expectationB//; [exact/Lfun1_integrable/integrable_esummable_new..|].
by rewrite fineB// expectation_pmfEFin esummable_esum_fin_num.
Qed.

Lemma pmf_expectation_ge0 mu (g : T -> R) :
  (forall y, 0 <= g y) -> 0 <= \E_[mu] g.
Proof.
move=> g0.
rewrite /pmf_expectation fine_ge0// esum_ge0// => x _.
by rewrite lee_fin mulr_ge0.
Qed.

End pmf_expectation_lemmas.

Section EspeCoreTheory.
Context {R : realType} {T : choiceType}.
Implicit Types (mu : R.-pmf T) (A B E : pred T).

Local Open Scope ereal_scope.

Lemma eexp_dunit (f : T -> \bar R) (x : T) : 'E_(measure_of_pmf (dunit x)) [f] = f x.
Proof.
rewrite expectation_def (eq_measure_integral (\d_(x : discrete_measurable_space T))).
  by move=> A _ _; exact: measure_of_pmf_dunit.
by rewrite integral_dirac//= diracT mul1e.
Qed.

Lemma eexp_dnull (f : T -> \bar R) :
  'E_(measure_of_pmf (dnull : R.-pmf T)) [f] = 0.
Proof.
rewrite expectation_def (eq_measure_integral mzero).
  by move=> A _ _; exact: measure_of_pmf_dnull.
by rewrite integral_measure_zero.
Qed.

Lemma eexp_dlet {U: choiceType} mu (nu : T -> R.-pmf U) F :
  (forall x, 0 <= F x)%E ->
  'E_(measure_of_pmf (dlet nu mu)) [F] =
  'E_(measure_of_pmf mu) [fun x => 'E_(measure_of_pmf (nu x)) [F]].
Proof.
move=> HF; rewrite !expectation_def.
under [in RHS]eq_integral do rewrite expectation_def.
rewrite (eq_measure_integral (giry_bind (measure_of_pmf mu) (measurable_measure_of_pmf nu))).
  by move=> A _ _; exact: measure_of_pmf_dlet_bind.
by apply: giry_int_bind.
Qed.

Lemma eexp_dmargin {U : choiceType} (h : T -> U) mu (F : U -> \bar R) :
  (forall y, 0 <= F y)%E ->
  'E_(measure_of_pmf (dmargin h mu)) [F] = 'E_(measure_of_pmf mu) [F \o h].
Proof.
move=> F0; rewrite !expectation_def.
rewrite (eq_measure_integral
  (giry_map (measurable_fun_discreteT h) (measure_of_pmf mu))).
  by move=> A _ _; exact: measure_of_pmf_dmargin.
by apply: giry_int_map.
Qed.

Local Open Scope ereal_scope.

Lemma eexp_dlet_esp {U: choiceType} mu (nu : T -> R.-pmf U) (g : U -> R) :
  (forall y, 0 <= g y)%R -> (forall eta, pmf_esummable eta g) ->
  'E_(measure_of_pmf (dlet nu mu)) [EFin \o g] =
  'E_(measure_of_pmf mu) [EFin \o (fun x => \E_[nu x] g)].
Proof.
move=> g0 sg.
rewrite (eexp_dlet mu nu)//= !expectation_pmf.
apply: eq_esum => t _ //=.
rewrite expectation_pmf.
congr (_ * _)%E.
rewrite /pmf_expectation fineK//.
exact: (esummable_esum_fin_num (sg (nu _))).
Qed.

End EspeCoreTheory.

(* -------------------------------------------------------------------- *)
Section espe_pmf.
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
move=> mf f0.
rewrite unlock /= -ge0_integral_distribution//.
have mid : measurable_fun [set: discrete_measurable_space R]
    (idfun : discrete_measurable_space R -> R).
  by move=> _ Y _.
transitivity (\int[giry_map mid (measure_of_pmf pmfX)]_y f y).
  by symmetry;  apply: giry_int_map.
apply: eq_measure_integral => A mA _.
exact: measure_of_pmf_distribution.
Qed.

Lemma expectation_pmf_RV (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  'E_(measure_of_pmf pmfX) [f] = \int[P]_w f (X w).
Proof.
move=> mf; rewrite unlock integralE [RHS]integralE; congr (_ - _).
- rewrite -[LHS]expectation_def ge0_expectation_pmf => //=;
    first exact: measurable_funepos.
  by apply: eq_integral => w _; rewrite !funeposE.
- rewrite -[LHS]expectation_def ge0_expectation_pmf => //=;
    first exact: measurable_funeneg.
  by apply: eq_integral => w _; rewrite !funenegE.
Qed.

Lemma expectation_pmf_dRV : 'E_(measure_of_pmf pmfX) [EFin] = 'E_P[EFin \o X].
Proof. by rewrite expectation_pmf_RV //= unlock. Qed.

End espe_pmf.

(* -------------------------------------------------------------------- *)
Section PrCoreTheory.
Context {R : realType} {T : choiceType}.

Implicit Types (mu : R.-pmf T) (A B E : pred T).

Lemma summable_pr E mu : esummable [set:T] (fun x => ((E x)%:R * mu x)%:E).
Proof.
apply/(le_esummable (g := EFin \o mu)) => [x _|//].
rewrite !lee_tofin//=.
  by rewrite mulr_ge0.
by rewrite ler_piMl //= lern1 leq_b1.
Qed.

Lemma prE_measure mu E :
  (\P_[mu] E)%:E = measure_of_pmf mu [set` E].
Proof.
have fin : \esum_(x in [set: T]) ((E x)%:R * mu x)%:E \is a fin_num.
  rewrite esum_abse.
    by move=> ?; rewrite mulr_ge0.
  by have := summable_pr E mu; rewrite esummableE.
rewrite /pr fineK//.
rewrite /measure_of_pmf [RHS]esum_mkcond esum_setT_discrete.
apply: eq_esum => x _ /=.
have -> : (x \in [set` E]) = E x by apply/idP/idP => [/set_mem//|/mem_set//].
by case: (E x); rewrite ?mul1r ?mul0r.
Qed.

Lemma pr_pred0 mu : \P_[mu] pred0 = 0.
Proof. by rewrite /pr esum1 // => x /=; rewrite mul0r. Qed.

Lemma pr_pred1 mu x : mu x = \P_[mu] (pred1 x).
Proof.
rewrite /pr.
rewrite (eq_esum _ _ (fun y => if x == y then (mu y)%:E else 0)); last first.
+ by rewrite esum_if_eq_op_set1.
move=> y _ /=; rewrite [y == x]eq_sym.
by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
Qed.

Lemma pr_exp mu (Q : pred T) : \P_[mu] Q = \E_[mu] (fun m => (Q m)%:R).
Proof. by []. Qed.

Lemma pr_predT mu : \P_[mu] predT = fine (esum [set: T] (EFin \o mu)).
Proof.
rewrite /pr /pmf_expectation; congr fine.
by apply/eq_esum=> x; rewrite mul1r.
Qed.

Lemma expectation_pmf_cst mu r : ('E_(measure_of_pmf mu) [cst r] = (\P_[mu] predT)%:E * r)%E.
Proof.
rewrite expectation_pmf.
rewrite esumZ.
  by move=> ?; rewrite lee_fin.
rewrite muleC; congr (_ * _)%E.
rewrite pr_predT.
rewrite fineK//=.
rewrite esum_abse//=.
have := @subpmf_summable _ _ mu.
by rewrite esummableE.
Qed.

Lemma exp_dunit (f : T -> R) (x : T) : \E_[dunit x] f = f x.
Proof. by rewrite /pmf_expectation -expectation_pmfEFin eexp_dunit. Qed.

Lemma pr_dunit E x : \P_[dunit x] E = (E x)%:R :> R.
Proof. by rewrite pr_exp exp_dunit. Qed.

Lemma exp_dnull (f : T -> R) : \E_[dnull : R.-pmf T] f = 0.
Proof. by rewrite /pmf_expectation -expectation_pmfEFin eexp_dnull. Qed.

Lemma pr_dnull E : \P_[dnull : R.-pmf T] E = 0.
Proof. by rewrite pr_exp exp_dnull. Qed.

Lemma dweight_dnull : dweight (dnull : R.-pmf T) = 0.
Proof. exact: pr_dnull. Qed.

Lemma exp_dmargin {U : choiceType} (h : T -> U) mu (g : U -> R) :
  (forall y, 0 <= g y) -> \E_[dmargin h mu] g = \E_[mu] (g \o h).
Proof.
move=> g0.
have g0E y : (0 <= (EFin \o g) y)%E by rewrite /= lee_fin.
by rewrite /pmf_expectation -!expectation_pmfEFin (eexp_dmargin h mu g0E).
Qed.

Lemma pr_ge0 A mu : 0 <= \P_[mu] A.
Proof. by rewrite -lee_fin prE_measure. Qed.

Lemma prc_ge0 A B mu : 0 <= \P_[mu, B] A.
Proof. by rewrite /prc mulr_ge0 ?invr_ge0 // pr_ge0. Qed.

Lemma eq_in_pr A B mu : {in dinsupp mu, A =i B} -> \P_[mu] A = \P_[mu] B.
Proof.
move=> eq_AB; rewrite /pr; congr fine.
apply/eq_esum => x _ /=.
case/boolP: (x \in dinsupp mu).
+ by move/eq_AB; rewrite -!topredE => /= ->.
+ by move/dinsuppPn => ->; rewrite !mulr0.
Qed.

Lemma eq_pr A B mu : A =i B -> \P_[mu] A = \P_[mu] B.
Proof. by move=> eq_AB; apply/eq_in_pr=> x _; apply/eq_AB. Qed.

Lemma pr_pred0_eq (mu : R.-pmf T) (E : pred T) :
  E =1 pred0 -> \P_[mu] E = 0.
Proof. by move=> eq; rewrite -(pr_pred0 mu); apply/eq_pr. Qed.

End PrCoreTheory.

(* -------------------------------------------------------------------- *)
Section PrTheory.
Context {R : realType} {T U : choiceType} {I : eqType}.

Implicit Types (mu : R.-pmf T) (A B E : pred T).

Lemma prE (nu : R.-pmf T) (E : pred T) :
  (\P_[nu] E)%:E = \esum_(t in [set: T]) ((E t)%:R * nu t)%:E.
Proof.
rewrite /pr fineK// esum_abse//.
+ by move => ?; rewrite mulr_ge0.
by have := summable_pr E nu; rewrite esummableE.
Qed.

Lemma EFin_esumZ {J : choiceType} {c : R} {a : J -> R} :
  0 <= c -> (forall i, 0 <= a i) ->
  \esum_(i in [set: J]) (c * a i)%:E = (c%:E * \esum_(i in [set: J]) (a i)%:E)%E.
Proof.
move=> c0 a0; rewrite -esumZ.
- by move=> i ?; rewrite lee_fin; exact: a0.
- by apply: eq_esum => i _; rewrite EFinM.
Qed.

Lemma eq0_pr A mu :
  (forall x, x \in dinsupp mu -> x \notin A) -> \P_[mu] A = 0.
Proof.
move=> h; rewrite /pr esum1 //= => x ?.
have -> // : (A x)%:R * mu x = 0.
apply /eqP; rewrite mulf_eq0 orbC; case/boolP: (mu x == 0) => //=.
by move/h; rewrite -topredE /= => /negbTE->.
Qed.

Lemma eq0_prc A B mu :
    (forall x, x \in dinsupp mu -> x \in B -> x \notin A)
  -> \P_[mu, B] A = 0.
Proof.
move=> h; rewrite /prc eq0_pr ?mul0r // => x /h {h} /orb_idl.
by rewrite negb_and /= => <-; rewrite orbAC orbN.
Qed.

Lemma subset_pr A B mu : {subset B <= A} -> \P_[mu] B <= \P_[mu] A.
Proof.
move=> le_BA; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
rewrite ler_wpM2r // ?ge0_mu.
rewrite ler_nat; have := le_BA x; rewrite -!topredE /=.
by case: (B x) => // ->.
Qed.

Lemma le1_pr A mu : \P_[mu] A <= 1.
Proof.
apply: (@le_trans _ _ \P_[mu] predT); first by apply/subset_pr.
rewrite pr_predT -fine1; apply: fine_le; [|by []|exact: subpmf_sum_le1].
rewrite ge0_fin_numE; last first.
 by apply: le_lt_trans; [exact: subpmf_sum_le1|rewrite ltey].
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

Lemma pr_dlet E f (mu : R.-pmf U) :
  \P_[dlet f mu] E = \E_[mu] (fun x => \P_[f x] E).
Proof.
have fin : esummable [set: U] (fun x => ((\P_[f x] E) * mu x)%:E).
  apply/(le_esummable (g := EFin \o mu)) => [x _|//].
  by rewrite !lee_fin mulr_ge0 ?pr_ge0//= ler_piMl ?le1_pr.
apply: EFin_inj; rewrite prE_measure measure_of_pmf_dlet.
under eq_integral do rewrite -prE_measure.
rewrite -expectation_def expectation_pmfEFin /pmf_expectation fineK//.
exact: esummable_esum_fin_num.
Qed.

Lemma pr_dmargin E f (mu : R.-pmf U) :
  \P_[dmargin f mu] E = \P_[mu] [pred x | f x \in E].
Proof.
by rewrite /dmargin pr_dlet pr_exp; apply/eq_pmf_expectation=> x _; rewrite pr_dunit.
Qed.

Lemma le_exp mu f1 f2 : pmf_esummable mu f1 -> pmf_esummable mu f2 ->
  f1 <=1 f2 -> \E_[mu] f1 <= \E_[mu] f2.
Proof.
move=> sm1 sm2 le_f; rewrite /pmf_expectation; apply: fine_le.
- exact: (esummable_esum_fin_num sm1).
- exact: (esummable_esum_fin_num sm2).
- apply: le_esum.
  move=> x /=; have hf := le_f x.
  by rewrite lee_fin ler_wpM2r // ?ge0_mu.
Qed.

Lemma le_in_pr E1 E2 mu :
  (forall x, x \in dinsupp mu -> x \in E1 -> x \in E2) ->
    \P_[mu] E1 <= \P_[mu] E2.
Proof.
move=> le; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP: (x \in dinsupp mu) => [xin|/dinsuppPn ->]; last by rewrite !mulr0.
have hE : (E1 x)%:R <= (E2 x)%:R :> R.
  rewrite ler_nat; have := le x xin; rewrite -!topredE /=.
  by case: (E1 x) => // ->.
by rewrite ler_wpM2r // ?ge0_mu.
Qed.

Lemma le_mu_pr A mu nu :
    (forall x, x \in dinsupp nu -> x \in A -> nu x <= mu x)
  -> \P_[nu] A <= \P_[mu] A.
Proof.
move=> h; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP: (x \in dinsupp nu) => [/h {}h|]; last first.
  by move/dinsuppPn=> ->; rewrite mulr0; apply: mulr_ge0; [exact: ler0n|].
by case/boolP: (A x) => [/h|]; rewrite ?(mul0r, mul1r).
Qed.

Lemma prc_le1 A B mu : \P_[mu, B] A <= 1.
Proof.
move: (pr_ge0 B mu); rewrite /prc le_eqVlt.
case/orP=> [/eqP<-|]; first by rewrite invr0 mulr0 ler01.
move/ler_pdivrMr=> ->; rewrite mul1r.
by apply: le_in_pr => x _ /andP[].
Qed.

Lemma prc_sum A mu : 0 < \P_[mu] A ->
 fine(esum [set: T] (fun x => (\P_[mu, A] (pred1 x))%:E)) = 1.
Proof.
move=> gt0.
have a0 : forall i, 0 <= (A i)%:R * mu i.
  by move=> i; apply: mulr_ge0; [exact: ler0n|].
have hpr1 : forall x, \P_[mu] [predI pred1 x & A] = (A x)%:R * mu x.
  move=> x; rewrite /pr.
  rewrite (eq_esum _ _ ( fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
    move=> y _ /=; rewrite !inE [y == x]eq_sym.
    by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
  by rewrite esum_if_eq_op_set1.
rewrite (eq_esum _ _ (fun x => ((\P_[mu] A)^-1 * ((A x)%:R * mu x))%:E)).
 by move=> x _; rewrite /prc hpr1; congr (_ %:E); rewrite mulrC.
rewrite (EFin_esumZ _ a0); last first. rewrite -prE -EFinM mulVf //.
+ by rewrite gt_eqF.
by rewrite invr_ge0// pr_ge0.
Qed.

Lemma pr_eq0 mu E : \P_[mu] E = 0 -> forall x, x \in E -> mu x = 0.
Proof.
move=> hE x xE.
have hle : \P_[mu] (pred1 x) <= \P_[mu] E.
  by apply: subset_pr => y; rewrite !inE => /eqP ->.
move: hle; rewrite hE -pr_pred1 => h.
by apply/eqP; rewrite eq_le h /=.
Qed.

Lemma prID A B mu :
  \P_[mu] A = \P_[mu] [predI A & B] + \P_[mu] [predI A & predC B].
Proof.
have ge0 : forall (P : pred T) i, (0 <= ((P i)%:R * mu i)%:E)%E.
  by move=> P i; rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
by case: (A x); case: (B x).
Qed.

Lemma pr_or_indep (A B : pred T) (mu : R.-pmf T) :
  (forall x, x \in A -> x \notin B) ->
    \P_[mu] [predU A & B] = \P_[mu] A + \P_[mu] B.
Proof.
move=> dsj.
have ge0 : forall (P : pred T) i, (0 <= ((P i)%:R * mu i)%:E)%E.
  by move=> P i; rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
case/boolP: (A x) => Ax; case/boolP: (B x) => Bx //=.
by move/dsj: Ax; rewrite -topredE /= Bx.
Qed.

Lemma pr_mem_map f mu (r : seq U) : uniq r ->
    \P_[mu] [pred x | f x \in r]
  = \sum_(y <- r) \P_[mu] [pred x | f x == y].
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pr_pred0_eq //.
case/andP=> yNr /ih {ih}h; rewrite big_cons -h -pr_or_indep.
  by move=> x; rewrite !inE => /eqP->. by apply/eq_pr.
Qed.

Lemma pr_mem mu (r : seq T) : uniq r ->
  \P_[mu] [pred x | x \in r] = \sum_(x <- r) mu x.
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pr_pred0_eq //.
case/andP=> yNr /ih {ih}h; rewrite big_cons /= pr_pred1.
by rewrite -h -pr_or_indep // => x /eqP ->.
Qed.

Lemma pr_bigor_indep mu (P : I -> pred T) (r : seq I) :
    uniq r
  -> (forall p1 p2 x, p1 != p2 -> p1 \in r -> p2 \in r -> x \in P p1 -> x \notin P p2)
  -> \P_[mu] [pred x | has [pred p | x \in P p] r]
  = \sum_(p <- r) \P_[mu] (P p).
Proof.
move=> uq_r dj; pose S x := \big[orb/false]_(p <- r) (x \in P p).
rewrite (eq_pr (B := S)) => [x|]; first by rewrite !inE -big_has.
rewrite {}/S; elim: r uq_r dj => [_|p r ih /andP[pNr /ih {ih}h]] dj.
 by rewrite big_nil pr_pred0_eq // => x; rewrite big_nil.
rewrite big_cons -h => [p1 p2 x ne_p p1r p2r|].
 by apply/dj=> //; rewrite in_cons (p1r, p2r) orbT.
rewrite -pr_or_indep => [x xNPp|].
  rewrite -topredE /= big_has; apply/hasPn => y y_in_r.
  apply/(dj p); rewrite ?in_cons ?(eqxx, y_in_r, orbT) //.
  by apply/contra: pNr=> /eqP->.
by apply/eq_pr=> x; rewrite -!topredE /= big_cons.
Qed.

Lemma pr_or A B mu : \P_[mu] [predU A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predI A & B].
Proof.
apply/eqP; rewrite eq_sym subr_eq [in X in _==X]addrC; apply/eqP.
rewrite (prID _ B) -addrA -pr_or_indep => [x|].
  by rewrite !inE => /andP[].
congr (_ + _); apply/eq_pr => x; rewrite !inE -!topredE /=.
by apply/orb_id2r => /negbTE ->; rewrite andbT.
Qed.

Lemma pr_and A B mu : \P_[mu] [predI A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predU A & B].
Proof. by rewrite pr_or subKr. Qed.

Lemma ler_pr_or A B mu : \P_[mu] [predU A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_or lerBlDr lerDl pr_ge0. Qed.

Lemma ler_pr_and A B mu : \P_[mu] [predI A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_and lerBlDr lerDl pr_ge0. Qed.

Lemma pr_predC E mu: \P_[mu](predC E) = \P_[mu] predT - \P_[mu] E.
Proof.
apply/esym/eqP; rewrite subr_eq -pr_or_indep //.
by apply/eqP/eq_pr=> x; rewrite !inE orNb.
Qed.

Lemma pr_split B A mu : \P_[mu] A =
    \P_[mu]        B  * \P_[mu,       B] A
  + \P_[mu] (predC B) * \P_[mu, predC B] A.
Proof.
suff h A' B': \P_[mu] [predI A' & B'] = \P_[mu] B' * \P_[mu, B'] A'.
  by rewrite (prID _ B); congr (_ + _); apply/h.
rewrite /prc mulrCA; have [] := eqVneq (\P_[mu] B') 0; last first.
  by move=> nzPB'; rewrite divff // mulr1.
move=> zPB'; rewrite zPB' invr0 !mulr0; apply/eq0_pr.
move=> x mux; move/pr_eq0: zPB' => /(_ x) h; rewrite !inE.
by apply/negP=> /andP[_ /h] /dinsuppP.
Qed.

Lemma prc_pred1 (mu : R.-pmf T) x A :
  prc mu (pred1 x) A = (A x)%:R * mu x / \P_[mu] A.
Proof.
rewrite /prc; congr (_ / _); rewrite /pr.
rewrite (eq_esum _ _ (fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
  move=> y _ /=; rewrite !inE [y == x]eq_sym.
  by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
by rewrite esum_if_eq_op_set1.
Qed.

Lemma summable_pr_f f mu (P : pred T):
  pmf_esummable mu f ->
  esummable [set: T] (EFin \o (fun x => (P x)%:R * (f x * mu x))).
Proof.
move=> sm; rewrite /esummable //= .
rewrite (eq_esum _ _ (fun x => `|((P x)%:R)%:E * (f x * mu x)%:E|)%E).
by move => i _ //; rewrite -abseM.
apply: esummableMl; last exact: sm.
exists 1%:E=> [x|]; last by [].
by rewrite gee0_abs ?lee_fin ?ler0n// lern1 leq_b1.
Qed.

Lemma sum_fin_num_mu_f f mu (P : pred T):
    pmf_esummable mu f ->
    esum [set:T] (EFin \o (fun x => (P x)%:R * (f x * mu x))) \is a fin_num.
Proof.
  move=> ?; apply: esummable_esum_fin_num;  exact: summable_pr_f.
Qed.

Lemma pr_esp_sum mu f (P : pred T):
  pmf_esummable mu f ->
  \P_[mu] P * \E_[mu, P] f =
  fine (esum [set: T] (EFin \o (fun x => (P x)%:R * (f x * mu x)))).
Proof.
move => sm.
  have [c0|cn0] := eqVneq (\P_[mu] P) 0.
rewrite c0 mul0r.
  suff -> : esum [set:T] (EFin \o (fun x => (P x)%:R * (f x * mu x))) = 0 by rewrite fine0.
  rewrite (esum.eq_esum _ _ (fun=> 0%E)) ?esum0// => x.
  suff h0 : (P x)%:R * mu x = 0 :> R by rewrite /= mulrCA h0 mulr0.
  case Hpx: (P x); last by rewrite mul0r.
  by rewrite (pr_eq0 c0 Hpx) mulr0.
rewrite /espc.
rewrite (esum.eq_esum _ _ (fun x => ((\P_[mu] P)^-1 %:E *
                (EFin \o (fun x => ((P x)%:R * (f x * mu x))%R)) x)%E)).
  move=> x ?; rewrite /= prc_pred1 -EFinM; congr (_ %:E).
  by rewrite mulrA mulrC; congr (_ * _); exact: mulrCA.
rewrite (esummable_esumZ _ (summable_pr_f P sm));
    first by rewrite abse_fin_num.
by rewrite fineM ?abse_fin_num ?sum_fin_num_mu_f// mulVKf.
Qed.

Lemma exp_split A f mu : pmf_esummable mu f -> \E_[mu] f =
    \P_[mu]        A  * \E_[mu,       A] f
  + \P_[mu] (predC A) * \E_[mu, predC A] f.
Proof.
move=> sm.
rewrite (pr_esp_sum A) // (pr_esp_sum (predC A)) // /pmf_expectation -fineD ?sum_fin_num_mu_f//.
congr fine; rewrite -(esummable_esumD (summable_pr_f A sm) (summable_pr_f (predC A) sm)).
apply: esum.eq_esum => x ? /=; rewrite -EFinD; congr (_ %:E).
rewrite -mulrDl -[LHS]mul1r; congr (_ * _).
by rewrite -natrD; case: (A x).
Qed.

Lemma exp_le_bd mu F (M : R) :
  0 <= M -> (forall x, `|F x| <= M) -> \E_[mu] F <= M.
Proof.
move=> ge0M bd; apply/(@le_trans _ _ (\E_[mu] (fun _ => M))).
+ apply/le_exp.
  + by apply/bounded_pmf_esummable; exists M.
  + exact/pmf_esummable_cst.
  + by move=> x; apply/(le_trans _ (bd x))/ler_norm.
by rewrite pmf_expectation_cst ler_piMl // le1_pr.
Qed.

Lemma exp_dlet_ge0 (mu : R.-pmf T) (nu : T -> R.-pmf U) (g : U -> R) :
  (forall y, 0 <= g y) -> (forall eta, pmf_esummable eta g) ->
  \E_[dlet nu mu] g = \E_[mu] (fun x => \E_[nu x] g).
Proof.
move=> g0 sg.
rewrite [LHS]pmf_expectationE.
rewrite eexp_dlet_esp//.
by rewrite -pmf_expectationE.
Qed.

Lemma pmf_esummable_le {V : choiceType} (mu : R.-pmf V) (k h : V -> R) :
  (forall x, `|k x| <= `|h x|) -> pmf_esummable mu h -> pmf_esummable mu k.
Proof.
move=> kh; rewrite /pmf_esummable => fh.
rewrite esummableE ge0_fin_numE.
+ apply: esum_ge0 => i _; exact: abse_ge0.
apply: (le_lt_trans _ fh).
apply: le_esum.
by move => ??; rewrite lee_fin !normrM ler_wpM2r.
Qed.

Lemma hcomp (mu : R.-pmf T) (nu : T -> R.-pmf U) (g : U -> R) :
  (forall y, 0 <= g y) -> (forall eta, pmf_esummable eta g) -> pmf_esummable mu (fun x => \E_[nu x] g).
Proof.
move=> g0 sg.
have hge0 x : 0 <= \E_[nu x] g * mu x by rewrite mulr_ge0// pmf_expectation_ge0.
rewrite /pmf_esummable esummableE.
rewrite (esum.eq_esum _ _ (EFin \o (fun x => \E_[nu x] g * mu x))).
+ move=> x _ /=; rewrite ger0_norm //.
rewrite -expectation_pmfEFin -(eexp_dlet_esp mu nu g0 sg) expectation_pmfEFin.
exact: (esummable_esum_fin_num (sg (dlet nu mu))).
Qed.

Lemma exp_dlet mu (nu : T -> R.-pmf U ) F :
  (forall eta, pmf_esummable eta F) ->
    \E_[dlet nu mu] F = \E_[mu] (fun x => \E_[nu x] F).
Proof.
move=> sF.
have spF : forall eta, pmf_esummable eta F^\+.
+ by move=> eta //=; apply: (pmf_esummable_le (le_funrpos F) (sF eta)).
have snF : forall eta, pmf_esummable eta F^\-.
+ by move=> eta; apply: (pmf_esummable_le (le_funrneg F) (sF eta)).
transitivity (\E_[mu] (fun x => \E_[nu x] F^\+)
            - \E_[mu] (fun x => \E_[nu x] F^\-)).
rewrite -(exp_dlet_ge0 mu nu _ spF) // -(exp_dlet_ge0 mu nu _ snF) //.
rewrite -(pmf_expectationB (spF _) (snF _)); congr (\E_[dlet nu mu] _); exact/esym/funrposBneg.
rewrite -(pmf_expectationB (hcomp mu nu _ spF) (hcomp mu nu _ snF)) //.
apply: eq_pmf_expectation => x _ /=.
rewrite -(pmf_expectationB (spF _) (snF _)).
congr (\E_[nu x] _); exact : funrposBneg.
Qed.

End PrTheory.

(* -------------------------------------------------------------------- *)
Section mono_esum.
Context {R : realType} {T : choiceType} {f : (R.-pmf T)^nat}.

Hypothesis ndf : nd f.

Lemma mono_esum_Efn (E: T -> \bar R):
  (forall m, 0 <= E m)%E ->
  forall m n, (m <= n)%N ->
  (\esum_(x in [set:T]) (E x * (f m x)%:E) <= \esum_(x in [set:T]) (E x * (f n x)%:E))%E.
Proof.
move=> hE m n le_mn.
apply /esum.le_esum.
move => ??; rewrite lee_pmul => //=.
- rewrite lee_tofin //.
- rewrite lee_tofin //; exact: ndf.
Qed.

Lemma distr_lub_sup a :
  ((dlim f) a)%:E = ereal_sup (range (fun n => (f n a)%:E)).
Proof. exact: (dlim_sup ndf a). Qed.

Lemma esum_dlim_r [E : T -> \bar R]  [r : \bar R]:
  (forall m, 0 <= E m)%E ->
  (forall (n : nat), esum [set:T] (fun x : T => E x * (f n x)%:E) <= r)%E ->
  (esum [set:T] (fun x : T => E x * ((dlim f ) x)%:E) <= r)%E.
Proof.
move => hE h.
rewrite (@esum.eq_esum _ _ _ _ (fun x => ereal_sup (range (fun n =>  E x * (f n x)%:E)%E))).
- move => ??; rewrite distr_lub_sup.
  rewrite (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
  move => ??; rewrite lee_tofin //.
rewrite exchange_esum_ereal_sup //.
- by move => ??; rewrite mule_ge0 // lee_tofin.
- by move => ????; rewrite lee_pmul // ?lee_tofin // ; exact: ndf.
rewrite ge_ereal_sup//= => x [n s] <-.
exact: h.
Qed.

Lemma esum_dlim_r_r [E : T -> R]  [r : \bar R]:
  (forall m, 0 <= E m) ->
  (forall (n : nat), esum [set:T] (fun x : T => (E x * f n x)%:E) <= r)%E ->
  (esum [set:T] (fun x : T => (E x * (dlim f ) x)%:E) <= r)%E.
Proof.
move=> hE h.
rewrite (eq_esum _ _ (fun x : T => ((E x)%:E * ((dlim f) x)%:E)%E)).
+ by move => ? _; rewrite EFinM.
apply: (esum_dlim_r (E := fun x => (E x)%:E)).
- by move=> m; exact: (lee_tofin (hE m)).
- move=> n; under eq_esum => x _ do rewrite -EFinM.
  exact: h n.
Qed.

Lemma esum_dlim (E : pred T) :
  esum [set:T] (fun x : T => ((E x)%:R * (dlim f) x)%:E) =
    limn (fun n => esum [set:T] (fun x : T => ((E x)%:R * f n x)%:E)).
Proof.
have hmono : forall n m, (n <= m)%N -> forall x,
    (((E x)%:R * f n x)%:E <= ((E x)%:R * f m x)%:E)%E.
  move=> n m nm x; rewrite lee_fin; apply: ler_wpM2l; first exact: ler0n.
  by rewrite -lee_fin; exact: (ndf x nm).
transitivity (ereal_sup (range
    (fun n => esum [set:T] (fun x : T => ((E x)%:R * f n x)%:E)))); last first.
  by apply: sup_range_lim => n m nm; apply: le_esum => x _; exact: (hmono n m nm x).
rewrite -(@exchange_esum_ereal_sup R T (fun x n => ((E x)%:R * f n x)%:E)) //.
+ by move=> x n; rewrite lee_fin; apply: mulr_ge0; [exact: ler0n |].
+ move => x n m nm. exact: (hmono n m nm x).
apply: eq_esum => x _.
rewrite EFinM distr_lub_sup (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
+ by move=> t n; rewrite lee_fin.
+ by rewrite lee_tofin.
Qed.

End mono_esum.

(* -------------------------------------------------------------------- *)
Lemma distr_eqP {R : realType} {T : choiceType} (f1 f2 : R.-pmf T):
  f1 =1 f2 <-> f1 = f2.
Proof.
split=> [|->] //.
case: f1 => f1 [[]ge0_1 s1 le1_1].
case: f2 => f2 [[]ge0_2 s2 le1_2].
move => /funext /= h.
by subst;f_equal; f_equal; f_equal.
Qed.
