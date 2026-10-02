From HB Require Import structures.
From mathcomp Require Import boot order algebra finmap.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal sequences esum measure.
From mathcomp Require Import simple_functions lebesgue_integral_definition
  lebesgue_integral_nonneg.

(**md**************************************************************************)
(* #                                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*   discrete_measurable_space == alias for the type of discrete measurable   *)
(*                                types                                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Section discrete_counting.
Local Open Scope ereal_scope.
Context {R : realType} {T : choiceType}.
Let U := discrete_measurable_space T.
Implicit Type u : U.

Lemma counting_set1 u : counting [set u] = 1 :> \bar R.
Proof. by rewrite /counting (asboolT (finite_set1 u)) fset_set1 cardfs1. Qed.

Lemma counting_esum_cst (c : R) (A : set T) : (0 <= c)%R ->
  c%:E * @counting U R A = \esum_(x in A) c%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-|c0]; first by rewrite mul0e esum1.
have [finA|infA] := pselect (finite_set A); last first.
  by rewrite /counting asboolF// mulry gtr0_sg// mul1e infinite_esum_cst.
rewrite /counting (asboolT finA)//.
rewrite esum_fset//; first by move=> i _; rewrite lee_fin ltW.
rewrite fsbig_finite//= sumEFin big_const_seq count_predT.
rewrite iter_addr addr0 -EFinM mulr_natr; congr (_ *+ _)%:E.
exact: fcard_eq.
Qed.

Implicit Type (g : U -> \bar R).

Lemma discrete_integral_set1 g u : \int[@counting U R]_(x in [set u]) g x = g u.
Proof.
transitivity (\int[@counting U R]_(x in [set u]) cst (g u) x).
  by apply: eq_integral => x /set_mem/= ->.
by rewrite integral_cst//= counting_set1 mule1.
Qed.

Lemma discrete_integral_sum g (A : set T) : finite_set A ->
  (forall x, 0 <= g x) ->
  \int[@counting U R]_(x in A) g x = \sum_(x \in A) g x.
Proof.
move=> finA /= f0; rewrite fsbig_finite//=.
rewrite (eq_bigr (fun u => \int[counting]_(x in [set u]) g x))/=.
  by move => ? ?; rewrite discrete_integral_set1.
rewrite -ge0_integral_bigsetU//=; first by move=> i j _ _ [x [-> ->]].
by rewrite (bigsetU_fset_set _ finA) bigcup_idset1.
Qed.

Import HBNNSimple.

Let sintegral_counting_esum (h : {nnsfun U >-> R}) :
  sintegral (@counting U R) h = \esum_(x in [set: T]) (h x)%:E.
Proof.
rewrite sintegralE //=.
transitivity (\sum_(c \in range h) \esum_(x in (h @^-1` [set c] : set T)) (h x)%:E).
  apply: eq_fsbigr => c /set_mem/= -[x _ <-{c}].
  by rewrite counting_esum_cst//; apply: eq_esum => i/= ->.
rewrite -esum_fset//.
  by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
rewrite -esum_bigcupT.
- exact: trivIset_preimage1.
- by move=> ?; rewrite lee_fin.
- suff -> : \bigcup_(c in range h) h @^-1` [set c] = setT by [].
  by rewrite -subTset => u/= _; exists (h u).
Qed.

Lemma integral_counting_esum (f : T -> \bar R) : (forall x, 0 <= f x) ->
  \int[@counting U R]_x f x = \esum_(x in [set: T]) f x.
Proof.
move=> f0; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite ge0_integralTE//=; apply: ge_ereal_sup => /= _ [h /= hf] <-.
  rewrite sintegral_counting_esum.
  by apply: le_esum => x _; exact: hf.
- rewrite ge0_esum//; apply: ge_ereal_sup => /= _ [A [finA _] <-].
  by rewrite -discrete_integral_sum// ge0_subset_integral.
Qed.

End discrete_counting.
