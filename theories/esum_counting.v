From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra functions.
From mathcomp Require Import xfinmap constructive_ereal reals discrete.
From mathcomp Require Import realseq realsum.
From mathcomp Require Import esum sequences normedtype ereal cardinality fsbigop.
From mathcomp Require Import measure lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.  (* remove this line when requiring MathComp >= 2.6 *)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation simpm := Monoid.simpm.

Local Open Scope classical_set_scope.

(* -------------------------------------------------------------------- *)

Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.


Section Counting.
  Context (R : realType) (T : choiceType).

Lemma esum_bigcup_set (T1 T2 : choiceType) (K : set T1) (J : T1 -> set T2)
    (a : T2 -> \bar R) :
    trivIset setT J -> (forall x, (0 <= a x)%E) ->
  (\esum_(i in \bigcup_(k in K) J k) a i =
   \esum_(k in K) \esum_(j in J k) a j)%E.
Proof.
move=> tJ a0; rewrite esum_esum//; apply: reindex_esum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2] /set_mem/= [Ki1 Jij1] /set_mem/= [Ki2 Jij2] /= j12.
  have iE : i1 = i2.
    by apply: (tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
  by rewrite iE j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

Lemma counting_esum_cst (c : R) (A : set T) : (0 <= c)%R ->
  (c%:E * @counting (discrete_measurable_space T) R A
     = \esum_(x in A) c%:E)%E.
Proof.
move=> c0.
have [-> | c_neq] := eqVneq c 0%R.
  by rewrite mul0e; apply/esym/esum1.
have c_pos : (0 < c)%R by rewrite lt_def c_neq.
have [finA|infA] := pselect (finite_set A).
+ rewrite /counting (asboolT finA).
  rewrite esum_fset// fsbig_finite//=.
  rewrite sumEFin big_const_seq count_predT iter_addr addr0.
  rewrite -EFinM; congr (_%:E).
  rewrite mulr_natr; congr (c *+ _).
  apply: (elimT (@fcard_eq (discrete_measurable_space T) T A A finA finA)).
  exact: card_eqxx.
+ rewrite /counting asboolF//=.
  rewrite mulry gtr0_sg// mul1e.
  apply/esym/eqyP => r r0.
  have [B BA Brc] := infinite_set_fset (Num.Def.truncn (c^-1 * r)).+1 infA.
  apply: esum_ge => // ; exists [set` B].
    by split=> //; apply/subsetP => x; rewrite inE => /BA.
  rewrite fsbig_finite//= set_fsetK sumEFin big_const_seq count_predT.
  rewrite iter_addr addr0 -mulr_natr lee_fin -ler_pdivrMl//.
  apply: (@le_trans _ _ (((Num.Def.truncn (c^-1 * r)).+1)%:R)).
    exact: ltW (truncnS_gt _).
  rewrite ler_nat.
  exact: Brc.
Qed.

Import HBNNSimple.

Lemma sintegral_counting_esum
    (h : {nnsfun (discrete_measurable_space T) >-> R}) :
  (sintegral (@counting (discrete_measurable_space T) R) h
     = \esum_(x in [set: T]) (h x)%:E)%E.
Proof.
rewrite sintegralE //=.
transitivity (\sum_(c \in range h)
                \esum_(x in (h @^-1` [set c] : set T)) (h x)%:E)%E.
+ apply: eq_fsbigr => c /set_mem/= -[x _ <-{c}].
  rewrite counting_esum_cst//.
  by apply: (eq_esum _ (fun=> (h x)%:E)) => x0 ->.
+ rewrite -esum_fset//.
  + by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
  rewrite -esum_bigcup_set.
  + exact: trivIset_preimage1.
  + by move=> ?; rewrite lee_fin.
  + suff -> : \bigcup_(c in range h) h @^-1` [set c] = [set: T] by [].
    apply/seteqP; split => [//|y _].
    by exists (h y); [exists y|].
Qed.

Lemma int1 f i :
(\int[@counting (discrete_measurable_space T) R]_(x in [set i]) f x = f i)%E.
Proof.
transitivity (\int[@counting (discrete_measurable_space T) R]_(x in [set i])
                cst (f i) x)%E.
+ by apply: eq_integral => x /set_mem/= ->.
rewrite integral_cst// -[X in _ = X](mule1 (f i)).
congr (f i * _)%E => /=.
rewrite /counting (asboolT (finite_set1 i)).
by rewrite fset_set1 cardfs1.
Qed.

Lemma UA (A : set T): \bigcup_(i in A) [set i] = A.
Proof.
  by apply/seteqP; split=> [x [i Ai ->//]|x Ax]; exists x.
Qed.

Lemma intA f : forall A : set T, finite_set A ->
(forall x, (0 <= f x)%E) ->
(\int[@counting (discrete_measurable_space T) R]_(x in A) f x = \sum_(x \in A) f x)%E.
Proof.
move=> A finA ?.
rewrite fsbig_finite//=.
under eq_bigr do rewrite -int1.
rewrite -ge0_integral_bigsetU//=.
- by move=> i j _ _ [x [-> ->]].
- by rewrite (@bigsetU_fset_set _ _ _ _ finA) UA.
Qed.

Lemma integral_counting_esum (f : T -> \bar R) :
  (forall x, (0 <= f x)%E) ->
  (\int[@counting (discrete_measurable_space T) R]_x f x
     = \esum_(x in [set: T]) f x)%E.
Proof.
move=> f0 ; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite ge0_integralTE //=.
  apply: ge_ereal_sup => /= _ [h /= hf] <-.
  rewrite sintegral_counting_esum.
  by apply: le_esum => x _; exact: hf.
- rewrite ge0_esum //; apply: ge_ereal_sup => /= _ [A [finA _] <-].
  rewrite -intA//.
  by apply: ge0_subset_integral => //.
Qed.

End Counting.
