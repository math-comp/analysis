(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop reals.
From mathcomp Require Import interval_inference ereal topology normedtype.
From mathcomp Require Import sequences esum numfun.
From mathcomp Require Import measurable_structure measure_function.

(**md**************************************************************************)
(* # The Dirac Measure                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*              \d_a == Dirac measure                                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'\d_' a" (at level 8, a at level 2, format "'\d_' a").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section dirac_measure.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (a : T) (R : realFieldType).

Definition dirac (A : set T) : \bar R := (\1_A a)%:E.

Let dirac0 : dirac set0 = 0. Proof. by rewrite /dirac indic0. Qed.

Let dirac_ge0 B : 0 <= dirac B. Proof. by rewrite /dirac indicE. Qed.

Let dirac_sigma_additive : semi_sigma_additive dirac.
Proof.
move=> F mF tF mUF; rewrite /dirac indicE; have [|aFn] /= := boolP (a \in _).
  rewrite inE => -[n _ Fna].
  have naF m : m != n -> a \notin F m.
    move=> mn; rewrite notin_setE => Fma.
    move/trivIsetP : tF => /(_ _ _ Logic.I Logic.I mn).
    by rewrite predeqE => /(_ a)[+ _]; exact.
  apply/cvg_ballP => _/posnumP[e]; near=> m.
  have mn : (n < m)%N by near: m; exists n.+1.
  rewrite big_mkord (bigID (xpred1 (Ordinal mn)))//= big_pred1_eq/= big1/=.
    by rewrite adde0 indicE mem_set//; exact: ballxx.
  by move=> j ij; rewrite indicE (negbTE (naF _ _)).
rewrite [X in X @ \oo --> _](_ : _ = cst 0); first exact: cvg_cst.
apply/funext => n; rewrite big1// => i _; rewrite indicE; apply/eqP.
by rewrite eqe pnatr_eq0 eqb0; apply: contra aFn => /[!inE] aFn; exists i.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  dirac dirac0 dirac_ge0 dirac_sigma_additive.

End dirac_measure.
Arguments dirac {d T} _ {R}.

Notation "\d_ a" := (dirac a) : ring_scope.

Section dirac_lemmas_realFieldType.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realFieldType).

Lemma diracE a (A : set T) : \d_a A = (a \in A)%:R%:E :> \bar R.
Proof. by rewrite /dirac indicE. Qed.

Lemma dirac0 (a : T) : \d_a set0 = 0 :> \bar R.
Proof. by rewrite diracE in_set0. Qed.

Lemma diracT (a : T) : \d_a setT = 1 :> \bar R.
Proof. by rewrite diracE in_setT. Qed.

End dirac_lemmas_realFieldType.

Section dirac_lemmas.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).

Lemma finite_card_sum (A : set T) : finite_set A ->
  \esum_(i in A) 1 = (#|` fset_set A|%:R)%:E :> \bar R.
Proof.
move=> finA; rewrite esum_fset// (eq_fsbigr (cst 1))//.
by rewrite card_fset_sum1// natr_sum -sumEFin fsbig_finite.
Qed.

Lemma finite_card_dirac (A : set T) : finite_set A ->
  \esum_(i in A) \d_ i A = (#|` fset_set A|%:R)%:E :> \bar R.
Proof.
move=> finA; rewrite esum_fset// (eq_fsbigr (cst 1))//.
  by rewrite card_fset_sum1// natr_sum -sumEFin fsbig_finite.
by move=> i iA; rewrite diracE iA.
Qed.

Lemma infinite_card_dirac (A : set T) : infinite_set A ->
  \esum_(i in A) \d_ i A = +oo :> \bar R.
Proof.
move=> infA; apply/eqyP => r r0.
have [B BA Br] := infinite_set_fset (truncn r).+1 infA.
apply: esum_ge; exists [set` B] => //.
apply: (@le_trans _ _ (truncn r).+1%:R%:E).
  by rewrite lee_fin ltW// truncnS_gt.
move: Br; rewrite -(@ler_nat R) -lee_fin => /le_trans; apply.
rewrite (eq_fsbigr (cst 1))/=; last first.
  by move=> i /[!inE] /BA /mem_set iA; rewrite diracE iA.
by rewrite fsbig_finite//= card_fset_sum1 sumEFin natr_sum// set_fsetK.
Qed.

End dirac_lemmas.
