(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
Require Import mathcomp_extra boolp reals ereal nsatz_realtype classical_sets.
Require Import signed functions topology normedtype landau sequences derive.
Require Import realfun sequences exp.
From mathcomp Require Import complex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Import ComplexField Normc.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* TODO: move *)
Lemma complexr_morph {R : realType} (k : nat) : k%:R = k%:R%:C :> R[i].
Proof. by elim: k => // k ih; rewrite -!natr1 rmorphD/= -ih. Qed.

Lemma normc_morph {R : realType} (r : R) : `|r%:C| = `|r|%:C.
Proof. by rewrite [in LHS]/normr/= expr0n /= addr0 sqrtr_sqr. Qed.

Lemma sumc_morph {R : realType} I (s : seq I) (f : I -> R) :
  (\sum_(k <- s) (f k))%:C = \sum_(k <- s) (f k)%:C.
Proof. by apply: big_morph => // ; exact: rmorphD. Qed.

Lemma eq_cseries (R : realType) (f g : (complex_ringType R)^nat) (P : pred nat) m :
  (forall i, P i -> f i = g i) ->
  \big[+%R/0]_(m <= i <oo | P i) f i = \big[+%R/0]_(m <= i <oo | P i) g i.
Proof.
move=> efg; congr (lim _); apply/funext => k.
by apply: eq_bigr => /= i Pi; exact: efg.
Qed.

(* NB: rename exp_coeff to expR_coeff? *)
Definition complex_exp_coeff (R : realFieldType) (x : R[i]) :=
  [sequence x ^+ n / n`!%:R]_n.

Definition complex_pseries {R : realFieldType} f (x : R[i]) :=
  [series f i * x ^+ i]_i.

Definition exp {R : realType} (x : R[i]) : R[i] :=
  lim (series (complex_exp_coeff x)).

Lemma expE {R : realType} : exp =
  fun x : R[i] => lim (complex_pseries (fun n => n`!%:R^-1) x).
Proof.
apply/funext => x; rewrite /complex_pseries.
rewrite /exp (_ : complex_exp_coeff _ = (fun i => i`!%:R^-1 * x ^+ i)) //.
by apply/funext => n; rewrite mulrC.
Qed.

Lemma continuous_complex (R : realType) :
   continuous (fun x => x%:C : complex_ringType R).
Proof.
move=> r/= A/= [/= e e0 reA]; exists (complex.Re e).
  by case: e e0 reA => x y/=; rewrite ltcE/= => /andP[].
move=> t /= rte; apply: reA => //.
by rewrite /ball_/= -rmorphB/= normc_morph ltcE/= ger0_Im ?eqxx// ltW.
Qed.

Lemma expC (R : realType) (x : R) : exp x%:C = (expR x)%:C.
Proof.
rewrite /exp /series /complex_exp_coeff/=.
rewrite /expR /series /exp_coeff/=.
transitivity (\big[+%R/0]_(0 <= k <oo) ((x ^+ k / k`!%:R)%:C : complex_ringType _)).
  apply: eq_cseries => k _.
  rewrite rmorphM/= rmorphX/= complexr_morph/= rmorphV//=.
  by rewrite unitfE/= pnatr_eq0 gt_eqF// ltEnat/= fact_gt0.
under eq_fun do rewrite -sumc_morph.
suff : (fun n => (\sum_(0 <= k < n) x ^+ k / k`!%:R)%:C : complex_ringType _) -->
       ((\big[+%R/0]_(0 <= k <oo) (x ^+ k / k`!%:R))%:C : complex_ringType _).
  by move/cvg_lim; exact.
apply: cvg_comp; last exact: continuous_complex.
exact: is_cvg_series_exp_coeff.
Qed.
