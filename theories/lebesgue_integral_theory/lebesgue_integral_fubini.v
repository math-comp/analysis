(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure numfun realfun.
From mathcomp Require Import function_spaces simple_functions.
From mathcomp Require Import measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.
From mathcomp Require Import lebesgue_integral_nonneg lebesgue_integrable.

(**md**************************************************************************)
(* # Fubini theorems for the Lebesgue Integral                                *)
(*                                                                            *)
(* This file contains a formalization of the product measure, of Tonelli-     *)
(* -Fubini' theorem, and Fubini's theorem.                                    *)
(*                                                                            *)
(* Main references:                                                           *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(* - R. Affeldt, C. Cohen. Measure Construction by Extension in Dependent     *)
(*   Type Theory with Application to Integration. JAR 2023                    *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*                 m1 \x m2 == product measure over T1 * T2, m1 is a measure  *)
(*                             over T1, and m2 is a sigma finite measure over *)
(*                             T2                                             *)
(* product_subprobability P == P.1 \x P.2 where P is a pair of subprobability *)
(*                             measures                                       *)
(*                m1 \x^ m2 == product measure over T1 * T2, m2 is a measure  *)
(*                             over T1, and m1 is a sigma finite measure over *)
(*                             T2                                             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "m1 '\x' m2" (at level 40, left associativity).
Reserved Notation "m1 '\x^' m2" (at level 40, left associativity).

(** Product measure *)

Section ndseq_closed_B.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (pt2 : T2) (m2 : T1 -> {measure set T2 -> \bar R}).
(* the generalization from m2 : {measure set T2 -> \bar R} to
   T1 -> {measure set T2 -> \bar R} is needed to develop the theory
   of kernels; the original type was sufficient for the development
   of the theory of integration  *)
Let phi A x := m2 x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma xsection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have phiF x : phi (F i) x @[i \oo] --> phi (\bigcup_i F i) x.
  rewrite /phi /= xsection_bigcup; apply: nondecreasing_cvg_mu.
  - by move=> n; apply: measurable_xsection; case: (BF n).
  - by apply: bigcupT_measurable => i; apply: measurable_xsection; case: (BF i).
  - by move=> m n mn; exact/subsetPset/le_xsection/subsetPset/ndF.
apply: (emeasurable_fun_cvg (phi \o F)) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: phiF.
Qed.
End xsection.

Section ysection.
Variable m1 : {measure set T1 -> \bar R}.
Let psi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma ysection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have psiF x : psi (F i) x @[i \oo] --> psi (\bigcup_i F i) x.
  rewrite /psi /= ysection_bigcup; apply: nondecreasing_cvg_mu.
  - by move=> n; apply: measurable_ysection; case: (BF n).
  - by apply: bigcupT_measurable => i; apply: measurable_ysection; case: (BF i).
  - by move=> m n mn; exact/subsetPset/le_ysection/subsetPset/ndF.
apply: (emeasurable_fun_cvg (psi \o F)) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: psiF.
Qed.
End ysection.

End ndseq_closed_B.

Section measurable_prod_subset.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variable (m2 : {measure set T2 -> \bar R}) (D : set T2) (mD : measurable D).
Let m2D := mrestr m2 mD.
HB.instance Definition _ := Measure.on m2D.
Let phi A := m2D \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_prod_subset_xsection
    (m2D_bounded : exists M, forall X, measurable X -> (m2D X < M%:E)%E) :
  measurable `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in measurable & A2 in measurable].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setXTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableX.
  have -> : phi (X1 `*` X2) = (fun x => m2D X2 * (\1_X1 x)%:E)%E.
    rewrite funeqE => x; rewrite indicE /phi /m2/= /mrestr.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionX.
    by rewrite mule0 notin_xsectionX// set0I measure0.
  exact/measurable_funeM/measurable_EFinP.
suff lsystemB : lambda_system setT B by exact: lambda_system_subset.
split => //; [exact: CB| |exact: xsection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
have -> : phi (X `\` Y) = (fun x => phi X x - phi Y x)%E.
  rewrite funeqE => x; rewrite /phi/= xsectionD// /m2D measureD.
  - by rewrite setIidr//; exact: le_xsection.
  - exact: measurable_xsection.
  - exact: measurable_xsection.
  - move: m2D_bounded => [M m2M].
    rewrite (lt_le_trans (m2M (xsection X x) _))// ?leey//.
    exact: measurable_xsection.
exact: emeasurable_funB.
Qed.

End xsection.

Section ysection.
Variable (m1 : {measure set T1 -> \bar R}) (D : set T1) (mD : measurable D).
Let m1D := mrestr m1 mD.
HB.instance Definition _ := Measure.on m1D.
Let psi A := m1D \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma measurable_prod_subset_ysection
    (m1_bounded : exists M, forall X, measurable X -> (m1D X < M%:E)%E) :
  measurable `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in measurable & A2 in measurable].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setXTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableX.
  have -> : psi (X1 `*` X2) = (fun x => m1D X1 * (\1_X2 x)%:E)%E.
    rewrite funeqE => y; rewrite indicE /psi /m1/= /mrestr.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionX.
    by rewrite mule0 notin_ysectionX// set0I measure0.
  exact/measurable_funeM/measurable_EFinP.
suff lsystemB : lambda_system setT B by exact: lambda_system_subset.
split => //; [exact: CB| |exact: ysection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
rewrite (_ : psi _ = (psi X \- psi Y)%E); first exact: emeasurable_funB.
rewrite funeqE => y; rewrite /psi/= ysectionD// /m1D measureD.
- by rewrite setIidr//; exact: le_ysection.
- exact: measurable_ysection.
- exact: measurable_ysection.
- have [M m1M] := m1_bounded.
  rewrite (lt_le_trans (m1M (ysection X y) _))// ?leey//.
  exact: measurable_ysection.
Qed.

End ysection.

End measurable_prod_subset.

Section measurable_fun_xsection.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection A : measurable A -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A => /[apply] -[].
have /sigma_finiteP [F [F_T F_nd F_oo]] := sigma_finiteT m2 => X mX.
have -> : X = \bigcup_n (X `&` (setT `*` F n)).
  by rewrite -setI_bigcupr -setX_bigcupr -F_T setXTT setIT.
apply: xsection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSX => //.
  exact/subsetPset/F_nd.
move=> n; rewrite -/B; have [? ?] := F_oo n.
pose m2Fn := mrestr m2 (F_oo n).1.
have m2Fn_bounded : exists M, forall X, measurable X -> (m2Fn X < M%:E)%E.
  exists (fine (m2Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0//= /m2Fn /mrestr setIid.
  by rewrite /m2Fn /mrestr/= setIid le_measure// inE//; exact: measurableI.
pose phi' A := m2Fn \o xsection A.
pose B' := [set A | measurable A /\ measurable_fun setT (phi' A)].
have subset_B' : measurable `<=` B' by exact: measurable_prod_subset_xsection.
split=> [|_ Y mY]; first by apply: measurableI => //; exact: measurableX.
have [_ /(_ measurableT Y mY)] := subset_B' X mX.
have ->// : phi' X = m2 \o xsection (X `&` setT `*` F n).
by apply/funext => x/=; rewrite /phi' setTX xsectionI xsection_preimage_snd.
Qed.

End measurable_fun_xsection.

Section measurable_fun_ysection.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let phi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection A : measurable A -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A => /[apply] -[].
have /sigma_finiteP[F [F_T F_nd F_oo]] := sigma_finiteT m1 => X mX.
have -> : X = \bigcup_n (X `&` (F n `*` setT)).
  by rewrite -setI_bigcupr -setX_bigcupl -F_T setXTT setIT.
apply: ysection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSX => //.
  exact/subsetPset/F_nd.
move=> n; have [? ?] := F_oo n; rewrite -/B.
pose m1Fn := mrestr m1 (F_oo n).1.
have m1Fn_bounded : exists M, forall X, measurable X -> (m1Fn X < M%:E)%E.
  exists (fine (m1Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0// /m1Fn/= /mrestr setIid.
  by rewrite /m1Fn/= /mrestr setIid le_measure// inE//=; exact: measurableI.
pose psi' A := m1Fn \o ysection A.
pose B' := [set A | measurable A /\ measurable_fun setT (psi' A)].
have subset_B' : measurable `<=` B' by exact: measurable_prod_subset_ysection.
split=> [|_ Y mY]; first by apply: measurableI => //; exact: measurableX.
have [_ /(_ measurableT Y mY)] := subset_B' X mX.
have ->// : psi' X = m1 \o (ysection (X `&` F n `*` setT)).
by apply/funext => y/=; rewrite /psi' setXT ysectionI// ysection_preimage_fst.
Qed.

End measurable_fun_ysection.

Section product_measures.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Context (m1 : set T1 -> \bar R) (m2 : set T2 -> \bar R).

Definition product_measure1 := (fun A => \int[m1]_x (m2 \o xsection A) x)%E.
Definition product_measure2 := (fun A => \int[m2]_x (m1 \o ysection A) x)%E.

End product_measures.

Notation "m1 '\x' m2" := (product_measure1 m1 m2) : ereal_scope.
Notation "m1 '\x^' m2" := (product_measure2 m1 m2) : ereal_scope.

Section product_measure1.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let pm10 : (m1 \x m2) set0 = 0.
Proof. by rewrite [LHS]integral0_eq// => x/= _; rewrite xsection0. Qed.

Let pm1_ge0 A : 0 <= (m1 \x m2) A.
Proof. by apply: integral_ge0 => // *. Qed.

Let pm1_sigma_additive : semi_sigma_additive (m1 \x m2).
Proof.
move=> F mF tF mUF.
rewrite [X in _ --> X](_ : _ = \sum_(n <oo) (m1 \x m2) (F n)).
  by apply/cvg_closeP; split; [exact: is_cvg_nneseries|rewrite closeE].
rewrite -integral_nneseries//; last by move=> n; exact: measurable_fun_xsection.
apply: eq_integral => x _; apply/esym/cvg_lim => //=; rewrite xsection_bigcup.
apply: (measure_sigma_additive _ (trivIset_xsection tF)) => ?.
exact: measurable_xsection.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (m1 \x m2)
  pm10 pm1_ge0 pm1_sigma_additive.

End product_measure1.

Section product_measure1E.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Lemma product_measure1E (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 -> (m1 \x m2) (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
move=> mA1 mA2 /=; rewrite /product_measure1 /=.
rewrite (eq_integral (fun x => (\1_A1 x)%:E * m2 A2)); last first.
  by move=> x _; rewrite indicE; have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionX// mul1e|rewrite mul0e notin_xsectionX].
rewrite ge0_integralZr ?integral_indic ?setIT//; exact: measurableT_comp.
Qed.

End product_measure1E.

Section product_subprobability.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.
Variable m12 : subprobability T1 R * subprobability T2 R.

Let prod := m12.1 \x m12.2.

HB.instance Definition _ := Measure.on prod.

Let prod_setT : prod setT <= 1.
Proof.
rewrite -setXTT [leLHS]product_measure1E// -[leRHS]mule1.
by rewrite lee_pmul// sprobability_setT.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ prod prod_setT.

Definition product_subprobability : subprobability (T1 * T2)%type R := prod.

End product_subprobability.

Section product_subprobability_setC.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

Lemma product_subprobability_setC (P : subprobability T1 R * subprobability T2 R)
    (A : set (T1 * T2)) : measurable A ->
  (P.1 \x P.2) (~` A) = (P.1 \x P.2) [set: T1 * T2] - (P.1 \x P.2) A.
Proof.
move=> mA.
rewrite -(setvU A) measureU//=; [|exact: measurableC|exact: setICl].
by rewrite addeK// (_ : (_ \x _)%E = product_subprobability P)// fin_num_measure.
Qed.

End product_subprobability_setC.

Section product_measure_unique.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.

Let product_measure_sigma_finite : sigma_finite setT (m1 \x m2).
Proof.
have /sigma_finiteP[F [TF ndF Foo]] := sigma_finiteT m1.
have /sigma_finiteP[G [TG ndG Goo]] := sigma_finiteT m2.
exists (fun n => F n `*` G n).
 rewrite -setXTT TF TG predeqE => -[x y]; split.
    move=> [/= [n _ Fnx] [k _ Gky]]; exists (maxn n k) => //; split.
    - by move: x Fnx; exact/subsetPset/ndF/leq_maxl.
    - by move: y Gky; exact/subsetPset/ndG/leq_maxr.
  by move=> [n _ []/= ? ?]; split; exists n.
move=> k; have [? ?] := Foo k; have [? ?] := Goo k.
split; first exact: measurableX.
by rewrite product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

HB.instance Definition _ := Measure_isSigmaFinite.Build _ _ _ (m1 \x m2)
  product_measure_sigma_finite.

Lemma product_measure_unique
    (m' : {measure set (T1 * T2) -> \bar R}) :
    (forall A B, measurable A -> measurable B -> m' (A `*` B) = m1 A * m2 B) ->
  forall X : set (T1 * T2), measurable X -> (m1 \x m2) X = m' X.
Proof.
move=> m'E.
have /sigma_finiteP[F [TF ndF Foo]] := sigma_finiteT m1.
have /sigma_finiteP[G [TG ndG Goo]] := sigma_finiteT m2.
have UFGT : \bigcup_k (F k `*` G k) = setT.
  rewrite -setXTT TF TG predeqE => -[x y]; split.
    by move=> [n _ []/= ? ?]; split; exists n.
  move=> [/= [n _ Fnx] [k _ Gky]]; exists (maxn n k) => //; split.
  - by move: x Fnx; exact/subsetPset/ndF/leq_maxl.
  - by move: y Gky; exact/subsetPset/ndG/leq_maxr.
pose C : set (set (T1 * T2)) :=
  [set C | exists A, measurable A /\ exists B, measurable B /\ C = A `*` B].
have CI : setI_closed C.
  move=> /= _ _ [X1 [mX1 [X2 [mX2 ->]]]] [Y1 [mY1 [Y2 [mY2 ->]]]].
  rewrite -setXI; exists (X1 `&` Y1); split; first exact: measurableI.
  by exists (X2 `&` Y2); split => //; exact: measurableI.
move=> X mX; apply: (measure_unique C (fun n => F n `*` G n)) => //.
- rewrite measurable_prod_measurableType //; congr (<<s _ >>).
  rewrite predeqE; split => [[A mA [B mB <-]]|[A [mA [B [mB ->]]]]].
    by exists A; split => //; exists B.
  by exists A => //; exists B.
- move=> n; rewrite /C /=; exists (F n); split; first by have [] := Foo n.
  by exists (G n); split => //; have [] := Goo n.
- by move=> A [A1 [mA1 [A2 [mA2 ->]]]]; rewrite m'E//= product_measure1E.
- move=> k; have [? ?] := Foo k; have [? ?] := Goo k.
  by rewrite /= product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

End product_measure_unique.

Section product_measure2.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let pm20 : (m1 \x^ m2) set0 = 0.
Proof.
by rewrite /(_ \x^ _) integral0_eq// => y/= _; rewrite ysection0 measure0.
Qed.

Let pm2_ge0 A : 0 <= (m1 \x^ m2) A.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_ysection.
Qed.

Let pm2_sigma_additive : semi_sigma_additive (m1 \x^ m2).
Proof.
move=> F mF tF mUF.
rewrite [X in _ --> X](_ : _ = \sum_(n <oo) (m1 \x^ m2) (F n)).
  apply/cvg_closeP; split; last by rewrite closeE.
  by apply: is_cvg_nneseries => *; exact: integral_ge0.
rewrite -integral_nneseries//; last first.
  by move=> n; apply: measurable_fun_ysection => //; rewrite inE.
apply: eq_integral => y _; apply/esym/cvg_lim => //=; rewrite ysection_bigcup.
apply: (measure_sigma_additive _ (trivIset_ysection tF)) => ?.
exact: measurable_ysection.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (m1 \x^ m2)
  pm20 pm2_ge0 pm2_sigma_additive.

End product_measure2.

Section product_measure2E.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {measure set T2 -> \bar R}.

Lemma product_measure2E (A1 : set T1) (A2 : set T2)
    (mA1 : measurable A1) (mA2 : measurable A2) :
  (m1 \x^ m2) (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
have mA1A2 : measurable (A1 `*` A2) by apply: measurableX.
transitivity (\int[m2]_y (m1 \o ysection (A1 `*` A2)) y) => //.
rewrite (_ : _ \o _ = fun y => m1 A1 * (\1_A2 y)%:E).
  rewrite ge0_integralZl ?integral_indic ?setIT//; exact: measurableT_comp.
rewrite funeqE => y; rewrite indicE.
have [yA2|yA2] := boolP (y \in A2); first by rewrite mule1 /= in_ysectionX.
by rewrite mule0 /= notin_ysectionX.
Qed.

End product_measure2E.

Section product_probability_measures.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  (R : realType) (P1 : probability T1 R) (P2 : probability T2 R).
Local Open Scope ereal_scope.

Local Notation pro1 := (P1 \x P2).

Let pro1_setT : pro1 [set: T1 * T2] = 1.
Proof.
rewrite -setXTT product_measure1E// -[RHS]mule1.
by rewrite -{1}(probability_setT P1) -(probability_setT P2).
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _ pro1 pro1_setT.

Local Notation pro2 := (P1 \x^ P2).

Let pro2_setT : pro2 setT = 1.
Proof.
rewrite -setXTT product_measure2E// -[RHS]mule1.
by rewrite -{1}(probability_setT P1) -(probability_setT P2).
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _ pro2 pro2_setT.

End product_probability_measures.

Section fubini_functions.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Variable f : T1 * T2 -> \bar R.

Definition fubini_F x := \int[m2]_y f (x, y).
Definition fubini_G y := \int[m1]_x f (x, y).

End fubini_functions.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.

Section indic_fubini_tonelli.
Variables (A : set (T1 * T2)) (mA : measurable A).
Implicit Types A : set (T1 * T2).
Let f : (T1 * T2) -> R := \1_A.

Let F := fubini_F m2 (EFin \o f).
Let G := fubini_G m1 (EFin \o f).

Lemma indic_fubini_tonelli_F_ge0 x : 0 <= F x.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma indic_fubini_tonelli_G_ge0 x : 0 <= G x.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma indic_fubini_tonelli_FE : F = m2 \o xsection A.
Proof.
apply/funext => x/=.
rewrite -[RHS]mul1e -integral_cst//; last exact: measurable_xsection.
rewrite /F /fubini_F /f [in RHS]integral_mkcond.
by apply: eq_integral => y _ /=; rewrite patchE mem_xsection indicE; case: ifPn.
Qed.

Lemma indic_fubini_tonelli_GE : G = m1 \o ysection A.
Proof.
apply/funext => x/=.
rewrite -[RHS]mul1e -integral_cst//; last exact: measurable_ysection.
rewrite /G /fubini_G /f [in RHS]integral_mkcond.
by apply: eq_integral => y _ /=; rewrite patchE mem_ysection indicE; case: ifPn.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
by rewrite indic_fubini_tonelli_FE//; exact: measurable_fun_xsection.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
by rewrite indic_fubini_tonelli_GE//; exact: measurable_fun_ysection.
Qed.

Lemma indic_fubini_tonelli1 : \int[m1 \x m2]_z (f z)%:E = \int[m1]_x F x.
Proof. by rewrite /f integral_indic// setIT indic_fubini_tonelli_FE. Qed.

Lemma indic_fubini_tonelli2 : \int[m1 \x^ m2]_z (f z)%:E = \int[m2]_y G y.
Proof. by rewrite /f integral_indic// setIT indic_fubini_tonelli_GE. Qed.

Lemma indic_fubini_tonelli : \int[m1]_x F x = \int[m2]_y G y.
Proof.
rewrite -indic_fubini_tonelli1// -indic_fubini_tonelli2// integral_indic//=.
rewrite integral_indic//= !setIT.
by apply: product_measure_unique => //= ? ? ? ?; rewrite product_measure2E.
Qed.

End indic_fubini_tonelli.

Section sfun_fubini_tonelli.
Variable f : {nnsfun T1 * T2 >-> R}.

Import HBNNSimple.

Let F := fubini_F m2 (EFin \o f).
Let G := fubini_G m1 (EFin \o f).

Lemma sfun_fubini_tonelli_FE : F = fun x =>
  \sum_(k \in range f) k%:E * m2 (xsection (f @^-1` [set k]) x).
Proof.
rewrite funeqE => x; rewrite /F /fubini_F [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/measurable_EFinP/measurableT_comp => //=.
    exact: measurableT_comp.
  - by move=> r y _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralZl//; last by rewrite lee_fin.
- by rewrite -/((m2 \o xsection _) x) -indic_fubini_tonelli_FE.
- exact/measurable_EFinP/measurableT_comp.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_F : measurable_fun [set: T1] F.
Proof.
rewrite sfun_fubini_tonelli_FE//; apply: emeasurable_fsum => // r.
exact/measurable_funeM/measurable_fun_xsection.
Qed.

Lemma sfun_fubini_tonelli_GE : G = fun y =>
  \sum_(k \in range f) k%:E * m1 (ysection (f @^-1` [set k]) y).
Proof.
rewrite funeqE => y; rewrite /G /fubini_G [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/measurable_EFinP/measurableT_comp => //=.
    exact: measurableT_comp.
  - by move=> r x _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralZl//; last by rewrite lee_fin.
- by rewrite -/((m1 \o ysection _) y) -indic_fubini_tonelli_GE.
- exact/measurable_EFinP/measurableT_comp.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
rewrite sfun_fubini_tonelli_GE//; apply: emeasurable_fsum => // r.
exact/measurable_funeM/measurable_fun_ysection.
Qed.

Let EFinf x : (f x)%:E =
  \sum_(k \in range f) k%:E * (\1_(f @^-1` [set k]) x)%:E.
Proof. by rewrite fsumEFin //= fimfunE. Qed.

Lemma sfun_fubini_tonelli1 : \int[m1 \x m2]_z (f z)%:E = \int[m1]_x F x.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m1]_x (k%:E * fubini_F m2 (EFin \o \1_(f @^-1` [set k])) x)).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralZl//; last 2 first.
    - exact/measurable_EFinP.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli1// -ge0_integralZl//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_F.
  - by move=> /= x _; exact: indic_fubini_tonelli_F_ge0.
rewrite -ge0_integral_fsum; last by [].
  - apply: eq_integral => x _; rewrite sfun_fubini_tonelli_FE.
    by under eq_fsbigr do rewrite indic_fubini_tonelli_FE//.
  - by [].
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_F.
move=> r x _; rewrite /fubini_F.
have [r0|r0] := leP 0%R r.
  by rewrite mule_ge0//; exact: indic_fubini_tonelli_F_ge0.
rewrite integral0_eq ?mule0// => y _.
by rewrite preimage_nnfun0//= indicE in_set0.
Qed.

Lemma sfun_fubini_tonelli2 : \int[m1 \x^ m2]_z (f z)%:E = \int[m2]_y G y.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - by move=> i; exact/measurable_EFinP/measurableT_comp.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m2]_x (k%:E * (fubini_G m1 (EFin \o \1_(f @^-1` [set k])) x))).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralZl//; last 2 first.
    - exact/measurable_EFinP.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli2// -ge0_integralZl//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_G.
  - by move=> /= x _; exact: indic_fubini_tonelli_G_ge0.
rewrite -ge0_integral_fsum; last by [].
  - apply: eq_integral => x _; rewrite sfun_fubini_tonelli_GE.
    by under eq_fsbigr do rewrite indic_fubini_tonelli_GE//.
  - by [].
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_G.
move=> r y _; rewrite /fubini_G.
have [r0|r0] := leP 0%R r.
  by rewrite mule_ge0//; exact: indic_fubini_tonelli_G_ge0.
rewrite integral0_eq ?mule0// => x _.
by rewrite preimage_nnfun0//= indicE in_set0.
Qed.

Lemma sfun_fubini_tonelli :
  \int[m1 \x m2]_z (f z)%:E = \int[m1 \x^ m2]_z (f z)%:E.
Proof.
apply: eq_measure_integral => /= A Ameasurable _.
by apply: product_measure_unique => //= *; rewrite product_measure2E.
Qed.

End sfun_fubini_tonelli.

Section fubini_tonelli.
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.
Hypothesis f0 : forall x, 0 <= f x.
Let T : measurableType _ := (T1 * T2)%type.

Let F := fubini_F m2 f.
Let G := fubini_G m1 f.

Import HBNNSimple.

Let F_ (g : {nnsfun T >-> R}^nat) n x := \int[m2]_y (g n (x, y))%:E.
Let G_ (g : {nnsfun T >-> R}^nat) n y := \int[m1]_x (g n (x, y))%:E.

Lemma measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
pose g := nnsfun_approx measurableT mf.
apply: (emeasurable_fun_cvg (F_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> x _.
  rewrite /F_ /F /fubini_F [in X in _ --> X](_ : (fun _ => _) =
      fun y => limn (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => y; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP => //; exact/measurableT_comp.
  - by move=> n y _; rewrite lee_fin//; exact: fun_ge0.
  - by move=> y _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
pose g := nnsfun_approx measurableT mf.
apply: (emeasurable_fun_cvg (G_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- move=> y _; rewrite /G_ /G /fubini_G [in X in _ --> X](_ : (fun _ => _) =
      fun x => limn (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => x; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP => //; exact/measurableT_comp.
  - by move=> n x _; rewrite lee_fin; exact: fun_ge0.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli1 : \int[m1 \x m2]_z f z = \int[m1]_x F x.
Proof.
pose g := nnsfun_approx measurableT mf.
have F_F x : F x = limn (F_ g ^~ x).
  rewrite [RHS](_ : _ = limn (fun n => \int[m2]_y (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/measurable_EFinP/measurableT_comp.
    - by move=> n /= y _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [RHS](_ : _ = limn (fun n => \int[m1 \x m2]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/measurable_EFinP.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [LHS](_ : _ =
    limn (fun n => \int[m1]_x (\int[m2]_y (EFin \o g n) (x, y)))).
  set r := fun _ => _; set l := fun _ => _; have -> // : l = r.
  by apply/funext  => n; rewrite /l /r sfun_fubini_tonelli1.
rewrite [RHS](_ : _ = limn (fun n => \int[m1]_x F_ g n x))//.
rewrite -monotone_convergence => [|//|||]; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> n x _; apply: integral_ge0 => // y _ /=; rewrite lee_fin.
  exact: fun_ge0.
- move=> x /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> y _; rewrite lee_fin; exact: fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> y _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli2 : \int[m1 \x m2]_z f z = \int[m2]_y G y.
Proof.
pose g := nnsfun_approx measurableT mf.
have G_G y : G y = limn (G_ g ^~ y).
  rewrite /G /fubini_G.
  rewrite [RHS](_ : _ = limn (fun n => \int[m1]_x (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/measurable_EFinP/measurableT_comp.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> x /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [RHS](_ : _ = limn (fun n => \int[m1 \x m2]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/measurable_EFinP.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [LHS](_ : _ = limn
    (fun n => \int[m2]_y (\int[m1]_x (EFin \o g n) (x, y)))).
  set r := fun _ => _; set l := fun _ => _; have -> // : l = r.
  by apply/funext => n; rewrite /l /r sfun_fubini_tonelli sfun_fubini_tonelli2.
rewrite [RHS](_ : _ = limn (fun n => \int[m2]_y G_ g n y))//.
rewrite -monotone_convergence => [|//|||]; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- by move=> n y _; apply: integral_ge0 => // x _ /=; rewrite lee_fin fun_ge0.
- move=> y /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> x _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite -fubini_tonelli1// fubini_tonelli2. Qed.

End fubini_tonelli.

End fubini_tonelli.
Arguments fubini_tonelli1 {d1 d2 T1 T2 R m1 m2} f.
Arguments fubini_tonelli2 {d1 d2 T1 T2 R m1 m2} f.
Arguments fubini_tonelli {d1 d2 T1 T2 R m1 m2} f.
Arguments measurable_fun_fubini_tonelli_F {d1 d2 T1 T2 R m2} f.
Arguments measurable_fun_fubini_tonelli_G {d1 d2 T1 T2 R m1} f.

Section fubini.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Variable f : T1 * T2 -> \bar R.

Lemma integrable12ltyP : measurable_fun setT f ->
  (m1 \x m2).-integrable setT f <-> \int[m1]_x \int[m2]_y `|f (x, y)| < +oo.
Proof.
move=> mf; split=> [/integrableP[_]|] ioo; [|apply/integrableP; split=> [//|]].
- by rewrite -(fubini_tonelli1 (abse \o f))//=; exact: measurableT_comp.
- by rewrite fubini_tonelli1//; exact: measurableT_comp.
Qed.

Lemma integrable21ltyP : measurable_fun setT f ->
  (m1 \x m2).-integrable setT f <-> \int[m2]_y \int[m1]_x `|f (x, y)| < +oo.
Proof.
move=> mf; split=> [/integrableP[_]|] ioo; [|apply/integrableP; split=> [//|]].
- by rewrite -(fubini_tonelli2 (abse \o f))//=; exact: measurableT_comp.
- by rewrite fubini_tonelli2//; exact: measurableT_comp.
Qed.

Let measurable_fun1 : measurable_fun setT f ->
  measurable_fun setT (fun x => \int[m2]_y `|f (x, y)|).
Proof.
move=> mf; apply: (measurable_fun_fubini_tonelli_F (abse \o f)) => //=.
exact: measurableT_comp.
Qed.

Let measurable_fun2 : measurable_fun setT f ->
  measurable_fun setT (fun y => \int[m1]_x `|f (x, y)|).
Proof.
move=> mf; apply: (measurable_fun_fubini_tonelli_G (abse \o f)) => //=.
exact: measurableT_comp.
Qed.

Hypothesis imf : (m1 \x m2).-integrable setT f.
Let mf : measurable_fun setT f. Proof. exact: measurable_int imf. Qed.

Lemma ae_integrable1 :
  {ae m1, forall x, m2.-integrable setT (fun y => f (x, y))}.
Proof.
have : m1.-integrable setT (fun x => \int[m2]_y `|f (x, y)|).
  apply/integrableP; split; first exact/measurable_fun1.
  rewrite (le_lt_trans _  ((integrable12ltyP mf).1 imf))// ge0_le_integral //.
  - by apply: measurableT_comp => //; exact: measurable_fun1.
  - exact: measurable_fun1.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT); apply: filterS => x /= /(_ I) im2f.
apply/integrableP; split; first exact/measurableT_comp.
by move/fin_numPlt : im2f => /andP[].
Qed.

Lemma ae_integrable2 :
  {ae m2, forall y, m1.-integrable setT (fun x => f (x, y))}.
Proof.
have : m2.-integrable setT (fun y => \int[m1]_x `|f (x, y)|).
  apply/integrableP; split; first exact/measurable_fun2.
  rewrite (le_lt_trans _ ((integrable21ltyP mf).1 imf))// ge0_le_integral //.
  - by apply: measurableT_comp => //; exact: measurable_fun2.
  - exact: measurable_fun2.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT); apply: filterS => x /= /(_ I) im2f.
apply/integrableP; split; first exact/measurableT_comp.
by move/fin_numPlt : im2f => /andP[].
Qed.

Let F := fubini_F m2 f.

Let Fplus x := \int[m2]_y f^\+ (x, y).
Let Fminus x := \int[m2]_y f^\- (x, y).

Let FE : F = Fplus \- Fminus.
Proof.
apply/funext=> x; rewrite [LHS]integralE.
under eq_integral do rewrite funepos_comp/=.
by under [X in _ - X = _]eq_integral do rewrite funeneg_comp/=.
Qed.

Let measurable_Fplus : measurable_fun setT Fplus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: measurable_funepos.
Qed.

Let measurable_Fminus : measurable_fun setT Fminus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: measurable_funeneg.
Qed.

Lemma measurable_fubini_F : measurable_fun setT F.
Proof.
rewrite FE.
by apply: emeasurable_funB; [exact: measurable_Fplus|exact: measurable_Fminus].
Qed.

Let integrable_Fplus : m1.-integrable setT Fplus.
Proof.
apply/integrableP; split=> //.
apply: le_lt_trans ((integrable12ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|..].
- by apply: measurableT_comp; last apply: measurable_Fplus.
- exact: measurable_fun1.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funepos.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funepos.
  + by apply: measurableT_comp => //; exact/measurableT_comp.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDl.
Qed.

Let integrable_Fminus : m1.-integrable setT Fminus.
Proof.
apply/integrableP; split=> //.
apply: le_lt_trans ((integrable12ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|..].
- exact: measurableT_comp.
- exact: measurable_fun1.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  + by apply: measurableT_comp => //; exact: measurableT_comp.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDr.
Qed.

Lemma integrable_fubini_F : m1.-integrable setT F.
Proof. by rewrite FE; exact: integrableB. Qed.

Let G := fubini_G m1 f.

Let Gplus y := \int[m1]_x f^\+ (x, y).
Let Gminus y := \int[m1]_x f^\- (x, y).

Let GE : G = Gplus \- Gminus.
Proof.
apply/funext=> x; rewrite [LHS]integralE.
under eq_integral do rewrite funepos_comp/=.
by under [X in _ - X = _]eq_integral do rewrite funeneg_comp/=.
Qed.

Let measurable_Gplus : measurable_fun setT Gplus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: measurable_funepos.
Qed.

Let measurable_Gminus : measurable_fun setT Gminus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: measurable_funeneg.
Qed.

Lemma measurable_fubini_G : measurable_fun setT G.
Proof. by rewrite GE; exact: emeasurable_funB. Qed.

Let integrable_Gplus : m2.-integrable setT Gplus.
Proof.
apply/integrableP; split=> //; apply: le_lt_trans ((integrable21ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|exact: measurableT_comp|..].
- exact: measurable_fun2.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funepos.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funepos.
  + by apply: measurableT_comp => //; exact: measurableT_comp.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDl.
Qed.

Let integrable_Gminus : m2.-integrable setT Gminus.
Proof.
apply/integrableP; split=> //; apply: le_lt_trans ((integrable21ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|exact: measurableT_comp|..].
- exact: measurable_fun2.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funeneg.
  + by apply: measurableT_comp => //; exact: measurableT_comp.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDr.
Qed.

Lemma integral12_prod_meas1 : \int[m1]_x F x = \int[m1 \x m2]_z f z.
Proof.
rewrite FE integralB; [|by[]|exact: integrable_Fplus|exact: integrable_Fminus].
by rewrite [in RHS]integralE ?fubini_tonelli1//;
  [exact: measurable_funeneg|exact: measurable_funepos].
Qed.

Lemma integral21_prod_meas1 : \int[m2]_x G x = \int[m1 \x m2]_z f z.
Proof.
rewrite GE integralB; [|by[]|exact: integrable_Gplus|exact: integrable_Gminus].
by rewrite [in RHS]integralE ?fubini_tonelli2//;
  [exact: measurable_funeneg|exact: measurable_funepos].
Qed.

Lemma integral21_prod_meas2 : \int[m2]_x G x = \int[m1 \x^ m2]_z f z.
Proof.
rewrite integral21_prod_meas1; apply: eq_measure_integral => //= A mA _.
by apply: product_measure_unique => // B C mB mC/=; rewrite product_measure2E.
Qed.

Lemma integral12_prod_meas2 : \int[m1]_x F x = \int[m1 \x^ m2]_z f z.
Proof.
rewrite integral12_prod_meas1//; apply: eq_measure_integral => //= A mA _.
by apply: product_measure_unique => // B C mB mC/=; rewrite product_measure2E.
Qed.

Theorem Fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite integral12_prod_meas1 -integral21_prod_meas1. Qed.

End fubini.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `integrable12ltyP`")]
Notation fubini1a := integrable12ltyP (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `integrable21ltyP`")]
Notation fubini1b := integrable21ltyP (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `integral12_prod_meas1`")]
Notation fubini1 := integral12_prod_meas1 (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `integral21_prod_meas1`")]
Notation fubini2 := integral21_prod_meas1 (only parsing).

Section sfinite_fubini.
Local Open Scope ereal_scope.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables (m1 : {sfinite_measure set X -> \bar R}).
Variables (m2 : {sfinite_measure set Y -> \bar R}).
Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
Hypothesis mf : measurable_fun [set: X * Y] f.

Lemma sfinite_Fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof.
pose s1 := sfinite_measure_seq m1.
pose s2 := sfinite_measure_seq m2.
rewrite [LHS](eq_measure_integral (mseries s1 0)); last first.
  by move=> A mA _; rewrite /=; exact: sfinite_measure_seqP.
transitivity (\int[mseries s1 0]_x \int[mseries s2 0]_y f (x, y)).
  apply: eq_integral => x _; apply: eq_measure_integral => ? ? _.
  exact: sfinite_measure_seqP.
transitivity (\sum_(n <oo) \int[s1 n]_x \sum_(m <oo) \int[s2 m]_y f (x, y)).
  rewrite ge0_integral_measure_series; [|by []| |]; last 2 first.
    by move=> t _; exact: integral_ge0.
    rewrite [X in measurable_fun _ X](_ : _ =
        fun x => \sum_(n <oo) \int[s2 n]_y f (x, y)); last first.
      apply/funext => x.
      by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
    apply: ge0_emeasurable_sum; first by move=> k x *; exact: integral_ge0.
    by move=> k _; exact: measurable_fun_fubini_tonelli_F.
  apply: eq_eseriesr => n _; apply: eq_integral => x _.
  by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[s1 n]_x \int[s2 m]_y f (x, y)).
  apply: eq_eseriesr => n _; rewrite integral_nneseries => [//|//||].
    by move=> m; exact: measurable_fun_fubini_tonelli_F.
  by move=> m x _; exact: integral_ge0.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[s2 m]_y \int[s1 n]_x f (x, y)).
  apply: eq_eseriesr => n _; apply: eq_eseriesr => m _.
  by rewrite fubini_tonelli//; exact: finite_measure_sigma_finite.
transitivity (\sum_(n <oo) \int[mseries s2 0]_y \int[s1 n]_x f (x, y)).
  apply: eq_eseriesr => n _; rewrite ge0_integral_measure_series => [//|//||].
    by move=> y _; exact: integral_ge0.
  exact: measurable_fun_fubini_tonelli_G.
transitivity (\int[mseries s2 0]_y \sum_(n <oo) \int[s1 n]_x f (x, y)).
  rewrite integral_nneseries => [//|//||].
    by move=> n; apply: measurable_fun_fubini_tonelli_G.
  by move=> n y _; exact: integral_ge0.
transitivity (\int[mseries s2 0]_y \int[mseries s1 0]_x f (x, y)).
  apply: eq_integral => y _.
  by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
transitivity (\int[m2]_y \int[mseries s1 0]_x f (x, y)).
  by apply: eq_measure_integral => A mA _ /=; rewrite sfinite_measure_seqP.
apply: eq_integral => y _; apply: eq_measure_integral => A mA _ /=.
by rewrite sfinite_measure_seqP.
Qed.

End sfinite_fubini.
Arguments sfinite_Fubini {d d' X Y R} m1 m2 f.
