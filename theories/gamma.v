(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra interval interval_inference.
From mathcomp Require Import boolp classical_sets cardinality reals.
From mathcomp Require Import topology normedtype ereal sequences exp.
From mathcomp Require Import derive measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import ftc realfun probability.

(**md**************************************************************************)
(* # The Gamma function                                                       *)
(*                                                                            *)
(* `Gamma`                                                                    *)
(* : the Gamma function                                                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Gamma.
Context {R : realType}.
Import MeasurableR.

Notation mu := lebesgue_measure.

Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (x`^ (a - 1) * expR (- x))%:E)%E.

Lemma Gamma1 : Gamma 1 = 1%E.
Proof.
transitivity (@exponential_prob R 1 `[0, +oo[).
  apply: eq_integral => x; rewrite inE/= in_itv/= => /andP[x0 _].
  by rewrite subrr powRr0 exponential_pdfE// mulN1r.
transitivity (@exponential_prob R 1 setT) => /=; last exact: probability_setT.
rewrite -[LHS]addr0 -(setUv `[0, +oo[) measureU//=.
- exact: measurableC.
- exact: setICr.
- by rewrite setCitv/= [X in _ `|` X]set_itv_ge// setU0 exponential_prob_itvNy0.
Qed.

Let fy0 a : x `^ a * - expR (- x) @[x --> +oo] --> (0:R).
Proof.
rewrite -[X in _ --> X]opprK.
under eq_fun do rewrite mulrN.
apply: cvgN; rewrite oppr0.
under eq_fun do rewrite -mulN1r.
exact: powRMexpR_cvgr0.
Qed.

Lemma Gammar1 a : 1 <= a -> (Gamma (a + 1) = a%:E * Gamma a)%E.
Proof.
move=> a1; have a0 : 0 < a by exact: lt_le_trans a1.
have dxa1 : {in `]0, +oo[%R,
    (fun x : R => x `^ a) ^`()%classic =1 (fun x => a * x `^ (a - 1))}.
  exact: powR_derive1.
have dex : {in `]0, +oo[%R,
    (fun x : R => - expR (- x)) ^`()%classic =1 (expR \o -%R)}.
  by move=> x _; rewrite derive1E derive_val mulrN mulr1 opprK.
rewrite /Gamma addrK.
rewrite (integration_by_partsy_le0_ge0 _ _ dex _ _ dxa1 (fy0 a)).
- by apply: continuous_subspaceT => ?; exact/(cvg_compNP expR)/continuous_expR.
- apply: derivable_oy_RcontinuousN; split.
    move=> x _; apply/diff_derivable/differentiable_comp => //.
    exact/derivable1_diffP/derivable_expR.
  exact/cvg_at_right_filter/(cvg_compNP expR)/continuous_expR.
- move: a1; rewrite le_eqVlt => /predU1P[<- |a1].
    apply: continuous_subspaceT => /= x.
    under eq_fun do rewrite mul1r subrr powRr0.
    exact: cvg_cst.
  by apply/within_continuousMl/within_continuous_powR; rewrite subr_gt0.
- split; first exact: derivable_powR.
  by rewrite powR0 ?gt_eqF//; exact: powR_cvg0.
- move=> y /[!inE] y0.
  rewrite mulrN EFinN oppe_le0 lee_fin -mulrA (mulr_ge0 (ltW a0))//.
  rewrite powRMexpR_ge0//.
  by apply: subset_itv y0 => //; rewrite bnd_simp.
- move=> y /[!inE] y0.
  rewrite lee_fin powRMexpR_ge0//.
  by apply: subset_itv y0 => //; rewrite bnd_simp.
- rewrite sub0r powR0 ?gt_eqF// mul0r EFinN oppe0 sub0e.
  under eq_integral do rewrite mulrN EFinN -mulrA EFinM -mulNe.
  rewrite ge0_integralZl//=.
  + by move=> x /[!inE] x0; rewrite lee_fin powRMexpR_ge0.
  + apply/measurable_EFinP/measurable_funTS.
    by apply: measurable_funM; [exact: measurable_powR|exact: measurableT_comp].
  + by rewrite EFinN mulNe oppeK.
Unshelve. all: end_near. Qed.

End Gamma.

Lemma GammaS {R : realType} n : Gamma n.+1%:R = n`!%:R%:E :> \bar R.
Proof.
elim: n => [|n ih]; first exact: Gamma1.
by rewrite -natr1 Gammar1 ?ler1n// ih factS natrM EFinM.
Qed.
