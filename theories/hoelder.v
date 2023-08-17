(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure lebesgue_integral numfun exp.

(******************************************************************************)
(*                         Hoelder's Inequality                               *)
(*                                                                            *)
(* This file provides Hoelder's inequality.                                   *)
(*                                                                            *)
(*           'N[mu]_p[f] := (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1             *)
(*                          The corresponding definition is Lnorm.            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "'N[ mu ]_ p [ F ]"
  (at level 5, F at level 36, mu at level 10,
  format "'[' ''N[' mu ]_ p '/  ' [ F ] ']'").
(* for use as a local notation when the measure is in context: *)
Reserved Notation "'N_ p [ F ]"
  (at level 5, F at level 36, format "'[' ''N_' p '/  ' [ F ] ']'").

Declare Scope Lnorm_scope.

Local Open Scope ereal_scope.

Section Lnorm.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : R) (f g : T -> R).

Definition Lnorm p f := (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1.

Local Notation "'N_ p [ f ]" := (Lnorm p f).

Lemma Lnorm1 f : 'N_1[f] = \int[mu]_x `|f x|%:E.
Proof.
rewrite /Lnorm invr1// poweRe1//.
  by apply: eq_integral => t _; rewrite powRr1.
by apply: integral_ge0 => t _; rewrite powRr1.
Qed.

Lemma Lnorm_ge0 p f : 0 <= 'N_p[f]. Proof. exact: poweR_ge0. Qed.

Lemma eq_Lnorm p f g : f =1 g -> 'N_p[f] = 'N_p[g].
Proof. by move=> fg; congr Lnorm; exact/funext. Qed.

Lemma Lnorm_eq0_eq0 p f : measurable_fun setT f -> 'N_p[f] = 0 ->
  ae_eq mu [set: T] (fun t => (`|f t| `^ p)%:E) (cst 0).
Proof.
move=> mf /poweR_eq0_eq0 fp; apply/ae_eq_integral_abs => //=.
  apply: measurableT_comp => //.
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
  exact: measurableT_comp.
under eq_integral => x _ do rewrite ger0_norm ?powR_ge0//.
by rewrite fp//; apply: integral_ge0 => t _; rewrite lee_fin powR_ge0.
Qed.

End Lnorm.
#[global]
Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnorm_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f).

Section hoelder.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p q : R) (f g : T -> R).

Let measurableT_comp_powR f p :
  measurable_fun [set: T] f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Let integrable_powR f p : (0 < p)%R ->
  measurable_fun [set: T] f -> 'N_p[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E).
Proof.
move=> p0 mf foo; apply/integrableP; split.
  apply: measurableT_comp => //; apply: measurableT_comp_powR.
  exact: measurableT_comp.
rewrite ltey; apply: contra foo.
move=> /eqP/(@eqy_poweR _ _ p^-1); rewrite invr_gt0 => /(_ p0) <-.
apply/eqP; congr (_ `^ _).
by apply/eq_integral => t _; rewrite gee0_abs// ?lee_fin ?powR_ge0.
Qed.

Let hoelder0 f g p q : measurable_fun setT f -> measurable_fun setT g ->
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  'N_p[f] = 0 -> 'N_1[(f \* g)%R]  <= 'N_p[f] * 'N_q[g].
Proof.
move=> mf mg p0 q0 pq f0; rewrite f0 mul0e Lnorm1 [leLHS](_ : _ = 0)//.
rewrite (ae_eq_integral (cst 0)) => [|//||//|]; first by rewrite integral0.
- apply: measurableT_comp => //; apply: measurableT_comp => //.
  exact: measurable_funM.
- have := Lnorm_eq0_eq0 mf f0.
  apply: filterS => x /(_ I) /= [] /powR_eq0_eq0 + _.
  by rewrite normrM => ->; rewrite mul0r.
Qed.

Let normalized p f x := `|f x| / fine 'N_p[f].

Let normalized_ge0 p f x : (0 <= normalized p f x)%R.
Proof. by rewrite /normalized divr_ge0// fine_ge0// Lnorm_ge0. Qed.

Let measurable_normalized p f : measurable_fun [set: T] f ->
  measurable_fun [set: T] (normalized p f).
Proof. by move=> mf; apply: measurable_funM => //; exact: measurableT_comp. Qed.

Let integral_normalized f p : (0 < p)%R -> 0 < 'N_p[f] ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E) ->
  \int[mu]_x (normalized p f x `^ p)%:E = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ p / fine ('N_p[f] `^ p))%:E).
  apply: eq_integral => t _.
  rewrite powRM//; last by rewrite invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -powR_inv1; last by rewrite fine_ge0 // Lnorm_ge0.
  by rewrite fine_poweR powRAC -powR_inv1 // powR_ge0.
have fp0 : 0 < \int[mu]_x (`|f x| `^ p)%:E.
  apply: gt0_poweR fpos; rewrite ?invr_gt0//.
  by apply integral_ge0 => x _; rewrite lee_fin; exact: powR_ge0.
rewrite /Lnorm -poweRrM mulVf ?lt0r_neq0// poweRe1//; last exact: ltW.
under eq_integral do rewrite EFinM muleC.
have foo : \int[mu]_x (`|f x| `^ p)%:E < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?lee_fin ?powR_ge0//.
rewrite integralZl//; apply/eqP; rewrite eqe_pdivr_mull ?mule1.
- by rewrite fineK// ge0_fin_numE// ltW.
- by rewrite gt_eqF// fine_gt0// foo andbT.
Qed.

Lemma hoelder f g p q : measurable_fun setT f -> measurable_fun setT g ->
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
 'N_1[(f \* g)%R] <= 'N_p[f] * 'N_q[g].
Proof.
move=> mf mg p0 q0 pq.
have [f0|f0] := eqVneq 'N_p[f] 0%E; first exact: hoelder0.
have [g0|g0] := eqVneq 'N_q[g] 0%E.
  rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
  by under eq_Lnorm do rewrite /= mulrC.
have {f0}fpos : 0 < 'N_p[f] by rewrite lt_neqAle eq_sym f0//= Lnorm_ge0.
have {g0}gpos : 0 < 'N_q[g] by rewrite lt_neqAle eq_sym g0//= Lnorm_ge0.
have [foo|foo] := eqVneq 'N_p[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q[g] +oo%E; first by rewrite goo gt0_muley ?leey.
pose F := normalized p f; pose G := normalized q g.
rewrite [leLHS](_ : _ = 'N_1[(F \* G)%R] * 'N_p[f] * 'N_q[g]); last first.
  rewrite !Lnorm1.
  under [in RHS]eq_integral.
    move=> x _.
    rewrite /F /G /= /normalized (mulrC `|f x|)%R mulrA -(mulrA (_^-1)).
    rewrite (mulrC (_^-1)) -mulrA ger0_norm; last first.
      by rewrite mulr_ge0// divr_ge0 ?(fine_ge0, Lnorm_ge0, invr_ge0).
    by rewrite mulrC -normrM EFinM; over.
  rewrite /= ge0_integralZl//; last 2 first.
    - apply: measurableT_comp => //; apply: measurableT_comp => //.
      exact: measurable_funM.
    - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -muleA muleC muleA EFinM muleCA 2!muleA.
  rewrite (_ : _ * 'N_p[f] = 1) ?mul1e; last first.
    rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
    by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// fpos/= ltey.
  rewrite (_ : 'N_q[g] * _ = 1) ?mul1e// muleC.
  rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
  by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// gpos/= ltey.
rewrite -(mul1e ('N_p[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnorm_ge0//.
rewrite [leRHS](_ : _ = \int[mu]_x (F x `^ p / p + G x `^ q / q)%:E).
  rewrite Lnorm1 ae_ge0_le_integral //.
  - apply: measurableT_comp => //; apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_normalized.
  - by move=> x _; rewrite lee_fin addr_ge0// divr_ge0// ?powR_ge0// ltW.
  - by apply: measurableT_comp => //; apply: measurable_funD => //;
       apply: measurable_funM => //; apply: measurableT_comp_powR => //;
       exact: measurable_normalized.
  apply/aeW => x _; rewrite lee_fin ger0_norm ?conjugate_powR ?normalized_ge0//.
  by rewrite mulr_ge0// normalized_ge0.
under eq_integral do rewrite EFinD mulrC (mulrC _ (_^-1)).
rewrite ge0_integralD//; last 4 first.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
under eq_integral do rewrite EFinM.
rewrite {1}ge0_integralZl//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
under [X in (_ + X)%E]eq_integral => x _ do rewrite EFinM.
rewrite ge0_integralZl//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
rewrite integral_normalized//; last exact: integrable_powR.
rewrite integral_normalized//; last exact: integrable_powR.
by rewrite 2!mule1 -EFinD pq.
Qed.

End hoelder.
