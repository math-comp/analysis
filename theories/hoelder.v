(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure lebesgue_integral numfun exp.
Require Import convex itv.

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

HB.lock Definition Lnorm {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) :=
  match p with
  | p%:E => (if p == 0%R then
              mu (f @^-1` (setT `\ 0%R))
            else
              (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1)%E
  | +oo%E => (if mu [set: T] > 0 then ess_sup mu (normr \o f) else 0)%E
  | -oo%E => 0%E
  end.
Canonical locked_Lnorm := Unlockable Lnorm.unlock.
Arguments Lnorm {d T R} mu p f.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnorm1 f : 'N_1[f] = \int[mu]_x `|f x|%:E.
Proof.
rewrite unlock oner_eq0 invr1// poweRe1//.
  by apply: eq_integral => t _; rewrite powRr1.
by apply: integral_ge0 => t _; rewrite powRr1.
Qed.

Lemma Lnorm_ge0 p f : 0 <= 'N_p[f].
Proof.
rewrite unlock; move: p => [r/=|/=|//].
  by case: ifPn => // r0; exact: poweR_ge0.
by case: ifPn => // /ess_sup_ge0; apply => t/=.
Qed.

Lemma eq_Lnorm p f g : f =1 g -> 'N_p[f] = 'N_p[g].
Proof. by move=> fg; congr Lnorm; exact/funext. Qed.

Lemma Lnorm_eq0_eq0 r f : (0 < r)%R -> measurable_fun setT f ->
  'N_r%:E[f] = 0 -> ae_eq mu [set: T] (fun t => (`|f t| `^ r)%:E) (cst 0).
Proof.
move=> r0 mf; rewrite unlock (gt_eqF r0) => /poweR_eq0_eq0 fp.
apply/ae_eq_integral_abs => //=.
  apply: measurableT_comp => //.
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
  exact: measurableT_comp.
under eq_integral => x _ do rewrite ger0_norm ?powR_ge0//.
by rewrite fp//; apply: integral_ge0 => t _; rewrite lee_fin powR_ge0.
Qed.

Lemma Lnorm_powR_K f (p : R) : p != 0%R ->
  'N_p%:E[f] `^ p = \int[mu]_x (`| f x | `^ p)%:E.
Proof.
move=> p0; rewrite unlock (negbTE p0) -poweRrM mulVf// poweRe1//.
by apply: integral_ge0 => x _; rewrite lee_fin// powR_ge0.
Qed.

End Lnorm_properties.

#[global]
Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnorm_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f).

Section lnorm.
(* l-norm is just L-norm applied to counting *)
Context d {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.
Local Notation "'N_ p [ f ]" := (Lnorm [the measure _ _ of counting] p f).

Lemma Lnorm_counting p (f : R^nat) : (0 < p)%R ->
  'N_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p)%:E) `^ p^-1.
Proof.
move=> p0; rewrite unlock gt_eqF// ge0_integral_count// => k.
by rewrite lee_fin powR_ge0.
Qed.

End lnorm.

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
    measurable_fun [set: T] f -> 'N_p%:E[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E).
Proof.
move=> p0 mf foo; apply/integrableP; split.
  apply: measurableT_comp => //; apply: measurableT_comp_powR.
  exact: measurableT_comp.
rewrite ltey; apply: contra foo.
move=> /eqP/(@eqy_poweR _ _ p^-1); rewrite invr_gt0 => /(_ p0) <-.
rewrite unlock (gt_eqF p0); apply/eqP; congr (_ `^ _).
by apply/eq_integral => t _; rewrite [RHS]gee0_abs// lee_fin powR_ge0.
Qed.

Let hoelder0 f g p q : measurable_fun setT f -> measurable_fun setT g ->
    (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  'N_p%:E[f] = 0 -> 'N_1[(f \* g)%R]  <= 'N_p%:E[f] * 'N_q%:E[g].
Proof.
move=> mf mg p0 q0 pq f0; rewrite f0 mul0e Lnorm1 [leLHS](_ : _ = 0)//.
rewrite (ae_eq_integral (cst 0)) => [|//||//|]; first by rewrite integral0.
- by do 2 apply: measurableT_comp => //; exact: measurable_funM.
- apply: filterS (Lnorm_eq0_eq0 p0 mf f0) => x /(_ I)[] /powR_eq0_eq0 + _.
  by rewrite normrM => ->; rewrite mul0r.
Qed.

Let normalized p f x := `|f x| / fine 'N_p%:E[f].

Let normalized_ge0 p f x : (0 <= normalized p f x)%R.
Proof. by rewrite /normalized divr_ge0// fine_ge0// Lnorm_ge0. Qed.

Let measurable_normalized p f : measurable_fun [set: T] f ->
  measurable_fun [set: T] (normalized p f).
Proof. by move=> mf; apply: measurable_funM => //; exact: measurableT_comp. Qed.

Let integral_normalized f p : (0 < p)%R -> 0 < 'N_p%:E[f] ->
    mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E) ->
  \int[mu]_x (normalized p f x `^ p)%:E = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ p / fine ('N_p%:E[f] `^ p))%:E).
  apply: eq_integral => t _.
  rewrite powRM//; last by rewrite invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -[in LHS]powR_inv1; last by rewrite fine_ge0 // Lnorm_ge0.
  by rewrite fine_poweR powRAC -powR_inv1 // powR_ge0.
have fp0 : 0 < \int[mu]_x (`|f x| `^ p)%:E.
  rewrite unlock (gt_eqF p0) in fpos.
  apply: gt0_poweR fpos; rewrite ?invr_gt0//.
  by apply integral_ge0 => x _; rewrite lee_fin; exact: powR_ge0.
rewrite unlock (gt_eqF p0) -poweRrM mulVf ?(gt_eqF p0)// (poweRe1 (ltW fp0))//.
under eq_integral do rewrite EFinM muleC.
have foo : \int[mu]_x (`|f x| `^ p)%:E < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?lee_fin ?powR_ge0//.
rewrite integralZl//; apply/eqP; rewrite eqe_pdivr_mull ?mule1.
- by rewrite fineK// gt0_fin_numE.
- by rewrite gt_eqF// fine_gt0// foo andbT.
Qed.

Lemma hoelder f g p q : measurable_fun setT f -> measurable_fun setT g ->
    (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
 'N_1[(f \* g)%R] <= 'N_p%:E[f] * 'N_q%:E[g].
Proof.
move=> mf mg p0 q0 pq.
have [f0|f0] := eqVneq 'N_p%:E[f] 0%E; first exact: hoelder0.
have [g0|g0] := eqVneq 'N_q%:E[g] 0%E.
  rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
  by under eq_Lnorm do rewrite /= mulrC.
have {f0}fpos : 0 < 'N_p%:E[f] by rewrite lt_neqAle eq_sym f0// Lnorm_ge0.
have {g0}gpos : 0 < 'N_q%:E[g] by rewrite lt_neqAle eq_sym g0// Lnorm_ge0.
have [foo|foo] := eqVneq 'N_p%:E[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q%:E[g] +oo%E; first by rewrite goo gt0_muley ?leey.
pose F := normalized p f; pose G := normalized q g.
rewrite [leLHS](_ : _ = 'N_1[(F \* G)%R] * 'N_p%:E[f] * 'N_q%:E[g]); last first.
  rewrite !Lnorm1.
  under [in RHS]eq_integral.
    move=> x _.
    rewrite /F /G /= /normalized (mulrC `|f x|)%R mulrA -(mulrA (_^-1)).
    rewrite (mulrC (_^-1)) -mulrA ger0_norm; last first.
      by rewrite mulr_ge0// divr_ge0 ?(fine_ge0, Lnorm_ge0, invr_ge0).
    by rewrite mulrC -normrM EFinM; over.
  rewrite ge0_integralZl//; last 2 first.
    - by do 2 apply: measurableT_comp => //; exact: measurable_funM.
    - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -muleA muleC muleA EFinM muleCA 2!muleA.
  rewrite (_ : _ * 'N_p%:E[f] = 1) ?mul1e; last first.
    rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
    by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// fpos/= ltey.
  rewrite (_ : 'N_q%:E[g] * _ = 1) ?mul1e// muleC.
  rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
  by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// gpos/= ltey.
rewrite -(mul1e ('N_p%:E[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnorm_ge0//.
rewrite [leRHS](_ : _ = \int[mu]_x (F x `^ p / p + G x `^ q / q)%:E).
  rewrite Lnorm1 ae_ge0_le_integral //.
  - do 2 apply: measurableT_comp => //.
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
- do 2 apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- do 2 apply: measurableT_comp => //.
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

Section hoelder2.
Context {R : realType}.
Local Open Scope ring_scope.

Lemma hoelder2 (a1 a2 b1 b2 : R) (p q : R) :
  0 <= a1 -> 0 <= a2 -> 0 <= b1 -> 0 <= b2 ->
  0 < p -> 0 < q -> p^-1 + q^-1 = 1 ->
  a1 * b1 + a2 * b2 <= (a1 `^ p + a2 `^ p) `^ p^-1 *
                       (b1 `^ q + b2 `^ q) `^ q^-1.
Proof.
move=> a10 a20 b10 b20 p0 q0 pq.
pose f a b n : R := match n with 0%nat => a | 1%nat => b | _ => 0 end.
have mf a b : measurable_fun setT (f a b) by [].
have := hoelder [the measure _ _ of counting] (mf a1 a2) (mf b1 b2) p0 q0 pq.
rewrite !Lnorm_counting//.
rewrite (nneseries_split 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= mulr0 normr0 powR0.
rewrite 2!big_ord_recr /= big_ord0 add0e powRr1 ?normr_ge0 ?powRr1 ?normr_ge0//.
rewrite (nneseries_split 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= normr0 powR0// gt_eqF.
rewrite 2!big_ord_recr /= big_ord0 add0e -EFinD poweR_EFin.
rewrite (nneseries_split 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= normr0 powR0// gt_eqF.
rewrite 2!big_ord_recr /= big_ord0 add0e -EFinD poweR_EFin.
rewrite -EFinM invr1 powRr1; last by rewrite addr_ge0.
do 2 (rewrite ger0_norm; last by rewrite mulr_ge0).
by do 4 (rewrite ger0_norm; last by []).
Qed.

End hoelder2.

Section convex_powR.
Context {R : realType}.
Local Open Scope ring_scope.

Lemma convex_powR p : 1 <= p ->
  convex_function `[0, +oo[%classic (@powR R ^~ p).
Proof.
move=> p1 t x y /[!inE] /= /[!in_itv] /= /[!andbT] x_ge0 y_ge0.
have p0 : 0 < p by rewrite (lt_le_trans _ p1).
rewrite !convRE; set w1 := `1-(t%:inum); set w2 := t%:inum.
have [->|w10] := eqVneq w1 0.
  rewrite !mul0r !add0r; have [->|w20] := eqVneq w2 0.
    by rewrite !mul0r powR0// gt_eqF.
  by rewrite ge1r_powRZ// /w2 lt_neqAle eq_sym w20/=; apply/andP.
have [->|w20] := eqVneq w2 0.
  rewrite !mul0r !addr0 ge1r_powRZ// onem_le1// andbT.
  by rewrite lt_neqAle eq_sym onem_ge0// andbT.
have [->|p_neq1] := eqVneq p 1.
  by rewrite !powRr1// addr_ge0// mulr_ge0// /w2 ?onem_ge0.
have {p_neq1} {}p1 : 1 < p by rewrite lt_neqAle eq_sym p_neq1.
pose q := p / (p - 1).
have q1 : 1 <= q by rewrite /q ler_pdivl_mulr// ?mul1r ?gerBl// subr_gt0.
have q0 : 0 < q by rewrite (lt_le_trans _ q1).
have pq1 : p^-1 + q^-1 = 1.
  rewrite /q invf_div -{1}(div1r p) -mulrDl addrCA subrr addr0.
  by rewrite mulfV// gt_eqF.
rewrite -(@powRr1 _ (w1 * x `^ p + w2 * y `^ p)); last first.
  by rewrite addr_ge0// mulr_ge0// ?powR_ge0// /w2 ?onem_ge0// itv_ge0.
have -> : 1 = p^-1 * p by rewrite mulVf ?gt_eqF.
rewrite powRrM (ge0_ler_powR (le_trans _ (ltW p1)))//.
- by rewrite nnegrE addr_ge0// mulr_ge0 /w2 ?onem_ge0.
- by rewrite nnegrE powR_ge0.
have -> : w1 * x + w2 * y = w1 `^ (p^-1) * w1 `^ (q^-1) * x +
                            w2 `^ (p^-1) * w2 `^ (q^-1) * y.
  rewrite -!powRD pq1; [|exact/implyP..].
  by rewrite !powRr1// /w2 ?onem_ge0.
apply: (@le_trans _ _ ((w1 * x `^ p + w2 * y `^ p) `^ (p^-1) *
                       (w1 + w2) `^ q^-1)).
  pose a1 := w1 `^ p^-1 * x. pose a2 := w2 `^ p^-1 * y.
  pose b1 := w1 `^ q^-1. pose b2 := w2 `^ q^-1.
  have : a1 * b1 + a2 * b2 <= (a1 `^ p + a2 `^ p) `^ p^-1 *
                              (b1 `^ q + b2 `^ q) `^ q^-1.
    by apply: hoelder2 => //; rewrite ?mulr_ge0 ?powR_ge0.
  rewrite ?powRM ?powR_ge0 -?powRrM ?mulVf ?powRr1 ?gt_eqF ?onem_ge0/w2//.
  by rewrite mulrAC (mulrAC _ y) => /le_trans; exact.
by rewrite {2}/w1 {2}/w2 subrK powR1 mulr1.
Qed.

End convex_powR.

Section minkowski.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope convex_scope.

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Let minkowski_half (f g : T -> R) (p : R) x : 1 <= p ->
  `| 2^-1 * f x + 2^-1 * g x | `^ p <=
   2^-1 * `| f x | `^ p + 2^-1 * `| g x | `^ p.
Proof.
move=> p1.
rewrite (@le_trans _ _ ((2^-1 * `| f x | + 2^-1 * `| g x |) `^ p))//.
  rewrite ge0_ler_powR ?nnegrE ?(le_trans _ p1)//.
  by rewrite (le_trans (ler_norm_add _ _))// 2!normrM ger0_norm.
rewrite {1 3}(_ : 2^-1 = 1 - 2^-1); last by rewrite {2}(splitr 1) div1r addrK.
rewrite (@convex_powR _ _ p1 (@Itv.mk _ _ _ _)) ?inE/= ?in_itv/= ?normr_ge0//.
by rewrite /Itv.itv_cond/= in_itv/= invr_ge0 ler0n invf_le1 ?ler1n.
Qed.

Local Open Scope ereal_scope.

Let measurableT_comp_powR (f : T -> R) p :
  measurable_fun setT f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Let minkowski_lty (f g : T -> R) (p : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (1 < p)%R -> 'N_p[f] < +oo -> 'N_p[g] < +oo -> 'N_p[(f \+ g)%R] < +oo.
Proof.
move=> mf mg p1 Nfoo Ngoo.
have h x : (`| f x + g x | `^ p <= 2 `^ (p - 1) * (`| f x | `^ p  + `| g x | `^ p))%R.
  have := minkowski_half (fun x => 2 * f x)%R (fun x => 2 * g x)%R x p1.
  rewrite mulrA mulVf// mul1r mulrA mulVf// mul1r !normrM (@ger0_norm _ 2)//.
  move=> /le_trans; apply.
  rewrite !powRM// !mulrA -powR_inv1//.
  rewrite -powRD; last by apply /implyP => _.
  by rewrite (addrC _ p) -mulrDr.
rewrite /Lnorm poweR_lty//.
apply: (@le_lt_trans _ _ (\int[mu]_x (2 `^ (p - 1) * (`|f x| `^ p + `|g x| `^ p)%R)%:E)).
  apply: ge0_le_integral => //=.
  - by move=> t _; rewrite lee_fin// powR_ge0.
  - apply/EFin_measurable_fun/measurableT_comp_powR.
    by apply: measurableT_comp => //; exact: measurable_funD.
  - by move=> t _; rewrite lee_fin// mulr_ge0// ?addr_ge0 ?powR_ge0.
  - by apply/EFin_measurable_fun/measurable_funM => //; apply/measurable_funD => //;
      apply: measurableT_comp_powR => //; apply: measurableT_comp.
  - by move=> x _; rewrite lee_fin.
under eq_integral do rewrite EFinM.
rewrite ge0_integralM_EFin//; last 3 first.
  - by move=> x _; rewrite lee_fin addr_ge0// powR_ge0.
  - by apply/EFin_measurable_fun/measurable_funD => //;
      apply: measurableT_comp_powR => //; apply: measurableT_comp.
  - by rewrite powR_ge0.
rewrite lte_mul_pinfty ?lee_fin ?powR_ge0//.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 4 first.
  - by move=> x _; rewrite lee_fin powR_ge0.
  - by apply/EFin_measurable_fun;
      apply: measurableT_comp_powR => //; apply: measurableT_comp.
  - by move=> x _; rewrite lee_fin powR_ge0.
  - by apply/EFin_measurable_fun;
      apply: measurableT_comp_powR => //; apply: measurableT_comp.
rewrite lte_add_pinfty//.
- apply: lty_poweRy Nfoo.
  by rewrite invr_neq0// gt_eqF// (le_lt_trans _ p1).
- apply: lty_poweRy Ngoo.
  by rewrite invr_neq0// gt_eqF// (le_lt_trans _ p1).
Qed.

Lemma minkowski (f g : T -> R) (p : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (1 < p)%R ->
  'N_p[(f \+ g)%R] <= 'N_p[f] + 'N_p[g].
Proof.
move=> mf mg p1.
have [->|Nfoo] := eqVneq 'N_p[f] +oo.
  by rewrite addye ?leey// -ltNye (lt_le_trans _ (Lnorm_ge0 _ _ _)).
have [->|Ngoo] := eqVneq 'N_p[g] +oo.
  by rewrite addey ?leey// -ltNye (lt_le_trans _ (Lnorm_ge0 _ _ _)).
have Nfgoo : 'N_p[(f \+ g)%R] < +oo.
  by apply: minkowski_lty => //; rewrite ltey; [exact: Nfoo|exact: Ngoo].
have pm10 : (p - 1 != 0)%R.
  by rewrite gt_eqF// subr_gt0.
have p0 : (0 < p)%R.
  by apply: (lt_trans _ p1).
have pneq0 : (p != 0)%R.
  by rewrite neq_lt p0 orbT.
have : 'N_p[(f \+ g)%R] `^ p <=
    ('N_p[f] + 'N_p[g]) * 'N_p[(f \+ g)%R] `^ p * ((fine 'N_p[(f \+ g)%R])^-1)%:E.
  rewrite Lnorm_powR_K//.
  under eq_integral => x _ do rewrite -powRDm1//.
  apply: (@le_trans _ _ (\int[mu]_x ((`|f x| + `|g x|) * `|f x + g x| `^ (p - 1))%:E)).
    apply: ge0_le_integral => //.
    - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        by apply: measurableT_comp => //; exact: measurable_funD.
      apply: (measurableT_comp (f:=@powR R^~ (p-1)%R)) =>//.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        by apply: measurable_funD => //; exact: measurableT_comp.
      apply: (measurableT_comp (f:=@powR R^~ (p-1)%R)) => //.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin ler_wpmul2r// ?powR_ge0// ler_norm_add.
  under eq_integral=> x _ do rewrite mulrDl EFinD.
  rewrite ge0_integralD//; last 4 first.
    - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        exact: measurableT_comp.
      apply: (measurableT_comp (f:=@powR R^~ (p-1)%R)) => //.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        exact: measurableT_comp.
      apply: (measurableT_comp (f:=@powR R^~ (p-1)%R)) => //.
      by apply: measurableT_comp => //; exact: measurable_funD.
  apply: (@le_trans _ _ (('N_p[f] + 'N_p[g]) *
      (\int[mu]_x (`|f x + g x| `^ p)%:E) `^ (`1- (p^-1)))).
    rewrite muleDl; last 2 first.
    - rewrite fin_numElt (@lt_le_trans _ _ 0) ?poweR_ge0// andTb poweR_lty//.
      by rewrite (@lty_poweRy _ _ (p^-1))// invr_neq0// eq_sym neq_lt (@lt_trans _ _ 1)%R.
    - by rewrite ge0_adde_def//= inE Lnorm_ge0.
    rewrite lee_add//.
    - apply: (@le_trans _ _ ('N_1[(f \* (@powR R ^~ (p - 1) \o normr \o (f \+ g)))%R])).
        rewrite /Lnorm invr1 [leRHS]poweRe1/=; last first.
          by apply: integral_ge0 => x _; rewrite lee_fin powRr1.
        rewrite le_eqVlt; apply/orP; left; apply/eqP.
        apply: eq_integral => x _; congr EFin.
          by rewrite powRr1// -{1}(ger0_norm (powR_ge0 _ _)) -normrM.
      apply: le_trans.
        apply: (@hoelder _ _ _ _ _ _ p (p / (p - 1))) => //.
        - by apply: (measurableT_comp (measurableT_comp _ _) (measurable_funD _ _)).
        - by rewrite divr_gt0// subr_gt0.
        - by rewrite invf_div -(oneminv pneq0) addrCA subrr addr0.
      rewrite le_eqVlt; apply/orP; left; apply/eqP; apply: congr2=>[//|].
      rewrite (oneminv pneq0) -[in RHS]invf_div /Lnorm; apply: congr2 => [|//].
      by apply: eq_integral => x _;
        rewrite norm_powR// normr_id -powRrM mulrC -mulrA (mulrC (_^-1)) divff ?mulr1.
    - rewrite [leLHS](_ : _ = 'N_1[(g \* (fun x => `|f x + g x| `^ (p - 1)))%R]); last first.
        under eq_integral=> x _ do rewrite -(normr_id (f x + g x))%R -norm_powR// -normrM.
        by rewrite -(Lnorm1).
      apply: le_trans.
        apply: (@hoelder _ _ _ _ _ _ p ((`1-(p^-1))^-1)) => //.
        - by apply: measurableT_comp_powR; apply: measurableT_comp => //; apply: measurable_funD => //.
        - by rewrite invr_gt0 onem_gt0// invf_lt1.
        - by rewrite invrK /onem (addrC 1%R) addrA subrr add0r.
      rewrite le_eqVlt; apply/orP; left; apply/eqP.
      apply: congr1; rewrite /Lnorm invrK; apply: congr2=>[|//].
      by apply: eq_integral => x _;
         rewrite ger0_norm ?powR_ge0// -powRrM oneminv// invf_div mulrCA divff ?mulr1.
  rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite -muleA; congr (_ * _).
  under [X in X * _]eq_integral=> x _ do rewrite powRDm1 ?subr_gt0//.
  rewrite poweRD; last by rewrite poweRD_defE gt_eqF ?implyFb// subr_gt0 invf_lt1//.
  rewrite poweRe1; last by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
  congr (_ * _); rewrite poweRN /Lnorm ?fine_poweR// fin_numElt (@lt_le_trans _ _ 0)// ?andTb.
    by rewrite (lty_poweRy (invr_neq0 pneq0) Nfgoo)//.
  by apply: integral_ge0=> x _; rewrite lee_fin powR_ge0.
have [-> _|Nfg0] := (eqVneq 'N_p[(f \+ g)%R] 0).
  by rewrite adde_ge0 ?Lnorm_ge0.
rewrite lee_pdivl_mulr ?fine_gt0// ?Nfgoo ?andbT; last by
  rewrite lt_neqAle Lnorm_ge0 andbT eq_sym.
rewrite -{1}(@fineK _ ('N_p[(f \+ g)%R] `^ p)); last by
  rewrite fin_numElt (@lt_le_trans _ _ 0 -oo _ _ (poweR_ge0 _ _))// andTb poweR_lty.
rewrite -(invrK (fine _)) lee_pdivr_mull; last by
  rewrite invr_gt0 fine_gt0// poweR_lty// andbT lt_neqAle eq_sym poweR_eq0 poweR_ge0// andbT;
  rewrite neq_lt (lt_trans _ p1)// orbT andbT.
rewrite muleC -muleA -{1}(@fineK _ ('N_p[(f \+ g)%R] `^ p)); last by
  rewrite fin_numElt (@lt_le_trans _ _ 0 -oo _ _ (poweR_ge0 _ _))// andTb poweR_lty.
rewrite -EFinM divff ?mule1; last by
  rewrite neq_lt fine_gt0 ?orbT// lt_neqAle poweR_ge0 andbT eq_sym poweR_eq0 ?Lnorm_ge0// neq_lt (lt_trans _ p1)// orbT andbT Nfg0 andTb poweR_lty.
by rewrite ?fineK// fin_numElt (@lt_le_trans _ _ 0 -oo _ _ (Lnorm_ge0 _ _ _)).
Qed.

End minkowski.
