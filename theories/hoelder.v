(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals ereal.
From mathcomp Require Import topology normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun exp convex interval_inference.

(**md**************************************************************************)
(* # Hoelder's Inequality                                                     *)
(*                                                                            *)
(* This file provides Hoelder's inequality and its consequences, most notably *)
(* Minkowski's inequality and the convexity of the power function.            *)
(* ```                                                                        *)
(*           'N[mu]_p[f] == the p-norm of f with measure mu                   *)
(* ```                                                                        *)
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
              (mu (f @^-1` (setT `\ 0%R)))
            else
              (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1)%E
  | +oo%E => (if mu [set: T] > 0 then ess_sup mu (normr \o f) else 0)%E
  | -oo%E => (if mu [set: T] > 0 then ess_inf mu (normr \o f) else 0)%E
  end.
Canonical locked_Lnorm := Unlockable Lnorm.unlock.
Arguments Lnorm {d T R} mu p f.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnorm0 p : 1 <= p -> 'N_p[cst 0%R] = 0.
Proof.
rewrite unlock /Lnorm.
case: p => [r||//].
- rewrite lee_fin => r1.
  have r0: r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
  rewrite gt_eqF ?(lt_le_trans _ r1)//.
  under eq_integral => x _ do rewrite /= normr0 powR0//.
  by rewrite integral0 poweR0r// invr_neq0.
case: ifPn => //mu0 _.
rewrite (_ : normr \o _ = 0%R); last by apply: funext => x/=; rewrite normr0.
exact: ess_sup_cst.
Qed.

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
case: ifPn => // muT0.
Admitted.

Lemma eq_Lnorm p f g : f =1 g -> 'N_p[f] = 'N_p[g].
Proof. by move=> fg; congr Lnorm; exact/funext. Qed.

Lemma Lnorm_eq0_eq0 (f : T -> R) p :
  measurable_fun setT f -> (0 < p)%E -> 'N_p[f] = 0 -> f = 0%R %[ae mu].
Proof.
rewrite unlock /Lnorm => mf.
case: p => [r r0||].
- case: ifPn => _.
    rewrite preimage_setI preimage_setT setTI -preimage_setC.
(*    move=> /poweR_eq0_eq0 /negligibleP.
    move/(_ (measurableC _)); rewrite -[X in d.-measurable X]setTI.
    move/(_ (mf _ _ _)).
    by case=> // A [mA muA0 fA]; exists A; split => // x/= ?; exact: fA.
  move=> /poweR_eq0_eq0.
  move=> /(_ (integral_ge0 _ _)) h.
  have: (\int[mu]_x (`|f x| `^ r)%:E)%E = 0 by apply: h => x _; rewrite lee_fin powR_ge0.
  under eq_integral => x _ do rewrite -[_%:E]gee0_abs ?lee_fin ?powR_ge0//.
  have mp: measurable_fun [set: T] (fun x : T => (`|f x| `^ r)%:E).
    apply: measurableT_comp => //.
    apply (measurableT_comp (measurable_powR _)) => //.
    exact: measurableT_comp.
  move/(ae_eq_integral_abs _ measurableT mp).
  apply: filterS => x/= /[apply].
  by case=> /powR_eq0_eq0 /eqP; rewrite normr_eq0 => /eqP.
- case: ifPn => [mu0 _|].
    exact: ess_sup_eq0.
  rewrite ltNge => /negbNE mu0 _ _.
  suffices mueq0: mu setT = 0 by exact: ae_eq0.
  move: mu0 (measure_ge0 mu setT) => mu0 mu1.
  suffices: (mu setT <= 0 <= mu setT)%E by move/le_anti.
  by rewrite mu0 mu1.
by [].
Qed.*) Admitted.

Lemma powR_Lnorm f r : r != 0%R ->
  'N_r%:E[f] `^ r = \int[mu]_x (`| f x | `^ r)%:E.
Proof.
move=> r0; rewrite unlock (negbTE r0) -poweRrM mulVf// poweRe1//.
by apply: integral_ge0 => x _; rewrite lee_fin// powR_ge0.
Qed.

Lemma oppr_Lnorm f p :
  'N_p[\- f]%R = 'N_p[f].
Proof.
rewrite unlock /Lnorm.
case: p => /= [r||//].
  case: eqP => _. (*congr ((mu _) `^ _).
    rewrite !preimage_setI.
    congr (_ `&` _).
    rewrite -!preimage_setC.
    congr (~` _).
    rewrite /preimage.
    apply: funext => x/=.
    rewrite -{1}oppr0.
    apply: propext. split; last by move=> ->.
    by move/oppr_inj.
  by under eq_integral => x _ do rewrite normrN.
rewrite compA (_ : normr \o -%R = normr)//.
apply: funext => x/=; exact: normrN.
Qed.*) Admitted.

Lemma Lnorm_cst1 r : ('N_r%:E[cst 1%R] = (mu setT)`^(r^-1)).
Proof.
rewrite unlock /Lnorm.
case: ifPn => [_|].
(*  by rewrite preimage_cst ifT// inE/=; split => //; apply/eqP; rewrite oner_neq0.
under eq_integral => x _ do rewrite normr1 powR1 (_ : 1 = cst 1 x)%R// -indicT.
by rewrite integral_indic// setTI.
Qed.*) Admitted.

End Lnorm_properties.

#[global]

Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnorm_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f).

Section lnorm.
(* l-norm is just L-norm applied to counting *)
Context d {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.
Local Notation "'N_ p [ f ]" := (Lnorm counting p f).

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
rewrite -lte_fin.
move=> mf mg p0 q0 pq f0; rewrite f0 mul0e Lnorm1 [leLHS](_ : _ = 0)//.
rewrite (ae_eq_integral (cst 0)) => [|//||//|]; first by rewrite integral0.
- by do 2 apply: measurableT_comp => //; exact: measurable_funM.
- apply: filterS (Lnorm_eq0_eq0 mf p0 f0) => x /(_ I)[] + _.
  by rewrite normrM => ->; rewrite normr0 mul0r.
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
rewrite integralZl//; apply/eqP; rewrite eqe_pdivrMl ?mule1.
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
have {f0}fpos : 0 < 'N_p%:E[f] by rewrite lt0e f0 Lnorm_ge0.
have {g0}gpos : 0 < 'N_q%:E[g] by rewrite lt0e g0 Lnorm_ge0.
have [foo|foo] := eqVneq 'N_p%:E[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q%:E[g] +oo%E; first by rewrite goo gt0_muley ?leey.
pose F := normalized p f; pose G := normalized q g.
rewrite [leLHS](_ : _ = 'N_1[(F \* G)%R] * 'N_p%:E[f] * 'N_q%:E[g]); last first.
  rewrite !Lnorm1; under [in RHS]eq_integral.
    move=> x _; rewrite /F /G /normalized/=.
    rewrite ger0_norm; last by rewrite mulr_ge0 ?divr_ge0 ?fine_ge0 ?Lnorm_ge0.
    by rewrite mulrACA -normrM EFinM; over.
  rewrite ge0_integralZr//; last 2 first.
    - by do 2 apply: measurableT_comp => //; exact: measurable_funM.
    - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -!muleA [X in _ * X](_ : _ = 1) ?mule1// EFinM muleACA.
  rewrite (_ : _ * 'N_p%:E[f] = 1) ?mul1e; last first.
    rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
    by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// fpos/= ltey.
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
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 4 first.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurable_funM => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurable_funM => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
under eq_integral do rewrite EFinM.
rewrite [X in X + _]ge0_integralZr//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
under [X in _ + X]eq_integral => x _ do rewrite EFinM.
rewrite ge0_integralZr//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
rewrite integral_normalized//; last exact: integrable_powR.
rewrite integral_normalized//; last exact: integrable_powR.
by rewrite 2!mul1e -EFinD pq.
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
have := hoelder counting (mf a1 a2) (mf b1 b2) p0 q0 pq.
rewrite !Lnorm_counting//.
rewrite (nneseries_split 0 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= mulr0 normr0 powR0.
rewrite big_mkord 2!big_ord_recr/= big_ord0 add0e.
rewrite powRr1 ?normr_ge0 ?powRr1 ?normr_ge0//.
rewrite (nneseries_split 0 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= normr0 powR0// gt_eqF.
rewrite big_mkord 2!big_ord_recr /= big_ord0 add0e -EFinD poweR_EFin.
rewrite (nneseries_split 0 2); last by move=> k; rewrite lee_fin powR_ge0.
rewrite ereal_series_cond eseries0 ?adde0; last first.
  by move=> [//|] [//|n _]; rewrite /f /= normr0 powR0// gt_eqF.
rewrite big_mkord 2!big_ord_recr /= big_ord0 add0e -EFinD poweR_EFin.
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
  by rewrite !mul0r !addr0 ge1r_powRZ// onem_le1// andbT lt0r w10 onem_ge0.
have [->|p_neq1] := eqVneq p 1.
  by rewrite !powRr1// addr_ge0// mulr_ge0// /w2 ?onem_ge0.
have {p_neq1} {}p1 : 1 < p by rewrite lt_neqAle eq_sym p_neq1.
pose q := p / (p - 1).
have q1 : 1 <= q by rewrite /q ler_pdivlMr// ?mul1r ?gerBl// subr_gt0.
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
Implicit Types (f g : T -> R) (p : R).

Let convex_powR_abs_half f g p x : 1 <= p ->
  `| 2^-1 * f x + 2^-1 * g x | `^ p <=
   2^-1 * `| f x | `^ p + 2^-1 * `| g x | `^ p.
Proof.
move=> p1; rewrite (@le_trans _ _ ((2^-1 * `| f x | + 2^-1 * `| g x |) `^ p))//.
  rewrite ge0_ler_powR ?nnegrE ?(le_trans _ p1)//.
  by rewrite (le_trans (ler_normD _ _))// 2!normrM ger0_norm.
rewrite {1 3}(_ : 2^-1 = 1 - 2^-1); last by rewrite {2}(splitr 1) div1r addrK.
rewrite (@convex_powR _ _ p1 (Itv01 _ _))// ?inE/= ?in_itv/= ?normr_ge0 ?invr_ge0//.
by rewrite invf_le1 ?ler1n.
Qed.

Let measurableT_comp_powR f p :
  measurable_fun setT f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).
Local Open Scope ereal_scope.

Let minkowski1 f g p : measurable_fun setT f -> measurable_fun setT g ->
  'N_1[(f \+ g)%R] <= 'N_1[f] + 'N_1[g].
Proof.
move=> mf mg.
rewrite !Lnorm1 -ge0_integralD//; [|by do 2 apply: measurableT_comp..].
rewrite ge0_le_integral//.
- by do 2 apply: measurableT_comp => //; exact: measurable_funD.
- by move=> x _; rewrite adde_ge0.
- by apply/measurableT_comp/measurable_funD; exact/measurableT_comp.
- by move=> x _; rewrite lee_fin ler_normD.
Qed.

Let minkowski_lty f g p :
  measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R ->
  'N_p%:E[f] < +oo -> 'N_p%:E[g] < +oo -> 'N_p%:E[(f \+ g)%R] < +oo.
Proof.
move=> mf mg p1 Nfoo Ngoo.
have p0 : p != 0%R by rewrite gt_eqF// (lt_le_trans _ p1).
have h x : (`| f x + g x | `^ p <=
            2 `^ (p - 1) * (`| f x | `^ p + `| g x | `^ p))%R.
  have := convex_powR_abs_half (fun x => 2 * f x)%R (fun x => 2 * g x)%R x p1.
  rewrite !normrM (@ger0_norm _ 2)// !mulrA mulVf// !mul1r => /le_trans; apply.
  rewrite !powRM// !mulrA -powR_inv1// -powRD ?pnatr_eq0 ?implybT//.
  by rewrite (addrC _ p) -mulrDr.
rewrite unlock (gt_eqF (lt_le_trans _ p1))// poweR_lty//.
pose x := \int[mu]_x (2 `^ (p - 1) * (`|f x| `^ p + `|g x| `^ p))%:E.
apply: (@le_lt_trans _ _ x).
  rewrite ge0_le_integral//=.
  - by move=> t _; rewrite lee_fin// powR_ge0.
  - apply/measurable_EFinP/measurableT_comp_powR/measurableT_comp => //.
    exact: measurable_funD.
  - by move=> t _; rewrite lee_fin mulr_ge0 ?addr_ge0 ?powR_ge0.
  - by apply/measurable_EFinP/measurable_funM/measurable_funD => //;
      exact/measurableT_comp_powR/measurableT_comp.
  - by move=> ? _; rewrite lee_fin.
rewrite {}/x; under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin ?powR_ge0//; last 2 first.
  - by move=> x _; rewrite lee_fin addr_ge0// powR_ge0.
  - by apply/measurable_EFinP/measurable_funD => //;
      exact/measurableT_comp_powR/measurableT_comp.
rewrite lte_mul_pinfty ?lee_fin ?powR_ge0//.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 4 first.
  - by move=> x _; rewrite lee_fin powR_ge0.
  - exact/measurable_EFinP/measurableT_comp_powR/measurableT_comp.
  - by move=> x _; rewrite lee_fin powR_ge0.
  - exact/measurable_EFinP/measurableT_comp_powR/measurableT_comp.
by rewrite lte_add_pinfty// -powR_Lnorm ?(gt_eqF (lt_trans _ p1))// poweR_lty.
Qed.

Lemma minkowski f g p :
  measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R ->
  'N_p%:E[(f \+ g)%R] <= 'N_p%:E[f] + 'N_p%:E[g].
Proof.
move=> mf mg; rewrite le_eqVlt => /predU1P[<-|p1]; first exact: minkowski1.
have [->|Nfoo] := eqVneq 'N_p%:E[f] +oo.
  by rewrite addye ?leey// -ltNye (lt_le_trans _ (Lnorm_ge0 _ _ _)).
have [->|Ngoo] := eqVneq 'N_p%:E[g] +oo.
  by rewrite addey ?leey// -ltNye (lt_le_trans _ (Lnorm_ge0 _ _ _)).
have Nfgoo : 'N_p%:E[(f \+ g)%R] < +oo.
  by rewrite minkowski_lty// ?ltW// ltey; [exact: Nfoo|exact: Ngoo].
suff : 'N_p%:E[(f \+ g)%R] `^ p <= ('N_p%:E[f] + 'N_p%:E[g]) *
    'N_p%:E[(f \+ g)%R] `^ p * (fine 'N_p%:E[(f \+ g)%R])^-1%:E.
  have [-> _|Nfg0] := eqVneq 'N_p%:E[(f \+ g)%R] 0.
    by rewrite adde_ge0 ?Lnorm_ge0.
  rewrite lee_pdivlMr ?fine_gt0// ?lt0e ?Nfg0 ?Lnorm_ge0//.
  rewrite -{1}(@fineK _ ('N_p%:E[(f \+ g)%R] `^ p)); last first.
    by rewrite fin_num_poweR// ge0_fin_numE// Lnorm_ge0.
  rewrite -(invrK (fine _)) lee_pdivrMl; last first.
    rewrite invr_gt0 fine_gt0// (poweR_lty _ Nfgoo) andbT poweR_gt0//.
    by rewrite lt0e Nfg0 Lnorm_ge0.
  rewrite fineK ?ge0_fin_numE ?Lnorm_ge0// => /le_trans; apply.
  rewrite lee_pdivrMl; last first.
    by rewrite fine_gt0// poweR_lty// andbT poweR_gt0// lt0e Nfg0 Lnorm_ge0.
  by rewrite fineK// 1?muleC// fin_num_poweR// ge0_fin_numE ?Lnorm_ge0.
have p0 : (0 < p)%R by exact: (lt_trans _ p1).
rewrite powR_Lnorm ?gt_eqF//.
under eq_integral => x _ do rewrite -mulr_powRB1//.
apply: (@le_trans _ _
    (\int[mu]_x ((`|f x| + `|g x|) * `|f x + g x| `^ (p - 1))%:E)).
  rewrite ge0_le_integral//.
  - by move=> ? _; rewrite lee_fin mulr_ge0// powR_ge0.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact/measurableT_comp/measurable_funD.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - by move=> ? _; rewrite lee_fin mulr_ge0// powR_ge0.
  - apply/measurableT_comp => //; apply: measurable_funM.
      by apply/measurable_funD => //; exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - by move=> ? _; rewrite lee_fin ler_wpM2r// ?powR_ge0// ler_normD.
under eq_integral=> ? _ do rewrite mulrDl EFinD.
rewrite ge0_integralD//; last 4 first.
  - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - by move=> x _; rewrite lee_fin mulr_ge0// powR_ge0.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
rewrite [leRHS](_ : _ = ('N_p%:E[f] + 'N_p%:E[g]) *
    (\int[mu]_x (`|f x + g x| `^ p)%:E) `^ `1-(p^-1)).
  rewrite muleDl; last 2 first.
    - rewrite fin_num_poweR// -powR_Lnorm ?gt_eqF// fin_num_poweR//.
      by rewrite ge0_fin_numE ?Lnorm_ge0.
    - by rewrite ge0_adde_def// inE Lnorm_ge0.
  apply: leeD.
  - pose h := (@powR R ^~ (p - 1) \o normr \o (f \+ g))%R; pose i := (f \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]%R); last first.
      rewrite Lnorm1; apply: eq_integral => x _.
      by rewrite normrM (ger0_norm (powR_ge0 _ _)).
    rewrite [X in _ * X](_ : _ = 'N_(p / (p - 1))%:E[h]); last first.
      rewrite unlock mulf_eq0 gt_eqF//= invr_eq0 subr_eq0 (gt_eqF p1).
      rewrite onemV ?gt_eqF// invf_div; apply: congr2; last by [].
      apply: eq_integral => x _; congr EFin.
      rewrite norm_powR// normr_id -powRrM mulrCA divff ?mulr1//.
      by rewrite subr_eq0 gt_eqF.
    apply: (@hoelder _ _ _ _ _ _ p (p / (p - 1))) => //.
    + exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
    + by rewrite divr_gt0// subr_gt0.
    + by rewrite invf_div -onemV ?gt_eqF// addrCA subrr addr0.
  - pose h := (fun x => `|f x + g x| `^ (p - 1))%R; pose i := (g \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]); last first.
      rewrite Lnorm1; apply: eq_integral => x _ .
      by rewrite normrM norm_powR// normr_id.
    rewrite [X in _ * X](_ : _ = 'N_((1 - p^-1)^-1)%:E[h])//; last first.
      rewrite unlock invrK invr_eq0 subr_eq0 eq_sym invr_eq1 (gt_eqF p1).
      apply: congr2; last by [].
      apply: eq_integral => x _; congr EFin.
      rewrite -/(onem p^-1) onemV ?gt_eqF// norm_powR// normr_id -powRrM.
      by rewrite invf_div mulrCA divff ?subr_eq0 ?gt_eqF// ?mulr1.
    apply: (le_trans (@hoelder _ _ _ _ _ _ p (1 - p^-1)^-1 _ _ _ _ _)) => //.
    + exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
    + by rewrite invr_gt0 onem_gt0// invf_lt1.
    + by rewrite invrK addrCA subrr addr0.
rewrite -muleA; congr (_ * _).
under [X in X * _]eq_integral=> x _ do rewrite mulr_powRB1 ?subr_gt0//.
rewrite poweRD; last by rewrite poweRD_defE gt_eqF ?implyFb// subr_gt0 invf_lt1.
rewrite poweRe1; last by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
congr (_ * _); rewrite poweRN.
- by rewrite unlock gt_eqF// fine_poweR.
- by rewrite -powR_Lnorm ?gt_eqF// fin_num_poweR// ge0_fin_numE ?Lnorm_ge0.
Qed.

Lemma minkowski' f g p :
  measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R ->
  'N_p%:E[f] <= 'N_p%:E[f \+ g] + 'N_p%:E[g].
Proof.
move=> mf mg p1.
rewrite (_ : f = ((f \+ g) \+ (-%R \o g))%R); last first.
  by apply: funext => x /=; rewrite -addrA subrr addr0.
rewrite [X in _ <= 'N__[X] + _](_ : ((f \+ g \- g) \+ g)%R = (f \+ g)%R); last first.
  by apply: funext => x /=; rewrite -addrA [X in _ + _ + X]addrC subrr addr0.
rewrite (_ : 'N__[g] = 'N_p%:E[-%R \o g]); last first.
  by rewrite oppr_Lnorm.
apply: minkowski => //.
  apply: measurable_funD => //.
apply: measurableT_comp => //.
Qed.

End minkowski.
