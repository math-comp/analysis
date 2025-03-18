(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra unstable boolp interval_inference.
From mathcomp Require Import classical_sets functions cardinality fsbigop reals.
From mathcomp Require Import ereal topology normedtype sequences real_interval.
From mathcomp Require Import esum measure ess_sup_inf lebesgue_measure.
From mathcomp Require Import lebesgue_integral numfun exp convex.

(**md**************************************************************************)
(* # Hoelder's Inequality                                                     *)
(*                                                                            *)
(* This file provides the Lp-norm, Hoelder's inequality and its consequences, *)
(* most notably Minkowski's inequality, the convexity of the power function,  *)
(* and a definition of Lp-spaces.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*         'N[mu]_p[f] == the Lp-norm of f with measure mu                    *)
(*         conjugate p == a real number q such that p^-1 + q^-1 = 1 when      *)
(*                        p is real, otherwise conjugate +oo = 1 and          *)
(*                        conjugate -oo = 0                                   *)
(* ```                                                                        *)
(*                                                                            *)
(* Lp-spaces and properties of Lp-norms:                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*    finite_norm mu p f := the L-norm of real-valued function f is finite    *)
(*                          The parameter p is an extended real.              *)
(*        LfunType mu p1 == type of measurable functions f with a finite      *)
(*                          L-norm                                            *)
(*                          p1 is a proof that the extended real number p is  *)
(*                          greater or equal to 1.                            *)
(*                          The HB class is Lfun.                             *)
(*            f \in lfun == holds for f : LfunType mu p1                      *)
(*            Lequiv f g == f is equal to g almost everywhere                 *)
(*                          The functions f and g have type LfunType mu p1.   *)
(*                          Lequiv is made a canonical equivalence relation.  *)
(*      LspaceType mu p1 == type of the elements of the Lp space for the      *)
(*                          measure mu                                        *)
(*          mu.-Lspace p == Lp space as a set                                 *)
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
Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").

Declare Scope Lnorm_scope.

Local Open Scope ereal_scope.
HB.lock Definition Lnorm {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (\int[mu]_x `|f x| `^ p) `^ p^-1
    (* (mu (f @^-1` (setT `\ 0%R))) when p = 0? *)
  | +oo%E => if mu [set: T] > 0 then ess_sup mu (abse \o f) else 0
  | -oo%E => if mu [set: T] > 0 then ess_inf mu (abse \o f) else 0
  end.
Canonical locked_Lnorm := Unlockable Lnorm.unlock.
Arguments Lnorm {d T R} mu p f.
Local Close Scope ereal_scope.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnorm0 p : 1 <= p -> 'N_p[cst 0] = 0.
Proof.
rewrite unlock /Lnorm.
case: p => [r||//].
- rewrite lee_fin => r1.
  have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
  under eq_integral => x _ do rewrite /= normr0 powR0//.
  by rewrite integral0 poweR0r// invr_neq0.
case: ifPn => //mu0 _; rewrite (ess_sup_ae_cst 0)//.
by apply: nearW => x; rewrite /= normr0.
Qed.

Lemma Lnorm1 f : 'N_1[f] = \int[mu]_x `|f x|.
Proof.
rewrite unlock invr1// poweRe1//; under eq_integral do [rewrite poweRe1//=] => //.
exact: integral_ge0.
Qed.

Lemma eq_Lnorm p f g : f =1 g -> 'N_p[f] = 'N_p[g].
Proof. by move=> fg; congr Lnorm; apply/eq_fun => ?; rewrite /= fg. Qed.

Lemma poweR_Lnorm f r : r != 0%R ->
  'N_r%:E[f] `^ r = \int[mu]_x (`| f x | `^ r).
Proof.
move=> r0; rewrite unlock -poweRrM mulVf// poweRe1//.
by apply: integral_ge0 => x _; exact: poweR_ge0.
Qed.

Lemma oppe_Lnorm f p : 'N_p[\- f]%E = 'N_p[f].
Proof.
have NfE : abse \o (\- f) = abse \o f.
  by apply/funext => x /=; rewrite abseN.
rewrite unlock /Lnorm NfE; case: p => /= [r|//|//].
by under eq_integral => x _ do rewrite abseN.
Qed.

Lemma Lnorm_cst1 r : ('N_r%:E[cst 1] = (mu setT)`^(r^-1)).
Proof.
rewrite unlock /Lnorm; under eq_integral do rewrite /= normr1 powR1.
by rewrite integral_cst// mul1e.
Qed.

End Lnorm_properties.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p (EFin \o f)).

Lemma Lnormr_ge0 p f : 0 <= 'N_p[f].
Proof.
rewrite unlock; move: p => [r/=|/=|//]; first exact: poweR_ge0.
- by case: ifPn => // /ess_sup_ger; apply => t/=.
- by case: ifPn => // muT0; apply/ess_infP/nearW => x /=.
Qed.

Lemma Lnormr_eq0_eq0 (f : T -> R) p :
  measurable_fun setT f -> (0 < p)%E -> 'N_p[f] = 0 -> f = 0%R %[ae mu].
Proof.
rewrite unlock /Lnorm => mf.
case: p => [r||//].
- rewrite lte_fin => r0 /poweR_eq0_eq0 => /(_ (integral_ge0 _ _)) h.
  have : \int[mu]_x (`|f x| `^ r)%:E = 0.
    by apply: h => x _; rewrite lee_fin powR_ge0.
  under eq_integral => x _ do rewrite -[_%:E]gee0_abs ?lee_fin ?powR_ge0//.
  have mp : measurable_fun [set: T] (fun x : T => (`|f x| `^ r)%:E).
    apply: measurableT_comp => //.
    apply (measurableT_comp (measurable_powR _)) => //.
    exact: measurableT_comp.
  move/(ae_eq_integral_abs _ measurableT mp).
  apply: filterS => x/= /[apply].
  by case=> /powR_eq0_eq0 /eqP; rewrite normr_eq0 => /eqP.
- case: ifPn => [mu0 _|].
    move=> /abs_sup_eq0_ae_eq/=.
    by apply: filterS => x/= /(_ I) /eqP + _; rewrite eqe => /eqP.
  rewrite ltNge => /negbNE mu0 _ _.
  suffices mueq0: mu setT = 0 by exact: ae_eq0.
  by apply/eqP; rewrite eq_le mu0/=.
Qed.

Lemma powR_Lnorm f r : r != 0%R ->
  'N_r%:E[f] `^ r = \int[mu]_x (`| f x | `^ r)%:E.
Proof. by move=> r0; rewrite poweR_Lnorm. Qed.

Lemma oppr_Lnorm f p : 'N_p[\- f]%R = 'N_p[f].
Proof. by rewrite -[RHS]oppe_Lnorm. Qed.

End Lnorm_properties.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `Lnormr_ge0`")]
Notation Lnorm_ge0 := Lnormr_ge0 (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `Lnormr_eq0_eq0`")]
Notation Lnorm_eq0_eq0 := Lnormr_eq0_eq0 (only parsing).

#[global]
Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnormr_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f) : ereal_scope.

Section lnorm.
Context d {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.
(** lp-norm is just Lp-norm applied to counting *)
Local Notation "'N_ p [ f ]" := (Lnorm counting p (EFin \o f)).

Lemma Lnorm_counting p (f : R^nat) : (0 < p)%R ->
  'N_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p)%:E) `^ p^-1.
Proof.
by move=> p0; rewrite unlock ge0_integral_count// => k; rewrite poweR_ge0.
Qed.

End lnorm.

Section conjugate.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Hypothesis (p1 : (1 <= p)%E).

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition conjugate :=
  match p with
  | r%:E => [get q : R | r^-1 + q^-1 = 1]%:E
  | +oo  => 1
  | -oo  => 0
  end.

Lemma conjugateE :
  conjugate = if p is r%:E then (r * (r-1)^-1)%:E
              else if p == +oo then 1 else 0.
Proof.
rewrite /conjugate.
case: p p1 => [r|//=|//].
rewrite lee_fin => r1.
have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
congr EFin; apply: get_unique.
  by rewrite invf_div mulrBl divff// mul1r addrCA subrr addr0.
move=> /= y ry1.
suff -> : y = (1 - r^-1)^-1.
  by rewrite -(mul1r r^-1) -{1}(divff r0) -mulrBl invf_div.
by rewrite -ry1 -addrAC subrr add0r invrK.
Qed.

End conjugate.

Section hoelder.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p q : R) (f g : T -> R).

Let measurableT_comp_powR f p :
  measurable_fun [set: T] f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p (EFin \o f)).

Let integrable_powR f p : (0 < p)%R ->
    measurable_fun [set: T] f -> 'N_p%:E[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E).
Proof.
move=> p0 mf foo; apply/integrableP; split.
  apply: measurableT_comp => //; apply: measurableT_comp_powR.
  exact: measurableT_comp.
rewrite ltey; apply: contra foo.
move=> /eqP/(@eqy_poweR _ _ p^-1); rewrite invr_gt0 => /(_ p0) <-.
rewrite unlock; apply/eqP; congr (_ `^ _).
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
- apply: filterS (Lnormr_eq0_eq0 mf p0 f0) => x /(_ I) + _.
  by rewrite /= normrM => ->; rewrite normr0 mul0r.
Qed.

Let normalized p f x := `|f x| / fine 'N_p%:E[f].

Let normalized_ge0 p f x : (0 <= normalized p f x)%R.
Proof. by rewrite /normalized divr_ge0// fine_ge0// Lnormr_ge0. Qed.

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
  rewrite powRM//; last by rewrite invr_ge0 fine_ge0// Lnormr_ge0.
  rewrite -[in LHS]powR_inv1; last by rewrite fine_ge0 // Lnormr_ge0.
  by rewrite fine_poweR powRAC -powR_inv1 // powR_ge0.
have fp0 : 0 < \int[mu]_x (`|f x| `^ p)%:E.
  rewrite unlock in fpos.
  apply: gt0_poweR fpos; rewrite ?invr_gt0//.
  by apply integral_ge0 => x _; rewrite lee_fin; exact: powR_ge0.
rewrite unlock -poweRrM mulVf ?(gt_eqF p0)// (poweRe1 (ltW fp0))//.
under eq_integral do rewrite EFinM muleC.
have foo : \int[mu]_x (`|f x| `^ p)%:E < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?lee_fin ?powR_ge0//.
rewrite integralZl//; apply/eqP; rewrite eqe_pdivrMl ?mule1.
- by rewrite fineK// gt0_fin_numE.
- by rewrite gt_eqF// fine_gt0// foo andbT.
Qed.

Lemma hoelder (f g : T -> R) p q :
    measurable_fun [set: T] f -> measurable_fun [set: T] g ->
    (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
 'N_1[(f \* g)%R] <= 'N_p%:E[f] * 'N_q%:E[g].
Proof.
move=> mf mg p0 q0 pq.
have [f0|f0] := eqVneq 'N_p%:E[f] 0%E; first exact: hoelder0.
have [g0|g0] := eqVneq 'N_q%:E[g] 0%E.
  rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
  by under eq_Lnorm do rewrite /= mulrC.
have {f0}fpos : 0 < 'N_p%:E[f] by rewrite lt0e f0 Lnormr_ge0.
have {g0}gpos : 0 < 'N_q%:E[g] by rewrite lt0e g0 Lnormr_ge0.
have [foo|foo] := eqVneq 'N_p%:E[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q%:E[g] +oo%E; first by rewrite goo gt0_muley ?leey.
pose F := normalized p f; pose G := normalized q g.
rewrite [leLHS](_ : _ = 'N_1[(F \* G)%R] * 'N_p%:E[f] * 'N_q%:E[g]); last first.
  rewrite !Lnorm1; under [in RHS]eq_integral.
    move=> x _; rewrite /F /G /normalized/=.
    rewrite ger0_norm; last by rewrite mulr_ge0 ?divr_ge0 ?fine_ge0 ?Lnormr_ge0.
    by rewrite mulrACA -normrM EFinM; over.
  rewrite ge0_integralZr//; last 2 first.
    - by do 2 apply: measurableT_comp => //; exact: measurable_funM.
    - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// Lnormr_ge0.
  rewrite -!muleA [X in _ * X](_ : _ = 1) ?mule1// EFinM muleACA.
  rewrite (_ : _ * 'N_p%:E[f] = 1) ?mul1e; last first.
    rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnormr_ge0.
    by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// fpos/= ltey.
  rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnormr_ge0.
  by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// gpos/= ltey.
rewrite -(mul1e ('N_p%:E[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnormr_ge0//.
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
rewrite (@convex_powR _ _ _ (Itv01 _ _))// ?inE/= ?in_itv/= ?normr_ge0 ?invr_ge0//.
by rewrite invf_le1 ?ler1n.
Qed.

Let measurableT_comp_powR f p :
  measurable_fun setT f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p (EFin \o f)).
Local Open Scope ereal_scope.

Let minkowski1 f g p : measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  'N_1[(f \+ g)%R] <= 'N_1[f] + 'N_1[g].
Proof.
move=> mf mg.
rewrite !Lnorm1 -ge0_integralD//=; [|by do 2 apply: measurableT_comp..].
rewrite ge0_le_integral//.
- by do 2 apply: measurableT_comp => //; exact: measurable_funD.
- by move=> x _; rewrite adde_ge0.
- by apply/measurableT_comp/measurable_funD; exact/measurableT_comp.
- by move=> x _; rewrite lee_fin ler_normD.
Qed.

Let minkowski_lty f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
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
rewrite unlock poweR_lty//.
pose x := \int[mu]_x (2 `^ (p - 1) * (`|f x| `^ p + `|g x| `^ p))%:E.
apply: (@le_lt_trans _ _ x).
  rewrite ge0_le_integral//=.
  - apply/measurable_EFinP/measurableT_comp_powR/measurableT_comp => //.
    exact: measurable_funD.
  - by apply/measurable_EFinP/measurable_funM/measurable_funD => //;
      exact/measurableT_comp_powR/measurableT_comp.
  - by move=> ? _; rewrite lee_fin.
rewrite {}/x; under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin ?powR_ge0//; last first.
  by apply/measurable_EFinP/measurable_funD => //;
    exact/measurableT_comp_powR/measurableT_comp.
rewrite lte_mul_pinfty ?lee_fin ?powR_ge0//.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 2 first.
  - exact/measurable_EFinP/measurableT_comp_powR/measurableT_comp.
  - exact/measurable_EFinP/measurableT_comp_powR/measurableT_comp.
by rewrite lte_add_pinfty// -powR_Lnorm ?(gt_eqF (lt_trans _ p1))// poweR_lty.
Qed.

Lemma minkowski_EFin f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[(f \+ g)%R] <= 'N_p%:E[f] + 'N_p%:E[g].
Proof.
move=> mf mg; rewrite le_eqVlt => /predU1P[<-|p1]; first exact: minkowski1.
have [->|Nfoo] := eqVneq 'N_p%:E[f] +oo.
  by rewrite addye ?leey// -ltNye (lt_le_trans _ (Lnormr_ge0 _ _ _)).
have [->|Ngoo] := eqVneq 'N_p%:E[g] +oo.
  by rewrite addey ?leey// -ltNye (lt_le_trans _ (Lnormr_ge0 _ _ _)).
have Nfgoo : 'N_p%:E[(f \+ g)%R] < +oo.
  by rewrite minkowski_lty// ?ltW// ltey; [exact: Nfoo|exact: Ngoo].
suff : 'N_p%:E[(f \+ g)%R] `^ p <= ('N_p%:E[f] + 'N_p%:E[g]) *
    'N_p%:E[(f \+ g)%R] `^ p * (fine 'N_p%:E[(f \+ g)%R])^-1%:E.
  have [-> _|Nfg0] := eqVneq 'N_p%:E[(f \+ g)%R] 0.
    by rewrite adde_ge0 ?Lnormr_ge0.
  rewrite lee_pdivlMr ?fine_gt0// ?lt0e ?Nfg0 ?Lnormr_ge0//.
  rewrite -{1}(@fineK _ ('N_p%:E[(f \+ g)%R] `^ p)); last first.
    by rewrite fin_num_poweR// ge0_fin_numE// Lnormr_ge0.
  rewrite -(invrK (fine _)) lee_pdivrMl; last first.
    rewrite invr_gt0 fine_gt0// (poweR_lty _ Nfgoo) andbT poweR_gt0//.
    by rewrite lt0e Nfg0 Lnormr_ge0.
  rewrite fineK ?ge0_fin_numE ?Lnormr_ge0// => /le_trans; apply.
  rewrite lee_pdivrMl; last first.
    by rewrite fine_gt0// poweR_lty// andbT poweR_gt0// lt0e Nfg0 Lnormr_ge0.
  by rewrite fineK// 1?muleC// fin_num_poweR// ge0_fin_numE ?Lnormr_ge0.
have p0 : (0 < p)%R by exact: (lt_trans _ p1).
rewrite powR_Lnorm ?gt_eqF//.
under eq_integral => x _ do rewrite -mulr_powRB1//.
apply: (@le_trans _ _
    (\int[mu]_x ((`|f x| + `|g x|) * `|f x + g x| `^ (p - 1))%:E)).
  rewrite ge0_le_integral//.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact/measurableT_comp/measurable_funD.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - apply/measurableT_comp => //; apply: measurable_funM.
      by apply/measurable_funD => //; exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - by move=> ? _; rewrite lee_fin ler_wpM2r// ?powR_ge0// ler_normD.
under eq_integral=> ? _ do rewrite mulrDl EFinD.
rewrite ge0_integralD//; last 2 first.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
rewrite [leRHS](_ : _ = ('N_p%:E[f] + 'N_p%:E[g]) *
    (\int[mu]_x (`|f x + g x| `^ p)%:E) `^ `1-(p^-1)).
  rewrite muleDl; last 2 first.
    - rewrite fin_num_poweR// -powR_Lnorm ?gt_eqF// fin_num_poweR//.
      by rewrite ge0_fin_numE ?Lnormr_ge0.
    - by rewrite ge0_adde_def// inE Lnormr_ge0.
  apply: leeD.
  - pose h := (@powR R ^~ (p - 1) \o normr \o (f \+ g))%R; pose i := (f \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]%R); last first.
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM (ger0_norm (powR_ge0 _ _)).
    rewrite [X in _ * X](_ : _ = 'N_(p / (p - 1))%:E[h]); last first.
      rewrite unlock.
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
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM norm_powR// normr_id.
    rewrite [X in _ * X](_ : _ = 'N_((1 - p^-1)^-1)%:E[h])//; last first.
      rewrite unlock.
      apply: congr2; last by rewrite invrK.
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
- by rewrite unlock fine_poweR.
- by rewrite -powR_Lnorm ?gt_eqF// fin_num_poweR// ge0_fin_numE ?Lnormr_ge0.
Qed.

Lemma lerB_DLnorm f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] <= 'N_p%:E[f \+ g] + 'N_p%:E[g].
Proof.
move=> mf mg p1.
rewrite (_ : f = ((f \+ g) \+ (-%R \o g))%R); last first.
  by apply: funext => x /=; rewrite -addrA subrr addr0.
rewrite [X in _ <= 'N__[X] + _](_ : _ = (f \+ g)%R); last first.
  by apply: funext => x /=; rewrite -addrA [X in _ + _ + X]addrC subrr addr0.
rewrite (_ : 'N__[g] = 'N_p%:E[-%R \o g]); last by rewrite oppr_Lnorm.
by apply: minkowski_EFin => //;
  [exact: measurable_funD|exact: measurableT_comp].
Qed.

Lemma lerB_LnormD f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] - 'N_p%:E[g] <= 'N_p%:E[f \+ g].
Proof.
move=> mf mg p1.
set rhs := (leRHS); have [?|] := boolP (rhs \is a fin_num).
  by rewrite lee_subel_addr//; exact: lerB_DLnorm.
rewrite fin_numEn => /orP[|/eqP ->]; last by rewrite leey.
by rewrite gt_eqF// (lt_le_trans _ (Lnormr_ge0 _ _ _)).
Qed.

(* TODO: rename to minkowski after version 1.12.0 *)
Lemma eminkowski f g (p : \bar R) :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> 1 <= p ->
  'N_p[(f \+ g)%R] <= 'N_p[f] + 'N_p[g].
Proof.
case: p => //[r|]; first exact: minkowski_EFin.
move=> mf mg _; rewrite unlock /Lnorm.
case: ifPn => mugt0; last by rewrite adde0 lexx.
exact: ess_sup_normD.
Qed.

End minkowski.
#[deprecated(since="mathcomp-analysis 1.10.0",
  note="use `minkowski_EFin` or `eminkowski` instead")]
Notation minkowski := minkowski_EFin (only parsing).

Definition finite_norm d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) :=
  ('N[ mu ]_p [ EFin \o f ] < +oo)%E.

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) (f : T -> R)
  of @MeasurableFun d _ T R f := {
  lfuny : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of @MeasurableFun d _ T R f & isLfun d T R mu p p1 f}.

Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) => solve [apply: lfuny] : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

HB.instance Definition _ := gen_eqMixin (LfunType mu p1).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p1).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Definition Lequiv (f g : LfunType mu p1) := `[< f = g %[ae mu] >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP/ae_eq_sym.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_eq_trans gf fh).
Qed.

Canonical Lequiv_canonical :=
  EquivRel Lequiv Lequiv_refl Lequiv_sym Lequiv_trans.

Local Open Scope quotient_scope.

Definition LspaceType := {eq_quot Lequiv}.
Canonical LspaceType_quotType := [the quotType _ of LspaceType].
Canonical LspaceType_eqType := [the eqType of LspaceType].
Canonical LspaceType_choiceType := [the choiceType of LspaceType].
Canonical LspaceType_eqQuotType := [the eqQuotType Lequiv of LspaceType].

Lemma LequivP (f g : LfunType mu p1) :
  reflect (f = g %[ae mu]) (f == g %[mod LspaceType]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

Record LType := MemLType { Lfun_class : LspaceType }.
Coercion LfunType_of_LType (f : LType) : LfunType mu p1 :=
  repr (Lfun_class f).

End Lequiv.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p (p1 : (1 <= p)%E) := [set: LType mu p1].
Arguments Lspace : clear implicits.

Lemma LType1_integrable (f : LType mu (@lexx _ _ 1%E)) :
  mu.-integrable setT (EFin \o f).
Proof.
apply/integrableP; split; first exact/measurable_EFinP.
have := lfuny _ f.
rewrite /finite_norm unlock /Lnorm invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1.
by under eq_integral => i _ do rewrite poweRe1//.
Qed.

Let le12 : (1 <= 2%:E :> \bar R)%E.
Proof.
rewrite lee_fin.
rewrite (ler_nat _ 1 2).
by [].
Qed.

Lemma LType2_integrable_sqr (f : LType mu le12) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  apply/measurable_EFinP.
  exact/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
rewrite (@lty_poweRy _ _ 2^-1)//.
rewrite (le_lt_trans _ (lfuny _ f))//.
rewrite unlock.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= leey integral_ge0.
- by rewrite in_itv/= leey integral_ge0.
- rewrite ge0_le_integral//.
  + apply: measurableT_comp => //; apply/measurable_EFinP.
    exact/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
  + by move=> x _; rewrite lee_fin powR_ge0.
  + apply/measurable_EFinP.
    apply/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R) => //.
    exact/measurableT_comp.
  + by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finlfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition lfun : {pred _ -> _} := [predI @mfun _ _ T R & finlfun].
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
Lemma sub_lfun_mfun : {subset lfun <= mfun}.
Proof. by move=> x /andP[]. Qed.
Lemma sub_lfun_finlfun : {subset lfun <= finlfun}.
Proof. by move=> x /andP[]. Qed.

End lfun_pred.

Section lfun.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Notation lfun := (@lfun _ T R mu p).
Section Sub.
Context (f : T -> R) (fP : f \in lfun).
Definition lfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ T R f (set_mem (sub_lfun_mfun fP)).
#[local] HB.instance Definition _ := lfun_Sub1_subproof.
Definition lfun_Sub2_subproof :=
  @isLfun.Build d T R mu p p1 f (set_mem (sub_lfun_finlfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := lfun_Sub2_subproof.
Definition lfun_Sub : LfunType mu p1 := f.
End Sub.

Lemma lfun_rect (K : LfunType mu p1 -> Type) :
  (forall f (Pf : f \in lfun), K (lfun_Sub Pf)) -> forall u, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]].
have Pf : f \in lfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_lfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_lfun_finlfun Pf) by [].
exact: Ksub.
Qed.

Lemma lfun_valP f (Pf : f \in lfun) : lfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ :=
  isSub.Build _ _ (LfunType mu p1) lfun_rect lfun_valP.

Lemma lfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Import numFieldNormedType.Exports.

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0// ltry. Qed.

HB.instance Definition _ := @isLfun.Build d T R mu p p1 (cst 0) lfuny0.

Lemma mfunP (f : {mfun T >-> R}) : (f : T -> R) \in mfun.
Proof. exact: valP. Qed.

Lemma lfunP (f : LfunType mu p1) : (f : T -> R) \in lfun.
Proof. exact: valP. Qed.

Lemma mfun_scaler_closed : scaler_closed (@mfun _ _ T R).
Proof. move=> a/= f; rewrite !inE; exact: measurable_funM. Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ (@mfun _ _ T R)
  mfun_scaler_closed.
HB.instance Definition _ := [SubZmodule_isSubLmodule of {mfun T >-> R} by <:].

Lemma LnormZ (f : LfunType mu p1) a :
  ('N[mu]_p[EFin \o (a \*: f)] = `|a|%:E * 'N[mu]_p[EFin \o f])%E.
Proof.
rewrite unlock /Lnorm.
case: p p1 f => //[r r1 f|? f].
- under eq_integral do rewrite /= -mulr_algl scaler1 normrM powRM ?EFinM//.
  rewrite integralZl//; last first.
    apply/integrableP; split.
      apply: measurableT_comp => //.
      apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
      exact: measurableT_comp.
    apply: (@lty_poweRy _ _ r^-1).
      by rewrite gt_eqF// invr_gt0 ?(lt_le_trans ltr01).
    rewrite [ltLHS](_ : _ = 'N[mu]_r%:E[EFin \o f]%E); first exact: (lfuny r1 f).
    rewrite unlock /Lnorm.
    by under eq_integral do rewrite gee0_abs ?lee_fin ?powR_ge0//.
  rewrite poweRM ?integral_ge0//.
  by rewrite poweR_EFin -powRrM mulfV ?gt_eqF ?(lt_le_trans ltr01)// powRr1.
- case: ifPn => mu0; last by rewrite mule0.
  rewrite -ess_supZl//; apply/eq_ess_sup/nearW => t /=.
  by rewrite normrZ EFinM.
Qed.

Lemma lfun_submod_closed : submod_closed lfun.
Proof.
split.
  by rewrite -[0]/(cst 0); exact: lfunP.
move=> a/= f g fP gP.
rewrite -[f]lfun_valP -[g]lfun_valP.
move: (lfun_Sub _) (lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=; apply: (le_lt_trans (eminkowski _ _ _ _)) => //.
- suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
- rewrite lte_add_pinfty//; last exact: lfuny.
  by rewrite LnormZ lte_mul_pinfty// ?lee_fin//; exact: lfuny.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ lfun
  lfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End lfun.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (p : \bar R) (p1 : (1 <= p)%E).

(* TODO: 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Let nm f := fine ('N[mu]_p[EFin \o f]).

Lemma finite_norm_fine (f : ty) : (nm f)%:E = 'N[mu]_p[EFin \o f]%E.
Proof.
rewrite /nm fineK// fin_numElt (lt_le_trans ltNy0) ?Lnormr_ge0//=.
exact: lfuny.
Qed.

Lemma ler_LnormD (f g : ty) : nm (f + g) <= nm f + nm g.
Proof. by rewrite -lee_fin EFinD !finite_norm_fine eminkowski. Qed.

Lemma LnormrN (f : ty) : nm (\-f) = nm f.
Proof. by rewrite /nm oppr_Lnorm. Qed.

Lemma Lnormr_natmul (f : ty) k : nm (f *+ k) = nm f *+ k.
Proof.
apply/EFin_inj; rewrite finite_norm_fine -scaler_nat LnormZ normr_nat.
by rewrite -[in RHS]mulr_natl EFinM finite_norm_fine.
Qed.

(* TODO : fix the definition *)
(* waiting for MathComp 2.4.0
HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (LfunType mu p1)
     nm ler_Lnorm_add Lnorm_natmul LnormN.
*)

(* TODO: add equivalent of mx_normZ and HB instance *)

Lemma fine_Lnormr_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
move=> /eqP; rewrite -eqe => /eqP.
rewrite finite_norm_fine => /Lnormr_eq0_eq0.
by apply; rewrite ?(lt_le_trans _ p1).
Qed.

End Lspace_norm.

Section Lspace_inclusion.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma Lspace_inclusion (p q : \bar R) :
  forall (p1 : 1 <= p) (q1 : 1 <= q),
    mu [set: T] < +oo -> p < q ->
    forall f : {mfun T >-> R}, finite_norm mu q f -> finite_norm mu p f.
Proof.
have := measure_ge0 mu [set: T].
rewrite le_eqVlt => /predU1P[mu0 p1 q1 _ _ f _|mu_pos].
  rewrite /finite_norm unlock /Lnorm.
  move: p p1; case=> //; last by rewrite -mu0 ltxx ltry.
  move=> r r1.
  under eq_integral do rewrite /= -[(_ `^ _)%R]ger0_norm ?powR_ge0//=.
  rewrite (@integral_abs_eq0 _ _ _ _ setT setT (fun x => (`|f x| `^ r)%:E))//.
    by rewrite poweR0r// invr_neq0// gt_eqF// -lte_fin (lt_le_trans _ r1).
  apply/measurable_EFinP.
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
  exact: measurableT_comp.
move: p q.
case=> //[p|]; case=> //[q|] p1 q1; last first.
  have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
  move=> muoo _ f.
  rewrite /finite_norm unlock /Lnorm mu_pos => supf_lty.
  rewrite poweR_lty//; move: supf_lty => /ess_supr_bounded[M fM].
  rewrite (@le_lt_trans _ _ (\int[mu]_x (M `^ p)%:E)); [by []| |]; last first.
    by rewrite integral_cst// lte_mul_pinfty// lee_fin powR_ge0.
  apply: ae_ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin powR_ge0.
    apply/measurable_EFinP.
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  - by move=> x _; rewrite lee_fin powR_ge0.
    apply: filterS fM => t/= ftM _.
    rewrite lee_fin ge0_ler_powR//; first exact: ltW.
    by rewrite nnegrE (le_trans _ ftM).
move=> mu_fin pleq f ffin.
have:= ffin; rewrite /finite_norm.
have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
have pN0 : p != 0%R by rewrite gt_eqF.
have q0 : (0 < q)%R by rewrite ?(lt_le_trans ltr01).
have qinv0 : q^-1 != 0%R by rewrite invr_neq0// gt_eqF.
pose r := q/p.
pose r' := (1 - r^-1)^-1.
have := (@hoelder _ _ _ mu (fun x => `|f x| `^ p) (cst 1)%R r r')%R.
rewrite (_ : (_ \* cst 1)%R = (fun x : T => `|f x| `^ p))%R -?fctM ?mulr1//.
rewrite Lnorm_cst1 unlock /Lnorm invr1.
have mfp : measurable_fun [set: T] (fun x : T => (`|f x| `^ p)%R).
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
  exact: measurableT_comp.
have m1 : measurable_fun [set: T] (@cst _ R 1%R).
  exact: measurable_cst.
have r0 : (0 < r)%R by rewrite/r divr_gt0.
have r'0 : (0 < r')%R.
  by rewrite /r' invr_gt0 subr_gt0 invf_lt1 ?(lt_trans ltr01)//;
    rewrite /r ltr_pdivlMr// mul1r.
have rr'1 : r^-1 + r'^-1 = 1%R.
  by rewrite /r' /r invf_div invrK addrCA subrr addr0.
move=> /(_ mfp m1 r0 r'0 rr'1).
under [in leLHS] eq_integral do rewrite /= powRr1// norm_powR// normrE.
under [in leRHS] eq_integral do
  rewrite /= norm_powR// normr_id -powRrM mulrCA divff// mulr1.
rewrite [X in X <= _]poweRe1; last
  by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
move=> h1 /lty_poweRy h2.
apply: poweR_lty.
apply: (le_lt_trans h1).
rewrite muleC lte_mul_pinfty ?fin_numElt?poweR_ge0//.
  by rewrite (lt_le_trans _ (poweR_ge0 _ _)) ?ltNyr// ?poweR_lty.
rewrite poweR_lty// (lty_poweRy qinv0)//.
by have:= ffin; rewrite /finite_norm unlock /Lnorm.
Qed.

End Lspace_inclusion.
