(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
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
(*          'N[mu]_p[f] == the Lp-norm of f with measure mu                   *)
(*  hoelder_conjugate p == an extended real number q s.t. p^-1 + q^-1 = 1     *)
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
(*                          The HB class is Lfunction.                        *)
(*            f \in Lfun == holds for f : LfunType mu p1                      *)
(*          ae_eq_op f g == boolean version of ae_eq,                         *)
(*                          ae_eq_op is canonically an equivalence relation   *)
(*  {mfun_mu, T1 >-> T2} == the quotient of measurable functions T1 -> T2,    *)
(*                          quotiented by the equivalence relation ae_eq_op   *)
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
  (format "'[' ''N[' mu ]_ p '/  ' [ F ] ']'").
(* for use as a local notation when the measure is in context: *)
Reserved Notation "'N_ p [ F ]" (format "'[' ''N_' p '/  ' [ F ] ']'").
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

(* TODO: true to remove conditions when we enable
(mu (f @^-1` (setT `\ 0%R))) when p = 0
*)
Lemma Lnorm0 p : p != 0 -> 'N_p[cst 0] = 0.
Proof.
rewrite unlock /Lnorm; case: p => [r|_|_].
- rewrite eqe => r0.
  under eq_integral => x _ do rewrite /= normr0 powR0//.
  by rewrite integral0 poweR0r// invr_neq0.
- case: ifPn => // mu0; apply: ess_sup_ae_cst => //.
  by apply/nearW => x/=; rewrite normr0.
- case: ifPn => // mu0; apply: ess_inf_ae_cst => //.
  by apply/nearW => x/=; rewrite normr0.
Qed.

Lemma Lnorm1 f : 'N_1[f] = \int[mu]_x `|f x|.
Proof.
rewrite unlock invr1 ?poweRe1//; under eq_integral do [rewrite poweRe1//] => //.
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

Lemma oppe_Lnorm f p : 'N_p[\- f] = 'N_p[f].
Proof.
have NfE : abse \o (\- f) = abse \o f by apply/funext => x /=; rewrite abseN.
rewrite unlock /Lnorm NfE; case: p => /= [r|//|//].
by under eq_integral => x _ do rewrite abseN.
Qed.

Lemma Lnorm_cst1 r : 'N_r%:E[cst 1] = mu [set: T] `^ (r^-1).
Proof.
rewrite unlock /Lnorm; under eq_integral do rewrite /= normr1 powR1.
by rewrite integral_cst// mul1e.
Qed.

Lemma Lnorm_ge0 p f : 0 <= 'N_p[f].
Proof.
rewrite unlock; move: p => [r/=|/=|//]; first exact: poweR_ge0.
- by case: ifPn => // /ess_sup_gee; apply; apply/nearW => r/=.
- by case: ifPn => // muT0; apply/ess_infP/nearW => x /=.
Qed.

Lemma Lnorm_eq0_eq0 f p : measurable_fun [set: T] f -> 0 < p ->
  'N_p[f] = 0 -> f = \0 %[ae mu].
Proof.
rewrite unlock /Lnorm => mf; case: p => [r||//].
- rewrite lte_fin => r0 /poweR_eq0_eq0 => /(_ (integral_ge0 _ _)) h.
  have : \int[mu]_x `| `|f x| `^ r | = 0%R.
    under eq_integral.
      move=> x _; rewrite gee0_abs; last by rewrite poweR_ge0. over.
    by apply: h => x _; rewrite poweR_ge0.
  have mp : measurable_fun [set: T] (fun x => `|f x| `^ r).
    apply: (@measurableT_comp _ _ _ _ _ _ (fun x => x `^ r)) => //=.
      exact: (measurableT_comp (measurable_poweR _)).
    exact: measurableT_comp.
  move/(ae_eq_integral_abs mu measurableT mp).
  apply: filterS => x/= /[apply].
  by move=> /poweR_eq0_eq0 /eqP => /(_ (abse_ge0 _)); rewrite abse_eq0 => /eqP.
- case: ifPn => [mu0 _|].
    move=> /abs_sup_eq0_ae_eq/=.
    by apply: filterS => x/= /(_ I) /eqP + _ => /eqP.
  rewrite ltNge => /negbNE mu0 _ _.
  suffices mueq0: mu setT = 0 by exact: ae_eq0.
  by apply/eqP; rewrite eq_le mu0/=.
Qed.

Lemma powR_Lnorm f r : r != 0%R -> 'N_r%:E[f] `^ r = \int[mu]_x `| f x | `^ r.
Proof. by move=> r0; rewrite poweR_Lnorm. Qed.

Lemma Lnorm_abse f p : 'N_p[abse \o f] = 'N_p[f].
Proof.
rewrite unlock/=; have -> : abse \o (abse \o f) = abse \o f.
  by apply: funext => x/=; rewrite abse_id.
by case: p => [r|//|//]; under eq_integral => x _ do rewrite abse_id.
Qed.

End Lnorm_properties.
Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f) : ereal_scope.
#[global] Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnorm_ge0] : core.

Section lnorm.
Context d {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.
(** lp-norm is just Lp-norm applied to counting *)
Local Notation "'N_ p [ f ]" := (Lnorm counting p f).

Lemma Lnorm_counting p (f : (\bar R)^nat) : (0 < p)%R ->
  'N_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p)) `^ p^-1.
Proof.
by move=> p0; rewrite unlock ge0_integral_count// => k; rewrite poweR_ge0.
Qed.

End lnorm.

Section hoelder_conjugate.
Context {d} {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types p q : \bar R.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition hoelder_conjugate p : \bar R :=
  if p == +oo then 1 else
  if p == -oo then 0 else
  if p == 0 then -oo else
  p / (p - 1).

Local Notation "p ^*" := (hoelder_conjugate p) : ereal_scope.

Lemma hoelder_conjugate0 : 0^* = -oo.
Proof. by rewrite /hoelder_conjugate/= eqxx. Qed.

Lemma hoelder_conjugate1 : 1^* = +oo.
Proof. by rewrite /hoelder_conjugate/= onee_eq0 EFinN subee// inve0 mul1e. Qed.

Lemma hoelder_conjugate2 : 2%:E^* = 2%:E.
Proof.
rewrite /hoelder_conjugate/= eqe/= pnatr_eq0/=.
by rewrite {2}(natrD _ 1 1) {2}EFinD EFinN addeK// inve1 mule1.
Qed.

Lemma hoelder_conjugatey : +oo^* = 1.
Proof. by []. Qed.

Lemma hoelder_conjugateNy : -oo^* = 0.
Proof. by []. Qed.

Lemma hoelder_conjugate_eqy p : p^* = +oo -> p = 1.
Proof.
move: p => [p| |].
- rewrite /hoelder_conjugate/=; case: ifPn => [/eqP p0//|p0].
  rewrite -EFinD inver subr_eq0 -eqe.
  by case: ifPn => // /eqP ->.
- by rewrite hoelder_conjugatey.
- by rewrite hoelder_conjugateNy.
Qed.

Lemma hoelder_conjugate_eqNy p : p^* = -oo -> p = 0.
Proof.
move: p => [p| |].
- rewrite /hoelder_conjugate/=; case: ifPn => [/eqP p0//|p0].
  rewrite -EFinD inver subr_eq0 -eqe.
  by case: ifPn => //; rewrite eqe => /eqP ->; rewrite mul1e.
- by rewrite hoelder_conjugatey.
- by rewrite hoelder_conjugateNy.
Qed.

Lemma hoelder_conjugate_eq1 p : p > -oo -> p != 0 ->
  p^-1 + (p^*)^-1 = 1.
Proof.
move=> pNy p0; rewrite /hoelder_conjugate/=.
case: ifPn => [/eqP py|py]; first by rewrite py invey inve1 add0e.
rewrite gt_eqF// (negbTE p0).
move: p p0 py pNy => [p| |]//.
rewrite eqe => p0 _ _.
rewrite inver (negbTE p0) inver subr_eq0.
case: ifPn => [/eqP ->|p1]; first by rewrite invr1 mul1e invey adde0.
rewrite inveM; last first.
  rewrite inveM_defE eqe (negbTE p0)/= andbT eqe.
  rewrite invr_eq0 subr_eq0; apply/implyP => /eqP ->.
  by rewrite lee01/= ltry.
rewrite inver (negbTE p0) inver invr_eq0 subr_eq0 (negbTE p1) invrK.
rewrite EFinB muleBr// mule1 -EFinM mulVf// -EFinD.
by rewrite (addrC p^-1%R) (subrK p^-1%R).
Qed.

Lemma hoelder_conj_ge1 p : 1 <= p -> 1 <= p^*.
Proof.
move: p => [r|//|//]; rewrite le_eqVlt => /predU1P[<-|r1].
  by rewrite hoelder_conjugate1 leey.
rewrite /hoelder_conjugate/= gt_eqF ?(lt_trans lte01)// inver subr_eq0 gt_eqF//.
by rewrite -EFinM lee_fin ler_pdivlMr ?subr_gt0// mul1r lerBlDl lerDr.
Qed.

Lemma hoelder_conjugateP p q : p > -oo -> p != 0 ->
  p^-1 + q^-1 = 1 <-> q = p^*.
Proof.
move=> pNy p0.
have [->|py] := eqVneq p +oo.
  rewrite hoelder_conjugatey invey add0e; split => /eqP.
    by rewrite inve_eq1 => /eqP.
  by rewrite -inve_eq1 => /eqP.
have pfin : p \is a fin_num by rewrite fin_numE py andbT -ltNye.
have [->|qNy] := eqVneq q -oo.
  rewrite inveNy addeNy; split => // /esym /hoelder_conjugate_eqNy /eqP.
  by rewrite (negbTE p0).
split => [pq1|pq]; last by rewrite pq hoelder_conjugate_eq1.
rewrite /hoelder_conjugate (negbTE py)//.
rewrite ifF//; last first.
  by apply/negbTE; move: pfin; rewrite fin_numE => /andP[].
by rewrite (negbTE p0); exact: Nyconjugate.
Qed.

Lemma hoelder_conjugateK : involutive hoelder_conjugate.
Proof.
move=> [x| |]; last 2 first.
  by rewrite hoelder_conjugatey hoelder_conjugate1.
  by rewrite hoelder_conjugateNy hoelder_conjugate0.
rewrite /hoelder_conjugate/= !eqe.
have [->//=|x0/=] := eqVneq x 0%R.
rewrite -EFinD inver subr_eq0 -eqe.
have [->/=|x1/=] := eqVneq x 1%R; first by rewrite mul1e eqxx.
rewrite -EFinM eqe mulf_eq0 (negbTE x0)/= invr_eq0 subr_eq0 (negbTE x1).
rewrite -EFinD -[X in (_ / _ - X)%R](@divff _ (x - 1)) ?subr_eq0//.
rewrite -mulrBl opprB (addrC x (1 - _)%R) subrK div1r.
by rewrite EFinM -muleA divee ?mule1// eqe invr_eq0 subr_eq0.
Qed.

Lemma hoelder_Mconjugate p : p > -oo -> p != 0 -> p * p^* = p + p^*.
Proof.
move=> pNy p0.
rewrite /hoelder_conjugate.
case: ifPn => [/eqP ->|py]; first by rewrite mule1.
rewrite gt_eqF// (negbTE p0).
have [->|p1] := eqVneq p 1; first by rewrite subee// inve0 !mul1e.
rewrite -[X in _ = X + _]mule1.
have pfin : p \is a fin_num by rewrite fin_numE -ltNye pNy.
rewrite -[X in _ * X + _](@divee _ (p - 1)); last first.
  by rewrite sube_eq ?add0e.
  by rewrite fin_numB// pfin.
rewrite [in RHS]muleA -muleDl; last 2 first.
  rewrite fin_numV//; first by rewrite sube_eq// add0e.
  by rewrite sube_eq// -ltNye.
  by rewrite fin_num_adde_defl.
by rewrite muleA muleBr ?fin_num_adde_defl// mule1 subeK.
Qed.

Lemma hoelder_div_conjugate p : p > -oo -> p != 0 -> p / p^* = p - 1.
Proof.
move=> pNy p0.
rewrite /hoelder_conjugate; case: ifPn => [/eqP->|py].
  by rewrite inve1 mule1.
rewrite gt_eqF// (negbTE p0).
have ? : p \is a fin_num by rewrite fin_numE py andbT -ltNye.
have [->|p1] := eqVneq p 1; first by rewrite subee// inve0 !mul1e invey.
rewrite inveM.
  by rewrite inveK muleA divee// ?mul1e// gt_eqF// (lt_trans _ p1).
apply: fin_inveM_def => //; first by rewrite inve_eq0 sube_eq.
rewrite fin_numV//; first by rewrite sube_eq// add0e.
by rewrite sube_eq// -ltNye.
Qed.

Lemma hoelder_conjugate_div p : p > -oo -> p != 0 -> p^* / p = p^* - 1.
Proof.
move=> pNy p0.
rewrite /hoelder_conjugate; case: ifPn => [/eqP->|py].
  by rewrite invey mule0 subee.
rewrite gt_eqF// (negbTE p0).
have ? : p \is a fin_num by rewrite fin_numE py andbT -ltNye.
rewrite muleAC divee//.
have [->|p1] := eqVneq p 1; first by rewrite subee// inve0 mul1e.
rewrite -[X in _ = _ - X](@divee _ (p - 1)); last first.
  by rewrite sube_eq// add0e.
  by rewrite fin_numB//; apply/andP.
rewrite -muleBl//; last 2 first.
  rewrite fin_numV//; first by rewrite sube_eq// add0e.
  by rewrite sube_eq// -ltNye.
  by rewrite fin_num_adde_defr.
by rewrite oppeB ?fin_num_adde_defl// addeA subee// add0e.
Qed.

End hoelder_conjugate.

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
- move/measurable_EFinP in mf.
  apply: filterS (Lnorm_eq0_eq0 mf p0 f0) => x /(_ I) + _.
  by rewrite /= normrM EFinM -abse_EFin => ->; rewrite abse0 mul0e.
Qed.

Let normalized p f x := (`|f x| / fine 'N_p%:E[f])%R.

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
have [f0|f0] := eqVneq 'N_p%:E[f] 0; first exact: hoelder0.
have [g0|g0] := eqVneq 'N_q%:E[g] 0.
  rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
  by under eq_Lnorm do rewrite /= mulrC.
have {f0}fpos : 0 < 'N_p%:E[f] by rewrite lt0e f0 Lnorm_ge0.
have {g0}gpos : 0 < 'N_q%:E[g] by rewrite lt0e g0 Lnorm_ge0.
have [foo|foo] := eqVneq 'N_p%:E[f] +oo; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q%:E[g] +oo; first by rewrite goo gt0_muley ?leey.
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
    by rewrite -EFinM mulVf ?gt_eqF// fine_gt0// fpos/= ltey.
  rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
  by rewrite -EFinM mulVf ?gt_eqF// fine_gt0// gpos/= ltey.
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
rewrite !convRE; set w1 := t%:num; set w2 := `1-(t%:inum).
have [->|w20] := eqVneq w2 0.
  rewrite !mul0r !addr0; have [->|w10] := eqVneq w1 0.
    by rewrite !mul0r powR0// gt_eqF.
  by rewrite ge1r_powRZ// /w1 lt_neqAle eq_sym w10/=; apply/andP.
have [->|w10] := eqVneq w1 0.
  by rewrite !mul0r !add0r ge1r_powRZ// onem_le1// andbT lt0r w20 onem_ge0.
have [->|p_neq1] := eqVneq p 1.
  by rewrite !powRr1// addr_ge0// mulr_ge0// /w1 ?onem_ge0.
have {p_neq1} {}p1 : 1 < p by rewrite lt_neqAle eq_sym p_neq1.
pose q := p / (p - 1).
have q1 : 1 <= q by rewrite /q ler_pdivlMr// ?mul1r ?gerBl// subr_gt0.
have q0 : 0 < q by rewrite (lt_le_trans _ q1).
have pq1 : p^-1 + q^-1 = 1.
  by rewrite /q invf_div -{1}(div1r p) -mulrDl subrKC mulfV// gt_eqF.
rewrite -(@powRr1 _ (w1 * x `^ p + w2 * y `^ p)); last first.
  by rewrite addr_ge0// mulr_ge0// ?powR_ge0// /w1 ?onem_ge0// itv_ge0.
have -> : 1 = p^-1 * p by rewrite mulVf ?gt_eqF.
rewrite powRrM (ge0_ler_powR (le_trans _ (ltW p1)))//.
- by rewrite nnegrE addr_ge0// mulr_ge0 /w1 ?onem_ge0.
- by rewrite nnegrE powR_ge0.
have -> : w1 * x + w2 * y = w1 `^ (p^-1) * w1 `^ (q^-1) * x +
                            w2 `^ (p^-1) * w2 `^ (q^-1) * y.
  rewrite -!powRD pq1; [|exact/implyP..].
  by rewrite !powRr1// /w1 ?onem_ge0.
apply: (@le_trans _ _ ((w1 * x `^ p + w2 * y `^ p) `^ (p^-1) *
                       (w1 + w2) `^ q^-1)).
  pose a1 := w1 `^ p^-1 * x. pose a2 := w2 `^ p^-1 * y.
  pose b1 := w1 `^ q^-1. pose b2 := w2 `^ q^-1.
  have : a1 * b1 + a2 * b2 <= (a1 `^ p + a2 `^ p) `^ p^-1 *
                              (b1 `^ q + b2 `^ q) `^ q^-1.
    by apply: hoelder2 => //; rewrite ?mulr_ge0 ?powR_ge0.
  rewrite ?powRM ?powR_ge0 -?powRrM ?mulVf ?powRr1 ?gt_eqF ?onem_ge0/w1//.
  by rewrite mulrAC (mulrAC _ y) => /le_trans; exact.
by rewrite {2}/w1 {2}/w2 subrKC powR1 mulr1.
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
rewrite {2 4}(_ : 2^-1 = 1 - 2^-1); last by rewrite {2}(splitr 1) div1r addrK.
by apply: (convex_powR p1 (Itv01 _ _)) => //=;
  rewrite ?inE/= ?in_itv/= ?normr_ge0// ?invr_ge0// invf_le1 ?ler1n.
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
by rewrite lte_add_pinfty//;
  under eq_integral do rewrite -poweR_EFin -abse_EFin;
  rewrite -powR_Lnorm// poweR_lty.
Qed.

Lemma minkowski_EFin f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
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
under eq_integral.
  move=> x _.
  rewrite abse_EFin poweR_EFin -mulr_powRB1//.
  over.
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
    - rewrite fin_num_poweR//.
      under eq_integral do rewrite -poweR_EFin -abse_EFin.
      rewrite -powR_Lnorm ?gt_eqF// fin_num_poweR//.
      by rewrite ge0_fin_numE ?Lnorm_ge0.
    - by rewrite ge0_adde_def// inE Lnorm_ge0.
  apply: leeD.
  - pose h := (@powR R ^~ (p - 1) \o normr \o (f \+ g))%R; pose i := (f \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]%R); last first.
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM (ger0_norm (powR_ge0 _ _)).
    rewrite [X in _ * X](_ : _ = 'N_(p / (p - 1))%:E[h]); last first.
      rewrite unlock.
      rewrite onemV ?gt_eqF// invf_div; apply: congr2; last by [].
      apply: eq_integral => x _; congr EFin.
      by rewrite norm_powR// normr_id -powRrM mulrC divfK// subr_eq0 gt_eqF.
    apply: (@hoelder _ _ _ _ _ _ p (p / (p - 1))) => //.
    + exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
    + by rewrite divr_gt0// subr_gt0.
    + by rewrite invf_div -onemV ?gt_eqF// subrKC.
  - pose h := (fun x => `|f x + g x| `^ (p - 1))%R; pose i := (g \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]); last first.
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM norm_powR// normr_id.
    rewrite [X in _ * X](_ : _ = 'N_((1 - p^-1)^-1)%:E[h])//; last first.
      rewrite unlock.
      apply: congr2; last by rewrite invrK.
      apply: eq_integral => x _; congr EFin.
      rewrite -/(onem p^-1) onemV ?gt_eqF// norm_powR// normr_id -powRrM.
      by rewrite divKf// ?subr_eq0 ?gt_eqF.
    apply: (le_trans (@hoelder _ _ _ _ _ _ p (1 - p^-1)^-1 _ _ _ _ _)) => //.
    + exact/measurableT_comp_powR/measurableT_comp/measurable_funD.
    + by rewrite invr_gt0 onem_gt0// invf_lt1.
    + by rewrite invrK subrKC.
rewrite -muleA; congr (_ * _).
under [X in X * _]eq_integral=> x _ do rewrite mulr_powRB1 ?subr_gt0//.
rewrite poweRD; last by rewrite poweRD_defE gt_eqF ?implyFb// subr_gt0 invf_lt1.
rewrite poweRe1; last by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
congr (_ * _); rewrite poweRN.
- by rewrite unlock fine_poweR.
- under eq_integral do rewrite -poweR_EFin -abse_EFin.
  by rewrite -powR_Lnorm ?gt_eqF// fin_num_poweR// ge0_fin_numE ?Lnorm_ge0.
Qed.

Lemma lerB_DLnorm f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] <= 'N_p%:E[f \+ g] + 'N_p%:E[g].
Proof.
move=> mf mg p1.
rewrite [in leLHS](_ : f = ((f + g) + (-%R \o g))%R); last by rewrite addrK.
rewrite (_ : 'N__[g] = 'N_p%:E[-%R \o g]); last first.
  rewrite (_ : EFin \o (-%R \o g) = \- (EFin \o g))//.
  apply: esym.
  exact: oppe_Lnorm.
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
by rewrite gt_eqF// (lt_le_trans _ (Lnorm_ge0 _ _ _)).
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

HB.mixin Record isLfunction d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) (f : T -> R)
  of @MeasurableFun d _ T R f := {
  Lfunction_finite : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfunction d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of @MeasurableFun d _ T R f & isLfunction d T R mu p p1 f}.

Arguments Lfunction_finite {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve Lfunction_finite : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) =>
  solve [apply: Lfunction_finite] : core.

Section LfunType_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

HB.instance Definition _ := gen_eqMixin (LfunType mu p1).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p1).

End LfunType_canonical.

Section AeEqEquiv.
Context d1 d2 (R : realType) (T1 : measurableType d1) (T2 : measurableType d2).
Variables (mu : {measure set T1 -> \bar R}).

Definition ae_eq_op (f g : {mfun T1 >-> T2}) := `[< f = g %[ae mu] >].

Let ae_eq_op_refl : reflexive ae_eq_op.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let ae_eq_op_sym : symmetric ae_eq_op.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP/ae_eq_sym.
Qed.

Let ae_eq_op_trans : transitive ae_eq_op.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_eq_trans gf fh).
Qed.

Canonical ae_eq_op_canonical :=
  EquivRel ae_eq_op ae_eq_op_refl ae_eq_op_sym ae_eq_op_trans.

Local Open Scope quotient_scope.

Definition aeEqMfun : Type := {eq_quot ae_eq_op}.
HB.instance Definition _ := Choice.on aeEqMfun.
HB.instance Definition _ := EqQuotient.on aeEqMfun.
Definition aqEqMfun_to_fun (f : aeEqMfun) : T1 -> T2 := repr f.
Coercion aqEqMfun_to_fun : aeEqMfun >-> Funclass.

Lemma ae_eqP (f g : aeEqMfun) : reflect (f = g %[ae mu]) (f == g %[mod aeEqMfun]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

End AeEqEquiv.

Reserved Notation "{ 'mfun_' mu , U >-> V }"
  (at level 0, U at level 69, format "{ 'mfun_'  mu ,  U  >->  V }").

Notation "{ 'mfun_' mu , aT >-> T }" := (@aeEqMfun _ _ _ aT T mu)
   : form_scope.

Import numFieldNormedType.Exports HBNNSimple.

HB.mixin Record isFinLebesgue d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E)
    (f : {mfun_ mu, T >-> measurableTypeR R}) := {
  Lebesgue_finite : finite_norm mu p f
}.

#[short(type=LspaceType)]
HB.structure Definition LebesgueSpace d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of isFinLebesgue d T R mu p p1 f}.

Section mfun_extra.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}).

Lemma mfunP (f : {mfun T >-> R}) : (f : T -> R) \in mfun.
Proof. exact: valP. Qed.

Import numFieldNormedType.Exports.

Lemma mfun_scaler_closed : scaler_closed (@mfun _ _ T R).
Proof. by move=> a/= f; rewrite !inE; exact: measurable_funM. Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ (@mfun _ _ T R)
  mfun_scaler_closed.

HB.instance Definition _ := [SubZmodule_isSubLmodule of {mfun T >-> R} by <:].

End mfun_extra.

Section Lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finLfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition Lfun : {pred _ -> _} := [predI @mfun _ _ T R & finLfun].
Definition Lfun_key : pred_key Lfun. Proof. exact. Qed.
Canonical Lfun_keyed := KeyedPred Lfun_key.
Lemma sub_Lfun_mfun : {subset Lfun <= mfun}.
Proof. by move=> x /andP[]. Qed.
Lemma sub_Lfun_finLfun : {subset Lfun <= finLfun}.
Proof. by move=> x /andP[]. Qed.

End Lfun_pred.

Section Lfun.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).
Notation Lfun := (@Lfun _ T R mu p).

Section Sub.
Context (f : T -> R) (fP : f \in Lfun).
Definition Lfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ T R f (set_mem (sub_Lfun_mfun fP)).
#[local] HB.instance Definition _ := Lfun_Sub1_subproof.

Definition Lfun_Sub2_subproof :=
  @isLfunction.Build d T R mu p p1 f (set_mem (sub_Lfun_finLfun fP)).
#[local] HB.instance Definition _ := Lfun_Sub2_subproof.
Definition Lfun_Sub := [the LfunType _ _ of f].
End Sub.

Lemma Lfun_rect (K : LfunType mu p1 -> Type) :
  (forall f (Pf : f \in Lfun), K (Lfun_Sub Pf)) -> forall u, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]].
have Pf : f \in Lfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_Lfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_Lfun_finLfun Pf) by [].
exact: Ksub.
Qed.

Lemma Lfun_valP f (Pf : f \in Lfun) : Lfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ :=
  isSub.Build _ _ (LfunType mu p1) Lfun_rect Lfun_valP.

Lemma LfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Lemma finite_norm_cst0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0// gt_eqF// (lt_le_trans _ p1). Qed.

HB.instance Definition _ :=
  @isLfunction.Build d T R mu p p1 (cst 0) finite_norm_cst0.

Lemma LfunP (f : LfunType mu p1) : (f : T -> R) \in Lfun.
Proof. exact: valP. Qed.

Lemma Lfun_oppr_closed : oppr_closed Lfun.
Proof.
move=> f /andP[mf /[!inE] lf].
rewrite rpredN/= mf/= inE/= /finite_norm.
rewrite (_ : _ \o _ = \- (EFin \o f))%E//.
by have -> := oppe_Lnorm mu (EFin \o f) p.
Qed.

HB.instance Definition _ := GRing.isOppClosed.Build _ Lfun
  Lfun_oppr_closed.

(* NB: not used directly by HB.instance *)
Lemma Lfun_addr_closed : addr_closed Lfun.
Proof.
split.
  by rewrite inE rpred0/= inE/=; exact: finite_norm_cst0.
move=> f g /andP[mf /[!inE]/= lf] /andP[mg /[!inE]/= lg].
rewrite rpredD//= inE/= /finite_norm.
rewrite (le_lt_trans (@eminkowski _ _ _ mu f g p _ _ _))//.
- by rewrite inE in mf.
- by rewrite inE in mg.
- by rewrite lte_add_pinfty.
Qed.

Import numFieldNormedType.Exports.

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
    rewrite [ltLHS](_ : _ = 'N[mu]_r%:E[EFin \o f]%E).
      exact: Lfunction_finite.
    rewrite unlock /Lnorm.
    by under eq_integral do rewrite gee0_abs ?lee_fin ?powR_ge0//.
  rewrite poweRM ?integral_ge0//.
  by rewrite poweR_EFin -powRrM mulfV ?gt_eqF ?(lt_le_trans ltr01)// powRr1.
- case: ifPn => mu0; last by rewrite mule0.
  rewrite -ess_supZl//; apply/eq_ess_sup/nearW => t /=.
  by rewrite normrZ EFinM.
Qed.

Lemma Lfun_submod_closed : submod_closed Lfun.
Proof.
split.
  by rewrite -[0]/(cst 0); exact: LfunP.
move=> a/= f g fP gP.
rewrite -[f]Lfun_valP -[g]Lfun_valP.
move: (Lfun_Sub _) (Lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=; apply: (le_lt_trans (eminkowski _ _ _ _)) => //.
- suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
- rewrite lte_add_pinfty//; last exact: Lfunction_finite.
  by rewrite LnormZ lte_mul_pinfty// ?lee_fin//; exact: Lfunction_finite.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ Lfun
  Lfun_submod_closed.

HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End Lfun.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (p : \bar R) (p1 : (1 <= p)%E).

(* TODO: 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Let nm f := fine ('N[mu]_p[EFin \o f]).

Lemma finite_norm_fine (f : ty) : (nm f)%:E = 'N[mu]_p[EFin \o f]%E.
Proof.
rewrite /nm fineK// fin_numElt (lt_le_trans ltNy0) ?Lnorm_ge0//=.
exact: Lfunction_finite.
Qed.

Lemma ler_LnormD (f g : ty) : nm (f + g) <= nm f + nm g.
Proof. by rewrite -lee_fin EFinD !finite_norm_fine eminkowski. Qed.

Lemma LnormrN (f : ty) : nm (\-f) = nm f.
Proof.
rewrite /nm (_ : _ \o _ = \- (EFin \o f))%E//; congr fine.
exact: oppe_Lnorm.
Qed.

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
rewrite finite_norm_fine => /Lnorm_eq0_eq0.
have /measurable_EFinP : measurable_fun setT f by [].
move=> /[swap] /[apply] => /(_ (lt_le_trans lte01 p1)).
by apply: filterS => x /(_ I) [].
Qed.

End Lspace_norm.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p (p1 : (1 <= p)%E) := [set: LspaceType mu p1].
Arguments Lspace : clear implicits.

Definition LspaceType1 := LspaceType mu (@lexx _ _ 1%E).

Definition LspaceType2 := LspaceType mu (lee1n 2).

Lemma Lfun_norm (f : T -> R) : f \in Lfun mu 1 -> normr \o f \in Lfun mu 1.
Proof.
case/andP; rewrite !inE/= => mf finf; apply/andP; split.
  by rewrite inE/=; exact: measurableT_comp.
rewrite inE/=/finite_norm.
under [X in ('N[_]__[X])%E]eq_fun => x do rewrite -abse_EFin.
by rewrite Lnorm_abse.
Qed.

Lemma Lfun_integrable (f : T -> R) r :
  1 <= r -> f \in Lfun mu r%:E ->
  mu.-integrable setT (fun x => (`|f x| `^ r)%:E).
Proof.
rewrite inE => r0 /andP[/[!inE]/= mf] lpf.
apply/integrableP; split => //.
  apply: measurableT_comp => //.
  apply: (measurableT_comp (measurable_powR _)) => //.
  exact: measurableT_comp.
move: lpf => /(poweR_lty r).
rewrite powR_Lnorm// ?gt_eqF// ?(lt_le_trans ltr01)//.
apply: le_lt_trans.
by under eq_integral => x _ do rewrite gee0_abs ?lee_fin ?powR_ge0//.
Qed.

Lemma Lfun1_integrable (f : T -> R) :
  f \in Lfun mu 1 <-> mu.-integrable setT (EFin \o f).
Proof.
split.
- move=> /[dup] lf /Lfun_integrable => /(_ (lexx _)).
  under eq_fun => x do rewrite powRr1//.
  move/integrableP => [mf fley]; apply/integrableP; split.
    by move: lf; rewrite inE=> /andP[/[!inE]/= {}mf _]; exact: measurableT_comp.
  rewrite (le_lt_trans _ fley)//=.
  by under [leRHS]eq_integral => x _ do rewrite normr_id.
- move/integrableP => [mF iF].
  rewrite inE; apply/andP; split; rewrite inE/=; first exact/measurable_EFinP.
  by rewrite /finite_norm Lnorm1.
Qed.

Lemma Lfun2_integrable_sqr (f : T -> R) : f \in Lfun mu 2%:E ->
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
rewrite inE => /andP[mf]; rewrite inE/= => l2f.
move: mf; rewrite inE/= => mf.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_funX.
rewrite (@lty_poweRy _ _ 2^-1)//.
rewrite (le_lt_trans _ l2f)//.
rewrite unlock.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= leey integral_ge0.
- by rewrite in_itv/= leey integral_ge0.
- rewrite ge0_le_integral//.
  + apply: measurableT_comp => //; apply/measurable_EFinP.
    exact: measurable_funX.
  + apply/measurable_EFinP.
    apply/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R) => //.
    exact/measurableT_comp.
  + by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

Lemma Lfun2_mul_Lfun1 (f g : T -> R) : f \in Lfun mu 2%:E -> g \in Lfun mu 2%:E ->
  f \* g \in Lfun mu 1.
Proof.
move=> l2f l2g.
move: (l2f) (l2g) => /[!inE] /andP[/[!inE]/= mf _] /andP[/[!inE]/= mg _].
apply/andP; split.
  by rewrite inE/=; apply: measurable_funM.
rewrite !inE/= /finite_norm.
apply: le_lt_trans.
  by apply: (@hoelder _ _ _ _ _ _ 2 2) => //; rewrite [RHS]splitr !div1r.
rewrite lte_mul_pinfty// ?ge0_fin_numE ?Lnorm_ge0//.
by move: l2f; rewrite inE => /andP[_]; rewrite inE/=.
by move: l2g; rewrite inE => /andP[_]; rewrite inE/=.
Qed.

Lemma Lfun_scale (f : T -> R) a r :
  1 <= r -> f \in Lfun mu r%:E -> a \o* f \in Lfun mu r%:E.
Proof.
move=> r1 /[dup] lf lpf.
rewrite inE; apply/andP; split.
  move: lf; rewrite inE => /andP[/[!inE]/= lf _].
  exact: measurable_funM.
rewrite !inE/= /finite_norm unlock /Lnorm.
rewrite poweR_lty//=.
under eq_integral => x _ do rewrite normrM powRM// EFinM.
rewrite integralZr// ?Lfun_integrable//.
rewrite muleC lte_mul_pinfty// ?lee_fin ?powR_ge0//.
move: lpf => /(Lfun_integrable r1) /integrableP[_].
under eq_integral => x _ do rewrite gee0_abs ?lee_fin ?powR_ge0//.
by [].
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

Section Lspace_finite_measure.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.

Lemma Lfun_cst c r : cst c \in Lfun mu r%:E.
Proof.
rewrite inE/=; apply/andP; split; rewrite inE//=.
rewrite /finite_norm unlock poweR_lty//.
under eq_integral => x _/= do rewrite (_ : `|c| `^ r = cst (`|c| `^ r) x)//.
apply/integrable_lty => //.
exact: finite_measure_integrable_cst.
Qed.

End Lspace_finite_measure.

Section Lfun_subset.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma Lfun_subset (p q : \bar R) : forall (p1 : 1 <= p) (q1 : 1 <= q),
  mu [set: T] \is a fin_num ->
  p <= q -> {subset Lfun mu q <= Lfun mu p}.
Proof.
have := measure_ge0 mu [set: T].
rewrite le_eqVlt => /predU1P[mu0 p1 q1 muTfin pq f +|mu_pos].
  rewrite inE => /andP[/[1!inE]/= mf _].
  rewrite inE; apply/andP; split; rewrite inE//=.
  rewrite /finite_norm unlock /Lnorm.
  move: p p1 {pq} => [r r1| |//]; last by rewrite -mu0 ltxx ltry.
  under eq_integral do rewrite /= -[(_ `^ _)%R]ger0_norm ?powR_ge0//=.
  rewrite (@integral_abs_eq0 _ _ _ _ _ (fun x => (`|f x| `^ r)%:E))//.
    by rewrite poweR0r// invr_neq0// gt_eqF// -lte_fin (lt_le_trans _ r1).
  apply/measurable_EFinP/(@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
  exact: measurableT_comp.
move: p q => [p| |//] [q| |]// p1 q1.
- move=> mu_fin.
  rewrite le_eqVlt => /predU1P[[->]//|]; rewrite lte_fin => pq f.
  rewrite inE/= => /andP[/[!inE]/= mf] ffin.
  apply/andP; split; rewrite inE//=.
  move: (ffin); rewrite /finite_norm.
  have p0 : (0 < p)%R by rewrite (lt_le_trans ltr01).
  have pN0 : p != 0%R by rewrite gt_eqF.
  have q0 : (0 < q)%R by rewrite (lt_le_trans ltr01).
  have qinv0 : (q^-1 != 0)%R by rewrite invr_neq0// gt_eqF.
  pose r := (q / p)%R.
  pose r' := (1 - r^-1)^-1%R.
  have := @hoelder _ _ _ mu (fun x => `|f x| `^ p)%R (cst 1)%R r r'.
  rewrite (_ : (_ \* cst 1)%R = (fun x => `|f x| `^ p))%R -?fctM ?mulr1//.
  rewrite Lnorm_cst1 unlock /Lnorm invr1.
  have mfp : measurable_fun [set: T] (fun x => (`|f x| `^ p)%R).
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  have m1 : measurable_fun [set: T] (@cst _ R 1%R) by exact: measurable_cst.
  have r0 : (0 < r)%R by rewrite/r divr_gt0.
  have r'0 : (0 < r')%R.
    by rewrite /r' invr_gt0 subr_gt0 invf_lt1 ?(lt_trans ltr01)//;
      rewrite /r ltr_pdivlMr// mul1r.
  have rr'1 : (r^-1 + r'^-1 = 1)%R by rewrite /r' /r invf_div invrK subrKC.
  move=> /(_ mfp m1 r0 r'0 rr'1).
  under [in leLHS] eq_integral do rewrite /= powRr1// norm_powR// normrE.
  under [in leRHS] eq_integral do
    rewrite /= norm_powR// normr_id -powRrM mulrCA divff// mulr1.
  rewrite [X in X <= _]poweRe1; last
    by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
  move=> h1 /lty_poweRy h2.
  apply/poweR_lty/(le_lt_trans h1).
  rewrite muleC lte_mul_pinfty ?fin_numElt?poweR_ge0//.
    by rewrite (lt_le_trans _ (poweR_ge0 _ _))//= ltey_eq fin_num_poweR.
  rewrite poweR_lty// (lty_poweRy qinv0)//.
  by have:= ffin; rewrite /finite_norm unlock /Lnorm.
- have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
  move=> muoo _ f.
  rewrite !inE => /andP[/[1!inE]/= mf].
  rewrite !inE/= /finite_norm unlock /Lnorm mu_pos => supf_lty.
  apply/andP; split; rewrite inE//= /finite_norm unlock /Lnorm.
  rewrite poweR_lty//; move: supf_lty => /ess_supr_bounded[M fM].
  rewrite (@le_lt_trans _ _ (\int[mu]_x (M `^ p)%:E)); [by []| |]; last first.
    by rewrite integral_cst// ltey_eq fin_numM.
  apply: ae_ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin powR_ge0.
  + apply/measurable_EFinP.
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  + by move=> x _; rewrite lee_fin powR_ge0.
  + apply: filterS fM => t/= ftM _.
    rewrite lee_fin ge0_ler_powR//; first exact: ltW.
    by rewrite nnegrE (le_trans _ ftM).
- by move=> muTfin _.
Qed.

Lemma Lfun_subset12 : mu [set: T] \is a fin_num ->
  {subset Lfun mu 2%:E <= Lfun mu 1}.
Proof. by move=> ?; apply: Lfun_subset => //; rewrite lee1n. Qed.

End Lfun_subset.
