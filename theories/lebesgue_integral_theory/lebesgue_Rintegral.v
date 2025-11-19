(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import function_spaces esum measure lebesgue_measure.
From mathcomp Require Import numfun realfun simple_functions.
From mathcomp Require Import measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.
From mathcomp Require Import lebesgue_integral_nonneg.
From mathcomp Require Import lebesgue_integrable.
From mathcomp Require Import lebesgue_integral_dominated_convergence.

(**md**************************************************************************)
(* # The Lebesgue Integral for real-valued functions                          *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*       Rintegral mu D f := fine (\int[mu]_(x in D) f x).                    *)
(* ```                                                                        *)
(*                                                                            *)
(* This file recasts lemmas about `integral` to `Rintegral`. It also          *)
(* established that Continuous functions are dense in $L^1$.                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Rintegral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Definition Rintegral (D : set T) (f : T -> R) :=
  fine (\int[mu]_(x in D) (f x)%:E).

End Rintegral.

Notation "\int [ mu ]_ ( x 'in' D ) f" :=
  (Rintegral mu D (fun x => f)%R) : ring_scope.
Notation "\int [ mu ]_ x f" :=
  (Rintegral mu setT (fun x => f)%R) : ring_scope.

Section Rintegral.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (D A B : set T) (f : T -> R).

Lemma EFin_normr_Rintegral A f : measurable A ->
  mu.-integrable A (EFin \o f) ->
  `| \int[mu]_(x in A) f x |%:E = `| \int[mu]_(x in A) (f x)%:E |%E.
Proof.
move=> mA /integrableP[mf intfoo]; rewrite -[RHS]fineK.
- rewrite /= fine_abse// fin_num_abs.
  exact: (le_lt_trans (le_abse_integral _ _ _)).
- rewrite abse_fin_num fin_num_abs.
  exact: (le_lt_trans (le_abse_integral _ _ _)).
Qed.

Lemma eq_Rintegral D g f : {in D, f =1 g} ->
  \int[mu]_(x in D) f x = \int[mu]_(x in D) g x.
Proof. by move=> fg; congr fine; apply: eq_integral => /= x xD; rewrite fg. Qed.

Lemma Rintegral_mkcond D f : \int[mu]_(x in D) f x = \int[mu]_x (f \_ D) x.
Proof.
rewrite {1}/Rintegral integral_mkcond/=.
by under eq_integral do rewrite restrict_EFin.
Qed.

Lemma Rintegral_mkcondr D P f :
  \int[mu]_(x in D `&` P) f x = \int[mu]_(x in D) (f \_ P) x.
Proof.
rewrite {1}/Rintegral integral_mkcondr.
by under eq_integral do rewrite restrict_EFin.
Qed.

Lemma Rintegral_mkcondl D P f :
  \int[mu]_(x in P `&` D) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite setIC Rintegral_mkcondr. Qed.

Lemma RintegralZl D f r : measurable D -> mu.-integrable D (EFin \o f) ->
  \int[mu]_(x in D) (r * f x) = r * \int[mu]_(x in D) f x.
Proof.
move=> mD intf; rewrite (_ : r = fine r%:E)// -fineM//; last first.
  exact: integrable_fin_num.
by congr fine; under eq_integral do rewrite EFinM; exact: integralZl.
Qed.

Lemma RintegralZr D f r : measurable D -> mu.-integrable D (EFin \o f) ->
  \int[mu]_(x in D) (f x * r) = \int[mu]_(x in D) f x * r.
Proof.
move=> mD intf; rewrite mulrC -RintegralZl//.
by under eq_Rintegral do rewrite mulrC.
Qed.

Lemma Rintegral_ge0 D f : (forall x, D x -> 0 <= f x) ->
  0 <= \int[mu]_(x in D) f x.
Proof. by move=> f0; rewrite fine_ge0// integral_ge0. Qed.

Lemma le_normr_Rintegral D f : measurable D -> mu.-integrable D (EFin \o f) ->
  `|\int[mu]_(t in D) f t| <= \int[mu]_(t in D) `|f t|.
Proof.
move=> mA /integrableP[mf ifoo].
rewrite -lee_fin; apply: le_trans.
  apply: (le_trans _ (le_abse_integral mu mA mf)).
  rewrite /abse.
  have [/fineK <-//|] := boolP (\int[mu]_(x in D) (EFin \o f) x \is a fin_num)%E.
  by rewrite fin_numEn => /orP[|] /eqP ->; rewrite leey.
rewrite /Rintegral.
move: ifoo.
rewrite -ge0_fin_numE; last exact: integral_ge0.
move/fineK ->.
by apply: ge0_le_integral => //=; do 2 apply: measurableT_comp => //;
  exact/measurable_EFinP.
Qed.

Lemma Rintegral_setU (A B : set T) (f : T -> R) :
    d.-measurable A -> d.-measurable B ->
    mu.-integrable (A `|` B) (EFin \o f) -> [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mA mB mf AB; rewrite /Rintegral integral_setU_EFin//; last first.
  exact/measurable_EFinP/(measurable_int mu).
have mAf :  mu.-integrable A (EFin \o f).
  by  apply: integrableS mf => //; exact: measurableU.
have mBf :  mu.-integrable B (EFin \o f).
  by apply: integrableS mf => //; exact: measurableU.
move/integrableP : mAf => [mAf itAfoo].
move/integrableP : mBf => [mBf itBfoo].
rewrite fineD//.
- by rewrite fin_num_abs (le_lt_trans _ itAfoo)//; exact: le_abse_integral.
- by rewrite fin_num_abs (le_lt_trans _ itBfoo)//; exact: le_abse_integral.
Qed.

Lemma Rintegral_set0 f : \int[mu]_(x in set0) f x = 0.
Proof. by rewrite /Rintegral integral_set0. Qed.

Lemma Rintegral_cst D : d.-measurable D ->
  forall r, \int[mu]_(x in D) (cst r) x = r * fine (mu D).
Proof.
move=> mD r; rewrite /Rintegral/= integral_cst//.
have := leey (mu D); rewrite le_eqVlt => /predU1P[->/=|muy]; last first.
  by rewrite fineM// ge0_fin_numE.
rewrite mulr0 mulr_infty/=; have [_|r0|r0] := sgrP r.
- by rewrite mul0e.
- by rewrite mul1e.
- by rewrite mulN1e.
Qed.

Lemma le_Rintegral D f1 f2 : measurable D ->
  mu.-integrable D (EFin \o f1) ->
  mu.-integrable D (EFin \o f2) ->
  (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> mD mf1 mf2 f12; rewrite /Rintegral fine_le//.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf1.
  by apply/measurable_EFinP; case/integrableP : mf1.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf2.
  by apply/measurable_EFinP; case/integrableP : mf2.
- by apply/le_integral => // x xD; rewrite lee_fin f12//; exact/set_mem.
Qed.

Lemma RintegralD D f1 f2 : measurable D ->
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
move=> mD if1 if2.
by rewrite /Rintegral integralD_EFin// fineD//; exact: integrable_fin_num.
Qed.

Lemma RintegralB D f1 f2 : measurable D ->
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  \int[mu]_(x in D) (f1 x - f2 x) =
  \int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x.
Proof.
move=> mD if1 if2.
by rewrite /Rintegral integralB_EFin// fineB//; exact: integrable_fin_num.
Qed.

End Rintegral.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `Rintegral_setU`")]
Notation Rintegral_setU_EFin := Rintegral_setU (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `le_normr_Rintegral`")]
Notation le_normr_integral := le_normr_Rintegral (only parsing).

Section Rintegral_lebesgue_measure.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Type f : R -> R.

Lemma Rintegral_itv_bndo_bndc (a : itv_bound R) (r : R) f :
  mu.-integrable [set` Interval a (BLeft r)] (EFin \o f) ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x) =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itv_bndo_bndc//.
by apply/measurable_EFinP; exact: (measurable_int mu).
Qed.

Lemma Rintegral_itv_obnd_cbnd (r : R) (b : itv_bound R) f :
  mu.-integrable [set` Interval (BRight r) b] (EFin \o f) ->
  \int[mu]_(x in [set` Interval (BRight r) b]) (f x) =
  \int[mu]_(x in [set` Interval (BLeft r) b]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itv_obnd_cbnd//.
by apply/measurable_EFinP; exact: (measurable_int mu).
Qed.

Lemma Rintegral_set1 f (r : R) : \int[mu]_(x in [set r]) f x = 0.
Proof. by rewrite /Rintegral integral_set1. Qed.

Lemma Rintegral_itvB f (a b : itv_bound R) x :
  mu.-integrable [set` (Interval a b)] (EFin \o f) ->
  (a <= BRight x)%O -> (BRight x <= b)%O ->
  \int[mu]_(t in [set` Interval a b]) f t -
  \int[mu]_(t in [set` Interval a (BRight x)]) f t =
  \int[mu]_(x in [set` Interval (BRight x) b]) f x.
Proof.
move=> itf; rewrite le_eqVlt => /predU1P[ax|ax xb].
  rewrite ax => _; rewrite [in X in _ - X]set_itv_ge ?bnd_simp//.
  by rewrite Rintegral_set0 subr0.
rewrite (@itv_bndbnd_setU _ _ _ (BLeft x)); last 2 first.
  by case: a ax {itf} => -[].
  by rewrite (le_trans _ xb)// bnd_simp.
rewrite Rintegral_setU//=.
- rewrite Rintegral_itv_bndo_bndc//; last first.
    apply: integrableS itf => //; apply: subset_itvl.
    by rewrite (le_trans _ xb)// bnd_simp.
  rewrite addrC addKr Rintegral_itv_obnd_cbnd//.
  by apply: integrableS itf => //; exact/subset_itvr/ltW.
- by rewrite -itv_bndbnd_setU -?ltBRight_leBLeft// ltW.
- apply/disj_setPS => y [/=]; rewrite 2!in_itv/= => /andP[_ yx] /andP[].
  by rewrite leNgt yx.
Qed.

End Rintegral_lebesgue_measure.
