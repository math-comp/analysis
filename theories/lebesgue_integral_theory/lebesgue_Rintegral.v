(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean finmap.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals real_interval topology ereal tvs.
From mathcomp Require Import normedtype sequences esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun measurable_realfun.
From mathcomp Require Import simple_functions measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.
From mathcomp Require Import lebesgue_integral_nonneg lebesgue_integrable.
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

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
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
Context d {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}).
Implicit Types (D A B : set T) (f : T -> R).

Lemma EFin_normr_Rintegral A f : measurable A ->
  mu.-integrable A (EFin \o f) ->
  `| \int[mu]_(x in A) f x |%:E = `| \int[mu]_(x in A) (f x)%:E |%E.
Proof.
move=> mA /integrableP[mf intfoo]; rewrite -[RHS]fineK.
- rewrite abse_fin_num fin_num_abs.
  exact: (le_lt_trans (le_abse_integral _ _ _)).
- rewrite /= fine_abse// fin_num_abs.
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
move=> mD intf; rewrite (_ : r = fine r%:E)// -fineM//.
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

Import MeasurableR.

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
rewrite -ge0_fin_numE; first exact: integral_ge0.
move/fineK ->.
by apply: ge0_le_integral => //=; do 2 apply: measurableT_comp => //;
  exact/measurable_EFinP.
Qed.

Lemma Rintegral_setU (A B : set T) (f : T -> R) :
    d.-measurable A -> d.-measurable B ->
    mu.-integrable (A `|` B) (EFin \o f) -> [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mA mB mf AB; rewrite /Rintegral integral_setU//.
  exact/(measurable_int mu).
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
  forall r, \int[mu]_(_ in D) r = r * fine (mu D).
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
- rewrite -integral_fin_num_abs//; last by case/integrableP : mf1.
  by apply/measurable_EFinP; case/integrableP : mf1.
- rewrite -integral_fin_num_abs//; last by case/integrableP : mf2.
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

Section Rintegral_lebesgue_measure.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Type f : R -> R.

Import MeasurableR.

Lemma Rintegral_itvbo_itvbc (a : itv_bound R) (r : R) f :
  mu.-integrable [set` Interval a (BLeft r)] (EFin \o f) ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x) =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itvbo_itvbc//.
exact: (measurable_int mu).
Qed.

Lemma Rintegral_itvob_itvcb (r : R) (b : itv_bound R) f :
  mu.-integrable [set` Interval (BRight r) b] (EFin \o f) ->
  \int[mu]_(x in [set` Interval (BRight r) b]) (f x) =
  \int[mu]_(x in [set` Interval (BLeft r) b]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itvob_itvcb//.
exact: (measurable_int mu).
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
rewrite (@itv_bndbnd_setU _ _ _ (BLeft x)).
  by case: a ax {itf} => -[].
  by rewrite (le_trans _ xb)// bnd_simp.
rewrite Rintegral_setU//=.
- by rewrite -itv_bndbnd_setU -?ltBRight_leBLeft// ltW.
- apply/disj_setPS => y [/=]; rewrite 2!in_itv/= => /andP[_ yx] /andP[].
  by rewrite leNgt yx.
rewrite Rintegral_itvbo_itvbc//.
  apply: integrableS itf => //; apply: subset_itvl.
  by rewrite (le_trans _ xb)// bnd_simp.
rewrite addrC addKr Rintegral_itvob_itvcb//.
by apply: integrableS itf => //; exact/subset_itvr/ltW.
Qed.

Lemma Rintegral_gt0 f D :
  mu.-integrable D (EFin \o f) ->
  open D ->
  {in D, continuous f} ->
  {in D, forall x : R, 0 <= f x} ->
  ~ {in D, forall x : R, f x == 0} ->
  0 < \int[mu]_(x in D) f x.
Proof.
move=> f_ble oD cf f_ge0 /existsNP [] c /not_implyP [] cD /negP fc_neq0.
have fc_gt0 : f c > 0 by rewrite lt_neqAle eq_sym fc_neq0 f_ge0.
pose U := `]f c / 2, +oo[%classic.
have oU : open U by exact: itv_open_ends_open.
have /(continuous_inP _ oD)/(_ U oU) oDfU:= cf.
have mD : measurable D by exact: open_measurable.
have : D `&` f @^-1` U != set0.
  apply/set0P; exists c; split => /=; first by move/set_mem: cD.
  rewrite /U /= in_itv/= andbT.
  by rewrite -[fc in fc / _]add0r midf_lt.
have -> := open_bigcup_basis real_basis oDfU.
case/eqP/bigcup0P/existsNP => I /not_implyP[] I_spec /eqP/set0P[]/= p Ip.
have := I_spec => -[]/= [] a _ [] b _ IE IDfU.
have mI : measurable I by rewrite -IE; exact: open_measurable.
have ID : I `<=` D by apply: (subset_trans IDfU); exact: subIsetl.
rewrite -fine0; apply: fine_lt => //; first exact: integrable_fin_num.
suff : (0 < \int[mu]_(x in I) (f x)%:E)%E.
  move/lt_le_trans; apply.
  apply: ge0_subset_integral => //=.
    apply/measurable_EFinP.
    exact: open_continuous_measurable_fun.
  by move=> x Dx; apply: f_ge0; rewrite inE.
apply: (@lt_le_trans _ _ (\int[mu]_(x in I) (cst (f c / 2)%:E x))%E).
  rewrite integral_cst//=.
  apply: mule_gt0; first by rewrite lte_fin divr_gt0.
  rewrite -IE lebesgue_measure_itv/= lte_fin.
  suff ab : a < b by rewrite ab lte_fin subr_gt0.
  by move: Ip; rewrite -IE/= in_itv/= => /andP[] /lt_trans /[apply].
apply: ge0_le_integral => //=.
- by move=> ? ?; rewrite lee_fin divr_ge0// ltW.
- apply/measurable_EFinP.
  apply: open_continuous_measurable_fun; first by rewrite -IE.
  by move=> ?; rewrite inE => ?; apply: cf; rewrite inE; apply: ID.
move=> x Ix; rewrite lee_fin ltW//.
move: Ix => /IDfU[] Dx /=.
by rewrite /U/= in_itv/= andbT.
Qed.

Lemma Rintegral_gt0_itvcc f (a b : R) :
  a < b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], forall x : R, 0 <= f x} ->
  ~ {in `[a, b], forall x : R, f x == 0} ->
  0 < \int[mu]_(x in `[a, b]) f x.
Proof.
move=> ab cf f_ge0 f_neq0.
have ooSab : `]a, b[ `<=` `[a, b] by exact: subset_itvW.
have cf_oo := sub_in1 ooSab cf.
have within_cf := continuous_subspace_itv cf.
have := f_neq0 => /existsNP[] p /not_implyP[] pab /negP fp_neq0.
have fp_gt0 : 0 < f p by rewrite lt_neqAle eq_sym fp_neq0/= f_ge0.
have f_ble : mu.-integrable `[a, b] (EFin \o f).
  apply: compact_continuous_Rintegrable => //; first by exists p.
  exact: segment_compact.
have f_ble_oo : mu.-integrable `]a, b[ (EFin \o f).
  exact: (integrableS _ _ _ f_ble).
suff : (0 < \int[mu]_(x in `[a, b]) (f x)%:E)%E.
  move/fine_lt; apply => //.
  exact: integrable_fin_num.
rewrite integral_itvbb_itvoo/=.
  apply/measurable_EFinP.
  apply: subspace_continuous_measurable_fun => //.
  exact: continuous_subspace_itv.
rewrite -[ltRHS]fineK ?integrable_fin_num//=.
rewrite lte_fin Rintegral_gt0//.
- by rewrite -in1_mksetP.
- by rewrite -in1_mksetP; apply: (sub_in1 ooSab).
(* the rest of the proof is just for ~ {in `]a, b[, forall x : R, f x == 0},
   i.e., about extending a constant function on an open interval to its closure *)
move=> f_eq0oo.
have faboo_sing : f @` `]a, b[%classic = [set 0].
  apply/seteqP; split => x /=.
    by case => y /mem_set /f_eq0oo /eqP -> /esym.
  move->; exists (miditv `]a, b[); first exact: mem_miditv.
  by apply/eqP/f_eq0oo; rewrite inE; exact: mem_miditv.
have: `[a, b]%classic p by [].
rewrite -(setUitv_set2 false true) ?ltW//.
case; first by move/mem_set/f_eq0oo; rewrite (negPf fp_neq0).
case => [pa|pb]/=.
  have : connected `[a, b[%classic.
    exact/connected_intervalP/interval_is_interval.
  have : {within `[a, b[, continuous f}.
    have := within_cf; apply: continuous_subspaceW.
    by apply/subset_itvl; rewrite bnd_simp.
  move/connected_continuous_connected/[apply].
  rewrite -setU_1itvob ?bnd_simp// image_setU faboo_sing -pa image_set1.
  apply/connectedPn; exists (fun b => if b then [set 0] else [set f p]).
  split => //; first by case; [exists 0 | exists (f p)].
  split.
    by rewrite -(closure_id [set _]).1// set1I in_set1 (negPf fp_neq0).
  by rewrite -(closure_id [set _]).1// set1I in_set1 (negPf fp_neq0).
have : connected `]a, b]%classic.
  exact/connected_intervalP/interval_is_interval.
have : {within `]a, b], continuous f}.
  have := within_cf; apply: continuous_subspaceW.
  by apply/subset_itvr; rewrite bnd_simp.
move/connected_continuous_connected/[apply].
rewrite -setU_itvob1 ?bnd_simp// image_setU faboo_sing -pb image_set1.
apply/connectedPn; exists (fun b => if b then [set f p] else [set 0]).
split => //; first by case; [exists (f p) | exists 0].
split.
  by rewrite -(closure_id [set _]).1// setI1 in_set1 (negPf fp_neq0).
by rewrite -(closure_id [set _]).1// setI1 in_set1 (negPf fp_neq0).
Qed.

End Rintegral_lebesgue_measure.
#[deprecated(since="mathcomp-analysis 1.17.0", use=Rintegral_itvbo_itvbc)]
Notation Rintegral_itv_bndo_bndc := Rintegral_itvbo_itvbc (only parsing).
#[deprecated(since="mathcomp-analysis 1.17.0", use=Rintegral_itvob_itvcb)]
Notation Rintegral_itv_obnd_cbnd := Rintegral_itvob_itvcb (only parsing).

Section Rdominated_convergence.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
  (f_ : (T -> R)^nat) (f g : T -> R).
Import MeasurableR.
Hypotheses (mf_ : forall n, measurable_fun D (f_ n))
  (f_f : forall x, D x -> f_ ^~ x @ \oo --> f x)
  (int_g : mu.-integrable D (EFin \o g))
  (absfg : forall n x, D x -> `|f_ n x| <= g x).

Lemma Rdominated_cvg :
  \int[mu]_(x in D) f_ n x @[n \oo] --> \int[mu]_(x in D) f x.
Proof.
rewrite /Rintegral.
have []// := @dominated_convergence _ _ _ mu _ mD (fun n t => (f_ n t)%:E)
    (EFin \o f) (EFin \o g).
- by move=> n; exact/measurable_EFinP.
- exact/measurable_EFinP/measurable_fun_cvg.
- by apply: aeW => x Dx; apply/fine_cvgP; split; [exact: nearW|exact: f_f].
- by apply: aeW => x n Dx/=; rewrite lee_fin absfg.
by move=> int_f _/= int_f_f; apply/fine_cvg; rewrite fineK// integrable_fin_num.
Qed.

End Rdominated_convergence.
