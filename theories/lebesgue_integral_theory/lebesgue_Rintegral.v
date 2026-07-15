(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop ereal topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
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
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
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

Lemma Rintegral_patch_negligible (f g : T -> R) (A D : set T) :
  d.-measurable A -> d.-measurable D -> mu D = 0 -> measurable_fun A f -> measurable_fun D g -> Rintegral mu A (patch f D g) = Rintegral mu A f.
Proof.
move=> mA mD muD0 mf mg.
wlog D_sub_A : D A mA mD muD0 mf mg / D `<=` A.
  move=> sub_case.
  transitivity (Rintegral mu A (patch f (D `&` A) g)).
    apply: eq_Rintegral => x.
    by rewrite in_setI andbC => ->.
  apply: sub_case => //.
  - by apply: measurableI.
  - apply: subset_measure0 muD0 => //.
    by apply: measurableI.
  - by apply: measurable_funS mg.   
congr (fine _).
apply: ae_eq_integral => //; [| exact/measurable_EFinP |].
  change (measurable_fun A (EFin \o patch f D g)).
  rewrite comp_patch /patch/=.
  rewrite -(setDUK D_sub_A).
  apply/measurable_funU => //; first by apply: measurableD.
  split.
  - apply: (eq_measurable_fun (EFin \o g)).
    + by move=> ? ->.
    + by apply/measurable_EFinP.
  - apply: (eq_measurable_fun (EFin \o f)).
    + move=> x.
      by rewrite in_setD => /andP[_ /negbTE ->].
    + apply/measurable_EFinP.
      by apply: measurable_funS mf.
rewrite /ae_eq /prop_near1 /nbhs/= /almost_everywhere/=.
exists D; split=> //.
apply: subsetCl => x /= nDx Ax.
by rewrite /patch ifN// notin_setE.
Qed.

End Rintegral.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `le_normr_Rintegral`")]
Notation le_normr_integral := le_normr_Rintegral (only parsing).

Section Rintegral_lebesgue_measure.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Type f : R -> R.

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

Lemma Rintegral_itvbb_itvoo (x y : R) f (b1 b2 : bool) :
  measurable_fun `]x, y[ (EFin \o f) ->
  \int[mu]_(z in [set` Interval (BSide b1 x) (BSide b2 y)]) f z =
  \int[mu]_(z in `]x, y[) f z.
Proof. by move=> mf /=; congr fine; rewrite integral_itvbb_itvoo. Qed.

Lemma Rintegral_itvby_itvoy (x : R) f (b1 : bool) :
  measurable_fun `]x, +oo[ (EFin \o f) ->
  \int[mu]_(z in [set` Interval (BSide b1 x) +oo%O]) f z =
  \int[mu]_(z in `]x, +oo[) f z.
Proof.
move=> mf /=; congr fine.
case: b1 => [|//]; symmetry.
by apply: integral_itvob_itvcb.
Qed.

Lemma Rintegral_itvbb_itvbb (x y : R) (f g : R -> R) (b1 b2 b1' b2' : bool) :
  measurable_fun `]x, y[ f ->
  {in `]x, y[%R, f =1 g} ->
  \int[mu]_(z in [set` Interval (BSide b1 x) (BSide b2 y)]) f z =
  \int[mu]_(z in [set` Interval (BSide b1' x) (BSide b2' y)]) g z.
Proof.
move=> mf eqfg.
transitivity (\int[mu]_(z in `]x, y[) f z).
  apply: Rintegral_itvbb_itvoo.
  by apply/measurable_EFinP.
transitivity (\int[mu]_(z in `]x, y[) g z).
  by apply: eq_Rintegral; move=> + /set_mem.
symmetry; apply: Rintegral_itvbb_itvoo.
apply/measurable_EFinP.
by apply: (eq_measurable_fun f); first by move=> + /set_mem.
Qed.

Lemma Rintegral_itvby_itvby (x : R) (f g : R -> R) (b1 b1' : bool) :
  measurable_fun `]x, +oo[ f ->
  {in `]x, +oo[, f =1 g} ->
  \int[mu]_(z in [set` Interval (BSide b1 x) +oo%O]) f z =
  \int[mu]_(z in [set` Interval (BSide b1' x) +oo%O]) g z.
Proof.
move=> mf eqfg.
transitivity (\int[mu]_(z in `]x, +oo[) f z).
  apply: Rintegral_itvby_itvoy.
  by apply/measurable_EFinP.
transitivity (\int[mu]_(z in `]x, +oo[) g z).
  by apply: eq_Rintegral; move=> + /set_mem.
symmetry; apply: Rintegral_itvby_itvoy.
apply/measurable_EFinP.
by apply: (eq_measurable_fun f); first by move=> + /set_mem.
Qed.

Lemma Rintegral_itv0 f (a b : R) (b1 b2 : bool) :
    a >= b -> Rintegral mu [set` Interval (BSide b1 a) (BSide b2 b)] f = 0.
Proof.
rewrite le_eqVlt => /predU1P[->|b_lt_a].
- case: b1 b2 => [] []; rewrite set_itvE ?Rintegral_set0//.
  exact: Rintegral_set1.
- rewrite set_itv_ge -?leNgt; first by apply: lteifS.
  exact: Rintegral_set0.
Qed.  

Lemma Rintegral_itvD f (a c : R) (b1 b2 b1' b2' : bool) (b : itv_bound R) :
  (BLeft a <= b <= BRight c)%O ->
  mu.-integrable `]a, c[ (EFin \o f) ->
  Rintegral mu [set` Interval (BSide b1 a) (BSide b2 c)] f = Rintegral mu [set` Interval (BSide b1' a) b] f + Rintegral mu [set` Interval b (BSide b2' c)] f.
Proof.
case: b => [b3 b|[] //].
rewrite !bnd_simp => /andP[a_le_b b_le_c] f_int.
have mf : measurable_fun `]a, c[ f.
  apply/measurable_EFinP.
  by apply: (measurable_int mu).
move: a_le_b; rewrite le_eqVlt => /predU1P[<-|a_lt_b].
  rewrite [X in _ = X + _]Rintegral_itv0// add0r.
  by apply: Rintegral_itvbb_itvbb.
move: b_le_c; rewrite le_eqVlt => /predU1P[->|b_lt_c].
  rewrite [X in _ = _ + X]Rintegral_itv0// addr0.
  by apply: Rintegral_itvbb_itvbb.
transitivity (Rintegral mu `]a, c[ f); first by apply: Rintegral_itvbb_itvbb.
rewrite (itv_bndbnd_setU (x := BSide b3 b)); [ by apply: lteifS .. |].
rewrite [LHS]Rintegral_setU; [ exact: measurable_itv .. | | |].
- by rewrite -itv_bndbnd_setU//; apply: lteifS.
- apply/disj_setPS => x /=[/andP[_ +] /andP[+ _]].
  move/le_trans/[apply].
  by rewrite bnd_simp ltxx.
congr (_ + _); apply: Rintegral_itvbb_itvbb => //.
- apply: (measurable_funS (E := `]a, c[)) => //.
  by apply: subset_itvl; rewrite bnd_simp ltW.
- apply: (measurable_funS (E := `]a, c[)) => //.
  by apply: subset_itvr; rewrite bnd_simp ltW.
Qed.

Lemma Rintegral_itvDy f (a : R) (b : itv_bound R) (b1 b1' : bool) :
  (BLeft a <= b)%O ->
  mu.-integrable `]a, +oo[ (EFin \o f) ->
  Rintegral mu [set` Interval (BSide b1 a) +oo%O] f 
  = Rintegral mu [set` Interval (BSide b1' a) b] f + Rintegral mu [set` Interval b +oo%O] f.
Proof.
move=> /[swap] int_f.
case: b => [b2 b|[] // _]; last first.
  rewrite set_itvxx Rintegral_set0 addr0.
  apply: Rintegral_itvby_itvby => //.
  apply/measurable_EFinP.
  exact: measurable_int int_f.
rewrite !bnd_simp => a_le_b.
have mf : measurable_fun `]a, +oo[ f.
  apply/measurable_EFinP.
  by apply: (measurable_int mu).
move: a_le_b; rewrite le_eqVlt => /predU1P[<-|a_lt_b].
  rewrite [X in _ = X + _]Rintegral_itv0// add0r.
  by apply: Rintegral_itvby_itvby.
transitivity (Rintegral mu `]a, +oo[ f); first by apply: Rintegral_itvby_itvby.
rewrite (itv_bndbnd_setU (x := BSide b2 b))//; [by apply: lteifS .. |].
rewrite [LHS]Rintegral_setU; [ exact: measurable_itv .. | | |].
- by rewrite -itv_bndbnd_setU//; apply: lteifS.
- apply/disj_setPS => x /=[/andP[_ +] /andP[+ _]].
  move/le_trans/[apply].
  by rewrite bnd_simp ltxx.
congr (_ + _); apply: Rintegral_itvbb_itvbb => //.
apply: measurable_funS mf => //.
by apply: subset_itvl.
Qed.

Lemma Rintegral_patch_finite (f g : R -> R) (A D : set R) :
  lebesgue_display.-measurable A -> finite_set D -> measurable_fun A f -> Rintegral mu A (patch f D g) = Rintegral mu A f.
Proof.
move=> mA finD mf.
case: (finD) => n; rewrite card_eq_sym => /pcard_eqP[indexD].
have bij_indexD := bij (f := indexD).
have D_bigcup : D = \bigcup_(i < n) [set indexD i].
  by rewrite -{1}(fsbig_setU_set1 finD) (reindex_fsbig indexD _ _ _ bij_indexD)/= fsbig_setU.
have mfD (h : R -> R) : measurable_fun D h.
  rewrite D_bigcup bigcup_mkcond.
  apply/measurable_fun_bigcup => i; first by case: ifP.
  case: ifP => // _.
  - exact: measurable_fun_set1.
  - exact: measurable_fun_set0.
apply: Rintegral_patch_negligible => //.
- rewrite D_bigcup bigcup_mkcond.
  apply: bigcup_measurable => k _.
  by case: ifP.
- apply: countable_lebesgue_measure0.
  exact: finite_set_countable finD.
Qed.

End Rintegral_lebesgue_measure.
#[deprecated(since="mathcomp-analysis 1.17.0", use=Rintegral_itvbo_itvbc)]
Notation Rintegral_itv_bndo_bndc := Rintegral_itvbo_itvbc (only parsing).
#[deprecated(since="mathcomp-analysis 1.17.0", use=Rintegral_itvob_itvcb)]
Notation Rintegral_itv_obnd_cbnd := Rintegral_itvob_itvcb (only parsing).

Section Rintegral_bound_continuity.
Context (R : realType) (mu := @lebesgue_measure R) (f : R -> R).
Context  (a b x y : R) (x_ y_ : R -> R) (b1 b2 b1' b2' : bool).

Hypothesis a_lt_b : a < b.
Hypothesis f_int : 
  mu.-integrable [set` Interval (BSide b1 a) (BSide b2 b)] (EFin \o f).
Hypotheses (a_le_x : a <= x) (y_le_b : y <= b).
Hypothesis near_x_ge_a : \forall e \near 0^'+, a <= x_ e.
Hypothesis near_y_le_b : \forall e \near 0^'+, y_ e <= b.
Hypotheses (cvg_x : x_ @ 0^'+ --> x) (cvg_y : y_ @ 0^'+ --> y).

Lemma Rintegral_bound_continuous :
  \int[mu]_(z in [set` Interval (BSide b1 (x_ e)) (BSide b2 (y_ e))]) (f z)
  @[e --> 0^'+] --> 
  \int[mu]_(z in [set` Interval (BSide b1' x) (BSide b2' y)]) (f z).
Proof.
have mf_oo x' y' : a <= x' -> y' <= b -> measurable_fun `]x', y'[ f.
  move=> a_le_x' y'_le_b.
  apply: measurable_funS; last first.
  - apply/measurable_EFinP.
      apply: (measurable_int mu).
    exact: f_int.
  - by apply: subset_itvW.
  - exact: measurable_itv.
wlog suff oo_cvg : / \int[mu]_(z in `]x_ e, y_ e[) f z 
    @[e --> 0^'+] --> \int[mu]_(z in `]x, y[) f z.
apply: cvg_trans; last apply: (cvg_to_eq oo_cvg).
- apply: near_eq_cvg.
  near=> e.
  apply: Rintegral_itvbb_itvbb => //.
  by apply: mf_oo; near: e.
- apply: Rintegral_itvbb_itvbb => //.
  by apply: mf_oo. 
apply: cvg_trans.
  apply: near_eq_cvg.
  near=> e.
  by rewrite Rintegral_mkcond.
apply/cvg_at_rightP => u [u_gt0 u_to0].
wlog x_u_gea : u u_gt0 u_to0 / forall n, a <= x_ (u n).
  move=> gea_case.
  have [/= r r0 br_gea] := near_x_ge_a.
  have [/= N _ geN_Nr] := u_to0 _ (nbhsx_ballx 0 r r0).
  rewrite -(cvg_shiftn N).
  apply: gea_case.
  - by move=> ?; exact: u_gt0.
  - by rewrite cvg_shiftn.
  - move=> n.
    apply: br_gea => //.
    apply: geN_Nr => /=.
    exact: leq_addl.
wlog y_u_leb : u u_gt0 u_to0 x_u_gea / forall n, y_ (u n) <= b.
  move=> leb_case.
  have [/= r r0 br_leb] := near_y_le_b.
  have [/= N _ geN_Nr] := u_to0 _ (nbhsx_ballx 0 r r0).
  rewrite -(cvg_shiftn N).
  apply: leb_case.
  - by move=> ?; exact: u_gt0.
  - by rewrite cvg_shiftn.
  - by move=> ?; exact: x_u_gea. 
  - move=> n.
    apply: br_leb => //.
    apply: geN_Nr => /=.
    exact: leq_addl.
rewrite Rintegral_mkcond.
wlog suff patch_cvg : / 
    \int[mu]_z patch (f \_ `]x_ (u n), y_ (u n)[) [set x; y] 0 z 
    @[n --> \oo] --> \int[mu]_z patch (f \_ `]x, y[) [set x; y] 0 z.
  apply: cvg_trans; last apply: (cvg_to_eq patch_cvg).
  - apply: near_eq_cvg.
    near=> n.
    apply: Rintegral_patch_finite => //.
    apply: (iffLR (measurable_restrictT _ _)) => //.
    by apply: mf_oo.
  - apply: Rintegral_patch_finite => //.
    apply: (iffLR (measurable_restrictT _ _)) => //.
    by apply: mf_oo.
unshelve apply: Rdominated_cvg => /=.
- exact: (fun z => `|(f \_ `]a, b[) z|).
- by [].  
- move=> n.
  apply: (eq_measurable_fun ((f \_ `]x_ (u n), y_ (u n)[) \_ ~` [set x; y])).
    move=> z _ /=.
    by rewrite /patch /= /in_mem/= /in_set/= asbool_neg if_neg.
  have mxy : measurable (~` [set x; y]).
    apply: measurableC.
    by apply/measurableU.
  apply: (iffLR (measurable_restrictT _ _)) => //.
  apply/measurable_restrict => //.
  rewrite setIC -setDE.
  apply/measurable_EFinP.
  apply: (measurable_int mu).
  apply: integrableS f_int => //.
  + by apply: measurableI.
  + apply: subset_trans; first exact: subDsetl.
    by apply: subset_itvW.   
- move=> z _ /=.
  apply/cvgrPdist_lt => /= eps eps0.
  under eq_near => ?. 
    rewrite /patch in_setU !in_set1 !set_itvE /in_mem/= /in_set/= !asboolb.
    over.
  case: (ltgtP x z) => [x_lt_z|z_lt_x|_] /=; last first.
  + by apply: nearW; rewrite subrr normr0. 
  + near=> n.
    case: (eqVneq z y) => _; first by rewrite subrr normr0.
    rewrite ifN ?subrr ?normr0// negb_and -leNgt.
    apply/orP; left.
    near: n.
    apply: (cvgr_ge x) => //.
    move: u {u_gt0 u_to0 x_u_gea y_u_leb} (conj u_gt0 u_to0).
    by apply/cvg_at_rightP.
  case: (ltgtP z y) => [z_lt_y|y_lt_z|_]; last first.
  + by apply: nearW; rewrite subrr normr0.
  + near=> n.
    rewrite ifN ?subrr ?normr0// negb_and -!leNgt.
    apply/orP; right.
    near: n.
    apply: (cvgr_le y) => //.
    move: u {u_gt0 u_to0 x_u_gea y_u_leb} (conj u_gt0 u_to0).
    by apply/cvg_at_rightP.
  + near=> n.
    rewrite ifT ?subrr ?normr0//.
    apply/andP; split; near: n.
    * apply: (cvgr_lt x) => //.
      move: u {u_gt0 u_to0 x_u_gea y_u_leb} (conj u_gt0 u_to0).
      by apply/cvg_at_rightP.
    * apply: (cvgr_gt y) => //.
      move: u {u_gt0 u_to0 x_u_gea y_u_leb} (conj u_gt0 u_to0).
      by apply/cvg_at_rightP.
- apply: eq_integrable; first by [].
    move=> z _ /=.
    rewrite -abse_EFin.
    transitivity (`|((EFin \o f) \_ `]a, b[) z|%E) => //.
    by rewrite restrict_EFin.
  apply: integrable_abse.
  apply: (iffLR (integrable_mkcond _ _)) => //.
  apply: integrableS; last exact: f_int; [ exact: measurable_itv .. |].
  by apply: subset_itvW.
- move=> n z _ /=.
  rewrite /patch /point/=.
  case: (ifP (z \in `]a, b[%classic)) => [_|/negbT z_not_itv].
  + by repeat (case: ifP => _); rewrite ?normr0.
  + rewrite normr0 normr_le0; apply/eqP.
    case: ifP => // /negbT z_not_xy.
    rewrite ifN// notin_setE set_itvE/= => /andP[xu_lt_z z_lt_yu].
    move: z_not_itv => /negP; apply.
    rewrite inE/= in_itv/=.
    apply/andP; split.
    * by apply: le_lt_trans; last exact: xu_lt_z.
    * by apply: lt_le_trans; first exact: z_lt_yu.
Unshelve. all: by end_near. Qed.

End Rintegral_bound_continuity.

Section Rintegral_bound_infty_continuity.
Context (R : realType) (f : R -> R) (mu := @lebesgue_measure R).
Context (a x : R) (x_ : R -> R) (b1 b1' : bool).
Hypothesis f_int : 
  mu.-integrable [set` Interval (BSide b1 a) +oo%O] (EFin \o f).
Hypothesis a_le_x : a <= x.
Hypothesis near_x_ge_a : \forall e \near 0^'+, a <= x_ e.
Hypotheses cvg_x : x_ @ 0^'+ --> x.

Lemma Rintegral_bound_infty_continuous :
  \int[mu]_(z in [set` Interval (BSide b1 (x_ e)) +oo%O]) (f z)
  @[e --> 0^'+] --> \int[mu]_(z in [set` Interval (BSide b1' x) +oo%O]) (f z).
Proof.
near +oo_R => M.
apply: cvg_trans.
  apply: near_eq_cvg.
  near=> e.
  rewrite (Rintegral_itvDy (b := BRight M) b1 b1)// ?bnd_simp.
  - near: e.
    apply: (cvgr_le x) => //.
    near: M.
    apply: nbhs_pinfty_gt.
    exact: num_real.
  - apply: integrableS f_int => //.
    apply: subset_itvr.
    by near: e.
apply: cvg_to_eq.
  apply: cvgDr.
  apply: (@Rintegral_bound_continuous _ _ a M x M _ _ _ _ b1' false) => //. 
  - apply: integrableS f_int => //.
    by apply: subset_itvl.
  - by near=> y.
  - exact: cvg_cst.
transitivity (\int[mu]_(z in `]x, +oo[) f z).
  apply: Rintegral_itvby_itvoy.
  apply: (measurable_int mu).
  apply: integrableS f_int => //.
  by apply: subset_itvr.
rewrite (Rintegral_itvDy (b := BRight M) _ b1')// ?bnd_simp.
- near: M.
  apply: nbhs_pinfty_ge.
  exact: num_real.
- apply: integrableS f_int => //.
  by apply: subset_itvr.
Unshelve. all: by end_near. Qed.

End Rintegral_bound_infty_continuity.
