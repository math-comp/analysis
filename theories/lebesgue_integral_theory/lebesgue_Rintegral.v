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
(* This file recasts lemmas about `integral` to `Rintegral`. It also          *)
(* establishes that continuous functions are dense in $L^1$.                  *)
(*                                                                            *)
(* `Rintegral mu D f`                                                         *)
(* : Definition for `fine (\int[mu]_(x in D) f x)`                            *)
(*                                                                            *)
(* `measure_of_density mf f0`                                                 *)
(* : measure induced by `f : T -> R`                                          *)
(* : `f` is called the density of the induced measure                         *)
(* : `mf` is a proof that `f` is measurable and `f0`, a proof that it is      *)
(* : non-negative                                                             *)
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
  \int[mu]_(x in D) f x * r = (\int[mu]_(x in D) f x) * r.
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

Section semi_sigma_additive_measure_of_density.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Lemma semi_sigma_additive_measure_of_density (f : T -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x) ->
  semi_sigma_additive (fun A => \int[mu]_(t in A) f t).
Proof.
move=> mf f0 /= F mF tF mUF; rewrite ge0_integral_bigcup//=.
  exact: measurable_funTS.
by apply: is_cvg_ereal_nneg_natsum_cond => // n _ _; exact: integral_ge0.
Qed.

End semi_sigma_additive_measure_of_density.
#[deprecated(since="mathcomp-analysis 1.19.0", use=semi_sigma_additive_measure_of_density)]
Notation semi_sigma_additive_nng_induced := semi_sigma_additive_measure_of_density (only parsing).

Section measure_of_density_def.
Import MeasurableR.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}).

Definition measure_of_density (f : T -> R) (mf : measurable_fun [set: T] f)
    (f0 : forall x, 0 <= f x) :=
  fun A => (\int[mu]_(t in A) (f t)%:E)%E.

End measure_of_density_def.

(* NB: this does not rely on the Lebesgue measure, just on the Borel sigma-algebra *)
Section measure_of_density.
Import MeasurableR.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (f : T -> R).

Hypotheses (mf : measurable_fun [set: T] f) (f0 : forall x, (0 <= f x)%R).

Local Notation m' := (measure_of_density mu mf f0).

Let m'0 : m' set0 = 0. Proof. exact: integral_set0. Qed.

Let m'_ge0 A : (0 <= m' A)%E.
Proof. by apply: integral_ge0 => t At; rewrite lee_fin. Qed.

Let m'_semi_sigma_additive : semi_sigma_additive m'.
Proof.
by apply: semi_sigma_additive_measure_of_density => //; exact/measurable_EFinP.
Qed.

HB.instance Definition _ := isMeasure.Build d T R m'
  m'0 m'_ge0 m'_semi_sigma_additive.

End measure_of_density.

Section integral_measure_of_density.
Import MeasurableR.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (h : T -> R).

Hypothesis mh : measurable_fun [set: T] h.
Hypothesis h0 : forall x, (0 <= h x)%R.

Let mu' : {measure set _ -> \bar _} := measure_of_density mu mh h0.

#[local] Lemma integral_measure_of_density_indic (A : set T) : measurable A ->
  \int[mu]_x ((\1_A x)%:E * (h x)%:E) = mu' A.
Proof.
move=> mA; rewrite [RHS]integral_mkcond; apply: eq_integral => x _.
rewrite patchE indicE; case: ifP => _; first by rewrite mul1e.
by rewrite mul0e.
Qed.

#[local] Lemma integral_measure_of_densityMindic (r : R) (A : set T) : measurable A ->
  (0 <= r)%R ->
  \int[mu]_x (r%:E * (\1_A x)%:E * (h x)%:E) = r%:E * mu' A.
Proof.
move=> mA r0.
under eq_integral do rewrite -muleA.
rewrite ge0_integralZl//=.
- apply: emeasurable_funM => //; by apply /measurable_EFinP.
- by move=> x _; apply: mule_ge0; rewrite ?lee_fin.
- by rewrite integral_measure_of_density_indic.
Qed.

Import HBNNSimple.

#[local] Lemma sintegral_measure_of_density (g : {nnsfun T >-> R}) :
  sintegral mu' g = \int[mu]_x ((g x)%:E * (h x)%:E).
Proof.
transitivity (\sum_(r \in range g)
    \int[mu]_x (r%:E * (\1_(g @^-1` [set r]) x)%:E * (h x)%:E)).
  rewrite sintegralE; apply: eq_fsbigr => r /set_mem[x0 _ <-].
  by rewrite integral_measure_of_densityMindic.
transitivity (\int[mu]_x (\sum_(r \in range g)
    ((r * (\1_(g @^-1` [set r]) x))%:E * (h x)%:E))).
  rewrite ge0_integral_fsum//=.
  - move=> r.
    under eq_fun do rewrite EFinM -muleA.
    apply: measurable_funeM.
    by apply: emeasurable_funM => //; exact/measurable_EFinP.
  - move=> r x _; have [r0|r0] := leP 0%R r.
      by rewrite mule_ge0// lee_fin// mulr_ge0.
    by rewrite preimage_nnfun0// indic0/= mulr0 mul0e.
apply: eq_integral => x _.
rewrite -ge0_mule_fsuml; first by move=> _ [t _ <-]; rewrite lee_fin mulr_ge0.
by rewrite fsumEFin// [in RHS](fimfunE g).
Qed.

Lemma integral_measure_of_density (f : T -> \bar R) :
    measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  \int[mu']_x f x = \int[mu]_x (f x * (h x)%:E).
Proof.
move=> mf f0.
pose g := nnsfun_approx measurableT mf.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (EFin \o g n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n p / (n <= p)%O >-> n <= p}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n => \int[mu']_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[mu]_x (gE n x * (h x)%:E))).
  apply: congr_lim; apply/funext => n.
  by rewrite integralT_nnsfun sintegral_measure_of_density.
have mgEh n : measurable_fun [set: T] (fun x => gE n x * (h x)%:E).
  by apply: emeasurable_funM => //; exact/measurable_EFinP.
have gEh_ge0 n x : 0 <= gE n x * (h x)%:E by rewrite mule_ge0// lee_fin.
have nd_gEh x :
    {homo (fun n => gE n x * (h x)%:E) : n p / (n <= p)%O >-> n <= p}.
  by move=> p q pq; rewrite lee_wpmul2r ?lee_fin//; exact: nd_gE.
rewrite -monotone_convergence//.
apply: eq_integral => x _.
apply: cvg_lim => //; apply: cvgeZr => //.
exact: cvg_nnsfun_approx.
Qed.

End integral_measure_of_density.

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
