(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference topology ereal tvs normedtype.
From mathcomp Require Import sequences real_interval function_spaces esum.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import simple_functions measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.
From mathcomp Require Import lebesgue_integral_nonneg.

(**md**************************************************************************)
(* # Theory of Lebesgue-integrable functions                                  *)
(*                                                                            *)
(* This file contains a theory for Lebesgue-integrable functions: linearity,  *)
(* order, union, subset, etc. of the domain of integration.                   *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*     mu.-integrable D f == f is measurable over D and the integral of f     *)
(*                           w.r.t. D is < +oo                                *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "mu .-integrable" (at level 2, format "mu .-integrable").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.lock Definition integrable {d} {T : measurableType d} {R : realType}
    (mu : set T -> \bar R) D f :=
  `[< measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E >].
Canonical integrable_unlockable := Unlockable integrable.unlock.

Notation "mu .-integrable" := (integrable mu) : type_scope.

Lemma integrableP d T R mu D f :
  reflect (measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E)
    (@integrable d T R mu D f).
Proof. by rewrite unlock; apply/(iffP (asboolP _)). Qed.

Section negligible_integrable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}).

Lemma negligible_integrable (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  mu N = 0 -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> mN mD mf muN0.
pose mCN := measurableC mN.
have /integrableP intone : mu.-integrable D (f \_ N).
  apply/integrableP; split.
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  rewrite (eq_integral ((abse \o f) \_ N)); last first.
    by move=> t _; rewrite restrict_abse.
  rewrite -integral_mkcondr integral_abs_eq0//.
  - exact: measurableI.
  - exact: measurable_funS mf.
  - by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
have h1 : mu.-integrable D f <-> mu.-integrable D (f \_ (~` N)).
  split=> [/integrableP intf|/integrableP intCf].
    apply/integrableP; split.
      by apply/measurable_restrict => //; exact: measurable_funS mf.
    rewrite (eq_integral ((abse \o f) \_ (~` N))); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr; case: intf => _; apply: le_lt_trans.
    by apply: ge0_subset_integral => //=; [exact:measurableI|
                                           exact:measurableT_comp].
  apply/integrableP; split => //; rewrite (funID N f).
  have mDfcN : measurable_fun D (f \_ (~` N)).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  have mDfN : measurable_fun D (f \_ N).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  apply: (@le_lt_trans _ _
    (\int[mu]_(x in D) (`|(f \_ (~` N)) x| + `|(f \_ N) x|))).
    apply: ge0_le_integral => //.
    - by apply: measurableT_comp => //; exact: emeasurable_funD.
    - by apply: emeasurable_funD; exact: measurableT_comp.
    - by move=> *; rewrite lee_abs_add.
  rewrite ge0_integralD//; [|exact: measurableT_comp..].
  by apply: lte_add_pinfty; [case: intCf|case: intone].
suff : mu.-integrable D (f \_ (~` N)) <-> mu.-integrable (D `\` N) f.
  exact: iff_trans.
apply: iff_sym.
split=> [/integrableP intCf|/integrableP intCf]; apply/integrableP.
- split.
  + by apply/measurable_restrict => //; exact: measurable_funS mf.
  + rewrite (eq_integral ((abse \o f) \_ (~` N))); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr //; case: intCf => _; apply: le_lt_trans.
    apply: ge0_subset_integral => //=; [exact: measurableI|exact: measurableD|].
    by apply: measurableT_comp => //; apply: measurable_funS mf => // ? [].
- split.
  + move=> mDN A mA; rewrite setDE (setIC D) -setIA; apply: measurableI => //.
    exact: mf.
  + rewrite integral_mkcondr/=.
    under eq_integral do rewrite restrict_abse.
    by case: intCf.
Qed.

End negligible_integrable.

Lemma measurable_int d T R mu D f :
  @integrable d T R mu D f -> measurable_fun D f.
Proof. by rewrite unlock => /asboolP[]. Qed.
Arguments measurable_int {d T R} mu {D f}.

Section integrable_theory.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Implicit Type f g : T -> \bar R.

Notation mu_int := (integrable mu D).

Lemma integrable0 : mu_int (cst 0).
Proof.
apply/integrableP; split=> //; under eq_integral do rewrite (gee0_abs (lexx 0)).
by rewrite integral0.
Qed.

Lemma integrable_set0 f : mu.-integrable set0 f.
Proof.
apply/integrableP; split; first exact: measurable_fun_set0.
by rewrite integral_set0.
Qed.

Lemma eq_integrable f g : {in D, f =1 g} -> mu_int f -> mu_int g.
Proof.
move=> fg /integrableP[mf fi]; apply/integrableP; split.
  exact: eq_measurable_fun mf.
rewrite (le_lt_trans _ fi)//; apply: ge0_le_integral=> //.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
by move=> x Dx; rewrite fg// inE.
Qed.

Lemma le_integrable f g : measurable_fun D f ->
  (forall x, D x -> `|f x| <= `|g x|) -> mu_int g -> mu_int f.
Proof.
move=> mf fg /integrableP[mfg goo]; apply/integrableP; split => //.
by apply: le_lt_trans goo; apply: ge0_le_integral => //; exact: measurableT_comp.
Qed.

Lemma integrableN f : mu_int f -> mu_int (-%E \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split; last first.
  by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; exact: measurableT_comp.
Qed.

Lemma integrableZl (k : R) f : mu_int f -> mu_int (fun x => k%:E * f x).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurable_funeM.
under eq_fun do rewrite abseM.
by rewrite ge0_integralZl// ?lte_mul_pinfty//; exact: measurableT_comp.
Qed.

Lemma integrableZr (k : R) f : mu_int f -> mu_int (f \* cst k%:E).
Proof.
by move=> mf; apply: eq_integrable (integrableZl k mf) => // x; rewrite muleC.
Qed.

Lemma integrableD f g : mu_int f -> mu_int g -> mu_int (f \+ g).
Proof.
move=> /integrableP[mf foo] /integrableP[mg goo]; apply/integrableP; split.
  exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int[mu]_(x in D) (`|f x| + `|g x|))).
  apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; exact: emeasurable_funD.
  - by apply: emeasurable_funD; apply: measurableT_comp.
  - by move=> *; exact: lee_abs_add.
by rewrite ge0_integralD //; [exact: lte_add_pinfty| exact: measurableT_comp..].
Qed.

Lemma integrable_sum I (s : seq I) (P : pred I) (h : I -> T -> \bar R) :
  (forall i, P i -> mu_int (h i)) ->
  mu_int (fun x => \sum_(i <- s | P i) h i x).
Proof.
elim: s => [_|i s ih hs].
  by under eq_fun do rewrite big_nil; exact: integrable0.
under eq_fun do rewrite big_cons.
have [Pi|Pi] := boolP (P i); last exact: ih.
by apply: integrableD => //; [exact: hs|exact: ih].
Qed.

Lemma integrableB f g : mu_int f -> mu_int g -> mu_int (f \- g).
Proof. by move=> fi gi; exact/(integrableD fi)/integrableN. Qed.

Lemma integrable_add_def f : mu_int f ->
  \int[mu]_(x in D) f^\+ x +? - (\int[mu]_(x in D) f^\- x).
Proof.
move=> /integrableP[mf]; rewrite -[fun x => _]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
- exact: measurable_funepos.
- exact: measurable_funeneg.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite leeDl// integral_ge0.
- by rewrite inE (@le_lt_trans _ _ 0)// leeNl oppe0 integral_ge0.
Qed.

Lemma integrable_funepos f : mu_int f -> mu_int f^\+.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funepos.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funepos.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDl.
Qed.

Lemma integrable_funeneg f : mu_int f -> mu_int f^\-.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funeneg.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funeneg.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDr.
Qed.

Lemma integral_funeneg_lt_pinfty f : mu_int f -> \int[mu]_(x in D) f^\- x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funeneg.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funenegE.
    by move: fx0; rewrite -{1}oppe0 -leeNr => /max_idPl ->.
  rewrite gee0_abs// funenegE.
  by move: (fx0); rewrite -{1}oppe0 -leeNl => /max_idPr ->.
Qed.

Lemma integral_funepos_lt_pinfty f : mu_int f -> \int[mu]_(x in D) f^\+ x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funepos.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funeposE.
    by move: (fx0) => /max_idPr ->; rewrite -leeNr oppe0.
  by rewrite gee0_abs// funeposE; move: (fx0) => /max_idPl ->.
Qed.

Lemma integrable_neg_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\- x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funeneg.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDr.
Qed.

Lemma integrable_pos_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\+ x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funepos.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDl.
Qed.

Lemma integrableMr (h : T -> R) g :
  measurable_fun D h -> [bounded h x | x in D] ->
  mu_int g -> mu_int ((EFin \o h) \* g).
Proof.
move=> mh [M [Mreal Mh]] gi; apply/integrableP; split.
  by apply: emeasurable_funM => //; [exact: measurableT_comp|
                                     exact: measurable_int gi].
under eq_integral do rewrite abseM.
have: \int[mu]_(x in D) (`|M + 1|%:E * `|g x|) < +oo.
  rewrite ge0_integralZl ?lte_mul_pinfty//; first by case/integrableP : gi.
  by apply: measurableT_comp => //; exact: measurable_int gi.
apply/le_lt_trans/ge0_le_integral => //.
- apply/emeasurable_funM; last exact/measurableT_comp/(measurable_int _ gi).
  exact/measurable_EFinP/measurableT_comp.
- apply/emeasurable_funM => //; apply/measurableT_comp => //.
  exact: measurable_int gi.
- move=> x Dx; rewrite lee_wpmul2r//= lee_fin Mh//=.
  by rewrite (lt_le_trans _ (ler_norm _))// ltrDl.
Qed.

Lemma integrableMl f (h : T -> R) :
  mu_int f -> measurable_fun D h -> [bounded h x | x in D] ->
  mu_int (f \* (EFin \o h)).
Proof.
move=> fi mh mg; rewrite /is_true -(integrableMr mh mg fi).
by apply/congr1/funext => ?; rewrite muleC.
Qed.

Lemma integrable_restrict (E : set T) (mE : d.-measurable E) f :
  integrable mu (E `&` D) f <-> integrable mu E (f \_ D).
Proof.
split; move=> /integrableP[mf intfoo]; apply/integrableP; split.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
Qed.

Lemma le_integral f g : mu_int f -> mu_int g ->
  {in D, forall x, f x <= g x} -> \int[mu]_(x in D) f x <= \int[mu]_(x in D) g x.
Proof.
move=> intf intg fg; rewrite integralE [leRHS]integralE leeB//.
- apply: ge0_le_integral => //.
  + by move/integrableP : intf => [+ _]; exact: measurable_funepos.
  + by move/integrableP : intg => [+ _]; exact: measurable_funepos.
  + by move=> x /mem_set; exact: funepos_le.
- apply: ge0_le_integral => //.
  + by move/integrableP : intg => [+ _]; exact: measurable_funeneg.
  + by move/integrableP : intf => [+ _]; exact: measurable_funeneg.
  + by move=> x /mem_set; exact: funeneg_le.
Qed.

Lemma integrable_abse f : mu_int f -> mu_int (abse \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurableT_comp.
by under eq_integral do rewrite abse_id.
Qed.

End integrable_theory.
Arguments eq_integrable {d T R mu D} mD f.

Section measurable_bounded_integrable.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (D A B : set T) (f : T -> R).

Lemma measurable_bounded_integrable (f : T -> R) A (mA : measurable A) :
  (mu A < +oo)%E -> measurable_fun A f ->
  [bounded f x | x in A] -> mu.-integrable A (EFin \o f).
Proof.
move=> Afin mfA bdA; apply/integrableP; split; first exact/measurable_EFinP.
have [M [_ mrt]] := bdA; apply: le_lt_trans.
  apply: (integral_le_bound (`|M| + 1)%:E) => //; first exact: measurableT_comp.
  by apply: aeW => z Az; rewrite lee_fin mrt// ltr_pwDr// ler_norm.
by rewrite lte_mul_pinfty.
Qed.

End measurable_bounded_integrable.

Lemma integrable_indic_itv {R : realType} (a b : R) (b0 b1 : bool) :
  let mu := lebesgue_measure in
  mu.-integrable setT (EFin \o \1_[set` Interval (BSide b0 a) (BSide b1 b)]).
Proof.
have [ab|ba] := leP a b; last first.
  rewrite set_itv_ge//; first by rewrite indic0//; exact: integrable0.
  by rewrite -leNgt leBSide; move: b0 b1 => [] []//=; exact/ltW.
set i := [set` _]; rewrite (_ : _ \o _ = (cst 1%E) \_ i); last first.
  by apply/funext => r/=; rewrite indic_restrict restrict_EFin.
rewrite {}/i; apply/integrable_restrict => //=.
rewrite setTI; apply: measurable_bounded_integrable => //=.
  rewrite lebesgue_measure_itv//=.
  by case: ifPn => // _; rewrite -EFinB ltry.
exact: bounded_cst.
Qed.

Section integrable_finite_measure.
Context d (T : measurableType d) {R : realType}.
Variable mu : {finite_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integrable_indic A : measurable A ->
  mu.-integrable [set: T] (fun x : T => (\1_A x)%:E).
Proof.
move=> mA; apply/integrableP; split; first exact/measurable_EFinP.
rewrite (eq_integral (fun x => (\1_A x)%:E)); last first.
  by move=> t _; rewrite gee0_abs// lee_fin.
rewrite integral_indic// setIT.
rewrite (@le_lt_trans _ _ (mu setT)) ?le_measure ?inE//.
by rewrite ?ltry ?fin_num_fun_lty//; exact: fin_num_measure.
Qed.

Lemma finite_measure_integrable_cst A k :
  measurable A -> mu.-integrable A (EFin \o cst k).
Proof.
move=> mA; apply/integrableP; split; first exact/measurable_EFinP.
have [k0|k0] := leP 0%R k.
- under eq_integral do rewrite /= ger0_norm//.
  rewrite lebesgue_integral_nonneg.integral_cstr//= lte_mul_pinfty//.
  by rewrite -ge0_fin_numE// fin_num_measure.
- under eq_integral do rewrite /= ltr0_norm//.
  rewrite lebesgue_integral_nonneg.integral_cstr//= lte_mul_pinfty//.
    by rewrite lee_fin lerNr oppr0 ltW.
  by rewrite -ge0_fin_numE// fin_num_measure.
Qed.

End integrable_finite_measure.

Section integrable_domain.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integrableS (E D : set T) (f : T -> \bar R) :
  measurable E -> measurable D -> D `<=` E ->
  mu.-integrable E f -> mu.-integrable D f.
Proof.
move=> mE mD DE /integrableP[mf ifoo]; apply/integrableP; split.
  exact: measurable_funS mf.
apply: le_lt_trans ifoo; apply: ge0_subset_integral => //.
exact: measurableT_comp.
Qed.

Lemma integrable_mkcond D f : measurable D ->
  mu.-integrable D f <-> mu.-integrable setT (f \_ D).
Proof.
move=> mD.
rewrite unlock; apply: asbool_equiv; rewrite [in X in X <-> _]integral_mkcond.
under [in X in X <-> _]eq_integral do rewrite restrict_abse.
split => [|] [mf foo].
- by split; [exact/(measurable_restrictT _ _).1| exact: le_lt_trans foo].
- by split; [exact/(measurable_restrictT _ _).2| exact: le_lt_trans foo].
Qed.

End integrable_domain.
Arguments integrable_mkcond {d T R mu D} f.

Section integrable_ae.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : T -> \bar R.
Hypotheses fint : mu.-integrable D f.

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite (_ : E = D `&` f @^-1` [set -oo; +oo]).
    by apply: (measurable_int _ fint) => //; exact: measurableU.
  rewrite /E predeqE => t; split=> [[/eqP]|[Dt [|]/= ->//]].
  by rewrite eqe_absl leey andbT /preimage/= => /orP[|]/eqP; tauto.
have [ET|ET] := eqVneq E setT.
  have foo t : `|f t| = +oo by have [] : E t by rewrite ET.
  suff: \int[mu]_(x in D) `|f x| = +oo.
    by case: (integrableP _ _ _ fint) => _; rewrite ltey => /eqP.
  by rewrite -(lebesgue_integral_nonneg.integral_csty mD muD0)//; exact: eq_integral.
suff: mu E = 0.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt].
  by rewrite fin_num_abs => /negP; rewrite -leNgt leye_eq => /eqP.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M M0 muM] : exists2 M, (0 <= M)%R &
    forall n, n%:R%:E * mu (E `&` D) <= M%:E.
  exists (fine (\int[mu]_(x in D) `|f x|)); first exact/fine_ge0/integral_ge0.
  move=> n; rewrite -integral_indic// -ge0_integralZl//; last first.
    exact: measurableT_comp.
  rewrite fineK//; last first.
    case: (integrableP _ _ _ fint) => _ foo.
    by rewrite ge0_fin_numE// integral_ge0.
  apply: ge0_le_integral => //.
  - exact/measurable_EFinP/measurableT_comp.
  - by apply: measurableT_comp => //; exact: measurable_int fint.
  - move=> x Dx; rewrite /= indicE.
    have [|xE] := boolP (x \in E); last by rewrite mule0.
    by rewrite /E inE /= => -[->]; rewrite leey.
apply/eqP/negPn/negP => /eqP muED0; move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite leye_eq => /eqP ->; exists 1%N; rewrite mul1e leye_eq.
exists (truncn (M * (fine (mu (E `&` D)))^-1)).+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  by rewrite fin_numElt muEDoo (lt_le_trans _ (measure_ge0 _ _)).
rewrite lte_fin -ltr_pdivrMr; first by rewrite truncnS_gt.
rewrite -lte_fin fineK.
  rewrite lt0e measure_ge0 andbT.
  suff: E `&` D = E by move=> ->; exact/eqP.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section integralZl.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Let mesf : measurable_fun D f. Proof. exact: measurable_int intf. Qed.

Lemma integralZl r :
  \int[mu]_(x in D) (r%:E * f x) = r%:E * \int[mu]_(x in D) f x.
Proof.
have /orP[r0|r0] := le_total r 0%R.
- rewrite [in LHS]integralE// le0_funeposM// le0_funenegM//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _)) ?oppr_ge0//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _)) ?oppr_ge0//.
  rewrite !EFinN addeC !mulNe oppeK -muleBr ?integrable_add_def//.
  by rewrite [in RHS]integralE.
- rewrite [in LHS]integralE// ge0_funeposM// ge0_funenegM//=.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _) r0)//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _) r0)//.
  by rewrite -muleBr 1?[in RHS]integralE// integrable_add_def.
Qed.

Lemma integralZr r :
  \int[mu]_(x in D) (f x * r%:E) = (\int[mu]_(x in D) f x) * r%:E.
Proof. by rewrite muleC -integralZl; under eq_integral do rewrite muleC. Qed.

End integralZl.

Section integralD_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> R.
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : mu.-integrable D g1.
Hypothesis if2 : mu.-integrable D g2.

Let mf1 : measurable_fun D g1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D g2. Proof. exact: measurable_int if2. Qed.

Lemma integralD_EFin :
  \int[mu]_(x in D) (g1 \+ g2) x =
  \int[mu]_(x in D) g1 x + \int[mu]_(x in D) g2 x.
Proof.
suff: \int[mu]_(x in D) ((g1 \+ g2)^\+ x) + \int[mu]_(x in D) (g1^\- x) +
        \int[mu]_(x in D) (g2^\- x) =
      \int[mu]_(x in D) ((g1 \+ g2)^\- x) + \int[mu]_(x in D) (g1^\+ x) +
        \int[mu]_(x in D) (g2^\+ x).
  move=> h; rewrite [in LHS]integralE.
  move/eqP : h; rewrite -[in eqbRHS]addeA [in eqbRHS]addeC.
  have g12pos :
      \int[mu]_(x in D) (g1^\+ x) + \int[mu]_(x in D) (g2^\+ x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funepos_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  have g12neg :
      \int[mu]_(x in D) (g1^\- x) + \int[mu]_(x in D) (g2^\- x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty// ; exact: integral_funeneg_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        exact: integral_funepos_lt_pinfty (integrableD _ _ _).
      apply: adde_ge0; last exact: integral_ge0.
      by apply: adde_ge0; apply: integral_ge0.
    - exact/fin_num_adde_defr/g12pos.
  rewrite -[X in X - _ == _]addeA [X in X - _ == _]addeC -[eqbLHS]addeA.
  rewrite [eqbLHS]addeC eq_sym.
  rewrite -(sube_eq g12pos) ?fin_num_adde_defl// => /eqP g12E.
  rewrite -{}[LHS]g12E fin_num_oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funeneg_lt_pinfty if2.
    exact: integral_ge0.
  by rewrite addeACA (integralE _ _ g1) (integralE _ _ g2).
have : (g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in eqbRHS]addeC -sube_eq; last 2 first.
    by rewrite funeposE !funenegE -!fine_max.
    by rewrite !funeposE funenegE -!fine_max.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite !funeposE -!fine_max.
    by rewrite funeposE !funenegE -!fine_max.
  apply/eqP.
  rewrite -[LHS]/((g1^\+ \+ g2^\+ \- (g1^\- \+ g2^\-)) x) -funeD_posD.
  by rewrite -[RHS]/((_ \- _) x) -funeD_Dpos.
move/(congr1 (fun y => \int[mu]_(x in D) (y x) )).
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funeneg.
    exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact: measurable_funeneg.
rewrite (ge0_integralD mu mD); last 4 first.
  - by [].
  - exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact/measurable_funeneg.
move=> g12E; rewrite {}[LHS]g12E.
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; exact: adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funepos.
    exact/measurable_funeneg/emeasurable_funD.
  - by [].
  - exact: measurable_funepos.
rewrite (ge0_integralD mu mD) //; last exact: measurable_funepos.
exact/measurable_funeneg/emeasurable_funD.
Qed.

End integralD_EFin.

Lemma integralB_EFin d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R)
  (mD : measurable D) :
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  (\int[mu]_(x in D) ((f1 x)%:E - (f2 x)%:E) =
    (\int[mu]_(x in D) (f1 x)%:E - \int[mu]_(x in D) (f2 x)%:E))%E.
Proof.
move=> if1 if2; rewrite (integralD_EFin mD if1); last first.
  by rewrite (_ : _ \o _ = (fun x => - (f2 x)%:E))%E; [exact: integrableN|by []].
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Section integralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> \bar R.
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Let mf1 : measurable_fun D f1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D f2. Proof. exact: measurable_int if2. Qed.

Lemma integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
pose A := D `&` [set x | f1 x \is a fin_num].
pose B := D `&` [set x | f2 x \is a fin_num].
have mA : measurable A by exact: emeasurable_fin_num.
have mB : measurable B by exact: emeasurable_fin_num.
have mAB : measurable (A `&` B) by apply: measurableI.
pose g1 := (fine \o f1 \_ (A `&` B))%R.
pose g2 := (fine \o f2 \_ (A `&` B))%R.
have ig1 : mu.-integrable D (EFin \o g1).
  rewrite (_ : _ \o _ = f1 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if1=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g1 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite 2!in_setI => /andP[/andP[xA f1xfin] _] /=.
  by rewrite fineK//; rewrite inE in f1xfin.
have mg1 := measurable_int _ ig1.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if2=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g2 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite in_setI => /andP[_]; rewrite in_setI => /andP[xB f2xfin] /=.
  by rewrite fineK//; rewrite inE in f2xfin.
have mg2 := measurable_int _ ig2.
transitivity (\int[mu]_(x in D) (EFin \o (g1 \+ g2)%R) x).
  apply: ae_eq_integral => //.
  - exact: emeasurable_funD.
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    exact: emeasurable_funD.
  - apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=.
    rewrite EFinD /g1 /g2 /restrict /=; have [|] := boolP (x \in A `&` B).
      by rewrite in_setI => /andP[xA xB] /=; rewrite !fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx)/= notin_setE/=.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// integralD_EFin//.
  congr (_ + _); apply: ae_eq_integral => //.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g1 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE/=.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g2 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE.
Qed.

End integralD.

Section integral_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis intf : forall n, mu.-integrable D (f n).

Lemma integral_sum (s : seq I) (P : pred I) :
  \int[mu]_(x in D) (\sum_(k <- s | P k) f k x) =
  \sum_(k <- s | P k) \int[mu]_(x in D) (f k x).
Proof.
elim: s => [|h t ih].
  under eq_integral do rewrite big_nil.
  by rewrite integral0 big_nil.
rewrite big_cons -ih -integralD//; last exact: integrable_sum.
case: ifPn => Ph.
  by apply: eq_integral => x xD; rewrite big_cons Ph.
by apply: eq_integral => x xD; rewrite big_cons/= (negbTE Ph).
Qed.

End integral_sum.

Section integralB.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralB : \int[mu]_(x in D) (f1 \- f2) x =
                  \int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x.
Proof.
rewrite -[in RHS](@integralN _ _ _ _ _ f2); last exact: integrable_add_def.
by rewrite -[in RHS]integralD//; exact: integrableN.
Qed.

End integralB.

Section integrable_lty_fin_num.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Local Open Scope ereal_scope.

Lemma integrable_lty (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x < +oo.
Proof.
move=> intf; rewrite (funeposneg f) integralB//;
  [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite lte_add_pinfty ?integral_funepos_lt_pinfty// lteNl ltNye_eq.
by rewrite integrable_neg_fin_num.
Qed.

Lemma integrable_fin_num (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x \is a fin_num.
Proof.
move=> h; apply/fin_numPlt; rewrite integrable_lty// andbC/= -/(- +oo).
rewrite lteNl -integralN; first exact/integrable_lty/integrableN.
by rewrite fin_num_adde_defl// fin_numN integrable_neg_fin_num.
Qed.

End integrable_lty_fin_num.
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `integrable_lty`")]
Notation integral_fune_lt_pinfty := integrable_lty (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `integrable_fin_num`")]
Notation integral_fune_fin_num := integrable_fin_num (only parsing).

Section transfer.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variable phi : X -> Y.
Hypothesis mphi : measurable_fun [set: X] phi.
Variable mu : {measure set X -> \bar R}.
Variables D : set Y.
Variables f : Y -> \bar R.
Hypotheses (mf : measurable_fun [set: Y] f)
  (intf : mu.-integrable (phi @^-1` D) (f \o phi)).
Let mf_mixin := isMeasurableFun.Build _ _ _ _ _ mf.
Let mf_pack := MeasurableFun.Pack (MeasurableFun.Class mf_mixin).

Lemma integrable_pushforward :
  measurable D -> (pushforward mu phi).-integrable D f.
Proof.
move=> mD; apply/integrableP; split; first exact: (measurable_funP mf_pack).
move/integrableP : (intf) => [_]; apply: le_lt_trans.
rewrite ge0_integral_pushforward//.
by apply: measurableT_comp => //; exact: measurable_funTS.
Qed.

Local Open Scope ereal_scope.

Lemma integral_pushforward : measurable D ->
  \int[pushforward mu phi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD.
rewrite [RHS]integralE.
under [X in X - _]eq_integral do rewrite funepos_comp/=.
under [X in _ - X]eq_integral do rewrite funeneg_comp.
rewrite -[X in _ = X - _]ge0_integral_pushforward//; last first.
  exact/measurable_funepos/measurable_funTS.
rewrite -[X in _ = _ - X]ge0_integral_pushforward//; last first.
  exact/measurable_funeneg/measurable_funTS.
rewrite -integralB//=; last first.
- by apply: integrable_funeneg => //=; exact: integrable_pushforward.
- by apply: integrable_funepos => //=; exact: integrable_pushforward.
- by apply/eq_integral=> // x _; rewrite /= [in LHS](funeposneg f).
Qed.

End transfer.

Section negligible_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> mu.-integrable D f ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf muN0; rewrite [f]funeposneg ?integralB //; first last.
- exact: integrable_funeneg.
- exact: integrable_funepos.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funeneg.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funepos.
- exact: measurableD.
congr (_ - _); apply: ge0_negligible_integral => //; apply: (measurable_int mu).
  exact: integrable_funepos.
exact: integrable_funeneg.
Qed.

Lemma null_set_integrable (N : set T) (f : T -> \bar R) :
  measurable N -> measurable_fun N f -> mu N = 0 -> mu.-integrable N f.
Proof.
move=> mN mf muN0.
by rewrite (negligible_integrable mN) ?setDv//; exact: integrable_set0.
Qed.

Lemma null_set_integral (N : set T) (f : T -> \bar R) :
  measurable N -> measurable_fun N f -> mu N = 0 -> \int[mu]_(x in N) f x = 0.
Proof.
move=> mN mf N0.
rewrite (negligible_integral mN mN) ?setDv ?integral_set0//.
exact: null_set_integrable.
Qed.

End negligible_integral.
Add Search Blacklist "ge0_negligible_integral".

Section integral_measure_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (m1 m2 : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Variable f : T -> \bar R.
Hypothesis intf1 : m1.-integrable D f.
Hypothesis intf2 : m2.-integrable D f.
Hypothesis mf : measurable_fun D f.

Lemma integral_measure_add : \int[measure_add m1 m2]_(x in D) f x =
  \int[m1]_(x in D) f x + \int[m2]_(x in D) f x.
Proof.
transitivity (\int[m1]_(x in D) (f^\+ \- f^\-) x +
              \int[m2]_(x in D) (f^\+ \- f^\-) x); last first.
  by congr +%E; apply: eq_integral => x _; rewrite [in RHS](funeposneg f).
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite addeACA -ge0_integral_measure_add//; last first.
  by apply: measurable_funepos; exact: measurable_int intf1.
rewrite -oppeD; last by rewrite ge0_adde_def// inE integral_ge0.
rewrite -ge0_integral_measure_add// 1?integralE//.
by apply: measurable_funeneg; exact: measurable_int intf1.
Qed.

End integral_measure_add.

Section subadditive_countable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integrable_summable (F : (set T)^nat) (g : T -> \bar R):
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  summable [set: nat] (fun i => \int[mu]_(x in F i) g x).
Proof.
move=> tF mF fi.
rewrite /summable -(_ : [set _ | true] = setT); last exact/seteqP.
rewrite -nneseries_esum//.
have [mf {fi}] := integrableP _ _ _ fi.
rewrite ge0_integral_bigcup//; last exact: measurableT_comp.
apply: le_lt_trans; apply: lee_lim.
- exact: is_cvg_ereal_nneg_natsum_cond.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ _; exact: integral_ge0.
- apply: nearW => n; apply: lee_sum => m _; apply: le_abse_integral => //.
  apply: measurable_funS mf => //; [exact: bigcup_measurable|].
  exact: bigcup_sup.
Qed.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int[mu]_(x in \bigcup_i F i) g x = \sum_(i <oo) \int[mu]_(x in F i) g x)%E.
Proof.
move=> tF mF fi.
have ? : \int[mu]_(x in \bigcup_i F i) g x \is a fin_num.
  rewrite fin_numElt -(lte_absl _ +oo).
  apply: le_lt_trans (integrableP _ _ _ fi).2; apply: le_abse_integral => //.
    exact: bigcupT_measurable.
  exact: measurable_int fi.
transitivity (\int[mu]_(x in \bigcup_i F i) g^\+ x -
              \int[mu]_(x in \bigcup_i F i) g^\- x)%E.
  rewrite -integralB.
  - by apply: eq_integral => t Ft; rewrite [in LHS](funeposneg g).
  - exact: bigcupT_measurable.
  - by apply: integrable_funepos => //; exact: bigcupT_measurable.
  - by apply: integrable_funeneg => //; exact: bigcupT_measurable.
transitivity (\sum_(i <oo) (\int[mu]_(x in F i) g^\+ x -
                            \int[mu]_(x in F i) g^\- x)); last first.
  by apply: eq_eseriesr => // i; rewrite [RHS]integralE.
transitivity ((\sum_(i <oo) \int[mu]_(x in F i) g^\+ x) -
              (\sum_(i <oo) \int[mu]_(x in F i) g^\- x))%E.
  rewrite ge0_integral_bigcup//; last first.
    by apply: measurable_funepos; case/integrableP : fi.
  rewrite ge0_integral_bigcup//.
  by apply: measurable_funeneg; case/integrableP : fi.
rewrite [X in X - _]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite [X in _ - X]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite set_true -esumB//=; last 4 first.
  - apply: integrable_summable => //; apply: integrable_funepos => //.
    exact: bigcup_measurable.
  - apply: integrable_summable => //; apply: integrable_funeneg => //.
    exact: bigcup_measurable.
  - by move=> n _; exact: integral_ge0.
  - by move=> n _; exact: integral_ge0.
rewrite summable_eseries; last first.
  under [X in summable _ X]eq_fun do rewrite -integralE.
  by rewrite fun_true; exact: integrable_summable.
by congr (_ - _)%E; rewrite nneseries_esum// set_true.
Qed.

End subadditive_countable.

Section sequence_of_measures.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Lemma integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall n, integrable (m_ n) D f) ->
  measurable_fun D f ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x | < +oo%E ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x | < +oo%E ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> fi mf fmoo fpoo; rewrite integralE.
rewrite ge0_integral_measure_series//; last exact/measurable_funepos.
rewrite ge0_integral_measure_series//; last exact/measurable_funeneg.
transitivity (\sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\+ x)%E)%:E -
              \sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\- x))%:E).
  by congr (_ - _); apply: eq_eseriesr => n _; rewrite fineK//;
    [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
have fineKn : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_neg_fin_num.
have fineKp : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_pos_fin_num.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -esumB//; last 4 first.
  - by rewrite /= /summable -nneseries_esum// -fineKp.
  - by rewrite /summable /= -nneseries_esum// -fineKn; exact: fmoo.
  - by move=> n _; exact/fine_ge0/integral_ge0.
  - by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -summable_eseries_esum; last first.
  apply: (@le_lt_trans _ _ (\esum_(i in (fun=> true))
     `|(fine (\int[m_ i]_(x in D) f x))%:E|)).
    by apply: le_esum => k _; rewrite -EFinB -fineB// -?integralE//;
      [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
  rewrite -nneseries_esum; last by [].
  apply: (@le_lt_trans _ _
      (\sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E| +
       \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|)).
    rewrite -nneseriesD//; apply: lee_nneseries => // n _.
    rewrite integralE fineB// ?EFinB.
    - exact: (le_trans (lee_abs_sub _ _)).
    - exact: integrable_pos_fin_num.
    - exact: integrable_neg_fin_num.
  apply: lte_add_pinfty; first by rewrite -fineKp.
  by rewrite -fineKn; exact: fmoo.
by apply: eq_eseriesr => k _; rewrite !fineK// -?integralE//;
  [exact: integrable_neg_fin_num|exact: integrable_pos_fin_num].
Qed.

End sequence_of_measures.

Section integral_counting.
Local Open Scope ereal_scope.
Variable R : realType.

Lemma integral_count (a : nat -> \bar R) : summable setT a ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
- by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
- move=> n; apply/integrableP; split=> [//|].
  by rewrite integral_dirac//= diracT mul1e (summable_pinfty sa).
- by apply: summable_integral_dirac => //; exact: summable_funeneg.
- by apply: summable_integral_dirac => //; exact: summable_funepos.
Qed.

End integral_counting.

Section integral_ae_eq.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Let integral_measure_lt (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  mu (D `&` [set x | g x < f x]) = 0.
Proof.
move=> itf itg fg; pose E j := D `&` [set x | f x - g x >= j.+1%:R^-1%:E].
have msf := measurable_int _ itf.
have msg := measurable_int _ itg.
have mE j : measurable (E j).
  rewrite /E; apply: measurable_lee => //.
  by apply/(emeasurable_funD msf)/measurableT_comp => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite -measure_le0.
  have fg0 : \int[mu]_(x in E j) (f \- g) x = 0.
    rewrite integralB//; last 2 first.
      by apply: integrableS itf => //; exact: subIsetl.
      by apply: integrableS itg => //; exact: subIsetl.
    rewrite fg//; last apply: subIsetl.
    rewrite subee// fin_num_abs (le_lt_trans (le_abse_integral _ _ _))//.
      by apply: measurable_funS msg => //; first exact: subIsetl.
    apply: le_lt_trans (integrableP _ _ _ itg).2.
    apply: ge0_subset_integral => //; first exact: measurableT_comp msg.
    exact: subIsetl.
  suff : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    by rewrite fg0 mule0.
  apply: (@le_trans _ _ (j.+1%:R%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)).
    by rewrite integral_cst// muleA -EFinM divff// mul1e.
  rewrite lee_pmul//; first exact: integral_ge0.
  apply: ge0_le_integral => //; last by move=> x [].
  apply: emeasurable_funB.
  - by apply: measurable_funS msf => //; exact: subIsetl.
  - by apply: measurable_funS msg => //; exact: subIsetl.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x [Dx /= ifg]; split => //.
  by move: ifg; apply: le_trans; rewrite lee_fin lef_pV2// ?posrE// ler_nat.
rewrite set_lte_bigcup.
have /cvg_lim h1 : (mu \o E) x @[x --> \oo]--> 0.
  by apply: cvg_near_cst; exact: nearW.
have := @nondecreasing_cvg_mu _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
by move/cvg_lim => h2; rewrite setI_bigcupr -h2// h1.
Qed.

Lemma integral_ae_eq (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> measurable_fun D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  ae_eq mu D f g.
Proof.
move=> fi mg fg; have mf := measurable_int _ fi; have gi : mu.-integrable D g.
  apply/integrableP; split => //; apply/abse_integralP => //; rewrite -fg//.
  by apply/abse_integralP => //; case/integrableP : fi.
have mugf : mu (D `&` [set x | g x < f x]) = 0 by apply: integral_measure_lt.
have mufg : mu (D `&` [set x | f x < g x]) = 0.
  by apply: integral_measure_lt => // E ED mE; rewrite fg.
have h : ~` [set x | D x -> f x = g x] = D `&` [set x | f x != g x].
  apply/seteqP; split => [x/= /not_implyP[? /eqP]//|x/= [Dx fgx]].
  by apply/not_implyP; split => //; exact/eqP.
apply/negligibleP; first by rewrite h; apply: measurable_neqe.
rewrite h set_neq_lt setIUr measureU//; [|exact: measurable_lte..|].
- by rewrite [X in X + _]mufg add0e [LHS]mugf.
- apply/seteqP; split => [x [[Dx/= + [_]]]|//].
  by move=> /lt_trans => /[apply]; rewrite ltxx.
Qed.

End integral_ae_eq.
