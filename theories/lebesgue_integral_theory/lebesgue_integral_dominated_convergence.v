(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import function_spaces esum measure lebesgue_measure.
From mathcomp Require Import numfun realfun simple_functions.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_properties.

(**md**************************************************************************)
(* # Dominated Convergence Theorem for the Lebesgue Integral                  *)
(*                                                                            *)
(* This file contains a formalization of the dominated convergence theorem    *)
(* for the Lebesgue integral.                                                 *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section dominated_convergence_lemma.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f_ : (T -> \bar R)^nat) (f : T -> \bar R) (g : T -> \bar R).
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Hypothesis f_f : forall x, D x -> f_ ^~ x @ \oo --> f x.
Hypothesis fing : forall x, D x -> g x \is a fin_num.
Hypothesis ig : mu.-integrable D g.
Hypothesis absfg : forall n x, D x -> `|f_ n x| <= g x.

Let g0 x : D x -> 0 <= g x.
Proof. by move=> Dx; rewrite (le_trans _ (@absfg O _ Dx))// lee_fin. Qed.

Let mf : measurable_fun D f.
Proof. exact: (emeasurable_fun_cvg _ _ mf_ f_f). Qed.

Local Lemma dominated_integrable : mu.-integrable D f.
Proof.
apply/integrableP; split => //; have Dfg x : D x -> `| f x | <= g x.
  move=> Dx; have /(@cvg_lim _) <- // : `|f_ n x| @[n --> \oo] --> `|f x|.
    by apply: cvg_abse => //; exact: f_f.
  apply: lime_le => //.
  - by apply: is_cvg_abse; apply/cvg_ex; eexists; exact: f_f.
  - by apply: nearW => n; exact: absfg.
move: ig => /integrableP[mg]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurableT_comp.
- exact: measurableT_comp.
- by move=> x Dx /=; rewrite (gee0_abs (g0 Dx)); exact: Dfg.
Qed.

Let g_ n x := `|f_ n x - f x|.

Let cvg_g_ x : D x -> g_ ^~ x @ \oo --> 0.
Proof.
move=> Dx; rewrite -abse0; apply: cvg_abse.
move: (f_f Dx); case: (f x) => [r|/=|/=].
- by move=> f_r; exact/sube_cvg0.
- move/cvgeyPge/(_ (fine (g x) + 1)%R) => [n _]/(_ _ (leqnn n))/= h.
  have : (fine (g x) + 1)%:E <= g x.
    by rewrite (le_trans h)// (le_trans _ (absfg n Dx))// lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lteDl ?lte01.
- move/cvgeNyPle/(_ (- (fine (g x) + 1))%R) => [n _]/(_ _ (leqnn n)) h.
  have : (fine (g x) + 1)%:E <= g x.
    move: h; rewrite EFinN leeNr => /le_trans ->//.
    by rewrite (le_trans _ (absfg n Dx))// -abseN lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lteDl ?lte01.
Qed.

Let gg_ n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof.
move=> Dx; rewrite subre_ge0; last by rewrite fin_numM// fing.
rewrite -(fineK (fing Dx)) -EFinM mulr_natl mulr2n /g_.
rewrite (le_trans (lee_abs_sub _ _))// [in leRHS]EFinD leeD//.
  by rewrite fineK// ?fing// absfg.
have f_fx : `|(f_ n x)| @[n --> \oo] --> `|f x| by apply: cvg_abse; exact: f_f.
move/cvg_lim : (f_fx) => <-//.
apply: lime_le; first by apply/cvg_ex; eexists; exact: f_fx.
by apply: nearW => k; rewrite fineK ?fing//; apply: absfg.
Qed.

Let mgg n : measurable_fun D (fun x => 2%:E * g x - g_ n x).
Proof.
apply/emeasurable_funB => //; [by apply/measurable_funeM/(measurable_int _ ig)|].
by apply/measurableT_comp => //; exact: emeasurable_funB.
Qed.

Let gg_ge0 n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof. by move=> Dx; rewrite gg_. Qed.

Local Lemma dominated_cvg0 : [sequence \int[mu]_(x in D) g_ n x]_n @ \oo --> 0.
Proof.
have := fatou mu mD mgg gg_ge0.
rewrite [X in X <= _ -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x) ); last first.
  apply: eq_integral => t; rewrite inE => Dt.
  rewrite limn_einf_shift//; last by rewrite fin_numM// fing.
  rewrite is_cvg_limn_einfE//; last first.
    by apply: is_cvgeN; apply/cvg_ex; eexists; exact: cvg_g_.
  rewrite [X in _ + X](_ : _ = 0) ?adde0//; apply/cvg_lim => //.
  by rewrite -oppe0; apply: cvgeN; exact: cvg_g_.
have i2g : \int[mu]_(x in D) (2%:E * g x)  < +oo.
rewrite integralZl// lte_mul_pinfty// ?lee_fin//; case: (integrableP _ _ _ ig) => _.
  apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => t Dt; rewrite gee0_abs// g0//; rewrite inE in Dt.
have ? : \int[mu]_(x in D) (2%:E * g x)  \is a fin_num.
  by rewrite ge0_fin_numE// integral_ge0// => ? ?; rewrite mule_ge0 ?lee_fin ?g0.
rewrite [X in _ <= X -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x)  + -
    limn_esup (fun n => \int[mu]_(x in D) g_ n x)); last first.
  rewrite (_ : (fun _ => _) = (fun n => \int[mu]_(x in D) (2%:E * g x)  +
      \int[mu]_(x in D) - g_ n x)); last first.
    rewrite funeqE => n; rewrite integralB//.
    - by rewrite -integral_ge0N// => x Dx//; rewrite /g_.
    - exact: integrableZl.
    - have integrable_normfn : mu.-integrable D (abse \o f_ n).
        apply: le_integrable ig => //; first exact: measurableT_comp.
        by move=> x Dx /=; rewrite abse_id (le_trans (absfg _ Dx))// lee_abs.
      suff: mu.-integrable D (fun x => `|f_ n x| + `|f x|).
        apply: le_integrable => //.
        - by apply: measurableT_comp => //; exact: emeasurable_funB.
        - move=> x Dx.
          by rewrite /g_ abse_id (le_trans (lee_abs_sub _ _))// lee_abs.
      apply: integrableD; [by []| by []|].
      apply: le_integrable dominated_integrable => //.
      - exact: measurableT_comp.
      - by move=> x Dx; rewrite /= abse_id.
  rewrite limn_einf_shift // -limn_einfN; congr (_ + limn_einf _).
  by rewrite funeqE => n /=; rewrite -integral_ge0N// => x Dx; rewrite /g_.
rewrite addeC -leeBlDr// subee// leeNr oppe0 => lim_ge0.
by apply/limn_esup_le_cvg => // n; rewrite integral_ge0// => x _; rewrite /g_.
Qed.

Lemma dominated_cvg :
  \int[mu]_(x in D) f_ n x @[n \oo] --> \int[mu]_(x in D) f x.
Proof.
have h n : `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x |
    <= \int[mu]_(x in D) g_ n x.
  rewrite -(integralB _ _ dominated_integrable)//; last first.
    by apply: le_integrable ig => // x Dx /=; rewrite (gee0_abs (g0 Dx)) absfg.
  by apply: le_abse_integral => //; exact: emeasurable_funB.
suff: `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x | @[n \oo] --> 0.
   move/cvg_abse0P/sube_cvg0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   move: dominated_integrable => /integrableP[?]; apply: le_lt_trans.
   by apply: (le_trans _ (@le_abse_integral _ _ _ mu D f mD _)).
apply: (@squeeze_cvge _ _ _ _ (cst 0) _ (fun n => \int[mu]_(x in D) g_ n x)).
- by apply: nearW => n; rewrite abse_ge0//=; exact: h.
- exact: cvg_cst.
- exact: dominated_cvg0.
Qed.

End dominated_convergence_lemma.
Arguments dominated_integrable {d T R mu D} _ f_ f g.

Section dominated_convergence_theorem.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f_ : (T -> \bar R)^nat) (f : T -> \bar R) (g : T -> \bar R).
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Hypothesis mf : measurable_fun D f.
Hypothesis f_f : {ae mu, forall x, D x -> f_ ^~ x @ \oo --> f x}.
Hypothesis ig : mu.-integrable D g.
Hypothesis f_g : {ae mu, forall x n, D x -> `|f_ n x| <= g x}.

Let g_ n x := `|f_ n x - f x|.

Theorem dominated_convergence : [/\ mu.-integrable D f,
  [sequence \int[mu]_(x in D) (g_ n x)]_n @ \oo --> 0 &
  [sequence \int[mu]_(x in D) (f_ n x)]_n @ \oo --> \int[mu]_(x in D) (f x) ].
Proof.
have [N1 [mN1 N10 subN1]] := f_f.
have [N2 [mN2 N20 subN2]] := f_g.
have [N3 [mN3 N30 subN3]] := integrable_ae mD ig.
pose N := N1 `|` N2 `|` N3.
have mN : measurable N by apply: measurableU => //; exact: measurableU.
have N0 : mu N = 0.
  by rewrite null_set_setU// ?null_set_setU//; exact: measurableU.
pose f' := f \_ (D `\` N); pose g' := g \_ (D `\` N).
pose f_' := fun n => f_ n \_ (D `\` N).
have f_f' x : D x -> f_' ^~ x @ \oo --> f' x.
  move=> Dx; rewrite /f_' /f' /restrict in_setD mem_set//=.
  have [/= xN|/= xN] := boolP (x \in N); first exact: cvg_cst.
  apply: contraPP (xN) => h; apply/negP; rewrite negbK inE; left; left.
  by apply: subN1 => /= /(_ Dx); exact: contra_not h.
have f_g' n x : D x -> `|f_' n x| <= g' x.
  move=> Dx; rewrite /f_' /g' /restrict in_setD mem_set//=.
  have [/=|/= xN] := boolP (x \in N); first by rewrite normr0.
  apply: contrapT => fg; move: xN; apply/negP; rewrite negbK inE; left; right.
  by apply: subN2 => /= /(_ n Dx).
have mu_ n : measurable_fun D (f_' n).
  apply/measurable_restrict => //; first exact: measurableD.
  exact: measurable_funS (mf_ _).
have ig' : mu.-integrable D g'.
  apply: (integrableS measurableT) => //.
  apply/(integrable_mkcond g (measurableD mD mN)).1.
  by apply: integrableS ig => //; exact: measurableD.
have finv x : D x -> g' x \is a fin_num.
  move=> Dx; rewrite /g' /restrict in_setD// mem_set//=.
  have [//|xN /=] := boolP (x \in N).
  apply: contrapT => fing; move: xN; apply/negP; rewrite negbK inE; right.
  by apply: subN3 => /= /(_ Dx).
split.
- have /integrableP if' : mu.-integrable D f'.
    exact: (dominated_integrable _ f_' _ g').
  apply/integrableP; split => //.
  move: if' => [?]; apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/ae_eq_integral => //;
    [exact: measurableT_comp|exact: measurableT_comp|].
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x Nx Dx.
  by rewrite /f' /restrict mem_set.
- have := @dominated_cvg0 _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X @ \oo --> _).
  rewrite [X in X @ \oo --> _ -> _](_ : _ = X) //.
  apply/funext => n; apply: ae_eq_integral => //.
  + apply: measurableT_comp => //; apply: emeasurable_funB => //.
    apply/measurable_restrict => //; first exact: measurableD.
    exact: (measurable_funS mD).
  + by rewrite /g_; apply: measurableT_comp => //; exact: emeasurable_funB.
  + exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /f' /restrict mem_set.
- have := @dominated_cvg _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X @ \oo --> _).
  rewrite [X in X @ \oo --> _ -> _](_ : _ = X) //; last first.
    apply/funext => n; apply: ae_eq_integral => //.
    exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /restrict mem_set.
  set Y := (X in _ -> _ --> X); rewrite [X in _ --> X -> _](_ : _ = Y) //.
  apply: ae_eq_integral => //.
    apply/measurable_restrict => //; first exact: measurableD.
    exact: (measurable_funS mD).
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
  by rewrite /f' /restrict mem_set.
Qed.

End dominated_convergence_theorem.
