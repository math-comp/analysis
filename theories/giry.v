From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets.
From mathcomp Require Import fsbigop functions reals topology separation_axioms.
From mathcomp Require Import ereal sequences numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

(**md**************************************************************************)
(* # The Giry monad                                                           *)
(*                                                                            *)
(*         giry T R == the type of subprobability measures over T             *)
(*      giry_ev P A == the evaluation map `giryM T R -> [0, 1]`               *)
(*    giry_int mu f := \int[mu]_x f x                                         *)
(*       giry_ret x == the unit of the Giry monad, i.e., \d_x                 *)
(* @giry_join _ T R == the multiplication of the Giry monad                   *)
(*                     type : giry (giry T R) R -> giry T R                   *)
(*      giry_map mf == the map of type  giry T1 R -> giry T2 R                *)
(*                     where mf is a proof that f : T1 -> T2 is measurable    *)
(*  giry_bind mu mf == the bind with mu : giry T1 R and f : T1 -> giry T2 R   *)
(*        giry_prod == product of type                                        *)
(*                     giry T1 R * giry T2 R -> giry (T1 * T2) R              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

(* TODO: PR to measure.v? *)
Section mzero_subprobability.
Context d (T : measurableType d) (R : realType).

Let mzero_setT : (@mzero d T R setT <= 1)%E.
Proof. by rewrite /mzero/=. Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.

End mzero_subprobability.

Section giry_def.
Local Open Scope classical_set_scope.
Context d (T : measurableType d) (R : realType).

Definition giry : Type := @subprobability d T R.

HB.instance Definition _ := gen_eqMixin giry.
HB.instance Definition _ := gen_choiceMixin giry.
HB.instance Definition _ := isPointed.Build giry mzero.

Definition giry_ev (mu : giry) (A : set T) := mu A.

Definition preimg_giry_ev (A : set T) : set_system giry :=
  preimage_set_system [set: giry] (giry_ev ^~ A) measurable.

Definition giry_measurable := <<s \bigcup_(A in measurable) preimg_giry_ev A >>.

Let giry_measurable0 : giry_measurable set0.
Proof. exact: sigma_algebra0. Qed.

Let giry_measurableC (U : set giry) :
  giry_measurable U -> giry_measurable (~` U).
Proof. exact: sigma_algebraC. Qed.

Let giry_measurableU (F : (set giry)^nat) :
  (forall i, giry_measurable (F i)) -> giry_measurable (\bigcup_i F i).
Proof. exact: sigma_algebra_bigcup. Qed.

Definition giry_display : measure_display.
Proof. by constructor. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build giry_display giry giry_measurable
    giry_measurable0 giry_measurableC giry_measurableU.

(* TODO: Make hint? *)
Lemma measurable_giry_ev (A : set T) : measurable A ->
  measurable_fun [set: giry] (giry_ev ^~ A).
Proof.
move=> mS.
apply: (@measurability giry_display _ giry _ setT (giry_ev ^~ A) measurable).
  by rewrite smallest_id//; exact: sigma_algebra_measurable.
apply: subset_trans; last exact: sub_gen_smallest.
exact: (bigcup_sup mS).
Qed.

End giry_def.
Arguments giry_ev {d T R} mu A.

Definition measure_eq {d} {T : measurableType d} {R : realType} :
  giry T R -> giry T R -> Prop :=
  fun μ1 μ2 => forall S : set T, measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).

Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.

Section giry_integral.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Definition giry_int (mu : giry T R) (f : T -> \bar R) := \int[mu]_x f x.

Import HBNNSimple.

Lemma measurable_giry_int (f : T -> \bar R) :
  measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  measurable_fun [set: giry T R] (giry_int ^~ f).
Proof.
(*
  The idea is to reconstruct f from simple functions, then use measurability of giry_ev.
  Tom Avery. Codensity and the Giry monad. https://arxiv.org/pdf/1410.4432.
 *)
move=> mf h0.
pose g := nnsfun_approx measurableT mf.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (gE n) by exact/measurable_EFinP.
have gE0 n x : [set: T] x -> 0 <= (gE n) x by rewrite /gE /= // lee_fin.
have HgEmono x : [set: T] x -> {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> _ n m nm; exact/lefP/nd_nnsfun_approx.
(* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
have Hcvg := cvg_monotone_convergence _ mgE gE0 HgEmono.
pose gEInt := fun n μ => \int[μ]_x (gE n) x.
have mgEInt n : measurable_fun [set: giry T R] (gEInt n).
  rewrite /gEInt /gE /=.
  apply (eq_measurable_fun (fun μ : giry T R =>
    \sum_(x \in range (g n)) x%:E * μ (g n @^-1` [set x]))).
    by move=> μ Hμ; rewrite integralT_nnsfun sintegralE.
  apply: emeasurable_fsum => // r.
  apply: measurable_funeM.
  exact: measurable_giry_ev.
(* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
apply: (emeasurable_fun_cvg _ (fun μ : giry T R => \int[μ]_x f x) mgEInt).
move=> μ Hμ.
rewrite /gEInt /=.
rewrite (eq_integral (fun x : T => limn (gE ^~ x))).
  exact: (Hcvg μ measurableT).
move=> x _; apply/esym/cvg_lim  => //.
exact/cvg_nnsfun_approx.
Qed.

End giry_integral.
Arguments giry_int {d T R} mu f.

Local Open Scope classical_set_scope.
(* Adapted from mathlib induction_on_inter *)
(* TODO: change premises to use setX_closed like notations *)
Lemma dynkin_induction d {T : measurableType d} (G : set (set T))
    (P : set_system T) :
  @measurable _ T = <<s G >> ->
  setI_closed G ->
  P [set: T] ->
  G `<=` P ->
  (forall S, measurable S -> P S -> P (~` S)) ->
  (forall F : (set T)^nat,
    (forall n, measurable (F n)) ->
    trivIset setT F ->
    (forall n, P (F n)) -> P (\bigcup_k F k)) ->
  (forall S, <<s G >> S -> P S).
Proof.
move=> GE GI PsetT GP PsetC Pbigcup A sGA.
suff: <<s G >> `<=` [set A | measurable A /\ P A] by move=> /(_ _ sGA)[].
apply: lambda_system_subset; [by []| | |by []].
- apply/dynkin_lambda_system; split => //.
  + by move=> B [mB PB]; split; [exact: measurableC|exact: PsetC].
  + move=> F tF Hm; split.
      by apply: bigcup_measurable => k _; apply Hm.
    by apply: Pbigcup => //; apply Hm.
- move=> B GB; split; last exact: GP.
  by rewrite GE; exact: sub_gen_smallest.
Qed.
Local Close Scope classical_set_scope.

Section measurable_giry_codensity.
Local Open Scope classical_set_scope.

(* TODO: move this lemma to a more accessible location? *)
Let measurability_image_sub d d' (aT : measurableType d) (rT : measurableType d')
    (f : aT -> rT) (G : set (set rT)) :
    @measurable _ rT = <<s G >> ->
    (forall B, G B -> measurable (f @^-1` B)) ->
  measurable_fun [set: aT] f.
Proof.
move=> GE Gf; apply/(measurability G) => //.
by apply/image_subP => A /Gf; rewrite setTI.
Qed.

Lemma measurable_giry_codensity {d1} {d2} {T1 : measurableType d1}
    {T2 : measurableType d2} {R : realType} (f : T1 -> giry T2 R) :
  (forall B, measurable B -> measurable_fun [set: T1] (f ^~ B)) ->
  measurable_fun [set: T1] f.
Proof.
move=> mf.
pose G : set_system (giry T2 R) := \bigcup_(B in measurable) preimg_giry_ev B.
apply: (measurability_image_sub (G := G)) => // _ [B mB [Y mY] <-].
exact: mf.
Qed.

End measurable_giry_codensity.

Section giry_map.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.

Variables (f : T1 -> T2) (mf : measurable_fun [set: T1] f) (mu1 : giry T1 R).

Let map := pushforward mu1 f.

Let map0 : map set0 = 0. Proof. exact: measure0. Qed.

Let map_ge0 A : 0 <= map A. Proof. exact: measure_ge0. Qed.

Let map_sigma_additive : semi_sigma_additive map.
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ map
  map0 map_ge0 map_sigma_additive.

(* used to work before the change of definition of pushforward
HB.instance Definition _ := Measure.on gMap_ev.
the change of definition was maybe not a good idea...
https://github.com/math-comp/analysis/pull/1661
*)

Let map_setT : map [set: T2] <= 1.
Proof. by rewrite /map /pushforward /= sprobability_setT. Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ map map_setT.

Definition giry_map : giry T2 R := map.

End giry_map.

Section giry_map_meas.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Type f : T1 -> T2.

Lemma giry_int_map f (mf : measurable_fun [set: T1] f)
    (mu : giry T1 R) (h : T2 -> \bar R) :
  measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  giry_int (giry_map mf mu) h = giry_int mu (h \o f).
Proof. by move=> mh h0; exact: ge0_integral_pushforward. Qed.

Lemma giry_mapE f (mf : measurable_fun [set: T1] f)
    (mu1 : giry T1 R) (B : set T2) : measurable B ->
  giry_map mf mu1 B = \int[mu1]_x (\d_(f x))%R B.
Proof.
move=> mA.
rewrite -[in LHS](setIT B) -[LHS]integral_indic// [LHS]giry_int_map//.
  exact/measurable_EFinP/measurable_indic.
by move=> ?; rewrite lee_fin.
Qed.

Lemma measurable_giry_map f (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: giry T1 R] (giry_map mf).
Proof.
rewrite /giry_map.
apply: (@measurable_giry_codensity _ _ (giry T1 R)) => B mB.
apply: measurable_giry_ev.
by rewrite -(setTI (f @^-1` B)); exact: mf.
Qed.

End giry_map_meas.

Section giry_ret.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}.

Definition giry_ret (x : T) : giry T R := \d_x.

Lemma measurable_giry_ret : measurable_fun [set: T] giry_ret.
Proof. by apply: measurable_giry_codensity; exact: measurable_fun_dirac. Qed.

Lemma giry_int_ret (x : T) (f : T -> \bar R) : measurable_fun [set: T] f ->
  giry_int (giry_ret x) f = f x.
Proof.
by move=> mf; rewrite /giry_int /giry_ret integral_dirac// diracT mul1e.
Qed.

End giry_ret.

Section giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable M : giry (giry T R) R.

Let join A := giry_int M (giry_ev ^~ A).

Let join0 : join set0 = 0.
Proof. by rewrite /join /giry_ev /giry_int/= integral0_eq. Qed.

Let join_ge0 A : 0 <= join A. Proof. by rewrite /join integral_ge0. Qed.

Let join_semi_sigma_additive : semi_sigma_additive join.
Proof.
move=> F mF tF _; rewrite [X in _ --> X](_ : _ =
    giry_int M (fun x => \sum_(0 <= k <oo) x (F k))); last first.
  apply: eq_integral => mu _.
  by apply/esym/cvg_lim => //; exact: measure_sigma_additive.
rewrite [X in X @ _](_ : _ =
    (fun n => giry_int M (fun mu => \sum_(0 <= i < n) mu (F i)))); last first.
  apply/funext => n; rewrite -ge0_integral_sum//.
  by move=> ?; exact: measurable_giry_ev.
apply: cvg_monotone_convergence => //.
- by move=> n; apply: emeasurable_sum => m; exact: measurable_giry_ev.
- by move=> n x _; rewrite sume_ge0.
- by move=> x _ m n mn; exact: ereal_nondecreasing_series.
Qed.

HB.instance Definition _ := isMeasure.Build d _ R join
  join0 join_ge0 join_semi_sigma_additive.

Let join_setT : join [set: T] <= 1.
Proof.
rewrite (@le_trans _ _ (\int[M]_x `|giry_ev x [set: T]|))//; last first.
  rewrite (le_trans _ (@sprobability_setT _ _ _ M))//.
  rewrite -[leRHS]mul1e integral_le_bound//.
    exact: measurable_giry_ev.
  by apply/aeW => x _; rewrite gee0_abs// sprobability_setT.
rewrite ge0_le_integral//=.
- exact: measurable_giry_ev.
- by move=> x _; rewrite abse_ge0.
- by apply: measurableT_comp => //; exact: measurable_giry_ev.
- by move=> x _; rewrite gee0_abs.
Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ join join_setT.

Definition giry_join : giry T R := join.

End giry_join.
Arguments giry_join {d T R}.

Section measurable_giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}.

Lemma measurable_giry_join : measurable_fun [set: giry (giry T R) R] giry_join.
Proof.
apply: measurable_giry_codensity => B mB/=.
by apply: measurable_giry_int => //; exact: measurable_giry_ev.
Qed.

Import HBNNSimple.

Lemma sintegral_giry_join (M : giry (giry T R) R) (h : {nnsfun T >-> R}) :
  sintegral (giry_join M) h = \int[M]_mu sintegral mu h.
Proof.
under eq_integral do rewrite sintegralE.
rewrite ge0_integral_fsum//; last 2 first.
  by move=> r; apply: measurable_funeM; exact: measurable_giry_ev.
  by move=> n x _; exact: nnsfun_mulemu_ge0.
rewrite sintegralE /=.
apply: fsbigop.eq_fsbigr => // r rh.
rewrite integralZl//.
have := finite_measure_integrable_cst M 1.
apply: le_integrable => //; first exact: measurable_giry_ev.
move=> mu _ /=.
rewrite normr1 (le_trans _ (@sprobability_setT _ _ _ mu))// gee0_abs//.
by rewrite le_measure// ?inE.
Qed.

Lemma giry_int_join (M : giry (giry T R) R) (h : T -> \bar R) :
    measurable_fun [set: T] h -> (forall x, 0 <= h x) ->
  giry_int (giry_join M) h = giry_int M (giry_int ^~ h).
Proof.
move=> mh h0.
pose g := nnsfun_approx measurableT mh.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (gE n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
rewrite /giry_int.
transitivity (limn (fun n => \int[giry_join M]_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[M]_mu \int[mu]_x gE n x)).
  apply: congr_lim; apply/funext => n.
  rewrite integralT_nnsfun sintegral_giry_join; apply: eq_integral => x _.
  by rewrite integralT_nnsfun.
rewrite -monotone_convergence//; last 3 first.
  by move=> n; exact: measurable_giry_int.
  by move=> n x _; exact: integral_ge0.
  by move=> x _ m n mn; apply: ge0_le_integral => // t _; exact: nd_gE.
apply: eq_integral => mu _.
rewrite -monotone_convergence//.
apply: eq_integral => t _.
by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.

End measurable_giry_join.

Reserved Notation "m >>= f" (at level 49).

Section giry_bind.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types (mu : giry T1 R) (f : T1 -> giry T2 R).

Definition giry_bind mu f (mf : measurable_fun [set: T1] f) : giry T2 R :=
  (giry_join \o giry_map mf) mu.

Local Notation "m >>= mf" := (giry_bind m mf).

Lemma measurable_giry_bind f (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: giry T1 R] (fun mu => mu >>= mf).
Proof.
apply: (@measurableT_comp _ _ _ _ _ _ _ _ (giry_map mf)) => //=.
  exact: measurable_giry_join.
exact: measurable_giry_map.
Qed.

Lemma giry_int_bind mu f (mf : measurable_fun [set: T1] f) (h : T2 -> \bar R) :
    measurable_fun [set: T2] h -> (forall x, 0 <= h x)%E ->
  giry_int (mu >>= mf) h = giry_int mu (fun x => giry_int (f x) h).
Proof.
move=> mh h0; rewrite /giry_bind /= giry_int_join// giry_int_map//.
  exact: measurable_giry_int.
by move=> ?; exact: integral_ge0.
Qed.

End giry_bind.

Section giry_monad.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2)
  (T3 : measurableType d3) (R : realType).

Lemma giry_joinA (x : giry (giry (giry T1 R) R) R) :
  (giry_join \o giry_map measurable_giry_join) x ≡μ
  (giry_join \o giry_join) x.
Proof.
move=> A mA/=.
rewrite giry_int_map//; last exact: measurable_giry_ev.
by rewrite giry_int_join//; exact: measurable_giry_ev.
Qed.

Lemma giry_join_id1 (x : giry T1 R) :
  (giry_join \o giry_map measurable_giry_ret) x ≡μ
  (giry_join \o giry_ret) x.
Proof.
move=> A mA/=.
rewrite giry_int_map//; last exact: measurable_giry_ev.
rewrite giry_int_ret//; last exact: measurable_giry_ev.
by rewrite /giry_int /giry_ev /giry_ret/= /dirac integral_indic// setIT.
Qed.

Lemma giry_join_id2 (x : giry (giry T1 R) R) (f : T1 -> T2)
    (mf : measurable_fun [set: T1] f) :
  (giry_join \o giry_map (measurable_giry_map mf)) x ≡μ
  (giry_map mf \o giry_join) x.
Proof.
by move=> X mS /=; rewrite giry_int_map//; exact: measurable_giry_ev.
Qed.

End giry_monad.

Section giry_map_zero.
Local Open Scope classical_set_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

Lemma giry_map_zero (f : T1 -> T2) (mf : measurable_fun [set: T1] f) :
  giry_map mf (@mzero d1 T1 R) ≡μ @mzero d2 T2 R.
Proof. by []. Qed.

End giry_map_zero.

Section giry_prod.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.
Variable μ12 : giry T1 R * giry T2 R.

(* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
Let prod := μ12.1 \x μ12.2.

HB.instance Definition _ := Measure.on prod.

Let prod_setT : prod setT <= 1.
Proof.
rewrite -setXTT [leLHS]product_measure1E// -[leRHS]mule1.
by rewrite lee_pmul// sprobability_setT.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ prod prod_setT.

Definition giry_prod : giry (T1 * T2)%type R := prod.

(*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)

End giry_prod.

Section measurable_giry_prod.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

(* TODO: Clean up, maybe move elsewhere *)
Lemma subprobability_prod_setC (P : giry T1 R * giry T2 R) (A : set (T1 * T2)) :
  measurable A ->
  (P.1 \x P.2) (~` A) = (P.1 \x P.2) [set: T1 * T2] - (P.1 \x P.2) A.
Proof.
move=> mA; rewrite -(setvU A) measureU//= ?addeK ?setICl//.
- by rewrite (_ : (_ \x _)%E = giry_prod P)// fin_num_measure.
- exact: measurableC.
Qed.

(* See: Tobias Fritz. A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics.
   https://arxiv.org/abs/1908.07021 *)
Lemma measurable_giry_prod :
  measurable_fun [set: giry T1 R * giry T2 R] giry_prod.
Proof.
apply: measurable_giry_codensity => /=.
rewrite measurable_prod_measurableType.
apply: dynkin_induction => /=.
- by rewrite measurable_prod_measurableType.
- move=> _ _ [A1 mA1 [A2 mA2 <-]] [B1 mB1 [B2 mB2 <-]].
  exists (A1 `&` B1); first exact: measurableI.
  exists (A2 `&` B2); first exact: measurableI.
  by rewrite setXI.
- apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      x.1 [set: T1] * x.2 [set: T2])).
    by move=> x _; rewrite -setXTT product_measure1E.
  by apply: emeasurable_funM => /=;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> _ [A mA [B mB <-]].
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R => x.1 A * x.2 B)).
    by move=> x _; rewrite product_measure1E.
  by apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> S mS HS.
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      x.1 [set: T1] * x.2 [set: T2] - (x.1 \x x.2) S)).
    move=> /= x _; rewrite subprobability_prod_setC//.
    by rewrite -setXTT product_measure1E.
  apply emeasurable_funB => //=.
  by apply: emeasurable_funM => //=;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> F mF tF Fn.
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      \sum_(0 <= k <oo) (x.1 \x x.2) (F k))).
    by move=> x _; rewrite measure_semi_bigcup//; exact: bigcup_measurable.
  exact: ge0_emeasurable_sum.
Qed.

End measurable_giry_prod.

Section giry_prod_int.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.
Variables (μ1 : giry T1 R) (μ2 : giry T2 R) (h : T1 * T2 -> \bar R).
Hypotheses (mh : measurable_fun [set: T1 * T2] h) (h0 : forall x, 0 <= h x).

Lemma giry_int_prod1 : giry_int (giry_prod (μ1, μ2)) h =
  giry_int μ1 (fun x => giry_int μ2 (fun y => h (x, y))).
Proof. exact: fubini_tonelli1. Qed.

Lemma giry_int_prod2 : giry_int (giry_prod (μ1, μ2)) h =
  giry_int μ2 (fun y => giry_int μ1 (fun x => h (x, y))).
Proof. exact: fubini_tonelli2. Qed.

End giry_prod_int.
