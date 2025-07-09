From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets.
From mathcomp Require Import fsbigop functions reals topology separation_axioms.
From mathcomp Require Import ereal sequences numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
(*
From clutch.prob.monad Require Export prelude.
From clutch.prelude Require Import classical.
Import Coq.Relations.Relation_Definitions.
From Coq Require Import Classes.Morphisms Reals.
 *)
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

(* TODO: small PR to measure.v? *)
Section mzero_subprobability.
Context d (T : measurableType d) (R : realType).

Let mzero_setT : (@mzero d T R setT <= 1)%E.
Proof. by rewrite /mzero/=. Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.

End mzero_subprobability.

Section giryM_def.
Local Open Scope classical_set_scope.
Context d (T : measurableType d) (R : realType).

Definition giryM : Type := @subprobability d T R.

HB.instance Definition _ := gen_eqMixin giryM.
HB.instance Definition _ := gen_choiceMixin giryM.
HB.instance Definition _ := isPointed.Build giryM mzero.

Definition gEval (S : set T) (mu : giryM) := mu S.

Definition gEvalPreImg (S : set T) :=
  preimage_set_system setT (gEval S) measurable.

Definition giry_measurable := <<s \bigcup_(S in measurable) (gEvalPreImg S) >>.

Let giry_measurable0 : giry_measurable set0.
Proof. exact: sigma_algebra0. Qed.

Let giry_measurableC (S : set giryM) :
  giry_measurable S -> giry_measurable (~` S).
Proof. exact: sigma_algebraC. Qed.

Let giry_measurableU (A : (set giryM)^nat) :
  (forall i, giry_measurable (A i)) -> giry_measurable (\bigcup_i A i).
Proof. exact: sigma_algebra_bigcup. Qed.

Definition giry_display : measure_display.
Proof. by constructor. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build giry_display giryM giry_measurable
    giry_measurable0 giry_measurableC giry_measurableU.

End giryM_def.

Definition measure_eq {d} {T : measurableType d} {R : realType} :
  giryM T R -> giryM T R -> Prop :=
  fun μ1 μ2 => forall S : set T, measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).

Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡μ _) => symmetry; assumption : core.

Section giry_eval.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Context d (T : measurableType d) (R : realType).

(* TODO: Make hint *)
Lemma gEval_meas_fun (S : set T) : d.-measurable S ->
  measurable_fun [set: giryM T R] (gEval S).
Proof.
move=> mS.
apply: (@measurability giry_display _ (@giryM _ T R) _ setT (@gEval _ _ R S)
    (@measurable _ (\bar R))).
  rewrite smallest_id//.
  exact: sigma_algebra_measurable.
apply: subset_trans; last exact: sub_gen_smallest.
exact: (bigcup_sup mS).
Qed.

End giry_eval.

Section giry_integral.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Definition gInt (f : T -> \bar R) (mu : giryM T R) := \int[mu]_x f x.

Import HBNNSimple.

Lemma gInt_meas_fun (f : T -> \bar R) :
  measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  measurable_fun [set: giryM T R] (gInt f).
Proof.
(*
  The idea is to reconstruct f from simple functions, then use
  measurability of gEval. See "Codensity and the Giry monad", Avery
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
have mgEInt n : measurable_fun [set: giryM T R] (gEInt n).
  rewrite /gEInt /gE /=.
  apply (eq_measurable_fun (fun μ : giryM T R =>
    \sum_(x \in range (g n)) (x%:E * μ (g n @^-1` [set x])))).
    by move=> μ Hμ; rewrite integralT_nnsfun sintegralE.
  apply: emeasurable_fsum => // r.
  have mg : d.-measurable (g n @^-1` [set r]) by [].
  apply (measurable_funeM r%:E).
  have : measurable_fun [set: giryM T R] (fun x : giryM T R => x (g n @^-1` [set r])); auto.
  exact : eq_measurable_fun (gEval_meas_fun mg).
(* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
apply: (emeasurable_fun_cvg _ (fun μ : giryM T R => \int[μ]_x f x) mgEInt).
move=> μ Hμ.
rewrite /gEInt /=.
rewrite (eq_integral (fun x : T => limn (gE^~ x))).
  exact: (Hcvg μ measurableT).
move=> x _; apply/esym/cvg_lim  => //.
exact/cvg_nnsfun_approx.
Qed.

End giry_integral.

(* TODO: Everything below needs to be cleaned up *)

Section giry_cod_meas.
Local Open Scope classical_set_scope.

 (* TODO: Either move this lemma to a more accessible location, or integrate within
    the proof below *)
Let measurability_aux d d' (aT : measurableType d) (rT : measurableType d')
  (f : aT -> rT) (G : set (set rT)) :
  @measurable _ rT = <<s G >> ->
  (forall (S : set rT), G S -> @measurable _ aT (f @^-1` S)) ->
  measurable_fun [set: aT] f.
Proof.
move=> HG HS.
apply/(measurability G) => //.
apply/image_subP => A GA.
rewrite setTI.
exact: HS.
Qed.

(* Adapted from mathlib induction_on_inter *)
(* TODO: Clean up proof, move lemma, change premises to use setX_closed like notations *)
Lemma dynkin_induction d {T : measurableType d} (G : set (set T)) (P : set_system T) :
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
move=> HG GI HsetT Hgen HsetC Hbigcup S HGS.
have mS : measurable S by rewrite HG.
suff Haux : <<s G >> `<=` [set S : set T | measurable S /\ P S].
  by apply Haux.
apply lambda_system_subset; first by [].
- apply (dynkin_lambda_system ([set S0 | measurable S0 /\ P S0])).
  split; first by [].
    move=> A [mA PA].
    split; first exact: measurableC.
    exact: HsetC.
  move=> F tF Hm.
  split.
    apply bigcup_measurable; auto.
    move=> k Hk.
    by apply Hm.
  apply: Hbigcup => //.
    by apply Hm.
  by apply Hm.
- move=> A GA; split; last exact: Hgen.
  rewrite HG //.
  exact: sub_gen_smallest.
- by [].
Qed.

Lemma giryM_cod_meas_fun {d1} {d2} {T1 : measurableType d1}
    {T2 : measurableType d2} {R : realType} (f : T1 -> giryM T2 R) :
  (forall (S : set T2), measurable S -> measurable_fun setT (f ^~ S)) ->
  measurable_fun [set: T1] f.
Proof.
move=> HS.
pose G : set_system (giryM T2 R) := \bigcup_(S in d2.-measurable) gEvalPreImg S.
apply: (measurability_aux (G := G)) => // S [U mU [M mB] <-].
rewrite -comp_preimage.
exact: HS.
Qed.

End giry_cod_meas.

Section giry_map.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.

Variables (f : T1 -> T2) (Hmf : measurable_fun [set: T1] f) (μ1 : giryM T1 R).

Definition gMap_ev := pushforward μ1 f.

Let gMap_ev0 : gMap_ev set0 = 0.
Proof. exact: measure0. Qed.

Let gMap_ev_ge0 A : 0 <= gMap_ev A.
Proof. exact: measure_ge0. Qed.

Let gMap_ev_sigma_additive : semi_sigma_additive gMap_ev.
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ gMap_ev
  gMap_ev0 gMap_ev_ge0 gMap_ev_sigma_additive.

(* used to work before the change of definition of pushforward
HB.instance Definition _ := Measure.on gMap_ev.
the change of definition was maybe not a good idea...
https://github.com/math-comp/analysis/pull/1661
*)

Let gMap_setT : gMap_ev setT <= 1.
Proof.
by rewrite /gMap_ev /pushforward /= sprobability_setT.
Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gMap_ev gMap_setT.

Definition gMap : giryM T2 R := gMap_ev.

End giry_map.

Section giry_map_meas.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).

Lemma gMap_to_int (f : T1 -> T2) (mf : measurable_fun [set: T1] f)
    (μ1 : giryM T1 R) (S : set T2) : measurable S ->
  gMap mf μ1 S = \int[μ1]_x (\1_S (f x))%:E.
Proof.
move=> mS.
rewrite -[in LHS](setIT S) -[LHS]integral_indic//.
rewrite ge0_integral_pushforward//.
  exact/measurable_EFinP/measurable_indic.
by move=> y _; rewrite lee_fin.
Qed.

Lemma gMap_meas_fun (f : T1 -> T2) (mf : measurable_fun [set: T1] f):
  measurable_fun [set: giryM T1 R] (gMap mf (R:= R)).
Proof.
rewrite /gMap.
apply: (@giryM_cod_meas_fun _ _ (giryM T1 R)) => S mS.
rewrite /gMap_ev /pushforward /=.
apply: gEval_meas_fun.
rewrite -(setTI (f @^-1` S)).
exact: mf.
Qed.

Lemma gMapInt (f : T1 -> T2) (mf : measurable_fun [set: T1] f) (μ : giryM T1 R)
  (h : T2 -> \bar R) :
  measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  gInt h (gMap mf μ) = gInt (h \o f) μ.
Proof.
by move=> mh h0; exact: ge0_integral_pushforward.
Qed.

End giry_map_meas.

Section giry_ret.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}.

Definition gRet (x : T) : giryM T R := dirac^~ R x.

Lemma gRet_meas_fun : measurable_fun [set: T] gRet.
Proof.
apply: giryM_cod_meas_fun.
exact: measurable_fun_dirac.
Qed.

Lemma gRetInt (x : T) (h : T -> \bar R) : measurable_fun [set: T] h ->
  gInt h (gRet x) = h x.
Proof.
move=> mh.
rewrite /gInt.
have : forall S, d.-measurable S -> S `<=` [set : T] -> gRet x S = dirac x S by [].
move/eq_measure_integral => ->//.
by rewrite integral_dirac// diracT mul1e.
Qed.

Lemma gRetInt_rw (x : T) (h : T -> \bar R) :
  measurable_fun [set: T] h -> \int[gRet x]_x h x = h x.
Proof. exact: gRetInt. Qed.

End giry_ret.

Section giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable M : giryM (giryM T R) R.

Definition gJoin_ev (S : set T) := gInt (gEval S) M.

Let gJoin0 : gJoin_ev set0 = 0.
Proof. by rewrite /gJoin_ev /gEval /gInt integral0_eq. Qed.

Let gJoin_ge0 A : 0 <= gJoin_ev A.
Proof. by rewrite /gJoin_ev integral_ge0. Qed.

(* TODO: Cleaner proof? *)
Let gJoin_semi_sigma_additive : semi_sigma_additive (gJoin_ev).
Proof.
move=> F mF tF _.
rewrite /gJoin_ev /gInt /gEval /=.
rewrite [X in _ --> X](_ : _ = \int[M]_x \sum_(0 <= k <oo) x (F k)); last first.
  apply eq_integral => mu _.
  apply/esym/cvg_lim => //.
  exact: measure_sigma_additive.
rewrite [X in X @ _](_ : _ =
    (fun n => \int[M]_x \sum_(0 <= i < n)  x (F i))); last first.
  apply/funext => n.
  rewrite -ge0_integral_sum// => m.
  exact: gEval_meas_fun.
apply: cvg_monotone_convergence => //.
- move=> n; apply: emeasurable_sum => m.
  exact: gEval_meas_fun.
- by move=> n x _; rewrite sume_ge0.
- by move=> x _ m n mn; exact: ereal_nondecreasing_series.
Qed.

HB.instance Definition _ := isMeasure.Build d _ R gJoin_ev
  gJoin0 gJoin_ge0 gJoin_semi_sigma_additive.

(* TODO: Cleaner proof? *)
Let gJoin_setT : gJoin_ev setT <= 1.
Proof.
rewrite /gJoin_ev.
rewrite (@le_trans _ _ (\int[M]_x `|gEval setT x|))//; last first.
  rewrite (@le_trans _ _ (1%E * M setT))//; last first.
    by rewrite mul1e sprobability_setT.
  rewrite integral_le_bound//.
    exact: gEval_meas_fun.
  apply/aeW => x _.
  by rewrite gee0_abs// sprobability_setT.
rewrite ge0_le_integral//=.
- exact: gEval_meas_fun.
- by move=> x _; rewrite abse_ge0.
- by apply: measurableT_comp => //; exact: gEval_meas_fun.
- by move=> x _; rewrite gee0_abs.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ gJoin_ev gJoin_setT.

Definition gJoin : giryM T R := gJoin_ev.

End giry_join.

Section giry_join_meas_fun.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}.

Lemma gJoin_meas_fun : measurable_fun [set: giryM (giryM T R) R] (@gJoin d T R).
Proof.
apply: (@giryM_cod_meas_fun _ _ (giryM (giryM T _)_)) => S mS.
apply: (@gInt_meas_fun _ _ _ (gEval S)) => //=.
exact: gEval_meas_fun.
Qed.

Import HBNNSimple.

(* TODO: Messy proof, cleanup *)
Lemma gJoinSInt (M : giryM (giryM T R) R) (h : {nnsfun T >-> R}) :
  sintegral (gJoin M) h = \int[M]_μ sintegral μ h.
Proof.
under eq_integral do rewrite sintegralE.
rewrite ge0_integral_fsum//; last 2 first.
  by move=> r; apply: measurable_funeM; exact: gEval_meas_fun.
  by move=> n x _; exact: nnsfun_mulemu_ge0.
rewrite sintegralE /=.
apply: fsbigop.eq_fsbigr => // r rh.
rewrite integralZl//.
have := finite_measure_integrable_cst M 1.
apply: le_integrable => //; first exact: gEval_meas_fun.
move=> mu _ /=.
rewrite normr1 gee0_abs// (le_trans _ (@sprobability_setT _ _ _ mu))//.
by rewrite le_measure// ?inE.
Qed.

(* TODO: Messy proof, cleanup *)

Lemma gJoinInt (M : giryM (giryM T R) R) (h : T -> \bar R) :
    measurable_fun [set: T] h -> (forall x, 0 <= h x) ->
  gInt h (gJoin M) = gInt (fun μ : giryM T R => \int[μ]_x h x) M.
Proof.
move=> mh h0.
pose g := nnsfun_approx measurableT mh.
pose gE := fun n => EFin \o (g n).
have mgE n : measurable_fun setT (gE n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
(* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
rewrite /gInt.
transitivity (limn (fun n => \int[gJoin M]_x gE n x)).
  rewrite -monotone_convergence//.
  apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[M]_μ \int[μ]_x gE n x)).
  apply: congr_lim; apply/funext => n.
  rewrite integralT_nnsfun.
  rewrite gJoinSInt.
  apply: eq_integral => x _.
  by rewrite integralT_nnsfun.
rewrite -monotone_convergence//; last 3 first.
  by move=> n; exact: gInt_meas_fun.
  by move=> n x _; exact: integral_ge0.
  by move=> x _ m n mn; apply: ge0_le_integral => // t _; exact: nd_gE.
apply: eq_integral => mu _.
rewrite -monotone_convergence//.
apply: eq_integral => t _.
by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.

End giry_join_meas_fun.

Section giry_bind.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).

Definition gBind (f : T1 -> giryM T2 R) (mf : measurable_fun [set: T1] f)
    : giryM T1 R -> giryM T2 R :=
  (gJoin (R := R)) \o (gMap mf (R := R)).

Lemma gBind_meas_fun (f : T1 -> giryM T2 R) (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: giryM T1 R] (gBind mf).
Proof.
apply: (@measurable_comp _ _ _ _ _ _ setT) => //.
  exact: gJoin_meas_fun.
exact: gMap_meas_fun.
Qed.

End giry_bind.

Section giry_bind_meas_fun.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

Lemma gBindInt_meas_fun (μ : giryM T1 R) (f : T1 -> giryM T2 R)
    (h : T2 -> \bar R) : measurable_fun [set: T1] f ->
    measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  measurable_fun setT (fun x => gInt h (f x)).
Proof.
move=> mf mh h0.
apply: (@measurable_comp _ _ _ _ _ _ setT _ _ f) => //.
exact: gInt_meas_fun.
Qed.

Lemma gBindInt (μ : giryM T1 R) (f : T1 -> giryM T2 R)
    (mf : measurable_fun [set: T1] f) (h : T2 -> \bar R) :
    measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  gInt h (gBind mf μ) = gInt (fun x => gInt h (f x)) μ.
Proof.
move=> mh h0; rewrite /gBind /= gJoinInt// gMapInt//.
  exact: gInt_meas_fun.
by move=> x; exact: integral_ge0.
Qed.

Lemma gBindInt_rw (μ : giryM T1 R) (f : T1 -> giryM T2 R)
    (mf : measurable_fun [set: T1] f) (h : T2 -> \bar R) :
    measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  \int[gBind mf μ]_y h y = \int[μ]_x \int[f x]_y  h y.
Proof. exact: gBindInt. Qed.

End giry_bind_meas_fun.

Section giry_monad.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2)
  (T3 : measurableType d3) (R : realType).

Lemma gJoin_assoc (x : giryM (giryM (giryM T1 R) R) R) :
  ((@gJoin _ _ R) \o (gMap (@gJoin_meas_fun _ _ R))) x ≡μ ((@gJoin _ _ R) \o (@gJoin _ _ R)) x.
Proof.
move=> S mS.
rewrite /= /gJoin_ev gMapInt//; last exact: gEval_meas_fun.
by rewrite gJoinInt//; exact: gEval_meas_fun.
Qed.

Lemma gJoin_id1 (x : giryM T1 R) :
  ((@gJoin _ _ R) \o (gMap (@gRet_meas_fun _ _ R))) x
  ≡μ ((@gJoin _ _ R) \o (@gRet _ _ R)) x.
Proof.
move=> S mS.
rewrite /= /gJoin_ev.
rewrite gMapInt//; last exact: gEval_meas_fun.
rewrite gRetInt//; last exact: gEval_meas_fun.
by rewrite /gInt /gEval /gRet /= /dirac integral_indic// setIT.
Qed.

Lemma gJoin_id2 (x : giryM (giryM T1 R) R) (f : T1 -> T2)
    (mf : measurable_fun [set: T1] f) :
  ((@gJoin _ _ R) \o gMap (gMap_meas_fun mf)) x ≡μ (gMap mf \o (@gJoin _ _ R)) x.
Proof.
move=> X mS.
rewrite /= /gJoin_ev gMapInt//.
exact: gEval_meas_fun.
Qed.

End giry_monad.

Section giry_zero_def.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {T1 : measurableType d1} {R : realType}.

Definition gZero := mzero : giryM T1 R.

Lemma gZero_eval S : (*d1.-measurable S ->*) gZero S = 0.
Proof. by []. Qed.

End giry_zero_def.

Section giry_zero.
Local Open Scope classical_set_scope.

Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

Lemma gZero_map (f : T1 -> T2) (mf : measurable_fun [set: T1] f) :
  gMap mf (@gZero d1 T1 R) ≡μ @gZero d2 T2 R.
Proof. by []. Qed.

End giry_zero.

Section giry_prod.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.
Variable μ12 : giryM T1 R * giryM T2 R.

(* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
Definition gProd_ev := μ12.1 \x μ12.2.

HB.instance Definition _ := Measure.on gProd_ev.

Let gProd_setT : gProd_ev setT <= 1.
Proof.
rewrite -setXTT [leLHS]product_measure1E// -[leRHS]mule1.
by rewrite lee_pmul// sprobability_setT.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ gProd_ev gProd_setT.

Definition gProd : giryM (T1 * T2)%type R := gProd_ev.

(*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)

End giry_prod.

Section giry_prod_meas_fun.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

(* TODO: Clean up, maybe move elsewhere *)
Lemma subprobability_prod_setC (P : giryM T1 R * giryM T2 R) (A : set (T1 * T2)) :
  measurable A ->
  ((P.1 \x P.2) (~` A) = (P.1 \x P.2) [set: T1 * T2] - (P.1 \x P.2) A)%E.
Proof.
move=> mA; rewrite -(setvU A) measureU//= ?addeK ?setICl//.
- rewrite -/(gProd_ev _).
  exact: fin_num_measure.
- exact: measurableC.
Qed.

(* See Tobias Fritz,
   A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics,
   https://arxiv.org/abs/1908.07021  *)
Lemma gProd_meas_fun : measurable_fun [set: giryM T1 R * giryM T2 R] gProd.
Proof.
apply: (@giryM_cod_meas_fun _ _ _ _ R (@gProd _ _ _ _ R)) => /=.
rewrite measurable_prod_measurableType.
rewrite /gProd_ev.
apply: dynkin_induction => /=.
- by rewrite measurable_prod_measurableType.
- move=> _ _ [A1 mA1 [A2 mA2 <-]] [B1 mB1 [B2 mB2 <-]].
  exists (A1 `&` B1); first exact: measurableI.
  exists (A2 `&` B2); first exact: measurableI.
  by rewrite setXI.
- apply: (eq_measurable_fun (fun x : giryM T1 R * giryM T2 R => x.1 [set: T1] * x.2 [set: T2])%E).
    by move=> x _; rewrite -setXTT product_measure1E.
  by apply: emeasurable_funM => /=;
    apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //; exact: gEval_meas_fun.
- move=> _ [A mA [B mB <-]].
- apply: (eq_measurable_fun (fun x : giryM T1 R * giryM T2 R => x.1 A * x.2 B)%E).
    by move=> x _; rewrite product_measure1E.
  by apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //; exact: gEval_meas_fun.
- move=> S mS HS.
  apply: (eq_measurable_fun (fun x : giryM T1 R * giryM T2 R =>
      x.1 [set: T1] * x.2 [set: T2] - (x.1 \x x.2) S)%E).
    by move=> /= x _; rewrite subprobability_prod_setC// -setXTT product_measure1E.
  apply emeasurable_funB => //=.
  by apply: emeasurable_funM => //=; apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //;
    exact: gEval_meas_fun.
- move=> F mF tF Fn.
  apply: (eq_measurable_fun (fun x : giryM T1 R * giryM T2 R => \sum_(0 <= k <oo) (x.1 \x x.2) (F k)))%E.
    by move=> x _; rewrite measure_semi_bigcup//; exact: bigcup_measurable.
  exact: ge0_emeasurable_sum.
Qed.

End giry_prod_meas_fun.

Section giry_prod_int.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.

Lemma gProdInt1 (μ1 : giryM T1 R) (μ2 : giryM T2 R) (h : T1 * T2 -> \bar R) :
  measurable_fun [set: T1 * T2] h -> (forall x, 0 <= h x) ->
  gInt h (gProd (μ1, μ2)) = gInt (fun x => gInt (fun y => h (x, y)) μ2 ) μ1.
Proof. by move=> mh h0; rewrite /gInt/= /gProd_ev/= fubini_tonelli1. Qed.

Lemma gProdInt2 (μ1 : giryM T1 R) (μ2 : giryM T2 R) (h : T1 * T2 -> \bar R) :
  measurable_fun [set: T1 * T2] h -> (forall x, 0 <= h x) ->
  gInt h (gProd (μ1, μ2)) = gInt (fun y => gInt (fun x => h (x, y)) μ1 ) μ2.
Proof. by move=> mh h0; rewrite /gInt/=/gProd_ev/= fubini_tonelli2. Qed.

End giry_prod_int.
