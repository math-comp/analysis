From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets functions.
From mathcomp Require Import reals topology separation_axioms ereal sequences numfun measure measurable_realfun lebesgue_measure lebesgue_integral.
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
Definition gEvalPreImg (S : set T) := preimage_set_system setT (gEval S) measurable.

Definition giry_measurable := <<s \bigcup_(S in measurable) (gEvalPreImg S)>>.

(*  Axiom giry_measurable : set (set giryM). *)
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


Definition measure_eq {d : measure_display} {T : measurableType d} {R : realType} : giryM T R -> giryM T R -> Prop :=
  fun μ1 μ2 => forall (S : set T), measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).
Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡μ _) => symmetry; assumption : core.

Section giry_eval.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Context d (T : measurableType d) (R : realType).

(* TODO: Make hint *)
Lemma gEval_meas_fun (S : set T) (HmS : d.-measurable S) : measurable_fun [set: giryM T R] (gEval S).
Proof.
  apply: (@measurability giry_display _ (@giryM _ T R) _ setT (@gEval _ _ R S)).
    rewrite smallest_id; first reflexivity.
    exact: sigma_algebra_measurable.
  rewrite /giry_display.-measurable /= /giry_measurable /=.
  apply: subset_trans; last exact: sub_gen_smallest.
  apply: subset_trans; [ | apply bigcup_sup; exact HmS].
  exact: subset_refl.
Qed.

End giry_eval.


Section giry_integral.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Definition gInt (f : T -> \bar R) (mu : giryM T R) := \int[mu]_x f x.

Import HBNNSimple.

Lemma gInt_meas_fun (f : T -> \bar R) :
 (measurable_fun setT f) ->
 (forall x, 0 <= f x) ->
 measurable_fun setT (gInt f).
Proof.
  (*
    The idea is to reconstruct f from simple functions, then use
    measurability of gEval. See "Codensity and the Giry monad", Avery
   *)
  move => Hmf Hge0.
  pose g := nnsfun_approx measurableT Hmf.
  pose gE := (fun n => EFin \o g n).
  have HgEmeas n : measurable_fun [set: T] (gE n).
    rewrite /gE /=.
    exact/ measurable_EFinP.
  have HgEge0 n x : [set: T] x -> 0 <= (gE n) x
    by rewrite /gE /= // lee_fin.
  have HgEmono x : [set: T] x -> {homo gE^~ x : n m / (Order.le n m) >-> n <= m}.
    move => Hx n m Hnm.
    apply/ lefP.
    exact/ nd_nnsfun_approx.

  (* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
  have Hcvg := (cvg_monotone_convergence _ HgEmeas HgEge0 HgEmono).

  pose gEInt := fun n => fun μ => \int[μ]_x (gE n) x.
  have HgEIntmeas n : measurable_fun [set: giryM T R] (gEInt n).
    rewrite /gEInt /gE /=.
    eapply eq_measurable_fun.
    move => μ Hμ.
    rewrite integralT_nnsfun sintegralE //.
    apply emeasurable_fsum => // r.
    have Hrmeas : d.-measurable (g n @^-1` [set r]) by [].
    apply (measurable_funeM (r%:E)).
    have : measurable_fun [set: giryM T R] (fun x : giryM T R => x (g n @^-1` [set r])); auto.
    exact : eq_measurable_fun (gEval_meas_fun Hrmeas).
  (* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
  apply (emeasurable_fun_cvg _ (fun (μ : giryM T R) => \int[μ]_x f x) HgEIntmeas).
  move => μ Hμ.
  rewrite /gEInt /=.
  rewrite (eq_integral (fun x : T => limn (gE^~ x))); first exact: (Hcvg μ measurableT).
  move => x Hx.
  apply: esym.
  apply/ cvg_lim => //.
  apply/ cvg_nnsfun_approx => //.
 Qed.

End giry_integral.

(* TODO: Everything below needs to be cleaned up *)

Section giry_cod_meas.
Local Open Scope classical_set_scope.

 (* TODO: Either move this lemma to a more accessible location, or integrate within
    the proof below *)
Let measurability_aux d d' (aT : measurableType d) (rT : measurableType d')
  (f : aT -> rT) (G : set (set rT)) :
  @measurable _ rT = <<s G >> -> ( forall (S : set rT), G S -> @measurable _ aT (f @^-1` S)) ->
  measurable_fun setT f.
Proof.
  move => HG HS.
  apply/ (measurability (G := G)) => //.
  apply image_subP => ??.
  rewrite setTI.
  exact: HS.
Qed.

(* Adapted from mathlib induction_on_inter *)
(* TODO: Clean up proof, move lemma, change premises to use setX_closed like notations *)
Lemma dynkin_induction d {T : measurableType d} (G : set (set T)) (P : (set T) -> Prop) :
  @measurable _ T = <<s G >> ->
  setI_closed G ->
  (P setT) ->
  (forall S, G S -> P S) ->
  (forall S, measurable S -> P S -> P (setC S)) ->
  (forall F : sequences.sequence (set T),
      (forall n, measurable (F n)) ->
      trivIset setT F ->
      (forall n, P (F n)) -> P (\bigcup_k F k)) ->
  (forall S, <<s G >> S -> P S).
Proof.
  move => HG HIclosed HsetT Hgen HsetC Hbigcup S HGS.
  have HmS : measurable S; [ rewrite HG // |].
  have Haux : <<s G >> `<=` [set S : (set T) | measurable S /\ P S];
    last by apply Haux.
  apply lambda_system_subset; first by [].
  apply (dynkin_lambda_system ([set S0 | measurable S0 /\ P S0])).
  split; first by [].
    move=> ?[??].
    split; first exact: measurableC.
    exact: HsetC.
    move=> ?? Hm.
    split.
    apply bigcup_measurable; auto.
    move=> k Hk.
    apply Hm => //.
    apply Hbigcup => //.
    apply Hm.
    apply Hm.
    move=> ??.
    split; last by apply Hgen.
    rewrite HG //.
    apply sub_gen_smallest; auto.
    by [].
Qed.

Let eq_measurable {d} {T : measurableType d} [X Y : set T] :
  d.-measurable X -> Y = X -> d.-measurable Y.
Proof. by move=>?->. Qed.

Lemma giryM_cod_meas_fun {d1 : measure_display} {d2 : measure_display}
  {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}
  (f : T1 -> giryM T2 R) :
  (forall (S : set T2) (HmS : measurable S), measurable_fun setT (fun t => f t S)) ->
  measurable_fun setT f.
Proof.
  move => HS.
  eapply measurability_aux.
  {
    rewrite /giry_display.-measurable /= /giry_measurable.
    auto.
  }
  move => S [U HU1 HU2].
  specialize (HS U HU1).
  rewrite /gEvalPreImg /preimage_class in HU2.
  destruct HU2 as [B HB <-].
  specialize (HS measurableT B HB).
  rewrite setTI.
  rewrite -comp_preimage.
  apply (eq_measurable HS).
  rewrite setTI /gEval /= //.
Qed.

End giry_cod_meas.

Section giry_map.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).

Variables (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ1 : giryM T1 R).

Definition gMap_ev := pushforward μ1 Hmf.

HB.instance Definition _ := Measure.on gMap_ev.

Let gMap_setT : (gMap_ev setT <= 1)%E.
Proof.
  rewrite /gMap_ev /pushforward /=.
  apply sprobability_setT.
Qed.


HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gMap_ev gMap_setT.

Definition gMap : giryM T2 R := gMap_ev.

End giry_map.

Section giry_map_meas.


Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).

Lemma gMap_to_int (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ1 : giryM T1 R)
  (S : set T2) (HmS : measurable S):
    (gMap Hmf μ1 S = \int[μ1]_x (\1_S (f x))%:E)%E.
Proof.
rewrite -[in LHS](setIT S) -[LHS]integral_indic//.
rewrite ge0_integral_pushforward//.
  exact/measurable_EFinP/measurable_indic.
by move=> y _; rewrite lee_fin.
Qed.

Lemma gMap_meas_fun (f : T1 -> T2) (Hmf : measurable_fun setT f):
  measurable_fun setT (gMap Hmf (R:= R)).
Proof.
  rewrite /gMap.
  apply (@giryM_cod_meas_fun _ _ (giryM T1 R)); simpl.
  intros S HmS.
  rewrite /gMap_ev /pushforward /=.
  apply gEval_meas_fun.
  rewrite -(setTI (f @^-1` S)).
  apply Hmf; auto.
Qed.


Lemma gMapInt (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ : giryM T1 R)
  (h : T2 -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
  gInt h (gMap Hmf μ) = gInt (h \o f) μ.
Proof.
exact: ge0_integral_pushforward.
Qed.


End giry_map_meas.

Section giry_ret.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).


Definition gRet (x:T) : giryM T R := (dirac^~ R x)%R.

Lemma gRet_meas_fun : measurable_fun setT gRet.
Proof.
  rewrite /gRet /dirac.
  apply giryM_cod_meas_fun; simpl.
exact: measurable_fun_dirac.
Qed.


Lemma gRetInt (x : T) (h : T -> \bar R) (H : measurable_fun setT h):
    gInt h (gRet x) = h x.
Proof.
  rewrite /gInt.
  have Haux : (forall S, d.-measurable S -> S `<=` [set : T] -> gRet x S = dirac x S); auto.
  erewrite (eq_measure_integral _ Haux).
  rewrite integral_dirac; auto.
  rewrite diracT mul1e //.
Qed.

Lemma gRetInt_rw (x : T) (h : T -> \bar R) (H : measurable_fun setT h):
    \int[gRet x]_x h x = h x.
Proof.
  apply gRetInt; auto.
Qed.


End giry_ret.


Section giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable (M : giryM (giryM T R) R).

Definition gJoin_ev (S : set T) := gInt (gEval S) M.

Let gJoin0 : gJoin_ev set0 = 0%E.
Proof.
  rewrite /gJoin_ev /gEval.
  apply integral0_eq.
  auto.
Qed.

Let gJoin_ge0 A : (0 <= gJoin_ev A)%E.
Proof.
  rewrite /gJoin_ev.
  apply integral_ge0.
  auto.
Qed.

(* TODO: Cleaner proof? *)
Let gJoin_semi_sigma_additive : semi_sigma_additive (gJoin_ev).
Proof.
  rewrite /gJoin_ev /gInt.
  rewrite /gEval /=.
  intros F HF HFTriv HcupF.
  eapply cvg_trans.
  {
    erewrite eq_cvg; last first.
    intros ?.
    rewrite -ge0_integral_sum; auto.
    by reflexivity.
    intros.
    apply gEval_meas_fun; auto.
    auto.
  }
  eapply cvg_trans.
  {
    apply cvg_monotone_convergence; auto.
    {
      intros n.
      apply emeasurable_fun_sum.
      intros.
      apply gEval_meas_fun; auto.
    }
    {
      intros n ? ?.
      rewrite sume_ge0; auto.
    }
    intros ? ?.
    intros ? ? ?.
    rewrite ereal_nondecreasing_series //.
  }
  simpl.
  have -> :(\int[M]_x x (\bigcup_n F n) = \int[M]_x \big[+%R/0%R]_(0 <= k <oo) x (F k));
    last by [].
  apply eq_integral.
  intros μ Hμ'.
  simpl.
  apply/esym/cvg_lim => //.
  exact: measure_sigma_additive.
Qed.

(* TODO: Cleaner proof? *)
Let gJoin_setT : (gJoin_ev setT <= 1)%E.
Proof.
  rewrite /gJoin_ev.
  apply (@Order.le_trans _ _ (1%:E * (M setT))); last first.
  {
    rewrite mul1e.
    apply sprobability_setT.
  }
  eapply Order.le_trans; last first.
  {
    apply (@integral_le_bound _ _ R M _ (gEval setT) 1); auto.
    apply gEval_meas_fun; auto.
    apply (aeW M).
    intros ??.
    rewrite gee0_abs; auto.
    rewrite /gEval.
    apply (@sprobability_setT d T R x).
  }
  apply ge0_le_integral; auto.
  apply gEval_meas_fun; auto.
  intros; apply abse_ge0.
  apply (@measurableT_comp _ _ _ _ _ _ abse).
  apply abse_measurable.
  apply gEval_meas_fun; auto.
  intros ??.
  rewrite gee0_abs; auto.
Qed.

HB.instance Definition _ := isMeasure.Build d _ R gJoin_ev gJoin0 gJoin_ge0 gJoin_semi_sigma_additive.
HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gJoin_ev gJoin_setT.

Definition gJoin : giryM T R := gJoin_ev.

End giry_join.


Section giry_join_meas_fun.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context d (T : measurableType d) (R : realType).


Lemma gJoin_meas_fun : measurable_fun setT (@gJoin d T R).
Proof.
  apply (@giryM_cod_meas_fun _ _ (giryM (giryM T _)_)); simpl.
  rewrite /gJoin_ev.
  intros S HmS.
  eapply (@gInt_meas_fun _ _ _ (gEval S)).
  Unshelve.
  apply gEval_meas_fun; auto.
  auto.
Qed.

Import HBNNSimple.

(* TODO: Messy proof, cleanup *)
Lemma gJoinSInt (M : giryM (giryM T R) R) (h : {nnsfun T >-> R}) :
  sintegral (gJoin M) h = \int[M]_μ sintegral μ h.
Proof.
  etransitivity; last first.
  {
    eapply eq_integral.
    intros μ Hμ.
    rewrite sintegralE.
    by reflexivity.
  }
  simpl.
  rewrite ge0_integral_fsum; auto; last first.
  {
    intros ???.
    apply nnsfun_mulemu_ge0.
  }
  {
    intros ?.
    apply measurable_funeM.
    apply gEval_meas_fun; auto.
  }
  rewrite sintegralE /=.
  have Heq x : (x%:E * gJoin_ev M (h @^-1` [set x]) = \int[M]_μ (x%:E * μ (h @^-1` [set x])))%E.
    rewrite integralZl//.
    have := finite_measure_integrable_cst M 1.
    apply: le_integrable => //; first exact: gEval_meas_fun.
    move=> mu _ /=.
    rewrite normr1 gee0_abs// (le_trans _ (@sprobability_setT _ _ _ mu))//.
    by rewrite le_measure// ?inE.
  apply: fsbigop.eq_fsbigr => //.
Qed.

(* TODO: Messy proof, cleanup *)

Lemma gJoinInt (M : giryM (giryM T R) R)
    (h : T -> \bar R) (mh : measurable_fun setT h) (h_ge0 : forall x, 0 <= h x) :
  gInt h (gJoin M) = gInt (fun μ : giryM T R => \int[μ]_x h x) M.
Proof.
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
Context d1 d2
 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).

Definition gBind (f : T1 -> giryM T2 R) (H : measurable_fun setT f) : giryM T1 R -> giryM T2 R :=
  (gJoin (R := R)) \o (gMap H (R := R)).


Lemma gBind_meas_fun (f : T1 -> giryM T2 R) (H : measurable_fun setT f) :  measurable_fun setT (gBind H).
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by apply subsetT. }
  { by apply gJoin_meas_fun. }
  { by apply gMap_meas_fun. }
Qed.


End giry_bind.


Section giry_bind_meas_fun.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).


Lemma gBindInt_meas_fun (μ : giryM T1 R) (f : T1 -> giryM T2 R) (H : measurable_fun setT f)
  (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x) :
    measurable_fun setT (fun x => gInt h (f x)).
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT _ _ f).
  { by eapply @measurableT. }
  { by apply subsetT. }
  { by apply gInt_meas_fun. }
  { by apply H. }
Qed.

Lemma gBindInt :
  forall (μ : giryM T1 R) (f : T1 -> giryM T2 R) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x),
    gInt h (gBind H μ) = gInt (fun x => gInt h (f x)) μ.
Proof.
  intros ??????.
  rewrite /gBind /=.
  rewrite gJoinInt; auto.
  rewrite gMapInt; auto.
  apply gInt_meas_fun; auto.
  intros.
  apply integral_ge0; auto.
Qed.

Lemma gBindInt_rw (μ : giryM T1 R) (f : T1 -> giryM T2 R) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x) :
  \int[gBind H μ]_y h y = \int[μ]_x \int[f x]_y  h y.
Proof.
  apply gBindInt; auto.
Qed.

End giry_bind_meas_fun.

Section giry_monad.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3).
Context (R : realType).

Lemma gJoin_assoc : forall (x : giryM (giryM (giryM T1 R) R) R),
    ((@gJoin _ _ R) \o (gMap (@gJoin_meas_fun _ _ R))) x ≡μ ((@gJoin _ _ R) \o (@gJoin _ _ R)) x.
Proof.
  intros μ S HmS.
  rewrite /= /gJoin_ev.
  rewrite gMapInt //.
  rewrite gJoinInt //.
  all: apply gEval_meas_fun; auto.
Qed.


Lemma gJoin_id1 : forall (x : giryM T1 R),
    ((@gJoin _ _ R) \o (gMap (@gRet_meas_fun _ _ R))) x ≡μ ((@gJoin _ _ R) \o (@gRet _ _ R)) x.
Proof.
  intros μ S HmS.
  rewrite /= /gJoin_ev; simpl.
  rewrite gMapInt; auto; [|apply gEval_meas_fun; auto].
  rewrite gRetInt; auto; [|apply gEval_meas_fun; auto].
  rewrite /gInt /gEval /gRet /= /dirac.
  rewrite integral_indic; auto.
  rewrite setIT //.
Qed.

Lemma gJoin_id2 : forall (x : giryM (giryM T1 R) R) (f : T1 -> T2) (H : measurable_fun setT f),
    ((@gJoin _ _ R) \o gMap (gMap_meas_fun H)) x ≡μ (gMap H \o (@gJoin _ _ R)) x.
Proof.
  intros μ f Hmf S HmS.
  rewrite /= /gJoin_ev; simpl.
  rewrite gMapInt; auto.
  apply gEval_meas_fun; auto.
Qed.


End giry_monad.

Section giry_zero_def.
Local Open Scope classical_set_scope.
Context d1 (T1 : measurableType d1) (R : realType).
Definition gZero := mzero : giryM T1 R.
Lemma gZero_eval : forall S (H: d1.-measurable S), gZero S = (0% E).
Proof.
  intros ??.
  rewrite /gZero/mzero //.
Qed.
End giry_zero_def.


Section giry_zero.
Local Open Scope classical_set_scope.

Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

Lemma gZero_map : forall (f : T1 -> T2) (H : measurable_fun setT f),
  gMap H (@gZero d1 T1 R) ≡μ (@gZero d2 T2 R).
Proof.
  intros f H S HmS.
  rewrite /=/gMap_ev /mzero //.
Qed.

End giry_zero.



Section giry_prod.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).
Variable (μ12 : giryM T1 R * giryM T2 R).

(* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
Definition gProd_ev := (μ12.1 \x μ12.2)%E.

HB.instance Definition _ := Measure.on gProd_ev.

Let gProd_setT : (gProd_ev setT <= 1)%E.
Proof.
rewrite -setXTT [leLHS]product_measure1E// -[1%E]mule1.
by rewrite lee_pmul// sprobability_setT.
Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gProd_ev gProd_setT.
Definition gProd : giryM (T1*T2)%type R := gProd_ev.

(*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)


End giry_prod.


Section giry_prod_meas_fun.
Local Open Scope classical_set_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

(* TODO: Clean up, maybe move elsewhere *)
Lemma subprobability_prod_setC
  (P : giryM T1 R * giryM T2 R) (A : set (prod T1 T2)) :
  measurable A ->
  ((P.1 \x P.2) (~` A) = (P.1 \x P.2) [set: T1 * T2] - (P.1 \x P.2) A)%E.
Proof.
move=> mA.
rewrite -(setvU A) measureU//= ?addeK ?setICl//.
- rewrite -/(gProd_ev _).
  exact: fin_num_measure.
- exact: measurableC.
Qed.

(*
   See "A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics", Fritz

   TODO: Clean up proof
 *)
Lemma gProd_meas_fun : measurable_fun setT (@gProd d1 d2 T1 T2 R).
Proof.
  simpl.
  apply (@giryM_cod_meas_fun _ _ _ _ R (@gProd _ _ _ _ R)).

  rewrite measurable_prod_measurableType; simpl.
  rewrite /gProd_ev.
  apply dynkin_induction; simpl.
  - rewrite measurable_prod_measurableType //.
  - intros A B [A1 HA1 [A2 HA2 <-]] [B1 HB1 [B2 HB2 <-]].
    exists (A1 `&` B1); first exact: measurableI.
    exists (A2 `&` B2); first exact: measurableI.
    by rewrite setXI.
  - eapply eq_measurable_fun; [intros ??; rewrite -setXTT product_measure1E // |].
    apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //;
    exact: gEval_meas_fun.
  - intros S [A HA [B HB <-]].
    eapply eq_measurable_fun; [intros ??; rewrite product_measure1E // |].
    apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //;
    exact: gEval_meas_fun.
  - intros S HmS HS.
    eapply (eq_measurable_fun).
      intros ??. simpl in x. rewrite (subprobability_prod_setC x).
      rewrite -setXTT product_measure1E; first by reflexivity.
      by [].
      by [].
      by [].
    apply emeasurable_funB; auto; simpl.
    apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (gEval _)) => //;
    exact: gEval_meas_fun.
  - intros F HmF HF Hn.
    eapply eq_measurable_fun.
      intros ??.
      rewrite measure_semi_bigcup //.
      apply bigcup_measurable; auto.
      simpl.
      apply ge0_emeasurable_sum; auto.
Qed.

End giry_prod_meas_fun.


Section giry_prod_int.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).

Lemma gProdInt1 (μ1 : giryM T1 R) (μ2 : giryM T2 R)
  (h : (T1 * T2)%type -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
  gInt h (gProd (μ1, μ2)) = gInt (fun x => gInt (fun y => h (x, y)) μ2 ) μ1.
Proof.
  rewrite /gInt/=/gProd_ev/=.
  rewrite fubini_tonelli1; auto.
Qed.

Lemma gProdInt2 (μ1 : giryM T1 R) (μ2 : giryM T2 R)
  (h : (T1 * T2)%type -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
  gInt h (gProd (μ1, μ2)) = gInt (fun y => gInt (fun x => h (x, y)) μ1 ) μ2.
Proof.
  rewrite /gInt/=/gProd_ev/=.
  rewrite fubini_tonelli2; auto.
Qed.

End giry_prod_int.
