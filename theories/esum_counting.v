From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra functions.
From mathcomp Require Import xfinmap constructive_ereal reals discrete.
From mathcomp Require Import realseq realsum.
From mathcomp Require Import topology esum sequences normedtype ereal.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import numfun measurable_realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import counting_distr.
From mathcomp Require Import random_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.  (* remove this line when requiring MathComp >= 2.6 *)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Notation simpm := Monoid.simpm.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Import HBNNSimple.
Import MeasurableR.

(* -------------------------------------------------------------------- *)
(* TODO: PR.  This generalizes `esum_bigcupT` (esum.v) *)
Lemma esum_bigcup_set {R : realType} (T1 T2 : choiceType) (K : set T1)
    (J : T1 -> set T2) (a : T2 -> \bar R) :
    trivIset setT J -> (forall x, (0 <= a x)%E) ->
  (\esum_(i in \bigcup_(k in K) J k) a i =
   \esum_(k in K) \esum_(j in J k) a j)%E.
Proof.
move=> tJ a0; rewrite esum_esum//; apply: reindex_esum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2] /set_mem/= [Ki1 Jij1] /set_mem/= [Ki2 Jij2] /= j12.
  have iE : i1 = i2.
    by apply: (tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
  by rewrite iE j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

(* -------------------------------------------------------------------- *)
Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} (T : choiceType) (f : T -> \bar R) :
  (\esum_(x in [set: discrete_measurable_space T]) f x
     = \esum_(x in [set: T]) f x)%E.
Proof.
apply: (@reindex_esum R T (discrete_measurable_space T)
          [set: T] [set: discrete_measurable_space T] id f); split.
- by move=> x.
- by move=> x y _ _.
- by move=> x _; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Section Counting.
Context d (T : measurableType d) (R : realType).
Hypothesis msingl : forall i : T, measurable [set i].

Lemma counting_esum_cst (c : R) (A : set T) : (0 <= c)%R ->
  (c%:E * @counting T R A = \esum_(x in A) c%:E)%E.
Proof.
move=> c0.
have [-> | c_neq] := eqVneq c 0%R.
  by rewrite mul0e; apply/esym/esum1.
have c_pos : (0 < c)%R by rewrite lt_def c_neq.
have [finA|infA] := pselect (finite_set A).
+ rewrite /counting (asboolT finA).
  rewrite esum_fset// fsbig_finite//=.
  rewrite sumEFin big_const_seq count_predT iter_addr addr0.
  by rewrite -EFinM mulr_natr.
+ rewrite /counting asboolF//=.
  rewrite mulry gtr0_sg// mul1e.
  apply/esym/eqyP => r r0.
  have [B BA Brc] := infinite_set_fset (Num.Def.truncn (c^-1 * r)).+1 infA.
  apply: esum_ge => // ; exists [set` B].
    by split=> //; apply/subsetP => x; rewrite inE => /BA.
  rewrite fsbig_finite//= set_fsetK sumEFin big_const_seq count_predT.
  rewrite iter_addr addr0 -mulr_natr lee_fin -ler_pdivrMl//.
  apply: (@le_trans _ _ (((Num.Def.truncn (c^-1 * r)).+1)%:R)).
    exact: ltW (truncnS_gt _).
  rewrite ler_nat.
  exact: Brc.
Qed.

Lemma sintegral_counting_esum (h : {nnsfun T >-> R}) :
  (sintegral (@counting T R) h = \esum_(x in [set: T]) (h x)%:E)%E.
Proof.
rewrite sintegralE //=.
transitivity (\sum_(c \in range h)
                \esum_(x in (h @^-1` [set c] : set T)) (h x)%:E)%E.
+ apply: eq_fsbigr => c /set_mem/= -[x _ <-{c}].
  rewrite counting_esum_cst//.
  by apply: (eq_esum _ (fun=> (h x)%:E)) => x0 ->.
+ rewrite -esum_fset//.
  + by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
  rewrite -esum_bigcup_set.
  + exact: trivIset_preimage1.
  + by move=> ?; rewrite lee_fin.
  + suff -> : \bigcup_(c in range h) h @^-1` [set c] = [set: T] by [].
    apply/seteqP; split => [//|y _].
    by exists (h y); [exists y|].
Qed.

Lemma measurable_fin_set (A : set T) :
  finite_set A -> measurable A.
Proof.
move=> finA; rewrite -[A]bigcup_id.
by apply: fin_bigcup_measurable => // i _; exact: msingl.
Qed.

Lemma integral_set1 f i :
  (\int[@counting T R]_(x in [set i]) f x = f i)%E.
Proof.
transitivity (\int[@counting T R]_(x in [set i]) cst (f i) x)%E.
+ by apply: eq_integral => x /set_mem/= ->.
rewrite (integral_cst _ (msingl i)) -[X in _ = X](mule1 (f i)).
congr (f i * _)%E => /=.
rewrite /counting (asboolT (finite_set1 i)).
by rewrite fset_set1 cardfs1.
Qed.

Lemma integral_sum f :
  measurable_fun [set: T] f ->
  forall A : set T, finite_set A ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_(x in A) f x = \sum_(x \in A) f x)%E.
Proof.
move=> mf A finA f0.
rewrite fsbig_finite//=.
rewrite (eq_bigr (fun i => (\int[@counting T R]_(x in [set i]) f x)%E)).
+ by move => ??;rewrite integral_set1.
rewrite -ge0_integral_bigsetU //=.
- exact: fset_uniq.
- by move=> i j _ _ [x [-> ->]].
- exact: measurable_funTS.
- by rewrite (@bigsetU_fset_set _ _ _ _ finA) bigcup_id.
Qed.

Lemma integral_counting_esum (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_x f x = \esum_(x in [set: T]) f x)%E.
Proof.
move=> mf f0 ; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite ge0_integralTE //=.
  apply: ge_ereal_sup => /= _ [h /= hf] <-.
  rewrite sintegral_counting_esum.
  apply: le_esum => x _; exact: hf.
- rewrite ge0_esum //; apply: ge_ereal_sup => /= _ [A [finA _] <-].
  rewrite -integral_sum//.
  apply: ge0_subset_integral => //.
  exact : (measurable_fin_set finA).
Qed.

Lemma integral_counting_esum_set (A : set T) (f : T -> \bar R) :
  measurable A ->
  measurable_fun [set: T] f ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_(x in A) f x = \esum_(x in A) f x)%E.
Proof.
move=> mA mf f0; rewrite integral_mkcond integral_counting_esum.
- by apply/(measurable_restrict _ mA measurableT); rewrite setTI; exact: measurable_funTS.
- by move=> x; rewrite patchE; case: ifP.
- rewrite [RHS]esum_mkcond; apply: eq_esum => x _.
  by rewrite patchE.
Qed.

End Counting.

(* -------------------------------------------------------------------- *)
Section SubDistribution.
Context (R : realType) (T : choiceType) (mu: R.-distr T).

Definition P (S : set (discrete_measurable_space T)) :=
    \esum_(x in S) (EFin \o mu) x.

Let P0 : P set0 = 0%E.
Proof. by rewrite /P esum_set0. Qed.

Let P_ge0 (S : set (discrete_measurable_space T)) : (0 <= P S)%E.
Proof. by apply: esum_ge0 => x _; rewrite lee_fin. Qed.

Let P_sigma_additive : semi_sigma_additive P.
Proof.
move=> F _ tF _.
have -> : P (\bigcup_n F n) = (\sum_(i <oo) P (F i))%E.
  rewrite nneseries_esumT; first by move=> n; exact: P_ge0.
  apply: esum_bigcup_set => //.
  by move=> x; rewrite lee_fin.
apply: cvg_toP => //.
apply: is_cvg_nneseries => n _ _; rewrite /P.
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ P
  P0 P_ge0 P_sigma_additive.

Let P_setT : (P [set: discrete_measurable_space T] <= 1)%E.
Proof. by rewrite /P esum_setT_discrete; exact: mu_sum_le1. Qed.

HB.instance Definition _ :=
  @Measure_isSubProbability.Build _ _ R P P_setT.

End SubDistribution.

(* -------------------------------------------------------------------- *)
(* TODO: PR. *)
Section integral_density.
Context d {T : measurableType d} {R : realType}.
Context (m1 m2 : {measure set T -> \bar R}) (h : T -> R).

Hypothesis h_mesurable : measurable_fun [set: T] h.
Hypothesis h_pos : forall x, (0 <= h x)%R.
Hypothesis H : forall A, measurable A -> m2 A = \int[m1]_(x in A) (h x)%:E.

Lemma integral_indicM (A : set T) : measurable A ->
  \int[m1]_x ((\1_A x)%:E * (h x)%:E) = m2 A.
Proof.
move=> mA; rewrite H// [RHS]integral_mkcond; apply: eq_integral => x _.
rewrite patchE indicE; case: ifP => _; first by rewrite mul1e.
by rewrite mul0e.
Qed.

Lemma integral_termE (r : R) (A : set T) : measurable A -> (0 <= r)%R ->
  \int[m1]_x (r%:E * ((\1_A x)%:E * (h x)%:E)) = r%:E * m2 A.
Proof.
move=> mA r0; rewrite ge0_integralZl//=.
- apply: emeasurable_funM => //; by apply /measurable_EFinP.
- move=> x _; apply: mule_ge0; rewrite lee_fin//.
- by rewrite integral_indicM.
Qed.

Lemma sintegral_density (g : {nnsfun T >-> R}) :
  sintegral m2 g = \int[m1]_x ((g x)%:E * (h x)%:E).
Proof.
transitivity (\sum_(r \in range g)
    \int[m1]_x (r%:E * ((\1_(g @^-1` [set r]) x)%:E * (h x)%:E))).
+ rewrite sintegralE; apply: eq_fsbigr => r /set_mem[x0 _ <-].
  by rewrite integral_termE//.
transitivity (\int[m1]_x (\sum_(r \in range g)
    (r%:E * ((\1_(g @^-1` [set r]) x)%:E * (h x)%:E)))).
+ rewrite ge0_integral_fsum//=.
+ move=> r; apply: measurable_funeM.
  by apply: emeasurable_funM => //;apply/measurable_EFinP.
  + move => r x ?.
    have [r0|r0] := leP 0%R r.
    + apply: mule_ge0; first by rewrite lee_fin.
      by apply: mule_ge0; rewrite lee_fin//.
    + by rewrite preimage_nnfun0 // indic0/= mul0e mule0.
apply: eq_integral => x _.
transitivity ((\sum_(r \in range g) (r * (\1_(g @^-1` [set r]) x * h x)))%:E).
  by rewrite -fsumEFin.
rewrite -EFinM; congr (_%:E).
rewrite [in RHS](fimfunE g) mulr_fsuml.
by apply: eq_fsbigr => r _; rewrite mulrA.
Qed.

Lemma integral_density (f : T -> \bar R) :
    measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  \int[m2]_x f x = \int[m1]_x (f x * (h x)%:E).
Proof.
move=> mf f0.
pose g := nnsfun_approx measurableT mf.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (EFin \o g n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n p / (n <= p)%O >-> n <= p}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n => \int[m2]_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[m1]_x (gE n x * (h x)%:E))).
  apply: congr_lim; apply/funext => n.
  by rewrite integralT_nnsfun sintegral_density.
have mgEh n : measurable_fun [set: T] (fun x => gE n x * (h x)%:E).
  apply: emeasurable_funM;  by apply/measurable_EFinP.
have gEh_ge0 n x : 0 <= gE n x * (h x)%:E.
  by apply: mule_ge0; rewrite lee_fin//.
have nd_gEh x : {homo (fun n => gE n x * (h x)%:E) : n p / (n <= p)%O >-> n <= p}.
  move=> p q pq; apply: lee_wpmul2r; first by rewrite lee_fin.
  exact: nd_gE.
rewrite -monotone_convergence//.
apply: eq_integral => x _.
apply: cvg_lim => //; apply: cvgeZr => //.
exact: cvg_nnsfun_approx.
Qed.

End integral_density.

(* -------------------------------------------------------------------- *)
Section maxe_distr.
Context (R : realType) (T : choiceType) (mu : R.-distr T).

Lemma maxe_distrM (a : \bar R) x :
  (maxe (a * (mu x)%:E) 0 = maxe a 0 * (mu x)%:E)%E.
Proof.
rewrite [in LHS]muleC [in RHS]muleC maxe_pMr.
- by [].
- by rewrite lee_fin.
- by rewrite mule0.
Qed.

Lemma maxeN_distrM (a : \bar R) x :
  (maxe (- (a * (mu x)%:E)) 0 = maxe (- a) 0 * (mu x)%:E)%E.
Proof. by rewrite -mulNe maxe_distrM. Qed.

End maxe_distr.

(* -------------------------------------------------------------------- *)
Section Expectation.
Context (R : realType) (T : choiceType) (mu : R.-distr T).

Lemma integral_espe (f : T -> \bar R) : (forall x, 0 <= f x)%E ->
  \int[P mu]_x f x = espe mu f.
Proof.
move=> f0.
rewrite (@integral_density _ (discrete_measurable_space T) R
          (@counting (discrete_measurable_space T) R) (P mu) mu)//=.
+ move=> A _; rewrite /P integral_counting_esum_set; try by [].
  by move=> x; rewrite lee_fin.
rewrite /espe -esum_setT_discrete integral_counting_esum; try by [].
by move=> x; apply: mule_ge0; [exact: f0|rewrite lee_fin].
Qed.

Lemma espeE (f : T ->  R) :  ('E_(P mu)[f] = espe mu (EFin \o f)).
Proof.
rewrite expectation_def integralE /espe esumE; congr (_ - _).
- transitivity (espe mu ((EFin \o f)^\+)).
    by rewrite integral_espe// => x; exact: funepos_ge0.
  by rewrite /espe; apply: eq_esum => x _; rewrite !funeposE maxe_distrM.
- transitivity (espe mu ((EFin \o f)^\-)).
    by rewrite integral_espe// => x; exact: funeneg_ge0.
  by rewrite /espe; apply: eq_esum => x _; rewrite !funenegE maxeN_distrM.
Qed.

End Expectation.

(* -------------------------------------------------------------------- *)
Section pmf_subdistribution.
Context d (T : measurableType d) (R : realType) (Pr : probability T R).
Variable X : {RV Pr >-> R}.

Let mX1 (r : R) : measurable (X @^-1` [set r]).
Proof. exact: measurable_funPTI. Qed.

Lemma pmf_fin_bigcup (J : seq R) : uniq J ->
  \sum_(j <- J) (pmf X j)%:E
    = Pr (\bigcup_(j in [set` J]) X @^-1` [set j]).
Proof.
move=> uJ.
rewrite (@measure_fin_bigcup _ _ _ Pr _ [set` J] (fun j : R => X @^-1` [set j])).
- exact: finite_seq.
- exact: trivIset_preimage1.
- by move=> j _; exact: mX1.
- rewrite fsbig_seq//; apply: eq_fsbigr => j _.
  by rewrite /pmf fineK// fin_num_measure.
Qed.

Lemma pmf_uniq_le1 (J : seq R) : uniq J -> (\sum_(j <- J) pmf X j <= 1)%R.
Proof.
move=> uJ; rewrite -lee_fin -sumEFin pmf_fin_bigcup//.
apply: probability_le1; apply: fin_bigcup_measurable.
- exact: finite_seq.
- by move=> j _; exact: mX1.
Qed.

HB.instance Definition _ :=
  @isSubDistr.Build R R (pmf X) (@pmf_ge0 _ _ _ Pr X) pmf_uniq_le1.

End pmf_subdistribution.

(* -------------------------------------------------------------------- *)
Section pr_pmf.
Context d (T : pmeasurableType d) (R : realType) (Pr : probability T R).
Variable X : {dRV Pr >-> R}.

Local Notation pmfX := (@pmf _ _ _ Pr X).

Lemma pmf_out (r : R) : ~ range X r -> pmfX r = 0%R.
Proof. by move=> nr; rewrite /pmf preimage10// measure0. Qed.

Lemma esum_pmf_range :
  esum [set: R] (EFin \o pmfX) = \esum_(r in range X) (pmfX r)%:E.
Proof.
rewrite (esumID (range X) [set: R] (EFin \o pmfX)).
- by move=> i _; rewrite lee_fin pmf_ge0.
- rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
  by rewrite pmf_out.
Qed.

Lemma esum_pmf_dRV : esum [set: R] (EFin \o pmfX) = 1.
Proof.
rewrite esum_pmf_range.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X)
          (fun r => (pmfX r)%:E))//.
transitivity (\esum_(k in dRV_dom X) enum_prob X k).
  apply: eq_esum => k kd.
  by rewrite /enum_prob patchE mem_set// /pmf fineK// fin_num_measure.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- by move=> n _; rewrite /enum_prob patchE; case: ifP.
- rewrite eseries_mkcond -[RHS](@sum_enum_prob _ _ _ _ _ Pr X measurable_set1).
  apply: eq_eseriesr => k _.
  case: ifPn => // kd.
  by rewrite /enum_prob patchE (negbTE kd).
Qed.

Lemma esum_pmf_set_dRV (A : set R) : measurable A ->
  \esum_(r in A) (pmfX r)%:E = distribution Pr X A.
Proof.
move=> mA.
pose g (r : R) := if r \in A then (pmfX r)%:E else 0.
have g0 r : ~ range X r -> g r = 0.
  by move=> nr; rewrite /g pmf_out//; case: ifP.
transitivity (\esum_(r in [set: R]) g r); first exact: esum_mkcond.
transitivity (\esum_(r in range X) g r).
  rewrite (esumID (range X) [set: R] g).
  - move=> i _; rewrite /g; case: ifPn => // _.
    by rewrite lee_fin pmf_ge0.
  - rewrite setTI [X in _ + X]esum1 ?adde0//= => r [_ /= nr].
    exact: g0.
rewrite (reindex_esum (dRV_dom X) (range X) (dRV_enum X) g)//.
rewrite -[X in \esum_(k in X) _]set_mem_set -nneseries_esum.
- move=> n _; rewrite /g; case: ifPn => // _.
  by rewrite lee_fin pmf_ge0.
- rewrite eseries_mkcond.
  rewrite [RHS](@distribution_dRV _ _ _ _ _ Pr X measurable_set1 A mA).
  apply: eq_eseriesr => k _.
  rewrite /g /enum_prob patchE diracE; case: ifPn => kd; last by rewrite mul0e.
  rewrite /pmf fineK ?fin_num_measure//.
  by case: ifPn => _; rewrite ?mule1 ?mule0.
Qed.

Lemma esum_pmf_pred (A : set R) :
  esum [set: R] (EFin \o (fun r : R => ((r \in A)%:R * pmfX r)%R))
    = \esum_(r in A) (pmfX r)%:E.
Proof.
rewrite [RHS]esum_mkcond; apply: eq_esum => r _.
by case: (r \in A) => /=; rewrite ?mul1r ?mul0r.
Qed.

Lemma pr_pmf_dRV (A : set R) : measurable A ->
  (\P_[pmfX] (fun r => r \in A))%:E = distribution Pr X A.
Proof.
by move=> mA; rewrite /pr esum_pmf_pred esum_pmf_set_dRV// fineK ?fin_num_measure.
Qed.

End pr_pmf.

(* -------------------------------------------------------------------- *)
Section espe_pmf.
Context d (T : pmeasurableType d) (R : realType) (Pr : probability T R).
Variable X : {dRV Pr >-> R}.

Local Notation pmfX := (@pmf _ _ _ Pr X).

Lemma distribution_integral_counting (A : set R) : measurable A ->
  distribution Pr X A = \int[@counting R R]_(r in A) (pmfX r)%:E.
Proof.
move=> mA; rewrite integral_counting_esum_set.
- exact: measurable_set1.
- exact: mA.
- by apply/measurable_EFinP; exact: pmf_measurable.
- by move=> r; rewrite lee_fin pmf_ge0.
- by rewrite esum_pmf_set_dRV.
Qed.

Lemma ge0_espe_pmf (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall r, 0 <= f r) ->
  espe pmfX f = \int[Pr]_w f (X w).
Proof.
move=> mf f0.
have mfh : measurable_fun [set: R] (fun r => f r * (pmfX r)%:E).
  by apply: emeasurable_funM => //; apply/measurable_EFinP; exact: pmf_measurable.
have fh0 r : 0 <= f r * (pmfX r)%:E.
  by apply: mule_ge0; [exact: f0|rewrite lee_fin pmf_ge0].
have step1 : espe pmfX f = \int[@counting R R]_r (f r * (pmfX r)%:E).
  rewrite /espe -integral_counting_esum//; exact: measurable_set1.
have step2 : \int[distribution Pr X]_r f r
           = \int[@counting R R]_r (f r * (pmfX r)%:E).
  apply: (@integral_density _ R R (@counting R R) (distribution Pr X) pmfX).
  - exact: pmf_measurable.
  - exact: pmf_ge0.
  - exact: distribution_integral_counting.
  - exact: mf.
  - exact: f0.
have step3 : \int[distribution Pr X]_r f r = \int[Pr]_w f (X w).
  by rewrite /distribution ge0_integral_pushforward.
by rewrite step1 -step2 step3.
Qed.

Lemma espe_pmf_dRV : espe pmfX EFin = 'E_Pr[X].
Proof.
have mE : measurable_fun [set: R] (EFin : R -> \bar R) by apply/measurable_EFinP.
rewrite /espe esumE expectation_def integralE; congr (_ - _).
- transitivity (espe pmfX (EFin^\+)).
    by rewrite /espe; apply: eq_esum => r _; rewrite !funeposE maxe_distrM.
  rewrite ge0_espe_pmf.
  + exact: measurable_funepos.
  + by move=> r; exact: funepos_ge0.
  + by apply: eq_integral => w _; rewrite !funeposE.
- transitivity (espe pmfX (EFin^\-)).
    by rewrite /espe; apply: eq_esum => r _; rewrite !funenegE maxeN_distrM.
  rewrite ge0_espe_pmf.
  + exact: measurable_funeneg.
  + by move=> r; exact: funeneg_ge0.
  + by apply: eq_integral => w _; rewrite !funenegE.
Qed.

End espe_pmf.
