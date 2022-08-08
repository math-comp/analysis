(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* PR 516 in progress *)
HB.mixin Record isProbability (d : measure_display) (T : measurableType d)
  (R : realType) (P : set T -> \bar R) of isMeasure d R T P :=
  { probability_setT : P setT = 1%E }.

#[short(type=probability)]
HB.structure Definition Probability (d : measure_display) (T : measurableType d)
    (R : realType) :=
  {P of isProbability d T R P & isMeasure d R T P }.

Section probability_lemmas.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_le1 (A : set T) : measurable A -> (P A <= 1)%E.
Proof.
Admitted.

End probability_lemmas.
(* /PR 516 in progress *)

HB.mixin Record isKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R}) := {
  kernelP : forall U, measurable U -> measurable_fun setT (k ^~ U)
}.

#[short(type=kernel)]
HB.structure Definition Kernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k & isKernel d d' R X Y k}.
Notation "X ^^> Y" := (kernel _ X Y) (at level 42).

(* TODO: define using the probability type *)
HB.mixin Record isProbabilityKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    of isKernel d d' R X Y k := {
  prob_kernelP : forall x : X, k x [set: Y] = 1
}.

#[short(type=probability_kernel)]
HB.structure Definition ProbabilityKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k of isProbabilityKernel d d' R X Y k & isKernel d d' R X Y k}.

Section sum_of_kernels.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variable k : (kernel R X Y)^nat.

Definition sum_of_kernels : X -> {measure set Y -> \bar R} :=
  fun x => [the measure _ _ of mseries (k ^~ x) 0].

Lemma kernel_measurable_fun_sum_of_kernels (U : set Y) :
  measurable U ->
  measurable_fun setT (sum_of_kernels ^~ U).
Proof.
move=> mU; rewrite /sum_of_kernels /= /mseries.
rewrite [X in measurable_fun _ X](_ : _ =
  (fun x => elim_sup (fun n => \sum_(0 <= i < n) k i x U))); last first.
  apply/funext => x; rewrite -lim_mkord is_cvg_elim_supE.
    by rewrite -lim_mkord.
  exact: is_cvg_nneseries.
apply: measurable_fun_elim_sup => n.
by apply: emeasurable_fun_sum => *; exact/kernelP.
Qed.

HB.instance Definition _ :=
  isKernel.Build d d' R X Y sum_of_kernels
    kernel_measurable_fun_sum_of_kernels.

End sum_of_kernels.

Lemma integral_sum_of_kernels (d d' : measure_display)
  (R : realType) (X : measurableType d) (Y : measurableType d')
  (k : (X ^^> Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun setT f ->
  \int[sum_of_kernels k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /sum_of_kernels/= ge0_integral_measure_series.
Qed.

Section kernel_uub.
Variables (d d' : measure_display) (R : numFieldType) (X : measurableType d)
  (Y : measurableType d') (k : X -> set Y -> \bar R).

Definition kernel_uub := exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E.

End kernel_uub.

HB.mixin Record isFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    := { finite_kernelP : kernel_uub k }.

#[short(type=finite_kernel)]
HB.structure Definition FiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k of isFiniteKernel d d' R X Y k & isKernel d d' R X Y k}.

HB.mixin Record isSFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    := {
  sfinite_kernelP : exists k_ : (finite_kernel R X Y)^nat,
    forall x U, measurable U ->
      k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U
}.

#[short(type=sfinite_kernel)]
HB.structure Definition SFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k of isSFiniteKernel d d' R X Y k &
        isKernel d d' R X Y k}.

Section star_is_measure.
Variables (d1 d2 d3 : _) (R : realType) (X : measurableType d1)
          (Y : measurableType d2) (Z : measurableType d3).
Variable k : kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : kernel R X Y.

Definition star : X -> set Z -> \bar R := fun x U => \int[l x]_y k (x, y) U.

Let star0 x : star x set0 = 0.
Proof.
by rewrite /star (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let star_ge0 x U : 0 <= star x U.
Proof. by apply: integral_ge0 => y _; exact: measure_ge0. Qed.

Let star_sigma_additive x : semi_sigma_additive (star x).
Proof.
move=> U mU tU mUU; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (U n)))%E; last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE// integral_sum// => n.
have := @kernelP _ _ R _ _ k (U n) (mU n).
exact/measurable_fun_prod1.
Qed.

HB.instance Definition _ x := isMeasure.Build _ R _
  (star x) (star0 x) (star_ge0 x) (@star_sigma_additive x).

Definition mstar : X -> {measure set Z -> \bar R} :=
  fun x => [the measure _ _ of star x].

End star_is_measure.

(* TODO: PR *)
Section integralM_0ifneg.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralM_0ifneg (f : R -> T -> \bar R) (k : R)
  (f0 : forall r t, D t -> (0 <= f r t)) :
  ((k < 0)%R -> f k = cst 0%E) -> measurable_fun setT (f k) ->
  \int[m]_(x in D) (k%:E * (f k) x) = k%:E * \int[m]_(x in D) ((f k) x).
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    by move=> x _; rewrite fk0// mule0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
rewrite ge0_integralM//.
- by apply/(@measurable_funS _ _ _ _ setT) => //.
- by move=> y Dy; rewrite f0.
Qed.

End integralM_0ifneg.
Arguments integralM_0ifneg {d T R} m {D} mD f.

(*Section integralM_0ifneg.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralM_0ifneg (f : R -> T -> R) (k : R)
  (f0 : forall r t, D t -> (0 <= f r t)%R) :
  ((k < 0)%R -> f k = cst 0%R) -> measurable_fun setT (f k) ->
  \int[m]_(x in D) (k * (f k) x)%:E = k%:E * \int[m]_(x in D) ((f k) x)%:E.
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    by move=> x _; rewrite fk0// mulr0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralM//.
- apply/EFin_measurable_fun/(@measurable_funS _ _ _ _ setT) => //.
- by move=> y Dy; rewrite lee_fin f0.
Qed.

End integralM_0ifneg.
Arguments integralM_0ifneg {d T R} m {D} mD f.*)

Section integralM_indic.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Let integralM_indic (f : R -> set T) (k : R) :
  ((k < 0)%R -> f k = set0) -> measurable (f k) ->
  \int[m]_(x in D) (k * \1_(f k) x)%:E = k%:E * \int[m]_(x in D) (\1_(f k) x)%:E.
Proof.
move=> fk0 mfk.
under eq_integral do rewrite EFinM.
apply: (integralM_0ifneg _ _ (fun k x => (\1_(f k) x)%:E)) => //=.
- by move=> r t Dt; rewrite lee_fin.
- by move/fk0 => -> /=; apply/funext => x; rewrite indicE in_set0.
- apply/EFin_measurable_fun.
  by rewrite (_ : \1_(f k) = mindic R mfk).
Qed.

End integralM_indic.
Arguments integralM_indic {d T R} m {D} mD f.

(* NB: PR in progress *)
Section integral_mscale.
Variables (R : realType) (k : {nonneg R}).
Variables (d : measure_display) (T : measurableType d).
Variable (m : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R).
Hypotheses (mD : measurable D).

Let integral_mscale_indic (E : set T) (mE : measurable E) :
  \int[mscale k m]_(x in D) (\1_E x)%:E =
  k%:num%:E * \int[m]_(x in D) (\1_E x)%:E.
Proof. by rewrite !integral_indic. Qed.

Let integral_mscale_nnsfun (h : {nnsfun T >-> R}) :
  \int[mscale k m]_(x in D) (h x)%:E = k%:num%:E * \int[m]_(x in D) (h x)%:E.
Proof.
rewrite -ge0_integralM//; last 2 first.
apply/EFin_measurable_fun.
  exact: measurable_funS (@measurable_funP _ _ _ h).
  by move=> x _; rewrite lee_fin.
under eq_integral do rewrite fimfunE -sumEFin.
under [LHS]eq_integral do rewrite fimfunE -sumEFin.
rewrite /=.
rewrite ge0_integral_sum//; last 2 first.
  move=> r.
  apply/EFin_measurable_fun/measurable_funrM.
  apply: (@measurable_funS _ _ _ _ setT) => //.
  have fr : measurable (h @^-1` [set r]) by exact/measurable_sfunP.
  by rewrite (_ : \1__ = mindic R fr).
  by move=> n x Dx; rewrite EFinM muleindic_ge0.
under eq_integral.
  move=> x xD.
  rewrite ge0_sume_distrr//; last first.
    by move=> r _; rewrite EFinM muleindic_ge0.
  over.
rewrite /=.
rewrite ge0_integral_sum//; last 2 first.
  move=> r.
  apply/EFin_measurable_fun/measurable_funrM/measurable_funrM.
  apply: (@measurable_funS _ _ _ _ setT) => //.
  have fr : measurable (h @^-1` [set r]) by exact/measurable_sfunP.
  by rewrite (_ : \1__ = mindic R fr).
  move=> n x Dx.
  by rewrite EFinM mule_ge0// muleindic_ge0.
apply eq_bigr => r _.
rewrite ge0_integralM//; last 2 first.
  apply/EFin_measurable_fun/measurable_funrM.
  apply: (@measurable_funS _ _ _ _ setT) => //.
  have fr : measurable (h @^-1` [set r]) by exact/measurable_sfunP.
  by rewrite (_ : \1__ = mindic R fr).
  by move=> t Dt; rewrite muleindic_ge0.
by rewrite !integralM_indic_nnsfun//= integral_mscale_indic// muleCA.
Qed.

Lemma ge0_integral_mscale (mf : measurable_fun D f) :
  (forall x, D x -> 0 <= f x) ->
  \int[mscale k m]_(x in D) f x = k%:num%:E * \int[m]_(x in D) f x.
Proof.
move=> f0; have [f_ [ndf_ f_f]] := approximation mD mf f0.
transitivity (lim (fun n => \int[mscale k m]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//=; last 3 first.
    move=> n; apply/EFin_measurable_fun.
    by apply: (@measurable_funS _ _ _ _ setT).
    by move=> n x Dx; rewrite lee_fin.
    by move=> x Dx a b /ndf_ /lefP; rewrite lee_fin.
  apply eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //=.
  exact: f_f.
rewrite (_ : \int[m]_(x in D) _ = lim (fun n => \int[m]_(x in D) (f_ n x)%:E)); last first.
  rewrite -monotone_convergence//.
  apply: eq_integral => x /[!inE] xD.
  apply/esym/cvg_lim => //.
  exact: f_f.
  move=> n.
  apply/EFin_measurable_fun.
  by apply: (@measurable_funS _ _ _ _ setT).
  by move=> n x Dx; rewrite lee_fin.
  by move=> x Dx a b /ndf_ /lefP; rewrite lee_fin.
rewrite -ereal_limrM//; last first.
  apply/ereal_nondecreasing_is_cvg => a b ab.
  apply ge0_le_integral => //.
  by move=> x Dx; rewrite lee_fin.
  apply/EFin_measurable_fun.
  by apply: (@measurable_funS _ _ _ _ setT).
  by move=> x Dx; rewrite lee_fin.
  apply/EFin_measurable_fun.
  by apply: (@measurable_funS _ _ _ _ setT).
  move=> x Dx.
  rewrite lee_fin.
  by move/ndf_ : ab => /lefP.
congr (lim _); apply/funext => n /=.
by rewrite integral_mscale_nnsfun.
Qed.

End integral_mscale.

Section ndseq_closed_B.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (pt2 : T2) (m2 : T1 -> {measure set T2 -> \bar R}).
Let phi A x := m2 x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma xsection_ndseq_closed_dep : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have phiF x : (fun i => phi (F i) x) --> phi (\bigcup_i F i) x.
  rewrite /phi /= xsection_bigcup; apply: cvg_mu_inc => //.
  - by move=> n; apply: measurable_xsection; case: (BF n).
  - by apply: bigcupT_measurable => i; apply: measurable_xsection; case: (BF i).
  - move=> m n mn; apply/subsetPset => y; rewrite /xsection/= !inE.
    by have /subsetPset FmFn := ndF _ _ mn; exact: FmFn.
apply: (emeasurable_fun_cvg (phi \o F)) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: phiF.
Qed.
End xsection.

End ndseq_closed_B.

Section measurable_prod_subset.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variable (m2 : T1 -> {measure set T2 -> \bar R}) (D : set T2) (mD : measurable D).
Let m2D x := mrestr (m2 x) mD.
HB.instance Definition _ x := Measure.on (m2D x).
Let phi A := fun x => m2D x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Hypothesis H1 : forall X2, measurable X2 -> measurable_fun [set: T1] (m2D^~ X2).

Lemma measurable_prod_subset_xsection_dep
    (m2D_bounded : forall x, exists M, forall X, measurable X -> (m2D x X < M%:E)%E) :
  measurable `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in measurable & A2 in measurable].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setMTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : phi (X1 `*` X2) = (fun x => m2D x X2 * (\1_X1 x)%:E)%E.
    rewrite funeqE => x; rewrite indicE /phi /m2/= /mrestr.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionM.
    by rewrite mule0 notin_xsectionM// set0I measure0.
  apply: emeasurable_funM => //.
    by apply: H1.
  apply/EFin_measurable_fun.
  by rewrite (_ : \1_ _ = mindic R mX1).
suff monoB : monotone_class setT B by exact: monotone_class_subset.
split => //; [exact: CB| |exact: xsection_ndseq_closed_dep].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
have -> : phi (X `\` Y) = (fun x => phi X x - phi Y x)%E.
  rewrite funeqE => x; rewrite /phi/= xsectionD// /m2D measureD.
  - by rewrite setIidr//; exact: le_xsection.
  - exact: measurable_xsection.
  - exact: measurable_xsection.
  - move: (m2D_bounded x) => [M m2M].
    rewrite (lt_le_trans (m2M (xsection X x) _))// ?leey//.
    exact: measurable_xsection.
exact: emeasurable_funB.
Qed.

End xsection.

End measurable_prod_subset.

Section measurable_fun_xsection.
Variables (d1 d2 : measure_display) (T1 : measurableType d1)
          (T2 : measurableType d2) (R : realType).
Variables (m2 : T1 -> {measure set T2 -> \bar R}).
Implicit Types A : set (T1 * T2).
Hypotheses m2_ub : kernel_uub m2.

Hypothesis H1 : forall X2, measurable X2 ->
  measurable_fun [set: T1] ((fun x => mrestr (m2 x) measurableT)^~ X2).

Let phi A := (fun x => m2 x (xsection A x)).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection_dep A :
  A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A; rewrite inE => /[apply] -[].
move=> X mX.
rewrite /B/=; split => //.
rewrite /phi.
rewrite -(_ : (fun x : T1 => mrestr (m2 x) measurableT (xsection X x)) = (fun x => (m2 x) (xsection X x)))//; last first.
  apply/funext => x//=.
  by rewrite /mrestr setIT.
apply measurable_prod_subset_xsection_dep => //.
move=> x.
case: m2_ub => r hr.
exists r%:num => Y mY.
apply: (le_lt_trans _ (hr x)) => //.
rewrite /mrestr.
apply le_measure => //.
rewrite inE.
apply: measurableI => //.
by rewrite inE.
Qed.

End measurable_fun_xsection.

Section fubini_F_dep.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m2 : T1 -> {measure set T2 -> \bar R}).
Variable f : T1 * T2 -> \bar R.

Definition fubini_F_dep x := \int[m2 x]_y f (x, y).

End fubini_F_dep.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : T1 -> {measure set T2 -> \bar R}).
Hypotheses m2_ub : kernel_uub m2.

Section indic_fubini_tonelli.
Variables (A : set (T1 * T2)) (mA : measurable A).
Implicit Types A : set (T1 * T2).
Let f : (T1 * T2) -> R := \1_A.

Let F := fubini_F_dep m2 (EFin \o f).

Lemma indic_fubini_tonelli_FE_dep : F = (fun x => m2 x (xsection A x)).
Proof.
rewrite funeqE => x; rewrite /= -(setTI (xsection _ _)).
rewrite -integral_indic//; last exact: measurable_xsection.
rewrite /F /fubini_F -(setTI (xsection _ _)).
rewrite integral_setI_indic; [|exact: measurable_xsection|by []].
apply: eq_integral => y _ /=; rewrite indicT mul1e /f !indicE.
have [|] /= := boolP (y \in xsection _ _).
  by rewrite inE /xsection /= => ->.
by rewrite /xsection /= notin_set /= => /negP/negbTE ->.
Qed.

Hypothesis H1 : forall X2, measurable X2 ->
  measurable_fun [set: T1] ((fun x => mrestr (m2 x) measurableT)^~ X2).

Lemma indic_measurable_fun_fubini_tonelli_F_dep : measurable_fun setT F.
Proof.
rewrite indic_fubini_tonelli_FE_dep//; apply: measurable_fun_xsection_dep => //.
by rewrite inE.
Qed.

End indic_fubini_tonelli.

End fubini_tonelli.

Lemma pollard_finite (d d' : measure_display) (R : realType)
    (X : measurableType d) (Y : measurableType d')
    (k : (X * Y)%type -> \bar R) (k0 : (forall t : X * Y, True -> 0 <= k t))
    (mk : measurable_fun setT k) (l : finite_kernel R X Y) :
  measurable_fun [set: X] (fun x : X => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := @approximation _ _ _ _ measurableT k mk k0.
simpl in *.
rewrite (_ : (fun x => \int[l x]_y k (x, y)) =
    (fun x => elim_sup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funeqP => x.
  transitivity (lim (fun n => \int[l x]_y (k_ n (x, y))%:E)); last first.
    rewrite is_cvg_elim_supE//.
    apply: ereal_nondecreasing_is_cvg => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y' _; rewrite lee_fin; apply/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
  - by move=> n y' _; rewrite lee_fin.
  - by move=> y' _ m n mn; rewrite lee_fin; apply/lefP/ndk_.
apply: measurable_fun_elim_sup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \int[l x0]_y
  ((\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) (x0, y)))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \sum_(r <- fset_set (range (k_ n)))
  (\int[l x0]_y
     (r * \1_(k_ n @^-1` [set r]) (x0, y))%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_sum//.
  - by apply: eq_integral => y _; rewrite sumEFin.
  - move=> r.
    apply/EFin_measurable_fun/measurable_funrM/measurable_fun_prod1 => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
  - by move=> m y _; rewrite muleindic_ge0.
apply emeasurable_fun_sum => r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => r%:E *
    \int[l x]_y (\1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite (integralM_0ifneg _ _ (fun k y => (\1_(k_ n @^-1` [set r]) (x, y))%:E))//.
  - by move=> _ t _; rewrite lee_fin.
  - by move=> r_lt0; apply/funext => y; rewrite preimage_nnfun0// indicE in_set0.
  - apply/EFin_measurable_fun/measurable_fun_prod1 => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
apply: measurable_funeM.
apply: indic_measurable_fun_fubini_tonelli_F_dep.
- by apply/finite_kernelP.
- by apply/measurable_sfunP.
- move=> X2.
  rewrite (_ : (fun x : X => mrestr (l x) measurableT X2) = (fun x : X => (l x) X2))//.
    by apply/kernelP.
  apply/funeqP => x.
  by rewrite /mrestr setIT.
Qed.

Module STAR_IS_FINITE_KERNEL.

Section star_is_kernel_finite.
Variables (d d' d3 : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).
Variable k : kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : finite_kernel R X Y.

Lemma star_measurable_finite U : measurable U -> measurable_fun setT (star k l ^~ U).
Proof.
(* k is a bounded measurable function *)
(* l is a finite kernel *)
move=> mU.
rewrite /star.
apply: (@pollard_finite _ _ R X Y (fun xy => k xy U)) => //.
by apply: (@kernelP _ _ R [the measurableType (d, d').-prod of (X * Y)%type] Z k U) => //.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ R X Z (mstar k l) star_measurable_finite.

End star_is_kernel_finite.

Section star_is_finite_kernel.
Variables (d d' d3 : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).
Variable k : finite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : finite_kernel R X Y.

Lemma star_finite : kernel_uub (mstar k l).
Proof.
have [r hr] := @finite_kernelP _ _ _ _ _ k.
have [s hs] := @finite_kernelP _ _ _ _ _ l.
exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x.
rewrite /star.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply: ge0_le_integral => //.
  - have := @kernelP _ _ _ _ _ k setT measurableT.
    exact/measurable_fun_prod1.
  - exact/measurable_fun_cst.
  - by move=> y _; apply/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  isFiniteKernel.Build _ _ R X Z (mstar k l) star_finite.

End star_is_finite_kernel.
End STAR_IS_FINITE_KERNEL.

Lemma pollard_sfinite (d d' d3 : measure_display) (R : realType)
    (X : measurableType d) (Y : measurableType d') (Z : measurableType d3)
    (k : Z -> \bar R) (k0 : (forall z, True -> 0 <= k z))
    (mk : measurable_fun setT k)
    (l : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z) c :
  measurable_fun [set: Y] (fun x0 : Y => \int[l (c, x0)]_z k z).
Proof.
have [k_ [ndk_ k_k]] := @approximation _ _ _ _ measurableT k mk k0.
simpl in *.
rewrite (_ : (fun x0 => \int[l (c, x0)]_z k z) =
    (fun x0 => elim_sup (fun n => \int[l (c, x0)]_z (k_ n z)%:E))); last first.
  apply/funeqP => x.
  transitivity (lim (fun n => \int[l (c, x)]_z (k_ n z)%:E)); last first.
    rewrite is_cvg_elim_supE//.
    apply: ereal_nondecreasing_is_cvg => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun.
    - by move=> y' _; rewrite lee_fin; apply/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/EFin_measurable_fun.
  - by move=> n y' _; rewrite lee_fin.
  - by move=> y' _ m n mn; rewrite lee_fin; apply/lefP/ndk_.
apply: measurable_fun_elim_sup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \int[l (c, x0)]_z
  ((\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) z))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \sum_(r <- fset_set (range (k_ n)))
  (\int[l (c, x0)]_z
     (r * \1_(k_ n @^-1` [set r]) z)%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_sum//.
  - by apply: eq_integral => y _; rewrite sumEFin.
  - move=> r.
    apply/EFin_measurable_fun/measurable_funrM => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
  - by move=> m y _; rewrite muleindic_ge0.
apply emeasurable_fun_sum => r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => r%:E *
    \int[l (c ,x)]_z (\1_(k_ n @^-1` [set r]) z)%:E)); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite (integralM_0ifneg _ _ (fun k z => (\1_(k_ n @^-1` [set r]) z)%:E))//.
  - by move=> _ t _; rewrite lee_fin.
  - by move=> r_lt0; apply/funext => y; rewrite preimage_nnfun0// indicE in_set0.
  - apply/EFin_measurable_fun => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
apply: measurable_funeM.
rewrite (_ : (fun x : Y => \int[l (c, x)]_z (\1_(k_ n @^-1` [set r]) z)%:E) =
  (fun x : Y => l (c, x) (k_ n @^-1` [set r]))); last first.
  apply/funext => y.
  by rewrite integral_indic// setIT.
have := @kernelP _ _ R _ _ l (k_ n @^-1` [set r]) (measurable_sfunP (k_ n) r).
rewrite /=.
move/measurable_fun_prod1.
exact.
Qed.

Lemma pollard_sfinite2 (d d' : measure_display) (R : realType)
    (X : measurableType d) (Y : measurableType d')
    (k : (X * Y)%type -> \bar R) (k0 : (forall (t : X * Y), True -> 0 <= k t))
    (l : sfinite_kernel R X Y)
  (mk : measurable_fun setT k) :
  measurable_fun [set: X] (fun x : X => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := @approximation _ _ _ _ measurableT k mk k0.
simpl in *.
rewrite (_ : (fun x => \int[l x]_y k (x, y)) =
    (fun x => elim_sup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funeqP => x.
  transitivity (lim (fun n => \int[l x]_y (k_ n (x, y))%:E)); last first.
    rewrite is_cvg_elim_supE//.
    apply: ereal_nondecreasing_is_cvg => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y' _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y' _; rewrite lee_fin; apply/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
  - by move=> n y' _; rewrite lee_fin.
  - by move=> y' _ m n mn; rewrite lee_fin; apply/lefP/ndk_.
apply: measurable_fun_elim_sup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \int[l x0]_y
  ((\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) (x0, y)))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x0 => \sum_(r <- fset_set (range (k_ n)))
  (\int[l x0]_y
     (r * \1_(k_ n @^-1` [set r]) (x0, y))%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_sum//.
  - by apply: eq_integral => y _; rewrite sumEFin.
  - move=> r.
    apply/EFin_measurable_fun/measurable_funrM/measurable_fun_prod1 => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
  - by move=> m y _; rewrite muleindic_ge0.
apply emeasurable_fun_sum => r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => r%:E *
    \int[l x]_y (\1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite (integralM_0ifneg _ _ (fun k y => (\1_(k_ n @^-1` [set r]) (x, y))%:E))//.
  - by move=> _ t _; rewrite lee_fin.
  - by move=> r_lt0; apply/funext => y; rewrite preimage_nnfun0// indicE in_set0.
  - apply/EFin_measurable_fun/measurable_fun_prod1 => /=.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r)).
apply: measurable_funeM.
rewrite (_ : (fun x : X => \int[l x]_z (\1_(k_ n @^-1` [set r]) (x, z))%:E) =
  (fun x : X => l x (xsection (k_ n @^-1` [set r]) x))); last first.
  apply/funext => y.
  rewrite integral_indic//; last first.
    rewrite (_ : (fun x : Y => (k_ n @^-1` [set r]) (y, x)) = xsection (k_ n @^-1` [set r]) y); last first.
      apply/seteqP; split.
        by move=> y2/=; rewrite /xsection/= inE//.
      by rewrite /xsection/= => y2/=; rewrite inE /preimage/=.
    by apply: measurable_xsection.
  congr (l y _).
  apply/funext => y1/=.
  rewrite /xsection/= inE.
  by apply/propext; tauto.
have [l_ hl_] := @sfinite_kernelP _ _ _ _ _ l.
rewrite (_ : (fun x : X => _) =
  (fun x : X => mseries (l_ ^~ x) 0 (xsection (k_ n @^-1` [set r]) x))
); last first.
  apply/funext => x.
  rewrite hl_//.
  by apply/measurable_xsection.
rewrite /mseries/=.
apply: ge0_emeasurable_fun_sum => // k1.
apply: measurable_fun_xsection_dep => //.
by have := @finite_kernelP _ _ _ _ _ (l_ k1).
move=> X2 mX2.
rewrite /mrestr.
apply/kernelP.
by rewrite setIT.
by rewrite inE.
Qed.

Section star_is_sfinite_kernel.
Variables (d d' d3 : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).
Variable k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : sfinite_kernel R X Y.

Import STAR_IS_FINITE_KERNEL.

Lemma star_sfinite : exists k_ : (finite_kernel R X Z)^nat, forall x U, measurable U ->
  mstar k l x U = [the measure _ _ of mseries (k_ ^~ x) O] U.
Proof.
have [k_ hk_] := @sfinite_kernelP _ _ _ _ _ k.
have [l_ hl_] := @sfinite_kernelP _ _ _ _ _ l.
pose K := [the kernel _ _ _ of sum_of_kernels k_].
pose L := [the kernel _ _ _ of sum_of_kernels l_].
have H1 x U : measurable U -> star k l x U = star K L x U.
  move=> mU.
  rewrite /star /L /K /=.
  transitivity (\int[
    [the measure _ _ of mseries (fun x0 : nat => l_ x0 x) 0] ]_y k (x, y) U).
    apply eq_measure_integral => A mA _ .
    by rewrite hl_.
  apply eq_integral => y _.
  by rewrite hk_//.
have H2 x U : star K L x U =
  \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U).
  rewrite /star /L /=.
  by apply eq_integral => y _.
have H3 x U : measurable U ->
     \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U) =
     \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U).
   move=> mU.
   rewrite integral_sum//= => n.
   have := @kernelP _ _ _ _ _ (k_ n) _ mU.
   by move/measurable_fun_prod1; exact.
have H4 x U : measurable U ->
    \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U) =
    \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U.
  move=> mU.
  apply: eq_nneseries => i _.
  rewrite integral_sum_of_kernels//.
  have := @kernelP _ _ _ _ _ (k_ i) _ mU.
  by move/measurable_fun_prod1; exact.
have H5 x U : \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U =
  \sum_(i <oo) \sum_(j <oo) star (k_ i) (l_ j) x U.
  by apply eq_nneseries => i _; exact: eq_nneseries.
suff: exists k_0 : (finite_kernel R X Z) ^nat, forall x U,
    \esum_(i in setT) star (k_ i.1) (l_ i.2) x U = \sum_(i <oo) k_0 i x U.
  move=> [kl_ hkl_].
  exists kl_ => x U mU.
  rewrite /=.
  rewrite /mstar/= /mseries H1// H2 H3//.
  rewrite H4//.
  rewrite H5// -hkl_ /=.
  rewrite (_ : setT = setT `*`` (fun=> setT)); last by apply/seteqP; split.
  rewrite -(@esum_esum _ _ _ _ _ (fun i j => star (k_ i) (l_ j) x U))//.
  rewrite nneseries_esum; last by move=> n _; exact: nneseries_lim_ge0(* TODO: rename this lemma *).
  by rewrite fun_true; apply: eq_esum => /= i _; rewrite nneseries_esum// fun_true.
rewrite /=.
have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
  by rewrite card_eq_sym; exact: card_nat2.
exists (fun i => [the finite_kernel _ _ _ of mstar (k_ (f i).1) (l_ (f i).2)]) => x U.
rewrite (reindex_esum [set: nat] [set: nat * nat] f)//.
by rewrite nneseries_esum// fun_true.
Qed.

Lemma star_measurable_sfinite U : measurable U -> measurable_fun setT (star k l ^~ U).
Proof.
move=> mU.
rewrite /star.
apply: (@pollard_sfinite2 _ _ _ _ _ (k ^~ U)) => //.
by apply/kernelP.
Qed.

End star_is_sfinite_kernel.

Module STAR_IS_SFINITE_KERNEL.
Section star_is_sfinite_kernel.
Variables (d d' d3 : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).
Variable k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : sfinite_kernel R X Y.

HB.instance Definition _ :=
  isKernel.Build _ _ R X Z (mstar k l) (star_measurable_sfinite k l).

#[export]
HB.instance Definition _ :=
  isSFiniteKernel.Build d d3 R X Z (mstar k l) (star_sfinite k l).

End star_is_sfinite_kernel.
End STAR_IS_SFINITE_KERNEL.
HB.export STAR_IS_SFINITE_KERNEL.

Lemma lemma3_indic d d' d3 (R : realType) (X : measurableType d)
    (Y : measurableType d') (Z : measurableType d3)
    (k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z)
    (l : sfinite_kernel R X Y) x (E : set _) (mE : measurable E) :
  \int[mstar k l x]_z (\1_E z)%:E = \int[l x]_y (\int[k (x, y)]_z (\1_E z)%:E).
Proof.
rewrite integral_indic// /mstar/= /star/=.
by apply eq_integral => y _; rewrite integral_indic.
Qed.

Lemma lemma3_nnsfun d d' d3 (R : realType) (X : measurableType d)
    (Y : measurableType d') (Z : measurableType d3)
    (k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z)
    (l : sfinite_kernel R X Y) x (f : {nnsfun Z >-> R}) :
  \int[mstar k l x]_z (f z)%:E = \int[l x]_y (\int[k (x, y)]_z (f z)%:E).
Proof.
under [in LHS]eq_integral do rewrite fimfunE -sumEFin.
rewrite ge0_integral_sum//; last 2 first.
  move=> r; apply/EFin_measurable_fun/measurable_funrM.
  have fr : measurable (f @^-1` [set r]) by exact/measurable_sfunP.
  by rewrite (_ : \1__ = mindic R fr).
  by move=> r z _; rewrite EFinM muleindic_ge0.
under [in RHS]eq_integral.
  move=> y _.
  under eq_integral.
    move=> z _.
    rewrite fimfunE -sumEFin.
    over.
  rewrite /= ge0_integral_sum//; last 2 first.
    move=> r; apply/EFin_measurable_fun/measurable_funrM.
    have fr : measurable (f @^-1` [set r]) by exact/measurable_sfunP.
    by rewrite (_ : \1__ = mindic R fr).
    by move=> r z _; rewrite EFinM muleindic_ge0.
  under eq_bigr.
    move=> r _.
    rewrite (@integralM_indic _ _ _ _ _ _ (fun r => f @^-1` [set r]))//; last first.
      by move=> r0; rewrite preimage_nnfun0.
    rewrite integral_indic// setIT.
    over.
  over.
rewrite /= ge0_integral_sum//; last 2 first.
  move=> r; apply: measurable_funeM.
  have := @kernelP _ _ _ _ _ k (f @^-1` [set r]) (measurable_sfunP f r).
  by move/measurable_fun_prod1; exact.
  move=> n y _.
  have := @mulem_ge0 _ _ _ (k (x, y)) n (fun n => f @^-1` [set n]).
  apply.
  exact: preimage_nnfun0.
apply eq_bigr => r _.
rewrite (@integralM_indic _ _ _ _ _ _ (fun r => f @^-1` [set r]))//; last first.
  exact: preimage_nnfun0.
rewrite /= lemma3_indic; last exact/measurable_sfunP.
rewrite (@integralM_0ifneg _ _ _ _ _ _ (fun r t => k (x, t) (f @^-1` [set r])))//; last 2 first.
  move=> r0.
  apply/funext => y.
  by rewrite preimage_nnfun0// measure0.
  have := @kernelP _ _ _ _ _ k (f @^-1` [set r]) (measurable_sfunP f r).
  by move/measurable_fun_prod1; exact.
congr (_ * _).
apply eq_integral => y _.
by rewrite integral_indic// setIT.
Qed.

Lemma lemma3 d d' d3 (R : realType) (X : measurableType d)
    (Y : measurableType d') (Z : measurableType d3)
    (k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z)
    (l : sfinite_kernel R X Y) x f : (forall z, 0 <= f z) -> measurable_fun setT f ->
  \int[mstar k l x]_z f z = \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
move=> f0 mf.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun z _ => f0 z).
transitivity (\int[mstar k l x]_z (lim (EFin \o (f_^~ z)))).
  apply/eq_integral => z _.
  apply/esym/cvg_lim => //=.
  exact: f_f.
rewrite monotone_convergence//; last 3 first.
  by move=> n; apply/EFin_measurable_fun.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b /ndf_ /lefP ab; rewrite lee_fin.
rewrite (_ : (fun _ => _) = (fun n => \int[l x]_y (\int[k (x, y)]_z (f_ n z)%:E)))//; last first.
  by apply/funext => n; rewrite lemma3_nnsfun.
transitivity (\int[l x]_y lim (fun n => \int[k (x, y)]_z (f_ n z)%:E)).
  rewrite -monotone_convergence//; last 3 first.
  move=> n.
  apply: pollard_sfinite => //.
  - by move=> z; rewrite lee_fin.
  - by apply/EFin_measurable_fun.
  - move=> n y _.
    by apply integral_ge0 => // z _; rewrite lee_fin.
  - move=> y _ a b ab.
    apply: ge0_le_integral => //.
    + by move=> z _; rewrite lee_fin.
    + exact/EFin_measurable_fun.
    + by move=> z _; rewrite lee_fin.
    + exact/EFin_measurable_fun.
    + move: ab => /ndf_ /lefP ab z _.
      by rewrite lee_fin.
apply eq_integral => y _.
rewrite -monotone_convergence//; last 3 first.
  move=> n; exact/EFin_measurable_fun.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b /ndf_ /lefP; rewrite lee_fin.
apply eq_integral => z _.
apply/cvg_lim => //.
exact: f_f.
Qed.

Canonical unit_pointedType := PointedType unit tt.

Section discrete_measurable_unit.

Definition discrete_measurable_unit : set (set unit) := [set: set unit].

Let discrete_measurable0 : discrete_measurable_unit set0. Proof. by []. Qed.

Let discrete_measurableC X : discrete_measurable_unit X -> discrete_measurable_unit (~` X).
Proof. by []. Qed.

Let discrete_measurableU (F : (set unit)^nat) :
  (forall i, discrete_measurable_unit (F i)) -> discrete_measurable_unit (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display unit (Pointed.class _)
  discrete_measurable_unit discrete_measurable0 discrete_measurableC
  discrete_measurableU.

End discrete_measurable_unit.

Section discrete_measurable_bool.

Definition discrete_measurable_bool : set (set bool) := [set: set bool].

Let discrete_measurable0 : discrete_measurable_bool set0. Proof. by []. Qed.

Let discrete_measurableC X :
  discrete_measurable_bool X -> discrete_measurable_bool (~` X).
Proof. by []. Qed.

Let discrete_measurableU (F : (set bool)^nat) :
  (forall i, discrete_measurable_bool (F i)) ->
  discrete_measurable_bool (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display bool (Pointed.class _)
  discrete_measurable_bool discrete_measurable0 discrete_measurableC
  discrete_measurableU.

End discrete_measurable_bool.

Section nonneg_constants.
Variable R : realType.
(* 
Let twoseven_proof : (0 <= 2 / 7 :> R)%R.
Proof. by rewrite divr_ge0// ler0n. Qed.
*)

(* Check (2%:R / 7%:R)%:nng. *)

(* Definition twoseven : {nonneg R} := (2%:R / 7%:R)%:nng. *)
(*
Let fiveseven_proof : (0 <= 5 / 7 :> R)%R.
Proof. by rewrite divr_ge0// ler0n. Qed.

Definition fiveseven : {nonneg R} := NngNum fiveseven_proof.
 *)

End nonneg_constants.

Lemma measure_diract_setT_true (R : realType) :
  [the measure _ _ of dirac true] [set: bool] = 1 :> \bar R.
Proof. by rewrite /= diracE in_setT. Qed.

Lemma measure_diract_setT_false (R : realType) :
  [the measure _ _ of dirac false] [set: bool] = 1 :> \bar R.
Proof. by rewrite /= diracE in_setT. Qed.

Section bernoulli27.
Variable R : realType.

Local Open Scope ring_scope.
Notation "'2/7'" := (2%:R / 7%:R)%:nng.
Definition twoseven : {nonneg R} := (2%:R / 7%:R)%:nng.
Definition fiveseven : {nonneg R} := (5%:R / 7%:R)%:nng.

Definition bernoulli27 : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale twoseven [the measure _ _ of dirac true]]
    [the measure _ _ of mscale fiveseven [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli27.

Local Close Scope ring_scope.

Lemma bernoulli27_setT : bernoulli27 [set: _] = 1.
Proof.
rewrite /bernoulli27/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
rewrite /mscale/= !diracE !in_setT !mule1 -EFinD.
by rewrite -mulrDl -natrD divrr// unitfE pnatr_eq0.
Qed.

HB.instance Definition _ := @isProbability.Build _ _ R bernoulli27 bernoulli27_setT.

End bernoulli27.

Section kernel_from_mzero.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (d' : measure_display) (T' : measurableType d').

Definition kernel_from_mzero : T' -> {measure set T -> \bar R} :=
  fun _ : T' => [the measure _ _ of mzero].

Lemma kernel_from_mzeroP : forall U, measurable U ->
  measurable_fun setT (kernel_from_mzero ^~ U).
Proof. by move=> U mU/=; exact: measurable_fun_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build d' d R T' T kernel_from_mzero
  kernel_from_mzeroP.

Lemma kernel_from_mzero_uub : kernel_uub kernel_from_mzero.
Proof.
exists (PosNum ltr01) => /= t.
by rewrite /mzero/=.
Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build d' d R _ T kernel_from_mzero
  kernel_from_mzero_uub.

End kernel_from_mzero.

(* a finite kernel is always an s-finite kernel *)
Lemma finite_kernel_sfinite_kernelP (d : measure_display)
    (R : realType) (X : measurableType d) (d' : measure_display) (T : measurableType d')
    (k : finite_kernel R T X) :
  exists k_ : (finite_kernel R _ _)^nat, forall x U, measurable U ->
    k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
exists (fun n => if n is O then
           k
         else
           [the finite_kernel _ _ _ of @kernel_from_mzero _ X R _ T]
           ).
move=> t U mU/=.
rewrite /mseries.
rewrite (nneseries_split 1%N)// big_ord_recl/= big_ord0 adde0.
rewrite ereal_series (@eq_nneseries _ _ (fun=> 0%E)); last first.
  by case.
by rewrite nneseries0// adde0.
Qed.

(* semantics for a sample operation? *)
Section kernel_probability.
Variables (d : measure_display) (R : realType) (X : measurableType d).
Variables (d' : _) (T' : measurableType d').
Variable m : probability X R.

Definition kernel_probability : T' -> {measure set X -> \bar R} :=
  fun _ : T' => m.

Lemma kernel_probabilityP : forall U, measurable U ->
  measurable_fun setT (kernel_probability ^~ U).
Proof.
move=> U mU.
rewrite /kernel_probability.
exact: measurable_fun_cst.
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ d R _ X kernel_probability
  kernel_probabilityP.

Lemma kernel_probability_uub : kernel_uub kernel_probability.
Proof.
(*NB: shouldn't this work? exists 2%:pos. *)
exists (PosNum (addr_gt0 ltr01 ltr01)) => /= ?.
rewrite (le_lt_trans (probability_le1 m measurableT))//.
by rewrite lte_fin ltr_addr.
Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build _ d R _ X kernel_probability
  kernel_probability_uub.

Lemma kernel_probability_sfinite_kernelP : exists k_ : (finite_kernel R _ _)^nat,
  forall x U, measurable U ->
    kernel_probability x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: finite_kernel_sfinite_kernelP. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ d R _ X kernel_probability
  kernel_probability_sfinite_kernelP.

End kernel_probability.

(* semantics for return? *)
Section kernel_dirac.
Variables (R : realType) (d : _) (T : measurableType d).

Definition kernel_dirac : T -> {measure set T -> \bar R} :=
  fun x => [the measure _ _ of dirac x].

Lemma kernel_diracP U : measurable U -> measurable_fun setT (kernel_dirac ^~ U).
Proof.
move=> mU; apply/EFin_measurable_fun.
by rewrite [X in measurable_fun _ X](_ : _ = mindic R mU).
Qed.

HB.instance Definition _ := isKernel.Build _ _ R _ _ kernel_dirac kernel_diracP.

Lemma kernel_dirac_uub : kernel_uub kernel_dirac.
Proof.
exists (PosNum (addr_gt0 ltr01 ltr01)) => t/=.
by rewrite diracE in_setT lte_fin ltr_addr.
Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build d d R _ T kernel_dirac kernel_dirac_uub.

Lemma kernel_dirac_sfinite_kernelP : exists k_ : (finite_kernel R _ _)^nat,
  forall x U, measurable U ->
    kernel_dirac x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: finite_kernel_sfinite_kernelP. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build d d R T T kernel_dirac kernel_dirac_sfinite_kernelP.

End kernel_dirac.

Section kernel_dirac2.
Variables (R : realType) (d d' : _) (T : measurableType d) (T' : measurableType d').
Variable (f : T -> T').

Definition kernel_dirac2 (mf : measurable_fun setT f) : T -> {measure set T' -> \bar R} :=
  fun x => [the measure _ _ of dirac (f x)].

Variable (mf : measurable_fun setT f).

Lemma kernel_dirac2P U : measurable U -> measurable_fun setT (kernel_dirac2 mf ^~ U).
Proof.
move=> mU; apply/EFin_measurable_fun.
have mTU : measurable (f @^-1` U).
  have := mf measurableT mU.
  by rewrite setTI.
by rewrite [X in measurable_fun _ X](_ : _ = mindic R mTU).
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ R _ _ (kernel_dirac2 mf) kernel_dirac2P.

Lemma kernel_dirac2_uub : kernel_uub (kernel_dirac2 mf).
Proof.
exists (PosNum (addr_gt0 ltr01 ltr01)) => t/=.
by rewrite diracE in_setT lte_fin ltr_addr.
Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build _ _ R _ _ (kernel_dirac2 mf) kernel_dirac2_uub.

Lemma kernel_dirac2_sfinite_kernelP : exists k_ : (finite_kernel R _ _)^nat,
  forall x U, measurable U ->
    kernel_dirac2 mf x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: finite_kernel_sfinite_kernelP. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ _ R _ _ (kernel_dirac2 mf) kernel_dirac2_sfinite_kernelP.

End kernel_dirac2.

Definition letin (d d' d3 : measure_display) (R : realType)
  (X : measurableType d) (Y : measurableType d') (Z : measurableType d3)
  (l : sfinite_kernel R X Y)
  (k : sfinite_kernel R [the measurableType (d, d').-prod of (X * Y)%type] Z)
  : sfinite_kernel R X Z :=
  [the sfinite_kernel _ _ _ of @mstar d d' d3 R X Y Z k l].

(* semantics for score? *)

Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/seteqP; split => [|] [].
Qed.

Section score_measure.
Variables (R : realType).

Definition mscore (r : R) (U : set unit) : \bar R := if U == set0 then 0 else `| r%:E |.

Lemma mscore0 r : mscore r (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /mscore eqxx. Qed.

Lemma mscore_ge0 r U : 0 <= mscore r U.
Proof. by rewrite /mscore; case: ifP. Qed.

Lemma mscore_sigma_additive r : semi_sigma_additive (mscore r).
Proof.
move=> /= F mF tF mUF; rewrite /mscore; case: ifPn => [/eqP/bigcup0P F0|].
  rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
  apply/funext => k.
  under eq_bigr do rewrite F0// eqxx.
  by rewrite big1.
move=> /eqP/bigcup0P/existsNP[k /not_implyP[_ /eqP Fk0]].
rewrite -(cvg_shiftn k.+1)/=.
rewrite (_ : (fun _ => _) = cst `|r%:E|); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
rewrite (negbTE Fk0) big1 ?adde0// => i/= ik; rewrite ifT//.
have [/eqP//|Fitt] := set_unit (F i).
move/trivIsetP : tF => /(_ i k Logic.I Logic.I ik).
by rewrite Fitt setTI => /eqP; rewrite (negbTE Fk0).
Qed.

HB.instance Definition _ (r : R) := isMeasure.Build _ _ _
  (mscore r) (mscore0 r) (mscore_ge0 r) (@mscore_sigma_additive r).

End score_measure.

(* NB: score r = observe 0 from exp r,
       the density of the exponential distribution exp(r) at 0 is r = r e^(-r * 0)
       more generally, score (r e^(-r * t)) = observe t from exp(r),
       score (f(r)) = observe r from p where f is the density of p

*)

Module KERNEL_SCORE.
Section kernel_score.
Variable (R : realType) (d : _) (T : measurableType d).

Definition k_' (r : R) (i : nat) : T -> set unit -> \bar R :=
  fun _ U =>
    if i%:R%:E <= mscore r U < i.+1%:R%:E then
      mscore r U
    else
      0.

Lemma k_'0 (r : R) i (t : T) : k_' r i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k_' measure0; case: ifP. Qed.

Lemma k_'ge0 (r : R) i (t : T) B : 0 <= k_' r i t B.
Proof. by rewrite /k_'; case: ifP. Qed.

Lemma k_'sigma_additive (r : R) i (t : T) : semi_sigma_additive (k_' r i t).
Proof.
move=> /= F mF tF mUF.
rewrite /k_' /=.
have [F0|] := eqVneq (\bigcup_n F n) set0.
  rewrite [in X in _ --> X]/mscore F0 eqxx.
  rewrite (_ : (fun _ => _) = cst 0).
    by case: ifPn => _; exact: cvg_cst.
  apply/funext => k; rewrite big1// => n _.
  move : F0 => /bigcup0P F0.
  by rewrite /mscore F0// eqxx; case: ifP.
move=> UF0; move: (UF0).
move=> /eqP/bigcup0P/existsNP[k /not_implyP[_ /eqP Fk0]].
rewrite [in X in _ --> X]/mscore (negbTE UF0).
rewrite -(cvg_shiftn k.+1)/=.
case: ifPn => ir.
  rewrite (_ : (fun _ => _) = cst `|r%:E|); first exact: cvg_cst.
  apply/funext => n.
  rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
  rewrite [in X in X + _]/mscore (negbTE Fk0) ir big1 ?adde0// => /= j jk.
  rewrite /mscore.
  have /eqP Fj0 : F j == set0.
    have [/eqP//|Fjtt] := set_unit (F j).
    move/trivIsetP : tF => /(_ j k Logic.I Logic.I jk).
    by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fk0).
  rewrite Fj0 eqxx.
  by case: ifP.
rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
rewrite [in X in if X then _ else _]/mscore (negbTE Fk0) (negbTE ir) add0e.
rewrite big1//= => j jk.
rewrite /mscore.
have /eqP Fj0 : F j == set0.
  have [/eqP//|Fjtt] := set_unit (F j).
  move/trivIsetP : tF => /(_ j k Logic.I Logic.I jk).
  by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fk0).
rewrite Fj0 eqxx.
by case: ifP.
Qed.

HB.instance Definition _ (r : R) (i : nat) (t : T) := isMeasure.Build _ _ _
  (k_' r i t) (k_'0 r i t) (k_'ge0 r i t) (@k_'sigma_additive r i t).

Lemma k_kernelP (r : R) (i : nat) : forall U, measurable U -> measurable_fun setT (k_' r i ^~ U).
Proof.
move=> /= U mU.
rewrite /k_'.
by case: ifPn => _; exact: measurable_fun_cst.
Qed.

Definition mk_' (r : R) i (t : T) := [the measure _ _ of k_' r i t].

HB.instance Definition _ (r : R) (i : nat) :=
  isKernel.Build _ _ R _ _ (mk_' r i) (k_kernelP r i).

Lemma k_uub (r : R) (i : nat) : kernel_uub (mk_' r i).
Proof.
exists (PosNum (ltr0Sn _ i)) => /= t.
rewrite /k_' /mscore setT_unit.
rewrite (_ : [set tt] == set0 = false); last first.
  by apply/eqP => /seteqP[] /(_ tt) /(_ erefl).
by case: ifPn => // /andP[].
Qed.

HB.instance Definition _ (r : R) (i : nat) :=
  @isFiniteKernel.Build _ _ R _ _ (mk_' r i) (k_uub r i).

End kernel_score.
End KERNEL_SCORE.

Section kernel_score_kernel.
Variables (R : realType) (d : _) (T : measurableType d).

Definition kernel_score (r : R) : T -> {measure set _ -> \bar R} :=
  fun _ : T => [the measure _ _ of mscore r].

Lemma kernel_scoreP (r : R) : forall U, measurable U ->
  measurable_fun setT (kernel_score r ^~ U).
Proof.
move=> /= U mU; rewrite /mscore; case: ifP => U0.
  exact: measurable_fun_cst.
apply: measurable_fun_comp => //.
apply/EFin_measurable_fun.
exact: measurable_fun_cst.
Qed.

HB.instance Definition _ (r : R) :=
  isKernel.Build _ _ R T
    _ (*Datatypes_unit__canonical__measure_Measurable*)
    (kernel_score r) (kernel_scoreP r).
End kernel_score_kernel.

Section kernel_score_sfinite_kernel.
Variables (R : realType) (d : _) (T : measurableType d).

Import KERNEL_SCORE.

Lemma kernel_score_sfinite_kernelP (r : R) : exists k_ : (finite_kernel R T _)^nat,
   forall x U, measurable U ->
     kernel_score r x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
exists (fun i => [the finite_kernel _ _ _ of mk_' r i]) => /= r' U mU.
rewrite /mseries /mscore; case: ifPn => [/eqP U0|U0].
  by apply/esym/nneseries0 => i _; rewrite U0 measure0.
rewrite /mk_' /= /k_' /= /mscore (negbTE U0).
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn `|floor (fine `|r%:E|)|%N.+1)/=.
rewrite (_ : (fun _ => _) = cst `|r%:E|); first exact: cvg_cst.
apply/funext => n.
pose floor_r := widen_ord (leq_addl n `|floor `|r| |.+1) (Ordinal (ltnSn `|floor `|r| |)).
rewrite big_mkord (bigD1 floor_r)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|r|)) ?floor_ge0 ?floor_le.
  by rewrite -addn1 natrD natr_absz (@ger0_norm _ (floor `|r|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|r|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|r|)) ?floor_ge0.
- suff : (`|r| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|r|)) ?floor_ge0// ltr_int.
  by rewrite -floor_lt_int.
Qed.

HB.instance Definition _ (r : R) := @isSFiniteKernel.Build _ _ _ _ _
  (kernel_score r) (kernel_score_sfinite_kernelP r).

End kernel_score_sfinite_kernel.

Section ite.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables
  (u1 : sfinite_kernel R
    [the measurableType _ of (T * bool)%type]
    [the measurableType _ of T'])
  (u2 : sfinite_kernel R
    [the measurableType _ of (T * bool)%type]
    [the measurableType _ of T']).

Definition ite : T * bool -> set _ -> \bar R :=
  fun t => if t.2 then u1 t else u2 t.

Lemma ite0 tb : ite tb set0 = 0.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_ge0 tb (U : set _) : 0 <= ite tb U.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_sigma_additive tb : semi_sigma_additive (ite tb).
Proof.
Admitted.

HB.instance Definition _ tb := isMeasure.Build _ _ _
  (ite tb)
  (ite0 tb) (ite_ge0 tb) (@ite_sigma_additive tb).

Lemma ite_kernelP : forall U, measurable U -> measurable_fun setT (ite ^~ U).
Admitted.

Definition mite tb := [the measure _ _ of ite tb].

HB.instance Definition _ := isKernel.Build _ _ R _ _ mite ite_kernelP.

Lemma ite_sfinite_kernelP : exists k_ : (finite_kernel R _ _)^nat,
   forall x U, measurable U ->
     ite x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Admitted.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ _ _ _ _ mite ite_sfinite_kernelP.

End ite.

Section insn.
Variables (R : realType).

Definition sample_bernoulli27 (d : _) (T : measurableType d) :=
  [the sfinite_kernel _ T _ of
   kernel_probability [the probability _ _ of bernoulli27 R]] .

Definition Ite (d d' : _) (T : measurableType d) (T' : measurableType d')
    (u1 : sfinite_kernel R [the measurableType _ of (T * bool)%type]
                           [the measurableType _ of T'])
    (u2 : sfinite_kernel R [the measurableType _ of (T * bool)%type]
                           [the measurableType _ of T'])
    : sfinite_kernel R [the measurableType _ of (T * bool)%type] _ :=
  [the sfinite_kernel R _ _ of mite u1 u2].

Definition Return (d : _) (T : measurableType d) : sfinite_kernel R T T :=
  [the sfinite_kernel _ _ _ of @kernel_dirac R _ _].

Definition Return2 (d d' : _) (T : measurableType d) (T' : measurableType d')
  (f : T -> T') (mf : measurable_fun setT f) : sfinite_kernel R T T' :=
  [the sfinite_kernel _ _ _ of @kernel_dirac2 R _ _ T T' f mf].

Definition Score (d : _) (T : measurableType d) (r : R) :
    sfinite_kernel R T Datatypes_unit__canonical__measure_Measurable :=
  [the sfinite_kernel R _ _ of @kernel_score R _ _ r].

End insn.

Section program1.
Variables (R : realType) (d : _) (T : measurableType d).

Lemma measurable_fun_snd : measurable_fun setT (snd : T * bool -> bool). Admitted.

Definition program1 : sfinite_kernel R T
     _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Return2 R measurable_fun_snd) (* T * B -> B *).

Lemma program1E (t : T) (U : _) : program1 t U =
  ((twoseven R)%:num)%:E * \d_true U +
  ((fiveseven R)%:num)%:E * \d_false U.
Proof.
rewrite /program1/= /star/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//=.
by rewrite indicE in_setT mul1e indicE in_setT mul1e.
Qed.

End program1.

Section program2.
Variables (R : realType) (d : _) (T : measurableType d).

Definition program2  : sfinite_kernel R T Datatypes_unit__canonical__measure_Measurable :=
     letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Score _ (1%:R : R)).

End program2.

Section program3.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)

Definition k3' : T * bool -> R := cst 3%:R.
Definition k10' : T * bool -> R := cst 10%:R.

Lemma mk3 : measurable_fun setT k3'.
exact: measurable_fun_cst.
Qed.

Lemma mk10 : measurable_fun setT k10'.
exact: measurable_fun_cst.
Qed.

Definition program10 : sfinite_kernel R T _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Return2 R mk3).

End program3.
