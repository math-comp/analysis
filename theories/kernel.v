(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral.

(******************************************************************************)
(*                                  Kernels                                   *)
(*                                                                            *)
(*      R.-ker X ~> Y == kernel                                               *)
(*    R.-sfker X ~> Y == s-finite kernel                                      *)
(*     R.-fker X ~> Y == finite kernel                                        *)
(*     R.-pker X ~> Y == probability kernel                                   *)
(*     sum_of_kernels ==                                                      *)
(*             l \; k == composition of kernels                               *)
(*        kernel_mfun == kernel defined by a measurable function              *)
(*     add_of_kernels ==                                                      *)
(******************************************************************************)

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
move=> mA; rewrite -(@probability_setT _ _ _ P).
by apply: le_measure => //; rewrite ?in_setE.
Qed.

End probability_lemmas.
(* /PR 516 in progress *)

(* TODO: PR? *)
Section integralM_0ifneg.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralM_0ifneg (f : R -> T -> \bar R) (k : R)
  (f0 : forall r t, D t -> 0 <= f r t) :
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

(* TODO: PR *)
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

Lemma measurable_fun_fst (d1 d2 : _) (T1 : measurableType d1)
  (T2 : measurableType d2) : measurable_fun setT (@fst T1 T2).
Proof.
have := @measurable_fun_id _ [the measurableType _ of (T1 * T2)%type] setT.
by move=> /prod_measurable_funP[].
Qed.

Lemma measurable_fun_snd (d1 d2 : _) (T1 : measurableType d1)
  (T2 : measurableType d2) : measurable_fun setT (@snd T1 T2).
Proof.
have := @measurable_fun_id _ [the measurableType _ of (T1 * T2)%type] setT.
by move=> /prod_measurable_funP[].
Qed.

Lemma measurable_uncurry (T1 T2 : Type) (d : _) (T : semiRingOfSetsType d)
    (G : T1 -> T2 -> set T) (x : T1 * T2) :
  measurable (G x.1 x.2) <-> measurable (uncurry G x).
Proof. by case: x. Qed.

Lemma measurable_curry (T1 T2 : Type) (d : _) (T : semiRingOfSetsType d)
    (G : T1 * T2 -> set T) (x : T1 * T2) :
  measurable (G x) <-> measurable (curry G x.1 x.2).
Proof. by case: x. Qed.

Lemma measurable_fun_if000 (d d' : _) (T : measurableType d) (T' : measurableType d') (x y : T -> T')
    D (md : measurable D) (f : T -> bool) (mf : measurable_fun setT f) :
  measurable_fun (D `&` [set b | f b ]) x ->
  measurable_fun (D `&` [set b | ~~ f b]) y ->
  measurable_fun D (fun b : T => if f b then x b else y b).
Proof.
move=> mx my /= _ Y mY.
have H1 : measurable (D `&` [set b | f b]).
  apply: measurableI => //.
  rewrite [X in measurable X](_ : _ = f @^-1` [set true])//.
  have := mf measurableT [set true].
  rewrite setTI.
  exact.
have := mx H1 Y mY.
have H0 : [set t | ~~ f t] = [set t | f t = false].
  by apply/seteqP; split => [t/= /negbTE//|t/= ->].
have H2 : measurable (D `&` [set b | ~~ f b]).
  apply: measurableI => //.
  have := mf measurableT [set false].
  rewrite setTI.
  rewrite /preimage/=.
  by rewrite H0; exact.
have := my H2 Y mY.
move=> yY xY.
rewrite (_ : _ @^-1` Y = ([set b | f b = true] `&` (x @^-1` Y) `&` (f @^-1` [set true])) `|`
                         ([set b | f b = false] `&` (y @^-1` Y) `&` (f  @^-1` [set false]))); last first.
  apply/seteqP; split.
    move=> t/=; case: ifPn => ft.
      by left.
    by right.
  by move=> t/= [|]; case: ifPn => ft; case=> -[].
rewrite setIUr.
apply: measurableU.
  rewrite -(setIid D).
  rewrite -(setIA D).
  rewrite setICA.
  rewrite setIA.
  apply: measurableI => //.
  by rewrite setIA.

  rewrite -(setIid D).
  rewrite -(setIA D).
  rewrite setICA.
  rewrite setIA.
  rewrite /preimage/=.
  rewrite -H0.
  apply: measurableI => //.
  by rewrite setIA.
Qed.

Lemma measurable_fun_if00 (d d' : _) (T : measurableType d) (T' : measurableType d') (x y : T -> T')
    (f : T -> bool) (mf : measurable_fun setT f) :
  measurable_fun [set b | f b = true] x ->
  measurable_fun [set b | f b = false] y ->
  measurable_fun setT (fun b : T => if f b then x b else y b).
Proof.
move=> mx my /= _ Y mY.
rewrite setTI.
have H1 : measurable [set b | f b = true].
rewrite [X in measurable X](_ : _ = f @^-1` [set true])//.
  have := mf measurableT [set true].
  rewrite setTI.
  exact.
have := mx H1 Y mY.
have H2 : measurable [set b | f b = false].
  have := mf measurableT [set false].
  rewrite setTI.
  exact.
have := my H2 Y mY.
move=> yY xY.
rewrite (_ : _ @^-1` Y = ([set b | f b = true] `&` (x @^-1` Y) `&` (f @^-1` [set true])) `|`
                         ([set b | f b = false] `&` (y @^-1` Y) `&` (f  @^-1` [set false]))); last first.
  apply/seteqP; split.
    move=> t/=; case: ifPn => ft.
      by left.
    by right.
  by move=> t/= [|]; case: ifPn => ft; case=> -[].
by apply: measurableU; apply: measurableI => //.
Qed.

Lemma measurable_fun_if0 (d d' : _) (T : measurableType d) (T' : measurableType d') (x y : T -> T')
    (f : T -> bool) (mf : measurable_fun setT f) :
  measurable_fun setT x ->
  measurable_fun setT y ->
  measurable_fun setT (fun b : T => if f b then x b else y b).
Proof.
move=> mx my.
apply: measurable_fun_if000 => //.
by apply: measurable_funS mx.
by apply: measurable_funS my.
Qed.

Lemma measurable_fun_if (d d' : _) (T : measurableType d) (T' : measurableType d') (x y : T -> T') :
  measurable_fun setT x ->
  measurable_fun setT y ->
  measurable_fun setT (fun b : T * bool => if b.2 then x b.1 else y b.1).
Proof.
move=> mx my.
have {}mx : measurable_fun [set: T * bool] (x \o fst).
  apply: measurable_fun_comp => //.
  exact: measurable_fun_fst.
have {}my : measurable_fun [set: T * bool] (y \o fst).
  apply: measurable_fun_comp => //.
  exact: measurable_fun_fst.
rewrite /=.
apply: measurable_fun_if0 => //=.
exact: measurable_fun_snd.
Qed.

Lemma emeasurable_itv (R : realType) (i : nat) :
  measurable (`[(i%:R)%:E, (i.+1%:R)%:E[%classic : set \bar R).
Proof.
rewrite -[X in measurable X]setCK.
apply: measurableC.
rewrite set_interval.setCitv /=.
apply: measurableU.
  exact: emeasurable_itv_ninfty_bnd.
exact: emeasurable_itv_bnd_pinfty.
Qed.

Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/seteqP; split => [|] [].
Qed.
(*/ PR*)

Reserved Notation "R .-ker X ~> Y" (at level 42).
Reserved Notation "R .-fker X ~> Y" (at level 42).
Reserved Notation "R .-sfker X ~> Y" (at level 42).
Reserved Notation "R .-pker X ~> Y" (at level 42).

HB.mixin Record isKernel d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { measurable_kernel : forall U, measurable U -> measurable_fun setT (k ^~ U) }.

#[short(type=kernel)]
HB.structure Definition Kernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k & isKernel _ _ X Y R k }.
Notation "R .-ker X ~> Y" := (kernel X Y R).

Arguments measurable_kernel {_ _ _ _ _} _.

Section sum_of_kernels.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variable k : (R.-ker X ~> Y)^nat.

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
by apply: emeasurable_fun_sum => *; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ sum_of_kernels
    kernel_measurable_fun_sum_of_kernels.

End sum_of_kernels.

Lemma integral_sum_of_kernels
  (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType) (k : (R.-ker X ~> Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun setT f ->
  \int[sum_of_kernels k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /sum_of_kernels/= ge0_integral_measure_series.
Qed.

Section measure_fam_uub.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : numFieldType) (k : X -> {measure set Y -> \bar R}).

Definition measure_fam_uub := exists r, forall x, k x [set: Y] < r%:E.

Lemma measure_fam_uubP : measure_fam_uub <->
  exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E.
Proof.
split => [|] [r kr]; last by exists r%:num.
suff r_gt0 : (0 < r)%R by exists (PosNum r_gt0).
by rewrite -lte_fin; apply: (le_lt_trans _ (kr point)).
Qed.

End measure_fam_uub.

HB.mixin Record isFiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { kernel_uub : measure_fam_uub k }.

#[short(type=finite_kernel)]
HB.structure Definition FiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of isFiniteKernel _ _ X Y R k & isKernel _ _ X Y R k}.
Notation "R .-fker X ~> Y" := (finite_kernel X Y R).

Arguments kernel_uub {_ _ _ _ _} _.

Section kernel_from_mzero.
Variables (d : _) (T : measurableType d) (R : realType).
Variables (d' : _) (T' : measurableType d').

Definition kernel_from_mzero : T' -> {measure set T -> \bar R} :=
  fun _ : T' => [the measure _ _ of mzero].

Lemma kernel_from_mzeroP : forall U, measurable U ->
  measurable_fun setT (kernel_from_mzero ^~ U).
Proof. by move=> U mU/=; exact: measurable_fun_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ T' T R kernel_from_mzero
  kernel_from_mzeroP.

Lemma kernel_from_mzero_uub : measure_fam_uub kernel_from_mzero.
Proof. by exists 1%R => /= t; rewrite /mzero/=. Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build _ _ _ T R kernel_from_mzero
  kernel_from_mzero_uub.

End kernel_from_mzero.

HB.mixin Record isSFiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  sfinite : exists s : (R.-fker X ~> Y)^nat,
    forall x U, measurable U ->
      k x U = [the measure _ _ of mseries (s ^~ x) 0] U }.

#[short(type=sfinite_kernel)]
HB.structure Definition SFiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of isSFiniteKernel _ _ X Y R k &
        isKernel _ _ X Y _ k}.
Notation "R .-sfker X ~> Y" := (sfinite_kernel X Y R).

Arguments sfinite {_ _ _ _ _} _.

(* a finite kernel is always an s-finite kernel *)
Section finite_is_sfinite.
Variables (d d' : _) (X : measurableType d) (T : measurableType d').
Variables (R : realType) (k : R.-fker T ~> X).

Lemma sfinite_finite :
  exists k_ : (R.-fker _ ~> _)^nat, forall x U, measurable U ->
    k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
exists (fun n => if n is O then k else
  [the finite_kernel _ _ _ of @kernel_from_mzero _ X R _ T]).
move=> t U mU/=.
rewrite /mseries.
rewrite (nneseries_split 1%N)// big_ord_recl/= big_ord0 adde0.
rewrite ereal_series (@eq_nneseries _ _ (fun=> 0%E)); last by case.
by rewrite nneseries0// adde0.
Qed.

End finite_is_sfinite.

(* TODO: define using the probability type *)
HB.mixin Record isProbabilityFam
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R})
    := {
  prob_kernelP : forall x, k x [set: Y] = 1
}.

#[short(type=probability_kernel)]
HB.structure Definition ProbabilityKernel
    (d d' : _) (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of isProbabilityFam _ _ X Y R k & isKernel _ _ X Y R k & isFiniteKernel _ _ X Y R k & isSFiniteKernel _ _ X Y R k}.
Notation "R .-pker X ~> Y" := (probability_kernel X Y R).

HB.factory Record isProbabilityKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) of isKernel _ _ X Y R k := {
  prob_kernelP2 : forall x, k x [set: Y] = 1
}.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) k of isProbabilityKernel d d' X Y R k.

Lemma is_finite_kernel : measure_fam_uub k.
Proof.
exists 2%R => /= ?.
rewrite (@le_lt_trans _ _ 1%:E)//.
rewrite prob_kernelP2//.
by rewrite lte_fin ltr1n.
Qed.

HB.instance Definition _ := @isFiniteKernel.Build _ _ _ _ _ _ is_finite_kernel.

Lemma is_sfinite_kernel :  exists k_ : (R.-fker _ ~> _)^nat, forall x U, measurable U ->
    k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
exact: sfinite_finite.
Qed.

HB.instance Definition _ := @isSFiniteKernel.Build _ _ _ _ _ _ is_sfinite_kernel.

Lemma is_probability_kernel : forall x, k x setT = 1.
Proof.
exact/prob_kernelP2.
Qed.

HB.instance Definition _ := @isProbabilityFam.Build _ _ _ _ _ _ is_probability_kernel.

HB.end.

(*Section tmp.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType)
  (f : R.-fker T ~> T').

Let tmp : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    f x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: sfinite_finite. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build d d' T T' R f tmp.
End tmp.*)

(* see measurable_prod_subset in lebesgue_integral.v;
   the differences between the two are:
   - m2 is a kernel instead of a measure
   - m2D_bounded holds for all x *)
Section measurable_prod_subset_kernel.
Variables (d1 d2 : _) (T1 : measurableType d1) (T2 : measurableType d2)
          (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection_kernel.
Variable (m2 : R.-ker T1 ~> T2) (D : set T2) (mD : measurable D).
Let m2D x := mrestr (m2 x) mD.
HB.instance Definition _ x := Measure.on (m2D x).
Let phi A := fun x => m2D x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_prod_subset_xsection_kernel
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
  apply: emeasurable_funM => //; first exact/measurable_kernel/measurableI.
  apply/EFin_measurable_fun.
  by rewrite (_ : \1_ _ = mindic R mX1).
suff monoB : monotone_class setT B by exact: monotone_class_subset.
split => //; [exact: CB| |exact: xsection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
suff : phi (X `\` Y) = (fun x => phi X x - phi Y x)%E.
  by move=> ->; exact: emeasurable_funB.
rewrite funeqE => x; rewrite /phi/= xsectionD// /m2D measureD.
- by rewrite setIidr//; exact: le_xsection.
- exact: measurable_xsection.
- exact: measurable_xsection.
- move: (m2D_bounded x) => [M m2M].
  rewrite (lt_le_trans (m2M (xsection X x) _))// ?leey//.
  exact: measurable_xsection.
Qed.

End xsection_kernel.

End measurable_prod_subset_kernel.

(* see measurable_fun_xsection in lebesgue_integral.v
   the difference is that this section uses a finite kernel m2
   instead of a sigma-finite measure m2 *)
Section measurable_fun_xsection_finite_kernel.
Variables (d1 d2 : _) (T1 : measurableType d1) (T2 : measurableType d2)
          (R : realType).
Variable m2 : R.-fker T1 ~> T2.
Implicit Types A : set (T1 * T2).

Let phi A := fun x => m2 x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection_finite_kernel A :
  A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A; rewrite inE => /[apply] -[].
move=> X mX.
rewrite /B/=; split => //.
rewrite /phi.
rewrite -(_ : (fun x => mrestr (m2 x) measurableT (xsection X x)) =
              (fun x => (m2 x) (xsection X x)))//; last first.
  by apply/funext => x//=; rewrite /mrestr setIT.
apply measurable_prod_subset_xsection_kernel => //.
move=> x.
have [r hr] := kernel_uub m2.
exists r => Y mY.
apply: (le_lt_trans _ (hr x)) => //.
rewrite /mrestr.
by apply le_measure => //; rewrite inE//; exact: measurableI.
Qed.

End measurable_fun_xsection_finite_kernel.

(* pollard *)
Section measurable_fun_integral_finite_sfinite.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType).

Lemma measurable_fun_xsection_integral
    (l : X -> {measure set Y -> \bar R})
    (k : X * Y -> \bar R)
    (k_ : ({nnsfun [the measurableType _ of (X * Y)%type] >-> R})^nat)
    (ndk_ : nondecreasing_seq (k_ : (X * Y -> R)^nat))
    (k_k : forall z, EFin \o (k_ ^~ z) --> k z) :
  (forall n r, measurable_fun setT (fun x => l x (xsection (k_ n @^-1` [set r]) x))) ->
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
move=> h.
rewrite (_ : (fun x => _) =
    (fun x => elim_sup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funext => x.
  transitivity (lim (fun n => \int[l x]_y (k_ n (x, y))%:E)); last first.
    rewrite is_cvg_elim_supE//.
    apply: ereal_nondecreasing_is_cvg => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y _; rewrite lee_fin; exact/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/ndk_.
apply: measurable_fun_elim_sup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \int[l x]_y
  (\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x =>
  \sum_(r <- fset_set (range (k_ n)))
    (\int[l x]_y (r * \1_(k_ n @^-1` [set r]) (x, y))%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_sum//.
  - by apply: eq_integral => y _; rewrite sumEFin.
  - move=> r.
    apply/EFin_measurable_fun/measurable_funrM/measurable_fun_prod1 => /=.
    rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r))//.
    exact/measurable_funP.
  - by move=> m y _; rewrite muleindic_ge0.
apply emeasurable_fun_sum => r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => r%:E *
    \int[l x]_y (\1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite (integralM_0ifneg _ _ (fun k y => (\1_(k_ n @^-1` [set r]) (x, y))%:E))//.
  - by move=> _ y _; rewrite lee_fin.
  - by move=> r0; apply/funext => y; rewrite preimage_nnfun0// indicE in_set0.
  - apply/EFin_measurable_fun/measurable_fun_prod1 => /=.
    rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r))//.
    exact/measurable_funP.
apply/measurable_funeM.
rewrite (_ : (fun x => _) = (fun x => l x (xsection (k_ n @^-1` [set r]) x))).
  exact/h.
apply/funext => x; rewrite integral_indic//; last first.
  rewrite (_ : (fun x => _) = xsection (k_ n @^-1` [set r]) x).
    exact: measurable_xsection.
  by rewrite /xsection; apply/seteqP; split=> y/= /[!inE].
congr (l x _); apply/funext => y1/=; rewrite /xsection/= inE.
by apply/propext; tauto.
Qed.

Lemma measurable_fun_integral_finite_kernel
    (l : R.-fker X ~> Y)
    (k : X * Y -> \bar R) (k0 : forall z, 0 <= k z) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun x _ => k0 x).
apply: (measurable_fun_xsection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := kernel_uub l.
by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

Lemma measurable_fun_integral_sfinite_kernel
    (l : R.-sfker X ~> Y)
    (k : X * Y -> \bar R) (k0 : forall t, 0 <= k t) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun xy _ => k0 xy).
apply: (measurable_fun_xsection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := sfinite l.
rewrite (_ : (fun x => _) =
    (fun x => mseries (l_ ^~ x) 0 (xsection (k_ n @^-1` [set r]) x))); last first.
  by apply/funext => x; rewrite hl_//; exact/measurable_xsection.
apply: ge0_emeasurable_fun_sum => // m.
by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

End measurable_fun_integral_finite_sfinite.
Arguments measurable_fun_xsection_integral {_ _ _ _ _} l k.
Arguments measurable_fun_integral_finite_kernel {_ _ _ _ _} l k.
Arguments measurable_fun_integral_sfinite_kernel {_ _ _ _ _} l k.

Section kcomp_def.
Variables (d1 d2 d3 : _) (X : measurableType d1) (Y : measurableType d2)
          (Z : measurableType d3) (R : realType).
Variable l : X -> {measure set Y -> \bar R}.
Variable k : (X * Y)%type -> {measure set Z -> \bar R}.

Definition kcomp x U := \int[l x]_y k (x, y) U.

End kcomp_def.

Section kcomp_is_measure.
Variables (d1 d2 d3 : _) (X : measurableType d1) (Y : measurableType d2)
          (Z : measurableType d3) (R : realType).
Variable l : R.-ker X ~> Y.
Variable k : R.-ker [the measurableType _ of (X * Y)%type] ~> Z.

Local Notation "l \; k" := (kcomp l k).

Let kcomp0 x : (l \; k) x set0 = 0.
Proof.
by rewrite /kcomp (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let kcomp_ge0 x U : 0 <= (l \; k) x U. Proof. exact: integral_ge0. Qed.

Let kcomp_sigma_additive x : semi_sigma_additive ((l \; k) x).
Proof.
move=> U mU tU mUU; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (U n)))%E; last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE// integral_sum// => n.
by have /measurable_fun_prod1 := measurable_kernel k (U n) (mU n).
Qed.

HB.instance Definition _ x := isMeasure.Build _ R _
  ((l \; k) x) (kcomp0 x) (kcomp_ge0 x) (@kcomp_sigma_additive x).

Definition mkcomp : X -> {measure set Z -> \bar R} :=
  fun x => [the measure _ _ of (l \; k) x].

End kcomp_is_measure.

Notation "l \; k" := (mkcomp l k).

Module KCOMP_FINITE_KERNEL.

Section kcomp_finite_kernel_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType) (l : R.-fker X ~> Y)
          (k : R.-ker [the measurableType _ of (X * Y)%type] ~> Z).

Lemma measurable_fun_kcomp_finite U :
  measurable U -> measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_finite_kernel _ (k ^~ U)) => //=.
exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) measurable_fun_kcomp_finite.

End kcomp_finite_kernel_kernel.

Section kcomp_finite_kernel_finite.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-fker X ~> Y.
Variable k : R.-fker [the measurableType _ of (X * Y)%type] ~> Z.

Lemma mkcomp_finite : measure_fam_uub (l \; k).
Proof.
have /measure_fam_uubP[r hr] := kernel_uub k.
have /measure_fam_uubP[s hs] := kernel_uub l.
apply/measure_fam_uubP; exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x /=.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply: ge0_le_integral => //.
  - have /measurable_fun_prod1 := measurable_kernel k setT measurableT.
    exact.
  - exact/measurable_fun_cst.
  - by move=> y _; exact/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  isFiniteKernel.Build _ _ X Z R (l \; k) mkcomp_finite.

End kcomp_finite_kernel_finite.
End KCOMP_FINITE_KERNEL.

Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z.

Import KCOMP_FINITE_KERNEL.

Lemma mkcomp_sfinite : exists k_ : (R.-fker X ~> Z)^nat, forall x U, measurable U ->
  (l \; k) x U = [the measure _ _ of mseries (k_ ^~ x) O] U.
Proof.
have [k_ hk_] := sfinite k.
have [l_ hl_] := sfinite l.
pose K := [the kernel _ _ _ of sum_of_kernels k_].
pose L := [the kernel _ _ _ of sum_of_kernels l_].
have H1 x U : measurable U -> (l \; k) x U = (L \; K) x U.
  move=> mU /=.
  rewrite /kcomp /L /K /=.
  (* TODO: lemma so that we can get away with a rewrite *)
  transitivity (\int[
    [the measure _ _ of mseries (l_ ^~ x) 0] ]_y k (x, y) U).
    by apply eq_measure_integral => A mA _; rewrite hl_.
  by apply eq_integral => y _; rewrite hk_.
have H2 x U : (L \; K) x U =
  \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U).
  exact: eq_integral.
have H3 x U : measurable U ->
     \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U) =
     \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U).
   move=> mU.
   rewrite integral_sum//= => n.
   have := measurable_kernel (k_ n) _ mU.
   by move=> /measurable_fun_prod1; exact.
have H4 x U : measurable U ->
    \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U) =
    \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U.
  move=> mU.
  apply: eq_nneseries => i _.
  rewrite integral_sum_of_kernels//.
  have := measurable_kernel (k_ i) _ mU.
  by move=> /measurable_fun_prod1; exact.
have H5 x U : \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U =
  \sum_(i <oo) \sum_(j <oo) (l_ j \; k_ i) x U.
  by apply eq_nneseries => i _; exact: eq_nneseries.
suff: exists k_0 : (R.-fker X ~> Z) ^nat, forall x U,
    \esum_(i in setT) ((l_ i.2) \; (k_ i.1)) x U = \sum_(i <oo) k_0 i x U.
  move=> [kl_ hkl_].
  exists kl_ => x U mU.
  rewrite /= H1// H2 H3// H4// H5// /mseries -hkl_/=.
  rewrite (_ : setT = setT `*`` (fun=> setT)); last by apply/seteqP; split.
  rewrite -(@esum_esum _ _ _ _ _ (fun i j => (l_ j \; k_ i) x U))//.
  rewrite nneseries_esum; last by move=> n _; exact: nneseries_lim_ge0.
  by rewrite fun_true; apply: eq_esum => /= i _; rewrite nneseries_esum// fun_true.
rewrite /=.
have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
  by rewrite card_eq_sym; exact: card_nat2.
exists (fun i => [the _.-fker _ ~> _ of (l_ (f i).2) \; (k_ (f i).1)]) => x U.
rewrite (reindex_esum [set: nat] [set: nat * nat] f)//.
by rewrite nneseries_esum// fun_true.
Qed.

Lemma measurable_fun_mkcomp_sfinite U : measurable U ->
  measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_sfinite_kernel _ (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

End kcomp_sfinite_kernel.

Module KCOMP_SFINITE_KERNEL.
Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) (measurable_fun_mkcomp_sfinite l k).

#[export]
HB.instance Definition _ :=
  isSFiniteKernel.Build _ _ X Z R (l \; k) (mkcomp_sfinite l k).

End kcomp_sfinite_kernel.
End KCOMP_SFINITE_KERNEL.
HB.export KCOMP_SFINITE_KERNEL.

(* pollard? *)
Section measurable_fun_integral_kernel'.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType).
Variables (l : X -> {measure set Y -> \bar R})
  (k : Y -> \bar R)
  (k_ : ({nnsfun Y >-> R}) ^nat)
  (ndk_ : nondecreasing_seq (k_ : (Y -> R)^nat))
  (k_k : forall z, setT z -> EFin \o (k_ ^~ z) --> k z).

Let p : (X * Y -> R)^nat := fun n xy => k_ n xy.2.

Let p_ge0 n x : (0 <= p n x)%R. Proof. by []. Qed.

HB.instance Definition _ n := @IsNonNegFun.Build _ R (p n) (p_ge0 n).

Let mp n : measurable_fun setT (p n).
Proof.
rewrite /p => _ /= B mB; rewrite setTI.
have mk_n : measurable_fun setT (k_ n) by [].
rewrite (_ : _ @^-1` _ = setT `*` (k_ n @^-1` B)); last first.
  by apply/seteqP; split => xy /=; tauto.
apply: measurableM => //.
have := mk_n measurableT _ mB.
by rewrite setTI.
Qed.

HB.instance Definition _ n := @IsMeasurableFun.Build _ _ R (p n) (mp n).

Let fp n : finite_set (range (p n)).
Proof.
have := @fimfunP _ _ (k_ n).
suff : range (k_ n) = range (p n) by move=> <-.
by apply/seteqP; split => r [y ?] <-; [exists (point, y)|exists y.2].
Qed.

HB.instance Definition _ n := @FiniteImage.Build _ _ (p n) (fp n).

Lemma measurable_fun_preimage_integral :
  (forall n r, measurable_fun setT (fun x => l x (k_ n @^-1` [set r]))) ->
  measurable_fun setT (fun x => \int[l x]_z k z).
Proof.
move=> h.
apply: (measurable_fun_xsection_integral l (fun xy => k xy.2)
  (fun n => [the {nnsfun _ >-> _} of p n])) => /=.
- by rewrite /p => m n mn; apply/lefP => -[x y] /=; exact/lefP/ndk_.
- by move=> [x y]; exact: k_k.
- move=> n r _ /= B mB.
  have := h n r measurableT B mB.
  rewrite !setTI.
  suff : ((fun x => l x (k_ n @^-1` [set r])) @^-1` B) =
         ((fun x => l x (xsection (p n @^-1` [set r]) x)) @^-1` B) by move=> ->.
  apply/seteqP; split => x/=.
    suff : (k_ n @^-1` [set r]) = (xsection (p n @^-1` [set r]) x) by move=> ->.
    by apply/seteqP; split; move=> y/=;
      rewrite /xsection/= /p /preimage/= inE/=.
  suff : (k_ n @^-1` [set r]) = (xsection (p n @^-1` [set r]) x) by move=> ->.
  by apply/seteqP; split; move=> y/=; rewrite /xsection/= /p /preimage/= inE/=.
Qed.

End measurable_fun_integral_kernel'.

Lemma measurable_fun_integral_kernel
    (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType)
    (l : R.-ker [the measurableType _ of (X * Y)%type] ~> Z) c
    (k : Z -> \bar R) (k0 : forall z, True -> 0 <= k z) (mk : measurable_fun setT k) :
  measurable_fun setT (fun y => \int[l (c, y)]_z k z).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk k0.
apply: (measurable_fun_preimage_integral ndk_ k_k) => n r.
have := measurable_kernel l (k_ n @^-1` [set r]) (measurable_sfunP (k_ n) r).
by move=> /measurable_fun_prod1; exact.
Qed.

Section integral_kcomp.

Let integral_kcomp_indic d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x (E : set _) (mE : measurable E) :
  \int[(l \; k) x]_z (\1_E z)%:E = \int[l x]_y (\int[k (x, y)]_z (\1_E z)%:E).
Proof.
rewrite integral_indic//= /kcomp.
by apply eq_integral => y _; rewrite integral_indic.
Qed.

Let integral_kcomp_nnsfun d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x (f : {nnsfun Z >-> R}) :
  \int[(l \; k) x]_z (f z)%:E = \int[l x]_y (\int[k (x, y)]_z (f z)%:E).
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
  - move=> r; apply: measurable_funeM.
    have := measurable_kernel k (f @^-1` [set r]) (measurable_sfunP f r).
    by move=> /measurable_fun_prod1; exact.
  - move=> n y _.
    have := @mulem_ge0 _ _ _ (k (x, y)) n (fun n => f @^-1` [set n]).
    by apply; exact: preimage_nnfun0.
apply eq_bigr => r _.
rewrite (@integralM_indic _ _ _ _ _ _ (fun r => f @^-1` [set r]))//; last first.
  exact: preimage_nnfun0.
rewrite /= integral_kcomp_indic; last exact/measurable_sfunP.
rewrite (@integralM_0ifneg _ _ _ _ _ _ (fun r t => k (x, t) (f @^-1` [set r])))//; last 2 first.
  move=> r0.
  apply/funext => y.
  by rewrite preimage_nnfun0// measure0.
  have := measurable_kernel k (f @^-1` [set r]) (measurable_sfunP f r).
  by move/measurable_fun_prod1; exact.
congr (_ * _); apply eq_integral => y _.
by rewrite integral_indic// setIT.
Qed.

Lemma integral_kcomp d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x f : (forall z, 0 <= f z) -> measurable_fun setT f ->
  \int[(l \; k) x]_z f z = \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
move=> f0 mf.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun z _ => f0 z).
transitivity (\int[(l \; k) x]_z (lim (EFin \o (f_^~ z)))).
  apply/eq_integral => z _.
  apply/esym/cvg_lim => //=.
  exact: f_f.
rewrite monotone_convergence//; last 3 first.
  by move=> n; apply/EFin_measurable_fun.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b /ndf_ /lefP ab; rewrite lee_fin.
rewrite (_ : (fun _ => _) = (fun n => \int[l x]_y (\int[k (x, y)]_z (f_ n z)%:E)))//; last first.
  by apply/funext => n; rewrite integral_kcomp_nnsfun.
transitivity (\int[l x]_y lim (fun n => \int[k (x, y)]_z (f_ n z)%:E)).
  rewrite -monotone_convergence//; last 3 first.
  move=> n.
  apply: measurable_fun_integral_kernel => //.
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

End integral_kcomp.

Definition finite_measure d (T : measurableType d) (R : realType) (mu : set T -> \bar R) :=
  mu setT < +oo.

Lemma finite_kernel_finite_measure d (T : measurableType d) (R : realType)
  (mu : R.-fker Datatypes_unit__canonical__measure_Measurable ~> T) :
  finite_measure (mu tt).
Proof.
have [M muM] := kernel_uub mu.
by rewrite /finite_measure (lt_le_trans (muM tt))// leey.
Qed.

Lemma finite_measure_sigma_finite d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) :
  finite_measure mu -> sigma_finite setT mu.
Proof.
rewrite /finite_measure => muoo.
exists (fun i => if i \in [set 0%N] then setT else set0).
  by rewrite -bigcup_mkcondr setTI bigcup_const//; exists 0%N.
move=> n; split; first by case: ifPn.
by case: ifPn => // _; rewrite measure0.
Qed.

Section finite_fubini.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d') (R : realType).
Variables (mu : {measure set X -> \bar R}) (fmu : finite_measure mu).
Variables (la : {measure set Y -> \bar R}) (fla : finite_measure la).
Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
Variables (mf : measurable_fun setT f).

Lemma finite_fubini :
  \int[mu]_x \int[la]_y f (x, y) = \int[la]_y \int[mu]_x f (x, y).
Proof.
rewrite -fubini_tonelli1//.
  exact: finite_measure_sigma_finite.
move=> H.
rewrite fubini_tonelli2//.
exact: finite_measure_sigma_finite.
Qed.

End finite_fubini.

Section sfinite_fubini.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d') (R : realType).
Variables (mu : R.-sfker Datatypes_unit__canonical__measure_Measurable ~> X).
Variables (la : R.-sfker Datatypes_unit__canonical__measure_Measurable ~> Y).
Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
Variable (mf : measurable_fun setT f).

Lemma sfinite_fubini :
  \int[mu tt]_x \int[la tt]_y f (x, y) = \int[la tt]_y \int[mu tt]_x f (x, y).
Proof.
have [mu_ mu_E] := sfinite mu.
have [la_ la_E] := sfinite la.
transitivity (
  \int[[the measure _ _ of mseries (fun i => mu_ i tt) 0]]_x
  \int[la tt]_y f (x, y)).
  apply: eq_measure_integral => U mU _. (* TODO: awkward *)
  by rewrite mu_E.
transitivity (
  \int[[the measure _ _ of mseries (fun i => mu_ i tt) 0]]_x
  \int[[the measure _ _ of mseries (fun i => la_ i tt) 0]]_y f (x, y)).
  apply eq_integral => x _.
  apply: eq_measure_integral => U mU _. (* TODO: awkward *)
  by rewrite la_E.
transitivity (\sum_(n <oo) \int[mu_ n tt]_x \sum_(m <oo) \int[la_ m tt]_y f (x, y)).
  rewrite ge0_integral_measure_series; last 3 first.
    by [].
    by move=> t _; exact: integral_ge0 => x _.
(*    have := @measurable_fun_integral_sfinite_kernel _ _ _ Y R la.
    rewrite /=.*)
    rewrite /=.
    rewrite [X in measurable_fun _ X](_ : _ =
      fun x => \sum_(n <oo) \int[la_ n tt]_y f (x, y)); last first.
      apply/funext => x.
      rewrite ge0_integral_measure_series//.
      exact/measurable_fun_prod1.
    apply: ge0_emeasurable_fun_sum => //.
      move=> k x.
      by apply: integral_ge0.
    move=> k.
    apply: measurable_fun_fubini_tonelli_F => //=.
    apply: finite_measure_sigma_finite.
    exact: finite_kernel_finite_measure.
  apply: eq_nneseries => n _; apply eq_integral => x _.
  rewrite ge0_integral_measure_series//.
  exact/measurable_fun_prod1.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[mu_ n tt]_x \int[la_ m tt]_y f (x, y)).
  apply eq_nneseries => n _.
  rewrite integral_sum(*TODO: ge0_integral_sum*)//.
    move=> m.
    apply: measurable_fun_fubini_tonelli_F => //=.
    apply: finite_measure_sigma_finite.
    exact: finite_kernel_finite_measure.
  by move=> m x _; exact: integral_ge0.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[la_ m tt]_y \int[mu_ n tt]_x f (x, y)).
  apply eq_nneseries => n _; apply eq_nneseries => m _.
  rewrite finite_fubini//.
  exact: finite_kernel_finite_measure.
  exact: finite_kernel_finite_measure.
transitivity (\sum_(n <oo) \int[[the measure _ _ of mseries (fun i => la_ i tt) 0]]_y \int[mu_ n tt]_x f (x, y)).
  apply eq_nneseries => n _.
  rewrite /= ge0_integral_measure_series//.
    by move=> y _; exact: integral_ge0.
  apply: measurable_fun_fubini_tonelli_G => //=.
  apply: finite_measure_sigma_finite.
  exact: finite_kernel_finite_measure.
rewrite /=.
transitivity (\int[[the measure _ _ of mseries (fun i => la_ i tt) 0]]_y \sum_(n <oo) \int[mu_ n tt]_x f (x, y)).
  rewrite integral_sum//.
    move=> n.
    apply: measurable_fun_fubini_tonelli_G => //=.
    apply: finite_measure_sigma_finite.
    exact: finite_kernel_finite_measure.
  by move=> n y _; exact: integral_ge0.
rewrite /=.
transitivity (\int[[the measure _ _ of mseries (fun i => la_ i tt) 0]]_y \int[[the measure _ _ of mseries (fun i => mu_ i tt) 0]]_x f (x, y)).
  apply eq_integral => y _.
  rewrite ge0_integral_measure_series//.
  exact/measurable_fun_prod2.
rewrite /=.
transitivity (
  \int[la tt]_y \int[mseries (fun i : nat => mu_ i tt) 0]_x f (x, y)
).
  apply eq_measure_integral => A mA _ /=.
  by rewrite la_E.
apply eq_integral => y _.
apply eq_measure_integral => A mA _ /=.
by rewrite mu_E.
Qed.

End sfinite_fubini.

(* semantics for a sample operation *)
Section kernel_probability.
Variables (d d' : _) (R : realType) (X : measurableType d) (T' : measurableType d').
Variable m : probability X R.

Definition kernel_probability : T' -> {measure set X -> \bar R} :=
  fun _ : T' => m.

Lemma kernel_probabilityP U : measurable U ->
  measurable_fun setT (kernel_probability ^~ U).
Proof. by move=> mU; exact: measurable_fun_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ _ X R kernel_probability kernel_probabilityP.

Lemma kernel_probability' x : kernel_probability x [set: X] = 1.
Proof. by rewrite /kernel_probability/= probability_setT. Qed.

HB.instance Definition _ :=
  @isProbabilityKernel.Build _ _ _ X R kernel_probability kernel_probability'.

End kernel_probability.

Section kernel_of_mfun.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (f : T -> T').

Definition kernel_mfun (mf : measurable_fun setT f) : T -> {measure set T' -> \bar R} :=
  fun t => [the measure _ _ of dirac (f t)].

Hypothesis mf : measurable_fun setT f.

Lemma measurable_kernel_mfun U : measurable U -> measurable_fun setT (kernel_mfun mf ^~ U).
Proof.
move=> mU.
apply/EFin_measurable_fun.
rewrite (_ : (fun x => _) = mindic R mU \o f)//.
exact/measurable_fun_comp.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R (kernel_mfun mf)
  measurable_kernel_mfun.

Lemma kernel_mfun_uub : measure_fam_uub (kernel_mfun mf).
Proof. by exists 2%R => t/=; rewrite diracE in_setT lte_fin ltr_addr. Qed.

HB.instance Definition _ := isFiniteKernel.Build _ _ _ _ R (kernel_mfun mf)
  kernel_mfun_uub.

Lemma sfinite_kernel_mfun : exists k_ : (R.-fker _ ~> _)^nat,
   forall x U, measurable U ->
     kernel_mfun mf x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: sfinite_finite. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ _ _ _ _ (kernel_mfun mf) sfinite_kernel_mfun.

End kernel_of_mfun.

Section add_of_kernels.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variables (u1 u2 : R.-ker X ~> Y).

Definition add_of_kernels : X -> {measure set Y -> \bar R} :=
  fun t => [the measure _ _ of measure_add (u1 t) (u2 t)].

Lemma measurable_add_of_kernels U : measurable U -> measurable_fun setT (add_of_kernels ^~ U).
Proof.
move=> mU.
rewrite /add_of_kernels.
rewrite (_ : (fun x : X => _) = (fun x => (u1 x U) + (u2 x U))); last first.
  apply/funext => x.
  by rewrite -measure_addE.
by apply: emeasurable_funD; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ _ _ _ add_of_kernels measurable_add_of_kernels.
End add_of_kernels.

Section add_of_finite_kernels.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variables (u1 u2 : R.-fker X ~> Y).

Lemma add_of_finite_kernels_uub : measure_fam_uub (add_of_kernels u1 u2).
Proof.
have [k1 hk1] := kernel_uub u1.
have [k2 hk2] := kernel_uub u2.
exists (k1 + k2)%R => x.
rewrite /add_of_kernels/=.
rewrite -/(measure_add (u1 x) (u2 x)).
rewrite measure_addE.
rewrite EFinD.
exact: lte_add.
Qed.

HB.instance Definition _ t :=
  isFiniteKernel.Build _ _ _ _ R (add_of_kernels u1 u2) add_of_finite_kernels_uub.
End add_of_finite_kernels.

Section add_of_sfinite_kernels.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (u1 u2 : R.-sfker X ~> Y).

Lemma sfinite_add_of_kernels : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    add_of_kernels u1 u2 x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k1 hk1] := sfinite u1.
have [k2 hk2] := sfinite u2.
exists (fun n => [the finite_kernel _ _ _ of add_of_kernels (k1 n) (k2 n)]) => x U mU.
rewrite /add_of_kernels/=.
rewrite -/(measure_add (u1 x) (u2 x)).
rewrite measure_addE.
rewrite /mseries.
rewrite hk1//= hk2//= /mseries.
rewrite -nneseriesD//.
apply: eq_nneseries => n _.
rewrite -/(measure_add (k1 n x) (k2 n x)).
by rewrite measure_addE.
Qed.

HB.instance Definition _ t :=
  isSFiniteKernel.Build _ _ _ _ R (add_of_kernels u1 u2) sfinite_add_of_kernels.
End add_of_sfinite_kernels.

Section normalize_measure.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : T -> {measure set T' -> \bar R}) (P : probability T' R).

Definition normalize (t : T) (U : set T') :=
  let evidence := f t setT in
  if evidence == 0%E then P U
  else if evidence == +oo then P U
  else f t U * (fine evidence)^-1%:E.

Lemma normalize0 t : normalize t set0 = 0.
Proof.
rewrite /normalize.
case: ifPn => // _.
case: ifPn => // _.
by rewrite measure0 mul0e.
Qed.

Lemma normalize_ge0 t U : 0 <= normalize t U.
Proof.
by rewrite /normalize; case: ifPn => //; case: ifPn.
Qed.

Lemma normalize_sigma_additive t : semi_sigma_additive (normalize t).
Proof.
move=> F mF tF mUF.
rewrite /normalize/=.
case: ifPn => [_|_].
  exact: measure_semi_sigma_additive.
case: ifPn => [_|_].
  exact: measure_semi_sigma_additive.
rewrite (_ : (fun n => _) = ((fun n=> \sum_(0 <= i < n) f t (F i)) \* cst ((fine (f t [set: T']))^-1)%:E)); last first.
  by apply/funext => n; rewrite -ge0_sume_distrl.
by apply: ereal_cvgMr => //; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ (t : T) := isMeasure.Build _ _ _
  (normalize t) (normalize0 t) (normalize_ge0 t) (@normalize_sigma_additive t).

Lemma normalize1 t : normalize t setT = 1.
Proof.
rewrite /normalize; case: ifPn.
  by rewrite probability_setT.
case: ifPn.
  by rewrite probability_setT.
move=> ftoo ft0.
have ? : f t [set: T'] \is a fin_num.
  by rewrite ge0_fin_numE// lt_neqAle ftoo/= leey.
rewrite -{1}(@fineK _ (f t setT))//.
by rewrite -EFinM divrr// ?unitfE fine_eq0.
Qed.

HB.instance Definition _ t := isProbability.Build _ _ _ (normalize t) (normalize1 t).

End normalize_measure.

Section measurable_fun_comp.
Variables (d1 d2 d3 : measure_display).
Variables (T1 : measurableType d1).
Variables (T2 : measurableType d2).
Variables (T3 : measurableType d3).

Lemma measurable_fun_comp_new F (f : T2 -> T3) E (g : T1 -> T2) :
  measurable F ->
  g @` E `<=` F ->
  measurable_fun F f -> measurable_fun E g -> measurable_fun E (f \o g).
Proof.
move=> mF FgE mf mg /= mE A mA.
rewrite comp_preimage.
rewrite [X in measurable X](_ : _ = (E `&` g @^-1` (F `&` f @^-1` A))); last first.
  apply/seteqP; split.
    move=> x/= [Ex Afgx]; split => //; split => //.
    by apply: FgE => //.
  by move=> x/= [Ex] [Fgx Afgx].
apply/mg => //.
by apply: mf => //.
Qed.

End measurable_fun_comp.

Lemma open_continuousP (S T : topologicalType) (f : S -> T) (D : set S) :
  open D ->
  {in D, continuous f} <-> (forall A, open A -> open (D `&` f @^-1` A)).
Proof.
move=> oD; split=> [fcont|fcont s /[!inE] sD A].
  rewrite !openE => A Aop s [Ds] /Aop /fcont; rewrite inE => /(_ Ds) fsA.
  by rewrite interiorI; split => //; move: oD; rewrite openE; exact.
rewrite nbhs_simpl /= !nbhsE => - [B [[oB Bfs] BA]].
by exists (D `&` f @^-1` B); split=> [|t [Dt] /BA//]; split => //; exact/fcont.
Qed.

Lemma open_continuous_measurable_fun (R : realType) (f : R -> R) D :
  open D -> {in D, continuous f} -> measurable_fun D f.
Proof.
move=> oD /(open_continuousP _ oD) cf.
apply: (measurability (RGenOpens.measurableE R)) => _ [_ [a [b ->] <-]].
by apply: open_measurable; exact/cf/interval_open.
Qed.

Lemma set_boolE (B : set bool) : [\/ B == [set true], B == [set false], B == set0 | B == setT].
Proof.
have [Bt|Bt] := boolP (true \in B).
  have [Bf|Bf] := boolP (false \in B).
    have -> : B = setT.
      by apply/seteqP; split => // -[] _; [rewrite inE in Bt| rewrite inE in Bf].
    apply/or4P.
    by rewrite eqxx/= !orbT.
  have -> : B = [set true].
      apply/seteqP; split => -[]//=.
        by rewrite notin_set in Bf.
      by rewrite inE in Bt.
  apply/or4P.
  by rewrite eqxx/=.
have [Bf|Bf] := boolP (false \in B).
  have -> : B = [set false].
    apply/seteqP; split => -[]//=.
      by rewrite notin_set in Bt.
    by rewrite inE in Bf.
  apply/or4P.
  by rewrite eqxx/= orbT.
have -> : B = set0.
  apply/seteqP; split => -[]//=.
    by rewrite notin_set in Bt.
  by rewrite notin_set in Bf.
apply/or4P.
by rewrite eqxx/= !orbT.
Qed.

Lemma measurable_eq_cst (d d' : _) (T : measurableType d) (T' : measurableType d')
    (R : realType) (f : R.-ker T ~> T') k :
  measurable [set t | f t setT == k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` [set k]); last first.
  by apply/seteqP; split => t/= /eqP.
rewrite /=.
have := measurable_kernel f setT measurableT.
rewrite /=.
move/(_ measurableT [set k]).
rewrite setTI.
exact.
Qed.

Lemma measurable_neq_cst (d d' : _) (T : measurableType d) (T' : measurableType d')
    (R : realType) (f : R.-ker T ~> T') k : measurable [set t | f t setT != k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` (setT `\` [set k])); last first.
  apply/seteqP; split => t/=.
    by move/eqP; tauto.
  by move=> []? /eqP; tauto.
rewrite /=.
have := measurable_kernel f setT measurableT.
rewrite /=.
move/(_ measurableT (setT `\` [set k])).
rewrite setTI.
apply => //.
exact: measurableD.
Qed.

Lemma measurable_fun_eq_cst (d d' : _) (T : measurableType d) (T' : measurableType d')
  (R : realType) (f : R.-ker T ~> T') k : measurable_fun [set: T] (fun b : T => f b setT == k).
Proof.
move=> _ /= B mB.
rewrite setTI.
have [/eqP->|/eqP->|/eqP->|/eqP->] := set_boolE B.
- exact: measurable_eq_cst.
- rewrite (_ : _ @^-1` _ = [set b | f b setT != k]); last first.
    apply/seteqP; split => t/=.
      by move/negbT.
    by move/negbTE.
  exact: measurable_neq_cst.
- by rewrite preimage_set0.
- by rewrite preimage_setT.
Qed.

(* TODO: PR *)
Lemma measurable_fun_fine (R : realType) : measurable_fun [set: \bar R] fine.
Proof.
move=> _ /= B mB.
rewrite setTI [X in measurable X](_ : _ @^-1` _ =
    if 0%R \in B then (EFin @` B) `|` [set -oo; +oo] else EFin @` B); last first.
  apply/seteqP; split=> [[r Br|B0|B0]|].
      case: ifPn => //= B0.
        by left; exists r.
      by exists r.
    by rewrite mem_set//=; tauto.
    by rewrite mem_set//=; tauto.
  move=> [r| |]//=; case: ifPn => B0 /=.
  case; last first.
    by case.
  by move=> [r' Br' [<-]].
  by move=> [r' Br' [<-]].
  by rewrite inE in B0.
  by case => //.
  case=> //.
  by case=> //.
  by rewrite inE in B0.
  by case=> //.
case: ifPn => B0.
  apply: measurableU.
    by apply: measurable_EFin.
  by apply: measurableU.
by apply: measurable_EFin.
Qed.

Section normalize_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : R.-ker T ~> T').

Definition normalize_kernel (P : probability T' R) :=
  fun t => [the measure _ _ of normalize f P t].

Variable P : probability T' R.

Lemma measurable_fun_normalize U : measurable U -> measurable_fun setT (normalize_kernel P ^~ U).
Proof.
move=> mU.
rewrite /normalize_kernel/= /normalize /=.
apply: measurable_fun_if000 => //.
- exact: measurable_fun_eq_cst.
- exact: measurable_fun_cst.
- apply: measurable_fun_if000 => //.
  + rewrite setTI.
    exact: measurable_neq_cst.
  + exact: measurable_fun_eq_cst.
  + exact: measurable_fun_cst.
  + apply: emeasurable_funM.
      have := (measurable_kernel f U mU).
      by apply: measurable_funS  => //.
    apply/EFin_measurable_fun.
    rewrite /=.
    apply: (measurable_fun_comp_new (F := [set r : R | r != 0%R])) => //.
      exact: open_measurable.
      move=> /= r [t] [] [_ H1] H2 H3.
      apply/eqP => H4; subst r.
      move/eqP : H4.
      rewrite fine_eq0 ?(negbTE H1)//.
      rewrite ge0_fin_numE//.
      by rewrite lt_neqAle leey H2.
    apply: open_continuous_measurable_fun => //.
    apply/in_setP => x /= x0.
    by apply: inv_continuous.
  apply: measurable_fun_comp => /=.
    exact: measurable_fun_fine.
  have := (measurable_kernel f setT measurableT).
  by apply: measurable_funS  => //.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R (normalize_kernel P)
  measurable_fun_normalize.

End normalize_kernel.

Section normalize_prob_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : R.-ker T ~> T') (P : probability T' R).

Lemma normalize_prob_kernelP x : normalize_kernel f P x [set: T'] = 1.
Proof.
rewrite /normalize_kernel/= /normalize.
case: ifPn => [_|fx0].
  by rewrite probability_setT.
case: ifPn => [_|fxoo].
  by rewrite probability_setT.
have ? : f x [set: _] \is a fin_num.
  by rewrite ge0_fin_numE// lt_neqAle fxoo/= leey.
rewrite -{1}(@fineK _ (f x setT))//=.
by rewrite -EFinM divrr// ?lte_fin ?ltr1n// ?unitfE fine_eq0.
Qed.

HB.instance Definition _ :=
  @isProbabilityKernel.Build _ _ _ _ _ (normalize_kernel f P)
  normalize_prob_kernelP.

End normalize_prob_kernel.
