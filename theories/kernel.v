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
(*     R.-fker X ~> Y == finite kernel                                        *)
(*    R.-sfker X ~> Y == s-finite kernel                                      *)
(*     sum_of_kernels ==                                                      *)
(*             l \; k == composition of kernels                               *)
(*        kernel_mfun == kernel defined by a measurable function              *)
(*             mscore ==                                                      *)
(* ite_true/ite_false ==                                                      *)
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
Admitted.

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

Lemma measurable_fun_if (d d' : _) (T : measurableType d) (T' : measurableType d') (x y : T -> T') :
  measurable_fun setT x ->
  measurable_fun setT y ->
  measurable_fun setT (fun b : T * bool => if b.2 then x b.1 else y b.1).
Proof.
move=> mx my /= _ Y mY.
rewrite setTI.
have := mx measurableT Y mY.
rewrite setTI => xY.
have := my measurableT Y mY.
rewrite setTI => yY.
rewrite (_ : _ @^-1` Y = (x @^-1` Y) `*` [set true] `|` (y @^-1` Y) `*` [set false]); last first.
  apply/seteqP; split.
    move=> [t [|]]/=.
      by left.
    by right.
  move=> [t [|]]/=.
    by case=> [[]//|[]].
  by case=> [[]//|[]].
by apply: measurableU; apply: measurableM => //.
Qed.

(*/ PR*)

Reserved Notation "R .-ker X ~> Y" (at level 42).
Reserved Notation "R .-fker X ~> Y" (at level 42).
Reserved Notation "R .-sfker X ~> Y" (at level 42).

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

(* TODO: define using the probability type *)
HB.mixin Record isProbabilityKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R})
    of isKernel _ _ X Y R k := {
  prob_kernelP : forall x, k x [set: Y] = 1
}.

#[short(type=probability_kernel)]
HB.structure Definition ProbabilityKernel
    (d d' : _) (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of isProbabilityKernel _ _ X Y R k & isKernel _ _ X Y R k}.

Section measure_uub.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : numFieldType) (k : X -> {measure set Y -> \bar R}).

Definition measure_uub := exists r, forall x, k x [set: Y] < r%:E.

Lemma measure_uubP : measure_uub <->
  exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E.
Proof.
split => [|] [r kr]; last by exists r%:num.
suff r_gt0 : (0 < r)%R by exists (PosNum r_gt0).
by rewrite -lte_fin; apply: (le_lt_trans _ (kr point)).
Qed.

End measure_uub.

HB.mixin Record isFiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { kernel_uub : measure_uub k }.

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

Lemma kernel_from_mzero_uub : measure_uub kernel_from_mzero.
Proof.
exists 1%R => /= t.
by rewrite /mzero/=.
Qed.

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
Lemma measurable_fun_integral_finite_kernel
    (d d' : _) (X : measurableType d) (Y : measurableType d')
    (R : realType) (l : R.-fker X ~> Y) (k : (X * Y)%type -> \bar R)
    (k0 : (forall z, True -> 0 <= k z)) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk k0.
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
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \int[l x]_y
  (\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \sum_(r <- fset_set (range (k_ n)))
  (\int[l x]_y (r * \1_(k_ n @^-1` [set r]) (x, y))%:E))); last first.
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
rewrite (_ : (fun x => _) = (fun x => l x (xsection (k_ n @^-1` [set r]) x))); last first.
  apply/funext => y.
  rewrite integral_indic//; last first.
    rewrite (_ : (fun x => _) = xsection (k_ n @^-1` [set r]) y); last first.
      apply/seteqP; split.
        by move=> y2/=; rewrite /xsection/= inE//.
      by rewrite /xsection/= => y2/=; rewrite inE.
    exact: measurable_xsection.
  congr (l y _).
  apply/funext => y1/=.
  rewrite /xsection/= inE.
  by apply/propext; tauto.
have [l_ hl_] := kernel_uub l.
by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

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
move=> mU.
rewrite /kcomp.
apply: (@measurable_fun_integral_finite_kernel _ _ _ _ _ _ (k ^~ U)) => //=.
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

Lemma mkcomp_finite : measure_uub (l \; k).
Proof.
have /measure_uubP[r hr] := kernel_uub k.
have /measure_uubP[s hs] := kernel_uub l.
apply/measure_uubP; exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x.
rewrite /=.
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

(* pollard *)
Lemma measurable_fun_integral_sfinite_kernel
    (d d' : _) (X : measurableType d) (Y : measurableType d') (R : realType)
    (l : R.-sfker X ~> Y)
    (k : (X * Y)%type -> \bar R) (k0 : (forall t, True -> 0 <= k t))
    (mk : measurable_fun setT k) :
  measurable_fun [set: X] (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk k0.
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
  (\sum_(r <- fset_set (range (k_ n)))
     r * \1_(k_ n @^-1` [set r]) (x0, y))%:E)); last first.
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
rewrite (_ : (fun x => \int[l x]_z (\1_(k_ n @^-1` [set r]) (x, z))%:E) =
    (fun x => l x (xsection (k_ n @^-1` [set r]) x))); last first.
  apply/funext => y.
  rewrite integral_indic//; last first.
    rewrite (_ : (fun x => (k_ n @^-1` [set r]) (y, x)) = xsection (k_ n @^-1` [set r]) y); last first.
      apply/seteqP; split.
        by move=> y2/=; rewrite /xsection/= inE//.
      by rewrite /xsection/= => y2/=; rewrite inE /preimage/=.
    exact: measurable_xsection.
  congr (l y _).
  apply/funext => y1/=.
  rewrite /xsection/= inE.
  by apply/propext; tauto.
have [l_ hl_] := sfinite l.
rewrite (_ : (fun x => _) = (fun x => mseries (l_ ^~ x) 0 (xsection (k_ n @^-1` [set r]) x))); last first.
  apply/funext => x.
  rewrite hl_//.
  exact/measurable_xsection.
rewrite /mseries/=.
apply: ge0_emeasurable_fun_sum => // k1.
apply: measurable_fun_xsection_finite_kernel => //.
by rewrite inE.
Qed.

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

Lemma measurable_fun_mkcomp_sfinite U : measurable U -> measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU.
apply: (@measurable_fun_integral_sfinite_kernel _ _ _ _ _ _ (k ^~ U)) => //.
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

(* pollard *)
Lemma measurable_fun_integral_sfinite_kernel_prod
    (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType)
    (l : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z) c
    (k : Z -> \bar R) (k0 : (forall z, True -> 0 <= k z)) (mk : measurable_fun setT k) :
  measurable_fun [set: Y] (fun y => \int[l (c, y)]_z k z).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk k0.
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
  apply: measurable_fun_integral_sfinite_kernel_prod => //.
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

(* semantics for a sample operation *)
Section kernel_probability.
Variables (d : _) (R : realType) (X : measurableType d).
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
  @isKernel.Build _ _ _ X R kernel_probability
  kernel_probabilityP.

Lemma kernel_probability_uub : measure_uub kernel_probability.
Proof.
(*NB: shouldn't this work? exists 2%:pos. *)
exists 2%R => /= ?.
rewrite (le_lt_trans (probability_le1 m measurableT))//.
by rewrite lte_fin ltr_addr.
Qed.

HB.instance Definition _ :=
  @isFiniteKernel.Build _ _ _ X R kernel_probability
  kernel_probability_uub.

Lemma sfinite_kernel_probability : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    kernel_probability x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof. exact: sfinite_finite. Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ _ _ X R kernel_probability
  sfinite_kernel_probability.

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

Lemma kernel_mfun_uub : measure_uub (kernel_mfun mf).
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

(* semantics for score *)
Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/seteqP; split => [|] [].
Qed.

Section score_measure.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R) (mr : measurable_fun setT r).

Definition mscore (t : T) (U : set unit) : \bar R :=
  if U == set0 then 0 else `| (r t)%:E |.

Lemma mscore0 t : mscore t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /mscore eqxx. Qed.

Lemma mscore_ge0 t U : 0 <= mscore t U.
Proof. by rewrite /mscore; case: ifP. Qed.

Lemma mscore_sigma_additive t : semi_sigma_additive (mscore t).
Proof.
move=> /= F mF tF mUF; rewrite /mscore; case: ifPn => [/eqP/bigcup0P F0|].
  rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
  apply/funext => k.
  under eq_bigr do rewrite F0// eqxx.
  by rewrite big1.
move=> /eqP/bigcup0P/existsNP[k /not_implyP[_ /eqP Fk0]].
rewrite -(cvg_shiftn k.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
rewrite (negbTE Fk0) big1 ?adde0// => i/= ik; rewrite ifT//.
have [/eqP//|Fitt] := set_unit (F i).
move/trivIsetP : tF => /(_ i k Logic.I Logic.I ik).
by rewrite Fitt setTI => /eqP; rewrite (negbTE Fk0).
Qed.

HB.instance Definition _ (t : T) := isMeasure.Build _ _ _
  (mscore t) (mscore0 t) (mscore_ge0 t) (@mscore_sigma_additive t).

End score_measure.

Module KERNEL_SCORE.
Section kernel_score.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition k_' (mr : measurable_fun setT r) (i : nat) : T -> set unit -> \bar R :=
  fun t U =>
    if i%:R%:E <= mscore r t U < i.+1%:R%:E then
      mscore r t U
    else
      0.

Variable (mr : measurable_fun setT r).

Lemma k_'0 i (t : T) : k_' mr i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k_' measure0; case: ifP. Qed.

Lemma k_'ge0 i (t : T) B : 0 <= k_' mr i t B.
Proof. by rewrite /k_'; case: ifP. Qed.

Lemma k_'sigma_additive i (t : T) : semi_sigma_additive (k_' mr i t).
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
  rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
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

HB.instance Definition _ (i : nat) (t : T) := isMeasure.Build _ _ _
  (k_' mr i t) (k_'0 i t) (k_'ge0 i t) (@k_'sigma_additive i t).

Lemma emeasurable_itv (i : nat) :
  measurable (`[(i%:R)%:E, (i.+1%:R)%:E[%classic : set \bar R).
Proof.
rewrite -[X in measurable X]setCK.
apply: measurableC.
rewrite set_interval.setCitv /=.
apply: measurableU.
exact: emeasurable_itv_ninfty_bnd.
exact: emeasurable_itv_bnd_pinfty.
Qed.

Lemma k_kernelP (i : nat) : forall U, measurable U -> measurable_fun setT (k_' mr i ^~ U).
Proof.
move=> /= U mU.
rewrite /k_' /=.
rewrite (_ : (fun x : T => _) = (fun x => if (i%:R)%:E <= x < (i.+1%:R)%:E then x else 0) \o (fun x => mscore r x U)) //.
apply: measurable_fun_comp; last first.
  rewrite /mscore.
  have [U0|U0] := eqVneq U set0.
    exact: measurable_fun_cst.
  apply: measurable_fun_comp => //.
  by apply/EFin_measurable_fun.
rewrite /=.
pose A : _ -> \bar R := (fun x : \bar R => x * (\1_(`[i%:R%:E, i.+1%:R%:E [%classic : set (\bar R)) x)%:E).
rewrite (_ : (fun x => _) = A); last first.
  apply/funext => x; rewrite /A; case: ifPn => ix.
    by rewrite indicE/= mem_set ?mule1//.
  rewrite indicE/= memNset ?mule0//.
  rewrite /= in_itv/=.
  exact/negP.
rewrite /A.
apply emeasurable_funM => /=.
  exact: measurable_fun_id.
apply/EFin_measurable_fun.
have mi : measurable (`[(i%:R)%:E, (i.+1%:R)%:E[%classic : set (\bar R)).
  exact: emeasurable_itv.
by rewrite (_ : \1__ = mindic R mi)//.
Qed.

Definition mk_' i (t : T) := [the measure _ _ of k_' mr i t].

HB.instance Definition _ (i : nat) :=
  isKernel.Build _ _ _ _ R (mk_' i) (k_kernelP i).

Lemma k_uub (i : nat) : measure_uub (mk_' i).
Proof.
exists i.+1%:R => /= t.
rewrite /k_' /mscore setT_unit.
rewrite (_ : [set tt] == set0 = false); last first.
  by apply/eqP => /seteqP[] /(_ tt) /(_ erefl).
by case: ifPn => // /andP[].
Qed.

HB.instance Definition _ (i : nat) :=
  @isFiniteKernel.Build _ _ _ _ R (mk_' i) (k_uub i).

End kernel_score.
End KERNEL_SCORE.

Section kernel_score_kernel.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition kernel_score (mr : measurable_fun setT r) : T -> {measure set Datatypes_unit__canonical__measure_Measurable -> \bar R} :=
  fun t : T => [the measure _ _ of mscore r t].

Variable (mr : measurable_fun setT r).

Lemma kernel_scoreP : forall U, measurable U ->
  measurable_fun setT (kernel_score mr ^~ U).
Proof.
move=> /= U mU.
rewrite /mscore.
have [U0|U0] := eqVneq U set0.
  exact: measurable_fun_cst.
apply: measurable_fun_comp => //.
by apply/EFin_measurable_fun.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ T
    _ (*Datatypes_unit__canonical__measure_Measurable*) R
    (kernel_score mr) (kernel_scoreP).
End kernel_score_kernel.

Section kernel_score_sfinite_kernel.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R) (mr : measurable_fun setT r).

Import KERNEL_SCORE.

Lemma kernel_score_sfinite_kernelP : exists k_ : (R.-fker T ~> _)^nat,
   forall x U, measurable U ->
     kernel_score mr x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
rewrite /=.
exists (fun i => [the finite_kernel _ _ _ of mk_' mr i]) => /= r' U mU.
rewrite /mseries /mscore; case: ifPn => [/eqP U0|U0].
  by apply/esym/nneseries0 => i _; rewrite U0 measure0.
rewrite /mk_' /= /k_' /= /mscore (negbTE U0).
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn `|floor (fine `|(r r')%:E|)|%N.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(r r')%:E|); first exact: cvg_cst.
apply/funext => n.
pose floor_r := widen_ord (leq_addl n `|floor `|(r r')| |.+1) (Ordinal (ltnSn `|floor `|(r r')| |)).
rewrite big_mkord (bigD1 floor_r)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|(r r')|)) ?floor_ge0 ?floor_le.
  by rewrite -addn1 natrD natr_absz (@ger0_norm _ (floor `|(r r')|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|(r r')|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|(r r')|)) ?floor_ge0.
- suff : (`|(r r')| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|(r r')|)) ?floor_ge0// ltr_int.
  by rewrite -floor_lt_int.
Qed.

HB.instance Definition _ := @isSFiniteKernel.Build _ _ _ _ _
  (kernel_score mr) (kernel_score_sfinite_kernelP).

End kernel_score_sfinite_kernel.

Section ite_true_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u1 : R.-ker T ~> T').

Definition ite_true : T * bool -> {measure set T' -> \bar R} :=
  fun b => if b.2 then u1 b.1 else [the measure _ _ of mzero].

Lemma measurable_ite_true U : measurable U -> measurable_fun setT (ite_true ^~ U).
Proof.
move=> /= mcU.
rewrite /ite_true.
rewrite (_ : (fun x : T * bool => _) = (fun x => if x.2 then u1 x.1 U else [the {measure set T' -> \bar R} of mzero] U)); last first.
  apply/funext => -[t b]/=.
  by case: ifPn.
apply: (@measurable_fun_if _ _ _ _ (u1 ^~ U) (fun=> mzero U)).
  exact/measurable_kernel.
exact: measurable_fun_cst.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R ite_true measurable_ite_true.
End ite_true_kernel.

Section ite_true_finite_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u1 : R.-fker T ~> T').

Lemma ite_true_uub : measure_uub (ite_true u1).
Proof.
have /measure_uubP[M hM] := kernel_uub u1.
exists M%:num => /= -[]; rewrite /ite_true => t [|]/=.
  exact: hM.
by rewrite /= /mzero.
Qed.

HB.instance Definition _ t :=
  isFiniteKernel.Build _ _ _ _ R (ite_true u1) ite_true_uub.
End ite_true_finite_kernel.

Section ite_true_sfinite_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u1 : R.-sfker T ~> T').

Lemma sfinite_ite_true : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    ite_true u1 x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k hk /=] := sfinite u1.
rewrite /ite_true.
exists (fun n => [the finite_kernel _ _ _ of ite_true (k n)]) => b U mU.
case: ifPn => hb.
  rewrite /mseries hk//= /mseries.
  apply: eq_nneseries => n _.
  by rewrite /ite_true hb.
rewrite /= /mseries nneseries0// => n _.
by rewrite /ite_true (negbTE hb).
Qed.

HB.instance Definition _ t :=
  @isSFiniteKernel.Build _ _ _ _ _ (ite_true u1) sfinite_ite_true.

End ite_true_sfinite_kernel.

Section ite_false_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u2 : R.-ker T ~> T').

Definition ite_false : T * bool -> {measure set T' -> \bar R} :=
  fun b => if ~~ b.2 then u2 b.1 else [the measure _ _ of mzero].

Lemma measurable_ite_false U : measurable U -> measurable_fun setT (ite_false ^~ U).
Proof.
move=> /= mcU.
rewrite /ite_false.
rewrite (_ : (fun x => _) = (fun x => if x.2 then [the {measure set T' -> \bar R} of mzero] U else u2 x.1 U)); last first.
  apply/funext => -[t b]/=.
  rewrite if_neg/=.
  by case: b.
apply: (@measurable_fun_if _ _ _ _ (fun=> mzero U) (u2 ^~ U)).
  exact: measurable_fun_cst.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R ite_false measurable_ite_false.

End ite_false_kernel.

Section ite_false_finite_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u2 : R.-fker T ~> T').

Lemma ite_false_uub : measure_uub (ite_false u2).
Proof.
have /measure_uubP[M hM] := kernel_uub u2.
exists M%:num => /= -[]; rewrite /ite_false/= => t b.
case: b => //=.
by rewrite /mzero.
Qed.

HB.instance Definition _ :=
  isFiniteKernel.Build _ _ _ _ R (ite_false u2) ite_false_uub.

End ite_false_finite_kernel.

Section ite_false_sfinite_kernel.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (u2 : R.-sfker T ~> T').

Lemma sfinite_ite_false : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    ite_false u2 x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k hk] := sfinite u2.
rewrite /= /ite_false.
exists (fun n => [the finite_kernel _ _ _ of ite_false (k n)]) => b U mU.
case: ifPn => hb.
  rewrite /mseries hk//= /mseries/=.
  apply: eq_nneseries => // n _.
  by rewrite /ite_false hb.
rewrite /= /mseries nneseries0// => n _.
rewrite negbK in hb.
by rewrite /ite_false hb/=.
Qed.

HB.instance Definition _ :=
  @isSFiniteKernel.Build _ _ _ _ _ (ite_false u2) sfinite_ite_false.

End ite_false_sfinite_kernel.

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

Lemma add_of_finite_kernels_uub : measure_uub (add_of_kernels u1 u2).
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
