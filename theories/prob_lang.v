(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import reals ereal signed topology normedtype sequences esum measure.
Require Import lebesgue_measure  numfun lebesgue_integral exp kernel.

(******************************************************************************)
(*  Semantics of a probabilistic programming language using s-finite kernels  *)
(*                                                                            *)
(*       bernoulli r1 == Bernoulli probability with r1 a proof that           *)
(*                       r : {nonneg R} is smaller than 1                     *)
(* uniform_probability a b ab0 == uniform probability over the interval [a,b] *)
(*          sample mP == sample according to the probability P where mP is a  *)
(*                       proof that P is a measurable function                *)
(*          letin l k == execute l, augment the context, and execute k        *)
(*             ret mf == access the context with f and return the result      *)
(*           score mf == observe t from d, where f is the density of d and    *)
(*                       t occurs in f                                        *)
(*                       e.g., score (r e^(-r * t)) = observe t from exp(r)   *)
(*      normalize k P == normalize the kernel k into a probability kernel,    *)
(*                       P is a default probability in case normalization is  *)
(*                       not possible                                         *)
(*       ite mf k1 k2 == access the context with the boolean function f and   *)
(*                       behaves as k1 or k2 according to the result          *)
(*                                                                            *)
(*            poisson == Poisson distribution function                        *)
(*        exp_density == density function for exponential distribution        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO: PR *)
Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) :
  (p%:num <= 1 -> 0 <= `1-(p%:num))%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R})
   (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).
(* /TODO: PR *)

Lemma invr_nonneg_proof (R : numDomainType) (p : {nonneg R}) :
  (0 <= (p%:num)^-1)%R.
Proof. by rewrite invr_ge0. Qed.

Definition invr_nonneg (R : numDomainType) (p : {nonneg R}) :=
  NngNum (invr_nonneg_proof p).

(* TODO: move *)
Lemma eq_probability R d (Y : measurableType d) (m1 m2 : probability Y R) :
  (m1 =1 m2 :> (set Y -> \bar R)) -> m1 = m2.
Proof.
move: m1 m2 => [m1 +] [m2 +] /= m1m2.
move/funext : m1m2 => <- -[[c11 c12] [m01] [sf1] [sig1] [fin1] [sub1] [p1]]
                    [[c21 c22] [m02] [sf2] [sig2] [fin2] [sub2] [p2]].
have ? : c11 = c21 by [].
subst c21.
have ? : c12 = c22 by [].
subst c22.
have ? : m01 = m02 by [].
subst m02.
have ? : sf1 = sf2 by [].
subst sf2.
have ? : sig1 = sig2 by [].
subst sig2.
have ? : fin1 = fin2 by [].
subst fin2.
have ? : sub1 = sub2 by [].
subst sub2.
have ? : p1 = p2 by [].
subst p2.
by f_equal.
Qed.

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition bernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac true]]
    [the measure _ _ of mscale (onem_nonneg p1) [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli.

Local Close Scope ring_scope.

Let bernoulli_setT : bernoulli [set: _] = 1.
Proof.
rewrite /bernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracT !mule1 -EFinD add_onemK.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

End bernoulli.

Lemma integral_bernoulli {R : realType}
    (p : {nonneg R}) (p1 : (p%:num <= 1)%R) (f : bool -> set bool -> _) U :
  (forall x y, 0 <= f x y) ->
  \int[bernoulli p1]_y (f y ) U =
  p%:num%:E * f true U + (`1-(p%:num))%:E * f false U.
Proof.
move=> f0.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section uniform_probability.
Context {R : realType}.
Variables (a b : R) (ab0 : (0 < b - a)%R).

Definition uniform_probability := mscale (invr_nonneg (NngNum (ltW ab0)))
  (mrestr lebesgue_measure (measurable_itv `[a, b])).

HB.instance Definition _ := Measure.on uniform_probability.

Let uniform_probability_setT : uniform_probability [set: _] = 1.
Proof.
rewrite /uniform_probability /mscale/= /mrestr/=.
rewrite setTI lebesgue_measure_itv hlength_itv/= lte_fin.
by rewrite -subr_gt0 ab0 -EFinD -EFinM mulVf// gt_eqF// subr_gt0.
Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R
  uniform_probability uniform_probability_setT.

End uniform_probability.

Section mscore.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition mscore t : {measure set _ -> \bar R} :=
  let p := NngNum (normr_ge0 (f t)) in
  [the measure _ _ of mscale p [the measure _ _ of dirac tt]].

Lemma mscoreE t U : mscore t U = if U == set0 then 0 else `| (f t)%:E |.
Proof.
rewrite /mscore/= /mscale/=; have [->|->] := set_unit U.
  by rewrite eqxx dirac0 mule0.
by rewrite diracT mule1 (negbTE setT0).
Qed.

Lemma measurable_fun_mscore U : measurable_fun setT f ->
  measurable_fun setT (mscore ^~ U).
Proof.
move=> mr; under eq_fun do rewrite mscoreE/=.
have [U0|U0] := eqVneq U set0; first exact: measurable_cst.
by apply: measurableT_comp => //; exact: measurableT_comp.
Qed.

End mscore.

(* decomposition of score into finite kernels *)
Module SCORE.
Section score.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition k (mf : measurable_fun setT f) i t U :=
    if i%:R%:E <= mscore f t U < i.+1%:R%:E then
      mscore f t U
    else
      0.

Hypothesis mf : measurable_fun setT f.

Lemma k0 i t : k mf i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k measure0; case: ifP. Qed.

Lemma k_ge0 i t B : 0 <= k mf i t B.
Proof. by rewrite /k; case: ifP. Qed.

Lemma k_sigma_additive i t : semi_sigma_additive (k mf i t).
Proof.
move=> /= F mF tF mUF; rewrite /k /=.
have [F0|UF0] := eqVneq (\bigcup_n F n) set0.
  rewrite F0 measure0 (_ : (fun _ => _) = cst 0).
    by case: ifPn => _; exact: cvg_cst.
  apply/funext => k; rewrite big1// => n _.
  by move: F0 => /bigcup0P -> //; rewrite measure0; case: ifPn.
move: (UF0) => /eqP/bigcup0P/existsNP[m /not_implyP[_ /eqP Fm0]].
rewrite [in X in _ --> X]mscoreE (negbTE UF0).
rewrite -(cvg_shiftn m.+1)/=.
case: ifPn => ir.
  rewrite (_ : (fun _ => _) = cst `|(f t)%:E|); first exact: cvg_cst.
  apply/funext => n.
  rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn m))))//=.
  rewrite [in X in X + _]mscoreE (negbTE Fm0) ir big1 ?adde0// => /= j jk.
  rewrite mscoreE; have /eqP -> : F j == set0.
    have [/eqP//|Fjtt] := set_unit (F j).
    move/trivIsetP : tF => /(_ j m Logic.I Logic.I jk).
    by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fm0).
  by rewrite eqxx; case: ifP.
rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn m))))//=.
rewrite [in X in if X then _ else _]mscoreE (negbTE Fm0) (negbTE ir) add0e.
rewrite big1//= => j jm; rewrite mscoreE; have /eqP -> : F j == set0.
  have [/eqP//|Fjtt] := set_unit (F j).
  move/trivIsetP : tF => /(_ j m Logic.I Logic.I jm).
  by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fm0).
by rewrite eqxx; case: ifP.
Qed.

HB.instance Definition _ i t := isMeasure.Build _ _ _
  (k mf i t) (k0 i t) (k_ge0 i t) (@k_sigma_additive i t).

Lemma measurable_fun_k i U : measurable U -> measurable_fun setT (k mf i ^~ U).
Proof.
move=> /= mU; rewrite /k /= (_ : (fun x => _) =
  (fun x => if i%:R%:E <= x < i.+1%:R%:E then x else 0) \o (mscore f ^~ U)) //.
apply: measurableT_comp => /=; last exact/measurable_fun_mscore.
rewrite (_ : (fun x => _) = (fun x => x *
    (\1_(`[i%:R%:E, i.+1%:R%:E [%classic : set _) x)%:E)); last first.
  apply/funext => x; case: ifPn => ix; first by rewrite indicE/= mem_set ?mule1.
  by rewrite indicE/= memNset ?mule0// /= in_itv/=; exact/negP.
apply: emeasurable_funM => //=; apply/EFin_measurable_fun.
by rewrite (_ : \1__ = mindic R (emeasurable_itv `[(i%:R)%:E, (i.+1%:R)%:E[)).
Qed.

Definition mk i t := [the measure _ _ of k mf i t].

HB.instance Definition _ i :=
  isKernel.Build _ _ _ _ _ (mk i) (measurable_fun_k i).

Lemma mk_uub i : measure_fam_uub (mk i).
Proof.
exists i.+1%:R => /= t; rewrite /k mscoreE setT_unit.
by case: ifPn => //; case: ifPn => // _ /andP[].
Qed.

HB.instance Definition _ i :=
  Kernel_isFinite.Build _ _ _ _ _ (mk i) (mk_uub i).

End score.
End SCORE.

Section kscore.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition kscore (mf : measurable_fun setT f)
    : T -> {measure set _ -> \bar R} :=
  mscore f.

Variable mf : measurable_fun setT f.

Let measurable_fun_kscore U : measurable U ->
  measurable_fun setT (kscore mf ^~ U).
Proof. by move=> /= _; exact: measurable_fun_mscore. Qed.

HB.instance Definition _ := isKernel.Build _ _ T _ R
  (kscore mf) measurable_fun_kscore.

Import SCORE.

Let sfinite_kscore : exists k : (R.-fker T ~> _)^nat,
  forall x U, measurable U ->
    kscore mf x U = mseries (k ^~ x) 0 U.
Proof.
rewrite /=; exists (fun i => [the R.-fker _ ~> _ of mk mf i]) => /= t U mU.
rewrite /mseries /kscore/= mscoreE; case: ifPn => [/eqP U0|U0].
  by apply/esym/eseries0 => i _; rewrite U0 measure0.
rewrite /mk /= /k /= mscoreE (negbTE U0).
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn `|floor (fine `|(f t)%:E|)|%N.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(f t)%:E|); first exact: cvg_cst.
apply/funext => n.
pose floor_f := widen_ord (leq_addl n `|floor `|f t| |.+1)
                          (Ordinal (ltnSn `|floor `|f t| |)).
rewrite big_mkord (bigD1 floor_f)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|f t|)) ?floor_ge0 ?floor_le.
  rewrite -addn1 natrD natr_absz.
  by rewrite (@ger0_norm _ (floor `|f t|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|f t|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|f t|)) ?floor_ge0.
- suff : (`|f t| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|f t|)) ?floor_ge0//.
  by rewrite ltr_int -floor_lt_int.
Qed.

HB.instance Definition _ :=
  @Kernel_isSFinite.Build _ _ _ _ _ (kscore mf) sfinite_kscore.

End kscore.

(* decomposition of ite into s-finite kernels *)
Module ITE.
Section ite.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Section kiteT.
Variable k : R.-ker X ~> Y.

Definition kiteT : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteT U : measurable U -> measurable_fun setT (kiteT ^~ U).
Proof.
move=> /= mcU; rewrite /kiteT.
rewrite (_ : (fun _ => _) =
    (fun x => if x.2 then k x.1 U else mzero U)); last first.
  by apply/funext => -[t b]/=; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (k ^~ U) (fun=> mzero U)) => //.
exact/measurable_kernel.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  kiteT measurable_fun_kiteT.
End kiteT.

Section sfkiteT.
Variable k : R.-sfker X ~> Y.

Let sfinite_kiteT : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kiteT k x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of kiteT (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteT//= /mzero//.
move=> [x b] U mU; rewrite /kiteT; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries eseries0.
Qed.

#[export]
HB.instance Definition _ := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (kiteT k) sfinite_kiteT.
End sfkiteT.

Section fkiteT.
Variable k : R.-fker X ~> Y.

Let kiteT_uub : measure_fam_uub (kiteT k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
exists M%:num => /= -[]; rewrite /kiteT => t [|]/=; first exact: hM.
by rewrite /= /mzero.
Qed.

#[export]
HB.instance Definition _ := Kernel_isFinite.Build _ _ _ _ _
  (kiteT k) kiteT_uub.
End fkiteT.

Section kiteF.
Variable k : R.-ker X ~> Y.

Definition kiteF : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if ~~ xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteF U : measurable U -> measurable_fun setT (kiteF ^~ U).
Proof.
move=> /= mcU; rewrite /kiteF.
rewrite (_ : (fun x => _) =
    (fun x => if x.2 then mzero U else k x.1 U)); last first.
  by apply/funext => -[t b]/=; rewrite if_neg//; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (fun=> mzero U) (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  kiteF measurable_fun_kiteF.

End kiteF.

Section sfkiteF.
Variable k : R.-sfker X ~> Y.

Let sfinite_kiteF : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kiteF k x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of kiteF (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteF//= /mzero//.
move=> [x b] U mU; rewrite /kiteF; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries eseries0.
Qed.

#[export]
HB.instance Definition _ := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (kiteF k) sfinite_kiteF.

End sfkiteF.

Section fkiteF.
Variable k : R.-fker X ~> Y.

Let kiteF_uub : measure_fam_uub (kiteF k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
by exists M%:num => /= -[]; rewrite /kiteF/= => t; case => //=; rewrite /mzero.
Qed.

#[export]
HB.instance Definition _ := Kernel_isFinite.Build _ _ _ _ _
  (kiteF k) kiteF_uub.

End fkiteF.
End ite.
End ITE.

Section ite.
Context d d' (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

(* NB: not used? *)
Definition mite (mf : measurable_fun setT f) : T -> set T' -> \bar R :=
  fun t => if f t then u1 t else u2 t.

Variables mf : measurable_fun setT f.

Let mite0 t : mite mf t set0 = 0.
Proof. by rewrite /mite; case: ifPn. Qed.

Let mite_ge0 t U : 0 <= mite mf t U.
Proof. by rewrite /mite; case: ifPn. Qed.

Let mite_sigma_additive t : semi_sigma_additive (mite mf t).
Proof.
by rewrite /mite; case: ifPn => ft; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ t := isMeasure.Build _ _ _ (mite mf t)
  (mite0 t) (mite_ge0 t) (@mite_sigma_additive t).

Import ITE.

(*
Definition kite : R.-sfker T ~> T' :=
  kdirac mf \; kadd (kiteT u1) (kiteF u2).
*)
Definition kite :=
  [the R.-sfker _ ~> _ of kdirac mf] \;
  [the R.-sfker _ ~> _ of kadd
    [the R.-sfker _ ~> T' of kiteT u1]
    [the R.-sfker _ ~> T' of kiteF u2] ].

End ite.

Section insn2.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition ret (f : X -> Y) (mf : measurable_fun setT f)
  : R.-pker X ~> Y := [the R.-pker _ ~> _ of kdirac mf].

Definition sample (P : X -> pprobability Y R) (mP : measurable_fun setT P)
    : R.-pker X ~> Y :=
  [the R.-pker _ ~> _ of kprobability mP].

Definition sample_cst (P : pprobability Y R) : R.-pker X ~> Y :=
  sample (measurable_cst P).

Definition normalize (k : R.-ker X ~> Y) P : X -> probability Y R :=
  knormalize k P.

Definition normalize_pt (k : R.-ker X ~> Y) : X -> probability Y R :=
  normalize k point.

Lemma measurable_normalize_pt (f : R.-ker X ~> Y) :
  measurable_fun [set: X] (normalize_pt f : X -> pprobability Y R).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability Y R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-.
apply: emeasurable_fun_infty_o => //.
exact: (measurable_kernel (knormalize f point) Ys).
Qed.

Definition ite (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y) : R.-sfker X ~> Y :=
  locked [the R.-sfker X ~> Y of kite k1 k2 mf].

End insn2.
Arguments ret {d d' X Y R f} mf.
Arguments sample_cst {d d' X Y R}.
Arguments sample {d d' X Y R}.

Section insn2_lemmas.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Lemma retE (f : X -> Y) (mf : measurable_fun setT f) x :
  ret mf x = \d_(f x) :> (_ -> \bar R).
Proof. by []. Qed.

Lemma sample_cstE (P : probability Y R) (x : X) : sample_cst P x = P.
Proof. by []. Qed.

Lemma sampleE (P : X -> pprobability Y R) (mP : measurable_fun setT P) (x : X) : sample P mP x = P x.
Proof. by []. Qed.

Lemma normalizeE (f : R.-sfker X ~> Y) P x U :
  normalize f P x U =
  if (f x [set: Y] == 0) || (f x [set: Y] == +oo) then P U
  else f x U * ((fine (f x [set: Y]))^-1)%:E.
Proof. by rewrite /normalize /= /mnormalize; case: ifPn. Qed.

Lemma iteE (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y) x :
  ite mf k1 k2 x = if f x then k1 x else k2 x.
Proof.
apply/eq_measure/funext => U.
rewrite /ite; unlock => /=.
rewrite /kcomp/= integral_dirac//=.
rewrite indicT mul1e.
rewrite -/(measure_add (ITE.kiteT k1 (x, f x)) (ITE.kiteF k2 (x, f x))).
rewrite measure_addE.
rewrite /ITE.kiteT /ITE.kiteF/=.
by case: ifPn => fx /=; rewrite /mzero ?(adde0,add0e).
Qed.

End insn2_lemmas.

Lemma normalize_kdirac (R : realType)
    d (T : measurableType d) d' (T' : measurableType d') (x : T) (r : T') P :
  normalize (kdirac (measurable_cst r)) P x = \d_r :> probability T' R.
Proof.
apply: eq_probability => U.
rewrite normalizeE /= diracE in_setT/=.
by rewrite onee_eq0/= indicE in_setT/= -div1r divr1 mule1.
Qed.

Section insn3.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Definition letin (l : R.-sfker X ~> Y) (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
   : R.-sfker X ~> Z :=
  [the R.-sfker X ~> Z of l \; k].

End insn3.

Section insn3_lemmas.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Lemma letinE (l : R.-sfker X ~> Y) (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z) x U :
  letin l k x U = \int[l x]_y k (x, y) U.
Proof. by []. Qed.

End insn3_lemmas.

(* rewriting laws *)
Section letin_return.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Lemma letin_kret (k : R.-sfker X ~> Y)
  (f : X * Y -> Z) (mf : measurable_fun setT f) x U :
  measurable U ->
  letin k (ret mf) x U = k x (curry f x @^-1` U).
Proof.
move=> mU; rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT// -[X in measurable X]setTI.
exact: (measurableT_comp mf).
Qed.

Lemma letin_retk
  (f : X -> Y) (mf : measurable_fun setT f)
  (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
  x U : measurable U ->
  letin (ret mf) k x U = k (x, f x) U.
Proof.
move=> mU; rewrite letinE retE integral_dirac ?indicT ?mul1e//.
exact: (measurableT_comp (measurable_kernel k _ mU)).
Qed.

End letin_return.

Section insn1.
Context d (X : measurableType d) (R : realType).

Definition score (f : X -> R) (mf : measurable_fun setT f)
    : R.-sfker X ~> _ :=
  [the R.-sfker X ~> _ of kscore mf].

End insn1.

Section hard_constraint.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition fail :=
  letin (score (@measurable_cst _ _ X _ setT (0%R : R)))
        (ret (@measurable_cst _ _ _ Y setT point)).

Lemma failE x U : fail x U = 0.
Proof. by rewrite /fail letinE ge0_integral_mscale//= normr0 mul0e. Qed.

End hard_constraint.
Arguments fail {d d' X Y R}.

Module Notations.

(*Notation var1of2 := (@measurable_fst _ _ _ _).
Notation var2of2 := (@measurable_snd _ _ _ _).
Notation var1of3 := (measurableT_comp (@measurable_fst _ _ _ _)
                                         (@measurable_fst _ _ _ _)).
Notation var2of3 := (measurableT_comp (@measurable_snd _ _ _ _)
                                         (@measurable_fst _ _ _ _)).
Notation var3of3 := (@measurable_snd _ _ _ _).*)

Notation mR := Real_sort__canonical__measure_Measurable.
Notation munit := Datatypes_unit__canonical__measure_Measurable.
Notation mbool := Datatypes_bool__canonical__measure_Measurable.

End Notations.

Section cst_fun.
Context d (T : measurableType d) (R : realType).

Definition kr (r : R) := @measurable_cst _ _ T _ setT r.
Definition k3 : measurable_fun _ _ := kr 3%:R.
Definition k10 : measurable_fun _ _ := kr 10%:R.
Definition ktt := @measurable_cst _ _ T _ setT tt.
Definition kb (b : bool) := @measurable_cst _ _ T _ setT b.

End cst_fun.
Arguments kr {d T R}.
Arguments k3 {d T R}.
Arguments k10 {d T R}.
Arguments ktt {d T}.
Arguments kb {d T}.

Section iter_mprod.
Import Notations.

Fixpoint iter_mprod (l : list {d & measurableType d})
    : {d & measurableType d} :=
  match l with
  | [::] => existT measurableType _ munit
  | h :: t => let t' := iter_mprod t in
    existT _ _ [the measurableType (projT1 h, projT1 t').-prod of
                (projT2 h * projT2 t')%type]
  end.

End iter_mprod.

Section acc.
Import Notations.
Context {R : realType}.

Fixpoint acc (l : seq {d & measurableType d}) n :
  projT2 (iter_mprod l) -> projT2 (nth (existT _ _ munit) l n) :=
  match l return
     projT2 (iter_mprod l) -> projT2 (nth (existT _ _ munit) l n)
  with
  | [::] => match n with | O => id | m.+1 => id end
  | _ :: _ => match n with
               | O => fst
               | m.+1 => fun H => acc m H.2
               end
  end.

Lemma measurable_acc (l : seq {d & measurableType d}) n :
  measurable_fun setT (@acc l n).
Proof.
by elim: l n => //= h t ih [|m] //; exact: (measurableT_comp (ih _)).
Qed.
End acc.
Arguments acc : clear implicits.
Arguments measurable_acc : clear implicits.

Section rpair_pairA.
Context d0 d1 d2 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2).

Definition rpair d (T : measurableType d) t :
    ([the measurableType _ of T0] -> [the measurableType _ of T0 * T])%type :=
  fun x => (x, t).

Lemma mrpair d (T : measurableType d) t : measurable_fun setT (@rpair _ T t).
Proof. exact: measurable_fun_prod. Qed.

Definition pairA : ([the measurableType _ of T0 * T1 * T2] ->
                    [the measurableType _ of T0 * (T1 * T2)])%type :=
  fun x => (x.1.1, (x.1.2, x.2)).

Definition mpairA : measurable_fun setT pairA.
Proof.
apply: measurable_fun_prod => /=; first exact: measurableT_comp.
by apply: measurable_fun_prod => //=; exact: measurableT_comp.
Qed.

Definition pairAi : ([the measurableType _ of T0 * (T1 * T2)] ->
                    [the measurableType _ of T0 * T1 * T2])%type :=
  fun x => (x.1, x.2.1, x.2.2).

Definition mpairAi : measurable_fun setT pairAi.
Proof.
apply: measurable_fun_prod => //=; last exact: measurableT_comp.
apply: measurable_fun_prod => //=; exact: measurableT_comp.
Qed.

End rpair_pairA.
Arguments rpair {d0 T0 d} T.
#[global] Hint Extern 0 (measurable_fun _ (rpair _ _)) =>
  solve [apply: mrpair] : core.
Arguments pairA {d0 d1 d2 T0 T1 T2}.
#[global] Hint Extern 0 (measurable_fun _ pairA) =>
  solve [apply: mpairA] : core.
Arguments pairAi {d0 d1 d2 T0 T1 T2}.
#[global] Hint Extern 0 (measurable_fun _ pairAi) =>
  solve [apply: mpairAi] : core.

Section rpair_pairA_comp.
Import Notations.
Context d0 d1 d2 d3 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) (T3 : measurableType d3) (R : realType).

Definition pairAr d (T : measurableType d) t :
    ([the measurableType _ of T0 * T1] ->
     [the measurableType _ of T0 * (T1 * T)])%type :=
  pairA \o rpair T t.
Arguments pairAr {d} T.

Lemma mpairAr d (T : measurableType d) t : measurable_fun setT (pairAr T t).
Proof. exact: measurableT_comp. Qed.

Definition pairAAr : ([the measurableType _ of T0 * T1 * T2] ->
    [the measurableType _ of T0 * (T1 * (T2 * munit))])%type :=
  pairA \o pairA \o rpair munit tt.

Lemma mpairAAr : measurable_fun setT pairAAr.
Proof. by do 2 apply: measurableT_comp => //. Qed.

Definition pairAAAr : ([the measurableType _ of T0 * T1 * T2 * T3] ->
    [the measurableType _ of T0 * (T1 * (T2 * (T3 * munit)))])%type :=
  pairA \o pairA \o pairA \o rpair munit tt.

Lemma mpairAAAr : measurable_fun setT pairAAAr.
Proof. by do 3 apply: measurableT_comp => //. Qed.

Definition pairAArAi : ([the measurableType _ of T0 * (T1 * T2)] ->
    [the measurableType _ of T0 * (T1 * (T2 * munit))])%type :=
  pairAAr \o pairAi.

Lemma mpairAArAi : measurable_fun setT pairAArAi.
Proof. by apply: measurableT_comp => //=; exact: mpairAAr. Qed.

Definition pairAAArAAi : ([the measurableType _ of T3 * (T0 * (T1 * T2))] ->
    [the measurableType _ of T3 * (T0 * (T1 * (T2 * munit)))])%type :=
  pairA \o pairA \o pairA \o rpair munit tt \o pairAi \o pairAi.

Lemma mpairAAARAAAi : measurable_fun setT pairAAArAAi.
Proof. by do 5 apply: measurableT_comp => //=. Qed.

End rpair_pairA_comp.
Arguments pairAr {d0 d1 T0 T1 d} T.
Arguments pairAAr {d0 d1 d2 T0 T1 T2}.
Arguments pairAAAr {d0 d1 d2 d3 T0 T1 T2 T3}.
Arguments pairAArAi {d0 d1 d2 T0 T1 T2}.
Arguments pairAAArAAi {d0 d1 d2 d3 T0 T1 T2 T3}.

Section accessor_functions.
Import Notations.
Context d0 d1 d2 d3 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) (T3 : measurableType d3) (R : realType).

Definition Of2 := [:: existT _ _ T0; existT _ _ T1].

Definition acc0of2 : [the measurableType _ of (T0 * T1)%type] -> T0 :=
  @acc Of2 0 \o pairAr munit tt.

Lemma macc0of2 : measurable_fun setT acc0of2.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of2 0)|exact: mpairAr].
Qed.

Definition acc1of2 : [the measurableType _ of (T0 * T1)%type] -> T1 :=
  acc Of2 1 \o pairAr munit tt.

Lemma macc1of2 : measurable_fun setT acc1of2.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of2 1)|exact: mpairAr].
Qed.

Definition Of3 := [:: existT _ _ T0; existT _ _ T1; existT _ d2 T2].

Definition acc1of3 : [the measurableType _ of (T0 * T1 * T2)%type] -> T1 :=
  acc Of3 1 \o pairAAr.

Lemma macc1of3 : measurable_fun setT acc1of3.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of3 1)|exact: mpairAAr].
Qed.

Definition acc2of3 : [the measurableType _ of (T0 * T1 * T2)%type] -> T2 :=
  acc Of3 2 \o pairAAr.

Lemma macc2of3 : measurable_fun setT acc2of3.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of3 2)|exact: mpairAAr].
Qed.

Definition acc0of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T0 :=
  acc Of3 0 \o pairAArAi.

Lemma macc0of3' : measurable_fun setT acc0of3'.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of3 0)|exact: mpairAArAi].
Qed.

Definition acc1of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T1 :=
  acc Of3 1 \o pairAArAi.

Lemma macc1of3' : measurable_fun setT acc1of3'.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of3 1)|exact: mpairAArAi].
Qed.

Definition acc2of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T2 :=
  acc Of3 2 \o pairAArAi.

Lemma macc2of3' : measurable_fun setT acc2of3'.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of3 2)|exact: mpairAArAi].
Qed.

Definition Of4 :=
  [:: existT _ _ T0; existT _ _ T1; existT _ d2 T2; existT _ d3 T3].

Definition acc1of4 : [the measurableType _ of (T0 * T1 * T2 * T3)%type] -> T1 :=
  acc Of4 1 \o pairAAAr.

Lemma macc1of4 : measurable_fun setT acc1of4.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of4 1)|exact: mpairAAAr].
Qed.

Definition acc2of4' :
    [the measurableType _ of (T0 * (T1 * (T2 * T3)))%type] -> T2 :=
  acc Of4 2 \o pairAAArAAi.

Lemma macc2of4' : measurable_fun setT acc2of4'.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of4 2)|exact: mpairAAARAAAi].
Qed.

Definition acc3of4 : [the measurableType _ of (T0 * T1 * T2 * T3)%type] -> T3 :=
  acc Of4 3 \o pairAAAr.

Lemma macc3of4 : measurable_fun setT acc3of4.
Proof.
by apply: measurableT_comp; [exact: (measurable_acc Of4 3)|exact: mpairAAAr].
Qed.

End accessor_functions.
Arguments macc0of2 {d0 d1 _ _}.
Arguments macc1of2 {d0 d1 _ _}.
Arguments macc0of3' {d0 d1 d2 _ _ _}.
Arguments macc1of3 {d0 d1 d2 _ _ _}.
Arguments macc1of3' {d0 d1 d2 _ _ _}.
Arguments macc2of3 {d0 d1 d2 _ _ _}.
Arguments macc2of3' {d0 d1 d2 _ _ _}.
Arguments macc1of4 {d0 d1 d2 d3 _ _ _ _}.
Arguments macc2of4' {d0 d1 d2 d3 _ _ _ _}.
Arguments macc3of4 {d0 d1 d2 d3 _ _ _ _}.

Section insn1_lemmas.
Import Notations.
Context d (T : measurableType d) (R : realType).

Let kcomp_scoreE d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
  (g : R.-sfker [the measurableType _ of (T1 * unit)%type] ~> T2)
  f (mf : measurable_fun setT f) r U :
  (score mf \; g) r U = `|f r|%:E * g (r, tt) U.
Proof.
rewrite /= /kcomp /kscore /= ge0_integral_mscale//=.
by rewrite integral_dirac// indicT mul1e.
Qed.

Lemma scoreE d' (T' : measurableType d') (x : T * T') (U : set T') (f : R -> R)
    (r : R) (r0 : (0 <= r)%R)
    (f0 : (forall r, 0 <= r -> 0 <= f r)%R) (mf : measurable_fun setT f) :
  score (measurableT_comp mf (@macc1of2 _ _ _ _))
    (x, r) (curry (snd \o fst) x @^-1` U) =
  (f r)%:E * \d_x.2 U.
Proof.
by rewrite /score/= /mscale/= ger0_norm//= f0.
Qed.

Lemma score_score (f : R -> R) (g : R * unit -> R)
    (mf : measurable_fun setT f)
    (mg : measurable_fun setT g) :
  letin (score mf) (score mg) =
  score (measurable_funM mf (measurableT_comp mg (measurable_pair2 tt))).
Proof.
apply/eq_sfkernel => x U.
rewrite {1}/letin; unlock.
by rewrite kcomp_scoreE/= /mscale/= diracE normrM muleA EFinM.
Qed.

(* hard constraints to express score below 1 *)
Lemma score_fail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  score (kr r%:num) =
  letin (sample_cst (bernoulli r1) : R.-pker T ~> _)
        (ite (@macc1of2 _ _ _ _) (ret ktt) fail).
Proof.
apply/eq_sfkernel => x U.
rewrite letinE/= /sample; unlock.
rewrite integral_measure_add//= ge0_integral_mscale//= ge0_integral_mscale//=.
rewrite integral_dirac//= integral_dirac//= !indicT/= !mul1e.
by rewrite /mscale/= iteE//= iteE//= failE mule0 adde0 ger0_norm.
Qed.

End insn1_lemmas.

Section letin_ite.
Context d d2 d3 (T : measurableType d) (T2 : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variables (k1 k2 : R.-sfker T ~> Z)
  (u : R.-sfker [the measurableType _ of (T * Z)%type] ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin_iteT : f t -> letin (ite mf k1 k2) u t U = letin k1 u t U.
Proof.
move=> ftT.
rewrite !letinE/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE ftT.
Qed.

Lemma letin_iteF : ~~ f t -> letin (ite mf k1 k2) u t U = letin k2 u t U.
Proof.
move=> ftF.
rewrite !letinE/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE (negbTE ftF).
Qed.

End letin_ite.

Section letinA.
Context d d' d1 d2 d3 (X : measurableType d) (Y : measurableType d')
  (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3)
  (R : realType).
Import Notations.
Variables (t : R.-sfker X ~> T1)
          (u : R.-sfker [the measurableType _ of (X * T1)%type] ~> T2)
          (v : R.-sfker [the measurableType _ of (X * T2)%type] ~> Y)
          (v' : R.-sfker [the measurableType _ of (X * T1 * T2)%type] ~> Y)
          (vv' : forall y, v =1 fun xz => v' (xz.1, y, xz.2)).

Lemma letinA x A : measurable A ->
  letin t (letin u v') x A
  =
  (letin (letin t u) v) x A.
Proof.
move=> mA.
rewrite !letinE.
under eq_integral do rewrite letinE.
rewrite integral_kcomp; [|by []|].
- apply: eq_integral => y _.
  apply: eq_integral => z _.
  by rewrite (vv' y).
exact: (measurableT_comp (measurable_kernel v _ mA)).
Qed.

End letinA.

Section letinC.
Context d d1 d' (X : measurableType d) (Y : measurableType d1)
  (Z : measurableType d') (R : realType).

Import Notations.

Variables (t : R.-sfker Z ~> X)
          (t' : R.-sfker [the measurableType _ of (Z * Y)%type] ~> X)
          (tt' : forall y, t =1 fun z => t' (z, y))
          (u : R.-sfker Z ~> Y)
          (u' : R.-sfker [the measurableType _ of (Z * X)%type] ~> Y)
          (uu' : forall x, u =1 fun z => u' (z, x)).

Definition T z : set X -> \bar R := t z.
Let T0 z : (T z) set0 = 0. Proof. by []. Qed.
Let T_ge0 z x : 0 <= (T z) x. Proof. by []. Qed.
Let T_semi_sigma_additive z : semi_sigma_additive (T z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R X (T z) (T0 z) (T_ge0 z)
  (@T_semi_sigma_additive z).

Let sfinT z : sfinite_measure (T z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ X R
  (T z) (sfinT z).

Definition U z : set Y -> \bar R := u z.
Let U0 z : (U z) set0 = 0. Proof. by []. Qed.
Let U_ge0 z x : 0 <= (U z) x. Proof. by []. Qed.
Let U_semi_sigma_additive z : semi_sigma_additive (U z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R Y (U z) (U0 z) (U_ge0 z)
  (@U_semi_sigma_additive z).

Let sfinU z : sfinite_measure (U z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ Y R
  (U z) (sfinU z).

Lemma letinC z A : measurable A ->
  letin t
  (letin u'
  (ret (measurable_fun_prod macc1of3 macc2of3))) z A =
  letin u
  (letin t'
  (ret (measurable_fun_prod macc2of3 macc1of3))) z A.
Proof.
move=> mA.
rewrite !letinE.
under eq_integral.
  move=> x _.
  rewrite letinE -uu'.
  under eq_integral do rewrite retE /=.
  over.
rewrite (sfinite_Fubini
  [the {sfinite_measure set X -> \bar R} of T z]
  [the {sfinite_measure set Y -> \bar R} of U z]
  (fun x => \d_(x.1, x.2) A ))//; last first.
  apply/EFin_measurable_fun => /=; rewrite (_ : (fun x => _) = mindic R mA)//.
  by apply/funext => -[].
rewrite /=.
apply: eq_integral => y _.
by rewrite letinE/= -tt'; apply: eq_integral => // x _; rewrite retE.
Qed.

End letinC.

(* sample programs *)

Section constants.
Variable R : realType.
Local Open Scope ring_scope.

Lemma onem1S n : `1- (1 / n.+1%:R) = (n%:R / n.+1%:R)%:nng%:num :> R.
Proof.
by rewrite /onem/= -{1}(@divrr _ n.+1%:R) ?unitfE// -mulrBl -natr1 addrK.
Qed.

Lemma p1S n : (1 / n.+1%:R)%:nng%:num <= 1 :> R.
Proof. by rewrite ler_pdivr_mulr//= mul1r ler1n. Qed.

Lemma p12 : (1 / 2%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Lemma p14 : (1 / 4%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Lemma onem27 : `1- (2 / 7%:R) = (5%:R / 7%:R)%:nng%:num :> R.
Proof. by apply/eqP; rewrite subr_eq/= -mulrDl -natrD divrr// unitfE. Qed.

Lemma p27 : (2 / 7%:R)%:nng%:num <= 1 :> R.
Proof. by rewrite /= lter_pdivr_mulr// mul1r ler_nat. Qed.

End constants.
Arguments p12 {R}.
Arguments p14 {R}.
Arguments p27 {R}.
Arguments p1S {R}.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for Poisson *)
Definition poisson k r : R :=
  if r > 0 then r ^+ k / k`!%:R^-1 * expR (- r) else 1%:R.

Lemma poisson_ge0 k r : 0 <= poisson k r.
Proof.
rewrite /poisson; case: ifPn => r0//.
by rewrite mulr_ge0 ?expR_ge0// mulr_ge0// exprn_ge0 ?ltW.
Qed.

Lemma poisson_gt0 k r : 0 < r -> 0 < poisson k.+1 r.
Proof.
move=> r0; rewrite /poisson r0 mulr_gt0  ?expR_gt0//.
by rewrite divr_gt0// ?exprn_gt0// invr_gt0 ltr0n fact_gt0.
Qed.

Lemma measurable_poisson k : measurable_fun setT (poisson k).
Proof.
rewrite /poisson; apply: measurable_fun_if => //.
  apply: (measurable_fun_bool true).
  rewrite (_ : _ @^-1` _ = `]0, +oo[%classic)//.
  by apply/seteqP; split => x /=; rewrite in_itv/= andbT.
by apply: measurable_funM => /=;
  [exact: measurable_funM|exact: measurableT_comp].
Qed.

Definition poisson3 := poisson 4 3%:R. (* 0.168 *)
Definition poisson10 := poisson 4 10%:R. (* 0.019 *)

End poisson.

Section exponential.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for exponential *)
Definition exp_density x r : R := r * expR (- r * x).

Lemma exp_density_gt0 x r : 0 < r -> 0 < exp_density x r.
Proof. by move=> r0; rewrite /exp_density mulr_gt0// expR_gt0. Qed.

Lemma exp_density_ge0 x r : 0 <= r -> 0 <= exp_density x r.
Proof. by move=> r0; rewrite /exp_density mulr_ge0// expR_ge0. Qed.

Lemma mexp_density x : measurable_fun setT (exp_density x).
Proof.
apply: measurable_funM => //=; apply: measurableT_comp => //.
exact: measurable_funM.
Qed.

End exponential.

Lemma letin_sample_bernoulli d d' (T : measurableType d)
    (T' : measurableType d') (R : realType)(r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample_cst (bernoulli r1)) u x y =
  r%:num%:E * u (x, true) y + (`1- (r%:num))%:E * u (x, false) y.
Proof.
rewrite letinE/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section sample_and_return.
Import Notations.
Context d (T : measurableType d) (R : realType).

Definition sample_and_return : R.-sfker T ~> _ :=
  letin
    (sample_cst [the probability _ _ of bernoulli p27]) (* T -> B *)
    (ret macc1of2) (* T * B -> B *).

Lemma sample_and_returnE t U : sample_and_return t U =
  (2 / 7%:R)%:E * \d_true U + (5%:R / 7%:R)%:E * \d_false U.
Proof.
by rewrite /sample_and_return letin_sample_bernoulli !retE onem27.
Qed.

End sample_and_return.

(* trivial example *)
Section sample_and_branch.
Import Notations.
Context d (T : measurableType d) (R : realType).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Definition sample_and_branch : R.-sfker T ~> mR R :=
  letin
    (sample_cst [the probability _ _ of bernoulli p27]) (* T -> B *)
    (ite macc1of2 (ret k3) (ret k10)).

Lemma sample_and_branchE t U : sample_and_branch t U =
  (2 / 7%:R)%:E * \d_(3%:R : R) U +
  (5%:R / 7%:R)%:E * \d_(10%:R : R) U.
Proof.
by rewrite /sample_and_branch letin_sample_bernoulli/= !iteE !retE onem27.
Qed.

End sample_and_branch.

Section bernoulli_and.
Context d (T : measurableType d) (R : realType).
Import Notations.

Definition mand (x y : T * mbool * mbool -> mbool)
  (t : T * mbool * mbool) : mbool := x t && y t.

Lemma measurable_fun_mand (x y : T * mbool * mbool -> mbool) :
  measurable_fun setT x -> measurable_fun setT y ->
  measurable_fun setT (mand x y).
Proof.
move=> /= mx my; apply: (measurable_fun_bool true).
rewrite [X in measurable X](_ : _ =
    (x @^-1` [set true]) `&` (y @^-1` [set true])); last first.
  by rewrite /mand; apply/seteqP; split => z/= /andP.
apply: measurableI.
- by rewrite -[X in measurable X]setTI; exact: mx.
- by rewrite -[X in measurable X]setTI; exact: my.
Qed.

Definition bernoulli_and : R.-sfker T ~> mbool :=
    (letin (sample_cst [the probability _ _ of bernoulli p12])
     (letin (sample_cst [the probability _ _ of bernoulli p12])
        (ret (measurable_fun_mand macc1of3 macc2of3)))).

Lemma bernoulli_andE t U :
  bernoulli_and t U =
  sample_cst (bernoulli p14) t U.
Proof.
rewrite /bernoulli_and 3!letin_sample_bernoulli/= /mand/= muleDr//= -muleDl//.
rewrite !muleA -addeA -muleDl// -!EFinM !onem1S/= -splitr mulr1.
have -> : (1 / 2 * (1 / 2) = 1 / 4%:R :> R)%R by rewrite mulf_div mulr1// -natrM.
rewrite /bernoulli/= measure_addE/= /mscale/= -!EFinM; congr( _ + (_ * _)%:E).
have -> : (1 / 2 = 2 / 4%:R :> R)%R.
  by apply/eqP; rewrite eqr_div// ?pnatr_eq0// mul1r -natrM.
by rewrite onem1S// -mulrDl.
Qed.

End bernoulli_and.

Section staton_bus.
Import Notations.
Context d (T : measurableType d) (R : realType) (h : R -> R).
Hypothesis mh : measurable_fun setT h.
Definition kstaton_bus : R.-sfker T ~> mbool :=
  letin (sample_cst [the probability _ _ of bernoulli p27])
  (letin
    (letin (ite macc1of2 (ret k3) (ret k10))
      (score (measurableT_comp mh macc2of3)))
    (ret macc1of3)).

Definition staton_bus := normalize kstaton_bus.

End staton_bus.

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)
Section staton_bus_poisson.
Import Notations.
Context d (T : measurableType d) (R : realType).
Let poisson4 := @poisson R 4%N.
Let mpoisson4 := @measurable_poisson R 4%N.

Definition kstaton_bus_poisson : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mpoisson4.

Let kstaton_bus_poissonE t U : kstaton_bus_poisson t U =
  (2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U.
Proof.
rewrite /kstaton_bus.
rewrite letin_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _).
- rewrite letin_kret//.
  rewrite letin_iteT//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: poisson_ge0.
- by rewrite onem27.
  rewrite letin_kret//.
  rewrite letin_iteF//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: poisson_ge0.
Qed.

(* true -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)
(* false -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)

Lemma staton_busE P (t : R) U :
  let N := ((2 / 7%:R) * poisson4 3%:R +
            (5%:R / 7%:R) * poisson4 10%:R)%R in
  staton_bus mpoisson4 P t U =
  ((2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus normalizeE /= !kstaton_bus_poissonE !diracT !mule1 ifF //.
apply/negbTE; rewrite gt_eqF// lte_fin.
by rewrite addr_gt0// mulr_gt0//= ?divr_gt0// ?ltr0n// poisson_gt0// ltr0n.
Qed.

End staton_bus_poisson.

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (r e^-(15/60 r)) in
   return x *)
Section staton_bus_exponential.
Import Notations.
Context d (T : measurableType d) (R : realType).
Let exp1560 := @exp_density R (ratr (15%:Q / 60%:Q)).
Let mexp1560 := @mexp_density R (ratr (15%:Q / 60%:Q)).

(* 15/60 = 0.25 *)

Definition kstaton_bus_exponential : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mexp1560.

Let kstaton_bus_exponentialE t U : kstaton_bus_exponential t U =
  (2 / 7%:R)%:E * (exp1560 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (exp1560 10%:R)%:E * \d_false U.
Proof.
rewrite /kstaton_bus.
rewrite letin_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _).
- rewrite letin_kret//.
  rewrite letin_iteT//.
  rewrite letin_retk//.
  rewrite scoreE//= => r r0; exact: exp_density_ge0.
- by rewrite onem27.
  rewrite letin_kret//.
  rewrite letin_iteF//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: exp_density_ge0.
Qed.

(* true -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)
(* false -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)

Lemma staton_bus_exponentialE P (t : R) U :
  let N := ((2 / 7%:R) * exp1560 3%:R +
            (5%:R / 7%:R) * exp1560 10%:R)%R in
  staton_bus mexp1560 P t U =
  ((2 / 7%:R)%:E * (exp1560 3%:R)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (exp1560 10%:R)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite normalizeE /= !kstaton_bus_exponentialE !diracT !mule1 ifF //.
apply/negbTE; rewrite gt_eqF// lte_fin.
by rewrite addr_gt0// mulr_gt0//= ?divr_gt0// ?ltr0n// exp_density_gt0 ?ltr0n.
Qed.

End staton_bus_exponential.

(* X + Y is a measurableType if X and Y are *)
Canonical sum_pointedType (X Y : pointedType) :=
  PointedType (X + Y) (@inl X Y point).

Section measurable_sum.
Context d d' (X : measurableType d) (Y : measurableType d').

Definition measurable_sum : set (set (X + Y)) := setT.

Let sum0 : measurable_sum set0. Proof. by []. Qed.

Let sumC A : measurable_sum A -> measurable_sum (~` A). Proof. by []. Qed.

Let sumU (F : (set (X + Y))^nat) : (forall i, measurable_sum (F i)) ->
  measurable_sum (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display (X + Y)%type
  (Pointed.class _) measurable_sum sum0 sumC sumU.

End measurable_sum.

Lemma measurable_fun_sum dA dB d' (A : measurableType dA) (B : measurableType dB)
    (Y : measurableType d') (f : A -> Y) (g : B -> Y) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun tb : A + B =>
    match tb with inl a => f a | inr b => g b end).
Proof.
move=> mx my/= _ Z mZ /=; rewrite setTI /=.
rewrite (_ : _ @^-1` Z = inl @` (f @^-1` Z) `|` inr @` (g @^-1` Z)).
  exact: measurableU.
apply/seteqP; split.
  by move=> [a Zxa|b Zxb]/=; [left; exists a|right; exists b].
by move=> z [/= [a Zxa <-//=]|]/= [b Zyb <-//=].
Qed.

(* TODO: measurable_fun_if_pair -> measurable_fun_if_pair_bool? *)
Lemma measurable_fun_if_pair_nat d d' (X : measurableType d)
    (Y : measurableType d') (f g : X -> Y) (n : nat) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun xn => if xn.2 == n then f xn.1 else g xn.1).
Proof.
move=> mx my; apply: measurable_fun_ifT => //=.
- have h : measurable_fun [set: nat] (fun t => t == n) by [].
  exact: (@measurableT_comp _ _ _ _ _ _ _ _ _ h).
- exact: measurableT_comp.
- exact: measurableT_comp.
Qed.

Module CASE_NAT.
Section case_nat.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Section case_nat_ker.
Variable k : R.-ker X ~> Y.

Definition case_nat_ j : X * nat -> {measure set Y -> \bar R} :=
  fun xn => if xn.2 == j then k xn.1 else [the measure _ _ of mzero].

Let measurable_fun_case_nat_ m U : measurable U ->
  measurable_fun setT (case_nat_ m ^~ U).
Proof.
move=> mU; rewrite /case_nat_ (_ : (fun _ => _) =
    (fun x => if x.2 == m then k x.1 U else mzero U)) /=; last first.
  by apply/funext => -[t b]/=; case: ifPn.
apply: (@measurable_fun_if_pair_nat _ _ _ _ (k ^~ U) (fun=> mzero U)) => //.
exact/measurable_kernel.
Qed.

#[export]
HB.instance Definition _ j := isKernel.Build _ _ _ _ _
  (case_nat_ j) (measurable_fun_case_nat_ j).
End case_nat_ker.

Section sfcase_nat.
Variable k : R.-sfker X ~> Y.

Let sfcase_nat_ j  : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> case_nat_ k j x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of case_nat_ (k_ n) j]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  exists r%:num => /= -[x [|n']]; rewrite /case_nat_//= /mzero//.
    by case: ifPn => //= ?; rewrite /mzero.
  by case: ifPn => // ?; rewrite /= /mzero.
move=> [x b] U mU; rewrite /case_nat_; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries eseries0.
Qed.

#[export]
HB.instance Definition _ j := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (case_nat_ k j) (sfcase_nat_ j).
End sfcase_nat.

Section fkcase_nat.
Variable k : R.-fker X ~> Y.

Let case_nat_uub (m : nat) : measure_fam_uub (case_nat_ k m).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
exists M%:num => /= -[]; rewrite /case_nat_ => t [|m']/=.
  by case: ifPn => //= ?; rewrite /mzero//=.
by case: ifPn => //= ?; rewrite /mzero//=.
Qed.

#[export]
HB.instance Definition _ j := Kernel_isFinite.Build _ _ _ _ _
  (case_nat_ k j) (case_nat_uub j).
End fkcase_nat.

End case_nat.
End CASE_NAT.

Import CASE_NAT.

Section case_nat.
Context d d' (T : measurableType d) (T' : measurableType d') (R : realType).

Import CASE_NAT.

(* case analysis on the nat datatype *)
Definition case_nat (t : R.-sfker T ~> nat) (u_ : (R.-sfker T ~> T')^nat)
    : R.-sfker T ~> T' :=
  [the R.-sfker T ~> nat of t] \;
  [the R.-sfker T * nat ~> T' of
    kseries (fun n => [the R.-sfker T * nat ~> T' of case_nat_ (u_ n) n])].

End case_nat.

Definition measure_sum_display :
  (measure_display * measure_display) -> measure_display.
Proof. exact. Qed.

Definition image_classes d1 d2
    (T1 : measurableType d1) (T2 : measurableType d2) (T : Type)
    (f1 : T1 -> T) (f2 : T2 -> T)  :=
  <<s image_class setT f1 measurable `|`
      image_class setT f2 measurable >>.

Section sum_salgebra_instance.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Let f1 : T1 -> T1 + T2 := @inl T1 T2.
Let f2 : T2 -> T1 + T2 := @inr T1 T2.

Lemma sum_salgebra_set0 : image_classes f1 f2 (set0 : set (T1 + T2)).
Proof. exact: sigma_algebra0. Qed.

Lemma sum_salgebra_setC A : image_classes f1 f2 A ->
  image_classes f1 f2 (~` A).
Proof. exact: sigma_algebraC. Qed.

Lemma sum_salgebra_bigcup (F : _^nat) : (forall i, image_classes f1 f2 (F i)) ->
  image_classes f1 f2 (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition sum_salgebra_mixin :=
  @isMeasurable.Build (measure_sum_display (d1, d2))
    (T1 + T2)%type (Pointed.class _) (image_classes f1 f2)
    (sum_salgebra_set0) (sum_salgebra_setC) (sum_salgebra_bigcup).

End sum_salgebra_instance.
Reserved Notation "p .-sum" (at level 1, format "p .-sum").
Reserved Notation "p .-sum.-measurable"
 (at level 2, format "p .-sum.-measurable").
Notation "p .-sum" := (measure_sum_display p) : measure_display_scope.
Notation "p .-sum.-measurable" :=
  ((p.-sum).-measurable : set (set (_ + _))) :
    classical_set_scope.

Module CASE_SUM.

Section case_suml.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Let A : measurableType _ := unit.

Section kcase_suml.
Variable k : R.-ker X ~> Y.

Definition case_suml (a : A) : X * A -> {measure set Y -> \bar R} :=
  fun xa => k xa.1.

Let measurable_fun_case_suml a U : measurable U ->
  measurable_fun setT (case_suml a ^~ U).
Proof.
move=> /= mU; rewrite /case_suml.
have h := measurable_kernel k _ mU.
rewrite (_ : (fun x : X * unit => k x.1 U) = (fun x : X => k x U) \o fst) //.
by apply: measurableT_comp => //.
Qed.

#[export]
HB.instance Definition _ a := isKernel.Build _ _ _ _ _
  (case_suml a) (measurable_fun_case_suml a).
End kcase_suml.

Section sfkcase_suml.
Variable k : R.-sfker X ~> Y.

Let sfinite_case_suml (a : A) : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> case_suml k a x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of case_suml (k_ n) a]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /case_suml//= /mzero//.
move=> [x b] U mU; rewrite /case_suml /=.
by rewrite /mseries hk.
Qed.

#[export]
HB.instance Definition _ (a : A) := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (case_suml k a) (sfinite_case_suml a).
End sfkcase_suml.

Section fkcase_suml.
Variable k : R.-fker X ~> Y.

Let case_suml_uub (a : A) : measure_fam_uub (case_suml k a).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
by exists M%:num => /= -[]; rewrite /case_suml.
Qed.

#[export]
HB.instance Definition _ a := Kernel_isFinite.Build _ _ _ _ _
  (case_suml k a) (case_suml_uub a).
End fkcase_suml.

End case_suml.

Section case_sumr.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Let B : measurableType _ := bool.

Section kcase_sumr.
Variable k : R.-ker X ~> Y.

Definition case_sumr (b : B) : X * B -> {measure set Y -> \bar R} :=
  fun xa => if xa.2 == b then k xa.1 else [the measure _ _ of mzero].

Let measurable_fun_case_sumr b U : measurable U ->
  measurable_fun setT (case_sumr b ^~ U).
Proof.
move=> /= mU; rewrite /case_suml.
have h := measurable_kernel k _ mU.
rewrite /case_sumr.
rewrite (_ : (fun x : X * bool => case_sumr b x U) =
  (fun x : X * bool => (if x.2 == b then k x.1 U else [the {measure set Y -> \bar R} of mzero] U))); last first.
  apply/funext => x.
  rewrite /case_sumr.
  by case: ifPn.
apply: measurable_fun_ifT => //=.
  rewrite (_ : (fun t : X * bool => t.2 == b) = (fun t : bool => t == b) \o snd)//.
  apply: measurableT_comp => //.
rewrite (_ : (fun t : X * bool => k t.1 U) = (fun t : X => k t U) \o fst)//.
by apply: measurableT_comp => //.
Qed.

#[export]
HB.instance Definition _ b := isKernel.Build _ _ _ _ _
  (case_sumr b) (measurable_fun_case_sumr b).
End kcase_sumr.

Section sfkcase_sumr.
Variable k : R.-sfker X ~> Y.

Let sfinite_case_sumr b : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> case_sumr k b x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of case_sumr (k_ n) b]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /case_sumr//=; case: ifPn => // _;
    rewrite /= (le_lt_trans _ (k_r x))// /mzero//.
move=> [x [|]] U mU; rewrite /case_sumr /=; case: b => //=; rewrite ?hk//;
by rewrite /mseries/= eseries0.
Qed.

#[export]
HB.instance Definition _ b := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (case_sumr k b) (sfinite_case_sumr b).
End sfkcase_sumr.

Section fkcase_sumr.
Variable k : R.-fker X ~> Y.

Let case_sumr_uub b : measure_fam_uub (case_sumr k b).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
by exists M%:num => /= -[]; rewrite /case_sumr => x [|] /=; case: b => //=;
  rewrite (le_lt_trans _ (hM x))// /mzero.
Qed.

#[export]
HB.instance Definition _ b := Kernel_isFinite.Build _ _ _ _ _
  (case_sumr k b) (case_sumr_uub b).
End fkcase_sumr.

End case_sumr.
End CASE_SUM.

Section case_sum'.

Section kcase_sum'.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Let A : measurableType _ := unit.
Let B : measurableType _ := bool.
Variables (k : (A + B)%type -> R.-sfker X ~> Y).

Definition case_sum' : X * (A + B)%type -> {measure set Y -> \bar R} :=
  fun xab => match xab with
             | (x, inl a) => CASE_SUM.case_suml (k xab.2) a (x, a)
             | (x, inr b) => CASE_SUM.case_sumr (k xab.2) b (x, b)
             end.

Let measurable_fun_case_sum' U : measurable U ->
  measurable_fun setT (case_sum' ^~ U).
Proof.
rewrite /= => mU.
apply: (measurability (ErealGenInftyO.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; apply: measurableI => //.
rewrite /case_sum' /CASE_SUM.case_suml /CASE_SUM.case_sumr /=.
rewrite (_ :
  (fun x : X * (unit + bool) => (let (x0, s) := x in
   match s with inl _ => k x.2 x0 | inr b => if b == b then k x.2 x0 else mzero
   end) U) =
  (fun x : X * (unit + bool) => k x.2 x.1 U)); last first.
  by apply/funext => -[x1 [a|b]] //; rewrite eqxx.
rewrite (_ : _ @^-1` _ =
  ([set x1 | k (inl tt) x1 U < x%:E] `*` inl @` [set tt]) `|`
  ([set x1 | k (inr false) x1 U < x%:E] `*` inr @` [set false]) `|`
  ([set x1 | k (inr true) x1 U < x%:E] `*` inr @` [set true])); last first.
  apply/seteqP; split.
  - move=> z /=; rewrite in_itv/=; move: z => [z [[]|[|]]]//= ?.
    + by do 2 left; split => //; exists tt.
    + by right; split => //; exists true.
    + by left; right; split => //; exists false.
  - move=> z /=; rewrite in_itv/=; move: z => [z [[]|[|]]]//=.
    - move=> [[[]//|]|].
      + by move=> [_ []].
      + by move=> [_ []].
    - move=> [[|]|[]//].
      + by move=> [_ []].
      + by move=> [_ [] [|]].
    - move=> [[|[]//]|].
      + by move=> [_ []].
      + by move=> [_ [] [|]].
pose h1 := [set xub : X * (unit + bool) | k (inl tt) xub.1 U < x%:E].
have mh1 : measurable h1.
  rewrite -[X in measurable X]setTI; apply: emeasurable_fun_infty_o => //=.
  have H : measurable_fun [set: X] (fun x => k (inl tt) x U) by exact/measurable_kernel.
  move=> _ /= C mC; rewrite setTI.
  have := H measurableT _ mC; rewrite setTI => {}H.
  rewrite [X in measurable X](_ : _ = ((fun x => k (inl tt) x U) @^-1` C) `*` setT)//.
    exact: measurableM.
  by apply/seteqP; split => [z//=| z/= []].
set h2 := [set xub : X * (unit + bool)| k (inr false) xub.1 U < x%:E].
have mh2 : measurable h2.
  rewrite -[X in measurable X]setTI.
  apply: emeasurable_fun_infty_o => //=.
  have H : measurable_fun [set: X] (fun x => k (inr false) x U) by exact/measurable_kernel.
  move=> _ /= C mC; rewrite setTI.
  have := H measurableT _ mC; rewrite setTI => {}H.
  rewrite [X in measurable X](_ : _ = ((fun x => k (inr false) x U) @^-1` C) `*` setT)//.
    exact: measurableM.
  by apply/seteqP; split => [z //=|z/= []].
set h3 := [set xub : X * (unit + bool)| k (inr true) xub.1 U < x%:E].
have mh3 : measurable h3.
  rewrite -[X in measurable X]setTI.
  apply: emeasurable_fun_infty_o => //=.
  have H : measurable_fun [set: X] (fun x => k (inr true) x U) by exact/measurable_kernel.
  move=> _ /= C mC; rewrite setTI.
  have := H measurableT _ mC; rewrite setTI => {}H.
  rewrite [X in measurable X](_ : _ = ((fun x => k (inr true) x U) @^-1` C) `*` setT)//.
    exact: measurableM.
  by apply/seteqP; split=> [z//=|z/= []].
apply: measurableU.
- apply: measurableU.
  + apply: measurableM => //.
    rewrite [X in measurable X](_ : _ = ysection h1 (inl tt))//.
    * by apply: measurable_ysection.
    * by apply/seteqP; split => z /=; rewrite /ysection /= inE.
  + apply: measurableM => //.
    rewrite [X in measurable X](_ : _ = ysection h2 (inr false))//.
    * by apply: measurable_ysection.
    * by apply/seteqP; split => z /=; rewrite /ysection /= inE.
- apply: measurableM => //.
  rewrite [X in measurable X](_ : _ = ysection h3 (inr true))//.
  + by apply: measurable_ysection.
  + by apply/seteqP; split => z /=; rewrite /ysection /= inE.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  (case_sum') (measurable_fun_case_sum').
End kcase_sum'.

Section sfkcase_sum'.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Let A : measurableType _ := unit.
Let B : measurableType _ := bool.
Variables (k : (A + B)%type -> R.-sfker X ~> Y).

Let sfinite_case_sum' : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> case_sum' k x U = mseries (k_ ^~ x) 0 U.
Proof.
rewrite /=.
set f : A + B -> (R.-fker _ ~> _)^nat :=
  fun ab : A + B => sval (cid (sfinite_kernel (k ab))).
set Hf := fun ab : A + B => svalP (cid (sfinite_kernel (k ab))).
rewrite /= in Hf.
exists (fun n => [the R.-ker _ ~> _ of case_sum' (fun ab => [the R.-fker _ ~> _ of f ab n])]).
  move=> n /=.
  have [rtt Hrtt] := measure_uub (f (inl tt) n).
  have [rfalse Hrfalse] := measure_uub (f (inr false) n).
  have [rtrue Hrtrue] := measure_uub (f (inr true) n).
  exists (maxr rtt (maxr rfalse rtrue)) => //= -[x [[]|[|]]] /=.
  by rewrite 2!EFin_max lt_maxr Hrtt.
  by rewrite /CASE_SUM.case_sumr /= 2!EFin_max 2!lt_maxr Hrtrue 2!orbT.
  by rewrite /CASE_SUM.case_sumr /= 2!EFin_max 2!lt_maxr Hrfalse orbT.
move=> [x [[]|[|]]] U mU/=-.
by rewrite (Hf (inl tt) x _ mU).
by rewrite (Hf (inr true) x _ mU).
by rewrite (Hf (inr false) x _ mU).
Qed.

#[export]
HB.instance Definition _ := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (case_sum' k) (sfinite_case_sum').
End sfkcase_sum'.

End case_sum'.

Section case_sum.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Let A : measurableType _ := unit.
Let B : measurableType _ := bool.

Import CASE_SUM.

(* case analysis on the datatype unit + bool *)
Definition case_sum (f : R.-sfker X ~> (A + B)%type)
    (k : (A + B)%type-> R.-sfker X ~> Y) : R.-sfker X ~> Y :=
  [the R.-sfker X ~> (A + B)%type of f] \;
  [the R.-sfker X * (A + B) ~> Y of case_sum' k].

End case_sum.

(* counting measure as a kernel *)
Section kcounting.
Context d (G : measurableType d) (R : realType).

Definition kcounting : G -> {measure set nat -> \bar R} := fun=> counting.

Let mkcounting U : measurable U -> measurable_fun setT (kcounting ^~ U).
Proof. by []. Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ kcounting mkcounting.

Let sfkcounting : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kcounting x U = mseries (k_ ^~ x) 0 U.
Proof.
exists (fun n => [the R.-fker _ ~> _ of
  @kdirac _ _ G nat R _ (@measurable_cst _ _ _ _ setT n)]).
  by move=> n /=; exact: measure_uub.
by move=> g U mU; rewrite /kcounting/= counting_dirac.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ R kcounting sfkcounting.

End kcounting.

(* formalization of the iterate construct of Staton ESOP 2017, Sect. 4.2 *)
Section iterate.
Context d {G : measurableType d} {R : realType}.
Let A : measurableType _ := unit.
Let B : measurableType _ := bool.

(* formalization of iterate^n
   Gamma |-p iterate^n t from x = u : B *)
Variables (t : R.-sfker (G * A) ~> (A + B)%type)
          (u : G -> A) (mu : measurable_fun setT u).

Fixpoint iterate_ n : R.-sfker G ~> B :=
  match n with
  | 0%N => case_sum (letin (ret mu) t)
             (fun x => match x with
                       | inl a => fail
                       | inr b => ret (measurable_cst b)
                       end)
  | m.+1 => case_sum (letin (ret mu) t)
              (fun x => match x with
                        | inl a => iterate_ m
                        | inr b => fail
                        end)
  end.

(* formalization of iterate (A = unit, B = bool)
 Gamma, x : A |-p t : A + B    Gamma |-d u : A
-----------------------------------------------
    Gamma |-p iterate t from x = u : B *)
Definition iterate : R.-sfker G ~> B := case_nat (kcounting R) iterate_.

End iterate.

(* an s-finite kernel to test that two expressions are different *)
Section lift_neq.
Context {R : realType} d (G : measurableType d).
Variables (f : G -> bool) (g : G -> bool).

Definition flift_neq  : G -> bool := fun x' => f x' != g x'.

Hypotheses (mf : measurable_fun setT f) (mg : measurable_fun setT g).

(* see also emeasurable_fun_neq *)
Lemma measurable_fun_flift_neq : measurable_fun setT flift_neq.
Proof.
apply: (measurable_fun_bool true).
rewrite /flift_neq /= (_ : _ @^-1` _ = ([set x | f x] `&` [set x | ~~ g x]) `|`
                                       ([set x | ~~ f x] `&` [set x | g x])).
  apply: measurableU; apply: measurableI.
  - by rewrite -[X in measurable X]setTI; exact: mf.
  - rewrite [X in measurable X](_ : _ = ~` [set x | g x]); last first.
      by apply/seteqP; split => x /= /negP.
    by apply: measurableC; rewrite -[X in measurable X]setTI; exact: mg.
  - rewrite [X in measurable X](_ : _ = ~` [set x | f x]); last first.
      by apply/seteqP; split => x /= /negP.
    by apply: measurableC; rewrite -[X in measurable X]setTI; exact: mf.
  - by rewrite -[X in measurable X]setTI; exact: mg.
by apply/seteqP; split => x /=; move: (f x) (g x) => [|] [|]//=; intuition.
Qed.

Definition lift_neq : R.-sfker G ~> bool := ret measurable_fun_flift_neq.

End lift_neq.

Section von_neumann_trick.
Context d {T : measurableType d} {R : realType}.

Definition kinrtt {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} :=
  @measurable_cst _ _ T1 _ setT (@inl unit T2 tt).

Definition finlb d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    : T1 * bool -> T2 + bool := fun t1b => inr t1b.2.

Lemma minlb {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} :
  measurable_fun setT (@finlb _ _ T1 T2).
Proof. exact: measurableT_comp. Qed.

Variable (D : pprobability bool R (* biased coin *)).

Definition von_neumann_trick' : R.-sfker (T * unit) ~> (unit + bool)%type :=
  letin (sample_cst D)
    (letin (sample_cst D)
      (letin (lift_neq macc1of3 macc2of3)
        (ite (macc3of4)
           (letin (ret macc1of4) (ret minlb))
           (ret kinrtt)))).

Definition von_neumann_trick : R.-sfker T ~> bool :=
  iterate von_neumann_trick' ktt.

End von_neumann_trick.
