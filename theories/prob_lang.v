From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral exp kernel.

(******************************************************************************)
(*  Semantics of a probabilistic programming language using s-finite kernels  *)
(*                                                                            *)
(*       bernoulli r1 == Bernoulli probability with r1 a proof that           *)
(*                       r : {nonneg R} is smaller than 1                     *)
(*                                                                            *)
(*           sample P == sample according to the probability P                *)
(*          letin l k == execute l, augment the context, and execute k        *)
(*             ret mf == access the context with f and return the result      *)
(*           score mf == observe t from d, where f is the density of d and    *)
(*                       t occurs in f                                        *)
(*                       e.g., score (r e^(-r * t)) = observe t from exp(r)   *)
(*     pnormalize k P == normalize the kernel k into a probability kernel,    *)
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
Lemma onem1' (R : numDomainType) (p : R) : (p + `1- p = 1)%R.
Proof. by rewrite /onem addrCA subrr addr0. Qed.

Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) :
  (p%:num <= 1 -> 0 <= `1-(p%:num))%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R})
   (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).

Lemma expR_ge0 (R : realType) (x : R) : (0 <= expR x)%R.
Proof. by rewrite ltW// expR_gt0. Qed.
(* /TODO: PR *)

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition mbernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac true]]
    [the measure _ _ of mscale (onem_nonneg p1) [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on mbernoulli.

Local Close Scope ring_scope.

Let mbernoulli_setT : mbernoulli [set: _] = 1.
Proof.
rewrite /mbernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracT !mule1 -EFinD onem1'.
Qed.

HB.instance Definition _ :=
  @isProbability.Build _ _ R mbernoulli mbernoulli_setT.

Definition bernoulli := [the probability _ _ of mbernoulli].

End bernoulli.

Section mscore.
Variables (d : _) (T : measurableType d).
Variables (R : realType) (f : T -> R).

Definition mscore t : {measure set _ -> \bar R} :=
  let p := NngNum (normr_ge0 (f t)) in
  [the measure _ _ of mscale p [the measure _ _ of dirac tt]].

Lemma mscoreE t U : mscore t U = if U == set0 then 0 else `| (f t)%:E |.
Proof.
rewrite /mscore/= /mscale/=; have [->|->] := set_unit U.
  by rewrite eqxx dirac0 mule0.
by rewrite diracT mule1 (negbTE (setT0 _)).
Qed.

Lemma measurable_fun_mscore U : measurable_fun setT f ->
  measurable_fun setT (mscore ^~ U).
Proof.
move=> mr; under eq_fun do rewrite mscoreE/=.
have [U0|U0] := eqVneq U set0; first exact: measurable_fun_cst.
by apply: measurable_fun_comp => //; exact: measurable_fun_comp.
Qed.

End mscore.

(* decomposition of score into finite kernels *)
Module SCORE.
Section score.
Variables (d : _) (T : measurableType d) (R : realType) (f : T -> R).

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
apply: measurable_fun_comp => /=; last exact/measurable_fun_mscore.
rewrite (_ : (fun x => _) = (fun x => x *
    (\1_(`[i%:R%:E, i.+1%:R%:E [%classic : set _) x)%:E)); last first.
  apply/funext => x; case: ifPn => ix; first by rewrite indicE/= mem_set ?mule1.
  by rewrite indicE/= memNset ?mule0// /= in_itv/=; exact/negP.
apply emeasurable_funM => /=; first exact: measurable_fun_id.
apply/EFin_measurable_fun.
by rewrite (_ : \1__ = mindic R (emeasurable_itv R i)).
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
Variables (R : realType) (d : _) (T : measurableType d) (r : T -> R).

Definition kscore (mr : measurable_fun setT r)
    : T -> {measure set _ -> \bar R} :=
  fun t => [the measure _ _ of mscore r t].

Variable (mr : measurable_fun setT r).

Let measurable_fun_kscore U : measurable U ->
  measurable_fun setT (kscore mr ^~ U).
Proof. by move=> /= _; exact: measurable_fun_mscore. Qed.

HB.instance Definition _ := isKernel.Build _ _ T _ R
  (kscore mr) measurable_fun_kscore.

Import SCORE.

Let sfinite_kscore : exists k : (R.-fker T ~> _)^nat,
   forall x U, measurable U ->
     kscore mr x U = [the measure _ _ of mseries (k ^~ x) 0] U.
Proof.
rewrite /=.
exists (fun i => [the R.-fker _ ~> _ of mk mr i]) => /= t U mU.
rewrite /mseries /kscore/= mscoreE; case: ifPn => [/eqP U0|U0].
  by apply/esym/nneseries0 => i _; rewrite U0 measure0.
rewrite /mk /= /k /= mscoreE (negbTE U0).
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn `|floor (fine `|(r t)%:E|)|%N.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
apply/funext => n.
pose floor_r := widen_ord (leq_addl n `|floor `|r t| |.+1)
                          (Ordinal (ltnSn `|floor `|r t| |)).
rewrite big_mkord (bigD1 floor_r)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|r t|)) ?floor_ge0 ?floor_le.
  rewrite -addn1 natrD natr_absz.
  by rewrite (@ger0_norm _ (floor `|r t|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|r t|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|r t|)) ?floor_ge0.
- suff : (`|r t| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|r t|)) ?floor_ge0//.
  by rewrite ltr_int -floor_lt_int.
Qed.

HB.instance Definition _ :=
  @Kernel_isSFinite.Build _ _ _ _ _ (kscore mr) sfinite_kscore.

End kscore.

(* decomposition of ite into s-finite kernels *)
Module ITE.
Section ite.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Section kiteT.
Variable k : R.-ker X ~> Y.

Definition kiteT : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteT U : measurable U -> measurable_fun setT (kiteT ^~ U).
Proof.
move=> /= mcU; rewrite /kiteT.
rewrite (_ : (fun _ => _) = (fun x => if x.2 then k x.1 U
    else [the {measure set Y -> \bar R} of mzero] U)); last first.
  by apply/funext => -[t b]/=; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (k ^~ U) (fun=> mzero U)).
  exact/measurable_kernel.
exact: measurable_fun_cst.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  kiteT measurable_fun_kiteT.
End kiteT.

Section sfkiteT.
Variable k : R.-sfker X ~> Y.

Let sfinite_kiteT : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U ->
    kiteT k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k_ hk /=] := sfinite k.
exists (fun n => [the _.-ker _ ~> _ of kiteT (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteT//= /mzero//.
move=> [x b] U mU; rewrite /kiteT; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries nneseries0.
Qed.

#[export]
HB.instance Definition _ t := @Kernel_isSFinite_subdef.Build _ _ _ _ _
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
HB.instance Definition _ t := Kernel_isFinite.Build _ _ _ _ _
  (kiteT k) kiteT_uub.
End fkiteT.

Section kiteF.
Variable k : R.-ker X ~> Y.

Definition kiteF : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if ~~ xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteF U : measurable U -> measurable_fun setT (kiteF ^~ U).
Proof.
move=> /= mcU; rewrite /kiteF.
rewrite (_ : (fun x => _) = (fun x => if x.2 then
    [the measure _ _ of mzero] U else k x.1 U)); last first.
  by apply/funext => -[t b]/=; rewrite if_neg//; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (fun=> mzero U) (k ^~ U)).
  exact: measurable_fun_cst.
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
  forall x U, measurable U ->
    kiteF k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k_ hk /=] := sfinite k.
exists (fun n => [the _.-ker _ ~> _ of kiteF (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteF//= /mzero//.
move=> [x b] U mU; rewrite /kiteF; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries nneseries0.
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
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

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

Definition kite :=
  [the R.-sfker _ ~> _ of kdirac mf] \;
  [the R.-sfker _ ~> _ of kadd
    [the R.-sfker _ ~> T' of kiteT u1]
    [the R.-sfker _ ~> T' of kiteF u2] ].

End ite.

Section insn2.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Definition ret (f : X -> Y) (mf : measurable_fun setT f) :=
  locked [the R.-sfker X ~> Y of kdirac mf].

Definition sample (P : pprobability Y R) :=
  locked [the R.-pker X ~> Y of kprobability (measurable_fun_cst P)] .

Definition normalize (k : R.-sfker X ~> Y) P x :=
  locked [the probability _ _ of mnormalize k P x].

Definition ite (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y):=
  locked [the R.-sfker X ~> Y of kite k1 k2 mf].

End insn2.
Arguments ret {d d' X Y R f} mf.
Arguments sample {d d' X Y R}.

Section insn2_lemmas.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Lemma retE (f : X -> Y) (mf : measurable_fun setT f) x :
  ret mf x = \d_(f x) :> (_ -> \bar R).
Proof. by rewrite [in LHS]/ret; unlock. Qed.

Lemma sampleE (P : probability Y R) (x : X) : sample P x = P.
Proof. by rewrite [in LHS]/sample; unlock. Qed.

Lemma normalizeE (f : R.-sfker X ~> Y) P x U :
  normalize f P x U =
  if (f x [set: Y] == 0) || (f x [set: Y] == +oo) then P U
  else f x U * ((fine (f x [set: Y]))^-1)%:E.
Proof.
by rewrite /normalize; unlock => /=; rewrite /mnormalize; case: ifPn.
Qed.

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

Section insn3.
Variables (R : realType).
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).

Definition letin (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z) :=
  locked [the R.-sfker X ~> Z of l \; k].

End insn3.

Section insn3_lemmas.
Variables (R : realType).
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3).

Lemma letinE (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z) x U :
  letin l k x U = \int[l x]_y k (x, y) U.
Proof. by rewrite /letin; unlock. Qed.

End insn3_lemmas.

(* rewriting laws *)
Section letin_return.
Variables (d d' d3 : _) (R : realType) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3).

Lemma letin_kret (k : R.-sfker X ~> Y)
  (f : X * Y -> Z) (mf : measurable_fun setT f) x U :
  measurable U ->
  letin k (ret mf) x U = k x (curry f x @^-1` U).
Proof.
move=> mU; rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT//.
move/measurable_fun_prod1 : mf => /(_ x measurableT U mU).
by rewrite setTI.
Qed.

Lemma letin_retk
  (f : X -> Y) (mf : measurable_fun setT f)
  (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
  x U : measurable U ->
  letin (ret mf) k x U = k (x, f x) U.
Proof.
move=> mU; rewrite letinE retE integral_dirac ?indicT ?mul1e//.
have /measurable_fun_prod1 := measurable_kernel k _ mU.
exact.
Qed.

End letin_return.

Section insn1.
Variables (R : realType) (d : _) (X : measurableType d).

Definition score (f : X -> R) (mf : measurable_fun setT f) :=
  [the R.-sfker X ~> _ of kscore mf].

End insn1.

Section hard_constraint.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Definition fail :=
  letin (score (@measurable_fun_cst _ _ X _ setT (0%R : R)))
        (ret (@measurable_fun_cst _ _ _ Y setT point)).

Lemma failE x U : fail x U = 0.
Proof. by rewrite /fail letinE ge0_integral_mscale//= normr0 mul0e. Qed.

End hard_constraint.
Arguments fail {d d' X Y R}.

Module Notations.

Notation var1of2 := (@measurable_fun_fst _ _ _ _).
Notation var2of2 := (@measurable_fun_snd _ _ _ _).
Notation var1of3 := (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
                                         (@measurable_fun_fst _ _ _ _)).
Notation var2of3 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
                                         (@measurable_fun_fst _ _ _ _)).
Notation var3of3 := (@measurable_fun_snd _ _ _ _).

Notation mR := Real_sort__canonical__measure_Measurable.
Notation munit := Datatypes_unit__canonical__measure_Measurable.
Notation mbool := Datatypes_bool__canonical__measure_Measurable.

End Notations.

Section cst_fun.
Variables (R : realType) (d : _) (T : measurableType d).

Definition kr (r : R) := @measurable_fun_cst _ _ T _ setT r.
Definition k3 : measurable_fun _ _ := kr 3%:R.
Definition k10 : measurable_fun _ _ := kr 10%:R.
Definition ktt := @measurable_fun_cst _ _ T _ setT tt.

End cst_fun.
Arguments kr {R d T}.
Arguments k3 {R d T}.
Arguments k10 {R d T}.
Arguments ktt {d T}.

Section insn1_lemmas.
Import Notations.
Variables (R : realType) (d : _) (T : measurableType d).

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
  score (measurable_fun_comp mf var2of2)
    (x, r) (curry (snd \o fst) x @^-1` U) =
  (f r)%:E * \d_x.2 U.
Proof. by rewrite /score/= /mscale/= ger0_norm// f0. Qed.

Lemma score_score (f : R -> R) (g : R * unit -> R)
    (mf : measurable_fun setT f)
    (mg : measurable_fun setT g) :
  letin (score mf) (score mg) =
  score (measurable_funM mf (measurable_fun_prod2 tt mg)).
Proof.
apply/eq_sfkernel => x U.
rewrite {1}/letin; unlock.
by rewrite kcomp_scoreE/= /mscale/= diracE normrM muleA EFinM.
Qed.

Import Notations.

(* hard constraints to express score below 1 *)
Lemma score_fail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  score (kr r%:num) =
  letin (sample (bernoulli r1) : R.-pker T ~> _)
        (ite var2of2 (ret ktt) fail).
Proof.
apply/eq_sfkernel => x U.
rewrite letinE/= /sample; unlock.
rewrite integral_measure_add//= ge0_integral_mscale//= ge0_integral_mscale//=.
rewrite integral_dirac//= integral_dirac//= !indicT/= !mul1e.
by rewrite iteE//= iteE//= /mscale/= failE retE//= mule0 adde0 ger0_norm.
Qed.

End insn1_lemmas.

Section letin_ite.
Variables (R : realType) (d d2 d3 : _) (T : measurableType d)
  (T2 : measurableType d2) (Z : measurableType d3)
  (k1 k2 : R.-sfker T ~> Z) (u : R.-sfker [the measurableType _ of (T * Z)%type] ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin_iteT : f t -> letin (ite mf k1 k2) u t U = letin k1 u t U.
Proof.
move=> ftT.
rewrite !letinE/=.
apply eq_measure_integral => V mV _.
by rewrite iteE ftT.
Qed.

Lemma letin_iteF : ~~ f t -> letin (ite mf k1 k2) u t U = letin k2 u t U.
Proof.
move=> ftF.
rewrite !letinE/=.
apply eq_measure_integral => V mV _.
by rewrite iteE (negbTE ftF).
Qed.

End letin_ite.

Section letinC.
Variables (d d1 : _) (X : measurableType d) (Y : measurableType d1).
Variables (R : realType) (d' : _) (Z : measurableType d').

Import Notations.

Variables (t : R.-sfker Z ~> X)
          (t' : R.-sfker [the measurableType _ of (Z * Y)%type] ~> X)
          (tt' : forall y, t =1 fun z => t' (z, y))
          (u : R.-sfker Z ~> Y)
          (u' : R.-sfker [the measurableType _ of (Z * X)%type] ~> Y)
          (uu' : forall x, u =1 fun z => u' (z, x)).

Lemma letinC z A : measurable A ->
  letin t
  (letin u'
  (ret (measurable_fun_pair var2of3 var3of3))) z A =
  letin u
  (letin t'
  (ret (measurable_fun_pair var3of3 var2of3))) z A.
Proof.
move=> mA.
rewrite !letinE.
under eq_integral.
  move=> x _.
  rewrite letinE/= -uu'.
  under eq_integral do rewrite retE /=.
  over.
rewrite (sfinite_fubini  _ _ (fun x => \d_(x.1, x.2) A ))//; last 3 first.
  exact: sfinite_kernel_measure.
  exact: sfinite_kernel_measure.
  apply/EFin_measurable_fun => /=; rewrite (_ : (fun x => _) = mindic R mA)//.
  by apply/funext => -[].
apply eq_integral => y _.
by rewrite letinE/= -tt'; apply eq_integral => // x _; rewrite retE.
Qed.

End letinC.

(* sample programs *)

Section constants.
Variable R : realType.
Local Open Scope ring_scope.

Lemma onem27 : `1- (2 / 7%:R) = (5%:R / 7%:R)%:nng%:num :> R.
Proof. by apply/eqP; rewrite subr_eq/= -mulrDl -natrD divrr// unitfE. Qed.

Lemma p27 : (2 / 7%:R)%:nng%:num <= 1 :> R.
Proof. by rewrite /= lter_pdivr_mulr// mul1r ler_nat. Qed.

End constants.
Arguments p27 {R}.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for Poisson *)
Definition poisson k r : R := r ^+ k / k`!%:R^-1 * expR (- r).

Lemma poisson_ge0 k r : 0 <= r -> 0 <= poisson k r.
Proof.
move=> r0; rewrite /poisson mulr_ge0 ?expR_ge0//.
by rewrite mulr_ge0// exprn_ge0.
Qed.

Lemma poisson_gt0 k r : 0 < r -> 0 < poisson k.+1 r.
Proof.
move=> r0; rewrite /poisson mulr_gt0 ?expR_gt0//.
by rewrite divr_gt0// ?exprn_gt0// invr_gt0 ltr0n fact_gt0.
Qed.

Lemma mpoisson k : measurable_fun setT (poisson k).
Proof.
apply: measurable_funM => /=.
  apply: measurable_funM => //=; last exact: measurable_fun_cst.
  exact/measurable_fun_exprn/measurable_fun_id.
apply: measurable_fun_comp; last exact: measurable_fun_opp.
by apply: continuous_measurable_fun; exact: continuous_expR.
Qed.

Definition poisson3 := poisson 4 3. (* 0.168 *)
Definition poisson10 := poisson 4 10. (* 0.019 *)

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
apply: measurable_funM => /=; first exact: measurable_fun_id.
apply: measurable_fun_comp.
  by apply: continuous_measurable_fun; exact: continuous_expR.
apply: measurable_funM => /=; first exact: measurable_fun_opp.
exact: measurable_fun_cst.
Qed.

End exponential.

Lemma letin_sample_bernoulli (R : realType) (d d' : _) (T : measurableType d)
    (T' : measurableType d') (r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample (bernoulli r1)) u x y =
  r%:num%:E * u (x, true) y + (`1- (r%:num : R))%:E * u (x, false) y.
Proof.
rewrite letinE/= sampleE.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section sample_and_return.
Import Notations.
Variables (R : realType) (d : _) (T : measurableType d).

Definition sample_and_return : R.-sfker T ~> _ :=
  letin
    (sample (bernoulli p27)) (* T -> B *)
    (ret var2of2) (* T * B -> B *).

Lemma sample_and_returnE t U : sample_and_return t U =
  (2 / 7)%:E * \d_true U + (5 / 7)%:E * \d_false U.
Proof.
rewrite /sample_and_return.
rewrite letin_sample_bernoulli/=.
rewrite !retE.
by rewrite onem27.
Qed.

End sample_and_return.

(* trivial example *)
Section sample_and_branch.
Import Notations.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Definition sample_and_branch :
  R.-sfker T ~> mR R :=
  letin
    (sample (bernoulli p27)) (* T -> B *)
    (ite var2of2 (ret k3) (ret k10)).

Lemma sample_and_branchE t U : sample_and_branch t U =
  (2 / 7)%:E * \d_(3 : R) U +
  (5 / 7)%:E * \d_(10 : R) U.
Proof.
rewrite /sample_and_branch letin_sample_bernoulli/=.
rewrite !iteE/= !retE.
by rewrite onem27.
Qed.

End sample_and_branch.

Section staton_bus.
Import Notations.
Variables (R : realType) (d : _) (T : measurableType d) (h : R -> R).
Hypothesis mh : measurable_fun setT h.
Definition kstaton_bus : R.-sfker T ~> mbool :=
  letin (sample (bernoulli p27))
  (letin
    (letin (ite var2of2 (ret k3) (ret k10))
      (score (measurable_fun_comp mh var3of3)))
    (ret var2of3)).

Definition staton_bus := normalize kstaton_bus.

End staton_bus.

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)
Section staton_bus_poisson.
Import Notations.
Variables (R : realType) (d : _) (T : measurableType d).
Let poisson4 := @poisson R 4%N.
Let mpoisson4 := @mpoisson R 4%N.

Definition kstaton_bus_poisson : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mpoisson4.

Let kstaton_bus_poissonE t U : kstaton_bus_poisson t U =
  (2 / 7)%:E * (poisson4 3)%:E * \d_true U +
  (5 / 7)%:E * (poisson4 10)%:E * \d_false U.
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
  let N := ((2 / 7) * poisson4 3 +
            (5 / 7) * poisson4 10)%R in
  staton_bus mpoisson4 P t U =
  ((2 / 7)%:E * (poisson4 3)%:E * \d_true U +
   (5 / 7)%:E * (poisson4 10)%:E * \d_false U) * N^-1%:E.
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
Variables (R : realType) (d : _) (T : measurableType d).
Let exp1560 := @exp_density R (ratr (15%:Q / 60%:Q)).
Let mexp1560 := @mexp_density R (ratr (15%:Q / 60%:Q)).

(* 15/60 = 0.25 *)

Definition kstaton_bus_exponential : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mexp1560.

Let kstaton_bus_exponentialE t U : kstaton_bus_exponential t U =
  (2 / 7)%:E * (exp1560 3)%:E * \d_true U +
  (5 / 7)%:E * (exp1560 10)%:E * \d_false U.
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
  let N := ((2 / 7) * exp1560 3 +
            (5 / 7) * exp1560 10)%R in
  staton_bus mexp1560 P t U =
  ((2 / 7)%:E * (exp1560 3)%:E * \d_true U +
   (5 / 7)%:E * (exp1560 10)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite normalizeE /= !kstaton_bus_exponentialE !diracT !mule1 ifF //.
apply/negbTE; rewrite gt_eqF// lte_fin.
by rewrite addr_gt0// mulr_gt0//= ?divr_gt0// ?ltr0n// exp_density_gt0 ?ltr0n.
Qed.

End staton_bus_exponential.
