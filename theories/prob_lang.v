From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.

(******************************************************************************)
(*      Semantics of a programming language PPL using s-finite kernels        *)
(*                                                                            *)
(*       bernoulli r1 == Bernoulli probability                                *)
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
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO: PR *)
Lemma setT0 (T1 : pointedType) : setT != set0 :> set T1.
Proof. by apply/eqP => /seteqP[] /(_ point) /(_ Logic.I). Qed.

Definition swap (T1 T2 : Type) (x : T1 * T2) := (x.2, x.1).

Lemma measurable_fun_swap d d' (X : measurableType d) (Y : measurableType d') :
  measurable_fun [set: X * Y] (@swap X Y).
Proof.
by apply/prod_measurable_funP => /=; split;
  [exact: measurable_fun_snd|exact: measurable_fun_fst].
Qed.

Lemma onem1' (R : numDomainType) (p : R) : (p + `1- p = 1)%R.
Proof. by rewrite /onem addrCA subrr addr0. Qed.

Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :
  (0 <= `1-(p%:num))%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).

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
by rewrite /mscale/= !diracE !in_setT !mule1 -EFinD onem1'.
Qed.

HB.instance Definition _ := @isProbability.Build _ _ R mbernoulli mbernoulli_setT.

Definition bernoulli := [the probability _ _ of mbernoulli].

End bernoulli.

Section mscore.
Variables (d : _) (T : measurableType d).
Variables (R : realType) (f : T -> R).

Definition mscore t : {measure set _ -> \bar R} :=
  let p := NngNum (@normr_ge0 _ _ (`| f t |)%R) in
  [the measure _ _ of mscale p [the measure _ _ of dirac tt]].

Lemma mscoreE t U : mscore t U = if U == set0 then 0 else `| (f t)%:E |.
Proof.
rewrite /mscore/= /mscale/=; have [->|->] := set_unit U.
  by rewrite eqxx diracE in_set0 mule0.
by rewrite diracE in_setT mule1 (negbTE (setT0 _)) normr_id.
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
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition k (mr : measurable_fun setT r) (i : nat) : T -> set unit -> \bar R :=
  fun t U =>
    if i%:R%:E <= mscore r t U < i.+1%:R%:E then
      mscore r t U
    else
      0.

Hypothesis mr : measurable_fun setT r.

Lemma k0 i t : k mr i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k measure0; case: ifP. Qed.

Lemma k_ge0 i t B : 0 <= k mr i t B.
Proof. by rewrite /k; case: ifP. Qed.

Lemma k_sigma_additive i t : semi_sigma_additive (k mr i t).
Proof.
move=> /= F mF tF mUF; rewrite /k /=.
have [F0|] := eqVneq (\bigcup_n F n) set0.
  rewrite F0 measure0 (_ : (fun _ => _) = cst 0).
    by case: ifPn => _; exact: cvg_cst.
  apply/funext => k; rewrite big1// => n _.
  by move: F0 => /bigcup0P -> //; rewrite measure0; case: ifPn.
move=> UF0; move: (UF0).
move=> /eqP/bigcup0P/existsNP[m /not_implyP[_ /eqP Fm0]].
rewrite [in X in _ --> X]mscoreE (negbTE UF0).
rewrite -(cvg_shiftn m.+1)/=.
case: ifPn => ir.
  rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
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
rewrite big1//= => j jm.
rewrite mscoreE; have /eqP -> : F j == set0.
  have [/eqP//|Fjtt] := set_unit (F j).
  move/trivIsetP : tF => /(_ j m Logic.I Logic.I jm).
  by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fm0).
by rewrite eqxx; case: ifP.
Qed.

HB.instance Definition _ i t := isMeasure.Build _ _ _
  (k mr i t) (k0 i t) (k_ge0 i t) (@k_sigma_additive i t).

Lemma measurable_fun_k i U : measurable U -> measurable_fun setT (k mr i ^~ U).
Proof.
move=> /= mU; rewrite /k /=.
rewrite (_ : (fun x : T => _) = (fun x => if (i%:R)%:E <= x < (i.+1%:R)%:E then x else 0) \o
                             (mscore r ^~ U)) //.
apply: measurable_fun_comp => /=; last exact/measurable_fun_mscore.
pose A : _ -> \bar R := (fun x => x * (\1_(`[i%:R%:E, i.+1%:R%:E [%classic : set (\bar R)) x)%:E).
rewrite (_ : (fun x => _) = A); last first.
  apply/funext => x; rewrite /A; case: ifPn => ix.
    by rewrite indicE/= mem_set ?mule1//.
  by rewrite indicE/= memNset ?mule0// /= in_itv/=; exact/negP.
rewrite {}/A.
apply emeasurable_funM => /=; first exact: measurable_fun_id.
apply/EFin_measurable_fun.
have mi : measurable (`[(i%:R)%:E, (i.+1%:R)%:E[%classic : set (\bar R)).
  exact: emeasurable_itv.
by rewrite (_ : \1__ = mindic R mi).
Qed.

Definition mk i t := [the measure _ _ of k mr i t].

HB.instance Definition _ i :=
  isKernel.Build _ _ _ _ R (mk i) (measurable_fun_k i).

Lemma mk_uub (i : nat) : measure_fam_uub (mk i).
Proof.
exists i.+1%:R => /= t; rewrite /k mscoreE setT_unit.
rewrite (_ : [set tt] == set0 = false); last first.
  by apply/eqP => /seteqP[] /(_ tt) /(_ erefl).
by case: ifPn => // /andP[].
Qed.

HB.instance Definition _ i := @isFiniteFam.Build _ _ _ _ R (mk i) (mk_uub i).

End score.
End SCORE.

Section kscore.
Variables (R : realType) (d : _) (T : measurableType d) (r : T -> R).

Definition kscore (mr : measurable_fun setT r)
    : T -> {measure set _ -> \bar R} :=
  fun t => [the measure _ _ of mscore r t].

Variable (mr : measurable_fun setT r).

Let measurable_fun_kscore U : measurable U -> measurable_fun setT (kscore mr ^~ U).
Proof. by move=> /= _; exact: measurable_fun_mscore. Qed.

HB.instance Definition _ := isKernel.Build _ _ T _
  (*Datatypes_unit__canonical__measure_Measurable*) R (kscore mr) measurable_fun_kscore.

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
pose floor_r := widen_ord (leq_addl n `|floor `|r t| |.+1) (Ordinal (ltnSn `|floor `|r t| |)).
rewrite big_mkord (bigD1 floor_r)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|r t|)) ?floor_ge0 ?floor_le.
  by rewrite -addn1 natrD natr_absz (@ger0_norm _ (floor `|r t|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|r t|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|r t|)) ?floor_ge0.
- suff : (`|r t| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|r t|)) ?floor_ge0// ltr_int.
  by rewrite -floor_lt_int.
Qed.

HB.instance Definition _ := @isSFinite.Build _ _ _ _ _ (kscore mr) sfinite_kscore.

End kscore.

(* decomposition of ite into s-finite kernels *)
Module ITE.
Section kiteT.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-ker X ~> Y).

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

HB.instance Definition _ := isKernel.Build _ _ _ _ R kiteT measurable_fun_kiteT.
End kiteT.

Section fkiteT.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-fker X ~> Y).

Let kiteT_uub : measure_fam_uub (kiteT k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
exists M%:num => /= -[]; rewrite /kiteT => t [|]/=; first exact: hM.
by rewrite /= /mzero.
Qed.

HB.instance Definition _ t := isFiniteFam.Build _ _ _ _ R (kiteT k) kiteT_uub.
End fkiteT.

Section sfkiteT.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-sfker X ~> Y).

Let sfinite_kiteT : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    kiteT k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k_ hk /=] := sfinite k.
exists (fun n => [the _.-fker _ ~> _ of kiteT (k_ n)]) => b U mU.
rewrite /kiteT; case: ifPn => hb.
  rewrite /mseries hk//= /mseries.
  apply: eq_nneseries => n _.
  by rewrite /kiteT hb.
rewrite /= /mseries nneseries0// => n _.
by rewrite /kiteT (negbTE hb).
Qed.

HB.instance Definition _ t := @isSFinite.Build _ _ _ _ _ (kiteT k) sfinite_kiteT.

End sfkiteT.

Section kiteF.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-ker X ~> Y).

Definition kiteF : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if ~~ xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteF U : measurable U -> measurable_fun setT (kiteF ^~ U).
Proof.
move=> /= mcU; rewrite /kiteF.
rewrite (_ : (fun x => _) = (fun x => if x.2 then [the measure _ _ of mzero] U else k x.1 U)); last first.
  apply/funext => -[t b]/=.
  by rewrite if_neg//; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (fun=> mzero U) (k ^~ U)).
  exact: measurable_fun_cst.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R kiteF measurable_fun_kiteF.

End kiteF.

Section fkiteF.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-fker X ~> Y).

Let kiteF_uub : measure_fam_uub (kiteF k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
exists M%:num => /= -[]; rewrite /kiteF/= => t.
by case => //=; rewrite /mzero.
Qed.

HB.instance Definition _ := isFiniteFam.Build _ _ _ _ R (kiteF k) kiteF_uub.

End fkiteF.

Section sfkiteF.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-sfker X ~> Y).

Let sfinite_kiteF : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    kiteF k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k_ hk] := sfinite k.
exists (fun n => [the finite_kernel _ _ _ of kiteF (k_ n)]) => b U mU.
rewrite /= /kiteF /=; case: ifPn => hb.
  by rewrite /mseries hk//= /mseries/=.
by rewrite /= /mseries nneseries0.
Qed.

HB.instance Definition _ := @isSFinite.Build _ _ _ _ _ (kiteF k) sfinite_kiteF.

End sfkiteF.
End ITE.

Section ite.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

Definition mite (mf : measurable_fun setT f) : T -> set T' -> \bar R :=
  fun t => if f t then u1 t else u2 t.

Variables mf : measurable_fun setT f.

Let mite0 tb : mite mf tb set0 = 0.
Proof. by rewrite /mite; case: ifPn => //. Qed.

Let mite_ge0 tb (U : set _) : 0 <= mite mf tb U.
Proof. by rewrite /mite; case: ifPn => //. Qed.

Let mite_sigma_additive tb : semi_sigma_additive (mite mf tb).
Proof.
by rewrite /mite; case: ifPn => ftb; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ tb := isMeasure.Build _ _ _ (mite mf tb)
  (mite0 tb) (mite_ge0 tb) (@mite_sigma_additive tb).

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

Definition sample (P : probability Y R) :=
  locked [the R.-pker X ~> Y of kprobability P] .

Definition pnormalize (k : R.-sfker X ~> Y) P :=
  locked [the R.-pker X ~> Y of knormalize k P].

Definition dnormalize t (k : R.-sfker X ~> Y) P :=
  locked [the probability _ _ of mnormalize k P t].

Definition ite (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y):=
  locked [the R.-sfker X ~> Y of kite k1 k2 mf].

End insn2.
Arguments sample {d d' X Y R}.

Section insn2_lemmas.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Lemma retE (f : X -> Y) (mf : measurable_fun setT f) x :
  ret R mf x = \d_(f x) :> (_ -> _).
Proof. by rewrite [in LHS]/ret; unlock. Qed.

Lemma sampleE (P : probability Y R) (x : X) : sample P x = P.
Proof. by rewrite [in LHS]/sample; unlock. Qed.

Lemma pnormalizeE (f : R.-sfker X ~> Y) P x U :
  pnormalize f P x U =
  if (f x [set: Y] == 0) || (f x [set: Y] == +oo) then P U
  else f x U * ((fine (f x [set: Y]))^-1)%:E.
Proof.
by rewrite /pnormalize; unlock => /=; rewrite /mnormalize; case: ifPn.
Qed.

Lemma dnormalizeE (f : R.-sfker X ~> Y) P x U :
  dnormalize x f P U =
  if (f x [set: Y] == 0) || (f x [set: Y] == +oo) then P U
  else f x U * ((fine (f x [set: Y]))^-1)%:E.
Proof.
by rewrite /dnormalize; unlock => /=; rewrite /mnormalize; case: ifPn.
Qed.

Lemma iteE (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y) x :
  ite mf k1 k2 x = if f x then k1 x else k2 x.
Proof.
apply/eq_measure/funext => U.
rewrite /ite; unlock => /=.
rewrite /kcomp/=.
rewrite integral_dirac//=.
rewrite indicT.
rewrite mul1e.
rewrite -/(measure_add (ITE.kiteT k1 (x, f x))
                       (ITE.kiteF k2 (x, f x))).
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

(* a few laws *)

Section letin_return.
Variables (d d' d3 : _) (R : realType) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3).

Lemma letin_kret (k : R.-sfker X ~> Y)
  (f : _ -> Z) (mf : measurable_fun setT f) x U :
  measurable U ->
  letin k (ret R mf) x U = k x (curry f x @^-1` U).
Proof.
move=> mU.
rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT//.
move/measurable_fun_prod1 : mf => /(_ x)/(_ measurableT U mU).
by rewrite setTI.
Qed.

Lemma letin_retk (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  (f : _ -> Y) (mf : measurable_fun setT f) :
  forall x U, measurable U -> letin (ret R mf) k x U = k (x, f x) U.
Proof.
move=> x U mU.
rewrite letinE retE integral_dirac//.
  by rewrite indicE mem_set// mul1e.
have /measurable_fun_prod1 := measurable_kernel k _ mU.
exact.
Qed.

End letin_return.

Section insn1.
Variables (R : realType) (d : _) (X : measurableType d).

Definition score (f : X -> R) (mf : measurable_fun setT f) :=
  [the R.-sfker X ~> _ of kscore mf].

End insn1.

Section insn1_lemmas.
Variables (R : realType) (d : _) (T : measurableType d).

Lemma scoreE' d' (T' : measurableType d') d2 (T2 : measurableType d2) (U : set T')
    (g : R.-sfker [the measurableType _ of (T2 * unit)%type] ~> T') r fh (mh : measurable_fun setT fh) :
  (score mh \; g) r U =
  g (r, tt) U * `|fh r|%:E.
Proof.
rewrite [in LHS]/score [in LHS]/=.
rewrite /kcomp.
rewrite /kscore.
rewrite [in LHS]/=.
rewrite ge0_integral_mscale//=.
rewrite integral_dirac// normr_id muleC.
by rewrite indicE in_setT mul1e.
Qed.

Lemma scoreE (t : T) (U : set bool) (n : nat) (b : bool)
    (f : R -> R)
    (f0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (mf : measurable_fun setT f) :
  score (measurable_fun_comp mf (@measurable_fun_snd _ _ _ _))
    (t, b, n%:R) (curry (snd \o fst) (t, b) @^-1` U) =
  (f n%:R)%:E * \d_b U.
Proof.
transitivity (letin (
  score (measurable_fun_comp mf (measurable_fun_snd (T2:=Real_sort__canonical__measure_Measurable R)))
  ) (
 ret R (@measurable_fun_id _ _ _)
) (t, b, n%:R) (curry (snd \o fst) (t, b) @^-1` U)).
  rewrite letin_kret//.
  rewrite /curry/=.
  rewrite preimage_cst.
  by case: ifPn => //.
rewrite /letin.
unlock.
rewrite scoreE'//.
rewrite retE.
by rewrite ger0_norm// ?f0//= muleC.
Qed.

(* example of property *)
Lemma score_score (f : R -> R) (g : R * unit -> R) (mf : measurable_fun setT f)
    (mg : measurable_fun setT g) x U :
  letin (score mf) (score mg) x U =
  if U == set0 then 0 else `|f x|%:E * `|g (x, tt)|%:E.
Proof.
rewrite {1}/letin.
unlock.
rewrite scoreE'//=.
rewrite /mscale/= diracE !normr_id.
have [->|->]:= set_unit U.
  by rewrite eqxx in_set0 mule0 mul0e.
by rewrite in_setT mule1 (negbTE (setT0 _)) muleC.
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

Require Import exp.

Definition poisson (R : realType) (r : R) (k : nat) := (r ^+ k / k%:R^-1 * expR (- r))%R.

Definition poisson3 (R : realType) := poisson (3%:R : R) 4. (* 0.168 *)
Definition poisson10 (R : realType) := poisson (10%:R : R) 4. (* 0.019 *)

Lemma poisson_ge0 (R : realType) (r : R) k : (0 <= r)%R -> (0 <= poisson r k)%R.
Proof.
move=> r0; rewrite /poisson mulr_ge0//.
  by rewrite mulr_ge0// exprn_ge0//.
by rewrite ltW// expR_gt0.
Qed.

Lemma poisson_gt0 (R : realType) (r : R) k : (0 < r)%R -> (0 < poisson r k.+1)%R.
Proof.
move=> r0; rewrite /poisson mulr_gt0//.
  by rewrite mulr_gt0// exprn_gt0.
by rewrite expR_gt0.
Qed.

Lemma mpoisson (R : realType) k : measurable_fun setT (@poisson R ^~ k).
Proof.
apply: measurable_funM => /=.
  apply: measurable_funM => //=; last exact: measurable_fun_cst.
  exact/measurable_fun_exprn/measurable_fun_id.
apply: measurable_fun_comp.
  apply: continuous_measurable_fun.
  exact: continuous_expR.
apply: continuous_measurable_fun.
by have := (@opp_continuous R [the normedModType R of R^o]).
Qed.

Section cst_fun.
Variables (R : realType) (d : _) (T : measurableType d).

Definition kn (n : nat) := @measurable_fun_cst _ _ T _ setT (n%:R : R).
Definition k3 : measurable_fun _ _ := kn 3.
Definition k10 : measurable_fun _ _ := kn 10.

End cst_fun.
Arguments k3 {R d T}.
Arguments k10 {R d T}.

Module Notations.

Notation var1_of2 := (@measurable_fun_fst _ _ _ _).
Notation var2_of2 := (@measurable_fun_snd _ _ _ _).
Notation var1_of3 := (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
                                          (@measurable_fun_fst _ _ _ _)).
Notation var2_of3 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
                                          (@measurable_fun_fst _ _ _ _)).
Notation var3_of3 := (@measurable_fun_snd _ _ _ _).

End Notations.

Lemma letin_sample_bernoulli (R : realType) (d d' : _) (T : measurableType d)
    (T' : measurableType d') (r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample (bernoulli r1)) u x y =
  r%:num%:E * u (x, true) y + (`1- (r%:num : R))%:E * u (x, false) y.
Proof.
rewrite letinE/= sampleE.
rewrite ge0_integral_measure_sum//.
rewrite 2!big_ord_recl/= big_ord0 adde0/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//=.
by rewrite indicE in_setT mul1e indicE in_setT mul1e.
Qed.

Section sample_and_return.
Variables (R : realType) (d : _) (T : measurableType d).

Import Notations.

Definition sample_and_return : R.-sfker T ~> _ :=
  letin
    (sample (bernoulli p27)) (* T -> B *)
    (ret R var2_of2) (* T * B -> B *).

Lemma sample_and_returnE t U : sample_and_return t U =
  (2 / 7%:R)%:E * \d_true U + (5%:R / 7%:R)%:E * \d_false U.
Proof.
rewrite /sample_and_return.
rewrite letin_sample_bernoulli/=.
rewrite !retE.
by rewrite onem27.
Qed.

End sample_and_return.

Section sample_and_score.
Variables (R : realType) (d : _) (T : measurableType d).

Definition sample_and_score  : R.-sfker T ~> _ :=
  letin
    (sample (bernoulli p27)) (* T -> B *)
    (score (measurable_fun_cst (1%R : R))).

End sample_and_score.

Section sample_and_branch.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Let mR := Real_sort__canonical__measure_Measurable R.

Import Notations.

Definition sample_and_branch :
  R.-sfker T ~> [the measurableType default_measure_display of mR] :=
  letin
    (sample (bernoulli p27)) (* T -> B *)
    (ite var2_of2
       (ret R k3)
       (ret R k10)).

Lemma sample_and_branchE t U : sample_and_branch t U =
  (2 / 7%:R)%:E * \d_(3%:R : R) U +
  (5%:R / 7%:R)%:E * \d_(10%:R : R) U.
Proof.
rewrite /sample_and_branch letin_sample_bernoulli/=.
rewrite !iteE/= !retE.
by rewrite onem27.
Qed.

End sample_and_branch.

Section staton_bus.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Variable P : probability mbool R.

Import Notations.

Definition staton_bus_annotated : R.-pker T ~> mbool :=
  pnormalize (letin
    (sample (bernoulli p27) : _.-sfker T ~> mbool)
    (letin
      (letin
        (ite var2_of2
           (ret R k3)
           (ret R k10)
         : _.-sfker [the measurableType _ of (T * bool)%type] ~> mR)
        (score (measurable_fun_comp (@mpoisson R 4) var3_of3)
         : _.-sfker [the measurableType _ of (T * bool* mR)%type] ~> munit)
       : _.-sfker [the measurableType _ of (T * bool)%type] ~> munit)
      (ret R var2_of3
       : _.-sfker [the measurableType _ of (T * bool * munit)%type] ~> mbool)
     : _.-sfker [the measurableType _ of (T * bool)%type] ~> mbool)) P.

Let staton_bus' : R.-sfker T ~> _ :=
  (letin (sample (bernoulli p27))
  (letin
    (letin (ite var2_of2
         (ret R k3)
         (ret R k10))
     (score (measurable_fun_comp (@mpoisson R 4) var3_of3)))
    (ret R var2_of3))).

(* true -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)
(* false -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)

Let staton_bus'E t U : staton_bus' t U =
  (2 / 7%:R)%:E * (poisson 3%:R 4)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson 10%:R 4)%:E * \d_false U.
Proof.
rewrite /staton_bus'.
rewrite letin_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _).
- rewrite letin_kret//.
  rewrite letin_iteT//.
  rewrite letin_retk//.
  by rewrite scoreE// => r r0; exact: poisson_ge0.
- by rewrite onem27.
  rewrite letin_kret//.
  rewrite letin_iteF//.
  rewrite letin_retk//.
  by rewrite scoreE// => r r0; exact: poisson_ge0.
Qed.

Definition staton_bus : R.-pker T ~> mbool := pnormalize staton_bus' P.

Lemma staton_busE t U :
  let N := ((2 / 7%:R)    * poisson 3%:R 4 +
            (5%:R / 7%:R) * poisson 10%:R 4)%R in
  staton_bus t U =
  ((2 / 7%:R)%:E    * (poisson 3%:R 4)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (poisson 10%:R 4)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite pnormalizeE /=.
rewrite !staton_bus'E.
rewrite diracE mem_set// mule1.
rewrite diracE mem_set// mule1.
rewrite ifF //.
apply/negbTE.
by rewrite gt_eqF// lte_fin addr_gt0// mulr_gt0//= poisson_gt0.
Qed.

Definition dstaton_bus (t : T) : probability mbool R := dnormalize t staton_bus' P.

Lemma dstaton_busE t U :
  let N := ((2 / 7%:R)    * poisson 3%:R 4 +
            (5%:R / 7%:R) * poisson 10%:R 4)%R in
  dstaton_bus t U =
  ((2 / 7%:R)%:E    * (poisson 3%:R 4)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (poisson 10%:R 4)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite dnormalizeE /=.
rewrite !staton_bus'E.
rewrite diracE mem_set// mule1.
rewrite diracE mem_set// mule1.
rewrite ifF //.
apply/negbTE.
by rewrite gt_eqF// lte_fin addr_gt0// mulr_gt0//= poisson_gt0.
Qed.

End staton_bus.

(* TODO: move *)
Section measurable_fun_pair.
Variables (d d' d3 : _) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3).

Lemma measurable_fun_pair (f : X -> Y) (g : X -> Z) :
  measurable_fun setT f ->
  measurable_fun setT g ->
  measurable_fun setT (fun x => (f x, g x)).
Proof.
by move=> mf mg; apply/prod_measurable_funP.
Qed.

End measurable_fun_pair.

(* TODO: move *)
Lemma finite_kernel_measure (d d' : _) (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-fker X ~> Y) (x : X) :
  finite_measure (k x).
Proof.
have [r k_r] := measure_uub k.
by rewrite /finite_measure (@lt_trans _ _ r%:E) ?ltey.
Qed.

Lemma sfinite_kernel_measure (d d' : _) (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-sfker X ~> Y) (x : X) :
  sfinite_measure (k x).
Proof.
have [k_ k_E] := sfinite k.
exists (fun n => k_ n x); split; last by move=> A mA; rewrite k_E.
by move=> n; exact: finite_kernel_measure.
Qed.

Section letinC.
Variables (d d1 : _) (X : measurableType d) (Y : measurableType d1).
Variables (R : realType) (d' : _) (Z : measurableType d').

Notation var2_of3 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
                                          (@measurable_fun_fst _ _ _ _)).
Notation var3_of3 := (@measurable_fun_snd _ _ _ _).

Variables (t : R.-sfker Z ~> X)
          (t' : R.-sfker [the measurableType _ of (Z * Y)%type] ~> X)
          (tt' : forall y, t =1 fun z => t' (z, y))
          (u : R.-sfker Z ~> Y)
          (u' : R.-sfker [the measurableType _ of (Z * X)%type] ~> Y)
          (uu' : forall x, u =1 fun z => u' (z, x)).

Lemma letinC z A : measurable A ->
  letin t
  (letin u'
  (ret R (measurable_fun_pair var2_of3 var3_of3))) z A =
  letin u
  (letin t'
  (ret R (measurable_fun_pair var3_of3 var2_of3))) z A.
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

Section dist_salgebra_instance.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables p0 : probability T R.

Definition prob_pointed := Pointed.Class
  (Choice.Class gen_eqMixin (Choice.Class gen_eqMixin gen_choiceMixin)) p0.

Canonical probability_eqType := EqType (probability T R) prob_pointed.
Canonical probability_choiceType := ChoiceType (probability T R) prob_pointed.
Canonical probability_ptType := PointedType (probability T R) prob_pointed.

Definition mset (U : set T) (r : R) := [set mu : probability T R | mu U < r%:E].

Definition pset : set (set (probability T R)) :=
  [set mset U r | r in `[0%R,1%R]%classic & U in @measurable d T].

Definition sset := [the measurableType pset.-sigma of salgebraType pset].

End dist_salgebra_instance.
