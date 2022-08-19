From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.

(******************************************************************************)
(*                  Semantics of a PPL using s-finite kernels                 *)
(*                                                                            *)
(*          bernoulli ==                                                      *)
(*              score ==                                                      *)
(* ite_true/ite_false ==                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition onem (R : numDomainType) (p : R) := (1 - p)%R.

Lemma onem1 (R : numDomainType) (p : R) : (p + onem p = 1)%R.
Proof. by rewrite /onem addrCA subrr addr0. Qed.

Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :
  (0 <= onem p%:num)%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition bernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac true]]
    [the measure _ _ of mscale (onem_nonneg p1) [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli.

Local Close Scope ring_scope.

Lemma bernoulli_setT : bernoulli [set: _] = 1.
Proof.
rewrite /bernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracE !in_setT !mule1 -EFinD onem1.
Qed.

HB.instance Definition _ := @isProbability.Build _ _ R bernoulli bernoulli_setT.

End bernoulli.

Section score_measure.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition score (t : T) (U : set unit) : \bar R :=
  if U == set0 then 0 else `| (r t)%:E |.

Let score0 t : score t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /score eqxx. Qed.

Let score_ge0 t U : 0 <= score t U.
Proof. by rewrite /score; case: ifP. Qed.

Let score_sigma_additive t : semi_sigma_additive (score t).
Proof.
move=> /= F mF tF mUF; rewrite /score; case: ifPn => [/eqP/bigcup0P F0|].
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
  (score t) (score0 t) (score_ge0 t) (@score_sigma_additive t).

End score_measure.

(* decomposition of score into finite kernels *)
Module SCORE.
Section score.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition k_ (mr : measurable_fun setT r) (i : nat) : T -> set unit -> \bar R :=
  fun t U =>
    if i%:R%:E <= score r t U < i.+1%:R%:E then
      score r t U
    else
      0.

Hypothesis mr : measurable_fun setT r.

Lemma k_0 i (t : T) : k_ mr i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k_ measure0; case: ifP. Qed.

Lemma k_ge0 i (t : T) B : 0 <= k_ mr i t B.
Proof. by rewrite /k_; case: ifP. Qed.

Lemma k_sigma_additive i (t : T) : semi_sigma_additive (k_ mr i t).
Proof.
move=> /= F mF tF mUF.
rewrite /k_ /=.
have [F0|] := eqVneq (\bigcup_n F n) set0.
  rewrite [in X in _ --> X]/score F0 eqxx.
  rewrite (_ : (fun _ => _) = cst 0).
    by case: ifPn => _; exact: cvg_cst.
  apply/funext => k; rewrite big1// => n _.
  move : F0 => /bigcup0P F0.
  by rewrite /score F0// eqxx; case: ifP.
move=> UF0; move: (UF0).
move=> /eqP/bigcup0P/existsNP[k /not_implyP[_ /eqP Fk0]].
rewrite [in X in _ --> X]/score (negbTE UF0).
rewrite -(cvg_shiftn k.+1)/=.
case: ifPn => ir.
  rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
  apply/funext => n.
  rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
  rewrite [in X in X + _]/score (negbTE Fk0) ir big1 ?adde0// => /= j jk.
  rewrite /score.
  have /eqP Fj0 : F j == set0.
    have [/eqP//|Fjtt] := set_unit (F j).
    move/trivIsetP : tF => /(_ j k Logic.I Logic.I jk).
    by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fk0).
  rewrite Fj0 eqxx.
  by case: ifP.
rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
rewrite [in X in if X then _ else _]/score (negbTE Fk0) (negbTE ir) add0e.
rewrite big1//= => j jk.
rewrite /score.
have /eqP Fj0 : F j == set0.
  have [/eqP//|Fjtt] := set_unit (F j).
  move/trivIsetP : tF => /(_ j k Logic.I Logic.I jk).
  by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fk0).
rewrite Fj0 eqxx.
by case: ifP.
Qed.

HB.instance Definition _ (i : nat) (t : T) := isMeasure.Build _ _ _
  (k_ mr i t) (k_0 i t) (k_ge0 i t) (@k_sigma_additive i t).

Lemma measurable_fun_k_ (i : nat) U : measurable U -> measurable_fun setT (k_ mr i ^~ U).
Proof.
move=> /= mU.
rewrite /k_ /=.
rewrite (_ : (fun x : T => _) = (fun x => if (i%:R)%:E <= x < (i.+1%:R)%:E then x else 0) \o (fun x => score r x U)) //.
apply: measurable_fun_comp; last first.
  rewrite /score.
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

Definition mk_ i (t : T) := [the measure _ _ of k_ mr i t].

HB.instance Definition _ (i : nat) :=
  isKernel.Build _ _ _ _ R (mk_ i) (measurable_fun_k_ i).

Lemma mk_uub (i : nat) : measure_fam_uub (mk_ i).
Proof.
exists i.+1%:R => /= t.
rewrite /k_ /score setT_unit.
rewrite (_ : [set tt] == set0 = false); last first.
  by apply/eqP => /seteqP[] /(_ tt) /(_ erefl).
by case: ifPn => // /andP[].
Qed.

HB.instance Definition _ (i : nat) :=
  @isFiniteKernel.Build _ _ _ _ R (mk_ i) (mk_uub i).

End score.
End SCORE.

Section score_kernel.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition kernel_score (mr : measurable_fun setT r)
    : T -> {measure set Datatypes_unit__canonical__measure_Measurable -> \bar R} :=
  fun t => [the measure _ _ of score r t].

Variable (mr : measurable_fun setT r).

Let measurable_fun_score U : measurable U -> measurable_fun setT (kernel_score mr ^~ U).
Proof.
move=> /= mU; rewrite /score.
have [U0|U0] := eqVneq U set0; first exact: measurable_fun_cst.
by apply: measurable_fun_comp => //; exact/EFin_measurable_fun.
Qed.

HB.instance Definition _ := isKernel.Build _ _ T _
  (*Datatypes_unit__canonical__measure_Measurable*) R (kernel_score mr) measurable_fun_score.
End score_kernel.

Section score_sfinite_kernel.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R) (mr : measurable_fun setT r).

Import SCORE.

Let sfinite_score : exists k_ : (R.-fker T ~> _)^nat,
   forall x U, measurable U ->
     kernel_score mr x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
rewrite /=.
exists (fun i => [the finite_kernel _ _ _ of mk_ mr i]) => /= r' U mU.
rewrite /mseries /score; case: ifPn => [/eqP U0|U0].
  by apply/esym/nneseries0 => i _; rewrite U0 measure0.
rewrite /mk_ /= /k_ /= /score (negbTE U0).
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
  (kernel_score mr) sfinite_score.

End score_sfinite_kernel.

(* decomposition of if-then-else *)
Module ITE.
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

Lemma ite_true_uub : measure_fam_uub (ite_true u1).
Proof.
have /measure_fam_uubP[M hM] := kernel_uub u1.
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

Let sfinite_ite_true : exists k_ : (R.-fker _ ~> _)^nat,
  forall x U, measurable U ->
    ite_true u1 x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [k hk /=] := sfinite u1.
rewrite /ite_true.
exists (fun n => [the _.-fker _ ~> _ of ite_true (k n)]) => b U mU.
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

Let measurable_ite_false U : measurable U -> measurable_fun setT (ite_false ^~ U).
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

Let ite_false_uub : measure_fam_uub (ite_false u2).
Proof.
have /measure_fam_uubP[M hM] := kernel_uub u2.
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

Let sfinite_ite_false : exists k_ : (R.-fker _ ~> _)^nat,
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
End ITE.

Section ite.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

Definition ite (mf : measurable_fun setT f) : T -> set T' -> \bar R :=
  fun t => if f t then u1 t else u2 t.

Variables mf : measurable_fun setT f.

Lemma ite0 tb : ite mf tb set0 = 0.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_ge0 tb (U : set _) : 0 <= ite mf tb U.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_sigma_additive tb : semi_sigma_additive (ite mf tb).
Proof.
rewrite /ite.
case: ifPn => ftb.
  exact: measure_semi_sigma_additive.
exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ tb := isMeasure.Build _ _ _ (ite mf tb)
  (ite0 tb) (ite_ge0 tb) (@ite_sigma_additive tb).

Import ITE.

Let ite' : R.-sfker
  [the measurableType _ of (T * bool)%type] ~> T' :=
  [the R.-sfker _ ~> _ of add_of_kernels
    [the R.-sfker _ ~> T' of ite_true u1]
    [the R.-sfker _ ~> T' of ite_false u2] ].

Definition mite := [the sfinite_kernel _ _ _ of kernel_mfun R mf] \; ite'.

End ite.

Section normalize.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d')
          (R : realType) (f : R.-sfker T ~> T') (Pdef : probability T' R).

Definition Normalize := [the R.-pker T ~> T' of normalize_kernel f Pdef].

Lemma NormalizeE x U : Normalize x U = normalize_kernel f Pdef x U.
Proof.
by [].
Qed.

End normalize.

Section bernoulli27.
Variable R : realType.
Local Open Scope ring_scope.
Definition twoseven : {nonneg R} := (2%:R / 7%:R)%:nng.
Definition fiveseven : {nonneg R} := (5%:R / 7%:R)%:nng.

Lemma onem_twoseven : onem (2 / 7) = fiveseven%:num.
Proof. by apply/eqP; rewrite subr_eq/= -mulrDl -natrD divrr// unitfE. Qed.

Lemma twoseven_proof : (twoseven%:num <= 1 :> R)%R.
Proof. by rewrite /= lter_pdivr_mulr// mul1r ler_nat. Qed.

Definition bernoulli27 : set _ -> \bar R := bernoulli twoseven_proof.

End bernoulli27.

Section insn.
Variables (R : realType).

Definition letin (d d' d3 : _)
  (X : measurableType d) (Y : measurableType d') (Z : measurableType d3)
  (l : R.-sfker X ~> Y)
  (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  : R.-sfker X ~> Z :=
  [the sfinite_kernel _ _ _ of l \; k].

Lemma letinE (d d' d3 : _)
  (X : measurableType d) (Y : measurableType d') (Z : measurableType d3)
  (l : R.-sfker X ~> Y)
  (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  : forall x U, letin l k x U = \int[l x]_y k (x, y) U.
Proof.
by [].
Qed.

Definition Return (d d' : _) (T : measurableType d) (T' : measurableType d')
  (f : T -> T') (mf : measurable_fun setT f) : R.-sfker T ~> T' :=
  [the sfinite_kernel _ _ _ of @kernel_mfun _ _ T T' R f mf].

Definition sample_bernoulli27 (d : _) (T : measurableType d) :=
  [the sfinite_kernel T _ _ of
   kernel_probability [the probability _ _ of bernoulli27 R]] .

(* NB: score r = observe 0 from exp r,
       the density of the exponential distribution exp(r) at 0 is r = r e^(-r * 0)
       more generally, score (r e^(-r * t)) = observe t from exp(r),
       score (f(r)) = observe r from p where f is the density of p *)
Definition Score (d : _) (T : measurableType d) (r : T -> R) (mr : measurable_fun setT r) :
    R.-sfker T ~> Datatypes_unit__canonical__measure_Measurable :=
  [the sfinite_kernel _ _ R of @kernel_score R _ _ r mr].

Lemma ScoreE (d : _) (T : measurableType d) (t : T) (U : set bool) (n : nat)  (b : bool)
  (f : R -> R) (f0 : forall r, (0 <= r)%R -> (0 <= f r)%R) (mf : measurable_fun setT f) :
  Score (measurable_fun_comp mf (@measurable_fun_snd _ _ _ _))
    (t, b, cst n%:R (t, b))
    ((fun y : unit => (snd \o fst) (t, b, y)) @^-1` U) =
  (f n%:R)%:E * \d_b U.
Proof.
rewrite /Score/= /score/= diracE.
have [U0|U0] := set_unit ((fun=> b) @^-1` U).
- rewrite U0 eqxx memNset ?mule0//.
  move=> Ub.
  move: U0.
  move/seteqP => [/(_ tt)] /=.
  by move/(_ Ub).
- rewrite U0 setT_unit ifF//; last first.
    by apply/negbTE/negP => /eqP/seteqP[/(_ tt erefl)].
  rewrite /= mem_set//; last first.
    by move: U0 => /seteqP[_]/(_ tt)/=; exact.
  by rewrite mule1 ger0_norm// f0.
Qed.

Definition Ite (d d' : _) (T : measurableType d) (T' : measurableType d')
    (f : T -> bool) (mf : measurable_fun setT f)
    (u1 u2 : R.-sfker T ~> T')
    : R.-sfker T ~> T' :=
  [the R.-sfker _ ~> _ of mite u1 u2 mf].

Lemma IteE (d d' : _) (T : measurableType d) (T' : measurableType d')
    (f : T -> bool) (mf : measurable_fun setT f)
    (u1 u2 : R.-sfker T ~> T') tb U :
  Ite mf u1 u2 tb U = ite u1 u2 mf tb U.
Proof.
rewrite /= /kcomp /ite.
rewrite integral_dirac//=.
rewrite indicT /cst.
rewrite mul1e.
rewrite -/(measure_add (ITE.ite_true u1 (tb, f tb))
                       (ITE.ite_false u2 (tb, f tb))).
rewrite measure_addE.
rewrite /ITE.ite_true /ITE.ite_false/=.
case: (ifPn (f tb)) => /=.
  by rewrite /mzero adde0.
by rewrite /mzero add0e.
Qed.

End insn.

(* a few laws *)

Section letin_return.
Variables (d d' d3 : _) (R : realType) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3).

Lemma letin_ureturn (u : R.-sfker X ~> Y)
  (f : _ -> Z) (mf : measurable_fun setT f) :
  forall x U, measurable U -> letin u (Return R mf) x U = u x ((fun y => f (x, y)) @^-1` U).
Proof.
move=> x U mU.
rewrite /letin/= /kcomp/= integral_indic// ?setIT//.
move/measurable_fun_prod1 : mf => /(_ x)/(_ measurableT U mU).
by rewrite setTI.
Qed.

Lemma letin_returnu
  (u : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  (f : _ -> Y) (mf : measurable_fun setT f) :
  forall x U, measurable U -> letin (Return R mf) u x U = u (x, f x) U.
Proof.
move=> x U mU.
rewrite /letin/= /kcomp/= integral_dirac//.
  by rewrite indicE mem_set// mul1e.
have /measurable_fun_prod1 := measurable_kernel u _ mU.
exact.
Qed.

End letin_return.

Section letin_ite.
Variables (R : realType) (d d2 d3 : _) (T : measurableType d)
  (T2 : measurableType d2) (T3 : measurableType d3)
  (u1 u2 : R.-sfker T ~> T3) (u : R.-sfker [the measurableType _ of (T * T3)%type] ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin_ite_true : f t -> letin (Ite mf u1 u2) u t U = letin u1 u t U.
Proof.
move=> ftT.
rewrite /letin/= /kcomp.
apply eq_measure_integral => V mV _.
by rewrite IteE /ite ftT.
Qed.

Lemma letin_ite_false : ~~ f t -> letin (Ite mf u1 u2) u t U = letin u2 u t U.
Proof.
move=> ftF.
rewrite /letin/= /kcomp.
apply eq_measure_integral => V mV _.
by rewrite IteE/= /ite (negbTE ftF).
Qed.

End letin_ite.

(* sample programs *)

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

Lemma letin_sample_bernoulli27 (R : realType) (d d' : _) (T : measurableType d)
    (T' : measurableType d')
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample_bernoulli27 R T) u x y =
  (2 / 7)%:E * u (x, true) y + (5 / 7)%:E * u (x, false) y.
Proof.
rewrite {1}/letin/= {1}/kcomp/=.
rewrite ge0_integral_measure_sum//.
rewrite 2!big_ord_recl/= big_ord0 adde0/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//=.
rewrite indicE in_setT mul1e indicE in_setT mul1e.
by rewrite onem_twoseven.
Qed.

Section sample_and_return.
Variables (R : realType) (d : _) (T : measurableType d).

Definition sample_and_return : R.-sfker T ~> _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Return R (@measurable_fun_snd _ _ _ _)) (* T * B -> B *).

Lemma sample_and_returnE t U : sample_and_return t U =
  (twoseven R)%:num%:E * \d_true U +
  (fiveseven R)%:num%:E * \d_false U.
Proof. by rewrite letin_sample_bernoulli27. Qed.

End sample_and_return.

Section sample_and_score.
Variables (R : realType) (d : _) (T : measurableType d).

Definition sample_and_score  : R.-sfker T ~> _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Score (measurable_fun_cst (1%R : R))).

End sample_and_score.

Section sample_and_branch.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Definition sample_and_branch :
  R.-sfker T ~> [the measurableType default_measure_display of Real_sort__canonical__measure_Measurable R] :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Ite (@measurable_fun_snd _ _ _ _)
       (Return R (@k3 _ _ [the measurableType _ of (T * bool)%type]))
       (Return R (@k10 _ _ [the measurableType _ of (T * bool)%type]))).

Lemma sample_and_branchE t U : sample_and_branch t U =
  (twoseven R)%:num%:E * \d_(3%R : R) U +
  (fiveseven R)%:num%:E * \d_(10%R : R) U.
Proof. by rewrite /sample_and_branch letin_sample_bernoulli27 !IteE. Qed.

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

Notation var2_of2 := (@measurable_fun_snd _ _ _ _).
Notation var2_of3 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
                                          (@measurable_fun_fst _ _ _ _)).
Notation var3_of3 := (@measurable_fun_snd _ _ _ _).

Variable Pdef : probability mbool R.

Definition staton_bus_measure' : R.-sfker T ~> mbool :=
  (letin
    (sample_bernoulli27 R T : _.-sfker T ~> mbool)
    (letin
      (letin
        (Ite var2_of2
           (Return R (@k3 _ _ _))
           (Return R (@k10 _ _ _))
         : _.-sfker [the measurableType _ of (T * bool)%type] ~> mR)
        (Score (measurable_fun_comp (@mpoisson R 4) var3_of3)
         : _.-sfker [the measurableType _ of (T * bool* mR)%type] ~> munit)
       : _.-sfker [the measurableType _ of (T * bool)%type] ~> munit)
      (Return R var2_of3
       : _.-sfker [the measurableType _ of (T * bool * munit)%type] ~> mbool)
     : _.-sfker [the measurableType _ of (T * bool)%type] ~> mbool)).

Definition staton_bus_measure : R.-sfker T ~> mbool :=
  (letin (sample_bernoulli27 R T)
  (letin
    (letin (Ite var2_of2
         (Return R (@k3 _ _ _))
         (Return R (@k10 _ _ _)))
     (Score (measurable_fun_comp (@mpoisson R 4) var3_of3)))
    (Return R var2_of3))).

(* true -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)
(* false -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)

Lemma staton_bus_measureE t U : staton_bus_measure t U =
  (twoseven R)%:num%:E * (poisson 3%:R 4)%:E * \d_true U +
  (fiveseven R)%:num%:E * (poisson 10%:R 4)%:E * \d_false U.
Proof.
rewrite /staton_bus_measure.
rewrite letin_sample_bernoulli27.
rewrite -!muleA.
congr (_ * _ + _ * _).
  rewrite letin_ureturn //.
  rewrite letin_ite_true//.
  rewrite letin_returnu//.
  by rewrite ScoreE// => r r0; exact: poisson_ge0.
rewrite letin_ureturn //.
rewrite letin_ite_false//.
rewrite letin_returnu//.
by rewrite ScoreE// => r r0; exact: poisson_ge0.
Qed.

Definition staton_bus : R.-pker T ~> mbool :=
  Normalize staton_bus_measure Pdef.

Lemma staton_busE t U :
  let N := (fine (((twoseven R)%:num)%:E * (poisson 3 4)%:E + ((fiveseven R)%:num)%:E * (poisson 10 4)%:E)) in
  staton_bus t U =
  ((twoseven R)%:num%:E * (poisson 3%:R 4)%:E * \d_true U +
   (fiveseven R)%:num%:E * (poisson 10%:R 4)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite NormalizeE /=.
rewrite /normalize.
rewrite !staton_bus_measureE.
rewrite diracE mem_set// mule1.
rewrite diracE mem_set// mule1.
rewrite ifF //.
apply/negbTE.
by rewrite gt_eqF// lte_fin addr_gt0// mulr_gt0//= poisson_gt0.
Qed.

End staton_bus.

(* wip *)

Definition swap (T1 T2 : Type) (x : T1 * T2) := (x.2, x.1).

Section letinC_example.

Variables (d d' d3 d4 : _) (R : realType) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3) (U : measurableType d4).
Let f (xyz : unit * X * X) := (xyz.1.2, xyz.2).
Lemma mf : measurable_fun setT f.
Proof.
rewrite /=.
apply/prod_measurable_funP => /=; split.
  rewrite /f.
  rewrite (_ : _ \o _ = (fun xyz : unit * X * X => xyz.1.2))//.
  apply: measurable_fun_comp => /=.
    exact: measurable_fun_snd.
  exact: measurable_fun_fst.
rewrite (_ : _ \o _ = (fun xyz : unit * X * X => xyz.2))//.
apply: measurable_fun_comp => /=.
  exact: measurable_fun_snd.
exact: measurable_fun_id.
Qed.

Let measurable_fun_swap : measurable_fun [set: X * X] (swap (T2:=X)).
Proof.
apply/prod_measurable_funP => /=; split.
  exact: measurable_fun_snd.
exact: measurable_fun_fst.
Qed.

Let f' := @swap _ _ \o f.
Lemma mf' : measurable_fun setT f'.
Proof.
rewrite /=.
apply: measurable_fun_comp => /=.
  exact: measurable_fun_swap.
exact: mf.
Qed.

Variables (t : R.-sfker Datatypes_unit__canonical__measure_Measurable ~> X)
          (t' : R.-sfker [the measurableType _ of (unit * X)%type] ~> X)
          (u : R.-sfker Datatypes_unit__canonical__measure_Measurable ~> X)
          (u' : R.-sfker [the measurableType _ of (unit * X)%type] ~> X)
          (H1 : forall y, u tt = u' (tt, y))
          (H2 : forall y, t tt = t' (tt, y)).
Lemma letinC x A : measurable A ->
  letin t (letin u' (Return R mf)) x A = letin u (letin t' (Return R mf')) x A.
Proof.
move=> mA.
rewrite /letin /= /kcomp /= /kcomp /=.
destruct x.
rewrite /f/=.
under eq_integral do rewrite -H1.
rewrite (@sfinite_fubini _ _ X X R t u (fun x => (\d_(x.1, x.2) A)))//=.
apply eq_integral => x _.
  by rewrite -H2.
apply/EFin_measurable_fun => /=.
rewrite (_ : (fun x => _) = mindic R mA)//.
by apply/funext => -[a b] /=.
Qed.

End letinC_example.
