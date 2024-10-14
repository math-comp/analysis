From mathcomp Require Import all_ssreflect all_algebra archimedean.
From mathcomp Require Import finmap (*lra*).
Require Import mathcomp_extra boolp classical_sets functions.
Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun realfun lebesgue_integral.
Require Import derive charge ftc trigo.

(* Formalisation of a simple proof that PI is irrational described in:
   http://projecteuclid.org/download/pdf_1/euclid.bams/1183510788 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(* TODO: move to ssrnum? *)
Lemma prodr_ile1 {R : realDomainType} (s : seq R) :
  (forall x, x \in s -> 0 <= x <= 1)%R -> (\prod_(j <- s) j <= 1)%R.
Proof.
elim: s => [_ | y s ih xs01]; rewrite ?big_nil// big_cons.
have /andP[y0 y1] : (0 <= y <= 1)%R by rewrite xs01// mem_head.
rewrite mulr_ile1 ?andbT//.
  rewrite big_seq prodr_ge0// => x xs.
  by have := xs01 x; rewrite inE xs orbT => /(_ _)/andP[].
by rewrite ih// => e xs; rewrite xs01// in_cons xs orbT.
Qed.

(* TODO: move to lebesgue_integral.v? *)
Section integral_fin_num_abs.
Local Open Scope ring_scope.
Context {d} {T : measurableType d} {R : realType}.
Variables (mu : {measure set T -> \bar R}) (D : set T).
Hypotheses (mD : measurable D).

Lemma integral_fin_num_abs (f : T -> R) : measurable_fun D f ->
  (\int[mu]_(x in D) `|(f x)%:E| < +oo)%E =
  ((\int[mu]_(x in D) (f x)%:E)%E \is a fin_num).
Proof.
move=> mf; rewrite fin_num_abs; case H : LHS; apply/esym.
- by move: H => /abse_integralP ->//; exact/EFin_measurable_fun.
- apply: contraFF H => /abse_integralP; apply => //.
  exact/EFin_measurable_fun.
Qed.

End integral_fin_num_abs.

(* TODO: move to lebesgue_integral.v *)
Section le_Rintegral.
Local Open Scope ring_scope.
Context {d} {T : measurableType d} {R : realType}.
Variables (mu : {measure set T -> \bar R}).
Variable (D : set T).
Hypotheses (mD : measurable D).
Variables f1 f2 : T -> R.
Local Open Scope ring_scope.
Hypotheses (mf1 : mu.-integrable D (EFin \o f1))
           (mf2 : mu.-integrable D (EFin \o f2)).

Lemma le_Rintegral : (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> f12; rewrite /Rintegral fine_le//.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf1.
  by apply/EFin_measurable_fun; case/integrableP : mf1.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf2.
  by apply/EFin_measurable_fun; case/integrableP : mf2.
- by apply/le_integral => // x xD; rewrite lee_fin f12//; exact/set_mem.
Qed.

End le_Rintegral.

(* TODO: move to lebesgue_integral.v *)
Lemma Rintegral_cst d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}%R) (D : set T) : (d.-measurable D)%classic ->
  forall r, (\int[mu]_(x in D) (cst r) x = r * fine (mu D))%R.
Proof.
move=> mD r; rewrite /Rintegral/= integral_cst//.
have := leey (mu D); rewrite le_eqVlt => /predU1P[->/=|muy]; last first.
  by rewrite fineM// ge0_fin_numE.
rewrite mulr_infty/=; have [_|r0|r0] := sgrP r.
- by rewrite mul0e/= mulr0.
- by rewrite mul1e/= mulr0.
- by rewrite mulN1e/= mulr0.
Qed.

(* two useful lemmas for the Num.int predicate *)
Lemma int_int {R : archiNumDomainType} (z : int) : (z%:~R)%R \is a @Num.int R.
Proof. by []. Qed.

Lemma nat_int {R : archiNumDomainType} (m : nat) : (m%:R)%R \is a @Num.int R.
Proof. by rewrite intrEge0. Qed.

Import numFieldNormedType.

(* connect MathComp's polynomials with analysis *)
Section derive_horner.
Variable (R : realFieldType).
Local Open Scope ring_scope.

Lemma horner0_ext : horner (0 : {poly R}) = 0.
Proof. by apply/funext => y /=; rewrite horner0. Qed.

Lemma hornerD_ext (p : {poly R}) r :
  horner (p * 'X + r%:P) = horner (p * 'X) + horner (r%:P).
Proof. by apply/funext => y /=; rewrite !(hornerE,fctE). Qed.

Lemma horner_scale_ext (p : {poly R}) :
  horner (p * 'X) = (fun x => p.[x] * x)%R.
Proof. by apply/funext => y; rewrite !hornerE. Qed.

Lemma hornerC_ext (r : R) : horner r%:P = cst r.
Proof. by apply/funext => y /=; rewrite !hornerE. Qed.

Lemma derivable_horner (p : {poly R}) x : derivable (horner p) x 1.
Proof.
elim/poly_ind: p => [|p r ih]; first by rewrite horner0_ext.
rewrite hornerD_ext; apply: derivableD.
- rewrite horner_scale_ext/=.
  by apply: derivableM; [exact:ih|exact:derivable_id].
- by rewrite hornerC_ext; exact: derivable_cst.
Qed.

Lemma derivE (p : {poly R}) : horner (deriv p) = derive1 (horner p).
Proof.
apply/funext => x; elim/poly_ind: p => [|p r ih].
  by rewrite deriv0 hornerC horner0_ext derive1_cst.
rewrite derivD hornerD hornerD_ext.
rewrite derive1E deriveD//; [|exact: derivable_horner..].
rewrite -!derive1E hornerC_ext derive1_cst addr0.
rewrite horner_scale_ext derive1E deriveM//; last exact: derivable_horner.
rewrite derive_id -derive1E -ih derivC horner0 addr0 derivM hornerD !hornerE.
rewrite derivX hornerE mulr1 addrC mulrC; congr +%R.
by rewrite /GRing.scale/= mulr1.
Qed.

Global Instance is_derive_poly (p : {poly R}) (x : R) :
  is_derive x (1:R) (horner p) p^`().[x].
Proof.
by apply: DeriveDef; [exact: derivable_horner|rewrite derivE derive1E].
Qed.

End derive_horner.

Local Open Scope classical_set_scope.

Lemma cvg_poly {R : realType} (p : {poly R}) (a : R^o) :
  (p.[x] @[x --> nbhs a] --> p.[a])%R.
Proof.
apply/differentiable_continuous.
exact/derivable1_diffP/derivable_horner.
Qed.

Lemma cvg_right_poly {R : realType} (p : {poly R}) a :
  (p.[x] @[x --> a^'+] --> p.[a])%R.
Proof.
apply/cvg_at_right_filter/differentiable_continuous.
exact/derivable1_diffP/derivable_horner.
Qed.

Lemma cvg_left_poly {R : realType} (p : {poly R}) a :
  (p.[x] @[x --> a^'-] --> p.[a])%R.
Proof.
apply/cvg_at_left_filter/differentiable_continuous.
exact/derivable1_diffP/derivable_horner.
Qed.

Local Close Scope classical_set_scope.

Lemma measurable_poly {R : realType} (p : {poly R}) (A : set R) :
  measurable_fun A (horner p).
Proof.
elim/poly_ind: p => [|p r ih].
  by rewrite horner0_ext; exact: measurable_cst.
rewrite hornerD_ext; apply: measurable_funD => //.
  by rewrite horner_scale_ext; exact: measurable_funM.
by rewrite hornerC_ext; exact: measurable_cst.
Qed.

Section Algebraic_part.
Local Open Scope ring_scope.
Context {R : realType}.
Variables na nb n : nat.
Hypothesis nb0 : nb != 0%N.

Definition a : R := (Posz na)%:~R.

Definition b : R := (Posz nb)%:~R.

Definition f : {poly R} := n`!%:R^-1 *: ('X^n * (a%:P - b*:'X)^+n).

Definition F : {poly R} := \sum_(i < n.+1) (-1)^i *: f^`(i.*2).

Let b0 : b != 0.
Proof. by rewrite intr_eq0. Qed.

Let P1_size : size (a%:P -  b *: 'X) = 2.
Proof.
have hs : size (- (b *: 'X)) = 2%N.
  by rewrite size_opp (* TODO: size_opp -> sizeN *) size_scale ?b0// size_polyX.
by rewrite addrC size_addl hs ?size_polyC//; case: (a != 0).
Qed.

Let P1_lead_coef : lead_coef (a%:P - b *: 'X) = - b.
Proof.
rewrite addrC lead_coefDl.
  by rewrite lead_coefN lead_coefZ lead_coefX mulr1.
by rewrite size_opp size_scale ?b0// size_polyX size_polyC; case: (a != 0).
Qed.

Let P_size : size ((a%:P -  b*:'X) ^+ n) = n.+1.
Proof.
elim : n => [|n0 Hn0]; first by rewrite expr0 size_polyC oner_neq0.
rewrite exprS size_proper_mul; first by rewrite P1_size /= Hn0.
by rewrite lead_coef_exp P1_lead_coef -exprS expf_neq0 // oppr_eq0 b0.
Qed.

Let comp_poly_exprn (p q : {poly R}) i : p ^+ i \Po q = (p \Po q) ^+ i.
Proof.
elim: i => [|i ih]; first by rewrite !expr0 comp_polyC.
by rewrite !exprS comp_polyM ih.
Qed.

(* Let's begin Niven's proof... *)
Let f_int i : n`!%:R * f`_i \is a Num.int.
Proof.
rewrite /f coefZ mulrA divff ?mul1r ?pnatr_eq0 ?gtn_eqF ?fact_gt0//.
apply/polyOverP => /=; rewrite rpredM ?rpredX ?polyOverX//=.
by rewrite rpredB ?polyOverC ?polyOverZ ?polyOverX//= ?int_int.
Qed.

Let f_small_coef0 i : (i < n)%N -> f`_i = 0.
Proof.
move=> ni; rewrite /f coefZ; apply/eqP.
rewrite mulf_eq0 invr_eq0 pnatr_eq0 gtn_eqF ?fact_gt0//=.
by rewrite coefXnM ni.
Qed.

Let derive_f_0_int i : f^`(i).[0] \is a Num.int.
Proof.
rewrite horner_coef0 coef_derivn addn0 ffactnn.
have [/f_small_coef0 ->|/bin_fact <-] := ltnP i n.
  by rewrite mul0rn // int_Qint.
by rewrite mulnCA -mulr_natl natrM mulrAC rpredM ?f_int ?nat_int.
Qed.

Lemma F0_int : F.[0] \is a Num.int.
Proof.
rewrite /F horner_sum rpred_sum //= =>  i _.
by rewrite !hornerE rpredM//= -exprnP rpredX// rpredN int_num1.
Qed.

Definition pirat := a / b.

Let pf_sym : f \Po (pirat%:P -'X) = f.
Proof.
rewrite /f comp_polyZ; congr *:%R.
rewrite comp_polyM !comp_poly_exprn comp_polyB comp_polyC !comp_polyZ.
rewrite !comp_polyX scalerBr.
have bap : b%:P * pirat%:P = a%:P.
  by rewrite polyCM mulrC -mulrA -polyCM mulVf ?b0 // mulr1.
suff -> : a%:P - (b *: pirat%:P - b *: 'X) = b%:P * 'X.
  rewrite exprMn mulrA mulrC; congr *%R.
  rewrite -exprMn; congr (_ ^+ _).
  rewrite mulrBl /pirat mul_polyC -bap (mulrC b%:P); congr (_ - _)%R.
    by rewrite mul_polyC.
  by rewrite mulrC mul_polyC.
by rewrite -mul_polyC bap opprB addrCA subrr addr0 mul_polyC.
Qed.

Let derivn_fpix i : f^`(i) \Po (pirat%:P -'X) = (-1) ^+ i *: f^`(i).
Proof.
elim:i ; first by rewrite /= expr0 scale1r pf_sym.
move=> i Hi.
rewrite [in RHS]derivnS exprS mulN1r scaleNr -(derivZ ((-1) ^+ i)) -Hi.
by rewrite deriv_comp derivB derivX -derivnS derivC sub0r mulrN1 opprK.
Qed.

Lemma FPi_int : F.[pirat] \is a Num.int.
Proof.
rewrite /F horner_sum rpred_sum // => i _ ; rewrite !hornerE rpredM //=.
  by rewrite -exprnP rpredX// (_ : -1 = (-1)%:~R)// intr_int.
move: (derivn_fpix i.*2).
rewrite -mul2n mulnC exprM sqrr_sign scale1r => <-.
by rewrite horner_comp !hornerE subrr derive_f_0_int.
Qed.

(* this is needed by the analytic part of the Niven proof *)
Lemma D2FDF : F^`(2) + F = f.
Proof.
rewrite /F linear_sum /=.
rewrite (eq_bigr (fun i : 'I_n.+1 => ((-1)^i *: f^`(i.+1.*2)%N))); last first.
  by move=> i _ ;rewrite !derivZ.
rewrite [X in _ + X]big_ord_recl/=.
rewrite -exprnP expr0 scale1r (addrC f) addrA -[X in _ = X]add0r.
congr (_ + _).
rewrite big_ord_recr addrC addrA -big_split big1=>[| i _].
  rewrite add0r /=; apply/eqP; rewrite scaler_eq0 -derivnS derivn_poly0.
    by rewrite deriv0 eqxx orbT.
  suff -> : size f = (n + n.+1)%N by rewrite addnS addnn.
  rewrite /f size_scale; last first.
    by rewrite invr_neq0 // pnatr_eq0 -lt0n (fact_gt0 n).
  rewrite size_monicM ?monicXn //; last by rewrite -size_poly_eq0 P_size.
  by rewrite  size_polyXn P_size.
rewrite /bump /= -scalerDl.
apply/eqP; rewrite scaler_eq0 /bump -exprnP add1n exprSr.
by rewrite mulrN1 addrC subr_eq0 eqxx orTb.
Qed.

End Algebraic_part.

Local Open Scope classical_set_scope.
Lemma exp_fact (R : realType) (r : R) :
  (r ^+ n / n`!%:R @[n --> \oo] --> 0)%R.
Proof.
apply/cvg_series_cvg_0.
exact: is_cvg_series_exp_coeff.
Qed.

Local Open Scope ring_scope.
(* NB: not used... *)
Lemma exp_fact_alternative (R : realType) (r : R) :
  (r ^+ n / n`!%:R @[n --> \oo] --> 0)%R.
Proof.
apply: norm_cvg0.
apply/cvgrPdist_le => /= e e0; near=> k; rewrite sub0r normrN normr_id.
pose N := `|Num.ceil r|.+1%N.
rewrite normrM normfV (@ger0_norm _ k`!%:R)// normrX.
rewrite -{1}[k]/(k.+1.-1) -subn1 -prodr_const_nat fact_prod natr_prod.
rewrite [in X in X / _]/index_iota subn1/=;
rewrite -[in X in X / _](@subnKC N k); last by near: k; exists N.
rewrite iotaD big_cat/= -[_ :: _]/(index_iota 1 N.+1).
rewrite -[in X in _ / X](@subnKC N k)/=; last by near: k; exists N.
rewrite [in X in _ / X]/index_iota subn1.
rewrite iotaD big_cat/= -[_ :: _]/(index_iota 1 N.+1).
rewrite -mulf_div -prodfV -big_split/= -prodfV -big_split /=.
apply: (@le_trans _ _ (\prod_(1 <= i < N.+1) (`|r| / i%:R) * (`|r| / k%:R))).
  rewrite ler_wpM2l//; first exact/prodr_ge0.
  rewrite (_ : iota _ _ = iota (1 + N) (k - N).-1 ++ [:: k]); last first.
    rewrite (_ : [:: k] = iota k 1)//.
    rewrite [X in iota X 1](_ : _ = (1 + N) + (k - N).-1)%N; last first.
      by rewrite add1n -subnS subnKC//; near: k; exists N.+1.
    by rewrite -iotaD addn1 prednK// subn_gt0//; near: k; exists N.+1.
  rewrite big_cat/= big_cons big_nil mulr1 ler_piMl//.
  have /prodr_ile1 : forall z : R,
      z \in [seq (`|r| / i%:R) | i <- iota (1 + N) (k - N).-1] ->
      0 <= z <= 1.
    move=> _ /mapP[/= m] /[!mem_iota] /andP[Nk kN] ->; apply/andP; split => //.
    rewrite ler_pdivrMr// ?mul1r//; last by rewrite ltr0n (leq_trans _ Nk).
    rewrite (@le_trans _ _ N.+1%:R)//; last by rewrite ler_nat -addn1 addnC.
    by rewrite /N (le_trans (abs_ceil_ge _))// ler_nat ltnS.
  by rewrite big_map.
rewrite mulrA ler_pdivrMr//; last by rewrite ltr0n; near: k; exists 1%N.
by rewrite (mulrC e) -ler_pdivrMr//; near: k; exact: nbhs_infty_ger.
Unshelve. all: by end_near. Qed.

Local Close Scope ring_scope.
Local Close Scope classical_set_scope.

Section Analytic_part.
Local Open Scope ring_scope.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Variable na nb : nat.
Hypothesis nb0 : nb != 0%N.

Let pirat : R := pirat na nb.

Let f := @f R na nb.

(* NB: helper lemma, not elegant... *)
Let abx x : 0 < x < pirat -> 0 < a na - b nb * x.
Proof.
move=> /andP[x0]; rewrite subr_gt0.
rewrite /pirat /exercise6.pirat ltr_pdivlMr 1?mulrC//.
by rewrite /b ltr0n lt0n.
Qed.

(* TODO: use the {in _, _} notation? *)
Let abx_ge0 x : 0 <= x <= pirat -> 0 <= a na - b nb * x.
Proof.
move=> /andP[x0 xpi]; rewrite subr_ge0.
rewrite -ler_pdivlMl//; last by rewrite /b ltr0n lt0n.
by rewrite mulrC.
Qed.

Let fsin n := fun x : R => (f n).[x] * sin x.

Let F := @F R na nb.

Lemma fsin_antiderivative n :
  derive1 (fun x => derive1 (horner (F n)) x * sin x - ((F n).[x]) * cos x) =
  fsin n :> (R -> R).
Proof.
apply/funext => x/=.
rewrite derive1E/= deriveD//=; last first.
  apply: derivableM; last exact: ex_derive.
  by rewrite -derivE; exact: derivable_horner.
rewrite deriveM//; last by rewrite -derivE; exact: derivable_horner.
rewrite deriveN//= deriveM// !derive_val opprD -addrA addrC !addrA.
rewrite scalerN opprK -addrA [X in (_ + X = _)%R](_ : _ = 0%R); last first.
  rewrite addrC derivE.
  by apply/eqP; rewrite subr_eq0 [eqbLHS]mulrC.
rewrite addr0 -derive1E.
have := @D2FDF R na _ n nb0.
rewrite -/F derivSn /fsin -/f => <-.
rewrite -!derivE derivn1.
rewrite [X in (X + _ = _)%R](_ : _ = (F n)^`()^`().[x]%R * sin x)%R; last first.
  by rewrite mulrC.
by rewrite -mulrDl hornerD.
Qed.

Definition intfsin n := \int[mu]_(x in `[0, pi]) (fsin n x).

Local Open Scope classical_set_scope.

Let cfsin n (A : set R^o) : {within A, continuous (fsin n : R^o -> R^o)}.
Proof.
apply/continuous_subspaceT => /= x.
by apply: cvgM => /=; [exact: cvg_poly|exact: continuous_sin].
Qed.

Hypothesis piratE : pirat = pi.

Lemma intfsinE n : intfsin n = (F n).[pi] + (F n).[0].
Proof.
rewrite /intfsin /Rintegral.
set h := fun x => (derive1 (fun x => (F n).[x]) x * sin x - (F n).[x] * cos x).
rewrite (@continuous_FTC2 _ _ h).
- rewrite /h sin0 cospi cos0 sinpi !mulr0 !add0r mulr1 mulrN1 !opprK EFinN.
  by rewrite oppeK -EFinD.
- by rewrite pi_gt0.
- exact: cfsin.
- split.
  + move=> x x0pi.
    by apply: derivableB => //; apply: derivableM => //; rewrite -derivE.
  + apply: cvgB => //.
      rewrite -!derivE.
      apply: cvgM => //; first exact: cvg_right_poly.
      by apply: (@cvg_at_right_filter R R^o); exact: continuous_sin.
    apply: cvgM => //; first exact: cvg_right_poly.
    by apply: (@cvg_at_right_filter R R^o); exact: continuous_cos.
  + apply: cvgB => //.
      apply: cvgM => //.
        rewrite -derivE.
        exact: cvg_left_poly.
      by apply: (@cvg_at_left_filter R R^o); exact: continuous_sin.
    apply: cvgM; first exact: cvg_left_poly.
    by apply: (@cvg_at_left_filter R R^o); exact: continuous_cos.
- by move=> x x0pi; rewrite fsin_antiderivative.
Qed.

Lemma intfsin_int n : intfsin n \is a Num.int.
Proof. by rewrite intfsinE rpredD ?F0_int -?piratE ?FPi_int. Qed.

Let f0 x : (f 0).[x] = 1.
Proof.
by rewrite /f /exercise6.f fact0 !expr0 invr1 mulr1 !hornerE.
Qed.

Lemma fsin_bounded n (x : R) : (0 < n)%N -> 0 < x < pi ->
  0 < fsin n x < (pi ^+ n * (a na) ^+ n) / n`!%:R.
Proof.
move=> n0 /andP[x0 xpi].
have sinx0 : 0 < sin x by rewrite sin_gt0_pi// x0.
apply/andP; split.
  rewrite mulr_gt0// /f !hornerE/= mulr_gt0//.
    by rewrite mulr_gt0 ?invr_gt0 ?ltr0n ?fact_gt0// exprn_gt0.
  by rewrite exprn_gt0// abx// x0 piratE.
rewrite /fsin !hornerE/= -2!mulrA mulrC ltr_pM2r ?invr_gt0 ?ltr0n ?fact_gt0//.
rewrite -!exprMn [in ltRHS]mulrC mulrA -exprMn.
have ? : 0 <= a na - b nb * x.
  by rewrite abx_ge0 ?piratE// (ltW x0) ltW.
have H1 : x * (a na - b nb * x) < a na * pi.
  rewrite [ltRHS]mulrC ltr_pM//; first exact/ltW.
  by rewrite ltrBlDl //ltrDr mulr_gt0// lt0r /b pnatr_eq0 nb0/=.
have := sin_le1 x; rewrite le_eqVlt => /predU1P[x1|x1].
- by rewrite x1 mulr1 ltrXn2r ?gtn_eqF// mulr_ge0//; exact/ltW.
- rewrite -[ltRHS]mulr1 ltr_pM//.
  + by rewrite exprn_ge0// mulr_ge0//; exact/ltW.
  + exact/ltW.
  + by rewrite ltrXn2r ?gtn_eqF// mulr_ge0//; exact/ltW.
Qed.

Lemma intsin : (\int[mu]_(x in `[0%R, pi]) (sin x)%:E = 2%:E)%E.
Proof.
rewrite (@continuous_FTC2 _ _ (- cos)) ?pi_gt0//.
- by rewrite /= !EFinN cos0 cospi !EFinN oppeK.
- exact/(@continuous_subspaceT R^o R^o)/continuous_sin.
- split.
  + by move=> x x0pi; exact/derivableN/derivable_cos.
  + by apply: cvgN; apply: cvg_at_right_filter; exact: continuous_cos.
  + by apply: cvgN; apply: cvg_at_left_filter; exact: continuous_cos.
  + by move=> x x0pi; rewrite derive1E deriveN// derive_val opprK.
Qed.

Lemma integrable_fsin n : mu.-integrable `[0%R, pi] (EFin \o fsin n).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: cfsin.
Qed.

Section fsin_small_ball.
Let m : R^o := pi / 2.
Let d : R := pi / 4.

Lemma small_ballS : closed_ball m d `<=` `]0%R, pi[.
Proof.
move=> z; rewrite closed_ball_itv/=; last by rewrite divr_gt0// pi_gt0.
rewrite in_itv/= => /andP[mdz zmd]; rewrite in_itv/=; apply/andP; split.
  rewrite (lt_le_trans _ mdz)// subr_gt0.
  by rewrite ltr_pM2l// ?pi_gt0// ltf_pV2// ?posrE// ltr_nat.
rewrite (le_lt_trans zmd)// -mulrDr gtr_pMr// ?pi_gt0//.
by rewrite -ltrBrDl [X in _ < X - _](splitr 1) div1r addrK ltf_pV2 ?posrE// ltr_nat.
(* that would be immediate with lra... *)
Qed.

Lemma min_fsin n : (0 < n)%N ->
  exists2 r : R, 0 < r & forall x, x \in closed_ball m d -> r <= fsin n x.
Proof.
move=> n0; have mdmd : m - d <= m + d.
  by rewrite lerBlDr -addrA lerDl -mulr2n mulrn_wge0// divr_ge0// pi_ge0.
have cf : {within `[m - d, m + d], continuous (fsin n : _ -> R^o)}.
  exact: cfsin.
have [c cmd Hc] := @EVT_min R (fsin n) _ _ mdmd cf.
exists (fsin n c).
  have /(_ _)/andP[]// := @fsin_bounded n c n0.
  have := @small_ballS c; rewrite /=in_itv/=; apply.
  by rewrite closed_ball_itv//= divr_gt0// pi_gt0.
move=> x /set_mem; rewrite closed_ball_itv//=; first exact: Hc.
by rewrite divr_gt0// pi_gt0.
Qed.

End fsin_small_ball.

Lemma intfsin_gt0 n : 0 < intfsin n.
Proof.
rewrite fine_gt0//; have [->|n0] := eqVneq n 0.
  rewrite /fsin; under eq_integral do rewrite f0 mul1r.
  by rewrite intsin ltry andbT.
have fsin_ge0 (x : R) : 0 <= x <= pi -> (0 <= (fsin n x)%:E)%E.
   move=> /andP[x0 xpi]; rewrite lee_fin mulr_ge0//.
     rewrite !hornerE mulr_ge0//=.
       by rewrite mulr_ge0// exprn_ge0.
     by rewrite exprn_ge0// abx_ge0// piratE x0.
   by rewrite sin_ge0_pi// x0.
apply/andP; split.
  rewrite -lt0n in n0.
  have [r r0] := @min_fsin _ n0.
  pose m : R^o := pi / 2; pose d : R := pi / 4 => rn.
  apply: (@lt_le_trans _ _ (\int[mu]_(x in closed_ball m d) r%:E))%E.
    rewrite integral_cst//=; last exact: measurable_closed_ball.
    rewrite mule_gt0// lebesgue_measure_closed_ball//.
      by rewrite lte_fin mulrn_wgt0// divr_gt0// pi_gt0.
    by rewrite divr_ge0// pi_ge0.
  apply: (@le_trans _ _ (\int[mu]_(x in (closed_ball m d)) (fsin n x)%:E))%E.
    apply: ge0_le_integral => //=.
    - exact: measurable_closed_ball.
    - by move=> x _; rewrite lee_fin ltW.
    - move=> x /small_ballS/= /[!in_itv]/= /andP[x0 xpi].
      by rewrite fsin_ge0// (ltW x0)/= ltW.
    - case/integrableP : (integrable_fsin n) => + _.
      apply: measurable_funS => // x ix.
      exact: subset_itv_oo_cc (small_ballS ix).
    - by move=> x /mem_set /rn; rewrite lee_fin.
  apply: ge0_subset_integral => //=.
  - exact: measurable_closed_ball.
  - by case/integrableP : (integrable_fsin n).
  - by move=> x ix; exact: subset_itv_oo_cc (small_ballS ix).
case/integrableP : (integrable_fsin n) => ? /=.
apply: le_lt_trans; apply: ge0_le_integral => //=.
- apply/EFin_measurable_fun => /=; apply/measurableT_comp => //.
  exact/EFin_measurable_fun.
- by move=> x x0pi; rewrite lee_fin ler_norm.
Qed.

Lemma intfsin_small (e : R) : 0 < e -> \forall n \near \oo, 0 < intfsin n < e.
Proof.
move=> e0; near=> n.
rewrite intfsin_gt0/=.
apply: (@le_lt_trans _ _
    (\int[mu]_(x in `[0, pi]) ((pi ^+ n * (a na) ^+ n) / n`!%:R))).
  apply: le_Rintegral => //=.
  - apply/continuous_compact_integrable; first exact: segment_compact.
    exact: cfsin.
  - apply/continuous_compact_integrable; first exact: segment_compact.
    by apply/continuous_subspaceT => x; exact: cvg_cst.
  - move=> x.
    have ? : 0 <= pi ^+ n * a na ^+ n / n`!%:R :> R.
      by rewrite mulr_ge0// mulr_ge0// exprn_ge0// pi_ge0.
    rewrite in_itv/= => /andP[].
    rewrite le_eqVlt => /predU1P[<- _|x0]; first by rewrite /fsin sin0 !hornerE.
    rewrite le_eqVlt => /predU1P[->|xpi]; first by rewrite /fsin sinpi mulr0.
    have n0 : (0 < n)%N by near: n; exists 1%N.
    have /(_ _)/andP[|//] := @fsin_bounded _ x n0.
    + by rewrite x0.
    + by move=> _ /ltW.
rewrite Rintegral_cst//= lebesgue_measure_itv/= lte_fin pi_gt0/=.
rewrite subr0 mulrAC -exprMn (mulrC _ pi) -mulrA.
near: n.
have : pi * (pi * a na) ^+ n / n`!%:R @[n --> \oo] --> (0:R^o).
  rewrite -[X in _ --> X](mulr0 pi).
  under eq_fun do rewrite -mulrA.
  by apply: cvgMr; exact: exp_fact.
move/cvgrPdist_lt => /(_ e e0)[k _]H.
near=> n.
have {H} := H n.
rewrite sub0r normrN ger0_norm; last first.
  by rewrite !mulr_ge0 ?pi_ge0// exprn_ge0// mulr_ge0// pi_ge0.
rewrite mulrA; apply.
by near: n; exists k.
Unshelve. all: by end_near. Qed.

End Analytic_part.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* TODO: what's the predicate for rationality? could be more elegant *)
Lemma pi_is_irrationnal {R : realType} (a b : nat) :
  b != 0 -> pi != a%:~R / b%:~R :> R.
Proof.
move=> b0; apply/negP => /eqP piratE.
have [N _] := intfsin_small b0 (esym piratE) (@ltr01 R).
near \oo => n.
have Nn : (N <= n)%N by near: n; exists N.
have := @intfsin_int R _ _ b0 (esym piratE) n.
rewrite intrEge0; last by rewrite ltW// intfsin_gt0.
move=> + /(_ n Nn).
move/natrP => [k] ->.
rewrite ltr0n ltrn1.
by case: k.
Unshelve. all: by end_near. Qed.
