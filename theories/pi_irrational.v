From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop itv reals ereal topology.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun lebesgue_integral.
From mathcomp Require Import derive charge ftc trigo.

(**md**************************************************************************)
(* # Formalisation of A simple proof that pi is irrational by Ivan Niven      *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - http://projecteuclid.org/download/pdf_1/euclid.bams/1183510788           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

(* TODO: move *)
Lemma measurable_poly {R : realType} (p : {poly R}) (A : set R) :
  measurable_fun A (horner p).
Proof.
apply/measurable_funTS; apply: continuous_measurable_fun.
exact/continuous_horner.
Qed.

(* TODO: move somewhere to classical *)
Definition rational {R : realType} (x : R) := exists m n, x = (m%:R / n%:R)%R.

Module pi_irrational.
Local Open Scope ring_scope.

Lemma exp_fact (R : realType) (r : R) :
  (r ^+ n / n`!%:R @[n --> \oo] --> 0)%classic.
Proof.
by apply/cvg_series_cvg_0; exact: is_cvg_series_exp_coeff.
Qed.

Section algebraic_part.
Context {R : realType}.
Variables na nb n : nat.
Hypothesis nb0 : nb != 0%N.

Definition a : R := na%:R.

Definition b : R := nb%:R.

Definition f : {poly R} := n`!%:R^-1 *: ('X^n * (a%:P - b *: 'X) ^+ n).

Definition F : {poly R} := \sum_(i < n.+1) (-1)^i *: f^`(i.*2).

Let b0 : b != 0. Proof. by rewrite pnatr_eq0. Qed.

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

Let f_int i : n`!%:R * f`_i \is a Num.int.
Proof.
rewrite /f coefZ mulrA divff ?mul1r ?pnatr_eq0 ?gtn_eqF ?fact_gt0//.
apply/polyOverP => /=; rewrite rpredM ?rpredX ?polyOverX//=.
by rewrite rpredB ?polyOverC ?polyOverZ ?polyOverX//= nat_int.
Qed.

Let f_small_coef0 i : (i < n)%N -> f`_i = 0.
Proof. by move=> ni; rewrite /f coefZ coefXnM ni mulr0. Qed.

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

Let pf_sym : f \Po (pirat%:P - 'X) = f.
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

Let derivn_fpix i : f^`(i) \Po (pirat%:P - 'X) = (-1) ^+ i *: f^`(i).
Proof.
elim:i ; first by rewrite /= expr0 scale1r pf_sym.
move=> i Hi.
rewrite [in RHS]derivnS exprS mulN1r scaleNr -(derivZ ((-1) ^+ i)) -Hi.
by rewrite deriv_comp derivB derivX -derivnS derivC sub0r mulrN1 opprK.
Qed.

Let derivn_f_pi_int i : f^`(i).[pirat] \is a Num.int.
Proof.
rewrite -pf_sym.
have := derivn_fpix i.
rewrite -signr_odd.
have [oi|ei] := boolP (odd i).
  rewrite expr1 scaleN1r => /eqP; rewrite -eqr_oppLR => /eqP.
  rewrite -[in X in _ = X -> _]pf_sym => <-.
  by rewrite hornerN rpredN/= horner_comp/= !hornerE subrr derive_f_0_int.
rewrite expr0 scale1r.
rewrite -[in X in _ = X -> _]pf_sym => <-.
by rewrite horner_comp/= !hornerE subrr derive_f_0_int.
Qed.

Lemma Fpi_int : F.[pirat] \is a Num.int.
Proof.
rewrite /F horner_sum rpred_sum // => i _; rewrite !hornerE rpredM //=.
by rewrite -exprnP rpredX// (_ : -1 = (-1)%:~R)// intr_int.
Qed.

Lemma D2FDF : F^`(2) + F = f.
Proof.
rewrite /F linear_sum /=.
rewrite (eq_bigr (fun i : 'I_n.+1 => (-1)^i *: f^`(i.*2.+2))); last first.
  by move=> i _; rewrite !derivZ.
rewrite [X in _ + X]big_ord_recl.
rewrite -exprnP expr0 scale1r (addrC f) addrA -[RHS]add0r.
congr (_ + _).
rewrite big_ord_recr addrC addrA -big_split big1=>[|i _].
  rewrite add0r /=; apply/eqP; rewrite scaler_eq0 -derivnS derivn_poly0.
    by rewrite deriv0 eqxx orbT.
  suff -> : size f = (n + n.+1)%N by rewrite addnS addnn.
  rewrite /f size_scale; last first.
    by rewrite invr_neq0 // pnatr_eq0 -lt0n (fact_gt0 n).
  rewrite size_monicM ?monicXn //; last by rewrite -size_poly_eq0 P_size.
  by rewrite size_polyXn P_size.
rewrite /bump /= -scalerDl.
apply/eqP; rewrite scaler_eq0 /bump -exprnP add1n exprSr.
by rewrite mulrN1 addrC subr_eq0 eqxx orTb.
Qed.

End algebraic_part.

Section analytic_part.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Variable na nb : nat.
Hypothesis nb0 : nb != 0%N.

Let pirat : R := pirat na nb.

Let a : R := a na.

Let b : R := b nb.

Let f := @f R na nb.

Let abx_gt0 x : 0 < x < pirat -> 0 < a - b * x.
Proof.
move=> /andP[x0]; rewrite subr_gt0.
rewrite /pirat /pirat ltr_pdivlMr 1?mulrC//.
by rewrite ltr0n lt0n.
Qed.

Let abx_ge0 x : 0 <= x <= pirat -> 0 <= a - b * x.
Proof.
move=> /andP[x0 xpi]; rewrite subr_ge0.
rewrite -ler_pdivlMl//; last by rewrite /b ltr0n lt0n.
by rewrite mulrC.
Qed.

Let fsin n := fun x : R => (f n).[x] * sin x.

Let F := @F R na nb.

Let fsin_antiderivative n :
  'D_1 (fun x => (F n)^`().[x] * sin x - (F n).[x] * cos x) =
  fsin n.
Proof.
apply/funext => x/=.
rewrite deriveB//= !deriveM// !derive_val.
rewrite opprD scalerN opprK.
rewrite -addrA addrC -!addrA [X in - X]mulrC !addrA subrK [X in X + _]mulrC.
rewrite -derivn1 -derivSn.
(* ((F n)^`(2)).[x] * sin x + (F n).[x] * sin x *)
by rewrite -mulrDl -hornerD (@D2FDF R na _ n nb0).
Qed.

Definition intfsin n := \int[mu]_(x in `[0, pi]) (fsin n x).

Local Open Scope classical_set_scope.

Let cfsin n (A : set R) : {within A, continuous (fsin n)}.
Proof.
apply/continuous_subspaceT => /= x.
by apply: cvgM => /=; [exact: continuous_horner|exact: continuous_sin].
Qed.

Goal forall (p : {poly R}) c, p.[x] @[x --> c^'+] --> p.[c].
by move=> p c; apply: cvg_at_right_filter; exact: continuous_horner.
Qed.

Let intfsinE n : intfsin n = (F n).[pi] + (F n).[0].
Proof.
rewrite /intfsin /Rintegral.
set h := fun x => ((F n)^`()).[x] * sin x - (F n).[x] * cos x.
rewrite (@continuous_FTC2 _ _ h).
- rewrite /h sin0 cospi cos0 sinpi !mulr0 !add0r mulr1 mulrN1 !opprK EFinN.
  by rewrite oppeK -EFinD.
- by rewrite pi_gt0.
- exact: cfsin.
- split=> [x x0pi| |].
  + by apply: derivableB => //; apply: derivableM => //; rewrite -derivE.
  + by apply: cvgB; apply: cvgM => //; apply: cvg_at_right_filter;
      (exact: continuous_horner||exact: continuous_sin||exact: continuous_cos).
  + by apply: cvgB; apply: cvgM => //; apply: cvg_at_left_filter;
      (exact: continuous_horner||exact: continuous_sin||exact: continuous_cos).
- by move=> x x0pi; rewrite -fsin_antiderivative derive1E.
Qed.

Hypothesis piratE : pirat = pi.

Lemma intfsin_int n : intfsin n \is a Num.int.
Proof. by rewrite intfsinE rpredD ?F0_int -?piratE ?Fpi_int. Qed.

Let f0 x : (f 0).[x] = 1.
Proof. by rewrite /f /pi_irrational.f fact0 !expr0 invr1 mulr1 !hornerE. Qed.

Let fsin_bounded n (x : R) : (0 < n)%N -> 0 < x < pi ->
  0 < fsin n x < (pi ^+ n * a ^+ n) / n`!%:R.
Proof.
move=> n0 /andP[x0 xpi].
have sinx0 : 0 < sin x by rewrite sin_gt0_pi// x0.
apply/andP; split.
  rewrite mulr_gt0// /f !hornerE/= mulr_gt0//.
    by rewrite mulr_gt0 ?invr_gt0 ?ltr0n ?fact_gt0// exprn_gt0.
  by rewrite exprn_gt0// abx_gt0// x0 piratE.
rewrite /fsin !hornerE/= -2!mulrA mulrC ltr_pM2r ?invr_gt0 ?ltr0n ?fact_gt0//.
rewrite -!exprMn [in ltRHS]mulrC mulrA -exprMn.
have ? : 0 <= a - b * x by rewrite abx_ge0 ?piratE// (ltW x0) ltW.
have ? : x * (a - b * x) < a * pi.
  rewrite [ltRHS]mulrC ltr_pM//; first exact/ltW.
  by rewrite ltrBlDl// ltrDr mulr_gt0// lt0r /b pnatr_eq0 nb0/=.
have := sin_le1 x; rewrite le_eqVlt => /predU1P[x1|x1].
- by rewrite x1 mulr1 ltrXn2r ?gtn_eqF// mulr_ge0//; exact/ltW.
- rewrite -[ltRHS]mulr1 ltr_pM//.
  + by rewrite exprn_ge0// mulr_ge0//; exact/ltW.
  + exact/ltW.
  + by rewrite ltrXn2r ?gtn_eqF// mulr_ge0//; exact/ltW.
Qed.

Let intsin : (\int[mu]_(x in `[0%R, pi]) (sin x)%:E = 2%:E)%E.
Proof.
rewrite (@continuous_FTC2 _ _ (- cos)) ?pi_gt0//.
- by rewrite /= !EFinN cos0 cospi !EFinN oppeK.
- exact/continuous_subspaceT/continuous_sin.
- split.
  + by move=> x x0pi; exact/derivableN/derivable_cos.
  + by apply: cvgN; apply: cvg_at_right_filter; exact: continuous_cos.
  + by apply: cvgN; apply: cvg_at_left_filter; exact: continuous_cos.
  + by move=> x x0pi; rewrite derive1E deriveN// derive_val opprK.
Qed.

Let integrable_fsin n : mu.-integrable `[0%R, pi] (EFin \o fsin n).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: cfsin.
Qed.

Let small_ballS (m : R := pi / 2) (d := pi / 4) :
  closed_ball m d `<=` `]0%R, pi[.
Proof.
move=> z; rewrite closed_ball_itv/=; last by rewrite divr_gt0// pi_gt0.
rewrite in_itv/= => /andP[mdz zmd]; rewrite in_itv/=; apply/andP; split.
  rewrite (lt_le_trans _ mdz)// subr_gt0.
  by rewrite ltr_pM2l// ?pi_gt0// ltf_pV2// ?posrE// ltr_nat.
rewrite (le_lt_trans zmd)// -mulrDr gtr_pMr// ?pi_gt0//.
by rewrite -ltrBrDl [X in _ < X - _](splitr 1) div1r addrK ltf_pV2 ?posrE// ltr_nat.
(* that would be immediate with lra... *)
Qed.

Let min_fsin (m : R := pi / 2) (d := pi / 4) n : (0 < n)%N ->
  exists2 r : R, 0 < r & forall x, x \in closed_ball m d -> r <= fsin n x.
Proof.
move=> n0; have mdmd : m - d <= m + d.
  by rewrite lerBlDr -addrA lerDl -mulr2n mulrn_wge0// divr_ge0// pi_ge0.
have cf : {within `[m - d, m + d], continuous (fsin n)}.
  exact: cfsin.
have [c cmd Hc] := @EVT_min R (fsin n) _ _ mdmd cf.
exists (fsin n c).
  have /(_ _)/andP[]// := @fsin_bounded n c n0.
  have := @small_ballS c; rewrite /=in_itv/=; apply.
  by rewrite closed_ball_itv//= divr_gt0// pi_gt0.
move=> x /set_mem; rewrite closed_ball_itv//=; first exact: Hc.
by rewrite divr_gt0// pi_gt0.
Qed.

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
  pose m : R := pi / 2; pose d : R := pi / 4 => rn.
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
- apply/measurable_EFinP => /=; apply/measurableT_comp => //.
  exact/measurable_EFinP.
- by move=> x x0pi; rewrite lee_fin ler_norm.
Qed.

Lemma intfsin_small (e : R) : 0 < e -> \forall n \near \oo, 0 < intfsin n < e.
Proof.
move=> e0; near=> n.
rewrite intfsin_gt0/=.
apply: (@le_lt_trans _ _
    (\int[mu]_(x in `[0, pi]) (pi ^+ n * a ^+ n / n`!%:R))).
  apply: le_Rintegral => //=.
  - apply/continuous_compact_integrable; first exact: segment_compact.
    by apply/continuous_subspaceT => x; exact: cvg_cst.
  - move=> x.
    have ? : 0 <= pi ^+ n * a ^+ n / n`!%:R :> R.
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
have : pi * (pi * a) ^+ n / n`!%:R @[n --> \oo] --> 0.
  rewrite -[X in _ --> X](mulr0 pi).
  under eq_fun do rewrite -mulrA.
  by apply: cvgMr; exact: exp_fact.
move/cvgrPdist_lt => /(_ e e0).
apply: filterS => n.
rewrite sub0r normrN ger0_norm; last first.
  by rewrite !mulr_ge0 ?pi_ge0// exprn_ge0// mulr_ge0// pi_ge0.
by rewrite mulrA; exact.
Unshelve. all: by end_near. Qed.

End analytic_part.

End pi_irrational.

Lemma pi_irrationnal {R : realType} : ~ rational (pi : R).
Proof.
move=> [a [b]]; have [->|b0 piratE] := eqVneq b O.
  by rewrite invr0 mulr0; apply/eqP; rewrite gt_eqF// pi_gt0.
have [N _] := pi_irrational.intfsin_small b0 (esym piratE) (@ltr01 R).
near \oo%classic => n.
have Nn : (N <= n)%N by near: n; exists N.
have := @pi_irrational.intfsin_int R _ _ b0 (esym piratE) n.
rewrite intrEge0; last by rewrite ltW// pi_irrational.intfsin_gt0.
move=> + /(_ n Nn).
move/natrP => [k] ->.
rewrite ltr0n ltrn1.
by case: k.
Unshelve. all: by end_near. Qed.
