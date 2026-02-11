(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg poly ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import measure exp numfun realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral charge ftc uniform_distribution.
From mathcomp Require Import bernoulli_distribution.

(**md**************************************************************************)
(* # Beta distribution                                                        *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(* ```                                                                        *)
(*            XMonemX a b := x ^+ a * x.~ ^+ b                                *)
(*           beta_fun a b := \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1] x)        *)
(*               beta_pdf == probability density function for beta            *)
(*              beta_prob == beta probability measure                         *)
(*   div_beta_fun a b c d := beta_fun (a + c) (b + d) / beta_fun a b          *)
(*  beta_prob_bernoulli_prob a b c d U := \int[beta_prob a b]_(y \in [0, 1])  *)
(*                         bernoulli_prob (XMonemX c d) U                     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(**md lemmas about the function $x \mapsto (1 - x)^n$ *)
Section about_onemXn.
Context {R : realType}.
Implicit Types x y : R.

Lemma continuous_onemXn n x : {for x, continuous (fun y => y.~ ^+ n)}.
Proof.
apply: (@continuous_comp _ _ _ (@onem R) (fun x => x ^+ n)).
  by apply: (@cvgB _ R^o); [exact: cvg_cst|exact: cvg_id].
exact: exprn_continuous.
Qed.

Lemma onemXn_derivable n x : derivable (fun y => y.~ ^+ n) x 1.
Proof.
have := @derivableX _ _ (@onem R) n x 1.
by rewrite fctE; apply; exact: derivableB.
Qed.

Lemma derivable_oo_LRcontinuous_onemXnMr n x :
  derivable_oo_LRcontinuous (fun y => y.~ ^+ n * x) 0 1.
Proof.
split.
- by move=> y y01; apply: derivableM => //=; exact: onemXn_derivable.
- apply: cvgM; last exact: cvg_cst.
  apply: cvg_at_right_filter; apply: (@cvg_comp _ _ _ onem (fun x => x ^+ n)).
    by apply: cvgB; [exact: cvg_cst|exact: cvg_id].
  exact: exprn_continuous.
- apply: cvg_at_left_filter; apply: cvgM; last exact: cvg_cst.
  apply: (@cvg_comp _ _ _ onem (fun x => x ^+ n)).
    by apply: cvgB; [exact: cvg_cst|exact: cvg_id].
  exact: exprn_continuous.
Qed.

Lemma derive_onemXn n x :
  (fun y => y.~ ^+ n)^`()%classic x = - n%:R * x.~ ^+ n.-1.
Proof.
rewrite (@derive1_comp _ (@onem _) (fun x => x ^+ n))//; last first.
  exact: exprn_derivable.
rewrite derive1E exp_derive// derive1E deriveB// -derive1E.
by rewrite derive1_cst derive_id sub0r mulrN1 [in RHS]mulNr scaler1.
Qed.

Lemma Rintegral_onemXn n :
  \int[lebesgue_measure]_(x in `[0, 1]) (x.~ ^+ n) = n.+1%:R^-1 :> R.
Proof.
rewrite /Rintegral.
rewrite (@continuous_FTC2 _ _ (fun x => x.~ ^+ n.+1 / - n.+1%:R))//=.
- rewrite onem1 expr0n/= mul0r onem0 expr1n mul1r sub0r.
  by rewrite -invrN -2!mulNrn opprK.
- by apply: continuous_in_subspaceT => x x01; exact: continuous_onemXn.
- exact: derivable_oo_LRcontinuous_onemXnMr.
- move=> x x01; rewrite derive1Mr//; last exact: onemXn_derivable.
  by rewrite derive_onemXn mulrAC divff// mul1r.
Qed.

End about_onemXn.
#[deprecated(since="mathcomp-analysis 1.15.0", note="renamed to `derivable_oo_LRcontinuous_onemXnMr`")]
Notation derivable_oo_continuous_bnd_onemXnMr := derivable_oo_LRcontinuous_onemXnMr (only parsing).

(**md about the function $x \mapsto x^a  (1 - x)^b$ *)
Section XMonemX.
Context {R : numDomainType}.
Implicit Types (x : R) (a b : nat).

Definition XMonemX a b := fun x => x ^+ a * x.~ ^+ b.

Lemma XMonemX_ge0 a b x : x \in `[0, 1] -> 0 <= XMonemX a b x.
Proof.
by rewrite in_itv=> /andP[? ?]; rewrite mulr_ge0 ?exprn_ge0 ?subr_ge0.
Qed.

Lemma XMonemX_le1 a b x : x \in `[0, 1] -> XMonemX a b x <= 1.
Proof.
rewrite in_itv/= => /andP[t0 t1].
by rewrite mulr_ile1// ?(exprn_ge0,onem_ge0,exprn_ile1,onem_le1).
Qed.

Lemma XMonemX0n n x : XMonemX 0 n x = x.~ ^+ n.
Proof. by rewrite /XMonemX/= expr0 mul1r. Qed.

Lemma XMonemXn0 n x : XMonemX n 0 x = x ^+ n.
Proof. by rewrite /XMonemX/= expr0 mulr1. Qed.

Lemma XMonemX00 x : XMonemX 0 0 x = 1.
Proof. by rewrite XMonemX0n expr0. Qed.

Lemma XMonemXC a b x : XMonemX a b (1 - x) = XMonemX b a x.
Proof. by rewrite /XMonemX [in LHS]/onem opprB subrKC mulrC. Qed.

Lemma XMonemXM a b a' b' x :
  XMonemX a' b' x * XMonemX a b x = XMonemX (a + a') (b + b') x.
Proof. by rewrite mulrCA -mulrA -exprD mulrA -exprD (addnC b'). Qed.

End XMonemX.

Section XMonemX_realType.
Context {R : realType}.
Local Notation XMonemX := (@XMonemX R).

Lemma continuous_XMonemX a b : continuous (XMonemX a b).
Proof.
by move=> x; apply: cvgM; [exact: exprn_continuous|exact: continuous_onemXn].
Qed.

Lemma within_continuous_XMonemX A a b : {within A, continuous (XMonemX a b)}.
Proof. by apply: continuous_in_subspaceT => x _; exact: continuous_XMonemX. Qed.

Lemma measurable_XMonemX A a b : measurable_fun A (XMonemX a b).
Proof.
apply/measurable_funM => //; apply/measurable_funX => //.
exact: measurable_funB.
Qed.

Lemma bounded_XMonemX a b : [bounded XMonemX a b x | x in `[0, 1]%classic].
Proof.
exists 1; split; [by rewrite num_real|move=> x x1 /= y y01].
rewrite ger0_norm//; last by rewrite XMonemX_ge0.
move: y01; rewrite in_itv/= => /andP[y0 y1].
rewrite (le_trans _ (ltW x1))// mulr_ile1 ?exprn_ge0//.
- exact: onem_ge0.
- by rewrite exprn_ile1.
- by rewrite exprn_ile1 ?onem_ge0 ?onem_le1.
Qed.

Local Notation mu := lebesgue_measure.

Lemma integrable_XMonemX a b : mu.-integrable `[0, 1] (EFin \o XMonemX a b).
Proof.
apply: continuous_compact_integrable => //; first exact: segment_compact.
by apply: continuous_in_subspaceT => x _; exact: continuous_XMonemX.
Qed.

Lemma integrable_XMonemX_restrict a b :
  mu.-integrable [set: R] (EFin \o XMonemX a.-1 b.-1 \_ `[0, 1]).
Proof.
rewrite -restrict_EFin; apply/integrable_restrict => //=.
by rewrite setTI; exact: integrable_XMonemX.
Qed.

Local Open Scope ereal_scope.

Lemma integral_XMonemX_restrict U a b :
  \int[mu]_(x in U) (XMonemX a b \_ `[0, 1] x)%:E =
  \int[mu]_(x in U `&` `[0%R, 1%R]) (XMonemX a b x)%:E.
Proof.
rewrite [RHS]integral_mkcondr /=; apply: eq_integral => x xU /=.
by rewrite restrict_EFin.
Qed.

End XMonemX_realType.

Section beta_fun.
Context {R : realType}.
Notation mu := (@lebesgue_measure _).
Local Open Scope ring_scope.
Local Notation XMonemX := (@XMonemX R).

Definition beta_fun a b : R := \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1]) x.

Local Open Scope ereal_scope.

Lemma EFin_beta_fun a b :
  (beta_fun a b)%:E = \int[mu]_x (XMonemX a.-1 b.-1 \_`[0,1] x)%:E.
Proof.
rewrite fineK//; apply: integrable_fin_num => //=.
under eq_fun.
  move=> x.
  rewrite /= -/((EFin \o ((XMonemX a.-1 b.-1) \_ _)) x) -restrict_EFin.
  over.
by apply/integrable_restrict => //=; rewrite setTI; exact: integrable_XMonemX.
Qed.

Local Close Scope ereal_scope.

Lemma beta_fun_sym a b : beta_fun a b = beta_fun b a.
Proof.
rewrite -[LHS]Rintegral_mkcond Rintegration_by_substitution_onem ?lexx ?ler01//=.
- rewrite onem1 -[RHS]Rintegral_mkcond; apply: eq_Rintegral => x x01.
  by rewrite XMonemXC.
- exact: within_continuous_XMonemX.
Qed.

Lemma beta_fun0n b : (0 < b)%N -> beta_fun 0 b = b%:R^-1.
Proof.
move=> b0; rewrite -[LHS]Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX0n.
by rewrite Rintegral_onemXn// prednK.
Qed.

Lemma beta_fun00 : beta_fun 0 0 = 1%R.
Proof.
rewrite -[LHS]Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX00.
by rewrite Rintegral_cst//= mul1r lebesgue_measure_itv/= lte01 EFinN sube0.
Qed.

Lemma beta_fun1Sn b : beta_fun 1 b.+1 = b.+1%:R^-1.
Proof.
rewrite /beta_fun -Rintegral_mkcond.
under eq_Rintegral do rewrite XMonemX0n.
by rewrite Rintegral_onemXn.
Qed.

Lemma beta_fun11 : beta_fun 1 1 = 1.
Proof. by rewrite (beta_fun1Sn O) invr1. Qed.

Lemma beta_funSSnSm a b :
  beta_fun a.+2 b.+1 = a.+1%:R / b.+1%:R * beta_fun a.+1 b.+2.
Proof.
rewrite -[LHS]Rintegral_mkcond.
rewrite (@Rintegration_by_parts _ _ (fun x => x.~ ^+ b.+1 / - b.+1%:R)
    (fun x => a.+1%:R * x ^+ a)); last 7 first.
  exact: ltr01.
  apply/continuous_subspaceT => x.
  by apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
  split.
    by move=> x x01; exact: exprn_derivable.
    exact/cvg_at_right_filter/exprn_continuous.
    exact/cvg_at_left_filter/exprn_continuous.
  by move=> x x01; rewrite derive1E exp_derive scaler1.
  by apply/continuous_subspaceT => x x01; exact: continuous_onemXn.
  exact: derivable_oo_LRcontinuous_onemXnMr.
  move=> x x01; rewrite derive1Mr; last exact: onemXn_derivable.
  by rewrite derive_onemXn mulrAC divff// mul1r.
rewrite {1}/onem !(expr1n,mul1r,expr0n,subr0,subrr,mul0r,oppr0,sub0r)/=.
transitivity (a.+1%:R / b.+1%:R * \int[mu]_(x in `[0, 1]) XMonemX a b.+1 x).
  under [in LHS]eq_Rintegral.
    move=> x x01.
    rewrite mulrA mulrC mulrA (mulrA _ a.+1%:R) -(mulrA (_ * _)%R).
    over.
  rewrite /= RintegralZl//=; last exact: integrable_XMonemX.
  by rewrite -mulNrn -2!mulNr -invrN -mulNrn opprK (mulrC _ a.+1%:R).
by rewrite Rintegral_mkcond.
Qed.

Lemma beta_funSnSm a b : beta_fun a.+1 b.+1 =
  a`!%:R / (\prod_(b.+1 <= i < (a + b).+1) i)%:R * beta_fun 1 (a + b).+1.
Proof.
elim: a b => [b|a ih b].
  by rewrite fact0 mul1r add0n /index_iota subnn big_nil invr1 mul1r.
rewrite beta_funSSnSm [in LHS]ih !mulrA; congr *%R; last by rewrite addSnnS.
rewrite -mulrA mulrCA 2!mulrA.
rewrite -natrM (mulnC a`!) -factS -mulrA -invfM; congr (_ / _).
rewrite big_add1 [in RHS]big_nat_recl/=; last by rewrite addSn ltnS leq_addl.
by rewrite -natrM addSnnS.
Qed.

Lemma beta_fun_fact a b :
  beta_fun a.+1 b.+1 = (a`! * b`!)%:R / (a + b).+1`!%:R.
Proof.
rewrite beta_funSnSm beta_fun1Sn natrM -!mulrA; congr *%R.
(* (b+1 b+2 ... b+1 b+a)^-1 / (a+b+1) = b! / (a+b+1)! *)
rewrite factS [in RHS]mulnC natrM invfM mulrA; congr (_ / _).
rewrite -(@invrK _ b`!%:R) -invfM; congr (_^-1).
apply: (@mulfI _ b`!%:R); first by rewrite gt_eqF// ltr0n fact_gt0.
rewrite mulrA divff// ?gt_eqF// ?ltr0n ?fact_gt0 ?mul1r//.
rewrite [in RHS]fact_prod -natrM; congr (_%:R).
rewrite fact_prod -big_cat/= /index_iota subn1 -iotaD.
by rewrite subSS addnK subn1 addnC.
Qed.

Lemma beta_funE a b : beta_fun a b =
  if (a == 0)%N && (0 < b)%N then
    b%:R^-1
  else if (b == 0)%N && (0 < a)%N then
    a%:R^-1
  else
    a.-1`!%:R * b.-1`!%:R / (a + b).-1`!%:R.
Proof.
case: a => [|a].
  rewrite eqxx/=; case: ifPn => [|].
    by case: b => [|b _] //; rewrite beta_fun0n.
  rewrite -leqNgt leqn0 => /eqP ->.
  by rewrite beta_fun00 eqxx ltnn/= fact0 mul1r divr1.
case: b => [|b].
  by rewrite beta_fun_sym beta_fun0n// fact0 addn0/= mulr1 divff.
by rewrite beta_fun_fact natrM// addnS.
Qed.

Lemma beta_fun_gt0 a b : 0 < beta_fun a b.
Proof.
rewrite beta_funE.
case: ifPn => [/andP[_ b0]|]; first by rewrite invr_gt0 ltr0n.
rewrite negb_and => /orP[a0|].
  case: ifPn => [/andP[_]|]; first by rewrite invr_gt0// ltr0n.
  rewrite negb_and => /orP[b0|].
    by rewrite divr_gt0// ?mulr_gt0 ?ltr0n ?fact_gt0.
  by rewrite -leqNgt leqn0 (negbTE a0).
rewrite -leqNgt leqn0 => /eqP ->; rewrite eqxx/=.
case: ifPn; first by rewrite invr_gt0 ltr0n.
by rewrite -leqNgt leqn0 => /eqP ->; rewrite fact0 mul1r divr1.
Qed.

Lemma beta_fun_ge0 a b : 0 <= beta_fun a b.
Proof. exact/ltW/beta_fun_gt0. Qed.

End beta_fun.

Section beta_pdf.
Local Open Scope ring_scope.
Context {R : realType}.
Variables a b : nat.

Local Notation XMonemX := (@XMonemX R).

Definition beta_pdf t : R := XMonemX a.-1 b.-1 \_`[0, 1] t / beta_fun a b.

Lemma measurable_beta_pdf : measurable_fun [set: R] beta_pdf.
Proof.
apply: measurable_funM => //; apply/measurable_restrict => //.
by rewrite setTI; exact: measurable_XMonemX.
Qed.

Lemma beta_pdf_ge0 t : 0 <= beta_pdf t.
Proof.
rewrite /beta_pdf divr_ge0 ?beta_fun_ge0//.
rewrite patchE; case: ifPn => //=.
by rewrite inE/= => ?; exact: XMonemX_ge0.
Qed.

Lemma beta_pdf_le_beta_funV x : beta_pdf x <= (beta_fun a b)^-1.
Proof.
rewrite /beta_pdf ler_pdivrMr ?beta_fun_gt0// mulVf ?gt_eqF ?beta_fun_gt0//.
by rewrite patchE; case: ifPn => //; rewrite inE/= => ?; exact: XMonemX_le1.
Qed.

Local Notation mu := lebesgue_measure.

Local Open Scope ereal_scope.

Let int_beta_pdf01 : \int[mu]_(x in `[0%R, 1%R]) (beta_pdf x)%:E =
                     \int[mu]_x (beta_pdf x)%:E :> \bar R.
Proof.
rewrite integral_mkcond/=; apply: eq_integral => /=x _.
by rewrite /beta_pdf/= !patchE; case: ifPn => [->//|_]; rewrite mul0r.
Qed.

Local Close Scope ereal_scope.

Lemma integrable_beta_pdf : mu.-integrable [set: _] (EFin \o beta_pdf).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_beta_pdf.
under eq_integral=> /= x _ do rewrite ger0_norm ?beta_pdf_ge0//.
rewrite /= -int_beta_pdf01.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R]) (beta_fun a b)^-1%:E)%E).
  apply: ge0_le_integral => //=.
  - by move=> x _; rewrite lee_fin beta_pdf_ge0.
  - by apply/measurable_funTS/measurable_EFinP=> /=; exact: measurable_beta_pdf.
  - by move=> x _; rewrite lee_fin beta_pdf_le_beta_funV.
rewrite integral_cst//= lebesgue_measure_itv//=.
by rewrite lte01 oppr0 adde0 mule1 ltry.
Qed.

Lemma bounded_beta_pdf_01 : [bounded beta_pdf x | x in `[0%R, 1%R]%classic].
Proof.
exists (beta_fun a b)^-1; split; first by rewrite num_real.
move=> // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M => M /=; rewrite in_itv/= => /andP[M0 M1].
rewrite ler_norml; apply/andP; split.
  rewrite lerNl (@le_trans _ _ 0%R)// ?invr_ge0 ?beta_fun_ge0//.
  by rewrite lerNl oppr0 beta_pdf_ge0.
rewrite /beta_pdf ler_pdivrMr ?beta_fun_gt0//.
rewrite mulVf ?gt_eqF ?beta_fun_gt0//.
by rewrite patchE; case: ifPn => //; rewrite inE => ?; exact: XMonemX_le1.
Unshelve. all: by end_near. Qed.

End beta_pdf.

Section beta.
Local Open Scope ring_scope.
Context {R : realType}.
Variables a b : nat.

Local Notation mu := (@lebesgue_measure R).
Local Notation XMonemX := (@XMonemX R).

Let beta_num (U : set (measurableTypeR R)) : \bar R :=
  \int[mu]_(x in U) (XMonemX a.-1 b.-1 \_`[0,1] x)%:E.

Let beta_numT : beta_num [set: (measurableTypeR R)] = (beta_fun a b)%:E.
Proof. by rewrite /beta_num/= EFin_beta_fun. Qed.

Let beta_num_lty U : measurable U -> (beta_num U < +oo)%E.
Proof.
move=> mU.
apply: (@le_lt_trans _ _ (\int[mu]_(x in U `&` `[0%R, 1%R]) 1)%E); last first.
  rewrite integral_cst//= ?mul1e//.
    rewrite (le_lt_trans (measureIr _ _ _))//= lebesgue_measure_itv//= lte01//.
    by rewrite EFinN sube0 ltry.
  exact: measurableI.
rewrite /beta_num integral_XMonemX_restrict ge0_le_integral//=.
- exact: measurableI.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_XMonemX.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_le1.
Qed.

Let beta_num0 : beta_num set0 = 0%:E.
Proof. by rewrite /beta_num integral_set0. Qed.

Let beta_num_ge0 U : (0 <= beta_num U)%E.
Proof.
rewrite /beta_num integral_ge0//= => x Ux; rewrite lee_fin.
by rewrite patchE; case: ifPn => //; rewrite inE/= => x01; exact: XMonemX_ge0.
Qed.

Let beta_num_sigma_additive : semi_sigma_additive beta_num.
Proof.
move=> /= F mF tF mUF; rewrite /beta_num; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _; apply: integral_ge0 => /= x Fkx.
  rewrite patchE; case: ifPn => //; rewrite inE/= => x01.
  by rewrite lee_fin XMonemX_ge0.
rewrite ge0_integral_bigcup//=.
- apply/measurable_funTS/measurableT_comp => //=.
  by apply/measurable_restrict => //=; rewrite setTI; exact: measurable_XMonemX.
- move=> x [? _ ?]; rewrite lee_fin.
  by rewrite patchE; case: ifPn => //; rewrite inE/= => x0; exact: XMonemX_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ beta_num
  beta_num0 beta_num_ge0 beta_num_sigma_additive.

Definition beta_prob :=
  mscale ((NngNum (beta_fun_ge0 a b))%:num^-1)%:nng beta_num.

HB.instance Definition _ := Measure.on beta_prob.

Let beta_prob_setT : beta_prob setT = 1%:E.
Proof.
rewrite /beta_prob /= /mscale /= beta_numT.
by rewrite -EFinM mulVf// gt_eqF// beta_fun_gt0.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ _ beta_prob beta_prob_setT.

Lemma integral_beta_pdf U : measurable U ->
  (\int[mu]_(x in U) (beta_pdf a b x)%:E = beta_prob U :> \bar R)%E.
Proof.
move=> mU; rewrite /beta_pdf.
under eq_integral do rewrite EFinM/=.
rewrite ge0_integralZr//=.
- by rewrite /beta_prob/= /mscale/= muleC.
- apply/measurable_funTS/measurableT_comp => //.
  by apply/measurable_restrict => //=; rewrite setTI; exact: measurable_XMonemX.
- move=> x Ux; rewrite patchE; case: ifPn => //; rewrite inE/= => x01.
  by rewrite lee_fin XMonemX_ge0.
- by rewrite lee_fin invr_ge0// beta_fun_ge0.
Qed.

Lemma beta_prob01 : beta_prob `[0, 1] = 1%:E.
Proof.
rewrite -beta_prob_setT/= /beta_prob/= /mscale/= /beta_num/=.
rewrite [in RHS]integral_XMonemX_restrict/= setTI.
by rewrite [in LHS]integral_XMonemX_restrict/= setIid.
Qed.

Lemma beta_prob_fin_num U : measurable U -> beta_prob U \is a fin_num.
Proof.
move=> mU; rewrite ge0_fin_numE//.
rewrite (@le_lt_trans _ _ (beta_prob setT))//=.
  by rewrite le_measure// inE.
by rewrite probability_setT ltry.
Qed.

Lemma beta_prob_dom : beta_prob `<< mu.
Proof.
apply/null_content_dominatesP => A mA muA0; rewrite /beta_prob /mscale/=.
apply/eqP; rewrite mule_eq0 eqe invr_eq0 gt_eqF/= ?beta_fun_gt0//; apply/eqP.
rewrite /beta_num integral_XMonemX_restrict.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: integral_ge0 => x [_ ?]; rewrite lee_fin XMonemX_ge0.
apply: (@le_trans _ _ (\int[mu]_(x in A `&` `[0%R, 1%R]) 1)%E); last first.
  rewrite integral_cst ?mul1e//=; last exact: measurableI.
  by rewrite -[leRHS]muA0 measureIl.
apply: ge0_le_integral => //=; first exact: measurableI.
- by move=> x [_ x01]; rewrite lee_fin XMonemX_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_XMonemX.
- by move=> x [_ ?]; rewrite lee_fin XMonemX_le1.
Qed.

End beta.
Arguments beta_prob {R}.

Lemma beta_prob_uniform {R : realType} :
  beta_prob 1 1 = uniform_prob (@ltr01 R).
Proof.
apply/funext => U.
rewrite /beta_prob /uniform_prob.
rewrite /mscale/= beta_fun11 invr1 !mul1e.
rewrite integral_XMonemX_restrict integral_uniform_pdf.
apply: eq_integral => /= x.
rewrite inE => -[Ux/=]; rewrite in_itv/= => x10.
rewrite /XMonemX !expr0 mul1r.
by rewrite /uniform_pdf x10 subr0 invr1.
Qed.

Local Open Scope ereal_scope.

Lemma integral_beta_prob_bernoulli_prob_lty {R : realType} a b (f : R -> R) U :
  measurable_fun [set: R] f ->
  (forall x : R, x \in `[0, 1]%R -> 0 <= f x <= 1)%R ->
  \int[beta_prob a b]_x `|bernoulli_prob (f x) U| < +oo.
Proof.
move=> mf /= f01.
apply: (@le_lt_trans _ _ (\int[beta_prob a b]_x cst 1 x)).
  apply: ge0_le_integral => //=.
    apply: measurableT_comp => //=.
    exact: (measurableT_comp (measurable_bernoulli_prob2 _)).
  by move=> x _; rewrite gee0_abs// probability_le1.
by rewrite integral_cst//= mul1e -ge0_fin_numE// beta_prob_fin_num.
Qed.

Local Close Scope ereal_scope.

Lemma integral_beta_prob_bernoulli_prob_onemX_lty {R : realType} n a b U :
  (\int[beta_prob a b]_x `|bernoulli_prob (x.~ ^+ n) U| < +oo :> \bar R)%E.
Proof.
apply: integral_beta_prob_bernoulli_prob_lty => //=.
  by apply: measurable_funX => //; exact: measurable_funB.
move=> x; rewrite in_itv/= => /andP[x0 x1].
rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
by rewrite lerBlDl -lerBlDr subrr.
Qed.

Lemma integral_beta_prob_bernoulli_prob_onem_lty {R : realType} n a b U :
  (\int[beta_prob a b]_x `|bernoulli_prob (1 - x.~ ^+ n) U| < +oo :> \bar R)%E.
Proof.
apply: integral_beta_prob_bernoulli_prob_lty => //=.
  apply: measurable_funB => //.
  by apply: measurable_funX => //; exact: measurable_funB.
move=> x; rewrite in_itv/= => /andP[x0 x1].
rewrite -[_ <= 1]subr_ge0 opprB subrKC subr_ge0 andbC.
rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
by rewrite lerBlDl -lerBlDr subrr.
Qed.

Lemma beta_prob_integrable {R :realType} a b a' b' :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x)%:E).
Proof.
apply/integrableP; split.
  by apply/measurableT_comp => //; exact: measurable_XMonemX.
apply: (@le_lt_trans _ _ (\int[beta_prob a b]_(x in `[0%R, 1%R]) 1)%E).
  apply: ge0_le_integral => //=.
    by do 2 apply/measurableT_comp => //; exact: measurable_XMonemX.
  move=> x; rewrite in_itv/= => /andP[x0 x1].
  rewrite lee_fin ger0_norm; last by rewrite !mulr_ge0// exprn_ge0// onem_ge0.
  by rewrite mulr_ile1// ?exprn_ge0 ?onem_ge0// exprn_ile1 ?onem_ge0 ?onem_le1.
by rewrite integral_cst//= mul1e -ge0_fin_numE// beta_prob_fin_num.
Qed.

Lemma beta_prob_integrable_onem {R : realType} a b a' b' :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x).~%:E).
Proof.
apply: (eq_integrable _ (cst 1 \- (fun x : measurableTypeR R =>
  (XMonemX a' b' x)%:E))%E) => //.
apply: integrableB => //=; last exact: beta_prob_integrable.
apply/integrableP; split => //.
rewrite (eq_integral (fun x => (\1_setT x)%:E))/=; last first.
  by move=> x _; rewrite /= indicT normr1.
rewrite integral_indic//= setTI /beta_prob /mscale/= lte_mul_pinfty//.
  by rewrite lee_fin invr_ge0 beta_fun_ge0.
rewrite (_ : integral _ _ _ = \int[lebesgue_measure]_x
  (((@XMonemX R a.-1 b.-1) \_ `[0, 1]) x)%:E)%E; last first.
  rewrite [LHS]integral_mkcond/=; apply: eq_integral => /= x _.
  by rewrite !patchE; case: ifPn => // ->.
have /integrableP[_] := @integrable_XMonemX_restrict R a b.
under eq_integral.
  move=> x _.
  rewrite gee0_abs//; last first.
    rewrite lee_fin patchE; case: ifPn => //; rewrite inE/= => x01.
    by rewrite XMonemX_ge0.
  over.
by [].
Qed.

Lemma beta_prob_integrable_dirac {R : realType} a b a' b' (c : bool) U :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x)%:E * \d_c U)%E.
Proof.
apply: integrableMl => //=; last first.
  exists 1; split => // x x1/= _ _; rewrite (le_trans _ (ltW x1))//.
  by rewrite ger0_norm// indicE; case: (_ \in _).
exact: beta_prob_integrable.
Qed.

Lemma beta_prob_integrable_onem_dirac {R : realType} a b a' b' (c : bool) U :
  (beta_prob a b).-integrable `[0, 1]
    (fun x : measurableTypeR R => (XMonemX a' b' x).~%:E * \d_c U)%E.
Proof.
apply: integrableMl => //=.
  exact: beta_prob_integrable_onem.
exists 1; split => // x x1/= _ _; rewrite (le_trans _ (ltW x1))//.
by rewrite ger0_norm// indicE; case: (_ \in _).
Qed.

Section integral_beta_prob.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

Lemma integral_beta_prob a b f U : measurable U -> measurable_fun U f ->
  (\int[beta_prob a b]_(x in U) `|f x| < +oo)%E ->
  (\int[beta_prob a b]_(x in U) f x =
   \int[mu]_(x in U) (f x * (beta_pdf a b x)%:E))%E.
Proof.
move=> mU mf finf.
rewrite -(Radon_Nikodym_change_of_variables (beta_prob_dom a b))//=; last first.
  by apply/integrableP; split.
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //; apply: (measurable_int mu).
  apply: (integrableS _ _ (@subsetT _ _)) => //=.
  by apply: Radon_Nikodym_integrable; exact: beta_prob_dom.
- apply: emeasurable_funM => //=; apply/measurableT_comp => //=.
  by apply/measurable_funTS; exact: measurable_beta_pdf.
- apply: ae_eqe_mul2l => /=.
  rewrite Radon_NikodymE//=; first exact: beta_prob_dom.
  move=> abmu.
  case: cid => /= h [h1 h2 h3].
  (* uniqueness of Radon-Nikodym derivative up to equality on non null sets of mu *)
  apply: integral_ae_eq => //=.
  + exact: integrableS h2.
  + by apply/measurable_funTS/measurableT_comp =>//; exact: measurable_beta_pdf.
  + by move=> E E01 mE; rewrite -h3//= integral_beta_pdf.
Qed.

End integral_beta_prob.

Section beta_prob_bernoulliE.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Open Scope ring_scope.

Definition div_beta_fun a b c d : R := beta_fun (a + c) (b + d) / beta_fun a b.

Lemma div_beta_fun_ge0 a b c d : 0 <= div_beta_fun a b c d.
Proof. by rewrite /div_beta_fun divr_ge0// beta_fun_ge0. Qed.

Lemma div_beta_fun_le1 a b c d : (0 < a)%N -> (0 < b)%N ->
  div_beta_fun a b c d <= 1.
Proof.
move=> a0 b0.
rewrite /div_beta_fun ler_pdivrMr// ?mul1r ?beta_fun_gt0//.
rewrite !beta_funE.
rewrite addn_eq0 (gtn_eqF a0)/=.
rewrite addn_eq0 (gtn_eqF b0)/=.
rewrite ler_pdivrMr ?ltr0n ?fact_gt0//.
rewrite mulrAC.
rewrite ler_pdivlMr ?ltr0n ?fact_gt0//.
rewrite -!natrM ler_nat.
move: a a0 => [//|a _].
rewrite addSn.
move: b b0 => [//|b _].
rewrite [(a + c).+1.-1]/=.
rewrite [a.+1.-1]/=.
rewrite [b.+1.-1]/=.
rewrite addnS.
rewrite [(_ + b).+1.-1]/=.
rewrite (addSn b d).
rewrite [(b + _).+1.-1]/=.
rewrite (addSn (a + c)).
rewrite [_.+1.-1]/=.
rewrite addSn addnS.
by rewrite leq_fact2// leq_addr.
Qed.

Definition beta_prob_bernoulli_prob a b c d U : \bar R :=
  \int[beta_prob a b]_(y in `[0, 1])
    bernoulli_prob ((@XMonemX R c d \_`[0, 1])%R y) U.

Lemma beta_prob_bernoulli_probE a b c d U : (a > 0)%N -> (b > 0)%N ->
  beta_prob_bernoulli_prob a b c d U = bernoulli_prob (div_beta_fun a b c d) U.
Proof.
move=> a0 b0.
rewrite /beta_prob_bernoulli_prob.
under eq_integral => x.
  rewrite inE/= in_itv/= => x01.
  rewrite bernoulli_probE/=; last first.
  rewrite patchE; case: ifPn => x01'.
    by rewrite XMonemX_ge0//= XMonemX_le1.
  by rewrite lexx ler01.
  over.
rewrite /= [in RHS]bernoulli_probE/= ?div_beta_fun_ge0 ?div_beta_fun_le1//=.
under eq_integral => x x01.
  rewrite patchE x01/=.
  over.
rewrite /= integralD//=; last 2 first.
  exact: beta_prob_integrable_dirac.
  exact: beta_prob_integrable_onem_dirac.
congr (_ + _).
  rewrite integralZr//=; last exact: beta_prob_integrable.
  congr (_ * _)%E.
  rewrite integral_beta_prob//; last 2 first.
    by apply/measurableT_comp => //; exact: measurable_XMonemX.
    by have /integrableP[_] := @beta_prob_integrable R a b c d.
  transitivity ((\int[mu]_(x in `[0%R, 1%R])
      ((x.~ ^+ d)%:E * ((beta_pdf a b x)%:E * (x ^+ c)%:E)))%E : \bar R).
    apply: eq_integral => /= x _.
    by rewrite [in LHS]EFinM -[LHS]muleA [LHS]muleC -[LHS]muleA.
  transitivity ((beta_fun a b)^-1%:E * \int[mu]_(x in `[0%R, 1%R])
      (@XMonemX R (a + c).-1 (b + d).-1 \_`[0,1] x)%:E)%E.
    rewrite -integralZl//=; last first.
      by apply: (integrableS measurableT) => //=; exact: integrable_XMonemX_restrict.
    apply: eq_integral => x x01.
    rewrite muleA muleC muleA -(EFinM (x ^+ c)) -/(XMonemX c d x) -EFinM mulrA.
    rewrite !patchE x01 XMonemXM// -EFinM mulrC.
    by move: a a0 b b0 => [//|a] _ [|b].
  rewrite /div_beta_fun mulrC EFinM; congr (_ * _)%E.
  rewrite /beta_fun integral_mkcond/= fineK; last first.
    by apply: integrable_fin_num => //; exact: integrable_XMonemX_restrict.
  by apply: eq_integral => /= x _; rewrite !patchE; case: ifPn => // ->.
under eq_integral do rewrite muleC.
rewrite /= integralZl//=; last exact: beta_prob_integrable_onem.
rewrite muleC; congr (_ * _)%E.
rewrite integral_beta_prob//=; last 2 first.
  apply/measurableT_comp => //=.
  by apply/measurable_funB => //; exact: measurable_XMonemX.
  by have /integrableP[] := @beta_prob_integrable_onem R a b c d.
rewrite /beta_pdf.
under eq_integral do rewrite EFinM muleA.
rewrite integralZr//=; last first.
  apply: integrableMr => //=.
  - by apply/measurable_funB => //=; exact: measurable_XMonemX.
  - apply/ex_bound => //.
    + apply: (@globally_properfilter _ _ 0%R) => //=.
      by apply: inferP; rewrite in_itv/= lexx ler01.
    + exists 1 => t.
      rewrite /= in_itv/= => t01.
      apply: normr_onem; apply/andP; split.
        by rewrite mulr_ge0// exprn_ge0// ?onem_ge0//; case/andP: t01.
      by rewrite mulr_ile1// ?exprn_ge0 ?exprn_ile1// ?onem_ge0 ?onem_le1//;
        case/andP: t01.
  - exact: integrableS (integrable_XMonemX_restrict _ _).
transitivity ((\int[mu]_x ((@XMonemX R a.-1 b.-1 \_`[0,1] x)%:E -
   (@XMonemX R (a + c).-1 (b + d).-1 \_`[0,1] x)%:E)) * (beta_fun a b)^-1%:E)%E.
  congr (_ * _)%E; rewrite [LHS]integral_mkcond/=; apply eq_integral => x _.
  rewrite !patchE; case: ifPn => [->|]; last by rewrite EFinN subee.
  rewrite /onem -EFinM mulrBl mul1r EFinB EFinN; congr (_ - _)%E.
  rewrite XMonemXM.
  by move: a a0 b b0 => [|a]// _ [|b].
rewrite integralB_EFin//=; last 2 first.
  exact: integrableS (integrable_XMonemX_restrict _ _).
  exact: integrableS (integrable_XMonemX_restrict _ _).
rewrite EFinB muleBl//; last by rewrite -!EFin_beta_fun.
by rewrite -!EFin_beta_fun -EFinM divff// gt_eqF// beta_fun_gt0.
Qed.

End beta_prob_bernoulliE.
