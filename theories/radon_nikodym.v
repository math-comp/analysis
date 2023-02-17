(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions fsbigop cardinality set_interval.
From HB Require Import structures.
Require Import reals ereal signed topology numfun normedtype sequences esum.
Require Import measure realfun lebesgue_measure lebesgue_integral charge.

(******************************************************************************)
(*              tentative proof of the Radon-Nikodym Theorem                  *)
(*                                                                            *)
(*  m1 `<< m2 == m1 is absolutely continuous w.r.t. m2 or m2 dominates m1     *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "m1 `<< m2" (at level 51).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*                   lemmas to be moved to other files                        *)
(******************************************************************************)

Lemma lteNy {R : realDomainType} (x : \bar R) : (x < -oo = false)%E.
Proof. by move: x => []. Qed.

Lemma ltye {R : realDomainType} (x : \bar R) : (+oo < x = false)%E.
Proof. by move: x => []. Qed.

(* TODO: move to classical_sets? *)
Section preimage_bool.
Context d (T : measurableType d).
Implicit Type D : set T.

Lemma preimage_mem_true D : mem D @^-1` [set true] = D.
Proof. by apply/seteqP; split => [x/= /set_mem//|x /mem_set]. Qed.

Lemma preimage_mem_false D : mem D @^-1` [set false] = ~` D.
Proof.
apply/seteqP; split => [x/=|x/=]; last exact: memNset.
by apply: contraFnot; exact/mem_set.
Qed.

End preimage_bool.

Lemma set_neg_setC T (f : T -> bool) : [set x | ~~ f x] = ~` [set x | f x].
Proof. by apply/seteqP; split => [x/= /negP//|x/= /negP]. Qed.

Lemma set_eq_leq_lt d (X : porderType d) T (f g : T -> X) :
  [set x | f x = g x] = [set x | (f x <= g x)%O] `\` [set x | (f x < g x)%O].
Proof.
apply/seteqP; split => [x/= ->|x []/=]; first by split => //; rewrite ltxx.
by rewrite le_eqVlt => /orP[/eqP ->|].
Qed.

Lemma set_neq_lt d (X : orderType d) T (f g : T -> X) :
  [set x | f x != g x ] = [set x | (f x > g x)%O] `|` [set x | (f x < g x)%O].
Proof.
apply/seteqP; split => [x/=|]; first by rewrite neq_lt => /orP; tauto.
by move=> x/= /orP; rewrite -neq_lt eq_sym.
Qed.

Section set_lt.
Context (R : realType) T (f g : T -> R).

Let E j := [set x | f x - g x >= j.+1%:R^-1].

Lemma set_lt_bigcup :
  [set x | f x > g x] = \bigcup_j E j.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  by rewrite /E/= -subr_gt0; apply: lt_le_trans; rewrite invr_gt0.
rewrite -subr_gt0 => fgx; exists `|floor (f x - g x)^-1%R|%N => //.
rewrite /E/= -natr1 natr_absz.
rewrite ger0_norm ?floor_ge0 ?invr_ge0; last exact/ltW.
rewrite -[leRHS]invrK lef_pinv//.
- by apply/ltW; rewrite lt_succ_floor.
- by rewrite posrE// ltr_spaddr// ler0z floor_ge0 invr_ge0 ltW.
- by rewrite posrE invr_gt0.
Qed.

End set_lt.

Section eset_lt.
Context (R : realType) T (f g : T -> \bar R).
Local Open Scope ereal_scope.

Let E j := [set x | f x - g x >= j.+1%:R^-1%:E].

Lemma eset_lt_bigcup : [set x | f x > g x] = \bigcup_j E j.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  rewrite /E/= -sube_gt0; apply: lt_le_trans.
  by rewrite lte_fin invr_gt0.
move Hgx : (g x) => gx.
case: gx Hgx => [gx| |gxoo fxoo].
- move Hfx : (f x) => fx.
  case: fx Hfx => [fx Hfx Hgx|fxoo Hgx _|].
  + rewrite lte_fin -subr_gt0 => fgx.
    exists `|floor (fx - gx)^-1%R|%N => //.
    rewrite /E/= -natr1 natr_absz.
    rewrite ger0_norm ?floor_ge0 ?invr_ge0; last exact/ltW.
    rewrite Hfx Hgx lee_fin -[leRHS]invrK lef_pinv//.
    - by apply/ltW; rewrite lt_succ_floor.
    - by rewrite posrE// ltr_spaddr// ler0z floor_ge0 invr_ge0 ltW.
    - by rewrite posrE invr_gt0.
  + by exists 0%N => //; rewrite /E/= fxoo Hgx// addye// leey.
  + by rewrite lteNy.
- by rewrite ltye.
- by exists 0%N => //; rewrite /E/= gxoo addey// ?leey// -ltNye.
Qed.

End eset_lt.

Section move_to_measure.
Local Open Scope ereal_scope.
Context d (X : measurableType d) (R : realType).

Lemma measurable_lt_fun (f g : X -> \bar R) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable [set x | f x < g x].
Proof.
move=> mf mg; under eq_set do rewrite -sube_gt0; rewrite -[X in measurable X]setTI.
by apply: emeasurable_fun_o_infty => //; exact: emeasurable_funB.
Qed.

Lemma measurable_le_fun (f g : X -> \bar R) :
  measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x <= g x].
Proof.
move=> mf mg; under eq_set do rewrite leNgt.
by rewrite set_neg_setC; apply: measurableC; exact : measurable_lt_fun.
Qed.

Lemma measurable_eq_fun (f g : X -> \bar R) :
  measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x = g x].
Proof.
move=> mf mg; rewrite set_eq_leq_lt.
by apply: measurableD; [exact : measurable_le_fun|exact : measurable_lt_fun].
Qed.

Lemma measurable_neq_fun (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x != g x].
Proof.
by move=> mf mg; rewrite set_neq_lt; apply: measurableU; apply: measurable_lt_fun.
Qed.

Lemma measurable_fun_bigcup (n : nat) (E : (set X)^nat)
  (mu : {measure set X -> \bar R}) (f : X -> \bar R) :
  (forall i, measurable (E i) /\ measurable_fun (E i) f) ->
     measurable_fun (\bigcup_i E i) f.
Proof.
move=> mfE mE /= Y mY; rewrite setI_bigcupl; apply: bigcup_measurable => i _.
by apply mfE => //; apply mfE.
Qed.

End move_to_measure.

Local Open Scope ereal_scope.

Lemma positive_set_measurable d (T : measurableType d) (R : realType)
  (nu : {charge set T -> \bar R}) (P : set T) :
  positive_set nu P -> measurable P.
Proof. by case. Qed.

Lemma negative_set_measurable d (T : measurableType d) (R : realType)
  (nu : {charge set T -> \bar R}) (P : set T) :
  negative_set nu P -> measurable P.
Proof. by case. Qed.

(******************************************************************************)
(*                  /lemmas to be moved to other files                        *)
(******************************************************************************)

(******************************************************************************)
(*                        Radon-Nikodym starts here                           *)
(******************************************************************************)

Definition measure_of_charge d (T : measurableType d) (R : realType)
  (nu : set T -> \bar R) of (forall E, 0 <= nu E) := nu.

Section measure_of_charge.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.
Hypothesis nupos : forall E, 0 <= nu E.

Local Notation mu := (measure_of_charge nupos).

Let mu0 : mu set0 = 0. Proof. exact: charge0. Qed.

Let mu_ge0 S : 0 <= mu S.
Proof. by rewrite nupos. Qed.

Let mu_sigma_additive : semi_sigma_additive mu.
Proof. exact: charge_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build d R T (measure_of_charge nupos)
  mu0 mu_ge0 mu_sigma_additive.

Lemma measure_of_chargeE S : mu S = nu S. Proof. by []. Qed.

End measure_of_charge.
Arguments measure_of_charge {d T R}.

(* TODO: move to measure.v? *)
Section absolute_continuity.
Context d (T : measurableType d) (R : realType).
Implicit Types m : set T -> \bar R.

Definition dominates m1 m2 :=
  forall A, measurable A -> m2 A = 0 -> m1 A = 0.

Local Notation "m1 `<< m2" := (dominates m1 m2).

Lemma dominates_trans m1 m2 m3 : m1 `<< m2 -> m2 `<< m3 -> m1 `<< m3.
Proof. by move=> m12 m23 A mA /m23-/(_ mA) /m12; exact. Qed.

End absolute_continuity.
Notation "m1 `<< m2" := (dominates m1 m2).

Definition crestr0 d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) :=
    fun X => if X \in measurable then f (X `&` D) else 0.

Section charge_restriction0.
Context d (T : measurableType d) (R : realFieldType).
Variables (mu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr0 mu mD).

Let crestr0_fin_num_fun : fin_num_fun restr.
Proof.
move=> U mU; rewrite /crestr0 mem_set//.
suff : measurable (U `&` D) by move/(@fin_num_measure _ _ _ mu).
exact: measurableI.
Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  restr crestr0_fin_num_fun.

Let crestr0_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /crestr0 mem_set//.
under [RHS]eq_bigr do rewrite mem_set//.
rewrite -(charge_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite big_distrl.
Qed.

HB.instance Definition _ := isAdditiveCharge.Build _ _ _ restr crestr0_additive.

Let crestr0_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /crestr0 setI_bigcupl ifT ?inE//.
under [X in X --> _]eq_fun do under eq_bigr do rewrite mem_set//.
apply: charge_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ restr crestr0_sigma_additive.

End charge_restriction0.

(* NB: move with Hahn decomposition? *)
Section jordan_decomposition.
Context d (X : measurableType d) (R : realType).
Variable nu : {charge set X -> \bar R}.
Variables P N : set X.
Hypothesis nuPN : hahn_decomposition nu P N.

Let mP : measurable P. Proof. by have [[mP _] _ _ _] := nuPN. Qed.

Let mN : measurable N. Proof. by have [_ [mN _] _ _] := nuPN. Qed.

Definition cjordan_pos : {charge set X -> \bar R} :=
  [the charge _ _ of crestr0 nu mP].

Let positive_set_cjordan_pos E : 0 <= cjordan_pos E.
Proof.
have [posP _ _ _] := nuPN.
rewrite /cjordan_pos/= /crestr0/=; case: ifPn => // /[1!inE] mE.
by apply posP; [apply: measurableI|apply: subIsetr].
Qed.

Definition jordan_pos := measure_of_charge _ positive_set_cjordan_pos.

HB.instance Definition _ := Measure.on jordan_pos.

Let finite_jordan_pos : fin_num_fun jordan_pos.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_pos finite_jordan_pos.

Definition cjordan_neg : {charge set X -> \bar R} :=
  [the charge _ _ of cscale (-1) [the charge _ _ of crestr0 nu mN]].

Let positive_set_cjordan_neg E : 0 <= cjordan_neg E.
Proof.
rewrite /cjordan_neg/= /cscale/= /crestr0/= muleC mule_le0//.
case: ifPn => // /[1!inE] mE.
by move: nuPN => [_ [_ +] _ _] => -> //; exact: measurableI.
Qed.

Definition jordan_neg := measure_of_charge _ positive_set_cjordan_neg.

HB.instance Definition _ := Measure.on jordan_neg.

Let finite_jordan_neg : fin_num_fun jordan_neg.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_neg finite_jordan_neg.

Lemma jordan_decomp A : measurable A -> nu A = jordan_pos A - jordan_neg A.
Proof.
move=> mA; rewrite /jordan_pos /jordan_neg/= /measure_of_charge/= /cscale/= /crestr0/=.
rewrite mem_set// -[in LHS](setIT A).
case: nuPN => _ _ <- PN0; rewrite setIUr chargeU//; last 3 first.
  exact: measurableI.
  exact: measurableI.
  by rewrite setIACA PN0 setI0.
by rewrite EFinN mulN1e oppeK.
Qed.

Lemma jordan_pos_dominates (mu : {measure set X -> \bar R}) :
  nu `<< mu -> jordan_pos `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
rewrite jordan_decomp// /jordan_pos /jordan_neg /measure_of_charge/=.
rewrite /cscale/= /crestr0/= mem_set//.
rewrite EFinN mulN1e oppeK.
have mAP : measurable (A `&` P).
  by apply: measurableI => //; exact: positive_set_measurable posP.
suff : mu (A `&` P) = 0 by move=> /(nu_mu _ mAP) ->.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

Lemma jordan_neg_dominates (mu : {measure set X -> \bar R}) :
  nu `<< mu -> jordan_neg `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
rewrite jordan_decomp// /jordan_pos /jordan_neg /measure_of_charge/=.
rewrite /cscale/= /crestr0/= mem_set//.
have mAN : measurable (A `&` N).
  by apply: measurableI => //; exact: negative_set_measurable negN.
suff : mu (A `&` N) = 0 by move=> /(nu_mu _ mAN) ->; rewrite mule0.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

End jordan_decomposition.

(* uniqueness of RN derivative up-to almost-everywhere equality *)
Section integral_ae_eq.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Let integral_measure_lt (g f : T -> \bar R) :
  mu.-integrable setT f -> mu.-integrable setT g ->
  (forall E, measurable E -> \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  mu [set x | g x < f x] = 0.
Proof.
move=> mf mg fg.
pose E j := [set x | f x - g x >= j.+1%:R^-1%:E].
have mE j : measurable (E j).
  rewrite /E -[X in measurable X]setTI.
  apply: emeasurable_fun_c_infty => //.
  apply: emeasurable_funD => //; first by case: mf.
  by apply: emeasurable_funN => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite eq_le measure_ge0// andbT.
  have fg0 : \int[mu]_(x in E j) (f \- g) x = 0.
    rewrite integralB//; last 2 first.
      exact: integrableS mf.
      exact: integrableS mg.
    rewrite fg// subee// fin_num_abs (le_lt_trans (le_abse_integral _ _ _))//.
      exact: measurable_funS mg.1.
    case: mg => mg; apply: le_lt_trans.
    by apply: subset_integral => //; exact/measurable_funT_comp.
  have : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    apply: (@le_trans _ _ ((j.+1%:R)%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)).
      by rewrite integral_cst// muleA -EFinM divrr ?unitfE// mul1e.
    rewrite lee_pmul//; first exact: integral_ge0.
    apply: ge0_le_integral => //.
    - exact: measurable_fun_cst.
    - by move=> x; rewrite /E/=; apply: le_trans.
    - by apply: emeasurable_funB; [case: mf => + _|case: mg => + _];
        exact: measurable_funS.
  by rewrite fg0 mule0.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x; rewrite /E/=; apply: le_trans.
  by rewrite lee_fin lef_pinv// ?posrE// ler_nat.
rewrite eset_lt_bigcup.
suff: mu (\bigcup_j E j) = 0 by [].
have /cvg_lim h1 : mu \o E --> 0.
  by apply: cvg_near_cst; apply: nearW.
have := @nondecreasing_cvg_mu _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
move/cvg_lim => h2.
by rewrite -h2// h1.
Qed.

Lemma integral_ae_eq (g f : T -> \bar R) :
  mu.-integrable setT f -> mu.-integrable setT g ->
  (forall E, measurable E -> \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  ae_eq mu setT f g.
Proof.
move=> mf mg fg.
have mugf : mu [set x | g x < f x] = 0.
  by apply: integral_measure_lt.
have mufg : mu [set x | f x < g x] = 0.
  by apply: integral_measure_lt => // E mE; rewrite fg.
have h : ~` [set x | [set: T] x -> f x = g x] = [set x | f x != g x].
  by apply/seteqP; split => [x/= ?|x/= /eqP]; [apply/eqP; tauto|tauto].
apply/negligibleP.
  by rewrite h; apply: measurable_neq_fun; [case: mf|case: mg].
rewrite h; rewrite set_neq_lt measureU//; last 3 first.
  by apply: measurable_lt_fun; [case: mg|case: mf].
  by apply: measurable_lt_fun; [case: mf|case: mg].
  by apply/seteqP; split => x//=[/lt_trans] => /[apply]; rewrite ltxx.
by rewrite [X in X + _]mugf add0e [LHS]mufg.
Qed.

End integral_ae_eq.

(* preparation of the elements of the proof of Radon-Nikodym *)
Section approxRN_measure.
Context d (X : measurableType d) (R : realType).
Variables mu nu : {measure set X -> \bar R}.

Definition approxRN := [set g : X -> \bar R | [/\
  forall x, 0 <= g x, mu.-integrable setT g &
  forall E, measurable E -> \int[mu]_(x in E) g x <= nu E] ].

Let approxRN_neq0 : approxRN !=set0.
Proof.
exists (cst 0); split => //; first exact: integrable0.
by move=> E mE; rewrite integral0 measure_ge0.
Qed.

Definition int_approxRN := [set \int[mu]_x g x | g in approxRN].

Definition sup_int_approxRN := ereal_sup int_approxRN.

Local Notation M := sup_int_approxRN.

Definition sup_int_approxRN_ge0 : 0 <= M.
Proof.
rewrite -(ereal_sup1 0) le_ereal_sup// sub1set inE.
exists (fun=> 0); last exact: integral0.
by split => //; [exact: integrable0|move=> E; rewrite integral0].
Qed.

End approxRN_measure.

Section approxRN_finite_measure.
Context d (X : measurableType d) (R : realType).
Variable mu : {measure set X -> \bar R}.
Variable nu : {finite_measure set X -> \bar R}.

Local Notation approxRN := (approxRN mu nu).
Local Notation int_approxRN := (int_approxRN mu nu).
Local Notation M := (sup_int_approxRN mu nu).

Let int_approxRN_ub : exists M, forall x, x \in int_approxRN -> x <= M%:E.
Proof.
exists (fine (nu setT)) => x /[1!inE] -[g [g0 g1 g2] <-{x}].
by rewrite fineK ?fin_num_measure// (le_trans (g2 setT _))// inE.
Qed.

Definition sup_int_approxRN_lty : M < +oo.
Proof.
rewrite /sup_int_approxRN; have [m hm] := int_approxRN_ub.
rewrite (@le_lt_trans _ _ m%:E)// ?ltey// ub_ereal_sup// => x IGx.
by apply: hm; rewrite inE.
Qed.

Definition sup_int_approxRN_fin_num : M \is a fin_num.
Proof.
rewrite ge0_fin_numE//; first exact: sup_int_approxRN_lty.
exact: sup_int_approxRN_ge0.
Qed.

Lemma approxRN_seq_ex : { g : (X -> \bar R)^nat |
  forall k, g k \in approxRN /\ \int[mu]_x g k x > M - k.+1%:R^-1%:E }.
Proof.
pose P m g := g \in approxRN /\ M - m.+1%:R^-1%:E < \int[mu]_x g x.
suff : { g : (X -> \bar R) ^nat & forall m, P m (g m)} by case => g ?; exists g.
apply: (@choice _ _ P) => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ int_approxRN) : (0 < m.+1%:R^-1 :> R)%R.
  by rewrite invr_gt0.
move/(_ sup_int_approxRN_fin_num) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition approxRN_seq : (X -> \bar R)^nat := sval approxRN_seq_ex.

Local Notation g_ := approxRN_seq.

Lemma approxRN_seq_prop : forall m,
  g_ m \in approxRN /\ \int[mu]_x (g_ m x) > M - m.+1%:R^-1%:E.
Proof. exact: (projT2 approxRN_seq_ex). Qed.

Lemma approxRN_seq_ge0 x n : 0 <= g_ n x.
Proof. by have [+ _]:= approxRN_seq_prop n; rewrite inE /= => -[]. Qed.

Lemma measurable_approxRN_seq n : measurable_fun setT (g_ n).
Proof. by have := approxRN_seq_prop n; rewrite inE /= => -[[_ []]]. Qed.

Definition max_approxRN_seq n x :=
  \big[maxe/-oo]_(j < n.+1) g_ j x.

Local Notation F_ := max_approxRN_seq.

Lemma measurable_max_approxRN_seq n : measurable_fun setT (F_ n).
Proof.
elim: n => [|n ih].
  rewrite /max_approxRN_seq.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := approxRN_seq_prop 0%N.
  by rewrite inE /= => -[]// _ _ _; exact: measurable_approxRN_seq.
rewrite /max_approxRN_seq => m.
under eq_fun do rewrite big_ord_recr.
by apply: emeasurable_fun_max => //; exact: measurable_approxRN_seq.
Qed.

Lemma max_approxRN_seq_ge0 n x : 0 <= F_ n x.
Proof.
by apply/bigmax_geP; right => /=; exists ord0 => //; exact: approxRN_seq_ge0.
Qed.

Lemma max_approxRN_seq_ge n x : F_ n x >= g_ n x.
Proof. by apply/bigmax_geP; right => /=; exists ord_max. Qed.

Lemma max_approxRN_seq_nd x : nondecreasing_seq (F_ ^~ x).
Proof. by move=> a b ab; rewrite (le_bigmax_ord xpredT (g_ ^~ x)). Qed.

Lemma is_cvg_max_approxRN_seq n : cvg (F_ ^~ n).
Proof. by apply: ereal_nondecreasing_is_cvg; exact: max_approxRN_seq_nd. Qed.

Lemma is_cvg_int_max_approxRN_seq A :
  measurable A -> cvg (fun n => \int[mu]_(x in A) F_ n x).
Proof.
move=> mA; apply: ereal_nondecreasing_is_cvg => a b ab.
apply: ge0_le_integral => //.
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by apply: measurable_funS (measurable_max_approxRN_seq a).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- exact: measurable_funS (measurable_max_approxRN_seq b).
- by move=> x _; exact: max_approxRN_seq_nd.
Qed.

Definition is_max_approxRN m j :=
  [set x | F_ m x = g_ j x /\ forall k, (k < j)%N -> g_ k x < g_ j x].

Local Notation E := is_max_approxRN.

Lemma is_max_approxRNE m j :
  E m j = [set x| F_ m x = g_ j x] `&`
    [set x |forall k, (k < j)%nat -> g_ k x < g_ j x].
Proof. by apply/seteqP; split. Qed.

Lemma trivIset_is_max_approxRN n : trivIset setT (E n).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Lemma bigsetU_is_max_approx_RN m : \big[setU/set0]_(j < m.+1) E m j = [set: X].
Proof.
apply/seteqP; split => // x _; rewrite -bigcup_mkord.
pose j := [arg max_(j > @ord0 m) g_ j x]%O.
have j0_proof : exists k, (k < m.+1)%N && (g_ k x == g_ j x).
  by exists j => //; rewrite eqxx andbT.
pose j0 := ex_minn j0_proof.
have j0m : (j0 < m.+1)%N by rewrite /j0; case: ex_minnP => // ? /andP[].
have j0max k : (k < j0)%N -> g_ k x < g_ j0 x.
  rewrite /j0; case: ex_minnP => //= j' /andP[j'm j'j] h kj'.
  rewrite lt_neqAle; apply/andP; split; last first.
    rewrite (eqP j'j) /j; case: arg_maxP => //= i _.
    by move/(_ (Ordinal (ltn_trans kj' j'm))); exact.
  apply/negP => /eqP gkj'.
  have := h k; rewrite -(eqP j'j) -gkj' eqxx andbT (ltn_trans kj' j'm).
  by move=> /(_ erefl); rewrite leqNgt kj'.
exists j0 => //; split.
  rewrite /F_ /max_approxRN_seq (bigmax_eq_arg _ ord0)//; last first.
    by move=> ? _; rewrite leNye.
  rewrite /j0/=; case: ex_minnP => //= j' /andP[j'm /eqP].
  by rewrite /g_ => -> h.
by move=> k kj; exact: j0max.
Qed.

Lemma measurable_is_max_approx_RN m j : measurable (E m j).
Proof.
rewrite is_max_approxRNE; apply: measurableI => /=.
  by apply: measurable_eq_fun; [exact: measurable_max_approxRN_seq|
                             exact: measurable_approxRN_seq].
(* TODO : want to use \bigcap_(k < j) [set x | g k x < g j x]) *)
rewrite [T in measurable T](_ : _ = \bigcap_(k in `I_j) [set x | g_ k x < g_ j x]).
  apply: bigcap_measurable => k _; apply: measurable_lt_fun => //;
  exact: measurable_approxRN_seq.
by apply/seteqP; split.
Qed.

End approxRN_finite_measure.

(* main lemma for Radon-Nikodym *)
Section radon_nikodym_finite_ge0.
Context d (X : measurableType d) (R : realType).
Variables mu nu : {finite_measure set X -> \bar R}.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.
Let g := approxRN_seq mu nu.
Let F := max_approxRN_seq mu nu.
Let f := fun x => lim (F ^~ x).

Let mf : measurable_fun setT f.
Proof.
rewrite (_ : f = fun x => lim_esup (F ^~ x)).
  by apply: measurable_fun_lim_esup => // n; exact: measurable_max_approxRN_seq.
by apply/funext=> n; rewrite is_cvg_lim_esupE//; exact: is_cvg_max_approxRN_seq.
Qed.

Let f_ge0 x : 0 <= f x.
Proof.
apply: lime_ge => //; first exact: is_cvg_max_approxRN_seq.
by apply: nearW => ?; exact: max_approxRN_seq_ge0.
Qed.

Let int_fE A : measurable A ->
  \int[mu]_(x in A) f x = lim (fun n => \int[mu]_(x in A) F n x).
Proof.
move=> mA; rewrite monotone_convergence// => n.
- exact: measurable_funS (measurable_max_approxRN_seq mu nu n).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by move=> ?; exact: max_approxRN_seq_nd.
Qed.

Let E m j := is_max_approxRN mu nu m j.

Let int_F_nu m A (mA : measurable A) : \int[mu]_(x in A) F m x <= nu A.
Proof.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) \int[mu]_(x in (A `&` E m j)) F m x);
    last first.
  rewrite -[in LHS](setIT A) -(bigsetU_is_max_approx_RN mu nu m) big_distrr/=.
  rewrite (@ge0_integral_bigsetU _ _ _ _ (fun n => A `&` E m n))//.
  - by move=> n; apply: measurableI => //; exact: measurable_is_max_approx_RN.
  - apply: (@measurable_funS _ _ _ _ setT) => //.
    exact: measurable_max_approxRN_seq.
  - by move=> ? ?; exact: max_approxRN_seq_ge0.
  - apply: trivIset_setIl; apply: (@sub_trivIset _ _ _ setT (E m)) => //.
    exact: trivIset_is_max_approxRN.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) (\int[mu]_(x in (A `&` (E m j))) g j x));
    last first.
  apply: eq_bigr => i _; apply:eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite /F Fmgi lexx.
rewrite [leRHS](_ : _ = \sum_(j < m.+1) (nu (A `&` E m j))); last first.
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => A `&` E m i))//.
  - by rewrite -big_distrr/= bigsetU_is_max_approx_RN// setIT.
  - by move=> k; apply: measurableI => //; exact: measurable_is_max_approx_RN.
  - by apply: trivIset_setIl => //; exact: trivIset_is_max_approxRN.
  - apply: bigsetU_measurable => /= i _; apply: measurableI => //.
    exact: measurable_is_max_approx_RN.
apply: lee_sum => //= i _.
have [+ _] := approxRN_seq_prop mu nu i.
rewrite inE /G/= => -[_ _]; apply.
by apply: measurableI => //; exact: measurable_is_max_approx_RN.
Qed.

Let F_G m : F m \in G.
Proof.
rewrite inE /G/=; split => //.
- by move=> ?; exact: max_approxRN_seq_ge0.
- split; first exact: measurable_max_approxRN_seq.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; last exact: max_approxRN_seq_ge0; over.
  have /le_lt_trans := int_F_nu m measurableT; apply.
  by apply: fin_num_fun_lty; exact: fin_num_measure.
- by move=> A; exact: int_F_nu.
Qed.

Let M_g_F m : M - m.+1%:R^-1%:E < \int[mu]_x g m x /\
              \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := approxRN_seq_prop mu nu m.
apply/andP; split; last first.
  by apply: ereal_sup_ub; exists (F m)  => //; have := F_G m; rewrite inE.
apply: ge0_le_integral => //.
- by move=> x _; exact: approxRN_seq_ge0.
- exact: measurable_approxRN_seq.
- by move=> ? *; exact: max_approxRN_seq_ge0.
- exact: measurable_max_approxRN_seq.
- by move=> ? _; exact: max_approxRN_seq_ge.
Qed.

Let int_foo : \int[mu]_x `|f x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last exact: sup_int_approxRN_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; last exact: f_ge0; over.
rewrite int_fE// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; have [_ /andP[_ ]] := M_g_F n.
Qed.

Let int_f_nu A : measurable A -> \int[mu]_(x in A) f x <= nu A.
Proof.
move=> mA; rewrite int_fE// lime_le //; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; exact: int_F_nu.
Qed.

Let int_f_M : \int[mu]_x f x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_fE// lime_le //; first exact: is_cvg_int_max_approxRN_seq.
  by apply: nearW => n; have [_ /andP[_]] := M_g_F n.
rewrite int_fE//.
have cvgM : (fun m => M - m.+1%:R^-1%:E) --> M.
  rewrite -[X in _ --> X]sube0; apply: cvgeB.
  + by rewrite fin_num_adde_defl.
  + exact: cvg_cst.
  + apply/fine_cvgP; split; first exact: nearW.
    rewrite [X in X @ _ --> _](_ : _ = (fun x => x.+1%:R^-1))//.
    apply/gtr0_cvgV0; first exact: nearW.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = fun n => n + 1)%N; first exact: cvg_addnr.
    by apply/funext => n; rewrite addn1.
apply: (@le_trans _ _ (lim (fun m => M - m.+1%:R^-1%:E))).
  by move/cvg_lim : cvgM => ->.
apply: lee_lim; [by apply/cvg_ex; exists M|exact: is_cvg_int_max_approxRN_seq|].
apply: nearW => m.
by have [/[swap] /andP[? _] /ltW/le_trans] := M_g_F m; exact.
Qed.

Section ab_absurdo.
Context A (mA : measurable A) (h : \int[mu]_(x in A) f x < nu A).

Lemma epsRN_ex :
  {eps : {posnum R} | \int[mu]_(x in A) (f x + eps%:num%:E) < nu A}.
Proof.
have [muA0|] := eqVneq (mu A) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _; rewrite -(@gee0_abs _ (_ + _)); last by rewrite adde_ge0.
    over.
  rewrite (@integral_abs_eq0 _ _ _ _ setT)//.
    by rewrite (le_lt_trans _ h)// integral_ge0.
  by apply: emeasurable_funD => //; exact: measurable_fun_cst.
rewrite neq_lt ltNge measure_ge0//= => muA_gt0.
pose mid := ((fine (nu A) - fine (\int[mu]_(x in A) f x)) / 2)%R.
pose e := (mid / fine (mu A))%R.
have ? : \int[mu]_(x in A) f x \is a fin_num.
  by rewrite ge0_fin_numE// ?(lt_le_trans h)// ?leey// integral_ge0.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last first.
    by rewrite fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
  by rewrite divr_gt0// subr_gt0// fine_lt// fin_num_measure.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mf.
  exact: measurable_fun_cst.
rewrite integral_cst// -lte_subr_addr//; last first.
  by rewrite fin_numM// fin_num_measure.
rewrite -[X in _ * X](@fineK _ (mu A)) ?fin_num_measure//.
rewrite -EFinM -mulrA mulVr ?mulr1; last first.
  by rewrite unitfE gt_eqF// fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
rewrite lte_subr_addl// addeC -lte_subr_addl//; last first.
rewrite -(@fineK _ (nu A))// ?fin_num_measure// -[X in _ - X](@fineK _)// -EFinB lte_fin.
by rewrite /mid ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// subr_gt0 fine_lt// fin_num_measure.
Qed.

Definition epsRN := sval epsRN_ex.

Definition sigmaRN B := nu B - \int[mu]_(x in B) (f x + epsRN%:num%:E).

Let fin_num_int_f_eps B : measurable B ->
  \int[mu]_(x in B) (f x + epsRN%:num%:E) \is a fin_num.
Proof.
move=> mB; rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mf.
  exact/EFin_measurable_fun/measurable_fun_cst.
rewrite fin_numD integral_cst// fin_numM ?fin_num_measure// andbT.
rewrite ge0_fin_numE ?measure_ge0//; last exact: integral_ge0.
rewrite (le_lt_trans _ int_foo)//.
under [in leRHS]eq_integral do rewrite gee0_abs//.
exact: subset_integral.
Qed.

Let fin_num_sigmaRN B : measurable B -> sigmaRN B \is a fin_num.
Proof.
move=> mB; rewrite /sigmaRN fin_numB fin_num_measure//=.
exact: fin_num_int_f_eps.
Qed.

HB.instance Definition _ :=
  @SigmaFinite_isFinite.Build _ _ _ sigmaRN fin_num_sigmaRN.

Let sigmaRN_semi_additive : semi_additive sigmaRN.
Proof.
move=> H n mH tH mUH.
rewrite /sigmaRN measure_semi_additive// big_split/= fin_num_sumeN; last first.
  by move=> i _; rewrite fin_num_int_f_eps.
congr (_ - _); rewrite ge0_integral_bigsetU//.
- rewrite -bigcup_mkord.
  have : measurable_fun setT (fun x => f x + epsRN%:num%:E).
    apply: emeasurable_funD => //.
    exact/EFin_measurable_fun/measurable_fun_cst.
  exact: measurable_funS.
- by move=> x _; rewrite adde_ge0.
- exact: sub_trivIset tH.
Qed.

HB.instance Definition _ :=
  @isAdditiveCharge.Build _ _ _ sigmaRN sigmaRN_semi_additive.

Let sigmaRN_semi_sigma_additive : semi_sigma_additive sigmaRN.
Proof.
move=> H mH tH mUH.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(0 <= i < n) nu (H i) -
  \sum_(0 <= i < n) \int[mu]_(x in H i) (f x + epsRN%:num%:E))); last first.
  apply/funext => n; rewrite big_split/= fin_num_sumeN// => i _.
  by rewrite fin_num_int_f_eps.
apply: cvgeB.
- by rewrite adde_defC fin_num_adde_defl// fin_num_measure.
- exact: measure_semi_sigma_additive.
- rewrite (ge0_integral_bigcup mH _ _ tH).
  + have /cvg_ex[/= l hl] : cvg (fun x =>
        \sum_(0 <= i < x) \int[mu]_(y in H i) (f y + epsRN%:num%:E)).
      apply: is_cvg_ereal_nneg_natsum => n _.
      by apply: integral_ge0 => x _; rewrite adde_ge0.
    by rewrite (@cvg_lim _ _ _ _ _ _ l).
  + split.
      suff: measurable_fun setT (fun x => f x + epsRN%:num%:E).
        exact: measurable_funS.
      apply: emeasurable_funD => //.
      exact/EFin_measurable_fun/measurable_fun_cst.
    apply: (@le_lt_trans _ _ (\int[mu]_(x in \bigcup_k H k) `|f x| +
       \int[mu]_(x in \bigcup_k H k)`| epsRN%:num%:E |)).
      rewrite -(integralD mUH); last 2 first.
        * apply: integrable_abse; split; first exact: measurable_funS mf.
          rewrite (le_lt_trans _ int_foo)// subset_integral//.
          exact: measurable_funT_comp.
        * apply: integrable_abse.
          split; first exact/EFin_measurable_fun/measurable_fun_cst.
          by rewrite integral_cst//= lte_mul_pinfty// ltey_eq fin_num_measure.
      apply: ge0_le_integral => //.
      * apply: measurable_funT_comp => //.
        apply: emeasurable_funD => //; first exact: measurable_funS mf.
        exact/EFin_measurable_fun/measurable_fun_cst.
      * apply: emeasurable_funD => //.
          apply: measurable_funT_comp => //; first exact: measurable_funS mf.
        apply: measurable_funT_comp => //.
        exact/EFin_measurable_fun/measurable_fun_cst.
      * by move=> x _; exact: lee_abs_add.
    apply: lte_add_pinfty.
      rewrite (le_lt_trans _ int_foo)// subset_integral//.
      exact: measurable_funT_comp.
    by rewrite integral_cst//= lte_mul_pinfty// ltey_eq fin_num_measure.
  + by move=> x _; rewrite adde_ge0.
Qed.

HB.instance Definition _ := @isCharge.Build _ _ _ sigmaRN
  sigmaRN_semi_sigma_additive.

End ab_absurdo.

Lemma radon_nikodym_finite_ge0 : nu `<< mu -> exists f : X -> \bar R,
  [/\ forall x, f x >= 0, mu.-integrable setT f &
      forall E, measurable E -> nu E = \int[mu]_(x in E) f x].
Proof.
move=> nu_mu; exists f; split => // A mA.
apply/eqP; rewrite eq_le int_f_nu// andbT leNgt; apply/negP => abs.
pose sigma : {charge set X -> \bar R} :=
  [the {charge set X -> \bar R} of sigmaRN mA abs].
have [P [N [[mP posP] [mN negN] PNX PN0]]] := Hahn_decomposition sigma.
pose AP := A `&` P.
have mAP : measurable AP by exact: measurableI.
have muAP_gt0 : 0 < mu AP.
  rewrite lt_neqAle measure_ge0// andbT eq_sym.
  apply/eqP/(contra_not (nu_mu _ mAP))/eqP; rewrite gt_eqF //.
  rewrite (@lt_le_trans _ _ (sigma AP))//.
    rewrite (@lt_le_trans _ _ (sigma A))//; last first.
      rewrite (charge_partition _ _ mP mN)// gee_addl//.
      by apply: negN => //; exact: measurableI.
    by rewrite sube_gt0// (proj2_sig (epsRN_ex mA abs)).
  rewrite /sigma/= /sigmaRN lee_subel_addl ?fin_num_measure//.
  by rewrite lee_paddl// integral_ge0// => x _; rewrite adde_ge0.
pose h x := if x \in AP then f x + (epsRN mA abs)%:num%:E else f x.
have mh : measurable_fun setT h.
  apply: (@measurable_fun_if _ _ _ _ _ _ _ _ (mem AP))=> //.
      apply: (@measurable_fun_bool _ _ _ _ true).
      by rewrite preimage_mem_true.
    apply: measurable_funTS; apply: emeasurable_funD => //.
    exact: measurable_fun_cst.
  exact: measurable_funTS.
have hge0 x : 0 <= h x by rewrite /h; case: ifPn => // _; rewrite adde_ge0.
have hnuP S : measurable S -> S `<=` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS SAP.
  have : 0 <= sigma S.
    apply: posP => //.
    by apply: (subset_trans SAP); exact: subIsetr.
  rewrite sube_ge0; last by rewrite fin_num_measure// orbT.
  apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite -{1}(setIid S) integral_mkcondr; apply/eq_integral => x /[!inE] Sx.
  by rewrite /restrict /h !ifT// inE//; exact: SAP.
have hnuN S : measurable S -> S `<=` ~` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS ScAP; rewrite /h; under eq_integral.
    move=> x xS; rewrite ifF; last first.
      by apply/negbTE; rewrite notin_set; apply: ScAP; apply: set_mem.
    over.
  exact: int_f_nu.
have hnu S : measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> mS.
  rewrite -(setD0 S) -(setDv AP) setDDr.
  have mSIAP : measurable (S `&` AP) by exact: measurableI.
  have mSDAP : measurable (S `\` AP) by exact: measurableD.
  rewrite integral_setU //; last 2 first.
    - exact: (measurable_funS measurableT).
    - by rewrite disj_set2E setDE setIACA setICl setI0.
  rewrite measureU//.
    by apply: lee_add; [exact: hnuN|exact: hnuP].
  by rewrite setDE setIACA setICl setI0.
have int_h_M : \int[mu]_x h x > M.
  have mCAP := measurableC mAP.
  have disj_AP : [disjoint AP & ~` AP] by exact/disj_set2P/setICr.
  rewrite -(setUv AP) integral_setU ?setUv// /h.
  under eq_integral do rewrite ifT//.
  under [X in _ < _ + X]eq_integral.
    by move=> x; rewrite inE /= => xE0p; rewrite memNset//; over.
  rewrite ge0_integralD//; last 2 first.
    - exact: measurable_funTS.
    - exact: measurable_fun_cst.
  rewrite integral_cst // addeAC -integral_setU ?setUv//.
  rewrite int_f_M -lte_subel_addl; last first.
    by rewrite ge0_fin_numE// ?sup_int_approxRN_lty// sup_int_approxRN_ge0.
  by rewrite /M subee ?mule_gt0// sup_int_approxRN_fin_num.
have Gh : G h.
  split=> //; split => //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite (le_lt_trans (hnu _ measurableT))// ltey_eq fin_num_measure.
have : \int[mu]_x h x <= M.
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  rewrite (@le_ereal_sup _ [set \int[mu]_x h x] (int_approxRN mu nu))//.
  by rewrite sub1set inE; exists h.
by rewrite leNgt int_h_M.
Qed.

End radon_nikodym_finite_ge0.

(* NB: PR in progress *)
Lemma eq_eseriesl (R : realFieldType) (P Q : pred nat) (f : (\bar R)^nat) :
  P =1 Q -> \sum_(i <oo | P i) f i = \sum_(i <oo | Q i) f i.
Proof. by move=> efg; congr (lim _); apply/funext => n; exact: eq_bigl. Qed.
Arguments eq_eseriesl {R P} Q.

Definition mfrestr d (T : measurableType d) (R : realFieldType) (D : set T)
    (f : set T -> \bar R) (mD : measurable D) (moo : f D < +oo) :=
  fun X => f (X `&` D).

Section measure_frestr.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Hypothesis moo : mu D < +oo.

Local Notation restr := (mfrestr mD moo).

Let restr0 : restr set0 = 0%E.
Proof. by rewrite /restr set0I measure0. Qed.

Let restr_ge0 (A : set _) : (0 <= restr A)%E.
Proof.
by rewrite /restr; apply: measure_ge0; apply: measurableI.
Qed.

Let restr_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
by rewrite /restr setI_bigcupl; exact: measure_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ restr
  restr0 restr_ge0 restr_sigma_additive.

Let restr_fin : fin_num_fun restr.
Proof.
move=> U mU; rewrite /restr ge0_fin_numE ?measure_ge0//.
by rewrite (le_lt_trans _ moo)// le_measure// ?inE//; exact: measurableI.
Qed.

HB.instance Definition _ := Measure_isFinite.Build _ _ _ restr
  restr_fin.

End measure_frestr.

Section radon_nikodym.
Context d (X : measurableType d) (R : realType).

Let radon_nikodym_sigma_finite_ge0
    (mu : {sigma_finite_measure set X -> \bar R})
    (nu : {finite_measure set X -> \bar R}) :
  nu `<< mu ->
  exists2 f : X -> \bar R, mu.-integrable setT f &
    forall E, E \in measurable -> nu E = integral mu E f.
Proof.
move=> nu_mu.
have [F TF mFAFfin] := sigma_finiteT mu.
have {mFAFfin}[mF Ffin] := all_and2 mFAFfin.
pose E := seqDU F.
have mE k : measurable (E k).
  by apply: measurableD => //; exact: bigsetU_measurable.
have Efin k : mu (E k) < +oo.
  by rewrite (le_lt_trans _ (Ffin k))// le_measure ?inE//; exact: subDsetl.
have bigcupE : \bigcup_i E i = setT by rewrite TF [RHS]seqDU_bigcup_eq.
have tE := @trivIset_seqDU _ F.
pose mu_ j : {finite_measure set X -> \bar R} :=
  [the {finite_measure set _ -> \bar _} of @mfrestr _ _ _ _ mu (mE j) (Efin j)].
have H1 i : nu (E i) < +oo by rewrite ltey_eq fin_num_measure.
pose nu_ j : {finite_measure set X -> \bar R} :=
  [the {finite_measure set _ -> \bar _} of @mfrestr _ _ _ _ nu (mE j) (H1 j)].
have nu_mu_ k : nu_ k `<< mu_ k.
  by move=> S mS mu_kS0; apply: nu_mu => //; exact: measurableI.
have [g Hg] := choice (fun j => radon_nikodym_finite_ge0 (nu_mu_ j)).
have [g_ge0 integrable_g int_gE {Hg}] := all_and3 Hg.
pose f_ j x := if x \in E j then g j x else 0.
have f_ge0 k x : 0 <= f_ k x by rewrite /f_; case: ifP.
have mf_ k : measurable_fun setT (f_ k).
  apply: (@measurable_fun_if _ _ _ _ _ _ _ _ (mem (E k))) => //.
      by apply: (@measurable_fun_bool _ _ _ _ true); rewrite preimage_mem_true.
    rewrite preimage_mem_true.
    by apply: (measurable_funS measurableT) => //; apply (integrable_g k).
  rewrite preimage_mem_false.
  by apply: (measurable_funS measurableT) => //; exact: measurable_fun_cst.
have int_f_T k : integrable mu setT (f_ k).
  split=> //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -(setUv (E k)) integral_setU //; last 3 first.
    - exact: measurableC.
    - by rewrite setUv.
    - exact/disj_set2P/subsets_disjoint.
  rewrite /f_; under eq_integral do rewrite ifT//.
  rewrite (@eq_measure_integral _ _ _ (E k) (mu_ k)); last first.
    by move=> A mA AEj; rewrite /mu_ /= /mfrestr setIidl.
  rewrite -int_gE ?inE//.
  under eq_integral.
    move=> x /[!inE] /= Ekx; rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 ?adde0 ltey_eq fin_num_measure.
have int_f_E j S : measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)) (integral_setU _ mSIEj mSDEj)//; last 2 first.
    - by rewrite setUIDK; exact: (measurable_funS measurableT).
    - by apply/disj_set2P; rewrite setDE setIACA setICr setI0.
  rewrite /f_ -(eq_integral _ (g j)); last first.
    by move=> x /[!inE] SIEjx; rewrite /f_ ifT// inE; exact: (@subIsetr _ S).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)); last first.
    by move=> A mA; rewrite subsetI => -[_ ?]; rewrite /mu_ /= /mfrestr setIidl.
  rewrite -int_gE; last exact: measurableI.
  under eq_integral.
    move=> x; rewrite inE setDE /= => -[_ Ejx].
    rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 adde0 /nu_/= /mfrestr -setIA setIid.
pose f x : \bar R := \sum_(j <oo) f_ j x.
have int_f_nu : \int[mu]_x f x = nu setT.
  rewrite integral_nneseries//.
  transitivity (\sum_(n <oo) nu (E n)).
    by apply: eq_eseriesr => i _; rewrite int_f_E// setTI.
  rewrite -bigcupE measure_bigcup//.
  by apply: eq_eseriesl => // x; rewrite in_setT.
exists f.
  split; first exact: ge0_emeasurable_fun_sum.
  under eq_integral do (rewrite gee0_abs; last exact: nneseries_ge0).
  by rewrite int_f_nu ltey_eq fin_num_measure.
move=> A /[!inE] mA; rewrite integral_nneseries//; last first.
  by move=> n; exact: (measurable_funS measurableT).
rewrite nneseries_esum; last by move=> m _; rewrite integral_ge0.
under eq_esum do rewrite int_f_E//.
rewrite -nneseries_esum; last first.
  by move=> n; rewrite measure_ge0//; exact: measurableI.
rewrite (eq_eseriesl (fun x => x \in [set: nat])); last by move=> x; rewrite in_setT.
rewrite -measure_bigcup//.
- by rewrite -setI_bigcupr bigcupE setIT.
- by move=> i _; exact: measurableI.
- exact: trivIset_setIl.
Qed.

Theorem Radon_Nikodym
  (mu : {sigma_finite_measure set X -> \bar R}) (nu : {charge set X -> \bar R}) :
  nu `<< mu ->
  exists2 f : X -> \bar R, mu.-integrable setT f &
    forall E, measurable E -> nu E = \int[mu]_(x in E) f x.
Proof.
move=> nu_mu; have [P [N nuPN]] := Hahn_decomposition nu.
have [fp intfp fpE] := @radon_nikodym_sigma_finite_ge0 mu
  [the {finite_measure set _ -> \bar _} of jordan_pos nuPN]
  (jordan_pos_dominates nuPN nu_mu).
have [fn intfn fnE] := @radon_nikodym_sigma_finite_ge0 mu
  [the {finite_measure set _ -> \bar _} of (jordan_neg nuPN)]
  (jordan_neg_dominates nuPN nu_mu).
exists (fp \- fn); first exact: integrableB.
move=> E mE; rewrite [LHS](jordan_decomp nuPN mE)// integralB//.
- by rewrite -fpE ?inE// -fnE ?inE.
- exact: (integrableS measurableT).
- exact: (integrableS measurableT).
Qed.

End radon_nikodym.
