From Coq Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp.
From mathcomp Require Import ring lra.
From mathcomp Require Import classical_sets functions cardinality fsbigop.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences esum measure lebesgue_measure numfun exp.
From mathcomp Require Import trigo realfun charge lebesgue_integral kernel.
From mathcomp Require Import probability prob_lang.
From mathcomp Require Import lang_syntax_util lang_syntax lang_syntax_examples.

(**md**************************************************************************)
(* # Inferring behavior from text-massage data example                        *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - *)
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


Definition neq01 {R : realType} := (@GRing.oner_neq0 R).
Definition exp_normal1 {R g} := (@exp_normal R g _ neq01).

Definition neq0Vsqrt2 {R : realType} : ((@Num.sqrt R 2)^-1 != 0)%R.
Proof. exact: lt0r_neq0. Qed.
Definition exp_normal_Vsqrt2 {R g} := (@exp_normal R g _ neq0Vsqrt2).

Definition neq0sqrt32 {R : realType} : ((@Num.sqrt R (3 / 2)) != 0)%R.
Proof. exact: lt0r_neq0. Qed.
Definition exp_normal_sqrt32 {R g} := (@exp_normal R g _ neq0sqrt32).

(*
Section eq_lebesgue_measure_measurable.
Context {R : realType}.

Local Notation mu := lebesgue_measure.

Variable f : cumulative R.
Hypothesis intf : integrable mu setT (EFin \o f).

Local Notation lsmf := (lebesgue_stieltjes_measure f).

Let fin_lsmf : fin_num_fun lsmf.
Proof.
apply: lty_fin_num_fun.
rewrite /=/lsmf/measure_extension/mu_ext.
Admitted.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _ lsmf fin_lsmf.

Lemma Radon_Nikodym_ae_unique :
  ae_eq mu setT (EFin \o f) ('d lsmf '/d mu).
Proof.
apply: integral_ae_eq => //.
  admit.
move=> E _ mE.
rewrite -Radon_Nikodym_integral//; last first.
  admit.


Lemma eq_lebesgue_measure_measurable (m' : measure _ R) :
sigma_additive m' ->
(forall U : set _, measurable U -> m' U = mu U) ->
m' = mu.
Proof.
move=> sm' H.
apply: eq_measure.
apply/funext => U.
have : setT U by [].
rewrite -(setUv measurable).
move=> [mU|nmU]; first exact: H.
pose e := m' U.
have : m' U = e by [].
Abort.

End eq_lebesgue_measure_measurable.
*)

(* TODO: PR *)
Section ge0_fin_measurable_probability_integrable.
Context d {T : measurableType d} {R : realType} {p : probability T R}
   {f : T -> \bar R}.

Lemma ge0_fin_measurable_probability_integrable :
  (forall x, 0 <= f x) ->
  (exists M : R, forall x, f x <= M%:E) ->
  measurable_fun setT f ->
  p.-integrable setT f.
Proof.
move=> f0 [M fleM] mf.
apply/integrableP; split => //.
apply (@le_lt_trans _ _ (\int[p]_x M%:E)).
  apply: ge0_le_integral => //=.
      exact: measurableT_comp.
    move=> t _.
    exact: (@le_trans _ _ (f t)).
  move=> t _.
  by rewrite gee0_abs.
by rewrite integral_cst// probability_setT mule1 ltry.
Qed.

End ge0_fin_measurable_probability_integrable.

(* TODO: PR *)
Section pkernel_probability_integrable.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  {p : probability T R} {f : R.-pker T ~> T'}.

Lemma pkernel_probability_integrable V :
  measurable V ->
  p.-integrable setT (fun x => f x V).
Proof.
move=> mV.
apply: ge0_fin_measurable_probability_integrable => //.
  exists 1%R.
  move=> x.
  apply: (@le_trans _ _ (f x setT)).
    by apply: le_measure; rewrite ?inE.
  by rewrite prob_kernel.
exact: measurable_kernel.
Qed.

End pkernel_probability_integrable.

(* TODO: move to probability? *)
Section normal_prob_properties.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Local Open Scope charge_scope.

Lemma normal_pdf_uniq_ae (m s : R) (s0 : (0 < s)%R) :
  ae_eq mu setT
   ('d ((charge_of_finite_measure (@normal_prob R m s))) '/d mu)
               (EFin \o (@normal_pdf R m s)).
Proof.
apply: integral_ae_eq => //.
    apply: Radon_Nikodym_integrable => /=.
    exact: normal_prob_dominates.
  apply/measurable_EFinP.
  exact: measurable_normal_pdf.
move=> /= E _ mE.
by rewrite -Radon_Nikodym_integral//=; apply: normal_prob_dominates.
Qed.

End normal_prob_properties.

(*
Section disintegration_measure.
Context {R : realType}.
(* define lebesgue syntax *)

End disintegration_measure.

Section disintegration_program.

Variable l : ctx.

Definition lhs : exp R _  l _ :=
 [let "t" := Sample {exp_normal ltr01 (exp_real 0)} in
  let "p" :=  (* ? TODO *) in
  return (#{"t"}, #{"p"})].

Definition rhs : exp R _ l _ :=
 [let "t" := Sample exp_lebesgue(* TODO *) in
  let "p" := Score (exp_normal_pdf [#{"t"}])) (* TODO *) in
  return (#{"t"}, #{"p"})].

Lemma disintegration_normal :
execD lhs = exec rhs.

End disintegration_program.
*)

Section normal_prob_lemmas.
Context {R: realType}.
Local Notation mu := lebesgue_measure.

(* TODO: move *)
Lemma emeasurable_normal_prob (s : R) U : s != 0%R -> measurable U ->
   measurable_fun setT (fun x => normal_prob x s U).
Proof.
move=> s0 mU.
under [X in _ _ X]eq_fun.
  move=> x.
  rewrite -(@fineK _ (_ x _ _)); last first.
    rewrite ge0_fin_numE//.
    apply: (@le_lt_trans _ _ (normal_prob x s setT)).
      by apply: le_measure; rewrite ?inE.
    by rewrite probability_setT ltry.
  over.
apply/measurable_EFinP.
apply: (continuous_measurable_fun).
exact: normal_prob_continuous.
Qed.

(* TODO: s != 0 *)
Lemma integral_normal_prob (m s : R) (s0 : (0 < s)%R) f U :
  measurable U ->
  (normal_prob m s).-integrable U f ->
  \int[@normal_prob _ m s]_(x in U) f x =
  \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E).
Proof.
move=> mU intf.
move/integrableP : (intf) => [mf intf_lty].
rewrite -(Radon_Nikodym_change_of_variables (normal_prob_dominates m s))//=.
apply: ae_eq_integral => //=.
    apply: emeasurable_funM => //.
    apply: measurable_funTS.
    have : charge_of_finite_measure (normal_prob m s) `<< mu.
      exact: normal_prob_dominates m s.
    move/Radon_Nikodym_integrable.
    by move/integrableP => [].
  apply: emeasurable_funM => //.
  apply/measurable_EFinP.
  apply: measurable_funTS.
  exact: measurable_normal_pdf.
apply: ae_eq_mul2l.
apply: (ae_eq_subset (@subsetT _ U)).
exact: (normal_pdf_uniq_ae m s0).
Qed.

(*
Definition tail1 : @exp R _ [:: ("x", Real)] _ :=
  [let "z" := Sample {exp_normal ltr01 [#{"x"}]} in
   return #{"z"}].

Lemma helloRight01 :
execP [let "x" := Sample {exp_normal ltr01 (exp_real 0)} in
  let "_" := Score {expR 1} `^
                     ({0}:R - (#{"y0"} - #{"x"}) ^+ {2} * {2^-1}:R)
                   * {(Num.sqrt 2 * pi)^-1}:R in
  {exp_weak _ [::] [:: ("x", Real); ("y0", Real)] ("_", Unit)
    (exp_weak _ [:: ("x", Real)] [::] ("y0", Real) tail1 _)}] =
  [let "_" := Score {expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  let "x" := Sample {exp_normal ltr0Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
  {tail1}].
*)

Lemma normal_prob_integrable_dirac (m s : R) (V : set R): measurable V ->
  (normal_prob m s).-integrable setT (fun x => \d_x V).
Proof.
move=> mV.
apply/integrableP; split; first exact: measurable_fun_dirac.
rewrite -(setUv V).
rewrite ge0_integral_setU => //; first last.
      exact/disj_setPCl.
    rewrite setUv.
    apply: measurableT_comp => //.
    exact: measurable_fun_dirac.
  exact: measurableC.
under eq_integral.
  move=> x Vx.
  rewrite diracE Vx/= normr1.
  over.
under [X in _ + X < _]eq_integral.
  move=> x.
  rewrite inE/= => nVx.
  have {}nVx := (memNset nVx).
  rewrite indicE nVx/= normr0.
  over.
rewrite !integral_cst//=; last exact: measurableC.
rewrite mul1e mul0e adde0.
apply: (le_lt_trans (probability_le1 (normal_prob m s) mV)).
exact: ltey.
Qed.

Lemma integral_normal_prob_dirac (s : R) (m : R) V :
  (0 < s)%R ->
  measurable V ->
  \int[normal_prob m s]_x0 (\d_x0 V) = normal_prob m s V.
Proof.
move=> s0 mV.
rewrite integral_normal_prob => //; last exact: (normal_prob_integrable_dirac m s).
under eq_integral do rewrite diracE.
rewrite /normal_prob.
rewrite [in RHS]integral_mkcond.
under [in RHS]eq_integral do rewrite patchE.
rewrite /=.
apply: eq_integral => x _.
by case: ifP => xV/=; rewrite ?mul1e ?mul0e.
Qed.

End normal_prob_lemmas.

Section hello_programs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Definition guard_real {g} str (r : R) :
 @exp R P [:: (str, _) ; g] _ :=
  [if #{str} ==R {r}:R then return TT else Score {0}:R].

Definition helloWrong (y0 : R) : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal1 (exp_real 0)} in
  let "y" := Sample {exp_normal1 [#{"x"}]} in
  let "_" := {guard_real "y" y0} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
  return #{"z"}].

Definition helloRight : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize
  let "x" := Sample {exp_normal1 (exp_real 0)} in
  let "_" := Score ({expR 1} `^
                     ({0}:R - (#{"y0"} - #{"x"}) ^+ {2} * {2^-1}:R))
                   * {(Num.sqrt 2 * pi)^-1}:R in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
 return #{"z"}].

Definition helloJoint : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal1 (exp_real 0)} in
  let "y" := Sample {exp_normal1 [#{"x"}]} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
 return (#{"y"}, #{"z"})].

End hello_programs.

Section helloRight_subproofs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Local Definition int_normal_helloRightP :=
  (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  \int[normal_prob 0 1]_x (fun x0 =>
 `|expR (- ((y.1 - x0) ^+ 2%R / 2)) / Num.sqrt (2 * pi)|%:E * normal_prob x0 1 V) x).

Local Definition int_mu_helloRightP :=
  (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  \int[mu]_x
     (`|expR (- ((y.1 - x) ^+ 2%R / 2)) / Num.sqrt (2 * pi)|%:E * normal_prob x 1 V *
      (normal_pdf 0 1 x)%:E)).

Local Definition int_normal_helloRight1P :=
(fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
(\int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
(((NngNum (normr_ge0 (expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi))))%:num)%:E *
 normal_prob x 1 V)%E)).

Local Definition int_mu_helloRight1P :=
(fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  \int[mu]_x
     (`|expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi)|%:E *
      (normal_prob x 1 V * (normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 x)%:E))).

Local Definition int_normal_helloRight2P :=
(fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  \int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x normal_prob x 1 V).

Local Definition int_mu_helloRight2P :=
(fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  normal_prob (y.1 / 2) (Num.sqrt (3 / 2)) V).

Lemma int_change_helloRightP y V : measurable V ->
int_normal_helloRightP y V = int_mu_helloRightP y V.
Proof.
move=> mV; rewrite /int_normal_helloRightP.
rewrite integral_normal_prob//; first last.
  apply: integrableMr => //.
      apply: (@measurableT_comp _ _ _ _ _ _ (@normr _ R^o)) => //.
      apply: measurable_funM => //.
      apply: measurableT_comp => //.
      apply: measurableT_comp => //.
      apply: measurable_funM => //.
      apply: (@measurableT_comp _ _ _ _ _ _ (fun t : R => (t ^+ 2%R)%R)) => //.
      exact: measurable_funB.
    exists (Num.sqrt (2 * pi))^-1%R; split; first exact: num_real.
    move=> x x_gt.
    move=> p _.
    rewrite /= normr_id.
    have /normr_idP -> : (0 <= expR (- ((y.1 - p) ^+ 2%R / 2)) / (Num.sqrt (2 * pi)))%R.
      apply: mulr_ge0; first exact: expR_ge0.
      by rewrite invr_ge0 sqrtr_ge0// mulr_ge0// pi_ge0.
    apply/ltW.
    apply: le_lt_trans x_gt.
    rewrite -[leRHS]mul1r ler_pM//.
      exact: expR_ge0.
    by rewrite -expR0 ler_expR oppr_le0 mulr_ge0// ?sqr_ge0// expR0 invr_ge0.
  apply/integrableP; split.
    exact: emeasurable_normal_prob.
  apply/abse_integralP => //.
    exact: emeasurable_normal_prob.
  have/gee0_abs -> : 0 <= \int[normal_prob 0 1]_x normal_prob x 1 V.
    exact: integral_ge0.
  apply: (@le_lt_trans _ _ (\int[normal_prob 0 1]_x (cst 1%R x)%:E)).
    apply: ge0_le_integral => //.
        exact: emeasurable_normal_prob.
      apply/measurable_EFinP.
      exact: measurable_cst.
    move=> x _.
    exact: probability_le1.
  by rewrite /= integral_cst// mul1e probability_setT ltry.
Qed.

Lemma int_change_helloRight1P y V : measurable V ->
int_normal_helloRight1P y V = int_mu_helloRight1P y V.
Proof.
move=> mV; rewrite /int_normal_helloRight1P.
rewrite integral_normal_prob//; first last.
  apply/integrableP; split.
    apply: measurable_funeM.
    exact: emeasurable_normal_prob.
  apply: (@le_lt_trans _ _
            (\int[normal_prob (y.1 / 2) (Num.sqrt 2)^-1]_x
   (((NngNum (normr_ge0 (expR (- (y.1 ^+ 2%R / 4)) /
                            Num.sqrt (4 * pi))))%:num)%:E * (cst 1%R x)%:E))).
  apply: ge0_le_integral => //.
          apply: measurableT_comp => //.
          apply: measurable_funeM.
          exact: emeasurable_normal_prob.
        by move=> x _; rewrite /= mule1.
      rewrite /= mule1.
      exact/measurable_EFinP.
    move=> x _/=.
    rewrite gee0_abs; last exact: mule_ge0.
    rewrite lee_pmul//.
    exact: probability_le1.
  rewrite integralZr//; last exact: finite_measure_integrable_cst.
  by rewrite integral_cst// mule1 probability_setT ltry.
by under eq_integral do rewrite -muleA.
Qed.

Lemma int_change_helloRight2P y V :
  measurable V ->
  int_normal_helloRight2P y V = int_mu_helloRight2P y V.
Proof.
move=> mV.
rewrite /int_normal_helloRight2P.
rewrite /int_mu_helloRight2P.
(* rewrite by fubini *)
transitivity (\int[mu]_(z in V)
     \int[mu]_x (
          (normal_pdf x 1 z * normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 x)%:E)).
  rewrite integral_normal_prob//; last first.
    apply: ge0_fin_measurable_probability_integrable => //.
      exists 1%R => ?; exact: probability_le1.
    exact: emeasurable_normal_prob.
  under eq_integral.
    move=> x _.
    rewrite /normal_prob.
    rewrite -integralZr//; last first.
      apply: (integrableS measurableT) => //.
      exact: integrable_normal_pdf.
    under eq_integral.
      move=> z _.
      rewrite -EFinM.
      rewrite [X in X%:E](_:_=
   (fun xz : R * R => (normal_pdf xz.1 1 xz.2 * normal_pdf (y.1 / 2)
                             (Num.sqrt 2)^-1 xz.1)%R) (x, z)); last by [].
      over.
    rewrite integral_mkcond.
    rewrite epatch_indic.
    over.
  rewrite /=.
  rewrite (@fubini_tonelli _ _ _ _ _ mu mu
(EFin \o ((fun xz : R * R => (normal_pdf xz.1 1 xz.2 *
           normal_pdf (y.1 / 2) (Num.sqrt 2)^-1 xz.1)%R * \1_V xz.2)%R)));
  first last.
    move=> x.
    rewrite lee_fin/=.
    apply: mulr_ge0 => //.
    apply: mulr_ge0; exact: normal_pdf_ge0.
  apply/measurable_EFinP.
  apply: measurable_funM; last first.
    apply: measurable_indic.
      rewrite -[X in measurable X]setTX.
      exact: measurableX.
    apply: measurable_funM.
      under [X in measurable_fun _ X]eq_fun.
        move=> x.
        rewrite normal_pdfE//.
        rewrite normal_pdf0_center/=.
        over.
      rewrite /=.
      apply: measurableT_comp.
        exact: measurable_normal_pdf0.
      exact: measurable_funB.
    apply: measurableT_comp => //.
    exact: measurable_normal_pdf.
  under eq_integral.
    move=> x _.
    rewrite /=.
    under eq_integral do rewrite EFinM.
    rewrite -epatch_indic.
    over.
  rewrite /=.
  rewrite [RHS]integral_mkcond/=.
  apply: eq_integral.
  move=> /= x _.
  rewrite patchE.
  case: ifPn => xV.
    apply: eq_integral => z _/=.
    by rewrite ifT.
  apply: integral0_eq => /= z _.
  rewrite ifF//.
  apply/negbTE.
  rewrite notin_setE/=.
  move/negP in xV.
  by move/mem_set.
apply: eq_integral.
move=> x _.
transitivity ((2 * pi * (Num.sqrt 2))^-1%:E *
                \int[mu]_x0 ((expR (- (x - x0) ^+ 2 / 2))%R * expR (- (x0 - (y.1 / 2)) ^+ 2 ))%:E).
  under eq_integral.
    move=> z _.
    rewrite !normal_pdfE//.
    rewrite /normal_pdf0.

    over.
  admit.
rewrite normal_pdfE// /normal_pdf0.
evar (C : Real.sort R).
transitivity (((2 * pi * Num.sqrt 2)^-1)%:E *
  \int[mu]_x0 (expR (- (3 / 2)%R * (x0 - C) ^+ 2 - (x - y.1 / 2) ^+ 2 / (3 / 2 *+ 2)))%:E).
  admit.
(* gauss integral *)
admit.
Admitted.


End helloRight_subproofs.

Section helloRight_proof.
Local Open Scope lang_scope.
Context {R : realType}.

Local Notation mu := lebesgue_measure.

(* TODO: remove P, helloRight -> helloRight0 *)
(* NB: exp_powR level setting is mistaken? *)
(*     ((_ `^ _) * _) cannot write as (_ `^ _ * _) *)
Definition helloRightP : @exp R P [:: ("y0", Real)] Real :=
[let "x" := Sample {exp_normal1 (exp_real 0)} in
 let "_" := Score ({expR 1} `^
                     ({0}:R - (#{"y0"} - #{"x"}) ^+ {2} * {2^-1}:R))
                   * {(Num.sqrt (2 * pi))^-1}:R in
 let "z" := Sample {exp_normal1 [#{"x"}]} in
 return #{"z"}].

(* rename *)
Definition helloRight1P : @exp R _ [:: ("y0", Real)] Real :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
  let "z" := Sample {exp_normal1 [#{"x"}]} in
 return #{"z"}].

Definition helloRight1 : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize {helloRight1P}].

Definition helloRight2P : @exp R _ [:: ("y0", Real)] _ :=
 [let "_" := Score ({expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R)) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  Sample {exp_normal_sqrt32 [#{"y0"} * {2^-1}:R]}]. (* ? *)

Definition helloRight2 : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize {helloRight2P}].

(* TODO: separate program and proof each line
Local Definition helloRightP_line1 :
  forall _, @exp R P [:: ("y0", Real)] Real :=
(fun (t : @exp R P [:: ("x", Real); ("y0", Real)] Real) =>
[let "x" := Sample {exp_normal1 (exp_real 0)} in
 {t}]).
*)

Lemma execP_helloRight12 y V : measurable V ->
 @execP R [:: ("_", Unit); ("y0", Real)] _
   [let "x" := Sample {exp_normal_Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
    let "z" := Sample {exp_normal1 [#{"x"}]} in
    return #{"z"}] y V =
 @execP R [:: ("_", Unit); ("y0", Real)] _
 [Sample {exp_normal_sqrt32 [#{"y0"} * {2^-1}:R]}] y V.
Proof.
move=> mV.
rewrite !execP_letin.
rewrite !execP_sample !execD_normal/=.
rewrite (@execD_bin _ _ binop_mult) execD_real/=.
rewrite execP_return.
rewrite !exp_var'E (execD_var_erefl "y0") (execD_var_erefl "x") (execD_var_erefl "z")/=.
rewrite !letin'E/=.
under eq_integral do rewrite letin'E/=.
rewrite /=.
(* *)
under eq_integral do rewrite integral_normal_prob_dirac//.
exact: (int_change_helloRight2P _ mV).
Qed.

(* ref: https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf
 * p.2, equation (7)
 * change sampling order by bayes' theorem.
 *)

Local Definition executed_helloRightP :=
  (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
   letin'
    (sample (fun=> normal_prob 0 1)
       (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0) (kr 0)))
    (letin'
       (score
          (measurable_funM
             (measurableT_comp (measurable_powRr (expR 1))
                (measurable_funB (kr 0)
                   (measurable_funM
                      (measurable_funX 2%R
                         (measurable_funB (measurable_acc_typ [:: Real; Real] 1)
                            (measurable_acc_typ [:: Real; Real] 0)))
                      (kr 2^-1)))) (kr (Num.sqrt (2 * pi))^-1)))
       (letin'
          (sample
             (fun
                x : unit *
                    (g_sigma_algebraType R.-ocitv.-measurable *
                     (g_sigma_algebraType R.-ocitv.-measurable * unit)) =>
              normal_prob x.2.1 1)
             (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0)
                (measurable_acc_typ [:: Unit; Real; Real] 1)))
        (ret (measurable_acc_typ [:: Real; Unit; Real; Real] 0)))) y V : \bar R).

Local Definition executed_helloRight1P :=
 (fun (y : (@mctx R [:: ("y0", Real)])) (V : set (@mtyp R Real)) =>
  letin'
    (score
       (measurable_funM
          (measurableT_comp (measurable_powRr (expR 1))
             (measurable_funB (kr 0)
                (measurable_funM (measurable_funX 2%R (measurable_acc_typ [:: Real] 0)) (kr 4^-1))))
          (kr (Num.sqrt (4 * pi))^-1)))
    (letin'
       (sample
          (fun x : unit * (g_sigma_algebraType R.-ocitv.-measurable * unit) =>
           probability_normal_prob__canonical__measure_Probability (x.2.1 / 2) (Num.sqrt 2)^-1)
          (measurableT_comp (measurable_normal_prob2 neq0Vsqrt2)
             (measurable_funM (measurable_acc_typ [:: Unit; Real] 1) (kr 2^-1))))
       (letin'
          (sample
             (fun
                x : g_sigma_algebraType R.-ocitv.-measurable *
                    (unit * (g_sigma_algebraType R.-ocitv.-measurable * unit)) =>
              probability_normal_prob__canonical__measure_Probability x.1 1)
             (measurableT_comp (measurable_normal_prob2 GRing.oner_neq0)
                (measurable_acc_typ [:: Real; Unit; Real] 0)))
          (ret (measurable_acc_typ [:: Real; Real; Unit; Real] 0)))) y V : \bar R).

(* TODO: rename, this is step0 of lhs *)
Lemma lhs_execPE y V :
  execP helloRightP y V = executed_helloRightP y V.
Proof.
rewrite !execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite execD_real/=.
rewrite execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execD_real/=.
rewrite execD_real/=.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return/=.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
done.
Qed.

Lemma rhs_execPE y V :
  execP helloRight1P y V = executed_helloRight1P y V.
Proof.
rewrite execP_letin.
rewrite execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite execD_real/=.
rewrite execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
done.
Qed.

Lemma helloRightP_intE y V : measurable V ->
  executed_helloRightP y V = int_normal_helloRightP y V.
Proof.
move=> mV.
rewrite /executed_helloRightP.
rewrite [in LHS]letin'E/=.
under [in LHS]eq_integral.
  move=> x _.
  rewrite letin'E/=.
  under eq_integral.
    move=> u _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//.
    over.
  rewrite /=.
  rewrite ge0_integral_mscale/=; first last.
  - by move=> ? _.
  - by [].
  - exact: measurableT.
  rewrite integral_dirac; first last.
  - by [].
  - exact: measurableT.
  rewrite diracT mul1e.
  rewrite sub0r.
  rewrite -expRM mul1r.
  over.
rewrite /=.
done.
Qed.

Lemma helloRight1P_intE y V : measurable V ->
  executed_helloRight1P y V = int_normal_helloRight1P y V.
Proof.
move=> mV; rewrite /executed_helloRight1P.
rewrite letin'E/=.
under eq_integral.
  move=> u _.
  rewrite letin'E/=.
  under eq_integral.
    move=> x _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//.
    over.
  over.
rewrite ge0_integral_mscale//; first last.
  move=> ? _.
  exact: integral_ge0.
rewrite integral_dirac//.
rewrite diracT mul1e.
rewrite sub0r -expRM mul1r.
rewrite /=.
rewrite -(@ge0_integralZl _ _ R (normal_prob _ _) _ measurableT _ _ (`|expR (- (y.1 ^+ 2%R / 4)) / Num.sqrt (4 * pi)|%:E) )//; first last.
exact: emeasurable_normal_prob.
Qed.

(* TODO: rename *)
Lemma execP_helloRight0_to_1 y V:
measurable V ->
execP helloRightP y V = execP helloRight1P y V.
Proof.
move=> mV.
(* lhs *)
rewrite lhs_execPE.
rewrite (helloRightP_intE _ mV).
rewrite (int_change_helloRightP _ mV).
(* rhs *)
rewrite rhs_execPE.
rewrite (helloRight1P_intE _ mV).
rewrite (int_change_helloRight1P _ mV).
(* eq_integral *)
apply: eq_integral.
move=> x _.
rewrite [in LHS]muleAC.
rewrite [in RHS](muleC (normal_prob x 1 V)) muleA.
congr (fun t => (t * normal_prob x 1 V)%E).
rewrite [in LHS]ger0_norm; last first.
- by rewrite mulr_ge0// expR_ge0.
rewrite [in RHS]ger0_norm; last first.
- by rewrite mulr_ge0// expR_ge0.
rewrite -!EFinM; congr EFin.
rewrite !normal_pdfE// /normal_pdf0.
rewrite mulrA.
rewrite mulrAC.
rewrite -(@sqrtrV _ 2)//.
rewrite sqr_sqrtr; last by rewrite invr_ge0.
rewrite subr0.
rewrite [X in X / _ = _]mulrC mulrA -expRD -mulrA -invfM.
rewrite [RHS]mulrAC [X in _ = _ * X / _]mulrC mulrA -mulrA -expRD -invfM.
congr *%R.
  congr expR; lra.
congr GRing.inv.
rewrite expr1n mul1r -mulrnAr -(mulr_natl pi) mulrA mulVf// mul1r -expr2.
rewrite sqr_sqrtr; last by rewrite mulr_ge0// pi_ge0.
rewrite !sqrtrM// mulrCA -expr2 sqr_sqrtr; last exact: pi_ge0.
congr *%R.
have /normr_idP <- : (@GRing.zero R <= 2)%R by [].
rewrite -(sqrtr_sqr 2%R).
congr Num.sqrt.
lra.
Qed.

Lemma helloRight0_to_2 y V : measurable V ->
execP helloRightP y V = execP helloRight2P y V.
Proof.
move=> mV.
rewrite execP_helloRight0_to_1//.
rewrite /helloRight1P/helloRight2P.
rewrite execP_letin/= [in RHS]execP_letin/=.
rewrite letin'E [RHS]letin'E.
by under eq_integral do rewrite execP_helloRight12//.
Qed.

(*
Lemma helloRight0_to_1 :
execD helloRight = execD helloRight1.
Proof.
apply: congr_normalize => y V.
(* lhs *)
rewrite ![in LHS]execP_letin.
rewrite [in LHS]execP_sample.
rewrite [in LHS]execD_normal/=.
rewrite [in LHS]execD_real/=.
rewrite [in LHS]execP_score.
rewrite [in LHS]execD_pow_real/=.
rewrite [in LHS](@execD_bin _ _ binop_mult)/=.
rewrite [in LHS](@execD_bin _ _ binop_minus)/=.
rewrite [in LHS]execD_real/=.
rewrite [in LHS](@execD_bin _ _ binop_mult)/=.
rewrite [in LHS]execD_pow/=.
rewrite [in LHS](@execD_bin _ _ binop_minus)/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "y0")/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "x")/=.
rewrite [in LHS]execD_real/=.
rewrite [in LHS]execD_real/=.
rewrite [in LHS]execP_sample.
rewrite [in LHS]execD_normal/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "x")/=.
rewrite [in LHS]execP_return/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "z")/=.
(* rhs *)
rewrite [in RHS]execP_letin.
rewrite [in RHS]execP_score.
rewrite [in RHS]execD_pow_real/=.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS](@execD_bin _ _ binop_minus)/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS]execD_pow/=.
rewrite [in RHS]exp_var'E/= (execD_var_erefl "y0")/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS]execP_letin.
rewrite [in RHS]execP_sample.
rewrite [in RHS]execD_normal/=.
rewrite [in RHS](@execD_bin _ _ binop_mult)/=.
rewrite [in RHS]exp_var'E/= (execD_var_erefl "y0")/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS]execP_letin.
rewrite [in RHS]execP_sample.
rewrite [in RHS]execD_normal/=.
rewrite [in RHS]exp_var'E/= (execD_var_erefl "x")/=.
rewrite [in RHS]execP_return.
rewrite [in RHS]exp_var'E/= (execD_var_erefl "z")/=.
(* lhs *)
rewrite [in LHS]letin'E/=.
under [in LHS]eq_integral.
  move=> x _.
  rewrite letin'E/=.
  under eq_integral.
    move=> u _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac; last first.
      admit. (* ? *)
    over.
  rewrite /=.
  rewrite ge0_integral_mscale/=; first last.
  - by move=> ? _.
  - by [].
  - exact: measurableT.
  rewrite integral_dirac; first last.
  - by [].
  - exact: measurableT.
  rewrite diracT mul1e.
  rewrite sub0r.
  rewrite -expRM mul1r.
  over.
rewrite /=.
rewrite [in LHS]integral_normal_prob; first last.
- apply: integrableMr => //.
      admit.
    exists (Num.sqrt 2 * pi)^-1; split; first exact: num_real.
    move=> x x_ge_Vsq2pi.
    move=> p _.
    rewrite /= normr_id.
    have /normr_idP -> : 0 <= expR (- ((y.1 - p) ^+ 2%R / 2) / (Num.sqrt 2 * pi)).
red.
    admit.
have := (@integrableZl _ _ _ (normal_prob 0 1) _ (@measurableT _ R) _ (fun x => normal_prob x 1 V)).
(* ? *) admit.
- apply: emeasurable_funM; last first.
(* TODO: Define instance of normal_prob is kernel *)
    (* apply: measurable_kernel. *)
rewrite /=.
  under [X in _ _ X]eq_fun.
    move=> x.
    rewrite -(@fineK _ (normal_prob _ _ _)); last first.
      admit.
    over.
  apply/measurable_EFinP.
  apply: continuous_measurable_fun.
  apply: continuous_normal_prob.
have := (@continuous_measurable_fun _ (fun x => normal_prob x 1 V)).
    have := measurable_normal_prob2.
    apply/measurability
    admit.
  apply/measurable_EFinP.
  admit.
- exact: measurableT.
- exact: ltr01.
(* rhs *)
rewrite [in RHS]letin'E/=.
under [in RHS]eq_integral.
  move=> u _.
  rewrite letin'E/=.
  under eq_integral.
    move=> x _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac.
    over.
  over.
rewrite ge0_integral_mscale; first last.
- move=> ? _.
  exact: integral_ge0.
- exact: measurable_cst.
- exact: measurableT.
rewrite integral_dirac/=; first last.
- exact: measurable_cst.
- exact: measurableT.
rewrite diracT mul1e.
rewrite sub0r -expRM mul1r.
rewrite [in RHS]integral_normal_prob; first last.
- (* ok *) admit.
- (* ? *)admit. (* TODO1: ish *)
- exact: measurableT.
rewrite -ge0_integralZl; first last.
- by [].
- move=> ? _.
  apply: mule_ge0 => //.
  rewrite lee_fin.
  exact: normal_pdf_ge0.
- apply: emeasurable_funM.
  + (* TODO1: ish *) admit.
  + (* ? *)admit.
- exact: measurableT.
(* eq_integral *)
apply: eq_integral.
move=> x _.
rewrite [in LHS]muleAC.
rewrite [in RHS](muleC (normal_prob1 x V)) muleA.
congr *%E.
rewrite [in LHS]ger0_norm; last first.
- (* ok *)admit.
rewrite [in RHS]ger0_norm; last first.
- (* ok *)admit.
rewrite /normal_pdf mul1r subr0 divr1.
(* ? *) (* TODO2: ish *)
rewrite -!EFinM.
congr EFin.
rewrite mulrA.
rewrite mulrAC.
rewrite -expRD.
rewrite [RHS]mulrA.
rewrite [RHS]mulrAC.
rewrite -expRD.
congr *%R.
- congr expR.
  rewrite [in RHS]expr_div_n.
  rewrite -[in RHS](@sqrtrV _ 2)//.
  rewrite sqr_sqrtr//.
  (* ? *)
  admit.
admit.
Admitted.
*)

(* ref : https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf
 * p.2, equation (9)
 * sum independent random variables that are normally distributed
 *)
(*
Lemma helloRight1_to_2 : execD helloRight1 = execD helloRight2.
Proof.
apply: congr_normalize => y V.
(* TODO: split rewriting on LHS and RHS *)
(* lhs *)
rewrite [in LHS]execP_letin.
rewrite !execP_score.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_real.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/=.
rewrite !execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite !(@execD_bin _ _ binop_mult)/=.
rewrite exp_var'E/= (execD_var_erefl "y0")/= !execD_real/=.
rewrite execP_letin.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execP_return/=.
rewrite exp_var'E/= (execD_var_erefl "z")/=.
(* rhs *)
rewrite execP_letin.
rewrite execP_score/=.
rewrite (@execD_bin _ _ binop_mult)/=.
rewrite execD_real/=.
rewrite execD_pow_real/=.
rewrite (@execD_bin _ _ binop_minus)/= execD_real/=.
rewrite (@execD_bin _ _ binop_mult)/= execD_real/=.
rewrite exp_var'E/=.
rewrite execD_pow/=.
rewrite execP_sample.
rewrite execD_normal/=.
rewrite (@execD_bin _ _ binop_mult)/= execD_real/=.
rewrite exp_var'E/= 2!(execD_var_erefl "y0")/=.
(* lhs *)
rewrite letin'E/=.
under eq_integral.
  move=> x _.
  rewrite letin'E/=.
  under eq_integral.
    move=> z _.
    rewrite letin'E/=.
    rewrite integral_normal_prob_dirac//; .
      admit.
    over.
  over.
rewrite ge0_integral_mscale//=; last first.
  move=> ? _; exact: integral_ge0.
rewrite integral_dirac//.
rewrite diracT mul1e.
(* rhs *)
rewrite letin'E/=.
rewrite ge0_integral_mscale//=.
rewrite integral_dirac//= diracT mul1e.
Abort.
*)

End helloRight_proof.

(* TODO: move *)
Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Definition exponential_pdf' (x : R) := (mean^-1 * expR (- x / mean))%R.
Definition exponential_pdf := exponential_pdf' \_ `[0%R, +oo[.

Lemma exponential_pdf_ge0 (x : R) : (0 <= exponential_pdf x)%R.
Proof.
apply: restrict_ge0 => {}x _.
apply: mulr_ge0; last exact: expR_ge0.
by rewrite invr_ge0 ltW.
Qed.

End exponential_pdf.

Definition exponential {R : realType} (m : R)
  of \int[@lebesgue_measure R]_x (exponential_pdf m x)%:E = 1%E : set _ -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (exponential_pdf m x)%:E)%E.

Section exponential.
Context {R : realType}.
Local Open Scope ring_scope.

Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Hypothesis integrable_exponential : forall (m : R), (0 < m)%R ->
  mu.-integrable [set: _] (EFin \o (exponential_pdf m)).

Hypothesis integral_exponential_pdf : forall (m : R), (0 < m)%R ->
  (\int[mu]_x (exponential_pdf m x)%:E = 1)%E.

Local Notation exponential := (exponential (integral_exponential_pdf mean0)).

Let exponential0 : exponential set0 = 0%E.
Proof. by rewrite /exponential integral_set0. Qed.

Let exponential_ge0 A : (0 <= exponential A)%E.
Proof.
by rewrite /exponential integral_ge0//= => x _; rewrite lee_fin exponential_pdf_ge0.
Qed.

Let exponential_sigma_additive : semi_sigma_additive exponential.
Proof.
Admitted.

HB.instance Definition _ := isMeasure.Build _ _ _
  exponential exponential0 exponential_ge0 exponential_sigma_additive.

Let exponential_setT : exponential [set: _] = 1%E.
Proof. by rewrite /exponential integral_exponential_pdf. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R exponential exponential_setT.

End exponential.
