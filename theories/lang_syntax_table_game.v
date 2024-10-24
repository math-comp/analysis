Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import ring lra.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import signed reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure charge lebesgue_measure numfun.
From mathcomp Require Import lebesgue_integral kernel probability prob_lang.
From mathcomp Require Import lang_syntax_util lang_syntax lang_syntax_examples.

(**md**************************************************************************)
(* # Eddy's table game example                                                *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - Sean R Eddy, What is Bayesian statistics?, Nature Biotechnology 22(9),   *)
(*   1177--1178 (2004)                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Open Scope ereal_scope.
Lemma letin'_sample_uniform {R : realType} d d' (T : measurableType d)
    (T' : measurableType d') (a b : R) (ab : (a < b)%R)
    (u : R.-sfker [the measurableType _ of (_ * T)%type] ~> T') x y :
  measurable y ->
  letin' (sample_cst (uniform_prob ab)) u x y =
  (b - a)^-1%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y.
Proof.
move=> my; rewrite letin'E/=.
rewrite integral_uniform//=.
move => _ /= Y mY /=.
have /= := measurable_kernel u _ my measurableT _ mY.
move/measurable_ysection => /(_ R x) /=.
set A := (X in measurable X).
set B := (X in _ -> measurable X).
suff : A = B by move=> ->.
rewrite {}/A {}/B !setTI /ysection/= (*TODO: lemma?*) /preimage/=.
by apply/seteqP; split => [z|z] /=; rewrite inE/=.
Qed.

Local Open Scope lang_scope.
Lemma execP_letin_uniform {R : realType}
  g t str (s0 s1 : exp P ((str, Real) :: g) t) :
  (forall (p : R) x U, (0 <= p <= 1)%R ->
    execP s0 (p, x) U = execP s1 (p, x) U) ->
  forall x U, measurable U ->
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s0}] x U =
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s1}] x U.
Proof.
move=> s01 x U mU.
rewrite !execP_letin execP_sample execD_uniform/=.
rewrite !letin'_sample_uniform//.
congr *%E.
apply: eq_integral => p p01.
apply: s01.
by rewrite inE in p01.
Qed.
Local Close Scope lang_scope.
Local Close Scope ereal_scope.

Section bounded.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Local Open Scope ereal_scope.
Context {R : realType}.

Lemma bounded_id_01 : [bounded x0 | x0 in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
by rewrite ler_norml M1 andbT (le_trans _ M0).
Unshelve. all: by end_near. Qed.

Lemma bounded_onem_01 : [bounded (`1- x : R) | x in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
rewrite ler_norml (@le_trans _ _ 0%R)//=.
  by rewrite lerBlDr addrC -lerBlDr subrr.
by rewrite onem_ge0.
Unshelve. all: by end_near. Qed.

Lemma bounded_cst_01 (x : R) : [bounded x | _ in `[0%R, 1%R]%classic : set R].
Proof.
exists `|x|%R; split.
  by rewrite num_real.
move=> y y1/= z.
rewrite in_itv/= => /andP[z0 z1].
by rewrite (le_trans _ (ltW y1)).
Qed.

Lemma bounded_norm (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] <->
  [bounded normr (f x) | x in (`[0%R, 1%R]%classic : set R)].
Proof.
split.
  move=> [M [Mreal HM]].
  exists `|M|%R; split; first by rewrite normr_real.
  move=> r Mr x/= x01.
  by rewrite ger0_norm// HM// (le_lt_trans _ Mr)// ler_norm.
move=> [M [Mreal HM]].
exists `|M|%R; split; first by rewrite normr_real.
move=> r Mr x/= x01.
rewrite -[leLHS]ger0_norm// HM//.
by rewrite (le_lt_trans _ Mr)// ler_norm.
Qed.

Lemma boundedMl k (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] ->
  [bounded (k * f x)%R | x in (`[0%R, 1%R]%classic : set R)].
Proof.
move=> [M [Mreal HM]].
exists `|k * M|%R; split; first by rewrite normr_real.
move=> r kMr x/= x01.
rewrite normrM.
have [->|k0] := eqVneq k 0%R.
  by rewrite normr0 mul0r (le_trans _ (ltW kMr)).
rewrite -ler_pdivlMl ?normr_gt0//.
apply: HM => //.
rewrite ltr_pdivlMl ?normr_gt0//.
rewrite (le_lt_trans _ kMr)//.
by rewrite normrM ler_pM2l ?normr_gt0// ler_norm.
Qed.

End bounded.

Lemma measurable_bernoulli_expn {R : realType} U n :
  measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x : g_sigma_algebraType (R.-ocitv.-measurable) => bernoulli (`1-x ^+ n) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
by apply: measurable_funX => //=; exact: measurable_funB.
Qed.

Lemma integrable_bernoulli_beta_pdf {R : realType} U : measurable U ->
  (@lebesgue_measure R).-integrable [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U * (beta_pdf 6 4 x)%:E)%E.
Proof.
move=> mU.
have ? : measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U).
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  apply: measurable_funB => //; apply: measurable_funX => //.
  exact: measurable_funB.
apply/integrableP; split => /=.
  apply: emeasurable_funM => //=.
  by apply/EFin_measurable_fun; exact: measurable_beta_pdf.
apply: (@le_lt_trans _ _ (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (beta_pdf 6 4 x)%:E))%E.
  rewrite [leRHS]integral_mkcond /=.
  apply: ge0_le_integral => //=.
  - apply: measurableT_comp => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun; exact: measurable_beta_pdf.
  - move=> x _ /=; rewrite patchE; case: ifPn => // _.
    by rewrite lee_fin beta_pdf_ge0.
  - apply/(measurable_restrict _ _ _) => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_beta_pdf.
  - move=> x _.
    rewrite patchE; case: ifPn => x01.
      rewrite gee0_abs//.
        rewrite gee_pMl// ?probability_le1//.
          by rewrite ge0_fin_numE// (le_lt_trans (probability_le1 _ _))// ltry.
        by rewrite lee_fin beta_pdf_ge0.
      by rewrite mule_ge0// lee_fin beta_pdf_ge0.
    by rewrite /beta_pdf /XMonemX01 patchE (negbTE x01) mul0r mule0 abse0.
apply: (@le_lt_trans _ _
    (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (betafun 6 4)^-1%:E)%E); last first.
  by rewrite integral_cst//= lebesgue_measure_itv/= lte01 EFinN sube0 mule1 ltry.
apply: ge0_le_integral => //=.
- by move=> ? _; rewrite lee_fin beta_pdf_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_beta_pdf.
- by move=> ? _; rewrite lee_fin invr_ge0// betafun_ge0.
- by move=> x _; rewrite lee_fin beta_pdf_le_betafunV.
Qed.

Section game_programs.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Definition guard {g} str n : @exp R P [:: (str, _) ; g] _ :=
  [if #{str} == {n}:N then return TT else Score {0}:R].

Definition prog0 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "x" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := {guard "x" 5} in
  let "y" := Sample {exp_binomial 3 [#{"p"}]} in
  return {1}:N <= #{"y"}].

Definition tail1 : @exp R _ [:: ("_", Unit); ("x", Nat) ; ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3}]}].

Definition tail2 : @exp R _ [:: ("_", Unit); ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3}]}].

Definition tail3 : @exp R _ [:: ("p", Real); ("_", Unit)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3}]}].

Definition prog1 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "x" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := {guard "x" 5} in
  {tail1}].

Definition prog2 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "_" :=
    Score {[{56}:R * #{"p"} ^+ {5} * {[{1}:R - #{"p"}]} ^+ {3}]} in
  {tail2}].

Definition prog2' : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_beta 1 1} in
  let "_" := Score
    {[{56}:R * #{"p"} ^+ {5} * {[{1}:R - #{"p"}]} ^+ {3}]} in
  {tail2}].

Definition prog3 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  let "p" := Sample {exp_beta 6 4} in
  {tail3}].

Definition prog4 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  Sample {exp_bernoulli [{10 / 11}:R]}].

Definition prog5 : @exp R _ [::] _ :=
  [Normalize Sample {exp_bernoulli [{10 / 11}:R]}].

End game_programs.
Arguments tail1 {R}.
Arguments tail2 {R}.
Arguments guard {R g}.

Section from_prog0_to_prog1.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let prog01_subproof
  (x : mctx (untag (ctx_of (recurse Unit (recurse Nat (found "p" Real [::]))))))
  U : (0 <= x.2.2.1 <= 1)%R ->
  execP [let "y" := Sample {exp_binomial 3 [#{"p"}]} in
         return {1}:N <= #{"y"}] x U =
  execP (@tail1 R) x U.
Proof.
move=> x01.
rewrite /tail1.
(* reduce lhs *)
rewrite execP_letin execP_sample execD_binomial/= execP_return/= execD_rel/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite exp_var'E (execD_var_erefl "y")/=.
rewrite execD_nat/=.
rewrite [LHS]letin'E/=.
(* reduce rhs *)
rewrite execP_sample/= execD_bernoulli/= (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/= execD_pow/= (@execD_bin _ _ binop_minus)/= execD_real/=.
rewrite (execD_var_erefl "p")/=.
exact/integral_binomial_prob.
Qed.

Lemma prog01 : execD (@prog0 R) = execD (@prog1 R).
Proof.
rewrite /prog0 /prog1.
apply: congr_normalize => y A.
apply: execP_letin_uniform => // p [] B p01.
apply: congr_letinr => a1 V0.
apply: congr_letinr => -[] V1.
exact: prog01_subproof.
Qed.

End from_prog0_to_prog1.

Section from_prog1_to_prog2.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let prog12_subproof (y : @mctx R [::]) (V : set (@mtyp R Bool))
  (p : R)
  (x : projT2 (existT measurableType default_measure_display unit))
  (U : set (mtyp Bool))
  (p0 : (0 <= p)%R)
  (p1 : (p <= 1)%R) :
  \int[binomial_prob 8 p]_y0
     execP [let "_" := {guard "x" 5} in {tail1}]
       (y0, (p, x)) U =
  \int[mscale (NngNum (normr_ge0 (56 * XMonemX 5 3 p))) \d_tt]_y0
     execP tail2 (y0, (p, x)) U.
Proof.
rewrite integral_binomial//=.
rewrite (bigD1 (inord 5))//=.
rewrite big1 ?adde0; last first.
  move=> i i5.
  rewrite execP_letin/= execP_if/= execD_rel/=.
  rewrite exp_var'E/= (execD_var_erefl "x")/=.
  rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
  rewrite letin'E iteE/=.
  move: i => [[|[|[|[|[|[|[|[|[|//]]]]]]]]]]//= Hi in i5 *;
  rewrite ?ge0_integral_mscale//= ?execD_real/= ?normr0 ?(mul0e,mule0)//.
  by rewrite -val_eqE/= inordK in i5.
(* reduce lhs *)
rewrite -[(p ^+ _ * _ ^+ _)%R]/(XMonemX _ _ p).
rewrite execP_letin/= execP_if/= execD_rel/=.
rewrite exp_var'E/= (execD_var_erefl "x")/=.
rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
rewrite letin'E iteE/=.
rewrite inordK// eqxx.
rewrite integral_dirac//= execD_unit/= diracE mem_set// mul1e.
(* reduce rhs *)
rewrite ge0_integral_mscale//=.
rewrite integral_dirac//= diracE mem_set// mul1e.
rewrite ger0_norm ?mulr_ge0 ?subr_ge0//.
rewrite mulr_natl.
(* same score *)
congr *%E.
(* the tails are the same module the shape of the environment *)
rewrite /tail1 /tail2 !execP_sample/=.
rewrite !execD_bernoulli/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
rewrite !execD_pow/=.
rewrite !execD_real/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
by rewrite !execD_real/= !exp_var'E/= !(execD_var_erefl "p")/=.
Qed.

Lemma prog12 : execD (@prog1 R) = execD (@prog2 R).
Proof.
apply: congr_normalize => y V.
apply: execP_letin_uniform => // p x U /andP[p0 p1].
(* reduce the lhs *)
rewrite execP_letin execP_sample execD_binomial/=.
rewrite letin'E/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite [in RHS]execP_letin execP_score/=.
rewrite letin'E/=.
do 2 rewrite (@execD_bin _ _ binop_mult)/=/=.
rewrite [in RHS]exp_var'E/=.
rewrite execD_pow/=.
rewrite (execD_var_erefl "p")/=.
rewrite execD_pow/=.
rewrite (@execD_bin _ _ binop_minus)/=/=.
rewrite 2!execD_real/=.
rewrite (execD_var_erefl "p")/=.
rewrite -(mulrA 56).
exact: prog12_subproof.
Qed.

End from_prog1_to_prog2.

Local Open Scope ereal_scope.

Lemma measurable_bernoulli_onemXn {R : realType} U :
  measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
apply: measurable_funB => //.
by apply: measurable_funX; exact: measurable_funB.
Qed.

Lemma bounded_norm_XnonemXn {R : realType} :
  [bounded normr (56 * XMonemX 5 3 x)%R : R | x in `[0%R, 1%R] : set R].
Proof. exact/(bounded_norm _).1/boundedMl/bounded_XMonemX. Qed.

Lemma integrable_bernoulli_XMonemX {R : realType} U :
  (beta_prob 1 1).-integrable [set: R]
    (fun x => bernoulli (1 - `1-x ^+ 3) U * (normr (56 * XMonemX 5 3 x))%:E).
Proof.
apply/integrableP; split.
  apply: emeasurable_funM; first exact: measurable_bernoulli_onemXn.
  apply/EFin_measurable_fun => //; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_fun_XMonemX.
rewrite beta_prob_uniform integral_uniform//=.
  rewrite subr0 invr1 mul1e.
  suff : lebesgue_measure.-integrable `[0%R, 1%R]
    (fun y : R => bernoulli (1 - `1-y ^+ 3) U * (normr (56 * XMonemX 5 3 y))%:E).
    by move=> /integrableP[].
  apply: integrableMl => //=.
  - apply/integrableP; split.
      by apply: measurable_funTS; exact: measurable_bernoulli_onemXn.
    have := @integral_beta_prob_bernoulli_onem_lty R 3 1%N 1%N U.
    rewrite beta_prob_uniform integral_uniform//=; last first.
      by apply: measurableT_comp => //=; exact: measurable_bernoulli_onemXn.
    by rewrite subr0 invr1 mul1e.
  - apply: @measurableT_comp => //=; apply: measurable_funM => //.
      exact: measurable_fun_XMonemX.
    exact: bounded_norm_XnonemXn.
apply: @measurableT_comp => //; apply: emeasurable_funM => //=.
  exact: measurable_bernoulli_onemXn.
do 2 apply: @measurableT_comp => //=.
by apply: measurable_funM => //; exact: measurable_fun_XMonemX.
Qed.

Section from_prog2_to_prog3.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma prog22' : execD (@prog2 R) = execD (@prog2' R).
Proof.
apply: congr_normalize => // x U.
apply: congr_letinl => // y V.
rewrite !execP_sample execD_uniform/= execD_beta/=.
by rewrite beta_prob_uniform.
Qed.

Lemma prog23 : execD (@prog2' R) = execD (@prog3 R).
Proof.
apply: congr_normalize => x U.
(* reduce the LHS *)
rewrite 2![in LHS]execP_letin.
rewrite ![in LHS]execP_sample.
rewrite [in LHS]execP_score.
rewrite [in LHS]execD_beta/=.
rewrite [in LHS]execD_bernoulli.
rewrite 2![in LHS](@execD_bin _ _ binop_mult)/=.
rewrite 2![in LHS]execD_pow/=.
rewrite 2![in LHS](@execD_bin _ _ binop_minus)/=.
rewrite 3![in LHS]execD_real.
rewrite [in LHS]exp_var'E [in LHS](execD_var_erefl "p")/=.
rewrite [in LHS]execD_pow/=.
rewrite [in LHS](@execD_bin _ _ binop_minus)/=.
rewrite [in LHS]execD_real.
rewrite [in LHS]exp_var'E [in LHS](execD_var_erefl "p")/=.
(* reduce the RHS *)
rewrite [in RHS]execP_letin.
rewrite [in RHS]execP_score.
rewrite [in RHS]execP_letin/=.
rewrite [in RHS]execP_sample/=.
rewrite [in RHS]execD_beta/=.
rewrite [in RHS]execP_sample/=.
rewrite [in RHS]execD_bernoulli/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS](@execD_bin _ _ binop_minus)/=.
rewrite [in RHS]execD_real/=.
rewrite [in RHS]execD_pow/=.
rewrite [in RHS](@execD_bin _ _ binop_minus)/=.
rewrite [in RHS]exp_var'E [in RHS](execD_var_erefl "p")/=.
rewrite [in RHS]execD_real/=.
rewrite [LHS]letin'E/=.
under eq_integral => y _.
  rewrite letin'E/=.
  rewrite integral_cst//= /mscale/= diracT mule1 -mulrA -/(XMonemX _ _ _).
  over.
rewrite [RHS]letin'E/=.
under [in RHS]eq_integral => y _.
  rewrite letin'E/=.
  over.
rewrite /=.
rewrite [RHS]ge0_integral_mscale//=; last first.
  by move=> _ _; rewrite integral_ge0.
rewrite integral_beta_prob//=; last 2 first.
  - apply: emeasurable_funM => //=.
      exact: measurable_bernoulli_onemXn.
    apply/EFin_measurable_fun; apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_fun_XMonemX.
  - by have /integrableP[] := @integrable_bernoulli_XMonemX R U.
rewrite ger0_norm// integral_dirac// diracT mul1e.
rewrite integral_beta_prob/=; [|by []|exact: measurable_bernoulli_onemXn
    |exact: integral_beta_prob_bernoulli_onem_lty].
rewrite -integralZl//=; last exact: integrable_bernoulli_beta_pdf.
apply: eq_integral => y _.
rewrite [in RHS]muleCA -[in LHS]muleA; congr *%E.
rewrite /beta_pdf /XMonemX01 2!patchE; case: ifPn => [y01|_]; last first.
  by rewrite !mul0r 2!mule0.
rewrite ger0_norm; last first.
  by rewrite mulr_ge0// XMonemX_ge0//; rewrite inE in y01.
rewrite [X in _ = _ * X]EFinM [in RHS]muleCA.
rewrite /= XMonemX00 mul1r [in LHS](mulrC 56) [in LHS]EFinM -[in LHS]muleA; congr *%E.
by rewrite !betafunE/= !factE/= -EFinM; congr EFin; lra.

Qed.

End from_prog2_to_prog3.

Local Open Scope ereal_scope.
(* TODO: move? *)
Lemma int_beta_prob01 {R : realType} (f : R -> R) a b U :
  measurable_fun [set: R] f ->
  (forall x, x \in `[0%R, 1%R] -> 0 <= f x <= 1)%R ->
  \int[beta_prob a b]_y bernoulli (f y) U =
  \int[beta_prob a b]_(y in `[0%R, 1%R] : set R) bernoulli (f y) U.
Proof.
move=> mf f01.
rewrite [LHS]integral_beta_prob//=; last 2 first.
  apply: measurable_funTS.
  by apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  exact: integral_beta_prob_bernoulli_lty.
rewrite [RHS]integral_beta_prob//; last 2 first.
  apply/measurable_funTS => //=.
  by apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  apply: (le_lt_trans _ (lang_syntax.integral_beta_prob_bernoulli_lty a b U mf f01)).
  apply: ge0_subset_integral => //=; apply: measurableT_comp => //=.
  by apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
rewrite [RHS]integral_mkcond/=; apply: eq_integral => x _ /=.
rewrite !patchE; case: ifPn => // x01.
by rewrite /beta_pdf /XMonemX01 patchE (negbTE x01) mul0r mule0.
Qed.

Lemma expr_onem_01 {R : realType} (x : R) : x \in `[0%R, 1%R] ->
  (0 <= `1-x ^+ 3 <= 1)%R.
Proof.
rewrite in_itv/= => /andP[x0 x1].
rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
by rewrite lerBlDl -lerBlDr subrr.
Qed.

Lemma int_beta_prob_bernoulli {R : realType} (U : set (@mtyp R Bool)) :
 \int[beta_prob 6 4]_y bernoulli (`1-y ^+ 3) U = bernoulli (1 / 11) U :> \bar R.
Proof.
rewrite int_beta_prob01//; last 2 first.
  by apply: measurable_funX => //; exact: measurable_funB.
  exact: expr_onem_01.
have := @beta_prob_bernoulliE R 6 4 0 3 U isT isT.
rewrite /beta_prob_bernoulli.
under eq_integral.
  move=> x x0.
  rewrite /XMonemX01 patchE x0 XMonemX0.
  over.
rewrite /= => ->; congr bernoulli.
by rewrite /div_betafun addn0 !betafunE/= !factE/=; field.
Qed.

Lemma dirac_bool {R : realType} (U : set bool) :
  \d_false U + \d_true U = (\sum_(x \in U) (1%E : \bar R))%R.
Proof.
have [| | |] := set_bool U => /eqP ->; rewrite !diracE.
- by rewrite memNset// mem_set//= fsbig_set1 add0e.
- by rewrite mem_set// memNset//= fsbig_set1 adde0.
- by rewrite !in_set0 fsbig_set0 adde0.
- rewrite !in_setT setT_bool fsbigU0//=; last by move=> x [->].
  by rewrite !fsbig_set1.
Qed.

Lemma int_beta_prob_bernoulli_onem {R : realType} (U : set (@mtyp R Bool)) :
 \int[beta_prob 6 4]_y bernoulli (`1-(`1-y ^+ 3)) U = bernoulli (10 / 11) U :> \bar R.
Proof.
transitivity (\d_false U + \d_true U - bernoulli (1 / 11) U : \bar R)%E; last first.
  rewrite /bernoulli ifT; last lra.
  rewrite ifT; last lra.
  apply/eqP; rewrite sube_eq//; last first.
    rewrite ge0_adde_def// inE.
      by apply/sume_ge0 => //= b _; rewrite lee_fin bernoulli_pmf_ge0//; lra.
    by apply/sume_ge0 => //= b _; rewrite lee_fin bernoulli_pmf_ge0//; lra.
  rewrite -fsbig_split//=.
  under eq_fsbigr.
    move=> /= x _.
    rewrite -EFinD /bernoulli_pmf [X in X%:E](_ : _ = 1%R); last first.
      case: x => //; lra.
    over.
  by rewrite /= dirac_bool.
rewrite -int_beta_prob_bernoulli.
apply/esym/eqP; rewrite sube_eq//; last first.
  by rewrite ge0_adde_def// inE; exact: integral_ge0.
rewrite int_beta_prob01; last 2 first.
  apply: measurable_funB => //; apply: measurable_funX => //.
  exact: measurable_funB.
  move=> x x01.
  by rewrite subr_ge0 andbC lerBlDr -lerBlDl subrr expr_onem_01.
rewrite [X in _ == _ + X]int_beta_prob01; last 2 first.
  by apply: measurable_funX => //; exact: measurable_funB.
  exact: expr_onem_01.
rewrite -ge0_integralD//=; last 2 first.
  apply: (@measurableT_comp _ _ _ _ _ _ (bernoulli ^~ U)) => /=.
    exact: measurable_bernoulli2.
  apply: measurable_funB => //=; apply: measurable_funX => //=.
  exact: measurable_funB.
  apply: (@measurableT_comp _ _ _ _ _ _ (bernoulli ^~ U)) => /=.
    exact: measurable_bernoulli2.
  by apply: measurable_funX => //=; exact: measurable_funB.
apply/eqP; transitivity
    (\int[beta_prob 6 4]_(x in `[0%R, 1%R]) (\d_false U + \d_true U) : \bar R).
  by rewrite integral_cst//= beta_prob01 mule1 EFinD.
apply: eq_integral => /= x x01.
rewrite /bernoulli subr_ge0 lerBlDr -lerBlDl subrr andbC.
rewrite (_ : (_ <= _ <= _)%R); last first.
  by apply: expr_onem_01; rewrite inE in x01.
rewrite -fsbig_split//=.
under eq_fsbigr.
  move=> /= y yU.
  rewrite -EFinD /bernoulli_pmf.
  rewrite [X in X%:E](_ : _ = 1%R); last first.
    by case: ifPn => _; rewrite subrK.
  over.
by rewrite /= dirac_bool.
Qed.

Local Close Scope ereal_scope.

Section from_prog3_to_prog4.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).

(* NB: not used *)
Lemma prog34' U :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli [{[{1}:R - #{"p"}]} ^+ {3%N}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli [{1 / 11}:R]}] tt U.
Proof.
(* reduce the lhs *)
rewrite execP_letin.
rewrite execP_sample execD_beta/=.
rewrite execP_sample/= execD_bernoulli/=.
rewrite execD_pow/= (@execD_bin _ _ binop_minus) execD_real/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite execP_sample execD_bernoulli/= execD_real.
(* semantics of lhs *)
rewrite letin'E/=.
exact: int_beta_prob_bernoulli.
Qed.

Lemma prog34 l u U :
  @execP R l _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%N}]}] u U =
  @execP R l _ [Sample {exp_bernoulli [{10 / 11}:R]}] u U.
Proof.
(* reduce the lhs *)
rewrite execP_letin.
rewrite execP_sample execD_beta/=.
rewrite execP_sample/= execD_bernoulli/=.
rewrite (@execD_bin _ _ binop_minus)/=.
rewrite execD_pow/= (@execD_bin _ _ binop_minus) execD_real/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite execP_sample execD_bernoulli/= execD_real.
(* semantics of lhs *)
rewrite letin'E/=.
exact: int_beta_prob_bernoulli_onem.
Qed.

End from_prog3_to_prog4.

Section from_prog4_to_prog5.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma normalize_score_bernoulli g p q (p0 : (0 < p)%R) (q01 : (0 <= q <= 1)%R) :
  @execD R g _ [Normalize let "_" := Score {p}:R in
                Sample {exp_bernoulli [{q}:R]}] =
  execD [Normalize Sample {exp_bernoulli [{q}:R]}].
Proof.
apply: eq_execD.
rewrite !execD_normalize_pt/= !execP_letin !execP_score.
rewrite !execP_sample !execD_bernoulli !execD_real/=.
apply: funext=> x.
apply: eq_probability=> /= U.
rewrite !normalizeE/=.
rewrite !bernoulliE//=; [|lra..].
rewrite !diracT !mule1 -EFinD add_onemK onee_eq0/=.
rewrite !letin'E.
under eq_integral.
  move=> A _ /=.
  rewrite !bernoulliE//=; [|lra..].
  rewrite !diracT !mule1 -EFinD add_onemK.
  over.
rewrite !ge0_integral_mscale//= (ger0_norm (ltW p0))//.
rewrite integral_dirac// !diracT !indicT /= !mule1 !mulr1.
rewrite add_onemK invr1 mule1.
rewrite gt_eqF ?lte_fin//=.
rewrite integral_dirac//= diracT mul1e.
by rewrite muleAC -EFinM divff ?gt_eqF// mul1e bernoulliE.
Qed.

Lemma prog45 : execD (@prog4 R) = execD (@prog5 R).
Proof. by rewrite normalize_score_bernoulli//; lra. Qed.

End from_prog4_to_prog5.

Lemma from_prog0_to_prog5 {R : realType} : execD (@prog0 R) = execD (@prog5 R).
Proof.
rewrite prog01 prog12 prog22' prog23.
rewrite -prog45.
apply: congr_normalize => y V.
apply: congr_letinr => x U.
by rewrite -prog34.
Qed.
