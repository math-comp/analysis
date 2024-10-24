From Coq Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp.
From mathcomp Require Import ring lra.
From mathcomp Require Import classical_sets functions cardinality fsbigop.
From mathcomp Require Import signed reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure lebesgue_measure numfun.
From mathcomp Require Import lebesgue_integral kernel probability prob_lang.
From mathcomp Require Import lang_syntax_util lang_syntax.

(**md**************************************************************************)
(* # Examples using the Probabilistic Programming Language of lang_syntax.v   *)
(*                                                                            *)
(* sample_pair1213 := normalize (                                             *)
(*   let x := sample (bernoulli 1/2) in                                       *)
(*   let y := sample (bernoulli 1/3) in                                       *)
(*   return (x, y))                                                           *)
(*                                                                            *)
(* sample_and1213 := normalize (                                              *)
(*   let x := sample (bernoulli 1/2) in                                       *)
(*   let y := sample (bernoulli 1/3) in                                       *)
(*   return (x && y))                                                         *)
(*                                                                            *)
(* bernoulli13_score := normalize (                                           *)
(*   let x := sample (bernoulli 1/3) in                                       *)
(*   let _ := if x then score (1/3) else score (2/3) in                       *)
(*   return x)                                                                *)
(*                                                                            *)
(* sample_binomial3 :=                                                        *)
(*   let x := sample (binomial 3 1/2) in                                      *)
(*   return x                                                                 *)
(*                                                                            *)
(* hard_constraint := let x := Score {0}:R in return TT                       *)
(*                                                                            *)
(* guard :=                                                                   *)
(*   let p := sample (bernoulli (1 / 3)) in                                   *)
(*   let _ := if p then return TT else score 0 in                             *)
(*   return p                                                                 *)
(*                                                                            *)
(* more examples about uniform, beta, and bernoulli distributions             *)
(*                                                                            *)
(* associativity of let-in expressions                                        *)
(*                                                                            *)
(* staton_bus_syntax == example from [Staton, ESOP 2017]                      *)
(*                                                                            *)
(* staton_busA_syntax == same as staton_bus_syntax module associativity of    *)
(*   let-in expression                                                        *)
(*                                                                            *)
(* commutativity of let-in expressions                                        *)
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

Local Open Scope lang_scope.

Local Close Scope lang_scope.

(* simple tests to check bidirectional hints *)
Module bidi_tests.
Section bidi_tests.
Local Open Scope lang_scope.
Import Notations.
Context (R : realType).

Definition bidi_test1 x : @exp R P [::] _ := [
  let x := return {1}:R in
  return #x].

Definition bidi_test2 (a b : string)
  (a := "a") (b := "b")
  (* (ba : infer (b != a)) *)
  : @exp R P [::] _ := [
  let a := return {1}:R in
  let b := return {true}:B in
  (* let c := return {3}:R in
  let d := return {4}:R in *)
  return (#a, #b)].

Definition bidi_test3 (a b c d : string)
    (ba : infer (b != a)) (ca : infer (c != a))
    (cb : infer (c != b)) (ab : infer (a != b))
    (ac : infer (a != c)) (bc : infer (b != c)) : @exp R P [::] _ := [
  let a := return {1}:R in
  let b := return {2}:R in
  let c := return {3}:R in
  (* let d := return {4}:R in *)
  return (#b, #a)].

Definition bidi_test4 (a b c d : string)
    (ba : infer (b != a)) (ca : infer (c != a))
    (cb : infer (c != b)) (ab : infer (a != b))
    (ac : infer (a != c)) (bc : infer (b != c)) : @exp R P [::] _ := [
  let a := return {1}:R in
  let b := return {2}:R in
  let c := return {3}:R in
  (* let d := return {4}:R in *)
  return {exp_poisson O [#c(*{exp_var c erefl}*)]}].

End bidi_tests.
End bidi_tests.

Section trivial_example.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Lemma exec_normalize_return g x r :
  projT1 (@execD _ g _ [Normalize return r:R]) x =
  @dirac _ (measurableTypeR R) r _ :> probability _ R.
  (* NB: \d_r notation? *)
Proof.
by rewrite execD_normalize_pt execP_return execD_real//=; exact: normalize_kdirac.
Qed.

End trivial_example.

Section sample_pair.
Local Open Scope lang_scope.
Local Open Scope ring_scope.
Import Notations.
Context {R : realType}.

Definition sample_pair1213' : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli [{1 / 2}:R]} in
   let "y" := Sample {exp_bernoulli [{1 / 3}:R]} in
   return (#{"x"}, #{"y"})].

Definition sample_pair1213 : exp _ [::] _ := [Normalize {sample_pair1213'}].

Lemma exec_sample_pair1213' (A : set (bool * bool)) :
  @execP R [::] _ sample_pair1213' tt A =
  ((1 / 2)%:E *
   ((1 / 3)%:E * \d_(true, true) A +
    (1 - 1 / 3)%:E * \d_(true, false) A) +
   (1 - 1 / 2)%:E *
   ((1 / 3)%:E * \d_(false, true) A +
    (1 - 1 / 3)%:E * \d_(false, false) A))%E.
Proof.
rewrite !execP_letin !execP_sample !execD_bernoulli !execP_return /=.
rewrite execD_pair !exp_var'E (execD_var_erefl "x") (execD_var_erefl "y") /=.
rewrite !execD_real//=.
do 2 (rewrite letin'E/= integral_bernoulli//=; last lra).
by rewrite letin'E/= integral_bernoulli//=; lra.
Qed.

Lemma exec_sample_pair1213'_TandT :
  @execP R [::] _ sample_pair1213' tt [set (true, true)] = (1 / 6)%:E.
Proof.
rewrite exec_sample_pair1213' !diracE mem_set//; do 3 rewrite memNset//=.
by rewrite /= !mule0 mule1 !add0e mule0 adde0; congr (_%:E); lra.
Qed.

Lemma exec_sample_pair1213'_TandT' :
  @execP R [::] _ sample_pair1213' tt [set p | p.1 && p.2] = (1 / 6)%:E.
Proof.
rewrite exec_sample_pair1213' !diracE mem_set//; do 3 rewrite memNset//=.
by rewrite /= !mule0 mule1 !add0e mule0 adde0; congr (_%:E); lra.
Qed.

Lemma exec_sample_pair1213'_TandF :
  @execP R [::] _ sample_pair1213' tt [set (true, false)] = (1 / 3)%:E.
Proof.
rewrite exec_sample_pair1213' !diracE memNset// mem_set//; do 2 rewrite memNset//.
by rewrite /= !mule0 mule1 !add0e mule0 adde0; congr (_%:E); lra.
Qed.

Lemma exec_sample_pair1213_TorT :
  (projT1 (execD sample_pair1213)) tt [set p | p.1 || p.2] = (2 / 3)%:E.
Proof.
rewrite execD_normalize_pt normalizeE/= exec_sample_pair1213'.
rewrite !diracE; do 4 rewrite mem_set//=.
rewrite eqe ifF; last by apply/negbTE/negP => /orP[/eqP|//]; lra.
rewrite exec_sample_pair1213' !diracE; do 3 rewrite mem_set//; rewrite memNset//=.
by rewrite !mule1; congr (_%:E); field.
Qed.

End sample_pair.

Section sample_and.
Local Open Scope lang_scope.
Local Open Scope ring_scope.
Import Notations.
Context {R : realType}.

Definition sample_and1213' : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli [{1 / 2}:R]} in
   let "y" := Sample {exp_bernoulli [{1 / 3}:R]} in
   return #{"x"} && #{"y"}].

Lemma exec_sample_and1213' (A : set bool) :
  @execP R [::] _ sample_and1213' tt A = ((1 / 6)%:E * \d_true A +
                                          (1 - 1 / 6)%:E * \d_false A)%E.
Proof.
rewrite !execP_letin !execP_sample/= !execD_bernoulli execP_return /=.
rewrite !(@execD_bin _ _ binop_and) !exp_var'E (execD_var_erefl "x").
rewrite (execD_var_erefl "y") /= !letin'E/= !execD_real/=.
rewrite integral_bernoulli//=; last lra.
rewrite !letin'E/= integral_bernoulli//=; last lra.
rewrite integral_bernoulli//=; last lra.
rewrite /onem.
rewrite muleDr// -addeA; congr (_ + _)%E.
  by rewrite !muleA; congr (_%:E); congr (_ * _); field.
rewrite -muleDl// !muleA -muleDl//.
by congr (_%:E); congr (_ * _); field.
Qed.

Definition sample_and121212 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli [{1 / 2}:R]} in
   let "y" := Sample {exp_bernoulli [{1 / 2}:R]} in
   let "z" := Sample {exp_bernoulli [{1 / 2}:R]} in
   return #{"x"} && #{"y"} && #{"z"}].

Lemma exec_sample_and121212 t U :
  execP sample_and121212 t U = ((1 / 8)%:E * \d_true U +
                                (1 - 1 / 8)%:E * \d_false U)%E.
Proof.
rewrite !execP_letin !execP_sample !execD_bernoulli !execP_return /=.
rewrite !(@execD_bin _ _ binop_and) !exp_var'E (execD_var_erefl "x").
rewrite (execD_var_erefl "y") (execD_var_erefl "z") /= !execD_real/=.
do 3 (rewrite !letin'E/= integral_bernoulli//=; last lra).
do 2 (rewrite integral_bernoulli//=; last lra).
rewrite !letin'E/= integral_bernoulli//=; last lra.
rewrite !muleDr// -!addeA; congr (_ + _)%E.
  by rewrite !muleA; congr *%E; congr EFin; field.
rewrite !muleA -!muleDl//; congr *%E; congr EFin.
by rewrite /onem; field.
Qed.

End sample_and.

Section sample_score.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition bernoulli13_score := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] [{1 / 3}:R]} in
  let "_" := if #{"x"} then Score {1 / 3}:R else Score {2 / 3}:R in
  return #{"x"}].

Lemma exec_bernoulli13_score :
  execD bernoulli13_score = execD (exp_bernoulli [{1 / 5}:R]).
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= /bernoulli13_score execD_normalize_pt 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= exp_var'E.
rewrite (execD_var_erefl "x")/= !execP_return/= 2!execP_score !execD_real/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite /=.
rewrite integral_bernoulli//=; [|lra|by move=> b; rewrite integral_ge0].
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI !diracT !mule1.
rewrite ger0_norm//.
rewrite -EFinD/= eqe ifF; last first.
  by apply/negbTE/negP => /orP[/eqP|//]; rewrite /onem; lra.
rewrite integral_bernoulli//=; last lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_dirac//= !diracT !mul1e ger0_norm//.
rewrite exp_var'E (execD_var_erefl "x")/=.
rewrite !indicT/= !mulr1.
rewrite bernoulliE//=; last lra.
by rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM; congr (_%:E);
  rewrite !indicE /onem /=; case: (_ \in _); field.
Qed.

Definition bernoulli12_score := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] [{1 / 2}:R]} in
  let "r" := if #{"x"} then Score {1 / 3}:R else Score {2 / 3}:R in
  return #{"x"}].

Lemma exec_bernoulli12_score :
  execD bernoulli12_score = execD (exp_bernoulli [{1 / 3}:R]).
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= /bernoulli12_score execD_normalize_pt 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= exp_var'E.
rewrite (execD_var_erefl "x")/= !execP_return/= 2!execP_score !execD_real/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite /= integral_bernoulli//=; [|lra|by move=> b; rewrite integral_ge0].
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI !diracT !mule1.
rewrite ger0_norm//.
rewrite -EFinD/= eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite integral_bernoulli//=; last lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_dirac//= !diracT !mul1e ger0_norm//.
rewrite exp_var'E (execD_var_erefl "x")/=.
rewrite bernoulliE//=; last lra.
rewrite !mul1r.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite !indicT !indicE /onem /=; case: (_ \in _); field.
Qed.

(* https://dl.acm.org/doi/pdf/10.1145/2933575.2935313 (Sect. 4) *)
Definition bernoulli14_score := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] [{1 / 4}:R]} in
  let "r" := if #{"x"} then Score {5}:R else Score {2}:R in
  return #{"x"}].

Lemma exec_bernoulli14_score :
  execD bernoulli14_score = execD (exp_bernoulli [{5%:R / 11%:R}:R]).
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= execD_normalize_pt 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= !exp_var'E.
rewrite !execP_return/= 2!execP_score !execD_real/=.
rewrite !(execD_var_erefl "x")/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite /= integral_bernoulli//=; [|lra|by move=> b; rewrite integral_ge0].
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_cst//= !diracT !(mule1,mul1e).
rewrite !iteE/= /mscale/= !diracT !mule1.
rewrite ger0_norm//.
rewrite !indicT/= !mul1r.
rewrite -EFinD/= eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite integral_bernoulli//=; last lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm//.
rewrite !integral_dirac//= !diracT !mul1e ger0_norm//.
rewrite bernoulliE//=; last lra.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite !indicE /onem /=; case: (_ \in _); field.
Qed.

End sample_score.

Section sample_binomial.
Context {R : realType}.
Open Scope lang_scope.
Open Scope ring_scope.

Definition sample_binomial3 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_binomial 3 [{1 / 2}:R]} in
   return #{"x"}].

Lemma exec_sample_binomial3 t U : measurable U ->
  execP sample_binomial3 t U = ((1 / 8)%:E * \d_0%N U +
                                (3 / 8)%:E * \d_1%N U +
                                (3 / 8)%:E * \d_2%N U +
                                (1 / 8)%:E * \d_3%N U)%E.
Proof.
move=> mU; rewrite /sample_binomial3 execP_letin execP_sample execP_return.
rewrite exp_var'E (execD_var_erefl "x") !execD_binomial/= execD_real//=.
rewrite letin'E/= /= integral_binomial//=; [lra|move=> _].
rewrite !big_ord_recl big_ord0/=.
rewrite /bump.
rewrite !binS/= !bin0 bin1 bin2 bin_small// addn0.
rewrite expr0 mulr1 mul1r subn0.
rewrite -2!addeA !mul1r.
congr _%:E.
rewrite !indicE /onem !addrA addr0 expr1/=.
by congr (_ + _ + _ + _); congr (_ * _); field.
Qed.

End sample_binomial.

Section hard_constraint.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType} {str : string}.

Definition hard_constraint g : @exp R _ g _ :=
  [let str := Score {0}:R in return TT].

Lemma exec_hard_constraint g mg U :
  execP (hard_constraint g) mg U = fail' (false, tt) U.
Proof.
rewrite execP_letin execP_score execD_real execP_return execD_unit/=.
rewrite letin'E integral_indic//= /mscale/= normr0 mul0e.
by rewrite /fail' letin'E/= ge0_integral_mscale//= normr0 mul0e.
Qed.

Lemma exec_score_fail (r : R) (r01 : (0 <= r <= 1)%R) :
  execP (g := [::]) [Score {r}:R] =
  execP [let str := Sample {exp_bernoulli [{r}:R]} in
         if #str then return TT else {hard_constraint _}].
Proof.
move: r01 => /andP[r0 r1]//.
rewrite execP_score execD_real /= score_fail' ?r0 ?r1//.
rewrite execP_letin execP_sample/= execD_bernoulli execP_if execP_return.
rewrite execD_unit/= exp_var'E /=.
  exact/ctx_prf_head (* TODO *).
move=> h.
apply: eq_sfkernel=> /= -[] U.
rewrite [LHS]letin'E/= [RHS]letin'E/=.
rewrite execD_real/=.
apply: eq_integral => b _.
rewrite 2!iteE//=.
case: b => //=.
- suff : projT1 (@execD R _ _ (exp_var str h)) (true, tt) = true by move=> ->.
  set g := [:: (str, Bool)].
  have /= := @execD_var R [:: (str, Bool)] str.
  by rewrite eqxx => /(_ h) ->.
- have -> : projT1 (@execD R _ _ (exp_var str h)) (false, tt) = false.
    set g := [:: (str, Bool)].
    have /= := @execD_var R [:: (str, Bool)] str.
    by rewrite eqxx /= => /(_ h) ->.
  by rewrite (@exec_hard_constraint [:: (str, Bool)]).
Qed.

End hard_constraint.

Section test_uniform.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Context (R : realType).

Definition uniform_syntax : @exp R _ [::] _ :=
  [let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
   return #{"p"}].

Lemma exec_uniform_syntax t U : measurable U ->
  execP uniform_syntax t U = uniform_prob (@ltr01 R) U.
Proof.
move=> mU.
rewrite /uniform_syntax execP_letin execP_sample execP_return !execD_uniform.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite letin'E /=.
rewrite integral_uniform//=; last exact: measurable_fun_dirac.
rewrite subr0 invr1 mul1e.
rewrite {1}/uniform_prob.
rewrite integral_mkcond//=.
rewrite [in RHS]integral_mkcond//=.
apply: eq_integral => x _.
rewrite !patchE.
case: ifPn => //; case: ifPn => //.
- move=> xU.
  rewrite inE/= in_itv/= => x01.
  by rewrite /uniform_pdf x01 diracE xU subr0 invr1.
- by rewrite diracE => /negbTE ->.
- move=> xU.
  rewrite notin_setE/= in_itv/= => /negP/negbTE x01.
  by rewrite /uniform_pdf x01.
Qed.

End test_uniform.

Section guard.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Context (R : realType).

Definition guard : @exp R _ [::] _ := [
  let "p" := Sample {exp_bernoulli [{1 / 3}:R]} in
  let "_" := if #{"p"} then return TT else Score {0}:R in
  return #{"p"}
].

Lemma exec_guard t U : execP guard t U = ((1 / 3)%:E * \d_true U)%E.
Proof.
rewrite /guard 2!execP_letin execP_sample execD_bernoulli execD_real.
rewrite execP_if/= !execP_return !exp_var'E !(execD_var_erefl "p") execD_unit.
rewrite execP_score execD_real/=.
rewrite letin'E/= integral_bernoulli//=; last lra.
rewrite !letin'E !iteE/= integral_dirac// ge0_integral_mscale//=.
by rewrite normr0 mul0e !mule0 !adde0 !diracT !mul1e.
Qed.

End guard.

Section test_binomial.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Context (R : realType).

Definition binomial_le : @exp R _ [::] Bool :=
  [let "a2" := Sample {exp_binomial 3 [{1 / 2}:R]} in
   return {1}:N <= #{"a2"}].

Lemma exec_binomial_le t U :
  execP binomial_le t U = ((7 / 8)%:E * \d_true U +
                          (1 / 8)%:E * \d_false U)%E.
Proof.
rewrite /binomial_le execP_letin execP_sample execP_return execD_rel execD_nat.
rewrite exp_var'E (execD_var_erefl "a2") execD_binomial/= !execD_real/=.
rewrite letin'E//= integral_binomial//=; [lra|move=> _].
rewrite !big_ord_recl big_ord0//=.
rewrite /bump.
rewrite !binS/= !bin0 bin1 bin2 bin_small// addn0.
rewrite addeC adde0.
congr (_ + _)%:E.
  rewrite !indicE !(mul0n,add0n,lt0n,mul1r)/=.
  rewrite -!mulrDl; congr (_ * _).
  rewrite /onem.
  lra.
rewrite !expr0 ltnn indicE/= !(mul1r,mul1e) /onem.
lra.
Qed.

Definition binomial_guard : @exp R _ [::] Nat :=
  [let "a1" := Sample {exp_binomial 3 [{1 / 2}:R]} in
   let "_" := if #{"a1"} == {1}:N then return TT else Score {0}:R in
   return #{"a1"}].

Lemma exec_binomial_guard t U :
  execP binomial_guard t U = ((3 / 8)%:E * \d_1%N U)%E.
Proof.
rewrite /binomial_guard !execP_letin execP_sample execP_return execP_if.
rewrite !exp_var'E execD_rel !(execD_var_erefl "a1") execP_return.
rewrite execD_unit execD_binomial execD_nat execP_score !execD_real.
rewrite !letin'E//=.
rewrite integral_binomial//=; [lra|move=> _].
rewrite !big_ord_recl big_ord0.
rewrite /bump/=.
rewrite !binS/= !bin0 bin1 bin2 bin_small//.
rewrite !letin'E//= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//= !diracE/=.
rewrite /bump/=.
rewrite !(normr0,mul0e,mule0,add0e,add0n,mul1e,adde0).
rewrite mem_set//=.
rewrite /onem mul1e.
congr (_%:E * _)%E.
lra.
Qed.

End test_binomial.

Section beta_bernoulli_bernoulli.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := (@lebesgue_measure R).

(* TODO: move? *)
Lemma integrable_bernoulli_XMonemX01 a b U
  (mu : {measure set (g_sigma_algebraType R.-ocitv.-measurable) -> \bar R}) :
  measurable U -> (mu `[0%R, 1%R]%classic < +oo)%E ->
  mu.-integrable `[0, 1] (fun x => bernoulli (XMonemX01 a b x) U).
Proof.
move=> mU mu01oo.
apply/integrableP; split.
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  by apply: measurable_funTS; exact: measurable_XMonemX01.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R]) cst 1 x)%E).
  apply: ge0_le_integral => //=.
    apply/measurable_funTS/measurableT_comp => //=.
    apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
    exact: measurable_XMonemX01.
  by move=> x _; rewrite gee0_abs// probability_le1.
by rewrite integral_cst//= mul1e.
Qed.

Let measurable_bernoulli_XMonemX01 U :
   measurable_fun setT (fun x : R => bernoulli (XMonemX01 2 1 x) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
exact: measurable_XMonemX01.
Qed.

Lemma beta_bernoulli_bernoulli U : measurable U ->
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli [#{"p"}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli [{3 / 5}:R]}] tt U.
Proof.
move=> mU.
rewrite execP_letin !execP_sample execD_beta !execD_bernoulli/=.
rewrite !execD_real/= exp_var'E (execD_var_erefl "p")/=.
transitivity (beta_prob_bernoulli 6 4 1 0 U : \bar R).
  rewrite /beta_prob_bernoulli !letin'E/=.
  rewrite integral_beta_prob//=; last 2 first.
    exact: measurable_bernoulli2.
    exact: integral_beta_prob_bernoulli_lty.
  rewrite integral_beta_prob//=; last 2 first.
    by apply: measurable_funTS => /=; exact: measurable_bernoulli_XMonemX01.
    rewrite integral_beta_prob//=.
    + suff: mu.-integrable `[0%R, 1%R]
          (fun x => bernoulli (XMonemX01 2 1 x) U * (beta_pdf 6 4 x)%:E)%E.
        move=> /integrableP[_].
        under eq_integral.
          move=> x _.
          rewrite gee0_abs//; last first.
            by rewrite mule_ge0// lee_fin beta_pdf_ge0.
        over.
        move=> ?.
        by under eq_integral do rewrite gee0_abs//.
    + apply: integrableMl => //=.
      * apply: integrable_bernoulli_XMonemX01 => //=.
        by rewrite lebesgue_measure_itv//= lte01 EFinN sube0 ltry.
      * by apply: measurable_funTS; exact: measurable_beta_pdf.
      * exact: bounded_beta_pdf_01.
    + apply/measurableT_comp => //; apply: measurable_funTS => /=.
      exact: measurable_bernoulli_XMonemX01.
    + under eq_integral do rewrite gee0_abs//=.
      have : (beta_prob 6 4 `[0%R, 1%R] < +oo :> \bar R)%E.
        by rewrite -ge0_fin_numE// beta_prob_fin_num.
      by move=> /(@integrable_bernoulli_XMonemX01 2 1 _ (beta_prob 6 4) mU) /integrableP[].
  rewrite [RHS]integral_mkcond.
  apply: eq_integral => x _ /=.
  rewrite patchE.
  case: ifPn => x01.
    by rewrite /XMonemX01 patchE x01 XMonemX0' expr1.
  by rewrite /beta_pdf /XMonemX01 patchE (negbTE x01) mul0r mule0.
rewrite beta_prob_bernoulliE// !bernoulliE//=; last 2 first.
  lra.
  by rewrite div_betafun_ge0 div_betafun_le1.
by congr (_ * _ + _ * _)%:E;
  rewrite /div_betafun/= /onem !betafunE/= !factE/=; field.
Qed.

End beta_bernoulli_bernoulli.

Section letinA.
Local Open Scope lang_scope.
Variable R : realType.

Lemma letinA g x y t1 t2 t3 (xyg : x \notin dom ((y, t2) :: g))
  (e1 : @exp R P g t1)
  (e2 : exp P [:: (x, t1) & g] t2)
  (e3 : exp P [:: (y, t2) & g] t3) :
  forall U, measurable U ->
  execP [let x := e1 in
         let y := e2 in
         {@exp_weak _ _ [:: (y, t2)] _ _ (x, t1) e3 xyg}] ^~ U =
  execP [let y :=
           let x := e1 in e2 in
         e3] ^~ U.
Proof.
move=> U mU; apply/funext=> z1.
rewrite !execP_letin.
rewrite (execP_weak [:: (y, t2)]).
apply: letin'A => //= z2 z3.
rewrite /kweak /mctx_strong /=.
by destruct z3.
Qed.

Example letinA12 : forall U, measurable U ->
  @execP R [::] _ [let "y" := return {1}:R in
                   let "x" := return {2}:R in
                   return #{"x"}] ^~ U =
  @execP R [::] _ [let "x" :=
                   let "y" := return {1}:R in return {2}:R in
                   return #{"x"}] ^~ U.
Proof.
move=> U mU.
rewrite !execP_letin !execP_return !execD_real.
apply: funext=> x.
rewrite !exp_var'E /= !(execD_var_erefl "x")/=.
exact: letin'A.
Qed.

End letinA.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition staton_bus_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli [{2 / 7}:R]} in
   let "r" := if #{"x"} then return {3}:R else return {10}:R in
   let "_" := Score {exp_poisson 4 [#{"r"}]} in
   return #{"x"}].

Definition staton_bus_syntax := [Normalize {staton_bus_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool :=
  sample _ (measurableT_comp measurable_bernoulli (measurable_cst (2 / 7 : R)%R)).

Let ite_3_10 : R.-sfker mbool * munit ~> measurableTypeR R :=
  ite macc0of2 (@ret _ _ _ (measurableTypeR R) R _ (kr 3)) (@ret _ _ _ (measurableTypeR R) R _ (kr 10)).

Let score_poisson4 : R.-sfker measurableTypeR R * (mbool * munit) ~> munit :=
  score (measurableT_comp (measurable_poisson_pdf 4) (@macc0of2 _ _ (measurableTypeR R) _)).

Let kstaton_bus' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poisson4 (ret macc2of4'))).

Lemma eval_staton_bus0 : staton_bus_syntax0 -P> kstaton_bus'.
Proof.
apply: eval_letin.
  by apply: eval_sample; apply: eval_bernoulli; exact: eval_real.
apply: eval_letin.
  apply/evalP_if; [|exact/eval_return/eval_real..].
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var_erefl "x")/=; congr existT.
apply: eval_letin.
  apply/eval_score/eval_poisson.
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var_erefl "r")/=; congr existT.
apply/eval_return/execD_evalD.
by rewrite exp_var'E (execD_var_erefl "x")/=; congr existT.
Qed.

Lemma exec_staton_bus0' : execP staton_bus_syntax0 = kstaton_bus'.
Proof.
rewrite 3!execP_letin execP_sample/= execD_bernoulli/= !execD_real.
rewrite /kstaton_bus'; congr letin'.
rewrite !execP_if !execP_return !execD_real/=.
rewrite exp_var'E (execD_var_erefl "x")/=.
have -> : measurable_acc_typ [:: Bool] 0 = macc0of2 by [].
congr letin'.
rewrite execP_score execD_poisson/=.
rewrite exp_var'E (execD_var_erefl "r")/=.
have -> : measurable_acc_typ [:: Real; Bool] 0 = macc0of2 by [].
congr letin'.
by rewrite exp_var'E (execD_var_erefl "x") /=; congr ret.
Qed.

Lemma exec_staton_bus : execD staton_bus_syntax =
  existT _ (normalize_pt kstaton_bus') (measurable_normalize_pt _).
Proof. by rewrite execD_normalize_pt exec_staton_bus0'. Qed.

Let poisson4 := @poisson_pdf R 4%N.

Let staton_bus_probability U :=
  ((2 / 7)%:E * (poisson4 3)%:E * \d_true U +
  (5 / 7)%:E * (poisson4 10)%:E * \d_false U)%E.

Lemma exec_staton_bus0 (U : set bool) :
  execP staton_bus_syntax0 tt U = staton_bus_probability U.
Proof.
rewrite exec_staton_bus0' /staton_bus_probability /kstaton_bus'.
rewrite /sample_bern.
rewrite letin'E/=.
rewrite integral_bernoulli//=; last lra.
rewrite -!muleA; congr (_ * _ + _ * _)%E.
- rewrite letin'_iteT//.
  rewrite letin'_retk//.
  rewrite letin'_kret//.
  rewrite /score_poisson4.
  by rewrite /score/= /mscale/= ger0_norm//= poisson_pdf_ge0.
- by rewrite onem27.
- rewrite letin'_iteF//.
  rewrite letin'_retk//.
  rewrite letin'_kret//.
  rewrite /score_poisson4.
  by rewrite /score/= /mscale/= ger0_norm//= poisson_pdf_ge0.
Qed.

End staton_bus.

(* same as staton_bus module associativity of letin *)
Section staton_busA.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition staton_busA_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli [{2 / 7}:R]} in
   let "_" :=
     let "r" := if #{"x"} then return {3}:R else return {10}:R in
     Score {exp_poisson 4 [#{"r"}]} in
   return #{"x"}].

Definition staton_busA_syntax : exp _ [::] _ :=
  [Normalize {staton_busA_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool :=
  sample _ (measurableT_comp measurable_bernoulli (measurable_cst (2 / 7 : R)%R)).

Let ite_3_10 : R.-sfker mbool * munit ~> measurableTypeR R :=
  ite macc0of2 (@ret _ _ _ (measurableTypeR R) R _ (kr 3)) (@ret _ _ _ (measurableTypeR R) R _ (kr 10)).

Let score_poisson4 : R.-sfker measurableTypeR R * (mbool * munit) ~> munit :=
  score (measurableT_comp (measurable_poisson_pdf 4) (@macc0of3' _ _ _ (measurableTypeR R) _ _)).

(* same as kstaton_bus _ (measurable_poisson 4) but expressed with letin'
   instead of letin *)
Let kstaton_busA' :=
  letin' sample_bern
  (letin'
    (letin' ite_3_10
      score_poisson4)
    (ret macc1of3')).

Lemma eval_staton_busA0 : staton_busA_syntax0 -P> kstaton_busA'.
Proof.
apply: eval_letin.
  by apply: eval_sample; apply: eval_bernoulli; exact: eval_real.
apply: eval_letin.
  apply: eval_letin.
    apply/evalP_if; [|exact/eval_return/eval_real..].
    rewrite exp_var'E.
    by apply/execD_evalD; rewrite (execD_var_erefl "x")/=; congr existT.
  apply/eval_score/eval_poisson.
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var_erefl "r")/=; congr existT.
apply/eval_return.
by apply/execD_evalD; rewrite exp_var'E (execD_var_erefl "x")/=; congr existT.
Qed.

Lemma exec_staton_busA0' : execP staton_busA_syntax0 = kstaton_busA'.
Proof.
rewrite 3!execP_letin execP_sample/= execD_bernoulli execD_real.
rewrite /kstaton_busA'; congr letin'.
rewrite !execP_if !execP_return !execD_real/=.
rewrite exp_var'E (execD_var_erefl "x")/=.
have -> : measurable_acc_typ [:: Bool] 0 = macc0of2 by [].
congr letin'.
  rewrite execP_score execD_poisson/=.
  rewrite exp_var'E (execD_var_erefl "r")/=.
  by have -> : measurable_acc_typ [:: Real; Bool] 0 = macc0of3' by [].
by rewrite exp_var'E (execD_var_erefl "x") /=; congr ret.
Qed.

Lemma exec_statonA_bus : execD staton_busA_syntax =
  existT _ (normalize_pt kstaton_busA') (measurable_normalize_pt _).
Proof. by rewrite execD_normalize_pt exec_staton_busA0'. Qed.

(* equivalence between staton_bus and staton_busA *)
Lemma staton_bus_staton_busA :
  execP staton_bus_syntax0 = @execP R _ _ staton_busA_syntax0.
Proof.
rewrite /staton_bus_syntax0 /staton_busA_syntax0.
rewrite execP_letin.
rewrite [in RHS]execP_letin.
congr (letin' _).
set e1 := exp_if _ _ _.
set e2 := exp_score _.
set e3 := (exp_return _ in RHS).
pose f := @found _ Unit "x" Bool [::].
have r_f : "r" \notin [seq i.1 | i <- ("_", Unit) :: untag (ctx_of f)] by [].
have H := @letinA _ _ _ _ _ _
  (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")
  r_f e1 e2 e3.
apply/eq_sfkernel => /= x U.
have mU :
  (@mtyp_disp R (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")).-measurable U.
  by [].
move: H => /(_ U mU) /(congr1 (fun f => f x)) <-.
set e3' := exp_return _.
set e3_weak := exp_weak _ _ _ _.
rewrite !execP_letin.
suff: execP e3' = execP (e3_weak e3 r_f) by move=> <-.
rewrite execP_return/= exp_var'E (execD_var_erefl "x") /= /e3_weak.
rewrite (@execP_weak R [:: ("_", Unit)] _ ("r", Real) _ e3 r_f).
rewrite execP_return exp_var'E/= (execD_var_erefl "x") //=.
by apply/eq_sfkernel => /= -[[] [a [b []]]] U0.
Qed.

Let poisson4 := @poisson_pdf R 4%N.

Lemma exec_staton_busA0 U : execP staton_busA_syntax0 tt U =
  ((2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U)%E.
Proof. by rewrite -staton_bus_staton_busA exec_staton_bus0. Qed.

End staton_busA.

Section letinC.
Local Open Scope lang_scope.
Variable (R : realType).

Let weak_head g {t1 t2} x (e : @exp R P g t2) (xg : x \notin dom g) :=
  exp_weak P [::] _ (x, t1) e xg.

Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : exp P g t2)
  (x y : string)
  (xy : infer (x != y)) (yx : infer (y != x))
  (xg : x \notin dom g) (yg : y \notin dom g) :
  forall U, measurable U ->
  execP [
    let x := e1 in
    let y := {weak_head e2 xg} in
    return (#x, #y)] ^~ U =
  execP [
    let y := e2 in
    let x := {weak_head e1 yg} in
    return (#x, #y)] ^~ U.
Proof.
move=> U mU; apply/funext => z.
rewrite 4!execP_letin.
rewrite 2!(execP_weak [::] g).
rewrite 2!execP_return/=.
rewrite 2!execD_pair/=.
rewrite !exp_var'E.
- exact/(ctx_prf_tail _ yx)/ctx_prf_head.
- exact/ctx_prf_head.
- exact/ctx_prf_head.
- exact/(ctx_prf_tail _ xy)/ctx_prf_head.
- move=> h1 h2 h3 h4.
  set g1 := [:: (y, t2), (x, t1) & g].
  set g2 := [:: (x, t1), (y, t2) & g].
  have /= := @execD_var R g1 x.
  rewrite (negbTE yx) eqxx => /(_ h4) ->.
  have /= := @execD_var R g2 x.
  rewrite (negbTE yx) eqxx => /(_ h2) ->.
  have /= := @execD_var R g1 y.
  rewrite eqxx => /(_ h3) ->.
  have /= := @execD_var R g2 y.
  rewrite (negbTE xy) eqxx => /(_ h1) -> /=.
  have -> : measurable_acc_typ [:: t2, t1 & map snd g] 0 = macc0of3' by [].
  have -> : measurable_acc_typ [:: t2, t1 & map snd g] 1 = macc1of3' by [].
  rewrite (letin'C _ _ (execP e2)
    [the R.-sfker _ ~> _ of @kweak _ [::] _ (y, t2) _ (execP e1)]);
    [ |by [] | by [] |by []].
  have -> : measurable_acc_typ [:: t1, t2 & map snd g] 0 = macc0of3' by [].
  by have -> : measurable_acc_typ [:: t1, t2 & map snd g] 1 = macc1of3' by [].
Qed.

Example letinC_ground_variables g t1 t2 (e1 : @exp R P g t1) (e2 : exp P g t2)
  (x := "x") (y := "y")
  (xg : x \notin dom g) (yg : y \notin dom g) :
  forall U, measurable U ->
  execP [
    let x := e1 in
    let y := {exp_weak _ [::] _ (x, t1) e2 xg} in
    return (#x, #y)] ^~ U =
  execP [
    let y := e2 in
    let x := {exp_weak _ [::] _ (y, t2) e1 yg} in
    return (#x, #y)] ^~ U.
Proof. by move=> U mU; rewrite letinC. Qed.

Example letinC_ground (g := [:: ("a", Unit); ("b", Bool)]) t1 t2
    (e1 : @exp R P g t1)
    (e2 : exp P g t2) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := e2 :+ {"x"} in
         return (#{"x"}, #{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := e1 :+ {"y"} in
         return (#{"x"}, #{"y"})] ^~ U.
Proof. move=> U mU; exact: letinC. Qed.

End letinC.
