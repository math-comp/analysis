Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.
Require Import lang_syntax_util lang_syntax.
From mathcomp Require Import ring lra.

(******************************************************************************)
(*  Casino example                                                            *)
(*  some steps *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
(* Local Open Scope ereal_scope. *)

Section trunc_lemmas.
Open Scope ring_scope.
Open Scope lang_scope.
Context (R : realType).

Lemma bernoulli_truncE (p : R) U :
  (0 <= p <= 1)%R ->
  (bernoulli_trunc p U =
  p%:E * \d_true U + (`1-p)%:E * \d_false U)%E.
Proof.
move=> /andP[p0 p1].
rewrite /bernoulli_trunc.
case: (sumbool_ler 0 p) => [{}p0/=|].
  case: (sumbool_ler p 1) => [{}p1/=|].
    by rewrite /bernoulli/= measure_addE.
  by rewrite ltNge p1.
by rewrite ltNge p0.
Qed.

Lemma __ p p1 :
  @execD R [::] _ (exp_bernoulli p p1) =
  execD (exp_bernoulli_trunc [{p%:num}:R]).
Proof.
apply: eq_execD.
rewrite execD_bernoulli execD_bernoulli_trunc execD_real/=.
apply: funext=> x /=.
rewrite /bernoulli_trunc.
case: (sumbool_ler 0 p%:num) => [{}p0/=|].
  case: (sumbool_ler p%:num 1) => [{}p1'/=|].
    admit.
Abort.

End trunc_lemmas.

Section beta_example.
Open Scope ring_scope.
Open Scope lang_scope.
Context (R : realType).

Let p610 : ((6 / 10%:R)%:nng : {nonneg R})%:num <= 1.
Proof. admit. Admitted.

Lemma beta_bernoulli :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in Sample {exp_bernoulli_trunc [#{"p"}]}] =
  execP [Sample {@exp_bernoulli _ _ (6 / 10%:R)%:nng p610}].
Proof.
rewrite execP_letin !execP_sample !execD_beta_nat !execD_bernoulli/=.
rewrite execD_bernoulli_trunc exp_var'E !(execD_var_erefl "p")/=.
apply: eq_sfkernel=> x U.
rewrite letin'E/=.
rewrite /beta_nat/mscale/=.
transitivity (bernoulli_trunc ((@beta_nat_norm R 7 4) / (@beta_nat_norm R 6 4)) U); last first.
  (* congr (bernoulli_trunc _ _). *)
  (* rewrite /beta_nat_norm/= factE/=; lra. *)
(* apply: beta_nat_bern_bern. *)
Admitted.

End beta_example.

Section casino_example.
Open Scope ring_scope.
Open Scope lang_scope.
Context (R : realType).
Lemma a01 : 0 < 1 - 0 :> R. Proof. by []. Qed.

(* guard test *)
Definition test_guard : @exp R _ [::] _ := [
  let "p" := Sample {exp_bernoulli (1 / 3)%:nng (p1S 2)} in
  let "_" := if #{"p"} then return TT else Score {0}:R in
  return #{"p"}
].

Lemma exec_guard t U : execP test_guard t U = ((1 / 3)%:E * \d_true U)%E.
Proof.
rewrite /test_guard 2!execP_letin execP_sample execD_bernoulli execP_if/=.
rewrite !execP_return !exp_var'E !(execD_var_erefl "p") execD_unit execP_score execD_real/=.
rewrite letin'E ge0_integral_measure_sum//.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//= !integral_dirac//.
rewrite !letin'E !iteE/= integral_dirac// ge0_integral_mscale//=.
by rewrite normr0 mul0e !mule0 !adde0 !diracT !mul1e.
Qed.

Lemma binomial_over1 n p U :
  0 <= p <= 1 ->
  (\int[binomial_probability_trunc n p]_y0 \d_(0 < y0)%N U =
  bernoulli_trunc (1 - `1-p ^+ n) U :> \bar R)%E.
Proof.
move=> /andP[p0 p1].
rewrite bernoulli_truncE; last first.
  apply/andP; split.
    apply/onemX_ge0; rewrite /onem; lra.
  apply/onem_le1/exprn_ge0; rewrite /onem; lra.
rewrite (@integral_binomial_probabilty_trunc _ n p _ _ (fun y => \d_(1 <= y)%N U))//; last first.
rewrite !big_ord_recl/=.
rewrite /bump.
under eq_bigr => i _.
  rewrite /=.
  have -> : (0 < 1 + i)%N => //.
  over.
rewrite addeC -ge0_sume_distrl.
  congr (_ + _)%E; congr (_ * _)%E.
  have -> : (\sum_(i < n) (p ^+ (1 + i) * `1-p ^+ (n - (1 + i)) *+ 'C(n, 1 + i))%:E)%E =
  (\sum_(i < n.+1) (p ^+ i * `1-p ^+ (n - i) *+ 'C(n, i))%:E - (`1-p ^+ n)%:E)%E.
    rewrite big_ord_recl/= expr0 subn0 mul1r bin0 mulr1n addeC addeA.
    have <- : 0%E = ((- `1-p ^+ n)%:E + (`1-p ^+ n)%:E)%E.
      rewrite EFinN.
      congr _%:E.
      lra.
    by rewrite add0e.
  congr _%E.
  rewrite sumEFin.
  rewrite !EFinB EFin_expe.
  congr (_ - _)%E.
  under eq_bigr do rewrite mulrC.
  rewrite -(@exprDn_comm _ `1-p p n); last first.
    by rewrite /GRing.comm/onem; lra.
  rewrite /onem addrC.
  have -> : p + (1 - p) = 1 by lra.
  by rewrite expr1n.
  rewrite subn0 expr0 bin0 mulr1n.
  rewrite /onem.
  congr _%:E.
  set pn := (1-p) ^+ n.
  lra.
move=> i _.
apply/mulrn_wge0/mulr_ge0; apply/exprn_ge0.
exact: p0.
apply/onem_ge0/p1.
Qed.

Lemma binomial_le1 n p U :
  0 <= p <= 1 ->
  (\int[binomial_probability_trunc n p]_y0 \d_(0 < y0)%N U =
  \int[bernoulli_trunc (1 - `1-p ^+ n)]_y0 \d_y0 U :> \bar R)%E.
Proof.
move=> /andP[p0 p1].
rewrite (@integral_bernoulli_trunc _ _ (fun x => \d_x U))//; last first.
  apply/andP; split.
    apply: onemX_ge0; rewrite /onem; lra.
  apply/onem_le1/exprn_ge0; rewrite /onem; lra.
rewrite (@integral_binomial_probabilty_trunc _ n p _ _ (fun y => \d_(1 <= y)%N U))//; last first.
rewrite !big_ord_recl/=.
rewrite /bump.
under eq_bigr => i _.
  rewrite /=.
  have -> : (0 < 1 + i)%N => //.
  over.
rewrite addeC -ge0_sume_distrl.
  congr (_ + _)%E; congr (_ * _)%E.
  have -> : (\sum_(i < n) (p ^+ (1 + i) * `1-p ^+ (n - (1 + i)) *+ 'C(n, 1 + i))%:E)%E =
  (\sum_(i < n.+1) (p ^+ i * `1-p ^+ (n - i) *+ 'C(n, i))%:E - (`1-p ^+ n)%:E)%E.
    rewrite big_ord_recl/= expr0 subn0 mul1r bin0 mulr1n addeC addeA.
    have <- : 0%E = ((- `1-p ^+ n)%:E + (`1-p ^+ n)%:E)%E.
      rewrite EFinN.
      congr _%:E.
      lra.
    by rewrite add0e.
  congr _%E.
  rewrite sumEFin.
  rewrite !EFinB EFin_expe.
  congr (_ - _)%E.
  under eq_bigr do rewrite mulrC.
  rewrite -(@exprDn_comm _ `1-p p n); last first.
    by rewrite /GRing.comm/onem; lra.
  rewrite /onem addrC.
  have -> : p + (1 - p) = 1 by lra.
  by rewrite expr1n.
  rewrite subn0 expr0 bin0 mulr1n.
  rewrite /onem.
  congr _%:E.
  set pn := (1-p) ^+ n.
  lra.
move=> i _.
apply/mulrn_wge0/mulr_ge0; apply/exprn_ge0.
exact: p0.
apply/onem_ge0/p1.
Qed.

Lemma __ : uniform_probability a01 `[0, (1 / 2)] = (1 / 2)%:E.
Proof.
rewrite /uniform_probability /mscale/= /mrestr.
Abort.

Lemma letin'_sample_uniform d d' (T : measurableType d)
    (T' : measurableType d') (a b : R) (ab0 : (0 < b - a)%R)
    (u : R.-sfker [the measurableType _ of (_ * T)%type] ~> T') x y :
  measurable y ->
  letin' (sample_cst (uniform_probability ab0)) u x y =
  ((b - a)^-1%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y)%E.
Proof.
move=> my; rewrite letin'E/=.
rewrite integral_uniform//= => _ /= Y mY /=.
have /= := measurable_kernel u _ my measurableT _ mY.
move/measurable_ysection => /(_ R x) /=.
set A := (X in measurable X).
set B := (X in _ -> measurable X).
suff : A = B by move=> ->.
rewrite {}/A {}/B !setTI /ysection/= (*TODO: lemma?*) /preimage/=.
by apply/seteqP; split => [z|z] /=; rewrite inE/=.
Qed.

Lemma execP_letin_uniform g t str (s0 s1 : exp P ((str, Real) :: g) t) :
  (forall (p : R) x U, 0 <= p <= 1 ->
    execP s0 (p, x) U = execP s1 (p, x) U) ->
  forall x U, measurable U ->
  execP [let str := Sample {@exp_uniform _ g 0 1 a01} in {s0}] x U =
  execP [let str := Sample {@exp_uniform _ g 0 1 a01} in {s1}] x U.
Proof.
move=> s01 x U mU.
rewrite !execP_letin execP_sample execD_uniform/=.
rewrite !letin'_sample_uniform//.
congr (_ * _)%E.
apply: eq_integral => p p01.
apply: s01.
by rewrite inE in p01.
Qed.

Lemma congr_letin g t1 t2 str (e : @exp _ _ _ t1) (e1 e2 : @exp _ _ (_ :: g) t2) x U :
  (forall y V, execP e1 (y, x) V = execP e2 (y, x) V) ->
  @execP R g t2 [let str := e in e1] x U = @execP R g t2 [let str := e in e2] x U.
Proof.
move=> He.
rewrite !execP_letin !letin'E.
apply: eq_integral => ? _.
apply: He.
Qed.

Lemma congr_normalize g t (e1 e2 : @exp R _ g t) :
  (forall x U, execP e1 x U = execP e2 x U) ->
  execD [Normalize e1] = execD [Normalize e2].
Proof.
move=> He.
apply: eq_execD.
rewrite !execD_normalize_pt /=.
f_equal.
apply: eq_kernel => y V.
apply: He.
Qed.

Definition uniform_syntax : @exp R _ [::] _ :=
  [let "p" := Sample {exp_uniform 0 1 a01} in
   return #{"p"}].

Lemma exec_uniform_syntax t U : measurable U ->
  execP uniform_syntax t U = uniform_probability a01 U.
Proof.
move=> mU.
rewrite /uniform_syntax execP_letin execP_sample execP_return !execD_uniform.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite letin'E /=.
rewrite integral_uniform//=; last exact: measurable_fun_dirac.
rewrite subr0 invr1 mul1e.
rewrite {1}/uniform_probability.
rewrite /mscale/= subr0 invr1 mul1e.
by rewrite integral_indic.
Qed.

Definition binomial_le : @exp R _ [::] Bool :=
  [let "a2" := Sample {exp_binomial 3 (1 / 2)%:nng (p1S 1)} in
   return {1}:N <= #{"a2"}].

Lemma exec_binomial_le t U :
  execP binomial_le t U = ((7 / 8)%:E * \d_true U +
                          (1 / 8)%:E * \d_false U)%E.
Proof.
rewrite /binomial_le execP_letin execP_sample execP_return execD_rel execD_nat.
rewrite exp_var'E (execD_var_erefl "a2") execD_binomial.
rewrite letin'E//= /binomial_probability ge0_integral_measure_sum//=.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//=.
rewrite !integral_dirac// /bump.
rewrite !binS/= !bin0 bin1 bin2 bin_small// addn0.
rewrite addeC adde0.
congr (_ + _)%:E.
  rewrite !indicT !(mul0n,add0n,lt0n,mul1r)/=.
  rewrite -!mulrDl; congr (_ * _).
  rewrite /onem.
  lra.
rewrite !expr0 ltnn indicT/= !(mul1r,mul1e) /onem.
lra.
Qed.

Definition binomial_guard : @exp R _ [::] Nat :=
  [let "a1" := Sample {exp_binomial 3 (1 / 2)%:nng (p1S 1)} in
   let "_" := if #{"a1"} == {1}:N then return TT else Score {0}:R in
   return #{"a1"}].

Lemma exec_binomial_guard t U :
  execP binomial_guard t U = ((3 / 8)%:E * \d_1%N U(* +
                             (1 / 8)%:E * \d_0%N U*))%E.
Proof.
rewrite /binomial_guard !execP_letin execP_sample execP_return execP_if.
rewrite !exp_var'E execD_rel !(execD_var_erefl "a1") execP_return.
rewrite execD_unit execD_binomial execD_nat execP_score execD_real.
rewrite !letin'E//= /binomial_probability ge0_integral_measure_sum//=.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//=.
rewrite !integral_dirac//.
rewrite /bump/=.
rewrite !binS/= !bin0 bin1 bin2 bin_small//.
rewrite !diracT !addn0 !expr0 !subn0 !mulr1n !mul1r !expr1 !mul1e.
rewrite !letin'E//= !iteE/= !diracE/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac// !diracT//.
rewrite !(normr0,mul0e,mule0,add0e,add0n,mul1e,adde0).
rewrite /onem.
congr (_%:E * _)%E.
lra.
Qed.

Lemma exec_beta_a1 U :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli_trunc [#{"p"}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli_trunc [{3 / 5}:R]}] tt U.
Proof.
rewrite execP_letin !execP_sample execD_beta_nat !execD_bernoulli_trunc/=.
rewrite !execD_real/= exp_var'E (execD_var_erefl "p")/=.
transitivity (beta_nat_bern 6 4 1 0 tt U : \bar R).
  rewrite /beta_nat_bern !letin'E/= /ubeta_nat_pdf/= /onem.
  apply: eq_integral => x _.
  rewrite /=.
  do 2 f_equal.
  by rewrite /ubeta_nat_pdf' expr1 expr0 mulr1.
rewrite beta_nat_bern_bern/= /bernoulli/= bernoulli_truncE; last by lra.
rewrite measure_addE/= /mscale/=.
congr (_ * _ + _ * _)%:E.
  rewrite /Baa'bb'Bab /beta_nat_norm/=.
  rewrite !factS/= fact0.
  by field.
rewrite /onem; rewrite /Baa'bb'Bab /beta_nat_norm/=;
rewrite !factS/= fact0.
by field.
Qed.

Definition casino0 : @exp R _ [::] _ :=
  [Normalize
   let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   let "a2" := Sample {exp_binomial_trunc 3 [#{"p"}]} in
   return {1}:N <= #{"a2"}].

Definition casino1 : @exp R _ [::] _ :=
  [Normalize
   let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Lemma casino01 :
  execD casino0 = execD casino1.
Proof.
rewrite /casino0 /casino1.
apply: eq_execD.
f_equal.
apply: congr_normalize => y V.
apply: execP_letin_uniform => //.
move=> p x U r01.
apply: congr_letin => y0 V0.
apply: congr_letin => y1 V1.
rewrite !execP_letin !execP_sample !execD_binomial_trunc /=.
rewrite !execP_return !execD_bernoulli_trunc/=.
rewrite !execD_rel (@execD_bin _ _ binop_minus) execD_pow.
rewrite (@execD_bin _ _ binop_minus) !execD_real/= !execD_nat.
rewrite !exp_var'E !(execD_var_erefl "p") !(execD_var_erefl "a2")/=.
rewrite !letin'E/=.
move: r01 => /andP[r0 r1].
by apply/binomial_over1/andP.
Qed.

Definition casino2 : @exp R _ [::] _ :=
  [Normalize
   let "p" := Sample {exp_uniform 0 1 a01} in 
   let "_" := Score {[{56}:R * #{"p"} ^+ {5%nat} * {[{1}:R - #{"p"}]} ^+ {3%nat}]} in
   Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Lemma casino12 :
  execD casino1 = execD casino2.
Proof.
apply: eq_execD.
f_equal.
apply: congr_normalize => y V.
apply: execP_letin_uniform => //.
move=> p x U /andP[p0 p1].
rewrite !execP_letin !execP_sample execP_if execD_rel/=.
rewrite !execP_score !(@execD_bin _ _ binop_mult).
rewrite !execD_bernoulli_trunc/= !(@execD_bin _ _ binop_minus) !execD_pow.
rewrite !(@execD_bin _ _ binop_minus)/=.
rewrite !execD_real !execD_nat/= execP_return execD_unit.
rewrite !execD_binomial_trunc/=.
rewrite !exp_var'E !(execD_var_erefl "p") !(execD_var_erefl "a1")/=.
rewrite !letin'E/=.
rewrite integral_binomial_probabilty_trunc//=.
rewrite (bigD1 (inord 5))//=.
  rewrite big1; last first.
  move=> [[|[|[|[|[|[|[|[|[|//]]]]]]]]]]//= Hi Hi5; rewrite letin'E iteE;
  rewrite ?ge0_integral_mscale//= ?normr0 ?mul0e ?mule0 ?add0e//.
  suff: false by [].
  move/negbTE: Hi5 => <-.
  by apply/eqP/val_inj => /=; rewrite inordK.
rewrite letin'E iteE ge0_integral_mscale//= inordK//= adde0 /onem.
congr (_ * _)%E.
rewrite ger0_norm.
  by rewrite -mulrA mulr_natl.
apply/mulr_ge0.
  exact/mulr_ge0/exprn_ge0.
apply/exprn_ge0.
by rewrite subr_ge0.
Qed.

Definition casino3 : @exp R _ [::] _ :=
  [Normalize
   let "_" := Score {1 / 9}:R in
   let "p" := Sample {exp_beta 6 4} in
   Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Lemma casino34' U :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli_trunc [{[{1}:R - #{"p"}]} ^+ {3%nat}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli_trunc [{1 / 11}:R]}] tt U.
Proof.
rewrite execP_letin !execP_sample execD_beta_nat !execD_bernoulli_trunc/=.
rewrite execD_pow/= (@execD_bin _ _ binop_minus) !execD_real/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
transitivity (beta_nat_bern 6 4 0 3 tt U : \bar R).
  rewrite /beta_nat_bern !letin'E/= /ubeta_nat_pdf/= /onem.
  apply: eq_integral => x _.
  do 2 f_equal.
  rewrite /ubeta_nat_pdf'.
  rewrite expr0.
  by rewrite mul1r.
rewrite bernoulli_truncE; last by lra.
rewrite beta_nat_bern_bern/= /bernoulli/=.
rewrite measure_addE/= /mscale/=.
congr (_ * _ + _ * _)%:E; rewrite /onem.
  rewrite /Baa'bb'Bab /beta_nat_norm/=.
  by rewrite !factS/= fact0; field.
rewrite /Baa'bb'Bab /beta_nat_norm/=.
by rewrite !factS/= fact0; field.
Qed.

Lemma bern_onem (f : _ -> R) U p :
  (\int[beta_nat 6 4]_y bernoulli_trunc (f y) U = p%:E * \d_true U + `1-p%:E * \d_false U)%E ->
  (\int[beta_nat 6 4]_y bernoulli_trunc (1 - f y) U = `1-p%:E * \d_true U + p%:E * \d_false U)%E.
Proof.
under eq_integral => x _.
  rewrite bernoulli_truncE.
  over.
admit.
rewrite /= /beta_nat/mscale/= /beta_nat_norm/= /ubeta_nat/ubeta_nat_pdf.
Admitted.

Definition casino4 : @exp R _ [::] _ :=
  [Normalize
   let "_" := Score {1 / 9}:R in
   Sample {exp_bernoulli_trunc [{10 / 11}:R]}].

Lemma casino34 :
  execD casino3 = execD casino4.
Proof.
apply: eq_execD.
f_equal.
apply: congr_normalize => y V.
apply: congr_letin => x U.
rewrite execP_letin !execP_sample execD_beta_nat !execD_bernoulli_trunc/=.
rewrite (@execD_bin _ _ binop_minus) execD_pow/= (@execD_bin _ _ binop_minus).
rewrite !execD_real/= exp_var'E (execD_var_erefl "p")/=.
transitivity (\int[beta_nat 6 4]_y bernoulli_trunc (1 - (1 - y) ^+ 3) U : \bar R)%E.
  by rewrite /beta_nat_bern !letin'E/= /onem.
rewrite bernoulli_truncE; last by lra.
have -> := (@bern_onem (fun x => (1 - x) ^+ 3) U (1 / 11) _).
  congr (_ * _ + _ * _)%E; congr _%:E; rewrite /onem; lra.
transitivity (beta_nat_bern 6 4 0 3 tt U : \bar R).
  rewrite /beta_nat_bern !letin'E/= /ubeta_nat_pdf/= /onem.
  apply: eq_integral => y0 _.
  do 2 f_equal.
  rewrite /ubeta_nat_pdf'/=.
  rewrite expr0.
  by rewrite mul1r.
rewrite beta_nat_bern_bern/= /bernoulli/=.
rewrite measure_addE/= /mscale/=.
congr (_ * _ + _ * _)%:E; rewrite /onem.
  rewrite /Baa'bb'Bab /beta_nat_norm/=.
  by rewrite !factS/= fact0; field.
rewrite /Baa'bb'Bab /beta_nat_norm/=.
by rewrite !factS/= fact0; field.
Qed.

Lemma norm_score_bern g p1 p2 (p10 : p1 != 0) (p1_ge0 : 0 <= p1)
(p201 : 0 <= p2 <= 1) :
  @execD R g _
    [Normalize let "_" := Score {p1}:R in
     Sample {exp_bernoulli_trunc [{p2}:R]}] =
  execD [Normalize Sample {exp_bernoulli_trunc [{p2}:R]}].
Proof.
apply: eq_execD.
rewrite !execD_normalize_pt/= !execP_letin !execP_score.
rewrite !execP_sample !execD_bernoulli_trunc !execD_real/=.
apply: funext=> x.
apply: eq_probability=> /= y.
rewrite /normalize_pt !normalizeE/=.
rewrite !bernoulli_truncE; last lra; last lra.
rewrite !diracT !mule1 /onem -EFinD addrCA subrr addr0.
rewrite !letin'E.
under eq_integral.
  move=> x0 _ /=.
  rewrite !bernoulli_truncE; last lra.
  rewrite !diracT !mule1 /onem -EFinD addrCA subrr addr0.
  over.
rewrite !ge0_integral_mscale//= ger0_norm//.
rewrite integral_dirac// diracT !mule1.
rewrite !ifF; last first.
  rewrite eqe.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
  rewrite eqe.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite !bernoulli_truncE; last lra.
rewrite integral_dirac//= diracT !diracE.
by rewrite muleC muleA -EFinM mulVf// invr1 /onem !(mul1r, mule1).
Qed.

Definition casino5 : @exp R _ [::] _ :=
  [Normalize Sample {exp_bernoulli_trunc [{10 / 11}:R]}].

Lemma casino45 :
  execD casino4 = execD casino5.
Proof.
rewrite norm_score_bern//.
lra.
Qed.

End casino_example.
