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

(* Definition ex : exp _ [::] _ := @exp_bernoulli R [::] (1 / 2)%:nng (p1S 1).
Example ex1 : projT1 (execD ex) tt = 1%:E. *)

Definition casino0 : exp _ [::] Bool :=
  [let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   let "a2" := Sample {exp_binomial_trunc 3 [#{"p"}]} in
   return {1}:N <= #{"a2"}].

Example e1 : @exp R _ [::] _ := [{1}:R + {2}:R * {2}:R ^+ {3%nat}].

Lemma exe1 : projT1 (execD e1) = (fun x => 17).
Proof.
rewrite /e1 (@execD_bin _ _ binop_add) (@execD_bin _ _ binop_mult)/=.
rewrite execD_pow/= !execD_real /=.
apply: funext => x /=.
lra.
Qed.

(* Arguments exp_bin {R g b} &. *)
Definition casino1 : @exp R _ [::] _ :=
  [let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   let "a2" :=
     Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]} in
   return #{"a2"}].

Definition casino1' : @exp R _ [::] _ :=
  [let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Lemma binomial_le1' n p U :
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

Let weak_head fl g {t1 t2} x (e : @exp R fl g t2) (xg : x \notin dom g) :=
  exp_weak fl [::] _ (x, t1) e xg.

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
by rewrite inE in t01.
admit.
admit.
Admitted.

(* Lemma casino01 : execP casino0 = execP casino1.
Proof.
rewrite /casino0 /casino1.
rewrite !execP_letin !execP_sample execD_uniform !execD_binomial_trunc /=.
rewrite execP_if execP_score !execP_return !execD_bernoulli_trunc/=.
rewrite !execD_rel (@execD_bin _ _ binop_minus) !execD_real execD_pow/=.
rewrite !execD_nat execD_unit/=.
rewrite !exp_var'E !(execD_var_erefl "p") !(execD_var_erefl "a1")/=.
rewrite !(execD_var_erefl "a2")/=.
do 3 congr letin'.
apply: eq_sfkernel => x U.
rewrite !letin'E/=.
apply: binomial_le1.

rewrite /=.
Abort. *)

(* Lemma casino01 : execP casino0 = execP casino1.
Proof.
rewrite /casino0 /casino1.
pose s0 := 
  [let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in 
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   let "a2" := Sample {exp_binomial_trunc 3 [#{"p"}]} in
   {exp_return [{1}:N <= #{"a2"}]}].
pose s1 :=
  [let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
   let "a2" := Sample {exp_bernoulli_trunc [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%N}]} in
   {exp_return [#{"a2"}]}].
have := (@execP_letin_uniform [::] Bool "p" (s0 R (found "p" Real [::]) _ _) (s1 R (found "p" Real [::]) _ _)).
apply.
move=> p x U r01.
rewrite /s0/s1/=.
rewrite !execP_letin !execP_sample !execD_binomial_trunc /=.
rewrite execP_if execP_score !execP_return !execD_bernoulli_trunc/=.
rewrite !execD_rel (@execD_bin _ _ binop_minus) execD_pow.
rewrite (@execD_bin _ _ binop_minus) !execD_real/=.
rewrite !execD_nat execD_unit/=.
rewrite !exp_var'E !(execD_var_erefl "p") !(execD_var_erefl "a1")/=.
rewrite !(execD_var_erefl "a2")/=.
rewrite !letin'E/=.
move: r01 => /andP[r0 r1].
rewrite !integral_binomial_probabilty_trunc//=.
apply: eq_bigr => i _.
congr (_ * _)%E.
rewrite !letin'E iteE/=.
congr (\int[_]_y _)%E.
apply: funext => x0.
rewrite !letin'E/=.
by apply/binomial_le1/andP.
Qed. *)

Lemma casino01' y V : measurable V -> execP casino0 y V = execP casino1' y V.
Proof.
move=> mV //.
rewrite /casino0 /casino1.
apply: execP_letin_uniform => //.
move=> p x U r01.
rewrite !execP_letin !execP_sample !execD_binomial_trunc /=.
rewrite execP_if execP_score !execP_return !execD_bernoulli_trunc/=.
rewrite !execD_rel (@execD_bin _ _ binop_minus) execD_pow.
rewrite (@execD_bin _ _ binop_minus) !execD_real/=.
rewrite !execD_nat execD_unit/=.
rewrite !exp_var'E !(execD_var_erefl "p") !(execD_var_erefl "a1")/=.
rewrite !(execD_var_erefl "a2")/=.
rewrite !letin'E/=.
move: r01 => /andP[r0 r1].
rewrite !integral_binomial_probabilty_trunc//=.
apply: eq_bigr => i _.
congr (_ * _)%E.
rewrite !letin'E iteE/=.
congr (\int[_]_y _)%E.
apply: funext => x0.
rewrite !letin'E/=.
by apply/binomial_le1'/andP.
Qed.

Lemma exec_casino t U :
  execP casino0 t U = ((10 / 99)%:E * \d_true U + (1 / 99)%:E * \d_false U)%E .
Proof.
rewrite /casino0 !execP_letin !execP_sample execD_uniform/=.
rewrite !execD_binomial_trunc execP_if !execP_return !execP_score/=.
rewrite !execD_rel !execD_real execD_unit/=.
rewrite !exp_var'E (execD_var_erefl "p") (execD_var_erefl "a1").
rewrite (execD_var_erefl "p") (execD_var_erefl "a2")/=.
rewrite letin'E/= /uniform_probability ge0_integral_mscale//=.
rewrite subr0 invr1 mul1e.
under eq_integral.
Admitted.

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

End casino_example.
