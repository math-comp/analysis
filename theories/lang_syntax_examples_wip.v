Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.
Require Import lang_syntax_util lang_syntax.
From mathcomp Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
(* Local Open Scope ereal_scope. *)

Section casino_example.
Open Scope ring_scope.
Open Scope lang_scope.
Context (R : realType).
Lemma a01 : 0 < 1 - 0 :> R. Proof. by []. Qed.

Definition casino0 : exp _ [::] Bool :=
  [let "p" := Sample {exp_uniform 0 1 a01} in
   let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]} in
   let "_" := if #{"a1"} == {5}:R then return TT else Score {0}:R in
   let "a2" := Sample {exp_binomial_trunc 3 [#{"p"}]} in
   return {1}:R <= #{"a2"}].

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
   let "_" := if #{"a1"} == {5}:R then return TT else Score {0}:R in
   let "a2" := Sample
     {exp_bernoulli_trunc [{1}:R - #{"p"} ^+ {3%nat}]} in
   return #{"a2"}].

(* exec [let x := sample (binomial n e) in  *)
(*       return (x >= 1)] =                 *)
(* exec [let y := sample (bernoulli (1 - e^n)) in   *)
(*       return y]                          *)
Lemma binomial_le1 x y n g e t U :
  (0 <= (projT1 (execD e) t : mtyp Real) <= 1) ->
  execP ([let x := Sample {exp_binomial_trunc n e} in
          return {1}:R <= #x] : @exp R _ g _) t U = 
  execP [let y := Sample {exp_bernoulli_trunc [{1}:R - e ^+ n]} in
         return #y] t U.
Proof.
rewrite !execP_letin !execP_sample execD_binomial_trunc execD_bernoulli_trunc/=.
rewrite !exp_var'E/=.
  exact/ctx_prf_head.
  exact/ctx_prf_head.
move=> H0 H1.
rewrite !execP_return !execD_rel.
  have /= := @execD_var R ((y, Bool) :: g) y.
  rewrite eqxx => /(_ H0) ->.
  have /= := @execD_var R ((x, Real) :: g) x.
  rewrite eqxx => /(_ H1) -> /=.
rewrite (@execD_bin _ _ binop_minus) execD_pow !execD_real/=.
rewrite 2!letin'E/=.
set p := projT1 (execD e) t.
move => /andP[p0 p1].
rewrite (@integral_bernoulli_trunc _ _ (fun x => \d_x U))//; last first.
  apply/andP; split.
    exact: (onemX_ge0 _ p0 p1).
  apply/onem_le1/exprn_ge0/p0.
rewrite (@integral_binomial_probabilty_trunc _ n p _ _ (fun y => \d_(1 <= y)%R U))//; last first.
  (* move=>/= _ y0 my0.
  rewrite setTI. *)
  apply: measurable_fun_dirac.
  have := @subsetT _ U; rewrite setT_bool => UT.
  have [->|->|->|->] /= := subset_set2 UT.
    exact: measurable0.
    rewrite [X in measurable X](_ : _ = `[1, +oo[%classic) //.
      apply/seteqP.
      admit.
    rewrite [X in measurable X](_ : _ = `]-oo, 1[%classic) //.
      apply/seteqP.
      admit.
    admit.
  (* rewrite diracE. *)
rewrite !big_ord_recl/=.
have -> : (1 <= 0 :> R) = false by lra.
rewrite /bump.
under eq_bigr => i _.
  rewrite /= natrD.
  have -> : 1 <= 1 + i%:R :> R.
  by rewrite lerDl.
  over.
rewrite addeC -ge0_sume_distrl.
  congr (_ + _)%E; congr (_ * _)%E.
  have -> : (\sum_(i < n) (p ^+ (n - (1 + i)) * `1-p ^+ (1 + i) *+ 'C(n, 1 + i))%:E)%E =
  (\sum_(i < n.+1) (p ^+ (n - i) * `1-p ^+ i *+ 'C(n, i))%:E - (p ^+ n)%:E)%E.
  rewrite big_ord_recl/= subn0 addeC addeA.
  rewrite bin0 mulr1 mulr1n.
  have <- : 0%E = ((- p ^+ n)%:E + (p ^+ n)%:E)%E.
    rewrite EFinN.
    congr _%:E.
    lra.
  by rewrite add0e.
  congr _%E.
  rewrite sumEFin.
  rewrite !EFinB EFin_expe.
  congr (_ - _)%E.
  rewrite -(@exprDn_comm _ p `1-p n); last first.
    by rewrite /GRing.comm/onem; lra.
  rewrite /onem addrC.
  have -> : 1 - p + p = 1 by lra.
  by rewrite expr1n.
  rewrite subn0 expr0 bin0 mulr1 mulr1n.
  rewrite /onem.
  congr _%:E.
  set pn := p ^+ n.
  lra.
move=> i _.
apply/mulrn_wge0/mulr_ge0; apply/exprn_ge0.
exact: p0.
apply/onem_ge0/p1.
Admitted.

Lemma __ : uniform_probability a01 `[0, (1 / 2)] = (1 / 2)%:E.
Proof.
rewrite /uniform_probability /mscale/= /mrestr.
Abort.

Lemma letin'_sample_uniform d d' (T : measurableType d)
    (T' : measurableType d') (a b : R) (ab0 : (0 < b - a)%R)
    (u : R.-sfker [the measurableType _ of (_ * T)%type] ~> T') x y :
  letin' (sample_cst (uniform_probability ab0)) u x y =
  (((b - a)^-1)%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y)%E.
Proof.
rewrite letin'E/=.
rewrite ge0_integral_mscale//=; last admit.
transitivity (
(((b - a)^-1)%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y)%E
).
  admit.
by [].
Admitted.

Lemma execP_letin_uniform g u a b p (Hap : infer (a != p)) 
(Hbp : infer (b != p)) (s0 s1 : @exp R D ((a, Unit) :: (b, Real) :: (p, Real) :: g) Real -> exp P ((p, Real) :: g) u) :
  (forall (t : R) x U, t \in `[0, 1] -> execP (s0 [#p]) (t, x) U = execP (s1 [#p]) (t, x) U) ->
  execP [let p := Sample {@exp_uniform _ g 0 1 a01} in {s0 [#p]}] = 
  execP [let p := Sample {@exp_uniform _ g 0 1 a01} in {s1 [#p]}].
Proof.
move=> s01.
rewrite !execP_letin execP_sample execD_uniform/=.
apply: eq_sfkernel => x U.
rewrite 2!letin'_sample_uniform.
congr (_ * _)%E.
apply: eq_integral => t t01.
apply: s01.
by rewrite inE in t01.
Qed.

Lemma casino01 : execP casino0 = execP casino1.
Proof.
rewrite /casino0 /casino1.
pose s0 := fun x => [let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]}
      in let "_" := if #{"a1"} == {5}:R then return TT else Score {0}:R
         in let "a2" := Sample {exp_binomial_trunc 3 [x]} in {exp_return [{1}:R <= #{"a2"}]}] : @exp R _ _ _.
pose s1 := fun x => [let "a1" := Sample {exp_binomial_trunc 8 [#{"p"}]}
      in let "_" := if #{"a1"} == {5}:R then return TT else Score {0}:R
         in let "a2"
            := Sample {exp_bernoulli_trunc [{1}:R - x ^+ {3%N}]}
            in {exp_return [#{"a2"}]}] : @exp R _ _ _.
apply: (@execP_letin_uniform [::] _ _ _ _ _ _ (s0 _) (s1 _)).
move=> e k k01 ek.
rewrite /s0/s1.
rewrite 2!execP_letin.
rewrite 2![in RHS]execP_letin.
congr (letin' _ _ _ _).
congr (letin' _ _ _).
(* apply: eq_sfkernel => x U. *)
rewrite !execP_letin !execP_sample execD_bernoulli_trunc execD_binomial_trunc/=.
rewrite (@execD_bin _ _ binop_minus) !execP_return execD_rel execD_pow/=.
rewrite !execD_real !exp_var'E !(execD_var_erefl "a2") (execD_var_erefl "p")/=.

have H := (@binomial_le1 "a2" "a2" 3 _ [#{"p"}]).
(* f_equal. *)
(* congr ((letin' _ _ _) _).
apply: eq_sfkernel => ?.
have : 0 <= e <= 1.
  admit.
move=> H.
rewrite (binomial_le1 _ _ _ _ H).
under eq_integral.
rewrite execP_letin.
congr (letin').

(* apply: eq_sfkernel => x U. *)
have : 0 <= (projT1 (execD e) x : mtyp Real) <= 1.
  by rewrite ek.
move=> H.
apply: (binomial_le1 _ _ _ _ H). *)
Admitted.

(* guard test *)
Definition test_guard : @exp R _ [::] _ := [
  let "p" := Sample {exp_bernoulli (1 / 3)%:nng (p1S 2)} in
  let "_" := if #{"p"} then return TT else Score {0}:R in
  return #{"p"}
].

Lemma exec_guard t U : execP test_guard t U = ((1 / 3)%:E * @dirac _ _ true R U)%E.
Proof.
rewrite /test_guard 2!execP_letin execP_sample execD_bernoulli execP_if/=.
rewrite !execP_return !exp_var'E !(execD_var_erefl "p") execD_unit execP_score execD_real/=.
rewrite letin'E ge0_integral_measure_sum//.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//= !integral_dirac//.
rewrite !letin'E !iteE/= integral_dirac// ge0_integral_mscale//=.
by rewrite normr0 mul0e !mule0 !adde0 !diracT !mul1e.
Qed.

Lemma exec_casino t U :
  execP casino0 t U = ((10 / 99)%:E * @dirac _ _ true R U +
                       (1 / 99)%:E * @dirac _ _ false R U)%E .
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

About integralT_nnsfun.

Lemma exec_uniform_syntax t U : measurable U ->
  execP uniform_syntax t U = uniform_probability a01 U.
Proof.
move=> mU.
rewrite /uniform_syntax execP_letin execP_sample execP_return !execD_uniform.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite letin'E /=.
rewrite {1}/uniform_probability.
set x := (X in mscale _ X).
set k := (X in mscale X _).
transitivity ((k%:num)%:E * \int[x]_y \d_y U)%E.
  rewrite -ge0_integral_mscale //.
  exact: measurable_fun_dirac.
rewrite /uniform_probability /mscale /=.
congr (_ * _)%E.
under eq_integral do rewrite diracE.
rewrite /=.
rewrite /lebesgue_measure/=.
rewrite -integral_cst.
set f := (mrestr lebesgue_measure (measurable_itv `[0%R, 1%R])).
admit.
rewrite -(@ge0_integral_mscale _ _ _ x setT measurableT k (fun y => \d_y U)) //.
rewrite /uniform_probability/mscale/=/integral//=.
Admitted.

Definition binomial_le : @exp R _ [::] Bool :=
  [let "a2" := Sample {exp_binomial 3 (1 / 2)%:nng (p1S 1)} in
   return {1}:R <= #{"a2"}].

Lemma exec_binomial_le t U :
  execP binomial_le t U = ((7 / 8)%:E * @dirac _ _ true R U +
                          (1 / 8)%:E * @dirac _ _ false R U)%E.
Proof.
rewrite /binomial_le execP_letin execP_sample execP_return execD_rel execD_real.
rewrite exp_var'E (execD_var_erefl "a2") execD_binomial.
rewrite letin'E//= /binomial_probability ge0_integral_measure_sum//=.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//=.
rewrite !integral_dirac// /bump.
rewrite !binS/= !bin0 bin1 bin2 bin_small// addn0.
rewrite addeC adde0.
congr (_ + _)%:E.
have -> : (1 <= 1)%R. admit.
have -> : (1 <= 2)%R. admit.
have -> : (1 <= 3)%R. admit.
rewrite -!mulrDl indicT !mul1r.
congr (_ * _).
rewrite /onem addn0 add0n.
by field.
congr (_ * _).
by field.
(* by rewrite ler10. *)
Admitted.

Definition binomial_guard : @exp R _ [::] Real :=
  [let "a1" := Sample {exp_binomial 3 (1 / 2)%:nng (p1S 1)} in
   let "_" := if #{"a1"} == {1}:R then return TT else Score {0}:R in
   return #{"a1"}].

Lemma exec_binomial_guard t U :
  execP binomial_guard t U = ((7 / 8)%:E * @dirac _ R 1%R R U +
                          (1 / 8)%:E * @dirac _ R 0%R R U)%E.
Proof.
rewrite /binomial_guard !execP_letin execP_sample execP_return execP_if.
rewrite !exp_var'E execD_rel !(execD_var_erefl "a1") execP_return execD_unit execD_binomial execD_real execP_score execD_real.
rewrite !letin'E//= /binomial_probability ge0_integral_measure_sum//=.
rewrite !big_ord_recl big_ord0 !ge0_integral_mscale//=.
rewrite !integral_dirac// /bump.
rewrite (* indicT *) !binS/= !bin0 bin1 bin2 bin_small// addn0 (* !mul1e *).
rewrite !letin'E//= !iteE/= !diracE/=.
have -> : (0 == 1)%R = false; first by admit.
have -> : (1 == 1)%R; first by admit.
have -> : (2 == 1)%R = false; first by admit.
have -> : (3 == 1)%R = false; first by admit.
rewrite addeC adde0.
Admitted.

End casino_example.
