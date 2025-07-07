(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Reals Interval.Tactic.
From mathcomp Require Import (canonicals) Rstruct Rstruct_topology.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype.
From mathcomp Require Import sequences realfun convex real_interval.
From mathcomp Require Import derive esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.
From mathcomp Require Import hoelder unstable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**md**************************************************************************)
(* # A Sampling Theorem                                                       *)
(*                                                                            *)
(* This file contains a formalization of a sampling theorem. The proof is     *)
(* decompose in two sections: sampling_theorem_part1 and                      *)
(* sampling_theorem_part2.                                                    *)
(*                                                                            *)
(* References:                                                                *)
(* - Michael Mitzenmacher and Eli Upfal. Probability and Computing—Randomized *)
(*   Algorithms and Probabilistic Analysis. Cambridge University Press, 2005  *)
(* - Samir Rajani. Applications of Chernoff bounds, 2019                      *)
(*   http://math.uchicago.edu/~may/REU2019/REUPapers/Rajani.pdf               *)
(*                                                                            *)
(* ## Construction of the product probability measure                         *)
(* Tnth X i x == the i-th component of X applied to the i-th component of x   *)
(*     \X_n P == the product probability measure P \x P \x ... \x P           *)
(*                                                                            *)
(* ## Lemmas for Expectation of Sum and Product on the Product Measure        *)
(* - expectation_sum_ipro: The expectation of the sum of random variables on  *)
(*   the product measure is the sum of their expectations.                    *)
(* - expectation_product: The expectation of the product of random variables  *)
(*   on the product measure is the product of their expectations.             *)
(*   Independence of the variables follows by construction on the product     *)
(*   measure.                                                                 *)
(*                                                                            *)
(* ## Key steps in the Sampling theorem                                       *)
(* - mmt_gen_fun_expectation: Expectation of the moment generating function   *)
(*   of a Bernoulli trial.                                                    *)
(* - bernoulli_trial_mmt_gen_fun: the moment generating function of a         *)
(*   Bernoulli trial is the product of each moment generating function.       *)
(* - exp2_le8: inequality solved by interval.                                 *)
(* - xlnx_lbound_i01: lower bound for x * ln x in the interval `]0, 1[.       *)
(* - xlnx_ubound_i1y: upper bound for x * ln x for x greater than 1.          *)
(* - sampling_ineq1: Concentration inequality on a Bernoulli trial X,         *)
(*   bounding the probability of X >= (1+delta) * 'E_(\X_n P)[X]              *)
(* - sampling_ineq2: Specialization of sampling_ineq1 using xlnx_lbound_i12   *)
(* - sampling_ineq3: Concentration inequality on a Bernoulli trial X,         *)
(*   bounding the probability of X <= (1-delta) * 'E_(\X_n P)[X]              *)
(* - sampling_ineq4: Combines the previous two inequalities to obtain a bound *)
(*   on the probability of `|X - 'E_(\X_n P)[X]| >= delta * 'E_(\X_n P)[X]    *)
(* - sampling: The main sampling theorem combining the above inequalities.    *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import hoelder ess_sup_inf.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "\X_ n P" (at level 10, n, P at next level,
  format "\X_ n  P").

(* NB: also in Jairo's PR about lne *)
Lemma norm_expR {R : realType} : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

Lemma preimage_set1 T {U : eqType} (X : T -> U) r :
  X @^-1` [set r] = [set i | X i == r].
Proof. by apply/seteqP; split => [x /eqP H//|x /eqP]. Qed.

(* PR in progress *)
Lemma integrable_prod_measP {d1} {T1 : measurableType d1} d2 {T2 : measurableType d2}
  {R : realType} (m1 : {sigma_finite_measure set T1 -> \bar R})
  (m2 : {sigma_finite_measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) :
  (m1 \x m2)%E.-integrable [set: T1 * T2] f <->
  (m1 \x^ m2)%E.-integrable [set: T1 * T2] f.
Proof.
split => /integrableP[mf intf]; apply/integrableP; split => //.
- rewrite (eq_measure_integral (m1 \x m2)%E)//= => C mC _.
  by apply/esym/product_measure_unique => //= *; rewrite product_measure2E.
- rewrite (eq_measure_integral (m1 \x^ m2)%E)//= => C mC _.
  by apply: product_measure_unique => //= *; rewrite product_measure2E.
Qed.

(* PR in progress *)
Lemma integral_prod_meas1E {d1} {T1 : measurableType d1}
    {d2} {T2 : measurableType d2} {R : realType}
    (m1 : {sigma_finite_measure set T1 -> \bar R})
    (m2 : {sigma_finite_measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) :
  (m1 \x m2)%E.-integrable [set: T1 * T2] f ->
  (\int[m1 \x^ m2]_x f x = \int[(m1 \x m2)%E]_z f z)%E.
Proof. by move=> intf; rewrite -integral12_prod_meas1// integral12_prod_meas2. Qed.

Section PR_to_hoelder.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma Lfun_bounded (f : T -> R) p : 1 <= p ->
  measurable_fun [set: T] f -> bounded_fun f -> f \in Lfun mu p.
Proof.
move=> p1 mX bX.
apply: (Lfun_subset p1 (leey _)).
- by rewrite fin_num_measure.
- by rewrite leey.
rewrite inE/=; apply/andP; split; rewrite inE//=.
rewrite /finite_norm unlock.
case: ifPn => P0//.
case: bX => M [Mreal bX].
apply: (@le_lt_trans _ _ (M + 1)%:E).
  by rewrite ess_sup_ler// => t; apply: bX => //; rewrite ltrDl.
by rewrite ltry.
Qed.

End PR_to_hoelder.

Section bool_to_real.
Context d (T : measurableType d) (R : realType) (P : probability T R)
  (f : {mfun T >-> bool}).
Definition bool_to_real : T -> R := (fun x => x%:R) \o (f : T -> bool).

Lemma measurable_bool_to_real : measurable_fun [set: T] bool_to_real.
Proof.
by apply: measurableT_comp => //=; exact: (@measurable_funPT _ _ _ _ f).
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ bool_to_real measurable_bool_to_real.

End bool_to_real.

Lemma bounded_integrable d (T : measurableType d) (R : realType)
    (P : {finite_measure set T -> \bar R}) (X : T -> R) :
  measurable_fun setT X ->
  bounded_fun X -> P.-integrable [set: T] (EFin \o X).
Proof.
move=> mf [M [Mreal HM]].
apply: (@le_integrable _ T R _ _ measurableT _ (EFin \o cst (M + 1))).
- exact/measurable_EFinP.
- move=> t _ /=; rewrite lee_fin/=.
  apply: HM => //=.
  by rewrite (lt_le_trans _ (ler_norm _))// ltrDl.
- exact: finite_measure_integrable_cst.
Qed.

Section Tnth.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition Tnth n (X : n.-tuple {mfun T >-> R}) i : n.-tuple T -> R :=
  fun t => (tnth X i) (tnth t i).

Lemma measurable_Tnth n (X : n.-tuple {mfun T >-> R}) i :
  measurable_fun [set: n.-tuple T] (Tnth X i).
Proof. by apply: measurableT_comp => //; exact: measurable_tnth. Qed.

HB.instance Definition _ n (X : n.-tuple {mfun T >-> R}) (i : 'I_n) :=
  isMeasurableFun.Build _ _ _ _ (Tnth X i) (measurable_Tnth X i).

Lemma measurable_sum_Tnth n (X : n.-tuple {mfun T >-> R}) :
  measurable_fun [set: n.-tuple T] (\sum_(i < n) Tnth X i).
Proof.
rewrite [X in measurable_fun _ X](_ : _
    = (fun x => \sum_(i < n) Tnth X i x)); last first.
  by apply/funext => x; rewrite fct_sumE.
apply: measurable_sum => i/=; apply/measurableT_comp => //.
exact: measurable_tnth.
Qed.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (\sum_(i < n) Tnth s i) (measurable_sum_Tnth s).

Lemma measurable_prod_Tnth m n (s : m.-tuple {mfun T >-> R}) (f : 'I_n -> 'I_m) :
  measurable_fun [set: m.-tuple T] (\prod_(i < n) Tnth s (f i))%R.
Proof.
rewrite [X in measurable_fun _ X](_ : _
    = (fun x => \prod_(i < n) Tnth s (f i) x)); last first.
  by apply/funext => x; rewrite fct_prodE.
by apply: measurable_prod => /= i _; apply/measurableT_comp.
Qed.

HB.instance Definition _ m n (s : m.-tuple {mfun T >-> R}) (f : 'I_n -> 'I_m) :=
  isMeasurableFun.Build _ _ _ _ (\prod_(i < n) Tnth s (f i))
    (measurable_prod_Tnth s f).

End Tnth.

Section tuple_of_pair.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Definition pair_of_tuple n (w : n.+1.-tuple T) :=
  (thead w, [the _.-tuple _ of behead w]).

Lemma measurable_pair_of_tuple n (D : set (n.+1.-tuple T)) :
  measurable_fun D (@pair_of_tuple n).
Proof.
by apply/measurable_funTS/measurable_fun_pair => /=;
  [exact: measurable_tnth|exact: measurable_behead].
Qed.

Lemma trivIset_pair_of_tuple n (F : nat -> set (n.+1.-tuple T)) :
  trivIset [set: nat] F ->
  trivIset [set: nat] (fun m => @pair_of_tuple n @` F m).
Proof.
move=> tF; apply/trivIsetP => i j _ _ ij.
move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
rewrite -!subset0 => ij0 /= [_ _] [[t Fit] [<- <-]]/=.
move=> [u Fju [hut tut]].
have := ij0 t; apply; split => //.
suff: t = u by move=> ->.
rewrite (tuple_eta t) (tuple_eta u) hut.
by apply/val_inj => /=; rewrite tut.
Qed.

Lemma range_pair_of_tuple n :
  range (pair_of_tuple (n:=n)) = [set: T * n.-tuple T].
Proof.
rewrite -subTset => -[x y] _; exists (x :: y) => //=.
by rewrite /pair_of_tuple/= theadE//; congr pair; exact/val_inj.
Qed.

Definition tuple_of_pair n (w : T * n.-tuple T) :=
  [the _.-tuple _ of w.1 :: w.2].

Lemma measurable_tuple_of_pair n :
  measurable_fun [set: T * n.-tuple T] (@tuple_of_pair n).
Proof. exact: measurable_cons. Qed.

Lemma pair_of_tupleK n : cancel (@tuple_of_pair n) (@pair_of_tuple n).
Proof.
move=> [x1 x2]; rewrite /pair_of_tuple /tuple_of_pair/=; congr pair => /=.
exact/val_inj.
Qed.

Lemma tuple_of_pairK n : cancel (@pair_of_tuple n) (@tuple_of_pair n).
Proof. by move=> x; rewrite /pair_of_tuple /tuple_of_pair/= [RHS]tuple_eta. Qed.

Lemma image_pair_of_tuple n (A : set (n.+1.-tuple T)) :
  @pair_of_tuple n @` A = @tuple_of_pair n @^-1` A.
Proof.
 apply/seteqP; split => [x/= [t At <-/=]|x/= Ax].
   by move: At; rewrite {1}(tuple_eta t).
exists (x.1 :: x.2) => //=.
by rewrite [RHS]surjective_pairing; congr pair; exact/val_inj.
Qed.

Lemma measurable_image_pair_of_tuple n (A : set (n.+1.-tuple T)) :
  measurable A -> measurable (@pair_of_tuple n @` A).
Proof.
move=> mA; rewrite image_pair_of_tuple.
by rewrite -[X in measurable X]setTI; exact: measurable_cons.
Qed.

End tuple_of_pair.
Arguments pair_of_tuple {d T} n.
Arguments tuple_of_pair {d T} n.
Arguments measurable_tuple_of_pair {d T} n.
Arguments measurable_pair_of_tuple {d T} n.

Section iterated_product_sigma_finite_measures.
Context d (T : measurableType d) (R : realType)
  (P : {sigma_finite_measure set T -> \bar R}).

Fixpoint ipro n : set (n.-tuple T) -> \bar R :=
  match n with
  | 0%N => \d_([::] : 0.-tuple T)
  | m.+1 => fun A => (P \x^ @ipro m)%E (pair_of_tuple m @` A)
  end.

Let ipro_measure n : @ipro n set0 = 0 /\ (forall A, 0 <= @ipro n A)%E
  /\ semi_sigma_additive (@ipro n).
Proof.
elim: n => //= [|n ih].
  by repeat split => //; exact: measure_semi_sigma_additive.
pose build_Mpro := isMeasure.Build _ _ _ (@ipro n) ih.1 ih.2.1 ih.2.2.
pose Mpro : measure _ R := HB.pack (@ipro n) build_Mpro.
pose ppro : measure _ R := (P \x^ Mpro)%E.
split.
  rewrite image_set0 /product_measure2 /=.
  under eq_fun => x do rewrite ysection0 measure0 (_ : 0 = cst 0 x)//.
  by rewrite (_ : @ipro n = Mpro)// integral_cst// mul0e.
split.
  by move => A; rewrite (_ : @ipro n = Mpro).
rewrite (_ : @ipro n = Mpro)// (_ : (P \x^ Mpro)%E = ppro)//.
move=> F mF dF mUF.
rewrite image_bigcup; apply: measure_semi_sigma_additive.
- by move=> i ; apply: measurable_image_pair_of_tuple.
- exact: trivIset_pair_of_tuple.
- by apply: bigcup_measurable => j _; apply: measurable_image_pair_of_tuple.
Qed.

HB.instance Definition _ n := isMeasure.Build _ _ _ (@ipro n)
  (ipro_measure n).1 (ipro_measure n).2.1 (ipro_measure n).2.2.

End iterated_product_sigma_finite_measures.
Arguments ipro {d T R} P n.

Notation "\X_ n P" := (ipro P n).

Section iterated_product_probability_measures.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Let ipro_setT n : \X_n P [set: n.-tuple T] = 1%E.
Proof.
elim: n => [|n ih]/=; first by rewrite diracT.
rewrite /product_measure2 /ysection/=.
under eq_fun => x.
  rewrite [X in P X](_ : _ = [set: T]); last first.
    under eq_fun => y.
      rewrite [X in _ \in X](_ : _ = setT); last first.
        apply: funext => z/=; apply: propT.
        exists (z.1 :: z.2) => //=.
        case: z => z1 z2/=; congr pair.
        exact/val_inj.
      over.
    by apply: funext => y /=; rewrite in_setT trueE.
  rewrite probability_setT.
  over.
by rewrite integral_cst// mul1e.
Qed.

HB.instance Definition _ n :=
  Measure_isProbability.Build _ _ _ (\X_n P) (@ipro_setT n).

End iterated_product_probability_measures.

Section integral_ipro.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma ge0_integral_iproS (P : {finite_measure set T -> \bar R})
    n (f : n.+1.-tuple T -> R) :
    measurable_fun [set: n.+1.-tuple T] f ->
    (forall x, 0 <= f x)%R ->
  \int[\X_n.+1 P]_w (f w)%:E = \int[P \x^ \X_n P]_w (f (w.1 :: w.2))%:E.
Proof.
move=> mf f0.
rewrite -(@ge0_integral_pushforward _ _ _ _ R _ (@measurable_tuple_of_pair _ _ n) _
    setT (fun x : n.+1.-tuple T => (f x)%:E)).
- apply: eq_measure_integral; first exact: measurable_tuple_of_pair.
  by move=> ? A mA _ //=; rewrite image_pair_of_tuple.
- exact: measurableT.
- exact: measurableT_comp.
- by move=> x/= _; rewrite lee_fin.
Qed.

Lemma ipro_tnth n A i (P : probability T R) : d.-measurable A ->
  (\X_n P) ((@tnth n T)^~ i @^-1` A) = P A.
Proof.
elim: n A i => [A [] []//|n ih A [] [i0|m mn mA]].
- transitivity ((P \x^ \X_n P) (A `*` [set: n.-tuple T])).
    by rewrite /= image_pair_of_tuple setXT.
  rewrite /product_measure2/= setXT.
  under [X in integral _ _ X]eq_fun => x do rewrite ysection_preimage_fst.
  by rewrite integral_cst//= probability_setT mule1.
- have mn' : (m < n)%N by rewrite -ltnS.
  transitivity ((P \x^ \X_n P)
      (setT `*` ((@tnth _ T) ^~ (Ordinal mn') @^-1` A))).
    rewrite /= image_pair_of_tuple//= setTX/=; congr (_ _).
    rewrite (_ : Ordinal mn = lift ord0 (Ordinal mn'))//=; last first.
       exact: val_inj.
    by apply: funext => -[x1 x2]//=; rewrite tnthS.
  rewrite product_measure2E//=; first by rewrite probability_setT mul1e ih.
  by rewrite -[X in measurable X]setTI; exact: measurable_tnth.
Qed.

Lemma integral_iproS (P : probability T R)
    n (f : n.+1.-tuple T -> R) :
    (\X_n.+1 P).-integrable [set: n.+1.-tuple T] (EFin \o f) ->
  \int[\X_n.+1 P]_w (f w)%:E = \int[P \x^ \X_n P]_w (f (w.1 :: w.2))%:E.
Proof.
move=> /integrableP[mf intf].
rewrite -(@integral_pushforward _ _ _ _ R _ (measurable_tuple_of_pair n) _
    setT (fun x : n.+1.-tuple T => (f x)%:E)).
- apply: eq_measure_integral => /=; first exact: measurable_tuple_of_pair.
  by move=> _ A mA _ /=; rewrite image_pair_of_tuple.
- exact: mf.
- rewrite /=.
  apply/integrable_prod_measP => /=.
  apply/integrableP; split => /=.
    by apply: measurableT_comp => //=; exact: measurable_tuple_of_pair.
  apply: le_lt_trans (intf).
  rewrite [leRHS](_ : _ = \int[\X_n.+1 P]_x
      (((abse \o (@EFin R \o (f \o tuple_of_pair n))))
       \o (pair_of_tuple n)) x); last first.
    by apply: eq_integral => x _ /=; rewrite tuple_of_pairK.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite -[RHS](@integral_pushforward _ _ _ _ R _ (measurable_pair_of_tuple n setT)
     _ setT (fun x => (abse \o (EFin \o (f \o (tuple_of_pair n)))) x))//.
  + apply: eq_measure_integral => /=; first exact: measurable_pair_of_tuple.
    move=> _ A mA _/=; rewrite /pushforward /=.
    rewrite image_pair_of_tuple -comp_preimage (_ : _ \o _ = id); last first.
      by apply/funext=> x/=; rewrite pair_of_tupleK.
    rewrite preimage_id; apply: product_measure_unique => // B C mB mC.
    by rewrite /= /pushforward/= -product_measure2E.
  + apply/measurable_EFinP => //=; apply: measurableT_comp => //=.
    by apply: measurableT_comp => //=; [exact/measurable_EFinP|
                                        exact: measurable_tuple_of_pair].
  + have : (\X_n.+1 P).-integrable [set: n.+1.-tuple T] (EFin \o f).
      exact/integrableP.
    apply: le_integrable => //=.
    * apply: measurableT_comp => //=; last exact: measurable_pair_of_tuple.
      apply/measurable_EFinP => //=; apply: measurableT_comp => //=.
      by apply: measurableT_comp => //=; [exact/measurable_EFinP|
                                          exact: measurable_tuple_of_pair].
    * by move=> x _; rewrite normr_id// tuple_of_pairK.
- exact: measurableT.
Qed.

Lemma integral_ipro_tnth (P : probability T R) n (f : {mfun T >-> R}) i :
  \int[\X_n P]_x `|f (tnth x i)|%:E = \int[P]_x (`|f x|)%:E.
Proof.
rewrite -(preimage_setT ((@tnth n _)^~ i)).
rewrite -(@ge0_integral_pushforward _ _ _ _ _ _ (measurable_tnth i) (\X_n P) _
    (EFin \o normr \o f) measurableT).
- apply: eq_measure_integral => /=; first exact: measurable_tnth.
  by move=> _ A mA _/=; rewrite /pushforward ipro_tnth.
- by do 2 apply: measurableT_comp.
- by move=> y _/=; rewrite lee_fin normr_ge0.
Qed.

Lemma tnth_Lfun (P : probability T R) n (F : n.-tuple {mfun T >-> R}) i :
  (tnth F i :> T -> R) \in Lfun P 1 -> Tnth F i \in Lfun (\X_n P) 1.
Proof.
rewrite !inE /Tnth => /andP[].
rewrite !inE /finite_norm/= unlock /Lnorm invr1 poweRe1; last first.
rewrite ?integral_ge0// => x _; rewrite poweRe1//.
under eq_integral => x _ do rewrite poweRe1//=.
move=> mF iF; apply/andP; rewrite !inE/=; split.
  apply: measurableT_comp => //.
  exact: measurable_tnth.
rewrite /finite_norm unlock /Lnorm/= invr1 poweRe1 ?integral_ge0//.
under eq_integral => x _ do rewrite powRr1//.
by rewrite (integral_ipro_tnth _ (tnth F i)).
Qed.

End integral_ipro.

Section integral_ipro_Tnth.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma integral_ipro_Tnth n (F : n.-tuple {mfun T >-> R}) (i : 'I_n) :
    (forall Fi : {mfun T >-> R}, Fi \in F -> (Fi : T -> R) \in Lfun P 1) ->
  \int[\X_n P]_x (Tnth F i x)%:E = \int[P]_x (tnth F i x)%:E.
Proof.
elim: n F i => [F []//|m ih F i lfunFi/=].
rewrite -/(\X_m.+1 P).
move: i => [] [i0|i im].
  rewrite [LHS](@integral_iproS _ _ _ _ m); last first.
    exact/Lfun1_integrable/tnth_Lfun/lfunFi/mem_tnth.
  under eq_fun => x do
    rewrite /Tnth (_ : tnth (_ :: _) _ = tnth [tuple of x.1 :: x.2] ord0)// tnth0.
  rewrite -integral12_prod_meas2 /fubini_F/=; last first.
    apply/integrable12ltyP => /=.
      by apply: measurableT_comp => //=; exact: measurableT_comp.
    under eq_integral => x _ do rewrite integral_cst//= probability_setT mule1.
    have /lfunFi : tnth F (Ordinal i0) \in F by apply/tnthP; exists (Ordinal i0).
    by case/Lfun1_integrable/integrableP.
  by apply: eq_integral => x _; rewrite integral_cst//= probability_setT mule1.
rewrite [LHS](@integral_iproS _ _ _ _ m); last first.
  exact/Lfun1_integrable/tnth_Lfun/lfunFi/mem_tnth.
have jm : (i < m)%N by rewrite ltnS in im.
pose j := Ordinal jm.
have liftj : Ordinal im = lift ord0 j by exact: val_inj.
rewrite (tuple_eta F).
under eq_integral => x _ do rewrite /Tnth !liftj !tnthS.
rewrite -integral21_prod_meas2 /fubini_G/=; last first.
  apply/integrable12ltyP => /=.
    do 2 apply: measurableT_comp => //=.
    apply: (@measurableT_comp _ _ _ _ _ _ (fun x => tnth x j) _ snd) => //.
    exact: measurable_tnth.
  rewrite [ltLHS](_ : _ =
      \int[\X_m P]_y `|tnth (behead F) j (tnth y j)|%:E); last first.
    by rewrite integral_cst//= probability_setT mule1.
  have : (tnth F (lift ord0 j) : T -> R) \in Lfun P 1.
    by rewrite lfunFi// mem_tnth.
  rewrite {1}(tuple_eta F) tnthS.
  by move/tnth_Lfun/Lfun1_integrable/integrableP => [_]/=.
transitivity (\int[\X_m P]_x (tnth (behead F) j (tnth x j))%:E).
  apply: eq_integral => /=x _.
  by rewrite integral_cst//= probability_setT mule1.
rewrite [LHS]ih; last by move=> Fi FiF; apply: lfunFi; rewrite mem_behead.
by apply: eq_integral => x _; rewrite liftj tnthS.
Qed.

End integral_ipro_Tnth.

Section properties_of_expectation.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma expectation_ipro_sum n (X : n.-tuple {RV P >-> R}) :
    [set` X] `<=` Lfun P 1 ->
  'E_(\X_n P)[\sum_(i < n) Tnth X i] = \sum_(i < n) 'E_P[(tnth X i)].
Proof.
move=>/= bX.
rewrite (_ : \sum_(i < n) Tnth X i = \sum_(Xi <- [seq Tnth X i | i in 'I_n]) Xi)%R; last first.
  by rewrite big_map big_enum.
rewrite expectation_sum/=.
  rewrite big_map big_enum/=.
  apply: eq_bigr => i i_n.
  by rewrite unlock; exact: integral_ipro_Tnth.
move=> Xi /tnthP[i] ->.
pose j := cast_ord (card_ord _) i.
rewrite /image_tuple tnth_map.
rewrite (_ : tnth (enum_tuple 'I_n) i = j).
  by apply/tnth_Lfun/bX/tnthP; exists j.
apply: val_inj => //=.
rewrite /tnth nth_enum_ord//.
have := ltn_ord i.
move/leq_trans; apply.
by rewrite card_ord leqnn.
Qed.

Lemma expectation_prod_meas2 d1 (T1 : measurableType d1)
  d2 (T2 : measurableType d2) (P1 : probability T1 R) (P2 : probability T2 R)
  (X : T1 -> R) (Y : T2 -> R) :
  (X : _ -> _) \in Lfun P1 1  ->
  (Y : _ -> _) \in Lfun P2 1 ->
  let XY := fun (x : T1 * T2) => (X x.1 * Y x.2)%R in
  'E_(P1 \x^ P2)[XY] = 'E_P1[X] * 'E_P2[Y].
Proof.
move=> /[dup]lX /sub_Lfun_mfun +/[dup]lY /sub_Lfun_mfun.
rewrite !inE/= => mX mY.
rewrite unlock /expectation/=.
rewrite -integral12_prod_meas2/=; last first.
  apply/integrable21ltyP.
  - apply/measurable_EFinP => //=.
    by apply: measurable_funM => //=; apply/measurableT_comp.
  - under eq_integral.
      move=> t _.
      under eq_integral.
        move=> x _.
        rewrite /= normrM EFinM muleC.
        over.
      rewrite integralZl//; last first.
        exact/Lfun1_integrable/Lfun_norm.
      over.
    rewrite /=.
    rewrite ge0_integralZr//; last 2 first.
      apply/measurable_EFinP => //.
      by apply/measurableT_comp => //.
      by apply: integral_ge0 => //.
    rewrite lte_mul_pinfty//.
    - exact: integral_ge0.
    - exact/integrable_fin_num/Lfun1_integrable/Lfun_norm.
    - by move: lX => /Lfun1_integrable/integrableP[_ /=].
rewrite /fubini_F/=.
under eq_integral => x _.
  under eq_integral => y _ do rewrite EFinM.
  rewrite integralZl//; last exact/Lfun1_integrable.
  rewrite -[X in _ * X]fineK ?integrable_fin_num//; last exact/Lfun1_integrable.
  over.
rewrite /=integralZr//; last exact/Lfun1_integrable.
by rewrite fineK// integrable_fin_num; last exact/Lfun1_integrable.
Qed.

End properties_of_expectation.

Section properties_of_independence.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma expectation_ipro_prod n (X : n.-tuple {RV P >-> R}) :
    [set` X] `<=` Lfun P 1 ->
  'E_(\X_n P)[ \prod_(i < n) Tnth X i] = \prod_(i < n) 'E_P[ (tnth X i) ].
Proof.
elim: n X => [X|n IH X] lfunX/=.
  by rewrite !big_ord0 expectation_cst.
rewrite unlock /expectation.
rewrite [X in integral X](_ : _ = \X_n.+1 P)//.
pose F : n.+1.-tuple T -> R := (\prod_(i < n.+1) Tnth X i)%R.
have mF : measurable_fun setT F by apply: measurable_prod_Tnth.
pose build_mF := isMeasurableFun.Build _ _ _ _ F mF.
pose MF : {mfun _ >-> _} := HB.pack F build_mF.
have h1 : (thead X : _ -> _) \in Lfun P 1 by exact/lfunX/mem_tnth.
have h2 : (\prod_(i < n) Tnth (behead_tuple X) i)%R \in Lfun (\X_n P) 1.
  apply/Lfun1_integrable/integrableP => /=; split.
    apply: measurableT_comp => //.
    exact: measurable_prod_Tnth.
  under eq_integral => x _ do rewrite -abse_EFin.
  apply/abse_integralP => //=.
    by apply: measurableT_comp => //; exact: measurable_prod_Tnth.
  have := IH (behead_tuple X).
  rewrite unlock /= => ->; last by move => x /mem_behead/lfunX.
  rewrite abse_prod -ge0_fin_numE ?prode_ge0// prode_fin_num// => i _.
  rewrite abse_fin_num integrable_fin_num//.
  exact/Lfun1_integrable/lfunX/mem_behead/mem_tnth.
rewrite [LHS](@integral_iproS _ _ _ _ _ MF); last first.
  rewrite /MF/F; apply/integrableP; split; first exact: measurableT_comp.
  rewrite ge0_integral_iproS/=; [|exact: measurableT_comp|by []].
  rewrite [ltLHS](_ : _ = \int[P \x^ (\X_n P)]_x (`|thead X x.1|
      * `|(\prod_(i < n) Tnth (behead_tuple X) i) x.2|)%:E); last first.
    apply: eq_integral => x _.
    rewrite big_ord_recl normrM /Tnth (tuple_eta X) !fct_prodE/= !tnth0/=.
    congr ((_ * `| _ |)%:E).
    by apply: eq_bigr => i _/=; rewrite !tnthS -tuple_eta.
  pose tuple_prod := (\prod_(i < n) Tnth (behead_tuple X) i)%R.
  pose meas_tuple_prod := measurable_prod_Tnth (behead_tuple X) id.
  pose build_MTP := isMeasurableFun.Build _ _ _ _ tuple_prod meas_tuple_prod.
  pose MTP : {mfun _ >-> _} := HB.pack tuple_prod build_MTP.
  pose normMTP : {mfun _ >-> _} := normr \o MTP.
  rewrite [ltLHS](_ : _ = \int[P]_w `|thead X w|%:E
    * \int[\X_n P]_w `|tuple_prod w|%:E); last first.
    have := @expectation_prod_meas2 _ _ _ _ _ P (\X_n P) (normr \o thead X)
      (normMTP).
    rewrite unlock /= /tuple_prod => <- //.
    - exact/Lfun_norm.
    - exact/Lfun_norm.
    rewrite lte_mul_pinfty ?ge0_fin_numE ?integral_ge0//.
    by move: h1 => /Lfun1_integrable/integrableP[_].
  by move: h2 => /Lfun1_integrable/integrableP[_].
under eq_fun.
  move=> /=x.
  rewrite /F/MF big_ord_recl/= /Tnth/= fctE tnth0.
  rewrite fct_prodE.
  under eq_bigr.
    move=> i _.
    rewrite tnthS.
    over.
  over.
have /Lfun1_integrable/integrableP/=[mXi iXi] := lfunX _ (mem_tnth ord0 X).
have ? : \int[\X_n P]_x0 (\prod_(i < n) tnth X (lift ord0 i) (tnth x0 i))%:E < +oo.
  under eq_integral => x _.
    rewrite [X in X%:E](_ : _ =
        \prod_(i < n) tnth (behead_tuple X) i (tnth x i))%R; last first.
      by apply: eq_bigr => i _; rewrite (tuple_eta X) tnthS -tuple_eta.
    over.
  rewrite /= -(_ : 'E_(\X_n P)[\prod_(i < n) Tnth (behead_tuple X) i]%R
      = \int[\X_n P]_x _); last first.
    rewrite unlock.
    apply: eq_integral => /=x _.
    by rewrite /Tnth fct_prodE.
  rewrite IH.
    rewrite ltey_eq prode_fin_num// => i _.
    rewrite expectation_fin_num//.
    exact/lfunX/mem_behead/mem_tnth.
  by move=> Xi XiX; rewrite lfunX//= mem_behead.
have ? : measurable_fun [set: n.-tuple T]
    (fun x : n.-tuple T => \prod_(i < n) tnth X (lift ord0 i) (tnth x i))%R.
  apply: measurable_prod => //= i i_n.
  apply: measurableT_comp => //.
  exact: measurable_tnth.
rewrite /=.
have ? : \int[\X_n P]_x `|\prod_(i < n) tnth X (lift ord0 i) (tnth x i)|%:E < +oo.
  move: h2 => /Lfun1_integrable/integrableP[?].
  apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply: eq_integral => x _/=.
  rewrite fct_prodE/=.
  congr (`| _ |%:E).
  apply: eq_bigr => i _.
  by rewrite {1}(tuple_eta X) tnthS.
rewrite -integral12_prod_meas2 /fubini_F/=; last first.
  apply/integrable21ltyP => //=.
    apply: measurableT_comp => //=; apply: measurable_funM => //=.
      exact: measurableT_comp.
    apply: measurable_prod => //= i i_n.
    apply: measurableT_comp => //.
    exact: (measurableT_comp (measurable_tnth i) measurable_snd).
  under eq_integral => y _.
    under eq_integral => x _ do rewrite normrM EFinM.
    rewrite integralZr//; last exact/Lfun1_integrable/Lfun_norm/lfunX/mem_tnth.
    rewrite -[X in X * _]fineK ?ge0_fin_numE ?integral_ge0//.
    over.
  rewrite integralZl ?fineK ?lte_mul_pinfty ?integral_ge0//=.
  - by rewrite ge0_fin_numE ?integral_ge0.
  - by rewrite ge0_fin_numE ?integral_ge0.
  - apply/integrableP; split; first by do 2 apply: measurableT_comp => //.
    by under eq_integral => x _ do rewrite /=normr_id.
under eq_integral => x _.
  under eq_integral => y _ do rewrite EFinM.
  rewrite integralZl/=; last 2 first.
  - apply: measurableT.
  - by apply/integrableP; split => //; first by apply: measurableT_comp => //.
  rewrite -[X in _ * X]fineK; last first.
  rewrite fin_num_abs. apply/abse_integralP => //.
    exact/measurable_EFinP.
  over.
rewrite /= integralZr//; last exact/Lfun1_integrable/lfunX/mem_tnth.
rewrite fineK; last first.
  rewrite fin_num_abs. apply/abse_integralP => //.
  exact/measurable_EFinP.
rewrite [X in _ * X](_ : _ =
    'E_(\X_n P)[\prod_(i < n) Tnth (behead X) i])%R; last first.
  rewrite [in RHS]unlock /Tnth.
  apply: eq_integral => x _.
  rewrite fct_prodE; congr (_%:E).
  apply: eq_bigr => i _.
  rewrite tnth_behead.
  congr (tnth X _ _).
  by apply: val_inj => /=; rewrite /bump/= inordK// ltnS.
rewrite IH; last by move => x /mem_behead/lfunX.
rewrite big_ord_recl/=; congr (_ * _).
apply: eq_bigr => /= i _.
rewrite unlock /expectation.
by apply: eq_integral => x _; rewrite [in RHS](tuple_eta X) tnthS.
Qed.

End properties_of_independence.

HB.mixin Record RV_isBernoulli d (T : measurableType d) (R : realType)
  (P : probability T R) (p : R) (X : T -> bool) of @isMeasurableFun d _ T bool X  := {
    bernoulliP : distribution P X = bernoulli_prob p }.

#[short(type=bernoulliRV)]
HB.structure Definition BernoulliRV d (T : measurableType d) (R : realType)
    (P : probability T R) (p : R) :=
  {X of @RV_isBernoulli _ _ _ P p X & MeasurableFun d X}.
Arguments bernoulliRV {d T R}.

Section properties_of_BernoulliRV.
Local Open Scope ereal_scope.
Context d (T : measurableType d) {R : realType} (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Lemma bounded_fun_bool_to_real (X : bernoulliRV P p) :
  bounded_fun (bool_to_real R X).
Proof.
rewrite /bool_to_real/=; exists 1%R; split => // r r1/= s _.
by rewrite (le_trans _ (ltW r1))// ler_norml lern1 (@le_trans _ _ 0%R) ?leq_b1.
Qed.

Lemma bernoulli_RV1 (X : bernoulliRV P p) : P [set i | X i == 1%R] = p%:E.
Proof.
have/(congr1 (fun f => f [set 1%:R])):= @bernoulliP _ _ _ _ _ X.
rewrite bernoulli_probE// diracE/= mem_set// mule1// diracE/= memNset//.
by rewrite mule0 adde0 -preimage_set1 /distribution /= => <-.
Qed.

Lemma bernoulli_RV2 (X : bernoulliRV P p) : P [set i | X i == 0%R] = (`1-p)%:E.
Proof.
have/(congr1 (fun f => f [set 0%:R])):= @bernoulliP _ _ _ _ _ X.
rewrite bernoulli_probE// diracE/= memNset// mule0// diracE/= mem_set// add0e mule1.
by rewrite /distribution /= => <-; rewrite -preimage_set1.
Qed.

Lemma bernoulli_expectation (X : bernoulliRV P p) :
  'E_P[bool_to_real R X] = p%:E.
Proof.
rewrite unlock.
rewrite -(@ge0_integral_distribution _ _ _ _ _ _ X (EFin \o GRing.natmul 1))//; last first.
  by move=> y //=.
rewrite /bernoulli_prob/=.
rewrite (@eq_measure_integral _ _ _ _ (bernoulli_prob p)); last first.
   by move=> A mA _ /=; congr (_ _); exact: bernoulliP.
rewrite integral_bernoulli_prob//=.
by rewrite -!EFinM -EFinD mulr0 addr0 mulr1.
Qed.

Lemma integrable_bernoulli (X : bernoulliRV P p) :
  P.-integrable [set: T] (EFin \o bool_to_real R X).
Proof.
apply/integrableP; split.
  by apply: measurableT_comp => //; exact: measurable_bool_to_real.
have -> : \int[P]_x `|(EFin \o bool_to_real R X) x| = 'E_P[bool_to_real R X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  by rewrite gee0_abs //= lee_fin.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma Lfun_bernoulli (X : bernoulliRV P p) q :
  1 <= q -> (bool_to_real R X : T -> R) \in Lfun P q.
Proof.
move=> q1; apply: (@Lfun_bounded _ _ _ P) => //.
exact: bounded_fun_bool_to_real.
Qed.

Lemma bool_RV_sqr (X : {RV P >-> bool}) :
  ((bool_to_real R X ^+ 2) = bool_to_real R X :> (T -> R))%R.
Proof.
apply: funext => x /=.
rewrite /GRing.exp /bool_to_real /GRing.mul/=.
by case: (X x) => /=; rewrite ?mulr1 ?mulr0.
Qed.

Lemma bernoulli_variance (X : bernoulliRV P p) :
  'V_P[bool_to_real R X] = (p * (`1-p))%:E.
Proof.
rewrite (@varianceE _ _ _ _ (bool_to_real R X));
  [|rewrite ?[X in _ \o X]bool_RV_sqr; apply: Lfun_bernoulli..]; last first.
  by rewrite lee1n.
rewrite [X in 'E_P[X]]bool_RV_sqr !bernoulli_expectation//.
by rewrite expe2 -EFinD onemMr.
Qed.

Definition real_of_bool n : _ -> n.-tuple _ :=
  map_tuple (bool_to_real R : bernoulliRV P p -> {mfun _ >-> _}).

Definition trial_value n (X : n.-tuple {RV P >-> _})
    : {RV (\X_n P) >-> R : realType} :=
  (\sum_(i < n) Tnth X i)%R.

Definition bool_trial_value n := @trial_value n \o @real_of_bool n.

Lemma btr_ge0 (X : {RV P >-> bool}) t : (0 <= bool_to_real R X t)%R.
Proof. by []. Qed.

Lemma btr_le1 (X : {RV P >-> bool}) t : (bool_to_real R X t <= 1)%R.
Proof. by rewrite /bool_to_real/=; case: (X t). Qed.

Lemma expectation_bernoulli_trial n (X : n.-tuple (bernoulliRV P p)) :
  'E_(\X_n P)[bool_trial_value X] = (n%:R * p)%:E.
Proof.
rewrite expectation_ipro_sum; last first.
  by move=> Xi /tnthP [i] ->; rewrite tnth_map; apply: Lfun_bernoulli.
transitivity (\sum_(i < n) p%:E).
  by apply: eq_bigr => k _; rewrite !tnth_map bernoulli_expectation.
by rewrite sumEFin big_const_ord iter_addr addr0 mulrC mulr_natr.
Qed.

Lemma bernoulli_trial_ge0 n (X : n.-tuple (bernoulliRV P p)) :
  (forall t, 0 <= bool_trial_value X t)%R.
Proof.
move=> t.
rewrite /bool_trial_value/=.
rewrite [in leRHS]fct_sumE.
apply/sumr_ge0 => /= i _.
rewrite /Tnth.
by rewrite !tnth_map.
Qed.

Lemma bernoulli_trial_mmt_gen_fun n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  let X := bool_trial_value X_ in
  'M_(\X_n P) X t = \prod_(i < n) 'M_P (bool_to_real R (tnth X_ i)) t.
Proof.
pose mmtX (i : 'I_n) : {RV P >-> R : realType} :=
  expR \o t \o* bool_to_real R (tnth X_ i).
transitivity ('E_(\X_n P)[ \prod_(i < n) Tnth (mktuple mmtX) i ]).
  congr expectation => /=; apply: funext => x/=.
  rewrite fct_sumE big_distrl/= expR_sum [in RHS]fct_prodE.
  apply: eq_bigr => i _.
  by rewrite /Tnth !tnth_map /mmtX/= tnth_ord_tuple.
rewrite expectation_ipro_prod; last first.
  move=> _ /mapP [/= i _ ->].
  apply/Lfun1_integrable/bounded_integrable => //.
  exists (expR `|t|); split => // M etM x _ /=.
  rewrite ger0_norm// (le_trans _ (ltW etM))// ler_expR/=.
  rewrite /bool_to_real/=.
  by case: (tnth X_ i x) => //=; rewrite ?mul1r ?mul0r// ler_norm.
apply: eq_bigr => /= i _.
by congr expectation; rewrite tnth_map/= tnth_ord_tuple.
Qed.

Arguments sub_countable [T U].
Arguments card_le_finite [T U].

Lemma bernoulli_mmt_gen_fun (X : bernoulliRV P p) (t : R) :
  'M_P (bool_to_real R X) t = (p * expR t + (1 - p))%:E.
Proof.
rewrite/mmt_gen_fun.
pose mmtX : {RV P >-> R : realType} := expR \o t \o* (bool_to_real R X).
set A := X @^-1` [set true].
set B := X @^-1` [set false].
have mA : measurable A by exact: measurable_sfunP.
have mB : measurable B by exact: measurable_sfunP.
have dAB : [disjoint A & B]
  by rewrite /disj_set /A /B preimage_true preimage_false setICr.
have TAB: setT = A `|` B by rewrite -preimage_setU -setT_bool preimage_setT.
rewrite unlock.
rewrite TAB integral_setU_EFin -?TAB//.
under eq_integral.
  move=> x /=.
  rewrite /A inE /bool_to_real /= => ->.
  rewrite mul1r.
  over.
rewrite integral_cst//.
under eq_integral.
  move=> x /=.
  rewrite /B inE /bool_to_real /= => ->.
  rewrite mul0r.
  over.
rewrite integral_cst//.
rewrite /A /B /preimage /=.
under eq_set do rewrite (propext (rwP eqP)).
rewrite bernoulli_RV1.
under eq_set do rewrite (propext (rwP eqP)).
rewrite bernoulli_RV2.
rewrite -EFinD; congr (_ + _)%:E; rewrite mulrC//.
by rewrite expR0 mulr1.
Qed.

(* wrong lemma *)
Lemma binomial_mmt_gen_fun n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  let X := bool_trial_value X_ : {RV \X_n P >-> R : realType} in
  'M_(\X_n P) X t = ((p * expR t + (1 - p))`^(n%:R))%:E.
Proof.
move: p01 => /andP[p0 p1] bX/=.
rewrite bernoulli_trial_mmt_gen_fun//.
under eq_bigr => i _ do rewrite bernoulli_mmt_gen_fun//.
rewrite big_const iter_mule mule1 cardT size_enum_ord -EFin_expe powR_mulrn//.
by rewrite addr_ge0// ?subr_ge0// mulr_ge0// expR_ge0.
Qed.

Lemma mmt_gen_fun_expectation n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  (0 <= t)%R ->
  let X := bool_trial_value X_ : {RV \X_n P >-> R : realType} in
  'M_(\X_n P) X t <= expeR ('E_(\X_n P)[X] * (expR t - 1)%:E).
Proof.
move=> t_ge0/=.
have /andP[p0 p1] := p01.
rewrite binomial_mmt_gen_fun//.
rewrite expectation_bernoulli_trial//.
rewrite addrCA -{2}(mulr1 p) -mulrN -mulrDr.
rewrite /= lee_fin.
rewrite -mulrA (mulrC (n%:R)) expRM ge0_ler_powR// ?nnegrE ?expR_ge0//.
  by rewrite addr_ge0// mulr_ge0// subr_ge0 -expR0 ler_expR.
exact: expR_ge1Dx.
Qed.

End properties_of_BernoulliRV.

(* the lemmas used in the sampling theorem that are generic w.r.t. R : realType *)
Section sampling_theorem_part1.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType} (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

(* [end of Theorem 2.4, Rajani]*)
Lemma end_thm24 n (X_ : n.-tuple (bernoulliRV P p)) (t delta : R) :
  (0 < delta)%R ->
  let X := bool_trial_value X_ in
  let mu := 'E_(\X_n P)[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: bernoulli_trial_ge0.
- by rewrite divr_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpM2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expRM lnK// posrE addr_gt0.
Qed.

(* [theorem 2.4, Rajani] / [thm 4.4.(2), MU] *)
Theorem sampling_ineq1 n (X_ : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta)%R ->
  let X := bool_trial_value X_ in
  let mu := 'E_(\X_n P)[X] in
  (\X_n P) [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => delta0.
set X := bool_trial_value X_.
set mu := 'E_(\X_n P)[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltrDl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expeR (mu * (expR t - 1)%:E)) *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  rewrite (le_trans (mmt_gen_fun_expectation p01 _ (ltW t0)))//.
rewrite -(@fineK _ mu)//; last first.
  by rewrite /mu expectation_bernoulli_trial.
rewrite [expeR _]/= mulrC expRM -mulNr mulrA expRM.
exact: end_thm24.
Qed.

Section xlnx_bounding.
Local Open Scope ring_scope.
Local Arguments derive_val {R V W a v f df}.

Let f (x : R) := x ^+ 2 - 2 * x * ln x.
Let idf (x : R) : 0 < x -> {df : R | is_derive x 1 f df}.
Proof.
move=> x0.
evar (df : (R : Type)); exists df.
apply: is_deriveD; first by [].
apply: is_deriveN.
apply: is_deriveM; first by [].
exact: is_derive1_ln.
Defined.
Let f1E : f 1 = 1. Proof. by rewrite /f expr1n ln1 !mulr0 subr0. Qed.
Let Df_gt0 (x : R) : 0 < x -> x != 1 -> 0 < 'D_1 f x.
Proof.
move=> x0 x1.
rewrite (derive_val (svalP (idf x0))) /=.
clear idf.
rewrite exp_derive deriveM// derive_cst derive_id .
rewrite scaler0 addr0 /GRing.scale /= !mulr1 expr1.
rewrite -mulrA divff ?lt0r_neq0//.
rewrite (mulrC _ 2) -mulrDr -mulrBr mulr_gt0//.
rewrite opprD addrA subr_gt0 -ltr_expR.
have:= x0; rewrite -lnK_eq => /eqP ->.
rewrite -[ltLHS]addr0 -(subrr 1) addrCA expR_gt1Dx//.
by rewrite subr_eq0.
Qed.

Let sqrxB2xlnx_lt1 (c x : R) :
  x \in `]0, 1[ -> x ^+ 2 - 2 * x * ln x < 1.
Proof.
rewrite in_itv=> /andP [] x0 x1.
fold (f x).
simpl in idf.
rewrite -f1E.
apply: (@gtr0_derive1_lt_oc _ f 0 1).
- move=> t /[!in_itv] /= /andP [] + _.
  by case/idf=> ? /@ex_derive.
- move=> t /[!in_itv] /= /andP [] t0 t1.
  rewrite derive1E.
  apply: Df_gt0 => //.
  by rewrite (lt_eqF t1).
- apply: derivable_within_continuous => t /[!in_itv] /= /andP [] + _.
  by case/idf=> ? /@ex_derive.
- by rewrite in_itv/=; apply/andP; split=> //; apply/ltW.
- by rewrite in_itv /= ltr01 lexx.
- assumption.
Qed.

Let sqrxB2xlnx_gt1 (c x : R) : 1 < x -> 1 < x ^+ 2 - 2 * x * ln x.
Proof.
move=> x1.
have x0 : 0 < x by rewrite (lt_trans _ x1).
fold (f x).
simpl in idf.
rewrite -f1E.
apply: (@gtr0_derive1_lt_cc _ f 1 x).
- move=> t /[!in_itv] /= /andP [] + _ => t1.
  have: 0 < t by rewrite (lt_trans _ t1).
  by case/idf=> ? /@ex_derive.
- move=> t /[!in_itv] /= /andP [] t1 tx.
  have t0: 0 < t by rewrite (lt_trans _ t1).
  rewrite derive1E.
  apply: Df_gt0=> //.
  by rewrite (gt_eqF t1).
- apply: derivable_within_continuous => t /[!in_itv] /= /andP [] + _ => t1.
  have: 0 < t by rewrite (lt_le_trans _ t1).
  by case/idf=> ? /@ex_derive.
- by rewrite in_itv/=; apply/andP; split=> //; apply/ltW.
- by rewrite in_itv /= lexx andbT ltW.
- assumption.
Qed.

Lemma xlnx_lbound_i01 (c x : R) :
  c <= 2 -> x \in `]0, 1[ -> x ^+ 2 - 1 < c * x * ln x.
Proof.
pose c' := c - 2.
have-> : c = c' + 2 by rewrite /c' addrAC -addrA subrr addr0.
rewrite -lerBrDr subrr.
move: c'; clear c => c.
rewrite ltrBlDr -ltrBlDl.
rewrite le_eqVlt=> /orP [/eqP-> |]; first by rewrite add0r; exact: sqrxB2xlnx_lt1.
move=> c0 /[dup] x01 /[!in_itv] /andP [] x0 x1.
rewrite -mulrA (addrC c) mulrDl !mulrA opprD addrA.
rewrite -[ltRHS]addr0 ltrD// ?sqrxB2xlnx_lt1// oppr_lt0.
by rewrite -mulrA nmulr_lgt0// nmulr_llt0// ln_lt0.
Qed.

Lemma xlnx_ubound_i1y (c x : R) :
  c <= 2 -> 1 < x -> c * x * ln x < x ^+ 2 - 1.
Proof.
pose c' := c - 2.
have-> : c = c' + 2 by rewrite /c' addrAC -addrA subrr addr0.
rewrite -lerBrDr subrr.
move: c'; clear c => c.
rewrite ltrBrDr -ltrBrDl.
rewrite le_eqVlt=> /orP [/eqP-> |]; first by rewrite add0r; exact: sqrxB2xlnx_gt1.
move=> c0 x1.
rewrite -mulrA (addrC c) mulrDl !mulrA opprD addrA.
rewrite -[ltLHS]addr0 ltrD// ?sqrxB2xlnx_gt1// oppr_gt0.
by rewrite nmulr_rlt0 ?ln_gt0// nmulr_rlt0 ?(lt_trans _ x1).
Qed.

End xlnx_bounding.

(* [Theorem 2.6, Rajani] / [thm 4.5.(2), MU] *)
Theorem sampling_ineq3 n (X_ : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta < 1)%R ->
  let X := bool_trial_value X_ : {RV \X_n P >-> R : realType} in
  let mu := 'E_(\X_n P)[X] in
  (\X_n P) [set i | X i <= (1 - delta) * fine mu]%R <=
    (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> /andP[delta0 delta1] /=.
set X := bool_trial_value X_ : {RV \X_n P >-> R : realType}.
set mu := 'E_(\X_n P)[X].
have /andP[p0 p1] := p01.
apply: (@le_trans _ _
    (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    (\X_n P) [set i | (X i <= (1 - delta) * fine mu)%R] =
    (\X_n P) [set i | `|(expR \o t \o* X) i|%:E >=
      (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    by rewrite ln_lt0// subr_gt0 delta1/= ltrBlDl ltrDr.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ ((fine 'E_(\X_n P)[normr \o expR \o t \o* X])
      / (expR (t * (1 - delta) * fine mu)))%:E).
    rewrite EFinM lee_pdivlMr ?expR_gt0// muleC fineK; last first.
      rewrite norm_expR.
      have -> : 'E_(\X_n P)[expR \o t \o* X] = 'M_(\X_n P) X t by [].
      by rewrite binomial_mmt_gen_fun.
    apply: (@markov _ _ _ (\X_n P) (expR \o t \o* X) id
      (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    exact: expR_gt0.
  apply: (@le_trans _ _ ((expR ((expR t - 1) * fine mu))
      / (expR (t * (1 - delta) * fine mu)))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_(\X_n P)[expR \o t \o* X] = 'M_(\X_n P) X t by [].
    rewrite binomial_mmt_gen_fun//.
    rewrite /mu /X expectation_bernoulli_trial//.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expRM powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      by rewrite addr_ge0 ?mulr_ge0// subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expRM.
    rewrite addrCA -{2}(mulr1 p) -mulrBr addrAC subrr sub0r mulrC mulNr.
    exact: expR_ge1Dx.
  rewrite !lnK ?posrE ?subr_gt0//.
  rewrite -addrAC subrr sub0r -mulrA [X in (_ / X)%R]expRM lnK ?posrE ?subr_gt0//.
  rewrite -[in leRHS]powR_inv1 ?powR_ge0// powRM// ?expR_ge0 ?invr_ge0 ?powR_ge0//.
  by rewrite powRAC powR_inv1 ?powR_ge0// powRrM expRM.
rewrite lee_fin.
rewrite -mulrN -mulrA [in leRHS]mulrC expRM ge0_ler_powR// ?nnegrE.
- by rewrite fine_ge0// expectation_ge0// => x; exact: bernoulli_trial_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- by rewrite expR_ge0.
- rewrite -ler_ln ?posrE ?divr_gt0 ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_div ?posrE ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_powR.
  (* analytical argument reduced to xlnx_lbound_i01; p.66 of mu's book *)
  rewrite ler_pdivlMr// mulrDl.
  rewrite -lerBrDr -lerBlDl !mulNr !opprK [in leRHS](mulrC _ 2%R) mulrA.
  rewrite ltW// (le_lt_trans _ (xlnx_lbound_i01 _ _))//; last first.
    by rewrite memB_itv add0r in_itv/=; apply/andP; split.
  by rewrite addrC lerBrDr mulr_natr -[in leRHS]sqrrN opprB sqrrB1.
Qed.

End sampling_theorem_part1.

(* this is a preliminary for the second part of the proof of the sampling lemma *)
Module with_interval.
Declare Scope bigQ_scope.
Import Reals.
Import Rstruct Rstruct_topology.
Import Interval.Tactic.

Section exp2_le8.
Let R := Rdefinitions.R.
Local Open Scope ring_scope.

Lemma exp2_le8 : (exp 2 <= 8)%R.
Proof. interval. Qed.

Lemma exp2_le8_conversion : reflect (exp 2 <= 8)%R (expR 2 <= 8 :> R).
Proof.
rewrite RexpE (_ : 8%R = 8); last first.
  by rewrite !mulrS -!RplusE Rplus_0_r !RplusA !IZRposE/=.
by apply: (iffP idP) => /RleP.
Qed.

End exp2_le8.
End with_interval.

Section xlnx_bounding_with_interval.
Let R := Rdefinitions.R.
Local Open Scope ring_scope.

Lemma xlnx_lbound_i12 (x : R) : x \in `]0, 1[ ->
  x + x^+2 / 3 <= (1 + x) * ln (1 + x).
Proof.
move=> x01; rewrite -subr_ge0.
pose f (x : R^o) := (1 + x) * ln (1 + x) - (x + x ^+ 2 / 3).
have f0 : f 0 = 0 by rewrite /f expr0n /= mul0r !addr0 ln1 mulr0 subr0.
rewrite [leRHS](_ : _ = f x) // -f0.
evar (df0 : R -> R); evar (df : R -> R).
have idf (y : R^o) : 0 < 1 + y -> is_derive y (1:R) f (df y).
  move=> y1.
  rewrite (_ : df y = df0 y).
    apply: is_deriveB; last exact: is_deriveD.
    apply: is_deriveM=> //.
    apply: is_derive1_comp=> //.
    exact: is_derive1_ln.
  rewrite /df0.
  rewrite deriveD// derive_cst derive_id.
  rewrite /GRing.scale /= !(mulr0,add0r,mulr1).
  rewrite divff ?lt0r_neq0// opprD addrAC addrA subrr add0r.
  instantiate (df := fun y : R => - (3^-1 * (y + y)) + ln (1 + y)).
  reflexivity.
clear df0.
have y1cc y : y \in `[0, 1] -> 0 < 1 + y.
  rewrite in_itv /= => /andP [] y0 ?.
  by have y1: 0 < 1 + y by apply: (le_lt_trans y0); rewrite ltrDr.
have y1oo y : y \in `]0, 1[ -> 0 < 1 + y by move/subset_itv_oo_cc/y1cc.
have dfge0 y : y \in `]0, 1[ -> 0 <= df y.
  move=> y01.
  have:= y01.
  rewrite /df in_itv /= => /andP [] y0 y1.
  rewrite -lerBlDl opprK add0r -mulr2n -(mulr_natl _ 2) mulrA.
  rewrite [in leLHS](_ : y = 1 + y - 1); last by rewrite addrAC subrr add0r.
  pose iy:= Itv01 (ltW y0) (ltW y1).
  have y1E: 1 + y = @convex.conv _ R^o iy 2 1.
    rewrite convRE /= /onem mulr1 (mulr_natr _ 2) mulr2n.
    by rewrite addrACA subrr addr0 addrC.
  rewrite y1E; apply: (le_trans _ (concave_ln _ _ _))=> //.
  rewrite -y1E addrAC subrr add0r convRE ln1 mulr0 addr0 /=.
  rewrite mulrC ler_pM// ?(@ltW _ _ 0)// mulrC.
  rewrite ler_pdivrMr//.
  rewrite -[leLHS]expRK -[leRHS]expRK ler_ln ?posrE ?expR_gt0//.
  rewrite expRM/= powR_mulrn ?expR_ge0// lnK ?posrE//.
  rewrite !exprS expr0 mulr1 -!natrM mulnE /=.
  exact/with_interval.exp2_le8_conversion/with_interval.exp2_le8.
apply: (@ger0_derive1_le_cc R f 0 1).
- by move=> y /y1oo /idf /@ex_derive.
- move=> y /[dup] /y1oo /idf /@derive_val.
  by rewrite derive1E => ->; exact: dfge0.
- by apply: derivable_within_continuous=> y /y1cc /idf /@ex_derive.
- by rewrite bound_itvE.
- exact: subset_itv_oo_cc.
- by have:= x01; rewrite in_itv=> /andP /= [] /ltW.
Qed.

End xlnx_bounding_with_interval.

(* the rest of the sampling theorem including lemmas relying on the Rocq standard library *)
Section sampling_theorem_part2.
Local Open Scope ereal_scope.
Let R := Rdefinitions.R.
Context d (T : measurableType d) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.
Local Open Scope ereal_scope.

(* [Theorem 2.5, Rajani] *)
Theorem sampling_ineq2 n (X_ : n.-tuple (bernoulliRV P p)) (delta : R) :
  let X := bool_trial_value X_ in
  let mu := 'E_(\X_n P)[X] in
  (0 < n)%N ->
  (0 < delta < 1)%R ->
  (\X_n P) [set i | X i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> X mu n0 /[dup] delta01 /andP[delta0 _].
apply: (@le_trans _ _
    (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK ?posrE ?addr_gt0//.
  exact: sampling_ineq1.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    rewrite fine_ge0//; apply: expectation_ge0 => t.
    exact: bernoulli_trial_ge0.
  by rewrite lerB// xlnx_lbound_i12.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

(* [Corollary 2.7, Rajani] / [Corollary 4.7, MU] *)
Corollary sampling_ineq4 n (X_ : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta < 1)%R ->
  (0 < n)%N ->
  (0 < p)%R ->
  let X := bool_trial_value X_ in
  let mu := 'E_(\X_n P)[X] in
  (\X_n P) [set i | `|X i - fine mu | >= delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> /andP[d0 d1] n0 p0/=.
set X := bool_trial_value X_.
set mu := 'E_(\X_n P)[X].
have mu_gt0 : (0 < fine mu)%R.
  by rewrite /mu /X expectation_bernoulli_trial// mulr_gt0// ltr0n.
under eq_set => x.
  rewrite ler_normr.
  rewrite lerBrDl opprD opprK -{1}(mul1r (fine mu)) -mulrDl.
  rewrite -lerBDr -(lerN2 (- _)%R) opprK opprB.
  rewrite -{2}(mul1r (fine mu)) -mulrBl -!lee_fin.
  over.
rewrite /= set_orb measureU; last 3 first.
- rewrite -[X in measurable X]setTI; apply: measurable_lee => //.
  exact/measurable_EFinP/measurableT_comp.
- rewrite -[X in measurable X]setTI; apply: measurable_lee => //.
  exact/measurable_EFinP/measurableT_comp.
- rewrite disjoints_subset => /= x deltaX; apply/negP.
  rewrite -ltNge (lt_le_trans _ deltaX)// lte_fin ltr_pM2r//.
  by rewrite ltrD2l gt0_cp.
rewrite mulr2n EFinD leeD//=.
- by apply: sampling_ineq2; rewrite //d0 d1.
- have d01 : (0 < delta < 1)%R by rewrite d0.
  rewrite (le_trans (sampling_ineq3 p01 X_ d01))//.
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?sqr_ge0// fine_ge0//.
  by rewrite /mu expectation_ge0//= => t; exact: bernoulli_trial_ge0.
Qed.

(* [Theorem 3.1, Rajani] / [thm 4.7, MU] *)
Theorem sampling n (X_ : n.-tuple (bernoulliRV P p)) (theta delta : R) :
  let X x := ((bool_trial_value X_ x) / n%:R)%R in
  (0 < delta <= 1)%R -> (0 < theta < p)%R ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  (\X_n P) [set i | `| X i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X /andP[delta0 delta1] /andP[theta0 thetap] tdn.
have /andP[_ p1] := p01.
set epsilon := (theta / p)%R.
have p0 : (0 < p)%R by rewrite (lt_trans _ thetap).
have n0 : (0 < n)%N.
  rewrite -(@ltr_nat R) (lt_le_trans _ tdn)// mulr_gt0//.
    by rewrite divr_gt0// exprn_gt0.
  by rewrite ln_gt0// ltr_pdivlMr ?mul1r// (le_lt_trans delta1)// ltr1n.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : (\X_n P) [set i | `| X i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in (\X_n P) X <= _](_ : _ =
      [set i | `| bool_trial_value X_ i - p * n%:R |
        >= epsilon * p * n%:R]%R); last first.
    apply/seteqP; split => [t|t]/=.
      move/(@ler_wpM2r _ n%:R (ler0n _ _)) => /le_trans; apply.
      rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R)// -normrM mulrBl.
      by rewrite -mulrA mulVf ?mulr1// ?gt_eqF ?ltr0n.
    move/(@ler_wpM2r _ n%:R^-1); rewrite invr_ge0// ler0n => /(_ erefl).
    rewrite -(mulrA _ _ n%:R^-1)%R divff ?mulr1 ?gt_eqF ?ltr0n//.
    move=> /le_trans; apply.
    rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R^-1)// -normrM mulrBl.
    by rewrite -mulrA divff ?mulr1// gt_eqF// ltr0n.
  rewrite -mulrA.
  have -> : (p * n%:R)%R = fine (p * n%:R)%:E by [].
  rewrite -(mulrC _ p) -(expectation_bernoulli_trial p01 X_).
  exact: (@sampling_ineq4 _ X_ epsilon).
have step2 : (\X_n P) [set i | `| X i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA.
  rewrite /epsilon -mulrA mulVf ?gt_eqF// mulr1 -!mulrA !ler_wpM2l ?(ltW theta0)//.
  rewrite mulrCA ler_wpM2l ?(ltW theta0)//.
  rewrite [X in (_ * X)%R]mulrA mulVf ?gt_eqF// -[leLHS]mul1r [in leRHS]mul1r.
  by rewrite ler_wpM2r// invf_ge1.
suff : delta%:E >= (\X_n P) [set i | (`|X i - p| >= theta)%R].
  rewrite [X in (\X_n P) X <= _ -> _](_ : _ =
      ~` [set i | (`|X i - p| < theta)%R]); last first.
    apply/seteqP; split => [t|t]/=.
      by rewrite leNgt => /negP.
    by rewrite ltNge => /negP/negPn.
  have ? : measurable [set i | (`|X i - p| < theta)%R].
    under eq_set => x do rewrite -lte_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X//.
    by apply: measurable_lte => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  rewrite probability_setC// lee_subel_addr//.
  rewrite -lee_subel_addl//; last by rewrite fin_num_measure.
  move=> /le_trans; apply.
  rewrite le_measure ?inE//.
    under eq_set => x do rewrite -lee_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X//.
    by apply: measurable_lee => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  by move=> t/= /ltW.
apply: (le_trans step2).
rewrite lee_fin -(mulr_natr _ 2) -ler_pdivlMr//.
rewrite -(@lnK _ (delta / 2)%R); last by rewrite posrE divr_gt0.
rewrite ler_expR mulNr lerNl -lnV; last by rewrite posrE divr_gt0.
rewrite invf_div ler_pdivlMr// mulrC.
rewrite -ler_pdivrMr; last by rewrite exprn_gt0.
by rewrite mulrAC.
Qed.

End sampling_theorem_part2.
