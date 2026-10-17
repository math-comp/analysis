From HB Require Import structures.
From mathcomp Require Import boot order algebra finmap.
From mathcomp Require Import boolp classical_sets cardinality fsbigop.
From mathcomp Require Import reals topology ereal sequences esum measure.
From mathcomp Require Import simple_functions lebesgue_integral_definition
  measurable_fun_approximation lebesgue_integral_monotone_convergence.
From mathcomp Require Import numfun measurable_realfun.

(**md**************************************************************************)
(* # integral w.r.t. counting measure as an infinite sum                      *)
(*                                                                            *)
(* The goal of this file is to show that                                      *)
(* $\int_A f \, d(\mathrm{counting}) = \sum_{x\in A} f(x)$.                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Counting.
Context {d} {T : measurableType d} {R : realType}.
Hypothesis msingl : forall i : T, measurable [set i].

Lemma cstMcounting_esum (c : R) (A : set T) : (0 <= c)%R ->
  c%:E * @counting T R A = \esum_(x in A) c%:E.
Proof.
move=> c_ge0.
have [->|] := eqVneq c 0%R; first by rewrite mul0e; apply/esym/esum1.
rewrite neq_lt ltNge c_ge0/= => c_gt0.
have [finA|infA] := pselect (finite_set A).
+ rewrite /counting (asboolT finA) esum_fset// -EFinM mulr_natr.
  by rewrite fsbig_finite//= sumEFin big_const_seq count_predT iter_addr addr0.
+ by rewrite /counting asboolF// mulry gtr0_sg// mul1e (infinite_esum_cst c%:E).
Qed.

Import HBNNSimple.

Lemma sintegral_counting_esum (h : {nnsfun T >-> R}) :
  sintegral (@counting T R) h = \esum_(x in [set: T]) (h x)%:E.
Proof.
rewrite sintegralE//=.
transitivity (\sum_(c \in range h) \esum_(x in (h @^-1` [set c])) (h x)%:E).
  apply: eq_fsbigr => _ /set_mem/= -[x _ <-].
  by rewrite cstMcounting_esum//; apply: eq_esum => x0 ->.
rewrite -esum_fset//.
  by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
rewrite -esum_bigcup; first exact: trivIset_preimage1.
- by move=> ?; rewrite lee_fin.
- suff -> : \bigcup_(c in range h) h @^-1` [set c] = [set: T] by [].
  by rewrite -subTset => y _; exists (h y).
Qed.

Local Lemma ge0_integral_counting_esum (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  (forall x, 0 <= f x) ->
  \int[@counting T R]_x f x = \esum_(x in [set: T]) f x.
Proof.
move=> mf f0 //=.
pose g := nnsfun_approx measurableT mf.
have g_ge0 x n : 0 <= (g n x)%:E by rewrite lee_fin.
have g_nd x : nondecreasing_seq (fun n => (g n x)%:E).
  by move=> m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
have gE x : f x = ereal_sup (range (fun n => (g n x)%:E)).
  rewrite -(cvg_lim _ (ereal_nondecreasing_cvgn (g_nd x)))//.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
under eq_esum do rewrite gE.
rewrite (exchange_esum_ereal_sup g_ge0 g_nd).
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g)//=.
  by move=> x; exact: cvg_nnsfun_approx.
apply/cvg_lim => //=.
under eq_cvg do rewrite /= sintegral_counting_esum.
by apply: ereal_nondecreasing_cvgn => m n ?; apply: le_esum => x _; exact: g_nd.
Qed.

Lemma integral_countingT_esum (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  \int[@counting T R]_x f x = \esum_(x in [set: T]) f x.
Proof.
move=> mf; rewrite integralE esumE/=.
rewrite ge0_integral_counting_esum//; first exact: measurable_funepos.
by rewrite ge0_integral_counting_esum//; exact: measurable_funeneg.
Qed.

Lemma integral_counting_esum (A : set T) (f : T -> \bar R) :
  measurable A -> measurable_fun [set: T] f ->
  \int[@counting T R]_(x in A) f x = \esum_(x in A) f x.
Proof.
move=> mA mf; rewrite integral_mkcond integral_countingT_esum.
- by apply/measurable_restrict => //; rewrite setTI; exact: measurable_funTS.
- by rewrite [RHS]esum_mkcond.
Qed.

End Counting.
