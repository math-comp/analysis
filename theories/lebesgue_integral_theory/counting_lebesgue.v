From HB Require Import structures.
From mathcomp Require Import boot order algebra finmap.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals topology ereal sequences esum measure.
From mathcomp Require Import simple_functions lebesgue_integral_definition
  lebesgue_integral_nonneg measurable_fun_approximation
  lebesgue_integral_monotone_convergence.
From mathcomp Require Import numfun measurable_realfun.

(**md**************************************************************************)
(* #                                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*   Equality of esum and lebesgue integral on measurable_space               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Import HBNNSimple.

Section Counting.
Context d (T : measurableType d) (R : realType).
Hypothesis msingl : forall i : T, measurable [set i].

Lemma counting_esum_cst (c : R) (A : set T) : (0 <= c)%R ->
  (c%:E * @counting T R A = \esum_(x in A) c%:E)%E.
Proof.
move=> c0.
have [-> | c_neq] := eqVneq c 0%R.
  by rewrite mul0e; apply/esym/esum1.
have c_pos : (0 < c)%R by rewrite lt_def c_neq.
have [finA|infA] := pselect (finite_set A).
+ rewrite /counting (asboolT finA).
  rewrite esum_fset// fsbig_finite//=.
  rewrite sumEFin big_const_seq count_predT iter_addr addr0.
  by rewrite -EFinM mulr_natr.
+ rewrite /counting asboolF//=.
  rewrite mulry gtr0_sg// mul1e.
  apply/esym/eqyP => r r0.
  have [B BA Brc] := infinite_set_fset (Num.Def.truncn (c^-1 * r)).+1 infA.
  apply: esum_ge => // ; exists [set` B].
    by split=> //; apply/subsetP => x; rewrite inE => /BA.
  rewrite fsbig_finite//= set_fsetK sumEFin big_const_seq count_predT.
  rewrite iter_addr addr0 -mulr_natr lee_fin -ler_pdivrMl//.
  apply: (@le_trans _ _ (((Num.Def.truncn (c^-1 * r)).+1)%:R)).
    exact: ltW (truncnS_gt _).
  rewrite ler_nat.
  exact: Brc.
Qed.

Lemma sintegral_counting_esum (h : {nnsfun T >-> R}) :
  (sintegral (@counting T R) h = \esum_(x in [set: T]) (h x)%:E)%E.
Proof.
rewrite sintegralE //=.
transitivity (\sum_(c \in range h)
                \esum_(x in (h @^-1` [set c] : set T)) (h x)%:E)%E.
+ apply: eq_fsbigr => c /set_mem/= -[x _ <-{c}].
  rewrite counting_esum_cst//.
  by apply: (eq_esum _ (fun=> (h x)%:E)) => x0 ->.
+ rewrite -esum_fset//.
  + by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
  rewrite -esum_bigcup.
  + exact: trivIset_preimage1.
  + by move=> ?; rewrite lee_fin.
  + suff -> : \bigcup_(c in range h) h @^-1` [set c] = [set: T] by [].
    apply/seteqP; split => [//|y _].
    by exists (h y); [exists y|].
Qed.

Local Lemma integral_counting_esum_ge0 (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_x f x = \esum_(x in [set: T]) f x)%E.
Proof.
move=> mf f0 //=.
pose g := nnsfun_approx measurableT mf.
have g_ge0 x n : (0 <= (g n x)%:E)%E by rewrite lee_fin.
have g_nd x : nondecreasing_seq (fun n => (g n x)%:E)%E.
+ by move=> m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
have gE x : (f x = ereal_sup (range (fun n => (g n x)%:E)))%E.
+ rewrite -(cvg_lim _ (ereal_nondecreasing_cvgn (g_nd x)))//.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
under eq_esum do rewrite gE.
rewrite (exchange_esum_ereal_sup g_ge0 g_nd).
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g)//=.
+ by move=> x; exact: cvg_nnsfun_approx.
apply/cvg_lim => //=.
under eq_cvg do rewrite /= sintegral_counting_esum.
by apply: ereal_nondecreasing_cvgn => m n mn; apply: le_esum => x _; exact: g_nd.
Qed.

Lemma integral_counting_esum (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  (\int[@counting T R]_x f x = \esum_(x in [set: T]) f x)%E.
Proof.
 move=> mf; rewrite integralE esumE.
 by rewrite (integral_counting_esum_ge0 (measurable_funepos mf))//
      (integral_counting_esum_ge0 (measurable_funeneg mf))//.
Qed.

Lemma integral_counting_esum_set (A : set T) (f : T -> \bar R) :
  measurable A ->
  measurable_fun [set: T] f ->
  (\int[@counting T R]_(x in A) f x = \esum_(x in A) f x)%E.
Proof.
move=> mA mf; rewrite integral_mkcond integral_counting_esum.
- by apply/(measurable_restrict _ mA measurableT); rewrite setTI; exact: measurable_funTS.
- rewrite [RHS]esum_mkcond; apply: eq_esum => x _.
  by rewrite patchE.
Qed.

End Counting.
