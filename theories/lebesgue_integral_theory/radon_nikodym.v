(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference finmap fingroup perm rat.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets cardinality.
From mathcomp Require Import functions fsbigop set_interval reals ereal.
From mathcomp Require Import topology numfun normedtype derive sequences esum.
From mathcomp Require Import measure realfun measurable_realfun.
From mathcomp Require Import lebesgue_measure.
From mathcomp Require Import lebesgue_integral_definition lebesgue_integrable
  lebesgue_integral_nonneg lebesgue_Rintegral
  lebesgue_integral_monotone_convergence measurable_fun_approximation
  simple_functions.

(**md**************************************************************************)
(* # Radon-Nikodym theorem                                                    *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - Y. Ishiguro, R. Affeldt. The Radon-Nikodym Theorem and the Lebesgue-     *)
(*   Stieltjes measure in Coq. Computer Software 41(2) 2024                   *)
(*                                                                            *)
(* ## Theory                                                                  *)
(* ```                                                                        *)
(*       induced_charge intf == charge induced by a function f : T -> \bar R  *)
(*                              R has type realType; T is a measurableType.   *)
(*                              intf is a proof that f is integrable over     *)
(*                              [set: T]                                      *)
(*              'd nu '/d mu == Radon-Nikodym derivative of nu w.r.t. mu      *)
(*                              (the scope is charge_scope)                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'d nu '/d mu" (mu at next level,
  format "''d'  nu  ''/d'  mu").

Declare Scope charge_scope.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition induced_charge d (T : measurableType d) {R : realType}
    (mu : {measure set T -> \bar R}) (f : T -> \bar R)
    (intf : mu.-integrable [set: T] f) :=
  fun A => (\int[mu]_(t in A) f t)%E.

#[deprecated(since="mathcomp-analysis 1.15.0", note="renamed to `induced_charge`")]
Notation induced := induced_charge (only parsing).

Section induced_charge.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Lemma semi_sigma_additive_nng_induced (f : T -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x) ->
  semi_sigma_additive (fun A => \int[mu]_(t in A) f t).
Proof.
move=> mf f0 /= F mF tF mUF; rewrite ge0_integral_bigcup//=.
  exact: measurable_funTS.
by apply: is_cvg_ereal_nneg_natsum_cond => // n _ _; exact: integral_ge0.
Qed.

Variable f : T -> \bar R.
Hypothesis intf : mu.-integrable setT f.

Local Notation nu := (induced_charge intf).

Let nu0 : nu set0 = 0. Proof. by rewrite /nu integral_set0. Qed.

Let finnu A : measurable A -> nu A \is a fin_num.
Proof.
by move=> mA; apply: integrable_fin_num => //=; exact: integrableS intf.
Qed.

Let snu : semi_sigma_additive nu.
Proof.
move=> /= F mF tF mUF; set SF := (f in f n @[n --> \oo] --> _).
rewrite (_ : SF = fun n =>
    \sum_(0 <= i < n) (\int[mu]_(x in F i) f^\+ x) -
    \sum_(0 <= i < n) (\int[mu]_(x in F i) f^\- x)).
  apply/funext => n; rewrite /SF; under eq_bigr do rewrite /nu integralE.
  rewrite big_split/= sumeN//= => i j _ _.
  rewrite fin_num_adde_defl// integrable_fin_num//= integrable_funeneg//=.
  exact: integrableS intf.
rewrite /nu integralE; apply: cvgeD.
- rewrite fin_num_adde_defr// integrable_fin_num//=.
  by apply: integrable_funepos => //=; exact: integrableS intf.
- apply/semi_sigma_additive_nng_induced => //.
  by apply: measurable_funepos; exact: (measurable_int mu).
- apply/cvgeN/semi_sigma_additive_nng_induced => //=.
  by apply: measurable_funeneg; exact: (measurable_int mu).
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ nu nu0 finnu snu.

End induced_charge.

Section dominates_induced.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Variable f : T -> \bar R.
Hypothesis intf : mu.-integrable setT f.

Let intnf : mu.-integrable [set: T] (abse \o f).
Proof. exact: integrable_abse. Qed.

Lemma dominates_induced : induced_charge intnf `<< mu.
Proof.
apply/null_content_dominatesP => /= A mA muA.
rewrite /induced_charge; apply/eqP; rewrite -abse_eq0 eq_le abse_ge0 andbT.
rewrite (le_trans (le_abse_integral _ _ _))//=.
  by case/integrableP : intnf => /= + _; exact: measurable_funTS.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
under eq_integral do rewrite abse_id.
apply: null_set_integral => //=.
by apply: measurable_funTS; apply: measurable_int intnf.
Qed.

End dominates_induced.

Section integral_normr_continuous.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Variable f : T -> R.
Hypothesis intf : mu.-integrable setT (EFin \o f).

Let intnf : mu.-integrable setT (abse \o EFin \o f).
Proof. exact: integrable_abse. Qed.

Lemma integral_normr_continuous (e : R) : (0 < e)%R ->
  exists d : R, (0 < d)%R /\
  forall A, measurable A -> mu A < d%:E -> (\int[mu]_(x in A) `|f x| < e)%R.
Proof.
move=> e0; have [P [N pn]] := Hahn_decomposition (induced_charge intnf).
have [r [r0 re]] := charge_variation_continuous pn (dominates_induced intf) e0.
exists r; split => //= A mA Ad.
have {re} := re _ mA Ad.
rewrite -lte_fin; apply: le_lt_trans.
rewrite /Rintegral fineK; last first.
  rewrite -[leLHS](gee0_abs)//; first exact: integral_ge0.
  exact: (le_trans _ (abse_charge_variation _ _)).
have : mu.-integrable A (abse \o EFin \o f) by exact: integrableS intnf.
move/integrableP : intf => -[_ intfoo _].
rewrite ge0_fin_numE//=; first exact: integral_ge0.
apply: le_lt_trans intfoo.
apply: ge0_subset_integral => //=.
apply: measurableT_comp => //.
by case/integrableP : intnf => /= /measurable_EFinP.
Qed.

End integral_normr_continuous.

(* We put definitions and lemmas used only in the proof of the Radon-Nikodym
   theorem as Definition's and Lemma's in the following modules. See
   https://staff.aist.go.jp/reynald.affeldt/documents/measure-ppl2023.pdf
   for an overview. *)
Module approxRN.
Section approxRN.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {measure set T -> \bar R}.

Definition approxRN := [set g : T -> \bar R | [/\
  forall x, 0 <= g x, mu.-integrable [set: T] g &
  forall E, measurable E -> \int[mu]_(x in E) g x <= nu E] ].

Let approxRN_neq0 : approxRN !=set0.
Proof.
exists (cst 0); split => //; first exact: integrable0.
by move=> E mE; rewrite integral0 measure_ge0.
Qed.

Definition int_approxRN := [set \int[mu]_x g x | g in approxRN].

Definition sup_int_approxRN := ereal_sup int_approxRN.

Lemma sup_int_approxRN_ge0 : 0 <= sup_int_approxRN.
Proof.
rewrite -(ereal_sup1 0) ereal_sup_le// sub1set inE.
exists (fun=> 0); last exact: integral0.
by split => //; [exact: integrable0|move=> E; rewrite integral0].
Qed.

End approxRN.
End approxRN.

Module approxRN_seq.
Section approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let approxRN := approxRN mu nu.
Let int_approxRN := int_approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Let int_approxRN_ub : exists M, forall x, x \in int_approxRN -> x <= M%:E.
Proof.
exists (fine (nu setT)) => x /[1!inE] -[g [g0 g1 g2] <-{x}].
by rewrite fineK ?fin_num_measure// (le_trans (g2 setT _))// inE.
Qed.

Lemma sup_int_approxRN_lty : M < +oo.
Proof.
rewrite /sup_int_approxRN; have [m hm] := int_approxRN_ub.
rewrite (@le_lt_trans _ _ m%:E)// ?ltey// ge_ereal_sup// => x IGx.
by apply: hm; rewrite inE.
Qed.

Lemma sup_int_approxRN_fin_num : M \is a fin_num.
Proof.
rewrite ge0_fin_numE; last exact: sup_int_approxRN_lty.
exact: sup_int_approxRN_ge0.
Qed.

Lemma approxRN_seq_ex : { g : (T -> \bar R)^nat |
  forall k, g k \in approxRN /\ \int[mu]_x g k x > M - k.+1%:R^-1%:E }.
Proof.
pose P m g := g \in approxRN /\ M - m.+1%:R^-1%:E < \int[mu]_x g x.
suff : { g : (T -> \bar R) ^nat & forall m, P m (g m)} by case => g ?; exists g.
apply: (@choice _ _ P) => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ int_approxRN) : (0 < m.+1%:R^-1 :> R)%R.
  by rewrite invr_gt0.
move/(_ sup_int_approxRN_fin_num) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition approxRN_seq : (T -> \bar R)^nat := sval approxRN_seq_ex.

Let g_ := approxRN_seq.

Lemma approxRN_seq_prop : forall m,
  g_ m \in approxRN /\ \int[mu]_x (g_ m x) > M - m.+1%:R^-1%:E.
Proof. exact: (projT2 approxRN_seq_ex). Qed.

Lemma approxRN_seq_ge0 x n : 0 <= g_ n x.
Proof. by have [+ _]:= approxRN_seq_prop n; rewrite inE /= => -[]. Qed.

Lemma measurable_approxRN_seq n : measurable_fun setT (g_ n).
Proof. by have := approxRN_seq_prop n; rewrite inE =>-[[_ /integrableP[]]]. Qed.

Definition max_approxRN_seq n x := \big[maxe/-oo]_(j < n.+1) g_ j x.

Let F_ := max_approxRN_seq.

Lemma measurable_max_approxRN_seq n : measurable_fun [set: T] (F_ n).
Proof.
elim: n => [|n ih].
  rewrite /F_ /max_approxRN_seq.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := approxRN_seq_prop 0%N.
  by rewrite inE /= => -[]// _ _ _; exact: measurable_approxRN_seq.
rewrite /F_ /max_approxRN_seq => m.
under eq_fun do rewrite big_ord_recr.
by apply: measurable_maxe => //; exact: measurable_approxRN_seq.
Qed.

Lemma max_approxRN_seq_ge0 n x : 0 <= F_ n x.
Proof.
by apply/bigmax_geP; right => /=; exists ord0; [|exact: approxRN_seq_ge0].
Qed.

Lemma max_approxRN_seq_ge n x : F_ n x >= g_ n x.
Proof. by apply/bigmax_geP; right => /=; exists ord_max. Qed.

Lemma max_approxRN_seq_nd x : nondecreasing_seq (F_ ^~ x).
Proof. by move=> a b ab; rewrite (le_bigmax_ord xpredT (g_ ^~ x)). Qed.

Lemma is_cvg_max_approxRN_seq n : cvg (F_ ^~ n @ \oo).
Proof. by apply: ereal_nondecreasing_is_cvgn; exact: max_approxRN_seq_nd. Qed.

Lemma is_cvg_int_max_approxRN_seq A :
  measurable A -> cvg ((fun n => \int[mu]_(x in A) F_ n x) @ \oo).
Proof.
move=> mA; apply: ereal_nondecreasing_is_cvgn => a b ab.
apply: ge0_le_integral => //.
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by apply: measurable_funS (measurable_max_approxRN_seq a).
- exact: measurable_funS (measurable_max_approxRN_seq b).
- by move=> x _; exact: max_approxRN_seq_nd.
Qed.

Definition is_max_approxRN m j :=
  [set x | F_ m x = g_ j x /\ forall k, (k < j)%N -> g_ k x < g_ j x].

Let E := is_max_approxRN.

Lemma is_max_approxRNE m j : E m j = [set x| F_ m x = g_ j x] `&`
    [set x |forall k, (k < j)%nat -> g_ k x < g_ j x].
Proof. by apply/seteqP; split. Qed.

Lemma trivIset_is_max_approxRN n : trivIset [set: nat] (E n).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Lemma bigsetU_is_max_approxRN m : \big[setU/set0]_(j < m.+1) E m j = [set: T].
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
  rewrite /F_ /max_approxRN_seq (bigmax_eq_arg _ ord0)//.
    by move=> ? _; rewrite leNye.
  rewrite /j0/=; case: ex_minnP => //= j' /andP[j'm /eqP].
  by rewrite /g_ => -> h.
by move=> k kj; exact: j0max.
Qed.

Lemma measurable_is_max_approxRN m j : measurable (E m j).
Proof.
rewrite is_max_approxRNE; apply: measurableI => /=.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_eqe => //; [exact: measurable_max_approxRN_seq|
                                   exact: measurable_approxRN_seq].
rewrite [T in measurable T](_ : _ =
  \bigcap_(k in `I_j) [set x | g_ k x < g_ j x])//.
apply: bigcap_measurableType => k _.
by rewrite -[X in measurable X]setTI; apply: measurable_lte => //;
  exact: measurable_approxRN_seq.
Qed.

End approxRN_seq.
End approxRN_seq.

Module lim_max_approxRN_seq.
Section lim_max_approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import approxRN_seq.

Let g := approxRN_seq mu nu.
Let F := max_approxRN_seq mu nu.

Definition fRN := fun x => lim (F ^~ x @ \oo).

Lemma measurable_fun_fRN : measurable_fun [set: T] fRN.
Proof.
rewrite (_ : fRN = fun x => limn_esup (F ^~ x)).
  apply/funext=> n; rewrite is_cvg_limn_esupE//.
  exact: is_cvg_max_approxRN_seq.
apply: measurable_fun_limn_esup => // n.
exact: measurable_max_approxRN_seq.
Qed.

Lemma fRN_ge0 x : 0 <= fRN x.
Proof.
apply: lime_ge => //; first exact: is_cvg_max_approxRN_seq.
by apply: nearW => ?; exact: max_approxRN_seq_ge0.
Qed.

Let int_fRN_lim A : measurable A ->
  \int[mu]_(x in A) fRN x = lim (\int[mu]_(x in A) F n x @[n --> \oo]).
Proof.
move=> mA; rewrite monotone_convergence// => n.
- exact: measurable_funS (measurable_max_approxRN_seq mu nu n).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by move=> ?; exact: max_approxRN_seq_nd.
Qed.

Let E m j := is_max_approxRN mu nu m j.

Let int_F_nu m A (mA : measurable A) : \int[mu]_(x in A) F m x <= nu A.
Proof.
rewrite [leLHS](_ : _ =
    \sum_(j < m.+1) \int[mu]_(x in (A `&` E m j)) F m x).
  rewrite -[in LHS](setIT A) -(bigsetU_is_max_approxRN mu nu m) big_distrr/=.
  rewrite -(@big_mkord _ _ _ m.+1 xpredT (fun i => A `&` is_max_approxRN mu nu m i)).
  rewrite ge0_integral_bigsetU ?big_mkord//.
  - by move=> n; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - exact: iota_uniq.
  - apply: trivIset_setIl; apply: (@sub_trivIset _ _ _ setT (E m)) => //.
    exact: trivIset_is_max_approxRN.
  - by apply: measurable_funTS => //; exact: measurable_max_approxRN_seq.
  - by move=> ? ?; exact: max_approxRN_seq_ge0.
rewrite [leLHS](_ : _ =
    \sum_(j < m.+1) (\int[mu]_(x in (A `&` (E m j))) g j x)).
  apply: eq_bigr => i _; apply:eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite /F Fmgi lexx.
rewrite [leRHS](_ : _ = \sum_(j < m.+1) (nu (A `&` E m j))).
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => A `&` E m i))//.
  - by move=> k; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - by apply: trivIset_setIl => //; exact: trivIset_is_max_approxRN.
  - apply: bigsetU_measurable => /= i _; apply: measurableI => //.
    exact: measurable_is_max_approxRN.
  - by rewrite -big_distrr/= bigsetU_is_max_approxRN// setIT.
apply: lee_sum => //= i _.
have [+ _] := approxRN_seq_prop mu nu i.
rewrite inE /G/= => -[_ _]; apply.
by apply: measurableI => //; exact: measurable_is_max_approxRN.
Qed.

Let F_G m : F m \in G.
Proof.
rewrite inE /G/=; split.
- by move=> ?; exact: max_approxRN_seq_ge0.
- apply/integrableP; split; first exact: measurable_max_approxRN_seq.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; first exact: max_approxRN_seq_ge0; over.
  have /le_lt_trans := int_F_nu m measurableT; apply.
  by apply: fin_num_fun_lty; exact: fin_num_measure.
- by move=> A; exact: int_F_nu.
Qed.

Let M_g_F m : M - m.+1%:R^-1%:E < \int[mu]_x g m x /\
              \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := approxRN_seq_prop mu nu m.
apply/andP; split; last first.
  by apply: ereal_sup_ubound; exists (F m)  => //; have := F_G m; rewrite inE.
apply: ge0_le_integral => //.
- by move=> x _; exact: approxRN_seq_ge0.
- exact: measurable_approxRN_seq.
- exact: measurable_max_approxRN_seq.
- by move=> ? _; exact: max_approxRN_seq_ge.
Qed.

Lemma int_fRN_lty : \int[mu]_x `|fRN x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last exact: sup_int_approxRN_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; first exact: fRN_ge0; over.
rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; have [_ /andP[_ ]] := M_g_F n.
Qed.

Lemma int_fRN_ub A : measurable A -> \int[mu]_(x in A) fRN x <= nu A.
Proof.
move=> mA; rewrite int_fRN_lim// lime_le //.
  exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; exact: int_F_nu.
Qed.

Lemma int_fRNE : \int[mu]_x fRN x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
  by apply: nearW => n; have [_ /andP[_]] := M_g_F n.
rewrite int_fRN_lim//.
have cvgM : (M - m.+1%:R^-1%:E) @[m --> \oo] --> M.
  rewrite -[X in _ --> X]sube0; apply: cvgeB.
  + by rewrite fin_num_adde_defl.
  + exact: cvg_cst.
  + apply/fine_cvgP; split; first exact: nearW.
    rewrite [X in X @ _ --> _](_ : _ = (fun x => x.+1%:R^-1)%R)//.
    apply/gtr0_cvgV0; first exact: nearW.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = fun n => n + 1)%N; last exact: cvg_addnr.
    by apply/funext => n; rewrite addn1.
apply: (@le_trans _ _ (lim (M - m.+1%:R^-1%:E @[m --> \oo]))).
  by move/cvg_lim : cvgM => ->.
apply: lee_lim; [by apply/cvg_ex; exists M|exact: is_cvg_int_max_approxRN_seq|].
apply: nearW => m.
by have [/[swap] /andP[? _] /ltW/le_trans] := M_g_F m; exact.
Qed.

Section ab_absurdo.
Context A (mA : measurable A) (h : \int[mu]_(x in A) fRN x < nu A).

Lemma epsRN_ex :
  {eps : {posnum R} | \int[mu]_(x in A) (fRN x + eps%:num%:E) < nu A}.
Proof.
have [muA0|] := eqVneq (mu A) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _; rewrite -(@gee0_abs _ (_ + _)).
      by rewrite adde_ge0 ?fRN_ge0.
    over.
  rewrite integral_abs_eq0//.
    by apply: emeasurable_funD => //; exact: measurable_funS measurable_fun_fRN.
  by rewrite (le_lt_trans _ h)// integral_ge0// => x Ax; exact: fRN_ge0.
rewrite neq_lt ltNge measure_ge0//= => muA_gt0.
pose mid := ((fine (nu A) - fine (\int[mu]_(x in A) fRN x)) / 2)%R.
pose e := (mid / fine (mu A))%R.
have ? : \int[mu]_(x in A) fRN x \is a fin_num.
  rewrite ge0_fin_numE// ?(lt_le_trans h)// ?leey// integral_ge0//.
  by move=> x Ax; exact: fRN_ge0.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last first.
    by rewrite fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
  by rewrite divr_gt0// subr_gt0// fine_lt// fin_num_measure.
exists (PosNum e_gt0); rewrite ge0_integralD//.
  by move=> x Ax; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite integral_cst// -lteBrDr//.
  by rewrite fin_numM// fin_num_measure.
rewrite -[X in _ * X](@fineK _ (mu A)) ?fin_num_measure//.
rewrite -EFinM divfK.
  by rewrite gt_eqF// fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
rewrite lteBrDl// addeC -lteBrDl//; last first.
rewrite -(@fineK _ (nu A))// ?fin_num_measure// -[X in _ - X](@fineK _)//.
rewrite -EFinB lte_fin /mid ltr_pdivrMr// ltr_pMr// ?ltr1n// subr_gt0.
by rewrite fine_lt// fin_num_measure.
Qed.

Definition epsRN := sval epsRN_ex.

Definition sigmaRN B := nu B - \int[mu]_(x in B) (fRN x + epsRN%:num%:E).

Let sigmaRN0 : sigmaRN set0 = 0.
Proof.
by rewrite /sigmaRN measure0 integral_set0 subee.
Qed.

Let fin_num_int_fRN_eps B : measurable B ->
  \int[mu]_(x in B) (fRN x + epsRN%:num%:E) \is a fin_num.
Proof.
move=> mB; rewrite ge0_integralD//.
  by move=> x Bx; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite fin_numD integral_cst// fin_numM ?fin_num_measure// andbT.
rewrite ge0_fin_numE ?measure_ge0.
  by apply: integral_ge0 => x Bx; exact: fRN_ge0.
rewrite (le_lt_trans _ int_fRN_lty)//.
under [in leRHS]eq_integral.
  move=> x _; rewrite gee0_abs.
    exact: fRN_ge0.
  over.
apply: ge0_subset_integral => //; first exact: measurable_fun_fRN.
by move=> x _; exact: fRN_ge0.
Qed.

Let fin_num_sigmaRN B : measurable B -> sigmaRN B \is a fin_num.
Proof.
move=> mB; rewrite /sigmaRN fin_numB fin_num_measure//=.
exact: fin_num_int_fRN_eps.
Qed.

Let sigmaRN_sigma_additive : semi_sigma_additive sigmaRN.
Proof.
move=> H mH tH mUH.
rewrite [X in X @ _ --> _](_ : _ = (fun n => \sum_(0 <= i < n) nu (H i) -
  \sum_(0 <= i < n) \int[mu]_(x in H i) (fRN x + epsRN%:num%:E))).
  apply/funext => n; rewrite big_split/= fin_num_sumeN// => i _.
  by rewrite fin_num_int_fRN_eps.
apply: cvgeB.
- by rewrite adde_defC fin_num_adde_defl// fin_num_measure.
- exact: measure_semi_sigma_additive.
rewrite (ge0_integral_bigcup _ mH _ _ tH).
- apply: emeasurable_funD => //=; apply: measurable_funTS.
  exact: measurable_fun_fRN.
- by move=> x _; rewrite adde_ge0 ?fRN_ge0.
have /cvg_ex[/= l hl] : cvg ((fun n =>
    \sum_(0 <= i < n) \int[mu]_(y in H i) (fRN y + epsRN%:num%:E)) @ \oo).
  apply: is_cvg_ereal_nneg_natsum => n _.
  by apply: integral_ge0 => x _; rewrite adde_ge0 ?fRN_ge0.
by rewrite (@cvg_lim _ _ _ _ _ _ l).
Qed.

HB.instance Definition _ := @isCharge.Build _ _ _ sigmaRN
  sigmaRN0 fin_num_sigmaRN sigmaRN_sigma_additive.

End ab_absurdo.

End lim_max_approxRN_seq.
End lim_max_approxRN_seq.

Section radon_nikodym_finite.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import lim_max_approxRN_seq.

Let f := fRN mu nu.
Let mf := measurable_fun_fRN.
Let f_ge0 := fRN_ge0.

Lemma radon_nikodym_finite : nu `<< mu -> exists f : T -> \bar R,
  [/\ forall x, f x >= 0, mu.-integrable [set: T] f &
      forall E, measurable E -> nu E = \int[mu]_(x in E) f x].
Proof.
move=> nu_mu; exists f; split.
  - by move=> x; exact: f_ge0.
  - by apply/integrableP; split; [exact: mf|exact: int_fRN_lty].
move=> // A mA.
apply/eqP; rewrite eq_le int_fRN_ub// andbT leNgt; apply/negP => abs.
pose sigma : {charge set T -> \bar R} := sigmaRN mA abs.
have [P [N [[mP posP] [mN negN] PNX PN0]]] := Hahn_decomposition sigma.
pose AP := A `&` P.
have mAP : measurable AP by exact: measurableI.
have muAP_gt0 : 0 < mu AP.
  rewrite lt0e measure_ge0// andbT.
  move/null_content_dominatesP in nu_mu.
  apply/eqP/(contra_not (nu_mu _ mAP))/eqP; rewrite gt_eqF//.
  rewrite (@lt_le_trans _ _ (sigma AP))//.
    rewrite (@lt_le_trans _ _ (sigma A))//; last first.
      rewrite (charge_partition _ _ mP mN)// geeDl//.
      by apply: negN => //; exact: measurableI.
    by rewrite sube_gt0// (proj2_sig (epsRN_ex mA abs)).
  rewrite /sigma/= /sigmaRN lee_subel_addl ?fin_num_measure//.
  by rewrite lee_paddl// integral_ge0// => x _; rewrite adde_ge0//; exact: f_ge0.
pose h x := if x \in AP then f x + (epsRN mA abs)%:num%:E else f x.
have mh : measurable_fun setT h.
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite setTI preimage_mem_true.
  - by apply: measurable_funTS; apply: emeasurable_funD => //; exact: mf.
  - by apply: measurable_funTS; exact: mf.
have hge0 x : 0 <= h x.
  by rewrite /h; case: ifPn => [_|?]; rewrite ?adde_ge0 ?f_ge0.
have hnuP S : measurable S -> S `<=` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS SAP.
  have : 0 <= sigma S.
    by apply: posP => //; apply: (subset_trans SAP); exact: subIsetr.
  rewrite sube_ge0; first by rewrite fin_num_measure// orbT.
  apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite -{1}(setIid S) integral_mkcondr; apply/eq_integral => x /[!inE] Sx.
  by rewrite /restrict /h !ifT// inE//; exact: SAP.
have hnuN S : measurable S -> S `<=` ~` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS ScAP; rewrite /h; under eq_integral.
    move=> x xS; rewrite ifF.
      by apply/negbTE; rewrite notin_setE; apply: ScAP; apply: set_mem.
    over.
  exact: int_fRN_ub.
have hnu S : measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> mS.
  rewrite -(setD0 S) -(setDv AP) setDDr.
  have mSIAP : measurable (S `&` AP) by exact: measurableI.
  have mSDAP : measurable (S `\` AP) by exact: measurableD.
  rewrite ge0_integral_setU //.
  - exact: measurable_funTS.
  - by rewrite disj_set2E setDE setIACA setICl setI0.
  rewrite measureU//.
    by rewrite setDE setIACA setICl setI0.
  by apply: leeD; [exact: hnuN|exact: hnuP].
have int_h_M : \int[mu]_x h x > M.
  have mCAP := measurableC mAP.
  have disj_AP : [disjoint AP & ~` AP] by exact/disj_set2P/setICr.
  rewrite -(setUv AP) ge0_integral_setU ?setUv// /h.
  under eq_integral do rewrite ifT//.
  under [X in _ < _ + X]eq_integral.
    by move=> x; rewrite inE /= => xE0p; rewrite memNset//; over.
  rewrite ge0_integralD//.
    - by move=> x _; exact: f_ge0.
    - by apply: measurable_funTS; exact: mf.
  rewrite integral_cst // addeAC -ge0_integral_setU//.
    by rewrite setUv//; exact: mf.
    by move=> x _; exact: f_ge0.
  rewrite setUv int_fRNE -lte_subel_addl.
    rewrite ge0_fin_numE ?sup_int_approxRN_lty.
      exact: sup_int_approxRN_ge0.
    exact: approxRN_seq.sup_int_approxRN_lty.
  by rewrite /M subee ?mule_gt0// approxRN_seq.sup_int_approxRN_fin_num.
have Gh : G h.
  split=> //; apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite (le_lt_trans (hnu _ measurableT))// ltey_eq fin_num_measure.
have : \int[mu]_x h x <= M.
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  rewrite (@ereal_sup_le _ [set \int[mu]_x h x] (int_approxRN mu nu))//.
  by rewrite sub1set inE; exists h.
by rewrite leNgt int_h_M.
Qed.

End radon_nikodym_finite.

Section radon_nikodym_sigma_finite.
Context d (T : measurableType d) (R : realType).
Variables (mu : {sigma_finite_measure set T -> \bar R})
          (nu : {finite_measure set T -> \bar R}).

Lemma radon_nikodym_sigma_finite : nu `<< mu ->
  exists f : T -> \bar R, [/\ forall x, f x >= 0, forall x, f x \is a fin_num,
    mu.-integrable [set: T] f &
    forall A, measurable A -> nu A = \int[mu]_(x in A) f x].
Proof.
move=> nu_mu; have [F TF /all_and2[mF muFoo]] := sigma_finiteT mu.
pose E := seqDU F.
have mE k : measurable (E k).
  by apply: measurableD => //; exact: bigsetU_measurable.
have muEoo k : mu (E k) < +oo.
  by rewrite (le_lt_trans _ (muFoo k))// le_measure ?inE//; exact: subDsetl.
have UET : \bigcup_i E i = [set: T] by rewrite TF [RHS]seqDU_bigcup_eq.
have tE := trivIset_seqDU F.
pose mu_ j : {finite_measure set T -> \bar R} := mfrestr (mE j) (muEoo j).
have nuEoo i : nu (E i) < +oo by rewrite ltey_eq fin_num_measure.
pose nu_ j : {finite_measure set T -> \bar R} := mfrestr (mE j) (nuEoo j).
have nu_mu_ k : nu_ k `<< mu_ k.
  apply/null_content_dominatesP => S mS mu_kS0.
  move/null_content_dominatesP : nu_mu; apply => //.
  exact: measurableI.
have [g_] := choice (fun j => radon_nikodym_finite (nu_mu_ j)).
move=> /all_and3[g_ge0 ig_ int_gE].
pose f_ j x := if x \in E j then g_ j x else 0.
have f_ge0 k x : 0 <= f_ k x by rewrite /f_; case: ifP.
have mf_ k : measurable_fun setT (f_ k).
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite setTI preimage_mem_true.
  - rewrite preimage_mem_true.
    by apply: measurable_funTS => //; have /integrableP[] := ig_ k.
have if_T k : integrable mu setT (f_ k).
  apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -(setUv (E k)) ge0_integral_setU //.
    - exact: measurableC.
    - by rewrite setUv.
    - exact/disj_set2P/subsets_disjoint.
  rewrite /f_; under eq_integral do rewrite ifT//.
  rewrite (@eq_measure_integral _ _ _ (E k) (mu_ k)).
    by move=> A mA AEj; rewrite /mu_ /= /mfrestr /mrestr setIidl.
  rewrite -int_gE ?inE//.
  under eq_integral.
    move=> x /[!inE] /= Ekx; rewrite ifF; first by rewrite memNset.
    over.
  by rewrite integral0 ?adde0 ltey_eq fin_num_measure.
have int_f_E j S : measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)) (ge0_integral_setU _ mSIEj mSDEj)//.
    - by rewrite setUIDK; exact: (measurable_funS measurableT).
    - by apply/disj_set2P; rewrite setDE setIACA setICr setI0.
  rewrite /f_ -(eq_integral _ (g_ j)).
    by move=> x /[!inE] SIEjx; rewrite /f_ ifT// inE; exact: (@subIsetr _ S).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)).
    move=> A mA; rewrite subsetI => -[_ ?]; rewrite /mu_ /=.
    by rewrite /mfrestr /mrestr setIidl.
  rewrite -int_gE; first exact: measurableI.
  under eq_integral.
    move=> x; rewrite inE setDE /= => -[_ Ejx].
    rewrite ifF; first by rewrite memNset.
    over.
  by rewrite integral0 adde0 /nu_/= /mfrestr /mrestr -setIA setIid.
pose f x : \bar R := \sum_(j <oo) f_ j x.
have int_f_nuT : \int[mu]_x f x = nu setT.
  rewrite integral_nneseries//.
  transitivity (\sum_(n <oo) nu (E n)).
    by apply: eq_eseriesr => i _; rewrite int_f_E// setTI.
  rewrite -UET measure_bigcup//.
  by apply: eq_eseriesl => // x; rewrite in_setT.
have mf : measurable_fun setT f by exact: ge0_emeasurable_sum.
have fi : mu.-integrable setT f.
  apply/integrableP; split => //.
  under eq_integral do (rewrite gee0_abs; first exact: nneseries_ge0).
  by rewrite int_f_nuT ltey_eq fin_num_measure.
have ae_f := integrable_ae measurableT fi.
pose f' x := if f x \is a fin_num then f x else 0.
have ff' : ae_eq mu setT f f'.
  case: ae_f => N [mN N0 fN]; exists N; split => //.
  apply: subset_trans fN; apply: subsetC => z/= /(_ I) fz _.
  by rewrite /f' fz.
have mf' : measurable_fun setT f'.
  apply: measurable_fun_ifT => //; apply: (measurable_fun_bool true) => /=.
  by have := emeasurable_fin_num measurableT mf; rewrite setTI.
exists f'; split.
- by move=> t; rewrite /f'; case: ifPn => // ?; exact: nneseries_ge0.
- by move=> t; rewrite /f'; case: ifPn.
- apply/integrableP; split => //; apply/abse_integralP => //.
  move/ae_eq_integral : (ff') => /(_ measurableT mf) <-//.
  by apply/abse_integralP => //; move/integrableP : fi => [].
have nuf A : d.-measurable A -> nu A = \int[mu]_(x in A) f x.
  move=> mA; rewrite integral_nneseries//.
    by move=> n; exact: measurable_funTS.
  rewrite nneseries_esum; first by move=> m _; rewrite integral_ge0.
  under eq_esum do rewrite int_f_E//.
  rewrite -nneseries_esum.
    by move=> n; rewrite measure_ge0//; exact: measurableI.
  rewrite (@eq_eseriesl _ _ (fun x => x \in [set: nat])).
    by move=> x; rewrite in_setT.
  rewrite -measure_bigcup//.
  - by move=> i _; exact: measurableI.
  - exact: trivIset_setIl.
  - by rewrite -setI_bigcupr UET setIT.
move=> A mA; rewrite nuf ?inE//; apply: ae_eq_integral => //.
- exact/measurable_funTS.
- exact/measurable_funTS.
- exact: ae_eq_subset ff'.
Qed.

End radon_nikodym_sigma_finite.

Module Radon_Nikodym_SigmaFinite.
Section radon_nikodym_sigma_finite_def.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).

Definition f : T -> \bar R :=
  match pselect (nu `<< mu) with
  | left nu_mu => sval (cid (radon_nikodym_sigma_finite nu_mu))
  | right _ => cst -oo
  end.

Lemma f_ge0 : nu `<< mu -> forall x, 0 <= f x.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_fin_num : nu `<< mu -> forall x, f x \is a fin_num.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_integrable : nu `<< mu -> mu.-integrable [set: T] f.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

Lemma f_integral : nu `<< mu -> forall A, measurable A ->
    nu A = \int[mu]_(x in A) f x.
Proof. by rewrite /f; case: pselect => // numu _; case: cid => x []. Qed.

End radon_nikodym_sigma_finite_def.

Section integrableM.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).
Hypothesis numu : nu `<< mu.
Implicit Types f : T -> \bar R.

Local Notation "'d nu '/d mu" := (f nu mu).

Import HBNNSimple.

Lemma change_of_variables f E : (forall x, 0 <= f x) ->
    measurable E -> measurable_fun E f ->
  \int[mu]_(x in E) (f x * ('d nu '/d mu) x) = \int[nu]_(x in E) f x.
Proof.
move=> f0 mE mf; set g := 'd nu '/d mu.
pose h := nnsfun_approx mE mf.
have -> : \int[nu]_(x in E) f x =
    lim (\int[nu]_(x in E) (EFin \o h n) x @[n --> \oo]).
  have fE x : E x -> f x = lim ((EFin \o h n) x @[n --> \oo]).
    by move=> Ex; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  under eq_integral => x /[!inE] /fE -> //.
  apply: monotone_convergence => //.
  - move=> n; apply/measurable_EFinP.
    by apply: (measurable_funS measurableT) => //; exact/measurable_funP.
  - by move=> n x Ex //=; rewrite lee_fin.
  - by move=> x Ex a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
have -> : \int[mu]_(x in E) (f \* g) x =
    lim (\int[mu]_(x in E) ((EFin \o h n) \* g) x @[n --> \oo]).
  have fg x : E x -> f x * g x = lim (((EFin \o h n) \* g) x @[n --> \oo]).
    by move=> Ex; apply/esym/cvg_lim => //; apply: cvgeZr;
      [exact: f_fin_num|exact: cvg_nnsfun_approx].
  under eq_integral => x /[!inE] /fg -> //.
  apply: monotone_convergence => [//| | |].
  - move=> n; apply/emeasurable_funM; apply/measurable_funTS.
      exact/measurable_EFinP.
    exact: measurable_int (f_integrable _).
  - by move=> n x Ex /=; rewrite mule_ge0 ?lee_fin ?f_ge0.
  - by move=> x Ex a b ab/=; rewrite lee_wpmul2r ?lee_fin ?f_ge0//; exact/lefP/nd_nnsfun_approx.
suff suf n : \int[mu]_(x in E) ((EFin \o h n) x * g x) =
    \int[nu]_(x in E) (EFin \o h n) x.
  by under eq_fun do rewrite suf.
transitivity (\int[nu]_(x in E)
   (\sum_(y \in range (h n)) (y * \1_(h n @^-1` [set y]) x)%:E)); last first.
  by apply: eq_integral => t tE; rewrite /= fimfunE -fsumEFin.
have indich m r : measurable_fun E (fun x => (r * \1_(h m @^-1` [set r]) x)%:E).
  by apply: (measurable_comp measurableT) => //; exact: measurable_funM.
rewrite ge0_integral_fsum//; first by move=> m y Ey; exact: nnfun_muleindic_ge0.
transitivity (\int[mu]_(x in E) (\sum_(y \in range (h n))
    (y * \1_(h n @^-1` [set y]) x)%:E * g x)).
  under [RHS]eq_integral => x xE.
    rewrite -ge0_mule_fsuml => [y|]; first exact: nnfun_muleindic_ge0.
    rewrite fsumEFin // -(fimfunE _ x); over.
  by [].
rewrite ge0_integral_fsum//.
  - move=> y; apply: emeasurable_funM => //; apply: measurable_funTS.
    exact: measurable_int (f_integrable _).
  - by move=> m y Ey; rewrite mule_ge0 ?f_ge0// nnfun_muleindic_ge0.
apply: eq_fsbigr => r rhn.
under [RHS]eq_integral do rewrite EFinM.
rewrite integralZl_indic_nnsfun => //.
under eq_integral do rewrite EFinM -muleA.
rewrite ge0_integralZl//.
- apply: emeasurable_funM; first exact/measurable_EFinP.
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
- by move=> t Et; rewrite mule_ge0 ?lee_fin ?f_ge0.
- by move: rhn; rewrite inE => -[t _ <-]; rewrite lee_fin.
under eq_integral do rewrite muleC.
rewrite (eq_integral (g \_ (h n @^-1` [set r]))).
  by move=> x xE; rewrite epatch_indic.
by rewrite -integral_mkcondr -f_integral// integral_indic// setIC.
Qed.

Lemma integrableM f E : (forall x, 0 <= f x) -> measurable E ->
  nu.-integrable E f -> mu.-integrable E (f \* 'd nu '/d mu).
Proof.
move=> f0 mE intEf; apply/integrableP; split.
  apply: emeasurable_funM; first exact: (measurable_int nu).
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
under eq_integral.
  move=> x _; rewrite gee0_abs.
    by apply: mule_ge0=> //; exact: f_ge0.
  over.
rewrite change_of_variables//; first exact: (measurable_int nu).
by move/integrableP : intEf=> [mf +]; under eq_integral do rewrite gee0_abs//.
Qed.

End integrableM.

Section chain_rule.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (la : {sigma_finite_measure set T -> \bar R})
          (mu : {finite_measure set T -> \bar R}).

Local Notation "'d nu '/d mu" := (f nu mu).

Lemma chain_rule E : nu `<< mu -> mu `<< la -> measurable E ->
  ae_eq la E ('d nu '/d la) ('d nu '/d mu \* 'd mu '/d la).
Proof.
move=> numu mula mE.
have mf : measurable_fun E ('d nu '/d mu).
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
apply: integral_ae_eq => //.
- apply: (integrableS measurableT) => //; apply: f_integrable.
  exact: null_dominates_trans numu mula.
- apply: emeasurable_funM => //.
  exact/measurable_funTS/(measurable_int _ (f_integrable _)).
move=> A AE mA; rewrite change_of_variables//.
- exact: f_ge0.
- exact: measurable_funS mf.
- by rewrite -!f_integral//; exact: null_dominates_trans numu mula.
Qed.

End chain_rule.
End Radon_Nikodym_SigmaFinite.

Section radon_nikodym.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).

Local Lemma Radon_Nikodym0 : nu `<< mu ->
  exists f : T -> \bar R, [/\ (forall x, f x \is a fin_num),
    mu.-integrable [set: T] f &
    forall A, measurable A -> nu A = \int[mu]_(x in A) f x].
Proof.
move=> nu_mu; have [P [N nuPN]] := Hahn_decomposition nu.
have [fp [fp0 fpfin intfp fpE]] := @radon_nikodym_sigma_finite _ _ _ mu
  (jordan_pos nuPN) (jordan_pos_dominates nuPN nu_mu).
have [fn [fn0 fnfin intfn fnE]] := @radon_nikodym_sigma_finite _ _ _ mu
  (jordan_neg nuPN) (jordan_neg_dominates nuPN nu_mu).
exists (fp \- fn); split; first by move=> x; rewrite fin_numB// fpfin fnfin.
  exact: integrableB.
move=> E mE; rewrite [LHS](jordan_decomp nuPN mE)// integralB//;
  [exact: (integrableS measurableT)..|].
by rewrite -fpE ?inE// -fnE ?inE//= /cadd/= cscaleN1.
Qed.

Definition Radon_Nikodym : T -> \bar R :=
  match pselect (nu `<< mu) with
  | left nu_mu => sval (cid (Radon_Nikodym0 nu_mu))
  | right _ => cst -oo
  end.

Lemma Radon_NikodymE (numu : nu `<< mu) :
  Radon_Nikodym = sval (cid (Radon_Nikodym0 numu)).
Proof.
rewrite /= /Radon_Nikodym; case: pselect => //= numu'.
by congr (sval (cid (Radon_Nikodym0 _))); exact: Prop_irrelevance.
Qed.

Lemma Radon_Nikodym_fin_num x : nu `<< mu ->
  Radon_Nikodym x \is a fin_num.
Proof. by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? []. Qed.

Lemma Radon_Nikodym_integrable : nu `<< mu ->
  mu.-integrable [set: T] Radon_Nikodym.
Proof. by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? []. Qed.

Lemma Radon_Nikodym_integral A : nu `<< mu ->
  measurable A -> nu A = \int[mu]_(x in A) Radon_Nikodym x.
Proof.
by move=> numu; rewrite (Radon_NikodymE numu); case: cid => ? [? ?]; exact.
Qed.

End radon_nikodym.
Notation "'d nu '/d mu" := (Radon_Nikodym nu mu) : charge_scope.

Local Open Scope charge_scope.

#[global] Hint Extern 0 (_.-integrable setT ('d _ '/d _)) =>
  solve [apply: Radon_Nikodym_integrable] : core.
#[global] Hint Extern 0 (measurable_fun setT ('d _ '/d _)) =>
  solve [apply: measurable_int; exact: Radon_Nikodym_integrable] : core.

Section Radon_Nikodym_charge_of_finite_measure.
Context d (T : measurableType d) (R : realType).
Variables (nu : {finite_measure set T -> \bar R})
          (mu : {sigma_finite_measure set T -> \bar R}).
Hypothesis numu : nu `<< mu.
Implicit Types f : T -> \bar R.

Lemma ae_eq_Radon_Nikodym_SigmaFinite E : measurable E ->
  ae_eq mu E (Radon_Nikodym_SigmaFinite.f nu mu)
             ('d (charge_of_finite_measure nu) '/d mu).
Proof.
move=> mE; apply: integral_ae_eq => //.
- apply: (integrableS measurableT) => //.
  exact: Radon_Nikodym_SigmaFinite.f_integrable.
- exact: measurable_funTS.
- move=> A AE mA; rewrite -Radon_Nikodym_integral//.
  by rewrite -Radon_Nikodym_SigmaFinite.f_integral.
Qed.

Lemma Radon_Nikodym_change_of_variables f E : measurable E ->
    nu.-integrable E f ->
  \int[mu]_(x in E) (f x * ('d (charge_of_finite_measure nu) '/d mu) x) =
  \int[nu]_(x in E) f x.
Proof.
move=> mE mf; rewrite -[in RHS](funeposBneg f) integralB //.
  - exact: integrable_funepos.
  - exact: integrable_funeneg.
transitivity (\int[mu]_(x in E) (f x * Radon_Nikodym_SigmaFinite.f nu mu x)).
  apply: ae_eq_integral => //.
  - apply: emeasurable_funM => //; first exact: measurable_int mf.
    exact: measurable_funTS.
  - apply: emeasurable_funM => //; first exact: measurable_int mf.
    apply: measurable_funTS.
    exact: measurable_int (Radon_Nikodym_SigmaFinite.f_integrable _).
  - apply: ae_eqe_mul2l.
    exact/ae_eq_sym/ae_eq_Radon_Nikodym_SigmaFinite.
rewrite -[in LHS](funeposBneg f).
under [in LHS]eq_integral => x xE. rewrite muleBl.
  - exact: Radon_Nikodym_SigmaFinite.f_fin_num.
  - exact: add_def_funeposneg.
  over.
rewrite [in LHS]integralB //.
- apply: Radon_Nikodym_SigmaFinite.integrableM => //.
  exact: integrable_funepos.
- apply: Radon_Nikodym_SigmaFinite.integrableM => //.
  exact: integrable_funeneg.
congr (_ - _) ; rewrite Radon_Nikodym_SigmaFinite.change_of_variables//;
  apply: measurable_int; first exact: integrable_funepos mf.
exact: integrable_funeneg mf.
Qed.

End Radon_Nikodym_charge_of_finite_measure.

Section radon_nikodym_lemmas.
Context d (T : measurableType d) (R : realType).
Implicit Types (nu : {charge set T -> \bar R})
               (mu : {sigma_finite_measure set T -> \bar R}).

Lemma Radon_Nikodym_cscale mu nu c E : measurable E -> nu `<< mu ->
  ae_eq mu E ('d (cscale c nu) '/d mu) (fun x => c%:E * 'd nu '/d mu x).
Proof.
move=> mE numu; apply: integral_ae_eq => [//| | |A AE mA].
- apply: (integrableS measurableT) => //.
  exact/Radon_Nikodym_integrable/dominates_cscalel.
- exact/measurable_funTS/emeasurable_funM.
- rewrite integralZl//.
    by apply: (integrableS measurableT) => //; exact: Radon_Nikodym_integrable.
  rewrite -Radon_Nikodym_integral => //; first exact: dominates_cscalel.
  by rewrite -Radon_Nikodym_integral.
Qed.

Lemma Radon_Nikodym_cadd mu nu0 nu1 E : measurable E ->
  nu0 `<< mu -> nu1 `<< mu ->
  ae_eq mu E ('d (cadd nu0 nu1) '/d mu) ('d nu0 '/d mu \+ 'd nu1 '/d mu).
Proof.
move=> mE nu0mu nu1mu; apply: integral_ae_eq => [//| | |A AE mA].
- apply: (integrableS measurableT) => //.
  by apply: Radon_Nikodym_integrable => /=; exact: dominates_cadd.
- by apply: measurable_funTS => //; exact: emeasurable_funD.
- rewrite integralD //; [exact: integrableS (Radon_Nikodym_integrable _)..|].
  rewrite -Radon_Nikodym_integral //=; first exact: dominates_cadd.
  by rewrite -Radon_Nikodym_integral // -Radon_Nikodym_integral.
Qed.

End radon_nikodym_lemmas.

Section Radon_Nikodym_chain_rule.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R})
          (la : {sigma_finite_measure set T -> \bar R})
          (mu : {finite_measure set T -> \bar R}).

Lemma Radon_Nikodym_chain_rule : nu `<< mu -> mu `<< la ->
  ae_eq la setT ('d nu '/d la)
                ('d nu '/d mu \* 'd (charge_of_finite_measure mu) '/d la).
Proof.
have [Pnu [Nnu nuPN]] := Hahn_decomposition nu.
move=> numu mula; have nula := null_dominates_trans numu mula.
apply: integral_ae_eq; [exact: measurableT| |exact: emeasurable_funM|].
- exact: Radon_Nikodym_integrable.
- move=> E _ mE.
  rewrite -Radon_Nikodym_integral// Radon_Nikodym_change_of_variables//.
  + by apply: (integrableS measurableT) => //; exact: Radon_Nikodym_integrable.
  + exact: Radon_Nikodym_integral.
Qed.

End Radon_Nikodym_chain_rule.
