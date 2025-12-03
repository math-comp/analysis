(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference topology ereal tvs normedtype.
From mathcomp Require Import sequences real_interval function_spaces esum.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import simple_functions measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_monotone_convergence.

(**md**************************************************************************)
(* # Theory of the Lebesgue integral for non-negative functions               *)
(*                                                                            *)
(* This file contains a formalization of the basic properties of the Lebesgue *)
(* integral for non-negative functions: linearity, order, union, subset, etc. *)
(* of the domain of integration, etc.                                         *)
(*                                                                            *)
(* About the naming convention: Lemmas about the Lebesgue integral often      *)
(* come in two flavors. They are either about non-negative, measurable        *)
(* functions or about integrable functions. In this file, lemmas are          *)
(* prefixed with `ge0_`, lemmas about integrable functions (file              *)
(* `lebesgue_integrable`) are not.                                            *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section eq_measure_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (D : set T).
Implicit Types m : {measure set T -> \bar R}.

Import HBNNSimple.

Let eq_measure_integral0 m2 m1 (f : T -> \bar R) :
  (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  [set sintegral m1 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]] `<=`
  [set sintegral m2 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]].
Proof.
move=> m12 _ [h hfD <-] /=; exists h => //; apply: eq_fsbigr => r _.
have [hrD|hrD] := pselect (h @^-1` [set r] `<=` D); first by rewrite m12.
suff : r = 0%R by move=> ->; rewrite !mul0e.
apply: contra_notP hrD => /eqP r0 t/= htr.
have := hfD t.
rewrite /patch/=; case: ifPn; first by rewrite inE.
move=> tD.
move: r0; rewrite -htr => ht0.
by rewrite le_eqVlt eqe (negbTE ht0)/= lte_fin// ltNge// fun_ge0.
Qed.

Lemma eq_measure_integral m2 m1 (f : T -> \bar R) :
    (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  \int[m1]_(x in D) f x = \int[m2]_(x in D) f x.
Proof.
move=> m12; rewrite /integral funepos_restrict funeneg_restrict.
by congr (ereal_sup _ - ereal_sup _); rewrite eqEsubset; split;
  apply: eq_measure_integral0 => A /m12 // /[apply].
Qed.

End eq_measure_integral.
Arguments eq_measure_integral {d T R D} m2 {m1 f}.

Section integral_measure_zero.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Let sintegral_measure_zero (f : T -> R) : sintegral mzero f = 0.
Proof. by rewrite sintegralE big1// => r _ /=; rewrite /mzero mule0. Qed.

Import HBNNSimple.

Lemma integral_measure_zero (D : set T) (f : T -> \bar R) :
  \int[mzero]_(x in D) f x = 0.
Proof.
have h g : (forall x, 0 <= g x) -> [set sintegral mzero h |
    h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= g x]] = [set 0].
  move=> g0; apply/seteqP; split => [_ [h/= Dt <-]|x -> /=].
    by rewrite sintegral_measure_zero.
  by exists (cst_nnsfun _ (@NngNum _ 0 (lexx _))).
rewrite integralE !ge0_integralE//= h ?ereal_sup1; last first.
  by move=> r; rewrite erestrict_ge0.
by rewrite h ?ereal_sup1 ?subee// => r; rewrite erestrict_ge0.
Qed.

End integral_measure_zero.

Lemma integral_set0 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : T -> \bar R) :
  (\int[mu]_(x in set0) f x = 0)%E.
Proof.
rewrite integral_mkcond integral0_eq// => x _.
by rewrite /restrict; case: ifPn => //; rewrite in_set0.
Qed.

Section ge0_integralZl_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> \bar R.
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.

Import HBNNSimple.

Lemma ge0_integralZl_EFin k : (0 <= k)%R ->
  \int[mu]_(x in D) (k%:E * f1 x) = k%:E * \int[mu]_(x in D) f1 x.
Proof.
rewrite integral_mkcond erestrict_scale [in RHS]integral_mkcond => k0.
set h1 := f1 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
pose g := nnsfun_approx measurableT mh1.
pose kg := fun n => scale_nnsfun (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ _ mu (fun x => k%:E * h1 x) kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu (scale_nnsfun (g n) k0))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (g n))).
    rewrite limeMl //; last first.
      by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx.
    by rewrite -(nd_ge0_integral_lim mu h10)// => [x m n mn|x];
      [exact/lefP/nd_nnsfun_approx|exact: cvg_nnsfun_approx].
  by under eq_fun do rewrite (sintegralrM mu k (g _)).
- by move=> t; rewrite mule_ge0.
- by move=> x m n mn; rewrite /kg ler_pM//; exact/lefP/nd_nnsfun_approx.
- move=> x.
  rewrite [X in X @ \oo --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
  exact/cvgeZl/cvg_nnsfun_approx.
Qed.

End ge0_integralZl_EFin.

Section ge0_linearityD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Import HBNNSimple.

Lemma ge0_integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
rewrite !(integral_mkcond D) erestrictD.
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
pose g1 := nnsfun_approx measurableT mh1.
pose g2 := nnsfun_approx measurableT mh2.
pose g12 := fun n => add_nnsfun (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ _ mu _ g12); last 3 first.
  - by move=> x; rewrite adde_ge0.
  - by apply: nondecreasing_seqD => // x m n mn;
      [exact/lefP/nd_nnsfun_approx|exact/lefP/nd_nnsfun_approx].
  - move=> x; rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E))//.
    apply: cvgeD => //; [|exact: cvg_nnsfun_approx..].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: h10|exact: h20].
under [_ \o _]eq_fun do rewrite sintegralD.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g2)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite limeD//; [
  by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx..|].
by rewrite ge0_adde_def => //; rewrite inE; apply: lime_ge; solve[
  (by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx) ||
  (by apply: nearW => n; exact: sintegral_ge0)].
Qed.

End ge0_linearityD.

Section ge0_integral_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_sum (s : seq I) :
  \int[mu]_(x in D) (\sum_(k <- s) f k x) =
  \sum_(k <- s) \int[mu]_(x in D) (f k x).
Proof.
elim: s => [|h t ih].
  by (under eq_fun do rewrite big_nil); rewrite big_nil integral0.
rewrite big_cons /= -ih -ge0_integralD//.
- by apply: eq_integral => x Dx; rewrite big_cons.
- by move=> *; exact: f0.
- by move=> *; apply: sume_ge0 => // k _; exact: f0.
- exact: emeasurable_sum.
Qed.

End ge0_integral_sum.

Section ge0_integral_fsum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : choiceType) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_fsum (A : set I) : finite_set A ->
  \int[mu]_(x in D) (\sum_(k \in A) f k x) =
  \sum_(k \in A) \int[mu]_(x in D) f k x.
Proof.
move=> fs; rewrite fsbig_finite//= -ge0_integral_sum//.
by apply: eq_integral => x xD; rewrite fsbig_finite.
Qed.

End ge0_integral_fsum.

Section integral_nneseries.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma integral_nneseries : \int[mu]_(x in D) (\sum_(n <oo) f n x) =
                           \sum_(n <oo) (\int[mu]_(x in D) (f n x)).
Proof.
rewrite monotone_convergence //.
- by rewrite -lim_mkord; under eq_fun do rewrite ge0_integral_sum// big_mkord.
- by move=> n; exact: emeasurable_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_nneseries.

(**md Generalization of `ge0_integralZl_EFin` to a constant potentially $+\infty$
   using the monotone convergence theorem: *)
Section ge0_integralZ.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.
Implicit Type k : \bar R.

Lemma ge0_integralZl k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (k * f x) = k * \int[mu]_(x in D) (f x).
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralZl_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by apply: measurable_funeM.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g ^~ x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => limn (g^~ x).
transitivity (\int[mu]_(x in D) limn (g^~ x)).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0 (f x).
  - rewrite gt0_mulye//; apply/cvgeyPgey; near=> M.
    have M0 : (0 <= M)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|_|//]; last first.
      by exists 1%N => // m /= m0; rewrite mulry gtr0_sg// ?ltr0n// mul1e leey.
    near=> n; rewrite lee_fin -ler_pdivrMr//.
    near: n; exists (truncn (M / r)).+1 => // m /= Mrm.
    by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
  - rewrite lt0_mulye//; apply/cvgeNyPleNy; near=> M;
    have M0 : (M <= 0)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|//|_]; last first.
      by exists 1%N => // m /= m0; rewrite mulrNy gtr0_sg// ?ltr0n// mul1e leNye.
    near=> n; rewrite lee_fin -ler_ndivrMr//.
    near: n; exists (truncn (M / r)).+1 => // m /= Mrm.
    by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
  - rewrite -fx0 mule0 /g -fx0.
    under eq_fun do rewrite mule0/=. (*TODO: notation broken*)
    exact: cvg_cst.
rewrite (monotone_convergence mu mD mg g0 nd_g).
under eq_fun do rewrite /g ge0_integralZl_EFin//.
have : 0 <= \int[mu]_(x in D) f x by exact: integral_ge0.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  by rewrite mule0; under eq_fun do rewrite mule0; rewrite lim_cst.
rewrite gt0_mulye//; apply/cvg_lim => //; apply/cvgeyPgey; near=> M.
have M0 : (0 <= M)%R by [].
near=> n; have [ifoo|] := ltP (\int[mu]_(x in D) f x) +oo; last first.
  rewrite leye_eq => /eqP ->; rewrite mulry muleC gt0_mulye ?leey//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (\int[mu]_(x in D) f x)); last first.
  by rewrite fin_numElt ifoo (le_lt_trans _ if_gt0).
rewrite -lee_pdivrMr//; last first.
  by move: if_gt0 ifoo; case: (\int[mu]_(x in D) f x).
near: n.
exists (truncn (M * (fine (\int[mu]_(x in D) f x))^-1)).+1 => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
by rewrite lee_fin ltW// truncnS_gt.
Unshelve. all: by end_near. Qed.

Lemma ge0_integralZr k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (f x * k) = \int[mu]_(x in D) (f x) * k.
Proof.
move=> f0 k0; under eq_integral do rewrite muleC.
by rewrite ge0_integralZl// muleC.
Qed.

End ge0_integralZ.

Section integralZl_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralZl_indic (f : R -> set T) (k : R) :
    ((k < 0)%R -> f k = set0) -> measurable (f k) ->
  \int[m]_(x in D) (k * \1_(f k) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f k) x)%:E.
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite integral0_eq//; last by move=> x _; rewrite fk0// indic0 mulr0.
  by rewrite integral0_eq ?mule0// => x _; rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl//; exact/measurable_EFinP.
Qed.

Import HBNNSimple.

Lemma integralZl_indic_nnsfun (f : {nnsfun T >-> R}) (k : R) :
  \int[m]_(x in D) (k * \1_(f @^-1` [set k]) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f @^-1` [set k]) x)%:E.
Proof.
rewrite (@integralZl_indic (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

End integralZl_indic.
Arguments integralZl_indic {d T R m D} mD f.

Section ge0_integral_mscale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (k : {nonneg R}) (f : T -> \bar R).

Let integral_mscale_indic E : measurable E ->
  \int[mscale k m]_(x in D) (\1_E x)%:E =
  k%:num%:E * \int[m]_(x in D) (\1_E x)%:E.
Proof. by move=> ?; rewrite !integral_indic. Qed.

Import HBNNSimple.

Let integral_mscale_nnsfun (h : {nnsfun T >-> R}) :
  \int[mscale k m]_(x in D) (h x)%:E = k%:num%:E * \int[m]_(x in D) (h x)%:E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralZl//; last 2 first.
  - by apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> x _; rewrite lee_fin.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/measurable_EFinP; do 2 apply/measurableT_comp => //.
  - by move=> n x _; rewrite EFinM mule_ge0// nnfun_muleindic_ge0.
apply: eq_fsbigr => r _; rewrite ge0_integralZl//.
- by rewrite !integralZl_indic_nnsfun//= integral_mscale_indic// muleCA.
- exact/measurable_EFinP/measurableT_comp.
- by move=> t _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma ge0_integral_mscale (mf : measurable_fun D f) :
    (forall x, D x -> 0 <= f x) ->
  \int[mscale k m]_(x in D) f x = k%:num%:E * \int[m]_(x in D) f x.
Proof.
move=> f0; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[mscale k m]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//=.
  - apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //=.
    exact: cvg_nnsfun_approx.
  - by move=> n; apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite (_ : \int[m]_(x in D) _ =
    limn (fun n => \int[m]_(x in D) (f_ n x)%:E)); last first.
  rewrite -monotone_convergence//=.
  - apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //.
    exact: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite -limeMl//.
  by congr (limn _); apply/funext => n /=; rewrite integral_mscale_nnsfun.
apply/ereal_nondecreasing_is_cvgn => a b ab; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- exact/measurable_EFinP/measurable_funTS.
- by move=> x _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

End ge0_integral_mscale.

Section integralN.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integralN D (f : T -> \bar R) :
  \int[mu]_(x in D) f^\+ x +? (- (\int[mu]_(x in D) f^\- x)) ->
  \int[mu]_(x in D) - f x = - (\int[mu]_(x in D) f x).
Proof.
have [f_fin _|] := boolP (\int[mu]_(x in D) f^\- x \is a fin_num).
  rewrite integralE// [in RHS]integralE// fin_num_oppeD ?fin_numN// oppeK addeC.
  by rewrite funenegN funeposN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -leeNy_eq; apply/negP.
  by rewrite -ltNge (lt_le_trans _ (integral_ge0 _ _)).
rewrite nfoo adde_defEninfty -leye_eq -ltNge ltey_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE [in RHS]integralE funeposN nfoo [in RHS]addeC/= funenegN.
  by rewrite addye// eqe_oppLR/= (andP (eqbLR (fin_numE _) f_fin)).2.
by rewrite integralE// [in RHS]integralE// funeposN funenegN nfoo pfoo.
Qed.

Lemma integral_ge0N (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) - f x = - (\int[mu]_(x in D) f x).
Proof.
move=> f0; rewrite integralN // (eq_integral _ _ (ge0_funenegE _))// integral0.
by rewrite oppe0 fin_num_adde_defl.
Qed.

End integralN.

Section integral_cst.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Variables (f : T -> \bar R) (D : set T) (mD : measurable D).

Lemma sintegral_EFin_cst (x : {nonneg R}) :
  sintegral mu (cst x%:num \_ D) = x%:num%:E * mu D.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; x%:num])/=.
- have [->|x0] := eqVneq x%:num 0%R; first by rewrite setUid fsbig_set1 !mul0e.
  rewrite fsbigU0//=; last by move=> y [->]/esym; apply/eqP.
  rewrite !fsbig_set1 mul0e add0e preimage_restrict//.
  by rewrite ifN ?set0U ?setIidl//= notin_setE => /esym; exact/eqP.
- by move=> y [t _ <-] /=; rewrite /patch; case: ifPn; [right|left].
- by move=> y [_ /=/preimage10->]; rewrite measure0 mule0.
Qed.

Import HBNNSimple.

Local Lemma integral_cstr r : \int[mu]_(x in D) r%:E = r%:E * mu D.
Proof.
wlog r0 : r / (0 <= r)%R.
  move=> h; have [|r0] := leP 0%R r; first exact: h.
  rewrite -[in RHS](opprK r) EFinN mulNe -h ?oppr_ge0; last exact: ltW.
  rewrite -integral_ge0N//; last by move=> t ?; rewrite /= lee_fin oppr_ge0 ltW.
  by under [RHS]eq_integral do rewrite /= opprK.
rewrite (eq_integral (EFin \o cst_nnsfun T (NngNum r0)))//.
by rewrite integral_nnsfun// sintegral_EFin_cst.
Qed.

Local Lemma integral_csty : mu D != 0 -> \int[mu]_(x in D) (cst +oo) x = +oo.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => limn (g^~ t)) = cst +oo.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/cvgeryP/cvgryPge => M; exists (truncn M).+1 => //= m/= Mn.
  by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
rewrite monotone_convergence //.
- under [in LHS]eq_fun do rewrite integral_cstr.
  apply/cvg_lim => //; apply/cvgeyPge => M.
  have [muDoo|muDoo] := ltP (mu D) +oo; last first.
    exists 1%N => // m /= m0; move: muDoo; rewrite leye_eq => /eqP ->.
    by rewrite mulry gtr0_sg ?mul1e ?leey// ltr0n.
  exists (truncn (M / fine (mu D))).+1 => // m /=.
  rewrite -lez_nat => MDm; rewrite -(@fineK _ (mu D)) ?ge0_fin_numE//.
  rewrite -lee_pdivrMr; last by rewrite fine_gt0// lt0e muD0 measure_ge0.
  by rewrite lee_fin (le_trans (ltW (truncnS_gt _)))// ler_nat.
- by move=> n; exact: measurable_cst.
- by move=> n x Dx; rewrite lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.

Local Lemma integral_cstNy : mu D != 0 -> \int[mu]_(x in D) (cst -oo) x = -oo.
Proof.
by move=> ?; rewrite (eq_integral (\- cst +oo)) ?integral_ge0N/= ?integral_csty.
Qed.

End integral_cst.

Section ge0_transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (mu : {measure set X -> \bar R}).
Let mphi_mixin := isMeasurableFun.Build _ _ _ _ _ mphi.
Let mphi_pack : {mfun _ >-> _} := HB.pack phi mphi_mixin.

Import HBNNSimple.

Lemma ge0_integral_pushforward D (f : Y -> \bar R) :
  measurable D -> measurable_fun D f -> {in D, forall y, 0 <= f y} ->
  \int[pushforward mu phi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD mf f0.
have mphiD : measurable (phi @^-1` D).
  by rewrite -(setTI (_ @^-1` _)); exact: (measurable_funP mphi_pack).
pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[pushforward mu phi]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - apply: eq_integral => y /[!inE] yD; apply/esym/cvg_lim => //.
    by apply: cvg_nnsfun_approx=> // *; apply: f0; rewrite inE.
  - by move=> n; exact/measurable_EFinP/measurable_funP.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite [X in limn X](_ : _ =
    (fun n => \int[mu]_(x in phi @^-1` D) (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; do 2 apply: measurableT_comp=> //.
      exact: (measurable_funP mphi_pack).
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  apply: eq_integral => x /[!inE] phiDx /=; apply/cvg_lim => //.
  by apply: cvg_nnsfun_approx=> // y Dy; apply: f0; rewrite inE.
apply/funext => n.
have mfnphi r : measurable (f_ n @^-1` [set r] \o phi).
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k \in range (f_ n))
    \int[mu]_(x in phi @^-1` D) (k * \1_((f_ n @^-1` [set k]) \o phi) x)%:E).
  under eq_integral do rewrite fimfunE -fsumEFin//.
  rewrite ge0_integral_fsum//; last 2 first.
  - by move=> y; exact/measurable_EFinP/measurable_funM.
  - by move=> y x _; rewrite nnfun_muleindic_ge0.
  apply: eq_fsbigr => r _; rewrite integralZl_indic_nnsfun// integral_indic//=.
  rewrite (integralZl_indic _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _); rewrite [RHS]integral_indic.
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_fsum//.
- by apply: eq_integral => x _; rewrite fsumEFin// -fimfunE.
- by move=> r; exact/measurable_EFinP/measurable_funM.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

End ge0_transfer.

Section integral_dirac.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (a : T) (R : realType).
Variables (D : set T) (mD : measurable D).

Import HBNNSimple.

Let ge0_integral_dirac (f : T -> \bar R) (mf : measurable_fun D f)
    (f0 : forall x, D x -> 0 <= f x) :
  D a -> \int[\d_a]_(x in D) (f x) = f a.
Proof.
move=> Da; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[\d_ a]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => x /set_mem Dx; apply/esym/cvg_lim => //; apply: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
apply/funext => n.
under eq_integral do rewrite fimfunE// -fsumEFin//.
rewrite ge0_integral_fsum//.
- under eq_fsbigr do rewrite integralZl_indic_nnsfun//.
  rewrite /= (fsbigD1 (f_ n a))//=; last by exists a.
  rewrite integral_indic//= diracE mem_set// mule1.
  rewrite fsbig1 ?adde0// => r /= [_ rfna].
  rewrite integral_indic//= diracE memNset ?mule0//=.
  by apply/not_andP; left; exact/nesym.
- by move=> r; exact/measurable_EFinP/measurableT_comp.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma integral_dirac (f : T -> \bar R) (mf : measurable_fun D f) :
  \int[\d_ a]_(x in D) f x = \d_a D * f a.
Proof.
have [/[!inE] aD|aD] := boolP (a \in D).
  rewrite integralE ge0_integral_dirac//; last exact/measurable_funepos.
  rewrite ge0_integral_dirac//; last exact/measurable_funeneg.
  by rewrite [in RHS](funeposneg f) diracE mem_set// mul1e.
rewrite diracE (negbTE aD) mul0e -(integral_measure_zero D f)//.
apply: eq_measure_integral => //= S mS DS; rewrite /dirac indicE memNset//.
by move=> /DS/mem_set; exact/negP.
Qed.

End integral_dirac.

Lemma summable_integral_dirac {R : realType} (a : nat -> \bar R) : summable setT a ->
  (\sum_(n <oo) `|\int[\d_ n]_x a x| < +oo)%E.
Proof.
move=> sa.
apply: (@le_lt_trans _ _ (\sum_(i <oo) `|fine (a i)|%:E))%E.
  apply: lee_nneseries => // n _; rewrite integral_dirac//.
  move: (@summable_pinfty _ _ _ _ sa n Logic.I).
  by case: (a n) => //= r _; rewrite indicE/= mem_set// mul1r.
move: (sa); rewrite /summable -fun_true -nneseries_esum//; apply: le_lt_trans.
by apply: lee_nneseries => // n _ /=; case: (a n) => //; rewrite leey.
Qed.

Section integral_measure_sum_nnsfun.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m_ : {measure set T -> \bar R}^nat) (N : nat).
Let m := msum m_ N.

Let integral_measure_sum_indic (E D : set T) (mE : measurable E)
    (mD : measurable D) :
  \int[m]_(x in E) (\1_D x)%:E = \sum_(n < N) \int[m_ n]_(x in E) (\1_D x)%:E.
Proof.
rewrite integral_indic//= /msum/=; apply: eq_bigr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Let integralT_measure_sum (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n < N) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n < N) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_sum_indic//.
  by rewrite ge0_sume_distrr// => n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= exchange_big/=; apply: eq_bigr => i _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

Lemma integral_measure_sum_nnsfun (D : set T) (mD : measurable D)
  (f : {nnsfun T >-> R}) :
  \int[m]_(x in D) (f x)%:E = \sum_(n < N) \int[m_ n]_(x in D) (f x)%:E.
Proof.
rewrite integral_mkcond.
transitivity (\int[m]_x (proj_nnsfun f mD x)%:E).
  by apply: eq_integral => t _ /=; rewrite /patch mindicE;
    case: ifPn => // tD; rewrite ?mulr1 ?mulr0.
rewrite integralT_measure_sum; apply: eq_bigr => i _.
rewrite [RHS]integral_mkcond; apply: eq_integral => t _.
rewrite /= /patch /mindic indicE.
by case: (boolP (t \in D)) => tD; rewrite ?mulr1 ?mulr0.
Qed.

End integral_measure_sum_nnsfun.

Section integral_measure_add_nnsfun.
Import HBNNSimple.

Lemma integral_measure_add_nnsfun d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  (\int[measure_add m1 m2]_(x in D) (f x)%:E =
   \int[m1]_(x in D) (f x)%:E + \int[m2]_(x in D) (f x)%:E)%E.
Proof.
rewrite /measureD integral_measure_sum_nnsfun// 2!big_ord_recl/= big_ord0.
by rewrite adde0.
Qed.

End integral_measure_add_nnsfun.

Section integral_mfun_measure_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.

Import HBNNSimple.

Lemma ge0_integral_measure_sum (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
    (forall x, D x -> 0 <= f x) -> measurable_fun D f -> forall N,
  \int[msum m_ N]_(x in D) f x = \sum_(n < N) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf; pose f_ := nnsfun_approx mD mf.
elim => [|N ih]; first by rewrite big_ord0 msum_mzero integral_measure_zero.
rewrite big_ord_recr/= -ih.
rewrite (_ : _ m_ N.+1 = measure_add (msum m_ N) (m_ N)); last first.
  by apply/funext => A; rewrite measure_addE /msum/= big_ord_recr.
have mf_ n : measurable_fun D (fun x => (f_ n x)%:E).
  exact/measurable_funTS/measurable_EFinP.
have f_ge0 n x : D x -> 0 <= (f_ n x)%:E by move=> Dx; rewrite lee_fin.
have cvg_f_ (m : {measure set T -> \bar R}) :
    cvgn (fun x => \int[m]_(x0 in D) (f_ x x0)%:E).
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: ge0_le_integral => //; first exact: f_ge0.
  by move=> t Dt; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n =>
    \int[measure_add (msum m_ N) (m_ N)]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//; last first.
    by move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => t /[!inE] Dt; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n =>
  \int[msum m_ N]_(x in D) (f_ n x)%:E + \int[m_ N]_(x in D) (f_ n x)%:E)).
  by congr (limn _); apply/funext => n; by rewrite integral_measure_add_nnsfun.
rewrite limeD//; do?[exact: cvg_f_]; last first.
  by apply: ge0_adde_def; rewrite inE; apply: lime_ge => //; do?[exact: cvg_f_];
      apply: nearW => n;  apply: integral_ge0 => //; exact: f_ge0.
by congr (_ + _); (rewrite -monotone_convergence//; [
    apply: eq_integral => t /[!inE] Dt; apply/cvg_lim => //; exact: cvg_nnsfun_approx |
    move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx]).
Qed.

End integral_mfun_measure_sum.

Lemma ge0_integral_measure_add d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> measurable_fun D f ->
  (\int[measure_add m1 m2]_(x in D) f x =
   \int[m1]_(x in D) f x + \int[m2]_(x in D) f x)%E.
Proof.
move=> f0 mf; rewrite /measureD ge0_integral_measure_sum// 2!big_ord_recl/=.
by rewrite big_ord0 adde0.
Qed.

Section integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Let integral_measure_series_indic (D : set T) (mD : measurable D) :
  \int[m]_x (\1_D x)%:E = \sum_(n <oo) \int[m_ n]_x (\1_D x)%:E.
Proof.
rewrite integral_indic// setIT /m/= /mseries; apply: eq_eseriesr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Lemma integral_measure_series_nnsfun (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n <oo) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n <oo) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_series_indic// nneseriesZl//.
  by move=> n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= -nneseries_sum; last first.
  move=> r j _.
  have [r0|r0] := leP 0%R r.
    by rewrite mule_ge0//; apply: integral_ge0 => // t _; rewrite lee_fin.
  rewrite integral0_eq ?mule0// => x _.
  by rewrite preimage_nnfun0// indicE in_set0.
apply: eq_eseriesr => k _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

End integral_measure_series.

Section ge0_integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Import HBNNSimple.

Lemma ge0_integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall t, D t -> 0 <= f t) ->
  measurable_fun D f ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  suff : forall n, \sum_(k < n) \int[m_ k]_(x in D) f x <= \int[m]_(x in D) f x.
    move=> n; apply: lime_le => //.
      by apply: is_cvg_ereal_nneg_natsum => k _; exact: integral_ge0.
    by apply: nearW => x; rewrite big_mkord.
  move=> n.
  rewrite [X in _ <= X](_ : _ = \sum_(k < n) \int[m_ k]_(x in D) f x +
                                \int[mseries m_ n]_(x in D) f x); last first.
    transitivity (\int[measure_add (msum m_ n) (mseries m_ n)]_(x in D) f x).
      congr (\int[_]_(_ in D) _); apply/funext => A.
      rewrite measure_addE/= /msum -(big_mkord xpredT (m_ ^~ A)).
      exact: nneseries_split.
    by rewrite ge0_integral_measure_add// -ge0_integral_measure_sum.
  by apply: leeDl; exact: integral_ge0.
rewrite ge0_integralE//=; apply: ge_ereal_sup => /= _ [g /= gf] <-.
rewrite -integralT_nnsfun (integral_measure_series_nnsfun _ mD).
apply: lee_nneseries => [n _ _|n _].
  by apply: integral_ge0 => // x _; rewrite lee_fin.
rewrite [leRHS]integral_mkcond; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP.
- exact/(measurable_restrictT _ mD).
Qed.

End ge0_integral_measure_series.

Section subset_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_setU (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun (A `|` B) f ->
  (forall x, (A `|` B) x -> 0 <= f x) -> [disjoint A & B] ->
  \int[mu]_(x in A `|` B) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB.
transitivity (\int[mu]_(x in A `|` B) ((f \_ A) x + (f \_ B) x)).
  apply: eq_integral => x; rewrite inE => -[xA|xB].
    rewrite /patch mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xB.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
  rewrite /patch addeC mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xA.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
rewrite ge0_integralD//; last 5 first.
  - exact: measurableU.
  - by move=> x _; apply: erestrict_ge0 => y Ay; apply: f0; left.
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
  - by move=> x _; apply: erestrict_ge0 => y By; apply: f0; right.
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
by rewrite -integral_mkcondl setIC setUK -integral_mkcondl setKU.
Qed.

Lemma ge0_subset_integral (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun B f -> (forall x, B x -> 0 <= f x) ->
  A `<=` B -> \int[mu]_(x in A) f x <= \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB; rewrite -(setDUK AB) ge0_integral_setU//; last 4 first.
  - exact: measurableD.
  - by rewrite setDUK.
  - by move=> x; rewrite setDUK//; exact: f0.
  - by rewrite disj_set2E setDIK.
by apply: leeDl; apply: integral_ge0 => x [Bx _]; exact: f0.
Qed.

Lemma ge0_integral_bigsetU (I : eqType) (F : I -> set T) (f : T -> \bar R)
    (s : seq I) : (forall n, measurable (F n)) -> uniq s ->
  trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) f x = \sum_(i <- s) \int[mu]_(x in F i) f x.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf f0.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons ge0_integral_setU//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
  + by move=> x UFx; apply: f0; rewrite /D big_cons; right.
- exact: bigsetU_measurable.
- by move: mf; rewrite /D big_cons.
- by move: f0; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> (0 < a)%R ->
  a%:E * mu (D `&` [set x | `|g x| >= a%:E]) <= \int[mu]_(x in D) `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | a%:E <= `|g x|]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) `|g x|)).
  rewrite -integral_cstr//; apply: ge0_le_integral => //.
  - by move=> x _ /=; exact/ltW.
  - by apply: measurableT_comp => //; exact: measurable_funS mg.
  - by move=> x /= [].
by apply: ge0_subset_integral => //; exact: measurableT_comp.
Qed.

End subset_integral.
#[deprecated(since="mathcomp-analysis 1.0.1", note="use `ge0_integral_setU` instead")]
Notation integral_setU := ge0_integral_setU (only parsing).

Section integral_setU_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_setU_EFin (A B : set T) (f : T -> R) :
  measurable A -> measurable B ->
  measurable_fun (A `|` B) f ->
  [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) (f x)%:E = \int[mu]_(x in A) (f x)%:E +
                                       \int[mu]_(x in B) (f x)%:E.
Proof.
move=> mA mB ABf AB.
rewrite integralE/=.
rewrite ge0_integral_setU//; last exact/measurable_funepos/measurable_EFinP.
rewrite ge0_integral_setU//; last exact/measurable_funeneg/measurable_EFinP.
rewrite [X in _ = X + _]integralE/=.
rewrite [X in _ = _ + X]integralE/=.
set ap : \bar R := \int[mu]_(x in A) _; set an : \bar R := \int[mu]_(x in A) _.
set bp : \bar R := \int[mu]_(x in B) _; set bn : \bar R := \int[mu]_(x in B) _.
rewrite oppeD 1?addeACA//.
by rewrite ge0_adde_def// inE integral_ge0.
Qed.

Lemma integral_bigsetU_EFin (I : eqType) (F : I -> set T) (f : T -> R)
    (s : seq I) :
  (forall i, d.-measurable (F i)) ->
  uniq s -> trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D (EFin \o f) ->
  \int[mu]_(x in D) (f x)%:E = \sum_(i <- s) \int[mu]_(x in F i) (f x)%:E.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons integral_setU_EFin//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
- exact: bigsetU_measurable.
- by move/measurable_EFinP : mf; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

End integral_setU_EFin.

Section ge0_integral_bigcup.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_bigcup (F : (set _)^nat) (f : T -> \bar R) :
  (forall k, measurable (F k)) ->
  let D := \bigcup_k F k in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset setT F ->
  \int[mu]_(x in D) f x = \sum_(i <oo) \int[mu]_(x in F i) f x.
Proof.
move=> mF D mf f0 tF.
pose f_ N := f \_ (\big[setU/set0]_(0 <= i < N) F i).
have lim_f_ t : f_ ^~ t @ \oo --> (f \_ D) t.
  rewrite [X in _ --> X](_ : _ = ereal_sup (range (f_ ^~ t))); last first.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite /restrict; case: ifPn => [|_].
        rewrite in_setE => -[n _ Fnt]; apply: ereal_sup_ubound; exists n.+1=>//.
        by rewrite /f_ big_mkord patchT// in_setE big_ord_recr/=; right.
      rewrite (@le_trans _ _ (f_ O t))// ?ereal_sup_ubound//.
      by rewrite /f_ patchN// big_mkord big_ord0 inE/= in_set0.
    apply: ge_ereal_sup => x [n _ <-].
    by rewrite /f_ restrict_lee// big_mkord; exact: bigsetU_bigcup.
  apply: ereal_nondecreasing_cvgn => a b ab.
  rewrite /f_ !big_mkord restrict_lee //; last exact: subset_bigsetU.
  by move=> x Dx; apply: f0 => //; exact: bigsetU_bigcup Dx.
transitivity (\int[mu]_x limn (f_ ^~ x)).
  rewrite integral_mkcond; apply: eq_integral => x _.
  by apply/esym/cvg_lim => //; exact: lim_f_.
rewrite monotone_convergence//; last 3 first.
  - move=> n; apply/(measurable_restrictT f) => //.
      by apply: bigsetU_measurable => k _; exact: mF.
    move: mf; apply/measurable_funS =>//; first exact: bigcup_measurable.
    by rewrite big_mkord; exact: bigsetU_bigcup.
  - move=> n x _; apply: erestrict_ge0 => y; rewrite big_mkord => Dy; apply: f0.
    exact: bigsetU_bigcup Dy.
  - move=> x _ a b ab; apply: restrict_lee.
      by move=> y; rewrite big_mkord => Dy; apply: f0; exact: bigsetU_bigcup Dy.
    by rewrite 2!big_mkord; apply: subset_bigsetU.
transitivity (limn (fun N => \int[mu]_(x in \big[setU/set0]_(i < N) F i) f x)).
  by apply/congr_lim/funext => n; rewrite /f_ [in RHS]integral_mkcond big_mkord.
apply/congr_lim/funext => /= n.
rewrite -(big_mkord xpredT) ge0_integral_bigsetU ?big_mkord//.
- exact: iota_uniq.
- exact: sub_trivIset tF.
- move: mf; apply: measurable_funS => //; first exact: bigcup_measurable.
  exact: bigsetU_bigcup.
- by move=> y Dy; apply: f0; exact: bigsetU_bigcup Dy.
Qed.

End ge0_integral_bigcup.

Section integral_patch.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma __deprecated__integral_setI_indic (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  \int[mu]_(x in E `&` D) f x = \int[mu]_(x in E) (f x * (\1_D x)%:E).
Proof.
move=> mE; rewrite integral_mkcondr.
by under eq_integral do rewrite epatch_indic.
Qed.

Lemma __deprecated__integralEindic (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f x * (\1_D x)%:E).
Proof. by rewrite -__deprecated__integral_setI_indic// setIid. Qed.

Lemma integralEpatch (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f \_ D) x.
Proof. by rewrite -[in LHS](setIid D) integral_mkcondr. Qed.

End integral_patch.
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integral_mkcondr` instead")]
Notation integral_setI_indic := __deprecated__integral_setI_indic (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integralEpatch` instead")]
Notation integralEindic := __deprecated__integralEindic (only parsing).

Section ge0_cvgn_integral.
Local Open Scope ereal_scope.
Context {R : realType}.
Variable mu : {measure set (@measurableTypeR R) -> \bar R}.
Variable f : R -> R.
Hypothesis f0 : (forall x, 0 <= f x)%R.
Hypothesis mf : measurable_fun setT f.

Lemma ge0_integral_ereal_sup :
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E =
  ereal_sup [set \int[mu]_(x in `[0%R, i.+1%:R]) (f x)%:E | i in [set: nat]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ge_ereal_sup => /=_ [n _ <-].
  apply: ge0_subset_integral => //=.
  - by apply/measurable_EFinP; exact: measurable_funS mf.
  - by move=> ? _; rewrite lee_fin f0.
  - exact: subset_itvl.
rewrite itv0y_bigcup0S.
rewrite seqDU_bigcup_eq ge0_integral_bigcup//; last 3 first.
- by move=> ?; apply: measurableD => //; exact: bigsetU_measurable.
- exact/measurable_funTS/measurable_EFinP.
- by move=> x; rewrite lee_fin f0.
apply: lime_le => /=.
  apply: is_cvg_nneseries => n _ _.
  by apply: integral_ge0 => k _; exact: f0.
apply: nearW => n.
rewrite -ge0_integral_bigsetU//=; first last.
- by move=> ? _; rewrite lee_fin ?expR_ge0.
- exact/measurable_EFinP/measurableT_comp.
- exact: (sub_trivIset (@subsetT _ _)).
- exact: iota_uniq.
- by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
rewrite big_mkord -bigsetU_seqDU.
move: n => [|n].
  rewrite big_ord0 integral_set0.
  apply: le_ereal_sup_tmp.
  exists (\int[mu]_(x in `[0%R, 1%:R]) (f x)%:E) => //.
  by apply: integral_ge0 => /= ? _; rewrite lee_fin f0.
rewrite [X in \int[_]_(_ in X) _](_ : _ = `[0%R, n.+1%:R]%classic); last first.
  rewrite eqEsubset; split => x/=; rewrite in_itv/=.
    rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
    move=> [k /= kSn].
    rewrite in_itv/= => /andP[-> xSk]/=.
    by rewrite (le_trans xSk)// ler_nat.
  move=> /andP[x0 Snx].
  rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
  exists n => //=.
  by rewrite in_itv/= x0 Snx.
apply: le_ereal_sup_tmp.
exists (\int[mu]_(x in `[0%R, n.+1%:R]) (f x)%:E); first by exists n.
apply: ge0_subset_integral => //= [|? _]; last by rewrite lee_fin f0.
exact/measurable_EFinP/measurableT_comp.
Qed.

Lemma ge0_cvgn_integral :
  \int[mu]_(x in `[0%R, n%:R]) (f x)%:E @[n --> \oo] -->
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E.
Proof.
rewrite -cvg_shiftS/= ge0_integral_ereal_sup//.
apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n.
apply: (@ge0_subset_integral _ _ _ mu) => //.
- by apply: measurable_funTS; exact: measurableT_comp.
- by move => ? _; exact: f0.
- by apply: subset_itvl; rewrite bnd_simp ler_nat.
Qed.

End ge0_cvgn_integral.

Lemma le_abse_integral d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R)
  (mD : measurable D) : measurable_fun D f ->
  (`| \int[mu]_(x in D) (f x) | <= \int[mu]_(x in D) `|f x|)%E.
Proof.
move=> mf.
rewrite integralE (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: integral_ge0.
rewrite gee0_abs; last exact: integral_ge0.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: measurable_funepos | exact: measurable_funeneg].
Qed.

Lemma abse_integralP d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R) :
    measurable D -> measurable_fun D f ->
  (`| \int[mu]_(x in D) f x | < +oo <-> \int[mu]_(x in D) `|f x| < +oo)%E.
Proof.
move=> mD mf; split => [|] foo; last first.
  exact: (le_lt_trans (le_abse_integral mu mD mf) foo).
under eq_integral do rewrite -/((abse \o f) _) fune_abse.
rewrite ge0_integralD//;[|exact/measurable_funepos|exact/measurable_funeneg].
move: foo; rewrite integralE/= -fin_num_abs fin_numB => /andP[fpoo fnoo].
by rewrite lte_add_pinfty// ltey_eq ?fpoo ?fnoo.
Qed.

Lemma integral_fin_num_abs d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> R) :
  measurable D -> measurable_fun D f ->
  (\int[mu]_(x in D) `|(f x)%:E| < +oo)%E =
  ((\int[mu]_(x in D) (f x)%:E)%E \is a fin_num).
Proof.
move=> mD mf; rewrite fin_num_abs; case H : LHS; apply/esym.
- by move: H => /abse_integralP ->//; exact/measurable_EFinP.
- apply: contraFF H => /abse_integralP; apply => //.
  exact/measurable_EFinP.
Qed.

Section ae_measurable_fun.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Hypothesis cmu : measure_is_complete mu.
Variables (D : set T) (f g : T -> \bar R).

(* TODO: move to measure.v *)
Lemma ae_measurable_fun : ae_eq mu D f g ->
  measurable_fun D f -> measurable_fun D g.
Proof.
move=> [N [mN N0 subN]] mf B mB mD.
apply: (measurability _ (ErealGenOInfty.measurableE R)) => // _ [_ [x ->] <-].
rewrite [X in measurable X](_ : _ = D `&` ~` N `&` (f @^-1` `]x%:E, +oo[)
    `|` (D `&` N `&` g @^-1` `]x%:E, +oo[)); last first.
  apply/seteqP; split=> [y /= [Dy gyxoo]|y /= [[[Dy Ny] fyxoo]|]].
  - have [->|fgy] := eqVneq (f y) (g y).
      have [yN|yN] := boolP (y \in N).
        by right; split => //; rewrite inE in yN.
      by left; split => //; rewrite notin_setE in yN.
    by right; split => //; split => //; apply: subN => /= /(_ Dy); exact/eqP.
  - split => //; have [<-//|fgy] := eqVneq (f y) (g y).
    by exfalso; apply/Ny/subN => /= /(_ Dy); exact/eqP.
  - by move=> [[]].
apply: measurableU.
- rewrite setIAC; apply: measurableI; last exact/measurableC.
  exact/mf/emeasurable_itv.
- by apply: cmu; exists N; split => //; rewrite setIAC; apply: subIset; right.
Qed.

End ae_measurable_fun.

Section ge0_integral_counting.
Local Open Scope ereal_scope.
Variable R : realType.

Lemma counting_dirac (A : set nat) :
  counting A = \sum_(n <oo) \d_ n A :> \bar R.
Proof.
have -> : \sum_(n <oo) \d_ n A = \esum_(i in A) \d_ i A :> \bar R.
  rewrite nneseries_esum// (_ : [set _ | _] = setT); last exact/seteqP.
  rewrite [in LHS](esumID A)// !setTI [X in _ + X](_ : _ = 0) ?adde0//.
  by apply: esum1 => i Ai; rewrite /= /dirac indicE memNset.
rewrite /counting/=; case: ifPn => /asboolP finA.
  by rewrite -finite_card_dirac.
by rewrite infinite_card_dirac.
Qed.

Lemma ge0_integral_count (a : nat -> \bar R) : (forall k, 0 <= a k) ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@ge0_integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
Qed.

End ge0_integral_counting.

Section ae_eq_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Local Notation ae_eq := (ae_eq mu).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  ae_eq D f (cst 0) -> \int[mu]_(x in D) `|f x|%E  = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose Df_neq0 := D `&` [set x | f x != 0].
have mDf_neq0 : measurable Df_neq0 by exact: emeasurable_neq.
pose f' : T -> R := indic Df_neq0.
have le_f_M t : D t -> `|f t| <= M%:E * (f' t)%:E.
  move=> Dt; rewrite /f' indicE; have [|] := boolP (t \in Df_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  by rewrite notin_setE=> /not_andP[//|/negP/negPn/eqP ->]; rewrite abse0 mule0.
have : 0 <= \int[mu]_(x in D) `|f x|  <= `|M|%:E * mu Df_neq0.
  rewrite integral_ge0//= /Df_neq0 -{2}(setIid D) setIAC -integral_indic//.
  rewrite -/Df_neq0 -ge0_integralZl//; last exact: measurableT_comp.
  apply: ge0_le_integral => //.
  - exact: measurableT_comp.
  - by apply: emeasurable_funM => //; exact: measurableT_comp.
  - move=> x Dx; rewrite (le_trans (le_f_M _ Dx))// lee_fin /f' indicE.
    by case: (_ \in _) => //; rewrite ?mulr1 ?mulr0// ler_norm.
have -> : mu Df_neq0 = 0.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
by rewrite mule0 -eq_le => /eqP.
Qed.

Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable_fun D f -> \int[mu]_(x in D) `|f x| = 0 <-> ae_eq D f (cst 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists (D `&` [set x | f x != 0]); split;
    [exact: emeasurable_neq| |by move=> t /= /not_implyP [Dt /eqP ft0]].
  have muDf a : (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x|]) = 0.
    move=> a0; apply/eqP; rewrite -measure_le0.
    by have := le_integral_abse mu mD mf a0; rewrite iDf0 pmule_rle0 ?lte_fin.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[Dt ft0]|[n _ /= [Dt nft]]].
      have [ftoo|ftoo] := eqVneq `|f t| +oo.
        by exists 0%N => //; split => //=; rewrite ftoo /= leey.
      pose m := truncn (fine `|f t|)^-1.
      have ftfin : `|f t|%E \is a fin_num by rewrite ge0_fin_numE// ltey.
      exists m => //; split => //=.
      rewrite -(@fineK _ `|f t|) // lee_fin invf_ple; last 2 first.
        exact: ltr0n.
        by apply/fine_gt0; rewrite lt0e abse_ge0 abse_eq0 ft0 ltey.
      by rewrite (le_trans (ltW (truncnS_gt _))).
    by split => //; apply: contraTN nft => /eqP ->; rewrite abse0 -ltNge.
  transitivity (limn (fun n => mu (D `&` [set x | `|f x| >= n.+1%:R^-1%:E]))).
    apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
    - move=> i; apply: emeasurable_fun_c_infty => //.
      exact: measurableT_comp.
    - apply: bigcupT_measurable => i.
      by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
    - move=> m n mn; apply/subsetPset; apply: setIS => t /=.
      by apply: le_trans; rewrite lee_fin lef_pV2 // ?ler_nat // posrE.
  by rewrite (_ : (fun _ => _) = cst 0) ?lim_cst//= funeqE => n /=; rewrite muDf.
pose f_ := fun n x => mine `|f x| n%:R%:E.
have -> : (fun x => `|f x|) = (fun x => limn (f_^~ x)).
  rewrite funeqE => x; apply/esym/cvg_lim => //; apply/cvg_ballP => _/posnumP[e].
  near=> n; rewrite /ball /= /ereal_ball /= /f_.
  have [->|fxoo] := eqVneq `|f x|%E +oo.
    rewrite -[contract +oo](@divff _ (1 + n%:R)) ?nat1r//=.
    rewrite (@ger0_norm _ n%:R)// nat1r -mulrBl -natrB// subSnn ger0_norm//.
    by rewrite div1r; near: n; exact: near_infty_natSinv_lt.
  have fxn : `|f x| <= n%:R%:E.
    rewrite -(@fineK _ `|f x|); last by rewrite ge0_fin_numE// ltey.
    rewrite lee_fin; near: n; exists (Num.bound (fine `|f x|)) => //= n/=.
    by rewrite -(ler_nat R); apply: le_trans; exact/ltW/archi_boundP.
  by rewrite min_l// subrr normr0.
transitivity (limn (fun n => \int[mu]_(x in D) (f_ n x) )).
  apply/esym/cvg_lim => //; apply: cvg_monotone_convergence => //.
  - by move=> n; apply: measurable_mine => //; exact: measurableT_comp.
  - by move=> n t Dt; rewrite /f_ lexI abse_ge0 //= lee_fin.
  - move=> t Dt m n mn; rewrite /f_ lexI.
    have [ftm|ftm] := leP `|f t|%E m%:R%:E.
      by rewrite lexx /= (le_trans ftm)// lee_fin ler_nat.
    by rewrite (ltW ftm) /= lee_fin ler_nat.
have ae_eq_f_ n : ae_eq D (f_ n) (cst 0).
  case: Df0 => N [mN muN0 DfN].
  exists N; split => // t /= /not_implyP[Dt fnt0].
  apply: DfN => /=; apply/not_implyP; split => //.
  apply: contra_not fnt0 => ft0.
  by rewrite /f_ ft0 /= normr0 min_l// lee_fin.
have f_bounded n x : D x -> `|f_ n x| <= n%:R%:E.
  move=> Dx; rewrite /f_; have [|_] := leP `|f x| n%:R%:E.
    by rewrite abse_id.
  by rewrite gee0_abs// lee_fin.
have if_0 n : \int[mu]_(x in D) `|f_ n x| = 0.
  apply: (@ae_eq_integral_abs_bounded _ _ _ n%:R) => //.
    by apply: measurable_mine => //; exact: measurableT_comp.
  exact: f_bounded.
rewrite (_ : (fun _ => _) = cst 0) // ?lim_cst// funeqE => n.
by rewrite -(if_0 n); apply: eq_integral => x _; rewrite gee0_abs// /f_.
Unshelve. all: by end_near. Qed.

Lemma integral_abs_eq0 (N : set T) (f : T -> \bar R) :
  measurable N -> measurable_fun N f ->
  mu N = 0 -> \int[mu]_(x in N) `|f x| = 0.
Proof.
move=> mN mf muN0; rewrite integralEpatch//.
rewrite (eq_integral (abse \o (f \_ N))); last first.
  by move=> t _; rewrite restrict_abse.
apply/ae_eq_integral_abs => //.
  by apply/measurable_restrict => //; rewrite setIidr.
exists N; split => // t /= /not_implyP[_].
by rewrite patchE; case: ifPn => //; rewrite inE.
Qed.

Lemma ge0_negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf f0 muN0.
rewrite {1}(funID N f) ge0_integralD//; last 4 first.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - apply/measurable_restrict => //; first exact/measurableC.
    exact: measurable_funS mf.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - by apply/measurable_restrict => //; exact: measurable_funS mf.
rewrite -integral_mkcondr [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite -integral_mkcondr (eq_integral (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite integral_abs_eq0//.
- exact: measurableI.
- exact: measurable_funS mf.
- by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) ->
  ae_eq D f g -> \int[mu]_(x in D) (f x) = \int[mu]_(x in D) (g x).
Proof.
move=> mD mf mg f0 g0 [N [mN N0 subN]].
rewrite integralEpatch// [RHS]integralEpatch//.
rewrite (ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) f0.
rewrite [RHS](ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) g0.
apply: eq_integral => x;rewrite in_setD => /andP[_ xN].
apply: contrapT; rewrite !patchE; case: ifPn => xD //.
move: xN; rewrite notin_setE; apply: contra_not => fxgx; apply: subN => /=.
by apply/not_implyP; split => //; exact/set_mem.
Qed.

Lemma ae_eq_integral (D : set T) (g f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  ae_eq D f g -> \int[mu]_(x in D) f x = \int[mu]_(x in D) g x.
Proof.
move=> mD mf mg /ae_eq_funeposneg[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: measurable_funepos|
                                       exact: measurable_funepos].
by apply: ge0_ae_eq_integral => //; [exact: measurable_funeneg|
                                     exact: measurable_funeneg].
Qed.

End ae_eq_integral.
Arguments ae_eq_integral {d T R mu D} g.

Section ae_ge0_le_integral.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ae_ge0_le_integral : {ae mu, forall x, D x -> f1 x <= f2 x} ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> [N [mN muN f1f2N]]; rewrite (ge0_negligible_integral _ _ _ _ muN)//.
rewrite [leRHS](ge0_negligible_integral _ _ _ _ muN)//.
apply: ge0_le_integral; first exact: measurableD.
- by move=> t [Dt _]; exact: f10.
- exact: measurable_funS mf1.
- exact: measurable_funS mf2.
- by move=> t [Dt Nt]; move/subsetCl : f1f2N; exact.
Qed.

End ae_ge0_le_integral.

Lemma integral_cst d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) : d.-measurable D ->
  forall r, (\int[mu]_(x in D) (cst r) x = r * mu D)%E.
Proof.
move=> mD; have [D0 r|D0 [r| |]] := eqVneq (mu D) 0.
  by rewrite (ae_eq_integral (cst 0))// ?integral0 ?D0 ?mule0//; exact: ae_eq0.
- by rewrite lebesgue_integral_nonneg.integral_cstr.
- by rewrite lebesgue_integral_nonneg.integral_csty// gt0_mulye// lt0e D0/=.
- by rewrite lebesgue_integral_nonneg.integral_cstNy// gt0_mulNye// lt0e D0/=.
Qed.
Add Search Blacklist "integral_cstr" "integral_csty" "integral_cstNy".

Local Open Scope ereal_scope.

Lemma le_integral_comp_abse d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R})  (D : set T) (mD : measurable D)
    (g : T -> \bar R) a (f : \bar R -> \bar R) (mf : measurable_fun setT f)
    (f0 : forall r, 0 <= r -> 0 <= f r)
    (f_nd : {in `[0, +oo[%classic &, {homo f : x y / x <= y}}) :
  measurable_fun D g -> (0 < a)%R ->
  (f a%:E) * mu (D `&` [set x | (`|g x| >= a%:E)%E]) <= \int[mu]_(x in D) f `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | (a%:E <= `|g x|)%E]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) f `|g x|)).
  rewrite -integral_cst//; apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite f0 // lee_fin ltW.
  - apply: measurableT_comp => //; apply: measurableT_comp => //.
    exact: measurable_funS mg.
  - by move=> x /= [Dx]; apply: f_nd;
      rewrite inE /= in_itv /= andbT// lee_fin ltW.
apply: ge0_subset_integral => //; last by move=> x _ /=; rewrite f0.
by apply: measurableT_comp => //; exact: measurableT_comp.
Qed.

Local Close Scope ereal_scope.

Section integral_bounded.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integral_le_bound (D : set T) (f : T -> \bar R) (M : \bar R) :
  measurable D -> measurable_fun D f -> 0 <= M ->
  {ae mu, forall x, D x -> `|f x| <= M} ->
  \int[mu]_(x in D) `|f x| <= M * mu D.
Proof.
move=> mD mf M0 dfx; rewrite -integral_cst => //.
by apply: ae_ge0_le_integral => //; exact: measurableT_comp.
Qed.

End integral_bounded.
Arguments integral_le_bound {d T R mu D f} M.

Section lebesgue_measure_integral.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma integral_Sset1 (f : R -> \bar R) A (r : R) : A `<=` [set r] ->
  (\int[mu]_(x in A) f x = 0)%E.
Proof.
move=> Ar; have [->|->] := subset_set1 Ar; first by rewrite integral_set0.
rewrite (eq_integral (cst (f r)))/=; last by move=> x; rewrite inE/= => ->.
by rewrite integral_cst//= lebesgue_measure_set1 mule0.
Qed.

Lemma integral_set1 (f : R -> \bar R) (r : R) : \int[mu]_(x in [set r]) f x = 0.
Proof. exact: (integral_Sset1 _ (@subset_refl _ _)). Qed.

Lemma ge0_integral_closed_ball c (r : R) (r0 : (0 < r)%R) (f : R -> \bar R) :
  measurable_fun (closed_ball c r : set R) f ->
  (forall x, x \in closed_ball c r -> 0 <= f x) ->
  \int[mu]_(x in closed_ball c r) f x = \int[mu]_(x in ball c r) f x.
Proof.
move=> mf f0.
rewrite closed_ball_ball//= ge0_integral_setU//=; last 4 first.
  by apply: measurableU => //; exact: measurable_ball.
  by move: mf; rewrite closed_ball_ball.
  by move=> x xcr; rewrite f0// closed_ball_ball// inE.
  apply/disj_setPLR => x [->|]/=; rewrite /ball/=.
    by move/addrI; apply/eqP; rewrite eqNr gt_eqF.
  by move=> /[swap] ->; rewrite opprD addNKr normrN gtr0_norm// ltxx.
rewrite ge0_integral_setU//=.
- by rewrite !integral_set1//= add0e adde0.
- exact: measurable_ball.
- apply: measurable_funS mf; first exact: measurable_closed_ball.
  by move=> x; rewrite closed_ball_ball//; left.
- by move=> x H; rewrite f0// closed_ball_ball// inE/=; left.
- by apply/disj_setPRL => x /[swap] ->; rewrite /ball/= subKr gtr0_norm// ltxx.
Qed.

Lemma integral_setD1_EFin (f : R -> R) r (D : set R) :
  measurable (D `\ r) -> measurable_fun (D `\ r) f ->
  \int[mu]_(x in D `\ r) (f x)%:E = \int[mu]_(x in D) (f x)%:E.
Proof.
move=> mD mfl; have [Dr|NDr] := pselect (D r); last by rewrite not_setD1.
rewrite -[in RHS](@setD1K _ r D)// integral_setU_EFin//=.
- by rewrite integral_set1// add0e.
- by apply/measurable_funU => //; split => //; exact: measurable_fun_set1.
- by rewrite disj_set2E setDIK.
Qed.

Lemma integral_itv_bndo_bndc (a : itv_bound R) (r : R) (f : R -> R) :
  measurable_fun [set` Interval a (BLeft r)] f ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x)%:E =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x)%:E.
Proof.
move=> mf; have [ar|ar] := leP a (BLeft r).
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1r.
- by rewrite !set_itv_ge// -leNgt// ltW.
Qed.

Lemma integral_itv_obnd_cbnd (r : R) (b : itv_bound R) (f : R -> R) :
  measurable_fun [set` Interval (BRight r) b] f ->
   \int[mu]_(x in [set` Interval (BRight r) b]) (f x)%:E =
   \int[mu]_(x in [set` Interval (BLeft r) b]) (f x)%:E.
Proof.
move=> mf; have [rb|rb] := leP (BRight r) b.
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1l.
- by rewrite !set_itv_ge// -leNgt -?ltBRight_leBLeft// ltW.
Qed.

Lemma integral_itv_bndoo (x y : R) (f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in `]x, y[) (f z)%:E.
Proof.
have [xy|yx _|-> _] := ltgtP x y; last 2 first.
- rewrite !set_itv_ge ?integral_set0//=.
  + by rewrite bnd_simp le_gtF// ltW.
  + by move: b0 b1 => [|] [|]; rewrite bnd_simp ?lt_geF// le_gtF// ltW.
- by move: b0 b1 => [|] [|]; rewrite !set_itvE ?integral_set0 ?integral_set1.
move=> mf.
transitivity (\int[mu]_(z in [set` Interval (BSide b0 x) (BLeft y)]) (f z)%:E).
  case: b1 => //; rewrite -integral_itv_bndo_bndc//.
  by case: b0 => //; exact/measurable_fun_itv_obnd_cbndP.
by case: b0 => //; rewrite -integral_itv_obnd_cbnd.
Qed.

Lemma eq_integral_itv_bounded (x y : R) (g f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f -> measurable_fun `]x, y[ g ->
  {in `]x, y[, f =1 g} ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (g z)%:E.
Proof.
move=> mf mg fg.
rewrite integral_itv_bndoo// (@integral_itv_bndoo _ _ g)//.
by apply: eq_integral => z; rewrite inE/= => zxy; congr EFin; exact: fg.
Qed.

End lebesgue_measure_integral.
Arguments integral_Sset1 {R f A} r.

Section ge0_nondecreasing_set_cvg_integral.
Context {d : measure_display} {T : measurableType d} {R : realType}.
Variables (F : (set T)^nat) (f : T -> \bar R) (mu : measure T R).
Local Open Scope ereal_scope.
Hypotheses (nndF : nondecreasing_seq F) (mF : forall i, measurable (F i)).
Hypothesis mf : forall i, measurable_fun (F i) f.
Hypothesis f0 : forall i x, F i x -> 0 <= f x.

Lemma ge0_nondecreasing_set_nondecreasing_integral :
  nondecreasing_seq (fun i => \int[mu]_(x in F i) f x).
Proof.
apply/nondecreasing_seqP => n; apply: ge0_subset_integral => //=.
- by move=> ?; exact: f0.
- by rewrite -subsetEset; exact: nndF.
Qed.

Lemma ge0_nondecreasing_set_cvg_integral :
  \int[mu]_(x in F i) f x @[i --> \oo] --> \int[mu]_(x in \bigcup_i F i) f x.
Proof.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn.
  exact: ge0_nondecreasing_set_nondecreasing_integral.
under eq_fun do rewrite integral_mkcond/=.
rewrite -monotone_convergence//=; last 3 first.
- by move=> n; apply/(measurable_restrictT f).
- by move=> n x _; apply: erestrict_ge0 => {}x; exact: f0.
- move=> x _; apply/nondecreasing_seqP => n; apply: restrict_lee => //.
    by move=> {}x; exact: f0.
  by rewrite -subsetEset; exact: nndF.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => /=; rewrite /g_sigma_algebraType/ocitv_type => x _.
transitivity (ereal_sup (range (fun n => (f \_ (F n)) x))).
  apply/cvg_lim => //.
  apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n; apply: restrict_lee.
    by move=> {}x; exact: f0.
  by rewrite -subsetEset; exact: nndF.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ge_ereal_sup => _/= [n _ <-].
  apply: restrict_lee; last exact: bigcup_sup.
  by move=> ? [? _]; exact: f0.
- rewrite patchE; case: ifPn=> [|/negP].
    rewrite inE => -[n _ Fnx].
    by apply: le_ereal_sup_tmp; exists (f \_ (F n) x) => //; rewrite patchE mem_set.
  rewrite inE -[X in X -> _]/((~` _) x) setC_bigcup => nFx.
  apply/le_ereal_sup_tmp; exists point => //=; exists 0%R => //.
  by rewrite patchE memNset//; exact: nFx.
Qed.

End ge0_nondecreasing_set_cvg_integral.

Section le0_nondecreasing_set_cvg_integral.
Context {d : measure_display} {T : measurableType d} {R : realType}.
Variables (F : (set T)^nat) (f : T -> \bar R) (mu : measure T R).
Local Open Scope ereal_scope.
Hypotheses (nndF : nondecreasing_seq F) (mF : forall i, measurable (F i)).
Hypothesis mf : forall i, measurable_fun (F i) f.
Hypothesis f0 : forall i x, F i x -> f x <= 0.

Let intNS n : (- (\int[mu]_(x in F n) f x)) = \int[mu]_(x in F n) - f x.
Proof.
apply/esym; apply: integralN => /=; apply: fin_num_adde_defr.
rewrite integral0_eq// => x Fnx.
by rewrite (@le0_funeposE _ _ (F n)) ?inE//; exact: f0.
Qed.

Let mNf i : measurable_fun (F i) (\- f).
Proof. by apply: measurableT_comp => //; exact: mf. Qed.

Let Nf_ge0 i x: F i x -> 0%R <= - f x.
Proof. by move=> Six; rewrite leeNr oppe0; exact: f0 Six. Qed.

Lemma le0_nondecreasing_set_nonincreasing_integral :
  nonincreasing_seq (fun i => \int[mu]_(x in F i) f x).
Proof.
move=> m n mn; rewrite -leeN2 2!intNS.
exact: ge0_nondecreasing_set_nondecreasing_integral.
Qed.

Lemma le0_nondecreasing_set_cvg_integral :
  \int[mu]_(x in F i) f x @[i --> \oo] --> \int[mu]_(x in \bigcup_i F i) f x.
Proof.
apply/cvgeNP; rewrite -integralN/=; last first.
  apply: fin_num_adde_defr; rewrite integral0_eq// => x [n _ Fnx].
  by rewrite (le0_funeposE (@f0 n))// inE.
under eq_cvg do rewrite intNS.
exact: ge0_nondecreasing_set_cvg_integral.
Qed.

End le0_nondecreasing_set_cvg_integral.
