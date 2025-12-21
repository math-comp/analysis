(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure numfun realfun.
From mathcomp Require Import interval_inference real_interval lebesgue_integral.
From mathcomp Require Import derive charge.

(**md**************************************************************************)
(* # Fundamental Theorem of Calculus and Consequences                         *)
(*                                                                            *)
(* This file provide formalization of the first fundamental theorem of        *)
(* calculus for the Lebesgue integral and its consequences, in particular a   *)
(* corollary to compute the integral of continuous functions (FTC2),          *)
(* integration by parts, substitution, etc.                                   *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - R. Affeldt, Z. Stone. A Comprehensive Overview of the Lebesgue           *)
(*   Differentiation Theorem in Coq. ITP 2024                                 *)
(*                                                                            *)
(* Examples of lemmas (with `F` and `G` antiderivatives of `f` and `g`):      *)
(* - `continuous_FTC2`: $\int_a^b f(x)dx = F(b) - F(a)$                       *)
(* - `{ge0,le0}_continuous_FTC2y`: $\int_a^\infty f(x)dx = \ell - F(a)$ with  *)
(*   $\lim_{x\to\infty}F(x)=\ell$ and $f$ non-negative or non-positive        *)
(* - `integration_by_parts`:                                                  *)
(*   $\int_a^b F(x)g(x)dx = F(b)G(b) - F(a)G(a) - \int_a^b f(x)G(x)dx$        *)
(* - `integration_by_substitution_{decreasing,increasing}`:                   *)
(*   $\int_{F(b)}^{F(a)} G(x)dx = \int_a^b -G(F(x))f(x)dx$                    *)
(*   with $F$ decreasing,                                                     *)
(*   $\int_{F(a)}^{F(b)} G(x)dx = \int_a^b G(F(x))f(x)dx$                     *)
(*   with $F$ increasing                                                      *)
(* - `{decreasing,increasing}_ge0_integration_by_substitutiony`:              *)
(*   $\int_{-\infty}^{F(a)} G(x)dx = \int_a^\infty -G(F(x))f(x)dx$            *)
(*   with $F$ decreasing, $\lim_{x\to\infty}F(x)=-\infty$, and                *)
(*   $G$ non-negative,                                                        *)
(*   $\int_{F(a)}^{\infty} G(x)dx = \int_a^\infty G(F(x))f(x)dx$              *)
(*   with $F$ increasing, $\lim_{x\to\infty}F(x)=\infty$, and                 *)
(*   $G$ non-negative                                                         *)
(* - `increasing_ge0_integration_by_substitutionT`:                           *)
(*   $\int_{-\infty}^{\infty} G(x)dx = \int_{-\infty}^\infty -G(F(x))f(x)dx$  *)
(*   with $F$ increasing and $G$ non-negative                                 *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(* parameterized_integral mu a x f := \int[mu]_(t \in `[a, x] f t)            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section FTC.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a : itv_bound R).

Lemma integrable_locally f (A : set R) : measurable A ->
  mu.-integrable A (EFin \o f) -> locally_integrable [set: R] (f \_ A).
Proof.
move=> mA intf; split.
- move/integrableP : intf => [mf _].
  by apply/(measurable_restrictT _ _).1 => //; exact/measurable_EFinP.
- exact: openT.
- move=> K _ cK.
  move/integrableP : intf => [mf].
  rewrite integral_mkcond/=.
  under eq_integral do rewrite restrict_EFin restrict_normr.
  apply: le_lt_trans.
  apply: ge0_subset_integral => //=; first exact: compact_measurable.
  apply/measurable_EFinP/measurableT_comp/measurable_EFinP => //=.
  move/(measurable_restrictT _ _).1 : mf => /=.
  by rewrite restrict_EFin; exact.
Qed.

Let FTC0 f a : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) f t)%R in
  forall x, a < BRight x -> lebesgue_pt f x ->
    h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> intf F x ax fx.
have locf : locally_integrable setT f.
  by apply: open_integrable_locally => //; exact: openT.
apply: cvg_at_right_left_dnbhs.
- apply/cvg_at_rightP => d [d_gt0 d0].
  pose E x n := `[x, x + d n[%classic%R.
  have muE y n : mu (E y n) = (d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin ltrDl d_gt0.
    by rewrite -EFinD -addrA subrKC.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2%R, fun n => PosNum (d_gt0 n)); split => //= [n z|n].
      rewrite /E/= in_itv/= /ball/= ltr_distlC => /andP[yz ->].
      by rewrite (lt_le_trans _ yz)// ltrBlDr ltrDl.
    rewrite (lebesgue_measure_ball _ (ltW _))// -/mu muE -EFinM lee_fin.
    by rewrite mulr_natl.
  have ixdf n : \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E =
                \int[mu]_(y in E x n) (f y)%:E.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      by case: locf => + _ _; exact: measurable_funS.
    rewrite (@itv_bndbnd_setU _ _ _ (BLeft x))//=; last 2 first.
      by case: a ax F => [[|] a|[|]]// /ltW.
      by rewrite bnd_simp lerDl ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in _ - X]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite subee ?add0e//.
      by apply: integrable_fin_num => //; exact: integrableS intf.
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPRL => z/=.
      rewrite /E /= !in_itv/= => /andP[xz zxdn].
      move: a ax {F} => [[|] t/=|[_ /=|//]].
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -leNgt xz orbT.
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -!leNgt xz orbT.
      - by apply/negP; rewrite -leNgt.
  rewrite [f in f n @[n --> _] --> _](_ : _ =
      fun n => (d n)^-1 *: fine (\int[mu]_(t in E x n) (f t)%:E)); last first.
    apply/funext => n; congr (_ *: _); rewrite -fineB/=.
    by rewrite /= (addrC (d n) x) ixdf.
    by apply: integrable_fin_num => //; exact: integrableS intf.
    by apply: integrable_fin_num => //; exact: integrableS intf.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  rewrite [g in g n @[n --> _] --> _ -> _](_ : _ =
      fun n => (d n)^-1%:E * \int[mu]_(y in E x n) (f y)%:E); last first.
    by apply/funext => n; rewrite muE inver// gt_eqF.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  set h := (f in f n @[n --> \oo] --> _).
  suff : g = h by move=> <-.
  apply/funext => n.
  rewrite /g /h /= fineM//.
  apply: integrable_fin_num => //; first exact: (nice_E _).1.
  by apply: integrableS intf => //; exact: (nice_E _).1.
- apply/cvg_at_leftP => d [d_gt0 d0].
  have {}Nd_gt0 n : (0 < - d n)%R by rewrite ltrNr oppr0.
  pose E x n := `]x + d n, x]%classic%R.
  have muE y n : mu (E y n) = (- d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin -ltrBrDr.
    by rewrite ltrDl Nd_gt0 -EFinD opprD addNKr.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2%R, (fun n => PosNum (Nd_gt0 n))); split => //=.
      by rewrite -oppr0; exact: cvgN.
    move=> n z.
      rewrite /E/= in_itv/= /ball/= => /andP[yz zy].
      by rewrite ltr_distlC opprK yz /= (le_lt_trans zy)// ltrDl.
    move=> n.
    rewrite lebesgue_measure_ball//; last exact: ltW.
    by rewrite -/mu muE -EFinM lee_fin mulr_natl.
  have ixdf : {near \oo,
      (fun n => \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E) =1
      (fun n => - (\int[mu]_(y in E x n) (f y)%:E))}.
    case: a ax {F}; last first.
      move=> [_|//].
      apply: nearW => n.
      rewrite -[in LHS]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite -/mu -[LHS]oppeK; congr oppe.
      rewrite oppeB; last first.
        rewrite fin_num_adde_defl// fin_numN//.
        by apply: integrable_fin_num => //; exact: integrableS intf.
      rewrite addeC.
      rewrite (_ : `]-oo, x] = `]-oo, (x + d n)%R] `|` E x n)%classic; last first.
        by rewrite -itv_bndbnd_setU//= bnd_simp ler_wnDr// ltW.
      rewrite integral_setU_EFin//=.
      - rewrite addeAC.
        rewrite -[X in X - _]integral_itv_bndo_bndc//; last first.
          by case: locf => + _ _; exact: measurable_funS.
        rewrite subee ?add0e//.
        by apply: integrable_fin_num => //; exact: integrableS intf.
      - exact: (nice_E _).1.
      - by case: locf => + _ _; exact: measurable_funS.
      - apply/disj_setPLR => z/=.
        rewrite /E /= !in_itv/= leNgt => xdnz.
        by apply/negP; rewrite negb_and xdnz.
    move=> b a ax.
    move/cvgrPdist_le : d0.
    move/(_ (x - a)%R); rewrite subr_gt0 => /(_ ax)[m _ /=] h.
    near=> n.
    have mn : (m <= n)%N by near: n; exists m.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      by case: locf => + _ _; exact: measurable_funS.
    rewrite -/mu -[LHS]oppeK; congr oppe.
    rewrite oppeB; last first.
      rewrite fin_num_adde_defl// fin_numN//.
      by apply: integrable_fin_num => //; exact: integrableS intf.
    rewrite addeC.
    rewrite (@itv_bndbnd_setU _ _ _ (BRight (x - - d n)%R))//; last 2 first.
      case: b in ax * => /=; rewrite bnd_simp.
        rewrite lerBrDl addrC -lerBrDl.
        by have := h _ mn; rewrite sub0r gtr0_norm.
      rewrite lerBrDl -lerBrDr.
      by have := h _ mn; rewrite sub0r gtr0_norm.
      by rewrite opprK bnd_simp -lerBrDl subrr ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in X - _]integral_itv_bndo_bndc//; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite opprK subee ?add0e//.
      by apply: integrable_fin_num => //; exact: integrableS intf.
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPLR => z/=.
      rewrite /E /= !in_itv/= => /andP[az zxdn].
      by apply/negP; rewrite negb_and -leNgt zxdn.
  suff: ((d n)^-1 * - fine (\int[mu]_(y in E x n) (f y)%:E))%R
          @[n --> \oo] --> f x.
    apply: cvg_trans; apply: near_eq_cvg; near=> n;  congr (_ *: _).
    rewrite /F -fineN -fineB; last 2 first.
      by apply: integrable_fin_num => //; exact: integrableS intf.
      by apply: integrable_fin_num => //; exact: integrableS intf.
    by congr fine => /=; apply/esym; rewrite (addrC _ x); near: n.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  rewrite (@eq_cvg _ _ _ _ g)// => n.
  rewrite /g /= fineM//=; last first.
    apply: integrable_fin_num => //; first exact: (nice_E _).1.
    by apply: integrableS intf => //; exact: (nice_E _).1.
    by rewrite muE inver oppr_eq0 lt_eqF.
  by rewrite muE/= inver oppr_eq0 lt_eqF// invrN mulNr -mulrN.
Unshelve. all: by end_near. Qed.

Let FTC0_restrict f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) f t)%R in
  a < BRight x -> lebesgue_pt f x ->
  h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> xu + F ax fx.
rewrite integrable_mkcond//= (restrict_EFin f) => intf.
have /(@FTC0 _ _ intf _ ax) : lebesgue_pt (f \_ [set` Interval a (BRight u)]) x.
  exact: lebesgue_pt_restrict.
rewrite patchE mem_set; last first.
  rewrite /= in_itv/= (ltW xu) andbT.
  by move: a ax {F intf} => [[a|]|[]]//=; rewrite lte_fin => /ltW.
apply: cvg_trans; apply: near_eq_cvg; near=> r; congr (_ *: (_ - _)).
- apply: eq_Rintegral => y yaxr; rewrite patchE mem_set//=.
  move: yaxr; rewrite /= !in_itv/= inE/= in_itv/= => /andP[->/=].
  move=> /le_trans; apply; rewrite -lerBrDr.
  have [r0|r0] := leP r 0%R; first by rewrite (le_trans r0)// subr_ge0 ltW.
  by rewrite -(gtr0_norm r0); near: r; apply: dnbhs0_le; rewrite subr_gt0.
- apply: eq_Rintegral => y yaxr; rewrite patchE mem_set//=.
  move: yaxr => /=; rewrite !in_itv/= inE/= in_itv/= => /andP[->/=].
  by move=> /le_trans; apply; exact/ltW.
Unshelve. all: by end_near. Qed.

(* NB: right-closed interval *)
Lemma FTC1_lebesgue_pt f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) (f t))%R in
  a < BRight x -> lebesgue_pt f x ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu intf F ax fx; split; last first.
  by apply/cvg_lim; [exact: Rhausdorff|exact: (@FTC0_restrict _ _ _ u)].
apply/cvg_ex; exists (f x).
have /= := FTC0_restrict xu intf ax fx.
set g := (f in f n @[n --> _] --> _ -> _).
set h := (f in _ -> f n @[n --> _] --> _).
suff : g = h by move=> <-.
by apply/funext => y;rewrite /g /h /= [X in F (X + _)]mulr1.
Qed.

Corollary FTC1 f a :
  (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
  locally_integrable [set: R] f ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  {ae mu, forall x, a < BRight x -> derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F; move: (locf) => /lebesgue_differentiation.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
move=> i fi ai.
by apply: (@FTC1_lebesgue_pt _ _ _ (i + 1)%R) => //; rewrite ltrDl.
Qed.

Corollary FTC1Ny f :
  (forall y, mu.-integrable `]-oo, y] (EFin \o f)) ->
  locally_integrable [set: R] f ->
  let F x := (\int[mu]_(t in [set` `]-oo, x]]) (f t))%R in
  {ae mu, forall x, derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F; have := FTC1 intf locf.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> r /=; apply; rewrite ltNyr.
Qed.

Let itv_continuous_lebesgue_pt f a x (u : R) : (x < u)%R ->
  measurable_fun [set` Interval a (BRight u)] f ->
  a < BRight x ->
  {for x, continuous f} -> lebesgue_pt f x.
Proof.
move=> xu fi + fx.
move: a fi => [b a fi /[1!(@lte_fin R)] ax|[|//] fi _].
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  + exact: ball_open_nbhs.
  + exact: measurable_ball.
  + apply: measurable_funS fi => //; rewrite ball_itv.
    apply: (@subset_trans _ `](x - e)%R, u]) => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
    apply: subset_itvr; rewrite bnd_simp lerBrDr -lerBrDl.
    by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  + exact: ball_open_nbhs.
  + exact: measurable_ball.
  + apply: measurable_funS fi => //; rewrite ball_itv.
    apply: (@subset_trans _ `](x - e)%R, u]) => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
    exact: subset_itvr.
Unshelve. all: by end_near. Qed.

Corollary continuous_FTC1 f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  a < BRight x -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu fi F ax fx; suff lfx : lebesgue_pt f x.
  have /(_ ax lfx)[dfx f'xE] := @FTC1_lebesgue_pt _ a _ _ xu fi.
  by split; [exact: dfx|rewrite f'xE].
apply: itv_continuous_lebesgue_pt xu _ ax fx.
by move/integrableP : fi => -[/measurable_EFinP].
Qed.

Corollary continuous_FTC1_closed f (a x : R) (u : R) : (x < u)%R ->
  mu.-integrable `[a, u] (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` `[a, x]]) (f t))%R in
  (a < x)%R -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof. by move=> xu locf F ax fx; exact: (@continuous_FTC1 _ _ _ u). Qed.

End FTC.

Definition parameterized_integral {R : realType}
    (mu : {measure set (measurableTypeR R) -> \bar R})
    a x (f : R -> R) : R :=
  (\int[mu]_(t in `[a, x]) f t)%R.

Section parameterized_integral_continuous.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).

Let int := (parameterized_integral mu).

Lemma parameterized_integral_near_left (a b : R) (e : R) (f : R -> R) :
  a < b -> 0 < e -> mu.-integrable `[a, b] (EFin \o f) ->
  \forall c \near a, a <= c -> `| int a c f | < e.
Proof.
move=> ab e0 intf.
have : mu.-integrable setT (EFin \o f \_ `[a, b]).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
move=> /integral_normr_continuous /(_ _ e0)[d [d0 /=]] ifab.
near=> c => ac.
have /ifab : (mu `[a, c] < d%:E)%E.
  rewrite lebesgue_measure_itv/= lte_fin.
  case: ifPn => // {}ac; rewrite -EFinD lte_fin.
  by move: ac; near: c; exact: nbhs_right_ltDr.
move=> /(_ (measurable_itv _)) {ifab}.
apply: le_lt_trans.
have acbc : `[a, c] `<=` `[a, b].
  apply: subset_itvl; rewrite bnd_simp; move: ac; near: c.
  exact: lt_nbhsl_le.
rewrite -lee_fin fineK; last first.
  apply: integrable_fin_num => //=.
  rewrite (_ : (fun _ => _) = abse \o ((EFin \o f) \_ `[a, b])); last first.
    by apply/funext => x /=; rewrite restrict_EFin.
  apply/integrable_abse/integrable_restrict => //=.
  by rewrite setIidl//; exact: integrableS intf.
rewrite [leRHS]integralEpatch//= [in leRHS]integralEpatch//=.
under [in leRHS]eq_integral.
  move=> /= x xac.
  rewrite -patch_setI setIid restrict_EFin/= restrict_normr/=.
  rewrite -patch_setI setIidl//.
  over.
rewrite /= [leRHS](_ : _ = \int[mu]_(x in `[a, c]) `| f x |%:E)%E; last first.
  rewrite [RHS]integralEpatch//=; apply: eq_integral => x xac/=.
  by rewrite restrict_EFin/= restrict_normr.
rewrite /int /parameterized_integral /=.
apply: (@le_trans _ _ ((\int[mu]_(t in `[a, c]) `|f t|))%:E).
  by apply: le_normr_Rintegral => //; exact: integrableS intf.
set rhs : \bar R := leRHS.
have [->|rhsoo] := eqVneq rhs +oo%E; first by rewrite leey.
rewrite /rhs /Rintegral -/rhs.
rewrite fineK// fin_numE rhsoo andbT -ltNye (@lt_le_trans _ _ 0%E)//.
exact: integral_ge0.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_cvg_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> a] --> 0.
Proof.
move=> ab intf; pose fab := f \_ `[a, b].
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
apply/cvgrPdist_le => /= e e0; near=> x.
rewrite {1}/int /parameterized_integral sub0r normrN.
have [|xa] := leP a x.
  move=> ax; apply/ltW; move: ax.
  by near: x; exact: (@parameterized_integral_near_left _ b).
by rewrite set_itv_ge ?Rintegral_set0 ?normr0 ?(ltW e0)// -leNgt bnd_simp.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_cvg_at_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> b^'-] --> int a b f.
Proof.
move=> ab intf; pose fab := f \_ `[a, b].
have /= int_normr_cont : forall e : R, 0 < e ->
    exists d : R, 0 < d /\
    forall A, measurable A -> (mu A < d%:E)%E -> \int[mu]_(x in A) `|fab x| < e.
  rewrite /= => e e0; apply: integral_normr_continuous => //=.
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
rewrite /int /parameterized_integral; apply/cvgrPdist_le => /= e e0.
have [d [d0 /= {}int_normr_cont]] := int_normr_cont _ e0.
near=> x.
rewrite [in X in X - _](@itv_bndbnd_setU _ _ _ (BRight x))//;
  [|by rewrite bnd_simp ltW..].
rewrite Rintegral_setU//=; last 2 first.
  rewrite -itv_bndbnd_setU// ?bnd_simp; last 2 first.
    by near: x; exact: nbhs_left_ge.
    exact/ltW.
  apply/disj_set2P; rewrite -subset0 => z/=; rewrite !in_itv/= => -[/andP[_]].
  by rewrite leNgt => /negbTE ->.
have xbab : `]x, b] `<=` `[a, b].
  by apply: subset_itvr; rewrite bnd_simp; near: x; exact: nbhs_left_ge.
rewrite -addrA subrKC (le_trans (le_normr_Rintegral _ _))//.
  exact: integrableS intf.
rewrite [leLHS](_ : _ = (\int[mu]_(t in `]x, b]) `|fab t|))//; last first.
  apply: eq_Rintegral => //= z; rewrite inE/= in_itv/= => /andP[xz zb].
  rewrite /fab patchE ifT// inE/= in_itv/= zb andbT (le_trans _ (ltW xz))//.
  by near: x; exact: nbhs_left_ge.
apply/ltW/int_normr_cont => //.
rewrite lebesgue_measure_itv/= lte_fin.
rewrite ifT// -EFinD lte_fin.
near: x; exists d => // z; rewrite /ball_/= => + zb.
by rewrite gtr0_norm// ?subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_continuous a b (f : R -> R) : a <= b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  {within `[a, b], continuous (fun x => int a x f)}.
Proof.
rewrite le_eqVlt => /predU1P[<- _|ab intf].
  by rewrite set_itv1; exact: continuous_subspace1.
apply/(continuous_within_itvP _ ab); split; first last.
  exact: parameterized_integral_cvg_at_left.
  apply/cvg_at_right_filter.
  rewrite {2}/int /parameterized_integral set_itv1 Rintegral_set1.
  exact: (parameterized_integral_cvg_left ab).
pose fab := f \_ `[a, b].
have /= int_normr_cont : forall e : R, 0 < e ->
    exists d : R, 0 < d /\
    forall A, measurable A -> (mu A < d%:E)%E -> \int[mu]_(x in A) `|fab x| < e.
  rewrite /= => e e0; apply: integral_normr_continuous => //=.
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
rewrite /int /parameterized_integral => z; rewrite in_itv/= => /andP[az zb].
apply/cvgrPdist_le => /= e e0.
have [d [d0 /= {}int_normr_cont]] := int_normr_cont _ e0.
near=> x.
have [xz|xz|->] := ltgtP x z; last by rewrite subrr normr0 ltW.
- have ax : a < x.
    move: xz; near: x.
    exists `|z - a| => /=; first by rewrite gtr0_norm ?subr_gt0.
    move=> y /= + yz.
    do 2 rewrite gtr0_norm ?subr_gt0//.
    by rewrite ltrBlDr -ltrBlDl opprB subrKC.
  rewrite Rintegral_itvB//; last 3 first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
    by rewrite bnd_simp ltW.
    exact: ltW.
  have xzab : `]x, z] `<=` `[a, b].
    by apply: subset_itvScc; rewrite bnd_simp; exact/ltW.
  apply: (le_trans (le_normr_Rintegral _ _)) => //; first exact: integrableS intf.
  rewrite -(setIidl xzab) Rintegral_mkcondr/=.
  under eq_Rintegral do rewrite restrict_normr.
  apply/ltW/int_normr_cont => //.
  rewrite lebesgue_measure_itv/= lte_fin xz -EFinD lte_fin ltrBlDl.
  move: xz; near: x.
  exists (d / 2); first by rewrite /= divr_gt0.
  move=> x/= /[swap] xz.
  rewrite gtr0_norm ?subr_gt0// ltrBlDl => /lt_le_trans; apply.
  by rewrite lerD2l ler_pdivrMr// ler_pMr// ler1n.
+ have ax : a < x by rewrite (lt_trans az).
  have xb : x < b.
    move: xz; near: x.
    exists `|b - z|; first by rewrite /= gtr0_norm ?subr_gt0.
    move=> y /= + yz.
    by rewrite ltr0_norm ?subr_lt0// gtr0_norm ?subr_gt0// opprB ltrBlDr subrK.
  rewrite -opprB normrN Rintegral_itvB ?bnd_simp; [| |exact/ltW..]; last first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
  have zxab : `[z, x] `<=` `[a, b] by apply: subset_itvScc; exact/ltW.
  have intzxf : mu.-integrable `[z, x] (EFin \o f) by exact: integrableS intf.
  rewrite Rintegral_itv_obnd_cbnd//; last first.
    by apply: (@integrableS _ _ _ mu `[z, x]) => //; exact: subset_itv_oc_cc.
  apply: (le_trans (le_normr_Rintegral _ _)) => //.
  rewrite -(setIidl zxab) Rintegral_mkcondr/=.
  under eq_Rintegral do rewrite restrict_normr.
  apply/ltW/int_normr_cont => //.
  rewrite lebesgue_measure_itv/= lte_fin xz -EFinD lte_fin ltrBlDl.
  move: xz; near: x.
  exists (d / 2); first by rewrite /= divr_gt0.
  move=> x/= /[swap] xz.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl => /lt_le_trans; apply.
  by rewrite lerD2l ler_pdivrMr// ler_pMr// ler1n.
Unshelve. all: by end_near. Qed.

End parameterized_integral_continuous.

Section corollary_FTC1.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a b : R).

(* TODO: move? *)
Let within_continuous_restrict f a b : (a < b)%R ->
  {within `[a, b], continuous f} -> {in `]a, b[, continuous (f \_ `[a, b])}.
Proof.
move=> ab + x xab; move=> /(_ x).
rewrite {1}/continuous_at => xf.
rewrite /prop_for /continuous_at  patchE.
rewrite mem_set ?mulr1 /=; last exact: subset_itv_oo_cc.
exact: cvg_patch.
Qed.

Corollary continuous_FTC2 f F a b : (a < b)%R ->
  {within `[a, b], continuous f} ->
  derivable_oo_LRcontinuous F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof.
move=> ab cf dF F'f.
pose fab := f \_ `[a, b].
pose G x := (\int[mu]_(t in `[a, x]) fab t)%R.
have iabf : mu.-integrable `[a, b] (EFin \o f).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
have G'f : {in `]a, b[, forall x, G^`() x = fab x /\ derivable G x 1}.
  move=> x /[!in_itv]/= /andP[ax xb].
  have ifab : mu.-integrable `[a, b] (EFin \o fab).
    by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIid.
  have cfab : {for x, continuous fab}.
    by apply: within_continuous_restrict => //; rewrite in_itv/= ax xb.
  by have [] := continuous_FTC1_closed xb ifab ax cfab.
have F'G'0 : {in `]a, b[, (F^`() - G^`() =1 cst 0)%R}.
  move=> x xab; rewrite !fctE (G'f x xab).1 /fab.
  by rewrite patchE mem_set/= ?F'f ?subrr//; exact: subset_itv_oo_cc.
have [k FGk] : exists k : R, {in `]a, b[, (F - G =1 cst k)%R}.
  have : {in `]a, b[ &, forall x y, (F x - G x = F y - G y)%R}.
    move=> x y xab yab.
    wlog xLy : x y xab yab / (x <= y)%R.
      move=> abFG; have [|/ltW] := leP x y; first exact: abFG.
      by move/abFG => /(_ yab xab).
    move: xLy; rewrite le_eqVlt => /predU1P[->//|xy].
    have [| |] := @MVT _ (F \- G)%R (F^`() - G^`())%R x y xy.
    - move=> z zxy; have zab : z \in `]a, b[.
        move: z zxy; apply: subset_itvW => //.
        + by move: xab; rewrite in_itv/= => /andP[/ltW].
        + by move: yab; rewrite in_itv/= => /andP[_ /ltW].
      have Fz1 : derivable F z 1.
        by case: dF => /= + _ _; apply; rewrite inE in zab.
      have Gz1 : derivable G z 1 by have [|] := G'f z.
      apply: DeriveDef.
      + by apply: derivableB; [exact: Fz1|exact: Gz1].
      + by rewrite deriveB -?derive1E; [by []|exact: Fz1|exact: Gz1].
    - apply: derivable_within_continuous => z zxy.
      apply: derivableB.
      + case: dF => /= + _ _; apply.
        apply: subset_itvSoo zxy => //.
        by move: xab; rewrite in_itv/= => /andP[].
        by move: yab; rewrite in_itv/= => /andP[].
      + apply: (G'f _ _).2; apply: subset_itvSoo zxy => //.
        by move: xab; rewrite in_itv/= => /andP[].
        by move: yab; rewrite in_itv/= => /andP[].
    - move=> z zxy; rewrite F'G'0.
        by rewrite /cst/= mul0r => /eqP; rewrite subr_eq0 => /eqP.
      apply: subset_itvSoo zxy => //=; rewrite bnd_simp.
      * by move: xab; rewrite in_itv/= => /andP[/ltW].
      * by move: yab; rewrite in_itv/= => /andP[_ /ltW].
  move=> H; pose c := ((a + b) / 2)%R.
  exists (F c - G c)%R => u /(H u c); apply.
  by rewrite in_itv/= midf_lt//= midf_lt.
have [c GFc] : exists c : R, forall x, x \in `]a, b[ -> (F x - G x)%R = c.
  by exists k => x xab; rewrite -[k]/(cst k x) -(FGk x xab).
case: (dF) => _ Fa Fb.
have GacFa : G x @[x --> a^'+] --> (- c + F a)%R.
  have Fap : Filter a^'+ by exact: at_right_proper_filter.
  have GFac : (G x - F x)%R @[x --> a^'+] --> (- c)%R.
    apply/cvgrPdist_le => /= e e0; near=> t.
    rewrite opprB GFc; last by rewrite in_itv/=; apply/andP.
    by rewrite addNr normr0 ltW.
  have := @cvgD _ _ _ _ Fap _ _ _ _ GFac Fa.
  rewrite (_ : (G \- F)%R + F = G)//.
  by apply/funext => x/=; rewrite subrK.
have GbcFb : G x @[x --> b^'-] --> (- c + F b)%R.
  have Fbn : Filter b^'- by exact: at_left_proper_filter.
  have GFbc : (G x - F x)%R @[x --> b^'-] --> (- c)%R.
    apply/cvgrPdist_le => /= e e0; near=> t.
    rewrite opprB GFc; last by rewrite in_itv/=; apply/andP.
    by rewrite addNr normr0 ltW.
  have := @cvgD _ _ _ _ Fbn _ _ _ _ GFbc Fb.
  rewrite (_ : (G \- F)%R + F = G)//.
  by apply/funext => x/=; rewrite subrK.
have contF : {within `[a, b], continuous F}.
  apply/(continuous_within_itvP _ ab); split => //.
  move=> z zab; apply/differentiable_continuous/derivable1_diffP.
  by case: dF => /= + _ _; exact.
have iabfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //; rewrite setIidr.
have Ga : G x @[x --> a^'+] --> G a.
   have := parameterized_integral_cvg_left ab iabfab.
   rewrite (_ : 0 = G a)%R.
     by move=> /left_right_continuousP[].
   by rewrite /G set_itv1 Rintegral_set1.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (parameterized_integral_cvg_at_left ab iabfab).
have Ga0 : G a = 0%R by rewrite /G set_itv1// Rintegral_set1.
have cE : c = F a.
  apply/eqP; rewrite -(opprK c) eq_sym -addr_eq0 addrC.
  by have := cvg_unique _ GacFa Ga; rewrite Ga0 => ->.
have GbFbc : G b = (F b - c)%R.
  by have := cvg_unique _ GbcFb Gb; rewrite addrC => ->.
rewrite -EFinB -cE -GbFbc /G /Rintegral/= fineK//.
  rewrite integralEpatch//=.
  by under eq_integral do rewrite restrict_EFin.
exact: integrable_fin_num.
Unshelve. all: by end_near. Qed.

Lemma ge0_continuous_FTC2y (f F : R -> R) a (l : R) :
  (forall x, a <= x -> 0 <= f x)%R ->
  {within `[a, +oo[, continuous f} ->
  F x @[x --> +oo%R] --> l ->
  (forall x, a < x -> derivable F x 1)%R -> F x @[x --> a^'+] --> F a ->
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, +oo[) (f x)%:E = l%:E - (F a)%:E)%E.
Proof.
move=> f_ge0 cf Fxl dF Fa dFE.
have mf : measurable_fun `]a, +oo[ f.
  apply: open_continuous_measurable_fun => //.
  by move: cf => /continuous_within_itvcyP[/in_continuous_mksetP cf _].
rewrite -integral_itv_obnd_cbnd// itv_bndy_bigcup_BRight seqDU_bigcup_eq.
rewrite ge0_integral_bigcup//=; last 3 first.
- by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
- by rewrite -seqDU_bigcup_eq -itv_bndy_bigcup_BRight; exact: measurableT_comp.
- move=> x/=; rewrite -seqDU_bigcup_eq -itv_bndy_bigcup_BRight/=.
  by rewrite /= in_itv/= => /andP[/ltW + _]; rewrite lee_fin; exact: f_ge0.
have dFEn n : {in `]a + n%:R, a + n.+1%:R[, F^`() =1 f}.
  apply: in1_subset_itv dFE.
  apply: subset_trans (subset_itvl _) (subset_itvr _) => //=.
  by rewrite bnd_simp lerDl.
have liml : limn (EFin \o (fun k => F (a + k%:R))) = l%:E.
  apply/cvg_lim => //.
  apply: cvg_EFin; first exact: nearW.
  apply/((cvg_pinftyP F l).1 Fxl)/cvgryPge => r.
  by near do rewrite -lerBlDl; exact: nbhs_infty_ger.
transitivity (\sum_(0 <= i <oo) ((F (a + i.+1%:R))%:E - (F (a + i%:R))%:E)).
  transitivity (\sum_(0 <= i <oo)
      \int[mu]_(x in seqDU (fun k => `]a, (a + k%:R)]%classic) i.+1) (f x)%:E).
    apply/cvg_lim => //; rewrite -cvg_shiftS/=.
    under eq_cvg.
      move=> k /=; rewrite big_nat_recl//.
      rewrite /seqDU addr0 set_itvoc0// set0D integral_set0 add0r.
      over.
    apply: cvg_toP => //; apply: is_cvg_nneseries => n _.
    rewrite integral_ge0//= => x []; rewrite in_itv/= => /andP[/ltW + _] _.
    by rewrite lee_fin; exact: f_ge0.
  apply: eq_eseriesr => n _.
  rewrite seqDUE/= integral_itv_obnd_cbnd; last first.
    apply/measurable_fun_itv_bndo_bndcP.
    apply: open_continuous_measurable_fun => //.
    move: cf => /continuous_within_itvcyP[cf _] x.
    rewrite inE/= in_itv/= => /andP[anx _].
    by apply: cf; rewrite in_itv/= andbT (le_lt_trans _ anx)// lerDl.
  apply: continuous_FTC2 (dFEn n).
  - by rewrite ltrD2l ltr_nat.
  - have : {within `[a, +oo[, continuous f}.
      apply/continuous_within_itvcyP => //.
      by move: cf => /continuous_within_itvcyP[].
    apply: continuous_subspaceW.
    apply: subset_trans (subset_itvl _) (subset_itvr _) => //=.
    by rewrite bnd_simp lerDl.
  - split => /=.
    + move=> x; rewrite in_itv/= => /andP[anx _].
      by apply/dF; rewrite (le_lt_trans _ anx)// lerDl.
    + move: n => [|n]; first by rewrite addr0.
      have : {within `[a + n.+1%:R, a + n.+2%:R], continuous F}.
        apply: derivable_within_continuous => /= x.
        rewrite in_itv/= => /andP[aSn _].
        by apply: dF; rewrite (lt_le_trans _ aSn)// ltrDl.
      move/continuous_within_itvP.
      by rewrite ltrD2l ltr_nat ltnS => /(_ (ltnSn _))[].
  - have : {within `[a + n%:R + 2^-1%R, a + n.+1%:R], continuous F}.
      apply: derivable_within_continuous => x.
      rewrite in_itv/= => /andP[aSn _].
      by apply: dF; rewrite (lt_le_trans _ aSn)// -addrA ltrDl ltr_wpDl.
    move/continuous_within_itvP.
    suff: (a + n%:R + 2^-1 < a + n.+1%:R)%R by move=> /[swap] /[apply] => -[].
    by rewrite -[in ltRHS]natr1 addrA ltrD2l invf_lt1// ltr1n.
rewrite nondecreasing_telescope_sumey.
- by rewrite addr0 EFinN; congr (_ - _).
- by rewrite liml.
- apply/nondecreasing_seqP => n; rewrite -subr_ge0.
  have isdF (x : R) : x \in `]a + n%:R, a + n.+1%:R[ -> is_derive x 1%R F (f x).
    rewrite in_itv/= => /andP[anx _].
    rewrite -dFE; last by rewrite in_itv/= andbT (le_lt_trans _ anx)// lerDl.
    rewrite derive1E.
    by apply/derivableP/dF; rewrite (le_lt_trans _ anx)// lerDl.
  have [| |r ranaSn ->] := MVT _ isdF.
  + by rewrite ltrD2l ltr_nat.
  + move : n isdF => [_ |n _].
    + have : {within `[a, +oo[, continuous F}.
        apply/continuous_within_itvcyP; split => // x.
        rewrite in_itv/= andbT => ax.
        by apply: differentiable_continuous; exact/derivable1_diffP/dF.
      by apply: continuous_subspaceW; rewrite addr0; exact: subset_itvl.
    + apply: @derivable_within_continuous => x.
      rewrite in_itv/= => /andP[aSnx _].
      by apply: dF; rewrite (lt_le_trans _ aSnx)// ltrDl.
  + move: ranaSn; rewrite in_itv/= => /andP[/ltW anr _].
    rewrite mulr_ge0//; last by rewrite subr_ge0 lerD2l ler_nat.
    by rewrite f_ge0// (le_trans _ anr)// lerDl.
Unshelve. end_near. Qed.

Lemma Rintegral_ge0_continuous_FTC2y (f F : R -> R) a (l : R) :
  (forall x, a <= x -> 0 <= f x)%R ->
  {within `[a, +oo[, continuous f} ->
  F x @[x --> +oo%R] --> l ->
  (forall x, a < x -> derivable F x 1)%R -> F x @[x --> a^'+] --> F a ->
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, +oo[) (f x) = l - F a)%R.
Proof.
move=> f_ge0 cf Fxl dF Fa dFE.
by rewrite /Rintegral (ge0_continuous_FTC2y f_ge0 cf Fxl dF Fa dFE) -EFinD.
Qed.

Lemma le0_continuous_FTC2y (f F : R -> R) a (l : R) :
  (forall x, a <= x -> f x <= 0)%R ->
  {within `[a, +oo[, continuous f} ->
  F x @[x --> +oo%R] --> l ->
  (F x @[x --> a^'+] --> F a) ->
  (forall x, (a < x)%R -> derivable F x 1) ->
  {in `]a, +oo[, F^`() =1 f} ->
  \int[mu]_(x in `[a, +oo[) (f x)%:E = l%:E - (F a)%:E.
Proof.
move=> f_ge0 cf Fl Fa dF dFE; rewrite -[LHS]oppeK -integralN/=; last first.
  rewrite adde_defN ge0_adde_def => //=; rewrite inE.
    rewrite oppe_ge0 le_eqVlt; apply/predU1P; left.
    apply: integral0_eq => /= x; rewrite in_itv/= => /andP[ax _].
    by rewrite funeposE -EFin_max; congr EFin; exact/max_idPr/f_ge0.
  apply: integral_ge0 => /= x; rewrite in_itv/= => /andP[ax _].
  by rewrite funenegE -fine_max// lee_fin le_max lexx orbT.
rewrite (@ge0_continuous_FTC2y (- f)%R (- F)%R _ (- l)%R).
- by rewrite oppeB// EFinN oppeK.
- by move=> x ax; rewrite oppr_ge0 f_ge0.
- move: cf => /continuous_within_itvcyP[cf fa].
  rewrite continuous_within_itvcyP; split; last exact: cvgN.
  by move=> x ax; exact/continuousN/cf.
- exact: cvgN.
- by move=> x ax; exact/derivableN/dF.
- exact: cvgN.
- move=> x ax; rewrite derive1E deriveN.
    by rewrite -derive1E dFE.
  by apply: dF; move: ax; rewrite in_itv/= andbT.
Qed.

End corollary_FTC1.

Section integration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma integration_by_parts F G f g a b : (a < b)%R ->
    {within `[a, b], continuous f} ->
    derivable_oo_LRcontinuous F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_LRcontinuous G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x)%:E = (F b * G b - F a * G a)%:E -
  \int[mu]_(x in `[a, b]) (f x * G x)%:E.
Proof.
move=> ab cf Fab Ff cg Gab Gg.
have cfg : {within `[a, b], continuous (f * G + F * g)%R}.
  apply/subspace_continuousP => x abx; apply: cvgD.
  - apply: cvgM.
    + by move/subspace_continuousP : cf; exact.
    + have := derivable_oo_LRcontinuous_within Gab.
      by move/subspace_continuousP; exact.
  - apply: cvgM.
    + have := derivable_oo_LRcontinuous_within Fab.
      by move/subspace_continuousP; exact.
    + by move/subspace_continuousP : cg; exact.
have FGab : derivable_oo_LRcontinuous (F * G)%R a b.
  move: Fab Gab => /= [abF FFa FFb] [abG GGa GGb];split; [|exact:cvgM..].
  by move=> z zab; apply: derivableM; [exact: abF|exact: abG].
have FGfg : {in `]a, b[, (F * G)^`() =1 f * G + F * g}%R.
  move: Fab Gab => /= [abF FFa FFb] [abG GGa GGb] z zba.
  rewrite derive1E deriveM; [|exact: abF|exact: abG].
  by rewrite -derive1E Gg// -derive1E Ff// addrC (mulrC f).
have := continuous_FTC2 ab cfg FGab FGfg; rewrite -EFinB => <-.
under [X in _ = X - _]eq_integral do rewrite EFinD.
have ? : mu.-integrable `[a, b] (fun x => ((f * G) x)%:E).
  apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx; apply: cvgM.
  + by move/subspace_continuousP : cf; exact.
  + have := derivable_oo_LRcontinuous_within Gab.
    by move/subspace_continuousP; exact.
rewrite /= integralD//=.
- by rewrite addeAC subee ?add0e// integrable_fin_num.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx;apply: cvgM.
  + have := derivable_oo_LRcontinuous_within Fab.
    by move/subspace_continuousP; exact.
  + by move/subspace_continuousP : cg; exact.
Qed.

End integration_by_parts.

Section Rintegration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma Rintegration_by_parts F G f g a b :
    (a < b)%R ->
    {within `[a, b], continuous f} ->
    derivable_oo_LRcontinuous F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_LRcontinuous G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x) = (F b * G b - F a * G a) -
  \int[mu]_(x in `[a, b]) (f x * G x).
Proof.
move=> ab cf Fab Ff cg Gab Gg.
rewrite [in LHS]/Rintegral (@integration_by_parts R F G f g)// fineB//.
suff: mu.-integrable `[a, b] (fun x => (f x * G x)%:E).
  move=> /integrableP[? abfG]; apply: fin_real.
  rewrite (_ : -oo = - +oo)%E// -lte_absl.
  by apply: le_lt_trans abfG; exact: le_abse_integral.
apply: continuous_compact_integrable.
  exact: segment_compact.
move=> /= z; apply: continuousM; [exact: cf|].
exact: (derivable_oo_LRcontinuous_within Gab).
Qed.

End Rintegration_by_parts.

Section integration_by_substitution_preliminaries.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma increasing_image_oo F (a b : R) : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  F @` `]a, b[ `<=` `]F a, F b[.
Proof.
move=> ab iF ? [x /= xab <-].
move: xab; rewrite !in_itv/= => /andP[ax xb].
by apply/andP; split; apply: iF; rewrite // in_itv/= ?lexx !ltW.
Qed.

Lemma decreasing_image_oo F (a b : R) : (a < b)%R ->
  {in `[a, b] &, {homo F : x y /~ (x < y)%R}} ->
  F @` `]a, b[ `<=` `]F b, F a[.
Proof.
move=> ab iF ? [x /= xab <-].
move: xab; rewrite !in_itv/= => /andP[ax xb].
by apply/andP; split; apply: iF; rewrite // in_itv/= ?lexx !ltW.
Qed.

Lemma increasing_cvg_at_right_comp F G a (b : itv_bound R) (l : R) :
  (BRight a < b)%O ->
  {in Interval (BLeft a) b &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'+] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab incrF cFa GFa.
apply/cvgrPdist_le => /= e e0.
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFa] := GFa.
have := cvg_at_right_within cFa.
move=> /cvgrPdist_lt/(_ _ d0)[d' /= d'0 {}cFa].
move: b ab incrF => [[b|b]|[//|]] ab incrF; rewrite bnd_simp in ab.
- near=> t.
  apply: GFa; last first.
    by apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
  apply: cFa => //=.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
- near=> t.
  apply: GFa; last first.
    apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split => //.
      exact: ltW.
    by near: t; exact: nbhs_right_le.
  apply: cFa => //=.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
- near=> t.
  apply: GFa; last first.
    by apply: incrF; rewrite //in_itv/= ?lexx//; exact/andP.
  apply: cFa => //=.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma increasing_cvg_at_left_comp F G (a : itv_bound R) b (l : R) :
  (a < BLeft b)%O ->
  {in Interval a (BRight b) &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'-] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab incrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d /= d0 {}GFb] := GFb.
have := cvg_at_left_within cFb.
move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
move: a ab incrF => [[a|a]|[|//]] ab incrF; rewrite bnd_simp in ab.
- near=> t.
  apply: GFb; last first.
    rewrite incrF// in_itv/= ?lexx ?andbT//.
      apply/andP; split => //.
      by near: t; exact: nbhs_left_ge.
    exact: ltW.
  rewrite /ball_/= cFb//= gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
- near=> t.
  apply: GFb; last first.
    rewrite incrF// in_itv/= ?lexx ?andbT//.
    exact/andP.
  rewrite /ball_/= cFb//= gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
- near=> t.
  apply: GFb; last by rewrite incrF// in_itv/=.
  apply: cFb => //=; rewrite gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_right_comp F G a (b : itv_bound R) (l : R) :
  (BRight a < b)%O ->
  {in Interval (BLeft a) b &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'-] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab decrF cFa GFa.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFa] := GFa.
have := cvg_at_right_within cFa.
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFa].
move: b ab decrF => [[b|b]|[//|]] ab decrF; rewrite bnd_simp in ab.
- near=> t.
  apply: GFa; last by rewrite decrF// in_itv/= ?lexx//; apply/andP; split.
  apply: cFa => //=; rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
- near=> t.
  apply: GFa; last first.
    rewrite decrF ?in_itv//= ?lexx//; apply/andP; split => //.
      by near: t; exact: nbhs_right_le.
    exact: ltW.
  apply: cFa => //=.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
- near=> t.
  apply: GFa; last first.
    by rewrite decrF ?in_itv//= ?lexx//; exact/andP.
  apply: cFa => //=.
  rewrite ltr0_norm// ?subr_lt0// opprB.
  by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_left_comp F G (a : itv_bound R) b (l : R) :
  (a < BLeft b)%O ->
  {in Interval a (BRight b) &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'+] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab decrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFb] := GFb.
have := cvg_at_left_within cFb. (* different point from gt0 version *)
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFb].
move: a ab decrF => [[a|a]|[|//]] ab decrF; rewrite bnd_simp in ab.
- near=> t.
  apply: GFb; last first.
    apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split => //.
      exact: ltW.
    by near: t; exact: nbhs_left_ge.
  apply: cFb => //=.
  rewrite gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
- near=> t.
  apply: GFb; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
  apply: cFb => //=.
  rewrite gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
- near=> t.
  apply: GFb; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
  apply: cFb => //=.
  rewrite gtr0_norm// ?subr_gt0//.
  by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

End integration_by_substitution_preliminaries.

(* PR in progress *)
Lemma cvgNy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> -oo] --> l <-> (f \o -%R) x @[x --> +oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg -oo _ f_opp) [in X in X <-> _]fmap_comp ninftyN.
Qed.

(* PR in progress *)
Lemma cvgy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> +oo] --> l <-> (f \o -%R) x @[x --> -oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg +oo _ f_opp) [in X in X <-> _]fmap_comp ninfty.
Qed.

Section integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma integration_by_substitution_decreasing F G a b : (a <= b)%R ->
  {in `[a, b] &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> b^'-]) ->
  derivable_oo_LRcontinuous F a b ->
  {within `[F b, F a], continuous G} ->
  \int[mu]_(x in `[F b, F a]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * - F^`()) x)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<- *|]; first by rewrite !set_itv1 !integral_set1.
move=> ab decrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] Fab cG.
have cF := derivable_oo_LRcontinuous_within Fab.
have FbFa : (F b < F a)%R by apply: decrF; rewrite //= in_itv/= (ltW ab) lexx.
have mGFF' : measurable_fun `]a, b[ ((G \o F) * F^`())%R.
  apply: measurable_funM.
  - apply: (measurable_comp (measurable_itv `]F b, F a[)).
    + exact: decreasing_image_oo.
    + apply: subspace_continuous_measurable_fun => //.
      by apply: continuous_subspaceW cG; exact/subset_itv_oo_cc.
    + apply: subspace_continuous_measurable_fun => //.
      by apply: continuous_subspaceW cF; exact/subset_itv_oo_cc.
  - apply: subspace_continuous_measurable_fun => //.
    by apply: continuous_in_subspaceT => x; rewrite inE/= => /cF'.
have {}mGFF' : measurable_fun `[a, b] ((G \o F) * F^`())%R.
  exact: measurable_fun_itv_cc mGFF'.
have intG : mu.-integrable `[F b, F a] (EFin \o G).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
pose PG x := parameterized_integral mu (F b) x G.
have PGFbFa : derivable_oo_LRcontinuous PG (F b) (F a).
  have [/= dF rF lF] := Fab; split => /=.
  - move=> x xFbFa /=.
    have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFa intG _ _).1 => /=.
      by move: xFbFa; rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFbFa).
  - have := parameterized_integral_continuous (ltW FbFa) intG.
    by move=> /(continuous_within_itvP _ FbFa)[].
  - exact: parameterized_integral_cvg_at_left.
rewrite (@continuous_FTC2 _ _ PG _ _ FbFa cG); last 2 first.
- split.
  + move=> x /[dup]xFbFa; rewrite in_itv/= => /andP[Fbx xFa].
    apply: (continuous_FTC1 xFa intG Fbx _).1.
    by move: cG => /(continuous_within_itvP _ FbFa)[+ _ _]; exact.
  + have := parameterized_integral_continuous (ltW FbFa) intG.
    by move=> /(continuous_within_itvP _ FbFa)[].
  + exact: parameterized_integral_cvg_at_left.
- move=> x xFbFa.
  have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
  apply: (continuous_FTC1 xFa _ _ _).2 => //=.
    by move: xFbFa; rewrite lte_fin in_itv/= => /andP[].
  exact: (within_continuous_continuous _ _ xFbFa).
set f  := fun x => if x == a then r else if x == b then l else F^`() x.
have fE : {in `]a, b[, F^`() =1 f}.
  by move=> x; rewrite in_itv/= => /andP[ax xb]; rewrite /f gt_eqF// lt_eqF.
have DPGFE : {in `]a, b[, (- (PG \o F))%R^`() =1 ((G \o F) * (- f))%R}.
  move=> x /[dup]xab /andP[ax xb]; rewrite derive1_comp //; last first.
    apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
      by case: Fab => + _ _; exact.
    by case: PGFbFa => + _ _; apply; exact: decreasing_image_oo.
  have /(@derive_val _ _ _ _ _ -%R) := @is_deriveNid _ _ (PG (F x)) 1%R.
  rewrite fctE -derive1E => ->; rewrite mulN1r mulrN; congr -%R.
  rewrite derive1_comp; last 2 first.
  - by case: Fab => + _ _; exact.
  - by case: PGFbFa => [+ _ _]; apply; exact: decreasing_image_oo.
  rewrite fE//; congr *%R.
  have /[dup]FxFbFa : F x \in `]F b, F a[ by exact: decreasing_image_oo.
  rewrite in_itv/= => /andP[FbFx FxFa].
  apply: (continuous_FTC1 FxFa intG FbFx _).2 => //=.
  exact: (within_continuous_continuous _ _ FxFbFa).
rewrite -[LHS]oppeK oppeB// addrC.
under eq_integral do rewrite mulrN EFinN.
rewrite oppeD//= -(continuous_FTC2 ab _ _ DPGFE); last 2 first.
- apply/(continuous_within_itvP _ ab); split.
  + move=> x xab; apply: continuousM; first apply: continuous_comp.
    * by move: cF => /(continuous_within_itvP _ ab)[+ _ _]; exact.
    * move/(continuous_within_itvP _ FbFa) : cG => [+ _ _]; apply.
      exact: decreasing_image_oo.
    * have : -%R F^`() @ x --> (- f x)%R.
        by rewrite -fE//; apply: cvgN; exact: cF'.
      apply: cvg_trans; apply: near_eq_cvg.
      apply: (@open_in_nearW _ _ `]a, b[) ; last by rewrite inE.
        exact: interval_open.
      by move=> z; rewrite inE/= => zab; rewrite fctE fE.
  + apply: cvgM.
      apply: (decreasing_cvg_at_right_comp _ decrF) => //.
      * by move/continuous_within_itvP : cF => /(_ ab)[].
      * by move/continuous_within_itvP : cG => /(_ FbFa)[].
    rewrite fctE {2}/f eqxx; apply: cvgN.
    apply: cvg_trans F'ar; apply: near_eq_cvg.
    by near=> z; rewrite fE// in_itv/=; apply/andP; split.
  + apply: cvgM.
      apply: (decreasing_cvg_at_left_comp _ decrF) => //.
      * by move/continuous_within_itvP : cF => /(_ ab)[].
      * by move/continuous_within_itvP : cG => /(_ FbFa)[].
    rewrite fctE {2}/f gt_eqF// eqxx.
    apply: cvgN; apply: cvg_trans F'bl; apply: near_eq_cvg.
    by near=> z; rewrite fE// in_itv/=; apply/andP; split.
- have [/= dF rF lF] := Fab.
  have := derivable_oo_LRcontinuous_within PGFbFa.
  move=> /(continuous_within_itvP _ FbFa)[_ PGFb PGFa]; split => /=.
  - move=> x xab; apply/derivable1_diffP; apply: differentiable_comp => //.
    apply: differentiable_comp; apply/derivable1_diffP.
      by case: Fab => + _ _; exact.
    by case: PGFbFa => + _ _; apply; exact: decreasing_image_oo.
  - apply: cvgN; apply/cvgrPdist_le => /= e e0.
    have /cvgrPdist_le/(_ e e0)[d /= d0 {}PGFa] := PGFa.
    have := cvg_at_right_within rF.
    move/cvgrPdist_lt => /(_ _ d0)[d' /= d'0 {}cFa].
    near=> t.
    apply: PGFa; last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFa => //=.
    rewrite ltr0_norm// ?subr_lt0// opprB.
    by near: t; exact: nbhs_right_ltDr.
  - apply: cvgN; apply/cvgrPdist_le => /= e e0.
    have /cvgrPdist_le/(_ e e0)[d /= d0 {}PGFb] := PGFb.
    have := cvg_at_left_within lF.
    move/cvgrPdist_lt => /(_ _ d0)[d' /= d'0 {}cFb].
    near=> t.
    apply: PGFb; last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFb => //=.
    rewrite gtr0_norm// ?subr_gt0//.
    by near: t; exact: nbhs_left_ltBl.
apply: eq_integral_itv_bounded.
- rewrite mulrN; apply: measurableT_comp => //.
  apply: (eq_measurable_fun ((G \o F) * F^`())%R) => //.
    by move=> x; rewrite inE/= => xab; rewrite !fctE fE.
  by move: mGFF'; apply: measurable_funS => //; exact: subset_itv_oo_cc.
- apply: measurableT_comp => //; apply: measurable_funS mGFF' => //.
  exact: subset_itv_oo_cc.
- by move=> x /[!inE] xab; rewrite mulrN !fctE fE.
Unshelve. all: end_near. Qed.

Lemma integration_by_substitution_oppr G a b : (a <= b)%R ->
  {within `[(- b)%R, (- a)%R], continuous G} ->
  \int[mu]_(x in `[(- b)%R, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, b]) ((G \o -%R) x)%:E.
Proof.
move=> ab cG; have Dopp: (@GRing.opp R)^`() = cst (-1)%R.
  by apply/funext => z; rewrite derive1E derive_val.
rewrite (@integration_by_substitution_decreasing -%R)//.
- apply: eq_integral => //= x /[!inE] xab; congr (EFin _).
  by rewrite !fctE -[RHS]mulr1 derive1E deriveN// opprK derive_val.
- by move=> ? ? _ _; rewrite ltrN2.
- by rewrite Dopp => ? _; exact: cvg_cst.
- by rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
- by rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
- split => //.
  + by rewrite -at_leftN; exact: cvg_at_left_filter.
  + by rewrite -at_rightN; exact: cvg_at_right_filter.
Qed.

Lemma integration_by_substitution_increasing F G a b : (a <= b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> b^'-]) ->
  derivable_oo_LRcontinuous F a b ->
  {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<- *|]; first by rewrite !set_itv1 !integral_set1.
move=> ab incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] Fab cG.
transitivity (\int[mu]_(x in `[F a, F b]) (((G \o -%R) \o -%R) x)%:E).
  by apply/eq_integral => x ? /=; rewrite opprK.
have FaFb : (F a < F b)%R by rewrite incrF// in_itv/= lexx (ltW ab).
have cGN : {within `[- F b, - F a]%classic%R, continuous (G \o -%R)}.
  apply/continuous_within_itvP; [by rewrite ltrN2|split].
  - move=> x /[dup]xab /[!in_itv]/= /andP[ax xb].
    apply: continuous_comp; first exact: continuousN.
  - move/(continuous_within_itvP _ FaFb) : cG => [+ _ _]; apply.
    by rewrite in_itv/= ltrNr xb ltrNl.
  - move/(continuous_within_itvP _ FaFb) : cG => [_ _].
    by rewrite /= opprK => /cvg_at_leftNP.
  - move/(continuous_within_itvP _ FaFb) : cG => [_ + _].
    by rewrite /= opprK => /cvg_at_rightNP.
rewrite -(integration_by_substitution_oppr (ltW FaFb))//.
rewrite (@integration_by_substitution_decreasing (- F)%R); first last.
- exact: cGN.
- split; [|by apply: cvgN; case: Fab..].
  by move=> x xab; apply: derivableN; case: Fab => + _ _; exact.
- apply/cvg_ex; exists (- l)%R.
  move/cvgN : F'bl; apply: cvg_trans; apply: near_eq_cvg.
  near=> z; rewrite fctE !derive1E deriveN//.
  by case: Fab => + _ _; apply; rewrite in_itv/=; apply/andP; split.
- apply/cvg_ex; exists (- r)%R.
  move/cvgN : F'ar; apply: cvg_trans; apply: near_eq_cvg.
  near=> z; rewrite fctE !derive1E deriveN//.
  by case: Fab => + _ _; apply; rewrite in_itv/=; apply/andP; split.
- move=> x xab; rewrite /continuous_at derive1E deriveN; last first.
    by case: Fab => + _ _; exact.
  rewrite -derive1E.
  have /cvgN := cF' _ xab; apply: cvg_trans; apply: near_eq_cvg.
  near=> y; rewrite fctE !derive1E deriveN//.
  by case: Fab => + _ _; apply; near: y; exact: near_in_itvoo.
- by move=> x y xab yab yx; rewrite ltrN2 incrF.
- exact/ltW.
have mGF : measurable_fun `]a, b[ (G \o F).
  apply: (@measurable_comp _ _ _ _ _ _ `]F a, F b[%classic) => //.
  - move=> /= _ [x] /[!in_itv]/= /andP[ax xb] <-.
    by rewrite incrF ?incrF// in_itv/= ?lexx/= ?(ltW ab)//= ?(ltW ax) ?(ltW xb).
  - apply: subspace_continuous_measurable_fun => //.
    by apply: continuous_subspaceW cG; exact/subset_itv_oo_cc.
  - apply: subspace_continuous_measurable_fun => //.
    by apply: derivable_within_continuous => x xab; case: Fab => + _ _; exact.
have mF' : measurable_fun `]a, b[ F^`().
  apply: subspace_continuous_measurable_fun => //.
  by apply: continuous_in_subspaceT => x /[!inE] xab; exact: cF'.
rewrite integral_itv_bndoo//; last first.
  rewrite compA -(compA G -%R) (_ : -%R \o -%R = id); last first.
    by apply/funext => y; rewrite /= opprK.
  apply: measurable_funM => //; apply: measurableT_comp => //.
  apply: (@eq_measurable_fun _ _ _ _ _ (- F^`())%R).
    move=> x /[!inE] xab; rewrite [in RHS]derive1E deriveN -?derive1E//.
    by case: Fab => + _ _; apply.
  exact: measurableT_comp.
rewrite [in RHS]integral_itv_bndoo//; last exact: measurable_funM.
apply: eq_integral => x /[!inE] xab; rewrite !fctE !opprK derive1E deriveN.
- by rewrite opprK -derive1E.
- by case: Fab => + _ _; exact.
Unshelve. all: end_near. Qed.

Lemma decreasing_ge0_integration_by_substitutiony F G a :
  {in `[a, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  derivable_oy_Rcontinuous F a -> F x @[x --> +oo%R] --> -oo%R ->
  {within `]-oo, F a], continuous G} ->
  {in `]-oo, F a[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F a]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> decrF cdF /cvg_ex[/= dFa cdFa] /cvg_ex[/= dFoo cdFoo].
move=> [dF cFa] Fny /continuous_within_itvNycP[cG cGFa] G0.
have mG n : measurable_fun `](F (a + n.+1%:R)), (F a)] G.
  apply/measurable_fun_itv_bndo_bndcP.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[_ xFa].
  by apply: cG; rewrite in_itv.
have mGFNF' i : measurable_fun `[a, (a + i.+1%:R)[ ((G \o F) * - F^`())%R.
  apply/measurable_fun_itv_obnd_cbndP.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  apply: continuousM; last first.
    apply: continuousN.
    by apply: cdF; rewrite in_itv/= andbT.
  apply: continuous_comp.
    have := derivable_within_continuous dF.
    rewrite continuous_open_subspace; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= andbT.
  by apply: cG; rewrite in_itv/=; apply: decrF; rewrite ?in_itv/= ?lexx ?ltW.
rewrite -integral_itv_bndo_bndc; last first.
  apply: open_continuous_measurable_fun => // x.
  by rewrite inE => /cG.
transitivity (limn (fun n => \int[mu]_(x in `[F (a + n%:R)%R, F a[) (G x)%:E)).
  rewrite (decreasing_itvNyo_bigcup decrF Fny).
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; first last.
  - exact: trivIset_seqDU.
  - rewrite -seqDU_bigcup_eq => x Fax; rewrite lee_fin G0//; move: x Fax.
    by apply: bigcup_sub => i _; exact: subset_itvr.
  - rewrite -seqDU_bigcup_eq.
    apply/measurable_EFinP/measurable_fun_bigcup => //.
    by move=> i; apply: measurable_funS (mG i) => //; exact: subset_itvW.
  - by move=> n; apply: measurableD => //;exact: bigsetU_measurable.
  apply: congr_lim; apply/funext => n.
  rewrite -ge0_integral_bigsetU//=; last 5 first.
    by move=> m; apply: measurableD => //; exact: bigsetU_measurable.
    exact: iota_uniq.
    exact: (@sub_trivIset _ _ _ [set: nat]).
    apply/measurable_EFinP.
    rewrite big_mkord -bigsetU_seqDU.
    apply: (measurable_funS _
        (@bigsetU_bigcup _ (fun k =>`]F (a + k.+1%:R)%R, _[%classic) _)).
      exact: bigcup_measurable.
    apply/measurable_fun_bigcup => //.
    by move=> i; apply: measurable_funS (mG i) => //; exact: subset_itvW.
  - move=> x xFaSkFa.
    apply: G0.
    move: xFaSkFa.
    rewrite big_mkord -bigsetU_seqDU.
    rewrite -(bigcup_mkord _ (fun k => `]F (a + k.+1%:R), F a[%classic)).
    by move: x; apply: bigcup_sub => k/= nk; exact: subset_itvr.
  rewrite -integral_itv_obnd_cbnd; last first.
    case: n => [|n].
      by rewrite addr0 set_itvoo0; exact: measurable_fun_set0.
    by apply: measurable_funS (mG n) => //; exact: subset_itvW.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord _ (fun k => `]F (a + k.+1%:R), F a[%classic)).
  exact/esym/decreasing_itvoo_bigcup.
transitivity (limn (fun n =>
    \int[mu]_(x in `]a, (a + n%:R)%R[) (((G \o F) * - F^`()) x)%:E)); last first.
  rewrite -integral_itv_obnd_cbnd; last first.
    rewrite (@itv_bndy_bigcup_BLeft_shift _ _ _ 1).
    under eq_bigcupr do rewrite addn1.
    apply/measurable_fun_bigcup => // n.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  rewrite (@itv_bndy_bigcup_BLeft_shift _ _ _ 1).
  under eq_bigcupr do rewrite addn1.
  rewrite seqDU_bigcup_eq ge0_integral_bigcup/=; last 4 first.
  - by move=> n; apply: measurableD => //; exact: bigsetU_measurable.
  - rewrite -seqDU_bigcup_eq; apply/measurable_fun_bigcup => // n.
    apply/measurable_EFinP; apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  - move=> x ax.
    have {}ax : (a < x)%R.
      move: ax; rewrite -seqDU_bigcup_eq => -[? _]/=.
      by rewrite in_itv/= => /andP[].
    rewrite fctE lee_fin mulr_ge0//.
    + apply: G0.
      by rewrite in_itv/= decrF ?in_itv ?andbT ?lexx//= ltW.
    + rewrite oppr_ge0.
      apply: (@decr_derive1_le0 _ _ `[a, +oo[).
      * by rewrite interior_itv => ?; rewrite inE/=; apply: dF.
      * by move=> ? ?; rewrite !inE/=; apply: decrF.
      * by rewrite interior_itv/= in_itv/= andbT.
  - exact: trivIset_seqDU.
  apply: congr_lim; apply/funext => n.
  rewrite -integral_bigsetU_EFin/=; last 4 first.
  - by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
  - exact: iota_uniq.
  - exact: (@sub_trivIset _ _ _ [set: nat]).
  - apply/measurable_EFinP.
    apply: (measurable_funS (measurable_itv `]a, (a + n.+1%:R)[)).
      rewrite big_mkord -bigsetU_seqDU.
      rewrite -(bigcup_mkord _ (fun k => `]a, (a + k.+1%:R)[%classic)).
      apply: bigcup_sub => k/= kn.
      by apply: subset_itvl; rewrite bnd_simp/= lerD2l ler_nat ltnS ltnW.
    by apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `]a, (a + k.+1%:R)[%classic)).
  rewrite eqEsubset; split.
    move: n => [|n]; first by rewrite addr0 set_itvoo0.
    by apply: (@bigcup_sup _ _ n) => /=.
  apply: bigcup_sub => k/= kn; apply: subset_itvl.
  by rewrite bnd_simp/= lerD2l ler_nat.
apply: congr_lim; apply/funext => -[|n].
  by rewrite addr0 set_itvco0 set_itvoo0 !integral_set0.
rewrite integral_itv_bndo_bndc; last first.
  apply/measurable_fun_itv_obnd_cbndP; apply: measurable_funS (mG n) => //.
  by apply: subset_itvl; rewrite bnd_simp.
rewrite integration_by_substitution_decreasing.
- rewrite integral_itv_bndo_bndc// ?integral_itv_obnd_cbnd//.
  + rewrite -setUitv1; last by rewrite bnd_simp ltrDl.
    rewrite measurable_funU//; split; last exact: measurable_fun_set1.
    by apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
  + by apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
- by rewrite lerDl.
- move=> x y /=; rewrite !in_itv/= => /andP[ax _] /andP[ay _] yx.
  by apply: decrF; rewrite //in_itv/= ?ax ?ay.
- move=> x; rewrite in_itv/= => /andP[ax _].
  by apply: cdF; rewrite in_itv/= ax.
- exact: (cvgP dFa).
- apply: (cvgP (F^`() (a + n.+1%:R))); apply/cvg_at_left_filter/cdF.
  by rewrite in_itv/= andbT ltr_pwDr.
- split.
  + move=> x; rewrite in_itv/= => /andP[ax _].
    by apply: dF; rewrite in_itv/= ax.
  + exact: cFa.
  + apply/cvg_at_left_filter/differentiable_continuous/derivable1_diffP/dF.
    by rewrite in_itv/= andbT ltr_pwDr.
- apply/continuous_within_itvP.
  + by rewrite decrF ?ltr_pwDr ?in_itv ?andbT//= lerDl.
  + split.
    * move=> y; rewrite in_itv/= => /andP[_ yFa].
      by apply: cG; rewrite in_itv/= yFa.
    * apply/cvg_at_right_filter/cG.
      by rewrite in_itv/= decrF ?in_itv/= ?andbT ?lerDl// ltr_pwDr.
    * exact: cGFa.
Qed.

Lemma ge0_integration_by_substitutionNy G a :
  {within `]-oo, (- a)%R], continuous G} ->
  {in `]-oo, (- a)%R[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) ((G \o -%R) x)%:E.
Proof.
move=> /continuous_within_itvNycP[cG GNa] G0.
have Dopp : (@GRing.opp R)^`() = cst (- 1)%R.
  by apply/funext => z; rewrite derive1E derive_val.
rewrite decreasing_ge0_integration_by_substitutiony//; last 7 first.
  by move=> x y _ _; rewrite ltrN2.
  by rewrite Dopp => ? _; exact: cst_continuous.
  by rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
  by rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
  split.
  - by [].
  - by apply: cvgN; exact: cvg_at_right_filter.
  exact/cvgNrNy.
  exact/continuous_within_itvNycP.
apply: eq_integral => x _; congr EFin.
rewrite fctE -[RHS]mulr1; congr *%R.
by rewrite fctE derive1E deriveN// opprK derive_id.
Qed.

Lemma increasing_ge0_integration_by_substitutiony F G a :
  {in `[a, +oo[ &, {homo F : x y / (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  derivable_oy_Rcontinuous F a -> F x @[x --> +oo%R] --> +oo%R->
  {within `[F a, +oo[, continuous G} ->
  {in `]F a, +oo[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `[F a, +oo[) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * F^`()) x)%:E.
Proof.
move=> incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'ool].
move=> [dF cFa] Fny /continuous_within_itvcyP[cG cGFa] G0.
transitivity (\int[mu]_(x in `[F a, +oo[) (((G \o -%R) \o -%R) x)%:E).
  by apply/eq_integral => x ? /=; rewrite opprK.
have cGN : {in `]-oo, - F a[%R, continuous (G \o -%R)}.
  move=> x; rewrite in_itv/= ltrNr => FaNx.
  apply: continuous_comp; first exact: continuousN.
  by apply: cG; rewrite in_itv/= FaNx.
rewrite -ge0_integration_by_substitutionNy//; last 2 first.
  apply/continuous_within_itvNycP; split => //.
  apply/cvg_at_rightNP.
  apply: cvg_toP; first by apply/cvg_ex; exists (G (F a)).
  by move/cvg_lim: cGFa => -> //; rewrite fctE opprK.
  by move=> x; rewrite in_itv/= ltrNr => FaNx; apply: G0; rewrite in_itv/= FaNx.
rewrite (@decreasing_ge0_integration_by_substitutiony (- F)%R); first last.
- move=> y; rewrite in_itv/= ltrNr => FaNy.
  by apply: G0; rewrite in_itv/= FaNy.
- apply/continuous_within_itvNycP; split => //.
  by rewrite fctE opprK; exact/cvg_at_rightNP.
- exact/cvgNrNy.
- split.
  + by move=> x ax; apply: derivableN; exact: dF.
  + exact: cvgN.
- apply/cvg_ex; exists (- l)%R.
  have /(_ (@filter_filter R _ proper_pinfty_nbhs)) := cvgN F'ool.
  apply: cvg_trans; apply: near_eq_cvg; near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF; rewrite in_itv/= andbT.
  by near: z; apply: nbhs_pinfty_gt; exact: num_real.
- apply/cvg_ex; exists (- r)%R.
  have /(_ (@filter_filter R _ (at_right_proper_filter a))) := cvgN F'ar.
  apply: cvg_trans; apply: near_eq_cvg; near=> z.
  rewrite derive1E deriveN -?derive1E//.
  by apply: dF; rewrite in_itv/= andbT.
- move=> x ax.
  rewrite /continuous_at derive1E deriveN -?derive1E; last exact: dF.
  have /(_ (nbhs_filter x)) := cvgN (cF' x ax).
  apply: cvg_trans; apply: near_eq_cvg; rewrite near_simpl/=; near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF.
  near: z; rewrite near_nbhs.
  apply: (@open_in_nearW _ _ `]a, +oo[).
  + exact: interval_open.
  + by move=> ?; rewrite inE.
  + by rewrite inE.
- by move=> x y ax ay yx; rewrite ltrN2; exact: incrF.
have mGF : measurable_fun `]a, +oo[ (G \o F).
  apply: (@measurable_comp _ _ _ _ _ _ `]F a, +oo[%classic) => //.
  - move=> /= _ [x] /[!in_itv]/= /andP[ax xb] <-.
    by rewrite incrF ?incrF// in_itv/= ?lexx/= ?(ltW ab)//= ?(ltW ax) ?(ltW xb).
  - apply: open_continuous_measurable_fun; first exact: interval_open.
    by move=> x; rewrite inE/= => Fax; exact: cG.
  - apply: subspace_continuous_measurable_fun => //.
    by apply: derivable_within_continuous => x; exact: dF.
have mF' : measurable_fun `]a, +oo[ (- F)%R^`().
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= => ax.
  rewrite /continuous_at derive1E deriveN; last exact: dF.
  rewrite -derive1E.
  under eq_cvg do rewrite -(opprK ((- F)%R^`() _)); apply: cvgN.
  apply: cvg_trans (cF' x ax).
  apply: near_eq_cvg => /=; rewrite near_simpl; near=> z.
  rewrite !derive1E deriveN ?opprK//.
  apply: dF.
  near: z.
  rewrite near_nbhs.
  exact: near_in_itvoy.
rewrite -!integral_itv_obnd_cbnd; last 2 first.
  apply: measurable_funM => //.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  by move=> x; rewrite inE/=; exact: cF'.
  apply: measurable_funM; last exact: measurableT_comp.
  apply: (measurable_comp (measurable_itv `]-oo, (- F a)%R[)).
  - move=> _ /= [x + <-].
    rewrite !in_itv/= andbT=> ax.
    by rewrite ltrN2 incrF// ?in_itv/= ?andbT// ltW.
  - apply: open_continuous_measurable_fun; first exact: interval_open.
    by move=> x; rewrite inE/=; exact: cGN.
  - apply: measurableT_comp => //.
    apply: subspace_continuous_measurable_fun => //.
    exact: derivable_within_continuous.
apply: eq_integral => x/=; rewrite inE/= => ax.
congr EFin.
rewrite !fctE/= opprK; congr (_ * _)%R.
rewrite !derive1E deriveN ?opprK//.
exact: dF.
Unshelve. all: end_near. Qed.

Lemma increasing_ge0_integration_by_substitutionNy F G b :
  {in `]-oo, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]-oo, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> -oo%R]) ->
  F^`() x @[x --> b^'-] --> F^`() b (* TODO: try with cvg (F^`() x @[x --> b^'-]) *) ->
  derivable_Nyo_Lcontinuous F b -> F x @[x --> -oo%R] --> -oo%R->
  {within `]-oo, F b], continuous G} ->
  {in `]-oo, F b[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F b]) (G x)%:E =
  \int[mu]_(x in `]-oo, b]) (((G \o F) * F^`()) x)%:E.
Proof.
move=> ndF cdF cvgFNy cvgFb [dF Fb] FNyNy.
move=> /continuous_within_itvNycP[cG cGFb] G0.
rewrite -(@opprK _ (F b)).
rewrite (@ge0_integration_by_substitutionNy _ (- F b)%R); last 2 first.
- apply/continuous_within_itvNycP; split; last by rewrite opprK.
  by rewrite opprK => x xFb; exact: cG.
- by rewrite opprK.
rewrite -[in LHS](@opprK _ b).
have dFN z : (- z < b)%R -> derivable F (- z) 1.
  by move=> zb; apply: dF; rewrite in_itv.
have dFcompN z : (- z < b)%R -> derivable (F \o -%R) z 1.
  move=> zb; apply/diff_derivable/differentiable_comp => //.
  by apply/derivable1_diffP; exact: dFN.
rewrite (@increasing_ge0_integration_by_substitutiony (\- (F \o -%R))%R); last 8 first.
- move=> x y; rewrite !in_itv/= !andbT => xb yb.
  rewrite -ltrN2 => /ndF.
  by rewrite /= ltrN2; apply; rewrite !in_itv/= lerNl//.
- move=> x; rewrite in_itv/= andbT ltrNl => xb.
  have := cdF (- x)%R.
  rewrite in_itv/= => /(_ xb) NxF.
  rewrite /continuous_at in NxF *.
  rewrite derive1N/=; last exact: dFcompN.
  rewrite [X in _ --> X](_ : _ = F^`() (- x))%R; last first.
    rewrite derive1_comp; last 2 first.
      exact: derivable_opp.
      exact: dFN.
    rewrite [X in (_ * X)%R]derive1E.
    rewrite deriveN; last exact: derivable_id.
    by rewrite derive_id mulrN1 opprK.
  move/(@cvg_compNP _ _ (F^`()) x (F^`() (- x))) : NxF.
  apply: cvg_trans.
  apply: near_eq_cvg; rewrite near_simpl; near=> z.
  rewrite derive1N; last first.
    apply: dFcompN.
    by near: z; exact: Nlt_nbhsl.
  rewrite [in RHS]derive1_comp; last 2 first.
    exact: derivable_opp.
    apply: dFN.
    by near: z; exact: Nlt_nbhsl.
  rewrite derive1N; last exact: derivable_id.
  by rewrite derive1_id mulrN1 opprK.
- move: cvgFb => /cvg_at_leftNP cvgFbl.
  apply/cvg_ex; exists (F^`() b)%R.
  apply: cvg_trans cvgFbl.
  apply: near_eq_cvg; near=> z.
  rewrite [RHS]derive1N; last first.
    apply: dFcompN.
    rewrite ltrNl.
    by near: z; exact: nbhs_right_gt.
  rewrite fctE [LHS]derive1_comp; last 2 first.
    exact: derivable_id.
    apply: dFN; rewrite ltrNl.
    by near: z; exact: nbhs_right_gt.
  rewrite derive1_id mulr1 [in RHS]derive1_comp; last 2 first.
    exact: derivable_opp.
    apply: dFN; rewrite ltrNl.
    by near: z; exact: nbhs_right_gt.
  rewrite derive1N; last exact: derivable_id.
  by rewrite derive1_id mulrN1 opprK.
- move/cvg_ex : cvgFNy => [/= l cvgFNy].
  apply/cvg_ex; exists l.
  move/cvgNy_compNP : cvgFNy.
  apply: cvg_trans.
  apply: near_eq_cvg; near=> x.
  rewrite derive1N; last first.
    apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
      exact: derivable_opp.
    apply: dFN; rewrite ltrNl.
    by near: x; apply: nbhs_pinfty_gt; rewrite num_real.
  rewrite /= [in RHS]derive1_comp; last 2 first.
    exact: derivable_opp.
    apply: dFN; rewrite ltrNl.
    by near: x; apply: nbhs_pinfty_gt; rewrite num_real.
  rewrite derive1N; last exact: derivable_id.
  by rewrite derive1_id mulrN1 opprK.
- split => /=.
  + move=> z; rewrite in_itv/= andbT => bz.
    apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
      apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
        exact: derivable_opp.
      by apply: dFN; rewrite ltrNl.
    exact: derivable_opp.
  - rewrite opprK; apply/cvg_at_rightNP.
    rewrite opprK; apply: cvgN.
    apply: cvg_trans Fb.
    by apply: near_eq_cvg; near=> x; rewrite /= opprK.
- move/cvgNy_compNP in FNyNy.
  apply/cvgNrNy.
  rewrite [X in X @ _ --> _](_ : _ = F \o -%R)//.
  by apply: funext => r/=; rewrite fctE opprK.
- apply/continuous_within_itvcyP; split.
    move=> x; rewrite in_itv/= opprK andbT => Fbx.
    apply: continuous_comp; first exact: oppr_continuous.
    by apply: cG; rewrite in_itv/= ltrNl.
  by rewrite /= !opprK; exact/cvg_at_leftNP.
- move=> z; rewrite in_itv/= opprK andbT => Fbz.
  by apply: G0; rewrite in_itv/= ltrNl.
rewrite -[in RHS](opprK b) ge0_integration_by_substitutionNy; last 2 first.
  apply/continuous_within_itvNycP; split.
  - move=> z; rewrite in_itv/= opprK => zb.
    apply: continuousM; last by apply: cdF; rewrite in_itv.
    apply: continuous_comp.
      move/derivable_within_continuous: dF.
      rewrite continuous_open_subspace; last exact: interval_open.
      by apply; rewrite inE/= in_itv.
    by apply: cG; rewrite in_itv/= ndF ?in_itv//= ltW.
  - rewrite opprK; apply: cvgM => //.
    exact: (increasing_cvg_at_left_comp _ ndF).
  rewrite opprK => x.
  rewrite in_itv/= => xb.
  rewrite mulr_ge0//; first by apply: G0; rewrite in_itv/= ndF ?in_itv//= ltW.
  apply: (@incr_derive1_ge0_itvNy _ _ false b).
  - move=> z; rewrite inE/= in_itv/= => zb.
    by apply: dF; rewrite in_itv.
  - exact: ndF.
  - by rewrite in_itv.
have mG : measurable_fun `]-oo, (F b)[ G.
  by apply: open_continuous_measurable_fun => // x; rewrite inE => /cG.
have mF : measurable_fun `]-oo, b[ F.
  apply: open_continuous_measurable_fun => // x xNyb.
  move/derivable_within_continuous : dF.
  by rewrite continuous_open_subspace; [exact|exact: interval_open].
rewrite -[RHS]integral_itv_obnd_cbnd; last first.
  apply: (@measurable_comp _ _ _ _ _ _ `]-oo, b]) => //=.
    rewrite opp_itv_bndy opprK/=.
    by apply: subset_itvl; rewrite bnd_simp.
  apply/measurable_fun_itv_bndo_bndcP; apply: measurable_funM => //.
  - apply: (@measurable_comp _ _ _ _ _ _ `]-oo, F b[) => //=.
    move=> x/= [r]; rewrite in_itv/= => rb <-{x}.
    by rewrite in_itv/= ndF ?in_itv//= ltW.
  - apply: open_continuous_measurable_fun; first by [].
    by move=> x/=; rewrite inE => /cdF.
rewrite -[LHS]integral_itv_obnd_cbnd; last first.
  apply: measurable_funM.
    apply: (@measurable_comp _ _ _ _ _ _ `](- F b)%R, +oo[) => //=.
    - move=> x/= [r]; rewrite in_itv/= andbT => br <-{x}.
      by rewrite in_itv/= andbT ltrN2 ndF ?in_itv//= 1?ltrNl// lerNl ltW.
    - apply: (@measurable_comp _ _ _ _ _ _ `]-oo, F b[) => //=.
      by rewrite opp_itv_bndy//= opprK.
    - apply: measurableT_comp => //.
      apply: (@measurable_comp _ _ _ _ _ _ `]-oo, b[) => //=.
      by rewrite opp_itv_bndy opprK/=.
  have : {in `](- b)%R, +oo[%classic, F^`() \o -%R =1 (\- (F \o -%R))%R^`()}.
    move=> z; rewrite inE/= in_itv/= andbT => zb.
    rewrite derive1N; last first.
      apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
        exact: derivable_opp.
      by apply: dFN; rewrite ltrNl.
    rewrite [in RHS]derive1_comp; last 2 first.
      exact: derivable_opp.
      by apply: dFN; rewrite ltrNl.
    rewrite derive1N; last exact: derivable_id.
    by rewrite derive1_id mulrN1 opprK.
  move/eq_measurable_fun; apply.
  apply: (@measurable_comp _ _ _ _ _ _ `]-oo, b[) => //=.
    by rewrite opp_itv_bndy opprK.
  apply: open_continuous_measurable_fun; first by [].
  by move=> x; rewrite inE => /cdF.
apply: eq_integral => /= z; rewrite inE/= in_itv/= andbT => bz.
congr EFin.
rewrite !fctE/= opprK; congr *%R.
rewrite derive1N; last first.
  apply: diff_derivable; apply: differentiable_comp; apply/derivable1_diffP.
    exact: derivable_opp.
  by apply: dFN; rewrite ltrNl.
rewrite derive1_comp/=; last 2 first.
  exact: derivable_opp.
  by apply: dFN; rewrite ltrNl.
rewrite derive1N; last exact: derivable_id.
by rewrite derive1_id mulrN1 opprK.
Unshelve. all: end_near. Qed.

Lemma increasing_ge0_integration_by_substitutionT F G :
  {homo F : x y / (x < y)%R} ->
  continuous F^`() ->
  cvg (F^`() x @[x --> -oo%R]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  (forall x, derivable F x 1) ->
  F x @[x --> -oo%R] --> -oo%R ->
  F x @[x --> +oo%R] --> +oo%R ->
  continuous G ->
  (forall x, 0 <= G x)%R ->
  \int[mu]_x (G x)%:E =
  \int[mu]_x (((G \o F) * F^`()) x)%:E.
Proof.
move=> ndF cdF cvgFNy cvgFy dF FNyNy Fyy cG G0.
have mGFF' : measurable_fun setT ((G \o F) * F^`())%R.
  apply: measurable_funM.
    apply: measurableT_comp; first exact: continuous_measurable_fun.
    apply: continuous_measurable_fun => x.
    exact/differentiable_continuous/derivable1_diffP/dF.
  exact: continuous_measurable_fun cdF.
have cF : continuous F.
  by move=> x; exact/differentiable_continuous/derivable1_diffP/dF.
rewrite -{2}setC0 -(set_itvoc0 0%R) setCitv/= ge0_integral_setU//=; first last.
  rewrite disj_set2E; apply/eqP; rewrite -subset0 => x []/= /[!in_itv]/=.
  by rewrite leNgt andbT => /negP.
- move=> x _; apply: mulr_ge0; first exact: G0.
  apply: (@incr_derive1_ge0 _ _ setT).
  + by move=> ? _; exact: dF.
  + by move=> ? ? _ _; exact: ndF.
  + by rewrite interiorT.
- by apply/measurable_EFinP; rewrite -setCitvr setvU; exact: mGFF'.
rewrite integral_itv_obnd_cbnd; last by apply: measurable_funTS; apply: mGFF'.
rewrite -(increasing_ge0_integration_by_substitutiony _ _ _ cvgFy); first last.
- by move=> x; rewrite in_itv/= andbT => F0x; exact: G0.
- exact: continuous_subspaceT.
- exact: Fyy.
- split=> [x _|]; first exact: dF.
  by apply: cvg_at_right_filter; exact: cF.
- apply/cvg_ex; exists (F^`() 0).
  by apply: cvg_at_right_filter; exact: cdF.
- by move=> x _; exact: cdF.
- by move=> x y _ _; exact: ndF.
rewrite -(increasing_ge0_integration_by_substitutionNy _ _ cvgFNy); first last.
- by move=> x _; exact: G0.
- exact: continuous_subspaceT.
- exact: FNyNy.
- split=> [x _|]; first apply: dF.
- by apply: cvg_at_left_filter; exact: cF.
- by apply: cvg_at_left_filter; exact: cdF.
- by move=> x _; exact: cdF.
- by move=> x y _ _; exact: ndF.
rewrite -integral_itv_obnd_cbnd; last first.
  by apply: measurable_funTS; exact: continuous_measurable_fun.
rewrite -ge0_integral_setU//=; first last.
- rewrite disj_set2E; apply/eqP; rewrite -subset0 => x/=.
  by rewrite !in_itv/= andbT ltNge => -[? /negP].
- by move=> x _; rewrite lee_fin; exact: G0.
- apply/measurable_EFinP; apply: measurable_funTS.
  exact: continuous_measurable_fun.
by rewrite -setCitvr setvU.
Qed.

End integration_by_substitution.

Section integration_by_substitution_onem.
Context {R : realType}.
Let mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma integration_by_substitution_onem (G : R -> R) (r : R) :
  (0 <= r <= 1)%R ->
  {within `[0%R, r], continuous G} ->
  \int[mu]_(x in `[0%R, r]) (G x)%:E =
  \int[mu]_(x in `[`1-r, 1%R]) (G `1-x)%:E.
Proof.
move=> /andP[]; rewrite le_eqVlt => /predU1P[<- *|r0 r1 cG].
  by rewrite onem0 2!set_itv1 2!integral_set1.
have := @integration_by_substitution_decreasing R onem G `1-r 1.
rewrite onemK onem1 => -> //.
- by apply: eq_integral => x xr; rewrite !fctE derive1_onem opprK mulr1.
- by rewrite lerBlDl lerDr ltW.
- by move=> x y _ _ xy; rewrite ler_ltB.
- by rewrite derive1_onem; move=> ? ?; exact: cvg_cst.
- by rewrite derive1_onem; exact: is_cvg_cst.
- by rewrite derive1_onem; exact: is_cvg_cst.
- split => /=.
  + by move=> x xr1; exact: derivableB.
  + apply: cvg_at_right_filter; rewrite onemK.
    apply: (@continuous_comp_cvg _ _ _ _ onem)=> //=.
      by move=> x; apply: continuousB => //; exact: cvg_cst.
    by under eq_fun do rewrite -/(onem _) onemK; exact: cvg_id.
  + by apply: cvg_at_left_filter; apply: cvgB => //; exact: cvg_cst.
Qed.

Lemma Rintegration_by_substitution_onem (G : R -> R) (r : R) :
  (0 <= r <= 1)%R ->
  {within `[0%R, r], continuous G} ->
  (\int[mu]_(x in `[0, r]) (G x) =
  \int[mu]_(x in `[`1-r, 1]) (G `1-x))%R.
Proof.
by move=> r01 cG; rewrite [in LHS]/Rintegral integration_by_substitution_onem.
Qed.

End integration_by_substitution_onem.

Section ge0_integralT_even.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Local Open Scope ereal_scope.

Lemma ge0_symfun_integralT (f : R -> R) : (forall x, 0 <= f x)%R ->
  continuous f -> f =1 f \o -%R ->
  \int[mu]_x (f x)%:E = 2%:E * \int[mu]_(x in [set x | (0 <= x)%R]) (f x)%:E.
Proof.
move=> f0 cf evenf.
have mf : measurable_fun [set: R] f by exact: continuous_measurable_fun.
have mposnums : measurable [set x : R | 0 <= x]%R by rewrite -set_itvcy.
rewrite -(setUv [set x : R | 0 <= x]%R) ge0_integral_setU//= ; last 4 first.
  exact: measurableC.
  by apply/measurable_EFinP; rewrite setUv.
  by move=> x _; rewrite lee_fin.
  exact/disj_setPCl.
rewrite mule_natl mule2n; congr +%E.
rewrite -set_itvcy// setCitvr.
rewrite integral_itv_bndo_bndc; last exact: measurable_funTS.
rewrite -{1}oppr0 ge0_integration_by_substitutionNy//.
- apply: eq_integral => /= x; rewrite inE/= in_itv/= andbT => x0.
  by rewrite (evenf x).
- exact: continuous_subspaceT.
Qed.

End ge0_integralT_even.
