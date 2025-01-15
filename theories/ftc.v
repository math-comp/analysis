(* mathcomp analysis (c) 2023 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop signed reals ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure numfun realfun.
From mathcomp Require Import lebesgue_integral derive charge.

(**md**************************************************************************)
(* # Fundamental Theorem of Calculus for the Lebesgue Integral                *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file provides a proof of the first fundamental theorem of calculus    *)
(* for the Lebesgue integral. We derive from this theorem a corollary to      *)
(* compute the definite integral of continuous functions.                     *)
(*                                                                            *)
(* parameterized_integral mu a x f := \int[mu]_(t \in `[a, x] f t)            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section FTC.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a : itv_bound R).

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
    by rewrite -EFinD addrAC subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, fun n => PosNum (d_gt0 n)); split => //= [n z|n].
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
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
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
    by apply: integral_fune_fin_num => //; exact: integrableS intf.
    by apply: integral_fune_fin_num => //; exact: integrableS intf.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  rewrite [g in g n @[n --> _] --> _ -> _](_ : _ =
      fun n => (d n)^-1%:E * \int[mu]_(y in E x n) (f y)%:E); last first.
    by apply/funext => n; rewrite muE.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  set h := (f in f n @[n --> \oo] --> _).
  suff : g = h by move=> <-.
  apply/funext => n.
  rewrite /g /h /= fineM//.
  apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
  by apply: integrableS intf => //; exact: (nice_E _).1.
- apply/cvg_at_leftP => d [d_gt0 d0].
  have {}Nd_gt0 n : (0 < - d n)%R by rewrite ltrNr oppr0.
  pose E x n := `]x + d n, x]%classic%R.
  have muE y n : mu (E y n) = (- d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin -ltrBrDr.
    by rewrite ltrDl Nd_gt0 -EFinD opprD addrA subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, (fun n => PosNum (Nd_gt0 n))); split => //=.
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
      (fun n => - \int[mu]_(y in E x n) (f y)%:E)}.
    case: a ax {F}; last first.
      move=> [_|//].
      apply: nearW => n.
      rewrite -[in LHS]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite -/mu -[LHS]oppeK; congr oppe.
      rewrite oppeB; last first.
        rewrite fin_num_adde_defl// fin_numN//.
        by apply: integral_fune_fin_num => //; exact: integrableS intf.
      rewrite addeC.
      rewrite (_ : `]-oo, x] = `]-oo, (x + d n)%R] `|` E x n)%classic; last first.
        by rewrite -itv_bndbnd_setU//= bnd_simp ler_wnDr// ltW.
      rewrite integral_setU_EFin//=.
      - rewrite addeAC.
        rewrite -[X in X - _]integral_itv_bndo_bndc//; last first.
          by case: locf => + _ _; exact: measurable_funS.
        rewrite subee ?add0e//.
        by apply: integral_fune_fin_num => //; exact: integrableS intf.
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
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
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
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPLR => z/=.
      rewrite /E /= !in_itv/= => /andP[az zxdn].
      by apply/negP; rewrite negb_and -leNgt zxdn.
  suff: ((d n)^-1 * - fine (\int[mu]_(y in E x n) (f y)%:E))%R
          @[n --> \oo] --> f x.
    apply: cvg_trans; apply: near_eq_cvg; near=> n;  congr (_ *: _).
    rewrite /F -fineN -fineB; last 2 first.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
    by congr fine => /=; apply/esym; rewrite (addrC _ x); near: n.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  rewrite (@eq_cvg _ _ _ _ g)// => n.
  rewrite /g /= fineM//=; last first.
    apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
    by apply: integrableS intf => //; exact: (nice_E _).1.
  by rewrite muE/= invrN mulNr -mulrN.
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
    (mu : {measure set (g_sigma_algebraType (R.-ocitv.-measurable)) -> \bar R})
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
  by apply: subset_itvl; rewrite bnd_simp; move: ac; near: c; exact: nbhs_le.
rewrite -lee_fin fineK; last first.
  apply: integral_fune_fin_num => //=.
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
  by apply: le_normr_integral => //; exact: integrableS intf.
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
rewrite Rintegral_setU_EFin//=; last 2 first.
  rewrite -itv_bndbnd_setU// ?bnd_simp; last 2 first.
    by near: x; exact: nbhs_left_ge.
    exact/ltW.
  apply/disj_set2P; rewrite -subset0 => z/=; rewrite !in_itv/= => -[/andP[_]].
  by rewrite leNgt => /negbTE ->.
have xbab : `]x, b] `<=` `[a, b].
  by apply: subset_itvr; rewrite bnd_simp; near: x; exact: nbhs_left_ge.
rewrite -addrAC subrr add0r (le_trans (le_normr_integral _ _))//.
  exact: integrableS intf.
rewrite [leLHS](_ : _ = (\int[mu]_(t in `]x, b]) normr (fab t)))//; last first.
  apply: eq_Rintegral => //= z; rewrite inE/= in_itv/= => /andP[xz zb].
  rewrite /fab patchE ifT// inE/= in_itv/= zb andbT (le_trans _ (ltW xz))//.
  by near: x; exact: nbhs_left_ge.
apply/ltW/int_normr_cont => //.
rewrite lebesgue_measure_itv/= lte_fin.
rewrite ifT// -EFinD lte_fin.
near: x; exists d => // z; rewrite /ball_/= => + zb.
by rewrite gtr0_norm// ?subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_continuous a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  {within `[a, b], continuous (fun x => int a x f)}.
Proof.
move=> ab intf; apply/(continuous_within_itvP _ ab); split; first last.
  exact: parameterized_integral_cvg_at_left.
  apply/cvg_at_right_filter.
  rewrite {2}/int /parameterized_integral interval_set1 Rintegral_set1.
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
    rewrite ltrBlDr -ltrBlDl; apply: le_lt_trans.
    by rewrite opprB addrCA subrr addr0.
  rewrite Rintegral_itvB//; last 3 first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
    by rewrite bnd_simp ltW.
    exact: ltW.
  have xzab : `]x, z] `<=` `[a, b].
    by apply: subset_itvScc; rewrite bnd_simp; exact/ltW.
  apply: (le_trans (le_normr_integral _ _)) => //; first exact: integrableS intf.
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
  apply: (le_trans (le_normr_integral _ _)) => //.
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
  derivable_oo_continuous_bnd F a b ->
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
  move=> H; pose c := (a + b) / 2.
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
    by rewrite addrC subrr normr0 ltW.
  have := @cvgD _ _ _ _ Fap _ _ _ _ GFac Fa.
  rewrite (_ : (G \- F)%R + F = G)//.
  by apply/funext => x/=; rewrite subrK.
have GbcFb : G x @[x --> b^'-] --> (- c + F b)%R.
  have Fbn : Filter b^'- by exact: at_left_proper_filter.
  have GFbc : (G x - F x)%R @[x --> b^'-] --> (- c)%R.
    apply/cvgrPdist_le => /= e e0; near=> t.
    rewrite opprB GFc; last by rewrite in_itv/=; apply/andP.
    by rewrite addrC subrr normr0 ltW.
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
   by rewrite /G interval_set1 Rintegral_set1.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (parameterized_integral_cvg_at_left ab iabfab).
have Ga0 : G a = 0%R by rewrite /G interval_set1// Rintegral_set1.
have cE : c = F a.
  apply/eqP; rewrite -(opprK c) eq_sym -addr_eq0 addrC.
  by have := cvg_unique _ GacFa Ga; rewrite Ga0 => ->.
have GbFbc : G b = (F b - c)%R.
  by have := cvg_unique _ GbcFb Gb; rewrite addrC => ->.
rewrite -EFinB -cE -GbFbc /G /Rintegral/= fineK//.
  rewrite integralEpatch//=.
  by under eq_integral do rewrite restrict_EFin.
exact: integral_fune_fin_num.
Unshelve. all: by end_near. Qed.

End corollary_FTC1.

Section integration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma integration_by_parts F G f g a b : (a < b)%R ->
    {within `[a, b], continuous f} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x)%:E = (F b * G b - F a * G a)%:E -
  \int[mu]_(x in `[a, b]) (f x * G x)%:E.
Proof.
move=> ab cf Fab Ff cg Gab Gg.
have cfg : {within `[a, b], continuous (f * G + F * g)%R}.
  apply/subspace_continuousP => x abx; apply: cvgD.
  - apply: cvgM.
    + by move/subspace_continuousP : cf; exact.
    + have := derivable_oo_continuous_bnd_within Gab.
      by move/subspace_continuousP; exact.
  - apply: cvgM.
    + have := derivable_oo_continuous_bnd_within Fab.
      by move/subspace_continuousP; exact.
    + by move/subspace_continuousP : cg; exact.
have FGab : derivable_oo_continuous_bnd (F * G)%R a b.
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
  + have := derivable_oo_continuous_bnd_within Gab.
    by move/subspace_continuousP; exact.
rewrite /= integralD//=.
- by rewrite addeAC subee ?add0e// integral_fune_fin_num.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx;apply: cvgM.
  + have := derivable_oo_continuous_bnd_within Fab.
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
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_continuous_bnd G a b ->
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
exact: (derivable_oo_continuous_bnd_within Gab).
Qed.

End Rintegration_by_parts.

(* TODO: move to realfun.v? *)
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

Lemma increasing_cvg_at_right_comp F G a b (l : R) : (a < b)%R ->
  {in `[a, b[ &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'+] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab incrF cFa GFa.
apply/cvgrPdist_le => /= e e0.
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFa] := GFa.
have := cvg_at_right_within cFa.
move=> /cvgrPdist_lt/(_ _ d0)[d' /= d'0 {}cFa].
near=> t.
apply: GFa; last by apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFa => //=.
rewrite ltr0_norm// ?subr_lt0// opprB.
by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma increasing_cvg_at_left_comp F G a b (l : R) : (a < b)%R ->
  {in `]a, b] &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'-] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab incrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d /= d0 {}GFb] := GFb.
have := cvg_at_left_within cFb.
move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
near=> t.
apply: GFb; last by apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFb => //=.
rewrite gtr0_norm// ?subr_gt0//.
by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_right_comp F G a b (l : R) : (a < b)%R ->
  {in `[a, b[ &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'-] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab decrF cFa GFa.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFa] := GFa.
have := cvg_at_right_within cFa.
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFa].
near=> t.
apply: GFa; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFa => //=.
rewrite ltr0_norm// ?subr_lt0// opprB.
by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_left_comp F G a b (l : R) : (a < b)%R ->
  {in `]a, b] &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'+] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab decrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have /cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFb] := GFb.
have := cvg_at_left_within cFb. (* different point from gt0 version *)
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFb].
near=> t.
apply: GFb; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFb => //=.
rewrite gtr0_norm// ?subr_gt0//.
by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

End integration_by_substitution_preliminaries.

(* PR in progress *)
Section integral_setU_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_bigsetU_EFin (I : eqType) (F : I -> set T) (f : T -> R)
    (s : seq I) :
  (forall i, d.-measurable (F i)) ->
  uniq s -> trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D (EFin \o f) ->
  \int[mu]_(x in D) (f x)%:E = (\sum_(i <- s) (\int[mu]_(x in F i) (f x)%:E)).
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

Section PR_in_progress.
Local Open Scope ereal_scope.
Context {R : realType}.

Lemma decr_derive1_le0 (f : R -> R) (D : set R) (x : R) :
  {in (interior D) : set R, forall x : R, derivable f x 1%R} ->
  {in D &, {homo f : x y /~ (x < y)%R}} ->
  (interior D) x -> (f^`() x <= 0)%R.
Proof.
move=> df decrf Dx.
apply: limr_le.
  under eq_fun.
    move=> h.
    rewrite {2}(_:h = h%:A :> R^o); last first.
      by rewrite /GRing.scale/= mulr1.
    over.
    by apply: df; rewrite inE.
have := open_subball (@open_interior R^o D) Dx.
move=> [e /= e0 Hball].
have/normr_idP normr2E : (@GRing.zero R <= 2)%R by [].
near=> h.
have hneq0 : h != 0%R by near: h; exact: nbhs_dnbhs_neq.
have Dohx : (interior D) (h + x).
  move: (Hball (`|2 * h|%R)).
  apply => //.
      rewrite /= sub0r normrN !normrM !normr_id normr2E -ltr_pdivlMl//.
      near: h.
      apply: (@dnbhs0_lt _ R^o).
      exact: mulr_gt0.
    by rewrite normrM normr2E mulr_gt0// normr_gt0.
  apply: ball_sym; rewrite /ball/= addrK.
  rewrite normrM normr2E ltr_pMl ?normr_gt0//.
    by rewrite (_:1%R = 1%:R)// ltr_nat.
move: hneq0; rewrite neq_lt => /orP[h0|h0].
+ rewrite nmulr_rle0 ?invr_lt0// subr_ge0 ltW//.
  apply: decrf; rewrite ?in_itv/= ?andbT ?ltW ?gtrDr// inE; exact: interior_subset.
+ rewrite pmulr_rle0 ?invr_gt0// subr_le0 ltW//.
  apply: decrf; rewrite ?in_itv/= ?andbT ?ltW ?ltrDr// inE; exact: interior_subset.
Unshelve. end_near. Qed.

Section itv_interior.

Lemma itv_interior_bounded (x y : R) (a b : bool) :
  (x < y)%R ->
  [set` (Interval (BSide a x) (BSide b y))]^° = `]x, y[%classic.
Proof.
move=> xy.
rewrite interval_bounded_interior//; last exact: interval_is_interval.
rewrite inf_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
rewrite sup_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
exact: set_itvoo.
Qed.

Lemma itv_interior_pinfty (x : R) (a : bool) :
  [set` (Interval (BSide a x) (BInfty _ false))]^° = `]x, +oo[%classic.
Proof.
rewrite interval_right_unbounded_interior//; first last.
    by apply: hasNubound_itv; rewrite lt_eqF.
  exact: interval_is_interval.
rewrite inf_itv; last by case: a; rewrite bnd_simp ?ltW.
by rewrite set_itv_o_infty.
Qed.

Lemma itv_interior_ninfty (y : R) (b : bool) :
  [set` (Interval (BInfty _ true) (BSide b y))]^° = `]-oo, y[%classic.
Proof.
rewrite interval_left_unbounded_interior//; first last.
    by apply: hasNlbound_itv; rewrite gt_eqF.
  exact: interval_is_interval.
rewrite sup_itv; last by case b; rewrite bnd_simp ?ltW.
by apply: set_itv_infty_o.
Qed.

Definition itv_interior :=
  (itv_interior_bounded, itv_interior_pinfty, itv_interior_ninfty).

End itv_interior.

Lemma decr_derive1_le0_itv (f : R^o -> R^o) (z : R) (x0 x1 : R) (b0 b1 : bool) :
  {in `]x0, x1[, forall x : R, derivable f x 1%R} ->
  {in (Interval (BSide b0 x0) (BSide b1 x1)) &, {homo f : x y /~ (x < y)%R}} ->
  z \in `]x0, x1[ -> (f^`() z <= 0)%R.
Proof.
have [x10|x01] := leP x1 x0.
  move=> _ _.
  by move/lt_in_itv; rewrite bnd_simp le_gtF.
set itv := Interval (BSide b0 x0) (BSide b1 x1).
move=> df decrf xx0x1.
apply: (@decr_derive1_le0 _ [set` itv]).
    rewrite itv_interior//.
    by move=> ?; rewrite inE/=; apply: df.
  move=> ? ?; rewrite !inE/=; apply: decrf.
by rewrite itv_interior/=.
Qed.

End PR_in_progress.

Section integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma integration_by_substitution_decreasing F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> b^'-]) ->
  derivable_oo_continuous_bnd F a b ->
  {within `[F b, F a], continuous G} ->
  \int[mu]_(x in `[F b, F a]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> ab decrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] Fab cG.
have cF := derivable_oo_continuous_bnd_within Fab.
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
have PGFbFa : derivable_oo_continuous_bnd PG (F b) (F a).
  have [/= dF rF lF] := Fab; split => /=.
  - move=> x xFbFa /=.
    have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFa intG _ _).1 => /=.
      by move: xFbFa; rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFbFa).
  - have := parameterized_integral_continuous FbFa intG.
    by move=> /(continuous_within_itvP _ FbFa)[].
  - exact: parameterized_integral_cvg_at_left.
rewrite (@continuous_FTC2 _ _ PG _ _ FbFa cG); last 2 first.
- split.
  + move=> x /[dup]xFbFa; rewrite in_itv/= => /andP[Fbx xFa].
    apply: (continuous_FTC1 xFa intG Fbx _).1.
    by move: cG => /(continuous_within_itvP _ FbFa)[+ _ _]; exact.
  + have := parameterized_integral_continuous FbFa intG.
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
      apply: (decreasing_cvg_at_right_comp ab) => //.
      * by move=> x y xab yab; apply: decrF; exact: subset_itv_co_cc.
      * by move/continuous_within_itvP : cF => /(_ ab)[].
      * by move/continuous_within_itvP : cG => /(_ FbFa)[].
    rewrite fctE {2}/f eqxx; apply: cvgN.
    apply: cvg_trans F'ar; apply: near_eq_cvg.
    by near=> z; rewrite fE// in_itv/=; apply/andP; split.
  + apply: cvgM.
      apply: (decreasing_cvg_at_left_comp ab).
      * by move=> //x y xab yab; apply: decrF; apply: subset_itv_oc_cc.
      * by move/continuous_within_itvP : cF => /(_ ab)[].
      * by move/continuous_within_itvP : cG => /(_ FbFa)[].
    rewrite fctE {2}/f gt_eqF// eqxx.
    apply: cvgN; apply: cvg_trans F'bl; apply: near_eq_cvg.
    by near=> z; rewrite fE// in_itv/=; apply/andP; split.
- have [/= dF rF lF] := Fab.
  have := derivable_oo_continuous_bnd_within PGFbFa.
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

Lemma integration_by_substitution_oppr G a b : (a < b)%R ->
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

Lemma integration_by_substitution_increasing F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> b^'-]) ->
  derivable_oo_continuous_bnd F a b ->
  {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
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
rewrite -integration_by_substitution_oppr//.
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
- by [].
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

Lemma decreasing_bigcup_itvS_Ny F (x : R) :
  {in `[x, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> +oo%R] --> -oo%R ->
  \bigcup_i `](F (x + i.+1%:R)%R), F x]%classic = `]-oo, F x]%classic.
Proof.
move=> dF nyF.
(* TODO: itv_infty_bnd_bigcup -> esym *)
rewrite itv_infty_bnd_bigcup eqEsubset; split.
- move=> z/= [n _ /=]; rewrite in_itv/= => /andP[Fxnz zFx].
  exists `| ceil (F (x + n.+1%:R) - F x)%R |%N.+1 => //=.
  rewrite in_itv/= zFx andbT lerBlDr -lerBlDl (le_trans _ (abs_ceil_ge _))//.
  by rewrite ler_normr orbC opprB lerB// ltW.
- move=> y/= [n _]/=; rewrite in_itv/= => /andP[Fxny yFx].
  have [i iFxn] : exists i, (F (x + i.+1%:R) < F x - n%:R)%R.
    move/cvgrNy_lt : nyF.
    move/(_ (F x - n%:R)%R) => [z [zreal zFxn]].
    exists `| ceil (z - x) |%N.
    apply: zFxn.
    rewrite -ltrBlDl (le_lt_trans (le_ceil _))// (le_lt_trans (ler_norm _))//.
    by rewrite -natr1 -intr_norm ltrDl.
  exists i => //=.
  rewrite in_itv/=; apply/andP; split => //.
  exact: lt_le_trans Fxny.
Qed.

Lemma decreasing_bigcup_itvS_bnd F a n :
  {in `[a, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  \bigcup_(i < n) `](F (a + i.+1%:R)), (F a)]%classic =
  `](F (a + n%:R)), (F a)]%classic.
Proof.
move=> decrF.
rewrite eqEsubset; split.
  apply: bigcup_sub => k/= kn.
  apply: subset_itvr; rewrite bnd_simp.
  move: kn; rewrite leq_eqVlt => /predU1P[<-//|kn].
  by rewrite ltW// decrF ?in_itv/= ?andbT ?lerDl//= ltrD2l ltr_nat.
move: n => [|n]; first by rewrite addr0 set_interval.set_itvoc0.
by apply: (@bigcup_sup _ _ n) => /=.
Qed.

Lemma itv_bndy_bigcup_shiftn (b : bool) (x : R) (n : nat):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + (i + n.+1)%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists (`|Num.ceil (y - x)|)%N => //=.
rewrite in_itv/= xy/= natrD natr_absz intr_norm addrA.
apply: ltr_pwDr; first by rewrite (_ : 0%R = 0%:R)// ltr_nat.
rewrite -lterBDl.
apply: (le_trans (le_ceil _)) => //=.
rewrite le_eqVlt; apply/predU1P; left.
apply/esym/normr_idP.
rewrite ler0z -ceil_ge0 (lt_le_trans (@ltrN10 R))// subr_ge0.
by case: b xy => //= /ltW.
Qed.

Lemma itv_bndy_bigcup_shiftS (b : bool) (x : R):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + i.+1%:R))].
Proof.
under eq_bigcupr do rewrite -addn1.
exact: itv_bndy_bigcup_shiftn.
Qed.

Definition derivable_oy_continuous_bnd {R' : numFieldType}
    (f : R' -> R') (x : R') :=
  {in `]x, +oo[, forall x, derivable f x 1} /\ f @ x^'+ --> f x.

Lemma decreasing_ge0_integration_by_substitutiony F G a :
  {in `[a, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  derivable_oy_continuous_bnd F a -> F x @[x --> +oo%R] --> -oo%R ->
  {within `]-oo, F a], continuous G} ->
  {in `]-oo, F a], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F a]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> decrF cdF /cvg_ex[/= dFa cdFa] /cvg_ex[/= dFoo cdFoo].
move=> [dF cFa] Fny /continuous_within_itvNycP[cG cGFa] G0.
have mG n : measurable_fun `](F (a + n.+1%:R)), (F a)] G.
  apply: (@measurable_fun_itv_oc _ _ _ false true).
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[_ xFa].
  by apply: cG; rewrite in_itv.
have mGFNF' i : measurable_fun `[a, (a + i.+1%:R)[ ((G \o F) * - F^`())%R.
  apply: (@measurable_fun_itv_co _ _ _ false true).
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
transitivity (limn (fun n => \int[mu]_(x in `[F (a + n%:R)%R, F a]) (G x)%:E)).
  rewrite -(decreasing_bigcup_itvS_Ny decrF Fny).
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; first last.
  - exact: trivIset_seqDU.
  - rewrite -seqDU_bigcup_eq => x Fax; rewrite lee_fin G0//; move: x Fax.
    by apply: bigcup_sub => i _; exact: subset_itvr.
  - rewrite -seqDU_bigcup_eq.
    exact/measurable_EFinP/measurable_fun_bigcup.
  - by move=> n; apply: measurableD => //;exact: bigsetU_measurable.
  apply: congr_lim; apply/funext => n.
  rewrite -ge0_integral_bigsetU//=; last 5 first.
    by move=> m; apply: measurableD => //; exact: bigsetU_measurable.
    exact: iota_uniq.
    exact: (@sub_trivIset _ _ _ [set: nat]).
    apply/measurable_EFinP.
    rewrite big_mkord -bigsetU_seqDU.
    apply: (measurable_funS _
        (@bigsetU_bigcup _ (fun k =>`]F (a + k.+1%:R)%R, _]%classic) _)).
      exact: bigcup_measurable.
    exact/measurable_fun_bigcup.
  - move=> x xFaSkFa.
    apply: G0.
    move: xFaSkFa.
    rewrite big_mkord.
    rewrite -bigsetU_seqDU.
    rewrite -(bigcup_mkord _ (fun k => `](F (a + k.+1%:R)), (F a)]%classic)).
    move: x.
    by apply: bigcup_sub => k/= nk; exact: subset_itvr.
  rewrite -integral_itv_obnd_cbnd; last first.
    case: n => //.
    by rewrite addr0 set_interval.set_itvoc0; exact: measurable_fun_set0.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord _ (fun k => `](F (a + k.+1%:R)), (F a)]%classic)).
  exact: decreasing_bigcup_itvS_bnd.
transitivity (limn (fun n =>
    \int[mu]_(x in `]a, (a + n%:R)%R[) (((G \o F) * - F^`()) x)%:E)); last first.
  rewrite -integral_itv_obnd_cbnd; last first.
    rewrite itv_bndy_bigcup_shiftS.
    apply/measurable_fun_bigcup => // n.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  rewrite itv_bndy_bigcup_shiftS.
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; last 4 first.
  - by move=> n; apply: measurableD => //; exact: bigsetU_measurable.
  - rewrite -seqDU_bigcup_eq.
    apply/measurable_fun_bigcup => // n.
    apply/measurable_EFinP.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  - move=> x ax.
    have {}ax : (a < x)%R.
      move: ax.
      rewrite -seqDU_bigcup_eq => -[? _]/=.
      by rewrite in_itv/= => /andP[].
    rewrite fctE lee_fin mulr_ge0//.
    + apply: G0.
      by rewrite in_itv/= ltW// decrF ?in_itv ?andbT ?lexx//= ltW.
    + rewrite oppr_ge0.
      apply: (@decr_derive1_le0 _ _ `[a, +oo[).
      * rewrite itv_interior.
        by move=> ?; rewrite inE/=; apply: dF.
      * by move=> ? ?; rewrite !inE/=; apply: decrF.
      * by rewrite itv_interior/= in_itv/= andbT.
  - exact: trivIset_seqDU.
  apply: congr_lim; apply/funext => n.
  rewrite -integral_bigsetU_EFin/=; last 4 first.
  - by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
  - exact: iota_uniq.
  - exact: (@sub_trivIset _ _ _ [set: nat]).
  - apply/measurable_EFinP.
    apply: (measurable_funS (measurable_itv `]a, (a + n.+1%:R)[)).
      rewrite big_mkord.
      rewrite -bigsetU_seqDU.
      rewrite -(bigcup_mkord _ (fun k => `]a, (a + k.+1%:R)[%classic)).
      apply: bigcup_sub => k/= kn.
      by apply: subset_itvl; rewrite bnd_simp/= lerD2l ler_nat ltnS ltnW.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `]a, (a + k.+1%:R)[%classic)).
  rewrite eqEsubset; split.
    move: n => [|n]; first by rewrite addr0 set_itvoo0.
    by apply: (@bigcup_sup _ _ n) => /=.
  apply: bigcup_sub => k/= kn; apply: subset_itvl.
  by rewrite bnd_simp/= lerD2l ler_nat.
apply: congr_lim; apply/funext => -[|n].
  by rewrite addr0 set_itv1 integral_set1 set_itv_ge -?leNgt ?bnd_simp// integral_set0.
rewrite integration_by_substitution_decreasing.
- rewrite integral_itv_bndo_bndc// ?integral_itv_obnd_cbnd//.
  + rewrite -setUitv1; last by rewrite bnd_simp ltrDl.
    rewrite measurable_funU//; split; last exact: measurable_fun_set1.
    by apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
  + by apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
- by rewrite ltrDl.
- move=> x y /=; rewrite !in_itv/= => /andP[ax _] /andP[ay _] yx.
  by apply: decrF; rewrite //in_itv/= ?ax ?ay.
- move=> x; rewrite in_itv/= => /andP[ax _].
  by apply: cdF; rewrite in_itv/= ax.
- exact: (cvgP dFa).
- apply: (cvgP (F^`() (a + n.+1%:R))).
  apply: cvg_at_left_filter.
  apply: cdF.
  by rewrite in_itv/= andbT ltr_pwDr.
- split.
  + move=> x; rewrite in_itv/= => /andP[ax _].
    by apply: dF; rewrite in_itv/= ax.
  + exact: cFa.
  + apply/cvg_at_left_filter/differentiable_continuous.
    apply/derivable1_diffP/dF.
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
  {in `]-oo, (- a)%R], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) ((G \o -%R) x)%:E.
Proof.
move=> /continuous_within_itvNycP[cG GNa] G0.
have Dopp : (@GRing.opp R)^`() = cst (-1).
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
  derivable_oy_continuous_bnd F a -> F x @[x --> +oo%R] --> +oo%R->
  {within `[F a, +oo[, continuous G} ->
  {in `[F a, +oo[, forall x, (0 <= G x)%R} ->
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
  by move=> x; rewrite in_itv/= lerNr => FaNx; apply: G0; rewrite in_itv/= FaNx.
rewrite (@decreasing_ge0_integration_by_substitutiony (- F)%R); first last.
- move=> y.
  rewrite in_itv/= lerNr => FaNy.
  by apply: G0; rewrite in_itv/= FaNy.
- apply/continuous_within_itvNycP; split => //.
  rewrite fctE opprK.
  exact/cvg_at_rightNP.
- exact/cvgNrNy.
- split.
  + move=> x ax; apply: derivableN.
    exact: dF.
  + exact: cvgN.
- apply/cvg_ex; exists (- l)%R.
  have /(_ (@filter_filter R _ proper_pinfty_nbhs)) := cvgN F'ool.
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF; rewrite in_itv/= andbT.
  by near: z; apply: nbhs_pinfty_gt; exact: num_real.
- apply/cvg_ex; exists (- r)%R.
  have /(_ (@filter_filter R _ (at_right_proper_filter a))) := cvgN F'ar.
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  by apply: dF; rewrite in_itv/= andbT.
- move=> x ax.
  rewrite /continuous_at.
  rewrite derive1E deriveN -?derive1E; last exact: dF.
  have /(_ (nbhs_filter x)) := cvgN (cF' x ax).
  apply: cvg_trans.
  apply: near_eq_cvg.
  rewrite near_simpl/=.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF.
  near: z.
  rewrite near_nbhs.
  apply: (@open_in_nearW _ _ `]a, +oo[).
  + exact: interval_open.
  + by move=> ?; rewrite inE/=.
  + by rewrite inE.
- by move=> x y ax ay yx; rewrite ltrN2; exact: incrF.
have mGF : measurable_fun `]a, +oo[ (G \o F).
  apply: (@measurable_comp _ _ _ _ _ _ `]F a, +oo[%classic) => //.
  - move=> /= _ [x] /[!in_itv]/= /andP[ax xb] <-.
    by rewrite incrF ?incrF// in_itv/= ?lexx/= ?(ltW ab)//= ?(ltW ax) ?(ltW xb).
  - apply: open_continuous_measurable_fun; first exact: interval_open.
    by move=> x; rewrite inE/= => Fax; exact: cG.
  - apply: subspace_continuous_measurable_fun => //.
    apply: derivable_within_continuous => x.
    exact: dF.
have mF' : measurable_fun `]a, +oo[ (- F)%R^`().
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= => ax.
  rewrite /continuous_at.
  rewrite derive1E deriveN; last exact: dF.
  rewrite -derive1E.
  under eq_cvg do rewrite -(opprK ((- F)%R^`() _)); apply: cvgN.
  apply: cvg_trans (cF' x ax).
  apply: near_eq_cvg => /=.
  rewrite near_simpl.
  near=> z.
  rewrite !derive1E deriveN ?opprK//.
  apply: dF.
  near: z.
  rewrite near_nbhs.
  exact: near_in_itvoy.
rewrite -!integral_itv_obnd_cbnd; last 2 first.
  apply: measurable_funM => //.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  by move=> x; rewrite inE/=; exact: cF'.
  apply: measurable_funM.
    apply: (measurable_comp (measurable_itv `]-oo, (- F a)%R[)).
        move=> _/=[x + <-].
        rewrite !in_itv/= andbT=> ax.
        by rewrite ltrN2 incrF// ?in_itv/= ?andbT// ltW.
      apply: open_continuous_measurable_fun; first exact: interval_open.
      by move=> x; rewrite inE/=; exact: cGN.
    apply: measurableT_comp => //.
    apply: subspace_continuous_measurable_fun => //.
    exact: derivable_within_continuous.
  exact: measurableT_comp.
apply: eq_integral => x/=; rewrite inE/= => ax.
congr EFin.
rewrite !fctE/= opprK; congr (_ * _)%R.
rewrite !derive1E deriveN ?opprK//.
exact: dF.
Unshelve. all: end_near. Qed.

(* move to PR *)
Lemma incr_derive1_ge0 (f : R -> R) (D : set R) (x : R):
  {in (interior D) : set R, forall x : R, derivable f x 1%R} ->
  {in D &, {homo f : x y / (x < y)%R}} ->
  (interior D) x -> (0 <= f^`() x)%R.
Proof.
move=> df incrf Dx.
rewrite -[leRHS]opprK oppr_ge0.
have dfx : derivable f x 1 by apply: df; rewrite inE.
rewrite derive1E -deriveN// -derive1E.
apply: (@decr_derive1_le0 _ _ D).
- move=> y Dy.
  apply: derivableN.
  exact: df.
- move=> y z Dy Dz yz.
  rewrite ltrN2.
  exact: incrf.
- exact: Dx.
Qed.

Lemma incr_derive1_ge0_itv (f : R^o -> R^o) (z : R) (x0 x1 : R) (b0 b1 : bool) :
  {in `]x0, x1[, forall x : R, derivable f x 1%R} ->
  {in (Interval (BSide b0 x0) (BSide b1 x1)) &, {homo f : x y / (x < y)%R}} ->
  z \in `]x0, x1[ -> (0 <= f^`() z)%R.
Proof.
have [x10|x01] := leP x1 x0.
  move=> _ _.
  by move/lt_in_itv; rewrite bnd_simp le_gtF.
set itv := Interval (BSide b0 x0) (BSide b1 x1).
move=> df incrf xx0x1.
apply: (@incr_derive1_ge0 _ [set` itv]).
    rewrite itv_interior//.
    by move=> ?; rewrite inE/=; apply: df.
  move=> ? ?; rewrite !inE/=; apply: incrf.
by rewrite itv_interior/=.
Qed.

(* PR? *)
Lemma interiorT {T : topologicalType} : interior (@setT T) = setT.
Proof.
rewrite eqEsubset; split; first exact: interior_subset.
rewrite -open_subsetE//.
exact: openT.
Qed.

Lemma derivable_within_continuousT (f : R -> R) :
  (forall x, derivable f x 1) -> continuous f.
Proof.
move=> df.
apply/continuous_subspace_setT.
rewrite -(@RhullK _ setT); last by rewrite inE.
apply: derivable_within_continuous.
move=> x _.
exact: df.
Qed.

Definition derivable_yo_continuous_bnd {R' : numFieldType}
    (f : R' -> R') (x : R') :=
  {in `]-oo, x[, forall x, derivable f x 1} /\ f @ x^'- --> f x.

Lemma increasing_ge0_integration_by_substitutionNy F G b :
  {in `]-oo, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]-oo, b[, continuous F^`()} ->
  cvg (F^`() x @[x --> -oo%R]) ->
  cvg (F^`() x @[x --> b^'-]) ->
  derivable_yo_continuous_bnd F b -> F x @[x --> -oo%R] --> -oo%R->
  {within `]-oo, F b], continuous G} ->
  {in `]-oo, F b], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F b]) (G x)%:E =
  \int[mu]_(x in `]-oo, b]) (((G \o F) * F^`()) x)%:E.
Proof.
move=> ndF cdF cvgFNy cvgFb [dF Fb] FNyNy cG G0.
Admitted.

Lemma increasing_ge0_integration_by_substitution F G a :
  {homo F : x y / (x < y)%R} ->
  continuous F^`() ->
  cvg (F^`() x @[x --> -oo%R]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  (forall x, derivable F x 1) ->
  F x @[x --> -oo%R] --> -oo%R ->
  F x @[x --> +oo%R] --> +oo%R ->
  continuous G ->
  (forall x, (0 <= G x)%R) ->
  \int[mu]_x (G x)%:E =
  \int[mu]_x (((G \o F) * F^`()) x)%:E.
Proof.
move=> ndF cdF cvgFNy cvgFy dF FNyNy Fyy cG G0.
have mGFF' : measurable_fun setT ((G \o F) * F^`())%R.
  apply: measurable_funM.
    apply: measurableT_comp.
      exact: continuous_measurable_fun.
    apply: continuous_measurable_fun.
    exact: derivable_within_continuousT.
  exact: continuous_measurable_fun cdF.
rewrite -{2}setC0 -(set_itvoc0 0%R) setCitv/=.
rewrite ge0_integral_setU//=; first last.
- rewrite -(@RhullK _ `]-oo, 0%R]%classic); last first.
    by rewrite inE/=; apply: interval_is_interval.
  rewrite -(@RhullK _ `]0%R, +oo[%classic)//; last first.
    by rewrite inE/=; apply: interval_is_interval.
  apply: disj_itv_Rhull; first last.
    1, 2: apply: interval_is_interval.
  rewrite eqEsubset; split => x//= []; rewrite !in_itv/= andbT => x0.
  move/(le_lt_trans x0).
  by rewrite ltxx.
- move=> x _.
  apply: mulr_ge0; last first.
  apply: (@incr_derive1_ge0 _ setT).
  - by move=> ? _; apply: dF.
  - by move=> ? ? _ _; apply: ndF.
  - by rewrite interiorT.
- exact: G0.
- apply/measurable_EFinP.
  rewrite -setCitvr setvU.
  exact: mGFF'.
rewrite integral_itv_obnd_cbnd; last by apply: measurable_funTS; apply: mGFF'.
rewrite -(increasing_ge0_integration_by_substitutiony _ _ _ cvgFy); first last.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
rewrite -(increasing_ge0_integration_by_substitutionNy _ _ cvgFNy); first last.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
rewrite -integral_itv_obnd_cbnd; last first.
  admit.
rewrite -ge0_integral_setU//=; first last.
- admit.
- admit.
- admit.
by rewrite -setCitvr setvU.
Abort.

End integration_by_substitution.

Section ge0_integralT_even.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Local Open Scope ereal_scope.

Lemma ge0_integralT_even (f : R -> R) : (forall x, 0 <= f x)%R ->
  continuous f ->
  f =1 f \o -%R ->
  \int[mu]_x (f x)%:E = 2%:E * \int[mu]_(x in [set x | (0 <= x)%R]) (f x)%:E.
Proof.
move=> f0 cf evenf.
have mf : measurable_fun [set: R] f by exact: continuous_measurable_fun.
have mposnums : measurable [set x : R | 0 <= x]%R.
  by rewrite -set_itv_c_infty.
rewrite -(setUv [set x : R | 0 <= x]%R) ge0_integral_setU//= ; last 4 first.
  exact: measurableC.
  by apply/measurable_EFinP; rewrite setUv.
  by move=> x _; rewrite lee_fin.
  exact/disj_setPCl.
rewrite mule_natl mule2n; congr +%E.
rewrite -set_itv_c_infty// setCitvr.
rewrite integral_itv_bndo_bndc; last exact: measurable_funTS.
rewrite -{1}oppr0 ge0_integration_by_substitutionNy//.
- apply: eq_integral => /= x.
  rewrite inE/= in_itv/= andbT => x0.
  by rewrite (evenf x).
- exact: continuous_subspaceT.
Qed.

End ge0_integralT_even.
