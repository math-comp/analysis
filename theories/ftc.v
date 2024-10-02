(* mathcomp analysis (c) 2023 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun realfun lebesgue_integral.
Require Import derive charge.

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
Import numFieldTopology.Exports.

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
by move/integrableP : fi => -[/EFin_measurable_fun].
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
apply/cvgrPdist_le => /= e e0; rewrite near_simpl; near=> x.
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
rewrite near_simpl.
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
pose G x : R := (\int[mu]_(t in `[a, x]) fab t)%R.
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
(* take arbitrary e > 0, find d s.t. `| G (F (a + d))) - G (F a)| < e *)
apply/cvgrPdist_le => /= e e0.
(* for this e,
   there exists d s.t. `| G (F a + d) - G (F a)| < e by continuity of G *)
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFa] := GFa.
(* for this d,
   there exists d' s.t. forall r, `| r - a | < d' implies F (a + d') - F a < d
   by continuity of F at a *)
(* apply a lemma for take r := (a + d') from `[a, b] *)
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
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFb] := GFb.
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
have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFa] := GFa.
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
have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFb] := GFb.
have := cvg_at_left_within cFb. (* different point from gt0 version *)
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFb].
near=> t.
apply: GFb; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFb => //=.
rewrite gtr0_norm// ?subr_gt0//.
by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

End integration_by_substitution_preliminaries.

Lemma integral_itv_oo (R : realType) (f : R -> R) (b0 b1 : bool) (x y : R) :
  measurable_fun `]x, y[ f ->
  (\int[lebesgue_measure]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
 \int[lebesgue_measure]_(z in `]x, y[) (f z)%:E)%E.
Proof.
have [xy|yx _|-> _] := ltgtP x y; last 2 first.
    rewrite !set_itv_ge ?integral_set0//=.
      by rewrite bnd_simp le_gtF// ltW.
    by case b0; case: b1; rewrite bnd_simp ?lt_geF// le_gtF// ltW.
  by case: b0; case: b1; rewrite !set_itvE ?integral_set0 ?integral_set1.
move=> mf.
transitivity (\int[lebesgue_measure]_(z in [set` Interval (BSide b0 x) (BLeft y)]) (f z)%:E)%E.
  case: b1 => //.
  rewrite -integral_itv_bndo_bndc//.
  case: b0 => //.
  rewrite -setU1itv ?bnd_simp// measurable_funU//; split => //.
  exact: measurable_fun_set1.
by case: b0 => //; rewrite -integral_itv_obnd_cbnd.
Qed.

Lemma eq_integral_itvoo (R : realType) (g f : R -> R) (b0 b1 : bool) (x y : R) :
  measurable_fun `]x, y[ f ->
  measurable_fun `]x, y[ g ->
  {in `]x, y[, f =1 g} ->
  (\int[lebesgue_measure]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
     \int[lebesgue_measure]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (g z)%:E)%E.
Proof.
move=> mf mg fg.
rewrite integral_itv_oo// (@integral_itv_oo _ g)//.
by apply: eq_integral => z; rewrite inE/= => zxy; congr EFin; exact: fg.
Qed.

Section integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma increasing_change F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg ((F^`() : R -> R) x @[x --> a^'+]) ->
  cvg ((F^`() : R -> R) x @[x --> b^'-]) ->
  derivable_oo_continuous_bnd F a b ->
 {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
move=> ab incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] dcbF cG.
have cF := (derivable_oo_continuous_bnd_within dcbF).
have FaFb : (F a < F b)%R by apply: incrF; rewrite //= in_itv/= (ltW ab) lexx.
have mGFF' : measurable_fun `]a, b[ ((G \o F) * F^`())%R.
  apply: measurable_funM.
  - apply: (measurable_comp (measurable_itv `]F a, F b[)).
      exact: increasing_image_oo.
    apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    move/(continuous_within_itvP _ FaFb) : cG => [+ _ _]; exact.
  - apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    move/(continuous_within_itvP _ ab) : cF => [+ _ _]; exact.
  - apply: subspace_continuous_measurable_fun; first by [].
    apply: continuous_in_subspaceT => x.
    rewrite inE/=.
    exact: cF'.
have intGFb : mu.-integrable `[(F a), (F b)] (EFin \o G).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
pose PG x := parameterized_integral mu (F a) x G.
have dcbPG : derivable_oo_continuous_bnd PG (F a) (F b).
  have [/= dF rF lF] := dcbF.
  split => /=.
  - move=> x xFaFb /=.
    have xFb : (x < F b)%R by move: xFaFb; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFb intGFb _ _).1 => /=.
      by move: (xFaFb); rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFaFb).
  - have := parameterized_integral_continuous FaFb intGFb.
    by move=> /(continuous_within_itvP _ FaFb)[].
  - exact: parameterized_integral_cvg_at_left.
rewrite (@continuous_FTC2 _ _ PG _ _ FaFb cG); last 2 first.
- split.
  + move=> x /[dup]xFaFb; rewrite in_itv/= => /andP[Fax xFb].
    apply: (continuous_FTC1 xFb intGFb Fax _).1.
    have/(continuous_within_itvP _ FaFb)[+ _ _] := cG; exact.
  + have := parameterized_integral_continuous FaFb intGFb.
    by move=> /(continuous_within_itvP _ FaFb)[].
  + exact: parameterized_integral_cvg_at_left.
- move=> x xFaFb.
  have xFb : (x < F b)%R by move: xFaFb; rewrite in_itv/= => /andP[].
  apply: (continuous_FTC1 xFb _ _ _).2 => //=.
    by move: (xFaFb); rewrite lte_fin in_itv/= => /andP[].
  exact: (within_continuous_continuous _ _ xFaFb).
set f  := fun x => if x == a then r else if x == b then l else F^`() x.
have fE : {in `]a, b[, F^`() =1 f}.
  move=> x; rewrite in_itv/= => /andP[ax xb].
  rewrite /f ifF; last by rewrite gt_eqF.
  by rewrite ifF// lt_eqF.
rewrite -(@continuous_FTC2 _ ((G \o F) * f)%R (PG \o F) _ _ ab); last 3 first.
- apply/(continuous_within_itvP _ ab); split.
  + move=> x xab.
    apply: continuousM; first apply: continuous_comp.
    * by move/(continuous_within_itvP _ ab) : cF => [+ _ _]; exact.
    * move/(continuous_within_itvP _ FaFb) : cG => [+ _ _]; apply.
      exact: increasing_image_oo.
    * have : F^`() @ x --> f x by rewrite -fE//; exact: cF'.
      apply: cvg_trans; apply: near_eq_cvg; rewrite near_simpl.
      apply: (@open_in_nearW _ _ `]a, b[); last by rewrite inE.
        exact: interval_open.
      move=> z; rewrite inE/=; exact: fE.
  + apply: cvgM.
      apply: (increasing_cvg_at_right_comp ab) => //.
          move=> x y xab yab.
          by apply: incrF; apply: subset_itv_co_cc.
        by move/continuous_within_itvP : cF => /(_ ab)[].
      by move/continuous_within_itvP : cG => /(_ FaFb)[].
    rewrite {2}/f eq_refl.
    move: F'ar.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    by rewrite fE// in_itv/=; apply/andP; split.
  + apply: cvgM.
      apply: (increasing_cvg_at_left_comp ab).
          move=> //x y xab yab.
          by apply: incrF; apply: subset_itv_oc_cc.
        by move/continuous_within_itvP : cF => /(_ ab) [].
      by move/continuous_within_itvP : cG => /(_ FaFb) [].
    rewrite {2}/f ifF; last by rewrite gt_eqF.
    rewrite eq_refl.
    move: F'bl.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    by rewrite fE// in_itv/=; apply/andP; split.
- have := derivable_oo_continuous_bnd_within dcbPG.
  have [/= dF rF lF] := dcbF.
  move=> /(continuous_within_itvP _ FaFb)[_ PGFa PGFb].
  split => /=.
  - move=> x xab.
    apply/derivable1_diffP.
    apply: differentiable_comp; apply/derivable1_diffP.
      by have [+ _ _] := dcbF; apply.
    have [+ _ _] := dcbPG.
    by apply; exact: increasing_image_oo.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFa] := PGFa.
    have := cvg_at_right_within rF.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFa].
    near=> t.
    apply: PGFa; last by apply: incrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFa => //=.
    rewrite ltr0_norm// ?subr_lt0// opprB.
    by near: t; exact: nbhs_right_ltDr.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFb] := PGFb.
    have := cvg_at_left_within lF.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
    near=> t.
    apply: (PGFb); last by apply: incrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFb => //=.
    rewrite gtr0_norm// ?subr_gt0//.
    by near: t; exact: nbhs_left_ltBl.
-  move=> x /[dup]xab /andP[ax xb]; rewrite derive1_comp.
  + congr (_ * _)%R.
    * have /[dup]FxFaFb : F x \in `]F a, F b[ by exact: increasing_image_oo.
      rewrite in_itv/= => /andP[FaFx FxFb].
      apply: (continuous_FTC1 FxFb intGFb FaFx _).2 => //=.
      exact: (within_continuous_continuous _ _ FxFaFb).
    * by rewrite fE.
  + by have [+ _ _] := dcbF; apply.
  + by have [+ _ _] := dcbPG; apply; exact: increasing_image_oo.
have mGFf : measurable_fun `]a, b[ ((G \o F) * f)%R.
  apply: (eq_measurable_fun ((G \o F) * F^`())%R) => //.
  move=> x; rewrite inE/= => xab; congr (_ * _)%R.
  by rewrite fE.
apply: eq_integral_itvoo => //x; rewrite inE/= => xab.
congr (_ * _)%R.
by rewrite fE.
Unshelve. all: end_near. Qed.

Lemma decreasing_change F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg ((F^`() : R -> R) x @[x --> a^'+]) ->
  cvg ((F^`() : R -> R) x @[x --> b^'-]) ->
  derivable_oo_continuous_bnd F a b ->
 {within `[F b, F a], continuous G} ->
  \int[mu]_(x in `[F b, F a]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * (- F^`())) x)%:E.
Proof.
move=> ab decrF cf /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] dcbF cG.
set f : R -> R := fun x => if x == a then r else
                            if x == b then l else F^`() x.
have FbFa : (F b < F a)%R by apply: decrF; rewrite //= in_itv/= (ltW ab) lexx.
pose PG x := parameterized_integral mu (F b) x G.
have intGFa : mu.-integrable `[(F b), (F a)] (EFin \o G).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
set H := PG \o F.
set h : R -> R := ((G \o F) * (- f))%R.
have dcbPG : derivable_oo_continuous_bnd PG (F b) (F a).
  have [/= dF rF lF] := dcbF.
  split => /=.
  - move=> x xFbFa /=.
    have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFa intGFa _ _).1 => /=.
      by move: (xFbFa); rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFbFa).
  - have := parameterized_integral_continuous FbFa intGFa.
    by move=> /(continuous_within_itvP _ FbFa)[].
  - exact: parameterized_integral_cvg_at_left.
have dPGE : {in `](F b), (F a)[, PG^`() =1 G}.
  move=> x xFbFa.
  have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
  apply: (continuous_FTC1 xFa intGFa _ _).2 => //=.
    by move: (xFbFa); rewrite lte_fin in_itv/= => /andP[].
  exact: (within_continuous_continuous _ _ xFbFa).
move/continuous_within_itvP : (cG) => /(_ FbFa)[incG GFb GFa].
have cF : {within `[a, b], continuous F} :=
  derivable_oo_continuous_bnd_within dcbF.
move/continuous_within_itvP : (cF) => /(_ ab)[incF cFa cFb].
have cNh : {within `[a, b], continuous (- h)%R}.
  move=> x; apply: continuousN; move: x.
  apply/(continuous_within_itvP _ ab); split.
  - move=> /= x xab.
    apply: continuousM; last first.
      have : (- F^`())%R y @[y --> x] --> (- f)%R x.
        apply: cvgN => //.
        rewrite /f.
        rewrite ifF; last first.
          apply: gt_eqF.
          by move: xab; rewrite in_itv/= => /andP[].
        rewrite ifF; last first.
          apply: lt_eqF.
          by move: xab; rewrite in_itv/= => /andP[].
        exact: cf.
      apply: cvg_trans.
      apply: near_eq_cvg.
      rewrite near_simpl.
      apply: (@open_in_nearW _ _ `]a, b[%classic).
      - exact: interval_open.
      - move=> z; rewrite inE/= in_itv/= => /andP[az zb].
        rewrite !fctE; congr (- _)%R.
        rewrite /f ifF; last by rewrite gt_eqF.
        by rewrite ifF// lt_eqF.
      by rewrite inE.
    apply: continuous_comp; first exact: incF.
    by apply: incG; exact: decreasing_image_oo.
  - apply: cvgM.
      apply: (decreasing_cvg_at_right_comp ab) => //x y xab yab.
      by apply: decrF; apply: subset_itv_co_cc.
    apply: cvgN.
    rewrite {2}/f eq_refl.
    move: F'ar.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    rewrite /f ifF; last by rewrite gt_eqF.
    by rewrite ifF// lt_eqF.
  - apply: cvgM.
      apply: (decreasing_cvg_at_left_comp ab) => //x y xab yab.
      by apply: decrF; apply: subset_itv_oc_cc.
    apply: cvgN.
    rewrite {2}/f ifF; last by rewrite gt_eqF.
    rewrite eq_refl.
    move: F'bl.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    rewrite /f ifF; last by rewrite gt_eqF.
    by rewrite ifF// lt_eqF.
have dcbH : derivable_oo_continuous_bnd H a b.
  have := derivable_oo_continuous_bnd_within dcbPG.
  move=> /(continuous_within_itvP _ FbFa)[_ PGFb PGFa].
  split => /=.
  - move=> x xab.
    apply/derivable1_diffP.
    apply: differentiable_comp; apply/derivable1_diffP.
      by have [+ _ _] := dcbF; apply.
    have [+ _ _] := dcbPG.
    by apply; exact: decreasing_image_oo.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFa] := PGFa.
    have := cvg_at_right_within cFa.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFa].
    near=> t.
    apply: PGFa; last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFa => //=.
    rewrite ltr0_norm// ?subr_lt0// opprB.
    by near: t; exact: nbhs_right_ltDr.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFb] := PGFb.
    have := cvg_at_left_within cFb.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
    near=> t.
    apply: (PGFb); last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFb => //=.
    rewrite gtr0_norm// ?subr_gt0//.
    by near: t; exact: nbhs_left_ltBl.
have dHE : {in `]a, b[, H^`() =1 (- h)%R}.
  move=> x xab; rewrite derive1_comp.
  - rewrite dPGE//; last exact: decreasing_image_oo.
    rewrite /h/f.
    move: xab.
    rewrite in_itv/= => /andP[ax xb].
    rewrite mulrN opprK.
    rewrite mulrfctE ifF; last by rewrite gt_eqF.
    by rewrite ifF// lt_eqF.
  - by have [+ _ _] := dcbF; apply.
  - by have [+ _ _] := dcbPG; apply; exact: decreasing_image_oo.
rewrite (continuous_FTC2 FbFa cG dcbPG dPGE).
apply: oppe_inj.
rewrite oppeB// addeC.
rewrite -(continuous_FTC2 ab cNh dcbH dHE).
have mGFF' : measurable_fun `]a, b[ ((G \o F) * F^`())%R.
  apply: measurable_funM.
  - apply: (measurable_comp (measurable_itv `]F b, F a[)).
      exact: decreasing_image_oo.
    apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    exact: incG.
  - apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    exact: incF.
  - apply: subspace_continuous_measurable_fun; first by [].
    apply: continuous_in_subspaceT => x.
    rewrite inE/=.
    exact: cf.
rewrite -!integral_itv_bndo_bndc; last 2 first.
- rewrite -setU1itv ?bnd_simp//.
  rewrite mulrN; apply: measurableT_comp => //.
  by rewrite measurable_funU//; split => //; apply: measurable_fun_set1.
- apply: subspace_continuous_measurable_fun => //.
  move: cNh; apply: continuous_subspaceW.
  exact: subset_itv_co_cc.
rewrite -!integral_itv_obnd_cbnd; last 2 first.
- rewrite mulrN.
  exact: measurableT_comp => //.
- apply: subspace_continuous_measurable_fun => //.
  move: cNh; apply: continuous_subspaceW.
  exact: subset_itv_oo_cc.
rewrite -[LHS]oppeK -integralN//=; last first.
  apply: integrable_add_def => //=.
  apply: (@integrableS _ _ _ mu `[a, b]) => //.
    exact: subset_itv_oo_cc.
  apply: continuous_compact_integrable => //.
  exact: segment_compact.
congr (- _).
apply: eq_integral => //.
move=> x xab.
rewrite mulrN; congr (- _)%:E.
rewrite /h/f.
rewrite mulrN opprK.
rewrite mulrfctE ifF; last first.
  apply: gt_eqF.
  by move: xab; rewrite inE/= in_itv/= => /andP[].
rewrite ifF//.
apply: lt_eqF.
by move: xab; rewrite inE/= in_itv/= => /andP[].
Unshelve. all: end_near. Qed.

Lemma oppr_change G a b : (a < b)%R ->
 {within `[(- b)%R, (- a)%R], continuous G} ->
  \int[mu]_(x in `[(- b)%R, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, b]) ((G \o -%R) x)%:E.
Proof.
move=> ab cG.
have Dopp: (@GRing.opp R)^`() = cst (-1)%R :> (R -> R).
  apply/funext => z.
  rewrite derive1E.
  exact: derive_val.
rewrite (@decreasing_change -%R)//.
- apply: eq_integral => //= x; rewrite inE/= => xab.
  congr (EFin _).
  rewrite !fctE -[RHS]mulr1; congr (_ * _)%R.
  rewrite derive1E.
  rewrite deriveN//.
  rewrite opprK.
  exact: derive_val.
- by move=> ? ? _ _; rewrite ltrN2.
- rewrite Dopp.
  move=> ? _; exact: cvg_cst.
- rewrite Dopp.
  apply: is_cvgN.
  exact: is_cvg_cst.
- rewrite Dopp.
  apply: is_cvgN.
  exact: is_cvg_cst.
- split.
  + by move=> x _.
  + rewrite -at_leftN.
    exact: cvg_at_left_filter.
  + rewrite -at_rightN.
    exact: cvg_at_right_filter.
Qed.

Lemma increasing_change2 F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {in `]a, b[, continuous F^`()} ->
  cvg ((F^`() : R -> R) x @[x --> a^'+]) ->
  cvg ((F^`() : R -> R) x @[x --> b^'-]) ->
  derivable_oo_continuous_bnd F a b ->
 {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
move=> ab incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'bl] dcbF cG.
have cF := (derivable_oo_continuous_bnd_within dcbF).
have FaFb : (F a < F b)%R by apply: incrF; rewrite //= in_itv/= (ltW ab) lexx.
set f  := fun x => if x == a then r else if x == b then l else F^`() x.
have fE : {in `]a, b[, F^`() =1 f}.
  move=> x; rewrite in_itv/= => /andP[ax xb].
  rewrite /f ifF; last by rewrite gt_eqF.
  by rewrite ifF// lt_eqF.
have mGFF' : measurable_fun `]a, b[ ((G \o F) * F^`())%R.
  apply: measurable_funM.
  - apply: (measurable_comp (measurable_itv `]F a, F b[)).
      exact: increasing_image_oo.
    apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    move/(continuous_within_itvP _ FaFb) : cG => [+ _ _]; exact.
  - apply: subspace_continuous_measurable_fun => //.
    apply: continuous_in_subspaceT => x; rewrite inE/=.
    move/(continuous_within_itvP _ ab) : cF => [+ _ _]; exact.
  - apply: subspace_continuous_measurable_fun; first by [].
    apply: continuous_in_subspaceT => x.
    rewrite inE/=.
    exact: cF'.
have intE : \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E = (\int[mu]_(x in `[a, b]) (((G \o F) * f) x)%:E).
  apply: eq_integral_itvoo => //.
    apply: eq_measurable_fun mGFF'.
    by move=> x; rewrite inE/= => xab; congr (_ * _)%R; rewrite fE.
  by move=> x xab; congr (_ * _)%R; rewrite fE.
rewrite intE.
have F'N : {in `](- b)%R, (- a)%R[, forall x, (- F^`() (- x) @[x --> x] --> (F \o -%R)^`() x)%R}.
  move=> x xNbNa.
  rewrite derive1_comp//; last first.
    by have [+ _ _] := dcbF; apply; rewrite oppr_itvoo.
  have := (@is_deriveNid _ _ x 1%R).
  move/(@derive_val _ _ _ _ _ -%R).
  rewrite -derive1E => ->.
  rewrite mulrN1.
  have cNF' : {in `]-%R b, -%R a[, continuous (F^`() \o -%R)}.
    move=> z; rewrite -oppr_itvoo => Nzab.
    apply: continuous_comp.
      exact: opp_continuous.
    exact: cF'.
  apply: cvgN.
  suff : F^`() (- x0) @[x0 --> x] --> F^`() (- x) by [].
  rewrite -/(F^`() \o -%R) -/((F^`() \o -%R) x).
  exact: cNF'.
rewrite -(opprK a) -(opprK b).
rewrite oppr_change; last 2 first.
- by rewrite ltrN2.
- rewrite !opprK; apply/(continuous_within_itvP _ ab); split.
  + move=> x /[dup]xab; rewrite in_itv/= => /andP[ax xb].
    apply: continuousM.
      apply: continuous_comp.
        by move/(continuous_within_itvP _ ab) : cF => [+ _ _]; exact.
      move/(continuous_within_itvP _ FaFb) : cG => [+ _ _]; apply.
      exact: increasing_image_oo.
    have : F^`() @ x --> f x by rewrite -fE//; exact: cF'.
    apply: cvg_trans; apply: near_eq_cvg; rewrite near_simpl.
    apply: (@open_in_nearW _ _ `]a, b[); last by rewrite inE.
      exact: interval_open.
    move=> z; rewrite inE/=; exact: fE.
  + apply: cvgM.
      apply: (increasing_cvg_at_right_comp ab) => //.
          move=> x y xab yab.
          by apply: incrF; apply: subset_itv_co_cc.
        by move/continuous_within_itvP : cF => /(_ ab)[].
      by move/continuous_within_itvP : cG => /(_ FaFb)[].
    rewrite {2}/f eq_refl.
    move: F'ar.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    by rewrite fE// in_itv/=; apply/andP; split.
  + apply: cvgM.
      apply: (increasing_cvg_at_left_comp ab).
          move=> //x y xab yab.
          by apply: incrF; apply: subset_itv_oc_cc.
        by move/continuous_within_itvP : cF => /(_ ab) [].
      by move/continuous_within_itvP : cG => /(_ FaFb) [].
    rewrite {2}/f ifF; last by rewrite gt_eqF.
    rewrite eq_refl.
    move: F'bl.
    apply: cvg_trans.
    apply: near_eq_cvg.
    near=> z.
    by rewrite fE// in_itv/=; apply/andP; split.
rewrite (@decreasing_change (F \o -%R) G (- b)%R (- a)%R); last 7 first.
- by rewrite ltrN2.
  move=> x y; rewrite -!oppr_itvcc => Nxab Nyab; rewrite -ltrN2 => NxNy.
  exact: incrF.
- move=> x xNbNa.
  move: (F'N x xNbNa).
  apply: cvg_trans; apply: near_eq_cvg; rewrite near_simpl.
  apply: (@open_in_nearW _ _ `]-%R b, -%R a[); last by rewrite inE.
    exact: interval_open.
  move=> z; rewrite inE/= -oppr_itvoo => Nzab.
  rewrite [RHS]derive1_comp//; last first.
    have [+ _ _] := dcbF; exact.
  have := (@is_deriveNid _ _ z 1%R).
  move/(@derive_val _ _ _ _ _ -%R).
  rewrite -derive1E => ->.
  by rewrite mulrN1.
- apply/(cvgP (- l)%R).
  have : -%R (F^`() \o -%R) x @[x --> (-b)^'+] --> (- l)%R.
    apply: cvgN.
    exact/cvg_at_leftNP.
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1_comp//; last first.
    have [+ _ _] := dcbF; apply; rewrite in_itv/=; apply/andP; split.
      rewrite ltrNr//.
      near: z.
      apply: nbhs_right_lt.
      by rewrite ltrN2.
    by rewrite ltrNl.
  have := (@is_deriveNid _ _ z 1%R).
  move/(@derive_val _ _ _ _ _ -%R).
  rewrite -derive1E => ->.
  by rewrite mulrN1.
- apply/(cvgP (- r)%R).
  have : -%R (F^`() \o -%R) x @[x --> (-a)^'-] --> (- r)%R.
    apply: cvgN.
    exact/cvg_at_rightNP.
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1_comp//; last first.
    have [+ _ _] := dcbF; apply; rewrite in_itv/=; apply/andP; split.
      by rewrite ltrNr.
    rewrite ltrNl//.
    near: z.
    apply: nbhs_left_gt.
    by rewrite ltrN2.
  have := (@is_deriveNid _ _ z 1%R).
  move/(@derive_val _ _ _ _ _ -%R).
  rewrite -derive1E => ->.
  by rewrite mulrN1.
- split.
  + move=> x xNbNa.
    apply: diff_derivable.
    apply: differentiable_comp => //.
    apply/derivable1_diffP.
    have [+ _ _] := dcbF; apply.
    by rewrite oppr_itvoo.
  + apply/cvg_at_leftNP; rewrite fctE opprK.
    by have [] := dcbF.
  + apply/cvg_at_rightNP; rewrite fctE opprK.
    by have [] := dcbF.
- by rewrite fctE !opprK.
have mGFNDFN : measurable_fun `](- b)%R, (- a)%R[ ((G \o (F \o -%R)) * - (F \o -%R)^`())%R.
  apply: measurable_funM.
  - rewrite compA.
    apply: (measurable_comp (measurable_itv `]a, b[)) => //.
      by move=> _/=[x + <-]; rewrite oppr_itvoo.
    apply: (measurable_comp (measurable_itv `]F a, F b[)).
        exact: increasing_image_oo.
      apply: subspace_continuous_measurable_fun => //.
      move: cG.
      apply: continuous_subspaceW.
      exact: subset_itv_oo_cc.
    apply: subspace_continuous_measurable_fun => //.
    move: cF.
    apply: continuous_subspaceW.
    exact: subset_itv_oo_cc.
  - apply: measurableT_comp => //.
    apply: (eq_measurable_fun (- (F^`() \o -%R))%R).
      move=> x.
      rewrite inE/= -oppr_itvoo => Nxab.
      rewrite derive1_comp//; last by have [+ _ _] := dcbF; apply.
      have := (@is_deriveNid _ _ x 1%R).
      move/(@derive_val _ _ _ _ _ -%R).
      rewrite -derive1E => ->.
      by rewrite mulrN1.
    apply: measurableT_comp => //.
    apply: (measurable_comp (measurable_itv `]a, b[)) => //.
      by move=> _ [x /= + <-]; rewrite -oppr_itvoo.
    apply: open_continuous_measurable_fun.
      exact: interval_open.
    move=> x; rewrite inE/= => xab.
    exact: cF'.
apply: (eq_integral_itvoo _ _ mGFNDFN).
  apply: (measurable_comp (measurable_itv `]a, b[)) => //.
    by move=> _ [x /= + <-]; rewrite oppr_itvoo.
  apply: (eq_measurable_fun ((G \o F) * F^`())%R) => //.
  move=> x; rewrite inE/= => xab; congr (_ * _)%R.
  by rewrite fE.
move=> x; rewrite -oppr_itvoo => Nxab.
rewrite fctE; congr (_ * _)%R.
rewrite -fE// -[RHS]opprK; congr -%R.
rewrite derive1_comp//; last first.
  by have [+ _ _] := dcbF; apply.
have := (@is_deriveNid _ _ x 1%R).
move/(@derive_val _ _ _ _ _ -%R).
rewrite -derive1E => ->.
by rewrite mulrN1.
Unshelve. all: end_near. Qed.

End integration_by_substitution.

Module old_integration_by_substitution.
Section old_integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma increasing_change_old F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {within `[a, b], continuous F^`()} ->
  derivable_oo_continuous_bnd F a b ->
 {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
move=> ab incrF.
move/(continuous_within_itvP _ ab) => [+ /cvgP + /cvgP].
exact: (increasing_change2 ab incrF).
Qed.

Lemma decreasing_change_old F G a b :
    (a < b)%R ->
    {in `[a, b]&, {homo F : x y /~ (x < y)%R}} ->
    {within `[a, b], continuous F^`()} ->
    derivable_oo_continuous_bnd F a b ->
    {within `[F b, F a], continuous G} ->
  \int[mu]_(x in `[F b, F a]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * - (F^`() : R -> R)) x)%:E.
Proof.
move=> ab decrF.
move/(continuous_within_itvP _ ab) => [+ /cvgP + /cvgP].
exact: decreasing_change.
Qed.

End old_integration_by_substitution.
End old_integration_by_substitution.
