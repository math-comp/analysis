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
(* indefinite_integral mu a x f := \int[mu]_(t \in `[a, x] f t)               *)
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
  by apply: integrable_locally => //; exact: openT.
apply: cvg_at_right_left_dnbhs.
- apply/cvg_at_rightP => d [d_gt0 d0].
  pose E x n := `[x, x + d n[%classic%R.
  have muE y n : mu (E y n) = (d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin ltrDl d_gt0.
    by rewrite -EFinD addrAC subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, (fun n => PosNum (d_gt0 n))); split => //= [n z|n].
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
    rewrite /F/= /Rintegral -fineN -fineB; last 2 first.
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

(* NB: right-closed interval *)
Lemma FTC1_lebesgue_pt f a : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  forall x, a < BRight x -> lebesgue_pt f x ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> intf F x ax fx; split; last first.
  by apply/cvg_lim; [exact: Rhausdorff|exact: FTC0].
apply/cvg_ex; exists (f x).
have /= := FTC0 intf ax fx.
set g := (f in f n @[n --> _] --> _ -> _).
set h := (f in _ -> f n @[n --> _] --> _).
suff : g = h by move=> <-.
by apply/funext => y;rewrite /g /h /= [X in F (X + _)]mulr1.
Qed.

Corollary FTC1 f a : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  {ae mu, forall x, a < BRight x -> derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf F.
have /lebesgue_differentiation : locally_integrable setT f.
  by apply: integrable_locally => //; exact: openT.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> i fi ai; apply: FTC1_lebesgue_pt => //; rewrite ltNyr.
Qed.

Corollary FTC1Ny f : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` `]-oo, x]]) (f t))%R in
  {ae mu, forall x, derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf F; have := FTC1 -oo%O intf.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> r /=; apply; rewrite ltNyr.
Qed.

Corollary continuous_FTC1 f a : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  forall x, a < BRight x -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> fi F x ax fx; have lfx : lebesgue_pt f x.
  near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)).
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - by apply/measurable_funTS/EFin_measurable_fun; exact: measurable_int fi.
  - exact: fx.
have /= /(_ ax lfx)/= [dfx f'xE] := @FTC1_lebesgue_pt f a fi x.
by split; [exact: dfx|rewrite f'xE].
Unshelve. all: by end_near. Qed.

End FTC.

Definition indefinite_integral {R : realType}
    (mu : {measure set (g_sigma_algebraType (R.-ocitv.-measurable)) -> \bar R})
    a x (f : R -> R) : R :=
  (\int[mu]_(t in `[a, x]) f t)%R.

Section indefinite_integral_continuous.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).

Let int := (indefinite_integral mu).

Lemma indefinite_integral_near_left (a b : R) (e : R) (f : R -> R) :
  a < b -> 0 < e -> mu.-integrable `[a, b] (EFin \o f) ->
  \forall c \near a, `| int a c f | < e.
Proof.
move=> ab e0 intf.
have : mu.-integrable setT (EFin \o f \_`[a, b]).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
move=> /integral_normr_continuous /(_ _ e0)[d [d0 /=]] ifab.
near=> c.
have [ca|ca] := leP c a.
  rewrite /int /indefinite_integral/= /Rintegral.
  rewrite (integral_Sset1 a) ?fine0 ?normr0//.
  move: ca; rewrite le_eqVlt => /predU1P[->|ca]; first by rewrite interval_set1.
  by rewrite set_itv_ge//= bnd_simp -ltNge.
have /ifab : (mu `[a, c] < d%:E)%E.
  rewrite lebesgue_measure_itv/= lte_fin ca -EFinD lte_fin.
  by move: ca; near: c; exact: nbhs_right_ltDr.
move=> /(_ (measurable_itv _)) {ifab}.
apply: le_lt_trans.
have acbc : `[a, c] `<=` `[a, b].
  rewrite (@itv_bndbnd_setU _ _ (BLeft a) (BRight c) (BRight b))// bnd_simp.
    exact: ltW.
  by move: ca; near: c; exact: nbhs_right_le.
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
set rhs : \bar R := leRHS.
have [->|rhsoo] := eqVneq rhs +oo%E; first by rewrite leey.
rewrite /int /indefinite_integral /= /Rintegral.
set lhs := (\int[mu]_(_ in _) _)%E.
have [->|lhsNoo] := eqVneq lhs -oo%E; first by rewrite /= normr0 integral_ge0.
have lhsoo : lhs != +oo%E.
  apply: contra rhsoo => /eqP lhsoo.
  rewrite -leye_eq  -lhsoo; apply: le_integral => //=.
  - exact: integrableS intf.
  - rewrite [X in integrable _ _ X](_ : _ = abse \o EFin \o f)//.
    by apply: integrable_abse => /=; exact: integrableS intf.
  - by move=> x _; rewrite lee_fin ler_norm.
rewrite [leLHS](_ : _ = `| lhs |)%E//; last first.
  by move: lhsNoo lhsoo; rewrite /lhs /rhs; case: integral.
apply: (le_trans (le_abse_integral _ _ _)) => //=.
by apply: (measurable_funS _ acbc) => //; exact: measurable_int intf.
Unshelve. all: by end_near. Qed.

Lemma indefinite_integral_cvg_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> a] --> int a a f.
Proof.
move=> ab intf.
pose fab := f \_ `[a, b].
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
apply/cvgrPdist_le => /= e e0; rewrite near_simpl; near=> x.
rewrite {1}/int /indefinite_integral /Rintegral /=.
rewrite (integral_Sset1 a) ?interval_set1// fine0 sub0r normrN.
apply/ltW.
by near: x; exact: (@indefinite_integral_near_left _ b).
Unshelve. all: by end_near. Qed.

Lemma indefinite_integral_cvg_at_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> b^'-] --> int a b f.
Proof.
move=> ab intf.
pose fab := f \_ `[a, b].
have /= int_normr_cont : forall e : R, 0 < e ->
    exists d : R, 0 < d /\
    forall A, measurable A -> (mu A < d%:E)%E -> \int[mu]_(x in A) `|fab x| < e.
  rewrite /= => e e0; apply: integral_normr_continuous => //=.
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
rewrite /int /indefinite_integral; apply/cvgrPdist_le => /= e e0.
have [d [d0 /= {}int_normr_cont]] := int_normr_cont _ e0.
near=> x.
rewrite [in X in X - _](@itv_bndbnd_setU _ _ _ (BRight x))//;
  [|by rewrite bnd_simp ltW..].
rewrite {1}/Rintegral integral_setU_EFin//=; last 2 first.
  rewrite -itv_bndbnd_setU// ?bnd_simp; last 2 first.
    by near: x; exact: nbhs_left_ge.
    exact/ltW.
  by apply/EFin_measurable_fun; apply: measurable_int intf.
  apply/disj_set2P; rewrite -subset0 => z/=; rewrite !in_itv/= => -[/andP[_]].
  by rewrite leNgt => /negbTE ->.
have xbab : `]x, b] `<=` `[a, b].
  move=> z/=; rewrite !in_itv/= => /andP[xz ->/=].
  rewrite andbT (le_trans _ (ltW xz))//.
  by near: x; exact: nbhs_left_ge.
rewrite /Rintegral fineD; last 2 first.
  - rewrite fin_num_abs (le_lt_trans (le_abse_integral _ _ _)) //=.
    + case/integrableP : intf => + _.
      apply: measurable_funS => // z/=; rewrite !in_itv/= => /andP[->/=].
      by move=> /le_trans; apply.
    + apply: integral_fune_lt_pinfty => //=.
      rewrite [X in _.-integrable _ X](_ : _ = abse \o (EFin \o f))//.
      apply/integrable_abse/(integrableS _ _ _ intf) => //.
      move=> z/=; rewrite !in_itv/= => /andP[->/=].
      by move=> /le_trans; apply.
  - rewrite fin_num_abs (le_lt_trans (le_abse_integral _ _ _)) //=.
    + by case/integrableP : intf => + _; exact: measurable_funS.
    + apply: integral_fune_lt_pinfty => //=.
      rewrite [X in _.-integrable _ X](_ : _ = abse \o (EFin \o f))//.
      exact/integrable_abse/(integrableS _ _ _ intf).
rewrite -addrAC subrr add0r.
rewrite [X in fine X](_ : _ =
    (\int[mu]_(x0 in `]x, b]) (fab x0)%:E))%E//; last first.
  apply: eq_integral => //= z.
  rewrite inE/= in_itv/= => /andP[xz zb].
  rewrite /fab patchE ifT// inE/= in_itv/=.
  rewrite zb andbT (le_trans _ (ltW xz))//.
  by near: x; exact: nbhs_left_ge.
apply: ltW.
rewrite -lte_fin EFin_normr_Rintegral//=; last exact: integrableS intfab.
rewrite (le_lt_trans (le_abse_integral _ _ _))//=.
  case/integrableP : intf => /EFin_measurable_fun mf _.
  apply/measurableT_comp => //; apply/measurable_restrict => //=.
  by rewrite setIidl//; exact: measurable_funS mf.
rewrite -[ltLHS]fineK//.
- rewrite lte_fin int_normr_cont// lebesgue_measure_itv/= lte_fin.
  rewrite ifT// -EFinD lte_fin.
  near: x; exists d => // z; rewrite /ball_/= => + zb.
  by rewrite gtr0_norm// ?subr_gt0.
- rewrite ge0_fin_numE//; last exact: integral_ge0.
  apply: integral_fune_lt_pinfty => //=.
  rewrite [X in _.-integrable _ X](_ : _ = abse \o (EFin \o fab))//.
  by apply: integrable_abse; exact: integrableS intfab.
Unshelve. all: by end_near. Qed.

End indefinite_integral_continuous.

Section corollary_FTC1.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a b : R).

Corollary continuous_FTC2 f F a b : (a < b)%R -> {in `[a, b], continuous f} ->
  derivable_oo_continuous_bnd F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof.
move=> ab cf dF F'f.
pose fab := f \_ `[a, b].
pose G x : R := (\int[mu]_(t in `[a, x]) fab t)%R.
have iabf : mu.-integrable `[a, b] (EFin \o f).
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_in_subspaceT => x /[!inE] => /cf.
have ifab : mu.-integrable setT (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have G'f : {in `]a, b[, forall x, G^`() x = fab x /\ derivable G x 1}.
  move=> x /[!in_itv]/= /andP[ax xb].
  have := @continuous_FTC1 _ _ (BLeft a) ifab x.
  rewrite /= lte_fin => /(_ ax).
  have : {for x, continuous fab}.
    have /cf xf : x \in `[a, b] by rewrite in_itv/= (ltW ax) (ltW xb).
    rewrite /prop_for /continuous_at {2}/fab/= patchE.
    rewrite mem_set ?mulr1 /=; last by rewrite in_itv/= (ltW ax) (ltW xb).
    apply: cvg_trans xf; apply: near_eq_cvg; rewrite !near_simpl; near=> z.
    rewrite /fab/= patchE mem_set ?mulr1//=.
    near: z; have := @near_in_itv R a b x.
    rewrite in_itv/= ax xb => /(_ isT).
    by apply: filterS => z; exact: subset_itv_oo_cc.
  by move=> /[swap] /[apply] -[].
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
        rewrite !in_itv/=; move: zxy; rewrite in_itv/= => /andP[xz zy].
        rewrite (le_lt_trans _ xz)//= ?(lt_le_trans zy)//=.
        + by move: yab; rewrite in_itv/= => /andP[_ /ltW].
        + by move: xab; rewrite in_itv/= => /andP[/ltW].
      have Fz1 : derivable F z 1.
        by case: dF => /= + _ _; apply; rewrite inE in zab.
      have Gz1 : derivable G z 1 by have [|] := G'f z.
      apply: DeriveDef.
      + by apply: derivableB; [exact: Fz1|exact: Gz1].
      + by rewrite deriveB -?derive1E; [by []|exact: Fz1|exact: Gz1].
    - apply: derivable_within_continuous => z zxy.
      apply: derivableB.
      + case: dF => /= + _ _; apply.
        rewrite in_itv/=; move: zxy; rewrite in_itv/= => /andP[xz zy].
        rewrite (lt_le_trans _ xz)/= ?(le_lt_trans zy)//=.
        * by move: yab; rewrite in_itv/= => /andP[].
        * by move: xab; rewrite in_itv/= => /andP[].
      + apply: (G'f _ _).2; rewrite in_itv/=; apply/andP; split.
        * move: zxy; rewrite in_itv/= => /andP[+ _]; apply: lt_le_trans.
          by move: xab; rewrite in_itv/= => /andP[].
        * move: zxy; rewrite in_itv/= => /andP[_]; move=> /le_lt_trans; apply.
          by move: yab; rewrite in_itv/= => /andP[].
    - move=> z zxy; rewrite F'G'0.
        by rewrite /cst/= mul0r => /eqP; rewrite subr_eq0 => /eqP.
      rewrite !in_itv/=; move: zxy; rewrite in_itv/= => /andP[xz zy].
      rewrite (le_lt_trans _ xz)//= ?(lt_le_trans zy)//=.
      * by move: yab; rewrite in_itv/= => /andP[_ /ltW].
      * by move: xab; rewrite in_itv/= => /andP[/ltW].
  move=> H; pose c := (a + b) / 2.
  exists (F c - G c)%R => u /(H u c); apply.
  by rewrite in_itv/= midf_lt//= midf_lt.
have [c GFc] : exists c : R, forall x, x \in `]a, b[ -> (F x - G x)%R = c.
  by exists k => x xab; rewrite -[k]/(cst k x) -(FGk x xab).
have Ga0 : G a = 0%R by rewrite /G/= interval_set1// /Rintegral integral_set1.
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
  apply/continuous_within_itvP => //; split => // z zab.
  apply/differentiable_continuous/derivable1_diffP.
  by case: dF => /= + _ _; exact.
have iabfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //; rewrite setIidr.
have Ga : G x @[x --> a^'+] --> G a.
  by have /left_right_continuousP[] := indefinite_integral_cvg_left ab iabfab.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (indefinite_integral_cvg_at_left ab iabfab).
have cE : c = F a.
  apply/eqP;rewrite -(opprK c) eq_sym -addr_eq0 addrC.
  by have := cvg_unique _ GacFa Ga; rewrite Ga0 => ->.
have GbFbc : G b = (F b - c)%R.
  by have := cvg_unique _ GbcFb Gb; rewrite addrC => ->.
rewrite -EFinB -cE -GbFbc /G/= /Rintegral/= fineK//.
  rewrite integralEpatch//=.
  by under eq_integral do rewrite restrict_EFin.
exact: integral_fune_fin_num.
Unshelve. all: by end_near. Qed.

End corollary_FTC1.
