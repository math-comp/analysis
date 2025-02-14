(* mathcomp analysis (c) 2023 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals itv ereal.
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
(*                   partial1of2 f == first partial derivative of f           *)
(*                                    f has type R -> T -> R for R : realType *)
(* parameterized_integral mu a x f := \int[mu]_(t \in `[a, x] f t)            *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'d1 f" (at level 10, f at next level, format "''d1'  f").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section differentiation_under_integral.

Definition partial1of2 {R : realType} {T : Type} (f : R -> T -> R) y : R -> R :=
  (f ^~ y)^`().

Local Notation "'d1 f" := (partial1of2 f).

Lemma partial1of2E {R : realType} {T : Type} (f : R -> T -> R) y x :
  ('d1 f) y x = 'D_1 (f^~ y) x.
Proof. by rewrite /partial1of2 derive1E. Qed.

Local Open Scope ring_scope.
Context {R : realType} d {Y : measurableType d}
  {mu : {measure set Y -> \bar R}}.
Variable f : R -> Y -> R.
Variable B : set Y.
Hypothesis mB : measurable B.
Variable a u v : R.
Let I : set R := `]u, v[.
Hypothesis Ia : I a.

Hypothesis intf : forall x, I x -> mu.-integrable B (EFin \o f x).

Hypothesis derf1 : forall x y, I x -> B y -> derivable (f ^~ y) x 1.

Variable G : Y -> R.
Hypothesis G_ge0 : forall y, 0 <= G y.
Hypothesis intG : mu.-integrable B (EFin \o G).
Hypothesis G_ub : forall x y, I x -> B y -> `|'d1 f y x| <= G y.

Let F x' := \int[mu]_(y in B) f x' y.

Lemma cvg_differentiation_under_integral :
  h^-1 *: (F (h + a) - F a) @[h --> 0^'] --> \int[mu]_(y in B) ('d1 f) y a.
Proof.
apply/cvgr_dnbhsP => t [t_neq0 t_cvg0].
suff: forall x_, (forall n : nat, x_ n != a) ->
      x_ n @[n --> \oo] --> a -> (forall n, I (x_ n)) ->
    (x_ n - a)^-1 *: (F (x_ n) - F a) @[n --> \oo] -->
      \int[mu]_(y in B) ('d1 f) y a.
  move=> suf.
  apply/cvgrPdist_le => /= r r0.
  have [rho /= rho0 arhouv] := near_in_itvoo Ia.
  move/cvgr_dist_lt : (t_cvg0) => /(_ _ rho0)[m _ t_cvg0'].
  near \oo => N.
  pose x k := a + t (N + k)%N.
  have x_a n : x n != a by rewrite /x addrC eq_sym -subr_eq subrr eq_sym t_neq0.
  have x_cvg_a : x n @[n --> \oo] --> a.
    apply: cvg_zero.
    rewrite [X in X @ _ --> _](_ : _ = (fun n => t (n + N)%N)); last first.
      by apply/funext => n; rewrite /x fctE addrAC subrr add0r addnC.
    by rewrite cvg_shiftn.
  have Ix n : I (x n).
    apply: arhouv => /=.
    rewrite /x opprD addrA subrr.
    apply: t_cvg0' => //=.
    by rewrite (@leq_trans N) ?leq_addr//; near: N; exists m.
  have /cvgrPdist_le/(_ _ r0)[n _ /=] := suf x x_a x_cvg_a Ix.
  move=> {}suf.
  near=> M.
  have /suf : (n <= M - N)%N.
    by rewrite leq_subRL; near: M; exact: nbhs_infty_ge.
  rewrite /x subnKC; last by near: M; exact: nbhs_infty_ge.
  by rewrite (addrC a) addrK.
move=> {t t_neq0 t_cvg0} x_ x_neqa x_cvga Ix_.
pose g_ n y : R := (f (x_ n) y - f a y) / (x_ n - a).
have mg_ n : measurable_fun B (fun y => (g_ n y)%:E).
  apply/measurable_EFinP/measurable_funM => //.
  apply: measurable_funB.
    by have /integrableP[/measurable_EFinP] := intf (Ix_ n).
  by have /integrableP[/measurable_EFinP] := intf Ia.
have intg_ m : mu.-integrable B (EFin \o g_ m).
  rewrite /g_ /comp/=.
  under eq_fun do rewrite EFinM.
  apply: integrableMl => //.
    under eq_fun do rewrite EFinB.
    by apply: integrableB; [by []|exact:intf..].
  exact: bounded_cst.
have Bg_G : {ae mu, forall y n, B y -> (`|(g_ n y)%:E| <= (EFin \o G) y)%E}.
  apply/aeW => y n By; rewrite /g_.
  have [axn|axn|<-] := ltgtP a (x_ n).
  - have axnI : `[a, (x_ n)] `<=` I.
      apply: subset_itvSoo; rewrite bnd_simp.
      + by have := Ia; rewrite /I/= in_itv/= => /andP[].
      + by have := Ix_ n; rewrite /I/= in_itv/= => /andP[].
    have x_fd1f x : x \in `]a, (x_ n)[ -> is_derive x 1 (f^~ y) (('d1 f) y x).
      move=> xax_n; apply: DeriveDef.
        by apply: derf1 => //; exact/axnI/subset_itv_oo_cc.
      by rewrite /partial1of2 derive1E.
    have cf : {within `[a, (x_ n)], continuous (f^~ y)}.
      have : {within I, continuous (f^~ y)}.
        by apply: derivable_within_continuous => /= r Ir; exact: derf1.
      by apply: continuous_subspaceW; exact: axnI.
    have [C caxn ->] := @MVT _ (f^~ y) (('d1 f) y) _ _ axn x_fd1f cf.
    rewrite -mulrA divff// ?subr_eq0// mulr1 lee_fin G_ub//.
    by move/subset_itv_oo_cc : caxn => /axnI.
  - have xnaI : `[(x_ n), a] `<=` I.
      apply: subset_itvSoo; rewrite bnd_simp.
      + by have := Ix_ n; rewrite /I/= in_itv/= => /andP[].
      + by have := Ia; rewrite /I/= in_itv/= => /andP[].
    have x_fd1f x : x \in `](x_ n), a[ -> is_derive x 1 (f^~ y) (('d1 f) y x).
      move=> xax_n; apply: DeriveDef.
        by apply: derf1 => //; exact/xnaI/subset_itv_oo_cc.
      by rewrite partial1of2E.
    have cf : {within `[(x_ n), a], continuous (f^~ y)}.
      have : {within I, continuous (f^~ y)}.
        by apply: derivable_within_continuous => /= r Ir; exact: derf1.
      by apply: continuous_subspaceW; exact: xnaI.
    have [C caxn] := @MVT _ (f^~ y) (('d1 f) y) _ _ axn x_fd1f cf.
    rewrite abse_EFin normrM distrC => ->.
    rewrite normrM -mulrA distrC normfV divff// ?normr_eq0 ?subr_eq0//.
    rewrite mulr1 lee_fin G_ub//.
    by move/subset_itv_oo_cc : caxn => /xnaI.
  - by rewrite subrr mul0r abse0 lee_fin.
have g_cvg_d1f : forall y, B y -> (g_ n y)%:E @[n --> \oo] --> (('d1 f) y a)%:E.
  move=> y By; apply/fine_cvgP; split; first exact: nearW.
  rewrite /comp/=.
  have /cvg_ex[/= l fayl] := derf1 Ia By.
  have d1fyal : ('d1 f) y a = l.
    apply/cvg_lim => //.
    by move: fayl; under eq_fun do rewrite scaler1.
  have xa0 : (forall n, x_ n - a != 0) /\ x_ n - a @[n --> \oo] --> 0.
    by split=> [x|]; [rewrite subr_eq0|exact/subr_cvg0].
  move: fayl => /cvgr_dnbhsP/(_ _ xa0).
  under [in X in X -> _]eq_fun do rewrite scaler1 subrK.
  move=> xa_l.
  suff : (f (x_ x) y - f a y) / (x_ x - a) @[x --> \oo] --> ('d1 f) y a by [].
  rewrite d1fyal.
  by under eq_fun do rewrite mulrC.
have mdf : measurable_fun B (fun y => (('d1 f) y a)%:E).
  by apply: emeasurable_fun_cvg g_cvg_d1f => m; exact: mg_.
have [intd1f g_d1f_0 _] := @dominated_convergence _ _ _ mu _ mB
  (fun n y => (g_ n y)%:E) _ (EFin \o G) mg_ mdf (aeW _ g_cvg_d1f) intG
  Bg_G.
rewrite /= in g_d1f_0.
rewrite [X in X @ _ --> _](_ : _ =
    (fun h => \int[mu]_(z in B) g_ h z)); last first.
  apply/funext => m; rewrite /F -RintegralB; [|by []|exact: intf..].
  rewrite -[LHS]RintegralZl; [|by []|].
  - by apply: eq_Rintegral => y _; rewrite mulrC.
  - rewrite /comp; under eq_fun do rewrite EFinB.
    by apply: integrableB => //; exact: intf.
apply/subr_cvg0.
rewrite [X in X @ _ --> _](_ : _ =
    (fun x => \int[mu]_(z in B) (g_ x z - ('d1 f) z a)))%R; last first.
  by apply/funext => n; rewrite RintegralB.
apply: norm_cvg0.
have {}g_d1f_0 : (\int[mu]_(x in B) `|g_ n x - ('d1 f) x a|) @[n --> \oo] --> 0.
  exact/fine_cvg.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) _ _ _ _ _ g_d1f_0) => //.
- apply/nearW => n.
  rewrite /= normr_ge0/= le_normr_integral//.
  rewrite /comp; under eq_fun do rewrite EFinB.
  by apply: integrableB => //; exact: intg_.
- exact: cvg_cst.
Unshelve. all: end_near. Qed.

Lemma differentiation_under_integral :
  F^`() a = \int[mu]_(y in B) ('d1 f y) a.
Proof.
rewrite /derive1.
by have /cvg_lim-> //:= cvg_differentiation_under_integral.
Qed.

Lemma derivable_under_integral : derivable F a 1.
Proof.
apply/cvg_ex => /=; exists (\int[mu]_(y in B) ('d1 f y) a).
under eq_fun do rewrite scaler1.
exact: cvg_differentiation_under_integral.
Qed.

End differentiation_under_integral.

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
rewrite Rintegral_setU//=; last 2 first.
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

End integration_by_substitution.
