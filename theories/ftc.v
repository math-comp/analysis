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

(* TODO: move to normedtype.v? *)
Lemma nbhs_right_lt_lt {R : realType} (x y : R) :
  (y < x)%R -> \forall z \near nbhs y^'+, (z < x)%R.
Proof.
move=> yx.
exists (x - y)%R => /=; first by rewrite subr_gt0.
move=> z/= /[swap] yz.
by rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl addrC subrK.
Qed.

(* TODO: move to normedtype.v? *)
Lemma nbhs_right_lt_le {R : realType} (x y : R) :
  (y < x)%R -> \forall z \near nbhs y^'+, (z <= x)%R.
Proof.
by move=> yx; near=> z; apply/ltW; near: z; exact: nbhs_right_lt_lt.
Unshelve. all: by end_near. Qed.

(* TODO: move to normedtype.v? *)
Lemma cvg_patch {R : realType} (f : R -> R^o) (a b : R) (x : R) : (a < b)%R ->
  x \in `]a, b[ ->
  f @ (x : subspace `[a, b]) --> f x ->
  (f \_ `[a, b] x) @[x --> x] --> f x.
Proof.
move=> ab xab xf; apply/cvgrPdist_lt => /= e e0.
move/cvgrPdist_lt : xf => /(_ e e0) xf.
rewrite near_simpl; near=> z.
rewrite patchE ifT//; last first.
  rewrite inE; apply: subset_itv_oo_cc.
  by near: z; exact: near_in_itv.
near: z.
rewrite /prop_near1 /nbhs/= /nbhs_subspace ifT// in xf; last first.
  by rewrite inE/=; exact: subset_itv_oo_cc xab.
case: xf => x0 /= x00 xf.
near=> z.
apply: xf => //=.
rewrite inE; apply: subset_itv_oo_cc.
by near: z; exact: near_in_itv.
Unshelve. all: by end_near. Qed.

Section FTC.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a : itv_bound R).

Let FTC0 f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  locally_integrable setT (f \_ [set` Interval a (BRight u)]) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) f t)%R in
  a < BRight x -> lebesgue_pt f x ->
    h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> xz intf locf F ax fx.
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
  have ixdf : {near \oo,
      (fun n => \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E) =1
      (fun n => \int[mu]_(y in E x n) (f y)%:E)}.
    move/cvgrPdist_le : d0 => /(_ (u - x)%R).
    rewrite subr_gt0 => /(_ xz) [m _ d0].
    near=> n.
    have xdu : (x + d n <= u)%R.
      rewrite -lerBrDl.
      have /= := d0 n; rewrite sub0r normrN gtr0_norm//; apply.
      by near: n; exists m.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      apply: (@measurable_funS _ _ _ _ [set` Interval a (BRight u)]) => //.
        by apply: subset_itvl; rewrite bnd_simp.
      by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
    rewrite (@itv_bndbnd_setU _ _ _ (BLeft x))//=; last 2 first.
      by case: a ax F {intf locf} => [[|] a|[|]]// /ltW.
      by rewrite bnd_simp lerDl ltW.
    rewrite integral_setU_EFin//=.
    + rewrite addeAC -[X in _ - X]integral_itv_bndo_bndc//=; last first.
        apply (@measurable_funS _ _ _ _ [set` Interval a (BRight u)]) => //.
          by apply: subset_itvl; rewrite bnd_simp ltW.
        by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
      rewrite subee ?add0e// integral_fune_fin_num//=.
      apply: integrableS intf => //=.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    + rewrite -itv_bndbnd_setU//; last 2 first.
        (* TODO: lemma? *)
(*        move/lt_ereal_bnd : ax. WIP *)
        have /(_ (BLeft x)) := lt_le_trans ax.
        by rewrite bnd_simp => /(_ isT)/lt_ereal_bnd/ltW.
        by rewrite bnd_simp lerDl ltW.
      apply (@measurable_funS _ _ _ _ [set` Interval a (BRight u)]) => //.
        by apply: subset_itvl; rewrite bnd_simp.
      by have [/(measurable_restrictT _ _).2+ _ _] := locf; apply.
    + apply/disj_setPRL; rewrite setCitv/=.
      exact: subset_trans (subset_itvl _) (@subsetUr _ _ _).
  suff: (d n)^-1 *: fine (\int[mu]_(t in E x n) (f t)%:E) @[n --> \oo] --> f x.
    apply: cvg_trans; apply: near_eq_cvg.
    move/cvgrPdist_le : d0 => /(_ (u - x)%R).
    rewrite subr_gt0 => /(_ xz)[m /= _] H.
    near=> n.
    have dxu : ((d n + x)%E <= u)%R.
      rewrite -lerBrDr.
      have /= := H n; rewrite sub0r normrN gtr0_norm//; apply.
      by near: n; exists m.
    congr (_ *: _); rewrite -fineB/=;
      [|apply: integral_fune_fin_num..] => //=; last 2 first.
        apply: integrableS intf => //=.
        by apply: subset_itvl; rewrite bnd_simp.
        apply: integrableS intf => //=.
        by apply: subset_itvl; rewrite bnd_simp ltW.
    rewrite /= (addrC (d n) x).
    by near: n; apply: filterS ixdf => k ->.
  have {}locf : \forall r \near 0^'+,
      locally_integrable [set: R] (f \_ (closed_ball x r)).
    case: a intf locf F ax ixdf => [| [|//] intf locf _ ax ixdf]; last first.
      near=> r.
      rewrite closed_ball_itv//.
      apply: locally_integrableS locf => //.
      apply: (@subset_trans _ `]-oo, (x + r)]) => //; first exact: subset_itvr.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
    move=> b a intf locf _ ax ixdf.
    case: b in intf locf ax ixdf *; rewrite /= lte_fin in ax.
    + near=> r.
      rewrite closed_ball_itv//.
      apply: (@locally_integrableS _ _ `[a, (x + r)]) => //.
        apply: subset_itvr.
        rewrite bnd_simp -lerBlDr opprK -lerBrDl.
        by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
      apply: locally_integrableS locf => //.
      apply: subset_itvl; rewrite bnd_simp/= -lerBrDl.
      by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
    + near=> r.
      apply: (@locally_integrableS _ _ `]a, (x + r)]) => //.
        exact: measurable_closed_ball.
        rewrite closed_ball_itv//.
        apply: subset_itvr.
        rewrite bnd_simp -ltrBlDr opprK -ltrBrDl.
        by near: r; apply: nbhs_right_lt_lt; rewrite subr_gt0.
      apply: locally_integrableS locf => //.
      apply: subset_itvl; rewrite bnd_simp/= -lerBrDl.
      by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  rewrite [g in g n @[n --> _] --> _ -> _](_ : _ =
      fun n => (d n)^-1%:E * \int[mu]_(y in E x n) (f y)%:E); last first.
    by apply/funext => n; rewrite muE.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  set h := (f in f n @[n --> \oo] --> _).
  apply: cvg_trans gf; apply: near_eq_cvg.
  move/cvgrPdist_le : d0 => /(_ (u - x)%R).
  rewrite subr_gt0 => /(_ xz)[m /= _] H.
  near=> n.
  rewrite /g /h /= fineM// integral_fune_fin_num//; first exact: (nice_E _).1.
  apply: integrableS intf => //=; first exact: (nice_E _).1.
  apply: subset_trans (@subset_itvl _ _ _ (BLeft (x + d n)) _ _); last first.
    rewrite bnd_simp -lerBrDl.
    have /= := H n; rewrite sub0r normrN gtr0_norm//; apply.
    by near: n; exists m.
  apply: subset_itvr => //.
  (* TODO: lemma? *)
  have /(_ (BLeft x)) := lt_le_trans ax.
  by rewrite bnd_simp => /(_ isT)/lt_ereal_bnd/ltW.
- apply/cvg_at_leftP => d [d_gt0 d0].
  have {}Nd_gt0 n : (0 < - d n)%R by rewrite ltrNr oppr0.
  pose E x n := `]x + d n, x]%classic%R.
  have muE y n : mu (E y n) = (- d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin -ltrBrDr.
    by rewrite ltrDl Nd_gt0 -EFinD opprD addrA subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, (fun n => PosNum (Nd_gt0 n))); split => //=.
    + by rewrite -oppr0; exact: cvgN.
    + move=> n; rewrite /E ball_itv opprK.
      by apply: subset_itvl; rewrite bnd_simp ltrDl.
    + move=> n; rewrite lebesgue_measure_ball//; last exact: ltW.
      by rewrite -/mu muE -EFinM lee_fin mulr_natl.
  have ixdf : {near \oo,
      (fun n => \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E) =1
      (fun n => - \int[mu]_(y in E x n) (f y)%:E)}.
    case: a ax intf locf {F}; last first.
      move=> [_ intf locf|//].
      near=> n.
      rewrite -[in LHS]integral_itv_bndo_bndc//=; last first.
         apply: (@measurable_funS _ _ _ _ `]-oo, u]) => //.
           apply: subset_itvl; rewrite bnd_simp.
           by rewrite -lerBrDl (@le_trans _ _ 0%R)// ?ltW// subr_gt0.
         by case: locf => /(measurable_restrictT _ _).2 + _ _; apply.
      rewrite -/mu -[LHS]oppeK; congr oppe.
      rewrite oppeB; last first.
        rewrite fin_num_adde_defl// fin_numN// integral_fune_fin_num//=.
        apply: integrableS intf => //=.
        by apply: subset_itvl => //=; rewrite bnd_simp ltW.
      rewrite addeC.
      rewrite (_ : `]-oo, x] = `]-oo, (x + d n)%R] `|` E x n)%classic; last first.
        by rewrite -itv_bndbnd_setU//= bnd_simp ler_wnDr// ltW.
      rewrite integral_setU_EFin//=.
      + rewrite addeAC -[X in X - _]integral_itv_bndo_bndc//; last first.
          apply: (@measurable_funS _ _ _ _ `]-oo, u]) => //.
            apply: subset_itvl; rewrite bnd_simp//.
            by rewrite -lerBrDl (@le_trans _ _ 0%R)// ltW// subr_gt0.
          by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
        rewrite subee ?add0e// integral_fune_fin_num//=.
        apply: integrableS intf => //=.
        apply: subset_itvl; rewrite bnd_simp.
        by rewrite -lerBrDl (@le_trans _ _ 0%R)// ltW// subr_gt0.
      + exact: (nice_E _).1.
      + rewrite -itv_bndbnd_setU//; last first.
          by rewrite bnd_simp ler_wnDr// ltW.
        apply: (@measurable_funS _ _ _ _ `]-oo, u]) => //.
          by apply: subset_itvl; rewrite bnd_simp// ltW.
        by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
      + by apply/disj_setPLR; rewrite setCitv/=; exact: subsetUl.
    move=> b a ax intf locf.
    move/cvgrPdist_le : (d0) => /(_ (x - a)%R).
    rewrite subr_gt0 => /(_ ax)[m /= _]d0xa.
    move/cvgrPdist_le : d0 => /(_ (u - x)%R).
    rewrite subr_gt0 => /(_ xz)[k /= _]d0ux.
    near=> n.
    have mn : (m <= n)%N by near: n; exists m.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      apply: (@measurable_funS _ _ _ _ [set` Interval (BSide b a) (BRight u)]) => //.
        apply: subset_itvl; rewrite bnd_simp.
        by rewrite -lerBrDl (@le_trans _ _ 0%R)// ltW// subr_gt0.
      by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
    rewrite -/mu -[LHS]oppeK; congr oppe.
    rewrite oppeB; last first.
      rewrite fin_num_adde_defl// fin_numN// integral_fune_fin_num//=.
      apply: integrableS intf => //.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    rewrite addeC.
    rewrite (@itv_bndbnd_setU _ _ _ (BRight (x - - d n)%R))//; last 2 first.
      case: b in ax intf locf * => /=; rewrite bnd_simp.
        rewrite lerBrDl addrC -lerBrDl.
        by have := d0xa _ mn; rewrite sub0r gtr0_norm.
      rewrite lerBrDl -lerBrDr.
      by have := d0xa _ mn; rewrite sub0r gtr0_norm.
      by rewrite opprK bnd_simp -lerBrDl subrr ltW.
    rewrite integral_setU_EFin//=.
    + rewrite addeAC -[X in X - _]integral_itv_bndo_bndc//; last first.
        apply: (@measurable_funS _ _ _ _ [set` Interval (BSide b a) (BRight u)]) => //.
          apply: subset_itvl; rewrite bnd_simp//.
          by rewrite -lerBrDl opprK (@le_trans _ _ 0%R)// ltW// subr_gt0.
        by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
      rewrite opprK subee ?add0e// integral_fune_fin_num => //=.
      apply: integrableS intf => //.
      apply: subset_itvl.
      by rewrite bnd_simp -lerBrDl (@le_trans _ _ 0%R)// ltW// subr_gt0.
    + rewrite -itv_bndbnd_setU//; last 2 first.
        case: b in ax intf locf * => /=; rewrite bnd_simp.
          rewrite lerBrDl addrC -lerBrDl.
          by have := d0xa _ mn; rewrite sub0r gtr0_norm.
        rewrite lerBrDl -lerBrDr.
        by have := d0xa _ mn; rewrite sub0r gtr0_norm.
        by rewrite opprK bnd_simp -lerBrDl subrr ltW.
      apply: (@measurable_funS _ _ _ _ [set` Interval (BSide b a) (BRight u)]) => //.
        by apply: subset_itvl; rewrite bnd_simp ltW.
      by have [/(measurable_restrictT _ _).2 + _ _] := locf; apply.
    + apply/disj_setPLR; rewrite opprK setCitv/=.
      exact: subset_trans (subset_itvr _) (subsetUl _).
  suff: ((d n)^-1 * - fine (\int[mu]_(y in E x n) (f y)%:E))%R
          @[n --> \oo] --> f x.
    apply: cvg_trans; apply: near_eq_cvg; near=> n;  congr (_ *: _).
    rewrite /F -fineN -fineB; last 2 first.
      apply: integral_fune_fin_num => //; apply: integrableS intf => //.
      apply: subset_itvl; rewrite bnd_simp.
      rewrite -lerBrDr.
      by rewrite (@le_trans _ _ 0%R)// ltW// subr_gt0.
      apply: integral_fune_fin_num => //; apply: integrableS intf => //.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    by congr fine => /=; apply/esym; rewrite (addrC _ x); near: n.
  have {}locf : \forall r \near 0^'+, locally_integrable [set: R] (f \_ (closed_ball x r)).
    case: a intf locf F ax ixdf => [|[|//] intf locf _ _ ixdf]; last first.
      near=> r.
      rewrite closed_ball_itv//.
      apply: (@locally_integrableS _ _ [set` `]-oo, (x + r)]]) => //.
        exact: subset_itvr.
      apply: locally_integrableS locf => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
    move=> b a intf locf _; rewrite /= lte_fin => ax ixdf.
    case: b in intf locf ixdf *.
      near=> r.
      rewrite closed_ball_itv//.
      apply: (@locally_integrableS _ _ `[a, (x + r)]) => //.
        apply: subset_itvr.
        rewrite bnd_simp -lerBlDr opprK -lerBrDl.
        by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
      apply: locally_integrableS locf => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
    near=> r.
    apply: (@locally_integrableS _ _ `]a, (x + r)]) => //.
      exact: measurable_closed_ball.
      rewrite closed_ball_itv//.
      apply: subset_itvr.
      rewrite bnd_simp -ltrBlDr opprK -ltrBrDl.
      by near: r; apply: nbhs_right_lt_lt; rewrite subr_gt0.
    apply: locally_integrableS locf => //.
    apply: subset_itvl; rewrite bnd_simp -lerBrDl.
    by near: r; apply: nbhs_right_lt_le; rewrite subr_gt0.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  apply: cvg_trans gf.
  move: a ax intf {F} => [[t/=|t/=]|[|//]]; rewrite ?lte_fin => tx intf.
  + move/cvgrPdist_le : d0 => /= /(_ (x - t)%R).
    rewrite subr_gt0 => /(_ tx)[k /= _] H.
    apply: near_eq_cvg; near=> n.
    rewrite /g /= fineM//=; last first.
      apply: integral_fune_fin_num => //=; first exact: (nice_E _).1.
      apply: integrableS (intf)%R => //=; first exact: (nice_E _).1.
      apply: (@subset_trans _ `[t, x]).
        apply: subset_itvr; rewrite bnd_simp -lerBlDr addrC -(opprK t) lerBlDr.
        have /= := H n; rewrite gtr0_norm ?sub0r//; apply.
        by near: n; exists k.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    by rewrite muE/= invrN mulNr -mulrN.
  + move/cvgrPdist_le : d0 => /= /(_ (x - t)%R).
    rewrite subr_gt0 => /(_ tx)[k /= _] H.
    apply: near_eq_cvg; near=> n.
    rewrite /g /= fineM//=; last first.
      apply: integral_fune_fin_num => //=; first exact: (nice_E _).1.
      apply: integrableS (intf)%R => //=; first exact: (nice_E _).1.
      apply: (@subset_trans _ `]t, x]).
        apply: subset_itvr; rewrite bnd_simp -lerBlDr addrC -(opprK t) lerBlDr.
        have /= := H n; rewrite gtr0_norm ?sub0r//; apply.
        by near: n; exists k.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    by rewrite muE/= invrN mulNr -mulrN.
  + rewrite (@eq_cvg _ _ _ _ g)// => n.
    rewrite /g /= fineM//=; last first.
      apply: integral_fune_fin_num => //=; first exact: (nice_E _).1.
      apply: integrableS intf => //=; first exact: (nice_E _).1.
      apply: (@subset_trans _ (`]-oo, x])); first exact: subset_itvr.
      by apply: subset_itvl; rewrite bnd_simp ltW.
    by rewrite muE/= invrN mulNr mulrN.
Unshelve. all: by end_near. Qed.

(* NB: right-closed interval *)
Lemma FTC1_lebesgue_pt f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  locally_integrable setT (f \_ [set` Interval a (BRight u)]) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) (f t))%R in
  a < BRight x -> lebesgue_pt f x ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu intf locf F ax fx; split; last first.
  apply/cvg_lim; [exact: Rhausdorff|].
  exact: (@FTC0 _ _ _ u).
apply/cvg_ex; exists (f x).
have /= := FTC0 xu intf locf ax fx.
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
move=> intf locf F.
move: (locf).
move/lebesgue_differentiation.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
move=> i fi ai.
apply: (@FTC1_lebesgue_pt _ _ _ (i + 1)%R) => //.
  by rewrite ltrDl.
apply: (@locally_integrableS _ _ setT) => //.
by rewrite patch_setT.
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

Corollary continuous_FTC1 f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  locally_integrable setT (f \_ [set` Interval a (BRight u)]) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  a < BRight x -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu fi locf F ax fx.
have lfx : lebesgue_pt f x; last first.
  have /= /(_ ax lfx)/= [dfx f'xE] := @FTC1_lebesgue_pt f a x _ xu fi locf.
  by split; [exact: dfx|rewrite f'xE].
case: a fi locf F ax => [|[|//] fi locf _ _]; last first.
  near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - have /measurable_int/EFin_measurable_fun := fi.
    apply: measurable_funS => //.
    rewrite ball_itv.
    apply: (@subset_trans _ (`](x - e)%R, u])) => //.
      apply: subset_itvl; rewrite bnd_simp.
      rewrite -lerBrDl.
      by near: e; apply: nbhs_right_lt_le; rewrite subr_gt0.
    exact: subset_itvr.
move=> b a fi locf _ /=; rewrite lte_fin => ax.
case: b fi locf => [|] fi locf.
  near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - have /measurable_int/EFin_measurable_fun := fi.
    apply: measurable_funS => //.
    rewrite ball_itv.
    apply: (@subset_trans _ (`](x - e)%R, u])) => //.
      apply: subset_itvl; rewrite bnd_simp.
      rewrite -lerBrDl.
      by near: e; apply: nbhs_right_lt_le; rewrite subr_gt0.
    apply: subset_itvr; rewrite bnd_simp.
    rewrite lerBrDr -lerBrDl.
    by near: e; apply: nbhs_right_lt_le; rewrite subr_gt0.
near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
- exact: ball_open_nbhs.
- exact: measurable_ball.
- have /measurable_int/EFin_measurable_fun := fi.
  apply: measurable_funS => //.
  rewrite ball_itv.
  apply: (@subset_trans _ (`](x - e)%R, u])) => //.
    apply: subset_itvl; rewrite bnd_simp.
    rewrite -lerBrDl.
    by near: e; apply: nbhs_right_lt_le; rewrite subr_gt0.
  apply: subset_itvr; rewrite bnd_simp.
  rewrite lerBrDr -lerBrDl.
  by near: e; apply: nbhs_right_lt_le; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Corollary continuous_FTC1_closed f (a x : R) (u : R) : (x < u)%R ->
  locally_integrable setT (f \_ [set` Interval (BLeft a) (BRight u)]) ->
  let F x := (\int[mu]_(t in [set` Interval (BLeft a) (BRight x)]) (f t))%R in
  (a < x)%R -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu locf F ax fx.
apply: (@continuous_FTC1 _ _ _ u) => //.
apply/integrableP; split.
  apply/EFin_measurable_fun.
  by case: locf => /(measurable_restrictT _ _ ).2 + _ _; apply.
rewrite integralEpatch//=.
under eq_integral do rewrite restrict_EFin/= restrict_normr/=.
rewrite /=.
case: locf => _ _; apply => //.
exact: segment_compact.
Qed.

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
move=> ab intf; apply/(continuous_within_itvP _ ab); split; last first.
  split; last exact: parameterized_integral_cvg_at_left.
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
    by apply: subset_itvS; rewrite bnd_simp; exact/ltW.
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
  rewrite -opprB normrN Rintegral_itvB ?bnd_simp; last 3 first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
    exact/ltW.
    exact/ltW.
  rewrite Rintegral_itv_obnd_cbnd//; last first.
    by apply: integrableS intf => //; apply: subset_itvS => //; exact/ltW.
  have zxab : `[z, x] `<=` `[a, b].
    by apply: subset_itvS; rewrite bnd_simp; exact/ltW.
  apply: (le_trans (le_normr_integral _ _)) => //; first exact: integrableS intf.
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
have locfab : locally_integrable [set: R] fab.
  split.
  - move: iabf => /(integrable_mkcond _ _).1 /=.
    move=> /(_ (measurable_itv _)) /integrableP[+ _].
    by rewrite restrict_EFin => /EFin_measurable_fun.
  - exact: openT.
  - move=> K _ cK.
    under eq_integral.
      move=> x xK.
      rewrite /fab.
      rewrite -[_%:E]/((EFin \o (normr \o f \_ `[a, b])) x).
      rewrite -restrict_normr.
      rewrite -restrict_EFin.
      over.
    rewrite /=.
    rewrite -integral_mkcondr/=.
    move: iabf => /integrableP[mabf].
    apply: le_lt_trans; apply: ge0_subset_integral => //=.
      by apply: measurableI => //; exact: compact_measurable.
    apply/EFin_measurable_fun => //=;apply/measurableT_comp => //.
    exact/EFin_measurable_fun.
have G'f : {in `]a, b[, forall x, G^`() x = fab x /\ derivable G x 1}.
  move=> x /[!in_itv]/= /andP[ax xb].
  have := @continuous_FTC1_closed _ fab a x b xb.
  rewrite -patch_setI setIid => /(_ locfab).
  move=> /(_ ax).
  have : {for x, continuous fab}.
    have : x \in `[a, b] by rewrite in_itv/= (ltW ax) (ltW xb).
    move: cf => /(_ x).
    rewrite {1}/continuous_at => xf xab.
    rewrite /prop_for /continuous_at {2}/fab/= patchE.
    rewrite mem_set ?mulr1 /=; last by rewrite in_itv/= (ltW ax) (ltW xb).
    apply: cvg_patch => //.
    by rewrite in_itv/= ax xb.
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
        (* TODO: lemma? *)
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
have Ga0 : G a = 0%R by rewrite /G interval_set1// Rintegral_set1.
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
  apply/(continuous_within_itvP _ ab); split; last exact: (conj Fa Fb).
  move=> z zab.
  apply/differentiable_continuous/derivable1_diffP.
  by case: dF => /= dF _ _; apply: dF.
have iabfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //; rewrite setIidr.
have Ga : G x @[x --> a^'+] --> G a.
   have := parameterized_integral_cvg_left ab iabfab.
   rewrite (_ : 0 = G a)%R.
     by move=> /left_right_continuousP[].
   by rewrite /G interval_set1 Rintegral_set1.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (parameterized_integral_cvg_at_left ab iabfab).
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
    {within `[a, b], continuous f} -> {within `[a, b], continuous F} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} -> {within `[a, b], continuous G} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x)%:E = (F b * G b - F a * G a)%:E -
  \int[mu]_(x in `[a, b]) (f x * G x)%:E.
Proof.
move=> ab cf cF Fab Ff cg cG Gab Gg.
have cfg : {within `[a, b], continuous (f * G + F * g)%R}.
  apply/subspace_continuousP => x abx; apply: cvgD.
  - apply: cvgM.
    + by move/subspace_continuousP : cf; exact.
    + by move/subspace_continuousP : cG; exact.
  - apply: cvgM.
    + by move/subspace_continuousP : cF; exact.
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
  + by move/subspace_continuousP : cG; exact.
rewrite /= integralD//=.
- by rewrite addeAC subee ?add0e// integral_fune_fin_num.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx;apply: cvgM.
  + by move/subspace_continuousP : cF; exact.
  + by move/subspace_continuousP : cg; exact.
Qed.

End integration_by_parts.

Section Rintegration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma Rintegration_by_parts F G f g a b :
    (a < b)%R ->
    {within `[a, b], continuous f} -> {within `[a, b], continuous F} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} -> {within `[a, b], continuous G} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x) = (F b * G b - F a * G a) -
  \int[mu]_(x in `[a, b]) (f x * G x).
Proof.
move=> ab cf cF Fab Ff cg cG Gab Gg.
rewrite [in LHS]/Rintegral (@integration_by_parts R F G f g)// fineB//.
suff: mu.-integrable `[a, b] (fun x => (f x * G x)%:E).
  move=> /integrableP[? abfG]; apply: fin_real.
  rewrite (_ : -oo = - +oo)%E// -lte_absl.
  by apply: le_lt_trans abfG; exact: le_abse_integral.
apply: continuous_compact_integrable.
  exact: segment_compact.
by move=> /= z; apply: continuousM; [exact: cf|exact: cG].
Qed.

End Rintegration_by_parts.
