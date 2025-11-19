(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import function_spaces derive esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun simple_functions.
From mathcomp Require Import lebesgue_integral_definition.
From mathcomp Require Import lebesgue_integral_nonneg.
From mathcomp Require Import lebesgue_integrable lebesgue_Rintegral.
From mathcomp Require Import lebesgue_integral_dominated_convergence.

(**md**************************************************************************)
(* # Continuity and differentiation under the integral sign                   *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*               partial1of2 f == first partial derivative of f               *)
(*                                f has type R -> T -> R for R : realType     *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "'d1 f" (at level 10, f at next level, format "''d1'  f").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section continuity_under_integral.
Context {R : realType} d {Y : measurableType d}
  {mu : {measure set Y -> \bar R}}.

Variable f : R -> Y -> R.
Variable B : set Y.
Hypothesis mB : measurable B.

Variable u v : R.
Let I : set R := `]u, v[.

Hypothesis int_f : forall x, I x -> mu.-integrable B (EFin \o (f x)).
Hypothesis cf : {ae mu, forall y, B y -> {in I, continuous (f ^~ y)}}.

Variable g : Y -> R.

Hypothesis int_g : mu.-integrable B (EFin \o g).
Hypothesis g_ub : forall x, I x -> {ae mu, forall y, B y -> `|f x y| <= g y}.

Let F x := (\int[mu]_(y in B) f x y)%R.

Lemma continuity_under_integral :
  {in I, continuous (fun l => \int[mu]_(x in B) f l x)}.
Proof.
move=> a /set_mem Ia.
have [Z [mZ Z0 /subsetCPl ncfZ]] := cf.
have BZ_cf x : x \in B `\` Z -> {in I, continuous (f ^~ x)}.
  by rewrite inE/= => -[Bx nZx]; exact: ncfZ.
have [vu|uv] := lerP v u.
  by move: (Ia); rewrite /I set_itv_ge// -leNgt bnd_simp.
apply/cvg_nbhsP => w wa.
have /near_in_itvoo[e /= e0 aeuv] : a \in `]u, v[ by rewrite inE.
move/cvgrPdist_lt : (wa) => /(_ _ e0)[N _ aue].
have IwnN n : I (w (n + N)) by apply: aeuv; apply: aue; exact: leq_addl.
have : forall n, {ae mu, forall y, B y -> `|f (w (n + N)) y| <= g y}.
  by move=> n; exact: g_ub.
move/choice  => [/= U /all_and3[mU U0 Ug_ub]].
have mUU n : measurable (\big[setU/set0]_(k < n) U k).
  exact: bigsetU_measurable.
set UU := \bigcup_n U n.
have mUUoo : measurable UU by exact: bigcup_measurable.
have {U0}UU0 : mu UU = 0.
  rewrite /UU seqDU_bigcup_eq measure_bigcup//; last first.
    by move=> ? _; apply: measurableD => //; exact: bigsetU_measurable.
  apply: eseries0 => n _ _; apply/eqP; rewrite -measure_le0.
  rewrite -[leRHS](U0 n) le_measure ?inE//; first exact: measurableD.
  exact: subIsetl.
set ZUU := Z `|` UU.
have mZUU : measurable ZUU by exact: measurableU.
have {Z0 UU0}ZUU0 : mu ZUU = 0.
  apply/eqP; rewrite -measure_le0.
  by rewrite (le_trans (measureU2 _ _ mUUoo))// [X in X + _]Z0 add0e [leLHS]UU0.
have : {near \oo, (fun n => \int[mu]_(x in B `\` ZUU) f (w n) x) =1
        (fun n => \int[mu]_(x in B) f (w n) x)}.
  move: (Ia); rewrite /I/= in_itv/= => /andP[ua av].
  near=> t.
  rewrite /Rintegral [in RHS](negligible_integral mZUU)//.
  apply: int_f.
  rewrite /I/= in_itv/=; apply/andP; split.
  - by near: t; exact: (cvgr_gt a).
  - by near: t; exact: (cvgr_lt a).
move/near_eq_cvg/cvg_trans; apply.
rewrite -(cvg_shiftn N).
apply: fine_cvg.
rewrite /Rintegral (negligible_integral mZUU)//; last exact: int_f.
rewrite fineK; last first.
  rewrite fin_num_abs -(negligible_integral mZUU)//; last exact: int_f.
  by have /integrableP[? ?] := int_f Ia; exact/abse_integralP.
apply: (@dominated_cvg _ _ _ mu _ _
    (fun n x => (f (w (n + N)) x)%:E) _ (EFin \o g)) => //=.
- exact: measurableD.
- move=> n; apply/(measurable_int mu)/(integrableS mB).
  + exact: measurableD.
  + exact: subIsetr.
  + exact/int_f/aeuv/aue/leq_addl.
- move=> x BZUUx.
  have {}BZUUx : x \in B `\`ZUU by rewrite inE.
  apply: cvg_EFin; first exact: nearW.
  have : x \in B `\` Z.
    move: BZUUx; rewrite inE/= => -[Bx nZUUx]; rewrite inE/=; split => //.
    by apply: contra_not nZUUx; left.
  move/(BZ_cf x)/(_ a); move/mem_set : Ia => /[swap] /[apply].
  by move/cvg_nbhsP; apply; rewrite (cvg_shiftn N).
- by apply: (integrableS mB) => //; exact: measurableD.
- move=> n x [Bx ZUUx]; rewrite lee_fin.
  move/subsetCPl : (Ug_ub n); apply => //=.
  by apply: contra_not ZUUx => ?; right; exists n.
Unshelve. end_near. Qed.

End continuity_under_integral.

Section differentiation_under_integral.

Definition partial1of2 {R : realType} {T : Type} (f : R -> T -> R) : R -> T -> R := fun x y => (f ^~ y)^`() x.

Local Notation "'d1 f" := (partial1of2 f).

Lemma partial1of2E {R : realType} {T : Type} (f : R -> T -> R) x y :
  ('d1 f) x y = 'D_1 (f^~ y) x.
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
Hypothesis G_ub : forall x y, I x -> B y -> `|'d1 f x y| <= G y.

Let F x' := \int[mu]_(y in B) f x' y.

Lemma cvg_differentiation_under_integral :
  h^-1 *: (F (h + a) - F a) @[h --> 0^'] --> \int[mu]_(y in B) ('d1 f) a y.
Proof.
apply/cvgr_dnbhsP => t [t_neq0 t_cvg0].
suff: forall x_, (forall n : nat, x_ n != a) ->
      x_ n @[n --> \oo] --> a -> (forall n, I (x_ n)) ->
    (x_ n - a)^-1 *: (F (x_ n) - F a) @[n --> \oo] -->
      \int[mu]_(y in B) ('d1 f) a y.
  move=> suf.
  apply/cvgrPdist_le => /= r r0.
  have [rho /= rho0 arhouv] := near_in_itvoo Ia.
  move/cvgr0_norm_lt: (t_cvg0) => /(_ _ rho0)[m _ t_cvg0'].
  near \oo => N.
  pose x k := a + t (N + k)%N.
  have x_a n : x n != a by rewrite /x addrC eq_sym -subr_eq subrr eq_sym t_neq0.
  have x_cvg_a : x n @[n --> \oo] --> a.
    apply: cvg_zero.
    suff ->: (x - cst a) = (fun n => t (n + N)%N) by rewrite cvg_shiftn.
    by apply/funext => n; rewrite !fctE [x _]addrC addrK addnC.
  have Ix n : I (x n).
    apply: arhouv => /=.
    rewrite opprD addNKr normrN.
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
  apply/aeW => y n By; rewrite /g_ lee_fin normf_div.
  have [axn|axn|<-] := ltgtP a (x_ n).
  - have axnI : `[a, (x_ n)] `<=` I.
      apply: subset_itvSoo; rewrite bnd_simp.
      + by have := Ia; rewrite /I/= in_itv/= => /andP[].
      + by have := Ix_ n; rewrite /I/= in_itv/= => /andP[].
    have x_fd1f x : x \in `]a, (x_ n)[ -> is_derive x 1 (f^~ y) (('d1 f) x y).
      move=> xax_n; apply: DeriveDef.
        by apply: derf1 => //; exact/axnI/subset_itv_oo_cc.
      by rewrite /partial1of2 derive1E.
    have cf : {within `[a, (x_ n)], continuous (f^~ y)}.
      apply: continuous_subspaceW axnI _.
      by apply: derivable_within_continuous => /= r Ir; exact: derf1.
    have [C caxn ->] := @MVT _ (f^~ y) (('d1 f) ^~ y) _ _ axn x_fd1f cf.
    rewrite normrM mulfK ?normr_eq0 ?subr_eq0// G_ub//.
    by move/subset_itv_oo_cc : caxn => /axnI.
  - have xnaI : `[(x_ n), a] `<=` I.
      apply: subset_itvSoo; rewrite bnd_simp.
      + by have := Ix_ n; rewrite /I/= in_itv/= => /andP[].
      + by have := Ia; rewrite /I/= in_itv/= => /andP[].
    have x_fd1f x : x \in `](x_ n), a[ -> is_derive x 1 (f^~ y) (('d1 f) x y).
      move=> xax_n; apply: DeriveDef.
        by apply: derf1 => //; exact/xnaI/subset_itv_oo_cc.
      by rewrite partial1of2E.
    have cf : {within `[(x_ n), a], continuous (f^~ y)}.
      apply: continuous_subspaceW xnaI _.
      by apply: derivable_within_continuous => /= r Ir; exact: derf1.
    have [C caxn] := @MVT _ (f^~ y) (('d1 f) ^~ y) _ _ axn x_fd1f cf.
    rewrite distrC => ->.
    rewrite normrM distrC mulfK ?normr_eq0 ?subr_eq0// G_ub//.
    by move/subset_itv_oo_cc : caxn => /xnaI.
  - by rewrite !subrr normr0 mul0r.
have g_cvg_d1f : forall y, B y -> (g_ n y)%:E @[n --> \oo] --> (('d1 f) a y)%:E.
  move=> y By; apply/fine_cvgP; split; first exact: nearW.
  rewrite /comp/=.
  have /cvg_ex[/= l fayl] := derf1 Ia By.
  have d1fyal : ('d1 f) a y = l.
    apply/cvg_lim => //.
    by move: fayl; under eq_fun do rewrite scaler1.
  have xa0 : (forall n, x_ n - a != 0) /\ x_ n - a @[n --> \oo] --> 0.
    by split=> [x|]; [rewrite subr_eq0|exact/subr_cvg0].
  move: fayl => /cvgr_dnbhsP/(_ _ xa0).
  under [in X in X -> _]eq_fun do rewrite scaler1 subrK.
  move=> xa_l.
  suff : (f (x_ x) y - f a y) / (x_ x - a) @[x --> \oo] --> ('d1 f) a y by [].
  rewrite d1fyal.
  by under eq_fun do rewrite mulrC.
have mdf : measurable_fun B (fun y => (('d1 f) a y)%:E).
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
    (fun x => \int[mu]_(z in B) (g_ x z - ('d1 f) a z)))%R; last first.
  by apply/funext => n; rewrite RintegralB.
apply: norm_cvg0.
have {}g_d1f_0 : (\int[mu]_(y in B) `|g_ n y - ('d1 f) a y|) @[n --> \oo] --> 0.
  exact/fine_cvg.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) _ _ _ _ _ g_d1f_0) => //.
- apply/nearW => n.
  rewrite /= normr_ge0/= le_normr_Rintegral//.
  rewrite /comp; under eq_fun do rewrite EFinB.
  by apply: integrableB => //; exact: intg_.
- exact: cvg_cst.
Unshelve. all: end_near. Qed.

Lemma differentiation_under_integral :
  F^`() a = \int[mu]_(y in B) ('d1 f ^~ y) a.
Proof.
rewrite /derive1.
by have /cvg_lim-> //:= cvg_differentiation_under_integral.
Qed.

Lemma derivable_under_integral : derivable F a 1.
Proof.
apply/cvg_ex => /=; exists (\int[mu]_(y in B) ('d1 f ^~ y) a).
under eq_fun do rewrite scaler1.
exact: cvg_differentiation_under_integral.
Qed.

End differentiation_under_integral.
