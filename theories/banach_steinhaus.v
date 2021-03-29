From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import boolp reals posnum classical_sets topology.
From mathcomp Require Import normedtype landau forms sequences.

(******************************************************************************)
(*                    Baire and Banach-Steinhaus theorems                     *)
(*                                                                            *)
(* initial author: Theo Vignon                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma le_closed_ball (R : numFieldType) (M : pseudoMetricNormedZmodType R)
  (x : M) (e1 e2 : R) : (e1 <= e2)%O -> closed_ball x e1 `<=` closed_ball x e2.
Proof. by rewrite /closed_ball => le; apply/closure_subset/le_ball. Qed.

(* NB: PR in progress *)
Lemma gtz0_norm (R : numDomainType) (i : int) : 0 < i -> `|i|%:R = i%:~R :> R.
Proof. by move/gtz0_abs => <-. Qed.

Lemma lez_abs (i : int) : i <= `|i|%N.
Proof.
have [i0|i0] := ltrP 0 i; first by rewrite gtz0_abs.
by rewrite lez0_abs // -subr_ge0 addr_ge0 // oppr_ge0.
Qed.
(* END NB: PR in progress *)

Section Baire.
Variable K : realType.

Definition Baire (U : completeNormedModType K) := forall F : (set U)^nat,
  (forall i, open (F i) /\ dense (F i)) -> dense (\bigcap_i (F i)).

Theorem DeBaire (U : completeNormedModType K) : Baire U.
Proof.
move=> F odF D Dy OpenD.
have /(_ D Dy OpenD)[a0 DF0a0] : dense (F 0%N) := proj2 (odF 0%N).
have {OpenD Dy} openIDF0 : open (D `&` F 0%N).
  by apply: openI => //; exact: (proj1 (odF 0%N)).
have /open_nbhs_nbhs/nbhs_closedballP[r0 Ball_a0] : open_nbhs a0 (D `&` F 0%N).
  by [].
pose P (m : nat) (arn : U * {posnum K}) (arm : U * {posnum K}) :=
  closed_ball arm.1 (arm.2%:num) `<=` (closed_ball arn.1 arn.2%:num)^° `&` F m /\
  arm.2%:num < m.+1%:R^-1.
have Ar : forall na : nat * (U * {posnum K}), exists b : U * {posnum K},
    P na.1.+1 na.2 b.
  move=> [n [an rn]].
  have [ openFn denseFn] := odF n.+1.
  have [an1 B0Fn2an1] : exists x, ((closed_ball an (numpos K rn))^° `&` F n.+1) x.
    move: (open_nbhs_closed_ball an rn)=> [? ?]; apply: denseFn => //.
    by exists an.
  have openIB0Fn1 : open ((closed_ball an (numpos K rn))^° `&` F n.+1).
    by apply/openI => //; exact/open_interior.
  have /open_nbhs_nbhs/nbhs_closedballP[rn01 Ball_an1] :
    open_nbhs an1 ((closed_ball an (numpos K rn))^° `&` F n.+1) by [].
  have n31_gt0 : n.+3%:R^-1 > 0 :> K by [].
  have majr : minr (PosNum n31_gt0)%:num rn01%:num > 0 by apply min_pos_gt0.
  exists (an1, PosNum majr); split.
    apply/(subset_trans _ Ball_an1)/le_closed_ball => /=.
    by rewrite le_minl lexx orbT.
  rewrite (@le_lt_trans _ _ n.+3%:R^-1) //= ?le_minl ?lexx//.
  by rewrite ltf_pinv // ?ltr_nat// posrE.
have [f Pf] := choice Ar.
pose fix ar n := if n is p.+1 then (f (p, ar p)) else (a0, r0).
pose a := fun n => (ar n).1.
pose r := fun n => (ar n).2.
have Suite_ball n m : (n <= m)%N ->
    closed_ball (a m) (r m)%:num `<=` closed_ball (a n) (r n)%:num.
  elim m=> [|k iHk]; first by rewrite leqn0 => /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP -> //|/iHk]; apply: subset_trans.
  have [+ _] : P k.+1 (a k, r k) (a k.+1, r k.+1) by apply: (Pf (k, ar k)).
  rewrite subsetI => -[+ _].
  by move/subset_trans; apply => //; exact: interior_subset.
have : cvg (a @ \oo).
  suff : cauchy (a @ \oo) by exact: cauchy_cvg.
  suff : cauchy_ex (a @ \oo) by exact: cauchy_exP.
  move=> e e0; rewrite /fmapE -ball_normE /ball_.
  have [n rne] : exists n, 2 * (r n)%:num < e.
    pose eps := e / 2.
    have [n n1e] : exists n, n.+1%:R^-1 < eps.
      exists `|ceil eps^-1|%N.
      rewrite -ltf_pinv ?(posrE,divr_gt0)// invrK -addn1 natrD.
      rewrite gtz0_norm ?(ceil_gt0,invr_gt0,divr_gt0)//.
      by rewrite (le_lt_trans (ler_ceil _)) // ltr_addl.
    exists n.+1; rewrite -ltr_pdivl_mull //.
    have /lt_trans : (r n.+1)%:num < n.+1%:R^-1.
      have [_ ] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply: (Pf (n, ar n)).
      by move/lt_le_trans => -> //; rewrite lef_pinv// // ?posrE// ler_nat.
    by apply; rewrite mulrC.
  exists (a n), n => // m nsupm.
  apply: (@lt_trans _ _ (2 * (r n)%:num) (`|a n - a m|) e) => //.
  have : (closed_ball (a n) (r n)%:num) (a m).
     have /(_ (a m)) := Suite_ball n m nsupm.
     by apply; exact: closed_ballxx.
  rewrite closed_ballE /closed_ball_ //= => /le_lt_trans; apply.
  by rewrite  -?ltr_pdivr_mulr ?mulfV ?ltr1n.
rewrite cvg_ex //= => -[l Hl]; exists l; split.
- have Hinter : (closed_ball a0 r0%:num) l.
    apply: (@closed_cvg _ _ \oo eventually_filter a) => //.
    + move=> m; have /(_ (a m)) := Suite_ball 0%N m (leq0n m).
      by apply; exact: closed_ballxx.
    + exact: closed_ball_closed.
  suff : closed_ball a0 r0%:num `<=` D by move/(_ _ Hinter).
  by move: Ball_a0; rewrite closed_ballE //= subsetI; apply: proj1.
- move=> i _.
  have : closed_ball (a i) (r i)%:num l.
    rewrite -(@cvg_shiftn i _ a l) /= in Hl.
    apply: (@closed_cvg _ _ \oo eventually_filter (fun n => a (n + i)%N)) => //=.
    + by move=> n; exact/(Suite_ball _ _ (leq_addl n i))/closed_ballxx.
    + exact: closed_ball_closed.
  move: i => [|n].
    by move: Ball_a0; rewrite subsetI => -[_ p] la0; move: (p _ la0).
  have [+ _] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply : (Pf (n , ar n)).
  by rewrite subsetI => -[_ p] lan1; move: (p l lan1).
Qed.

End Baire.

Definition bounded_fun_norm (K : realType) (V : completeNormedModType K)
    (W : normedModType K) (f : V -> W) :=
  forall r, exists M, forall x, `|x| <= r -> `|f x| <= M.

(* TODO: imp to define in normedtype.v *)
Lemma bounded_landau (K : realType) (V : completeNormedModType K)
    (W : normedModType K) (f : {linear V -> W}) :
  bounded_fun_norm f <-> ((f : V -> W) =O_ (0 : V) cst 1).
Proof.
rewrite eqOP; split => [|Bf].
- move=> /(_ 1)[M bm].
  rewrite !nearE /=; exists M; rewrite num_real; split => // x Mx.
  rewrite nearE nbhs_normP /=; exists 1 => // y /=.
  rewrite -ball_normE /ball_ //= sub0r normrN /cst normr1 mulr1 => y1.
  by rewrite (le_trans (bm _ _)) // ltW.
- apply/bounded_funP; rewrite /bounded_near.
  near=> M.
  rewrite (_ : mkset _ = (fun x => (`|f x| <= M * `|cst 1%R x|))); last first.
    by rewrite funeqE => x; rewrite normr1 mulr1.
  by near: M.
Grab Existential Variables. all: end_near. Qed.

Section banach_steinhaus.
Variables (K : realType) (V : completeNormedModType K) (W : normedModType K).

Definition pointwise_bounded (F : set (V -> W)) :=
  forall x, exists M, forall f, F f -> `|f x| <= M.

Definition uniform_bounded (F : set (V -> W)) :=
  forall r, exists M, forall f, F f -> forall x, `|x| <= r -> `|f x| <= M.

Theorem Banach_Steinhauss (F : set (V -> W)):
  (forall f, F f -> bounded_fun_norm f /\ linear f) ->
  pointwise_bounded F -> uniform_bounded F.
Proof.
move=> Propf BoundedF.
set O := fun n => \bigcup_(f in F) (normr \o f)@^-1` [set y | y > n%:R].
have O_open : forall n, open ( O n ).
  move=> n; apply: open_bigU => i Fi.
  apply: (@open_comp _ _ (normr \o i) [set y | y > n%:R]); last first.
    exact: open_gt.
  move=> x Hx; apply: continuous_comp; last exact: norm_continuous.
  have Li : linear i := proj2 (Propf _ Fi).
  apply: (@linear_continuous K V W (Linear Li)) => /=.
  exact/(proj1 (bounded_landau (Linear Li)))/(proj1 (Propf _ Fi)).
set O_inf := \bigcap_i (O i).
have O_infempty : O_inf = set0.
  rewrite -subset0 => x.
  have [M FxM] := BoundedF x; rewrite /O_inf /O /=.
  move=> /(_ `|ceil M|%N Logic.I)[f Ff]; apply/negP; rewrite -leNgt.
  rewrite (le_trans (FxM _ Ff))// (le_trans (ler_ceil _))//.
  by have := lez_abs (ceil M); rewrite -(@ler_int K).
have ContraBaire : exists i, not (dense (O i)).
  have dOinf : ~ dense O_inf.
    rewrite /dense O_infempty ; apply /existsNP; exists setT; elim.
    - by move=> x; rewrite setI0.
    - by exists point.
    - exact: openT.
  have /contra_not/(_ dOinf) : (forall i, open(O i) /\ dense (O i)) -> dense (O_inf).
    exact: (@DeBaire _ V).
  move=> /asboolPn /existsp_asboolPn[n /and_asboolP /nandP Hn].
  by exists n; case: Hn => /asboolPn.
have [n [x0 [r H]] k] :
    exists n x (r : {posnum K}), (ball x r%:num) `<=` (~` (O n)).
  move: ContraBaire =>
  [i /(denseNE) [ O0 [ [ x /open_nbhs_nbhs /nbhs_ballP [r [r0 bxr]]
   /((@subsetI_eq0 _ (ball x r) O0 (O i) (O i)))]]]] /(_ bxr) bxrOi.
  by exists i, x, (PosNum r0); apply/disjoints_subset/bxrOi.
exists ((n + n)%:R * k * 2 / r%:num)=> f Ff y Hx; move: (Propf f Ff) => [ _ linf].
case: (eqVneq y 0) => [-> | Zeroy].
  move: (linear0 (Linear linf)) => /= ->.
  by rewrite normr0 !mulr_ge0 // (le_trans _ Hx).
have majballi : forall f x, F f -> (ball x0 r%:num) x -> `|f x | <= n%:R.
  move=> g x Fg /(H x); rewrite leNgt.
  by rewrite /O /= setC_bigcup /= => /(_ _ Fg)/negP.
have majball : forall f x, F f -> (ball x0 r%:num) x -> `|f (x - x0)| <= n%:R + n%:R.
  move=> g x Fg; move: (Propf g Fg) => [Bg Lg].
  move: (linearB (Linear Lg)) => /= -> Ballx.
  apply/(le_trans (ler_norm_sub _ _))/ler_add; first exact: majballi.
  by apply: majballi => //; exact/ball_center.
have ballprop : ball x0 r%:num (2^-1 * (r%:num / `|y|) *: y  + x0).
  rewrite -ball_normE /ball_ /= opprD addrCA subrr addr0 normrN normmZ.
  rewrite 2!normrM -2!mulrA (@normfV _ `|y|) normr_id mulVf ?mulr1 ?normr_eq0//.
  by rewrite gtr0_norm // gtr0_norm // gtr_pmull // invf_lt1 // ltr1n.
have := majball f (2^-1 * (r%:num / `|y|) *: y + x0) Ff ballprop.
rewrite -addrA addrN linf.
move: (linear0 (Linear linf)) => /= ->.
rewrite addr0 normmZ 2!normrM gtr0_norm // gtr0_norm //.
rewrite normfV normr_id -ler_pdivl_mull //=; last first.
  by rewrite mulr_gt0 // mulr_gt0 // invr_gt0 normr_gt0.
move/le_trans; apply.
rewrite -natrD -!mulrA (mulrC (_%:R)) ler_pmul //.
  by rewrite invr_ge0 // mulr_ge0 // divr_ge0.
by rewrite invfM invrK mulrCA ler_pmul2l // invf_div // ler_pmul2r.
Qed.

End banach_steinhaus.
