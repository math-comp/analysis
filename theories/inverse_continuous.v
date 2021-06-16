From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical_sets posnum topology
  normedtype landau sequences boolp reals ereal derive.

Import GRing.Theory Num.Theory Num.ExtraDef.
Import Order.POrderTheory Order.TotalTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section real_inverse_functions.

Variable R : realType.

Definition strict_increasing (f : R -> R) :=
  forall x y, x < y -> f x < f y.

Definition monotone (f : R -> R) :=
  {mono f : y z / y <= z} \/ {mono f : y z /~ y <= z}.

Let Cf (f : R -> R) a b := {in `[a, b], continuous f}.
Let If (f : R -> R) a b := {in `[a, b] &, injective f}.
Let Mf (f : R -> R) a b := {in `[a, b] &, {mono f : x y / x <= y}}.

Lemma near_injective_monotone (f : R -> R) (a b : R) :
  If f a b -> Cf f a b ->
  {in `[a, b] &, {mono f : x y / x <= y}} \/
  {in `[a, b] &, {mono f : x y /~ x <= y}}.
Proof.
move: f.
suff F (f : R -> R) : f a <= f b -> If f a b -> Cf f a b -> Mf f a b.
  move=> f fI fC.
  have [faLfb|fbLfa] : f a <= f b \/ f b <= f a.
  - by case: ltrgtP; try (by left); right.
  - by left; apply: F.
  right => x y xI yI.
  suff : (- f) y <= (- f) x = (y <= x) by rewrite ler_oppl opprK.
  apply: F xI => // [|x1 x2 x1I y1I U| x1 x1I].
  - by rewrite ler_oppl opprK.
  - by apply: fI => //; rewrite -[LHS]opprK [- f _]U opprK.
  by apply/continuousN/fC.
move: a b f.
suff F (f : R -> R) (a b c : R) :
  f a <= f b -> If f a b -> Cf f a b -> a <= c <= b -> f a <= f c <= f b.
  move=> a b f faLfb fI fC x y /itvP xI /itvP yI.
  have aLb : a <= b by apply: le_trans (_ : x <= b); rewrite xI.
  have : x <= y -> f x <= f y.
    move=> xLy.
    have /andP[faLfx fxLfb] : f a <= f x <= f b.
      by apply: F; rewrite ?xI.
    suff /andP[-> //] : f x <= f y <= f b.
    apply: F => [|x1 x2 /itvP x1I /itvP x2I |x1 /itvP x1I|] //.
    - by apply: fI; rewrite in_itv /= (le_trans (_ : a <= x)) !(xI, x1I,
x2I).
    - by apply: fC; rewrite in_itv /= (le_trans (_ : a <= x)) !(xI, x1I).
    by rewrite xLy yI.
  have : y <= x -> f y <= f x.
    move=> yLx.
    have /andP[faLfx fxLfb] : f a <= f y <= f b by apply: F; rewrite ?yI.
    suff /andP[-> //] : f y <= f x <= f b.
    apply: F => [|x1 x2 /itvP x1I /itvP x2I |x1 /itvP x1I|] //.
    - by apply: fI; rewrite in_itv /= (le_trans (_ : a <= y)) !(yI, x1I,
x2I).
    - by apply: fC; rewrite in_itv /= (le_trans (_ : a <= y)) !(yI, x1I).
    by rewrite yLx xI.
  have : f x == f y -> x == y.
    by move=> /eqP/fI-> //; rewrite in_itv /= !(xI, yI).
  by case: (ltrgtP x y); case: (ltrgtP (f x) (f y)) => // _ _ H1 H2 H3;
     (case: (H1 isT) || case: (H2 isT) || case: (H3 isT)).
move=> faLfb fI fC /andP[aLc cLb].
have aLb : a <= b  by apply: le_trans cLb.
have cIab : c \in `[a,b] by rewrite in_itv /= aLc.
have acIab d : d \in `[a,c] -> d \in `[a,b].
  by move=> /itvP dI; rewrite in_itv /= (le_trans _ cLb) // dI.
have cbIab d : d \in `[c,b] -> d \in `[a,b].
  by move=> /itvP dI; rewrite in_itv /= (le_trans aLc) // dI.
case: (ltrgtP (f a) (f c)) => /= [faLfc|fcLfa|faEfc]; last first.
- by rewrite -(fI _  _ _ _ faEfc) // in_itv /= lexx.
- case: (ltrgtP (f b) (f c))=> /= [fbLfc|fcLfb|fbEfc]; last first.
  + by move: fcLfa; rewrite -fbEfc ltNge faLfb.
  + have [d dI]: exists2 d, d \in `[c, b] & f d = f a.
      apply: IVT => //; first by move=> d dIab; apply/fC/cbIab.
      by case: ltrgtP fcLfb => // _ _; rewrite ltW.
    move=> fdEfa; move: fcLfa.
    have : a <= c <= d by rewrite aLc  (itvP dI).
    rewrite (fI _  _ _ _ fdEfa) ?in_itv /= ?lexx ?(itvP dI) //.
      by case: (ltrgtP a) => // ->; rewrite ltxx.
    by rewrite (le_trans aLc) //  (itvP dI).
  by have := lt_trans fbLfc fcLfa; rewrite ltNge faLfb.
case: (ltrgtP (f b) (f c))=> //= fbLfc.
have [d dI]: exists2 d, d \in `[a, c] & f d = f b.
  apply: IVT => //; first by move=> d dIab; apply/fC/acIab.
  by case: ltrgtP faLfc; rewrite // faLfb // ltW.
move=> fdEfb; move: fbLfc.
have : d <= c <= b by rewrite cLb  (itvP dI).
rewrite (fI _  _ _ _ fdEfb) ?in_itv /= ?lexx ?(itvP dI) ?aLb //.
  by case: (ltrgtP b) => //= ->; rewrite ltxx.
by rewrite (le_trans _ cLb) //  (itvP dI).
Qed.

(* Maybe this belongs in normedtype. *)
Lemma near_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof.
move=> y ayb; rewrite (near_shift 0 y).
have minlt : 0 < Num.min (y - a) (b - y).
  have : 0 < y - a by rewrite subr_gt0 (itvP ayb).
  have : 0 < b - y by rewrite subr_gt0 (itvP ayb).
  by case: (ltrP (y - a) (b - y)).
near=> z; rewrite /= subr0.
rewrite in_itv /= -ltr_subl_addl -ltr_subr_addl ltr_normlW /=; last first.
  rewrite normrN.
  by near: z; apply: nbhs0_lt; rewrite (lt_le_trans minlt) // le_minl lexx.
rewrite -ltr_subr_addr ltr_normlW //.
near: z; apply: nbhs0_lt; rewrite (lt_le_trans minlt) //.
by rewrite le_minl lexx orbT.
Unshelve. all: end_near. Qed.


Lemma near_0_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near 0 : R, (z + y : R) \in `]a, b[}.
Proof.
move=> y ayb.
rewrite (near_shift y 0); near=> z; rewrite /= sub0r subrK; near: z.
by rewrite near_simpl; apply: near_in_interval.
Unshelve. all: end_near. Qed.

Lemma inverse_increasing_continuous (a b k : R) (f g : R -> R) :
  0 < k ->
  {in (g @` [set x | x \in `]a, b[ ])%classic &,
       forall x y, x < y -> k * (y - x) < f y - f x} ->
  {in `]a, b[, cancel g f} ->
  {in `]a, b[, continuous g}.
Proof.
move=> kgt0 incrf gK y ayb.
apply/cvg_distP=> _ /posnumP[e].
have main1 : \forall x \near y, g y < g x -> `|g y - g x| < e%:num.
  rewrite (near_shift 0 y); near=> z; rewrite /=subr0.
  move=> yltz; rewrite ltr0_norm ?opprB; last by rewrite subr_lt0.
  move: yltz.
  have zin : z + y \in `]a, b[.
    by near:z; rewrite near_simpl; apply: near_0_in_interval.
  have gzin : g (z + y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists (z + y).
  have gyin : g (y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists y.
  move/incrf=> /(_ gyin gzin); rewrite !gK //.
  rewrite addrK -ltr_pdivl_mull //; move/lt_trans; apply.
  rewrite mulrC lter_pdivr_mulr //; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; apply: mulr_gt0.
have main2 : \forall x \near y, g x < g y -> `|g y - g x| < e%:num.
  rewrite (near_shift 0 y); near=> z; rewrite /= subr0.
  move=> zlty; rewrite gtr0_norm; last by rewrite subr_gt0.
  move: zlty.
  have zin : z + y \in `]a, b[.
    by near: z; rewrite near_simpl; apply: near_0_in_interval.
  have gzin : g (z + y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists (z + y).
  have gyin : g (y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists y.
  move/incrf=> /(_ gzin gyin); rewrite !gK //.
  rewrite opprD addrA addrAC addrN sub0r.
  rewrite -ltr_pdivl_mull //; move/lt_trans; apply.
  rewrite mulrC lter_pdivr_mulr //; apply: ltr_normlW; rewrite normrN.
  by near: z; apply: nbhs0_lt; apply: mulr_gt0.
rewrite !near_simpl /=; near=> x.
have [ | ] := boolP (g x < g y).
  near:x; rewrite near_simpl; apply: main2.
rewrite -leNgt le_eqVlt=> /orP[/eqP -> | gyltgx].
  by rewrite subrr normr0.
move: gyltgx; near:x; rewrite near_simpl; apply: main1.
Unshelve. all: end_near. Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x.
have [xlt0 | ] := boolP(x < 0).
  apply: (near_cst_continuous 0).
  rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
have neg_part (y : R) (e : {posnum R}) : y < 0 -> Num.sqrt y < e%:num.
  by move=> ylt0; rewrite ltr0_sqrtr.
rewrite -leNgt le_eqVlt eq_sym=> /orP[/eqP -> | ].
  apply/cvg_distP=> _ /posnumP[e]; rewrite !near_simpl /=.
  near=> y; rewrite sqrtr0 sub0r normrN.
  rewrite ger0_norm ?sqrtr_ge0 //.
  have ylte2 : y < e%:num ^+ 2.
    rewrite ltr_normlW //; near: y; apply: nbhs0_lt.
    by rewrite exprn_gt0.
  have twogt0 : (0 < 2)%N by [].
  rewrite -(ltr_pexpn2r twogt0) ?inE ?nnegrE ?ltrW ?sqrtr_ge0 //.
  have [ylt0 | ] := boolP(y < 0).
    by rewrite ltr0_sqrtr // expr0n /= exprn_gt0.
  by rewrite -leNgt => yge0; rewrite sqr_sqrtr.
suff main : forall a b, 0 < a -> {in `]a, b[, continuous (@Num.sqrt R)}.
  move=> xgt0.
  have halfxgt0 : 0 < x / 2 by apply: divr_gt0.
  have xgthalf : x / 2 < x by case: (midf_lt xgt0); rewrite add0r.
  have xltxp1 : x < x + 1 by rewrite ltr_addl.
  set a := x / 2; set b := x + 1.
  by apply: (main a b); rewrite // in_itv //= xgthalf xltxp1.
move=> a b agt0.
set k := Num.sqrt a.
set f := fun u : R => u ^+ 2.
set g := @Num.sqrt R.
have sagt0 : 0 < Num.sqrt a by rewrite sqrtr_gt0.
have incr : {in [set g u | u in [set x1 | x1 \in `]a, b[]]%classic &,
         forall u y : R, u < y -> k * (y - u) < f y - f u}.
  move=> u v; rewrite !inE /= => [][u' u'in u'q][v' v'in v'q] ultv.
  have u'gt0 : 0 < u'.
    by rewrite (lt_trans agt0) // (itvP u'in).
  have ugt0 : 0 < u.
    by rewrite (lt_trans sagt0) // -u'q /g ltr_sqrt // (itvP u'in).
  have v'gt0 : 0 < v'.
    by rewrite (lt_trans agt0) // (itvP v'in).
  have vgt0 : 0 < v.
    by rewrite (lt_trans sagt0) // -v'q /g ltr_sqrt // (itvP v'in).
  rewrite /f subr_sqr (mulrC (_ - _)) ltr_pmul2r; last by rewrite subr_gt0.
  rewrite ltr_spsaddr // -?u'q -?u'v /g ?sqrtr_gt0.
  by rewrite /k -v'q /g ltr_sqrt //; case/andP: v'in.
have gK : {in `]a, b[, cancel g f}.
  by move=> u uin; rewrite /f /g sqr_sqrtr ?ltW ?(lt_trans agt0) ?(itvP uin).
apply: (inverse_increasing_continuous sagt0 incr gK).
Unshelve. all: end_near. Qed.

Section logarithm.

Variable exp : R -> R.
Hypothesis exp0 : exp 0 = 1.
Hypothesis exp_gt0 : forall x, 0 < exp x.
Hypothesis exp_total : forall x, 0 < x -> exists y, exp y = x.
Hypothesis expD : forall x y, exp (x + y) = exp x * exp y.
Hypothesis exp_ge1Dx : forall x, 0 <= x -> 1 + x <= exp x.
Hypothesis ltr_exp : {mono exp : x y / x < y}.
Hypothesis is_derive_exp : forall x, is_derive x 1 exp (exp x).
Variable ln : R -> R.
Hypothesis expK : cancel exp ln.

Lemma lnK : {in `]0, +oo[, cancel ln exp}.
Proof.
move=> x xgt0.
have /exp_total [vl Pvl] : 0 < x by rewrite (itvP xgt0).
by rewrite -Pvl expK.
Qed.

Lemma ln1 : ln 1 = 0.
Proof. by rewrite -exp0 expK. Qed.

Lemma ln_continuous : {in > 0, continuous ln}.
Proof.
suff main : forall a b, 0 < a -> {in `]a, b[, continuous ln}.
  move=> x xgt0.
  have halfxgt0 : 0 < x / 2 by apply: divr_gt0.
  have xltxp1 : x < x + 1 by rewrite ltr_addl.
  have halfltx : x / 2 < x by case: (midf_lt xgt0); rewrite add0r.
  by apply: (main (x / 2) (x + 1) halfxgt0); rewrite in_itv /= halfltx xltxp1.
move=> a b agt0.
apply: (inverse_increasing_continuous agt0 (f := exp)).
  move=> x y; rewrite !inE /= => [][lx lxin Plx] [ly lyin Ply] xlty.
  rewrite [X in _ < exp X - _](_ : y = y - x + x); last by rewrite subrK.
  rewrite expD -[X in _ < _ - X]mul1r -mulrBl mulrC.
  have /ltW/exp_ge1Dx : 0 < y - x by rewrite subr_gt0.
  have altexpx : a < exp x.
    have lxgt0 : 0 < lx by rewrite (lt_trans agt0) // (itvP lxin).
    by rewrite -Plx lnK ?in_itv /= ?andbT ?(itvP lxin).
  rewrite le_eqVlt (addrC 1)=> /orP[/eqP <- | expgt].
    by rewrite addrK ltr_pmul2l ?subr_gt0.
  by apply ltr_pmul; rewrite // ?ltW ?subr_gt0 // ltr_subr_addr.
by move=> x xin; apply:lnK; rewrite in_itv /= andbT (lt_trans agt0) ?(itvP xin).
Qed.

Lemma is_derive_ln x : 0 < x -> is_derive x 1 ln (x ^-1).
Proof.
move=> xgt0.
have : derivable ln 1 1.
  apply/cvg_ex; exists 1.
(* I would like to discuss this piece of code.
  have step : forall h, h != 0 -> `|h| < 1 ->
     h ^-1 = (exp (ln (1 + h)) - exp 0) ^-1.
    move=> h hn0 abshlt1; rewrite exp0 lnK; last first.
      rewrite in_itv /= andbT -ltr_subl_addl add0r ltr_oppl ltr_normlW //.
      by rewrite normrN.
    by rewrite addrAC addrN add0r.
  under eq_fun do rewrite ln1 subr0 /=.
*)
  apply/cvg_distP=> e.
End logarithm.

End real_inverse_functions.
