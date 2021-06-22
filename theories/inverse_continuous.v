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

Lemma strict_to_large_itv (a b x : R) :
  x \in `]a, b[ -> x \in `[a, b].
Proof.
by rewrite !in_itv /= => /andP[aLx xLb]; rewrite !le_eqVlt aLx xLb !orbT.
Qed.

(* This belongs in mathcomp *)
Lemma oppr_min (x y : R) : - Num.min x y = Num.max (-x) (- y).
Proof.
by rewrite /Num.max ltr_oppr !opprK; case: (ltrgtP x y).
Qed.

Lemma oppr_max (x y : R) : - Num.max x y = Num.min (-x) (- y).
Proof.
by rewrite /Num.min ltr_oppr !opprK; case: (ltrgtP x y)=> // ->.
Qed.

(* Maybe this belongs in normedtype. *)
Lemma near_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof.
move=> y ayb; rewrite (near_shift 0 y).
have mingt0 : 0 < Num.min (y - a) (b - y).
  have : 0 < y - a by rewrite subr_gt0 (itvP ayb).
  have : 0 < b - y by rewrite subr_gt0 (itvP ayb).
  by case: (ltrP (y - a) (b - y)).
near=> z; rewrite /= subr0.
rewrite in_itv /= -ltr_subl_addl -ltr_subr_addl ltr_normlW /=; last first.
  rewrite normrN.
  by near: z; apply: nbhs0_lt; rewrite (lt_le_trans mingt0) // le_minl lexx.
rewrite -ltr_subr_addr ltr_normlW //.
near: z; apply: nbhs0_lt; rewrite (lt_le_trans mingt0) //.
by rewrite le_minl lexx orbT.
Grab Existential Variables. all: end_near. Qed.

Lemma near_0_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near 0 : R, (z + y : R) \in `]a, b[}.
Proof.
move=> y ayb.
rewrite (near_shift y 0); near=> z; rewrite /= sub0r subrK; near: z.
by rewrite near_simpl; apply: near_in_interval.
Grab Existential Variables. all: end_near. Qed.

Lemma inverse_continuous (a b : R) (f g : R -> R) :
  {in `[(Num.min a b), (Num.max a b)], continuous f} ->
  {in `[(Num.min a b), (Num.max a b)], cancel f g} ->
  {in `](Num.min (f a) (f b)), (Num.max (f a) (f b))[, continuous g}.
Proof.
wlog aLb : a b f g / a < b.
  move=> main.
  case: (ltrgtP a b); last first.
  - move=> <-; rewrite minxx maxxx=> _ _ y; rewrite in_itv //=.
    by case: (ltrgtP (f a) y).
  - move=> blta; move: blta (main _ _ f g blta); case: (ltrP b a)=> // _ _.
    by rewrite minC maxC.
  move=> altb; move: altb (main _ _ f g altb); case: (ltrP a b)=> // _ _.
wlog faLfb : f g / f a < f b.
  case: (ltrgtP (f a) (f b)); last first.
  - by move=> _ _ _ _ y; rewrite in_itv /=; case: (ltrgtP (f a) y).
  - move=> fbLfa /(_ (-%R \o f) (g \o -%R)) main ctf fK.
    have ctf' : {in `[(Num.min a b), (Num.max a b)], continuous (-%R \o f)}.
      move=> x xin.
      by apply: continuous_comp;[apply ctf | apply: opp_continuous].
    have fK' : {in `[(Num.min a b), (Num.max a b)],
                      cancel (-%R \o f)(g \o -%R)}.
      by move=> x; rewrite /= opprK; exact: fK.
    suff ct_gopp : {in `](-f a), (-f b)[, continuous (g \o -%R)}.
      rewrite (_ : g = (g \o -%R) \o -%R); last first.
        by apply: funext => x; rewrite /= opprK.
      move=> x xin; apply: continuous_comp.
        by rewrite forE; apply: opp_continuous.
      rewrite forE; apply: ct_gopp.
      by rewrite oppr_itvoo !opprK.
    move=> x xin; apply: main.
    + by rewrite /= ltr_oppr opprK.
    + case: (ltrgtP a b) (aLb) ctf=> // _ _ ctf.
      move=> y yin; apply: continuous_comp; first by apply: ctf.
      by apply: opp_continuous.
    + case: (ltrgtP a b) (aLb) fK=> _ _ fK y yin // /=; rewrite opprK.
      by apply: fK.
    by rewrite /= -oppr_min -oppr_max; case: (ltrgtP (f b) (f a)) (fbLfa).
  move=> faLfb main; move: {main} (main _ g faLfb).
  by case: (ltrP (f a) (f b)) faLfb.
case: (ltrP a b) (aLb)=> // _ _; case: (ltrP (f a) (f b)) (faLfb)=> // _ _.
move=> ctf fK.
have ivt : {in `](f a), (f b)[, forall y, exists2 x, a < x < b & y = f x}.
  move=> y yin.
  have yin' : y \in `[(f a), (f b)] by rewrite strict_to_large_itv.
  have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb)=> // _ _.
  move=> /(_ _ yin')=> [][] c; rewrite in_itv /= !le_eqVlt=> /andP[].
  move=> /orP[/eqP <- |aLc].
    by move=> _ fay; move: yin; rewrite -fay in_itv /= ltxx.
  move=> /orP[/eqP -> |cLb].
    by move=> fy; move: yin; rewrite -fy in_itv /= ltxx andbF.
  by move=> <-; exists c; rewrite ?aLc ?cLb.
move=> y yin; have [x /andP[aLx xLb] fxy] := ivt _ yin.
have xab : x \in `[a, b] by rewrite strict_to_large_itv // in_itv /= aLx.
have ifab : If f a b.
  by rewrite /If=> u v uin vin fufv; rewrite -(fK u uin) fufv fK.
have [incr | abs] := near_injective_monotone ifab ctf; last first.
  move: (abs a b); rewrite !in_itv /= !lexx ltW // ltW // leNgt aLb.
  by move=> /(_ isT isT).
apply/cvg_distP=> _ /posnumP[e].
wlog /andP [esmall_a esmall_b] : e / (a <= x - e%:num) && (x + e%:num <= b).
  move=> main.
  set e' := Num.min e%:num (Num.min (x - a) (b - x)).  
  have e'gt0 : 0 < e'.
    rewrite /e'; case: (lerP e%:num (Num.min (x - a) (b - x))) => // _.
    by case: (lerP (x - a) (b - x)) => _; rewrite subr_gt0.
  have e'in : (a <= x - e') && (x + e' <= b).
    rewrite ler_subr_addr -ler_subr_addl -[X in _ && X]ler_subr_addl /e'.
    case: (lerP e%:num (Num.min (x - a) (b - x)));
    case: (lerP (x - a) (b - x))=> //.
    + by move=> cmp2 cmp1; rewrite (le_trans _ cmp2) ?andbT.
    + by move=> /ltW cmp2 cmp1; rewrite (le_trans _ cmp2) ?andbT.
    + by move=> cmp2 cmp1; rewrite lexx.
    by move=> /ltW cmp2 cmp1; rewrite lexx ?andbT.
  have e'lee : e' <= e%:num.
    by rewrite /e'; case: (lerP e%:num (Num.min (x - a) (b - x)))=> // /ltW.
  have main' := (main (PosNum e'gt0) e'in).
  near=> y'; apply: (lt_le_trans _ e'lee).
  rewrite -[e']/(num_of_pos (PosNum e'gt0)).
  near: y'; exact main'.
have /andP [xmex xxpe] : x - e%:num < x < x + e%:num.
  by rewrite ltr_subl_addr cpr_add; apply/andP.
have xedif : x - e%:num < x + e%:num by rewrite (lt_trans xmex).
have [aab bab] : a \in `[a, b] /\ b \in `[a, b]
  by rewrite !in_itv /= !lexx !ltW.
have xmeab : x - e%:num \in `[a, b].
  by rewrite in_itv /= esmall_a ltW // (lt_le_trans xedif).
have xpeab : x + e%:num \in `[a, b].
  by rewrite in_itv /= esmall_b ltW // (le_lt_trans _ xedif).
have gyx : g y = x by rewrite fxy fK // strict_to_large_itv.
have infcfd : {in `](f (x - e%:num)), (f (x + e%:num))[,
   forall u, `|g y - g u| < e%:num}.
  move=> u uin; move: (uin); rewrite in_itv /= => /andP[] fxmeLu uLfxpe.
  have uinab : u \in `](f a), (f b)[.
    rewrite in_itv /= (le_lt_trans _ fxmeLu) ?(lt_le_trans uLfxpe) //.
      by rewrite incr // in_itv /= ?esmall_b (le_trans esmall_a) // ltW.
    by rewrite incr // in_itv /= ?esmall_a ?(le_trans _ esmall_b) // ltW.
  have:= ivt _ uinab => [][v vin fvu]; move/andP: (vin)=> [altv vltb].
  have guv : g u = v by rewrite fvu fK // strict_to_large_itv.
  rewrite guv gyx ?in_itv /=.
  have vnxme : v != x - e%:num.
    by apply/eqP=> vxme; move: fxmeLu; rewrite fvu vxme ltxx.
  have vnxpe : v != x + e%:num.
    by apply/eqP=> vxpe; move: uLfxpe; rewrite fvu vxpe ltxx.
  rewrite distrC lter_distl //.
  rewrite lt_neqAle eq_sym vnxme /= -incr //; last first.
    by rewrite strict_to_large_itv.
  rewrite -fvu ltW // lt_neqAle vnxpe /= -incr //; last first.
    by rewrite strict_to_large_itv.
  by rewrite -fvu ltW.
have fanfx : f a != f x.
  by apply/eqP=>/ifab fafx; move: (aLx); rewrite fafx ?ltxx.
have fxnfb : f x != f b.
  by apply/eqP=>/ifab fxfb; move: (xLb); rewrite fxfb ?ltxx.
have fxLfb : f x <= f b by rewrite incr // ?ltW.
have faLfx : f a <= f x by rewrite incr // ?ltW.
have fxmey : f (x - e%:num) < y.
  rewrite fxy lt_neqAle andbC incr // (ltW xmex) /=.
  by apply/eqP=>/ifab => /(_ xmeab xab) abs; move: xmex; rewrite abs ltxx.
have fyxpe : y < f (x + e%:num).
  rewrite fxy lt_neqAle andbC incr // (ltW xxpe) /=.
  by apply/eqP=>/ifab => /(_ xab xpeab) abs; move: xxpe; rewrite -abs ltxx.
have yfcfd : y \in `](f (x - e%:num)), (f (x + e%:num))[.
  by rewrite in_itv /= fxmey.
rewrite !near_simpl; near=> z; apply: infcfd; near: z.
by rewrite !near_simpl; apply: near_in_interval.
Grab Existential Variables. all: end_near. Qed.

Lemma sqr_continuous : continuous (exprz (R := R) ^~ 2).
Proof.
move => x s.
rewrite (_ : exprz (R := R) ^~ 2 = fun x : R => x * x); last first.
  by  apply: funext=> y; rewrite exprSz expr1z.
rewrite exprSz expr1z; move: x s.
change (continuous ((fun x : R * R => x.1 * x.2) \o (fun u => (u, u)))).
  move=> x; apply: continuous_comp; last by apply: mul_continuous.
rewrite forE /=.
(* I hate having to do this step without understanding it. *)
by apply: (cvg_pair (F := nbhs x)(G := nbhs x) (H := nbhs x)).
Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x.
case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0).
  rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
- have csqr bnd : 0 < bnd -> {in `[0, bnd], continuous (exprz (R := R) ^~ 2)}.
  by move=> bndgt0 u _; apply: sqr_continuous.
  have xp1gt0 : 0 < Num.sqrt (x + 1) by rewrite sqrtr_gt0 addr_gt0.
  have m01 : Num.min 0 (Num.sqrt (x + 1)) = 0
    by case: (ltrgtP 0 (Num.sqrt (x + 1))) xp1gt0.
  have M01 : Num.max 0 (Num.sqrt (x + 1)) = (Num.sqrt (x + 1))
    by case: (ltrgtP 0 (Num.sqrt (x + 1))) xp1gt0.
  have xp1gt0' : 0 < x + 1 by rewrite addr_gt0.
  have m01' : Num.min 0 (x + 1) = 0 by case: (ltrgtP 0 (x + 1)) xp1gt0'.
  have M01' : Num.max 0 (x + 1) = (x + 1) by case: (ltrgtP 0 (x + 1)) xp1gt0'.
  move: (csqr _ xp1gt0); rewrite -m01 -[A in `[_, A]]M01=> ctf.
  apply: (inverse_continuous ctf).
  move=> u; rewrite m01 M01=> uin; rewrite sqrtr_sqr; apply/normr_idP.
  by rewrite (itvP uin).
  rewrite /exprz /= ?addn1 sqr_sqrtr ?expr0n /=; last first.
    by rewrite addr_ge0 // ltW.
  by rewrite in_itv m01' M01' /= xgt0 cpr_add ltr01.
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
Grab Existential Variables. all: end_near. Qed.

End real_inverse_functions.
