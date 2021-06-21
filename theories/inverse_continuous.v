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
have /andP [xmex xxpe] : x - e%:num < x < x + e%:num.
  by rewrite ltr_subl_addr cpr_add; apply/andP.
set c := Num.max a (x - e%:num); set d := Num.min (x + e%:num) b.
have xedif : x - e%:num < x + e%:num by rewrite (lt_trans xmex).
have cLd : c < d.
  rewrite /c /d; case: (ltrgtP a (x - e%:num));
    case: (ltrgtP (x + e%:num) b) => //=.
  + by move=> bxpe axme; rewrite (lt_trans xmex).
  + by move=> xpeb xmea; rewrite (lt_trans aLx).
  + by move=> xpeb xmea; rewrite (lt_trans aLx).
  + by move=> xpeb axme; rewrite axme.
  by move=> xpeb axme; rewrite axme.
have [aLc [xmeLc cLb]] : (a <= c) /\ (x - e%:num <= c) /\ (c <= b).
  rewrite /c; case: (ltrgtP a (x - e%:num))=> // ax;
  by rewrite ?ax ?lexx // !ltW // (lt_trans xmex).
have [dLb [dLxpe aLd]] : (d <= b) /\ (d <= x + e%:num) /\ (a <= d).
  rewrite /d; case: (ltrgtP (x + e%:num) b)=> // xb;
  by rewrite -?xb ?lexx // !ltW // (lt_trans _ xxpe).
have aLd' : a < d by rewrite (le_lt_trans aLc).
have cLb' : c < b by rewrite (lt_le_trans cLd).
have [aab bab] : a \in `[a, b] /\ b \in `[a, b]
  by rewrite !in_itv /= !lexx !ltW.
have gyx : g y = x by rewrite fxy fK // strict_to_large_itv.
have infcfd : {in `](f c), (f d)[, forall u, `|g y - g u| < e%:num}.
  move=> u uin; move: (uin); rewrite in_itv /= => /andP[] fcLu uLfd.
  have uinab : u \in `](f a), (f b)[.
    by rewrite in_itv /= (le_lt_trans _ fcLu) ?(lt_le_trans uLfd) //;
      rewrite incr // in_itv //= ?aLc ?aLd ?dLb.
  have uin' : u \in `[(f c), (f d)] by rewrite strict_to_large_itv.
  have:= ivt _ uinab => [][v vin fvu]; move/andP: (vin)=> [altv vltb].
  have guv : g u = v by rewrite fvu fK // strict_to_large_itv.
  rewrite guv gyx ?in_itv /=.
  have vnc : v != c by apply/eqP=> vc; move: fcLu; rewrite fvu vc ltxx.
  have vnd : v != d by apply/eqP=> vc; move: uLfd; rewrite fvu vc ltxx.
  rewrite distrC lter_distl (lt_le_trans _ dLxpe) ?(le_lt_trans xmeLc) //.
    rewrite lt_neqAle eq_sym vnc /= -incr; last first.
    + by rewrite strict_to_large_itv.
    + by rewrite in_itv /= aLc.
    by rewrite -fvu ltW.
  rewrite lt_neqAle vnd /= -incr; last first.
      by rewrite in_itv /= aLd.
    by rewrite strict_to_large_itv.
  by rewrite -fvu ltW.
have fanfx : f a != f x.
  by apply/eqP=>/ifab fafx; move: (aLx); rewrite fafx ?ltxx.
have fxnfb : f x != f b.
  by apply/eqP=>/ifab fxfb; move: (xLb); rewrite fxfb ?ltxx.
have fxLfb : f x <= f b by rewrite incr // ?ltW.
have faLfx : f a <= f x by rewrite incr // ?ltW.
have fcy : f c < y.
  rewrite /c; case: (ltrgtP a (x - e%:num))=> ax;
  rewrite fxy lt_neqAle -?ax ?fanfx ?faLfx //.
  have xmeab : x - e%:num \in `[a, b].
    by rewrite strict_to_large_itv // in_itv /= andbC (lt_trans xmex _).
  rewrite andbC incr // (ltW xmex); apply/eqP=>/ifab => /(_ xmeab xab) abs.
  by move: xmex; rewrite abs ltxx.
have yfd : y < f d.
  rewrite /d; case: (ltrgtP (x + e%:num) b)=> bx;
  rewrite fxy lt_neqAle ?bx ?fxnfb ?fxLfb //.
  have xpeab : x + e%:num \in `[a, b].
    by rewrite strict_to_large_itv // in_itv /= (lt_trans aLx xxpe).
  rewrite andbC incr // (ltW xxpe); apply/eqP=>/ifab => /(_ xab xpeab) abs.
  by move: xxpe; rewrite -abs ltxx.
have yfcfd : y \in `](f c), (f d)[.
  by rewrite in_itv /= fcy.
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
