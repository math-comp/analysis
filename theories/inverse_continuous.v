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

Lemma near_injective_monotone (f : R -> R) (a b : R) :
  {in `]a, b[ &, injective f} -> 
  {in `]a, b[, continuous f} ->
  {in `]a, b[ &, {mono f : x y / x <= y}} \/
  {in `]a, b[ &, {mono f : x y /~ x <= y}}.
Proof.  
move=> ijf ctf; have [altb | blea ] := boolP(a < b); last first.
  left=> x y; rewrite in_itv /= => /andP[] ax xb; case/negP: blea.
  by apply: lt_trans xb.
set ctxt := fun (g : R -> R) => {in `]a, b[ &, injective g} /\
    {in `]a, b[, continuous g}.
have ctxtg' g : ctxt g -> ctxt (-%R \o g).
  move=> [ijg ctg]; split; first by move=> u v uin vin /= /oppr_inj /ijg=> ->.
  move=> u uin; apply: continuous_comp; first by apply: ctg.
  by apply: opp_continuous.
have keepin : {in `]a, b[, forall x, a + b - x \in `]a, b[}.
  move=> x xin; rewrite in_itv /= !ltr_sub_addl !ltr_add2r (addrC x a).
  by rewrite !ltr_add2l !(itvP xin).
have ctxtg2 g : ctxt g -> ctxt (g \o (fun x => a + b - x)).
  move=> [ijg ctg]; split.
    move=> u v uin vin /= /ijg; rewrite !keepin // => /(_ isT isT)/eqP.
    by rewrite -subr_eq0 (addrC (a + b)) addrKA subr_eq0 eqr_opp=>/eqP.
  move=> u uin; apply: continuous_comp; last first.
    by rewrite forE; apply/ctg/keepin.
  by apply: continuousB;[apply: continuous_cst |].
have allin : {in `]a, b[ &, forall x z u, x <= u <= z -> u \in `]a, b[}.
    move=> x z xin zin u /andP[] xleu ulez; rewrite in_itv /=.
    by rewrite (lt_le_trans _ xleu) ?(le_lt_trans ulez) ?(itvP zin)
         ?(itvP xin).
have keepy : {in `]a, b[ &, forall x z y, x < y < z -> y \in `]a, b[}.
  move=> x z xin zin y /andP[xlty yltz]; apply: (allin x z)=> //.
  by rewrite !le_eqVlt xlty yltz !orbT.
have reverse : {in `]a, b[ &, forall x z y, x < y < z ->
                  a + b - z < a + b - y < a + b - x}.
  by move=> x z xin zin y xyz; rewrite !ltr_add2l !ltr_opp2 andbC.
have noturn : forall g, ctxt g ->
   {in `]a, b[ &, forall x z y, x < y < z -> g x < g y -> g y < g z}.
  move=> g [ijg ctg] x z xin zin y /andP[xlty yltz] glt; rewrite ltNge le_eqVlt.
  have gctuw : {in `]a, b[ &, forall u w, {in `[u,w], continuous g}}.
    move=> u w uin win.
    move=> v vin; apply ctg.
    rewrite in_itv /= (lt_le_trans (_ : a < u) _) ?(itvP vin) ?(itvP uin) //.
    rewrite (le_lt_trans _ (_ : w < b)) ?(itvP win) //.
      by rewrite ?(itvP vin).
  have yin : y \in `]a, b[ by apply: (keepy _ _ xin zin); rewrite xlty.
  apply/negP=> /orP[/eqP gygz | gzltgy].
    by move: yltz; rewrite lt_neqAle (ijg _ _ yin zin (esym gygz)) eqxx.
  have [ gxltgz | ] := boolP(g x < g z).
    have gzmid : Num.min (g x) (g y) <= g z <= Num.max (g x) (g y).
      by rewrite /Num.min  /Num.max glt !ltW ?gzltgy.
    have [u uin Pu] := IVT (ltW xlty) (gctuw _ _ xin yin) gzmid.
    have ultz : u < z by rewrite (le_lt_trans _ yltz) ?(itvP uin).
    have uab : u \in `]a, b[.
      by apply: (allin _ _ xin zin); rewrite (itvP uin) ltW.
    by move: ultz; rewrite lt_neqAle (ijg _ _ uab zin Pu) eqxx.
  rewrite -leNgt=> gzlegx.
  have gzmid : Num.min (g y) (g z) <= g x <= Num.max (g y) (g z).
    by rewrite minC maxC /Num.min  /Num.max gzltgy ?gzlegx ltW.
  have [u uin Pu] := IVT (ltW yltz) (gctuw _ _ yin zin) gzmid.
  have xltu : x < u by rewrite (lt_le_trans xlty _) ?(itvP uin).
  have uab : u \in `]a, b[.
    by apply: (allin x z xin zin); rewrite (itvP uin) le_eqVlt xltu orbT.
  by move: xltu; rewrite lt_neqAle (ijg _ _ uab xin Pu) eqxx.
have noturn2 g : ctxt g ->
   {in `]a, b[ &, forall x z y, x < y < z -> g y < g x -> g z < g y}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g y)) ltr_oppr.
  apply: (noturn _ (ctxtg' _ ctg) x z xin zin y xyz)=> /=.
  by rewrite ltr_oppr opprK.
have noturn3 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g z < g y -> g y < g x}.
  move=> ctg x z xin zin y xyz flt.
  have := noturn _ (ctxtg2 _ ctg) _ _
     (keepin _ zin) (keepin _ xin) _ (reverse _ _ xin zin _ xyz).
  by rewrite /= !subKr; apply.
have noturn4 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g y < g z -> g x < g y}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g y)) ltr_oppr.
  apply: (noturn3 _ (ctxtg' _ ctg) x z xin zin y xyz)=> /=.
  by rewrite ltr_oppr opprK.
have noturn5 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g x < g z -> g x < g y}.
  move=> ctg x z xin zin y xyz flt; have [xlty yltz] := andP(xyz).
  have yin : y \in `]a, b[ by apply: (keepy x z).
  rewrite ltNge le_eqVlt negb_or eq_sym; apply/andP; split.
    by apply/eqP=>/(proj1 ctg x y xin yin) xy; move: xlty; rewrite xy ltxx.
  apply/negP=> gyltgx.
  have := flt; apply/negP; rewrite -leNgt le_eqVlt.
  by rewrite (lt_trans _ gyltgx) ?orbT // (noturn2 _ ctg x z xin zin y xyz).
have noturn6 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g z < g x -> g y < g x}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g x)) ltr_oppr.
  apply: (noturn5 _  (ctxtg' _ ctg) x z xin zin y xyz)=> /=.
  by rewrite ltr_oppr opprK.
have noturn7 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g x < g z -> g y < g z}.
  move=> ctg x z xin zin y xyz flt.
  have := noturn5 _  (ctxtg2 _ (ctxtg' _ ctg)) _ _
                  (keepin _ zin) (keepin _ xin) _ (reverse _ _ xin zin _ xyz).
  by rewrite /= !subKr !ltr_opp2; apply.
have noturn8 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g z < g x -> g z < g y}.
  move=> ctg x z xin zin y xyz flt.
  have := noturn6 _  (ctxtg2 _ (ctxtg' _ ctg)) _ _
                  (keepin _ zin) (keepin _ xin) _ (reverse _ _ xin zin _ xyz).
  by rewrite /= !subKr !ltr_opp2; apply.
apply: contrapT; rewrite not_orP /prop_in2 -!existsNE=> [][[x1 Px1][x2 Px2]].
move:Px1 Px2; rewrite -!existsNE=> [] [x3 Px3][x4 Px4].
move: Px3 Px4; rewrite !not_implyE=> [][x1in [x3in decr]][x2in [x4in incr]].
have x1nx3 : x1 != x3.
  by apply/eqP=> x1x3; move: decr; rewrite x1x3 !lexx.
have x2nx4 : x2 != x4.
  by apply/eqP=> x2x4; move: incr; rewrite x2x4 !lexx.
have fx1nfx3 : f x1 != f x3.
  apply/negP=>/eqP/(ijf _ _ x1in x3in)=> x1x3.
  by move: x1nx3; rewrite x1x3 eqxx.
have fx2nfx4 : f x2 != f x4.
  apply/negP=>/eqP/(ijf _ _ x2in x4in)=> x2x4.
  by move: x2nx4; rewrite x2x4 eqxx.
move: decr; rewrite !le_eqVlt (negbTE x1nx3) (negbTE fx1nfx3) /= => decr.
move: incr; rewrite !le_eqVlt (negbTE fx2nfx4) eq_sym (negbTE x2nx4) /= => incr.
wlog x1ltx3 : x1 x3 x1in x3in decr {x1nx3} fx1nfx3 / x1 < x3.
  move=> special.
  have [ | ] := boolP(x1 <= x3).
    by rewrite le_eqVlt (negbTE x1nx3)=>/special; apply.
  rewrite -ltNge=>/special; apply=> //.
  rewrite !ltNge !le_eqVlt (negbTE x1nx3) (negbTE fx1nfx3) /=.
    by apply/eqP; rewrite eqb_negLR negbK; apply/eqP.
  by rewrite eq_sym.
wlog x2ltx4 : x2 x4 x2in x4in {x2nx4} fx2nfx4 incr / x2 < x4.
  move=> special.
  have [ | ] := boolP(x2 <= x4).
    by rewrite le_eqVlt (negbTE x2nx4)=> /special; apply.
  rewrite -ltNge=>/special; apply=> //.
    by rewrite eq_sym.
  rewrite !ltNge !le_eqVlt (negbTE fx2nfx4) eq_sym (negbTE x2nx4) /=.
  by apply/eqP; rewrite eqb_negLR negbK; apply/eqP.
have fx2ltfx4 : f x2 < f x4.
  move/eqP: incr; rewrite (ltNge x4 x2) le_eqVlt x2ltx4 orbT.
  by case: (f x2 < f x4).
suff : f x1 < f x3 by move=> fx1ltfx3; move: decr; rewrite fx1ltfx3 x1ltx3.
have [ x1ltx2 | ] := boolP(x1 < x2).
  have fx1ltfx2 : f x1 < f x2.
  suff /(noturn4 _ (conj ijf ctf)) : x1 < x2 < x4 by apply.
    by rewrite x1ltx2.
  have [ x3ltx2 | ] := boolP(x3 < x2).
    have /(noturn5 _ (conj ijf ctf)) : x1 < x3 < x2 by rewrite x1ltx3.
      by apply.
  rewrite -leNgt le_eqVlt=> /orP[/eqP <- //| x2ltx3].
  have : f x2 < f x3.
    by apply: (noturn _ (conj ijf ctf) x1)=> //; rewrite x1ltx2.
  by apply lt_trans.
rewrite -leNgt le_eqVlt eq_sym=> /orP[/eqP x1x2 | x2ltx1 ].
  rewrite x1x2; have [x3ltx4 | ] := boolP(x3 < x4).
    apply: (noturn5 _ (conj ijf ctf) _ x4) => //.
      by rewrite -x1x2 x1ltx3.
    rewrite -leNgt le_eqVlt eq_sym=> /orP[/eqP -> // | x4ltx3].
  apply: (lt_trans fx2ltfx4).
  by apply: (noturn _ (conj ijf ctf) x2)=> //; rewrite x2ltx4.
have [x1ltx4 | ] := boolP(x1 < x4).
  have fx2ltfx1 : f x2 < f x1.
    by apply: (noturn5 _ (conj ijf ctf) _ x4)=> //; rewrite x2ltx1.
  by apply: (noturn _ (conj ijf ctf) x2)=> //; rewrite x2ltx1.    
rewrite -leNgt le_eqVlt eq_sym=> /orP[/eqP x1x4 | x4ltx1].
  rewrite x1x4.
  by apply: (noturn _ (conj ijf ctf) x2)=> //; rewrite x2ltx4 -x1x4.
have fx2ltfx1 : f x2 < f x1.
  apply: (lt_trans fx2ltfx4).
  by apply: (noturn _ (conj ijf ctf) x2)=> //; rewrite x2ltx4.
by apply: (noturn _ (conj ijf ctf) x2)=> //; rewrite x2ltx1.
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
