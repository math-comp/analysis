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
            
have noturn : forall g, ctxt g ->
   {in `]a, b[ &, forall x z y, x < y < z -> g x < g y -> g y < g z}.
  move=> g [ijg ctg] x z xin zin y /andP[xlty yltz] glt; rewrite ltNge le_eqVlt.
  have allin u : x <= u <= z -> u \in `]a, b[.
    move=> /andP[] xleu ulez; rewrite in_itv /=.
    by rewrite (lt_le_trans _ xleu) ?(le_lt_trans ulez) ?(itvP zin)
         ?(itvP xin).
  have gctuw : {in `]a, b[ &, forall u w, {in `[u,w], continuous g}}.
    move=> u w uin win.
    move=> v vin; apply ctg.
    rewrite in_itv /= (lt_le_trans (_ : a < u) _) ?(itvP vin) ?(itvP uin) //.
    rewrite (le_lt_trans _ (_ : w < b)) ?(itvP win) //.
      by rewrite ?(itvP vin).
  have yin : y \in `]a, b[ by rewrite allin ?(ltW xlty) ?(ltW yltz).
  apply/negP=> /orP[/eqP gygz | gzltgy].
    by move: yltz; rewrite lt_neqAle (ijg _ _ yin zin (esym gygz)) eqxx.
  have [ gxltgz | ] := boolP(g x < g z).
    have gzmid : Num.min (g x) (g y) <= g z <= Num.max (g x) (g y).
      by rewrite /Num.min  /Num.max glt !ltW ?gzltgy.
    have [u uin Pu] := IVT (ltW xlty) (gctuw _ _ xin yin) gzmid.
    have ultz : u < z by rewrite (le_lt_trans _ yltz) ?(itvP uin).
    have uab : u \in `]a, b[ by rewrite allin  ?(ltW ultz) ?(itvP uin).
    by move: ultz; rewrite lt_neqAle (ijg _ _ uab zin Pu) eqxx.
  rewrite -leNgt=> gzlegx.
  have gzmid : Num.min (g y) (g z) <= g x <= Num.max (g y) (g z).
    by rewrite minC maxC /Num.min  /Num.max gzltgy ?gzlegx ltW.
  have [u uin Pu] := IVT (ltW yltz) (gctuw _ _ yin zin) gzmid.
  have xltu : x < u by rewrite (lt_le_trans xlty _) ?(itvP uin).
  have uab : u \in `]a, b[ by rewrite allin  ?(ltW xltu) ?(itvP uin).
  by move: xltu; rewrite lt_neqAle (ijg _ _ uab xin Pu) eqxx.
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
have noturn2 g : ctxt g ->
   {in `]a, b[ &, forall x z y, x < y < z -> g y < g x -> g z < g y}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g y)) ltr_oppr.
  have := noturn (-%R \o g) (ctxtg' _ ctg) x z xin zin y xyz.
  apply=> /=.
  by rewrite ltr_oppr opprK.
have noturn3 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g z < g y -> g y < g x}.
  move=> ctg x z xin zin y xyz flt.
  have zyx : (a + b - z < a + b - y < a + b -x).
     by rewrite !ltr_add2l !ltr_opp2 andbC.
  by have := noturn _ (ctxtg2 _ ctg) _ _
     (keepin _ zin) (keepin _ xin) _ zyx; rewrite /= !subKr; apply.
have noturn4 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g y < g z -> g x < g y}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g y)) ltr_oppr.
  have := noturn3 _ (ctxtg' _ ctg) x z xin zin y xyz.
  rewrite /=; apply.
  by rewrite ltr_oppr opprK.
have noturn5 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g x < g z -> g x < g y}.
  move=> ctg x z xin zin y xyz flt.
  have [xlty yltz] := andP(xyz).
  have yin : y \in `]a, b[.
    by rewrite in_itv /= (lt_trans _ xlty) ?(lt_trans yltz) ?(itvP zin)
        ?(itvP xin).
  rewrite ltNge le_eqVlt negb_or eq_sym; apply/andP; split.
    by apply/eqP=>/(proj1 ctg x y xin yin) xy; move: xlty; rewrite xy ltxx.
  apply/negP=> gyltgx.
  have := flt; apply/negP; rewrite -leNgt le_eqVlt.
  by rewrite (lt_trans _ gyltgx) ?orbT // (noturn2 _ ctg x z xin zin y xyz).
have noturn6 g : ctxt g ->
  {in `]a, b[ &, forall x z y, x < y < z -> g z < g x -> g y < g x}.
  move=> ctg x z xin zin y xyz flt.
  rewrite -(opprK (g x)) ltr_oppr.
  have := noturn5 _  (ctxtg' _ ctg) x z xin zin y xyz.
  rewrite /=; apply.
  by rewrite ltr_oppr opprK.

(*
have noturn3 : forall g : R -> R,
   {in `]a, b[, continuous g} ->
   {in `]a, b[ &, forall x z y, x < y < z -> g y < g x -> g z < g y}.
   forall x z y, x < y < z -> (f x < f y) = (f y < f z)}.
  move=> x z xin zin y /andP [xlty yltz].
  have [fxltfy | ] := boolP(f x < f y).
   by rewrite (noturn1 x z xin zin y) ?xlty ?xltz.
  have allin u : x <= u <= z -> u \in `]a, b[.
    move=> /andP[] xleu ulez; rewrite in_itv /=.
    by rewrite (lt_le_trans _ xleu) ?(le_lt_trans ulez) ?(itvP zin) ?(itvP xin).
  have yin : y \in `]a, b[ by apply: allin; rewrite !ltW.
  rewrite -leNgt le_eqVlt eq_sym => /orP[/eqP/(ijf _ _ xin yin) xisy | ].
    by move: xlty; rewrite lt_neqAle xisy eqxx.
  move/(noturn2 _ _ xin zin); rewrite xlty yltz=> /(_ isT) fzltfy.
  by apply/esym/negbTE; rewrite -leNgt le_eqVlt fzltfy orbT.
*)
have injlt : forall g : R -> R, {in `]a, b[ &, injective g} ->
      {in `]a, b[ &, forall u v, u < v -> g u != g v}.
  move=> g ijg u v uin vin ultv; apply/eqP=> /(ijg u v uin vin) uv.
  by move: ultv; rewrite uv ltxx.
have noturn4 : forall g : R -> R,
  {in `]a, b[ &, injective g} ->
   {in `]a, b[, continuous g} ->{in `]a, b[ &, forall x z y, x < y < z ->
                   g y < g z -> g x < g y}.
  move=> g ijg ctg x z xin zin y xyz glt.
  have [xlty yltz] := andP(xyz).
  have yin : y \in `]a, b[.
    by rewrite in_itv /= (lt_trans _ xlty) ?(lt_trans yltz) ?(itvP zin)
        ?(itvP xin).
  rewrite ltNge le_eqVlt negb_or eq_sym injlt //; apply/negP => gyltgx.
  move: glt; rewrite ltNge le_eqVlt negb_or eq_sym injlt //= => /negP[].
  by apply: (noturn2 g ijg ctg x).
have noturn5 : {in `]a, b[ &, forall x z y, x < y < z ->
                   f z < f y -> f y < f x}.
  move=> x z xin zin y xyz fzltfy.
  have [xlty yltz] := andP(xyz).
  have yin : y \in `]a, b[.
    by rewrite in_itv /= (lt_trans _ xlty) ?(lt_trans yltz) ?(itvP zin)
        ?(itvP xin).
  rewrite ltNge le_eqVlt negb_or injlt //; apply/negP=> fxltfy.
  move: fzltfy; rewrite ltNge le_eqVlt negb_or injlt //= => /negP[].
  by apply: (noturn1 x).
have noturn6 : {in `]a, b[ &, forall x  z y, x < y < z -> f x < f z ->
     f x < f y < f z}.
  move=> x z xin zin y xyz fxltfz; have [xlty yltz] := andP(xyz).
  have yin : y \in `]a, b[.
    by rewrite in_itv /= (lt_trans _ xlty) ?(lt_trans yltz) ?(itvP zin)
        ?(itvP xin).
  suff fxltfy : f x < f y by rewrite fxltfy /=; apply: (noturn1 x).
  rewrite ltNge le_eqVlt negb_or eq_sym injlt //=; apply/negP => fyltfx.
  have fzltfx : f z < f x.
    rewrite (lt_trans _ fyltfx) //; apply: (noturn2 x)=> //.
    by move: fxltfz; rewrite ltNge le_eqVlt fzltfx orbT.
have noturn6 : {in `]a, b[ &, forall x y, x < y -> f x < f y ->
                  {in `]a, b[ &, forall  z t, z < t -> f z < f t}}.
  move=> x y xin yin xlty fxlty z t zin tin zltt.
  have [ yltz | ] := boolP (y < z).
    have fyltfz : (f y < f z) by  apply: (noturn1 x)=> //; rewrite xlty.
    by apply: (noturn1 x)=> //; rewrite ?(lt_trans xlty) ?(lt_trans fxlty).
  rewrite -leNgt le_eqVlt=> /orP[/eqP zisy | zlty ].
    by rewrite zisy; apply: (noturn1 x) => //; rewrite xlty -zisy.
  have [ tltx | ] := boolP(t < x).
    rewrite ltNge le_eqVlt eq_sym negb_or injlt //; apply/negP=> ftltfz.
    have fxltfz : f x < f z.
      rewrite (lt_trans _ ftltfz) //; apply:(noturn2 z)=> //.
      by rewrite zltt.
    move: fxlty; rewrite ltNge le_eqVlt negb_or eq_sym injlt // => /negP[].
    by apply: (noturn2 z)=> //; rewrite (lt_trans zltt tltx).
  rewrite -leNgt le_eqVlt=> /orP[/eqP xist | xltt ].
    rewrite -xist ltNge le_eqVlt negb_or eq_sym injlt //; last first.
      by rewrite xist.
    apply/negP=> fxltfz.
    move: fxlty; rewrite ltNge le_eqVlt negb_or eq_sym injlt //= => /negP [].
    by apply: (noturn2 z)=> //; rewrite xist zltt -xist.
  have [xltz | ] := boolP (x < z).
    
  have fxltfz : f x < f z.
    apply: lt_trans ftltfz.
    apply: (noturn2 z)=> //.
  have [ tltx | ] := boolP (t < x).
    have ftltfx : f t < f x. apply: (noturn1 z)=> //; rewrite ?zltt //.

(* have := midf_lt altb; set m := _ / 2 => [][] altm mltb.
have := midf_lt mltb; set m' := _ / 2 => [] [] mltm' m'ltb. *)
apply: contrapT; rewrite not_orP /prop_in2 -!existsNE=> [][[x1 Px1][x2 Px2]].
move:Px1 Px2; rewrite -!existsNE=> [] [x3 Px3][x4 Px4].
move: Px3 Px4; rewrite !not_implyE=> [][x1in [x3in decr]][x2in [x4in incr]].
have x1nx3 : x1 != x3.
  by apply/eqP=> x1x3; move: decr; rewrite x1x3 !lexx.
have x2nx4 : x2 != x4.
  by apply/eqP=> x2x4; move: incr; rewrite x2x4 !lexx.
have [ | ] := boolP (x1 <= x3).
  rewrite le_eqVlt (negbTE x1nx3) /= => x1ltx3.
  have [ | ] := boolP (x4 <= x1).
    rewrite le_eqVlt eq_sym=> /orP[/eqP x1x4| ].
      have [ | ] := boolP(x4 <= x2).
        rewrite le_eqVlt eq_sym (negbTE x2nx4) /= => x4ltx2.
        have [ | ] := boolP(x2 <= x3).
          rewrite le_eqVlt=> /orP[/eqP x2x3 | x2ltx3].
            move: incr decr; rewrite x2x3 -x1x4.
            rewrite le_eqVlt; have [ | ] := boolP (f x3 == f x1).
              by move/eqP/(ijf _ _ x3in x1in)=> x3x1; move: x1nx3; rewrite x3x1 eqxx.
            by rewrite eq_sym /= ltNge; case: (f x1 <= f x3); case: (x1 <= x3).
          move: x4ltx2 incr; rewrite -x1x4 (le_eqVlt x1) => x1ltx2.
          rewrite x1ltx2 orbT /= => /Bool.not_true_is_false/negbT.
          rewrite -ltNge=> fx1ltfx2.
          case: decr; rewrite !le_eqVlt x1ltx3 orbT; apply/orP; right.
          apply/(lt_trans fx1ltfx2).
          have/(noturn' _ _ x1in x3in) <- : x1 < x2 < x3 by rewrite x1ltx2 x2ltx3.
          by [].
        rewrite -ltNge => x3ltx2.
        have/(noturn' _ _ x1in x2in) allincr : x1 < x3 < x2 by rewrite x1ltx3.
        move: decr; rewrite !le_eqVlt x1ltx3 orbT=> /Bool.not_true_is_false/negbT.
        rewrite negb_or=> /andP[] _; rewrite allincr -leNgt.
        rewrite le_eqVlt=> /orP[/eqP/(ijf _ _ x2in x3in) x2isx3 | fx2ltfx3].
          by move: x3ltx2; rewrite lt_neqAle x2isx3 eqxx.
        move: allincr; rewrite [A in _ = A -> False]ltNge le_eqVlt fx2ltfx3 orbT.
        case/negbT/negP; apply: lt_trans fx2ltfx3.
        move: incr; rewrite !le_eqVlt x4ltx2 orbT=> /Bool.not_true_is_false/negbT.
        rewrite negb_or -x1x4 -leNgt le_eqVlt=> /andP[] _.
        move=> /orP[/eqP/(ijf _ _ x1in x2in) x1x2 | //].
        by move: x4ltx2; rewrite -x1x4 lt_neqAle x1x2 eqxx.
      rewrite -ltNge -x1x4=> x2ltx1.
      move: decr; rewrite (le_eqVlt x1) x1ltx3 orbT=> /Bool.not_true_is_false/negbT.
      rewrite -ltNge=> fx3ltfx1.
      have/(noturn' _ _ x2in x3in) : x2 < x1 < x3 by rewrite x2ltx1 x1ltx3.
      move=> alldecr.
      case: incr; rewrite -x1x4 le_eqVlt alldecr leNgt x2ltx1.
      apply/Bool.not_true_is_false/negP; rewrite negb_or -leNgt le_eqVlt fx3ltfx1.
      rewrite orbT andbT; apply/eqP=> /(ijf _ _ x2in x1in) x2x1.
      by move: x2ltx1; rewrite x2x1 ltxx.
    move=> x4ltx1.
    have fx1ltfx4 : f x1 < f x4.
      rewrite ltNge le_eqVlt negb_or; apply/andP; split; apply/negP.
        move=> /eqP/(ijf _ _ x4in x1in)=> x4x1; move: x4ltx1.
        by rewrite x4x1 ltxx.
      move=> fx4ltfx1.
      have /(noturn1 _ _ x4in x3in _) : x4 < x1 < x3 by rewrite x4ltx1 x1ltx3.
      rewrite fx4ltfx1=> /(_ isT) fx1ltfx3; move: decr; rewrite !le_eqVlt.
      by rewrite x1ltx3 fx1ltfx3 !orbT.
wlog : x1 x4
have [ decr | ] := boolP(f m' < f m); last first.
  rewrite -leNgt le_eqVlt=> /orP [/eqP/ijf | incr].
    rewrite !in_itv /= altm mltb m'ltb (lt_trans altm mltm')=> /(_ isT isT).
    by move=> abs; move: mltm'; rewrite lt_neqAle abs eqxx.
  left.

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
