(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
Require Import boolp ereal reals mathcomp_extra functions.
Require Import classical_sets signed topology prodnormedzmodule.
Require Import cardinality normedtype derive.

(******************************************************************************)
(* This file provides properties of standard real-valued functions over real  *)
(* numbers (e.g., the continuity of the inverse of a continuous function).    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

Section real_inverse_functions.
Variable R : realType.
Implicit Types (a b : R) (f g : R -> R).

(* TODO: this is a workaround to weaken {in I, continuous f} to use IVT.
   Updating this whole file to use {within [set` I], continuous f} is the
   better, but more labor intensive approach *)
Lemma continuous_subspace_itv (I : interval R) (f : R -> R) :
  {in I, continuous f} -> {within [set` I], continuous f}.
Proof.
move=> ctsf; apply: continuous_in_subspaceT => x Ix; apply: ctsf.
by move: Ix; rewrite inE.
Qed.

Lemma itv_continuous_inj_le f (I : interval R) :
  (exists x y, [/\ x \in I, y \in I, x < y & f x <= f y]) ->
  {in I, continuous f} -> {in I &, injective f} ->
  {in I &, {mono f : x y / x <= y}}.
Proof.
gen have fxy : f / {in I &, injective f} ->
    {in I &, forall x y, x < y -> f x != f y}.
  move=> fI x y xI yI xLy; apply/negP => /eqP /fI => /(_ xI yI) xy.
  by move: xLy; rewrite xy ltxx.
gen have main : f / forall c, {in I, continuous f} -> {in I &, injective f} ->
    {in I &, forall a b, f a < f b -> a < c -> c < b -> f a < f c /\ f c < f b}.
  move=> c fC fI a b aI bI faLfb aLc cLb.
  have intP := interval_is_interval aI bI.
  have cI : c \in I by rewrite intP// (ltW aLc) ltW.
  have ctsACf : {within `[a, c], continuous f}.
    apply: continuous_in_subspaceT => x; rewrite inE => /itvP axc; apply: fC.
    by rewrite intP// axc/= (le_trans _ (ltW cLb))// axc.
  have ctsCBf : {within `[c,b], continuous f}.
    apply: continuous_in_subspaceT => x; rewrite inE => /itvP axc; apply: fC.
    by rewrite intP// axc andbT (le_trans (ltW aLc)) ?axc.
  have [aLb alb'] : a < b /\ a <= b by rewrite ltW (lt_trans aLc).
  have [faLfc|fcLfa|/eqP faEfc] /= := ltrgtP (f a) (f c).
  - split; rewrite // lt_neqAle fxy // leNgt; apply/negP => fbLfc.
    move: (fbLfc); suff /eqP -> : c == b by rewrite ltxx.
    rewrite eq_le (ltW cLb) /=.
    have [d /andP[ad dc] fdEfb] : exists2 d, a <= d <= c & f d = f b.
      have aLc' : a <= c by rewrite ltW.
      apply: IVT => //; last first.
        by case: ltrgtP faLfc; rewrite // (ltW faLfb) // ltW.
    rewrite -(fI _ _ _ _ fdEfb) //.
    move: ad dc; rewrite le_eqVlt =>/predU1P[<-//| /ltW L] dc.
    by rewrite intP// L (le_trans _ (ltW cLb)).
  - have [fbLfc | fcLfb | fbEfc] /= := ltrgtP (f b) (f c).
    + by have := lt_trans fbLfc fcLfa; rewrite ltNge (ltW faLfb).
    + have [d /andP[cLd dLb] /eqP] : exists2 d, c <= d <= b & f d = f a.
        have cLb' : c <= b by rewrite ltW.
        apply: IVT => //; last by case: ltrgtP fcLfb; rewrite // !ltW.
      have /(fxy f fI) : a < d by rewrite (lt_le_trans aLc).
      suff dI' : d \in I by rewrite eq_sym=> /(_ aI dI') => /negbTE ->.
      move: dLb; rewrite le_eqVlt => /predU1P[->//|/ltW db].
      by rewrite intP// db  (le_trans (ltW aLc)).
    + by move: fcLfa; rewrite -fbEfc ltNge (ltW faLfb).
  by move/(fxy _ fI) : aLc=> /(_ aI cI); rewrite faEfc.
move=> [u [v [uI vI ulv +]]] fC fI; rewrite le_eqVlt => /predU1P[fufv|fuLfv].
  by move/fI: fufv => /(_ uI vI) uv; move: ulv; rewrite uv ltxx.
have aux a c b : a \in I -> b \in I -> a < c -> c < b ->
   (f a < f c -> f a < f b /\ f c < f b) /\
   (f c < f b -> f a < f b /\ f a < f c).
  move=> aI bI aLc cLb; have aLb := lt_trans aLc cLb.
  have cI : c \in I by rewrite (interval_is_interval aI bI)// (ltW aLc)/= ltW.
  have fanfb : f a != f b by apply: (fxy f fI).
  have decr : f b  < f a -> f b < f c /\ f c < f a.
    have ofC : {in I, continuous (-f)} by move=>> ?; apply/continuousN/fC.
    have ofI : {in I &, injective (-f)} by move=>> ? ? /oppr_inj/fI ->.
    rewrite -[X in X < _ -> _](opprK (f b)) ltr_oppl => ofaLofb.
    have := main _ c ofC ofI a b aI bI ofaLofb aLc cLb.
    by (do 2 rewrite ltr_oppl opprK); rewrite and_comm.
  split=> [faLfc|fcLfb].
    suff L : f a < f b by have [] := main f c fC fI a b aI bI L aLc cLb.
    by case: ltgtP decr fanfb => // fbfa []//; case: ltgtP faLfc.
  suff L : f a < f b by have [] := main f c fC fI a b aI bI L aLc cLb.
  by case: ltgtP decr fanfb => // fbfa []//; case: ltgtP fcLfb.
have{main fC} whole a c b := main f c fC fI a b.
have low a c b : f a < f c -> a \in I -> b \in I ->
       a < c -> c < b -> f a < f b /\ f c < f b.
  by move=> L aI bI ac cb; case: (aux a c b aI bI ac cb)=> [/(_ L)].
have high a c b : f c < f b -> a \in I -> b \in I ->
     a < c -> c < b -> f a < f b /\ f a < f c.
  by move=> L aI bI ac cb; case: (aux a c b aI bI ac cb)=> [_ /(_ L)].
apply: le_mono_in => x y xI yI xLy.
have [uLx | xLu | xu] := ltrgtP u x.
- suff fuLfx : f u < f x by have [] := low u x y fuLfx uI yI uLx xLy.
  have [xLv | vLx | -> //] := ltrgtP x v; first by case: (whole u x v).
  by case: (low u v x).
- have fxLfu : f x < f u by have [] := high x u v fuLfv xI vI xLu ulv.
  have [yLu | uLy | -> //] := ltrgtP y u; first by case: (whole x y u).
  by case: (low x u y).
move: xLy; rewrite -xu => uLy.
have [yLv | vLy | -> //] := ltrgtP y v; first by case: (whole u y v).
by case: (low u v y).
Qed.

Lemma itv_continuous_inj_ge f (I : interval R) :
  (exists x y, [/\ x \in I, y \in I, x < y & f y <= f x]) ->
  {in I, continuous f} -> {in I &, injective f} ->
  {in I &, {mono f : x y /~ x <= y}}.
Proof.
move=> [a [b [aI bI ab fbfa]]] fC fI x y xI yI.
suff : (- f) y <= (- f) x = (y <= x) by rewrite ler_oppl opprK.
apply: itv_continuous_inj_le xI => // [|x1 x1I | x1 x2 x1I x2I].
- by exists a, b; split => //; rewrite ler_oppl opprK.
- by apply/continuousN/fC.
by move/oppr_inj; apply/fI.
Qed.

Lemma itv_continuous_inj_mono f (I : interval R) :
    {in I, continuous f} -> {in I &, injective f} -> monotonous I f.
Proof.
move=> fC fI.
case: (pselect (exists a b, [/\ a \in I , b \in I & a < b])); last first.
  move=> N2I; left => x y xI yI; suff -> : x = y by rewrite ?lexx.
  by apply: contra_notP N2I => /eqP; case: ltgtP; [exists x, y|exists y, x|].
move=> [a [b [aI bI lt_ab]]].
have /orP[faLfb|fbLfa] := le_total (f a) (f b).
  by left; apply: itv_continuous_inj_le => //; exists a, b; rewrite ?faLfb.
by right; apply: itv_continuous_inj_ge => //; exists a, b; rewrite ?fbLfa.
Qed.

Lemma segment_continuous_inj_le f a b :
    f a <= f b -> {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y / x <= y}}.
Proof.
move=> fafb fct finj; have [//|] := itv_continuous_inj_mono fct finj.
have [aLb|bLa|<-] := ltrgtP a b; first 1 last.
- by move=> _ x ?; rewrite itv_ge// -ltNge.
- by move=> _ x y /itvxxP-> /itvxxP->; rewrite !lexx.
move=> /(_ a b); rewrite !bound_itvE fafb.
by move=> /(_ (ltW aLb) (ltW aLb)); rewrite lt_geF.
Qed.

Lemma segment_continuous_inj_ge f a b :
    f a >= f b -> {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y /~ x <= y}}.
Proof.
move=> fafb fct finj; have [|//] := itv_continuous_inj_mono fct finj.
have [aLb|bLa|<-] := ltrgtP a b; first 1 last.
- by move=> _ x ?; rewrite itv_ge// -ltNge.
- by move=> _ x y /itvxxP-> /itvxxP->; rewrite !lexx.
move=> /(_ b a); rewrite !bound_itvE fafb.
by move=> /(_ (ltW aLb) (ltW aLb)); rewrite lt_geF.
Qed.

(* The condition "f a <= f b" is unnecessary because the last                *)
(* interval condition is vacuously true otherwise.                           *)
Lemma segment_can_le a b f g : a <= b ->
    {in `[a, b], continuous f} ->
    {in `[a, b], cancel f g} ->
  {in `[f a, f b] &, {mono g : x y / x <= y}}.
Proof.
move=> aLb ctf fK; have [fbLfa | faLfb] := ltrP (f b) (f a).
  by move=> x y; rewrite itv_ge// -ltNge.
have [aab bab] : a \in `[a, b] /\ b \in `[a, b] by rewrite !bound_itvE.
case: ltgtP faLfb => // [faLfb _|-> _ _ _ /itvxxP-> /itvxxP->]; rewrite ?lexx//.
have lt_ab : a < b by case: (ltgtP a b) aLb faLfb => // ->; rewrite ltxx.
have w : exists x y, [/\ x \in `[a, b], y \in `[a, b], x < y & f x <= f y].
  by exists a, b; rewrite !bound_itvE (ltW faLfb).
have fle := itv_continuous_inj_le w ctf (can_in_inj fK).
move=> x y xin yin; have := IVT aLb (continuous_subspace_itv ctf).
case: (ltrgtP (f a) (f b)) faLfb => // _ _ ivt.
by have [[u uin <-] [v vin <-]] := (ivt _ xin, ivt _ yin); rewrite !fK// !fle.
Qed.

(* The condition "f b <= f a" is unnecessary---see seg...increasing above    *)
Lemma segment_can_ge a b f g : a <= b ->
    {in `[a, b], continuous f} ->
    {in `[a, b], cancel f g} ->
  {in `[f b, f a] &, {mono g : x y /~ x <= y}}.
Proof.
move=> aLb fC fK x y xfbfa yfbfa; rewrite -ler_opp2.
apply: (@segment_can_le (- b) (- a) (f \o -%R) (- g));
    rewrite /= ?ler_opp2 ?opprK//.
  move=> z zab; apply: continuous_comp; first exact: continuousN.
  by apply: fC; rewrite oppr_itvcc.
by move=> z zab; rewrite -[- g]/(@GRing.opp _ \o g)/= fK ?opprK// oppr_itvcc.
Qed.

Lemma segment_can_mono a b f g : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  monotonous (f @`[a, b]) g.
Proof.
move=> le_ab fct fK; rewrite /monotonous/=; case: ltrgtP => fab; [left|right..];
  do ?by [apply: segment_can_le|apply: segment_can_ge].
by move=> x y /itvxxP<- /itvxxP<-; rewrite !lexx.
Qed.

Lemma segment_continuous_surjective a b f : a <= b ->
  {in `[a, b], continuous f} -> set_surj `[a, b] (f @`[a, b]) f.
Proof. by move=> ? /continuous_subspace_itv fct y/= /IVT[]// x; exists x. Qed.

Lemma segment_continuous_le_surjective a b f : a <= b -> f a <= f b ->
  {in `[a, b], continuous f} -> set_surj `[a, b] `[f a, f b] f.
Proof.
move=> le_ab f_ab /(segment_continuous_surjective le_ab).
by rewrite (min_idPl _)// (max_idPr _).
Qed.

Lemma segment_continuous_ge_surjective a b f : a <= b -> f b <= f a ->
  {in `[a, b], continuous f} -> set_surj `[a, b] `[f b, f a] f.
Proof.
move=> le_ab f_ab /(segment_continuous_surjective le_ab).
by rewrite (min_idPr _)// (max_idPl _).
Qed.

Lemma continuous_inj_image_segment a b f : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  f @` `[a, b] = f @`[a, b]%classic.
Proof.
move=> leab fct finj; apply: mono_surj_image_segment => //.
  exact: itv_continuous_inj_mono.
exact: segment_continuous_surjective.
Qed.

Lemma continuous_inj_image_segmentP a b f : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in f @`[a, b]).
Proof.
move=> /continuous_inj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) faby.
by apply/(equivP idP); symmetry.
Qed.

Lemma segment_continuous_can_sym a b f g : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in f @`[a, b], cancel g f}.
Proof.
move=> aLb ctf fK; have g_mono := segment_can_mono aLb ctf fK.
have f_mono := itv_continuous_inj_mono ctf (can_in_inj fK).
have f_surj := segment_continuous_surjective aLb ctf.
have fIP := mono_surj_image_segmentP aLb f_mono f_surj.
suff: {in f @`[a, b], {on `[a, b], cancel g & f}}.
  by move=> gK _ /fIP[x xab <-]; rewrite fK.
have: {in f @`[a, b] &, {on `[a, b]  &, injective g}}.
  by move=> _ _ /fIP [x xab <-] /fIP[y yab <-]; rewrite !fK// => _ _ ->.
by apply/ssrbool.inj_can_sym_in_on => x xab; rewrite ?fK ?mono_mem_image_segment.
Qed.

Lemma segment_continuous_le_can_sym a b f g : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in `[f a, f b], cancel g f}.
Proof.
move=> aLb fct fK x xfafb; apply: (segment_continuous_can_sym aLb fct fK).
have : f a <= f b by rewrite (itvP xfafb).
by case: ltrgtP xfafb => // ->.
Qed.

Lemma segment_continuous_ge_can_sym a b f g : a <= b ->
    {in `[a, b], continuous f} -> {in `[a, b], cancel f g} ->
  {in `[f b, f a], cancel g f}.
Proof.
move=> aLb fct fK x xfafb; apply: (segment_continuous_can_sym aLb fct fK).
have : f a >= f b by rewrite (itvP xfafb).
by case: ltrgtP xfafb => // ->.
Qed.

Lemma segment_inc_surj_continuous a b f :
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  {in `]a, b[, continuous f}.
Proof.
move=> fle f_surj; have [f_inj flt] := (inc_inj_in fle, leW_mono_in fle).
have [aLb|bLa] := ltP a b; last by move=> z; rewrite itv_ge//= -leNgt.
have le_ab : a <= b by rewrite ltW.
have [aab bab] : a \in `[a, b] /\ b \in `[a, b] by rewrite !bound_itvE ltW.
have fab : f @` `[a, b] = `[f a, f b]%classic by exact:inc_surj_image_segment.
pose g := pinv `[a, b] f.
have fK : {in `[a, b], cancel f g}.
  by rewrite -[mem _]mem_setE; apply: pinvKV; rewrite !mem_setE.
have gK : {in `[f a, f b], cancel g f} by move=> z zab; rewrite pinvK// fab inE.
have gle : {in `[f a, f b] &, {mono g : x y / x <= y}}.
  apply: can_mono_in (fle); first by move=> *; rewrite gK.
  move=> z zfab; have {zfab} : `[f a, f b]%classic z by [].
  by rewrite -fab => -[x xab <-]; rewrite fK.
have glt := leW_mono_in gle.
move=> x xab; have xabcc : x \in `[a, b] by apply: subset_itv_oo_cc.
have fxab : f x \in `](f a), (f b)[ by rewrite in_itv/= !flt.
have fxabcc : f x \in `[f a, f b] by apply: subset_itv_oo_cc.
apply/cvg_distP => _ /posnumP[e]; rewrite !near_simpl; near=> y.
rewrite (@le_lt_trans _ _ (e%:num / 2%:R))//; last first.
  by rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n.
rewrite ler_distlC; near: y.
pose u := minr (f x + e%:num / 2) (f b).
pose l := maxr (f x - e%:num / 2) (f a).
have ufab : u \in `[f a, f b].
  rewrite !in_itv/= le_minl ?le_minr lexx ?fle// le_ab orbT ?andbT.
  by rewrite ler_paddr// fle ?in_itv/= ?(itvP xab)// lexx.
have lfab : l \in `[f a, f b].
  rewrite !in_itv/= le_maxl ?le_maxr lexx ?fle// le_ab orbT ?andbT/=.
  by rewrite ler_subl_addr ler_paddr// fle ?(itvP xab)// lexx.
near=> y; suff: l <= f y <= u by rewrite le_maxl le_minr -!andbA => /and4P[-> _ ->].
have yab : y \in `[a, b] by apply: subset_itv_oo_cc; near: y; apply: near_in_itv.
have fyab : f y \in `[f a, f b] by rewrite in_itv/= !fle// ?ltW.
rewrite -[l <= _]gle -?[_ <= u]gle// ?fK//.
apply: subset_itv_oo_cc; near: y; apply: near_in_itv; rewrite in_itv/= -[x]fK//.
by rewrite !glt//= lt_minr lt_maxl !(itvP fxab) ?andbT ltr_subl_addr ltr_spaddr.
Unshelve. all: by end_near. Qed.

Lemma segment_dec_surj_continuous a b f :
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  {in `]a, b[, continuous f}.
Proof.
move=> fge f_surj; suff: {in `]a, b[, continuous (- f)}.
  move=> contNf x xab; rewrite -[f]opprK.
  exact/continuous_comp/opp_continuous/contNf.
apply: segment_inc_surj_continuous.
  by move=> x y xab yab; rewrite ler_opp2 fge.
by move=> y /=; rewrite -oppr_itvcc => /f_surj[x ? /(canLR opprK)<-]; exists x.
Qed.

Lemma segment_mono_surj_continuous a b f :
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  {in `]a, b[, continuous f}.
Proof.
move=> -[fle|fge] f_surj x xab; have leab : a <= b by rewrite (itvP xab).
  have fafb : f a <= f b by rewrite fle // ?bound_itvE.
  by apply: segment_inc_surj_continuous x xab => //; case: ltrP f_surj fafb.
have fafb : f b <= f a by rewrite fge // ?bound_itvE.
by apply: segment_dec_surj_continuous x xab => //; case: ltrP f_surj fafb.
Qed.


Lemma segment_can_le_continuous a b f g : a <= b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `](f a), (f b)[, continuous g}.
Proof.
move=> aLb ctf fK x xab; have faLfb : f a <= f b by rewrite (itvP xab).
apply: segment_inc_surj_continuous x xab; first exact: segment_can_le.
rewrite !fK ?bound_itvE//=; apply: (@can_surj _ _ f); first by rewrite mem_setE.
exact/image_subP/mem_inc_segment/segment_continuous_inj_le/(can_in_inj fK).
Qed.

Lemma segment_can_ge_continuous a b f g : a <= b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `](f b), (f a)[, continuous g}.
Proof.
move=> aLb ctf fK x xab; have fbLfa : f b <= f a by rewrite (itvP xab).
apply: segment_dec_surj_continuous x xab; first exact: segment_can_ge.
rewrite !fK ?bound_itvE//=; apply: (@can_surj _ _ f); first by rewrite mem_setE.
exact/image_subP/mem_dec_segment/segment_continuous_inj_ge/(can_in_inj fK).
Qed.

Lemma segment_can_continuous a b f g : a <= b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in f @`]a, b[, continuous g}.
Proof.
move=> aLb crf fK x; case: lerP => // _;
  by [apply: segment_can_ge_continuous|apply: segment_can_le_continuous].
Qed.

Lemma near_can_continuousAcan_sym f g (x : R) :
    {near x, cancel f g} -> {near x, continuous f} ->
  {near (f x), continuous g} /\ {near (f x), cancel g f}.
Proof.
move=> fK fct; near (at_right (0 : R)) => e.
have e_gt0 : 0 < e by near: e; exists 1 => /=.
have xBeLxDe : x - e <= x + e by rewrite ler_add2l gt0_cp.
have fcte : {in `[x - e, x + e], continuous f}.
  by near: e; apply/at_right_in_segment.
have fKe : {in `[x - e, x + e], cancel f g}
  by near: e; apply/at_right_in_segment.
have nearfx : \forall y \near f x, y \in f @`](x - e), (x + e)[.
  apply: near_in_itv; apply: mono_mem_image_itvoo; last first.
    by rewrite in_itv/= -ltr_distlC subrr normr0.
  apply: itv_continuous_inj_mono; first by near: e; apply/at_right_in_segment.
  by apply: (@can_in_inj _ _ _ _ g); near: e; apply/at_right_in_segment.
split; near=> y.
  by apply: (@segment_can_continuous (x - e) (x + e) f) => //; near: y.
rewrite (@segment_continuous_can_sym (x - e) (x + e))//.
by apply: subset_itv_oo_cc; near: y.
Unshelve. all: by end_near. Qed.

Lemma near_can_continuous f g (x : R) :
  {near x, cancel f g} -> {near x, continuous f} -> {near (f x), continuous g}.
Proof. by move=> fK fct; have [] := near_can_continuousAcan_sym fK fct. Qed.

Lemma near_continuous_can_sym f g (x : R) :
  {near x, continuous f} -> {near x, cancel f g} -> {near (f x), cancel g f}.
Proof. by move=> fct fK; have [] := near_can_continuousAcan_sym fK fct. Qed.

End real_inverse_functions.

Section real_inverse_function_instances.

Variable R : realType.

Lemma exprn_continuous n : continuous (@GRing.exp R ^~ n).
Proof.
move=> x; elim: n=> [|n /(continuousM cvg_id) ih]; first exact: cst_continuous.
by rewrite exprS; under eq_fun do rewrite exprS; exact: ih.
Qed.

Lemma sqr_continuous : continuous (@exprz R ^~ 2).
Proof. exact: (@exprn_continuous 2%N). Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x; case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0); rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
- suff main b : 0 <= b -> {in `]0 ^+ 2, (b ^+ 2)[, continuous (@Num.sqrt R)}.
    apply: (@main (x + 1)); rewrite ?ler_paddl// ?in_itv/= ?ltW// expr0n xgt0/=.
    by rewrite sqrrD1 ltr_paddr// ltr_paddl ?sqr_ge0// (ltr_pmuln2l _ 1%N 2%N).
  move=> b0; apply: (@segment_can_le_continuous _ _ _ (@GRing.exp _^~ _)) => //.
    by apply: in1W; apply: exprn_continuous.
  by move=> y y0b; rewrite sqrtr_sqr ger0_norm// (itvP y0b).
- apply/cvg_distP => _ /posnumP[e]; rewrite !near_simpl /=; near=> y.
  rewrite sqrtr0 sub0r normrN ger0_norm ?sqrtr_ge0 //.
  have [ylt0|yge0] := ltrP y 0; first by rewrite ltr0_sqrtr//.
  have: `|y| < e%:num ^+ 2 by near: y; apply: nbhs0_lt.
  by rewrite -ltr_sqrt// ger0_norm// sqrtr_sqr ger0_norm.
Unshelve. all: by end_near. Qed.

End real_inverse_function_instances.

Section is_derive_inverse.
Variable R : realType.

(* Attempt to prove the diff of inverse *)

Lemma is_derive1_caratheodory (f : R -> R) (x a : R) :
  is_derive x 1 f a <->
  exists g, [/\ forall z, f z - f x = g z * (z - x),
        {for x, continuous g} & g x = a].
Proof.
split => [Hd|[g [fxE Cg gxE]]].
  exists (fun z => if z == x then a else (f(z) - f(x)) / (z - x)); split.
  - move=> z; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
    by rewrite -subr_eq0 => /divfK->.
  - apply/continuous_withinNshiftx; rewrite eqxx /=.
    pose g1 h := (h^-1 *: ((f \o shift x) h%:A - f x)).
    have F1 : g1 @ 0^' --> a by case: Hd => H1 <-.
    apply: cvg_trans F1; apply: near_eq_cvg; rewrite /g1 !fctE.
    near=> i.
    rewrite ifN; first by rewrite addrK mulrC /= [_%:A]mulr1.
    rewrite -subr_eq0 addrK.
    by near: i; rewrite near_withinE /= near_simpl; near=> x1.
  by rewrite eqxx.
suff Hf : h^-1 *: ((f \o shift x) h%:A - f x) @[h --> 0^'] --> a.
  have F1 : 'D_1 f x = a by apply: cvg_lim.
  rewrite -F1 in Hf.
    by constructor.
  have F1 :  (g \o shift x) y @[y --> 0^'] --> a.
  by rewrite -gxE; apply/continuous_withinNshiftx.
apply: cvg_trans F1; apply: near_eq_cvg.
near=> y.
rewrite /= fxE /= addrK [_%:A]mulr1.
suff yNZ : y != 0 by rewrite [RHS]mulrC mulfK.
by near: y; rewrite near_withinE /= near_simpl; near=> x1.
Unshelve. all: by end_near. Qed.

Lemma is_derive_0_is_cst (f : R -> R) x y :
  (forall x, is_derive x 1 f 0) -> f x = f y.
Proof.
move=> Hd.
wlog xLy : x y / x <= y by move=> H; case: (leP x y) => [/H |/ltW /H].
rewrite -(subKr (f y) (f x)).
have [| _ _] := MVT_segment xLy; last by rewrite mul0r => ->; rewrite subr0.
apply/continuous_subspaceT=> r.
exact/differentiable_continuous/derivable1_diffP.
Qed.

Global Instance is_derive1_comp (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b ->
  is_derive x 1 (f \o g) (a * b).
Proof.
move=> [fgxv <-{a}] [gv <-{b}]; apply: (@DeriveDef _ _ _ _ _ (f \o g)).
  apply/derivable1_diffP/differentiable_comp; first exact/derivable1_diffP.
  by move/derivable1_diffP in fgxv.
by rewrite -derive1E (derive1_comp gv fgxv) 2!derive1E.
Qed.

Lemma is_deriveV (f : R -> R) (x t v : R) :
  f x != 0 -> is_derive x v f t ->
  is_derive x v (fun y => (f y)^-1) (- (f x) ^- 2 *: t).
Proof.
move=> fxNZ Df.
constructor; first by apply: derivableV => //; case: Df.
by rewrite deriveV //; case: Df => _ ->.
Qed.

Lemma is_derive_inverse (f g : R -> R) l x :
  {near x, cancel f g}  ->
  {near x, continuous f}  ->
  is_derive x 1 f l -> l != 0 -> is_derive (f x) 1 g l^-1.
Proof.
move=> fgK fC fD lNZ.
have /is_derive1_caratheodory [h [fE hC hxE]] := fD.
(* There should be something simpler *)
have gfxE : g (f x) = x by have [d Hd]:= nbhs_ex fgK; apply: Hd.
pose g1 y := if y == f x then (h (g y))^-1
             else (g y - g (f x)) / (y - f x).
apply/is_derive1_caratheodory.
exists g1; split; first 2 last.
- by rewrite /g1 eqxx gfxE hxE.
- move=> z; rewrite /g1; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
  by rewrite -subr_eq0 => /divfK.
have F1 : (h (g x))^-1 @[x --> f x] --> g1 (f x).
  rewrite /g1 eqxx; apply: continuousV; first by rewrite /= gfxE hxE.
  apply: continuous_comp; last by rewrite gfxE.
  by apply: nbhs_singleton (near_can_continuous _ _).
apply: cvg_sub0 F1.
apply/cvg_distP => eps eps_gt0 /=; rewrite !near_simpl /=.
near=> y; rewrite sub0r normrN !fctE.
have fgyE : f (g y) = y by near: y; apply: near_continuous_can_sym.
rewrite /g1; case: eqP => [_|/eqP x1Dfx]; first by rewrite subrr normr0.
have -> : y - f x  = h (g y) * (g y - x) by rewrite -fE fgyE.
rewrite gfxE invfM mulrC divfK ?subrr ?normr0 // subr_eq0.
by apply: contra x1Dfx => /eqP<-; apply/eqP.
Unshelve. all: by end_near. Qed.

End is_derive_inverse.

#[global] Hint Extern 0 (is_derive _ _ (fun _ => (_ _)^-1) _) =>
  (eapply is_deriveV; first by []) : typeclass_instances.
