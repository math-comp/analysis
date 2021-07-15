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

Let Cf (f : R -> R) a b := {in `[a, b], continuous f}.
Let If (f : R -> R) a b := {in `[a, b] &, injective f}.
Let Mf (f : R -> R) a b := {in `[a, b] &, {mono f : x y / x <= y}}.

Lemma itvlc (a b : R) : (a \in `[a, b]) = (a <= b).
Proof.  by rewrite in_itv /= lexx. Qed.

Lemma itvcr (a b : R) : (b \in `[a, b]) = (a <= b).
Proof. by rewrite in_itv /= lexx andbT. Qed.

Lemma itvcc_le (x y : R) (I : interval R) :
  x <= y ->
  (`[x, y] <= I)%O = ((x \in I) && (y \in I)).
Proof.
move=> xLy.
apply/idP/idP.
  case: I => [[b1 lb| b] [b2 ub| b']]; rewrite !subitvE /Order.le /=
   !in_itv /=.
  - move=> /andP[xl yu]; rewrite xl yu; case: b1 xl; case: b2 yu=> /= yu xl.
    + by rewrite (le_lt_trans xLy _) // (le_trans xl).
    + by rewrite (le_trans xLy) // (le_trans xl).
    + by rewrite (le_lt_trans xLy) // (lt_le_trans _ xLy).
    by rewrite (le_trans xLy) // (lt_le_trans _ xLy).
  - case: b'; move=>/andP[xl yu] //; rewrite xl {yu}.
    by case: b1 xl=> /= xl; rewrite ?(le_trans _ xLy) ?(lt_le_trans _ xLy).
  - case: b => //=; case: b2 => /= yu; rewrite yu ?(le_lt_trans xLy) //.
    by rewrite (le_trans xLy).
  - by case: b; case: b'.
case: I => [[b1 lb| b] [b2 ub| b']]; rewrite !subitvE /Order.le /=
   !in_itv /=.
- by case: b1; case:b2=> /= /andP[/andP[-> _] /andP[_ ->]].
- by case: b'; case: b1; rewrite /= ?andbF //; move/andP=> [/andP[] -> ].
- by case: b; case: b2; rewrite /= ?andbF //; move/andP=> [] _ ->.
by case: b; case: b'.
Qed.

Lemma itvcc_sub (x y : R) (I : interval R) : x <= y ->
  {subset `[x, y] <= I} <-> ((x \in I) && (y \in I)).
Proof.
move=> xLy; split.
  by move=> itvI; apply/andP; split; apply itvI; rewrite ?itvlc ?itvcr.
by move=> xIyI; apply/subitvP; rewrite itvcc_le.
Qed.

Lemma interval_connected_le (I : interval R) (a b c : R) :
  a <= c <= b ->  a \in I -> b \in I -> c \in I.
Proof.
move=> /andP[aLc cLb] aI bI.
have /subitvP : (`[a, b] <= I)%O by rewrite itvcc_le ?aI ?(le_trans aLc cLb).
by apply; rewrite in_itv/= ?aLc.
Qed.

Lemma continuous_inj_le_itv (f : R -> R) (I : interval R) :
  (exists x y, x \in I /\ y \in I /\ x < y /\ f x <= f y) ->
  {in I, continuous f} -> {in I &, injective f} ->
  {in I &, {mono f : x y / x <= y}}.
Proof.
move: f.
have stepper_main (f : R -> R) (a c b : R) :
  {in I, continuous f} -> {in I &, injective f} ->
  f a < f b -> a \in I -> b \in I -> a < c -> c < b -> f a < f c  /\ f c < f b.
  move=> fC fI faLfb aI bI aLc cLb.
  have cI : c \in I by rewrite (@interval_connected_le _ a b) // !ltW ?aLc.
  have [aLb alb'] : a < b /\ a <= b by rewrite ltW (lt_trans aLc).
  have fxy x y : x\in I -> y\in I -> x < y -> f x != f y.
    move=> xI yI xLy; apply/negP=> /eqP /fI => /(_ xI yI) xy.
    by move: xLy; rewrite xy ltxx.
  have abI : (`[a, b] <= I)%O by rewrite itvcc_le ?aI.
  have [acI cbI] : (`[a,c] <= I)%O /\ (`[c,b] <= I)%O.
    by split; apply: (le_trans _ abI);
     rewrite subitvE /Order.le /= ?lexx ?aLc ?ltW.
  have [faLfc|fcLfa|/eqP faEfc] /= := ltrgtP (f a) (f c).
  - split;rewrite // lt_neqAle fxy // leNgt; apply/negP => fbLfc.
    move: (fbLfc); suff /eqP -> : c == b by rewrite ltxx.
    rewrite eq_le (ltW cLb) /=.
    have [d dI fdEfb] : exists2 d, d \in `[a, c] & f d = f b.
      have aLc' : a <= c by rewrite ltW.
      apply: IVT => //; last first.
        by case: ltrgtP faLfc; rewrite // (ltW faLfb) // ltW.
      by apply: sub_in1 fC; rewrite itvcc_sub ?aI.
    suff <- : d = b by rewrite (itvP dI).
    by apply: fI fdEfb => //; rewrite (subitvP acI).
  - have [fbLfc | fcLfb | fbEfc] /= := ltrgtP (f b) (f c).
    + by have := lt_trans fbLfc fcLfa; rewrite ltNge (ltW faLfb).
    + have [d dI /eqP] : exists2 d, d \in `[c, b] & f d = f a.
        have cLb' : c <= b by rewrite ltW.
        apply: IVT => //; last by case: ltrgtP fcLfb; rewrite // !ltW.
        by apply: sub_in1 fC; apply/subitvP.
      have /fxy : a < d by rewrite (lt_le_trans aLc) ?(itvP dI).
      by rewrite eq_sym => /(_ aI (interval_connected_le dI _ _)) /negbTE ->.
    + by move: fcLfa; rewrite -fbEfc ltNge (ltW faLfb).
  by move/fxy: aLc=> /(_ aI cI); rewrite faEfc.
move=> f [u [v [uI [vI [ulv fuLfv]]]]] fC fI.
move: fuLfv; rewrite le_eqVlt=> /orP[/eqP fufv | fuLfv].
  by move/fI: fufv => /(_ uI vI) uv; move: ulv; rewrite uv ltxx.
have tid a c b:
  f b < f a -> a \in I -> b \in I -> a < c -> c < b -> f b < f c /\ f c < f a.
  have ofC : {in I, continuous (-f)} by move=> x xin; apply/continuousN/fC.
  have ofI : {in I &, injective (-f)} by move=> x y xin yin /oppr_inj/fI ->.
  move=> fbLfa aI bI aLc cLb.
  have aLb : a < b by apply: (lt_trans aLc).
  have cI : c \in I by rewrite (@interval_connected_le _ a b) // !ltW ?aLc.
  have fanfc : f a != f c.
    by apply/eqP=> /fI => /(_ aI cI)=> abs; move: aLc; rewrite abs ltxx.
  have fcnfb : f c != f b.
    by apply/eqP=> /fI => /(_ cI bI)=> abs; move: cLb; rewrite abs ltxx.
  have := stepper_main (-f) a c b ofC ofI _ aI bI.
  rewrite aLc cLb ltr_oppl opprK and_comm => /(_ fbLfa isT isT).
  by rewrite ltr_oppl opprK ltr_oppl opprK /=.
have tii a c b := stepper_main f a c b fC fI; move=> {stepper_main fC}.
have tii1 a c b : f a < f c -> a \in I -> b \in I ->
       a < c -> c < b -> f a < f b /\ f c < f b.
  move=> faLfc aI bI aLc cLb; suff faLfb : f a < f b.
    have cI : c \in I by rewrite (@interval_connected_le _ a b) ?ltW ?aLc.
    split; first by [].
    by have [] := tii a c b faLfb aI bI aLc cLb.
  rewrite lt_neqAle (_ : f a != f b) /=; last first.
    apply/eqP=> /fI=> /(_ aI bI) Q.
    by move: (lt_trans aLc cLb); rewrite Q ltxx.
  rewrite leNgt; apply/negP=> /tid => /(_ c aI bI aLc cLb)=> [] [_ fcLfa].
  by case: (ltrgtP (f c) (f a)) faLfc fcLfa.
have tii2 a c b : f c < f b -> a \in I -> b \in I ->
     a < c -> c < b -> f a < f b /\ f a < f c.
  move=> fcLfb aI bI aLc cLb; suff faLfb : f a < f b.
  have cI : c \in I by rewrite (@interval_connected_le _ a b) ?ltW ?aLc.
  split; first by [].
  by have [] := tii a c b faLfb aI bI aLc cLb.
  rewrite lt_neqAle (_ : f a != f b) /=; last first.
    apply/eqP=> /fI=> /(_ aI bI) Q.
    by move: (lt_trans aLc cLb); rewrite Q ltxx.
  rewrite leNgt; apply/negP=> /tid => /(_ c aI bI aLc cLb)=> [][fbLfc _].
  by case: (ltrgtP (f c) (f b)) fbLfc fcLfb.
suff main : {in I &, forall x y, x <= y -> f x <= f y}.
  move=> x y xI yI; case : (lerP x y) => [/main xLy | yLx ].
    by apply: xLy.
  rewrite leNgt lt_neqAle main ?ltW // andbT negbK; apply/eqP=> fyfx.
  by have := fI y x yI xI fyfx => yx; move: yLx; rewrite yx ltxx.
move=> x y xI yI; rewrite le_eqVlt=>/orP[/eqP -> | xLy]; first by rewrite lexx.
apply/ltW; case: (ltrgtP u x)=> [uLx | xLu | xu].
- have fuLfx : f u < f x.
  case: (ltrgtP x v) => [xLv | vLx | xv].
  + by have [] := tii u x v fuLfv uI vI uLx xLv.
  + by have [] := tii1 u v x fuLfv uI xI ulv vLx.
  by rewrite xv.
  by have[] := tii1 u x y fuLfx uI yI uLx xLy.
- have fxLfu : f x < f u by have[] := tii2 x u v fuLfv xI vI xLu ulv.
  case: (ltrgtP y u) => [yLu | uLy | yu].
  + by have [] := tii x y u fxLfu xI uI xLy yLu.
  + by have [] := tii1 x u y fxLfu xI yI xLu uLy.
  by rewrite yu.
move: xLy; rewrite -xu => uLy.
case: (ltrgtP y v)=> [yLv | vLy | -> //].
  by have [] := tii u y v fuLfv uI vI uLy yLv.
by have [] := tii1 u v y fuLfv uI yI ulv vLy.
Qed.

Lemma continuous_inj_le_itvcc (f : R -> R) (a b : R) :
  f a <= f b -> {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y / x <= y}}.
Proof.
case: (ltrgtP a b)=> [aLb | bLa | ab].
- move=> faLfb fC fI; apply: continuous_inj_le_itv => //.
  by exists a, b; rewrite itvlc itvcr faLfb !ltW.
- move=> _ _ _ x y; rewrite in_itv /= => /andP[aLx xLb]; move: bLa.
  by rewrite ltNge (le_trans aLx).
move=> _ _ _ x y; rewrite !in_itv /= -ab=> /le_anti -> /le_anti ->.
by rewrite !lexx.
Qed.

Lemma segment_continuous_inj_monotone (f : R -> R) (a b : R) :
  {in `[a, b], continuous f} -> {in `[a, b] &, injective f} ->
  {in `[a, b] &, {mono f : x y / x <= y}} \/
  {in `[a, b] &, {mono f : x y /~ x <= y}}.
Proof.
move=> fC fI.
have [faLfb|fbLfa] : f a <= f b \/ f b <= f a.
- by case: ltrgtP; try (by left); right.
- by left; apply: continuous_inj_le_itvcc.
right => x y xI yI.
suff : (- f) y <= (- f) x = (y <= x) by rewrite ler_oppl opprK.
apply: continuous_inj_le_itvcc xI => // [| x1 x1I |x1 x2 x1I y1I U].
- by rewrite ler_oppl opprK.
- by apply/continuousN/fC.
by apply: fI => //; rewrite -[LHS]opprK [- f _]U opprK.
Qed.

Lemma subset_itv_oo_cc (a b : R) : {subset `]a, b[ <= `[a, b]}.
Proof. by apply: subitvP; rewrite subitvE !bound_lexx. Qed.

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

Lemma left_inverse_increasing (a b : R) (f g : R -> R) :
  a < b -> f a <= f b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `[(f a), (f b)] &, {mono g : x y / x <= y}}.
Proof.
move=> aLb faLfb ctf fK.
have [aab bab] : a \in `[a, b] /\ b \in `[a, b] by rewrite itvlc itvcr ltW.
have fanfb : f a != f b.
  by apply/eqP=> fafb; move: (aLb); rewrite -(fK a) // fafb (fK b) // ltxx.
have ijf : If f a b by move=> x y xin yin fq; rewrite -(fK x) ?fq ?(fK y).
have incr := continuous_inj_le_itvcc faLfb ctf ijf.
have faLfb' : f a < f b.
  by rewrite lt_neqAle fanfb faLfb.
move=> x y xin yin.
have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb')=> // _ _ ivt.
case: (ivt _ xin) => [u uin fux]; case: (ivt _ yin) => [v vin fvy].
by rewrite -fvy -fux; apply/esym; rewrite !fK //; apply: incr.
Qed.

Lemma interval_injective_continuous_bijective (a b : R) (f g : R -> R) :
 a < b ->
 {in `[a, b], continuous f} ->
 {in `[a, b] &, {mono f : x y / x <= y}} ->
 {in `[a, b], cancel f g} ->
 {in `[(f a), (f b)], cancel g f}.
Proof.
move=> aLb ctf monf fK y yin.
have faLfb' : f a <= f b by rewrite monf ?in_itv /= ?lexx ltW.
have := IVT (ltW aLb) ctf; case: (lerP (f a) (f b)) (faLfb')=> // _ _=> ivt.
by case: (ivt _ yin)=> x xin <-; rewrite fK.
Qed.
  
Lemma nearN (a : R) (P : R -> Prop) :
  (\forall x \near a,  P (- x)) <-> (\forall x \near (- a), P x).
Proof.
split; last by apply: opp_continuous.
case=> [e epos Pe]; exists e;[exact epos | ].
move=> z zclose; rewrite -(opprK z); apply: Pe.
by move: zclose; rewrite /ball_ /= -opprD normrN opprK.
Qed.

Lemma monotone_surjective_continuous (a b : R) (f g : R -> R) :
  a < b ->
  {in `[a, b] &, {mono f : x y / x <= y}} ->
  {in `[(f a), (f b)] &, {mono g : x y / x <= y}} ->
  {in `[a, b], cancel f g} ->
  {in `[(f a), (f b)], cancel g f} ->
  {in `](f a), (f b)[, continuous g}.
Proof.
move=> aLb monf mong fK gK y yin; apply/cvg_distP=> _ /posnumP[e].
have faLfb : f a < f b.
  by rewrite (lt_trans (_ : f a <  y) _) // (itvP yin).
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
suff main : (forall (a b : R) (g f : R -> R) y, a < b -> f a < f b ->
         Mf f a b -> Mf g (f a) (f b) ->
         {in `[a, b], cancel f g} ->
         {in `[(f a), (f b)], cancel g f} ->
         y \in `](f a), (f b)[ ->
         \forall u \near y, u < y -> `|g y - g u| < e%:num).
  rewrite !near_simpl.
  have obLoa : -b < -a by rewrite ltr_oppl opprK.
  have ofbLofa : - f b < - f a by rewrite ltr_oppl opprK.
  have monof : Mf (-%R \o f \o -%R) (-b) (-a).
    move=> v w vin win; rewrite /= ler_oppl opprK monf ?oppr_itvcc //.
    by rewrite ler_oppl opprK.
  have monog : Mf (-%R \o g \o -%R) (- f b) (- f a).
    move=> v w vin win; rewrite /= ler_oppl opprK mong ?oppr_itvcc //.
    by rewrite ler_oppl opprK.
  have ofK : {in `[(-b), (-a)], cancel (-%R \o f \o -%R)(-%R \o g \o -%R)}.
    move=> v; rewrite -oppr_itvcc /= => vin.
    by rewrite opprK fK // opprK.
  have ogK : {in `[(- f b), (- f a)],
        cancel (-%R \o g \o -%R) (-%R \o f \o -%R)}.
    move=> v; rewrite -oppr_itvcc /= => vin.
    by rewrite opprK gK // opprK.    
  have oyin : -y \in `](- f b), (- f a)[ by rewrite oppr_itvoo !opprK.
  have := main _ _ (-%R \o g \o -%R)(-%R \o f \o -%R) (-y) obLoa.
    rewrite /= 2!opprK=> /(_ ofbLofa monof monog ofK ogK oyin) main'.
  near=> u; case: (ltrgtP u y); last 1 first.
  - by move=> ->; rewrite subrr normr0.
  - by near: u; apply: (main a b _ f).
  rewrite -(opprK y) -(opprK u) ltr_oppr -normrN opprD [in X in X -> _]opprK.
  near: u; rewrite near_simpl.
  by rewrite (nearN y (fun w => w < - y -> 
                `|- g(- - y) - - g (- w)| < e%:num)).
move=> {a b f g aLb faLfb aab bab monf mong fK gK y yin}. 
move=> a b g f y aLb faLfb monf mong fK gK yin.
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
have fafafb : f a \in `[(f a), (f b)].
  by rewrite in_itv /= lexx ltW.
have gyLb : g y < b.
  by rewrite -(fK b) // ltNge mong ?(itvP yin) // subset_itv_oo_cc.
have aLgy : a < g y.
  by rewrite -(fK a) // ltNge mong // ?(itvP yin) ?subset_itv_oo_cc.
have gymeLgy : g y - e%:num < g y.
   by rewrite ltr_subl_addr ltr_addl.
case: (lerP a (g y - e%:num))=> [aLgyme | gymeLa ]; last first.
  have below : forall u, f a < u -> u < y -> `|g y - g u| < e%:num.
    move=> u aLu uLy.
    have uin : u \in `[(f a), (f b)].
      by rewrite in_itv /= ltW //= (ltW (lt_trans uLy _)) ?(itvP yin).
    have guLgy : g u <= g y.
      by rewrite mong //;[ rewrite ltW | rewrite subset_itv_oo_cc].
    move: (guLgy); rewrite -subr_ge0=> /ger0_norm => ->.
    rewrite ltr_subl_addr -ltr_subl_addl (lt_trans gymeLa) //.
    by rewrite ltNge -(fK a) // mong // -ltNge.
  near=> u; apply: below; suff h : u \in `](f a), (f b)[ by rewrite (itvP h).
  by near: u; apply: near_in_interval.
have below : forall u, f (g y - e%:num) < u -> u < y ->
     `|g y - g u| < e%:num.
  have gymein : g y - e%:num \in `[a, b].
    by rewrite in_itv /= aLgyme (le_trans _ (ltW gyLb)) // ler_subl_addl ler_addr.
  have faLfgyme : f a <= f (g y - e%:num) by rewrite monf.
  move=> u fgymeLu uLy.
  have uin : u \in `[(f a), (f b)].
    rewrite in_itv /= (ltW (lt_trans uLy _)) // ?andbT ?(itvP yin) //.
    by rewrite (le_trans faLfgyme) // ltW.
  have guLgy : g u <= g y.
    rewrite mong;[rewrite ltW //| | rewrite subset_itv_oo_cc //].
    rewrite in_itv /= (ltW (le_lt_trans _ fgymeLu)) /=.
      by rewrite (ltW (lt_trans uLy _)) // (itvP yin).
    by rewrite monf.
  move: (guLgy).
  rewrite -subr_ge0=> /ger0_norm=> ->; rewrite ltr_subl_addl -ltr_subl_addr.
  rewrite ltNge -monf //.
    by rewrite -ltNge gK //.
  rewrite in_itv /= -(fK a) ?mong // ltW //=.
    by rewrite (le_trans guLgy) // ltW.
  by rewrite (le_lt_trans faLfgyme fgymeLu).
near=> u; apply: below.
suff : u \in `]f (g y - e%:num), (f b)[ by move=> uin; rewrite (itvP uin).
near: u; apply: near_in_interval; rewrite in_itv /= ?(itvP yin) andbT.
rewrite -[X in _ < X](gK y); last by rewrite subset_itv_oo_cc.
rewrite ltNge monf -?ltNge //; first by rewrite in_itv /= !ltW.
rewrite in_itv /= aLgyme /= (le_trans _ (ltW gyLb)) // ltW //.
Grab Existential Variables.  all:end_near. Qed.

Lemma inverse_increasing_continuous (a b : R) (f g : R -> R) : a < b ->
  f a <= f b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `](f a), (f b)[, continuous g}.
Proof.
move=> aLb faLfb' ctf fK.
have faLfb : f a < f b.
  rewrite lt_neqAle faLfb' andbT; apply/eqP=> fafb.
  by move: (aLb); rewrite -(fK a) ?fafb ?fK ?ltxx // ?in_itv /= lexx (ltW aLb).
have ivt : {in `](f a), (f b)[, forall y, exists2 x, a < x < b & y = f x}.
  move=> y yin.
  have yin' : y \in `[(f a), (f b)] by rewrite subset_itv_oo_cc.
  have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb)=> // _ _.
  move=> /(_ _ yin')=> [][] c; rewrite in_itv /= !le_eqVlt=> /andP[].
  move=> /orP[/eqP <- |aLc].
    by move=> _ fay; move: yin; rewrite -fay in_itv /= ltxx.
  move=> /orP[/eqP -> |cLb].
    by move=> fy; move: yin; rewrite -fy in_itv /= ltxx andbF.
  by move=> <-; exists c; rewrite ?aLc ?cLb.
have ifab : If f a b.
  by rewrite /If=> u v uin vin fufv; rewrite -(fK u uin) fufv fK.
have [incrf | abs] := segment_continuous_inj_monotone ctf ifab; last first.
  move: (abs a b); rewrite !in_itv /= !lexx ltW // ltW // leNgt aLb.
  by move=> /(_ isT isT).
have incrg := left_inverse_increasing aLb faLfb' ctf fK.
have gK := interval_injective_continuous_bijective aLb ctf incrf fK.
by apply: monotone_surjective_continuous.
Qed.

Lemma subset_ball_prop_in_itv (x : R) e P :
  (ball_ [eta Num.Def.normr] x e `<=` P)%classic <->
  {in  `](x - e), (x + e)[ , forall y, P y}.
Proof.
split.
  move=> bp y; rewrite in_itv/= => yin; apply: bp=> /=.
  by rewrite distrC ltr_distl.
by move=> inxep y /= inball; apply: inxep; rewrite in_itv/= -ltr_distl distrC.
Qed.

Lemma prop_in_and (p : mem_pred R) (P Q : R -> Prop) :
  {in p, forall x, P x /\ Q x} <->
  {in p, forall x, P x} /\ {in p, forall x, Q x}.
Proof.
split.
  by move=> cnd; split; move=> x xin; case: (cnd x xin).
by move=> [cnd1 cnd2] x xin; split;[apply: cnd1 | apply: cnd2].
Qed.

Ltac staged_split :=
  repeat (rewrite andb_idr;[ | move=> *]).

(* This is an example that appears in the following proof.  I think
  there could be a use case for tactic that leads the user to proving
  a conjunction by addressing the second component with the assumption
  that the first one already holds. *)
Fact itv_example (x e  : R):
  0 < e -> [&& x < x + e, x - e < x & x - e < x + e].
Proof.
move=> e0; staged_split;[rewrite ltr_addl // | rewrite ltr_subl_addr //| ].
(* Unfortunately, the name of the hypotheses could be useful here. *)
eapply lt_trans; eassumption.
Qed.

Fact continuous_inverse_main  (f g : R -> R) (x : R) :
  {near x, cancel f g} -> {near x, continuous f} ->
  {near (f x), continuous g} /\ {near (f x), cancel g f}.
Proof.
(* The first 3 lines to get the left inverse propoerty and the continuity    *)
(* in the same ball, and transform this ball into an interval, and have      *)
(* the two properties separately.                                            *)
move=> fK ctf; have /(proj1 (and_comm _ _) (near_andP _ _ _)) :=
  conj fK ctf => {fK ctf}.
case=> [e' e'gt0]/subset_ball_prop_in_itv/prop_in_and [fK ctf].
(* We then need a non-singleton closed interval containing x inside the      *)
(* ball.                                                                     *)
set e := e' / 2.
have e0 : 0 < e by apply: divr_gt0.
have elte' : e < e' by rewrite /e ltr_pdivr_mulr // mulr_natr mulr2n ltr_addl.
have itvsub  : {subset `[(x - e), (x + e)] <= `](x - e'), (x + e')[}.
  apply/subitvP.
  by rewrite subitvE /Order.le /= !ltr_add2l ltr_oppl opprK elte'.
have fK' : {in `[x - e, x + e], cancel f g}.
  by apply/(sub_in1 itvsub fK).
have ctf' : {in `[x - e, x + e], continuous f}.
  by apply/(sub_in1 itvsub ctf).
have /and3P[cmp2 [cmp1 cmp]] : [&& x < x + e, x - e < x & x - e < x + e].
  by rewrite !(ltr_subl_addr, ltr_addl, ltr_spsaddr) e0.
have ifx : If f (x - e) (x + e).
  by move=> v w vin win fq; rewrite -(fK' v) // fq fK'.
have [mfx |mfx] := segment_continuous_inj_monotone ctf' ifx; split.
- near=> z; apply: inverse_increasing_continuous ctf' _ _ _ => //.
  * by rewrite mfx ?ltW // in_itv /= ?lexx ltW.
  near: z; rewrite near_simpl; apply: near_in_interval.
  by rewrite in_itv /= !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp1, ltW).
- near=> z.
  apply: (interval_injective_continuous_bijective _ ctf') => //.
  apply: subset_itv_oo_cc.
  near: z; rewrite near_simpl; apply: near_in_interval.
  by rewrite in_itv /= !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp1, ltW).
- have ctNf: {in `[(x - e), (x + e)], continuous (- f)}.
  *  by move=> z zI; apply/continuousN/ctf'.
  near=> y; rewrite -[y]opprK (_ : g = (g \o -%R \o -%R)); last first.
  *  by apply: funext=> u; rewrite /= opprK.
  apply: continuous_comp; rewrite opprK; first by apply: continuousN.
  apply: inverse_increasing_continuous ctNf _ _ _ => //.
  * by rewrite lter_oppr opprK mfx ?ltW // in_itv /= ?lexx ltW.
  * by move=> z zI; rewrite /= opprK fK'.
  rewrite oppr_itvoo !opprK.
  near: y; rewrite near_simpl; apply: near_in_interval.
  by rewrite in_itv /= !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp2, ltW).
near=> y; suff : ((f \o -%R) \o -g) y = y by rewrite /= opprK.
have ctNf' : {in `[ (- x - e), (- x + e)], continuous (f \o -%R)}.
  move=> z zin; apply: continuous_comp; first by apply: continuousN.
  by apply: ctf'; rewrite oppr_itvcc !opprD opprK.
  apply: (interval_injective_continuous_bijective _ ctNf').
- by rewrite -opprD lter_oppl opprD opprK.
- move=> z1 z2; rewrite -opprD (addrC (- x)) -opprB -!oppr_itvcc=> z1I z2I.
  by rewrite mfx // 1?lter_oppl ?opprK.
- move=> z; rewrite -opprD (addrC (- x)) -opprB -!oppr_itvcc=> zI.
  by rewrite -[RHS](opprK z); congr (- _); rewrite /= fK'.
apply: subset_itv_oo_cc.
near: y; rewrite near_simpl; apply: near_in_interval.
rewrite in_itv /= !(opprD, opprK).
by rewrite !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp2) // ltW // ltW.
Grab Existential Variables. all:end_near. Qed.

Lemma continuous_inverse (f g : R -> R) (x : R) :
  {near x, cancel f g} -> {near x, continuous f} ->
  {near (f x), continuous g}.
Proof. by move=> fK ctf; case: (continuous_inverse_main fK ctf). Qed.

Lemma inverse_swap_continuous  (f g : R -> R) (x : R) :
  {near x, cancel f g} -> {near x, continuous f} -> {near (f x), cancel g f}.
Proof. by move=> fK ctf; case: (continuous_inverse_main fK ctf). Qed.

Lemma sqr_continuous : continuous (exprz (R := R) ^~ 2).
Proof.
move => x s.
rewrite (_ : (fun x => x ^ 2) = fun x : R => x * x); last first.
  by  apply: funext=> y; rewrite exprSz expr1z.
by rewrite exprSz expr1z; apply: continuousM.
Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x.
case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0).
  rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
- by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
  have csqr : \forall z \near Num.sqrt x,
     {for z, continuous (exprz (R := R) ^~ 2)}.
    by near=> z; apply: sqr_continuous.
  have sqrtxgt0 : 0 < Num.sqrt x by rewrite sqrtr_gt0.
  have sqrK : \forall z \near (Num.sqrt x),
                  Num.sqrt ((exprz (R := R) ^~ 2) z) = z.
    near=> z; rewrite sqrtr_sqr; apply/normr_idP/ltW.
    near: z; rewrite !near_simpl (near_shift 0).
    near=> z; rewrite /= subr0 -ltr_subl_addl sub0r ltr_normlW // normrN.
    by near: z; apply: nbhs0_lt.
  have := (nbhs_singleton (continuous_inverse sqrK csqr)).
  by rewrite -exprnP sqr_sqrtr // ltW.
apply/cvg_distP=> _ /posnumP[e]; rewrite !near_simpl /=.
near=> y; rewrite sqrtr0 sub0r normrN.
rewrite ger0_norm ?sqrtr_ge0 //.
have ylte2 : y < e%:num ^+ 2.
  rewrite ltr_normlW //; near: y; apply: nbhs0_lt.
  by rewrite exprn_gt0.
have twogt0 : (0 < 2)%N by [].
rewrite -(ltr_pexpn2r twogt0) ?inE ?nnegrE ?ltrW ?sqrtr_ge0 //.
have [ylt0 | yge0 ] := (ltrP y 0); last by rewrite sqr_sqrtr.
by rewrite ltr0_sqrtr // expr0n /= exprn_gt0.
Grab Existential Variables. all: end_near. Qed.

End real_inverse_functions.
