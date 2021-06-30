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

Lemma inverse_monotone (a b : R) (f g : R -> R) :
  a < b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `[(Num.min (f a) (f b)), (Num.max (f a) (f b))] &, {mono g : x y / x <= y}} \/
  {in `[(Num.min (f a) (f b)), (Num.max (f a) (f b))] &, {mono g : x y /~ x <= y}}.
Proof.
move=> aLb ctf fK.
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
have fanfb : f a != f b.
  by apply/eqP=> fafb; move: (aLb); rewrite -(fK a) // fafb (fK b) // ltxx.
wlog incr : f g ctf fK fanfb/ {in `[a, b] &, {mono f : x y / x <= y}}.
  move=> main.
  have ijf : If f a b by move=> x y xin yin fq; rewrite -(fK x) ?fq ?(fK y).
  case: (near_injective_monotone ijf ctf) => monf.
    by apply: (main _ _ ctf fK fanfb monf).
  have monof : {in `[a, b] &, {mono (-%R \o f) : x y / x <= y}}.
    by move=> x y xin yin; rewrite ler_oppl opprK; apply: monf.
  have ofK : {in `[a, b], cancel (-%R \o f) (g \o -%R)}.
    by move=> x xin; rewrite /= opprK; apply: fK.
  have ctof : {in `[a, b], continuous (-%R \o f)}.
    by move=> x ?; apply: continuous_comp;[apply: ctf | apply: opp_continuous].
  have ofanofb : -f a != - f b by rewrite (inj_eq oppr_inj).
  have faLfb : f b < f a.
    by rewrite lt_neqAle monf ?in_itv //= ltW ?andbT // eq_sym.
  case: (main _ _ ctof ofK ofanofb monof)=> monog.
    right; move=> x y xin yin; rewrite -(opprK y) ler_oppl.
    rewrite -[X in (g X <= _) = _](opprK x).
    have := monog (-x) (-y); rewrite /= -oppr_max -oppr_min.
    case: (ltrgtP (f b) (f a)) (faLfb) xin yin=> _ _ // xin yin.
    by apply; rewrite oppr_itv /= !opprK.
  left; move=> x y xin yin; rewrite -(opprK y) ler_oppr.
    rewrite -[X in (g X <= _) = _](opprK x).
  have := monog (- x) (-y); rewrite /= -oppr_max -oppr_min.
  case: (ltrgtP (f b) (f a)) (faLfb) xin yin=> _ _ // xin yin.
  by apply; rewrite oppr_itv /= !opprK.
left.
have faLfb : f a < f b.
  by rewrite lt_neqAle fanfb incr // ltW.
move=> x y; case: (ltrgtP (f a) (f b)) (faLfb)=> // _ _ xin yin.
have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb)=> // _ _ ivt.
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
have faLfb : f a <= f b by rewrite monf ?in_itv /= ?lexx ltW.
have := IVT (ltW aLb) ctf; case: (lerP (f a) (f b)) (faLfb)=> // _ _=> ivt.
by case: (ivt _ yin)=> x xin <-; rewrite fK.
Qed.
  
Lemma near_opp (a : R) (P : R -> Prop) :
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
  {in `](f a), (f b)[ , continuous g}.
Proof.
move=> aLb monf mong fK gK y yin; apply/cvg_distP=> _ /posnumP[e].
have faLfb : f a < f b.
  by rewrite (lt_trans (_ : f a <  y) _) // (itvP yin).
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
suff main : (forall (a b : R) (g f : R -> R) y, a < b -> f a < f b ->
         {in `[a, b] &, {mono f : x y / x <= y}} ->
         {in `[(f a), (f b)] &, {mono g : x y / x <= y}} ->
         {in `[a, b], cancel f g} ->
         {in `[(f a), (f b)], cancel g f} ->
         y \in `](f a), (f b)[ ->
         \forall u \near y, u < y -> `|g y - g u| < e%:num).
  rewrite !near_simpl.
  have obLoa : -b < -a by rewrite ltr_oppl opprK.
  have ofbLofa : - f b < - f a by rewrite ltr_oppl opprK.
  have monof : {in `[(-b), (-a)] &, 
        {mono (-%R \o f \o -%R) : v w / v <= w}}.
    move=> v w vin win; rewrite /= ler_oppl opprK monf ?oppr_itvcc //.
    by rewrite ler_oppl opprK.
  have monog : {in `[(-f b), (-f a)] &,
          {mono (-%R \o g \o -%R) : v w / v <= w}}.
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
  - by near: u; rewrite near_simpl; apply: (main a b _ f).
  rewrite -(opprK y) -(opprK u) ltr_oppr -normrN opprD [in X in X -> _]opprK.
  near: u; rewrite near_simpl.
  by rewrite (near_opp y (fun w => w < - y -> 
                `|- g(- - y) - - g (- w)| < e%:num)).
move=> {a b f g aLb faLfb aab bab monf mong fK gK y yin}. 
move=> a b g f y aLb faLfb monf mong fK gK yin.
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
have fafafb : f a \in `[(f a), (f b)].
  by rewrite in_itv /= lexx ltW.
have gyLb : g y < b.
  by rewrite -(fK b) // ltNge mong ?(itvP yin) // strict_to_large_itv.
have aLgy : a < g y.
  by rewrite -(fK a) // ltNge mong // ?(itvP yin) ?strict_to_large_itv.
have gymeLgy : g y - e%:num < g y.
   by rewrite ltr_subl_addr ltr_addl.
case: (lerP a (g y - e%:num))=> [aLgyme | gymeLa ]; last first.
  have below : forall u, f a < u -> u < y -> `|g y - g u| < e%:num.
    move=> u aLu uLy.
    have uin : u \in `[(f a), (f b)].
      by rewrite in_itv /= ltW //= (ltW (lt_trans uLy _)) ?(itvP yin).
    have guLgy : g u <= g y.
      by rewrite mong //;[ rewrite ltW | rewrite strict_to_large_itv].
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
    rewrite mong;[rewrite ltW //| | rewrite strict_to_large_itv //].
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
rewrite -[X in _ < X](gK y); last by rewrite strict_to_large_itv.
rewrite ltNge monf //.
* by rewrite -ltNge.
* by rewrite in_itv /= (ltW aLgy) (ltW gyLb).
rewrite in_itv /= aLgyme /= (le_trans _ (ltW gyLb)) // ltW //.
Grab Existential Variables.  all:end_near. Qed.

Lemma inverse_continuous (a b : R) (f g : R -> R) : a < b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `](Num.min (f a) (f b)), (Num.max (f a) (f b))[, continuous g}.
Proof.
move=> aLb.
wlog faLfb : f g / f a < f b.
  case: (ltrgtP (f a) (f b)); last 1 first.
  - by move=> _ _ _ _ y; rewrite in_itv /=; case: (ltrgtP (f a) y).
  - move=> faLfb main; move: {main} (main _ g faLfb).
    by case: (ltrP (f a) (f b)) faLfb.
  move=> fbLfa /(_ (-%R \o f) (g \o -%R)) main ctf fK.
   have ctf' : {in `[a, b], continuous (-%R \o f)}.
    move=> x xin.
    by apply: continuous_comp;[apply ctf | apply: opp_continuous].
  have fK' : {in `[a, b], cancel (-%R \o f)(g \o -%R)}.
    by move=> x; rewrite /= opprK; exact: fK.
  suff ct_gopp : {in `](-f a), (-f b)[, continuous (g \o -%R)}.
    rewrite (_ : g = (g \o -%R) \o -%R); last first.
      by apply: funext => x; rewrite /= opprK.
    move=> x xin; apply: continuous_comp.
      by rewrite forE; apply: opp_continuous.
    rewrite forE; apply: ct_gopp.
    by rewrite oppr_itvoo !opprK.
  move=> x xin; apply: main => //.
  + by rewrite /= ltr_oppr opprK.
  by rewrite /= -oppr_min -oppr_max; case: (ltrgtP (f b) (f a)) (fbLfa).
case: (ltrP (f a) (f b)) (faLfb)=> // _ _ ctf fK.
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
have ifab : If f a b.
  by rewrite /If=> u v uin vin fufv; rewrite -(fK u uin) fufv fK.
have [incrf | abs] := near_injective_monotone ifab ctf; last first.
  move: (abs a b); rewrite !in_itv /= !lexx ltW // ltW // leNgt aLb.
  by move=> /(_ isT isT).
have := inverse_monotone aLb ctf fK.
case: (ltrgtP (f a) (f b)) (faLfb) => // _ _ => [] [incrg | abs]; last first. 
  move: (aLb); rewrite ltNge -(fK b) ?in_itv /= ?lexx ?(ltW aLb) //.
  rewrite -(fK a) ?in_itv /= ?lexx ?(ltW aLb) //.
  by rewrite abs ?(ltW faLfb) // in_itv /= lexx (ltW faLfb).
have gK := interval_injective_continuous_bijective aLb ctf incrf fK.
by apply: monotone_surjective_continuous.
Qed.

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
  have xp1gt0' : 0 < x + 1 by rewrite addr_gt0.
  have m01' : Num.min 0 (x + 1) = 0 by case: (ltrgtP 0 (x + 1)) xp1gt0'.
  have M01' : Num.max 0 (x + 1) = (x + 1) by case: (ltrgtP 0 (x + 1)) xp1gt0'. 
  have ctf := csqr _ xp1gt0.
  apply: (inverse_continuous xp1gt0 ctf).
  move=> u; rewrite sqrtr_sqr => uin; apply/normr_idP.
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
