From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
From mathcomp Require Import wochoice contra mathcomp_extra.
From mathcomp Require Import boolp classical_sets set_interval.
From mathcomp Require Import topology_structure separation_axioms connected.
From mathcomp Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Import boolp.

Import classical_sets.
Local Open Scope classical_set_scope.

Section general_topology.
Context {T : topologicalType}.

Section connected_separated.
Let open_half_separated (A B : set T) :
  open A -> open B -> A `&` B = set0 -> closure A `&` B = set0.
Proof.
move=> oA oB.
rewrite disjoints_subset -subset0.
move=> /closure_subset; rewrite closure_setC.
move: oB=> /interior_id -> /(@setSI _ B).
by rewrite setICl.
Qed.

Lemma open_separated (A B : set T) :
  open A -> open B -> A `&` B = set0 -> separated A B.
Proof.
move=> oA oB AB0; split; first exact: open_half_separated.
by rewrite setIC; apply: open_half_separated=> //; rewrite setIC.
Qed.

Lemma subset_separated2l (A B C : set T) :
  B `<=` C -> separated A C -> separated A B.
Proof.
move=> BC []; rewrite -!subset0.
have:= BC => /(@setIS _ (closure A)) /subset_trans /[apply] ?.
have:= closure_subset BC=> /(@setIS _ A) /subset_trans /[apply] ?.
by split; rewrite -!subset0.
Qed.

Lemma subset_separated2r (A B C : set T) :
  B `<=` C -> separated C A -> separated B A.
Proof. by rewrite !(separatedC _ A); exact: subset_separated2l. Qed.

Lemma subset_separated (A B C D : set T) :
  A `<=` B -> C `<=` D -> separated B D -> separated A C.
Proof. by move=> ? /subset_separated2l /[apply]; exact: subset_separated2r. Qed.

Lemma connectedPn (A : set T) :
  ~ connected A <->
    (exists E1 E2 : set T,
        [/\ E1 !=set0, E2 !=set0, A = E1 `|` E2 & separated E1 E2]).
Proof.
split; first by move/connectedPn=> [] E [] *; exists (E false), (E true).
case=> E1 [] E2 [] *.
apply/connectedPn; exists (fun b=> if b then E2 else E1); split=> //.
by case.
Qed.

End connected_separated.

Section extra.

(* TODO: better name? *)
Lemma nbhs_cobind (x y : T) :
  (forall A, nbhs x A -> A y) -> forall A, nbhs x A -> nbhs y A.
Proof.
move=> + A /[1!(nbhsE x)] -[] U oU UA => /(_ U (open_nbhs_nbhs oU)) Uy.
by rewrite nbhsE; exists U=> //; split; case: oU.
Qed.

Lemma all_and2P (P Q : T -> Prop):
  (forall A, P A /\ Q A) <-> ((forall A, P A) /\ (forall A, Q A)).
Proof. by firstorder. Qed.

Lemma all_and2E (P Q : T -> Prop):
  (forall A, P A /\ Q A) = ((forall A, P A) /\ (forall A, Q A)).
Proof. exact/propeqP/all_and2P. Qed.

End extra.

Lemma kolmogorov_inj_nbhsP : kolmogorov_space T <-> injective (@nbhs _ T).
Proof.
split => i x y.
  apply: contraPP => /eqP /i [] X [] [] /[swap] h1 /[swap] xy;
  by rewrite inE in h1; rewrite (xy, esym xy) inE => /nbhs_singleton /h1.
apply: contraNP => /asboolPn /forallp_asboolPn H.
apply/eqP/i/predeqP => A.
wlog: x y H / nbhs x A.
  split => ?; first by rewrite -(H0 x).
  by rewrite -(H0 y) => // B; rewrite boolp.orC.
split=> //.
rewrite nbhsE => -[] B /[dup] /open_nbhs_nbhs nbhsB [] opB Bx BA.
move: (H B); rewrite not_orE !inE !not_andE -!implyE !notK.
by case => /(_ nbhsB) By _; apply/(filterS BA) /open_nbhs_nbhs.
Qed.

End general_topology.

Section Sorgenfrey_line.
Variable R : realType.

Let I := (R^o * R^o)%type.
Let D := [set : I].
Let b (d : I) := `[ d.1, d.2 [%classic.
Let b_cover : \bigcup_(i in D) b i = setT. 
Proof.
apply/seteqP; split  => // x _ .
exists (x, x+1)%R => //=.
by rewrite /b /=  in_itv /= lexx /= ltrDl.
Qed.
Let b_join i j t : D i -> D j -> b i t -> b j t ->
    exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof.
move=> _ _; case: i=> i1 i2; case: j=> j1 j2.
rewrite /b /= !in_itv /= => /andP [] i1t ti2 /andP [] j1t tj2.
exists (Order.max i1 j1, Order.min i2 j2).
rewrite /D /= in_itv /= subsetI.
case: (leP i1 j1) => ij1; case: (leP i2 j2) => ij2.
all: rewrite !(i1t, ti2, j1t, tj2)/=.
all: split=> //; split; apply: subset_itv.
all: by rewrite leBSide //= ltW.
Qed.

#[non_forgetful_inheritance]
HB.instance Definition _ := @isPointed.Build R 0.
#[non_forgetful_inheritance]
HB.instance Definition Sorgenfrey_mixin := @isBaseTopological.Build R I D b b_cover b_join. 
Definition sorgenfrey := HB.pack_for topologicalType _ Sorgenfrey_mixin.

Lemma sorgenfrey_totally_disconnected : totally_disconnected [set: sorgenfrey].
Proof.
move=> x _.
apply/seteqP; split=> y //=; last by move->; apply: connected_component_refl.
case=> C [] Cx _ + Cy; apply: contraPP=> yx.
wlog xy : x y yx Cx Cy / x < y.
  have/eqP:= yx; rewrite real_neqr_lt ?num_real// => /orP [].
    by move/[swap]/[apply]/(_ (nesym yx)); exact.
  by move/[swap]/[apply]; exact.
apply/connectedPn; exists (C `&` `]-oo, y[ ), (C `&` `[y, +oo[ ); split.
- by exists x.
- by exists y; split=> //=; rewrite in_itv /= lexx.
- by rewrite -setIUr -itv_bndbnd_setU// set_itvNyy setIT.
apply: subset_separated; [exact: subIsetr | exact: subIsetr |].
apply: open_separated.
- have-> : `]-oo, y[ = \bigcup_(z in `]-oo, y[ ) `[z, y[.
    apply/seteqP; split=> w /=; rewrite in_itv/=.
      by move=> wy; exists w=> //=; rewrite in_itv/= lexx.
    by case=> z /=; rewrite !in_itv/= => _ /andP [].
  apply: bigcup_open=> w ?; exists [set (w, y)]=> //.
  exact: bigcup_set1.
- have-> : `[y, +oo[ = \bigcup_(z in `[y, +oo[ ) `[y, z[.
    apply/seteqP; split=> w /=; rewrite in_itv/= andbT.
      move=> yw; exists (w+1) => /=; rewrite in_itv/= ?ler_wpDr//.
      by rewrite yw/= ltrDl.
    by case=> z /=; rewrite !in_itv/= => _ /andP [].
  apply: bigcup_open=> w _; exists [set (y, w)]=> //.
  exact: bigcup_set1.
rewrite -subset0=> w [] /=; rewrite !in_itv /= andbT.
by move/lt_le_trans/[apply]; rewrite ltxx.
Qed.

Section distance.
Variable E : set sorgenfrey.
Hypothesis CE : closed E.

(* Pseudo-distance function for perfectly normal space *)
Let dl x := [set y | x - y \in E /\ 0 <= y].
Let dr x := [set y | x + y \in E /\ 0 < y].
Definition sdist (x : sorgenfrey) : R :=
  Order.min (if x - inf (dl x) \in E then inf (dl x) else 1)
            (if dr x == set0 then 1 else inf (dr x)).

From mathcomp Require Import topology normedtype.
Let Rtopo := num_topology.numFieldTopology.Real_sort__canonical__topology_structure_Topological R.

Local Lemma dlE x : dl x = [set shift x (- y) | y in E] `&` `[0, +oo[.
Proof.
rewrite /dl; apply/seteqP; split=> y /=; rewrite in_itv inE /=.
  case=> Exy ->; split => //.
  by exists (x - y) => //; rewrite opprB addrAC addrK.
case=> -[] u Eu <- /[!andbT] ->; split => //.
by rewrite opprD opprK subrKC.
Qed.

Local Lemma drE x : dr x = (center x) @` E `&` `]0, +oo[.
Proof.
rewrite /dr; apply/seteqP; split=> y /=; rewrite in_itv inE /=.
  case=> Exy ->; split => //.
  by exists (x + y) => //; rewrite addrAC subrr add0r.
case=> -[] v Ev <- /[!andbT] ->; split => //.
by rewrite mathcomp_extra.subrKC.
Qed.

Local Lemma lt_dr_set0 x y : x < y -> dr x = set0 -> dr y = set0.
Proof.
move=> xy.
rewrite !drE !(rwP eqP); apply: contraLR.
case/set0P=> u /= [] [] v Ev <-.
rewrite in_itv /= andbT subr_gt0 => yv.
apply/set0P; exists (v - x) => /=.
rewrite in_itv /= subr_gt0 (lt_trans xy yv); split => //.
by exists v.
Qed.

Local Lemma lt_dl_set0 x y : x < y -> dl y = set0 -> dl x = set0.
move=> xy.
rewrite !dlE !(rwP eqP); apply: contraLR.
case/set0P=> u /= [] [] v Ev <-.
rewrite in_itv /= andbT addrC subr_ge0 => vx.
apply/set0P; exists (y - v) => /=.
rewrite in_itv /= subr_ge0 (le_trans vx (ltW xy)); split => //.
by exists v => //; rewrite addrC.
Qed.

Lemma abs_subr_min (x y t u : R) :
  `|Num.min x y - Num.min t u| <= Num.max `|x - t| `|y - u|.
Proof.
wlog: x y t u / x <= y.
  move=> H.
  case/boolP: (x <= y) => [/H //| xy].
  by rewrite minC (minC t) maxC H // ltW // ltNge.
case: (lerP x y) => // xy _.
case: (lerP t u) => tu; rewrite le_max.
  by rewrite lexx.
case: (lerP x u) => xu.
  case: (lerP x t) => xt. by rewrite lerD2r ltW.
  by rewrite leNgt (lt_trans tu xt) in xu.
case: (lerP u y) => uy. by rewrite lerD2r xy orbT.
by rewrite leNgt (lt_trans uy xu) in xy.
Qed.

Lemma inf_ge0 (S : set R) : lbound S 0 -> inf S >= 0.
Proof.
move=> S_ge0.
case/boolP: (S == set0) => [/eqP -> | /set0P S0].
  by rewrite inf0.
by apply: lb_le_inf.
Qed.

Let dl_ge0 x : lbound (dl x) 0.
Proof. by move=> y []. Qed.

Let dr_ge0 x : lbound (dr x) 0.
Proof. move=> y [] _; exact: ltW. Qed.

Lemma sdist_ge0 x : 0 <= sdist x.
Proof. by rewrite /sdist le_min !fun_if ler01 !inf_ge0 // !if_same. Qed.

Lemma image2_set1 A B C (S : set A) (eb : B) (f : A -> B -> C) :
  [set f x y | x in S & y in [set eb]] = [set f x eb | x in S].
Proof.
apply/seteqP; split => y /= [] u dlxu.
  by case=> v -> <-; exists u.
by move <-; exists u => //; exists eb.
Qed.

Lemma image2X A B C (SA : set A) (SB : set B) (f : A -> B -> C) :
  [set f x y | x in SA & y in SB] = [set f x y | y in SB & x in SA].
Proof.
rewrite !image2E.
by apply/seteqP; split => c /= [] [x y] /= [] Hx Hy <-; exists (y,x).
Qed.

Let dl_shift x z :
  x < z -> `]x, z] `<=` ~` E -> dl z = [set t + (z - x) | t in dl x].
Proof.
move=> xz xzNE.
apply/seteqP; rewrite /dl; split => t /= [].
  move => ztE y0.
  case: (ltrP x (z-t)) => ztx.
    suff : z - t \notin E by rewrite ztE.
    rewrite -in_setC inE.
    apply: xzNE.
    by rewrite /= in_itv /= ztx lerBlDr lerDl.
  exists (x - (z-t)).
    by rewrite opprD addrA subrr opprK add0r ztE subr_ge0.
  by rewrite (addrC z) opprD opprK !addrA subrK addrC addKr.
move=> w [] xwE w0 <-.
rewrite !opprD (addrCA z) !addrA addrK addrC opprK.
by rewrite subr_ge0 ler_wpDl // ltW.
Qed.

Let dr_shift x z :
  x < z -> `]x, z] `<=` ~` E -> dr x = [set t + (z - x) | t in dr z].
Proof.
move=> xz xzNE.
apply/seteqP; rewrite /dr; split => t /= [].
  move => xtE y0.
  case: (ltrP z (x+t)) => zxt; last first.
    suff : x + t \notin E by rewrite xtE.
    rewrite -in_setC inE.
    apply: xzNE.
    by rewrite /= in_itv /= zxt ltrDl y0.
  exists (x + t - z).
    by rewrite addrC subrK xtE subr_gt0.
  by rewrite addrA subrK addrC addKr.
move=> w [] xwE w0 <-.
rewrite !addrA addrC addrA addKr addrC.
by rewrite subr_gt0 ltr_wpDr // ltW.
Qed.

Lemma inf_shift (s1 s2 : set R) (d : R) :
  s2 = [set t + d | t in s1] ->
  has_inf s1 ->
  inf s2 = inf s1 + d.
Proof. by move=> -> lbs1; rewrite -image2_set1 inf_sumE // inf1. Qed.

Lemma inf_dlxz x z :
  dl z = [set t + (z - x) | t in dl x] ->
  dl x !=set0 ->
  inf (dl z) = inf (dl x) + z - x.
Proof. by move=> H *; rewrite -addrA -(inf_shift H)//; split=>//; exists 0. Qed.

Lemma inf_drxz x z :
  dr x = [set t + (z - x) | t in dr z] ->
  dr z !=set0 ->
  inf (dr x) = inf (dr z) + z - x.
Proof. by move=> H *; rewrite -addrA -(inf_shift H)//; split=>//; exists 0. Qed.

Lemma sdist_in_le x t d :
  x + d \in E -> x <= t < x + d -> sdist t <= d.
Proof.
move=> dE /andP[xt tx] /=.
rewrite /sdist.
rewrite ge_min; apply/orP; right.
have Ht : dr t (d + x - t) by rewrite /dr /= addrC subrK subr_gt0 addrC.
have /set0P /negbTE -> : dr t !=set0 by exists (d+x-t).
apply: (le_trans _ _ (y:=d+x-t)).
  by apply: inf_lbound => //; exists 0.
by rewrite lerBlDr lerD.
Qed.

Lemma lerPnormB (x y m : R) : 0 <= x <= m -> 0 <= y <= m -> `|x - y| <= m.
Proof. by do!case/andP=>??; rewrite -maxrN ge_max opprB !lerBlDr !ler_wpDr. Qed.

Definition continuous_at_sorgenfrey_to_Rtopo x (f : sorgenfrey -> R) :=
  forall eps : R, 0 < eps -> exists2 d : R, 0 < d & forall y : R, x <= y < x + d -> `|f x - f y| < eps.

Lemma continuous_at_sorgenfrey_to_RtopoP f x :
  continuous_at_sorgenfrey_to_Rtopo x f -> @continuous_at sorgenfrey Rtopo x f.
Proof.
move=> H B.
rewrite -(@filter_from_ballE R (GRing_regular__canonical__pseudometric_structure_PseudoMetric R)).
case => eps /= eps0 epsB.
change (nbhs (f y @[y --> x]) B).
case: (H eps eps0) => /= d d0 H'.
exists (`[x,x+d[); split => //=.
- exists [set (x,x+d)] => //.
  by rewrite bigcup_set1.
- by rewrite in_itv /= lexx ltrDl d0.
rewrite -image_sub.
move=> y /= [] z.
rewrite in_itv /= => /andP[xz zx] <- {y}.
apply: epsB.
apply: H'.
by rewrite xz zx.
Qed.

Lemma continuous_sdist :
  forall x, @continuous_at sorgenfrey Rtopo x sdist.
Proof.
move=> x.
apply: continuous_at_sorgenfrey_to_RtopoP => /= eps eps0.
pose xepsE := [set y | x + y \in E /\ 0 < y < eps].
exists (xget eps xepsE).
  by case: (xgetP eps xepsE) => // y -> [] _ /andP[].
(* forall z : R, x <= z < x + eps' -> `|sdist x - sdist z| < eps *)
move=> z /andP[xz zx].
have [<-|xz'] := eqVneq x z.
  by rewrite subrr normr0.
have {xz xz'} xz: x < z by rewrite lt_neqAle xz'.
rewrite /sdist.
set xr : R := if dr x == set0 then _ else _.
set zr : R := if dr z == set0 then _ else _.
case/boolP: (xepsE == set0) => [xepsE0 | /set0P]; last first.
  move/xgetPex => /= /(_ eps).
  set d := xget eps xepsE in zx *.
  case=> xdE /andP[d0 deps].
  rewrite -/(sdist x) -/(sdist z) (le_lt_trans _ deps) //.
  have Hx : sdist x <= d by apply: (sdist_in_le xdE); rewrite // lexx ltrDl.
  have Hz : sdist z <= d by apply: (sdist_in_le xdE); rewrite // zx ltW // xz.
  by rewrite lerPnormB // sdist_ge0.
rewrite xgetPN in zx; last by move=> t; rewrite (eqP xepsE0).
have xznE : `]x,z] `<=` ~`E.
  move=> t /=.
  rewrite in_itv /= => /andP[xt tz].
  apply: contraTnot xepsE0.
  rewrite -inE => Et; apply/set0P.
  exists (t-x); rewrite /xepsE /= addrC subrK.
  by rewrite subr_gt0 xt ltrBlDl (le_lt_trans tz).
have znE : z \notin E.
  rewrite -in_setC inE; apply: xznE.
  by rewrite /= in_itv /= xz lexx.
rewrite (le_lt_trans (abs_subr_min _ _ _ _)) // gt_max.
apply/andP; split; last first.
- have drzx : dr x = [set t + (z - x) | t in dr z] by apply: dr_shift.
  rewrite /xr /zr drzx.
  have[-> | drz0] := eqVneq (dr z) set0.
    by rewrite image_set0 eqxx subrr normr0 eps0.
  case: ifPn => [/eqP /image_set0_set0 /eqP | drx0].
    by rewrite (negPf drz0).
  rewrite -drzx (inf_drxz drzx); last exact/set0P.
  by rewrite addrC addrA addKr ltr_distl zx ltrBlDr ltr_wpDr // ltW.
- have dlxz : dl z = [set t + (z - x) | t in dl x] by apply: dl_shift.
  case/boolP: (dl x == set0) => [/eqP | /set0P] dlx0.
    rewrite dlx0 inf0 subr0.
    case: ifPn => xinE.
      suff : 0 \in dl x by rewrite inE dlx0.
      by rewrite inE /dl /= subr0.
    by rewrite dlxz dlx0 image_set0 inf0 subr0 (negbTE znE) subrr normr0.
  rewrite (inf_dlxz dlxz) //.
  rewrite !opprD !addrA (addrC z) addrK (opprK x) (addrC (- _)).
  case: ifPn => xlE; last by rewrite subrr normr0.
  rewrite !opprD !addrA subrr add0r (addrC (- _)) (opprK x).
  by rewrite ltr_distl ltrBlDr zx ltr_wpDr // ltW.
Qed.

Lemma zeroset_sdist :  E = sdist @^-1` [set 0].
Proof.
apply/seteqP; split => x /= Hx.
  suff /eqP H : inf (dl x) == 0.
    apply/esym/eqP; rewrite eq_le sdist_ge0 /sdist H /=.
    by rewrite subr0 ifT ?inE // ge_min lexx.
  rewrite eq_le inf_ge0 // andbT.
  apply: inf_lbound.
    exists 0. by move => t /dl_ge0.
  by rewrite /dl /= subr0 inE.
move/eqP: Hx; rewrite /sdist minEle.
case: ifP => _.
  case: ifP; last by rewrite (negbTE (@oner_neq0 _)).
  rewrite inE => /[swap] /eqP ->.
  by rewrite subr0.
case: ifPn; first by rewrite (negbTE (@oner_neq0 _)).
move=> n0 /eqP infeq.
apply/notP => xE.
have : open (~` E) by rewrite openC.
rewrite openE /= => /(_ x xE) [] opx [] /= [] L HL <- [] /= [a a'] La.
rewrite /b /= in_itv /= => /andP[ax xa'].
move/(subset_trans (bigcup_sup La)) => /= aE.
have a'x_gt0 : a' - x > 0 by rewrite subr_gt0 xa'.
have hE : has_inf (dr x) by split; [apply/set0P | exists 0].
case: (inf_adherent a'x_gt0 hE) => y drxy.
rewrite infeq add0r ltrBrDl => xya'.
case: drxy => xyE y0.
suff : x+y \notin E by rewrite xyE.
rewrite -in_setC inE. apply: aE => /=.
by rewrite in_itv /= xya' (le_trans ax) // ler_wpDr // ltW.
Qed.
End distance.

Lemma sorgenfrey_line_perfectly_normal_space : 
  perfectly_normal_space R sorgenfrey.
Proof.
move=> E cE.
exists (sdist E).
split.
  exact: continuous_sdist.
exact: zeroset_sdist.
Qed.

End Sorgenfrey_line.
