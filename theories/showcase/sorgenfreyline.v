From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
From mathcomp Require Import wochoice contra.
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


Definition sdist (E : set sorgenfrey) (x : sorgenfrey) : R :=
  let dl := [set y | x - y \in E /\ 0 <= y] in
  let dr := [set y | x + y \in E /\ 0 < y] in
  Order.min (if x - inf dl \in E then inf dl else 1)
            (if dr == set0 then 1 else inf dr).

From mathcomp Require Import topology normedtype.
Let Rtopo := num_topology.numFieldTopology.Real_sort__canonical__topology_structure_Topological R.

From mathcomp Require Import ring.

Lemma abs_subr_min (x y t u : R) :
  `|Num.min x y - Num.min t u| <= Num.max `|x - t| `|y - u|.
Proof.
wlog xy: x y t u / x <= y.
  move=> H.
  case/boolP: (x <= y) => [/H //| xy].
  by rewrite minC (minC t) maxC H // ltW // ltNge.
case: (lerP x y); [move=> _ | by rewrite ltNge xy].
have cxtyu : `|x-t| >=< `|y-u| by rewrite comparablerE num_real.
case: (lerP t u) => tu; rewrite comparable_le_max //.
  by rewrite lexx.
case: (lerP x u) => xu.
  case: (lerP x t) => xt. by rewrite lerD2r ltW.
  by rewrite leNgt (lt_trans tu xt) in xu.
case: (lerP u y) => uy. by rewrite lerD2r xy orbT.
by rewrite leNgt (lt_trans uy xu) in xy.
Qed.

Lemma le_inf_n0 (E : set R) (x : R) : x \in E -> inf E != 0 -> inf E <= x.
Proof.
move=> xE infE0.
rewrite -(inf1 x) le_inf //.
- rewrite image_set1 => z /= ->.
  apply/downP; exists (-x) => //.
  by exists x => //; rewrite -inE.
- by exists x.
- move: infE0.
  by apply: contraNP => /inf_out ->.
Qed.

Lemma inf_ge0 (E : set R) : {in E, forall x : R, x >= 0} -> inf E >= 0.
Proof.
move=> E_ge0.
case/boolP: (E == set0) => [/eqP -> | /set0P E0].
  by rewrite inf0.
apply: lb_le_inf => // x Ex.
by apply: E_ge0; rewrite inE.
Qed.

Lemma continuous_sdist E :
  closed E -> forall x, @continuous_at sorgenfrey Rtopo x (sdist E).
Proof.
move=> CE x N.
rewrite -(@filter_from_ballE R (GRing_regular__canonical__pseudometric_structure_PseudoMetric R)).
case => eps /= eps0 epsN.
pose xepsE := [set y | x + y \in E /\ 0 < y < eps].
pose eps' := xget eps xepsE.
exists (`[x,x+eps'[); split => //=.
- exists [set (x,x+eps')].
    by move=> i /= ->.
  by rewrite bigcup_set1.
- rewrite in_itv /= lexx ltrDl /eps' /=.
  case: (xgetP eps xepsE) => //.
  move=> y ->.
  by rewrite /xepsE /= => -[] _ /andP[].
rewrite -image_sub.
move=> y /= [] z.
rewrite in_itv /= => /andP[xz zx] <- {y}.
apply: epsN.
rewrite /ball /=.
rewrite /sdist.
have [<-|xz'] := eqVneq x z.
  by rewrite subrr normr0.
have {xz xz'} xz: x < z by rewrite lt_neqAle xz'.
set dxl := [set y | x - y \in E /\ 0 <= y].
set dxr := [set y | x + y \in E /\ 0 < y].
set xr : R := if dxr == set0 then _ else _.
set dzl := [set y | z - y \in E /\ 0 <= y].
set dzr := [set y | z + y \in E /\ 0 < y].
set zr : R := if dzr == set0 then _ else _.
case/boolP: (xepsE == set0).
  move/eqP => xepsE0.
  have Heps' : eps' = eps.
    rewrite /eps'.
    case: (xgetP eps xepsE) => //.
    move=> y ->.
    by rewrite xepsE0.
  rewrite {}Heps' {eps'} in zx.
  have znE : z \notin E.
    apply/negP => zE.
    suff : xepsE (z-x) by rewrite xepsE0.
    by rewrite /xepsE /= addrA (addrC x) addrK zE ltrBrDl addr0 ltrBlDl xz zx.
  have Hr : `|Num.min 1 xr - Num.min 1 zr| < eps.
    rewrite /xr /zr.
    case/boolP: (dxr == set0) => dxr0.
      suff -> : dzr == set0 by rewrite subrr normr0.
      apply/notP => /negP/set0P [] y [] Hy y0.
      suff : y + z - x \in dxr by rewrite (eqP dxr0) inE.
      rewrite inE /dxr /= addrA (addrC x) addrK addrC Hy.
      by rewrite subr_gt0 ltr_wpDr // ltW.
    rewrite ifF. rewrite (le_lt_trans (abs_subr_min _ _ _ _)) //. admit.
    apply/negbTE/set0P.
    case/set0P: dxr0 => y [] Hy y0.
    exists (y + x - z).
    rewrite /dzr /= addrA (addrC z) addrK addrC Hy.
    rewrite subr_gt0 ltNge.
    split => //; apply/negP => xyz.
    suff : xepsE y by rewrite xepsE0.
    by rewrite /xepsE /= Hy y0 -(ltrD2l x) (le_lt_trans xyz).
  have [dxl0|] := eqVneq dxl set0.
    rewrite dxl0 inf0 subr0.
    case: ifPn => xinE.
      suff : 0 \in dxl by rewrite inE dxl0.
      by rewrite inE /dxl /= subr0.
    have dzl0 : dzl = set0.
      apply/notP => /eqP/set0P [t] [] ztE t0.
      case/boolP: (z - t > x) => ztx.
        suff : z-t-x \in xepsE by rewrite xepsE0 inE.
        rewrite inE /xepsE /= addrA (addrC x) addrK ztE.
        rewrite ltrBrDl addr0 ztx ltrBlDl.
        by rewrite -(subr0 (x+eps)) ltr_leB.
      rewrite -leNgt in ztx.
      suff : x - (z-t) \in dxl by rewrite dxl0 inE.
      rewrite inE /dxl /=.
      by rewrite opprD addrA addrC subrr addr0 opprK ztE lerBrDl addr0.
    by rewrite dzl0 inf0 subr0 (negbTE znE).
  case/set0P => w Hw.
  have xzl : x - inf dxl = z - inf dzl.
    rewrite /dzl.
    rewrite -{1}(addrNK x z) (addrC (z-x)) -(opprB x) -(inf1 (x-z)).
    rewrite -addrA -opprD -inf_sumE; first last.
    - split; last by exists 0 => t [].
      exists (w+z-x) => //=.
      rewrite -addrA opprD !addrA (addrC z) addrKA opprK addrC.
      case: Hw => -> w0.
      by rewrite lerBrDl addr0 ler_wpDl // (ltW xz).
    - exact: has_inf1.
    congr (x - inf _); symmetry.
    apply/seteqP; split => t /=.
      case=> u -> [{}u] [wE w0] <-{t}.
      rewrite /dxl /= !opprD opprK !addrA subrr add0r wE.
      have : z - u <= x.
        rewrite -subr_le0 leNgt.
        apply/negP => zux.
        suff : xepsE (z - u - x) by rewrite xepsE0.
        rewrite /xepsE /=  (addrC x) -addrA (addrC _ x) subrr addr0 wE.
        by rewrite zux ltrBlDr (addrC _ x) (le_lt_trans _ zx) // gerBl.
      by rewrite -addrA (addrC (-z)) -(opprB z) lerBrDl addr0.
    case=> xtE t0.
    exists (x-z) => //.
    exists (t+z-x); last by ring.
    rewrite (_ : z - _ = x - t); last by ring.
    by rewrite xtE -addrA addr_ge0 // subr_ge0 ltW.
  rewrite -xzl.
  case: ifPn => xlE //.
  rewrite (le_lt_trans (abs_subr_min _ _ _ _)) //. admit.
move/set0P/xgetPex => /(_ eps).
rewrite -/eps' => -[] eps'E Heps'.
have eps'l : forall t, x <= t < x + eps' ->
        let dr := [set y | t + y \in E /\ 0 < y] in
        0 <= (if dr == set0 then 1 else inf dr) < eps.
  move=> t Ht /=.
  set dr := [set y | t + y \in E /\ 0 < y].
  rewrite ifF; last first.
    apply/negbTE/set0P.
    exists (x+eps'-t).
    rewrite /dr /= (addrC _ (-t)) addrA subrr add0r eps'E.
    rewrite addrC subr_gt0 //; by case/andP: Ht.
  rewrite inf_ge0; last by move=> u; rewrite inE => -[] _ /ltW.
  case/boolP: (dr == set0) => [/eqP ->|/set0P dr0].
    by rewrite inf0 eps0.
  have [-> // | infdr0] := eqVneq (inf dr) 0.
  apply (@le_lt_trans _ _ (eps'+x-t)).
    apply: le_inf_n0 => //.
    rewrite inE /dr /= (addrC _ (-t)) addrA subrr add0r addrC eps'E.
    rewrite addrC subr_gt0 //; by case/andP: Ht.
  apply: (@le_lt_trans _ _ eps').
    rewrite -addrA gerDl lerBlDl addr0; by case/andP: Ht.
  by case/andP: Heps'.
set dr := Num.min _ _.
set dr' := Num.min _ _.
have Hdr : 0 <= dr < eps.
  rewrite /dr.
  rewrite comparable_le_min; last first.
    apply:real_leVge; apply:num_real; apply:num_real.
  rewrite comparable_gt_min; last first.
    apply:real_leVge; apply:num_real; apply:num_real.
  rewrite fun_if inf_ge0; last by move=> u; rewrite inE => -[].
  rewrite ler01 if_same /=.
  have : x <= x < x + eps'.
    by rewrite lexx ltrDl; case/andP: Heps'.
  move/eps'l => /andP[] -> ->.
  by rewrite orbT.
have Hdr' : 0 <= dr' < eps.
  rewrite /dr'.
  rewrite comparable_le_min; last first.
    apply:real_leVge; apply:num_real; apply:num_real.
  rewrite comparable_gt_min; last first.
    apply:real_leVge; apply:num_real; apply:num_real.
  rewrite fun_if inf_ge0; last by move=> u; rewrite inE => -[].
  rewrite ler01 if_same /=.
  have : x <= z < x + eps'.
    by rewrite zx ltW // xz.
  move/eps'l => /andP[] -> ->.
  by rewrite orbT.
rewrite -maxrN comparable_gt_max; last exact/real_leVge/num_real/num_real.
case/andP: Hdr => Hdr1 Hdr2.
case/andP: Hdr' => Hdr1' Hdr2'.
rewrite (le_lt_trans _ Hdr2) ?gerBl //.
by rewrite (le_lt_trans _ Hdr2') // opprD opprK addrC gerBl.
Abort.


End Sorgenfrey_line.
