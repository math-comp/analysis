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

Lemma open_separated (T : topologicalType) (A B : set T) :
  open A -> open B -> (A `&` B = set0 -> separated A B).
Proof.
move=> oA oB.
apply:contraPP.
rewrite /separated.
rewrite not_andP.
case.
  contra.
  rewrite disjoints_subset => AsubnB.
  rewrite disjoints_subset.
  move:(closure_subset AsubnB).
  have:closed (~` B).
    by apply:open_closedC.
  move/closure_id => csB. 
  by rewrite -csB.
contra.
rewrite setIC.
rewrite disjoints_subset => BsubnA.
rewrite setIC disjoints_subset.
move:(closure_subset BsubnA).
have:closed (~` A).
  by apply:open_closedC.
move/closure_id => csA.
by rewrite -csA.
Qed.

Lemma separated_sub (T : topologicalType)(A B C : set T) :
  separated A B -> C `<=` B -> separated A C.
Proof.
rewrite /separated.
case.
move=> cAB0 AcB0. 
move=> CB.
split.
  rewrite setIC disjoints_subset.
  apply (subset_trans CB).
  by rewrite -disjoints_subset setIC.
rewrite setIC disjoints_subset.
apply (subset_trans (closure_subset CB)).
by rewrite -disjoints_subset setIC.
Qed.

Check sorgenfrey.

Lemma sorgenfrey_line_totally_disconnected : totally_disconnected [set: sorgenfrey].
Proof.
rewrite /totally_disconnected.
move=> x Rx.
(*rewrite /setT /set1.*)
rewrite /connected_component.
have:forall C : set sorgenfrey, C x -> connected C -> C = [set x].
  move=> C Cx.
  apply:contraPP.
  move=> Cneqsetx.
  have[y [yx Cy]]:(exists y, y != x /\ C y).
    apply/not_existsP.
    move:Cneqsetx.
    contra.
    move=> H.
    apply:funext.
    move=> y.
    move:(H y).
    rewrite not_andE.
    move=>Hy.
    rewrite propeqP /=.
    split.
      case:Hy => //.
      move/negP.
      rewrite negbK.
      by move/eqP.
    by move->.
  wlog xy : x y yx Cx Cy {Rx Cneqsetx} / x < y.
    move:(yx). 
    rewrite neq_lt.
    case/orP.
      move=> ylx H.
      apply:(H y x) => //.
      by rewrite eq_sym.        
    move=> xly H.
    by apply:(H x y) => //.
  rewrite connectedPn.
  exists (fun b => if b then C `&` `]-oo, y[ else C `&` `[ y, +oo[).
  split.
  - case.
      exists x.
      by split.
    exists y.
    split => //=.
    by rewrite in_itv /= lexx.
  - rewrite -setIUr.
    move:(setCitv `[y, y[%R ).
    rewrite /=.
    rewrite setUC => <-.
    by rewrite set_itvco0 setC0 setIT.
  apply: (separated_sub (B := `]-oo, y[)); last by apply: subIsetr.
  rewrite separatedC. 
  apply: (separated_sub (B := `[y, +oo[)); last by apply: subIsetr.
  apply: open_separated. 
  - have -> : `]-oo, y[ = \bigcup_( z in `]-oo, y[ ) `[z, y[.
      apply/seteqP.
      split => w Hw /=.
        exists w => //=.
        move: Hw.
        by rewrite /= !in_itv /= lexx => ->.
      by case: Hw => t /= /[!in_itv] /= _ /andP [].
    apply: bigcup_open => w ? /=.
    rewrite /open /=.
    exists [set (w, y)] => //.
    by rewrite bigcup_set1.
  - have -> : `[y, +oo[ = \bigcup_( z in `[y, +oo[ ) `[y, z[.
      apply/seteqP.
      split => w Hw /=.
        exists (w+1) => //=.
          move: Hw.
          rewrite /= !in_itv /=.
          rewrite andbC /= andbC /=.
          by apply/(ler_wpDr ler01).
        rewrite in_itv /=.
        apply/andP.
        split.
          move:Hw. 
          by rewrite /= in_itv /= andbC.
        apply:ltr_pwDr; last by [].
        by apply: ltr01.
      rewrite in_itv /= andbC /=.
      by case: Hw => t /= /[!in_itv] /= _ /andP [].
    apply: bigcup_open => w ? /=.
    rewrite /open /=.
    exists [set (y, w)] => //.
    by rewrite bigcup_set1.
  apply/seteqP.
  split => w //=.
  by rewrite !in_itv /= leNgt => -[] ->.
move=> H.
rewrite ( _ : [set C | _ ] = [set [set x]]). 
  by rewrite bigcup_set1.
apply/seteqP.
split => C //=.
  case=>*.
  exact: H.
move->.
split => //.
exact: connected1.
Qed.


Definition sdist (E : set sorgenfrey) (x : sorgenfrey) :=
  let xl := inf [set y | x - y \in E /\ 0 < y] in
  let xr := inf [set y | x + y \in E /\ 0 <= y] in
  if x - xl \in E then Order.min xl xr else Order.min 1 xr.


End Sorgenfrey_line.
