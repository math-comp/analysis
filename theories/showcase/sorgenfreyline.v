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


Definition sdist (E : set sorgenfrey) (x : sorgenfrey) :=
  let xl := inf [set y | x - y \in E /\ 0 < y] in
  let xr := inf [set y | x + y \in E /\ 0 <= y] in
  if x - xl \in E then Order.min xl xr else Order.min 1 xr.


End Sorgenfrey_line.
