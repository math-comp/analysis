(* mathcomp analysis (c) 2024 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals topology.
From mathcomp Require Import separation_axioms function_spaces.

(**md**************************************************************************)
(* # wedge sum for sigT                                                       *)
(* A foundational construction for homotopy theory. It glues a dependent sum  *)
(* at a single point. It's classicaly used in the proof that every free group *)
(* is a fundamental group of some space. We also will use it as part of our   *)
(* construction of paths and path concatenation.                              *)
(* ```                                                                        *)
(*    wedge_rel p0 x y == x and y are equal, or they are (p0 i) and           *)
(*                        (p0 j) for some i and j                             *)
(*            wedge p0 == the quotient of {i : X i} along `wedge_rel p0`      *)
(*        wedge_lift i == the lifting of elements of (X i) into the wedge     *)
(*           pwedge p0 == the wedge of ptopologicalTypes at their designated  *)
(*                        point                                               *)
(*         wedge_fun f == lifts a family of functions on each component into  *)
(*                        a function on the wedge, when they all agree at the *)
(*                        wedge point                                         *)
(*          wedge_prod == the mapping from the wedge as a quotient of sums to *)
(*                        the wedge as a subspace of the product topology.    *)
(*                        It's an embedding when the index is finite.         *)
(* bpwedge_shared_pt b == the shared point in the bpwedge. Either zero or one *)
(*                        depending on `b`.                                   *)
(*             bpwedge == wedge of two bipointed spaces gluing zero to one    *)
(*        bpwedge_lift == wedge_lift specialized to the bipointed wedge       *)
(* ```                                                                        *)
(*                                                                            *)
(* The type `wedge p0` is endowed with the structures of:                     *)
(* - topology via `quotient_topology`                                         *)
(* - quotient                                                                 *)
(*                                                                            *)
(* The type `pwedge` is endowed with the structures of:                       *)
(* - topology via `quotient_topology`                                         *)
(* - quotient                                                                 *)
(* - pointed                                                                  *)
(*                                                                            *)
(* The type `bpwedge` is endowed with the structures of:                      *)
(* - topology via `quotient_topology`                                         *)
(* - quotient                                                                 *)
(* - bipointed                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section wedge.
Context {I : choiceType} (X : I -> topologicalType) (p0 : forall i, X i).
Implicit Types i : I.

Let wedge_rel' (a b : {i & X i}) :=
  (a == b) || ((projT2 a == p0 _) && (projT2 b == p0 _)).

Local Lemma wedge_rel_refl : reflexive wedge_rel'.
Proof. by move=> ?; rewrite /wedge_rel' eqxx. Qed.

Local Lemma wedge_rel_sym : symmetric wedge_rel'.
Proof.
by move=> a b; apply/is_true_inj/propext; rewrite /wedge_rel'; split;
  rewrite (eq_sym b) andbC.
Qed.

Local Lemma wedge_rel_trans : transitive wedge_rel'.
Proof.
move=> a b c /predU1P[-> //|] + /predU1P[<- //|]; rewrite /wedge_rel'.
by move=> /andP[/eqP -> /eqP <-] /andP[_ /eqP <-]; rewrite !eqxx orbC.
Qed.

Definition wedge_rel := EquivRel _ wedge_rel_refl wedge_rel_sym wedge_rel_trans.
Global Opaque wedge_rel.

Definition wedge := {eq_quot wedge_rel}.
Definition wedge_lift i : X i -> wedge := \pi_wedge \o existT X i.

HB.instance Definition _ := Topological.copy wedge (quotient_topology wedge).
HB.instance Definition _ := Quotient.on wedge.
Global Opaque wedge.

Lemma wedge_lift_continuous i : continuous (@wedge_lift i).
Proof. by move=> ?; apply: continuous_comp => //; exact: pi_continuous. Qed.

HB.instance Definition _ i :=
  @isContinuous.Build _ _ (@wedge_lift i) (@wedge_lift_continuous i).

Lemma wedge_lift_nbhs i (x : X i) :
  closed [set p0 i] -> x != p0 _ -> @wedge_lift i @ x = nbhs (@wedge_lift _ x).
Proof.
move=> clx0 xNx0; rewrite eqEsubset; split => U; first last.
  by move=> ?; exact: wedge_lift_continuous.
rewrite ?nbhsE /= => -[V [oV Vx VU]].
exists (@wedge_lift i @` (V `&` ~` [set p0 i])); first last.
  by move=> ? /= [l] [Vl lx] <-; exact: VU.
split; last by exists x => //; split => //=; exact/eqP.
rewrite /open /= /quotient_open /wedge_lift /=.
suff -> : \pi_wedge @^-1` (@wedge_lift i @` (V `&` ~`[set p0 i])) =
          existT X i @` (V `&` ~` [set p0 i]).
  by apply: existT_open_map; apply: openI => //; exact: closed_openC.
rewrite eqEsubset; split => t /= [l [Vl] lNx0]; last by move=> <-; exists l.
by case/eqmodP/predU1P => [<-|/andP [/eqP]//]; exists l.
Qed.

Lemma wedge_liftE i (x : X i) j (y : X j) :
  wedge_lift (p0 j) = wedge_lift (p0 i).
Proof. by apply/eqmodP/orP; right; rewrite !eqxx. Qed.

Lemma wedge_openP (U : set wedge) :
  open U <-> forall i, open (@wedge_lift i @^-1` U).
Proof.
split=> [oU i|oiU].
  by apply: open_comp => // x _; exact: wedge_lift_continuous.
have : open (\bigcup_i (@wedge_lift i @` (@wedge_lift i @^-1` U))).
  apply/sigT_openP => i; move: (oiU i); congr open.
  rewrite eqEsubset; split => x /=.
    by move=> Ux; exists i => //; exists x.
  case=> j _ /= [] y Uy /eqmodP /predU1P[R|].
    have E : j = i by move: R; apply: existT_inj1.
    by rewrite -E in x R *; rewrite -(existT_inj2 R).
  case/andP => /eqP/= + /eqP -> => yj.
  by rewrite yj (wedge_liftE x y) in Uy.
congr open; rewrite eqEsubset; split => /= z.
  by case=> i _ /= [x] Ux <-.
move=> Uz; exists (projT1 (repr z)) => //=.
by exists (projT2 (repr z)); rewrite /wedge_lift /= surjective_existT reprK.
Qed.

Lemma wedge_point_nbhs i0 :
  nbhs (wedge_lift (p0 i0)) = \bigcap_i (@wedge_lift i @ p0 i).
Proof.
rewrite eqEsubset; split => //= U /=; rewrite ?nbhs_simpl.
  case=> V [/= oV Vp] VU j _; apply: wedge_lift_continuous.
  apply: (filterS VU); first exact: (@nbhs_filter wedge).
  apply: open_nbhs_nbhs; split => //.
  by rewrite (wedge_liftE (p0 i0)).
move=> Uj; have V_ : forall i, {V : set (X i) |
    [/\ open V, V (p0 i) & V `<=` @wedge_lift i @^-1` U]}.
  move=> j; apply: cid; have /Uj : [set: I] j by [].
  by rewrite nbhsE /= => -[B [? ? ?]]; exists B.
pose W := \bigcup_i (@wedge_lift i) @` (projT1 (V_ i)).
exists W; split.
- apply/wedge_openP => i; rewrite /W; have [+ Vpj _] := projT2 (V_ i).
  congr (_ _); rewrite eqEsubset; split => z; first by move=> Viz; exists i.
  case => j _ /= [] w /= svw /eqmodP /predU1P[[E]|].
    by rewrite E in w svw * => R; rewrite -(existT_inj2 R).
  by case/andP => /eqP /= _ /eqP ->.
- by exists i0 => //=; exists (p0 i0) => //; have [_ + _] := projT2 (V_ i0).
- by move=> ? [j _ [x ? <-]]; have [_ _] := projT2 (V_ j); exact.
Qed.

Variant wedge_nbhs_spec (z : wedge) : wedge -> set_system wedge -> Type :=
  | wedge_liftsPoint i0 :
      wedge_nbhs_spec z (wedge_lift (p0 i0)) (\bigcap_i (@wedge_lift i @ p0 i))
  | WedgeNotPoint (i : I) (x : X i) of (x != p0 i):
      wedge_nbhs_spec z (wedge_lift x) (@wedge_lift i @ x).

Lemma wedge_nbhs_specP (z : wedge) : (forall i, closed [set p0 i]) ->
  wedge_nbhs_spec z z (nbhs z).
Proof.
move=> clP; rewrite -[z](@reprK _ wedge); case: (repr z) => i x.
have [->|xpi] := eqVneq x (p0 i).
  by rewrite wedge_point_nbhs => /=; exact: wedge_liftsPoint.
by rewrite /= -wedge_lift_nbhs //; exact: WedgeNotPoint.
Qed.

Lemma wedgeTE : \bigcup_i (@wedge_lift i) @` setT = [set: wedge].
Proof.
rewrite -subTset => z _; rewrite -[z]reprK; exists (projT1 (repr z)) => //.
by exists (projT2 (repr z)) => //; rewrite /wedge_lift/= surjective_existT.
Qed.

Lemma wedge_compact : finite_set [set: I] -> (forall i, compact [set: X i]) ->
  compact [set: wedge].
Proof.
move=> fsetI cptX; rewrite -wedgeTE -fsbig_setU //; apply: big_ind.
- exact: compact0.
- by move=> ? ? ? ?; exact: compactU.
move=> i _; apply: continuous_compact; last exact: cptX.
exact/continuous_subspaceT/wedge_lift_continuous.
Qed.

Lemma wedge_connected : (forall i, connected [set: X i]) ->
  connected [set: wedge].
Proof.
move=> ctdX; rewrite -wedgeTE.
have [I0|/set0P[i0 Ii0]] := eqVneq [set: I] set0.
  rewrite [X in connected X](_ : _ = set0); first exact: connected0.
  by rewrite I0 bigcup_set0.
apply: bigcup_connected.
  exists (@wedge_lift i0 (p0 _)) => i Ii; exists (p0 i) => //.
  exact: wedge_liftE.
move=> i ? /=; apply: connected_continuous_connected => //.
exact/continuous_subspaceT/wedge_lift_continuous.
Qed.

Definition wedge_fun {Z : Type} (f : forall i, X i -> Z) : wedge -> Z :=
  sigT_fun f \o repr.

Lemma wedge_fun_continuous {Z : topologicalType} (f : forall i, X i -> Z) :
  (forall i, continuous (f i)) -> (forall i j, f i (p0 i) = f j (p0 j)) ->
  continuous (wedge_fun f).
Proof.
move=> cf fE; apply: repr_comp_continuous; first exact: sigT_continuous.
move=> a b /eqP/eqmodP /predU1P[-> //|/andP[/eqP + /eqP +]].
by rewrite /sigT_fun /= => -> ->; exact/eqP.
Qed.

Lemma wedge_lift_funE {Z : Type} (f : forall i, X i -> Z) i0 (a : X i0):
  (forall i j, f i (p0 i) = f j (p0 j)) -> wedge_fun f (wedge_lift a) = f i0 a.
Proof.
move=> fE.
rewrite /wedge_fun/= /sigT_fun /=; case: piP => z /= /eqmodP.
by move/predU1P => [<- //|/andP[/= /eqP -> /eqP ->]].
Qed.

Lemma wedge_fun_comp {Z1 Z2 : Type} (h : Z1 -> Z2) (f : forall i, X i -> Z1) :
  h \o wedge_fun f = wedge_fun (fun i => h \o f i).
Proof. exact/funext. Qed.

(* The wedge maps into the product
   \bigcup_i [x | x j = p0 j  when j != i]

   For the box topology, it's an embedding. But more practically,
   since the box and product agree when `I` is finite,
   we get that the finite wedge embeds into the finite product.
 *)
Section wedge_as_product.

Definition wedge_prod : wedge -> prod_topology X := wedge_fun (dfwith p0).

Lemma wedge_prod_pointE (i j : I) : dfwith p0 i (p0 i) = dfwith p0 j (p0 j).
Proof.
apply: functional_extensionality_dep => k /=.
by case: dfwithP => [|*]; case: dfwithP.
Qed.

Lemma wedge_prod_inj : injective wedge_prod.
Proof.
have dfwithp0 := wedge_prod_pointE.
move=> a b; rewrite -[a](@reprK _ wedge) -[b](@reprK _ wedge).
move Ea : (repr a)=> [i x]; move Eb : (repr b) => [j y].
rewrite /wedge_prod !wedge_lift_funE//= => dfij; apply/eqmodP/orP.
have [E|E /=] := eqVneq i j.
  rewrite -{}E in x y Ea Eb dfij *; left; apply/eqP; congr existT.
  have : dfwith p0 i x i = dfwith p0 i y i by rewrite dfij.
  by rewrite !dfwithin.
right; apply/andP; split; apply/eqP.
- have : dfwith p0 i x i = dfwith p0 j y i by rewrite dfij.
  by rewrite dfwithin => ->; rewrite dfwithout // eq_sym.
- have : dfwith p0 i x j = dfwith p0 j y j by rewrite dfij.
  by rewrite dfwithin => <-; rewrite dfwithout.
Qed.

Lemma wedge_prod_continuous : continuous wedge_prod.
Proof.
apply: wedge_fun_continuous; last exact: wedge_prod_pointE.
exact: dfwith_continuous.
Qed.

Lemma wedge_prod_open (x : wedge) (A : set wedge) :
  finite_set [set: I] ->
  (forall i, closed [set p0 i]) ->
  nbhs x A ->
  @nbhs _ (subspace (range wedge_prod)) (wedge_prod x) (wedge_prod @` A).
Proof.
move=> fsetI clI; case: wedge_nbhs_specP => [//|i0 bcA|i z zNp0 /= wNz].
  pose B_ i : set (subspace (range wedge_prod)) :=
    proj i @^-1` (@wedge_lift i @^-1` A).
  have /finite_fsetP[fI fIE] := fsetI.
  have /filterS : (\bigcap_(i in [set` fI]) B_ i) `&` range wedge_prod
      `<=` wedge_prod @` A.
    move=> _ [] /[swap] [] [z _] <- /= Bwz; exists z => //.
    have /Bwz : [set` fI] (projT1 (repr z)) by rewrite -fIE.
    congr (A _); rewrite /wedge_lift /= -[RHS]reprK.
    apply/eqmodP/orP; left; rewrite /proj /=.
    by rewrite /wedge_prod/= /wedge_fun /sigT_fun/= dfwithin surjective_existT.
  apply; apply/nbhs_subspace_ex; first by exists (wedge_lift (p0 i0)).
  exists (\bigcap_(i in [set` fI]) B_ i); last by rewrite -setIA setIid.
  apply: filter_bigI => i _; rewrite /B_; apply: proj_continuous.
  have /bcA : [set: I] i by [].
  congr (nbhs _ _).
  rewrite /proj /wedge_prod wedge_lift_funE; first by case: dfwithP.
  exact: wedge_prod_pointE.
rewrite [x in nbhs x _]/wedge_prod /= wedge_lift_funE; first last.
  exact: wedge_prod_pointE.
have : wedge_prod @` (A `&` (@wedge_lift i @` ~`[set p0 i]))
    `<=`  wedge_prod @` A.
  by move=> ? [] ? [] + /= [w] wpi => /[swap] <- Aw <-; exists (wedge_lift w).
move/filterS; apply; apply/nbhs_subspace_ex.
  exists (wedge_lift z) => //.
  by rewrite /wedge_prod wedge_lift_funE //; exact: wedge_prod_pointE.
exists (proj i @^-1` (@wedge_lift i @^-1`
    (A `&` (@wedge_lift i @` ~`[set p0 i])))).
  apply/ proj_continuous; rewrite /proj dfwithin preimage_setI; apply: filterI.
    exact: wNz.
  have /filterS := @preimage_image _ _ (@wedge_lift i) (~` [set p0 i]).
  by apply; apply: open_nbhs_nbhs; split; [exact: closed_openC|exact/eqP].
rewrite eqEsubset; split => // prodX; case => /[swap] [][] r _ <- /=.
  case => _ /[swap] /wedge_prod_inj -> [+ [e /[swap]]] => /[swap].
  move=> <- Awe eNpi; rewrite /proj /wedge_prod /=.
  rewrite wedge_lift_funE; last exact: wedge_prod_pointE.
  rewrite dfwithin; split => //; first by split => //; exists e.
  exists (wedge_lift e) => //.
  by rewrite wedge_lift_funE //; exact: wedge_prod_pointE.
case=> /[swap] [][y] yNpi E Ay.
have [riE|R] := eqVneq i (projT1 (repr r)); last first.
  apply: absurd yNpi.
  move: E; rewrite /proj/wedge_prod /wedge_fun /=/sigT_fun /=.
  rewrite dfwithout //; last by rewrite eq_sym.
  by case/eqmodP/orP => [/eqP E|/andP[/= /eqP//]]; exact: (existT_inj2 E).
split; exists (wedge_lift y); [by split; [rewrite E | exists y]| |by []|].
- congr wedge_prod; rewrite E.
  rewrite /proj /wedge_prod /wedge_fun /=/sigT_fun.
  by rewrite riE dfwithin /wedge_lift /= surjective_existT reprK.
- congr wedge_prod; rewrite E.
  rewrite /proj /wedge_prod /wedge_fun /=/sigT_fun.
  by rewrite riE dfwithin /wedge_lift /= surjective_existT reprK.
Qed.

End wedge_as_product.

Lemma wedge_hausdorff :
  (forall i, hausdorff_space (X i)) -> hausdorff_space wedge.
Proof.
move=> /hausdorff_product hf x y clxy.
apply/wedge_prod_inj/hf => U V /wedge_prod_continuous nU.
move=> /wedge_prod_continuous nV; have := clxy _ _ nU nV.
by case => z [/= ? ?]; exists (wedge_prod z).
Qed.

Lemma wedge_fun_joint_continuous (T R : topologicalType)
  (k : forall (x : I), T -> X x -> R):
  finite_set [set: I] ->
  (forall x, closed [set p0 x]) ->
  (forall t x y, k x t (p0 x) = k y t (p0 y)) ->
  (forall x, continuous (uncurry (k x))) ->
  continuous (uncurry (fun t => wedge_fun (k^~ t))).
Proof.
move=> Ifin clp0 kE kcts /= [t u] U.
case : (wedge_nbhs_specP u) => [//|i0 /=|].
  rewrite wedge_lift_funE // => Ukp0.
  have pq_ x : {PQ : set T * set (X x) | [/\ nbhs (p0 x) PQ.2,
      nbhs t PQ.1 & PQ.1 `*` PQ.2 `<=` uncurry (k x) @^-1` U]}.
    apply: cid.
    move: Ukp0; rewrite (@kE t i0 x).
    rewrite -[k x ]uncurryK /curry=> /kcts[[P Q] [Pt Qp0 pqU]].
    by exists (P, Q).
  have UPQ : nbhs (wedge_lift (p0 i0))
      (\bigcup_x (@wedge_lift x) @` (projT1 (pq_ x)).2).
    rewrite wedge_point_nbhs => r _.
    by case: (projT2 (pq_ r)) => /filterS + ? ?; apply => z /= ?; exists r.
  have /finite_fsetP [fI fIE] := Ifin.
  have UPt : nbhs t (\bigcap_(r in [set` fI]) (projT1 (pq_ r)).1).
    by apply: filter_bigI => x ?; case: (projT2 (pq_ x)).
  near_simpl => /=; near=> t1 t2 => /=.
  have [//|x _ [w /=] ? <-]:= near UPQ t2.
  rewrite wedge_lift_funE //.
  case: (projT2 (pq_ x)) => ? Npt /(_ (t1, w)) => /=; apply; split => //.
  by apply: (near UPt t1) => //; rewrite -fIE.
move=> x {}u uNp0 /=; rewrite wedge_lift_funE //= -[k x]uncurryK /curry.
move/kcts; rewrite nbhs_simpl /= => -[[P Q] [Pt Qu] PQU].
have wQu : nbhs (wedge_lift u) ((@wedge_lift x) @` Q).
  by rewrite -wedge_lift_nbhs //=; apply: filterS Qu => z; exists z.
near_simpl; near=> t1 t2 => /=.
have [//|l ? <-] := near wQu t2; rewrite wedge_lift_funE//.
by apply: (PQU (t1,l)); split => //; exact: (near Pt t1).
Unshelve. all: by end_near. Qed.

End wedge.

Section pwedge.
Context {I : pointedType} (X : I -> ptopologicalType).

Definition pwedge := wedge (fun i => @point (X i)).

Let pwedge_point : pwedge := wedge_lift _ (@point (X (@point I))).

HB.instance Definition _ := Topological.on pwedge.
HB.instance Definition _ := Quotient.on pwedge.
HB.instance Definition _ := isPointed.Build pwedge pwedge_point.

End pwedge.

Section bpwedge.
Context (X Y : bpTopologicalType).

Definition bpwedge_shared_pt b :=
  if b return (if b then X else Y) then @one X else @zero Y.
Local Notation bpwedge := (@wedge bool _ bpwedge_shared_pt).
Local Notation bpwedge_lift := (@wedge_lift bool _ bpwedge_shared_pt).

Local Lemma wedge_neq : @bpwedge_lift true zero != @bpwedge_lift false one.
Proof.
by apply/eqP => /eqmodP/predU1P[//|/andP[/= + _]]; exact/negP/zero_one_neq.
Qed.

Local Lemma bpwedgeE : @bpwedge_lift true one = @bpwedge_lift false zero .
Proof. by apply/eqmodP/orP; rewrite !eqxx; right. Qed.

HB.instance Definition _ := @isBiPointed.Build
  bpwedge (@bpwedge_lift true zero) (@bpwedge_lift false one) wedge_neq.
End bpwedge.

Notation bpwedge X Y := (@wedge bool _ (bpwedge_shared_pt X Y)).
Notation bpwedge_lift X Y := (@wedge_lift bool _ (bpwedge_shared_pt X Y)).
