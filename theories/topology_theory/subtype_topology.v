From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology_structure uniform_structure compact.
From mathcomp Require Import pseudometric_structure connected weak_topology.
From mathcomp Require Import product_topology subspace_topology.

(**md**************************************************************************)
(* # Subtypes of topological spaces                                           *)
(* We have two distinct ways of building topologies as subsets of a           *)
(* topological space `X`. One is the `subspace topology`, which is defined in *)
(* `subspace_topology.v`. It builds a topology on X which 'isolates' a set A. *)
(* The other, defined in this file, defines a topology on the sigma type      *)
(* `set_type` in the weak topology by the inclusion. Note `subspace A` has    *)
(* the advantage that it preserves all the algebraic structure on X, but only *)
(* the local behavior A (in particular, continuity). On the other hand        *)
(* `set_type A` has the right global properties you'd expect for the subset   *)
(* topology. But you can't easily add two elements of `set_val [0, 1]`.       *)
(* Note the implicit coercion from sets to `set_val` from `classical_sets.v`. *)
(*                                                                            *)
(* This file provides `set_type` with a topology, and some theory.            *)
(* ```                                                                        *)
(*           sigT_of_setX == commutes `set_type` and product topologies       *)
(*           setX_of_sigT == commutes product and `set_type` topologies       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.instance Definition _ {X : topologicalType} (A : set X) :=
  Topological.copy (set_type A) (weak_topology set_val).

HB.instance Definition _ {X : uniformType} (A : set X) :=
  Uniform.copy (A : Type) (@weak_topology (A : Type) X set_val).

HB.instance Definition _ {R : realType} {X : pseudoMetricType R} (A : set X) :=
  PseudoMetric.copy (A : Type) (@weak_topology (A : Type) X set_val).

Section subspace_sig.
Context {X : topologicalType} (A : set X).

Lemma subspace_subtypeP (x : A) (U : set A) :
  nbhs x U <-> nbhs (set_val x : subspace A) (set_val @` U).
Proof.
rewrite /nbhs /= -nbhs_subspace_in //; first last.
  by case: x; rewrite set_valE => //= ? /set_mem.
split.
  case=> _ /= [] [W oW <- /= Wx sWU]; move: oW; rewrite openE /= /interior.
  move=> /(_ _ Wx); apply: filter_app; apply: nearW => w /= Ww /mem_set Aw.
  by exists (@exist _ _ w Aw) => //; exact: sWU.
rewrite withinE => -[V + UAVA]; rewrite nbhsE => -[V' [oV' V'x V'V]].
exists (sval @^-1` V'); split => //=; first by exists V'.
move=> w /= /V'V Vsw; have : (V `&` A) (\val w).
  by split => //; case: w Vsw => //= ? /set_mem.
by rewrite -UAVA => -[[v ? /eq_sig_hprop] <-].
Qed.

Lemma subspace_sigL_continuousP {Y : topologicalType} (f : X -> Y) :
  {within A, continuous f} <-> continuous (sigL A f).
Proof.
split.
  have /continuous_subspaceT/subspaceT_continuous :=
    @weak_continuous A X set_val.
  move=> svf ctsf; apply/continuous_subspace_setT => x.
  apply: (@continuous_comp (subspace _) (subspace A)); last exact: ctsf.
  by move=> U nfU; exact: svf.
rewrite continuous_subspace_in => + x Ax U nfxU.
move=> /(_ (@exist _ _ x Ax) U) /= []; first exact: nfxU.
move=> _ [/= [W + <- /=]] Wx svWU; rewrite nbhs_simpl/=.
rewrite /nbhs /= -nbhs_subspace_in; last exact/set_mem.
rewrite openE /= /interior=> /(_ _ Wx); rewrite {1}set_valE/=.
apply: filter_app; apply: nearW => w Ww /= /mem_set Aw.
by have /= := svWU (@exist _ _ w Aw); rewrite ?set_valE /=; exact.
Qed.

Lemma subspace_valL_continuousP' {Y : topologicalType} (y : Y) (f : A -> Y) :
  {within A, continuous (valL_ y f)} <-> continuous f.
Proof.
rewrite -{2}[f](@valLK _ _ y A); split=> [/subspace_sigL_continuousP//|cf].
exact/subspace_sigL_continuousP.
Qed.

Lemma subspace_valL_continuousP {Y : ptopologicalType} (f : A -> Y) :
  {within A, continuous (valL f)} <-> continuous f.
Proof. exact: (@subspace_valL_continuousP' _ point). Qed.

End subspace_sig.

Section subtype_setX.
Context {X Y : topologicalType} (A : set X) (B : set Y).

Program Definition setX_of_sigT (ab : A `*` B) : (A * B)%type :=
  (@exist _ _ ab.1 _, @exist _ _ ab.2 _).
Next Obligation. by case; case => a b /= /set_mem [] ? ?; exact/mem_set. Qed.
Next Obligation. by case; case => a b /= /set_mem [] ? ?; exact/mem_set. Qed.

Program Definition sigT_of_setX (ab : (A * B)%type) : A `*` B :=
  (@exist _ _ (\val ab.1, \val ab.2) _).
Next Obligation.
by move=> [[x/= /set_mem Ax] [y/= /set_mem By]]; exact/mem_set.
Qed.

Lemma sigT_of_setXK : cancel sigT_of_setX setX_of_sigT.
Proof. by move=> [[x ?] [y ?]]; congr (( _, _)); exact: eq_sig_hprop. Qed.

Lemma setX_of_sigTK : cancel setX_of_sigT sigT_of_setX.
Proof. by move=> [[a b] ?]; exact: eq_sig_hprop. Qed.

Lemma setX_of_sigT_continuous : continuous setX_of_sigT.
Proof.
move=> [[x y] p] U [/= [P Q]] /= [nxP nyQ] pqU.
case: nxP => _ [/= [] P' oP' <- /=]; rewrite set_valE /= => P'x P'P.
case: nyQ => _ [/= [] Q' oQ' <- /=]; rewrite set_valE /= => Q'x Q'Q.
pose PQ : set (A `*` B) := \val @^-1` (P' `*` Q').
exists PQ; split => //=.
  exists (P' `*` Q') => //; rewrite openE => -[a b /=] [P'a Q'b].
  exists (P', Q') => //; split.
  - by move: oP'; rewrite openE; exact.
  - by move: oQ'; rewrite openE; exact.
by move=> [[a b]/= abAB [P'a Q'b]]; apply/pqU; split; [exact: P'P|exact: Q'Q].
Qed.

Lemma sigT_of_setX_continuous : continuous sigT_of_setX.
Proof.
move=> [[x Ax] [y By]] U [? [] [W + <-] /=]; rewrite set_valE/=.
rewrite openE /= => /[apply] [][][] P Q /=; rewrite (nbhsE x) (nbhsE y) => -[].
move=> [P' [oP' P'x P'P]] [Q' [oQ' Q'y Q'Q]] PQW WU.
exists (val @^-1` P', \val @^-1` Q') => /=; first split.
- by exists (\val@^-1` P'); split => //=; exists P'.
- by exists (\val @^-1` Q'); split => //=; exists Q'.
- by move=> [[p Ap] [q Bq]]/= [P'p Q'q]; apply/WU/PQW;
    split; [exact: P'P|exact: Q'Q].
Qed.

End subtype_setX.
