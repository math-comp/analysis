(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure order_topology compact.

(**md**************************************************************************)
(* # Topology for boolean numbers                                             *)
(*          pseudoMetric_bool == an alias for bool equipped with the          *)
(*                               discrete pseudometric                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build bool
  principal_filter_proper discrete_sing discrete_nbhs.

Lemma discrete_bool : discrete_space bool.
Proof. by []. Qed.

Lemma bool_compact : compact [set: bool].
Proof. by rewrite setT_bool; apply/compactU; exact: compact_set1. Qed.

Section bool_ord_topology.
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Local Lemma bool_nbhs_itv (b : bool) :
  nbhs b = filter_from
    (fun i => itv_open_ends i /\ b \in i)
    (fun i => [set` i]).
Proof.
rewrite discrete_bool eqEsubset; split=> U; first last.
  by case => V [_ Vb] VU; apply/principal_filterP/VU; apply: Vb.
move/principal_filterP; case: b.
  move=> Ut; exists `]false, +oo[; first split => //; first by left.
  by move=> r /=; rewrite in_itv /=; case: r.
move=> Ut; exists `]-oo, true[; first split => //; first by left.
by move=> r /=; rewrite in_itv /=; case: r.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ bool bool_nbhs_itv.
End bool_ord_topology.

Lemma discrete_bool_compact : compact [set: discrete_topology discrete_bool].
Proof. by rewrite setT_bool; apply/compactU; exact: compact_set1. Qed.

Definition pseudoMetric_bool {R : realType} :=
  [the pseudoMetricType R of discrete_topology discrete_bool : Type].

#[global] Hint Resolve discrete_bool : core.
