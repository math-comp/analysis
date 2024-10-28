(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure compact subspace_topology.

(**md**************************************************************************)
(* # Sum topology                                                             *)
(*  This file equips the dependent sum {i & X i} with its standard topology   *)
(*                                                                            *)
(* ```                                                                        *)
(*         sum_nbhs x == the neighborhoods of the standard topology on the    *)
(*                       dependent sum type {i & X i}                         *)
(* ```                                                                        *)
(******************************************************************************)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sum_topology.
Context {I : choiceType} {X : I -> topologicalType}.

Definition sum_nbhs (x : {i & X i}) : set_system {i & X i} :=
  existT _ _ @ nbhs (projT2 x).

Lemma sum_nbhsE (i : I) (x : X i) :
  sum_nbhs (existT _ i x) = (existT _ _) @ (nbhs x).
Proof. by done. Qed.

HB.instance Definition _ := hasNbhs.Build {i & X i} sum_nbhs.

Local Lemma sum_nbhs_proper x : ProperFilter (sum_nbhs x).
Proof. by case: x => i xi; exact: fmap_proper_filter. Qed.

Local Lemma sum_nbhs_singleton x A : sum_nbhs x A -> A x.
Proof. by case: x => ? ? /=; exact: nbhs_singleton. Qed.

Local Lemma sum_nbhs_nbhs x A: sum_nbhs x A -> sum_nbhs x (sum_nbhs^~ A).
Proof.
case: x => i Xi /=.
rewrite sum_nbhsE /= nbhsE /= => -[W [oW Wz WlA]].
by exists W => // x /= Wx; exact/(filterS WlA)/open_nbhs_nbhs.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build {i & X i}
  sum_nbhs_proper sum_nbhs_singleton sum_nbhs_nbhs.

Lemma existT_continuous (i : I) : continuous (existT X i).
Proof. by move=> ? ?. Qed.

Lemma existT_open_map (i : I) (A : set (X i)) : open A -> open (existT X i @` A).
Proof.
move=> oA; rewrite openE /interior /= => iXi [x Ax <-].
rewrite /nbhs /= sum_nbhsE /= nbhs_simpl /=.
move: oA; rewrite openE => /(_ _ Ax); apply: filterS.
by move=> z Az; exists z.
Qed.

Lemma existT_nbhs (i : I) (x : X i) (U : set (X i)) :
  nbhs x U -> nbhs (existT _ i x) (existT _ i @` U).
Proof. exact/filterS/preimage_image. Qed.

Lemma sum_openP (U : set {i & X i}) :
  open U <-> forall i, open (existT _ i @^-1` U).
Proof.
split=> [oU i|?]; first by apply: open_comp=> // y _; exact: existT_continuous.
rewrite openE => -[i x Uxi].
by rewrite /interior /nbhs/= sum_nbhsE; exact: open_nbhs_nbhs.
Qed.

Lemma sum_continuous {Z : topologicalType} (f : forall i, X i -> Z) :
  (forall i, continuous (f i)) -> continuous (sum_fun f).
Proof. by move=> ctsf [] i x U nU; apply: existT_continuous; exact: ctsf. Qed.

Lemma sum_setUE : [set: {i & X i}] = \bigcup_i (existT _ i @` [set: X i]).
Proof. by rewrite eqEsubset; split => [[i x] _|[]//]; exists i. Qed.

Lemma sum_compact : finite_set [set: I] -> (forall i, compact [set: X i]) ->
  compact [set: {i & X i}].
Proof.
move=> fsetI cptX; rewrite sum_setUE -fsbig_setU//.
apply: big_rec; first exact: compact0.
move=> i ? _ cptx; apply: compactU => //.
apply: continuous_compact; last exact: cptX.
exact/continuous_subspaceT/existT_continuous.
Qed.

End sum_topology.
