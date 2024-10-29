(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure compact subspace_topology.

(**md**************************************************************************)
(* # sigT topology                                                            *)
(*  This file equips the type {i & X i} with its standard topology            *)
(*                                                                            *)
(* ```                                                                        *)
(*         sigT_nbhs x == the neighborhoods of the standard topology on the   *)
(*                        type {i & X i}                                      *)
(* ```                                                                        *)
(******************************************************************************)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sigT_topology.
Context {I : choiceType} {X : I -> topologicalType}.

Definition sigT_nbhs (x : {i & X i}) : set_system {i & X i} :=
  existT _ _ @ nbhs (projT2 x).

Lemma sigT_nbhsE (i : I) (x : X i) :
  sigT_nbhs (existT _ i x) = (existT _ _) @ (nbhs x).
Proof. by done. Qed.

HB.instance Definition _ := hasNbhs.Build {i & X i} sigT_nbhs.

Local Lemma sigT_nbhs_proper x : ProperFilter (sigT_nbhs x).
Proof. by case: x => i xi; exact: fmap_proper_filter. Qed.

Local Lemma sigT_nbhs_singleton x A : sigT_nbhs x A -> A x.
Proof. by case: x => ? ? /=; exact: nbhs_singleton. Qed.

Local Lemma sigT_nbhs_nbhs x A: sigT_nbhs x A -> sigT_nbhs x (sigT_nbhs^~ A).
Proof.
case: x => i Xi /=.
rewrite sigT_nbhsE /= nbhsE /= => -[W [oW Wz WlA]].
by exists W => // x /= Wx; exact/(filterS WlA)/open_nbhs_nbhs.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build {i & X i}
  sigT_nbhs_proper sigT_nbhs_singleton sigT_nbhs_nbhs.

Lemma existT_continuous (i : I) : continuous (existT X i).
Proof. by move=> ? ?. Qed.

Lemma existT_open_map (i : I) (A : set (X i)) : open A -> open (existT X i @` A).
Proof.
move=> oA; rewrite openE /interior /= => iXi [x Ax <-].
rewrite /nbhs /= sigT_nbhsE /= nbhs_simpl /=.
move: oA; rewrite openE => /(_ _ Ax); apply: filterS.
by move=> z Az; exists z.
Qed.

Lemma existT_nbhs (i : I) (x : X i) (U : set (X i)) :
  nbhs x U -> nbhs (existT _ i x) (existT _ i @` U).
Proof. exact/filterS/preimage_image. Qed.

Lemma sigT_openP (U : set {i & X i}) :
  open U <-> forall i, open (existT _ i @^-1` U).
Proof.
split=> [oU i|?]; first by apply: open_comp=> // y _; exact: existT_continuous.
rewrite openE => -[i x Uxi].
by rewrite /interior /nbhs/= sigT_nbhsE; exact: open_nbhs_nbhs.
Qed.

Lemma sigT_continuous {Z : topologicalType} (f : forall i, X i -> Z) :
  (forall i, continuous (f i)) -> continuous (sigT_fun f).
Proof. by move=> ctsf [] i x U nU; apply: existT_continuous; exact: ctsf. Qed.

Lemma sigT_setUE : [set: {i & X i}] = \bigcup_i (existT _ i @` [set: X i]).
Proof. by rewrite eqEsubset; split => [[i x] _|[]//]; exists i. Qed.

Lemma sigT_compact : finite_set [set: I] -> (forall i, compact [set: X i]) ->
  compact [set: {i & X i}].
Proof.
move=> fsetI cptX; rewrite sigT_setUE -fsbig_setU//.
apply: big_rec; first exact: compact0.
move=> i ? _ cptx; apply: compactU => //.
apply: continuous_compact; last exact: cptX.
exact/continuous_subspaceT/existT_continuous.
Qed.

End sigT_topology.
