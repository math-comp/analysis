(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical.
From mathcomp Require Import itv topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure.
(**md**************************************************************************)
(* # Matrix topology                                                          *)
(* ```                                                                        *)
(*                  mx_ent m n A == entourages for the m x n matrices        *)
(*                 mx_ball m n A == balls for the m x n matrices             *)
(* ```                                                                        *)
(* Matrices `'M[T]_(m, n)` are endowed with the structures of:                *)
(* - topology                                                                 *)
(* - uniform space                                                            *)
(* - pseudometric space                                                       *)
(* - complete uniform space                                                   *)
(* - complete pseudometric space                                              *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section matrix_Topology.
Variables (m n : nat) (T : topologicalType).

Implicit Types M : 'M[T]_(m, n).

Lemma mx_nbhs_filter M : ProperFilter (nbhs M).
Proof.
apply: (filter_from_proper (filter_from_filter _ _)) => [|P Q M_P M_Q|P M_P].
- by exists (fun i j => setT) => ??; apply: filterT.
- exists (fun i j => P i j `&` Q i j) => [??|mx PQmx]; first exact: filterI.
  by split=> i j; have [] := PQmx i j.
- exists (\matrix_(i, j) xget (M i j) (P i j)) => i j; rewrite mxE.
  by apply: xgetPex; exact: filter_ex (M_P i j).
Qed.

Lemma mx_nbhs_singleton M (A : set 'M[T]_(m, n)) : nbhs M A -> A M.
Proof. by move=> [P M_P]; apply=> ??; apply: nbhs_singleton. Qed.

Lemma mx_nbhs_nbhs M (A : set 'M[T]_(m, n)) : nbhs M A -> nbhs M (nbhs^~ A).
Proof.
move=> [P M_P sPA]; exists (fun i j => (P i j)^°).
  by move=> ? ?; apply: nbhs_interior.
by move=> ? ?; exists P.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build 'M[T]_(m, n)
  mx_nbhs_filter mx_nbhs_singleton mx_nbhs_nbhs.

End matrix_Topology.

Section matrix_PointedTopology.
Variables (m n : nat) (T : pointedType).
Implicit Types M : 'M[T]_(m, n).
HB.instance Definition _ := Pointed.on 'M[T]_(m, n).

End matrix_PointedTopology.

Section matrix_Uniform.
Local Open Scope relation_scope.
Variables (m n : nat) (T : uniformType).

Implicit Types A : set ('M[T]_(m, n) * 'M[T]_(m, n)).

Definition mx_ent := filter_from
  [set P : 'I_m -> 'I_n -> set (T * T) | forall i j, entourage (P i j)]
  (fun P => [set MN : 'M[T]_(m, n) * 'M[T]_(m, n) |
    forall i j, P i j (MN.1 i j, MN.2 i j)]).

Lemma mx_ent_filter : Filter mx_ent.
Proof.
apply: filter_from_filter => [|A B entA entB].
  by exists (fun _ _ => setT) => _ _; apply: filterT.
exists (fun i j => A i j `&` B i j); first by move=> ??; apply: filterI.
by move=> MN ABMN; split=> i j; have [] := ABMN i j.
Qed.

Lemma mx_ent_refl A : mx_ent A -> diagonal `<=` A.
Proof.
move=> [B entB sBA] MN MN1e2; apply: sBA => i j.
by rewrite MN1e2; exact: entourage_refl.
Qed.

Lemma mx_ent_inv A : mx_ent A -> mx_ent A^-1.
Proof.
move=> [B entB sBA]; exists (fun i j => (B i j)^-1).
  by move=> i j; apply: entourage_inv.
by move=> MN BMN; apply: sBA.
Qed.

Lemma mx_ent_split A : mx_ent A -> exists2 B, mx_ent B & B \; B `<=` A.
Proof.
move=> [B entB sBA].
have Bsplit : forall i j, exists C, entourage C /\ C \; C `<=` B i j.
  by move=> ??; apply/exists2P/entourage_split_ex.
exists [set MN : 'M[T]_(m, n) * 'M[T]_(m, n) |
  forall i j, get [set C | entourage C /\ C \; C `<=` B i j]
  (MN.1 i j, MN.2 i j)].
  by exists (fun i j => get [set C | entourage C /\ C \; C `<=` B i j]).
move=> MN [P CMN1P CPMN2]; apply/sBA => i j.
have /getPex [_] := Bsplit i j; apply; exists (P i j); first exact: CMN1P.
exact: CPMN2.
Qed.

Lemma mx_ent_nbhsE : nbhs = nbhs_ mx_ent.
Proof.
rewrite predeq2E => M A; split.
  move=> [B]; rewrite -nbhs_entourageE => M_B sBA.
  set sB := fun i j => [set C | entourage C /\ xsection C (M i j) `<=` B i j].
  have {}M_B : forall i j, sB i j !=set0 by move=> ??; apply/exists2P/M_B.
  exists [set MN : 'M[T]_(m, n) * 'M[T]_(m, n) | forall i j,
    get (sB i j) (MN.1 i j, MN.2 i j)].
    by exists (fun i j => get (sB i j)) => // i j; have /getPex [] := M_B i j.
  move=> N /xsectionP CMN; apply/sBA => i j; have /getPex [_] := M_B i j; apply.
  exact/xsectionP/CMN.
move=> [B [C entC sCB] sBA]; exists (fun i j => xsection (C i j) (M i j)).
  by rewrite -nbhs_entourageE => i j; exists (C i j).
by move=> N CMN; apply/sBA; apply/xsectionP/sCB => ? ?; exact/xsectionP/CMN.
Qed.

HB.instance Definition _ := Nbhs_isUniform.Build 'M[T]_(m, n)
  mx_ent_filter mx_ent_refl mx_ent_inv mx_ent_split mx_ent_nbhsE.

End matrix_Uniform.

Lemma cvg_mx_entourageP (T : puniformType) m n (F : set_system 'M[T]_(m,n))
  (FF : Filter F) (M : 'M[T]_(m,n)) :
  F --> M <->
  forall A, entourage A -> \forall N \near F,
  forall i j, (M i j, (N : 'M[T]_(m,n)) i j) \in A.
Proof.
split.
  rewrite filter_fromP => FM A ?.
  by apply: (FM (fun i j => xsection A (M i j))).
move=> FM; apply/cvg_entourageP => A [P entP sPA]; near=> N; apply/xsectionP.
move/subsetP : sPA; apply => /=; near: N; set Q := \bigcap_ij P ij.1 ij.2.
apply: filterS (FM Q _).
  move=> N QN; rewrite inE/= => i j.
  by have := QN i j; rewrite !inE => /(_ (i, j)); exact.
have -> : Q =
  \bigcap_(ij in [set k | k \in [fset x in predT]%fset]) P ij.1 ij.2.
  by rewrite predeqE => t; split=> Qt ij _; apply: Qt => //=; rewrite !inE.
by apply: filter_bigI => ??; apply: entP.
Unshelve. all: by end_near. Qed.

Section matrix_PointedTopology.
Variables (m n : nat) .
HB.instance Definition _ (T : ptopologicalType) := Filtered.on 'M[T]_(m, n).
HB.instance Definition _ (T : ptopologicalType) := Pointed.on 'M[T]_(m, n).
HB.instance Definition _ (T : ptopologicalType) :=
  PointedFiltered.on 'M[T]_(m, n).
HB.instance Definition _ (T : ptopologicalType) :=
  PointedTopological.on 'M[T]_(m, n).
HB.instance Definition _ (T : uniformType) := Uniform.on 'M[T]_(m, n).
HB.instance Definition _ (T : puniformType) := Pointed.on 'M[T]_(m, n).
HB.instance Definition _ (T : puniformType) := PointedUniform.on 'M[T]_(m, n).
End matrix_PointedTopology.

Section matrix_Complete.
Variables (T : completeType) (m n : nat).

Lemma mx_complete (F : set_system 'M[T]_(m, n)) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
  cauchy ((fun M : 'M[T]_(m, n) => M _ _) @ F).
  move=> i j A /= entA; rewrite near_simpl -near2E near_map2.
  by apply: Fc; exists (fun _ _ => A).
apply/cvg_ex.
set Mlim := \matrix_(i, j) (lim ((fun M : 'M[T]_(m, n) => M i j) @ F) : T).
exists Mlim; apply/cvg_mx_entourageP => A entA; near=> M => i j; near F => M'.
rewrite inE.
apply: subset_split_ent => //; exists (M' i j) => /=.
  by near: M'; rewrite mxE; exact: cvF.
move: (i) (j); near: M'; near: M; apply: nearP_dep; apply: Fc.
by exists (fun _ _ => (split_ent A)^-1%relation) => ?? //; apply: entourage_inv.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Uniform_isComplete.Build 'M[T]_(m, n) mx_complete.

End matrix_Complete.

(** matrices *)
Section matrix_PseudoMetric.
Variables (m n : nat) (R : numDomainType) (T : pseudoMetricType R).
Implicit Types (x y : 'M[T]_(m, n)) (e : R).

Definition mx_ball x e y := forall i j, ball (x i j) e (y i j).

Local Lemma mx_ball_center x e : 0 < e -> mx_ball x e x.
Proof. by move=> ? ? ?; exact: ballxx. Qed.

Local Lemma mx_ball_sym x y e : mx_ball x e y -> mx_ball y e x.
Proof. by move=> xe_y ? ?; apply/ball_sym/xe_y. Qed.

Local Lemma mx_ball_triangle x y z e1 e2 :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ??; apply: ball_triangle; [exact: xe1_y|exact: ye2_z].
Qed.

Local Lemma mx_entourage : entourage = entourage_ mx_ball.
Proof.
rewrite predeqE=> A; split; last first.
  move=> [_/posnumP[e] sbeA].
  exists (fun _ _ => [set xy | ball xy.1 e%:num xy.2]) => //= _ _.
move=> [P]; rewrite -entourage_ballE => entP sPA.
set diag := fun e : {posnum R} => [set xy : T * T | ball xy.1 e%:num xy.2].
exists (\big[Num.min/1%:pos]_i \big[Num.min/1%:pos]_j xget 1%:pos
  (fun e : {posnum R} => diag e `<=` P i j))%:num => //=.
move=> MN MN_min; apply: sPA => i j.
have /(xgetPex 1%:pos): exists e : {posnum R}, diag e `<=` P i j.
  by have [_/posnumP[e]] := entP i j; exists e.
apply; apply: le_ball (MN_min i j).
apply: le_trans (@bigmin_le _ {posnum R} _ _ i _) _.
exact: bigmin_le.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R 'M[T]_(m, n)
  mx_ball_center mx_ball_sym mx_ball_triangle mx_entourage.
End matrix_PseudoMetric.

HB.instance Definition _ (R : numFieldType) (T : completePseudoMetricType R)
  (m n : nat) := Uniform_isComplete.Build 'M[T]_(m, n) cauchy_cvg.
