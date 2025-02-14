(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import itv topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure compact.

(**md**************************************************************************)
(* # Product topology                                                         *)
(*                                                                            *)
(* Product `(T * U)%type` are endowed with the structures of:                 *)
(* - topology                                                                 *)
(* - uniform space                                                            *)
(* - pseudometric space                                                       *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Prod_Topology.
Context {T U : topologicalType}.

Let prod_nbhs (p : T * U) := filter_prod (nbhs p.1) (nbhs p.2).

Lemma prod_nbhs_filter (p : T * U) : ProperFilter (prod_nbhs p).
Proof. exact: filter_prod_proper. Qed.

Lemma prod_nbhs_singleton (p : T * U) (A : set (T * U)) : prod_nbhs p A -> A p.
Proof.
by move=> [QR [/nbhs_singleton Qp1 /nbhs_singleton Rp2]]; apply.
Qed.

Lemma prod_nbhs_nbhs (p : T * U) (A : set (T * U)) :
  prod_nbhs p A -> prod_nbhs p (prod_nbhs^~ A).
Proof.
move=> [QR [/nbhs_interior p1_Q /nbhs_interior p2_R] sQRA].
by exists (QR.1^°, QR.2^°) => // ??; exists QR.
Qed.

HB.instance Definition _ := hasNbhs.Build (T * U)%type prod_nbhs.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build (T * U)%type
  prod_nbhs_filter prod_nbhs_singleton prod_nbhs_nbhs.

End Prod_Topology.

Lemma fst_open {U V : topologicalType} (A : set (U * V)) :
  open A -> open (fst @` A).
Proof.
rewrite !openE => oA z [[a b/=] Aab <-]; rewrite /interior.
have [[P Q] [Pa Qb] pqA] := oA _ Aab; apply: (@filterS _ _ _ P) => // p Pp.
by exists (p, b) => //=; apply: pqA; split=> //=; exact: nbhs_singleton.
Qed.

Lemma snd_open {U V : topologicalType} (A : set (U * V)) :
  open A -> open (snd @` A).
Proof.
rewrite !openE => oA z [[a b/=] Aab <-]; rewrite /interior.
have [[P Q] [Pa Qb] pqA] := oA _ Aab; apply: (@filterS _ _ _ Q) => // q Qq.
by exists (a, q) => //=; apply: pqA; split => //; exact: nbhs_singleton.
Qed.

(** product of two uniform spaces *)

Section prod_Uniform.
Local Open Scope relation_scope.
Context {U V : uniformType}.
Implicit Types A : set ((U * V) * (U * V)).

Definition prod_ent :=
  [set A : set ((U * V) * (U * V)) |
    filter_prod (@entourage U) (@entourage V)
    [set ((xy.1.1,xy.2.1),(xy.1.2,xy.2.2)) | xy in A]].

Lemma prod_entP (A : set (U * U)) (B : set (V * V)) :
  entourage A -> entourage B ->
  prod_ent [set xy | A (xy.1.1, xy.2.1) /\ B (xy.1.2, xy.2.2)].
Proof.
move=> entA entB; exists (A,B) => // xy ABxy.
by exists ((xy.1.1, xy.2.1),(xy.1.2,xy.2.2)); rewrite /= -!surjective_pairing.
Qed.

Lemma prod_ent_filter : Filter prod_ent.
Proof.
have prodF := filter_prod_filter (@entourage_filter U) (@entourage_filter V).
split; rewrite /prod_ent.
- by rewrite -setXTT; apply: prod_entP filterT filterT.
- move=> A B /= entA entB; apply: filterS (filterI entA entB) => xy [].
  move=> [zt Azt ztexy] [zt' Bzt' zt'exy]; exists zt => //; split=> //.
  move/eqP: ztexy; rewrite -zt'exy !xpair_eqE.
  by rewrite andbACA -!xpair_eqE -!surjective_pairing => /eqP->.
- by move=> A B sAB /=; apply: filterS => ? [xy /sAB ??]; exists xy.
Qed.

Lemma prod_ent_refl A : prod_ent A -> diagonal `<=` A.
Proof.
move=> [B [entB1 entB2] sBA] xy /eqP.
rewrite [_.1]surjective_pairing [xy.2]surjective_pairing xpair_eqE.
move=> /andP [/eqP xy1e /eqP xy2e].
have /sBA : (B.1 `*` B.2) ((xy.1.1, xy.2.1), (xy.1.2, xy.2.2)).
  by rewrite xy1e xy2e; split=> /=; exact: entourage_refl.
move=> [zt Azt /eqP]; rewrite !xpair_eqE.
by rewrite andbACA -!xpair_eqE -!surjective_pairing => /eqP<-.
Qed.

Lemma prod_ent_inv A : prod_ent A -> prod_ent A^-1.
Proof.
move=> [B [/entourage_inv entB1 /entourage_inv entB2] sBA].
have:= prod_entP entB1 entB2; rewrite /prod_ent/=; apply: filterS.
move=> _ [p /(sBA (_,_)) [[x y] ? xyE] <-]; exists (y,x) => //; move/eqP: xyE.
by rewrite !xpair_eqE => /andP[/andP[/eqP-> /eqP->] /andP[/eqP-> /eqP->]].
Qed.

Lemma prod_ent_split A : prod_ent A ->
  exists2 B, prod_ent B & (B \; B `<=` A).
Proof.
move=> [B [entB1 entB2]] sBA; exists [set xy | split_ent B.1 (xy.1.1,xy.2.1) /\
  split_ent B.2 (xy.1.2,xy.2.2)].
  by apply: prod_entP; apply: entourage_split_ent.
move=> xy [uv /= [hB1xyuv1 hB2xyuv1] [hB1xyuv2 hB2xyuv2]].
have /sBA : (B.1 `*` B.2) ((xy.1.1, xy.2.1),(xy.1.2,xy.2.2)).
  by split=> /=; apply: subset_split_ent => //; [exists uv.1|exists uv.2].
move=> [zt Azt /eqP]; rewrite !xpair_eqE andbACA -!xpair_eqE.
by rewrite -!surjective_pairing => /eqP<-.
Qed.

Lemma prod_ent_nbhsE : nbhs = nbhs_ prod_ent.
Proof.
rewrite predeq2E => xy A; split=> [[B []] | [B [C [entC1 entC2] sCB] sBA]].
  rewrite -!nbhs_entourageE => - [C1 entC1 sCB1] [C2 entC2 sCB2] sBA.
  exists [set xy | C1 (xy.1.1, xy.2.1) /\ C2 (xy.1.2, xy.2.2)].
    exact: prod_entP.
  move=> uv /xsectionP/= [/xsectionP/sCB1 Buv1 /xsectionP/sCB2/(conj Buv1)].
  exact: sBA.
exists (xsection C.1 xy.1, xsection C.2 xy.2).
  by rewrite -!nbhs_entourageE; split; [exists C.1|exists C.2].
move=> uv [/= /xsectionP Cxyuv1 /xsectionP Cxyuv2]; apply: sBA.
have /sCB : (C.1 `*` C.2) ((xy.1,uv.1), (xy.2,uv.2)) => //.
move=> [zt Bzt /eqP]; rewrite !xpair_eqE andbACA -!xpair_eqE.
by  rewrite -!surjective_pairing => /eqP ztE; apply/xsectionP; rewrite -ztE.
Qed.

HB.instance Definition _ := Nbhs_isUniform.Build (U * V)%type
  prod_ent_filter prod_ent_refl prod_ent_inv prod_ent_split prod_ent_nbhsE.

End prod_Uniform.

(** product of two pseudoMetric spaces *)
Section prod_PseudoMetric.
Context {R : numDomainType} {U V : pseudoMetricType R}.
Implicit Types (x y : U * V).

Definition prod_ball x (eps : R) y :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).

Lemma prod_ball_center x (eps : R) : 0 < eps -> prod_ball x eps x.
Proof. by move=> /posnumP[?]. Qed.

Lemma prod_ball_sym x y (eps : R) : prod_ball x eps y -> prod_ball y eps x.
Proof. by move=> [bxy1 bxy2]; split; apply: ball_sym. Qed.

Lemma prod_ball_triangle x y z (e1 e2 : R) :
  prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Proof.
by move=> [bxy1 bxy2] [byz1 byz2]; split; apply: ball_triangle; eassumption.
Qed.

Lemma prod_entourage : entourage = entourage_ prod_ball.
Proof.
rewrite predeqE => P; split; last first.
  move=> [_/posnumP[e] sbeP].
  exists ([set xy | ball xy.1 e%:num xy.2],
          [set xy | ball xy.1 e%:num xy.2]) => //=.
  move=> [[a b] [c d]] [bab bcd]; exists ((a, c), (b, d))=> //=.
  exact: sbeP.
move=> [[A B]] /=; rewrite -!entourage_ballE.
move=> [[_/posnumP[eA] sbA] [_/posnumP[eB] sbB] sABP].
exists (Num.min eA eB)%:num => //= -[[a b] [c d] [/= bac bbd]].
suff /sABP [] : (A `*` B) ((a, c), (b, d)) by move=> [[??] [??]] ? [<-<-<-<-].
split; [apply: sbA|apply: sbB] => /=.
  by apply: le_ball bac; rewrite num_le ge_min lexx.
by apply: le_ball bbd; rewrite num_le ge_min lexx orbT.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R (U * V)%type
  prod_ball_center prod_ball_sym prod_ball_triangle prod_entourage.

End prod_PseudoMetric.

Section Nbhs_fct2.
Context {T : Type} {R : numDomainType} {U V : pseudoMetricType R}.
Lemma fcvg_ball2P {F : set_system U} {G : set_system V}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall y' \near F & z' \near G,
                ball y eps y' /\ ball z eps z'.
Proof. exact: fcvg_ballP. Qed.

Lemma cvg_ball2P {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V):
  (f @ F, g @ G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall i \near F & j \near G,
                ball y eps (f i) /\ ball z eps (g j).
Proof.
rewrite fcvg_ball2P; split=> + e e0 => /(_ e e0).
  by rewrite near_map2; apply.
by move=> fgyz; rewrite near_map2; apply: fgyz.
Qed.

End Nbhs_fct2.

Lemma compact_setX {U V : topologicalType} (P : set U) (Q : set V) :
  compact P -> compact Q -> compact (P `*` Q).
Proof.
rewrite !compact_near_coveringP => cptP cptQ I F Pr Ff cvfPQ.
have := cptP I F (fun i u => forall q, Q q -> Pr i (u, q)) Ff.
set R := (R in (R -> _) -> _); suff R' : R.
  by move/(_ R'); apply:filter_app; near=> i => + [a b] [Pa Qb]; apply.
rewrite /R => x Px;  apply: (@cptQ _ (filter_prod _ _)) => v Qv.
case: (cvfPQ (x, v)) => // [[N G]] /= [[[N1 N2 /= [N1x N2v]]]] N1N2N FG ngPr.
exists (N2, N1`*`G); first by split => //; exists (N1, G).
case=> a [b i] /= [N2a [N1b]] Gi.
by apply: (ngPr (b, a, i)); split => //; exact: N1N2N.
Unshelve. all: by end_near. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `compact_setX`")]
Notation compact_setM := compact_setX (only parsing).

Lemma swap_continuous {X Y : topologicalType} : continuous (@swap X Y).
Proof.
case=> a b W /= [[U V]][] /= Ub Va UVW; exists (V, U); first by split.
by case => //= ? ? [] ? ?; exact: UVW.
Qed.

Section reassociate_continuous.
Context {X Y Z : topologicalType}.

Lemma prodA_continuous : continuous (@prodA X Y Z).
Proof.
move=> [] [a b] c U [[/= P V]] [Pa] [][/= Q R][ Qb Rc] QRV PVU.
exists ((P `*` Q), R); first split.
- exists (P, Q); first by [].
  by case=> x y /= [Px Qy].
- by [].
- by move=> [[x y] z] [] [] ? ? ?; apply: PVU; split => //; exact: QRV.
Qed.

Lemma prodAr_continuous : continuous (@prodAr X Y Z).
Proof.
case=> a [b c] U [[V R]] [/= [[P Q /=]]] [Pa Qb] PQV Rc VRU.
exists (P, (Q `*` R)); first split => //.
- exists (Q, R); first by [].
  by case=> ? ? /= [].
- by case=> x [y z] [? [? ?]]; apply: VRU; split => //; exact: PQV.
Qed.

End reassociate_continuous.
