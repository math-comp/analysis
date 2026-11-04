(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions wochoice.
From mathcomp Require Import cardinality fsbigop set_interval filter reals.
From mathcomp Require Import topology_structure compact subspace_topology
  discrete_topology order_topology uniform_structure uniform_metrizable
  pseudometric_structure num_topology one_point_compactification connected
  supremum_topology sigT_topology.

(**md**************************************************************************)
(* # Separation Axioms                                                        *)
(*                                                                            *)
(* This file introduces the separation axioms, a series of topological        *)
(* properties about separating points and sets. They are sometimes denoted by *)
(* the names T0 through T6. Although we use their full names (hausdorff,      *)
(* accessible, uniform, etc). This file also provides related topological     *)
(* properties like zero dimensional and discrete.                             *)
(*                                                                            *)
(* ```                                                                        *)
(*              set_nbhs A == filter from open sets containing A              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## The classic separation axioms                                           *)
(* ```                                                                        *)
(*      kolmogorov_space T == T is a Kolmogorov space (T0)                    *)
(*      accessible_space T == T is an accessible space (T1)                   *)
(*       hausdorff_space T == T is a Hausdorff space (T2)                     *)
(*               close x y == x and y are arbitrarily close w.r.t. open sets  *)
(*          normal_space T == T is normal (sometimes called T4)               *)
(*         regular_space T == T is regular (sometimes called T3)              *)
(* ```                                                                        *)
(* ## related concepts                                                        *)
(* ```                                                                        *)
(*  totally_disconnected A == the only connected subsets of A are             *)
(*                            empty or singletons                             *)
(*      zero_dimensional T == points are separable by a clopen set            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section set_nbhs.
Context {T : topologicalType} (A : set T).

Definition set_nbhs := \bigcap_(x in A) nbhs x.

Global Instance set_nbhs_filter : Filter set_nbhs.
Proof.
split => P Q; first by exact: filterT.
  by move=> Px Qx x Ax; apply: filterI; [exact: Px | exact: Qx].
by move=> PQ + x Ax => /(_ _ Ax)/filterS; exact.
Qed.

Global Instance set_nbhs_pfilter : A !=set0 -> ProperFilter set_nbhs.
Proof.
case=> x Ax; split; last exact: set_nbhs_filter.
by move/(_ x Ax)/nbhs_singleton.
Qed.

Lemma set_nbhsP (B : set T) :
   set_nbhs B <-> (exists C, [/\ open C, A `<=` C & C `<=` B]).
Proof.
split; first last.
  by case=> V [? AV /filterS +] x /AV ?; apply; apply: open_nbhs_nbhs.
move=> snB; have Ux x : exists U, A x -> [/\ U x, open U & U `<=` B].
  have [/snB|?] := pselect (A x); last by exists point.
  by rewrite nbhsE => -[V [? ? ?]]; exists V.
exists (\bigcup_(x in A) (projT1 (cid (Ux x)))); split.
- by apply: bigcup_open => x Ax; have [] := projT2 (cid (Ux x)).
- by move=> x Ax; exists x => //; have [] := projT2 (cid (Ux x)).
- by move=> x [y Ay]; have [//| _ _] := projT2 (cid (Ux y)); exact.
Qed.

End set_nbhs.

Section point_separation_axioms.
Context {T : topologicalType}.

Definition kolmogorov_space := forall x y, x != y ->
  exists A : set T, (A \in nbhs x /\ y \in ~` A) \/ (A \in nbhs y /\ x \in ~` A).

Definition accessible_space := forall x y, x != y ->
  exists A : set T, [/\ open A, x \in A & y \in ~` A].

Definition hausdorff_space := forall p q : T, cluster (nbhs p) q -> p = q.

Lemma compact_closed (A : set T) : hausdorff_space -> compact A -> closed A.
Proof.
move=> hT Aco p clAp; have pA := [elaborate @withinT _ (nbhs p) A _].
have [q [Aq clsAp_q]] := [elaborate Aco _ _ pA]; rewrite (hT p q) //.
by apply: cvg_cluster clsAp_q; apply: cvg_within.
Qed.

Lemma compact_cluster_set1 (x : T) F V :
  hausdorff_space -> compact V -> nbhs x V ->
  ProperFilter F -> F V -> cluster F = [set x] -> F --> x.
Proof.
move=> ? cptV nxV PF FV clFx1 U nbhsU; rewrite nbhs_simpl.
wlog oU : U nbhsU / open U.
  rewrite /= nbhsE in nbhsU; case: nbhsU => O oO OsubU /(_ O) WH.
  by apply: (filterS OsubU); apply: WH; [exact: open_nbhs_nbhs | by case: oO].
have /compact_near_coveringP : compact (V `\` U).
  apply: (subclosed_compact _ cptV) => //.
  by apply: closedI; [exact: compact_closed | exact: open_closedC].
move=> /(_ _ (powerset_filter_from F) (fun W x => ~ W x))[].
  move=> z [Vz ?]; have zE : x <> z by move/nbhs_singleton: nbhsU => /[swap] ->.
  have : ~ cluster F z by move: zE; apply: contra_not; rewrite clFx1 => ->.
  case/existsNP=> C /existsPNP [D] FC /existsNP [Dz] /nonemptyPn.
  rewrite setIC => /disjoints_subset CD0; exists (D, [set W | F W /\ W `<=` C]).
    by split; rewrite //= nbhs_simpl; exact: powerset_filter_fromP.
  by case => t W [Dt] [FW] /subsetCP; apply; apply: CD0.
move=> M [MF ME2 [W] MW /(_ _ MW) VUW].
apply: (@filterS _ _ _ (V `&` W)); last by apply: filterI => //; exact: MF.
by move=> t [Vt Wt]; apply: contrapT => Ut; exact: (VUW t).
Qed.

Lemma compact_precompact (A : set T) :
  hausdorff_space -> compact A -> precompact A.
Proof.
by move=> h c; rewrite precompactE -(closure_id _).1//; exact: compact_closed.
Qed.

Lemma open_hausdorff : hausdorff_space =
  forall (x y : T), x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
                [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0].
Proof.
rewrite propeqE; split => [T_filterT2|T_openT2] x y.
  have := contra_not (T_filterT2 x y); rewrite (rwP eqP) (rwP negP).
  move=> /[apply] /asboolPn/existsp_asboolPn[A]; rewrite -existsNE => -[B].
  rewrite [nbhs _ _ -> _](rwP imply_asboolP) => /negP.
  rewrite asbool_imply !negb_imply => /andP[/asboolP xA] /andP[/asboolP yB].
  move=> /asboolPn; rewrite -set0P => /negP; rewrite negbK => /eqP AIB_eq0.
  move: xA yB; rewrite !nbhsE.
  move=> - [oA [oA_open oAx] oAA] [oB [oB_open oBx] oBB].
  by exists (oA, oB); rewrite ?inE; split => //; apply: subsetI_eq0 AIB_eq0.
apply: contraPP => /eqP /T_openT2[[/=A B]].
rewrite !inE => - [xA yB] [Aopen Bopen /eqP AIB_eq0].
move=> /(_ A B (open_nbhs_nbhs _) (open_nbhs_nbhs _)).
by rewrite -set0P => /(_ _ _)/negP; apply.
Qed.

Lemma hausdorff_accessible : hausdorff_space -> accessible_space.
Proof.
rewrite open_hausdorff => hsdfT => x y /hsdfT [[U V] [xU yV]] [/= ? ? /eqP].
rewrite setIC => /disjoints_subset VUc; exists U; repeat split => //.
by rewrite inE; apply: VUc; rewrite -inE.
Qed.

Lemma accessible_closed_set1 : accessible_space -> forall x : T, closed [set x].
Proof.
move=> T1 x; rewrite -[X in closed X]setCK; apply: open_closedC.
rewrite openE => y /eqP /T1 [U [oU yU xU]].
rewrite /interior nbhsE /=; exists U; last by rewrite subsetC1.
by split=> //; exact: set_mem.
Qed.

Lemma accessible_kolmogorov : accessible_space -> kolmogorov_space.
Proof.
move=> T1 x y /T1 [A [oA xA yA]]; exists A; left; split=> //.
by rewrite nbhsE inE; exists A => //; rewrite inE in xA.
Qed.

Lemma accessible_finite_set_closed :
  accessible_space <-> forall A : set T, finite_set A -> closed A.
Proof.
split => [TT1 A fA|h x y xy].
  rewrite -(fsbig_setU_set1 fA) fsbig_finite//=.
  by apply: bigsetU_closed => x xA; exact: accessible_closed_set1.
by exists (~` [set y]); rewrite !inE/=; split;
  [rewrite openC; exact: h|exact/eqP|].
Qed.

End point_separation_axioms.

Arguments hausdorff_space : clear implicits.
Arguments accessible_space : clear implicits.
Arguments kolmogorov_space : clear implicits.

Lemma limit_point_closed {T : topologicalType} (A : set T) :
  accessible_space T -> closed (limit_point A).
Proof.
move=> accT; rewrite -openC openE/= => a.
rewrite /setC/= not_limit_pointE => -[X].
rewrite nbhsE/= => -[U oaU UX] XAa.
rewrite /interior nbhsE/=.
exists U => // x Ux /=.
rewrite not_limit_pointE.
have [xa|xneqa] := eqVneq x a.
  exists U; rewrite xa; first exact: open_nbhs_nbhs.
  by apply: subset_trans XAa; exact: setIS.
exists (U `&` [set~ a]).
  apply: open_nbhs_nbhs; split.
    apply: openI; first by case: oaU.
    by rewrite openC; exact: accessible_closed_set1.
  by split => //; exact/eqP.
apply: (@subset_trans _ (A `&` (X `&` [set~ a]))).
  by apply: setIS; exact: setSI.
apply: (@subset_trans _ ([set a] `&` [set~ a])).
  by rewrite setIA; exact: setSI.
by rewrite setICr.
Qed.
Arguments limit_point_closed {T} A.

Lemma subspace_hausdorff {T : topologicalType} (A : set T) :
  hausdorff_space T -> hausdorff_space (subspace A).
Proof.
rewrite ?open_hausdorff => + x y xNy => /(_ x y xNy).
move=> [[P Q]] /= [Px Qx] /= [/open_subspaceW oP /open_subspaceW oQ].
by move=> ?; exists (P, Q); split => //=; [exact: oP | exact: oQ].
Qed.

Lemma discrete_hausdorff {T : discreteTopologicalType} : hausdorff_space T.
Proof.
by move=> p q /(_ _ _ (discrete_set1 p) (discrete_set1 q)) [] // x [] -> ->.
Qed.

Lemma order_hausdorff {d} {T : orderTopologicalType d} : hausdorff_space T.
Proof.
rewrite open_hausdorff=> p q; wlog : p q / (p < q)%O.
  have /orP[] := le_total p q; rewrite le_eqVlt => /predU1P[->|].
  - by rewrite eqxx.
  - by move=> ?; exact.
  - by rewrite eqxx.
  - move=> qp WH; rewrite eq_sym => /(WH _ _ qp)[[P Q] [? ?] [? ? ?]].
    by exists (Q, P); split; rewrite // setIC.
move=> plq ?; have [[z /andP[pz zq]]|] := pselect (exists z, p < z < q)%O.
  exists (`]-oo,z[, `]z,+oo[)%classic.
    by split => //=; apply/mem_set; rewrite set_itvE.
  split => //= ; apply/eqP; rewrite -subset0 => r; rewrite set_itvE => -[/= rz].
  by apply/negP; rewrite in_itv/= andbT -leNgt (ltW rz).
move=> npzq; exists (`]-oo, q[, `]p, +oo[)%classic; split => //=.
- by apply /mem_set; rewrite set_itvE.
- by apply /mem_set; rewrite set_itvE.
- apply/eqP; rewrite -subset0 => r; rewrite !set_itvE => -[/= rz zr].
  by apply: npzq; exists r; rewrite rz zr.
Qed.

Section ball_hausdorff.
Variables (R : numDomainType) (T : pseudoMetricType R).

Lemma ball_hausdorff : hausdorff_space T =
  forall (a b : T), a != b ->
  exists r : {posnum R} * {posnum R},
    ball a r.1%:num `&` ball b r.2%:num == set0.
Proof.
rewrite propeqE open_hausdorff; split => T2T a b /T2T[[/=]].
  move=> A B; rewrite 2!inE => [[aA bB] [oA oB /eqP ABeq0]].
  have /nbhs_ballP[_/posnumP[r] rA]: nbhs a A by apply: open_nbhs_nbhs.
  have /nbhs_ballP[_/posnumP[s] rB]: nbhs b B by apply: open_nbhs_nbhs.
  by exists (r, s) => /=; rewrite (subsetI_eq0 _ _ ABeq0).
move=> r s /eqP brs_eq0; exists ((ball a r%:num)°, (ball b s%:num)°) => /=.
  split; by rewrite inE; apply: nbhs_singleton; apply: nbhs_interior;
            apply/nbhs_ballP; apply: in_filter_from => /=.
split; do ?by apply: open_interior.
by rewrite (subsetI_eq0 _ _ brs_eq0)//; exact: interior_subset.
Qed.
End ball_hausdorff.

Import numFieldTopology.Exports.
Lemma Rhausdorff (R : realFieldType) : hausdorff_space R.
Proof. exact: order_hausdorff. Qed.

Lemma one_point_compactification_hausdorff {X : topologicalType} :
   locally_compact [set: X] ->
   hausdorff_space X ->
   hausdorff_space (one_point_compactification X).
Proof.
move=> lcpt hsdfX [x|] [y|] //=.
- move=> clxy; congr Some; apply: hsdfX => U V Ux Vy.
  have [] := clxy (Some @` U) (Some @` V).
    by apply: filterS Ux; exact: preimage_image.
    by apply: filterS Vy; exact: preimage_image.
  by case=> [_|] [] /= [// p /[swap] -[] <- Up] [q /[swap] -[] -> Vp]; exists p.
- have [U] := lcpt x I; rewrite withinET => Ux [cU clU].
  case/(_ (Some @` U) (Some @` (~` U) `|` [set None])).
  + exact: one_point_compactification_some_nbhs.
  + by exists U.
  + by move=> [?|] [][]// z /[swap] -[] <- ? []//= [? /[swap] -[] ->].
- have [U] := lcpt y I; rewrite withinET => Uy [cU clU].
  case/(_ (Some @` (~` U) `|` [set None]) (Some @` U)); first by exists U.
    exact: one_point_compactification_some_nbhs.
  by case=> [?|] [] [] //= + [] ? // /[swap] -[] -> => -[? /[swap] -[] <-].
Qed.

Section hausdorff_topologicalType.
Variable T : topologicalType.
Implicit Types x y : T.

Local Open Scope classical_set_scope.
Definition close x y : Prop := forall M, open_nbhs y M -> closure M x.

Lemma closeEnbhs x : close x = cluster (nbhs x).
Proof.
transitivity (cluster (open_nbhs x)); last first.
  by rewrite /cluster; under eq_fun do rewrite -meets_openl.
rewrite clusterEonbhs /close funeqE => y /=; rewrite meetsC /meets.
apply/eq_forall => A; rewrite forall_swap.
by rewrite closureEonbhs/= meets_globallyl.
Qed.

Lemma closeEonbhs x : close x = [set y | open_nbhs x `#` open_nbhs y].
Proof.
by rewrite closeEnbhs; under eq_fun do rewrite -meets_openl -meets_openr.
Qed.

Lemma close_sym x y : close x y -> close y x.
Proof. by rewrite !closeEnbhs /cluster/= meetsC. Qed.

Lemma cvg_close {F} {FF : ProperFilter F} x y : F --> x -> F --> y -> close x y.
Proof.
by move=> /sub_meets sx /sx; rewrite closeEnbhs; apply; apply/proper_meetsxx.
Qed.

Lemma close_refl x : close x x.
Proof. exact: (@cvg_close (nbhs x)). Qed.
Hint Resolve close_refl : core.

Lemma cvgx_close x y : x --> y -> close x y.
Proof. exact: cvg_close. Qed.

Lemma cvgi_close T' {F} {FF : ProperFilter F} (f : T' -> set T) (l l' : T) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: {near F, is_totalfun f}.
  by apply: cvg_close fFl fFl'; exact: fmapi_proper_filter.
apply: filter_app f_prop; near do split=> //=.
have: (f `@ F) setT by apply: fFl; apply: filterT.
by rewrite fmapiE; apply: filterS => x [y []]; exists y.
Unshelve. all: by end_near. Qed.

Hypothesis sep : hausdorff_space T.

Lemma closeE x y : close x y = (x = y).
Proof.
rewrite propeqE; split; last by move=> ->; exact: close_refl.
by rewrite closeEnbhs; exact: sep.
Qed.

Lemma close_eq x y : close x y -> x = y.
Proof. by rewrite closeE. Qed.

Lemma cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : T | F --> x].
Proof. move=> Fx Fy; rewrite -closeE //; exact: (@cvg_close F). Qed.

Lemma cvg_eq x y : x --> y -> x = y.
Proof. by rewrite -closeE //; apply: cvg_close. Qed.

Lemma cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set T) :
  {near F, is_fun f} -> is_subset1 [set x : T | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE //; exact: cvgi_close. Qed.

End hausdorff_topologicalType.

Section hausdorff_ptopologicalType.
Variable T : ptopologicalType.
Implicit Types x y : T.

Lemma close_cvg (F1 F2 : set_system T) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
move=> F12 F21.
have [/(cvg_trans F21) F2l|dvgF1] := pselect (cvg F1).
  by apply: (@cvg_close _ F2) => //; apply: cvgP F2l.
have [/(cvg_trans F12)/cvgP//|dvgF2] := pselect (cvg F2).
rewrite dvgP // dvgP //; exact/close_refl.
Qed.

Hypothesis sep : hausdorff_space T.

Lemma cvg_lim {F} {FF : ProperFilter F} (l : T) :
  F --> l -> lim F = l.
Proof. by move=> /[dup] /cvgP /cvg_unique; apply. Qed.

Lemma lim_id x : lim (nbhs x) = x.
Proof. exact: cvg_lim. Qed.

Lemma lim_near_cst {U} {F} {FF : ProperFilter F} (l : T) (f : U -> T) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. by move=> /cvg_near_cst/cvg_lim. Qed.

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) : lim (@cst U _ k @ F) = k.
Proof. exact: cvg_lim. Qed.

Lemma cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> T -> Prop) (l : T) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
by move=> f_prop fl; apply: get_unique =>// l' fl'; exact: cvgi_unique _ fl' fl.
Qed.

End hausdorff_ptopologicalType.
#[global] Hint Resolve close_refl : core.
Arguments close_cvg {T} F1 F2 {FF2} _.

Section close_uniform.
Implicit Types (U : uniformType).

Lemma entourage_close {U} (x y : U) :
  close x y = forall A, entourage A -> A (x, y).
Proof.
rewrite propeqE; split=> [cxy A entA|cxy].
  have /entourage_split_ent entsA := entA; rewrite closeEnbhs in cxy.
  have yl := nbhs_entourage _ (entourage_inv entsA).
  have yr := nbhs_entourage _ entsA.
  have [z [/xsectionP zx /xsectionP zy]] := cxy _ _ (yr x) (yl y).
  exact: (entourage_split z).
rewrite closeEnbhs => A B /nbhsP[E1 entE1 sE1A] /nbhsP[E2 entE2 sE2B].
exists y; split.
- by apply/sE1A/xsectionP; exact: cxy.
- by apply/sE2B/xsectionP; exact: entourage_refl.
Qed.

Lemma close_trans {U} (y x z : U) : close x y -> close y z -> close x z.
Proof.
rewrite !entourage_close => cxy cyz A entA.
exact: entourage_split (cxy _ _) (cyz _ _).
Qed.

Lemma close_cvgxx {U} (x y : U) : close x y -> x --> y.
Proof.
rewrite entourage_close => cxy P /= /nbhsP[A entA sAP].
apply/nbhsP; exists (split_ent A) => // z /xsectionP xz; apply: sAP.
apply/xsectionP; apply: (entourage_split x) => //.
by have := cxy _ (entourage_inv (entourage_split_ent entA)).
Qed.

Lemma cvg_closeP {U : puniformType} (F : set_system U) (l : U) :
    ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Proof.
move=> FF; split=> [Fl|[cvF]Cl].
  by have /cvgP := Fl; split=> //; apply: (@cvg_close _ F).
by apply: cvg_trans (close_cvgxx Cl).
Qed.

Lemma ball_close {R : numFieldType} {M : pseudoMetricType R} (x y : M) :
  close x y = forall eps : {posnum R}, ball x eps%:num y.
Proof.
rewrite propeqE; split => [cxy eps|cxy].
  have := [elaborate cxy _ (open_nbhs_ball _ (eps%:num/2)%:pos)].
  rewrite closureEonbhs/= meetsC meets_globallyr.
  move/(_ _ (open_nbhs_ball _ (eps%:num/2)%:pos)) => [z [zx zy]].
  by apply: (@ball_splitl _ _ z); apply: interior_subset.
rewrite closeEnbhs => B A /nbhs_ballP[_/posnumP[e2 e2B]]
  /nbhs_ballP[_/posnumP[e1 e1A]].
by exists y; split; [apply/e2B|apply/e1A; exact: ballxx].
Qed.
End close_uniform.

Section set_separations.
Context {T : topologicalType}.

Definition normal_space :=
  forall A : set T, closed A ->
    filter_from (set_nbhs A) closure `=>` set_nbhs A.

Definition regular_space :=
  forall a : T, filter_from (nbhs a) closure --> a.

Lemma compact_regular (x : T) V : hausdorff_space T -> compact V ->
  nbhs x V -> {for x, regular_space}.
Proof.
move=> sep cptv Vx; apply: (@compact_cluster_set1 T x _ V) => //.
- apply: filter_from_proper => //; first last.
    by move=> ? /nbhs_singleton/subset_closure ?; exists x.
  apply: filter_from_filter; first by exists setT; exact: filterT.
  move=> P Q Px Qx; exists (P `&` Q); [exact: filterI | exact: closureI].
- by exists V => //; have /closure_id <- : closed V by exact: compact_closed.
rewrite eqEsubset; split; first last.
  move=> _ -> A B [C Cx CA /nbhs_singleton Bx]; exists x; split => //.
  by apply/CA/subset_closure; exact: nbhs_singleton.
move=> y /=; apply: contraPeq; move: sep; rewrite open_hausdorff => /[apply].
move=> [[B A]]/=; rewrite ?inE; case=> By Ax [oB oA BA0].
apply/existsNP; exists (closure A); apply/existsNP; exists B; apply/not_implyP.
split; first by exists A => //; exact: open_nbhs_nbhs.
apply/not_implyP; split; first exact: open_nbhs_nbhs.
apply/set0P/negP; rewrite negbK; apply/eqP/disjoints_subset.
have /closure_id -> : closed (~` B); first by exact: open_closedC.
by apply/closureS/disjoints_subset; rewrite setIC.
Qed.

Lemma compact_normal_local (K : set T) : hausdorff_space T -> compact K ->
  forall A : set T, A `<=` K° -> {for A, normal_space}.
Proof.
move=> hT cptV A AK clA B snAB; have /compact_near_coveringP cvA : compact A.
  apply/(subclosed_compact clA cptV)/(subset_trans AK).
  exact: interior_subset.
have snbC (U : set T) : Filter (filter_from (set_nbhs U) closure).
  apply: filter_from_filter; first by exists setT; apply: filterT.
  by move=> P Q sAP sAQ; exists (P `&` Q); [apply filterI|exact: closureI].
have [/(congr1 setC)|/set0P[b0 B0]] := eqVneq (~` B) set0.
  by rewrite setCK setC0 => ->; exact: filterT.
have PsnA : ProperFilter (filter_from (set_nbhs (~` B)) closure).
  apply: filter_from_proper => ? P.
  by exists b0; apply/subset_closure; apply: nbhs_singleton; exact: P.
pose F := powerset_filter_from (filter_from (set_nbhs (~` B)) closure).
have PF : Filter F by exact: powerset_filter_from_filter.
have cvP (x : T) : A x -> \forall x' \near x & i \near F, (~` i) x'.
  move=> Ax; case/set_nbhsP : snAB => C [oC AC CB].
  have [] := @compact_regular x _ hT cptV _ C; first exact: AK.
    by rewrite nbhsE /=; exists C => //; split => //; exact: AC.
  move=> D /nbhs_interior nD cDC.
  have snBD : filter_from (set_nbhs (~` B)) closure (closure (~` closure D)).
    exists (closure (~` closure D)) => [z|].
      move=> nBZ; apply: filterS; first exact: subset_closure.
      apply: open_nbhs_nbhs; split; first exact/closed_openC/closed_closure.
      exact/(subsetC _ nBZ)/(subset_trans cDC).
    by have := @closed_closure _ (~` closure D); rewrite closure_id => <-.
  near=> y U => /=; have Dy : D° y by exact: (near nD _).
  have UclD : U `<=` closure (~` closure D).
    exact: (near (small_set_sub snBD) U).
  move=> Uy; have [z [/= + Dz]] := UclD _ Uy _ Dy.
  by apply; exact: subset_closure.
case/(_ _ _ _ _ cvP) : cvA => R /= [RA Rmono [U RU] RBx].
have [V /set_nbhsP [W [oW cBW WV] clVU]] := RA _ RU; exists (~` W).
  apply/set_nbhsP; exists (~` closure W); split.
  - exact/closed_openC/closed_closure.
  - by move=> y /(RBx _ RU) + Wy; apply; exact/clVU/(closureS WV).
  - by apply: subsetC; exact/subset_closure.
have : closed (~` W) by exact: open_closedC.
by rewrite closure_id => <-; exact: subsetCl.
Unshelve. all: by end_near. Qed.

Lemma compact_normal : hausdorff_space T -> compact [set: T] -> normal_space.
Proof.
move=> ? /compact_normal_local + A clA; apply => //.
by move=> z ?; exact: filterT.
Qed.

End set_separations.

Arguments normal_space : clear implicits.
Arguments regular_space : clear implicits.

Local Open Scope relation_scope.
Lemma uniform_regular {T : uniformType} : @regular_space T.
Proof.
move=> x R /=; rewrite -{1}nbhs_entourageE => -[E entE ER].
pose E' := split_ent E; have eE' : entourage E' by exact: entourage_split_ent.
exists (xsection (E' `&` E'^-1) x).
  rewrite -nbhs_entourageE; exists (E' `&` E'^-1) => //.
  exact: filterI.
move=> z /= clEz; apply/ER/xsectionP; apply: subset_split_ent => //.
have [] := clEz (xsection (E' `&` E'^-1) z).
  rewrite -nbhs_entourageE; exists (E' `&` E'^-1) => //.
  exact: filterI.
by move=> y /= [/xsectionP[? ?] /xsectionP[? ?]]; exists y.
Qed.
Local Close Scope relation_scope.

#[global] Hint Resolve uniform_regular : core.

Section totally_disconnected.
Implicit Types T : topologicalType.

Definition totally_disconnected {T} (A : set T) :=
  forall x, A x -> connected_component A x = [set x].

Definition zero_dimensional T :=
  (forall x y, x != y -> exists U : set T, [/\ clopen U, U x & ~ U y]).

Lemma discrete_zero_dimension {T : discreteTopologicalType} : zero_dimensional T.
Proof.
move=> x y xny; exists [set x]; split => //; last exact/nesym/eqP.
by split; [exact: discrete_open | exact: discrete_closed].
Qed.

Lemma zero_dimension_totally_disconnected {T} :
  zero_dimensional T -> totally_disconnected [set: T].
Proof.
move=> zdA x _; rewrite eqEsubset.
split=> [z [R [Rx _ ctdR Rz]]|_ ->]; last exact: connected_component_refl.
apply: contrapT => /eqP znx; have [U [[oU cU] Uz Ux]] := zdA _ _  znx.
suff : R `&` U = R by move: Rx => /[swap] <- [].
by apply: ctdR; [exists z|exists U|exists U].
Qed.

Lemma zero_dimensional_cvg {T} (x : T) :
  hausdorff_space T -> zero_dimensional T -> compact [set: T] ->
  filter_from [set D : set T | D x /\ clopen D] id --> x.
Proof.
pose F := filter_from [set D : set T | D x /\ clopen D] id.
have FF : Filter F.
  apply: filter_from_filter; first by exists setT; split => //; exact: clopenT.
  by move=> A B [? ?] [? ?]; exists (A `&` B) => //; split=> //; exact: clopenI.
have PF : ProperFilter F by apply: filter_from_proper; move=> ? [? _]; exists x.
move=> hsdfT zdT cmpT U Ux; rewrite nbhs_simpl -/F.
wlog oU : U Ux / open U.
  move: Ux; rewrite /= nbhsE => -[] V [? ?] /filterS + /(_ V) P.
  by apply; apply: P => //; exists V.
have /(iffLR (compact_near_coveringP _)) : compact (~` U).
  by apply: (subclosed_compact _ cmpT) => //; exact: open_closedC.
move=> /(_ _ _ setC (powerset_filter_from_filter PF))[].
  move=> y nUy; have /zdT [C [[oC cC] Cx Cy]] : x != y.
    by apply: contra_notN nUy => /eqP <-; exact: nbhs_singleton.
  exists (~` C, [set U | U `<=` C]); first split.
  - by apply: open_nbhs_nbhs; split => //; exact: closed_openC.
  - apply/near_powerset_filter_fromP; first by move=> ? ?; exact: subset_trans.
    by exists C => //; exists C.
  - by case=> i j [? /subsetC]; apply.
by move=> D [DF _ [C DC]]/(_ _ DC)/subsetC2/filterS; apply; exact: DF.
Qed.

Lemma zero_dimensional_ray {d} {T : orderTopologicalType d} (x y : T) :
  (x < y)%O -> zero_dimensional T ->
  exists U, [/\ clopen U, U y , ~ U x & forall l r, U r -> ~ U l -> l < r]%O.
Proof.
move=> xy zt; have xNy : y != x by move: xy; rewrite lt_def => /andP[].
have [U [clU Uy nUx]] := zt y x xNy.
have := clopen_bigcup_clopen clU Uy; set I := (I in clopen I); case=> ? ?.
pose V := I `|` `[y, +oo[; have Iy : I y.
  case: clU => + _; rewrite openE => /(_ _ Uy).
  rewrite /interior /= itv_nbhsE /= => -[i [] iy yi iU].
  by exists i => //; split => //; exact: itv_open_ends_open.
have IU : I `<=` U by move=> ? [? [+ _ _]] => /subset_trans; exact.
exists V; split; first split.
- suff -> : V = I `|` `]y,+oo[ by exact: openU.
  have /mem_set := Iy; rewrite -sub1set => /setUidl <-.
  by rewrite -setUA setU1itv.
- by apply: closedU => //; exact: rray_closed.
- by left.
- by move=> [/IU //|]; rewrite set_itvE/= leNgt xy.
- move=> l r Vr Vl; rewrite ltNge; apply/negP; move: Vl; apply: contra_not.
  move=> rl; case: Vr; first last.
    by rewrite set_itvE => yr; right; rewrite set_itvE; exact: (le_trans yr).
  have /orP[|ly] := le_total y l; first by move=> + _; right; rewrite set_itvE.
  case=> i [iu oi /= yi ri]; left; exists i; first by split.
  move: iu oi => _ _; case: i yi ri => p q /= /andP [py yq] /andP[pr rq].
  apply/andP; split.
  + by rewrite (le_trans pr)// bnd_simp.
  + by rewrite (le_trans _ yq)// bnd_simp.
Qed.

End totally_disconnected.

Section sigT_separations.
Context {I : choiceType} {X : I -> topologicalType}.

Lemma sigT_hausdorff :
  (forall i, hausdorff_space (X i)) -> hausdorff_space {i & X i}.
Proof.
move=> hX [i x] [j y]; rewrite/cluster /= /nbhs /= 2!sigT_nbhsE /= => cl.
have [] := cl (existT X i @` [set: X i]) (existT X j @` [set: X j]);
  [by apply: existT_nbhs; exact: filterT..|].
move=> p [/= [_ _ <-] [_ _ [ji]]] _.
rewrite {}ji {j} in x y cl *.
congr existT; apply: hX => U V Ux Vy.
have [] := cl (existT X i @` U) (existT X i @` V); [exact: existT_nbhs..|].
move=> z [] [l Ul <-] [r Vr lr]; exists l; split => //.
by rewrite -(existT_inj2 lr).
Qed.

End sigT_separations.
