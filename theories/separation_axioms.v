(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions wochoice.
From mathcomp Require Import cardinality mathcomp_extra fsbigop set_interval.
From mathcomp Require Import filter reals itv topology.

(**md**************************************************************************)
(* # Separation Axioms                                                        *)
(*                                                                            *)
(* This file introduces the separation axioms, a series of topological        *)
(* properties about separating points and sets. They are somtimes denoted by  *)
(* the names T0 through T6. Although we use their full names (hausdorff,      *)
(* accessible, uniform, etc). This file also provides related topological     *)
(* properties like zero dimensional and perfect, and discrete.                *)
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
(*           perfect_set A == A is closed, and every point in A is            *)
(*                            a limit point of A                              *)
(* ```                                                                        *)
(* ## metrizability for uniform spaces                                        *)
(* ```                                                                        *)
(*  countable_uniform.type == endows a pseudoMetric on a uniform type whose   *)
(*                            entourage has a countable basis                 *)
(*        sup_pseudometric == the pseudometric induced for the supremum       *)
(*                            of countably many pseudoMetrics                 *)
(*                 gauge E == for an entourage E, gauge E is a filter which   *)
(*                            includes `iter n split_ent E`.                  *)
(*                            Critically, `gauge E` forms a uniform space     *)
(*                            with a countable uniformity.                    *)
(*          perfect_set A  := closed A /\ limit_point A = A                   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
From mathcomp Require Import mathcomp_extra.
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
  case/existsNP=> C /existsPNP [D] FC /existsNP [Dz] /set0P/negP/negPn/eqP.
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
move=> h c; rewrite precompactE ( _ : closure A = A)//.
by apply/esym/closure_id; exact: compact_closed.
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
  by apply: closed_bigsetU => x xA; exact: accessible_closed_set1.
by exists (~` [set y]); rewrite !inE/=; split;
  [rewrite openC; exact: h|exact/eqP|].
Qed.

End point_separation_axioms.

Arguments hausdorff_space : clear implicits.
Arguments accessible_space : clear implicits.
Arguments kolmogorov_space : clear implicits.

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
move=> r s /eqP brs_eq0; exists ((ball a r%:num)^°, (ball b s%:num)^°) => /=.
  split; by rewrite inE; apply: nbhs_singleton; apply: nbhs_interior;
            apply/nbhs_ballP; apply: in_filter_from => /=.
split; do ?by apply: open_interior.
by rewrite (subsetI_eq0 _ _ brs_eq0)//; apply: interior_subset.
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

#[deprecated(since="mathcomp-analysis 1.5.0", note="use `cvgi_close` instead")]
Definition cvg_toi_locally_close := @cvgi_close.

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

Lemma lim_id x : lim (nbhs x) = x.
Proof. by apply/esym/cvg_eq/cvg_ex => //; exists x. Qed.

Lemma cvg_lim {U : Type} {F} {FF : ProperFilter F} (f : U -> T) (l : T) :
  f @ F --> l -> lim (f @ F) = l.
Proof. by move=> /[dup] /cvgP /cvg_unique; apply. Qed.

Lemma lim_near_cst {U} {F} {FF : ProperFilter F} (l : T) (f : U -> T) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. by move=> /cvg_near_cst/cvg_lim. Qed.

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) :
   lim ((fun _ : U => k) @ F) = k.
Proof. by apply: cvg_lim; apply: cvg_cst. Qed.

Lemma cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> T -> Prop) (l : T) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
move=> f_prop fl; apply: get_unique => // l' fl'; exact: cvgi_unique _ fl' fl.
Qed.

End hausdorff_ptopologicalType.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvg_lim`")]
Notation cvg_map_lim := cvg_lim (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgi_lim`")]
Notation cvgi_map_lim := cvgi_lim (only parsing).

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
by apply/closure_subset/disjoints_subset; rewrite setIC.
Qed.

Lemma compact_normal_local (K : set T) : hausdorff_space T -> compact K ->
  forall A : set T, A `<=` K^° -> {for A, normal_space}.
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
  near=> y U => /=; have Dy : D^° y by exact: (near nD _).
  have UclD : U `<=` closure (~` closure D).
    exact: (near (small_set_sub snBD) U).
  move=> Uy; have [z [/= + Dz]] := UclD _ Uy _ Dy.
  by apply; exact: subset_closure.
case/(_ _ _ _ _ cvP) : cvA => R /= [RA Rmono [U RU] RBx].
have [V /set_nbhsP [W [oW cBW WV] clVU]] := RA _ RU; exists (~` W).
  apply/set_nbhsP; exists (~` closure W); split.
  - exact/closed_openC/closed_closure.
  - by move=> y /(RBx _ RU) + Wy; apply; exact/clVU/(closure_subset WV).
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
  rewrite eqEsubset; split => z; case; first by left.
  + by rewrite -setU1itv // => -[->|]; [left| right].
  + by left.
  + by rewrite /V -setU1itv //; right; right.
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

(* This section proves that uniform spaces, with a countable base for their
   entourage, are metrizable. The definition of this metric is rather arcane,
   and the proof is tough. That's ok because the resulting metric is not
   intended to be used explicitly. Instead, this is typically used in
   applications that do not depend on the metric:
   - `metric spaces are T4`
   - `in metric spaces, compactness and sequential compactness agree`
   - infinite products of metric spaces are metrizable
*)
Module countable_uniform.
Section countable_uniform.
Local Open Scope relation_scope.
Context {R : realType} {T : uniformType}.

Hypothesis cnt_unif : @countable_uniformity T.

Let f_ := projT1 (cid2 (iffLR countable_uniformityP cnt_unif)).

Local Lemma countableBase : forall A, entourage A -> exists N, f_ N `<=` A.
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

Let entF : forall n, entourage (f_ n).
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

(* Step 1:
   We build a nicer base `g` for `entourage` with better assumptions than `f`
   - each (g_ n) is symmetric
   - the sets (g_ n) are nested downward
   - g_ n.+1 \o g_ n.+1 \o g_ n.+1 `<=` g_ n says the sets descend `quickly`
 *)

Local Fixpoint g_ n : set (T * T) :=
  if n is n.+1 then let W := split_ent (split_ent (g_ n)) `&` f_ n in W `&` W^-1
  else [set: T*T].

Let entG n : entourage (g_ n).
Proof.
elim: n => /=; first exact: entourageT.
by move=> n entg; apply/entourage_invI; exact: filterI.
Qed.

Local Lemma symG n : (g_ n)^-1 = g_ n.
Proof.
by case: n => // n; rewrite eqEsubset; split; case=> ? ?; rewrite /= andC.
Qed.

Local Lemma descendG1 n : g_ n.+1 `<=` g_ n.
Proof.
apply: subIset; left; apply: subIset; left; apply: subset_trans.
  by apply: split_ent_subset; exact: entourage_split_ent.
by apply: subset_trans; last exact: split_ent_subset.
Qed.

Local Lemma descendG n m : (m <= n)%N -> g_ n `<=` g_ m.
Proof.
elim: n; rewrite ?leqn0; first by move=>/eqP ->.
move=> n IH; rewrite leq_eqVlt ltnS => /orP [/eqP <- //|] /IH.
by apply: subset_trans; exact: descendG1.
Qed.

Local Lemma splitG3 n : g_ n.+1 \; g_ n.+1 \; g_ n.+1 `<=` g_ n.
Proof.
suff g2split : g_ n.+1 \; g_ n.+1 `<=` split_ent (g_ n).
  apply: subset_trans; last exact: subset_split_ent (entG n).
  apply: set_compose_subset (g2split); rewrite -[_ n.+1]set_compose_diag.
  apply: subset_trans g2split; apply: set_compose_subset => //.
  by move=> [_ _] [z _] [<- <-]; exact: entourage_refl.
apply: subset_trans; last exact: subset_split_ent.
by apply: set_compose_subset; apply: subIset; left; apply: subIset; left.
Qed.

Local Lemma gsubf n : g_ n.+1 `<=` f_ n.
Proof. by apply: subIset; left; apply: subIset; right. Qed.

Local Lemma countableBaseG A : entourage A -> exists N, g_ N `<=` A.
Proof.
move=> /countableBase [N] fnA; exists N.+1.
by apply: subset_trans fnA; exact: gsubf.
Qed.

(* Step 2.
   We build a sensible notion of balls for our metric.
   The naive attempt,
                     `ball x e y := g_ (distN e) (x,y))
   doesn't respect triangle inequality. We need to cook triangle inequality
   into the balls themselves. So we define balls in terms of steps:
      `ball x e y := there are n steps x_0 = x,...,x_i,..., x_n.+1 = y and
                     e_1,...,e_n such that
                           g_ (distN e_i) (x_i,x_i+1)
                                    and
                               sum (e_i) = e
*)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Definition distN (e : R) : nat := `|Num.floor e^-1|%N.

Local Lemma distN0 : distN 0 = 0%N.
Proof. by rewrite /distN invr0 floor0. Qed.

Local Lemma distN_nat (n : nat) : distN n%:R^-1 = n.
Proof.
rewrite /distN invrK.
apply/eqP; rewrite -(@eqr_nat R) natr_absz ger0_norm ?floor_ge0//.
by rewrite -intrEfloor intrEge0.
Qed.

Local Lemma distN_le e1 e2 : e1 > 0 -> e1 <= e2 -> (distN e2 <= distN e1)%N.
Proof.
move=> e1pos e1e2; rewrite /distN; apply: lez_abs2.
  by rewrite floor_ge0 ltW// invr_gt0 (lt_le_trans _ e1e2).
by rewrite floor_le// lef_pV2 ?invrK ?invr_gt0//; exact: (lt_le_trans _ e1e2).
Qed.

Local Fixpoint n_step_ball n x e z :=
  if n is n.+1 then exists y d1 d2,
    [/\ n_step_ball n x d1 y,
        0 < d1,
        0 < d2,
        g_ (distN d2) (y, z) &
        d1 + d2 = e]
  else e > 0 /\ g_ (distN e) (x, z).

Local Definition step_ball x e z := exists i, (n_step_ball i x e z).

Local Lemma n_step_ball_pos n x e z : n_step_ball n x e z -> 0 < e.
Proof.
by case: n => [[]|] // n; case=> [?] [?] [?] [] ? ? ? ? <-; exact: addr_gt0.
Qed.

Local Lemma step_ball_pos x e z : step_ball x e z -> 0 < e.
Proof. by case => ?; exact: n_step_ball_pos. Qed.

Local Lemma entourage_nball e :
  0 < e -> entourage [set xy | step_ball xy.1 e xy.2].
Proof.
move=> epos; apply: (@filterS _ _ _ (g_ (distN e))) => // [[x y]] ?.
by exists 0%N.
Qed.

Local Lemma n_step_ball_center x e : 0 < e -> n_step_ball 0 x e x.
Proof. by move=> epos; split => //; exact: entourage_refl. Qed.

Local Lemma step_ball_center x e : 0 < e -> step_ball x e x.
Proof. by move=> epos; exists 0%N; apply: n_step_ball_center. Qed.

Local Lemma n_step_ball_triangle n m x y z d1 d2 :
  n_step_ball n x d1 y ->
  n_step_ball m y d2 z ->
  n_step_ball (n + m).+1 x (d1 + d2) z.
Proof.
move: n z d2; elim: m => [n z d2 Nxy [? ?]|n IH m z d2 Oxy].
  by exists y, d1, d2; split; rewrite ?addn0 // (n_step_ball_pos Nxy).
move=> [w] [e1] [e2] [Oyw ? ? ? <-].
exists w, (d1 + e1), e2; rewrite addnS addrA.
split => //; last by rewrite addr_gt0//; exact: n_step_ball_pos Oxy.
by case: (IH m w e1 Oxy Oyw) => t [e3] [e4] [] Oxt ? ? ? <-; exists t, e3, e4.
Qed.

Local Lemma step_ball_triangle x y z d1 d2 :
  step_ball x d1 y -> step_ball y d2 z -> step_ball x (d1 + d2) z.
Proof.
move=> [n Oxy] [m Oyz]; exists (n + m).+1.
exact: n_step_ball_triangle Oxy Oyz.
Qed.

Local Lemma n_step_ball_sym n x y e :
  n_step_ball n x e y -> n_step_ball n y e x.
Proof.
move: x y e; elim: n; first by move=> ? ? ?; rewrite /= -{1}symG.
move=> n IH x y e [t] [d1] [d2] [] /IH Oty ? ?.
rewrite addrC -symG -[n]add0n => gty <-; apply: (n_step_ball_triangle _ Oty).
by split => //; exact: gty.
Qed.

Local Lemma step_ball_sym x y e : step_ball x e y -> step_ball y e x.
Proof. by case=> n /n_step_ball_sym ?; exists n. Qed.

(* Step 3:
   We prove that step_ball respects the original entourage. This requires an
   induction on the length of the steps, which is pretty tricky. The central
   lemma is `split_n_step_ball`, which lets us break a list into parts three
   parts as: half + one_step + half. Then our we can break apart our n +1 path

                         nlong + one_step
   into
                  (half + one_step + half) + one_step
                                =
                  half + one_step + (half + one_step)

   and we can we can use our (strong) induction hypothesis.
   And lastly we finish with splitG3.
*)

Local Lemma n_step_ball_le n x e1 e2 :
  e1 <= e2 -> n_step_ball n x e1 `<=` n_step_ball n x e2.
Proof.
move: x e1 e2; elim: n.
  move=> x e1 e2 e1e2 y [?] gxy; split; first exact: (lt_le_trans _ e1e2).
  by apply: descendG; last (exact: gxy); exact: distN_le.
move=> n IH x e1 e2 e1e2 z [y] [d1] [d2] [] /IH P d1pos d2pos gyz d1d2e1.
exists y, (e2 - d2), d2; split => //.
- by apply: P; rewrite lerBrDr d1d2e1.
- by apply: lt_le_trans d1pos _; rewrite lerBrDr d1d2e1.
- by rewrite subrK.
Qed.

Local Lemma step_ball_le x e1 e2 :
  e1 <= e2 -> step_ball x e1 `<=` step_ball x e2.
Proof. by move=> e1e2 ? [n P]; exists n; exact: (n_step_ball_le e1e2). Qed.

Local Lemma distN_half (n : nat) : n.+1%:R^-1 / (2:R) <= n.+2%:R^-1.
Proof.
rewrite -invrM //; [|exact: unitf_gt0 |exact: unitf_gt0].
rewrite lef_pV2 ?posrE // -?natrM ?ler_nat -addn1 -addn1 -addnA mulnDr.
by rewrite muln1 leq_add2r leq_pmull.
Qed.

Local Lemma split_n_step_ball n x e1 e2 z :
  0 < e1 -> 0 < e2 -> n_step_ball n.+1 x (e1 + e2) z ->
    exists t1 t2 a b,
    [/\
      n_step_ball a x e1 t1,
      n_step_ball 0 t1 (e1 + e2) t2,
      n_step_ball b t2 e2 z &
      (a + b = n)%N
    ].
Proof.
move: e1 e2 x z; elim: n.
  move=> e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Oxy ? ? gd2yz deE.
  case: (pselect (e1 <= d1)).
    move=> e1d1; exists x, y, 0%N, 0%N; split.
    - exact: n_step_ball_center.
    - apply: n_step_ball_le; last exact: Oxy.
      by rewrite -deE lerDl; apply: ltW.
    - apply: (@n_step_ball_le _ _ d2); last by split.
      rewrite -[e2]addr0 -(subrr e1) addrA -lerBlDr opprK [leLHS]addrC.
      by rewrite [e2 + _]addrC -deE; exact: lerD.
    - by rewrite addn0.
  move=> /negP; rewrite -ltNge//.
  move=> e1d1; exists y, z, 0%N, 0%N; split.
  - by apply: n_step_ball_le; last (exact: Oxy); exact: ltW.
  - rewrite -deE; apply: (@n_step_ball_le _ _ d2) => //.
    by rewrite lerDr; apply: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
move=> n IH e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Od1xy d1pos d2pos gd2yz deE.
case: (pselect (e2 <= d2)).
  move=> e2d2; exists y, z, n.+1, 0%N; split.
  - apply: (@n_step_ball_le _ _ d1); rewrite // -[e1]addr0 -(subrr e2) addrA.
    by rewrite -deE -lerBlDr opprK lerD.
  - apply: (@n_step_ball_le _ _ d2); last by split.
    by rewrite -deE lerDr; exact: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
have d1E' : d1 = e1 + (e2 - d2) by rewrite addrA -deE addrK.
move=> /negP; rewrite -ltNge// => d2lee2.
  case: (IH e1 (e2 - d2) x y); rewrite ?subr_gt0 // -d1E' //.
  move=> t1 [t2] [c1] [c2] [] Oxy1 gt1t2 t2y <-.
  exists t1, t2, c1, c2.+1; split => //.
  - by apply: (@n_step_ball_le _ _ d1); rewrite -?deE // ?lerDl; exact: ltW.
  - by exists y, (e2 - d2), d2; split; rewrite // ?subr_gt0// subrK.
  - by rewrite addnS.
Qed.

Local Lemma n_step_ball_le_g x n :
  n_step_ball 0 x n%:R^-1 `<=` [set y | g_ n (x,y)].
Proof. by move=> y [] ?; rewrite distN_nat. Qed.

Local Lemma subset_n_step_ball n x N :
  n_step_ball n x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof.
move: N x; elim: n {-2}n (leqnn n) => n.
  rewrite leqn0 => /eqP -> N x; apply: subset_trans.
    exact: n_step_ball_le_g.
  by move=> y ?; exact: descendG.
move=> IH1 + + N x1 x4; case.
  by move=> ? [?] P; apply: descendG _ P; rewrite distN_nat.
move=> l ln1 Ox1x4.
case: (@split_n_step_ball l x1 (N.+1%:R^-1/2) (N.+1%:R^-1/2) x4) => //.
  by rewrite -splitr.
move=> x2 [x3] [l1] [l2] [] P1 [? +] P3 l1l2; rewrite -splitr distN_nat => ?.
have l1n : (l1 <= n)%N by rewrite (leq_trans (leq_addr l2 l1))// l1l2 -ltnS.
have l2n : (l2 <= n)%N by rewrite (leq_trans (leq_addl l1 l2))// l1l2 -ltnS.
apply: splitG3; exists x3; [exists x2 => //|].
  by move/(n_step_ball_le (distN_half N))/(IH1 _ l1n) : P1.
by move/(n_step_ball_le (distN_half N))/(IH1 _ l2n) : P3.
Qed.

Local Lemma subset_step_ball x N :
  step_ball x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof. by move=> y [] n; exact: subset_n_step_ball. Qed.

Local Lemma step_ball_entourage : entourage = entourage_ step_ball.
Proof.
rewrite predeqE => E; split; first last.
  by case=> e /= epos esubE; apply: (filterS esubE); exact: entourage_nball.
move=> entE; case: (countableBase entE) => N fN.
exists N.+2%:R^-1; first by rewrite /= invr_gt0.
apply: (subset_trans _ fN); apply: subset_trans; last apply: gsubf.
by case=> x y /= N1ball; apply: (@subset_step_ball x N.+1).
Qed.

Definition type : Type := let _ := countableBase in let _ := entF in T.

#[export] HB.instance Definition _ := Uniform.on type.
#[export] HB.instance Definition _ := Uniform_isPseudoMetric.Build R type
  step_ball_center step_ball_sym step_ball_triangle step_ball_entourage.
#[export] HB.instance Definition _ {q : Pointed T} :=
  Pointed.copy type (Pointed.Pack q).

Lemma countable_uniform_bounded (x y : T) : @ball _ type x 2 y.
Proof.
rewrite /ball; exists O%N; rewrite /n_step_ball; split; rewrite // /distN.
rewrite [X in `|X|%N](_ : _ = 0) ?absz0//.
apply/eqP; rewrite -[_ == _]negbK; rewrite floor_neq0 negb_or -?ltNge -?leNgt.
by apply/andP; split => //; rewrite invf_lt1 //= ltrDl.
Qed.

End countable_uniform.

Module Exports. HB.reexport. End Exports.
End countable_uniform.
Export countable_uniform.Exports.

Notation countable_uniform := countable_uniform.type.

Definition sup_pseudometric (R : realType) (T : Type) (Ii : Type)
  (Tc : Ii -> PseudoMetric R T) (Icnt : countable [set: Ii]) : Type := T.

Section sup_pseudometric.
Variable (R : realType) (T : choiceType) (Ii : Type).
Variable (Tc : Ii -> PseudoMetric R T).

Hypothesis Icnt : countable [set: Ii].

Local Notation S := (sup_pseudometric Tc Icnt).

Let TS := fun i => PseudoMetric.Pack (Tc i).

Let countable_uniformityT := @countable_sup_ent T Ii Tc Icnt
  (fun i => @countable_uniformity_metric _ (TS i)).

HB.instance Definition _ : PseudoMetric R S :=
  PseudoMetric.on (countable_uniform countable_uniformityT).

End sup_pseudometric.

Module gauge.
Section gauge.
Local Open Scope relation_scope.

Let split_sym {T : uniformType} (W : set (T * T)) :=
  (split_ent W) `&` (split_ent W)^-1.

Section entourage_gauge.
Context {T : uniformType} (E : set (T * T)) (entE : entourage E).

Definition gauge :=
  filter_from [set: nat] (fun n => iter n split_sym (E `&` E^-1)).

Lemma iter_split_ent j : entourage (iter j split_sym (E `&` E^-1)).
Proof. by elim: j => [|i IH]; exact: filterI. Qed.

Lemma gauge_ent A : gauge A -> entourage A.
Proof.
case=> n; elim: n A; first by move=> ? _ /filterS; apply; apply: filterI.
by move=> n ? A _ /filterS; apply; apply: filterI; have ? := iter_split_ent n.
Qed.

Lemma gauge_filter : Filter gauge.
Proof.
apply: filter_from_filter; first by exists 0%N.
move=> i j _ _; wlog ilej : i j / (i <= j)%N.
  by move=> WH; have [|/ltnW] := leqP i j;
    [|rewrite (setIC (iter _ _ _))]; exact: WH.
exists j => //; rewrite subsetI; split => //; elim: j i ilej => [i|j IH i].
  by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /predU1P[<-//|/ltnSE/IH]; apply: subset_trans.
by move=> x/= [jx _]; apply: split_ent_subset => //; exact: iter_split_ent.
Qed.

Lemma gauge_refl A : gauge A -> diagonal `<=` A.
Proof.
case=> n _; apply: subset_trans => -[_ a]/diagonalP ->.
by apply: entourage_refl; exact: iter_split_ent.
Qed.

Lemma gauge_inv A : gauge A -> gauge A^-1.
Proof.
case=> n _ EA; apply: (@filterS _ _ _ (iter n split_sym (E `&` E^-1))).
- exact: gauge_filter.
- by case: n EA; last move=> n; move=> EA [? ?] [/=] ? ?; exact: EA.
- by exists n .
Qed.

Lemma gauge_split A : gauge A -> exists2 B, gauge B & B \; B `<=` A.
Proof.
case => n _ EA; exists (iter n.+1 split_sym (E `&` E^-1)); first by exists n.+1.
apply: subset_trans EA; apply: subset_trans; first last.
  by apply: subset_split_ent; exact: iter_split_ent.
by case=> a c [b] [] ? ? [] ? ?; exists b.
Qed.

Let gauged : Type := T.

HB.instance Definition _ := Choice.on gauged.
HB.instance Definition _ :=
  @isUniform.Build gauged gauge gauge_filter gauge_refl gauge_inv gauge_split.

Lemma gauge_countable_uniformity : countable_uniformity gauged.
Proof.
exists [set iter n split_sym (E `&` E^-1) | n in [set: nat]].
split; [exact: card_image_le | by move=> W [n] _ <-; exists n|].
by move=> D [n _ ?]; exists (iter n split_sym (E `&` E^-1)).
Qed.

Definition type := countable_uniform.type gauge_countable_uniformity.
End entourage_gauge.

End gauge.
Module Exports. HB.reexport. End Exports.
End gauge.
Export gauge.Exports.

Lemma uniform_pseudometric_sup {R : realType} {T : puniformType} :
    @entourage T = @sup_ent T {E : set (T * T) | @entourage T E}
  (fun E => Uniform.class (@gauge.type T (projT1 E) (projT2 E))).
Proof.
rewrite eqEsubset; split => [E entE|E].
  exists E => //=.
  pose pe : {classic {E0 : set (T * T) | _}} * _ := (exist _ E entE, E).
  have entPE : `[< @entourage (gauge.type entE) E >].
    by apply/asboolP; exists 0%N => // ? [].
  exists (fset1 (exist _ pe entPE)) => //=; first by move=> ?; rewrite in_setE.
  by rewrite set_fset1 bigcap_set1.
case=> W /= [/= J] _ <- /filterS; apply; apply: filter_bigI => -[] [] [] /= D.
move=> entD G /[dup] /asboolP [n _ + _ _] => /filterS; apply.
exact: gauge.iter_split_ent.
Qed.

Section perfect_sets.

Implicit Types (T : topologicalType).

Definition perfect_set {T} (A : set T) := closed A /\ limit_point A = A.

Lemma perfectTP {T} : perfect_set [set: T] <-> forall x : T, ~ open [set x].
Proof.
split.
  case=> _; rewrite eqEsubset; case=> _ + x Ox => /(_ x I [set x]).
  by case; [by apply: open_nbhs_nbhs; split |] => y [+ _] => /[swap] -> /eqP.
move=> NOx; split; [exact: closedT |]; rewrite eqEsubset; split => x // _.
move=> U; rewrite nbhsE; case=> V [] oV Vx VU.
have Vnx: V != [set x] by apply/eqP => M; apply: (NOx x); rewrite -M.
have /existsNP [y /existsNP [Vy Ynx]] : ~ forall y, V y -> y = x.
  move/negP: Vnx; apply: contra_not => Vxy; apply/eqP; rewrite eqEsubset.
  by split => // ? ->.
by exists y; split => //; [exact/eqP | exact: VU].
Qed.

Lemma perfectTP_ex {T} : perfect_set [set: T] <->
  forall (U : set T), open U -> U !=set0 ->
  exists x y, [/\ U x, U y & x != y] .
Proof.
apply: (iff_trans perfectTP); split.
  move=> nx1 U oU [] x Ux; exists x.
  have : U <> [set x] by move=> Ux1; apply: (nx1 x); rewrite -Ux1.
  apply: contra_notP => /not_existsP/contrapT=> Uyx; rewrite eqEsubset.
  by split => [y Uy|? ->//]; have /not_and3P[//|//|/negP/negPn/eqP] := Uyx y.
move=> Unxy x Ox; have [] := Unxy _ Ox; first by exists x.
by move=> y [] ? [->] -> /eqP.
Qed.

End perfect_sets.

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
