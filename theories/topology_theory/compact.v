(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical.
From mathcomp Require Import itv reals topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure.

(**md**************************************************************************)
(* # Compactness                                                              *)
(* This file provides various formulations of compactness, and some theory.   *)
(*                                                                            *)
(* ```                                                                        *)
(*                  cluster F == set of cluster points of F                   *)
(*                    compact == set of compact sets w.r.t. the filter-based  *)
(*                               definition of compactness                    *)
(*              near_covering == a reformulation of covering compact better   *)
(*                               suited for use with `near`                   *)
(*       near_covering_within == equivalent definition of near_covering       *)
(*             compact_near F == the filter F contains a closed compact set   *)
(*               precompact A == A is contained in a closed compact set       *)
(*          locally_compact A == every point in A has a compact (and closed)  *)
(*                               neighborhood                                 *)
(*  finite_subset_cover D F A == the family of sets F is a cover of A         *)
(*                               for a finite number of indices in D          *)
(*              cover_compact == set of compact sets w.r.t. the open          *)
(*                               cover-based definition of compactness        *)
(*          open_fam_of A D f == the family of f indexed by D restricted to A *)
(*                               is a family of open sets                     *)
(*        closed_fam_of A D f == the family of f indexed by D restricted to A *)
(*                               is a family of closed sets                   *)
(*                                                                            *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Compact.
Context {T : topologicalType}.

Definition cluster (F : set_system T) := [set p : T | F `#` nbhs p].

Lemma cluster_nbhs t : cluster (nbhs t) t.
Proof. by move=> A B /nbhs_singleton At /nbhs_singleton Bt; exists t. Qed.

Lemma clusterEonbhs F : cluster F = [set p | F `#` open_nbhs p].
Proof. by under eq_fun do rewrite -meets_openr. Qed.

Lemma clusterE F : cluster F = \bigcap_(A in F) (closure A).
Proof. by rewrite predeqE => p; split=> cF ????; apply: cF. Qed.

Lemma closureEcluster E : closure E = cluster (globally E).
Proof. by rewrite closureEnbhs. Qed.

Lemma cvg_cluster F G : F --> G -> cluster F `<=` cluster G.
Proof. by move=> sGF p Fp P Q GP Qp; apply: Fp Qp; apply: sGF. Qed.

Lemma cluster_cvgE F :
  Filter F ->
  cluster F = [set p | exists2 G, ProperFilter G & G --> p /\ F `<=` G].
Proof.
move=> FF; have [F0|nF0] := pselect (F set0).
  have -> : cluster F = set0.
    by rewrite -subset0 clusterE => x /(_ set0 F0); rewrite closure0.
  by apply/esym; rewrite -subset0 => p [? PG [_ /(_ set0 F0)]]; apply PG.
rewrite predeqE => p; have PF : ProperFilter F by [].
split=> [clFp|[G Gproper [cvGp sFG]] A B]; last first.
  by move=> /sFG GA /cvGp GB; apply: (@filter_ex _ G); apply: filterI.
exists (filter_from (\bigcup_(A in F) [set A `&` B | B in nbhs p]) id).
  apply: filter_from_proper; last first.
    by move=> _ [A FA [B p_B <-]]; have := clFp _ _ FA p_B.
  apply: filter_from_filter.
    exists setT; exists setT; first exact: filterT.
    by exists setT; [apply: filterT|rewrite setIT].
  move=> _ _ [A1 FA1 [B1 p_B1 <-]] [A2 FA2 [B2 p_B2 <-]].
  exists (A1 `&` B1 `&` (A2 `&` B2)) => //; exists (A1 `&` A2).
    exact: filterI.
  by exists (B1 `&` B2); [apply: filterI|rewrite setIACA].
split.
  move=> A p_A; exists A => //; exists setT; first exact: filterT.
  by exists A => //; rewrite setIC setIT.
move=> A FA; exists A => //; exists A => //; exists setT; first exact: filterT.
by rewrite setIT.
Qed.

Lemma closureEcvg (E : set T):
  closure E =
  [set p | exists2 G, ProperFilter G & G --> p /\ globally E `<=` G].
Proof. by rewrite closureEcluster cluster_cvgE. Qed.

Definition compact A := forall (F : set_system T),
  ProperFilter F -> F A -> A `&` cluster F !=set0.

Lemma compact0 : compact set0.
Proof. by move=> F FF /filter_ex []. Qed.

Lemma subclosed_compact (A B : set T) :
  closed A -> compact B -> A `<=` B -> compact A.
Proof.
move=> Acl Bco sAB F Fproper FA.
have [|p [Bp Fp]] := Bco F; first exact: filterS FA.
by exists p; split=> //; apply: Acl=> C Cp; apply: Fp.
Qed.

Typeclasses Opaque within.
Global Instance within_nbhs_proper (A : set T) p :
  infer (closure A p) -> ProperFilter (within A (nbhs p)).
Proof.
move=> clAp; apply: Build_ProperFilter_ex => B.
by move=> /clAp [q [Aq AqsoBq]]; exists q; apply: AqsoBq.
Qed.

Lemma compact_set1 (x : T) : compact [set x].
Proof.
move=> F PF Fx; exists x; split; first by [].
move=> P B nbhsB; exists x; split; last exact: nbhs_singleton.
suff [y [Py <-//]] : P `&` [set x] !=set0.
by apply: filter_ex; [exact: PF| exact: filterI].
Qed.

Lemma compact_closedI (A B : set T) :
  compact A -> closed B -> compact (A `&` B).
Proof.
move=> cptA clB F PF FAB; have FA : F A by move: FAB; exact: filterS.
(have FB : F B by move: FAB; apply: filterS); have [x [Ax]] := cptA F PF FA.
move=> /[dup] clx; rewrite {1}clusterE => /(_ (closure B)); move: clB.
by rewrite closure_id => /[dup] + <- => <- /(_ FB) Bx; exists x.
Qed.
End Compact.

Section near_covering.
Context {X : topologicalType}.

Definition near_covering (K : set X) :=
  forall (I : Type) (F : set_system I) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, P i x') ->
  \near F, K `<=` P F.

Let near_covering_compact : near_covering `<=` compact.
Proof.
move=> K locK F PF FK; apply/set0P/eqP=> KclstF0; case: (PF) => + FF; apply.
rewrite -(setICr K); apply: filterI => //.
have /locK : forall x, K x ->
    \forall x' \near x & i \near powerset_filter_from F, (~` i) x'.
  move=> x Kx; have : ~ cluster F x.
    by apply: contraPnot KclstF0 => clstFx; apply/eqP/set0P; exists x.
  move=> /existsNP [U /existsNP [V /not_implyP [FU /not_implyP [nbhsV]]]] UV0.
  near=> x' W => //= => Wx'; apply: UV0; exists x'.
  by split; [exact: (near (small_set_sub FU) W) | exact: (near nbhsV x')].
case=> G [GF Gdown [U GU]] GP; apply: (@filterS _ _ _ U); last exact: GF.
by move=> y Uy Ky; exact: (GP _ GU y Ky).
Unshelve. all: end_near. Qed.

Let compact_near_covering : compact `<=` near_covering.
Proof.
move=> K cptK I F P FF cover.
pose badPoints := fun U => K `\` [set x | K x /\ U `<=` P ^~ x].
pose G := filter_from F badPoints.
have FG : Filter G.
  apply: filter_from_filter; first by exists setT; exact: filterT.
  move=> L R FL FR; exists (L `&` R); first exact: filterI.
  rewrite /badPoints /= !setDIr !setDv !set0U -setDUr; apply: setDS.
  by move=> ? [|] => + ? [? ?]; exact.
have [[V FV]|G0] := pselect (G set0).
  rewrite subset0 setD_eq0 => subK.
  by apply: (@filterS _ _ _ V) => // ? ? ? /subK [?]; exact.
have PG : ProperFilter G by [].
have GK : G K by exists setT; [exact: filterT | move=> ? []].
case: (cptK _ PG GK) => x [Kx].
have [[/= U1 U2] [U1x FU2 subP]] := cover x Kx.
have GP : G (badPoints (P ^~ x `&` U2)).
  apply: filterI => //; exists (P ^~ x `&` U2); last by move=> ? [].
  near=> i; split; last exact: (near FU2 i).
  by apply: (subP (x, i)); split; [exact: nbhs_singleton|exact: (near FU2 i)].
move=> /(_ _ _ GP U1x) => [[x'[]]][] Kx' /[swap] U1x'.
by case; split => // i [? ?]; exact: (subP (x', i)).
Unshelve. end_near. Qed.

Lemma compact_near_coveringP A : compact A <-> near_covering A.
Proof.
by split; [exact: compact_near_covering| exact: near_covering_compact].
Qed.

Definition near_covering_within (K : set X) :=
  forall (I : Type) (F : set_system I) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, K x' -> P i x') ->
  \near F, K `<=` P F.

Lemma near_covering_withinP (K : set X) :
  near_covering_within K <-> near_covering K.
Proof.
split => cvrW I F P FF cvr; near=> i;
    (suff: K `<=` fun q : X => K q -> P i q by move=> + k Kk; exact); near: i.
  by apply: cvrW => x /cvr; apply: filter_app; near=> j.
have := cvrW _ _ (fun i q => K q -> P i q) FF.
by apply => x /cvr; apply: filter_app; near=> j => + ?; apply.
Unshelve. all: by end_near. Qed.

End near_covering.

Lemma ultra_cvg_clusterE (T : topologicalType) (F : set_system T) :
  UltraFilter F -> cluster F = [set p | F --> p].
Proof.
move=> FU; rewrite predeqE => p; split.
  by rewrite cluster_cvgE => - [G GF [cvGp /max_filter <-]].
by move=> cvFp; rewrite cluster_cvgE; exists F; [apply: ultra_proper|split].
Qed.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : set_system T,
  UltraFilter F -> F A -> A `&` [set p | F --> p] !=set0].
Proof.
rewrite predeqE => A; split=> Aco F FF FA.
  by have /Aco [p [?]] := FA; rewrite ultra_cvg_clusterE; exists p.
have [G [GU sFG]] := ultraFilterLemma FF.
have /Aco [p [Ap]] : G A by apply: sFG.
rewrite /= -[_ --> p]/([set _ | _] p) -ultra_cvg_clusterE.
by move=> /(cvg_cluster sFG); exists p.
Qed.

Section Precompact.
Context {X : topologicalType}.

Lemma compactU (A B : set X) : compact A -> compact B -> compact (A `|` B).
Proof.
rewrite compact_ultra => cptA cptB F UF FAB; rewrite setIUl.
have [/cptA[x AFx]|] := in_ultra_setVsetC A UF; first by exists x; left.
move=> /(filterI FAB); rewrite setIUl setICr set0U => FBA.
have /cptB[x BFx] : F B by apply: filterS FBA; exact: subIsetr.
by exists x; right.
Qed.

Lemma bigsetU_compact I (F : I -> set X) (s : seq I) (P : pred I) :
    (forall i, P i -> compact (F i)) ->
  compact (\big[setU/set0]_(i <- s | P i) F i).
Proof. by move=> ?; elim/big_ind : _ =>//; [exact:compact0|exact:compactU]. Qed.

(** The closed condition here is neccessary to make this definition work in a
    non-hausdorff setting. *)
Definition compact_near (F : set_system X) :=
  exists2 U, F U & compact U /\ closed U.

Definition precompact (C : set X) := compact_near (globally C).

Lemma precompactE (C : set X) : precompact C = compact (closure C).
Proof.
rewrite propeqE; split=> [[B CsubB [cptB cB]]|]; last first.
  move=> clC; exists (closure C) => //; first exact: subset_closure.
  by split => //; exact: closed_closure.
apply: (subclosed_compact _ cptB); first exact: closed_closure.
by move/closure_id: cB => ->; exact: closure_subset.
Qed.

Lemma precompact_subset (A B : set X) :
  A `<=` B -> precompact B -> precompact A.
Proof.
by move=> AsubB [B' B'subB cptB']; exists B' => // ? ?; exact/B'subB/AsubB.
Qed.

Lemma precompact_closed (A : set X) : closed A -> precompact A = compact A.
Proof.
move=> clA; rewrite propeqE; split=> [[B AsubB [ + _ ]]|].
  by move=> /subclosed_compact; exact.
by rewrite {1}(_ : A = closure A) ?precompactE// -closure_id.
Qed.

Definition locally_compact (A : set X) := [locally precompact A].

End Precompact.

Definition finite_subset_cover (I : choiceType) (D : set I)
    U (F : I -> set U) (A : set U) :=
  exists2 D' : {fset I}, {subset D' <= D} & A `<=` cover [set` D'] F.

Section Covers.
Variable T : topologicalType.

Definition cover_compact (A : set T) :=
  forall (I : choiceType) (D : set I) (f : I -> set T),
  (forall i, D i -> open (f i)) -> A `<=` cover D f ->
  finite_subset_cover D f A.

Definition open_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> open (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma cover_compactE : cover_compact =
  [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    open_fam_of A D f ->
      A `<=` cover D f -> finite_subset_cover D f A].
Proof.
rewrite predeqE => A; split=> [Aco I D f [g gop feAg] fcov|Aco I D f fop fcov].
  have gcov : A `<=` \bigcup_(i in D) g i.
    by move=> p /fcov [i Di]; rewrite feAg // => - []; exists i.
  have [D' sD sgcov] := Aco _ _ _ gop gcov.
  exists D' => // p Ap; have /sgcov [i D'i gip] := Ap.
  by exists i => //; rewrite feAg //; have /sD := D'i; rewrite inE.
have Afcov : A `<=` \bigcup_(i in D) (A `&` f i).
  by move=> p Ap; have /fcov [i ??] := Ap; exists i.
have Afop : open_fam_of A D (fun i => A `&` f i) by exists f.
have [D' sD sAfcov] := Aco _ _ _ Afop Afcov.
by exists D' => // p /sAfcov [i ? []]; exists i.
Qed.

Definition closed_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> closed (g i)) &
    forall i, D i -> f i = A `&` g i.

End Covers.

Section PCovers.
Variable T : ptopologicalType.

Lemma compact_In0 :
  compact = [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    closed_fam_of A D f -> finI D f -> \bigcap_(i in D) f i !=set0].
Proof.
rewrite predeqE => A; split=> [Aco I D f [g gcl feAg] finIf|Aco F FF FA].
  case: (pselect (exists i, D i)) => [[i Di] | /asboolP]; last first.
    by rewrite asbool_neg => /forallp_asboolPn D0; exists point => ? /D0.
  have [|p [Ap clfinIfp]] := Aco _ (finI_filter finIf).
    by exists (f i); [apply: finI_from1|rewrite feAg // => ? []].
  exists p => j Dj; rewrite feAg //; split=> //; apply: gcl => // B.
  by apply: clfinIfp; exists (f j); [apply: finI_from1|rewrite feAg // => ? []].
have finIAclF : finI F (fun B => A `&` closure B).
  apply: (@filter_finI _ F) => B FB.
  by apply: filterI => //; apply: filterS FB; apply: subset_closure.
have [|p AclFIp] := Aco _ _ _ _ finIAclF.
  by exists closure=> //; move=> ??; apply: closed_closure.
exists p; split=> [|B C FB p_C]; first by have /AclFIp [] := FA.
by have /AclFIp [_] := FB; move=> /(_ _ p_C).
Qed.

Lemma compact_cover : compact = @cover_compact T.
Proof.
rewrite compact_In0 cover_compactE predeqE => A.
split=> [Aco I D f [g gop feAg] fcov|Aco I D f [g gcl feAg]].
  case: (pselect (exists i, D i)) => [[j Dj] | /asboolP]; last first.
    rewrite asbool_neg => /forallp_asboolPn D0.
    by exists fset0 => // ? /fcov [? /D0].
  apply/exists2P; apply: contrapT.
  move=> /asboolP; rewrite asbool_neg => /forallp_asboolPn sfncov.
  suff [p IAnfp] : \bigcap_(i in D) (A `\` f i) !=set0.
    by have /IAnfp [Ap _] := Dj; have /fcov [k /IAnfp [_]] := Ap.
  apply: Aco.
    exists (fun i => ~` g i) => i Di; first exact/open_closedC/gop.
    rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
      by move=> gip; apply: nfip; rewrite feAg.
    by rewrite feAg // => - [].
  move=> D' sD.
  have /asboolP : ~ A `<=` cover [set` D'] f by move=> sAIf; exact: (sfncov D').
  rewrite asbool_neg => /existsp_asboolPn [p /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ap nUfp].
  by exists p => i D'i; split=> // fip; apply: nUfp; exists i.
case: (pselect (exists i, D i)) => [[j Dj] | /asboolP]; last first.
  by rewrite asbool_neg => /forallp_asboolPn D0 => _; exists point => ? /D0.
apply: contraPP => /asboolP; rewrite asbool_neg => /forallp_asboolPn If0.
apply/asboolP; rewrite asbool_neg; apply/existsp_asboolPn.
have Anfcov : A `<=` \bigcup_(i in D) (A `\` f i).
  move=> p Ap; have /asboolP := If0 p; rewrite asbool_neg => /existsp_asboolPn.
  move=> [i /asboolP]; rewrite asbool_neg => /imply_asboolPn [Di nfip].
  by exists i.
have Anfop : open_fam_of A D (fun i => A `\` f i).
  exists (fun i => ~` g i) => i Di; first exact/closed_openC/gcl.
  rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
    by move=> gip; apply: nfip; rewrite feAg.
  by rewrite feAg // => - [].
have [D' sD sAnfcov] := Aco _ _ _ Anfop Anfcov.
wlog [k D'k] : D' sD sAnfcov / exists i, i \in D'.
  move=> /(_ (D' `|` [fset j])%fset); apply.
  - by move=> k; rewrite !inE => /orP [/sD|/eqP->] //; rewrite inE.
  - by move=> p /sAnfcov [i D'i Anfip]; exists i => //=; rewrite !inE D'i.
  - by exists j; rewrite !inE orbC eq_refl.
exists D' => /(_ sD) [p Ifp].
have /Ifp := D'k; rewrite feAg; last by have /sD := D'k; rewrite inE.
by move=> [/sAnfcov [i D'i [_ nfip]] _]; have /Ifp := D'i.
Qed.

End PCovers.

Lemma finite_compact {X : topologicalType} (A : set X) :
  finite_set A -> compact A.
Proof.
case/finite_setP=> n; elim: n A => [A|n ih A /eq_cardSP[x Ax /ih ?]].
  by rewrite II0 card_eq0 => /eqP ->; exact: compact0.
by rewrite -(setD1K Ax); apply: compactU => //; exact: compact_set1.
Qed.

Lemma clopen_countable {T : ptopologicalType}:
  compact [set: T] -> @second_countable T -> countable (@clopen T).
Proof.
move=> cmpT [B /fset_subset_countable cntB] [obase Bbase].
apply/(card_le_trans _ cntB)/pcard_surjP.
pose f := fun F : {fset set T} => \bigcup_(x in [set` F]) x; exists f.
move=> D [] oD cD /=; have cmpt : cover_compact D.
  by rewrite -compact_cover; exact: (subclosed_compact _ cmpT).
have h (x : T) : exists V : set T, D x -> [/\ B V, nbhs x V & V `<=` D].
  have [Dx|] := pselect (D x); last by move=> ?; exists set0.
  have [V [BV Vx VD]] := Bbase x D (open_nbhs_nbhs (conj oD Dx)).
  exists V => _; split => //; apply: open_nbhs_nbhs; split => //.
  exact: obase.
pose h' := fun z => projT1 (cid (h z)).
have [fs fsD DsubC] : finite_subset_cover D h' D.
  apply: cmpt.
  - by move=> z Dz; apply: obase; have [] := projT2 (cid (h z)) Dz.
  - move=> z Dz; exists z => //; apply: nbhs_singleton.
    by have [] := projT2 (cid (h z)) Dz.
exists [fset h' z | z in fs]%fset.
  move=> U/imfsetP [z /=] /fsD /set_mem Dz ->; rewrite inE.
  by have [] := projT2 (cid (h z)) Dz.
rewrite eqEsubset; split => z.
  case=> y /imfsetP [x /= /fsD/set_mem Dx ->]; move: z.
  by have [] := projT2 (cid (h x)) Dx.
move=> /DsubC /= [y /= yfs hyz]; exists (h' y) => //.
by rewrite set_imfset /=; exists y.
Qed.

Lemma compact_cauchy_cvg {T : puniformType} (U : set T) (F : set_system T) :
  ProperFilter F -> cauchy F -> F U -> compact U -> cvg F.
Proof.
move=> PF cf FU /(_ F PF FU) [x [_ clFx]]; apply: (cvgP x).
apply/cvg_entourageP => E entE.
have : nbhs entourage (split_ent E) by rewrite nbhs_filterE.
move=> /(cf (split_ent E))[] [D1 D2]/= /[!nbhs_simpl] -[FD1 FD2 D1D2E].
have : nbhs x (xsection (split_ent E) x) by exact: nbhs_entourage.
move=> /(clFx _ (xsection (split_ent E) x) FD1)[z [Dz /xsectionP Exz]].
by near=> t; apply/(entourage_split z entE Exz)/D1D2E; split => //; near: t.
Unshelve. all: by end_near. Qed.

Lemma compact_second_countable {R : realType} {T : pseudoPMetricType R} :
  compact [set: T] -> @second_countable T.
Proof.
have npos n : (0:R) < n.+1%:R^-1 by [].
pose f n (z : T): set T := (ball z (PosNum (npos n))%:num)^°.
move=> cmpt; have h n : finite_subset_cover [set: T] (f n) [set: T].
  move: cmpt; rewrite compact_cover; apply.
  - by move=> z _; rewrite /f; exact: open_interior.
  - by move=> z _; exists z => //; rewrite /f /interior; exact: nbhsx_ballx.
pose h' n := cid (iffLR (exists2P _ _) (h n)).
pose h'' n := projT1 (h' n).
pose B := \bigcup_n (f n) @` [set` h'' n]; exists B;[|split].
- apply: bigcup_countable => // n _; apply: finite_set_countable.
  exact/finite_image/ finite_fset.
- by move => ? [? _ [? _ <-]]; exact: open_interior.
- move=> x V /nbhs_ballP [] _/posnumP[eps] ballsubV.
  have [//|N] := @ltr_add_invr R 0%R (eps%:num/2) _; rewrite add0r => deleps.
  have [w wh fx] : exists2 w : T, w \in h'' N & f N w x.
    by have [_ /(_ x) [// | w ? ?]] := projT2 (h' N); exists w.
  exists (f N w); first split => //; first (by exists N).
  apply: (subset_trans _ ballsubV) => z bz.
  rewrite [_%:num]splitr; apply: (@ball_triangle _ _ w).
    by apply: (le_ball (ltW deleps)); apply/ball_sym; apply: interior_subset.
  by apply: (le_ball (ltW deleps)); apply: interior_subset.
Qed.

Lemma clopen_surj {R : realType} {T : pseudoPMetricType R} :
  compact [set: T] -> $|{surjfun [set: nat] >-> @clopen T}|.
Proof.
move=> cmptT.
suff : @clopen T = set0 \/ $|{surjfun [set: nat] >-> @clopen T}|.
  by case => //; rewrite eqEsubset => -[/(_ _ clopenT)].
exact/pfcard_geP/clopen_countable/compact_second_countable.
Qed.
