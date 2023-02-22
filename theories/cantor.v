(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix .
From mathcomp Require Import interval rat fintype finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import fsbigop reals topology sequences real_interval normedtype.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Lemma bool2E : [set: bool] = [set true; false].
Proof.  by rewrite eqEsubset; split => //= [[]] //= _;[left|right]. Qed.

Lemma bool_predE (P : set bool -> Prop) :
  (forall A, P A) = 
  [/\ P set0, P [set true], P [set false] & P [set true; false]].
Proof.
rewrite propeqE; split; first by move=> Pa; split; exact: Pa.
move=> [? ? ? ?] A; have Atf : A `<=` [set true; false] by rewrite -bool2E => ?.
by have := (subset_set2 Atf); case => ->.
Qed.

Canonical cantor_space := 
  product_uniformType (fun (_ : nat) => @discrete_uniformType _ discrete_bool).

Definition countable_nat : countable [set: nat_countType].
Proof. done. Qed.

Canonical cantor_psuedoMetric {R} := 
  @product_pseudoMetricType R _ (fun (_ : nat) => 
    @discrete_pseudoMetricType R _ discrete_bool) countable_nat.

Lemma cantor_space_compact: compact [set: cantor_space].
Proof.
have := (@tychonoff _ (fun (_: nat) => _) _ (fun=> bool_compact)).
by congr (compact _) => //=; rewrite eqEsubset; split => b //=.
Qed.

Lemma cantor_space_hausdorff : hausdorff_space cantor_space.
Proof. apply: hausdorff_product => ?; exact: discrete_hausdorff. Qed.

Section perfect_sets.

Implicit Types (T : topologicalType).
Lemma perfect_set2 {T} : perfect_set [set: T] <->
  forall (U : set T), open U -> U !=set0 -> 
  exists x y, [/\ U x, U y & x != y] .
Proof.

apply: iff_trans; first exact: perfectTP; split.
  move=> nx1 U oU [] x Ux; exists x.
  have : U <> [set x] by move=> Ux1; apply: (nx1 x); rewrite -Ux1.
  apply: contra_notP; move/not_existsP/contrapT=> Uyx; rewrite eqEsubset.
  (split => //; last by move=> ? ->); move=> y Uy; have  /not_and3P := Uyx y.
  by case => // /negP; rewrite negbK => /eqP ->.
move=> Unxy x Ox; have [] := Unxy _ Ox; first by exists x.
by move=> y [] ? [->] -> /eqP.
Qed.

End perfect_sets.

Section clopen.
Definition totally_disconnected (T : topologicalType) :=
  forall (x y : T), x != y -> exists A, A x /\ ~ A y /\ clopen A.


Lemma totally_disconnected_prod (I : choiceType) (T : I -> topologicalType) :
  (forall i, @totally_disconnected (T i)) ->
  totally_disconnected (product_topologicalType T).
Proof.
move=> dctTI /= x y /eqP xneqy.
have [i /eqP /dctTI [A] [] Axi [] nAy coA] : exists i, x i <> y i.
  by apply/existsNP=> W; exact/xneqy/functional_extensionality_dep.
exists (proj i @^-1` A); split;[|split] => //.
by apply: clopen_comp => //; exact: proj_continuous.
Qed.

Lemma totally_disconnected_discrete {T} :
  discrete_space T -> totally_disconnected T.
Proof.
move=> dsct x y /eqP xneqy; exists [set x]; split; [|split] => //.
  by move=> W; apply: xneqy; rewrite W.
by split => //; [exact: discrete_open | exact: discrete_closed].
Qed.

Lemma cantor_totally_disconnected : totally_disconnected cantor_space.
Proof.
by apply: totally_disconnected_prod => _; apply: totally_disconnected_discrete.
Qed.

Lemma cantor_perfect : perfect_set [set: cantor_space].
Proof.
by apply: perfect_diagonal => _; exists (true, false).
Qed. 

Definition countable_basis (T : topologicalType) := exists B, 
  [/\ countable B,
      forall A, B A -> open A &
      forall (x:T) V, nbhs x V -> exists A, B A /\ nbhs x A /\ A `<=` V].

Definition cantor_like (T : topologicalType) :=
  [/\ perfect_set [set: T], 
      compact [set: T],
      hausdorff_space T
      & totally_disconnected T].

Lemma separator_continuous {T: topologicalType} (A : set T) :
  open A -> closed A -> continuous (fun x => x \in A).
Proof.
move=> oA /closed_openC oAc; apply/continuousP; rewrite bool_predE; split => _.
- by rewrite preimage_set0; exact: open0.
- suff -> : (in_mem^~ (mem A) @^-1` [set true] = A) by [].
  rewrite eqEsubset; split => x //=; first by move=> /set_mem.
  by move=> ?; apply/mem_set.
- suff -> : (in_mem^~ (mem A) @^-1` [set false] = ~`A) by [].
  rewrite eqEsubset; split => x //=; last exact: memNset.
  by move=> + /mem_set => ->.
- rewrite -bool2E preimage_setT; exact: openT.
Qed.

Lemma discrete_closed {T : topologicalType} (dsc : discrete_space T) A : 
  @closed T A.
Proof. rewrite -openC; exact: discrete_open. Qed.

Lemma closure_discrete {T : topologicalType} (dsc : discrete_space T) A : 
  @closure T A = A.
Proof. by apply/sym_equal/closure_id; exact: discrete_closed. Qed.

Section totally_disconnected.
Local Open Scope ring_scope.

Lemma totally_disconnected_cvg {T : topologicalType} (x : T) : 
  {for x, totally_disconnected T} -> compact [set: T] ->
  filter_from [set D | D x /\ clopen D] id --> x. 
Proof.
pose F := filter_from [set D | D x /\ open D /\ closed D] id.
have PF : ProperFilter F. 
  apply: filter_from_proper; first apply: filter_from_filter.
  - by exists setT; split => //; split => //; exact: openT.
  - move=> A B [? [] ? ?] [? [] ? ?]; exists (A `&` B) => //.
    by split => //; split; [exact: openI | exact: closedI].
  - by move=> ? [? _]; exists x.
move=> disct cmpT U Ux; rewrite nbhs_simpl -/F; wlog oU : U Ux / open U.
  move: Ux; rewrite /= {1}nbhsE => [][] O Ox OsubU P; apply: (filterS OsubU).
  by apply: P => //; [exact: open_nbhs_nbhs | case: Ox].
have /(iffLR (compact_near_coveringP _)): compact (~`U).
  by apply: (subclosed_compact _ cmpT) => //; exact: open_closedC.
move=> /( _ _ _ (fun C y => ~ C y) (powerset_filter_from_filter PF)); case.
  move=> y nUy; have /disct [C [Cx [] ? [] ? ?]] : x != y. 
    by apply/eqP => E; move: nUy; rewrite -E; apply; apply: nbhs_singleton. 
  exists (~`C, [set U | U `<=` C]); last by move=> [? ?] [? /subsetC]; exact.
  split; first by apply: open_nbhs_nbhs; split => //; exact: closed_openC.
  apply/near_powerset_filter_fromP; first by move=> ? ?; exact: subset_trans.
  by exists C => //; exists C.
by move=> D [] DF Dsub [C] DC /(_ _ DC) /subsetC2/filterS; apply; exact: DF.
Qed.

Lemma clopen_countable {T : topologicalType}: 
  compact [set: T] ->
  countable_basis T ->
  countable (@clopen T).
Proof.
move=> cmpT [B []] /fset_subset_countable cntB obase Bbase.
apply/(card_le_trans _ cntB)/pcard_surjP.
pose f := (fun (F : {fset set T}) => \bigcup_(x in [set` F]) x); exists f.
move=> D [] oD cD /=; have cmpt : cover_compact D. 
  by rewrite -compact_cover; exact: (subclosed_compact _ cmpT).
have h : forall (x : T), exists (V : set T), D x -> B V /\ nbhs x V /\ V `<=` D.
  move=> x; case: (pselect (D x)); last by move=> ?; exists set0.
  by rewrite openE in oD; move=> /oD/Bbase [A[] ? [] ? ?]; exists A.
pose h' := fun z => projT1 (cid (h z)).
have [] := @cmpt T D h'.
- by move=> z Dz; apply: obase; have [] := projT2 (cid (h z)) Dz.
- move=> z Dz; exists z => //; apply: nbhs_singleton. 
  by have [? []] := projT2 (cid (h z)) Dz.
move=> fs fsD DsubC; exists ([fset h' z | z in fs])%fset.
  move=> U/imfsetP [z /=] /fsD /set_mem Dz ->; rewrite inE.
  by have [? []] := projT2 (cid (h z)) Dz.
rewrite eqEsubset; split => z.
  case=> y /imfsetP [x /= /fsD/set_mem Dx ->]; move: z.
  by have [? []] := projT2 (cid (h x)) Dx.
move=> /DsubC /= [y /= yfs hyz]; exists (h' y) => //.
by rewrite set_imfset /=; exists y.
Qed.
Lemma compact_countable_base {R : realType} {T : pseudoMetricType R} : 
  compact [set: T] -> countable_basis T.
Proof.
have npos : forall n, ((0:R) < (n.+1%:R^-1))%R by [].
pose f : nat -> T -> (set T) := fun n z => (ball z (PosNum (npos n))%:num)^°.
move=> cmpt; have h : forall n, finite_subset_cover [set: T] (f n) [set: T].
  move=> n; rewrite compact_cover in cmpt; apply: cmpt.
    by move=> z _; rewrite /f; exact: open_interior.
  move=> z _; exists z => //; rewrite /f/interior; exact: nbhsx_ballx.
pose h' := fun n => (cid (iffLR (exists2P _ _) (h n))).
pose h'' := fun n => projT1 (h' n).
pose B := \bigcup_n (f n) @` [set` (h'' n)]; exists B; split.
- apply: bigcup_countable => // n _; apply: finite_set_countable.
  exact/finite_image/ finite_fset.
- by move=> z [n _ [w /= wn <-]]; exact: open_interior.
- move=> x V /nbhs_ballP [] _/posnumP[eps] ballsubV.
  have [//|N] := @ltr_add_invr R 0%R (eps%:num/2) _; rewrite add0r => deleps.
  have [w [wh fx]] : exists w : T, w \in h'' N /\ f N w x. 
    by have [_ /(_ x) [// | w ? ?]] := projT2 (h' N); exists w.
  exists (f N w); split; first (by exists N); split.
    by apply: open_nbhs_nbhs; split => //; exact: open_interior.
  apply: (subset_trans _ ballsubV) => z bz.
  rewrite [_%:num]splitr; apply: (@ball_triangle _ _ w). 
    by apply: (le_ball (ltW deleps)); apply/ball_sym; apply: interior_subset.
  by apply: (le_ball (ltW deleps)); apply: interior_subset.
Qed.

(* A technique for encoding 'cantor_like' spaces as trees. We build a new
   function 'node' which encodes the homeomorphism to the cantor space.
   Other than the 'tree_map is a homeomorphism', no additinal information is
   will be needed outside this context. So it's OK that the definitions are 
   rather unpleasant *)
Section TreeStructure.
Context {R : realType} {T : pseudoMetricType R}.
Hypothesis cantorT : cantor_like T.
Local Lemma dsctT : @totally_disconnected T.
Proof. by case: cantorT. Qed.
Local Lemma pftT : perfect_set [set: T].
Proof. by case: cantorT. Qed.
Local Lemma cmptT : compact [set: T].
Proof. by case: cantorT. Qed.
Local Lemma hsdfT : @hausdorff_space T.
Proof. by case: cantorT. Qed.

Local Lemma clopen_surj : $|{surjfun [set: nat] >-> @clopen T}|.
Proof. 
suff : (@clopen T = set0 \/ $|{surjfun [set: nat] >-> @clopen T}|).
  by case; rewrite // eqEsubset; case=>/(_ _ clopenT).
by apply/pfcard_geP/clopen_countable/ compact_countable_base; case: cantorT.
Qed.

Let U_ := unsquash clopen_surj.

Local Lemma split_clopen (U : set T) : open U -> U !=set0 -> 
  exists V, clopen V /\ V `&` U !=set0 /\ ~`V `&` U !=set0.
Proof.
move=> oU Un0; have [x [y] [Ux] Uy xny] := (iffLR perfect_set2) pftT U oU Un0.
have [V [?] [?] [? ?]] := dsctT xny; exists V. 
by repeat split => //; [exists x | exists y].
Qed.

Let split_open' (U : set T) : set T := 
  if pselect (open U /\ U !=set0) is left (conj oU n0)
  then projT1 (cid (split_clopen oU n0))
  else set0.

Local Lemma split_openI (U : set T) : 
  open U -> U !=set0 -> split_open' U `&` U !=set0.
Proof.
move=> oU Un0; rewrite /split_open'; case: pselect; last exact: absurd.
by move=> W; case: W => w1 w2; have [? []] := projT2 (cid (split_clopen w1 w2)).
Qed.

Local Lemma split_openIC (U : set T) : 
  open U -> U !=set0 -> ~` (split_open' U) `&` U !=set0.
Proof.
move=> oU Un0; rewrite /split_open'; case: pselect; last exact: absurd.
by move=> W; case: W => w1 w2; have [? []] := projT2 (cid (split_clopen w1 w2)).
Qed.

Local Lemma split_open_clopen (U : set T) : clopen (split_open' U).
Proof.
rewrite/split_open'; case: pselect; last by move=> ?; exact: clopen0.
by case=> w1 w2; have [? []] := projT2 (cid (split_clopen w1 w2)).
Qed.

Local Fixpoint node (pfx: seq bool): set T := 
  match pfx with 
  | nil => setT
  | head :: tail => 
    let Un := U_ (length tail) in
    let Vn := node tail in 
    let Wn := if pselect (Un `&` Vn !=set0 /\ ~` Un `&` Vn !=set0)
      then Un else split_open' Vn in 
    (if head then Wn else ~` Wn) `&` Vn
  end.

Local Lemma node_clopen_n0 pfx : clopen (node pfx) /\ node pfx !=set0.
Proof.
elim: pfx => /=; first (split; last by exists point).
  split; [exact: openT | exact: closedT].
move=> head tail [tail_clopen tailn0]; split; first last.
  case: pselect=> UnI /=; first by case: head; case: UnI.
  case head; first by apply: split_openI => //; case: tail_clopen.
  by apply: split_openIC => //; case: tail_clopen.
apply: clopenI => //.
set Wn := (x in if _ then x else ~` x); suff: clopen Wn.
  by move=> ?; case: head => //; exact: clopenC.
rewrite /Wn; case: pselect => P /=; last apply: split_open_clopen.
exact: funS.
Qed.

Local Lemma node_clopen pfx : clopen (node pfx).
Proof. by have [] := node_clopen_n0 pfx. Qed.

Local Lemma node_n0 pfx : node pfx !=set0.
Proof. by have [] := node_clopen_n0 pfx. Qed.

Local Lemma node_subsetS b pfx : node (b :: pfx) `<=` node pfx.
Proof. by move: b; elim: pfx => //= ? ?. Qed.

Local Lemma nodeUS pfx : node (true :: pfx) `|` node (false :: pfx) = node pfx.
rewrite eqEsubset; split; last by rewrite /= -setIUl setUv setTI.
by rewrite -[node pfx]setUid; apply: setUSS; exact: node_subsetS.
Qed.

Local Lemma nodeIS pfx : node (true :: pfx) `&` node (false :: pfx) = set0.
Proof.
rewrite /=; set W := if _ then _ else _.
by rewrite /= -setIA [~` _ `&` _]setIC setIC -?setIA setICl ?setI0.
Qed.

Local Lemma node_trivIset (n : nat) : trivIset [set pfx | length pfx = n] node. 
Proof.
elim: n.
  by move=> i j /List.length_zero_iff_nil -> /List.length_zero_iff_nil ->.
move=> n IH pfx1 pfx2 /=.
case: pfx1 => // b1 pfx1 /eq_add_S pfx1N.
case: pfx2 => // b2 pfx2 /eq_add_S pfx2N.
case=> x [] [] P1 npfx1 [] P2 npfx2; have pfxE : pfx1 = pfx2. 
  by apply: IH => //; exists x.
rewrite pfxE in P1, P2 *; congr (_ :: _).
have /set0P/eqP : node (b1 :: pfx2) `&` node (b2 :: pfx2) !=set0 by exists x.
by case: {P1 P2} b1; case: b2; rewrite ?nodeIS // setIC nodeIS.
Qed.

Local Lemma nodeT (n : nat) : bigcup [set pfx | length pfx = n] node = setT. 
Proof.
elim: n.
  rewrite (_ : [set pfx | length pfx = 0%N] = [set [::]]) ?bigcup_set1 //.
  rewrite eqEsubset; split => // ?; last by move=> ->. 
  by move/List.length_zero_iff_nil=> ->.
move=> N; rewrite ?eqEsubset; case=> _ IH; split => // x Tx.
have [pfx /= pfxN] := IH _ Tx; rewrite -nodeUS=> pfxX.
have [b bpfxX] : exists b, node (b :: pfx) x.
  by case: pfxX=> ?; [exists true | exists false].
by exists (b :: pfx) => //=; f_equal.
Qed.

Local Lemma nodeUn n pfx : length pfx = S n -> 
  (node pfx `<=` U_ n) \/ (node pfx `&` U_ n == set0).
Proof.
case: pfx => // b pfx /= /eq_add_S pfxN; rewrite pfxN.
case: pselect => /=; case: b => //=; [left | right | |] => //=.
- by rewrite setIC setIA setICr set0I.
- case/not_andP => /set0P/negP; rewrite negbK setIC -setIA => /eqP.
    by move=> ->; rewrite setI0; right.
  by move/subsets_disjoint => ?; left; apply: subIset; right.
- case/not_andP => /set0P/negP; rewrite negbK setIC -setIA => /eqP.
    by move=> ->; rewrite setI0; right.
  by move/subsets_disjoint => ?; left; apply: subIset; right.
Qed.

Let level (n : nat) (b : bool) : set T := 
  bigcup [set pfx | length pfx = n] (fun pfx => node (b :: pfx)).

Local Lemma finite_set_seq (n : nat) : 
  finite_set [set pfx : seq bool | length pfx = n].
Proof.
elim: n.
  rewrite (_ : [set pfx | length pfx = 0%N] = [set [::]]) //.
  rewrite eqEsubset; split => // ?; last by move=> ->. 
  by move/List.length_zero_iff_nil=> ->.
pose L := fun (n:nat) => [set pfx : seq bool | length pfx = n]; move=> n IH.
suff : (L n.+1 = (cons true @` L n) `|` (cons false @` L n)).
  by rewrite /L => - => ->; rewrite finite_setU; split; apply: finite_image.
rewrite eqEsubset; split; rewrite /L.
  by case=> // b pfx /= /eq_add_S pfxn; case: b; [left | right]; exists pfx.
by move=> pfx /= [][] ? <- <-.
Qed.

Local Lemma lvl_clopen (n : nat) (b : bool) : clopen (level n b).
Proof.
move: b; elim: n.
  move=> b; rewrite /level.
  rewrite (_ : [set pfx | length pfx = 0%N] = [set [::]]) ?bigcup_set1 //.
    exact: node_clopen.
  rewrite eqEsubset; split => // ?; last by move=> ->. 
  by move/List.length_zero_iff_nil=> ->.
move=> n IH b; split. 
  by apply: bigcup_open => pfx _; case: (node_clopen (b :: pfx)).
rewrite /level -bigsetU_fset_set.
  by apply: closed_bigsetU => pfx _; case: (node_clopen (b :: pfx)).
exact: finite_set_seq.
Qed.

Let tree_map (x : T) : cantor_space := fun n => x \in level n true.

Local Lemma continuous_tree_map : continuous tree_map.
move=> x; apply/cvg_sup => /= n U /=; rewrite {1}/nbhs /=; case=> ? [][M oM <-].
move=> Mtxn /filterS; apply; apply: separator_continuous.
- by case: (lvl_clopen n true).
- by case: (lvl_clopen n true).
- by rewrite /=/nbhs /=; apply/principal_filterP.
Qed.

Local Lemma closed_tree_map : forall (C : set T), closed C -> closed (tree_map @` C).
move=> C clC; apply: compact_closed; first exact: cantor_space_hausdorff.
apply: continuous_compact; last exact: (subclosed_compact _ cmptT).
exact/continuous_subspaceT/continuous_tree_map.
Qed.

Local Lemma tree_map_node b (z : T) L : node (b :: L) z -> tree_map z (length L) = b.
Proof.
rewrite /tree_map; case: b => // nbz; first by apply: asboolT; exists L.
apply: asboolF; case=> M LMN nMz.
  have L13x : node L `&` node M !=set0.
    exists z; split; apply: node_subsetS; [exact: nbz | exact: nMz].
  have L13E := @node_trivIset (length L) _ M erefl LMN L13x.
  by (suff : set0 z by apply); rewrite -(nodeIS L); split => //; rewrite L13E.
Qed.

Local Lemma tree_map_prefix x y pfxX pfxY : 
  tree_map x = tree_map y -> length pfxX = length pfxY -> 
  node pfxX x -> node pfxY y -> pfxX = pfxY.
Proof.
move=> tmXY; move: pfxY; elim: pfxX.
  by move=> pfxy ln0 _ _; apply/sym_equal/List.length_zero_iff_nil/sym_equal.
move=> b1 L1 IH pfxY; case: pfxY => // b2 L2 /eq_add_S /[dup] LN /IH L12 nx ny. 
f_equal; last by case: nx; case: ny => ? ? ? ?; apply: L12. 
by rewrite -(tree_map_node nx) -(tree_map_node ny) tmXY /length LN.
Qed.

Local Lemma inj_tree_map : set_inj [set: T] tree_map.
Proof.
move=> x y _ _; apply: contra_eq => xNy.
have [V [Vx] [nVy clV]] := dsctT xNy.
have [N UNVE] : exists N, U_ N = V.
  by have [N ? <-] := (@surj _ _ _ _ U_ V clV); exists N.
rewrite -{}UNVE in clV, nVy, Vx.
have [pfX [pfXx pfXN]] : exists pfX, node pfX x /\ length pfX = N.+1.
  by have := nodeT N.+1; rewrite -subTset => /(_ x I) [] pfx /= ? ?; exists pfx.
have [pfY [pfYy pfYN]] : exists pfX, node pfX y /\ length pfX = N.+1.
  by have := nodeT N.+1; rewrite -subTset => /(_ y I) [] pfx /= ? ?; exists pfx.
have : pfY != pfX.
  apply/eqP => pfXYE; have [] := nodeUn pfYN; first by move=> /(_ y pfYy).
  by rewrite pfXYE => /eqP/disjoints_subset/(_ _ pfXx).
apply: contraNN => /eqP ?; apply/eqP; apply: (@tree_map_prefix y x) => //.
by rewrite pfXN pfYN.
Qed.

Local Fixpoint branch_prefix (f : nat -> bool) (n : nat) : seq bool := 
  match n with 
  | 0%N => [::]
  | S n => f n :: branch_prefix f n
  end.

Local Lemma branch_prefix_length f n : length (branch_prefix f n) = n.
Proof. by elim: n => // n /= ->. Qed.

Local Lemma branch_prefix_lt_subset f (i j : nat) : 
  (i < j)%N -> node (branch_prefix f j) `<=` node (branch_prefix f i).
Proof. 
move: i; elim: j => // j IH i /ltnSE ij1; rewrite [branch_prefix _ _]/=.
apply: subset_trans; first apply: node_subsetS.
move: ij1; rewrite leq_eqVlt => /orP; case; first by move/eqP ->.
exact: IH.
Qed.

Local Lemma branch_prefix_le_subset f (i j : nat) : 
  (i <= j)%N -> node (branch_prefix f j) `<=` node (branch_prefix f i).
Proof.
rewrite leq_eqVlt => /orP []; first by move/eqP ->.
exact: branch_prefix_lt_subset.
Qed.

Local Lemma surj_tree_map : set_surj [set: T] [set: cantor_space] tree_map.
Proof.
move=> f /= _.
suff [F [PF Ff]] : exists F : set (set T), ProperFilter F /\ tree_map @ F --> f.
  have [x [_ clfFx]] := cmptT PF filterT; exists x => //.
  apply: cantor_space_hausdorff => U V.
  move=> /continuous_tree_map/clfFx clF /Ff; rewrite ?nbhs_simpl /= => FtV.
  by move: (clF _ FtV); rewrite -preimage_setI; case=> z [? ?]; exists (tree_map z).
pose G := (filter_from [set: nat] (fun n => (node (branch_prefix f n)))).
have PG : ProperFilter G.
  apply: filter_from_proper; first apply: filter_from_filter.
  - by exists point.
  - move=> i j _ _; exists (maxn i j) => //; rewrite subsetI.
    by split; apply: branch_prefix_le_subset; rewrite ?leq_maxr ?leq_maxl.
  - move=> i _; apply: node_n0.
exists G; split => //; apply/cvg_sup => i U.
rewrite /= {1}/nbhs /=; case=> ? [][M oM <-].
move => /= Mtxn /filterS; apply; rewrite /nbhs /= nbhs_simpl.
exists i.+1 => // z fiz /=; suff -> : tree_map z i = f i by done.
rewrite /tree_map; move: fiz; rewrite [branch_prefix _ _]/=; case E: (f i). 
  move=> nfz. apply: asboolT; exists (branch_prefix f i) => //.
  exact: branch_prefix_length.
move=> nfz; apply: asboolF; case=> L Li ntz.
have := (@node_trivIset i.+1 (false :: branch_prefix f i) (true :: L)).
have -> : (false :: _ = true :: _) = False by move=> ? ?; apply/propext; split.
apply.
- by rewrite /= branch_prefix_length.
- by rewrite /= Li.
- by exists z.
Qed.

Local Lemma tree_map_bij : bijective tree_map.
Proof. 
rewrite -setTT_bijective.
by split=> //; [exact: inj_tree_map | exact: surj_tree_map ].
Qed.

#[local] HB.instance Definition _ := @BijTT.Build _ _ _ tree_map_bij.

Lemma cantor_like_homeomorphism : 
  exists (f : {splitbij [set: T] >->  [set: cantor_space]}), 
    continuous f /\
    (forall A, closed A -> closed (f@`A)).
Proof.
exists tree_map.
by split; [exact: continuous_tree_map | exact: closed_tree_map ].
Qed.

Lemma homeomorphism_cantor_like : 
  exists (f : {splitbij [set: cantor_space] >->  [set: T]}), 
    continuous f /\
    (forall A, closed A -> closed (f@`A)).
Proof.
case: cantor_like_homeomorphism => f [ctsf clsdf].
exists [splitbij of (f^-1)%FUN]; split.
  apply/continuous_closedP => A /clsdf /=; congr(_ _).
  rewrite eqEsubset; split => // z /=.
    by case => t Ax <-; rewrite invK // in_setE.
  move=> ?; exists (f^-1 z)%FUN => //.
  by apply: funK; rewrite in_setE.
move=> A clA /=; move/continuous_closedP/(_ _ clA): ctsf; congr(_ _).
rewrite eqEsubset; split => z.
  by move=> Az; exists (f z) => //; rewrite funK // in_setE.
by case=> x Ax <-; rewrite /= invK // in_setE.
Qed.
End TreeStructure.


Lemma cantor_like_cantor_space: cantor_like (cantor_space).
Proof.
split.
- by apply: perfect_diagonal => //= _; exists (true, false).
- exact: cantor_space_compact.
- exact: cantor_space_hausdorff.
- exact: cantor_totally_disconnected.
Qed.

Section FinitelyBranchingTrees.
Context {R : realType}.
Definition pointedDiscrete (P : pointedType) : pseudoMetricType R :=
  @discrete_pseudoMetricType R
    (@discrete_uniformType (TopologicalType
      (FilteredType P P principal_filter)
         discrete_topological_mixin)
    erefl) erefl.

Definition tree_of (T : nat -> pointedType) : pseudoMetricType R :=
  @product_pseudoMetricType R _ 
    (fun n => pointedDiscrete (T n))
    countable_nat.

Lemma cantor_like_finite_prod (T : nat -> topologicalType) : 
  (forall n, finite_set [set: pointedDiscrete (T n)]) ->
  (forall n, (exists xy : T n * T n, xy.1 != xy.2)) ->
  cantor_like (tree_of T).
Proof.
move=> finiteT twoElems; split.
- by apply perfect_diagonal => n; apply: twoElems.
- have /= := tychonoff (fun n => finite_compact (finiteT n)).
  by congr (compact _) => //=; rewrite eqEsubset; split => b.
- apply (@hausdorff_product _ (fun n => pointedDiscrete (T n))).
  by move=> n; exact: discrete_hausdorff.
- apply totally_disconnected_prod => ?. 
  exact: totally_disconnected_discrete.
Qed.

End FinitelyBranchingTrees.

Section CompactEmbedding.
Context {R: realType} {T : pseudoMetricType R}.

Hypothesis cptT : compact [set: T].
Hypothesis hsdfT : hausdorff_space T.

Local Definition oball eps x : set T := interior (ball x eps).

Local Lemma refine_aux (eps : R) (B : set T) : 0 < eps ->
  exists (U : set (set T)), 
  [/\
    finite_set U,
    (forall C, U C -> C `<=` B),  
    B `<=` bigcup U id,
    (forall C, U C -> B `&` C !=set0) &
    (forall C, U C -> exists t, C `<=` ball t eps)
  ].
Proof.
move:eps=>_/posnumP[eps]; have : compact (closure B).
 by apply: (subclosed_compact _ cptT) => //; exact: closed_closure.
rewrite compact_cover => /(_ T (closure B) (oball eps%:num)) [].
- by move=> i _; exact: open_interior.
- move=> t clBt; exists t => //; exact: nbhsx_ballx.
move=> C CsubB cvrBcl; exists (
  (fun i => B `&` (oball eps%:num i)) @` [set` C]); split.
- exact/finite_image/finite_fset.
- by move=> ? [?] ? <-.
- move=> z Bz; have /cvrBcl [d /= Cd odz] : closure B z by exact: subset_closure.
  by exists (B `&` (oball eps%:num d)) => //; exists d.
- move=> ? /= [d] Cd <-; have : closure B d by move/CsubB/set_mem:Cd.
  case/(_ (oball eps%:num d)). 
    apply: open_nbhs_nbhs; split; [exact: open_interior | apply: nbhsx_ballx].
  by move=> e ?; exists e; rewrite setIA setIid.
- move=> ? /= [e /CsubB/set_mem] ? <-; exists e.
  by apply: subset_trans; last exact: interior_subset.
Qed.

Local Lemma harmonic_pos (n : nat) : 0 < (n.+1%:R^-1:R).
Proof. by []. Qed.

Local Lemma harmonicS (n : nat) : (n.+2%:R^-1) < (n.+1%:R^-1) :> R.
Proof. 
rewrite ltr_pinv ?inE ?unitfE ?ltr_nat //; by apply/andP. 
Qed.
  
Local Lemma ltn_leq_trans (n m p : nat) :
  (m < n)%N -> (n <= p)%N -> (m < p)%N.
Proof. exact: (@leq_ltn_trans n (S m) (S p)). Qed.

Local Definition tier : Type := ((set (set T)) * (nat -> set T) * nat).

Local Lemma refine_indexed (eps : R) (B : set T) : 0 < eps ->
  exists (Ufn : tier), 
    forall n, (n >= Ufn.2)%N ->
  [/\
    B!=set0 -> Ufn.1.2 @` `I_n = Ufn.1.1 ,
    (forall C, Ufn.1.1 C -> C `<=` B),  
    B `<=` bigcup `I_n Ufn.1.2,
    (forall i, B!=set0 -> B `&` Ufn.1.2 i !=set0) &
    (forall i, exists t, Ufn.1.2 i `<=` ball t eps)
  ].
Proof.
case: (pselect (B != set0)); first last.
  move=>/negP; rewrite negbK=> /eqP -> epspos.
  exists (set0, (fun=> interior (ball point eps)), O) => n /= ?; split.
  - by move/set0P/eqP.
  - by move=> ?.
  - by move=> ? ?. 
  - by move=> ? /set0P /negP.
  - move=> ?; exists point; exact: interior_subset.
case/set0P => b0 Bb0 /(@refine_aux _ B) [U]. 
move=> [/finite_setP [N idx] subB cvrB BIU Ueps].
have [U0 UU0 U0b0] := cvrB _ Bb0; case/card_esym/ppcard_eqP: idx => f.
pose g := patch (fun=> U0) `I_N f; exists (U, g, N) => // n /= Nsubn;
have Ugi : forall (i : nat), U (g i).
  by move=> i; rewrite /=/g patch_pred; case E: (_<_)%N => //; exact: funS.
split.
- move=> _; rewrite eqEsubset; split; first by move=> i [] ? ? <-; exact: Ugi.
  move=> C /(@surj _ _ _ _ f) [m /= mN <-]. 
  exists m; first exact: (ltn_leq_trans mN).
  by rewrite /g patchT // in_setE /=.
- by move=> C UC; exact: subB.
- move=> ? /cvrB [C] /(@surj _ _ _ _ f) [m] ? <- ?. 
  by exists m; [exact: (@ltn_leq_trans N) | by rewrite /=/g patchT // in_setE].
- by move=> i ?; exact: BIU.
- by move=> i; exact: Ueps.
Qed.

Local Definition refine (n : nat) (B : set T) : tier :=
  (projT1 (cid (@refine_indexed _ B (harmonic_pos n) ))).

Local Lemma refine_spec (N : nat) (B : set T) :
  let Ufn := refine N B in 
  [/\
    forall n, (n >= Ufn.2)%N -> B!=set0 -> Ufn.1.2 @` `I_n = Ufn.1.1,
    forall C, Ufn.1.1 C -> C `<=` B,  
    forall n, (n >= Ufn.2)%N -> B `<=` bigcup `I_n Ufn.1.2,
    forall i, B!=set0 -> B `&` Ufn.1.2 i !=set0 &
    forall i, exists t, Ufn.1.2 i `<=` ball t (N.+1%:R^-1)
  ].
Proof.
split.
- by move=> n /(projT2 (cid (refine_indexed B (harmonic_pos N))) _) [].
- by have [] := projT2 (cid (refine_indexed B (harmonic_pos N))) _ (leqnn _).
- by move=> n /(projT2 (cid (refine_indexed B (harmonic_pos N))) _) [].
- by have [] := projT2 (cid (refine_indexed B (harmonic_pos N))) _ (leqnn _).
- by have [] := projT2 (cid (refine_indexed B (harmonic_pos N))) _ (leqnn _).
Qed.

Local Fixpoint tiers (n : nat) : set tier := 
  if n is S m
  then refine n @` (\bigcup_(Ufn in tiers m) Ufn.1.1)
  else [set ([set setT], (fun=> setT), (2)%N)].

Local Definition lvl_aux (n : nat) : nat :=
  (supremum (0)%N ((fun Ufn => Ufn.2) @` tiers n)).

Local Lemma lt02 (n : nat) : (0 \in `I_(n.+2))%N. 
Proof. by rewrite in_setE. Qed.

Local Definition lvl (n : nat) :=
  PointedType (`I_(lvl_aux n).+2) (exist _ O (lt02 n)).

Local Definition Ttree := @tree_of R lvl.
  
Local Fixpoint target (branch : Ttree) (n : nat) : (set T) := 
  if n is S m 
  then (refine n (target branch m) ).1.2 (projT1 (branch n))
  else setT.
  
Local Lemma targetN0 (b : Ttree) (n : nat) : target b n !=set0.
Proof.
elim: n => //=; first by exists point.
move=> n [x tbnx]. 
have [_ _ _ /(_ (proj1_sig (b (S n)))) + _] := @refine_spec n.+1 (target b n).
by (case; first by exists x); move=> t [? ?]; exists t.
Qed.

Local Lemma tierN0 n Ufn : tiers n Ufn -> 
  Ufn.1.1 !=set0 /\ (forall V, Ufn.1.1 V -> V!=set0).
elim: n Ufn => //. 
  move=> ?; rewrite /tiers=> ->; split; first by exists [set: T].
  by move=> ? /= ->; exists point.
move=> n IH Ufn /= [V [t /IH [IH1 IH2]] tV <-].
have VN0 : V!=set0 by exact: IH2.
have [/(_ (refine n.+1 V).2.+1) img _ _ UN0 _] := refine_spec (n.+1) V; split.
  rewrite -img //.
  by exists ((refine n.+1 V).1.2 (refine n.+1 V).2), (refine n.+1 V).2 => //=.
move=> U /=; rewrite -img //=.
by case=> M + <-; have [z [_ ?] _] := UN0 M VN0; exists z.
Qed.

Local Lemma tiersN0 n : tiers n !=set0.
elim: n => //=; first by exists ([set [set: T]], fun=> [set: T], 2%N).
move=> n [Ufn] Ufn_tier; have [[U UfnU] _] := tierN0 Ufn_tier.
by exists (refine n.+1 U); exists U => //; exists Ufn.
Qed.

Local Lemma refine_finite (n : nat) (B : set T) :
  B!=set0 -> finite_set (refine n B).1.1.
Proof.
move=> Bn0; have [/(_ _ (leqnn _) Bn0) <- _ _ _ _] := refine_spec n B.
exact/finite_image/finite_II.
Qed.
 
Local Lemma tier_finite Ufn n : tiers n Ufn -> finite_set Ufn.1.1.
Proof.
elim: n Ufn; first by move=> ? -> /=; exact: finite_set1.
move=> n IH Ufn /= [V [tr] tier_tr trV <-]; apply: refine_finite.
by have [_ ] := (tierN0 tier_tr); exact.
Qed.


Local Lemma tiers_finite n : finite_set (tiers n).
Proof.
elim: n; first exact: finite_set1.
move=> n IH /=; apply: finite_image; apply: bigcup_finite => //.
by move=> ? ?; apply: (@tier_finite _ n).
Qed.

Local Lemma cauchy_branch (b : Ttree) : 
  cauchy (filter_from [set: nat] (target b)).
Proof.
move=> E; rewrite /= nbhs_simpl -entourage_from_ballE; case => _/posnumP[eps].
have [] := @cvg_harmonic R (ball (0:R) eps%:num); first exact: nbhsx_ballx.
move=> n _ /(_ n (leqnn n)) /=; rewrite /ball /= sub0r normrE ger0_norm //.
move=> neps nE; exists (target b (n*2)%N.+1, target b (n*2)%N.+1). 
  by split; exists (n*2)%N.+1.
case=> y z [] /= rfy rfz; apply: nE; apply: (le_ball (ltW neps)) => /=.
have [_ _ _ _] := refine_spec (n * 2)%N.+1 (target b (n*2)).
move=> /= /(_ (proj1_sig (b ((n * 2)%N.+1)))) [] t rfball.
have zball := rfball z rfz; have /ball_sym yball := rfball y rfy.
have := ball_triangle yball zball; apply: le_ball.
suff P : (n*2).+2%:R^-1 <= n.+1%:R^-1/2 :> R. 
  by rewrite (splitr n.+1%:R^-1) ler_add //; exact: P.
rewrite -invrM // ?unitfE // ler_pinv ?inE ?unitfE; first last.
  by apply/andP. 
  by apply/andP. 
by rewrite mulrC -natrM ler_nat ?mulSn addnC ?addnS addn0.
Qed.

Lemma ubound_finite_set (U : set nat) : 
  finite_set U -> ubound U !=set0.
Proof.
case/finite_setP => n; move: U; elim: n.
  by move=> ?; rewrite II0 card_eq0 => /eqP ->; exists O => ?.
move=> n IH U /eq_cardSP [N UN] /IH [/= M ubdM]; exists (maxn M N).
move=> w; case: (eqVneq w N); first by move=> -> ?; exact: leq_maxr.
by move=> /eqP wN Uw; apply: leq_trans; [exact: ubdM  |  exact: leq_maxl].
Qed.

Lemma lvl_aux_ge : forall n Ufn, tiers n Ufn -> (Ufn.2 <= lvl_aux n)%N.
Proof.
elim. 
  move => /= ? -> /=; rewrite /lvl_aux.
  rewrite (_ : [set Ufn.2 | Ufn in tiers 0] = [set 2%N]) ?supremum1 //.
  rewrite eqEsubset; split => t /=; first by (do 3 case) => ? ? ? /= + <-; case.
  by move=> ->; exists ([set [set: T]], fun=> [set: T], 2%N).
move=> n IH Ufn TUfn; rewrite /lvl_aux/supremum; case: ifPn. 
  move=> /eqP/image_set0_set0 /= /image_set0_set0/bigcup0P.
  have [Ufn2 Ufn_tier] := tiersN0 n => /(_ _ Ufn_tier).
  by have [/set0P/eqP + _] := @tierN0 _ Ufn2 Ufn_tier.
move=> cands.
case: xgetP => [y yA [uAy ?]|]. 
  apply: (@leq_trans y) => //.
  by apply: uAy => /=; exists Ufn => //.
move=> /forallNP; apply: contra_notP => _; apply: nat_supremums_neq0.
apply/ubound_finite_set/finite_image/tiers_finite.
Qed.

Lemma refine_inje n B C : B!=set0 -> 
  refine n B = refine n C -> B `<=` C.
Proof.
move=> ? rfnBC t Bt. 
have [img _ /(_ _ (leqnn _ ) _ Bt) + _ _] := refine_spec n B.
case => m/= msmall rfbm.
have [_ /(_ _ _ _ rfbm) + _ _ _] := refine_spec n C.
apply; rewrite -rfnBC -(img _ (leqnn _)) => //.
Qed.

Lemma refine_inj n B C : B!=set0 -> C !=set0 -> 
  refine n B = refine n C -> B = C.
Proof.
by move=> ? ? rfnBC; rewrite eqEsubset; split; apply: (@refine_inje n).
Qed.

Lemma tier_target b n : tiers n.+1 (refine n.+1 (target b n)).
Proof.
elim: n; first by exists [set: T]; rewrite // bigcup_set1.
move=> n IH /=; exists ((refine n.+1 (target b n)).1.2 (projT1 (b n.+1))) => //.
exists (refine n.+1 (target b n)) => //.
have [/(_ (lvl_aux n.+1).+2) img _ _ _ _] := refine_spec n.+1 (target b n).
rewrite -img; last exact: targetN0.
  by exists (projT1 (b n.+1)) => //; have := projT2 (b n.+1); rewrite in_setE.
do 2 apply: leqW; apply: lvl_aux_ge; exists (target b n) => //.
case: IH => V [ Ufn trUfn UfnV E]; exists Ufn => //.
have := UfnV; congr (_ _); apply: (@refine_inj n.+1) => //.
  by have [_ ] := tierN0 trUfn; apply.
apply: targetN0.
Qed.


Lemma branch_subsetS b n : target b n.+1 `<=` target b n.
Proof. 
have [img + _ _ _] /= := refine_spec n.+1 (target b n).
apply; rewrite -(img (lvl_aux n.+1).+2 _ ); first last. 
- exact: targetN0.
- by do 2 apply: leqW; apply: lvl_aux_ge; exact: tier_target.
by exists (projT1 (b n.+1)) => //; have := projT2 (b n.+1); rewrite in_setE.
Qed.

Lemma branch_subset b i j : (i <= j)%N -> target b j `<=` target b i.
Proof. 
elim: j i; first by move => ?; rewrite leqn0 => /eqP ->.
move=> j IH i; rewrite leq_eqVlt => /orP [/eqP -> //| /IH ji1].
exact/(subset_trans _ ji1)/branch_subsetS.
Qed.

Lemma filter_branch b: 
  ProperFilter (filter_from [set: nat] (target b)).
Proof.
apply: filter_from_proper; last by move=>? _; exact: targetN0.
apply: filter_from_filter; first by exists O.
move=> i j _ _; exists (maxn i j) => // t targetIJ. 
by split; apply: (branch_subset _ targetIJ); rewrite ?leq_maxl ?leq_maxr.
Qed.

Local Lemma target_cvg b : cvg (filter_from [set: nat] (target b)).
Proof.
apply: (@compact_cauchy_cvg _ [set: T]) => //=.
- apply: filter_branch.
- apply: cauchy_branch.
- by exists O => //.
Qed.

Local Definition bullseye (b : Ttree) : T :=
  lim (filter_from [set: nat] (target b)).


Local Fixpoint retract_aux (t : T) (n : nat) : ((set T) * lvl n) := 
  if n is S m 
  then 
    let rfn := refine n (retract_aux t m).1 in
    get (fun (Ui :((set T) * lvl n)) => Ui.1 t /\ rfn.1.2 (projT1 Ui.2) = Ui.1)
  else (setT, point).

Local Lemma retract_refine (t : T) (n : nat) : 
    (retract_aux t n).1 t /\ 
    exists Ufn, [/\
      if n is S m then Ufn = (refine n (retract_aux t m).1) else True,
      tiers n Ufn, 
      Ufn.1.1 (retract_aux t n).1 &
      Ufn.1.2 (projT1 (retract_aux t n).2) = (retract_aux t n).1
    ].
Proof.
elim: n; first by split => //; exists ([set setT], (fun=> setT), (2)%N).
move=> n [rtt] [Ufn [? tn retractN] ufnT]; split; first last.
  exists (refine n.+1 (retract_aux t n).1) => //=; split => //.
  - exists (retract_aux t n).1 => //; exists Ufn => //.
  - have rtN0 : (retract_aux t n).1 !=set0 by have [_] := (tierN0 tn); exact.
    case: xgetP => [[U lvln] uAx /= [? <-]|].
      have [rsurj _ _ _ _] := refine_spec n.+1 (retract_aux t n).1.
      have <- /= := rsurj (lvl_aux n.+1).+2 => //.
        by exists (projT1 lvln) => //; have := projT2 lvln; rewrite in_setE.
      do 2 apply: leqW; apply: lvl_aux_ge; exists (retract_aux t n).1 => //.
      by exists Ufn.
    move=> /forallNP; apply: contra_notP => /= _.
    have [rsurj _ cvr _ _] := refine_spec n.+1 (retract_aux t n).1.
    have [|N Nlt rfNt] := cvr (lvl_aux n.+1).+2 _ t rtt.
      do 2 apply: leqW; apply: lvl_aux_ge; exists (retract_aux t n).1 => //.
      by exists Ufn.
    have Nlvl : N \in `I_(lvl_aux n.+1).+2 by rewrite in_setE.
    by exists ( (refine n.+1 (retract_aux t n).1).1.2 N, exist _ N Nlvl). 
  - case: xgetP => [[U lvln] uAx /= [? <-]|] => //.
    move=> /forallNP; apply: contra_notP => /= _.
    have [rsurj _ cvr _ _] := refine_spec n.+1 (retract_aux t n).1.
    have [|N Nlt rfNt] := cvr (lvl_aux n.+1).+2 _ t rtt.
      do 2 apply: leqW; apply: lvl_aux_ge; exists (retract_aux t n).1 => //.
      by exists Ufn.
    have Nlvl : N \in `I_(lvl_aux n.+1).+2 by rewrite in_setE.
    by exists ( (refine n.+1 (retract_aux t n).1).1.2 N, exist _ N Nlvl). 
move=> /=; case: xgetP => [[U lvln] uAx [/= //]|].
move=> /forallNP; apply: contra_notP => /= _.
have [rsurj _ cvr _ _] := refine_spec n.+1 (retract_aux t n).1.
have [|N Nlt rfNt] := cvr (lvl_aux n.+1).+2 _ t rtt.
  do 2 apply: leqW; apply: lvl_aux_ge; exists (retract_aux t n).1 => //.
  by exists Ufn.
have Nlvl : N \in `I_(lvl_aux n.+1).+2 by rewrite in_setE.
by exists ( (refine n.+1 (retract_aux t n).1).1.2 N, exist _ N Nlvl). 
Qed.

Local Definition retract (t : T) : Ttree := fun n => (retract_aux t n).2.

Local Lemma bullseye_surj : set_surj [set: Ttree] [set: T] bullseye.
Proof.
move=> t _; suff : exists f : Ttree, forall n, target f n t.
  case=> f fnt; exists f => //.
  apply/close_eq/close_sym => // U /open_nbhs_nbhs Ubf W Wt; exists t.
  split; last exact: nbhs_singleton.
  have /= [M _] := target_cvg (Ubf); apply; exact: fnt.
exists (retract t) => n; case: n => // n /=.
suff -> : target (retract t) n = (retract_aux t n).1.
  by have [rtxt [Ufn] [-> trUfn ? ->]] // := retract_refine t n.+1.
elim: n => // n IH; rewrite [LHS]/= IH.
by have [_ [?] [-> ?] ] := retract_refine t n.+1.
Qed.

Lemma bullseye_prefixE (br1 br2 : Ttree) (n : nat) : 
  (forall i, (i <= n)%N -> br1 i = br2 i) -> 
  (forall i, (i <= n)%N -> target br1 i = target br2 i).
Proof.
elim: n; first by move=> i ?; rewrite leqn0 => /eqP ->.
move=> n IH eqSn i; rewrite leq_eqVlt => /orP []; first last.
  by apply: IH => // ? /leqW; exact: eqSn.
move/eqP => -> /=; rewrite IH => //; first last.
  by move=> ? /leqW; exact: eqSn.
by rewrite eqSn.
Qed.

Lemma bullseye_target_clousre (br : Ttree) (n : nat) :
  closure (target br n) (bullseye br).
Proof.
move=> B /target_cvg [N] _ NsubB; suff : target br n `&` target br N !=set0.
  by case=> z [??]; exists z; split => //; exact: NsubB.
move=> {NsubB}; wlog nN : N n / (n <= N)%N.
  move=> WL; case/orP: (leq_total N n); last exact: WL. 
  rewrite setIC; exact: WL.
have [z ?] := targetN0 br N; exists z; split => //.
by apply: (branch_subset nN). 
Qed.
 
Lemma closed_ball_subset (M : pseudoMetricType R) (x : M)
  (r0 r1 : R) : 0 < r0 -> r0 < r1 -> closed_ball x r0 `<=` ball x r1.
Proof.
move=> r00 r01; rewrite (_ : r0 = (PosNum r00)%:num) // => y.
have r0r1 : 0 < r1 - r0 by rewrite subr_gt0.
move=> /(_ (ball y (PosNum r0r1)%:num)) []; first exact: nbhsx_ballx.
move=> z [xz /ball_sym zy]; have := ball_triangle xz zy; congr(ball _ _ _).
by rewrite /= addrC -addrA [-_ + _]addrC subrr addr0.
Qed.

Lemma bullseye_prefix (br1 br2 : Ttree) (n : nat) : 
  (forall i, (i <= n.+1)%N -> br1 i = br2 i) -> 
  ball (bullseye br1) (2 * (n.+1%:R^-1)) (bullseye br2).
Proof.
move=> pfxE; have := @bullseye_target_clousre br1 n.+1.
rewrite (@bullseye_prefixE br1 br2 n.+1) // => /= near_br1. 
have /= near_br2 := @bullseye_target_clousre br2 n.+1.
have [surj _ _ _ rball] := refine_spec n.+1 (target br2 n).
have [t /= /closure_subset rfn] := rball (proj1_sig (br2 n.+1)).
have /(closed_ball_subset (harmonic_pos n.+1) (harmonicS n)) := rfn _ near_br1.
have /(closed_ball_subset (harmonic_pos n.+1) (harmonicS n)) := rfn _ near_br2.
rewrite [_ / _]splitr mulrC mulrA mulVf // div1r => /ball_sym b1 b2.
by have /ball_sym := ball_triangle b1 b2.
Qed.

Lemma tree_prefix (y: Ttree) (n : nat) : 
  \forall z \near y, forall i,  (i < n)%N -> y i = z i.
Proof.
elim: n; first by near=> z => ?; rewrite ltn0.
move=> n IH.
near=> z => i; rewrite leq_eqVlt => /orP []; first last.
  move=> iSn; have -> := near IH z => //.
move=> /eqP/(succn_inj) ->; near: z.
  exists ((proj n)@^-1` [set (y n)]); split => //.
  suff : @open Ttree ((proj n)@^-1` [set (y n)]) by [].
  apply: open_comp; last apply: discrete_open => //.
  by move=> + _; apply: proj_continuous.
Unshelve. all: end_near. Qed.

Lemma tree_prefix_le (y: Ttree) (n : nat) : 
  \forall z \near y, forall i,  (i <= n)%N -> y i = z i.
Proof. exact: (tree_prefix y n.+1). Qed.
 
Local Lemma bullseye_cts : continuous bullseye.
Proof.
move=> x; apply/ cvg_ballP; first exact: nbhs_filter.
move=> _/posnumP[eps].
have [] := @cvg_harmonic R (ball (0:R) eps%:num); first exact: nbhsx_ballx.
move=> n _ /(_  n (leqnn n)); rewrite /ball [x in x -> _]/= sub0r.
rewrite normrE ger0_norm // => neps; have n2 : n.+2%:R^-1 <= n.+1%:R^-1 :> R.
  by rewrite ler_pinv ?inE ?unitfE ?ler_nat //; exact/andP. 
near=> z. 
  apply/(@le_ball _ _ _ (2 * ((2 *n).+2)%:R^-1)); last apply: bullseye_prefix.
    apply: le_trans; last apply/ltW/neps.
    rewrite ( _ : (2 * n).+2 = 2 * n.+1)%N ?natrM; first last.
      by rewrite ?mulSn ?mul0n ?addn0 ?addnS addSn. 
    by rewrite -[x in x/(_ * _)]mulr1 -mulf_div divrr ?unitfE // ?mul1r.
near: z.
exact: tree_prefix_le.
Unshelve. all: end_near. Qed.

Lemma ttree_finite : cantor_like Ttree.
Proof.
apply: cantor_like_finite_prod.
  by move=> n /=; apply/ finite_setP; exists (lvl_aux n).+2; exact: card_setT.
move=> n /=. 
have IO : O \in `I_(lvl_aux n).+2 by rewrite in_setE.
have I1 : 1%N \in `I_(lvl_aux n).+2 by rewrite in_setE.
by exists (exist _ O IO, exist _ 1%N I1).
Qed.

Lemma cantor_surj : exists (f : {surj [set: cantor_space] >-> [set: T]}), 
  continuous f.
Proof.
have [f [ctsf _]] := homeomorphism_cantor_like (ttree_finite).
have /Psurj blz := bullseye_surj.
pose g := [surj of (projT1 blz) \o f].
exists g => /= x; apply: (@continuous_comp cantor_space Ttree).
  exact: ctsf.
have <- := projT2 blz; exact: bullseye_cts.
Qed.

End CompactEmbedding.