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

Lemma compact_cluster_set1 {T : topologicalType} (x : T) F V :
  hausdorff_space T -> compact V -> nbhs x V ->
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

Section topological_trees.
Context {K : nat -> topologicalType} {X : topologicalType}.
Context (tree_ind : forall n, set X -> K n -> set X).
Context (tree_invariant : (set X -> Prop)).

Hypothesis cmptX : compact [set: X].
Hypothesis hsdfX : hausdorff_space X.
Hypothesis discreteK : forall n, discrete_space (K n).
Hypothesis ind_cover : forall n U, U = \bigcup_e @tree_ind n U e .
Hypothesis ind_invar : forall n U e, 
  tree_invariant U -> tree_invariant (@tree_ind n U e).
Hypothesis invar_n0 : forall U, tree_invariant U -> U !=set0.
Hypothesis invarT : tree_invariant [set: X].
Hypothesis invar_cl : (tree_invariant `<=` closed).
Hypothesis ind_separates: forall (x y : X),
  x != y -> 
  exists n, (forall (U : set X) e, 
    @tree_ind n U e x -> ~@tree_ind n U e y).


Local Lemma ind_sub : forall n U e, @tree_ind n U e `<=` U.
Proof.
move=> n U e; rewrite [x in _ `<=` x] (ind_cover n U); exact: bigcup_sup.
Qed.

Let T := product_topologicalType K.

Local Fixpoint branch_apx (b : T) n := 
  if n is S m 
  then tree_ind (branch_apx b m) (b m)
  else [set: X].

Local Definition tree_mapF (b : T) := 
  filter_from [set: nat] (branch_apx b).

Local Lemma tree_map_invar b n : tree_invariant (branch_apx b n).
Proof. elim: n => // n ? /=; exact: ind_invar. Qed.

Local Lemma tree_map_sub b i j : (i <= j)%N -> branch_apx b j `<=` branch_apx b i.
elim: j i => //=; first by move=> ?; rewrite leqn0 => /eqP ->.
move=> j IH i; rewrite leq_eqVlt => /orP; case; first by move=> /eqP ->.
by move/IH/(subset_trans _); apply; exact: ind_sub.
Qed.

Local Lemma tree_map_filter b : ProperFilter (tree_mapF b).
Proof.
split. 
  by case => n _ brn; case: (invar_n0 (tree_map_invar b n)) => x /brn.
apply: filter_from_filter; first by exists O.
move=> i j _ _; exists (maxn i j) => //; rewrite subsetI.
by split; apply: tree_map_sub; [exact: leq_maxl | exact: leq_maxr].
Qed.

Let tree_map (b : T) := lim (tree_mapF b).

Local Lemma cvg_tree_map b : cvg (tree_mapF b).
Proof.
have [|x [_ clx]] := cmptX (tree_map_filter b).
  apply: filterT; exact: tree_map_filter.
apply/cvg_ex; exists x => /=; apply: (compact_cluster_set1 _ cmptX) => //.
  exact: filterT.
  exact: tree_map_filter.
  by apply: filterT; exact: tree_map_filter.
rewrite eqEsubset; split; last by move=> ? ->. 
move=> y cly; case: (eqVneq x y); first by move=> ->.
case/ind_separates => n sep.
have bry : branch_apx b n.+1 y.
  rewrite [branch_apx _ _](iffLR (closure_id _)). 
    by move: cly; rewrite clusterE; apply; exists n.+1.
  apply: invar_cl; apply: tree_map_invar.
suff /sep : branch_apx b n.+1 x by done.
rewrite [branch_apx _ _](iffLR (closure_id _)). 
  by move: clx; rewrite clusterE; apply; exists n.+1.
apply: invar_cl; apply: tree_map_invar.
Qed.

Local Lemma tree_map_surj : set_surj [set: T] [set: X] tree_map.
Proof.
move=> z _; suff : exists g, forall n, branch_apx g n z.
  case=> g gnz; exists g => //; apply: close_eq => // U [oU Uz] V ngV; exists z.
  split => //; have /(_ _ ngV) [n _] : tree_mapF g --> tree_map g by exact:cvg_tree_map.
  by apply; exact: gnz.
have zcov' : forall n (U : set X), exists e, U z -> @tree_ind n U e z.
  move=> n U; case: (pselect (U z)); last by move => ?; exists point.
  by rewrite {1}(@ind_cover n U); case => e _ ?; exists e.
pose zcov n U := projT1 (cid (zcov' n U)).
pose fix g n : (K n * set X) := 
  if n is S m 
  then (zcov m.+1 (g m).2, @tree_ind m.+1 (g m).2 (zcov m.+1 (g m).2))
  else (zcov O [set: X], @tree_ind O [set: X] (zcov O [set: X])).
pose g' n := (g n).1; have apxg : forall n, branch_apx g' n.+1 = (g n).2.
  by elim => //= n ->; congr (_ _).
exists g'; elim => // n /= IH.
have /(_ IH) := projT2 (cid (zcov' n (branch_apx g' n)));move => {IH}.
by case: n => // n; rewrite apxg /=.
Qed.

Local Lemma tree_prefix (b: T) (n : nat) : 
  \forall c \near b, forall i,  (i < n)%N -> b i = c i.
Proof.
elim: n; first by near=> z => ?; rewrite ltn0.
move=> n IH.
near=> z => i; rewrite leq_eqVlt => /orP []; first last.
  move=> iSn; have -> := near IH z => //.
move=> /eqP/(succn_inj) ->; near: z.
  exists ((proj n)@^-1` [set (b n)]); split => //.
  suff : @open T ((proj n)@^-1` [set (b n)]) by [].
  apply: open_comp; last apply: discrete_open => //.
  by move=> + _; apply: proj_continuous.
Unshelve. all: end_near. Qed.

Local Lemma apx_prefix (b c : T) (n : nat) : 
  (forall i, (i < n)%N -> b i = c i) -> 
  branch_apx b n = branch_apx c n.
Proof.
elim: n => //= n IH inS; rewrite IH; first by congr (tree_ind _); exact: inS.
by move=> ? ?; apply: inS; apply: ltnW.
Qed.

Local Lemma tree_map_apx b n: branch_apx b n (tree_map b). 
Proof.
apply: (@closed_cvg _ _ _ (tree_map_filter b) idfun); last exact: cvg_tree_map.
  by apply: invar_cl; exact: tree_map_invar.
exists n => //.
Qed.

Local Lemma tree_map_cts : continuous tree_map. 
Proof.
move=> b U /cvg_tree_map /= [n _] /filterS; apply.
  by apply: fmap_filter; exact: (@nbhs_filter T).
rewrite nbhs_simpl /=; near_simpl => /=.
have := tree_prefix b n; apply: filter_app; near_simpl => /=.
by near=> z => /apx_prefix ->; apply: tree_map_apx.
Unshelve. all: end_near. Qed.

Local Lemma tree_map_inj :
  (forall n U, trivIset [set: K n] (@tree_ind n U)) -> 
  set_inj [set: T] tree_map.
Proof.
move=> triv x y _ _ xyE; apply: functional_extensionality_dep => n.
suff : forall n, branch_apx x n = branch_apx y n.
  move=> brE; have := @triv n (branch_apx x n) (x n) (y n) I I; apply.
  exists (tree_map y); split. 
    by rewrite -?xyE -/(branch_apx x n.+1); apply: tree_map_apx.
  rewrite brE -/(branch_apx y n.+1); apply: tree_map_apx.
elim => // m /= brE. 
have -> := @triv m (branch_apx x m) (x m) (y m) I I; first by rewrite brE. 
exists (tree_map y); split. 
  by rewrite -?xyE -/(branch_apx x m.+1); apply: tree_map_apx.
rewrite brE -/(branch_apx y m.+1); apply: tree_map_apx.
Qed.

Lemma tree_map_props : exists (f : T -> X),
  [/\ continuous f,
      set_surj [set: T] [set: X] f &
      (forall n U, trivIset [set: K n] (@tree_ind n U)) -> 
        set_inj [set: T] f
  ].
Proof.
exists tree_map; split.
- exact: tree_map_cts.
- exact: tree_map_surj.
- exact: tree_map_inj.
Qed.

End topological_trees.

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

Definition c_invar (U : set T) := clopen U /\ U !=set0.

Local Lemma clopen_surj : $|{surjfun [set: nat] >-> @clopen T}|.
Proof. 
suff : (@clopen T = set0 \/ $|{surjfun [set: nat] >-> @clopen T}|).
  by case; rewrite // eqEsubset; case=>/(_ _ clopenT).
by apply/pfcard_geP/clopen_countable/ compact_countable_base; case: cantorT.
Qed.

Let U_ := unsquash clopen_surj.

Local Lemma split_clopen' (U : set T) :
  exists V,  open U -> U !=set0 -> clopen V /\ V `&` U !=set0 /\ ~`V `&` U !=set0.
Proof.
case: (pselect (open U)) => oU; last by exists point.
case: (pselect (U !=set0)) => Un0; last by exists point.
have [x [y] [Ux] Uy xny] := (iffLR perfect_set2) pftT U oU Un0.
have [V [?] [?] [? ?]] := dsctT xny; exists V. 
by repeat split => //; [exists x | exists y].
Qed.

Let split_clopen (U : set T) := projT1 (cid (split_clopen' U)).

Definition c_ind (n : nat) (V : set T) (b : bool) := 
  let Wn := 
    if pselect ((U_ n) `&` V !=set0 /\ ~` (U_ n) `&` V !=set0)
    then (U_ n) 
    else split_clopen V in 
  (if b then Wn else ~` Wn) `&` V.

Lemma cantor_map : exists (f : cantor_space -> T), 
  [/\ continuous f,
      set_surj [set: cantor_space] [set: T] f &
      set_inj [set: cantor_space] f
  ].
Proof.
have [] := (@tree_map_props 
  (fun=> [topologicalType of bool])
  T (c_ind) (c_invar) cmptT hsdfT _ _ _ _ _).
- done.
- move=> n V; rewrite eqEsubset; split => t; last by case => ? ? [].
  move=> Vt; case: (pselect ((U_ n) `&` V !=set0 /\ ~` (U_ n) `&` V !=set0)).
    move=> ?; case: (pselect (U_ n t)). 
      by exists true => //; rewrite /c_ind; case pselect.
    by exists false => //; rewrite /c_ind; case pselect.
  move=> ?; case: (pselect (split_clopen V t)). 
    by exists true => //; rewrite /c_ind; case pselect.
  by exists false => //; rewrite /c_ind; case pselect.
- move=> n U e [] clU Un0; rewrite /c_ind; case: pselect.
    case => /= ? ?; case: e => //; split => //; apply: clopenI => //.
      exact: funS.
    by apply: clopenC => //; exact: funS.
  have [| | ? [? ?]] := projT2 (cid (split_clopen' U)) => //; first by case: clU.
  move=> ?; case: e => //=; (split; first apply: clopenI) => //.
  exact: clopenC.
- by move=> ? []. 
- by split;[ exact: clopenT |exists point]. 
- by move=> ? [[]]. 
- move=> x y /dsctT [A [Ax [Any clA]]]. 
  have [] := (@surj _ _ _ _ U_ _ clA) => n _ UnA; exists n => V e.
  case: (pselect (V y)); last by move=> + _; apply: subsetC => ? [].
  case: (pselect (V x)); last by move=> + _ [].
  move=> Vx Vy; rewrite {1 2}/c_ind; case: pselect => /=; rewrite ?UnA.
    by move=> _; case: e; case => // ? ?; apply/not_andP; left.
  by apply: absurd; split; [exists x | exists y].
- move=> f [ctsf surjf injf]; exists f; split => //; apply: injf.
  move=> n U i j _ _ [z] [] [] + Uz [+ _]; case: pselect => /=. 
    by case => ? ?; case: i; case: j => //.
  by move=> ?; case: i; case: j => //.
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