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

Lemma cantor_like_cantor_space: cantor_like (cantor_space).
Proof.
split.
- by apply: perfect_diagonal => //= _; exists (true, false).
- exact: cantor_space_compact.
- exact: cantor_space_hausdorff.
- exact: cantor_totally_disconnected.
Qed.


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

Local Lemma tree_map_inj:
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

Let c_invar (U : set T) := clopen U /\ U !=set0.

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

Let c_ind (n : nat) (V : set T) (b : bool) := 
  let Wn := 
    if pselect ((U_ n) `&` V !=set0 /\ ~` (U_ n) `&` V !=set0)
    then (U_ n) 
    else split_clopen V in 
  (if b then Wn else ~` Wn) `&` V.

Local Lemma cantor_map : exists (f : cantor_space -> T), 
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

Let tree_map := projT1 (cid (cantor_map)).

Local Lemma tree_map_bij : bijective tree_map.
Proof. 
by rewrite -setTT_bijective; have [? ? ?] := projT2 (cid cantor_map); split. 
Qed.

#[local] HB.instance Definition _ := @BijTT.Build _ _ _ tree_map_bij.

Lemma homeomorphism_cantor_like : 
  exists (f : {splitbij [set: cantor_space] >->  [set: T]}), 
    continuous f /\
    (forall A, closed A -> closed (f@`A)).
Proof.
exists tree_map => /=; have [? ? ?] := projT2 (cid cantor_map); split => //.
move=> A clA; apply: compact_closed; first exact: hsdfT.
apply (@continuous_compact _ _ tree_map); first exact: continuous_subspaceT.
apply: (@subclosed_compact _ _ [set: cantor_space]) => //.
exact: cantor_space_compact.
Qed.

End TreeStructure.
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

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.
Lemma ent_closure {X : uniformType} (x z : X) E : entourage E -> 
  closure [set y | split_ent E (x, y)] z -> E (x, z).
Proof.
pose E' := ((split_ent E) `&` ((split_ent E)^-1)%classic).
move=> entE /(_ [set y | E' (z, y)]) [].
  by rewrite -nbhs_entourageE; exists E' => //; apply: filterI.
by move=> y [/=] + [_]; apply: entourage_split.
Qed.

Section alexandroff_hausdorff.
Context {R: realType} {T : pseudoMetricType R}.

Hypothesis cptT : compact [set: T].
Hypothesis hsdfT : hausdorff_space T.

Section two_pointed.
Context (t0 t1 : T).
Hypothesis T2e : (t0 != t1).

Let ent_balls' (E : set (T*T)) : 
  exists (M : set (set T)), 
    entourage E -> [/\ 
      finite_set M,
      (forall A, M A -> exists a, A a /\ 
        A `<=` closure [set y | split_ent E (a,y)]),
      (exists (A B : set T), M A /\ M B /\ A != B),
      \bigcup_(A in M) A = [set: T] &
      M `<=` closed].
Proof.
case: (pselect (entourage E)); last by move=> ?; exists point.
move=> entE; move: cptT; rewrite compact_cover.
pose fs x := interior [set y | split_ent E (x, y)].
case/(_ T ([set: T]) fs).
- by move=> i _; apply: open_interior.
- move=> t _; exists t => //. 
- by rewrite /fs /interior -nbhs_entourageE; exists (split_ent E).
move=> M' _ Mcov; exists (
    ((fun x => closure (fs x)) @` [set` M']) `|` [set [set t0];[set t1]]) => _.
split.
- rewrite finite_setU; split; first by apply: finite_image; exact: finite_fset.
  exact: finite_set2.
- move=> A []. 
    case=> z M'z <-; exists z; split. 
    apply: subset_closure; apply: nbhs_singleton; apply: nbhs_interior.
    by rewrite -nbhs_entourageE; exists (split_ent E).
  by apply:closure_subset; exact:interior_subset.
  by case => ->; [exists t0 | exists t1]; split => // t ->;
    apply: subset_closure; apply:entourage_refl.
- exists [set t0], [set t1]; split;[|split]. 
  + by right; left.
  + by right; right.
  + apply/eqP; rewrite eqEsubset; case=> /(_ t0) => /= /(_ erefl).
    by move: T2e => /[swap] ->/eqP.
- rewrite -subTset => t /Mcov [t' M't' fsxt]; exists (closure (fs t')).
  left; by exists t' => //.
  by apply: subset_closure.
- move=> ? []; first by case=> ? ? <-; exact: closed_closure.
  by case => ->; apply: accessible_closed_set1; apply: hausdorff_accessible. 
Qed.

Let ent_balls E := projT1 (cid (ent_balls' E)).

Let count_unif' := (cid2 
  ((iffLR countable_uniformityP) (@countable_uniformity_metric _ T))).
Let count_unif := projT1 count_unif'.

Local Lemma ent_count_unif n : entourage (count_unif n).
Proof.
have := projT2 (cid (ent_balls' (count_unif n))).
rewrite /count_unif; case: count_unif'.
by move=> /= f fnA fnE; case /(_ (fnE _)) => _ _ _ + _; rewrite -subTset.
Qed.

Local Lemma count_unif_sub E : entourage E -> exists N, count_unif N `<=` E.
Proof.
by move=> entE; rewrite /count_unif; case: count_unif' => f + ? /=; exact.
Qed.

Hint Resolve ent_count_unif : core.

Let K' (n : nat) : Type := @sigT (set T) (ent_balls (count_unif n)).

Local Lemma K'p n :  K' n.
Proof.
apply: cid; have [//| _ _ _ + _] := projT2 (cid (ent_balls' (count_unif n))).
by rewrite -subTset => /(_ point I) [W Q ?]; exists W; apply Q.
Qed.

Let K n := PointedType (classicType_choiceType (K' n)) (K'p n).
Let Tree := (@tree_of R K).

Let emb_ind n (U : set T) (k : K n) :=
  (if (pselect (projT1 k `&` U !=set0))
  then projT1 k
  else if (pselect (exists e : K n , projT1 e `&` U !=set0)) is left e
    then projT1 (projT1 (cid e))
    else set0) `&` U.
Let emb_invar (U : set T) := closed U /\ U!=set0.

Local Lemma Kn_closed n (e : K n) : closed (projT1 e).
Proof.
case: e => //= W; have [//| _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
exact.
Qed.

Local Lemma cantor_surj_pt1 : exists (f : Tree -> T), 
  continuous f /\ set_surj [set: Tree] [set: T] f.
Proof.
pose entn n := projT2 (cid (ent_balls' (count_unif n))).
have [] := (@tree_map_props (fun (n : nat) => @pointedDiscrete R (K n)) 
  T (emb_ind) (emb_invar) cptT hsdfT).
- done.
- move=> n U; rewrite eqEsubset; split; last by move => t [? ? []].
  move=> t Ut; have [//|_ _ _ + _] := entn n; rewrite -subTset.
  case/(_ t I) => W cbW Wt; exists (existT _ W cbW) => //.
  by rewrite /emb_ind; case: pselect => //=; apply: absurd; exists t.
- move=> n U e [clU Un0]; split.
    apply: closedI => //; case: pselect => //= ?; first exact: Kn_closed.
    case: pselect; last by move=> ?; exact: closed0.
    move=> ?; exact: Kn_closed.
  rewrite /emb_ind; case: pselect => //=  ?; case: pselect.
    by case => i [z [pz bz]]; set P := cid _; have := projT2 P; apply.
  case: Un0 => z Uz; apply: absurd.
  have [//|_ _ _ + _] := entn n; rewrite -subTset; case/(_ z I)=> i bi iz.
  by exists (existT _ _ bi); exists z.
- by move => ? []. 
- by split; [exact: closedT | exists point].
- by move => ? [].
- move=> x y xny; move: hsdfT; rewrite open_hausdorff.
  case/(_ _ _ xny); case => U V /= [/set_mem Ux /set_mem Vy] [oU oV UVI0].
  move: oU; rewrite openE => /(_ _ Ux); rewrite /interior -nbhs_entourageE.
  case => E entE ExU. 
  have [//| n ctE] := @count_unif_sub ((split_ent E) `&` ((split_ent E)^-1%classic)).
    exact: filterI.
  exists n => B [C ebC]; have [//|_ Csub _ _ _] := entn n => embx emby.
  have [[D cbD] /= [Dx Dy]] : exists (e : K n), projT1 e x /\ projT1 e y.
    move: embx emby; rewrite /emb_ind; case: pselect => /=.
      by move => ? [? ?] [? ?]; exists (existT _ _ ebC); split.
    case: pselect ; last by move => ? ? [].
    by move=> e _ [? ?] [? ?]; exists (projT1 (cid e)).
  suff : E (x, y).
    by move/ExU; move/eqP/disjoints_subset:UVI0 => /[apply].
  have [z [Dz DzE]] := Csub _ cbD. 
  have /ent_closure:= DzE _ Dx => /(_ (ent_count_unif n))/ctE [_ /= ?].
  have /ent_closure:= DzE _ Dy => /(_ (ent_count_unif n))/ctE [? _].
  exact: (@entourage_split [uniformType of T] z).
by move=> f [ctsf surjf _]; exists f.
Qed.

Local Lemma cantor_surj_pt2 :
  exists (f : {surj [set: cantor_space] >->  [set: Tree]}), continuous f.
Proof.
have [] := @homeomorphism_cantor_like R Tree; first last.
  by move=> f [ctsf _]; exists f.
apply: cantor_like_finite_prod.
  move=> n /=; have [// | fs _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
  suff -> : [set: {classic K' n}] =  
      (@projT1 (set T) _) @^-1` (projT1 (cid (ent_balls' (count_unif n)))).
    by apply: finite_preimage => //; move=> ? ? _ _; apply: eq_sigT_hprop.
  by rewrite eqEsubset; split => //; case=> /= W p.
move=> n; have [// | _ _ [A [B [pA [pB AB]]]] _ _] := 
  projT2 (cid (ent_balls' (count_unif n))).
simpl; exists ((existT _ _ pA), (existT _ _ pB)).
by move: AB; apply: contra_neq; apply: EqdepFacts.eq_sigT_fst.
Qed.

Local Lemma cantor_surj_twop :
  exists (f : {surj [set: cantor_space] >->  [set: T]}), continuous f.
Proof.
case: cantor_surj_pt2 => f ctsf; case: cantor_surj_pt1.
move => g [ctsg /Psurj [sjg gsjg]]; exists [surj of sjg \o f].
by move=> z; apply continuous_comp; [apply: ctsf|rewrite -gsjg; apply: ctsg].
Qed.
End two_pointed.

Lemma cantor_surj :
  exists (f : {surj [set: cantor_space] >->  [set: T]}), continuous f.
Proof.
case: (pselect (exists (p : T), p != point)).
  case => p ppt; apply: cantor_surj_twop; exact: ppt.
move=> /forallNP xpt.
have : set_surj [set: cantor_space] [set: T] (cst point).
  by move=> q _; exists point => //; have /negP := xpt q; rewrite negbK => /eqP.
by case/Psurj => f cstf; exists f; rewrite -cstf; apply: cst_continuous.
Qed.
Section alexandroff_hausdorff.