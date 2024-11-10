(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum interval rat.
From mathcomp Require Import finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals.
From mathcomp Require Import topology function_spaces separation_axioms.

(**md**************************************************************************)
(* # The Cantor Space and Applications                                        *)
(*                                                                            *)
(* This file develops the theory of the Cantor space, that is bool^nat with   *)
(* the product topology. The two main theorems proved here are                *)
(* homeomorphism_cantor_like, and cantor_surj, a.k.a. Alexandroff-Hausdorff.  *)
(*                                                                            *)
(* ```                                                                        *)
(*          cantor_space == the Cantor space, with its canonical metric       *)
(*         cantor_like T == perfect + compact + hausdroff + zero dimensional  *)
(*             tree_of T == builds a topological tree with levels (T n)       *)
(* ```                                                                        *)
(*                                                                            *)
(* The overall goal of the next few sections is to prove that                 *)
(*       Every compact metric space `T` is the image of the Cantor space.     *)
(*  The overall proof will build two continuous functions                     *)
(*           Cantor space -> a bespoke tree for `T` -> `T`                    *)
(*                                                                            *)
(* The proof is in 4 parts:                                                   *)
(* - Part 1: Some generic machinery about continuous functions from trees.    *)
(* - Part 2: All cantor-like spaces are homeomorphic to the Cantor space.     *)
(*           (an application of part 1)                                       *)
(* - Part 3: Finitely branching trees are Cantor-like.                        *)
(* - Part 4: Every compact metric space has a finitely branching tree with    *)
(*           a continuous surjection. (a second application of part 1)        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.

Definition cantor_space : Type :=
  prod_topology (fun _ : nat => bool).

HB.instance Definition _ := Pointed.on cantor_space.
HB.instance Definition _ := Nbhs.on cantor_space.
HB.instance Definition _ := Topological.on cantor_space.
HB.instance Definition _ := Uniform.on cantor_space.

Definition cantor_like (T : topologicalType) :=
  [/\ perfect_set [set: T],
      compact [set: T],
      hausdorff_space T &
      zero_dimensional T].

Lemma cantor_space_compact : compact [set: cantor_space].
Proof.
have := @tychonoff _ (fun _ : nat => _) _ (fun=> bool_compact).
by congr (compact _); rewrite eqEsubset.
Qed.

Lemma cantor_space_hausdorff : hausdorff_space cantor_space.
Proof.
apply: hausdorff_product => ?; apply: discrete_hausdorff.
Qed.

Lemma cantor_zero_dimensional : zero_dimensional cantor_space.
Proof.
apply: zero_dimension_prod => _; apply: discrete_zero_dimension.
Qed.

Lemma cantor_perfect : perfect_set [set: cantor_space].
Proof. by apply: perfect_diagonal => _; exists (true, false). Qed.

Lemma cantor_like_cantor_space : cantor_like cantor_space.
Proof.
split.
- exact: cantor_perfect.
- exact: cantor_space_compact.
- exact: cantor_space_hausdorff.
- exact: cantor_zero_dimensional.
Qed.


(**md**************************************************************************)
(* ## Part 1                                                                  *)
(*                                                                            *)
(* A tree here has countable levels, and nodes of type `K n` on the nth       *)
(* level.                                                                     *)
(* Each level is in the 'discrete' topology, so the nodes are independent.    *)
(* The goal is to build a map from branches to X.                             *)
(* 1. Each level of the tree corresponds to an approximation of `X`.          *)
(* 2. Each level refines the previous approximation.                          *)
(* 3. Then each branch has a corresponding Cauchy filter.                     *)
(* 4. The overall function from branches to X is a continuous surjection.     *)
(* 5. With an extra disjointness condition, this is also an injection         *)
(*                                                                            *)
(******************************************************************************)
Section topological_trees.
Context {K : nat -> pdiscreteTopologicalType} {X : ptopologicalType}
        (refine_apx : forall n, set X -> K n -> set X)
        (tree_invariant : set X -> Prop).

Hypothesis cmptX : compact [set: X].
Hypothesis hsdfX : hausdorff_space X.
Hypothesis refine_cover : forall n U, U = \bigcup_e @refine_apx n U e.
Hypothesis refine_invar : forall n U e,
  tree_invariant U -> tree_invariant (@refine_apx n U e).
Hypothesis invar_n0 : forall U, tree_invariant U -> U !=set0.
Hypothesis invarT : tree_invariant [set: X].
Hypothesis invar_cl : tree_invariant `<=` closed.
Hypothesis refine_separates: forall x y : X, x != y ->
  exists n, forall (U : set X) e,
    @refine_apx n U e x -> ~@refine_apx n U e y.

Let refine_subset n U e : @refine_apx n U e `<=` U.
Proof. by rewrite [X in _ `<=` X](refine_cover n); exact: bigcup_sup. Qed.

Let T := prod_topology (K : nat -> ptopologicalType).

Local Fixpoint branch_apx (b : T) n :=
  if n is m.+1 then refine_apx (branch_apx b m) (b m) else [set: X].

Let tree_mapF b := filter_from [set: nat] (branch_apx b).

Let tree_map_invar b n : tree_invariant (branch_apx b n).
Proof. by elim: n => // n ?; exact: refine_invar. Qed.

Let tree_map_sub b i j : (i <= j)%N -> branch_apx b j `<=` branch_apx b i.
Proof.
elim: j i => [?|j IH i]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /predU1P[->//|/IH].
by apply: subset_trans; exact: refine_subset.
Qed.

Instance tree_map_filter b : ProperFilter (tree_mapF b).
Proof.
split; first by case => n _ P; case: (invar_n0 (tree_map_invar b n)) => x /P.
apply: filter_from_filter; first by exists 0%N.
move=> i j _ _; exists (maxn i j)  => //; rewrite subsetI.
by split; apply: tree_map_sub; [exact: leq_maxl | exact: leq_maxr].
Qed.

Let tree_map b := lim (tree_mapF b).

Let cvg_tree_map b : cvg (tree_mapF b).
Proof.
have [|x [_ clx]] := cmptX (tree_map_filter b); first exact: filterT.
apply/cvg_ex; exists x => /=; apply: (compact_cluster_set1 _ cmptX) => //.
- exact: filterT.
- exact: filterT.
rewrite eqEsubset; split=> [y cly|? -> //].
have [->//|/refine_separates[n sep]] := eqVneq x y.
have bry : branch_apx b n.+1 y.
  have /closure_id -> := invar_cl (tree_map_invar b n.+1).
  by move: cly; rewrite clusterE; apply; exists n.+1.
suff /sep : branch_apx b n.+1 x by [].
have /closure_id -> := invar_cl (tree_map_invar b n.+1).
by move: clx; rewrite clusterE; apply; exists n.+1.
Qed.

Local Lemma tree_map_surj : set_surj [set: T] [set: X] tree_map.
Proof.
move=> z _; suff : exists g, forall n, branch_apx g n z.
  case=> g gnz; exists g => //; apply: close_eq => // U [oU Uz] V ngV; exists z.
  by split => //; have [n _] := @cvg_tree_map g _ ngV; exact.
have zcov' : forall n (U : set X), exists e, U z -> @refine_apx n U e z.
  move=> n U; have [|?] := pselect (U z); last by exists point.
  by rewrite [X in X z -> _](@refine_cover n U); case => e _ ?; exists e.
pose zcov n U := projT1 (cid (zcov' n U)).
pose fix g n : K n * set X :=
  if n is m.+1
  then (zcov m.+1 (g m).2, @refine_apx m.+1 (g m).2 (zcov m.+1 (g m).2))
  else (zcov O [set: X], @refine_apx O [set: X] (zcov O [set: X])).
pose g' n := (g n).1; have apxg n : branch_apx g' n.+1 = (g n).2.
  by elim: n => //= n ->.
exists g'; elim => // n /= IH.
have /(_ IH) := projT2 (cid (zcov' n (branch_apx g' n))).
by case: n {IH} => // n; rewrite apxg.
Qed.

Let tree_prefix (b : T) (n : nat) :
  \forall c \near b, forall i,  (i < n)%N -> b i = c i.
Proof.
elim: n => [|n IH]; first by near=> z => ?; rewrite ltn0.
near=> z => i; rewrite leq_eqVlt => /predU1P[|iSn]; last by rewrite (near IH z).
move=> [->]; near: z; exists (proj n @^-1` [set b n]).
split => //; suff : @open T (proj n @^-1` [set b n]) by [].
apply: open_comp; [move=> + _; exact: proj_continuous| apply: discrete_open].
Unshelve. all: end_near. Qed.

Let apx_prefix b c n :
  (forall i, (i < n)%N -> b i = c i) -> branch_apx b n = branch_apx c n.
Proof.
elim: n => //= n IH inS; rewrite IH; first by rewrite inS.
by move=> ? ?; exact/inS/ltnW.
Qed.

Let tree_map_apx b n : branch_apx b n (tree_map b).
Proof.
apply: (@closed_cvg _ _ _ (tree_map_filter b)); last exact: cvg_tree_map.
  by apply: invar_cl; exact: tree_map_invar.
by exists n.
Qed.

Local Lemma tree_map_cts : continuous tree_map.
Proof.
move=> b U /cvg_tree_map [n _] /filterS; apply.
rewrite nbhs_simpl /=; near_simpl; have := tree_prefix b n; apply: filter_app.
by near=> z => /apx_prefix ->; exact: tree_map_apx.
Unshelve. all: end_near. Qed.

Let tree_map_setI x y n : tree_map x = tree_map y ->
  refine_apx (branch_apx x n) (x n) `&` refine_apx (branch_apx y n) (y n) !=set0.
Proof.
move=> xyE; exists (tree_map y); split.
  by rewrite -xyE -/(branch_apx x n.+1); exact: tree_map_apx.
by rewrite -/(branch_apx y n.+1); exact: tree_map_apx.
Qed.

Local Lemma tree_map_inj : (forall n U, trivIset [set: K n] (@refine_apx n U)) ->
  set_inj [set: T] tree_map.
Proof.
move=> triv x y _ _ xyE; apply: functional_extensionality_dep => n.
suff : forall n, branch_apx x n = branch_apx y n.
  move=> brE; apply: (@triv n (branch_apx x n) _ _ I I).
  by rewrite [in X in _ `&` X]brE; exact: tree_map_setI.
elim => // m /= brE.
rewrite (@triv m (branch_apx x m) (x m) (y m) I I) 1?brE//.
by rewrite -[in X in X `&` _]brE; exact: tree_map_setI.
Qed.

Lemma tree_map_props : exists f : T -> X,
  [/\ continuous f,
      set_surj [set: T] [set: X] f &
      (forall n U, trivIset [set: K n] (@refine_apx n U)) ->
        set_inj [set: T] f].
Proof.
exists tree_map; split.
- exact: tree_map_cts.
- exact: tree_map_surj.
- exact: tree_map_inj.
Qed.

End topological_trees.

(**md**************************************************************************)
(* ## Part 2                                                                  *)
(* We can use `tree_map_props` to build a homeomorphism from the              *)
(* cantor_space to a Cantor-like space T.                                     *)
(******************************************************************************)

Section TreeStructure.
Context {R : realType} {T : pseudoPMetricType R}.
Hypothesis cantorT : cantor_like T.

Let dsctT : zero_dimensional T.   Proof. by case: cantorT. Qed.
Let pftT  : perfect_set [set: T]. Proof. by case: cantorT. Qed.
Let cmptT : compact [set: T].     Proof. by case: cantorT. Qed.
Let hsdfT : @hausdorff_space T.   Proof. by case: cantorT. Qed.

Let c_invar (U : set T) := clopen U /\ U !=set0.

Let U_ := unsquash (clopen_surj cmptT).

Let split_clopen' (U : set T) : exists V,
  open U -> U !=set0 -> [/\ clopen V, V `&` U !=set0 & ~`V `&` U !=set0].
Proof.
have [oU|?] := pselect (open U); last by exists point.
have [Un0|?] := pselect (U !=set0); last by exists point.
have [x [y] [Ux] Uy xny] := (iffLR perfectTP_ex) pftT U oU Un0.
have [V [clV Vx Vy]] := dsctT xny; exists V => _ _.
by split => //; [exists x | exists y].
Qed.

Let split_clopen (U : set T) := projT1 (cid (split_clopen' U)).

Let c_ind n (V : set T) (b : bool) :=
  let Wn :=
    if pselect ((U_ n) `&` V !=set0 /\ ~` (U_ n) `&` V !=set0)
    then U_ n else split_clopen V in
  (if b then Wn else ~` Wn) `&` V.

Local Lemma cantor_map : exists f : cantor_space -> T,
  [/\ continuous f,
      set_surj [set: cantor_space] [set: T] f &
      set_inj [set: cantor_space] f ].
Proof.
have [] := @tree_map_props (fun=> bool) T c_ind c_invar cmptT hsdfT.
- move=> n V; rewrite eqEsubset; split => [t Vt|t [? ? []]//].
  have [?|?] := pselect (U_ n `&` V !=set0 /\ ~` U_ n `&` V !=set0).
  + have [Unt|Unt] := pselect (U_ n t).
    * by exists true => //; rewrite /c_ind; case: pselect.
    * by exists false => //; rewrite /c_ind; case: pselect.
  + have [scVt|scVt] := pselect (split_clopen V t).
    * by exists true => //; rewrite /c_ind; case: pselect.
    * by exists false => //; rewrite /c_ind; case: pselect.
- move=> n U e [] clU Un0; rewrite /c_ind; case: pselect => /=.
  + move=> [UU CUU]; case: e => //; split => //; apply: clopenI => //.
      exact: funS.
    by apply: clopenC => //; exact: funS.
  + move=> _; have [|//|clscU scUU CscUU] := projT2 (cid (split_clopen' U)).
      by case: clU.
    case: e; split => //; first exact: clopenI.
    by apply: clopenI => //; exact: clopenC.
- by move=> ? [].
- by split; [exact: clopenT | exists point].
- by move=> ? [[]].
- move=> x y /dsctT [A [clA Ax Any]].
  have [n _ UnA] := @surj _ _ _ _ U_ _ clA; exists n => V e.
  have [|+ _] := pselect (V y); last by apply: subsetC => ? [].
  have [Vx Vy|? _ []//] := pselect (V x).
  rewrite {1 2}/c_ind; case: pselect => /=; rewrite ?UnA.
    by move=> _; case: e; case => // ? ?; apply/not_andP; left.
  by apply: absurd; split; [exists x | exists y].
- move=> f [ctsf surjf injf]; exists f; split => //.
  apply: injf.
  by move=> n U i j _ _ [z] [] [] + Uz [+ _]; move: i j => [] [].
Qed.

Let tree_map := projT1 (cid cantor_map).

Let tree_map_bij : bijective tree_map.
Proof.
by rewrite -setTT_bijective; have [? ? ?] := projT2 (cid cantor_map); split.
Qed.

#[local] HB.instance Definition _ := @BijTT.Build _ _ _ tree_map_bij.

Lemma homeomorphism_cantor_like :
  exists f : {splitbij [set: cantor_space] >-> [set: T]},
    continuous f /\ (forall A, closed A -> closed (f @` A)).
Proof.
exists tree_map => /=.
have [cts surj inje] := projT2 (cid cantor_map); split; first exact: cts.
move=> A clA; apply: (compact_closed hsdfT).
apply: (@continuous_compact _ _ tree_map); first exact: continuous_subspaceT.
apply: (@subclosed_compact _ _ [set: cantor_space]) => //.
exact: cantor_space_compact.
Qed.

End TreeStructure.

Section cantor.
Context {R : realType}.

(**md**************************************************************************)
(* ## Part 3: Finitely branching trees are Cantor-like                        *)
(******************************************************************************)
Section FinitelyBranchingTrees.

Definition tree_of (T : nat -> pointedType) : Type :=
  prod_topology (fun n => discrete_topology (T n)).

HB.instance Definition _ (T : nat -> pointedType) : Pointed (tree_of T):= 
  Pointed.on (tree_of T).

HB.instance Definition _ (T : nat -> pointedType) := Uniform.on (tree_of T).

HB.instance Definition _ (T : nat -> pointedType) : 
    @PseudoMetric R _ :=
   @PseudoMetric.on (tree_of T).

Lemma cantor_like_finite_prod (T : nat -> ptopologicalType) :
  (forall n, finite_set [set: discrete_topology (T n)]) ->
  (forall n, (exists xy : T n * T n, xy.1 != xy.2)) ->
  cantor_like (tree_of T).
Proof.
move=> finiteT twoElems; split.
- exact/(@perfect_diagonal (discrete_topology \o T))/twoElems.
- have := tychonoff (fun n => finite_compact (finiteT n)).
  set A := (X in compact X -> _).
  suff : A = [set: tree_of (fun x : nat => T x)] by move=> ->.
  by rewrite eqEsubset.
- apply: (@hausdorff_product _ (discrete_topology \o T)) => n.
  by apply: discrete_hausdorff; exact: discrete_space_discrete.
- apply: zero_dimension_prod => ?; apply: discrete_zero_dimension.
Qed.

End FinitelyBranchingTrees.

(**md**************************************************************************)
(* ## Part 4: Building a finitely branching tree to cover `T`                 *)
(******************************************************************************)
Section alexandroff_hausdorff.
Context {T : pseudoPMetricType R}.

Hypothesis cptT : compact [set: T].
Hypothesis hsdfT : hausdorff_space T.

Section two_pointed.
Context (t0 t1 : T).
Hypothesis T2e : t0 != t1.

Let ent_balls' (E : set (T * T)) :
  exists M : set (set T), entourage E -> [/\
    finite_set M,
    forall A, M A -> exists a, A a /\
      A `<=` closure (xsection (split_ent E) a),
    exists A B : set T, M A /\ M B /\ A != B,
    \bigcup_(A in M) A = [set: T] &
    M `<=` closed].
Proof.
have [entE|?] := pselect (entourage E); last by exists point.
move: cptT; rewrite compact_cover.
pose fs x := interior (xsection (split_ent E) x).
move=> /(_ T [ set: T] fs)[t _|t _ |].
- exact: open_interior.
- exists t => //; rewrite /fs /interior.
  by rewrite -nbhs_entourageE; exists (split_ent E) => // ? /xsectionP.
move=> M' _ Mcov; exists
  ((closure \o fs) @` [set` M'] `|` [set [set t0]; [set t1]]).
move=> _; split=> [|A [|]| | |].
- rewrite finite_setU; split; first exact/finite_image/finite_fset.
  exact: finite_set2.
- move=> [z M'z] <-; exists z; split.
  + apply: subset_closure; apply: nbhs_singleton; apply: nbhs_interior.
      by rewrite -nbhs_entourageE; exists (split_ent E) => // t /xsectionP.
  + by apply: closure_subset; exact: interior_subset.
- by case => ->; [exists t0 | exists t1]; split => // t ->;
    apply/subset_closure/xsectionP; exact: entourage_refl.
- exists [set t0], [set t1]; split;[|split].
  + by right; left.
  + by right; right.
  + apply/eqP; rewrite eqEsubset => -[] /(_ t0 erefl).
    by move: T2e => /[swap] -> /eqP.
- rewrite -subTset => t /Mcov [t' M't' fsxt]; exists (closure (fs t')).
    by left; exists t'.
  exact: subset_closure.
- move=> ? [[? ?] <-|]; first exact: closed_closure.
  by move=> [|] ->; exact/accessible_closed_set1/hausdorff_accessible.
Qed.

Let ent_balls E := projT1 (cid (ent_balls' E)).

Let count_unif' := cid2
  ((iffLR countable_uniformityP) (@countable_uniformity_metric _ T)).

Let count_unif := projT1 count_unif'.

Let ent_count_unif n : entourage (count_unif n).
Proof.
have := projT2 (cid (ent_balls' (count_unif n))).
rewrite /count_unif; case: count_unif'.
by move=> /= f fnA fnE; case /(_ (fnE _)) => _ _ _ + _; rewrite -subTset.
Qed.

Let count_unif_sub E : entourage E -> exists N, count_unif N `<=` E.
Proof.
by move=> entE; rewrite /count_unif; case: count_unif' => f + ? /=; exact.
Qed.

Let K' n : Type := @sigT (set T) (ent_balls (count_unif n)).

Let K'p n : K' n.
Proof.
apply: cid; have [//| _ _ _ + _] := projT2 (cid (ent_balls' (count_unif n))).
by rewrite -subTset => /(_ point I) [W Q ?]; exists W; exact: Q.
Qed.

HB.instance Definition _ n := gen_eqMixin (K' n).
HB.instance Definition _ n := gen_choiceMixin (K' n).
HB.instance Definition _ n := isPointed.Build (K' n) (K'p n).

Let K n := discrete_topology (K' n).
Let Tree := @tree_of K.

HB.instance Definition _ n :=
  DiscreteTopology.on (K n). 
HB.instance Definition _ n :=
  Pointed.on (K n). 

Let embed_refine n (U : set T) (k : K n) :=
  (if pselect (projT1 k `&` U !=set0)
  then projT1 k
  else if pselect (exists e : K n , projT1 e `&` U !=set0) is left e
    then projT1 (projT1 (cid e))
    else set0) `&` U.
Let embed_invar (U : set T) := closed U /\ U !=set0.

Let Kn_closed n (e : K n) : closed (projT1 e).
Proof.
case: e => W; have [//| _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
exact.
Qed.

Local Lemma cantor_surj_pt1 : exists2 f : Tree -> T,
  continuous f & set_surj [set: Tree] [set: T] f.
Proof.
pose entn n := projT2 (cid (ent_balls' (count_unif n))).
have [ | |? []//| |? []// | |] := @tree_map_props
    K T (embed_refine) (embed_invar) cptT hsdfT.
- move=> n U; rewrite eqEsubset; split=> [t Ut|t [? ? []]//].
  have [//|_ _ _ + _] := entn n; rewrite -subTset.
  move=> /(_ t I)[W cbW Wt]; exists (existT _ W cbW) => //.
  by rewrite /embed_refine; case: pselect => //=; apply: absurd; exists t.
- move=> n U e [clU Un0]; split.
    apply: closedI => //; case: pselect => //= ?.
    by case: pselect => ?; [exact: Kn_closed|exact: closed0].
  rewrite /embed_refine; case: pselect => //= ?; case: pselect.
    by case=> i [z [pz bz]]; set P := cid _; have := projT2 P; apply.
  case: Un0 => z Uz; apply: absurd.
  have [//|_ _ _ + _] := entn n; rewrite -subTset; move=> /(_ z I)[i bi iz].
  by exists (existT _ _ bi), z.
- by split; [exact: closedT | exists point].
- move=> x y xny; move: hsdfT; rewrite open_hausdorff.
  move=> /(_ _ _ xny)[[U V]] /= [/set_mem Ux /set_mem Vy] [+ oV UVI0].
  rewrite openE => /(_ _ Ux); rewrite /interior -nbhs_entourageE => -[E entE ExU].
  have [//| n ctE] :=
    @count_unif_sub (split_ent E `&` (split_ent E)^-1%relation).
    exact: filterI.
  exists n => B [C ebC]; have [//|_ Csub _ _ _ embx emby] := entn n.
  have [[D cbD] /= Dx Dy] : exists2 e : K n, projT1 e x & projT1 e y.
    move: embx emby; rewrite /embed_refine; case: pselect => /=.
      by move=> ? [? ?] [? ?]; exists (existT _ _ ebC).
    case: pselect; last by move => ? ? [].
    by move=> e _ [? ?] [? ?]; exists (projT1 (cid e)).
  suff : E (x, y).
    by move/xsectionP/ExU; move/eqP/disjoints_subset: UVI0 => /[apply].
  have [z [Dz DzE]] := Csub _ cbD.
  have /ent_closure := DzE _ Dx => /(_ (ent_count_unif n))/xsectionP/ctE [_ /= Exz].
  have /ent_closure := DzE _ Dy => /(_ (ent_count_unif n))/xsectionP/ctE [Ezy _].
  exact: (@entourage_split T z).
by move=> f [ctsf surjf _]; exists f.
Qed.

Local Lemma cantor_surj_pt2 :
  exists f : {surj [set: cantor_space] >-> [set: Tree]}, continuous f.
Proof.
have [|f [ctsf _]] := @homeomorphism_cantor_like R Tree; last by exists f.
apply: (@cantor_like_finite_prod (discrete_topology \o K)) => [n /=|n].
  have [//| fs _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
  suff -> : [set: {classic K' n}] =
      (@projT1 (set T) _) @^-1` (projT1 (cid (ent_balls' (count_unif n)))).
    by apply: finite_preimage => // ? ? _ _; exact: eq_sigT_hprop.
  by rewrite eqEsubset; split => // -[].
have [//| _ _ [A [B [pA [pB AB]]]] _ _] :=
  projT2 (cid (ent_balls' (count_unif n))).
exists (existT _ _ pA, existT _ _ pB) => /=.
by move: AB; apply: contra_neq => -[].
Qed.

Local Lemma cantor_surj_twop :
  exists f : {surj [set: cantor_space] >-> [set: T]}, continuous f.
Proof.
move: cantor_surj_pt2 cantor_surj_pt1 => -[f ctsf] [g ctsg /Psurj[sjg gsjg]].
exists [surj of sjg \o f] => z.
by apply continuous_comp; [exact: ctsf|rewrite -gsjg; exact: ctsg].
Qed.

End two_pointed.

(** The Alexandroff-Hausdorff theorem *)
Theorem cantor_surj :
  exists f : {surj [set: cantor_space] >-> [set: T]}, continuous f.
Proof.
have [[p ppt]|/forallNP xpt] := pselect (exists p : T, p != point).
  by apply: cantor_surj_twop; exact: ppt.
have /Psurj[f cstf] : set_surj [set: cantor_space] [set: T] (cst point).
  by move=> q _; exists point => //; have /negP/negPn/eqP -> := xpt q.
by exists f; rewrite -cstf; exact: cst_continuous.
Qed.

End alexandroff_hausdorff.
End cantor.
