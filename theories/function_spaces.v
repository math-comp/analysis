(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import boolp classical_sets functions set_interval.
From mathcomp Require Import cardinality mathcomp_extra fsbigop.
From mathcomp Require Import reals signed topology separation_axioms.

(**md**************************************************************************)
(* # The topology of functions spaces                                         *)
(*                                                                            *)
(* Function spaces have no canonical topology. We develop the theory of       *)
(* several general-purpose function space topologies here.                    *)
(*                                                                            *)
(* ## Topologies on `U -> V`                                                  *)
(* There is no canonical topology on `U->V` in this library. Mathematically,  *)
(* the right topology usually depends on context. We provide three general    *)
(* options in this file which work for various amounts of structures on the   *)
(* domain and codomain.                                                       *)
(*                                                                            *)
(* Topologies we consider are:                                                *)
(* - Topology of pointwise convergence                                        *)
(*   + requires only a topology on V                                          *)
(* - Topology of uniform convergence                                          *)
(*   + requires only a uniformity on V                                        *)
(* - Topology of uniform convergence on subspaces                             *)
(*   + requires only a uniformity on V                                        *)
(* - The compact-open topology                                                *)
(*   + requires a topology on U and V                                         *)
(*                                                                            *)
(* if you're looking for the topology of compact convergence, note that       *)
(* it is exactly the compact-open topology via `compact_open_fam_compactP`.   *)
(*                                                                            *)
(* To locally assign a topology to `->`, import one of the following modules  *)
(* - ArrowAsProduct assigns the product topology                              *)
(* - ArrowAsUniformType assigns the uniform topology                          *)
(* - ArrowAsCompactOpen assign the compact-open topology                      *)
(*                                                                            *)
(* The major results are:                                                     *)
(* - Compactness in the product topology via Tychonoff's                      *)
(* - Compactness in the compact convergence topology via Ascoli's             *)
(* - Conditions when the supremum and weak topology commute in products       *)
(* - The compact-open topology is the topopology of compact convergence       *)
(* - Cartesian closedness for the category of locally compact topologies      *)
(*                                                                            *)
(* ## Function space notations                                                *)
(* ```                                                                        *)
(*       {uniform` A -> V} == the space U -> V, equipped with the topology    *)
(*                            of uniform convergence from a set A to V, where *)
(*                            V is a uniformType                              *)
(*        {uniform U -> V} := {uniform` [set: U] -> V}                        *)
(*    {uniform A, F --> f} == F converges to f in {uniform A -> V}            *)
(*      {uniform, F --> f} := {uniform setT, F --> f}                         *)
(*       prod_topology I T == the topology of pointwise convergence on the    *)
(*                            dependent space `forall (i:I), T i`             *)
(*  arrow_uniform_type U V == the topology of uniform convergence on the      *)
(*                            type `U -> V`                                   *)
(*           {ptws U -> V} == prod_topology for the non-dependent product     *)
(* separate_points_from_closed f == for a closed set U and point x outside    *)
(*                            some member of the family f, it sends f_i(x)    *)
(*                            outside (closure (f_i @` U))                    *)
(*                            Used together with join_product.                *)
(*          join_product f == the function (x => f ^~ x)                      *)
(*                            When the family f separates points from closed  *)
(*                            sets, join_product is an embedding.             *)
(*         {ptws, F --> f} == F converges to f in {ptws U -> V}               *)
(*    {family fam, U -> V} == the supremum of {uniform A -> f} for each A in  *)
(*                            `fam`                                           *)
(*                            In particular, {family compact, U -> V} is the  *)
(*                            topology of compact convergence.                *)
(*   {family fam, F --> f} == F converges to f in {family fam, U -> V}        *)
(*  {compact_open, U -> V} == compact-open topology                           *)
(* {compact_open, F --> f} == F converges to f in {compact_open, U -> V}      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Ascoli's theorem notations                                              *)
(* ```                                                                        *)
(*      equicontinuous W x == the set (W : X -> Y) is equicontinuous at x     *)
(*            singletons T := [set [set x] | x in [set: T]]                   *)
(*  pointwise_precompact W == for each (x : X), the set of images             *)
(*                            [f x | f in W] is precompact                    *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "{ 'uniform`' A -> V }"
  (at level 0, A at level 69, format "{ 'uniform`'  A  ->  V }").
Reserved Notation "{ 'uniform' U -> V }"
  (at level 0, U at level 69, format "{ 'uniform'  U  ->  V }").
Reserved Notation "{ 'uniform' A , F --> f }"
  (at level 0, A at level 69, F at level 69,
   format "{ 'uniform'  A ,  F  -->  f }").
Reserved Notation "{ 'uniform' , F --> f }"
  (at level 0, F at level 69,
   format "{ 'uniform' ,  F  -->  f }").
Reserved Notation "{ 'ptws' U -> V }"
  (at level 0, U at level 69, format "{ 'ptws'  U  ->  V }").
Reserved Notation "{ 'ptws' , F --> f }"
  (at level 0, F at level 69, format "{ 'ptws' ,  F  -->  f }").
Reserved Notation "{ 'family' fam , U -> V }"
  (at level 0, U at level 69, format "{ 'family'  fam ,  U  ->  V }").
Reserved Notation "{ 'family' fam , F --> f }"
  (at level 0, F at level 69, format "{ 'family'  fam ,  F  -->  f }").
Reserved Notation "{ 'compact-open' , U -> V }"
  (at level 0, U at level 69, format "{ 'compact-open' ,  U  ->  V }").
Reserved Notation "{ 'compact-open' , F --> f }"
  (at level 0, F at level 69, format "{ 'compact-open' ,  F  -->  f }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := idtac.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Product topology, also known as the topology of pointwise convergence *)
Section Product_Topology.

Definition prod_topology {I : Type} (T : I -> Type) := forall i, T i.

Variable I : Type.

Definition product_topology_def (T : I -> topologicalType) :=
  sup_topology (fun i => Topological.class
    (weak_topology (fun f : [the choiceType of forall i, T i] => f i))).

HB.instance Definition _ (T : I -> topologicalType) :=
  Topological.copy (prod_topology T) (product_topology_def T).

HB.instance Definition _ (T : I -> uniformType) :=
  Uniform.copy (prod_topology T)
    (sup_topology (fun i => Uniform.class
      [the uniformType of weak_topology (@proj _ T i)])).

HB.instance Definition _ (R : realType) (Ii : countType)
    (Tc : Ii -> pseudoMetricType R) := PseudoMetric.copy (prod_topology Tc)
  (sup_pseudometric (fun i => PseudoMetric.class
     [the pseudoMetricType R of weak_topology (@proj _ Tc i)]) (countableP _)).

End Product_Topology.

Notation "{ 'ptws' U -> V }" := (prod_topology (fun _ : U => V)) : type_scope.
Notation "{ 'ptws' , F --> f }" :=
  (cvg_to F (nbhs (f : {ptws _ -> _}))) : classical_set_scope.

Module ArrowAsProduct.
HB.instance Definition _ (U : Type) (T : U -> topologicalType) :=
  Topological.copy (forall x : U, T x) (prod_topology T).

HB.instance Definition _ (U : Type) (T : U -> uniformType) :=
  Uniform.copy (forall x : U, T x) (prod_topology T).

HB.instance Definition _ (U T : topologicalType) :=
  Topological.copy 
    (continuousType U T) 
    (weak_topology (id : continuousType U T -> (U -> T))).

HB.instance Definition _ (U : topologicalType) (T : uniformType) :=
  Uniform.copy 
    (continuousType U T) 
    (weak_topology (id : continuousType U T -> (U -> T))).

End ArrowAsProduct.

Section product_spaces.
Local Import ArrowAsProduct.

Section projection_maps.
Context {I : eqType} {K : I -> topologicalType}.

Lemma proj_continuous i : continuous (@proj I K i).
Proof.
move=> f; have /cvg_sup/(_ i)/cvg_image : f --> f by apply: cvg_id.
move=> h; apply: cvg_trans (h _) => {h}.
  by move=> Q /= [W nbdW <-]; apply: filterS nbdW; exact: preimage_image.
rewrite eqEsubset; split => y //; exists (dfwith f i y) => //.
by rewrite dfwithin.
Qed.

Lemma dfwith_continuous g (i : I) : continuous (@dfwith I K g i).
Proof.
move=> z U [] P [] [] Q QfinP <- [] V JV Vpz.
move/(@preimage_subset _ _ (dfwith g i))/filterS; apply.
apply: (@filterS _ _ _ ((dfwith g i) @^-1` V)); first by exists V.
have [L Lsub /[dup] VL <-] := QfinP _ JV; rewrite preimage_bigcap.
apply: filter_bigI => /= M /[dup] LM /Lsub /set_mem [] w _ [+] + /[dup] + <-.
have [->|wnx] := eqVneq w i => N oN NM.
  apply: (@filterS _ _ _ N); first by move=> ? ?; rewrite /= dfwithin.
  apply: open_nbhs_nbhs; split => //; move: Vpz.
  by rewrite -VL => /(_ _ LM); rewrite -NM /= dfwithin.
apply: nearW => y /=; move: Vpz.
by rewrite -VL => /(_ _ LM); rewrite -NM /= ?dfwithout // eq_sym.
Qed.

Lemma proj_open i (A : set (prod_topology K)) : open A -> open (proj i @` A).
Proof.
move=> oA; rewrite openE => z [f Af <-]; rewrite openE in oA.
have {oA} := oA _ Af; rewrite /interior => nAf.
apply: (@filterS _ _ _ ((dfwith f i) @^-1` A)).
  by move=> w Apw; exists (dfwith f i w) => //; rewrite projK.
apply: dfwith_continuous => /=; move: nAf; congr (nbhs _ A).
by apply: functional_extensionality_dep => ?; case: dfwithP.
Qed.

Lemma hausdorff_product :
  (forall x, hausdorff_space (K x)) -> hausdorff_space (forall x, K x).
Proof.
move=> hsdfK p q /= clstr; apply: functional_extensionality_dep => x.
apply: hsdfK; move: clstr; rewrite ?cluster_cvgE /= => -[G PG [GtoQ psubG]].
exists (proj x @ G); [exact: fmap_proper_filter|split].
  apply: cvg_trans; last exact: (@proj_continuous x q).
  by apply: cvg_app; exact: GtoQ.
move/(cvg_app (proj x)): psubG => /cvg_trans; apply.
exact: proj_continuous.
Qed.

End projection_maps.

Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :
  (forall i, compact (A i)) ->
  compact [set f : forall i, T i | forall i, A i (f i)].
Proof.
case: (pselect ([set f : forall i, T i | forall i, A i (f i)] == set0)). 
  move/eqP => -> _; exact: compact0.
case/negP/set0P=> a0 Aa0 Aco; rewrite compact_ultra => F FU FA.
set subst_coord := fun (i : I) (pi : T i) (f : forall x : I, T x) (j : I) =>
  if eqP is ReflectT e then ecast i (T i) (esym e) pi else f j.
have subst_coordT i pi f : subst_coord i pi f i = pi.
  rewrite /subst_coord; case: eqP => // e.
  by rewrite (eq_irrelevance e (erefl _)).
have subst_coordN i pi f j : i != j -> subst_coord i pi f j = f j.
  move=> inej; rewrite /subst_coord; case: eqP => // e.
  by move: inej; rewrite {1}e => /negP.
have pr_surj i : @^~ i @` [set: forall i, T i] = setT.
  rewrite predeqE => pi; split=> // _.
  by exists (subst_coord i pi a0) => //; rewrite subst_coordT.
pose pF i : set_system _ := [set @^~ i @` B | B in F].
have pFultra i : UltraFilter (pF i) by exact: ultra_image (pr_surj i).
have pFA i : pF i (A i).
  exists [set g | forall i, A i (g i)] => //.
  rewrite predeqE => pi; split; first by move=> [g Ag <-]; apply: Ag.
  move=> Aipi; have [f Af] := filter_ex FA.
  exists (subst_coord i pi f); last exact: subst_coordT.
  move=> j; have [<-{j}|] := eqVneq i j; first by rewrite subst_coordT.
  by move=> /subst_coordN ->; apply: Af.
have cvpFA i : A i `&` [set p | pF i --> p] !=set0.
  by rewrite -ultra_cvg_clusterE; apply: Aco.
exists (fun i => xget (a0 i) (A i `&` [set p | pF i --> p])).
split=> [i|]; first by have /(xgetPex (a0 i)) [] := cvpFA i.
apply/cvg_sup => i; apply/cvg_image=> //. 
by have /(xgetPex (a0 i)) [] := cvpFA i.
Qed.

Lemma perfect_prod {I : Type} (i : I) (K : I -> topologicalType) :
  perfect_set [set: K i] -> perfect_set [set: forall i, K i].
Proof.
move=> /perfectTP KPo; apply/perfectTP => f oF; apply: (KPo (f i)).
rewrite (_ : [set f i] = proj i @` [set f]).
  by apply: (@proj_open {classic I} _ i); exact: oF.
by rewrite eqEsubset; split => ? //; [move=> -> /=; exists f | case=> g ->].
Qed.

Lemma perfect_diagonal (K : nat -> topologicalType) :
  (forall i, exists xy : K i * K i, xy.1 != xy.2) ->
  perfect_set [set: forall i, K i].
Proof.
move=> npts; split; first exact: closedT.
rewrite eqEsubset; split => f // _.
pose distincts (i : nat) := projT1 (sigW (npts i)).
pose derange i (z : K i) :=
  if z == (distincts i).1 then (distincts i).2 else (distincts i).1.
pose g (N i : nat) := if (i < N)%N then f i else derange _ (f i).
have gcvg : g @ \oo --> f.
  apply/cvg_sup => N U [V] [[W] oW <-] WfN WU.
  by apply: (filterS WU); rewrite nbhs_simpl /g; exists N.+1 => // i /= ->.
move=> A /gcvg; rewrite nbhs_simpl => -[N _ An].
exists (g N); split => //; last by apply: An; rewrite /= leqnn.
apply/eqP => M; suff: g N N != f N by rewrite M; move/eqP.
rewrite /g ltnn /derange eq_sym; have [->|//] := eqVneq (f N) (distincts N).1.
exact: projT2 (sigW (npts N)).
Qed.

Lemma zero_dimension_prod (I : choiceType) (T : I -> topologicalType) :
  (forall i, zero_dimensional (T i)) ->
  zero_dimensional (forall i, T i).
Proof.
move=> dctTI x y /eqP xneqy.
have [i/eqP/dctTI [U [clU Ux nUy]]] : exists i, x i <> y i.
  by apply/existsNP=> W; exact/xneqy/functional_extensionality_dep.
exists (proj i @^-1` U); split => //; apply: clopen_comp => //.
exact/proj_continuous.
Qed.

Lemma totally_disconnected_prod (I : choiceType)
  (T : I -> topologicalType) (A : forall i, set (T i)) :
  (forall i, totally_disconnected (A i)) ->
  @totally_disconnected (forall i, T i) (fun f => forall i, A i (f i)).
Proof.
move=> dsctAi x /= Aix; rewrite eqEsubset; split; last first.
  by move=> ? ->; exact: connected_component_refl.
move=> f /= [C /= [Cx CA ctC Cf]]; apply/functional_extensionality_dep => i.
suff : proj i @` C `<=` [set x i] by apply; exists f.
rewrite -(dsctAi i) // => Ti ?; exists (proj i @` C) => //.
split; [by exists x | by move=> ? [r Cr <-]; exact: CA |].
apply/(connected_continuous_connected ctC)/continuous_subspaceT.
exact: proj_continuous.
Qed.

(**md A handy technique for embedding a space `T` into a product. The key
  interface is `separate_points_from_closed`, which guarantees that the
  topologies
   - `T`'s native topology
   - `sup (weak f_i)`: the sup of all the weak topologies of `f_i`
   - `weak (x => (f_1 x, f_2 x, ...))`: the weak topology from the product space

  are equivalent (the last equivalence seems to require `accessible_space`). *)
Section product_embeddings.
Context {I : choiceType} {T : topologicalType} {U_ : I -> topologicalType}.
Variable (f_ : forall i, T -> U_ i).

Definition separate_points_from_closed := forall (U : set T) x,
  closed U -> ~ U x -> exists i, ~ (closure (f_ i @` U)) (f_ i x).

Hypothesis sepf : separate_points_from_closed.
Hypothesis ctsf : forall i, continuous (f_ i).

Let weakT := [the topologicalType of
  sup_topology (fun i => Topological.on (weak_topology (f_ i)))].

Let PU := [the topologicalType of prod_topology U_].

Local Notation sup_open := (@open weakT).
Local Notation "'weak_open' i" := (@open weakT) (at level 0).
Local Notation natural_open := (@open T).

Lemma weak_sep_cvg (F : set_system T) (x : T) :
  Filter F -> (F --> (x : T)) <-> (F --> (x : weakT)).
Proof.
move=> FF; split.
  move=> FTx; apply/cvg_sup => i U.
  have /= -> := @nbhsE (weak_topology (f_ i)) x.
  case=> B [[C oC <- ?]] /filterS; apply; apply: FTx; rewrite /= nbhsE.
  by exists (f_ i @^-1` C) => //; split => //; exact: open_comp.
move/cvg_sup => wiFx U; rewrite /= nbhs_simpl nbhsE => [[B [oB ?]]].
move/filterS; apply; have [//|i nclfix] := @sepf _ x (open_closedC oB).
apply: (wiFx i); have /= -> := @nbhsE (weak_topology (f_ i)) x.
exists (f_ i @^-1` (~` closure [set f_ i x | x in ~` B])); [split=>//|].
  apply: open_comp; last by rewrite ?openC//; exact: closed_closure.
  by move=> + _; exact: (@weak_continuous _ _ (f_ i)).
rewrite -interiorC interiorEbigcup preimage_bigcup => z [V [oV]] VnB => /VnB.
by move/forall2NP => /(_ z) [] // /contrapT.
Qed.

Lemma weak_sep_nbhsE x : @nbhs T T x = @nbhs T weakT x.
Proof.
rewrite predeqE => U; split; move: U.
  by have P := weak_sep_cvg x (nbhs_filter (x : weakT)); exact/P.
by have P := weak_sep_cvg x (nbhs_filter (x : T)); exact/P.
Qed.

Lemma weak_sep_openE : @open T = @open weakT.
Proof.
rewrite predeqE => A; rewrite ?openE /interior.
by split => + z => /(_ z); rewrite weak_sep_nbhsE.
Qed.

Definition join_product (x : T) : PU := f_ ^~ x.

Lemma join_product_continuous : continuous join_product.
Proof.
suff : continuous (join_product : weakT -> PU).
  by move=> cts x U => /cts; rewrite nbhs_simpl /= -weak_sep_nbhsE.
move=> x; apply/cvg_sup; first exact/fmap_filter/(nbhs_filter (x : weakT)).
move=> i; move: x; apply/(@continuousP _ (weak_topology (@^~ i))) => A [B ? E].
rewrite -E (_ : @^~ i =  proj i) //.
have -> : join_product @^-1` (proj i @^-1` B) = f_ i @^-1` B by [].
apply: open_comp => // + _; rewrite /cvg_to => x U.
by rewrite nbhs_simpl /= -weak_sep_nbhsE; move: x U; exact: ctsf.
Qed.

Local Notation prod_open := (@open (subspace (range join_product))).

Lemma join_product_open (A : set T) : open A ->
  open ((join_product @` A) : set (subspace (range join_product))).
Proof.
move=> oA; rewrite openE => y /= [x Ax] jxy.
have [// | i nAfiy] := @sepf (~` A) x (open_closedC oA).
pose B : set PU := proj i @^-1` (~` closure (f_ i @` ~` A)).
apply: (@filterS _ _ _ (range join_product `&` B)).
  move=> z [[w ?]] wzE Bz; exists w => //.
  move: Bz; rewrite /B -wzE -interiorC interiorEbigcup.
  case=> K [oK KsubA] /KsubA.
  have -> : proj i (join_product w) = f_ i w by [].
  by move=> /exists2P/forallNP/(_ w)/not_andP [] // /contrapT.
apply: open_nbhs_nbhs; split; last by rewrite -jxy.
apply: openI; first exact: open_subspaceT.
apply: open_subspaceW; apply: open_comp; last exact/closed_openC/closed_closure.
by move=> + _; exact: proj_continuous.
Qed.

Lemma join_product_inj : accessible_space T -> set_inj [set: T] join_product.
Proof.
move=> /accessible_closed_set1 cl1 x y; case: (eqVneq x y) => // xny _ _ jxjy.
have [] := @sepf [set y] x (cl1 y); first exact/eqP.
move=> i P; suff : join_product x i != join_product y i by rewrite jxjy => /eqP.
apply/negP; move: P; apply: contra_not => /eqP; rewrite /join_product => ->.
by apply: subset_closure; exists y.
Qed.

Lemma join_product_weak : set_inj [set: T] join_product ->
  @open T = @open (weak_topology join_product).
Proof.
move=> inj; rewrite predeqE => U; split; first last.
  by move=> [V ? <-]; apply: open_comp => // + _; exact: join_product_continuous.
move=> /join_product_open/open_subspaceP [V [oU VU]].
exists V => //; have := @f_equal _ _ (preimage join_product) _ _ VU.
rewrite !preimage_setI // !preimage_range !setIT => ->.
rewrite eqEsubset; split; last exact: preimage_image.
by move=> z [w Uw] /inj <- //; rewrite inE.
Qed.

End product_embeddings.

Global Instance prod_topology_filter (U : Type) (T : U -> ptopologicalType) (f : prod_topology T) :
  ProperFilter (nbhs f).
Proof.
exact: nbhs_pfilter.
Qed.

End product_spaces.

HB.instance Definition _ (U : Type) (T : U -> ptopologicalType) :=
  Pointed.copy (forall x : U, T x) (prod_topology T).

(**md the uniform topologies type *)
Section fct_Uniform.
Local Open Scope relation_scope.
Variables (T : choiceType) (U : uniformType).

Definition fct_ent := filter_from (@entourage U)
  (fun P => [set fg | forall t : T, P (fg.1 t, fg.2 t)]).

Lemma fct_ent_filter : Filter fct_ent.
Proof.
apply: filter_from_filter; first by exists setT; apply: filterT.
move=> A B entA entB.
exists (A `&` B); first exact: filterI.
by move=> fg ABfg; split=> t; have [] := ABfg t.
Qed.

Lemma fct_ent_refl A : fct_ent A -> diagonal `<=` A.
Proof.
move=> [B entB sBA] fg feg; apply/sBA => t; rewrite feg.
exact: entourage_refl.
Qed.

Lemma fct_ent_inv A : fct_ent A -> fct_ent A^-1.
Proof.
move=> [B entB sBA]; exists B^-1; first exact: entourage_inv.
by move=> fg Bgf; exact/sBA.
Qed.

Lemma fct_ent_split A : fct_ent A -> exists2 B, fct_ent B & B \; B `<=` A.
Proof.
move=> [B entB sBA].
exists [set fg | forall t, split_ent B (fg.1 t, fg.2 t)].
  by exists (split_ent B).
move=> fg [h spBfh spBhg].
by apply: sBA => t; apply: entourage_split (spBfh t) (spBhg t).
Qed.

Definition arrow_uniform_type : Type := T -> U.

#[export] HB.instance Definition _ := Choice.on arrow_uniform_type.
#[export] HB.instance Definition _ := isUniform.Build arrow_uniform_type
  fct_ent_filter fct_ent_refl fct_ent_inv fct_ent_split.

End fct_Uniform.

#[export] HB.instance Definition _ {T : choiceType} {U : puniformType} :=
  Pointed.on (arrow_uniform_type T U).

Lemma cvg_fct_entourageP (T : choiceType) (U : uniformType)
    (F : set_system (arrow_uniform_type T U)) (FF : Filter F)
    (f : arrow_uniform_type T U) :
  F --> f <-> forall A, entourage A ->
              \forall g \near F, forall t, A (f t, g t).
Proof.
split => [/cvg_entourageP Ff A entA|Ff].
  by apply: (Ff [set fg | forall t : T, A (fg.1 t, fg.2 t)]); exists A.
apply/cvg_entourageP => A [P entP sPA].
by near=> g do apply: sPA; apply: Ff.
Unshelve. all: by end_near. Qed.

Section fun_Complete.
Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set_system (arrow_uniform_type T U))
  {FF :  ProperFilter F} : cauchy F -> cvg F.
Proof.
move=> Fc.
have /(_ _) /cauchy_cvg /cvg_app_entourageP cvF : cauchy (@^~_ @ F).
  move=> t A /= entA; rewrite near_simpl -near2E near_map2.
  by apply: Fc; exists A.
apply/cvg_ex; exists (fun t => lim (@^~t @ F)).
apply/cvg_fct_entourageP => A entA; near=> f => t; near F => g.
apply: (entourage_split (g t)) => //; first by near: g; apply: cvF.
move: (t); near: g; near: f; apply: nearP_dep; apply: Fc.
by exists (split_ent A)^-1%relation => /=.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Uniform_isComplete.Build
  (arrow_uniform_type T U) fun_complete.

HB.instance Definition _ (R : numFieldType) :=
  Uniform_isComplete.Build (arrow_uniform_type T U) cauchy_cvg.

End fun_Complete.

(** Functional metric spaces *)
Section fct_PseudoMetric.
Variable (T : choiceType) (R : numFieldType) (U : pseudoMetricType R).
Definition fct_ball (x : arrow_uniform_type T U) (eps : R)
  (y : arrow_uniform_type T U) := forall t : T, ball (x t) eps (y t).
Lemma fct_ball_center (x : T -> U) (e : R) : 0 < e -> fct_ball x e x.
Proof. by move=> /posnumP[{}e] ?. Qed.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Proof. by move=> P t; apply: ball_sym. Qed.
Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof. by move=> xy yz t; apply: (@ball_triangle _ _ (y t)). Qed.
Lemma fct_entourage : entourage = entourage_ fct_ball.
Proof.
rewrite predeqE => A; split; last first.
  by move=> [_/posnumP[e] sbeA]; exists [set xy | ball xy.1 e%:num xy.2].
move=> [P]; rewrite -entourage_ballE => -[_/posnumP[e] sbeP] sPA.
by exists e%:num => //= fg fg_e; apply: sPA => t; apply: sbeP; apply: fg_e.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R
  (arrow_uniform_type T U) fct_ball_center fct_ball_sym
  fct_ball_triangle fct_entourage.
End fct_PseudoMetric.

Module ArrowAsUniformType.
HB.instance Definition _ (U : choiceType) (V : uniformType) :=
  Uniform.copy (U -> V) (arrow_uniform_type U V).

HB.instance Definition _ (U : choiceType) (R : numFieldType)
    (V : pseudoMetricType R) :=
  PseudoMetric.copy (U -> V) (arrow_uniform_type U V).

HB.instance Definition _ (U : topologicalType) (T : uniformType) :=
  Uniform.copy 
    (continuousType U T) 
    (weak_topology (id : continuousType U T -> (U -> T))).

HB.instance Definition _ (U : topologicalType) (R : realType) 
     (T : pseudoMetricType R) :=
  PseudoMetric.on 
    (weak_topology (id : continuousType U T -> (U -> T))).

End ArrowAsUniformType.

(** Limit switching *)
Section Cvg_switch.
Context {T1 T2 : choiceType}.
Local Import ArrowAsUniformType.

Lemma cvg_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/cvg_app_entourageP => A entA.
near F1 => x1; near=> x2; apply: (entourage_split (h x1)) => //.
  by apply/xsectionP; near: x1; exact: hl.
apply: (entourage_split (f x1 x2)) => //.
  by apply/xsectionP; near: x2; exact: fh.
move: (x2); near: x1; have /cvg_fct_entourageP /(_ _^-1%relation):= fg; apply.
exact: entourage_inv.
Unshelve. all: by end_near. Qed.

Lemma cvg_switch_2 {U : completeType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : ProperFilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Proof.
move=> fg fh; apply: cauchy_cvg => A entA.
rewrite !near_simpl -near2_pair near_map2; near=> x1 y1 => /=; near F2 => x2.
apply: (entourage_split (f x1 x2)) => //.
  by apply/xsectionP; near: x2; exact: fh.
apply: (entourage_split (f y1 x2)) => //; last first.
  apply/xsectionP; near: x2; apply/(fh _ (xsection _^-1%relation _)).
  exact: nbhs_entourage (entourage_inv _).
apply: (entourage_split (g x2)) => //; move: (x2); [near: x1|near: y1].
  have /cvg_fct_entourageP /(_ _^-1%relation) := fg; apply.
  exact: entourage_inv.
by have /cvg_fct_entourageP := fg; apply.
Unshelve. all: by end_near. Qed.

Lemma cvg_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
move=> Hfg Hfh; have hcv := !! cvg_switch_2 Hfg Hfh.
by exists (lim (h @ F1)); split=> //; apply: cvg_switch_1 Hfg Hfh hcv.
Qed.

End Cvg_switch.

Definition uniform_fun {U : Type} (A : set U) (V : Type) : Type := U -> V.

Notation "{ 'uniform`' A -> V }" := (@uniform_fun _ A V) : type_scope.
Notation "{ 'uniform' U -> V }" := ({uniform` [set: U] -> V}) : type_scope.
Notation "{ 'uniform' A , F --> f }" :=
  (cvg_to F (nbhs (f : {uniform` A -> _}))) : classical_set_scope.
Notation "{ 'uniform' , F --> f }" :=
  (cvg_to F (nbhs (f : {uniform _ -> _}))) : classical_set_scope.

Definition sigL_arrow {U : choiceType} (A : set U) (V : uniformType) :
  (U -> V) -> arrow_uniform_type A V := @sigL _ V A.

HB.instance Definition _ (U : choiceType) (A : set U) (V : uniformType) :=
  Uniform.copy {uniform` A -> V} (weak_topology (@sigL_arrow _ A V)).

Section RestrictedUniformTopology.
Context {U : choiceType} (A : set U) {V : uniformType} .

Lemma uniform_nbhs (f : {uniform` A -> V}) P:
  nbhs f P <-> (exists E, entourage E /\
    [set h | forall y, A y -> E(f y, h y)] `<=` P).
Proof.
split=> [[Q [[/= W oW <- /=] Wf subP]]|[E [entE subP]]].
  rewrite openE /= /interior in oW.
  case: (oW _ Wf) => ? [ /= E entE] Esub subW.
  exists E; split=> // h Eh; apply/subP/subW/xsectionP/Esub => /= [[u Au]].
  by apply: Eh => /=; rewrite -inE.
case : (pselect (exists (u : U), True)); first last.
  move=> nU; apply: (filterS subP); apply: (@filterS _ _ _ setT).
  by move=> t _ /= y; move: nU; apply: absurd; exists y.
  exact: filterT.
case=> u0 _; near=> g; apply: subP => y /mem_set Ay; rewrite -!(sigLE A).
move: (SigSub _); near: g.
have := (@cvg_image _ _ (@sigL_arrow _ A V) _ f (nbhs_filter f)
  (image_sigL (f u0))).1 cvg_id [set h | forall y, E (sigL A f y, h y)].
case.
  exists [set fg | forall y, E (fg.1 y, fg.2 y)] => //; first by exists E.
  by move=> g /xsectionP.
move=> B nbhsB rBrE; apply: (filterS _ nbhsB) => g Bg [y yA].
by move: rBrE; rewrite eqEsubset; case => [+ _]; apply; exists g.
Unshelve. all: by end_near. Qed.

Lemma uniform_entourage :
  @entourage [the uniformType of {uniform` A -> V}] =
  filter_from
    (@entourage V)
    (fun P => [set fg | forall t : U, A t -> P (fg.1 t, fg.2 t)]).
Proof.
rewrite eqEsubset; split => P /=.
  case=> /= E [F entF FsubE EsubP]; exists F => //; case=> f g Ffg.
  by apply/EsubP/FsubE=> [[x p]] /=; apply: Ffg; move/set_mem: (p).
case=> E entE EsubP; exists [set fg | forall t, E (fg.1 t, fg.2 t)].
  by exists E.
case=> f g Efg; apply: EsubP => t /mem_set At.
by move: Efg => /= /(_ (@exist _ (fun x => in_mem x (mem A)) _ At)).
Qed.

End RestrictedUniformTopology.

Lemma restricted_cvgE {U : choiceType} {V : uniformType}
    (F : set_system (U -> V)) A (f : U -> V) :
  {uniform A, F --> f} = (F --> (f : {uniform` A -> V})).
Proof. by []. Qed.

Lemma pointwise_cvgE {U : Type} {V : topologicalType}
    (F : set_system (U -> V)) (A : set U) (f : U -> V) :
  {ptws, F --> f} = (F --> (f : {ptws U -> V})).
Proof. by []. Qed.


(**md We use this function to help Coq identify the correct notation to use
  when printing. Otherwise you get goals like `F --> f -> F --> f`. *)
Definition uniform_fun_family {U} V (fam : set U -> Prop) := U -> V.

Notation "{ 'family' fam , U -> V }" :=  (@uniform_fun_family U V fam).
Notation "{ 'family' fam , F --> f }" :=
  (cvg_to F (@nbhs _ {family fam, _ -> _} f)) : type_scope.

HB.instance Definition _ {U : choiceType} {V : uniformType}
    (fam : set U -> Prop) :=
  Uniform.copy {family fam, U -> V} (sup_topology (fun k : sigT fam =>
       Uniform.class [the uniformType of {uniform` projT1 k -> V}])).

Section UniformCvgLemmas.
Context {U : choiceType} {V : uniformType}.

Lemma uniform_set1 F (f : U -> V) (x : U) :
  Filter F -> {uniform [set x], F --> f} = (g x @[g --> F] --> f x).
Proof.
move=> FF; rewrite propeqE; split.
  move=> + W => /(_ [set t | W (t x)]) +; rewrite -nbhs_entourageE.
  rewrite uniform_nbhs => + [Q entQ subW].
  by apply; exists Q; split => // h Qf; exact/subW/xsectionP/Qf.
move=> Ff W; rewrite uniform_nbhs => [[E] [entE subW]].
apply: (filterS subW); move/(nbhs_entourage (f x))/Ff: entE => //=; near_simpl.
by apply: filter_app; apply: nearW=> ? /xsectionP ? ? ->.
Qed.

Lemma uniform_subset_nbhs (f : U -> V) (A B : set U) :
  B `<=` A -> nbhs (f : {uniform` A -> V}) `=>` nbhs (f : {uniform` B -> V}).
Proof.
move => BsubA P /uniform_nbhs [E [entE EsubP]].
apply: (filterS EsubP); apply/uniform_nbhs; exists E; split => //.
by move=> h Eh y /BsubA Ay; exact: Eh.
Qed.

Lemma uniform_subset_cvg (f : U -> V) (A B : set U) F :
  Filter F -> B `<=` A -> {uniform A, F --> f} -> {uniform B, F --> f}.
Proof.
move => FF /uniform_subset_nbhs => /(_ f).
by move=> nbhsF Acvg; apply: cvg_trans; [exact: Acvg|exact: nbhsF].
Qed.

Lemma pointwise_uniform_cvg  (f : U -> V) (F : set_system (U -> V)) :
  Filter F -> {uniform, F --> f} -> {ptws, F --> f}.
Proof.
move=> FF; rewrite cvg_sup => + i; have isubT : [set i] `<=` setT by move=> ?.
move=> /(uniform_subset_cvg _ isubT); rewrite uniform_set1.
rewrite cvg_image; last by rewrite eqEsubset; split=> v // _; exists (cst v).
apply: cvg_trans => W /=; rewrite nbhs_simpl; exists (@^~ i @^-1` W) => //.
by rewrite image_preimage // eqEsubset; split=> // j _; exists (fun _ => j).
Qed.

Lemma cvg_sigL (A : set U) (f : U -> V) (F : set_system (U -> V)) :
    Filter F ->
  {uniform A, F --> f} <->
  {uniform, sigL A @ F --> sigL A f}.
Proof.
move=> FF; split.
- move=> cvgF P' /uniform_nbhs [E [entE EsubP]].
  apply: (filterS EsubP); apply: cvgF => /=.
  apply: (filterS (P := [set h | forall y, A y -> E (f y, h y)])).
    + by move=> h/= Eh [y ?] _; apply Eh; rewrite -inE.
    + by (apply/uniform_nbhs; eexists; split; eauto).
- move=> cvgF P' /= /uniform_nbhs [ E [/= entE EsubP]].
  apply: (filterS EsubP).
  move: (cvgF  [set h | (forall y , E (sigL A f y, h y))]) => /=.
  set Q := (x in (_ -> x) -> _); move=> W.
  have: Q by apply W, uniform_nbhs; exists E; split => // h + ?; apply.
  rewrite {}/W {}/Q; near_simpl => /= R; apply: (filterS _ R) => h /=.
  by rewrite forall_sig /sigL /=.
Qed.

Lemma eq_in_close (A : set U) (f g : {uniform` A -> V}) :
  {in A, f =1 g} -> close f g.
Proof.
rewrite entourage_close => /eq_sigLP eqfg ? [E entE]; apply=> /=.
by rewrite /map_pair/sigL_arrow eqfg; exact: entourage_refl.
Qed.

Lemma hausdorrf_close_eq_in (A : set U) (f g : {uniform` A -> V}) :
  hausdorff_space V -> close f g = {in A, f =1 g}.
Proof.
move=> hV.
rewrite propeqE; split; last exact: eq_in_close.
rewrite entourage_close => C u; rewrite inE => uA; apply: hV.
rewrite /cluster -nbhs_entourageE /= => X Y [X' eX X'X] [Y' eY Y'Y].
exists (g u); split; [apply: X'X| apply: Y'Y]; apply/xsectionP; last first.
  exact: entourage_refl.
apply: (C [set fg | forall y, A y -> X' (fg.1 y, fg.2 y)]) => //=.
by rewrite uniform_entourage; exists X'.
Qed.

Lemma uniform_nbhsT (f : U -> V) :
  (nbhs (f : {uniform U -> V})) = nbhs (f : arrow_uniform_type U V).
Proof.
rewrite eqEsubset; split=> A.
  case/uniform_nbhs => E [entE] /filterS; apply.
  exists [set fh | forall y, E (fh.1 y, fh.2 y)]; first by exists E.
  by move=> ? /xsectionP /=.
case => J [E entE EJ] /filterS; apply; apply/uniform_nbhs; exists E.
by split => // z /= Efz; apply/xsectionP/EJ => t /=; exact: Efz.
Qed.

Lemma cvg_uniformU (f : U -> V) (F : set_system (U -> V)) A B : Filter F ->
  {uniform A, F --> f} -> {uniform B, F --> f} ->
  {uniform (A `|` B), F --> f}.
Proof.
move=> FF AFf BFf Q /=/uniform_nbhs [E [entE EsubQ]].
apply: (filterS EsubQ).
rewrite (_:  [set h | (forall y : U, (A `|` B) y -> E (f y, h y))] =
    [set h | forall y, A y -> E (f y, h y)] `&`
    [set h | forall y, B y -> E (f y, h y)]).
- apply: filterI; [apply: AFf| apply: BFf].
  + by apply/uniform_nbhs; exists E; split.
  + by apply/uniform_nbhs; exists E; split.
- rewrite eqEsubset; split=> h.
  + by move=> R; split=> t ?; apply: R;[left| right].
  + by move=> [R1 R2] y [? | ?]; [apply: R1| apply: R2].
Qed.

Lemma cvg_uniform_set0 (F : set_system (U -> V)) (f : U -> V) : Filter F ->
  {uniform set0, F --> f}.
Proof.
move=> FF P /= /uniform_nbhs [E [? R]].
suff -> : P = setT by exact: filterT.
rewrite eqEsubset; split => //=.
by apply: subset_trans R => g _ ?.
Qed.

Lemma fam_cvgP (fam : set U -> Prop) (F : set_system (U -> V)) (f : U -> V) :
  Filter F -> {family fam, F --> f} <->
  (forall A : set U, fam A -> {uniform A, F --> f }).
Proof.
split; first by move=> /cvg_sup + A FA; move/(_ (existT _ _ FA)).
by move=> famFf /=; apply/cvg_sup => [[? ?] FA]; apply: famFf.
Qed.

Lemma family_cvg_subset (famA famB : set U -> Prop) (F : set_system (U -> V))
    (f : U -> V) : Filter F ->
  famA `<=` famB -> {family famB, F --> f} -> {family famA, F --> f}.
Proof.
by move=> FF S /fam_cvgP famBFf; apply/fam_cvgP => A ?; apply/famBFf/S.
Qed.

Lemma family_cvg_finite_covers (famA famB : set U -> Prop)
  (F : set_system (U -> V)) (f : U -> V) : Filter F ->
  (forall P, famA P ->
    exists (I : choiceType) f,
      (forall i, famB (f i)) /\ finite_subset_cover [set: I] f P) ->
  {family famB, F --> f} -> {family famA, F --> f}.
Proof.
move=> FF ex_finCover /fam_cvgP rFf; apply/fam_cvgP => A famAA.
move: ex_finCover => /(_ _ famAA) [R [g [g_famB [D _]]]].
move/uniform_subset_cvg; apply.
elim/finSet_rect: D => X IHX.
have [->|/set0P[x xX]] := eqVneq [set` X] set0.
  by rewrite coverE bigcup_set0; apply: cvg_uniform_set0.
rewrite coverE (bigcup_fsetD1 x)//; apply: cvg_uniformU.
  exact/rFf/g_famB.
exact/IHX/fproperD1.
Qed.

End UniformCvgLemmas.

Lemma uniform_restrict_cvg {U : choiceType} {V : puniformType}
    (F : set_system (U -> V)) (f : U -> V) A : Filter F ->
  {uniform A, F --> f} <-> {uniform, restrict A @ F --> restrict A f}.
Proof.
move=> FF; rewrite cvg_sigL; split.
- rewrite -sigLK; move/(cvg_app valL) => D.
  apply: cvg_trans; first exact: D.
  move=> P /uniform_nbhs [E [/=entE EsubP]]; apply: (filterS EsubP).
  apply/uniform_nbhs; exists E; split=> //= h /=.
  rewrite /sigL => R u _; rewrite oinv_set_val.
  by case: insubP=> /= *; [apply: R|apply: entourage_refl].
- move/(@cvg_app _ _ _ _ (sigL A)).
  rewrite -fmap_comp sigL_restrict => D.
  apply: cvg_trans; first exact: D.
  move=> P /uniform_nbhs [E [/=entE EsubP]]; apply: (filterS EsubP).
  apply/uniform_nbhs; exists E; split=> //= h /=.
  rewrite /sigL => R [u Au] _ /=.
  by have := R u I; rewrite /patch Au.
Qed.


Section FamilyConvergence.

Lemma fam_cvgE {U : choiceType} {V : uniformType} (F : set_system (U -> V))
    (f : U -> V) fam :
  {family fam, F --> f} = (F --> (f : {family fam, U -> V})).
Proof. by []. Qed.

Lemma fam_nbhs {U : choiceType} {V : uniformType} (fam : set U -> Prop)
    (A : set U) (E : set (V * V)) (f : {family fam, U -> V}) :
  entourage E -> fam A -> nbhs f [set g | forall y, A y -> E (f y, g y)].
Proof.
move=> entE famA; have /fam_cvgP /(_ A) : (nbhs f --> f) by []; apply => //.
by apply uniform_nbhs; exists E; split.
Qed.

Lemma fam_compact_nbhs {U : topologicalType} {V : uniformType}
    (A : set U) (O : set V) (f : {family compact, U -> V}) :
  open O -> f @` A `<=` O -> compact A -> continuous f ->
  nbhs (f : {family compact, U -> V}) [set g | forall y, A y -> O (g y)].
Proof.
move=> oO fAO /[dup] cA /compact_near_coveringP/near_covering_withinP cfA ctsf.
near=> z => /=; (suff: A `<=` [set y | O (z y)] by exact); near: z.
apply: cfA => x Ax; have : O (f x) by exact: fAO.
move: (oO); rewrite openE /= => /[apply] /[dup] /ctsf Ofx /=.
rewrite /interior -nbhs_entourageE => -[E entE EfO].
exists (f @^-1` xsection (split_ent E) (f x),
    [set g | forall w, A w -> split_ent E (f w, g w)]).
  split => //=; last exact: fam_nbhs.
  by apply: ctsf; rewrite /= -nbhs_entourageE; exists (split_ent E).
case=> y g [/= /xsectionP Efxy] AEg Ay; apply/EfO/xsectionP.
by apply: subset_split_ent => //; exists (f y) => //=; exact: AEg.
Unshelve. all: by end_near. Qed.

End FamilyConvergence.

(**md It turns out `{family compact, U -> V}` can be generalized to only assume
  `topologicalType` on `V`. This topology is called the compact-open topology.
   This topology is special because it is the _only_ topology that will allow
   `curry`/`uncurry` to be continuous. *)
Section compact_open.
Context {T U : topologicalType}.

Definition compact_open : Type := T -> U.

Section compact_open_setwise.
Context {K : set T}.

Definition compact_openK := let _ := K in compact_open.

Definition compact_openK_nbhs (f : compact_openK) :=
  filter_from
    [set O | f @` K `<=` O /\ open O]
    (fun O => [set g | g @` K `<=` O]).

Global Instance compact_openK_nbhs_filter (f : compact_openK) :
  ProperFilter (compact_openK_nbhs f).
Proof.
split; first by case=> g [gKO oO] /(_ f); apply.
apply: filter_from_filter; first by exists setT; split => //; exact: openT.
move=> P Q [fKP oP] [fKQ oQ]; exists (P `&` Q); first split.
- by move=> ? [z Kz M-]; split; [apply: fKP | apply: fKQ]; exists z.
- exact: openI.
by move=> g /= gPQ; split; exact: (subset_trans gPQ).
Qed.

HB.instance Definition _ := Choice.on compact_openK.

HB.instance Definition _ := hasNbhs.Build compact_openK compact_openK_nbhs.

Definition compact_open_of_nbhs := [set A : set compact_openK | A `<=` nbhs^~ A].

Lemma compact_openK_nbhsE_subproof (p : compact_openK) :
  compact_openK_nbhs p =
    [set A | exists B : set compact_openK,
      [/\ compact_open_of_nbhs B, B p & B `<=` A]].
Proof.
rewrite eqEsubset; split => A /=.
  case=> B /= [fKB oB gKBA]; exists [set g | g @` K `<=` B]; split => //.
  by move=> h /= hKB; exists B.
by case=> B [oB Bf /filterS]; apply; exact: oB.
Qed.

Lemma compact_openK_openE_subproof :
  compact_open_of_nbhs = [set A | A `<=` compact_openK_nbhs^~ A].
Proof. by []. Qed.

HB.instance Definition _ :=
  Nbhs_isTopological.Build compact_openK compact_openK_nbhs_filter
  compact_openK_nbhsE_subproof compact_openK_openE_subproof.

End compact_open_setwise.

Definition compact_open_def :=
  sup_topology (fun i : sigT (@compact T) =>
    Topological.class (@compact_openK (projT1 i))).

HB.instance Definition _ := Nbhs.copy compact_open compact_open_def.

HB.instance Definition _ : Nbhs_isTopological compact_open :=
  Topological.copy compact_open compact_open_def.

Lemma compact_open_cvgP (F : set_system compact_open)
    (f : compact_open) :
  Filter F ->
  F --> f <-> forall K O, @compact T K -> @open U O -> f @` K `<=` O ->
    F [set g | g @` K `<=` O].
Proof.
move=> FF; split.
  by move/cvg_sup => + K O cptK ? ? => /(_ (existT _ _ cptK)); apply; exists O.
move=> fko; apply/cvg_sup => -[A cptK] O /= [C /= [fAC oC]].
by move/filterS; apply; exact: fko.
Qed.

Lemma compact_open_open (K : set T) (O : set U) :
  compact K -> open O -> open ([set g | g @` K `<=` O] : set compact_open).
Proof.
pose C := [set g | g @` K `<=` O]; move=> cptK oO.
exists [set C]; last by rewrite bigcup_set1.
move=> _ ->; exists (fset1 C) => //; last by rewrite set_fset1 bigcap_set1.
by move=> _ /[!inE] ->; exists (existT _ _ cptK) => // z Cz; exists O.
Qed.

End compact_open.

HB.instance Definition _ {U : topologicalType} {V : ptopologicalType} K := 
    Pointed.on (@compact_openK U V K).

HB.instance Definition _ {U : topologicalType} {V : ptopologicalType} := 
  Pointed.on (@compact_open U V).


Notation "{ 'compact-open' , U -> V }" := (@compact_open U V).
Notation "{ 'compact-open' , F --> f }" :=
  (F --> (f : @compact_open _ _)).

Section compact_open_uniform.
Context {U : topologicalType} {V : puniformType}.

Let small_ent_sub := @small_set_sub _ (@entourage V).

Lemma compact_open_fam_compactP (f : U -> V) (F : set_system (U -> V)) :
  continuous f -> Filter F ->
  {compact-open, F --> f} <-> {family compact, F --> f}.
Proof.
move=> ctsf FF; split; first last.
  move=> cptF; apply/compact_open_cvgP => K O cptK oO fKO.
  apply: cptF; have := fam_compact_nbhs oO fKO cptK ctsf; apply: filter_app.
  by near=> g => /=  gKO ? [z Kx <-]; exact: gKO.
move/compact_open_cvgP=> cptOF; apply/cvg_sup => -[K cptK R].
case=> D [[E oE <-] Ekf] /filterS; apply.
move: oE; rewrite openE => /(_ _ Ekf); case => A [J entJ] EKR KfE.
near=> z; apply/KfE/xsectionP/EKR => -[u Kp]; rewrite /sigL_arrow /= /set_val /= /eqincl.
(have Ku : K u by rewrite inE in Kp); move: u Ku {D Kp}; near: z.
move/compact_near_coveringP/near_covering_withinP : (cptK); apply.
move=> u Ku; near (powerset_filter_from (@entourage V)) => E'.
have entE' : entourage E' by exact: (near (near_small_set _)).
pose C := f @^-1` xsection E' (f u).
pose B := \bigcup_(z in K `&` closure C) interior (xsection E' (f z)).
have oB : open B by apply: bigcup_open => ? ?; exact: open_interior.
have fKB : f @` (K `&` closure C) `<=` B.
  move=> _ [z KCz <-]; exists z => //; rewrite /interior.
  by rewrite -nbhs_entourageE; exists E'.
have cptKC : compact (K `&` closure C).
  by apply: compact_closedI => //; exact: closed_closure.
have := cptOF (K `&` closure C) B cptKC oB fKB.
exists (C, [set g | [set g x | x in K `&` closure C] `<=` B]).
  split; last exact: cptOF.
  by apply: (ctsf) => //; rewrite /filter_of -nbhs_entourageE; exists E'.
case=> z h /= [Cz KB Kz].
case: (KB (h z)); first by exists z; split => //; exact: subset_closure.
move=> w [Kw Cw /interior_subset Jfwhz]; apply: subset_split_ent => //.
exists (f w); last first.
  apply: (near (small_ent_sub _) E') => //.
  exact/xsectionP.
apply: subset_split_ent => //; exists (f u).
  apply/entourage_sym; apply: (near (small_ent_sub _) E') => //.
  exact/xsectionP.
have [] := Cw (f @^-1` xsection E' (f w)).
  by apply: ctsf; rewrite /= -nbhs_entourageE; exists E'.
move=> r [Cr /= Ewr]; apply: subset_split_ent => //; exists (f r).
  apply: (near (small_ent_sub _) E') => //.
  exact/xsectionP.
apply/entourage_sym; apply: (near (small_ent_sub _) E') => //.
exact/xsectionP.
Unshelve. all: by end_near. Qed.

End compact_open_uniform.

Module ArrowAsCompactOpen.
HB.instance Definition _ (U : topologicalType) (V : topologicalType) :=
  Topological.copy (U -> V) {compact-open, U -> V}.

HB.instance Definition _ (U : topologicalType) (V : topologicalType) :=
  Topological.copy (continuousType U V) 
    (weak_topology (id : (continuousType U V) -> (U -> V)) ).
End ArrowAsCompactOpen.

Definition compactly_in {U : topologicalType} (A : set U) :=
  [set B | B `<=` A /\ compact B].

Lemma compact_cvg_within_compact {U : topologicalType} {V : uniformType}
    (C : set U) (F : set_system (U -> V)) (f : U -> V) :
  Filter F -> compact C ->
  {uniform C, F --> f} <-> {family compactly_in C, F --> f}.
Proof.
move=> FF CC.
apply: (iff_trans _ (iff_sym (fam_cvgP _ _ FF))); split.
- by move=> CFf D [/uniform_subset_cvg + _]; apply.
- by apply; split.
Qed.

Section UniformContinuousLimits.

Lemma uniform_limit_continuous {U : topologicalType} {V : uniformType}
    (F : set_system (U -> V)) (f : U -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : U -> V)) ->
  {uniform, F --> f} -> continuous f.
Proof.
move=> PF ctsF Ff x; apply/cvg_app_entourageP => A entA; near F => g; near=> y.
apply: (entourage_split (g x)) => //.
  by near: g; apply/Ff/uniform_nbhs; exists (split_ent A); split => // ?; exact.
apply: (entourage_split (g y)) => //; near: y; near: g.
  by apply: (filterS _ ctsF) => g /(_ x) /cvg_app_entourageP; exact.
apply/Ff/uniform_nbhs; exists (split_ent (split_ent A))^-1%relation.
by split; [exact: entourage_inv | move=> g fg; near_simpl; near=> z; exact: fg].
Unshelve. all: end_near. Qed.

Lemma uniform_limit_continuous_subspace {U : topologicalType} {V : puniformType}
    (K : set U) (F : set_system (U -> V)) (f : subspace K -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : subspace K -> V)) ->
  {uniform K, F --> f} -> {within K, continuous f}.
Proof.
move=> PF ctsF Ff; apply: (@subspace_eq_continuous _ _ _ (restrict K f)).
  by rewrite /restrict => ? ->.
apply: (@uniform_limit_continuous (subspace K) _ (restrict K @ F) _).
  apply: (filterS _ ctsF) => g; apply: subspace_eq_continuous.
  by rewrite /restrict => ? ->.
by apply (@uniform_restrict_cvg _ _ F ) => //; exact: PF.
Qed.

End UniformContinuousLimits.

Section UniformPointwise.
Context {U : topologicalType} {V : uniformType}.

Definition singletons {T : Type} := [set [set x] | x in [set: T]].

Lemma pointwise_cvg_family_singleton F (f: U -> V):
  Filter F -> {ptws, F --> f} = {family @singletons U, F --> f}.
Proof.
move=> FF; apply/propext.
rewrite (@fam_cvgP _ _ singletons). (* BUG: slowdown if no arguments *)
rewrite cvg_sup; split.
  move=> + A [x _ <-] => /(_ x); rewrite uniform_set1.
  rewrite cvg_image; last by rewrite eqEsubset; split=> v // _; exists (cst v).
  apply: cvg_trans => W /=; rewrite ?nbhs_simpl /fmap /= => [[W' + <-]].
  by apply: filterS => g W'g /=; exists g.
move=> + i; have /[swap] /[apply] : singletons [set i] by exists i.
rewrite uniform_set1.
rewrite cvg_image; last by rewrite eqEsubset; split=> v // _; exists (cst v).
move=> + W //=; rewrite ?nbhs_simpl => Q => /Q Q'; exists (@^~ i @^-1` W) => //.
by rewrite eqEsubset; split => [j [? + <-//]|j Wj]; exists (fun _ => j).
Qed.

Lemma pointwise_cvg_compact_family F (f : U -> V) :
  Filter F -> {family compact, F --> f} -> {ptws, F --> f}.
Proof.
move=> PF; rewrite pointwise_cvg_family_singleton; apply: family_cvg_subset.
by move=> A [x _ <-]; exact: compact_set1.
Qed.

Lemma pointwise_cvgP F (f: U -> V):
  Filter F -> {ptws, F --> f} <-> forall (t : U), (fun g => g t) @ F --> f t.
Proof.
move=> Ff; rewrite pointwise_cvg_family_singleton; split.
  move/fam_cvgP => + t A At => /(_ [set t]); rewrite uniform_set1; apply => //.
  by exists t.
by move=> pf; apply/fam_cvgP => ? [t _ <-]; rewrite uniform_set1; exact: pf.
Qed.

End UniformPointwise.

Section ArzelaAscoli.
Context {X : topologicalType} {Y : puniformType} {hsdf : hausdorff_space Y}.
Implicit Types (I : Type).

(** The key condition in Arzela-Ascoli that, like uniform continuity, moves a
    quantifier around so all functions have the same "deltas": *)
Definition equicontinuous {I} (W : set I) (d : I -> (X -> Y)) :=
  forall x (E : set (Y * Y)), entourage E ->
    \forall y \near x, forall i, W i -> E (d i x, d i y).

Lemma equicontinuous_subset {I J} (W : set I) (V : set J)
    {fW : I -> X -> Y} {fV : J -> X -> Y} :
  fW @`W `<=` fV @` V -> equicontinuous V fV -> equicontinuous W fW.
Proof.
move=> WsubV + x E entE => /(_ x E entE); apply: filterS => y VE i Wi.
by case: (WsubV (fW i)); [exists i | move=> j Vj <-; exact: VE].
Qed.

Lemma equicontinuous_subset_id (W V : set (X -> Y)) :
  W `<=` V -> equicontinuous V id -> equicontinuous W id.
Proof.
move=> WsubV; apply: equicontinuous_subset => ? [y ? <- /=]; exists y => //.
exact: WsubV.
Qed.

Lemma equicontinuous_continuous_for {I} (W : set I) (fW : I -> X -> Y) i x :
  {for x, equicontinuous W fW} -> W i -> {for x, continuous (fW i)}.
Proof.
move=> ectsW Wf; apply/cvg_entourageP => E entE; near_simpl.
by near=> y; apply: (near (ectsW _ entE) y).
Unshelve. end_near. Qed.

Lemma equicontinuous_continuous {I} (W : set I) (fW : I -> (X -> Y)) (i : I) :
  equicontinuous W fW -> W i -> continuous (fW i).
Proof.
move=> ectsW Wf x; apply: equicontinuous_continuous_for; last exact: Wf.
by move=> ?; exact: ectsW.
Qed.

(**md A convenient notion that is in between compactness in
   `{family compact, X -> y}` and compactness in `{ptws X -> y}`: *)
Definition pointwise_precompact {I} (W : set I) (d : I -> X -> Y) :=
  forall x, precompact [set d i x | i in W].

Lemma pointwise_precompact_subset {I J} (W : set I) (V : set J)
    {fW : I -> X -> Y} {fV : J -> X -> Y} :
  fW @` W `<=` fV @` V -> pointwise_precompact V fV ->
  pointwise_precompact W fW.
Proof.
move=> WsubV + x => /(_ x) pcptV; apply: precompact_subset pcptV => y [i Wi <-].
by case: (WsubV (fW i)); [exists i | move=> j Vj <-; exists j].
Qed.

Lemma pointwise_precompact_precompact {I} (W : set I) (fW : I -> (X -> Y)) :
  pointwise_precompact W fW -> precompact ((fW @` W) : set {ptws X -> Y}).
Proof.
rewrite precompactE => ptwsPreW.
pose K := fun x => closure [set fW i x | i in W].
set R := [set f : {ptws X -> Y} | forall x : X, K x (f x)].
have C : compact R.
  by apply: tychonoff => x; rewrite -precompactE; move: ptwsPreW; exact.
apply: (subclosed_compact _ C); first exact: closed_closure.
have WsubR : (fW @` W) `<=` R.
  move=> f Wf x; rewrite /R /K closure_limit_point; left.
  by case: Wf => i ? <-; exists i.
rewrite closureE; apply: smallest_sub (compact_closed _ C) WsubR.
exact: hausdorff_product.
Qed.

Lemma uniform_pointwise_compact (W : set (X -> Y)) :
  compact (W : set (@uniform_fun_family X Y compact)) ->
  compact (W : set {ptws X -> Y}).
Proof.
rewrite [x in x _ -> _]compact_ultra [x in _ -> x _]compact_ultra.
move=> + F UF FW => /(_ F UF FW) [h [Wh Fh]]; exists h; split => //.
by move=> Q Fq; apply: (pointwise_cvg_compact_family _ Fh).
Qed.

Lemma precompact_pointwise_precompact (W : set {family compact, X -> Y}) :
  precompact W -> pointwise_precompact W id.
Proof.
move=> + x; rewrite ?precompactE => pcptW.
have : compact (proj x @` (closure W)).
  apply: continuous_compact => //; apply: continuous_subspaceT=> g.
  move=> E nbhsE; have := (@proj_continuous _ _ x g E nbhsE).
  exact: (@pointwise_cvg_compact_family _ _ (nbhs g)).
move=> /[dup]/(compact_closed hsdf)/closure_id -> /subclosed_compact.
apply; first exact: closed_closure.
by apply/closure_subset/image_subset; exact: (@subset_closure _ W).
Qed.

Lemma pointwise_cvg_entourage (x : X) (f : {ptws X -> Y}) E :
  entourage E -> \forall g \near f, E (f x, g x).
Proof.
move=> entE; have : ({ptws, nbhs f --> f}) by [].
have ? : Filter (nbhs f) by exact: nbhs_pfilter. (* NB: This Filter (nbhs f) used to infer correctly. *)
rewrite pointwise_cvg_family_singleton => /fam_cvgP /(_ [set x]).
rewrite uniform_set1 => /(_ _ [set y | E (f x, y)]); apply; first by exists x.
by move: E entE; exact/cvg_entourageP.
Qed.

Lemma equicontinuous_closure (W : set {ptws X -> Y}) :
  equicontinuous W id -> equicontinuous (closure W) id.
Proof.
move=> ectsW x E entE; near=> y => f clWf.
have ? : ProperFilter (within W (nbhs (f : {ptws X -> Y}))).
  exact: within_nbhs_proper. (* TODO: This ProperFilter _ also used to infer correctly. *)
near (within W (nbhs (f : {ptws X -> Y}))) => g.
near: g; rewrite near_withinE; near_simpl; near=> g => Wg.
apply: (@entourage_split _ (g x)) => //.
  exact: (near (pointwise_cvg_entourage _ _ _)).
apply: (@entourage_split _ (g y)) => //; first exact: (near (@ectsW x _ _)).
by apply/entourage_sym; exact: (near (pointwise_cvg_entourage _ _ _)).
Unshelve. all: by end_near. Qed.

Definition small_ent_sub := @small_set_sub _ (@entourage Y).

Lemma pointwise_compact_cvg (F : set_system {ptws X -> Y}) (f : {ptws X -> Y}) :
  ProperFilter F ->
  (\forall W \near powerset_filter_from F, equicontinuous W id) ->
  {ptws, F --> f} <-> {family compact, F --> f}.
Proof.
move=> PF /near_powerset_filter_fromP; case.
  exact: equicontinuous_subset_id.
move=> W; wlog Wf : f W / W f.
  move=> + FW /equicontinuous_closure => /(_ f (closure (W : set {ptws X -> Y}))) Q.
  split => Ff; last by apply: pointwise_cvg_compact_family.
  apply/Q => //.
    by rewrite closureEcvg; exists F; [|split] => // ? /= /filterS; apply.
  by apply: (filterS _ FW) => z Wz; apply: subset_closure.
move=> FW ectsW; split=> [ptwsF|]; last exact: pointwise_cvg_compact_family.
apply/fam_cvgP => K ? U /=; rewrite uniform_nbhs => [[E [eE EsubU]]].
suff : \forall g \near within W (nbhs (f : {ptws X -> Y})),
    forall y, K y -> E (f y, g y).
  rewrite near_withinE; near_simpl => N; apply: (filter_app _ _ FW).
  by apply: ptwsF; near=> g => ?; apply: EsubU; apply: (near N g).
near (powerset_filter_from (@entourage Y)) => E'.
have entE' : entourage E' by exact: (near (near_small_set _)).
pose Q := fun (h : X -> Y) x => E' (f x, h x).
apply: (iffLR (compact_near_coveringP K)) => // x Kx.
near=> y g => /=.
apply: (entourage_split (f x) eE).
  apply entourage_sym; apply: (near (small_ent_sub _) E') => //.
  exact: (near (ectsW x E' entE') y).
apply: (@entourage_split _ (g x)) => //.
  apply: (near (small_ent_sub _) E') => //.
  near: g; near_simpl; apply: (@cvg_within _ (nbhs (f : {ptws X -> Y}))).
  exact: pointwise_cvg_entourage.
apply: (near (small_ent_sub _) E') => //.
apply: (near (ectsW x E' entE')) => //.
exact: (near (withinT _ (nbhs_filter (f : {ptws X -> Y})))).
Unshelve. all: end_near. Qed.

Lemma pointwise_compact_closure (W : set (X -> Y)) :
  equicontinuous W id ->
  closure (W : set {family compact, X -> Y}) =
  closure (W : set {ptws X -> Y}).
Proof.
rewrite ?closureEcvg // predeqE => ? ?.
split; move=> [F PF [Fx WF]]; (exists F; last split) => //.
  apply/@pointwise_compact_cvg => //; apply/near_powerset_filter_fromP.
    exact: equicontinuous_subset_id.
  by exists W => //; exact: WF.
apply/@pointwise_compact_cvg => //; apply/near_powerset_filter_fromP.
  exact: equicontinuous_subset_id.
by exists W => //; exact: WF.
Qed.

Lemma pointwise_precompact_equicontinuous (W : set (X -> Y)) :
  pointwise_precompact W id ->
  equicontinuous W id ->
  precompact (W : set {family compact, X -> Y }).
Proof.
move=> /pointwise_precompact_precompact + ectsW.
rewrite ?precompactE compact_ultra compact_ultra pointwise_compact_closure //.
move=> /= + F UF FcW => /(_ F UF); rewrite image_id => /(_ FcW)[p [cWp Fp]].
exists p; split => //; apply/pointwise_compact_cvg => //.
apply/near_powerset_filter_fromP; first exact: equicontinuous_subset_id.
exists (closure (W : set {ptws X -> Y })) => //.
exact: equicontinuous_closure.
Qed.

Section precompact_equicontinuous.
Hypothesis lcptX : locally_compact [set: X].

Lemma compact_equicontinuous (W : set {family compact, X -> Y}) :
  (forall f, W f -> continuous f) ->
  compact (W : set {family compact, X -> Y}) ->
  equicontinuous W id.
Proof.
move=> ctsW cptW x E entE.
have [//|U UWx [cptU clU]] := @lcptX x; rewrite withinET in UWx.
near (powerset_filter_from (@entourage Y)) => E'.
have entE' : entourage E' by exact: (near (near_small_set _)).
pose Q := fun (y : X) (f : {family compact, X -> Y}) => E' (f x, f y).
apply: (iffLR (compact_near_coveringP W)) => // f Wf; near=> g y => /=.
apply: (entourage_split (f x) entE).
  apply/entourage_sym; apply: (near (small_ent_sub _) E') => //.
  exact: (near (fam_nbhs _ entE' (@compact_set1 _ x)) g).
apply: (entourage_split (f y) (entourage_split_ent entE)).
  apply: (near (small_ent_sub _) E') => //.
  by apply/xsectionP; near: y; apply: (@ctsW f Wf x); exact: nbhs_entourage.
apply: (near (small_ent_sub _) E') => //.
by apply: (near (fam_nbhs _ entE' cptU) g) => //; exact: (near UWx y).
Unshelve. all: end_near. Qed.

Lemma precompact_equicontinuous (W : set {family compact, X -> Y}) :
  (forall f, W f -> continuous f) ->
  precompact (W : set {family compact, X -> Y}) ->
  equicontinuous W id.
Proof.
move=> pcptW ctsW; apply: (equicontinuous_subset_id (@subset_closure _ W)).
apply: compact_equicontinuous; last by rewrite -precompactE.
move=> f; rewrite closureEcvg => [[G PG [Gf GW]]] x B /=.
rewrite -nbhs_entourageE => -[E entE] /filterS; apply; near_simpl.
suff ctsf : continuous f.
  near=> x0; apply/xsectionP; near: x0.
  by move: E entE; apply/cvg_app_entourageP; exact: ctsf.
apply/continuous_localP => x'; apply/near_powerset_filter_fromP.
  by move=> ? ?; exact: continuous_subspaceW.
case: (@lcptX x') => // U; rewrite withinET => nbhsU [cptU _].
exists U => //; apply: (uniform_limit_continuous_subspace PG _ _).
  by near=> g; apply: continuous_subspaceT; near: g; exact: GW.
by move/fam_cvgP/(_ _ cptU) : Gf.
Unshelve. all: end_near. Qed.

End precompact_equicontinuous.

Theorem Ascoli (W : set {family compact, X -> Y}) :
    locally_compact [set: X] ->
  pointwise_precompact W id /\ equicontinuous W id <->
    (forall f, W f -> continuous f) /\
    precompact (W : set {family compact, X -> Y}).
Proof.
move=> lcpt; split => [[Wid ectsW]|[fWf]pcptW].
  split=> [?|]; first exact: equicontinuous_continuous.
  exact: pointwise_precompact_equicontinuous.
split; last exact: precompact_equicontinuous.
exact: precompact_pointwise_precompact.
Qed.

End ArzelaAscoli.

Section currying.
Local Import ArrowAsCompactOpen.

Section cartesian_closed.
Context {U V W : topologicalType}.

(**md In this section, we consider under what conditions \
       `[f in U ~> V ~> W | continuous f /\ forall u, continuous (f u)]` \
   and \
       `[f in U * V ~> W | continuous f]` \
   are homeomorphic.
   - Always: \
         `curry` sends continuous functions to continuous functions.
   - `V` locally_compact + regular or Hausdorff: \
         `uncurry` sends continuous functions to continuous functions.
   - `U` regular or Hausdorff: \
         `curry` itself is a continuous map.
   - `U` regular or Hausdorff AND `V` locally_compact + regular or Hausdorff \
         `uncurry` itself is a continuous map. \
         Therefore `curry`/`uncurry` are homeomorphisms.

   So the category of locally compact regular spaces is cartesian closed.
*)

Lemma continuous_curry (f : U * V -> W) :
  continuous f ->
    continuous (curry f) /\ forall u, continuous (curry f u).
Proof.
move=> ctsf; split; first last.
  move=> u z; apply: continuous_comp; last exact: ctsf.
  by apply: cvg_pair => //=; exact: cvg_cst.
move=> x; apply/compact_open_cvgP => K O /= cptK oO fKO.
near=> z => w /= [+ + <-]; near: z.
move/compact_near_coveringP/near_covering_withinP : cptK; apply.
move=> v Kv; have [[P Q] [Px Qv] PQfO] : nbhs (x, v) (f @^-1` O).
  by apply: ctsf; move: oO; rewrite openE; apply; apply: fKO; exists v.
by exists (Q, P) => // -[b a] /= [Qb Pa] Kb; exact: PQfO.
Unshelve. all: by end_near. Qed.

Lemma continuous_curryf (f : U * V -> W) : continuous f -> continuous (curry f).
Proof. by case/continuous_curry. Qed.

Lemma continuous_curry_joint_cvg (f : U * V -> W) (u : U) (v : V) : 
  continuous f -> curry f z.1 z.2 @[z --> (u,v)] --> curry f u v.
Proof. 
move=> cf D /cf; rewrite ?nbhs_simpl /curry /=; apply: filterS => z.
by move=> ?; rewrite /= -surjective_pairing.
Qed.

Lemma continuous_uncurry_regular (f : U -> V -> W) :
  locally_compact [set: V] -> @regular_space V -> continuous f ->
  (forall u, continuous (f u)) -> continuous (uncurry f).
Proof.
move=> lcV reg cf cfp /= [u v] D; rewrite /= nbhsE => -[O [oO Ofuv]] /filterS.
apply; have [B] := @lcV v I; rewrite withinET => Bv [cptB clB].
have [R Rv RO] : exists2 R, nbhs v R & forall z, closure R z -> O (f u z).
  have [] := reg v (f u @^-1` O); first by apply: cfp; exact: open_nbhs_nbhs.
  by move=> R ? ?; exists R.
exists (f @^-1` [set g | g @` (B `&` closure R) `<=` O], B `&` closure R).
  split; [apply/cf/open_nbhs_nbhs; split | apply: filterI] => //.
  - apply: compact_open_open => //; apply: compact_closedI => //.
    exact: closed_closure.
  - by move=> ? [x [? + <-]]; apply: RO.
  - by apply: filterS; first exact: subset_closure.
by case=> a r /= [fBMO [Br] cmR]; apply: fBMO; exists r.
Qed.

Lemma continuous_uncurry (f : U -> V -> W) :
  locally_compact [set: V] -> hausdorff_space V -> continuous f ->
  (forall u, continuous (f u)) -> continuous (uncurry f).
Proof.
move=> lcV hsdf ctsf cf; apply: continuous_uncurry_regular => //.
move=> v; have [B] := @lcV v I; rewrite withinET => Bv [cptB clB].
by move=> z; exact: (compact_regular _ cptB).
Qed.

Lemma curry_continuous (f : (U * V)%type -> W) : continuous f -> @regular_space U ->
  {for f, continuous curry}.
Proof.
move=> ctsf regU; apply/compact_open_cvgP.
  by apply: fmap_filter; exact: nbhs_filter.
move=> K ? cptK [D OfinIo <-] fKD /=; near=> z => w [+ + <-]; near: z.
move/compact_near_coveringP/near_covering_withinP : (cptK); apply => u Ku.
have [] := fKD (curry f u); first by exists u.
move=> E /[dup] /[swap] /OfinIo [N Asub <- DIN INf].
suff : \forall x' \near u & i \near nbhs f, K x' ->
    (\bigcap_(i in [set` N]) i) (curry i x').
  apply: filter_app; near=> a b => /[apply] ?.
  by exists (\bigcap_(i in [set` N]) i).
apply: filter_bigI_within => R RN; have /set_mem [[M cptM _]] := Asub _ RN.
have Rfu : R (curry f u) by exact: INf.
move/(_ _ Rfu) => [O [fMO oO] MOR]; near=> p => /= Ki; apply: MOR => + [+ + <-].
move=> _ v Mv; move: v Mv Ki; near: p.
have umb : \forall y \near u, (forall b, M b -> nbhs (y, b) (f @^-1` O)).
  move/compact_near_coveringP/near_covering_withinP : (cptM); apply => v Mv.
  have [[P Q] [Pu Qv] PQO] : nbhs (u, v) (f @^-1` O).
    by apply: ctsf; apply: open_nbhs_nbhs; split => //; apply: fMO; exists v.
  exists (Q, P); [by []| move=> [b a [/= Qb Pa Mb]]].
  by apply: ctsf; apply: open_nbhs_nbhs; split => //; exact: PQO.
move/compact_near_coveringP/near_covering_withinP : (cptM); apply => v Mv.
have [P' P'u cPO] := regU u _ umb.
pose L := [set h | h @` ((K `&` closure P') `*` M) `<=` O].
exists (setT, P' `*` L).
  split => //; [exact: filterT|]; exists (P', L) => //; split => //.
  apply: open_nbhs_nbhs; split; first apply: compact_open_open => //.
    apply: compact_setX => //; apply: compact_closedI => //.
    exact: closed_closure.
  by move=> ? [[a b] [[Ka /cPO +] Mb <-]] => /(_ _ Mb)/nbhs_singleton.
move=> [b [a h]] [/= _ [Pa] +] Ma Ka; apply.
by exists (a, b); split => //; split => //; exact/subset_closure.
Unshelve. all: by end_near. Qed.

Lemma uncurry_continuous (f : U -> V -> W) :
  locally_compact [set: V] -> @regular_space V -> @regular_space U ->
  continuous f -> (forall u, continuous (f u)) ->
  {for f, continuous uncurry}.
Proof.
move=> lcV regV regU ctsf ctsfp; apply/compact_open_cvgP.
  by apply: fmap_filter; exact:nbhs_filter.
move=> /= K O cptK oO fKO; near=> h => ? [+ + <-]; near: h.
move/compact_near_coveringP/near_covering_withinP: (cptK); apply.
case=> u v Kuv.
have : exists P Q, [/\ closed P, compact Q, nbhs u P,
    nbhs v Q & P `*` Q `<=` uncurry f @^-1` O].
  have : continuous (uncurry f) by exact: continuous_uncurry_regular.
  move/continuousP/(_ _ oO); rewrite openE => /(_ (u, v))[].
    by apply: fKO; exists (u, v).
  case=> /= P' Q' [P'u Q'v] PQO.
  have [B] := @lcV v I; rewrite withinET; move=> Bv [cptB clB].
  have [P Pu cPP'] := regU u P' P'u; have [Q Qv cQQ'] := regV v Q' Q'v.
  exists (closure P), (B `&` closure Q); split.
  - exact: closed_closure.
  - by apply: compact_closedI => //; exact: closed_closure.
  - by apply: filterS; first exact: subset_closure.
  - by apply: filterI=> //; apply: filterS; first exact: subset_closure.
  - by case => a b [/cPP' ?] [_ /cQQ' ?]; exact: PQO.
case=> P [Q [clP cptQ Pu Qv PQfO]]; pose R := [set g : V -> W | g @` Q `<=` O].
(have oR : open R by exact: compact_open_open); pose P' := f @^-1` R.
pose L := [set h : U -> V -> W | h @` (fst @` K `&` P) `<=` R].
exists ((P `&` P') `*` Q, L); first split => /=.
- exists (P `&` P', Q) => //; split => //=; apply: filterI => //.
  apply: ctsf; apply: open_nbhs_nbhs; split => // _ [b Qb <-].
  by apply: (PQfO (u, b)); split => //; exact: nbhs_singleton.
- rewrite nbhs_simpl /=; apply: open_nbhs_nbhs; split.
    apply: compact_open_open => //; apply: compact_closedI => //.
    apply: continuous_compact => //; apply: continuous_subspaceT => x.
    exact: cvg_fst.
  move=> /= _ [a [Kxa Pa] <-] _ [b Qb <-].
  by apply: (PQfO (a, b)); split => //; exact: nbhs_singleton.
move=> [[a b h]] [/= [[Pa P'a] Qb Lh] Kab].
apply: (Lh (h a)); first by exists a => //; split => //; exists (a, b).
by exists b.
Unshelve. all: by end_near. Qed.

End cartesian_closed.

End currying.

HB.mixin Record isContinuous {X Y : nbhsType} (f : X -> Y):= {
  cts_fun : continuous f
}.

#[short(type = "continuousType")]
HB.structure Definition Continuous {X Y : nbhsType} := {
  f of @isContinuous X Y f
}.

HB.instance Definition _ {X Y : topologicalType} := gen_eqMixin (continuousType X Y).
HB.instance Definition _ {X Y : topologicalType} := gen_choiceMixin (continuousType X Y).

Lemma continuousEP {X Y : nbhsType} (f g : continuousType X Y) :
  f = g <-> f =1 g.
Proof.
case: f g => [f [[ffun]]] [g [[gfun]]]/=; split=> [[->//]|/funext eqfg].
rewrite eqfg in ffun *; congr {| Continuous.sort := _; Continuous.class := {|
  Continuous.function_spaces_isContinuous_mixin := {|isContinuous.cts_fun := _|}|}|}.
exact: Prop_irrelevance.
Qed.

Definition mkcts {X Y : nbhsType} (f : X -> Y) (f_cts : continuous f) := f.
HB.instance Definition _ {X Y : nbhsType} (f: X -> Y) (f_cts : continuous f) :=
  @isContinuous.Build X Y (mkcts f_cts) f_cts.

Section continuous_comp.
Context {X Y Z : topologicalType}.
Context (f : continuousType X Y) (g : continuousType Y Z).

Local Lemma cts_fun_comp : continuous (g \o f).
Proof. move=> x; apply: continuous_comp; exact: cts_fun. Qed.

HB.instance Definition _ := @isContinuous.Build X Z (g \o f) cts_fun_comp.

End continuous_comp.

Section continuous_id.
Context {X : topologicalType}.

Local Lemma cts_id : continuous (@idfun X).
Proof. by move=> ?. Qed.

HB.instance Definition _ := @isContinuous.Build X X (@idfun X) cts_id.
End continuous_id.

Section continuous_const.
Context {X Y : topologicalType} (y : Y).

Local Lemma cts_const : continuous (@cst X Y y).
Proof. by move=> ?; exact: cvg_cst. Qed.

HB.instance Definition _ := @isContinuous.Build X Y (cst y) cts_const.
End continuous_const.


Lemma swap_continuous {X Y : topologicalType} : continuous (@swap X Y).
Proof.
case=> a b W /=[[U V]][] /= Ua Vb UVW; exists (V, U); first by split.
by case => //= ? ? [] ? ?; apply: UVW.
Qed.

Lemma min_continuous {d} {T : orderTopologicalType d} :
  continuous (fun xy : T * T => Order.min xy.1 xy.2).
Proof.
case=> x y; case : (pselect (x = y)).
  move=> <- U; rewrite /= min_l // => ux; exists (U, U) => //=.
  case=> a b [/= ? ?]; case /orP : (le_total a b) => ?; first by rewrite min_l.
  by rewrite min_r.
move=>/eqP; wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP []; first exact: WH.
  rewrite eq_sym; move=> yx yNx. 
  have -> : (fun (xy : T *T ) => Order.min xy.1 xy.2) = 
      ((fun xy => Order.min xy.1 xy.2) \o @swap T T).
    apply/funext; case => a b /=; have /orP [? | ?]  := le_total a b.
      by rewrite min_l // min_r.
    by rewrite min_r // min_l.
  apply: continuous_comp; first exact: swap_continuous.
  by apply: WH.
move=> _ U /=; (rewrite min_l //; last exact: ltW) => Ux.
case : (pselect (exists z, x < z < y)%O).
  case=> z xzy; exists (U `&` `]-oo,z[, `]z,+oo[%classic) => //=.
  - split; [apply: filterI =>// |]; apply: open_nbhs_nbhs; split.
    + exact: lray_open.
    + by rewrite set_itvE; case/andP: xzy.
    + exact: rray_open.
    + by rewrite set_itvE; case/andP: xzy.
  - case=> a b /= [][Ua]; rewrite ?in_itv andbT /= => az ?.
    by rewrite min_l //; apply: ltW; apply: (lt_trans az).
move/forallNP => /= xNy.
exists (U `&` `]-oo,y[, `]x,+oo[%classic) => //=.
- split; [apply: filterI =>// |]; apply: open_nbhs_nbhs; split.
  + exact: lray_open.
  + by rewrite set_itvE.
  + exact: rray_open.
  + by rewrite set_itvE.
- case=> a b /= [][Ua]; rewrite ?in_itv andbT /= => ay xb.
  rewrite min_l //; rewrite leNgt; have := xNy b; apply: contra_notN.
  move=> ba; apply/andP; split => //.
  by apply: (lt_trans ba).
Qed.

Lemma min_fun_continuous {d} {X : topologicalType} {T : orderTopologicalType d} 
    (f g : X -> T):
  continuous f -> continuous g -> continuous (f \min g).
Proof.
move=> fc gc z; apply: continuous2_cvg; first apply min_continuous.
  exact: fc.
exact: gc.
Qed.

Lemma max_continuous {d} {T : orderTopologicalType d} :
  continuous (fun xy : T * T => Order.max xy.1 xy.2).
Proof.
case=> x y; case : (pselect (x = y)).
  move=> <- U; rewrite /= max_r // => ux; exists (U, U) => //=.
  case=> a b [/= ? ?]; case /orP : (le_total a b) => ?; first by rewrite max_r.
  by rewrite max_l.
move=>/eqP; wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP []; first exact: WH.
  rewrite eq_sym; move=> yx yNx. 
  have -> : (fun (xy : T *T ) => Order.max xy.1 xy.2) = 
      ((fun xy => Order.max xy.1 xy.2) \o @swap T T).
    apply/funext; case => a b /=; have /orP [? | ?]  := le_total a b.
      by rewrite max_r // max_l.
    by rewrite max_l // max_r.
  apply: continuous_comp; first exact: swap_continuous.
  by apply: WH.
move=> _ U /=; (rewrite max_r //; last exact: ltW) => Ux.
case : (pselect (exists z, x < z < y)%O).
  case=> z xzy; exists (`]-oo,z[%classic, U `&` `]z,+oo[%classic) => //=.
  - split; [|apply: filterI =>//]; apply: open_nbhs_nbhs; split.
    + exact: lray_open.
    + by rewrite set_itvE; case/andP: xzy.
    + exact: rray_open.
    + by rewrite set_itvE; case/andP: xzy.
  - case=> a b /= [] + []; rewrite ?in_itv andbT /= => az ? zb.
    by rewrite max_r //; apply: ltW; apply: (lt_trans az).
move/forallNP => /= xNy.
exists (`]-oo,y[%classic, U `&` `]x,+oo[%classic) => //=.
- split; [|apply: filterI =>//]; apply: open_nbhs_nbhs; split.
  + exact: lray_open.
  + by rewrite set_itvE.
  + exact: rray_open.
  + by rewrite set_itvE.
- case=> a b /=; rewrite ?in_itv /= andbT => [/=] [ay] [?] xb. 
  rewrite max_r //; rewrite leNgt; have := xNy b; apply: contra_notN.
  move=> ba; apply/andP; split => //.
  by apply: (lt_trans ba).
Qed.

Lemma max_fun_continuous {d} {X : topologicalType} {T : orderTopologicalType d} 
    (f g : X -> T):
  continuous f -> continuous g -> continuous (f \max g).
Proof.
move=> fc gc z; apply: continuous2_cvg; first apply max_continuous.
  exact: fc.
exact: gc.
Qed.

Lemma continuous_comp_weak {Y : choiceType} {X Z : topologicalType} (w : Y -> Z) 
  (f : X -> (weak_topology w)) :
  continuous (w \o f) -> continuous f.
Proof.
move=> cf z U [?/= [[W oW <-]]] /= Wsfz /filterS; apply; apply: cf.
by apply: open_nbhs_nbhs; split.
Qed.

Lemma uncurryK  {X Y Z : Type} : cancel (@uncurry X Y Z) curry.
Proof. by move=> f; rewrite funeq2E => ? ?. Qed.

Lemma curryK  {X Y Z : Type} : cancel curry (@uncurry X Y Z).
Proof. by move=> f; rewrite funeqE; case=> ? ?. Qed.

Section reassociate_products.
Context {X Y Z : Type}.
Definition left_assoc_prod (xyz : (X * Y) * Z) : X * (Y * Z) := 
  (xyz.1.1,(xyz.1.2,xyz.2)).

Definition right_assoc_prod (xyz : X * (Y * Z)) : (X * Y) * Z := 
  ((xyz.1,xyz.2.1),xyz.2.2).

Lemma left_assoc_prodK : cancel left_assoc_prod right_assoc_prod.
Proof. by case;case. Qed.

Lemma right_assoc_prodK : cancel right_assoc_prod left_assoc_prod.
Proof. by case => ? []. Qed.
End reassociate_products.

Section reassociate_continuous.
Context {X Y Z : topologicalType}.

Lemma left_assoc_prod_continuous : continuous (@left_assoc_prod X Y Z). 
Proof.
case;case=> a b c U [[/= P V]] [Pa] [][/= Q R][ Qb Rc] QRV PVU.
exists ((P `*` Q), R); first split.
- exists (P, Q); first split => //=.
  by case=> x y /= [Px Qy]; split => //.
- done.
- case; case=> x y z /= [][] ? ? ?; apply: PVU; split => //.
  exact: QRV.
Qed.

Lemma right_assoc_prod_continuous : continuous (@right_assoc_prod X Y Z). 
Proof.
case=> a [b c] U [[V R]] [/= [[P Q /=]]] [Pa Qb] PQV Rc VRU.
exists (P, (Q `*` R)); first split.
- done. 
- exists (Q, R); first split => //=.
  by case=> ? ? /= [? ?]; split.
- case=> x [y z] [? [? ?]]; apply: VRU; split => //.
  exact: PQV.
Qed.

End reassociate_continuous.

Section composition.

HB.instance Definition _ (U T : topologicalType) :=
  Topological.copy 
    (continuousType U T)
    (weak_topology (id : continuousType U T -> {compact-open, U -> T})).

Local Import ArrowAsCompactOpen.

Definition eval {X Y : topologicalType} : continuousType X Y * X -> Y  := 
  uncurry (id : continuousType X Y -> (X -> Y)).

Lemma eval_continuous {X Y : topologicalType} : 
  locally_compact [set: X] -> regular_space X -> continuous (@eval X Y).
Proof.
move=> ? ?; apply: continuous_uncurry_regular => //.
  exact: weak_continuous.
by move=> ?; exact: cts_fun.
Qed.

Definition comp_cts {X Y Z : topologicalType} (g : continuousType Y Z)
    (f : continuousType X Y) : continuousType X Z :=
  g \o f.

Lemma compose_continuous {X Y Z : topologicalType} : 
  locally_compact [set: X] -> @regular_space X ->
  locally_compact [set: Y] -> @regular_space Y ->
  continuous (uncurry (fun g f => (@comp_cts X Y Z) g f)).
Proof.
move=> ? ? lY rY; apply: continuous_comp_weak. 
set F := _ \o _.
rewrite -[F]uncurryK; apply: continuous_curryf.
pose g := uncurry F \o right_assoc_prod \o (@swap _ _); simpl in *.
have -> : uncurry F = uncurry F \o right_assoc_prod \o left_assoc_prod.
  by rewrite funeqE; case; case.
move=> z; apply: continuous_comp; first exact: left_assoc_prod_continuous.
have -> : uncurry F \o right_assoc_prod = 
    uncurry F \o right_assoc_prod \o (@swap _ _) \o (@swap _ _).
  by rewrite funeqE; case; case.
apply: continuous_comp; first exact: swap_continuous.
pose h (fxg : continuousType X Y * X * continuousType Y Z) : Z := 
  eval (fxg.2, ((eval fxg.1))).
have <- : h = uncurry F \o right_assoc_prod \o (@swap _ _).
  by rewrite /h/g/right_assoc_prod/uncurry/swap/F funeqE; case; case.
rewrite /h.
apply: (@continuous2_cvg _ _ _ _ _ _ (snd) (eval \o fst) (curry eval)).
- by apply: continuous_curry_joint_cvg; exact: eval_continuous.
- exact: cvg_snd.
- by apply: cvg_comp; [exact: cvg_fst | exact: eval_continuous].
Qed.
End composition.

Lemma openX {X Y : topologicalType} (A : set X) (B : set Y) : 
  open A -> open B -> open (A `*` B).
Proof.
move=> oA oB; move=> [a b] [/= ? ?]; exists (A, B).
  by split; apply: open_nbhs_nbhs.
by case=> ? ? [] /=.
Qed.

Lemma weak_hausdorff {X : choiceType} {Y : topologicalType} (f : X -> Y) : 
  injective f -> hausdorff_space Y -> hausdorff_space (weak_topology f).
Proof.
move=> injf hY a b clA; apply: injf; apply: hY => U V Ufa Vfb.
have [] := clA (f @^-1` U) (f @^-1` V); try exact: weak_continuous. 
by move=> z [/= ? ?]; exists (f z).
Qed.

Require Import EqdepFacts.

Section wedge.
Local Open Scope quotient_scope.
Context {I : choiceType} (X : I -> topologicalType) (p0 : forall i, X i).

Let wedge_rel' (a b : {i & X i}) := 
  (a == b) || ((projT2 a == p0 _) && (projT2 b == p0 _)).

Local Lemma wedge_rel_refl : reflexive wedge_rel'.
Proof. by move=> ?; rewrite /wedge_rel' eqxx. Qed.

Local Lemma wedge_rel_sym : symmetric wedge_rel'.
Proof. move=> a b.
suff : (is_true (wedge_rel' a b) <-> is_true (wedge_rel' b a)).
  case: (wedge_rel' a b) => //; case: (wedge_rel' b a) => // [].
    by case=> ->.
  by case=> _ ->.
by split; rewrite /wedge_rel'=> /orP [/eqP -> // /[!eqxx] //|] /andP [] /eqP ->;
  move=> /eqP ->; rewrite ?eqxx /= orbT.
Qed.

Local Lemma wedge_rel_trans : transitive wedge_rel'.
Proof. 
move=> a b c /orP [/eqP -> //|] + /orP [ /eqP <- // |].
rewrite /wedge_rel'; case/andP=> /eqP -> /eqP <- /andP [] /eqP _ ->.
by apply/orP; right; rewrite eqxx.
Qed.

Definition wedge_rel := EquivRel _ wedge_rel_refl wedge_rel_sym wedge_rel_trans.
Global Opaque wedge_rel.

Definition wedge := {eq_quot wedge_rel}.
Definition wedgei (i : I) : X i -> wedge := \pi_wedge \o (existT X i).

HB.instance Definition _ := Topological.copy wedge (quotient_topology wedge).
HB.instance Definition _ := Quotient.on wedge.
Global Opaque wedge.

Lemma wedgei_continuous (i : I) : continuous (@wedgei i).
Proof. by move=> ?; apply: continuous_comp => //; exact: pi_continuous. Qed.

HB.instance Definition _ (i : I) := @isContinuous.Build _ _ 
  (@wedgei i) (@wedgei_continuous i).

Lemma wedgei_nbhs (i : I) (x : X i) : 
  closed [set p0 i] -> x != p0 _ -> (@wedgei i) @ x = nbhs (wedgei x).
Proof.
move=> clx0 xNx0; rewrite eqEsubset; split => U; first last.
  by move=> ?; apply: wedgei_continuous.
rewrite ?nbhsE /=; case => V [oV Vx VU].
exists ((@wedgei  i) @` (V `&` ~`[set p0 i])); first last.
  by move=> ? /= [l] [Vl lx] <-; apply: VU.
split; last by exists x => //; split => //=; apply/eqP.
rewrite /open /= /quotient_open /wedgei /=.
suff -> : \pi_wedge @^-1` ((@wedgei i) @` (V `&` ~`[set p0 i])) = 
          (existT X i) @` (V `&` ~`[set p0 i]).
  by apply: existT_open_map; apply: openI => //; exact: closed_openC.
rewrite eqEsubset; split => t /= [l [Vl] lNx0]; last by move=> <-; exists l.
case/eqmodP/orP => [/eqP <- |]; first by exists l.
by move=> /= /andP [/eqP]; move: lNx0 => /[swap] ->.  
Qed.

Lemma wedge_openP (U : set wedge) :
  open U <-> (forall i, open (@wedgei i @^-1` U)).
Proof.
split.
  move=> oU i; apply: open_comp => // ? _.
  by apply: continuous_comp => //; exact: pi_continuous.
move=> oiU.
have : open (\bigcup_i (@wedgei i @` (@wedgei i @^-1` U) )).
  apply/sigT_openP => i; move: (oiU i); congr(open _). 
  rewrite eqEsubset; split => x /=.
    by move=> Ux; exists i => //; exists x => //.
  case=> j _ /= [] y Uy /eqmodP /orP [/eqP R|].
    have : j = i by move: R; apply: eq_sigT_fst.
    move=> E; destruct E; move: Uy; congr(U (_ _)); move: R.
    apply: Eqdep_dec.inj_pair2_eq_dec.
    by move => p q; case: (pselect (p = q)) => ?; [left | right].
  case/andP=> /eqP/= + /eqP ->; move: Uy => /[swap] ->; congr(_ _).
  by apply/eqmodP; apply/orP; right; rewrite ?eqxx.
congr(open _); rewrite eqEsubset; split => /= z.
  by case=> i _ /= [x] Ux <-.
move=> Uz; exists (projT1 (repr z)) => //=. 
by exists (projT2 (repr z)); rewrite /wedgei /= -?sigT_eta ?reprK.
Qed.

Lemma wedge_pointE i j : existT _ i (p0 i)  = existT _ j (p0 j)  %[mod wedge].
Proof. by apply/eqmodP; apply/orP; right; rewrite ?eqxx. Qed.

Lemma wedge_point_nbhs i0 : 
  nbhs (wedgei (p0 i0)) = \bigcap_i ((@wedgei i) @ p0 i).
Proof.
rewrite eqEsubset; split => //= U /=; rewrite ?nbhs_simpl.
  case=> V [/= oV Vp] VU j _; apply: wedgei_continuous.
  move/filterS: VU; apply => //; first exact: (@nbhs_filter wedge).
  apply: open_nbhs_nbhs; split => //; move: Vp; congr( _ _).
  by rewrite /wedgei /=; exact: wedge_pointE.
move=> Uj; have V_ : forall i, {V : set (X i) |  
    [/\ open V, V (p0 i) & V `<=` (@wedgei i) @^-1` U]}.
  (move=> j; have Ij : [set: I] j by done); apply: cid.
  by move: (Uj _ Ij); rewrite nbhsE /=; case=> B [? ? ?]; exists B.
pose W := \bigcup_i (@wedgei i) @` (projT1 (V_ i)).
exists W; split.
- apply/wedge_openP => i; rewrite /W; have [+ Vpj _] := projT2 (V_ i).
  congr(_ _); rewrite eqEsubset; split => z; first by move=> Viz; exists i.
  case => j _ /= [] w /= svw /eqmodP /orP [/eqP [E]| ].
    destruct E => R; have <- // := Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ R.
    by move=> a b; case: (pselect (a = b)) => ?; [left | right].
  by case/andP=> /eqP /= _ /eqP ->.
- by exists i0 => //=; exists (p0 i0) => //; have [_ + _] := projT2 (V_ i0).
- by move=> ? [j _ [x ? <-]]; have [_ _] := projT2 (V_ j); apply.
Qed.

Variant wedge_nbhs_spec (z : wedge) : wedge -> set_system wedge -> Type := 
  | WedgeIsPoint i0 :
      wedge_nbhs_spec z (wedgei (p0 i0)) (\bigcap_i ((@wedgei i) @ p0 i))
  | WedgeNotPoint (i : I) (x : X i) of (x != p0 i):
      wedge_nbhs_spec z (wedgei x) (@wedgei i @ x).

Lemma wedge_nbhs_specP (z : wedge) : (forall i, closed [set p0 i]) ->
  wedge_nbhs_spec z z (nbhs z).
Proof.
move=> clP; rewrite -[z](@reprK _ wedge); case: (repr z).
move=> i x; case: (pselect (x = p0 i)).
  move=> ->; rewrite wedge_point_nbhs => /=; apply: WedgeIsPoint. 
by move/eqP => xpi; rewrite /= -wedgei_nbhs //; apply: WedgeNotPoint.
Qed.

Definition wedge_fun {Z : Type} (f : forall i, X i -> Z) : wedge -> Z := 
  sigT_fun f \o repr.

Lemma wedge_fun_continuous {Z : topologicalType} (f : forall i, X i -> Z) :
  (forall i, continuous (f i)) ->
  (forall i j, f i (p0 i) = f j (p0 j)) -> 
  continuous (wedge_fun f).
Proof.
move=> cf fE; apply: repr_comp_continuous; first exact: sigT_continuous.
move=> a b /eqP/eqmodP /orP [ /eqP -> // | /andP [/eqP +] /eqP +].
by rewrite /sigT_fun /= => -> ->; exact/eqP/fE.
Qed.

Lemma wedge_fun_wedgei {Z : Type} (f : forall i, X i -> Z) i0 (a : X i0): 
  (forall i j, f i (p0 i) = f j (p0 j)) -> wedge_fun f (wedgei a) = f i0 a.
Proof. 
move=> fE.
rewrite /wedge_fun /wedgei /= /sigT_fun /=; case: piP => z /= /eqmodP.
by case/orP => [/eqP <- // | /andP [/eqP /= ->] /eqP ->]; apply: fE.
Qed.

Lemma wedge_fun_comp {Z1 Z2 : Type} (h : Z1 -> Z2) (f : forall i, X i -> Z1) : 
  h \o wedge_fun f = wedge_fun (fun i => h \o f i).
Proof. by apply/funext => z; rewrite /= /wedge_fun /= /sigT_fun /=. Qed.

Lemma wedgeTE : \bigcup_i (@wedgei i) @` setT = [set: wedge].
Proof. 
rewrite -subTset=> z _; rewrite -[z]reprK; exists (projT1 (repr z)) => //.
by exists (projT2 (repr z)); rewrite // reprK /wedgei /= -sigT_eta reprK.
Qed.

Lemma wedge_compact : finite_set [set: I] -> (forall i, compact [set: X i]) -> 
  compact [set: wedge].
Proof.
move=> fsetI cptX.
rewrite -wedgeTE -fsbig_setU //; apply: big_ind.
- exact: compact0.
- by move=> ? ? ? ?; exact: compactU.
move=> i _; apply: continuous_compact; last exact: cptX.
by apply: continuous_subspaceT; exact: wedgei_continuous.
Qed.

(* The wedge maps into the product
   \bigcup_i [x | x j = p0 j  when j != i]
   
   For the box topology, it's an embedding. But more practically,
   since the box and product agree when `I` is finite, 
   we get that the finite wedge embeds into the finite product.
 *)
Section wedge_as_product.
Definition wedge_prod_fun : wedge -> prod_topology X :=
  wedge_fun (fun i x => dfwith (p0) i x).

Lemma wedge_prod_fun_pointE (i j : I) : dfwith p0 i (p0 i) = dfwith p0 j (p0 j).
Proof.
apply: functional_extensionality_dep => k /=.
case: dfwithP; first case: dfwithP => //.
by move=> i1 iNi1; case: dfwithP => //.
Qed.

Lemma wedge_prod_fun_inj : injective wedge_prod_fun.
Proof.
have ? := wedge_prod_fun_pointE.
move=> a b; rewrite -[a](@reprK _ wedge) -[b](@reprK _ wedge). 
case Ea : (repr a)=> [i x]; case Eb : (repr b) => [j y].
rewrite /wedge_prod_fun /= ?wedge_fun_wedgei //. 
move=> dfij; apply/eqmodP/orP.
case: (pselect (i = j)) => E.
  destruct E; left; apply/eqP; congr(_ _).
  have : dfwith p0 i x i = dfwith p0 i y i by rewrite dfij.
  by rewrite ?dfwithin.
right => /=; apply/andP; split; apply/eqP.
  have : dfwith p0 i x i = dfwith p0 j y i by rewrite dfij.
  by rewrite dfwithin => ->; rewrite dfwithout // eq_sym; apply/eqP.
have : dfwith p0 i x j = dfwith p0 j y j by rewrite dfij.
by rewrite dfwithin => <-; rewrite dfwithout //; apply/eqP.
Qed.

Lemma wedge_prod_continuous : continuous wedge_prod_fun.
Proof.
apply: wedge_fun_continuous; last exact: wedge_prod_fun_pointE.
exact: dfwith_continuous.
Qed.

Lemma wedge_prod_open (x : wedge) (A : set wedge) :
  finite_set [set: I] -> 
  (forall i, closed [set p0 i]) ->
  nbhs x A -> 
  @nbhs _ (subspace (range wedge_prod_fun)) (wedge_prod_fun x) (wedge_prod_fun @` A).
Proof.
move=> fsetI clI; case: wedge_nbhs_specP => //. 
  move=> i0 bcA. 
  pose B_ i : set ((subspace (range wedge_prod_fun))) := proj i @^-1` (@wedgei i@^-1` A).
  have /finite_fsetP [fI fIE] := fsetI.
  have : (\bigcap_(i in [set` fI]) B_ i) `&` range wedge_prod_fun `<=` wedge_prod_fun @` A.
    move=> ? [] /[swap] [][] z _ <- /= Bwz; exists z => //.
    have Iz : [set` fI] (projT1 (repr z)) by rewrite -fIE //.
    have := Bwz _ Iz; congr(A _); rewrite /wedgei /= -[RHS]reprK.
    apply/eqmodP/orP; left; rewrite /proj /=.
    by rewrite /wedge_prod_fun /= /wedge_fun /sigT_fun /= dfwithin -sigT_eta.
  move/filterS; apply.
  apply/nbhs_subspace_ex; first by exists (wedgei (p0 i0)).
  exists (\bigcap_(i in [set` fI]) B_ i); last by rewrite -setIA setIid.
  apply: filter_bigI => i _.
  rewrite /B_; apply: proj_continuous. 
  (have Ii : [set: I] i by done); have /= := bcA _ Ii; congr(nbhs _ _).
  rewrite /proj /wedge_prod_fun. 
  rewrite wedge_fun_wedgei; last exact: wedge_prod_fun_pointE.
  by case: dfwithP.
move=> i z zNp0 /= wNz.
rewrite [x in nbhs x _]/wedge_prod_fun /= wedge_fun_wedgei; first last. 
  exact: wedge_prod_fun_pointE.
have : wedge_prod_fun @` (A `&` (@wedgei i @` ~`[set p0 i]))  `<=`  wedge_prod_fun @` A.
  by move=> ? [] ? [] + /= [w] wpi => /[swap] <- Aw <-; exists (wedgei w).
move/filterS; apply; apply/nbhs_subspace_ex. 
  exists (wedgei z) => //.
  by rewrite /wedge_prod_fun wedge_fun_wedgei //; exact: wedge_prod_fun_pointE.
exists (proj i @^-1` (@wedgei i @^-1` (A `&` (@wedgei i @` ~`[set p0 i])))).
  apply/ proj_continuous; rewrite /proj dfwithin preimage_setI; apply: filterI.
    exact: wNz.
  have /filterS := @preimage_image _ _ (@wedgei i) (~` [set p0 i]).
  apply; apply: open_nbhs_nbhs; split; first exact: closed_openC.
  by apply/eqP.
rewrite eqEsubset; split => // ?; case => /[swap] [][] r _ <- /=.
  case => ? /[swap] /wedge_prod_fun_inj -> [+ [e /[swap]]] => /[swap].
  move=> <- Awe eNpi; rewrite /proj /wedge_prod_fun /=.
  rewrite ?wedge_fun_wedgei; last exact: wedge_prod_fun_pointE.
  rewrite dfwithin; split => //; first by (split => //; exists e).
  exists (wedgei e) => //.
  by rewrite wedge_fun_wedgei //; exact: wedge_prod_fun_pointE.
case=> /[swap] [][y] yNpi E Ay.
case : (pselect (i = (projT1 (repr r)))); first last. 
  move=> R; move: yNpi; apply: absurd.
  move: E; rewrite /proj/wedge_prod_fun /wedge_fun /=/sigT_fun /=. 
  rewrite dfwithout //; last by rewrite eq_sym; apply/eqP.
  case/eqmodP/orP; last by case/andP => /= /eqP E.
  move=> /eqP => E.
  have := Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ E; apply.
  by move=> a b; case: (pselect (a = b)) => ?; [left | right].
move=> riE; split; exists (wedgei y) => //.
- by split; [rewrite E | exists y].
- congr (wedge_prod_fun _); rewrite E.
  rewrite /proj /wedge_prod_fun /wedge_fun /=/sigT_fun.
  by rewrite riE dfwithin  /wedgei /= -sigT_eta reprK.
- congr(wedge_prod_fun _); rewrite E .
  rewrite /proj /wedge_prod_fun /wedge_fun /=/sigT_fun.
  by rewrite riE dfwithin  /wedgei /= -sigT_eta reprK.
Qed.
End wedge_as_product.

Lemma wedge_hausdorff : 
  (forall i, hausdorff_space (X i)) -> 
  hausdorff_space wedge.
Proof.
move=> /hausdorff_product hf => x y clxy.
apply: wedge_prod_fun_inj; apply: hf => U V /wedge_prod_continuous.
move=> nU /wedge_prod_continuous nV; have := clxy _ _ nU nV.
by case => z [/=] ? ?; exists (wedge_prod_fun z).
Qed.

Lemma wedge_fun_joint_continuous (T R: topologicalType) 
  (k : forall (x : I), T -> X x -> R):
  (finite_set [set: I]) ->
  (forall x, closed [set p0 x]) ->
  (forall t x y, k x t (p0 x) = k y t (p0 y)) ->
  (forall x, continuous (uncurry (k x))) ->
  continuous (uncurry (fun t => wedge_fun (fun x => k x t))). 
Proof.
move=> Ifin clp0 kE kcts /= [t u] U.
case : (wedge_nbhs_specP u) => //.
  move=> i0; rewrite /= wedge_fun_wedgei // => Ukp0.
  have pq_ : forall x, {PQ : set T * set (X x) |
    [/\nbhs (p0 x) PQ.2, nbhs t PQ.1 & PQ.1 `*` PQ.2 `<=` uncurry (k x) @^-1` U]}.
    move=> x; apply: cid.
    move: Ukp0; rewrite (@kE t i0 x).
    rewrite -[k x ]uncurryK /curry=> /kcts; case; case=> P Q /= [Pt Qp0 pqU].
    by exists (P,Q) => //.
  have UPQ : nbhs (wedgei (p0 i0)) (
      \bigcup_x (@wedgei x) @` (snd (projT1 (pq_ x)))).
    rewrite wedge_point_nbhs => r _.
    by case: (projT2 (pq_ r)) => /filterS + ? ?; apply => z /= ?; by exists r.
  have /finite_fsetP [fI fIE] := Ifin.
  have UPt : nbhs t (\bigcap_(r in [set` fI]) (fst (projT1 (pq_ r)))).
    by apply: filter_bigI => x ?; case: (projT2 (pq_ x)).
  near_simpl => /=; near=> t1 t2 => /=.
  have [] // := near UPQ t2 => x _ [w /=] ? <-.
  rewrite wedge_fun_wedgei //.
  case: (projT2 (pq_ x)) => ? Npt /(_ (t1, w)) => /=; apply; split => //.
  by have := near UPt t1; apply; rewrite // -fIE.
move: u => _ x u uNp0 /=; rewrite wedge_fun_wedgei //=.
rewrite -[k x]uncurryK /curry => /kcts; rewrite nbhs_simpl /=.
case; case => /= P Q [Pt Qu] PQU.
have wQu : nbhs (wedgei u) ((@wedgei x) @` Q).
  rewrite -wedgei_nbhs //=; move/filterS: Qu; apply.
  by move=> z; exists z.
near_simpl; near=> t1 t2 => /=.
have [] // := near wQu t2 => l ? <-; rewrite wedge_fun_wedgei //.
apply: (PQU (t1,l)); split => //.
exact: (near Pt t1).
Unshelve. all: by end_near. Qed.
End wedge.

HB.mixin Record isBiPointed (X : Type) of Equality X := {
  zero : X;
  one : X;
  zero_one_neq : zero != one;
}.

#[short(type="biPointedType")]
HB.structure Definition BiPointed := 
  { X of Choice X & isBiPointed X }.

#[short(type="bpTopologicalType")]
HB.structure Definition BiPointedTopological := 
  { X of BiPointed X & Topological X }.

Section bpwedge.
Context (X Y : bpTopologicalType).
Definition wedge2 b := if b then X else Y.
Definition wedge2p b := if b return wedge2 b then (@one X) else (@zero Y).
Local Notation bpwedge := (@wedge bool wedge2 wedge2p).
Local Notation bpwedgei := (@wedgei bool wedge2 wedge2p).
  
Local Lemma wedge_neq : @bpwedgei true zero != @bpwedgei false one .
Proof.
apply/eqP => R; have /eqmodP/orP[/eqP //|/andP[ /= + _]] := R.
by have := (@zero_one_neq X) => /[swap] ->.
Qed.

Local Lemma bpwedgeE : @bpwedgei true one = @bpwedgei false zero .
Proof. by rewrite/wedgei /= (@wedge_pointE bool _ _ true false). Qed.

HB.instance Definition _ := @isBiPointed.Build 
  bpwedge (@bpwedgei true zero) (@bpwedgei false one) wedge_neq.
End bpwedge.

Notation bpwedge X Y := (@wedge bool (wedge2 X Y) (wedge2p X Y)).
Notation bpwedgei X Y := (@wedgei bool (wedge2 X Y) (wedge2p X Y)).

HB.mixin Record isPath {i : bpTopologicalType} {T: topologicalType} (x y : T) 
    (f : i -> T) of isContinuous i T f := {
  path_zero : f zero = x;
  path_one : f one = y;
}.

#[short(type="pathType")]
HB.structure Definition Path {i : bpTopologicalType} {T: topologicalType} 
  (x y : T) := {f of isPath i T x y f & isContinuous i T f}.

Notation "{ 'path' i 'from' x 'to' y }" := (pathType i x y) (at level 0) : type_scope.

HB.instance Definition _ {i : bpTopologicalType} 
    {T : topologicalType} (x y : T) := gen_eqMixin {path i from x to y}.
HB.instance Definition _ {i : bpTopologicalType} 
    {T : topologicalType} (x y : T) := gen_choiceMixin {path i from x to y}.
HB.instance Definition _ {i : bpTopologicalType} 
    {T : topologicalType} (x y : T) := 
  Topological.copy {path i from x to y} 
    (@weak_topology {path i from x to y} {compact-open, i -> T} id).

Section path_eq.
Context {T : topologicalType} {i : bpTopologicalType} (x y : T).

Lemma path_eqP (a b : {path i from x to y}) :   
  a = b <-> Path.sort a = Path.sort b.
Proof.
split; first by move => ->.
case: a; case: b => /= f [[+ +]] g [[+ +]] fgE. 
rewrite fgE => /= a1 [b1 c1] a2 [b2 c2]. 
congr (_ _ ).
have -> : a1 = a2 by exact: Prop_irrelevance.
have -> : b1 = b2 by exact: Prop_irrelevance.
have -> : c1 = c2 by exact: Prop_irrelevance.
done.
Qed.
End path_eq.

Section cst_path.
Context {T : topologicalType} {i : bpTopologicalType} (x: T).

HB.instance Definition _ := @isPath.Build i T x x (cst x) erefl erefl.
End cst_path.

Section path_domain_path.
Context {i : bpTopologicalType}.
HB.instance Definition _ := @isPath.Build i i zero one idfun erefl erefl.
End path_domain_path.

Section path_compose.
Context {T U : topologicalType} (i: bpTopologicalType) (x y : T).
Context (f : continuousType T U) (p : {path i from x to y}).

Local Lemma fp_zero : (f \o p) zero = f x.
Proof. by rewrite /= ?path_zero. Qed.

Local Lemma fp_one : (f \o p) one = f y.
Proof. by rewrite /= ?path_one. Qed.

HB.instance Definition _ := isPath.Build i U (f x) (f y) (f \o p)
  fp_zero fp_one.

End path_compose.

Section path_reparameterize.
Context {T : topologicalType} (i j: bpTopologicalType) (x y : T).
Context (f : {path i from x to y}) (phi : {path j from (@zero i) to one}).

Definition reparameterize := f \o phi.

Local Lemma fphi_zero : reparameterize zero = x.
Proof. by rewrite /reparameterize /= ?path_zero. Qed.

Local Lemma fphi_one : reparameterize one = y.
Proof. by rewrite /reparameterize /= ?path_one. Qed.

Local Lemma fphi_cts : continuous reparameterize.
Proof. by move=> ?; apply: continuous_comp; apply: cts_fun. Qed.

HB.instance Definition _ := isContinuous.Build _ _ reparameterize fphi_cts.

HB.instance Definition _ := isPath.Build j T x y reparameterize
  fphi_zero fphi_one.
End path_reparameterize.

Section mk_path.
Context {i : bpTopologicalType} {T : topologicalType}.
Context {x y : T} {f : continuousType i T}.
Context (f0 : f zero = x) (f1 : f one = y).

Definition mk_path : i -> T := let _ := (f0,f1) in f.

HB.instance Definition _ := Continuous.on mk_path.
HB.instance Definition _ := @isPath.Build i T x y mk_path f0 f1.
End mk_path.

Definition chain_path {i j : bpTopologicalType} {T : topologicalType} 
    (f : i -> T) (g : j -> T) : bpwedge i j -> T :=
  wedge_fun (fun b => if b return wedge2 i j b -> T then f else g).

Section chain_path.
Context {T : topologicalType} {i j : bpTopologicalType} (x y z: T).
Context (p : {path i from x to y}) (q : {path j from y to z}).

Local Lemma chain_path_zero : chain_path p q zero = x.
Proof.
rewrite /chain_path /= wedge_fun_wedgei ?path_one ?path_zero //.
by case => //= [][] //=; rewrite ?path_one ?path_zero.
Qed.

Local Lemma chain_path_one : chain_path p q one = z.
Proof.
rewrite /chain_path /= wedge_fun_wedgei ?path_zero ?path_one //.
by case => //= [][] //=; rewrite ?path_one ?path_zero.
Qed.

Local Lemma chain_path_cts : continuous (chain_path p q).
Proof.
by apply: wedge_fun_continuous; case; (try now (exact: cts_fun));
  case => //=;rewrite ?path_one ?path_zero //.
Qed.

HB.instance Definition _ :=  @isContinuous.Build _ T (chain_path p q)
  chain_path_cts.
HB.instance Definition _ :=  @isPath.Build _ T x z (chain_path p q)
  chain_path_zero chain_path_one.
End chain_path.

(* Such a structure is very much like [a,b] in that
   one can split it in half like `[0,1] \/ [0,1] ~ [0,2] ~ [0,1]
*)
HB.mixin Record isSelfSplit (X : Type) of BiPointedTopological X := {
  to_wedge  : {path X from (@zero (bpwedge X X)) to one};
  to_wedge_bij : bijective to_wedge;
  to_wedge_cts : continuous to_wedge;
  to_wedge_open : forall A, open A -> open (to_wedge @` A);
}.

#[short(type="selfSplitType")]
HB.structure Definition SelfSplit := {
  X of BiPointedTopological X & isSelfSplit X
}.

Section path_concat.
Context {T : topologicalType} {i : selfSplitType} (x y z: T).
Context (p : {path i from x to y}) (q : {path i from y to z}).

Definition path_concat : {path i from x to z} :=
  reparameterize (chain_path p q) (to_wedge).

End path_concat.

Section self_wedge_path.
Context {i : selfSplitType}.

Definition from_wedge_sub : bpwedge i i -> i  := 
  ((bijection_of_bijective (@to_wedge_bij i))^-1)%FUN.

Local Lemma from_wedge_zero : from_wedge_sub zero = zero.
Proof.
move/bij_inj : (@to_wedge_bij i); apply.
rewrite /from_wedge_sub /=. 
have /= -> := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
  by rewrite path_zero.
by apply/mem_set.
Qed.

Local Lemma from_wedge_one : from_wedge_sub one = one.
Proof.
move/bij_inj : (@to_wedge_bij i); apply.
rewrite /from_wedge_sub /=. 
have /= -> := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
  by rewrite path_one.
exact/mem_set.
Qed.

Local Lemma from_wedge_cts : continuous from_wedge_sub.
Proof.
apply/continuousP => A /to_wedge_open.
congr(_ _); rewrite eqEsubset; split => //.
  move=> ? /= [z Az <-]; rewrite /from_wedge_sub.
  by rewrite funK => //; apply/mem_set.
move=> z /=; exists (from_wedge_sub z) => //.
rewrite /from_wedge_sub.
have /= -> // := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
exact/mem_set.
Qed.

HB.instance Definition _ := isContinuous.Build _ _ from_wedge_sub from_wedge_cts.

HB.instance Definition _ := isPath.Build (bpwedge i i) i zero one from_wedge_sub
  from_wedge_zero from_wedge_one.
End self_wedge_path.

HB.lock Definition from_wedge {i : selfSplitType} : {path (bpwedge i i) from (@zero i) to one} := 
  [the pathType _ _ _ of from_wedge_sub].
Canonical locked_from_wedge := Unlockable from_wedge.unlock.

Lemma from_wedgeK {i : selfSplitType} : cancel from_wedge (@to_wedge i).
Proof.
move=> z; rewrite unlock /= /from_wedge_sub.
have /= -> // := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
exact/mem_set.
Qed.

Lemma to_wedgeK {i : selfSplitType}: cancel (@to_wedge i) from_wedge.
Proof.
move=> z; rewrite unlock /= /from_wedge_sub funK //. 
exact/mem_set.
Qed.

Section path_join_assoc. 
Context (i : selfSplitType).

Let i_i := @bpwedge i i.
Local Open Scope quotient_scope.
Notation "f '<>' g" := (@path_concat _ i _ _ _ f g).

Lemma conact_cstr {T : topologicalType} (x y : T) (f : {path i from x to y}) :
  exists (p : {path i from zero to one}), f \o p = (f <> cst y).
Proof.
exists (idfun <> cst one). 
rewrite compA wedge_fun_comp /path_concat.
congr( _ \o to_wedge); congr(wedge_fun _).
apply: functional_extensionality_dep; case => //=.
by apply/funext => ? /=; rewrite /cst path_one.
Qed.

Lemma conact_cstl {T : topologicalType} (x y : T) (f : {path i from x to y}) :
  exists (p : {path i from zero to one}), f \o p = (cst x <> f).
Proof.
exists (cst zero <> idfun). 
rewrite compA wedge_fun_comp /path_concat.
congr( _ \o to_wedge); congr(wedge_fun _).
apply: functional_extensionality_dep; case => //=.
by apply/funext => ? /=; rewrite /cst path_zero.
Qed.

Let ii_i := (bpwedge i_i i).
Let i_ii := (bpwedge i i_i).
Check @wedgei.
Let wedgel_i_i : {path i from zero to _} := 
  @mk_path _ _ _ _ 
    [the continuousType _ _ of @wedgei _ (wedge2 i i) _ true]
    erefl (bpwedgeE _ _).
Let wedger_i_i : {path i from _ to one} :=
  @mk_path _ _ _ _ 
    [the continuousType _ _ of @wedgei _ (wedge2 i i) _ false] 
    erefl erefl.

Let splitl_left : {path i_i from (@zero ii_i) to _} := 
  (@mk_path _ _ _ _ 
      [the continuousType _ _ of @bpwedgei i_i i true] 
    erefl (@bpwedgeE _ _)).
Let splitl_right : {path i from _ to (@one ii_i)} := 
  @mk_path _ _ _ _ 
      [the continuousType _ _ of @bpwedgei i_i i false] 
     erefl erefl.
Let splitl : {path i from (@zero ii_i) to one} := 
  (reparameterize splitl_left to_wedge) <> splitl_right.

Let splitr_right : {path i_i from _ to (@one i_ii)} := 
  @mk_path _ _ _ _ 
    [the continuousType _ _ of @bpwedgei i i_i false]
    erefl erefl.
Let splitr_left : {path i from (@zero i_ii) to _} := 
  @mk_path _ _ _ _ 
    [the continuousType _ _ of @bpwedgei i i_i true]
     erefl (bpwedgeE _ _).

Let unsplitr : {path i_ii from zero to one} := 
  reparameterize 
    from_wedge 
    (chain_path wedgel_i_i (reparameterize wedger_i_i from_wedge)).
  
Let associ : continuousType ii_i i_ii := 
  chain_path 
    (chain_path 
      (splitr_left)
      (splitr_right \o wedgel_i_i))
    (splitr_right \o wedger_i_i).

Section assoc.
Context {T : topologicalType} {p1 p2 p3 p4: T}. 
Context (f : {path i from p1 to p2}).
Context (g : {path i from p2 to p3}).
Context (h : {path i from p3 to p4}).

Local Lemma assoc0 : associ zero = zero.
Proof.
rewrite /associ /= /chain_path /= ?wedge_fun_wedgei //.
  by case; case; rewrite //= ?bpwedgeE.
case; case; rewrite //= ?bpwedgeE //= ?wedge_fun_wedgei /= ?bpwedgeE //=.
  by case; case; rewrite //= ?bpwedgeE.
by case; case; rewrite //= ?bpwedgeE.
Qed.

Local Lemma assoc1 : associ one = one.
Proof.
rewrite /associ /= /chain_path /= ?wedge_fun_wedgei //.
case; case; rewrite //= ?bpwedgeE //= ?wedge_fun_wedgei /= ?bpwedgeE //=.
  by case; case; rewrite //= ?bpwedgeE.
by case; case; rewrite //= ?bpwedgeE.
Qed.
 
(* not really non-forgetful, but we can make it local anyway so it's fine*)
#[local, non_forgetful_inheritance]
HB.instance Definition _ := isPath.Build ii_i _ _ _ associ
  assoc0 assoc1.

Local Lemma concat_assocl : 
  (f <> (g <> h)) \o (unsplitr \o associ \o splitl) = 
    ((f <> g) <> h).
Proof.
Ltac wedge_simpl := repeat (
    rewrite ?(wedge_fun_wedgei, path_one, path_zero, bpwedgeE, reprK) //=;
  (try (case;case))).
apply/funext => z; rewrite /= /reparameterize /=/associ/chain_path.
rewrite -[to_wedge z](@reprK _ i_i). 
case E : (repr (to_wedge z)) => [b x] /=.
wedge_simpl;  rewrite /= ?from_wedgeK ?to_wedgeK.
case: b x E => x E /=; wedge_simpl; first last.
  by rewrite from_wedgeK; wedge_simpl.
rewrite -[to_wedge x](@reprK _ i_i); case: (repr (to_wedge x)) => [b2 y] /=.
case: b2 y => y; wedge_simpl; rewrite from_wedgeK.
wedge_simpl.
Qed.
  
Lemma concat_assoc: 
  exists p : {path i from zero to one}, 
    (f <> (g <> h)) \o p = ((f <> g) <> h).
Proof.
exists (reparameterize unsplitr (reparameterize associ splitl)). 
by rewrite concat_assocl. 
Qed.

End assoc.
End path_join_assoc.

HB.mixin Record isPathDomain {d} (i : Type) of 
  OrderTopological d i & SelfSplit i := {
  (* this makes the path_between relation symmetric*)
  flip : {path i from (@one i) to (@zero i)};
  flipK : involutive flip;
  (* this lets us curry for paths between paths*)
  domain_locally_compact : locally_compact [set: i];
  (* this gives us homotopies between {path i from zero to one} and `idfun`*)
  zero_bot : forall (y:i), (@Order.le d i zero y);
  one_top : forall (y:i), (@Order.le d i y one);
}.

#[short(type="pathDomainType")]
HB.structure Definition PathDomain {d} := 
  { i of @OrderTopological d i & SelfSplit i & isPathDomain d i}.

Lemma path_domain_set1 {d} {i : pathDomainType d} (x : i) : 
  closed [set x].
Proof.
exact/accessible_closed_set1/hausdorff_accessible/order_hausdorff.
Qed.

#[global] Hint Resolve path_domain_set1 : core.

Section path_flip.
Context {d} {T : topologicalType} (i : pathDomainType d) (x y : T).
Context (f : {path i from x to y}).

Definition path_flip := f \o flip.

Local Lemma fflip_zero : path_flip zero = y.
Proof. by rewrite /path_flip /= path_zero path_one. Qed.

Local Lemma fflip_one : path_flip one = x.
Proof. by rewrite /path_flip /= path_one path_zero. Qed.

Local Lemma fflip_cts : continuous path_flip.
Proof. by move=> ?; apply: continuous_comp; apply: cts_fun. Qed.

HB.instance Definition _ := isContinuous.Build _ _ path_flip fflip_cts.

HB.instance Definition _ := isPath.Build i T y x path_flip
  fflip_zero fflip_one.
End path_flip.


Lemma continuous_uncurry_min {d} {T : orderTopologicalType d} : 
  continuous (uncurry (@Order.min d T)). 
Proof.
by have := (@min_continuous d T); congr(continuous _); rewrite funeq2E => ? []. 
Qed.

Lemma continuous_uncurry_max {d} {T : orderTopologicalType d} : 
  continuous (uncurry (@Order.max d T)). 
Proof.
by have := (@max_continuous d T); congr(continuous _); rewrite funeq2E => ? []. 
Qed.

Section path_connected.
Context {d} {i : pathDomainType d}.
Local Open Scope quotient_scope.
Notation "f '<>' g" := (path_concat f g).

Section path_component.
Context {T : topologicalType}.

Let path_between_sub (a b : T) := `[<$| {path i from a to b}|>].

Lemma path_between_refl : reflexive path_between_sub.
Proof. by move=> x; apply/asboolP; apply: squash; exact: (cst x). Qed.

Lemma path_between_sym : symmetric path_between_sub. 
Proof.  
move=> a b.
suff : (is_true (path_between_sub a b) <-> is_true (path_between_sub b a)).
  case: (path_between_sub a b) => //; case: (path_between_sub b a) => // [].
    by case=> ->.
  by case=> _ ->.
by split => /asboolP /unsquash f; exact/asboolP/squash/(path_flip f).
Qed.

Lemma path_between_trans : transitive path_between_sub.
Proof.  
move=> x y z; case/asboolP=> f /asboolP [g].
apply/asboolP/squash; exact: (f <> g).
Qed.

Definition path_between := EquivRel _ 
  path_between_refl path_between_sym path_between_trans.

Definition path_components := {eq_quot path_between}.
End path_component.

Arguments path_components : clear implicits.

Lemma path_uncurry_cts {T : topologicalType} (x y : T)
  (a b : {path i from x to y}) (f : {path i from a to b})  : 
    continuous (uncurry [eta f]).
Proof.
apply: continuous_uncurry.
- exact: domain_locally_compact.
- exact: order_hausdorff.
- suff : continuous (@Path.sort i _ x y \o f : i -> {compact-open, i -> T}). 
    by exact.
  move=> ?; apply: continuous_comp; first exact: cts_fun.
  exact: weak_continuous.
- by move=> t; exact: cts_fun.
Qed.

Lemma path_between_pathP {T : topologicalType} (x y : T) (a b : {path i from x to y}) : 
  path_between a b <-> exists (f : i * i -> T), 
    [/\continuous f, 
       forall t, curry f t zero = x,
       forall t, curry f t one = y,
       curry f zero = a & 
       curry f one = b].
Proof.
split.
  case/asboolP => f; exists (uncurry [eta f]); split.
  - exact: path_uncurry_cts.
  - by move=> t; exact: path_zero.
  - by move=> t; exact: path_one.
  - by apply/funext => ?; rewrite /curry /= path_zero.
  - by apply/funext => ?; rewrite /curry /= path_one.
case=> f [cf ft0 ft1 f0 f1]; apply/asboolP.
have ftcts t : Continuous.axioms_ (curry f t).
  by have [_ ] := continuous_curry cf; exact.
have ftpath t : Path.axioms_ x y (curry f t).
  by exists (ftcts t); split => //.
apply: squash; exists (fun t => Path.Pack (ftpath t)). 
have cpf : Continuous.axioms_ (fun t => Path.Pack (ftpath t)).
  split; split; apply: continuous_comp_weak; rewrite /comp //=.
  exact: continuous_curryf.
by exists cpf; split; apply/path_eqP => //=.
Qed.

Section i_path.

Local Lemma reparam_path_lt (p q: {path i from (@zero i) to one}) :
  (forall j, p j <= q j)%O ->
  path_between p q.
Proof.
move=> svj; apply/path_between_pathP.
pose f := ((q \o snd) \min (fst \max (p \o snd))).
exists f; split; rewrite /f/curry /=.
- apply: min_fun_continuous => //. 
      move=>? ; apply:continuous_comp; first by move=> ?; exact: cvg_snd.
      exact: cts_fun.
  apply: max_fun_continuous => //; first by move=> ?; exact: cvg_fst.
  move=>? ; apply:continuous_comp; first by move=> ?; exact: cvg_snd.
  exact: cts_fun.
- by move=> t; rewrite min_l ?path_zero ?zero_bot.
- by move=> t; rewrite min_r ?path_one ?one_top ?max_r ?one_top.
- by apply/funext=> u; rewrite max_r ?zero_bot // min_r.
- by apply/funext=> u; rewrite max_l ?one_top // min_l // one_top.
Qed.

Local Lemma reparam_path_id (p: {path i from (@zero i) to one}) :
  path_between p idfun.
Proof.
pose q := idfun \min p.
have cq : Continuous.axioms_ q.
  split; split; apply: min_fun_continuous; first by move=> ?; exact: cvg_id. 
  exact: cts_fun.
have q_path : Path.axioms_ zero one q.
  by exists cq; split; rewrite /q /= ?path_zero ?path_one ?min_l ?path_zero.
apply: (@path_between_trans _ (Path.Pack q_path)). 
  rewrite path_between_sym; apply: reparam_path_lt; move=> j. 
  by rewrite /= /q /= ge_min lexx orbT.
by apply: reparam_path_lt; move=> j; rewrite /q /= ge_min lexx.
Qed.

Lemma reparam_path (p q: {path i from (@zero i) to one}) :
  path_between p q.
Proof.
apply: (@path_between_trans {path i from zero to one} idfun). 
  exact: reparam_path_id.
by rewrite path_between_sym; exact: reparam_path_id.
Qed.

Lemma reparam_path_between {T : topologicalType} (x y : T) 
  (phi: {path i from (@zero i) to one}) (f : {path i from x to y}) :
  path_between f (reparameterize f phi).
Proof.
apply/path_between_pathP.
have /path_between_pathP [h [hcts ht0 ht1 h0 h1]] := reparam_path idfun phi.
exists (f \o h); split.
- by move=> ?; apply: continuous_comp; [exact: hcts | exact: cts_fun].
- by move=> t; move: (ht0 t); rewrite /curry /= => ->; rewrite path_zero.
- by move=> t; move: (ht1 t); rewrite /curry /= => ->; rewrite path_one.
- by apply/funext => u; move/funeqP/(_ u): h0;  rewrite /curry /= => ->.
- by apply/funext => u; move/funeqP/(_ u): h1;  rewrite /curry /= => ->.
Qed.

End i_path.

Section path_between_functor.
Context {T U: topologicalType}.

Lemma path_bewteen_fun {f : T -> U} (p q : T):
  continuous f -> path_between p q -> path_between (f p) (f q).
Proof.
move=> cf /asboolP/unsquash => g; apply/asboolP/squash.
have fg0 : (f \o g) zero = f p by rewrite /= path_zero.
have fg1 : (f \o g) one = f q by rewrite /= path_one.
apply: @mk_path _ _ _ _ (mkcts cf \o g) fg0 fg1.
Qed.

End path_between_functor.

Section path_between_wedge.
Local Import ArrowAsCompactOpen.
Context {T: topologicalType} (x y z : T).

Lemma path_concat_joint_continuous 
  (f g : i -> i -> T):
  (forall t, f t one = g t zero) ->
  (continuous (uncurry f)) ->
  (continuous (uncurry g)) ->
  continuous (uncurry (fun t => chain_path (f t) (g t) \o to_wedge)). 
Proof.
move=> hkE cf cg.
set k := fun _ => _.
pose h := uncurry (fun t => chain_path (f t) (g t)).
rewrite (_ : uncurry k = h \o (fun xy => (xy.1, to_wedge (xy.2)))); first last.
  by rewrite /h /k funeqE; case.
move=> r; apply: continuous_comp.
  apply: @continuous2_cvg. 
  - by move=> ? /filterS; apply =>  ? //=; rewrite -surjective_pairing.
  - exact: cvg_fst.
  - apply: cvg_comp; first exact: cvg_snd.
  - exact: cts_fun.
apply: wedge_fun_joint_continuous => //.
- exact: finite_finset.
- move => ?; apply/ accessible_closed_set1/ hausdorff_accessible.
  by rewrite /wedge2 /= if_same; apply: order_hausdorff.
- by move=> ? [][].
- by case.
Qed.

Lemma path_between_wedge (a a' : {path i from x to y}) 
    (b b' : {path i from y to z}) :
  path_between a a' -> path_between b b' ->
  path_between (a <> b) (a' <> b').
Proof.
have ? := (@domain_locally_compact _ i).
have ? : hausdorff_space i by exact: order_hausdorff.
case/asboolP => h /asboolP [] k; apply/path_between_pathP.
exists (uncurry (fun t => (h t) <> (k t))); split.
- apply: path_concat_joint_continuous.
- by move=> ?; rewrite ?path_one ?path_zero.
- apply: continuous_uncurry => //.
    move=> ?; apply: continuous_comp; first exact: cts_fun.
    exact: weak_continuous.
  by move=> ?; apply: cts_fun.
- apply: continuous_uncurry => //.
    move=> ?; apply: continuous_comp; first exact: cts_fun.
    exact: weak_continuous.
  by move=> ?; apply: cts_fun.
- by move => t; rewrite uncurryK path_zero.
- by move => t; rewrite uncurryK path_one.
- by rewrite uncurryK ?path_zero.
- by rewrite uncurryK ?path_one.
Qed.
End path_between_wedge.
  
Section fundamental_groupoid.
Context {T: topologicalType}.

(* arrows in the category of endpoint-preserving homotopies *)
Definition fundamental_groupoid (x y : T) := 
  path_components {path i from x to y}.

HB.instance Definition _ (x y : T) := EqQuotient.on (fundamental_groupoid x y).

Local Notation fdg := (fundamental_groupoid).

Definition fdg_op {x y z : T} (l : fdg x y) (r : fdg y z) : fdg x z := 
  \pi_(fdg x z) (repr l <> repr r).

Notation "l '<.>' r" := (fdg_op l r) (at level 70).

Definition fdg_zero (x : T) : fdg x x := \pi_(fdg x x) (cst x).

Lemma fdg_op_zeror (x y : T) (a : fdg x y) : (a <.> fdg_zero y) = a.
Proof.
rewrite -[a]reprK /fdg_zero; apply/eqmodP; rewrite ?reprK /=.
apply: (@path_between_trans {path i from x to y} (repr a <> cst y)).
  apply: path_between_wedge => //.
  rewrite /fdg_zero /=; case: piP=> r /eqmodP; rewrite path_between_sym; apply.
rewrite path_between_sym.
have [p /= E] := conact_cstr (repr a).
have /= := (reparam_path_between p (repr a)).
congr (path_between _ _); apply/path_eqP => //=.
Qed.

Lemma fdg_op_zerol (x y : T) (a : fdg x y) : (fdg_zero x <.> a) = a.
Proof.
rewrite -[a]reprK; apply/eqmodP; rewrite ?reprK /=.
apply: (@path_between_trans {path i from x to y} (cst x <> repr a)).
  apply: path_between_wedge => //.
  rewrite /fdg_zero /=; case: piP=> r /eqmodP; rewrite path_between_sym; apply.
rewrite path_between_sym; have [p /= E] := conact_cstl (repr a).
have /= := (reparam_path_between p (repr a)).
congr (path_between _ _); apply/path_eqP => //=.
Qed.

Lemma fdg_op_assoc (p1 p2 p3 p4 : T) (f : fdg p1 p2) 
    (g : fdg p2 p3) (h : fdg p3 p4) : 
  (f <.> (g <.> h)) = ((f <.> g) <.> h).
Proof.
rewrite -[f]reprK -[g]reprK -[h]reprK /=; apply/eqmodP. 
rewrite /fdg_op ?reprK /=.
apply: (@path_between_trans _ ((repr f) <> ((repr g) <> (repr h)))).
  apply: path_between_wedge => //.
  by case: piP => r /eqmodP; rewrite /= path_between_sym.
apply: (@path_between_trans _ (((repr f) <> (repr g)) <> (repr h))).
  have [] := @concat_assoc _ _ _ _ _ _ (repr f) (repr g) (repr h);
     rewrite ?path_one ?path_zero //.
  move=> p E.
  have /= := (reparam_path_between p (repr f <> (repr g <> repr h))).
  congr (path_between _ _); apply/path_eqP => //=.
apply: path_between_wedge => //.
by case: piP => r /eqmodP; rewrite /= path_between_sym.
Qed.

Definition fdg_op_inv (x y : T) (f : fdg x y) :=
  \pi_(fdg y x) (path_flip (repr f)).

Lemma fdg_op_invr (x y : T) (f : fdg x y) : 
  fdg_zero x = (f <.> fdg_op_inv f).
Proof.
Ltac wedge_simpl := repeat (
    rewrite ?(wedge_fun_wedgei, path_one, path_zero, bpwedgeE) //=;
  (try (case;case))).
rewrite -[f]reprK; apply/eqmodP; rewrite ?reprK.
apply: (@path_between_trans _ (repr f <> (path_flip (repr f)))); first last.
  apply: path_between_wedge => //.
  by case: piP => r /eqmodP; rewrite /= path_between_sym.
apply/path_between_pathP.
pose h t := chain_path 
  ((repr f) \o (Order.min t)) 
  ((repr f) \o (Order.min t) \o flip) \o to_wedge.
have ? := @order_hausdorff _ i.
have ? := @domain_locally_compact _ i.
have ? : forall b : bool, closed [set wedge2p i i b].
  by case; exact: path_domain_set1.
exists (uncurry h); split => //; first last.
- apply/funext => u; rewrite /curry/uncurry/h /=.
  by case: (wedge_nbhs_specP (to_wedge u)) => //; case; rewrite /chain_path /path_flip;
    [ | | move=> ? ? | move=> ? ?]; wedge_simpl; rewrite ?min_r ?one_top; wedge_simpl.
- apply/funext => u; rewrite /curry/uncurry/h /=.
  by case: (wedge_nbhs_specP (to_wedge u)) => //; case; rewrite /chain_path /path_flip;
    [ | | move=> ? ? | move=> ? ?]; wedge_simpl; rewrite ?min_l ?zero_bot; wedge_simpl.
- move=> t; rewrite /curry/uncurry/h /= /chain_path.
  by wedge_simpl; rewrite min_r ?zero_bot ?path_zero.
- move=> t; rewrite /curry/uncurry/h /= /chain_path.
  by wedge_simpl; rewrite min_r ?zero_bot ?path_zero.
apply: path_concat_joint_continuous.
- by move=> t; rewrite /= path_zero.
- rewrite ( _ : uncurry _ = (repr f \o (fun tu => @Order.min _ i tu.1 tu.2))) //.
    move=> ?; apply: continuous_comp;[exact: min_continuous | exact: cts_fun].
  by apply/funext; case=> ? ?.
- rewrite ( _ : uncurry _ = 
  (repr f \o (fun tu => @Order.min _ i tu.1 tu.2) \o (fun xy => (xy.1, flip xy.2)))) //; first last.
    by apply/funext; case=> ? ?.
move=> ?; apply: continuous_comp. 
    apply: cvg_pair; first exact: cvg_fst.
    apply: cvg_comp; first exact: cvg_snd.
    exact: cts_fun.
move=> ?; apply: continuous_comp; first exact: min_continuous.
exact: cts_fun.
Qed.

Lemma fdg_op_invl (x y : T) (f : fdg x y) : 
  fdg_zero y = (fdg_op_inv f <.> f).
Proof.
rewrite -[f]reprK; apply/eqmodP; rewrite ?reprK.
apply: (@path_between_trans _ ((path_flip (repr f)) <> repr f)); first last.
  apply: path_between_wedge => //.
  by case: piP => r /eqmodP; rewrite /= path_between_sym.
rewrite path_between_sym; apply/path_between_pathP.
pose h t := chain_path 
  ((repr f) \o (Order.max t) \o flip) 
  ((repr f) \o (Order.max t)) \o to_wedge.
have ? := @order_hausdorff _ i.
have ? := @domain_locally_compact _ i.
have ? : forall b : bool, closed [set wedge2p i i b].
  by case; exact: path_domain_set1.
exists (uncurry h); split => //; first last.
- apply/funext => u; rewrite /curry/uncurry/h /=.
  by case: (wedge_nbhs_specP (to_wedge u)) => //; case; rewrite /chain_path /path_flip;
    [ | | move=> ? ? | move=> ? ?]; wedge_simpl; rewrite ?max_l ?one_top; wedge_simpl.
- apply/funext => u; rewrite /curry/uncurry/h /=.
  by case: (wedge_nbhs_specP (to_wedge u)) => //; case; rewrite /chain_path /path_flip;
    [ | | move=> ? ? | move=> ? ?]; wedge_simpl; rewrite ?max_r ?zero_bot; wedge_simpl.
- move=> t; rewrite /curry/uncurry/h /= /chain_path.
  by wedge_simpl; rewrite max_r ?one_top ?path_one.
- move=> t; rewrite /curry/uncurry/h /= /chain_path.
  by wedge_simpl; rewrite max_r ?one_top ?path_one.
apply: path_concat_joint_continuous.
- by move=> t; rewrite /= path_one.
- rewrite ( _ : uncurry _ = 
    (repr f \o (fun tu => @Order.max _ i tu.1 tu.2) \o (fun xy => (xy.1, flip xy.2)))) //; first last.
      by apply/funext; case=> ? ?.
  move=> ?; apply: continuous_comp. 
      apply: cvg_pair; first exact: cvg_fst.
      apply: cvg_comp; first exact: cvg_snd.
      exact: cts_fun.
  move=> ?; apply: continuous_comp; first exact: max_continuous.
  exact: cts_fun.
- rewrite ( _ : uncurry _ = (repr f \o (fun tu => @Order.max _ i tu.1 tu.2))) //.
    move=> ?; apply: continuous_comp;[exact: max_continuous | exact: cts_fun].
  by apply/funext; case=> ? ?.
Qed.

End fundamental_groupoid.


Section fundamental_groupoid_functor.

Implicit Types T U V: topologicalType.

Notation "l '<.>' r" := (fdg_op l r) (at level 70).

Local Notation fdg := (fundamental_groupoid).

Definition fdg_lift {T U} (f : continuousType T U)  (x y : T) (a : fdg x y) : 
    fdg (f x) (f y) :=
  \pi_(fdg (f x) (f y)) (comp_cts f (repr a) : {path i from f x to f y}).

Lemma fundamental_groupoid_functor {T U} (f : continuousType T U) (x y z : T)
  (a : fdg x y) (b : fdg y z) : 
  fdg_lift f a <.> fdg_lift f b = fdg_lift f (a <.> b).
Proof.
apply/eqmodP.
case: piP => p1 /eqmodP; case: piP => p2 /eqmodP; case: piP => p3/eqmodP.
move=> p3ab p2b p1a; apply: equiv_trans.
  apply: path_between_wedge.
    rewrite equiv_sym; exact: p1a.
  rewrite equiv_sym; exact: p2b.
have -> : comp_cts f (repr a) <> comp_cts f (repr b) = 
    (comp_cts f (repr a <> repr b)).
  apply/path_eqP; rewrite /= /comp_cts /path_concat /reparameterize /chain_path.
  rewrite /chain_path [f \o (_ \o to_wedge)]compA.
  rewrite wedge_fun_comp /= /chain_path /=.
  congr (wedge_fun _ \o to_wedge). 
  apply: functional_extensionality_dep; case => //.
apply/path_between_pathP.
case/path_between_pathP: p3ab => h [ch ht0 ht1 h0 h1].
exists (f \o h); split.
- by move=> ?; apply: continuous_comp; [exact: ch | exact: cts_fun].
- by move=> t; move: (ht0 t); rewrite /curry/= => <-.
- by move=> t; move: (ht1 t); rewrite /curry/= => <-.
- apply/funext => t; move: h0; rewrite funeqE.
  by move/(_ t); rewrite /curry/= => <-.
- apply/funext => t; move: h1; rewrite funeqE.
  by move/(_ t); rewrite /curry/= => <-.
Qed.

Lemma fdg_lift_zero {T U} 
  (f : continuousType T U) (x : T) :
  fdg_lift f (fdg_zero x) = fdg_zero (f x).
Proof.
apply/eqmodP; rewrite equiv_sym.
case: piP=> p1/eqmodP/path_between_pathP [h [ch ht0 ht1 h0 h1]].
apply/path_between_pathP; exists (f \o h); split.
- by move=> ?; apply: continuous_comp; [exact: ch | exact: cts_fun].
- by move=> t; move: (ht0 t); rewrite /curry/= => <-.
- by move=> t; move: (ht1 t); rewrite /curry/= => <-.
- apply/funext => t. move: h0; rewrite funeqE.
  by move/(_ t); rewrite /cst /= /cst /curry /= => ->.
- apply/funext => t; move: h1; rewrite funeqE.
  by move/(_ t); rewrite /curry/= => <-.
Qed.

Lemma fdg_lift_comp {T U V} 
  (f : continuousType T U) (g : continuousType U V) (x y : T) :
  @fdg_lift _ _ (g \o f) x y = 
  (@fdg_lift _ _ g (f x) (f y)) \o (@fdg_lift _ _ f x y).
Proof.
apply/funext=> a /=; apply/eqmodP.
case: piP => p1 /eqmodP. 
rewrite /comp_cts -[(g \o f) \o _]compA.
case/path_between_pathP=> h [ch ht0 ht1 h0 h1].
apply/path_between_pathP; exists (g \o h); split.
- by move=> ?; apply: continuous_comp; [exact: ch | exact: cts_fun].
- by move=> t; move: (ht0 t); rewrite /curry/= => <-.
- by move=> t; move: (ht1 t); rewrite /curry/= => <-.
- apply/funext => t; move: h0; rewrite funeqE.
  by move/(_ t); rewrite /curry/= => <-.
- apply/funext => t; move: h1; rewrite funeqE.
  by move/(_ t); rewrite /curry/= => <-.
Qed.

Lemma fdg_lift_id {T} (x y : T) (a : fdg x y) :
  fdg_lift (idfun) a = a.
Proof.
rewrite -[RHS]reprK /= /fdg_lift; congr(_ _). 
by apply/path_eqP; apply/funext.
Qed.

End fundamental_groupoid_functor.
End path_connected.
