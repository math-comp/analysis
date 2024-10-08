(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions wochoice.
From mathcomp Require Import cardinality mathcomp_extra fsbigop set_interval.
From mathcomp Require Export filter.
Require Import reals signed.

(**md**************************************************************************)
(* # Basic topological notions                                                *)
(*                                                                            *)
(* This file develops tools for the manipulation of basic topological         *)
(* notions. The development of topological notions builds on "filtered types" *)
(* by extending the hierarchy.                                                *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### Topology                                                               *)
(* ```                                                                        *)
(*                  topologicalType == interface type for topological space   *)
(*                                     structure                              *)
(*                                     the HB class is Topological.           *)
(*                 ptopologicalType == a pointed topologicalType              *)
(*             orderTopologicalType == a topology built from intervals        *)
(*                             open == set of open sets                       *)
(*                           closed == set of closed sets                     *)
(*                         clopen U == U is both open and closed              *)
(*                      open_nbhs p == set of open neighbourhoods of p        *)
(*                          basis B == a family of open sets that converges   *)
(*                                     to each point                          *)
(*               second_countable T == T has a countable basis                *)
(*                    continuous f <-> f is continuous w.r.t the topology     *)
(*                      [locally P] := forall a, A a -> G (within A (nbhs x)) *)
(*                                     if P is convertible to G (globally A)  *)
(*           Nbhs_isNbhsTopological == factory for a topology defined by a    *)
(*                                     filter                                 *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of nbhs and  *)
(*                                     hence assumes that the carrier is a    *)
(*                                     filterType.                            *)
(*                isOpenTopological == factory for a topology defined by open *)
(*                                     sets                                   *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of open      *)
(*                                     sets, nbhs_of_open must be used to     *)
(*                                     declare a filterType.                  *)
(*                isBaseTopological == factory for a topology defined by a    *)
(*                                     base of open sets                      *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of a base of *)
(*                                     open sets; the type of indices must be *)
(*                                     a pointedType                          *)
(*                 filterI_iter F n == nth stage of recursively building the  *)
(*                                     filter of finite intersections of F    *)
(*                    finI_from D f == set of \bigcap_(i in E) f i where E is *)
(*                                     a finite subset of D                   *)
(*             isSubBaseTopological == factory for a topology defined by a    *)
(*                                     subbase of open sets                   *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from a subbase of open sets b    *)
(*                                     indexed on domain D                    *)
(* ```                                                                        *)
(* We endow several standard types with the structure of topology, e.g.:      *)
(* - products `(T * U)%type`                                                  *)
(* - matrices `'M[T]_(m, n)`                                                  *)
(* - natural numbers `nat`                                                    *)
(* ```                                                                        *)
(*                  weak_topology f == weak topology by a function f : S -> T *)
(*                                     on S                                   *)
(*                                     S must be a choiceType and T a         *)
(*                                     topologicalType.                       *)
(*                  sup_topology Tc == supremum topology of the family of     *)
(*                                     topologicalType structures Tc on T     *)
(*                 order_topology T == the induced order topology on T        *)
(*              quotient_topology Q == the quotient topology corresponding to *)
(*                                     quotient Q : quotType T where T has    *)
(*                                     type topologicalType                   *)
(*                              x^' == set of neighbourhoods of x where x is  *)
(*                                     excluded (a "deleted neighborhood")    *)
(*                        closure A == closure of the set A.                  *)
(*                    limit_point E == the set of limit points of E           *)
(*                           closed == set of closed sets.                    *)
(*                        cluster F == set of cluster points of F             *)
(*                          compact == set of compact sets w.r.t. the filter- *)
(*                                     based definition of compactness        *)
(*                   compact_near F == the filter F contains a closed compact *)
(*                                     set                                    *)
(*                     precompact A == the set A is contained in a closed and *)
(*                                     compact set                            *)
(*                locally_compact A == every point in A has a compact         *)
(*                                     (and closed) neighborhood              *)
(*                discrete_space T <-> every nbhs is a principal filter       *)
(*           discrete_topology dscT == the discrete topology on T, provided   *)
(*                                     dscT : discrete_space T                *)
(*        finite_subset_cover D F A == the family of sets F is a cover of A   *)
(*                                     for a finite number of indices in D    *)
(*                    cover_compact == set of compact sets w.r.t. the open    *)
(*                                     cover-based definition of compactness  *)
(*                    near_covering == a reformulation of covering compact    *)
(*                                     better suited for use with `near`      *)
(*             near_covering_within == equivalent definition of near_covering *)
(*                     connected A <-> the only non empty subset of A which   *)
(*                                     is both open and closed in A is A      *)
(*                    separated A B == the two sets A and B are separated     *)
(*            connected_component x == the connected component of point x     *)
(* ```                                                                        *)
(*                                                                            *)
(* ### Uniform spaces                                                         *)
(* ```                                                                        *)
(*                      nbhs_ ent == neighborhoods defined using entourages   *)
(*                    uniformType == interface type for uniform spaces: a     *)
(*                                   type equipped with entourages            *)
(*                                   The HB class is Uniform.                 *)
(*                   puniformType == a pointed and uniform space              *)
(*                      entourage == set of entourages in a uniform space     *)
(*                 Nbhs_isUniform == factory to build a topological space     *)
(*                                   from a mixin for a uniform space         *)
(*                    split_ent E == when E is an entourage, split_ent E is   *)
(*                                   an entourage E' such that E' \o E' is    *)
(*                                   included in E when seen as a relation    *)
(*         countable_uniformity T == T's entourage has a countable base       *)
(*                                   This is equivalent to `T` being          *)
(*                                   metrizable.                              *)
(*             unif_continuous f <-> f is uniformly continuous                *)
(*                entourage_ ball == entourages defined using balls           *)
(* ```                                                                        *)
(*                                                                            *)
(* `weak_topology`, `sup_ent`, `discrete_ent` are equipped with the `Uniform` *)
(* structure.                                                                 *)
(* We endow several standard types with the structure of uniform space, e.g.: *)
(* - products `(U * V)%type`                                                  *)
(* - matrices `'M[T]_(m, n)`                                                  *)
(*                                                                            *)
(* ### PseudoMetric spaces                                                    *)
(* ```                                                                        *)
(*                entourage_ ball == entourages defined using balls           *)
(*               pseudoMetricType == interface type for pseudo metric space   *)
(*                                   structure: a type equipped with balls    *)
(*                                   The HB class is PseudoMetric.            *)
(*              pseudoPMetricType == a pointed an pseudoMetric space          *)
(*                       ball x e == ball of center x and radius e            *)
(*            Nbhs_isPseudoMetric == factory to build a topological space     *)
(*                                   from a mixin for a pseudoMetric space    *)
(*                nbhs_ball_ ball == nbhs defined using the given balls       *)
(*                      nbhs_ball == nbhs defined using balls in a            *)
(*                                   pseudometric space                       *)
(*                  discrete_ball == singleton balls for the discrete         *)
(*                                   topology                                 *)
(*         discrete_topology_type == equip choice types with a discrete       *)
(*                                   topology                                 *)
(* ```                                                                        *)
(*                                                                            *)
(* We endow several standard types with the structure of pseudometric space,  *)
(* e.g.:                                                                      *)
(* - products `(U * V)%type`                                                  *)
(* - matrices `'M[T]_(m, n)`                                                  *)
(* - `weak_topology` (the metric space for weak topologies)                   *)
(*                                                                            *)
(* ### Complete uniform spaces                                                *)
(* ```                                                                        *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (entourage definition)                   *)
(*                   completeType == interface type for a complete uniform    *)
(*                                   space structure                          *)
(*                                   The HB class is Complete.                *)
(* ```                                                                        *)
(*                                                                            *)
(* We endow several standard types with the structure of complete uniform     *)
(* space, e.g.:                                                               *)
(* - matrices `'M[T]_(m, n)`                                                  *)
(* - functions `T -> U`                                                       *)
(*                                                                            *)
(* ### Complete pseudometric spaces                                           *)
(* ```                                                                        *)
(*                   cauchy_ex F <-> the set of sets F is a cauchy filter     *)
(*                                   (epsilon-delta definition)               *)
(*                 cauchy_ball F <-> the set of sets F is a cauchy filter     *)
(*                                   (using the near notations)               *)
(*       completePseudoMetricType == interface type for a complete            *)
(*                                   pseudometric space structure             *)
(*                                   The HB class is CompletePseudoMetric.    *)
(*                        ball_ N == balls defined by the norm/absolute       *)
(*                                   value N                                  *)
(* ```                                                                        *)
(*                                                                            *)
(* We endow several standard types with the structure of complete             *)
(* pseudometric space, e.g.:                                                  *)
(* - matrices `'M[T]_(m, n)`                                                  *)
(* - functions `T -> U`                                                       *)
(*                                                                            *)
(* We endow `numFieldType` with the types of topological notions              *)
(* (accessible with `Import numFieldTopology.Exports.`)                       *)
(*                                                                            *)
(* ```                                                                        *)
(*                 dense S == the set (S : set T) is dense in T, with T of    *)
(*                            type topologicalType                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ### Subspaces of topological spaces                                        *)
(* ```                                                                        *)
(*              subspace A == for (A : set T), this is a copy of T with a     *)
(*                            topology that ignores points outside A          *)
(*         incl_subspace x == with x of type subspace A with (A : set T),     *)
(*                            inclusion of subspace A into T                  *)
(*          join_product f == the function (x => f ^~ x)                      *)
(*                            When the family f separates points from closed  *)
(*                            sets, join_product is an embedding.             *)
(*            singletons T := [set [set x] | x in [set: T]]                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "A ^°" (at level 1, format "A ^°").
Reserved Notation "[ 'locally' P ]" (at level 0, format "[ 'locally'  P ]").
Reserved Notation "x ^'" (at level 2, format "x ^'").
Reserved Notation "{ 'within' A , 'continuous' f }"
  (at level 70, A at level 69, format "{ 'within'  A ,  'continuous'  f }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Making sure that [Program] does not automatically introduce *)
Obligation Tactic := idtac.

Import Order.TTheory GRing.Theory Num.Theory.
From mathcomp Require Import mathcomp_extra.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
HB.instance Definition _ := gen_eqMixin {linear U -> V | s}.
HB.instance Definition _ := gen_choiceMixin {linear U -> V | s}.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : GRing.Scale.law R V).
HB.instance Definition _ :=
  isPointed.Build {linear U -> V | GRing.Scale.Law.sort s} \0.
End Linear2.

(** Topological spaces *)
HB.mixin Record Nbhs_isTopological (T : Type) of Nbhs T := {
  open : set_system T;
  nbhs_pfilter_subproof : forall p : T, ProperFilter (nbhs p) ;
  nbhsE_subproof : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE_subproof : open = [set A : set T | A `<=` nbhs^~ A ]
}.

#[short(type="topologicalType")]
HB.structure Definition Topological :=
  {T of Nbhs T & Nbhs_isTopological T}.

#[short(type="ptopologicalType")]
HB.structure Definition PointedTopological :=
  {T of PointedNbhs T & Nbhs_isTopological T}.

Section Topological1.

Context {T : topologicalType}.

Definition open_nbhs (p : T) (A : set T) := open A /\ A p.

Definition basis (B : set (set T)) :=
  B `<=` open /\ forall x, filter_from [set U | B U /\ U x] id --> x.

Definition second_countable := exists2 B, countable B & basis B.

Global Instance nbhs_pfilter (p : T) : ProperFilter (nbhs p).
Proof. by apply: nbhs_pfilter_subproof; case: T p => ? []. Qed.
Typeclasses Opaque nbhs.
Lemma nbhs_filter (p : T) : Filter (nbhs p).
Proof. exact: (@nbhs_pfilter). Qed.

Canonical nbhs_filter_on (x : T) := FilterType (nbhs x) (@nbhs_filter x).

Lemma nbhsE (p : T) :
  nbhs p = [set A : set T | exists2 B : set T, open_nbhs p B & B `<=` A].
Proof.
have -> : nbhs p = [set A : set T | exists B, [/\ open B, B p & B `<=` A] ].
  exact: nbhsE_subproof.
by rewrite predeqE => A; split=> [[B [?]]|[B[]]]; exists B.
Qed.

Lemma open_nbhsE (p : T) (A : set T) : open_nbhs p A = (open A /\ nbhs p A).
Proof.
by rewrite nbhsE propeqE; split=> [[? ?]|[? [B [? ?] BA]]]; split => //;
  [exists A | exact: BA].
Qed.

Definition interior (A : set T) := (@nbhs _ T)^~ A.

Local Notation "A ^°" := (interior A).

Lemma interior_subset (A : set T) : A^° `<=` A.
Proof.
by move=> p; rewrite /interior nbhsE => -[? [? ?]]; apply.
Qed.

Lemma openE : open = [set A : set T | A `<=` A^°].
Proof. exact: openE_subproof. Qed.

Lemma nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Proof. by rewrite nbhsE => - [? [_ ?]]; apply. Qed.

Lemma nbhs_interior (p : T) (A : set T) : nbhs p A -> nbhs p A^°.
Proof.
rewrite nbhsE /open_nbhs openE => - [B [Bop Bp] sBA].
by exists B => // q Bq; apply: filterS sBA _; apply: Bop.
Qed.

Lemma open0 : open (set0 : set T).
Proof. by rewrite openE. Qed.

Lemma openT : open (setT : set T).
Proof. by rewrite openE => ??; apply: filterT. Qed.

Lemma openI (A B : set T) : open A -> open B -> open (A `&` B).
Proof.
rewrite openE => Aop Bop p [Ap Bp].
by apply: filterI; [apply: Aop|apply: Bop].
Qed.

Lemma bigcup_open (I : Type) (D : set I) (f : I -> set T) :
  (forall i, D i -> open (f i)) -> open (\bigcup_(i in D) f i).
Proof.
rewrite openE => fop p [i Di].
by have /fop fiop := Di; move/fiop; apply: filterS => ??; exists i.
Qed.

Lemma openU (A B : set T) : open A -> open B -> open (A `|` B).
Proof.
by rewrite openE => Aop Bop p [/Aop|/Bop]; apply: filterS => ??; [left|right].
Qed.

Lemma open_subsetE (A B : set T) : open A -> (A `<=` B) = (A `<=` B^°).
Proof.
rewrite openE => Aop; rewrite propeqE; split.
  by move=> sAB p Ap; apply: filterS sAB _; apply: Aop.
by move=> sAB p /sAB /interior_subset.
Qed.

Lemma open_interior (A : set T) : open A^°.
Proof.
rewrite openE => p; rewrite /interior nbhsE => - [B [Bop Bp]].
by rewrite open_subsetE //; exists B.
Qed.

Lemma interior_bigcup I (D : set I) (f : I -> set T) :
  \bigcup_(i in D) (f i)^° `<=` (\bigcup_(i in D) f i)^°.
Proof.
move=> p [i Di]; rewrite /interior nbhsE => - [B [Bop Bp] sBfi].
by exists B => // ? /sBfi; exists i.
Qed.

Lemma open_nbhsT (p : T) : open_nbhs p setT.
Proof. by split=> //; apply: openT. Qed.

Lemma open_nbhsI (p : T) (A B : set T) :
  open_nbhs p A -> open_nbhs p B -> open_nbhs p (A `&` B).
Proof. by move=> [Aop Ap] [Bop Bp]; split; [apply: openI|split]. Qed.

Lemma open_nbhs_nbhs (p : T) (A : set T) : open_nbhs p A -> nbhs p A.
Proof. by rewrite nbhsE => p_A; exists A. Qed.

Lemma interiorI (A B:set T): (A `&` B)^° = A^° `&` B^°.
Proof.
rewrite /interior predeqE => //= x; rewrite nbhsE; split => [[B0 ?] | []].
- by rewrite subsetI => // -[? ?]; split; exists B0.
- by move=> -[B0 ? ?] [B1 ? ?]; exists (B0 `&` B1);
  [exact: open_nbhsI | rewrite subsetI; split; apply: subIset; [left|right]].
Qed.

End Topological1.

Lemma open_in_nearW {T : topologicalType} (P : T -> Prop) (S : set T) :
  open S -> {in S, forall x, P x} -> {in S, forall x, \near x, P x}.
Proof.
by move=> oS SP z /set_mem Sz; apply: in_nearW SP => //=; exact: open_nbhs_nbhs.
Qed.

#[global] Hint Extern 0 (Filter (nbhs _)) =>
  solve [apply: nbhs_filter] : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter (nbhs _)) =>
  solve [apply: nbhs_pfilter] : typeclass_instances.

Global Instance alias_nbhs_filter {T : topologicalType} x :
  @Filter T^o (@nbhs T^o T x).
Proof. apply: @nbhs_filter T x. Qed.

Global Instance alias_nbhs_pfilter {T : topologicalType} x :
  @ProperFilter T^o (@nbhs T^o T x).
Proof. exact: @nbhs_pfilter T x. Qed.

Notation "A ^°" := (interior A) : classical_set_scope.

Lemma continuousP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, open A -> open (f @^-1` A).
Proof.
split=> fcont; first by rewrite !openE => A Aop ? /Aop /fcont.
move=> s A; rewrite nbhs_simpl /= !nbhsE => - [B [Bop Bfs] sBA].
by exists (f @^-1` B); [split=> //; apply/fcont|move=> ? /sBA].
Qed.

Lemma continuous_comp (R S T : topologicalType) (f : R -> S) (g : S -> T) x :
  {for x, continuous f} -> {for (f x), continuous g} ->
  {for x, continuous (g \o f)}.
Proof. exact: cvg_comp. Qed.

Lemma open_comp  {T U : topologicalType} (f : T -> U) (D : set U) :
  {in f @^-1` D, continuous f} -> open D -> open (f @^-1` D).
Proof.
rewrite !openE => fcont Dop x /= Dfx.
by apply: fcont; [rewrite inE|apply: Dop].
Qed.

Lemma cvg_fmap {T: topologicalType} {U : topologicalType}
  (F : set_system T) x (f : T -> U) :
   {for x, continuous f} -> F --> x -> f @ F --> f x.
Proof. by move=> cf fx P /cf /fx. Qed.

Lemma near_join (T : topologicalType) (x : T) (P : set T) :
  (\near x, P x) -> \near x, \near x, P x.
Proof. exact: nbhs_interior. Qed.

Lemma near_bind (T : topologicalType) (P Q : set T) (x : T) :
  (\near x, (\near x, P x) -> Q x) -> (\near x, P x) -> \near x, Q x.
Proof.
move=> PQ xP; near=> y; apply: (near PQ y) => //;
by apply: (near (near_join xP) y).
Unshelve. all: by end_near. Qed.

(* limit composition *)

Lemma continuous_cvg {T : Type} {V U : topologicalType}
  (F : set_system T) (FF : Filter F)
  (f : T -> V) (h : V -> U) (a : V) :
  {for a, continuous h} ->
  f @ F --> a -> (h \o f) @ F --> h a.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ h _ _ _ fa).
Qed.

Lemma continuous_is_cvg {T : Type} {V U : ptopologicalType} [F : set_system T]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma continuous2_cvg {T : Type} {V W U : topologicalType}
  (F : set_system T) (FF : Filter F)
  (f : T -> V) (g : T -> W) (h : V -> W -> U) (a : V) (b : W) :
  h z.1 z.2 @[z --> (a, b)] --> h a b ->
  f @ F --> a -> g @ F --> b -> (fun x => h (f x) (g x)) @ F --> h a b.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ (fun x => h x.1 x.2) _ _ _ (cvg_pair fa fb)).
Qed.

Lemma cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set_system T) {FF : Filter F} :
  (\forall x \near F, f x = l) -> f @ F --> l.
Proof.
move=> fFl P /=; rewrite !near_simpl => Pl.
by apply: filterS fFl => _ ->; apply: nbhs_singleton.
Qed.
Arguments cvg_near_cst {T U} l {f F FF}.

Lemma is_cvg_near_cst (T : Type) (U : ptopologicalType)
  (l : U) (f : T -> U) (F : set_system T) {FF : Filter F} :
  (\forall x \near F, f x = l) -> cvg (f @ F).
Proof. by move=> /cvg_near_cst/cvgP. Qed.
Arguments is_cvg_near_cst {T U} l {f F FF}.

Lemma near_cst_continuous (T U : topologicalType)
  (l : U) (f : T -> U) (x : T) :
  (\forall y \near x, f y = l) -> {for x, continuous f}.
Proof.
move=> eq_f_l; apply: cvg_near_cst; apply: filterS (eq_f_l) => y ->.
by rewrite (nbhs_singleton eq_f_l).
Qed.
Arguments near_cst_continuous {T U} l [f x].

Lemma cvg_cst (U : topologicalType) (x : U) (T : Type)
    (F : set_system T) {FF : Filter F} :
  (fun _ : T => x) @ F --> x.
Proof. by apply: cvg_near_cst; near=> x0. Unshelve. all: by end_near. Qed.
Arguments cvg_cst {U} x {T F FF}.
#[global] Hint Resolve cvg_cst : core.

Lemma is_cvg_cst (U : ptopologicalType) (x : U) (T : Type)
  (F : set_system T) {FF : Filter F} :
  cvg ((fun _ : T => x) @ F).
Proof. by apply: cvgP; apply: cvg_cst. Qed.
Arguments is_cvg_cst {U} x {T F FF}.
#[global] Hint Resolve is_cvg_cst : core.

Lemma cst_continuous {T U : topologicalType} (x : U) :
  continuous (fun _ : T => x).
Proof. by move=> t; apply: cvg_cst. Qed.

Section within_topologicalType.
Context {T : topologicalType} (A : set T).
Implicit Types B : set T.

(* Relation between  globally  and  within A (nbhs x)          *)
(* to be combined with lemmas such as boundedP in normedtype.v *)
Lemma within_nbhsW (x : T) : A x -> within A (nbhs x) `=>` globally A.
Proof.
move=> Ax P AP; rewrite /within/=; near=> y; apply: AP.
Unshelve. all: by end_near. Qed.

(* [locally P] replaces a (globally A) in P by a within A (nbhs x)      *)
(* Can be combined with a notation taking a filter as its last argument *)
Definition locally_of (P : set_system T -> Prop) of phantom Prop (P (globally A))
  := forall x, A x -> P (within A (nbhs x)).
Local Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).
(* e.g. [locally [bounded f x | x in A]]                  *)
(* see lemmas bounded_locally in normedtype.v for example *)

Lemma within_interior (x : T) : A^° x -> within A (nbhs x) = nbhs x.
Proof.
move=> Aox; rewrite eqEsubset; split; last exact: cvg_within.
rewrite ?nbhsE => W /= => [[B + BsubW]].
rewrite open_nbhsE => [[oB nbhsB]].
exists (B `&` A^°); last by move=> t /= [] /BsubW + /interior_subset; apply.
rewrite open_nbhsE; split; first by apply: openI => //; exact: open_interior.
by apply: filterI => //; move:(open_interior A); rewrite openE; exact.
Qed.

Lemma within_subset B F : Filter F -> A `<=` B -> within A F `=>` within B F.
Proof.
move=> FF AsubB W; rewrite /within/=; apply: filter_app; rewrite nbhs_simpl.
by apply: filterE => ? + ?; apply; exact: AsubB.
Qed.

Lemma withinE F : Filter F ->
  within A F = [set U | exists2 V, F V & U `&` A = V `&` A].
Proof.
move=> FF; rewrite eqEsubset; split=> U.
  move=> Wu; exists [set x | A x -> U x] => //.
  by rewrite eqEsubset; split => t [L R]; split=> //; apply: L.
move=> [V FV AU]; rewrite /within /prop_near1 nbhs_simpl/=; near=> w => Aw.
by have []// : (U `&` A) w; rewrite AU; split => //; apply: (near FV).
Unshelve. all: by end_near. Qed.

Lemma fmap_within_eq {S : topologicalType} (F : set_system T) (f g : T -> S) :
  Filter F -> {in A, f =1 g} -> f @ within A F --> g @ within A F.
Proof.
move=> FF feq U /=; near_simpl; apply: filter_app.
rewrite ?nbhs_simpl; near_simpl; near=> w; rewrite (feq w) // inE.
exact: (near (withinT A FF) w).
Unshelve. all: by end_near. Qed.

End within_topologicalType.

Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).

(** Topology defined by a filter *)

HB.factory Record Nbhs_isNbhsTopological T of Nbhs T := {
  nbhs_filter : forall p : T, ProperFilter (nbhs p);
  nbhs_singleton : forall (p : T) (A : set T), nbhs p A -> A p;
  nbhs_nbhs : forall (p : T) (A : set T), nbhs p A -> nbhs p (nbhs^~ A);
}.

HB.builders Context T of Nbhs_isNbhsTopological T.

Definition open_of_nbhs := [set A : set T | A `<=` nbhs^~ A].

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ open_of_nbhs B, B p & B `<=` A] ].
Proof.
rewrite predeqE => A; split=> [p_A|]; last first.
  move=> [B [Bop Bp sBA]]; apply: filterS sBA _; last exact: Bop.
  exact/nbhs_filter.
exists (nbhs^~ A); split=> //; first by move=> ?; apply: nbhs_nbhs.
by move=> q /nbhs_singleton.
Qed.

Let openE_subproof : open_of_nbhs = [set A : set T | A `<=` nbhs^~ A].
Proof. by []. Qed.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_filter nbhsE_subproof openE_subproof.

HB.end.

(** Topology defined by open sets *)

Definition nbhs_of_open (T : Type) (op : set T -> Prop) (p : T) (A : set T) :=
  exists B, [/\ op B, B p & B `<=` A].

HB.factory Record isOpenTopological T of Choice T := {
  op : set T -> Prop;
  opT : op setT;
  opI : forall (A B : set T), op A -> op B -> op (A `&` B);
  op_bigU : forall (I : Type) (f : I -> set T), (forall i, op (f i)) ->
    op (\bigcup_i f i);
}.

HB.builders Context T of isOpenTopological T.

HB.instance Definition _ := hasNbhs.Build T (nbhs_of_open op).

Let nbhs_pfilter_subproof (p : T) : ProperFilter (nbhs p).
Proof.
apply: Build_ProperFilter_ex.
  by move=> A [B [_ Bp sBA]]; exists p; apply: sBA.
split; first by exists setT; split=> [|//|//]; exact: opT.
  move=> A B [C [Cop Cp sCA]] [D [Dop Dp sDB]].
  exists (C `&` D); split=> //; first exact: opI.
  by move=> q [/sCA Aq /sDB Bq].
move=> A B sAB [C [Cop p_C sCA]].
by exists C; split=> //; apply: subset_trans sAB.
Qed.

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ op B, B p & B `<=` A] ].
Proof. by []. Qed.

Let openE_subproof : op = [set A : set T | A `<=` nbhs^~ A].
Proof.
rewrite predeqE => A; split=> [Aop p Ap|Aop].
  by exists A; split=> //; split.
suff -> : A = \bigcup_(B : {B : set T & op B /\ B `<=` A}) projT1 B.
  by apply: op_bigU => B; have [] := projT2 B.
rewrite predeqE => p; split=> [|[B _ Bp]]; last by have [_] := projT2 B; apply.
by move=> /Aop [B [Bop Bp sBA]]; exists (existT _ B (conj Bop sBA)).
Qed.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_pfilter_subproof nbhsE_subproof openE_subproof.

HB.end.

(** Topology defined by a base of open sets *)

HB.factory Record isBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
  b_cover : \bigcup_(i in D) b i = setT;
  b_join : forall i j t, D i -> D j -> b i t -> b j t ->
    exists k, [/\ D k, b k t & b k `<=` b i `&` b j];
}.

HB.builders Context T of isBaseTopological T.

Definition open_from := [set \bigcup_(i in D') b i | D' in subset^~ D].

Let open_fromT : open_from setT.
Proof. exists D => //; exact: b_cover. Qed.

Let open_fromI (A B : set T) : open_from A -> open_from B ->
  open_from (A `&` B).
Proof.
move=> [DA sDAD AeUbA] [DB sDBD BeUbB].
have ABU : forall t, (A `&` B) t ->
  exists it, D it /\ b it t /\ b it `<=` A `&` B.
  move=> t [At Bt].
  have [iA [DiA [biAt sbiA]]] : exists i, D i /\ b i t /\ b i `<=` A.
    move: At; rewrite -AeUbA => - [i DAi bit]; exists i.
    by split; [apply: sDAD|split=> // ?; exists i].
  have [iB [DiB [biBt sbiB]]] : exists i, D i /\ b i t /\ b i `<=` B.
    move: Bt; rewrite -BeUbB => - [i DBi bit]; exists i.
    by split; [apply: sDBD|split=> // ?; exists i].
  have [i [Di bit sbiAB]] := b_join DiA DiB biAt biBt.
  by exists i; split=> //; split=> // s /sbiAB [/sbiA ? /sbiB].
set Dt := fun t => [set it | D it /\ b it t /\ b it `<=` A `&` B].
exists [set get (Dt t) | t in A `&` B].
  by move=> _ [t ABt <-]; have /ABU/getPex [] := ABt.
rewrite predeqE => t; split=> [[_ [s ABs <-] bDtst]|ABt].
  by have /ABU/getPex [_ [_]] := ABs; apply.
by exists (get (Dt t)); [exists t| have /ABU/getPex [? []]:= ABt].
Qed.

Let open_from_bigU (I0 : Type) (f : I0 -> set T) :
  (forall i, open_from (f i)) -> open_from (\bigcup_i f i).
Proof.
set fop := fun j => [set Dj | Dj `<=` D /\ f j = \bigcup_(i in Dj) b i].
exists (\bigcup_j get (fop j)).
  move=> i [j _ fopji].
  suff /getPex [/(_ _ fopji)] : exists Dj, fop j Dj by [].
  by have [Dj] := H j; exists Dj.
rewrite predeqE => t; split=> [[i [j _ fopji bit]]|[j _]].
  exists j => //; suff /getPex [_ ->] : exists Dj, fop j Dj by exists i.
  by have [Dj] := H j; exists Dj.
have /getPex [_ ->] : exists Dj, fop j Dj by have [Dj] := H j; exists Dj.
by move=> [i]; exists i => //; exists j.
Qed.

HB.instance Definition _ := isOpenTopological.Build T
  open_fromT open_fromI open_from_bigU.

HB.end.

HB.factory Record isSubBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
}.

HB.builders Context T of isSubBaseTopological T.

Local Notation finI_from := (finI_from D b).

Let finI_from_cover : \bigcup_(A in finI_from) A = setT.
Proof.
rewrite predeqE => t; split=> // _; exists setT => //.
by exists fset0 => //; rewrite predeqE.
Qed.

Let finI_from_join A B t : finI_from A -> finI_from B -> A t -> B t ->
  exists k, [/\ finI_from k, k t & k `<=` A `&` B].
Proof.
move=> [DA sDAD AeIbA] [DB sDBD BeIbB] At Bt.
exists (A `&` B); split => //.
exists (DA `|` DB)%fset; first by move=> i /fsetUP [/sDAD|/sDBD].
rewrite predeqE => s; split=> [Ifs|[As Bs] i /fsetUP].
  split; first by rewrite -AeIbA => i DAi; apply: Ifs; rewrite /= inE DAi.
  by rewrite -BeIbB => i DBi; apply: Ifs; rewrite /= inE DBi orbC.
by move=> [DAi|DBi];
  [have := As; rewrite -AeIbA; apply|have := Bs; rewrite -BeIbB; apply].
Qed.

HB.instance Definition _ := isBaseTopological.Build T
  finI_from_cover finI_from_join.

HB.end.

(** Topology on nat *)

Section nat_topologicalType.

Let D : set nat := setT.
Let b : nat -> set nat := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite predeqE => i; split => // _; exists i. Qed.

Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof. by move=> i j t _ _ -> ->; exists j. Qed.

HB.instance Definition _ := isBaseTopological.Build nat bT bD.

End nat_topologicalType.

Lemma nbhs_infty_gt N : \forall n \near \oo, (N < n)%N.
Proof. by exists N.+1. Qed.
#[global] Hint Resolve nbhs_infty_gt : core.

Lemma nbhs_infty_ge N : \forall n \near \oo, (N <= n)%N.
Proof. by exists N. Qed.

Lemma nbhs_infty_ger {R : realType} (r : R) :
  \forall n \near \oo, (r <= n%:R)%R.
Proof.
exists `|Num.ceil r|%N => // n /=; rewrite -(ler_nat R); apply: le_trans.
by rewrite (le_trans (ceil_ge _))// natr_absz ler_int ler_norm.
Qed.

Lemma cvg_addnl N : addn N @ \oo --> \oo.
Proof.
by move=> P [n _ Pn]; exists (n - N)%N => // m; rewrite /= leq_subLR => /Pn.
Qed.

Lemma cvg_addnr N : addn^~ N @ \oo --> \oo.
Proof. by under [addn^~ N]funext => n do rewrite addnC; apply: cvg_addnl. Qed.

Lemma cvg_subnr N : subn^~ N @ \oo --> \oo.
Proof.
move=> P [n _ Pn]; exists (N + n)%N => //= m le_m.
by apply: Pn; rewrite /= leq_subRL// (leq_trans _ le_m)// leq_addr.
Qed.

Lemma cvg_mulnl N : (N > 0)%N -> muln N @ \oo --> \oo.
Proof.
case: N => N // _ P [n _ Pn]; exists (n %/ N.+1).+1 => // m.
by rewrite /= ltn_divLR// => n_lt; apply: Pn; rewrite mulnC /= ltnW.
Qed.

Lemma cvg_mulnr N :(N > 0)%N -> muln^~ N @ \oo --> \oo.
Proof.
by move=> N_gt0; under [muln^~ N]funext => n do rewrite mulnC; apply: cvg_mulnl.
Qed.

Lemma cvg_divnr N : (N > 0)%N -> divn^~ N @ \oo --> \oo.
Proof.
move=> N_gt0 P [n _ Pn]; exists (n * N)%N => //= m.
by rewrite /= -leq_divRL//; apply: Pn.
Qed.

Lemma near_inftyS (P : set nat) :
  (\forall x \near \oo, P (S x)) -> (\forall x \near \oo, P x).
Proof. case=> N _ NPS; exists (S N) => // [[]]; rewrite /= ?ltn0 //. Qed.

Section infty_nat.
Local Open Scope nat_scope.

Let cvgnyP {F : set_system nat} {FF : Filter F} : [<->
(* 0 *) F --> \oo;
(* 1 *) forall A, \forall x \near F, A <= x;
(* 2 *) forall A, \forall x \near F, A < x;
(* 3 *) \forall A \near \oo, \forall x \near F, A < x;
(* 4 *) \forall A \near \oo, \forall x \near F, A <= x ].
Proof.
tfae; first by move=> Foo A; apply: Foo; apply: nbhs_infty_ge.
- move=> AF A; near \oo => B; near=> x.
  suff : (B <= x)%N by apply: leq_trans; near: B; apply: nbhs_infty_gt.
  by near: x; apply: AF; near: B.
- by move=> Foo; near do apply: Foo.
- by apply: filterS => ?; apply: filterS => ?; apply: ltnW.
case=> [A _ AF] P [n _ Pn]; near \oo => B; near=> m; apply: Pn => /=.
suff: (B <= m)%N by apply: leq_trans; near: B; apply: nbhs_infty_ge.
by near: m; apply: AF; near: B; apply: nbhs_infty_ge.
Unshelve. all: end_near. Qed.

Section map.

Context {I : Type} {F : set_system I} {FF : Filter F} (f : I -> nat).

Lemma cvgnyPge :
  f @ F --> \oo <-> forall A, \forall x \near F, A <= f x.
Proof. exact: (cvgnyP 0%N 1%N). Qed.

Lemma cvgnyPgt :
  f @ F --> \oo <-> forall A, \forall x \near F, A < f x.
Proof. exact: (cvgnyP 0%N 2%N). Qed.

Lemma cvgnyPgty :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A < f x.
Proof. exact: (cvgnyP 0%N 3%N). Qed.

Lemma cvgnyPgey :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A <= f x.
Proof. exact: (cvgnyP 0%N 4%N). Qed.

End map.

End infty_nat.

(** Topology on the product of two spaces *)

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

(** Topology on matrices *)

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

(** Weak topology by a function *)

Definition weak_topology {S : Type} {T : Type}
  (f : S -> T) : Type := S.

Section Weak_Topology.
Variable (S : choiceType) (T : topologicalType) (f : S -> T).
Local Notation W := (weak_topology f).

Definition wopen := [set f @^-1` A | A in open].

Lemma wopT : wopen [set: W].
Proof. by exists setT => //; apply: openT. Qed.

Lemma wopI (A B : set W) : wopen A -> wopen B -> wopen (A `&` B).
Proof.
by move=> [C Cop <-] [D Dop <-]; exists (C `&` D) => //; apply: openI.
Qed.

Lemma wop_bigU (I : Type) (g : I -> set W) :
  (forall i, wopen (g i)) -> wopen (\bigcup_i g i).
Proof.
move=> gop.
set opi := fun i => [set Ui | open Ui /\ g i = f @^-1` Ui].
exists (\bigcup_i get (opi i)).
  apply: bigcup_open => i.
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
have g_preim i : g i = f @^-1` (get (opi i)).
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
rewrite predeqE => s; split=> [[i _]|[i _]]; last by rewrite g_preim; exists i.
by rewrite -[_ _]/((f @^-1` _) _) -g_preim; exists i.
Qed.

HB.instance Definition _ := Choice.on W.
HB.instance Definition _ :=
  isOpenTopological.Build W wopT wopI wop_bigU.

Lemma weak_continuous : continuous (f : W -> T).
Proof. by apply/continuousP => A ?; exists A. Qed.

Lemma cvg_image (F : set_system S) (s : S) :
  Filter F -> f @` setT = setT ->
  F --> (s : W) <-> ([set f @` A | A in F] : set_system _) --> f s.
Proof.
move=> FF fsurj; split=> [cvFs|cvfFfs].
  move=> A /weak_continuous [B [Bop Bs sBAf]].
  have /cvFs FB : nbhs (s : W) B by apply: open_nbhs_nbhs.
  rewrite nbhs_simpl; exists (f @^-1` A); first exact: filterS FB.
  exact: image_preimage.
move=> A /= [_ [[B Bop <-] Bfs sBfA]].
have /cvfFfs [C FC fCeB] : nbhs (f s) B by rewrite nbhsE; exists B.
rewrite nbhs_filterE; apply: filterS FC.
by apply: subset_trans sBfA; rewrite -fCeB; apply: preimage_image.
Qed.

End Weak_Topology.

HB.instance Definition _ (S : pointedType) (T : topologicalType) (f : S -> T) :=
  Pointed.on (weak_topology f).

(** Supremum of a family of topologies *)

Definition sup_topology {T : Type} {I : Type}
  (Tc : I -> Topological T) : Type := T.

Section Sup_Topology.
Variable (T : choiceType) (I : Type) (Tc : I -> Topological T).
Local Notation S := (sup_topology Tc).

Let TS := fun i => Topological.Pack (Tc i).

Definition sup_subbase := \bigcup_i (@open (TS i) : set_system T).

HB.instance Definition _ := Choice.on S.
HB.instance Definition _ := isSubBaseTopological.Build S sup_subbase id.

Lemma cvg_sup (F : set_system T) (t : T) :
  Filter F -> F --> (t : S) <-> forall i, F --> (t : TS i).
Proof.
move=> Ffilt; split=> cvFt.
  move=> i A /=; rewrite (@nbhsE (TS i)) => - [B [Bop Bt] sBA].
  apply: cvFt; exists B; split=> //; exists [set B]; last first.
    by rewrite predeqE => ?; split=> [[_ ->]|] //; exists B.
  move=> _ ->; exists [fset B]%fset.
    by move=> ?; rewrite inE inE => /eqP->; exists i.
  by rewrite predeqE=> ?; split=> [|??]; [apply|]; rewrite /= inE // =>/eqP->.
move=> A /=; rewrite (@nbhsE [the topologicalType of S]).
move=> [_ [[B sB <-] [C BC Ct] sUBA]].
rewrite nbhs_filterE; apply: filterS sUBA _; apply: (@filterS _ _ _ C).
  by move=> ? ?; exists C.
have /sB [D sD IDeC] := BC; rewrite -IDeC; apply: filter_bigI => E DE.
have /sD := DE; rewrite inE => - [i _]; rewrite openE => Eop.
by apply: (cvFt i); apply: Eop; move: Ct; rewrite -IDeC => /(_ _ DE).
Qed.

End Sup_Topology.

HB.instance Definition _ (I : Type) (T : pointedType) (f : I -> Topological T) :=
  Pointed.on (sup_topology f).

(** deleted neighborhood *)

Definition dnbhs {T : topologicalType} (x : T) :=
  within (fun y => y != x) (nbhs x).
Notation "x ^'" := (dnbhs x) : classical_set_scope.

Lemma nbhs_dnbhs_neq {T : topologicalType} (p : T) :
  \forall x \near nbhs p^', x != p.
Proof. exact: withinT. Qed.

Lemma dnbhsE (T : topologicalType) (x : T) : nbhs x = x^' `&` at_point x.
Proof.
rewrite predeqE => A; split=> [x_A|[x_A Ax]].
  split; last exact: nbhs_singleton.
  move: x_A; rewrite nbhsE => -[B [oB x_B sBA]]; rewrite /dnbhs nbhsE.
  by exists B => // ? /sBA.
move: x_A; rewrite /dnbhs !nbhsE => -[B [oB x_B sBA]]; exists B => //.
by move=> y /sBA Ay; case: (eqVneq y x) => [->|].
Qed.

Global Instance dnbhs_filter {T : topologicalType} (x : T) : Filter x^'.
Proof. exact: within_filter. Qed.
#[global] Typeclasses Opaque dnbhs.

Canonical dnbhs_filter_on (T : topologicalType)  (x : T) :=
  FilterType x^' (dnbhs_filter _).

Lemma cvg_fmap2 (T U : Type) (f : T -> U):
  forall (F G : set_system T), G `=>` F -> f @ G `=>` f @ F.
Proof. by move=> F G H A fFA ; exact: H (preimage f A) fFA. Qed.

Lemma cvg_within_filter {T U} {f : T -> U} (F : set_system T) {FF : (Filter F) }
  (G : set_system U) : forall (D : set T), (f @ F) --> G -> (f @ within D F) --> G.
Proof. move=> ?;  exact: cvg_trans (cvg_fmap2 (cvg_within _)). Qed.

Lemma cvg_app_within {T} {U : ptopologicalType} (f : T -> U) (F : set_system T)
  (D : set T): Filter F -> cvg (f @ F) -> cvg (f @ within D F).
Proof. by move => FF /cvg_ex [l H]; apply/cvg_ex; exists l; exact: cvg_within_filter. Qed.

Lemma nbhs_dnbhs {T : topologicalType} (x : T) : x^' `=>` nbhs x.
Proof. exact: cvg_within. Qed.

(** meets *)

Lemma meets_openr {T : topologicalType} (F : set_system T) (x : T) :
  F `#` nbhs x = F `#` open_nbhs x.
Proof.
rewrite propeqE; split; [exact/meetsSr/open_nbhs_nbhs|].
by move=> P A B {}/P P; rewrite nbhsE => -[B' /P + sB]; apply: subsetI_neq0.
Qed.

Lemma meets_openl {T : topologicalType} (F : set_system T) (x : T) :
  nbhs x `#` F = open_nbhs x `#` F.
Proof. by rewrite meetsC meets_openr meetsC. Qed.
(** Closed sets in topological spaces *)

Section Closed.

Context {T : topologicalType}.

Definition closure (A : set T) :=
  [set p : T | forall B, nbhs p B -> A `&` B !=set0].

Lemma closure0 : closure set0 = set0 :> set T.
Proof.
rewrite predeqE => x; split => // /(_ _ (filter_nbhsT _))/set0P.
by rewrite set0I eqxx.
Qed.

Lemma closureEnbhs A : closure A = [set p | globally A `#` nbhs p].
Proof. by under eq_fun do rewrite meets_globallyl. Qed.

Lemma closureEonbhs A : closure A = [set p | globally A `#` open_nbhs p].
Proof. by under eq_fun do rewrite -meets_openr meets_globallyl. Qed.

Lemma subset_closure (A : set T) : A `<=` closure A.
Proof. by move=> p ??; exists p; split=> //; apply: nbhs_singleton. Qed.

Lemma closure_eq0 (A : set T) : closure A = set0 -> A = set0.
Proof.
by move=> A0; apply/seteqP; split => //; rewrite -A0; exact: subset_closure.
Qed.

Lemma closureI (A B : set T) : closure (A `&` B) `<=` closure A `&` closure B.
Proof. by move=> p clABp; split=> ? /clABp [q [[]]]; exists q. Qed.

Definition limit_point E := [set t : T |
  forall U, nbhs t U -> exists y, [/\ y != t, E y & U y]].

Lemma limit_pointEnbhs E :
  limit_point E = [set p | globally (E `\ p) `#` nbhs p].
Proof.
under eq_fun do rewrite meets_globallyl; rewrite funeqE => p /=.
apply/eq_forall2 => x px; apply/eq_exists => y.
by rewrite propeqE; split => [[/eqP ? ?]|[[? /eqP ?]]]; do 2?split.
Qed.

Lemma limit_pointEonbhs E :
  limit_point E = [set p | globally (E `\ p) `#` open_nbhs p].
Proof. by rewrite limit_pointEnbhs; under eq_fun do rewrite meets_openr. Qed.

Lemma subset_limit_point E : limit_point E `<=` closure E.
Proof. by move=> t Et U tU; have [p [? ? ?]] := Et _ tU; exists p. Qed.

Lemma closure_limit_point E : closure E = E `|` limit_point E.
Proof.
rewrite predeqE => t; split => [cEt|]; last first.
  by case; [exact: subset_closure|exact: subset_limit_point].
have [?|Et] := pselect (E t); [by left|right=> U tU; have [p []] := cEt _ tU].
by exists p; split => //; apply/eqP => pt; apply: Et; rewrite -pt.
Qed.

Definition closed (D : set T) := closure D `<=` D.

Lemma open_closedC (D : set T) : open D -> closed (~` D).
Proof. by rewrite openE => Dop p clNDp /Dop /clNDp [? []]. Qed.

Lemma closed_bigI {I} (D : set I) (f : I -> set T) :
  (forall i, D i -> closed (f i)) -> closed (\bigcap_(i in D) f i).
Proof.
move=> fcl t clft i Di; have /fcl := Di; apply.
by move=> A /clft [s [/(_ i Di)]]; exists s.
Qed.

Lemma closedI (D E : set T) : closed D -> closed E -> closed (D `&` E).
Proof.
by move=> Dcl Ecl p clDEp; split; [apply: Dcl|apply: Ecl];
  move=> A /clDEp [q [[]]]; exists q.
Qed.

Lemma closedT : closed setT. Proof. by []. Qed.

Lemma closed0 : closed set0.
Proof. by move=> ? /(_ setT) [|? []] //; apply: filterT. Qed.

Lemma closedE : closed = [set A : set T | forall p, ~ (\near p, ~ A p) -> A p].
Proof.
rewrite predeqE => A; split=> Acl p; last first.
  by move=> clAp; apply: Acl; rewrite -nbhs_nearE => /clAp [? []].
rewrite -nbhs_nearE nbhsE => /asboolP.
rewrite asbool_neg => /forallp_asboolPn2 clAp.
apply: Acl => B; rewrite nbhsE => - [C [oC pC]].
have /asboolP := clAp C.
rewrite asbool_or 2!asbool_neg => /orP[/asboolP/not_andP[]//|/existsp_asboolPn [q]].
move/asboolP; rewrite asbool_neg => /imply_asboolPn[+ /contrapT Aq sCB] => /sCB.
by exists q.
Qed.

Lemma closed_openC (D : set T) : closed D -> open (~` D).
Proof.
rewrite closedE openE => Dcl t nDt; apply: contrapT.
by rewrite /interior nbhs_nearE => /Dcl.
Qed.

Lemma closedC (D : set T) : closed (~` D) = open D.
Proof.
by apply/propext; split=> [/closed_openC|]; [rewrite setCK|exact: open_closedC].
Qed.

Lemma openC (D : set T) : open (~`D) = closed (D).
Proof. by rewrite -closedC setCK. Qed.

Lemma closed_closure (A : set T) : closed (closure A).
Proof. by move=> p clclAp B /nbhs_interior /clclAp [q [clAq /clAq]]. Qed.

End Closed.

Lemma closed_comp {T U : topologicalType} (f : T -> U) (D : set U) :
  {in ~` f @^-1` D, continuous f} -> closed D -> closed (f @^-1` D).
Proof.
rewrite !closedE=> f_continuous D_cl x /= xDf.
apply: D_cl; apply: contra_not xDf => fxD.
have NDfx : ~ D (f x).
  by move: fxD; rewrite -nbhs_nearE nbhsE => - [A [? ?]]; apply.
by apply: f_continuous fxD; rewrite inE.
Qed.

Lemma closed_cvg {T} {V : topologicalType} {F} {FF : ProperFilter F}
    (u_ : T -> V) (A : V -> Prop) :
    (* BUG: elim does not see this as an elimination principle if A : set V *)
    closed A -> (\forall n \near F, A (u_ n)) ->
  forall l, u_ @ F --> l -> A l.
Proof.
move=> + FAu_ l u_Fl; apply => B /u_Fl /=; rewrite nbhs_filterE.
by move=> /(filterI FAu_) => /filter_ex[t [Au_t u_Bt]]; exists (u_ t).
Qed.
Arguments closed_cvg {T V F FF u_} _ _ _ _ _.

Lemma continuous_closedP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, closed A -> closed (f @^-1` A).
Proof.
rewrite continuousP; split=> ctsf ? ?.
  by rewrite -openC preimage_setC; apply: ctsf; rewrite openC.
by rewrite -closedC preimage_setC; apply: ctsf; rewrite closedC.
Qed.

Lemma closedU (T : topologicalType) (D E : set T) :
  closed D -> closed E -> closed (D `|` E).
Proof. by rewrite -?openC setCU; exact: openI. Qed.

Lemma closed_bigsetU (T : topologicalType) (I : eqType) (s : seq I)
    (F : I -> set T) : (forall x, x \in s -> closed (F x)) ->
  closed (\big[setU/set0]_(x <- s) F x).
Proof.
move=> scF; rewrite big_seq.
by elim/big_ind : _ => //; [exact: closed0|exact: closedU].
Qed.

Lemma closed_bigcup (T : topologicalType) (I : choiceType) (A : set I)
    (F : I -> set T) :
    finite_set A -> (forall i, A i -> closed (F i)) ->
  closed (\bigcup_(i in A) F i).
Proof.
move=> finA cF; rewrite -bigsetU_fset_set//; apply: closed_bigsetU => i.
by rewrite in_fset_set// inE; exact: cF.
Qed.

Section closure_lemmas.
Variable T : topologicalType.
Implicit Types E A B U : set T.

Lemma closure_subset A B : A `<=` B -> closure A `<=` closure B.
Proof. by move=> ? ? CAx ?; move/CAx; exact/subsetI_neq0. Qed.

Lemma closureE A : closure A = smallest closed A.
Proof.
rewrite eqEsubset; split=> [x ? B [cB AB]|]; first exact/cB/(closure_subset AB).
exact: (smallest_sub (@closed_closure _ _) (@subset_closure _ _)).
Qed.

Lemma closureC E :
  ~` closure E = \bigcup_(x in [set U | open U /\ U `<=` ~` E]) x.
Proof.
rewrite closureE setC_bigcap eqEsubset; split => t [U [? EU Ut]].
  by exists (~` U) => //; split; [exact: closed_openC|exact: subsetC].
by rewrite -(setCK E); exists (~` U)=> //; split; [exact:open_closedC|exact:subsetC].
Qed.

Lemma closure_id E : closed E <-> E = closure E.
Proof.
split=> [?|->]; last exact: closed_closure.
rewrite eqEsubset; split => //; exact: subset_closure.
Qed.

End closure_lemmas.

(** Compact sets *)

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

Section ClopenSets.
Implicit Type T : topologicalType.

Definition clopen {T} (A : set T) := open A /\ closed A.

Lemma clopenI {T} (A B : set T) : clopen A -> clopen B -> clopen (A `&` B).
Proof. by case=> ? ? [] ? ?; split; [exact: openI | exact: closedI]. Qed.

Lemma clopenU {T} (A B : set T) : clopen A -> clopen B -> clopen (A `|` B).
Proof. by case=> ? ? [] ? ?; split; [exact: openU | exact: closedU]. Qed.

Lemma clopenC {T} (A B : set T) : clopen A -> clopen (~`A).
Proof. by case=> ? ?; split;[exact: closed_openC | exact: open_closedC ]. Qed.

Lemma clopen0 {T} : @clopen T set0.
Proof. by split; [exact: open0 | exact: closed0]. Qed.

Lemma clopenT {T} : clopen [set: T].
Proof. by split; [exact: openT | exact: closedT]. Qed.

Lemma clopen_comp {T U : topologicalType} (f : T -> U) (A : set U) :
 clopen A -> continuous f -> clopen (f @^-1` A).
Proof. by case=> ? ?; split; [ exact: open_comp | exact: closed_comp]. Qed.

End ClopenSets.

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

Section connected_sets.
Variable T : topologicalType.
Implicit Types A B C D : set T.

Definition connected A :=
  forall B, B !=set0 -> (exists2 C, open C & B = A `&` C) ->
  (exists2 C, closed C & B = A `&` C) -> B = A.

Lemma connected0 : connected (@set0 T).
Proof. by move=> ? ? [? ?]; rewrite set0I. Qed.

Definition separated A B :=
  (closure A) `&` B = set0 /\ A `&` (closure B) = set0.

Lemma separatedC A B : separated A B = separated B A.
Proof. by rewrite /separated andC setIC (setIC _ B). Qed.

Lemma separated_disjoint A B : separated A B -> A `&` B = set0.
Proof.
move=> AB; rewrite predeqE => x; split => // -[Ax Bx].
by move: AB; rewrite /separated => -[<- _]; split => //; apply: subset_closure.
Qed.

Lemma connectedPn A : ~ connected A <->
  exists E : bool -> set T, [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Proof.
rewrite -propeqE; apply: notLR; rewrite propeqE.
split=> [conE [E [E0 EU [E1 E2]]]|conE B B0 [C oC BAC] [D cD BAD]].
  suff : E true = A.
    move/esym/(congr1 (setD^~ (closure (E true)))); rewrite EU setDUl.
    have := @subset_closure _ (E true); rewrite -setD_eq0 => ->; rewrite setU0.
    by move/setDidPl : E2 => ->; exact/eqP/set0P.
  apply: (conE _ (E0 true)).
  - exists (~` (closure (E false))); first exact/closed_openC/closed_closure.
    rewrite EU setIUl.
    have /subsets_disjoint -> := @subset_closure _ (E false); rewrite set0U.
    by apply/esym/setIidPl/disjoints_subset; rewrite setIC.
  - exists (closure (E true)); first exact: closed_closure.
    by rewrite EU setIUl E2 set0U; exact/esym/setIidPl/subset_closure.
apply: contrapT => AF; apply: conE.
exists (fun i => if i is false then A `\` C else A `&` C); split.
- case=> /=; first by rewrite -BAC.
  apply/set0P/eqP => /disjoints_subset; rewrite setCK => EC.
  by apply: AF; rewrite BAC; exact/setIidPl.
- by rewrite setDE -setIUr setUCl setIT.
- split.
  + rewrite setIC; apply/disjoints_subset; rewrite closureC => x [? ?].
    by exists C => //; split=> //; rewrite setDE setCI setCK; right.
  + apply/disjoints_subset => y -[Ay Cy].
    rewrite -BAC BAD => /closureI[_]; move/closure_id : cD => <- Dy.
    by have : B y; [by rewrite BAD; split|rewrite BAC => -[]].
Qed.

Lemma connectedP A : connected A <->
  forall E : bool -> set T, ~ [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Proof.
rewrite -propeqE forallNE; apply: notRL; rewrite propeqE; exact: connectedPn.
Qed.

Lemma connected_subset A B C : separated A B -> C `<=` A `|` B ->
  connected C -> C `<=` A \/ C `<=` B.
Proof.
move=> AB CAB; have -> : C = (C `&` A) `|` (C `&` B).
  rewrite predeqE => x; split=> [Cx|[] [] //].
  by have [Ax|Bx] := CAB _ Cx; [left|right].
move/connectedP/(_ (fun b => if b then C `&` B else C `&` A)) => /not_and3P[]//.
  by move/existsNP => [b /set0P/negP/negPn]; case: b => /eqP ->;
    rewrite !(setU0,set0U); [left|right]; apply: subIset; right.
case/not_andP => /eqP/set0P[x []].
- move=> /closureI[cCx cAx] [Cx Bx]; exfalso.
  by move: AB; rewrite /separated => -[] + _; apply/eqP/set0P; exists x.
- move=> [Cx Ax] /closureI[cCx cBx]; exfalso.
  by move: AB; rewrite /separated => -[] _; apply/eqP/set0P; exists x.
Qed.

Lemma connected1 x : connected [set x].
Proof.
move=> X [y +] [O Oopen XO] [C Cclosed XC]; rewrite XO.
by move=> [{y}-> Ox]; apply/seteqP; split=> y => [[->//]|->].
Qed.
Hint Resolve connected1 : core.

Lemma bigcup_connected I (A : I -> set T) (P : I -> Prop) :
  \bigcap_(i in P) (A i) !=set0 -> (forall i, P i -> connected (A i)) ->
  connected (\bigcup_(i in P) (A i)).
Proof.
move=> [c AIc] cA; have [[i Pi]|] := pselect (exists i, P i); last first.
  move/forallNP => P0.
  rewrite (_ : P = set0) ?bigcup_set0; first exact: connected0.
  by rewrite predeqE => x; split => //; exact: P0.
apply/connectedP => [E [E0 EU sE]].
wlog E0c : E E0 EU sE / E false c.
  move=> G; have : (\bigcup_(i in P) A i) c by exists i => //; exact: AIc.
  rewrite EU => -[E0c|E1c]; first exact: G.
  by apply: (G (E \o negb)) => //;
    [case => /=|rewrite EU setUC|rewrite separatedC].
move: (E0 true) => /set0P/eqP; apply.
have [/eqP //|/set0P[d E1d]] := boolP (E true == set0).
have : \bigcup_(i in P) A i `<=` E false.
  suff AE : forall i, P i -> A i `<=` E false by move=> x [j ? ?]; exact: (AE j).
  move=> j Pj.
  move: (@connected_subset _ _ (A j) sE).
  rewrite -EU => /(_ (bigcup_sup _) (cA _ Pj)) [//| | AjE1]; first exact.
  exfalso; have E1c := AjE1 _ (AIc _ Pj).
  by move/separated_disjoint : sE; apply/eqP/set0P; exists c.
rewrite EU subUset => -[_] /(_ _ E1d) E0d; exfalso.
by move/separated_disjoint : sE; apply/eqP/set0P; exists d.
Qed.

Lemma connectedU A B : A `&` B !=set0 -> connected A -> connected B ->
  connected (A `|` B).
Proof.
move=> [x [Ax Bx]] Ac Bc; rewrite -bigcup2inE; apply: bigcup_connected.
  by exists x => //= -[|[|[]]].
by move=> [|[|[]]].
Qed.

Lemma connected_closure A : connected A -> connected (closure A).
Proof.
move=> ctdA U U0 [C1 oC1 C1E] [C2 cC2 C2E]; rewrite eqEsubset C2E; split => //.
suff : A `<=` U.
  move/closure_subset; rewrite [_ `&` _](iffLR (closure_id _)) ?C2E//.
  by apply: closedI => //; exact: closed_closure.
rewrite -setIidPl; apply: ctdA.
- move: U0; rewrite C1E => -[z [clAx C1z]]; have [] := clAx C1.
    exact: open_nbhs_nbhs.
  by move=> w [Aw C1w]; exists w; rewrite setIA (setIidl (@subset_closure _ _)).
- by exists C1 => //; rewrite C1E setIA (setIidl (@subset_closure _ _)).
- by exists C2 => //; rewrite C2E setIA (setIidl (@subset_closure _ _)).
Qed.

Definition connected_component (A : set T) (x : T) :=
  \bigcup_(A in [set C : set T | [/\ C x, C `<=` A & connected C]]) A.

Lemma component_connected A x : connected (connected_component A x).
Proof. by apply: bigcup_connected; [exists x => C []|move=> C []]. Qed.

Lemma connected_component_sub A x : connected_component A x `<=` A.
Proof. by move=> y [B [_ + _]] => /[apply]. Qed.

Lemma connected_component_id A x :
  A x -> connected A -> connected_component A x = A.
Proof.
move=> Ax Ac; apply/seteqP; split; first exact: connected_component_sub.
by move=> y Ay; exists A => //; split.
Qed.

Lemma connected_component_out A x :
  ~ A x -> connected_component A x = set0.
Proof. by move=> NAx; rewrite -subset0 => y [B [/[swap]/[apply]]]. Qed.

Lemma connected_component_max A B x : B x -> B `<=` A ->
  connected B -> B `<=` connected_component A x.
Proof. by move=> Bx BA Bc y By; exists B. Qed.

Lemma connected_component_refl A x : A x -> connected_component A x x.
Proof. by move=> Ax; exists [set x] => //; split => // _ ->. Qed.

Lemma connected_component_cover A :
  \bigcup_(A in connected_component A @` A) A = A.
Proof.
apply/predeqP => x; split=> [[B [y By <- /connected_component_sub//]]|Ax].
by exists (connected_component A x) => //; apply: connected_component_refl.
Qed.

Lemma connected_component_sym A x y :
  connected_component A x y -> connected_component A y x.
Proof. by move=> [B [*]]; exists B. Qed.

Lemma connected_component_trans A y x z :
    connected_component A x y -> connected_component A y z ->
  connected_component A x z.
Proof.
move=> [B [Bx BA Ac Ay]] [C [Cy CA Cc Cz]]; exists (B `|` C); last by right.
by split; [left | rewrite subUset | apply: connectedU=> //; exists y].
Qed.

Lemma same_connected_component A x y : connected_component A x y ->
  connected_component A x = connected_component A y.
Proof.
move=> Axy; apply/seteqP; split => z; apply: connected_component_trans => //.
by apply: connected_component_sym.
Qed.

Lemma component_closed A x : closed A -> closed (connected_component A x).
Proof.
move=> clA; have [Ax|Ax] := pselect (A x); first last.
  by rewrite connected_component_out //; exact: closed0.
rewrite closure_id eqEsubset; split; first exact: subset_closure.
move=> z Axz; exists (closure (connected_component A x)) => //.
split; first exact/subset_closure/connected_component_refl.
  rewrite [X in _ `<=` X](closure_id A).1//.
  by apply: closure_subset; exact: connected_component_sub.
by apply: connected_closure; exact: component_connected.
Qed.

Lemma clopen_separatedP A : clopen A <-> separated A (~` A).
Proof.
split=> [[oA cA]|[] /[!(@disjoints_subset T)] /[!(@setCK T)] clAA AclA].
  rewrite /separated -((closure_id A).1 cA) setICr ; split => //.
  by rewrite -((closure_id _).1 (open_closedC oA)) setICr.
split; last by rewrite closure_id eqEsubset; split => //; exact: subset_closure.
by rewrite -closedC closure_id eqEsubset; split;
  [exact: subset_closure|exact: subsetCr].
Qed.

End connected_sets.
Arguments connected {T}.
Arguments connected_component {T}.

Section DiscreteTopology.
Section DiscreteMixin.
Context {X : Type}.

Lemma discrete_sing (p : X) (A : set X) : principal_filter p A -> A p.
Proof. by move=> /principal_filterP. Qed.

Lemma discrete_nbhs (p : X) (A : set X) :
  principal_filter p A -> principal_filter p (principal_filter^~ A).
Proof. by move=> ?; exact/principal_filterP. Qed.

End DiscreteMixin.

Definition discrete_space (X : nbhsType) := @nbhs X _ = @principal_filter X.

Context {X : topologicalType} {dsc : discrete_space X}.

Lemma discrete_open (A : set X) : open A.
Proof.
by rewrite openE => ? ?; rewrite /interior dsc; exact/principal_filterP.
Qed.

Lemma discrete_set1 (x : X) : nbhs x [set x].
Proof. by apply: open_nbhs_nbhs; split => //; exact: discrete_open. Qed.

Lemma discrete_closed (A : set X) : closed A.
Proof. by rewrite -[A]setCK closedC; exact: discrete_open. Qed.

Lemma discrete_cvg (F : set_system X) (x : X) :
  Filter F -> F --> x <-> F [set x].
Proof.
rewrite dsc nbhs_simpl; split; first by exact.
by move=> Fx U /principal_filterP ?; apply: filterS Fx => ? ->.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build bool
  principal_filter_proper discrete_sing discrete_nbhs.

End DiscreteTopology.

Lemma discrete_bool : discrete_space bool.
Proof. by []. Qed.

Lemma bool_compact : compact [set: bool].
Proof. by rewrite setT_bool; apply/compactU; exact: compact_set1. Qed.

Lemma discrete_nat : discrete_space nat.
Proof.
rewrite /discrete_space predeq2E => n U; split.
   by case => /= V [_ Vn VU]; exact/principal_filterP/VU.
move/principal_filterP => Un; exists U; split => //=; exists U => //.
by rewrite eqEsubset; split => [z [i Ui ->//]|z Uz]; exists z.
Qed.

#[global] Hint Resolve discrete_bool : core.

(** TODO: generalize this to a preOrder once that's available *)
HB.mixin Record Order_isNbhs d (T : Type) of Nbhs T & Order.Total d T := {
  (** Note that just the intervals `]a, b[ doesn't work when the order has a
      top or bottom element, so we also need the rays `]-oo, b[ and ]a, +oo[ *)
  itv_nbhsE : forall x : T, nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i])
}.

#[short(type="orderNbhsType")]
HB.structure Definition OrderNbhs d :=
  { T of Nbhs T & Order.Total d T & Order_isNbhs d T }.

#[short(type="orderTopologicalType")]
HB.structure Definition OrderTopological d :=
  { T of Topological T & Order.Total d T & Order_isNbhs d T }.

Section order_topologies.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Context {d} {T : orderTopologicalType d}.
Implicit Types x y : T.

Lemma rray_open x : open `]x, +oo[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists `]x, +oo[%O => //; split => //; left.
Qed.
Hint Resolve rray_open : core.

Lemma lray_open x : open `]-oo, x[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists (`]-oo, x[)%O => //; split => //; left.
Qed.
Hint Resolve lray_open : core.

Lemma itv_open x y : open `]x, y[.
Proof. by rewrite set_itv_splitI /=; apply: openI. Qed.
Hint Resolve itv_open : core.

Lemma itv_open_ends_open (i : interval T) : itv_open_ends i -> open [set` i].
Proof.
case: i; rewrite /itv_open_ends => [[[]t1|[]]] [[]t2|[]] []? => //.
by rewrite set_itvE; exact: openT.
Qed.

Lemma rray_closed x : closed `[x, +oo[.
Proof. by rewrite -setCitvl closedC. Qed.
Hint Resolve rray_closed : core.

Lemma lray_closed x : closed `]-oo, x].
Proof. by rewrite -setCitvr closedC. Qed.
Hint Resolve lray_closed : core.

Lemma itv_closed x y : closed `[x, y].
Proof. by rewrite set_itv_splitI; apply: closedI => /=. Qed.
Hint Resolve itv_closed : core.

Lemma itv_closure x y : closure `]x, y[ `<=` `[x, y].
Proof.
rewrite closureE => r; apply; split => //.
by apply: subset_itvScc => /=; rewrite bnd_simp.
Qed.

Lemma itv_closed_infimums (A : set T) : A !=set0 -> closed A ->
  infimums A `<=` A.
Proof.
move=> [a0 Aa0] + l [loL] hiL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q []]].
have [E|E] := eqVneq ([set` Interval (BSide true l) q] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: q E.
- move=> b q /[swap] /itv_open_ends_rside -> E lpq ; suff : lbound A q.
    move/hiL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`[l, q[ `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[|//].
  by rewrite ltNge (loL _ Aa).
- move=> b _ /itv_open_ends_rinfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundlr /= => /andP[pl _]; apply/andP.
  by split => //; exact/(le_trans pl)/loL.
Qed.

Lemma itv_closed_supremums (A : set T) : A !=set0 -> closed A ->
  supremums A `<=` A.
Proof.
move=> [a0 Aa0] + l [upL] lbL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q[]]].
have [E|E] := eqVneq ([set` Interval p (BSide false l)] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: p E.
- move=> b p /[swap] /itv_open_ends_lside -> E lpq ; suff : ubound A p.
    move/lbL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`]p, l] `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[//|].
  by rewrite ltNge (upL _ Aa).
- move=> b _ /itv_open_ends_linfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundrl /= => /andP[_ pl]; apply/andP.
  by split => //; exact/(le_trans _ pl)/upL.
Qed.

Let sub_open_mem x (U : set T) (i : interval T) :=
  [/\ [set` i] `<=` U, open [set` i] & x \in i].

Lemma clopen_bigcup_clopen x (U : set T) : clopen U -> U x ->
  clopen (\bigcup_(i in sub_open_mem x U) [set` i]).
Proof.
pose I := \bigcup_(i in sub_open_mem x U) [set` i].
move=> clU Ux; split; first by apply: bigcup_open => ? [].
have cIV : closure I `<=` U.
  rewrite closureE => z /(_ U); apply; split; first by case: clU.
  by move=> ? [? [+ _ _]]; exact.
apply/closure_id; rewrite eqEsubset; split; first exact: subset_closure.
move=> z cIi; have Uz : U z by exact: cIV.
case: clU => + _;  rewrite {1}openE => /(_ _ Uz).
rewrite /interior /= itv_nbhsE /= => -[i [/itv_open_ends_open oi iy] siU].
case/(_ [set` i]): cIi; first by move: oi; rewrite openE; exact.
move=> /= w [[j [jU oJ jy jw]]] wi; exists (i `|` j)%O; first last.
  exact/(le_trans iy)/leUl.
split; first by rewrite itv_setU ?{1}subUset //; exists w.
by rewrite itv_setU ?{1}subUset //; [exact: openU | exists w].
exact/(le_trans jy)/leUr.
Qed.

End order_topologies.
Hint Resolve lray_open : core.
Hint Resolve rray_open : core.
Hint Resolve itv_open : core.
Hint Resolve lray_closed : core.
Hint Resolve rray_closed : core.
Hint Resolve itv_closed : core.

Section bool_ord_topology.
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Local Lemma bool_nbhs_itv (b : bool) :
  nbhs b = filter_from
    (fun i => itv_open_ends i /\ b \in i)
    (fun i => [set` i]).
Proof.
rewrite discrete_bool eqEsubset; split=> U; first last.
  by case => V [_ Vb] VU; apply/principal_filterP/VU; apply: Vb.
move/principal_filterP; case: b.
  move=> Ut; exists `]false, +oo[; first split => //; first by left.
  by move=> r /=; rewrite in_itv /=; case: r.
move=> Ut; exists `]-oo, true[; first split => //; first by left.
by move=> r /=; rewrite in_itv /=; case: r.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ bool bool_nbhs_itv.
End bool_ord_topology.

Section nat_ord_topology.
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Local Lemma nat_nbhs_itv (n : nat) :
  nbhs n = filter_from
    (fun i => itv_open_ends i /\ n \in i)
    (fun i => [set` i]).
Proof.
rewrite discrete_nat eqEsubset; split=> U; first last.
  by case => V [_ Vb] VU; apply/principal_filterP/VU; apply: Vb.
move/principal_filterP; case: n.
  move=> U0; exists `]-oo, 1[; first split => //; first by left.
  by move=> r /=; rewrite in_itv /=; case: r.
move=> n USn; exists `]n, n.+2[; first split => //; first by right.
  by rewrite in_itv; apply/andP;split => //=; rewrite /Order.lt //=.
move=> r /=; rewrite in_itv /= => nr2; suff: r = n.+1 by move=> ->.
exact/esym/le_anti.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ nat nat_nbhs_itv.

End nat_ord_topology.

Definition order_topology (T : Type) : Type := T.
Section induced_order_topology.

Context {d} {T : orderType d}.

Local Notation oT := (order_topology T).

HB.instance Definition _ := isPointed.Build (interval T) (`]-oo,+oo[).

HB.instance Definition _ := Order.Total.on oT.
HB.instance Definition _ := @isSubBaseTopological.Build oT
  (interval T) (itv_is_ray) (fun i => [set` i]).

Lemma order_nbhs_itv (x : oT) : nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U; first last.
  case=> /= i [ro xi /filterS]; apply; move: ro => [rayi|].
    exists [set` i]; split => //=.
    exists [set [set` i]]; last by rewrite bigcup_set1.
    move=> A ->; exists (fset1 i); last by rewrite set_fset1 bigcap_set1.
    by move=> ?; rewrite !inE => /eqP ->.
  case: i xi => [][[]l|[]] [[]r|[]] xlr []//=; exists `]l, r[%classic.
  split => //; exists [set `]l, r[%classic]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset `]-oo, r[ ; `]l, +oo[]%fset.
    by move=> ?; rewrite !inE => /orP[] /eqP ->.
  rewrite set_fsetU !set_fset1 bigcap_setU !bigcap_set1.
  by rewrite (@set_itv_splitI _ _ `]l, r[) /= setIC.
case=> ? [[ I Irp] <-] [?] /[dup] /(Irp _) [F rayF <-] IF Fix IU.
pose j := \big[Order.meet/`]-oo, +oo[]_(i <- F) i.
exists j; first split.
- rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//.
  + apply: big_ind; [by left| exact: itv_open_endsI|].
    by move=> i /rayF /set_mem ?; left.
  + by move=> p /=; rewrite !inE/=; exact: andb_id2l.
- pose f (i : interval T) : Prop := x \in i; suff : f j by [].
  rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//=.
  + by apply: big_ind => //=; rewrite /f /= => a ? xa ?; rewrite in_itvI xa.
  + by move=> p /=; rewrite !inE/=; exact: andb_id2l.
- suff -> : [set` j] = \bigcap_(i in [set` F]) [set` i].
    by move=> i Fi; apply: IU; exists (\bigcap_(i in [set` F]) [set` i]).
  rewrite -bigsetI_fset_set ?set_fsetK//.
  pose f (i : interval T) (j : set T) : Prop := [set` i] = j.
  suff : f j (\big[setI/[set: T]]_(i <- F) [set` i]) by [].
  rewrite /j big_mkcond /=; apply: big_ind2; rewrite /f ?set_itvE//.
  by move=> ? ? ? ? <- <-; rewrite itv_setI.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ oT order_nbhs_itv.
End induced_order_topology.

(** for an orderedTopologicalType T, and subtype U
    (order_topology (sub_type U)) `<=` (weak_topology (sub_type U))
    but generally the topologies are not equal!
    Consider `[0,1[ | {2}` as a subset of `[0,3]` for an example
*)
Section weak_order_refine.
Context {d} {X : orderTopologicalType d} {Y : subType X}.

Let OrdU : orderTopologicalType d := order_topology (sub_type Y).
Let WeakU : topologicalType := @weak_topology (sub_type Y) X val.

Lemma open_order_weak (U : set Y) : @open OrdU U -> @open WeakU U.
Proof.
rewrite ?openE /= /interior => + x Ux => /(_ x Ux); rewrite itv_nbhsE /=.
move=> [][][[]l|[]] [[]r|[]][][]//= _ xlr /filterS; apply.
- exists `]l, r[%classic; split => //=; exists `]\val l, \val r[%classic.
    exact: itv_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- exists `]l, +oo[%classic; split => //=; exists `]\val l, +oo[%classic.
    exact: rray_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- exists `]-oo, r[%classic; split => //=; exists `]-oo, \val r[%classic.
    exact: lray_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- by rewrite set_itvE; exact: filterT.
Qed.

End weak_order_refine.

(** Uniform spaces *)

Definition nbhs_ {T T'} (ent : set_system (T * T')) (x : T) :=
  filter_from ent (fun A => xsection A x).

Lemma nbhs_E {T T'} (ent : set_system (T * T')) x :
  nbhs_ ent x = filter_from ent (fun A => xsection A x).
Proof. by []. Qed.

Local Open Scope relation_scope.

HB.mixin Record Nbhs_isUniform_mixin M of Nbhs M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal_subproof :
    forall A, entourage A -> diagonal `<=` A;
  entourage_inv_subproof : forall A, entourage A -> entourage A^-1;
  entourage_split_ex_subproof :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE_subproof : nbhs = nbhs_ entourage;
}.

#[short(type="uniformType")]
HB.structure Definition Uniform :=
  {T of Topological T & Nbhs_isUniform_mixin T}.

#[short(type="puniformType")]
HB.structure Definition PointedUniform :=
  {T of PointedTopological T & Nbhs_isUniform_mixin T}.

#[short(type="orderUniformType")]
HB.structure Definition OrderUniform d :=
  {T of Uniform T & OrderTopological d  T}.

HB.factory Record Nbhs_isUniform M of Nbhs M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE : nbhs = nbhs_ entourage;
}.

Local Close Scope relation_scope.

HB.builders Context M of Nbhs_isUniform M.

Let nbhs_filter (p : M) : ProperFilter (nbhs p).
Proof.
rewrite nbhsE nbhs_E; apply: filter_from_proper; last first.
  by move=> A entA; exists p; apply/mem_set; apply: entourage_diagonal entA _ _.
apply: filter_from_filter.
  by exists setT; exact: @filterT entourage_filter.
move=> A B entA entB; exists (A `&` B); last by rewrite xsectionI.
exact: (@filterI _ _ entourage_filter).
Qed.

Let nbhs_singleton (p : M) A : nbhs p A -> A p.
Proof.
rewrite nbhsE nbhs_E  => - [B entB sBpA].
by apply/sBpA/mem_set; exact: entourage_diagonal entB _ _.
Qed.

Let nbhs_nbhs (p : M) A : nbhs p A -> nbhs p (nbhs^~ A).
Proof.
rewrite nbhsE nbhs_E => - [B entB sBpA].
have /entourage_split_ex[C entC sC2B] := entB.
exists C => // q Cpq; rewrite nbhs_E; exists C => // r Cqr.
by apply/sBpA/mem_set/sC2B; exists q; exact/set_mem.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build M
  nbhs_filter nbhs_singleton nbhs_nbhs.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build M
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex nbhsE.

HB.end.

Local Open Scope relation_scope.

HB.factory Record isUniform M of Choice M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
}.

Local Close Scope relation_scope.

HB.builders Context M of isUniform M.

HB.instance Definition _ := @hasNbhs.Build M (nbhs_ entourage).

HB.instance Definition _ := @Nbhs_isUniform.Build M entourage
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex erefl.

HB.end.

Lemma nbhs_entourageE {M : uniformType} : nbhs_ (@entourage M) = nbhs.
Proof. by rewrite -Nbhs_isUniform_mixin.nbhsE_subproof. Qed.

Lemma entourage_sym {X Y : Type} E (x : X) (y : Y) :
  E (x, y) <-> (E ^-1)%relation (y, x).
Proof. by []. Qed.

Lemma filter_from_entourageE {M : uniformType} x :
  filter_from (@entourage M) (fun A => xsection A x) = nbhs x.
Proof. by rewrite -nbhs_entourageE. Qed.

Module Export NbhsEntourage.
Definition nbhs_simpl :=
  (nbhs_simpl,@filter_from_entourageE,@nbhs_entourageE).
End NbhsEntourage.

Lemma nbhsP {M : uniformType} (x : M) P : nbhs x P <-> nbhs_ entourage x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma filter_inv {T : Type} (F : set (set (T * T))) :
  Filter F -> Filter [set V^-1 | V in F]%relation.
Proof.
move=> FF; split => /=.
- by exists [set: T * T] => //; exact: filterT.
- by move=> P Q [R FR <-] [S FS <-]; exists (R `&` S) => //; exact: filterI.
- move=> P Q PQ [R FR RP]; exists Q^-1%relation => //; first last.
    by rewrite eqEsubset; split; case.
  by apply: filterS FR; case=> ? ? /= ?; apply: PQ; rewrite -RP.
Qed.

Section uniformType1.
Local Open Scope relation_scope.
Context {M : uniformType}.

Lemma entourage_refl (A : set (M * M)) x : entourage A -> A (x, x).
Proof. by move=> entA; exact: entourage_diagonal_subproof entA _ _. Qed.

Global Instance entourage_filter' : Filter (@entourage M).
Proof.
exact: entourage_filter.
Qed.

Lemma entourageT : entourage [set: M * M].
Proof. exact: filterT. Qed.

Lemma entourage_inv (A : set (M * M)) : entourage A -> entourage A^-1.
Proof. exact: entourage_inv_subproof. Qed.

Lemma entourage_split_ex (A : set (M * M)) :
  entourage A -> exists2 B, entourage B & B \; B `<=` A.
Proof. exact: entourage_split_ex_subproof. Qed.

Definition split_ent (A : set (M * M)) :=
  get (entourage `&` [set B | B \; B `<=` A]).

Lemma split_entP (A : set (M * M)) : entourage A ->
  entourage (split_ent A) /\ split_ent A \; split_ent A `<=` A.
Proof. by move/entourage_split_ex/exists2P/getPex. Qed.

Lemma entourage_split_ent (A : set (M * M)) : entourage A ->
  entourage (split_ent A).
Proof. by move=> /split_entP []. Qed.

Lemma subset_split_ent (A : set (M * M)) : entourage A ->
  split_ent A \; split_ent A `<=` A.
Proof. by move=> /split_entP []. Qed.

Lemma entourage_split (z x y : M) A : entourage A ->
  split_ent A (x, z) -> split_ent A (z, y) -> A (x, y).
Proof. by move=> /subset_split_ent sA ? ?; apply: sA; exists z. Qed.

Lemma nbhs_entourage (x : M) A : entourage A -> nbhs x (xsection A x).
Proof. by move=> ?; apply/nbhsP; exists A. Qed.

Lemma cvg_entourageP F (FF : Filter F) (p : M) :
  F --> p <-> forall A, entourage A -> \forall q \near F, A (p, q).
Proof.
rewrite -filter_fromP [X in filter_from _ X](_ : _ = @xsection M M ^~ p)//.
  by rewrite filter_from_entourageE.
by apply/funext => E; apply/seteqP; split => [|] ? /xsectionP.
Qed.

Lemma cvg_entourage {F} {FF : Filter F} (x : M) :
  F --> x -> forall A, entourage A -> \forall y \near F, A (x, y).
Proof. by move/cvg_entourageP. Qed.

Lemma cvg_app_entourageP T (f : T -> M) F (FF : Filter F) p :
  f @ F --> p <-> forall A, entourage A -> \forall t \near F, A (p, f t).
Proof. exact: cvg_entourageP. Qed.

Lemma entourage_invI (E : set (M * M)) : entourage E -> entourage (E `&` E^-1).
Proof. by move=> ?; apply: filterI; last exact: entourage_inv. Qed.

Lemma split_ent_subset (E : set (M * M)) : entourage E -> split_ent E `<=` E.
Proof.
move=> entE; case=> x y splitxy; apply: subset_split_ent => //; exists y => //.
by apply: entourage_refl; exact: entourage_split_ent.
Qed.

End uniformType1.

Global Instance entourage_pfilter {M : puniformType} : ProperFilter (@entourage M).
Proof.
apply Build_ProperFilter_ex; last exact: entourage_filter.
by move=> A entA; exists (point, point); apply: entourage_refl.
Qed.

#[global]
Hint Extern 0 (entourage (split_ent _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (get _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (_^-1)%relation) => exact: entourage_inv : core.
Arguments entourage_split {M} z {x y A}.
#[global]
Hint Extern 0 (nbhs _ (xsection _ _)) => exact: nbhs_entourage : core.

Lemma ent_closure {M : uniformType} (x : M) E : entourage E ->
  closure (xsection (split_ent E) x) `<=` xsection E x.
Proof.
pose E' := (split_ent E) `&` (split_ent E)^-1%relation.
move=> entE z /(_ (xsection E' z))[].
  by rewrite -nbhs_entourageE; exists E' => //; exact: filterI.
move=> y; rewrite xsectionI => -[/xsectionP xy [_ /xsectionP yz]].
by apply/xsectionP; move: xy yz; exact: entourage_split.
Qed.

Lemma continuous_withinNx {U V : uniformType} (f : U -> V) x :
  {for x, continuous f} <-> f @ x^' --> f x.
Proof.
split=> - cfx P /= fxP.
  by rewrite !near_simpl; apply: cvg_within; apply: cfx.
rewrite !nbhs_nearE !near_map !near_nbhs in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Unshelve. all: by end_near. Qed.

(* This property is primarily useful only for metrizability on uniform spaces *)
Definition countable_uniformity (T : uniformType) :=
  exists R : set_system (T * T), [/\
    countable R,
    R `<=` entourage &
    forall P, entourage P -> exists2 Q, R Q & Q `<=` P].

Lemma countable_uniformityP {T : uniformType} :
  countable_uniformity T <-> exists2 f : nat -> set (T * T),
    (forall A, entourage A -> exists N, f N `<=` A) &
    (forall n, entourage (f n)).
Proof.
split=> [[M []]|[f fsubE entf]].
  move=> /pfcard_geP[-> _ /(_ _ (@entourageT _))[]//|/unsquash f eM Msub].
  exists f; last by move=> n; apply: eM; exact: funS.
  by move=> ? /Msub [Q + ?] => /(@surj _ _ _ _ f)[n _ fQ]; exists n; rewrite fQ.
exists (range f); split; first exact: card_image_le.
  by move=> E [n _] <-; exact: entf.
by move=> E /fsubE [n fnA]; exists (f n) => //; exists n.
Qed.

Lemma open_nbhs_entourage (U : uniformType) (x : U) (A : set (U * U)) :
  entourage A -> open_nbhs x (xsection A x)^°.
Proof.
move=> entA; split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; apply: nbhs_entourage.
Qed.

Definition unif_continuous (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourage --> entourage.

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

(** matrices *)

Section matrix_Uniform.
Local Open Scope relation_scope.
Variables (m n : nat) (T : uniformType).

Implicit Types A : set ('M[T]_(m, n) * 'M[T]_(m, n)).

Definition mx_ent :=
  filter_from
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

(** Functional metric spaces *)

Definition map_pair {S U} (f : S -> U) (x : (S * S)) : (U * U) :=
  (f x.1, f x.2).

Section weak_uniform.
Local Open Scope relation_scope.
Variable (pS : choiceType) (U : uniformType) (f : pS -> U).

Let S := weak_topology f.

Definition weak_ent : set_system (S * S) :=
  filter_from (@entourage U) (fun V => (map_pair f)@^-1` V).

Lemma weak_ent_filter : Filter weak_ent.
Proof.
apply: filter_from_filter; first by exists setT; exact: entourageT.
by move=> P Q ??; (exists (P `&` Q); first exact: filterI) => ?.
Qed.

Lemma weak_ent_refl A : weak_ent A -> diagonal `<=` A.
Proof.
by move=> [B ? sBA] [x y]/diagonalP ->; apply/sBA; exact: entourage_refl.
Qed.

Lemma weak_ent_inv A : weak_ent A -> weak_ent A^-1.
Proof.
move=> [B ? sBA]; exists B^-1; first exact: entourage_inv.
by move=> ??; exact/sBA.
Qed.

Lemma weak_ent_split A : weak_ent A -> exists2 B, weak_ent B & B \; B `<=` A.
Proof.
move=> [B entB sBA]; have : exists C, entourage C /\ C \; C `<=` B.
  exact/exists2P/entourage_split_ex.
case=> C [entC CsubB]; exists ((map_pair f)@^-1` C); first by exists C.
by case=> x y [a ? ?]; apply/sBA/CsubB; exists (f a).
Qed.

Lemma weak_ent_nbhs : nbhs = nbhs_ weak_ent.
Proof.
rewrite predeq2E => x V; split.
  case=> [? [[B  ? <-] ? BsubV]]; have: nbhs (f x) B by apply: open_nbhs_nbhs.
  move=> /nbhsP [W ? WsubB]; exists ((map_pair f) @^-1` W); first by exists W.
  by move=>??; exact/BsubV/WsubB.
case=> W [V' entV' V'subW] /filterS; apply.
have : nbhs (f x) (xsection V' (f x)) by apply/nbhsP; exists V'.
rewrite (@nbhsE U) => [[O [openU Ofx Osub]]].
(exists (f @^-1` O); repeat split => //); first by exists O => //.
by move=> w ?; apply/mem_set; apply: V'subW; apply/set_mem; exact: Osub.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build (weak_topology f) weak_ent
  weak_ent_filter weak_ent_refl weak_ent_inv weak_ent_split weak_ent_nbhs.

End weak_uniform.

HB.instance Definition _ (pS : pointedType) (U : uniformType) (f : pS -> U) :=
  Pointed.on (weak_topology f).


Definition entourage_set (U : uniformType) (A : set ((set U) * (set U))) :=
  exists2 B, entourage B & forall PQ, A PQ -> forall p q,
    PQ.1 p -> PQ.2 q -> B (p,q).
(* HB.instance Definition _ (U : uniformType) := isSource.Build Prop _ U *)
(*   (fun A => nbhs_ (@entourage_set U) A). *)

Section sup_uniform.
Local Open Scope relation_scope.
Variable (T : choiceType) (Ii : Type) (Tc : Ii -> Uniform T).

Let I : choiceType := {classic Ii}.
Let TS := fun i => Uniform.Pack (Tc i).
Notation Tt := (sup_topology Tc).
Let ent_of (p : I * set (T * T)) := `[< @entourage (TS p.1) p.2 >].
Let IEntType := {p : (I * set (T * T)) | ent_of p}.
Let IEnt : choiceType := IEntType.

Local Lemma IEnt_pointT (i : I) : ent_of (i, setT).
Proof. by apply/asboolP; exact: entourageT. Qed.

Definition sup_ent : set_system (T * T) :=
  filter_from (finI_from [set: IEnt] (fun p => (projT1 p).2)) id.

Ltac IEntP := move=> [[ /= + + /[dup] /asboolP]].

Definition sup_ent_filter : Filter sup_ent.
Proof.
case: (pselect (exists t:T, True)).
  case => p _; apply: finI_filter; move=> J JsubEnt /=; exists (p, p).
  by IEntP => i b /= /entourage_refl ? ? _.
move=> empT. 
have TT0 (E : set (T*T)) : E = set0.
  rewrite eqEsubset; split => //=; case=> t ? _; move: empT. 
  by apply: absurd; exists t.
have ent0 : sup_ent set0.
  rewrite -(TT0 setT); exists set0 => //=; exists fset0 => //=.
split.
- rewrite (TT0 setT); exact: ent0.
- by move => P Q ? ?; rewrite (TT0 (P `&` Q)).
- by move=> P Q _ _; rewrite (TT0 Q).
Qed.

Lemma sup_ent_refl A : sup_ent A -> diagonal `<=` A.
Proof.
move=> [B [F ? <-] BA] [? ?]/diagonalP ->; apply/BA.
by IEntP => i w /= /entourage_refl.
Qed.

Lemma sup_ent_inv A : sup_ent A -> sup_ent A^-1.
Proof.
move=> [B [F ? FB] BA]; exists B^-1; last by move=> ?; exact: BA.
have inv : forall ie : IEnt, ent_of ((projT1 ie).1, (projT1 ie).2^-1).
  by IEntP=> ?? /entourage_inv ??; exact/asboolP.
exists [fset (fun x => @exist (I * set (T * T)) _ _ (inv x)) w | w in F]%fset.
  by move=> ? /imfsetP; IEntP => ? ? ? ? ->; exact: in_setT.
rewrite -FB eqEsubset; split; case=> x y + ie.
  by move=> /(_ (exist ent_of _ (inv ie))) + ?; apply; apply/imfsetP; exists ie.
by move=> + /imfsetP [v vW ->]; exact.
Qed.

Lemma sup_ent_split A : sup_ent A -> exists2 B, sup_ent B & B \; B `<=` A.
Proof.
have spt : (forall ie : IEnt, ent_of ((projT1 ie).1,
    (@split_ent (TS (projT1 ie).1) (projT1 ie).2))).
  by case=> [[/= ? ?] /asboolP/entourage_split_ent ?]; exact/asboolP.
pose g : (IEnt -> IEnt) := fun x => exist ent_of _ (spt x).
case => W [F _ <-] sA; exists (\bigcap_(x in [set` F]) (projT1 (g x)).2).
  exists (\bigcap_(ie in [set`F]) (projT1 (g ie)).2) => //.
  exists [fset (g ie) | ie in F]%fset; first by move=> /= ??; exact: in_setT.
  rewrite eqEsubset; split; case=> x y Igxy ie.
    by move => ?; apply/(Igxy (g ie))/imfsetP; exists ie.
  by move=> /imfsetP [?? ->]; exact: Igxy.
case => ?? [z Fxz Fzy]; apply: sA; IEntP=> i e ? ? eF.
apply: ((@entourage_split (TS i)) z) => //.
  exact: (Fxz _ eF).
exact: (Fzy _ eF).
Qed.

Lemma sup_ent_nbhs : @nbhs Tt Tt = nbhs_ sup_ent.
Proof.
rewrite predeq2E => x V; split.
  move=> [/= X [[/= B + <-] [W BW Wx BV]]] => /(_ W BW) [] /=.
  move=> F Fsup Weq; move: Weq Wx BW => <- Fx BF.
  case (pselect ([set: I] = set0)) => [I0 | /eqP/set0P [i0 _]].
    suff -> : V = setT  by exists setT; apply: filterT; exact: sup_ent_filter.
    rewrite -subTset => ??; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /Fsup/set_mem; rewrite /sup_subbase I0 bigcup_set0.
  have f : forall w, {p : IEnt |  w \in F -> xsection ((projT1 p).2) x `<=` w}.
    move=> /= v; apply: cid; case (pselect (v \in F)); first last.
      by move=> ?; exists (exist ent_of _ (IEnt_pointT i0)).
    move=> /[dup] /Fx vx /Fsup/set_mem [i _]; rewrite openE => /(_ x vx).
    by move=> /(@nbhsP (TS i)) [w /asboolP ent ?]; exists (exist _ (i, w) ent).
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2); first last.
    move=> v /= /xsectionP Fgw; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /[dup] ? /Fgw /= /mem_set/(projT2 (f w)); exact.
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2) => //.
  exists [fset (fun i => projT1 (f i)) w | w in F]%fset.
    by move=> u ?; exact: in_setT.
  rewrite eqEsubset; split => y + z.
    by move=>/(_ (projT1 (f z))) => + ?; apply; apply/imfsetP; exists z.
  by move=> Fgy /imfsetP [/= u uF ->]; exact: Fgy.
case=> E [D [/= F FsubEnt <-] FsubE EsubV].
have F_nbhs_x : Filter (nbhs x) by typeclasses eauto.
apply: (filterS EsubV).
pose f : IEnt -> set T := fun w =>
  @interior (TS (projT1 w).1) (xsection (projT1 w).2 x).
exists (\bigcap_(w in [set` F]) f w); repeat split.
- exists [set \bigcap_(w in [set` F]) f w]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset f w | w in F]%fset.
    move=> /= ? /imfsetP [[[/= i w /[dup] /asboolP entw ? Fiw ->]]].
    by apply/mem_set; rewrite /f /=; exists i => //; exact: open_interior.
  by rewrite set_imfset bigcap_image //=.
- by IEntP=> ? ? /open_nbhs_entourage entw ??; apply entw.
- move=> t /= Ifwt.
  by apply/mem_set/FsubE => it /Ifwt/interior_subset => /set_mem.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build Tt sup_ent
   sup_ent_filter sup_ent_refl sup_ent_inv sup_ent_split sup_ent_nbhs.

Lemma countable_sup_ent :
  countable [set: Ii] -> (forall n, countable_uniformity (TS n)) ->
  countable_uniformity Tt.
Proof.
move=> Icnt countable_ent; pose f n := cid (countable_ent n).
pose g (n : Ii) : set (set (T * T)) := projT1 (f n).
have [I0 | /set0P [i0 _]] := eqVneq [set: I] set0.
  exists [set setT]; split; [exact: countable1|move=> A ->; exact: entourageT|].
  move=> P [w [A _]] <- subP; exists setT => //.
  apply: subset_trans subP; apply: sub_bigcap => i _ ? _.
  by suff : [set: I] (projT1 i).1 by rewrite I0.
exists (finI_from (\bigcup_n g n) id); split.
- by apply/finI_from_countable/bigcup_countable => //i _; case: (projT2 (f i)).
- move=> E [A AsubGn AE]; exists E => //.
  have h (w : set (T * T)) : { p : IEnt | w \in A -> w = (projT1 p).2 }.
    apply: cid; have [|] := boolP (w \in A); last first.
      by exists (exist ent_of _ (IEnt_pointT i0)).
    move=> /[dup] /AsubGn /set_mem [n _ gnw] wA.
    suff ent : ent_of (n, w) by exists (exist ent_of (n, w) ent).
    by apply/asboolP; have [_ + _] := projT2 (f n); exact.
  exists [fset sval (h w) | w in A]%fset; first by move=> ?; exact: in_setT.
  rewrite -AE; rewrite eqEsubset; split => t Ia.
    by move=> w Aw; rewrite (svalP (h w) Aw); apply/Ia/imfsetP; exists w.
  case=> [[n w]] p /imfsetP [x /= xA M]; apply: Ia.
  by rewrite (_ : w = x) // (svalP (h x) xA) -M.
- move=> E [w] [ A _ wIA wsubE].
  have ent_Ip (i : IEnt) : @entourage (TS (projT1 i).1) (projT1 i).2.
    by apply/asboolP; exact: (projT2 i).
  pose h (i : IEnt) : {x : set (T * T) | _} := cid2 (and3_rec
    (fun _ _ P => P) (projT2 (f (projT1 i).1)) (projT1 i).2 (ent_Ip i)).
  have ehi (i : IEnt) : ent_of ((projT1 i).1, projT1 (h i)).
    apply/asboolP => /=; have [] := projT2 (h i).
    by have [_ + _ ? ?] := projT2 (f (projT1 i).1); exact.
  pose AH := [fset projT1 (h w) | w in A]%fset.
  exists (\bigcap_(i in [set` AH]) i).
    exists AH => // p /imfsetP [i iA ->]; rewrite inE //.
    by exists (projT1 i).1 => //; have [] := projT2 (h i).
  apply: subset_trans wsubE; rewrite -wIA => ? It i ?.
  by have [?] := projT2 (h i); apply; apply: It; apply/imfsetP; exists i.
Qed.

End sup_uniform.

(** PseudoMetric spaces defined using balls *)

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Lemma entourage_E {R : numDomainType} {T T'} (ball : T -> R -> set T') :
  entourage_ ball =
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).
Proof. by []. Qed.

HB.mixin Record Uniform_isPseudoMetric (R : numDomainType) M of Uniform M := {
  ball : M -> R -> M -> Prop ;
  ball_center_subproof : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym_subproof : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle_subproof :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE_subproof : entourage = entourage_ ball
}.

#[short(type="pseudoMetricType")]
HB.structure Definition PseudoMetric (R : numDomainType) :=
  {T of Uniform T & Uniform_isPseudoMetric R T}.

#[short(type="pseudoPMetricType")]
HB.structure Definition PseudoPointedMetric (R : numDomainType) :=
  {T of Pointed T & Uniform T & Uniform_isPseudoMetric R T}.

#[short(type="orderPseudoMetricType")]
HB.structure Definition OrderPseudoMetric d (R : numDomainType) :=
  {T of PseudoMetric R T & OrderTopological d T}.

Definition discrete_topology T (dsc : discrete_space T) : Type := T.

Section discrete_uniform.

Context {T : nbhsType} {dsc: discrete_space T}.

Definition discrete_ent : set (set (T * T)) :=
  globally (range (fun x => (x, x))).

Program Definition discrete_uniform_mixin :=
  @isUniform.Build (discrete_topology dsc) discrete_ent _ _ _ _.
Next Obligation.
by move=> ? + x x12; apply; exists x.1; rewrite // {2}x12 -surjective_pairing.
Qed.
Next Obligation.
by move=> ? dA x [i _ <-]; apply: dA; exists i.
Qed.
Next Obligation.
move=> ? dA; exists (range (fun x => (x, x))) => //.
by rewrite set_compose_diag => x [i _ <-]; apply: dA; exists i.
Qed.

HB.instance Definition _ := Choice.on (discrete_topology dsc).
HB.instance Definition _ := discrete_uniform_mixin.
End discrete_uniform.

HB.instance Definition _ (P : pnbhsType) (dsc : discrete_space P) :=
  Pointed.on (discrete_topology dsc).

Lemma discrete_bool_compact : compact [set: discrete_topology discrete_bool].
Proof. by rewrite setT_bool; apply/compactU; exact: compact_set1. Qed.

HB.instance Definition _ {T : pnbhsType} {dsc: discrete_space T} :=
  Pointed.on (discrete_topology dsc).

(* was uniformityOfBallMixin *)
HB.factory Record Nbhs_isPseudoMetric (R : numFieldType) M of Nbhs M := {
  ent : set_system (M * M);
  nbhsE : nbhs = nbhs_ ent;
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : ent = entourage_ ball
}.

HB.builders Context R M of Nbhs_isPseudoMetric R M.
Local Open Scope relation_scope.

Let ball_le x : {homo ball x : e1 e2 / e1 <= e2 >-> e1 `<=` e2}.
Proof.
move=> e1 e2 le12 y xe1_y.
move: le12; rewrite le_eqVlt => /orP [/eqP <- //|].
rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: ball_triangle xe1_y.
suff : ball x (PosNum lt12)%:num x by [].
exact: ball_center.
Qed.

Let entourage_filter_subproof : Filter ent.
Proof.
rewrite entourageE; apply: filter_from_filter; first by exists 1 => /=.
move=> _ _ /posnumP[e1] /posnumP[e2]; exists (Num.min e1 e2)%:num => //=.
by rewrite subsetI; split=> ?; apply: ball_le;
   rewrite num_le// ge_min lexx ?orbT.
Qed.

Let ball_sym_subproof A : ent A -> diagonal `<=` A.
Proof.
rewrite entourageE; move=> [e egt0 sbeA] xy xey.
by apply: sbeA; rewrite /= xey; exact: ball_center.
Qed.

Let ball_triangle_subproof A : ent A -> ent A^-1.
Proof.
rewrite entourageE => - [e egt0 sbeA].
by exists e => // xy xye; apply: sbeA; exact: ball_sym.
Qed.

Let entourageE_subproof A : ent A -> exists2 B, ent B & B \; B `<=` A.
Proof.
rewrite entourageE; move=> [_/posnumP[e] sbeA].
exists [set xy | ball xy.1 (e%:num / 2) xy.2].
  by exists (e%:num / 2) => /=.
move=> xy [z xzhe zyhe]; apply: sbeA.
by rewrite [e%:num]splitr; exact: ball_triangle zyhe.
Qed.

HB.instance Definition _ := Nbhs_isUniform.Build M
  entourage_filter_subproof ball_sym_subproof ball_triangle_subproof
  entourageE_subproof nbhsE.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R M
  ball_center ball_sym ball_triangle entourageE.

HB.end.

Lemma entourage_ballE {R : numDomainType} {M : pseudoMetricType R} :
  entourage_ (@ball R M) = entourage.
Proof. by rewrite entourageE_subproof. Qed.

Lemma entourage_from_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @filter_from R _ [set x : R | 0 < x]
    (fun e => [set xy | @ball R M xy.1 e xy.2]) = entourage.
Proof. by rewrite -entourage_ballE. Qed.

Lemma entourage_ball {R : numDomainType} (M : pseudoMetricType R)
  (e : {posnum R}) : entourage [set xy : M * M | ball xy.1 e%:num xy.2].
Proof. by rewrite -entourage_ballE; exists e%:num => /=. Qed.
#[global] Hint Resolve entourage_ball : core.

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition nbhs_ball {R : numDomainType} {M : pseudoMetricType R} :=
  nbhs_ball_ (@ball R M).

Lemma nbhs_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @nbhs_ball R M = nbhs.
Proof.
rewrite predeq2E => x P; rewrite -nbhs_entourageE; split.
  move=> [_/posnumP[e] sbxeP]; exists [set xy | ball xy.1 e%:num xy.2] => //.
  by move=> y /xsectionP/sbxeP.
rewrite -entourage_ballE; move=> [A [e egt0 sbeA] sAP].
by exists e => // ? ?; exact/sAP/xsectionP/sbeA.
Qed.

Lemma filter_from_ballE {R : numDomainType} {M : pseudoMetricType R} x :
  @filter_from R _ [set x : R | 0 < x] (@ball R M x) = nbhs x.
Proof. by rewrite -nbhs_ballE. Qed.

Module Export NbhsBall.
Definition nbhs_simpl := (nbhs_simpl,@filter_from_ballE,@nbhs_ballE).
End NbhsBall.

Lemma nbhs_ballP {R : numDomainType} {M : pseudoMetricType R} (x : M) P :
  nbhs x P <-> nbhs_ball x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma ball_center {R : numDomainType} (M : pseudoMetricType R) (x : M)
  (e : {posnum R}) : ball x e%:num x.
Proof. exact: ball_center_subproof. Qed.
#[global] Hint Resolve ball_center : core.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.

Lemma ballxx (x : M) (e : R) : 0 < e -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: ball_sym_subproof. Qed.

Lemma ball_symE (x y : M) (e : R) : ball x e y = ball y e x.
Proof. by rewrite propeqE; split; exact/ball_sym. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: ball_triangle_subproof. Qed.

Lemma nbhsx_ballx (x : M) (eps : R) : 0 < eps -> nbhs x (ball x eps).
Proof. by move=> e0; apply/nbhs_ballP; exists eps. Qed.

Lemma open_nbhs_ball (x : M) (eps : {posnum R}) : open_nbhs x (ball x eps%:num)^°.
Proof.
split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; exact: nbhsx_ballx.
Qed.

Lemma le_ball (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y. case: comparableP le12 => [lte12 _|//|//|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma near_ball (y : M) (eps : R) : 0 < eps -> \forall y' \near y, ball y eps y'.
Proof. exact: nbhsx_ballx. Qed.

Lemma dnbhs_ball (a : M) (e : R) : (0 < e)%R -> a^' (ball a e `\ a).
Proof.
move: e => _/posnumP[e]; rewrite /dnbhs /within /=; near=> r => ra.
split => //=; last exact/eqP.
by near: r; rewrite near_simpl; exact: near_ball.
Unshelve. all: by end_near. Qed.

Lemma fcvg_ballP {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by rewrite -filter_fromP !nbhs_simpl /=. Qed.

Lemma __deprecated__cvg_ballPpos {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : {posnum R}, \forall y' \near F, ball y eps%:num y'.
Proof.
split => [/fcvg_ballP + eps|pos]; first exact.
by apply/fcvg_ballP=> _/posnumP[eps] //.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use a combination of `cvg_ballP` and `posnumP`")]
Notation cvg_ballPpos := __deprecated__cvg_ballPpos (only parsing).

Lemma fcvg_ball {F} {FF : Filter F} (y : M) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by move/fcvg_ballP. Qed.

Lemma cvg_ballP {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ballP. Qed.

Lemma cvg_ball {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y -> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ball. Qed.

Lemma cvgi_ballP T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Proof.
split=> [Fy _/posnumP[eps] |Fy P] /=; first exact/Fy/nbhsx_ballx.
move=> /nbhs_ballP[_ /posnumP[eps] subP].
rewrite near_simpl near_mapi; near=> x.
have [//|z [fxz yz]] := near (Fy _ (gt0 eps)) x.
by exists z => //; split => //; apply: subP.
Unshelve. all: end_near. Qed.
Definition cvg_toi_locally := @cvgi_ballP.

Lemma cvgi_ball T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/cvgi_ballP. Qed.

End pseudoMetricType_numDomainType.

#[global] Hint Resolve nbhsx_ballx : core.

Global Instance entourage_proper_filter {R : numDomainType}
  {M : pseudoPMetricType R} : ProperFilter (@entourage M).
Proof.
apply: Build_ProperFilter_ex; rewrite -entourage_ballE => A [_/posnumP[e] sbeA].
by exists (point, point); apply: sbeA; apply: ballxx.
Qed.

Arguments nbhsx_ballx {R M} x eps.
Arguments near_ball {R M} y eps.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `cvg_ball`")]
Notation app_cvg_locally := cvg_ball (only parsing).

Section pseudoMetricType_numFieldType.
Context {R : numFieldType} {M : pseudoMetricType R}.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2) z -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -splitr. Qed.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2) x -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

End pseudoMetricType_numFieldType.

Section entourages.
Variable R : numDomainType.

Lemma unif_continuousP (U V : pseudoMetricType R) (f : U -> V) :
  unif_continuous f <->
  forall e, e > 0 -> exists2 d, d > 0 &
    forall x, ball x.1 d x.2 -> ball (f x.1) e (f x.2).
Proof.
have fappF : Filter ((fun xy => (f xy.1, f xy.2)) @ entourage_ ball).
  by rewrite entourage_ballE; apply: fmap_filter.
by rewrite /unif_continuous -!entourage_ballE filter_fromP.
Qed.

End entourages.

Lemma countable_uniformity_metric {R : realType} {T : pseudoMetricType R} :
  countable_uniformity T.
Proof.
apply/countable_uniformityP.
exists (fun n => [set xy : T * T | ball xy.1 n.+1%:R^-1 xy.2]); last first.
  by move=> n; exact: (entourage_ball _ n.+1%:R^-1%:pos).
move=> E; rewrite -entourage_ballE => -[e e0 subE].
exists `|Num.floor e^-1|%N; apply: subset_trans subE => xy; apply: le_ball.
rewrite /= -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0// -natr1.
rewrite natr_absz ger0_norm; last first.
  by rewrite -floor_ge_int ?invr_ge0// ltW.
by rewrite intrD1 ltW// lt_succ_floor.
Qed.

(** Specific pseudoMetric spaces *)

(** matrices *)
Section matrix_PseudoMetric.
Variables (m n : nat) (R : numDomainType) (T : pseudoMetricType R).
Implicit Types (x y : 'M[T]_(m, n)) (e : R).

Definition mx_ball x e y := forall i j, ball (x i j) e (y i j).

Lemma mx_ball_center x e : 0 < e -> mx_ball x e x.
Proof. by move=> ? ? ?; exact: ballxx. Qed.

Lemma mx_ball_sym x y e : mx_ball x e y -> mx_ball y e x.
Proof. by move=> xe_y ? ?; apply/ball_sym/xe_y. Qed.

Lemma mx_ball_triangle x y z e1 e2 :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ??; apply: ball_triangle; [exact: xe1_y|exact: ye2_z].
Qed.

Lemma mx_entourage : entourage = entourage_ mx_ball.
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

Definition quotient_topology (T : Type) (Q : quotType T) : Type := Q.

Section quotients.
Local Open Scope quotient_scope.
Section unpointed.
Context {T : topologicalType} {Q0 : quotType T}.

Local Notation Q := (quotient_topology Q0).

HB.instance Definition _ := Quotient.copy Q Q0.
HB.instance Definition _ := [Sub Q of T by %/].
HB.instance Definition _ := [Choice of Q by <:].

Definition quotient_open U := open (\pi_Q @^-1` U).

Program Definition quotient_topologicalType_mixin :=
  @isOpenTopological.Build Q quotient_open _ _ _.
Next Obligation. by rewrite /quotient_open preimage_setT; exact: openT. Qed.
Next Obligation. by move=> ? ? ? ?; exact: openI. Qed.
Next Obligation. by move=> I f ofi; apply: bigcup_open => i _; exact: ofi. Qed.
HB.instance Definition _ := quotient_topologicalType_mixin.

Lemma pi_continuous : continuous (\pi_Q : T -> Q).
Proof. exact/continuousP. Qed.

Lemma quotient_continuous {Z : topologicalType} (f : Q -> Z) :
  continuous f <-> continuous (f \o \pi_Q).
Proof.
split => /continuousP /= cts; apply/continuousP => A oA; last exact: cts.
by rewrite comp_preimage; move/continuousP: pi_continuous; apply; exact: cts.
Qed.

Lemma repr_comp_continuous (Z : topologicalType) (g : T -> Z) :
  continuous g -> {homo g : a b / \pi_Q a == \pi_Q b :> Q >-> a == b} ->
  continuous (g \o repr : Q -> Z).
Proof.
move=> /continuousP ctsG rgE; apply/continuousP => A oA.
rewrite /open/= /quotient_open (_ : _ @^-1` _ = g @^-1` A); first exact: ctsG.
have greprE x : g (repr (\pi_Q x)) = g x by apply/eqP; rewrite rgE// reprK.
by rewrite eqEsubset; split => x /=; rewrite greprE.
Qed.

End unpointed.

Section pointed.
Context {T : ptopologicalType} {Q0 : quotType T}.
Local Notation Q := (quotient_topology Q0).
HB.instance Definition _ := isPointed.Build Q (\pi_Q point : Q).
End pointed.
End quotients.

Section discrete_pseudoMetric.
Context {R : numDomainType} {T : nbhsType} {dsc : discrete_space T}.

Definition discrete_ball (x : T) (eps : R) y : Prop := x = y.

Lemma discrete_ball_center x (eps : R) : 0 < eps -> discrete_ball x eps x.
Proof. by []. Qed.

Program Definition discrete_pseudometric_mixin :=
  @Uniform_isPseudoMetric.Build R (discrete_topology dsc) discrete_ball
    _ _ _ _.
Next Obligation. by done. Qed.
Next Obligation. by move=> ? ? ? ->. Qed.
Next Obligation. by move=> ? ? ? ? ? -> ->. Qed.
Next Obligation.
rewrite predeqE => P; split; last first.
  by case=> e _ leP; move=> [a b] [i _] [-> ->]; apply: leP.
move=> entP; exists 1 => //= z z12; apply: entP; exists z.1 => //.
by rewrite {2}z12 -surjective_pairing.
Qed.

HB.instance Definition _ := discrete_pseudometric_mixin.
End discrete_pseudoMetric.

Definition pseudoMetric_bool {R : realType} :=
  [the pseudoMetricType R of discrete_topology discrete_bool : Type].

(** we use `discrete_topology` to equip choice types with a discrete topology *)
Section discrete_topology.

Let discrete_subproof (P : choiceType) :
  discrete_space (principal_filter_type P).
Proof. by []. Qed.

Definition discrete_topology_type (P : Type) : Type := P.

HB.instance Definition _ (P : choiceType) := Choice.copy
  (discrete_topology_type P) (discrete_topology (discrete_subproof P)).
HB.instance Definition _ (P : choiceType) := Filtered.copy
  (discrete_topology_type P) (discrete_topology (discrete_subproof P)).
HB.instance Definition _  (P : choiceType) := Uniform.copy
  (discrete_topology_type P) (discrete_topology (discrete_subproof P)).
HB.instance Definition _ (P : pointedType) := Pointed.copy
  (discrete_topology_type P) (discrete_topology (discrete_subproof P)).
HB.instance Definition _ R (P : choiceType) : @PseudoMetric R _ :=
  PseudoMetric.copy
    (discrete_topology_type P) (discrete_topology (discrete_subproof P)).

End discrete_topology.

Lemma discrete_space_discrete (P : choiceType) :
  discrete_space (discrete_topology_type P).
Proof.
apply/funext => /= x; apply/funext => A; apply/propext; split.
- by move=> [E hE EA] _ ->; apply/EA/xsectionP/hE; exists x.
- move=> h; exists diagonal; first by move=> -[a b] [t _] [<- <-].
  by move=> y /xsectionP/= xy; exact: h.
Qed.

(** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set_system T) := (F, F) --> entourage.

Lemma cvg_cauchy {T : puniformType} (F : set_system T) : Filter F ->
  [cvg F in T] -> cauchy F.
Proof.
move=> FF cvF A entA; have /entourage_split_ex [B entB sB2A] := entA.
exists (xsection (B^-1%relation) (lim F), xsection B (lim F)).
  split=> /=; apply: cvF; rewrite /= -nbhs_entourageE; last by exists B.
  by exists B^-1%relation => //; exact: entourage_inv.
move=> ab [/= /xsectionP Balima /xsectionP Blimb]; apply: sB2A.
by exists (lim F).
Qed.

HB.mixin Record Uniform_isComplete T of PointedUniform T := {
  cauchy_cvg :
    forall (F : set_system T), ProperFilter F -> cauchy F -> cvg F
}.

#[short(type="completeType")]
HB.structure Definition Complete :=
  {T of Uniform T & Uniform_isComplete T & isPointed T}.

#[deprecated(since="mathcomp-analysis 2.0", note="use cauchy_cvg instead")]
Notation complete_ax := cauchy_cvg (only parsing).

Section completeType1.

Context {T : completeType}.

Lemma cauchy_cvgP (F : set_system T) (FF : ProperFilter F) : cauchy F <-> cvg F.
Proof. by split=> [/cauchy_cvg|/cvg_cauchy]. Qed.

End completeType1.
Arguments cauchy_cvg {T} F {FF} _ : rename.
Arguments cauchy_cvgP {T} F {FF}.

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

(** Complete pseudoMetric spaces *)

Definition cauchy_ex {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy_ball {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_ballP (R : numDomainType) (T  : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ball F <-> cauchy F.
Proof.
split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply/cauchyF/entourage_ball.
move=> U; rewrite -entourage_ballE => - [_/posnumP[eps] xyepsU].
by near do apply: xyepsU; apply: cauchyF.
Unshelve. all: by end_near. Qed.
Arguments cauchy_ballP {R T} F {FF}.

Lemma cauchy_exP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ex F -> cauchy F.
Proof.
move=> Fc A; rewrite !nbhs_simpl /= -entourage_ballE => -[_/posnumP[e] sdeA].
have /Fc [z /= Fze] := [gt0 of e%:num / 2]; near=> x y; apply: sdeA => /=.
by apply: (@ball_splitr _ _ z); [near: x|near: y].
Unshelve. all: by end_near. Qed.
Arguments cauchy_exP {R T} F {FF}.

Lemma cauchyP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (PF : ProperFilter F) :
  cauchy F <-> cauchy_ex F.
Proof.
split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
near F => x; exists x; near: x; apply: (@nearP_dep _ _ F F).
exact/Fcauchy/entourage_ball.
Unshelve. all: by end_near. Qed.
Arguments cauchyP {R T} F {PF}.

#[short(type="completePseudoMetricType")]
HB.structure Definition CompletePseudoMetric R :=
  {T of Complete T & PseudoPointedMetric R T}.

HB.instance Definition _ (R : numFieldType) (T : completePseudoMetricType R)
  (m n : nat) := Uniform_isComplete.Build 'M[T]_(m, n) cauchy_cvg.

HB.instance Definition _ (R : zmodType) := isPointed.Build R 0.

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

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%R y /.

Lemma subset_ball_prop_in_itv (R : realDomainType) (x : R) e P :
  ball_ Num.Def.normr x e `<=` P <->
  {in `](x - e), (x + e)[, forall y, P y}.
Proof.
by split=> exP y /=; rewrite ?in_itv (ltr_distlC, =^~ltr_distlC); apply: exP.
Qed.

Lemma subset_ball_prop_in_itvcc (R : realDomainType) (x : R) e P : 0 < e ->
  ball_ Num.Def.normr x (2 * e) `<=` P ->
  {in `[(x - e), (x + e)], forall y, P y}.
Proof.
move=> e_gt0 PP y; rewrite in_itv/= -ler_distlC => ye; apply: PP => /=.
by rewrite (le_lt_trans ye)// ltr_pMl// ltr1n.
Qed.

Global Instance ball_filter (R : realDomainType) (t : R) : Filter
  [set P | exists2 i : R, 0 < i & ball_ Num.norm t i `<=` P].
Proof.
apply: Build_Filter; [by exists 1 | move=> P Q | move=> P Q PQ]; rewrite /mkset.
- move=> -[x x0 xP] [y ? yQ]; exists (Num.min x y); first by rewrite lt_min x0.
  move=> z tz; split.
    by apply: xP; rewrite /= (lt_le_trans tz) // ge_min lexx.
  by apply: yQ; rewrite /= (lt_le_trans tz) // ge_min lexx orbT.
- by move=> -[x ? xP]; exists x => //; apply: (subset_trans xP).
Qed.

#[global] Hint Extern 0 (Filter [set P | exists2 i, _ & ball_ _ _ i `<=` P]) =>
  (apply: ball_filter) : typeclass_instances.

Section pseudoMetric_of_normedDomain.
Context {K : numDomainType} {R : normedZmodType K}.

Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Proof. by move=> ? /=; rewrite subrr normr0. Qed.

Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Proof. by rewrite /= distrC. Qed.

Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Proof.
move=> /= ? ?; rewrite -(subr0 x) -(subrr y) opprD opprK addrA -(addrA _ y).
by rewrite (le_lt_trans (ler_normD _ _)) // ltrD.
Qed.

Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Proof.
rewrite /nbhs_ entourage_E predeq2E => x A; split.
  move=> [e egt0 sbeA].
  exists [set xy | ball_ Num.norm xy.1 e xy.2]; first by exists e.
  by move=> r /xsectionP; exact: sbeA.
by move=> [E [e egt0 sbeE] sEA]; exists e => // ? ?; exact/sEA/xsectionP/sbeE.
Qed.

End pseudoMetric_of_normedDomain.

HB.instance Definition _ (R : zmodType) := Pointed.on R^o.

HB.instance Definition _ (R : numDomainType) := hasNbhs.Build R^o
  (nbhs_ball_ (ball_ (fun x => `|x|))).

HB.instance Definition _ (R : numFieldType) :=
  Nbhs_isPseudoMetric.Build R R^o
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma real_order_nbhsE (R : realFieldType) (x : R^o) : nbhs x =
  filter_from (fun i => itv_open_ends i /\ x \in i) (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U.
  case => _ /posnumP[e] xeU.
  exists (`]x - e%:num, x + e%:num[); first split; first by right.
    by rewrite in_itv /= -real_lter_distl subrr // normr0.
  apply: (subset_trans _ xeU) => z /=.
  by rewrite in_itv /= -real_lter_distl //= distrC.
case => [][[[]l|[]]] [[]r|[]] [[]]//= _.
- move=> xlr lrU; exists (Order.min (x - l) (r - x)).
    by rewrite /= lt_min ?lterBDr ?add0r ?(itvP xlr).
  apply/(subset_trans _ lrU)/subset_ball_prop_in_itv.
  suff : (`]x - Order.min (x - l) (r - x), x + Order.min (x - l) (r - x)[
          <= `]l, r[)%O by move/subitvP => H ? ?; exact: H.
  apply/andP; rewrite lteBSide; split => /=.
    apply: (@le_trans _ _ (x - (x - l))); last by rewrite lerB // ge_min lexx.
    by rewrite opprB addrCA subrr addr0.
  apply: (@le_trans _ _ (x + (r - x))); last by rewrite addrCA subrr addr0.
  by rewrite lerD // ge_min lexx orbT.
- move=> xl lU; exists (x - l) => /=; first by rewrite lterBDr add0r (itvP xl).
  apply/(subset_trans _ lU)/subset_ball_prop_in_itv.
  suff : (`]x - (x - l), x + (x - l)[ <= `]l, +oo[)%O.
    by move/subitvP => H ?; exact: H.
  by apply/andP; rewrite lteBSide/=; split; rewrite // opprB addrCA subrr addr0.
- move=> xr rU; exists (r - x) => /=; first by rewrite lterBDr add0r (itvP xr).
  apply/(subset_trans _ rU)/subset_ball_prop_in_itv.
  suff : (`]x - (r - x), x + (r - x)[ <= `]-oo, r[)%O.
    by move/subitvP => H ?; exact: H.
  by apply/andP; rewrite lteBSide/=; split; rewrite // addrCA subrr addr0.
- by move=> _; rewrite set_itvE subTset => ->; exists 1 => /=.
Qed.

Module numFieldTopology.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : rcfType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : archiFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numClosedFieldType) :=
  PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) :=
  Order_isNbhs.Build _ R (@real_order_nbhsE R).

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numFieldType) := PseudoPointedMetric.copy R R^o.

Module Exports. HB.reexport. End Exports.

End numFieldTopology.

Import numFieldTopology.Exports.

Lemma nbhs0_ltW (R : realFieldType) (x : R) : (0 < x)%R ->
 \forall r \near nbhs (0%R:R), (r <= x)%R.
Proof.
exists x => // y; rewrite /ball/= sub0r normrN => /ltW.
by apply: le_trans; rewrite ler_norm.
Qed.

Lemma nbhs0_lt (R : realType) (x : R) : (0 < x)%R ->
 \forall r \near nbhs (0%R:R), (r < x)%R.
Proof.
exists x => // z /=; rewrite sub0r normrN.
by apply: le_lt_trans; rewrite ler_norm.
Qed.

Global Instance Proper_dnbhs_regular_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
Qed.

Definition dense (T : topologicalType) (S : set T) :=
  forall (O : set T), O !=set0 -> open O -> O `&` S !=set0.

Lemma denseNE (T : topologicalType) (S : set T) : ~ dense S ->
  exists O, (exists x, open_nbhs x O) /\ (O `&` S = set0).
Proof.
rewrite /dense /open_nbhs.
move=> /existsNP[X /not_implyP[[x Xx] /not_implyP[ Ox /forallNP A]]].
by exists X; split; [exists x | rewrite -subset0; apply/A].
Qed.

Lemma dense_rat (R : realType) : dense (@ratr R @` setT).
Proof.
move=> A [r Ar]; rewrite openE => /(_ _ Ar)/nbhs_ballP[_/posnumP[e] reA].
have /rat_in_itvoo[q /itvP qre] : r < r + e%:num by rewrite ltrDl.
exists (ratr q) => //; split; last by exists q.
apply: reA; rewrite /ball /= distrC ltr_distl qre andbT.
by rewrite (@le_lt_trans _ _ r)// ?qre// lerBlDl lerDr ltW.
Qed.

Lemma separated_open_countable
    {R : realType} (I : Type) (B : I -> set R) (D : set I) :
    (forall i, open (B i)) -> (forall i, B i !=set0) ->
  trivIset D B -> countable D.
Proof.
move=> oB B0 tB; have [f fB] :
    {f : I -> rat & forall i, D i -> B i (ratr (f i))}.
  apply: (@choice _ _ (fun x y => D x -> B x (ratr y))) => i.
  have [r [Bir [q _ qr]]] := dense_rat (B0 _) (oB i).
  by exists q => Di; rewrite qr.
have inj_f : {in D &, injective f}.
  move=> i j /[!inE] Di Dj /(congr1 ratr) ratrij.
  have ? : (B i `&` B j) (ratr (f i)).
    by split => //; [exact: fB|rewrite ratrij; exact: fB].
  by apply/(tB _ _ Di Dj); exists (ratr (f i)).
apply/pcard_injP; have /card_bijP/cid[g bijg] := card_rat.
pose nat_of_rat (q : rat) : nat := set_val (g (to_setT q)).
have inj_nat_of_rat : injective nat_of_rat.
  rewrite /nat_of_rat; apply: inj_comp => //; apply: inj_comp => //.
  exact/bij_inj.
by exists (nat_of_rat \o f) => i j Di Dj /inj_nat_of_rat/inj_f; exact.
Qed.

Section weak_pseudoMetric.
Context {R : realType} (pS : choiceType) (U : pseudoMetricType R) .
Variable (f : pS -> U).

Notation S := (weak_topology f).

Definition weak_ball (x : S) (r : R) (y : S) := ball (f x) r (f y).

Lemma weak_pseudo_metric_ball_center (x : S) (e : R) : 0 < e -> weak_ball x e x.
Proof. by move=> /posnumP[{}e]; exact: ball_center. Qed.

Lemma weak_pseudo_metric_entourageE : entourage = entourage_ weak_ball.
Proof.
rewrite /entourage /= /weak_ent -entourage_ballE /entourage_.
have -> : (fun e => [set xy | ball (f xy.1) e (f xy.2)]) =
   (preimage (map_pair f) \o fun e => [set xy | ball xy.1 e xy.2])%FUN.
  by [].
rewrite eqEsubset; split; apply/filter_fromP.
- apply: filter_from_filter; first by exists 1 => /=.
  move=> e1 e2 e1pos e2pos; wlog e1lee2 : e1 e2 e1pos e2pos / e1 <= e2.
    by have [?|/ltW ?] := lerP e1 e2; [exact | rewrite setIC; exact].
  exists e1 => //; rewrite -preimage_setI; apply: preimage_subset.
  by move=> ? ?; split => //; apply: le_ball; first exact: e1lee2.
- by move=> E [e ?] heE; exists e => //; apply: preimage_subset.
- apply: filter_from_filter.
    by exists [set xy | ball xy.1 1 xy.2]; exists 1 => /=.
  move=> E1 E2 [e1 e1pos he1E1] [e2 e2pos he2E2].
  wlog ? : E1 E2 e1 e2 e1pos e2pos he1E1 he2E2 / e1 <= e2.
    have [? /(_ _ _ e1 e2)|/ltW ? ] := lerP e1 e2; first exact.
    by rewrite setIC => /(_ _ _ e2 e1); exact.
  exists (E1 `&` E2) => //; exists e1 => // xy /= B; split; first exact: he1E1.
  by apply/he2E2/le_ball; last exact: B.
- by move=> e ?; exists [set xy | ball xy.1 e xy.2] => //; exists e => /=.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R S
  weak_pseudo_metric_ball_center (fun _ _ _ => @ball_sym _ _ _ _ _)
  (fun _ _ _ _ _ => @ball_triangle _ _ _ _ _ _ _)
  weak_pseudo_metric_entourageE.

Lemma weak_ballE (e : R) (x : S) : f @^-1` (ball (f x) e) = ball x e.
Proof. by []. Qed.

End weak_pseudoMetric.

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

Definition subspace {T : Type} (A : set T) := T.
Arguments subspace {T} _ : simpl never.

Definition incl_subspace {T A} (x : subspace A) : T := x.

Section Subspace.
Context {T : topologicalType} (A : set T).

Definition nbhs_subspace (x : subspace A) : set_system (subspace A) :=
  if x \in A then within A (nbhs x) else globally [set x].

Variant nbhs_subspace_spec x : Prop -> Prop -> bool -> set_system T -> Type :=
  | WithinSubspace :
      A x -> nbhs_subspace_spec x True False true (within A (nbhs x))
  | WithoutSubspace :
    ~ A x -> nbhs_subspace_spec x False True false (globally [set x]).

Lemma nbhs_subspaceP_subproof x :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs_subspace x).
Proof.
rewrite /nbhs_subspace; case:(boolP (x \in A)); rewrite ?(inE, notin_setE) => xA.
  by rewrite (@propext (A x) True)// not_True; constructor.
by rewrite (@propext (A x) False)// not_False; constructor.
Qed.

Lemma nbhs_subspace_in (x : T) : A x -> within A (nbhs x) = nbhs_subspace x.
Proof. by case: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_out (x : T) : ~ A x -> globally [set x] = nbhs_subspace x.
Proof. by case: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_filter (x : subspace A) : ProperFilter (nbhs_subspace x).
Proof.
case: nbhs_subspaceP_subproof => ?; last exact: globally_properfilter.
by apply: within_nbhs_proper; apply: subset_closure.
Qed.

HB.instance Definition _ := Choice.copy (subspace A) _.

HB.instance Definition _ := hasNbhs.Build (subspace A) nbhs_subspace.

Lemma nbhs_subspaceP (x : subspace A) :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs x).
Proof. exact: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_singleton (p : subspace A) B : nbhs p B -> B p.
Proof. by case: nbhs_subspaceP => ? => [/nbhs_singleton|]; apply. Qed.

Lemma nbhs_subspace_nbhs (p : subspace A) B : nbhs p B -> nbhs p (nbhs^~ B).
Proof.
case: nbhs_subspaceP => [|] Ap.
  by move=> /nbhs_interior; apply: filterS => y A0y Ay; case: nbhs_subspaceP.
by move=> E x ->; case: nbhs_subspaceP.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build (subspace A)
  nbhs_subspace_filter nbhs_subspace_singleton nbhs_subspace_nbhs.

Lemma subspace_cvgP (F : set_system T) (x : T) : Filter F -> A x ->
  (F --> (x : subspace A)) <-> (F --> within A (nbhs x)).
Proof. by case: _ / nbhs_subspaceP. Qed.

Lemma subspace_continuousP {S : topologicalType} (f : T -> S) :
  continuous (f : subspace A -> S) <->
  (forall x, A x -> f @ within A (nbhs x) --> f x) .
Proof.
split => [ctsf x Ax W /=|wA x].
  by rewrite nbhs_simpl //= nbhs_subspace_in //=; apply: ctsf.
rewrite /continuous_at; case: _ / (nbhs_subspaceP x) => Ax.
  exact: (cvg_trans _ (wA _ Ax)).
by move=> ? /nbhs_singleton //= ?; rewrite nbhs_simpl => ? ->.
Qed.

Lemma subspace_eq_continuous {S : topologicalType} (f g : subspace A -> S) :
  {in A, f =1 g} -> continuous f -> continuous g.
Proof.
rewrite ?subspace_continuousP => feq L x Ax; rewrite -(feq x) ?inE //.
by apply: cvg_trans _ (L x Ax); apply: fmap_within_eq=> ? ?; rewrite feq.
Qed.

Lemma continuous_subspace_in {U : topologicalType} (f : subspace A -> U) :
  continuous f = {in A, continuous f}.
Proof.
rewrite propeqE in_setP subspace_continuousP /continuous_at //=; split.
  by move=> Q x Ax; case: (nbhs_subspaceP x) => //=; exact: Q.
by move=> + x Ax => /(_ x Ax); case: (nbhs_subspaceP x) => //=; exact: Q.
Qed.

Lemma nbhs_subspace_interior (x : T) :
  A^° x -> nbhs x = (nbhs (x : subspace A)).
Proof.
move=> /[dup] /[dup] /interior_subset ? /within_interior <- ?.
by case: RHS / nbhs_subspaceP.
Qed.

Lemma nbhs_subspace_ex (U : set T) (x : T) : A x ->
  nbhs (x : subspace A) U <->
  exists2 V, nbhs (x : T) V & U `&` A = V `&` A.
Proof. by case: (nbhs _) / nbhs_subspaceP; rewrite // ?withinE. Qed.

Lemma incl_subspace_continuous : continuous incl_subspace.
Proof. by apply/subspace_continuousP => x Ax; apply: cvg_within. Qed.

Section SubspaceOpen.

Lemma open_subspace1out (x : subspace A) : ~ A x -> open [set x].
Proof.
move=> /nbhs_subspace_out E; have : nbhs x [set x] by rewrite /nbhs //= -E.
rewrite nbhsE => [[U []]] oU Ux Usub; suff : U = [set x] by move=> <-.
by rewrite eqEsubset; split => // t ->.
Qed.

Lemma open_subspace_out (U : set (subspace A)) : U `<=` ~` A -> open U.
Proof.
move=> Usub; rewrite (_ : U = \bigcup_(i in U) [set i]).
  by apply: bigcup_open => ? ?; apply: open_subspace1out; exact: Usub.
by rewrite eqEsubset; split => x; [move=> ?; exists x|case=> i ? ->].
Qed.

Lemma open_subspaceT : open (A : set (subspace A)).
Proof. by move=> ?; case: nbhs_subspaceP => //= ? ?; apply: withinT. Qed.

Lemma open_subspaceIT (U : set (subspace A)) : open (U `&` A) = open U.
Proof.
apply/propext; split; last first.
  by move=> oU; apply: openI => //; apply: open_subspaceT.
move=> oUA; rewrite (_ : U = (U `&` A) `|` (U `&` ~`A)).
  by apply: openU => //; apply: open_subspace_out => ? [].
by rewrite -setIUr setUCr setIT.
Qed.

Lemma open_subspaceTI (U : set (subspace A)) :
  open (A `&` U : set (subspace A)) = open U.
Proof. by rewrite setIC open_subspaceIT. Qed.

Lemma closed_subspaceT : closed (A : set (subspace A)).
Proof.
rewrite -(setCK A);
by apply: open_closedC; rewrite -open_subspaceIT setICl; exact: open0.
Qed.

Lemma open_subspaceP (U : set T) :
  open (U : set (subspace A)) <->
  exists V, open (V : set T) /\ V `&` A = U `&` A.
Proof.
split; first last.
  case=> V [oV UV]; rewrite -open_subspaceIT -UV.
  move=> x //= []; case: nbhs_subspaceP; rewrite //= withinE.
  move=> ? ? _; exists V; last by rewrite -setIA setIid.
  by move: oV; rewrite openE /interior; apply.
rewrite -open_subspaceIT => oUA.
have oxF : forall x : T, (U `&` A) x ->
    exists V, (open_nbhs (x : T) V) /\ (V `&` A `<=` U `&` A).
  move=> x /[dup] UAx /= [??]; move: (oUA _ UAx);
    case: nbhs_subspaceP => // ?.
  rewrite withinE /= => [[V nbhsV UV]]; rewrite -setIA setIid in UV.
  exists V^°; split; first rewrite open_nbhsE; first split => //.
  - exact: open_interior.
  - exact: nbhs_interior.
  - by rewrite UV=> t [/interior_subset] ??; split.
pose f (x : T) :=
  if pselect ((U `&` A) x) is left e then projT1 (cid (oxF x e)) else set0.
set V := \bigcup_(x in (U `&` A)) (f x); exists V; split.
  apply: bigcup_open => i UAi; rewrite /f; case: pselect => // ?; case: (cid _).
  by move=> //= W; rewrite open_nbhsE=> -[[]].
rewrite eqEsubset /V /f; split.
  move=> t [[u]] UAu /=; case: pselect => //= ?.
  by case: (cid _) => //= W [] _ + ? ?; apply; split.
move=> t UAt; split => //; last by case: UAt.
exists t => //; case: pselect => //= [[? ?]].
by case: (cid _) => //= W [] [] _.
Qed.

Lemma closed_subspaceP (U : set T) :
  closed (U : set (subspace A)) <->
  exists V, closed (V : set T) /\ V `&` A = U `&` A.
Proof.
rewrite -openC open_subspaceP.
under [X in _ <-> X] eq_exists => V do rewrite -openC.
by split => -[V [? VU]]; exists (~` V); split; rewrite ?setCK //;
  move/(congr1 setC): VU; rewrite ?eqEsubset ?setCI ?setCK; firstorder.
Qed.

Lemma open_subspaceW (U : set T) :
  open (U : set T) -> open (U : set (subspace A)).
Proof. by move=> oU; apply/open_subspaceP; exists U. Qed.

Lemma closed_subspaceW (U : set T) :
  closed (U : set T) -> closed (U : set (subspace A)).
Proof.  by move=> /closed_openC/open_subspaceW/open_closedC; rewrite setCK. Qed.

Lemma open_setIS (U : set (subspace A)) : open A ->
  open (U `&` A : set T) = open U.
Proof.
move=> oA; apply/propext; rewrite open_subspaceP.
split=> [|[V [oV <-]]]; last exact: openI.
by move=> oUA; exists (U `&` A); rewrite -setIA setIid.
Qed.

Lemma open_setSI (U : set (subspace A)) : open A -> open (A `&` U) = open U.
Proof. by move=> oA; rewrite -setIC open_setIS. Qed.

Lemma closed_setIS (U : set (subspace A)) : closed A ->
  closed (U `&` A : set T) = closed U.
Proof.
move=> oA; apply/propext; rewrite closed_subspaceP.
split=> [|[V [oV <-]]]; last exact: closedI.
by move=> oUA; exists (U `&` A); rewrite -setIA setIid.
Qed.

Lemma closed_setSI (U : set (subspace A)) :
  closed A -> closed (A `&` U) = closed U.
Proof. by move=> oA; rewrite -setIC closed_setIS. Qed.

Lemma closure_subspaceW (U : set T) :
  U `<=` A -> closure (U : set (subspace A)) = closure (U : set T) `&` A.
Proof.
have /closed_subspaceP := (@closed_closure _ (U : set (subspace A))).
move=> [V] [clV VAclUA].
move=> /[dup] /(@closure_subset [the topologicalType of subspace _]).
have /closure_id <- := closed_subspaceT => /setIidr <-; rewrite setIC.
move=> UsubA; rewrite eqEsubset; split.
  apply: setSI; rewrite closureE; apply: smallest_sub (@subset_closure _ U).
  by apply: closed_subspaceW; exact: closed_closure.
rewrite -VAclUA; apply: setSI; rewrite closureE //=; apply: smallest_sub => //.
apply: subset_trans (@subIsetl _ V A); rewrite VAclUA subsetI; split => //.
exact: (@subset_closure _ (U : set (subspace A))).
Qed.

End SubspaceOpen.

Lemma compact_subspaceIP (U : set T) :
  compact (U `&` A : set (subspace A)) <-> compact (U `&` A : set T).
Proof.
rewrite ?compact_ultra /=.
split=> + F UF FUA => /(_ F UF FUA) [x] [[Ux Ax] Fp].
  exists x; split=> //; move/subspace_cvgP: Fp => /(_ Ax) Fx.
  by apply: cvg_trans; [exact: Fx | exact: cvg_within].
exists x; split=> //; apply/subspace_cvgP => //.
rewrite withinE => W/= -[V nbhsV WV]; apply: filterS (V `&` (U `&` A)) _ _ _.
  by rewrite setIC -setIA [A `&` _]setIC -WV=>?[]?[].
by apply: filterI; rewrite nbhs_simpl //; exact: Fp.
Qed.

Lemma clopen_connectedP : connected A <->
  (forall U, @clopen [the topologicalType of subspace A] U ->
    U `<=` A  -> U !=set0 -> U = A).
Proof.
split.
  move=> + U [/open_subspaceP oU /closed_subspaceP cU] UA U0; apply => //.
  - case: oU => V [oV VAUA]; exists V; rewrite // setIC VAUA.
    exact/esym/setIidPl.
  - case: cU => V [cV VAUA]; exists V => //; rewrite setIC VAUA.
    exact/esym/setIidPl.
move=> clpnA U Un0 [V oV UVA] [W cW UWA]; apply: clpnA => //; first split.
- by apply/open_subspaceP; exists V; rewrite setIC UVA setIAC setIid.
- by apply/closed_subspaceP; exists W; rewrite setIC UWA setIAC setIid.
- by rewrite UWA; exact: subIsetl.
Qed.

End Subspace.

HB.instance Definition _ {T : ptopologicalType} (A : set T) :=
  isPointed.Build (subspace A) point.

Global Instance subspace_filter {T : topologicalType}
    (A : set T) (x : subspace A) :
  Filter (nbhs_subspace x) := nbhs_subspace_filter x.

Global Instance subspace_proper_filter {T : topologicalType}
    (A : set T) (x : subspace A) :
  ProperFilter (nbhs_subspace x) := nbhs_subspace_filter x.

Notation "{ 'within' A , 'continuous' f }" :=
  (continuous (f : subspace A -> _)) : classical_set_scope.

Arguments nbhs_subspaceP {T} A x.

Section SubspaceRelative.
Context {T : topologicalType}.
Implicit Types (U : topologicalType) (A B : set T).

Lemma nbhs_subspace_subset A B (x : T) :
  A `<=` B -> nbhs (x : subspace B) `<=` nbhs (x : subspace A).
Proof.
rewrite /= => AB; case: (nbhs_subspaceP A); case: (nbhs_subspaceP B).
- by move=> ? ?; apply: within_subset => //=; exact: (nbhs_filter x).
- by move=> ? /AB.
- by move=> Bx ? W /nbhs_singleton /(_ Bx) ? ? ->.
- by move=> ? ?.
Qed.

Lemma continuous_subspaceW {U} A B (f : T -> U) :
  A `<=` B ->
  {within B, continuous f} -> {within A, continuous f}.
Proof.
by move=> ? ctsF ? ? ?; apply: (@nbhs_subspace_subset A B) => //; exact: ctsF.
Qed.

Lemma nbhs_subspaceT (x : T) : nbhs (x : subspace setT) = nbhs x.
Proof.
have [_|] := nbhs_subspaceP [set: T]; last by cbn.
rewrite eqEsubset withinE; split => [W [V nbhsV]|W ?]; last by exists W.
by rewrite 2!setIT => ->.
Qed.

Lemma continuous_subspaceT_for {U} A (f : T -> U) (x : T) :
  A x -> {for x, continuous f} -> {for x, continuous (f : subspace A -> U)}.
Proof.
rewrite /continuous_at /prop_for => inA ctsf.
have [_|//] := nbhs_subspaceP A x.
apply: (cvg_trans _ ctsf); apply: cvg_fmap2; apply: cvg_within.
Qed.

Lemma continuous_in_subspaceT {U} A (f : T -> U) :
  {in A, continuous f} -> {within A, continuous f}.
Proof.
rewrite continuous_subspace_in ?in_setP => ctsf t At.
by apply: continuous_subspaceT_for => //=; apply: ctsf.
Qed.

Lemma continuous_subspaceT {U} A (f : T -> U) :
  continuous f -> {within A, continuous f}.
Proof.
move=> ctsf; rewrite continuous_subspace_in => ? ?.
exact: continuous_in_subspaceT.
Qed.

Lemma continuous_open_subspace {U} A (f : T -> U) :
  open A -> {within A, continuous f} = {in A, continuous f}.
Proof.
rewrite openE continuous_subspace_in /= => oA; rewrite propeqE ?in_setP.
by split => + x /[dup] Ax /oA Aox => /(_ _ Ax);
  rewrite /continuous_at -(nbhs_subspace_interior Aox).
Qed.

Lemma continuous_inP {U} A (f : T -> U) : open A ->
  {in A, continuous f} <-> forall X, open X -> open (A `&` f @^-1` X).
Proof.
move=> oA; rewrite -continuous_open_subspace// continuousP.
by under eq_forall do rewrite -open_setSI//.
Qed.

(* pasting lemma *)
Lemma withinU_continuous {U} A B (f : T -> U) : closed A -> closed B ->
  {within A, continuous f} -> {within B, continuous f} ->
  {within A `|` B, continuous f}.
Proof.
move=> ? ? ctsA ctsB; apply/continuous_closedP => W oW.
case/continuous_closedP/(_ _ oW)/closed_subspaceP: ctsA => V1 [? V1W].
case/continuous_closedP/(_ _ oW)/closed_subspaceP: ctsB => V2 [? V2W].
apply/closed_subspaceP; exists ((V1 `&` A) `|` (V2 `&` B)); split.
  by apply: closedU; exact: closedI.
rewrite [RHS]setIUr -V2W -V1W eqEsubset; split=> ?.
  by case=> [[][]] ? ? [] ?; [left | left | right | right]; split.
by case=> [][] ? ?; split=> []; [left; split | left | right; split | right].
Qed.

Lemma subspaceT_continuous {U} A (B : set U) (f : {fun A >-> B}) :
  {within A, continuous f} -> continuous (f : subspace A -> subspace B).
Proof.
move=> /continuousP ctsf; apply/continuousP => O /open_subspaceP [V [oV VBOB]].
rewrite -open_subspaceIT; apply/open_subspaceP.
case/open_subspaceP: (ctsf _ oV) => W [oW fVA]; exists W; split => //.
rewrite fVA -setIA setIid eqEsubset; split => x [fVx Ax]; split => //.
- by have /[!VBOB]-[] : (V `&` B) (f x) by split => //; exact: funS.
- by have /[!esym VBOB]-[] : (O `&` B) (f x) by split => //; exact: funS.
Qed.

Lemma continuous_subspace0 {U} (f : T -> U) : {within set0, continuous f}.
Proof.
move=> x Q /=.
by case: (nbhs_subspaceP (@set0 T) x) => // _ /nbhs_singleton /= ? ? ->.
Qed.

Lemma continuous_subspace1 {U} (a : T) (f : T -> U) :
  {within [set a], continuous f}.
Proof.
move=> x Q /=.
case: (nbhs_subspaceP [set a] x); last by move=> _ /nbhs_singleton /= ? ? ->.
by move=> -> /nbhs_singleton ?; apply: nearW => ? ->.
Qed.

End SubspaceRelative.

Section SubspaceUniform.
Local Open Scope relation_scope.
Context {X : uniformType} (A : set X).

Definition subspace_ent :=
  filter_from (@entourage X)
  (fun E => [set xy | (xy.1 = xy.2) \/ (A xy.1 /\ A xy.2 /\ E xy)]).

Let Filter_subspace_ent : Filter subspace_ent.
Proof.
apply: filter_from_filter; first by (exists setT; exact: filterT).
move=> P Q entP entQ; exists (P `&` Q); first exact: filterI.
move=> [x y] /=; case; first (by move=> ->; split=> /=; left).
by move=> [Ax [Ay [Pxy Qxy]]]; split=> /=; right.
Qed.

Let subspace_uniform_entourage_diagonal :
  forall X : set (subspace A * subspace A),
    subspace_ent X -> diagonal `<=` X.
Proof. by move=> ? + [x y]/diagonalP ->; case=> V entV; apply; left. Qed.

Let subspace_uniform_entourage_inv : forall A : set (subspace A * subspace A),
  subspace_ent A -> subspace_ent A^-1.
Proof.
move=> ?; case=> V ? Vsub; exists V^-1; first exact: entourage_inv.
move=> [x y] /= G; apply: Vsub; case: G; first by (move=> <-; left).
by move=> [? [? Vxy]]; right; repeat split.
Qed.

Let subspace_uniform_entourage_split_ex :
  forall A : set (subspace A * subspace A),
    subspace_ent A -> exists2 B, subspace_ent B & B \; B `<=` A.
Proof.
move=> ?; case=> E entE Esub.
exists  [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ split_ent E xy].
  by exists (split_ent E).
move=> [x y] [z /= Ez zE] /=; case: Ez; case: zE.
  - by move=> -> ->; apply: Esub; left.
  - move=> [ ? []] ? G xy; subst; apply: Esub; right; repeat split => //=.
    by apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  - move=> -> [ ? []] ? G; apply: Esub; right; repeat split => //=.
    by apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  - move=> []? []? ?[]?[]??; apply: Esub; right; repeat split => //=.
    by apply: subset_split_ent => //; exists z.
Qed.

Let subspace_uniform_nbhsE : @nbhs _ (subspace A) = nbhs_ subspace_ent.
Proof.
pose EA := [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2].
have entEA : subspace_ent EA.
  exists setT; first exact: filterT.
  by move=> [??] /= [ ->|[?] [?]];[left|right].
rewrite funeq2E=> x U.
case: (@nbhs_subspaceP X A x); rewrite propeqE; split => //=.
- rewrite withinE; case=> V /[dup] nbhsV => [/nbhsP [E entE Esub] UV].
  exists [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ E xy].
    by exists E => //= [[? ?]] /= [->| [? []]//]; exact: entourage_refl.
  move=> y /= /xsectionP/= -[<-{y}|].
    suff : (U `&` A) x by case.
    by rewrite UV; split => //; exact: (@nbhs_singleton X).
  case=> _ [Ay Ey]; suff : (U `&` A) y by case.
  by rewrite UV; split => //; exact/Esub/xsectionP.
- move=> [] W [E eentE subW] subU //=.
  near=> w; apply/subU/xsectionP/subW; right; repeat split => //=.
    exact: (near (withinT _ (@nbhs_filter X _))).
  by near: w; apply/nbhsP; exists E => // y /xsectionP.
- move=> //= Ux; exists EA => //.
  by move=> y /xsectionP => -[|[]] //= <-; exact: Ux.
- rewrite //= => [[W [W' entW' subW] subU]] ? ->.
  by apply/subU/xsectionP/subW; left.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build (subspace A)
  Filter_subspace_ent subspace_uniform_entourage_diagonal
  subspace_uniform_entourage_inv subspace_uniform_entourage_split_ex
  subspace_uniform_nbhsE.

End SubspaceUniform.

Section SubspacePseudoMetric.
Context {R : numDomainType} {X : pseudoMetricType R} (A : set X).
Implicit Type e : R.

Definition subspace_ball (x : subspace A) (r : R) :=
  if x \in A then A `&` ball (x : X) r else [set x].

Let subspace_pm_ball_center x e : 0 < e -> subspace_ball x e x.
Proof.
rewrite /subspace_ball; case: ifP => //= /asboolP ? ?.
by split=> //; exact: ballxx.
Qed.

Let subspace_pm_ball_sym x y e :
  subspace_ball x e y -> subspace_ball y e x.
Proof.
rewrite /subspace_ball; case: ifP => //= /asboolP ?.
  by move=> [] Ay /ball_sym yBx; case: ifP => /asboolP.
by move=> ->; case: ifP => /asboolP.
Qed.

Let subspace_pm_ball_triangle x y z e1 e2 :
  subspace_ball x e1 y -> subspace_ball y e2 z -> subspace_ball x (e1 + e2) z.
Proof.
rewrite /subspace_ball; (repeat case: ifP => /asboolP).
- by move=>?? [??] [??]; split => //=; apply: ball_triangle; eauto.
- by move=> ?? [??] ->.
- by move=> + /[swap] => /[swap] => ->.
- by move=> _ _ -> ->.
Qed.

Let subspace_pm_entourageE :
  @entourage (subspace A) = entourage_ subspace_ball.
Proof.
rewrite eqEsubset; split; rewrite /subspace_ball.
  move=> U [W + subU]; rewrite -entourage_ballE => [[eps] nneg subW].
  exists eps => //; apply: (subset_trans _ subU).
  move=> [x y] /=; case: ifP => /asboolP ?.
    by move=> [Ay xBy]; right; repeat split => //; exact: subW.
  by move=> ->; left.
move=> E [eps nneg subE]; exists [set xy | ball (xy.1 : X) eps xy.2].
  by rewrite -entourage_ballE; exists eps.
move=> [x y] /= [->|[]Ax []Ay xBy]; apply: subE => //=.
  by case: ifP => /asboolP; split => //; exact: ballxx.
by case: ifP => /asboolP.
Qed.

HB.instance Definition _ :=
  @Uniform_isPseudoMetric.Build R (subspace A) subspace_ball
    subspace_pm_ball_center subspace_pm_ball_sym subspace_pm_ball_triangle
    subspace_pm_entourageE.

Lemma ball_subspace_ball (x : subspace A) r (y : subspace A) :
  ball x r y = subspace_ball x r y.
Proof. by []. Qed.

End SubspacePseudoMetric.

Section SubspaceWeak.
Context {T : topologicalType} {U : choiceType}.
Variables (f : U -> T).

Lemma weak_subspace_open (A : set (weak_topology f)) :
  open A -> open (f @` A : set (subspace (range f))).
Proof.
case=> B oB <-; apply/open_subspaceP; exists B; split => //; rewrite eqEsubset.
split => z [] /[swap]; first by case=> w _ <- ?; split; exists w.
by case=> w _ <- [v] ? <-.
Qed.

End SubspaceWeak.

Lemma continuous_compact {T U : topologicalType} (f : T -> U) A :
  {within A, continuous f} -> compact A -> compact (f @` A).
Proof.
move=> fcont Aco F FF FfA; set G := filter_from F (fun C => A `&` f @^-1` C).
have GF : ProperFilter G.
  apply: (filter_from_proper (filter_from_filter _ _)).
  - by exists (f @` A).
  - by move=> C1 C2 F1 F2; exists (C1 `&` C2); [exact: filterI|move=> ? [? []]].
  - by move=> C /(filterI FfA) /filter_ex [_ [[p ? <-]]]; exists p.
move: Aco; rewrite -[A]setIid => /compact_subspaceIP; rewrite setIid.
case /(_ G); first by exists (f @` A) => // ? [].
move=> p [Ap clsGp]; exists (f p); split; first exact/imageP.
move=> B C FB /fcont p_Cf.
have : G (A `&` f @^-1` B) by exists B.
by move=> /clsGp /(_ p_Cf) [q [[]]]; exists (f q).
Qed.

Lemma connected_continuous_connected (T U : topologicalType)
    (A : set T) (f : T -> U) :
  connected A -> {within A, continuous f} -> connected (f @` A).
Proof.
move=> cA cf; apply: contrapT => /connectedPn[E [E0 fAE sE]].
set AfE := fun b =>(A `&` f @^-1` E b) : set (subspace A).
suff sAfE : separated (AfE false) (AfE true).
  move: cA; apply/connectedPn; exists AfE; split; last (rewrite /AfE; split).
  - move=> b; case: (E0 b) => /= u Ebu.
    have [t Et ftu] : (f @` A) u by rewrite fAE; case: b Ebu; [right|left].
    by exists t; split => //=; rewrite /preimage ftu.
  - by rewrite -setIUr -preimage_setU -fAE; exact/esym/setIidPl/preimage_image.
  + rewrite -{2}(setIid A) ?setIA -(@closure_subspaceW _ A); last by move=> ?[].
    by rewrite -/(AfE false) -setIA -/(AfE true); case: sAfE.
  + rewrite -{1}(setIid A) setIC ?setIA -(@closure_subspaceW _ A).
      by rewrite -/(AfE true) -setIA -/(AfE false) setIC; case: sAfE.
    by move=> ?[].
suff cI0 b : closure (AfE b) `&` AfE (~~ b) = set0.
  by rewrite /separated cI0 setIC cI0.
have [fAfE cEIE] :
    f @` AfE (~~ b) = E (~~ b) /\ closure (E b) `&` E (~~ b) = set0.
  split; last by case: sE => ? ?; case: b => //; rewrite setIC.
  rewrite eqEsubset; split => [|u Ebu].
    apply: (subset_trans sub_image_setI).
    by apply: subIset; right; exact: image_preimage_subset.
  have [t [At ftu]] : exists t, A t /\ f t = u.
    suff [t At ftu] : (f @` A) u by exists t.
    by rewrite fAE; case: b Ebu; [left|right].
  by exists t => //; split => //=; rewrite /preimage ftu.
have ? : f @` closure (AfE b) `<=` closure (E b).
  have /(@image_subset _ _ f) : closure (AfE b) `<=` f @^-1` closure (E b).
    have /closure_id -> : closed (f @^-1` closure (E b) : set (subspace A)).
      by apply: closed_comp => //; exact: closed_closure.
    apply: closure_subset.
    have /(@preimage_subset _ _ f) A0cA0 := @subset_closure _ (E b).
    by apply: subset_trans A0cA0; apply: subIset; right.
  by move/subset_trans; apply; exact: image_preimage_subset.
apply/eqP/negPn/negP/set0P => -[t [? ?]].
have : f @` closure (AfE b) `&` f @` AfE (~~ b) = set0.
  by rewrite fAfE; exact: subsetI_eq0 cEIE.
by rewrite predeqE => /(_ (f t)) [fcAfEb] _; apply: fcAfEb; split; exists t.
Qed.

Lemma continuous_localP {X Y : topologicalType} (f : X -> Y) :
  continuous f <->
  forall (x : X), \forall U \near powerset_filter_from (nbhs x),
    {within U, continuous f}.
Proof.
split; first by move=> ? ?; near=> U; apply: continuous_subspaceT=> ?; exact.
move=> + x => /(_ x)/near_powerset_filter_fromP.
case; first by move=> ? ?; exact: continuous_subspaceW.
move=> U nbhsU wctsf; wlog oU : U wctsf nbhsU / open U.
  move: nbhsU; rewrite nbhsE => -[] W [oW Wx WU] /(_ W).
  by move/(_ (continuous_subspaceW WU wctsf)); apply => //; exists W.
move/nbhs_singleton: nbhsU; move: x; apply/in_setP.
by rewrite -continuous_open_subspace.
Unshelve. end_near. Qed.
