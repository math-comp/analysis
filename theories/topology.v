(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality mathcomp_extra fsbigop.
Require Import reals signed.

(******************************************************************************)
(*                  Filters and basic topological notions                     *)
(*                                                                            *)
(* This file develops tools for the manipulation of filters and basic         *)
(* topological notions. The development of topological notions builds on      *)
(* "filtered types". They are types equipped with an interface that           *)
(* associates to each element a set of sets, intended to represent a filter.  *)
(* The notions of limit and convergence are defined for filtered types and in *)
(* the documentation below we call "canonical filter" of an element the set   *)
(* of sets associated to it by the interface of filtered types.               *)
(*                                                                            *)
(*                 monotonous A f := {in A &, {mono f : x y / x <= y}} \/     *)
(*                                   {in A &, {mono f : x y /~ x <= y}}.      *)
(*                                                                            *)
(* * Filters :                                                                *)
(*                   filteredType U == interface type for types whose         *)
(*                                     elements represent sets of sets on U.  *)
(*                                     These sets are intended to be filters  *)
(*                                     on U but this is not enforced yet.     *)
(*               FilteredType U T m == packs the function m: T -> set (set U) *)
(*                                     to build a filtered type of type       *)
(*                                     filteredType U; T must have a          *)
(*                                     pointedType structure.                 *)
(*     [filteredType U of T for cT] == T-clone of the filteredType U          *)
(*                                     structure cT.                          *)
(*            [filteredType U of T] == clone of a canonical structure of      *)
(*                                     filteredType U on T.                   *)
(*              Filtered.source Y Z == structure that records types X such    *)
(*                                     that there is a function mapping       *)
(*                                     functions of type X -> Y to filters on *)
(*                                     Z. Allows to infer the canonical       *)
(*                                     filter associated to a function by     *)
(*                                     looking at its source type.            *)
(*                Filtered.Source F == if F : (X -> Y) -> set (set Z), packs  *)
(*                                     X with F in a Filtered.source Y Z      *)
(*                                     structure.                             *)
(*                           nbhs p == set of sets associated to p (in a      *)
(*                                     filtered type).                        *)
(*                  filter_from D B == set of the supersets of the elements   *)
(*                                     of the family of sets B whose indices  *)
(*                                     are in the domain D.                   *)
(*                                     This is a filter if (B_i)_(i in D)     *)
(*                                     forms a filter base.                   *)
(*                  filter_prod F G == product of the filters F and G.        *)
(*                    [filter of x] == canonical filter associated to x.      *)
(*                        F `=>` G <-> G is included in F; F and G are sets   *)
(*                                     of sets.                               *)
(*                         F --> G <-> the canonical filter associated to G   *)
(*                                     is included in the canonical filter    *)
(*                                     associated to F.                       *)
(*                            lim F == limit of the canonical filter          *)
(*                                     associated with F if there is such a   *)
(*                                     limit, i.e., an element l such that    *)
(*                                     the canonical filter associated to l   *)
(*                                     is a subset of F.                      *)
(*                     [lim F in T] == limit of the canonical filter          *)
(*                                     associated to F in T where T has type  *)
(*                                     filteredType U.                        *)
(*                    [cvg F in T] <-> the canonical filter associated to F   *)
(*                                     converges in T.                        *)
(*                           cvg F <-> same as [cvg F in T] where T is        *)
(*                                     inferred from the type of the          *)
(*                                     canonical filter associated to F.      *)
(*                         Filter F == type class proving that the set of     *)
(*                                     sets F is a filter.                    *)
(*                   ProperFilter F == type class proving that the set of     *)
(*                                     sets F is a proper filter.             *)
(*                    UltraFilter F == type class proving that the set of     *)
(*                                     sets F is an ultrafilter               *)
(*                      filter_on T == interface type for sets of sets on T   *)
(*                                     that are filters.                      *)
(*                  FilterType F FF == packs the set of sets F with the proof *)
(*                                     FF of Filter F to build a filter_on T  *)
(*                                     structure.                             *)
(*                     pfilter_on T == interface type for sets of sets on T   *)
(*                                     that are proper filters.               *)
(*                 PFilterPack F FF == packs the set of sets F with the proof *)
(*                                     FF of ProperFilter F to build a        *)
(*                                     pfilter_on T structure.                *)
(*                         fmap f F == image of the filter F by the function  *)
(*                                     f                                      *)
(*                       E @[x --> F] == image of the canonical filter        *)
(*                                     associated to F by the function        *)
(*                                     (fun x => E).                          *)
(*                            f @ F == image of the canonical filter          *)
(*                                     associated to F by the function f.     *)
(*                        fmapi f F == image of the filter F by the relation  *)
(*                                     f                                      *)
(*                      E `@[x --> F] == image of the canonical filter        *)
(*                                     associated to F by the relation        *)
(*                                     (fun x => E).                          *)
(*                           f `@ F == image of the canonical filter          *)
(*                                     associated to F by the relation f.     *)
(*                       globally A == filter of the sets containing A.       *)
(*                @frechet_filter T := [set S : set T | finite_set (~` S)]    *)
(*                                     a.k.a. cofinite filter                 *)
(*                       at_point a == filter of the sets containing a.       *)
(*                       within D F == restriction of the filter F to the     *)
(*                                     domain D.                              *)
(*               principal_filter x == filter containing every superset of x. *)
(*                subset_filter F D == similar to within D F, but with        *)
(*                                     dependent types.                       *)
(*           powerset_filter_from F == The filter of downward closed subsets  *)
(*                                     of F. Enables use of near notation to  *)
(*                                     pick suitably small members of F       *)
(*                      in_filter F == interface type for the sets that       *)
(*                                     belong to the set of sets F.           *)
(*                      InFilter FP == packs a set P with a proof of F P to   *)
(*                                     build a in_filter F structure.         *)
(*                              \oo == "eventually" filter on nat: set of     *)
(*                                     predicates on natural numbers that are *)
(*                                     eventually true.                       *)
(*                         clopen U == U is both open and closed              *)
(*                   normal_space X == X is normal, sometimes called T4       *)
(*                  regular_space X == X is regular, sometimes called T3      *)
(*    separate_points_from_closed f == For a closed set U and point x outside *)
(*                                     some member of the family f sends      *)
(*                                     f_i(x) outside (closure (f_i @` U)).   *)
(*                                     Used together with join_product.       *)
(*                   join_product f == The function (x => f ^~ x). When the   *)
(*                                     family f separates points from closed  *)
(*                                     sets, join_product is an embedding.    *)
(*                                                                            *)
(* * Near notations and tactics:                                              *)
(*   --> The purpose of the near notations and tactics is to make the         *)
(*       manipulation of filters easier. Instead of proving F G, one can      *)
(*       prove G x for x "near F", i.e. for x such that H x for H arbitrarily *)
(*       precise as long as F H. The near tactics allow for a delayed         *)
(*       introduction of H: H is introduced as an existential variable and    *)
(*       progressively instantiated during the proof process.                 *)
(*   --> Notations:                                                           *)
(*                      {near F, P} == the property P holds near the          *)
(*                                     canonical filter associated to F; P    *)
(*                                     must have the form forall x, Q x.      *)
(*                                     Equivalent to F Q.                     *)
(*          \forall x \near F, P x <-> F (fun x => P x).                      *)
(*                     \near x, P x := \forall y \near x, P y.                *)
(*                  {near F & G, P} == same as {near H, P}, where H is the    *)
(*                                     product of the filters F and G.        *)
(*   \forall x \near F & y \near G, P x y := {near F & G, forall x y, P x y}. *)
(*     \forall x & y \near F, P x y == same as before, with G = F.            *)
(*               \near x & y, P x y := \forall z \near x & t \near y, P x y.  *)
(*                     x \is_near F == x belongs to a set P : in_filter F.    *)
(*   --> Tactics:                                                             *)
(*     - near=> x    introduces x:                                            *)
(*       On the goal \forall x \near F, G x, introduces the variable x and an *)
(*       "existential", and unaccessible hypothesis ?H x and asks the user to *)
(*       prove (G x) in this context.                                         *)
(*       Under the hood delays the proof of F ?H and waits for near: x        *)
(*       Also exists under the form near=> x y.                               *)
(*     - near: x     discharges x:                                            *)
(*       On the goal H_i x, and where x \is_near F, it asks the user to prove *)
(*       that (\forall x \near F, H_i x), provided that H_i x does not depend *)
(*       on variables introduced after x.                                     *)
(*       Under the hood, it refines by intersection the existential variable  *)
(*       ?H attached to x, computes the intersection with F, and asks the     *)
(*       user to prove F H_i, right now                                       *)
(*     - end_near should be used to close remaining existentials trivially    *)
(*     - near F => x     poses a variable near F, where F is a proper filter  *)
(*       adds to the context a variable x that \is_near F, i.e. one may       *)
(*       assume H x for any H in F. This new variable x can be dealt with     *)
(*       using  near: x, as for variables introduced by near=>.               *)
(*                                                                            *)
(* * Topology :                                                               *)
(*                  topologicalType == interface type for topological space   *)
(*                                     structure.                             *)
(* TopologicalMixin nbhs_filt nbhsE == builds the mixin for a topological     *)
(*                                     space from the proofs that nbhs        *)
(*                                     outputs proper filters and defines the *)
(*                                     same notion of neighbourhood as the    *)
(*                                     open sets.                             *)
(* topologyOfFilterMixin nbhs_filt nbhs_sing nbhs_nbhs == builds the mixin    *)
(*                                     for a topological space from the       *)
(*                                     properties of nbhs and hence assumes   *)
(*                                     that the carrier is a filterType       *)
(*   topologyOfOpenMixin opT opI op_bigU == builds the mixin for a            *)
(*                                     topological space from the properties  *)
(*                                     of open sets, assuming the carrier is  *)
(*                                     a pointed type. nbhs_of_open must be   *)
(*                                     used to declare a filterType.          *)
(*   topologyOfBaseMixin b_cover b_join == builds the mixin for a topological *)
(*                                     space from the properties of a base of *)
(*                                     open sets; the type of indices must be *)
(*                                     a pointedType, as well as the carrier. *)
(*                                     nbhs_of_open \o open_from must be      *)
(*                                     used to declare a filterType           *)
(*                 filterI_iter F n == nth stage of recursively building the  *)
(*                                     filter of finite intersections of F    *)
(*                    finI_from D f == set of \bigcap_(i in E) f i where E is *)
(*                                     a finite subset of D                   *)
(*       topologyOfSubbaseMixin D b == builds the mixin for a topological     *)
(*                                     space from a subbase of open sets b    *)
(*                                     indexed on domain D; the type of       *)
(*                                     indices must be a pointedType.         *)
(*              TopologicalType T m == packs the mixin m to build a           *)
(*                                     topologicalType; T must have a         *)
(*                                     canonical structure of filteredType T. *)
(*           weak_topologicalType f == weak topology by f : S -> T on S; S    *)
(*                                     must be a pointedType and T a          *)
(*                                     topologicalType.                       *)
(*           sup_topologicalType Tc == supremum topology of the family of     *)
(*                                     topologicalType structures Tc on T; T  *)
(*                                     must be a pointedType.                 *)
(*        product_topologicalType T == product topology of the family of      *)
(*                                     topologicalTypes T.                    *)
(*    [topologicalType of T for cT] == T-clone of the topologicalType         *)
(*                                     structure cT.                          *)
(*           [topologicalType of T] == clone of a canonical structure of      *)
(*                                     topologicalType on T.                  *)
(*                             open == set of open sets.                      *)
(*                      open_nbhs p == set of open neighbourhoods of p.       *)
(*                          basis B == a family of open sets that converges   *)
(*                                     to each point                          *)
(*               second_countable T == T has a countable basis                *)
(*                    continuous f <-> f is continuous w.r.t the topology.    *)
(*                              x^' == set of neighbourhoods of x where x is  *)
(*                                     excluded (a "deleted neighborhood").   *)
(*                        closure A == closure of the set A.                  *)
(*                    limit_point E == the set of limit points of E           *)
(*                           closed == set of closed sets.                    *)
(*                        cluster F == set of cluster points of F.            *)
(*                          compact == set of compact sets w.r.t. the filter- *)
(*                                     based definition of compactness.       *)
(*                   compact_near F == the filter F contains a closed comapct *)
(*                                     set                                    *)
(*                     precompact A == The set A is contained in a closed and *)
(*                                     compact set                            *)
(*                locally_compact A == every point in A has a compact         *)
(*                                     (and closed) neighborhood              *)
(*               hausdorff_space T <-> T is a Hausdorff space (T_2).          *)
(*                discrete_space T <-> every nbhs is a principal filter       *)
(*        finite_subset_cover D F A == the family of sets F is a cover of A   *)
(*                                     for a finite number of indices in D    *)
(*                    cover_compact == set of compact sets w.r.t. the open    *)
(*                                     cover-based definition of compactness. *)
(*                    near_covering == a reformulation of covering compact    *)
(*                                     better suited for use with `near`      *)
(*                     connected A <-> the only non empty subset of A which   *)
(*                                     is both open and closed in A is A.     *)
(*              kolmogorov_space T <-> T is a Kolmogorov space (T_0).         *)
(*              accessible_space T <-> T is an accessible space (T_1).        *)
(*                    separated A B == the two sets A and B are separated     *)
(*                      component x == the connected component of point x     *)
(*                    perfect_set A == A is closed, and is every point in A   *)
(*                                     is a limit point of A.                 *)
(*           totally_disconnected A == The only connected subsets of A are    *)
(*                                     empty or singletons.                   *)
(*               zero_dimensional T == Points are separable by a clopen set.  *)
(*                       set_nbhs A == filter from open sets containing A     *)
(*                                                                            *)
(*                                                                            *)
(*                      [locally P] := forall a, A a -> G (within A (nbhs x)) *)
(*                                     if P is convertible to G (globally A)  *)
(*              quotient_topology Q == the quotient topology corresponding to *)
(*                                     quotient Q : quotType T where T has    *)
(*                                     type topologicalType                   *)
(*                                                                            *)
(* * Function space topologies :                                              *)
(*     {uniform` A -> V} == The space U -> V, equipped with the topology of   *)
(*                          uniform convergence from a set A to V, where      *)
(*                          V is a uniformType.                               *)
(*      {uniform U -> V} := {uniform` [set: U] -> V}                          *)
(*  {uniform A, F --> f} == F converges to f in {uniform A -> V}.             *)
(*    {uniform, F --> f} := {uniform setT, F --> f}                           *)
(*         {ptws U -> V} == The space U -> V, equipped with the topology of   *)
(*                          pointwise convergence from U to V, where V is a   *)
(*                          topologicalType; notation for @fct_Pointwise U V. *)
(*       {ptws, F --> f} == F converges to f in {ptws U -> V}.                *)
(*  {family fam, U -> V} == The space U -> V, equipped with the supremum      *)
(*                          topology of {uniform A -> f} for each A in 'fam'  *)
(*                          In particular {family compact, U -> V} is the     *)
(*                          topology of compact convergence.                  *)
(* {family fam, F --> f} == F converges to f in {family fam, U -> V}.         *)
(*                                                                            *)
(* --> We used these topological notions to prove Tychonoff's Theorem, which  *)
(*     states that any product of compact sets is compact according to the    *)
(*     product topology.                                                      *)
(* * Uniform spaces :                                                         *)
(*                      nbhs_ ent == neighbourhoods defined using entourages  *)
(*                    uniformType == interface type for uniform spaces: a     *)
(*                                   type equipped with entourages            *)
(*   UniformMixin efilter erefl einv esplit nbhse == builds the mixin for a   *)
(*                                   uniform space from the properties of     *)
(*                                   entourages and the compatibility between *)
(*                                   entourages and nbhs                      *)
(*                UniformType T m == packs the uniform space mixin into a     *)
(*                                   uniformType. T must have a canonical     *)
(*                                   structure of topologicalType             *)
(*      [uniformType of T for cT] == T-clone of the uniformType structure cT  *)
(*             [uniformType of T] == clone of a canonical structure of        *)
(*                                   uniformType on T                         *)
(*   topologyOfEntourageMixin umixin == builds the mixin for a topological    *)
(*                                   space from a mixin for a uniform space   *)
(*                      entourage == set of entourages in a uniform space     *)
(*                    split_ent E == when E is an entourage, split_ent E is   *)
(*                                   an entourage E' such that E' \o E' is    *)
(*                                   included in E when seen as a relation    *)
(*                   unif_continuous f <-> f is uniformly continuous.         *)
(*               weak_uniformType == the uniform space for weak topologies    *)
(*                sup_uniformType == the uniform space for sup topologies     *)
(*         countable_uniformity T == T's entourage has a countable base. This *)
(*                                   is equivalent to `T` being metrizable    *)
(*                        gauge E == For an entourage E, gauge E is a filter  *)
(*                                   which includes `iter n split_ent E`.     *)
(*                                   Critically, `gauge E` forms a uniform    *)
(*                                   space with a countable uniformity        *)
(*       gauge_psuedoMetricType E == the pseudoMetricType associated with the *)
(*                                   `gauge E`                                *)
(*                   discrete_ent == entourages for the discrete topology     *)
(*                                                                            *)
(* * PseudoMetric spaces :                                                    *)
(*                entourage_ ball == entourages defined using balls           *)
(*               pseudoMetricType == interface type for pseudo metric space   *)
(*                                   structure: a type equipped with balls.   *)
(*  PseudoMetricMixin brefl bsym btriangle nbhsb == builds the mixin for a    *)
(*                                   pseudo metric space from the properties  *)
(*                                   of balls and the compatibility between   *)
(*                                   balls and entourages.                    *)
(*           PseudoMetricType T m == packs the pseudo metric space mixin into *)
(*                                   a pseudoMetricType. T must have a        *)
(*                                   canonical structure of uniformType.      *)
(* [pseudoMetricType R of T for cT] == T-clone of the pseudoMetricType        *)
(*                                   structure cT, with R the ball radius.    *)
(*      [pseudoMetricType R of T] == clone of a canonical structure of        *)
(*                                   pseudoMetricType on T, with R the ball   *)
(*                                   radius.                                  *)
(*   uniformityOfBallMixin umixin == builds the mixin for a topological space *)
(*                                   from a mixin for a pseudoMetric space.   *)
(*                       ball x e == ball of center x and radius e.           *)
(*                nbhs_ball_ ball == nbhs defined using the given balls       *)
(*                      nbhs_ball == nbhs defined using balls in a            *)
(*                                   pseudometric space                       *)
(*                     close x y <-> x and y are arbitrarily close w.r.t. to  *)
(*                                   balls.                                   *)
(*          weak_pseudoMetricType == the metric space for weak topologies     *)
(*            quotient_topology Q == the quotient topology corresponding to   *)
(*                                   quotient Q : quotType T. where T has     *)
(*                                   type topologicalType                     *)
(*                  discrete_ball == singleton balls for thediscrete topology *)
(*                                                                            *)
(* * Complete uniform spaces :                                                *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (entourage definition)                   *)
(*                   completeType == interface type for a complete uniform    *)
(*                                   space structure.                         *)
(*       CompleteType T cvgCauchy == packs the proof that every proper cauchy *)
(*                                   filter on T converges into a             *)
(*                                   completeType structure; T must have a    *)
(*                                   canonical structure of uniformType.      *)
(*     [completeType of T for cT] == T-clone of the completeType structure    *)
(*                                   cT.                                      *)
(*            [completeType of T] == clone of a canonical structure of        *)
(*                                   completeType on T.                       *)
(*                                                                            *)
(* * Complete pseudometric spaces :                                           *)
(*                   cauchy_ex F <-> the set of sets F is a cauchy filter     *)
(*                                   (epsilon-delta definition).              *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (using the near notations).              *)
(*       completePseudoMetricType == interface type for a complete            *)
(*                                   pseudometric space structure.            *)
(* CompletePseudoMetricType T cvgCauchy == packs the proof that every proper  *)
(*                                   cauchy filter on T converges into a      *)
(*                                   completePseudoMetricType structure; T    *)
(*                                   must have a canonical structure of       *)
(*                                   pseudoMetricType.                        *)
(* [completePseudoMetricType of T for cT] == T-clone of the                   *)
(*                                   completePseudoMetricType structure cT.   *)
(* [completePseudoMetricType of T] == clone of a canonical structure of       *)
(*                                   completePseudoMetricType on T.           *)
(*                                                                            *)
(*                        ball_ N == balls defined by the norm/absolute       *)
(*                                   value N                                  *)
(*                        dense S == the set (S : set T) is dense in T, with  *)
(*                                   T of type topologicalType                *)
(*                                                                            *)
(* * Subspaces of topological spaces :                                        *)
(*                 subspace A == for (A : set T), this is a copy of T with    *)
(*                               a topology that ignores points outside A     *)
(*            incl_subspace x == with x of type subspace A with (A : set T),  *)
(*                               inclusion of subspace A into T               *)
(*                                                                            *)
(* * Arzela Ascoli' theorem :                                                 *)
(*            singletons T := [set [set x] | x in [set: T]].                  *)
(*      equicontinuous W x == the set (W : X -> Y) is equicontinuous at x     *)
(*  pointwise_precompact W == For each (x : X), set of images [f x | f in W]  *)
(*                            is precompact                                   *)
(*                                                                            *)
(* We endow several standard types with the types of topological notions:     *)
(* - products: prod_topologicalType, prod_uniformType, prod_pseudoMetricType  *)
(*     sup_pseudoMetricType, weak_pseudoMetricType, product_pseudoMetricType  *)
(* - matrices: matrix_filtered, matrix_topologicalType, matrix_uniformType,   *)
(*     matrix_pseudoMetricType, matrix_completeType,                          *)
(*     matrix_completePseudoMetricType                                        *)
(* - nat: nat_filteredType, nat_topologicalType                               *)
(* - numFieldType: numField_filteredType, numField_topologicalType,           *)
(*     numField_uniformType, numField_pseudoMetricType (accessible with       *)
(*     "Import numFieldTopology.Exports.")                                    *)
(******************************************************************************)

Reserved Notation "{ 'near' x , P }" (at level 0, format "{ 'near'  x ,  P }").
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x name, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "'\near' x , P"
  (at level 200, x at level 99, P at level 200,
   format "'\near'  x ,  P", only parsing).
Reserved Notation "{ 'near' x & y , P }"
  (at level 0, format "{ 'near'  x  &  y ,  P }").
Reserved Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P"
  (at level 200, x name, y name, P at level 200,
   format "'\forall'  x  '\near'  x_0  &  y  '\near'  y_0 ,  P").
Reserved Notation "'\forall' x & y '\near' z , P"
  (at level 200, x name, y name, P at level 200,
   format "'\forall'  x  &  y  '\near'  z ,  P").
Reserved Notation "'\near' x & y , P"
  (at level 200, x, y at level 99, P at level 200,
   format "'\near'  x  &  y ,  P", only parsing).
Reserved Notation "[ 'filter' 'of' x ]" (format "[ 'filter'  'of'  x ]").
Reserved Notation "F `=>` G" (at level 70, format "F  `=>`  G").
Reserved Notation "F --> G" (at level 70, format "F  -->  G").
Reserved Notation "[ 'lim' F 'in' T ]" (format "[ 'lim'  F  'in'  T ]").
Reserved Notation "[ 'cvg' F 'in' T ]" (format "[ 'cvg'  F  'in'  T ]").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").
Reserved Notation "E @[ x --> F ]"
  (at level 60, x name, format "E  @[ x  -->  F ]").
Reserved Notation "f @ F" (at level 60, format "f  @  F").
Reserved Notation "E `@[ x --> F ]"
  (at level 60, x name, format "E  `@[ x  -->  F ]").
Reserved Notation "f `@ F" (at level 60, format "f  `@  F").
Reserved Notation "A ^°" (at level 1, format "A ^°").
Reserved Notation "[ 'locally' P ]" (at level 0, format "[ 'locally'  P ]").
Reserved Notation "x ^'" (at level 2, format "x ^'").
Reserved Notation "{ 'within' A , 'continuous' f }"
  (at level 70, A at level 69, format "{ 'within'  A ,  'continuous'  f }").
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Making sure that [Program] does not automatically introduce *)
Obligation Tactic := idtac.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section bigmaxmin.
Local Notation max := Order.max.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : unit) (T : orderType d) (x : T) (I : finType) (P : pred I)
          (m : T) (F : I -> T).

Lemma bigmax_geP : reflect (m <= x \/ exists2 i, P i & m <= F i)
                           (m <= \big[max/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[mx|[i Pi mFi]]].
- rewrite leNgt => /bigmax_ltP /not_andP[/negP|]; first by rewrite -leNgt; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -leNgt; right; exists i.
- by rewrite bigmax_idl le_maxr mx.
- by rewrite (bigmaxD1 i)// le_maxr mFi.
Qed.

Lemma bigmax_gtP : reflect (m < x \/ exists2 i, P i & m < F i)
                           (m < \big[max/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[mx|[i Pi mFi]]].
- rewrite ltNge => /bigmax_leP /not_andP[/negP|]; first by rewrite -ltNge; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -ltNge; right; exists i.
- by rewrite bigmax_idl lt_maxr mx.
- by rewrite (bigmaxD1 i)// lt_maxr mFi.
Qed.

Lemma bigmin_leP : reflect (x <= m \/ exists2 i, P i & F i <= m)
                           (\big[min/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[xm|[i Pi Fim]]].
- rewrite leNgt => /bigmin_gtP /not_andP[/negP|]; first by rewrite -leNgt; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -leNgt; right; exists i.
- by rewrite bigmin_idl le_minl xm.
- by rewrite (bigminD1 i)// le_minl Fim.
Qed.

Lemma bigmin_ltP : reflect (x < m \/ exists2 i, P i & F i < m)
                           (\big[min/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[xm|[i Pi Fim]]].
- rewrite ltNge => /bigmin_geP /not_andP[/negP|]; first by rewrite -ltNge; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -ltNge; right; exists i.
- by rewrite bigmin_idl lt_minl xm.
- by rewrite (bigminD1 _ _ _ Pi) lt_minl Fim.
Qed.

End bigmaxmin.

Definition monotonous d (T : porderType d) (pT : predType T) (A : pT) (f : T -> T) :=
  {in A &, {mono f : x y / (x <= y)%O}} \/ {in A &, {mono f : x y /~ (x <= y)%O}}.

Lemma and_prop_in (T : Type) (p : mem_pred T) (P Q : T -> Prop) :
  {in p, forall x, P x /\ Q x} <->
  {in p, forall x, P x} /\ {in p, forall x, Q x}.
Proof.
split=> [cnd|[cnd1 cnd2] x xin]; first by split=> x xin; case: (cnd x xin).
by split; [apply: cnd1 | apply: cnd2].
Qed.

Lemma mem_inc_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y / (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f a, f b]}.
Proof.
move=> fle x xab; have leab : (a <= b)%O by rewrite (itvP xab).
by rewrite in_itv/= !fle ?(itvP xab).
Qed.

Lemma mem_dec_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y /~ (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f b, f a]}.
Proof.
move=> fge x xab; have leab : (a <= b)%O by rewrite (itvP xab).
by rewrite in_itv/= !fge ?(itvP xab).
Qed.

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Canonical linear_eqType := EqType {linear U -> V | s} gen_eqMixin.
Canonical linear_choiceType := ChoiceType {linear U -> V | s} gen_choiceMixin.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).
Canonical linear_pointedType := PointedType {linear U -> V | GRing.Scale.op s_law}
                                            (@GRing.null_fun_linear R U V s s_law).
End Linear2.

Module Filtered.

(* Index a family of filters on a type, one for each element of the type *)
Definition nbhs_of U T := T -> set (set U).
Record class_of U T := Class {
  base : Pointed.class_of T;
  nbhs_op : nbhs_of U T
}.

Section ClassDef.
Variable U : Type.

Structure type := Pack { sort; _ : class_of U sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of U cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of U xT).
Local Coercion base : class_of >-> Pointed.class_of.

Definition pack m :=
  fun bT b of phant_id (Pointed.class bT) b => @Pack T (Class b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition fpointedType := @Pointed.Pack cT xclass.

End ClassDef.

(* filter on arrow sources *)
Structure source Z Y := Source {
  source_type :> Type;
  _ : (source_type -> Z) -> set (set Y)
}.
Definition source_filter Z Y (F : source Z Y) : (F -> Z) -> set (set Y) :=
  let: Source X f := F in f.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Pointed.class_of.
Coercion nbhs_op : class_of >-> nbhs_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion fpointedType : type >-> Pointed.type.
Canonical fpointedType.
Notation filteredType := type.
Notation FilteredType U T m := (@pack U T m _ _ idfun).
Notation "[ 'filteredType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'filteredType'  U  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'filteredType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'filteredType'  U  'of'  T ]") : form_scope.

(* The default filter for an arbitrary element is the one obtained *)
(* from its type *)
Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  FilteredType Y (X -> Z) (@source_filter _ _ X).
Canonical source_filter_filter Y :=
  @Source Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).
Canonical source_filter_filter' Y :=
  @Source Prop _ (set _) (fun x : (set (set Y)) => x).

End Exports.
End Filtered.
Export Filtered.Exports.

Definition nbhs {U} {T : filteredType U} : T -> set (set U) :=
  Filtered.nbhs_op (Filtered.class T).
Arguments nbhs {U T} _ _ : simpl never.

Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T) :=
  [set P | exists2 i, D i & B i `<=` P].

(* the canonical filter on matrices on X is the product of the canonical filter
   on X *)
Canonical matrix_filtered m n X (Z : filteredType X) : filteredType 'M[X]_(m, n) :=
  FilteredType 'M[X]_(m, n) 'M[Z]_(m, n) (fun mx => filter_from
    [set P | forall i j, nbhs (mx i j) (P i j)]
    (fun P => [set my : 'M[X]_(m, n) | forall i j, P i j (my i j)])).

Definition filter_prod {T U : Type}
  (F : set (set T)) (G : set (set U)) : set (set (T * U)) :=
  filter_from (fun P => F P.1 /\ G P.2) (fun P => P.1 `*` P.2).

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X} {fX : filteredType X} (x : fX)
   P (phP : ph {all1 P}) := nbhs x P.

Definition prop_near2 {X X'} {fX : filteredType X} {fX' : filteredType X'}
  (x : fX) (x' : fX') := fun P of ph {all2 P} =>
  filter_prod (nbhs x) (nbhs x') (fun x => P x.1 x.2).

End Near.

Notation "{ 'near' x , P }" := (@prop_near1 _ _ x _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 , P" := {near x_0, forall x, P} : type_scope.
Notation "'\near' x , P" := (\forall x \near x, P) : type_scope.
Notation "{ 'near' x & y , P }" :=
  (@prop_near2 _ _ _ _ x y _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P" :=
  {near x_0 & y_0, forall x y, P} : type_scope.
Notation "'\forall' x & y '\near' z , P" :=
  {near z & z, forall x y, P} : type_scope.
Notation "'\near' x & y , P" := (\forall x \near x & y \near y, P) : type_scope.
Arguments prop_near1 : simpl never.
Arguments prop_near2 : simpl never.

Lemma nearE {T} {F : set (set T)} (P : set T) : (\forall x \near F, P x) = F P.
Proof. by []. Qed.

Lemma eq_near {T} {F : set (set T)} (P Q : set T) :
   (forall x, P x <-> Q x) ->
   (\forall x \near F, P x) = (\forall x \near F, Q x).
Proof. by move=> /predeqP ->. Qed.

Definition filter_of X (fX : filteredType X) (x : fX) of phantom fX x :=
   nbhs x.
Notation "[ 'filter' 'of' x ]" :=
  (@filter_of _ _ _ (Phantom _ x)) : classical_set_scope.
Arguments filter_of _ _ _ _ _ /.

Lemma filter_of_filterE {T : Type} (F : set (set T)) : [filter of F] = F.
Proof. by []. Qed.

Lemma nbhs_filterE {T : Type} (F : set (set T)) : nbhs F = F.
Proof. by []. Qed.

Module Export NbhsFilter.
Definition nbhs_simpl := (@filter_of_filterE, @nbhs_filterE).
End NbhsFilter.

Definition cvg_to {T : Type} (F G : set (set T)) := G `<=` F.
Notation "F `=>` G" := (cvg_to F G) : classical_set_scope.
Lemma cvg_refl T (F : set (set T)) : F `=>` F.
Proof. exact. Qed.
Arguments cvg_refl {T F}.
#[global] Hint Resolve cvg_refl : core.

Lemma cvg_trans T (G F H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Notation "F --> G" := (cvg_to [filter of F] [filter of G]) : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filteredType U) :=
  fun F : set (set U) => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T [filter of F]) : classical_set_scope.
Notation lim F := [lim F in [filteredType _ of @type_of_filter _ [filter of F]]].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := [cvg F in [filteredType _ of @type_of_filter _ [filter of F]]].

Section FilteredTheory.

Canonical filtered_prod X1 X2 (Z1 : filteredType X1)
  (Z2 : filteredType X2) : filteredType (X1 * X2) :=
  FilteredType (X1 * X2) (Z1 * Z2)
    (fun x => filter_prod (nbhs x.1) (nbhs x.2)).

Lemma cvg_prod T {U U' V V' : filteredType T} (x : U) (l : U') (y : V) (k : V') :
  x --> l -> y --> k -> (x, y) --> (l, k).
Proof.
move=> xl yk X [[X1 X2] /= [HX1 HX2] H]; exists (X1, X2) => //=.
split; [exact: xl | exact: yk].
Qed.

Lemma cvg_ex {U : Type} (T : filteredType U) (F : set (set U)) :
  [cvg F in T] <-> (exists l : T, F --> l).
Proof. by split=> [cvg|/getPex//]; exists [lim F in T]. Qed.

Lemma cvgP {U : Type} (T : filteredType U) (F : set (set U)) (l : T) :
   F --> l -> [cvg F in T].
Proof. by move=> Fl; apply/cvg_ex; exists l. Qed.

Lemma cvg_toP {U : Type} (T : filteredType U) (F : set (set U)) (l : T) :
   [cvg F in T] -> [lim F in T] = l -> F --> l.
Proof. by move=> /[swap]->. Qed.

Lemma dvgP {U : Type} (T : filteredType U) (F : set (set U)) :
  ~ [cvg F in T] -> [lim F in T] = point.
Proof. by rewrite /lim_in /=; case xgetP. Qed.

Lemma cvgNpoint {U} (T : filteredType U) (F : set (set U)) :
  [lim F in T] != point -> [cvg F in T].
Proof. by apply: contra_neqP; apply: dvgP. Qed.

End FilteredTheory.
Arguments cvgP {U T F} l.
Arguments dvgP {U} T {F}.

Lemma nbhs_nearE {U} {T : filteredType U} (x : T) (P : set U) :
  nbhs x P = \near x, P x.
Proof. by []. Qed.

Lemma near_nbhs {U} {T : filteredType U} (x : T) (P : set U) :
  (\forall x \near nbhs x, P x) = \near x, P x.
Proof. by []. Qed.

Lemma near2_curry {U V} (F : set (set U)) (G : set (set V)) (P : U -> set V) :
  {near F & G, forall x y, P x y} = {near (F, G), forall x, P x.1 x.2}.
Proof. by []. Qed.

Lemma near2_pair {U V} (F : set (set U)) (G : set (set V)) (P : set (U * V)) :
  {near F & G, forall x y, P (x, y)} = {near (F, G), forall x, P x}.
Proof. by symmetry; congr (nbhs _); rewrite predeqE => -[]. Qed.

Definition near2E := (@near2_curry, @near2_pair).

Lemma filter_of_nearI (X : Type) (fX : filteredType X)
  (x : fX) (ph : phantom fX x) : forall P,
  @filter_of X fX x ph P = @prop_near1 X fX x P (inPhantom (forall x, P x)).
Proof. by []. Qed.

Module Export NearNbhs.
Definition near_simpl := (@near_nbhs, @nbhs_nearE, filter_of_nearI).
Ltac near_simpl := rewrite ?near_simpl.
End NearNbhs.

Lemma near_swap {U V} (F : set (set U)) (G : set (set V)) (P : U -> set V) :
  (\forall x \near F & y \near G, P x y) = (\forall y \near G & x \near F, P x y).
Proof.
rewrite propeqE; split => -[[/=A B] [FA FB] ABP];
by exists (B, A) => // -[x y] [/=Bx Ay]; apply: (ABP (y, x)).
Qed.

(** * Filters *)

(** ** Definitions *)

Class Filter {T : Type} (F : set (set T)) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.
Global Hint Mode Filter - ! : typeclass_instances.

Class ProperFilter' {T : Type} (F : set (set T)) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' : Filter F
}.
(* TODO: Reuse :> above and remove the following line and the coercion below
   after 8.17 is the minimum required version for Coq *)
Global Existing Instance filter_filter'.
Global Hint Mode ProperFilter' - ! : typeclass_instances.
Arguments filter_not_empty {T} F {_}.

Notation ProperFilter := ProperFilter'.

Lemma filter_setT (T' : Type) : Filter [set: set T'].
Proof. by constructor. Qed.

Lemma filterP_strong T (F : set (set T)) {FF : Filter F} (P : set T) :
  (exists Q : set T, exists FQ  : F Q, forall x : T, Q x -> P x) <-> F P.
Proof.
split; last by exists P.
by move=> [Q [FQ QP]]; apply: (filterS QP).
Qed.

Structure filter_on T := FilterType {
  filter :> (T -> Prop) -> Prop;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F :=
  let: FilterType _ class := F in class.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.
(* Typeclasses Opaque filter. *)
Coercion filter_filter' : ProperFilter >-> Filter.

Structure pfilter_on T := PFilterPack {
  pfilter :> (T -> Prop) -> Prop;
  _ : ProperFilter pfilter
}.
Definition pfilter_class T (F : pfilter_on T) : ProperFilter F :=
  let: PFilterPack _ class := F in class.
Arguments PFilterPack {T} _ _.
#[global] Existing Instance pfilter_class.
(* Typeclasses Opaque pfilter. *)
Canonical pfilter_filter_on T (F : pfilter_on T) :=
  FilterType F (pfilter_class F).
Coercion pfilter_filter_on : pfilter_on >-> filter_on.
Definition PFilterType {T} (F : (T -> Prop) -> Prop)
  {fF : Filter F} (fN0 : not (F set0)) :=
  PFilterPack F (Build_ProperFilter' fN0 fF).
Arguments PFilterType {T} F {fF} fN0.

Canonical filter_on_eqType T := EqType (filter_on T) gen_eqMixin.
Canonical filter_on_choiceType T :=
  ChoiceType (filter_on T) gen_choiceMixin.
Canonical filter_on_PointedType T :=
  PointedType (filter_on T) (FilterType _ (filter_setT T)).
Canonical filter_on_FilteredType T :=
  FilteredType T (filter_on T) (@filter T).

Global Instance filter_on_Filter T (F : filter_on T) : Filter F.
Proof. by case: F. Qed.
Global Instance pfilter_on_ProperFilter T (F : pfilter_on T) : ProperFilter F.
Proof. by case: F. Qed.

Lemma nbhs_filter_onE T (F : filter_on T) : nbhs F = nbhs (filter F).
Proof. by []. Qed.
Definition nbhs_simpl := (@nbhs_simpl, @nbhs_filter_onE).

Lemma near_filter_onE T (F : filter_on T) (P : set T) :
  (\forall x \near F, P x) = \forall x \near filter F, P x.
Proof. by []. Qed.
Definition near_simpl := (@near_simpl, @near_filter_onE).

Program Definition trivial_filter_on T := FilterType [set setT : set T] _.
Next Obligation.
split=> // [_ _ -> ->|Q R sQR QT]; first by rewrite setIT.
by move; rewrite eqEsubset; split => // ? _; apply/sQR; rewrite QT.
Qed.
Canonical trivial_filter_on.

Lemma filter_nbhsT {T : Type} (F : set (set T)) :
   Filter F -> nbhs F setT.
Proof. by move=> FF; apply: filterT. Qed.
#[global] Hint Resolve filter_nbhsT : core.

Lemma nearT {T : Type} (F : set (set T)) : Filter F -> \near F, True.
Proof. by move=> FF; apply: filterT. Qed.
#[global] Hint Resolve nearT : core.

Lemma filter_not_empty_ex {T : Type} (F : set (set T)) :
    (forall P, F P -> exists x, P x) -> ~ F set0.
Proof. by move=> /(_ set0) ex /ex []. Qed.

Definition Build_ProperFilter {T : Type} (F : set (set T))
  (filter_ex : forall P, F P -> exists x, P x)
  (filter_filter : Filter F) :=
  Build_ProperFilter' (filter_not_empty_ex filter_ex) (filter_filter).

Lemma filter_ex_subproof {T : Type} (F : set (set T)) :
     ~ F set0 -> (forall P, F P -> exists x, P x).
Proof.
move=> NFset0 P FP; apply: contra_notP NFset0 => nex; suff <- : P = set0 by [].
by rewrite funeqE => x; rewrite propeqE; split=> // Px; apply: nex; exists x.
Qed.

Definition filter_ex {T : Type} (F : set (set T)) {FF : ProperFilter F} :=
  filter_ex_subproof (filter_not_empty F).
Arguments filter_ex {T F FF _}.

Lemma filter_getP {T : pointedType} (F : set (set T)) {FF : ProperFilter F}
      (P : set T) : F P -> P (get P).
Proof. by move=> /filter_ex /getPex. Qed.

(* Near Tactic *)

Record in_filter T (F : set (set T)) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.
(* add ball x e as a canonical instance of nbhs x *)

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set (set T)), in_filter F -> T -> Prop.
Axiom tE : t = prop_in_filter_proj.
End PropInFilterSig.
Module PropInFilter : PropInFilterSig.
Definition t := prop_in_filter_proj.
Lemma tE : t = prop_in_filter_proj. Proof. by []. Qed.
End PropInFilter.
(* Coercion PropInFilter.t : in_filter >-> Funclass. *)
Notation prop_of := PropInFilter.t.
Definition prop_ofE := PropInFilter.tE.
Notation "x \is_near F" := (@PropInFilter.t _ F _ x).
Definition is_nearE := prop_ofE.

Lemma prop_ofP T F (iF : @in_filter T F) : F (prop_of iF).
Proof. by rewrite prop_ofE; apply: prop_in_filterP_proj. Qed.

Definition in_filterT T F (FF : Filter F) : @in_filter T F :=
  InFilter (filterT).
Canonical in_filterI T F (FF : Filter F) (P Q : @in_filter T F) :=
  InFilter (filterI (prop_in_filterP_proj P) (prop_in_filterP_proj Q)).

Lemma filter_near_of T F (P : @in_filter T F) (Q : set T) : Filter F ->
  (forall x, prop_of P x -> Q x) -> F Q.
Proof.
by move: P => [P FP] FF /=; rewrite prop_ofE /= => /filterS; apply.
Qed.

Fact near_key : unit. Proof. exact. Qed.

Lemma mark_near (P : Prop) : locked_with near_key P -> P.
Proof. by rewrite unlock. Qed.

Lemma near_acc T F (P : @in_filter T F) (Q : set T) (FF : Filter F)
   (FQ : \forall x \near F, Q x) :
   locked_with near_key (forall x, prop_of (in_filterI FF P (InFilter FQ)) x -> Q x).
Proof. by rewrite unlock => x /=; rewrite !prop_ofE /= => -[Px]. Qed.

Lemma near_skip_subproof T F (P Q : @in_filter T F) (G : set T) (FF : Filter F) :
   locked_with near_key (forall x, prop_of P x -> G x) ->
   locked_with near_key (forall x, prop_of (in_filterI FF P Q) x -> G x).
Proof.
rewrite !unlock => FG x /=; rewrite !prop_ofE /= => -[Px Qx].
by have /= := FG x; apply; rewrite prop_ofE.
Qed.

Tactic Notation "near=>" ident(x) := apply: filter_near_of => x ?.

Ltac just_discharge_near x :=
  tryif match goal with Hx : x \is_near _ |- _ => move: (x) (Hx); apply: mark_near end
        then idtac else fail "the variable" x "is not a ""near"" variable".
Ltac near_skip :=
  match goal with |- locked_with near_key (forall _, @PropInFilter.t _ _ ?P _ -> _) =>
    tryif is_evar P then fail "nothing to skip" else apply: near_skip_subproof end.

Tactic Notation "near:" ident(x) :=
  just_discharge_near x;
  tryif do ![apply: near_acc; first shelve|near_skip]
  then idtac
  else fail "the goal depends on variables introduced after" x.

Ltac under_near i tac := near=> i; tac; near: i.
Tactic Notation "near=>" ident(i) "do" tactic3(tac) := under_near i ltac:(tac).
Tactic Notation "near=>" ident(i) "do" "[" tactic4(tac) "]" := near=> i do tac.
Tactic Notation "near" "do" tactic3(tac) :=
  let i := fresh "i" in under_near i ltac:(tac).
Tactic Notation "near" "do" "[" tactic4(tac) "]" := near do tac.

Ltac end_near := do ?exact: in_filterT.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end
   | match goal with |- ?x \is_near _ => near: x; apply: prop_ofP end ].

Lemma have_near (U : Type) (fT : filteredType U) (x : fT) (P : Prop) :
  ProperFilter (nbhs x) -> (\forall x \near x, P) -> P.
Proof. by move=> FF nP; have [] := @filter_ex _ _ FF (fun=> P). Qed.
Arguments have_near {U fT} x.

Tactic Notation "near" constr(F) "=>" ident(x) :=
  apply: (have_near F); near=> x.

Lemma near T (F : set (set T)) P (FP : F P) (x : T)
  (Px : prop_of (InFilter FP) x) : P x.
Proof. by move: Px; rewrite prop_ofE. Qed.
Arguments near {T F P} FP x Px.

Lemma nearW {T : Type} {F : set (set T)} (P : T -> Prop) :
  Filter F -> (forall x, P x) -> (\forall x \near F, P x).
Proof. by move=> FF FP; apply: filterS filterT. Qed.

Lemma filterE {T : Type} {F : set (set T)} :
  Filter F -> forall P : set T, (forall x, P x) -> F P.
Proof. by move=> [FT _ +] P fP => /(_ setT); apply. Qed.

Lemma filter_app (T : Type) (F : set (set T)) :
  Filter F -> forall P Q : set T, F (fun x => P x -> Q x) -> F P -> F Q.
Proof. by move=> FF P Q subPQ FP; near=> x do suff: P x.
Unshelve. all: by end_near. Qed.

Lemma filter_app2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T,  F (fun x => P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Proof. by move=> ???? PQR FP; apply: filter_app; apply: filter_app FP. Qed.

Lemma filter_app3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, F (fun x => P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ????? PQR FP; apply: filter_app2; apply: filter_app FP. Qed.

Lemma filterS2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T, (forall x, P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Proof. by move=> ? ? ? ? ?; apply: filter_app2; apply: filterE. Qed.

Lemma filterS3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, (forall x, P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ? ? ? ? ? ?; apply: filter_app3; apply: filterE. Qed.

Lemma filter_const {T : Type} {F} {FF: @ProperFilter T F} (P : Prop) :
  F (fun=> P) -> P.
Proof. by move=> FP; case: (filter_ex FP). Qed.

Lemma in_filter_from {I T : Type} (D : set I) (B : I -> set T) (i : I) :
  D i -> filter_from D B (B i).
Proof. by exists i. Qed.

Lemma near_andP {T : Type} F (b1 b2 : T -> Prop) : Filter F ->
  (\forall x \near F, b1 x /\ b2 x) <->
    (\forall x \near F, b1 x) /\ (\forall x \near F, b2 x).
Proof.
move=> FF; split=> [H|[H1 H2]]; first by split; apply: filterS H => ? [].
by apply: filterS2 H1 H2.
Qed.

Lemma nearP_dep {T U} {F : set (set T)} {G : set (set U)}
   {FF : Filter F} {FG : Filter G} (P : T -> U -> Prop) :
  (\forall x \near F & y \near G, P x y) ->
  \forall x \near F, \forall y \near G, P x y.
Proof.
move=> [[Q R] [/=FQ GR]] QRP.
by apply: filterS FQ => x Q1x; apply: filterS GR => y Q2y; apply: (QRP (_, _)).
Qed.

Lemma filter2P T U (F : set (set T)) (G : set (set U))
  {FF : Filter F} {FG : Filter G} (P : set (T * U)) :
  (exists2 Q : set T * set U, F Q.1 /\ G Q.2
     & forall (x : T) (y : U), Q.1 x -> Q.2 y -> P (x, y))
   <-> \forall x \near (F, G), P x.
Proof.
split=> [][[A B] /=[FA GB] ABP]; exists (A, B) => //=.
  by move=> [a b] [/=Aa Bb]; apply: ABP.
by move=> a b Aa Bb; apply: (ABP (_, _)).
Qed.

Lemma filter_ex2 {T U : Type} (F : set (set T)) (G : set (set U))
  {FF : ProperFilter F} {FG : ProperFilter G} (P : set T) (Q : set U) :
    F P -> G Q -> exists x : T, exists2 y : U, P x & Q y.
Proof. by move=> /filter_ex [x Px] /filter_ex [y Qy]; exists x, y. Qed.
Arguments filter_ex2 {T U F G FF FG _ _}.

Lemma filter_fromP {I T : Type} (D : set I) (B : I -> set T) (F : set (set T)) :
  Filter F -> F `=>` filter_from D B <-> forall i, D i -> F (B i).
Proof.
split; first by move=> FB i ?; apply/FB/in_filter_from.
by move=> FB P [i Di BjP]; apply: (filterS BjP); apply: FB.
Qed.

Lemma filter_fromTP {I T : Type} (B : I -> set T) (F : set (set T)) :
  Filter F -> F `=>` filter_from setT B <-> forall i, F (B i).
Proof. by move=> FF; rewrite filter_fromP; split=> [P i|P i _]; apply: P. Qed.

Lemma filter_from_filter {I T : Type} (D : set I) (B : I -> set T) :
  (exists i : I, D i) ->
  (forall i j, D i -> D j -> exists2 k, D k & B k `<=` B i `&` B j) ->
  Filter (filter_from D B).
Proof.
move=> [i0 Di0] Binter; constructor; first by exists i0.
  move=> P Q [i Di BiP] [j Dj BjQ]; have [k Dk BkPQ]:= Binter _ _ Di Dj.
  by exists k => // x /BkPQ [/BiP ? /BjQ].
by move=> P Q subPQ [i Di BiP]; exists i => //; apply: subset_trans subPQ.
Qed.

Lemma filter_fromT_filter {I T : Type} (B : I -> set T) :
  (exists _ : I, True) ->
  (forall i j, exists k, B k `<=` B i `&` B j) ->
  Filter (filter_from setT B).
Proof.
move=> [i0 _] BI; apply: filter_from_filter; first by exists i0.
by move=> i j _ _; have [k] := BI i j; exists k.
Qed.

Lemma filter_from_proper {I T : Type} (D : set I) (B : I -> set T) :
  Filter (filter_from D B) ->
  (forall i, D i -> B i !=set0) ->
  ProperFilter (filter_from D B).
Proof.
move=> FF BN0; apply: Build_ProperFilter=> P [i Di BiP].
by have [x Bix] := BN0 _ Di; exists x; apply: BiP.
Qed.

Lemma filter_bigI T (I : choiceType) (D : {fset I}) (f : I -> set T)
  (F : set (set T)) :
  Filter F -> (forall i, i \in D -> F (f i)) ->
  F (\bigcap_(i in [set i | i \in D]) f i).
Proof.
move=> FF FfD.
suff: F [set p | forall i, i \in enum_fset D -> f i p] by [].
have {FfD} : forall i, i \in enum_fset D -> F (f i) by move=> ? /FfD.
elim: (enum_fset D) => [|i s ihs] FfD; first exact: filterS filterT.
apply: (@filterS _ _ _ (f i `&` [set p | forall i, i \in s -> f i p])).
  by move=> p [fip fsp] j; rewrite inE => /orP [/eqP->|] //; apply: fsp.
apply: filterI; first by apply: FfD; rewrite inE eq_refl.
by apply: ihs => j sj; apply: FfD; rewrite inE sj orbC.
Qed.

Lemma filter_forall T (I : finType) (f : I -> set T) (F : set (set T)) :
    Filter F -> (forall i : I, \forall x \near F, f i x) ->
  \forall x \near F, forall i, f i x.
Proof.
move=> FF fIF; apply: filterS (@filter_bigI T I [fset x in I]%fset f F FF _).
  by move=> x fIx i; have := fIx i; rewrite /= inE/=; apply.
by move=> i; rewrite inE/= => _; apply: (fIF i).
Qed.

Lemma filter_imply [T : Type] [P : Prop] [f : set T] [F : set (set T)] :
  Filter F -> (P -> \near F, f F) -> \near F, P -> f F.
Proof.
move=> ? PF; near do move=> /asboolP.
by case: asboolP=> [/PF|_]; by [apply: filterS|apply: nearW].
Unshelve. all: by end_near. Qed.

(** ** Limits expressed with filters *)

Definition fmap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].
Arguments fmap _ _ _ _ _ /.

Lemma fmapE {U V : Type} (f : U -> V)
  (F : set (set U)) (P : set V) : fmap f F P = F (f @^-1` P).
Proof. by []. Qed.

Notation "E @[ x --> F ]" :=
  (fmap (fun x => E) [filter of F]) : classical_set_scope.
Notation "f @ F" := (fmap f [filter of F]) : classical_set_scope.
Global Instance fmap_filter T U (f : T -> U) (F : set (set T)) :
  Filter F -> Filter (f @ F).
Proof.
move=> FF; constructor => [|P Q|P Q PQ]; rewrite ?fmapE ?filter_ofE //=.
- exact: filterT.
- exact: filterI.
- by apply: filterS=> ?/PQ.
Qed.
(*Typeclasses Opaque fmap.*)

Global Instance fmap_proper_filter T U (f : T -> U) (F : set (set T)) :
  ProperFilter F -> ProperFilter (f @ F).
Proof.
move=> FF; apply: Build_ProperFilter';
by rewrite fmapE; apply: filter_not_empty.
Qed.
Definition fmap_proper_filter' := fmap_proper_filter.

Definition fmapi {T U : Type} (f : T -> set U) (F : set (set T)) :=
  [set P | \forall x \near F, exists y, f x y /\ P y].

Notation "E `@[ x --> F ]" :=
  (fmapi (fun x => E) [filter of F]) : classical_set_scope.
Notation "f `@ F" := (fmapi f [filter of F]) : classical_set_scope.

Lemma fmapiE {U V : Type} (f : U -> set V)
  (F : set (set U)) (P : set V) :
  fmapi f F P = \forall x \near F, exists y, f x y /\ P y.
Proof. by []. Qed.

Global Instance fmapi_filter T U (f : T -> set U) (F : set (set T)) :
  infer {near F, is_totalfun f} -> Filter F -> Filter (f `@ F).
Proof.
move=> f_totalfun FF; rewrite /fmapi; apply: Build_Filter.
- by apply: filterS f_totalfun => x [[y Hy] H]; exists y.
- move=> /= P Q FP FQ; near=> x.
    have [//|y [fxy Py]] := near FP x.
    have [//|z [fxz Qz]] := near FQ x.
    have [//|_ fx_prop] := near f_totalfun x.
    by exists y; split => //; split => //; rewrite [y](fx_prop _ z).
- move=> /= P Q subPQ FP; near=> x.
  by have [//|y [fxy /subPQ Qy]] := near FP x; exists y.
Unshelve. all: by end_near. Qed.

#[global] Typeclasses Opaque fmapi.

Global Instance fmapi_proper_filter
  T U (f : T -> U -> Prop) (F : set (set T)) :
  infer {near F, is_totalfun f} ->
  ProperFilter F -> ProperFilter (f `@ F).
Proof.
move=> f_totalfun FF; apply: Build_ProperFilter.
by move=> P; rewrite /fmapi/= => /filter_ex [x [y [??]]]; exists y.
Qed.
Definition filter_map_proper_filter' := fmapi_proper_filter.

Lemma cvg_id T (F : set (set T)) : x @[x --> F] --> F.
Proof. exact. Qed.
Arguments cvg_id {T F}.

Lemma fmap_comp {A B C} (f : B -> C) (g : A -> B) F:
  Filter F -> (f \o g)%FUN @ F = f @ (g @ F).
Proof. by []. Qed.

Lemma appfilter U V (f : U -> V) (F : set (set U)) :
  f @ F = [set P : set _ | \forall x \near F, P (f x)].
Proof. by []. Qed.

Lemma cvg_app U V (F G : set (set U)) (f : U -> V) :
  F --> G -> f @ F --> f @ G.
Proof. by move=> FG P /=; exact: FG. Qed.
Arguments cvg_app {U V F G} _.

Lemma cvgi_app U V (F G : set (set U)) (f : U -> set V) :
  F --> G -> f `@ F --> f `@ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma cvg_comp T U V (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Proof. by move=> fFG gGH; apply: cvg_trans gGH => P /fFG. Qed.

Lemma cvgi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g `@ G `=>` H -> g \o f `@ F `=>` H.
Proof. by move=> fFG gGH; apply: cvg_trans gGH => P /fFG. Qed.

Lemma near_eq_cvg {T U} {F : set (set T)} {FF : Filter F} (f g : T -> U) :
  {near F, f =1 g} -> g @ F `=>` f @ F.
Proof. by move=> eq_fg P /=; apply: filterS2 eq_fg => x /= <-. Qed.

Lemma eq_cvg (T T' : Type) (F : set (set T)) (f g : T -> T') (x : set (set T')) :
  f =1 g -> (f @ F --> x) = (g @ F --> x).
Proof. by move=> /funext->. Qed.

Lemma eq_is_cvg (T T' : Type) (fT : filteredType T') (F : set (set T)) (f g : T -> T') :
  f =1 g -> [cvg (f @ F) in fT] = [cvg (g @ F) in fT].
Proof. by move=> /funext->. Qed.

Lemma neari_eq_loc {T U} {F : set (set T)} {FF : Filter F} (f g : T -> set U) :
  {near F, f =2 g} -> g `@ F `=>` f `@ F.
Proof.
move=> eq_fg P /=; apply: filterS2 eq_fg => x eq_fg [y [fxy Py]].
by exists y; rewrite -eq_fg.
Qed.

Lemma cvg_near_const (T U : Type) (f : T -> U) (F : set (set T)) (G : set (set U)) :
  Filter F -> ProperFilter G ->
  (\forall y \near G, \forall x \near F, f x = y) -> f @ F --> G.
Proof.
move=> FF FG fFG P /= GP; rewrite !near_simpl; apply: (have_near G).
by apply: filter_app fFG; near do apply: filterS => x /= ->.
Unshelve. all: by end_near. Qed.

(* globally filter *)

Definition globally {T : Type} (A : set T) : set (set T) :=
   [set P : set T | forall x, A x -> P x].
Arguments globally {T} A _ /.

Lemma globally0 {T : Type} (A : set T) : globally set0 A. Proof. by []. Qed.

Global Instance globally_filter {T : Type} (A : set T) :
  Filter (globally A).
Proof.
constructor => //= P Q; last by move=> PQ AP x /AP /PQ.
by move=> AP AQ x Ax; split; [apply: AP|apply: AQ].
Qed.

Global Instance globally_properfilter {T : Type} (A : set T) a :
  infer (A a) -> ProperFilter (globally A).
Proof. by move=> Aa; apply: Build_ProperFilter' => /(_ a). Qed.

(** ** Specific filters *)

Section frechet_filter.
Variable T : Type.

Definition frechet_filter := [set S : set T | finite_set (~` S)].

Global Instance frechet_properfilter : infinite_set [set: T] ->
  ProperFilter frechet_filter.
Proof.
move=> infT; rewrite /frechet_filter.
constructor; first by rewrite /= setC0; exact: infT.
constructor; first by rewrite /= setCT.
- by move=> ? ?; rewrite /= setCI finite_setU.
- by move=> P Q PQ; exact/sub_finite_set/subsetC.
Qed.

End frechet_filter.

Global Instance frechet_properfilter_nat : ProperFilter (@frechet_filter nat).
Proof. by apply: frechet_properfilter; exact: infinite_nat. Qed.

Section at_point.

Context {T : Type}.

Definition at_point (a : T) (P : set T) : Prop := P a.

Global Instance at_point_filter (a : T) : ProperFilter (at_point a).
Proof. by constructor=> //; constructor=> // P Q subPQ /subPQ. Qed.
Typeclasses Opaque at_point.

End at_point.

(** Filters for pairs *)

Global Instance filter_prod_filter T U (F : set (set T)) (G : set (set U)) :
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
move=> FF FG; apply: filter_from_filter.
  by exists (setT, setT); split; apply: filterT.
move=> [P Q] [P' Q'] /= [FP GQ] [FP' GQ'].
exists (P `&` P', Q `&` Q') => /=; first by split; apply: filterI.
by move=> [x y] [/= [??] []].
Qed.

Canonical prod_filter_on T U (F : filter_on T) (G : filter_on U) :=
  FilterType (filter_prod F G) (filter_prod_filter _ _).

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Proof.
apply: filter_from_proper => -[A B] [/=FA GB].
by have [[x ?] [y ?]] := (filter_ex FA, filter_ex GB); exists (x, y).
Qed.
Definition filter_prod_proper' := @filter_prod_proper.

Lemma filter_prod1 {T U} {F : set (set T)} {G : set (set U)}
  {FG : Filter G} (P : set T) :
  (\forall x \near F, P x) -> \forall x \near F & _ \near G, P x.
Proof.
move=> FP; exists (P, setT)=> //= [|[?? []//]].
by split=> //; apply: filterT.
Qed.
Lemma filter_prod2 {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (P : set U) :
  (\forall y \near G, P y) -> \forall _ \near F & y \near G, P y.
Proof.
move=> FP; exists (setT, P)=> //= [|[?? []//]].
by split=> //; apply: filterT.
Qed.

Program Definition in_filter_prod {T U} {F : set (set T)} {G : set (set U)}
  (P : in_filter F) (Q : in_filter G) : in_filter (filter_prod F G) :=
  @InFilter _ _ (fun x => prop_of P x.1 /\ prop_of Q x.2) _.
Next Obligation.
move=> T U F G P Q.
by exists (prop_of P, prop_of Q) => //=; split; apply: prop_ofP.
Qed.

Lemma near_pair {T U} {F : set (set T)} {G : set (set U)}
      {FF : Filter F} {FG : Filter G}
      (P : in_filter F) (Q : in_filter G) x :
       prop_of P x.1 -> prop_of Q x.2 -> prop_of (in_filter_prod P Q) x.
Proof. by case: x=> x y; do ?rewrite prop_ofE /=; split. Qed.

Lemma cvg_fst {T U F G} {FG : Filter G} :
  (@fst T U) @ filter_prod F G --> F.
Proof. by move=> P; apply: filter_prod1. Qed.

Lemma cvg_snd {T U F G} {FF : Filter F} :
  (@snd T U) @ filter_prod F G --> G.
Proof. by move=> P; apply: filter_prod2. Qed.

Lemma near_map {T U} (f : T -> U) (F : set (set T)) (P : set U) :
  (\forall y \near f @ F, P y) = (\forall x \near F, P (f x)).
Proof. by []. Qed.

Lemma near_map2 {T T' U U'} (f : T -> U) (g : T' -> U')
      (F : set (set T)) (G : set (set T')) (P : U -> set U') :
  Filter F -> Filter G ->
  (\forall y \near f @ F & y' \near g @ G, P y y') =
  (\forall x \near F     & x' \near G     , P (f x) (g x')).
Proof.
move=> FF FG; rewrite propeqE; split=> -[[A B] /= [fFA fGB] ABP].
  exists (f @^-1` A, g @^-1` B) => //= -[x y /=] xyAB.
  by apply: (ABP (_, _)); apply: xyAB.
exists (f @` A, g @` B) => //=; last first.
  by move=> -_ [/= [x Ax <-] [x' Bx' <-]]; apply: (ABP (_, _)).
rewrite !nbhs_simpl /fmap /=; split.
  by apply: filterS fFA=> x Ax; exists x.
by apply: filterS fGB => x Bx; exists x.
Qed.

Lemma near_mapi {T U} (f : T -> set U) (F : set (set T)) (P : set U) :
  (\forall y \near f `@ F, P y) = (\forall x \near F, exists y, f x y /\ P y).
Proof. by []. Qed.

Lemma filter_pair_set (T T' : Type) (F : set (set T)) (F' : set (set T')) :
   Filter F -> Filter F' ->
   forall (P : set T) (P' : set T') (Q : set (T * T')),
   (forall x x', P x -> P' x' -> Q (x, x')) -> F P /\ F' P' ->
   filter_prod F F' Q.
Proof.
by move=> FF FF' P P' Q PQ [FP FP'];
   near=> x do [have := PQ x.1 x.2; rewrite -surjective_pairing; apply];
   [apply: cvg_fst | apply: cvg_snd].
Unshelve. all: by end_near. Qed.

Lemma filter_pair_near_of (T T' : Type) (F : set (set T)) (F' : set (set T')) :
   Filter F -> Filter F' ->
   forall (P : @in_filter T F) (P' : @in_filter T' F') (Q : set (T * T')),
   (forall x x', prop_of P x -> prop_of P' x' -> Q (x, x')) ->
   filter_prod F F' Q.
Proof.
move=> FF FF' [P FP] [P' FP'] Q PQ; rewrite prop_ofE in FP FP' PQ.
by exists (P, P') => //= -[t t'] [] /=; exact: PQ.
Qed.

Tactic Notation "near=>" ident(x) ident(y) :=
  (apply: filter_pair_near_of => x y ? ?).
Tactic Notation "near" constr(F) "=>" ident(x) ident(y) :=
  apply: (have_near F); near=> x y.

Module Export NearMap.
Definition near_simpl := (@near_simpl, @near_map, @near_mapi, @near_map2).
Ltac near_simpl := rewrite ?near_simpl.
End NearMap.

Lemma cvg_pair {T U V F} {G : set (set U)} {H : set (set V)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H} (f : T -> U) (g : T -> V) :
  f @ F --> G -> g @ F --> H ->
  (f x, g x) @[x --> F] --> (G, H).
Proof.
move=> fFG gFH P; rewrite !near_simpl => -[[A B] /=[GA HB] ABP]; near=> x.
by apply: (ABP (_, _)); split=> //=; near: x; [apply: fFG|apply: gFH].
Unshelve. all: by end_near. Qed.

Lemma cvg_comp2 {T U V W}
  {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) @[x --> (G, H)] --> I ->
  h (f x) (g x) @[x --> F] --> I.
Proof. by move=> fFG gFH hGHI P /= IP; apply: cvg_pair (hGHI _ IP). Qed.
Arguments cvg_comp2 {T U V W F G H I FF FG FH f g h} _ _ _.
Definition cvg_to_comp_2 := @cvg_comp2.

(* Lemma cvgi_comp_2 {T U V W} *)
(*   {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)} *)
(*   {FF : Filter F} *)
(*   (f : T -> U) (g : T -> V) (h : U -> V -> set W) : *)
(*   f @ F --> G -> g @ F --> H -> *)
(*   h (fst x) (snd x) `@[x --> (G, H)] --> I -> *)
(*   h (f x) (g x) `@[x --> F] --> I. *)
(* Proof. *)
(* intros Cf Cg Ch. *)
(* change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))). *)
(* apply: cvgi_comp Ch. *)
(* now apply cvg_pair. *)
(* Qed. *)

(** Restriction of a filter to a domain *)

Section within.
Context {T : Type}.
Implicit Types (D : set T) (F : set (set T)).

Definition within D F (P : set T) := {near F, D `<=` P}.
Arguments within : simpl never.

Lemma near_withinE D F (P : set T) :
  (\forall x \near within D F, P x) = {near F, D `<=` P}.
Proof. by []. Qed.

Lemma withinT F D : Filter F -> within D F D.
Proof. by move=> FF; rewrite /within; apply: filterE. Qed.

Lemma near_withinT F D : Filter F -> \forall x \near within D F, D x.
Proof. exact: withinT. Qed.

Lemma cvg_within {F} {FF : Filter F} D : within D F --> F.
Proof. by move=> P; apply: filterS. Qed.

Lemma withinET {F} {FF : Filter F} : within setT F = F.
Proof.
rewrite eqEsubset /within; split => ?; apply: filter_app; apply: nearW => //.
by move=> ?; exact.
Qed.

End within.

Global Instance within_filter T D F : Filter F -> Filter (@within T D F).
Proof.
move=> FF; rewrite /within; constructor.
- by apply: filterE.
- by move=> P Q; apply: filterS2 => x DP DQ Dx; split; [apply: DP|apply: DQ].
- by move=> P Q subPQ; apply: filterS => x DP /DP /subPQ.
Qed.

#[global] Typeclasses Opaque within.

Canonical within_filter_on T D (F : filter_on T) :=
  FilterType (within D F) (within_filter _ _).

Definition subset_filter {T} (F : set (set T)) (D : set T) :=
  [set P : set {x | D x} | F [set x | forall Dx : D x, P (exist _ x Dx)]].
Arguments subset_filter {T} F D _.

Global Instance subset_filter_filter T F (D : set T) :
  Filter F -> Filter (subset_filter F D).
Proof.
move=> FF; constructor; rewrite /subset_filter/=.
- exact: filterE.
- by move=> P Q; apply: filterS2=> x PD QD Dx; split.
- by move=> P Q subPQ; apply: filterS => R PD Dx; apply: subPQ.
Qed.
#[global] Typeclasses Opaque subset_filter.

Lemma subset_filter_proper {T F} {FF : Filter F} (D : set T) :
  (forall P, F P -> ~ ~ exists x, D x /\ P x) ->
  ProperFilter (subset_filter F D).
Proof.
move=> DAP; apply: Build_ProperFilter'; rewrite /subset_filter => subFD.
by have /(_ subFD) := DAP (~` D); apply => -[x [dx /(_ dx)]].
Qed.

(* For using near on sets in a filter *)
Section NearSet.

Context {T : choiceType} {Y : filteredType T}.
Context (F : set (set Y)) (PF : ProperFilter F).

Definition powerset_filter_from : set (set (set Y)) := filter_from
  [set M | [/\ M `<=` F,
    (forall E1 E2, M E1 -> F E2 -> E2 `<=` E1 -> M E2) & M !=set0 ] ]
  id.

Global Instance powerset_filter_from_filter : ProperFilter powerset_filter_from.
Proof.
split.
  rewrite (_ : xpredp0 = set0); last by rewrite eqEsubset; split.
  by move=> [W [_ _ [N +]]]; rewrite subset0 => /[swap] ->; apply.
apply: filter_from_filter.
  by exists F; split => //; exists setT; exact: filterT.
move=> M N /= [entM subM [M0 MM0]] [entN subN [N0 NN0]].
exists [set E | exists P Q, [/\ M P, N Q & E = P `&` Q] ]; first split.
- by move=> ? [? [? [? ? ->]]]; apply: filterI; [exact: entM | exact: entN].
- move=> ? E2 [P [Q [MP MQ ->]]] entE2 E2subPQ; exists E2, E2.
  split; last by rewrite setIid.
  + by apply: (subM _ _ MP) => // ? /E2subPQ [].
  + by apply: (subN _ _ MQ) => // ? /E2subPQ [].
- by exists (M0 `&` N0), M0, N0.
- move=> E /= [P [Q [MP MQ ->]]]; have entPQ : F (P `&` Q).
    by apply: filterI; [exact: entM | exact: entN].
  by split; [apply: (subM _ _ MP) | apply: (subN _ _ MQ)] => // ? [].
Qed.

Lemma near_small_set : \forall E \near powerset_filter_from, F E.
Proof. by exists F => //; split => //; exists setT; exact: filterT. Qed.

Lemma small_set_sub (E : set Y) : F E ->
  \forall E' \near powerset_filter_from, E' `<=` E.
Proof.
move=> entE; exists [set E' | F E' /\ E' `<=` E]; last by move=> ? [].
split; [by move=> E' [] | | by exists E; split].
by move=> E1 E2 [] ? sub ? ?; split => //; exact: subset_trans sub.
Qed.

Lemma near_powerset_filter_fromP (P : set Y -> Prop) :
  (forall A B, A `<=` B -> P B -> P A) ->
  (\forall U \near powerset_filter_from, P U) <-> exists2 U, F U & P U.
Proof.
move=> Psub; split=> [[M [FM ? [U MU]]] MsubP|[U FU PU]].
  by exists U; [exact: FM | exact: MsubP].
exists [set V | F V /\ V `<=` U]; last by move=> V [_] /Psub; exact.
split=> [E [] //| |]; last by exists U; split.
by move=> E1 E2 [F1 E1U F2 E2subE1]; split => //; exact: subset_trans E1U.
Qed.

Lemma powerset_filter_fromP C :
  F C -> powerset_filter_from [set W | F W /\ W `<=` C].
Proof.
move=> FC; exists [set W | F W /\ W `<=` C] => //; split; first by move=> ? [].
  by move=> A B [_ AC] FB /subset_trans/(_ AC).
by exists C; split.
Qed.

End NearSet.

Section PrincipalFilters.

Definition principal_filter {X : Type} (x : X) : set (set X) :=
  globally [set x].

Lemma principal_filterP {X} (x : X) (W : set X) : principal_filter x W <-> W x.
Proof. by split=> [|? ? ->]; [exact|]. Qed.

Lemma principal_filter_proper {X} (x : X) : ProperFilter (principal_filter x).
Proof. exact: globally_properfilter. Qed.

Canonical bool_discrete_filter := FilteredType bool bool principal_filter.

End PrincipalFilters.

(** * Topological spaces *)

Module Topological.

Record mixin_of (T : Type) (nbhs : T -> set (set T)) := Mixin {
  open : set (set T) ;
  nbhs_pfilter : forall p : T, ProperFilter (nbhs p) ;
  nbhsE : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE : open = [set A : set T | A `<=` nbhs^~ A ]
}.

Record class_of (T : Type) := Class {
  base : Filtered.class_of T T;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Filtered.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack nbhs' (m : @mixin_of T nbhs') :=
  fun bT (b : Filtered.class_of T T) of phant_id (@Filtered.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Filtered.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Notation topologicalType := type.
Notation TopologicalType T m := (@pack T _ m _ _ idfun _ idfun).
Notation TopologicalMixin := Mixin.
Notation "[ 'topologicalType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'topologicalType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'topologicalType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'topologicalType'  'of'  T ]") : form_scope.

End Exports.

End Topological.

Export Topological.Exports.

Section Topological1.

Context {T : topologicalType}.

Definition open := Topological.open (Topological.class T).

Definition open_nbhs (p : T) (A : set T) := open A /\ A p.

Definition basis (B : set (set T)) :=
  B `<=` open /\ forall x, filter_from [set U | B U /\ U x] id --> x.

Definition second_countable := exists2 B, countable B & basis B.

Global Instance nbhs_pfilter (p : T) : ProperFilter (nbhs p).
Proof. by apply: Topological.nbhs_pfilter; case: T p => ? []. Qed.
Typeclasses Opaque nbhs.

Lemma nbhs_filter (p : T) : Filter (nbhs p).
Proof. exact: (@nbhs_pfilter). Qed.

Canonical nbhs_filter_on (x : T) := FilterType (nbhs x) (@nbhs_filter x).

Lemma nbhsE (p : T) :
  nbhs p = [set A : set T | exists2 B : set T, open_nbhs p B & B `<=` A].
Proof.
have -> : nbhs p = [set A : set T | exists B, [/\ open B, B p & B `<=` A] ].
  exact: Topological.nbhsE.
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
Proof. exact: Topological.openE. Qed.

Lemma nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Proof. by rewrite nbhsE => - [? [_ ?]]; apply. Qed.

Lemma nbhs_interior (p : T) (A : set T) : nbhs p A -> nbhs p A^°.
Proof.
rewrite nbhsE /open_nbhs openE => - [B [Bop Bp] sBA].
by exists B => // q Bq; apply: filterS sBA _; apply: Bop.
Qed.

Lemma open0 : open set0.
Proof. by rewrite openE. Qed.

Lemma openT : open setT.
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

#[global] Hint Extern 0 (Filter (nbhs _)) =>
  solve [apply: nbhs_filter] : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter (nbhs _)) =>
  solve [apply: nbhs_pfilter] : typeclass_instances.

Notation "A ^°" := (interior A) : classical_set_scope.

Notation continuous f := (forall x, f%function @ x --> f%function x).

Lemma near_fun (T T' : topologicalType) (f : T -> T') (x : T) (P : T' -> Prop) :
    {for x, continuous f} ->
  (\forall y \near f x, P y) -> (\near x, P (f x)).
Proof. exact. Qed.
Arguments near_fun {T T'} f x.

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
  (F : set (set T)) x (f : T -> U) :
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
  (F : set (set T)) (FF : Filter F)
  (f : T -> V) (h : V -> U) (a : V) :
  {for a, continuous h} ->
  f @ F --> a -> (h \o f) @ F --> h a.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ h _ _ _ fa).
Qed.

Lemma continuous_is_cvg {T : Type} {V U : topologicalType} [F : set (set T)]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma continuous2_cvg {T : Type} {V W U : topologicalType}
  (F : set (set T)) (FF : Filter F)
  (f : T -> V) (g : T -> W) (h : V -> W -> U) (a : V) (b : W) :
  h z.1 z.2 @[z --> (a, b)] --> h a b ->
  f @ F --> a -> g @ F --> b -> (fun x => h (f x) (g x)) @ F --> h a b.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ (fun x => h x.1 x.2) _ _ _ (cvg_pair fa fb)).
Qed.

Lemma cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set (set T)) {FF : Filter F} :
  (\forall x \near F, f x = l) -> f @ F --> l.
Proof.
move=> fFl P /=; rewrite !near_simpl => Pl.
by apply: filterS fFl => _ ->; apply: nbhs_singleton.
Qed.
Arguments cvg_near_cst {T U} l {f F FF}.

Lemma is_cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set (set T)) {FF : Filter F} :
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
    (F : set (set T)) {FF : Filter F} :
  (fun _ : T => x) @ F --> x.
Proof. by apply: cvg_near_cst; near=> x0. Unshelve. all: by end_near. Qed.
Arguments cvg_cst {U} x {T F FF}.
#[global] Hint Resolve cvg_cst : core.

Lemma is_cvg_cst (U : topologicalType) (x : U) (T : Type)
  (F : set (set T)) {FF : Filter F} :
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
move=> Ax P AP; rewrite /within; near=> y; apply: AP.
Unshelve. all: by end_near. Qed.

(* [locally P] replaces a (globally A) in P by a within A (nbhs x)      *)
(* Can be combined with a notation taking a filter as its last argument *)
Definition locally_of (P : set (set T) -> Prop) of phantom Prop (P (globally A))
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
move=> FF AsubB W; rewrite /within; apply: filter_app; rewrite nbhs_simpl.
by apply: filterE => ? + ?; apply; exact: AsubB.
Qed.

Lemma withinE F : Filter F ->
  within A F = [set U | exists2 V, F V & U `&` A = V `&` A].
Proof.
move=> FF; rewrite eqEsubset; split=> U.
  move=> Wu; exists [set x | A x -> U x] => //.
  by rewrite eqEsubset; split => t [L R]; split=> //; apply: L.
move=> [V FV AU]; rewrite /within /prop_near1 nbhs_simpl; near=> w => Aw.
by have []// : (U `&` A) w; rewrite AU; split => //; apply: (near FV).
Unshelve. all: by end_near. Qed.

Lemma fmap_within_eq {S : topologicalType} (F : set (set T)) (f g : T -> S) :
  Filter F -> {in A, f =1 g} -> f @ within A F --> g @ within A F.
Proof.
move=> FF feq U /=; near_simpl; apply: filter_app.
rewrite ?nbhs_simpl; near_simpl; near=> w; rewrite (feq w) // inE.
exact: (near (withinT A FF) w).
Unshelve. all: by end_near. Qed.

End within_topologicalType.

Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).

(** ** Topology defined by a filter *)

Section TopologyOfFilter.

Context {T : Type} {nbhs' : T -> set (set T)}.
Hypothesis (nbhs'_filter : forall p : T, ProperFilter (nbhs' p)).
Hypothesis (nbhs'_singleton : forall (p : T) (A : set T), nbhs' p A -> A p).
Hypothesis (nbhs'_nbhs' : forall (p : T) (A : set T), nbhs' p A -> nbhs' p (nbhs'^~ A)).

Definition open_of_nbhs := [set A : set T | A `<=` nbhs'^~ A].

Program Definition topologyOfFilterMixin : Topological.mixin_of nbhs' :=
  @Topological.Mixin T nbhs' open_of_nbhs _ _ _.
Next Obligation.
move=> p; rewrite predeqE => A; split=> [p_A|]; last first.
  by move=> [B [Bop Bp sBA]]; apply: filterS sBA _; apply: Bop.
exists (nbhs'^~ A) ; split => //; first by move=> ?; apply: nbhs'_nbhs'.
by move=> q /nbhs'_singleton.
Qed.
Next Obligation. done. Qed.

End TopologyOfFilter.

(** ** Topology defined by open sets *)

Section TopologyOfOpen.

Variable (T : Type) (op : set T -> Prop).
Hypothesis (opT : op setT).
Hypothesis (opI : forall (A B : set T), op A -> op B -> op (A `&` B)).
Hypothesis (op_bigU : forall (I : Type) (f : I -> set T),
  (forall i, op (f i)) -> op (\bigcup_i f i)).

Definition nbhs_of_open (p : T) (A : set T) :=
  exists B, [/\ op B, B p & B `<=` A].

Program Definition topologyOfOpenMixin : Topological.mixin_of nbhs_of_open :=
  @Topological.Mixin T nbhs_of_open op _ _ _.
Next Obligation.
move=> p; apply: Build_ProperFilter.
  by move=> A [B [_ Bp sBA]]; exists p; apply: sBA.
split; first by exists setT.
  move=> A B [C [Cop Cp sCA]] [D [Dop Dp sDB]].
  exists (C `&` D); split => //; first exact: opI.
  by move=> q [/sCA Aq /sDB Bq].
move=> A B sAB [C [Cop p_C sCA]].
by exists C; split=> //; apply: subset_trans sAB.
Qed.
Next Obligation. done. Qed.
Next Obligation.
rewrite predeqE => A; split=> [Aop p Ap|Aop].
  by exists A; split=> //; split.
suff -> : A = \bigcup_(B : {B : set T & op B /\ B `<=` A}) projT1 B.
  by apply: op_bigU => B; have [] := projT2 B.
rewrite predeqE => p; split=> [|[B _ Bp]]; last by have [_] := projT2 B; apply.
by move=> /Aop [B [Bop Bp sBA]]; exists (existT _ B (conj Bop sBA)).
Qed.

End TopologyOfOpen.

(** ** Topology defined by a base of open sets *)

Section TopologyOfBase.

Definition open_from I T (D : set I) (b : I -> set T) :=
  [set \bigcup_(i in D') b i | D' in subset^~ D].

Lemma open_fromT I T (D : set I) (b : I -> set T) :
  \bigcup_(i in D) b i = setT -> open_from D b setT.
Proof. by move=> ?; exists D. Qed.

Variable (I : pointedType) (T : Type) (D : set I) (b : I -> (set T)).
Hypothesis (b_cover : \bigcup_(i in D) b i = setT).
Hypothesis (b_join : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j]).

Program Definition topologyOfBaseMixin :=
  @topologyOfOpenMixin _ (open_from D b) (open_fromT b_cover) _ _.
Next Obligation.
move=> A B [DA sDAD AeUbA] [DB sDBD BeUbB].
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
Next Obligation.
move=> I0 f.
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

End TopologyOfBase.

Section filter_supremums.

Global Instance smallest_filter_filter {T : Type} (F : set (set T)) :
  Filter (smallest Filter F).
Proof.
split.
- by move=> G [? _]; apply: filterT.
- by move=> ? ? sFP sFQ ? [? ?]; apply: filterI; [apply: sFP | apply: sFQ].
- by move=> ? ? /filterS + sFP ? [? ?]; apply; apply: sFP.
Qed.

Fixpoint filterI_iter {T : Type} (F : set (set T)) (n : nat) :=
  if n is m.+1
  then [set P `&` Q |
    P in filterI_iter F m & Q in filterI_iter F m]
  else setT |` F.

Lemma filterI_iter_sub {T : Type} (F : set (set T)) :
  {homo filterI_iter F : i j / (i <= j)%N >-> i `<=` j}.
Proof.
move=> + j; elim: j; first by move=> i; rewrite leqn0 => /eqP ->.
move=> j IH i; rewrite leq_eqVlt => /predU1P[->//|].
by move=> /IH/subset_trans; apply=> A ?; do 2 exists A => //; rewrite setIid.
Qed.

Lemma filterI_iterE {T : Type} (F : set (set T)) :
  smallest Filter F = filter_from (\bigcup_n (filterI_iter F n)) id.
Proof.
rewrite eqEsubset; split.
  apply: smallest_sub => //; first last.
    by move=> A FA; exists A => //; exists O => //; right.
  apply: filter_from_filter; first by exists setT; exists O => //; left.
  move=> P Q [i _ sFP] [j _ sFQ]; exists (P `&` Q) => //.
  exists (maxn i j).+1 => //=; exists P.
    by apply: filterI_iter_sub; first exact: leq_maxl.
  by exists Q => //; apply: filterI_iter_sub; first exact: leq_maxr.
move=> + [+ [n _]]; elim: n => [A B|n IH/= A B].
  move=> [-> /[!(@subTset T)] ->|]; first exact: filterT.
  by move=> FB /filterS; apply; apply: sub_gen_smallest.
move=> [P sFP] [Q sFQ] PQB /filterS; apply; rewrite -PQB.
by apply: (filterI _ _); [exact: (IH _ _ sFP)|exact: (IH _ _ sFQ)].
Qed.

(** ** Topology defined by a subbase of open sets *)

Definition finI_from (I : choiceType) T (D : set I) (f : I -> set T) :=
  [set \bigcap_(i in [set` D']) f i |
    D' in [set A : {fset I} | {subset A <= D}]].

Lemma finI_from_cover (I : choiceType) T (D : set I) (f : I -> set T) :
  \bigcup_(A in finI_from D f) A = setT.
Proof.
rewrite predeqE => t; split=> // _; exists setT => //.
by exists fset0 => //; rewrite set_fset0 bigcap_set0.
Qed.

Lemma finI_from1 (I : choiceType) T (D : set I) (f : I -> set T) i :
  D i -> finI_from D f (f i).
Proof.
move=> Di; exists [fset i]%fset; first by move=> ?; rewrite !inE => /eqP ->.
by rewrite bigcap_fset big_seq_fset1.
Qed.

Lemma finI_from_countable (I : pointedType) T (D : set I) (f : I -> set T) :
  countable D -> countable (finI_from D f).
Proof.
move=> ?; apply: (card_le_trans (card_image_le _ _)).
exact: fset_subset_countable.
Qed.

Lemma finI_fromI {I : choiceType} T D (f : I -> set T) A B :
  finI_from D f A -> finI_from D f B -> finI_from D f (A `&` B) .
Proof.
case=> N ND <- [M MD <-]; exists (N `|` M)%fset.
  by move=> ?; rewrite inE => /orP[/ND | /MD].
by rewrite -bigcap_setU set_fsetU.
Qed.

Lemma filterI_iter_finI {I : choiceType} T D (f : I -> set T) :
  finI_from D f = \bigcup_n (filterI_iter (f @` D) n).
Proof.
rewrite eqEsubset; split.
  move=> A [N /= + <-]; have /finite_setP[n] := finite_fset N; elim: n N.
    move=> ?; rewrite II0 card_eq0 => /eqP -> _; rewrite bigcap_set0.
    by exists O => //; left.
  move=> n IH N /eq_cardSP[x Ax + ND]; rewrite -set_fsetD1 => Nxn.
  have NxD : {subset (N `\ x)%fset <= D}.
    by move=> ?; rewrite ?inE => /andP [_ /ND /set_mem].
  have [r _ xr] := IH _ Nxn NxD; exists r.+1 => //; exists (f x).
    apply: (@filterI_iter_sub _ _ O) => //; right; exists x => //.
    by rewrite -inE; apply: ND.
  exists (\bigcap_(i in [set` (N `\ x)%fset]) f i) => //.
  by rewrite -bigcap_setU1 set_fsetD1 setD1K.
move=> A [n _]; elim: n A.
  move=> a [-> |[i Di <-]]; [exists fset0 | exists [fset i]%fset] => //.
  - by rewrite set_fset0 bigcap_set0.
  - by move=> ?; rewrite !inE => /eqP ->.
  - by rewrite set_fset1 bigcap_set1.
by move=> n IH A /= [B snB [C snC <-]]; apply: finI_fromI; apply: IH.
Qed.

Lemma smallest_filter_finI {T : choiceType} (D : set T) f :
  filter_from (finI_from D f) id = smallest (@Filter T) (f @` D).
Proof. by rewrite filterI_iter_finI filterI_iterE. Qed.

End filter_supremums.

Section TopologyOfSubbase.

Variable (I : pointedType) (T : Type) (D : set I) (b : I -> set T).

Program Definition topologyOfSubbaseMixin :=
  @topologyOfBaseMixin _ _ (finI_from D b) id (finI_from_cover D b) _.
Next Obligation.
move=> A B t [DA sDAD AeIbA] [DB sDBD BeIbB] At Bt.
exists (A `&` B); split => //.
exists (DA `|` DB)%fset; first by move=> i /fsetUP [/sDAD|/sDBD].
rewrite predeqE => s; split=> [Ifs|[As Bs] i /fsetUP].
  split; first by rewrite -AeIbA => i DAi; apply: Ifs; rewrite /= inE DAi.
  by rewrite -BeIbB => i DBi; apply: Ifs; rewrite /= inE DBi orbC.
by move=> [DAi|DBi];
  [have := As; rewrite -AeIbA; apply|have := Bs; rewrite -BeIbB; apply].
Qed.

End TopologyOfSubbase.

(* Topology on nat *)

Section nat_topologicalType.

Let D : set nat := setT.
Let b : nat -> set nat := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite predeqE => i; split => // _; exists i. Qed.

Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof. by move=> i j t _ _ -> ->; exists j. Qed.

Definition nat_topologicalTypeMixin := topologyOfBaseMixin bT bD.
Canonical nat_filteredType := FilteredType nat nat (nbhs_of_open (open_from D b)).
Canonical nat_topologicalType := TopologicalType nat nat_topologicalTypeMixin.

End nat_topologicalType.

(* :TODO: ultimately nat could be replaced by any lattice *)
Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Canonical eventually_filter_source X :=
   @Filtered.Source X _ nat (fun f => f @ \oo).

Global Instance eventually_filter : ProperFilter eventually.
Proof.
eapply @filter_from_proper; last by move=> i _; exists i => /=.
apply: filter_fromT_filter; first by exists 0%N.
move=> i j; exists (maxn i j) => n //=.
by rewrite geq_max => /andP[ltin ltjn].
Qed.

Canonical eventually_filterType := FilterType eventually _.
Canonical eventually_pfilterType := PFilterType eventually (filter_not_empty _).

Lemma nbhs_infty_gt N : \forall n \near \oo, (N < n)%N.
Proof. by exists N.+1. Qed.
#[global] Hint Resolve nbhs_infty_gt : core.

Lemma nbhs_infty_ge N : \forall n \near \oo, (N <= n)%N.
Proof. by exists N. Qed.

Lemma cvg_addnl N : addn N @ \oo --> \oo.
Proof.
by move=> P [n _ Pn]; exists (n - N)%N => // m; rewrite /= leq_subLR => /Pn.
Qed.

Lemma cvg_addnr N : addn^~ N --> \oo.
Proof. by under [addn^~ N]funext => n do rewrite addnC; apply: cvg_addnl. Qed.

Lemma cvg_subnr N : subn^~ N --> \oo.
Proof.
move=> P [n _ Pn]; exists (N + n)%N => //= m le_m.
by apply: Pn; rewrite /= leq_subRL// (leq_trans _ le_m)// leq_addr.
Qed.

Lemma cvg_mulnl N : (N > 0)%N -> muln N --> \oo.
Proof.
case: N => N // _ P [n _ Pn]; exists (n %/ N.+1).+1 => // m.
by rewrite /= ltn_divLR// => n_lt; apply: Pn; rewrite mulnC /= ltnW.
Qed.

Lemma cvg_mulnr N :(N > 0)%N -> muln^~ N --> \oo.
Proof.
by move=> N_gt0; under [muln^~ N]funext => n do rewrite mulnC; apply: cvg_mulnl.
Qed.

Lemma cvg_divnr N : (N > 0)%N -> divn^~ N --> \oo.
Proof.
move=> N_gt0 P [n _ Pn]; exists (n * N)%N => //= m.
by rewrite /= -leq_divRL//; apply: Pn.
Qed.

Lemma near_inftyS (P : set nat) :
  (\forall x \near \oo, P (S x)) -> (\forall x \near \oo, P x).
Proof. case=> N _ NPS; exists (S N) => // [[]]; rewrite /= ?ltn0 //. Qed.

Section infty_nat.
Local Open Scope nat_scope.

Let cvgnyP {F : set (set nat)} {FF : Filter F} : [<->
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

Context {I : Type} {F : set (set I)} {FF : Filter F} (f : I -> nat).

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

(** ** Topology on the product of two spaces *)

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

Definition prod_topologicalTypeMixin :=
  topologyOfFilterMixin prod_nbhs_filter prod_nbhs_singleton prod_nbhs_nbhs.

Canonical prod_topologicalType :=
  TopologicalType (T * U) prod_topologicalTypeMixin.

End Prod_Topology.

(** ** Topology on matrices *)

Section matrix_Topology.

Variables (m n : nat) (T : topologicalType).

Implicit Types M : 'M[T]_(m, n).

Lemma mx_nbhs_filter M : ProperFilter (nbhs M).
Proof.
apply: (filter_from_proper (filter_from_filter _ _)) => [|P Q M_P M_Q|P M_P].
- by exists (fun i j => setT) => ??; apply: filterT.
- exists (fun i j => P i j `&` Q i j) => [??|mx PQmx]; first exact: filterI.
  by split=> i j; have [] := PQmx i j.
- exists (\matrix_(i, j) get (P i j)) => i j; rewrite mxE; apply: getPex.
  exact: filter_ex (M_P i j).
Qed.

Lemma mx_nbhs_singleton M (A : set 'M[T]_(m, n)) : nbhs M A -> A M.
Proof. by move=> [P M_P]; apply=> ??; apply: nbhs_singleton. Qed.

Lemma mx_nbhs_nbhs M (A : set 'M[T]_(m, n)) : nbhs M A -> nbhs M (nbhs^~ A).
Proof.
move=> [P M_P sPA]; exists (fun i j => (P i j)^°).
  by move=> ? ?; apply: nbhs_interior.
by move=> ? ?; exists P.
Qed.

Definition matrix_topologicalTypeMixin :=
  topologyOfFilterMixin mx_nbhs_filter mx_nbhs_singleton mx_nbhs_nbhs.

Canonical matrix_topologicalType :=
  TopologicalType 'M[T]_(m, n) matrix_topologicalTypeMixin.

End matrix_Topology.

(** ** Weak topology by a function *)

Section Weak_Topology.

Variable (S : pointedType) (T : topologicalType) (f : S -> T).

Definition wopen := [set f @^-1` A | A in open].

Lemma wopT : wopen setT.
Proof. by exists setT => //; apply: openT. Qed.

Lemma wopI (A B : set S) : wopen A -> wopen B -> wopen (A `&` B).
Proof.
by move=> [C Cop <-] [D Dop <-]; exists (C `&` D) => //; apply: openI.
Qed.

Lemma wop_bigU (I : Type) (g : I -> set S) :
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

Definition weak_topologicalTypeMixin := topologyOfOpenMixin wopT wopI wop_bigU.

Let S_filteredClass := Filtered.Class (Pointed.class S) (nbhs_of_open wopen).
Definition weak_topologicalType :=
  Topological.Pack (@Topological.Class _ S_filteredClass
    weak_topologicalTypeMixin).

Lemma weak_continuous : continuous (f : weak_topologicalType -> T).
Proof. by apply/continuousP => A ?; exists A. Qed.

Lemma cvg_image (F : set (set S)) (s : S) :
  Filter F -> f @` setT = setT ->
  F --> (s : weak_topologicalType) <-> [set f @` A | A in F] --> f s.
Proof.
move=> FF fsurj; split=> [cvFs|cvfFfs].
  move=> A /weak_continuous [B [Bop Bs sBAf]].
  have /cvFs FB : nbhs (s : weak_topologicalType) B by apply: open_nbhs_nbhs.
  rewrite nbhs_simpl; exists (f @^-1` A); first exact: filterS FB.
  exact: image_preimage.
move=> A /= [_ [[B Bop <-] Bfs sBfA]].
have /cvfFfs [C FC fCeB] : nbhs (f s) B by rewrite nbhsE; exists B.
rewrite nbhs_filterE; apply: filterS FC.
by apply: subset_trans sBfA; rewrite -fCeB; apply: preimage_image.
Qed.

End Weak_Topology.

(** ** Supremum of a family of topologies *)

Section Sup_Topology.

Variable (T : pointedType) (I : Type) (Tc : I -> Topological.class_of T).

Let TS := fun i => Topological.Pack (Tc i).

Definition sup_subbase := \bigcup_i (@open (TS i) : set (set T)).

Definition sup_topologicalTypeMixin := topologyOfSubbaseMixin sup_subbase id.

Definition sup_topologicalType :=
  Topological.Pack (@Topological.Class _ (Filtered.Class (Pointed.class T) _)
  sup_topologicalTypeMixin).

Lemma cvg_sup (F : set (set T)) (t : T) :
  Filter F -> F --> (t : sup_topologicalType) <-> forall i, F --> (t : TS i).
Proof.
move=> Ffilt; split=> cvFt.
  move=> i A /=; rewrite (@nbhsE (TS i)) => - [B [Bop Bt] sBA].
  apply: cvFt; exists B; split=> //; exists [set B]; last first.
    by rewrite predeqE => ?; split=> [[_ ->]|] //; exists B.
  move=> _ ->; exists [fset B]%fset.
    by move=> ?; rewrite inE inE => /eqP->; exists i.
  by rewrite predeqE=> ?; split=> [|??]; [apply|]; rewrite /= inE // =>/eqP->.
move=> A /=; rewrite (@nbhsE sup_topologicalType).
move=> [_ [[B sB <-] [C BC Ct] sUBA]].
rewrite nbhs_filterE; apply: filterS sUBA _; apply: (@filterS _ _ _ C).
  by move=> ? ?; exists C.
have /sB [D sD IDeC] := BC; rewrite -IDeC; apply: filter_bigI => E DE.
have /sD := DE; rewrite inE => - [i _]; rewrite openE => Eop.
by apply: (cvFt i); apply: Eop; move: Ct; rewrite -IDeC => /(_ _ DE).
Qed.

End Sup_Topology.

(** ** Product topology *)

Section Product_Topology.

Variable (I : Type) (T : I -> topologicalType).

Definition product_topologicalType :=
  sup_topologicalType (fun i => Topological.class
    (weak_topologicalType (fun f : dep_arrow_pointedType T => f i))).

End Product_Topology.

(** deleted neighborhood *)

Definition dnbhs {T : topologicalType} (x : T) :=
  within (fun y => y != x) (nbhs x).
Notation "x ^'" := (dnbhs x) : classical_set_scope.

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
  forall (F G : set (set T)), G `=>` F -> f @ G `=>` f @ F.
Proof. by move=> F G H A fFA ; exact: H (preimage f A) fFA. Qed.

Lemma cvg_within_filter {T U} {f : T -> U} (F : set (set T)) {FF : (Filter F) }
  (G : set (set U)) : forall (D : set T), (f @ F) --> G -> (f @ within D F) --> G.
Proof. move=> ?;  exact: cvg_trans (cvg_fmap2 (cvg_within _)). Qed.

Lemma cvg_app_within {T} {U : topologicalType} (f : T -> U) (F : set (set T))
  (D : set T): Filter F -> cvg (f @ F) -> cvg (f @ within D F).
Proof. by move => FF /cvg_ex [l H]; apply/cvg_ex; exists l; exact: cvg_within_filter. Qed.

Lemma nbhs_dnbhs {T : topologicalType} (x : T) : x^' `=>` nbhs x.
Proof. exact: cvg_within. Qed.

(** meets *)

Lemma meets_openr {T : topologicalType} (F : set (set T)) (x : T) :
  F `#` nbhs x = F `#` open_nbhs x.
Proof.
rewrite propeqE; split; [exact/meetsSr/open_nbhs_nbhs|].
by move=> P A B {}/P P; rewrite nbhsE => -[B' /P + sB]; apply: subsetI_neq0.
Qed.

Lemma meets_openl {T : topologicalType} (F : set (set T)) (x : T) :
  nbhs x `#` F = open_nbhs x `#` F.
Proof. by rewrite meetsC meets_openr meetsC. Qed.

Lemma meets_globallyl T (A : set T) G :
  globally A `#` G = forall B, G B -> A `&` B !=set0.
Proof.
rewrite propeqE; split => [/(_ _ _ (fun=> id))//|clA A' B sA].
by move=> /clA; apply: subsetI_neq0.
Qed.

Lemma meets_globallyr T F (B : set T) :
  F `#` globally B = forall A, F A -> A `&` B !=set0.
Proof.
by rewrite meetsC meets_globallyl; under eq_forall do rewrite setIC.
Qed.

Lemma meetsxx T (F : set (set T)) (FF : Filter F) : F `#` F = ~ (F set0).
Proof.
rewrite propeqE; split => [FmF F0|]; first by have [x []] := FmF _ _ F0 F0.
move=> FN0 A B /filterI FAI {}/FAI FAB; apply/set0P/eqP => AB0.
by rewrite AB0 in FAB.
Qed.

Lemma proper_meetsxx T (F : set (set T)) (FF : ProperFilter F) : F `#` F.
Proof. by rewrite meetsxx; apply: filter_not_empty. Qed.

(** ** Closed sets in topological spaces *)

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

(** ** Compact sets *)

Section Compact.

Context {T : topologicalType}.

Definition cluster (F : set (set T)) := [set p : T | F `#` nbhs p].

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

Definition compact A := forall (F : set (set T)),
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

Definition hausdorff_space := forall p q : T, cluster (nbhs p) q -> p = q.

Typeclasses Opaque within.
Global Instance within_nbhs_proper (A : set T) p :
  infer (closure A p) -> ProperFilter (within A (nbhs p)).
Proof.
move=> clAp; apply: Build_ProperFilter => B.
by move=> /clAp [q [Aq AqsoBq]]; exists q; apply: AqsoBq.
Qed.

Lemma compact_closed (A : set T) : hausdorff_space -> compact A -> closed A.
Proof.
move=> hT Aco p clAp; have pA := !! @withinT _ (nbhs p) A _.
have [q [Aq clsAp_q]] := !! Aco _ _ pA; rewrite (hT p q) //.
by apply: cvg_cluster clsAp_q; apply: cvg_within.
Qed.

Lemma compact_set1 (x : T) : compact [set x].
Proof.
move=> F PF Fx; exists x; split; first by [].
move=> P B nbhsB; exists x; split; last exact: nbhs_singleton.
suff [y [Py <-//]] : P `&` [set x] !=set0.
by apply: filter_ex; [exact: PF| exact: filterI].
Qed.

End Compact.
Arguments hausdorff_space : clear implicits.

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
  forall (I : Type) (F : set (set I)) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, P i x') ->
  \near F, K `<=` P F.

Let near_covering_compact : near_covering `<=` compact.
Proof.
move=> K locK F PF FK; apply/set0P/eqP=> KclstF0; case: (PF) => + FF; apply.
rewrite (_ : xpredp0 = set0)// -(setICr K); apply: filterI => //.
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

End near_covering.

Section Tychonoff.

Class UltraFilter T (F : set (set T)) := {
  ultra_proper :> ProperFilter F ;
  max_filter : forall G : set (set T), ProperFilter G -> F `<=` G -> G = F
}.

Lemma ultra_cvg_clusterE (T : topologicalType) (F : set (set T)) :
  UltraFilter F -> cluster F = [set p | F --> p].
Proof.
move=> FU; rewrite predeqE => p; split.
  by rewrite cluster_cvgE => - [G GF [cvGp /max_filter <-]].
by move=> cvFp; rewrite cluster_cvgE; exists F; [apply: ultra_proper|split].
Qed.

Lemma ultraFilterLemma T (F : set (set T)) :
  ProperFilter F -> exists G, UltraFilter G /\ F `<=` G.
Proof.
move=> FF.
set filter_preordset := ({G : set (set T) & ProperFilter G /\ F `<=` G}).
set preorder := fun G1 G2 : filter_preordset => projT1 G1 `<=` projT1 G2.
suff [G Gmax] : exists G : filter_preordset, premaximal preorder G.
  have [GF sFG] := projT2 G; exists (projT1 G); split=> //; split=> // H HF sGH.
  have sFH : F `<=` H by apply: subset_trans sGH.
  have sHG : preorder (existT _ H (conj HF sFH)) G by apply: Gmax.
  by rewrite predeqE => ?; split=> [/sHG|/sGH].
have sFF : F `<=` F by [].
apply: (ZL_preorder ((existT _ F (conj FF sFF)) : filter_preordset)) =>
  [?|G H I sGH sHI ? /sGH /sHI|A Atot] //.
case: (pselect (A !=set0)) => [[G AG] | A0]; last first.
  exists (existT _ F (conj FF sFF)) => G AG.
  by have /asboolP := A0; rewrite asbool_neg => /forallp_asboolPn /(_ G).
have [GF sFG] := projT2 G.
suff UAF : ProperFilter (\bigcup_(H in A) projT1 H).
  have sFUA : F `<=` \bigcup_(H in A) projT1 H.
    by move=> B FB; exists G => //; apply: sFG.
  exists (existT _ (\bigcup_(H in A) projT1 H) (conj UAF sFUA)) => H AH B HB /=.
  by exists H.
apply: Build_ProperFilter.
  by move=> B [H AH HB]; have [HF _] := projT2 H; apply: (@filter_ex _ _ HF).
split; first by exists G => //; apply: filterT.
  move=> B C [HB AHB HBB] [HC AHC HCC]; have [sHBC|sHCB] := Atot _ _ AHB AHC.
    exists HC => //; have [HCF _] := projT2 HC; apply: filterI HCC.
    exact: sHBC.
  exists HB => //; have [HBF _] := projT2 HB; apply: filterI HBB _.
  exact: sHCB.
move=> B C SBC [H AH HB]; exists H => //; have [HF _] := projT2 H.
exact: filterS HB.
Qed.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : set (set T),
  UltraFilter F -> F A -> A `&` [set p | F --> p] !=set0].
Proof.
rewrite predeqE => A; split=> Aco F FF FA.
  by have /Aco [p [?]] := FA; rewrite ultra_cvg_clusterE; exists p.
have [G [GU sFG]] := ultraFilterLemma FF.
have /Aco [p [Ap]] : G A by apply: sFG.
rewrite /= -[_ --> p]/([set _ | _] p) -ultra_cvg_clusterE.
by move=> /(cvg_cluster sFG); exists p.
Qed.

Lemma filter_image (T U : Type) (f : T -> U) (F : set (set T)) :
  Filter F -> f @` setT = setT -> Filter [set f @` A | A in F].
Proof.
move=> FF fsurj; split.
- by exists setT => //; apply: filterT.
- move=> _ _ [A FA <-] [B FB <-].
  exists (f @^-1` (f @` A `&` f @` B)); last by rewrite image_preimage.
  have sAB : A `&` B `<=` f @^-1` (f @` A `&` f @` B).
    by move=> x [Ax Bx]; split; exists x.
  by apply: filterS sAB _; apply: filterI.
- move=> A B sAB [C FC fC_eqA].
  exists (f @^-1` B); last by rewrite image_preimage.
  by apply: filterS FC => p Cp; apply: sAB; rewrite -fC_eqA; exists p.
Qed.

Lemma proper_image (T U : Type) (f : T -> U) (F : set (set T)) :
  ProperFilter F -> f @` setT = setT -> ProperFilter [set f @` A | A in F].
Proof.
move=> FF fsurj; apply: Build_ProperFilter; last exact: filter_image.
by move=> _ [A FA <-]; have /filter_ex [p Ap] := FA; exists (f p); exists p.
Qed.

Lemma principal_filter_ultra {T : Type} (x : T) :
  UltraFilter (principal_filter x).
Proof.
split=> [|G [G0 xG] FG]; first exact: principal_filter_proper.
rewrite eqEsubset; split => // U GU; apply/principal_filterP.
have /(filterI GU): G [set x] by exact/FG/principal_filterP.
by rewrite setIC set1I; case: ifPn => // /[!inE].
Qed.

Lemma in_ultra_setVsetC T (F : set (set T)) (A : set T) :
  UltraFilter F -> F A \/ F (~` A).
Proof.
move=> FU; case: (pselect (F (~` A))) => [|nFnA]; first by right.
left; suff : ProperFilter (filter_from (F `|` [set A `&` B | B in F]) id).
  move=> /max_filter <-; last by move=> B FB; exists B => //; left.
  by exists A => //; right; exists setT; [apply: filterT|rewrite setIT].
apply: filter_from_proper; last first.
  move=> B [|[C FC <-]]; first exact: filter_ex.
  apply: contrapT => /asboolP; rewrite asbool_neg => /forallp_asboolPn AC0.
  by apply: nFnA; apply: filterS FC => p Cp Ap; apply: (AC0 p).
apply: filter_from_filter.
  by exists A; right; exists setT; [apply: filterT|rewrite setIT].
move=> B C [FB|[DB FDB <-]].
  move=> [FC|[DC FDC <-]]; first by exists (B `&` C)=> //; left; apply: filterI.
  exists (A `&` (B `&` DC)); last by rewrite setICA.
  by right; exists (B `&` DC) => //; apply: filterI.
move=> [FC|[DC FDC <-]].
  exists (A `&` (DB `&` C)); last by rewrite setIA.
  by right; exists (DB `&` C) => //; apply: filterI.
exists (A `&` (DB `&` DC)); last by move=> ??; rewrite setIACA setIid.
by right; exists (DB `&` DC) => //; apply: filterI.
Qed.

Lemma ultra_image (T U : Type) (f : T -> U) (F : set (set T)) :
  UltraFilter F -> f @` setT = setT -> UltraFilter [set f @` A | A in F].
Proof.
move=> FU fsurj; split; first exact: proper_image.
move=> G GF sfFG; rewrite predeqE => A; split; last exact: sfFG.
move=> GA; exists (f @^-1` A); last by rewrite image_preimage.
have [//|FnAf] := in_ultra_setVsetC (f @^-1` A) FU.
have : G (f @` (~` (f @^-1` A))) by apply: sfFG; exists (~` (f @^-1` A)).
suff : ~ G (f @` (~` (f @^-1` A))) by [].
rewrite preimage_setC image_preimage // => GnA.
by have /filter_ex [? []] : G (A `&` (~` A)) by apply: filterI.
Qed.

Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :
  (forall i, compact (A i)) ->
  @compact (product_topologicalType T)
    [set f : forall i, T i | forall i, A i (f i)].
Proof.
move=> Aco; rewrite compact_ultra => F FU FA.
set subst_coord := fun (i : I) (pi : T i) (f : forall x : I, T x) (j : I) =>
  if eqP is ReflectT e then ecast i (T i) (esym e) pi else f j.
have subst_coordT i pi f : subst_coord i pi f i = pi.
  rewrite /subst_coord; case eqP => // e.
  by rewrite (eq_irrelevance e (erefl _)).
have subst_coordN i pi f j : i != j -> subst_coord i pi f j = f j.
  move=> inej; rewrite /subst_coord; case: eqP => // e.
  by move: inej; rewrite {1}e => /negP.
have pr_surj i : @^~ i @` [set: forall i, T i] = setT.
  rewrite predeqE => pi; split=> // _.
  by exists (subst_coord i pi (fun _ => point))=> //; rewrite subst_coordT.
set pF := fun i => [set @^~ i @` B | B in F].
have pFultra : forall i, UltraFilter (pF i).
  by move=> i; apply: ultra_image (pr_surj i).
have pFA : forall i, pF i (A i).
  move=> i; exists [set g | forall i, A i (g i)] => //.
  rewrite predeqE => pi; split; first by move=> [g Ag <-]; apply: Ag.
  move=> Aipi; have [f Af] := filter_ex FA.
  exists (subst_coord i pi f); last exact: subst_coordT.
  move=> j; case: (eqVneq i j); first by case: _ /; rewrite subst_coordT.
  by move=> /subst_coordN ->; apply: Af.
have cvpFA i : A i `&` [set p | pF i --> p] !=set0.
  by rewrite -ultra_cvg_clusterE; apply: Aco.
exists (fun i => get (A i `&` [set p | pF i --> p])).
split=> [i|]; first by have /getPex [] := cvpFA i.
by apply/cvg_sup => i; apply/cvg_image=> //; have /getPex [] := cvpFA i.
Qed.

End Tychonoff.

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

(* The closed condition here is neccessary to make this definition work in a  *)
(* non-hausdorff setting.                                                     *)
Definition compact_near (F : set (set X)) :=
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

Lemma compact_precompact (A B : set X) :
  hausdorff_space X -> compact A -> precompact A.
Proof.
move=> h c; rewrite precompactE ( _ : closure A = A)//.
by apply/esym/closure_id; exact: compact_closed.
Qed.

Lemma precompact_closed (A : set X) : closed A -> precompact A = compact A.
Proof.
move=> clA; rewrite propeqE; split=> [[B AsubB [ + _ ]]|].
  by move=> /subclosed_compact; exact.
by rewrite {1}(_ : A = closure A) ?precompactE// -closure_id.
Qed.

Definition locally_compact (A : set X) := [locally precompact A].

End Precompact.

Section product_spaces.
Context {I : eqType} {K : I -> topologicalType}.

Let PK := product_topologicalType K.

(* Note we have to give the signature explicitly because there's no canonical *)
(* topology associated with `K`. This should be cleaned up after HB port.     *)

Lemma proj_continuous i : continuous (proj i : PK -> K i).
Proof.
move=> f; have /cvg_sup/(_ i)/cvg_image : f --> f by apply: cvg_id.
move=> h; apply: cvg_trans (h _) => {h}.
  by move=> Q /= [W nbdW <-]; apply: filterS nbdW; exact: preimage_image.
rewrite eqEsubset; split => y //; exists (dfwith (fun=> point) i y) => //.
by rewrite dfwithin.
Qed.

Lemma dfwith_continuous g (i : I) : continuous (dfwith g _ : K i -> PK).
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
by rewrite -VL => /(_ _ LM); rewrite -NM /= ? dfwithout // eq_sym.
Qed.

Lemma proj_open i (A : set PK) : open A -> open (proj i @` A).
Proof.
move=> oA; rewrite openE => z [f Af <-]; rewrite openE in oA.
have {oA} := oA _ Af; rewrite /interior => nAf.
apply: (@filterS _ _ _ ((dfwith f i) @^-1` A)).
  by move=> w Apw; exists (dfwith f i w) => //; rewrite projK.
apply: dfwith_continuous => /=; move: nAf; congr (nbhs _ A).
by apply: functional_extensionality_dep => ?; case: dfwithP.
Qed.

Lemma hausdorff_product :
  (forall x, hausdorff_space (K x)) -> hausdorff_space PK.
Proof.
move=> hsdfK p q /= clstr; apply: functional_extensionality_dep => x.
apply: hsdfK; move: clstr; rewrite ?cluster_cvgE /= => -[G PG [GtoQ psubG]].
exists (proj x @ G); [exact: fmap_proper_filter|split].
  apply: cvg_trans; last exact: (@proj_continuous x q).
  by apply: cvg_app; exact: GtoQ.
move/(cvg_app (proj x)): psubG => /cvg_trans; apply.
exact: proj_continuous.
Qed.

End product_spaces.

Definition finI (I : choiceType) T (D : set I) (f : I -> set T) :=
  forall D' : {fset I}, {subset D' <= D} ->
  \bigcap_(i in [set i | i \in D']) f i !=set0.

Lemma finI_filter (I : choiceType) T (D : set I) (f : I -> set T) :
  finI D f -> ProperFilter (filter_from (finI_from D f) id).
Proof.
move=> finIf; apply: (filter_from_proper (filter_from_filter _ _)).
- by exists setT; exists fset0 => //; rewrite predeqE.
- move=> A B [DA sDA IfA] [DB sDB IfB]; exists (A `&` B) => //.
  exists (DA `|` DB)%fset.
    by move=> ?; rewrite inE => /orP [/sDA|/sDB].
  rewrite -IfA -IfB predeqE => p; split=> [Ifp|[IfAp IfBp] i].
    by split=> i Di; apply: Ifp; rewrite /= inE Di // orbC.
  by rewrite /= inE => /orP []; [apply: IfAp|apply: IfBp].
- by move=> _ [?? <-]; apply: finIf.
Qed.

Lemma filter_finI (T : pointedType) (F : set (set T)) (D : set (set T))
  (f : set T -> set T) :
  ProperFilter F -> (forall A, D A -> F (f A)) -> finI D f.
Proof.
move=> FF sDFf D' sD; apply: (@filter_ex _ F); apply: filter_bigI.
by move=> A /sD; rewrite inE => /sDFf.
Qed.

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

Lemma compact_cover : compact = cover_compact.
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

End Covers.

Lemma finite_compact {X : topologicalType} (A : set X) :
  finite_set A -> compact A.
Proof.
case/finite_setP=> n; elim: n A => [A|n ih A /eq_cardSP[x Ax /ih ?]].
  by rewrite II0 card_eq0 => /eqP ->; exact: compact0.
by rewrite -(setD1K Ax); apply: compactU => //; exact: compact_set1.
Qed.

Lemma clopen_countable {T : topologicalType}:
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

Section separated_topologicalType.
Variable (T : topologicalType).
Implicit Types x y : T.

Local Open Scope classical_set_scope.

Definition kolmogorov_space := forall x y, x != y ->
  exists A : set T, (A \in nbhs x /\ y \in ~` A) \/ (A \in nbhs y /\ x \in ~` A).

Definition accessible_space := forall x y, x != y ->
  exists A : set T, open A /\ x \in A /\ y \in ~` A.

Lemma accessible_closed_set1 : accessible_space -> forall x, closed [set x].
Proof.
move=> T1 x; rewrite -[X in closed X]setCK; apply: open_closedC.
rewrite openE => y /eqP /T1 [U [oU [yU xU]]].
rewrite /interior nbhsE /=; exists U; last by rewrite subsetC1.
by split=> //; exact: set_mem.
Qed.

Lemma accessible_kolmogorov : accessible_space -> kolmogorov_space.
Proof.
move=> T1 x y /T1 [A [oA [xA yA]]]; exists A; left; split=> //.
by rewrite nbhsE inE; exists A => //; rewrite inE in xA.
Qed.

Lemma accessible_finite_set_closed :
  accessible_space <-> forall A : set T, finite_set A -> closed A.
Proof.
split => [TT1 A fA|h x y xy].
  rewrite -(fsbig_setU_set1 fA) fsbig_finite//=.
  by apply: closed_bigsetU => x xA; exact: accessible_closed_set1.
exists (~` [set y]); split; first by rewrite openC; exact: h.
by rewrite !inE/=; split=> [|/eqP]; [exact/eqP|rewrite eqxx].
Qed.

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

Lemma close_cvg (F1 F2 : set (set T)) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
move=> F12 F21.
have [/(cvg_trans F21) F2l|dvgF1] := pselect (cvg F1).
  by apply: (@cvg_close F2) => //; apply: cvgP F2l.
have [/(cvg_trans F12)/cvgP//|dvgF2] := pselect (cvg F2).
rewrite dvgP // dvgP //; exact/close_refl.
Qed.

Lemma cvgx_close x y : x --> y -> close x y.
Proof. exact: cvg_close. Qed.

Lemma cvgi_close T' {F} {FF : ProperFilter F} (f : T' -> set T) (l l' : T) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: infer {near F, is_totalfun f} by exact: cvg_close fFl fFl'.
apply: filter_app f_prop; near do split=> //=.
have: (f `@ F) setT by apply: fFl; apply: filterT.
by rewrite fmapiE; apply: filterS => x [y []]; exists y.
Unshelve. all: by end_near. Qed.
Definition cvg_toi_locally_close := @cvgi_close.

Lemma open_hausdorff : hausdorff_space T =
  forall x y, x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
                [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0].
Proof.
rewrite propeqE; split => [T_filterT2|T_openT2] x y.
  have := @contra_not _ _ (T_filterT2 x y); rewrite (rwP eqP) (rwP negP).  (* change @contra_not _ _ to contra_not when requiring MathComp > 1.14 *)
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

Definition hausdorff_accessible : hausdorff_space T -> accessible_space.
Proof.
rewrite open_hausdorff => hsdfT => x y /hsdfT [[U V] [xU yV]] [/= ? ? /eqP].
rewrite setIC => /disjoints_subset VUc; exists U; repeat split => //.
by rewrite inE; apply: VUc; rewrite -inE.
Qed.

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

Lemma lim_id x : lim x = x.
Proof. by apply/esym/cvg_eq/cvg_ex; exists x. Qed.

Lemma cvg_lim {U : Type} {F} {FF : ProperFilter F} (f : U -> T) (l : T) :
  f @ F --> l -> lim (f @ F) = l.
Proof. by move=> /[dup] /cvgP /cvg_unique; apply. Qed.

Lemma lim_near_cst {U} {F} {FF : ProperFilter F} (l : T) (f : U -> T) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. by move=> /cvg_near_cst/cvg_lim. Qed.

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) :
   lim ((fun _ : U => k) @ F) = k.
Proof. by apply: cvg_lim; apply: cvg_cst. Qed.

Lemma cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set T) :
  {near F, is_fun f} -> is_subset1 [set x : T | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE //; exact: cvgi_close. Qed.

Lemma cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> T -> Prop) (l : T) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
move=> f_prop fl; apply: get_unique => // l' fl'; exact: cvgi_unique _ fl' fl.
Qed.

End separated_topologicalType.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvg_lim`")]
Notation cvg_map_lim := cvg_lim (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgi_lim`")]
Notation cvgi_map_lim := cvgi_lim (only parsing).

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

Definition discrete_topological_mixin :=
  topologyOfFilterMixin principal_filter_proper discrete_sing discrete_nbhs.

End DiscreteMixin.

Definition discrete_space (X : topologicalType) :=
  @nbhs X _ = @principal_filter X.

Context {X : topologicalType} {dsc: discrete_space X}.

Lemma discrete_open (A : set X) : open A.
Proof.
by rewrite openE => ? ?; rewrite /interior dsc; exact/principal_filterP.
Qed.

Lemma discrete_set1 (x : X) : nbhs x [set x].
Proof. by apply: open_nbhs_nbhs; split => //; exact: discrete_open. Qed.

Lemma discrete_closed (A : set X) : closed A.
Proof. by rewrite -[A]setCK closedC; exact: discrete_open. Qed.

Lemma discrete_cvg (F : set (set X)) (x : X) :
  Filter F -> F --> x <-> F [set x].
Proof.
rewrite /filter_of dsc nbhs_simpl; split; first by exact.
by move=> Fx U /principal_filterP ?; apply: filterS Fx => ? ->.
Qed.

Lemma discrete_hausdorff : hausdorff_space X.
Proof.
by move=> p q /(_ _ _ (discrete_set1 p) (discrete_set1 q))[x [] -> ->].
Qed.

Canonical bool_discrete_topology : topologicalType :=
  TopologicalType bool discrete_topological_mixin.

Lemma discrete_bool : discrete_space bool_discrete_topology.
Proof. by []. Qed.

Lemma bool_compact : compact [set: bool].
Proof. by rewrite setT_bool; apply/compactU; exact: compact_set1. Qed.

End DiscreteTopology.

#[global] Hint Resolve discrete_bool : core.

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

Lemma perfect_prod {I : Type} (i : I) (K : I -> topologicalType) :
  perfect_set [set: K i] -> perfect_set [set: product_topologicalType K].
Proof.
move=> /perfectTP KPo; apply/perfectTP => f oF; apply: (KPo (f i)).
rewrite (_ : [set f i] = proj i @` [set f]).
  by apply: (@proj_open (classicType_choiceType I) _ i); exact: oF.
by rewrite eqEsubset; split => ? //; [move=> -> /=; exists f | case=> g ->].
Qed.

Lemma perfect_diagonal (K : nat_topologicalType -> topologicalType) :
  (forall i, exists (xy: K i * K i), xy.1 != xy.2) ->
  perfect_set [set: product_topologicalType K].
Proof.
move=> npts; split; first exact: closedT.
rewrite eqEsubset; split => f // _.
pose distincts (i : nat) := projT1 (sigW (npts i)).
pose derange (i : nat) (z : K i) :=
  if z == (distincts i).1 then (distincts i).2 else (distincts i).1.
pose g (N i : nat) := if (i < N)%nat then f i else derange _ (f i).
have gcvg : g @ \oo --> (f : product_topologicalType K).
  apply/(@cvg_sup (product_topologicalType K)) => N U [V] [][W] oW <- WfN WU.
  by apply: (filterS WU); rewrite nbhs_simpl /g; exists N.+1 => // i /= ->.
move=> A /gcvg; rewrite nbhs_simpl; case=> N _ An.
exists (g N); split => //; last by apply: An; rewrite /= ?leqnn //.
apply/eqP => M; suff: g N N != f N by rewrite M; move/eqP.
rewrite /g ltnn /derange eq_sym; case: (eqVneq (f N) (distincts N).1) => //.
by move=> ->; have := projT2 (sigW (npts N)).
Qed.

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

Section totally_disconnected.
Implicit Types T : topologicalType.

Definition totally_disconnected {T} (A : set T) :=
  forall x, A x -> connected_component A x = [set x].

Definition zero_dimensional T :=
  (forall x y, x != y -> exists U : set T, [/\ clopen U, U x & ~ U y]).

Lemma zero_dimension_prod (I : choiceType) (T : I -> topologicalType) :
  (forall i, zero_dimensional (T i)) ->
  zero_dimensional (product_topologicalType T).
Proof.
move=> dctTI x y /eqP xneqy.
have [i/eqP/dctTI [U [clU Ux nUy]]] : exists i, x i <> y i.
  by apply/existsNP=> W; exact/xneqy/functional_extensionality_dep.
exists (proj i @^-1` U); split => //; apply: clopen_comp => //.
exact/proj_continuous.
Qed.

Lemma discrete_zero_dimension {T} : discrete_space T -> zero_dimensional T.
Proof.
move=> dctT x y xny; exists [set x]; split => //; last exact/nesym/eqP.
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

Lemma totally_disconnected_cvg {T : topologicalType} (x : T) :
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

End totally_disconnected.

Section set_nbhs.

Context {T : topologicalType} (A : set T).
Definition set_nbhs := \bigcap_(x in A) (nbhs x).

Global Instance set_nbhs_filter : Filter set_nbhs.
Proof.
split => P Q; first by exact: filterT.
  by move=> Px Qx x Ax; apply: filterI; [exact: Px | exact: Qx].
by move=> PQ + x Ax => /(_ _ Ax)/filterS; exact.
Qed.

Global Instance set_nbhs_pfilter : A!=set0 -> ProperFilter set_nbhs.
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

(** * Uniform spaces *)

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Local Notation "'to_set' A x" := ([set y | A (x, y)])
  (at level 0, A at level 0) : classical_set_scope.

Definition nbhs_ {T T'} (ent : set (set (T * T'))) (x : T) :=
  filter_from ent (fun A => to_set A x).

Lemma nbhs_E {T T'} (ent : set (set (T * T'))) x :
  nbhs_ ent x = filter_from ent (fun A => to_set A x).
Proof. by []. Qed.

Module Uniform.

Record mixin_of (M : Type) (nbhs : M -> set (set M)) := Mixin {
  entourage : (M * M -> Prop) -> Prop ;
  entourage_filter : Filter entourage ;
  entourage_refl : forall A, entourage A -> [set xy | xy.1 = xy.2] `<=` A ;
  entourage_inv : forall A, entourage A -> entourage (A^-1)%classic ;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A ;
  nbhsE : nbhs = nbhs_ entourage
}.

Record class_of (M : Type) := Class {
  base : Topological.class_of M;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Topological.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack nbhs (m : @mixin_of T nbhs) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Topological.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.
Notation "[ 'uniformType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'uniformType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'uniformType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'uniformType'  'of'  T ]") : form_scope.

End Exports.

End Uniform.

Export Uniform.Exports.

Section UniformTopology.

Program Definition topologyOfEntourageMixin (T : Type)
  (nbhs : T -> set (set T)) (m : Uniform.mixin_of nbhs) :
  Topological.mixin_of nbhs := topologyOfFilterMixin _ _ _.
Next Obligation.
move=> T nbhsT m p.
rewrite (Uniform.nbhsE m) nbhs_E; apply: filter_from_proper; last first.
  by move=> A entA; exists p; apply: Uniform.entourage_refl entA _ _.
apply: filter_from_filter.
  by exists setT; apply: @filterT (Uniform.entourage_filter m).
move=> A B entA entB; exists (A `&` B) => //.
exact: (@filterI _ _ (Uniform.entourage_filter m)).
Qed.
Next Obligation.
move=> T nbhsT m p A; rewrite (Uniform.nbhsE m) nbhs_E  => - [B entB sBpA].
by apply: sBpA; apply: Uniform.entourage_refl entB _ _.
Qed.
Next Obligation.
move=> T nbhsT m p A; rewrite (Uniform.nbhsE m) nbhs_E => - [B entB sBpA].
have /Uniform.entourage_split_ex [C entC sC2B] := entB.
exists C => // q Cpq; rewrite nbhs_E; exists C => // r Cqr.
by apply/sBpA/sC2B; exists q.
Qed.

End UniformTopology.

Definition entourage {M : uniformType} := Uniform.entourage (Uniform.class M).

Lemma nbhs_entourageE {M : uniformType} : nbhs_ (@entourage M) = nbhs.
Proof. by case: M=> [?[?[]]]. Qed.

Lemma entourage_sym {X Y : Type} E (x : X) (y : Y) :
  E (x, y) <-> (E ^-1)%classic (y, x).
Proof. by []. Qed.

Lemma filter_from_entourageE {M : uniformType} x :
  filter_from (@entourage M) (fun A => to_set A x) = nbhs x.
Proof. by rewrite -nbhs_entourageE. Qed.

Module Export NbhsEntourage.
Definition nbhs_simpl :=
  (nbhs_simpl,@filter_from_entourageE,@nbhs_entourageE).
End NbhsEntourage.

Lemma nbhsP {M : uniformType} (x : M) P : nbhs x P <-> nbhs_ entourage x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma filter_inv {T : Type} (F : set (set (T * T))) :
  Filter F -> Filter [set (V^-1)%classic | V in F].
Proof.
move=> FF; split => /=.
- by exists [set: T * T] => //; exact: filterT.
- by move=> P Q [R FR <-] [S FS <-]; exists (R `&` S) => //; exact: filterI.
- move=> P Q PQ [R FR RP]; exists Q^-1%classic => //; first last.
    by rewrite eqEsubset; split; case.
  by apply: filterS FR; case=> ? ? /= ?; apply: PQ; rewrite -RP.
Qed.

Section uniformType1.
Context {M : uniformType}.

Lemma entourage_refl (A : set (M * M)) x : entourage A -> A (x, x).
Proof. by move=> entA; apply: Uniform.entourage_refl entA _ _. Qed.

Global Instance entourage_pfilter : ProperFilter (@entourage M).
Proof.
apply: Build_ProperFilter; last exact: Uniform.entourage_filter.
by move=> A entA; exists (point, point); apply: entourage_refl.
Qed.

Lemma entourageT : entourage [set: M * M].
Proof. exact: filterT. Qed.

Lemma entourage_inv (A : set (M * M)) : entourage A -> entourage (A^-1)%classic.
Proof. exact: Uniform.entourage_inv. Qed.

Lemma entourage_split_ex (A : set (M * M)) :
  entourage A -> exists2 B, entourage B & B \; B `<=` A.
Proof. exact: Uniform.entourage_split_ex. Qed.

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
  split_ent A (x,z) -> split_ent A (z,y) -> A (x,y).
Proof. by move=> /subset_split_ent sA ??; apply: sA; exists z. Qed.

Lemma nbhs_entourage (x : M) A : entourage A -> nbhs x (to_set A x).
Proof. by move=> ?; apply/nbhsP; exists A. Qed.

Lemma cvg_entourageP F (FF : Filter F) (p : M) :
  F --> p <-> forall A, entourage A -> \forall q \near F, A (p, q).
Proof. by rewrite -filter_fromP !nbhs_simpl. Qed.

Lemma cvg_entourage {F} {FF : Filter F} (y : M) :
  F --> y -> forall A, entourage A -> \forall y' \near F, A (y,y').
Proof. by move/cvg_entourageP. Qed.

Lemma cvg_app_entourageP T (f : T -> M) F (FF : Filter F) p :
  f @ F --> p <-> forall A, entourage A -> \forall t \near F, A (p, f t).
Proof. exact: cvg_entourageP. Qed.

Lemma entourage_invI (E : set (M * M)) :
  entourage E -> entourage (E `&` E^-1)%classic.
Proof. by move=> ?; apply: filterI; last exact: entourage_inv. Qed.

Lemma split_ent_subset (E : set (M * M)) : entourage E -> split_ent E `<=` E.
Proof.
move=> entE; case=> x y splitxy; apply: subset_split_ent => //; exists y => //.
by apply: entourage_refl; exact: entourage_split_ent.
Qed.

End uniformType1.

#[global]
Hint Extern 0 (entourage (split_ent _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (get _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (_^-1)%classic) => exact: entourage_inv : core.
Arguments entourage_split {M} z {x y A}.
#[global]
Hint Extern 0 (nbhs _ (to_set _ _)) => exact: nbhs_entourage : core.

Lemma ent_closure {M : uniformType} (x : M) E : entourage E ->
  closure (to_set (split_ent E) x) `<=` to_set E x.
Proof.
pose E' := (split_ent E) `&` ((split_ent E)^-1)%classic.
move=> entE z /(_ [set y | E' (z, y)])[].
  by rewrite -nbhs_entourageE; exists E' => //; exact: filterI.
by move=> y [/=] + [_]; exact: entourage_split.
Qed.

Lemma continuous_withinNx {U V : uniformType} (f : U -> V) x :
  {for x, continuous f} <-> f @ x^' --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /dnbhs !near_simpl near_withinE.
  by rewrite /dnbhs; apply: cvg_within; apply: cfx.
rewrite !nbhs_nearE !near_map !near_nbhs in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Unshelve. all: by end_near. Qed.

(* This property is primarily useful only for metrizability on uniform spaces *)
Definition countable_uniformity (T : uniformType) :=
  exists R : set (set (T * T)), [/\
    countable R,
    R `<=` entourage &
    forall P, entourage P -> exists2 Q, R Q & Q `<=` P].

Lemma countable_uniformityP {T : uniformType} :
  countable_uniformity T <-> exists2 f : nat -> set (T * T),
    (forall A, entourage A -> exists N, f N `<=` A) &
    (forall n, entourage (f n)).
Proof.
split=> [[M []]|[f fsubE entf]].
  move=> /pfcard_geP[-> _ /(_ _ entourageT)[]//|/unsquash f eM Msub].
  exists f; last by move=> n; apply: eM; exact: funS.
  by move=> ? /Msub [Q + ?] => /(@surj _ _ _ _ f)[n _ fQ]; exists n; rewrite fQ.
exists (range f); split; first exact: card_image_le.
  by move=> E [n _] <-; exact: entf.
by move=> E /fsubE [n fnA]; exists (f n) => //; exists n.
Qed.

Section uniform_closeness.

Variable (U : uniformType).

Lemma open_nbhs_entourage (x : U) (A : set (U * U)) :
  entourage A -> open_nbhs x (to_set A x)^°.
Proof.
move=> entA; split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; apply: nbhs_entourage.
Qed.

Lemma entourage_close (x y : U) : close x y = forall A, entourage A -> A (x, y).
Proof.
rewrite propeqE; split=> [cxy A entA|cxy].
  have /entourage_split_ent entsA := entA; rewrite closeEnbhs in cxy.
  have yl := nbhs_entourage _ (entourage_inv entsA).
  have yr := nbhs_entourage _ entsA.
  have [z [zx zy]] := cxy _ _ (yr x) (yl y).
  exact: (entourage_split z).
rewrite closeEnbhs => A B /nbhsP[E1 entE1 sE1A] /nbhsP[E2 entE2 sE2B].
by exists y; split;[apply: sE1A; apply: cxy|apply: sE2B; apply: entourage_refl].
Qed.

Lemma close_trans (y x z : U) : close x y -> close y z -> close x z.
Proof.
rewrite !entourage_close => cxy cyz A entA.
exact: entourage_split (cxy _ _) (cyz _ _).
Qed.

Lemma close_cvgxx (x y : U) : close x y -> x --> y.
Proof.
rewrite entourage_close => cxy P /= /nbhsP[A entA sAP].
apply/nbhsP; exists (split_ent A) => // z xz; apply: sAP.
apply: (entourage_split x) => //.
by have := cxy _ (entourage_inv (entourage_split_ent entA)).
Qed.

Lemma cvg_closeP (F : set (set U)) (l : U) : ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Proof.
move=> FF; split=> [Fl|[cvF]Cl].
  by have /cvgP := Fl; split=> //; apply: (@cvg_close _ F).
by apply: cvg_trans (close_cvgxx Cl).
Qed.

End uniform_closeness.

Definition unif_continuous (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourage --> entourage.

(** product of two uniform spaces *)

Section prod_Uniform.

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
have prodF := filter_prod_filter (@entourage_pfilter U) (@entourage_pfilter V).
split; rewrite /prod_ent; last 1 first.
- by move=> A B sAB /=; apply: filterS => ? [xy /sAB ??]; exists xy.
- by rewrite -setMTT; apply: prod_entP filterT filterT.
move=> A B /= entA entB; apply: filterS (filterI entA entB) => xy [].
move=> [zt Azt ztexy] [zt' Bzt' zt'exy]; exists zt => //; split=> //.
move/eqP: ztexy; rewrite -zt'exy !xpair_eqE.
by rewrite andbACA -!xpair_eqE -!surjective_pairing => /eqP->.
Qed.

Lemma prod_ent_refl A : prod_ent A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
move=> [B [entB1 entB2] sBA] xy /eqP.
rewrite [_.1]surjective_pairing [xy.2]surjective_pairing xpair_eqE.
move=> /andP [/eqP xy1e /eqP xy2e].
have /sBA : (B.1 `*` B.2) ((xy.1.1, xy.2.1), (xy.1.2, xy.2.2)).
  by rewrite xy1e xy2e; split=> /=; apply: entourage_refl.
move=> [zt Azt /eqP]; rewrite !xpair_eqE.
by rewrite andbACA -!xpair_eqE -!surjective_pairing => /eqP<-.
Qed.

Lemma prod_ent_inv A : prod_ent A -> prod_ent (A^-1)%classic.
Proof.
move=> [B [/entourage_inv entB1 /entourage_inv entB2] sBA].
have:= prod_entP entB1 entB2; rewrite /prod_ent/=; apply: filterS.
move=> _ [p /(sBA (_,_)) [[x y] ? xyE] <-]; exists (y,x) => //; move/eqP: xyE.
by rewrite !xpair_eqE => /andP[/andP[/eqP-> /eqP->] /andP[/eqP-> /eqP->]].
Qed.

Lemma prod_ent_split A : prod_ent A -> exists2 B, prod_ent B & B \; B `<=` A.
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
  by move=> uv [/= /sCB1 Buv1 /sCB2 /(conj Buv1) /sBA].
exists (to_set (C.1) (xy.1), to_set (C.2) (xy.2)).
  by rewrite -!nbhs_entourageE; split; [exists C.1|exists C.2].
move=> uv [/= Cxyuv1 Cxyuv2]; apply: sBA.
have /sCB : (C.1 `*` C.2) ((xy.1,uv.1),(xy.2,uv.2)) by [].
move=> [zt Bzt /eqP]; rewrite !xpair_eqE andbACA -!xpair_eqE.
by rewrite /= -!surjective_pairing => /eqP<-.
Qed.

Definition prod_uniformType_mixin :=
  Uniform.Mixin prod_ent_filter prod_ent_refl prod_ent_inv prod_ent_split
  prod_ent_nbhsE.

End prod_Uniform.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (@prod_uniformType_mixin U V).

(** matrices *)

Section matrix_Uniform.

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

Lemma mx_ent_refl A : mx_ent A -> [set MN | MN.1 = MN.2] `<=` A.
Proof.
move=> [B entB sBA] MN MN1e2; apply: sBA => i j.
by rewrite MN1e2; apply: entourage_refl.
Qed.

Lemma mx_ent_inv A : mx_ent A -> mx_ent (A^-1)%classic.
Proof.
move=> [B entB sBA]; exists (fun i j => ((B i j)^-1)%classic).
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
  set sB := fun i j => [set C | entourage C /\ to_set C (M i j) `<=` B i j].
  have {}M_B : forall i j, sB i j !=set0 by move=> ??; apply/exists2P/M_B.
  exists [set MN : 'M[T]_(m, n) * 'M[T]_(m, n) | forall i j,
    get (sB i j) (MN.1 i j, MN.2 i j)].
    by exists (fun i j => get (sB i j)) => // i j; have /getPex [] := M_B i j.
  move=> N CMN; apply/sBA => i j; have /getPex [_] := M_B i j; apply.
  exact/CMN.
move=> [B [C entC sCB] sBA]; exists (fun i j => to_set (C i j) (M i j)).
  by rewrite -nbhs_entourageE => i j; exists (C i j).
by move=> N CMN; apply/sBA/sCB.
Qed.

Definition matrix_uniformType_mixin :=
  Uniform.Mixin mx_ent_filter mx_ent_refl mx_ent_inv mx_ent_split
  mx_ent_nbhsE.

Canonical matrix_uniformType :=
  UniformType 'M[T]_(m, n) matrix_uniformType_mixin.

End matrix_Uniform.

Lemma cvg_mx_entourageP (T : uniformType) m n (F : set (set 'M[T]_(m,n)))
  (FF : Filter F) (M : 'M[T]_(m,n)) :
  F --> M <->
  forall A, entourage A -> \forall N \near F,
  forall i j, A (M i j, (N : 'M[T]_(m,n)) i j).
Proof.
split.
  by rewrite filter_fromP => FM A ?; apply: (FM (fun i j => to_set A (M i j))).
move=> FM; apply/cvg_entourageP => A [P entP sPA]; near=> N.
apply: sPA => /=; near: N; set Q := \bigcap_ij P ij.1 ij.2.
apply: filterS (FM Q _); first by move=> N QN i j; apply: (QN _ _ (i, j)).
have -> : Q =
  \bigcap_(ij in [set k | k \in [fset x in predT]%fset]) P ij.1 ij.2.
  by rewrite predeqE => t; split=> Qt ij _; apply: Qt => //=; rewrite !inE.
by apply: filter_bigI => ??; apply: entP.
Unshelve. all: by end_near. Qed.

(** Functional metric spaces *)

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_ent :=
  filter_from
  (@entourage U)
  (fun P => [set fg | forall t : T, P (fg.1 t, fg.2 t)]).

Lemma fct_ent_filter : Filter fct_ent.
Proof.
apply: filter_from_filter; first by exists setT; apply: filterT.
move=> A B entA entB.
exists (A `&` B); first exact: filterI.
by move=> fg ABfg; split=> t; have [] := ABfg t.
Qed.

Lemma fct_ent_refl A : fct_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Proof.
move=> [B entB sBA] fg feg; apply/sBA => t; rewrite feg.
exact: entourage_refl.
Qed.

Lemma fct_ent_inv A : fct_ent A -> fct_ent (A^-1)%classic.
Proof.
move=> [B entB sBA]; exists (B^-1)%classic; first exact: entourage_inv.
by move=> fg Bgf; apply/sBA.
Qed.

Lemma fct_ent_split A : fct_ent A -> exists2 B, fct_ent B & B \; B `<=` A.
Proof.
move=> [B entB sBA].
(* have Bsplit : exists C, entourage C /\ C \o C `<=` B. *)
(*   exact/exists2P/entourage_split_ex. *)
exists [set fg | forall t, split_ent B (fg.1 t, fg.2 t)].
  by exists (split_ent B).
move=> fg [h spBfh spBhg].
by apply: sBA => t; apply: entourage_split (spBfh t) (spBhg t).
Qed.

Definition fct_uniformType_mixin :=
  UniformMixin fct_ent_filter fct_ent_refl fct_ent_inv fct_ent_split erefl.

Definition fct_topologicalTypeMixin :=
  topologyOfEntourageMixin fct_uniformType_mixin.

Canonical generic_source_filter := @Filtered.Source _ _ _ (nbhs_ fct_ent).
Canonical fct_topologicalType :=
  TopologicalType (T -> U) fct_topologicalTypeMixin.
Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.

End fct_Uniform.

Lemma cvg_fct_entourageP (T : choiceType) (U : uniformType)
  (F : set (set (T -> U))) (FF : Filter F) (f : T -> U) :
  F --> f <->
  forall A, entourage A ->
  \forall g \near F, forall t, A (f t, g t).
Proof.
split.
  move=> /cvg_entourageP Ff A entA.
  by apply: (Ff [set fg | forall t : T, A (fg.1 t, fg.2 t)]); exists A.
move=> Ff; apply/cvg_entourageP => A [P entP sPA].
by near=> g do apply: sPA; apply: Ff.
Unshelve. all: by end_near. Qed.

Definition entourage_set (U : uniformType) (A : set ((set U) * (set U))) :=
  exists2 B, entourage B & forall PQ, A PQ -> forall p q,
    PQ.1 p -> PQ.2 q -> B (p,q).
Canonical set_filter_source (U : uniformType) :=
  @Filtered.Source Prop _ U (fun A => nbhs_ (@entourage_set U) A).

(** * PseudoMetric spaces defined using balls *)

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Lemma entourage_E {R : numDomainType} {T T'} (ball : T -> R -> set T') :
  entourage_ ball =
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).
Proof. by []. Qed.

Definition map_pair {S U} (f : S -> U) (x : (S * S)) : (U * U) :=
  (f x.1, f x.2).

Section weak_uniform.

Variable (pS : pointedType) (U : uniformType) (f : pS -> U).

Let S := weak_topologicalType f.

Definition weak_ent : set (set (S * S)) :=
  filter_from (@entourage U) (fun V => (map_pair f)@^-1` V).

Lemma weak_ent_filter : Filter weak_ent.
Proof.
apply: filter_from_filter; first by exists setT; exact: entourageT.
by move=> P Q ??; (exists (P `&` Q); first exact: filterI) => ?.
Qed.

Lemma weak_ent_refl A : weak_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Proof.
by move=> [B ? sBA] [x y] /= ->; apply/sBA; exact: entourage_refl.
Qed.

Lemma weak_ent_inv A : weak_ent A -> weak_ent (A^-1)%classic.
Proof.
move=> [B ? sBA]; exists (B^-1)%classic; first exact: entourage_inv.
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
have : nbhs (f x) to_set V' (f x) by apply/nbhsP; exists V'.
rewrite (@nbhsE U) => [[O [openU Ofx Osub]]].
(exists (f @^-1` O); repeat split => //); first by exists O => //.
by move=> w ? ; apply: V'subW; exact: Osub.
Qed.

Definition weak_uniform_mixin :=
  @UniformMixin S nbhs weak_ent
    weak_ent_filter weak_ent_refl weak_ent_inv weak_ent_split weak_ent_nbhs.

Definition weak_uniformType :=
  UniformType S weak_uniform_mixin.

End weak_uniform.

Section sup_uniform.

Variable (T : pointedType) (Ii : Type) (Tc : Ii -> Uniform.class_of T).

Let I : choiceType := classicType_choiceType Ii.
Let TS := fun i => Uniform.Pack (Tc i).
Let Tt := @sup_topologicalType T I Tc.
Let ent_of (p : I * set (T * T)) := `[< @entourage (TS p.1) p.2>].
Let IEnt := ChoiceType {p : (I * set (T * T)) | ent_of p} (sig_choiceMixin _).

Local Lemma IEnt_pointT (i : I) : ent_of (i, setT).
Proof. by apply/asboolP; exact: entourageT. Qed.

Definition sup_ent : (set (set (T * T))) :=
  filter_from (finI_from [set: IEnt] (fun p => (projT1 p).2)) id.

Ltac IEntP := move=> [[ /= + + /[dup] /asboolP]].

Definition sup_ent_filter : Filter sup_ent.
Proof.
apply: finI_filter; move=> J JsubEnt /=; exists (point, point).
by IEntP => i b /= /entourage_refl ? ? _.
Qed.

Lemma sup_ent_refl A : sup_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Proof.
by move=> [B [F ? <-] BA] [??] /= ->; apply/BA; IEntP => i w /= /entourage_refl.
Qed.

Lemma sup_ent_inv A : sup_ent A -> sup_ent (A^-1)%classic.
Proof.
move=> [B [F ? FB] BA]; exists (B^-1)%classic; last by move=> ?; exact: BA.
have inv : forall ie : IEnt, ent_of ((projT1 ie).1, ((projT1 ie).2)^-1)%classic.
  by IEntP=> ?? /entourage_inv ??; exact/asboolP.
exists [fset (fun x => @exist (I * set (T * T)) _ _ (inv x)) w | w in F]%fset.
  by move=> ? /imfsetP; IEntP => ???? ->; exact: in_setT.
rewrite -FB eqEsubset; split; case=> x y + ie.
  by move=> /(_ (exist ent_of _ (inv ie))) + ?; apply; apply/imfsetP; exists ie.
by move=> + /imfsetP [v vW ->]; exact.
Qed.

Lemma sup_ent_split A : sup_ent A -> exists2 B, sup_ent B & B \; B `<=` A.
Proof.
have spt : (forall ie : IEnt, ent_of ((projT1 ie).1,
    ((@split_ent (TS (projT1 ie).1) (projT1 ie).2)))).
  by case=> [[/= ??] /asboolP/entourage_split_ent ?]; exact/asboolP.
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
  rewrite /nbhs_of_open => [[? [[B  + <-] [W BW Wx] BV]]] => /(_ W BW) [].
  move=> F Fsup Weq; move: Weq Wx BW => <- Fx BF.
  case (pselect ([set: I] = set0)) => [I0 | /eqP/set0P [i0 _]].
    suff -> : V = setT  by exists setT; apply: filterT; exact: sup_ent_filter.
    rewrite -subTset => ??; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /Fsup/set_mem; rewrite /sup_subbase I0 bigcup_set0.
  have f : forall w, {p : IEnt |  w \in F -> to_set ((projT1 p).2) x `<=` w}.
    move=> /= v; apply: cid; case (pselect (v \in F)); first last.
      by move=> ?; exists (exist ent_of _ (IEnt_pointT i0)).
    move=> /[dup] /Fx vx /Fsup/set_mem [i _]; rewrite openE => /(_ x vx).
    by move=> /(@nbhsP (TS i)) [w /asboolP ent ?]; exists (exist _ (i, w) ent).
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2); first last.
    move=> v /= Fgw; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /[dup] ? /Fgw /= /(projT2 (f w)); exact.
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2) => //.
  exists [fset (fun i => (projT1 (f i))) w | w in F]%fset.
    by move=> u ?; exact: in_setT.
  rewrite eqEsubset; split => y + z.
    by move=>/(_ (projT1 (f z))) => + ?; apply; apply/imfsetP; exists z.
  by move=> Fgy /imfsetP [/= u uF ->]; exact: Fgy.
case=> E [D [/= F FsubEnt <-] FsubE EsubV]; apply: (filterS EsubV).
pose f : IEnt -> set T := fun w =>
  @interior (TS (projT1 w).1) (to_set ((projT1 w).2) (x)).
exists (\bigcap_(w in [set` F]) f w); repeat split.
- exists [set \bigcap_(w in [set` F]) f w]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset f w | w in F]%fset.
    move=> /= ? /imfsetP [[[/= i w /[dup] /asboolP entw ? Fiw ->]]].
    by apply/mem_set; rewrite /f /=; exists i => //; exact: open_interior.
  by rewrite set_imfset bigcap_image //=.
- by IEntP=> ? ? /open_nbhs_entourage entw ??; apply entw.
- by move=> t /= Ifwt; apply: FsubE => it /Ifwt/interior_subset.
Qed.

Definition sup_uniform_mixin:=
  @UniformMixin Tt nbhs
    sup_ent sup_ent_filter sup_ent_refl sup_ent_inv sup_ent_split sup_ent_nbhs.

Definition sup_uniformType := UniformType Tt sup_uniform_mixin.

Lemma countable_sup_ent :
  countable [set: Ii] -> (forall n, countable_uniformity (TS n)) ->
  countable_uniformity sup_uniformType.
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

Section product_uniform.

Variable (I : choiceType) (T : I -> uniformType).

Definition product_uniformType :=
  sup_uniformType (fun i => Uniform.class
    (weak_uniformType (fun f : dep_arrow_pointedType T => f i))).

End product_uniform.

Section discrete_uniform.

Context {T : topologicalType} {dsc: discrete_space T}.

Definition discrete_ent : set (set (T * T)) :=
  globally (range (fun x => (x, x))).

Program Definition discrete_uniform_mixin :=
  @UniformMixin T nbhs discrete_ent _ _ _ _ _.
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
Next Obligation.
rewrite dsc predeq2E => x V; split => [].
  move=> Px; exists (range (fun x => (x, x))) => //.
  by move=> z [i _] [+ <-] => ->; exact/principal_filterP.
by case=> U dV UV; apply/principal_filterP/UV/dV; exists x.
Qed.

Definition discrete_uniformType := UniformType T discrete_uniform_mixin.

End discrete_uniform.

Module PseudoMetric.

Record mixin_of (R : numDomainType) (M : Type)
    (entourage : set (set (M * M))) := Mixin {
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : entourage = entourage_ ball
}.

Record class_of (R : numDomainType) (M : Type) := Class {
  base : Uniform.class_of M;
  mixin : mixin_of R (Uniform.entourage base)
}.

Section ClassDef.
Variable R : numDomainType.
Structure type := Pack { sort; _ : class_of R sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of R cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of R xT).
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack ent (m : @mixin_of R T ent) :=
  fun bT (b : Uniform.class_of T) of phant_id (@Uniform.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of R T (Uniform.entourage b)) =>
  @Pack T (@Class R _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Notation pseudoMetricType := type.
Notation PseudoMetricType T m := (@pack _ T _ m _ _ idfun _ idfun).
Notation PseudoMetricMixin := Mixin.
Notation "[ 'pseudoMetricType' R 'of' T 'for' cT ]" := (@clone R T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pseudoMetricType' R 'of' T ]" := (@clone R T _ _ id)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T ]") : form_scope.

End Exports.

End PseudoMetric.

Export PseudoMetric.Exports.

Section PseudoMetricUniformity.

Let ball_le (R : numDomainType) (M : Type) (ent : set (set (M * M)))
    (m : PseudoMetric.mixin_of R ent) :
  forall (x : M), {homo PseudoMetric.ball m x : e1 e2 / e1 <= e2 >-> e1 `<=` e2}.
Proof.
move=> x e1 e2 + y xe1_y.
rewrite le_eqVlt => /predU1P[<- //|]; rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: PseudoMetric.ball_triangle xe1_y.
suff : PseudoMetric.ball m x (PosNum lt12)%:num x by [].
exact: PseudoMetric.ball_center.
Qed.

Program Definition uniformityOfBallMixin (R : numFieldType) (T : Type)
  (ent : set (set (T * T))) (nbhs : T -> set (set T)) (nbhsE : nbhs = nbhs_ ent)
  (m : PseudoMetric.mixin_of R ent) : Uniform.mixin_of nbhs :=
  UniformMixin _ _ _ _ nbhsE.
Next Obligation.
move=> R T ent nbhs nbhsE m; rewrite (PseudoMetric.entourageE m).
apply: filter_from_filter; first by exists 1 => /=.
move=> _ _ /posnumP[e1] /posnumP[e2]; exists (Num.min e1 e2)%:num => //=.
by rewrite subsetI; split=> ?; apply: ball_le;
   rewrite -leEsub// le_minl lexx ?orbT.
Qed.
Next Obligation.
move=> R T ent nbhs nbhsE m A; rewrite (PseudoMetric.entourageE m).
move=> [e egt0 sbeA] xy xey.
by apply: sbeA; rewrite /= xey; exact: PseudoMetric.ball_center.
Qed.
Next Obligation.
move=> R T ent nbhs nbhsE m A; rewrite (PseudoMetric.entourageE m) => - [e egt0 sbeA].
by exists e => // xy xye; apply: sbeA; apply: PseudoMetric.ball_sym.
Qed.
Next Obligation.
move=> R T ent nbhs nbhsE m A; rewrite (PseudoMetric.entourageE m).
move=> [_/posnumP[e] sbeA].
exists [set xy | PseudoMetric.ball m xy.1 (e%:num / 2) xy.2].
  by exists (e%:num / 2) => /=.
move=> xy [z xzhe zyhe]; apply: sbeA.
by rewrite [e%:num]splitr; apply: PseudoMetric.ball_triangle zyhe.
Qed.

End PseudoMetricUniformity.

Definition ball {R : numDomainType} {M : pseudoMetricType R} :=
  PseudoMetric.ball (PseudoMetric.class M).

Lemma entourage_ballE {R : numDomainType} {M : pseudoMetricType R}
  : entourage_ (@ball R M) = entourage.
Proof. by case: M=> [?[?[]]]. Qed.

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

Lemma nbhs_ballE {R : numDomainType} {M : pseudoMetricType R} : (@nbhs_ball R M) = nbhs.
Proof.
rewrite predeq2E => x P; rewrite -nbhs_entourageE; split.
  by move=> [_/posnumP[e] sbxeP]; exists [set xy | ball xy.1 e%:num xy.2].
rewrite -entourage_ballE; move=> [A [e egt0 sbeA] sAP].
by exists e => // ??; apply/sAP/sbeA.
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
Proof. exact: PseudoMetric.ball_center. Qed.
#[global] Hint Resolve ball_center : core.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.

Lemma ballxx (x : M) (e : R) : 0 < e -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: PseudoMetric.ball_sym. Qed.

Lemma ball_symE (x y : M) (e : R) : ball x e y = ball y e x.
Proof. by rewrite propeqE; split; exact/ball_sym. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: PseudoMetric.ball_triangle. Qed.

Lemma nbhsx_ballx (x : M) (eps : {posnum R}) : nbhs x (ball x eps%:num).
Proof. by apply/nbhs_ballP; exists eps%:num => /=. Qed.

Lemma open_nbhs_ball (x : M) (eps : {posnum R}) : open_nbhs x ((ball x eps%:num)^°).
Proof.
split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; apply:nbhsx_ballx.
Qed.

Lemma le_ball (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y. case: comparableP le12 => [lte12 _|//|//|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Global Instance entourage_proper_filter : ProperFilter (@entourage M).
Proof.
apply: Build_ProperFilter; rewrite -entourage_ballE => A [_/posnumP[e] sbeA].
by exists (point, point); apply: sbeA; apply: ballxx.
Qed.

Lemma near_ball (y : M) (eps : {posnum R}) :
   \forall y' \near y, ball y eps%:num y'.
Proof. exact: nbhsx_ballx. Qed.

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
#[global] Hint Resolve close_refl : core.
Arguments close_cvg {T} F1 F2 {FF2} _.

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

Lemma ball_close (x y : M) :
  close x y = forall eps : {posnum R}, ball x eps%:num y.
Proof.
rewrite propeqE; split => [cxy eps|cxy].
  have := !! cxy _ (open_nbhs_ball _ (eps%:num/2)%:pos).
  rewrite closureEonbhs/= meetsC meets_globallyr.
  move/(_ _ (open_nbhs_ball _ (eps%:num/2)%:pos)) => [z [zx zy]].
  by apply: (@ball_splitl z); apply: interior_subset.
rewrite closeEnbhs => B A /nbhs_ballP[_/posnumP[e2 e2B]]
  /nbhs_ballP[_/posnumP[e1 e1A]].
by exists y; split; [apply/e2B|apply/e1A; exact: ballxx].
Qed.

End pseudoMetricType_numFieldType.

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
exists `|floor e^-1|%N; apply: subset_trans subE => xy; apply: le_ball.
rewrite /= -[leRHS]invrK lef_pinv ?posrE ?invr_gt0// -natr1.
by rewrite natr_absz ger0_norm ?floor_ge0 ?invr_ge0// 1?ltW// lt_succ_floor.
Qed.

(** ** Specific pseudoMetric spaces *)

(** matrices *)
Section matrix_PseudoMetric.
Variables (m n : nat) (R : numDomainType) (T : pseudoMetricType R).
Implicit Types x y : 'M[T]_(m, n).
Definition mx_ball x (e : R) y := forall i j, ball (x i j) e (y i j).
Lemma mx_ball_center x (e : R) : 0 < e -> mx_ball x e x.
Proof. by move=> ???; apply: ballxx. Qed.
Lemma mx_ball_sym x y (e : R) : mx_ball x e y -> mx_ball y e x.
Proof. by move=> xe_y ??; apply/ball_sym/xe_y. Qed.
Lemma mx_ball_triangle x y z (e1 e2 : R) :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ??; apply: ball_triangle; [apply: xe1_y| apply: ye2_z].
Qed.

Lemma mx_entourage : entourage = entourage_ mx_ball.
Proof.
rewrite predeqE=> A; split; last first.
  move=> [_/posnumP[e] sbeA].
  by exists (fun _ _ => [set xy | ball xy.1 e%:num xy.2]).
move=> [P]; rewrite -entourage_ballE => entP sPA.
set diag := fun (e : {posnum R}) => [set xy : T * T | ball xy.1 e%:num xy.2].
exists (\big[Num.min/1%:pos]_i \big[Num.min/1%:pos]_j xget 1%:pos
  (fun e : {posnum R} => diag e `<=` P i j))%:num => //=.
move=> MN MN_min; apply: sPA => i j.
have /(xgetPex 1%:pos): exists e : {posnum R}, diag e `<=` P i j.
  by have [_/posnumP[e]] := entP i j; exists e.
apply; apply: le_ball (MN_min i j).
apply: le_trans (@bigmin_le _ [orderType of {posnum R}] _ _ i _) _.
exact: bigmin_le.
Qed.
Definition matrix_pseudoMetricType_mixin :=
  PseudoMetric.Mixin mx_ball_center mx_ball_sym mx_ball_triangle mx_entourage.
Canonical matrix_pseudoMetricType :=
  PseudoMetricType 'M[T]_(m, n) matrix_pseudoMetricType_mixin.
End matrix_PseudoMetric.

(** product of two pseudoMetric spaces *)
Section prod_PseudoMetric.
Context {R : numDomainType} {U V : pseudoMetricType R}.
Implicit Types (x y : U * V).
Definition prod_point : U * V := (point, point).
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
  by apply: le_ball bac; rewrite -leEsub le_minl lexx.
by apply: le_ball bbd; rewrite -leEsub le_minl lexx orbT.
Qed.
Definition prod_pseudoMetricType_mixin :=
  PseudoMetric.Mixin prod_ball_center prod_ball_sym prod_ball_triangle prod_entourage.
End prod_PseudoMetric.

Canonical prod_pseudoMetricType (R : numDomainType) (U V : pseudoMetricType R) :=
  PseudoMetricType (U * V) (@prod_pseudoMetricType_mixin R U V).

Section Nbhs_fct2.
Context {T : Type} {R : numDomainType} {U V : pseudoMetricType R}.
Lemma fcvg_ball2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall y' \near F & z' \near G,
                ball y eps y' /\ ball z eps z'.
Proof. exact: fcvg_ballP. Qed.

Lemma cvg_ball2P {I J} {F : set (set I)} {G : set (set J)}
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

(** Functional metric spaces *)
Section fct_PseudoMetric.
Variable (T : choiceType) (R : numFieldType) (U : pseudoMetricType R).
Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).
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
Definition fct_pseudoMetricType_mixin :=
  PseudoMetricMixin fct_ball_center fct_ball_sym fct_ball_triangle fct_entourage.
Canonical fct_pseudoMetricType := PseudoMetricType (T -> U) fct_pseudoMetricType_mixin.
End fct_PseudoMetric.

Definition quotient_topology (T : topologicalType) (Q : quotType T) := Q.

Section quotients.
Local Open Scope quotient_scope.
Context {T : topologicalType} {Q0 : quotType T}.

Let Q := quotient_topology Q0.

Canonical quotient_subtype := [subType Q of T by %/].
Canonical quotient_eq := EqType Q [eqMixin of Q by <:].
Canonical quotient_choice := ChoiceType Q  [choiceMixin of Q by <:].
Canonical quotient_pointed := PointedType Q (\pi_Q point).

Definition quotient_open U := open (\pi_Q @^-1` U).

Program Definition quotient_topologicalType_mixin :=
  @topologyOfOpenMixin Q quotient_open _ _ _.
Next Obligation. by rewrite /quotient_open preimage_setT; exact: openT. Qed.
Next Obligation. by move=> ? ? ? ?; exact: openI. Qed.
Next Obligation. by move=> I f ofi; apply: bigcup_open => i _; exact: ofi. Qed.

Let quotient_filtered := Filtered.Class (Pointed.class quotient_pointed)
  (nbhs_of_open quotient_open).

Canonical quotient_topologicalType := @Topological.Pack Q
  (@Topological.Class _ quotient_filtered quotient_topologicalType_mixin).

Let Q' := quotient_topologicalType.

Lemma pi_continuous : continuous (\pi_Q : T -> Q').
Proof. exact/continuousP. Qed.

Lemma quotient_continuous {Z : topologicalType} (f : Q' -> Z) :
  continuous f <-> continuous (f \o \pi_Q).
Proof.
split => /continuousP /= cts; apply/continuousP => A oA; last exact: cts.
by rewrite comp_preimage; move/continuousP: pi_continuous; apply; exact: cts.
Qed.

Lemma repr_comp_continuous (Z : topologicalType) (g : T -> Z) :
  continuous g -> {homo g : a b / a == b %[mod Q] >-> a == b} ->
  continuous (g \o repr : Q' -> Z).
Proof.
move=> /continuousP ctsG rgE; apply/continuousP => A oA.
rewrite /open/= /quotient_open (_ : _ @^-1` _ = g @^-1` A); first exact: ctsG.
have greprE x : g (repr (\pi_Q x)) = g x by apply/eqP; rewrite rgE// reprK.
by rewrite eqEsubset; split => x /=; rewrite greprE.
Qed.

End quotients.

Section discrete_pseudoMetric.
Context {R : numDomainType} {T : topologicalType} {dsc : discrete_space T}.

Definition discrete_ball (x : T) (eps : R) y : Prop := x = y.

Lemma discrete_ball_center x (eps : R) : 0 < eps -> discrete_ball x eps x.
Proof. by []. Qed.

Program Definition discrete_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R T discrete_ent discrete_ball _ _ _ _.
Next Obligation. by done. Qed.
Next Obligation. by move=> ? ? ? ->. Qed.
Next Obligation. by move=> ? ? ? ? ? -> ->. Qed.
Next Obligation.
rewrite predeqE => P; split; last by case=> e _ + [a b] [i _] [-> ->]; apply.
move=> entP; exists 1 => //= z z12; apply: entP; exists z.1 => //.
by rewrite {2}z12 -surjective_pairing.
Qed.

Definition discrete_pseudoMetricType := PseudoMetricType
  (@discrete_uniformType _ dsc) discrete_pseudoMetricType_mixin.

End discrete_pseudoMetric.

Definition pseudoMetric_bool {R : realType} :=
  @discrete_pseudoMetricType R [topologicalType of bool] discrete_bool.

(** ** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set (set T)) := (F, F) --> entourage.

Lemma cvg_cauchy {T : uniformType} (F : set (set T)) : Filter F ->
  [cvg F in T] -> cauchy F.
Proof.
move=> FF cvF A entA; have /entourage_split_ex [B entB sB2A] := entA.
exists (to_set ((B^-1)%classic) (lim F), to_set B (lim F)).
  split=> /=; apply: cvF; rewrite /= -nbhs_entourageE; last by exists B.
  by exists (B^-1)%classic => //; apply: entourage_inv.
by move=> ab [/= Balima Blimb]; apply: sB2A; exists (lim F).
Qed.

Module Complete.
Definition axiom (T : uniformType) :=
  forall (F : set (set T)), ProperFilter F -> cauchy F -> F --> lim F.
Section ClassDef.
Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : axiom (Uniform.Pack base)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> Complete.axiom.
Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack b0 (m0 : axiom (@Uniform.Pack T b0)) :=
  fun bT b of phant_id (@Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m).
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
End ClassDef.
Module Exports.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Notation completeType := type.
Notation "[ 'completeType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completeType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completeType'  'of'  T ]") : form_scope.
Notation CompleteType T m := (@pack T _ m _ _ idfun _ idfun).
End Exports.
End Complete.
Export Complete.Exports.

Section completeType1.

Context {T : completeType}.

Lemma cauchy_cvg (F : set (set T)) (FF : ProperFilter F) :
  cauchy F -> cvg F.
Proof. by case: T F FF => [? [?]]. Qed.

Lemma cauchy_cvgP (F : set (set T)) (FF : ProperFilter F) : cauchy F <-> cvg F.
Proof. by split=> [/cauchy_cvg|/cvg_cauchy]. Qed.

End completeType1.
Arguments cauchy_cvg {T} F {FF} _.
Arguments cauchy_cvgP {T} F {FF}.

Section matrix_Complete.

Variables (T : completeType) (m n : nat).

Lemma mx_complete (F : set (set 'M[T]_(m, n))) :
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
apply: subset_split_ent => //; exists (M' i j) => /=.
  by near: M'; rewrite mxE; apply: cvF.
move: (i) (j); near: M'; near: M; apply: nearP_dep; apply: Fc.
by exists (fun _ _ => (split_ent A)^-1%classic) => ?? //; apply: entourage_inv.
Unshelve. all: by end_near. Qed.

Canonical matrix_completeType := CompleteType 'M[T]_(m, n) mx_complete.

End matrix_Complete.

Section fun_Complete.

Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set (set (T -> U)))
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
exists ((split_ent A)^-1)%classic=> //=.
Unshelve. all: by end_near. Qed.

Canonical fun_completeType := CompleteType (T -> U) fun_complete.

End fun_Complete.

(** ** Limit switching *)
Section Cvg_switch.
Context {T1 T2 : choiceType}.

Lemma cvg_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/cvg_app_entourageP => A entA.
near F1 => x1; near=> x2; apply: (entourage_split (h x1)) => //.
  by near: x1; apply/(hl (to_set _ l)) => /=.
apply: (entourage_split (f x1 x2)) => //.
  by near: x2; apply/(fh x1 (to_set _ _)) => /=.
move: (x2); near: x1; have /cvg_fct_entourageP /(_ (_^-1%classic)):= fg; apply.
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
  by near: x2; apply/(fh _ (to_set _ _)) => /=.
apply: (entourage_split (f y1 x2)) => //; last first.
  near: x2; apply/(fh _ (to_set ((_^-1)%classic) _)).
  exact: nbhs_entourage (entourage_inv _).
apply: (entourage_split (g x2)) => //; move: (x2); [near: x1|near: y1].
  have /cvg_fct_entourageP /(_ (_^-1)%classic) := fg; apply.
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
by exists [lim h @ F1 in U]; split=> //; apply: cvg_switch_1 Hfg Hfh hcv.
Qed.

End Cvg_switch.

(** ** Complete pseudoMetric spaces *)

Definition cauchy_ex {R : numDomainType} {T : pseudoMetricType R} (F : set (set T)) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy_ball {R : numDomainType} {T : pseudoMetricType R} (F : set (set T)) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_ballP (R : numDomainType) (T  : pseudoMetricType R)
    (F : set (set T)) (FF : Filter F) :
  cauchy_ball F <-> cauchy F.
Proof.
split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply/cauchyF/entourage_ball.
move=> U; rewrite -entourage_ballE => - [_/posnumP[eps] xyepsU].
by near do apply: xyepsU; apply: cauchyF.
Unshelve. all: by end_near. Qed.
Arguments cauchy_ballP {R T} F {FF}.

Lemma cauchy_exP (R : numFieldType) (T : pseudoMetricType R)
    (F : set (set T)) (FF : Filter F) :
  cauchy_ex F -> cauchy F.
Proof.
move=> Fc A; rewrite !nbhs_simpl /= -entourage_ballE => -[_/posnumP[e] sdeA].
have /Fc [z /= Fze] := [gt0 of e%:num / 2]; near=> x y; apply: sdeA => /=.
by apply: (@ball_splitr _ _ z); [near: x|near: y].
Unshelve. all: by end_near. Qed.
Arguments cauchy_exP {R T} F {FF}.

Lemma cauchyP (R : numFieldType) (T : pseudoMetricType R)
    (F : set (set T)) (PF : ProperFilter F) :
  cauchy F <-> cauchy_ex F.
Proof.
split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
near F => x; exists x; near: x; apply: (@nearP_dep _ _ F F).
exact/Fcauchy/entourage_ball.
Unshelve. all: by end_near. Qed.
Arguments cauchyP {R T} F {PF}.

Lemma compact_cauchy_cvg {T : uniformType} (U : set T) (F : set (set T)) :
  ProperFilter F -> cauchy F -> F U -> compact U -> cvg F.
Proof.
move=> PF cf FU /(_ F PF FU) [x [_ clFx]]; apply: (cvgP x).
apply/cvg_entourageP => E entE.
have : nbhs entourage (split_ent E) by rewrite nbhs_filterE.
move=> /(cf (split_ent E))[] [D1 D2]/= /[!nbhs_simpl] -[FD1 FD2 D1D2E].
have : nbhs x to_set (split_ent E) x by exact: nbhs_entourage.
move=> /(clFx _ (to_set (split_ent E) x) FD1)[z [Dz Exz]].
by near=> t; apply/(entourage_split z entE Exz)/D1D2E; split => //; near: t.
Unshelve. all: by end_near. Qed.

Module CompletePseudoMetric.
Section ClassDef.
Variable R : numDomainType.
Record class_of (T : Type) := Class {
  base : PseudoMetric.class_of R T;
  mixin : Complete.axiom (Uniform.Pack base)
}.
Local Coercion base : class_of >-> PseudoMetric.class_of.
Definition base2 T m := Complete.Class (@mixin T m).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (@PseudoMetric.class R bT) (b : PseudoMetric.class_of R T) =>
  fun mT m & phant_id (Complete.class mT) (@Complete.Class T b m) =>
  Pack (@Class T b m).
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition completeType := @Complete.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pseudoMetric_completeType := @Complete.Pack pseudoMetricType xclass.
End ClassDef.
Module Exports.
Coercion base : class_of >-> PseudoMetric.class_of.
Coercion mixin : class_of >-> Complete.axiom.
Coercion base2 : class_of >-> Complete.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pseudoMetric_completeType.
Notation completePseudoMetricType := type.
Notation "[ 'completePseudoMetricType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completePseudoMetricType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completePseudoMetricType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completePseudoMetricType'  'of'  T ]") : form_scope.
Notation CompletePseudoMetricType T m := (@pack _ T _ _ id _ _ id).
End Exports.
End CompletePseudoMetric.
Export CompletePseudoMetric.Exports.

Canonical matrix_completePseudoMetricType (R : numFieldType)
  (T : completePseudoMetricType R) (m n : nat) :=
  CompletePseudoMetricType 'M[T]_(m, n) mx_complete.

Canonical fct_completePseudoMetricType (T : choiceType) (R : numFieldType)
  (U : completePseudoMetricType R) :=
  CompletePseudoMetricType (T -> U) fun_complete.

Definition pointed_of_zmodule (R : zmodType) : pointedType := PointedType R 0.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%R y /.

Lemma subset_ball_prop_in_itv (R : realDomainType) (x : R) e P :
  (ball_ Num.Def.normr x e `<=` P)%classic <->
  {in `](x - e), (x + e)[, forall y, P y}.
Proof.
by split=> exP y /=; rewrite ?in_itv (ltr_distlC, =^~ltr_distlC); apply: exP.
Qed.

Lemma subset_ball_prop_in_itvcc (R : realDomainType) (x : R) e P : 0 < e ->
  (ball_ Num.Def.normr x (2 * e) `<=` P)%classic ->
  {in `[(x - e), (x + e)], forall y, P y}.
Proof.
move=> e_gt0 PP y; rewrite in_itv/= -ler_distlC => ye; apply: PP => /=.
by rewrite (le_lt_trans ye)// ltr_pmull// ltr1n.
Qed.

Global Instance ball_filter (R : realDomainType) (t : R) : Filter
  [set P | exists2 i : R, 0 < i & ball_ Num.norm t i `<=` P].
Proof.
apply: Build_Filter; [by exists 1 | move=> P Q | move=> P Q PQ]; rewrite /mkset.
- move=> -[x x0 xP] [y ? yQ]; exists (Num.min x y); first by rewrite lt_minr x0.
  move=> z tz; split.
    by apply: xP; rewrite /= (lt_le_trans tz) // le_minl lexx.
  by apply: yQ; rewrite /= (lt_le_trans tz) // le_minl lexx orbT.
- by move=> -[x ? xP]; exists x => //; apply: (subset_trans xP).
Qed.

#[global] Hint Extern 0 (Filter [set P | exists2 i, _ & ball_ _ _ i `<=` P]) =>
  (apply: ball_filter) : typeclass_instances.

Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R := Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|)))).

Section pseudoMetric_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Proof. by move=> ? /=; rewrite subrr normr0. Qed.
Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Proof. by rewrite /= distrC. Qed.
Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Proof.
move=> /= ? ?; rewrite -(subr0 x) -(subrr y) opprD opprK (addrA x _ y) -addrA.
by rewrite (le_lt_trans (ler_norm_add _ _)) // ltr_add.
Qed.
Definition pseudoMetric_of_normedDomain
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|)))
  := PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Proof.
rewrite /nbhs_ entourage_E predeq2E => x A; split.
  move=> [e egt0 sbeA].
  by exists [set xy | ball_ Num.norm xy.1 e xy.2] => //; exists e.
by move=> [E [e egt0 sbeE] sEA]; exists e => // ??; apply/sEA/sbeE.
Qed.
End pseudoMetric_of_normedDomain.

Module regular_topology.

Section regular_topology.
Local Canonical pointedType (R : zmodType) : pointedType :=
  [pointedType of R^o for pointed_of_zmodule R].
Local Canonical filteredType (R : numDomainType) : filteredType R :=
  [filteredType R of R^o for filtered_of_normedZmod R].
Local Canonical topologicalType (R : numFieldType) : topologicalType :=
  TopologicalType R^o (topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Local Canonical uniformType (R : numFieldType) : uniformType :=
  UniformType R^o (uniformityOfBallMixin
                     (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)).
Local Canonical pseudoMetricType (R : numFieldType) :=
  PseudoMetricType R^o (@pseudoMetric_of_normedDomain R R).
End regular_topology.

Module Exports.
Canonical pointedType.
Canonical filteredType.
Canonical topologicalType.
Canonical uniformType.
Canonical pseudoMetricType.
End Exports.

End regular_topology.
Export regular_topology.Exports.

Module numFieldTopology.

Section realType.
Variable (R : realType).
Local Canonical real_pointedType := [pointedType of R for [pointedType of R^o]].
Local Canonical real_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical real_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical real_uniformType := [uniformType of R for [uniformType of R^o]].
Local Canonical real_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End realType.

Section rcfType.
Variable (R : rcfType).
Local Canonical rcf_pointedType := [pointedType of R for [pointedType of R^o]].
Local Canonical rcf_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical rcf_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical rcf_uniformType := [uniformType of R for [uniformType of R^o]].
Local Canonical rcf_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
Local Canonical archiField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical archiField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical archiField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical archiField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical archiField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
Local Canonical realField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical realField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical realField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical realField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical realField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_latticeType := [latticeType of realField_pointedType].
Definition pointed_distrLatticeType :=
  [distrLatticeType of realField_pointedType].
Definition pointed_orderType := [orderType of realField_pointedType].
Definition pointed_realDomainType :=
  [realDomainType of realField_pointedType].
Definition filtered_latticeType := [latticeType of realField_filteredType].
Definition filtered_distrLatticeType :=
  [distrLatticeType of realField_filteredType].
Definition filtered_orderType := [orderType of realField_filteredType].
Definition filtered_realDomainType :=
  [realDomainType of realField_filteredType].
Definition topological_latticeType :=
  [latticeType of realField_topologicalType].
Definition topological_distrLatticeType :=
  [distrLatticeType of realField_topologicalType].
Definition topological_orderType := [orderType of realField_topologicalType].
Definition topological_realDomainType :=
  [realDomainType of realField_topologicalType].
Definition uniform_latticeType := [latticeType of realField_uniformType].
Definition uniform_distrLatticeType :=
  [distrLatticeType of realField_uniformType].
Definition uniform_orderType := [orderType of realField_uniformType].
Definition uniform_realDomainType := [realDomainType of realField_uniformType].
Definition pseudoMetric_latticeType :=
  [latticeType of realField_pseudoMetricType].
Definition pseudoMetric_distrLatticeType :=
  [distrLatticeType of realField_pseudoMetricType].
Definition pseudoMetric_orderType := [orderType of realField_pseudoMetricType].
Definition pseudoMetric_realDomainType :=
  [realDomainType of realField_pseudoMetricType].
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
Local Canonical numClosedField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical numClosedField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical numClosedField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical numClosedField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical numClosedField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_decFieldType :=
  [decFieldType of numClosedField_pointedType].
Definition pointed_closedFieldType :=
  [closedFieldType of numClosedField_pointedType].
Definition filtered_decFieldType :=
  [decFieldType of numClosedField_filteredType].
Definition filtered_closedFieldType :=
  [closedFieldType of numClosedField_filteredType].
Definition topological_decFieldType :=
  [decFieldType of numClosedField_topologicalType].
Definition topological_closedFieldType :=
  [closedFieldType of numClosedField_topologicalType].
Definition uniform_decFieldType := [decFieldType of numClosedField_uniformType].
Definition uniform_closedFieldType :=
  [closedFieldType of numClosedField_uniformType].
Definition pseudoMetric_decFieldType :=
  [decFieldType of numClosedField_pseudoMetricType].
Definition pseudoMetric_closedFieldType :=
  [closedFieldType of numClosedField_pseudoMetricType].
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical numField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical numField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical numField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical numField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_ringType := [ringType of numField_pointedType].
Definition pointed_comRingType := [comRingType of numField_pointedType].
Definition pointed_unitRingType := [unitRingType of numField_pointedType].
Definition pointed_comUnitRingType := [comUnitRingType of numField_pointedType].
Definition pointed_idomainType := [idomainType of numField_pointedType].
Definition pointed_fieldType := [fieldType of numField_pointedType].
Definition pointed_porderType := [porderType of numField_pointedType].
Definition pointed_numDomainType := [numDomainType of numField_pointedType].
Definition filtered_ringType := [ringType of numField_filteredType].
Definition filtered_comRingType := [comRingType of numField_filteredType].
Definition filtered_unitRingType := [unitRingType of numField_filteredType].
Definition filtered_comUnitRingType :=
  [comUnitRingType of numField_filteredType].
Definition filtered_idomainType := [idomainType of numField_filteredType].
Definition filtered_fieldType := [fieldType of numField_filteredType].
Definition filtered_porderType := [porderType of numField_filteredType].
Definition filtered_numDomainType := [numDomainType of numField_filteredType].
Definition topological_ringType := [ringType of numField_topologicalType].
Definition topological_comRingType := [comRingType of numField_topologicalType].
Definition topological_unitRingType :=
  [unitRingType of numField_topologicalType].
Definition topological_comUnitRingType :=
  [comUnitRingType of numField_topologicalType].
Definition topological_idomainType := [idomainType of numField_topologicalType].
Definition topological_fieldType := [fieldType of numField_topologicalType].
Definition topological_porderType := [porderType of numField_topologicalType].
Definition topological_numDomainType :=
  [numDomainType of numField_topologicalType].
Definition uniform_ringType := [ringType of numField_uniformType].
Definition uniform_comRingType := [comRingType of numField_uniformType].
Definition uniform_unitRingType := [unitRingType of numField_uniformType].
Definition uniform_comUnitRingType := [comUnitRingType of numField_uniformType].
Definition uniform_idomainType := [idomainType of numField_uniformType].
Definition uniform_fieldType := [fieldType of numField_uniformType].
Definition uniform_porderType := [porderType of numField_uniformType].
Definition uniform_numDomainType := [numDomainType of numField_uniformType].
Definition pseudoMetric_ringType := [ringType of numField_pseudoMetricType].
Definition pseudoMetric_comRingType :=
  [comRingType of numField_pseudoMetricType].
Definition pseudoMetric_unitRingType :=
  [unitRingType of numField_pseudoMetricType].
Definition pseudoMetric_comUnitRingType :=
  [comUnitRingType of numField_pseudoMetricType].
Definition pseudoMetric_idomainType :=
  [idomainType of numField_pseudoMetricType].
Definition pseudoMetric_fieldType := [fieldType of numField_pseudoMetricType].
Definition pseudoMetric_porderType := [porderType of numField_pseudoMetricType].
Definition pseudoMetric_numDomainType :=
  [numDomainType of numField_pseudoMetricType].
End numFieldType.

Module Exports.
(* realType *)
Canonical real_pointedType.
Canonical real_filteredType.
Canonical real_topologicalType.
Canonical real_uniformType.
Canonical real_pseudoMetricType.
Coercion real_pointedType : realType >-> pointedType.
Coercion real_filteredType : realType >-> filteredType.
Coercion real_topologicalType : realType >-> topologicalType.
Coercion real_uniformType : realType >-> uniformType.
Coercion real_pseudoMetricType : realType >-> pseudoMetricType.
(* rcfType *)
Canonical rcf_pointedType.
Canonical rcf_filteredType.
Canonical rcf_topologicalType.
Canonical rcf_uniformType.
Canonical rcf_pseudoMetricType.
Coercion rcf_pointedType : rcfType >-> pointedType.
Coercion rcf_filteredType : rcfType >-> filteredType.
Coercion rcf_topologicalType : rcfType >-> topologicalType.
Coercion rcf_uniformType : rcfType >-> uniformType.
Coercion rcf_pseudoMetricType : rcfType >-> pseudoMetricType.
(* archiFieldType *)
Canonical archiField_pointedType.
Canonical archiField_filteredType.
Canonical archiField_topologicalType.
Canonical archiField_uniformType.
Canonical archiField_pseudoMetricType.
Coercion archiField_pointedType : archiFieldType >-> pointedType.
Coercion archiField_filteredType : archiFieldType >-> filteredType.
Coercion archiField_topologicalType : archiFieldType >-> topologicalType.
Coercion archiField_uniformType : archiFieldType >-> uniformType.
Coercion archiField_pseudoMetricType : archiFieldType >-> pseudoMetricType.
(* realFieldType *)
Canonical realField_pointedType.
Canonical realField_filteredType.
Canonical realField_topologicalType.
Canonical realField_uniformType.
Canonical realField_pseudoMetricType.
Canonical pointed_latticeType.
Canonical pointed_distrLatticeType.
Canonical pointed_orderType.
Canonical pointed_realDomainType.
Canonical filtered_latticeType.
Canonical filtered_distrLatticeType.
Canonical filtered_orderType.
Canonical filtered_realDomainType.
Canonical topological_latticeType.
Canonical topological_distrLatticeType.
Canonical topological_orderType.
Canonical topological_realDomainType.
Canonical uniform_latticeType.
Canonical uniform_distrLatticeType.
Canonical uniform_orderType.
Canonical uniform_realDomainType.
Canonical pseudoMetric_latticeType.
Canonical pseudoMetric_distrLatticeType.
Canonical pseudoMetric_orderType.
Canonical pseudoMetric_realDomainType.
Coercion realField_pointedType : realFieldType >-> pointedType.
Coercion realField_filteredType : realFieldType >-> filteredType.
Coercion realField_topologicalType : realFieldType >-> topologicalType.
Coercion realField_uniformType : realFieldType >-> uniformType.
Coercion realField_pseudoMetricType : realFieldType >-> pseudoMetricType.
(* numClosedFieldType *)
Canonical numClosedField_pointedType.
Canonical numClosedField_filteredType.
Canonical numClosedField_topologicalType.
Canonical numClosedField_uniformType.
Canonical numClosedField_pseudoMetricType.
Canonical pointed_decFieldType.
Canonical pointed_closedFieldType.
Canonical filtered_decFieldType.
Canonical filtered_closedFieldType.
Canonical topological_decFieldType.
Canonical topological_closedFieldType.
Canonical uniform_decFieldType.
Canonical uniform_closedFieldType.
Canonical pseudoMetric_decFieldType.
Canonical pseudoMetric_closedFieldType.
Coercion numClosedField_pointedType : numClosedFieldType >-> pointedType.
Coercion numClosedField_filteredType : numClosedFieldType >-> filteredType.
Coercion numClosedField_topologicalType :
  numClosedFieldType >-> topologicalType.
Coercion numClosedField_uniformType : numClosedFieldType >-> uniformType.
Coercion numClosedField_pseudoMetricType :
  numClosedFieldType >-> pseudoMetricType.
(* numFieldType *)
Canonical numField_pointedType.
Canonical numField_filteredType.
Canonical numField_topologicalType.
Canonical numField_uniformType.
Canonical numField_pseudoMetricType.
Canonical pointed_ringType.
Canonical pointed_comRingType.
Canonical pointed_unitRingType.
Canonical pointed_comUnitRingType.
Canonical pointed_idomainType.
Canonical pointed_fieldType.
Canonical pointed_porderType.
Canonical pointed_numDomainType.
Canonical filtered_ringType.
Canonical filtered_comRingType.
Canonical filtered_unitRingType.
Canonical filtered_comUnitRingType.
Canonical filtered_idomainType.
Canonical filtered_fieldType.
Canonical filtered_porderType.
Canonical filtered_numDomainType.
Canonical topological_ringType.
Canonical topological_comRingType.
Canonical topological_unitRingType.
Canonical topological_comUnitRingType.
Canonical topological_idomainType.
Canonical topological_fieldType.
Canonical topological_porderType.
Canonical topological_numDomainType.
Canonical uniform_ringType.
Canonical uniform_comRingType.
Canonical uniform_unitRingType.
Canonical uniform_comUnitRingType.
Canonical uniform_idomainType.
Canonical uniform_fieldType.
Canonical uniform_porderType.
Canonical uniform_numDomainType.
Canonical pseudoMetric_ringType.
Canonical pseudoMetric_comRingType.
Canonical pseudoMetric_unitRingType.
Canonical pseudoMetric_comUnitRingType.
Canonical pseudoMetric_idomainType.
Canonical pseudoMetric_fieldType.
Canonical pseudoMetric_porderType.
Canonical pseudoMetric_numDomainType.
Coercion numField_pointedType : numFieldType >-> pointedType.
Coercion numField_filteredType : numFieldType >-> filteredType.
Coercion numField_topologicalType : numFieldType >-> topologicalType.
Coercion numField_uniformType : numFieldType >-> uniformType.
Coercion numField_pseudoMetricType : numFieldType >-> pseudoMetricType.
End Exports.

End numFieldTopology.
Import numFieldTopology.Exports.

Global Instance Proper_dnbhs_regular_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
Qed.

Lemma Rhausdorff (R : realFieldType) : hausdorff_space R.
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/in_segment_addgt0Pr => _ /posnumP[e].
rewrite in_itv /= -ler_distl; set he := (e%:num / 2)%:pos.
have [z [zx_he yz_he]] := clxy _ _ (nbhsx_ballx x he) (nbhsx_ballx y he).
have := ball_triangle yz_he (ball_sym zx_he).
by rewrite -mulr2n -mulr_natr divfK // => /ltW.
Qed.

Section RestrictedUniformTopology.
Context {U : choiceType} (A : set U) {V : uniformType} .

Definition fct_RestrictedUniform := let _ := A in U -> V.
Definition fct_RestrictedUniformTopology :=
  @weak_uniformType
    ([pointedType of @fct_RestrictedUniform])
    (fct_uniformType [choiceType of { x : U | x \in A }] V)
    (@sigL U V A).

Canonical fct_RestrictUniformFilteredType:=
  [filteredType fct_RestrictedUniform of
      fct_RestrictedUniform for
      fct_RestrictedUniformTopology].

Canonical fct_RestrictUniformTopologicalType :=
  [topologicalType of fct_RestrictedUniform for fct_RestrictedUniformTopology].

Canonical fct_restrictedUniformType :=
  [uniformType of fct_RestrictedUniform for fct_RestrictedUniformTopology].

Lemma uniform_nbhs (f : fct_RestrictedUniformTopology) P:
  nbhs f P <-> (exists E, entourage E /\
    [set h | forall y, A y -> E(f y, h y)] `<=` P).
Proof.
split=> [[Q [[/= W oW <- /=] Wf subP]]|[E [entE subP]]].
  rewrite openE /= /interior in oW.
  case: (oW _ Wf) => ? [ /= E entE] Esub subW.
  exists E; split=> // h Eh; apply/subP/subW/Esub => /= [[u Au]].
  by apply: Eh => /=; rewrite -inE.
near=> g; apply: subP => y /mem_set Ay; rewrite -!(sigLE A).
move: (SigSub _); near: g.
have := (@cvg_image _ _ (sigL A) _ f (nbhs_filter f)
  (image_sigL point)).1 cvg_id [set h | forall y, E (sigL A f y, h y)].
case; first by exists [set fg | forall y, E (fg.1 y, fg.2 y)]; [exists E|].
move=> B nbhsB rBrE; apply: (filterS _ nbhsB) => g Bg [y yA].
by move: rBrE; rewrite eqEsubset; case => [+ _]; apply; exists g.
Unshelve. all: by end_near. Qed.

Lemma uniform_entourage :
  @entourage fct_restrictedUniformType =
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

Notation "{ 'uniform`' A -> V }" := (@fct_RestrictedUniform _ A V) :
  classical_set_scope.
Notation "{ 'uniform' U -> V }" := ({uniform` [set: U] -> V}) :
  classical_set_scope.

Notation "{ 'uniform' A , F --> f }" :=
  (cvg_to [filter of F]
     (filter_of (Phantom (fct_RestrictedUniform A) f)))
   : classical_set_scope.
Notation "{ 'uniform' , F --> f }" :=
  (cvg_to [filter of F]
     (filter_of (Phantom (fct_RestrictedUniform setT) f)))
   : classical_set_scope.

(* We use this function to help coq identify the correct notation to use
   when printing. Otherwise you get goals like `F --> f -> F --> f`      *)

Lemma restricted_cvgE {U : choiceType} {V : uniformType}
    (F : set (set (U -> V))) A (f : U -> V) :
  {uniform A, F --> f} = (F --> (f : {uniform` A -> V})).
Proof. by []. Qed.

Definition fct_Pointwise U (V: topologicalType) := U -> V.

Definition fct_PointwiseTopology (U : Type) (V : topologicalType) :=
  @product_topologicalType U (fun=> V).

Canonical fct_PointwiseFilteredType (U : Type) (V : topologicalType) :=
  [filteredType @fct_Pointwise U V of
     @fct_Pointwise U V for
     @fct_PointwiseTopology U V].

Canonical fct_PointwiseTopologicalType (U : Type) (V : topologicalType) :=
  [topologicalType of
     @fct_Pointwise U V for
     @fct_PointwiseTopology U V].

Notation "{ 'ptws' U -> V }" := (@fct_Pointwise U V).

Notation "{ 'ptws' , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (@fct_Pointwise _ _) f)))
  : classical_set_scope.

Lemma pointwise_cvgE {U : Type} {V : topologicalType}
    (F : set (set(U -> V))) (A : set U) (f : U -> V) :
  {ptws, F --> f} = (F --> (f : {ptws U -> V})).
Proof. by []. Qed.

Section UniformCvgLemmas.
Context {U : choiceType} {V : uniformType}.

Lemma uniform_set1 F (f : U -> V) (x : U) :
  Filter F -> {uniform [set x], F --> f} = ((g x) @[g --> F] --> f x).
Proof.
move=> FF; rewrite propeqE; split.
  move=> + W => /(_ [set t | W (t x)]) +; rewrite /filter_of -nbhs_entourageE.
  rewrite uniform_nbhs => + [Q entQ subW].
  by apply; exists Q; split => // h Qf; exact/subW/Qf.
move=> Ff W; rewrite /filter_of uniform_nbhs => [[E] [entE subW]].
apply: (filterS subW); move/(nbhs_entourage (f x))/Ff: entE => //=; near_simpl.
by apply: filter_app; apply: nearW=> ? ? ? ->.
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

Lemma pointwise_uniform_cvg  (f : U -> V) (F : set (set (U -> V))) :
  Filter F -> {uniform, F --> f} -> {ptws, F --> f}.
Proof.
move=> FF; rewrite cvg_sup => + i; have isubT : [set i] `<=` setT by move=> ?.
move=> /(uniform_subset_cvg _ isubT); rewrite uniform_set1.
rewrite cvg_image; last by rewrite eqEsubset; split=> v // _; exists (cst v).
apply: cvg_trans => W /=; rewrite nbhs_simpl; exists (@^~ i @^-1` W) => //.
by rewrite image_preimage // eqEsubset; split=> // j _; exists (fun _ => j).
Qed.

Lemma cvg_sigL (A : set U) (f : U -> V) (F : set (set (U -> V))) :
    Filter F ->
  {uniform A, F --> f} <->
  {uniform, sigL A @ F --> sigL A f}.
Proof.
move=> FF; split.
- move=> cvgF P' /= /uniform_nbhs [ E [/= entE EsubP]].
  apply: (filterS EsubP); apply: cvgF => /=.
  apply: (filterS ( P:= [set h | forall y, A y -> E(f y, h y)])).
    + by move=> h/= Eh [y ?] _; apply: Eh; rewrite -inE.
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
by rewrite /map_pair eqfg; exact: entourage_refl.
Qed.

Lemma hausdorrf_close_eq_in (A : set U) (f g : {uniform` A -> V}) :
  hausdorff_space V -> close f g = {in A, f =1 g}.
Proof.
move=> hV.
rewrite propeqE; split; last exact: eq_in_close.
rewrite entourage_close => C u; rewrite inE => uA; apply: hV.
rewrite /cluster -nbhs_entourageE /= => X Y [X' eX X'X] [Y' eY Y'Y].
exists (g u); split; [apply: X'X| apply: Y'Y]; last exact: entourage_refl.
apply: (C [set fg | forall y, A y -> X' (fg.1 y, fg.2 y)]) => //=.
by rewrite uniform_entourage; exists X'.
Qed.

Lemma uniform_restrict_cvg
    (F : set (set (U -> V))) (f : U -> V) A : Filter F ->
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

Lemma uniform_nbhsT (f : U -> V) :
  (nbhs (f : {uniform U -> V})) = nbhs (f : fct_topologicalType U V).
Proof.
rewrite eqEsubset; split=> A.
  case/uniform_nbhs => E [entE] /filterS; apply.
  exists [set fh | forall y, E (fh.1 y, fh.2 y)]; first by exists E.
  by move=> ? /=.
case => J [E entE EJ] /filterS; apply; apply/uniform_nbhs; exists E.
by split => // z /= Efz; apply: EJ => t /=; exact: Efz.
Qed.

Lemma cvg_uniformU (f : U -> V) (F : set (set (U -> V))) A B : Filter F ->
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

Lemma cvg_uniform_set0 (F : set (set (U -> V))) (f : U -> V) : Filter F ->
  {uniform set0, F --> f}.
Proof.
move=> FF P /= /uniform_nbhs [E [? R]].
suff -> : P = setT by exact: filterT.
rewrite eqEsubset; split => //=.
by apply: subset_trans R => g _ ?.
Qed.

Definition fct_UniformFamily (fam : (set U) -> Prop) := U -> V.

Definition family_cvg_uniformType (fam: set U -> Prop) :=
  @sup_uniformType  _
    (sigT fam)
    (fun k => Uniform.class (@fct_restrictedUniformType U (projT1 k) V)).

Canonical fct_UniformFamilyFilteredType fam :=
  [filteredType fct_UniformFamily fam of
    fct_UniformFamily fam for
    family_cvg_uniformType fam].

Canonical fct_UniformFamilyTopologicalType fam :=
  [topologicalType of
     fct_UniformFamily fam for
     family_cvg_uniformType fam].

Canonical fct_UniformFamilyUniformType fam :=
  [uniformType of
     fct_UniformFamily fam for
     family_cvg_uniformType fam].

Local Notation "{ 'family' fam , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (fct_UniformFamily fam) f)))
  : classical_set_scope.

Lemma fam_cvgP (fam : set U -> Prop) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> {family fam, F --> f} <->
  (forall A : set U, fam A -> {uniform A, F --> f }).
Proof.
split; first by move=> /cvg_sup + A FA; move/(_ (existT _ _ FA)).
by move=> famFf /=; apply/cvg_sup => [[? ?] FA]; apply: famFf.
Qed.

Lemma family_cvg_subset (famA famB : set U -> Prop) (F : set (set (U -> V)))
    (f : U -> V) : Filter F ->
  famA `<=` famB -> {family famB, F --> f} -> {family famA, F --> f}.
Proof.
by move=> FF S /fam_cvgP famBFf; apply/fam_cvgP => A ?; apply/famBFf/S.
Qed.

Lemma family_cvg_finite_covers (famA famB : set U -> Prop)
  (F : set (set (U -> V))) (f : U -> V) : Filter F ->
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

Notation "{ 'family' fam , U -> V }" :=  (@fct_UniformFamily U V fam).
Notation "{ 'family' fam , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (fct_UniformFamily fam) f)))
  : classical_set_scope.

Lemma fam_cvgE {U : choiceType} {V : uniformType} (F : set (set (U -> V)))
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

Definition compactly_in {U : topologicalType} (A : set U) :=
  [set B | B `<=` A /\ compact B].

Lemma compact_cvg_within_compact {U : topologicalType} {V : uniformType}
    (C : set U) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> compact C ->
  {uniform C, F --> f} <-> {family compactly_in C, F --> f}.
Proof.
move=> FF CC.
apply: (iff_trans _ (iff_sym (fam_cvgP _ _ FF))); split.
- by move=> CFf D [/uniform_subset_cvg + _]; apply.
- by apply; split.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
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
have /rat_in_itvoo[q /itvP qre] : r < r + e%:num by rewrite ltr_addl.
exists (ratr q) => //; split; last by exists q.
apply: reA; rewrite /ball /= distrC ltr_distl qre andbT.
by rewrite (@le_lt_trans _ _ r)// ?qre// ler_subl_addl ler_addr ltW.
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
Context {R : realType} (pS : pointedType) (U : pseudoMetricType R) .
Variable (f : pS -> U).

Let S := weak_uniformType f.

Definition weak_ball (x : S) (r : R) (y : S) := ball (f x) r (f y).

Program Definition weak_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R S entourage weak_ball
  _ _ _ _.

Next Obligation. by move=> ? _/posnumP[e]; exact: ball_center. Qed.
Next Obligation. by move=> ? ? ?; exact: ball_sym. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: ball_triangle. Qed.
Next Obligation.
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
    by exists [set xy | (ball xy.1 1 xy.2)]; exists 1 => /=.
  move=> E1 E2 [e1 e1pos he1E1] [e2 e2pos he2E2].
  wlog ? : E1 E2 e1 e2 e1pos e2pos he1E1 he2E2 / e1 <= e2.
    have [? /(_ _ _ e1 e2)|/ltW ? ] := lerP e1 e2; first exact.
    by rewrite setIC => /(_ _ _ e2 e1); exact.
  exists (E1 `&` E2) => //; exists e1 => // xy /= B; split; first exact: he1E1.
  by apply/he2E2/le_ball; last exact: B.
- by move=> e ?; exists ([set xy | ball xy.1 e xy.2]) => //; by exists e => /=.
Qed.

Definition weak_pseudoMetricType :=
  PseudoMetricType S weak_pseudoMetricType_mixin.

Lemma weak_ballE (e : R) (x : weak_pseudoMetricType) :
  f@^-1` (ball (f x) e) = ball x e.
Proof. by []. Qed.

End weak_pseudoMetric.

Lemma compact_second_countable {R : realType} {T : pseudoMetricType R} :
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

Lemma clopen_surj {R : realType} {T : pseudoMetricType R} :
  compact [set: T] -> $|{surjfun [set: nat] >-> @clopen T}|.
Proof.
move=> cmptT.
suff : @clopen T = set0 \/ $|{surjfun [set: nat] >-> @clopen T}|.
  by case => //; rewrite eqEsubset => -[/(_ _ clopenT)].
exact/pfcard_geP/clopen_countable/compact_second_countable.
Qed.

(* This section proves that uniform spaces, with a countable base for their
   entourage, are metrizable. The definition of this metric is rather arcane,
   and the proof is tough. That's ok because the resulting metric is not
   intended to be used explicitly. Instead, this is typically used in
   applications that do not depend on the metric:
   - `metric spaces are T4`
   - `in metric spaces, compactness and sequential compactness agree`
   - infinite products of metric spaces are metrizable
*)
Section countable_uniform.
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

Local Fixpoint g_ (n : nat) : set (T * T) :=
  if n is S n then let W := split_ent (split_ent (g_ n)) `&` f_ n in W `&` W^-1
  else [set: T*T].

Let entG (n : nat) : entourage (g_ n).
Proof.
elim: n => /=; first exact: entourageT.
by move=> n entg; apply/entourage_invI; exact: filterI.
Qed.

Local Lemma symG (n : nat) : ((g_ n)^-1)%classic = g_ n.
Proof.
by case: n => // n; rewrite eqEsubset; split; case=> ? ?; rewrite /= andC.
Qed.

Local Lemma descendG1 n : g_ n.+1 `<=` g_ n.
Proof.
apply: subIset; left; apply: subIset; left; apply: subset_trans.
  by apply: split_ent_subset; exact: entourage_split_ent.
by apply: subset_trans; last exact: split_ent_subset.
Qed.

Local Lemma descendG (n m: nat) : (m <= n)%N -> g_ n `<=` g_ m.
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

Local Definition distN (e : R) : nat := `|floor e^-1|%N.

Local Lemma distN0 : distN 0 = 0%N.
Proof. by rewrite /distN invr0 floor0. Qed.

Local Lemma distN_nat (n : nat): distN (n%:R^-1) = n.
Proof.
by rewrite /distN invrK floor_natz -[RHS]distn0; congr absz; rewrite subr0 intz.
Qed.

Local Lemma distN_le e1 e2 : e1 > 0 -> e1 <= e2 -> (distN e2 <= distN e1)%N.
Proof.
move=> e1pos e1e2; rewrite /distN; apply: lez_abs2.
  by rewrite floor_ge0 ltW// invr_gt0 (lt_le_trans _ e1e2).
by rewrite le_floor// lef_pinv ?invrK ?invr_gt0//; exact: (lt_le_trans _ e1e2).
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
by case: n => [[]|] // n; case=> [?] [?] [?] [] ? ? ? ? <-; apply: addr_gt0.
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
Proof. by move=> epos; split => //; apply: entourage_refl. Qed.

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
have d1e1d2 : d1 = e1 - d2 by rewrite -d1d2e1 -addrA subrr addr0.
have e2d2le : e1 - d2 <= e2 - d2 by exact: ler_sub.
exists y, (e2 - d2), d2; split => //.
- by apply: P; apply: le_trans e2d2le; rewrite d1e1d2.
- by apply: lt_le_trans e2d2le; rewrite -d1e1d2.
- by rewrite -addrA [-_ + _]addrC subrr addr0.
Qed.

Local Lemma step_ball_le x e1 e2 :
  e1 <= e2 -> step_ball x e1 `<=` step_ball x e2.
Proof. by move=> e1e2 ? [n P]; exists n; exact: (n_step_ball_le e1e2). Qed.

Local Lemma distN_half (n : nat) : n.+1%:R^-1 / (2:R) <= n.+2%:R^-1.
Proof.
rewrite -invrM //; [|exact: unitf_gt0 |exact: unitf_gt0].
rewrite lef_pinv ?posrE // -?natrM ?ler_nat -addn1 -addn1 -addnA mulnDr.
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
      by rewrite -deE ler_addl; apply: ltW.
    - apply: (@n_step_ball_le _ _ d2); last by split.
      rewrite -[e2]addr0 -(subrr e1) addrA -ler_subl_addr opprK addrC.
      by rewrite [e2 + _]addrC -deE; exact: ler_add.
    - by rewrite addn0.
  move=> /negP; rewrite -real_ltNge ?num_real //.
  move=> e1d1; exists y, z, 0%N, 0%N; split.
  - by apply: n_step_ball_le; last (exact: Oxy); exact: ltW.
  - rewrite -deE; apply: (@n_step_ball_le _ _ d2) => //.
    by rewrite ler_addr; apply: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
move=> n IH e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Od1xy d1pos d2pos gd2yz deE.
case: (pselect (e2 <= d2)).
  move=> e2d2; exists y, z, n.+1, 0%N; split.
  - apply: (@n_step_ball_le _ _ d1); rewrite // -[e1]addr0 -(subrr e2) addrA.
    by rewrite -deE -ler_subl_addr opprK ler_add.
  - apply: (@n_step_ball_le _ _ d2); last by split.
    by rewrite -deE ler_addr; exact: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
have d1E' : d1 = e1 + (e2 - d2).
  by move: deE; rewrite addrA [e1 + _]addrC => <-; rewrite -addrA subrr addr0.
move=> /negP; rewrite -?real_ltNge // ?num_real // => d2lee2.
  case: (IH e1 (e2 - d2) x y); rewrite ?subr_gt0 // -d1E' //.
  move=> t1 [t2] [c1] [c2] [] Oxy1 gt1t2 t2y <-.
  exists t1, t2, c1, c2.+1; split => //.
  - by apply: (@n_step_ball_le _ _ d1); rewrite -?deE // ?ler_addl; exact: ltW.
  - exists y, (e2 - d2), d2; split; rewrite // ?subr_gt0//.
    by rewrite -addrA [-_ + _]addrC subrr addr0.
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

(* Note these are the only non-local result from this section *)
Definition countable_uniform_pseudoMetricType_mixin := PseudoMetric.Mixin
  step_ball_center step_ball_sym step_ball_triangle step_ball_entourage.

Lemma countable_uniform_bounded (x y : T) :
  let U := PseudoMetricType _ countable_uniform_pseudoMetricType_mixin
  in @ball _ U x 2 y.
Proof.
rewrite /ball; exists O%N; rewrite /n_step_ball; split; rewrite // /distN. 
suff -> : @floor R 2^-1 = 0 by rewrite absz0 /=.
apply/eqP; rewrite -[_ == _]negbK; rewrite floor_neq0 negb_or -?ltNge -?leNgt.
by apply/andP; split => //; rewrite invf_lt1 //= ltr_addl.
Qed.

End countable_uniform.

Section sup_pseudometric.
Variable (R : realType) (T : pointedType) (Ii : Type).
Variable (Tc : Ii -> PseudoMetric.class_of R T).

Hypothesis Icnt : countable [set: Ii].

Let I : choiceType := classicType_choiceType Ii.
Let TS := fun i => PseudoMetric.Pack (Tc i).

Definition countable_uniformityT := @countable_sup_ent T Ii Tc Icnt
  (fun i => @countable_uniformity_metric _ (TS i)).

Definition sup_pseudoMetric_mixin := @countable_uniform_pseudoMetricType_mixin R
  (sup_uniformType Tc) countable_uniformityT.

Definition sup_pseudoMetricType :=
  PseudoMetricType (sup_uniformType Tc) sup_pseudoMetric_mixin.

End sup_pseudometric.

Section product_pseudometric.
Variable (R : realType) (Ii : countType) (Tc : Ii -> pseudoMetricType R).

Hypothesis Icnt : countable [set: Ii].

Definition product_pseudoMetricType :=
  sup_pseudoMetricType (fun i => PseudoMetric.class
    (weak_pseudoMetricType (fun f : dep_arrow_pointedType Tc => f i)))
    Icnt.

End product_pseudometric.

Definition subspace {T : Type} (A : set T) := T.
Arguments subspace {T} _ : simpl never.

Definition incl_subspace {T A} (x : subspace A) : T := x.

Section Subspace.
Context {T : topologicalType} (A : set T).

Definition nbhs_subspace (x : subspace A) : set (set (subspace A)) :=
  if x \in A then within A (nbhs x) else globally [set x].

Variant nbhs_subspace_spec x : Prop -> Prop -> bool -> set (set T) -> Type :=
  | WithinSubspace :
      A x -> nbhs_subspace_spec x True False true (within A (nbhs x))
  | WithoutSubspace :
    ~ A x -> nbhs_subspace_spec x False True false (globally [set x]).

Lemma nbhs_subspaceP x :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs_subspace x).
Proof.
rewrite /nbhs_subspace; case:(boolP (x \in A)); rewrite ?(inE, notin_set) => xA.
  by rewrite (@propext (A x) True)// not_True; constructor.
by rewrite (@propext (A x) False)// not_False; constructor.
Qed.

Lemma nbhs_subspace_in (x : T) : A x -> within A (nbhs x) = nbhs_subspace x.
Proof. by case: nbhs_subspaceP. Qed.

Lemma nbhs_subspace_out (x : T) : ~ A x -> globally [set x] = nbhs_subspace x.
Proof. by case: nbhs_subspaceP. Qed.

Lemma nbhs_subspace_filter (x : subspace A) : ProperFilter (nbhs_subspace x).
Proof.
case: nbhs_subspaceP => ?; last exact: globally_properfilter.
by apply: within_nbhs_proper; apply: subset_closure.
Qed.

Definition subspace_pointedType := PointedType (subspace A) point.

Canonical subspace_filteredType :=
  FilteredType (subspace A) (subspace A) nbhs_subspace.

Program Definition subspace_topologicalMixin :
  Topological.mixin_of (nbhs_subspace) := @topologyOfFilterMixin
    (subspace A) nbhs_subspace nbhs_subspace_filter _ _.
Next Obligation.
by move=> p A0; case: nbhs_subspaceP => ? => [/nbhs_singleton|]; apply.
Qed.
Next Obligation.
move=> p A0; case: nbhs_subspaceP => [|] Ap.
  by move=> /nbhs_interior; apply: filterS => y A0y Ay; case: nbhs_subspaceP.
by move=> E x ->; case: nbhs_subspaceP.
Qed.

Canonical subspace_topologicalType :=
  TopologicalType (subspace A) subspace_topologicalMixin.

Lemma subspace_cvgP (F : set (set T)) (x : T) :
  Filter F -> A x ->
  (F --> (x : subspace A)) <-> (F --> within A (nbhs x)).
Proof. by case: (y in F --> y) / nbhs_subspaceP. Qed.

Lemma subspace_continuousP {S : topologicalType} (f : T -> S) :
  continuous (f : subspace A -> S) <->
  (forall x, A x -> f @ within A (nbhs x) --> f x) .
Proof.
split => [ctsf x Ax W /=|wA x].
  by rewrite nbhs_simpl //= nbhs_subspace_in //=; apply: ctsf.
case: (y in _ @[_ --> y]) / (nbhs_subspaceP x) => Ax.
  exact: (cvg_trans _ (wA _ Ax)).
by move=> ? /nbhs_singleton //= ?; rewrite nbhs_simpl => ? ->.
Qed.

Lemma subspace_eq_continuous {S : topologicalType} (f g : subspace A -> S) :
  {in A, f =1 g} -> continuous f -> continuous g.
Proof.
rewrite ?subspace_continuousP=> feq L x Ax; rewrite -(feq x) ?inE //.
by apply: cvg_trans _ (L x Ax); apply: fmap_within_eq=> ? ?; rewrite feq.
Qed.

Lemma continuous_subspace_in {U : topologicalType} (f : subspace A -> U) :
  continuous f = {in A, continuous f}.
Proof.
rewrite propeqE in_setP subspace_continuousP/filter_of/nbhs //=; split.
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
split=> [|[V [oV UV]]]; first last.
  rewrite -open_subspaceIT -UV => x //= []; case: nbhs_subspaceP => //=.
  rewrite withinE /= => Ax Vx _; exists V; last by rewrite -setIA setIid.
  by move: oV; rewrite openE; exact.
rewrite -open_subspaceIT => oUA.
have oxF x : (U `&` A) x -> exists2 V, open_nbhs x V & V `&` A `<=` U `&` A.
  move=> /[dup] UAx [Ux Ax]; move: (oUA _ UAx); case: nbhs_subspaceP => // _.
  rewrite withinE /= => -[V nbhsV]; rewrite -setIA setIid => UV.
  exists V^°; rewrite ?open_nbhsE.
  - by split; [exact: open_interior|exact: nbhs_interior].
  - by rewrite UV => t [/interior_subset].
pose f x :=
  if pselect ((U `&` A) x) is left e then projT1 (cid2 (oxF x e)) else set0.
exists (\bigcup_(x in U `&` A) f x); split.
  apply: bigcup_open => i UAi; rewrite /f; case: pselect => // ?.
  by case: (cid2 _) => //= W; rewrite open_nbhsE => -[].
rewrite eqEsubset /f; split.
  move=> t [[u UAu]] /=; case: pselect => //= ?.
  by case: (cid2 _) => /= W _ + ? ?; exact.
move=> t UAt; split; last by case: UAt.
by exists t => //; case: pselect => //= -[Ut At]; case: (cid2 _) => //= W [].
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
move=> [V] [clV VAclUA] /[dup] /(@closure_subset subspace_topologicalType).
have/closure_id <- := (closed_subspaceT) => /setIidr <-; rewrite setIC.
move=> UsubA; rewrite eqEsubset; split.
  apply: setSI; rewrite closureE; apply: smallest_sub (@subset_closure _ U).
  by apply: closed_subspaceW; exact: closed_closure.
rewrite -VAclUA; apply: setSI; rewrite closureE //=; apply: smallest_sub => //.
apply: subset_trans (@subIsetl _ V A); rewrite VAclUA subsetI; split => //.
exact: (@subset_closure _ (U : set (subspace A))).
Qed.

Lemma subspace_hausdorff :
  hausdorff_space T -> hausdorff_space [topologicalType of subspace A].
Proof.
rewrite ?open_hausdorff => + x y xNy => /(_ x y xNy).
move=> [[P Q]] /= [Px Qx] /= [/open_subspaceW oP /open_subspaceW oQ].
by move=> ?; exists (P, Q).
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
  (forall U, @clopen (subspace_topologicalType) U ->
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

Global Instance subspace_filter {T : topologicalType}
     (A : set T) (x : subspace A) :
   Filter (nbhs_subspace x) := nbhs_subspace_filter x.

Global Instance subspace_proper_filter {T : topologicalType}
     (A : set T) (x : subspace A) :
   ProperFilter (nbhs_subspace x) := nbhs_subspace_filter x.

(*Notation "{ 'within' A , 'continuous' f }" :=
  (continuous (f : subspace A -> _)).*)
Notation "{ 'within' A , 'continuous' f }" := (forall x,
  cvg_to [filter of fmap f (filter_of (Phantom (subspace A) x))]
         [filter of f x]) : classical_set_scope.

Section SubspaceRelative.
Context {T : topologicalType}.
Implicit Types (U : topologicalType) (A B : set T).

Lemma nbhs_subspace_subset A B (x : T) :
  A `<=` B -> nbhs (x : subspace B) `<=` nbhs (x : subspace A).
Proof.
rewrite /nbhs //= => AB; case: (nbhs_subspaceP A); case: (nbhs_subspaceP B).
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
rewrite {1}/nbhs //=; have [_|] := nbhs_subspaceP [set: T]; last by cbn.
rewrite eqEsubset withinE; split => [W [V nbhsV]|W ?]; last by exists W.
by rewrite 2!setIT => ->.
Qed.

Lemma continuous_subspaceT_for {U} A (f : T -> U) (x : T) :
  A x -> {for x, continuous f} -> {for x, continuous (f : subspace A -> U)}.
Proof.
rewrite /filter_of/nbhs/=/prop_for => inA ctsf.
have [_|//] := nbhs_subspaceP A x.
apply: (cvg_trans _ ctsf); apply: cvg_fmap2; apply: cvg_within.
by rewrite /subspace; exact: nbhs_filter.
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
  rewrite /filter_of -(nbhs_subspace_interior Aox).
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
move=> x Q; rewrite nbhs_simpl /= {2}/nbhs /=.
by case: (nbhs_subspaceP (@set0 T) x) => // _ /nbhs_singleton /= ? ? ->.
Qed.

Lemma continuous_subspace1 {U} (a : T) (f : T -> U) :
  {within [set a], continuous f}.
Proof.
move=> x Q; rewrite nbhs_simpl /= {2}/nbhs /=.
case: (nbhs_subspaceP [set a] x); last by move=> _ /nbhs_singleton /= ? ? ->.
by move=> -> /nbhs_singleton ?; apply: nearW => ? ->.
Qed.

End SubspaceRelative.

Section SubspaceUniform.
Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.
Context {X : uniformType} (A : set X).

Definition subspace_ent :=
  filter_from (@entourage X)
  (fun E => [set xy | (xy.1 = xy.2) \/ (A xy.1 /\ A xy.2 /\ E xy)]).

Program Definition subspace_uniformMixin :=
  @Uniform.Mixin (subspace A) (@nbhs_subspace _ _) subspace_ent _ _ _ _ _.
Next Obligation.
apply: filter_from_filter; first by (exists setT; exact: filterT).
move=> P Q entP entQ; exists (P `&` Q); first exact: filterI.
move=> [x y] /=; case; first (by move=> ->; split=> /=; left).
by move=> [Ax [Ay [Pxy Qxy]]]; split=> /=; right.
Qed.
Next Obligation. by move=> ? + [x y]/= ->; case=> V entV; apply; left. Qed.
Next Obligation.
move=> ?; case=> V ? Vsub; exists (V^-1)%classic; first exact: entourage_inv.
move=> [x y] /= G; apply: Vsub; case: G; first by (move=> <-; left).
by move=> [? [? Vxy]]; right; repeat split => //.
Qed.
Next Obligation.
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
Next Obligation.
pose  EA := [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2].
have entEA : subspace_ent EA.
  exists setT; first exact: filterT.
  by move=> [??] /= [ ->|[?] [?]];[left|right].
rewrite funeq2E=> x U.
case: (@nbhs_subspaceP X A x); rewrite propeqE; split => //=.
- rewrite withinE; case=> V /[dup] nbhsV => [/nbhsP [E entE Esub] UV].
  exists [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ E xy].
    by exists E => //= [[??]] /= [->| [?[]]//]; exact: entourage_refl.
  move=> y /= [<-|].
    suff : (U `&` A) x by case.
    by rewrite UV; split => //; apply: (@nbhs_singleton X).
  case=> _ [Ay Ey]; suff : (U `&` A) y by case.
  by rewrite UV; split => //; apply: Esub.
- move=> [] W [E eentE subW] subU //=.
  near=> w; apply: subU; apply: subW; right; repeat split => //=.
    by exact: (near (withinT _ (@nbhs_filter X _))).
  by near: w; apply/nbhsP; exists E => // y /= Ey.
- move=> //= Ux; exists EA => //.
  by move=> y /= [|[]] //= <-; apply: Ux.
- rewrite //= => [[W [W' entW' subW] subU]] ? ->.
  by apply: subU; apply: subW; left.
Unshelve. all: by end_near. Qed.

Canonical subspace_uniformType :=
  UniformType (subspace A) subspace_uniformMixin.
End SubspaceUniform.

Section SubspacePseudoMetric.
Context {R : numDomainType} {X : pseudoMetricType R} (A : set X).

Definition subspace_ball (x : subspace A) (r : R) :=
  if x \in A then A `&` ball (x : X) r else [set x].

Program Definition subspace_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R (subspace A) (subspace_ent A) (subspace_ball)
  _ _ _ _.
Next Obligation.
move=> x e; rewrite /subspace_ball; case: ifP => //= /asboolP ? ?.
by split=> //; exact: ballxx.
Qed.
Next Obligation.
move=> x y e; rewrite /subspace_ball; case: ifP => //= /asboolP ?.
  by move=> [] Ay /ball_sym yBx; case: ifP => /asboolP.
by move=> ->; case: ifP => /asboolP.
Qed.
Next Obligation.
move=> x y z e1 e2; rewrite /subspace_ball; (repeat case: ifP => /asboolP).
- by move=>?? [??] [??]; split => //=; apply: ball_triangle; eauto.
- by move=> ?? [??] ->.
- by move=> + /[swap] => /[swap] => ->.
- by move=> _ _ -> ->.
Qed.
Next Obligation.
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

Canonical subspace_pseudoMetricType :=
  PseudoMetricType (subspace A) subspace_pseudoMetricType_mixin.

End SubspacePseudoMetric.

Section SubspaceWeak.
Context {T : topologicalType} {U : pointedType}.
Variables (f : U -> T).

Let U' := weak_topologicalType f.

Lemma weak_subspace_open (A : set U') :
  open A -> open (f @` A : set (subspace (range f))).
Proof.
case=> B oB <-; apply/open_subspaceP; exists B; split => //; rewrite eqEsubset.
split => z [] /[swap]; first by case=> w _ <- ?; split; exists w.
by case=> w _ <- [v] ? <-.
Qed.

End SubspaceWeak.

Definition separate_points_from_closed {I : Type} {T : topologicalType}
    {U_ : I -> topologicalType} (f_ : forall i, T -> U_ i) :=
  forall (U : set T) x,
  closed U -> ~ U x -> exists i, ~ (closure (f_ i @` U)) (f_ i x).

(* A handy technique for embedding a space T into a product. The key interface
   is 'separate_points_from_closed', which guarantees that the topologies
   - T's native topology
   - sup (weak f_i) - the sup of all the weak topologies of f_i
   - weak (x => (f_1 x, f_2 x,...)) - the weak topology from the product space
  are equivalent (the last equivalence seems to require accessible_space).
*)
Section product_embeddings.
Context {I : choiceType} {T : topologicalType} {U_ : I -> topologicalType}.
Variable (f_ : forall i, T -> U_ i).

Hypothesis sepf : separate_points_from_closed f_.
Hypothesis ctsf : forall i, continuous (f_ i).

Let weakT := @sup_topologicalType T I
  (fun i => Topological.class (weak_topologicalType (f_ i))).

Let PU := product_topologicalType U_.

Local Notation sup_open := (@open weakT).
Local Notation "'weak_open' i" :=
  (@open (weak_topologicalType (f_ i))) (at level 0).
Local Notation natural_open := (@open T).

Lemma weak_sep_cvg (F : set (set T)) (x : T) :
  Filter F -> (F --> (x : T)) <-> (F --> (x : weakT)).
Proof.
move=> FF; split.
  move=> FTx; apply/cvg_sup => i U.
  have /= -> := @nbhsE (weak_topologicalType (f_ i)) x.
  case=> B [[C oC <- ?]] /filterS; apply; apply: FTx; rewrite /= nbhsE.
  by exists (f_ i @^-1` C) => //; split => //; exact: open_comp.
move/cvg_sup => wiFx U; rewrite /= nbhs_simpl nbhsE => [[B [oB ?]]].
move/filterS; apply; have [//|i nclfix] := @sepf _ x (open_closedC oB).
apply: (wiFx i); have /= -> := @nbhsE (weak_topologicalType (f_ i)) x.
exists (f_ i @^-1` (~` closure [set f_ i x | x in ~` B])); [split=>//|].
  apply: open_comp; last by rewrite ?openC; last apply: closed_closure.
  by move=> + _; exact: weak_continuous.
rewrite closureC preimage_bigcup => z [V [oV]] VnB => /VnB.
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
move=> i; move: x; apply/(@continuousP _ (weak_topologicalType _)) => A [B ? E].
rewrite -E (_ : @^~ i =  proj i) //.
have -> : join_product @^-1` (proj i @^-1` B) = f_ i @^-1` B by [].
apply: open_comp => // + _; rewrite /cvg_to => x U.
by rewrite nbhs_simpl /= -weak_sep_nbhsE; move: x U; exact: ctsf.
Qed.

Local Notation prod_open :=
  (@open (subspace_topologicalType (range join_product))).

Lemma join_product_open (A : set T) : open A ->
  open ((join_product @` A) : set (subspace (range join_product))).
Proof.
move=> oA; rewrite openE => y /= [x Ax] jxy.
have [// | i nAfiy] := @sepf (~` A) x (open_closedC oA).
pose B : set PU := proj i @^-1` (~` closure (f_ i @` ~` A)).
apply: (@filterS _ _ _ (range join_product `&` B)).
  move=> z [[w ?]] wzE Bz; exists w => //.
  move: Bz; rewrite /B -wzE closureC; case=> K [oK KsubA] /KsubA.
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
have [] := (@sepf [set y] x (cl1 y)); first by exact/eqP.
move=> i P; suff : join_product x i != join_product y i by rewrite jxjy => /eqP.
apply/negP; move: P; apply: contra_not => /eqP; rewrite /join_product => ->.
by apply: subset_closure; exists y.
Qed.

Lemma join_product_weak : set_inj [set: T] join_product ->
  @open T = @open (weak_topologicalType join_product).
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

Lemma uniform_limit_continuous {U : topologicalType} {V : uniformType}
    (F : set (set (U -> V))) (f : U -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : U -> V)) ->
  {uniform, F --> f} -> continuous f.
Proof.
move=> PF ctsF Ff x; apply/cvg_app_entourageP => A entA; near F => g; near=> y.
apply: (entourage_split (g x)) => //.
  by near: g; apply/Ff/uniform_nbhs; exists (split_ent A); split => // ?; exact.
apply: (entourage_split (g y)) => //; near: y; near: g.
  by apply: (filterS _ ctsF) => g /(_ x) /cvg_app_entourageP; exact.
apply/Ff/uniform_nbhs; exists (split_ent (split_ent A))^-1%classic.
by split; [exact: entourage_inv | move=> g fg; near_simpl; near=> z; exact: fg].
Unshelve. all: end_near. Qed.

Lemma uniform_limit_continuous_subspace {U : topologicalType} {V : uniformType}
    (K : set U) (F : set (set (U -> V))) (f : subspace K -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : subspace K -> V)) ->
  {uniform K, F --> f} -> {within K, continuous f}.
Proof.
move=> PF ctsF Ff; apply: (@subspace_eq_continuous _ _ _ (restrict K f)).
  by rewrite /restrict => ? ->.
apply: (@uniform_limit_continuous
  (subspace_topologicalType K) _ (restrict K @ F) _).
  apply: (filterS _ ctsF) => g; apply: subspace_eq_continuous.
  by rewrite /restrict => ? ->.
by apply (@uniform_restrict_cvg _ _ F ) => //; exact: PF.
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

Lemma totally_disconnected_prod (I : choiceType)
  (T : I -> topologicalType) (A : forall i, set (T i)) :
  (forall i, totally_disconnected (A i)) ->
  @totally_disconnected (product_topologicalType T)
    (fun f => forall i, A i (f i)).
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

Section UniformPointwise.
Context {U : topologicalType} {V : uniformType}.

Definition singletons {T : Type} := [set [set x] | x in [set: T]].

Lemma pointwise_cvg_family_singleton F (f: U -> V):
  Filter F -> {ptws, F --> f} = {family @singletons U, F --> f}.
Proof.
move=> FF; rewrite propeqE fam_cvgP cvg_sup; split.
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

Section gauges.

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

Lemma gauge_refl A : gauge A -> [set fg | fg.1 = fg.2] `<=` A.
Proof.
case=> n _; apply: subset_trans => -[_ a]/= ->.
by apply: entourage_refl; exact: iter_split_ent.
Qed.

Lemma gauge_inv A : gauge A -> gauge (A^-1)%classic.
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

Definition gauge_uniformType_mixin :=
 UniformMixin gauge_filter gauge_refl gauge_inv gauge_split erefl.

Definition gauge_topologicalTypeMixin :=
  topologyOfEntourageMixin gauge_uniformType_mixin.

Definition gauge_filtered := FilteredType T T (nbhs_ gauge).
Definition gauge_topologicalType :=
  TopologicalType gauge_filtered gauge_topologicalTypeMixin.
Definition gauge_uniformType := UniformType
  gauge_topologicalType gauge_uniformType_mixin.

Lemma gauge_countable_uniformity : countable_uniformity gauge_uniformType.
Proof.
exists [set iter n split_sym (E `&` E^-1) | n in [set: nat]].
split; [exact: card_image_le | by move=> W [n] _ <-; exists n|].
by move=> D [n _ ?]; exists (iter n split_sym (E `&` E^-1)).
Qed.

Definition gauge_pseudoMetric_mixin {R : realType} :=
  @countable_uniform_pseudoMetricType_mixin R _ gauge_countable_uniformity.

Definition gauge_pseudoMetricType {R : realType} :=
  PseudoMetricType gauge_uniformType (@gauge_pseudoMetric_mixin R).

End entourage_gauge.

Lemma uniform_pseudometric_sup {R : realType} {T : uniformType} :
    @entourage T = @sup_ent T {E : set (T * T) | @entourage T E}
  (fun E => Uniform.class (@gauge_pseudoMetricType T (projT1 E) (projT2 E) R)).
Proof.
rewrite eqEsubset; split => [E entE|E].
  exists E => //=.
  pose pe : {classic {E0 : set (T * T) | _}} * _ := (exist _ E entE, E).
  have entPE : `[< @entourage (gauge_uniformType entE) E >].
    by apply/asboolP; exists 0%N => // ? [].
  exists (fset1 (exist _ pe entPE)) => //=; first by move=> ?; rewrite in_setE.
  by rewrite set_fset1 bigcap_set1.
case=> W /= [/= J] _ <- /filterS; apply; apply: filter_bigI => -[] [] [] /= D.
move=> entD G /[dup] /asboolP [n _ + _ _] => /filterS; apply.
exact: iter_split_ent.
Qed.

End gauges.

Definition normal_space (T : topologicalType) :=
  forall A : set T, closed A ->
    set_nbhs A `<=` filter_from (set_nbhs A) closure.

Definition regular_space (T : topologicalType) :=
  forall a : T, nbhs a `<=` filter_from (nbhs a) closure.

Section ArzelaAscoli.
Context {X : topologicalType}.
Context {Y : uniformType}.
Context {hsdf : hausdorff_space Y}.
Implicit Types (I : Type).

(* The key condition in Arzela-Ascoli that, like uniform continuity,
   moves a quantifier around so all functions have the same 'deltas'. *)

Definition equicontinuous {I} (W : set I) (d : I -> (X -> Y)) :=
  forall x (E : set (Y * Y)), entourage E ->
    \forall y \near x, forall i, W i -> E(d i x, d i y).

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

(* A convenient notion that is in between compactness in
   {family compact, X -> y} and compactness in {ptws X -> y}.*)
Definition pointwise_precompact {I} (W : set I) (d : I -> X -> Y) :=
  forall x, precompact [set (d i x) | i in W].

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
  compact (W : set (@fct_UniformFamily X Y compact)) ->
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
rewrite pointwise_cvg_family_singleton => /fam_cvgP /(_ [set x]).
rewrite uniform_set1 => /(_ _ (to_set E (f x))); apply; first by exists x.
by move: E entE; exact/cvg_entourageP.
Qed.

Lemma equicontinuous_closure (W : set {ptws X -> Y}) :
  equicontinuous W id -> equicontinuous (closure W) id.
Proof.
move=> ectsW => x E entE; near=> y => f clWf.
near (within W (nbhs (f : {ptws X -> Y}))) => g.
near: g; rewrite near_withinE; near_simpl; near=> g => Wg.
apply: (@entourage_split _ (g x)) => //.
  exact: (near (pointwise_cvg_entourage _ _ _)).
apply: (@entourage_split _ (g y)) => //; first exact: (near (@ectsW x _ _)).
by apply/entourage_sym; exact: (near (pointwise_cvg_entourage _ _ _)).
Unshelve. all: by end_near. Qed.

Definition small_ent_sub := @small_set_sub _ _ (@entourage Y).

Lemma pointwise_compact_cvg (F : set (set {ptws X -> Y})) (f : {ptws X -> Y}) :
  ProperFilter F ->
  (\forall W \near powerset_filter_from F, equicontinuous W id) ->
  {ptws, F --> f} <-> {family compact, F --> f}.
Proof.
move=> PF /near_powerset_filter_fromP; case.
  exact: equicontinuous_subset_id.
move=> W; wlog Wf : f W / W f.
  move=> + FW /equicontinuous_closure => /(_ f (closure W)) Q.
  split => Ff; last by apply: pointwise_cvg_compact_family.
  apply Q => //; last by (apply: (filterS _ FW); exact: subset_closure).
  by rewrite closureEcvg; exists F; [|split] => // ? /filterS; apply.
move=> FW ectsW; split=> [ptwsF|]; last exact: pointwise_cvg_compact_family.
apply/fam_cvgP => K ? U /=; rewrite uniform_nbhs => [[E [eE EsubU]]].
suff : \forall g \near within W (nbhs f), forall y, K y -> E (f y, g y).
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
  near: g; near_simpl; apply: (@cvg_within _ (nbhs f)).
  exact: pointwise_cvg_entourage.
apply: (near (small_ent_sub _) E') => //.
apply: (near (ectsW x E' entE')) => //.
exact: (near (withinT _ (nbhs_filter f))).
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
move=> /= + F UF FcW => /(_ F UF); rewrite image_id; case => // p [cWp Fp].
exists p; split => //; apply/(pointwise_compact_cvg) => //.
apply/near_powerset_filter_fromP; first exact: equicontinuous_subset_id.
exists (closure (W : set {ptws X -> Y })) => //; exact: equicontinuous_closure.
Qed.

Section precompact_equicontinuous.
Hypothesis lcptX : locally_compact [set: X].

Let compact_equicontinuous (W : set {family compact, X -> Y}) :
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
  by near: y; apply: ((@ctsW f Wf x) (to_set _ _)); exact: nbhs_entourage.
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
suff ctsf : continuous f by move: E entE; apply/cvg_app_entourageP; exact: ctsf.
apply/continuous_localP => x'; apply/near_powerset_filter_fromP.
  by move=> ? ?; exact: continuous_subspaceW.
case: (@lcptX x') => // U; rewrite withinET => nbhsU [cptU _].
exists U => //; apply: (uniform_limit_continuous_subspace PG _ _).
  by near=> g; apply: continuous_subspaceT; near: g; exact: GW.
by move/fam_cvgP/(_ _ cptU) : Gf.
Unshelve. end_near. Qed.

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
