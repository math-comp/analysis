(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions wochoice.
From mathcomp Require Import cardinality mathcomp_extra fsbigop set_interval.

(**md**************************************************************************)
(* # Filters                                                                  *)
(*                                                                            *)
(* The theory of (powerset) filters and tools for manipulating them.          *)
(* This file introduces convergence for filters. It also provides the         *)
(* interface of filtered types for associating a "canonical filter" to each   *)
(* element. And lastly it provides typeclass instances for verifying when     *)
(* a (set_system T) is really a filter in T, as a Filter or Properfilter.     *)
(*                                                                            *)
(* ## Structure of filter                                                     *)
(* ```                                                                        *)
(*                   filteredType U == interface type for types whose         *)
(*                                     elements represent sets of sets on U   *)
(*                                     These sets are intended to be filters  *)
(*                                     on U but this is not enforced yet.     *)
(*                                     The HB class is called Filtered.       *)
(*                                     It extends Pointed.                    *)
(*                           nbhs p == set of sets associated to p (in a      *)
(*                                     filtered type)                         *)
(*                  pfilteredType U == a pointed and filtered type            *)
(*                          hasNbhs == factory for filteredType               *)
(*                     continuous f == f is continuous w.r.t the topology     *)
(*                 filterI_iter F n == nth stage of recursively building the  *)
(*                                     filter of finite intersections of F    *)
(*                    finI_from D f == set of \bigcap_(i in E) f i where E is *)
(*                                     a finite subset of D                   *)
(* ```                                                                        *)
(*                                                                            *)
(* We endow several standard types with the structure of filter, e.g.:        *)
(* - products `(X1 * X2)%type`                                                *)
(* - matrices `'M[X]_(m, n)`                                                  *)
(* - natural numbers `nat`                                                    *)
(*                                                                            *)
(* ## Theory of filters                                                       *)
(* ```                                                                        *)
(*                  filter_from D B == set of the supersets of the elements   *)
(*                                     of the family of sets B whose indices  *)
(*                                     are in the domain D                    *)
(*                                     This is a filter if (B_i)_(i in D)     *)
(*                                     forms a filter base.                   *)
(*                  filter_prod F G == product of the filters F and G         *)
(*                        F `=>` G <-> G is included in F                     *)
(*                                     F and G are sets of sets.              *)
(*                              \oo == "eventually" filter on nat: set of     *)
(*                                     predicates on natural numbers that are *)
(*                                     eventually true                        *)
(*                         F --> G <-> the canonical filter associated to G   *)
(*                                     is included in the canonical filter    *)
(*                                     associated to F                        *)
(*                            lim F == limit of the canonical filter          *)
(*                                     associated with F if there is such a   *)
(*                                     limit, i.e., an element l such that    *)
(*                                     the canonical filter associated to l   *)
(*                                     is a subset of F                       *)
(*                     [lim F in T] == limit of the canonical filter          *)
(*                                     associated to F in T where T has type  *)
(*                                     filteredType U                         *)
(*                    [cvg F in T] <-> the canonical filter associated to F   *)
(*                                     converges in T                         *)
(*                           cvg F <-> same as [cvg F in T] where T is        *)
(*                                     inferred from the type of the          *)
(*                                     canonical filter associated to F       *)
(*                         Filter F == type class proving that the set of     *)
(*                                     sets F is a filter                     *)
(*                   ProperFilter F == type class proving that the set of     *)
(*                                     sets F is a proper filter              *)
(*                    UltraFilter F == type class proving that the set of     *)
(*                                     sets F is an ultrafilter               *)
(*                      filter_on T == interface type for sets of sets on T   *)
(*                                     that are filters                       *)
(*                  FilterType F FF == packs the set of sets F with the proof *)
(*                                     FF of Filter F to build a filter_on T  *)
(*                                     structure                              *)
(*                     pfilter_on T == interface type for sets of sets on T   *)
(*                                     that are proper filters                *)
(*                 PFilterPack F FF == packs the set of sets F with the proof *)
(*                                     FF of ProperFilter F to build a        *)
(*                                     pfilter_on T structure                 *)
(*                         fmap f F == image of the filter F by the function  *)
(*                                     f                                      *)
(*                     E @[x --> F] == image of the canonical filter          *)
(*                                     associated to F by the function        *)
(*                                     (fun x => E)                           *)
(*                            f @ F == image of the canonical filter          *)
(*                                     associated to F by the function f      *)
(*                        fmapi f F == image of the filter F by the relation  *)
(*                                     f                                      *)
(*                    E `@[x --> F] == image of the canonical filter          *)
(*                                     associated to F by the relation        *)
(*                                     (fun x => E)                           *)
(*                           f `@ F == image of the canonical filter          *)
(*                                     associated to F by the relation f      *)
(*                       globally A == filter of the sets containing A        *)
(*                @frechet_filter T := [set S : set T | finite_set (~` S)]    *)
(*                                     a.k.a. cofinite filter                 *)
(*                       at_point a == filter of the sets containing a        *)
(*                       within D F == restriction of the filter F to the     *)
(*                                     domain D                               *)
(*               principal_filter x == filter containing every superset of x  *)
(*            principal_filter_type == alias for choice types with principal  *)
(*                                     filters                                *)
(*                subset_filter F D == similar to within D F, but with        *)
(*                                     dependent types                        *)
(*           powerset_filter_from F == the filter of downward closed subsets  *)
(*                                     of F.                                  *)
(*                                     Enables use of near notation to pick   *)
(*                                     suitably small members of F            *)
(*                      in_filter F == interface type for the sets that       *)
(*                                     belong to the set of sets F            *)
(*                      InFilter FP == packs a set P with a proof of F P to   *)
(*                                     build a in_filter F structure          *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Near notations and tactics                                              *)
(* The purpose of the near notations and tactics is to make the manipulation  *)
(* of filters easier. Instead of proving $F\; G$, one can prove $G\; x$ for   *)
(* $x$ "near F", i.e., for x such that H x for H arbitrarily precise as long  *)
(* as $F\; H$. The near tactics allow for a delayed introduction of $H$:      *)
(* $H$ is introduced as an existential variable and progressively             *)
(* instantiated during the proof process.                                     *)
(*                                                                            *)
(* ### Notations                                                              *)
(* ```                                                                        *)
(*                      {near F, P} == the property P holds near the          *)
(*                                     canonical filter associated to F       *)
(*                                     P must have the form forall x, Q x.    *)
(*                                     Equivalent to F Q.                     *)
(*          \forall x \near F, P x <-> F (fun x => P x).                      *)
(*                     \near x, P x := \forall y \near x, P y.                *)
(*                  {near F & G, P} == same as {near H, P}, where H is the    *)
(*                                     product of the filters F and G         *)
(*   \forall x \near F & y \near G, P x y := {near F & G, forall x y, P x y}  *)
(*     \forall x & y \near F, P x y == same as before, with G = F             *)
(*               \near x & y, P x y := \forall z \near x & t \near y, P x y   *)
(*                     x \is_near F == x belongs to a set P : in_filter F     *)
(* ```                                                                        *)
(*                                                                            *)
(* ### Tactics                                                                *)
(* - `near=> x` introduces x.                                                 *)
(*   On the goal `\forall x \near F, G x`, introduces the variable `x` and an *)
(*   "existential", and an unaccessible hypothesis `?H x` and asks the user   *)
(*   to prove `(G x)` in this context.                                        *)
(*   Under the hood, it delays the proof of `F ?H` and waits for `near: x`.   *)
(*   Also exists under the form `near=> x y`.                                 *)
(* - `near: x` discharges x.                                                  *)
(*   On the goal `H_i x`, and where `x \is_near F`, it asks the user to prove *)
(*   that `\forall x \near F, H_i x`, provided that `H_i x` does not depend   *)
(*   on variables introduced after `x`.                                       *)
(*   Under the hood, it refines by intersection the existential variable `?H` *)
(*   attached to `x`, computes the intersection with `F`, and asks the user   *)
(*   to prove `F H_i`, right now.                                             *)
(* - `end_near` should be used to close remaining existentials trivially.     *)
(* - `near F => x` poses a variable near `F`, where `F` is a proper filter.   *)
(*   It adds to the context a variable `x` that `\is_near F`, i.e., one may   *)
(*   assume `H x` for any `H` in `F`. This new variable `x` can be dealt with *)
(*   using `near: x`, as for variables introduced by `near=>`.                *)
(* - `near do tac` does `near=> x; tac; near: x` where `x` is a fresh         *)
(*   variable                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Making sure that [Program] does not automatically introduce *)
Obligation Tactic := idtac.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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
(*Reserved Notation "[ 'filter' 'of' x ]" (format "[ 'filter'  'of'  x ]").*)
Reserved Notation "F `=>` G" (at level 70, format "F  `=>`  G").
Reserved Notation "F --> G" (at level 70, format "F  -->  G").
Reserved Notation "[ 'lim' F 'in' T ]" (format "[ 'lim'  F  'in'  T ]").
Reserved Notation "[ 'cvg' F 'in' T ]" (format "[ 'cvg'  F  'in'  T ]").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").
Reserved Notation "E @[ x --> F ]"
  (at level 60, x name, format "E  @[ x  -->  F ]").
Reserved Notation "E @[ x \oo ]"
  (at level 60, x name, format "E  @[ x  \oo ]").
Reserved Notation "f @ F" (at level 60, format "f  @  F").
Reserved Notation "E `@[ x --> F ]"
  (at level 60, x name, format "E  `@[ x  -->  F ]").
Reserved Notation "f `@ F" (at level 60, format "f  `@  F").

Definition set_system U := set (set U).
Identity Coercion set_system_to_set : set_system >-> set.

HB.mixin Record isFiltered U T := {
  nbhs : T -> set_system U
}.

#[short(type="filteredType")]
HB.structure Definition Filtered (U : Type) := {T of Choice T & isFiltered U T}.
Arguments nbhs {_ _} _ _ : simpl never.

#[short(type="pfilteredType")]
HB.structure Definition PointedFiltered (U : Type) := {T of Pointed T & isFiltered U T}.

HB.instance Definition _ T := Equality.on (set_system T).
HB.instance Definition _ T := Choice.on (set_system T).
HB.instance Definition _ T := Pointed.on (set_system T).
HB.instance Definition _ T := isFiltered.Build T (set_system T) id.

HB.mixin Record selfFiltered T := {}.

HB.factory Record hasNbhs T := { nbhs : T -> set_system T }.
HB.builders Context T of hasNbhs T.
  HB.instance Definition _ := isFiltered.Build T T nbhs.
  HB.instance Definition _ := selfFiltered.Build T.
HB.end.

#[short(type="nbhsType")]
HB.structure Definition Nbhs := {T of Choice T & hasNbhs T}.

#[short(type="pnbhsType")]
HB.structure Definition PointedNbhs := {T of Pointed T & hasNbhs T}.

Definition filter_from {I T : Type} (D : set I) (B : I -> set T) :
  set_system T := [set P | exists2 i, D i & B i `<=` P].

(* the canonical filter on matrices on X is the product of the canonical filter
   on X *)
HB.instance Definition _ m n X (Z : filteredType X) :=
  isFiltered.Build 'M[X]_(m, n) 'M[Z]_(m, n) (fun mx => filter_from
    [set P | forall i j, nbhs (mx i j) (P i j)]
    (fun P => [set my : 'M[X]_(m, n) | forall i j, P i j (my i j)])).

HB.instance Definition _ m n (X : nbhsType) := selfFiltered.Build 'M[X]_(m, n).

Definition filter_prod {T U : Type}
  (F : set_system T) (G : set_system U) : set_system (T * U) :=
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

Lemma nearE {T} {F : set_system T} (P : set T) :
  (\forall x \near F, P x) = F P.
Proof. by []. Qed.

Lemma eq_near {T} {F : set_system T} (P Q : set T) :
  (forall x, P x <-> Q x) ->
  (\forall x \near F, P x) = (\forall x \near F, Q x).
Proof. by move=> /predeqP ->. Qed.

Lemma nbhs_filterE {T : Type} (F : set_system T) : nbhs F = F.
Proof. by []. Qed.

Module Export NbhsFilter.
Definition nbhs_simpl := (@nbhs_filterE).
End NbhsFilter.

Definition cvg_to {T : Type} (F G : set_system T) := G `<=` F.
Notation "F `=>` G" := (cvg_to F G) : classical_set_scope.

Lemma cvg_refl T (F : set_system T) : F `=>` F. Proof. exact. Qed.
Arguments cvg_refl {T F}.
#[global] Hint Resolve cvg_refl : core.

Lemma cvg_trans T (G F H : set_system T) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Notation "F --> G" := (cvg_to (nbhs F) (nbhs G)) : classical_set_scope.
Definition type_of_filter {T} (F : set_system T) := T.

Definition lim_in {U : Type} (T : pfilteredType U) :=
  fun F : set_system U => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T (nbhs F)) : classical_set_scope.
Definition lim {T : pnbhsType} (F : set_system T) := [lim F in T].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := (F --> lim F).

(* :TODO: ultimately nat could be replaced by any lattice *)
Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Section FilteredTheory.

HB.instance Definition _ X1 X2 (Z1 : filteredType X1) (Z2 : filteredType X2) :=
  isFiltered.Build (X1 * X2)%type (Z1 * Z2)%type
    (fun x => filter_prod (nbhs x.1) (nbhs x.2)).

HB.instance Definition _ (X1 X2 : nbhsType)  :=
  selfFiltered.Build (X1 * X2)%type.

Lemma cvg_prod T {U U' V V' : filteredType T} (x : U) (l : U') (y : V) (k : V') :
  x --> l -> y --> k -> (x, y) --> (l, k).
Proof.
move=> xl yk X [[X1 X2] /= [HX1 HX2] H]; exists (X1, X2) => //=.
split; [exact: xl | exact: yk].
Qed.

Lemma cvg_in_ex {U : Type} (T : pfilteredType U) (F : set_system U) :
  [cvg F in T] <-> (exists l : T, F --> l).
Proof. by split=> [cvg|/getPex//]; exists [lim F in T]. Qed.

Lemma cvg_ex (T : pnbhsType) (F : set_system T) :
  cvg F <-> (exists l : T, F --> l).
Proof. exact: cvg_in_ex. Qed.

Lemma cvg_inP {U : Type} (T : pfilteredType U) (F : set_system U) (l : T) :
  F --> l -> [cvg F in T].
Proof. by move=> Fl; apply/cvg_in_ex; exists l. Qed.

Lemma cvgP (T : pnbhsType) (F : set_system T) (l : T) : F --> l -> cvg F.
Proof. exact: cvg_inP. Qed.

Lemma cvg_in_toP {U : Type} (T : pfilteredType U) (F : set_system U) (l : T) :
  [cvg F in T] -> [lim F in T] = l -> F --> l.
Proof. by move=> /[swap]->. Qed.

Lemma cvg_toP (T : pnbhsType) (F : set_system T) (l : T) :
  cvg F -> lim F = l -> F --> l.
Proof. exact: cvg_in_toP. Qed.

Lemma dvg_inP {U : Type} (T : pfilteredType U) (F : set_system U) :
  ~ [cvg F in T] -> [lim F in T] = point.
Proof. by rewrite /lim_in /=; case xgetP. Qed.

Lemma dvgP (T : pnbhsType) (F : set_system T) : ~ cvg F -> lim F = point.
Proof. exact: dvg_inP. Qed.

Lemma cvg_inNpoint {U} (T : pfilteredType U) (F : set_system U) :
  [lim F in T] != point -> [cvg F in T].
Proof. by apply: contra_neqP; apply: dvg_inP. Qed.

Lemma cvgNpoint (T : pnbhsType) (F : set_system T) : lim F != point -> cvg F.
Proof. exact: cvg_inNpoint. Qed.

End FilteredTheory.
Arguments cvg_inP {U T F} l.
Arguments dvg_inP {U} T {F}.
Arguments cvgP {T F} l.
Arguments dvgP {T F}.

Lemma nbhs_nearE {U} {T : filteredType U} (x : T) (P : set U) :
  nbhs x P = \near x, P x.
Proof. by []. Qed.

Lemma near_nbhs {U} {T : filteredType U} (x : T) (P : set U) :
  (\forall x \near nbhs x, P x) = \near x, P x.
Proof. by []. Qed.

Lemma near2_curry {U V} (F : set_system U) (G : set_system V) (P : U -> set V) :
  {near F & G, forall x y, P x y} = {near (F, G), forall x, P x.1 x.2}.
Proof. by []. Qed.

Lemma near2_pair {U V} (F : set_system U) (G : set_system V) (P : set (U * V)) :
  {near F & G, forall x y, P (x, y)} = {near (F, G), forall x, P x}.
Proof. by symmetry; congr (nbhs _); rewrite predeqE => -[]. Qed.

Definition near2E := (@near2_curry, @near2_pair).

Lemma filter_of_nearI (X : Type) (fX : filteredType X)
  (x : fX) : forall P,
  nbhs x P = @prop_near1 X fX x P (inPhantom (forall x, P x)).
Proof. by []. Qed.

Module Export NearNbhs.
Definition near_simpl := (@near_nbhs, @nbhs_nearE, filter_of_nearI).
Ltac near_simpl := rewrite ?near_simpl.
End NearNbhs.

Lemma near_swap {U V} (F : set_system U) (G : set_system V) (P : U -> set V) :
  (\forall x \near F & y \near G, P x y) = (\forall y \near G & x \near F, P x y).
Proof.
rewrite propeqE; split => -[[/=A B] [FA FB] ABP];
by exists (B, A) => // -[x y] [/=Bx Ay]; apply: (ABP (y, x)).
Qed.

(** Filters *)

Class Filter {T : Type} (F : set_system T) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.
Global Hint Mode Filter - ! : typeclass_instances.

Class ProperFilter {T : Type} (F : set_system T) := {
  filter_not_empty : ~ F set0 ;
  filter_filter : Filter F
}.
(* TODO: Reuse :> above and remove the following line and the coercion below
   after 8.21 is the minimum required version for Coq *)
Global Existing Instance filter_filter.
Global Hint Mode ProperFilter - ! : typeclass_instances.
Arguments filter_not_empty {T} F {_}.
Hint Extern 0 (~ _ set0) => solve [apply: filter_not_empty] : core.

Lemma filter_setT (T : Type) : Filter [set: set T].
Proof. by constructor. Qed.

Lemma filterP_strong T (F : set_system T) {FF : Filter F} (P : set T) :
  (exists Q : set T, exists FQ  : F Q, forall x : T, Q x -> P x) <-> F P.
Proof.
split; last by exists P.
by move=> [Q [FQ QP]]; apply: (filterS QP).
Qed.

Structure filter_on T := FilterType {
  filter :> set_system T;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F :=
  let: FilterType _ class := F in class.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.
(* Typeclasses Opaque filter. *)
Coercion filter_filter : ProperFilter >-> Filter.

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
  PFilterPack F (Build_ProperFilter fN0 fF).
Arguments PFilterType {T} F {fF} fN0.

HB.instance Definition _ T := gen_eqMixin (filter_on T).
HB.instance Definition _ T := gen_choiceMixin (filter_on T).
HB.instance Definition _ T := isPointed.Build (filter_on T)
  (FilterType _ (filter_setT T)).
HB.instance Definition _ T := isFiltered.Build T (filter_on T) (@filter T).

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

Lemma filter_nbhsT {T : Type} (F : set_system T) :
   Filter F -> nbhs F setT.
Proof. by move=> FF; apply: filterT. Qed.
#[global] Hint Resolve filter_nbhsT : core.

Lemma nearT {T : Type} (F : set_system T) : Filter F -> \near F, True.
Proof. by move=> FF; apply: filterT. Qed.
#[global] Hint Resolve nearT : core.

Lemma filter_not_empty_ex {T : Type} (F : set_system T) :
  (forall P, F P -> exists x, P x) -> ~ F set0.
Proof. by move=> /(_ set0) ex /ex []. Qed.

Definition Build_ProperFilter_ex {T : Type} (F : set_system T)
  (filter_ex : forall P, F P -> exists x, P x)
  (FF : Filter F) :=
  Build_ProperFilter (filter_not_empty_ex filter_ex) FF.

Lemma filter_ex_subproof {T : Type} (F : set_system T) :
  ~ F set0 -> (forall P, F P -> exists x, P x).
Proof.
move=> NFset0 P FP; apply: contra_notP NFset0 => nex; suff <- : P = set0 by [].
by rewrite funeqE => x; rewrite propeqE; split=> // Px; apply: nex; exists x.
Qed.

Definition filter_ex {T : Type} (F : set_system T) {FF : ProperFilter F} :=
  filter_ex_subproof (filter_not_empty F).
Arguments filter_ex {T F FF _}.

Lemma filter_getP {T : pointedType} (F : set_system T) {FF : ProperFilter F}
  (P : set T) : F P -> P (get P).
Proof. by move=> /filter_ex /getPex. Qed.

(* Near Tactic *)

Record in_filter T (F : set_system T) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.
(* add ball x e as a canonical instance of nbhs x *)

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set_system T), in_filter F -> T -> Prop.
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
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end
   | match goal with |- ?x \is_near _ => near: x; apply: prop_ofP end ].

Lemma have_near (U : Type) (fT : filteredType U) (x : fT) (P : Prop) :
  ProperFilter (nbhs x) -> (\forall x \near x, P) -> P.
Proof. by move=> FF nP; have [] := @filter_ex _ _ FF (fun=> P). Qed.
Arguments have_near {U fT} x.

Tactic Notation "near" constr(F) "=>" ident(x) :=
  apply: (have_near F); near=> x.

Lemma near T (F : set_system T) P (FP : F P) (x : T)
  (Px : prop_of (InFilter FP) x) : P x.
Proof. by move: Px; rewrite prop_ofE. Qed.
Arguments near {T F P} FP x Px.

Lemma nearW {T : Type} {F : set_system T} (P : T -> Prop) :
  Filter F -> (forall x, P x) -> (\forall x \near F, P x).
Proof. by move=> FF FP; apply: filterS filterT. Qed.

Lemma filterE {T : Type} {F : set_system T} :
  Filter F -> forall P : set T, (forall x, P x) -> F P.
Proof. by move=> [FT _ +] P fP => /(_ setT); apply. Qed.

Lemma filter_app (T : Type) (F : set_system T) :
  Filter F -> forall P Q : set T, F (fun x => P x -> Q x) -> F P -> F Q.
Proof. by move=> FF P Q subPQ FP; near=> x do suff: P x.
Unshelve. all: by end_near. Qed.

Lemma filter_app2 (T : Type) (F : set_system T) :
  Filter F -> forall P Q R : set T,  F (fun x => P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Proof. by move=> ???? PQR FP; apply: filter_app; apply: filter_app FP. Qed.

Lemma filter_app3 (T : Type) (F : set_system T) :
  Filter F -> forall P Q R S : set T, F (fun x => P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ????? PQR FP; apply: filter_app2; apply: filter_app FP. Qed.

Lemma filterS2 (T : Type) (F : set_system T) :
  Filter F -> forall P Q R : set T, (forall x, P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Proof. by move=> ? ? ? ? ?; apply: filter_app2; apply: filterE. Qed.

Lemma filterS3 (T : Type) (F : set_system T) :
  Filter F -> forall P Q R S : set T, (forall x, P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ? ? ? ? ? ?; apply: filter_app3; apply: filterE. Qed.

Lemma filter_const {T : Type} {F} {FF: @ProperFilter T F} (P : Prop) :
  F (fun=> P) -> P.
Proof. by move=> FP; case: (filter_ex FP). Qed.

Lemma in_filter_from {I T : Type} (D : set I) (B : I -> set T) (i : I) :
  D i -> filter_from D B (B i).
Proof. by exists i. Qed.

Lemma in_nearW {T : Type} (F : set_system T) (P : T -> Prop) (S : set T) :
  Filter F -> F S -> {in S, forall x, P x} -> \near F, P F.
Proof.
move=> FF FS SP; rewrite -nbhs_nearE.
by apply: (@filterS _ F _ S) => // x /mem_set /SP.
Qed.

Lemma near_andP {T : Type} F (b1 b2 : T -> Prop) : Filter F ->
  (\forall x \near F, b1 x /\ b2 x) <->
    (\forall x \near F, b1 x) /\ (\forall x \near F, b2 x).
Proof.
move=> FF; split=> [H|[H1 H2]]; first by split; apply: filterS H => ? [].
by apply: filterS2 H1 H2.
Qed.

Lemma nearP_dep {T U} {F : set_system T} {G : set_system U}
   {FF : Filter F} {FG : Filter G} (P : T -> U -> Prop) :
  (\forall x \near F & y \near G, P x y) ->
  \forall x \near F, \forall y \near G, P x y.
Proof.
move=> [[Q R] [/=FQ GR]] QRP.
by apply: filterS FQ => x Q1x; apply: filterS GR => y Q2y; apply: (QRP (_, _)).
Qed.

Lemma filter2P T U (F : set_system T) (G : set_system U)
  {FF : Filter F} {FG : Filter G} (P : set (T * U)) :
  (exists2 Q : set T * set U, F Q.1 /\ G Q.2
     & forall (x : T) (y : U), Q.1 x -> Q.2 y -> P (x, y))
   <-> \forall x \near (F, G), P x.
Proof.
split=> [][[A B] /=[FA GB] ABP]; exists (A, B) => //=.
  by move=> [a b] [/=Aa Bb]; apply: ABP.
by move=> a b Aa Bb; apply: (ABP (_, _)).
Qed.

Lemma filter_ex2 {T U : Type} (F : set_system T) (G : set_system U)
  {FF : ProperFilter F} {FG : ProperFilter G} (P : set T) (Q : set U) :
    F P -> G Q -> exists x : T, exists2 y : U, P x & Q y.
Proof. by move=> /filter_ex [x Px] /filter_ex [y Qy]; exists x, y. Qed.
Arguments filter_ex2 {T U F G FF FG _ _}.

Lemma filter_fromP {I T : Type} (D : set I) (B : I -> set T) (F : set_system T) :
  Filter F -> F `=>` filter_from D B <-> forall i, D i -> F (B i).
Proof.
split; first by move=> FB i ?; apply/FB/in_filter_from.
by move=> FB P [i Di BjP]; apply: (filterS BjP); apply: FB.
Qed.

Lemma filter_fromTP {I T : Type} (B : I -> set T) (F : set_system T) :
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
move=> FF BN0; apply: Build_ProperFilter_ex => P [i Di BiP].
by have [x Bix] := BN0 _ Di; exists x; apply: BiP.
Qed.

Global Instance eventually_filter : ProperFilter eventually.
Proof.
eapply @filter_from_proper; last by move=> i _; exists i => /=.
apply: filter_fromT_filter; first by exists 0%N.
move=> i j; exists (maxn i j) => n //=.
by rewrite geq_max => /andP[ltin ltjn].
Qed.

Canonical eventually_filterType := FilterType eventually _.
Canonical eventually_pfilterType := PFilterType eventually (filter_not_empty _).

Lemma filter_bigI T (I : choiceType) (D : {fset I}) (f : I -> set T)
  (F : set_system T) :
  Filter F -> (forall i, i \in D -> F (f i)) ->
  F (\bigcap_(i in [set` D]) f i).
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

Lemma filter_forall T (I : finType) (f : I -> set T) (F : set_system T) :
    Filter F -> (forall i : I, \forall x \near F, f i x) ->
  \forall x \near F, forall i, f i x.
Proof.
move=> FF fIF; apply: filterS (@filter_bigI T I [fset x in I]%fset f F FF _).
  by move=> x fIx i; have := fIx i; rewrite /= inE/=; apply.
by move=> i; rewrite inE/= => _; apply: (fIF i).
Qed.

Lemma filter_imply [T : Type] [P : Prop] [f : set T] [F : set_system T] :
  Filter F -> (P -> \near F, f F) -> \near F, P -> f F.
Proof.
move=> ? PF; near do move=> /asboolP.
by case: asboolP=> [/PF|_]; by [apply: filterS|apply: nearW].
Unshelve. all: by end_near. Qed.

(** Limits expressed with filters *)

Definition fmap {T U : Type} (f : T -> U) (F : set_system T) : set_system U :=
  [set P | F (f @^-1` P)].
Arguments fmap _ _ _ _ _ /.

Lemma fmapE {U V : Type} (f : U -> V)
  (F : set_system U) (P : set V) : fmap f F P = F (f @^-1` P).
Proof. by []. Qed.

Notation "E @[ x --> F ]" :=
  (fmap (fun x => E) (nbhs F)) : classical_set_scope.
Notation "E @[ x \oo ]" :=
  (fmap (fun x => E) \oo) : classical_set_scope.
Notation "f @ F" := (fmap f (nbhs F)) : classical_set_scope.

Notation limn F := (lim (F @ \oo)).
Notation cvgn F := (cvg (F @ \oo)).

Global Instance fmap_filter T U (f : T -> U) (F : set_system T) :
  Filter F -> Filter (f @ F).
Proof.
move=> FF; constructor => [|P Q|P Q PQ]; rewrite ?fmapE //=.
- exact: filterT.
- exact: filterI.
- by apply: filterS=> ?/PQ.
Qed.
(*Typeclasses Opaque fmap.*)

Global Instance fmap_proper_filter T U (f : T -> U) (F : set_system T) :
  ProperFilter F -> ProperFilter (f @ F).
Proof.
by move=> FF; apply: Build_ProperFilter; rewrite fmapE preimage_set0.
Qed.

Definition fmapi {T U : Type} (f : T -> set U) (F : set_system T) :
    set_system _ :=
  [set P | \forall x \near F, exists y, f x y /\ P y].

Notation "E `@[ x --> F ]" :=
  (fmapi (fun x => E) (nbhs F)) : classical_set_scope.
Notation "f `@ F" := (fmapi f (nbhs F)) : classical_set_scope.

Lemma fmapiE {U V : Type} (f : U -> set V)
  (F : set_system U) (P : set V) :
  fmapi f F P = \forall x \near F, exists y, f x y /\ P y.
Proof. by []. Qed.

Global Instance fmapi_filter T U (f : T -> set U) (F : set_system T) :
  {near F, is_totalfun f} -> Filter F -> Filter (f `@ F).
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
  T U (f : T -> U -> Prop) (F : set_system T) :
  {near F, is_totalfun f} ->
  ProperFilter F -> ProperFilter (f `@ F).
Proof.
move=> f_totalfun FF; apply: Build_ProperFilter_ex.
  by move=> P; rewrite /fmapi/= => /filter_ex [x [y [??]]]; exists y.
exact: fmapi_filter.
Qed.

Lemma cvg_id T (F : set_system T) : x @[x --> F] --> F.
Proof. exact. Qed.
Arguments cvg_id {T F}.

Lemma fmap_comp {A B C} (f : B -> C) (g : A -> B) F:
  Filter F -> (f \o g)%FUN @ F = f @ (g @ F).
Proof. by []. Qed.

Lemma appfilter U V (f : U -> V) (F : set_system U) :
  f @ F = [set P : set _ | \forall x \near F, P (f x)].
Proof. by []. Qed.

Lemma cvg_app U V (F G : set_system U) (f : U -> V) :
  F --> G -> f @ F --> f @ G.
Proof. by move=> FG P /=; exact: FG. Qed.
Arguments cvg_app {U V F G} _.

Lemma cvgi_app U V (F G : set_system U) (f : U -> set V) :
  F --> G -> f `@ F --> f `@ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma cvg_comp T U V (f : T -> U) (g : U -> V)
  (F : set_system T) (G : set_system U) (H : set_system V) :
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Proof. by move=> fFG gGH; apply: cvg_trans gGH => P /fFG. Qed.

Lemma cvgi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set_system T) (G : set_system U) (H : set_system V) :
  f @ F `=>` G -> g `@ G `=>` H -> g \o f `@ F `=>` H.
Proof. by move=> fFG gGH; apply: cvg_trans gGH => P /fFG. Qed.

Lemma near_eq_cvg {T U} {F : set_system T} {FF : Filter F} (f g : T -> U) :
  {near F, f =1 g} -> g @ F `=>` f @ F.
Proof. by move=> eq_fg P /=; apply: filterS2 eq_fg => x /= <-. Qed.

Lemma eq_cvg (T T' : Type) (F : set_system T) (f g : T -> T') (x : set_system T') :
  f =1 g -> (f @ F --> x) = (g @ F --> x).
Proof. by move=> /funext->. Qed.

Lemma eq_is_cvg_in (T T' : Type) (fT : pfilteredType T') (F : set_system T) (f g : T -> T') :
  f =1 g -> [cvg (f @ F) in fT] = [cvg (g @ F) in fT].
Proof. by move=> /funext->. Qed.

Lemma eq_is_cvg (T : Type) (T' : pnbhsType) (F : set_system T) (f g : T -> T') :
  f =1 g -> cvg (f @ F) = cvg (g @ F).
Proof. by move=> /funext->. Qed.

Lemma neari_eq_loc {T U} {F : set_system T} {FF : Filter F} (f g : T -> set U) :
  {near F, f =2 g} -> g `@ F `=>` f `@ F.
Proof.
move=> eq_fg P /=; apply: filterS2 eq_fg => x eq_fg [y [fxy Py]].
by exists y; rewrite -eq_fg.
Qed.

Lemma cvg_near_const (T U : Type) (f : T -> U) (F : set_system T) (G : set_system U) :
  Filter F -> ProperFilter G ->
  (\forall y \near G, \forall x \near F, f x = y) -> f @ F --> G.
Proof.
move=> FF FG fFG P /= GP; rewrite !near_simpl; apply: (have_near G).
by apply: filter_app fFG; near do apply: filterS => x /= ->.
Unshelve. all: by end_near. Qed.

Definition continuous_at (T U : nbhsType) (x : T) (f : T -> U) :=
  (f%function @ x --> f%function x).
Notation continuous f := (forall x, continuous_at x f).

Lemma near_fun (T T' : nbhsType) (f : T -> T') (x : T) (P : T' -> Prop) :
    {for x, continuous f} ->
  (\forall y \near f x, P y) -> (\near x, P (f x)).
Proof. exact. Qed.
Arguments near_fun {T T'} f x.

(* globally filter *)

Definition globally {T : Type} (A : set T) : set_system T :=
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
  A a -> ProperFilter (globally A).
Proof. by move=> Aa; apply: Build_ProperFilter => /(_ a); exact. Qed.

(** Specific filters *)

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

Global Instance filter_prod_filter T U (F : set_system T) (G : set_system U) :
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

Lemma filter_prod1 {T U} {F : set_system T} {G : set_system U}
  {FG : Filter G} (P : set T) :
  (\forall x \near F, P x) -> \forall x \near F & _ \near G, P x.
Proof.
move=> FP; exists (P, setT)=> //= [|[?? []//]].
by split=> //; apply: filterT.
Qed.

Lemma filter_prod2 {T U} {F : set_system T} {G : set_system U}
  {FF : Filter F} (P : set U) :
  (\forall y \near G, P y) -> \forall _ \near F & y \near G, P y.
Proof.
move=> FP; exists (setT, P)=> //= [|[?? []//]].
by split=> //; apply: filterT.
Qed.

Program Definition in_filter_prod {T U} {F : set_system T} {G : set_system U}
  (P : in_filter F) (Q : in_filter G) : in_filter (filter_prod F G) :=
  @InFilter _ _ (fun x => prop_of P x.1 /\ prop_of Q x.2) _.
Next Obligation.
move=> T U F G P Q.
by exists (prop_of P, prop_of Q) => //=; split; apply: prop_ofP.
Qed.

Lemma near_pair {T U} {F : set_system T} {G : set_system U}
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

Lemma near_map {T U} (f : T -> U) (F : set_system T) (P : set U) :
  (\forall y \near f @ F, P y) = (\forall x \near F, P (f x)).
Proof. by []. Qed.

Lemma near_map2 {T T' U U'} (f : T -> U) (g : T' -> U')
      (F : set_system T) (G : set_system T') (P : U -> set U') :
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

Lemma near_mapi {T U} (f : T -> set U) (F : set_system T) (P : set U) :
  (\forall y \near f `@ F, P y) = (\forall x \near F, exists y, f x y /\ P y).
Proof. by []. Qed.

Lemma filter_pair_set (T T' : Type) (F : set_system T) (F' : set_system T') :
   Filter F -> Filter F' ->
   forall (P : set T) (P' : set T') (Q : set (T * T')),
   (forall x x', P x -> P' x' -> Q (x, x')) -> F P /\ F' P' ->
   filter_prod F F' Q.
Proof.
by move=> FF FF' P P' Q PQ [FP FP'];
   near=> x do [have := PQ x.1 x.2; rewrite -surjective_pairing; apply];
   [apply: cvg_fst | apply: cvg_snd].
Unshelve. all: by end_near. Qed.

Lemma filter_pair_near_of (T T' : Type) (F : set_system T) (F' : set_system T') :
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

Lemma filterN {R : numDomainType} (P : pred R) (F : set_system R) :
  (\forall x \near - x @[x --> F], (P \o -%R) x) = \forall x \near F, P x.
Proof. by rewrite near_simpl/= !nearE; under eq_fun do rewrite opprK. Qed.

Lemma cvg_pair {T U V F} {G : set_system U} {H : set_system V}
  {FF : Filter F} {FG : Filter G} {FH : Filter H} (f : T -> U) (g : T -> V) :
  f @ F --> G -> g @ F --> H ->
  (f x, g x) @[x --> F] --> (G, H).
Proof.
move=> fFG gFH P; rewrite !near_simpl => -[[A B] /=[GA HB] ABP]; near=> x.
by apply: (ABP (_, _)); split=> //=; near: x; [apply: fFG|apply: gFH].
Unshelve. all: by end_near. Qed.

Lemma cvg_comp2 {T U V W}
  {F : set_system T} {G : set_system U} {H : set_system V} {I : set_system W}
  {FF : Filter F} {FG : Filter G} {FH : Filter H}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) @[x --> (G, H)] --> I ->
  h (f x) (g x) @[x --> F] --> I.
Proof. by move=> fFG gFH hGHI P /= IP; apply: cvg_pair (hGHI _ IP). Qed.
Arguments cvg_comp2 {T U V W F G H I FF FG FH f g h} _ _ _.
Definition cvg_to_comp_2 := @cvg_comp2.

(* Lemma cvgi_comp_2 {T U V W} *)
(*   {F : set_system T} {G : set_system U} {H : set_system V} {I : set_system W} *)
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
Implicit Types (D : set T) (F : set_system T).

Definition within D F : set_system T := [set P | {near F, D `<=` P}].
Arguments within : simpl never.

Lemma near_withinE D F (P : set T) :
  (\forall x \near within D F, P x) = {near F, D `<=` P}.
Proof. by []. Qed.

Lemma withinT F D : Filter F -> within D F D.
Proof. by move=> FF; rewrite /within/=; apply: filterE. Qed.

Lemma near_withinT F D : Filter F -> \forall x \near within D F, D x.
Proof. exact: withinT. Qed.

Lemma cvg_within {F} {FF : Filter F} D : within D F --> F.
Proof. by move=> P; apply: filterS. Qed.

Lemma withinET {F} {FF : Filter F} : within setT F = F.
Proof.
rewrite eqEsubset /within; split => X //=;
by apply: filter_app => //=; apply: nearW => // x; apply.
Qed.

End within.

Global Instance within_filter T D F : Filter F -> Filter (@within T D F).
Proof.
move=> FF; rewrite /within; constructor => /=.
- by apply: filterE.
- by move=> P Q; apply: filterS2 => x DP DQ Dx; split; [apply: DP|apply: DQ].
- by move=> P Q subPQ; apply: filterS => x DP /DP /subPQ.
Qed.

#[global] Typeclasses Opaque within.

Canonical within_filter_on T D (F : filter_on T) :=
  FilterType (within D F) (within_filter _ _).

Lemma filter_bigI_within T (I : choiceType) (D : {fset I}) (f : I -> set T)
  (F : set (set T)) (P : set T) :
  Filter F -> (forall i, i \in D -> F [set j | P j -> f i j]) ->
  F ([set j | P j -> (\bigcap_(i in [set` D]) f i) j]).
Proof. move=> FF FfD; exact: (@filter_bigI T I D f _ (within_filter P FF)). Qed.

Definition subset_filter {T} (F : set_system T) (D : set T) :=
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
move=> DAP; apply: Build_ProperFilter; rewrite /subset_filter => subFD.
by have /(_ subFD) := DAP (~` D); apply => -[x [dx /(_ dx)]].
Qed.

(* For using near on sets in a filter *)
Section NearSet.
Context {Y : Type}.
Context (F : set_system Y) (PF : ProperFilter F).

Definition powerset_filter_from : set_system (set Y) := filter_from
  [set M | [/\ M `<=` F,
    (forall E1 E2, M E1 -> F E2 -> E2 `<=` E1 -> M E2) & M !=set0 ] ]
  id.

Global Instance powerset_filter_from_filter : ProperFilter powerset_filter_from.
Proof.
split.
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
by move=> E1 E2 [] ? subE ? ?; split => //; exact: subset_trans subE.
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

Lemma near_powerset_map {T U : Type} (f : T -> U) (F : set_system T)
  (P : set U -> Prop) :
  ProperFilter F ->
  (\forall y \near powerset_filter_from (f x @[x --> F]), P y) ->
  (\forall y \near powerset_filter_from F, P (f @` y)).
Proof.
move=> FF [] G /= [Gf Gs [D GD GP]].
have PpF : ProperFilter (powerset_filter_from F).
  exact: powerset_filter_from_filter.
have /= := Gf _ GD; rewrite nbhs_simpl => FfD.
near=> M; apply: GP; apply: (Gs D) => //.
  apply: filterS; first exact: preimage_image.
  exact: (near (near_small_set _) M).
have : M `<=` f @^-1` D by exact: (near (small_set_sub FfD) M).
by move/image_subset/subset_trans; apply; exact: image_preimage_subset.
Unshelve. all: by end_near. Qed.

Lemma near_powerset_map_monoE {T U : Type} (f : T -> U) (F : set_system T)
  (P : set U -> Prop) :
  (forall X Y, X `<=` Y -> P Y -> P X) ->
  ProperFilter F ->
  (\forall y \near powerset_filter_from F, P (f @` y)) =
  (\forall y \near powerset_filter_from (f x @[x --> F]), P y).
Proof.
move=> Pmono FF; rewrite propeqE; split; last exact: near_powerset_map.
case=> G /= [Gf Gs [D GD GP]].
have PpF : ProperFilter (powerset_filter_from (f x @[x-->F])).
  exact: powerset_filter_from_filter.
have /= := Gf _ GD; rewrite nbhs_simpl => FfD; have ffiD : fmap f F (f@` D).
  by rewrite /fmap /=; apply: filterS; first exact: preimage_image.
near=> M; have FfM : fmap f F M by exact: (near (near_small_set _) M).
apply: (@Pmono _ (f @` D)); first exact: (near (small_set_sub ffiD) M).
exact: GP.
Unshelve. all: by end_near. Qed.

Section PrincipalFilters.

Definition principal_filter {X : Type} (x : X) : set_system X :=
  globally [set x].

(** we introducing an alias for pointed types with principal filters *)
Definition principal_filter_type (P : Type) : Type := P.
HB.instance Definition _ (P : choiceType) :=
  Choice.copy (principal_filter_type P) P.
HB.instance Definition _ (P : pointedType) :=
  Pointed.on (principal_filter_type P).
HB.instance Definition _ (P : choiceType) :=
  hasNbhs.Build (principal_filter_type P) principal_filter.
HB.instance Definition _ (P : pointedType) :=
  Filtered.on (principal_filter_type P).

Lemma principal_filterP {X} (x : X) (W : set X) : principal_filter x W <-> W x.
Proof. by split=> [|? ? ->]; [exact|]. Qed.

Lemma principal_filter_proper {X} (x : X) : ProperFilter (principal_filter x).
Proof. exact: globally_properfilter. Qed.

HB.instance Definition _ := hasNbhs.Build bool principal_filter.

End PrincipalFilters.

Section UltraFilters.

Class UltraFilter T (F : set_system T) := {
  #[global] ultra_proper :: ProperFilter F ;
  max_filter : forall G : set_system T, ProperFilter G -> F `<=` G -> G = F
}.

Lemma ultraFilterLemma T (F : set_system T) :
  ProperFilter F -> exists G, UltraFilter G /\ F `<=` G.
Proof.
move=> FF.
set filter_preordset := ({G : set_system T & ProperFilter G /\ F `<=` G}).
set preorder :=
  fun G1 G2 : {classic filter_preordset} => `[< projT1 G1 `<=` projT1 G2 >].
suff [G Gmax] : exists G : {classic filter_preordset}, premaximal preorder G.
  have [GF sFG] := projT2 G; exists (projT1 G); split; last exact: sFG.
  split; [exact: GF|move=> H HF sGH].
  have sFH : F `<=` H by apply: subset_trans sGH.
  have sHG : preorder (existT _ H (conj HF sFH)) G.
    by move/asboolP in sGH; exact: (Gmax (existT _ H (conj HF sFH)) sGH).
  by rewrite predeqE => A; split; [move/asboolP : sHG; exact|exact: sGH].
have sFF : F `<=` F by [].
apply: (ZL_preorder (existT _ F (conj FF sFF))).
- by move=> t; exact/asboolP.
- move=> r s t; rewrite /preorder => /asboolP sr /asboolP st.
  exact/asboolP/(subset_trans _ st).
- move=> A Atot; have [[G AG] | A0] := pselect (A !=set0); last first.
    exists (existT _ F (conj FF sFF)) => G AG.
    by have /asboolP := A0; rewrite asbool_neg => /forallp_asboolPn /(_ G).
  have [GF sFG] := projT2 G.
  suff UAF : ProperFilter (\bigcup_(H in A) projT1 H).
    have sFUA : F `<=` \bigcup_(H in A) projT1 H.
      by move=> B FB; exists G => //; exact: sFG.
    exists (existT _ (\bigcup_(H in A) projT1 H) (conj UAF sFUA)) => H AH.
    by apply/asboolP => B HB /=; exists H.
  apply: Build_ProperFilter_ex.
    by move=> B [H AH HB]; have [HF _] := projT2 H; exact: (@filter_ex _ _ HF).
  split; first by exists G => //; apply: filterT.
  + move=> B C [HB AHB HBB] [HC AHC HCC]; have [sHBC|sHCB] := Atot _ _ AHB AHC.
    * exists HC => //; have [HCF _] := projT2 HC; apply: filterI HCC.
      by move/asboolP : sHBC; exact.
    * exists HB => //; have [HBF _] := projT2 HB; apply: filterI HBB _.
      by move/asboolP : sHCB; exact.
  + move=> B C SBC [H AH HB]; exists H => //; have [HF _] := projT2 H.
    exact: filterS HB.
Qed.

Lemma filter_image (T U : Type) (f : T -> U) (F : set_system T) :
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

Lemma proper_image (T U : Type) (f : T -> U) (F : set_system T) :
  ProperFilter F -> f @` setT = setT -> ProperFilter [set f @` A | A in F].
Proof.
move=> FF fsurj; apply: Build_ProperFilter_ex; last exact: filter_image.
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

Lemma in_ultra_setVsetC T (F : set_system T) (A : set T) :
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

Lemma ultra_image (T U : Type) (f : T -> U) (F : set_system T) :
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

End UltraFilters.

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

Lemma smallest_filter_finI {I T : choiceType} (D : set I) (f : I -> set T) :
  filter_from (finI_from D f) id = smallest (@Filter T) (f @` D).
Proof. by rewrite filterI_iter_finI filterI_iterE. Qed.

End filter_supremums.

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

Lemma filter_finI (T : choiceType) (F : set_system T) (D : set_system T)
  (f : set T -> set T) :
  ProperFilter F -> (forall A, D A -> F (f A)) -> finI D f.
Proof.
move=> FF sDFf D' sD; apply: (@filter_ex _ F); apply: filter_bigI.
by move=> A /sD; rewrite inE => /sDFf.
Qed.

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

Lemma meetsxx T (F : set_system T) (FF : Filter F) : F `#` F = ~ (F set0).
Proof.
rewrite propeqE; split => [FmF F0|]; first by have [x []] := FmF _ _ F0 F0.
move=> FN0 A B /filterI FAI {}/FAI FAB; apply/set0P/eqP => AB0.
by rewrite AB0 in FAB.
Qed.

Lemma proper_meetsxx T (F : set_system T) (FF : ProperFilter F) : F `#` F.
Proof. by rewrite meetsxx. Qed.
