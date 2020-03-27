(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop ssralg ssrnum finmap matrix.
Require Import boolp Rstruct classical_sets posnum.

(******************************************************************************)
(* This file develops tools for the manipulation of filters and basic         *)
(* topological notions.                                                       *)
(*                                                                            *)
(* * Filters :                                                                *)
(*                   filterType U == interface type for types whose         *)
(*                                     elements represent sets of sets on U.  *)
(*                                     These sets are intended to be filters  *)
(*                                     on U but this is not enforced yet.     *)
(*               FilterType U T m == packs the function m: T -> set (set U) *)
(*                                     to build a filtered type of type       *)
(*                                     filterType U; T must have a          *)
(*                                     pointedType structure.                 *)
(*     [filterType U of T for cT] == T-clone of the filterType U          *)
(*                                     structure cT.                          *)
(*            [filterType U of T] == clone of a canonical filterType U    *)
(*                                     structure on T.                        *)
(*              Filter.source Y Z == structure that records types X such    *)
(*                                     that there is a function mapping       *)
(*                                     functions of type X -> Y to filters on *)
(*                                     Z. Allows to infer the canonical       *)
(*                                     filter associated to a function by     *)
(*                                     looking at its source type.            *)
(*                Filter.Source F == if F : (X -> Y) -> set (set Z), packs  *)
(*                                     X with F in a Filter.source Y Z      *)
(*                                     structure.                             *)
(*                        locally p == set of sets associated to p (in a      *)
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
(*                     [lim F in T] == limit in T of the canonical filter     *)
(*                                     associated to F; T must have a         *)
(*                                     filterType structure.                *)
(*                            lim F == same as [lim F in T] where T is        *)
(*                                     inferred from the type of the          *)
(*                                     canonical filter associated to F.      *)
(*                    [cvg F in T] <-> the canonical filter associated to F   *)
(*                                     converges in T.                        *)
(*                           cvg F <-> same as [cvg F in T] where T is        *)
(*                                     inferred from the type of the          *)
(*                                     canonical filter associated to F.      *)
(*                         is_filter F == type class proving that the set of     *)
(*                                     sets F is a filter.                    *)
(*                   is_pfilter F == type class proving that the set of     *)
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
(*                                     FF of is_pfilter F to build a        *)
(*                                     pfilter_on T structure.                *)
(*                    filtermap f F == image of the filter F by the function  *)
(*                                     f.                                     *)
(*                     E @[x --> F] == image of the canonical filter          *)
(*                                     associated to F by the function        *)
(*                                     (fun x => E).                          *)
(*                            f @ F == image of the canonical filter          *)
(*                                     associated to F by the function f.     *)
(*                   filtermapi f F == image of the filter F by the relation  *)
(*                                     f.                                     *)
(*                    E `@[x --> F] == image of the canonical filter          *)
(*                                     associated to F by the relation        *)
(*                                     (fun x => E).                          *)
(*                           f `@ F == image of the canonical filter          *)
(*                                     associated to F by the relation f.     *)
(*                       at_point a == filter of the sets containing a.       *)
(*                       within D F == restriction of the filter F to the     *)
(*                                     domain D.                              *)
(*                subset_filter F D == similar to within D F, but with        *)
(*                                     dependent types.                       *)
(*                      in_filter F == interface type for the sets that       *)
(*                                     belong to the set of sets F.           *)
(*                      InFilter FP == packs a set P with a proof of F P to   *)
(*                                     build a in_filter F structure.         *)
(*                              \oo == "eventually" filter on nat: set of     *)
(*                                     predicates on natural numbers that are *)
(*                                     eventually true.                       *)
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
(*                     \near x, P x := \forall y \near x, P x.                *)
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
(*   TopologicalMixin loc_filt locE == builds the mixin for a topological     *)
(*                                     space from the proofs that locally     *)
(*                                     outputs proper filters and defines the *)
(*                                     same notion of neighbourhood as the    *)
(*                                     open sets.                             *)
(*   topologyOfFilterMixin loc_filt loc_sing loc_loc == builds the mixin for  *)
(*                                     a topological space from the           *)
(*                                     properties of nbhs.                 *)
(*   topologyOfOpenMixin opT opI op_bigU == builds the mixin for a            *)
(*                                     topological space from the properties  *)
(*                                     of open sets.                          *)
(*   topologyOfBaseMixin b_cover b_join == builds the mixin for a topological *)
(*                                     space from the properties of a base of *)
(*                                     open sets; the type of indices must be *)
(*                                     a pointedType.                         *)
(*       topologyOfSubbaseMixin D b == builds the mixin for a topological     *)
(*                                     space from a subbase of open sets b    *)
(*                                     indexed on domain D; the type of       *)
(*                                     indices must be a pointedType.         *)
(*              TopologicalType T m == packs the mixin m to build a           *)
(*                                     topologicalType; T must have a         *)
(*                                     canonical filterType T structure.    *)
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
(*           [topologicalType of T] == clone of a canonical topologicalType   *)
(*                                     structure on T.                        *)
(*                             open == set of open sets.                      *)
(*                          neigh p == set of open neighbourhoods of p.       *)
(*                    continuous f <-> f is continuous w.r.t the topology.    *)
(*                       nbhs' x == set of neighbourhoods of x where x is  *)
(*                                     excluded.                              *)
(*                        closure A == closure of the set A.                  *)
(*                           closed == set of closed sets.                    *)
(*                        cluster F == set of cluster points of F.            *)
(*                          compact == set of compact sets w.r.t. the filter- *)
(*                                     based definition of compactness.       *)
(*                     hausdorff T <-> T is a Hausdorff space (T_2).          *)
(*                    cover_compact == set of compact sets w.r.t. the open    *)
(*                                     cover-based definition of compactness. *)
(*                     connected A <-> the only non empty subset of A which   *)
(*                                     is both open and closed in A is A.     *)
(* --> We used these topological notions to prove Tychonoff's Theorem, which  *)
(*     states that any product of compact sets is compact according to the    *)
(*     product topology.                                                      *)
(*                                                                            *)
(* * Uniform spaces :                                                         *)
(*                  nbhs_ ball == neighbourhoods defined using balls       *)
(*                    uniformType == interface type for uniform space         *)
(*                                   structure. We use here a pseudo-metric   *)
(*                                   definition of uniform space: a type      *)
(*                                   equipped with balls.                     *)
(*      UniformMixin brefl bsym btriangle locb == builds the mixin for a      *)
(*                                   uniform space from the properties of     *)
(*                                   balls and the compatibility between      *)
(*                                   balls and nbhs.                       *)
(*                UniformType T m == packs the uniform space mixin into a     *)
(*                                   uniformType. T must have a canonical     *)
(*                                   topologicalType structure.               *)
(*      [uniformType of T for cT] == T-clone of the uniformType structure cT. *)
(*             [uniformType of T] == clone of a canonical uniformType         *)
(*                                   structure on T.                          *)
(*     topologyOfBallMixin umixin == builds the mixin for a topological space *)
(*                                   from a mixin for a uniform space.        *)
(*                       ball x e == ball of center x and radius e.           *)
(*                     close x y <-> x and y are arbitrarily close w.r.t. to  *)
(*                                   balls.                                   *)
(*                     entourages == set of entourages defined by balls. An   *)
(*                                   entourage can be seen as a               *)
(*                                   "neighbourhood" of the diagonal set      *)
(*                                   D = {(x, x) | x in T}.                   *)
(*                   ball_set A e == set A extended with a band of width e    *)
(*                   unif_cont f <-> f is uniformly continuous.               *)
(*                                                                            *)
(* * Complete spaces :                                                        *)
(*                   cauchy_ex F <-> the set of sets F is a cauchy filter     *)
(*                                   (epsilon-delta definition).              *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (using the near notations).              *)
(*                   completeType == interface type for a complete uniform    *)
(*                                   space structure.                         *)
(*       CompleteType T cvgCauchy == packs the proof that every proper cauchy *)
(*                                   filter on T converges into a             *)
(*                                   completeType structure; T must have a    *)
(*                                   canonical uniformType structure.         *)
(*     [completeType of T for cT] == T-clone of the completeType structure    *)
(*                                   cT.                                      *)
(*            [completeType of T] == clone of a canonical completeType        *)
(*                                   structure on T.                          *)
(******************************************************************************)

Reserved Notation "{ 'near' x , P }" (at level 0, format "{ 'near'  x ,  P }").
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x ident, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "'\near' x , P"
  (at level 200, x at level 99, P at level 200,
   format "'\near'  x ,  P", only parsing).
Reserved Notation "{ 'near' x & y , P }"
  (at level 0, format "{ 'near'  x  &  y ,  P }").
Reserved Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P"
  (at level 200, x ident, y ident, P at level 200,
   format "'\forall'  x  '\near'  x_0  &  y  '\near'  y_0 ,  P").
Reserved Notation "'\forall' x & y '\near' z , P"
  (at level 200, x ident, y ident, P at level 200,
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
  (at level 60, x ident, format "E  @[ x  -->  F ]").
Reserved Notation "f @ F" (at level 60, format "f  @  F").
Reserved Notation "E `@[ x --> F ]"
  (at level 60, x ident, format "E  `@[ x  -->  F ]").
Reserved Notation "f `@ F" (at level 60, format "f  `@  F").
Reserved Notation "A ^°" (at level 1, format "A ^°").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.

Section function_space.

Definition cst {T T' : Type} (x : T') : T -> T' := fun=> x.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @ZmodMixin (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g) _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite addrA. Qed.
Next Obligation. by move=> f g; rewrite funeqE=> x /=; rewrite addrC. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite add0r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite addNr. Qed.
Canonical fct_zmodType T (M : zmodType) := ZmodType (T -> M) (fct_zmodMixin T M).

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @RingMixin [zmodType of T -> M] (cst 1) (fun f g x => f x * g x)
             _ _ _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrA. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mul1r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mulr1. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDl. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDr. Qed.
Next Obligation.
by apply/eqP; rewrite funeqE => /(_ point) /eqP; rewrite oner_eq0.
Qed.
Canonical fct_ringType (T : pointedType) (M : ringType) :=
  RingType (T -> M) (fct_ringMixin T M).

Program Canonical fct_comRingType (T : pointedType) (M : comRingType) :=
  ComRingType (T -> M) _.
Next Obligation. by move=> f g; rewrite funeqE => x; rewrite mulrC. Qed.

Program Definition fct_lmodMixin (U : Type) (R : ringType) (V : lmodType R)
  := @LmodMixin R [zmodType of U -> V] (fun k f => k \*: f) _ _ _ _.
Next Obligation. rewrite funeqE => x; exact: scalerA. Qed.
Next Obligation. by move=> f; rewrite funeqE => x /=; rewrite scale1r. Qed.
Next Obligation. by move=> f g h; rewrite funeqE => x /=; rewrite scalerDr. Qed.
Next Obligation. by move=> f g; rewrite funeqE => x /=; rewrite scalerDl. Qed.
Canonical fct_lmodType U (R : ringType) (V : lmodType R) :=
  LmodType _ (U -> V) (fct_lmodMixin U V).

Lemma fct_sumE (T : Type) (M : zmodType) n (f : 'I_n -> T -> M) (x : T) :
  (\sum_(i < n) f i) x = \sum_(i < n) f i x.
Proof. by elim/big_rec2: _ => // ? ? ? _ <-. Qed.

End function_space.

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

Record is_filter {T : Type} (F : set (set T)) := {
  filterT_prop : F setT ;
  filterI_prop : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS_prop : forall P Q : set T, P `<=` Q -> F P -> F Q
}.

Record is_pfilter {T : Type} (F : set (set T)) := Build_is_pfilter' {
  filter_not_empty_prop : ~ F set0 ;
  filter_pfilter : is_filter F
}.  

Lemma filter_setT (T' : Type) : is_filter (@setT (set T')).
Proof. by constructor. Qed.

Coercion filter_pfilter : is_pfilter >-> is_filter.

Structure nbhs_on T := Nbhs {
  in_nbhs :> set (set T);
}.
Arguments Nbhs {T}.
Arguments in_nbhs : simpl never.

Structure filter_on T := Filter {
  in_filter :> (T -> Prop) -> Prop;
  _ : is_filter in_filter
}.
Definition filter_class T (F : filter_on T) : is_filter F :=
  let: Filter _ class := F in class.
Arguments Filter {T} _ _.
Canonical filter_nbhs_on T (F : filter_on T) :=
  Nbhs (in_filter F).
Coercion filter_nbhs_on : filter_on >-> nbhs_on.

Structure pfilter_on T := PFilterPack {
  in_pfilter :> (T -> Prop) -> Prop;
  _ : is_pfilter in_pfilter
}.
Definition pfilter_class T (F : pfilter_on T) : is_pfilter F :=
  let: PFilterPack _ class := F in class.
Arguments PFilterPack {T} _ _.
Canonical pfilter_nbhs_on T (F : pfilter_on T) := Nbhs F.
Coercion pfilter_nbhs_on : pfilter_on >-> nbhs_on.
Canonical pfilter_filter_on T (F : pfilter_on T) :=
  Filter F (pfilter_class F).
Coercion pfilter_filter_on : pfilter_on >-> filter_on.

Definition PFilter_of {T} (F : set (set T)) (fN0 : not (F set0)) :=
  fun (fF : filter_on T) of phant_id F (fF : set (set T)) =>
  fun fFF of phant_id (Filter _ fFF) fF =>
  PFilterPack F (Build_is_pfilter' fN0 fFF).
Notation PFilter F fN0 := (@PFilter_of _ F fN0 _ id _ id).

Identity Coercion set_id : set >-> Funclass.
Arguments filter : simpl never.

Module Nbhs.

(* Index a family of filters on a type, one for each element of the type *)
Record mixin_of U T := Mixin {
  nbhs_op : T -> nbhs_on U;
}.
Definition Mixin_ U T nbhs_op := @Mixin U T (fun x => Nbhs (nbhs_op x)).

Record class_of U T := Class {
  base : Pointed.class_of T;
  mixin : mixin_of U T
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
  _ : mixin_of Y (source_type -> Z)
}.
Definition source_filter Z Y (F : source Z Y) : mixin_of Y (F -> Z) :=
  let: Source X f := F in f.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Pointed.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion fpointedType : type >-> Pointed.type.
Canonical fpointedType.
Notation nbhsType := type.
Notation NbhsMixin := Mixin_.
Notation NbhsType U T m := (@pack U T m _ _ idfun).
Notation "[ 'nbhsType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'nbhsType'  U  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'nbhsType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'nbhsType'  U  'of'  T ]") : form_scope.
Notation "[ 'nbhsType' 'of' T 'for' cT ]" :=  (@clone T T cT _ idfun)
  (at level 0, format "[ 'nbhsType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'nbhsType' 'of' T ]" := (@clone T T _ _ id)
  (at level 0, format "[ 'nbhsType'  'of'  T ]") : form_scope.

(* The default filter for an arbitrary element is the one obtained *)
(* from its type *)
Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  NbhsType Y (X -> Z) (@source_filter _ _ X).

Canonical source_filter_filter_to_Prop Y :=
  @Source Prop _ (_ -> Prop) (Mixin_ (fun x : (set (set Y)) => x)).
Canonical source_filter_filter_set Y :=
  @Source Prop _ (set _) (Mixin_ (fun x : (set (set Y)) => x)).
 
End Exports.
End Nbhs.
Export Nbhs.Exports.

Canonical nbhs_on_eqType T := EqType (nbhs_on T) gen_eqMixin.
Canonical nbhs_on_choiceType T :=
  ChoiceType (nbhs_on T) gen_choiceMixin.
Canonical nbhs_on_PointedType T :=
  PointedType (nbhs_on T) (Filter _ (filter_setT T)).
Definition nbhs_on_nbhs_mixin T := NbhsMixin (@in_nbhs T).
Canonical nbhs_on_NbhsType T :=
  NbhsType T (nbhs_on T) (@nbhs_on_nbhs_mixin T).
Notation "{ 'nbhs' T }" := (nbhs_on_NbhsType T)
  (at level 0, format "{ 'nbhs'  T }" ) : type_scope.

Definition nbhs {U} {T : nbhsType U} := Nbhs.nbhs_op (Nbhs.class T).
(* Coercion nbhs_coercion := @nbhs. *)
(* Arguments nbhs_coercion /. *)

(* Notation "[ 'nbhs' x ]" :=  *)
(*   (at level 0, format "[ 'nbhs'  x ]" ) : type_scope. *)

Module Filter.

Section ClassDef.
Variable U : Type.

(* Index a family of filters on a type, one for each element of the type *)
Record mixin_of (T : nbhsType U) := Mixin {
  _ : forall x : T, is_filter (nbhs x)
}.

Record class_of T := Class {
  base : Nbhs.class_of U T;
  mixin : mixin_of (Nbhs.Pack base)
}.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Nbhs.class_of.

Definition pack (fT : nbhsType U) (m : mixin_of fT) :=
  fun bT b of phant_id (@Nbhs.class U bT) b =>
  fun m' of phant_id m m' => @Pack T (@Class T b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition nbhsType := @Nbhs.Pack U cT xclass.

Definition nbhs (x : cT) : nbhsType := x.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Nbhs.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion nbhsType : type >-> Nbhs.type.
Canonical nbhsType.
Coercion nbhs : Filter.sort >-> Nbhs.sort.
Notation filterType := type.
Notation FilterMixin := Mixin.
Notation FilterType U T m := (@pack U T _ m _ _ idfun _ idfun).
Notation "[ 'filterType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'filterType'  U  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'filterType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'filterType'  U  'of'  T ]") : form_scope.

End Exports.
End Filter.
Export Filter.Exports.

Canonical filter_on_eqType T := EqType (filter_on T) gen_eqMixin.
Canonical filter_on_choiceType T :=
  ChoiceType (filter_on T) gen_choiceMixin.
Canonical filter_on_PointedType T :=
  PointedType (filter_on T) (Filter _ (filter_setT T)).
Definition filter_on_nbhs_mixin T := NbhsMixin (@in_filter T).
Canonical filter_on_NbhsType T :=
  NbhsType T (filter_on T) (@filter_on_nbhs_mixin T).
Definition filter_on_filtered_mixin T := FilterMixin (@filter_class T).
Canonical filter_on_filterType T :=
  FilterType T (filter_on T) (@filter_on_filtered_mixin T).
Notation "{ 'filter' T }" := (filter_on_NbhsType T)
  (at level 0, format "{ 'filter'  T }" ) : type_scope.

Lemma nbhs_is_filter {U} {T : filterType U} (x : T) : is_filter (nbhs x).
Proof. by rewrite /nbhs /Nbhs.nbhs_op; move: T x => [? [? []]]. Qed.

Canonical nbhs_filter {U} {T : filterType U} (x : T) :=
  Filter (nbhs x) (nbhs_is_filter x).

Notation "'\forall' x '\near' x_0 , P" := (in_nbhs (nbhs x_0) (fun x => P))
  (at level 200, x ident, P at level 200, format "'\forall'  x  '\near'  x_0 ,  P") : type_scope.
Notation "'\near' x , P" := (\forall x \near x, P)
  (at level 200, x at level 99, P at level 200, format "'\near'  x ,  P", only parsing) : type_scope.

Section NearBasics.
Context {T : nonPropType} {fT : filterType T}.
Implicit Type x : fT.

Lemma nearT x : \near x, True. Proof. by case: (nbhs_is_filter x). Qed.

Lemma nearI x P Q : (\near x, P x) -> (\near x, Q x) -> \near x, P x /\ Q x.
Proof. by case: (nbhs_is_filter x) => _ nI _; apply: nI. Qed.

Lemma nearS x P Q : P `<=` Q -> (\near x, P x) -> \near x, Q x.
Proof. by case: (nbhs_is_filter x) => _ _; apply. Qed.
End NearBasics.

Module PFilter.

Section ClassDef.
Variable U : Type.

(* Index a family of filters on a type, one for each element of the type *)
Record mixin_of (T : filterType U) := Mixin {
  nbhs_pfilter : forall x : T, ~ \near x, False
}.

Record class_of T := Class {
  base : Filter.class_of U T;
  mixin : mixin_of (Filter.Pack base)
}.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Filter.class_of.

Definition pack (fT : filterType U) (m : mixin_of fT) :=
  fun bT b of phant_id (@Filter.class U bT) b => 
  fun m' of phant_id m m' => @Pack T (@Class T b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition nbhsType := @Nbhs.Pack U cT xclass.
Definition filterType := @Filter.Pack U cT xclass.

Definition nbhs (x : cT) : nbhsType := x.
Definition filter (x : cT) : filterType := x.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Filter.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion nbhsType : type >-> Nbhs.type.
Canonical nbhsType.
Coercion filterType : type >-> Filter.type.
Canonical filterType.
Coercion nbhs : sort >-> Nbhs.sort.
Coercion filter : sort >-> Filter.sort.
Notation pfilterType := type.
Notation PFilterMixin := Mixin.
Notation PFilterType U T m := (@pack U T _ m _ _ idfun _ idfun).
Notation "[ 'pfilterType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'pfilterType'  U  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pfilterType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'pfilterType'  U  'of'  T ]") : form_scope.

End Exports.
End PFilter.
Export PFilter.Exports.

Lemma nbhs_is_pfilter {U} {T : pfilterType U} (x : T) : ~ \near x, False.
Proof. by case: T x => T [/= ? []]. Qed.

Canonical nbhs_pfilter {U} {T : pfilterType U} (x : T) :=
  PFilterPack (in_nbhs (nbhs x))
   (Build_is_pfilter' (@nbhs_is_pfilter U T x) (@nbhs_is_filter U T x)).

Definition nbhs_pfilter_mixin U T := PFilterMixin (@nbhs_is_pfilter U T).

Canonical nbhs_pfilterType {U} {T : pfilterType U} (x : T) :=
  PFilterType U T (@nbhs_pfilter_mixin U T).

(* Near Tactic *)

Record filter_elt T (F : set (set T)) := FilterElt {
  prop_filter_elt_proj : set T;
  prop_filter_eltP_proj : F prop_filter_elt_proj
}.
(* add ball x e as a canonical instance of nbhs x *)

Module Type FilterEltSig.
Axiom t : forall (T : Type) (F : set (set T)), filter_elt F -> T -> Prop.
Axiom tE : t = prop_filter_elt_proj.
End FilterEltSig.
Module FilterElt : FilterEltSig.
Definition t := prop_filter_elt_proj.
Lemma tE : t = prop_filter_elt_proj. Proof. by []. Qed.
End FilterElt.
(* Coercion FilterElt.t : filter_elt >-> Funclass. *)
Notation prop_of := FilterElt.t.
Definition prop_ofE := FilterElt.tE.
Notation "x \is_near F" := (@FilterElt.t _ F _ x).
Definition is_nearE := prop_ofE.

Lemma prop_ofP T F (iF : @filter_elt T F) : F (prop_of iF).
Proof. by rewrite prop_ofE; apply: prop_filter_eltP_proj. Qed.

Definition filter_eltT T (fT : filterType T) (F : fT) : @filter_elt T (nbhs F) :=
  FilterElt (nearT _).
Canonical filter_eltI T (fT : filterType T) (F : fT) (P Q : @filter_elt T (nbhs F)) :=
  FilterElt (nearI (prop_filter_eltP_proj P) (prop_filter_eltP_proj Q)).

Lemma filter_near_of T (fT : filterType T) (F : fT)
  (P : @filter_elt T (nbhs F)) (Q : set T) :
  (forall x, prop_of P x -> Q x) -> nbhs F Q.
Proof. by move: P => [P FP] /=; rewrite prop_ofE /= => /nearS; apply. Qed.

Lemma near_acc_key : unit. Proof. exact: tt. Qed.

Fact near_key : unit. Proof. exact. Qed.

Lemma mark_near (P : Prop) : locked_with near_key P -> P.
Proof. by rewrite unlock. Qed.

Lemma near_acc T (fT : filterType T) (F : fT) (P : @filter_elt T (nbhs F)) (Q : set T)
   (FQ : \forall x \near F, Q x) :
   locked_with near_key
  (forall x, prop_of (filter_eltI P (FilterElt FQ)) x -> (Q x)).
Proof. by rewrite unlock => x /=; rewrite !prop_ofE /= => -[Px]. Qed.

Lemma nearW T (fT : filterType T) (F : fT) (P Q : @filter_elt T (nbhs F)) (G : set T) :
   locked_with near_key (forall x, prop_of P x -> G x) ->
   locked_with near_key (forall x, prop_of (filter_eltI P Q) x -> G x).
Proof.
rewrite !unlock => FG x /=; rewrite !prop_ofE /= => -[Px Qx].
by have /= := FG x; apply; rewrite prop_ofE.
Qed.

Tactic Notation "near=>" ident(x) := apply: filter_near_of => x ?.

Ltac just_discharge_near x :=
  tryif match goal with Hx : x \is_near _ |- _ => move: (x) (Hx); apply: mark_near end
        then idtac else fail "the variable" x "is not a ""near"" variable".
Ltac near_skip :=
  match goal with |- locked_with near_key (forall _, @FilterElt.t _ _ ?P _ -> _) =>
    tryif is_evar P then fail "nothing to skip" else apply: nearW end.

Tactic Notation "near:" ident(x) :=
  just_discharge_near x;
  tryif do ![apply: near_acc; [shelve|..]|near_skip]
  then idtac
  else fail "the goal depends on variables introduced after" x.

Ltac end_near := do ?exact: filter_eltT.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end
   | match goal with |- ?x \is_near _ => near: x; apply: prop_ofP end ].

Canonical pfilter_on_eqType T := EqType (pfilter_on T) gen_eqMixin.
Canonical pfilter_on_choiceType T :=
  ChoiceType (pfilter_on T) gen_choiceMixin.

Lemma set1T_is_filter T : @is_filter T (set1 setT).
Proof.
rewrite /set1; split => //= P Q; first by move=> -> ->; rewrite predeqE.
by move=> PQ PT; rewrite predeqE => x; split => // _; apply/PQ; rewrite PT.
Qed.

Lemma setTN0 (T : pointedType) :  ~ [set (@setT T)] set0.
Proof. by rewrite /set0 => /(congr1 (@^~ point)) ->. Qed.

Lemma pfilter_is_filter (T : Type) (pT : pfilter_on T) : is_filter (in_pfilter pT).
Proof. by case: pT => ? []. Qed.

Canonical pfilter_on_PointedType (T : pointedType) :=
  PointedType (pfilter_on T)
   (@PFilterPack _ _ (Build_is_pfilter' (@setTN0 _) (set1T_is_filter _))).
Definition pfilter_on_nbhs_mixin (T : pointedType)  := NbhsMixin (@in_pfilter T).
Canonical pfilter_on_NbhsType (T : pointedType) :=
  NbhsType T (pfilter_on T) (@pfilter_on_nbhs_mixin T).
Definition pfilter_on_filter_mixin (T : pointedType)  :=
  FilterMixin (@pfilter_is_filter T).
Canonical pfilter_on_filterType (T : pointedType) :=
  FilterType T (pfilter_on T) (@pfilter_on_filter_mixin T).

Lemma pfilter_on_pfilter (T : pointedType) (pT : pfilter_on T) :
   ~ (in_pfilter pT) set0.
Proof. by case: pT => /= F []. Qed.
Definition pfilter_on_pfilter_mixin (T : pointedType)  :=
  PFilterMixin (@pfilter_on_pfilter T).
Canonical pfilter_on_pfilterType (T : pointedType) :=
  PFilterType T (pfilter_on T) (@pfilter_on_pfilter_mixin T).

Notation "{ 'pfilter' T }" := (pfilter_on_NbhsType T)
  (at level 0, format "{ 'pfilter'  T }" ) : type_scope.

Lemma pfilter_on_is_pfilter T (x : {pfilter T}) : is_pfilter x.
Proof. by case: x. Qed.

Lemma near_ex_subproof {T : Type} (F : set (set T)) :
     ~ nbhs F set0 -> (forall P, F P -> exists x, P x).
Proof.
move=> NFset0 P FP; apply: contrapNT NFset0 => nex; suff <- : P = set0 by [].
by rewrite funeqE => x; rewrite propeqE; split=> // Px; apply: nex; exists x.
Qed.

Lemma filter_not_empty T (fT : pfilterType T) (F : fT) : ~ \near F, False.
Proof. by case: fT F => [? [? []]]. Qed.
Arguments filter_not_empty {T fT} F _.

Definition near_ex {T : nonPropType}  {fT : pfilterType T} (F : fT) :
  forall P, nbhs F P -> exists x : T, P x :=
  near_ex_subproof (filter_not_empty F).

Lemma near_getP {T : pointedType} {fT : pfilterType T} (F : fT) (P : set T) :
  nbhs F P -> P (get P).
Proof. by move=> /near_ex /getPex. Qed.

Lemma near_const {T : nonPropType} {fT : pfilterType T} (F : fT) (P : Prop) :
  (\near F, P) -> P.
Proof. by move=> FP; case: (near_ex FP). Qed.
Arguments near_const {T fT} x : rename.

Tactic Notation "near" constr(F) "=>" ident(x) :=
  apply: (near_const F); near=> x.

Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T) :=
  [set P | exists2 i, D i & B i `<=` P].

Lemma filter_from_filter {I T : Type} (D : set I) (B : I -> set T) :
  (exists i : I, D i) ->
  (forall i j, D i -> D j -> exists2 k, D k & B k `<=` B i `&` B j) ->
  is_filter (filter_from D B).
Proof.
move=> [i0 Di0] Binter; constructor; first by exists i0.
- move=> P Q [i Di BiP] [j Dj BjQ]; have [k Dk BkPQ]:= Binter _ _ Di Dj.
  by exists k => // x /BkPQ [/BiP ? /BjQ].
- by move=> P Q subPQ [i Di BiP]; exists i; apply: subset_trans subPQ.
Qed.

Lemma filter_fromT_filter {I T : Type} (B : I -> set T) :
  (exists _ : I, True) ->
  (forall i j, exists k, B k `<=` B i `&` B j) ->
  is_filter (filter_from setT B).
Proof.
move=> [i0 _] BI; apply: filter_from_filter; first by exists i0.
by move=> i j _ _; have [k] := BI i j; exists k.
Qed.

Section ProdNbhsType.
Context {T U : Type} {fT : nbhsType T} {fU : nbhsType U}.

Definition prod_filter (x : fT) (y : fU) : set (set (T * U)) :=
  filter_from (fun P => (nbhs x) P.1 /\ (nbhs y) P.2) (fun P => P.1 `*` P.2).

Definition prod_nbhs_mixin := NbhsMixin (fun x => prod_filter x.1 x.2).

Canonical prod_nbhs := NbhsType (T * U) (fT * fU) prod_nbhs_mixin.
End ProdNbhsType.

Section ProdFilter.
Context {T U : Type} {fT : filterType T} {fU : filterType U}.

Lemma prod_filter_filter (x : fT * fU) : is_filter (in_nbhs (nbhs x)).
Proof.
apply: filter_from_filter => [|[P Q] [P' Q'] /= [FP GQ] [FP' GQ']].
  by exists (setT, setT) => /=; split; apply: nearT.
exists (P `&` P', Q `&` Q') => /=; first by split; apply: nearI.
by move=> [p q] [/= [? ?] []].
Qed.
 
Definition prod_filter_mixin := FilterMixin prod_filter_filter.

Canonical prod_filtered := FilterType (T * U) (fT * fU) prod_filter_mixin.
End ProdFilter.

Section ProdPFilter.
Context {T U : pointedType} {fT : pfilterType T} {fU : pfilterType U}.

Lemma filter_prod_nontriv (x : fT * fU) : ~ \near x, False.
Proof.
move=> [[/= X Y] [Xx Yx]]; rewrite subset0; apply/eqP; rewrite set0P.
near x.1 => x1; near x.2 => x2.
by exists (x1, x2); split => /=; [near: x1|near: x2].
Grab Existential Variables. all: by end_near. Qed.

Definition prod_pfilter_mixin := PFilterMixin filter_prod_nontriv.

Canonical prod_pfiltered := PFilterType (T * U) (fT * fU) prod_pfilter_mixin.
End ProdPFilter.

Definition uncurry X Y Z (f : X -> Y -> Z) xy := f xy.1 xy.2.
Arguments uncurry : simpl never.

Definition uncurry_dep X Y Z (f : forall x : X, forall y : Y, Z x y) xy :=
   f xy.1 xy.2.
Arguments uncurry_dep : simpl never.

Definition uncurry_sig X Y Z (f : forall x : X, forall y : Y x, Z x y) xy :=
   f (projT1 xy) (projT2 xy).
Arguments uncurry_sig : simpl never.

Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P" :=
  ((nbhs (x_0, y_0)) (uncurry (fun x y => P)))
  (at level 200, x ident, y ident, P at level 200,
   format "'\forall'  x  '\near'  x_0  &  y  '\near'  y_0 ,  P") : type_scope.
Notation "'\forall' x & y '\near' z , P" :=
  (\forall x \near z & y \near z, P)
  (at level 200, x ident, y ident, P at level 200,
   format "'\forall'  x  &  y  '\near'  z ,  P") : type_scope.
Notation "'\near' x & y , P" := (\forall x \near x & y \near y, P)
  (at level 200, x, y at level 99, P at level 200, format "'\near'  x  &  y ,  P", only parsing) : type_scope.

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X} {fX : filterType X} (x : fX)
   P (phP : ph {all1 P}) := (nbhs x) P.

Definition prop_near2 {X X'} {fX : filterType X} {fX' : filterType X'}
  (x : fX) (x' : fX') := fun P of ph {all2 P} =>
  (nbhs (x, x')) (fun x => P x.1 x.2).

End Near.

Notation "{ 'near' x , P }" := (@prop_near1 _ _ x _ (inPhantom P))
  (at level 0, format "{ 'near'  x ,  P }") : type_scope.
Notation "{ 'near' x & y , P }" := (@prop_near2 _ _ _ _ x y _ (inPhantom P))
  (at level 0, format "{ 'near'  x  &  y ,  P }") : type_scope.
Arguments prop_near1 : simpl never.
Arguments prop_near2 : simpl never.

Lemma nbhsE {T : Type} (F : {filter T}) : (nbhs F) = F :> set (set T).
Proof. by []. Qed.

Lemma near_simpl {T : Type} (F : {filter T}) :
  (nbhs (nbhs F) = nbhs F)%type.
Proof. by []. Qed.

Definition flim {T : Type} (F G : set (set T)) := G `<=` F.
Notation "F `=>` G" := (flim F G) : classical_set_scope.
Lemma flim_refl T (F : set (set T)) : F `=>` F.
Proof. exact. Qed.

Lemma flim_trans T (G F H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Notation "F --> G" := (flim (in_nbhs (nbhs F)) (in_nbhs (nbhs G)))
  (at level 70, format "F  -->  G") : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filterType U) :=
  fun F : set (set U) => get (fun l : T => F `=>` nbhs l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T F)
  (format "[ 'lim'  F  'in'  T ]") : classical_set_scope.
Notation lim F := [lim F in [filterType _ of type_of_filter F]].
Notation "[ 'cvg' F 'in' T ]" := (F `=>` nbhs [lim F in T])
  (format "[ 'cvg'  F  'in'  T ]") : classical_set_scope.
Notation cvg F := [cvg F in [filterType _ of type_of_filter F]].

Section is_filteredTheory.

Lemma flim_prod T (x y l k : {filter T}) :
  x --> l -> y --> k -> (x, y) --> (l, k).
Proof.
move=> xl yk X [[X1 X2] /= [HX1 HX2] H]; exists (X1, X2) => //=.
by split; [exact: xl | exact: yk].
Qed.

Lemma cvg_ex {U : Type} (T : filterType U) (F : set (set U)) :
  [cvg F in T] <-> (exists l : T, F `=>` nbhs l).
Proof. by split=> [cvg|/getPex//]; exists [lim F in T]. Qed.

Lemma cvgP {U : Type} (T : filterType U) (F : set (set U)) (l : T) :
   F `=>` nbhs l -> [cvg F in T].
Proof. by move=> Fl; apply/cvg_ex; exists l. Qed.

Lemma dvgP {U : Type} (T : filterType U) (F : set (set U)) :
  ~ [cvg F in T] -> [lim F in T] = point.
Proof. by rewrite /lim_in /=; case xgetP. Qed.

(* CoInductive cvg_spec {U : Type} (T : filterType U) (F : set (set U)) : *)
(*    U -> Prop -> Type := *)
(* | HasLim  of F --> [lim F in T] : cvg_spec T F [lim F in T] True *)
(* | HasNoLim of ~ [cvg F in U] : cvg_spec F point False. *)

(* Lemma cvgP (F : set (set U)) : cvg_spec F (lim F) [cvg F in U]. *)
(* Proof. *)
(* have [cvg|dvg] := pselect [cvg F in U]. *)
(*   by rewrite (propT cvg); apply: HasLim; rewrite -cvgE. *)
(* by rewrite (propF dvg) (dvgP _) //; apply: HasNoLim. *)
(* Qed. *)

End is_filteredTheory.

Lemma near2_curry {U V} (F : {filter U}) (G : {filter V}) (P : U -> set V) :
  {near F & G, forall x y, P x y} = {near (F, G), forall x, P x.1 x.2}.
Proof. by []. Qed.

Lemma near2_pair {U V} (F : {filter U}) (G : {filter V}) (P : set (U * V)) :
  {near F & G, forall x y, P (x, y)} = {near (F, G), forall x, P x}.
Proof. by rewrite near2_curry; congr {near _, _}; rewrite predeqE => -[]. Qed.

Definition near2E := (@near2_curry, @near2_pair).

Lemma near_swap {U V} (F : {filter U}) (G : {filter V}) (P : U -> set V) :
  (\forall x \near F & y \near G, P x y) = (\forall y \near G & x \near F, P x y).
Proof.
rewrite propeqE; split => -[[/=A B] [FA FB] ABP];
by exists (B, A) => // -[x y] [/=Bx Ay]; apply: (ABP (y, x)).
Qed.


Lemma filter_not_empty_ex {T : Type} (F : set (set T)) :
    (forall P, F P -> exists x, P x) -> ~ \near F, False.
Proof. by move=> /(_ set0) ex /ex []. Qed.

Definition Build_is_pfilter {T : Type} (F : set (set T))
  (near_ex : forall P, F P -> exists x, P x)
  (filter_filter : is_filter F) :=
  Build_is_pfilter' (filter_not_empty_ex near_ex) (filter_filter).

Lemma filter_bigI {T} {fT : filterType T} (I : choiceType)
  (D : {fset I}) (f : I -> set T) (F : fT) :
  (forall i, i \in D -> nbhs F (f i)) ->
  nbhs F (\bigcap_(i in [set i | i \in D]) f i).
Proof.
move=> FfD.
suff: nbhs F [set p | forall i, i \in enum_fset D -> f i p] by [].
have {FfD} : forall i, i \in enum_fset D -> nbhs F (f i) by move=> ? /FfD.
elim: (enum_fset D) => [|i s ihs] FfD; first exact: nearS (nearT _).
apply: (@nearS _ _ _ (f i `&` [set p | forall i, i \in s -> f i p])).
  by move=> p [fip fsp] j; rewrite inE => /orP [/eqP->|] //; apply: fsp.
apply: nearI; first by apply: FfD; rewrite inE eq_refl.
by apply: ihs => j sj; apply: FfD; rewrite inE sj orbC.
Qed.

Lemma near T (F : set (set T)) P (FP : F P) (x : T)
  (Px : prop_of (FilterElt FP) x) : P x.
Proof. by move: Px; rewrite prop_ofE. Qed.
Arguments near {T F P} FP x Px.


Section NearTheorems.
Context {T : Type} {fT : filterType T}.
Implicit Type (F : fT).

Lemma nearE {x : fT} {P : set T} : (forall x, P x) -> \near x, P x.
Proof. by move=> ?; near=> x0. Unshelve. end_near. Qed.

Lemma near_app {F} (P Q : set T) :
   (\forall x \near F, P x -> Q x) -> (nbhs F) P -> (nbhs F) Q.
Proof. by move=> subPQ FP; near=> x; suff: P x; near: x.
Grab Existential Variables. by end_near. Qed.

Lemma near_app2 {F} :
  forall P Q R : set T,  nbhs F (fun x => P x -> Q x -> R x) ->
  nbhs F P -> nbhs F Q -> nbhs F R.
Proof. by move=> ? ? ? PQR FP; apply: near_app; apply: near_app FP. Qed.

Lemma near_app3 {F} :
  forall P Q R S : set T, nbhs F (fun x => P x -> Q x -> R x -> S x) ->
  nbhs F P -> nbhs F Q -> nbhs F R -> nbhs F S.
Proof. by move=> ? ? ? ? PQR FP; apply: near_app2; apply: near_app FP. Qed.

Lemma nearS2 {F} :
  forall P Q R : set T, (forall x, P x -> Q x -> R x) ->
  nbhs F P -> nbhs F Q -> nbhs F R.
Proof. by move=> ? ? ? ?; apply/near_app2/nearE. Qed.

Lemma nearS3 {F} :
  forall P Q R S : set T, (forall x, P x -> Q x -> R x -> S x) ->
  nbhs F P -> nbhs F Q -> nbhs F R -> nbhs F S.
Proof. by move=> ? ? ? ? ?; apply/near_app3/nearE. Qed.

End NearTheorems.
Arguments nearE {T fT x P}.

Section Near2Theorems.
Context {I T U : nonPropType} {fT : filterType T} {fU : filterType U}.
Implicit Type (F : fT).

Lemma near_andP {F} (b1 b2 : T -> Prop) :
  (\forall x \near F, b1 x /\ b2 x) <->
    (\forall x \near F, b1 x) /\ (\forall x \near F, b2 x).
Proof.
split=> [H|[H1 H2]]; first by split; move: H; apply: nearS => ? [].
by apply: nearS2 H1 H2.
Qed.

Lemma nearP_dep {F : fT} {G : fU} (P : T -> U -> Prop) :
  (\forall x \near F & y \near G, P x y) ->
  \forall x \near F, \forall y \near G, P x y.
Proof.
move=> [[Q R] [/=FQ GR]] QRP.
by apply: nearS FQ => x Q1x; apply: nearS GR => y Q2y; apply: (QRP (_, _)).
Qed.

Lemma near2P (F : fT) (G : fU) (P : set (T * U)) :
  (exists2 Q : set T * set U, nbhs F Q.1 /\ nbhs G Q.2
     & forall (x : T) (y : U), Q.1 x -> Q.2 y -> P (x, y))
   <-> \forall x \near (F, G), P x.
Proof.
split=> [][[A B] /=[FA GB] ABP]; exists (A, B) => //=.
  by move=> [a b] [/=Aa Bb]; apply: ABP.
by move=> a b Aa Bb; apply: (ABP (_, _)).
Qed.

Lemma in_filter_from (D : set I) (B : I -> set T) (i : I) :
   D i -> filter_from D B (B i).
Proof. by exists i. Qed.

Lemma filter_fromP (D : set I) (B : I -> set T) (F : fT) :
  F --> filter_from D B <-> forall i, D i -> nbhs F (B i).
Proof.
split; first by move=> FB i ?; apply/FB/in_filter_from.
by move=> FB P [i Di BjP]; apply: (nearS BjP); apply: FB.
Qed.

Lemma filter_fromTP (B : I -> set T) (F : fT) :
  nbhs F `=>` filter_from setT B <-> forall i, nbhs F (B i).
Proof. by rewrite filter_fromP; split=> [P i|P i _]; apply: P. Qed.

Lemma filter_from_proper (D : set I) (B : I -> set T) :
  is_filter (filter_from D B) ->
  (forall i, D i -> B i !=set0) ->
  is_pfilter (filter_from D B).
Proof.
move=> FF BN0; apply: Build_is_pfilter => // P [i Di BiP].
by have [x Bix] := BN0 _ Di; exists x; apply: BiP.
Qed.

End Near2Theorems.

Lemma near_ex2 {T U : nonPropType} {fT : pfilterType T} {fU : pfilterType U}
  (F : fT) (G : fU) (P : set T) (Q : set U) :
   nbhs F P -> nbhs G Q -> exists x : T, exists2 y : U, P x & Q y.
Proof. by move=> /near_ex [x Px] /near_ex [y Qy]; exists x, y. Qed.

(** ** Limits expressed with filters *)

Definition filtermap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].
Arguments filtermap _ _ _ _ _ /.

Lemma filtermapE {U V : Type} (f : U -> V)
  (F : set (set U)) (P : set V) : filtermap f F P = F (f @^-1` P).
Proof. by []. Qed.

Notation "E @[ x --> F ]" := (filtermap (fun x => E) (in_nbhs (nbhs F)))
  (at level 60, x ident, format "E  @[ x  -->  F ]") : classical_set_scope.
Notation "f @ F" := (filtermap f (in_nbhs (nbhs F)))
  (at level 60, format "f  @  F") : classical_set_scope.

Canonical filtermap_set_set T U (f : T -> U) (F : {nbhs T}) :=
  Nbhs (f @ F).

Lemma filtermap_is_filter T U (f : T -> U) (F : {filter T}) : is_filter (f @ F).
Proof.
constructor => [|P Q|P Q PQ]; rewrite ?filtermapE ?filter_ofE //=.
- exact: nearT.
- exact: nearI.
- by apply: nearS=> ?/PQ.
Qed.

Canonical filtermap_filter T U (f : T -> U) (F : {filter T}) :=
  Filter (f @ F) (filtermap_is_filter f F).

Lemma filtermap_is_not_empty {T : pointedType} {U : Type}
   (f : T -> U) (F : {pfilter T}) : ~ \forall _ \near f @ F, False.
Proof. exact: filter_not_empty. Qed.
Arguments filtermap_is_not_empty {T U} f F.

Canonical filtermap_pfilter {T : pointedType} U (f : T -> U) (F : {pfilter T}) :=
  PFilter (f @ F) (filtermap_is_not_empty f F).

Definition filtermapi {T U : Type} (f : T -> set U) (F : set (set T)) : set (set U) :=
  [set P | \forall x \near F, exists y, f x y /\ P y].

Notation "E `@[ x --> y ]" := (filtermapi (fun x => E) y)
  (at level 60, x ident, format "E  `@[ x  -->  y ]") : classical_set_scope.
Notation "f `@ x" := (filtermapi f (in_nbhs (nbhs x)))
  (at level 60, format "f  `@  x") : classical_set_scope.

Canonical filtermapi_set_set T U (f : T -> U -> Prop) (F : {nbhs T}) :=
  Nbhs (f `@ F).

Lemma filtermapiE {U V : Type} (f : U -> set V)
  (F : {filter U}) (P : set V) :
  filtermapi f F P = \forall x \near F, exists y, f x y /\ P y.
Proof. by []. Qed.

Lemma filtermapi_is_filter {T U} {fT : filterType T} (f : T -> set U) (F : fT) :
  {near F, is_totalfun f} -> is_filter (f `@ F).
Proof.
move=> f_totalfun; rewrite /filtermapi; apply: Build_is_filter. (* bug *)
- by apply: nearS f_totalfun => x [[y Hy] H]; exists y.
- move=> P Q FP FQ; near=> x.
    have [//|y [fxy Py]] := near FP x.
    have [//|z [fxz Qz]] := near FQ x.
    have [//|_ fx_prop] := near f_totalfun x.
    by exists y; split => //; split => //; rewrite [y](fx_prop _ z).
- move=> P Q subPQ FP; near=> x.
  by have [//|y [fxy /subPQ Qy]] := near FP x; exists y.
Grab Existential Variables. all: end_near. Qed.

Lemma near_map {T U} {fT : filterType T} (f : T -> U) (F : fT) (P : set U) :
  (\forall x \near f @ F, P x) = (\forall x \near F, P (f x)).
Proof. by []. Qed.

Lemma near_map2 {T T' U U'} {fT : filterType T} {fT' : filterType T'}
    (f : T -> U) (g : T' -> U')
    (F : fT) (G : fT') (P : U -> set U') :
  (\forall y \near f @ F & y' \near g @ G, P y y') =
  (\forall x \near F     & x' \near G     , P (f x) (g x')).
Proof.
rewrite propeqE; split=> -[[A B] /= [fFA fGB] ABP].
  exists (f @^-1` A, g @^-1` B) => //= -[x y /=] xyAB.
  by apply: (ABP (_, _)); apply: xyAB.
exists (f @` A, g @` B) => //=; last first.
  by move=> -[a1 a2] [/= [x Ax <-] [x' Bx' <-]]; apply: (ABP (_, _)).
split; first by apply: nearS fFA=> x Ax; exists x.
by apply: nearS fGB => x Bx; exists x.
Qed.

Lemma near_mapi {T U} {fT : filterType T} (f : T -> set U) (F : fT) (P : set U) :
  nbhs (f `@ F) P = (\forall x \near F, exists y, f x y /\ P y).
Proof. by []. Qed.

Lemma complete_fun_subproof
  {T : pointedType} {U : choiceType} (F : {pfilter T})
  (f : T -> U -> Prop) : {near F, is_totalfun f} ->
  {g : T -> U | \forall t \near F, f t = eq (g t)}.
Proof.
move=> fF; suff: exists g, `[<\forall t \near F, f t = eq (g t)>].
  by move=> /sigW[g]; exists g; apply/asboolP.
have [x0 [[y0 fxy0 fx0P]]] := near_ex fF.
exists (fun x => xget y0 (f x)); apply/asboolP; near=> t.
rewrite predeqE => u; have [|[v ftv] ftP]// := near fF t.
by case: xgetP => [x -> ftx|/(_ v)//]; split=> [/(ftP _ _ ftx)|<-].
Grab Existential Variables. all: end_near. Qed.

Definition complete_fun 
  {T : pointedType} {U : choiceType} (F : {pfilter T})
  (f : T -> U -> Prop) (fFtotal : {near F, is_totalfun f}) : T -> U
  := projT1 (complete_fun_subproof fFtotal).

Definition complete_funE
  {T : pointedType} {U : choiceType} (F : {pfilter T})
  (f : T -> U -> Prop) (fFtotal : {near F, is_totalfun f}) :
  \forall t \near F, f t = eq (complete_fun fFtotal t)
 := projT2 (complete_fun_subproof fFtotal).

Lemma neareqE T (F G : {nbhs T}) :
  (nbhs F = nbhs G :> set _) = (forall P, nbhs F P <-> nbhs G P).
Proof. by rewrite predeqE propeqE; split => []. Qed.

Lemma filtermapi_complete
  {T : pointedType} {U : choiceType} (F : {pfilter T})
  (f : T -> U -> Prop) (fFtotal : {near F, is_totalfun f}) :
  f `@ F = complete_fun fFtotal @ F.
Proof.
rewrite neareqE => x /=; split; rewrite near_mapi near_map => Fx; near=> t.
  have [//|u [ftu xu]] := near Fx t.
  by move: ftu; rewrite (near (complete_funE fFtotal) t)// => ->.
exists (complete_fun fFtotal t); split; last by near: t.
by rewrite (near (complete_funE fFtotal) t).
Grab Existential Variables. all: end_near. Qed.

Lemma filtermapi_proper_filter
  {T U : pointedType} (f : T -> U -> Prop) (F : {pfilter T}) :
  {near F, is_totalfun f} -> is_pfilter (f `@ F).
Proof.
move=> fFtotal; rewrite (filtermapi_complete fFtotal).
exact: pfilter_on_is_pfilter.
Qed.

Section FlimTheory.
Context {T U V : Type} {fT : filterType T}.

Lemma flim_id (y : set (set T)) : id @ y `=>` y.
Proof. exact. Qed.

Lemma fappE  (f : U -> V) (F : set (set U)) :
  f @ F = [set P : set _ | \forall x \near F, P (f x)].
Proof. by []. Qed.

Lemma flim_app  (F G : set (set U)) (f : U -> V) :
  F --> G -> f @ F `=>` f @ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma flimi_app (F G : set (set U)) (f : U -> set V) :
  F --> G -> f `@ F `=>` f `@ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma flim_comp (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Proof. by move=> fFG gGH; apply: flim_trans gGH => P /fFG. Qed.

Lemma flimi_comp (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` nbhs G -> g `@ G `=>` nbhs H -> g \o f `@ F `=>` nbhs H.
Proof. by move=> fFG gGH; apply: flim_trans gGH => P /fFG. Qed.

Lemma flim_eq_loc {F : fT} (f g : T -> U) :
  {near F, f =1 g} -> g @ F `=>` f @ F.
Proof. by move=> eq_fg P /=; apply: nearS2 eq_fg => x <-. Qed.

Lemma flimi_eq_loc {F : fT} (f g : T -> set U) :
  {near F, f =2 g} -> g `@ F `=>` f `@ F.
Proof.
move=> eq_fg P /=; apply: nearS2 eq_fg => x eq_fg [y [fxy Py]].
by exists y; rewrite -eq_fg.
Qed.

End FlimTheory.

(** ** Specific filters *)

Section at_point.

Context {T : Type}.

Definition at_point (a : T) (P : set T) : Prop := P a.

Lemma at_point_filter (a : T) : is_pfilter (at_point a).
Proof. by constructor=> //; constructor=> // P Q subPQ /subPQ. Qed.

End at_point.

(** is_filters for pairs *)

Lemma filter_prod1 {T U} {F : {filter T}} {G : {filter U}} (P : set T) :
  (\forall x \near F, P x) -> \forall x \near F & _ \near G, P x.
Proof.
move=> FP; exists (P, setT)=> //= [|[? ? []//]].
by split=> //; apply: nearT.
Qed.

Lemma filter_prod2 {T U} {F : {filter T}} {G : {filter U}} (P : set U) :
  (\forall y \near G, P y) -> \forall _ \near F & y \near G, P y.
Proof.
move=> FP; exists (setT, P)=> //= [|[? ? []//]].
by split=> //; apply: nearT.
Qed.

Program Definition filter_elt_prod {T U} {F : {filter T}} {G : {filter U}}
  (P : filter_elt F) (Q : filter_elt G) : filter_elt (nbhs (F, G)) :=
  @FilterElt _ _ (fun x => prop_of P x.1 /\ prop_of Q x.2) _.
Next Obligation.
by exists (prop_of P, prop_of Q) => //=; split; apply: prop_ofP.
Qed.

Lemma near_pair {T U} {F : {filter T}} {G : {filter U}}
      {FF : is_filter F} {FG : is_filter G}
      (P : filter_elt F) (Q : filter_elt G) x :
       prop_of P x.1 -> prop_of Q x.2 -> prop_of (filter_elt_prod P Q) x.
Proof. by case: x=> x y; do ?rewrite prop_ofE /=; split. Qed.

Lemma flim_fst {T U} (F : {filter T}) (G : {filter U}) :
  (@fst T U) @ (F, G) `=>` nbhs F.
Proof. move=> P; apply: filter_prod1. Qed.

Lemma flim_snd {T U} (F : {filter T}) (G : {filter U}) :
  nbhs ((@snd T U) @ (F, G)) `=>` nbhs G.
Proof. by move=> P; apply: filter_prod2. Qed.

(* Lemma nearSpair (T T' : Type) (F : {filter T}) (F' : set (set T')) : *)
(*    is_filter F -> is_filter F' -> *)
(*    forall (P : set T) (P' : set T') (Q : set (T * T')), *)
(*    (forall x x', P x -> P' x' -> Q (x, x')) -> F P /\ F' P' -> *)
(*    filter_prod F F' Q. *)
(* Proof. *)
(* move=> FF FF' P P' Q PQ [FP FP']; near=> x. *)
(* have := PQ x.1 x.2; rewrite -surjective_pairing; apply; near: x; *)
(* by [apply: flim_fst|apply: flim_snd]. *)
(* Grab Existential Variables. all: end_near. Qed. *)

Lemma filter_pair_near_of (T T' : Type) (F : {filter T}) (F' : {filter T'}) :
   forall (P : @filter_elt T F) (P' : @filter_elt T' F') (Q : set (T * T')),
   (forall x x', prop_of P x -> prop_of P' x' -> Q (x, x')) ->
  (nbhs (F, F')) Q.
Proof.
move=> [P FP] [P' FP'] Q PQ; rewrite prop_ofE in FP FP' PQ.
near=> x; have := PQ x.1 x.2; rewrite -surjective_pairing; apply; near: x;
by [apply: flim_fst|apply: flim_snd].
Grab Existential Variables. all: end_near. Qed.

Tactic Notation "near=>" ident(x) ident(y) :=
  (apply: filter_pair_near_of => x y ? ?).
Tactic Notation "near" constr(F) "=>" ident(x) ident(y) :=
  apply: (near_const F); near=> x y.

Module Export NearMap.
Definition near_simpl := (@near_simpl, @near_map, @near_mapi, @near_map2).
Ltac near_simpl := rewrite /= ?near_simpl /=.
End NearMap.

Lemma nearN {T} {pfT : pfilterType T} (F : pfT) P : (* the converse impplication is for ultra filters *)
 (\forall x \near F, ~ P x) -> ~ \forall x \near F, P x.
Proof.
move=> FPN NFP; apply: (near_const F).
by apply: nearS2 FPN NFP => x Px/Px.
Qed.

Section NearPair.
Context {T U V W : nonPropType}.
Context {fT : filterType T} {fU : filterType U} {fV : filterType V} {fW : filterType W}.

Lemma flim_pair {F : fT} {G : fU} {H : fV} (f : T -> U) (g : T -> V) :
  f @ F `=>` nbhs G -> g @ F `=>` nbhs H -> (f x, g x) @[x --> F] `=>` nbhs (G, H).
Proof.
move=> fFG gFH /= P [[/=A B] [GA HB] ABP]; rewrite near_map; near=> x.
by apply: ABP; split=> /=; near: x; [apply: fFG|apply: gFH].
Grab Existential Variables. all: end_near. Qed.

Lemma flim_comp2 {F : fT} {G : fU} {H : fV} {I : fW}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F `=>` nbhs G -> g @ F `=>` nbhs H ->
  h (fst x) (snd x) @[x --> (G, H)] `=>` nbhs I ->
  h (f x) (g x) @[x --> F] `=>` nbhs I.
Proof. by move=> fFG gFH hGHI P /= IP; apply: flim_pair (hGHI _ IP). Qed.

End NearPair.
Arguments flim_comp2 {T U V W fT fU fV fW F G H I f g h} _ _ _.

(** Restriction of a filter to a domain *)

Section Within.
Context {T : Type} {fT : filterType T}.
Implicit Types (A D P : set T) (F : fT).

Definition within D F P := {near F, D `<=` P}.
Arguments within : simpl never.

Lemma near_withinE D F P :
  (\forall x \near within D F, P x) = {near F, D `<=` P}.
Proof. by []. Qed.

Lemma withinT D F : within D F D.
Proof. by rewrite /within; apply: nearE. Qed.

Lemma near_withinT D F  : \forall x \near within D F, D x.
Proof. exact: withinT. Qed.

Lemma within_filter D F : is_filter (within D F).
Proof.
rewrite /within; constructor.
- by apply: nearE.
- by move=> P Q; apply: nearS2 => x DP DQ Dx; split; [apply: DP|apply: DQ].
- by move=> P Q subPQ; apply: nearS => x DP /DP /subPQ.
Qed.

Canonical within_filterType D F :=
 Filter (within D F) (within_filter _ _).

Lemma flim_within D F : within D F --> F.
Proof. by move=> P; apply: nearS. Qed.

Definition subset_filter D F :=
  [set P : set {x | D x} | \forall x \near F, forall Dx : D x, P (exist _ x Dx)].
Arguments subset_filter D F _ : clear implicits.

Lemma subset_filter_filter D F : is_filter (subset_filter D F).
Proof.
constructor; rewrite /subset_filter.
- exact: nearE.
- by move=> P Q; apply: nearS2=> x PD QD Dx; split.
- by move=> P Q subPQ; apply: nearS => R PD Dx; apply: subPQ.
Qed.

Lemma subset_filter_proper D F :
  (forall P, nbhs F P -> ~ ~ exists x, D x /\ P x) ->
  is_pfilter (subset_filter D F).
Proof.
move=> DAP; apply: Build_is_pfilter'; last exact: subset_filter_filter.
rewrite /subset_filter => subFD.
by have /(_ subFD) := DAP (~` D); apply => -[x [dx /(_ dx)]].
Qed.

End Within.

(** * Topological spaces *)

Module Topological.

Record mixin_of (T : Type) (nbhs : T -> set (set T)) := Mixin {
  open : set (set T);
  ax2 : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A]] ;
  ax3 : open = [set A : set T | A `<=` nbhs^~ A ]
}.

Record class_of (T : Type) := Class {
  base : PFilter.class_of T T;
  mixin : mixin_of (Nbhs.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> PFilter.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack loc (m : @mixin_of T loc) :=
  fun bT (b : PFilter.class_of T T) of phant_id (@PFilter.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Nbhs.nbhs_op b)) =>
  @Pack T (@Class _ b m') T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition nbhsType := @Nbhs.Pack cT cT xclass.
Definition filterType := @Filter.Pack cT cT xclass.
Definition pfilterType := @PFilter.Pack cT cT xclass.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> PFilter.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion nbhsType : type >-> Nbhs.type.
Canonical nbhsType.
Coercion filterType : type >-> Filter.type.
Canonical filterType.
Coercion pfilterType : type >-> PFilter.type.
Canonical pfilterType.
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

Definition neigh (p : T) (A : set T) := open A /\ A p.

Lemma open_nbhsE (p : T) :
  (nbhs p) = 
  [set A : set T | exists B : set T, neigh p B /\ B `<=` A] :> set _.
Proof.
have -> : (nbhs p) = [set A : set T | exists B, [/\ open B, B p & B `<=` A]] :> set _.
  exact: Topological.ax2.
by rewrite predeqE => A; split=> [[B [?]]|[B [[]]]]; exists B.
Qed.

Definition interior (A : set T) : set T := [set x | (nbhs x) A].

Local Notation "A ^°" := (interior A).

Lemma interior_subset (A : set T) : A^° `<=` A.
Proof.
by move=> p; rewrite /interior open_nbhsE => -[? [[? ?]]]; apply.
Qed.

Lemma openE : open = [set A : set T | A `<=` A^°].
Proof. exact: Topological.ax3. Qed.

Lemma nbhs_singleton (p : T) (A : set T) : (nbhs p) A -> A p.
Proof. by rewrite open_nbhsE => - [? [[_ ?]]]; apply. Qed.

Lemma nbhs_interior (p : T) (A : set T) : (nbhs p) A -> (nbhs p) A^°.
Proof.
rewrite open_nbhsE /neigh openE => - [B [[Bop Bp] sBA]].
exists B; split=> // q Bq; rewrite /interior.
by near=> x; apply: sBA; near: x; apply: Bop.
Grab Existential Variables. all: end_near. Qed.

Lemma open0 : open set0.
Proof. by rewrite openE. Qed.

Lemma openT : open setT.
Proof. by rewrite openE => ? ?; apply: nearT. Qed.

Lemma openI (A B : set T) : open A -> open B -> open (A `&` B).
Proof.
rewrite openE => Aop Bop p [Ap Bp].
by apply: nearI; [apply: Aop|apply: Bop].
Qed.

Lemma open_bigU (I : Type) (D : set I) (f : I -> set T) :
  (forall i, D i -> open (f i)) -> open (\bigcup_(i in D) f i).
Proof.
rewrite openE => fop p [i Di].
by have /fop fiop := Di; move/fiop; apply: nearS => ? ?; exists i.
Qed.

Lemma openU (A B : set T) : open A -> open B -> open (A `|` B).
Proof.
by rewrite openE => Aop Bop p [/Aop|/Bop]; apply: nearS => ? ?; [left|right].
Qed.

Lemma open_subsetE (A B : set T) : open A -> (A `<=` B) = (A `<=` B^°).
Proof.
rewrite openE => Aop; rewrite propeqE; split.
  by move=> sAB p Ap; apply: nearS sAB _; apply: Aop.
by move=> sAB p /sAB /interior_subset.
Qed.

Lemma open_interior (A : set T) : open A^°.
Proof.
rewrite openE => p; rewrite /interior open_nbhsE => - [B [[Bop Bp]]].
by rewrite open_subsetE //; exists B.
Qed.

Lemma interior_bigcup I (D : set I) (f : I -> set T) :
  \bigcup_(i in D) (f i)^° `<=` (\bigcup_(i in D) f i)^°.
Proof.
move=> p [i Di]; rewrite /interior open_nbhsE => - [B [[Bop Bp] sBfi]].
by exists B; split=> // ? /sBfi; exists i.
Qed.

Lemma neighT (p : T) : neigh p setT.
Proof. by split=> //; apply: openT. Qed.

Lemma neighI (p : T) (A B : set T) :
  neigh p A -> neigh p B -> neigh p (A `&` B).
Proof. by move=> [Aop Ap] [Bop Bp]; split; [apply: openI|split]. Qed.

Lemma neigh_nbhs (p : T) (A : set T) : neigh p A -> (nbhs p) A.
Proof. by rewrite open_nbhsE => p_A; exists A; split. Qed.

End Topological1.

Notation "A ^°" := (interior A) : classical_set_scope.

Notation continuous f := (forall x, f%function @ x --> f%function x).

Lemma continuous_cst (S T : topologicalType) (a : T) :
  continuous (fun _ : S => a).
Proof.
move=> x A; rewrite !open_nbhsE => - [B [[_ Ba] sBA]].
by exists setT; split; [apply: neighT|move=> ? ?; apply: sBA].
Qed.

Lemma continuousP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, open A -> open (f @^-1` A).
Proof.
split=> fcont; first by rewrite !openE => A Aop ? /Aop /fcont.
move=> s A; rewrite !open_nbhsE => - [B [[Bop Bfs] sBA]].
by exists (f @^-1` B); split; [split=> //; apply/fcont|move=> ? /sBA].
Qed.

Lemma continuous_comp (R S T : topologicalType) (f : R -> S) (g : S -> T) x :
  {for x, continuous f} -> {for (f x), continuous g} ->
  {for x, continuous (g \o f)}.
Proof. exact: flim_comp. Qed.

Lemma open_comp  {T U : topologicalType} (f : T -> U) (D : set U) :
  {in f @^-1` D, continuous f} -> open D -> open (f @^-1` D).
Proof.
rewrite !openE => fcont Dop x /= Dfx.
by apply: fcont; [rewrite in_setE|apply: Dop].
Qed.

Lemma is_filter_lim_filtermap {T: topologicalType} {U : topologicalType}
  (F : {filter T}) x (f : T -> U) :
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
Grab Existential Variables. all: end_near. Qed.

(* limit composition *)

Lemma lim_cont {T : Type} {V U : topologicalType} {fT : filterType T} (F : fT)
  (f : T -> V) (h : V -> U) (a : V) :
  {for a, continuous h} ->
  f @ F --> a -> (h \o f) @ F --> h a.
Proof.
by move=> h_cont fa fb; apply: (flim_trans _ h_cont); apply: @flim_comp fa _.
Qed.

Lemma lim_cont2 {T : Type} {V W U : topologicalType} {fT : filterType T} (F : fT)
  (f : T -> V) (g : T -> W) (h : V -> W -> U) (a : V) (b : W) :
  h z.1 z.2 @[z --> (a, b)] --> h a b ->
  f @ F --> a -> g @ F --> b -> (fun x => h (f x) (g x)) @ F --> h a b.
Proof.
suff: False by [].
move: (fun z : V * W => h z.1 z.2) => uh.
move: (a, b) => ab.
evar (fU : filterType U).
evar (x : Filter.sort fU).
unify (in_nbhs (nbhs ?x)) (uh @ ab).

move=> hc fa fb; apply: flim_trans hc.
have := flim_comp2 fa fb.
move=> /(_ _ _ _ h)/=.
move: ((fun x : T => h (f x) (g x)) @ F) => G.
move: (fun z : V * W => h z.1 z.2) => uh.
move: (a, b) => ab.
nbhs ?s
uh @ ab
move=> /(_ _ _ (@flim_refl _ (nbhs (uh @ ab)))).
move=> XX.
Set Printing All.
apply XX.
apply.


rewrite /flim.
apply.
apply.

apply.
 apply: flim_comp2 fa fb _. Qed.
Admitted.

Lemma cst_continuous {T : Type} {T' : topologicalType} (k : T') (F : {filter T}) :
  (fun _ : T => k) @ F --> k.
Proof. move=> x /nbhs_singleton ?; apply: nearE. Admitted.
Arguments cst_continuous {T T'} k F.
Hint Resolve cst_continuous : core.

(** ** Topology defined by a filter *)

Section TopologyOfFilter.

Context {T : pointedType} {loc : T -> {filter T}}.
Hypothesis (loc_singleton : forall (p : T) (A : set T), loc p A -> A p).
Hypothesis (loc_loc : forall (p : T) (A : set T), loc p A -> loc p (loc^~ A)).

Definition open_of_nbhs := [set A : set T | A `<=` loc^~ A].

Program Definition topologyOfFilterMixin : Topological.mixin_of loc :=
  @Topological.Mixin T loc open_of_nbhs _ _.
Next Obligation.
rewrite predeqE => A; split=> [p_A|]; last first.
  by move=> [B [Bop Bp sBA]]; apply: nearS sBA _; apply: Bop.
exists (loc^~ A); split => //; do ?by move=> ?; apply: loc_loc.
by move=> // q /loc_singleton.
Qed.

End TopologyOfFilter.

(** ** Topology defined by open sets *)

Module OfOpen.
Section OfOpen.

Variable (T : pointedType).
Definition type : Type := T.
Variable (op : set type -> Prop).
Hypothesis (opT : op setT).
Hypothesis (opI : forall (A B : set type), op A -> op B -> op (A `&` B)).
Hypothesis (op_bigU : forall (I : Type) (f : I -> set type),
  (forall i, op (f i)) -> op (\bigcup_i f i)).

Canonical pointedType := [pointedType of type].

Definition nbhsMixin : Nbhs.mixin_of type type :=
   NbhsMixin (fun p => [set A | exists B, [/\ op B, B p & B `<=` A]]).
Canonical nbhsType := NbhsType type type nbhsMixin.

Lemma filterMixin : Filter.mixin_of [nbhsType type of type].
Proof.
constructor=> x; split; first by exists setT.  
  move=> A B [OA [OPop OAp OAA] [OB [OBop OBp OBB]]].
  by exists (OA `&` OB); split => //; [exact: opI|exact: subsetI2].
by move=> A B AB [OA [OPop OAp OAA]]; exists OA; split => // y /OAA /AB.
Qed.
Canonical filterType := FilterType type type filterMixin.

Lemma pfilterMixin : PFilter.mixin_of [filterType type of type].
Proof. by constructor => x; move=> [O [Oop Op]] /(_ _ Op). Qed.
Canonical pfilterType := PFilterType type type pfilterMixin.

Fact nbhs_of_openE : op = [set A : set type | A `<=` nbhs^~ A].
Proof.
rewrite predeqE => A; split=> [Aop p Ap|Aop].
  by exists A; split=> //; split.
suff -> : A = \bigcup_(B : {B : set type & op B /\ B `<=` A}) projT1 B.
  by apply: op_bigU => B; have [] := projT2 B.
rewrite predeqE => p; split=> [|[B _ Bp]]; last by have [_] := projT2 B; apply.
by move=> /Aop [B [Bop Bp sBA]]; exists (existT _ B (conj Bop sBA)).
Qed.

Definition topologyMixin : Topological.mixin_of (nbhs : type -> set (set type)) :=
  Topological.Mixin (fun=> erefl) nbhs_of_openE.
Canonical topologicalType := TopologicalType type topologyMixin.

End OfOpen.
End OfOpen.


Lemma bigcup1 (I R : Type) (i : I) (F : I -> set R) :
  \bigcup_(j in [set i]) F j = F i.
Proof. by rewrite predeqE => x; split=> [[j->//]|]; exists i. Qed.

Lemma in_nbhs_inj T : injective (@in_nbhs T).
Proof. by move=> [A] [B]; rewrite /in_nbhs => ->. Qed.

Notation flip f := (fun x y => f y x).
Definition imagei U V (f : U -> V -> Prop) (A : set U) : set V :=
  [set v | exists2 u, A u & f u v].
Definition preimagei U V (f : U -> V -> Prop) (B : set V) : set U :=
  imagei (flip f) B.

Lemma bigcup_image I J (f : I -> J -> Prop) R (F : J -> set R) (A : set I) :
  \bigcup_(j in imagei f A) F j = \bigcup_(i in A) \bigcup_(j in f i) F j.
Proof.
rewrite predeqE => x; split=> [[j [i Ai fij] Fjx]|[i Ai [j fij Fjx]]].
  by exists i => //; exists j.
by exists j => //; exists i.
Qed.

Lemma predeqP T (A B : set T) : (A = B) <-> (A `<=>` B).
Proof.
by rewrite predeqE; split=> [AB|[AB BA]]; split=> ? *; by [apply/AB|apply/BA].
Qed.

Lemma eq_bigcup I R (F G : I -> set R) (A B : set I) :
  A `<=>` B -> (forall x, A x -> F x = G x) -> 
  \bigcup_(i in A) F i = \bigcup_(i in B) G i.
Proof.
move=> /predeqP <- eqFG; rewrite predeqE=> x.
by split=> -[i Bi Pix]; exists i => //; rewrite ?eqFG// -?eqFG.
Qed.

Lemma eq_bigcupr I R (F G : I -> set R) (A : set I) :
  (forall x, A x -> F x = G x) -> 
  \bigcup_(i in A) F i = \bigcup_(i in A) G i.
Proof. by move=> /eq_bigcup; apply; split. Qed.

(** ** Topology defined by a base of open sets *)

Module OfBase.
Section OfBase.

Variable (I : Type) (T : pointedType) (D : set I) (b : I -> set T).
Definition type : Type := T.

Definition open_of : set (set type) :=
 [set A | exists E, E `<=` D /\ A = \bigcup_(i in E) b i].

Definition nbhs_of (p : type) : set (set type) :=
  [set A | exists i, [/\ D i, b i p & b i `<=` A]].

Canonical pointedType := [pointedType of type].

Definition nbhsMixin : Nbhs.mixin_of type type := NbhsMixin nbhs_of.
Canonical nbhsType := NbhsType type type nbhsMixin.

Hypothesis (b_cover : \bigcup_(i in D) b i = setT).
Hypothesis (b_join : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j]).

Fact geti (x : type) : exists2 i, D i & b i x.
Proof.
have: True by []; have /(congr1 (@^~ x))/= := b_cover; rewrite /setT => <-.
by move=> [i Di]; exists i.
Qed.

Lemma filterMixin : Filter.mixin_of [nbhsType type of type].
Proof.
constructor=> x; split.
  by have [i Di bix] := geti x; exists i.
move=> A B [i [Di bix biA]] [j [Dj bjx bjB]].
  have [||||k [Dk bkx bkij]] // := @b_join i j x.
  by exists k; split => //; apply: subset_trans bkij _; apply: subsetI2.
by move=> A B AB [i [Di bix biA]]; exists i; split => // y /biA /AB.
Qed.
Canonical filterType := FilterType type type filterMixin.

Lemma pfilterMixin : PFilter.mixin_of [filterType type of type].
Proof. by constructor => x; move=> [O [Oop Op]] /(_ _ Op). Qed.
Canonical pfilterType := PFilterType type type pfilterMixin.

Notation base_nbhs p := [set A | exists B, [/\ open_of B, B p & B `<=` A]].

Lemma nbhs_open (p : type) : nbhs p = base_nbhs p :> set _.
Proof.
rewrite predeqE => A; split => [[i [Di bip biA]]|[O [[E [ED ->]] Op OA]]].
  exists (b i); split => //; exists [set i].
  by split => [j ->//|]; rewrite bigcup1.
have [i Ei bip] := Op; exists i; split => //; first exact: ED.
by apply: subset_trans OA => q biq; exists i.
Qed.

Lemma op_bigU (J : Type) (f : J -> set type) :
  (forall i : J, open_of (f i)) -> open_of (\bigcup_i f i).
Proof.
move=> /choice [select selectP]; exists (imagei select setT).
split; first by move=> i [j _ sji]; have [/(_ _ sji)] := selectP j.
by rewrite bigcup_image; apply: eq_bigcupr => x _; have [] := selectP x.
Qed.

Fact nbhs_of_openE : open_of = [set A : set type | A `<=` nbhs^~ A].
Proof.
have -> : nbhs = fun p => Nbhs (base_nbhs p). (* reexpress [nbhs x | base_nbhs p] *)
  by rewrite funeqE=> U; apply: in_nbhs_inj; rewrite nbhs_open.
by apply: OfOpen.nbhs_of_openE; apply: op_bigU.
Qed.

Definition topologyMixin : Topological.mixin_of (nbhs : type -> set (set type)) :=
  Topological.Mixin nbhs_open nbhs_of_openE.
Canonical topologicalType := TopologicalType type topologyMixin.

End OfBase.
End OfBase.

(** ** Topology defined by a subbase of open sets *)

Definition finI_from (I : choiceType) T (D : set I) (f : I -> set T) :=
  [set \bigcap_(i in [set i | i \in D']) f i |
    D' in [set A : {fset I} | {subset A <= D}]].

Lemma finI_from_cover (I : choiceType) T (D : set I) (f : I -> set T) :
  \bigcup_(A in finI_from D f) A = setT.
Proof.
rewrite predeqE => t; split=> // _; exists setT => //.
by exists fset0 => //; rewrite predeqE.
Qed.

Lemma finI_from1 (I : choiceType) T (D : set I) (f : I -> set T) i :
  D i -> finI_from D f (f i).
Proof.
move=> Di; exists [fset i]%fset.
  by move=> ?; rewrite in_fsetE in_setE => /eqP->.
rewrite predeqE => t; split=> [|fit]; first by apply; rewrite in_fsetE.
by move=> ?; rewrite in_fsetE => /eqP->.
Qed.

Module OfSubbase.
Section OfSubbase.

Variable (I : choiceType) (T : pointedType) (sD : set I) (sb : I -> set T).
Definition type : Type := T.

Notation D := (finI_from sD sb).
Definition b := (@id (set T)).
Notation nbhs_of := (OfBase.nbhs_of D b).
Notation open_of := (OfBase.open_of D b).

Canonical pointedType := [pointedType of type].

Definition nbhsMixin : Nbhs.mixin_of type type := NbhsMixin nbhs_of.
Canonical nbhsType := NbhsType type type nbhsMixin.

Let b_cover : \bigcup_(i in D) b i = setT.
Proof. exact: finI_from_cover. Qed.

Let b_join : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof.
move=> _ _ x [A AsD <-] [B BsD <-] bAx bBx.
exists (\bigcap_(i in [set i | i \in (A `|` B)%fset]) sb i); split.
- by exists (A `|` B)%fset => // y; rewrite inE => /orP[/AsD|/BsD].
- by move=> y; rewrite inE => /orP[yA|yB]; [apply: bAx|apply: bBx].
- move=> y b_y; split.
    by move=> z zA; apply: b_y; rewrite inE zA.
  by move=> z zB; apply: b_y; rewrite inE zB orbT.
Qed.

Lemma filterMixin : Filter.mixin_of [nbhsType type of type].
Proof. by apply: OfBase.filterMixin; [apply: b_cover|apply: b_join]. Qed.
Canonical filterType := FilterType type type filterMixin.

Lemma pfilterMixin : PFilter.mixin_of [filterType type of type].
Proof. by have [P] := (OfBase.pfilterMixin b_cover b_join); exists. Qed.
Canonical pfilterType := PFilterType type type pfilterMixin.

Notation base_nbhs p := [set A | exists B, [/\ open_of B, B p & B `<=` A]].

Definition topologyMixin : Topological.mixin_of (nbhs : type -> set (set type)) :=
  Topological.Mixin (OfBase.nbhs_open D b) (OfBase.nbhs_of_openE D b).
Canonical topologicalType := TopologicalType type topologyMixin.

End OfSubbase.
End OfSubbase.


(** ** Topology on the product of two spaces *)

Section Prod_Topology.

Context {T U : topologicalType}.

Lemma prod_loc_singleton (p : T * U) (A : set (T * U)) : nbhs p A -> A p.
Proof.
by move=> [QR [/nbhs_singleton Qp1 /nbhs_singleton Rp2]]; apply.
Qed.

Lemma prod_loc_loc (p : T * U) (A : set (T * U)) :
  nbhs p A -> nbhs p (nbhs^~ A).
Proof.
move=> [QR [/nbhs_interior p1_Q /nbhs_interior p2_R] sQRA].
by exists (QR.1^°, QR.2^°) => // ? ?; exists QR.
Qed.

Definition prod_topologicalTypeMixin :=
  topologyOfFilterMixin prod_loc_singleton prod_loc_loc.

Canonical prod_topologicalType :=
  TopologicalType (T * U) prod_topologicalTypeMixin.

End Prod_Topology.

(** ** Topology on matrices *)

Section MatrixNbhsType.
Context (m n : nat) {T : Type} (fT : nbhsType T).

Definition mx_filter (mx : 'M[fT]_(m, n)) : set (set 'M[T]_(m,n)) :=
  filter_from [set P | forall i j, (nbhs (mx i j)) (P i j)]
              (fun P => [set my : 'M[T]_(m, n) | forall i j, P i j (my i j)]).

Definition mx_nbhs_mixin := NbhsMixin mx_filter.

Canonical mx_nbhs := NbhsType 'M[T]_(m,n) 'M[fT]_(m,n) mx_nbhs_mixin.
End MatrixNbhsType.

Section MatrixFilter.
Context (m n : nat) {T : Type} (fT : filterType T).

Lemma mx_filter_mixin :
  Filter.mixin_of [nbhsType 'M[T]_(m, n) of 'M[fT]_(m, n)].
Proof.
constructor=> /= M; apply: filter_from_filter => [|A B AM BM].
  by exists (fun _ _ => setT) => i j; apply: nearT.
exists (fun i j => A i j `&` B i j) => [i j|].
  by move: (AM i j) (BM i j); apply: nearS2.
by move=> M' ABM'; split=> i j; move: (ABM' i j) => [].
Qed.

Canonical mx_filtered := FilterType 'M[T]_(m,n) 'M[fT]_(m,n) mx_filter_mixin.
End MatrixFilter.

Section MatrixPFilter.
Context (m n : nat) {T : pointedType} (fT : pfilterType T).

Lemma mx_pfilter_mixin :
  PFilter.mixin_of [filterType 'M[T]_(m, n) of 'M[fT]_(m, n)].
Proof.
constructor=> /= M [A AF].
have /choice [f /(_ (_,_))/= fP] := fun ij => near_ex (uncurry_dep AF ij).
by move=> /(_ (\matrix_(i,j) f (i, j))); apply=> i j; rewrite mxE; apply: fP.
Qed.

Canonical mx_pfiltered := PFilterType 'M[T]_(m,n) 'M[fT]_(m,n) mx_pfilter_mixin.
End MatrixPFilter.

Section matrix_Topology.

Variables (m n : nat) (T : topologicalType).

Implicit Types M : 'M[T]_(m, n).

Lemma mx_loc_singleton M (A : set 'M[T]_(m, n)) : nbhs M A -> A M.
Proof. by move=> [P M_P]; apply=> ? ?; apply: nbhs_singleton. Qed.

Lemma mx_loc_loc M (A : set 'M[T]_(m, n)) :
  nbhs M A -> nbhs M (nbhs^~ A).
Proof.
move=> [P M_P sPA]; exists (fun i j => (P i j)^°).
  by move=> ? ?; apply: nbhs_interior.
by move=> ? ?; exists P.
Qed.

Definition matrix_topologicalTypeMixin :=
  topologyOfFilterMixin mx_loc_singleton mx_loc_loc.

Canonical matrix_topologicalType :=
  TopologicalType 'M[T]_(m, n) matrix_topologicalTypeMixin.

End matrix_Topology.

(** ** Weak topology by a function *)

Section Weak_Topology.

Definition weak_topology {S T : Type} (f : S -> T) := S.
Variable (S : pointedType) (T : topologicalType) (f : S -> T).

Notation fweak := (weak_topology f). 

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
  apply: open_bigU => i.
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
have g_preim i : g i = f @^-1` (get (opi i)).
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
rewrite predeqE => s; split=> [[i _]|[i _]]; last by rewrite g_preim; exists i.
by rewrite -[_ _]/((f @^-1` _) _) -g_preim; exists i.
Qed.

Canonical weak_pointedType := [pointedType of fweak].
Definition weak_nbhsMixin := OfOpen.nbhsMixin wopen.
Canonical weak_nbhsType := NbhsType fweak fweak weak_nbhsMixin. 
Definition weak_filterMixin := OfOpen.filterMixin wopT wopI.
Canonical weak_filterType := FilterType fweak fweak weak_filterMixin. 
Definition weak_pfilterMixin := OfOpen.pfilterMixin wopT wopI.
Canonical weak_pfilterType := PFilterType fweak fweak weak_pfilterMixin. 
Definition weak_topologyMixin := OfOpen.topologyMixin wop_bigU.
Canonical weak_topologyType := TopologicalType fweak weak_topologyMixin.

Lemma weak_continuous : continuous (f : fweak -> T).
Proof. by apply/continuousP => A ?; exists A. Qed.

Lemma flim_image (F : {filter S}) (s : fweak) :
  f @` setT = setT ->
  F --> s <-> [set f @` A | A in F] --> f s.
Proof.
move=> fsurj; split=> [cvFs|cvfFfs].
  move=> A /weak_continuous [B [Bop Bs sBAf]].
  have /cvFs FB: nbhs s B by apply: neigh_nbhs.
  exists (f @^-1` A); first exact: nearS FB.
  exact: image_preimage.
move=> A /= [_ [[B Bop <-]]/= Bfs sBfA].
have /cvfFfs [C FC fCeB] : nbhs (f s) B.
  by rewrite open_nbhsE; exists B; split.
apply: nearS FC.
by apply: subset_trans sBfA; rewrite -fCeB; apply: preimage_image.
Qed.

End Weak_Topology.

(** ** Supremum of a family of topologies *)

(* Section Sup_Topology. *)

(* Variable (T : pointedType) (I : Type) (Tc : I -> Topological.class_of T). *)

(* Let TS := fun i => Topological.Pack (Tc i) T. *)

(* Definition sup_subbase := \bigcup_i (@open (TS i) : set (set T)). *)

(* Definition sup_topologicalTypeMixin := OfSubbase.topologyMixin sup_subbase id. *)

(* Definition sup_topologicalType := Topological.Pack *)
(*   (@Topological.Class _ *)
(*     (@PFilter.Class _ _ *)
(*       (@Filter.Class _ _ *)
(*         (Nbhs.Class (Pointed.class T) _) _) _) *)
(*   sup_topologicalTypeMixin) T. *)

(* Lemma flim_sup (F : {filter T}) (t : T) : *)
(*   F --> (t : sup_topologicalType) <-> forall i, F --> (t : TS i). *)
(* Proof. *)
(* move=> Ffilt; split=> cvFt. *)
(*   move=> i A /=; rewrite (@nbhsE (TS i)) => - [B [[Bop Bt] sBA]]. *)
(*   apply: cvFt; exists B; split=> //; exists [set B]; last first. *)
(*     by rewrite predeqE => ?; split=> [[_ ->]|] //; exists B. *)
(*   move=> _ ->; exists [fset B]%fset. *)
(*     by move=> ?; rewrite in_fsetE in_setE => /eqP->; exists i. *)
(*   by rewrite predeqE=> ?; split=> [|? ?]; [apply|]; rewrite in_fsetE // =>/eqP->. *)
(* move=> A /=; rewrite (@nbhsE sup_topologicalType). *)
(* move=> [_ [[[B sB <-] [C BC Ct]] sUBA]]. *)
(* rewrite nbhs_filterE; apply: nearS sUBA _; apply: (@nearS _ _ _ C). *)
(*   by move=> ? ?; exists C. *)
(* have /sB [D sD IDeC] := BC; rewrite -IDeC; apply: filter_bigI => E DE. *)
(* have /sD := DE; rewrite in_setE => - [i _]; rewrite openE => Eop. *)
(* by apply: (cvFt i); apply: Eop; move: Ct; rewrite -IDeC => /(_ _ DE). *)
(* Qed. *)

(* End Sup_Topology. *)

(* (** ** Product topology *) *)

(* Section Product_Topology. *)

(* Variable (I : Type) (T : I -> topologicalType). *)

(* Definition dep_arrow_choiceClass := *)
(*   Choice.Class (Equality.class (dep_arrow_eqType T)) gen_choiceMixin. *)

(* Definition dep_arrow_pointedType := *)
(*   Pointed.Pack (Pointed.Class dep_arrow_choiceClass (fun i => @point (T i))) *)
(*   (forall i, T i). *)

(* Definition product_topologicalType := *)
(*   sup_topologicalType (fun i => Topological.class *)
(*     (weak_topologicalType (fun f : dep_arrow_pointedType => f i))). *)

(* End Product_Topology. *)

(** * The topology on natural numbers *)

(* :TODO: ultimately nat could be replaced by any lattice *)
Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Canonical eventually_filter_source X :=
   @Nbhs.Source X _ nat (NbhsMixin (fun f => f @ \oo)).

Definition eventually_filter : is_pfilter eventually.
Proof.
eapply @filter_from_proper; last by move=> i _; exists i.
apply: filter_fromT_filter; first by exists 0%N.
move=> i j; exists (maxn i j) => n //=.
by rewrite geq_max => /andP[ltin ltjn].
Qed.

(** nbhs' *)

(* Should have a generic ^' operator *)
Definition nbhs' {T : topologicalType} (x : T) :=
  within (fun y => y != x) (nbhs x).

Lemma nbhsE' (T : topologicalType) (x : T) :
  nbhs x = nbhs' x `&` at_point x.
Proof.
rewrite predeqE => A; split=> [x_A|[x_A Ax]].
  split; last exact: nbhs_singleton.
  move: x_A; rewrite nbhsE => -[B [x_B sBA]]; rewrite /nbhs' nbhsE.
  by exists B; split=> // ? /sBA.
move: x_A; rewrite /nbhs' !nbhsE => -[B [x_B sBA]]; exists B.
by split=> // y /sBA Ay; case: (eqVneq y x) => [->|].
Qed.

Global Instance nbhs'_filter {T : topologicalType} (x : T) :
  is_filter (nbhs' x).
Proof. exact: within_filter. Qed.
Typeclasses Opaque nbhs'.

Canonical nbhs'_filter_on (T : topologicalType)  (x : T) :=
  Filter (nbhs' x) (nbhs'_filter _).

(** ** Closed sets in topological spaces *)

Section Closed.

Context {T : topologicalType}.

Definition closure (A : set T) :=
  [set p : T | forall B, nbhs p B -> A `&` B !=set0].

Lemma subset_closure (A : set T) : A `<=` closure A.
Proof. by move=> p ? ?; exists p; split=> //; apply: nbhs_singleton. Qed.

Lemma closureI (A B : set T) : closure (A `&` B) `<=` closure A `&` closure B.
Proof. by move=> p clABp; split=> ? /clABp [q [[]]]; exists q. Qed.

Definition closed (D : set T) := closure D `<=` D.

Lemma closedC (D : set T) : open D -> closed (~` D).
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
Proof. by move=> ? /(_ setT) [|? []] //; apply: nearT. Qed.

Lemma closedE : closed = [set A : set T | forall p, ~ (\near p, ~ A p) -> A p].
Proof.
rewrite predeqE => A; split=> Acl p; last first.
  by move=> clAp; apply: Acl; rewrite -nbhs_nearE => /clAp [? []].
rewrite -nbhs_nearE nbhsE => /asboolP.
rewrite asbool_neg => /forallp_asboolPn clAp.
apply: Acl => B; rewrite nbhsE => - [C [p_C sCB]].
have /asboolP := clAp C.
rewrite asbool_neg asbool_and => /nandP [/asboolP//|/existsp_asboolPn [q]].
move/asboolP; rewrite asbool_neg => /imply_asboolPn [/sCB Bq /contrapT Aq].
by exists q.
Qed.

Lemma openC (D : set T) : closed D -> open (~` D).
Proof.
rewrite closedE openE => Dcl t nDt; apply: contrapT.
by rewrite /interior nbhs_nearE => /Dcl.
Qed.

Lemma closed_closure (A : set T) : closed (closure A).
Proof. by move=> p clclAp B /nbhs_interior /clclAp [q [clAq /clAq]]. Qed.

End Closed.

Lemma closed_comp {T U : topologicalType} (f : T -> U) (D : set U) :
  {in ~` f @^-1` D, continuous f} -> closed D -> closed (f @^-1` D).
Proof.
rewrite !closedE=> f_cont D_cl x /= xDf; apply: D_cl; apply: contrap xDf => fxD.
have NDfx : ~ D (f x).
  by move: fxD; rewrite -nbhs_nearE nbhsE => - [A [[? ?]]]; apply.
by apply: f_cont fxD; rewrite in_setE.
Qed.

Lemma closed_flim_loc {T} {U : topologicalType} {F} {FF : is_pfilter F}
  (f : T -> U) (D : U -> Prop) :
  forall y, f @ F --> y -> F (f @^-1` D) -> closed D -> D y.
Proof.
move=> y Ffy Df; apply => A /Ffy /=; rewrite nbhs_filterE.
by move=> /(nearI Df); apply: near_ex.
Qed.

Lemma closed_flim {T} {U : topologicalType} {F} {FF : is_pfilter F}
  (f : T -> U) (D : U -> Prop) :
  forall y, f @ F --> y -> (forall x, D (f x)) -> closed D -> D y.
Proof.
by move=> y fy FDf; apply: (closed_flim_loc fy); apply: filterE.
Qed.

(** ** Compact sets *)

Section Compact.

Context {T : topologicalType}.

Definition cluster (F : {filter T}) (p : T) :=
  forall A B, F A -> nbhs p B -> A `&` B !=set0.

Lemma clusterE F : cluster F = \bigcap_(A in F) (closure A).
Proof. by rewrite predeqE => p; split=> cF ? ? ? ?; apply: cF. Qed.

Lemma flim_cluster F G : F --> G -> cluster F `<=` cluster G.
Proof. by move=> sGF p Fp P Q GP Qp; apply: Fp Qp; apply: sGF. Qed.

Lemma cluster_flimE F :
  is_pfilter F ->
  cluster F = [set p | exists2 G, is_pfilter G & G --> p /\ F `<=` G].
Proof.
move=> FF; rewrite predeqE => p.
split=> [clFp|[G Gproper [cvGp sFG]] A B]; last first.
  by move=> /sFG GA /cvGp GB; apply: (@near_ex _ G); apply: nearI.
exists (filter_from (\bigcup_(A in F) [set A `&` B | B in nbhs p]) id).
  apply filter_from_proper; last first.
    by move=> _ [A FA [B p_B <-]]; have := clFp _ _ FA p_B.
  apply: filter_from_filter.
    exists setT; exists setT; first exact: nearT.
    by exists setT; [apply: nearT|rewrite setIT].
  move=> _ _ [A1 FA1 [B1 p_B1 <-]] [A2 FA2 [B2 p_B2 <-]].
  exists (A1 `&` B1 `&` (A2 `&` B2)) => //; exists (A1 `&` A2).
    exact: nearI.
  by exists (B1 `&` B2); [apply: nearI|rewrite setIACA].
split.
  move=> A p_A; exists A => //; exists setT; first exact: nearT.
  by exists A => //; rewrite setIC setIT.
move=> A FA; exists A => //; exists A => //; exists setT; first exact: nearT.
by rewrite setIT.
Qed.

Definition compact A := forall (F : {filter T}),
  is_pfilter F -> F A -> A `&` cluster F !=set0.

Lemma compact0 : compact set0.
Proof. by move=> F FF /near_ex []. Qed.

Lemma subclosed_compact (A B : set T) :
  closed A -> compact B -> A `<=` B -> compact A.
Proof.
move=> Acl Bco sAB F Fproper FA.
have [|p [Bp Fp]] := Bco F; first exact: nearS FA.
by exists p; split=> //; apply: Acl=> C Cp; apply: Fp.
Qed.

Definition hausdorff := forall p q : T, cluster (nbhs p) q -> p = q.

Typeclasses Opaque within.
Global Instance within_nbhs_proper (A : set T) p :
  infer (closure A p) -> is_pfilter (within A (nbhs p)).
Proof.
move=> clAp; apply: Build_is_pfilter => B.
by move=> /clAp [q [Aq AqsoBq]]; exists q; apply: AqsoBq.
Qed.

Lemma compact_closed (A : set T) : hausdorff -> compact A -> closed A.
Proof.
move=> hT Aco p clAp; have pA := !! @withinT _ (nbhs p) A _.
have [q [Aq clsAp_q]] := !! Aco _ _ pA; rewrite (hT p q) //.
by apply: flim_cluster clsAp_q; apply: flim_within.
Qed.

End Compact.
Arguments hausdorff : clear implicits.

Lemma continuous_compact (T U : topologicalType) (f : T -> U) A :
  {in A, continuous f} -> compact A -> compact (f @` A).
Proof.
move=> fcont Aco F FF FfA; set G := filter_from F (fun C => A `&` f @^-1` C).
have GF : is_pfilter G.
  apply: (filter_from_proper (filter_from_filter _ _)); first by exists (f @` A).
    move=> C1 C2 F1 F2; exists (C1 `&` C2); first exact: nearI.
    by move=> ?[?[]]; split; split.
  by move=> C /(nearI FfA) /near_ex [_ [[p ? <-]]]; eexists p.
case: (Aco G); first by exists (f @` A) => // ? [].
move=> p [Ap clsGp]; exists (f p); split; first exact/imageP.
move=> B C FB /fcont; rewrite in_setE /= nbhs_filterE => /(_ Ap) p_Cf.
have : G (A `&` f @^-1` B) by exists B.
by move=> /clsGp /(_ p_Cf) [q [[]]]; exists (f q).
Qed.

Section Tychonoff.

Class Ultrais_filter T (F : {filter T}) := {
  ultra_proper :> is_pfilter F ;
  max_filter : forall G : {filter T}, is_pfilter G -> F `<=` G -> G = F
}.

Lemma ultra_flim_clusterE (T : topologicalType) (F : {filter T}) :
  Ultrais_filter F -> cluster F = [set p | F --> p].
Proof.
move=> FU; rewrite predeqE => p; split.
  by rewrite cluster_flimE => - [G GF [cvGp /max_filter <-]].
by move=> cvFp; rewrite cluster_flimE; exists F; [apply: ultra_proper|split].
Qed.

Lemma ultrais_filterLemma T (F : {filter T}) :
  is_pfilter F -> exists G, Ultrais_filter G /\ F `<=` G.
Proof.
move=> FF.
set filter_preordset := ({G : {filter T} & is_pfilter G /\ F `<=` G}).
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
suff UAF : is_pfilter (\bigcup_(H in A) projT1 H).
  have sFUA : F `<=` \bigcup_(H in A) projT1 H.
    by move=> B FB; exists G => //; apply: sFG.
  exists (existT _ (\bigcup_(H in A) projT1 H) (conj UAF sFUA)) => H AH B HB /=.
  by exists H.
apply Build_is_pfilter.
  by move=> B [H AH HB]; have [HF _] := projT2 H; apply: (@near_ex _ _ HF).
split; first by exists G => //; apply: nearT.
  move=> B C [HB AHB HBB] [HC AHC HCC]; have [sHBC|sHCB] := Atot _ _ AHB AHC.
    exists HC => //; have [HCF _] := projT2 HC; apply: nearI HCC.
    exact: sHBC.
  exists HB => //; have [HBF _] := projT2 HB; apply: nearI HBB _.
  exact: sHCB.
move=> B C SBC [H AH HB]; exists H => //; have [HF _] := projT2 H.
exact: nearS HB.
Qed.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : {filter T},
  Ultrais_filter F -> F A -> A `&` [set p | F --> p] !=set0].
Proof.
rewrite predeqE => A; split=> Aco F FF FA.
  by have /Aco [p [?]] := FA; rewrite ultra_flim_clusterE; exists p.
have [G [GU sFG]] := ultrais_filterLemma FF.
have /Aco [p [Ap]] : G A by apply: sFG.
rewrite -[_ --> p]/([set _ | _] p) -ultra_flim_clusterE.
by move=> /(flim_cluster sFG); exists p.
Qed.

Lemma filter_image (T U : Type) (f : T -> U) (F : {filter T}) :
  is_filter F -> f @` setT = setT -> is_filter [set f @` A | A in F].
Proof.
move=> FF fsurj; split.
- by exists setT => //; apply: nearT.
- move=> _ _ [A FA <-] [B FB <-].
  exists (f @^-1` (f @` A `&` f @` B)); last by rewrite image_preimage.
  have sAB : A `&` B `<=` f @^-1` (f @` A `&` f @` B).
    by move=> x [Ax Bx]; split; exists x.
  by apply: nearS sAB _; apply: nearI.
- move=> A B sAB [C FC fC_eqA].
  exists (f @^-1` B); last by rewrite image_preimage.
  by apply: nearS FC => p Cp; apply: sAB; rewrite -fC_eqA; exists p.
Qed.

Lemma proper_image (T U : Type) (f : T -> U) (F : {filter T}) :
  is_pfilter F -> f @` setT = setT -> is_pfilter [set f @` A | A in F].
Proof.
move=> FF fsurj; apply Build_is_pfilter; last exact: filter_image.
by move=> _ [A FA <-]; have /near_ex [p Ap] := FA; exists (f p); exists p.
Qed.

Lemma in_ultra_setVsetC T (F : {filter T}) (A : set T) :
  Ultrais_filter F -> F A \/ F (~` A).
Proof.
move=> FU; case: (pselect (F (~` A))) => [|nFnA]; first by right.
left; suff : is_pfilter (filter_from (F `|` [set A `&` B | B in F]) id).
  move=> /max_filter <-; last by move=> B FB; exists B => //; left.
  by exists A => //; right; exists setT; [apply: nearT|rewrite setIT].
apply filter_from_proper; last first.
  move=> B [|[C FC <-]]; first exact: near_ex.
  apply: contrapT => /asboolP; rewrite asbool_neg => /forallp_asboolPn AC0.
  by apply: nFnA; apply: nearS FC => p Cp Ap; apply: (AC0 p).
apply: filter_from_filter.
  by exists A; right; exists setT; [apply: nearT|rewrite setIT].
move=> B C [FB|[DB FDB <-]].
  move=> [FC|[DC FDC <-]]; first by exists (B `&` C)=> //; left; apply: nearI.
  exists (A `&` (B `&` DC)); last by rewrite setICA.
  by right; exists (B `&` DC) => //; apply: nearI.
move=> [FC|[DC FDC <-]].
  exists (A `&` (DB `&` C)); last by rewrite setIA.
  by right; exists (DB `&` C) => //; apply: nearI.
exists (A `&` (DB `&` DC)); last by move=> ? ?; rewrite setIACA setIid.
by right; exists (DB `&` DC) => //; apply: nearI.
Qed.

Lemma ultra_image (T U : Type) (f : T -> U) (F : {filter T}) :
  Ultrais_filter F -> f @` setT = setT -> Ultrais_filter [set f @` A | A in F].
Proof.
move=> FU fsurj; split; first exact: proper_image.
move=> G GF sfFG; rewrite predeqE => A; split; last exact: sfFG.
move=> GA; exists (f @^-1` A); last by rewrite image_preimage.
have [//|FnAf] := in_ultra_setVsetC (f @^-1` A) FU.
have : G (f @` (~` (f @^-1` A))) by apply: sfFG; exists (~` (f @^-1` A)).
suff : ~ G (f @` (~` (f @^-1` A))) by [].
rewrite preimage_setC image_preimage // => GnA.
by have /near_ex [? []] : G (A `&` (~` A)) by apply: nearI.
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
  rewrite /subst_coord; case: eqP => // e.
  by rewrite (eq_irrelevance e (erefl _)).
have subst_coordN i pi f j : i != j -> subst_coord i pi f j = f j.
  move=> inej; rewrite /subst_coord; case: eqP => // e.
  by move: inej; rewrite {1}e => /negP.
have pr_surj i : @^~ i @` (@setT (forall i, T i)) = setT.
  rewrite predeqE => pi; split=> // _.
  by exists (subst_coord i pi (fun _ => point))=> //; rewrite subst_coordT.
set pF := fun i => [set @^~ i @` B | B in F].
have pFultra : forall i, Ultrais_filter (pF i).
  by move=> i; apply: ultra_image (pr_surj i).
have pFA : forall i, pF i (A i).
  move=> i; exists [set g | forall i, A i (g i)] => //.
  rewrite predeqE => pi; split; first by move=> [g Ag <-]; apply: Ag.
  move=> Aipi; have [f Af] := near_ex FA.
  exists (subst_coord i pi f); last exact: subst_coordT.
  move=> j; case: (eqVneq i j); first by case: _ /; rewrite subst_coordT.
  by move=> /subst_coordN ->; apply: Af.
have cvpFA i : A i `&` [set p | pF i --> p] !=set0.
  by rewrite -ultra_flim_clusterE; apply: Aco.
exists (fun i => get (A i `&` [set p | pF i --> p])).
split=> [i|]; first by have /getPex [] := cvpFA i.
by apply/flim_sup => i; apply/flim_image=> //; have /getPex [] := cvpFA i.
Qed.

End Tychonoff.

Definition finI (I : choiceType) T (D : set I) (f : I -> set T) :=
  forall D' : {fset I}, {subset D' <= D} ->
  \bigcap_(i in [set i | i \in D']) f i !=set0.

Lemma finI_filter (I : choiceType) T (D : set I) (f : I -> set T) :
  finI D f -> is_pfilter (filter_from (finI_from D f) id).
Proof.
move=> finIf; apply: (filter_from_proper (filter_from_filter _ _)).
- by exists setT; exists fset0 => //; rewrite predeqE.
- move=> A B [DA sDA IfA] [DB sDB IfB]; exists (A `&` B) => //.
  exists (DA `|` DB)%fset.
    by move=> ?; rewrite in_fsetE => /orP [/sDA|/sDB].
  rewrite -IfA -IfB predeqE => p; split=> [Ifp|[IfAp IfBp] i].
    by split=> i Di; apply: Ifp; rewrite in_fsetE Di // orbC.
  by rewrite in_fsetE => /orP []; [apply: IfAp|apply: IfBp].
- by move=> _ [? ? <-]; apply: finIf.
Qed.

Lemma filter_finI (T : pointedType) (F : {filter T}) (D : {filter T})
  (f : set T -> set T) :
  is_pfilter F -> (forall A, D A -> F (f A)) -> finI D f.
Proof.
move=> FF sDFf D' sD; apply: (@near_ex _ F); apply: filter_bigI.
by move=> A /sD; rewrite in_setE => /sDFf.
Qed.

Section Covers.

Variable T : topologicalType.

Definition cover_compact (A : set T) :=
  forall (I : choiceType) (D : set I) (f : I -> set T),
  (forall i, D i -> open (f i)) -> A `<=` \bigcup_(i in D) f i ->
  exists2 D' : {fset I}, {subset D' <= D} &
    A `<=` \bigcup_(i in [set i | i \in D']) f i.

Definition open_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> open (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma cover_compactE :
  cover_compact =
  [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    open_fam_of A D f -> A `<=` \bigcup_(i in D) f i ->
    exists2 D' : {fset I}, {subset D' <= D} &
      A `<=` \bigcup_(i in [set i | i \in D']) f i].
Proof.
rewrite predeqE => A; split=> [Aco I D f [g gop feAg] fcov|Aco I D f fop fcov].
  have gcov : A `<=` \bigcup_(i in D) g i.
    by move=> p /fcov [i Di]; rewrite feAg // => - []; exists i.
  have [D' sD sgcov] := Aco _ _ _ gop gcov.
  exists D' => // p Ap; have /sgcov [i D'i gip] := Ap.
  by exists i => //; rewrite feAg //; have /sD := D'i; rewrite in_setE.
have Afcov : A `<=` \bigcup_(i in D) (A `&` f i).
  by move=> p Ap; have /fcov [i ? ?] := Ap; exists i.
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
  by apply: nearI => //; apply: nearS FB; apply: subset_closure.
have [|p AclFIp] := Aco _ _ _ _ finIAclF.
  by exists closure=> //; move=> ? ?; apply: closed_closure.
exists p; split=> [|B C FB p_C]; first by have /AclFIp [] := FA.
by have /AclFIp [_] := FB; move=> /(_ _ p_C).
Qed.

Lemma exists2P A (P Q : A -> Prop) :
  (exists2 x, P x & Q x) <-> exists x, P x /\ Q x.
Proof. by split=> [[x ? ?] | [x []]]; exists x. Qed.

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
    exists (fun i => ~` g i) => i Di; first exact/closedC/gop.
    rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
      by move=> gip; apply: nfip; rewrite feAg.
    by rewrite feAg // => - [].
  move=> D' sD.
  have /asboolP : ~ A `<=` \bigcup_(i in [set i | i \in D']) f i.
    by move=> sAIf; apply: (sfncov D').
  rewrite asbool_neg => /existsp_asboolPn [p /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ap nUfp].
  by exists p => i D'i; split=> // fip; apply: nUfp; exists i.
case: (pselect (exists i, D i)) => [[j Dj] | /asboolP]; last first.
  by rewrite asbool_neg => /forallp_asboolPn D0 => _; exists point => ? /D0.
apply: contrapTT => /asboolP; rewrite asbool_neg => /forallp_asboolPn If0.
apply/asboolP; rewrite asbool_neg; apply/existsp_asboolPn.
have Anfcov : A `<=` \bigcup_(i in D) (A `\` f i).
  move=> p Ap; have /asboolP := If0 p; rewrite asbool_neg => /existsp_asboolPn.
  move=> [i /asboolP]; rewrite asbool_neg => /imply_asboolPn [Di nfip].
  by exists i.
have Anfop : open_fam_of A D (fun i => A `\` f i).
  exists (fun i => ~` g i) => i Di; first exact/openC/gcl.
  rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
    by move=> gip; apply: nfip; rewrite feAg.
  by rewrite feAg // => - [].
have [D' sD sAnfcov] := Aco _ _ _ Anfop Anfcov.
wlog [k D'k] : D' sD sAnfcov / exists i, i \in D'.
  move=> /(_ (D' `|` [fset j])%fset); apply.
  - by move=> k; rewrite !in_fsetE => /orP [/sD|/eqP->] //; rewrite in_setE.
  - by move=> p /sAnfcov [i D'i Anfip]; exists i => //; rewrite !in_fsetE D'i.
  - by exists j; rewrite !in_fsetE orbC eq_refl.
exists D' => /(_ sD) [p Ifp].
have /Ifp := D'k; rewrite feAg; last by have /sD := D'k; rewrite in_setE.
by move=> [/sAnfcov [i D'i [_ nfip]] _]; have /Ifp := D'i.
Qed.

End Covers.

(* connected sets *)

Definition connected (T : topologicalType) (A : set T) :=
  forall B : set T, B !=set0 -> (exists2 C, open C & B = A `&` C) ->
  (exists2 C, closed C & B = A `&` C) -> B = A.

(** * Uniform spaces defined using balls *)

Definition nbhs_ {T T'} (ball : T -> R -> set T') (x : T) :=
   @filter_from R _ [set x | 0 < x] (ball x).

Lemma nbhs_E {T T'} (ball : T -> R -> set T') x :
  nbhs_ ball x = @filter_from R _ [set x : R | 0 < x] (ball x).
Proof. by []. Qed.

Module Uniform.

Record mixin_of (M : Type) (nbhs : M -> {filter M}) := Mixin {
  ball : M -> R -> M -> Prop ;
  ax1 : forall x (e : R), 0 < e -> ball x e x ;
  ax2 : forall x y (e : R), ball x e y -> ball y e x ;
  ax3 : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  ax4 : nbhs = nbhs_ ball
}.

Record class_of (M : Type) := Class {
  base : Topological.class_of M;
  mixin : mixin_of (Filter.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Topological.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack loc (m : @mixin_of T loc) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filter.nbhs_op b)) =>
  @Pack T (@Class _ b m') T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filterType := @Filter.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.

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
Coercion filterType : type >-> Filter.type.
Canonical filterType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.
Notation "[ 'uniformType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'uniformType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'uniformType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'uniformType'  'of'  T ]") : form_scope.

End Exports.

End Uniform.

Export Uniform.Exports.

Section UniformTopology.

Lemma my_ball_le (M : Type) (loc : M -> {filter M})
  (m : Uniform.mixin_of loc) :
  forall (x : M) (e1 e2 : R), e1 <= e2 ->
  forall (y : M), Uniform.ball m x e1 y -> Uniform.ball m x e2 y.
Proof.
move=> x e1 e2 le12 y xe1_y.
move: le12; rewrite ler_eqVlt => /orP [/eqP <- //|].
rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: Uniform.ax3 xe1_y.
suff : Uniform.ball m x (PosNum lt12)%:num x by [].
exact: Uniform.ax1.
Qed.

Program Definition OfBall.topologyMixin (T : Type)
  (loc : T -> {filter T}) (m : Uniform.mixin_of loc) :
  Topological.mixin_of loc := OfFilter.topologyMixin _ _ _.
Next Obligation.
rewrite (Uniform.ax4 m) nbhs_E; apply filter_from_proper; last first.
  move=> e egt0; exists p; suff : Uniform.ball m p (PosNum egt0)%:num p by [].
  exact: Uniform.ax1.
apply: filter_from_filter; first by exists 1%:pos%:num.
move=> e1 e2 e1gt0 e2gt0; exists (Num.min e1 e2).
  by have := min_pos_gt0 (PosNum e1gt0) (PosNum e2gt0).
by move=> q pmin_q; split; apply: my_ball_le pmin_q;
  rewrite ler_minl lerr // orbC.
Qed.
Next Obligation.
move: H; rewrite (Uniform.ax4 m) nbhs_E => - [e egt0]; apply.
by have : Uniform.ball m p (PosNum egt0)%:num p by exact: Uniform.ax1.
Qed.
Next Obligation.
move: H; rewrite (Uniform.ax4 m) nbhs_E => - [e egt0 pe_A].
exists ((PosNum egt0)%:num / 2) => // q phe_q.
rewrite nbhs_E; exists ((PosNum egt0)%:num / 2) => // r qhe_r.
by apply: pe_A; rewrite [e]splitr; apply: Uniform.ax3 qhe_r.
Qed.

End UniformTopology.

Definition ball {M : uniformType} := Uniform.ball (Uniform.class M).

Lemma nbhs_ballE {M : uniformType} : nbhs_ (@ball M) = nbhs.
Proof. by case: M=> [?[?[]]]. Qed.

Lemma filter_from_ballE {M : uniformType} x :
  @filter_from R _ [set x : R | 0 < x] (@ball M x) = nbhs x.
Proof. by rewrite -nbhs_ballE. Qed.

Module Export NbhsBall.
Definition nbhs_simpl := (nbhs_simpl,@filter_from_ballE,@nbhs_ballE).
End NbhsBall.

Lemma nbhsP {M : uniformType} (x : M) P :
  nbhs x P <-> nbhs_ ball x P.
Proof. by rewrite nbhs_simpl. Qed.

Section uniformType1.
Context {M : uniformType}.

Lemma ball_center (x : M) (e : posreal) : ball x e%:num x.
Proof. exact: Uniform.ax1. Qed.
Hint Resolve ball_center : core.

Lemma ballxx (x : M) (e : R) : (0 < e)%R -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: Uniform.ax2. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2)%R z.
Proof. exact: Uniform.ax3. Qed.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2)%R z -> ball z (e / 2)%R y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -splitr. Qed.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2)%R x -> ball z (e / 2)%R y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

Lemma ball_ler (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y; case: ltrgtP le12 => [//|lte12 _|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma ball_le (x : M) (e1 e2 : R) : (e1 <= e2)%coqR -> ball x e1 `<=` ball x e2.
Proof. by move=> /RleP/ball_ler. Qed.

Lemma nbhs_ball (x : M) (eps : posreal) : nbhs x (ball x eps%:num).
Proof. by apply/nbhsP; exists eps%:num. Qed.
Hint Resolve nbhs_ball : core.

Definition close (x y : M) : Prop := forall eps : posreal, ball x eps%:num y.

Lemma close_refl (x : M) : close x x. Proof. by []. Qed.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof. by move=> ? ?; apply: ball_sym. Qed.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof. by move=> cxy cyz eps; apply: ball_split (cxy _) (cyz _). Qed.

Lemma close_limxx (x y : M) : close x y -> x --> y.
Proof.
move=> cxy P /= /nbhsP /= [_/posnumP [eps] epsP].
apply/nbhsP; exists (eps%:num / 2) => // z bxz.
by apply: epsP; apply: ball_splitr (cxy _) bxz.
Qed.

Definition entourages : set (set (M * M)):=
  filter_from [set eps : R | eps > 0]
              (fun eps => [set xy | ball xy.1 eps xy.2]).

Global Instance entourages_filter : is_pfilter entourages.
Proof.
apply filter_from_proper; last by exists (point,point); apply: ballxx.
apply: filter_from_filter; first by exists 1; rewrite ltr01.
move=> _ _ /posnumP[i] /posnumP[j]; exists (minr i j) => // [[/= x y]] bxy.
by eexists => /=; apply: ball_ler bxy; rewrite ler_minl lerr ?orbT.
Qed.
Typeclasses Opaque entourages.

Lemma flim_close {F} {FF : is_pfilter F} (x y : M) :
  F --> x -> F --> y -> close x y.
Proof.
move=> Fx Fy e; near F => z; apply: (@ball_splitl z); near: z;
by [apply/Fx/nbhs_ball|apply/Fy/nbhs_ball].
Grab Existential Variables. all: end_near. Qed.

Lemma flimx_close (x y : M) : x --> y -> close x y.
Proof. exact: flim_close. Qed.

Lemma near_ball (y : M) (eps : posreal) :
   \forall y' \near y, ball y eps%:num y'.
Proof. exact: nbhs_ball. Qed.

Lemma flim_ballP {F} {FF : is_filter F} (y : M) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by rewrite -filter_fromP !nbhs_simpl /=. Qed.
Definition flim_nbhs := @flim_ballP.

Lemma flim_ballPpos {F} {FF : is_filter F} (y : M) :
  F --> y <-> forall eps : {posnum R}, \forall y' \near F, ball y eps%:num y'.
Proof.
by split => [/flim_ballP|] pos; [case|apply/flim_ballP=> _/posnumP[eps] //].
Qed.

Lemma flim_ball {F} {FF : is_filter F} (y : M) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by move/flim_ballP. Qed.

Lemma app_flim_nbhs T {F} {FF : is_filter F} (f : T -> M) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: flim_ballP. Qed.

Lemma flimi_ballP T {F} {FF : is_filter F} (f : T -> M -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Proof.
split=> [Fy _/posnumP[eps] |Fy P] /=; first exact/Fy/nbhs_ball.
move=> /nbhsP[_ /posnumP[eps] subP].
rewrite near_simpl near_mapi; near=> x.
have [//|z [fxz yz]] := near (Fy _ (posnum_gt0 eps)) x.
by exists z => //; split => //; apply: subP.
Unshelve. all: end_near. Qed.
Definition flimi_nbhs := @flimi_ballP.

Lemma flimi_ball T {F} {FF : is_filter F} (f : T -> M -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/flimi_ballP. Qed.

Lemma flimi_close T {F} {FF: is_pfilter F} (f : T -> set M) (l l' : M) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: infer {near F, is_totalfun f} by exact: flim_close fFl fFl'.
apply: filter_app f_prop; near=> x; split=> //=.
by have [//|y [fxy _]] := near (flimi_ball fFl [gt0 of 1]) x; exists y.
Grab Existential Variables. all: end_near. Qed.
Definition flimi_nbhs_close := @flimi_close.

Lemma flim_const {T} {F : {filter T}}
   {FF : is_filter F} (a : M) : a @[_ --> F] --> a.
Proof.
move=> P /nbhsP[_ /posnumP[eps] subP]; rewrite !near_simpl /=.
by apply: filterE=> ?; apply/subP.
Qed.

Lemma close_lim (F1 F2 : {filter M}) {FF2 : is_pfilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
move=> F12 F21; have [/(flim_trans F21) F2l|dvgF1] := pselect (cvg F1).
  by apply: (@flim_close F2) => //; apply: cvgP F2l.
have [/(flim_trans F12)/cvgP//|dvgF2] := pselect (cvg F2).
by rewrite dvgP // dvgP //.
Qed.

Lemma flim_closeP (F : {filter M}) (l : M) : is_pfilter F ->
  F --> l <-> ([cvg F in M] /\ close (lim F) l).
Proof.
move=> FF; split=> [Fl|[cvF]Cl].
  by have /cvgP := Fl; split=> //; apply: (@flim_close F).
by apply: flim_trans (close_limxx Cl).
Qed.

Definition ball_set (A : set M) e := \bigcup_(p in A) ball p e.
Canonical set_filter_source :=
  @Filter.Source Prop _ M (fun A => nbhs_ ball_set A).

End uniformType1.

Hint Resolve ball_center : core.
Hint Resolve close_refl : core.
Hint Resolve nbhs_ball : core.
Arguments flim_const {M T F FF} a.
Arguments close_lim {M} F1 F2 {FF2} _.

Section entourages.

Definition unif_cont (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourages --> entourages.

Lemma unif_contP (U V : uniformType) (f : U -> V) :
  unif_cont f <->
  forall e, e > 0 -> exists2 d, d > 0 &
    forall x, ball x.1 d x.2 -> ball (f x.1) e (f x.2).
Proof. exact: filter_fromP. Qed.

End entourages.

(** ** Specific uniform spaces *)

(** matrices *)

Section matrix_Uniform.

Variables (m n : nat) (T : uniformType).

Implicit Types x y : 'M[T]_(m, n).

Definition mx_ball x (e : R) y := forall i j, ball (x i j) e (y i j).

Lemma mx_ball_center x (e : R) : 0 < e -> mx_ball x e x.
Proof. by move=> ? ? ?; apply: ballxx. Qed.

Lemma mx_ball_sym x y (e : R) : mx_ball x e y -> mx_ball y e x.
Proof. by move=> xe_y ? ?; apply/ball_sym/xe_y. Qed.

Lemma mx_ball_triangle x y z (e1 e2 : R) :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ? ?; apply: ball_triangle; [apply: xe1_y| apply: ye2_z].
Qed.

Lemma ltr_bigminr (I : finType) (R : realDomainType) (f : I -> R) (x0 x : R) :
  x < x0 -> (forall i, x < f i) -> x < \big[minr/x0]_i f i.
Proof.
move=> ltx0 ltxf; elim/big_ind: _ => // y z ltxy ltxz.
by rewrite ltr_minr ltxy ltxz.
Qed.

Lemma bigminr_ler (I : finType) (R : realDomainType) (f : I -> R) (x0 : R) i :
  \big[minr/x0]_j f j <= f i.
Proof.
have := mem_index_enum i; rewrite unlock; elim: (index_enum I) => //= j l ihl.
by rewrite inE => /orP [/eqP->|/ihl leminlfi];
  rewrite ler_minl ?lerr // leminlfi orbC.
Qed.

Canonical R_pointedType := PointedType R 0.

Lemma mx_nbhs : nbhs = nbhs_ mx_ball.
Proof.
rewrite predeq2E => x A; split; last first.
  by move=> [e egt0 xe_A]; exists (fun i j => ball (x i j) (PosNum egt0)%:num).
move=> [P]; rewrite -nbhs_ballE => x_P sPA.
exists (\big[minr/1]_i \big[minr/1]_j
  get (fun e : R => 0 < e /\ ball (x i j) e `<=` P i j)).
  apply: ltr_bigminr => // i; apply: ltr_bigminr => // j.
  by have /exists2P/getPex [] := x_P i j.
move=> y xmin_y; apply: sPA => i j; have /exists2P/getPex [_] := x_P i j; apply.
apply: ball_ler (xmin_y i j).
by apply: ler_trans (bigminr_ler _ _ i) _; apply: bigminr_ler.
Qed.

Definition matrix_uniformType_mixin :=
  Uniform.Mixin mx_ball_center mx_ball_sym mx_ball_triangle mx_nbhs.

Canonical matrix_uniformType :=
  UniformType 'M[T]_(m, n) matrix_uniformType_mixin.

End matrix_Uniform.

(** product of two uniform spaces *)

Section prod_Uniform.

Context {U V : uniformType}.
Implicit Types (x y : U * V).

Definition prod_point : U * V := (point, point).

Definition prod_ball x (eps : R) y :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).

Lemma prod_ball_center x (eps : R) : 0 < eps -> prod_ball x eps x.
Proof. by move=> /posnumP[e]; split. Qed.

Lemma prod_ball_sym x y (eps : R) : prod_ball x eps y -> prod_ball y eps x.
Proof. by move=> [bxy1 bxy2]; split; apply: ball_sym. Qed.

Lemma prod_ball_triangle x y z (e1 e2 : R) :
  prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Proof.
by move=> [bxy1 bxy2] [byz1 byz2]; split; eapply ball_triangle; eassumption.
Qed.

Lemma prod_nbhs : nbhs = nbhs_ prod_ball.
Proof.
rewrite predeq2E => -[x y] P; split=> [[[A B] /=[xX yY] XYP] |]; last first.
  by move=> [_ /posnumP[eps] epsP]; exists (ball x eps%:num, ball y eps%:num) => /=.
move: xX yY => /nbhsP [_ /posnumP[ex] eX] /nbhsP [_ /posnumP[ey] eY].
exists (minr ex%:num ey%:num) => // -[x' y'] [/= xx' yy'].
apply: XYP; split=> /=.
  by apply/eX/(ball_ler _ xx'); rewrite ler_minl lerr.
by apply/eY/(ball_ler _ yy'); rewrite ler_minl lerr orbT.
Qed.

Definition prod_uniformType_mixin :=
  Uniform.Mixin prod_ball_center prod_ball_sym prod_ball_triangle prod_nbhs.

End prod_Uniform.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (@prod_uniformType_mixin U V).

Section Nbhs_fct2.

Context {T : Type} {U V : uniformType}.

Lemma flim_ball2P {F : {filter U}} {G : {filter V}}
  {FF : is_filter F} {FG : is_filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall y' \near F & z' \near G,
                ball y eps y' /\ ball z eps z'.
Proof. exact: flim_ballP. Qed.

End Nbhs_fct2.

(** Functional metric spaces *)

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).

Lemma fct_ball_center (x : T -> U) (e : R) : 0 < e -> fct_ball x e x.
Proof. by move=> /posnumP[{e}e] t. Qed.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Proof. by move=> P t; apply: ball_sym. Qed.

Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof. by move=> xy yz t; apply: (@ball_triangle _ (y t)). Qed.

Definition fct_uniformType_mixin :=
  UniformMixin fct_ball_center fct_ball_sym fct_ball_triangle erefl.

Definition fct_topologicalTypeMixin :=
  OfBall.topologyMixin fct_uniformType_mixin.

Canonical generic_source_filter := @Filter.Source _ _ _ (nbhs_ fct_ball).
Canonical fct_topologicalType :=
  TopologicalType (T -> U) fct_topologicalTypeMixin.
Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.

End fct_Uniform.

(** ** Complete uniform spaces *)

(* :TODO: Use cauchy2 alternative to define cauchy? *)
(* Or not: is the fact that cauchy F -/> is_pfilter F a problem? *)
Definition cauchy_ex {T : uniformType} (F : {filter T}) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy {T : uniformType} (F : {filter T}) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_entouragesP (T  : uniformType) (F : {filter T}) :
  is_filter F -> cauchy F <-> (F, F) --> entourages.
Proof.
move=> FF; split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply: cauchyF; exists eps%:num.
move=> U [_/posnumP[eps] xyepsU].
by near=> x; apply: xyepsU; near: x; apply: cauchyF.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_cauchy_ex {T : uniformType} (F : {filter T}) :
  [cvg F in T] -> cauchy_ex F.
Proof. by move=> Fl _/posnumP[eps]; exists (lim F); apply/Fl/nbhs_ball. Qed.

Lemma cauchy_exP (T : uniformType) (F : {filter T}) : is_filter F ->
  cauchy_ex F -> cauchy F.
Proof.
move=> FF Fc; apply/cauchy_entouragesP => A [_/posnumP[e] sdeA].
have /Fc [z /= Fze] := [gt0 of e%:num / 2]; near=> x y; apply: sdeA => /=.
by apply: (@ball_splitr _ z); [near: x|near: y].
Grab Existential Variables. all: end_near. Qed.

Lemma cauchyP (T : uniformType) (F : {filter T}) : is_pfilter F ->
  cauchy F <-> cauchy_ex F.
Proof.
move=> FF; split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
by near F => x; exists x; near: x; apply: (@nearP_dep _ _ F F); apply: Fcauchy.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_cauchy {T : uniformType} (F : {filter T}) : is_filter F ->
  [cvg F in T] -> cauchy F.
Proof. by move=> FF /cvg_cauchy_ex /cauchy_exP. Qed.

Module Complete.

Definition axiom (T : uniformType) :=
  forall (F : {filter T}), is_pfilter F -> cauchy F -> F --> lim F.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : axiom (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> Complete.axiom.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : axiom (@Uniform.Pack T b0 T)) :=
  fun bT b of phant_id (Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filterType := @Filter.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.

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
Coercion filterType : type >-> Filter.type.
Canonical filterType.
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

Lemma complete_cauchy (F : {filter T}) (FF : is_pfilter F) :
  cauchy F -> F --> lim F.
Proof. by case: T F FF => [? [?]]. Qed.

End completeType1.
Arguments complete_cauchy {T} F {FF} _.

Section matrix_Complete.

Variables (T : completeType) (m n : nat).

Lemma mx_complete (F : set (set 'M[T]_(m, n))) :
  is_pfilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _) /complete_cauchy cvF :
  cauchy ((fun M : 'M[T]_(m, n) => M _ _) @ F).
  by move=> ? ? _ /posnumP[e]; rewrite near_simpl; apply: nearS (Fc _ _).
apply/cvg_ex.
exists (\matrix_(i, j) (lim ((fun M : 'M[T]_(m, n) => M i j) @ F) : T)).
apply/flim_ballP => _ /posnumP[e]; near=> M => i j.
rewrite mxE; near F => M' => /=; apply: (@ball_splitl _ (M' i j)).
  by near: M'; apply/cvF/nbhs_ball.
by move: (i) (j); near: M'; near: M; apply: nearP_dep; apply: nearS (Fc _ _).
Grab Existential Variables. all: end_near. Qed.

Canonical matrix_completeType := CompleteType 'M[T]_(m, n) mx_complete.

End matrix_Complete.

Section fun_Complete.

Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set (set (T -> U)))
  {FF :  is_pfilter F} : cauchy F -> cvg F.
Proof.
move=> Fc; have /(_ _) /complete_cauchy Ft_cvg : cauchy (@^~_ @ F).
  by move=> t e ?; rewrite near_simpl; apply: nearS (Fc _ _).
apply/cvg_ex; exists (fun t => lim (@^~t @ F)).
apply/flim_ballPpos => e; near=> f => t; near F => g => /=.
apply: (@ball_splitl _ (g t)); first by near: g; exact/Ft_cvg/nbhs_ball.
by move: (t); near: g; near: f; apply: nearP_dep; apply: nearS (Fc _ _).
Grab Existential Variables. all: end_near. Qed.

Canonical fun_completeType := CompleteType (T -> U) fun_complete.

End fun_Complete.

(** ** Limit switching *)

Section Flim_switch.

Context {T1 T2 : choiceType}.

Lemma flim_switch_1 {U : uniformType}
  F1 {FF1 : is_pfilter F1} F2 {FF2 : is_filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/flim_ballPpos => e.
rewrite near_simpl; near F1 => x1; near=> x2.
apply: (@ball_split _ (h x1)); first by near: x1; apply/hl/nbhs_ball.
apply: (@ball_splitl _ (f x1 x2)); first by near: x2; apply/fh/nbhs_ball.
by move: (x2); near: x1; apply/(flim_ball fg).
Grab Existential Variables. all: end_near. Qed.

Lemma flim_switch_2 {U : completeType}
  F1 {FF1 : is_pfilter F1} F2 {FF2 : is_pfilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Proof.
move=> fg fh; apply: complete_cauchy => _/posnumP[e].
rewrite !near_simpl; near=> x1 y1=> /=; near F2 => x2.
apply: (@ball_splitl _ (f x1 x2)); first by near: x2; apply/fh/nbhs_ball.
apply: (@ball_split _ (f y1 x2)); first by near: x2; apply/fh/nbhs_ball.
apply: (@ball_splitr _ (g x2)); move: (x2); [near: y1|near: x1];
by apply/(flim_ball fg).
Grab Existential Variables. all: end_near. Qed.

(* Alternative version *)
(* Lemma flim_switch {U : completeType} *)
(*   F1 (FF1 : is_pfilter F1) F2 (FF2 : is_pfilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) : *)
(*   [cvg f @ F1 in T2 -> U] -> (forall x, [cvg f x @ F2 in U]) -> *)
(*   [/\ [cvg [lim f @ F1] @ F2 in U], [cvg (fun x => [lim f x @ F2]) @ F1 in U] *)
(*   & [lim [lim f @ F1] @ F2] = [lim (fun x => [lim f x @ F2]) @ F1]]. *)
Lemma flim_switch {U : completeType}
  F1 (FF1 : is_pfilter F1) F2 (FF2 : is_pfilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
move=> Hfg Hfh; have hcv := !! flim_switch_2 Hfg Hfh.
by exists [lim h @ F1 in U]; split=> //; apply: flim_switch_1 Hfg Hfh hcv.
Qed.

End Flim_switch.
